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

variable {ι E F : Type*} {G : ι → Type*}

/-! ### `PUnit` -/

namespace PUnit

/-
**PUnit.normedAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `PUnit`。
形式化陈述：normedAddCommGroup : NormedAddCommGroup PUnit where norm
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance normedAddCommGroup : NormedAddCommGroup PUnit where
  norm := Function.const _ 0
  dist_eq _ _ := rfl
/-
**PUnit.norm_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `PUnit`。
形式化陈述：∀ (x : PUnit.{u_5 + 1}), ‖x‖ = 0
参数：x : PUnit.{u_5 + 1}。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma norm_eq_zero (x : PUnit) : ‖x‖ = 0 := rfl

end PUnit

/-! ### `ULift` -/

namespace ULift
section Norm
variable [Norm E]

/-
**ULift.norm** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：norm : Norm (ULift E) where norm x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance norm : Norm (ULift E) where norm x := ‖x.down‖
/-
**ULift.norm_def** 是 Mathlib 中的一个引理，位于命名空间 `ULift`。
形式化陈述：norm_def (x : ULift E) : ‖x‖ = ‖x.down‖
参数：x : ULift E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma norm_def (x : ULift E) : ‖x‖ = ‖x.down‖ := rfl
/-
**ULift.norm_up** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：∀ {E : Type u_2} [inst : Norm E] (x : E), ‖{ down := x }‖ = ‖x‖
参数：x : E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma norm_up (x : E) : ‖ULift.up x‖ = ‖x‖ := rfl
/-
**ULift.norm_down** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：∀ {E : Type u_2} [inst : Norm E] (x : ULift.{u_5, u_2} E), ‖x.down‖ = ‖x‖
参数：x : ULift.{u_5, u_2} E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma norm_down (x : ULift E) : ‖x.down‖ = ‖x‖ := rfl

end Norm

section NNNorm
variable [NNNorm E]

/-
**ULift.nnnorm** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：nnnorm : NNNorm (ULift E) where nnnorm x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance nnnorm : NNNorm (ULift E) where nnnorm x := ‖x.down‖₊
/-
**ULift.nnnorm_def** 是 Mathlib 中的一个引理，位于命名空间 `ULift`。
形式化陈述：nnnorm_def (x : ULift E) : ‖x‖₊ = ‖x.down‖₊
参数：x : ULift E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma nnnorm_def (x : ULift E) : ‖x‖₊ = ‖x.down‖₊ := rfl
/-
**ULift.nnnorm_up** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：∀ {E : Type u_2} [inst : NNNorm E] (x : E), ‖{ down := x }‖₊ = ‖x‖₊
参数：x : E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma nnnorm_up (x : E) : ‖ULift.up x‖₊ = ‖x‖₊ := rfl
/-
**ULift.nnnorm_down** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：∀ {E : Type u_2} [inst : NNNorm E] (x : ULift.{u_5, u_2} E), ‖x.down‖₊ = ‖
x‖₊
参数：x : ULift.{u_5, u_2} E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma nnnorm_down (x : ULift E) : ‖x.down‖₊ = ‖x‖₊ := rfl

end NNNorm

@[to_additive]
/-
**ULift.seminormedGroup** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：seminormedGroup [SeminormedGroup E] : SeminormedGroup (ULift E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance seminormedGroup [SeminormedGroup E] : SeminormedGroup (ULift E) :=
  SeminormedGroup.induced _ _
  { toFun := ULift.down,
    map_one' := rfl,
    map_mul' := fun _ _ => rfl : ULift E →* E }

@[to_additive]
/-
**ULift.seminormedCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：seminormedCommGroup [SeminormedCommGroup E] : SeminormedCommGroup (ULift E
)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance seminormedCommGroup [SeminormedCommGroup E] : SeminormedCommGroup (ULift E) :=
  SeminormedCommGroup.induced _ _
  { toFun := ULift.down,
    map_one' := rfl,
    map_mul' := fun _ _ => rfl : ULift E →* E }

@[to_additive]
/-
**ULift.normedGroup** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：normedGroup [NormedGroup E] : NormedGroup (ULift E)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ULift.down_injective`：∀ {α : Type u_1}, Function.Injective ULift.down
-/
instance normedGroup [NormedGroup E] : NormedGroup (ULift E) :=
  NormedGroup.induced _ _
  { toFun := ULift.down,
    map_one' := rfl,
    map_mul' := fun _ _ => rfl : ULift E →* E }
  down_injective

@[to_additive]
/-
**ULift.normedCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
形式化陈述：normedCommGroup [NormedCommGroup E] : NormedCommGroup (ULift E)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ULift.down_injective`：∀ {α : Type u_1}, Function.Injective ULift.down
-/
instance normedCommGroup [NormedCommGroup E] : NormedCommGroup (ULift E) :=
  NormedCommGroup.induced _ _
  { toFun := ULift.down,
    map_one' := rfl,
    map_mul' := fun _ _ => rfl : ULift E →* E }
  down_injective

end ULift

/-! ### `Additive`, `Multiplicative` -/

section AdditiveMultiplicative

open Additive Multiplicative

section Norm
variable [Norm E]

/-
**Additive.toNorm** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Additive.toNorm : Norm (Additive E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Additive.toNorm : Norm (Additive E) := ‹Norm E›
/-
**Multiplicative.toNorm** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiplicative.toNorm : Norm (Multiplicative E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Multiplicative.toNorm : Norm (Multiplicative E) := ‹Norm E›
/-
**norm_toMul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {E : Type u_2} [inst : Norm E] (x : Additive E), ‖Additive.toMul x‖ = ‖x
‖
参数：x : Additive E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma norm_toMul (x : Additive E) : ‖(x.toMul : E)‖ = ‖x‖ := rfl
/-
**norm_ofMul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {E : Type u_2} [inst : Norm E] (x : E), ‖Additive.ofMul x‖ = ‖x‖
参数：x : E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma norm_ofMul (x : E) : ‖ofMul x‖ = ‖x‖ := rfl
/-
**norm_toAdd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {E : Type u_2} [inst : Norm E] (x : Multiplicative E), ‖Multiplicative.t
oAdd x‖ = ‖x‖
参数：x : Multiplicative E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma norm_toAdd (x : Multiplicative E) : ‖(x.toAdd : E)‖ = ‖x‖ := rfl
/-
**norm_ofAdd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {E : Type u_2} [inst : Norm E] (x : E), ‖Multiplicative.ofAdd x‖ = ‖x‖
参数：x : E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma norm_ofAdd (x : E) : ‖ofAdd x‖ = ‖x‖ := rfl

end Norm

section NNNorm
variable [NNNorm E]

/-
**Additive.toNNNorm** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Additive.toNNNorm : NNNorm (Additive E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Additive.toNNNorm : NNNorm (Additive E) := ‹NNNorm E›
/-
**Multiplicative.toNNNorm** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiplicative.toNNNorm : NNNorm (Multiplicative E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Multiplicative.toNNNorm : NNNorm (Multiplicative E) := ‹NNNorm E›
/-
**nnnorm_toMul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {E : Type u_2} [inst : NNNorm E] (x : Additive E), ‖Additive.toMul x‖₊ =
 ‖x‖₊
参数：x : Additive E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma nnnorm_toMul (x : Additive E) : ‖(x.toMul : E)‖₊ = ‖x‖₊ := rfl
/-
**nnnorm_ofMul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {E : Type u_2} [inst : NNNorm E] (x : E), ‖Additive.ofMul x‖₊ = ‖x‖₊
参数：x : E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma nnnorm_ofMul (x : E) : ‖ofMul x‖₊ = ‖x‖₊ := rfl
/-
**nnnorm_toAdd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {E : Type u_2} [inst : NNNorm E] (x : Multiplicative E), ‖Multiplicative
.toAdd x‖₊ = ‖x‖₊
参数：x : Multiplicative E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma nnnorm_toAdd (x : Multiplicative E) : ‖(x.toAdd : E)‖₊ = ‖x‖₊ := rfl
/-
**nnnorm_ofAdd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {E : Type u_2} [inst : NNNorm E] (x : E), ‖Multiplicative.ofAdd x‖₊ = ‖x
‖₊
参数：x : E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma nnnorm_ofAdd (x : E) : ‖ofAdd x‖₊ = ‖x‖₊ := rfl

end NNNorm

/-
**Additive.seminormedAddGroup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Additive.seminormedAddGroup [SeminormedGroup E] : SeminormedAddGroup (Addi
tive E) where dist_eq x y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Additive.seminormedAddGroup [SeminormedGroup E] : SeminormedAddGroup (Additive E) where
  dist_eq x y := dist_eq_norm_inv_mul x.toMul y.toMul
/-
**Multiplicative.seminormedGroup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiplicative.seminormedGroup [SeminormedAddGroup E] : SeminormedGroup (M
ultiplicative E) where dist_eq x y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Multiplicative.seminormedGroup [SeminormedAddGroup E] :
    SeminormedGroup (Multiplicative E) where
  dist_eq x y := dist_eq_norm_neg_add x.toAdd y.toAdd
/-
**Additive.seminormedCommGroup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Additive.seminormedCommGroup [SeminormedCommGroup E] : SeminormedAddCommGr
oup (Additive E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Additive.seminormedCommGroup [SeminormedCommGroup E] :
    SeminormedAddCommGroup (Additive E) :=
  { Additive.seminormedAddGroup with
    add_comm := add_comm }
/-
**Multiplicative.seminormedAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiplicative.seminormedAddCommGroup [SeminormedAddCommGroup E] : Seminor
medCommGroup (Multiplicative E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Multiplicative.seminormedAddCommGroup [SeminormedAddCommGroup E] :
    SeminormedCommGroup (Multiplicative E) :=
  { Multiplicative.seminormedGroup with
    mul_comm := mul_comm }
/-
**Additive.normedAddGroup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Additive.normedAddGroup [NormedGroup E] : NormedAddGroup (Additive E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Additive.normedAddGroup [NormedGroup E] : NormedAddGroup (Additive E) :=
  { Additive.seminormedAddGroup with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }
/-
**Multiplicative.normedGroup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiplicative.normedGroup [NormedAddGroup E] : NormedGroup (Multiplicativ
e E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Multiplicative.normedGroup [NormedAddGroup E] : NormedGroup (Multiplicative E) :=
  { Multiplicative.seminormedGroup with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }
/-
**Additive.normedAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Additive.normedAddCommGroup [NormedCommGroup E] : NormedAddCommGroup (Addi
tive E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Additive.normedAddCommGroup [NormedCommGroup E] : NormedAddCommGroup (Additive E) :=
  { Additive.seminormedAddGroup with
    add_comm := add_comm
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }
/-
**Multiplicative.normedCommGroup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiplicative.normedCommGroup [NormedAddCommGroup E] : NormedCommGroup (M
ultiplicative E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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

/-
**OrderDual.toNorm** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OrderDual.toNorm : Norm Eᵒᵈ where norm x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance OrderDual.toNorm : Norm Eᵒᵈ where
  norm x := ‖ofDual x‖
/-
**norm_toDual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {E : Type u_2} [inst : Norm E] (x : E), ‖OrderDual.toDual x‖ = ‖x‖
参数：x : E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma norm_toDual (x : E) : ‖toDual x‖ = ‖x‖ := rfl
/-
**norm_ofDual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {E : Type u_2} [inst : Norm E] (x : Eᵒᵈ), ‖OrderDual.ofDual x‖ = ‖x‖
参数：x : Eᵒᵈ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma norm_ofDual (x : Eᵒᵈ) : ‖ofDual x‖ = ‖x‖ := rfl

end Norm

section NNNorm
variable [NNNorm E]

/-
**OrderDual.toNNNorm** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OrderDual.toNNNorm : NNNorm Eᵒᵈ where nnnorm x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance OrderDual.toNNNorm : NNNorm Eᵒᵈ where
  nnnorm x := ‖ofDual x‖₊
/-
**nnnorm_toDual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {E : Type u_2} [inst : NNNorm E] (x : E), ‖OrderDual.toDual x‖₊ = ‖x‖₊
参数：x : E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma nnnorm_toDual (x : E) : ‖toDual x‖₊ = ‖x‖₊ := rfl
/-
**nnnorm_ofDual** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {E : Type u_2} [inst : NNNorm E] (x : Eᵒᵈ), ‖OrderDual.ofDual x‖₊ = ‖x‖₊
参数：x : Eᵒᵈ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma nnnorm_ofDual (x : Eᵒᵈ) : ‖ofDual x‖₊ = ‖x‖₊ := rfl

end NNNorm

namespace OrderDual

-- See note [lower instance priority]
@[to_additive]
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) seminormedGroup [SeminormedGroup E] : SeminormedGroup Eᵒᵈ :=
  inferInstanceAs <| SeminormedGroup E

-- See note [lower instance priority]
@[to_additive]
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) seminormedCommGroup [SeminormedCommGroup E] : SeminormedCommGroup Eᵒᵈ :=
  inferInstanceAs <| SeminormedCommGroup E

-- See note [lower instance priority]
@[to_additive]
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) normedGroup [NormedGroup E] : NormedGroup Eᵒᵈ :=
  inferInstanceAs <| NormedGroup E

-- See note [lower instance priority]
@[to_additive]
/-
**OrderDual.** 是 Mathlib 中的一个实例，位于命名空间 `OrderDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) normedCommGroup [NormedCommGroup E] : NormedCommGroup Eᵒᵈ :=
  inferInstanceAs <| NormedCommGroup E

end OrderDual
end OrderDual

/-! ### Binary product of normed groups -/

section Norm
variable [Norm E] [Norm F] {x : E × F} {r : ℝ}

/-
**Prod.toNorm** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.toNorm : Norm (E × F) where norm x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Prod.toNorm : Norm (E × F) where norm x := ‖x.1‖ ⊔ ‖x.2‖
/-
**Prod.norm_def** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Prod.norm_def (x : E × F) : ‖x‖ = max ‖x.1‖ ‖x.2‖
参数：x : E × F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Prod.norm_def (x : E × F) : ‖x‖ = max ‖x.1‖ ‖x.2‖ := rfl
/-
**Prod.norm_mk** 是 Mathlib 中的一个定理，位于命名空间 `Prod`。
形式化陈述：∀ {E : Type u_2} {F : Type u_3} [inst : Norm E] [inst_1 : Norm F] (x : E) 
(y : F), ‖(x, y)‖ = max ‖x‖ ‖y‖
参数：x : E；y : F；x, y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma Prod.norm_mk (x : E) (y : F) : ‖(x, y)‖ = max ‖x‖ ‖y‖ := rfl
/-
**norm_fst_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：norm_fst_le (x : E × F) : ‖x.1‖ <= ‖x‖
参数：x : E × F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
-/
lemma norm_fst_le (x : E × F) : ‖x.1‖ ≤ ‖x‖ := le_max_left _ _
/-
**norm_snd_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：norm_snd_le (x : E × F) : ‖x.2‖ <= ‖x‖
参数：x : E × F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
-/
lemma norm_snd_le (x : E × F) : ‖x.2‖ ≤ ‖x‖ := le_max_right _ _
/-
**norm_prod_le_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：norm_prod_le_iff : ‖x‖ <= r ↔ ‖x.1‖ <= r ∧ ‖x.2‖ <= r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `max_le_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, max a b ≤
 c ↔ a ≤ c ∧ b ≤ c
-/
lemma norm_prod_le_iff : ‖x‖ ≤ r ↔ ‖x.1‖ ≤ r ∧ ‖x.2‖ ≤ r := max_le_iff

end Norm

section SeminormedGroup
variable [SeminormedGroup E] [SeminormedGroup F]

/-- Product of seminormed groups, using the sup norm. -/
@[to_additive /-- Product of seminormed groups, using the sup norm. -/]
/-
**Prod.seminormedGroup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.seminormedGroup : SeminormedGroup (E × F) where dist_eq x y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Product of seminormed groups, using the sup norm.
-/
instance Prod.seminormedGroup : SeminormedGroup (E × F) where
  dist_eq x y := by simp [Prod.norm_def, Prod.dist_eq, dist_eq_norm_inv_mul]

/-- Multiplicative version of `Prod.nnnorm_def`.
Earlier, this name was used for the additive version. -/
@[to_additive Prod.nnnorm_def /-- Additive version of `Prod.nnnorm_def'`.
Earlier, this name was used for the multiplicative version. -/]
/-
**Prod.nnnorm_def'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Prod.nnnorm_def' (x : E × F) : ‖x‖₊ = max ‖x.1‖₊ ‖x.2‖₊
参数：x : E × F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Prod.nnnorm_def' (x : E × F) : ‖x‖₊ = max ‖x.1‖₊ ‖x.2‖₊ := rfl

/-- Multiplicative version of `Prod.nnnorm_mk`. -/
@[to_additive (attr := simp) Prod.nnnorm_mk /-- Additive version of `Prod.nnnorm_mk'`. -/]
/-
**Prod.nnnorm_mk'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Prod.nnnorm_mk' (x : E) (y : F) : ‖(x, y)‖₊ = max ‖x‖₊ ‖y‖₊
参数：x : E；y : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplicative version of `Prod.nnnorm_mk`.
-/
lemma Prod.nnnorm_mk' (x : E) (y : F) : ‖(x, y)‖₊ = max ‖x‖₊ ‖y‖₊ := rfl

end SeminormedGroup

namespace Prod

/-- Product of seminormed groups, using the sup norm. -/
@[to_additive /-- Product of seminormed groups, using the sup norm. -/]
/-
**Prod.seminormedCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：seminormedCommGroup [SeminormedCommGroup E] [SeminormedCommGroup F] : Semi
normedCommGroup (E × F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Product of seminormed groups, using the sup norm.
-/
instance seminormedCommGroup [SeminormedCommGroup E] [SeminormedCommGroup F] :
    SeminormedCommGroup (E × F) :=
  { Prod.seminormedGroup with
    mul_comm := mul_comm }

/-- Product of normed groups, using the sup norm. -/
@[to_additive /-- Product of normed groups, using the sup norm. -/]
/-
**Prod.normedGroup** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：normedGroup [NormedGroup E] [NormedGroup F] : NormedGroup (E × F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Product of normed groups, using the sup norm.
-/
instance normedGroup [NormedGroup E] [NormedGroup F] : NormedGroup (E × F) :=
  { Prod.seminormedGroup with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

/-- Product of normed groups, using the sup norm. -/
@[to_additive /-- Product of normed groups, using the sup norm. -/]
/-
**Prod.normedCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `Prod`。
形式化陈述：normedCommGroup [NormedCommGroup E] [NormedCommGroup F] : NormedCommGroup 
(E × F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Product of normed groups, using the sup norm.
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
variable [∀ i, SeminormedGroup (G i)] [SeminormedGroup E] (f : ∀ i, G i) {x : ∀ i, G i} {r : ℝ}

/-- Finite product of seminormed groups, using the sup norm. -/
@[to_additive /-- Finite product of seminormed groups, using the sup norm. -/]
/-
**Pi.seminormedGroup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.seminormedGroup : SeminormedGroup (forall i, G i) where norm f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Finite product of seminormed groups, using the sup norm.
-/
instance Pi.seminormedGroup : SeminormedGroup (∀ i, G i) where
  norm f := ↑(Finset.univ.sup fun b => ‖f b‖₊)
  dist_eq x y :=
    congr_arg (toReal : ℝ≥0 → ℝ) <|
      congr_arg (Finset.sup Finset.univ) <| funext fun a =>
        show nndist (x a) (y a) = ‖(x a)⁻¹ * y a‖₊ from nndist_eq_nnnorm_inv_mul (x a) (y a)

@[to_additive Pi.norm_def]
/-
**Pi.norm_def'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Pi.norm_def' : ‖f‖ = ↑(Finset.univ.sup fun b => ‖f b‖₊)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Pi.norm_def' : ‖f‖ = ↑(Finset.univ.sup fun b => ‖f b‖₊) := rfl

@[to_additive Pi.nnnorm_def]
/-
**Pi.nnnorm_def'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Pi.nnnorm_def' : ‖f‖₊ = Finset.univ.sup fun b => ‖f b‖₊
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.eta`：∀ {α : Sort u} {p : α → Prop} (a : { x // p x }) (h : p ↑a)
, ⟨↑a, h⟩ = a
· 使用定理 `norm_nonneg'`：norm_nonneg' (a : E) : 0 <= ‖a‖
-/
lemma Pi.nnnorm_def' : ‖f‖₊ = Finset.univ.sup fun b => ‖f b‖₊ := Subtype.eta _ _

/-- The seminorm of an element in a product space is `≤ r` if and only if the norm of each
component is. -/
@[to_additive pi_norm_le_iff_of_nonneg /-- The seminorm of an element in a product space is `≤ r` if
and only if the norm of each component is. -/]
/-
**pi_norm_le_iff_of_nonneg'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pi_norm_le_iff_of_nonneg' (hr : 0 <= r) : ‖x‖ <= r ↔ forall i, ‖x i‖ <= r
参数：hr : 0 <= r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `dist_pi_le_iff`：dist_pi_le_iff {f g : forall b, X b} {r : Real} (hr : 0 
<= r) : dist f g <= r ↔ forall b, dist (f b) (g b) <= r
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma pi_norm_le_iff_of_nonneg' (hr : 0 ≤ r) : ‖x‖ ≤ r ↔ ∀ i, ‖x i‖ ≤ r := by
  simp only [← dist_one_right, dist_pi_le_iff hr, Pi.one_apply]

@[to_additive pi_nnnorm_le_iff]
/-
**pi_nnnorm_le_iff'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pi_nnnorm_le_iff' {r : Real>=0} : ‖x‖₊ <= r ↔ forall i, ‖x i‖₊ <= r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `pi_norm_le_iff_of_nonneg'`：pi_norm_le_iff_of_nonneg' (hr : 0 <= r) : ‖x‖
 <= r ↔ forall i, ‖x i‖ <= r
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
-/
lemma pi_nnnorm_le_iff' {r : ℝ≥0} : ‖x‖₊ ≤ r ↔ ∀ i, ‖x i‖₊ ≤ r :=
  pi_norm_le_iff_of_nonneg' r.coe_nonneg

@[to_additive pi_norm_le_iff_of_nonempty]
/-
**pi_norm_le_iff_of_nonempty'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pi_norm_le_iff_of_nonempty' [Nonempty ι] : ‖f‖ <= r ↔ forall b, ‖f b‖ <= r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `pi_norm_le_iff_of_nonneg'`：pi_norm_le_iff_of_nonneg' (hr : 0 <= r) : ‖x‖
 <= r ↔ forall i, ‖x i‖ <= r
· 使用定理 `iff_of_false`：∀ {a b : Prop}, ¬a → ¬b → (a ↔ b)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `norm_nonneg'`：norm_nonneg' (a : E) : 0 <= ‖a‖
-/
lemma pi_norm_le_iff_of_nonempty' [Nonempty ι] : ‖f‖ ≤ r ↔ ∀ b, ‖f b‖ ≤ r := by
  by_cases hr : 0 ≤ r
  · exact pi_norm_le_iff_of_nonneg' hr
  · exact
      iff_of_false (fun h => hr <| (norm_nonneg' _).trans h) fun h =>
        hr <| (norm_nonneg' _).trans <| h <| Classical.arbitrary _

/-- The seminorm of an element in a product space is `< r` if and only if the norm of each
component is. -/
@[to_additive pi_norm_lt_iff /-- The seminorm of an element in a product space is `< r` if and only
if the norm of each component is. -/]
/-
**pi_norm_lt_iff'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pi_norm_lt_iff' (hr : 0 < r) : ‖x‖ < r ↔ forall i, ‖x i‖ < r
参数：hr : 0 < r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `dist_pi_lt_iff`：dist_pi_lt_iff {f g : forall b, X b} {r : Real} (hr : 0 
< r) : dist f g < r ↔ forall b, dist (f b) (g b) < r
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma pi_norm_lt_iff' (hr : 0 < r) : ‖x‖ < r ↔ ∀ i, ‖x i‖ < r := by
  simp only [← dist_one_right, dist_pi_lt_iff hr, Pi.one_apply]

@[to_additive pi_nnnorm_lt_iff]
/-
**pi_nnnorm_lt_iff'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pi_nnnorm_lt_iff' {r : Real>=0} (hr : 0 < r) : ‖x‖₊ < r ↔ forall i, ‖x i‖₊
 < r
参数：hr : 0 < r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `pi_norm_lt_iff'`：pi_norm_lt_iff' (hr : 0 < r) : ‖x‖ < r ↔ forall i, ‖x i
‖ < r
-/
lemma pi_nnnorm_lt_iff' {r : ℝ≥0} (hr : 0 < r) : ‖x‖₊ < r ↔ ∀ i, ‖x i‖₊ < r :=
  pi_norm_lt_iff' hr

@[to_additive norm_le_pi_norm]
/-
**norm_le_pi_norm'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：norm_le_pi_norm' (i : ι) : ‖f i‖ <= ‖f‖
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `pi_norm_le_iff_of_nonneg'`：pi_norm_le_iff_of_nonneg' (hr : 0 <= r) : ‖x‖
 <= r ↔ forall i, ‖x i‖ <= r
· 使用定理 `norm_nonneg'`：norm_nonneg' (a : E) : 0 <= ‖a‖
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma norm_le_pi_norm' (i : ι) : ‖f i‖ ≤ ‖f‖ :=
  (pi_norm_le_iff_of_nonneg' <| norm_nonneg' _).1 le_rfl i

@[to_additive nnnorm_le_pi_nnnorm]
/-
**nnnorm_le_pi_nnnorm'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nnnorm_le_pi_nnnorm' (i : ι) : ‖f i‖₊ <= ‖f‖₊
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `norm_le_pi_norm'`：norm_le_pi_norm' (i : ι) : ‖f i‖ <= ‖f‖
-/
lemma nnnorm_le_pi_nnnorm' (i : ι) : ‖f i‖₊ ≤ ‖f‖₊ :=
  norm_le_pi_norm' _ i

@[to_additive pi_norm_const_le]
/-
**pi_norm_const_le'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pi_norm_const_le' (a : E) : ‖fun _ : ι => a‖ <= ‖a‖
参数：a : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `pi_norm_le_iff_of_nonneg'`：pi_norm_le_iff_of_nonneg' (hr : 0 <= r) : ‖x‖
 <= r ↔ forall i, ‖x i‖ <= r
· 使用定理 `norm_nonneg'`：norm_nonneg' (a : E) : 0 <= ‖a‖
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma pi_norm_const_le' (a : E) : ‖fun _ : ι => a‖ ≤ ‖a‖ :=
  (pi_norm_le_iff_of_nonneg' <| norm_nonneg' _).2 fun _ => le_rfl

@[to_additive pi_nnnorm_const_le]
/-
**pi_nnnorm_const_le'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pi_nnnorm_const_le' (a : E) : ‖fun _ : ι => a‖₊ <= ‖a‖₊
参数：a : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `pi_norm_const_le'`：pi_norm_const_le' (a : E) : ‖fun _ : ι => a‖ <= ‖a‖
-/
lemma pi_nnnorm_const_le' (a : E) : ‖fun _ : ι => a‖₊ ≤ ‖a‖₊ :=
  pi_norm_const_le' _

@[to_additive (attr := simp) pi_norm_const]
/-
**pi_norm_const'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pi_norm_const' [Nonempty ι] (a : E) : ‖fun _i : ι => a‖ = ‖a‖
参数：a : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `dist_pi_const`：dist_pi_const [Nonempty β] (a b : α) : (dist (fun _ : β =
> a) fun _ => b) = dist a b
-/
lemma pi_norm_const' [Nonempty ι] (a : E) : ‖fun _i : ι => a‖ = ‖a‖ := by
  simpa only [← dist_one_right] using! dist_pi_const a 1

@[to_additive (attr := simp) pi_nnnorm_const]
/-
**pi_nnnorm_const'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pi_nnnorm_const' [Nonempty ι] (a : E) : ‖fun _i : ι => a‖₊ = ‖a‖₊
参数：a : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用引理 `pi_norm_const'`：pi_norm_const' [Nonempty ι] (a : E) : ‖fun _i : ι => a‖ 
= ‖a‖
-/
lemma pi_nnnorm_const' [Nonempty ι] (a : E) : ‖fun _i : ι => a‖₊ = ‖a‖₊ :=
  NNReal.eq <| pi_norm_const' a

@[to_additive pi_norm_comp_le]
/-
**pi_norm_comp_le'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：pi_norm_comp_le' [Fintype F] (g : ι -> E) (f : F -> ι) : ‖g ∘ f‖ <= ‖g‖
参数：g : ι -> E；f : F -> ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pi_norm_le_iff_of_nonneg'`：pi_norm_le_iff_of_nonneg' (hr : 0 <= r) : ‖x‖
 <= r ↔ forall i, ‖x i‖ <= r
· 使用定理 `norm_nonneg'`：norm_nonneg' (a : E) : 0 <= ‖a‖
· 使用引理 `norm_le_pi_norm'`：norm_le_pi_norm' (i : ι) : ‖f i‖ <= ‖f‖
-/
lemma pi_norm_comp_le' [Fintype F] (g : ι → E) (f : F → ι) : ‖g ∘ f‖ ≤ ‖g‖ := by
  rw [pi_norm_le_iff_of_nonneg' (by positivity)]
  exact fun x ↦ norm_le_pi_norm' g (f x)

@[to_additive IsGreatest.pi_norm]
/-
**IsGreatest.pi_norm'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsGreatest.pi_norm' [Nonempty ι] (f : ι -> E) : IsGreatest (Set.range (‖f 
·‖)) ‖f‖
参数：f : ι -> E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Pi.norm_def'`：Pi.norm_def' : ‖f‖ = ↑(Finset.univ.sup fun b => ‖f b‖₊)
· 使用定理 `Finset.exists_mem_eq_sup`：exists_mem_eq_sup [OrderBot α] (s : Finset ι) 
(h : s.Nonempty) (f : ι -> α) : exists i, i in s ∧ s.sup f = f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `norm_le_pi_norm'`：norm_le_pi_norm' (i : ι) : ‖f i‖ <= ‖f‖
-/
lemma IsGreatest.pi_norm' [Nonempty ι] (f : ι → E) : IsGreatest (Set.range (‖f ·‖)) ‖f‖ := by
  constructor
  · rw [Pi.norm_def' f]
    obtain ⟨x, -, hx⟩ := (Finset.univ (α := ι)).exists_mem_eq_sup (by simp) (‖f ·‖₊)
    simp [hx]
  · rintro - ⟨x, rfl⟩
    exact norm_le_pi_norm' f x

@[to_additive Function.Surjective.pi_norm_comp]
/-
**Function.Surjective.pi_norm_comp'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Function.Surjective.pi_norm_comp' [Fintype F] {f : ι -> F} (hf : Function.
Surjective f) (g : F -> E) : ‖g ∘ f‖ = ‖g‖
参数：hf : Function.Surjective f；g : F -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `Function.isEmpty`：∀ {α : Sort u} {β : Sort v} [IsEmpty β] (f : α → β), I
sEmpty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `norm_one'`：norm_one' : ‖(1 : E)‖ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `pi_norm_comp_le'`：pi_norm_comp_le' [Fintype F] (g : ι -> E) (f : F -> ι)
 : ‖g ∘ f‖ <= ‖g‖
· 使用引理 `IsGreatest.pi_norm'`：IsGreatest.pi_norm' [Nonempty ι] (f : ι -> E) : IsG
reatest (Set.range (‖f ·‖)) ‖f‖
· 使用引理 `norm_le_pi_norm'`：norm_le_pi_norm' (i : ι) : ‖f i‖ <= ‖f‖
-/
lemma Function.Surjective.pi_norm_comp' [Fintype F] {f : ι → F} (hf : Function.Surjective f)
    (g : F → E) : ‖g ∘ f‖ = ‖g‖ := by
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
/-
**Pi.sum_norm_apply_le_norm'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Pi.sum_norm_apply_le_norm' : ∑ i, ‖f i‖ <= Fintype.card ι • ‖f‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_le_card_nsmul`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCom
mMonoid N] [inst_1 : Preorder N] [AddLeftMono N] (s : Finset ι)   (f : ι → N) (n
 : N), (∀ x ∈ …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `norm_le_pi_norm'`：norm_le_pi_norm' (i : ι) : ‖f i‖ <= ‖f‖
-/
lemma Pi.sum_norm_apply_le_norm' : ∑ i, ‖f i‖ ≤ Fintype.card ι • ‖f‖ :=
  Finset.sum_le_card_nsmul _ _ _ fun i _hi => norm_le_pi_norm' _ i

/-- The $L^1$ norm is less than the $L^\infty$ norm scaled by the cardinality. -/
@[to_additive Pi.sum_nnnorm_apply_le_nnnorm /-- The $L^1$ norm is less than the $L^\infty$ norm
scaled by the cardinality. -/]
/-
**Pi.sum_nnnorm_apply_le_nnnorm'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Pi.sum_nnnorm_apply_le_nnnorm' : ∑ i, ‖f i‖₊ <= Fintype.card ι • ‖f‖₊
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `NNReal.coe_sum`：coe_sum (s : Finset ι) (f : ι -> Real>=0) : ∑ i in s, f 
i = ∑ i in s, (f i : Real)
· 使用引理 `Pi.sum_norm_apply_le_norm'`：Pi.sum_norm_apply_le_norm' : ∑ i, ‖f i‖ <= F
intype.card ι • ‖f‖
-/
lemma Pi.sum_nnnorm_apply_le_nnnorm' : ∑ i, ‖f i‖₊ ≤ Fintype.card ι • ‖f‖₊ :=
  (NNReal.coe_sum ..).trans_le <| Pi.sum_norm_apply_le_norm' _

end SeminormedGroup

/-- Finite product of seminormed groups, using the sup norm. -/
@[to_additive /-- Finite product of seminormed groups, using the sup norm. -/]
/-
**Pi.seminormedCommGroup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.seminormedCommGroup [forall i, SeminormedCommGroup (G i)] : SeminormedC
ommGroup (forall i, G i)
参数：G i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Finite product of seminormed groups, using the sup norm.
-/
instance Pi.seminormedCommGroup [∀ i, SeminormedCommGroup (G i)] : SeminormedCommGroup (∀ i, G i) :=
  { Pi.seminormedGroup with
    mul_comm := mul_comm }

/-- Finite product of normed groups, using the sup norm. -/
@[to_additive /-- Finite product of seminormed groups, using the sup norm. -/]
/-
**Pi.normedGroup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.normedGroup [forall i, NormedGroup (G i)] : NormedGroup (forall i, G i)
参数：G i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Finite product of normed groups, using the sup norm.
-/
instance Pi.normedGroup [∀ i, NormedGroup (G i)] : NormedGroup (∀ i, G i) :=
  { Pi.seminormedGroup with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

/-- Finite product of normed groups, using the sup norm. -/
@[to_additive /-- Finite product of seminormed groups, using the sup norm. -/]
/-
**Pi.normedCommGroup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.normedCommGroup [forall i, NormedCommGroup (G i)] : NormedCommGroup (fo
rall i, G i)
参数：G i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Finite product of normed groups, using the sup norm.
-/
instance Pi.normedCommGroup [∀ i, NormedCommGroup (G i)] : NormedCommGroup (∀ i, G i) :=
  { Pi.seminormedGroup with
    mul_comm := mul_comm
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }
/-
**Pi.nnnorm_single** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Pi.nnnorm_single [DecidableEq ι] [forall i, NormedAddCommGroup (G i)] {i :
 ι} (y : G i) : ‖Pi.single i y‖₊ = ‖y‖₊
参数：G i；y : G i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.apply_single`：∀ {ι : Type u_1} {M : ι → Type u_6} {N : ι → Type u_7} 
[inst : (i : ι) → Zero (M i)] [inst_1 : (i : ι) → Zero (N i)]   [inst_2 : Decida
bleEq…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nnnorm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖₊ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Pi.nnnorm_def`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : Fintype ι] [i
nst_1 : (i : ι) → SeminormedAddGroup (G i)]   (f : (i : ι) → G i), ‖f‖₊ = Finset
.un…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
· 使用定理 `Finset.sup_ite`：sup_ite (p : β -> Prop) [DecidablePred p] : (s.sup fun i
 => ite (p i) (f i) (g i)) = (s.filter p).sup f ⊔ (s.filter fun i => ¬p i).sup g
· 使用定理 `Finset.filter_eq'`：filter_eq' [DecidableEq β] (s : Finset β) (b : β) : (
s.filter fun a => a = b) = ite (b in s) {b} ∅
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Finset.sup_singleton`：sup_singleton {b : β} : ({b} : Finset β).sup f = f
 b
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
theorem Pi.nnnorm_single [DecidableEq ι] [∀ i, NormedAddCommGroup (G i)] {i : ι} (y : G i) :
    ‖Pi.single i y‖₊ = ‖y‖₊ := by
  have H : ∀ b, ‖single i y b‖₊ = single (M := fun _ ↦ ℝ≥0) i ‖y‖₊ b := by
    intro b
    refine Pi.apply_single (fun i (x : G i) ↦ ‖x‖₊) ?_ i y b
    simp
  simp [Pi.nnnorm_def, H, Pi.single_apply, Finset.sup_ite, Finset.filter_eq']
/-
**Pi.enorm_single** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Pi.enorm_single [DecidableEq ι] [forall i, NormedAddCommGroup (G i)] {i : 
ι} (y : G i) : ‖Pi.single i y‖ₑ = ‖y‖ₑ
参数：G i；y : G i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.nnnorm_single`：Pi.nnnorm_single [DecidableEq ι] [forall i, NormedAddC
ommGroup (G i)] {i : ι} (y : G i) : ‖Pi.single i y‖₊ = ‖y‖₊
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Pi.enorm_single [DecidableEq ι] [∀ i, NormedAddCommGroup (G i)] {i : ι} (y : G i) :
    ‖Pi.single i y‖ₑ = ‖y‖ₑ := by simp [enorm, Pi.nnnorm_single]
/-
**Pi.norm_single** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Pi.norm_single [DecidableEq ι] [forall i, NormedAddCommGroup (G i)] {i : ι
} (y : G i) : ‖Pi.single i y‖ = ‖y‖
参数：G i；y : G i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Pi.nnnorm_single`：Pi.nnnorm_single [DecidableEq ι] [forall i, NormedAddC
ommGroup (G i)] {i : ι} (y : G i) : ‖Pi.single i y‖₊ = ‖y‖₊
-/
theorem Pi.norm_single [DecidableEq ι] [∀ i, NormedAddCommGroup (G i)] {i : ι} (y : G i) :
    ‖Pi.single i y‖ = ‖y‖ :=
  congr_arg Subtype.val <| Pi.nnnorm_single y

end Pi

/-! ### Multiplicative opposite -/

namespace MulOpposite

/-- The (additive) norm on the multiplicative opposite is the same as the norm on the original type.

Note that we do not provide this more generally as `Norm Eᵐᵒᵖ`, as this is not always a good
choice of norm in the multiplicative `SeminormedGroup E` case.

We could repeat this instance to provide a `[SeminormedGroup E] : SeminormedGroup Eᵃᵒᵖ` instance,
but that case would likely never be used.
-/
/-
**MulOpposite.instSeminormedAddGroup** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instSeminormedAddGroup [SeminormedAddGroup E] : SeminormedAddGroup Eᵐᵒᵖ wh
ere __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (additive) norm on the multiplicative opposite is the same as the norm on th
e original type.

Note that we do not provide this more generally as `Norm Eᵐᵒᵖ`, as this is not a
lways a good
choice of norm in the multiplicative `SeminormedGroup E` case.

We could repeat this instance to provide a `[SeminormedGroup E] : SeminormedGrou
p Eᵃᵒᵖ` instance,
but that case would likely never be used.
-/
instance instSeminormedAddGroup [SeminormedAddGroup E] : SeminormedAddGroup Eᵐᵒᵖ where
  __ := instPseudoMetricSpace
  norm x := ‖x.unop‖
  dist_eq _ _ := dist_eq_norm_neg_add _ _
/-
**MulOpposite.norm_op** 是 Mathlib 中的一个引理，位于命名空间 `MulOpposite`。
形式化陈述：norm_op [SeminormedAddGroup E] (a : E) : ‖MulOpposite.op a‖ = ‖a‖
参数：a : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma norm_op [SeminormedAddGroup E] (a : E) : ‖MulOpposite.op a‖ = ‖a‖ := rfl
/-
**MulOpposite.norm_unop** 是 Mathlib 中的一个引理，位于命名空间 `MulOpposite`。
形式化陈述：norm_unop [SeminormedAddGroup E] (a : Eᵐᵒᵖ) : ‖MulOpposite.unop a‖ = ‖a‖
参数：a : Eᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma norm_unop [SeminormedAddGroup E] (a : Eᵐᵒᵖ) : ‖MulOpposite.unop a‖ = ‖a‖ := rfl
/-
**MulOpposite.nnnorm_op** 是 Mathlib 中的一个引理，位于命名空间 `MulOpposite`。
形式化陈述：nnnorm_op [SeminormedAddGroup E] (a : E) : ‖MulOpposite.op a‖₊ = ‖a‖₊
参数：a : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma nnnorm_op [SeminormedAddGroup E] (a : E) : ‖MulOpposite.op a‖₊ = ‖a‖₊ := rfl
/-
**MulOpposite.nnnorm_unop** 是 Mathlib 中的一个引理，位于命名空间 `MulOpposite`。
形式化陈述：nnnorm_unop [SeminormedAddGroup E] (a : Eᵐᵒᵖ) : ‖MulOpposite.unop a‖₊ = ‖a
‖₊
参数：a : Eᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma nnnorm_unop [SeminormedAddGroup E] (a : Eᵐᵒᵖ) : ‖MulOpposite.unop a‖₊ = ‖a‖₊ := rfl
/-
**MulOpposite.instNormedAddGroup** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instNormedAddGroup [NormedAddGroup E] : NormedAddGroup Eᵐᵒᵖ where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNormedAddGroup [NormedAddGroup E] : NormedAddGroup Eᵐᵒᵖ where
  __ := instMetricSpace
  __ := instSeminormedAddGroup
/-
**MulOpposite.instSeminormedAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`
。
形式化陈述：instSeminormedAddCommGroup [SeminormedAddCommGroup E] : SeminormedAddCommG
roup Eᵐᵒᵖ where dist_eq _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSeminormedAddCommGroup [SeminormedAddCommGroup E] : SeminormedAddCommGroup Eᵐᵒᵖ where
  dist_eq _ _ := dist_eq_norm_neg_add _ _
/-
**MulOpposite.instNormedAddCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `MulOpposite`。
形式化陈述：instNormedAddCommGroup [NormedAddCommGroup E] : NormedAddCommGroup Eᵐᵒᵖ wh
ere __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNormedAddCommGroup [NormedAddCommGroup E] : NormedAddCommGroup Eᵐᵒᵖ where
  __ := instSeminormedAddCommGroup
  __ := instNormedAddGroup

end MulOpposite

