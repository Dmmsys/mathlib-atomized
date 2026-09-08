/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Logic.Function.ULift
public import Mathlib.Order.Basic

/-! # Ordered structures on `ULift.{v} α`

Once these basic instances are setup, the instances of more complex typeclasses should live next to
the corresponding `Prod` instances.
-/

public section

namespace ULift

open Batteries

universe v u

variable {α : Type u}

/-
**ULift.** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LE α] : LE (ULift.{v} α) where le x y := x.down ≤ y.down
/-
**ULift.up_le** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：∀ {α : Type u} [inst : LE α] {a b : α}, { down := a } ≤ { down := b } ↔ a 
≤ b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp, to_dual self] theorem up_le [LE α] {a b : α} : up a ≤ up b ↔ a ≤ b := Iff.rfl
/-
**ULift.down_le** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：∀ {α : Type u} [inst : LE α] {a b : ULift.{u_1, u} α}, a.down ≤ b.down ↔ a
 ≤ b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp, to_dual self] theorem down_le [LE α] {a b : ULift α} : down a ≤ down b ↔ a ≤ b := Iff.rfl
/-
**ULift.** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LT α] : LT (ULift.{v} α) where lt x y := x.down < y.down
/-
**ULift.up_lt** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：∀ {α : Type u} [inst : LT α] {a b : α}, { down := a } < { down := b } ↔ a 
< b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp, to_dual self] theorem up_lt [LT α] {a b : α} : up a < up b ↔ a < b := Iff.rfl
/-
**ULift.down_lt** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：∀ {α : Type u} [inst : LT α] {a b : ULift.{u_1, u} α}, a.down < b.down ↔ a
 < b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp, to_dual self] theorem down_lt [LT α] {a b : ULift α} : down a < down b ↔ a < b := Iff.rfl
/-
**ULift.** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [BEq α] : BEq (ULift.{v} α) where beq x y := x.down == y.down
/-
**ULift.up_beq** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：∀ {α : Type u} [inst : BEq α] (a b : α), ({ down := a } == { down := b }) 
= (a == b)
参数：a b : α；{ down := a } == { down := b }；a == b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem up_beq [BEq α] (a b : α) : (up a == up b) = (a == b) := rfl
/-
**ULift.down_beq** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：∀ {α : Type u} [inst : BEq α] (a b : ULift.{u_1, u} α), (a.down == b.down)
 = (a == b)
参数：a b : ULift.{u_1, u} α；a.down == b.down；a == b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem down_beq [BEq α] (a b : ULift α) : (down a == down b) = (a == b) := rfl
/-
**ULift.** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Ord α] : Ord (ULift.{v} α) where compare x y := compare x.down y.down
/-
**ULift.up_compare** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：∀ {α : Type u} [inst : Ord α] (a b : α), compare { down := a } { down := b
 } = compare a b
参数：a b : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem up_compare [Ord α] (a b : α) : compare (up a) (up b) = compare a b := rfl
/-
**ULift.down_compare** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：∀ {α : Type u} [inst : Ord α] (a b : ULift.{u_1, u} α), compare a.down b.d
own = compare a b
参数：a b : ULift.{u_1, u} α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem down_compare [Ord α] (a b : ULift α) : compare (down a) (down b) = compare a b :=
  rfl

@[to_dual]
/-
**ULift.** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Max α] : Max (ULift.{v} α) where max x y := up <| x.down ⊔ y.down

@[to_dual (attr := simp)]
/-
**ULift.up_sup** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：up_sup [Max α] (a b : α) : up (a ⊔ b) = up a ⊔ up b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem up_sup [Max α] (a b : α) : up (a ⊔ b) = up a ⊔ up b := rfl

@[to_dual (attr := simp)]
/-
**ULift.down_sup** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：down_sup [Max α] (a b : ULift α) : down (a ⊔ b) = down a ⊔ down b
参数：a b : ULift α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem down_sup [Max α] (a b : ULift α) : down (a ⊔ b) = down a ⊔ down b := rfl
/-
**ULift.** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SDiff α] : SDiff (ULift.{v} α) where sdiff x y := up <| x.down \ y.down
/-
**ULift.up_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：∀ {α : Type u} [inst : SDiff α] (a b : α), { down := a \ b } = { down := a
 } \ { down := b }
参数：a b : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem up_sdiff [SDiff α] (a b : α) : up (a \ b) = up a \ up b := rfl
/-
**ULift.down_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：∀ {α : Type u} [inst : SDiff α] (a b : ULift.{u_1, u} α), (a \ b).down = a
.down \ b.down
参数：a b : ULift.{u_1, u} α；a \ b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem down_sdiff [SDiff α] (a b : ULift α) : down (a \ b) = down a \ down b := rfl
/-
**ULift.** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Compl α] : Compl (ULift.{v} α) where compl x := up <| x.downᶜ
/-
**ULift.up_compl** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：∀ {α : Type u} [inst : Compl α] (a : α), { down := aᶜ } = { down := a }ᶜ
参数：a : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem up_compl [Compl α] (a : α) : up (aᶜ) = (up a)ᶜ := rfl
/-
**ULift.down_compl** 是 Mathlib 中的一个定理，位于命名空间 `ULift`。
形式化陈述：∀ {α : Type u} [inst : Compl α] (a : ULift.{u_1, u} α), aᶜ.down = a.downᶜ
参数：a : ULift.{u_1, u} α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem down_compl [Compl α] (a : ULift α) : down aᶜ = (down a)ᶜ := rfl
/-
**ULift.** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Ord α] [inst : Std.OrientedOrd α] : Std.OrientedOrd (ULift.{v} α) where
  eq_swap := inst.eq_swap
/-
**ULift.** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Ord α] [inst : Std.TransOrd α] : Std.TransOrd (ULift.{v} α) where
  isLE_trans := inst.isLE_trans
/-
**ULift.** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [BEq α] [Ord α] [inst : Std.LawfulBEqOrd α] : Std.LawfulBEqOrd (ULift.{v} α) where
  compare_eq_iff_beq := inst.compare_eq_iff_beq
/-
**ULift.** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LT α] [Ord α] [inst : Std.LawfulLTOrd α] : Std.LawfulLTOrd (ULift.{v} α) where
  eq_lt_iff_lt := inst.eq_lt_iff_lt
/-
**ULift.** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LE α] [Ord α] [inst : Std.LawfulLEOrd α] : Std.LawfulLEOrd (ULift.{v} α) where
  isLE_iff_le := inst.isLE_iff_le
/-
**ULift.** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LE α] [LT α] [BEq α] [Ord α] [inst : Std.LawfulBOrd α] :
    Std.LawfulBOrd (ULift.{v} α) where
  eq_lt_iff_lt := inst.eq_lt_iff_lt
  isLE_iff_le := inst.isLE_iff_le
/-
**ULift.** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preorder α] : Preorder (ULift.{v} α) :=
  Preorder.lift ULift.down
/-
**ULift.** 是 Mathlib 中的一个实例，位于命名空间 `ULift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [PartialOrder α] : PartialOrder (ULift.{v} α) :=
  PartialOrder.lift ULift.down ULift.down_injective

end ULift

