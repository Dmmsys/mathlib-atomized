/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
module

public import Mathlib.Control.Functor.Multivariate
public import Mathlib.Data.QPF.Multivariate.Basic

/-!
# Constant functors are QPFs

Constant functors map every type vectors to the same target type. This
is a useful device for constructing data types from more basic types
that are not actually functorial. For instance `Const n Nat` makes
`Nat` into a functor that can be used in a functor-based data type
specification.
-/

@[expose] public section


universe u

namespace MvQPF

open MvFunctor

variable (n : ℕ)

/-- Constant multivariate functor -/
@[nolint unusedArguments]
/-
**MvQPF.Const** 是 Mathlib 中的一个定义，位于命名空间 `MvQPF`。
形式化陈述：Const (A : Type*) (_v : TypeVec.{u} n) : Type _
参数：A : Type*；_v : TypeVec.{u} n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constant multivariate functor
-/
def Const (A : Type*) (_v : TypeVec.{u} n) : Type _ := A
/-
**MvQPF.Const.inhabited** 是 Mathlib 中的一个定义，位于命名空间 `MvQPF.Const`。
形式化陈述：(n : ℕ) → {A : Type u_1} → {α : TypeVec.{u_2} n} → [Inhabited A] → Inhabit
ed (MvQPF.Const n A α)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Const.inhabited {A α} [Inhabited A] : Inhabited (Const n A α) := ⟨(default : A)⟩

namespace Const

open MvPFunctor

variable {n} {A : Type u} {α β : TypeVec.{u} n} (f : α ⟹ β)

/-- Constructor for constant functor -/
/-
**MvQPF.Const.mk** 是 Mathlib 中的一个定义，位于命名空间 `MvQPF.Const`。
形式化陈述：{n : ℕ} → {A : Type u} → {α : TypeVec.{u} n} → A → MvQPF.Const n A α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for constant functor
-/
protected def mk (x : A) : Const n A α := x

/-- Destructor for constant functor -/
/-
**MvQPF.Const.get** 是 Mathlib 中的一个定义，位于命名空间 `MvQPF.Const`。
形式化陈述：{n : ℕ} → {A : Type u} → {α : TypeVec.{u} n} → MvQPF.Const n A α → A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Destructor for constant functor
-/
protected def get (x : Const n A α) : A := x

@[simp]
/-
**MvQPF.Const.mk_get** 是 Mathlib 中的一个定理，位于命名空间 `MvQPF.Const`。
形式化陈述：∀ {n : ℕ} {A : Type u} {α : TypeVec.{u} n} (x : MvQPF.Const n A α), MvQPF.
Const.mk x.get = x
参数：x : MvQPF.Const n A α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem mk_get (x : Const n A α) : Const.mk (Const.get x) = x := rfl

@[simp]
/-
**MvQPF.Const.get_mk** 是 Mathlib 中的一个定理，位于命名空间 `MvQPF.Const`。
形式化陈述：∀ {n : ℕ} {A : Type u} {α : TypeVec.{u} n} (x : A), (MvQPF.Const.mk x).get
 = x
参数：x : A；MvQPF.Const.mk x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem get_mk (x : A) : Const.get (Const.mk x : Const n A α) = x := rfl

/-- `map` for constant functor -/
/-
**MvQPF.Const.map** 是 Mathlib 中的一个定义，位于命名空间 `MvQPF.Const`。
形式化陈述：{n : ℕ} → {A : Type u} → {α β : TypeVec.{u} n} → MvQPF.Const n A α → MvQPF
.Const n A β
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`map` for constant functor
-/
protected def map : Const n A α → Const n A β := fun x => x
/-
**MvQPF.Const.MvFunctor** 是 Mathlib 中的一个实例，位于命名空间 `MvQPF.Const`。
形式化陈述：MvFunctor : MvFunctor (Const n A) where map _f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance MvFunctor : MvFunctor (Const n A) where map _f := Const.map
/-
**MvQPF.Const.map_mk** 是 Mathlib 中的一个定理，位于命名空间 `MvQPF.Const`。
形式化陈述：map_mk (x : A) : f < > Const.mk x = Const.mk x
参数：x : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_mk (x : A) : f <$$> Const.mk x = Const.mk x := rfl
/-
**MvQPF.Const.get_map** 是 Mathlib 中的一个定理，位于命名空间 `MvQPF.Const`。
形式化陈述：get_map (x : (Const n A) α) : Const.get (f <$$> x) = Const.get x
参数：x : (Const n A) α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem get_map (x : (Const n A) α) : Const.get (f <$$> x) = Const.get x := rfl
/-
**MvQPF.Const.mvqpf** 是 Mathlib 中的一个实例，位于命名空间 `MvQPF.Const`。
形式化陈述：mvqpf : @MvQPF _ (Const n A) where P
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPFunctor.const.get_map`：∀ {n : ℕ} {A : Type u} {α β : TypeVec.{u} n} (
f : α.Arrow β) (x : ↑(MvPFunctor.const n A) α),   MvPFunctor.const.get (MvFuncto
r.map f x) = M…
-/
instance mvqpf : @MvQPF _ (Const n A) where
  P := MvPFunctor.const n A
  abs x := MvPFunctor.const.get x
  repr x := MvPFunctor.const.mk n x
  abs_repr := fun _ => const.get_mk _
  abs_map := fun _ => const.get_map _

end Const

end MvQPF

