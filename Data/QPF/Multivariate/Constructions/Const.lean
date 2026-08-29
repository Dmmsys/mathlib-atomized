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

variable (n : Nat)

/-- Constant multivariate functor -/
@[nolint unusedArguments]
/--
Definition of `Const` / `Const` 的定义

English:
definition Const
  signature: (A : Type*) (_v : TypeVec.{u} n)
  body: A

中文:
定义 Const
  签名: (A : 类型) (_v : TypeVec.{u} n)
  定义体: A
-/
def Const (A : Type*) (_v : TypeVec.{u} n) : Type _ := A

/--
Instance `Const.inhabited` / 实例 `Const.inhabited`

English:
instance Const.inhabited
  signature: {A α} [Inhabited A]
  body: ⟨(default : A)⟩

中文:
实例 Const.inhabited
  签名: {A α} [可居 A]
  定义体: ⟨(default : A)⟩
-/
instance Const.inhabited {A α} [Inhabited A] : Inhabited (Const n A α) := ⟨(default : A)⟩

namespace Const

open MvPFunctor

variable {n} {A : Type u} {α β : TypeVec.{u} n} (f : α ⟹ β)

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: (x : A)
  body: x

中文:
定义 mk
  签名: (x : A)
  定义体: x
-/
protected def mk (x : A) : Const n A α := x

/--
Definition of `get` / `get` 的定义

English:
definition get
  signature: (x : Const n A α)
  body: x

@[simp]

中文:
定义 get
  签名: (x : Const n A α)
  定义体: x

@[simp]
-/
protected def get (x : Const n A α) : A := x

@[simp]
/--
theorem `mk_get` / 定理 `mk_get`

English:
theorem mk_get
  given: (x : Const n A α)
  statement: Const.mk (Const.get x) = x
  proof: rfl

@[simp]

中文:
定理 mk_get
  条件: (x : Const n A α)
  结论: Const.mk (Const.get x) = x
  证明: rfl

@[simp]
-/
protected theorem mk_get (x : Const n A α) : Const.mk (Const.get x) = x := rfl

@[simp]
/--
theorem `get_mk` / 定理 `get_mk`

English:
theorem get_mk
  given: (x : A)
  statement: Const.get (Const.mk x : Const n A α) = x
  proof: rfl

中文:
定理 get_mk
  条件: (x : A)
  结论: Const.get (Const.mk x : Const n A α) = x
  证明: rfl
-/
protected theorem get_mk (x : A) : Const.get (Const.mk x : Const n A α) = x := rfl

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: : Const n A α -> Const n A β
  body: fun x => x

中文:
定义 map
  签名: : Const n A α -> Const n A β
  定义体: fun x => x
-/
protected def map : Const n A α -> Const n A β := fun x => x

/--
Instance `MvFunctor` / 实例 `MvFunctor`

English:
instance MvFunctor
  signature: : MvFunctor (Const n A) where map _f
  body: Const.map

中文:
实例 Mv函子
  签名: : Mv函子 (Const n A) where map _f
  定义体: Const.map

Depends on / 依赖: Const.map
-/
instance MvFunctor : MvFunctor (Const n A) where map _f := Const.map

/--
theorem `map_mk` / 定理 `map_mk`

English:
theorem map_mk
  given: (x : A)
  statement: f < > Const.mk x = Const.mk x
  proof: rfl

中文:
定理 map_mk
  条件: (x : A)
  结论: f < > Const.mk x = Const.mk x
  证明: rfl
-/
theorem map_mk (x : A) : f < > Const.mk x = Const.mk x := rfl

/--
theorem `get_map` / 定理 `get_map`

English:
theorem get_map
  given: (x : (Const n A) α)
  statement: Const.get (f <$$> x) = Const.get x
  proof: rfl

中文:
定理 get_map
  条件: (x : (Const n A) α)
  结论: Const.get (f <$$> x) = Const.get x
  证明: rfl
-/
theorem get_map (x : (Const n A) α) : Const.get (f <$$> x) = Const.get x := rfl

/--
Instance `mvqpf` / 实例 `mvqpf`

English:
instance mvqpf
  signature: : @MvQPF _ (Const n A) where
  body: MvPFunctor.const n A
  abs x := MvPFunctor.const.get x
  repr x := MvPFunctor.const.mk n x
  abs_repr := fun _ => const.get_mk _
  abs_map := fun _ => const.get_map _

中文:
实例 mvqpf
  签名: : @MvQPF _ (Const n A) where
  定义体: MvPFunctor.const n A
  abs x := MvPFunctor.const.get x
  repr x := MvPFunctor.const.mk n x
  abs_repr := fun _ => const.get_mk _
  abs_map := fun _ => const.get_map _

Depends on / 依赖: MvPFunctor, MvPFunctor.const
-/
instance mvqpf : @MvQPF _ (Const n A) where
  P := MvPFunctor.const n A
  abs x := MvPFunctor.const.get x
  repr x := MvPFunctor.const.mk n x
  abs_repr := fun _ => const.get_mk _
  abs_map := fun _ => const.get_map _

end Const

end MvQPF
