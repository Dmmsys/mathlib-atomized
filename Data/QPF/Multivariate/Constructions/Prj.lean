/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
module

public import Mathlib.Control.Functor.Multivariate
public import Mathlib.Data.QPF.Multivariate.Basic

/-!
Projection functors are QPFs. The `n`-ary projection functors on `i` is an `n`-ary
functor `F` such that `F (α₀..αᵢ₋₁, αᵢ, αᵢ₊₁..αₙ₋₁) = αᵢ`
-/

@[expose] public section


universe u v

namespace MvQPF

open MvFunctor

variable {n : Nat} (i : Fin2 n)

/--
Definition of `Prj` / `Prj` 的定义

English:
definition Prj
  signature: (v : TypeVec.{u} n)
  body: v i

中文:
定义 Prj
  签名: (v : TypeVec.{u} n)
  定义体: v i
-/
def Prj (v : TypeVec.{u} n) : Type u := v i

/--
Instance `Prj.inhabited` / 实例 `Prj.inhabited`

English:
instance Prj.inhabited
  signature: {v : TypeVec.{u} n} [Inhabited (v i)]
  body: ⟨(default : v i)⟩

中文:
实例 Prj.inhabited
  签名: {v : TypeVec.{u} n} [可居 (v i)]
  定义体: ⟨(default : v i)⟩
-/
instance Prj.inhabited {v : TypeVec.{u} n} [Inhabited (v i)] : Inhabited (Prj i v) :=
  ⟨(default : v i)⟩

/--
Definition of `Prj.map` / `Prj.map` 的定义

English:
definition Prj.map
  signature: ⦃α β
  body: f _

中文:
定义 Prj.map
  签名: ⦃α β
  定义体: f _
-/
def Prj.map ⦃α β : TypeVec n⦄ (f : α ⟹ β) : Prj i α -> Prj i β := f _

/--
Instance `Prj.mvfunctor` / 实例 `Prj.mvfunctor`

English:
instance Prj.mvfunctor
  signature: : MvFunctor (Prj i) where map
  body: @Prj.map _ i

中文:
实例 Prj.mvfunctor
  签名: : Mv函子 (Prj i) where map
  定义体: @Prj.map _ i

Depends on / 依赖: Prj.map
-/
instance Prj.mvfunctor : MvFunctor (Prj i) where map := @Prj.map _ i

/--
Definition of `Prj.P` / `Prj.P` 的定义

English:
definition Prj.P
  signature: : MvPFunctor.{u} n where
  body: PUnit
B _ j := ULift PLift i = j

中文:
定义 Prj.P
  签名: : MvP函子.{u} n where
  定义体: PUnit
B _ j := ULift PLift i = j
-/
def Prj.P : MvPFunctor.{u} n where
  A := PUnit
B _ j := ULift PLift i = j

/--
Definition of `Prj.abs` / `Prj.abs` 的定义

English:
definition Prj.abs
  signature: ⦃α

中文:
定义 Prj.abs
  签名: ⦃α
-/
def Prj.abs ⦃α : TypeVec n⦄ : Prj.P i α -> Prj i α
  | ⟨_x, f⟩ => f _ ⟨⟨rfl⟩⟩

/--
Definition of `Prj.repr` / `Prj.repr` 的定义

English:
definition Prj.repr
  signature: ⦃α
  body: fun x : α i =>
  ⟨⟨⟩, fun j ⟨⟨h⟩⟩ => (h.rec x : α j)⟩

中文:
定义 Prj.repr
  签名: ⦃α
  定义体: fun x : α i =>
  ⟨⟨⟩, fun j ⟨⟨h⟩⟩ => (h.rec x : α j)⟩
-/
def Prj.repr ⦃α : TypeVec n⦄ : Prj i α -> Prj.P i α := fun x : α i =>
  ⟨⟨⟩, fun j ⟨⟨h⟩⟩ => (h.rec x : α j)⟩

/--
Instance `Prj.mvqpf` / 实例 `Prj.mvqpf`

English:
instance Prj.mvqpf
  signature: : MvQPF (Prj i) where
  body: Prj.P i
  abs := @Prj.abs _ i
  repr := @Prj.repr _ i
  abs_repr := by intros; rfl
  abs_map := by intro α β f P; cases P; rfl

中文:
实例 Prj.mvqpf
  签名: : MvQPF (Prj i) where
  定义体: Prj.P i
  abs := @Prj.abs _ i
  repr := @Prj.repr _ i
  abs_repr := by intros; rfl
  abs_map := by intro α β f P; cases P; rfl

Depends on / 依赖: Prj.P
-/
instance Prj.mvqpf : MvQPF (Prj i) where
  P := Prj.P i
  abs := @Prj.abs _ i
  repr := @Prj.repr _ i
  abs_repr := by intros; rfl
  abs_map := by intro α β f P; cases P; rfl

end MvQPF
