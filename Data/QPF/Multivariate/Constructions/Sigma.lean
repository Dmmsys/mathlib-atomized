/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
module

public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Mathlib.Data.QPF.Multivariate.Basic

/-!
# Dependent product and sum of QPFs are QPFs
-/

@[expose] public section


universe u

namespace MvQPF

open MvFunctor

variable {n : Nat} {A : Type u}
variable (F : A -> TypeVec.{u} n -> Type u)

/--
Definition of `Sigma` / `Sigma` 的定义

English:
definition Sigma
  signature: (v : TypeVec.{u} n)
  body: Σ α : A, F α v

中文:
定义 依赖和类型
  签名: (v : TypeVec.{u} n)
  定义体: Σ α : A, F α v
-/
def Sigma (v : TypeVec.{u} n) : Type u :=
  Σ α : A, F α v

/--
Definition of `Pi` / `Pi` 的定义

English:
definition Pi
  signature: (v : TypeVec.{u} n)
  body: forall α : A, F α v

中文:
定义 依赖函数类型
  签名: (v : TypeVec.{u} n)
  定义体: forall α : A, F α v
-/
def Pi (v : TypeVec.{u} n) : Type u :=
  forall α : A, F α v

/--
Instance `Sigma.inhabited` / 实例 `Sigma.inhabited`

English:
instance Sigma.inhabited
  signature: {α} [Inhabited A] [Inhabited (F default α)]
  body: ⟨⟨default, default⟩⟩

中文:
实例 依赖和类型.inhabited
  签名: {α} [可居 A] [可居 (F default α)]
  定义体: ⟨⟨default, default⟩⟩
-/
instance Sigma.inhabited {α} [Inhabited A] [Inhabited (F default α)] : Inhabited (Sigma F α) :=
  ⟨⟨default, default⟩⟩

/--
Instance `Pi.inhabited` / 实例 `Pi.inhabited`

English:
instance Pi.inhabited
  signature: {α} [forall a, Inhabited (F a α)]
  body: ⟨fun _a => default⟩

中文:
实例 依赖函数类型.inhabited
  签名: {α} [对任意 a, 可居 (F a α)]
  定义体: ⟨fun _a => default⟩
-/
instance Pi.inhabited {α} [forall a, Inhabited (F a α)] : Inhabited (Pi F α) :=
  ⟨fun _a => default⟩

namespace Sigma

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: α, MvFunctor <| F α] : MvFunctor (Sigma F) where
  body: fun f ⟨a, x⟩ => ⟨a, f < > x⟩

中文:
实例 [对任意
  签名: α, Mv函子 <| F α] : Mv函子 (依赖和类型 F) where
  定义体: fun f ⟨a, x⟩ => ⟨a, f < > x⟩
-/
instance [forall α, MvFunctor <| F α] : MvFunctor (Sigma F) where
map := fun f ⟨a, x⟩ => ⟨a, f < > x⟩


variable [forall α, MvQPF <| F α]

/--
Definition of `P` / `P` 的定义

English:
definition P
  signature: : MvPFunctor n
  body: ⟨Σ a, (P (F a)).A, fun x => (P (F x.1)).B x.2⟩

中文:
定义 P
  签名: : MvP函子 n
  定义体: ⟨Σ a, (P (F a)).A, fun x => (P (F x.1)).B x.2⟩
-/
protected def P : MvPFunctor n :=
  ⟨Σ a, (P (F a)).A, fun x => (P (F x.1)).B x.2⟩

/--
Definition of `abs` / `abs` 的定义

English:
definition abs
  signature: ⦃α⦄

中文:
定义 abs
  签名: ⦃α⦄
-/
protected def abs ⦃α⦄ : Sigma.P F α -> Sigma F α
  | ⟨a, f⟩ => ⟨a.1, MvQPF.abs ⟨a.2, f⟩⟩

/--
Definition of `repr` / `repr` 的定义

English:
definition repr
  signature: ⦃α⦄
  body: MvQPF.repr f
    ⟨⟨a, x.1⟩, x.2⟩

中文:
定义 repr
  签名: ⦃α⦄
  定义体: MvQPF.repr f
    ⟨⟨a, x.1⟩, x.2⟩
-/
protected def repr ⦃α⦄ : Sigma F α -> Sigma.P F α
  | ⟨a, f⟩ =>
    let x := MvQPF.repr f
    ⟨⟨a, x.1⟩, x.2⟩

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MvQPF (Sigma F)
  body: Sigma.P F
  abs {α} := @Sigma.abs _ _ F _ α
  repr {α} := @Sigma.repr _ _ F _ α
  abs_repr := by rintro α ⟨x, f⟩; simp only [Sigma.abs, Sigma.repr, Sigma.eta, abs_repr]
  abs_map := by rintro α β f ⟨x, g⟩; simp only [Sigma.abs, MvPFunctor.map_eq]
                simp only [(· <$$> ·), ← abs_map, ← MvPFunctor.map_eq]

中文:
实例 :
  签名: MvQPF (依赖和类型 F)
  定义体: Sigma.P F
  abs {α} := @Sigma.abs _ _ F _ α
  repr {α} := @Sigma.repr _ _ F _ α
  abs_repr := by rintro α ⟨x, f⟩; simp only [Sigma.abs, Sigma.repr, Sigma.eta, abs_repr]
  abs_map := by rintro α β f ⟨x, g⟩; simp only [Sigma.abs, MvPFunctor.map_eq]
                simp only [(· <$$> ·), ← abs_map, ← MvPFunctor.map_eq]

Depends on / 依赖: Sigma.P
-/
instance : MvQPF (Sigma F) where
  P := Sigma.P F
  abs {α} := @Sigma.abs _ _ F _ α
  repr {α} := @Sigma.repr _ _ F _ α
  abs_repr := by rintro α ⟨x, f⟩; simp only [Sigma.abs, Sigma.repr, Sigma.eta, abs_repr]
  abs_map := by rintro α β f ⟨x, g⟩; simp only [Sigma.abs, MvPFunctor.map_eq]
                simp only [(· <$$> ·), ← abs_map, ← MvPFunctor.map_eq]

end Sigma

namespace Pi

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: α, MvFunctor <| F α] : MvFunctor (Pi F) where map f x a
  body: f < > x a

中文:
实例 [对任意
  签名: α, Mv函子 <| F α] : Mv函子 (依赖函数类型 F) where map f x a
  定义体: f < > x a
-/
instance [forall α, MvFunctor <| F α] : MvFunctor (Pi F) where map f x a := f < > x a

variable [forall α, MvQPF <| F α]

/--
Definition of `P` / `P` 的定义

English:
definition P
  signature: : MvPFunctor n
  body: ⟨forall a, (P (F a)).A, fun x i => Σ a, (P (F a)).B (x a) i⟩

中文:
定义 P
  签名: : MvP函子 n
  定义体: ⟨forall a, (P (F a)).A, fun x i => Σ a, (P (F a)).B (x a) i⟩
-/
protected def P : MvPFunctor n :=
  ⟨forall a, (P (F a)).A, fun x i => Σ a, (P (F a)).B (x a) i⟩

/--
Definition of `abs` / `abs` 的定义

English:
definition abs
  signature: ⦃α⦄

中文:
定义 abs
  签名: ⦃α⦄
-/
protected def abs ⦃α⦄ : Pi.P F α -> Pi F α
  | ⟨a, f⟩ => fun x => MvQPF.abs ⟨a x, fun i y => f i ⟨_, y⟩⟩

/--
Definition of `repr` / `repr` 的定义

English:
definition repr
  signature: ⦃α⦄

中文:
定义 repr
  签名: ⦃α⦄
-/
protected def repr ⦃α⦄ : Pi F α -> Pi.P F α
  | f => ⟨fun a => (MvQPF.repr (f a)).1, fun _i a => (MvQPF.repr (f _)).2 _ a.2⟩

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MvQPF (Pi F)
  body: Pi.P F
  abs := @Pi.abs _ _ F _
  repr := @Pi.repr _ _ F _
  abs_repr := by
    rintro α f
    simp +instances only [Pi.abs, Pi.repr, Sigma.eta, abs_repr]
  abs_map := by rintro α β f ⟨x, g⟩; simp only [Pi.abs, (· <$$> ·), ← abs_map]; rfl

中文:
实例 :
  签名: MvQPF (依赖函数类型 F)
  定义体: Pi.P F
  abs := @Pi.abs _ _ F _
  repr := @Pi.repr _ _ F _
  abs_repr := by
    rintro α f
    simp +instances only [Pi.abs, Pi.repr, Sigma.eta, abs_repr]
  abs_map := by rintro α β f ⟨x, g⟩; simp only [Pi.abs, (· <$$> ·), ← abs_map]; rfl

Depends on / 依赖: Pi.P
-/
instance : MvQPF (Pi F) where
  P := Pi.P F
  abs := @Pi.abs _ _ F _
  repr := @Pi.repr _ _ F _
  abs_repr := by
    rintro α f
    simp +instances only [Pi.abs, Pi.repr, Sigma.eta, abs_repr]
  abs_map := by rintro α β f ⟨x, g⟩; simp only [Pi.abs, (· <$$> ·), ← abs_map]; rfl

end Pi

end MvQPF
