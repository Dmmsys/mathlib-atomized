/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Simon Hudon
-/
module

public import Mathlib.Data.QPF.Multivariate.Basic

/-!
# The quotient of QPF is itself a QPF

The quotients are here defined using a surjective function and
its right inverse. They are very similar to the `abs` and `repr`
functions found in the definition of `MvQPF`
-/

@[expose] public section


universe u

open MvFunctor

namespace MvQPF

variable {n : Nat}
variable {F : TypeVec.{u} n -> Type u}

section repr

variable [q : MvQPF F]
variable {G : TypeVec.{u} n -> Type u} [MvFunctor G]
variable {FG_abs : forall {α}, F α -> G α}
variable {FG_repr : forall {α}, G α -> F α}

/-- If `F` is a QPF then `G` is a QPF as well. Can be used to
construct `MvQPF` instances by transporting them across
surjective functions -/
@[instance_reducible]
/--
Definition of `quotientQPF` / `quotientQPF` 的定义

English:
definition quotientQPF
  signature: (FG_abs_repr : forall {α} (x : G α), FG_abs (FG_repr x) = x)
  body: q.P
  abs p := FG_abs (abs p)
  repr x := repr (FG_repr x)
  abs_repr x := by rw [abs_repr, FG_abs_repr]
  abs_map f p := by rw [abs_map, FG_abs_map]

中文:
定义 quotientQPF
  签名: (FG_abs_repr : 对任意 {α} (x : G α), FG_abs (FG_repr x) = x)
  定义体: q.P
  abs p := FG_abs (abs p)
  repr x := repr (FG_repr x)
  abs_repr x := by rw [abs_repr, FG_abs_repr]
  abs_map f p := by rw [abs_map, FG_abs_map]
-/
def quotientQPF (FG_abs_repr : forall {α} (x : G α), FG_abs (FG_repr x) = x)
    (FG_abs_map : forall {α β} (f : α ⟹ β) (x : F α), FG_abs (f <$$> x) = f <$$> FG_abs x) :
    MvQPF G where
  P := q.P
  abs p := FG_abs (abs p)
  repr x := repr (FG_repr x)
  abs_repr x := by rw [abs_repr, FG_abs_repr]
  abs_map f p := by rw [abs_map, FG_abs_map]

end repr

section Rel

variable (R : forall ⦃α⦄, F α -> F α -> Prop)

/--
Definition of `Quot1` / `Quot1` 的定义

English:
definition Quot1
  signature: (α : TypeVec n)
  body: Quot (@R α)

中文:
定义 Quot1
  签名: (α : TypeVec n)
  定义体: Quot (@R α)
-/
def Quot1 (α : TypeVec n) :=
  Quot (@R α)

/--
Instance `Quot1.inhabited` / 实例 `Quot1.inhabited`

English:
instance Quot1.inhabited
  signature: {α : TypeVec n} [Inhabited <| F α]
  body: ⟨Quot.mk _ default⟩

中文:
实例 Quot1.inhabited
  签名: {α : TypeVec n} [Inhabited <| F α]
  定义体: ⟨Quot.mk _ default⟩

Depends on / 依赖: Quot.mk
-/
instance Quot1.inhabited {α : TypeVec n} [Inhabited <| F α] : Inhabited (Quot1 R α) :=
  ⟨Quot.mk _ default⟩

section

variable [MvFunctor F] (Hfunc : forall ⦃α β⦄ (a b : F α) (f : α ⟹ β), R a b -> R (f <$$> a) (f <$$> b))

/--
Definition of `Quot1.map` / `Quot1.map` 的定义

English:
definition Quot1.map
  signature: ⦃α β⦄ (f : α ⟹ β)
  body: Quot.lift (fun x : F α => Quot.mk _ (f <$$> x : F β)) fun a b h => Quot.sound Hfunc a b _ h

中文:
定义 Quot1.map
  签名: ⦃α β⦄ (f : α ⟹ β)
  定义体: Quot.lift (fun x : F α => Quot.mk _ (f <$$> x : F β)) fun a b h => Quot.sound Hfunc a b _ h

Depends on / 依赖: Quot.lift, Quot.mk, Quot.sound
-/
def Quot1.map ⦃α β⦄ (f : α ⟹ β) : Quot1.{u} R α -> Quot1.{u} R β :=
Quot.lift (fun x : F α => Quot.mk _ (f <$$> x : F β)) fun a b h => Quot.sound Hfunc a b _ h

/-- `mvFunctor` instance for `Quot1` with well-behaved `R` -/
@[instance_reducible]
/--
Definition of `Quot1.mvFunctor` / `Quot1.mvFunctor` 的定义

English:
definition Quot1.mvFunctor
  signature: : MvFunctor (Quot1 R) where map
  body: @Quot1.map _ _ R _ Hfunc

中文:
定义 Quot1.mvFunctor
  签名: : MvFunctor (Quot1 R) where map
  定义体: @Quot1.map _ _ R _ Hfunc

Depends on / 依赖: Quot1.map
-/
def Quot1.mvFunctor : MvFunctor (Quot1 R) where map := @Quot1.map _ _ R _ Hfunc

end

section

variable [q : MvQPF F] (Hfunc : forall ⦃α β⦄ (a b : F α) (f : α ⟹ β), R a b -> R (f <$$> a) (f <$$> b))

/-- `Quot1` is a QPF -/
@[instance_reducible]
/--
Definition of `relQuot` / `relQuot` 的定义

English:
definition relQuot
  signature: : @MvQPF _ (Quot1 R)
  body: @quotientQPF n F q _ (MvQPF.Quot1.mvFunctor R Hfunc) (fun x => Quot.mk _ x)
    Quot.out (fun _x => Quot.out_eq _) fun _f _x => rfl

中文:
定义 relQuot
  签名: : @MvQPF _ (Quot1 R)
  定义体: @quotientQPF n F q _ (MvQPF.Quot1.mvFunctor R Hfunc) (fun x => Quot.mk _ x)
    Quot.out (fun _x => Quot.out_eq _) fun _f _x => rfl

Depends on / 依赖: MvQPF.Quot1.mvFunctor, Quot.mk, Quot.out, Quot.out_eq, mvFunctor, out_eq, quotientQPF
-/
noncomputable def relQuot : @MvQPF _ (Quot1 R) :=
  @quotientQPF n F q _ (MvQPF.Quot1.mvFunctor R Hfunc) (fun x => Quot.mk _ x)
    Quot.out (fun _x => Quot.out_eq _) fun _f _x => rfl

end

end Rel

end MvQPF
