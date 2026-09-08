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

variable {n : ℕ}
variable {F : TypeVec.{u} n → Type u}

section repr

variable [q : MvQPF F]
variable {G : TypeVec.{u} n → Type u} [MvFunctor G]
variable {FG_abs : ∀ {α}, F α → G α}
variable {FG_repr : ∀ {α}, G α → F α}

/-- If `F` is a QPF then `G` is a QPF as well. Can be used to
construct `MvQPF` instances by transporting them across
surjective functions -/
@[instance_reducible]
/-
**MvQPF.quotientQPF** 是 Mathlib 中的一个定义，位于命名空间 `MvQPF`。
形式化陈述：quotientQPF (FG_abs_repr : forall {α} (x : G α), FG_abs (FG_repr x) = x) (
FG_abs_map : forall {α β} (f : α ⟹ β) (x : F α), FG_abs (f <$$> x) = f <$$> FG_a
bs x) : MvQPF G where P
参数：FG_abs_repr : forall {α} (x : G α), FG_abs (FG_repr x) = x；FG_abs_map : foral
l {α β} (f : α ⟹ β) (x : F α), FG_abs (f <$$> x) = f <$$> FG_abs x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `F` is a QPF then `G` is a QPF as well. Can be used to
construct `MvQPF` instances by transporting them across
surjective functions
-/
def quotientQPF (FG_abs_repr : ∀ {α} (x : G α), FG_abs (FG_repr x) = x)
    (FG_abs_map : ∀ {α β} (f : α ⟹ β) (x : F α), FG_abs (f <$$> x) = f <$$> FG_abs x) :
    MvQPF G where
  P := q.P
  abs p := FG_abs (abs p)
  repr x := repr (FG_repr x)
  abs_repr x := by rw [abs_repr, FG_abs_repr]
  abs_map f p := by rw [abs_map, FG_abs_map]

end repr

section Rel

variable (R : ∀ ⦃α⦄, F α → F α → Prop)

/-- Functorial quotient type -/
/-
**MvQPF.Quot1** 是 Mathlib 中的一个定义，位于命名空间 `MvQPF`。
形式化陈述：Quot1 (α : TypeVec n)
参数：α : TypeVec n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Functorial quotient type
-/
def Quot1 (α : TypeVec n) :=
  Quot (@R α)
/-
**MvQPF.Quot1.inhabited** 是 Mathlib 中的一个定义，位于命名空间 `MvQPF.Quot1`。
形式化陈述：{n : ℕ} →   {F : TypeVec.{u} n → Type u} →     (R : ⦃α : TypeVec.{u} n⦄ → 
F α → F α → Prop) → {α : TypeVec.{u} n} → [Inhabited (F α)] → Inhabited (MvQPF.Q
uot1 R α)
参数：R : ⦃α : TypeVec.{u} n⦄ → F α → F α → Prop；F α；MvQPF.Quot1 R α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Quot1.inhabited {α : TypeVec n} [Inhabited <| F α] : Inhabited (Quot1 R α) :=
  ⟨Quot.mk _ default⟩

section

variable [MvFunctor F] (Hfunc : ∀ ⦃α β⦄ (a b : F α) (f : α ⟹ β), R a b → R (f <$$> a) (f <$$> b))

/-- `map` of the `Quot1` functor -/
/-
**MvQPF.Quot1.map** 是 Mathlib 中的一个定义，位于命名空间 `MvQPF.Quot1`。
形式化陈述：{n : ℕ} →   {F : TypeVec.{u} n → Type u} →     (R : ⦃α : TypeVec.{u} n⦄ → 
F α → F α → Prop) →       [inst : MvFunctor F] →         (∀ ⦃α β : TypeVec.{u} n
⦄ (a b : F α) (f : α.Arrow β), R a b → R (MvFunctor.map f a) (MvFunctor.map f b)
) →           ⦃α β : TypeVec.{u} n⦄ → α.Arrow β → MvQPF.Quot1 R α → MvQPF.Quot1 
R β
参数：R : ⦃α : TypeVec.{u} n⦄ → F α → F α → Prop；∀ ⦃α β : TypeVec.{u} n⦄ (a b : F α
) (f : α.Arrow β), R a b → R (MvFunctor.map f a) (MvFunctor.map f b)。
该定义给出了一个带前提的构造。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`map` of the `Quot1` functor
-/
def Quot1.map ⦃α β⦄ (f : α ⟹ β) : Quot1.{u} R α → Quot1.{u} R β :=
  Quot.lift (fun x : F α => Quot.mk _ (f <$$> x : F β)) fun a b h => Quot.sound <| Hfunc a b _ h

/-- `mvFunctor` instance for `Quot1` with well-behaved `R` -/
@[instance_reducible]
/-
**MvQPF.Quot1.mvFunctor** 是 Mathlib 中的一个定义，位于命名空间 `MvQPF.Quot1`。
形式化陈述：{n : ℕ} →   {F : TypeVec.{u} n → Type u} →     (R : ⦃α : TypeVec.{u} n⦄ → 
F α → F α → Prop) →       [inst : MvFunctor F] →         (∀ ⦃α β : TypeVec.{u} n
⦄ (a b : F α) (f : α.Arrow β), R a b → R (MvFunctor.map f a) (MvFunctor.map f b)
) →           MvFunctor (MvQPF.Quot1 R)
参数：R : ⦃α : TypeVec.{u} n⦄ → F α → F α → Prop；∀ ⦃α β : TypeVec.{u} n⦄ (a b : F α
) (f : α.Arrow β), R a b → R (MvFunctor.map f a) (MvFunctor.map f b)；MvQPF.Quot1
 R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`mvFunctor` instance for `Quot1` with well-behaved `R`
-/
def Quot1.mvFunctor : MvFunctor (Quot1 R) where map := @Quot1.map _ _ R _ Hfunc

end

section

variable [q : MvQPF F] (Hfunc : ∀ ⦃α β⦄ (a b : F α) (f : α ⟹ β), R a b → R (f <$$> a) (f <$$> b))

/-- `Quot1` is a QPF -/
@[instance_reducible]
/-
**MvQPF.relQuot** 是 Mathlib 中的一个定义，位于命名空间 `MvQPF`。
形式化陈述：relQuot : @MvQPF _ (Quot1 R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Quot1` is a QPF
-/
noncomputable def relQuot : @MvQPF _ (Quot1 R) :=
  @quotientQPF n F q _ (MvQPF.Quot1.mvFunctor R Hfunc) (fun x => Quot.mk _ x)
    Quot.out (fun _x => Quot.out_eq _) fun _f _x => rfl

end

end Rel

end MvQPF

