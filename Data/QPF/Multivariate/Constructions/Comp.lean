/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Simon Hudon
-/
module

public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Mathlib.Data.QPF.Multivariate.Basic

/-!
# The composition of QPFs is itself a QPF

We define composition between one `n`-ary functor and `n` `m`-ary functors
and show that it preserves the QPF structure
-/

@[expose] public section


universe u

namespace MvQPF

open MvFunctor

variable {n m : Nat} (F : TypeVec.{u} n -> Type*) (G : Fin2 n -> TypeVec.{u} m -> Type u)

/--
Definition of `Comp` / `Comp` 的定义

English:
definition Comp
  signature: (v : TypeVec.{u} m)
  body: F fun i : Fin2 n => G i v

中文:
定义 Comp
  签名: (v : TypeVec.{u} m)
  定义体: F fun i : Fin2 n => G i v
-/
def Comp (v : TypeVec.{u} m) : Type _ :=
  F fun i : Fin2 n => G i v

namespace Comp

open MvPFunctor

variable {F G} {α β : TypeVec.{u} m} (f : α ⟹ β)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [I
  signature: : Inhabited (F fun i : Fin2 n => G i α)] : Inhabited (Comp F G α)
  body: I

中文:
实例 [I
  签名: : Inhabited (F fun i : Fin2 n => G i α)] : Inhabited (Comp F G α)
  定义体: I
-/
instance [I : Inhabited (F fun i : Fin2 n => G i α)] : Inhabited (Comp F G α) := I

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: (x : F fun i => G i α)
  body: x

中文:
定义 mk
  签名: (x : F fun i => G i α)
  定义体: x
-/
protected def mk (x : F fun i => G i α) : Comp F G α := x

/--
Definition of `get` / `get` 的定义

English:
definition get
  signature: (x : Comp F G α)
  body: x

@[simp]

中文:
定义 get
  签名: (x : Comp F G α)
  定义体: x

@[simp]
-/
protected def get (x : Comp F G α) : F fun i => G i α := x

@[simp]
/--
theorem `mk_get` / 定理 `mk_get`

English:
theorem mk_get
  given: (x : Comp F G α)
  statement: Comp.mk (Comp.get x) = x
  proof: rfl

@[simp]

中文:
定理 mk_get
  条件: (x : Comp F G α)
  结论: Comp.mk (Comp.get x) = x
  证明: rfl

@[simp]
-/
protected theorem mk_get (x : Comp F G α) : Comp.mk (Comp.get x) = x := rfl

@[simp]
/--
theorem `get_mk` / 定理 `get_mk`

English:
theorem get_mk
  given: (x : F fun i => G i α)
  statement: Comp.get (Comp.mk x) = x
  proof: rfl

中文:
定理 get_mk
  条件: (x : F fun i => G i α)
  结论: Comp.get (Comp.mk x) = x
  证明: rfl
-/
protected theorem get_mk (x : F fun i => G i α) : Comp.get (Comp.mk x) = x := rfl

section
variable [MvFunctor F] [forall i, MvFunctor <| G i]

/--
Definition of `map'` / `map'` 的定义

English:
definition map'
  signature: : (fun i : Fin2 n => G i α) ⟹ fun i : Fin2 n => G i β
  body: fun _i => map f

中文:
定义 map'
  签名: : (fun i : Fin2 n => G i α) ⟹ fun i : Fin2 n => G i β
  定义体: fun _i => map f
-/
protected def map' : (fun i : Fin2 n => G i α) ⟹ fun i : Fin2 n => G i β := fun _i => map f

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: : (Comp F G) α -> (Comp F G) β
  body: (map fun _i => map f : (F fun i => G i α) -> F fun i => G i β)

中文:
定义 map
  签名: : (Comp F G) α -> (Comp F G) β
  定义体: (map fun _i => map f : (F fun i => G i α) -> F fun i => G i β)
-/
protected def map : (Comp F G) α -> (Comp F G) β :=
  (map fun _i => map f : (F fun i => G i α) -> F fun i => G i β)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MvFunctor (Comp F G)
  body: Comp.map f

中文:
实例 :
  签名: MvFunctor (Comp F G)
  定义体: Comp.map f

Depends on / 依赖: Comp.map
-/
instance : MvFunctor (Comp F G) where map f := Comp.map f

/--
theorem `map_mk` / 定理 `map_mk`

English:
theorem map_mk
  given: (x : F fun i => G i α)
  proof: rfl

中文:
定理 map_mk
  条件: (x : F fun i => G i α)
  证明: rfl
-/
theorem map_mk (x : F fun i => G i α) :
f < > Comp.mk x = Comp.mk ((fun i (x : G i α) => f <$$> x) <$$> x) := rfl

/--
theorem `get_map` / 定理 `get_map`

English:
theorem get_map
  given: (x : Comp F G α)
  proof: rfl

中文:
定理 get_map
  条件: (x : Comp F G α)
  证明: rfl
-/
theorem get_map (x : Comp F G α) :
Comp.get (f <$$> x) = (fun i (x : G i α) => f <$$> x) < > Comp.get x := rfl

end

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MvQPF
  signature: F] [forall i, MvQPF <| G i] : MvQPF (Comp F G) where
  body: MvPFunctor.comp (P F) fun i => P G i
  abs := Comp.mk ∘ (map fun _ => abs) ∘ abs ∘ MvPFunctor.comp.get
  repr {α} := MvPFunctor.comp.mk ∘ repr ∘
              (map fun i => (repr : G i α -> (fun i : Fin2 n => Obj (P (G i)) α) i)) ∘ Comp.get
  abs_repr := by
    intros
    simp +unfoldPartialApp only

中文:
实例 [MvQPF
  签名: F] [对任意 i, MvQPF <| G i] : MvQPF (Comp F G) where
  定义体: MvPFunctor.comp (P F) fun i => P G i
  abs := Comp.mk ∘ (map fun _ => abs) ∘ abs ∘ MvPFunctor.comp.get
  repr {α} := MvPFunctor.comp.mk ∘ repr ∘
              (map fun i => (repr : G i α -> (fun i : Fin2 n => Obj (P (G i)) α) i)) ∘ Comp.get
  abs_repr := by
    intros
    simp +unfoldPartialApp only

Depends on / 依赖: MvPFunctor, MvPFunctor.comp
-/
instance [MvQPF F] [forall i, MvQPF <| G i] : MvQPF (Comp F G) where
P := MvPFunctor.comp (P F) fun i => P G i
  abs := Comp.mk ∘ (map fun _ => abs) ∘ abs ∘ MvPFunctor.comp.get
  repr {α} := MvPFunctor.comp.mk ∘ repr ∘
              (map fun i => (repr : G i α -> (fun i : Fin2 n => Obj (P (G i)) α) i)) ∘ Comp.get
  abs_repr := by
    intros
    simp +unfoldPartialApp only [Function.comp_def, comp.get_mk, abs_repr,
      map_map, TypeVec.comp, MvFunctor.id_map', Comp.mk_get]
  abs_map := by
    intros
    simp only [(· ∘ ·)]
    rw [← abs_map]
    simp +unfoldPartialApp only [comp.get_map, map_map, TypeVec.comp,
      abs_map, map_mk]

end Comp

end MvQPF
