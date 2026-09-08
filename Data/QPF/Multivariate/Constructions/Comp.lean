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

variable {n m : ℕ} (F : TypeVec.{u} n → Type*) (G : Fin2 n → TypeVec.{u} m → Type u)

/-- Composition of an `n`-ary functor with `n` `m`-ary
functors gives us one `m`-ary functor -/
/-
**MvQPF.Comp** 是 Mathlib 中的一个定义，位于命名空间 `MvQPF`。
形式化陈述：Comp (v : TypeVec.{u} m) : Type _
参数：v : TypeVec.{u} m。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of an `n`-ary functor with `n` `m`-ary
functors gives us one `m`-ary functor
-/
def Comp (v : TypeVec.{u} m) : Type _ :=
  F fun i : Fin2 n ↦ G i v

namespace Comp

open MvPFunctor

variable {F G} {α β : TypeVec.{u} m} (f : α ⟹ β)

/-
**MvQPF.Comp.** 是 Mathlib 中的一个实例，位于命名空间 `MvQPF.Comp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [I : Inhabited (F fun i : Fin2 n ↦ G i α)] : Inhabited (Comp F G α) := I

/-- Constructor for functor composition -/
/-
**MvQPF.Comp.mk** 是 Mathlib 中的一个定义，位于命名空间 `MvQPF.Comp`。
形式化陈述：{n m : ℕ} →   {F : TypeVec.{u} n → Type u_1} →     {G : Fin2 n → TypeVec.{
u} m → Type u} → {α : TypeVec.{u} m} → (F fun i => G i α) → MvQPF.Comp F G α
参数：F fun i => G i α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for functor composition
-/
protected def mk (x : F fun i ↦ G i α) : Comp F G α := x

/-- Destructor for functor composition -/
/-
**MvQPF.Comp.get** 是 Mathlib 中的一个定义，位于命名空间 `MvQPF.Comp`。
形式化陈述：{n m : ℕ} →   {F : TypeVec.{u} n → Type u_1} →     {G : Fin2 n → TypeVec.{
u} m → Type u} → {α : TypeVec.{u} m} → MvQPF.Comp F G α → F fun i => G i α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Destructor for functor composition
-/
protected def get (x : Comp F G α) : F fun i ↦ G i α := x

@[simp]
/-
**MvQPF.Comp.mk_get** 是 Mathlib 中的一个定理，位于命名空间 `MvQPF.Comp`。
形式化陈述：∀ {n m : ℕ} {F : TypeVec.{u} n → Type u_1} {G : Fin2 n → TypeVec.{u} m → T
ype u} {α : TypeVec.{u} m}   (x : MvQPF.Comp F G α), MvQPF.Comp.mk x.get = x
参数：x : MvQPF.Comp F G α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem mk_get (x : Comp F G α) : Comp.mk (Comp.get x) = x := rfl

@[simp]
/-
**MvQPF.Comp.get_mk** 是 Mathlib 中的一个定理，位于命名空间 `MvQPF.Comp`。
形式化陈述：∀ {n m : ℕ} {F : TypeVec.{u} n → Type u_1} {G : Fin2 n → TypeVec.{u} m → T
ype u} {α : TypeVec.{u} m}   (x : F fun i => G i α), (MvQPF.Comp.mk x).get = x
参数：x : F fun i => G i α；MvQPF.Comp.mk x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem get_mk (x : F fun i ↦ G i α) : Comp.get (Comp.mk x) = x := rfl

section
variable [MvFunctor F] [∀ i, MvFunctor <| G i]

/-- map operation defined on a vector of functors -/
/-
**MvQPF.Comp.map'** 是 Mathlib 中的一个定义，位于命名空间 `MvQPF.Comp`。
形式化陈述：{n m : ℕ} →   {G : Fin2 n → TypeVec.{u} m → Type u} →     {α β : TypeVec.{
u} m} → α.Arrow β → [(i : Fin2 n) → MvFunctor (G i)] → TypeVec.Arrow (fun i => G
 i α) fun i => G i β
参数：i : Fin2 n；G i；fun i => G i α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
map operation defined on a vector of functors
-/
protected def map' : (fun i : Fin2 n ↦ G i α) ⟹ fun i : Fin2 n ↦ G i β := fun _i ↦ map f

/-- The composition of functors is itself functorial -/
/-
**MvQPF.Comp.map** 是 Mathlib 中的一个定义，位于命名空间 `MvQPF.Comp`。
形式化陈述：{n m : ℕ} →   {F : TypeVec.{u} n → Type u_1} →     {G : Fin2 n → TypeVec.{
u} m → Type u} →       {α β : TypeVec.{u} m} →         α.Arrow β → [MvFunctor F]
 → [(i : Fin2 n) → MvFunctor (G i)] → MvQPF.Comp F G α → MvQPF.Comp F G β
参数：i : Fin2 n；G i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of functors is itself functorial
-/
protected def map : (Comp F G) α → (Comp F G) β :=
  (map fun _i ↦ map f : (F fun i ↦ G i α) → F fun i ↦ G i β)
/-
**MvQPF.Comp.** 是 Mathlib 中的一个实例，位于命名空间 `MvQPF.Comp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MvFunctor (Comp F G) where map f := Comp.map f
/-
**MvQPF.Comp.map_mk** 是 Mathlib 中的一个定理，位于命名空间 `MvQPF.Comp`。
形式化陈述：map_mk (x : F fun i => G i α) : f < > Comp.mk x = Comp.mk ((fun i (x : G i
 α) => f <$$> x) <$$> x)
参数：x : F fun i => G i α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_mk (x : F fun i ↦ G i α) :
    f <$$> Comp.mk x = Comp.mk ((fun i (x : G i α) ↦ f <$$> x) <$$> x) := rfl
/-
**MvQPF.Comp.get_map** 是 Mathlib 中的一个定理，位于命名空间 `MvQPF.Comp`。
形式化陈述：get_map (x : Comp F G α) : Comp.get (f <$$> x) = (fun i (x : G i α) => f <
$$> x) < > Comp.get x
参数：x : Comp F G α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem get_map (x : Comp F G α) :
    Comp.get (f <$$> x) = (fun i (x : G i α) ↦ f <$$> x) <$$> Comp.get x := rfl

end

set_option backward.isDefEq.respectTransparency false in
/-
**MvQPF.Comp.** 是 Mathlib 中的一个实例，位于命名空间 `MvQPF.Comp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MvQPF F] [∀ i, MvQPF <| G i] : MvQPF (Comp F G) where
  P := MvPFunctor.comp (P F) fun i ↦ P <| G i
  abs := Comp.mk ∘ (map fun _ ↦ abs) ∘ abs ∘ MvPFunctor.comp.get
  repr {α} := MvPFunctor.comp.mk ∘ repr ∘
              (map fun i ↦ (repr : G i α → (fun i : Fin2 n ↦ Obj (P (G i)) α) i)) ∘ Comp.get
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

