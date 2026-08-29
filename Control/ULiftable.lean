/-
Copyright (c) 2020 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
module

public import Mathlib.Control.Monad.Basic
public import Mathlib.Control.Monad.Cont
public import Mathlib.Control.Monad.Writer
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Logic.Equiv.Functor
public import Mathlib.Control.Lawful

/-!
# Universe lifting for type families

Some functors such as `Option` and `List` are universe polymorphic. Unlike
type polymorphism where `Option α` is a function application and reasoning and
generalizations that apply to functions can be used, `Option.{u}` and `Option.{v}`
are not one function applied to two universe names but one polymorphic definition
instantiated twice. This means that whatever works on `Option.{u}` is hard
to transport over to `Option.{v}`. `ULiftable` is an attempt at improving the situation.

`ULiftable Option.{u} Option.{v}` gives us a generic and composable way to use
`Option.{u}` in a context that requires `Option.{v}`. It is often used in tandem with
`ULift` but the two are purposefully decoupled.


## Main definitions
* `ULiftable` class

## Tags

universe polymorphism functor

-/

@[expose] public section


universe v u₀ u₁ v₀ v₁ v₂ w w₀ w₁

variable {s : Type u₀} {s' : Type u₁} {r r' w w' : Type*}

/--
Definition of `ULiftable` / `ULiftable` 的定义

English:
class ULiftable
  parameters: (f : outParam (Type u₀ -> Type u₁)) (g : Type v₀ -> Type v₁)
  axioms and operations (1):
    - congr({α β}) : α ≃ β -> f α ≃ g β

中文:
类 ULiftable
  参数: (f : outParam (类型u₀ -> 类型u₁)) (g : 类型v₀ -> 类型v₁)
  公理与运算 (1 个):
    - congr({α β}) : α ≃ β -> f α ≃ g β
-/
class ULiftable (f : outParam (Type u₀ -> Type u₁)) (g : Type v₀ -> Type v₁) where
  congr {α β} : α ≃ β -> f α ≃ g β

namespace ULiftable

/--
Definition of `symm` / `symm` 的定义

English:
abbreviation symm
  signature: (f : Type u₀ -> Type u₁) (g : Type v₀ -> Type v₁) [ULiftable f g]
  body: (ULiftable.congr e.symm).symm

中文:
缩写 symm
  签名: (f : 类型u₀ -> 类型u₁) (g : 类型v₀ -> 类型v₁) [ULiftable f g]
  定义体: (ULiftable.congr e.symm).symm

Depends on / 依赖: ULiftable, ULiftable.congr, e.symm
-/
abbrev symm (f : Type u₀ -> Type u₁) (g : Type v₀ -> Type v₁) [ULiftable f g] : ULiftable g f where
  congr e := (ULiftable.congr e.symm).symm

/--
Instance `refl` / 实例 `refl`

English:
instance refl
  signature: (f : Type u₀ -> Type u₁) [Functor f] [LawfulFunctor f]
  body: Functor.mapEquiv _ e

中文:
实例 refl
  签名: (f : 类型u₀ -> 类型u₁) [Functor f] [LawfulFunctor f]
  定义体: Functor.mapEquiv _ e

Depends on / 依赖: Functor, Functor.mapEquiv, mapEquiv
-/
instance refl (f : Type u₀ -> Type u₁) [Functor f] [LawfulFunctor f] : ULiftable f f where
  congr e := Functor.mapEquiv _ e

/--
Definition of `up` / `up` 的定义

English:
abbreviation up
  signature: {f : Type u₀ -> Type u₁} {g : Type max u₀ v -> Type v₁} [ULiftable f g] {α}
  body: (ULiftable.congr Equiv.ulift.symm).toFun

中文:
缩写 up
  签名: {f : 类型u₀ -> 类型u₁} {g : Type max u₀ v -> 类型v₁} [ULiftable f g] {α}
  定义体: (ULiftable.congr Equiv.ulift.symm).toFun

Depends on / 依赖: Equiv.ulift.symm, ULiftable, ULiftable.congr
-/
abbrev up {f : Type u₀ -> Type u₁} {g : Type max u₀ v -> Type v₁} [ULiftable f g] {α} :
    f α -> g (ULift.{v} α) :=
  (ULiftable.congr Equiv.ulift.symm).toFun

/--
Definition of `down` / `down` 的定义

English:
abbreviation down
  signature: {f : Type u₀ -> Type u₁} {g : Type max u₀ v -> Type v₁} [ULiftable f g] {α}
  body: (ULiftable.congr Equiv.ulift.symm).invFun

中文:
缩写 down
  签名: {f : 类型u₀ -> 类型u₁} {g : Type max u₀ v -> 类型v₁} [ULiftable f g] {α}
  定义体: (ULiftable.congr Equiv.ulift.symm).invFun

Depends on / 依赖: Equiv.ulift.symm, ULiftable, ULiftable.congr, invFun, mem_dropLast_of_mem_of_ne_getLast
-/
abbrev down {f : Type u₀ -> Type u₁} {g : Type max u₀ v -> Type v₁} [ULiftable f g] {α} :
    g (ULift.{v} α) -> f α :=
  (ULiftable.congr Equiv.ulift.symm).invFun

/--
Definition of `adaptUp` / `adaptUp` 的定义

English:
definition adaptUp
  signature: (F : Type v₀ -> Type v₁) (G : Type max v₀ u₀ -> Type u₁) [ULiftable F G] [Monad G] {α β}
  body: up x >>= f ∘ ULift.down.{u₀}

中文:
定义 adaptUp
  签名: (F : 类型v₀ -> 类型v₁) (G : Type max v₀ u₀ -> 类型u₁) [ULiftable F G] [Monad G] {α β}
  定义体: up x >>= f ∘ ULift.down.{u₀}

Depends on / 依赖: ULift.down
-/
def adaptUp (F : Type v₀ -> Type v₁) (G : Type max v₀ u₀ -> Type u₁) [ULiftable F G] [Monad G] {α β}
    (x : F α) (f : α -> G β) : G β :=
  up x >>= f ∘ ULift.down.{u₀}

/--
Definition of `adaptDown` / `adaptDown` 的定义

English:
definition adaptDown
  signature: {F : Type max u₀ v₀ -> Type u₁} {G : Type v₀ -> Type v₁} [L : ULiftable G F] [Monad F]
  body: @down.{max u₀ v₀} G F L β x >>= @up.{max u₀ v₀} G F L β ∘ f

中文:
定义 adaptDown
  签名: {F : Type max u₀ v₀ -> 类型u₁} {G : 类型v₀ -> 类型v₁} [L : ULiftable G F] [Monad F]
  定义体: @down.{max u₀ v₀} G F L β x >>= @up.{max u₀ v₀} G F L β ∘ f
-/
def adaptDown {F : Type max u₀ v₀ -> Type u₁} {G : Type v₀ -> Type v₁} [L : ULiftable G F] [Monad F]
    {α β} (x : F α) (f : α -> G β) : G β :=
@down.{max u₀ v₀} G F L β x >>= @up.{max u₀ v₀} G F L β ∘ f

/--
Definition of `upMap` / `upMap` 的定义

English:
definition upMap
  signature: {F : Type u₀ -> Type u₁} {G : Type max u₀ v₀ -> Type v₁} [ULiftable F G] [Functor G]
  body: Functor.map (f ∘ ULift.down.{v₀}) (up x)

中文:
定义 upMap
  签名: {F : 类型u₀ -> 类型u₁} {G : Type max u₀ v₀ -> 类型v₁} [ULiftable F G] [Functor G]
  定义体: Functor.map (f ∘ ULift.down.{v₀}) (up x)

Depends on / 依赖: Functor, Functor.map, ULift.down
-/
def upMap {F : Type u₀ -> Type u₁} {G : Type max u₀ v₀ -> Type v₁} [ULiftable F G] [Functor G]
    {α β} (f : α -> β) (x : F α) : G β :=
  Functor.map (f ∘ ULift.down.{v₀}) (up x)

/--
Definition of `downMap` / `downMap` 的定义

English:
definition downMap
  signature: {F : Type max u₀ v₀ -> Type u₁} {G : Type u₀ -> Type v₁} [ULiftable G F]
  body: down (Functor.map (ULift.up.{v₀} ∘ f) x : F (ULift β))

中文:
定义 downMap
  签名: {F : Type max u₀ v₀ -> 类型u₁} {G : 类型u₀ -> 类型v₁} [ULiftable G F]
  定义体: down (Functor.map (ULift.up.{v₀} ∘ f) x : F (ULift β))

Depends on / 依赖: Functor, Functor.map, ULift.up, _eq_head, _getD
-/
def downMap {F : Type max u₀ v₀ -> Type u₁} {G : Type u₀ -> Type v₁} [ULiftable G F]
    [Functor F] {α β} (f : α -> β) (x : F α) : G β :=
  down (Functor.map (ULift.up.{v₀} ∘ f) x : F (ULift β))

/--
Definition of `up'` / `up'` 的定义

English:
abbreviation up'
  signature: {f : Type u₀ -> Type u₁} {g : Type v₀ -> Type v₁} [ULiftable f g]
  body: ULiftable.congr Equiv.punitEquivPUnit

中文:
缩写 up'
  签名: {f : 类型u₀ -> 类型u₁} {g : 类型v₀ -> 类型v₁} [ULiftable f g]
  定义体: ULiftable.congr Equiv.punitEquivPUnit

Depends on / 依赖: Equiv.punitEquivPUnit, ULiftable, ULiftable.congr, punitEquivPUnit
-/
abbrev up' {f : Type u₀ -> Type u₁} {g : Type v₀ -> Type v₁} [ULiftable f g] :
    f PUnit -> g PUnit :=
  ULiftable.congr Equiv.punitEquivPUnit

/--
Definition of `down'` / `down'` 的定义

English:
abbreviation down'
  signature: {f : Type u₀ -> Type u₁} {g : Type v₀ -> Type v₁} [ULiftable f g]
  body: (ULiftable.congr Equiv.punitEquivPUnit).symm

中文:
缩写 down'
  签名: {f : 类型u₀ -> 类型u₁} {g : 类型v₀ -> 类型v₁} [ULiftable f g]
  定义体: (ULiftable.congr Equiv.punitEquivPUnit).symm

Depends on / 依赖: Equiv.punitEquivPUnit, Option.forall, ULiftable, ULiftable.congr, punitEquivPUnit
-/
abbrev down' {f : Type u₀ -> Type u₁} {g : Type v₀ -> Type v₁} [ULiftable f g] :
    g PUnit -> f PUnit :=
  (ULiftable.congr Equiv.punitEquivPUnit).symm

/--
theorem `up_down` / 定理 `up_down`

English:
theorem up_down
  statement: {f : Type u₀ -> Type u₁} {g : Type max u₀ v₀ -> Type v₁} [ULiftable f g] {α}
  proof: (ULiftable.congr Equiv.ulift.symm).right_inv _

中文:
定理 up_down
  结论: {f : 类型u₀ -> 类型u₁} {g : Type max u₀ v₀ -> 类型v₁} [ULiftable f g] {α}
  证明: (ULiftable.congr Equiv.ulift.symm).right_inv _

Depends on / 依赖: Equiv.ulift.symm, ULiftable, ULiftable.congr, right_inv
-/
theorem up_down {f : Type u₀ -> Type u₁} {g : Type max u₀ v₀ -> Type v₁} [ULiftable f g] {α}
    (x : g (ULift.{v₀} α)) : up (down x : f α) = x :=
  (ULiftable.congr Equiv.ulift.symm).right_inv _

/--
theorem `down_up` / 定理 `down_up`

English:
theorem down_up
  statement: {f : Type u₀ -> Type u₁} {g : Type max u₀ v₀ -> Type v₁} [ULiftable f g] {α}
  proof: (ULiftable.congr Equiv.ulift.symm).left_inv _

中文:
定理 down_up
  结论: {f : 类型u₀ -> 类型u₁} {g : Type max u₀ v₀ -> 类型v₁} [ULiftable f g] {α}
  证明: (ULiftable.congr Equiv.ulift.symm).left_inv _

Depends on / 依赖: Equiv.ulift.symm, ULiftable, ULiftable.congr, left_inv
-/
theorem down_up {f : Type u₀ -> Type u₁} {g : Type max u₀ v₀ -> Type v₁} [ULiftable f g] {α}
    (x : f α) : down (up x : g (ULift.{v₀} α)) = x :=
  (ULiftable.congr Equiv.ulift.symm).left_inv _

end ULiftable

open ULift

/--
Instance `instULiftableId` / 实例 `instULiftableId`

English:
instance instULiftableId
  signature: : ULiftable Id Id where
  body: F

中文:
实例 instULiftableId
  签名: : ULiftable Id Id where
  定义体: F
-/
instance instULiftableId : ULiftable Id Id where
  congr F := F

/-- for specific state types, this function helps to create a uliftable instance -/
@[instance_reducible]
/--
Definition of `StateT.uliftable'` / `StateT.uliftable'` 的定义

English:
definition StateT.uliftable'
  signature: {m : Type u₀ -> Type v₀} {m' : Type u₁ -> Type v₁} [ULiftable m m']
  body: StateT.equiv Equiv.piCongr F fun _ => ULiftable.congr Equiv.prodCongr G F

中文:
定义 StateT.uliftable'
  签名: {m : 类型u₀ -> 类型v₀} {m' : 类型u₁ -> 类型v₁} [ULiftable m m']
  定义体: StateT.equiv Equiv.piCongr F fun _ => ULiftable.congr Equiv.prodCongr G F

Depends on / 依赖: Equiv.piCongr, Equiv.prodCongr, StateT, StateT.equiv, ULiftable, ULiftable.congr, piCongr, prodCongr
-/
def StateT.uliftable' {m : Type u₀ -> Type v₀} {m' : Type u₁ -> Type v₁} [ULiftable m m']
    (F : s ≃ s') : ULiftable (StateT s m) (StateT s' m') where
  congr G :=
StateT.equiv Equiv.piCongr F fun _ => ULiftable.congr Equiv.prodCongr G F

instance {m m'} [ULiftable m m'] : ULiftable (StateT s m) (StateT (ULift s) m') :=
  StateT.uliftable' Equiv.ulift.symm

/--
Instance `StateT.instULiftableULiftULift` / 实例 `StateT.instULiftableULiftULift`

English:
instance StateT.instULiftableULiftULift
  signature: {m m'} [ULiftable m m']
  body: StateT.uliftable' Equiv.ulift.trans Equiv.ulift.symm

中文:
实例 StateT.instULiftableULiftULift
  签名: {m m'} [ULiftable m m']
  定义体: StateT.uliftable' Equiv.ulift.trans Equiv.ulift.symm

Depends on / 依赖: Equiv.ulift.symm, Equiv.ulift.trans, StateT, StateT.uliftable, _mem_head, _tail, cons_head, uliftable
-/
instance StateT.instULiftableULiftULift {m m'} [ULiftable m m'] :
    ULiftable (StateT (ULift.{max v₀ u₀} s) m) (StateT (ULift.{max v₁ u₀} s) m') :=
StateT.uliftable' Equiv.ulift.trans Equiv.ulift.symm

/-- for specific reader monads, this function helps to create a uliftable instance -/
@[instance_reducible]
/--
Definition of `ReaderT.uliftable'` / `ReaderT.uliftable'` 的定义

English:
definition ReaderT.uliftable'
  signature: {m m'} [ULiftable m m'] (F : s ≃ s')
  body: ReaderT.equiv Equiv.piCongr F fun _ => ULiftable.congr G

中文:
定义 ReaderT.uliftable'
  签名: {m m'} [ULiftable m m'] (F : s ≃ s')
  定义体: ReaderT.equiv Equiv.piCongr F fun _ => ULiftable.congr G

Depends on / 依赖: Equiv.piCongr, ReaderT, ReaderT.equiv, ULiftable, ULiftable.congr, _tail, cons_head, l.head, l.tail, mem_cons_self, piCongr
-/
def ReaderT.uliftable' {m m'} [ULiftable m m'] (F : s ≃ s') :
    ULiftable (ReaderT s m) (ReaderT s' m') where
congr G := ReaderT.equiv Equiv.piCongr F fun _ => ULiftable.congr G

instance {m m'} [ULiftable m m'] : ULiftable (ReaderT s m) (ReaderT (ULift s) m') :=
  ReaderT.uliftable' Equiv.ulift.symm

/--
Instance `ReaderT.instULiftableULiftULift` / 实例 `ReaderT.instULiftableULiftULift`

English:
instance ReaderT.instULiftableULiftULift
  signature: {m m'} [ULiftable m m']
  body: ReaderT.uliftable' Equiv.ulift.trans Equiv.ulift.symm

中文:
实例 ReaderT.instULiftableULiftULift
  签名: {m m'} [ULiftable m m']
  定义体: ReaderT.uliftable' Equiv.ulift.trans Equiv.ulift.symm

Depends on / 依赖: Equiv.ulift.symm, Equiv.ulift.trans, ReaderT, ReaderT.uliftable, uliftable
-/
instance ReaderT.instULiftableULiftULift {m m'} [ULiftable m m'] :
    ULiftable (ReaderT (ULift.{max v₀ u₀} s) m) (ReaderT (ULift.{max v₁ u₀} s) m') :=
ReaderT.uliftable' Equiv.ulift.trans Equiv.ulift.symm

/-- for specific continuation passing monads, this function helps to create a uliftable instance -/
@[instance_reducible]
/--
Definition of `ContT.uliftable'` / `ContT.uliftable'` 的定义

English:
definition ContT.uliftable'
  signature: {m m'} [ULiftable m m'] (F : r ≃ r')
  body: ContT.equiv (ULiftable.congr F)

中文:
定义 ContT.uliftable'
  签名: {m m'} [ULiftable m m'] (F : r ≃ r')
  定义体: ContT.equiv (ULiftable.congr F)

Depends on / 依赖: ContT.equiv, ULiftable, ULiftable.congr
-/
def ContT.uliftable' {m m'} [ULiftable m m'] (F : r ≃ r') :
    ULiftable (ContT r m) (ContT r' m') where
  congr := ContT.equiv (ULiftable.congr F)

instance {s m m'} [ULiftable m m'] : ULiftable (ContT s m) (ContT (ULift s) m') :=
  ContT.uliftable' Equiv.ulift.symm

/--
Instance `ContT.instULiftableULiftULift` / 实例 `ContT.instULiftableULiftULift`

English:
instance ContT.instULiftableULiftULift
  signature: {m m'} [ULiftable m m']
  body: ContT.uliftable' Equiv.ulift.trans Equiv.ulift.symm

中文:
实例 ContT.instULiftableULiftULift
  签名: {m m'} [ULiftable m m']
  定义体: ContT.uliftable' Equiv.ulift.trans Equiv.ulift.symm

Depends on / 依赖: ContT.uliftable, Equiv.ulift.symm, Equiv.ulift.trans, uliftable
-/
instance ContT.instULiftableULiftULift {m m'} [ULiftable m m'] :
    ULiftable (ContT (ULift.{max v₀ u₀} s) m) (ContT (ULift.{max v₁ u₀} s) m') :=
ContT.uliftable' Equiv.ulift.trans Equiv.ulift.symm

/-- for specific writer monads, this function helps to create a uliftable instance -/
@[instance_reducible]
/--
Definition of `WriterT.uliftable'` / `WriterT.uliftable'` 的定义

English:
definition WriterT.uliftable'
  signature: {m m'} [ULiftable m m'] (F : w ≃ w')
  body: WriterT.equiv ULiftable.congr Equiv.prodCongr G F

中文:
定义 WriterT.uliftable'
  签名: {m m'} [ULiftable m m'] (F : w ≃ w')
  定义体: WriterT.equiv ULiftable.congr Equiv.prodCongr G F

Depends on / 依赖: Equiv.prodCongr, ULiftable, ULiftable.congr, WriterT, WriterT.equiv, prodCongr
-/
def WriterT.uliftable' {m m'} [ULiftable m m'] (F : w ≃ w') :
    ULiftable (WriterT w m) (WriterT w' m') where
congr G := WriterT.equiv ULiftable.congr Equiv.prodCongr G F

instance {m m'} [ULiftable m m'] : ULiftable (WriterT s m) (WriterT (ULift s) m') :=
  WriterT.uliftable' Equiv.ulift.symm

/--
Instance `WriterT.instULiftableULiftULift` / 实例 `WriterT.instULiftableULiftULift`

English:
instance WriterT.instULiftableULiftULift
  signature: {m m'} [ULiftable m m']
  body: WriterT.uliftable' Equiv.ulift.trans Equiv.ulift.symm

中文:
实例 WriterT.instULiftableULiftULift
  签名: {m m'} [ULiftable m m']
  定义体: WriterT.uliftable' Equiv.ulift.trans Equiv.ulift.symm

Depends on / 依赖: Equiv.ulift.symm, Equiv.ulift.trans, WriterT, WriterT.uliftable, uliftable
-/
instance WriterT.instULiftableULiftULift {m m'} [ULiftable m m'] :
    ULiftable (WriterT (ULift.{max v₀ u₀} s) m) (WriterT (ULift.{max v₁ u₀} s) m') :=
WriterT.uliftable' Equiv.ulift.trans Equiv.ulift.symm

/--
Instance `Except.instULiftable` / 实例 `Except.instULiftable`

English:
instance Except.instULiftable
  signature: {ε : Type u₀}
  body: { toFun := Except.map e
      invFun := Except.map e.symm
      left_inv := fun f => by cases f <;> simp [Except.map]
      right_inv := fun f => by cases f <;> simp [Except.map] }

中文:
实例 Except.instULiftable
  签名: {ε : 类型u₀}
  定义体: { toFun := Except.map e
      invFun := Except.map e.symm
      left_inv := fun f => by cases f <;> simp [Except.map]
      right_inv := fun f => by cases f <;> simp [Except.map] }

Depends on / 依赖: Except, Except.map, e.symm, invFun, left_inv, right_inv
-/
instance Except.instULiftable {ε : Type u₀} :
    ULiftable (Except.{u₀, v₁} ε) (Except.{u₀, v₂} ε) where
  congr e :=
    { toFun := Except.map e
      invFun := Except.map e.symm
      left_inv := fun f => by cases f <;> simp [Except.map]
      right_inv := fun f => by cases f <;> simp [Except.map] }

/--
Instance `Option.instULiftable` / 实例 `Option.instULiftable`

English:
instance Option.instULiftable
  signature: : ULiftable Option.{u₀} Option.{u₁} where
  body: { toFun := Option.map e
      invFun := Option.map e.symm
      left_inv := fun f => by cases f <;> simp
      right_inv := fun f => by cases f <;> simp }

中文:
实例 Option.instULiftable
  签名: : ULiftable Option.{u₀} Option.{u₁} where
  定义体: { toFun := Option.map e
      invFun := Option.map e.symm
      left_inv := fun f => by cases f <;> simp
      right_inv := fun f => by cases f <;> simp }

Depends on / 依赖: Option.map, e.symm, invFun, left_inv, right_inv
-/
instance Option.instULiftable : ULiftable Option.{u₀} Option.{u₁} where
  congr e :=
    { toFun := Option.map e
      invFun := Option.map e.symm
      left_inv := fun f => by cases f <;> simp
      right_inv := fun f => by cases f <;> simp }
