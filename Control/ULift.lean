/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Jannis Limperg
-/
module

public import Mathlib.Init
/-!
# Monadic instances for `ULift` and `PLift`

In this file we define `Monad` and `IsLawfulMonad` instances on `PLift` and `ULift`. -/

@[expose] public section

universe u v u' v'

namespace PLift

variable {α : Sort u} {β : Sort v}

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : α -> β) (a : PLift α)
  body: PLift.up (f a.down)

@[simp]

中文:
定义 map
  签名: (f : α -> β) (a : 命题层提升 α)
  定义体: PLift.up (f a.down)

@[simp]
-/
protected def map (f : α -> β) (a : PLift α) : PLift β :=
  PLift.up (f a.down)

@[simp]
/--
theorem `map_up` / 定理 `map_up`

English:
theorem map_up
  given: (f : α -> β) (a : α)
  statement: (PLift.up a).map f = PLift.up (f a)
  proof: rfl

中文:
定理 map_up
  条件: (f : α -> β) (a : α)
  结论: (命题层提升.up a).map f = 命题层提升.up (f a)
  证明: rfl
-/
theorem map_up (f : α -> β) (a : α) : (PLift.up a).map f = PLift.up (f a) :=
  rfl

/-- Embedding of pure values. -/
@[simp]
/--
Definition of `pure` / `pure` 的定义

English:
definition pure
  signature: : α -> PLift α
  body: up

中文:
定义 pure
  签名: : α -> 命题层提升 α
  定义体: up
-/
protected def pure : α -> PLift α :=
  up

/--
Definition of `seq` / `seq` 的定义

English:
definition seq
  signature: (f : PLift (α -> β)) (x : Unit -> PLift α)
  body: PLift.up (f.down (x ()).down)

@[simp]

中文:
定义 seq
  签名: (f : 命题层提升 (α -> β)) (x : 单元 -> 命题层提升 α)
  定义体: PLift.up (f.down (x ()).down)

@[simp]
-/
protected def seq (f : PLift (α -> β)) (x : Unit -> PLift α) : PLift β :=
  PLift.up (f.down (x ()).down)

@[simp]
/--
theorem `seq_up` / 定理 `seq_up`

English:
theorem seq_up
  given: (f : α -> β) (x : α)
  statement: (PLift.up f).seq (fun _ => PLift.up x) = PLift.up (f x)
  proof: rfl

中文:
定理 seq_up
  条件: (f : α -> β) (x : α)
  结论: (命题层提升.up f).seq (fun _ => 命题层提升.up x) = 命题层提升.up (f x)
  证明: rfl
-/
theorem seq_up (f : α -> β) (x : α) : (PLift.up f).seq (fun _ => PLift.up x) = PLift.up (f x) :=
  rfl

/--
Definition of `bind` / `bind` 的定义

English:
definition bind
  signature: (a : PLift α) (f : α -> PLift β)
  body: f a.down

@[simp]

中文:
定义 bind
  签名: (a : 命题层提升 α) (f : α -> 命题层提升 β)
  定义体: f a.down

@[simp]
-/
protected def bind (a : PLift α) (f : α -> PLift β) : PLift β :=
  f a.down

@[simp]
/--
theorem `bind_up` / 定理 `bind_up`

English:
theorem bind_up
  given: (a : α) (f : α -> PLift β)
  statement: (PLift.up a).bind f = f a
  proof: rfl

中文:
定理 bind_up
  条件: (a : α) (f : α -> 命题层提升 β)
  结论: (命题层提升.up a).bind f = f a
  证明: rfl
-/
theorem bind_up (a : α) (f : α -> PLift β) : (PLift.up a).bind f = f a :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Monad PLift
  body: @PLift.map
  pure := @PLift.pure
  seq := @PLift.seq
  bind := @PLift.bind

中文:
实例 :
  签名: 单子 命题层提升
  定义体: @PLift.map
  pure := @PLift.pure
  seq := @PLift.seq
  bind := @PLift.bind

Depends on / 依赖: PLift.map
-/
instance : Monad PLift where
  map := @PLift.map
  pure := @PLift.pure
  seq := @PLift.seq
  bind := @PLift.bind

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulFunctor PLift
  body: @fun _ ⟨_⟩ => rfl
  comp_map := @fun _ _ _ _ _ ⟨_⟩ => rfl
  map_const := @fun _ _ => rfl

中文:
实例 :
  签名: Lawful函子 命题层提升
  定义体: @fun _ ⟨_⟩ => rfl
  comp_map := @fun _ _ _ _ _ ⟨_⟩ => rfl
  map_const := @fun _ _ => rfl
-/
instance : LawfulFunctor PLift where
  id_map := @fun _ ⟨_⟩ => rfl
  comp_map := @fun _ _ _ _ _ ⟨_⟩ => rfl
  map_const := @fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulApplicative PLift
  body: @fun _ _ _ _ => rfl
  seqRight_eq := @fun _ _ _ _ => rfl
  pure_seq := @fun _ _ _ ⟨_⟩ => rfl
  map_pure := @fun _ _ _ _ => rfl
  seq_pure := @fun _ _ ⟨_⟩ _ => rfl
  seq_assoc := @fun _ _ _ ⟨_⟩ ⟨_⟩ ⟨_⟩ => rfl

中文:
实例 :
  签名: 合法适用 命题层提升
  定义体: @fun _ _ _ _ => rfl
  seqRight_eq := @fun _ _ _ _ => rfl
  pure_seq := @fun _ _ _ ⟨_⟩ => rfl
  map_pure := @fun _ _ _ _ => rfl
  seq_pure := @fun _ _ ⟨_⟩ _ => rfl
  seq_assoc := @fun _ _ _ ⟨_⟩ ⟨_⟩ ⟨_⟩ => rfl
-/
instance : LawfulApplicative PLift where
  seqLeft_eq := @fun _ _ _ _ => rfl
  seqRight_eq := @fun _ _ _ _ => rfl
  pure_seq := @fun _ _ _ ⟨_⟩ => rfl
  map_pure := @fun _ _ _ _ => rfl
  seq_pure := @fun _ _ ⟨_⟩ _ => rfl
  seq_assoc := @fun _ _ _ ⟨_⟩ ⟨_⟩ ⟨_⟩ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulMonad PLift
  body: @fun _ _ _ ⟨_⟩ => rfl
  bind_map := @fun _ _ ⟨_⟩ ⟨_⟩ => rfl
  pure_bind := @fun _ _ _ _ => rfl
  bind_assoc := @fun _ _ _ ⟨_⟩ _ _ => rfl

@[simp]

中文:
实例 :
  签名: 合法单子 命题层提升
  定义体: @fun _ _ _ ⟨_⟩ => rfl
  bind_map := @fun _ _ ⟨_⟩ ⟨_⟩ => rfl
  pure_bind := @fun _ _ _ _ => rfl
  bind_assoc := @fun _ _ _ ⟨_⟩ _ _ => rfl

@[simp]
-/
instance : LawfulMonad PLift where
  bind_pure_comp := @fun _ _ _ ⟨_⟩ => rfl
  bind_map := @fun _ _ ⟨_⟩ ⟨_⟩ => rfl
  pure_bind := @fun _ _ _ _ => rfl
  bind_assoc := @fun _ _ _ ⟨_⟩ _ _ => rfl

@[simp]
/--
theorem `rec.constant` / 定理 `rec.constant`

English:
theorem rec.constant
  given: {α : Sort u} {β : Type v} (b : β)
  proof: rfl

中文:
定理 rec.constant
  条件: {α : 类型层 u} {β : 类型v} (b : β)
  证明: rfl
-/
theorem rec.constant {α : Sort u} {β : Type v} (b : β) :
    (@PLift.rec α (fun _ => β) fun _ => b) = fun _ => b := rfl

end PLift

namespace ULift

variable {α : Type u} {β : Type v}

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : α -> β) (a : ULift.{u'} α)
  body: ULift.up.{v'} (f a.down)

@[simp]

中文:
定义 map
  签名: (f : α -> β) (a : 类型层提升.{u'} α)
  定义体: ULift.up.{v'} (f a.down)

@[simp]
-/
protected def map (f : α -> β) (a : ULift.{u'} α) : ULift.{v'} β := ULift.up.{v'} (f a.down)

@[simp]
/--
theorem `map_up` / 定理 `map_up`

English:
theorem map_up
  given: (f : α -> β) (a : α)
  statement: (ULift.up.{u'} a).map f = ULift.up.{v'} (f a)
  proof: rfl

中文:
定理 map_up
  条件: (f : α -> β) (a : α)
  结论: (类型层提升.up.{u'} a).map f = 类型层提升.up.{v'} (f a)
  证明: rfl
-/
theorem map_up (f : α -> β) (a : α) : (ULift.up.{u'} a).map f = ULift.up.{v'} (f a) := rfl

/-- Embedding of pure values. -/
@[simp]
/--
Definition of `pure` / `pure` 的定义

English:
definition pure
  signature: : α -> ULift α
  body: up

中文:
定义 pure
  签名: : α -> 类型层提升 α
  定义体: up
-/
protected def pure : α -> ULift α :=
  up

/--
Definition of `seq` / `seq` 的定义

English:
definition seq
  signature: {α β} (f : ULift (α -> β)) (x : Unit -> ULift α)
  body: ULift.up.{u} (f.down (x ()).down)

@[simp]

中文:
定义 seq
  签名: {α β} (f : 类型层提升 (α -> β)) (x : 单元 -> 类型层提升 α)
  定义体: ULift.up.{u} (f.down (x ()).down)

@[simp]
-/
protected def seq {α β} (f : ULift (α -> β)) (x : Unit -> ULift α) : ULift β :=
  ULift.up.{u} (f.down (x ()).down)

@[simp]
/--
theorem `seq_up` / 定理 `seq_up`

English:
theorem seq_up
  given: (f : α -> β) (x : α)
  statement: (ULift.up f).seq (fun _ => ULift.up x) = ULift.up (f x)
  proof: rfl

中文:
定理 seq_up
  条件: (f : α -> β) (x : α)
  结论: (类型层提升.up f).seq (fun _ => 类型层提升.up x) = 类型层提升.up (f x)
  证明: rfl
-/
theorem seq_up (f : α -> β) (x : α) : (ULift.up f).seq (fun _ => ULift.up x) = ULift.up (f x) :=
  rfl

/--
Definition of `bind` / `bind` 的定义

English:
definition bind
  signature: (a : ULift α) (f : α -> ULift β)
  body: f a.down

@[simp]

中文:
定义 bind
  签名: (a : 类型层提升 α) (f : α -> 类型层提升 β)
  定义体: f a.down

@[simp]
-/
protected def bind (a : ULift α) (f : α -> ULift β) : ULift β :=
  f a.down

@[simp]
/--
theorem `bind_up` / 定理 `bind_up`

English:
theorem bind_up
  given: (a : α) (f : α -> ULift β)
  statement: (ULift.up a).bind f = f a
  proof: rfl

中文:
定理 bind_up
  条件: (a : α) (f : α -> 类型层提升 β)
  结论: (类型层提升.up a).bind f = f a
  证明: rfl
-/
theorem bind_up (a : α) (f : α -> ULift β) : (ULift.up a).bind f = f a :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Monad ULift
  body: @ULift.map
  pure := @ULift.pure
  seq := @ULift.seq
  bind := @ULift.bind

中文:
实例 :
  签名: 单子 类型层提升
  定义体: @ULift.map
  pure := @ULift.pure
  seq := @ULift.seq
  bind := @ULift.bind

Depends on / 依赖: ULift.map
-/
instance : Monad ULift where
  map := @ULift.map
  pure := @ULift.pure
  seq := @ULift.seq
  bind := @ULift.bind

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulFunctor ULift
  body: @fun _ ⟨_⟩ => rfl
  comp_map := @fun _ _ _ _ _ ⟨_⟩ => rfl
  map_const := @fun _ _ => rfl

中文:
实例 :
  签名: Lawful函子 类型层提升
  定义体: @fun _ ⟨_⟩ => rfl
  comp_map := @fun _ _ _ _ _ ⟨_⟩ => rfl
  map_const := @fun _ _ => rfl
-/
instance : LawfulFunctor ULift where
  id_map := @fun _ ⟨_⟩ => rfl
  comp_map := @fun _ _ _ _ _ ⟨_⟩ => rfl
  map_const := @fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulApplicative ULift
  body: @fun _ _ _ _ => rfl
  seqRight_eq := @fun _ _ _ _ => rfl
  pure_seq := @fun _ _ _ ⟨_⟩ => rfl
  map_pure := @fun _ _ _ _ => rfl
  seq_pure := @fun _ _ ⟨_⟩ _ => rfl
  seq_assoc := @fun _ _ _ ⟨_⟩ ⟨_⟩ ⟨_⟩ => rfl

中文:
实例 :
  签名: 合法适用 类型层提升
  定义体: @fun _ _ _ _ => rfl
  seqRight_eq := @fun _ _ _ _ => rfl
  pure_seq := @fun _ _ _ ⟨_⟩ => rfl
  map_pure := @fun _ _ _ _ => rfl
  seq_pure := @fun _ _ ⟨_⟩ _ => rfl
  seq_assoc := @fun _ _ _ ⟨_⟩ ⟨_⟩ ⟨_⟩ => rfl
-/
instance : LawfulApplicative ULift where
  seqLeft_eq := @fun _ _ _ _ => rfl
  seqRight_eq := @fun _ _ _ _ => rfl
  pure_seq := @fun _ _ _ ⟨_⟩ => rfl
  map_pure := @fun _ _ _ _ => rfl
  seq_pure := @fun _ _ ⟨_⟩ _ => rfl
  seq_assoc := @fun _ _ _ ⟨_⟩ ⟨_⟩ ⟨_⟩ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulMonad ULift
  body: @fun _ _ _ ⟨_⟩ => rfl
  bind_map := @fun _ _ ⟨_⟩ ⟨_⟩ => rfl
  pure_bind := @fun _ _ _ _ => rfl
  bind_assoc := @fun _ _ _ ⟨_⟩ _ _ => rfl

@[simp]

中文:
实例 :
  签名: 合法单子 类型层提升
  定义体: @fun _ _ _ ⟨_⟩ => rfl
  bind_map := @fun _ _ ⟨_⟩ ⟨_⟩ => rfl
  pure_bind := @fun _ _ _ _ => rfl
  bind_assoc := @fun _ _ _ ⟨_⟩ _ _ => rfl

@[simp]
-/
instance : LawfulMonad ULift where
  bind_pure_comp := @fun _ _ _ ⟨_⟩ => rfl
  bind_map := @fun _ _ ⟨_⟩ ⟨_⟩ => rfl
  pure_bind := @fun _ _ _ _ => rfl
  bind_assoc := @fun _ _ _ ⟨_⟩ _ _ => rfl

@[simp]
/--
theorem `rec.constant` / 定理 `rec.constant`

English:
theorem rec.constant
  given: {α : Type u} {β : Sort v} (b : β)
  proof: rfl

中文:
定理 rec.constant
  条件: {α : 类型u} {β : 类型层 v} (b : β)
  证明: rfl
-/
theorem rec.constant {α : Type u} {β : Sort v} (b : β) :
    (@ULift.rec α (fun _ => β) fun _ => b) = fun _ => b := rfl

end ULift
