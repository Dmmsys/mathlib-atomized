/-
Copyright (c) 2017 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
module

public import Mathlib.Data.Set.Defs

import Mathlib.Tactic.Attr.Register

/-!
# Functors

This module provides additional lemmas, definitions, and instances for `Functor`s.

## Main definitions

* `Functor.Const α` is the functor that sends all types to `α`.
* `Functor.AddConst α` is `Functor.Const α` but for when `α` has an additive structure.
* `Functor.Comp F G` for functors `F` and `G` is the functor composition of `F` and `G`.
* `Liftp` and `Liftr` respectively lift predicates and relations on a type `α`
  to `F α`. Terms of `F α` are considered to, in some sense, contain values of type `α`.

## Tags

functor, applicative
-/

@[expose] public section

universe u v w

section Functor

variable {F : Type u -> Type v}
variable {α β γ : Type u}
variable [Functor F] [LawfulFunctor F]

/--
theorem `Functor.map_id` / 定理 `Functor.map_id`

English:
theorem Functor.map_id
  statement: (id <$> ·) = (id : F α -> F α)
  proof: funext id_map

中文:
定理 Functor.map_id
  结论: (id <$> ·) = (id : F α -> F α)
  证明: funext id_map

Depends on / 依赖: id_map
-/
theorem Functor.map_id : (id <$> ·) = (id : F α -> F α) := funext id_map

/--
theorem `Functor.map_comp_map` / 定理 `Functor.map_comp_map`

English:
theorem Functor.map_comp_map
  given: (f : α -> β) (g : β -> γ)
  proof: funext fun _ => (comp_map _ _ _).symm

中文:
定理 Functor.map_comp_map
  条件: (f : α -> β) (g : β -> γ)
  证明: funext fun _ => (comp_map _ _ _).symm

Depends on / 依赖: comp_map
-/
theorem Functor.map_comp_map (f : α -> β) (g : β -> γ) :
    ((g <$> ·) ∘ (f <$> ·) : F α -> F γ) = ((g ∘ f) <$> ·) :=
  funext fun _ => (comp_map _ _ _).symm

set_option linter.overlappingInstances false in
/--
theorem `Functor.ext` / 定理 `Functor.ext`

English:
theorem Functor.ext
  given: {F}
  proof: @map_const _ ⟨@m, @mc⟩ H1
    have E2 := @map_const _ ⟨@m, @mc'⟩ H2
    exact E1.trans E2.symm

中文:
定理 Functor.ext
  条件: {F}
  证明: @map_const _ ⟨@m, @mc⟩ H1
    have E2 := @map_const _ ⟨@m, @mc'⟩ H2
    exact E1.trans E2.symm

Depends on / 依赖: map_const
-/
theorem Functor.ext {F} :
    forall {F1 : Functor F} {F2 : Functor F} [@LawfulFunctor F F1] [@LawfulFunctor F F2],
    (forall (α β) (f : α -> β) (x : F α), @Functor.map _ F1 _ _ f x = @Functor.map _ F2 _ _ f x) ->
    F1 = F2
  | ⟨m, mc⟩, ⟨m', mc'⟩, H1, H2, H => by
    cases show @m = @m' by funext α β f x; apply H
    congr
    funext α β
    have E1 := @map_const _ ⟨@m, @mc⟩ H1
    have E2 := @map_const _ ⟨@m, @mc'⟩ H2
    exact E1.trans E2.symm

end Functor

namespace Functor

/-- `Const α` is the constant functor, mapping every type to `α`. When
`α` has a monoid structure, `Const α` has an `Applicative` instance.
(If `α` has an additive monoid structure, see `Functor.AddConst`.) -/
@[nolint unusedArguments]
/--
Definition of `Const` / `Const` 的定义

English:
definition Const
  signature: (α : Type*) (_β : Type*)
  body: α

中文:
定义 Const
  签名: (α : 类型) (_β : 类型)
  定义体: α
-/
def Const (α : Type*) (_β : Type*) :=
  α

/-- `Const.mk` is the canonical map `α → Const α β` (the identity), and
it can be used as a pattern to extract this value. -/
@[match_pattern]
/--
Definition of `Const.mk` / `Const.mk` 的定义

English:
definition Const.mk
  signature: {α β} (x : α)
  body: x

中文:
定义 Const.mk
  签名: {α β} (x : α)
  定义体: x
-/
def Const.mk {α β} (x : α) : Const α β :=
  x

/--
Definition of `Const.mk'` / `Const.mk'` 的定义

English:
definition Const.mk'
  signature: {α} (x : α)
  body: x

中文:
定义 Const.mk'
  签名: {α} (x : α)
  定义体: x
-/
def Const.mk' {α} (x : α) : Const α PUnit :=
  x

/--
Definition of `Const.run` / `Const.run` 的定义

English:
definition Const.run
  signature: {α β} (x : Const α β)
  body: x

中文:
定义 Const.run
  签名: {α β} (x : Const α β)
  定义体: x
-/
def Const.run {α β} (x : Const α β) : α :=
  x

namespace Const

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {α β} {x y : Const α β} (h : x.run = y.run)
  statement: x = y
  proof: h

中文:
定理 ext
  条件: {α β} {x y : Const α β} (h : x.run = y.run)
  结论: x = y
  证明: h
-/
protected theorem ext {α β} {x y : Const α β} (h : x.run = y.run) : x = y :=
  h

/-- The map operation of the `Const γ` functor. -/
@[nolint unusedArguments]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {γ α β} (_f : α -> β) (x : Const γ β)
  body: x

中文:
定义 map
  签名: {γ α β} (_f : α -> β) (x : Const γ β)
  定义体: x
-/
protected def map {γ α β} (_f : α -> β) (x : Const γ β) : Const γ α :=
  x

/--
Instance `functor` / 实例 `functor`

English:
instance functor
  signature: {γ}
  body: @Const.map γ

中文:
实例 functor
  签名: {γ}
  定义体: @Const.map γ

Depends on / 依赖: Const.map
-/
instance functor {γ} : Functor (Const γ) where map := @Const.map γ

/--
Instance `lawfulFunctor` / 实例 `lawfulFunctor`

English:
instance lawfulFunctor
  signature: {γ}
  body: by constructor <;> intros <;> rfl

中文:
实例 lawfulFunctor
  签名: {γ}
  定义体: by constructor <;> intros <;> rfl

Depends on / 依赖: intros
-/
instance lawfulFunctor {γ} : LawfulFunctor (Const γ) := by constructor <;> intros <;> rfl

instance {α β} [Inhabited α] : Inhabited (Const α β) :=
  ⟨(default : α)⟩

end Const

/--
Definition of `AddConst` / `AddConst` 的定义

English:
definition AddConst
  signature: (α : Type*)
  body: Const α

中文:
定义 AddConst
  签名: (α : 类型)
  定义体: Const α
-/
def AddConst (α : Type*) :=
  Const α

/-- `AddConst.mk` is the canonical map `α → AddConst α β`, which is the identity,
where `AddConst α β = Const α β`. It can be used as a pattern to extract this value. -/
@[match_pattern]
/--
Definition of `AddConst.mk` / `AddConst.mk` 的定义

English:
definition AddConst.mk
  signature: {α β} (x : α)
  body: x

中文:
定义 AddConst.mk
  签名: {α β} (x : α)
  定义体: x
-/
def AddConst.mk {α β} (x : α) : AddConst α β :=
  x

/--
Definition of `AddConst.run` / `AddConst.run` 的定义

English:
definition AddConst.run
  signature: {α β}
  body: id

中文:
定义 AddConst.run
  签名: {α β}
  定义体: id
-/
def AddConst.run {α β} : AddConst α β -> α :=
  id

/--
Instance `AddConst.functor` / 实例 `AddConst.functor`

English:
instance AddConst.functor
  signature: {γ}
  body: @Const.functor γ

中文:
实例 AddConst.functor
  签名: {γ}
  定义体: @Const.functor γ

Depends on / 依赖: Const.functor, functor
-/
instance AddConst.functor {γ} : Functor (AddConst γ) :=
  @Const.functor γ

/--
Instance `AddConst.lawfulFunctor` / 实例 `AddConst.lawfulFunctor`

English:
instance AddConst.lawfulFunctor
  signature: {γ}
  body: @Const.lawfulFunctor γ

中文:
实例 AddConst.lawfulFunctor
  签名: {γ}
  定义体: @Const.lawfulFunctor γ

Depends on / 依赖: Const.lawfulFunctor, lawfulFunctor
-/
instance AddConst.lawfulFunctor {γ} : LawfulFunctor (AddConst γ) :=
  @Const.lawfulFunctor γ

instance {α β} [Inhabited α] : Inhabited (AddConst α β) :=
  ⟨(default : α)⟩

/--
Definition of `Comp` / `Comp` 的定义

English:
definition Comp
  signature: (F : Type u -> Type w) (G : Type v -> Type u) (α : Type v)
  body: F G α

中文:
定义 Comp
  签名: (F : 类型u -> Type w) (G : 类型v -> 类型u) (α : 类型v)
  定义体: F G α
-/
def Comp (F : Type u -> Type w) (G : Type v -> Type u) (α : Type v) : Type w :=
F G α

/-- Construct a term of `Comp F G α` from a term of `F (G α)`, which is the same type.
Can be used as a pattern to extract a term of `F (G α)`. -/
@[match_pattern]
/--
Definition of `Comp.mk` / `Comp.mk` 的定义

English:
definition Comp.mk
  signature: {F : Type u -> Type w} {G : Type v -> Type u} {α : Type v} (x : F (G α))
  body: x

中文:
定义 Comp.mk
  签名: {F : 类型u -> Type w} {G : 类型v -> 类型u} {α : 类型v} (x : F (G α))
  定义体: x
-/
def Comp.mk {F : Type u -> Type w} {G : Type v -> Type u} {α : Type v} (x : F (G α)) : Comp F G α :=
  x

/--
Definition of `Comp.run` / `Comp.run` 的定义

English:
definition Comp.run
  signature: {F : Type u -> Type w} {G : Type v -> Type u} {α : Type v} (x : Comp F G α)
  body: x

中文:
定义 Comp.run
  签名: {F : 类型u -> Type w} {G : 类型v -> 类型u} {α : 类型v} (x : Comp F G α)
  定义体: x
-/
def Comp.run {F : Type u -> Type w} {G : Type v -> Type u} {α : Type v} (x : Comp F G α) : F (G α) :=
  x

namespace Comp

variable {F : Type u -> Type w} {G : Type v -> Type u}

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {α} {x y : Comp F G α}
  statement: x.run = y.run -> x = y
  proof: id

中文:
定理 ext
  条件: {α} {x y : Comp F G α}
  结论: x.run = y.run -> x = y
  证明: id
-/
protected theorem ext {α} {x y : Comp F G α} : x.run = y.run -> x = y :=
  id

instance {α} [Inhabited (F (G α))] : Inhabited (Comp F G α) :=
  ⟨(default : F (G α))⟩

variable [Functor F] [Functor G]

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {α β : Type v} (h : α -> β)

中文:
定义 map
  签名: {α β : 类型v} (h : α -> β)
-/
protected def map {α β : Type v} (h : α -> β) : Comp F G α -> Comp F G β
  | Comp.mk x => Comp.mk ((h <$> ·) <$> x)

/--
Instance `functor` / 实例 `functor`

English:
instance functor
  signature: : Functor (Comp F G) where map
  body: @Comp.map F G _ _

@[functor_norm]

中文:
实例 functor
  签名: : Functor (Comp F G) where map
  定义体: @Comp.map F G _ _

@[functor_norm]

Depends on / 依赖: Comp.map
-/
instance functor : Functor (Comp F G) where map := @Comp.map F G _ _

@[functor_norm]
/--
theorem `map_mk` / 定理 `map_mk`

English:
theorem map_mk
  given: {α β} (h : α -> β) (x : F (G α))
  statement: h < > Comp.mk x = Comp.mk ((h <$> ·) <$> x)
  proof: rfl

@[simp]

中文:
定理 map_mk
  条件: {α β} (h : α -> β) (x : F (G α))
  结论: h < > Comp.mk x = Comp.mk ((h <$> ·) <$> x)
  证明: rfl

@[simp]
-/
theorem map_mk {α β} (h : α -> β) (x : F (G α)) : h < > Comp.mk x = Comp.mk ((h <$> ·) <$> x) :=
  rfl

@[simp]
/--
theorem `run_map` / 定理 `run_map`

English:
theorem run_map
  given: {α β} (h : α -> β) (x : Comp F G α)
  proof: rfl

中文:
定理 run_map
  条件: {α β} (h : α -> β) (x : Comp F G α)
  证明: rfl
-/
protected theorem run_map {α β} (h : α -> β) (x : Comp F G α) :
(h <$> x).run = (h <$> ·) < > x.run :=
  rfl

variable [LawfulFunctor F] [LawfulFunctor G]
variable {α β γ : Type v}

set_option backward.isDefEq.respectTransparency false in
/--
theorem `id_map` / 定理 `id_map`

English:
theorem id_map
  statement: forall x : Comp F G α, Comp.map id x = x

中文:
定理 id_map
  结论: 对任意 x : Comp F G α, Comp.map id x = x
-/
protected theorem id_map : forall x : Comp F G α, Comp.map id x = x
  | Comp.mk x => by simp only [Comp.map, id_map, id_map']; rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `comp_map` / 定理 `comp_map`

English:
theorem comp_map
  given: (g' : α -> β) (h : β -> γ)

中文:
定理 comp_map
  条件: (g' : α -> β) (h : β -> γ)
-/
protected theorem comp_map (g' : α -> β) (h : β -> γ) :
    forall x : Comp F G α, Comp.map (h ∘ g') x = Comp.map h (Comp.map g' x)
  | Comp.mk x => by simp [Comp.map, Comp.mk, functor_norm, Function.comp_def]

/--
Instance `lawfulFunctor` / 实例 `lawfulFunctor`

English:
instance lawfulFunctor
  signature: : LawfulFunctor (Comp F G) where
  body: rfl
  id_map := Comp.id_map
  comp_map := Comp.comp_map

中文:
实例 lawfulFunctor
  签名: : LawfulFunctor (Comp F G) where
  定义体: rfl
  id_map := Comp.id_map
  comp_map := Comp.comp_map
-/
instance lawfulFunctor : LawfulFunctor (Comp F G) where
  map_const := rfl
  id_map := Comp.id_map
  comp_map := Comp.comp_map

/--
theorem `functor_comp_id` / 定理 `functor_comp_id`

English:
theorem functor_comp_id
  given: {F} [AF : Functor F] [LawfulFunctor F]
  proof: @Functor.ext F _ AF (Comp.lawfulFunctor (G := Id)) _ fun _ _ _ _ => rfl

中文:
定理 functor_comp_id
  条件: {F} [AF : Functor F] [LawfulFunctor F]
  证明: @Functor.ext F _ AF (Comp.lawfulFunctor (G := Id)) _ fun _ _ _ _ => rfl
-/
theorem functor_comp_id {F} [AF : Functor F] [LawfulFunctor F] :
    Comp.functor (G := Id) = AF :=
  @Functor.ext F _ AF (Comp.lawfulFunctor (G := Id)) _ fun _ _ _ _ => rfl

/--
theorem `functor_id_comp` / 定理 `functor_id_comp`

English:
theorem functor_id_comp
  given: {F} [AF : Functor F] [LawfulFunctor F]
  statement: Comp.functor (F := Id) = AF
  proof: @Functor.ext F _ AF (Comp.lawfulFunctor (F := Id)) _ fun _ _ _ _ => rfl

中文:
定理 functor_id_comp
  条件: {F} [AF : Functor F] [LawfulFunctor F]
  结论: Comp.functor (F := Id) = AF
  证明: @Functor.ext F _ AF (Comp.lawfulFunctor (F := Id)) _ fun _ _ _ _ => rfl
-/
theorem functor_id_comp {F} [AF : Functor F] [LawfulFunctor F] : Comp.functor (F := Id) = AF :=
  @Functor.ext F _ AF (Comp.lawfulFunctor (F := Id)) _ fun _ _ _ _ => rfl

end Comp

namespace Comp

open Function hiding comp

open Functor

variable {F : Type u -> Type w} {G : Type v -> Type u}
variable [Applicative F] [Applicative G]

/--
Definition of `seq` / `seq` 的定义

English:
definition seq
  signature: {α β : Type v}

中文:
定义 seq
  签名: {α β : 类型v}
-/
protected def seq {α β : Type v} : Comp F G (α -> β) -> (Unit -> Comp F G α) -> Comp F G β
  | Comp.mk f, g => match g () with
| Comp.mk x => Comp.mk (· <*> ·) < > f <*> x
-- `ₓ` because the type of `Seq.seq` doesn't match `has_seq.seq`

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Pure (Comp F G)
  body: ⟨fun x => Comp.mk pure pure x⟩

中文:
实例 :
  签名: Pure (Comp F G)
  定义体: ⟨fun x => Comp.mk pure pure x⟩

Depends on / 依赖: Comp.mk
-/
instance : Pure (Comp F G) :=
⟨fun x => Comp.mk pure pure x⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Seq (Comp F G)
  body: ⟨fun f x => Comp.seq f x⟩

@[simp]

中文:
实例 :
  签名: Seq (Comp F G)
  定义体: ⟨fun f x => Comp.seq f x⟩

@[simp]

Depends on / 依赖: Comp.seq
-/
instance : Seq (Comp F G) :=
  ⟨fun f x => Comp.seq f x⟩

@[simp]
/--
theorem `run_pure` / 定理 `run_pure`

English:
theorem run_pure
  given: {α : Type v}
  statement: forall x : α, (pure x : Comp F G α).run = pure (pure x)

中文:
定理 run_pure
  条件: {α : 类型v}
  结论: 对任意 x : α, (pure x : Comp F G α).run = pure (pure x)
-/
protected theorem run_pure {α : Type v} : forall x : α, (pure x : Comp F G α).run = pure (pure x)
  | _ => rfl

@[simp]
/--
theorem `run_seq` / 定理 `run_seq`

English:
theorem run_seq
  given: {α β : Type v} (f : Comp F G (α -> β)) (x : Comp F G α)
  proof: rfl

中文:
定理 run_seq
  条件: {α β : 类型v} (f : Comp F G (α -> β)) (x : Comp F G α)
  证明: rfl
-/
protected theorem run_seq {α β : Type v} (f : Comp F G (α -> β)) (x : Comp F G α) :
(f <*> x).run = (· <*> ·) < > f.run <*> x.run :=
  rfl

/--
Instance `instApplicativeComp` / 实例 `instApplicativeComp`

English:
instance instApplicativeComp
  signature: : Applicative (Comp F G)
  body: { map := @Comp.map F G _ _, seq := @Comp.seq F G _ _ }

中文:
实例 instApplicativeComp
  签名: : Applicative (Comp F G)
  定义体: { map := @Comp.map F G _ _, seq := @Comp.seq F G _ _ }

Depends on / 依赖: Comp.map, Comp.seq
-/
instance instApplicativeComp : Applicative (Comp F G) :=
  { map := @Comp.map F G _ _, seq := @Comp.seq F G _ _ }

end Comp

variable {F : Type u -> Type v} [Functor F]

/--
Definition of `Liftp` / `Liftp` 的定义

English:
definition Liftp
  signature: {α : Type u} (p : α -> Prop) (x : F α)
  body: exists u : F (Subtype p), Subtype.val < > u = x

中文:
定义 Liftp
  签名: {α : 类型u} (p : α -> 命题) (x : F α)
  定义体: exists u : F (Subtype p), Subtype.val < > u = x

Depends on / 依赖: Subtype, Subtype.val
-/
def Liftp {α : Type u} (p : α -> Prop) (x : F α) : Prop :=
exists u : F (Subtype p), Subtype.val < > u = x

/--
Definition of `Liftr` / `Liftr` 的定义

English:
definition Liftr
  signature: {α : Type u} (r : α -> α -> Prop) (x y : F α)
  body: exists u : F { p : α × α // r p.fst p.snd },
(fun t : { p : α × α // r p.fst p.snd } => t.val.fst) < > u = x ∧
(fun t : { p : α × α // r p.fst p.snd } => t.val.snd) < > u = y

中文:
定义 Liftr
  签名: {α : 类型u} (r : α -> α -> 命题) (x y : F α)
  定义体: exists u : F { p : α × α // r p.fst p.snd },
(fun t : { p : α × α // r p.fst p.snd } => t.val.fst) < > u = x ∧
(fun t : { p : α × α // r p.fst p.snd } => t.val.snd) < > u = y

Depends on / 依赖: p.fst, p.snd, t.val.fst, t.val.snd
-/
def Liftr {α : Type u} (r : α -> α -> Prop) (x y : F α) : Prop :=
  exists u : F { p : α × α // r p.fst p.snd },
(fun t : { p : α × α // r p.fst p.snd } => t.val.fst) < > u = x ∧
(fun t : { p : α × α // r p.fst p.snd } => t.val.snd) < > u = y

/--
Definition of `supp` / `supp` 的定义

English:
definition supp
  signature: {α : Type u} (x : F α)
  body: { y : α | forall ⦃p⦄, Liftp p x -> p y }

中文:
定义 supp
  签名: {α : 类型u} (x : F α)
  定义体: { y : α | forall ⦃p⦄, Liftp p x -> p y }
-/
def supp {α : Type u} (x : F α) : Set α :=
  { y : α | forall ⦃p⦄, Liftp p x -> p y }

/--
theorem `of_mem_supp` / 定理 `of_mem_supp`

English:
theorem of_mem_supp
  given: {α : Type u} {x : F α} {p : α -> Prop} (h : Liftp p x)
  statement: forall y in supp x, p y
  proof: fun _ hy => hy h

中文:
定理 of_mem_supp
  条件: {α : 类型u} {x : F α} {p : α -> 命题} (h : Liftp p x)
  结论: 对任意 y in supp x, p y
  证明: fun _ hy => hy h
-/
theorem of_mem_supp {α : Type u} {x : F α} {p : α -> Prop} (h : Liftp p x) : forall y in supp x, p y :=
  fun _ hy => hy h

/--
Definition of `mapConstRev` / `mapConstRev` 的定义

English:
abbreviation mapConstRev
  signature: {f : Type u -> Type v} [Functor f] {α β : Type u}
  body: fun a b => Functor.mapConst b a

中文:
缩写 mapConstRev
  签名: {f : 类型u -> 类型v} [Functor f] {α β : 类型u}
  定义体: fun a b => Functor.mapConst b a

Depends on / 依赖: Functor, Functor.mapConst, mapConst
-/
abbrev mapConstRev {f : Type u -> Type v} [Functor f] {α β : Type u} :
    f β -> α -> f α :=
  fun a b => Functor.mapConst b a
/-- If `f` is a functor, if `fb : f β` and `a : α`, then `mapConstRev fb a` is the result of
  applying `f.map` to the constant function `β → α` sending everything to `a`, and then
  evaluating at `fb`. In other words it's `const a <$> fb`. -/
infix:100 " > " => Functor.mapConstRev

end Functor
