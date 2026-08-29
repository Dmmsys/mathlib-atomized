/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Control.Combinators
public import Mathlib.Tactic.CasesM
public import Mathlib.Tactic.Attr.Core

import Mathlib.Tactic.Attr.Register

/-!
# Basic control operations

Extends the theory on functors, applicatives and monads.
-/

@[expose] public section

universe u v w

variable {α β γ : Type u}

section Functor

attribute [functor_norm] Functor.map_map

end Functor

section Applicative

variable {F : Type u -> Type v} [Applicative F]

/--
Definition of `zipWithM` / `zipWithM` 的定义

English:
definition zipWithM
  signature: {α₁ α₂ φ : Type u} (f : α₁ -> α₂ -> F φ)

中文:
定义 zipWithM
  签名: {α₁ α₂ φ : 类型u} (f : α₁ -> α₂ -> F φ)
-/
def zipWithM {α₁ α₂ φ : Type u} (f : α₁ -> α₂ -> F φ) : forall (_ : List α₁) (_ : List α₂), F (List φ)
| x :: xs, y :: ys => (· :: ·) < > f x y <*> zipWithM f xs ys
  | _, _ => pure []

/--
Definition of `zipWithM'` / `zipWithM'` 的定义

English:
definition zipWithM'
  signature: (f : α -> β -> F γ)

中文:
定义 zipWithM'
  签名: (f : α -> β -> F γ)
-/
def zipWithM' (f : α -> β -> F γ) : List α -> List β -> F PUnit
  | x :: xs, y :: ys => f x y *> zipWithM' f xs ys
  | [], _ => pure PUnit.unit
  | _, [] => pure PUnit.unit

variable [LawfulApplicative F]

@[simp]
/--
theorem `pure_id'_seq` / 定理 `pure_id'_seq`

English:
theorem pure_id'_seq
  given: (x : F α)
  statement: (pure fun x => x) <*> x = x
  proof: pure_id_seq x

@[functor_norm]

中文:
定理 pure_id'_seq
  条件: (x : F α)
  结论: (pure fun x => x) <*> x = x
  证明: pure_id_seq x

@[functor_norm]

Depends on / 依赖: pure_id_seq
-/
theorem pure_id'_seq (x : F α) : (pure fun x => x) <*> x = x :=
  pure_id_seq x

@[functor_norm]
/--
theorem `seq_map_assoc` / 定理 `seq_map_assoc`

English:
theorem seq_map_assoc
  given: (x : F (α -> β)) (f : γ -> α) (y : F γ)
  proof: by
  simp only [← pure_seq]
  simp only [seq_assoc, seq_pure, ← comp_map]
  simp [pure_seq]
  rfl

@[functor_norm]

中文:
定理 seq_map_assoc
  条件: (x : F (α -> β)) (f : γ -> α) (y : F γ)
  证明: by
  simp only [← pure_seq]
  simp only [seq_assoc, seq_pure, ← comp_map]
  simp [pure_seq]
  rfl

@[functor_norm]

Depends on / 依赖: comp_map, pure_seq, seq_assoc, seq_pure
-/
theorem seq_map_assoc (x : F (α -> β)) (f : γ -> α) (y : F γ) :
x <*> f < > y = (· ∘ f) < > x <*> y := by
  simp only [← pure_seq]
  simp only [seq_assoc, seq_pure, ← comp_map]
  simp [pure_seq]
  rfl

@[functor_norm]
/--
theorem `map_seq` / 定理 `map_seq`

English:
theorem map_seq
  given: (f : β -> γ) (x : F (α -> β)) (y : F α)
  proof: by
  simp only [← pure_seq]; simp [seq_assoc]

中文:
定理 map_seq
  条件: (f : β -> γ) (x : F (α -> β)) (y : F α)
  证明: by
  simp only [← pure_seq]; simp [seq_assoc]

Depends on / 依赖: pure_seq, seq_assoc
-/
theorem map_seq (f : β -> γ) (x : F (α -> β)) (y : F α) :
f < > (x <*> y) = (f ∘ ·) < > x <*> y := by
  simp only [← pure_seq]; simp [seq_assoc]

end Applicative

section Monad

variable {m : Type u -> Type v} [Monad m] [LawfulMonad m]

/--
theorem `seq_bind_eq` / 定理 `seq_bind_eq`

English:
theorem seq_bind_eq
  given: (x : m α) {g : β -> m γ} {f : α -> β}
  proof: show bind (f <$> x) g = bind x (g ∘ f) by
    simp [Function.comp_def]

中文:
定理 seq_bind_eq
  条件: (x : m α) {g : β -> m γ} {f : α -> β}
  证明: show bind (f <$> x) g = bind x (g ∘ f) by
    simp [Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, comp_def
-/
theorem seq_bind_eq (x : m α) {g : β -> m γ} {f : α -> β} :
f < > x >>= g = x >>= g ∘ f :=
  show bind (f <$> x) g = bind x (g ∘ f) by
    simp [Function.comp_def]
-- order of implicits and `Seq.seq` has a lazily evaluated second argument using `Unit`

@[functor_norm]
/--
theorem `fish_pure` / 定理 `fish_pure`

English:
theorem fish_pure
  given: {α β} (f : α -> m β)
  statement: f >=> pure = f
  proof: by
  simp +unfoldPartialApp only [(· >=> ·), functor_norm]

@[functor_norm]

中文:
定理 fish_pure
  条件: {α β} (f : α -> m β)
  结论: f >=> pure = f
  证明: by
  simp +unfoldPartialApp only [(· >=> ·), functor_norm]

@[functor_norm]

Depends on / 依赖: functor_norm, unfoldPartialApp
-/
theorem fish_pure {α β} (f : α -> m β) : f >=> pure = f := by
  simp +unfoldPartialApp only [(· >=> ·), functor_norm]

@[functor_norm]
/--
theorem `fish_pipe` / 定理 `fish_pipe`

English:
theorem fish_pipe
  given: {α β} (f : α -> m β)
  statement: pure >=> f = f
  proof: by
  simp +unfoldPartialApp only [(· >=> ·), functor_norm]

中文:
定理 fish_pipe
  条件: {α β} (f : α -> m β)
  结论: pure >=> f = f
  证明: by
  simp +unfoldPartialApp only [(· >=> ·), functor_norm]

Depends on / 依赖: functor_norm, unfoldPartialApp
-/
theorem fish_pipe {α β} (f : α -> m β) : pure >=> f = f := by
  simp +unfoldPartialApp only [(· >=> ·), functor_norm]

-- note: in Lean 3 `>=>` is left-associative, but in Lean 4 it is right-associative.
@[functor_norm]
/--
theorem `fish_assoc` / 定理 `fish_assoc`

English:
theorem fish_assoc
  given: {α β γ φ} (f : α -> m β) (g : β -> m γ) (h : γ -> m φ)
  proof: by
  simp +unfoldPartialApp only [(· >=> ·), functor_norm]

中文:
定理 fish_assoc
  条件: {α β γ φ} (f : α -> m β) (g : β -> m γ) (h : γ -> m φ)
  证明: by
  simp +unfoldPartialApp only [(· >=> ·), functor_norm]

Depends on / 依赖: functor_norm, unfoldPartialApp
-/
theorem fish_assoc {α β γ φ} (f : α -> m β) (g : β -> m γ) (h : γ -> m φ) :
    (f >=> g) >=> h = f >=> g >=> h := by
  simp +unfoldPartialApp only [(· >=> ·), functor_norm]

variable {β' γ' : Type v}
variable {m' : Type v -> Type w} [Monad m']

/--
Definition of `List.mapAccumRM` / `List.mapAccumRM` 的定义

English:
definition List.mapAccumRM
  signature: (f : α -> β' -> m' (β' × γ'))

中文:
定义 列表.mapAccumRM
  签名: (f : α -> β' -> m' (β' × γ'))
-/
def List.mapAccumRM (f : α -> β' -> m' (β' × γ')) : β' -> List α -> m' (β' × List γ')
  | a, [] => pure (a, [])
  | a, x :: xs => do
    let (a', ys) ← List.mapAccumRM f a xs
    let (a'', y) ← f x a'
    pure (a'', y :: ys)

/--
Definition of `List.mapAccumLM` / `List.mapAccumLM` 的定义

English:
definition List.mapAccumLM
  signature: (f : β' -> α -> m' (β' × γ'))

中文:
定义 列表.mapAccumLM
  签名: (f : β' -> α -> m' (β' × γ'))
-/
def List.mapAccumLM (f : β' -> α -> m' (β' × γ')) : β' -> List α -> m' (β' × List γ')
  | a, [] => pure (a, [])
  | a, x :: xs => do
    let (a', y) ← f a x
    let (a'', ys) ← List.mapAccumLM f a' xs
    pure (a'', y :: ys)

end Monad

section

variable {m : Type u -> Type u} [Monad m] [LawfulMonad m]

/--
theorem `joinM_map_map` / 定理 `joinM_map_map`

English:
theorem joinM_map_map
  given: {α β : Type u} (f : α -> β) (a : m (m α))
  proof: by
  simp only [joinM, id, ← bind_pure_comp, bind_assoc, pure_bind]

中文:
定理 joinM_map_map
  条件: {α β : 类型u} (f : α -> β) (a : m (m α))
  证明: by
  simp only [joinM, id, ← bind_pure_comp, bind_assoc, pure_bind]

Depends on / 依赖: bind_assoc, bind_pure_comp, pure_bind
-/
theorem joinM_map_map {α β : Type u} (f : α -> β) (a : m (m α)) :
joinM (Functor.map f <$> a) = f < > joinM a := by
  simp only [joinM, id, ← bind_pure_comp, bind_assoc, pure_bind]

/--
theorem `joinM_map_joinM` / 定理 `joinM_map_joinM`

English:
theorem joinM_map_joinM
  given: {α : Type u} (a : m (m (m α)))
  statement: joinM (joinM <$> a) = joinM (joinM a)
  proof: by
  simp only [joinM, id, ← bind_pure_comp, bind_assoc, pure_bind]

@[simp]

中文:
定理 joinM_map_joinM
  条件: {α : 类型u} (a : m (m (m α)))
  结论: joinM (joinM <$> a) = joinM (joinM a)
  证明: by
  simp only [joinM, id, ← bind_pure_comp, bind_assoc, pure_bind]

@[simp]

Depends on / 依赖: bind_assoc, bind_pure_comp, pure_bind
-/
theorem joinM_map_joinM {α : Type u} (a : m (m (m α))) : joinM (joinM <$> a) = joinM (joinM a) := by
  simp only [joinM, id, ← bind_pure_comp, bind_assoc, pure_bind]

@[simp]
/--
theorem `joinM_map_pure` / 定理 `joinM_map_pure`

English:
theorem joinM_map_pure
  given: {α : Type u} (a : m α)
  statement: joinM (pure <$> a) = a
  proof: by
  simp only [joinM, id, ← bind_pure_comp, bind_assoc, pure_bind, bind_pure]

@[simp]

中文:
定理 joinM_map_pure
  条件: {α : 类型u} (a : m α)
  结论: joinM (pure <$> a) = a
  证明: by
  simp only [joinM, id, ← bind_pure_comp, bind_assoc, pure_bind, bind_pure]

@[simp]

Depends on / 依赖: bind_assoc, bind_pure, bind_pure_comp, pure_bind
-/
theorem joinM_map_pure {α : Type u} (a : m α) : joinM (pure <$> a) = a := by
  simp only [joinM, id, ← bind_pure_comp, bind_assoc, pure_bind, bind_pure]

@[simp]
/--
theorem `joinM_pure` / 定理 `joinM_pure`

English:
theorem joinM_pure
  given: {α : Type u} (a : m α)
  statement: joinM (pure a) = a
  proof: LawfulMonad.pure_bind a id

中文:
定理 joinM_pure
  条件: {α : 类型u} (a : m α)
  结论: joinM (pure a) = a
  证明: LawfulMonad.pure_bind a id

Depends on / 依赖: LawfulMonad, LawfulMonad.pure_bind, pure_bind
-/
theorem joinM_pure {α : Type u} (a : m α) : joinM (pure a) = a :=
  LawfulMonad.pure_bind a id

end

section Alternative

variable {F : Type -> Type v} [Alternative F]

-- [todo] add notation for `Functor.mapConst` and port `Functor.mapConstRev`
/--
Definition of `succeeds` / `succeeds` 的定义

English:
definition succeeds
  signature: {α} (x : F α)
  body: Functor.mapConst true x > pure false

中文:
定义 succeeds
  签名: {α} (x : F α)
  定义体: Functor.mapConst true x > pure false

Depends on / 依赖: Functor, Functor.mapConst, mapConst
-/
def succeeds {α} (x : F α) : F Bool :=
Functor.mapConst true x > pure false

/--
Definition of `tryM` / `tryM` 的定义

English:
definition tryM
  signature: {α} (x : F α)
  body: Functor.mapConst () x > pure ()

中文:
定义 tryM
  签名: {α} (x : F α)
  定义体: Functor.mapConst () x > pure ()

Depends on / 依赖: Functor, Functor.mapConst, mapConst
-/
def tryM {α} (x : F α) : F Unit :=
Functor.mapConst () x > pure ()

/--
Definition of `try?` / `try?` 的定义

English:
definition try?
  signature: {α} (x : F α)
  body: some < > x > pure none

@[simp]

中文:
定义 try?
  签名: {α} (x : F α)
  定义体: some < > x > pure none

@[simp]
-/
def try? {α} (x : F α) : F (Option α) :=
some < > x > pure none

@[simp]
/--
theorem `guard_true` / 定理 `guard_true`

English:
theorem guard_true
  given: {h : Decidable True}
  statement: @guard F _ True h = pure ()
  proof: by simp [guard]

@[simp]

中文:
定理 guard_true
  条件: {h : 可判定 真}
  结论: @guard F _ 真 h = pure ()
  证明: by simp [guard]

@[simp]
-/
theorem guard_true {h : Decidable True} : @guard F _ True h = pure () := by simp [guard]

@[simp]
/--
theorem `guard_false` / 定理 `guard_false`

English:
theorem guard_false
  given: {h : Decidable False}
  statement: @guard F _ False h = failure
  proof: by
  simp [guard]

中文:
定理 guard_false
  条件: {h : 可判定 假}
  结论: @guard F _ 假 h = failure
  证明: by
  simp [guard]
-/
theorem guard_false {h : Decidable False} : @guard F _ False h = failure := by
  simp [guard]

end Alternative

namespace Sum

variable {e : Type v}

/--
Definition of `bind` / `bind` 的定义

English:
definition bind
  signature: {α β}

中文:
定义 bind
  签名: {α β}
-/
protected def bind {α β} : e oplus α -> (α -> e oplus β) -> e oplus β
  | inl x, _ => inl x
  | inr x, f => f x
-- incorrectly marked as a bad translation by mathport, so we do not mark with `ₓ`.

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Monad (Sum.{v, u} e)
  body: @Sum.inr e
  bind := @Sum.bind e

中文:
实例 :
  签名: 单子 (和.{v, u} e)
  定义体: @Sum.inr e
  bind := @Sum.bind e

Depends on / 依赖: Sum.inr
-/
instance : Monad (Sum.{v, u} e) where
  pure := @Sum.inr e
  bind := @Sum.bind e

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulFunctor (Sum.{v, u} e)
  body: by
  constructor <;> intros <;> (try casesm Sum _ _) <;> rfl

中文:
实例 :
  签名: Lawful函子 (和.{v, u} e)
  定义体: by
  constructor <;> intros <;> (try casesm Sum _ _) <;> rfl

Depends on / 依赖: Int.log, casesm, intros
-/
instance : LawfulFunctor (Sum.{v, u} e) := by
  constructor <;> intros <;> (try casesm Sum _ _) <;> rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulMonad (Sum.{v, u} e)
  body: by
    intros
    casesm Sum _ _ <;> casesm Sum _ _ <;> rfl
  seqLeft_eq := by
    intros
    casesm Sum _ _ <;> rfl
  pure_seq := by
    intros
    rfl
  bind_assoc := by
    intros
    casesm Sum _ _ <;> rfl
  pure_bind := by
    intros
    rfl
  bind_pure_comp := by
    intros
    casesm Sum _ _ <;> rfl
  bind_map := by
    intros
    casesm Sum _ _ <;> rfl

中文:
实例 :
  签名: 合法单子 (和.{v, u} e)
  定义体: by
    intros
    casesm Sum _ _ <;> casesm Sum _ _ <;> rfl
  seqLeft_eq := by
    intros
    casesm Sum _ _ <;> rfl
  pure_seq := by
    intros
    rfl
  bind_assoc := by
    intros
    casesm Sum _ _ <;> rfl
  pure_bind := by
    intros
    rfl
  bind_pure_comp := by
    intros
    casesm Sum _ _ <;> rfl
  bind_map := by
    intros
    casesm Sum _ _ <;> rfl

Depends on / 依赖: bind_assoc, bind_map, bind_pure_comp, casesm, intros, pure_bind, pure_seq, seqLeft_eq
-/
instance : LawfulMonad (Sum.{v, u} e) where
  seqRight_eq := by
    intros
    casesm Sum _ _ <;> casesm Sum _ _ <;> rfl
  seqLeft_eq := by
    intros
    casesm Sum _ _ <;> rfl
  pure_seq := by
    intros
    rfl
  bind_assoc := by
    intros
    casesm Sum _ _ <;> rfl
  pure_bind := by
    intros
    rfl
  bind_pure_comp := by
    intros
    casesm Sum _ _ <;> rfl
  bind_map := by
    intros
    casesm Sum _ _ <;> rfl

end Sum

/--
Definition of `CommApplicative` / `CommApplicative` 的定义

English:
class CommApplicative
  parameters: (m : Type u -> Type v) [Applicative m]
  extends: LawfulApplicative m
  axioms and operations (1):
    - commutative_prod : forall {α β} (a : m α) (b : m β),

中文:
类 交换适用
  参数: (m : 类型u -> 类型v) [适用 m]
  继承: 合法适用 m
  公理与运算 (1 个):
    - commutative_prod : 对任意 {α β} (a : m α) (b : m β),
-/
class CommApplicative (m : Type u -> Type v) [Applicative m] : Prop extends LawfulApplicative m where
  /-- Computations performed first on `a : α` and then on `b : β` are equal to those performed in
  the reverse order. -/
  commutative_prod : forall {α β} (a : m α) (b : m β),
Prod.mk < > a <*> b = (fun (b : β) a => (a, b)) < > b <*> a

open Functor

/--
theorem `CommApplicative.commutative_map` / 定理 `CommApplicative.commutative_map`

English:
theorem CommApplicative.commutative_map
  statement: {m : Type u -> Type v} [h : Applicative m]
  proof: calc
f < > a <*> b = (fun p : α × β => f p.1 p.2) < > (Prod.mk <$> a <*> b) := by
      simp only [map_seq, map_map, Function.comp_def]
_ = (fun b a => f a b) < > b <*> a := by
      rw [@CommApplicative.commutative_prod m h]
      simp [map_seq, map_map]
      rfl

中文:
定理 交换适用.commutative_map
  结论: {m : 类型u -> 类型v} [h : 适用 m]
  证明: calc
f < > a <*> b = (fun p : α × β => f p.1 p.2) < > (Prod.mk <$> a <*> b) := by
      simp only [map_seq, map_map, Function.comp_def]
_ = (fun b a => f a b) < > b <*> a := by
      rw [@CommApplicative.commutative_prod m h]
      simp [map_seq, map_map]
      rfl

Depends on / 依赖: CommApplicative, CommApplicative.commutative_prod, Function, Function.comp_def, Prod.mk, commutative_prod, comp_def, map_map, map_seq
-/
theorem CommApplicative.commutative_map {m : Type u -> Type v} [h : Applicative m]
    [CommApplicative m] {α β γ} (a : m α) (b : m β) {f : α -> β -> γ} :
f < > a <*> b = flip f < > b <*> a :=
  calc
f < > a <*> b = (fun p : α × β => f p.1 p.2) < > (Prod.mk <$> a <*> b) := by
      simp only [map_seq, map_map, Function.comp_def]
_ = (fun b a => f a b) < > b <*> a := by
      rw [@CommApplicative.commutative_prod m h]
      simp [map_seq, map_map]
      rfl
