/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

public import Mathlib.Data.Nat.Notation

/-!
# Definition of `Stream'` and functions on streams

A stream `Stream' α` is an infinite sequence of elements of `α`. One can also think about it as an
infinite list. In this file we define `Stream'` and some functions that take and/or return streams.
Note that we already have `Stream` to represent a similar object, hence the awkward naming.
-/

@[expose] public section

universe u v w
variable {α : Type u} {β : Type v} {δ : Type w}

/--
Definition of `Stream'` / `Stream'` 的定义

English:
definition Stream'
  signature: (α : Type u)
  body: Nat -> α

中文:
定义 Stream'
  签名: (α : 类型u)
  定义体: Nat -> α
-/
def Stream' (α : Type u) := Nat -> α

namespace Stream'

/--
Definition of `cons` / `cons` 的定义

English:
definition cons
  signature: (a : α) (s : Stream' α)

中文:
定义 cons
  签名: (a : α) (s : Stream' α)
-/
def cons (a : α) (s : Stream' α) : Stream' α
  | 0 => a
  | n + 1 => s n

@[inherit_doc] scoped infixr:67 " :: " => cons

/--
Definition of `get` / `get` 的定义

English:
definition get
  signature: (s : Stream' α) (n : Nat)
  body: s n

中文:
定义 get
  签名: (s : Stream' α) (n : 自然数)
  定义体: s n
-/
def get (s : Stream' α) (n : Nat) : α := s n

/--
Definition of `head` / `head` 的定义

English:
abbreviation head
  signature: (s : Stream' α)
  body: s.get 0

中文:
缩写 head
  签名: (s : Stream' α)
  定义体: s.get 0

Depends on / 依赖: s.get
-/
abbrev head (s : Stream' α) : α := s.get 0

/--
Definition of `tail` / `tail` 的定义

English:
definition tail
  signature: (s : Stream' α)
  body: fun i => s.get (i + 1)

中文:
定义 tail
  签名: (s : Stream' α)
  定义体: fun i => s.get (i + 1)

Depends on / 依赖: s.get
-/
def tail (s : Stream' α) : Stream' α := fun i => s.get (i + 1)

/--
Definition of `drop` / `drop` 的定义

English:
definition drop
  signature: (n : Nat) (s : Stream' α)
  body: fun i => s.get (i + n)

中文:
定义 drop
  签名: (n : 自然数) (s : Stream' α)
  定义体: fun i => s.get (i + n)

Depends on / 依赖: s.get
-/
def drop (n : Nat) (s : Stream' α) : Stream' α := fun i => s.get (i + n)

/--
Definition of `All` / `All` 的定义

English:
definition All
  signature: (p : α -> Prop) (s : Stream' α)
  body: forall n, p (get s n)

中文:
定义 All
  签名: (p : α -> 命题) (s : Stream' α)
  定义体: forall n, p (get s n)
-/
def All (p : α -> Prop) (s : Stream' α) := forall n, p (get s n)

/--
Definition of `Any` / `Any` 的定义

English:
definition Any
  signature: (p : α -> Prop) (s : Stream' α)
  body: exists n, p (get s n)

中文:
定义 Any
  签名: (p : α -> 命题) (s : Stream' α)
  定义体: exists n, p (get s n)
-/
def Any (p : α -> Prop) (s : Stream' α) := exists n, p (get s n)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Membership α (Stream' α)
  body: ⟨fun s a => Any (fun b => a = b) s⟩

中文:
实例 :
  签名: Membership α (Stream' α)
  定义体: ⟨fun s a => Any (fun b => a = b) s⟩
-/
instance : Membership α (Stream' α) :=
  ⟨fun s a => Any (fun b => a = b) s⟩

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : α -> β) (s : Stream' α)
  body: fun n => f (get s n)

中文:
定义 map
  签名: (f : α -> β) (s : Stream' α)
  定义体: fun n => f (get s n)
-/
def map (f : α -> β) (s : Stream' α) : Stream' β := fun n => f (get s n)

/--
Definition of `zip` / `zip` 的定义

English:
definition zip
  signature: (f : α -> β -> δ) (s₁ : Stream' α) (s₂ : Stream' β)
  body: fun n => f (get s₁ n) (get s₂ n)

中文:
定义 zip
  签名: (f : α -> β -> δ) (s₁ : Stream' α) (s₂ : Stream' β)
  定义体: fun n => f (get s₁ n) (get s₂ n)
-/
def zip (f : α -> β -> δ) (s₁ : Stream' α) (s₂ : Stream' β) : Stream' δ :=
  fun n => f (get s₁ n) (get s₂ n)

/--
Definition of `enum` / `enum` 的定义

English:
definition enum
  signature: (s : Stream' α)
  body: fun n => (n, s.get n)

中文:
定义 enum
  签名: (s : Stream' α)
  定义体: fun n => (n, s.get n)

Depends on / 依赖: s.get
-/
def enum (s : Stream' α) : Stream' (Nat × α) := fun n => (n, s.get n)

/--
Definition of `const` / `const` 的定义

English:
definition const
  signature: (a : α)
  body: fun _ => a

中文:
定义 const
  签名: (a : α)
  定义体: fun _ => a
-/
def const (a : α) : Stream' α := fun _ => a

/--
Definition of `iterate` / `iterate` 的定义

English:
definition iterate
  signature: (f : α -> α) (a : α)

中文:
定义 iterate
  签名: (f : α -> α) (a : α)
-/
def iterate (f : α -> α) (a : α) : Stream' α
  | 0 => a
  | n + 1 => f (iterate f a n)

/--
Definition of `corec` / `corec` 的定义

English:
definition corec
  signature: (f : α -> β) (g : α -> α)
  body: fun a => map f (iterate g a)

中文:
定义 corec
  签名: (f : α -> β) (g : α -> α)
  定义体: fun a => map f (iterate g a)

Depends on / 依赖: iterate
-/
def corec (f : α -> β) (g : α -> α) : α -> Stream' β := fun a => map f (iterate g a)

/--
Definition of `corecOn` / `corecOn` 的定义

English:
definition corecOn
  signature: (a : α) (f : α -> β) (g : α -> α)
  body: corec f g a

中文:
定义 corecOn
  签名: (a : α) (f : α -> β) (g : α -> α)
  定义体: corec f g a
-/
def corecOn (a : α) (f : α -> β) (g : α -> α) : Stream' β :=
  corec f g a

/--
Definition of `corec'` / `corec'` 的定义

English:
definition corec'
  signature: (f : α -> β × α)
  body: corec (Prod.fst ∘ f) (Prod.snd ∘ f)

中文:
定义 corec'
  签名: (f : α -> β × α)
  定义体: corec (Prod.fst ∘ f) (Prod.snd ∘ f)

Depends on / 依赖: CommGroup, CommGroup.center_eq_top, CommGroup.isNilpotent, IsNilpotent, Prod.fst, Prod.snd, center_eq_top, isNilpotent, upperCentralSeries_one
-/
def corec' (f : α -> β × α) : α -> Stream' β :=
  corec (Prod.fst ∘ f) (Prod.snd ∘ f)

/--
Definition of `corecState` / `corecState` 的定义

English:
definition corecState
  signature: {σ α} (cmd : StateM σ α) (s : σ)
  body: corec Prod.fst (cmd.run ∘ Prod.snd) (cmd.run s)

中文:
定义 corecState
  签名: {σ α} (cmd : StateM σ α) (s : σ)
  定义体: corec Prod.fst (cmd.run ∘ Prod.snd) (cmd.run s)

Depends on / 依赖: Prod.fst, Prod.snd, cmd.run
-/
def corecState {σ α} (cmd : StateM σ α) (s : σ) : Stream' α :=
  corec Prod.fst (cmd.run ∘ Prod.snd) (cmd.run s)

-- corec is also known as unfolds
/--
Definition of `unfolds` / `unfolds` 的定义

English:
abbreviation unfolds
  signature: (g : α -> β) (f : α -> α) (a : α)
  body: corec g f a

中文:
缩写 unfolds
  签名: (g : α -> β) (f : α -> α) (a : α)
  定义体: corec g f a
-/
abbrev unfolds (g : α -> β) (f : α -> α) (a : α) : Stream' β :=
  corec g f a

/--
Definition of `interleave` / `interleave` 的定义

English:
definition interleave
  signature: (s₁ s₂ : Stream' α)
  body: corecOn (s₁, s₂) (fun ⟨s₁, _⟩ => head s₁) fun ⟨s₁, s₂⟩ => (s₂, tail s₁)

@[inherit_doc] infixl:65 " ⋈ " => interleave

中文:
定义 interleave
  签名: (s₁ s₂ : Stream' α)
  定义体: corecOn (s₁, s₂) (fun ⟨s₁, _⟩ => head s₁) fun ⟨s₁, s₂⟩ => (s₂, tail s₁)

@[inherit_doc] infixl:65 " ⋈ " => interleave

Depends on / 依赖: corecOn
-/
def interleave (s₁ s₂ : Stream' α) : Stream' α :=
  corecOn (s₁, s₂) (fun ⟨s₁, _⟩ => head s₁) fun ⟨s₁, s₂⟩ => (s₂, tail s₁)

@[inherit_doc] infixl:65 " ⋈ " => interleave

/--
Definition of `even` / `even` 的定义

English:
definition even
  signature: (s : Stream' α)
  body: corec head (fun s => tail (tail s)) s

中文:
定义 even
  签名: (s : Stream' α)
  定义体: corec head (fun s => tail (tail s)) s
-/
def even (s : Stream' α) : Stream' α :=
  corec head (fun s => tail (tail s)) s

/--
Definition of `odd` / `odd` 的定义

English:
definition odd
  signature: (s : Stream' α)
  body: even (tail s)

中文:
定义 odd
  签名: (s : Stream' α)
  定义体: even (tail s)
-/
def odd (s : Stream' α) : Stream' α :=
  even (tail s)

/--
Definition of `appendStream'` / `appendStream'` 的定义

English:
definition appendStream'
  signature: : List α -> Stream' α -> Stream' α

中文:
定义 appendStream'
  签名: : List α -> Stream' α -> Stream' α
-/
def appendStream' : List α -> Stream' α -> Stream' α
  | [], s => s
  | List.cons a l, s => a::appendStream' l s

@[inherit_doc] infixl:65 " ++ₛ " => appendStream'

/--
Definition of `take` / `take` 的定义

English:
definition take
  signature: : Nat -> Stream' α -> List α

中文:
定义 take
  签名: : 自然数 -> Stream' α -> List α
-/
def take : Nat -> Stream' α -> List α
  | 0, _ => []
  | n + 1, s => List.cons (head s) (take n (tail s))

/--
Definition of `cycleF` / `cycleF` 的定义

English:
definition cycleF
  signature: : α × List α × α × List α -> α

中文:
定义 cycleF
  签名: : α × List α × α × List α -> α
-/
protected def cycleF : α × List α × α × List α -> α
  | (v, _, _, _) => v

/--
Definition of `cycleG` / `cycleG` 的定义

English:
definition cycleG
  signature: : α × List α × α × List α -> α × List α × α × List α

中文:
定义 cycleG
  签名: : α × List α × α × List α -> α × List α × α × List α
-/
protected def cycleG : α × List α × α × List α -> α × List α × α × List α
  | (_, [], v₀, l₀) => (v₀, l₀, v₀, l₀)
  | (_, List.cons v₂ l₂, v₀, l₀) => (v₂, l₂, v₀, l₀)

/--
Definition of `cycle` / `cycle` 的定义

English:
definition cycle
  signature: : forall l : List α, l != [] -> Stream' α

中文:
定义 cycle
  签名: : 对任意 l : List α, l != [] -> Stream' α
-/
def cycle : forall l : List α, l != [] -> Stream' α
  | [], h => absurd rfl h
  | List.cons a l, _ => corec Stream'.cycleF Stream'.cycleG (a, l, a, l)

/--
Definition of `tails` / `tails` 的定义

English:
definition tails
  signature: (s : Stream' α)
  body: corec id tail (tail s)

中文:
定义 tails
  签名: (s : Stream' α)
  定义体: corec id tail (tail s)
-/
def tails (s : Stream' α) : Stream' (Stream' α) :=
  corec id tail (tail s)

/--
Definition of `initsCore` / `initsCore` 的定义

English:
definition initsCore
  signature: (l : List α) (s : Stream' α)
  body: corecOn (l, s) (fun ⟨a, _⟩ => a) fun p =>
    match p with
    | (l', s') => (l' ++ [head s'], tail s')

中文:
定义 initsCore
  签名: (l : List α) (s : Stream' α)
  定义体: corecOn (l, s) (fun ⟨a, _⟩ => a) fun p =>
    match p with
    | (l', s') => (l' ++ [head s'], tail s')

Depends on / 依赖: corecOn
-/
def initsCore (l : List α) (s : Stream' α) : Stream' (List α) :=
  corecOn (l, s) (fun ⟨a, _⟩ => a) fun p =>
    match p with
    | (l', s') => (l' ++ [head s'], tail s')

/--
Definition of `inits` / `inits` 的定义

English:
definition inits
  signature: (s : Stream' α)
  body: initsCore [head s] (tail s)

中文:
定义 inits
  签名: (s : Stream' α)
  定义体: initsCore [head s] (tail s)

Depends on / 依赖: initsCore
-/
def inits (s : Stream' α) : Stream' (List α) :=
  initsCore [head s] (tail s)

/--
Definition of `pure` / `pure` 的定义

English:
definition pure
  signature: (a : α)
  body: const a

中文:
定义 pure
  签名: (a : α)
  定义体: const a
-/
def pure (a : α) : Stream' α :=
  const a

/--
Definition of `apply` / `apply` 的定义

English:
definition apply
  signature: (f : Stream' (α -> β)) (s : Stream' α)
  body: fun n => (get f n) (get s n)

@[inherit_doc] infixl:75 " ⊛ " => apply -- input as `\circledast`

中文:
定义 apply
  签名: (f : Stream' (α -> β)) (s : Stream' α)
  定义体: fun n => (get f n) (get s n)

@[inherit_doc] infixl:75 " ⊛ " => apply -- input as `\circledast`
-/
def apply (f : Stream' (α -> β)) (s : Stream' α) : Stream' β := fun n => (get f n) (get s n)

@[inherit_doc] infixl:75 " ⊛ " => apply -- input as `\circledast`

/--
Definition of `nats` / `nats` 的定义

English:
definition nats
  signature: : Stream' Nat
  body: fun n => n

中文:
定义 nats
  签名: : Stream' 自然数
  定义体: fun n => n
-/
def nats : Stream' Nat := fun n => n

end Stream'
