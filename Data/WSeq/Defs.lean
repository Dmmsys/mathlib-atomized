/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Batteries.Data.DList.Basic
public import Mathlib.Data.WSeq.Basic

/-!
# Miscellaneous definitions concerning weak sequences

These definitions, as well as those in `Mathlib/Data/WSeq/Productive.lean`, are not needed for the
development of `Mathlib/Data/Seq/Parallel.lean`.
-/

@[expose] public section

universe u v w

namespace Stream'.WSeq

variable {α : Type u} {β : Type v} {γ : Type w}

open Function

/--
Definition of `length` / `length` 的定义

English:
definition length
  signature: (s : WSeq α)
  body: @Computation.corec Nat (Nat × WSeq α)
    (fun ⟨n, s⟩ =>
      match Seq.destruct s with
      | none => Sum.inl n
      | some (none, s') => Sum.inr (n, s')
      | some (some _, s') => Sum.inr (n + 1, s'))
    (0, s)

中文:
定义 length
  签名: (s : WSeq α)
  定义体: @Computation.corec Nat (Nat × WSeq α)
    (fun ⟨n, s⟩ =>
      match Seq.destruct s with
      | none => Sum.inl n
      | some (none, s') => Sum.inr (n, s')
      | some (some _, s') => Sum.inr (n + 1, s'))
    (0, s)

Depends on / 依赖: Computation, Computation.corec, Seq.destruct, Sum.inl, Sum.inr, destruct
-/
def length (s : WSeq α) : Computation Nat :=
  @Computation.corec Nat (Nat × WSeq α)
    (fun ⟨n, s⟩ =>
      match Seq.destruct s with
      | none => Sum.inl n
      | some (none, s') => Sum.inr (n, s')
      | some (some _, s') => Sum.inr (n + 1, s'))
    (0, s)

/--
Definition of `IsFinite` / `IsFinite` 的定义

English:
class IsFinite
  parameters: (s : WSeq α)
  axioms and operations (1):
    - out : (toList s).Terminates

中文:
类 是有限
  参数: (s : WSeq α)
  公理与运算 (1 个):
    - out : (toList s).Terminates
-/
class IsFinite (s : WSeq α) : Prop where
  out : (toList s).Terminates

/--
Instance `toList_terminates` / 实例 `toList_terminates`

English:
instance toList_terminates
  signature: (s : WSeq α) [h : IsFinite s]
  body: h.out

中文:
实例 toList_terminates
  签名: (s : WSeq α) [h : 是有限 s]
  定义体: h.out

Depends on / 依赖: h.out
-/
instance toList_terminates (s : WSeq α) [h : IsFinite s] : (toList s).Terminates :=
  h.out

/--
Definition of `get` / `get` 的定义

English:
definition get
  signature: (s : WSeq α) [IsFinite s]
  body: (toList s).get

中文:
定义 get
  签名: (s : WSeq α) [是有限 s]
  定义体: (toList s).get
-/
def get (s : WSeq α) [IsFinite s] : List α :=
  (toList s).get

/--
Definition of `updateNth` / `updateNth` 的定义

English:
definition updateNth
  signature: (s : WSeq α) (n : Nat) (a : α)
  body: @Seq.corec (Option α) (Nat × WSeq α)
    (fun ⟨n, s⟩ =>
      match Seq.destruct s, n with
      | none, _ => none
      | some (none, s'), n => some (none, n, s')
      | some (some a', s'), 0 => some (some a', 0, s')
      | some (some _, s'), 1 => some (some a, 0, s')
      | some (some a', s'), n + 2 => some (some a', n + 1, s'))
    (n + 1, s)

中文:
定义 updateNth
  签名: (s : WSeq α) (n : 自然数) (a : α)
  定义体: @Seq.corec (Option α) (Nat × WSeq α)
    (fun ⟨n, s⟩ =>
      match Seq.destruct s, n with
      | none, _ => none
      | some (none, s'), n => some (none, n, s')
      | some (some a', s'), 0 => some (some a', 0, s')
      | some (some _, s'), 1 => some (some a, 0, s')
      | some (some a', s'), n + 2 => some (some a', n + 1, s'))
    (n + 1, s)

Depends on / 依赖: Seq.corec, Seq.destruct, destruct
-/
def updateNth (s : WSeq α) (n : Nat) (a : α) : WSeq α :=
  @Seq.corec (Option α) (Nat × WSeq α)
    (fun ⟨n, s⟩ =>
      match Seq.destruct s, n with
      | none, _ => none
      | some (none, s'), n => some (none, n, s')
      | some (some a', s'), 0 => some (some a', 0, s')
      | some (some _, s'), 1 => some (some a, 0, s')
      | some (some a', s'), n + 2 => some (some a', n + 1, s'))
    (n + 1, s)

/--
Definition of `removeNth` / `removeNth` 的定义

English:
definition removeNth
  signature: (s : WSeq α) (n : Nat)
  body: @Seq.corec (Option α) (Nat × WSeq α)
    (fun ⟨n, s⟩ =>
      match Seq.destruct s, n with
      | none, _ => none
      | some (none, s'), n => some (none, n, s')
      | some (some a', s'), 0 => some (some a', 0, s')
      | some (some _, s'), 1 => some (none, 0, s')
      | some (some a', s'), n + 2 => some (some a', n + 1, s'))
    (n + 1, s)

中文:
定义 removeNth
  签名: (s : WSeq α) (n : 自然数)
  定义体: @Seq.corec (Option α) (Nat × WSeq α)
    (fun ⟨n, s⟩ =>
      match Seq.destruct s, n with
      | none, _ => none
      | some (none, s'), n => some (none, n, s')
      | some (some a', s'), 0 => some (some a', 0, s')
      | some (some _, s'), 1 => some (none, 0, s')
      | some (some a', s'), n + 2 => some (some a', n + 1, s'))
    (n + 1, s)

Depends on / 依赖: Seq.corec, Seq.destruct, destruct
-/
def removeNth (s : WSeq α) (n : Nat) : WSeq α :=
  @Seq.corec (Option α) (Nat × WSeq α)
    (fun ⟨n, s⟩ =>
      match Seq.destruct s, n with
      | none, _ => none
      | some (none, s'), n => some (none, n, s')
      | some (some a', s'), 0 => some (some a', 0, s')
      | some (some _, s'), 1 => some (none, 0, s')
      | some (some a', s'), n + 2 => some (some a', n + 1, s'))
    (n + 1, s)

/--
Definition of `filterMap` / `filterMap` 的定义

English:
definition filterMap
  signature: (f : α -> Option β)
  body: Seq.corec fun s =>
    match Seq.destruct s with
    | none => none
    | some (none, s') => some (none, s')
    | some (some a, s') => some (f a, s')

中文:
定义 filterMap
  签名: (f : α -> 选项类型 β)
  定义体: Seq.corec fun s =>
    match Seq.destruct s with
    | none => none
    | some (none, s') => some (none, s')
    | some (some a, s') => some (f a, s')

Depends on / 依赖: Seq.corec, Seq.destruct, destruct
-/
def filterMap (f : α -> Option β) : WSeq α -> WSeq β :=
  Seq.corec fun s =>
    match Seq.destruct s with
    | none => none
    | some (none, s') => some (none, s')
    | some (some a, s') => some (f a, s')

/--
Definition of `filter` / `filter` 的定义

English:
definition filter
  signature: (p : α -> Prop) [DecidablePred p]
  body: filterMap fun a => if p a then some a else none

中文:
定义 filter
  签名: (p : α -> 命题) [DecidablePred p]
  定义体: filterMap fun a => if p a then some a else none

Depends on / 依赖: filterMap
-/
def filter (p : α -> Prop) [DecidablePred p] : WSeq α -> WSeq α :=
  filterMap fun a => if p a then some a else none

-- example of infinite list manipulations
/--
Definition of `find` / `find` 的定义

English:
definition find
  signature: (p : α -> Prop) [DecidablePred p] (s : WSeq α)
  body: head filter p s

中文:
定义 find
  签名: (p : α -> 命题) [DecidablePred p] (s : WSeq α)
  定义体: head filter p s

Depends on / 依赖: filter
-/
def find (p : α -> Prop) [DecidablePred p] (s : WSeq α) : Computation (Option α) :=
head filter p s

/--
Definition of `zipWith` / `zipWith` 的定义

English:
definition zipWith
  signature: (f : α -> β -> γ) (s1 : WSeq α) (s2 : WSeq β)
  body: @Seq.corec (Option γ) (WSeq α × WSeq β)
    (fun ⟨s1, s2⟩ =>
      match Seq.destruct s1, Seq.destruct s2 with
      | some (none, s1'), some (none, s2') => some (none, s1', s2')
      | some (some _, _), some (none, s2') => some (none, s1, s2')
      | some (none, s1'), some (some _, _) => some (none, s1', s2)
      | some (some a1, s1'), some (some a2, s2') => some (some (f a1 a2), s1', s2')
      | _, _ => none)
    (s1, s2)

中文:
定义 zipWith
  签名: (f : α -> β -> γ) (s1 : WSeq α) (s2 : WSeq β)
  定义体: @Seq.corec (Option γ) (WSeq α × WSeq β)
    (fun ⟨s1, s2⟩ =>
      match Seq.destruct s1, Seq.destruct s2 with
      | some (none, s1'), some (none, s2') => some (none, s1', s2')
      | some (some _, _), some (none, s2') => some (none, s1, s2')
      | some (none, s1'), some (some _, _) => some (none, s1', s2)
      | some (some a1, s1'), some (some a2, s2') => some (some (f a1 a2), s1', s2')
      | _, _ => none)
    (s1, s2)

Depends on / 依赖: Seq.corec, Seq.destruct, destruct
-/
def zipWith (f : α -> β -> γ) (s1 : WSeq α) (s2 : WSeq β) : WSeq γ :=
  @Seq.corec (Option γ) (WSeq α × WSeq β)
    (fun ⟨s1, s2⟩ =>
      match Seq.destruct s1, Seq.destruct s2 with
      | some (none, s1'), some (none, s2') => some (none, s1', s2')
      | some (some _, _), some (none, s2') => some (none, s1, s2')
      | some (none, s1'), some (some _, _) => some (none, s1', s2)
      | some (some a1, s1'), some (some a2, s2') => some (some (f a1 a2), s1', s2')
      | _, _ => none)
    (s1, s2)

/--
Definition of `zip` / `zip` 的定义

English:
definition zip
  signature: : WSeq α -> WSeq β -> WSeq (α × β)
  body: zipWith Prod.mk

中文:
定义 zip
  签名: : WSeq α -> WSeq β -> WSeq (α × β)
  定义体: zipWith Prod.mk

Depends on / 依赖: Prod.mk, zipWith
-/
def zip : WSeq α -> WSeq β -> WSeq (α × β) :=
  zipWith Prod.mk

/--
Definition of `findIndexes` / `findIndexes` 的定义

English:
definition findIndexes
  signature: (p : α -> Prop) [DecidablePred p] (s : WSeq α)
  body: (zip s (Stream'.nats : WSeq Nat)).filterMap fun ⟨a, n⟩ => if p a then some n else none

中文:
定义 findIndexes
  签名: (p : α -> 命题) [DecidablePred p] (s : WSeq α)
  定义体: (zip s (Stream'.nats : WSeq Nat)).filterMap fun ⟨a, n⟩ => if p a then some n else none

Depends on / 依赖: Stream, filterMap
-/
def findIndexes (p : α -> Prop) [DecidablePred p] (s : WSeq α) : WSeq Nat :=
  (zip s (Stream'.nats : WSeq Nat)).filterMap fun ⟨a, n⟩ => if p a then some n else none

/--
Definition of `findIndex` / `findIndex` 的定义

English:
definition findIndex
  signature: (p : α -> Prop) [DecidablePred p] (s : WSeq α)
  body: (fun o => Option.getD o 0) < > head (findIndexes p s)

中文:
定义 findIndex
  签名: (p : α -> 命题) [DecidablePred p] (s : WSeq α)
  定义体: (fun o => Option.getD o 0) < > head (findIndexes p s)

Depends on / 依赖: Option.getD, findIndexes
-/
def findIndex (p : α -> Prop) [DecidablePred p] (s : WSeq α) : Computation Nat :=
(fun o => Option.getD o 0) < > head (findIndexes p s)

/--
Definition of `indexOf` / `indexOf` 的定义

English:
definition indexOf
  signature: [DecidableEq α] (a : α)
  body: findIndex (Eq a)

中文:
定义 indexOf
  签名: [DecidableEq α] (a : α)
  定义体: findIndex (Eq a)

Depends on / 依赖: findIndex
-/
def indexOf [DecidableEq α] (a : α) : WSeq α -> Computation Nat :=
  findIndex (Eq a)

/--
Definition of `indexesOf` / `indexesOf` 的定义

English:
definition indexesOf
  signature: [DecidableEq α] (a : α)
  body: findIndexes (Eq a)

中文:
定义 indexesOf
  签名: [DecidableEq α] (a : α)
  定义体: findIndexes (Eq a)

Depends on / 依赖: findIndexes
-/
def indexesOf [DecidableEq α] (a : α) : WSeq α -> WSeq Nat :=
  findIndexes (Eq a)

/--
Definition of `union` / `union` 的定义

English:
definition union
  signature: (s1 s2 : WSeq α)
  body: @Seq.corec (Option α) (WSeq α × WSeq α)
    (fun ⟨s1, s2⟩ =>
      match Seq.destruct s1, Seq.destruct s2 with
      | none, none => none
      | some (a1, s1'), none => some (a1, s1', nil)
      | none, some (a2, s2') => some (a2, nil, s2')
      | some (none, s1'), some (none, s2') => some (none, s1', s2')
      | some (some a1, s1'), some (none, s2') => some (some a1, s1', s2')
      | some (none, s1'), some (some a2, s2') => some (some a2, s1', s2')
      | some (some a1, s1'), some (some a2, s2') => some (some a1, cons a2 s1', s2'))
    (s1, s2)

中文:
定义 union
  签名: (s1 s2 : WSeq α)
  定义体: @Seq.corec (Option α) (WSeq α × WSeq α)
    (fun ⟨s1, s2⟩ =>
      match Seq.destruct s1, Seq.destruct s2 with
      | none, none => none
      | some (a1, s1'), none => some (a1, s1', nil)
      | none, some (a2, s2') => some (a2, nil, s2')
      | some (none, s1'), some (none, s2') => some (none, s1', s2')
      | some (some a1, s1'), some (none, s2') => some (some a1, s1', s2')
      | some (none, s1'), some (some a2, s2') => some (some a2, s1', s2')
      | some (some a1, s1'), some (some a2, s2') => some (some a1, cons a2 s1', s2'))
    (s1, s2)

Depends on / 依赖: Seq.corec, Seq.destruct, destruct
-/
def union (s1 s2 : WSeq α) : WSeq α :=
  @Seq.corec (Option α) (WSeq α × WSeq α)
    (fun ⟨s1, s2⟩ =>
      match Seq.destruct s1, Seq.destruct s2 with
      | none, none => none
      | some (a1, s1'), none => some (a1, s1', nil)
      | none, some (a2, s2') => some (a2, nil, s2')
      | some (none, s1'), some (none, s2') => some (none, s1', s2')
      | some (some a1, s1'), some (none, s2') => some (some a1, s1', s2')
      | some (none, s1'), some (some a2, s2') => some (some a2, s1', s2')
      | some (some a1, s1'), some (some a2, s2') => some (some a1, cons a2 s1', s2'))
    (s1, s2)

/--
Definition of `isEmpty` / `isEmpty` 的定义

English:
definition isEmpty
  signature: (s : WSeq α)
  body: Computation.map Option.isNone head s

中文:
定义 isEmpty
  签名: (s : WSeq α)
  定义体: Computation.map Option.isNone head s

Depends on / 依赖: Computation, Computation.map, Option.isNone, isNone
-/
def isEmpty (s : WSeq α) : Computation Bool :=
Computation.map Option.isNone head s

/--
Definition of `compute` / `compute` 的定义

English:
definition compute
  signature: (s : WSeq α)
  body: match Seq.destruct s with
  | some (none, s') => s'
  | _ => s

中文:
定义 compute
  签名: (s : WSeq α)
  定义体: match Seq.destruct s with
  | some (none, s') => s'
  | _ => s

Depends on / 依赖: Seq.destruct, destruct
-/
def compute (s : WSeq α) : WSeq α :=
  match Seq.destruct s with
  | some (none, s') => s'
  | _ => s

/--
Definition of `take` / `take` 的定义

English:
definition take
  signature: (s : WSeq α) (n : Nat)
  body: @Seq.corec (Option α) (Nat × WSeq α)
    (fun ⟨n, s⟩ =>
      match n, Seq.destruct s with
      | 0, _ => none
      | _ + 1, none => none
      | m + 1, some (none, s') => some (none, m + 1, s')
      | m + 1, some (some a, s') => some (some a, m, s'))
    (n, s)

中文:
定义 take
  签名: (s : WSeq α) (n : 自然数)
  定义体: @Seq.corec (Option α) (Nat × WSeq α)
    (fun ⟨n, s⟩ =>
      match n, Seq.destruct s with
      | 0, _ => none
      | _ + 1, none => none
      | m + 1, some (none, s') => some (none, m + 1, s')
      | m + 1, some (some a, s') => some (some a, m, s'))
    (n, s)

Depends on / 依赖: Seq.corec, Seq.destruct, destruct
-/
def take (s : WSeq α) (n : Nat) : WSeq α :=
  @Seq.corec (Option α) (Nat × WSeq α)
    (fun ⟨n, s⟩ =>
      match n, Seq.destruct s with
      | 0, _ => none
      | _ + 1, none => none
      | m + 1, some (none, s') => some (none, m + 1, s')
      | m + 1, some (some a, s') => some (some a, m, s'))
    (n, s)

/--
Definition of `splitAt` / `splitAt` 的定义

English:
definition splitAt
  signature: (s : WSeq α) (n : Nat)
  body: @Computation.corec (List α × WSeq α) (Nat × List α × WSeq α)
    (fun ⟨n, l, s⟩ =>
      match n, Seq.destruct s with
      | 0, _ => Sum.inl (l.reverse, s)
      | _ + 1, none => Sum.inl (l.reverse, s)
      | _ + 1, some (none, s') => Sum.inr (n, l, s')
      | m + 1, some (some a, s') => Sum.inr (m, a::l, s'))
    (n, [], s)

中文:
定义 splitAt
  签名: (s : WSeq α) (n : 自然数)
  定义体: @Computation.corec (List α × WSeq α) (Nat × List α × WSeq α)
    (fun ⟨n, l, s⟩ =>
      match n, Seq.destruct s with
      | 0, _ => Sum.inl (l.reverse, s)
      | _ + 1, none => Sum.inl (l.reverse, s)
      | _ + 1, some (none, s') => Sum.inr (n, l, s')
      | m + 1, some (some a, s') => Sum.inr (m, a::l, s'))
    (n, [], s)

Depends on / 依赖: Computation, Computation.corec, Seq.destruct, Sum.inl, Sum.inr, destruct, l.reverse, reverse
-/
def splitAt (s : WSeq α) (n : Nat) : Computation (List α × WSeq α) :=
  @Computation.corec (List α × WSeq α) (Nat × List α × WSeq α)
    (fun ⟨n, l, s⟩ =>
      match n, Seq.destruct s with
      | 0, _ => Sum.inl (l.reverse, s)
      | _ + 1, none => Sum.inl (l.reverse, s)
      | _ + 1, some (none, s') => Sum.inr (n, l, s')
      | m + 1, some (some a, s') => Sum.inr (m, a::l, s'))
    (n, [], s)

/--
Definition of `any` / `any` 的定义

English:
definition any
  signature: (s : WSeq α) (p : α -> Bool)
  body: Computation.corec
    (fun s : WSeq α =>
      match Seq.destruct s with
      | none => Sum.inl false
      | some (none, s') => Sum.inr s'
      | some (some a, s') => if p a then Sum.inl true else Sum.inr s')
    s

中文:
定义 any
  签名: (s : WSeq α) (p : α -> 布尔值)
  定义体: Computation.corec
    (fun s : WSeq α =>
      match Seq.destruct s with
      | none => Sum.inl false
      | some (none, s') => Sum.inr s'
      | some (some a, s') => if p a then Sum.inl true else Sum.inr s')
    s

Depends on / 依赖: Computation, Computation.corec, Seq.destruct, Sum.inl, Sum.inr, destruct
-/
def any (s : WSeq α) (p : α -> Bool) : Computation Bool :=
  Computation.corec
    (fun s : WSeq α =>
      match Seq.destruct s with
      | none => Sum.inl false
      | some (none, s') => Sum.inr s'
      | some (some a, s') => if p a then Sum.inl true else Sum.inr s')
    s

/--
Definition of `all` / `all` 的定义

English:
definition all
  signature: (s : WSeq α) (p : α -> Bool)
  body: Computation.corec
    (fun s : WSeq α =>
      match Seq.destruct s with
      | none => Sum.inl true
      | some (none, s') => Sum.inr s'
      | some (some a, s') => if p a then Sum.inr s' else Sum.inl false)
    s

中文:
定义 all
  签名: (s : WSeq α) (p : α -> 布尔值)
  定义体: Computation.corec
    (fun s : WSeq α =>
      match Seq.destruct s with
      | none => Sum.inl true
      | some (none, s') => Sum.inr s'
      | some (some a, s') => if p a then Sum.inr s' else Sum.inl false)
    s

Depends on / 依赖: Computation, Computation.corec, Seq.destruct, Sum.inl, Sum.inr, destruct
-/
def all (s : WSeq α) (p : α -> Bool) : Computation Bool :=
  Computation.corec
    (fun s : WSeq α =>
      match Seq.destruct s with
      | none => Sum.inl true
      | some (none, s') => Sum.inr s'
      | some (some a, s') => if p a then Sum.inr s' else Sum.inl false)
    s

/--
Definition of `scanl` / `scanl` 的定义

English:
definition scanl
  signature: (f : α -> β -> α) (a : α) (s : WSeq β)
  body: cons a
    @Seq.corec (Option α) (α × WSeq β)
      (fun ⟨a, s⟩ =>
        match Seq.destruct s with
        | none => none
        | some (none, s') => some (none, a, s')
        | some (some b, s') =>
          let a' := f a b
          some (some a', a', s'))
      (a, s)

中文:
定义 scanl
  签名: (f : α -> β -> α) (a : α) (s : WSeq β)
  定义体: cons a
    @Seq.corec (Option α) (α × WSeq β)
      (fun ⟨a, s⟩ =>
        match Seq.destruct s with
        | none => none
        | some (none, s') => some (none, a, s')
        | some (some b, s') =>
          let a' := f a b
          some (some a', a', s'))
      (a, s)

Depends on / 依赖: Seq.corec, Seq.destruct, destruct
-/
def scanl (f : α -> β -> α) (a : α) (s : WSeq β) : WSeq α :=
cons a
    @Seq.corec (Option α) (α × WSeq β)
      (fun ⟨a, s⟩ =>
        match Seq.destruct s with
        | none => none
        | some (none, s') => some (none, a, s')
        | some (some b, s') =>
          let a' := f a b
          some (some a', a', s'))
      (a, s)

/--
Definition of `inits` / `inits` 的定义

English:
definition inits
  signature: (s : WSeq α)
  body: cons []
    @Seq.corec (Option (List α)) (Batteries.DList α × WSeq α)
      (fun ⟨l, s⟩ =>
        match Seq.destruct s with
        | none => none
        | some (none, s') => some (none, l, s')
        | some (some a, s') =>
          let l' := l.push a
          some (some l'.toList, l', s'))
      (Batteries.DList.empty, s)

中文:
定义 inits
  签名: (s : WSeq α)
  定义体: cons []
    @Seq.corec (Option (List α)) (Batteries.DList α × WSeq α)
      (fun ⟨l, s⟩ =>
        match Seq.destruct s with
        | none => none
        | some (none, s') => some (none, l, s')
        | some (some a, s') =>
          let l' := l.push a
          some (some l'.toList, l', s'))
      (Batteries.DList.empty, s)

Depends on / 依赖: Batteries, Batteries.DList, Batteries.DList.empty, Seq.corec, Seq.destruct, destruct, l.push, toList
-/
def inits (s : WSeq α) : WSeq (List α) :=
cons []
    @Seq.corec (Option (List α)) (Batteries.DList α × WSeq α)
      (fun ⟨l, s⟩ =>
        match Seq.destruct s with
        | none => none
        | some (none, s') => some (none, l, s')
        | some (some a, s') =>
          let l' := l.push a
          some (some l'.toList, l', s'))
      (Batteries.DList.empty, s)

/--
Definition of `collect` / `collect` 的定义

English:
definition collect
  signature: (s : WSeq α) (n : Nat)
  body: (Seq.take n s).filterMap id

中文:
定义 collect
  签名: (s : WSeq α) (n : 自然数)
  定义体: (Seq.take n s).filterMap id

Depends on / 依赖: Seq.take, filterMap
-/
def collect (s : WSeq α) (n : Nat) : List α :=
  (Seq.take n s).filterMap id

/--
theorem `length_eq_map` / 定理 `length_eq_map`

English:
theorem length_eq_map
  given: (s : WSeq α)
  statement: length s = Computation.map List.length (toList s)
  proof: by
  refine
    Computation.eq_of_bisim
      (fun c1 c2 =>
        exists (l : List α) (s : WSeq α),
          c1 = Computation.corec (fun ⟨n, s⟩ =>
            match Seq.destruct s with
            | none => Sum.inl n
            | some (none, s') => Sum.inr (n, s')
            | some (some _, s') => Sum.inr (n + 1, s')) (l.length, s) ∧
            c2 = Computation.map List.length (Computation.corec (fun ⟨l, s⟩ =>
              match Seq.destruct s with
              | none => Sum.inl l.reverse
              | some (none, s') => Sum.inr (l, s')
              | some (some a, s') => Sum.inr (a::l, s')) (l, s)))
      ?_ ⟨[], s, rfl, rfl⟩
  intro s1 s2 h; rcases h with ⟨l, s, h⟩; rw [h.left, h.right]
  induction s using WSeq.recOn with
  | nil => simp [nil]
  | cons a s => simpa using ⟨a::l, s, by simp, by simp⟩
  | think s => simpa using ⟨l, s, by simp, by simp⟩

中文:
定理 length_eq_map
  条件: (s : WSeq α)
  结论: length s = Computation.map 列表.length (toList s)
  证明: by
  refine
    Computation.eq_of_bisim
      (fun c1 c2 =>
        exists (l : List α) (s : WSeq α),
          c1 = Computation.corec (fun ⟨n, s⟩ =>
            match Seq.destruct s with
            | none => Sum.inl n
            | some (none, s') => Sum.inr (n, s')
            | some (some _, s') => Sum.inr (n + 1, s')) (l.length, s) ∧
            c2 = Computation.map List.length (Computation.corec (fun ⟨l, s⟩ =>
              match Seq.destruct s with
              | none => Sum.inl l.reverse
              | some (none, s') => Sum.inr (l, s')
              | some (some a, s') => Sum.inr (a::l, s')) (l, s)))
      ?_ ⟨[], s, rfl, rfl⟩
  intro s1 s2 h; rcases h with ⟨l, s, h⟩; rw [h.left, h.right]
  induction s using WSeq.recOn with
  | nil => simp [nil]
  | cons a s => simpa using ⟨a::l, s, by simp, by simp⟩
  | think s => simpa using ⟨l, s, by simp, by simp⟩

Depends on / 依赖: Computation, Computation.corec, Computation.eq_of_bisim, Computation.map, List.length, Seq.destruct, Sum.inl, Sum.inr, destruct, eq_of_bisim, l.length, l.reverse, length, reverse
-/
theorem length_eq_map (s : WSeq α) : length s = Computation.map List.length (toList s) := by
  refine
    Computation.eq_of_bisim
      (fun c1 c2 =>
        exists (l : List α) (s : WSeq α),
          c1 = Computation.corec (fun ⟨n, s⟩ =>
            match Seq.destruct s with
            | none => Sum.inl n
            | some (none, s') => Sum.inr (n, s')
            | some (some _, s') => Sum.inr (n + 1, s')) (l.length, s) ∧
            c2 = Computation.map List.length (Computation.corec (fun ⟨l, s⟩ =>
              match Seq.destruct s with
              | none => Sum.inl l.reverse
              | some (none, s') => Sum.inr (l, s')
              | some (some a, s') => Sum.inr (a::l, s')) (l, s)))
      ?_ ⟨[], s, rfl, rfl⟩
  intro s1 s2 h; rcases h with ⟨l, s, h⟩; rw [h.left, h.right]
  induction s using WSeq.recOn with
  | nil => simp [nil]
  | cons a s => simpa using ⟨a::l, s, by simp, by simp⟩
  | think s => simpa using ⟨l, s, by simp, by simp⟩

end Stream'.WSeq
