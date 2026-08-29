/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

public import Mathlib.Init

/-!
# Helper definitions and instances for `Ordering`
-/

@[expose] public section

universe u

namespace Ordering

variable {α : Type*}

/--
Definition of `Compares` / `Compares` 的定义

English:
definition Compares
  signature: [LT α]

中文:
定义 Compares
  签名: [LT α]
-/
def Compares [LT α] : Ordering -> α -> α -> Prop
  | lt, a, b => a < b
  | eq, a, b => a = b
  | gt, a, b => a > b

/--
lemma `compares_lt` / 引理 `compares_lt`

English:
lemma compares_lt
  given: [LT α] (a b : α)
  statement: Compares lt a b = (a < b)
  proof: rfl

中文:
引理 compares_lt
  条件: [LT α] (a b : α)
  结论: Compares lt a b = (a < b)
  证明: rfl
-/
@[simp] lemma compares_lt [LT α] (a b : α) : Compares lt a b = (a < b) := rfl

/--
lemma `compares_eq` / 引理 `compares_eq`

English:
lemma compares_eq
  given: [LT α] (a b : α)
  statement: Compares eq a b = (a = b)
  proof: rfl

中文:
引理 compares_eq
  条件: [LT α] (a b : α)
  结论: Compares eq a b = (a = b)
  证明: rfl
-/
@[simp] lemma compares_eq [LT α] (a b : α) : Compares eq a b = (a = b) := rfl

/--
lemma `compares_gt` / 引理 `compares_gt`

English:
lemma compares_gt
  given: [LT α] (a b : α)
  statement: Compares gt a b = (a > b)
  proof: rfl

中文:
引理 compares_gt
  条件: [LT α] (a b : α)
  结论: Compares gt a b = (a > b)
  证明: rfl
-/
@[simp] lemma compares_gt [LT α] (a b : α) : Compares gt a b = (a > b) := rfl

/--
Definition of `dthen` / `dthen` 的定义

English:
definition dthen
  signature: :

中文:
定义 dthen
  签名: :
-/
@[macro_inline] def dthen :
    (o : Ordering) -> (o = .eq -> Ordering) -> Ordering
  | .eq, f => f rfl
  | o, _ => o

end Ordering

/--
Definition of `cmpUsing` / `cmpUsing` 的定义

English:
definition cmpUsing
  signature: {α : Type u} (lt : α -> α -> Prop) [DecidableRel lt] (a b : α)
  body: if lt a b then Ordering.lt else if lt b a then Ordering.gt else Ordering.eq

中文:
定义 cmpUsing
  签名: {α : 类型u} (lt : α -> α -> 命题) [DecidableRel lt] (a b : α)
  定义体: if lt a b then Ordering.lt else if lt b a then Ordering.gt else Ordering.eq

Depends on / 依赖: Ordering, Ordering.eq, Ordering.gt, Ordering.lt
-/
def cmpUsing {α : Type u} (lt : α -> α -> Prop) [DecidableRel lt] (a b : α) : Ordering :=
  if lt a b then Ordering.lt else if lt b a then Ordering.gt else Ordering.eq

/--
Definition of `cmp` / `cmp` 的定义

English:
definition cmp
  signature: {α : Type u} [LT α] [DecidableLT α] (a b : α)
  body: cmpUsing (· < ·) a b

中文:
定义 cmp
  签名: {α : 类型u} [LT α] [DecidableLT α] (a b : α)
  定义体: cmpUsing (· < ·) a b

Depends on / 依赖: cmpUsing
-/
def cmp {α : Type u} [LT α] [DecidableLT α] (a b : α) : Ordering :=
  cmpUsing (· < ·) a b
