/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
module

public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Common
public import Mathlib.Util.CompileInductive

/-! ### Induction principles for lists -/

@[expose] public section

variable {α : Type*}

namespace List

/-- Induction principle from the right for lists: if a property holds for the empty list, and
for `l ++ [a]` if it holds for `l`, then it holds for all lists. The principle is given for
a `Sort`-valued predicate, i.e., it can also be used to construct data. -/
@[elab_as_elim]
/--
Definition of `reverseRec` / `reverseRec` 的定义

English:
definition reverseRec
  signature: {motive : List α -> Sort*} (nil : motive [])

中文:
定义 reverseRec
  签名: {motive : 列表 α -> 类型层*} (nil : motive [])
-/
def reverseRec {motive : List α -> Sort*} (nil : motive [])
    (append_singleton : forall (l : List α) (a : α), motive l -> motive (l ++ [a])) : forall l, motive l
  | [] => nil
  | a :: l => (dropLast_concat_getLast (cons_ne_nil a l)) ▸
    append_singleton _ _ ((a :: l).dropLast.reverseRec nil append_singleton)
  termination_by l => l.length

@[simp]
/--
theorem `reverseRec_nil` / 定理 `reverseRec_nil`

English:
theorem reverseRec_nil
  statement: {motive : List α -> Sort*} (nil : motive [])
  proof: by grind [reverseRec]

@[simp]

中文:
定理 reverseRec_nil
  结论: {motive : 列表 α -> 类型层*} (nil : motive [])
  证明: by grind [reverseRec]

@[simp]

Depends on / 依赖: reverseRec
-/
theorem reverseRec_nil {motive : List α -> Sort*} (nil : motive [])
    (append_singleton : forall (l : List α) (a : α), motive l -> motive (l ++ [a])) :
    [].reverseRec nil append_singleton = nil := by grind [reverseRec]

@[simp]
/--
theorem `reverseRec_concat` / 定理 `reverseRec_concat`

English:
theorem reverseRec_concat
  statement: {motive : List α -> Sort*} (x : α) (xs : List α) (nil : motive [])
  proof: by
  grind [reverseRec, cases List]

中文:
定理 reverseRec_concat
  结论: {motive : 列表 α -> 类型层*} (x : α) (xs : 列表 α) (nil : motive [])
  证明: by
  grind [reverseRec, cases List]

Depends on / 依赖: reverseRec
-/
theorem reverseRec_concat {motive : List α -> Sort*} (x : α) (xs : List α) (nil : motive [])
    (append_singleton : forall (l : List α) (a : α), motive l -> motive (l ++ [a])) :
    (xs ++ [x]).reverseRec nil append_singleton =
    append_singleton xs x (xs.reverseRec nil append_singleton) := by
  grind [reverseRec, cases List]

/-- Like `reverseRec`, but with the list parameter placed first. -/
@[elab_as_elim]
/--
Definition of `reverseRecOn` / `reverseRecOn` 的定义

English:
abbreviation reverseRecOn
  signature: {motive : List α -> Sort*} (l : List α) (nil : motive [])
  body: reverseRec nil append_singleton l

中文:
缩写 reverseRecOn
  签名: {motive : 列表 α -> 类型层*} (l : 列表 α) (nil : motive [])
  定义体: reverseRec nil append_singleton l

Depends on / 依赖: append_singleton, reverseRec
-/
abbrev reverseRecOn {motive : List α -> Sort*} (l : List α) (nil : motive [])
    (append_singleton : forall (l : List α) (a : α), motive l -> motive (l ++ [a])) : motive l :=
  reverseRec nil append_singleton l

/--
theorem `reverseRecOn_nil` / 定理 `reverseRecOn_nil`

English:
theorem reverseRecOn_nil
  statement: {motive : List α -> Sort*} (nil : motive [])
  proof: by simp

中文:
定理 reverseRecOn_nil
  结论: {motive : 列表 α -> 类型层*} (nil : motive [])
  证明: by simp
-/
theorem reverseRecOn_nil {motive : List α -> Sort*} (nil : motive [])
    (append_singleton : forall (l : List α) (a : α), motive l -> motive (l ++ [a])) :
    reverseRecOn [] nil append_singleton = nil := by simp

/--
theorem `reverseRecOn_concat` / 定理 `reverseRecOn_concat`

English:
theorem reverseRecOn_concat
  statement: {motive : List α -> Sort*} (x : α) (xs : List α) (nil : motive [])
  proof: by simp

中文:
定理 reverseRecOn_concat
  结论: {motive : 列表 α -> 类型层*} (x : α) (xs : 列表 α) (nil : motive [])
  证明: by simp
-/
theorem reverseRecOn_concat {motive : List α -> Sort*} (x : α) (xs : List α) (nil : motive [])
    (append_singleton : forall (l : List α) (a : α), motive l -> motive (l ++ [a])) :
    (xs ++ [x]).reverseRecOn nil append_singleton =
      append_singleton xs x (reverseRecOn xs nil append_singleton) := by simp

/-- Bidirectional induction principle for lists: if a property holds for the empty list, the
singleton list, and `a :: (l ++ [b])` from `l`, then it holds for all lists. This can be used to
prove statements about palindromes. The principle is given for a `Sort`-valued predicate, i.e., it
can also be used to construct data. -/
@[elab_as_elim]
/--
Definition of `bidirectionalRec` / `bidirectionalRec` 的定义

English:
definition bidirectionalRec
  signature: {motive : List α -> Sort*} (nil : motive []) (singleton : forall a : α, motive [a])

中文:
定义 bidirectionalRec
  签名: {motive : 列表 α -> 类型层*} (nil : motive []) (singleton : 对任意 a : α, motive [a])
-/
def bidirectionalRec {motive : List α -> Sort*} (nil : motive []) (singleton : forall a : α, motive [a])
    (cons_append : forall (a : α) (l : List α) (b : α), motive l -> motive (a :: (l ++ [b]))) :
    forall l, motive l
  | [] => nil
  | [a] => singleton a
  | a :: b :: l =>
    (dropLast_concat_getLast (cons_ne_nil b l)) ▸
    cons_append a ((b :: l).dropLast) ((b :: l).getLast (cons_ne_nil _ _))
    ((b :: l).dropLast.bidirectionalRec nil singleton cons_append)
termination_by l => l.length

@[simp]
/--
theorem `bidirectionalRec_nil` / 定理 `bidirectionalRec_nil`

English:
theorem bidirectionalRec_nil
  statement: {motive : List α -> Sort*}
  proof: by grind [bidirectionalRec]


@[simp]

中文:
定理 bidirectionalRec_nil
  结论: {motive : 列表 α -> 类型层*}
  证明: by grind [bidirectionalRec]


@[simp]

Depends on / 依赖: bidirectionalRec
-/
theorem bidirectionalRec_nil {motive : List α -> Sort*}
    (nil : motive []) (singleton : forall a : α, motive [a])
    (cons_append : forall (a : α) (l : List α) (b : α), motive l -> motive (a :: (l ++ [b]))) :
    bidirectionalRec nil singleton cons_append [] = nil := by grind [bidirectionalRec]


@[simp]
/--
theorem `bidirectionalRec_singleton` / 定理 `bidirectionalRec_singleton`

English:
theorem bidirectionalRec_singleton
  statement: {motive : List α -> Sort*}
  proof: by
  grind [bidirectionalRec]

@[simp]

中文:
定理 bidirectionalRec_singleton
  结论: {motive : 列表 α -> 类型层*}
  证明: by
  grind [bidirectionalRec]

@[simp]

Depends on / 依赖: bidirectionalRec
-/
theorem bidirectionalRec_singleton {motive : List α -> Sort*}
    (nil : motive []) (singleton : forall a : α, motive [a])
    (cons_append : forall (a : α) (l : List α) (b : α), motive l -> motive (a :: (l ++ [b]))) (a : α) :
    bidirectionalRec nil singleton cons_append [a] = singleton a := by
  grind [bidirectionalRec]

@[simp]
/--
theorem `bidirectionalRec_cons_append` / 定理 `bidirectionalRec_cons_append`

English:
theorem bidirectionalRec_cons_append
  statement: {motive : List α -> Sort*}
  proof: by
  grind [bidirectionalRec, cases List]

中文:
定理 bidirectionalRec_cons_append
  结论: {motive : 列表 α -> 类型层*}
  证明: by
  grind [bidirectionalRec, cases List]

Depends on / 依赖: bidirectionalRec
-/
theorem bidirectionalRec_cons_append {motive : List α -> Sort*}
    (nil : motive []) (singleton : forall a : α, motive [a])
    (cons_append : forall (a : α) (l : List α) (b : α), motive l -> motive (a :: (l ++ [b])))
    (a : α) (l : List α) (b : α) :
    bidirectionalRec nil singleton cons_append (a :: (l ++ [b])) =
      cons_append a l b (bidirectionalRec nil singleton cons_append l) := by
  grind [bidirectionalRec, cases List]

/-- Like `bidirectionalRec`, but with the list parameter placed first. -/
@[elab_as_elim]
/--
Definition of `bidirectionalRecOn` / `bidirectionalRecOn` 的定义

English:
abbreviation bidirectionalRecOn
  signature: {C : List α -> Sort*} (l : List α) (H0 : C []) (H1 : forall a : α, C [a])
  body: bidirectionalRec H0 H1 Hn l

中文:
缩写 bidirectionalRecOn
  签名: {C : 列表 α -> 类型层*} (l : 列表 α) (H0 : C []) (H1 : 对任意 a : α, C [a])
  定义体: bidirectionalRec H0 H1 Hn l

Depends on / 依赖: bidirectionalRec
-/
abbrev bidirectionalRecOn {C : List α -> Sort*} (l : List α) (H0 : C []) (H1 : forall a : α, C [a])
    (Hn : forall (a : α) (l : List α) (b : α), C l -> C (a :: (l ++ [b]))) : C l :=
  bidirectionalRec H0 H1 Hn l

/--
A dependent recursion principle for nonempty lists. Useful for dealing with
operations like `List.head` which are not defined on the empty list.
-/
@[elab_as_elim]
/--
Definition of `recNeNil` / `recNeNil` 的定义

English:
definition recNeNil
  signature: {motive : (l : List α) -> l != [] -> Sort*}
  body: match l with
  | [x] => singleton x
  | x :: y :: xs =>
    cons x (y :: xs) (cons_ne_nil y xs) (recNeNil singleton cons (y :: xs) (cons_ne_nil y xs))

@[simp]

中文:
定义 recNeNil
  签名: {motive : (l : 列表 α) -> l != [] -> 类型层*}
  定义体: match l with
  | [x] => singleton x
  | x :: y :: xs =>
    cons x (y :: xs) (cons_ne_nil y xs) (recNeNil singleton cons (y :: xs) (cons_ne_nil y xs))

@[simp]

Depends on / 依赖: cons_ne_nil, recNeNil, singleton
-/
def recNeNil {motive : (l : List α) -> l != [] -> Sort*}
    (singleton : forall x, motive [x] (cons_ne_nil x []))
    (cons : forall x xs h, motive xs h -> motive (x :: xs) (cons_ne_nil x xs))
    (l : List α) (h : l != []) : motive l h :=
  match l with
  | [x] => singleton x
  | x :: y :: xs =>
    cons x (y :: xs) (cons_ne_nil y xs) (recNeNil singleton cons (y :: xs) (cons_ne_nil y xs))

@[simp]
/--
theorem `recNeNil_singleton` / 定理 `recNeNil_singleton`

English:
theorem recNeNil_singleton
  statement: {motive : (l : List α) -> l != [] -> Sort*} (x : α)
  proof: rfl

@[simp]

中文:
定理 recNeNil_singleton
  结论: {motive : (l : 列表 α) -> l != [] -> 类型层*} (x : α)
  证明: rfl

@[simp]
-/
theorem recNeNil_singleton {motive : (l : List α) -> l != [] -> Sort*} (x : α)
    (singleton : forall x, motive [x] (cons_ne_nil x []))
    (cons : forall x xs h, motive xs h -> motive (x :: xs) (cons_ne_nil x xs)) :
    recNeNil singleton cons [x] (cons_ne_nil x []) = singleton x := rfl

@[simp]
/--
theorem `recNeNil_cons` / 定理 `recNeNil_cons`

English:
theorem recNeNil_cons
  statement: {motive : (l : List α) -> l != [] -> Sort*} (x : α) (xs : List α) (h : xs != [])
  proof: match xs with
  | _ :: _ => rfl

中文:
定理 recNeNil_cons
  结论: {motive : (l : 列表 α) -> l != [] -> 类型层*} (x : α) (xs : 列表 α) (h : xs != [])
  证明: match xs with
  | _ :: _ => rfl
-/
theorem recNeNil_cons {motive : (l : List α) -> l != [] -> Sort*} (x : α) (xs : List α) (h : xs != [])
    (singleton : forall x, motive [x] (cons_ne_nil x []))
    (cons : forall x xs h, motive xs h -> motive (x :: xs) (cons_ne_nil x xs)) :
    recNeNil singleton cons (x :: xs) (cons_ne_nil x xs) =
      cons x xs h (recNeNil singleton cons xs h) :=
  match xs with
  | _ :: _ => rfl

/--
A dependent recursion principle for nonempty lists. Useful for dealing with
operations like `List.head` which are not defined on the empty list.
Same as `List.recNeNil`, with a more convenient argument order.
-/
@[elab_as_elim, simp]
/--
Definition of `recOnNeNil` / `recOnNeNil` 的定义

English:
abbreviation recOnNeNil
  signature: {motive : (l : List α) -> l != [] -> Sort*} (l : List α) (h : l != [])
  body: recNeNil singleton cons l h

中文:
缩写 recOnNeNil
  签名: {motive : (l : 列表 α) -> l != [] -> 类型层*} (l : 列表 α) (h : l != [])
  定义体: recNeNil singleton cons l h

Depends on / 依赖: recNeNil, singleton
-/
abbrev recOnNeNil {motive : (l : List α) -> l != [] -> Sort*} (l : List α) (h : l != [])
    (singleton : forall x, motive [x] (cons_ne_nil x []))
    (cons : forall x xs h, motive xs h -> motive (x :: xs) (cons_ne_nil x xs)) :
    motive l h := recNeNil singleton cons l h

/--
A recursion principle for lists which separates the singleton case.
-/
@[elab_as_elim]
/--
Definition of `twoStepInduction` / `twoStepInduction` 的定义

English:
definition twoStepInduction
  signature: {motive : (l : List α) -> Sort*} (nil : motive [])
  body: match l with
  | [] => nil
  | [x] => singleton x
  | x :: y :: xs =>
    cons_cons x y xs
    (twoStepInduction nil singleton cons_cons xs)
    (fun y => twoStepInduction nil singleton cons_cons (y :: xs))

@[simp]

中文:
定义 twoStepInduction
  签名: {motive : (l : 列表 α) -> 类型层*} (nil : motive [])
  定义体: match l with
  | [] => nil
  | [x] => singleton x
  | x :: y :: xs =>
    cons_cons x y xs
    (twoStepInduction nil singleton cons_cons xs)
    (fun y => twoStepInduction nil singleton cons_cons (y :: xs))

@[simp]
-/
def twoStepInduction {motive : (l : List α) -> Sort*} (nil : motive [])
    (singleton : forall x, motive [x])
    (cons_cons : forall x y xs, motive xs -> (forall y, motive (y :: xs)) -> motive (x :: y :: xs))
    (l : List α) : motive l := match l with
  | [] => nil
  | [x] => singleton x
  | x :: y :: xs =>
    cons_cons x y xs
    (twoStepInduction nil singleton cons_cons xs)
    (fun y => twoStepInduction nil singleton cons_cons (y :: xs))

@[simp]
/--
theorem `twoStepInduction_nil` / 定理 `twoStepInduction_nil`

English:
theorem twoStepInduction_nil
  statement: {motive : (l : List α) -> Sort*} (nil : motive [])
  proof: twoStepInduction.eq_1 ..

@[simp]

中文:
定理 twoStepInduction_nil
  结论: {motive : (l : 列表 α) -> 类型层*} (nil : motive [])
  证明: twoStepInduction.eq_1 ..

@[simp]

Depends on / 依赖: eq_1, twoStepInduction, twoStepInduction.eq_1
-/
theorem twoStepInduction_nil {motive : (l : List α) -> Sort*} (nil : motive [])
    (singleton : forall x, motive [x])
    (cons_cons : forall x y xs, motive xs -> (forall y, motive (y :: xs)) -> motive (x :: y :: xs)) :
    twoStepInduction nil singleton cons_cons [] = nil := twoStepInduction.eq_1 ..

@[simp]
/--
theorem `twoStepInduction_singleton` / 定理 `twoStepInduction_singleton`

English:
theorem twoStepInduction_singleton
  statement: {motive : (l : List α) -> Sort*} (x : α) (nil : motive [])
  proof: twoStepInduction.eq_2 ..

@[simp]

中文:
定理 twoStepInduction_singleton
  结论: {motive : (l : 列表 α) -> 类型层*} (x : α) (nil : motive [])
  证明: twoStepInduction.eq_2 ..

@[simp]

Depends on / 依赖: eq_2, twoStepInduction, twoStepInduction.eq_2
-/
theorem twoStepInduction_singleton {motive : (l : List α) -> Sort*} (x : α) (nil : motive [])
    (singleton : forall x, motive [x])
    (cons_cons : forall x y xs, motive xs -> (forall y, motive (y :: xs)) -> motive (x :: y :: xs)) :
    twoStepInduction nil singleton cons_cons [x] = singleton x := twoStepInduction.eq_2 ..

@[simp]
/--
theorem `twoStepInduction_cons_cons` / 定理 `twoStepInduction_cons_cons`

English:
theorem twoStepInduction_cons_cons
  statement: {motive : (l : List α) -> Sort*} (x y : α) (xs : List α)
  proof: twoStepInduction.eq_3 ..

中文:
定理 twoStepInduction_cons_cons
  结论: {motive : (l : 列表 α) -> 类型层*} (x y : α) (xs : 列表 α)
  证明: twoStepInduction.eq_3 ..

Depends on / 依赖: eq_3, twoStepInduction, twoStepInduction.eq_3
-/
theorem twoStepInduction_cons_cons {motive : (l : List α) -> Sort*} (x y : α) (xs : List α)
    (nil : motive []) (singleton : forall x, motive [x])
    (cons_cons : forall x y xs, motive xs -> (forall y, motive (y :: xs)) -> motive (x :: y :: xs)) :
    twoStepInduction nil singleton cons_cons (x :: y :: xs) =
    cons_cons x y xs
    (twoStepInduction nil singleton cons_cons xs)
    (fun y => twoStepInduction nil singleton cons_cons (y :: xs)) := twoStepInduction.eq_3 ..

end List
