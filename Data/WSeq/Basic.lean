/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Seq.Basic
public import Mathlib.Util.CompileInductive

/-!
# Partially defined possibly infinite lists

This file provides a `WSeq α` type representing partially defined possibly infinite lists
(referred here as weak sequences).
-/

@[expose] public section

namespace Stream'

open Function

universe u v w

/--
Definition of `WSeq` / `WSeq` 的定义

English:
definition WSeq
  signature: (α)
  body: Seq (Option α)

中文:
定义 WSeq
  签名: (α)
  定义体: Seq (Option α)
-/
def WSeq (α) :=
  Seq (Option α)

namespace WSeq

variable {α : Type u} {β : Type v} {γ : Type w}

/-- Turn a sequence into a weak sequence -/
@[coe]
/--
Definition of `ofSeq` / `ofSeq` 的定义

English:
definition ofSeq
  signature: : Seq α -> WSeq α
  body: (· <$> ·) some

中文:
定义 ofSeq
  签名: : 序列 α -> WSeq α
  定义体: (· <$> ·) some
-/
def ofSeq : Seq α -> WSeq α :=
  (· <$> ·) some

/-- Turn a list into a weak sequence -/
@[coe]
/--
Definition of `ofList` / `ofList` 的定义

English:
definition ofList
  signature: (l : List α)
  body: ofSeq l

中文:
定义 ofList
  签名: (l : 列表 α)
  定义体: ofSeq l
-/
def ofList (l : List α) : WSeq α :=
  ofSeq l

/-- Turn a stream into a weak sequence -/
@[coe]
/--
Definition of `ofStream` / `ofStream` 的定义

English:
definition ofStream
  signature: (l : Stream' α)
  body: ofSeq l

中文:
定义 ofStream
  签名: (l : Stream' α)
  定义体: ofSeq l
-/
def ofStream (l : Stream' α) : WSeq α :=
  ofSeq l

/--
Instance `coeSeq` / 实例 `coeSeq`

English:
instance coeSeq
  signature: : Coe (Seq α) (WSeq α)
  body: ⟨ofSeq⟩

中文:
实例 coeSeq
  签名: : Coe (序列 α) (WSeq α)
  定义体: ⟨ofSeq⟩
-/
instance coeSeq : Coe (Seq α) (WSeq α) :=
  ⟨ofSeq⟩

/--
Instance `coeList` / 实例 `coeList`

English:
instance coeList
  signature: : Coe (List α) (WSeq α)
  body: ⟨ofList⟩

中文:
实例 coeList
  签名: : Coe (列表 α) (WSeq α)
  定义体: ⟨ofList⟩

Depends on / 依赖: ofList
-/
instance coeList : Coe (List α) (WSeq α) :=
  ⟨ofList⟩

/--
Instance `coeStream` / 实例 `coeStream`

English:
instance coeStream
  signature: : Coe (Stream' α) (WSeq α)
  body: ⟨ofStream⟩

中文:
实例 coeStream
  签名: : Coe (Stream' α) (WSeq α)
  定义体: ⟨ofStream⟩

Depends on / 依赖: ofStream
-/
instance coeStream : Coe (Stream' α) (WSeq α) :=
  ⟨ofStream⟩

/--
Definition of `nil` / `nil` 的定义

English:
definition nil
  signature: : WSeq α
  body: Seq.nil

中文:
定义 nil
  签名: : WSeq α
  定义体: Seq.nil

Depends on / 依赖: Seq.nil
-/
def nil : WSeq α :=
  Seq.nil

/--
Instance `inhabited` / 实例 `inhabited`

English:
instance inhabited
  signature: : Inhabited (WSeq α)
  body: ⟨nil⟩

中文:
实例 inhabited
  签名: : 可居 (WSeq α)
  定义体: ⟨nil⟩
-/
instance inhabited : Inhabited (WSeq α) :=
  ⟨nil⟩

/--
Definition of `cons` / `cons` 的定义

English:
definition cons
  signature: (a : α)
  body: Seq.cons (some a)

中文:
定义 cons
  签名: (a : α)
  定义体: Seq.cons (some a)

Depends on / 依赖: Seq.cons
-/
def cons (a : α) : WSeq α -> WSeq α :=
  Seq.cons (some a)

/--
Definition of `think` / `think` 的定义

English:
definition think
  signature: : WSeq α -> WSeq α
  body: Seq.cons none

中文:
定义 think
  签名: : WSeq α -> WSeq α
  定义体: Seq.cons none

Depends on / 依赖: Seq.cons
-/
def think : WSeq α -> WSeq α :=
  Seq.cons none

/--
Definition of `destruct` / `destruct` 的定义

English:
definition destruct
  signature: : WSeq α -> Computation (Option (α × WSeq α))
  body: Computation.corec fun s =>
    match Seq.destruct s with
    | none => Sum.inl none
    | some (none, s') => Sum.inr s'
    | some (some a, s') => Sum.inl (some (a, s'))

中文:
定义 destruct
  签名: : WSeq α -> Computation (选项类型 (α × WSeq α))
  定义体: Computation.corec fun s =>
    match Seq.destruct s with
    | none => Sum.inl none
    | some (none, s') => Sum.inr s'
    | some (some a, s') => Sum.inl (some (a, s'))

Depends on / 依赖: Computation, Computation.corec, Seq.destruct, Sum.inl, Sum.inr, destruct
-/
def destruct : WSeq α -> Computation (Option (α × WSeq α)) :=
  Computation.corec fun s =>
    match Seq.destruct s with
    | none => Sum.inl none
    | some (none, s') => Sum.inr s'
    | some (some a, s') => Sum.inl (some (a, s'))

/-- Recursion principle for weak sequences, compare with `List.recOn`. -/
@[elab_as_elim]
/--
Definition of `recOn` / `recOn` 的定义

English:
definition recOn
  signature: {motive : WSeq α -> Sort v} (s : WSeq α) (nil : motive nil)
  body: Seq.recOn s nil fun o => Option.recOn o think cons

中文:
定义 recOn
  签名: {motive : WSeq α -> 类型层 v} (s : WSeq α) (nil : motive nil)
  定义体: Seq.recOn s nil fun o => Option.recOn o think cons

Depends on / 依赖: Option.recOn, Seq.recOn
-/
def recOn {motive : WSeq α -> Sort v} (s : WSeq α) (nil : motive nil)
    (cons : forall x s, motive (cons x s)) (think : forall s, motive (think s)) : motive s :=
  Seq.recOn s nil fun o => Option.recOn o think cons

/--
Definition of `Mem` / `Mem` 的定义

English:
definition Mem
  signature: (s : WSeq α) (a : α)
  body: Seq.Mem s (some a)

中文:
定义 Mem
  签名: (s : WSeq α) (a : α)
  定义体: Seq.Mem s (some a)
-/
protected def Mem (s : WSeq α) (a : α) :=
  Seq.Mem s (some a)

/--
Instance `membership` / 实例 `membership`

English:
instance membership
  signature: : Membership α (WSeq α)
  body: ⟨WSeq.Mem⟩

中文:
实例 membership
  签名: : Membership α (WSeq α)
  定义体: ⟨WSeq.Mem⟩

Depends on / 依赖: WSeq.Mem
-/
instance membership : Membership α (WSeq α) :=
  ⟨WSeq.Mem⟩

/--
theorem `notMem_nil` / 定理 `notMem_nil`

English:
theorem notMem_nil
  given: (a : α)
  statement: a ∉ @nil α
  proof: Seq.notMem_nil (some a)

中文:
定理 notMem_nil
  条件: (a : α)
  结论: a ∉ @nil α
  证明: Seq.notMem_nil (some a)

Depends on / 依赖: Seq.notMem_nil, notMem_nil
-/
theorem notMem_nil (a : α) : a ∉ @nil α :=
  Seq.notMem_nil (some a)

/--
Definition of `head` / `head` 的定义

English:
definition head
  signature: (s : WSeq α)
  body: Computation.map (Prod.fst <$> ·) (destruct s)

中文:
定义 head
  签名: (s : WSeq α)
  定义体: Computation.map (Prod.fst <$> ·) (destruct s)

Depends on / 依赖: Computation, Computation.map, Prod.fst, destruct
-/
def head (s : WSeq α) : Computation (Option α) :=
  Computation.map (Prod.fst <$> ·) (destruct s)

/--
Definition of `flatten` / `flatten` 的定义

English:
definition flatten
  signature: : Computation (WSeq α) -> WSeq α
  body: Seq.corec fun c =>
    match Computation.destruct c with
    | Sum.inl s => Seq.omap (return ·) (Seq.destruct s)
    | Sum.inr c' => some (none, c')

中文:
定义 flatten
  签名: : Computation (WSeq α) -> WSeq α
  定义体: Seq.corec fun c =>
    match Computation.destruct c with
    | Sum.inl s => Seq.omap (return ·) (Seq.destruct s)
    | Sum.inr c' => some (none, c')

Depends on / 依赖: Computation, Computation.destruct, Seq.corec, Seq.destruct, Seq.omap, Sum.inl, Sum.inr, destruct, return
-/
def flatten : Computation (WSeq α) -> WSeq α :=
  Seq.corec fun c =>
    match Computation.destruct c with
    | Sum.inl s => Seq.omap (return ·) (Seq.destruct s)
    | Sum.inr c' => some (none, c')

/--
Definition of `tail` / `tail` 的定义

English:
definition tail
  signature: (s : WSeq α)
  body: flatten (fun o => Option.recOn o nil Prod.snd) < > destruct s

中文:
定义 tail
  签名: (s : WSeq α)
  定义体: flatten (fun o => Option.recOn o nil Prod.snd) < > destruct s

Depends on / 依赖: Option.recOn, Prod.snd, destruct, flatten
-/
def tail (s : WSeq α) : WSeq α :=
flatten (fun o => Option.recOn o nil Prod.snd) < > destruct s

/--
Definition of `drop` / `drop` 的定义

English:
definition drop
  signature: (s : WSeq α)

中文:
定义 drop
  签名: (s : WSeq α)
-/
def drop (s : WSeq α) : Nat -> WSeq α
  | 0 => s
  | n + 1 => tail (drop s n)

/--
Definition of `get?` / `get?` 的定义

English:
definition get?
  signature: (s : WSeq α) (n : Nat)
  body: head (drop s n)

中文:
定义 get?
  签名: (s : WSeq α) (n : 自然数)
  定义体: head (drop s n)
-/
def get? (s : WSeq α) (n : Nat) : Computation (Option α) :=
  head (drop s n)

/--
Definition of `toList` / `toList` 的定义

English:
definition toList
  signature: (s : WSeq α)
  body: @Computation.corec (List α) (List α × WSeq α)
    (fun ⟨l, s⟩ =>
      match Seq.destruct s with
      | none => Sum.inl l.reverse
      | some (none, s') => Sum.inr (l, s')
      | some (some a, s') => Sum.inr (a::l, s'))
    ([], s)

中文:
定义 toList
  签名: (s : WSeq α)
  定义体: @Computation.corec (List α) (List α × WSeq α)
    (fun ⟨l, s⟩ =>
      match Seq.destruct s with
      | none => Sum.inl l.reverse
      | some (none, s') => Sum.inr (l, s')
      | some (some a, s') => Sum.inr (a::l, s'))
    ([], s)

Depends on / 依赖: Computation, Computation.corec, Seq.destruct, Sum.inl, Sum.inr, destruct, l.reverse, reverse
-/
def toList (s : WSeq α) : Computation (List α) :=
  @Computation.corec (List α) (List α × WSeq α)
    (fun ⟨l, s⟩ =>
      match Seq.destruct s with
      | none => Sum.inl l.reverse
      | some (none, s') => Sum.inr (l, s')
      | some (some a, s') => Sum.inr (a::l, s'))
    ([], s)

/--
Definition of `append` / `append` 的定义

English:
definition append
  signature: : WSeq α -> WSeq α -> WSeq α
  body: Seq.append

中文:
定义 append
  签名: : WSeq α -> WSeq α -> WSeq α
  定义体: Seq.append

Depends on / 依赖: Seq.append, append
-/
def append : WSeq α -> WSeq α -> WSeq α :=
  Seq.append

/--
Definition of `join` / `join` 的定义

English:
definition join
  signature: (S : WSeq (WSeq α))
  body: Seq.join
    ((fun o : Option (WSeq α) =>
        match o with
        | none => Seq1.ret none
        | some s => (none, s)) <$>
      S)

中文:
定义 join
  签名: (S : WSeq (WSeq α))
  定义体: Seq.join
    ((fun o : Option (WSeq α) =>
        match o with
        | none => Seq1.ret none
        | some s => (none, s)) <$>
      S)

Depends on / 依赖: Seq.join, Seq1.ret
-/
def join (S : WSeq (WSeq α)) : WSeq α :=
  Seq.join
    ((fun o : Option (WSeq α) =>
        match o with
        | none => Seq1.ret none
        | some s => (none, s)) <$>
      S)

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : α -> β)
  body: Seq.map (Option.map f)

中文:
定义 map
  签名: (f : α -> β)
  定义体: Seq.map (Option.map f)

Depends on / 依赖: Option.map, Seq.map
-/
def map (f : α -> β) : WSeq α -> WSeq β :=
  Seq.map (Option.map f)

/--
Definition of `ret` / `ret` 的定义

English:
definition ret
  signature: (a : α)
  body: ofList [a]

中文:
定义 ret
  签名: (a : α)
  定义体: ofList [a]

Depends on / 依赖: ofList
-/
def ret (a : α) : WSeq α :=
  ofList [a]

/--
Definition of `bind` / `bind` 的定义

English:
definition bind
  signature: (s : WSeq α) (f : α -> WSeq β)
  body: join (map f s)

中文:
定义 bind
  签名: (s : WSeq α) (f : α -> WSeq β)
  定义体: join (map f s)
-/
def bind (s : WSeq α) (f : α -> WSeq β) : WSeq β :=
  join (map f s)

/--
Instance `monad` / 实例 `monad`

English:
instance monad
  signature: : Monad WSeq where
  body: @map
  pure := @ret
  bind := @bind

中文:
实例 monad
  签名: : 单子 WSeq where
  定义体: @map
  pure := @ret
  bind := @bind
-/
instance monad : Monad WSeq where
  map := @map
  pure := @ret
  bind := @bind

open Computation

@[simp]
/--
theorem `destruct_nil` / 定理 `destruct_nil`

English:
theorem destruct_nil
  statement: destruct (nil : WSeq α) = Computation.pure none
  proof: Computation.destruct_eq_pure rfl

中文:
定理 destruct_nil
  结论: destruct (nil : WSeq α) = Computation.pure none
  证明: Computation.destruct_eq_pure rfl

Depends on / 依赖: Computation, Computation.destruct_eq_pure, destruct_eq_pure
-/
theorem destruct_nil : destruct (nil : WSeq α) = Computation.pure none :=
  Computation.destruct_eq_pure rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `destruct_cons` / 定理 `destruct_cons`

English:
theorem destruct_cons
  given: (a : α) (s)
  statement: destruct (cons a s) = Computation.pure (some (a, s))
  proof: Computation.destruct_eq_pure by simp [destruct, cons, Computation.rmap]

中文:
定理 destruct_cons
  条件: (a : α) (s)
  结论: destruct (cons a s) = Computation.pure (some (a, s))
  证明: Computation.destruct_eq_pure by simp [destruct, cons, Computation.rmap]

Depends on / 依赖: Computation, Computation.destruct_eq_pure, Computation.rmap, destruct, destruct_eq_pure
-/
theorem destruct_cons (a : α) (s) : destruct (cons a s) = Computation.pure (some (a, s)) :=
Computation.destruct_eq_pure by simp [destruct, cons, Computation.rmap]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `destruct_think` / 定理 `destruct_think`

English:
theorem destruct_think
  given: (s : WSeq α)
  statement: destruct (think s) = (destruct s).think
  proof: Computation.destruct_eq_think by simp [destruct, think, Computation.rmap]

@[simp]

中文:
定理 destruct_think
  条件: (s : WSeq α)
  结论: destruct (think s) = (destruct s).think
  证明: Computation.destruct_eq_think by simp [destruct, think, Computation.rmap]

@[simp]

Depends on / 依赖: Computation, Computation.destruct_eq_think, Computation.rmap, destruct, destruct_eq_think
-/
theorem destruct_think (s : WSeq α) : destruct (think s) = (destruct s).think :=
Computation.destruct_eq_think by simp [destruct, think, Computation.rmap]

@[simp]
/--
theorem `seq_destruct_nil` / 定理 `seq_destruct_nil`

English:
theorem seq_destruct_nil
  statement: Seq.destruct (nil : WSeq α) = none
  proof: rfl

@[simp]

中文:
定理 seq_destruct_nil
  结论: 序列.destruct (nil : WSeq α) = none
  证明: rfl

@[simp]
-/
theorem seq_destruct_nil : Seq.destruct (nil : WSeq α) = none :=
  rfl

@[simp]
/--
theorem `seq_destruct_cons` / 定理 `seq_destruct_cons`

English:
theorem seq_destruct_cons
  given: (a : α) (s)
  statement: Seq.destruct (cons a s) = some (some a, s)
  proof: Seq.destruct_cons _ _

@[simp]

中文:
定理 seq_destruct_cons
  条件: (a : α) (s)
  结论: 序列.destruct (cons a s) = some (some a, s)
  证明: Seq.destruct_cons _ _

@[simp]

Depends on / 依赖: Seq.destruct_cons, destruct_cons
-/
theorem seq_destruct_cons (a : α) (s) : Seq.destruct (cons a s) = some (some a, s) :=
  Seq.destruct_cons _ _

@[simp]
/--
theorem `seq_destruct_think` / 定理 `seq_destruct_think`

English:
theorem seq_destruct_think
  given: (s : WSeq α)
  statement: Seq.destruct (think s) = some (none, s)
  proof: Seq.destruct_cons _ _

@[simp]

中文:
定理 seq_destruct_think
  条件: (s : WSeq α)
  结论: 序列.destruct (think s) = some (none, s)
  证明: Seq.destruct_cons _ _

@[simp]

Depends on / 依赖: Seq.destruct_cons, destruct_cons
-/
theorem seq_destruct_think (s : WSeq α) : Seq.destruct (think s) = some (none, s) :=
  Seq.destruct_cons _ _

@[simp]
/--
theorem `head_nil` / 定理 `head_nil`

English:
theorem head_nil
  statement: head (nil : WSeq α) = Computation.pure none
  proof: by simp [head]

@[simp]

中文:
定理 head_nil
  结论: head (nil : WSeq α) = Computation.pure none
  证明: by simp [head]

@[simp]
-/
theorem head_nil : head (nil : WSeq α) = Computation.pure none := by simp [head]

@[simp]
/--
theorem `head_cons` / 定理 `head_cons`

English:
theorem head_cons
  given: (a : α) (s)
  statement: head (cons a s) = Computation.pure (some a)
  proof: by simp [head]

@[simp]

中文:
定理 head_cons
  条件: (a : α) (s)
  结论: head (cons a s) = Computation.pure (some a)
  证明: by simp [head]

@[simp]
-/
theorem head_cons (a : α) (s) : head (cons a s) = Computation.pure (some a) := by simp [head]

@[simp]
/--
theorem `head_think` / 定理 `head_think`

English:
theorem head_think
  given: (s : WSeq α)
  statement: head (think s) = (head s).think
  proof: by simp [head]

中文:
定理 head_think
  条件: (s : WSeq α)
  结论: head (think s) = (head s).think
  证明: by simp [head]
-/
theorem head_think (s : WSeq α) : head (think s) = (head s).think := by simp [head]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `flatten_pure` / 定理 `flatten_pure`

English:
theorem flatten_pure
  given: (s : WSeq α)
  statement: flatten (Computation.pure s) = s
  proof: by
  refine Seq.eq_of_bisim (fun s1 s2 => flatten (Computation.pure s2) = s1) ?_ rfl
  intro s' s h
  rw [← h]
  simp only [Seq.BisimO, flatten, Seq.omap, pure_def, Seq.corec_eq, destruct_pure]
  cases Seq.destruct s with
  | none => simp
  | some val =>
    obtain ⟨o, s'⟩ := val
    simp

中文:
定理 flatten_pure
  条件: (s : WSeq α)
  结论: flatten (Computation.pure s) = s
  证明: by
  refine Seq.eq_of_bisim (fun s1 s2 => flatten (Computation.pure s2) = s1) ?_ rfl
  intro s' s h
  rw [← h]
  simp only [Seq.BisimO, flatten, Seq.omap, pure_def, Seq.corec_eq, destruct_pure]
  cases Seq.destruct s with
  | none => simp
  | some val =>
    obtain ⟨o, s'⟩ := val
    simp

Depends on / 依赖: BisimO, Computation, Computation.pure, Seq.BisimO, Seq.corec_eq, Seq.destruct, Seq.eq_of_bisim, Seq.omap, corec_eq, destruct, destruct_pure, eq_of_bisim, flatten, pure_def
-/
theorem flatten_pure (s : WSeq α) : flatten (Computation.pure s) = s := by
  refine Seq.eq_of_bisim (fun s1 s2 => flatten (Computation.pure s2) = s1) ?_ rfl
  intro s' s h
  rw [← h]
  simp only [Seq.BisimO, flatten, Seq.omap, pure_def, Seq.corec_eq, destruct_pure]
  cases Seq.destruct s with
  | none => simp
  | some val =>
    obtain ⟨o, s'⟩ := val
    simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `flatten_think` / 定理 `flatten_think`

English:
theorem flatten_think
  given: (c : Computation (WSeq α))
  statement: flatten c.think = think (flatten c)
  proof: Seq.destruct_eq_cons by simp [flatten]

@[simp]

中文:
定理 flatten_think
  条件: (c : Computation (WSeq α))
  结论: flatten c.think = think (flatten c)
  证明: Seq.destruct_eq_cons by simp [flatten]

@[simp]

Depends on / 依赖: Seq.destruct_eq_cons, destruct_eq_cons, flatten
-/
theorem flatten_think (c : Computation (WSeq α)) : flatten c.think = think (flatten c) :=
Seq.destruct_eq_cons by simp [flatten]

@[simp]
/--
theorem `destruct_flatten` / 定理 `destruct_flatten`

English:
theorem destruct_flatten
  given: (c : Computation (WSeq α))
  statement: destruct (flatten c) = c >>= destruct
  proof: by
  refine
    Computation.eq_of_bisim
      (fun c1 c2 => c1 = c2 ∨ exists c, c1 = destruct (flatten c) ∧ c2 = Computation.bind c destruct) ?_
      (Or.inr ⟨c, rfl, rfl⟩)
  intro c1 c2 h
  exact
    match c1, c2, h with
    | c, _, Or.inl rfl => by cases c.destruct <;> simp
    | _, _, Or.inr ⟨c,

中文:
定理 destruct_flatten
  条件: (c : Computation (WSeq α))
  结论: destruct (flatten c) = c >>= destruct
  证明: by
  refine
    Computation.eq_of_bisim
      (fun c1 c2 => c1 = c2 ∨ exists c, c1 = destruct (flatten c) ∧ c2 = Computation.bind c destruct) ?_
      (Or.inr ⟨c, rfl, rfl⟩)
  intro c1 c2 h
  exact
    match c1, c2, h with
    | c, _, Or.inl rfl => by cases c.destruct <;> simp
    | _, _, Or.inr ⟨c,

Depends on / 依赖: Computation, Computation.bind, Computation.eq_of_bisim, Computation.recOn, Or.inl, Or.inr, c.destruct, destruct, eq_of_bisim, flatten
-/
theorem destruct_flatten (c : Computation (WSeq α)) : destruct (flatten c) = c >>= destruct := by
  refine
    Computation.eq_of_bisim
      (fun c1 c2 => c1 = c2 ∨ exists c, c1 = destruct (flatten c) ∧ c2 = Computation.bind c destruct) ?_
      (Or.inr ⟨c, rfl, rfl⟩)
  intro c1 c2 h
  exact
    match c1, c2, h with
    | c, _, Or.inl rfl => by cases c.destruct <;> simp
    | _, _, Or.inr ⟨c, rfl, rfl⟩ => by
      induction c using Computation.recOn with
      | pure a => simp; cases (destruct a).destruct <;> simp
      | think c' => simpa using Or.inr ⟨c', rfl, rfl⟩

/--
theorem `head_terminates_iff` / 定理 `head_terminates_iff`

English:
theorem head_terminates_iff
  given: (s : WSeq α)
  statement: Terminates (head s) ↔ Terminates (destruct s)
  proof: terminates_map_iff _ (destruct s)

@[simp]

中文:
定理 head_terminates_iff
  条件: (s : WSeq α)
  结论: Terminates (head s) ↔ Terminates (destruct s)
  证明: terminates_map_iff _ (destruct s)

@[simp]

Depends on / 依赖: destruct, terminates_map_iff
-/
theorem head_terminates_iff (s : WSeq α) : Terminates (head s) ↔ Terminates (destruct s) :=
  terminates_map_iff _ (destruct s)

@[simp]
/--
theorem `tail_nil` / 定理 `tail_nil`

English:
theorem tail_nil
  statement: tail (nil : WSeq α) = nil
  proof: by simp [tail]

@[simp]

中文:
定理 tail_nil
  结论: tail (nil : WSeq α) = nil
  证明: by simp [tail]

@[simp]
-/
theorem tail_nil : tail (nil : WSeq α) = nil := by simp [tail]

@[simp]
/--
theorem `tail_cons` / 定理 `tail_cons`

English:
theorem tail_cons
  given: (a : α) (s)
  statement: tail (cons a s) = s
  proof: by simp [tail]

@[simp]

中文:
定理 tail_cons
  条件: (a : α) (s)
  结论: tail (cons a s) = s
  证明: by simp [tail]

@[simp]
-/
theorem tail_cons (a : α) (s) : tail (cons a s) = s := by simp [tail]

@[simp]
/--
theorem `tail_think` / 定理 `tail_think`

English:
theorem tail_think
  given: (s : WSeq α)
  statement: tail (think s) = (tail s).think
  proof: by simp [tail]

@[simp]

中文:
定理 tail_think
  条件: (s : WSeq α)
  结论: tail (think s) = (tail s).think
  证明: by simp [tail]

@[simp]
-/
theorem tail_think (s : WSeq α) : tail (think s) = (tail s).think := by simp [tail]

@[simp]
/--
theorem `dropn_nil` / 定理 `dropn_nil`

English:
theorem dropn_nil
  given: (n)
  statement: drop (nil : WSeq α) n = nil
  proof: by induction n <;> simp [*, drop]

@[simp]

中文:
定理 dropn_nil
  条件: (n)
  结论: drop (nil : WSeq α) n = nil
  证明: by induction n <;> simp [*, drop]

@[simp]
-/
theorem dropn_nil (n) : drop (nil : WSeq α) n = nil := by induction n <;> simp [*, drop]

@[simp]
/--
theorem `dropn_cons` / 定理 `dropn_cons`

English:
theorem dropn_cons
  given: (a : α) (s) (n)
  statement: drop (cons a s) (n + 1) = drop s n
  proof: by
  induction n with
  | zero => simp [drop]
  | succ n n_ih =>
    simp [drop, ← n_ih]

@[simp]

中文:
定理 dropn_cons
  条件: (a : α) (s) (n)
  结论: drop (cons a s) (n + 1) = drop s n
  证明: by
  induction n with
  | zero => simp [drop]
  | succ n n_ih =>
    simp [drop, ← n_ih]

@[simp]

Depends on / 依赖: n_ih
-/
theorem dropn_cons (a : α) (s) (n) : drop (cons a s) (n + 1) = drop s n := by
  induction n with
  | zero => simp [drop]
  | succ n n_ih =>
    simp [drop, ← n_ih]

@[simp]
/--
theorem `dropn_think` / 定理 `dropn_think`

English:
theorem dropn_think
  given: (s : WSeq α) (n)
  statement: drop (think s) n = (drop s n).think
  proof: by
  induction n <;> simp [*, drop]

中文:
定理 dropn_think
  条件: (s : WSeq α) (n)
  结论: drop (think s) n = (drop s n).think
  证明: by
  induction n <;> simp [*, drop]
-/
theorem dropn_think (s : WSeq α) (n) : drop (think s) n = (drop s n).think := by
  induction n <;> simp [*, drop]

/--
theorem `dropn_add` / 定理 `dropn_add`

English:
theorem dropn_add
  given: (s : WSeq α) (m)
  statement: forall n, drop s (m + n) = drop (drop s m) n

中文:
定理 dropn_add
  条件: (s : WSeq α) (m)
  结论: 对任意 n, drop s (m + n) = drop (drop s m) n
-/
theorem dropn_add (s : WSeq α) (m) : forall n, drop s (m + n) = drop (drop s m) n
  | 0 => rfl
  | n + 1 => congr_arg tail (dropn_add s m n)

/--
theorem `dropn_tail` / 定理 `dropn_tail`

English:
theorem dropn_tail
  given: (s : WSeq α) (n)
  statement: drop (tail s) n = drop s (n + 1)
  proof: by
  rw [Nat.add_comm]
  symm
  apply dropn_add

中文:
定理 dropn_tail
  条件: (s : WSeq α) (n)
  结论: drop (tail s) n = drop s (n + 1)
  证明: by
  rw [Nat.add_comm]
  symm
  apply dropn_add

Depends on / 依赖: Nat.add_comm, add_comm, dropn_add
-/
theorem dropn_tail (s : WSeq α) (n) : drop (tail s) n = drop s (n + 1) := by
  rw [Nat.add_comm]
  symm
  apply dropn_add

/--
theorem `get?_add` / 定理 `get?_add`

English:
theorem get?_add
  given: (s : WSeq α) (m n)
  statement: get? s (m + n) = get? (drop s m) n
  proof: congr_arg head (dropn_add _ _ _)

中文:
定理 get?_add
  条件: (s : WSeq α) (m n)
  结论: get? s (m + n) = get? (drop s m) n
  证明: congr_arg head (dropn_add _ _ _)
-/
theorem get?_add (s : WSeq α) (m n) : get? s (m + n) = get? (drop s m) n :=
  congr_arg head (dropn_add _ _ _)

/--
theorem `get?_tail` / 定理 `get?_tail`

English:
theorem get?_tail
  given: (s : WSeq α) (n)
  statement: get? (tail s) n = get? s (n + 1)
  proof: congr_arg head (dropn_tail _ _)

@[simp]

中文:
定理 get?_tail
  条件: (s : WSeq α) (n)
  结论: get? (tail s) n = get? s (n + 1)
  证明: congr_arg head (dropn_tail _ _)

@[simp]
-/
theorem get?_tail (s : WSeq α) (n) : get? (tail s) n = get? s (n + 1) :=
  congr_arg head (dropn_tail _ _)

@[simp]
/--
theorem `join_nil` / 定理 `join_nil`

English:
theorem join_nil
  statement: join nil = (nil : WSeq α)
  proof: Seq.join_nil

中文:
定理 join_nil
  结论: join nil = (nil : WSeq α)
  证明: Seq.join_nil

Depends on / 依赖: Seq.join_nil, join_nil
-/
theorem join_nil : join nil = (nil : WSeq α) :=
  Seq.join_nil

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `join_think` / 定理 `join_think`

English:
theorem join_think
  given: (S : WSeq (WSeq α))
  statement: join (think S) = think (join S)
  proof: by
  simp only [join, think]
  dsimp only [(· <$> ·)]
  simp [Seq1.ret]

中文:
定理 join_think
  条件: (S : WSeq (WSeq α))
  结论: join (think S) = think (join S)
  证明: by
  simp only [join, think]
  dsimp only [(· <$> ·)]
  simp [Seq1.ret]

Depends on / 依赖: Seq1.ret
-/
theorem join_think (S : WSeq (WSeq α)) : join (think S) = think (join S) := by
  simp only [join, think]
  dsimp only [(· <$> ·)]
  simp [Seq1.ret]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `join_cons` / 定理 `join_cons`

English:
theorem join_cons
  given: (s : WSeq α) (S)
  statement: join (cons s S) = think (append s (join S))
  proof: by
  simp only [join, think]
  dsimp only [(· <$> ·)]
  simp [cons, append]

@[simp]

中文:
定理 join_cons
  条件: (s : WSeq α) (S)
  结论: join (cons s S) = think (append s (join S))
  证明: by
  simp only [join, think]
  dsimp only [(· <$> ·)]
  simp [cons, append]

@[simp]

Depends on / 依赖: append
-/
theorem join_cons (s : WSeq α) (S) : join (cons s S) = think (append s (join S)) := by
  simp only [join, think]
  dsimp only [(· <$> ·)]
  simp [cons, append]

@[simp]
/--
theorem `nil_append` / 定理 `nil_append`

English:
theorem nil_append
  given: (s : WSeq α)
  statement: append nil s = s
  proof: Seq.nil_append _

@[simp]

中文:
定理 nil_append
  条件: (s : WSeq α)
  结论: append nil s = s
  证明: Seq.nil_append _

@[simp]

Depends on / 依赖: Seq.nil_append, nil_append
-/
theorem nil_append (s : WSeq α) : append nil s = s :=
  Seq.nil_append _

@[simp]
/--
theorem `cons_append` / 定理 `cons_append`

English:
theorem cons_append
  given: (a : α) (s t)
  statement: append (cons a s) t = cons a (append s t)
  proof: Seq.cons_append _ _ _

@[simp]

中文:
定理 cons_append
  条件: (a : α) (s t)
  结论: append (cons a s) t = cons a (append s t)
  证明: Seq.cons_append _ _ _

@[simp]

Depends on / 依赖: Seq.cons_append, cons_append
-/
theorem cons_append (a : α) (s t) : append (cons a s) t = cons a (append s t) :=
  Seq.cons_append _ _ _

@[simp]
/--
theorem `think_append` / 定理 `think_append`

English:
theorem think_append
  given: (s t : WSeq α)
  statement: append (think s) t = think (append s t)
  proof: Seq.cons_append _ _ _

@[simp]

中文:
定理 think_append
  条件: (s t : WSeq α)
  结论: append (think s) t = think (append s t)
  证明: Seq.cons_append _ _ _

@[simp]

Depends on / 依赖: Seq.cons_append, cons_append
-/
theorem think_append (s t : WSeq α) : append (think s) t = think (append s t) :=
  Seq.cons_append _ _ _

@[simp]
/--
theorem `append_nil` / 定理 `append_nil`

English:
theorem append_nil
  given: (s : WSeq α)
  statement: append s nil = s
  proof: Seq.append_nil _

@[simp]

中文:
定理 append_nil
  条件: (s : WSeq α)
  结论: append s nil = s
  证明: Seq.append_nil _

@[simp]

Depends on / 依赖: Seq.append_nil, append_nil
-/
theorem append_nil (s : WSeq α) : append s nil = s :=
  Seq.append_nil _

@[simp]
/--
theorem `append_assoc` / 定理 `append_assoc`

English:
theorem append_assoc
  given: (s t u : WSeq α)
  statement: append (append s t) u = append s (append t u)
  proof: Seq.append_assoc _ _ _

中文:
定理 append_assoc
  条件: (s t u : WSeq α)
  结论: append (append s t) u = append s (append t u)
  证明: Seq.append_assoc _ _ _

Depends on / 依赖: Seq.append_assoc, append_assoc
-/
theorem append_assoc (s t u : WSeq α) : append (append s t) u = append s (append t u) :=
  Seq.append_assoc _ _ _

/-- auxiliary definition of tail over weak sequences -/
@[simp]
/--
Definition of `tail.aux` / `tail.aux` 的定义

English:
definition tail.aux
  signature: : Option (α × WSeq α) -> Computation (Option (α × WSeq α))

中文:
定义 tail.aux
  签名: : 选项类型 (α × WSeq α) -> Computation (选项类型 (α × WSeq α))
-/
def tail.aux : Option (α × WSeq α) -> Computation (Option (α × WSeq α))
  | none => Computation.pure none
  | some (_, s) => destruct s

/--
theorem `destruct_tail` / 定理 `destruct_tail`

English:
theorem destruct_tail
  given: (s : WSeq α)
  statement: destruct (tail s) = destruct s >>= tail.aux
  proof: by
  simp only [tail, destruct_flatten]; rw [← bind_pure_comp, LawfulMonad.bind_assoc]
  apply congr_arg; ext1 (_ | ⟨a, s⟩) <;> apply (@pure_bind Computation _ _ _ _ _ _).trans _ <;> simp

中文:
定理 destruct_tail
  条件: (s : WSeq α)
  结论: destruct (tail s) = destruct s >>= tail.aux
  证明: by
  simp only [tail, destruct_flatten]; rw [← bind_pure_comp, LawfulMonad.bind_assoc]
  apply congr_arg; ext1 (_ | ⟨a, s⟩) <;> apply (@pure_bind Computation _ _ _ _ _ _).trans _ <;> simp

Depends on / 依赖: Computation, LawfulMonad, LawfulMonad.bind_assoc, bind_assoc, bind_pure_comp, congr_arg, destruct_flatten, pure_bind
-/
theorem destruct_tail (s : WSeq α) : destruct (tail s) = destruct s >>= tail.aux := by
  simp only [tail, destruct_flatten]; rw [← bind_pure_comp, LawfulMonad.bind_assoc]
  apply congr_arg; ext1 (_ | ⟨a, s⟩) <;> apply (@pure_bind Computation _ _ _ _ _ _).trans _ <;> simp

/-- auxiliary definition of drop over weak sequences -/
@[simp]
/--
Definition of `drop.aux` / `drop.aux` 的定义

English:
definition drop.aux
  signature: : Nat -> Option (α × WSeq α) -> Computation (Option (α × WSeq α))

中文:
定义 drop.aux
  签名: : 自然数 -> 选项类型 (α × WSeq α) -> Computation (选项类型 (α × WSeq α))
-/
def drop.aux : Nat -> Option (α × WSeq α) -> Computation (Option (α × WSeq α))
  | 0 => Computation.pure
  | n + 1 => fun a => tail.aux a >>= drop.aux n

/--
theorem `drop.aux_none` / 定理 `drop.aux_none`

English:
theorem drop.aux_none
  statement: forall n, @drop.aux α n none = Computation.pure none

中文:
定理 drop.aux_none
  结论: 对任意 n, @drop.aux α n none = Computation.pure none
-/
theorem drop.aux_none : forall n, @drop.aux α n none = Computation.pure none
  | 0 => rfl
  | n + 1 =>
    show Computation.bind (Computation.pure none) (drop.aux n) = Computation.pure none by
      rw [ret_bind]; rw [drop.aux_none n]

/--
theorem `destruct_dropn` / 定理 `destruct_dropn`

English:
theorem destruct_dropn
  statement: forall (s : WSeq α) (n), destruct (drop s n) = destruct s >>= drop.aux n

中文:
定理 destruct_dropn
  结论: 对任意 (s : WSeq α) (n), destruct (drop s n) = destruct s >>= drop.aux n
-/
theorem destruct_dropn : forall (s : WSeq α) (n), destruct (drop s n) = destruct s >>= drop.aux n
  | _, 0 => (bind_pure' _).symm
  | s, n + 1 => by
    rw [← dropn_tail]; rw [destruct_dropn _ n]; rw [destruct_tail]; rw [LawfulMonad.bind_assoc]
    rfl

/--
theorem `head_terminates_of_head_tail_terminates` / 定理 `head_terminates_of_head_tail_terminates`

English:
theorem head_terminates_of_head_tail_terminates
  given: (s : WSeq α) [T : Terminates (head (tail s))]
  proof: (head_terminates_iff _).2 by
    rcases (head_terminates_iff _).1 T with ⟨⟨a, h⟩⟩
    simp? [tail] at h says simp only [tail, destruct_flatten, bind_map_left] at h
    rcases exists_of_mem_bind h with ⟨s', h1, _⟩
    exact terminates_of_mem h1

中文:
定理 head_terminates_of_head_tail_terminates
  条件: (s : WSeq α) [T : Terminates (head (tail s))]
  证明: (head_terminates_iff _).2 by
    rcases (head_terminates_iff _).1 T with ⟨⟨a, h⟩⟩
    simp? [tail] at h says simp only [tail, destruct_flatten, bind_map_left] at h
    rcases exists_of_mem_bind h with ⟨s', h1, _⟩
    exact terminates_of_mem h1

Depends on / 依赖: bind_map_left, destruct_flatten, exists_of_mem_bind, head_terminates_iff, terminates_of_mem
-/
theorem head_terminates_of_head_tail_terminates (s : WSeq α) [T : Terminates (head (tail s))] :
    Terminates (head s) :=
(head_terminates_iff _).2 by
    rcases (head_terminates_iff _).1 T with ⟨⟨a, h⟩⟩
    simp? [tail] at h says simp only [tail, destruct_flatten, bind_map_left] at h
    rcases exists_of_mem_bind h with ⟨s', h1, _⟩
    exact terminates_of_mem h1

/--
theorem `destruct_some_of_destruct_tail_some` / 定理 `destruct_some_of_destruct_tail_some`

English:
theorem destruct_some_of_destruct_tail_some
  given: {s : WSeq α} {a} (h : some a in destruct (tail s))
  proof: by
  unfold tail Functor.map at h; simp only [destruct_flatten] at h
  rcases exists_of_mem_bind h with ⟨t, tm, td⟩; clear h
  rcases Computation.exists_of_mem_map tm with ⟨t', ht', ht2⟩; clear tm
  rcases t' with - | t' <;> rw [← ht2] at td <;> simp only [destruct_nil] at td
  · have := mem_unique 

中文:
定理 destruct_some_of_destruct_tail_some
  条件: {s : WSeq α} {a} (h : some a in destruct (tail s))
  证明: by
  unfold tail Functor.map at h; simp only [destruct_flatten] at h
  rcases exists_of_mem_bind h with ⟨t, tm, td⟩; clear h
  rcases Computation.exists_of_mem_map tm with ⟨t', ht', ht2⟩; clear tm
  rcases t' with - | t' <;> rw [← ht2] at td <;> simp only [destruct_nil] at td
  · have := mem_unique 

Depends on / 依赖: Computation, Computation.exists_of_mem_map, Functor, Functor.map, destruct_flatten, destruct_nil, exists_of_mem_bind, exists_of_mem_map, mem_unique, ret_mem
-/
theorem destruct_some_of_destruct_tail_some {s : WSeq α} {a} (h : some a in destruct (tail s)) :
    exists a', some a' in destruct s := by
  unfold tail Functor.map at h; simp only [destruct_flatten] at h
  rcases exists_of_mem_bind h with ⟨t, tm, td⟩; clear h
  rcases Computation.exists_of_mem_map tm with ⟨t', ht', ht2⟩; clear tm
  rcases t' with - | t' <;> rw [← ht2] at td <;> simp only [destruct_nil] at td
  · have := mem_unique td (ret_mem _)
    contradiction
  · exact ⟨_, ht'⟩

/--
theorem `head_some_of_head_tail_some` / 定理 `head_some_of_head_tail_some`

English:
theorem head_some_of_head_tail_some
  given: {s : WSeq α} {a} (h : some a in head (tail s))
  proof: by
  unfold head at h
  rcases Computation.exists_of_mem_map h with ⟨o, md, e⟩; clear h
  rcases o with - | o <;> [injection e; injection e with h']; clear h'
  obtain ⟨a, am⟩ := destruct_some_of_destruct_tail_some md
  exact ⟨_, Computation.mem_map (@Prod.fst α (WSeq α) <$> ·) am⟩

中文:
定理 head_some_of_head_tail_some
  条件: {s : WSeq α} {a} (h : some a in head (tail s))
  证明: by
  unfold head at h
  rcases Computation.exists_of_mem_map h with ⟨o, md, e⟩; clear h
  rcases o with - | o <;> [injection e; injection e with h']; clear h'
  obtain ⟨a, am⟩ := destruct_some_of_destruct_tail_some md
  exact ⟨_, Computation.mem_map (@Prod.fst α (WSeq α) <$> ·) am⟩

Depends on / 依赖: Computation, Computation.exists_of_mem_map, Computation.mem_map, Prod.fst, destruct_some_of_destruct_tail_some, exists_of_mem_map, injection, mem_map
-/
theorem head_some_of_head_tail_some {s : WSeq α} {a} (h : some a in head (tail s)) :
    exists a', some a' in head s := by
  unfold head at h
  rcases Computation.exists_of_mem_map h with ⟨o, md, e⟩; clear h
  rcases o with - | o <;> [injection e; injection e with h']; clear h'
  obtain ⟨a, am⟩ := destruct_some_of_destruct_tail_some md
  exact ⟨_, Computation.mem_map (@Prod.fst α (WSeq α) <$> ·) am⟩

/--
theorem `head_some_of_get?_some` / 定理 `head_some_of_get?_some`

English:
theorem head_some_of_get?_some
  given: {s : WSeq α} {a n} (h : some a in get? s n)
  proof: by
  induction n generalizing a with
  | zero => exact ⟨_, h⟩
  | succ n IH =>
      let ⟨a', h'⟩ := head_some_of_head_tail_some h
      exact IH h'

中文:
定理 head_some_of_get?_some
  条件: {s : WSeq α} {a n} (h : some a in get? s n)
  证明: by
  induction n generalizing a with
  | zero => exact ⟨_, h⟩
  | succ n IH =>
      let ⟨a', h'⟩ := head_some_of_head_tail_some h
      exact IH h'

Depends on / 依赖: generalizing, head_some_of_head_tail_some
-/
theorem head_some_of_get?_some {s : WSeq α} {a n} (h : some a in get? s n) :
    exists a', some a' in head s := by
  induction n generalizing a with
  | zero => exact ⟨_, h⟩
  | succ n IH =>
      let ⟨a', h'⟩ := head_some_of_head_tail_some h
      exact IH h'

/--
theorem `get?_terminates_le` / 定理 `get?_terminates_le`

English:
theorem get?_terminates_le
  given: {s : WSeq α} {m n} (h : m <= n)
  proof: by
  induction h with
  | refl => exact id
  | step _ IH => exact fun T => IH (@head_terminates_of_head_tail_terminates _ _ T)

中文:
定理 get?_terminates_le
  条件: {s : WSeq α} {m n} (h : m <= n)
  证明: by
  induction h with
  | refl => exact id
  | step _ IH => exact fun T => IH (@head_terminates_of_head_tail_terminates _ _ T)
-/
theorem get?_terminates_le {s : WSeq α} {m n} (h : m <= n) :
    Terminates (get? s n) -> Terminates (get? s m) := by
  induction h with
  | refl => exact id
  | step _ IH => exact fun T => IH (@head_terminates_of_head_tail_terminates _ _ T)

/--
theorem `head_terminates_of_get?_terminates` / 定理 `head_terminates_of_get?_terminates`

English:
theorem head_terminates_of_get?_terminates
  given: {s : WSeq α} {n}
  proof: get?_terminates_le (Nat.zero_le n)

中文:
定理 head_terminates_of_get?_terminates
  条件: {s : WSeq α} {n}
  证明: get?_terminates_le (Nat.zero_le n)

Depends on / 依赖: Nat.zero_le, _terminates_le, zero_le
-/
theorem head_terminates_of_get?_terminates {s : WSeq α} {n} :
    Terminates (get? s n) -> Terminates (head s) :=
  get?_terminates_le (Nat.zero_le n)

/--
theorem `destruct_terminates_of_get?_terminates` / 定理 `destruct_terminates_of_get?_terminates`

English:
theorem destruct_terminates_of_get?_terminates
  given: {s : WSeq α} {n} (T : Terminates (get? s n))
  proof: (head_terminates_iff _).1 head_terminates_of_get?_terminates T

中文:
定理 destruct_terminates_of_get?_terminates
  条件: {s : WSeq α} {n} (T : Terminates (get? s n))
  证明: (head_terminates_iff _).1 head_terminates_of_get?_terminates T

Depends on / 依赖: _terminates, head_terminates_iff, head_terminates_of_get
-/
theorem destruct_terminates_of_get?_terminates {s : WSeq α} {n} (T : Terminates (get? s n)) :
    Terminates (destruct s) :=
(head_terminates_iff _).1 head_terminates_of_get?_terminates T

/--
theorem `mem_rec_on` / 定理 `mem_rec_on`

English:
theorem mem_rec_on
  statement: {C : WSeq α -> Prop} {a s} (M : a in s) (h1 : forall b s', a = b ∨ C s' -> C (cons b s'))
  proof: by
  apply Seq.mem_rec_on M
  intro o s' h; rcases o with - | b
  · apply h2
    cases h
    · contradiction
    · assumption
  · apply h1
    apply Or.imp_left _ h
    intro h
    injection h

@[simp]

中文:
定理 mem_rec_on
  结论: {C : WSeq α -> 命题} {a s} (M : a in s) (h1 : 对任意 b s', a = b ∨ C s' -> C (cons b s'))
  证明: by
  apply Seq.mem_rec_on M
  intro o s' h; rcases o with - | b
  · apply h2
    cases h
    · contradiction
    · assumption
  · apply h1
    apply Or.imp_left _ h
    intro h
    injection h

@[simp]

Depends on / 依赖: Or.imp_left, Seq.mem_rec_on, imp_left, injection, mem_rec_on
-/
theorem mem_rec_on {C : WSeq α -> Prop} {a s} (M : a in s) (h1 : forall b s', a = b ∨ C s' -> C (cons b s'))
    (h2 : forall s, C s -> C (think s)) : C s := by
  apply Seq.mem_rec_on M
  intro o s' h; rcases o with - | b
  · apply h2
    cases h
    · contradiction
    · assumption
  · apply h1
    apply Or.imp_left _ h
    intro h
    injection h

@[simp]
/--
theorem `mem_think` / 定理 `mem_think`

English:
theorem mem_think
  given: (s : WSeq α) (a)
  statement: a in think s ↔ a in s
  proof: by
  obtain ⟨f, al⟩ := s
  change (some (some a) in some none::f) ↔ some (some a) in f
  constructor <;> intro h
  · apply (Stream'.eq_or_mem_of_mem_cons h).resolve_left
    intro
    injections
  · apply Stream'.mem_cons_of_mem _ h

中文:
定理 mem_think
  条件: (s : WSeq α) (a)
  结论: a in think s ↔ a in s
  证明: by
  obtain ⟨f, al⟩ := s
  change (some (some a) in some none::f) ↔ some (some a) in f
  constructor <;> intro h
  · apply (Stream'.eq_or_mem_of_mem_cons h).resolve_left
    intro
    injections
  · apply Stream'.mem_cons_of_mem _ h

Depends on / 依赖: Stream, eq_or_mem_of_mem_cons, injections, mem_cons_of_mem, resolve_left
-/
theorem mem_think (s : WSeq α) (a) : a in think s ↔ a in s := by
  obtain ⟨f, al⟩ := s
  change (some (some a) in some none::f) ↔ some (some a) in f
  constructor <;> intro h
  · apply (Stream'.eq_or_mem_of_mem_cons h).resolve_left
    intro
    injections
  · apply Stream'.mem_cons_of_mem _ h

/--
theorem `eq_or_mem_iff_mem` / 定理 `eq_or_mem_iff_mem`

English:
theorem eq_or_mem_iff_mem
  given: {s : WSeq α} {a a' s'}
  proof: by
  generalize e : destruct s = c
  intro h
  revert s
  apply Computation.memRecOn h <;> [skip; intro c IH] <;> intro s m <;>
    induction s using WSeq.recOn <;>
    have := congr_arg Computation.destruct m
  case h1.nil | h1.think | h2.nil | h2.cons => simp at this
  case h2.think => simp at thi

中文:
定理 eq_or_mem_iff_mem
  条件: {s : WSeq α} {a a' s'}
  证明: by
  generalize e : destruct s = c
  intro h
  revert s
  apply Computation.memRecOn h <;> [skip; intro c IH] <;> intro s m <;>
    induction s using WSeq.recOn <;>
    have := congr_arg Computation.destruct m
  case h1.nil | h1.think | h2.nil | h2.cons => simp at this
  case h2.think => simp at thi

Depends on / 依赖: Computation, Computation.destruct, Computation.memRecOn, Membership, Membership.mem, Option.some.injEq, Prod.mk.injEq, Sum.inl.injEq, WSeq.Mem, WSeq.recOn, congr_arg, destruct, destruct_cons, destruct_pure, generalize, h1.cons, h1.nil, h1.think, h2.cons, h2.nil
-/
theorem eq_or_mem_iff_mem {s : WSeq α} {a a' s'} :
    some (a', s') in destruct s -> (a in s ↔ a = a' ∨ a in s') := by
  generalize e : destruct s = c
  intro h
  revert s
  apply Computation.memRecOn h <;> [skip; intro c IH] <;> intro s m <;>
    induction s using WSeq.recOn <;>
    have := congr_arg Computation.destruct m
  case h1.nil | h1.think | h2.nil | h2.cons => simp at this
  case h2.think => simp at this; simp [IH this]
  case h1.cons =>
    simp only [destruct_cons, destruct_pure, Sum.inl.injEq, Option.some.injEq,
      Prod.mk.injEq] at this
    obtain ⟨i1, i2⟩ := this
    rw [i1]; rw [i2]
    dsimp only [cons, Membership.mem, WSeq.Mem, Seq.Mem, Seq.cons]
    have h_a_eq_a' : a = a' ↔ some (some a) = some (some a') := by simp
    rw [h_a_eq_a']
    refine ⟨Stream'.eq_or_mem_of_mem_cons, fun o => ?_⟩
    rcases o with e | m
    · rw [e]
      apply Stream'.mem_cons
    · exact Stream'.mem_cons_of_mem _ m

@[simp]
/--
theorem `mem_cons_iff` / 定理 `mem_cons_iff`

English:
theorem mem_cons_iff
  given: (s : WSeq α) (b) {a}
  statement: a in cons b s ↔ a = b ∨ a in s
  proof: eq_or_mem_iff_mem by simp

中文:
定理 mem_cons_iff
  条件: (s : WSeq α) (b) {a}
  结论: a in cons b s ↔ a = b ∨ a in s
  证明: eq_or_mem_iff_mem by simp

Depends on / 依赖: eq_or_mem_iff_mem
-/
theorem mem_cons_iff (s : WSeq α) (b) {a} : a in cons b s ↔ a = b ∨ a in s :=
eq_or_mem_iff_mem by simp

/--
theorem `mem_cons_of_mem` / 定理 `mem_cons_of_mem`

English:
theorem mem_cons_of_mem
  given: {s : WSeq α} (b) {a} (h : a in s)
  statement: a in cons b s
  proof: (mem_cons_iff _ _).2 (Or.inr h)

中文:
定理 mem_cons_of_mem
  条件: {s : WSeq α} (b) {a} (h : a in s)
  结论: a in cons b s
  证明: (mem_cons_iff _ _).2 (Or.inr h)

Depends on / 依赖: Or.inr, mem_cons_iff
-/
theorem mem_cons_of_mem {s : WSeq α} (b) {a} (h : a in s) : a in cons b s :=
  (mem_cons_iff _ _).2 (Or.inr h)

/--
theorem `mem_cons` / 定理 `mem_cons`

English:
theorem mem_cons
  given: (s : WSeq α) (a)
  statement: a in cons a s
  proof: (mem_cons_iff _ _).2 (Or.inl rfl)

中文:
定理 mem_cons
  条件: (s : WSeq α) (a)
  结论: a in cons a s
  证明: (mem_cons_iff _ _).2 (Or.inl rfl)

Depends on / 依赖: Or.inl, mem_cons_iff
-/
theorem mem_cons (s : WSeq α) (a) : a in cons a s :=
  (mem_cons_iff _ _).2 (Or.inl rfl)

/--
theorem `mem_of_mem_tail` / 定理 `mem_of_mem_tail`

English:
theorem mem_of_mem_tail
  given: {s : WSeq α} {a} (h : a in tail s)
  statement: a in s
  proof: by
  have ⟨n, e⟩ := h
  revert s
  induction n <;> intro s m e <;> induction s using WSeq.recOn
  case zero.nil | succ.nil => simpa using m
.mpr Or.inr (by simpa using m) case zero.cons | succ.cons => exact WSeq.mem_cons_iff ..
  case zero.think => injections
  case succ.think n IH s =>
    simp onl

中文:
定理 mem_of_mem_tail
  条件: {s : WSeq α} {a} (h : a in tail s)
  结论: a in s
  证明: by
  have ⟨n, e⟩ := h
  revert s
  induction n <;> intro s m e <;> induction s using WSeq.recOn
  case zero.nil | succ.nil => simpa using m
.mpr Or.inr (by simpa using m) case zero.cons | succ.cons => exact WSeq.mem_cons_iff ..
  case zero.think => injections
  case succ.think n IH s =>
    simp onl

Depends on / 依赖: Or.inr, WSeq.mem_cons_iff, WSeq.recOn, injections, mem_cons_iff, mem_think, revert, succ.cons, succ.nil, succ.think, tail_think, zero.cons, zero.nil, zero.think
-/
theorem mem_of_mem_tail {s : WSeq α} {a} (h : a in tail s) : a in s := by
  have ⟨n, e⟩ := h
  revert s
  induction n <;> intro s m e <;> induction s using WSeq.recOn
  case zero.nil | succ.nil => simpa using m
.mpr Or.inr (by simpa using m) case zero.cons | succ.cons => exact WSeq.mem_cons_iff ..
  case zero.think => injections
  case succ.think n IH s =>
    simp only [tail_think, mem_think] at m e ⊢
    apply IH m
    rw [e]
    cases tail s
    rfl

/--
theorem `mem_of_mem_dropn` / 定理 `mem_of_mem_dropn`

English:
theorem mem_of_mem_dropn
  given: {s : WSeq α} {a}
  statement: forall {n}, a in drop s n -> a in s

中文:
定理 mem_of_mem_dropn
  条件: {s : WSeq α} {a}
  结论: 对任意 {n}, a in drop s n -> a in s
-/
theorem mem_of_mem_dropn {s : WSeq α} {a} : forall {n}, a in drop s n -> a in s
  | 0, h => h
  | n + 1, h => @mem_of_mem_dropn s a n (mem_of_mem_tail h)

/--
theorem `get?_mem` / 定理 `get?_mem`

English:
theorem get?_mem
  given: {s : WSeq α} {a n}
  statement: some a in get? s n -> a in s
  proof: by
  induction n generalizing s <;> intro h
  case zero =>
    rcases Computation.exists_of_mem_map h with ⟨o, h1, h2⟩
    rcases o with - | o
    · injection h2
    injection h2 with h'
    obtain ⟨a', s'⟩ := o
    exact (eq_or_mem_iff_mem h1).2 (Or.inl h'.symm)
  case succ n IH =>
    have := @IH 

中文:
定理 get?_mem
  条件: {s : WSeq α} {a n}
  结论: some a in get? s n -> a in s
  证明: by
  induction n generalizing s <;> intro h
  case zero =>
    rcases Computation.exists_of_mem_map h with ⟨o, h1, h2⟩
    rcases o with - | o
    · injection h2
    injection h2 with h'
    obtain ⟨a', s'⟩ := o
    exact (eq_or_mem_iff_mem h1).2 (Or.inl h'.symm)
  case succ n IH =>
    have := @IH 
-/
theorem get?_mem {s : WSeq α} {a n} : some a in get? s n -> a in s := by
  induction n generalizing s <;> intro h
  case zero =>
    rcases Computation.exists_of_mem_map h with ⟨o, h1, h2⟩
    rcases o with - | o
    · injection h2
    injection h2 with h'
    obtain ⟨a', s'⟩ := o
    exact (eq_or_mem_iff_mem h1).2 (Or.inl h'.symm)
  case succ n IH =>
    have := @IH (tail s)
    rw [get?_tail] at this
    exact mem_of_mem_tail (this h)

/--
theorem `exists_get?_of_mem` / 定理 `exists_get?_of_mem`

English:
theorem exists_get?_of_mem
  given: {s : WSeq α} {a} (h : a in s)
  statement: exists n, some a in get? s n
  proof: by
  apply mem_rec_on h
  · intro a' s' h
    rcases h with h | h
    · exists 0
      simp only [get?, drop, head_cons]
      rw [h]
      apply ret_mem
    · obtain ⟨n, h⟩ := h
      exists n + 1
      simpa [get?]
  · intro s' h
    obtain ⟨n, h⟩ := h
    exists n
    simp only [get?, dropn_think

中文:
定理 存在_get?_of_mem
  条件: {s : WSeq α} {a} (h : a in s)
  结论: 存在 n, some a in get? s n
  证明: by
  apply mem_rec_on h
  · intro a' s' h
    rcases h with h | h
    · exists 0
      simp only [get?, drop, head_cons]
      rw [h]
      apply ret_mem
    · obtain ⟨n, h⟩ := h
      exists n + 1
      simpa [get?]
  · intro s' h
    obtain ⟨n, h⟩ := h
    exists n
    simp only [get?, dropn_think

Depends on / 依赖: dropn_think, head_cons, head_think, mem_rec_on, ret_mem, think_mem
-/
theorem exists_get?_of_mem {s : WSeq α} {a} (h : a in s) : exists n, some a in get? s n := by
  apply mem_rec_on h
  · intro a' s' h
    rcases h with h | h
    · exists 0
      simp only [get?, drop, head_cons]
      rw [h]
      apply ret_mem
    · obtain ⟨n, h⟩ := h
      exists n + 1
      simpa [get?]
  · intro s' h
    obtain ⟨n, h⟩ := h
    exists n
    simp only [get?, dropn_think, head_think]
    apply think_mem h

/--
theorem `exists_dropn_of_mem` / 定理 `exists_dropn_of_mem`

English:
theorem exists_dropn_of_mem
  given: {s : WSeq α} {a} (h : a in s)
  proof: let ⟨n, h⟩ := exists_get?_of_mem h
  ⟨n, by
    rcases (head_terminates_iff _).1 ⟨⟨_, h⟩⟩ with ⟨⟨o, om⟩⟩
    have := Computation.mem_unique (Computation.mem_map _ om) h
    rcases o with - | o
    · injection this
    injection this with i
    obtain ⟨a', s'⟩ := o
    dsimp at i
    rw [i] at om
   

中文:
定理 存在_dropn_of_mem
  条件: {s : WSeq α} {a} (h : a in s)
  证明: let ⟨n, h⟩ := exists_get?_of_mem h
  ⟨n, by
    rcases (head_terminates_iff _).1 ⟨⟨_, h⟩⟩ with ⟨⟨o, om⟩⟩
    have := Computation.mem_unique (Computation.mem_map _ om) h
    rcases o with - | o
    · injection this
    injection this with i
    obtain ⟨a', s'⟩ := o
    dsimp at i
    rw [i] at om
   

Depends on / 依赖: Computation, Computation.mem_map, Computation.mem_unique, _of_mem, exists_get, head_terminates_iff, injection, mem_map, mem_unique
-/
theorem exists_dropn_of_mem {s : WSeq α} {a} (h : a in s) :
    exists n s', some (a, s') in destruct (drop s n) :=
  let ⟨n, h⟩ := exists_get?_of_mem h
  ⟨n, by
    rcases (head_terminates_iff _).1 ⟨⟨_, h⟩⟩ with ⟨⟨o, om⟩⟩
    have := Computation.mem_unique (Computation.mem_map _ om) h
    rcases o with - | o
    · injection this
    injection this with i
    obtain ⟨a', s'⟩ := o
    dsimp at i
    rw [i] at om
    exact ⟨_, om⟩⟩

/--
theorem `head_terminates_of_mem` / 定理 `head_terminates_of_mem`

English:
theorem head_terminates_of_mem
  given: {s : WSeq α} {a} (h : a in s)
  statement: Terminates (head s)
  proof: let ⟨_, h⟩ := exists_get?_of_mem h
  head_terminates_of_get?_terminates ⟨⟨_, h⟩⟩

中文:
定理 head_terminates_of_mem
  条件: {s : WSeq α} {a} (h : a in s)
  结论: Terminates (head s)
  证明: let ⟨_, h⟩ := exists_get?_of_mem h
  head_terminates_of_get?_terminates ⟨⟨_, h⟩⟩

Depends on / 依赖: _of_mem, _terminates, exists_get, head_terminates_of_get
-/
theorem head_terminates_of_mem {s : WSeq α} {a} (h : a in s) : Terminates (head s) :=
  let ⟨_, h⟩ := exists_get?_of_mem h
  head_terminates_of_get?_terminates ⟨⟨_, h⟩⟩

/--
theorem `of_mem_append` / 定理 `of_mem_append`

English:
theorem of_mem_append
  given: {s₁ s₂ : WSeq α} {a : α}
  statement: a in append s₁ s₂ -> a in s₁ ∨ a in s₂
  proof: Seq.of_mem_append

中文:
定理 of_mem_append
  条件: {s₁ s₂ : WSeq α} {a : α}
  结论: a in append s₁ s₂ -> a in s₁ ∨ a in s₂
  证明: Seq.of_mem_append

Depends on / 依赖: Seq.of_mem_append, of_mem_append
-/
theorem of_mem_append {s₁ s₂ : WSeq α} {a : α} : a in append s₁ s₂ -> a in s₁ ∨ a in s₂ :=
  Seq.of_mem_append

/--
theorem `mem_append_left` / 定理 `mem_append_left`

English:
theorem mem_append_left
  given: {s₁ s₂ : WSeq α} {a : α}
  statement: a in s₁ -> a in append s₁ s₂
  proof: Seq.mem_append_left

中文:
定理 mem_append_left
  条件: {s₁ s₂ : WSeq α} {a : α}
  结论: a in s₁ -> a in append s₁ s₂
  证明: Seq.mem_append_left

Depends on / 依赖: Seq.mem_append_left, mem_append_left
-/
theorem mem_append_left {s₁ s₂ : WSeq α} {a : α} : a in s₁ -> a in append s₁ s₂ :=
  Seq.mem_append_left

/--
theorem `exists_of_mem_map` / 定理 `exists_of_mem_map`

English:
theorem exists_of_mem_map
  given: {f} {b : β}
  statement: forall {s : WSeq α}, b in map f s -> exists a, a in s ∧ f a = b
  proof: Seq.exists_of_mem_map h
    rcases o with - | a
    · injection oe
    injection oe with h'
    exact ⟨a, om, h'⟩

@[simp]

中文:
定理 存在_of_mem_map
  条件: {f} {b : β}
  结论: 对任意 {s : WSeq α}, b in map f s -> 存在 a, a in s ∧ f a = b
  证明: Seq.exists_of_mem_map h
    rcases o with - | a
    · injection oe
    injection oe with h'
    exact ⟨a, om, h'⟩

@[simp]

Depends on / 依赖: Seq.exists_of_mem_map, exists_of_mem_map
-/
theorem exists_of_mem_map {f} {b : β} : forall {s : WSeq α}, b in map f s -> exists a, a in s ∧ f a = b
  | ⟨g, al⟩, h => by
    let ⟨o, om, oe⟩ := Seq.exists_of_mem_map h
    rcases o with - | a
    · injection oe
    injection oe with h'
    exact ⟨a, om, h'⟩

@[simp]
/--
theorem `ofList_nil` / 定理 `ofList_nil`

English:
theorem ofList_nil
  statement: ofList [] = (nil : WSeq α)
  proof: rfl

@[simp]

中文:
定理 ofList_nil
  结论: ofList [] = (nil : WSeq α)
  证明: rfl

@[simp]
-/
theorem ofList_nil : ofList [] = (nil : WSeq α) :=
  rfl

@[simp]
/--
theorem `ofList_cons` / 定理 `ofList_cons`

English:
theorem ofList_cons
  given: (a : α) (l)
  statement: ofList (a::l) = cons a (ofList l)
  proof: show Seq.map some (Seq.ofList (a::l)) = Seq.cons (some a) (Seq.map some (Seq.ofList l)) by simp

@[simp]

中文:
定理 ofList_cons
  条件: (a : α) (l)
  结论: ofList (a::l) = cons a (ofList l)
  证明: show Seq.map some (Seq.ofList (a::l)) = Seq.cons (some a) (Seq.map some (Seq.ofList l)) by simp

@[simp]

Depends on / 依赖: Seq.cons, Seq.map, Seq.ofList, ofList
-/
theorem ofList_cons (a : α) (l) : ofList (a::l) = cons a (ofList l) :=
  show Seq.map some (Seq.ofList (a::l)) = Seq.cons (some a) (Seq.map some (Seq.ofList l)) by simp

@[simp]
/--
theorem `toList'_nil` / 定理 `toList'_nil`

English:
theorem toList'_nil
  given: (l : List α)
  proof: destruct_eq_pure rfl

中文:
定理 toList'_nil
  条件: (l : 列表 α)
  证明: destruct_eq_pure rfl

Depends on / 依赖: destruct_eq_pure
-/
theorem toList'_nil (l : List α) :
    Computation.corec (fun ⟨l, s⟩ =>
      match Seq.destruct s with
      | none => Sum.inl l.reverse
      | some (none, s') => Sum.inr (l, s')
      | some (some a, s') => Sum.inr (a::l, s')) (l, nil) = Computation.pure l.reverse :=
  destruct_eq_pure rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `toList'_cons` / 定理 `toList'_cons`

English:
theorem toList'_cons
  given: (l : List α) (s : WSeq α) (a : α)
  proof: destruct_eq_think by simp [cons]

中文:
定理 toList'_cons
  条件: (l : 列表 α) (s : WSeq α) (a : α)
  证明: destruct_eq_think by simp [cons]
-/
theorem toList'_cons (l : List α) (s : WSeq α) (a : α) :
    Computation.corec (fun ⟨l, s⟩ =>
      match Seq.destruct s with
      | none => Sum.inl l.reverse
      | some (none, s') => Sum.inr (l, s')
      | some (some a, s') => Sum.inr (a::l, s')) (l, cons a s) =
      (Computation.corec (fun ⟨l, s⟩ =>
        match Seq.destruct s with
        | none => Sum.inl l.reverse
        | some (none, s') => Sum.inr (l, s')
        | some (some a, s') => Sum.inr (a::l, s')) (a::l, s)).think :=
destruct_eq_think by simp [cons]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `toList'_think` / 定理 `toList'_think`

English:
theorem toList'_think
  given: (l : List α) (s : WSeq α)
  proof: destruct_eq_think by simp [think]

中文:
定理 toList'_think
  条件: (l : 列表 α) (s : WSeq α)
  证明: destruct_eq_think by simp [think]
-/
theorem toList'_think (l : List α) (s : WSeq α) :
    Computation.corec (fun ⟨l, s⟩ =>
      match Seq.destruct s with
      | none => Sum.inl l.reverse
      | some (none, s') => Sum.inr (l, s')
      | some (some a, s') => Sum.inr (a::l, s')) (l, think s) =
      (Computation.corec (fun ⟨l, s⟩ =>
        match Seq.destruct s with
        | none => Sum.inl l.reverse
        | some (none, s') => Sum.inr (l, s')
        | some (some a, s') => Sum.inr (a::l, s')) (l, s)).think :=
destruct_eq_think by simp [think]

/--
theorem `toList'_map` / 定理 `toList'_map`

English:
theorem toList'_map
  given: (l : List α) (s : WSeq α)
  proof: by
  refine
    Computation.eq_of_bisim
      (fun c1 c2 =>
        exists (l' : List α) (s : WSeq α),
          c1 = Computation.corec (fun ⟨l, s⟩ =>
            match Seq.destruct s with
            | none => Sum.inl l.reverse
            | some (none, s') => Sum.inr (l, s')
            | some (so

中文:
定理 toList'_map
  条件: (l : 列表 α) (s : WSeq α)
  证明: by
  refine
    Computation.eq_of_bisim
      (fun c1 c2 =>
        exists (l' : List α) (s : WSeq α),
          c1 = Computation.corec (fun ⟨l, s⟩ =>
            match Seq.destruct s with
            | none => Sum.inl l.reverse
            | some (none, s') => Sum.inr (l, s')
            | some (so
-/
theorem toList'_map (l : List α) (s : WSeq α) :
    Computation.corec (fun ⟨l, s⟩ =>
      match Seq.destruct s with
      | none => Sum.inl l.reverse
      | some (none, s') => Sum.inr (l, s')
      | some (some a, s') => Sum.inr (a :: l, s')) (l, s) = (l.reverse ++ ·) <$> toList s := by
  refine
    Computation.eq_of_bisim
      (fun c1 c2 =>
        exists (l' : List α) (s : WSeq α),
          c1 = Computation.corec (fun ⟨l, s⟩ =>
            match Seq.destruct s with
            | none => Sum.inl l.reverse
            | some (none, s') => Sum.inr (l, s')
            | some (some a, s') => Sum.inr (a::l, s')) (l' ++ l, s) ∧
            c2 = Computation.map (l.reverse ++ ·) (Computation.corec (fun ⟨l, s⟩ =>
              match Seq.destruct s with
              | none => Sum.inl l.reverse
              | some (none, s') => Sum.inr (l, s')
              | some (some a, s') => Sum.inr (a::l, s')) (l', s)))
      ?_ ⟨[], s, rfl, rfl⟩
  intro s1 s2 h; rcases h with ⟨l', s, h⟩; rw [h.left, h.right]
  induction s using WSeq.recOn
  case nil => simp
  case cons a s => refine ⟨a :: l', s, ?_, ?_⟩ <;> simp
  case think s => refine ⟨l', s, ?_, ?_⟩ <;> simp

@[simp]
/--
theorem `toList_cons` / 定理 `toList_cons`

English:
theorem toList_cons
  given: (a : α) (s)
  statement: toList (cons a s) = (List.cons a <$> toList s).think
  proof: destruct_eq_think by
    unfold toList
    simp only [toList'_cons, Computation.destruct_think, Sum.inr.injEq]
    rw [toList'_map]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
    rfl

@[simp]

中文:
定理 toList_cons
  条件: (a : α) (s)
  结论: toList (cons a s) = (列表.cons a <$> toList s).think
  证明: destruct_eq_think by
    unfold toList
    simp only [toList'_cons, Computation.destruct_think, Sum.inr.injEq]
    rw [toList'_map]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
    rfl

@[simp]

Depends on / 依赖: Computation, Computation.destruct_think, List.nil_append, List.reverse_cons, List.reverse_nil, List.singleton_append, Sum.inr.injEq, _cons, _map, destruct_eq_think, destruct_think, nil_append, reverse_cons, reverse_nil, singleton_append, toList
-/
theorem toList_cons (a : α) (s) : toList (cons a s) = (List.cons a <$> toList s).think :=
destruct_eq_think by
    unfold toList
    simp only [toList'_cons, Computation.destruct_think, Sum.inr.injEq]
    rw [toList'_map]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
    rfl

@[simp]
/--
theorem `toList_nil` / 定理 `toList_nil`

English:
theorem toList_nil
  statement: toList (nil : WSeq α) = Computation.pure []
  proof: destruct_eq_pure rfl

中文:
定理 toList_nil
  结论: toList (nil : WSeq α) = Computation.pure []
  证明: destruct_eq_pure rfl

Depends on / 依赖: destruct_eq_pure
-/
theorem toList_nil : toList (nil : WSeq α) = Computation.pure [] :=
  destruct_eq_pure rfl

/--
theorem `toList_ofList` / 定理 `toList_ofList`

English:
theorem toList_ofList
  given: (l : List α)
  statement: l in toList (ofList l)
  proof: by
  induction l with
  | nil => simp
  | cons a l IH => simpa [ret_mem] using! think_mem (Computation.mem_map _ IH)

中文:
定理 toList_ofList
  条件: (l : 列表 α)
  结论: l in toList (ofList l)
  证明: by
  induction l with
  | nil => simp
  | cons a l IH => simpa [ret_mem] using! think_mem (Computation.mem_map _ IH)

Depends on / 依赖: Computation, Computation.mem_map, mem_map, ret_mem, think_mem
-/
theorem toList_ofList (l : List α) : l in toList (ofList l) := by
  induction l with
  | nil => simp
  | cons a l IH => simpa [ret_mem] using! think_mem (Computation.mem_map _ IH)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `destruct_ofSeq` / 定理 `destruct_ofSeq`

English:
theorem destruct_ofSeq
  given: (s : Seq α)
  proof: destruct_eq_pure by
    simp only [destruct, Seq.destruct, Option.map_eq_map, ofSeq, Computation.corec_eq, rmap,
      Seq.head]
    rw [show Seq.get? (some <$> s) 0 = some <$> Seq.get? s 0 by apply Seq.map_get?]
    rcases Seq.get? s 0 with - | a
    · rfl
    dsimp only [(· <$> ·)]
    simp

@[sim

中文:
定理 destruct_ofSeq
  条件: (s : 序列 α)
  证明: destruct_eq_pure by
    simp only [destruct, Seq.destruct, Option.map_eq_map, ofSeq, Computation.corec_eq, rmap,
      Seq.head]
    rw [show Seq.get? (some <$> s) 0 = some <$> Seq.get? s 0 by apply Seq.map_get?]
    rcases Seq.get? s 0 with - | a
    · rfl
    dsimp only [(· <$> ·)]
    simp

@[sim

Depends on / 依赖: Computation, Computation.corec_eq, Option.map_eq_map, Seq.destruct, Seq.get, Seq.head, Seq.map_get, corec_eq, destruct, destruct_eq_pure, map_eq_map, map_get
-/
theorem destruct_ofSeq (s : Seq α) :
    destruct (ofSeq s) = Computation.pure (s.head.map fun a => (a, ofSeq s.tail)) :=
destruct_eq_pure by
    simp only [destruct, Seq.destruct, Option.map_eq_map, ofSeq, Computation.corec_eq, rmap,
      Seq.head]
    rw [show Seq.get? (some <$> s) 0 = some <$> Seq.get? s 0 by apply Seq.map_get?]
    rcases Seq.get? s 0 with - | a
    · rfl
    dsimp only [(· <$> ·)]
    simp

@[simp]
/--
theorem `head_ofSeq` / 定理 `head_ofSeq`

English:
theorem head_ofSeq
  given: (s : Seq α)
  statement: head (ofSeq s) = Computation.pure s.head
  proof: by
  simp only [head, Option.map_eq_map, destruct_ofSeq, Computation.map_pure, Option.map_map]
  cases Seq.head s <;> rfl

中文:
定理 head_ofSeq
  条件: (s : 序列 α)
  结论: head (ofSeq s) = Computation.pure s.head
  证明: by
  simp only [head, Option.map_eq_map, destruct_ofSeq, Computation.map_pure, Option.map_map]
  cases Seq.head s <;> rfl

Depends on / 依赖: Computation, Computation.map_pure, Option.map_eq_map, Option.map_map, Seq.head, destruct_ofSeq, map_eq_map, map_map, map_pure
-/
theorem head_ofSeq (s : Seq α) : head (ofSeq s) = Computation.pure s.head := by
  simp only [head, Option.map_eq_map, destruct_ofSeq, Computation.map_pure, Option.map_map]
  cases Seq.head s <;> rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `tail_ofSeq` / 定理 `tail_ofSeq`

English:
theorem tail_ofSeq
  given: (s : Seq α)
  statement: tail (ofSeq s) = ofSeq s.tail
  proof: by
  simp only [tail, destruct_ofSeq, map_pure', flatten_pure]
  induction s using Seq.recOn <;> simp only [ofSeq, Seq.tail_nil, Seq.head_nil,
    Option.map_none, Seq.tail_cons, Seq.head_cons, Option.map_some]
  · rfl

@[simp]

中文:
定理 tail_ofSeq
  条件: (s : 序列 α)
  结论: tail (ofSeq s) = ofSeq s.tail
  证明: by
  simp only [tail, destruct_ofSeq, map_pure', flatten_pure]
  induction s using Seq.recOn <;> simp only [ofSeq, Seq.tail_nil, Seq.head_nil,
    Option.map_none, Seq.tail_cons, Seq.head_cons, Option.map_some]
  · rfl

@[simp]

Depends on / 依赖: Option.map_none, Option.map_some, Seq.head_cons, Seq.head_nil, Seq.recOn, Seq.tail_cons, Seq.tail_nil, destruct_ofSeq, flatten_pure, head_cons, head_nil, map_none, map_pure, map_some, tail_cons, tail_nil
-/
theorem tail_ofSeq (s : Seq α) : tail (ofSeq s) = ofSeq s.tail := by
  simp only [tail, destruct_ofSeq, map_pure', flatten_pure]
  induction s using Seq.recOn <;> simp only [ofSeq, Seq.tail_nil, Seq.head_nil,
    Option.map_none, Seq.tail_cons, Seq.head_cons, Option.map_some]
  · rfl

@[simp]
/--
theorem `dropn_ofSeq` / 定理 `dropn_ofSeq`

English:
theorem dropn_ofSeq
  given: (s : Seq α)
  statement: forall n, drop (ofSeq s) n = ofSeq (s.drop n)

中文:
定理 dropn_ofSeq
  条件: (s : 序列 α)
  结论: 对任意 n, drop (ofSeq s) n = ofSeq (s.drop n)
-/
theorem dropn_ofSeq (s : Seq α) : forall n, drop (ofSeq s) n = ofSeq (s.drop n)
  | 0 => rfl
  | n + 1 => by
    simp only [drop, Seq.drop]
    rw [dropn_ofSeq s n]; rw [tail_ofSeq]

/--
theorem `get?_ofSeq` / 定理 `get?_ofSeq`

English:
theorem get?_ofSeq
  given: (s : Seq α) (n)
  statement: get? (ofSeq s) n = Computation.pure (Seq.get? s n)
  proof: by
  dsimp [get?]; rw [dropn_ofSeq, head_ofSeq, Seq.head_dropn]

@[simp]

中文:
定理 get?_ofSeq
  条件: (s : 序列 α) (n)
  结论: get? (ofSeq s) n = Computation.pure (序列.get? s n)
  证明: by
  dsimp [get?]; rw [dropn_ofSeq, head_ofSeq, Seq.head_dropn]

@[simp]
-/
theorem get?_ofSeq (s : Seq α) (n) : get? (ofSeq s) n = Computation.pure (Seq.get? s n) := by
  dsimp [get?]; rw [dropn_ofSeq, head_ofSeq, Seq.head_dropn]

@[simp]
/--
theorem `map_nil` / 定理 `map_nil`

English:
theorem map_nil
  given: (f : α -> β)
  statement: map f nil = nil
  proof: rfl

@[simp]

中文:
定理 map_nil
  条件: (f : α -> β)
  结论: map f nil = nil
  证明: rfl

@[simp]
-/
theorem map_nil (f : α -> β) : map f nil = nil :=
  rfl

@[simp]
/--
theorem `map_cons` / 定理 `map_cons`

English:
theorem map_cons
  given: (f : α -> β) (a s)
  statement: map f (cons a s) = cons (f a) (map f s)
  proof: Seq.map_cons _ _ _

@[simp]

中文:
定理 map_cons
  条件: (f : α -> β) (a s)
  结论: map f (cons a s) = cons (f a) (map f s)
  证明: Seq.map_cons _ _ _

@[simp]

Depends on / 依赖: Seq.map_cons, map_cons
-/
theorem map_cons (f : α -> β) (a s) : map f (cons a s) = cons (f a) (map f s) :=
  Seq.map_cons _ _ _

@[simp]
/--
theorem `map_think` / 定理 `map_think`

English:
theorem map_think
  given: (f : α -> β) (s)
  statement: map f (think s) = think (map f s)
  proof: Seq.map_cons _ _ _

中文:
定理 map_think
  条件: (f : α -> β) (s)
  结论: map f (think s) = think (map f s)
  证明: Seq.map_cons _ _ _

Depends on / 依赖: Seq.map_cons, map_cons
-/
theorem map_think (f : α -> β) (s) : map f (think s) = think (map f s) :=
  Seq.map_cons _ _ _

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  given: (s : WSeq α)
  statement: map id s = s
  proof: by simp [map]

@[simp]

中文:
定理 map_id
  条件: (s : WSeq α)
  结论: map id s = s
  证明: by simp [map]

@[simp]
-/
theorem map_id (s : WSeq α) : map id s = s := by simp [map]

@[simp]
/--
theorem `map_ret` / 定理 `map_ret`

English:
theorem map_ret
  given: (f : α -> β) (a)
  statement: map f (ret a) = ret (f a)
  proof: by simp [ret]

@[simp]

中文:
定理 map_ret
  条件: (f : α -> β) (a)
  结论: map f (ret a) = ret (f a)
  证明: by simp [ret]

@[simp]
-/
theorem map_ret (f : α -> β) (a) : map f (ret a) = ret (f a) := by simp [ret]

@[simp]
/--
theorem `map_append` / 定理 `map_append`

English:
theorem map_append
  given: (f : α -> β) (s t)
  statement: map f (append s t) = append (map f s) (map f t)
  proof: Seq.map_append _ _ _

中文:
定理 map_append
  条件: (f : α -> β) (s t)
  结论: map f (append s t) = append (map f s) (map f t)
  证明: Seq.map_append _ _ _

Depends on / 依赖: Seq.map_append, map_append
-/
theorem map_append (f : α -> β) (s t) : map f (append s t) = append (map f s) (map f t) :=
  Seq.map_append _ _ _

set_option backward.isDefEq.respectTransparency false in
/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  given: (f : α -> β) (g : β -> γ) (s : WSeq α)
  statement: map (g ∘ f) s = map g (map f s)
  proof: by
  dsimp [map]; rw [← Seq.map_comp]
  apply congr_fun; apply congr_arg
  ext ⟨⟩ <;> rfl

中文:
定理 map_comp
  条件: (f : α -> β) (g : β -> γ) (s : WSeq α)
  结论: map (g ∘ f) s = map g (map f s)
  证明: by
  dsimp [map]; rw [← Seq.map_comp]
  apply congr_fun; apply congr_arg
  ext ⟨⟩ <;> rfl

Depends on / 依赖: Seq.map_comp, congr_arg, congr_fun, map_comp
-/
theorem map_comp (f : α -> β) (g : β -> γ) (s : WSeq α) : map (g ∘ f) s = map g (map f s) := by
  dsimp [map]; rw [← Seq.map_comp]
  apply congr_fun; apply congr_arg
  ext ⟨⟩ <;> rfl

/--
theorem `mem_map` / 定理 `mem_map`

English:
theorem mem_map
  given: (f : α -> β) {a : α} {s : WSeq α}
  statement: a in s -> f a in map f s
  proof: Seq.mem_map (Option.map f)

中文:
定理 mem_map
  条件: (f : α -> β) {a : α} {s : WSeq α}
  结论: a in s -> f a in map f s
  证明: Seq.mem_map (Option.map f)

Depends on / 依赖: Option.map, Seq.mem_map, mem_map
-/
theorem mem_map (f : α -> β) {a : α} {s : WSeq α} : a in s -> f a in map f s :=
  Seq.mem_map (Option.map f)

set_option backward.isDefEq.respectTransparency false in
-- The converse is not true without additional assumptions
/--
theorem `exists_of_mem_join` / 定理 `exists_of_mem_join`

English:
theorem exists_of_mem_join
  given: {a : α}
  statement: forall {S : WSeq (WSeq α)}, a in join S -> exists s, s in S ∧ a in s
  proof: by
  suffices
    forall ss : WSeq α,
      a in ss -> forall s S, append s (join S) = ss -> a in append s (join S) -> a in s ∨ exists s, s in S ∧ a in s
    from fun S h => (this _ h nil S (by simp) (by simp [h])).resolve_left (notMem_nil _)
  intro ss h
  apply mem_rec_on h
  · intro b ss o s S ej

中文:
定理 存在_of_mem_join
  条件: {a : α}
  结论: 对任意 {S : WSeq (WSeq α)}, a in join S -> 存在 s, s in S ∧ a in s
  证明: by
  suffices
    forall ss : WSeq α,
      a in ss -> forall s S, append s (join S) = ss -> a in append s (join S) -> a in s ∨ exists s, s in S ∧ a in s
    from fun S h => (this _ h nil S (by simp) (by simp [h])).resolve_left (notMem_nil _)
  intro ss h
  apply mem_rec_on h
  · intro b ss o s S ej

Depends on / 依赖: Seq.destruct, WSeq.recOn, append, congr_arg, cons_append, destruct, mem_rec_on, nil.cons, nil.nil, nil.think, notMem_nil, resolve_left, seq_dest
-/
theorem exists_of_mem_join {a : α} : forall {S : WSeq (WSeq α)}, a in join S -> exists s, s in S ∧ a in s := by
  suffices
    forall ss : WSeq α,
      a in ss -> forall s S, append s (join S) = ss -> a in append s (join S) -> a in s ∨ exists s, s in S ∧ a in s
    from fun S h => (this _ h nil S (by simp) (by simp [h])).resolve_left (notMem_nil _)
  intro ss h
  apply mem_rec_on h
  · intro b ss o s S ej m
    induction s using WSeq.recOn <;>
      [induction S using WSeq.recOn; skip; skip] <;>
      have := congr_arg Seq.destruct ej
    case nil.nil | nil.cons | nil.think | think => simp at this
    case cons =>
      simp only [cons_append, seq_destruct_cons, Option.some.injEq, Prod.mk.injEq] at this
      cases this with
      | intro b' s =>
        subst b' ss
        simp? at m ⊢ says simp only [cons_append, mem_cons_iff] at m ⊢
        rcases o with e | IH
        · simp [e]
        rcases m with e | m
        · simp [e]
        exact Or.imp_left Or.inr (IH _ _ rfl m)
  · intro ss IH s S ej m
    induction s using WSeq.recOn <;>
      [induction S using WSeq.recOn; skip; skip] <;>
      have := congr_arg Seq.destruct ej
    case nil.cons | nil.think | think => simp at this; simp_all
    case nil.nil | cons => simp at this

/--
theorem `exists_of_mem_bind` / 定理 `exists_of_mem_bind`

English:
theorem exists_of_mem_bind
  given: {s : WSeq α} {f : α -> WSeq β} {b} (h : b in bind s f)
  proof: let ⟨t, tm, bt⟩ := exists_of_mem_join h
  let ⟨a, as, e⟩ := exists_of_mem_map tm
  ⟨a, as, by rwa [e]⟩

中文:
定理 存在_of_mem_bind
  条件: {s : WSeq α} {f : α -> WSeq β} {b} (h : b in bind s f)
  证明: let ⟨t, tm, bt⟩ := exists_of_mem_join h
  let ⟨a, as, e⟩ := exists_of_mem_map tm
  ⟨a, as, by rwa [e]⟩

Depends on / 依赖: exists_of_mem_join, exists_of_mem_map
-/
theorem exists_of_mem_bind {s : WSeq α} {f : α -> WSeq β} {b} (h : b in bind s f) :
    exists a in s, b in f a :=
  let ⟨t, tm, bt⟩ := exists_of_mem_join h
  let ⟨a, as, e⟩ := exists_of_mem_map tm
  ⟨a, as, by rwa [e]⟩

/--
theorem `destruct_map` / 定理 `destruct_map`

English:
theorem destruct_map
  given: (f : α -> β) (s : WSeq α)
  proof: by
  apply
    Computation.eq_of_bisim fun c1 c2 =>
      exists s,
        c1 = destruct (map f s) ∧
          c2 = Computation.map (Option.map (Prod.map f (map f))) (destruct s)
  · intro c1 c2 h
    obtain ⟨s, h⟩ := h
    rw [h.left]; rw [h.right]
    induction s using WSeq.recOn
    case nil | c

中文:
定理 destruct_map
  条件: (f : α -> β) (s : WSeq α)
  证明: by
  apply
    Computation.eq_of_bisim fun c1 c2 =>
      exists s,
        c1 = destruct (map f s) ∧
          c2 = Computation.map (Option.map (Prod.map f (map f))) (destruct s)
  · intro c1 c2 h
    obtain ⟨s, h⟩ := h
    rw [h.left]; rw [h.right]
    induction s using WSeq.recOn
    case nil | c

Depends on / 依赖: Computation, Computation.eq_of_bisim, Computation.map, Option.map, Prod.map, WSeq.recOn, destruct, eq_of_bisim, h.left, h.right
-/
theorem destruct_map (f : α -> β) (s : WSeq α) :
    destruct (map f s) = Computation.map (Option.map (Prod.map f (map f))) (destruct s) := by
  apply
    Computation.eq_of_bisim fun c1 c2 =>
      exists s,
        c1 = destruct (map f s) ∧
          c2 = Computation.map (Option.map (Prod.map f (map f))) (destruct s)
  · intro c1 c2 h
    obtain ⟨s, h⟩ := h
    rw [h.left]; rw [h.right]
    induction s using WSeq.recOn
    case nil | cons => simp
    case think s => exact ⟨s, by simp⟩
  · exact ⟨s, rfl, rfl⟩

/-- auxiliary definition of `destruct_append` over weak sequences -/
@[simp]
/--
Definition of `destruct_append.aux` / `destruct_append.aux` 的定义

English:
definition destruct_append.aux
  signature: (t : WSeq α)

中文:
定义 destruct_append.aux
  签名: (t : WSeq α)
-/
def destruct_append.aux (t : WSeq α) : Option (α × WSeq α) -> Computation (Option (α × WSeq α))
  | none => destruct t
  | some (a, s) => Computation.pure (some (a, append s t))

/--
theorem `destruct_append` / 定理 `destruct_append`

English:
theorem destruct_append
  given: (s t : WSeq α)
  proof: by
  apply
    Computation.eq_of_bisim
      (fun c1 c2 =>
        exists s t, c1 = destruct (append s t) ∧ c2 = (destruct s).bind (destruct_append.aux t))
      _ ⟨s, t, rfl, rfl⟩
  intro c1 c2 h; rcases h with ⟨s, t, h⟩; rw [h.left, h.right]
  induction s using WSeq.recOn
  case nil =>
    inducti

中文:
定理 destruct_append
  条件: (s t : WSeq α)
  证明: by
  apply
    Computation.eq_of_bisim
      (fun c1 c2 =>
        exists s t, c1 = destruct (append s t) ∧ c2 = (destruct s).bind (destruct_append.aux t))
      _ ⟨s, t, rfl, rfl⟩
  intro c1 c2 h; rcases h with ⟨s, t, h⟩; rw [h.left, h.right]
  induction s using WSeq.recOn
  case nil =>
    inducti

Depends on / 依赖: Computation, Computation.eq_of_bisim, WSeq.recOn, append, destruct, destruct_append, destruct_append.aux, eq_of_bisim, h.left, h.right
-/
theorem destruct_append (s t : WSeq α) :
    destruct (append s t) = (destruct s).bind (destruct_append.aux t) := by
  apply
    Computation.eq_of_bisim
      (fun c1 c2 =>
        exists s t, c1 = destruct (append s t) ∧ c2 = (destruct s).bind (destruct_append.aux t))
      _ ⟨s, t, rfl, rfl⟩
  intro c1 c2 h; rcases h with ⟨s, t, h⟩; rw [h.left, h.right]
  induction s using WSeq.recOn
  case nil =>
    induction t using WSeq.recOn
    case nil | cons => simp
    case think t => exact ⟨nil, t, by simp⟩
  case cons => simp
  case think s => exact ⟨s, t, by simp⟩

/-- auxiliary definition of `destruct_join` over weak sequences -/
@[simp]
/--
Definition of `destruct_join.aux` / `destruct_join.aux` 的定义

English:
definition destruct_join.aux
  signature: : Option (WSeq α × WSeq (WSeq α)) -> Computation (Option (α × WSeq α))

中文:
定义 destruct_join.aux
  签名: : 选项类型 (WSeq α × WSeq (WSeq α)) -> Computation (选项类型 (α × WSeq α))
-/
def destruct_join.aux : Option (WSeq α × WSeq (WSeq α)) -> Computation (Option (α × WSeq α))
  | none => Computation.pure none
  | some (s, S) => (destruct (append s (join S))).think

/--
theorem `destruct_join` / 定理 `destruct_join`

English:
theorem destruct_join
  given: (S : WSeq (WSeq α))
  proof: by
  apply
    Computation.eq_of_bisim
      (fun c1 c2 =>
        c1 = c2 ∨ exists S, c1 = destruct (join S) ∧ c2 = (destruct S).bind destruct_join.aux)
      _ (Or.inr ⟨S, rfl, rfl⟩)
  intro c1 c2 h
  exact
    match c1, c2, h with
| c, _, Or.inl rfl => by cases c.destruct <;> simp
    | _, _, Or.

中文:
定理 destruct_join
  条件: (S : WSeq (WSeq α))
  证明: by
  apply
    Computation.eq_of_bisim
      (fun c1 c2 =>
        c1 = c2 ∨ exists S, c1 = destruct (join S) ∧ c2 = (destruct S).bind destruct_join.aux)
      _ (Or.inr ⟨S, rfl, rfl⟩)
  intro c1 c2 h
  exact
    match c1, c2, h with
| c, _, Or.inl rfl => by cases c.destruct <;> simp
    | _, _, Or.

Depends on / 依赖: Computation, Computation.eq_of_bisim, Or.inl, Or.inr, WSeq.recOn, c.destruct, destruct, destruct_join, destruct_join.aux, eq_of_bisim
-/
theorem destruct_join (S : WSeq (WSeq α)) :
    destruct (join S) = (destruct S).bind destruct_join.aux := by
  apply
    Computation.eq_of_bisim
      (fun c1 c2 =>
        c1 = c2 ∨ exists S, c1 = destruct (join S) ∧ c2 = (destruct S).bind destruct_join.aux)
      _ (Or.inr ⟨S, rfl, rfl⟩)
  intro c1 c2 h
  exact
    match c1, c2, h with
| c, _, Or.inl rfl => by cases c.destruct <;> simp
    | _, _, Or.inr ⟨S, rfl, rfl⟩ => by
      induction S using WSeq.recOn
      case nil | cons => simp
      case think S => exact Or.inr ⟨S, by simp⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `map_join` / 定理 `map_join`

English:
theorem map_join
  given: (f : α -> β) (S)
  statement: map f (join S) = join (map (map f) S)
  proof: by
  apply
    Seq.eq_of_bisim fun s1 s2 =>
      exists s S, s1 = append s (map f (join S)) ∧ s2 = append s (join (map (map f) S))
  · rintro s1 s2 ⟨s, S, rfl, rfl⟩
    induction s using WSeq.recOn
    · induction S using WSeq.recOn with
      | nil => simp
      | cons s S => simpa using ⟨map f s,

中文:
定理 map_join
  条件: (f : α -> β) (S)
  结论: map f (join S) = join (map (map f) S)
  证明: by
  apply
    Seq.eq_of_bisim fun s1 s2 =>
      exists s S, s1 = append s (map f (join S)) ∧ s2 = append s (join (map (map f) S))
  · rintro s1 s2 ⟨s, S, rfl, rfl⟩
    induction s using WSeq.recOn
    · induction S using WSeq.recOn with
      | nil => simp
      | cons s S => simpa using ⟨map f s,

Depends on / 依赖: Seq.eq_of_bisim, WSeq.recOn, append, eq_of_bisim
-/
theorem map_join (f : α -> β) (S) : map f (join S) = join (map (map f) S) := by
  apply
    Seq.eq_of_bisim fun s1 s2 =>
      exists s S, s1 = append s (map f (join S)) ∧ s2 = append s (join (map (map f) S))
  · rintro s1 s2 ⟨s, S, rfl, rfl⟩
    induction s using WSeq.recOn
    · induction S using WSeq.recOn with
      | nil => simp
      | cons s S => simpa using ⟨map f s, S, rfl, rfl⟩
      | think S => simpa using ⟨nil, S, by simp, by simp⟩
    · simpa using ⟨_, _, rfl, rfl⟩
    · simpa using ⟨_, _, rfl, rfl⟩
  · exact ⟨nil, S, by simp, by simp⟩

end WSeq

end Stream'
