/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Option.NAry
public import Mathlib.Data.Seq.Computation
public import Mathlib.Data.ENat.Defs
public import Batteries.Data.MLList.Basic
public import Mathlib.Data.Subtype

/-!
# Possibly infinite lists

This file provides `Stream'.Seq α`, a type representing possibly infinite lists (referred here as
sequences). It is encoded as an infinite stream of options such that if `f n = none`, then
`f m = none` for all `m ≥ n`.

## Main definitions

* `Seq α`: The type of possibly infinite lists (sequences) encoded as streams of options. It is
  encoded as `Stream' (Option α)` such that if `f n = none`, then `f m = none` for all `m ≥ n`.
  It has two "constructors": `nil` and `cons`, and a destructor `destruct`.
* `Seq1 α`: The type of nonempty sequences
* `Seq.get?`: Extract the nth element of a sequence (if it exists).
* `Seq.corec`: Corecursion principle for `Seq α` as a coinductive type.
* `Seq.Terminates`: Predicate for when a sequence is finite.

One can convert between sequences and other types: `List`, `Stream'`, `MLList` using corresponding
functions defined in this file.

There are also a number of operations and predicates on sequences mirroring those on lists:
`Seq.map`, `Seq.zip`, `Seq.zipWith`, `Seq.unzip`, `Seq.fold`, `Seq.update`, `Seq.drop`,
`Seq.splitAt`, `Seq.append`, `Seq.join`, `Seq.enum`, `Seq.Pairwise`,
as well as a cases principle `Seq.recOn` which allows one to reason about
sequences by cases (`nil` and `cons`).

## Main statements

* `eq_of_bisim`: Bisimulation principle for sequences.
-/

@[expose] public section

namespace Stream'

universe u v w

/-
coinductive seq (α : Type u) : Type u
| nil : seq α
| cons : α → seq α → seq α
-/
/--
Definition of `IsSeq` / `IsSeq` 的定义

English:
definition IsSeq
  signature: {α : Type u} (s : Stream' (Option α))
  body: forall {n : Nat}, s n = none -> s (n + 1) = none

中文:
定义 IsSeq
  签名: {α : 类型u} (s : Stream' (选项类型 α))
  定义体: forall {n : Nat}, s n = none -> s (n + 1) = none
-/
def IsSeq {α : Type u} (s : Stream' (Option α)) : Prop :=
  forall {n : Nat}, s n = none -> s (n + 1) = none

/--
Definition of `Seq` / `Seq` 的定义

English:
definition Seq
  signature: (α : Type u)
  body: { f : Stream' (Option α) // f.IsSeq }

中文:
定义 序列
  签名: (α : 类型u)
  定义体: { f : Stream' (Option α) // f.IsSeq }

Depends on / 依赖: Stream, f.IsSeq
-/
def Seq (α : Type u) : Type u :=
  { f : Stream' (Option α) // f.IsSeq }

/--
Definition of `Seq1` / `Seq1` 的定义

English:
definition Seq1
  signature: (α)
  body: α × Seq α

中文:
定义 Seq1
  签名: (α)
  定义体: α × Seq α
-/
def Seq1 (α) :=
  α × Seq α

namespace Seq

variable {α : Type u} {β : Type v} {γ : Type w}

/--
Definition of `get?` / `get?` 的定义

English:
definition get?
  signature: : Seq α -> Nat -> Option α
  body: Subtype.val

@[simp]

中文:
定义 get?
  签名: : 序列 α -> 自然数 -> 选项类型 α
  定义体: Subtype.val

@[simp]
-/
def get? : Seq α -> Nat -> Option α :=
  Subtype.val

@[simp]
/--
theorem `val_eq_get` / 定理 `val_eq_get`

English:
theorem val_eq_get
  given: (s : Seq α) (n : Nat)
  statement: s.val n = s.get? n
  proof: rfl

@[simp]

中文:
定理 val_eq_get
  条件: (s : 序列 α) (n : 自然数)
  结论: s.val n = s.get? n
  证明: rfl

@[simp]
-/
theorem val_eq_get (s : Seq α) (n : Nat) : s.val n = s.get? n :=
  rfl

@[simp]
/--
theorem `get?_mk` / 定理 `get?_mk`

English:
theorem get?_mk
  given: (f hf)
  statement: @get? α ⟨f, hf⟩ = f
  proof: rfl

中文:
定理 get?_mk
  条件: (f hf)
  结论: @get? α ⟨f, hf⟩ = f
  证明: rfl
-/
theorem get?_mk (f hf) : @get? α ⟨f, hf⟩ = f :=
  rfl

/--
theorem `le_stable` / 定理 `le_stable`

English:
theorem le_stable
  given: (s : Seq α) {m n} (h : m <= n)
  statement: s.get? m = none -> s.get? n = none
  proof: by
  obtain ⟨f, al⟩ := s
  induction h with | refl => exact id | step _ IH => exact fun h2 => al (IH h2)

中文:
定理 le_stable
  条件: (s : 序列 α) {m n} (h : m <= n)
  结论: s.get? m = none -> s.get? n = none
  证明: by
  obtain ⟨f, al⟩ := s
  induction h with | refl => exact id | step _ IH => exact fun h2 => al (IH h2)
-/
theorem le_stable (s : Seq α) {m n} (h : m <= n) : s.get? m = none -> s.get? n = none := by
  obtain ⟨f, al⟩ := s
  induction h with | refl => exact id | step _ IH => exact fun h2 => al (IH h2)

/--
theorem `ge_stable` / 定理 `ge_stable`

English:
theorem ge_stable
  statement: (s : Seq α) {aₙ : α} {n m : Nat} (m_le_n : m <= n)
  proof: have : s.get? n != none := by simp [s_nth_eq_some]
  have : s.get? m != none := mt (s.le_stable m_le_n) this
  Option.ne_none_iff_exists'.mp this

@[ext]

中文:
定理 ge_stable
  结论: (s : 序列 α) {aₙ : α} {n m : 自然数} (m_le_n : m <= n)
  证明: have : s.get? n != none := by simp [s_nth_eq_some]
  have : s.get? m != none := mt (s.le_stable m_le_n) this
  Option.ne_none_iff_exists'.mp this

@[ext]

Depends on / 依赖: Option.ne_none_iff_exists, le_stable, m_le_n, ne_none_iff_exists, s.get, s.le_stable, s_nth_eq_some
-/
theorem ge_stable (s : Seq α) {aₙ : α} {n m : Nat} (m_le_n : m <= n)
    (s_nth_eq_some : s.get? n = some aₙ) : exists aₘ : α, s.get? m = some aₘ :=
  have : s.get? n != none := by simp [s_nth_eq_some]
  have : s.get? m != none := mt (s.le_stable m_le_n) this
  Option.ne_none_iff_exists'.mp this

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {s t : Seq α} (h : forall n : Nat, s.get? n = t.get? n)
  statement: s = t
  proof: Subtype.ext funext h

中文:
定理 ext
  条件: {s t : 序列 α} (h : 对任意 n : 自然数, s.get? n = t.get? n)
  结论: s = t
  证明: Subtype.ext funext h
-/
protected theorem ext {s t : Seq α} (h : forall n : Nat, s.get? n = t.get? n) : s = t :=
Subtype.ext funext h

/-!
### Constructors
-/

/--
Definition of `nil` / `nil` 的定义

English:
definition nil
  signature: : Seq α
  body: ⟨Stream'.const none, fun {_} _ => rfl⟩

中文:
定义 nil
  签名: : 序列 α
  定义体: ⟨Stream'.const none, fun {_} _ => rfl⟩

Depends on / 依赖: Stream
-/
def nil : Seq α :=
  ⟨Stream'.const none, fun {_} _ => rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Seq α)
  body: ⟨nil⟩

中文:
实例 :
  签名: 可居 (序列 α)
  定义体: ⟨nil⟩
-/
instance : Inhabited (Seq α) :=
  ⟨nil⟩

/--
Definition of `cons` / `cons` 的定义

English:
definition cons
  signature: (a : α) (s : Seq α)
  body: ⟨some a::s.1, by
    rintro (n | _) h
    · contradiction
    · exact s.2 h⟩

@[simp]

中文:
定义 cons
  签名: (a : α) (s : 序列 α)
  定义体: ⟨some a::s.1, by
    rintro (n | _) h
    · contradiction
    · exact s.2 h⟩

@[simp]
-/
def cons (a : α) (s : Seq α) : Seq α :=
  ⟨some a::s.1, by
    rintro (n | _) h
    · contradiction
    · exact s.2 h⟩

@[simp]
/--
theorem `val_cons` / 定理 `val_cons`

English:
theorem val_cons
  given: (s : Seq α) (x : α)
  statement: (cons x s).val = some x::s.val
  proof: rfl

@[simp]

中文:
定理 val_cons
  条件: (s : 序列 α) (x : α)
  结论: (cons x s).val = some x::s.val
  证明: rfl

@[simp]
-/
theorem val_cons (s : Seq α) (x : α) : (cons x s).val = some x::s.val :=
  rfl

@[simp]
/--
theorem `get?_nil` / 定理 `get?_nil`

English:
theorem get?_nil
  given: (n : Nat)
  statement: (@nil α).get? n = none
  proof: rfl

@[simp]

中文:
定理 get?_nil
  条件: (n : 自然数)
  结论: (@nil α).get? n = none
  证明: rfl

@[simp]
-/
theorem get?_nil (n : Nat) : (@nil α).get? n = none :=
  rfl

@[simp]
/--
theorem `get?_zero_eq_none` / 定理 `get?_zero_eq_none`

English:
theorem get?_zero_eq_none
  given: {s : Seq α}
  statement: s.get? 0 = none ↔ s = nil
  proof: by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  ext1 n
  exact le_stable s (Nat.zero_le _) h

@[simp]

中文:
定理 get?_zero_eq_none
  条件: {s : 序列 α}
  结论: s.get? 0 = none ↔ s = nil
  证明: by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  ext1 n
  exact le_stable s (Nat.zero_le _) h

@[simp]
-/
theorem get?_zero_eq_none {s : Seq α} : s.get? 0 = none ↔ s = nil := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  ext1 n
  exact le_stable s (Nat.zero_le _) h

@[simp]
/--
theorem `get?_cons_zero` / 定理 `get?_cons_zero`

English:
theorem get?_cons_zero
  given: (a : α) (s : Seq α)
  statement: (cons a s).get? 0 = some a
  proof: rfl

@[simp]

中文:
定理 get?_cons_zero
  条件: (a : α) (s : 序列 α)
  结论: (cons a s).get? 0 = some a
  证明: rfl

@[simp]
-/
theorem get?_cons_zero (a : α) (s : Seq α) : (cons a s).get? 0 = some a :=
  rfl

@[simp]
/--
theorem `get?_cons_succ` / 定理 `get?_cons_succ`

English:
theorem get?_cons_succ
  given: (a : α) (s : Seq α) (n : Nat)
  statement: (cons a s).get? (n + 1) = s.get? n
  proof: rfl

@[simp]

中文:
定理 get?_cons_succ
  条件: (a : α) (s : 序列 α) (n : 自然数)
  结论: (cons a s).get? (n + 1) = s.get? n
  证明: rfl

@[simp]
-/
theorem get?_cons_succ (a : α) (s : Seq α) (n : Nat) : (cons a s).get? (n + 1) = s.get? n :=
  rfl

@[simp]
/--
theorem `cons_ne_nil` / 定理 `cons_ne_nil`

English:
theorem cons_ne_nil
  given: {x : α} {s : Seq α}
  statement: (cons x s) != .nil
  proof: by
  intro h
  simpa using congrArg (·.get? 0) h

@[simp]

中文:
定理 cons_ne_nil
  条件: {x : α} {s : 序列 α}
  结论: (cons x s) != .nil
  证明: by
  intro h
  simpa using congrArg (·.get? 0) h

@[simp]
-/
theorem cons_ne_nil {x : α} {s : Seq α} : (cons x s) != .nil := by
  intro h
  simpa using congrArg (·.get? 0) h

@[simp]
/--
theorem `nil_ne_cons` / 定理 `nil_ne_cons`

English:
theorem nil_ne_cons
  given: {x : α} {s : Seq α}
  statement: .nil != (cons x s)
  proof: cons_ne_nil.symm

中文:
定理 nil_ne_cons
  条件: {x : α} {s : 序列 α}
  结论: .nil != (cons x s)
  证明: cons_ne_nil.symm

Depends on / 依赖: cons_ne_nil, cons_ne_nil.symm
-/
theorem nil_ne_cons {x : α} {s : Seq α} : .nil != (cons x s) := cons_ne_nil.symm

/--
theorem `cons_injective2` / 定理 `cons_injective2`

English:
theorem cons_injective2
  statement: Function.Injective2 (cons : α -> Seq α -> Seq α)
  proof: fun x y s t h =>
  ⟨by rw [← Option.some_inj, ← get?_cons_zero, h, get?_cons_zero],
    Seq.ext fun n => by simp_rw [← get?_cons_succ x s n, h, get?_cons_succ]⟩

中文:
定理 cons_injective2
  结论: 函数.Injective2 (cons : α -> 序列 α -> 序列 α)
  证明: fun x y s t h =>
  ⟨by rw [← Option.some_inj, ← get?_cons_zero, h, get?_cons_zero],
    Seq.ext fun n => by simp_rw [← get?_cons_succ x s n, h, get?_cons_succ]⟩
-/
theorem cons_injective2 : Function.Injective2 (cons : α -> Seq α -> Seq α) := fun x y s t h =>
  ⟨by rw [← Option.some_inj, ← get?_cons_zero, h, get?_cons_zero],
    Seq.ext fun n => by simp_rw [← get?_cons_succ x s n, h, get?_cons_succ]⟩

/--
theorem `cons_left_injective` / 定理 `cons_left_injective`

English:
theorem cons_left_injective
  given: (s : Seq α)
  statement: Function.Injective fun x => cons x s
  proof: cons_injective2.left _

中文:
定理 cons_left_injective
  条件: (s : 序列 α)
  结论: 函数.单射 fun x => cons x s
  证明: cons_injective2.left _

Depends on / 依赖: cons_injective2, cons_injective2.left
-/
theorem cons_left_injective (s : Seq α) : Function.Injective fun x => cons x s :=
  cons_injective2.left _

/--
theorem `cons_right_injective` / 定理 `cons_right_injective`

English:
theorem cons_right_injective
  given: (x : α)
  statement: Function.Injective (cons x)
  proof: cons_injective2.right _

@[simp]

中文:
定理 cons_right_injective
  条件: (x : α)
  结论: 函数.单射 (cons x)
  证明: cons_injective2.right _

@[simp]

Depends on / 依赖: cons_injective2, cons_injective2.right
-/
theorem cons_right_injective (x : α) : Function.Injective (cons x) :=
  cons_injective2.right _

@[simp]
/--
theorem `cons_eq_cons` / 定理 `cons_eq_cons`

English:
theorem cons_eq_cons
  given: {x x' : α} {s s' : Seq α}
  proof: by
  constructor
  · apply cons_injective2
  · intro ⟨_, _⟩
    congr

中文:
定理 cons_eq_cons
  条件: {x x' : α} {s s' : 序列 α}
  证明: by
  constructor
  · apply cons_injective2
  · intro ⟨_, _⟩
    congr

Depends on / 依赖: cons_injective2
-/
theorem cons_eq_cons {x x' : α} {s s' : Seq α} :
    (cons x s = cons x' s') ↔ (x = x' ∧ s = s') := by
  constructor
  · apply cons_injective2
  · intro ⟨_, _⟩
    congr

/-!
### Destructors
-/

/--
Definition of `head` / `head` 的定义

English:
definition head
  signature: (s : Seq α)
  body: get? s 0

中文:
定义 head
  签名: (s : 序列 α)
  定义体: get? s 0
-/
def head (s : Seq α) : Option α :=
  get? s 0

/--
Definition of `tail` / `tail` 的定义

English:
definition tail
  signature: (s : Seq α)
  body: ⟨s.1.tail, fun n' => by
    obtain ⟨f, al⟩ := s
    exact al n'⟩

中文:
定义 tail
  签名: (s : 序列 α)
  定义体: ⟨s.1.tail, fun n' => by
    obtain ⟨f, al⟩ := s
    exact al n'⟩
-/
def tail (s : Seq α) : Seq α :=
  ⟨s.1.tail, fun n' => by
    obtain ⟨f, al⟩ := s
    exact al n'⟩

/--
Definition of `destruct` / `destruct` 的定义

English:
definition destruct
  signature: (s : Seq α)
  body: (fun a' => (a', s.tail)) < > get? s 0

中文:
定义 destruct
  签名: (s : 序列 α)
  定义体: (fun a' => (a', s.tail)) < > get? s 0

Depends on / 依赖: s.tail
-/
def destruct (s : Seq α) : Option (Seq1 α) :=
(fun a' => (a', s.tail)) < > get? s 0

-- Porting note: needed universe annotation to avoid universe issues
/--
theorem `head_eq_destruct` / 定理 `head_eq_destruct`

English:
theorem head_eq_destruct
  given: (s : Seq α)
  statement: head s = Prod.fst < > destruct.{u} s
  proof: by
  unfold destruct head; cases get? s 0 <;> rfl

@[simp]

中文:
定理 head_eq_destruct
  条件: (s : 序列 α)
  结论: head s = 积类型.fst < > destruct.{u} s
  证明: by
  unfold destruct head; cases get? s 0 <;> rfl

@[simp]

Depends on / 依赖: destruct
-/
theorem head_eq_destruct (s : Seq α) : head s = Prod.fst < > destruct.{u} s := by
  unfold destruct head; cases get? s 0 <;> rfl

@[simp]
/--
theorem `get?_tail` / 定理 `get?_tail`

English:
theorem get?_tail
  given: (s : Seq α) (n)
  statement: get? (tail s) n = get? s (n + 1)
  proof: rfl

@[simp]

中文:
定理 get?_tail
  条件: (s : 序列 α) (n)
  结论: get? (tail s) n = get? s (n + 1)
  证明: rfl

@[simp]
-/
theorem get?_tail (s : Seq α) (n) : get? (tail s) n = get? s (n + 1) :=
  rfl

@[simp]
/--
theorem `destruct_nil` / 定理 `destruct_nil`

English:
theorem destruct_nil
  statement: destruct (nil : Seq α) = none
  proof: rfl

@[simp]

中文:
定理 destruct_nil
  结论: destruct (nil : 序列 α) = none
  证明: rfl

@[simp]
-/
theorem destruct_nil : destruct (nil : Seq α) = none :=
  rfl

@[simp]
/--
theorem `destruct_cons` / 定理 `destruct_cons`

English:
theorem destruct_cons
  given: (a : α)
  statement: forall s, destruct (cons a s) = some (a, s)

中文:
定理 destruct_cons
  条件: (a : α)
  结论: 对任意 s, destruct (cons a s) = some (a, s)
-/
theorem destruct_cons (a : α) : forall s, destruct (cons a s) = some (a, s)
  | ⟨f, al⟩ => by
    unfold cons destruct Functor.map
    apply congr_arg fun s => some (a, s)
    apply Subtype.ext; dsimp [tail]

/--
theorem `destruct_eq_none` / 定理 `destruct_eq_none`

English:
theorem destruct_eq_none
  given: {s : Seq α}
  statement: destruct s = none -> s = nil
  proof: by
  dsimp [destruct]
  rcases f0 : get? s 0 <;> intro h
  · exact get?_zero_eq_none.mp f0
  · contradiction

中文:
定理 destruct_eq_none
  条件: {s : 序列 α}
  结论: destruct s = none -> s = nil
  证明: by
  dsimp [destruct]
  rcases f0 : get? s 0 <;> intro h
  · exact get?_zero_eq_none.mp f0
  · contradiction

Depends on / 依赖: _zero_eq_none, _zero_eq_none.mp, destruct
-/
theorem destruct_eq_none {s : Seq α} : destruct s = none -> s = nil := by
  dsimp [destruct]
  rcases f0 : get? s 0 <;> intro h
  · exact get?_zero_eq_none.mp f0
  · contradiction

/--
theorem `destruct_eq_cons` / 定理 `destruct_eq_cons`

English:
theorem destruct_eq_cons
  given: {s : Seq α} {a s'}
  statement: destruct s = some (a, s') -> s = cons a s'
  proof: by
  dsimp [destruct]
  rcases f0 : get? s 0 with - | a' <;> intro h
  · contradiction
  · obtain ⟨f, al⟩ := s
    injections _ h1 h2
    rw [← h2]
    apply Subtype.ext
    dsimp [tail, cons]
    rw [h1] at f0
    rw [← f0]
    exact (Stream'.eta f).symm

@[simp]

中文:
定理 destruct_eq_cons
  条件: {s : 序列 α} {a s'}
  结论: destruct s = some (a, s') -> s = cons a s'
  证明: by
  dsimp [destruct]
  rcases f0 : get? s 0 with - | a' <;> intro h
  · contradiction
  · obtain ⟨f, al⟩ := s
    injections _ h1 h2
    rw [← h2]
    apply Subtype.ext
    dsimp [tail, cons]
    rw [h1] at f0
    rw [← f0]
    exact (Stream'.eta f).symm

@[simp]

Depends on / 依赖: Stream, Subtype, Subtype.ext, destruct, injections
-/
theorem destruct_eq_cons {s : Seq α} {a s'} : destruct s = some (a, s') -> s = cons a s' := by
  dsimp [destruct]
  rcases f0 : get? s 0 with - | a' <;> intro h
  · contradiction
  · obtain ⟨f, al⟩ := s
    injections _ h1 h2
    rw [← h2]
    apply Subtype.ext
    dsimp [tail, cons]
    rw [h1] at f0
    rw [← f0]
    exact (Stream'.eta f).symm

@[simp]
/--
theorem `head_nil` / 定理 `head_nil`

English:
theorem head_nil
  statement: head (nil : Seq α) = none
  proof: rfl

@[simp]

中文:
定理 head_nil
  结论: head (nil : 序列 α) = none
  证明: rfl

@[simp]
-/
theorem head_nil : head (nil : Seq α) = none :=
  rfl

@[simp]
/--
theorem `head_cons` / 定理 `head_cons`

English:
theorem head_cons
  given: (a : α) (s)
  statement: head (cons a s) = some a
  proof: by
  rw [head_eq_destruct]; rw [destruct_cons]; rw [Option.map_eq_map]; rw [Option.map_some]

@[simp]

中文:
定理 head_cons
  条件: (a : α) (s)
  结论: head (cons a s) = some a
  证明: by
  rw [head_eq_destruct]; rw [destruct_cons]; rw [Option.map_eq_map]; rw [Option.map_some]

@[simp]

Depends on / 依赖: Option.map_eq_map, Option.map_some, destruct_cons, head_eq_destruct, map_eq_map, map_some
-/
theorem head_cons (a : α) (s) : head (cons a s) = some a := by
  rw [head_eq_destruct]; rw [destruct_cons]; rw [Option.map_eq_map]; rw [Option.map_some]

@[simp]
/--
theorem `tail_nil` / 定理 `tail_nil`

English:
theorem tail_nil
  statement: tail (nil : Seq α) = nil
  proof: rfl

@[simp]

中文:
定理 tail_nil
  结论: tail (nil : 序列 α) = nil
  证明: rfl

@[simp]
-/
theorem tail_nil : tail (nil : Seq α) = nil :=
  rfl

@[simp]
/--
theorem `tail_cons` / 定理 `tail_cons`

English:
theorem tail_cons
  given: (a : α) (s)
  statement: tail (cons a s) = s
  proof: rfl

中文:
定理 tail_cons
  条件: (a : α) (s)
  结论: tail (cons a s) = s
  证明: rfl
-/
theorem tail_cons (a : α) (s) : tail (cons a s) = s := rfl

/--
theorem `head_eq_some` / 定理 `head_eq_some`

English:
theorem head_eq_some
  given: {s : Seq α} {x : α} (h : s.head = some x)
  proof: by
  ext1 n
  cases n <;> simp only [get?_cons_zero, get?_cons_succ, get?_tail]
  exact h

中文:
定理 head_eq_some
  条件: {s : 序列 α} {x : α} (h : s.head = some x)
  证明: by
  ext1 n
  cases n <;> simp only [get?_cons_zero, get?_cons_succ, get?_tail]
  exact h

Depends on / 依赖: _cons_succ, _cons_zero, _tail
-/
theorem head_eq_some {s : Seq α} {x : α} (h : s.head = some x) :
    s = cons x s.tail := by
  ext1 n
  cases n <;> simp only [get?_cons_zero, get?_cons_succ, get?_tail]
  exact h

/--
theorem `head_eq_none` / 定理 `head_eq_none`

English:
theorem head_eq_none
  given: {s : Seq α} (h : s.head = none)
  statement: s = nil
  proof: get?_zero_eq_none.mp h

@[simp]

中文:
定理 head_eq_none
  条件: {s : 序列 α} (h : s.head = none)
  结论: s = nil
  证明: get?_zero_eq_none.mp h

@[simp]

Depends on / 依赖: _zero_eq_none, _zero_eq_none.mp
-/
theorem head_eq_none {s : Seq α} (h : s.head = none) : s = nil :=
  get?_zero_eq_none.mp h

@[simp]
/--
theorem `head_eq_none_iff` / 定理 `head_eq_none_iff`

English:
theorem head_eq_none_iff
  given: {s : Seq α}
  statement: s.head = none ↔ s = nil
  proof: by
  constructor
  · apply head_eq_none
  · intro h
    simp [h]

中文:
定理 head_eq_none_iff
  条件: {s : 序列 α}
  结论: s.head = none ↔ s = nil
  证明: by
  constructor
  · apply head_eq_none
  · intro h
    simp [h]

Depends on / 依赖: head_eq_none
-/
theorem head_eq_none_iff {s : Seq α} : s.head = none ↔ s = nil := by
  constructor
  · apply head_eq_none
  · intro h
    simp [h]

/-!
### Recursion and corecursion principles
-/

/-- Recursion principle for sequences, compare with `List.recOn`. -/
@[cases_eliminator]
/--
Definition of `recOn` / `recOn` 的定义

English:
definition recOn
  signature: {motive : Seq α -> Sort v} (s : Seq α) (nil : motive nil)
  body: by
  rcases H : destruct s with - | v
  · rw [destruct_eq_none H]
    apply nil
  · obtain ⟨a, s'⟩ := v
    rw [destruct_eq_cons H]
    apply cons

中文:
定义 recOn
  签名: {motive : 序列 α -> 类型层 v} (s : 序列 α) (nil : motive nil)
  定义体: by
  rcases H : destruct s with - | v
  · rw [destruct_eq_none H]
    apply nil
  · obtain ⟨a, s'⟩ := v
    rw [destruct_eq_cons H]
    apply cons

Depends on / 依赖: destruct, destruct_eq_cons, destruct_eq_none
-/
def recOn {motive : Seq α -> Sort v} (s : Seq α) (nil : motive nil)
    (cons : forall x s, motive (cons x s)) :
    motive s := by
  rcases H : destruct s with - | v
  · rw [destruct_eq_none H]
    apply nil
  · obtain ⟨a, s'⟩ := v
    rw [destruct_eq_cons H]
    apply cons

/-- Functorial action of the functor `Option (α × _)` -/
@[simp]
/--
Definition of `omap` / `omap` 的定义

English:
definition omap
  signature: (f : β -> γ)

中文:
定义 omap
  签名: (f : β -> γ)
-/
def omap (f : β -> γ) : Option (α × β) -> Option (α × γ)
  | none => none
  | some (a, b) => some (a, f b)

/--
Definition of `Corec.f` / `Corec.f` 的定义

English:
definition Corec.f
  signature: (f : β -> Option (α × β))

中文:
定义 Corec.f
  签名: (f : β -> 选项类型 (α × β))
-/
def Corec.f (f : β -> Option (α × β)) : Option β -> Option α × Option β
  | none => (none, none)
  | some b =>
    match f b with
    | none => (none, none)
    | some (a, b') => (some a, some b')

/--
Definition of `corec` / `corec` 的定义

English:
definition corec
  signature: (f : β -> Option (α × β)) (b : β)
  body: by
  refine ⟨Stream'.corec' (Corec.f f) (some b), fun {n} h => ?_⟩
  rw [Stream'.corec'_eq]
  change Stream'.corec' (Corec.f f) (Corec.f f (some b)).2 n = none
  revert h; generalize some b = o
  induction n generalizing o with
  | zero =>
    change (Corec.f f o).1 = none -> (Corec.f f (Corec.f f o).2).1 = none
    rcases o with - | b <;> intro h
    · rfl
    dsimp [Corec.f] at h
    dsimp [Corec.f]
    revert h; rcases h₁ : f b with - | s <;> intro h
    · rfl
    · obtain ⟨a, b'⟩ := s
      contradiction
  | succ n IH =>
    rw [Stream'.corec'_eq (Corec.f f) (Corec.f f o).2]; rw [Stream'.corec'_eq (Corec.f f) o]
    exact IH (Corec.f f o).2

中文:
定义 corec
  签名: (f : β -> 选项类型 (α × β)) (b : β)
  定义体: by
  refine ⟨Stream'.corec' (Corec.f f) (some b), fun {n} h => ?_⟩
  rw [Stream'.corec'_eq]
  change Stream'.corec' (Corec.f f) (Corec.f f (some b)).2 n = none
  revert h; generalize some b = o
  induction n generalizing o with
  | zero =>
    change (Corec.f f o).1 = none -> (Corec.f f (Corec.f f o).2).1 = none
    rcases o with - | b <;> intro h
    · rfl
    dsimp [Corec.f] at h
    dsimp [Corec.f]
    revert h; rcases h₁ : f b with - | s <;> intro h
    · rfl
    · obtain ⟨a, b'⟩ := s
      contradiction
  | succ n IH =>
    rw [Stream'.corec'_eq (Corec.f f) (Corec.f f o).2]; rw [Stream'.corec'_eq (Corec.f f) o]
    exact IH (Corec.f f o).2

Depends on / 依赖: Corec.f, Stream, generalize, generalizing, revert
-/
def corec (f : β -> Option (α × β)) (b : β) : Seq α := by
  refine ⟨Stream'.corec' (Corec.f f) (some b), fun {n} h => ?_⟩
  rw [Stream'.corec'_eq]
  change Stream'.corec' (Corec.f f) (Corec.f f (some b)).2 n = none
  revert h; generalize some b = o
  induction n generalizing o with
  | zero =>
    change (Corec.f f o).1 = none -> (Corec.f f (Corec.f f o).2).1 = none
    rcases o with - | b <;> intro h
    · rfl
    dsimp [Corec.f] at h
    dsimp [Corec.f]
    revert h; rcases h₁ : f b with - | s <;> intro h
    · rfl
    · obtain ⟨a, b'⟩ := s
      contradiction
  | succ n IH =>
    rw [Stream'.corec'_eq (Corec.f f) (Corec.f f o).2]; rw [Stream'.corec'_eq (Corec.f f) o]
    exact IH (Corec.f f o).2

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `corec_eq` / 定理 `corec_eq`

English:
theorem corec_eq
  given: (f : β -> Option (α × β)) (b : β)
  proof: by
  dsimp [corec, destruct, get]
  rw [show Stream'.corec' (Corec.f f) (some b) 0 = (Corec.f f (some b)).1 from rfl]
  dsimp [Corec.f]
  rcases h : f b with - | s; · rfl
  obtain ⟨a, b'⟩ := s; dsimp [Corec.f]
  apply congr_arg fun b' => some (a, b')
  apply Subtype.ext
  dsimp [corec, tail]
  rw [Stream'.corec'_eq]; rw [Stream'.tail_cons]
  dsimp [Corec.f]; rw [h]

中文:
定理 corec_eq
  条件: (f : β -> 选项类型 (α × β)) (b : β)
  证明: by
  dsimp [corec, destruct, get]
  rw [show Stream'.corec' (Corec.f f) (some b) 0 = (Corec.f f (some b)).1 from rfl]
  dsimp [Corec.f]
  rcases h : f b with - | s; · rfl
  obtain ⟨a, b'⟩ := s; dsimp [Corec.f]
  apply congr_arg fun b' => some (a, b')
  apply Subtype.ext
  dsimp [corec, tail]
  rw [Stream'.corec'_eq]; rw [Stream'.tail_cons]
  dsimp [Corec.f]; rw [h]

Depends on / 依赖: Corec.f, Stream, Subtype, Subtype.ext, congr_arg, destruct, tail_cons
-/
theorem corec_eq (f : β -> Option (α × β)) (b : β) :
    destruct (corec f b) = omap (corec f) (f b) := by
  dsimp [corec, destruct, get]
  rw [show Stream'.corec' (Corec.f f) (some b) 0 = (Corec.f f (some b)).1 from rfl]
  dsimp [Corec.f]
  rcases h : f b with - | s; · rfl
  obtain ⟨a, b'⟩ := s; dsimp [Corec.f]
  apply congr_arg fun b' => some (a, b')
  apply Subtype.ext
  dsimp [corec, tail]
  rw [Stream'.corec'_eq]; rw [Stream'.tail_cons]
  dsimp [Corec.f]; rw [h]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `corec_nil` / 定理 `corec_nil`

English:
theorem corec_nil
  statement: (f : β -> Option (α × β)) (b : β)
  proof: by
  apply destruct_eq_none
  simp [h]

中文:
定理 corec_nil
  结论: (f : β -> 选项类型 (α × β)) (b : β)
  证明: by
  apply destruct_eq_none
  simp [h]

Depends on / 依赖: destruct_eq_none
-/
theorem corec_nil (f : β -> Option (α × β)) (b : β)
    (h : f b = .none) : corec f b = nil := by
  apply destruct_eq_none
  simp [h]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `corec_cons` / 定理 `corec_cons`

English:
theorem corec_cons
  statement: {f : β -> Option (α × β)} {b : β} {x : α} {s : β}
  proof: by
  apply destruct_eq_cons
  simp [h]

中文:
定理 corec_cons
  结论: {f : β -> 选项类型 (α × β)} {b : β} {x : α} {s : β}
  证明: by
  apply destruct_eq_cons
  simp [h]

Depends on / 依赖: destruct_eq_cons
-/
theorem corec_cons {f : β -> Option (α × β)} {b : β} {x : α} {s : β}
    (h : f b = .some (x, s)) : corec f b = cons x (corec f s) := by
  apply destruct_eq_cons
  simp [h]

/-!
### Bisimulation
-/

section Bisim

variable (R : Seq α -> Seq α -> Prop)

local infixl:50 " ~ " => R

/--
Definition of `BisimO` / `BisimO` 的定义

English:
definition BisimO
  signature: : Option (Seq1 α) -> Option (Seq1 α) -> Prop

中文:
定义 BisimO
  签名: : 选项类型 (Seq1 α) -> 选项类型 (Seq1 α) -> 命题
-/
def BisimO : Option (Seq1 α) -> Option (Seq1 α) -> Prop
  | none, none => True
  | some (a, s), some (a', s') => a = a' ∧ R s s'
  | _, _ => False

attribute [simp] BisimO
attribute [nolint simpNF] BisimO.eq_3

/--
Definition of `IsBisimulation` / `IsBisimulation` 的定义

English:
definition IsBisimulation
  body: forall ⦃s₁ s₂⦄, s₁ ~ s₂ -> BisimO R (destruct s₁) (destruct s₂)

中文:
定义 是Bisimulation
  定义体: forall ⦃s₁ s₂⦄, s₁ ~ s₂ -> BisimO R (destruct s₁) (destruct s₂)

Depends on / 依赖: BisimO, destruct
-/
def IsBisimulation :=
  forall ⦃s₁ s₂⦄, s₁ ~ s₂ -> BisimO R (destruct s₁) (destruct s₂)

/--
theorem `eq_of_bisim` / 定理 `eq_of_bisim`

English:
theorem eq_of_bisim
  given: (bisim : IsBisimulation R) {s₁ s₂} (r : s₁ ~ s₂)
  statement: s₁ = s₂
  proof: by
  apply Subtype.ext
  apply Stream'.eq_of_bisim fun x y => exists s s' : Seq α, s.1 = x ∧ s'.1 = y ∧ R s s'
  · dsimp [Stream'.IsBisimulation]
    intro t₁ t₂ e
    exact
    match t₁, t₂, e with
    | _, _, ⟨s, s', rfl, rfl, r⟩ => by
      suffices head s = head s' ∧ R (tail s) (tail s') from
        And.imp id (fun r => ⟨tail s, tail s', by cases s using Subtype.recOn; rfl,
          by cases s' using Subtype.recOn; rfl, r⟩) this
      have := bisim r; revert r this
      cases s <;> cases s'
      · intro r _
        constructor
        · rfl
        · assumption
      · intro _ this
        rw [destruct_nil]; rw [destruct_cons] at this
        exact False.elim this
      · intro _ this
        rw [destruct_nil]; rw [destruct_cons] at this
        exact False.elim this
      · simp
  · exact ⟨s₁, s₂, rfl, rfl, r⟩

中文:
定理 eq_of_bisim
  条件: (bisim : 是Bisimulation R) {s₁ s₂} (r : s₁ ~ s₂)
  结论: s₁ = s₂
  证明: by
  apply Subtype.ext
  apply Stream'.eq_of_bisim fun x y => exists s s' : Seq α, s.1 = x ∧ s'.1 = y ∧ R s s'
  · dsimp [Stream'.IsBisimulation]
    intro t₁ t₂ e
    exact
    match t₁, t₂, e with
    | _, _, ⟨s, s', rfl, rfl, r⟩ => by
      suffices head s = head s' ∧ R (tail s) (tail s') from
        And.imp id (fun r => ⟨tail s, tail s', by cases s using Subtype.recOn; rfl,
          by cases s' using Subtype.recOn; rfl, r⟩) this
      have := bisim r; revert r this
      cases s <;> cases s'
      · intro r _
        constructor
        · rfl
        · assumption
      · intro _ this
        rw [destruct_nil]; rw [destruct_cons] at this
        exact False.elim this
      · intro _ this
        rw [destruct_nil]; rw [destruct_cons] at this
        exact False.elim this
      · simp
  · exact ⟨s₁, s₂, rfl, rfl, r⟩

Depends on / 依赖: And.imp, IsBisimulation, Stream, Subtype, Subtype.ext, Subtype.recOn, eq_of_bisim, revert
-/
theorem eq_of_bisim (bisim : IsBisimulation R) {s₁ s₂} (r : s₁ ~ s₂) : s₁ = s₂ := by
  apply Subtype.ext
  apply Stream'.eq_of_bisim fun x y => exists s s' : Seq α, s.1 = x ∧ s'.1 = y ∧ R s s'
  · dsimp [Stream'.IsBisimulation]
    intro t₁ t₂ e
    exact
    match t₁, t₂, e with
    | _, _, ⟨s, s', rfl, rfl, r⟩ => by
      suffices head s = head s' ∧ R (tail s) (tail s') from
        And.imp id (fun r => ⟨tail s, tail s', by cases s using Subtype.recOn; rfl,
          by cases s' using Subtype.recOn; rfl, r⟩) this
      have := bisim r; revert r this
      cases s <;> cases s'
      · intro r _
        constructor
        · rfl
        · assumption
      · intro _ this
        rw [destruct_nil]; rw [destruct_cons] at this
        exact False.elim this
      · intro _ this
        rw [destruct_nil]; rw [destruct_cons] at this
        exact False.elim this
      · simp
  · exact ⟨s₁, s₂, rfl, rfl, r⟩

/--
theorem `eq_of_bisim'` / 定理 `eq_of_bisim'`

English:
theorem eq_of_bisim'
  statement: {s₁ s₂ : Seq α}
  proof: by
  apply eq_of_bisim motive _ base
  intro s₁ s₂ h
  rcases step s₁ s₂ h with ⟨h_nil₁, h_nil₂⟩ | ⟨_, _, _, h₁, h₂, _⟩
  · simp [h_nil₁, h_nil₂]
  · simpa [h₁, h₂]

中文:
定理 eq_of_bisim'
  结论: {s₁ s₂ : 序列 α}
  证明: by
  apply eq_of_bisim motive _ base
  intro s₁ s₂ h
  rcases step s₁ s₂ h with ⟨h_nil₁, h_nil₂⟩ | ⟨_, _, _, h₁, h₂, _⟩
  · simp [h_nil₁, h_nil₂]
  · simpa [h₁, h₂]

Depends on / 依赖: eq_of_bisim, motive
-/
theorem eq_of_bisim' {s₁ s₂ : Seq α}
    (motive : Seq α -> Seq α -> Prop)
    (base : motive s₁ s₂)
    (step : forall s₁ s₂, motive s₁ s₂ ->
      (s₁ = nil ∧ s₂ = nil) ∨
      (exists x s₁' s₂', s₁ = cons x s₁' ∧ s₂ = cons x s₂' ∧ motive s₁' s₂')) :
    s₁ = s₂ := by
  apply eq_of_bisim motive _ base
  intro s₁ s₂ h
  rcases step s₁ s₂ h with ⟨h_nil₁, h_nil₂⟩ | ⟨_, _, _, h₁, h₂, _⟩
  · simp [h_nil₁, h_nil₂]
  · simpa [h₁, h₂]

/--
theorem `eq_of_bisim_strong` / 定理 `eq_of_bisim_strong`

English:
theorem eq_of_bisim_strong
  statement: {s₁ s₂ : Seq α}
  proof: by
  let motive' : Seq α -> Seq α -> Prop := fun s₁ s₂ => s₁ = s₂ ∨ motive s₁ s₂
  apply eq_of_bisim' motive' (by grind)
  intro s₁ s₂ ih
  simp only [motive'] at ih ⊢
  rcases ih with (rfl | ih)
  · cases s₁ <;> grind
  rcases step s₁ s₂ ih with (rfl | ⟨hd, s₁', s₂', _⟩)
  · cases s₁ <;> grind
  · grind

中文:
定理 eq_of_bisim_strong
  结论: {s₁ s₂ : 序列 α}
  证明: by
  let motive' : Seq α -> Seq α -> Prop := fun s₁ s₂ => s₁ = s₂ ∨ motive s₁ s₂
  apply eq_of_bisim' motive' (by grind)
  intro s₁ s₂ ih
  simp only [motive'] at ih ⊢
  rcases ih with (rfl | ih)
  · cases s₁ <;> grind
  rcases step s₁ s₂ ih with (rfl | ⟨hd, s₁', s₂', _⟩)
  · cases s₁ <;> grind
  · grind

Depends on / 依赖: eq_of_bisim, motive
-/
theorem eq_of_bisim_strong {s₁ s₂ : Seq α}
    (motive : Seq α -> Seq α -> Prop)
    (base : motive s₁ s₂)
    (step : forall s₁ s₂, motive s₁ s₂ ->
      (s₁ = s₂) ∨
      (exists x s₁' s₂', s₁ = cons x s₁' ∧ s₂ = cons x s₂' ∧ (motive s₁' s₂'))) : s₁ = s₂ := by
  let motive' : Seq α -> Seq α -> Prop := fun s₁ s₂ => s₁ = s₂ ∨ motive s₁ s₂
  apply eq_of_bisim' motive' (by grind)
  intro s₁ s₂ ih
  simp only [motive'] at ih ⊢
  rcases ih with (rfl | ih)
  · cases s₁ <;> grind
  rcases step s₁ s₂ ih with (rfl | ⟨hd, s₁', s₂', _⟩)
  · cases s₁ <;> grind
  · grind

end Bisim

/--
theorem `coinduction` / 定理 `coinduction`

English:
theorem coinduction

中文:
定理 coinduction
-/
theorem coinduction :
    forall {s₁ s₂ : Seq α},
      head s₁ = head s₂ ->
        (forall (β : Type u) (fr : Seq α -> β), fr s₁ = fr s₂ -> fr (tail s₁) = fr (tail s₂)) -> s₁ = s₂
  | _, _, hh, ht =>
    Subtype.ext (Stream'.coinduction hh fun β fr => ht β fun s => fr s.1)

/--
theorem `coinduction2` / 定理 `coinduction2`

English:
theorem coinduction2
  statement: (s) (f g : Seq α -> Seq β)
  proof: by
  refine eq_of_bisim (fun s1 s2 => exists s, s1 = f s ∧ s2 = g s) ?_ ⟨s, rfl, rfl⟩
  intro s1 s2 h; rcases h with ⟨s, h1, h2⟩
  rw [h1]; rw [h2]; apply H

中文:
定理 coinduction2
  结论: (s) (f g : 序列 α -> 序列 β)
  证明: by
  refine eq_of_bisim (fun s1 s2 => exists s, s1 = f s ∧ s2 = g s) ?_ ⟨s, rfl, rfl⟩
  intro s1 s2 h; rcases h with ⟨s, h1, h2⟩
  rw [h1]; rw [h2]; apply H

Depends on / 依赖: eq_of_bisim
-/
theorem coinduction2 (s) (f g : Seq α -> Seq β)
    (H :
      forall s,
        BisimO (fun s1 s2 : Seq β => exists s : Seq α, s1 = f s ∧ s2 = g s) (destruct (f s))
          (destruct (g s))) :
    f s = g s := by
  refine eq_of_bisim (fun s1 s2 => exists s, s1 = f s ∧ s2 = g s) ?_ ⟨s, rfl, rfl⟩
  intro s1 s2 h; rcases h with ⟨s, h1, h2⟩
  rw [h1]; rw [h2]; apply H

/-!
### Termination
-/

/--
Definition of `TerminatedAt` / `TerminatedAt` 的定义

English:
definition TerminatedAt
  signature: (s : Seq α) (n : Nat)
  body: s.get? n = none

中文:
定义 TerminatedAt
  签名: (s : 序列 α) (n : 自然数)
  定义体: s.get? n = none

Depends on / 依赖: s.get
-/
def TerminatedAt (s : Seq α) (n : Nat) : Prop :=
  s.get? n = none

/--
Instance `terminatedAtDecidable` / 实例 `terminatedAtDecidable`

English:
instance terminatedAtDecidable
  signature: (s : Seq α) (n : Nat)
  body: decidable_of_iff' (s.get? n).isNone by unfold TerminatedAt; cases s.get? n <;> simp

中文:
实例 terminatedAtDecidable
  签名: (s : 序列 α) (n : 自然数)
  定义体: decidable_of_iff' (s.get? n).isNone by unfold TerminatedAt; cases s.get? n <;> simp

Depends on / 依赖: TerminatedAt, decidable_of_iff, isNone, s.get
-/
instance terminatedAtDecidable (s : Seq α) (n : Nat) : Decidable (s.TerminatedAt n) :=
decidable_of_iff' (s.get? n).isNone by unfold TerminatedAt; cases s.get? n <;> simp

/--
Definition of `Terminates` / `Terminates` 的定义

English:
definition Terminates
  signature: (s : Seq α)
  body: exists n : Nat, s.TerminatedAt n

中文:
定义 Terminates
  签名: (s : 序列 α)
  定义体: exists n : Nat, s.TerminatedAt n

Depends on / 依赖: TerminatedAt, s.TerminatedAt
-/
def Terminates (s : Seq α) : Prop :=
  exists n : Nat, s.TerminatedAt n

/--
Definition of `length` / `length` 的定义

English:
definition length
  signature: (s : Seq α) (h : s.Terminates)
  body: Nat.find h

中文:
定义 length
  签名: (s : 序列 α) (h : s.Terminates)
  定义体: Nat.find h

Depends on / 依赖: Nat.find
-/
def length (s : Seq α) (h : s.Terminates) : Nat :=
  Nat.find h

open scoped Classical in
/--
Definition of `length'` / `length'` 的定义

English:
definition length'
  signature: (s : Seq α)
  body: if h : s.Terminates then s.length h else ⊤

中文:
定义 length'
  签名: (s : 序列 α)
  定义体: if h : s.Terminates then s.length h else ⊤
-/
noncomputable def length' (s : Seq α) : Nat∞ :=
  if h : s.Terminates then s.length h else ⊤

/--
theorem `terminated_stable` / 定理 `terminated_stable`

English:
theorem terminated_stable
  statement: forall (s : Seq α) {m n : Nat}, m <= n -> s.TerminatedAt m -> s.TerminatedAt n
  proof: le_stable

中文:
定理 terminated_stable
  结论: 对任意 (s : 序列 α) {m n : 自然数}, m <= n -> s.TerminatedAt m -> s.TerminatedAt n
  证明: le_stable

Depends on / 依赖: le_stable
-/
theorem terminated_stable : forall (s : Seq α) {m n : Nat}, m <= n -> s.TerminatedAt m -> s.TerminatedAt n :=
  le_stable

/--
theorem `not_terminates_iff` / 定理 `not_terminates_iff`

English:
theorem not_terminates_iff
  given: {s : Seq α}
  statement: ¬s.Terminates ↔ forall n, (s.get? n).isSome
  proof: by
  simp only [Terminates, TerminatedAt, ← Ne.eq_def, Option.ne_none_iff_isSome, not_exists, iff_self]

中文:
定理 not_terminates_iff
  条件: {s : 序列 α}
  结论: ¬s.Terminates ↔ 对任意 n, (s.get? n).isSome
  证明: by
  simp only [Terminates, TerminatedAt, ← Ne.eq_def, Option.ne_none_iff_isSome, not_exists, iff_self]

Depends on / 依赖: Ne.eq_def, Option.ne_none_iff_isSome, TerminatedAt, Terminates, eq_def, iff_self, ne_none_iff_isSome, not_exists
-/
theorem not_terminates_iff {s : Seq α} : ¬s.Terminates ↔ forall n, (s.get? n).isSome := by
  simp only [Terminates, TerminatedAt, ← Ne.eq_def, Option.ne_none_iff_isSome, not_exists, iff_self]

/--
theorem `terminatedAt_nil` / 定理 `terminatedAt_nil`

English:
theorem terminatedAt_nil
  given: {n : Nat}
  statement: TerminatedAt (nil : Seq α) n
  proof: rfl

@[simp]

中文:
定理 terminatedAt_nil
  条件: {n : 自然数}
  结论: TerminatedAt (nil : 序列 α) n
  证明: rfl

@[simp]
-/
theorem terminatedAt_nil {n : Nat} : TerminatedAt (nil : Seq α) n := rfl

@[simp]
/--
theorem `cons_not_terminatedAt_zero` / 定理 `cons_not_terminatedAt_zero`

English:
theorem cons_not_terminatedAt_zero
  given: {x : α} {s : Seq α}
  proof: by
  simp [TerminatedAt]

@[simp]

中文:
定理 cons_not_terminatedAt_zero
  条件: {x : α} {s : 序列 α}
  证明: by
  simp [TerminatedAt]

@[simp]

Depends on / 依赖: TerminatedAt
-/
theorem cons_not_terminatedAt_zero {x : α} {s : Seq α} :
    ¬(cons x s).TerminatedAt 0 := by
  simp [TerminatedAt]

@[simp]
/--
theorem `cons_terminatedAt_succ_iff` / 定理 `cons_terminatedAt_succ_iff`

English:
theorem cons_terminatedAt_succ_iff
  given: {x : α} {s : Seq α} {n : Nat}
  proof: by
  simp [TerminatedAt]

@[simp]

中文:
定理 cons_terminatedAt_succ_iff
  条件: {x : α} {s : 序列 α} {n : 自然数}
  证明: by
  simp [TerminatedAt]

@[simp]

Depends on / 依赖: TerminatedAt, h.toBumpCovering.toPartitionOfUnity, toBumpCovering, toPartitionOfUnity
-/
theorem cons_terminatedAt_succ_iff {x : α} {s : Seq α} {n : Nat} :
    (cons x s).TerminatedAt (n + 1) ↔ s.TerminatedAt n := by
  simp [TerminatedAt]

@[simp]
/--
theorem `terminates_nil` / 定理 `terminates_nil`

English:
theorem terminates_nil
  statement: Terminates (nil : Seq α)
  proof: ⟨0, rfl⟩

@[simp]

中文:
定理 terminates_nil
  结论: Terminates (nil : 序列 α)
  证明: ⟨0, rfl⟩

@[simp]
-/
theorem terminates_nil : Terminates (nil : Seq α) := ⟨0, rfl⟩

@[simp]
/--
theorem `terminates_cons_iff` / 定理 `terminates_cons_iff`

English:
theorem terminates_cons_iff
  given: {x : α} {s : Seq α}
  proof: by
  constructor <;> intro ⟨n, h⟩
  · exact ⟨n, cons_terminatedAt_succ_iff.mp (terminated_stable _ (Nat.le_succ _) h)⟩
  · exact ⟨n + 1, cons_terminatedAt_succ_iff.mpr h⟩

中文:
定理 terminates_cons_iff
  条件: {x : α} {s : 序列 α}
  证明: by
  constructor <;> intro ⟨n, h⟩
  · exact ⟨n, cons_terminatedAt_succ_iff.mp (terminated_stable _ (Nat.le_succ _) h)⟩
  · exact ⟨n + 1, cons_terminatedAt_succ_iff.mpr h⟩

Depends on / 依赖: Nat.le_succ, cons_terminatedAt_succ_iff, cons_terminatedAt_succ_iff.mp, cons_terminatedAt_succ_iff.mpr, le_succ, terminated_stable
-/
theorem terminates_cons_iff {x : α} {s : Seq α} :
    (cons x s).Terminates ↔ s.Terminates := by
  constructor <;> intro ⟨n, h⟩
  · exact ⟨n, cons_terminatedAt_succ_iff.mp (terminated_stable _ (Nat.le_succ _) h)⟩
  · exact ⟨n + 1, cons_terminatedAt_succ_iff.mpr h⟩

/--
theorem `terminatedAt_zero_iff` / 定理 `terminatedAt_zero_iff`

English:
theorem terminatedAt_zero_iff
  given: {s : Seq α}
  statement: s.TerminatedAt 0 ↔ s = nil
  proof: by
  refine ⟨?_, ?_⟩
  · intro h
    ext n
    rw [le_stable _ (Nat.zero_le _) h]
    simp
  · rintro rfl
    simp [TerminatedAt]

中文:
定理 terminatedAt_zero_iff
  条件: {s : 序列 α}
  结论: s.TerminatedAt 0 ↔ s = nil
  证明: by
  refine ⟨?_, ?_⟩
  · intro h
    ext n
    rw [le_stable _ (Nat.zero_le _) h]
    simp
  · rintro rfl
    simp [TerminatedAt]

Depends on / 依赖: Nat.zero_le, TerminatedAt, le_stable, zero_le
-/
theorem terminatedAt_zero_iff {s : Seq α} : s.TerminatedAt 0 ↔ s = nil := by
  refine ⟨?_, ?_⟩
  · intro h
    ext n
    rw [le_stable _ (Nat.zero_le _) h]
    simp
  · rintro rfl
    simp [TerminatedAt]

/-!
### Membership
-/

/--
Definition of `Mem` / `Mem` 的定义

English:
definition Mem
  signature: (s : Seq α) (a : α)
  body: some a in s.1

中文:
定义 Mem
  签名: (s : 序列 α) (a : α)
  定义体: some a in s.1
-/
protected def Mem (s : Seq α) (a : α) :=
  some a in s.1

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Membership α (Seq α)
  body: ⟨Seq.Mem⟩

中文:
实例 :
  签名: Membership α (序列 α)
  定义体: ⟨Seq.Mem⟩

Depends on / 依赖: Seq.Mem
-/
instance : Membership α (Seq α) :=
  ⟨Seq.Mem⟩

-- Cannot be @[simp] because `n` can not be inferred by `simp`.
/--
theorem `get?_mem` / 定理 `get?_mem`

English:
theorem get?_mem
  given: {s : Seq α} {n : Nat} {x : α} (h : s.get? n = .some x)
  statement: x in s
  proof: ⟨n, h.symm⟩

中文:
定理 get?_mem
  条件: {s : 序列 α} {n : 自然数} {x : α} (h : s.get? n = .some x)
  结论: x in s
  证明: ⟨n, h.symm⟩
-/
theorem get?_mem {s : Seq α} {n : Nat} {x : α} (h : s.get? n = .some x) : x in s := ⟨n, h.symm⟩

/--
theorem `mem_iff_exists_get?` / 定理 `mem_iff_exists_get?`

English:
theorem mem_iff_exists_get?
  given: {s : Seq α} {x : α}
  statement: x in s ↔ exists i, some x = s.get? i where
  proof: by
    change (some x in s.1) at h
    rwa [Stream'.mem_iff_exists_get_eq] at h
  mpr h := get?_mem h.choose_spec.symm

@[simp]

中文:
定理 mem_iff_存在_get?
  条件: {s : 序列 α} {x : α}
  结论: x in s ↔ 存在 i, some x = s.get? i where
  证明: by
    change (some x in s.1) at h
    rwa [Stream'.mem_iff_exists_get_eq] at h
  mpr h := get?_mem h.choose_spec.symm

@[simp]

Depends on / 依赖: Stream, _mem, choose_spec, h.choose_spec.symm, mem_iff_exists_get_eq
-/
theorem mem_iff_exists_get? {s : Seq α} {x : α} : x in s ↔ exists i, some x = s.get? i where
  mp h := by
    change (some x in s.1) at h
    rwa [Stream'.mem_iff_exists_get_eq] at h
  mpr h := get?_mem h.choose_spec.symm

@[simp]
/--
theorem `notMem_nil` / 定理 `notMem_nil`

English:
theorem notMem_nil
  given: (a : α)
  statement: a ∉ @nil α
  proof: fun ⟨_, (h : some a = none)⟩ => by injection h

中文:
定理 notMem_nil
  条件: (a : α)
  结论: a ∉ @nil α
  证明: fun ⟨_, (h : some a = none)⟩ => by injection h

Depends on / 依赖: injection
-/
theorem notMem_nil (a : α) : a ∉ @nil α := fun ⟨_, (h : some a = none)⟩ => by injection h

/--
theorem `mem_cons` / 定理 `mem_cons`

English:
theorem mem_cons
  given: (a : α)
  statement: forall s : Seq α, a in cons a s

中文:
定理 mem_cons
  条件: (a : α)
  结论: 对任意 s : 序列 α, a in cons a s
-/
theorem mem_cons (a : α) : forall s : Seq α, a in cons a s
  | ⟨_, _⟩ => Stream'.mem_cons (some a) _

/--
theorem `mem_cons_of_mem` / 定理 `mem_cons_of_mem`

English:
theorem mem_cons_of_mem
  given: (y : α) {a : α}
  statement: forall {s : Seq α}, a in s -> a in cons y s

中文:
定理 mem_cons_of_mem
  条件: (y : α) {a : α}
  结论: 对任意 {s : 序列 α}, a in s -> a in cons y s
-/
theorem mem_cons_of_mem (y : α) {a : α} : forall {s : Seq α}, a in s -> a in cons y s
  | ⟨_, _⟩ => Stream'.mem_cons_of_mem (some y)

/--
theorem `eq_or_mem_of_mem_cons` / 定理 `eq_or_mem_of_mem_cons`

English:
theorem eq_or_mem_of_mem_cons
  given: {a b : α}
  statement: forall {s : Seq α}, a in cons b s -> a = b ∨ a in s

中文:
定理 eq_or_mem_of_mem_cons
  条件: {a b : α}
  结论: 对任意 {s : 序列 α}, a in cons b s -> a = b ∨ a in s
-/
theorem eq_or_mem_of_mem_cons {a b : α} : forall {s : Seq α}, a in cons b s -> a = b ∨ a in s
  | ⟨_, _⟩, h => (Stream'.eq_or_mem_of_mem_cons h).imp_left fun h => by injection h

@[simp]
/--
theorem `mem_cons_iff` / 定理 `mem_cons_iff`

English:
theorem mem_cons_iff
  given: {a b : α} {s : Seq α}
  statement: a in cons b s ↔ a = b ∨ a in s
  proof: ⟨eq_or_mem_of_mem_cons, by rintro (rfl | m) <;> [apply mem_cons; exact mem_cons_of_mem _ m]⟩

中文:
定理 mem_cons_iff
  条件: {a b : α} {s : 序列 α}
  结论: a in cons b s ↔ a = b ∨ a in s
  证明: ⟨eq_or_mem_of_mem_cons, by rintro (rfl | m) <;> [apply mem_cons; exact mem_cons_of_mem _ m]⟩

Depends on / 依赖: eq_or_mem_of_mem_cons, mem_cons, mem_cons_of_mem
-/
theorem mem_cons_iff {a b : α} {s : Seq α} : a in cons b s ↔ a = b ∨ a in s :=
  ⟨eq_or_mem_of_mem_cons, by rintro (rfl | m) <;> [apply mem_cons; exact mem_cons_of_mem _ m]⟩

/--
theorem `mem_rec_on` / 定理 `mem_rec_on`

English:
theorem mem_rec_on
  statement: {C : Seq α -> Prop} {a s} (M : a in s)
  proof: by
  obtain ⟨k, e⟩ := M; unfold Stream'.get at e
  induction k generalizing s with
  | zero =>
    have TH : s = cons a (tail s) := by
      apply destruct_eq_cons
      unfold destruct get? Functor.map
      rw [← e]
      rfl
    rw [TH]
    apply h1 _ _ (Or.inl rfl)
  | succ k IH =>
    cases s with
    | nil => injection e
    | cons b s' =>
      have h_eq : (cons b s').val (Nat.succ k) = s'.val k := by cases s' using Subtype.recOn; rfl
      rw [h_eq] at e
      apply h1 _ _ (Or.inr (IH e))

中文:
定理 mem_rec_on
  结论: {C : 序列 α -> 命题} {a s} (M : a in s)
  证明: by
  obtain ⟨k, e⟩ := M; unfold Stream'.get at e
  induction k generalizing s with
  | zero =>
    have TH : s = cons a (tail s) := by
      apply destruct_eq_cons
      unfold destruct get? Functor.map
      rw [← e]
      rfl
    rw [TH]
    apply h1 _ _ (Or.inl rfl)
  | succ k IH =>
    cases s with
    | nil => injection e
    | cons b s' =>
      have h_eq : (cons b s').val (Nat.succ k) = s'.val k := by cases s' using Subtype.recOn; rfl
      rw [h_eq] at e
      apply h1 _ _ (Or.inr (IH e))

Depends on / 依赖: Functor, Functor.map, Nat.succ, Or.inl, Or.inr, Stream, Subtype, Subtype.recOn, destruct, destruct_eq_cons, generalizing, h_eq, injection
-/
theorem mem_rec_on {C : Seq α -> Prop} {a s} (M : a in s)
    (h1 : forall b s', a = b ∨ C s' -> C (cons b s')) : C s := by
  obtain ⟨k, e⟩ := M; unfold Stream'.get at e
  induction k generalizing s with
  | zero =>
    have TH : s = cons a (tail s) := by
      apply destruct_eq_cons
      unfold destruct get? Functor.map
      rw [← e]
      rfl
    rw [TH]
    apply h1 _ _ (Or.inl rfl)
  | succ k IH =>
    cases s with
    | nil => injection e
    | cons b s' =>
      have h_eq : (cons b s').val (Nat.succ k) = s'.val k := by cases s' using Subtype.recOn; rfl
      rw [h_eq] at e
      apply h1 _ _ (Or.inr (IH e))

/-!
### Converting from/to other types
-/

/-- Embed a list as a sequence -/
@[coe]
/--
Definition of `ofList` / `ofList` 的定义

English:
definition ofList
  signature: (l : List α)
  body: ⟨(l[·]?), fun {n} h => by
    rw [List.getElem?_eq_none_iff] at h ⊢
    exact Nat.le_succ_of_le h⟩

中文:
定义 ofList
  签名: (l : 列表 α)
  定义体: ⟨(l[·]?), fun {n} h => by
    rw [List.getElem?_eq_none_iff] at h ⊢
    exact Nat.le_succ_of_le h⟩

Depends on / 依赖: List.getElem, Nat.le_succ_of_le, _eq_none_iff, getElem, le_succ_of_le
-/
def ofList (l : List α) : Seq α :=
  ⟨(l[·]?), fun {n} h => by
    rw [List.getElem?_eq_none_iff] at h ⊢
    exact Nat.le_succ_of_le h⟩

/--
Instance `coeList` / 实例 `coeList`

English:
instance coeList
  signature: : Coe (List α) (Seq α)
  body: ⟨ofList⟩

@[simp]

中文:
实例 coeList
  签名: : Coe (列表 α) (序列 α)
  定义体: ⟨ofList⟩

@[simp]

Depends on / 依赖: ofList
-/
instance coeList : Coe (List α) (Seq α) :=
  ⟨ofList⟩

@[simp]
/--
theorem `ofList_nil` / 定理 `ofList_nil`

English:
theorem ofList_nil
  statement: ofList [] = (nil : Seq α)
  proof: rfl

@[simp]

中文:
定理 ofList_nil
  结论: ofList [] = (nil : 序列 α)
  证明: rfl

@[simp]
-/
theorem ofList_nil : ofList [] = (nil : Seq α) :=
  rfl

@[simp]
/--
theorem `ofList_get?` / 定理 `ofList_get?`

English:
theorem ofList_get?
  given: (l : List α) (n : Nat)
  statement: (ofList l).get? n = l[n]?
  proof: rfl

@[simp]

中文:
定理 ofList_get?
  条件: (l : 列表 α) (n : 自然数)
  结论: (ofList l).get? n = l[n]?
  证明: rfl

@[simp]
-/
theorem ofList_get? (l : List α) (n : Nat) : (ofList l).get? n = l[n]? :=
  rfl

@[simp]
/--
theorem `ofList_cons` / 定理 `ofList_cons`

English:
theorem ofList_cons
  given: (a : α) (l : List α)
  statement: ofList (a::l) = cons a (ofList l)
  proof: by
  ext1 (_ | n) <;> simp

中文:
定理 ofList_cons
  条件: (a : α) (l : 列表 α)
  结论: ofList (a::l) = cons a (ofList l)
  证明: by
  ext1 (_ | n) <;> simp
-/
theorem ofList_cons (a : α) (l : List α) : ofList (a::l) = cons a (ofList l) := by
  ext1 (_ | n) <;> simp

/--
theorem `ofList_injective` / 定理 `ofList_injective`

English:
theorem ofList_injective
  statement: Function.Injective (ofList : List α -> _)
  proof: fun _ _ h => List.ext_getElem? fun _ => congr_fun (Subtype.ext_iff.1 h) _

中文:
定理 ofList_injective
  结论: 函数.单射 (ofList : 列表 α -> _)
  证明: fun _ _ h => List.ext_getElem? fun _ => congr_fun (Subtype.ext_iff.1 h) _

Depends on / 依赖: List.ext_getElem, Subtype, Subtype.ext_iff, congr_fun, ext_getElem, ext_iff
-/
theorem ofList_injective : Function.Injective (ofList : List α -> _) :=
  fun _ _ h => List.ext_getElem? fun _ => congr_fun (Subtype.ext_iff.1 h) _

/-- Embed an infinite stream as a sequence -/
@[coe]
/--
Definition of `ofStream` / `ofStream` 的定义

English:
definition ofStream
  signature: (s : Stream' α)
  body: ⟨s.map some, fun {n} h => by contradiction⟩

中文:
定义 ofStream
  签名: (s : Stream' α)
  定义体: ⟨s.map some, fun {n} h => by contradiction⟩

Depends on / 依赖: s.map
-/
def ofStream (s : Stream' α) : Seq α :=
  ⟨s.map some, fun {n} h => by contradiction⟩

/--
Instance `coeStream` / 实例 `coeStream`

English:
instance coeStream
  signature: : Coe (Stream' α) (Seq α)
  body: ⟨ofStream⟩

中文:
实例 coeStream
  签名: : Coe (Stream' α) (序列 α)
  定义体: ⟨ofStream⟩

Depends on / 依赖: ofStream
-/
instance coeStream : Coe (Stream' α) (Seq α) :=
  ⟨ofStream⟩

section MLList

/--
Definition of `ofMLList` / `ofMLList` 的定义

English:
definition ofMLList
  signature: : MLList Id α -> Seq α
  body: corec fun l =>
    match l.uncons with
    | .none => none
    | .some (a, l') => some (a, l')

中文:
定义 ofMLList
  签名: : MLList Id α -> 序列 α
  定义体: corec fun l =>
    match l.uncons with
    | .none => none
    | .some (a, l') => some (a, l')

Depends on / 依赖: l.uncons, uncons
-/
def ofMLList : MLList Id α -> Seq α :=
  corec fun l =>
    match l.uncons with
    | .none => none
    | .some (a, l') => some (a, l')

/--
Instance `coeMLList` / 实例 `coeMLList`

English:
instance coeMLList
  signature: : Coe (MLList Id α) (Seq α)
  body: ⟨ofMLList⟩

中文:
实例 coeMLList
  签名: : Coe (MLList Id α) (序列 α)
  定义体: ⟨ofMLList⟩

Depends on / 依赖: ofMLList
-/
instance coeMLList : Coe (MLList Id α) (Seq α) :=
  ⟨ofMLList⟩

/-- Translate a sequence into a `MLList`. -/
unsafe def toMLList : Seq α -> MLList Id α
  | s =>
    match destruct s with
    | none => .nil
    | some (a, s') => .cons a (toMLList s')

end MLList

/-- Translate a sequence to a list. This function will run forever if
  run on an infinite sequence. -/
unsafe def forceToList (s : Seq α) : List α :=
  (toMLList s).force

/--
Definition of `take` / `take` 的定义

English:
definition take
  signature: : Nat -> Seq α -> List α

中文:
定义 take
  签名: : 自然数 -> 序列 α -> 列表 α
-/
def take : Nat -> Seq α -> List α
  | 0, _ => []
  | n + 1, s =>
    match destruct s with
    | none => []
    | some (x, r) => List.cons x (take n r)

/--
Definition of `toList` / `toList` 的定义

English:
definition toList
  signature: (s : Seq α) (h : s.Terminates)
  body: take (length s h) s

中文:
定义 toList
  签名: (s : 序列 α) (h : s.Terminates)
  定义体: take (length s h) s

Depends on / 依赖: length
-/
def toList (s : Seq α) (h : s.Terminates) : List α :=
  take (length s h) s

/--
Definition of `toStream` / `toStream` 的定义

English:
definition toStream
  signature: (s : Seq α) (h : ¬s.Terminates)
  body: fun n =>
Option.get _ not_terminates_iff.1 h n

中文:
定义 toStream
  签名: (s : 序列 α) (h : ¬s.Terminates)
  定义体: fun n =>
Option.get _ not_terminates_iff.1 h n
-/
def toStream (s : Seq α) (h : ¬s.Terminates) : Stream' α := fun n =>
Option.get _ not_terminates_iff.1 h n

/--
Definition of `toListOrStream` / `toListOrStream` 的定义

English:
definition toListOrStream
  signature: (s : Seq α) [Decidable s.Terminates]
  body: if h : s.Terminates then Sum.inl (toList s h) else Sum.inr (toStream s h)

中文:
定义 toListOrStream
  签名: (s : 序列 α) [可判定 s.Terminates]
  定义体: if h : s.Terminates then Sum.inl (toList s h) else Sum.inr (toStream s h)

Depends on / 依赖: Sum.inl, Sum.inr, Terminates, s.Terminates, toList, toStream
-/
def toListOrStream (s : Seq α) [Decidable s.Terminates] : List α oplus Stream' α :=
  if h : s.Terminates then Sum.inl (toList s h) else Sum.inr (toStream s h)

/--
Definition of `toList'` / `toList'` 的定义

English:
definition toList'
  signature: {α} (s : Seq α)
  body: @Computation.corec (List α) (List α × Seq α)
    (fun ⟨l, s⟩ =>
      match destruct s with
      | none => Sum.inl l.reverse
      | some (a, s') => Sum.inr (a::l, s'))
    ([], s)

中文:
定义 toList'
  签名: {α} (s : 序列 α)
  定义体: @Computation.corec (List α) (List α × Seq α)
    (fun ⟨l, s⟩ =>
      match destruct s with
      | none => Sum.inl l.reverse
      | some (a, s') => Sum.inr (a::l, s'))
    ([], s)

Depends on / 依赖: Computation, Computation.corec, Sum.inl, Sum.inr, destruct, l.reverse, reverse
-/
def toList' {α} (s : Seq α) : Computation (List α) :=
  @Computation.corec (List α) (List α × Seq α)
    (fun ⟨l, s⟩ =>
      match destruct s with
      | none => Sum.inl l.reverse
      | some (a, s') => Sum.inr (a::l, s'))
    ([], s)

/-!
### Operations on sequences
-/

/--
Definition of `append` / `append` 的定义

English:
definition append
  signature: (s₁ s₂ : Seq α)
  body: @corec α (Seq α × Seq α)
    (fun ⟨s₁, s₂⟩ =>
      match destruct s₁ with
      | none => omap (fun s₂ => (nil, s₂)) (destruct s₂)
      | some (a, s₁') => some (a, s₁', s₂))
    (s₁, s₂)

中文:
定义 append
  签名: (s₁ s₂ : 序列 α)
  定义体: @corec α (Seq α × Seq α)
    (fun ⟨s₁, s₂⟩ =>
      match destruct s₁ with
      | none => omap (fun s₂ => (nil, s₂)) (destruct s₂)
      | some (a, s₁') => some (a, s₁', s₂))
    (s₁, s₂)

Depends on / 依赖: destruct
-/
def append (s₁ s₂ : Seq α) : Seq α :=
  @corec α (Seq α × Seq α)
    (fun ⟨s₁, s₂⟩ =>
      match destruct s₁ with
      | none => omap (fun s₂ => (nil, s₂)) (destruct s₂)
      | some (a, s₁') => some (a, s₁', s₂))
    (s₁, s₂)

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : α -> β)

中文:
定义 map
  签名: (f : α -> β)

Depends on / 依赖: members, s.members
-/
def map (f : α -> β) : Seq α -> Seq β
  | ⟨s, al⟩ =>
    ⟨s.map (Option.map f), fun {n} => by
      dsimp [Stream'.map, Stream'.get]
      rcases e : s n with - | e <;> intro
      · rw [al e]
        assumption
      · contradiction⟩

/--
Definition of `join` / `join` 的定义

English:
definition join
  signature: : Seq (Seq1 α) -> Seq α
  body: corec fun S =>
    match destruct S with
    | none => none
    | some ((a, s), S') =>
      some
        (a,
          match destruct s with
          | none => S'
          | some s' => cons s' S')

中文:
定义 join
  签名: : 序列 (Seq1 α) -> 序列 α
  定义体: corec fun S =>
    match destruct S with
    | none => none
    | some ((a, s), S') =>
      some
        (a,
          match destruct s with
          | none => S'
          | some s' => cons s' S')

Depends on / 依赖: destruct
-/
def join : Seq (Seq1 α) -> Seq α :=
  corec fun S =>
    match destruct S with
    | none => none
    | some ((a, s), S') =>
      some
        (a,
          match destruct s with
          | none => S'
          | some s' => cons s' S')

/--
Definition of `drop` / `drop` 的定义

English:
definition drop
  signature: (s : Seq α)

中文:
定义 drop
  签名: (s : 序列 α)
-/
def drop (s : Seq α) : Nat -> Seq α
  | 0 => s
  | n + 1 => tail (drop s n)

/--
Definition of `splitAt` / `splitAt` 的定义

English:
definition splitAt
  signature: : Nat -> Seq α -> List α × Seq α
  body: splitAt n s'
      (List.cons x l, r)

中文:
定义 splitAt
  签名: : 自然数 -> 序列 α -> 列表 α × 序列 α
  定义体: splitAt n s'
      (List.cons x l, r)

Depends on / 依赖: splitAt
-/
def splitAt : Nat -> Seq α -> List α × Seq α
  | 0, s => ([], s)
  | n + 1, s =>
    match destruct s with
    | none => ([], nil)
    | some (x, s') =>
      let (l, r) := splitAt n s'
      (List.cons x l, r)

/--
Definition of `zipWith` / `zipWith` 的定义

English:
definition zipWith
  signature: (f : α -> β -> γ) (s₁ : Seq α) (s₂ : Seq β)
  body: ⟨fun n => Option.map₂ f (s₁.get? n) (s₂.get? n), fun {_} hn =>
Option.map₂_eq_none_iff.2 (Option.map₂_eq_none_iff.1 hn).imp s₁.2 s₂.2⟩

中文:
定义 zipWith
  签名: (f : α -> β -> γ) (s₁ : 序列 α) (s₂ : 序列 β)
  定义体: ⟨fun n => Option.map₂ f (s₁.get? n) (s₂.get? n), fun {_} hn =>
Option.map₂_eq_none_iff.2 (Option.map₂_eq_none_iff.1 hn).imp s₁.2 s₂.2⟩

Depends on / 依赖: Option.map
-/
def zipWith (f : α -> β -> γ) (s₁ : Seq α) (s₂ : Seq β) : Seq γ :=
  ⟨fun n => Option.map₂ f (s₁.get? n) (s₂.get? n), fun {_} hn =>
Option.map₂_eq_none_iff.2 (Option.map₂_eq_none_iff.1 hn).imp s₁.2 s₂.2⟩

/--
Definition of `zip` / `zip` 的定义

English:
definition zip
  signature: : Seq α -> Seq β -> Seq (α × β)
  body: zipWith Prod.mk

中文:
定义 zip
  签名: : 序列 α -> 序列 β -> 序列 (α × β)
  定义体: zipWith Prod.mk

Depends on / 依赖: Prod.mk, zipWith
-/
def zip : Seq α -> Seq β -> Seq (α × β) :=
  zipWith Prod.mk

/--
Definition of `unzip` / `unzip` 的定义

English:
definition unzip
  signature: (s : Seq (α × β))
  body: (map Prod.fst s, map Prod.snd s)

中文:
定义 unzip
  签名: (s : 序列 (α × β))
  定义体: (map Prod.fst s, map Prod.snd s)

Depends on / 依赖: Prod.fst, Prod.snd
-/
def unzip (s : Seq (α × β)) : Seq α × Seq β :=
  (map Prod.fst s, map Prod.snd s)

/--
Definition of `nats` / `nats` 的定义

English:
definition nats
  signature: : Seq Nat
  body: Stream'.nats

中文:
定义 nats
  签名: : 序列 自然数
  定义体: Stream'.nats

Depends on / 依赖: Stream
-/
def nats : Seq Nat :=
  Stream'.nats

/--
Definition of `enum` / `enum` 的定义

English:
definition enum
  signature: (s : Seq α)
  body: Seq.zip nats s

中文:
定义 enum
  签名: (s : 序列 α)
  定义体: Seq.zip nats s

Depends on / 依赖: Seq.zip
-/
def enum (s : Seq α) : Seq (Nat × α) :=
  Seq.zip nats s

/--
Definition of `fold` / `fold` 的定义

English:
definition fold
  signature: (s : Seq α) (init : β) (f : β -> α -> β)
  body: let f : β × Seq α -> Option (β × (β × Seq α)) := fun (acc, x) =>
    match destruct x with
    | none => .none
    | some (x, s) => .some (f acc x, f acc x, s)
cons init corec f (init, s)

中文:
定义 fold
  签名: (s : 序列 α) (init : β) (f : β -> α -> β)
  定义体: let f : β × Seq α -> Option (β × (β × Seq α)) := fun (acc, x) =>
    match destruct x with
    | none => .none
    | some (x, s) => .some (f acc x, f acc x, s)
cons init corec f (init, s)

Depends on / 依赖: destruct
-/
def fold (s : Seq α) (init : β) (f : β -> α -> β) : Seq β :=
  let f : β × Seq α -> Option (β × (β × Seq α)) := fun (acc, x) =>
    match destruct x with
    | none => .none
    | some (x, s) => .some (f acc x, f acc x, s)
cons init corec f (init, s)

/--
Definition of `update` / `update` 的定义

English:
definition update
  signature: (s : Seq α) (n : Nat) (f : α -> α)
  body: Function.update s.val n ((s.val n).map f)
  property := by
    have (i : Nat) : Function.update s.val n ((s.get? n).map f) i = none ↔ s.get? i = none := by
      by_cases hi : i = n <;> simp [Function.update, hi]
    simp only [IsSeq, val_eq_get, this]
    exact @s.prop

中文:
定义 update
  签名: (s : 序列 α) (n : 自然数) (f : α -> α)
  定义体: Function.update s.val n ((s.val n).map f)
  property := by
    have (i : Nat) : Function.update s.val n ((s.get? n).map f) i = none ↔ s.get? i = none := by
      by_cases hi : i = n <;> simp [Function.update, hi]
    simp only [IsSeq, val_eq_get, this]
    exact @s.prop

Depends on / 依赖: Function, Function.update, s.val, update
-/
def update (s : Seq α) (n : Nat) (f : α -> α) : Seq α where
  val := Function.update s.val n ((s.val n).map f)
  property := by
    have (i : Nat) : Function.update s.val n ((s.get? n).map f) i = none ↔ s.get? i = none := by
      by_cases hi : i = n <;> simp [Function.update, hi]
    simp only [IsSeq, val_eq_get, this]
    exact @s.prop

/--
Definition of `set` / `set` 的定义

English:
definition set
  signature: (s : Seq α) (n : Nat) (a : α)
  body: update s n fun _ => a

中文:
定义 set
  签名: (s : 序列 α) (n : 自然数) (a : α)
  定义体: update s n fun _ => a

Depends on / 依赖: update
-/
def set (s : Seq α) (n : Nat) (a : α) : Seq α :=
  update s n fun _ => a

/--
Definition of `Pairwise` / `Pairwise` 的定义

English:
definition Pairwise
  signature: (R : α -> α -> Prop) (s : Seq α)
  body: forall i j, i < j -> forall x in s.get? i, forall y in s.get? j, R x y

中文:
定义 两两
  签名: (R : α -> α -> 命题) (s : 序列 α)
  定义体: forall i j, i < j -> forall x in s.get? i, forall y in s.get? j, R x y

Depends on / 依赖: s.get
-/
def Pairwise (R : α -> α -> Prop) (s : Seq α) : Prop :=
  forall i j, i < j -> forall x in s.get? i, forall y in s.get? j, R x y

end Seq

end Stream'
