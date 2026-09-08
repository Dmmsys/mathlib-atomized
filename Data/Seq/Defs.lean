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
/-- A stream `s : Option α` is a sequence if `s.get n = none` implies `s.get (n + 1) = none`.
-/
/-
**Stream.IsSeq** 是 Mathlib 中的一个定义，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A stream `s : Option α` is a sequence if `s.get n = none` implies `s.get (n + 1)
 = none`.
-/
def IsSeq {α : Type u} (s : Stream' (Option α)) : Prop :=
  ∀ {n : ℕ}, s n = none → s (n + 1) = none

/-- `Seq α` is the type of possibly infinite lists (referred here as sequences).
  It is encoded as an infinite stream of options such that if `f n = none`, then
  `f m = none` for all `m ≥ n`. -/
/-
**Stream.Seq** 是 Mathlib 中的一个定义，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Seq α` is the type of possibly infinite lists (referred here as sequences).
  It is encoded as an infinite stream of options such that if `f n = none`, then
  `f m = none` for all `m ≥ n`.
-/
def Seq (α : Type u) : Type u :=
  { f : Stream' (Option α) // f.IsSeq }

/-- `Seq1 α` is the type of nonempty sequences. -/
/-
**Stream.Seq1** 是 Mathlib 中的一个定义，位于命名空间 `Stream`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Seq1 α` is the type of nonempty sequences.
-/
def Seq1 (α) :=
  α × Seq α

namespace Seq

variable {α : Type u} {β : Type v} {γ : Type w}

/-- Get the nth element of a sequence (if it exists) -/
/-
**Stream.Seq.get** 是 Mathlib 中的一个定义，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Get the nth element of a sequence (if it exists)
-/
def get? : Seq α → ℕ → Option α :=
  Subtype.val

@[simp]
/-
**Stream.Seq.val_eq_get** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem val_eq_get (s : Seq α) (n : ℕ) : s.val n = s.get? n :=
  rfl

@[simp]
/-
**Stream.Seq.get** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem get?_mk (f hf) : @get? α ⟨f, hf⟩ = f :=
  rfl
/-
**Stream.Seq.le_stable** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem le_stable (s : Seq α) {m n} (h : m ≤ n) : s.get? m = none → s.get? n = none := by
  obtain ⟨f, al⟩ := s
  induction h with | refl => exact id | step _ IH => exact fun h2 ↦ al (IH h2)

/-- If `s.get? n = some aₙ` for some value `aₙ`, then there is also some value `aₘ` such
that `s.get? = some aₘ` for `m ≤ n`.
-/
/-
**Stream.Seq.ge_stable** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `s.get? n = some aₙ` for some value `aₙ`, then there is also some value `aₘ` 
such
that `s.get? = some aₘ` for `m ≤ n`.
-/
theorem ge_stable (s : Seq α) {aₙ : α} {n m : ℕ} (m_le_n : m ≤ n)
    (s_nth_eq_some : s.get? n = some aₙ) : ∃ aₘ : α, s.get? m = some aₘ :=
  have : s.get? n ≠ none := by simp [s_nth_eq_some]
  have : s.get? m ≠ none := mt (s.le_stable m_le_n) this
  Option.ne_none_iff_exists'.mp this

@[ext]
/-
**Stream.Seq.ext** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem ext {s t : Seq α} (h : ∀ n : ℕ, s.get? n = t.get? n) : s = t :=
  Subtype.ext <| funext h

/-!
### Constructors
-/

/-- The empty sequence -/
/-
**Stream.Seq.nil** 是 Mathlib 中的一个定义，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The empty sequence
-/
def nil : Seq α :=
  ⟨Stream'.const none, fun {_} _ => rfl⟩
/-
**Stream.Seq.** 是 Mathlib 中的一个实例，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Seq α) :=
  ⟨nil⟩

/-- Prepend an element to a sequence -/
/-
**Stream.Seq.cons** 是 Mathlib 中的一个定义，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Prepend an element to a sequence
-/
def cons (a : α) (s : Seq α) : Seq α :=
  ⟨some a::s.1, by
    rintro (n | _) h
    · contradiction
    · exact s.2 h⟩

@[simp]
/-
**Stream.Seq.val_cons** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem val_cons (s : Seq α) (x : α) : (cons x s).val = some x::s.val :=
  rfl

@[simp]
/-
**Stream.Seq.get** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem get?_nil (n : ℕ) : (@nil α).get? n = none :=
  rfl

@[simp]
/-
**Stream.Seq.get** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem get?_zero_eq_none {s : Seq α} : s.get? 0 = none ↔ s = nil := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  ext1 n
  exact le_stable s (Nat.zero_le _) h

@[simp]
/-
**Stream.Seq.get** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem get?_cons_zero (a : α) (s : Seq α) : (cons a s).get? 0 = some a :=
  rfl

@[simp]
/-
**Stream.Seq.get** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem get?_cons_succ (a : α) (s : Seq α) (n : ℕ) : (cons a s).get? (n + 1) = s.get? n :=
  rfl

@[simp]
/-
**Stream.Seq.cons_ne_nil** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cons_ne_nil {x : α} {s : Seq α} : (cons x s) ≠ .nil := by
  intro h
  simpa using congrArg (·.get? 0) h

@[simp]
/-
**Stream.Seq.nil_ne_cons** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nil_ne_cons {x : α} {s : Seq α} : .nil ≠ (cons x s) := cons_ne_nil.symm
/-
**Stream.Seq.cons_injective2** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cons_injective2 : Function.Injective2 (cons : α → Seq α → Seq α) := fun x y s t h =>
  ⟨by rw [← Option.some_inj, ← get?_cons_zero, h, get?_cons_zero],
    Seq.ext fun n => by simp_rw [← get?_cons_succ x s n, h, get?_cons_succ]⟩
/-
**Stream.Seq.cons_left_injective** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cons_left_injective (s : Seq α) : Function.Injective fun x => cons x s :=
  cons_injective2.left _
/-
**Stream.Seq.cons_right_injective** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cons_right_injective (x : α) : Function.Injective (cons x) :=
  cons_injective2.right _

@[simp]
/-
**Stream.Seq.cons_eq_cons** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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

/-- Get the first element of a sequence -/
/-
**Stream.Seq.head** 是 Mathlib 中的一个定义，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Get the first element of a sequence
-/
def head (s : Seq α) : Option α :=
  get? s 0

/-- Get the tail of a sequence (or `nil` if the sequence is `nil`) -/
/-
**Stream.Seq.tail** 是 Mathlib 中的一个定义，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Get the tail of a sequence (or `nil` if the sequence is `nil`)
-/
def tail (s : Seq α) : Seq α :=
  ⟨s.1.tail, fun n' => by
    obtain ⟨f, al⟩ := s
    exact al n'⟩

/-- Destructor for a sequence, resulting in either `none` (for `nil`) or
  `some (a, s)` (for `cons a s`). -/
/-
**Stream.Seq.destruct** 是 Mathlib 中的一个定义，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Destructor for a sequence, resulting in either `none` (for `nil`) or
  `some (a, s)` (for `cons a s`).
-/
def destruct (s : Seq α) : Option (Seq1 α) :=
  (fun a' => (a', s.tail)) <$> get? s 0

-- Porting note: needed universe annotation to avoid universe issues
/-
**Stream.Seq.head_eq_destruct** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem head_eq_destruct (s : Seq α) : head s = Prod.fst <$> destruct.{u} s := by
  unfold destruct head; cases get? s 0 <;> rfl

@[simp]
/-
**Stream.Seq.get** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem get?_tail (s : Seq α) (n) : get? (tail s) n = get? s (n + 1) :=
  rfl

@[simp]
/-
**Stream.Seq.destruct_nil** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem destruct_nil : destruct (nil : Seq α) = none :=
  rfl

@[simp]
/-
**Stream.Seq.destruct_cons** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem destruct_cons (a : α) : ∀ s, destruct (cons a s) = some (a, s)
  | ⟨f, al⟩ => by
    unfold cons destruct Functor.map
    apply congr_arg fun s => some (a, s)
    apply Subtype.ext; dsimp [tail]
/-
**Stream.Seq.destruct_eq_none** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem destruct_eq_none {s : Seq α} : destruct s = none → s = nil := by
  dsimp [destruct]
  rcases f0 : get? s 0 <;> intro h
  · exact get?_zero_eq_none.mp f0
  · contradiction
/-
**Stream.Seq.destruct_eq_cons** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem destruct_eq_cons {s : Seq α} {a s'} : destruct s = some (a, s') → s = cons a s' := by
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
/-
**Stream.Seq.head_nil** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem head_nil : head (nil : Seq α) = none :=
  rfl

@[simp]
/-
**Stream.Seq.head_cons** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem head_cons (a : α) (s) : head (cons a s) = some a := by
  rw [head_eq_destruct, destruct_cons, Option.map_eq_map, Option.map_some]

@[simp]
/-
**Stream.Seq.tail_nil** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tail_nil : tail (nil : Seq α) = nil :=
  rfl

@[simp]
/-
**Stream.Seq.tail_cons** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tail_cons (a : α) (s) : tail (cons a s) = s := rfl
/-
**Stream.Seq.head_eq_some** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem head_eq_some {s : Seq α} {x : α} (h : s.head = some x) :
    s = cons x s.tail := by
  ext1 n
  cases n <;> simp only [get?_cons_zero, get?_cons_succ, get?_tail]
  exact h
/-
**Stream.Seq.head_eq_none** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem head_eq_none {s : Seq α} (h : s.head = none) : s = nil :=
  get?_zero_eq_none.mp h

@[simp]
/-
**Stream.Seq.head_eq_none_iff** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**Stream.Seq.recOn** 是 Mathlib 中的一个定义，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Recursion principle for sequences, compare with `List.recOn`.
-/
def recOn {motive : Seq α → Sort v} (s : Seq α) (nil : motive nil)
    (cons : ∀ x s, motive (cons x s)) :
    motive s := by
  rcases H : destruct s with - | v
  · rw [destruct_eq_none H]
    apply nil
  · obtain ⟨a, s'⟩ := v
    rw [destruct_eq_cons H]
    apply cons

/-- Functorial action of the functor `Option (α × _)` -/
@[simp]
/-
**Stream.Seq.omap** 是 Mathlib 中的一个定义，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Functorial action of the functor `Option (α × _)`
-/
def omap (f : β → γ) : Option (α × β) → Option (α × γ)
  | none => none
  | some (a, b) => some (a, f b)

/-- Corecursor over pairs of `Option` values -/
/-
**Stream.Seq.Corec.f** 是 Mathlib 中的一个定义，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Corecursor over pairs of `Option` values
-/
def Corec.f (f : β → Option (α × β)) : Option β → Option α × Option β
  | none => (none, none)
  | some b =>
    match f b with
    | none => (none, none)
    | some (a, b') => (some a, some b')

/-- Corecursor for `Seq α` as a coinductive type. Iterates `f` to produce new elements
  of the sequence until `none` is obtained. -/
/-
**Stream.Seq.corec** 是 Mathlib 中的一个定义，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Corecursor for `Seq α` as a coinductive type. Iterates `f` to produce new elemen
ts
  of the sequence until `none` is obtained.
-/
def corec (f : β → Option (α × β)) (b : β) : Seq α := by
  refine ⟨Stream'.corec' (Corec.f f) (some b), fun {n} h => ?_⟩
  rw [Stream'.corec'_eq]
  change Stream'.corec' (Corec.f f) (Corec.f f (some b)).2 n = none
  revert h; generalize some b = o
  induction n generalizing o with
  | zero =>
    change (Corec.f f o).1 = none → (Corec.f f (Corec.f f o).2).1 = none
    rcases o with - | b <;> intro h
    · rfl
    dsimp [Corec.f] at h
    dsimp [Corec.f]
    revert h; rcases h₁ : f b with - | s <;> intro h
    · rfl
    · obtain ⟨a, b'⟩ := s
      contradiction
  | succ n IH =>
    rw [Stream'.corec'_eq (Corec.f f) (Corec.f f o).2, Stream'.corec'_eq (Corec.f f) o]
    exact IH (Corec.f f o).2

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Stream.Seq.corec_eq** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem corec_eq (f : β → Option (α × β)) (b : β) :
    destruct (corec f b) = omap (corec f) (f b) := by
  dsimp [corec, destruct, get]
  rw [show Stream'.corec' (Corec.f f) (some b) 0 = (Corec.f f (some b)).1 from rfl]
  dsimp [Corec.f]
  rcases h : f b with - | s; · rfl
  obtain ⟨a, b'⟩ := s; dsimp [Corec.f]
  apply congr_arg fun b' => some (a, b')
  apply Subtype.ext
  dsimp [corec, tail]
  rw [Stream'.corec'_eq, Stream'.tail_cons]
  dsimp [Corec.f]; rw [h]

set_option backward.isDefEq.respectTransparency false in
/-
**Stream.Seq.corec_nil** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem corec_nil (f : β → Option (α × β)) (b : β)
    (h : f b = .none) : corec f b = nil := by
  apply destruct_eq_none
  simp [h]

set_option backward.isDefEq.respectTransparency false in
/-
**Stream.Seq.corec_cons** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem corec_cons {f : β → Option (α × β)} {b : β} {x : α} {s : β}
    (h : f b = .some (x, s)) : corec f b = cons x (corec f s) := by
  apply destruct_eq_cons
  simp [h]

/-!
### Bisimulation
-/

section Bisim

variable (R : Seq α → Seq α → Prop)

local infixl:50 " ~ " => R

/-- Bisimilarity relation over `Option` of `Seq1 α` -/
/-
**Stream.Seq.BisimO** 是 Mathlib 中的一个定义，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bisimilarity relation over `Option` of `Seq1 α`
-/
def BisimO : Option (Seq1 α) → Option (Seq1 α) → Prop
  | none, none => True
  | some (a, s), some (a', s') => a = a' ∧ R s s'
  | _, _ => False

attribute [simp] BisimO
attribute [nolint simpNF] BisimO.eq_3

/-- a relation is bisimilar if it meets the `BisimO` test -/
/-
**Stream.Seq.IsBisimulation** 是 Mathlib 中的一个定义，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
a relation is bisimilar if it meets the `BisimO` test
-/
def IsBisimulation :=
  ∀ ⦃s₁ s₂⦄, s₁ ~ s₂ → BisimO R (destruct s₁) (destruct s₂)

/-- If two streams are bisimilar, then they are equal. There are also versions
`eq_of_bisim'` and `eq_of_bisim_strong` that does not mention `IsBisimulation` and look
more like an induction principles. -/
/-
**Stream.Seq.eq_of_bisim** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If two streams are bisimilar, then they are equal. There are also versions
`eq_of_bisim'` and `eq_of_bisim_strong` that does not mention `IsBisimulation` a
nd look
more like an induction principles.
-/
theorem eq_of_bisim (bisim : IsBisimulation R) {s₁ s₂} (r : s₁ ~ s₂) : s₁ = s₂ := by
  apply Subtype.ext
  apply Stream'.eq_of_bisim fun x y => ∃ s s' : Seq α, s.1 = x ∧ s'.1 = y ∧ R s s'
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
        rw [destruct_nil, destruct_cons] at this
        exact False.elim this
      · intro _ this
        rw [destruct_nil, destruct_cons] at this
        exact False.elim this
      · simp
  · exact ⟨s₁, s₂, rfl, rfl, r⟩

/-- Coinductive principle for equality on sequences.
This is a version of `eq_of_bisim` that looks more like an induction principle. -/
/-
**Stream.Seq.eq_of_bisim'** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coinductive principle for equality on sequences.
This is a version of `eq_of_bisim` that looks more like an induction principle.
-/
theorem eq_of_bisim' {s₁ s₂ : Seq α}
    (motive : Seq α → Seq α → Prop)
    (base : motive s₁ s₂)
    (step : ∀ s₁ s₂, motive s₁ s₂ →
      (s₁ = nil ∧ s₂ = nil) ∨
      (∃ x s₁' s₂', s₁ = cons x s₁' ∧ s₂ = cons x s₂' ∧ motive s₁' s₂')) :
    s₁ = s₂ := by
  apply eq_of_bisim motive _ base
  intro s₁ s₂ h
  rcases step s₁ s₂ h with ⟨h_nil₁, h_nil₂⟩ | ⟨_, _, _, h₁, h₂, _⟩
  · simp [h_nil₁, h_nil₂]
  · simpa [h₁, h₂]

/-- Coinductive principle for equality on sequences.
This is a version of `eq_of_bisim'` that requires proving only `s₁ = s₂`
instead of `s₁ = nil ∧ s₂ = nil` in `step`. -/
/-
**Stream.Seq.eq_of_bisim_strong** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coinductive principle for equality on sequences.
This is a version of `eq_of_bisim'` that requires proving only `s₁ = s₂`
instead of `s₁ = nil ∧ s₂ = nil` in `step`.
-/
theorem eq_of_bisim_strong {s₁ s₂ : Seq α}
    (motive : Seq α → Seq α → Prop)
    (base : motive s₁ s₂)
    (step : ∀ s₁ s₂, motive s₁ s₂ →
      (s₁ = s₂) ∨
      (∃ x s₁' s₂', s₁ = cons x s₁' ∧ s₂ = cons x s₂' ∧ (motive s₁' s₂'))) : s₁ = s₂ := by
  let motive' : Seq α → Seq α → Prop := fun s₁ s₂ => s₁ = s₂ ∨ motive s₁ s₂
  apply eq_of_bisim' motive' (by grind)
  intro s₁ s₂ ih
  simp only [motive'] at ih ⊢
  rcases ih with (rfl | ih)
  · cases s₁ <;> grind
  rcases step s₁ s₂ ih with (rfl | ⟨hd, s₁', s₂', _⟩)
  · cases s₁ <;> grind
  · grind

end Bisim

/-
**Stream.Seq.coinduction** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coinduction :
    ∀ {s₁ s₂ : Seq α},
      head s₁ = head s₂ →
        (∀ (β : Type u) (fr : Seq α → β), fr s₁ = fr s₂ → fr (tail s₁) = fr (tail s₂)) → s₁ = s₂
  | _, _, hh, ht =>
    Subtype.ext (Stream'.coinduction hh fun β fr => ht β fun s => fr s.1)
/-
**Stream.Seq.coinduction2** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coinduction2 (s) (f g : Seq α → Seq β)
    (H :
      ∀ s,
        BisimO (fun s1 s2 : Seq β => ∃ s : Seq α, s1 = f s ∧ s2 = g s) (destruct (f s))
          (destruct (g s))) :
    f s = g s := by
  refine eq_of_bisim (fun s1 s2 => ∃ s, s1 = f s ∧ s2 = g s) ?_ ⟨s, rfl, rfl⟩
  intro s1 s2 h; rcases h with ⟨s, h1, h2⟩
  rw [h1, h2]; apply H

/-!
### Termination
-/

/-- A sequence has terminated at position `n` if the value at position `n` equals `none`. -/
/-
**Stream.Seq.TerminatedAt** 是 Mathlib 中的一个定义，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sequence has terminated at position `n` if the value at position `n` equals `n
one`.
-/
def TerminatedAt (s : Seq α) (n : ℕ) : Prop :=
  s.get? n = none

/-- It is decidable whether a sequence terminates at a given position. -/
/-
**Stream.Seq.terminatedAtDecidable** 是 Mathlib 中的一个实例，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
It is decidable whether a sequence terminates at a given position.
-/
instance terminatedAtDecidable (s : Seq α) (n : ℕ) : Decidable (s.TerminatedAt n) :=
  decidable_of_iff' (s.get? n).isNone <| by unfold TerminatedAt; cases s.get? n <;> simp

/-- A sequence terminates if there is some position `n` at which it has terminated. -/
/-
**Stream.Seq.Terminates** 是 Mathlib 中的一个定义，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sequence terminates if there is some position `n` at which it has terminated.
-/
def Terminates (s : Seq α) : Prop :=
  ∃ n : ℕ, s.TerminatedAt n

/-- The length of a terminating sequence. -/
/-
**Stream.Seq.length** 是 Mathlib 中的一个定义，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The length of a terminating sequence.
-/
def length (s : Seq α) (h : s.Terminates) : ℕ :=
  Nat.find h

open scoped Classical in
/-- The `ENat`-valued length of a sequence. For non-terminating sequences, it is `⊤`. -/
/-
**Stream.Seq.length'** 是 Mathlib 中的一个定义，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `ENat`-valued length of a sequence. For non-terminating sequences, it is `⊤`
.
-/
noncomputable def length' (s : Seq α) : ℕ∞ :=
  if h : s.Terminates then s.length h else ⊤

/-- If a sequence terminated at position `n`, it also terminated at `m ≥ n`. -/
/-
**Stream.Seq.terminated_stable** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a sequence terminated at position `n`, it also terminated at `m ≥ n`.
-/
theorem terminated_stable : ∀ (s : Seq α) {m n : ℕ}, m ≤ n → s.TerminatedAt m → s.TerminatedAt n :=
  le_stable
/-
**Stream.Seq.not_terminates_iff** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem not_terminates_iff {s : Seq α} : ¬s.Terminates ↔ ∀ n, (s.get? n).isSome := by
  simp only [Terminates, TerminatedAt, ← Ne.eq_def, Option.ne_none_iff_isSome, not_exists, iff_self]
/-
**Stream.Seq.terminatedAt_nil** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem terminatedAt_nil {n : ℕ} : TerminatedAt (nil : Seq α) n := rfl

@[simp]
/-
**Stream.Seq.cons_not_terminatedAt_zero** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cons_not_terminatedAt_zero {x : α} {s : Seq α} :
    ¬(cons x s).TerminatedAt 0 := by
  simp [TerminatedAt]

@[simp]
/-
**Stream.Seq.cons_terminatedAt_succ_iff** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cons_terminatedAt_succ_iff {x : α} {s : Seq α} {n : ℕ} :
    (cons x s).TerminatedAt (n + 1) ↔ s.TerminatedAt n := by
  simp [TerminatedAt]

@[simp]
/-
**Stream.Seq.terminates_nil** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem terminates_nil : Terminates (nil : Seq α) := ⟨0, rfl⟩

@[simp]
/-
**Stream.Seq.terminates_cons_iff** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem terminates_cons_iff {x : α} {s : Seq α} :
    (cons x s).Terminates ↔ s.Terminates := by
  constructor <;> intro ⟨n, h⟩
  · exact ⟨n, cons_terminatedAt_succ_iff.mp (terminated_stable _ (Nat.le_succ _) h)⟩
  · exact ⟨n + 1, cons_terminatedAt_succ_iff.mpr h⟩
/-
**Stream.Seq.terminatedAt_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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

/-- member definition for `Seq` -/
/-
**Stream.Seq.Mem** 是 Mathlib 中的一个定义，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
member definition for `Seq`
-/
protected def Mem (s : Seq α) (a : α) :=
  some a ∈ s.1
/-
**Stream.Seq.** 是 Mathlib 中的一个实例，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Membership α (Seq α) :=
  ⟨Seq.Mem⟩

-- Cannot be @[simp] because `n` can not be inferred by `simp`.
/-
**Stream.Seq.get** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem get?_mem {s : Seq α} {n : ℕ} {x : α} (h : s.get? n = .some x) : x ∈ s := ⟨n, h.symm⟩
/-
**Stream.Seq.mem_iff_exists_get** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_iff_exists_get? {s : Seq α} {x : α} : x ∈ s ↔ ∃ i, some x = s.get? i where
  mp h := by
    change (some x ∈ s.1) at h
    rwa [Stream'.mem_iff_exists_get_eq] at h
  mpr h := get?_mem h.choose_spec.symm

@[simp]
/-
**Stream.Seq.notMem_nil** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem notMem_nil (a : α) : a ∉ @nil α := fun ⟨_, (h : some a = none)⟩ => by injection h
/-
**Stream.Seq.mem_cons** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_cons (a : α) : ∀ s : Seq α, a ∈ cons a s
  | ⟨_, _⟩ => Stream'.mem_cons (some a) _
/-
**Stream.Seq.mem_cons_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_cons_of_mem (y : α) {a : α} : ∀ {s : Seq α}, a ∈ s → a ∈ cons y s
  | ⟨_, _⟩ => Stream'.mem_cons_of_mem (some y)
/-
**Stream.Seq.eq_or_mem_of_mem_cons** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eq_or_mem_of_mem_cons {a b : α} : ∀ {s : Seq α}, a ∈ cons b s → a = b ∨ a ∈ s
  | ⟨_, _⟩, h => (Stream'.eq_or_mem_of_mem_cons h).imp_left fun h => by injection h

@[simp]
/-
**Stream.Seq.mem_cons_iff** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_cons_iff {a b : α} {s : Seq α} : a ∈ cons b s ↔ a = b ∨ a ∈ s :=
  ⟨eq_or_mem_of_mem_cons, by rintro (rfl | m) <;> [apply mem_cons; exact mem_cons_of_mem _ m]⟩
/-
**Stream.Seq.mem_rec_on** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_rec_on {C : Seq α → Prop} {a s} (M : a ∈ s)
    (h1 : ∀ b s', a = b ∨ C s' → C (cons b s')) : C s := by
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
/-
**Stream.Seq.ofList** 是 Mathlib 中的一个定义，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Embed a list as a sequence
-/
def ofList (l : List α) : Seq α :=
  ⟨(l[·]?), fun {n} h => by
    rw [List.getElem?_eq_none_iff] at h ⊢
    exact Nat.le_succ_of_le h⟩
/-
**Stream.Seq.coeList** 是 Mathlib 中的一个实例，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance coeList : Coe (List α) (Seq α) :=
  ⟨ofList⟩

@[simp]
/-
**Stream.Seq.ofList_nil** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofList_nil : ofList [] = (nil : Seq α) :=
  rfl

@[simp]
/-
**Stream.Seq.ofList_get** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofList_get? (l : List α) (n : ℕ) : (ofList l).get? n = l[n]? :=
  rfl

@[simp]
/-
**Stream.Seq.ofList_cons** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofList_cons (a : α) (l : List α) : ofList (a::l) = cons a (ofList l) := by
  ext1 (_ | n) <;> simp
/-
**Stream.Seq.ofList_injective** 是 Mathlib 中的一个定理，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofList_injective : Function.Injective (ofList : List α → _) :=
  fun _ _ h => List.ext_getElem? fun _ => congr_fun (Subtype.ext_iff.1 h) _

/-- Embed an infinite stream as a sequence -/
@[coe]
/-
**Stream.Seq.ofStream** 是 Mathlib 中的一个定义，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Embed an infinite stream as a sequence
-/
def ofStream (s : Stream' α) : Seq α :=
  ⟨s.map some, fun {n} h => by contradiction⟩
/-
**Stream.Seq.coeStream** 是 Mathlib 中的一个实例，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance coeStream : Coe (Stream' α) (Seq α) :=
  ⟨ofStream⟩

section MLList

/-- Embed a `MLList α` as a sequence. Note that even though this
  is non-meta, it will produce infinite sequences if used with
  cyclic `MLList`s created by meta constructions. -/
/-
**Stream.Seq.ofMLList** 是 Mathlib 中的一个定义，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Embed a `MLList α` as a sequence. Note that even though this
  is non-meta, it will produce infinite sequences if used with
  cyclic `MLList`s created by meta constructions.
-/
def ofMLList : MLList Id α → Seq α :=
  corec fun l =>
    match l.uncons with
    | .none => none
    | .some (a, l') => some (a, l')
/-
**Stream.Seq.coeMLList** 是 Mathlib 中的一个实例，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance coeMLList : Coe (MLList Id α) (Seq α) :=
  ⟨ofMLList⟩

/-- Translate a sequence into a `MLList`. -/
/-
**Stream.Seq.toMLList** 是 Mathlib 中的一个定义，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Translate a sequence into a `MLList`.
-/
unsafe def toMLList : Seq α → MLList Id α
  | s =>
    match destruct s with
    | none => .nil
    | some (a, s') => .cons a (toMLList s')

end MLList

/-- Translate a sequence to a list. This function will run forever if
  run on an infinite sequence. -/
/-
**Stream.Seq.forceToList** 是 Mathlib 中的一个定义，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Translate a sequence to a list. This function will run forever if
  run on an infinite sequence.
-/
unsafe def forceToList (s : Seq α) : List α :=
  (toMLList s).force

/-- Take the first `n` elements of the sequence (producing a list) -/
/-
**Stream.Seq.take** 是 Mathlib 中的一个定义，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Take the first `n` elements of the sequence (producing a list)
-/
def take : ℕ → Seq α → List α
  | 0, _ => []
  | n + 1, s =>
    match destruct s with
    | none => []
    | some (x, r) => List.cons x (take n r)

/-- Convert a sequence which is known to terminate into a list -/
/-
**Stream.Seq.toList** 是 Mathlib 中的一个定义，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convert a sequence which is known to terminate into a list
-/
def toList (s : Seq α) (h : s.Terminates) : List α :=
  take (length s h) s

/-- Convert a sequence which is known not to terminate into a stream -/
/-
**Stream.Seq.toStream** 是 Mathlib 中的一个定义，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convert a sequence which is known not to terminate into a stream
-/
def toStream (s : Seq α) (h : ¬s.Terminates) : Stream' α := fun n =>
  Option.get _ <| not_terminates_iff.1 h n

/-- Convert a sequence into either a list or a stream depending on whether
  it is finite or infinite. (Without decidability of the infiniteness predicate,
  this is not constructively possible.) -/
/-
**Stream.Seq.toListOrStream** 是 Mathlib 中的一个定义，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convert a sequence into either a list or a stream depending on whether
  it is finite or infinite. (Without decidability of the infiniteness predicate,
  this is not constructively possible.)
-/
def toListOrStream (s : Seq α) [Decidable s.Terminates] : List α ⊕ Stream' α :=
  if h : s.Terminates then Sum.inl (toList s h) else Sum.inr (toStream s h)

/-- Convert a sequence into a list, embedded in a computation to allow for
  the possibility of infinite sequences (in which case the computation
  never returns anything). -/
/-
**Stream.Seq.toList'** 是 Mathlib 中的一个定义，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convert a sequence into a list, embedded in a computation to allow for
  the possibility of infinite sequences (in which case the computation
  never returns anything).
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

/-- Append two sequences. If `s₁` is infinite, then `s₁ ++ s₂ = s₁`,
  otherwise it puts `s₂` at the location of the `nil` in `s₁`. -/
/-
**Stream.Seq.append** 是 Mathlib 中的一个定义，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Append two sequences. If `s₁` is infinite, then `s₁ ++ s₂ = s₁`,
  otherwise it puts `s₂` at the location of the `nil` in `s₁`.
-/
def append (s₁ s₂ : Seq α) : Seq α :=
  @corec α (Seq α × Seq α)
    (fun ⟨s₁, s₂⟩ =>
      match destruct s₁ with
      | none => omap (fun s₂ => (nil, s₂)) (destruct s₂)
      | some (a, s₁') => some (a, s₁', s₂))
    (s₁, s₂)

/-- Map a function over a sequence. -/
/-
**Stream.Seq.map** 是 Mathlib 中的一个定义，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Map a function over a sequence.
-/
def map (f : α → β) : Seq α → Seq β
  | ⟨s, al⟩ =>
    ⟨s.map (Option.map f), fun {n} => by
      dsimp [Stream'.map, Stream'.get]
      rcases e : s n with - | e <;> intro
      · rw [al e]
        assumption
      · contradiction⟩

/-- Flatten a sequence of sequences. (It is required that the
  sequences be nonempty to ensure productivity; in the case
  of an infinite sequence of `nil`, the first element is never
  generated.) -/
/-
**Stream.Seq.join** 是 Mathlib 中的一个定义，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Flatten a sequence of sequences. (It is required that the
  sequences be nonempty to ensure productivity; in the case
  of an infinite sequence of `nil`, the first element is never
  generated.)
-/
def join : Seq (Seq1 α) → Seq α :=
  corec fun S =>
    match destruct S with
    | none => none
    | some ((a, s), S') =>
      some
        (a,
          match destruct s with
          | none => S'
          | some s' => cons s' S')

/-- Remove the first `n` elements from the sequence. -/
/-
**Stream.Seq.drop** 是 Mathlib 中的一个定义，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Remove the first `n` elements from the sequence.
-/
def drop (s : Seq α) : ℕ → Seq α
  | 0 => s
  | n + 1 => tail (drop s n)

/-- Split a sequence at `n`, producing a finite initial segment
  and an infinite tail. -/
/-
**Stream.Seq.splitAt** 是 Mathlib 中的一个定义，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Split a sequence at `n`, producing a finite initial segment
  and an infinite tail.
-/
def splitAt : ℕ → Seq α → List α × Seq α
  | 0, s => ([], s)
  | n + 1, s =>
    match destruct s with
    | none => ([], nil)
    | some (x, s') =>
      let (l, r) := splitAt n s'
      (List.cons x l, r)

/-- Combine two sequences with a function -/
/-
**Stream.Seq.zipWith** 是 Mathlib 中的一个定义，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Combine two sequences with a function
-/
def zipWith (f : α → β → γ) (s₁ : Seq α) (s₂ : Seq β) : Seq γ :=
  ⟨fun n => Option.map₂ f (s₁.get? n) (s₂.get? n), fun {_} hn =>
    Option.map₂_eq_none_iff.2 <| (Option.map₂_eq_none_iff.1 hn).imp s₁.2 s₂.2⟩

/-- Pair two sequences into a sequence of pairs -/
/-
**Stream.Seq.zip** 是 Mathlib 中的一个定义，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pair two sequences into a sequence of pairs
-/
def zip : Seq α → Seq β → Seq (α × β) :=
  zipWith Prod.mk

/-- Separate a sequence of pairs into two sequences -/
/-
**Stream.Seq.unzip** 是 Mathlib 中的一个定义，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Separate a sequence of pairs into two sequences
-/
def unzip (s : Seq (α × β)) : Seq α × Seq β :=
  (map Prod.fst s, map Prod.snd s)

/-- The sequence of natural numbers some 0, some 1, ... -/
/-
**Stream.Seq.nats** 是 Mathlib 中的一个定义，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sequence of natural numbers some 0, some 1, ...
-/
def nats : Seq ℕ :=
  Stream'.nats

/-- Enumerate a sequence by tagging each element with its index. -/
/-
**Stream.Seq.enum** 是 Mathlib 中的一个定义，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Enumerate a sequence by tagging each element with its index.
-/
def enum (s : Seq α) : Seq (ℕ × α) :=
  Seq.zip nats s

/-- Folds a sequence using `f`, producing a sequence of intermediate values, i.e.
`[init, f init s.head, f (f init s.head) s.tail.head, ...]`. -/
/-
**Stream.Seq.fold** 是 Mathlib 中的一个定义，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Folds a sequence using `f`, producing a sequence of intermediate values, i.e.
`[init, f init s.head, f (f init s.head) s.tail.head, ...]`.
-/
def fold (s : Seq α) (init : β) (f : β → α → β) : Seq β :=
  let f : β × Seq α → Option (β × (β × Seq α)) := fun (acc, x) =>
    match destruct x with
    | none => .none
    | some (x, s) => .some (f acc x, f acc x, s)
  cons init <| corec f (init, s)

/-- Applies `f` to the `n`th element of the sequence, if it exists, replacing that element
with the result. -/
/-
**Stream.Seq.update** 是 Mathlib 中的一个定义，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Applies `f` to the `n`th element of the sequence, if it exists, replacing that e
lement
with the result.
-/
def update (s : Seq α) (n : ℕ) (f : α → α) : Seq α where
  val := Function.update s.val n ((s.val n).map f)
  property := by
    have (i : ℕ) : Function.update s.val n ((s.get? n).map f) i = none ↔ s.get? i = none := by
      by_cases hi : i = n <;> simp [Function.update, hi]
    simp only [IsSeq, val_eq_get, this]
    exact @s.prop

/-- Sets the value of sequence `s` at index `n` to `a`. If the `n`th element does not exist
(`s` terminates earlier), the sequence is left unchanged. -/
/-
**Stream.Seq.set** 是 Mathlib 中的一个定义，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Sets the value of sequence `s` at index `n` to `a`. If the `n`th element does no
t exist
(`s` terminates earlier), the sequence is left unchanged.
-/
def set (s : Seq α) (n : ℕ) (a : α) : Seq α :=
  update s n fun _ ↦ a

/--
`Pairwise R s` means that all the elements with earlier indices are
`R`-related to all the elements with later indices.
```
Pairwise R [1, 2, 3] ↔ R 1 2 ∧ R 1 3 ∧ R 2 3
```
For example if `R = (· ≠ ·)` then it asserts `s` has no duplicates,
and if `R = (· < ·)` then it asserts that `s` is (strictly) sorted.
-/
/-
**Stream.Seq.Pairwise** 是 Mathlib 中的一个定义，位于命名空间 `Stream.Seq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Pairwise R s` means that all the elements with earlier indices are
`R`-related to all the elements with later indices.
```
Pairwise R [1, 2, 3] ↔ R 1 2 ∧ R 1 3 ∧ R 2 3
```
For example if `R = (· ≠ ·)` then it asserts `s` has no duplicates,
and if `R = (· < ·)` then it asserts that `s` is (strictly) sorted.
-/
def Pairwise (R : α → α → Prop) (s : Seq α) : Prop :=
  ∀ i j, i < j → ∀ x ∈ s.get? i, ∀ y ∈ s.get? j, R x y

end Seq

end Stream'

