/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Stream.Init
public import Mathlib.Logic.Relator
public import Mathlib.Tactic.Common
public import Batteries.Tactic.Lint.Simp

/-!
# Coinductive formalization of unbounded computations.

This file provides a `Computation` type where `Computation α` is the type of
unbounded computations returning `α`.
-/

@[expose] public section

open Function

universe u v w

/-
coinductive Computation (α : Type u) : Type u
| pure : α → Computation α
| think : Computation α → Computation α
-/
/--
Definition of `Computation` / `Computation` 的定义

English:
definition Computation
  signature: (α : Type u)
  body: { f : Stream' (Option α) // forall ⦃n a⦄, f n = some a -> f (n + 1) = some a }

中文:
定义 Computation
  签名: (α : 类型u)
  定义体: { f : Stream' (Option α) // forall ⦃n a⦄, f n = some a -> f (n + 1) = some a }

Depends on / 依赖: Stream
-/
def Computation (α : Type u) : Type u :=
  { f : Stream' (Option α) // forall ⦃n a⦄, f n = some a -> f (n + 1) = some a }

namespace Computation

variable {α : Type u} {β : Type v} {γ : Type w}

-- constructors
/--
Definition of `pure` / `pure` 的定义

English:
definition pure
  signature: (a : α)
  body: ⟨Stream'.const (some a), fun _ _ => id⟩

中文:
定义 pure
  签名: (a : α)
  定义体: ⟨Stream'.const (some a), fun _ _ => id⟩

Depends on / 依赖: Stream
-/
def pure (a : α) : Computation α :=
  ⟨Stream'.const (some a), fun _ _ => id⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeTC α (Computation α)
  body: ⟨pure⟩

中文:
实例 :
  签名: CoeTC α (Computation α)
  定义体: ⟨pure⟩
-/
instance : CoeTC α (Computation α) :=
  ⟨pure⟩

-- note [use has_coe_t]
/--
Definition of `think` / `think` 的定义

English:
definition think
  signature: (c : Computation α)
  body: ⟨Stream'.cons none c.1, fun n a h => by
    rcases n with - | n
    · contradiction
    · exact c.2 h⟩

中文:
定义 think
  签名: (c : Computation α)
  定义体: ⟨Stream'.cons none c.1, fun n a h => by
    rcases n with - | n
    · contradiction
    · exact c.2 h⟩

Depends on / 依赖: Stream
-/
def think (c : Computation α) : Computation α :=
  ⟨Stream'.cons none c.1, fun n a h => by
    rcases n with - | n
    · contradiction
    · exact c.2 h⟩

/--
Definition of `thinkN` / `thinkN` 的定义

English:
definition thinkN
  signature: (c : Computation α)

中文:
定义 thinkN
  签名: (c : Computation α)
-/
def thinkN (c : Computation α) : Nat -> Computation α
  | 0 => c
  | n + 1 => think (thinkN c n)

-- check for immediate result
/--
Definition of `head` / `head` 的定义

English:
definition head
  signature: (c : Computation α)
  body: c.1.head

中文:
定义 head
  签名: (c : Computation α)
  定义体: c.1.head
-/
def head (c : Computation α) : Option α :=
  c.1.head

-- one step of computation
/--
Definition of `tail` / `tail` 的定义

English:
definition tail
  signature: (c : Computation α)
  body: ⟨c.1.tail, fun _ _ h => c.2 h⟩

中文:
定义 tail
  签名: (c : Computation α)
  定义体: ⟨c.1.tail, fun _ _ h => c.2 h⟩
-/
def tail (c : Computation α) : Computation α :=
  ⟨c.1.tail, fun _ _ h => c.2 h⟩

/--
Definition of `empty` / `empty` 的定义

English:
definition empty
  signature: (α)
  body: ⟨Stream'.const none, fun _ _ => id⟩

中文:
定义 empty
  签名: (α)
  定义体: ⟨Stream'.const none, fun _ _ => id⟩

Depends on / 依赖: Stream
-/
def empty (α) : Computation α :=
  ⟨Stream'.const none, fun _ _ => id⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Computation α)
  body: ⟨empty _⟩

中文:
实例 :
  签名: 可居 (Computation α)
  定义体: ⟨empty _⟩
-/
instance : Inhabited (Computation α) :=
  ⟨empty _⟩

/--
Definition of `runFor` / `runFor` 的定义

English:
definition runFor
  signature: : Computation α -> Nat -> Option α
  body: Subtype.val

中文:
定义 runFor
  签名: : Computation α -> 自然数 -> 选项类型 α
  定义体: Subtype.val

Depends on / 依赖: Subtype, Subtype.val
-/
def runFor : Computation α -> Nat -> Option α :=
  Subtype.val

/--
Definition of `destruct` / `destruct` 的定义

English:
definition destruct
  signature: (c : Computation α)
  body: match c.1 0 with
  | none => Sum.inr (tail c)
  | some a => Sum.inl a

中文:
定义 destruct
  签名: (c : Computation α)
  定义体: match c.1 0 with
  | none => Sum.inr (tail c)
  | some a => Sum.inl a

Depends on / 依赖: Sum.inl, Sum.inr
-/
def destruct (c : Computation α) : α oplus (Computation α) :=
  match c.1 0 with
  | none => Sum.inr (tail c)
  | some a => Sum.inl a

/-- `run c` is an unsound meta function that runs `c` to completion, possibly
  resulting in an infinite loop in the VM. -/
unsafe def run : Computation α -> α
  | c =>
    match destruct c with
    | Sum.inl a => a
    | Sum.inr ca => run ca

/--
theorem `destruct_eq_pure` / 定理 `destruct_eq_pure`

English:
theorem destruct_eq_pure
  given: {s : Computation α} {a : α}
  statement: destruct s = Sum.inl a -> s = pure a
  proof: by
  dsimp [destruct]
  cases f0 : s.1 0 <;> intro h
  · contradiction
  · apply Subtype.ext
    funext n
    induction n with
    | zero => injection h with h'; rwa [h'] at f0
    | succ n IH => exact s.2 IH

中文:
定理 destruct_eq_pure
  条件: {s : Computation α} {a : α}
  结论: destruct s = 和.inl a -> s = pure a
  证明: by
  dsimp [destruct]
  cases f0 : s.1 0 <;> intro h
  · contradiction
  · apply Subtype.ext
    funext n
    induction n with
    | zero => injection h with h'; rwa [h'] at f0
    | succ n IH => exact s.2 IH

Depends on / 依赖: Subtype, Subtype.ext, destruct, injection
-/
theorem destruct_eq_pure {s : Computation α} {a : α} : destruct s = Sum.inl a -> s = pure a := by
  dsimp [destruct]
  cases f0 : s.1 0 <;> intro h
  · contradiction
  · apply Subtype.ext
    funext n
    induction n with
    | zero => injection h with h'; rwa [h'] at f0
    | succ n IH => exact s.2 IH

/--
theorem `destruct_eq_think` / 定理 `destruct_eq_think`

English:
theorem destruct_eq_think
  given: {s : Computation α} {s'}
  statement: destruct s = Sum.inr s' -> s = think s'
  proof: by
  dsimp [destruct]
  rcases f0 : s.1 0 with - | a' <;> intro h
  · injection h with h'
    rw [← h']
    obtain ⟨f, al⟩ := s
    apply Subtype.ext
    dsimp [think, tail]
    rw [← f0]
    exact (Stream'.eta f).symm
  · contradiction

@[simp]

中文:
定理 destruct_eq_think
  条件: {s : Computation α} {s'}
  结论: destruct s = 和.inr s' -> s = think s'
  证明: by
  dsimp [destruct]
  rcases f0 : s.1 0 with - | a' <;> intro h
  · injection h with h'
    rw [← h']
    obtain ⟨f, al⟩ := s
    apply Subtype.ext
    dsimp [think, tail]
    rw [← f0]
    exact (Stream'.eta f).symm
  · contradiction

@[simp]

Depends on / 依赖: Stream, Subtype, Subtype.ext, destruct, injection
-/
theorem destruct_eq_think {s : Computation α} {s'} : destruct s = Sum.inr s' -> s = think s' := by
  dsimp [destruct]
  rcases f0 : s.1 0 with - | a' <;> intro h
  · injection h with h'
    rw [← h']
    obtain ⟨f, al⟩ := s
    apply Subtype.ext
    dsimp [think, tail]
    rw [← f0]
    exact (Stream'.eta f).symm
  · contradiction

@[simp]
/--
theorem `destruct_pure` / 定理 `destruct_pure`

English:
theorem destruct_pure
  given: (a : α)
  statement: destruct (pure a) = Sum.inl a
  proof: rfl

@[simp]

中文:
定理 destruct_pure
  条件: (a : α)
  结论: destruct (pure a) = 和.inl a
  证明: rfl

@[simp]
-/
theorem destruct_pure (a : α) : destruct (pure a) = Sum.inl a :=
  rfl

@[simp]
/--
theorem `destruct_think` / 定理 `destruct_think`

English:
theorem destruct_think
  statement: forall s : Computation α, destruct (think s) = Sum.inr s

中文:
定理 destruct_think
  结论: 对任意 s : Computation α, destruct (think s) = 和.inr s
-/
theorem destruct_think : forall s : Computation α, destruct (think s) = Sum.inr s
  | ⟨_, _⟩ => rfl

@[simp]
/--
theorem `destruct_empty` / 定理 `destruct_empty`

English:
theorem destruct_empty
  statement: destruct (empty α) = Sum.inr (empty α)
  proof: rfl

@[simp]

中文:
定理 destruct_empty
  结论: destruct (empty α) = 和.inr (empty α)
  证明: rfl

@[simp]
-/
theorem destruct_empty : destruct (empty α) = Sum.inr (empty α) :=
  rfl

@[simp]
/--
theorem `head_pure` / 定理 `head_pure`

English:
theorem head_pure
  given: (a : α)
  statement: head (pure a) = some a
  proof: rfl

@[simp]

中文:
定理 head_pure
  条件: (a : α)
  结论: head (pure a) = some a
  证明: rfl

@[simp]
-/
theorem head_pure (a : α) : head (pure a) = some a :=
  rfl

@[simp]
/--
theorem `head_think` / 定理 `head_think`

English:
theorem head_think
  given: (s : Computation α)
  statement: head (think s) = none
  proof: rfl

@[simp]

中文:
定理 head_think
  条件: (s : Computation α)
  结论: head (think s) = none
  证明: rfl

@[simp]
-/
theorem head_think (s : Computation α) : head (think s) = none :=
  rfl

@[simp]
/--
theorem `head_empty` / 定理 `head_empty`

English:
theorem head_empty
  statement: head (empty α) = none
  proof: rfl

@[simp]

中文:
定理 head_empty
  结论: head (empty α) = none
  证明: rfl

@[simp]
-/
theorem head_empty : head (empty α) = none :=
  rfl

@[simp]
/--
theorem `tail_pure` / 定理 `tail_pure`

English:
theorem tail_pure
  given: (a : α)
  statement: tail (pure a) = pure a
  proof: rfl

@[simp]

中文:
定理 tail_pure
  条件: (a : α)
  结论: tail (pure a) = pure a
  证明: rfl

@[simp]
-/
theorem tail_pure (a : α) : tail (pure a) = pure a :=
  rfl

@[simp]
/--
theorem `tail_think` / 定理 `tail_think`

English:
theorem tail_think
  given: (s : Computation α)
  statement: tail (think s) = s
  proof: rfl

@[simp]

中文:
定理 tail_think
  条件: (s : Computation α)
  结论: tail (think s) = s
  证明: rfl

@[simp]
-/
theorem tail_think (s : Computation α) : tail (think s) = s := rfl

@[simp]
/--
theorem `tail_empty` / 定理 `tail_empty`

English:
theorem tail_empty
  statement: tail (empty α) = empty α
  proof: rfl

中文:
定理 tail_empty
  结论: tail (empty α) = empty α
  证明: rfl
-/
theorem tail_empty : tail (empty α) = empty α :=
  rfl

/--
theorem `think_empty` / 定理 `think_empty`

English:
theorem think_empty
  statement: empty α = think (empty α)
  proof: destruct_eq_think destruct_empty

中文:
定理 think_empty
  结论: empty α = think (empty α)
  证明: destruct_eq_think destruct_empty

Depends on / 依赖: destruct_empty, destruct_eq_think
-/
theorem think_empty : empty α = think (empty α) :=
  destruct_eq_think destruct_empty

/-- Recursion principle for computations, compare with `List.recOn`. -/
@[elab_as_elim]
/--
Definition of `recOn` / `recOn` 的定义

English:
definition recOn
  signature: {motive : Computation α -> Sort v} (s : Computation α) (pure : forall a, motive (pure a))
  body: match H : destruct s with
  | Sum.inl v => by
    rw [destruct_eq_pure H]
    apply pure
  | Sum.inr v => match v with
    | ⟨a, s'⟩ => by
      rw [destruct_eq_think H]
      apply think

中文:
定义 recOn
  签名: {motive : Computation α -> 类型层 v} (s : Computation α) (pure : 对任意 a, motive (pure a))
  定义体: match H : destruct s with
  | Sum.inl v => by
    rw [destruct_eq_pure H]
    apply pure
  | Sum.inr v => match v with
    | ⟨a, s'⟩ => by
      rw [destruct_eq_think H]
      apply think

Depends on / 依赖: Sum.inl, Sum.inr, destruct, destruct_eq_pure, destruct_eq_think
-/
def recOn {motive : Computation α -> Sort v} (s : Computation α) (pure : forall a, motive (pure a))
    (think : forall s, motive (think s)) : motive s :=
  match H : destruct s with
  | Sum.inl v => by
    rw [destruct_eq_pure H]
    apply pure
  | Sum.inr v => match v with
    | ⟨a, s'⟩ => by
      rw [destruct_eq_think H]
      apply think

/--
Definition of `Corec.f` / `Corec.f` 的定义

English:
definition Corec.f
  signature: (f : β -> α oplus β)

中文:
定义 Corec.f
  签名: (f : β -> α oplus β)
-/
def Corec.f (f : β -> α oplus β) : α oplus β -> Option α × (α oplus β)
  | Sum.inl a => (some a, Sum.inl a)
  | Sum.inr b =>
    (match f b with
      | Sum.inl a => some a
      | Sum.inr _ => none,
      f b)

/--
Definition of `corec` / `corec` 的定义

English:
definition corec
  signature: (f : β -> α oplus β) (b : β)
  body: by
  refine ⟨Stream'.corec' (Corec.f f) (Sum.inr b), fun n a' h => ?_⟩
  rw [Stream'.corec'_eq]
  change Stream'.corec' (Corec.f f) (Corec.f f (Sum.inr b)).2 n = some a'
  revert h; generalize Sum.inr b = o
  induction n generalizing o with
  | zero =>
    change (Corec.f f o).1 = some a' -> (Corec.

中文:
定义 corec
  签名: (f : β -> α oplus β) (b : β)
  定义体: by
  refine ⟨Stream'.corec' (Corec.f f) (Sum.inr b), fun n a' h => ?_⟩
  rw [Stream'.corec'_eq]
  change Stream'.corec' (Corec.f f) (Corec.f f (Sum.inr b)).2 n = some a'
  revert h; generalize Sum.inr b = o
  induction n generalizing o with
  | zero =>
    change (Corec.f f o).1 = some a' -> (Corec.

Depends on / 依赖: Corec.f, Stream, Sum.inr, generalize, generalizing, revert
-/
def corec (f : β -> α oplus β) (b : β) : Computation α := by
  refine ⟨Stream'.corec' (Corec.f f) (Sum.inr b), fun n a' h => ?_⟩
  rw [Stream'.corec'_eq]
  change Stream'.corec' (Corec.f f) (Corec.f f (Sum.inr b)).2 n = some a'
  revert h; generalize Sum.inr b = o
  induction n generalizing o with
  | zero =>
    change (Corec.f f o).1 = some a' -> (Corec.f f (Corec.f f o).2).1 = some a'
    rcases o with _ | b <;> intro h
    · exact h
    unfold Corec.f at *; split <;> simp_all
  | succ n IH =>
    rw [Stream'.corec'_eq (Corec.f f) (Corec.f f o).2]; rw [Stream'.corec'_eq (Corec.f f) o]
    exact IH (Corec.f f o).2

/--
Definition of `lmap` / `lmap` 的定义

English:
definition lmap
  signature: (f : α -> β)

中文:
定义 lmap
  签名: (f : α -> β)
-/
def lmap (f : α -> β) : α oplus γ -> β oplus γ
  | Sum.inl a => Sum.inl (f a)
  | Sum.inr b => Sum.inr b

/--
Definition of `rmap` / `rmap` 的定义

English:
definition rmap
  signature: (f : β -> γ)

中文:
定义 rmap
  签名: (f : β -> γ)
-/
def rmap (f : β -> γ) : α oplus β -> α oplus γ
  | Sum.inl a => Sum.inl a
  | Sum.inr b => Sum.inr (f b)

attribute [simp] lmap rmap

@[simp]
/--
theorem `corec_eq` / 定理 `corec_eq`

English:
theorem corec_eq
  given: (f : β -> α oplus β) (b : β)
  statement: destruct (corec f b) = rmap (corec f) (f b)
  proof: by
  dsimp [corec, destruct]
  rw [show Stream'.corec' (Corec.f f) (Sum.inr b) 0 =
    Sum.rec Option.some (fun _ => none) (f b) by
    dsimp [Corec.f]; rw [Stream'.corec']; rw [Stream'.corec]; rw [Stream'.map]; rw [Stream'.get]; rw [Stream'.iterate]
    match (f b) with
    | Sum.inl x => rfl
    |

中文:
定理 corec_eq
  条件: (f : β -> α oplus β) (b : β)
  结论: destruct (corec f b) = rmap (corec f) (f b)
  证明: by
  dsimp [corec, destruct]
  rw [show Stream'.corec' (Corec.f f) (Sum.inr b) 0 =
    Sum.rec Option.some (fun _ => none) (f b) by
    dsimp [Corec.f]; rw [Stream'.corec']; rw [Stream'.corec]; rw [Stream'.map]; rw [Stream'.get]; rw [Stream'.iterate]
    match (f b) with
    | Sum.inl x => rfl
    |

Depends on / 依赖: Corec.f, Option.some, Stream, Subtype, Subtype.ext, Sum.inl, Sum.inr, Sum.rec, congr_arg, destruct, iterate, tail_cons
-/
theorem corec_eq (f : β -> α oplus β) (b : β) : destruct (corec f b) = rmap (corec f) (f b) := by
  dsimp [corec, destruct]
  rw [show Stream'.corec' (Corec.f f) (Sum.inr b) 0 =
    Sum.rec Option.some (fun _ => none) (f b) by
    dsimp [Corec.f]; rw [Stream'.corec']; rw [Stream'.corec]; rw [Stream'.map]; rw [Stream'.get]; rw [Stream'.iterate]
    match (f b) with
    | Sum.inl x => rfl
    | Sum.inr x => rfl]
  rcases h : f b with a | b'; · rfl
  dsimp [Corec.f, destruct]
  apply congr_arg; apply Subtype.ext
  dsimp [corec, tail]
  rw [Stream'.corec'_eq]; rw [Stream'.tail_cons]
  dsimp [Corec.f]; rw [h]

section Bisim

variable (R : Computation α -> Computation α -> Prop)

/-- bisimilarity relation -/
local infixl:50 " ~ " => R

/--
Definition of `BisimO` / `BisimO` 的定义

English:
definition BisimO
  signature: : α oplus (Computation α) -> α oplus (Computation α) -> Prop

中文:
定义 BisimO
  签名: : α oplus (Computation α) -> α oplus (Computation α) -> 命题
-/
def BisimO : α oplus (Computation α) -> α oplus (Computation α) -> Prop
  | Sum.inl a, Sum.inl a' => a = a'
  | Sum.inr s, Sum.inr s' => R s s'
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

-- If two computations are bisimilar, then they are equal
/--
theorem `eq_of_bisim` / 定理 `eq_of_bisim`

English:
theorem eq_of_bisim
  given: (bisim : IsBisimulation R) {s₁ s₂} (r : s₁ ~ s₂)
  statement: s₁ = s₂
  proof: by
  apply Subtype.ext
  apply Stream'.eq_of_bisim fun x y => exists s s' : Computation α, s.1 = x ∧ s'.1 = y ∧ R s s'
  · dsimp [Stream'.IsBisimulation]
    intro t₁ t₂ e
    match t₁, t₂, e with
    | _, _, ⟨s, s', rfl, rfl, r⟩ =>
      suffices head s = head s' ∧ R (tail s) (tail s') from
       

中文:
定理 eq_of_bisim
  条件: (bisim : 是Bisimulation R) {s₁ s₂} (r : s₁ ~ s₂)
  结论: s₁ = s₂
  证明: by
  apply Subtype.ext
  apply Stream'.eq_of_bisim fun x y => exists s s' : Computation α, s.1 = x ∧ s'.1 = y ∧ R s s'
  · dsimp [Stream'.IsBisimulation]
    intro t₁ t₂ e
    match t₁, t₂, e with
    | _, _, ⟨s, s', rfl, rfl, r⟩ =>
      suffices head s = head s' ∧ R (tail s) (tail s') from
       

Depends on / 依赖: And.imp, Computation, IsBisimulation, Stream, Subtype, Subtype.ext, eq_of_bisim, revert
-/
theorem eq_of_bisim (bisim : IsBisimulation R) {s₁ s₂} (r : s₁ ~ s₂) : s₁ = s₂ := by
  apply Subtype.ext
  apply Stream'.eq_of_bisim fun x y => exists s s' : Computation α, s.1 = x ∧ s'.1 = y ∧ R s s'
  · dsimp [Stream'.IsBisimulation]
    intro t₁ t₂ e
    match t₁, t₂, e with
    | _, _, ⟨s, s', rfl, rfl, r⟩ =>
      suffices head s = head s' ∧ R (tail s) (tail s') from
        And.imp id (fun r => ⟨tail s, tail s', by cases s; rfl, by cases s'; rfl, r⟩) this
      have h := bisim r; revert r h
      refine recOn s ?_ ?_ <;> intro r' <;> refine recOn s' ?_ ?_ <;> intro a' r h
      · constructor <;> dsimp at h
        · rw [h]
        · rw [h] at r
          rw [tail_pure]; rw [tail_pure]; rw [h]
          assumption
      · rw [destruct_pure, destruct_think] at h
        exact False.elim h
      · rw [destruct_pure, destruct_think] at h
        exact False.elim h
      · simp_all
  · exact ⟨s₁, s₂, rfl, rfl, r⟩

end Bisim

-- It's more of a stretch to use ∈ for this relation, but it
-- asserts that the computation limits to the given value.
/--
Definition of `Mem` / `Mem` 的定义

English:
definition Mem
  signature: (s : Computation α) (a : α)
  body: some a in s.1

中文:
定义 Mem
  签名: (s : Computation α) (a : α)
  定义体: some a in s.1
-/
protected def Mem (s : Computation α) (a : α) :=
  some a in s.1

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Membership α (Computation α)
  body: ⟨Computation.Mem⟩

中文:
实例 :
  签名: Membership α (Computation α)
  定义体: ⟨Computation.Mem⟩

Depends on / 依赖: Computation, Computation.Mem
-/
instance : Membership α (Computation α) :=
  ⟨Computation.Mem⟩

/--
theorem `le_stable` / 定理 `le_stable`

English:
theorem le_stable
  given: (s : Computation α) {a m n} (h : m <= n)
  statement: s.1 m = some a -> s.1 n = some a
  proof: by
  obtain ⟨f, al⟩ := s
  induction h with
  | refl => exact id
  | step _ IH => exact fun h2 => al (IH h2)

中文:
定理 le_stable
  条件: (s : Computation α) {a m n} (h : m <= n)
  结论: s.1 m = some a -> s.1 n = some a
  证明: by
  obtain ⟨f, al⟩ := s
  induction h with
  | refl => exact id
  | step _ IH => exact fun h2 => al (IH h2)
-/
theorem le_stable (s : Computation α) {a m n} (h : m <= n) : s.1 m = some a -> s.1 n = some a := by
  obtain ⟨f, al⟩ := s
  induction h with
  | refl => exact id
  | step _ IH => exact fun h2 => al (IH h2)

/--
theorem `mem_unique` / 定理 `mem_unique`

English:
theorem mem_unique
  given: {s : Computation α} {a b : α}
  statement: a in s -> b in s -> a = b

中文:
定理 mem_unique
  条件: {s : Computation α} {a b : α}
  结论: a in s -> b in s -> a = b
-/
theorem mem_unique {s : Computation α} {a b : α} : a in s -> b in s -> a = b
  | ⟨m, ha⟩, ⟨n, hb⟩ => by
    injection
      (le_stable s (le_max_left m n) ha.symm).symm.trans (le_stable s (le_max_right m n) hb.symm)

/--
theorem `Mem.left_unique` / 定理 `Mem.left_unique`

English:
theorem Mem.left_unique
  statement: Relator.LeftUnique ((· in ·) : α -> Computation α -> Prop)
  proof: fun _ _ _ =>
  mem_unique

中文:
定理 Mem.left_unique
  结论: Relator.LeftUnique ((· in ·) : α -> Computation α -> 命题)
  证明: fun _ _ _ =>
  mem_unique
-/
theorem Mem.left_unique : Relator.LeftUnique ((· in ·) : α -> Computation α -> Prop) := fun _ _ _ =>
  mem_unique

/--
Definition of `Terminates` / `Terminates` 的定义

English:
class Terminates
  parameters: (s : Computation α)
  axioms and operations (1):
    - term : exists a, a in s

中文:
类 Terminates
  参数: (s : Computation α)
  公理与运算 (1 个):
    - term : 存在 a, a in s
-/
class Terminates (s : Computation α) : Prop where
  /-- assertion that there is some term `a` such that the `Computation` terminates -/
  term : exists a, a in s

/--
theorem `terminates_iff` / 定理 `terminates_iff`

English:
theorem terminates_iff
  given: (s : Computation α)
  statement: Terminates s ↔ exists a, a in s
  proof: ⟨fun h => h.1, Terminates.mk⟩

中文:
定理 terminates_iff
  条件: (s : Computation α)
  结论: Terminates s ↔ 存在 a, a in s
  证明: ⟨fun h => h.1, Terminates.mk⟩

Depends on / 依赖: Terminates, Terminates.mk
-/
theorem terminates_iff (s : Computation α) : Terminates s ↔ exists a, a in s :=
  ⟨fun h => h.1, Terminates.mk⟩

/--
theorem `terminates_of_mem` / 定理 `terminates_of_mem`

English:
theorem terminates_of_mem
  given: {s : Computation α} {a : α} (h : a in s)
  statement: Terminates s
  proof: ⟨⟨a, h⟩⟩

中文:
定理 terminates_of_mem
  条件: {s : Computation α} {a : α} (h : a in s)
  结论: Terminates s
  证明: ⟨⟨a, h⟩⟩
-/
theorem terminates_of_mem {s : Computation α} {a : α} (h : a in s) : Terminates s :=
  ⟨⟨a, h⟩⟩

/--
theorem `terminates_def` / 定理 `terminates_def`

English:
theorem terminates_def
  given: (s : Computation α)
  statement: Terminates s ↔ exists n, (s.1 n).isSome
  proof: ⟨fun ⟨⟨a, n, h⟩⟩ =>
    ⟨n, by
      dsimp [Stream'.get] at h
      rw [← h]
      exact rfl⟩,
    fun ⟨n, h⟩ => ⟨⟨Option.get _ h, n, (Option.eq_some_of_isSome h).symm⟩⟩⟩

中文:
定理 terminates_def
  条件: (s : Computation α)
  结论: Terminates s ↔ 存在 n, (s.1 n).isSome
  证明: ⟨fun ⟨⟨a, n, h⟩⟩ =>
    ⟨n, by
      dsimp [Stream'.get] at h
      rw [← h]
      exact rfl⟩,
    fun ⟨n, h⟩ => ⟨⟨Option.get _ h, n, (Option.eq_some_of_isSome h).symm⟩⟩⟩

Depends on / 依赖: Option.eq_some_of_isSome, Option.get, Stream, eq_some_of_isSome
-/
theorem terminates_def (s : Computation α) : Terminates s ↔ exists n, (s.1 n).isSome :=
  ⟨fun ⟨⟨a, n, h⟩⟩ =>
    ⟨n, by
      dsimp [Stream'.get] at h
      rw [← h]
      exact rfl⟩,
    fun ⟨n, h⟩ => ⟨⟨Option.get _ h, n, (Option.eq_some_of_isSome h).symm⟩⟩⟩

/--
theorem `ret_mem` / 定理 `ret_mem`

English:
theorem ret_mem
  given: (a : α)
  statement: a in pure a
  proof: Exists.intro 0 rfl

中文:
定理 ret_mem
  条件: (a : α)
  结论: a in pure a
  证明: Exists.intro 0 rfl

Depends on / 依赖: Exists, Exists.intro
-/
theorem ret_mem (a : α) : a in pure a :=
  Exists.intro 0 rfl

/--
theorem `eq_of_pure_mem` / 定理 `eq_of_pure_mem`

English:
theorem eq_of_pure_mem
  given: {a a' : α} (h : a' in pure a)
  statement: a' = a
  proof: mem_unique h (ret_mem _)

@[simp]

中文:
定理 eq_of_pure_mem
  条件: {a a' : α} (h : a' in pure a)
  结论: a' = a
  证明: mem_unique h (ret_mem _)

@[simp]

Depends on / 依赖: mem_unique, ret_mem
-/
theorem eq_of_pure_mem {a a' : α} (h : a' in pure a) : a' = a :=
  mem_unique h (ret_mem _)

@[simp]
/--
theorem `mem_pure_iff` / 定理 `mem_pure_iff`

English:
theorem mem_pure_iff
  given: (a b : α)
  statement: a in pure b ↔ a = b
  proof: ⟨eq_of_pure_mem, fun h => h ▸ ret_mem _⟩

中文:
定理 mem_pure_iff
  条件: (a b : α)
  结论: a in pure b ↔ a = b
  证明: ⟨eq_of_pure_mem, fun h => h ▸ ret_mem _⟩

Depends on / 依赖: eq_of_pure_mem, ret_mem
-/
theorem mem_pure_iff (a b : α) : a in pure b ↔ a = b :=
  ⟨eq_of_pure_mem, fun h => h ▸ ret_mem _⟩

/--
Instance `ret_terminates` / 实例 `ret_terminates`

English:
instance ret_terminates
  signature: (a : α)
  body: terminates_of_mem (ret_mem _)

中文:
实例 ret_terminates
  签名: (a : α)
  定义体: terminates_of_mem (ret_mem _)

Depends on / 依赖: ret_mem, terminates_of_mem
-/
instance ret_terminates (a : α) : Terminates (pure a) :=
  terminates_of_mem (ret_mem _)

/--
theorem `think_mem` / 定理 `think_mem`

English:
theorem think_mem
  given: {s : Computation α} {a}
  statement: a in s -> a in think s

中文:
定理 think_mem
  条件: {s : Computation α} {a}
  结论: a in s -> a in think s
-/
theorem think_mem {s : Computation α} {a} : a in s -> a in think s
  | ⟨n, h⟩ => ⟨n + 1, h⟩

/--
Instance `think_terminates` / 实例 `think_terminates`

English:
instance think_terminates
  signature: (s : Computation α)

中文:
实例 think_terminates
  签名: (s : Computation α)
-/
instance think_terminates (s : Computation α) : forall [Terminates s], Terminates (think s)
  | ⟨⟨a, n, h⟩⟩ => ⟨⟨a, n + 1, h⟩⟩

/--
theorem `of_think_mem` / 定理 `of_think_mem`

English:
theorem of_think_mem
  given: {s : Computation α} {a}
  statement: a in think s -> a in s

中文:
定理 of_think_mem
  条件: {s : Computation α} {a}
  结论: a in think s -> a in s
-/
theorem of_think_mem {s : Computation α} {a} : a in think s -> a in s
  | ⟨n, h⟩ => by
    rcases n with - | n'
    · contradiction
    · exact ⟨n', h⟩

/--
theorem `of_think_terminates` / 定理 `of_think_terminates`

English:
theorem of_think_terminates
  given: {s : Computation α}
  statement: Terminates (think s) -> Terminates s

中文:
定理 of_think_terminates
  条件: {s : Computation α}
  结论: Terminates (think s) -> Terminates s
-/
theorem of_think_terminates {s : Computation α} : Terminates (think s) -> Terminates s
  | ⟨⟨a, h⟩⟩ => ⟨⟨a, of_think_mem h⟩⟩

/--
theorem `notMem_empty` / 定理 `notMem_empty`

English:
theorem notMem_empty
  given: (a : α)
  statement: a ∉ empty α
  proof: fun ⟨n, h⟩ => by contradiction

中文:
定理 notMem_empty
  条件: (a : α)
  结论: a ∉ empty α
  证明: fun ⟨n, h⟩ => by contradiction
-/
theorem notMem_empty (a : α) : a ∉ empty α := fun ⟨n, h⟩ => by contradiction

/--
theorem `not_terminates_empty` / 定理 `not_terminates_empty`

English:
theorem not_terminates_empty
  statement: ¬Terminates (empty α)
  proof: fun ⟨⟨a, h⟩⟩ => notMem_empty a h

中文:
定理 not_terminates_empty
  结论: ¬Terminates (empty α)
  证明: fun ⟨⟨a, h⟩⟩ => notMem_empty a h

Depends on / 依赖: notMem_empty
-/
theorem not_terminates_empty : ¬Terminates (empty α) := fun ⟨⟨a, h⟩⟩ => notMem_empty a h

/--
theorem `eq_empty_of_not_terminates` / 定理 `eq_empty_of_not_terminates`

English:
theorem eq_empty_of_not_terminates
  given: {s} (H : ¬Terminates s)
  statement: s = empty α
  proof: by
  apply Subtype.ext; funext n
  rcases h : s.val n; · rfl
  refine absurd ?_ H; exact ⟨⟨_, _, h.symm⟩⟩

中文:
定理 eq_empty_of_not_terminates
  条件: {s} (H : ¬Terminates s)
  结论: s = empty α
  证明: by
  apply Subtype.ext; funext n
  rcases h : s.val n; · rfl
  refine absurd ?_ H; exact ⟨⟨_, _, h.symm⟩⟩

Depends on / 依赖: Subtype, Subtype.ext, absurd, h.symm, s.val
-/
theorem eq_empty_of_not_terminates {s} (H : ¬Terminates s) : s = empty α := by
  apply Subtype.ext; funext n
  rcases h : s.val n; · rfl
  refine absurd ?_ H; exact ⟨⟨_, _, h.symm⟩⟩

/--
theorem `thinkN_mem` / 定理 `thinkN_mem`

English:
theorem thinkN_mem
  given: {s : Computation α} {a}
  statement: forall n, a in thinkN s n ↔ a in s

中文:
定理 thinkN_mem
  条件: {s : Computation α} {a}
  结论: 对任意 n, a in thinkN s n ↔ a in s
-/
theorem thinkN_mem {s : Computation α} {a} : forall n, a in thinkN s n ↔ a in s
  | 0 => Iff.rfl
  | n + 1 => Iff.trans ⟨of_think_mem, think_mem⟩ (thinkN_mem n)

/--
Instance `thinkN_terminates` / 实例 `thinkN_terminates`

English:
instance thinkN_terminates
  signature: (s : Computation α)

中文:
实例 thinkN_terminates
  签名: (s : Computation α)
-/
instance thinkN_terminates (s : Computation α) : forall [Terminates s] (n), Terminates (thinkN s n)
  | ⟨⟨a, h⟩⟩, n => ⟨⟨a, (thinkN_mem n).2 h⟩⟩

/--
theorem `of_thinkN_terminates` / 定理 `of_thinkN_terminates`

English:
theorem of_thinkN_terminates
  given: (s : Computation α) (n)
  statement: Terminates (thinkN s n) -> Terminates s

中文:
定理 of_thinkN_terminates
  条件: (s : Computation α) (n)
  结论: Terminates (thinkN s n) -> Terminates s
-/
theorem of_thinkN_terminates (s : Computation α) (n) : Terminates (thinkN s n) -> Terminates s
  | ⟨⟨a, h⟩⟩ => ⟨⟨a, (thinkN_mem _).1 h⟩⟩

/--
Definition of `Promises` / `Promises` 的定义

English:
definition Promises
  signature: (s : Computation α) (a : α)
  body: forall ⦃a'⦄, a' in s -> a = a'

中文:
定义 Promises
  签名: (s : Computation α) (a : α)
  定义体: forall ⦃a'⦄, a' in s -> a = a'
-/
def Promises (s : Computation α) (a : α) : Prop :=
  forall ⦃a'⦄, a' in s -> a = a'

/-- `Promises s a`, or `s ~> a`, asserts that although the computation `s`
  may not terminate, if it does, then the result is `a`. -/
scoped infixl:50 " ~> " => Promises

/--
theorem `mem_promises` / 定理 `mem_promises`

English:
theorem mem_promises
  given: {s : Computation α} {a : α}
  statement: a in s -> s ~> a
  proof: fun h _ => mem_unique h

中文:
定理 mem_promises
  条件: {s : Computation α} {a : α}
  结论: a in s -> s ~> a
  证明: fun h _ => mem_unique h

Depends on / 依赖: mem_unique
-/
theorem mem_promises {s : Computation α} {a : α} : a in s -> s ~> a := fun h _ => mem_unique h

/--
theorem `empty_promises` / 定理 `empty_promises`

English:
theorem empty_promises
  given: (a : α)
  statement: empty α ~> a
  proof: fun _ h => absurd h (notMem_empty _)

中文:
定理 empty_promises
  条件: (a : α)
  结论: empty α ~> a
  证明: fun _ h => absurd h (notMem_empty _)

Depends on / 依赖: absurd, notMem_empty
-/
theorem empty_promises (a : α) : empty α ~> a := fun _ h => absurd h (notMem_empty _)

section get

variable (s : Computation α) [h : Terminates s]

/--
Definition of `length` / `length` 的定义

English:
definition length
  signature: : Nat
  body: Nat.find ((terminates_def _).1 h)

中文:
定义 length
  签名: : 自然数
  定义体: Nat.find ((terminates_def _).1 h)

Depends on / 依赖: Nat.find, terminates_def
-/
def length : Nat :=
  Nat.find ((terminates_def _).1 h)

/--
Definition of `get` / `get` 的定义

English:
definition get
  signature: : α
  body: Option.get _ (Nat.find_spec <| (terminates_def _).1 h)

中文:
定义 get
  签名: : α
  定义体: Option.get _ (Nat.find_spec <| (terminates_def _).1 h)

Depends on / 依赖: Nat.find_spec, Option.get, find_spec, terminates_def
-/
def get : α :=
  Option.get _ (Nat.find_spec <| (terminates_def _).1 h)

/--
theorem `get_mem` / 定理 `get_mem`

English:
theorem get_mem
  statement: get s in s
  proof: Exists.intro (length s) (Option.eq_some_of_isSome _).symm

中文:
定理 get_mem
  结论: get s in s
  证明: Exists.intro (length s) (Option.eq_some_of_isSome _).symm

Depends on / 依赖: Exists, Exists.intro, Option.eq_some_of_isSome, eq_some_of_isSome, length
-/
theorem get_mem : get s in s :=
  Exists.intro (length s) (Option.eq_some_of_isSome _).symm

/--
theorem `get_eq_of_mem` / 定理 `get_eq_of_mem`

English:
theorem get_eq_of_mem
  given: {a}
  statement: a in s -> get s = a
  proof: mem_unique (get_mem _)

中文:
定理 get_eq_of_mem
  条件: {a}
  结论: a in s -> get s = a
  证明: mem_unique (get_mem _)

Depends on / 依赖: get_mem, mem_unique
-/
theorem get_eq_of_mem {a} : a in s -> get s = a :=
  mem_unique (get_mem _)

/--
theorem `mem_of_get_eq` / 定理 `mem_of_get_eq`

English:
theorem mem_of_get_eq
  given: {a}
  statement: get s = a -> a in s
  proof: by intro h; rw [← h]; apply get_mem

@[simp]

中文:
定理 mem_of_get_eq
  条件: {a}
  结论: get s = a -> a in s
  证明: by intro h; rw [← h]; apply get_mem

@[simp]

Depends on / 依赖: get_mem
-/
theorem mem_of_get_eq {a} : get s = a -> a in s := by intro h; rw [← h]; apply get_mem

@[simp]
/--
theorem `get_think` / 定理 `get_think`

English:
theorem get_think
  statement: get (think s) = get s
  proof: get_eq_of_mem _
    let ⟨n, h⟩ := get_mem s
    ⟨n + 1, h⟩

@[simp]

中文:
定理 get_think
  结论: get (think s) = get s
  证明: get_eq_of_mem _
    let ⟨n, h⟩ := get_mem s
    ⟨n + 1, h⟩

@[simp]

Depends on / 依赖: get_eq_of_mem, get_mem
-/
theorem get_think : get (think s) = get s :=
get_eq_of_mem _
    let ⟨n, h⟩ := get_mem s
    ⟨n + 1, h⟩

@[simp]
/--
theorem `get_thinkN` / 定理 `get_thinkN`

English:
theorem get_thinkN
  given: (n)
  statement: get (thinkN s n) = get s
  proof: get_eq_of_mem _ (thinkN_mem _).2 (get_mem _)

中文:
定理 get_thinkN
  条件: (n)
  结论: get (thinkN s n) = get s
  证明: get_eq_of_mem _ (thinkN_mem _).2 (get_mem _)

Depends on / 依赖: get_eq_of_mem, get_mem, thinkN_mem
-/
theorem get_thinkN (n) : get (thinkN s n) = get s :=
get_eq_of_mem _ (thinkN_mem _).2 (get_mem _)

/--
theorem `get_promises` / 定理 `get_promises`

English:
theorem get_promises
  statement: s ~> get s
  proof: fun _ => get_eq_of_mem _

中文:
定理 get_promises
  结论: s ~> get s
  证明: fun _ => get_eq_of_mem _

Depends on / 依赖: get_eq_of_mem
-/
theorem get_promises : s ~> get s := fun _ => get_eq_of_mem _

/--
theorem `mem_of_promises` / 定理 `mem_of_promises`

English:
theorem mem_of_promises
  given: {a} (p : s ~> a)
  statement: a in s
  proof: by
  obtain ⟨a', h⟩ := h
  rw [p h]
  exact h

中文:
定理 mem_of_promises
  条件: {a} (p : s ~> a)
  结论: a in s
  证明: by
  obtain ⟨a', h⟩ := h
  rw [p h]
  exact h
-/
theorem mem_of_promises {a} (p : s ~> a) : a in s := by
  obtain ⟨a', h⟩ := h
  rw [p h]
  exact h

/--
theorem `get_eq_of_promises` / 定理 `get_eq_of_promises`

English:
theorem get_eq_of_promises
  given: {a}
  statement: s ~> a -> get s = a
  proof: get_eq_of_mem _ ∘ mem_of_promises _

中文:
定理 get_eq_of_promises
  条件: {a}
  结论: s ~> a -> get s = a
  证明: get_eq_of_mem _ ∘ mem_of_promises _

Depends on / 依赖: get_eq_of_mem, mem_of_promises
-/
theorem get_eq_of_promises {a} : s ~> a -> get s = a :=
  get_eq_of_mem _ ∘ mem_of_promises _

end get

/--
Definition of `Results` / `Results` 的定义

English:
definition Results
  signature: (s : Computation α) (a : α) (n : Nat)
  body: exists h : a in s, @length _ s (terminates_of_mem h) = n

中文:
定义 Results
  签名: (s : Computation α) (a : α) (n : 自然数)
  定义体: exists h : a in s, @length _ s (terminates_of_mem h) = n

Depends on / 依赖: length, terminates_of_mem
-/
def Results (s : Computation α) (a : α) (n : Nat) :=
  exists h : a in s, @length _ s (terminates_of_mem h) = n

/--
theorem `results_of_terminates` / 定理 `results_of_terminates`

English:
theorem results_of_terminates
  given: (s : Computation α) [_T : Terminates s]
  proof: ⟨get_mem _, rfl⟩

中文:
定理 results_of_terminates
  条件: (s : Computation α) [_T : Terminates s]
  证明: ⟨get_mem _, rfl⟩

Depends on / 依赖: get_mem
-/
theorem results_of_terminates (s : Computation α) [_T : Terminates s] :
    Results s (get s) (length s) :=
  ⟨get_mem _, rfl⟩

/--
theorem `results_of_terminates'` / 定理 `results_of_terminates'`

English:
theorem results_of_terminates'
  given: (s : Computation α) [T : Terminates s] {a} (h : a in s)
  proof: by rw [← get_eq_of_mem _ h]; apply results_of_terminates

中文:
定理 results_of_terminates'
  条件: (s : Computation α) [T : Terminates s] {a} (h : a in s)
  证明: by rw [← get_eq_of_mem _ h]; apply results_of_terminates

Depends on / 依赖: get_eq_of_mem, results_of_terminates
-/
theorem results_of_terminates' (s : Computation α) [T : Terminates s] {a} (h : a in s) :
    Results s a (length s) := by rw [← get_eq_of_mem _ h]; apply results_of_terminates

/--
theorem `Results.mem` / 定理 `Results.mem`

English:
theorem Results.mem
  given: {s : Computation α} {a n}
  statement: Results s a n -> a in s

中文:
定理 Results.mem
  条件: {s : Computation α} {a n}
  结论: Results s a n -> a in s
-/
theorem Results.mem {s : Computation α} {a n} : Results s a n -> a in s
  | ⟨m, _⟩ => m

/--
theorem `Results.terminates` / 定理 `Results.terminates`

English:
theorem Results.terminates
  given: {s : Computation α} {a n} (h : Results s a n)
  statement: Terminates s
  proof: terminates_of_mem h.mem

中文:
定理 Results.terminates
  条件: {s : Computation α} {a n} (h : Results s a n)
  结论: Terminates s
  证明: terminates_of_mem h.mem

Depends on / 依赖: h.mem, terminates_of_mem
-/
theorem Results.terminates {s : Computation α} {a n} (h : Results s a n) : Terminates s :=
  terminates_of_mem h.mem

/--
theorem `Results.length` / 定理 `Results.length`

English:
theorem Results.length
  given: {s : Computation α} {a n} [_T : Terminates s]
  statement: Results s a n -> length s = n

中文:
定理 Results.length
  条件: {s : Computation α} {a n} [_T : Terminates s]
  结论: Results s a n -> length s = n
-/
theorem Results.length {s : Computation α} {a n} [_T : Terminates s] : Results s a n -> length s = n
  | ⟨_, h⟩ => h

/--
theorem `Results.val_unique` / 定理 `Results.val_unique`

English:
theorem Results.val_unique
  given: {s : Computation α} {a b m n} (h1 : Results s a m) (h2 : Results s b n)
  proof: mem_unique h1.mem h2.mem

中文:
定理 Results.val_unique
  条件: {s : Computation α} {a b m n} (h1 : Results s a m) (h2 : Results s b n)
  证明: mem_unique h1.mem h2.mem

Depends on / 依赖: h1.mem, h2.mem, mem_unique
-/
theorem Results.val_unique {s : Computation α} {a b m n} (h1 : Results s a m) (h2 : Results s b n) :
    a = b :=
  mem_unique h1.mem h2.mem

/--
theorem `Results.len_unique` / 定理 `Results.len_unique`

English:
theorem Results.len_unique
  given: {s : Computation α} {a b m n} (h1 : Results s a m) (h2 : Results s b n)
  proof: by have := h1.terminates; have := h2.terminates; rw [← h1.length, h2.length]

中文:
定理 Results.len_unique
  条件: {s : Computation α} {a b m n} (h1 : Results s a m) (h2 : Results s b n)
  证明: by have := h1.terminates; have := h2.terminates; rw [← h1.length, h2.length]

Depends on / 依赖: h1.length, h1.terminates, h2.length, h2.terminates, length, terminates
-/
theorem Results.len_unique {s : Computation α} {a b m n} (h1 : Results s a m) (h2 : Results s b n) :
    m = n := by have := h1.terminates; have := h2.terminates; rw [← h1.length, h2.length]

/--
theorem `exists_results_of_mem` / 定理 `exists_results_of_mem`

English:
theorem exists_results_of_mem
  given: {s : Computation α} {a} (h : a in s)
  statement: exists n, Results s a n
  proof: haveI := terminates_of_mem h
  ⟨_, results_of_terminates' s h⟩

@[simp]

中文:
定理 存在_results_of_mem
  条件: {s : Computation α} {a} (h : a in s)
  结论: 存在 n, Results s a n
  证明: haveI := terminates_of_mem h
  ⟨_, results_of_terminates' s h⟩

@[simp]

Depends on / 依赖: results_of_terminates, terminates_of_mem
-/
theorem exists_results_of_mem {s : Computation α} {a} (h : a in s) : exists n, Results s a n :=
  haveI := terminates_of_mem h
  ⟨_, results_of_terminates' s h⟩

@[simp]
/--
theorem `get_pure` / 定理 `get_pure`

English:
theorem get_pure
  given: (a : α)
  statement: get (pure a) = a
  proof: get_eq_of_mem _ ⟨0, rfl⟩

@[simp]

中文:
定理 get_pure
  条件: (a : α)
  结论: get (pure a) = a
  证明: get_eq_of_mem _ ⟨0, rfl⟩

@[simp]

Depends on / 依赖: get_eq_of_mem
-/
theorem get_pure (a : α) : get (pure a) = a :=
  get_eq_of_mem _ ⟨0, rfl⟩

@[simp]
/--
theorem `length_pure` / 定理 `length_pure`

English:
theorem length_pure
  given: (a : α)
  statement: length (pure a) = 0
  proof: let h := Computation.ret_terminates a
Nat.eq_zero_of_le_zero Nat.find_min' ((terminates_def (pure a)).1 h) rfl

中文:
定理 length_pure
  条件: (a : α)
  结论: length (pure a) = 0
  证明: let h := Computation.ret_terminates a
Nat.eq_zero_of_le_zero Nat.find_min' ((terminates_def (pure a)).1 h) rfl

Depends on / 依赖: Computation, Computation.ret_terminates, Nat.eq_zero_of_le_zero, Nat.find_min, eq_zero_of_le_zero, find_min, ret_terminates, terminates_def
-/
theorem length_pure (a : α) : length (pure a) = 0 :=
  let h := Computation.ret_terminates a
Nat.eq_zero_of_le_zero Nat.find_min' ((terminates_def (pure a)).1 h) rfl

/--
theorem `results_pure` / 定理 `results_pure`

English:
theorem results_pure
  given: (a : α)
  statement: Results (pure a) a 0
  proof: ⟨ret_mem a, length_pure _⟩

@[simp]

中文:
定理 results_pure
  条件: (a : α)
  结论: Results (pure a) a 0
  证明: ⟨ret_mem a, length_pure _⟩

@[simp]

Depends on / 依赖: length_pure, ret_mem
-/
theorem results_pure (a : α) : Results (pure a) a 0 :=
  ⟨ret_mem a, length_pure _⟩

@[simp]
/--
theorem `length_think` / 定理 `length_think`

English:
theorem length_think
  given: (s : Computation α) [h : Terminates s]
  statement: length (think s) = length s + 1
  proof: by
  apply le_antisymm
  · exact Nat.find_min' _ (Nat.find_spec ((terminates_def _).1 h))
  · have : (Option.isSome ((think s).val (length (think s))) : Prop) :=
      Nat.find_spec ((terminates_def _).1 s.think_terminates)
    revert this; rcases length (think s) with - | n <;> intro this
    · sim

中文:
定理 length_think
  条件: (s : Computation α) [h : Terminates s]
  结论: length (think s) = length s + 1
  证明: by
  apply le_antisymm
  · exact Nat.find_min' _ (Nat.find_spec ((terminates_def _).1 h))
  · have : (Option.isSome ((think s).val (length (think s))) : Prop) :=
      Nat.find_spec ((terminates_def _).1 s.think_terminates)
    revert this; rcases length (think s) with - | n <;> intro this
    · sim

Depends on / 依赖: Nat.find_min, Nat.find_spec, Nat.succ_le_succ, Option.isSome, Stream, find_min, find_spec, isSome, le_antisymm, length, revert, s.think_terminates, succ_le_succ, terminates_def, think_terminates
-/
theorem length_think (s : Computation α) [h : Terminates s] : length (think s) = length s + 1 := by
  apply le_antisymm
  · exact Nat.find_min' _ (Nat.find_spec ((terminates_def _).1 h))
  · have : (Option.isSome ((think s).val (length (think s))) : Prop) :=
      Nat.find_spec ((terminates_def _).1 s.think_terminates)
    revert this; rcases length (think s) with - | n <;> intro this
    · simp [think, Stream'.cons] at this
    · apply Nat.succ_le_succ
      apply Nat.find_min'
      apply this

/--
theorem `results_think` / 定理 `results_think`

English:
theorem results_think
  given: {s : Computation α} {a n} (h : Results s a n)
  statement: Results (think s) a (n + 1)
  proof: haveI := h.terminates
  ⟨think_mem h.mem, by rw [length_think, h.length]⟩

中文:
定理 results_think
  条件: {s : Computation α} {a n} (h : Results s a n)
  结论: Results (think s) a (n + 1)
  证明: haveI := h.terminates
  ⟨think_mem h.mem, by rw [length_think, h.length]⟩

Depends on / 依赖: h.length, h.mem, h.terminates, length, length_think, terminates, think_mem
-/
theorem results_think {s : Computation α} {a n} (h : Results s a n) : Results (think s) a (n + 1) :=
  haveI := h.terminates
  ⟨think_mem h.mem, by rw [length_think, h.length]⟩

/--
theorem `of_results_think` / 定理 `of_results_think`

English:
theorem of_results_think
  given: {s : Computation α} {a n} (h : Results (think s) a n)
  proof: by
  have := of_think_terminates h.terminates
  have := results_of_terminates' _ (of_think_mem h.mem)
  exact ⟨_, this, Results.len_unique h (results_think this)⟩

@[simp]

中文:
定理 of_results_think
  条件: {s : Computation α} {a n} (h : Results (think s) a n)
  证明: by
  have := of_think_terminates h.terminates
  have := results_of_terminates' _ (of_think_mem h.mem)
  exact ⟨_, this, Results.len_unique h (results_think this)⟩

@[simp]

Depends on / 依赖: Results, Results.len_unique, h.mem, h.terminates, len_unique, of_think_mem, of_think_terminates, results_of_terminates, results_think, terminates
-/
theorem of_results_think {s : Computation α} {a n} (h : Results (think s) a n) :
    exists m, Results s a m ∧ n = m + 1 := by
  have := of_think_terminates h.terminates
  have := results_of_terminates' _ (of_think_mem h.mem)
  exact ⟨_, this, Results.len_unique h (results_think this)⟩

@[simp]
/--
theorem `results_think_iff` / 定理 `results_think_iff`

English:
theorem results_think_iff
  given: {s : Computation α} {a n}
  statement: Results (think s) a (n + 1) ↔ Results s a n
  proof: ⟨fun h => by
    let ⟨n', r, e⟩ := of_results_think h
    injection e with h'; rwa [h'], results_think⟩

中文:
定理 results_think_iff
  条件: {s : Computation α} {a n}
  结论: Results (think s) a (n + 1) ↔ Results s a n
  证明: ⟨fun h => by
    let ⟨n', r, e⟩ := of_results_think h
    injection e with h'; rwa [h'], results_think⟩

Depends on / 依赖: injection, of_results_think, results_think
-/
theorem results_think_iff {s : Computation α} {a n} : Results (think s) a (n + 1) ↔ Results s a n :=
  ⟨fun h => by
    let ⟨n', r, e⟩ := of_results_think h
    injection e with h'; rwa [h'], results_think⟩

/--
theorem `results_thinkN` / 定理 `results_thinkN`

English:
theorem results_thinkN
  given: {s : Computation α} {a m}

中文:
定理 results_thinkN
  条件: {s : Computation α} {a m}
-/
theorem results_thinkN {s : Computation α} {a m} :
    forall n, Results s a m -> Results (thinkN s n) a (m + n)
  | 0, h => h
  | n + 1, h => results_think (results_thinkN n h)

/--
theorem `results_thinkN_pure` / 定理 `results_thinkN_pure`

English:
theorem results_thinkN_pure
  given: (a : α) (n)
  statement: Results (thinkN (pure a) n) a n
  proof: by
  have := results_thinkN n (results_pure a); rwa [Nat.zero_add] at this

@[simp]

中文:
定理 results_thinkN_pure
  条件: (a : α) (n)
  结论: Results (thinkN (pure a) n) a n
  证明: by
  have := results_thinkN n (results_pure a); rwa [Nat.zero_add] at this

@[simp]

Depends on / 依赖: Nat.zero_add, results_pure, results_thinkN, zero_add
-/
theorem results_thinkN_pure (a : α) (n) : Results (thinkN (pure a) n) a n := by
  have := results_thinkN n (results_pure a); rwa [Nat.zero_add] at this

@[simp]
/--
theorem `length_thinkN` / 定理 `length_thinkN`

English:
theorem length_thinkN
  given: (s : Computation α) [_h : Terminates s] (n)
  proof: (results_thinkN n (results_of_terminates _)).length

中文:
定理 length_thinkN
  条件: (s : Computation α) [_h : Terminates s] (n)
  证明: (results_thinkN n (results_of_terminates _)).length

Depends on / 依赖: length, results_of_terminates, results_thinkN
-/
theorem length_thinkN (s : Computation α) [_h : Terminates s] (n) :
    length (thinkN s n) = length s + n :=
  (results_thinkN n (results_of_terminates _)).length

/--
theorem `eq_thinkN` / 定理 `eq_thinkN`

English:
theorem eq_thinkN
  given: {s : Computation α} {a n} (h : Results s a n)
  statement: s = thinkN (pure a) n
  proof: by
  induction n generalizing s with | zero | succ n IH <;>
  induction s using recOn with | pure a' | think s
  · rw [← eq_of_pure_mem h.mem]
    rfl
  · obtain ⟨n, h⟩ := of_results_think h
    cases h
    contradiction
  · have := h.len_unique (results_pure _)
    contradiction
  · rw [IH (results

中文:
定理 eq_thinkN
  条件: {s : Computation α} {a n} (h : Results s a n)
  结论: s = thinkN (pure a) n
  证明: by
  induction n generalizing s with | zero | succ n IH <;>
  induction s using recOn with | pure a' | think s
  · rw [← eq_of_pure_mem h.mem]
    rfl
  · obtain ⟨n, h⟩ := of_results_think h
    cases h
    contradiction
  · have := h.len_unique (results_pure _)
    contradiction
  · rw [IH (results

Depends on / 依赖: eq_of_pure_mem, generalizing, h.len_unique, h.mem, len_unique, of_results_think, results_pure, results_think_iff
-/
theorem eq_thinkN {s : Computation α} {a n} (h : Results s a n) : s = thinkN (pure a) n := by
  induction n generalizing s with | zero | succ n IH <;>
  induction s using recOn with | pure a' | think s
  · rw [← eq_of_pure_mem h.mem]
    rfl
  · obtain ⟨n, h⟩ := of_results_think h
    cases h
    contradiction
  · have := h.len_unique (results_pure _)
    contradiction
  · rw [IH (results_think_iff.1 h)]
    rfl

/--
theorem `eq_thinkN'` / 定理 `eq_thinkN'`

English:
theorem eq_thinkN'
  given: (s : Computation α) [_h : Terminates s]
  proof: eq_thinkN (results_of_terminates _)

中文:
定理 eq_thinkN'
  条件: (s : Computation α) [_h : Terminates s]
  证明: eq_thinkN (results_of_terminates _)

Depends on / 依赖: eq_thinkN, results_of_terminates
-/
theorem eq_thinkN' (s : Computation α) [_h : Terminates s] :
    s = thinkN (pure (get s)) (length s) :=
  eq_thinkN (results_of_terminates _)

/--
Definition of `memRecOn` / `memRecOn` 的定义

English:
definition memRecOn
  signature: {C : Computation α -> Sort v} {a s} (M : a in s) (h1 : C (pure a))
  body: by
  haveI T := terminates_of_mem M
  rw [eq_thinkN' s]; rw [get_eq_of_mem s M]
  generalize length s = n
  induction n with | zero => exact h1 | succ n IH => exact h2 _ IH

中文:
定义 memRecOn
  签名: {C : Computation α -> 类型层 v} {a s} (M : a in s) (h1 : C (pure a))
  定义体: by
  haveI T := terminates_of_mem M
  rw [eq_thinkN' s]; rw [get_eq_of_mem s M]
  generalize length s = n
  induction n with | zero => exact h1 | succ n IH => exact h2 _ IH

Depends on / 依赖: eq_thinkN, generalize, get_eq_of_mem, length, terminates_of_mem
-/
def memRecOn {C : Computation α -> Sort v} {a s} (M : a in s) (h1 : C (pure a))
    (h2 : forall s, C s -> C (think s)) : C s := by
  haveI T := terminates_of_mem M
  rw [eq_thinkN' s]; rw [get_eq_of_mem s M]
  generalize length s = n
  induction n with | zero => exact h1 | succ n IH => exact h2 _ IH

/--
Definition of `terminatesRecOn` / `terminatesRecOn` 的定义

English:
definition terminatesRecOn
  body: memRecOn (get_mem s) (h1 _) h2

中文:
定义 terminatesRecOn
  定义体: memRecOn (get_mem s) (h1 _) h2

Depends on / 依赖: get_mem, memRecOn
-/
def terminatesRecOn
    {C : Computation α -> Sort v}
    (s) [Terminates s]
    (h1 : forall a, C (pure a))
    (h2 : forall s, C s -> C (think s)) : C s :=
  memRecOn (get_mem s) (h1 _) h2

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : α -> β)

中文:
定义 map
  签名: (f : α -> β)
-/
def map (f : α -> β) : Computation α -> Computation β
  | ⟨s, al⟩ =>
    ⟨s.map fun o => Option.casesOn o none (some ∘ f), fun n b => by
      dsimp [Stream'.map, Stream'.get]
      rcases e : s n with - | a <;> intro h
      · contradiction
      · rw [al e]; exact h⟩

/--
Definition of `Bind.g` / `Bind.g` 的定义

English:
definition Bind.g
  signature: : β oplus Computation β -> β oplus (Computation α oplus Computation β)

中文:
定义 Bind.g
  签名: : β oplus Computation β -> β oplus (Computation α oplus Computation β)
-/
def Bind.g : β oplus Computation β -> β oplus (Computation α oplus Computation β)
  | Sum.inl b => Sum.inl b
| Sum.inr cb' => Sum.inr Sum.inr cb'

/--
Definition of `Bind.f` / `Bind.f` 的定义

English:
definition Bind.f
  signature: (f : α -> Computation β)

中文:
定义 Bind.f
  签名: (f : α -> Computation β)
-/
def Bind.f (f : α -> Computation β) :
    Computation α oplus Computation β -> β oplus (Computation α oplus Computation β)
  | Sum.inl ca =>
    match destruct ca with
| Sum.inl a => Bind.g destruct (f a)
| Sum.inr ca' => Sum.inr Sum.inl ca'
| Sum.inr cb => Bind.g destruct cb

/--
Definition of `bind` / `bind` 的定义

English:
definition bind
  signature: (c : Computation α) (f : α -> Computation β)
  body: corec (Bind.f f) (Sum.inl c)

中文:
定义 bind
  签名: (c : Computation α) (f : α -> Computation β)
  定义体: corec (Bind.f f) (Sum.inl c)

Depends on / 依赖: Bind.f, Sum.inl
-/
def bind (c : Computation α) (f : α -> Computation β) : Computation β :=
  corec (Bind.f f) (Sum.inl c)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bind Computation
  body: ⟨@bind⟩

中文:
实例 :
  签名: Bind Computation
  定义体: ⟨@bind⟩
-/
instance : Bind Computation :=
  ⟨@bind⟩

/--
theorem `has_bind_eq_bind` / 定理 `has_bind_eq_bind`

English:
theorem has_bind_eq_bind
  given: {β} (c : Computation α) (f : α -> Computation β)
  statement: c >>= f = bind c f
  proof: rfl

中文:
定理 has_bind_eq_bind
  条件: {β} (c : Computation α) (f : α -> Computation β)
  结论: c >>= f = bind c f
  证明: rfl
-/
theorem has_bind_eq_bind {β} (c : Computation α) (f : α -> Computation β) : c >>= f = bind c f :=
  rfl

/--
Definition of `join` / `join` 的定义

English:
definition join
  signature: (c : Computation (Computation α))
  body: c >>= id

@[simp]

中文:
定义 join
  签名: (c : Computation (Computation α))
  定义体: c >>= id

@[simp]
-/
def join (c : Computation (Computation α)) : Computation α :=
  c >>= id

@[simp]
/--
theorem `map_pure` / 定理 `map_pure`

English:
theorem map_pure
  given: (f : α -> β) (a)
  statement: map f (pure a) = pure (f a)
  proof: rfl

@[simp]

中文:
定理 map_pure
  条件: (f : α -> β) (a)
  结论: map f (pure a) = pure (f a)
  证明: rfl

@[simp]
-/
theorem map_pure (f : α -> β) (a) : map f (pure a) = pure (f a) :=
  rfl

@[simp]
/--
theorem `map_think` / 定理 `map_think`

English:
theorem map_think
  given: (f : α -> β)
  statement: forall s, map f (think s) = think (map f s)

中文:
定理 map_think
  条件: (f : α -> β)
  结论: 对任意 s, map f (think s) = think (map f s)
-/
theorem map_think (f : α -> β) : forall s, map f (think s) = think (map f s)
  | ⟨s, al⟩ => by apply Subtype.ext; dsimp [think, map]; rw [Stream'.map_cons]

@[simp]
/--
theorem `destruct_map` / 定理 `destruct_map`

English:
theorem destruct_map
  given: (f : α -> β) (s)
  statement: destruct (map f s) = lmap f (rmap (map f) (destruct s))
  proof: by
  induction s using recOn <;> simp

@[simp]

中文:
定理 destruct_map
  条件: (f : α -> β) (s)
  结论: destruct (map f s) = lmap f (rmap (map f) (destruct s))
  证明: by
  induction s using recOn <;> simp

@[simp]
-/
theorem destruct_map (f : α -> β) (s) : destruct (map f s) = lmap f (rmap (map f) (destruct s)) := by
  induction s using recOn <;> simp

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: forall s : Computation α, map id s = s
  proof: by ext ⟨⟩ <;> rfl
    have h : ((fun x : Option α => x) = id) := rfl
    simp [e, h, Stream'.map_id]

中文:
定理 map_id
  结论: 对任意 s : Computation α, map id s = s
  证明: by ext ⟨⟩ <;> rfl
    have h : ((fun x : Option α => x) = id) := rfl
    simp [e, h, Stream'.map_id]

Depends on / 依赖: Stream, map_id
-/
theorem map_id : forall s : Computation α, map id s = s
  | ⟨f, al⟩ => by
    apply Subtype.ext; simp only [map, comp_apply, id_eq]
    have e : @Option.rec α (fun _ => Option α) none some = id := by ext ⟨⟩ <;> rfl
    have h : ((fun x : Option α => x) = id) := rfl
    simp [e, h, Stream'.map_id]

/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  given: (f : α -> β) (g : β -> γ)
  statement: forall s : Computation α, map (g ∘ f) s = map g (map f s)

中文:
定理 map_comp
  条件: (f : α -> β) (g : β -> γ)
  结论: 对任意 s : Computation α, map (g ∘ f) s = map g (map f s)
-/
theorem map_comp (f : α -> β) (g : β -> γ) : forall s : Computation α, map (g ∘ f) s = map g (map f s)
  | ⟨s, al⟩ => by
    apply Subtype.ext; dsimp [map]
    apply congr_arg fun f : _ -> Option γ => Stream'.map f s
    ext ⟨⟩ <;> rfl

@[simp]
/--
theorem `ret_bind` / 定理 `ret_bind`

English:
theorem ret_bind
  given: (a) (f : α -> Computation β)
  statement: bind (pure a) f = f a
  proof: by
  apply
    eq_of_bisim fun c₁ c₂ => c₁ = bind (pure a) f ∧ c₂ = f a ∨ c₁ = corec (Bind.f f) (Sum.inr c₂)
  · intro c₁ c₂ h
    match c₁, c₂, h with
    | _, _, Or.inl ⟨rfl, rfl⟩ =>
      simp only [BisimO, bind, Bind.f, corec_eq, rmap, destruct_pure]
      rcases destruct (f a) with b | cb <;> s

中文:
定理 ret_bind
  条件: (a) (f : α -> Computation β)
  结论: bind (pure a) f = f a
  证明: by
  apply
    eq_of_bisim fun c₁ c₂ => c₁ = bind (pure a) f ∧ c₂ = f a ∨ c₁ = corec (Bind.f f) (Sum.inr c₂)
  · intro c₁ c₂ h
    match c₁, c₂, h with
    | _, _, Or.inl ⟨rfl, rfl⟩ =>
      simp only [BisimO, bind, Bind.f, corec_eq, rmap, destruct_pure]
      rcases destruct (f a) with b | cb <;> s

Depends on / 依赖: Bind.f, Bind.g, BisimO, Or.inl, Or.inr, Sum.inr, corec_eq, destruct, destruct_pure, eq_of_bisim
-/
theorem ret_bind (a) (f : α -> Computation β) : bind (pure a) f = f a := by
  apply
    eq_of_bisim fun c₁ c₂ => c₁ = bind (pure a) f ∧ c₂ = f a ∨ c₁ = corec (Bind.f f) (Sum.inr c₂)
  · intro c₁ c₂ h
    match c₁, c₂, h with
    | _, _, Or.inl ⟨rfl, rfl⟩ =>
      simp only [BisimO, bind, Bind.f, corec_eq, rmap, destruct_pure]
      rcases destruct (f a) with b | cb <;> simp [Bind.g]
    | _, c, Or.inr rfl =>
      simp only [BisimO, Bind.f, corec_eq, rmap]
      rcases destruct c with b | cb <;> simp [Bind.g]
  · simp

@[simp]
/--
theorem `think_bind` / 定理 `think_bind`

English:
theorem think_bind
  given: (c) (f : α -> Computation β)
  statement: bind (think c) f = think (bind c f)
  proof: destruct_eq_think by simp [bind, Bind.f]

@[simp]

中文:
定理 think_bind
  条件: (c) (f : α -> Computation β)
  结论: bind (think c) f = think (bind c f)
  证明: destruct_eq_think by simp [bind, Bind.f]

@[simp]

Depends on / 依赖: Bind.f, destruct_eq_think
-/
theorem think_bind (c) (f : α -> Computation β) : bind (think c) f = think (bind c f) :=
destruct_eq_think by simp [bind, Bind.f]

@[simp]
/--
theorem `bind_pure` / 定理 `bind_pure`

English:
theorem bind_pure
  given: (f : α -> β) (s)
  statement: bind s (pure ∘ f) = map f s
  proof: by
  apply eq_of_bisim fun c₁ c₂ => c₁ = c₂ ∨ exists s, c₁ = bind s (pure ∘ f) ∧ c₂ = map f s
  · intro c₁ c₂ h
    match c₁, c₂, h with
    | _, c₂, Or.inl (Eq.refl _) => rcases destruct c₂ with b | cb <;> simp
    | _, _, Or.inr ⟨s, rfl, rfl⟩ =>
      induction s using recOn with
      | pure s =>

中文:
定理 bind_pure
  条件: (f : α -> β) (s)
  结论: bind s (pure ∘ f) = map f s
  证明: by
  apply eq_of_bisim fun c₁ c₂ => c₁ = c₂ ∨ exists s, c₁ = bind s (pure ∘ f) ∧ c₂ = map f s
  · intro c₁ c₂ h
    match c₁, c₂, h with
    | _, c₂, Or.inl (Eq.refl _) => rcases destruct c₂ with b | cb <;> simp
    | _, _, Or.inr ⟨s, rfl, rfl⟩ =>
      induction s using recOn with
      | pure s =>

Depends on / 依赖: Eq.refl, Or.inl, Or.inr, destruct, eq_of_bisim
-/
theorem bind_pure (f : α -> β) (s) : bind s (pure ∘ f) = map f s := by
  apply eq_of_bisim fun c₁ c₂ => c₁ = c₂ ∨ exists s, c₁ = bind s (pure ∘ f) ∧ c₂ = map f s
  · intro c₁ c₂ h
    match c₁, c₂, h with
    | _, c₂, Or.inl (Eq.refl _) => rcases destruct c₂ with b | cb <;> simp
    | _, _, Or.inr ⟨s, rfl, rfl⟩ =>
      induction s using recOn with
      | pure s => simp
      | think s => simpa using Or.inr ⟨s, rfl, rfl⟩
  · exact Or.inr ⟨s, rfl, rfl⟩

@[simp]
/--
theorem `bind_pure'` / 定理 `bind_pure'`

English:
theorem bind_pure'
  given: (s : Computation α)
  statement: bind s pure = s
  proof: by
  simpa using bind_pure id s

@[simp]

中文:
定理 bind_pure'
  条件: (s : Computation α)
  结论: bind s pure = s
  证明: by
  simpa using bind_pure id s

@[simp]

Depends on / 依赖: bind_pure
-/
theorem bind_pure' (s : Computation α) : bind s pure = s := by
  simpa using bind_pure id s

@[simp]
/--
theorem `bind_assoc` / 定理 `bind_assoc`

English:
theorem bind_assoc
  given: (s : Computation α) (f : α -> Computation β) (g : β -> Computation γ)
  proof: by
  apply
    eq_of_bisim fun c₁ c₂ =>
      c₁ = c₂ ∨ exists s, c₁ = bind (bind s f) g ∧ c₂ = bind s fun x : α => bind (f x) g
  · intro c₁ c₂ h
    match c₁, c₂, h with
    | _, c₂, Or.inl (Eq.refl _) => rcases destruct c₂ with b | cb <;> simp
    | _, _, Or.inr ⟨s, rfl, rfl⟩ =>
      induction s

中文:
定理 bind_assoc
  条件: (s : Computation α) (f : α -> Computation β) (g : β -> Computation γ)
  证明: by
  apply
    eq_of_bisim fun c₁ c₂ =>
      c₁ = c₂ ∨ exists s, c₁ = bind (bind s f) g ∧ c₂ = bind s fun x : α => bind (f x) g
  · intro c₁ c₂ h
    match c₁, c₂, h with
    | _, c₂, Or.inl (Eq.refl _) => rcases destruct c₂ with b | cb <;> simp
    | _, _, Or.inr ⟨s, rfl, rfl⟩ =>
      induction s

Depends on / 依赖: BisimO, Eq.refl, Or.inl, Or.inr, destruct, eq_of_bisim, generalize, ret_bind
-/
theorem bind_assoc (s : Computation α) (f : α -> Computation β) (g : β -> Computation γ) :
    bind (bind s f) g = bind s fun x : α => bind (f x) g := by
  apply
    eq_of_bisim fun c₁ c₂ =>
      c₁ = c₂ ∨ exists s, c₁ = bind (bind s f) g ∧ c₂ = bind s fun x : α => bind (f x) g
  · intro c₁ c₂ h
    match c₁, c₂, h with
    | _, c₂, Or.inl (Eq.refl _) => rcases destruct c₂ with b | cb <;> simp
    | _, _, Or.inr ⟨s, rfl, rfl⟩ =>
      induction s using recOn with
      | pure s =>
        simp only [BisimO, ret_bind]; generalize f s = fs
        induction fs using recOn with
        | pure t => rw [ret_bind]; rcases destruct (g t) with b | cb <;> simp
        | think => simp
      | think s => simpa [BisimO] using Or.inr ⟨s, rfl, rfl⟩
  · exact Or.inr ⟨s, rfl, rfl⟩

/--
theorem `results_bind` / 定理 `results_bind`

English:
theorem results_bind
  statement: {s : Computation α} {f : α -> Computation β} {a b m n} (h1 : Results s a m)
  proof: by
  have := h1.mem; revert m
  apply memRecOn this _ fun s IH => _
  · intro _ h1
    rw [ret_bind]
    rw [h1.len_unique (results_pure _)]
    exact h2
  · intro _ h3 _ h1
    rw [think_bind]
    obtain ⟨m', h⟩ := of_results_think h1
    obtain ⟨h1, e⟩ := h
    rw [e]
    exact results_think (h3 h

中文:
定理 results_bind
  结论: {s : Computation α} {f : α -> Computation β} {a b m n} (h1 : Results s a m)
  证明: by
  have := h1.mem; revert m
  apply memRecOn this _ fun s IH => _
  · intro _ h1
    rw [ret_bind]
    rw [h1.len_unique (results_pure _)]
    exact h2
  · intro _ h3 _ h1
    rw [think_bind]
    obtain ⟨m', h⟩ := of_results_think h1
    obtain ⟨h1, e⟩ := h
    rw [e]
    exact results_think (h3 h

Depends on / 依赖: h1.len_unique, h1.mem, len_unique, memRecOn, of_results_think, results_pure, results_think, ret_bind, revert, think_bind
-/
theorem results_bind {s : Computation α} {f : α -> Computation β} {a b m n} (h1 : Results s a m)
    (h2 : Results (f a) b n) : Results (bind s f) b (n + m) := by
  have := h1.mem; revert m
  apply memRecOn this _ fun s IH => _
  · intro _ h1
    rw [ret_bind]
    rw [h1.len_unique (results_pure _)]
    exact h2
  · intro _ h3 _ h1
    rw [think_bind]
    obtain ⟨m', h⟩ := of_results_think h1
    obtain ⟨h1, e⟩ := h
    rw [e]
    exact results_think (h3 h1)

/--
theorem `mem_bind` / 定理 `mem_bind`

English:
theorem mem_bind
  given: {s : Computation α} {f : α -> Computation β} {a b} (h1 : a in s) (h2 : b in f a)
  proof: let ⟨_, h1⟩ := exists_results_of_mem h1
  let ⟨_, h2⟩ := exists_results_of_mem h2
  (results_bind h1 h2).mem

中文:
定理 mem_bind
  条件: {s : Computation α} {f : α -> Computation β} {a b} (h1 : a in s) (h2 : b in f a)
  证明: let ⟨_, h1⟩ := exists_results_of_mem h1
  let ⟨_, h2⟩ := exists_results_of_mem h2
  (results_bind h1 h2).mem

Depends on / 依赖: exists_results_of_mem, results_bind
-/
theorem mem_bind {s : Computation α} {f : α -> Computation β} {a b} (h1 : a in s) (h2 : b in f a) :
    b in bind s f :=
  let ⟨_, h1⟩ := exists_results_of_mem h1
  let ⟨_, h2⟩ := exists_results_of_mem h2
  (results_bind h1 h2).mem

/--
Instance `terminates_bind` / 实例 `terminates_bind`

English:
instance terminates_bind
  signature: (s : Computation α) (f : α -> Computation β) [Terminates s]
  body: terminates_of_mem (mem_bind (get_mem s) (get_mem (f (get s))))

@[simp]

中文:
实例 terminates_bind
  签名: (s : Computation α) (f : α -> Computation β) [Terminates s]
  定义体: terminates_of_mem (mem_bind (get_mem s) (get_mem (f (get s))))

@[simp]

Depends on / 依赖: get_mem, mem_bind, terminates_of_mem
-/
instance terminates_bind (s : Computation α) (f : α -> Computation β) [Terminates s]
    [Terminates (f (get s))] : Terminates (bind s f) :=
  terminates_of_mem (mem_bind (get_mem s) (get_mem (f (get s))))

@[simp]
/--
theorem `get_bind` / 定理 `get_bind`

English:
theorem get_bind
  statement: (s : Computation α) (f : α -> Computation β) [Terminates s]
  proof: get_eq_of_mem _ (mem_bind (get_mem s) (get_mem (f (get s))))

@[simp]

中文:
定理 get_bind
  结论: (s : Computation α) (f : α -> Computation β) [Terminates s]
  证明: get_eq_of_mem _ (mem_bind (get_mem s) (get_mem (f (get s))))

@[simp]

Depends on / 依赖: get_eq_of_mem, get_mem, mem_bind
-/
theorem get_bind (s : Computation α) (f : α -> Computation β) [Terminates s]
    [Terminates (f (get s))] : get (bind s f) = get (f (get s)) :=
  get_eq_of_mem _ (mem_bind (get_mem s) (get_mem (f (get s))))

@[simp]
/--
theorem `length_bind` / 定理 `length_bind`

English:
theorem length_bind
  statement: (s : Computation α) (f : α -> Computation β) [_T1 : Terminates s]
  proof: (results_of_terminates _).len_unique
    results_bind (results_of_terminates _) (results_of_terminates _)

中文:
定理 length_bind
  结论: (s : Computation α) (f : α -> Computation β) [_T1 : Terminates s]
  证明: (results_of_terminates _).len_unique
    results_bind (results_of_terminates _) (results_of_terminates _)

Depends on / 依赖: len_unique, results_bind, results_of_terminates
-/
theorem length_bind (s : Computation α) (f : α -> Computation β) [_T1 : Terminates s]
    [_T2 : Terminates (f (get s))] : length (bind s f) = length (f (get s)) + length s :=
(results_of_terminates _).len_unique
    results_bind (results_of_terminates _) (results_of_terminates _)

/--
theorem `of_results_bind` / 定理 `of_results_bind`

English:
theorem of_results_bind
  given: {s : Computation α} {f : α -> Computation β} {b k}
  proof: by
  induction k generalizing s with | zero | succ n IH <;>
  induction s using recOn with intro h | pure a | think s'
  · simp only [ret_bind] at h
    exact ⟨_, _, _, results_pure _, h, rfl⟩
  · have := congr_arg head (eq_thinkN h)
    contradiction
  · simp only [ret_bind] at h
    exact ⟨_, _, n

中文:
定理 of_results_bind
  条件: {s : Computation α} {f : α -> Computation β} {b k}
  证明: by
  induction k generalizing s with | zero | succ n IH <;>
  induction s using recOn with intro h | pure a | think s'
  · simp only [ret_bind] at h
    exact ⟨_, _, _, results_pure _, h, rfl⟩
  · have := congr_arg head (eq_thinkN h)
    contradiction
  · simp only [ret_bind] at h
    exact ⟨_, _, n

Depends on / 依赖: congr_arg, eq_thinkN, generalizing, m.succ, results_pure, results_think, results_think_iff, ret_bind, think_bind
-/
theorem of_results_bind {s : Computation α} {f : α -> Computation β} {b k} :
    Results (bind s f) b k -> exists a m n, Results s a m ∧ Results (f a) b n ∧ k = n + m := by
  induction k generalizing s with | zero | succ n IH <;>
  induction s using recOn with intro h | pure a | think s'
  · simp only [ret_bind] at h
    exact ⟨_, _, _, results_pure _, h, rfl⟩
  · have := congr_arg head (eq_thinkN h)
    contradiction
  · simp only [ret_bind] at h
    exact ⟨_, _, n + 1, results_pure _, h, rfl⟩
  · simp only [think_bind, results_think_iff] at h
    let ⟨a, m, n', h1, h2, e'⟩ := IH h
    rw [e']
    exact ⟨a, m.succ, n', results_think h1, h2, rfl⟩

/--
theorem `exists_of_mem_bind` / 定理 `exists_of_mem_bind`

English:
theorem exists_of_mem_bind
  given: {s : Computation α} {f : α -> Computation β} {b} (h : b in bind s f)
  proof: let ⟨_, h⟩ := exists_results_of_mem h
  let ⟨a, _, _, h1, h2, _⟩ := of_results_bind h
  ⟨a, h1.mem, h2.mem⟩

中文:
定理 存在_of_mem_bind
  条件: {s : Computation α} {f : α -> Computation β} {b} (h : b in bind s f)
  证明: let ⟨_, h⟩ := exists_results_of_mem h
  let ⟨a, _, _, h1, h2, _⟩ := of_results_bind h
  ⟨a, h1.mem, h2.mem⟩

Depends on / 依赖: exists_results_of_mem, h1.mem, h2.mem, of_results_bind
-/
theorem exists_of_mem_bind {s : Computation α} {f : α -> Computation β} {b} (h : b in bind s f) :
    exists a in s, b in f a :=
  let ⟨_, h⟩ := exists_results_of_mem h
  let ⟨a, _, _, h1, h2, _⟩ := of_results_bind h
  ⟨a, h1.mem, h2.mem⟩

/--
theorem `bind_promises` / 定理 `bind_promises`

English:
theorem bind_promises
  statement: {s : Computation α} {f : α -> Computation β} {a b} (h1 : s ~> a)
  proof: fun b' bB => by
  rcases exists_of_mem_bind bB with ⟨a', a's, ba'⟩
  rw [← h1 a's] at ba'; exact h2 ba'

中文:
定理 bind_promises
  结论: {s : Computation α} {f : α -> Computation β} {a b} (h1 : s ~> a)
  证明: fun b' bB => by
  rcases exists_of_mem_bind bB with ⟨a', a's, ba'⟩
  rw [← h1 a's] at ba'; exact h2 ba'

Depends on / 依赖: exists_of_mem_bind
-/
theorem bind_promises {s : Computation α} {f : α -> Computation β} {a b} (h1 : s ~> a)
    (h2 : f a ~> b) : bind s f ~> b := fun b' bB => by
  rcases exists_of_mem_bind bB with ⟨a', a's, ba'⟩
  rw [← h1 a's] at ba'; exact h2 ba'

/--
Instance `monad` / 实例 `monad`

English:
instance monad
  signature: : Monad Computation where
  body: @map
  pure := @pure
  bind := @bind

中文:
实例 monad
  签名: : 单子 Computation where
  定义体: @map
  pure := @pure
  bind := @bind
-/
instance monad : Monad Computation where
  map := @map
  pure := @pure
  bind := @bind

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulMonad Computation
  body: LawfulMonad.mk'
  (id_map := @map_id)
  (bind_pure_comp := @bind_pure)
  (pure_bind := @ret_bind)
  (bind_assoc := @bind_assoc)

中文:
实例 :
  签名: 合法单子 Computation
  定义体: LawfulMonad.mk'
  (id_map := @map_id)
  (bind_pure_comp := @bind_pure)
  (pure_bind := @ret_bind)
  (bind_assoc := @bind_assoc)

Depends on / 依赖: LawfulMonad, LawfulMonad.mk
-/
instance : LawfulMonad Computation := LawfulMonad.mk'
  (id_map := @map_id)
  (bind_pure_comp := @bind_pure)
  (pure_bind := @ret_bind)
  (bind_assoc := @bind_assoc)

/--
theorem `has_map_eq_map` / 定理 `has_map_eq_map`

English:
theorem has_map_eq_map
  given: {β} (f : α -> β) (c : Computation α)
  statement: f < > c = map f c
  proof: rfl

@[simp]

中文:
定理 has_map_eq_map
  条件: {β} (f : α -> β) (c : Computation α)
  结论: f < > c = map f c
  证明: rfl

@[simp]
-/
theorem has_map_eq_map {β} (f : α -> β) (c : Computation α) : f < > c = map f c :=
  rfl

@[simp]
/--
theorem `pure_def` / 定理 `pure_def`

English:
theorem pure_def
  given: (a)
  statement: (return a : Computation α) = pure a
  proof: rfl

@[simp]

中文:
定理 pure_def
  条件: (a)
  结论: (return a : Computation α) = pure a
  证明: rfl

@[simp]
-/
theorem pure_def (a) : (return a : Computation α) = pure a :=
  rfl

@[simp]
/--
theorem `map_pure'` / 定理 `map_pure'`

English:
theorem map_pure'
  given: {α β}
  statement: forall (f : α -> β) (a), f < > pure a = pure (f a)
  proof: map_pure

@[simp]

中文:
定理 map_pure'
  条件: {α β}
  结论: 对任意 (f : α -> β) (a), f < > pure a = pure (f a)
  证明: map_pure

@[simp]

Depends on / 依赖: map_pure
-/
theorem map_pure' {α β} : forall (f : α -> β) (a), f < > pure a = pure (f a) :=
  map_pure

@[simp]
/--
theorem `map_think'` / 定理 `map_think'`

English:
theorem map_think'
  given: {α β}
  statement: forall (f : α -> β) (s), f < > think s = think (f <$> s)
  proof: map_think

中文:
定理 map_think'
  条件: {α β}
  结论: 对任意 (f : α -> β) (s), f < > think s = think (f <$> s)
  证明: map_think

Depends on / 依赖: map_think
-/
theorem map_think' {α β} : forall (f : α -> β) (s), f < > think s = think (f <$> s) :=
  map_think

/--
theorem `mem_map` / 定理 `mem_map`

English:
theorem mem_map
  given: (f : α -> β) {a} {s : Computation α} (m : a in s)
  statement: f a in map f s
  proof: by
  rw [← bind_pure]; apply mem_bind m; apply ret_mem

中文:
定理 mem_map
  条件: (f : α -> β) {a} {s : Computation α} (m : a in s)
  结论: f a in map f s
  证明: by
  rw [← bind_pure]; apply mem_bind m; apply ret_mem

Depends on / 依赖: bind_pure, mem_bind, ret_mem
-/
theorem mem_map (f : α -> β) {a} {s : Computation α} (m : a in s) : f a in map f s := by
  rw [← bind_pure]; apply mem_bind m; apply ret_mem

/--
theorem `exists_of_mem_map` / 定理 `exists_of_mem_map`

English:
theorem exists_of_mem_map
  given: {f : α -> β} {b : β} {s : Computation α} (h : b in map f s)
  proof: by
  rw [← bind_pure] at h
  let ⟨a, as, fb⟩ := exists_of_mem_bind h
  exact ⟨a, as, mem_unique (ret_mem _) fb⟩

中文:
定理 存在_of_mem_map
  条件: {f : α -> β} {b : β} {s : Computation α} (h : b in map f s)
  证明: by
  rw [← bind_pure] at h
  let ⟨a, as, fb⟩ := exists_of_mem_bind h
  exact ⟨a, as, mem_unique (ret_mem _) fb⟩

Depends on / 依赖: bind_pure, exists_of_mem_bind, mem_unique, ret_mem
-/
theorem exists_of_mem_map {f : α -> β} {b : β} {s : Computation α} (h : b in map f s) :
    exists a, a in s ∧ f a = b := by
  rw [← bind_pure] at h
  let ⟨a, as, fb⟩ := exists_of_mem_bind h
  exact ⟨a, as, mem_unique (ret_mem _) fb⟩

/--
Instance `terminates_map` / 实例 `terminates_map`

English:
instance terminates_map
  signature: (f : α -> β) (s : Computation α) [Terminates s]
  body: by
  rw [← bind_pure]; exact terminates_of_mem (mem_bind (get_mem s) (get_mem (α := β) (f (get s))))

中文:
实例 terminates_map
  签名: (f : α -> β) (s : Computation α) [Terminates s]
  定义体: by
  rw [← bind_pure]; exact terminates_of_mem (mem_bind (get_mem s) (get_mem (α := β) (f (get s))))

Depends on / 依赖: bind_pure, get_mem, mem_bind, terminates_of_mem
-/
instance terminates_map (f : α -> β) (s : Computation α) [Terminates s] : Terminates (map f s) := by
  rw [← bind_pure]; exact terminates_of_mem (mem_bind (get_mem s) (get_mem (α := β) (f (get s))))

/--
theorem `terminates_map_iff` / 定理 `terminates_map_iff`

English:
theorem terminates_map_iff
  given: (f : α -> β) (s : Computation α)
  statement: Terminates (map f s) ↔ Terminates s
  proof: ⟨fun ⟨⟨_, h⟩⟩ =>
    let ⟨_, h1, _⟩ := exists_of_mem_map h
    ⟨⟨_, h1⟩⟩,
    @Computation.terminates_map _ _ _ _⟩

中文:
定理 terminates_map_iff
  条件: (f : α -> β) (s : Computation α)
  结论: Terminates (map f s) ↔ Terminates s
  证明: ⟨fun ⟨⟨_, h⟩⟩ =>
    let ⟨_, h1, _⟩ := exists_of_mem_map h
    ⟨⟨_, h1⟩⟩,
    @Computation.terminates_map _ _ _ _⟩

Depends on / 依赖: Computation, Computation.terminates_map, exists_of_mem_map, terminates_map
-/
theorem terminates_map_iff (f : α -> β) (s : Computation α) : Terminates (map f s) ↔ Terminates s :=
  ⟨fun ⟨⟨_, h⟩⟩ =>
    let ⟨_, h1, _⟩ := exists_of_mem_map h
    ⟨⟨_, h1⟩⟩,
    @Computation.terminates_map _ _ _ _⟩

-- Parallel computation
/--
Definition of `orElse` / `orElse` 的定义

English:
definition orElse
  signature: (c₁ : Computation α) (c₂ : Unit -> Computation α)
  body: @Computation.corec α (Computation α × Computation α)
    (fun ⟨c₁, c₂⟩ =>
      match destruct c₁ with
      | Sum.inl a => Sum.inl a
      | Sum.inr c₁' =>
        match destruct c₂ with
        | Sum.inl a => Sum.inl a
        | Sum.inr c₂' => Sum.inr (c₁', c₂'))
    (c₁, c₂ ())

中文:
定义 orElse
  签名: (c₁ : Computation α) (c₂ : 单元 -> Computation α)
  定义体: @Computation.corec α (Computation α × Computation α)
    (fun ⟨c₁, c₂⟩ =>
      match destruct c₁ with
      | Sum.inl a => Sum.inl a
      | Sum.inr c₁' =>
        match destruct c₂ with
        | Sum.inl a => Sum.inl a
        | Sum.inr c₂' => Sum.inr (c₁', c₂'))
    (c₁, c₂ ())

Depends on / 依赖: Computation, Computation.corec, Sum.inl, Sum.inr, destruct
-/
def orElse (c₁ : Computation α) (c₂ : Unit -> Computation α) : Computation α :=
  @Computation.corec α (Computation α × Computation α)
    (fun ⟨c₁, c₂⟩ =>
      match destruct c₁ with
      | Sum.inl a => Sum.inl a
      | Sum.inr c₁' =>
        match destruct c₂ with
        | Sum.inl a => Sum.inl a
        | Sum.inr c₂' => Sum.inr (c₁', c₂'))
    (c₁, c₂ ())

/--
Instance `instAlternativeComputation` / 实例 `instAlternativeComputation`

English:
instance instAlternativeComputation
  signature: : Alternative Computation
  body: { Computation.monad with
    orElse := @orElse
    failure := @empty }

@[simp]

中文:
实例 instAlternativeComputation
  签名: : Alternative Computation
  定义体: { Computation.monad with
    orElse := @orElse
    failure := @empty }

@[simp]

Depends on / 依赖: Computation, Computation.monad, failure, orElse
-/
instance instAlternativeComputation : Alternative Computation :=
  { Computation.monad with
    orElse := @orElse
    failure := @empty }

@[simp]
/--
theorem `ret_orElse` / 定理 `ret_orElse`

English:
theorem ret_orElse
  given: (a : α) (c₂ : Computation α)
  statement: (pure a <|> c₂) = pure a
  proof: destruct_eq_pure by
    unfold_projs
    simp [orElse]

@[simp]

中文:
定理 ret_orElse
  条件: (a : α) (c₂ : Computation α)
  结论: (pure a <|> c₂) = pure a
  证明: destruct_eq_pure by
    unfold_projs
    simp [orElse]

@[simp]

Depends on / 依赖: destruct_eq_pure, orElse, unfold_projs
-/
theorem ret_orElse (a : α) (c₂ : Computation α) : (pure a <|> c₂) = pure a :=
destruct_eq_pure by
    unfold_projs
    simp [orElse]

@[simp]
/--
theorem `orElse_pure` / 定理 `orElse_pure`

English:
theorem orElse_pure
  given: (c₁ : Computation α) (a : α)
  statement: (think c₁ <|> pure a) = pure a
  proof: destruct_eq_pure by
    unfold_projs
    simp [orElse]

@[simp]

中文:
定理 orElse_pure
  条件: (c₁ : Computation α) (a : α)
  结论: (think c₁ <|> pure a) = pure a
  证明: destruct_eq_pure by
    unfold_projs
    simp [orElse]

@[simp]

Depends on / 依赖: destruct_eq_pure, orElse, unfold_projs
-/
theorem orElse_pure (c₁ : Computation α) (a : α) : (think c₁ <|> pure a) = pure a :=
destruct_eq_pure by
    unfold_projs
    simp [orElse]

@[simp]
/--
theorem `orElse_think` / 定理 `orElse_think`

English:
theorem orElse_think
  given: (c₁ c₂ : Computation α)
  statement: (think c₁ <|> think c₂) = think (c₁ <|> c₂)
  proof: destruct_eq_think by
    unfold_projs
    simp [orElse]

@[simp]

中文:
定理 orElse_think
  条件: (c₁ c₂ : Computation α)
  结论: (think c₁ <|> think c₂) = think (c₁ <|> c₂)
  证明: destruct_eq_think by
    unfold_projs
    simp [orElse]

@[simp]

Depends on / 依赖: destruct_eq_think, orElse, unfold_projs
-/
theorem orElse_think (c₁ c₂ : Computation α) : (think c₁ <|> think c₂) = think (c₁ <|> c₂) :=
destruct_eq_think by
    unfold_projs
    simp [orElse]

@[simp]
/--
theorem `empty_orElse` / 定理 `empty_orElse`

English:
theorem empty_orElse
  given: (c)
  statement: (empty α <|> c) = c
  proof: by
  apply eq_of_bisim (fun c₁ c₂ => (empty α <|> c₂) = c₁) _ rfl
  intro s' s h; rw [← h]
  induction s using recOn with rw [think_empty]
  | pure s => simp
  | think s => simp only [BisimO, orElse_think, destruct_think]; rw [← think_empty]

@[simp]

中文:
定理 empty_orElse
  条件: (c)
  结论: (empty α <|> c) = c
  证明: by
  apply eq_of_bisim (fun c₁ c₂ => (empty α <|> c₂) = c₁) _ rfl
  intro s' s h; rw [← h]
  induction s using recOn with rw [think_empty]
  | pure s => simp
  | think s => simp only [BisimO, orElse_think, destruct_think]; rw [← think_empty]

@[simp]

Depends on / 依赖: BisimO, destruct_think, eq_of_bisim, orElse_think, think_empty
-/
theorem empty_orElse (c) : (empty α <|> c) = c := by
  apply eq_of_bisim (fun c₁ c₂ => (empty α <|> c₂) = c₁) _ rfl
  intro s' s h; rw [← h]
  induction s using recOn with rw [think_empty]
  | pure s => simp
  | think s => simp only [BisimO, orElse_think, destruct_think]; rw [← think_empty]

@[simp]
/--
theorem `orElse_empty` / 定理 `orElse_empty`

English:
theorem orElse_empty
  given: (c : Computation α)
  statement: (c <|> empty α) = c
  proof: by
  apply eq_of_bisim (fun c₁ c₂ => (c₂ <|> empty α) = c₁) _ rfl
  intro s' s h; rw [← h]
  induction s using recOn with rw [think_empty]
  | pure s => simp
  | think s => simp only [BisimO, orElse_think, destruct_think]; rw [← think_empty]

中文:
定理 orElse_empty
  条件: (c : Computation α)
  结论: (c <|> empty α) = c
  证明: by
  apply eq_of_bisim (fun c₁ c₂ => (c₂ <|> empty α) = c₁) _ rfl
  intro s' s h; rw [← h]
  induction s using recOn with rw [think_empty]
  | pure s => simp
  | think s => simp only [BisimO, orElse_think, destruct_think]; rw [← think_empty]

Depends on / 依赖: BisimO, destruct_think, eq_of_bisim, orElse_think, think_empty
-/
theorem orElse_empty (c : Computation α) : (c <|> empty α) = c := by
  apply eq_of_bisim (fun c₁ c₂ => (c₂ <|> empty α) = c₁) _ rfl
  intro s' s h; rw [← h]
  induction s using recOn with rw [think_empty]
  | pure s => simp
  | think s => simp only [BisimO, orElse_think, destruct_think]; rw [← think_empty]

/--
Definition of `Equiv` / `Equiv` 的定义

English:
definition Equiv
  signature: (c₁ c₂ : Computation α)
  body: forall a, a in c₁ ↔ a in c₂

中文:
定义 等价
  签名: (c₁ c₂ : Computation α)
  定义体: forall a, a in c₁ ↔ a in c₂
-/
def Equiv (c₁ c₂ : Computation α) : Prop :=
  forall a, a in c₁ ↔ a in c₂

/-- equivalence relation for computations -/
scoped infixl:50 " ~ " => Equiv

@[refl]
/--
theorem `Equiv.refl` / 定理 `Equiv.refl`

English:
theorem Equiv.refl
  given: (s : Computation α)
  statement: s ~ s
  proof: fun _ => Iff.rfl

@[symm]

中文:
定理 等价.refl
  条件: (s : Computation α)
  结论: s ~ s
  证明: fun _ => Iff.rfl

@[symm]

Depends on / 依赖: Iff.rfl
-/
theorem Equiv.refl (s : Computation α) : s ~ s := fun _ => Iff.rfl

@[symm]
/--
theorem `Equiv.symm` / 定理 `Equiv.symm`

English:
theorem Equiv.symm
  given: {s t : Computation α}
  statement: s ~ t -> t ~ s
  proof: fun h a => (h a).symm

@[trans]

中文:
定理 等价.symm
  条件: {s t : Computation α}
  结论: s ~ t -> t ~ s
  证明: fun h a => (h a).symm

@[trans]
-/
theorem Equiv.symm {s t : Computation α} : s ~ t -> t ~ s := fun h a => (h a).symm

@[trans]
/--
theorem `Equiv.trans` / 定理 `Equiv.trans`

English:
theorem Equiv.trans
  given: {s t u : Computation α}
  statement: s ~ t -> t ~ u -> s ~ u
  proof: fun h1 h2 a =>
  (h1 a).trans (h2 a)

中文:
定理 等价.trans
  条件: {s t u : Computation α}
  结论: s ~ t -> t ~ u -> s ~ u
  证明: fun h1 h2 a =>
  (h1 a).trans (h2 a)
-/
theorem Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~ u := fun h1 h2 a =>
  (h1 a).trans (h2 a)

/--
theorem `Equiv.equivalence` / 定理 `Equiv.equivalence`

English:
theorem Equiv.equivalence
  statement: Equivalence (@Equiv α)
  proof: ⟨@Equiv.refl _, @Equiv.symm _, @Equiv.trans _⟩

中文:
定理 等价.equivalence
  结论: 等价 (@等价 α)
  证明: ⟨@Equiv.refl _, @Equiv.symm _, @Equiv.trans _⟩

Depends on / 依赖: Equiv.refl, Equiv.symm, Equiv.trans
-/
theorem Equiv.equivalence : Equivalence (@Equiv α) :=
  ⟨@Equiv.refl _, @Equiv.symm _, @Equiv.trans _⟩

/--
theorem `equiv_of_mem` / 定理 `equiv_of_mem`

English:
theorem equiv_of_mem
  given: {s t : Computation α} {a} (h1 : a in s) (h2 : a in t)
  statement: s ~ t
  proof: fun a' =>
  ⟨fun ma => by rw [mem_unique ma h1]; exact h2, fun ma => by rw [mem_unique ma h2]; exact h1⟩

中文:
定理 equiv_of_mem
  条件: {s t : Computation α} {a} (h1 : a in s) (h2 : a in t)
  结论: s ~ t
  证明: fun a' =>
  ⟨fun ma => by rw [mem_unique ma h1]; exact h2, fun ma => by rw [mem_unique ma h2]; exact h1⟩
-/
theorem equiv_of_mem {s t : Computation α} {a} (h1 : a in s) (h2 : a in t) : s ~ t := fun a' =>
  ⟨fun ma => by rw [mem_unique ma h1]; exact h2, fun ma => by rw [mem_unique ma h2]; exact h1⟩

/--
theorem `terminates_congr` / 定理 `terminates_congr`

English:
theorem terminates_congr
  given: {c₁ c₂ : Computation α} (h : c₁ ~ c₂)
  statement: Terminates c₁ ↔ Terminates c₂
  proof: by
  simp only [terminates_iff, exists_congr h]

中文:
定理 terminates_congr
  条件: {c₁ c₂ : Computation α} (h : c₁ ~ c₂)
  结论: Terminates c₁ ↔ Terminates c₂
  证明: by
  simp only [terminates_iff, exists_congr h]

Depends on / 依赖: exists_congr, terminates_iff
-/
theorem terminates_congr {c₁ c₂ : Computation α} (h : c₁ ~ c₂) : Terminates c₁ ↔ Terminates c₂ := by
  simp only [terminates_iff, exists_congr h]

/--
theorem `promises_congr` / 定理 `promises_congr`

English:
theorem promises_congr
  given: {c₁ c₂ : Computation α} (h : c₁ ~ c₂) (a)
  statement: c₁ ~> a ↔ c₂ ~> a
  proof: forall_congr' fun a' => imp_congr (h a') Iff.rfl

中文:
定理 promises_congr
  条件: {c₁ c₂ : Computation α} (h : c₁ ~ c₂) (a)
  结论: c₁ ~> a ↔ c₂ ~> a
  证明: forall_congr' fun a' => imp_congr (h a') Iff.rfl

Depends on / 依赖: Iff.rfl, forall_congr, imp_congr
-/
theorem promises_congr {c₁ c₂ : Computation α} (h : c₁ ~ c₂) (a) : c₁ ~> a ↔ c₂ ~> a :=
  forall_congr' fun a' => imp_congr (h a') Iff.rfl

/--
theorem `get_equiv` / 定理 `get_equiv`

English:
theorem get_equiv
  given: {c₁ c₂ : Computation α} (h : c₁ ~ c₂) [Terminates c₁] [Terminates c₂]
  proof: get_eq_of_mem _ (h _).2 get_mem _

中文:
定理 get_equiv
  条件: {c₁ c₂ : Computation α} (h : c₁ ~ c₂) [Terminates c₁] [Terminates c₂]
  证明: get_eq_of_mem _ (h _).2 get_mem _

Depends on / 依赖: get_eq_of_mem, get_mem
-/
theorem get_equiv {c₁ c₂ : Computation α} (h : c₁ ~ c₂) [Terminates c₁] [Terminates c₂] :
    get c₁ = get c₂ :=
get_eq_of_mem _ (h _).2 get_mem _

/--
theorem `think_equiv` / 定理 `think_equiv`

English:
theorem think_equiv
  given: (s : Computation α)
  statement: think s ~ s
  proof: fun _ => ⟨of_think_mem, think_mem⟩

中文:
定理 think_equiv
  条件: (s : Computation α)
  结论: think s ~ s
  证明: fun _ => ⟨of_think_mem, think_mem⟩

Depends on / 依赖: of_think_mem, think_mem
-/
theorem think_equiv (s : Computation α) : think s ~ s := fun _ => ⟨of_think_mem, think_mem⟩

/--
theorem `thinkN_equiv` / 定理 `thinkN_equiv`

English:
theorem thinkN_equiv
  given: (s : Computation α) (n)
  statement: thinkN s n ~ s
  proof: fun _ => thinkN_mem n

中文:
定理 thinkN_equiv
  条件: (s : Computation α) (n)
  结论: thinkN s n ~ s
  证明: fun _ => thinkN_mem n

Depends on / 依赖: thinkN_mem
-/
theorem thinkN_equiv (s : Computation α) (n) : thinkN s n ~ s := fun _ => thinkN_mem n

/--
theorem `bind_congr` / 定理 `bind_congr`

English:
theorem bind_congr
  statement: {s1 s2 : Computation α} {f1 f2 : α -> Computation β} (h1 : s1 ~ s2)
  proof: fun b =>
  ⟨fun h =>
    let ⟨a, ha, hb⟩ := exists_of_mem_bind h
    mem_bind ((h1 a).1 ha) ((h2 a b).1 hb),
    fun h =>
    let ⟨a, ha, hb⟩ := exists_of_mem_bind h
    mem_bind ((h1 a).2 ha) ((h2 a b).2 hb)⟩

中文:
定理 bind_congr
  结论: {s1 s2 : Computation α} {f1 f2 : α -> Computation β} (h1 : s1 ~ s2)
  证明: fun b =>
  ⟨fun h =>
    let ⟨a, ha, hb⟩ := exists_of_mem_bind h
    mem_bind ((h1 a).1 ha) ((h2 a b).1 hb),
    fun h =>
    let ⟨a, ha, hb⟩ := exists_of_mem_bind h
    mem_bind ((h1 a).2 ha) ((h2 a b).2 hb)⟩
-/
theorem bind_congr {s1 s2 : Computation α} {f1 f2 : α -> Computation β} (h1 : s1 ~ s2)
    (h2 : forall a, f1 a ~ f2 a) : bind s1 f1 ~ bind s2 f2 := fun b =>
  ⟨fun h =>
    let ⟨a, ha, hb⟩ := exists_of_mem_bind h
    mem_bind ((h1 a).1 ha) ((h2 a b).1 hb),
    fun h =>
    let ⟨a, ha, hb⟩ := exists_of_mem_bind h
    mem_bind ((h1 a).2 ha) ((h2 a b).2 hb)⟩

/--
theorem `equiv_pure_of_mem` / 定理 `equiv_pure_of_mem`

English:
theorem equiv_pure_of_mem
  given: {s : Computation α} {a} (h : a in s)
  statement: s ~ pure a
  proof: equiv_of_mem h (ret_mem _)

中文:
定理 equiv_pure_of_mem
  条件: {s : Computation α} {a} (h : a in s)
  结论: s ~ pure a
  证明: equiv_of_mem h (ret_mem _)

Depends on / 依赖: equiv_of_mem, ret_mem
-/
theorem equiv_pure_of_mem {s : Computation α} {a} (h : a in s) : s ~ pure a :=
  equiv_of_mem h (ret_mem _)

/--
Definition of `LiftRel` / `LiftRel` 的定义

English:
definition LiftRel
  signature: (R : α -> β -> Prop) (ca : Computation α) (cb : Computation β)
  body: (forall {a}, a in ca -> exists b, b in cb ∧ R a b) ∧ forall {b}, b in cb -> exists a, a in ca ∧ R a b

中文:
定义 LiftRel
  签名: (R : α -> β -> 命题) (ca : Computation α) (cb : Computation β)
  定义体: (forall {a}, a in ca -> exists b, b in cb ∧ R a b) ∧ forall {b}, b in cb -> exists a, a in ca ∧ R a b
-/
def LiftRel (R : α -> β -> Prop) (ca : Computation α) (cb : Computation β) : Prop :=
  (forall {a}, a in ca -> exists b, b in cb ∧ R a b) ∧ forall {b}, b in cb -> exists a, a in ca ∧ R a b

/--
theorem `LiftRel.swap` / 定理 `LiftRel.swap`

English:
theorem LiftRel.swap
  given: (R : α -> β -> Prop) (ca : Computation α) (cb : Computation β)
  proof: @and_comm _ _

中文:
定理 LiftRel.swap
  条件: (R : α -> β -> 命题) (ca : Computation α) (cb : Computation β)
  证明: @and_comm _ _

Depends on / 依赖: and_comm
-/
theorem LiftRel.swap (R : α -> β -> Prop) (ca : Computation α) (cb : Computation β) :
    LiftRel (swap R) cb ca ↔ LiftRel R ca cb :=
  @and_comm _ _

/--
theorem `lift_eq_iff_equiv` / 定理 `lift_eq_iff_equiv`

English:
theorem lift_eq_iff_equiv
  given: (c₁ c₂ : Computation α)
  statement: LiftRel (· = ·) c₁ c₂ ↔ c₁ ~ c₂
  proof: ⟨fun ⟨h1, h2⟩ a =>
    ⟨fun a1 => by let ⟨b, b2, ab⟩ := h1 a1; rwa [ab],
     fun a2 => by let ⟨b, b1, ab⟩ := h2 a2; rwa [← ab]⟩,
    fun e => ⟨fun {a} a1 => ⟨a, (e _).1 a1, rfl⟩, fun {a} a2 => ⟨a, (e _).2 a2, rfl⟩⟩⟩

中文:
定理 lift_eq_iff_equiv
  条件: (c₁ c₂ : Computation α)
  结论: LiftRel (· = ·) c₁ c₂ ↔ c₁ ~ c₂
  证明: ⟨fun ⟨h1, h2⟩ a =>
    ⟨fun a1 => by let ⟨b, b2, ab⟩ := h1 a1; rwa [ab],
     fun a2 => by let ⟨b, b1, ab⟩ := h2 a2; rwa [← ab]⟩,
    fun e => ⟨fun {a} a1 => ⟨a, (e _).1 a1, rfl⟩, fun {a} a2 => ⟨a, (e _).2 a2, rfl⟩⟩⟩
-/
theorem lift_eq_iff_equiv (c₁ c₂ : Computation α) : LiftRel (· = ·) c₁ c₂ ↔ c₁ ~ c₂ :=
  ⟨fun ⟨h1, h2⟩ a =>
    ⟨fun a1 => by let ⟨b, b2, ab⟩ := h1 a1; rwa [ab],
     fun a2 => by let ⟨b, b1, ab⟩ := h2 a2; rwa [← ab]⟩,
    fun e => ⟨fun {a} a1 => ⟨a, (e _).1 a1, rfl⟩, fun {a} a2 => ⟨a, (e _).2 a2, rfl⟩⟩⟩

/--
Instance `LiftRel.refl` / 实例 `LiftRel.refl`

English:
instance LiftRel.refl
  signature: (R : α -> α -> Prop) [Std.Refl R]
  body: ⟨fun {a} as => ⟨a, as, refl_of R a⟩, fun {b} bs => ⟨b, bs, refl_of R b⟩⟩

中文:
实例 LiftRel.refl
  签名: (R : α -> α -> 命题) [Std.Refl R]
  定义体: ⟨fun {a} as => ⟨a, as, refl_of R a⟩, fun {b} bs => ⟨b, bs, refl_of R b⟩⟩

Depends on / 依赖: refl_of
-/
instance LiftRel.refl (R : α -> α -> Prop) [Std.Refl R] : Std.Refl (LiftRel R) where
  refl _ := ⟨fun {a} as => ⟨a, as, refl_of R a⟩, fun {b} bs => ⟨b, bs, refl_of R b⟩⟩

/--
Instance `LiftRel.symm` / 实例 `LiftRel.symm`

English:
instance LiftRel.symm
  signature: (R : α -> α -> Prop) [Std.Symm R]
  body: fun ⟨l, r⟩ => {
    left a2 :=
      let ⟨b, b1, ab⟩ := r a2
      ⟨b, b1, symm_of R ab⟩
    right a1 :=
      let ⟨b, b2, ab⟩ := l a1
      ⟨b, b2, symm_of R ab⟩
  }

中文:
实例 LiftRel.symm
  签名: (R : α -> α -> 命题) [Std.Symm R]
  定义体: fun ⟨l, r⟩ => {
    left a2 :=
      let ⟨b, b1, ab⟩ := r a2
      ⟨b, b1, symm_of R ab⟩
    right a1 :=
      let ⟨b, b2, ab⟩ := l a1
      ⟨b, b2, symm_of R ab⟩
  }
-/
instance LiftRel.symm (R : α -> α -> Prop) [Std.Symm R] : Std.Symm (LiftRel R) where
  symm _ _ := fun ⟨l, r⟩ => {
    left a2 :=
      let ⟨b, b1, ab⟩ := r a2
      ⟨b, b1, symm_of R ab⟩
    right a1 :=
      let ⟨b, b2, ab⟩ := l a1
      ⟨b, b2, symm_of R ab⟩
  }

/--
Instance `LiftRel.trans` / 实例 `LiftRel.trans`

English:
instance LiftRel.trans
  signature: (R : α -> α -> Prop) [IsTrans α R]
  body: ⟨fun _ _ _ ⟨l1, r1⟩ ⟨l2, r2⟩ =>
  ⟨fun {_a} a1 =>
    let ⟨_b, b2, ab⟩ := l1 a1
    let ⟨c, c3, bc⟩ := l2 b2
    ⟨c, c3, trans_of R ab bc⟩,
    fun {_c} c3 =>
    let ⟨_b, b2, bc⟩ := r2 c3
    let ⟨a, a1, ab⟩ := r1 b2
    ⟨a, a1, trans_of R ab bc⟩⟩⟩

中文:
实例 LiftRel.trans
  签名: (R : α -> α -> 命题) [是Trans α R]
  定义体: ⟨fun _ _ _ ⟨l1, r1⟩ ⟨l2, r2⟩ =>
  ⟨fun {_a} a1 =>
    let ⟨_b, b2, ab⟩ := l1 a1
    let ⟨c, c3, bc⟩ := l2 b2
    ⟨c, c3, trans_of R ab bc⟩,
    fun {_c} c3 =>
    let ⟨_b, b2, bc⟩ := r2 c3
    let ⟨a, a1, ab⟩ := r1 b2
    ⟨a, a1, trans_of R ab bc⟩⟩⟩

Depends on / 依赖: trans_of
-/
instance LiftRel.trans (R : α -> α -> Prop) [IsTrans α R] : IsTrans _ (LiftRel R) :=
  ⟨fun _ _ _ ⟨l1, r1⟩ ⟨l2, r2⟩ =>
  ⟨fun {_a} a1 =>
    let ⟨_b, b2, ab⟩ := l1 a1
    let ⟨c, c3, bc⟩ := l2 b2
    ⟨c, c3, trans_of R ab bc⟩,
    fun {_c} c3 =>
    let ⟨_b, b2, bc⟩ := r2 c3
    let ⟨a, a1, ab⟩ := r1 b2
    ⟨a, a1, trans_of R ab bc⟩⟩⟩

/--
theorem `LiftRel.equiv` / 定理 `LiftRel.equiv`

English:
theorem LiftRel.equiv
  given: (R : α -> α -> Prop) (H : Equivalence R)
  statement: Equivalence (LiftRel R) where
  proof: @LiftRel.refl α R H.stdRefl
.symm _ _ symm := @LiftRel.symm α R H.stdSymm
.trans _ _ _ trans := @LiftRel.trans α R H.isTrans

中文:
定理 LiftRel.equiv
  条件: (R : α -> α -> 命题) (H : 等价 R)
  结论: 等价 (LiftRel R) where
  证明: @LiftRel.refl α R H.stdRefl
.symm _ _ symm := @LiftRel.symm α R H.stdSymm
.trans _ _ _ trans := @LiftRel.trans α R H.isTrans

Depends on / 依赖: H.stdRefl, LiftRel, LiftRel.refl, stdRefl
-/
theorem LiftRel.equiv (R : α -> α -> Prop) (H : Equivalence R) : Equivalence (LiftRel R) where
.refl refl := @LiftRel.refl α R H.stdRefl
.symm _ _ symm := @LiftRel.symm α R H.stdSymm
.trans _ _ _ trans := @LiftRel.trans α R H.isTrans

/--
theorem `LiftRel.imp` / 定理 `LiftRel.imp`

English:
theorem LiftRel.imp
  given: {R S : α -> β -> Prop} (H : forall {a b}, R a b -> S a b) (s t)
  proof: l as
      ⟨b, bt, H ab⟩,
      fun {_} bt =>
      let ⟨a, as, ab⟩ := r bt
      ⟨a, as, H ab⟩⟩

中文:
定理 LiftRel.imp
  条件: {R S : α -> β -> 命题} (H : 对任意 {a b}, R a b -> S a b) (s t)
  证明: l as
      ⟨b, bt, H ab⟩,
      fun {_} bt =>
      let ⟨a, as, ab⟩ := r bt
      ⟨a, as, H ab⟩⟩
-/
theorem LiftRel.imp {R S : α -> β -> Prop} (H : forall {a b}, R a b -> S a b) (s t) :
    LiftRel R s t -> LiftRel S s t
  | ⟨l, r⟩ =>
    ⟨fun {_} as =>
      let ⟨b, bt, ab⟩ := l as
      ⟨b, bt, H ab⟩,
      fun {_} bt =>
      let ⟨a, as, ab⟩ := r bt
      ⟨a, as, H ab⟩⟩

/--
theorem `terminates_of_liftRel` / 定理 `terminates_of_liftRel`

English:
theorem terminates_of_liftRel
  given: {R : α -> β -> Prop} {s t}
  proof: l as
      ⟨⟨b, bt⟩⟩,
      fun ⟨⟨_, bt⟩⟩ =>
      let ⟨a, as, _⟩ := r bt
      ⟨⟨a, as⟩⟩⟩

中文:
定理 terminates_of_liftRel
  条件: {R : α -> β -> 命题} {s t}
  证明: l as
      ⟨⟨b, bt⟩⟩,
      fun ⟨⟨_, bt⟩⟩ =>
      let ⟨a, as, _⟩ := r bt
      ⟨⟨a, as⟩⟩⟩
-/
theorem terminates_of_liftRel {R : α -> β -> Prop} {s t} :
    LiftRel R s t -> (Terminates s ↔ Terminates t)
  | ⟨l, r⟩ =>
    ⟨fun ⟨⟨_, as⟩⟩ =>
      let ⟨b, bt, _⟩ := l as
      ⟨⟨b, bt⟩⟩,
      fun ⟨⟨_, bt⟩⟩ =>
      let ⟨a, as, _⟩ := r bt
      ⟨⟨a, as⟩⟩⟩

/--
theorem `rel_of_liftRel` / 定理 `rel_of_liftRel`

English:
theorem rel_of_liftRel
  given: {R : α -> β -> Prop} {ca cb}
  proof: l ma
    rw [mem_unique mb mb']; exact ab'

中文:
定理 rel_of_liftRel
  条件: {R : α -> β -> 命题} {ca cb}
  证明: l ma
    rw [mem_unique mb mb']; exact ab'
-/
theorem rel_of_liftRel {R : α -> β -> Prop} {ca cb} :
    LiftRel R ca cb -> forall {a b}, a in ca -> b in cb -> R a b
  | ⟨l, _⟩, a, b, ma, mb => by
    let ⟨b', mb', ab'⟩ := l ma
    rw [mem_unique mb mb']; exact ab'

/--
theorem `liftRel_of_mem` / 定理 `liftRel_of_mem`

English:
theorem liftRel_of_mem
  given: {R : α -> β -> Prop} {a b ca cb} (ma : a in ca) (mb : b in cb) (ab : R a b)
  proof: ⟨fun {a'} ma' => by rw [mem_unique ma' ma]; exact ⟨b, mb, ab⟩, fun {b'} mb' => by
    rw [mem_unique mb' mb]; exact ⟨a, ma, ab⟩⟩

中文:
定理 liftRel_of_mem
  条件: {R : α -> β -> 命题} {a b ca cb} (ma : a in ca) (mb : b in cb) (ab : R a b)
  证明: ⟨fun {a'} ma' => by rw [mem_unique ma' ma]; exact ⟨b, mb, ab⟩, fun {b'} mb' => by
    rw [mem_unique mb' mb]; exact ⟨a, ma, ab⟩⟩

Depends on / 依赖: mem_unique
-/
theorem liftRel_of_mem {R : α -> β -> Prop} {a b ca cb} (ma : a in ca) (mb : b in cb) (ab : R a b) :
    LiftRel R ca cb :=
  ⟨fun {a'} ma' => by rw [mem_unique ma' ma]; exact ⟨b, mb, ab⟩, fun {b'} mb' => by
    rw [mem_unique mb' mb]; exact ⟨a, ma, ab⟩⟩

/--
theorem `exists_of_liftRel_left` / 定理 `exists_of_liftRel_left`

English:
theorem exists_of_liftRel_left
  given: {R : α -> β -> Prop} {ca cb} (H : LiftRel R ca cb) {a} (h : a in ca)
  proof: H.left h

中文:
定理 存在_of_liftRel_left
  条件: {R : α -> β -> 命题} {ca cb} (H : LiftRel R ca cb) {a} (h : a in ca)
  证明: H.left h

Depends on / 依赖: H.left
-/
theorem exists_of_liftRel_left {R : α -> β -> Prop} {ca cb} (H : LiftRel R ca cb) {a} (h : a in ca) :
    exists b, b in cb ∧ R a b :=
  H.left h

/--
theorem `exists_of_liftRel_right` / 定理 `exists_of_liftRel_right`

English:
theorem exists_of_liftRel_right
  given: {R : α -> β -> Prop} {ca cb} (H : LiftRel R ca cb) {b} (h : b in cb)
  proof: H.right h

中文:
定理 存在_of_liftRel_right
  条件: {R : α -> β -> 命题} {ca cb} (H : LiftRel R ca cb) {b} (h : b in cb)
  证明: H.right h

Depends on / 依赖: H.right
-/
theorem exists_of_liftRel_right {R : α -> β -> Prop} {ca cb} (H : LiftRel R ca cb) {b} (h : b in cb) :
    exists a, a in ca ∧ R a b :=
  H.right h

/--
theorem `liftRel_def` / 定理 `liftRel_def`

English:
theorem liftRel_def
  given: {R : α -> β -> Prop} {ca cb}
  proof: ⟨fun h =>
    ⟨terminates_of_liftRel h, fun {a b} ma mb => by
      let ⟨b', mb', ab⟩ := h.left ma
      rwa [mem_unique mb mb']⟩,
    fun ⟨l, r⟩ =>
    ⟨fun {_} ma =>
      let ⟨⟨b, mb⟩⟩ := l.1 ⟨⟨_, ma⟩⟩
      ⟨b, mb, r ma mb⟩,
      fun {_} mb =>
      let ⟨⟨a, ma⟩⟩ := l.2 ⟨⟨_, mb⟩⟩
      ⟨a, ma, 

中文:
定理 liftRel_def
  条件: {R : α -> β -> 命题} {ca cb}
  证明: ⟨fun h =>
    ⟨terminates_of_liftRel h, fun {a b} ma mb => by
      let ⟨b', mb', ab⟩ := h.left ma
      rwa [mem_unique mb mb']⟩,
    fun ⟨l, r⟩ =>
    ⟨fun {_} ma =>
      let ⟨⟨b, mb⟩⟩ := l.1 ⟨⟨_, ma⟩⟩
      ⟨b, mb, r ma mb⟩,
      fun {_} mb =>
      let ⟨⟨a, ma⟩⟩ := l.2 ⟨⟨_, mb⟩⟩
      ⟨a, ma, 

Depends on / 依赖: h.left, mem_unique, terminates_of_liftRel
-/
theorem liftRel_def {R : α -> β -> Prop} {ca cb} :
    LiftRel R ca cb ↔ (Terminates ca ↔ Terminates cb) ∧ forall {a b}, a in ca -> b in cb -> R a b :=
  ⟨fun h =>
    ⟨terminates_of_liftRel h, fun {a b} ma mb => by
      let ⟨b', mb', ab⟩ := h.left ma
      rwa [mem_unique mb mb']⟩,
    fun ⟨l, r⟩ =>
    ⟨fun {_} ma =>
      let ⟨⟨b, mb⟩⟩ := l.1 ⟨⟨_, ma⟩⟩
      ⟨b, mb, r ma mb⟩,
      fun {_} mb =>
      let ⟨⟨a, ma⟩⟩ := l.2 ⟨⟨_, mb⟩⟩
      ⟨a, ma, r ma mb⟩⟩⟩

/--
theorem `liftRel_bind` / 定理 `liftRel_bind`

English:
theorem liftRel_bind
  statement: {δ} (R : α -> β -> Prop) (S : γ -> δ -> Prop) {s1 : Computation α}
  proof: let ⟨l1, r1⟩ := h1
  ⟨fun {_} cB =>
    let ⟨_, a1, c₁⟩ := exists_of_mem_bind cB
    let ⟨_, b2, ab⟩ := l1 a1
    let ⟨l2, _⟩ := h2 ab
    let ⟨_, d2, cd⟩ := l2 c₁
    ⟨_, mem_bind b2 d2, cd⟩,
    fun {_} dB =>
    let ⟨_, b1, d1⟩ := exists_of_mem_bind dB
    let ⟨_, a2, ab⟩ := r1 b1
    let ⟨_, r2⟩

中文:
定理 liftRel_bind
  结论: {δ} (R : α -> β -> 命题) (S : γ -> δ -> 命题) {s1 : Computation α}
  证明: let ⟨l1, r1⟩ := h1
  ⟨fun {_} cB =>
    let ⟨_, a1, c₁⟩ := exists_of_mem_bind cB
    let ⟨_, b2, ab⟩ := l1 a1
    let ⟨l2, _⟩ := h2 ab
    let ⟨_, d2, cd⟩ := l2 c₁
    ⟨_, mem_bind b2 d2, cd⟩,
    fun {_} dB =>
    let ⟨_, b1, d1⟩ := exists_of_mem_bind dB
    let ⟨_, a2, ab⟩ := r1 b1
    let ⟨_, r2⟩

Depends on / 依赖: exists_of_mem_bind, mem_bind
-/
theorem liftRel_bind {δ} (R : α -> β -> Prop) (S : γ -> δ -> Prop) {s1 : Computation α}
    {s2 : Computation β} {f1 : α -> Computation γ} {f2 : β -> Computation δ} (h1 : LiftRel R s1 s2)
    (h2 : forall {a b}, R a b -> LiftRel S (f1 a) (f2 b)) : LiftRel S (bind s1 f1) (bind s2 f2) :=
  let ⟨l1, r1⟩ := h1
  ⟨fun {_} cB =>
    let ⟨_, a1, c₁⟩ := exists_of_mem_bind cB
    let ⟨_, b2, ab⟩ := l1 a1
    let ⟨l2, _⟩ := h2 ab
    let ⟨_, d2, cd⟩ := l2 c₁
    ⟨_, mem_bind b2 d2, cd⟩,
    fun {_} dB =>
    let ⟨_, b1, d1⟩ := exists_of_mem_bind dB
    let ⟨_, a2, ab⟩ := r1 b1
    let ⟨_, r2⟩ := h2 ab
    let ⟨_, c₂, cd⟩ := r2 d1
    ⟨_, mem_bind a2 c₂, cd⟩⟩

@[simp]
/--
theorem `liftRel_pure_left` / 定理 `liftRel_pure_left`

English:
theorem liftRel_pure_left
  given: (R : α -> β -> Prop) (a : α) (cb : Computation β)
  proof: ⟨fun ⟨l, _⟩ => l (ret_mem _), fun ⟨b, mb, ab⟩ =>
    ⟨fun {a'} ma' => by rw [eq_of_pure_mem ma']; exact ⟨b, mb, ab⟩, fun {b'} mb' =>
      ⟨_, ret_mem _, by rw [mem_unique mb' mb]; exact ab⟩⟩⟩

@[simp]

中文:
定理 liftRel_pure_left
  条件: (R : α -> β -> 命题) (a : α) (cb : Computation β)
  证明: ⟨fun ⟨l, _⟩ => l (ret_mem _), fun ⟨b, mb, ab⟩ =>
    ⟨fun {a'} ma' => by rw [eq_of_pure_mem ma']; exact ⟨b, mb, ab⟩, fun {b'} mb' =>
      ⟨_, ret_mem _, by rw [mem_unique mb' mb]; exact ab⟩⟩⟩

@[simp]

Depends on / 依赖: eq_of_pure_mem, mem_unique, ret_mem
-/
theorem liftRel_pure_left (R : α -> β -> Prop) (a : α) (cb : Computation β) :
    LiftRel R (pure a) cb ↔ exists b, b in cb ∧ R a b :=
  ⟨fun ⟨l, _⟩ => l (ret_mem _), fun ⟨b, mb, ab⟩ =>
    ⟨fun {a'} ma' => by rw [eq_of_pure_mem ma']; exact ⟨b, mb, ab⟩, fun {b'} mb' =>
      ⟨_, ret_mem _, by rw [mem_unique mb' mb]; exact ab⟩⟩⟩

@[simp]
/--
theorem `liftRel_pure_right` / 定理 `liftRel_pure_right`

English:
theorem liftRel_pure_right
  given: (R : α -> β -> Prop) (ca : Computation α) (b : β)
  proof: by rw [LiftRel.swap, liftRel_pure_left]

中文:
定理 liftRel_pure_right
  条件: (R : α -> β -> 命题) (ca : Computation α) (b : β)
  证明: by rw [LiftRel.swap, liftRel_pure_left]

Depends on / 依赖: LiftRel, LiftRel.swap, liftRel_pure_left
-/
theorem liftRel_pure_right (R : α -> β -> Prop) (ca : Computation α) (b : β) :
    LiftRel R ca (pure b) ↔ exists a, a in ca ∧ R a b := by rw [LiftRel.swap, liftRel_pure_left]

/--
theorem `liftRel_pure` / 定理 `liftRel_pure`

English:
theorem liftRel_pure
  given: (R : α -> β -> Prop) (a : α) (b : β)
  proof: by
  simp

@[simp]

中文:
定理 liftRel_pure
  条件: (R : α -> β -> 命题) (a : α) (b : β)
  证明: by
  simp

@[simp]
-/
theorem liftRel_pure (R : α -> β -> Prop) (a : α) (b : β) :
    LiftRel R (pure a) (pure b) ↔ R a b := by
  simp

@[simp]
/--
theorem `liftRel_think_left` / 定理 `liftRel_think_left`

English:
theorem liftRel_think_left
  given: (R : α -> β -> Prop) (ca : Computation α) (cb : Computation β)
  proof: and_congr (forall_congr' fun _ => imp_congr ⟨of_think_mem, think_mem⟩ Iff.rfl)
    (forall_congr' fun _ =>
imp_congr Iff.rfl exists_congr fun _ => and_congr ⟨of_think_mem, think_mem⟩ Iff.rfl)

@[simp]

中文:
定理 liftRel_think_left
  条件: (R : α -> β -> 命题) (ca : Computation α) (cb : Computation β)
  证明: and_congr (forall_congr' fun _ => imp_congr ⟨of_think_mem, think_mem⟩ Iff.rfl)
    (forall_congr' fun _ =>
imp_congr Iff.rfl exists_congr fun _ => and_congr ⟨of_think_mem, think_mem⟩ Iff.rfl)

@[simp]

Depends on / 依赖: Iff.rfl, and_congr, exists_congr, forall_congr, imp_congr, of_think_mem, think_mem
-/
theorem liftRel_think_left (R : α -> β -> Prop) (ca : Computation α) (cb : Computation β) :
    LiftRel R (think ca) cb ↔ LiftRel R ca cb :=
  and_congr (forall_congr' fun _ => imp_congr ⟨of_think_mem, think_mem⟩ Iff.rfl)
    (forall_congr' fun _ =>
imp_congr Iff.rfl exists_congr fun _ => and_congr ⟨of_think_mem, think_mem⟩ Iff.rfl)

@[simp]
/--
theorem `liftRel_think_right` / 定理 `liftRel_think_right`

English:
theorem liftRel_think_right
  given: (R : α -> β -> Prop) (ca : Computation α) (cb : Computation β)
  proof: by
  rw [← LiftRel.swap R]; rw [← LiftRel.swap R]; apply liftRel_think_left

中文:
定理 liftRel_think_right
  条件: (R : α -> β -> 命题) (ca : Computation α) (cb : Computation β)
  证明: by
  rw [← LiftRel.swap R]; rw [← LiftRel.swap R]; apply liftRel_think_left

Depends on / 依赖: LiftRel, LiftRel.swap, liftRel_think_left
-/
theorem liftRel_think_right (R : α -> β -> Prop) (ca : Computation α) (cb : Computation β) :
    LiftRel R ca (think cb) ↔ LiftRel R ca cb := by
  rw [← LiftRel.swap R]; rw [← LiftRel.swap R]; apply liftRel_think_left

/--
theorem `liftRel_mem_cases` / 定理 `liftRel_mem_cases`

English:
theorem liftRel_mem_cases
  statement: {R : α -> β -> Prop} {ca cb} (Ha : forall a in ca, LiftRel R ca cb)
  proof: ⟨fun {_} ma => (Ha _ ma).left ma, fun {_} mb => (Hb _ mb).right mb⟩

中文:
定理 liftRel_mem_cases
  结论: {R : α -> β -> 命题} {ca cb} (Ha : 对任意 a in ca, LiftRel R ca cb)
  证明: ⟨fun {_} ma => (Ha _ ma).left ma, fun {_} mb => (Hb _ mb).right mb⟩
-/
theorem liftRel_mem_cases {R : α -> β -> Prop} {ca cb} (Ha : forall a in ca, LiftRel R ca cb)
    (Hb : forall b in cb, LiftRel R ca cb) : LiftRel R ca cb :=
  ⟨fun {_} ma => (Ha _ ma).left ma, fun {_} mb => (Hb _ mb).right mb⟩

/--
theorem `liftRel_congr` / 定理 `liftRel_congr`

English:
theorem liftRel_congr
  statement: {R : α -> β -> Prop} {ca ca' : Computation α} {cb cb' : Computation β}
  proof: and_congr
    (forall_congr' fun _ => imp_congr (ha _) <| exists_congr fun _ => and_congr (hb _) Iff.rfl)
    (forall_congr' fun _ => imp_congr (hb _) <| exists_congr fun _ => and_congr (ha _) Iff.rfl)

中文:
定理 liftRel_congr
  结论: {R : α -> β -> 命题} {ca ca' : Computation α} {cb cb' : Computation β}
  证明: and_congr
    (forall_congr' fun _ => imp_congr (ha _) <| exists_congr fun _ => and_congr (hb _) Iff.rfl)
    (forall_congr' fun _ => imp_congr (hb _) <| exists_congr fun _ => and_congr (ha _) Iff.rfl)

Depends on / 依赖: Iff.rfl, and_congr, exists_congr, forall_congr, imp_congr
-/
theorem liftRel_congr {R : α -> β -> Prop} {ca ca' : Computation α} {cb cb' : Computation β}
    (ha : ca ~ ca') (hb : cb ~ cb') : LiftRel R ca cb ↔ LiftRel R ca' cb' :=
  and_congr
    (forall_congr' fun _ => imp_congr (ha _) <| exists_congr fun _ => and_congr (hb _) Iff.rfl)
    (forall_congr' fun _ => imp_congr (hb _) <| exists_congr fun _ => and_congr (ha _) Iff.rfl)

/--
theorem `liftRel_map` / 定理 `liftRel_map`

English:
theorem liftRel_map
  statement: {δ} (R : α -> β -> Prop) (S : γ -> δ -> Prop) {s1 : Computation α}
  proof: by
  rw [← bind_pure]; rw [← bind_pure]; apply liftRel_bind _ _ h1; simpa

中文:
定理 liftRel_map
  结论: {δ} (R : α -> β -> 命题) (S : γ -> δ -> 命题) {s1 : Computation α}
  证明: by
  rw [← bind_pure]; rw [← bind_pure]; apply liftRel_bind _ _ h1; simpa

Depends on / 依赖: bind_pure, liftRel_bind
-/
theorem liftRel_map {δ} (R : α -> β -> Prop) (S : γ -> δ -> Prop) {s1 : Computation α}
    {s2 : Computation β} {f1 : α -> γ} {f2 : β -> δ} (h1 : LiftRel R s1 s2)
    (h2 : forall {a b}, R a b -> S (f1 a) (f2 b)) : LiftRel S (map f1 s1) (map f2 s2) := by
  rw [← bind_pure]; rw [← bind_pure]; apply liftRel_bind _ _ h1; simpa

/--
theorem `map_congr` / 定理 `map_congr`

English:
theorem map_congr
  statement: {s1 s2 : Computation α} {f : α -> β}
  proof: by
  rw [← lift_eq_iff_equiv]
  exact liftRel_map Eq _ ((lift_eq_iff_equiv _ _).2 h1) fun {a} b => congr_arg _

中文:
定理 map_congr
  结论: {s1 s2 : Computation α} {f : α -> β}
  证明: by
  rw [← lift_eq_iff_equiv]
  exact liftRel_map Eq _ ((lift_eq_iff_equiv _ _).2 h1) fun {a} b => congr_arg _

Depends on / 依赖: congr_arg, liftRel_map, lift_eq_iff_equiv
-/
theorem map_congr {s1 s2 : Computation α} {f : α -> β}
    (h1 : s1 ~ s2) : map f s1 ~ map f s2 := by
  rw [← lift_eq_iff_equiv]
  exact liftRel_map Eq _ ((lift_eq_iff_equiv _ _).2 h1) fun {a} b => congr_arg _

/--
Definition of `LiftRelAux` / `LiftRelAux` 的定义

English:
definition LiftRelAux
  signature: (R : α -> β -> Prop) (C : Computation α -> Computation β -> Prop)

中文:
定义 LiftRelAux
  签名: (R : α -> β -> 命题) (C : Computation α -> Computation β -> 命题)
-/
def LiftRelAux (R : α -> β -> Prop) (C : Computation α -> Computation β -> Prop) :
    α oplus (Computation α) -> β oplus (Computation β) -> Prop
  | Sum.inl a, Sum.inl b => R a b
  | Sum.inl a, Sum.inr cb => exists b, b in cb ∧ R a b
  | Sum.inr ca, Sum.inl b => exists a, a in ca ∧ R a b
  | Sum.inr ca, Sum.inr cb => C ca cb

variable {R : α -> β -> Prop} {C : Computation α -> Computation β -> Prop}

/--
lemma `liftRelAux_inl_inl` / 引理 `liftRelAux_inl_inl`

English:
lemma liftRelAux_inl_inl
  given: {a : α} {b : β}
  statement: LiftRelAux R C (Sum.inl a) (Sum.inl b) = R a b
  proof: rfl

中文:
引理 liftRelAux_inl_inl
  条件: {a : α} {b : β}
  结论: LiftRelAux R C (和.inl a) (和.inl b) = R a b
  证明: rfl
-/
@[simp] lemma liftRelAux_inl_inl {a : α} {b : β} : LiftRelAux R C (Sum.inl a) (Sum.inl b) = R a b :=
  rfl
/--
lemma `liftRelAux_inl_inr` / 引理 `liftRelAux_inl_inr`

English:
lemma liftRelAux_inl_inr
  given: {a : α} {cb}
  proof: rfl

中文:
引理 liftRelAux_inl_inr
  条件: {a : α} {cb}
  证明: rfl
-/
@[simp] lemma liftRelAux_inl_inr {a : α} {cb} :
    LiftRelAux R C (Sum.inl a) (Sum.inr cb) = exists b, b in cb ∧ R a b :=
  rfl
/--
lemma `liftRelAux_inr_inl` / 引理 `liftRelAux_inr_inl`

English:
lemma liftRelAux_inr_inl
  given: {b : β} {ca}
  proof: rfl

中文:
引理 liftRelAux_inr_inl
  条件: {b : β} {ca}
  证明: rfl
-/
@[simp] lemma liftRelAux_inr_inl {b : β} {ca} :
    LiftRelAux R C (Sum.inr ca) (Sum.inl b) = exists a, a in ca ∧ R a b :=
  rfl
/--
lemma `liftRelAux_inr_inr` / 引理 `liftRelAux_inr_inr`

English:
lemma liftRelAux_inr_inr
  given: {ca cb}
  proof: rfl

@[simp]

中文:
引理 liftRelAux_inr_inr
  条件: {ca cb}
  证明: rfl

@[simp]
-/
@[simp] lemma liftRelAux_inr_inr {ca cb} :
    LiftRelAux R C (Sum.inr ca) (Sum.inr cb) = C ca cb :=
  rfl

@[simp]
/--
theorem `LiftRelAux.ret_left` / 定理 `LiftRelAux.ret_left`

English:
theorem LiftRelAux.ret_left
  given: (R : α -> β -> Prop) (C : Computation α -> Computation β -> Prop) (a cb)
  proof: by
  induction cb using recOn with
  | pure b =>
    exact
      ⟨fun h => ⟨_, ret_mem _, h⟩, fun ⟨b', mb, h⟩ => by rw [mem_unique (ret_mem _) mb]; exact h⟩
  | think cb =>
    rw [destruct_think]
    exact ⟨fun ⟨b, h, r⟩ => ⟨b, think_mem h, r⟩, fun ⟨b, h, r⟩ => ⟨b, of_think_mem h, r⟩⟩

中文:
定理 LiftRelAux.ret_left
  条件: (R : α -> β -> 命题) (C : Computation α -> Computation β -> 命题) (a cb)
  证明: by
  induction cb using recOn with
  | pure b =>
    exact
      ⟨fun h => ⟨_, ret_mem _, h⟩, fun ⟨b', mb, h⟩ => by rw [mem_unique (ret_mem _) mb]; exact h⟩
  | think cb =>
    rw [destruct_think]
    exact ⟨fun ⟨b, h, r⟩ => ⟨b, think_mem h, r⟩, fun ⟨b, h, r⟩ => ⟨b, of_think_mem h, r⟩⟩

Depends on / 依赖: destruct_think, mem_unique, of_think_mem, ret_mem, think_mem
-/
theorem LiftRelAux.ret_left (R : α -> β -> Prop) (C : Computation α -> Computation β -> Prop) (a cb) :
    LiftRelAux R C (Sum.inl a) (destruct cb) ↔ exists b, b in cb ∧ R a b := by
  induction cb using recOn with
  | pure b =>
    exact
      ⟨fun h => ⟨_, ret_mem _, h⟩, fun ⟨b', mb, h⟩ => by rw [mem_unique (ret_mem _) mb]; exact h⟩
  | think cb =>
    rw [destruct_think]
    exact ⟨fun ⟨b, h, r⟩ => ⟨b, think_mem h, r⟩, fun ⟨b, h, r⟩ => ⟨b, of_think_mem h, r⟩⟩

/--
theorem `LiftRelAux.swap` / 定理 `LiftRelAux.swap`

English:
theorem LiftRelAux.swap
  given: (R : α -> β -> Prop) (C) (a b)
  proof: by
  rcases a with a | ca <;> rcases b with b | cb <;> simp only [LiftRelAux]

@[simp]

中文:
定理 LiftRelAux.swap
  条件: (R : α -> β -> 命题) (C) (a b)
  证明: by
  rcases a with a | ca <;> rcases b with b | cb <;> simp only [LiftRelAux]

@[simp]

Depends on / 依赖: LiftRelAux
-/
theorem LiftRelAux.swap (R : α -> β -> Prop) (C) (a b) :
    LiftRelAux (swap R) (swap C) b a = LiftRelAux R C a b := by
  rcases a with a | ca <;> rcases b with b | cb <;> simp only [LiftRelAux]

@[simp]
/--
theorem `LiftRelAux.ret_right` / 定理 `LiftRelAux.ret_right`

English:
theorem LiftRelAux.ret_right
  given: (R : α -> β -> Prop) (C : Computation α -> Computation β -> Prop) (b ca)
  proof: by
  rw [← LiftRelAux.swap]; rw [LiftRelAux.ret_left]

中文:
定理 LiftRelAux.ret_right
  条件: (R : α -> β -> 命题) (C : Computation α -> Computation β -> 命题) (b ca)
  证明: by
  rw [← LiftRelAux.swap]; rw [LiftRelAux.ret_left]

Depends on / 依赖: LiftRelAux, LiftRelAux.ret_left, LiftRelAux.swap, ret_left
-/
theorem LiftRelAux.ret_right (R : α -> β -> Prop) (C : Computation α -> Computation β -> Prop) (b ca) :
    LiftRelAux R C (destruct ca) (Sum.inl b) ↔ exists a, a in ca ∧ R a b := by
  rw [← LiftRelAux.swap]; rw [LiftRelAux.ret_left]

/--
theorem `LiftRelRec.lem` / 定理 `LiftRelRec.lem`

English:
theorem LiftRelRec.lem
  statement: {R : α -> β -> Prop} (C : Computation α -> Computation β -> Prop)
  proof: by
  revert cb
  refine memRecOn (C := (fun ca => forall (cb : Computation β), C ca cb -> LiftRel R ca cb))
    ha ?_ (fun ca' IH => ?_) <;> intro cb Hc <;> have h := H Hc
  · simp only [destruct_pure, LiftRelAux.ret_left] at h
    simp [h]
  · simp only [liftRel_think_left]
    induction cb using r

中文:
定理 LiftRelRec.lem
  结论: {R : α -> β -> 命题} (C : Computation α -> Computation β -> 命题)
  证明: by
  revert cb
  refine memRecOn (C := (fun ca => forall (cb : Computation β), C ca cb -> LiftRel R ca cb))
    ha ?_ (fun ca' IH => ?_) <;> intro cb Hc <;> have h := H Hc
  · simp only [destruct_pure, LiftRelAux.ret_left] at h
    simp [h]
  · simp only [liftRel_think_left]
    induction cb using r

Depends on / 依赖: Computation, LiftRel, LiftRelAux, LiftRelAux.ret_left, destruct_pure, liftRel_think_left, memRecOn, ret_left, revert
-/
theorem LiftRelRec.lem {R : α -> β -> Prop} (C : Computation α -> Computation β -> Prop)
    (H : forall {ca cb}, C ca cb -> LiftRelAux R C (destruct ca) (destruct cb)) (ca cb) (Hc : C ca cb) (a)
    (ha : a in ca) : LiftRel R ca cb := by
  revert cb
  refine memRecOn (C := (fun ca => forall (cb : Computation β), C ca cb -> LiftRel R ca cb))
    ha ?_ (fun ca' IH => ?_) <;> intro cb Hc <;> have h := H Hc
  · simp only [destruct_pure, LiftRelAux.ret_left] at h
    simp [h]
  · simp only [liftRel_think_left]
    induction cb using recOn with
    | pure b => simpa using h
    | think cb => simpa [h] using IH _ h

/--
theorem `liftRel_rec` / 定理 `liftRel_rec`

English:
theorem liftRel_rec
  statement: {R : α -> β -> Prop} (C : Computation α -> Computation β -> Prop)
  proof: liftRel_mem_cases (LiftRelRec.lem C (@H) ca cb Hc) fun b hb =>
(LiftRel.swap _ _ _).2
      LiftRelRec.lem (swap C) (fun {_ _} h => cast (LiftRelAux.swap _ _ _ _).symm <| H h) cb ca Hc b
        hb

中文:
定理 liftRel_rec
  结论: {R : α -> β -> 命题} (C : Computation α -> Computation β -> 命题)
  证明: liftRel_mem_cases (LiftRelRec.lem C (@H) ca cb Hc) fun b hb =>
(LiftRel.swap _ _ _).2
      LiftRelRec.lem (swap C) (fun {_ _} h => cast (LiftRelAux.swap _ _ _ _).symm <| H h) cb ca Hc b
        hb

Depends on / 依赖: LiftRel, LiftRel.swap, LiftRelAux, LiftRelAux.swap, LiftRelRec, LiftRelRec.lem, liftRel_mem_cases
-/
theorem liftRel_rec {R : α -> β -> Prop} (C : Computation α -> Computation β -> Prop)
    (H : forall {ca cb}, C ca cb -> LiftRelAux R C (destruct ca) (destruct cb)) (ca cb) (Hc : C ca cb) :
    LiftRel R ca cb :=
  liftRel_mem_cases (LiftRelRec.lem C (@H) ca cb Hc) fun b hb =>
(LiftRel.swap _ _ _).2
      LiftRelRec.lem (swap C) (fun {_ _} h => cast (LiftRelAux.swap _ _ _ _).symm <| H h) cb ca Hc b
        hb

end Computation
