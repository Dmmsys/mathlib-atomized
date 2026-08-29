/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Computability.TuringMachine.Tape
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.PFun
public import Mathlib.Computability.TuringMachine.PostTuringMachine

/-!
# Turing machines

The files `PostTuringMachine.lean` and `StackTuringMachine.lean` define
a sequence of simple machine languages, starting with Turing machines and working
up to more complex languages based on Wang B-machines.

`PostTuringMachine.lean` covers the TM0 model and TM1 model;
`StackTuringMachine.lean` adds the TM2 model.

## Naming conventions

Each model of computation in this file shares a naming convention for the elements of a model of
computation. These are the parameters for the language:

* `Γ` is the alphabet on the tape.
* `Λ` is the set of labels, or internal machine states.
* `σ` is the type of internal memory, not on the tape. This does not exist in the TM0 model, and
  later models achieve this by mixing it into `Λ`.
* `K` is used in the TM2 model, which has multiple stacks, and denotes the number of such stacks.

All of these variables denote "essentially finite" types, but for technical reasons it is
convenient to allow them to be infinite anyway. When using an infinite type, we will be interested
in proving that only finitely many values of the type are ever interacted with.

Given these parameters, there are a few common structures for the model that arise:

* `Stmt` is the set of all actions that can be performed in one step. For the TM0 model this set is
  finite, and for later models it is an infinite inductive type representing "possible program
  texts".
* `Cfg` is the set of instantaneous configurations, that is, the state of the machine together with
  its environment.
* `Machine` is the set of all machines in the model. Usually this is approximately a function
  `Λ → Stmt`, although different models have different ways of halting and other actions.
* `step : Cfg → Option Cfg` is the function that describes how the state evolves over one step.
  If `step c = none`, then `c` is a terminal state, and the result of the computation is read off
  from `c`. Because of the type of `step`, these models are all deterministic by construction.
* `init : Input → Cfg` sets up the initial state. The type `Input` depends on the model;
  in most cases it is `List Γ`.
* `eval : Machine → Input → Part Output`, given a machine `M` and input `i`, starts from
  `init i`, runs `step` until it reaches an output, and then applies a function `Cfg → Output` to
  the final state to obtain the result. The type `Output` depends on the model.
* `Supports : Machine → Finset Λ → Prop` asserts that a machine `M` starts in `S : Finset Λ`, and
  can only ever jump to other states inside `S`. This implies that the behavior of `M` on any input
  cannot depend on its values outside `S`. We use this to allow `Λ` to be an infinite set when
  convenient, and prove that only finitely many of these states are actually accessible. This
  formalizes "essentially finite" mentioned above.
-/

@[expose] public section

assert_not_exists MonoidWithZero

open List (Vector)
open Relation

open Nat (iterate)

open Function (update iterate_succ iterate_succ_apply iterate_succ' iterate_succ_apply'
  iterate_zero_apply)

namespace Turing


/-!
## The TM2 model

The TM2 model removes the tape entirely from the TM1 model, replacing it with an arbitrary (finite)
collection of stacks, each with elements of different types (the alphabet of stack `k : K` is
`Γ k`). The statements are:

* `push k (f : σ → Γ k) q` puts `f a` on the `k`-th stack, then does `q`.
* `pop k (f : σ → Option (Γ k) → σ) q` changes the state to `f a (S k).head`, where `S k` is the
  value of the `k`-th stack, and removes this element from the stack, then does `q`.
* `peek k (f : σ → Option (Γ k) → σ) q` changes the state to `f a (S k).head`, where `S k` is the
  value of the `k`-th stack, then does `q`.
* `load (f : σ → σ) q` reads nothing but applies `f` to the internal state, then does `q`.
* `branch (f : σ → Bool) qtrue qfalse` does `qtrue` or `qfalse` according to `f a`.
* `goto (f : σ → Λ)` jumps to label `f a`.
* `halt` halts on the next step.

The configuration is a tuple `(l, var, stk)` where `l : Option Λ` is the current label to run or
`none` for the halting state, `var : σ` is the (finite) internal state, and `stk : ∀ k, List (Γ k)`
is the collection of stacks. (Note that unlike the `TM0` and `TM1` models, these are not
`ListBlank`s, they have definite ends that can be detected by the `pop` command.)

Given a designated stack `k` and a value `L : List (Γ k)`, the initial configuration has all the
stacks empty except the designated "input" stack; in `eval` this designated stack also functions
as the output stack.
-/


namespace TM2

variable {K : Type*}

-- Index type of stacks
variable (Γ : K -> Type*)

-- Type of stack elements
variable (Λ : Type*)

-- Type of function labels
variable (σ : Type*)

-- Type of variable settings
/--
Inductive type `Stmt` / 归纳类型 `Stmt`

English:
inductive Stmt
  constructors (7):
    - push: forall k, (σ -> Γ k) -> Stmt -> Stmt
    - peek: forall k, (σ -> Option (Γ k) -> σ) -> Stmt -> Stmt
    - pop: forall k, (σ -> Option (Γ k) -> σ) -> Stmt -> Stmt
    - load: (σ -> σ) -> Stmt -> Stmt
    - branch: (σ -> Bool) -> Stmt -> Stmt -> Stmt
    - goto: (σ -> Λ) -> Stmt
    - halt: Stmt

中文:
归纳类型 Stmt
  构造子 (7 个):
    - push: 对任意 k, (σ -> Γ k) -> Stmt -> Stmt
    - peek: 对任意 k, (σ -> 选项类型 (Γ k) -> σ) -> Stmt -> Stmt
    - pop: 对任意 k, (σ -> 选项类型 (Γ k) -> σ) -> Stmt -> Stmt
    - load: (σ -> σ) -> Stmt -> Stmt
    - branch: (σ -> 布尔值) -> Stmt -> Stmt -> Stmt
    - goto: (σ -> Λ) -> Stmt
    - halt: Stmt
-/
inductive Stmt
  | push : forall k, (σ -> Γ k) -> Stmt -> Stmt
  | peek : forall k, (σ -> Option (Γ k) -> σ) -> Stmt -> Stmt
  | pop : forall k, (σ -> Option (Γ k) -> σ) -> Stmt -> Stmt
  | load : (σ -> σ) -> Stmt -> Stmt
  | branch : (σ -> Bool) -> Stmt -> Stmt -> Stmt
  | goto : (σ -> Λ) -> Stmt
  | halt : Stmt

open Stmt

/--
Instance `Stmt.inhabited` / 实例 `Stmt.inhabited`

English:
instance Stmt.inhabited
  signature: : Inhabited (Stmt Γ Λ σ)
  body: ⟨halt⟩

中文:
实例 Stmt.inhabited
  签名: : 可居 (Stmt Γ Λ σ)
  定义体: ⟨halt⟩
-/
instance Stmt.inhabited : Inhabited (Stmt Γ Λ σ) :=
  ⟨halt⟩

/--
Definition of `Cfg` / `Cfg` 的定义

English:
structure Cfg
  parameters: where
  axioms and operations (3):
    - l : Option Λ
    - var : σ
    - stk : forall k, List (Γ k)

中文:
结构 Cfg
  参数: where
  公理与运算 (3 个):
    - l : 选项类型 Λ
    - var : σ
    - stk : 对任意 k, 列表 (Γ k)
-/
structure Cfg where
  /-- The current label to run (or `none` for the halting state) -/
  l : Option Λ
  /-- The internal state -/
  var : σ
  /-- The (finite) collection of internal stacks -/
  stk : forall k, List (Γ k)

/--
Instance `Cfg.inhabited` / 实例 `Cfg.inhabited`

English:
instance Cfg.inhabited
  signature: [Inhabited σ]
  body: ⟨⟨default, default, default⟩⟩

中文:
实例 Cfg.inhabited
  签名: [可居 σ]
  定义体: ⟨⟨default, default, default⟩⟩
-/
instance Cfg.inhabited [Inhabited σ] : Inhabited (Cfg Γ Λ σ) :=
  ⟨⟨default, default, default⟩⟩

variable {Γ Λ σ}

section
variable [DecidableEq K]

/--
Definition of `stepAux` / `stepAux` 的定义

English:
definition stepAux
  signature: : Stmt Γ Λ σ -> σ -> (forall k, List (Γ k)) -> Cfg Γ Λ σ

中文:
定义 stepAux
  签名: : Stmt Γ Λ σ -> σ -> (对任意 k, 列表 (Γ k)) -> Cfg Γ Λ σ
-/
def stepAux : Stmt Γ Λ σ -> σ -> (forall k, List (Γ k)) -> Cfg Γ Λ σ
  | push k f q, v, S => stepAux q v (update S k (f v :: S k))
  | peek k f q, v, S => stepAux q (f v (S k).head?) S
  | pop k f q, v, S => stepAux q (f v (S k).head?) (update S k (S k).tail)
  | load a q, v, S => stepAux q (a v) S
  | branch f q₁ q₂, v, S => cond (f v) (stepAux q₁ v S) (stepAux q₂ v S)
  | goto f, v, S => ⟨some (f v), v, S⟩
  | halt, v, S => ⟨none, v, S⟩

/--
Definition of `step` / `step` 的定义

English:
definition step
  signature: (M : Λ -> Stmt Γ Λ σ)

中文:
定义 step
  签名: (M : Λ -> Stmt Γ Λ σ)
-/
def step (M : Λ -> Stmt Γ Λ σ) : Cfg Γ Λ σ -> Option (Cfg Γ Λ σ)
  | ⟨none, _, _⟩ => none
  | ⟨some l, v, S⟩ => some (stepAux (M l) v S)

attribute [simp] stepAux.eq_1 stepAux.eq_2 stepAux.eq_3
  stepAux.eq_4 stepAux.eq_5 stepAux.eq_6 stepAux.eq_7 step.eq_1 step.eq_2

/--
Definition of `Reaches` / `Reaches` 的定义

English:
definition Reaches
  signature: (M : Λ -> Stmt Γ Λ σ)
  body: ReflTransGen fun a b => b in step M a

中文:
定义 Reaches
  签名: (M : Λ -> Stmt Γ Λ σ)
  定义体: ReflTransGen fun a b => b in step M a

Depends on / 依赖: ReflTransGen
-/
def Reaches (M : Λ -> Stmt Γ Λ σ) : Cfg Γ Λ σ -> Cfg Γ Λ σ -> Prop :=
  ReflTransGen fun a b => b in step M a

end

/--
Definition of `SupportsStmt` / `SupportsStmt` 的定义

English:
definition SupportsStmt
  signature: (S : Finset Λ)

中文:
定义 SupportsStmt
  签名: (S : 有限集 Λ)
-/
def SupportsStmt (S : Finset Λ) : Stmt Γ Λ σ -> Prop
  | push _ _ q => SupportsStmt S q
  | peek _ _ q => SupportsStmt S q
  | pop _ _ q => SupportsStmt S q
  | load _ q => SupportsStmt S q
  | branch _ q₁ q₂ => SupportsStmt S q₁ ∧ SupportsStmt S q₂
  | goto l => forall v, l v in S
  | halt => True

section

open scoped Classical in
/--
Definition of `stmts₁` / `stmts₁` 的定义

English:
definition stmts₁
  signature: : Stmt Γ Λ σ -> Finset (Stmt Γ Λ σ)

中文:
定义 stmts₁
  签名: : Stmt Γ Λ σ -> 有限集 (Stmt Γ Λ σ)
-/
noncomputable def stmts₁ : Stmt Γ Λ σ -> Finset (Stmt Γ Λ σ)
  | Q@(push _ _ q) => insert Q (stmts₁ q)
  | Q@(peek _ _ q) => insert Q (stmts₁ q)
  | Q@(pop _ _ q) => insert Q (stmts₁ q)
  | Q@(load _ q) => insert Q (stmts₁ q)
  | Q@(branch _ q₁ q₂) => insert Q (stmts₁ q₁ union stmts₁ q₂)
  | Q@(goto _) => {Q}
  | Q@halt => {Q}

/--
theorem `stmts₁_self` / 定理 `stmts₁_self`

English:
theorem stmts₁_self
  given: {q : Stmt Γ Λ σ}
  statement: q in stmts₁ q
  proof: by
  cases q <;> simp only [Finset.mem_insert_self, Finset.mem_singleton_self, stmts₁]

中文:
定理 stmts₁_self
  条件: {q : Stmt Γ Λ σ}
  结论: q in stmts₁ q
  证明: by
  cases q <;> simp only [Finset.mem_insert_self, Finset.mem_singleton_self, stmts₁]

Depends on / 依赖: Finset, Finset.mem_insert_self, Finset.mem_singleton_self, mem_insert_self, mem_singleton_self
-/
theorem stmts₁_self {q : Stmt Γ Λ σ} : q in stmts₁ q := by
  cases q <;> simp only [Finset.mem_insert_self, Finset.mem_singleton_self, stmts₁]

/--
theorem `stmts₁_trans` / 定理 `stmts₁_trans`

English:
theorem stmts₁_trans
  given: {q₁ q₂ : Stmt Γ Λ σ}
  statement: q₁ in stmts₁ q₂ -> stmts₁ q₁ subseteq stmts₁ q₂
  proof: by
  classical
  intro h₁₂ q₀ h₀₁
  induction q₂ with (
    simp only [stmts₁] at h₁₂ ⊢
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union] at h₁₂)
  | branch f q₁ q₂ IH₁ IH₂ =>
    rcases h₁₂ with (rfl | h₁₂ | h₁₂)
    · unfold stmts₁ at h₀₁
      exact h₀₁
    · exact Finset.

中文:
定理 stmts₁_trans
  条件: {q₁ q₂ : Stmt Γ Λ σ}
  结论: q₁ in stmts₁ q₂ -> stmts₁ q₁ subseteq stmts₁ q₂
  证明: by
  classical
  intro h₁₂ q₀ h₀₁
  induction q₂ with (
    simp only [stmts₁] at h₁₂ ⊢
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union] at h₁₂)
  | branch f q₁ q₂ IH₁ IH₂ =>
    rcases h₁₂ with (rfl | h₁₂ | h₁₂)
    · unfold stmts₁ at h₀₁
      exact h₀₁
    · exact Finset.

Depends on / 依赖: Finset, Finset.mem_insert, Finset.mem_insert_of_mem, Finset.mem_singleton, Finset.mem_union, Finset.mem_union_left, Finset.mem_union_right, branch, classical, mem_insert, mem_insert_of_mem, mem_singleton, mem_union, mem_union_left, mem_union_right
-/
theorem stmts₁_trans {q₁ q₂ : Stmt Γ Λ σ} : q₁ in stmts₁ q₂ -> stmts₁ q₁ subseteq stmts₁ q₂ := by
  classical
  intro h₁₂ q₀ h₀₁
  induction q₂ with (
    simp only [stmts₁] at h₁₂ ⊢
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_union] at h₁₂)
  | branch f q₁ q₂ IH₁ IH₂ =>
    rcases h₁₂ with (rfl | h₁₂ | h₁₂)
    · unfold stmts₁ at h₀₁
      exact h₀₁
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (IH₁ h₁₂))
    · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (IH₂ h₁₂))
  | goto l => subst h₁₂; exact h₀₁
  | halt => subst h₁₂; exact h₀₁
  | load _ q IH | _ _ _ q IH =>
    rcases h₁₂ with (rfl | h₁₂)
    · unfold stmts₁ at h₀₁
      exact h₀₁
    · exact Finset.mem_insert_of_mem (IH h₁₂)

/--
theorem `stmts₁_supportsStmt_mono` / 定理 `stmts₁_supportsStmt_mono`

English:
theorem stmts₁_supportsStmt_mono
  statement: {S : Finset Λ} {q₁ q₂ : Stmt Γ Λ σ} (h : q₁ in stmts₁ q₂)
  proof: by
  induction q₂ with
    simp only [stmts₁, SupportsStmt, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
      at h hs
  | branch f q₁ q₂ IH₁ IH₂ => rcases h with (rfl | h | h); exacts [hs, IH₁ h hs.1, IH₂ h hs.2]
  | goto l => subst h; exact hs
  | halt => subst h; trivial
  | load _ 

中文:
定理 stmts₁_supportsStmt_mono
  结论: {S : 有限集 Λ} {q₁ q₂ : Stmt Γ Λ σ} (h : q₁ in stmts₁ q₂)
  证明: by
  induction q₂ with
    simp only [stmts₁, SupportsStmt, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
      at h hs
  | branch f q₁ q₂ IH₁ IH₂ => rcases h with (rfl | h | h); exacts [hs, IH₁ h hs.1, IH₂ h hs.2]
  | goto l => subst h; exact hs
  | halt => subst h; trivial
  | load _ 

Depends on / 依赖: Finset, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, SupportsStmt, branch, exacts, mem_insert, mem_singleton, mem_union
-/
theorem stmts₁_supportsStmt_mono {S : Finset Λ} {q₁ q₂ : Stmt Γ Λ σ} (h : q₁ in stmts₁ q₂)
    (hs : SupportsStmt S q₂) : SupportsStmt S q₁ := by
  induction q₂ with
    simp only [stmts₁, SupportsStmt, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
      at h hs
  | branch f q₁ q₂ IH₁ IH₂ => rcases h with (rfl | h | h); exacts [hs, IH₁ h hs.1, IH₂ h hs.2]
  | goto l => subst h; exact hs
  | halt => subst h; trivial
  | load _ _ IH | _ _ _ _ IH => rcases h with (rfl | h) <;> [exact hs; exact IH h hs]

open scoped Classical in
/--
Definition of `stmts` / `stmts` 的定义

English:
definition stmts
  signature: (M : Λ -> Stmt Γ Λ σ) (S : Finset Λ)
  body: Finset.insertNone (S.biUnion fun q => stmts₁ (M q))

中文:
定义 stmts
  签名: (M : Λ -> Stmt Γ Λ σ) (S : 有限集 Λ)
  定义体: Finset.insertNone (S.biUnion fun q => stmts₁ (M q))

Depends on / 依赖: Finset, Finset.insertNone, S.biUnion, biUnion, insertNone
-/
noncomputable def stmts (M : Λ -> Stmt Γ Λ σ) (S : Finset Λ) : Finset (Option (Stmt Γ Λ σ)) :=
  Finset.insertNone (S.biUnion fun q => stmts₁ (M q))

/--
theorem `stmts_trans` / 定理 `stmts_trans`

English:
theorem stmts_trans
  given: {M : Λ -> Stmt Γ Λ σ} {S : Finset Λ} {q₁ q₂ : Stmt Γ Λ σ} (h₁ : q₁ in stmts₁ q₂)
  proof: by
  simp only [stmts, Finset.mem_insertNone, Finset.mem_biUnion, Option.mem_def, Option.some.injEq,
    forall_eq', exists_imp, and_imp]
  exact fun l ls h₂ => ⟨_, ls, stmts₁_trans h₂ h₁⟩

中文:
定理 stmts_trans
  条件: {M : Λ -> Stmt Γ Λ σ} {S : 有限集 Λ} {q₁ q₂ : Stmt Γ Λ σ} (h₁ : q₁ in stmts₁ q₂)
  证明: by
  simp only [stmts, Finset.mem_insertNone, Finset.mem_biUnion, Option.mem_def, Option.some.injEq,
    forall_eq', exists_imp, and_imp]
  exact fun l ls h₂ => ⟨_, ls, stmts₁_trans h₂ h₁⟩

Depends on / 依赖: Finset, Finset.mem_biUnion, Finset.mem_insertNone, Option.mem_def, Option.some.injEq, and_imp, exists_imp, forall_eq, mem_biUnion, mem_def, mem_insertNone
-/
theorem stmts_trans {M : Λ -> Stmt Γ Λ σ} {S : Finset Λ} {q₁ q₂ : Stmt Γ Λ σ} (h₁ : q₁ in stmts₁ q₂) :
    some q₂ in stmts M S -> some q₁ in stmts M S := by
  simp only [stmts, Finset.mem_insertNone, Finset.mem_biUnion, Option.mem_def, Option.some.injEq,
    forall_eq', exists_imp, and_imp]
  exact fun l ls h₂ => ⟨_, ls, stmts₁_trans h₂ h₁⟩

end

variable [Inhabited Λ]

/--
Definition of `Supports` / `Supports` 的定义

English:
definition Supports
  signature: (M : Λ -> Stmt Γ Λ σ) (S : Finset Λ)
  body: default in S ∧ forall q in S, SupportsStmt S (M q)

中文:
定义 Supports
  签名: (M : Λ -> Stmt Γ Λ σ) (S : 有限集 Λ)
  定义体: default in S ∧ forall q in S, SupportsStmt S (M q)

Depends on / 依赖: SupportsStmt
-/
def Supports (M : Λ -> Stmt Γ Λ σ) (S : Finset Λ) :=
  default in S ∧ forall q in S, SupportsStmt S (M q)

/--
theorem `stmts_supportsStmt` / 定理 `stmts_supportsStmt`

English:
theorem stmts_supportsStmt
  statement: {M : Λ -> Stmt Γ Λ σ} {S : Finset Λ} {q : Stmt Γ Λ σ}
  proof: by
  simp only [stmts, Finset.mem_insertNone, Finset.mem_biUnion, Option.mem_def, Option.some.injEq,
    forall_eq', exists_imp, and_imp]
  exact fun l ls h => stmts₁_supportsStmt_mono h (ss.2 _ ls)

中文:
定理 stmts_supportsStmt
  结论: {M : Λ -> Stmt Γ Λ σ} {S : 有限集 Λ} {q : Stmt Γ Λ σ}
  证明: by
  simp only [stmts, Finset.mem_insertNone, Finset.mem_biUnion, Option.mem_def, Option.some.injEq,
    forall_eq', exists_imp, and_imp]
  exact fun l ls h => stmts₁_supportsStmt_mono h (ss.2 _ ls)

Depends on / 依赖: Finset, Finset.mem_biUnion, Finset.mem_insertNone, Option.mem_def, Option.some.injEq, and_imp, exists_imp, forall_eq, mem_biUnion, mem_def, mem_insertNone
-/
theorem stmts_supportsStmt {M : Λ -> Stmt Γ Λ σ} {S : Finset Λ} {q : Stmt Γ Λ σ}
    (ss : Supports M S) : some q in stmts M S -> SupportsStmt S q := by
  simp only [stmts, Finset.mem_insertNone, Finset.mem_biUnion, Option.mem_def, Option.some.injEq,
    forall_eq', exists_imp, and_imp]
  exact fun l ls h => stmts₁_supportsStmt_mono h (ss.2 _ ls)

variable [DecidableEq K]

/--
theorem `step_supports` / 定理 `step_supports`

English:
theorem step_supports
  given: (M : Λ -> Stmt Γ Λ σ) {S : Finset Λ} (ss : Supports M S)
  proof: ss.2 _ (Finset.some_mem_insertNone.1 h₂)
    simp only [step, Option.mem_def, Option.some.injEq] at h₁; subst c'
    revert h₂; induction M l₁ generalizing v T with intro hs
    | branch p q₁' q₂' IH₁ IH₂ =>
      unfold stepAux; cases p v
      · exact IH₂ _ _ hs.2
      · exact IH₁ _ _ hs.1
    | 

中文:
定理 step_supports
  条件: (M : Λ -> Stmt Γ Λ σ) {S : 有限集 Λ} (ss : Supports M S)
  证明: ss.2 _ (Finset.some_mem_insertNone.1 h₂)
    simp only [step, Option.mem_def, Option.some.injEq] at h₁; subst c'
    revert h₂; induction M l₁ generalizing v T with intro hs
    | branch p q₁' q₂' IH₁ IH₂ =>
      unfold stepAux; cases p v
      · exact IH₂ _ _ hs.2
      · exact IH₁ _ _ hs.1
    | 

Depends on / 依赖: Finset, Finset.some_mem_insertNone, some_mem_insertNone
-/
theorem step_supports (M : Λ -> Stmt Γ Λ σ) {S : Finset Λ} (ss : Supports M S) :
    forall {c c' : Cfg Γ Λ σ}, c' in step M c -> c.l in Finset.insertNone S -> c'.l in Finset.insertNone S
  | ⟨some l₁, v, T⟩, c', h₁, h₂ => by
    replace h₂ := ss.2 _ (Finset.some_mem_insertNone.1 h₂)
    simp only [step, Option.mem_def, Option.some.injEq] at h₁; subst c'
    revert h₂; induction M l₁ generalizing v T with intro hs
    | branch p q₁' q₂' IH₁ IH₂ =>
      unfold stepAux; cases p v
      · exact IH₂ _ _ hs.2
      · exact IH₁ _ _ hs.1
    | goto => exact Finset.some_mem_insertNone.2 (hs _)
    | halt => apply Multiset.mem_cons_self
    | load _ _ IH | _ _ _ _ IH => exact IH _ _ hs

variable [Inhabited σ]

/--
Definition of `init` / `init` 的定义

English:
definition init
  signature: (k : K) (L : List (Γ k))
  body: ⟨some default, default, update (fun _ => []) k L⟩

中文:
定义 init
  签名: (k : K) (L : 列表 (Γ k))
  定义体: ⟨some default, default, update (fun _ => []) k L⟩

Depends on / 依赖: update
-/
def init (k : K) (L : List (Γ k)) : Cfg Γ Λ σ :=
  ⟨some default, default, update (fun _ => []) k L⟩

/--
Definition of `eval` / `eval` 的定义

English:
definition eval
  signature: (M : Λ -> Stmt Γ Λ σ) (k : K) (L : List (Γ k))
  body: (StateTransition.eval (step M) (init k L)).map fun c => c.stk k

中文:
定义 eval
  签名: (M : Λ -> Stmt Γ Λ σ) (k : K) (L : 列表 (Γ k))
  定义体: (StateTransition.eval (step M) (init k L)).map fun c => c.stk k

Depends on / 依赖: StateTransition, StateTransition.eval, c.stk
-/
def eval (M : Λ -> Stmt Γ Λ σ) (k : K) (L : List (Γ k)) : Part (List (Γ k)) :=
  (StateTransition.eval (step M) (init k L)).map fun c => c.stk k

end TM2

/-!
## TM2 emulator in TM1

To prove that TM2 computable functions are TM1 computable, we need to reduce each TM2 program to a
TM1 program. So suppose a TM2 program is given. This program has to maintain a whole collection of
stacks, but we have only one tape, so we must "multiplex" them all together. Pictorially, if stack
1 contains `[a, b]` and stack 2 contains `[c, d, e, f]` then the tape looks like this:

```
bottom: ... | _ | T | _ | _ | _ | _ | ...
stack 1: ... | _ | b | a | _ | _ | _ | ...
stack 2: ... | _ | f | e | d | c | _ | ...
```

where a tape element is a vertical slice through the diagram. Here the alphabet is
`Γ' := Bool × ∀ k, Option (Γ k)`, where:

* `bottom : Bool` is marked only in one place, the initial position of the TM, and represents the
  tail of all stacks. It is never modified.
* `stk k : Option (Γ k)` is the value of the `k`-th stack, if in range, otherwise `none` (which is
  the blank value). Note that the head of the stack is at the far end; this is so that push and pop
  don't have to do any shifting.

In "resting" position, the TM is sitting at the position marked `bottom`. For non-stack actions,
it operates in place, but for the stack actions `push`, `peek`, and `pop`, it must shuttle to the
end of the appropriate stack, make its changes, and then return to the bottom. So the states are:

* `normal (l : Λ)`: waiting at `bottom` to execute function `l`
* `go k (s : StAct k) (q : Stmt₂)`: travelling to the right to get to the end of stack `k` in
  order to perform stack action `s`, and later continue with executing `q`
* `ret (q : Stmt₂)`: travelling to the left after having performed a stack action, and executing
  `q` once we arrive

Because of the shuttling, emulation overhead is `O(n)`, where `n` is the current maximum of the
length of all stacks. Therefore a program that takes `k` steps to run in TM2 takes `O((m+k)k)`
steps to run when emulated in TM1, where `m` is the length of the input.
-/


namespace TM2to1

-- A displaced lemma proved in unnecessary generality
/--
theorem `stk_nth_val` / 定理 `stk_nth_val`

English:
theorem stk_nth_val
  statement: {K : Type*} {Γ : K -> Type*} {L : ListBlank (forall k, Option (Γ k))} {k S} (n)
  proof: by
  rw [← proj_map_nth]; rw [hL]; rw [← List.map_reverse]; rw [ListBlank.nth_mk]; rw [List.getI_eq_getElem?_getD]; rw [List.getElem?_map]
  cases S.reverse[n]? <;> rfl

中文:
定理 stk_nth_val
  结论: {K : 类型} {Γ : K -> 类型} {L : ListBlank (对任意 k, 选项类型 (Γ k))} {k S} (n)
  证明: by
  rw [← proj_map_nth]; rw [hL]; rw [← List.map_reverse]; rw [ListBlank.nth_mk]; rw [List.getI_eq_getElem?_getD]; rw [List.getElem?_map]
  cases S.reverse[n]? <;> rfl

Depends on / 依赖: Infinite, List.getElem, List.getI_eq_getElem, List.map_reverse, ListBlank, ListBlank.nth_mk, Nontrivial, S.reverse, _getD, _map, getElem, getI_eq_getElem, map_reverse, nth_mk, proj_map_nth, reverse
-/
theorem stk_nth_val {K : Type*} {Γ : K -> Type*} {L : ListBlank (forall k, Option (Γ k))} {k S} (n)
    (hL : ListBlank.map (proj k) L = ListBlank.mk (List.map some S).reverse) :
    L.nth n k = S.reverse[n]? := by
  rw [← proj_map_nth]; rw [hL]; rw [← List.map_reverse]; rw [ListBlank.nth_mk]; rw [List.getI_eq_getElem?_getD]; rw [List.getElem?_map]
  cases S.reverse[n]? <;> rfl

variable (K : Type*)
variable (Γ : K -> Type*)
variable {Λ σ : Type*}

/--
Definition of `Γ'` / `Γ'` 的定义

English:
definition Γ'
  body: Bool × forall k, Option (Γ k)

中文:
定义 Γ'
  定义体: Bool × forall k, Option (Γ k)
-/
def Γ' :=
  Bool × forall k, Option (Γ k)

variable {K Γ}

/--
Instance `Γ'.inhabited` / 实例 `Γ'.inhabited`

English:
instance Γ'.inhabited
  signature: : Inhabited (Γ' K Γ)
  body: ⟨⟨false, fun _ => none⟩⟩

中文:
实例 Γ'.inhabited
  签名: : 可居 (Γ' K Γ)
  定义体: ⟨⟨false, fun _ => none⟩⟩
-/
instance Γ'.inhabited : Inhabited (Γ' K Γ) :=
  ⟨⟨false, fun _ => none⟩⟩

/--
Instance `Γ'.fintype` / 实例 `Γ'.fintype`

English:
instance Γ'.fintype
  signature: [DecidableEq K] [Fintype K] [forall k, Fintype (Γ k)]
  body: instFintypeProd _ _

中文:
实例 Γ'.fintype
  签名: [DecidableEq K] [有限类型 K] [对任意 k, 有限类型 (Γ k)]
  定义体: instFintypeProd _ _

Depends on / 依赖: Infinite, Infinite.of_surjective, Sigma.fst, Sigma.fst_surjective, fst_surjective, of_surjective
-/
instance Γ'.fintype [DecidableEq K] [Fintype K] [forall k, Fintype (Γ k)] : Fintype (Γ' K Γ) :=
  instFintypeProd _ _

/--
Definition of `addBottom` / `addBottom` 的定义

English:
definition addBottom
  signature: (L : ListBlank (forall k, Option (Γ k)))
  body: ListBlank.cons (true, L.head) (L.tail.map ⟨Prod.mk false, rfl⟩)

中文:
定义 addBottom
  签名: (L : ListBlank (对任意 k, 选项类型 (Γ k)))
  定义体: ListBlank.cons (true, L.head) (L.tail.map ⟨Prod.mk false, rfl⟩)

Depends on / 依赖: L.head, L.tail.map, ListBlank, ListBlank.cons, Prod.mk
-/
def addBottom (L : ListBlank (forall k, Option (Γ k))) : ListBlank (Γ' K Γ) :=
  ListBlank.cons (true, L.head) (L.tail.map ⟨Prod.mk false, rfl⟩)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `addBottom_map` / 定理 `addBottom_map`

English:
theorem addBottom_map
  given: (L : ListBlank (forall k, Option (Γ k)))
  proof: by
  simp only [addBottom, ListBlank.map_cons]
  convert! ListBlank.cons_head_tail L
  generalize ListBlank.tail L = L'
  refine L'.induction_on fun l => ?_; simp

中文:
定理 addBottom_map
  条件: (L : ListBlank (对任意 k, 选项类型 (Γ k)))
  证明: by
  simp only [addBottom, ListBlank.map_cons]
  convert! ListBlank.cons_head_tail L
  generalize ListBlank.tail L = L'
  refine L'.induction_on fun l => ?_; simp

Depends on / 依赖: Classical, Classical.arbitrary, Infinite, Infinite.sigma_of_right, ListBlank, ListBlank.cons_head_tail, ListBlank.map_cons, ListBlank.tail, addBottom, arbitrary, cons_head_tail, convert, generalize, induction_on, map_cons, sigma_of_right
-/
theorem addBottom_map (L : ListBlank (forall k, Option (Γ k))) :
    (addBottom L).map ⟨Prod.snd, by rfl⟩ = L := by
  simp only [addBottom, ListBlank.map_cons]
  convert! ListBlank.cons_head_tail L
  generalize ListBlank.tail L = L'
  refine L'.induction_on fun l => ?_; simp

set_option backward.isDefEq.respectTransparency false in
/--
theorem `addBottom_modifyNth` / 定理 `addBottom_modifyNth`

English:
theorem addBottom_modifyNth
  statement: (f : (forall k, Option (Γ k)) -> forall k, Option (Γ k))
  proof: by
  cases n <;>
    simp only [addBottom, ListBlank.head_cons, ListBlank.modifyNth, ListBlank.tail_cons]
  congr; symm; apply ListBlank.map_modifyNth; intro; rfl

中文:
定理 addBottom_modifyNth
  结论: (f : (对任意 k, 选项类型 (Γ k)) -> 对任意 k, 选项类型 (Γ k))
  证明: by
  cases n <;>
    simp only [addBottom, ListBlank.head_cons, ListBlank.modifyNth, ListBlank.tail_cons]
  congr; symm; apply ListBlank.map_modifyNth; intro; rfl

Depends on / 依赖: ListBlank, ListBlank.head_cons, ListBlank.map_modifyNth, ListBlank.modifyNth, ListBlank.tail_cons, addBottom, head_cons, map_modifyNth, modifyNth, tail_cons
-/
theorem addBottom_modifyNth (f : (forall k, Option (Γ k)) -> forall k, Option (Γ k))
    (L : ListBlank (forall k, Option (Γ k))) (n : Nat) :
    (addBottom L).modifyNth (fun a => (a.1, f a.2)) n = addBottom (L.modifyNth f n) := by
  cases n <;>
    simp only [addBottom, ListBlank.head_cons, ListBlank.modifyNth, ListBlank.tail_cons]
  congr; symm; apply ListBlank.map_modifyNth; intro; rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `addBottom_nth_snd` / 定理 `addBottom_nth_snd`

English:
theorem addBottom_nth_snd
  given: (L : ListBlank (forall k, Option (Γ k))) (n : Nat)
  proof: by
  conv => rhs; rw [← addBottom_map L, ListBlank.nth_map]

中文:
定理 addBottom_nth_snd
  条件: (L : ListBlank (对任意 k, 选项类型 (Γ k))) (n : 自然数)
  证明: by
  conv => rhs; rw [← addBottom_map L, ListBlank.nth_map]

Depends on / 依赖: ListBlank, ListBlank.nth_map, addBottom_map, nth_map
-/
theorem addBottom_nth_snd (L : ListBlank (forall k, Option (Γ k))) (n : Nat) :
    ((addBottom L).nth n).2 = L.nth n := by
  conv => rhs; rw [← addBottom_map L, ListBlank.nth_map]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `addBottom_nth_succ_fst` / 定理 `addBottom_nth_succ_fst`

English:
theorem addBottom_nth_succ_fst
  given: (L : ListBlank (forall k, Option (Γ k))) (n : Nat)
  proof: by
  rw [ListBlank.nth_succ]; rw [addBottom]; rw [ListBlank.tail_cons]; rw [ListBlank.nth_map]

中文:
定理 addBottom_nth_succ_fst
  条件: (L : ListBlank (对任意 k, 选项类型 (Γ k))) (n : 自然数)
  证明: by
  rw [ListBlank.nth_succ]; rw [addBottom]; rw [ListBlank.tail_cons]; rw [ListBlank.nth_map]

Depends on / 依赖: ListBlank, ListBlank.nth_map, ListBlank.nth_succ, ListBlank.tail_cons, addBottom, nth_map, nth_succ, tail_cons
-/
theorem addBottom_nth_succ_fst (L : ListBlank (forall k, Option (Γ k))) (n : Nat) :
    ((addBottom L).nth (n + 1)).1 = false := by
  rw [ListBlank.nth_succ]; rw [addBottom]; rw [ListBlank.tail_cons]; rw [ListBlank.nth_map]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `addBottom_head_fst` / 定理 `addBottom_head_fst`

English:
theorem addBottom_head_fst
  given: (L : ListBlank (forall k, Option (Γ k)))
  statement: (addBottom L).head.1 = true
  proof: by
  rw [addBottom]; rw [ListBlank.head_cons]

中文:
定理 addBottom_head_fst
  条件: (L : ListBlank (对任意 k, 选项类型 (Γ k)))
  结论: (addBottom L).head.1 = true
  证明: by
  rw [addBottom]; rw [ListBlank.head_cons]

Depends on / 依赖: ListBlank, ListBlank.head_cons, addBottom, head_cons
-/
theorem addBottom_head_fst (L : ListBlank (forall k, Option (Γ k))) : (addBottom L).head.1 = true := by
  rw [addBottom]; rw [ListBlank.head_cons]

variable (K Γ σ) in
/--
Inductive type `StAct` / 归纳类型 `StAct`

English:
inductive StAct
  parameters: (k : K)
  constructors (3):
    - push: (σ -> Γ k) -> StAct k
    - peek: (σ -> Option (Γ k) -> σ) -> StAct k
    - pop: (σ -> Option (Γ k) -> σ) -> StAct k

中文:
归纳类型 StAct
  参数: (k : K)
  构造子 (3 个):
    - push: (σ -> Γ k) -> StAct k
    - peek: (σ -> 选项类型 (Γ k) -> σ) -> StAct k
    - pop: (σ -> 选项类型 (Γ k) -> σ) -> StAct k
-/
inductive StAct (k : K)
  | push : (σ -> Γ k) -> StAct k
  | peek : (σ -> Option (Γ k) -> σ) -> StAct k
  | pop : (σ -> Option (Γ k) -> σ) -> StAct k

/--
Instance `StAct.inhabited` / 实例 `StAct.inhabited`

English:
instance StAct.inhabited
  signature: {k : K}
  body: ⟨StAct.peek fun s _ => s⟩

中文:
实例 StAct.inhabited
  签名: {k : K}
  定义体: ⟨StAct.peek fun s _ => s⟩

Depends on / 依赖: StAct.peek
-/
instance StAct.inhabited {k : K} : Inhabited (StAct K Γ σ k) :=
  ⟨StAct.peek fun s _ => s⟩

section

open StAct

/--
Definition of `stRun` / `stRun` 的定义

English:
definition stRun
  signature: {k : K}

中文:
定义 stRun
  签名: {k : K}
-/
def stRun {k : K} : StAct K Γ σ k -> TM2.Stmt Γ Λ σ -> TM2.Stmt Γ Λ σ
  | push f => TM2.Stmt.push k f
  | peek f => TM2.Stmt.peek k f
  | pop f => TM2.Stmt.pop k f

/--
Definition of `stVar` / `stVar` 的定义

English:
definition stVar
  signature: {k : K} (v : σ) (l : List (Γ k))

中文:
定义 stVar
  签名: {k : K} (v : σ) (l : 列表 (Γ k))
-/
def stVar {k : K} (v : σ) (l : List (Γ k)) : StAct K Γ σ k -> σ
  | push _ => v
  | peek f => f v l.head?
  | pop f => f v l.head?

/--
Definition of `stWrite` / `stWrite` 的定义

English:
definition stWrite
  signature: {k : K} (v : σ) (l : List (Γ k))

中文:
定义 stWrite
  签名: {k : K} (v : σ) (l : 列表 (Γ k))
-/
def stWrite {k : K} (v : σ) (l : List (Γ k)) : StAct K Γ σ k -> List (Γ k)
  | push f => f v :: l
  | peek _ => l
  | pop _ => l.tail

/-- We have partitioned the TM2 statements into "stack actions", which require going to the end
of the stack, and all other actions, which do not. This is a modified recursor which lumps the
stack actions into one. -/
@[elab_as_elim]
/--
Definition of `stmtStRec.` / `stmtStRec.` 的定义

English:
definition stmtStRec.{l}
  signature: {motive : TM2.Stmt Γ Λ σ -> Sort l}

中文:
定义 stmtStRec.{l}
  签名: {motive : TM2.Stmt Γ Λ σ -> 类型层 l}
-/
def stmtStRec.{l} {motive : TM2.Stmt Γ Λ σ -> Sort l}
    (run : forall (k) (s : StAct K Γ σ k) (q) (_ : motive q), motive (stRun s q))
    (load : forall (a q) (_ : motive q), motive (TM2.Stmt.load a q))
    (branch : forall (p q₁ q₂) (_ : motive q₁) (_ : motive q₂), motive (TM2.Stmt.branch p q₁ q₂))
    (goto : forall l, motive (TM2.Stmt.goto l)) (halt : motive TM2.Stmt.halt) : forall n, motive n
  | TM2.Stmt.push _ f q => run _ (push f) _ (stmtStRec run load branch goto halt q)
  | TM2.Stmt.peek _ f q => run _ (peek f) _ (stmtStRec run load branch goto halt q)
  | TM2.Stmt.pop _ f q => run _ (pop f) _ (stmtStRec run load branch goto halt q)
  | TM2.Stmt.load _ q => load _ _ (stmtStRec run load branch goto halt q)
  | TM2.Stmt.branch _ q₁ q₂ =>
    branch _ _ _ (stmtStRec run load branch goto halt q₁) (stmtStRec run load branch goto halt q₂)
  | TM2.Stmt.goto _ => goto _
  | TM2.Stmt.halt => halt

/--
theorem `supports_run` / 定理 `supports_run`

English:
theorem supports_run
  given: (S : Finset Λ) {k : K} (s : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ)
  proof: by
  cases s <;> rfl

中文:
定理 supports_run
  条件: (S : 有限集 Λ) {k : K} (s : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ)
  证明: by
  cases s <;> rfl
-/
theorem supports_run (S : Finset Λ) {k : K} (s : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ) :
    TM2.SupportsStmt S (stRun s q) ↔ TM2.SupportsStmt S q := by
  cases s <;> rfl

end

variable (K Γ Λ σ)

/--
Inductive type `Λ'` / 归纳类型 `Λ'`

English:
inductive Λ'
  constructors (3):
    - normal: Λ -> Λ'
    - go: (k : K) : StAct K Γ σ k -> TM2.Stmt Γ Λ σ -> Λ'
    - ret: TM2.Stmt Γ Λ σ -> Λ'

中文:
归纳类型 Λ'
  构造子 (3 个):
    - normal: Λ -> Λ'
    - go: (k : K) : StAct K Γ σ k -> TM2.Stmt Γ Λ σ -> Λ'
    - ret: TM2.Stmt Γ Λ σ -> Λ'
-/
inductive Λ'
  | normal : Λ -> Λ'
  | go (k : K) : StAct K Γ σ k -> TM2.Stmt Γ Λ σ -> Λ'
  | ret : TM2.Stmt Γ Λ σ -> Λ'

variable {K Γ Λ σ}

open Λ'

/--
Instance `Λ'.inhabited` / 实例 `Λ'.inhabited`

English:
instance Λ'.inhabited
  signature: [Inhabited Λ]
  body: ⟨normal default⟩

中文:
实例 Λ'.inhabited
  签名: [可居 Λ]
  定义体: ⟨normal default⟩

Depends on / 依赖: normal
-/
instance Λ'.inhabited [Inhabited Λ] : Inhabited (Λ' K Γ Λ σ) :=
  ⟨normal default⟩

open TM1.Stmt

section
variable [DecidableEq K]

/--
Definition of `trStAct` / `trStAct` 的定义

English:
definition trStAct
  signature: {k : K} (q : TM1.Stmt (Γ' K Γ) (Λ' K Γ Λ σ) σ)

中文:
定义 trStAct
  签名: {k : K} (q : TM1.Stmt (Γ' K Γ) (Λ' K Γ Λ σ) σ)
-/
def trStAct {k : K} (q : TM1.Stmt (Γ' K Γ) (Λ' K Γ Λ σ) σ) :
    StAct K Γ σ k -> TM1.Stmt (Γ' K Γ) (Λ' K Γ Λ σ) σ
| StAct.push f => (write fun a s => (a.1, update a.2 k <| some <| f s)) move Dir.right q
| StAct.peek f => move Dir.left (load fun a s => f s (a.2 k)) move Dir.right q
  | StAct.pop f =>
    branch (fun a _ => a.1) (load (fun _ s => f s none) q)
      (move Dir.left <|
(load fun a s => f s (a.2 k)) write (fun a _ => (a.1, update a.2 k none)) q)

/--
Definition of `trInit` / `trInit` 的定义

English:
definition trInit
  signature: (k : K) (L : List (Γ k))
  body: let L' : List (Γ' K Γ) := L.reverse.map fun a => (false, update (fun _ => none) k (some a))
  (true, L'.headI.2) :: L'.tail

中文:
定义 trInit
  签名: (k : K) (L : 列表 (Γ k))
  定义体: let L' : List (Γ' K Γ) := L.reverse.map fun a => (false, update (fun _ => none) k (some a))
  (true, L'.headI.2) :: L'.tail

Depends on / 依赖: L.reverse.map, reverse, update
-/
def trInit (k : K) (L : List (Γ k)) : List (Γ' K Γ) :=
  let L' : List (Γ' K Γ) := L.reverse.map fun a => (false, update (fun _ => none) k (some a))
  (true, L'.headI.2) :: L'.tail

/--
theorem `step_run` / 定理 `step_run`

English:
theorem step_run
  given: {k : K} (q : TM2.Stmt Γ Λ σ) (v : σ) (S : forall k, List (Γ k))
  statement: forall s : StAct K Γ σ k,

中文:
定理 step_run
  条件: {k : K} (q : TM2.Stmt Γ Λ σ) (v : σ) (S : 对任意 k, 列表 (Γ k))
  结论: 对任意 s : StAct K Γ σ k,
-/
theorem step_run {k : K} (q : TM2.Stmt Γ Λ σ) (v : σ) (S : forall k, List (Γ k)) : forall s : StAct K Γ σ k,
    TM2.stepAux (stRun s q) v S = TM2.stepAux q (stVar v (S k) s) (update S k (stWrite v (S k) s))
  | StAct.push _ => rfl
  | StAct.peek f => by unfold stWrite; rw [Function.update_eq_self]; rfl
  | StAct.pop _ => rfl

end

/--
Definition of `trNormal` / `trNormal` 的定义

English:
definition trNormal
  signature: : TM2.Stmt Γ Λ σ -> TM1.Stmt (Γ' K Γ) (Λ' K Γ Λ σ) σ

中文:
定义 trNormal
  签名: : TM2.Stmt Γ Λ σ -> TM1.Stmt (Γ' K Γ) (Λ' K Γ Λ σ) σ
-/
def trNormal : TM2.Stmt Γ Λ σ -> TM1.Stmt (Γ' K Γ) (Λ' K Γ Λ σ) σ
  | TM2.Stmt.push k f q => goto fun _ _ => go k (StAct.push f) q
  | TM2.Stmt.peek k f q => goto fun _ _ => go k (StAct.peek f) q
  | TM2.Stmt.pop k f q => goto fun _ _ => go k (StAct.pop f) q
  | TM2.Stmt.load a q => load (fun _ => a) (trNormal q)
  | TM2.Stmt.branch f q₁ q₂ => branch (fun _ => f) (trNormal q₁) (trNormal q₂)
  | TM2.Stmt.goto l => goto fun _ s => normal (l s)
  | TM2.Stmt.halt => halt

/--
theorem `trNormal_run` / 定理 `trNormal_run`

English:
theorem trNormal_run
  given: {k : K} (s : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ)
  proof: by
  cases s <;> rfl

中文:
定理 trNormal_run
  条件: {k : K} (s : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ)
  证明: by
  cases s <;> rfl
-/
theorem trNormal_run {k : K} (s : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ) :
    trNormal (stRun s q) = goto fun _ _ => go k s q := by
  cases s <;> rfl

section

open scoped Classical in
/--
Definition of `trStmts₁` / `trStmts₁` 的定义

English:
definition trStmts₁
  signature: : TM2.Stmt Γ Λ σ -> Finset (Λ' K Γ Λ σ)

中文:
定义 trStmts₁
  签名: : TM2.Stmt Γ Λ σ -> 有限集 (Λ' K Γ Λ σ)
-/
noncomputable def trStmts₁ : TM2.Stmt Γ Λ σ -> Finset (Λ' K Γ Λ σ)
  | TM2.Stmt.push k f q => {go k (StAct.push f) q, ret q} union trStmts₁ q
  | TM2.Stmt.peek k f q => {go k (StAct.peek f) q, ret q} union trStmts₁ q
  | TM2.Stmt.pop k f q => {go k (StAct.pop f) q, ret q} union trStmts₁ q
  | TM2.Stmt.load _ q => trStmts₁ q
  | TM2.Stmt.branch _ q₁ q₂ => trStmts₁ q₁ union trStmts₁ q₂
  | _ => ∅

/--
theorem `trStmts₁_run` / 定理 `trStmts₁_run`

English:
theorem trStmts₁_run
  given: {k : K} {s : StAct K Γ σ k} {q : TM2.Stmt Γ Λ σ}
  proof: by
  cases s <;> simp only [trStmts₁, stRun]

中文:
定理 trStmts₁_run
  条件: {k : K} {s : StAct K Γ σ k} {q : TM2.Stmt Γ Λ σ}
  证明: by
  cases s <;> simp only [trStmts₁, stRun]
-/
theorem trStmts₁_run {k : K} {s : StAct K Γ σ k} {q : TM2.Stmt Γ Λ σ} :
    open scoped Classical in
    trStmts₁ (stRun s q) = {go k s q, ret q} union trStmts₁ q := by
  cases s <;> simp only [trStmts₁, stRun]

/--
theorem `tr_respects_aux₂` / 定理 `tr_respects_aux₂`

English:
theorem tr_respects_aux₂
  statement: [DecidableEq K] {k : K} {q : TM1.Stmt (Γ' K Γ) (Λ' K Γ Λ σ) σ} {v : σ}
  proof: stVar v (S k) o
    let Sk' := stWrite v (S k) o
    let S' := update S k Sk'
    exists L' : ListBlank (forall k, Option (Γ k)),
      (forall k, L'.map (proj k) = ListBlank.mk ((S' k).map some).reverse) ∧
        TM1.stepAux (trStAct q o) v
            ((Tape.move Dir.right)^[(S k).length] (Tape.m

中文:
定理 tr_respects_aux₂
  结论: [DecidableEq K] {k : K} {q : TM1.Stmt (Γ' K Γ) (Λ' K Γ Λ σ) σ} {v : σ}
  证明: stVar v (S k) o
    let Sk' := stWrite v (S k) o
    let S' := update S k Sk'
    exists L' : ListBlank (forall k, Option (Γ k)),
      (forall k, L'.map (proj k) = ListBlank.mk ((S' k).map some).reverse) ∧
        TM1.stepAux (trStAct q o) v
            ((Tape.move Dir.right)^[(S k).length] (Tape.m
-/
theorem tr_respects_aux₂ [DecidableEq K] {k : K} {q : TM1.Stmt (Γ' K Γ) (Λ' K Γ Λ σ) σ} {v : σ}
    {S : forall k, List (Γ k)} {L : ListBlank (forall k, Option (Γ k))}
    (hL : forall k, L.map (proj k) = ListBlank.mk ((S k).map some).reverse) (o : StAct K Γ σ k) :
    let v' := stVar v (S k) o
    let Sk' := stWrite v (S k) o
    let S' := update S k Sk'
    exists L' : ListBlank (forall k, Option (Γ k)),
      (forall k, L'.map (proj k) = ListBlank.mk ((S' k).map some).reverse) ∧
        TM1.stepAux (trStAct q o) v
            ((Tape.move Dir.right)^[(S k).length] (Tape.mk' ∅ (addBottom L))) =
          TM1.stepAux q v' ((Tape.move Dir.right)^[(S' k).length] (Tape.mk' ∅ (addBottom L'))) := by
  simp only [Function.update_self]; cases o with simp only [stWrite, stVar, trStAct, TM1.stepAux]
  | push f =>
    have := Tape.write_move_right_n fun a : Γ' K Γ => (a.1, update a.2 k (some (f v)))
    refine
      ⟨_, fun k' => ?_, by
        -- Porting note: `rw [...]` to `erw [...]; rfl`.
        -- https://github.com/leanprover-community/mathlib4/issues/5164
        rw [Tape.move_right_n_head]; rw [List.length]; rw [Tape.mk'_nth_nat]; rw [this]
        erw [addBottom_modifyNth fun a => update a k (some (f v))]
        rw [Nat.add_one]; rw [iterate_succ']
        rfl⟩
    refine ListBlank.ext fun i => ?_
    rw [ListBlank.nth_map]; rw [ListBlank.nth_modifyNth]; rw [proj]; rw [PointedMap.mk_val]
    by_cases h' : k' = k
    · subst k'
      split_ifs with h
        <;> simp only [List.reverse_cons, Function.update_self, ListBlank.nth_mk, List.map]
      · rw [List.getI_eq_getElem _, List.getElem_append_right] <;>
        simp only [List.length_append, List.length_reverse, List.length_map, ← h,
          Nat.sub_self, List.length_singleton, List.getElem_singleton,
          le_refl, Nat.lt_succ_self]
      rw [← proj_map_nth]; rw [hL]; rw [ListBlank.nth_mk]
      rcases lt_or_gt_of_ne h with h | h
      · rw [List.getI_append]
        simpa only [List.length_map, List.length_reverse] using h
      · rw [List.getI_eq_default, List.getI_eq_default] <;>
          simp only [Nat.add_one_le_iff, h, List.length, le_of_lt, List.length_reverse,
            List.length_append, List.length_map]
    · split_ifs <;> rw [Function.update_of_ne h', ← proj_map_nth, hL]
      rw [Function.update_of_ne h']
  | peek f =>
    rw [Function.update_eq_self]
    use L, hL; rw [Tape.move_left_right]; congr
    cases e : S k; · rfl
    rw [List.length_cons]; rw [iterate_succ']; rw [Function.comp]; rw [Tape.move_right_left]; rw [Tape.move_right_n_head]; rw [Tape.mk'_nth_nat]; rw [addBottom_nth_snd]; rw [stk_nth_val _ (hL k)]; rw [e]; rw [List.reverse_cons]; rw [← List.length_reverse]; rw [List.getElem?_concat_length]
    rfl
  | pop f =>
    rcases e : S k with - | ⟨hd, tl⟩
    · simp only [Tape.mk'_head, ListBlank.head_cons, Tape.move_left_mk', List.length,
        List.head?, iterate_zero_apply, List.tail_nil]
      rw [← e]; rw [Function.update_eq_self]
      exact ⟨L, hL, by rw [addBottom_head_fst, cond]⟩
    · refine
        ⟨_, fun k' => ?_, by
          erw [List.length_cons, Tape.move_right_n_head, Tape.mk'_nth_nat, addBottom_nth_succ_fst,
            cond_false, iterate_succ', Function.comp, Tape.move_right_left, Tape.move_right_n_head,
            Tape.mk'_nth_nat, Tape.write_move_right_n fun a : Γ' K Γ => (a.1, update a.2 k none),
            addBottom_modifyNth fun a => update a k none, addBottom_nth_snd,
            stk_nth_val _ (hL k), e,
            show (List.cons hd tl).reverse[tl.length]? = some hd by
              rw [List.reverse_cons]; rw [← List.length_reverse]; rw [List.getElem?_concat_length],
            List.head?, List.tail]⟩
      refine ListBlank.ext fun i => ?_
      rw [ListBlank.nth_map]; rw [ListBlank.nth_modifyNth]; rw [proj]; rw [PointedMap.mk_val]
      by_cases h' : k' = k
      · subst k'
        split_ifs with h <;> simp only [Function.update_self, ListBlank.nth_mk, List.tail]
        · rw [List.getI_eq_default]
          · rfl
          rw [h]; rw [List.length_reverse]; rw [List.length_map]
        rw [← proj_map_nth]; rw [hL]; rw [ListBlank.nth_mk]; rw [e]; rw [List.map]; rw [List.reverse_cons]
        rcases lt_or_gt_of_ne h with h | h
        · rw [List.getI_append]
          simpa only [List.length_map, List.length_reverse] using h
        · rw [List.getI_eq_default, List.getI_eq_default] <;>
            simp only [Nat.add_one_le_iff, h, List.length, le_of_lt, List.length_reverse,
              List.length_append, List.length_map]
      · split_ifs <;> rw [Function.update_of_ne h', ← proj_map_nth, hL]
        rw [Function.update_of_ne h']

end

open StateTransition

variable [DecidableEq K]
variable (M : Λ -> TM2.Stmt Γ Λ σ)

/--
Definition of `tr` / `tr` 的定义

English:
definition tr
  signature: : Λ' K Γ Λ σ -> TM1.Stmt (Γ' K Γ) (Λ' K Γ Λ σ) σ

中文:
定义 tr
  签名: : Λ' K Γ Λ σ -> TM1.Stmt (Γ' K Γ) (Λ' K Γ Λ σ) σ
-/
def tr : Λ' K Γ Λ σ -> TM1.Stmt (Γ' K Γ) (Λ' K Γ Λ σ) σ
  | normal q => trNormal (M q)
  | go k s q =>
    branch (fun a _ => (a.2 k).isNone) (trStAct (goto fun _ _ => ret q) s)
      (move Dir.right <| goto fun _ _ => go k s q)
  | ret q => branch (fun a _ => a.1) (trNormal q) (move Dir.left <| goto fun _ _ => ret q)

/--
Inductive type `TrCfg` / 归纳类型 `TrCfg`

English:
inductive TrCfg
  parameters: : TM2.Cfg Γ Λ σ -> TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ -> Prop
  constructors (1):
    - mk: {q : Option Λ} {v : σ} {S : forall k, List (Γ k)} (L : ListBlank (forall k, Option (Γ k))) : (forall k, L.map (proj k) = ListBlank.mk ((S k).map some).reverse) -> TrCfg ⟨q, v, S⟩ ⟨q.map normal, v, Tape.mk' ∅ (addBottom L)⟩

中文:
归纳类型 TrCfg
  参数: : TM2.Cfg Γ Λ σ -> TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ -> 命题
  构造子 (1 个):
    - mk: {q : 选项类型 Λ} {v : σ} {S : 对任意 k, 列表 (Γ k)} (L : ListBlank (对任意 k, 选项类型 (Γ k))) : (对任意 k, L.map (proj k) = ListBlank.mk ((S k).map some).reverse) -> TrCfg ⟨q, v, S⟩ ⟨q.map normal, v, Tape.mk' ∅ (addBottom L)⟩
-/
inductive TrCfg : TM2.Cfg Γ Λ σ -> TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ -> Prop
  | mk {q : Option Λ} {v : σ} {S : forall k, List (Γ k)} (L : ListBlank (forall k, Option (Γ k))) :
    (forall k, L.map (proj k) = ListBlank.mk ((S k).map some).reverse) ->
      TrCfg ⟨q, v, S⟩ ⟨q.map normal, v, Tape.mk' ∅ (addBottom L)⟩

/--
theorem `tr_respects_aux₁` / 定理 `tr_respects_aux₁`

English:
theorem tr_respects_aux₁
  statement: {k} (o q v) {S : List (Γ k)} {L : ListBlank (forall k, Option (Γ k))}
  proof: by
  induction n with
  | zero => rfl
  | succ n IH =>
    apply (IH (le_of_lt H)).tail
    rw [iterate_succ_apply']
    simp only [TM1.step, TM1.stepAux, tr, Tape.mk'_nth_nat, Tape.move_right_n_head,
      addBottom_nth_snd, Option.mem_def]
    rw [stk_nth_val _ hL]; rw [List.getElem?_eq_getElem]
 

中文:
定理 tr_respects_aux₁
  结论: {k} (o q v) {S : 列表 (Γ k)} {L : ListBlank (对任意 k, 选项类型 (Γ k))}
  证明: by
  induction n with
  | zero => rfl
  | succ n IH =>
    apply (IH (le_of_lt H)).tail
    rw [iterate_succ_apply']
    simp only [TM1.step, TM1.stepAux, tr, Tape.mk'_nth_nat, Tape.move_right_n_head,
      addBottom_nth_snd, Option.mem_def]
    rw [stk_nth_val _ hL]; rw [List.getElem?_eq_getElem]
 

Depends on / 依赖: List.getElem, List.length_reverse, Option.mem_def, TM1.step, TM1.stepAux, Tape.mk, Tape.move_right_n_head, _eq_getElem, _nth_nat, addBottom_nth_snd, getElem, iterate_succ_apply, le_of_lt, length_reverse, mem_def, move_right_n_head, stepAux, stk_nth_val
-/
theorem tr_respects_aux₁ {k} (o q v) {S : List (Γ k)} {L : ListBlank (forall k, Option (Γ k))}
    (hL : L.map (proj k) = ListBlank.mk (S.map some).reverse) (n) (H : n <= S.length) :
    Reaches₀ (TM1.step (tr M)) ⟨some (go k o q), v, Tape.mk' ∅ (addBottom L)⟩
      ⟨some (go k o q), v, (Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩ := by
  induction n with
  | zero => rfl
  | succ n IH =>
    apply (IH (le_of_lt H)).tail
    rw [iterate_succ_apply']
    simp only [TM1.step, TM1.stepAux, tr, Tape.mk'_nth_nat, Tape.move_right_n_head,
      addBottom_nth_snd, Option.mem_def]
    rw [stk_nth_val _ hL]; rw [List.getElem?_eq_getElem]
    · rfl
    · rwa [List.length_reverse]

/--
theorem `tr_respects_aux₃` / 定理 `tr_respects_aux₃`

English:
theorem tr_respects_aux₃
  given: {q v} {L : ListBlank (forall k, Option (Γ k))} (n)
  statement: Reaches₀ (TM1.step (tr M))
  proof: by
  induction n with
  | zero => rfl
  | succ n IH =>
    refine Reaches₀.head ?_ IH
    simp only [Option.mem_def, TM1.step]
    rw [Option.some_inj]; rw [tr]; rw [TM1.stepAux]; rw [Tape.move_right_n_head]; rw [Tape.mk'_nth_nat]; rw [addBottom_nth_succ_fst]; rw [TM1.stepAux]; rw [iterate_succ']; r

中文:
定理 tr_respects_aux₃
  条件: {q v} {L : ListBlank (对任意 k, 选项类型 (Γ k))} (n)
  结论: Reaches₀ (TM1.step (tr M))
  证明: by
  induction n with
  | zero => rfl
  | succ n IH =>
    refine Reaches₀.head ?_ IH
    simp only [Option.mem_def, TM1.step]
    rw [Option.some_inj]; rw [tr]; rw [TM1.stepAux]; rw [Tape.move_right_n_head]; rw [Tape.mk'_nth_nat]; rw [addBottom_nth_succ_fst]; rw [TM1.stepAux]; rw [iterate_succ']; r

Depends on / 依赖: Function, Function.comp_apply, Option.mem_def, Option.some_inj, TM1.step, TM1.stepAux, Tape.mk, Tape.move_right_left, Tape.move_right_n_head, _nth_nat, addBottom_nth_succ_fst, comp_apply, iterate_succ, mem_def, move_right_left, move_right_n_head, some_inj, stepAux
-/
theorem tr_respects_aux₃ {q v} {L : ListBlank (forall k, Option (Γ k))} (n) : Reaches₀ (TM1.step (tr M))
    ⟨some (ret q), v, (Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩
    ⟨some (ret q), v, Tape.mk' ∅ (addBottom L)⟩ := by
  induction n with
  | zero => rfl
  | succ n IH =>
    refine Reaches₀.head ?_ IH
    simp only [Option.mem_def, TM1.step]
    rw [Option.some_inj]; rw [tr]; rw [TM1.stepAux]; rw [Tape.move_right_n_head]; rw [Tape.mk'_nth_nat]; rw [addBottom_nth_succ_fst]; rw [TM1.stepAux]; rw [iterate_succ']; rw [Function.comp_apply]; rw [Tape.move_right_left]
    rfl

/--
theorem `tr_respects_aux` / 定理 `tr_respects_aux`

English:
theorem tr_respects_aux
  statement: {q v T k} {S : forall k, List (Γ k)}
  proof: by
  simp only [trNormal_run, step_run]
  have hgo := tr_respects_aux₁ M o q v (hT k) _ le_rfl
  obtain ⟨T', hT', hrun⟩ := tr_respects_aux₂ (Λ := Λ) hT o
  have := hgo.tail' rfl
  rw [tr]; rw [TM1.stepAux]; rw [Tape.move_right_n_head]; rw [Tape.mk'_nth_nat]; rw [addBottom_nth_snd]; rw [stk_nth_val _

中文:
定理 tr_respects_aux
  结论: {q v T k} {S : 对任意 k, 列表 (Γ k)}
  证明: by
  simp only [trNormal_run, step_run]
  have hgo := tr_respects_aux₁ M o q v (hT k) _ le_rfl
  obtain ⟨T', hT', hrun⟩ := tr_respects_aux₂ (Λ := Λ) hT o
  have := hgo.tail' rfl
  rw [tr]; rw [TM1.stepAux]; rw [Tape.move_right_n_head]; rw [Tape.mk'_nth_nat]; rw [addBottom_nth_snd]; rw [stk_nth_val _

Depends on / 依赖: List.getElem, List.length_reverse, Option.isNone, TM1.stepAux, Tape.mk, Tape.move_right_n_head, _eq_none, _nth_nat, addBottom_nth_snd, getElem, hgo.tail, isNone, le_of_eq, le_rfl, length_reverse, move_right_n_head, stepAux, step_run, stk_nth_val, this.to
-/
theorem tr_respects_aux {q v T k} {S : forall k, List (Γ k)}
    (hT : forall k, ListBlank.map (proj k) T = ListBlank.mk ((S k).map some).reverse)
    (o : StAct K Γ σ k)
    (IH : forall {v : σ} {S : forall k : K, List (Γ k)} {T : ListBlank (forall k, Option (Γ k))},
      (forall k, ListBlank.map (proj k) T = ListBlank.mk ((S k).map some).reverse) ->
      exists b, TrCfg (TM2.stepAux q v S) b ∧
        Reaches (TM1.step (tr M)) (TM1.stepAux (trNormal q) v (Tape.mk' ∅ (addBottom T))) b) :
    exists b, TrCfg (TM2.stepAux (stRun o q) v S) b ∧ Reaches (TM1.step (tr M))
      (TM1.stepAux (trNormal (stRun o q)) v (Tape.mk' ∅ (addBottom T))) b := by
  simp only [trNormal_run, step_run]
  have hgo := tr_respects_aux₁ M o q v (hT k) _ le_rfl
  obtain ⟨T', hT', hrun⟩ := tr_respects_aux₂ (Λ := Λ) hT o
  have := hgo.tail' rfl
  rw [tr]; rw [TM1.stepAux]; rw [Tape.move_right_n_head]; rw [Tape.mk'_nth_nat]; rw [addBottom_nth_snd]; rw [stk_nth_val _ (hT k)]; rw [List.getElem?_eq_none (le_of_eq List.length_reverse)]; rw [Option.isNone]; rw [cond]; rw [hrun]; rw [TM1.stepAux] at this
  obtain ⟨c, gc, rc⟩ := IH hT'
  refine ⟨c, gc, (this.to₀.trans (tr_respects_aux₃ M _) c (TransGen.head' rfl ?_)).to_reflTransGen⟩
  rw [tr]; rw [TM1.stepAux]; rw [Tape.mk'_head]; rw [addBottom_head_fst]
  exact rc

attribute [local simp] Respects TM2.step TM2.stepAux trNormal

/--
theorem `tr_respects` / 定理 `tr_respects`

English:
theorem tr_respects
  statement: Respects (TM2.step M) (TM1.step (tr M)) TrCfg
  proof: by
  intro c₁ c₂ h
  obtain @⟨- | l, v, S, L, hT⟩ := h; · constructor
  rsuffices ⟨b, c, r⟩ : exists b, _ ∧ Reaches (TM1.step (tr M)) _ _
  · exact ⟨b, c, TransGen.head' rfl r⟩
  simp only [tr]
  generalize M l = N
  induction N using stmtStRec generalizing v S L hT with
  | run k s q IH => exact tr

中文:
定理 tr_respects
  结论: Respects (TM2.step M) (TM1.step (tr M)) TrCfg
  证明: by
  intro c₁ c₂ h
  obtain @⟨- | l, v, S, L, hT⟩ := h; · constructor
  rsuffices ⟨b, c, r⟩ : exists b, _ ∧ Reaches (TM1.step (tr M)) _ _
  · exact ⟨b, c, TransGen.head' rfl r⟩
  simp only [tr]
  generalize M l = N
  induction N using stmtStRec generalizing v S L hT with
  | run k s q IH => exact tr

Depends on / 依赖: Reaches, TM1.step, TM1.stepAux, TM2.stepAux, TransGen, TransGen.head, branch, generalize, generalizing, rsuffices, stepAux, stmtStRec, trNormal, tr_respects_aux
-/
theorem tr_respects : Respects (TM2.step M) (TM1.step (tr M)) TrCfg := by
  intro c₁ c₂ h
  obtain @⟨- | l, v, S, L, hT⟩ := h; · constructor
  rsuffices ⟨b, c, r⟩ : exists b, _ ∧ Reaches (TM1.step (tr M)) _ _
  · exact ⟨b, c, TransGen.head' rfl r⟩
  simp only [tr]
  generalize M l = N
  induction N using stmtStRec generalizing v S L hT with
  | run k s q IH => exact tr_respects_aux M hT s @IH
  | load a _ IH => exact IH _ hT
  | branch p q₁ q₂ IH₁ IH₂ =>
    unfold TM2.stepAux trNormal TM1.stepAux
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/12129): additional beta reduction needed
    beta_reduce
    cases p v <;> [exact IH₂ _ hT; exact IH₁ _ hT]
  | goto => exact ⟨_, ⟨_, hT⟩, ReflTransGen.refl⟩
  | halt => exact ⟨_, ⟨_, hT⟩, ReflTransGen.refl⟩

section
variable [Inhabited Λ] [Inhabited σ]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `trCfg_init` / 定理 `trCfg_init`

English:
theorem trCfg_init
  given: (k) (L : List (Γ k))
  statement: TrCfg (TM2.init k L)
  proof: by
  rw [(_ : TM1.init _ = _)]
  · refine ⟨ListBlank.mk (L.reverse.map fun a => update default k (some a)), fun k' => ?_⟩
    refine ListBlank.ext fun i => ?_
    rw [ListBlank.map_mk]; rw [ListBlank.nth_mk]; rw [List.getI_eq_getElem?_getD]; rw [List.map_map]
    have : ((proj k').f ∘ fun a => updat

中文:
定理 trCfg_init
  条件: (k) (L : 列表 (Γ k))
  结论: TrCfg (TM2.init k L)
  证明: by
  rw [(_ : TM1.init _ = _)]
  · refine ⟨ListBlank.mk (L.reverse.map fun a => update default k (some a)), fun k' => ?_⟩
    refine ListBlank.ext fun i => ?_
    rw [ListBlank.map_mk]; rw [ListBlank.nth_mk]; rw [List.getI_eq_getElem?_getD]; rw [List.map_map]
    have : ((proj k').f ∘ fun a => updat

Depends on / 依赖: L.reverse.map, List.getElem, List.getI_eq_getElem, List.map_map, ListBlank, ListBlank.ext, ListBlank.map_mk, ListBlank.mk, ListBlank.nth_mk, PointedMap, PointedMap.mk_val, TM1.init, _getD, _map, getElem, getI_eq_getElem, map_map, map_mk, mk_val, nth_mk
-/
theorem trCfg_init (k) (L : List (Γ k)) : TrCfg (TM2.init k L)
    (TM1.init (trInit k L) : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ) := by
  rw [(_ : TM1.init _ = _)]
  · refine ⟨ListBlank.mk (L.reverse.map fun a => update default k (some a)), fun k' => ?_⟩
    refine ListBlank.ext fun i => ?_
    rw [ListBlank.map_mk]; rw [ListBlank.nth_mk]; rw [List.getI_eq_getElem?_getD]; rw [List.map_map]
    have : ((proj k').f ∘ fun a => update (β := fun k => Option (Γ k)) default k (some a))
      = fun a => (proj k').f (update (β := fun k => Option (Γ k)) default k (some a)) := rfl
    rw [this]; rw [List.getElem?_map]; rw [proj]; rw [PointedMap.mk_val]
    by_cases h : k' = k
    · subst k'
      simp only [Function.update_self]
      rw [ListBlank.nth_mk]; rw [List.getI_eq_getElem?_getD]; rw [← List.map_reverse]; rw [List.getElem?_map]
    · simp only [Function.update_of_ne h]
      rw [ListBlank.nth_mk]; rw [List.getI_eq_getElem?_getD]; rw [List.map]; rw [List.reverse_nil]
      cases L.reverse[i]? <;> rfl
  · rw [trInit, TM1.init]
    congr <;> cases L.reverse <;> try rfl
    simp only [List.map_map, List.tail_cons, List.map]
    rfl

/--
theorem `tr_eval_dom` / 定理 `tr_eval_dom`

English:
theorem tr_eval_dom
  given: (k) (L : List (Γ k))
  proof: StateTransition.tr_eval_dom (tr_respects M) (trCfg_init k L)

中文:
定理 tr_eval_dom
  条件: (k) (L : 列表 (Γ k))
  证明: StateTransition.tr_eval_dom (tr_respects M) (trCfg_init k L)

Depends on / 依赖: StateTransition, StateTransition.tr_eval_dom, trCfg_init, tr_eval_dom, tr_respects
-/
theorem tr_eval_dom (k) (L : List (Γ k)) :
    (TM1.eval (tr M) (trInit k L)).Dom ↔ (TM2.eval M k L).Dom :=
  StateTransition.tr_eval_dom (tr_respects M) (trCfg_init k L)

/--
theorem `tr_eval` / 定理 `tr_eval`

English:
theorem tr_eval
  statement: (k) (L : List (Γ k)) {L₁ L₂} (H₁ : L₁ in TM1.eval (tr M) (trInit k L))
  proof: by
  obtain ⟨c₁, h₁, rfl⟩ := (Part.mem_map_iff _).1 H₁
  obtain ⟨c₂, h₂, rfl⟩ := (Part.mem_map_iff _).1 H₂
  obtain ⟨_, ⟨L', hT⟩, h₃⟩ := StateTransition.tr_eval (tr_respects M) (trCfg_init k L) h₂
  cases Part.mem_unique h₁ h₃
  exact ⟨_, L', by simp only [Tape.mk'_right₀], hT, rfl⟩

中文:
定理 tr_eval
  结论: (k) (L : 列表 (Γ k)) {L₁ L₂} (H₁ : L₁ in TM1.eval (tr M) (trInit k L))
  证明: by
  obtain ⟨c₁, h₁, rfl⟩ := (Part.mem_map_iff _).1 H₁
  obtain ⟨c₂, h₂, rfl⟩ := (Part.mem_map_iff _).1 H₂
  obtain ⟨_, ⟨L', hT⟩, h₃⟩ := StateTransition.tr_eval (tr_respects M) (trCfg_init k L) h₂
  cases Part.mem_unique h₁ h₃
  exact ⟨_, L', by simp only [Tape.mk'_right₀], hT, rfl⟩

Depends on / 依赖: Part.mem_map_iff, Part.mem_unique, StateTransition, StateTransition.tr_eval, Tape.mk, mem_map_iff, mem_unique, trCfg_init, tr_eval, tr_respects
-/
theorem tr_eval (k) (L : List (Γ k)) {L₁ L₂} (H₁ : L₁ in TM1.eval (tr M) (trInit k L))
    (H₂ : L₂ in TM2.eval M k L) :
    exists (S : forall k, List (Γ k)) (L' : ListBlank (forall k, Option (Γ k))),
      addBottom L' = L₁ ∧
        (forall k, L'.map (proj k) = ListBlank.mk ((S k).map some).reverse) ∧ S k = L₂ := by
  obtain ⟨c₁, h₁, rfl⟩ := (Part.mem_map_iff _).1 H₁
  obtain ⟨c₂, h₂, rfl⟩ := (Part.mem_map_iff _).1 H₂
  obtain ⟨_, ⟨L', hT⟩, h₃⟩ := StateTransition.tr_eval (tr_respects M) (trCfg_init k L) h₂
  cases Part.mem_unique h₁ h₃
  exact ⟨_, L', by simp only [Tape.mk'_right₀], hT, rfl⟩

end

section

variable [Inhabited Λ]

open scoped Classical in
/--
Definition of `trSupp` / `trSupp` 的定义

English:
definition trSupp
  signature: (S : Finset Λ)
  body: S.biUnion fun l => insert (normal l) (trStmts₁ (M l))

中文:
定义 trSupp
  签名: (S : 有限集 Λ)
  定义体: S.biUnion fun l => insert (normal l) (trStmts₁ (M l))

Depends on / 依赖: S.biUnion, biUnion, insert, normal
-/
noncomputable def trSupp (S : Finset Λ) : Finset (Λ' K Γ Λ σ) :=
  S.biUnion fun l => insert (normal l) (trStmts₁ (M l))

open scoped Classical in
/--
theorem `tr_supports` / 定理 `tr_supports`

English:
theorem tr_supports
  given: {S} (ss : TM2.Supports M S)
  statement: TM1.Supports (tr M) (trSupp M S)
  proof: ⟨Finset.mem_biUnion.2 ⟨_, ss.1, Finset.mem_insert.2 Or.inl rfl⟩, fun l' h => by
    suffices forall (q) (_ : TM2.SupportsStmt S q) (_ : forall x in trStmts₁ q, x in trSupp M S),
        TM1.SupportsStmt (trSupp M S) (trNormal q) ∧
        forall l' in trStmts₁ q, TM1.SupportsStmt (trSupp M S) (tr M 

中文:
定理 tr_supports
  条件: {S} (ss : TM2.Supports M S)
  结论: TM1.Supports (tr M) (trSupp M S)
  证明: ⟨Finset.mem_biUnion.2 ⟨_, ss.1, Finset.mem_insert.2 Or.inl rfl⟩, fun l' h => by
    suffices forall (q) (_ : TM2.SupportsStmt S q) (_ : forall x in trStmts₁ q, x in trSupp M S),
        TM1.SupportsStmt (trSupp M S) (trNormal q) ∧
        forall l' in trStmts₁ q, TM1.SupportsStmt (trSupp M S) (tr M 

Depends on / 依赖: Finset, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_insert_of_mem, Or.inl, SupportsStmt, TM1.SupportsStmt, TM2.SupportsStmt, mem_biUnion, mem_insert, mem_insert_of_mem, trNormal, trSupp
-/
theorem tr_supports {S} (ss : TM2.Supports M S) : TM1.Supports (tr M) (trSupp M S) :=
⟨Finset.mem_biUnion.2 ⟨_, ss.1, Finset.mem_insert.2 Or.inl rfl⟩, fun l' h => by
    suffices forall (q) (_ : TM2.SupportsStmt S q) (_ : forall x in trStmts₁ q, x in trSupp M S),
        TM1.SupportsStmt (trSupp M S) (trNormal q) ∧
        forall l' in trStmts₁ q, TM1.SupportsStmt (trSupp M S) (tr M l') by
      rcases Finset.mem_biUnion.1 h with ⟨l, lS, h⟩
      have :=
        this _ (ss.2 l lS) fun x hx => Finset.mem_biUnion.2 ⟨_, lS, Finset.mem_insert_of_mem hx⟩
      rcases Finset.mem_insert.1 h with (rfl | h) <;> [exact this.1; exact this.2 _ h]
    clear h l'
    refine stmtStRec ?_ ?_ ?_ ?_ ?_
    · intro _ s _ IH ss' sub -- stack op
      rw [TM2to1.supports_run] at ss'
      simp only [TM2to1.trStmts₁_run, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        at sub
      have hgo := sub _ (Or.inl <| Or.inl rfl)
      have hret := sub _ (Or.inl <| Or.inr rfl)
obtain ⟨IH₁, IH₂⟩ := IH ss' fun x hx => sub x Or.inr hx
      refine ⟨by simp only [trNormal_run, TM1.SupportsStmt]; intros; exact hgo, fun l h => ?_⟩
      rw [trStmts₁_run] at h
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        at h
      rcases h with (⟨rfl | rfl⟩ | h)
      · cases s
        · exact ⟨fun _ _ => hret, fun _ _ => hgo⟩
        · exact ⟨fun _ _ => hret, fun _ _ => hgo⟩
        · exact ⟨⟨fun _ _ => hret, fun _ _ => hret⟩, fun _ _ => hgo⟩
      · unfold TM1.SupportsStmt TM2to1.tr
        exact ⟨IH₁, fun _ _ => hret⟩
      · exact IH₂ _ h
    · intro _ _ IH ss' sub -- load
      unfold TM2to1.trStmts₁ at sub ⊢
      exact IH ss' sub
    · intro _ _ _ IH₁ IH₂ ss' sub -- branch
      unfold TM2to1.trStmts₁ at sub
obtain ⟨IH₁₁, IH₁₂⟩ := IH₁ ss'.1 fun x hx => sub x Finset.mem_union_left _ hx
obtain ⟨IH₂₁, IH₂₂⟩ := IH₂ ss'.2 fun x hx => sub x Finset.mem_union_right _ hx
      refine ⟨⟨IH₁₁, IH₂₁⟩, fun l h => ?_⟩
      rw [trStmts₁] at h
      rcases Finset.mem_union.1 h with (h | h) <;> [exact IH₁₂ _ h; exact IH₂₂ _ h]
    · intro _ ss' _ -- goto
      simp only [trStmts₁, Finset.notMem_empty]; refine ⟨?_, fun _ => False.elim⟩
      exact fun _ v => Finset.mem_biUnion.2 ⟨_, ss' v, Finset.mem_insert_self _ _⟩
    · intro _ _ -- halt
      simp only [trStmts₁, Finset.notMem_empty]
      exact ⟨trivial, fun _ => False.elim⟩⟩

end

end TM2to1

end Turing
