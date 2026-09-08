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
variable (Γ : K → Type*)

-- Type of stack elements
variable (Λ : Type*)

-- Type of function labels
variable (σ : Type*)

-- Type of variable settings
/-- The TM2 model removes the tape entirely from the TM1 model,
  replacing it with an arbitrary (finite) collection of stacks.
  The operation `push` puts an element on one of the stacks,
  and `pop` removes an element from a stack (and modifies the
  internal state based on the result). `peek` modifies the
  internal state but does not remove an element. -/
/-
**Turing.TM2.Stmt** 是 Mathlib 中的一个归纳类型，位于命名空间 `Turing.TM2`。
形式化陈述：{K : Type u_1} → (K → Type u_2) → Type u_3 → Type u_4 → Type (max (max (ma
x u_1 u_2) u_3) u_4)
参数：K → Type u_2；max (max (max u_1 u_2) u_3) u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The TM2 model removes the tape entirely from the TM1 model,
  replacing it with an arbitrary (finite) collection of stacks.
  The operation `push` puts an element on one of the stacks,
  and `pop` removes an element from a stack (and modifies the
  internal state based on the result). `peek` modifies the
  internal state but does not remove an element.
-/
inductive Stmt
  | push : ∀ k, (σ → Γ k) → Stmt → Stmt
  | peek : ∀ k, (σ → Option (Γ k) → σ) → Stmt → Stmt
  | pop : ∀ k, (σ → Option (Γ k) → σ) → Stmt → Stmt
  | load : (σ → σ) → Stmt → Stmt
  | branch : (σ → Bool) → Stmt → Stmt → Stmt
  | goto : (σ → Λ) → Stmt
  | halt : Stmt

open Stmt
/-
**Turing.TM2.Stmt.inhabited** 是 Mathlib 中的一个定义，位于命名空间 `Turing.TM2.Stmt`。
形式化陈述：{K : Type u_1} → (Γ : K → Type u_2) → (Λ : Type u_3) → (σ : Type u_4) → In
habited (Turing.TM2.Stmt Γ Λ σ)
参数：Γ : K → Type u_2；Λ : Type u_3；σ : Type u_4；Turing.TM2.Stmt Γ Λ σ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Stmt.inhabited : Inhabited (Stmt Γ Λ σ) :=
  ⟨halt⟩

/-- A configuration in the TM2 model is a label (or `none` for the halt state), the state of
local variables, and the stacks. (Note that the stacks are not `ListBlank`s, they have a definite
size.) -/
/-
**Turing.TM2.Cfg** 是 Mathlib 中的一个归纳类型，位于命名空间 `Turing.TM2`。
形式化陈述：{K : Type u_1} → (K → Type u_2) → Type u_3 → Type u_4 → Type (max (max (ma
x u_1 u_2) u_3) u_4)
参数：K → Type u_2；max (max (max u_1 u_2) u_3) u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A configuration in the TM2 model is a label (or `none` for the halt state), the 
state of
local variables, and the stacks. (Note that the stacks are not `ListBlank`s, the
y have a definite
size.)
-/
structure Cfg where
  /-- The current label to run (or `none` for the halting state) -/
  l : Option Λ
  /-- The internal state -/
  var : σ
  /-- The (finite) collection of internal stacks -/
  stk : ∀ k, List (Γ k)
/-
**Turing.TM2.Cfg.inhabited** 是 Mathlib 中的一个定义，位于命名空间 `Turing.TM2.Cfg`。
形式化陈述：{K : Type u_1} → (Γ : K → Type u_2) → (Λ : Type u_3) → (σ : Type u_4) → [I
nhabited σ] → Inhabited (Turing.TM2.Cfg Γ Λ σ)
参数：Γ : K → Type u_2；Λ : Type u_3；σ : Type u_4；Turing.TM2.Cfg Γ Λ σ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Cfg.inhabited [Inhabited σ] : Inhabited (Cfg Γ Λ σ) :=
  ⟨⟨default, default, default⟩⟩

variable {Γ Λ σ}

section
variable [DecidableEq K]

/-- The step function for the TM2 model. -/
/-
**Turing.TM2.stepAux** 是 Mathlib 中的一个定义，位于命名空间 `Turing.TM2`。
形式化陈述：{K : Type u_1} →   {Γ : K → Type u_2} →     {Λ : Type u_3} →       {σ : Ty
pe u_4} → [DecidableEq K] → Turing.TM2.Stmt Γ Λ σ → σ → ((k : K) → List (Γ k)) →
 Turing.TM2.Cfg Γ Λ σ
参数：(k : K) → List (Γ k)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The step function for the TM2 model.
-/
def stepAux : Stmt Γ Λ σ → σ → (∀ k, List (Γ k)) → Cfg Γ Λ σ
  | push k f q, v, S => stepAux q v (update S k (f v :: S k))
  | peek k f q, v, S => stepAux q (f v (S k).head?) S
  | pop k f q, v, S => stepAux q (f v (S k).head?) (update S k (S k).tail)
  | load a q, v, S => stepAux q (a v) S
  | branch f q₁ q₂, v, S => cond (f v) (stepAux q₁ v S) (stepAux q₂ v S)
  | goto f, v, S => ⟨some (f v), v, S⟩
  | halt, v, S => ⟨none, v, S⟩

/-- The step function for the TM2 model. -/
/-
**Turing.TM2.step** 是 Mathlib 中的一个定义，位于命名空间 `Turing.TM2`。
形式化陈述：{K : Type u_1} →   {Γ : K → Type u_2} →     {Λ : Type u_3} →       {σ : Ty
pe u_4} →         [DecidableEq K] → (Λ → Turing.TM2.Stmt Γ Λ σ) → Turing.TM2.Cfg
 Γ Λ σ → Option (Turing.TM2.Cfg Γ Λ σ)
参数：Λ → Turing.TM2.Stmt Γ Λ σ；Turing.TM2.Cfg Γ Λ σ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The step function for the TM2 model.
-/
def step (M : Λ → Stmt Γ Λ σ) : Cfg Γ Λ σ → Option (Cfg Γ Λ σ)
  | ⟨none, _, _⟩ => none
  | ⟨some l, v, S⟩ => some (stepAux (M l) v S)

attribute [simp] stepAux.eq_1 stepAux.eq_2 stepAux.eq_3
  stepAux.eq_4 stepAux.eq_5 stepAux.eq_6 stepAux.eq_7 step.eq_1 step.eq_2

/-- The (reflexive) reachability relation for the TM2 model. -/
/-
**Turing.TM2.Reaches** 是 Mathlib 中的一个定义，位于命名空间 `Turing.TM2`。
形式化陈述：Reaches (M : Λ -> Stmt Γ Λ σ) : Cfg Γ Λ σ -> Cfg Γ Λ σ -> Prop
参数：M : Λ -> Stmt Γ Λ σ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (reflexive) reachability relation for the TM2 model.
-/
def Reaches (M : Λ → Stmt Γ Λ σ) : Cfg Γ Λ σ → Cfg Γ Λ σ → Prop :=
  ReflTransGen fun a b ↦ b ∈ step M a

end

/-- Given a set `S` of states, `SupportsStmt S q` means that `q` only jumps to states in `S`. -/
/-
**Turing.TM2.SupportsStmt** 是 Mathlib 中的一个定义，位于命名空间 `Turing.TM2`。
形式化陈述：{K : Type u_1} → {Γ : K → Type u_2} → {Λ : Type u_3} → {σ : Type u_4} → Fi
nset Λ → Turing.TM2.Stmt Γ Λ σ → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a set `S` of states, `SupportsStmt S q` means that `q` only jumps to state
s in `S`.
-/
def SupportsStmt (S : Finset Λ) : Stmt Γ Λ σ → Prop
  | push _ _ q => SupportsStmt S q
  | peek _ _ q => SupportsStmt S q
  | pop _ _ q => SupportsStmt S q
  | load _ q => SupportsStmt S q
  | branch _ q₁ q₂ => SupportsStmt S q₁ ∧ SupportsStmt S q₂
  | goto l => ∀ v, l v ∈ S
  | halt => True

section

open scoped Classical in
/-- The set of subtree statements in a statement. -/
/-
**Turing.TM2.stmts** 是 Mathlib 中的一个定义，位于命名空间 `Turing.TM2`。
形式化陈述：stmts (M : Λ -> Stmt Γ Λ σ) (S : Finset Λ) : Finset (Option (Stmt Γ Λ σ))
参数：M : Λ -> Stmt Γ Λ σ；S : Finset Λ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of subtree statements in a statement.
-/
noncomputable def stmts₁ : Stmt Γ Λ σ → Finset (Stmt Γ Λ σ)
  | Q@(push _ _ q) => insert Q (stmts₁ q)
  | Q@(peek _ _ q) => insert Q (stmts₁ q)
  | Q@(pop _ _ q) => insert Q (stmts₁ q)
  | Q@(load _ q) => insert Q (stmts₁ q)
  | Q@(branch _ q₁ q₂) => insert Q (stmts₁ q₁ ∪ stmts₁ q₂)
  | Q@(goto _) => {Q}
  | Q@halt => {Q}
/-
**Turing.TM2.stmts** 是 Mathlib 中的一个定义，位于命名空间 `Turing.TM2`。
形式化陈述：stmts (M : Λ -> Stmt Γ Λ σ) (S : Finset Λ) : Finset (Option (Stmt Γ Λ σ))
参数：M : Λ -> Stmt Γ Λ σ；S : Finset Λ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem stmts₁_self {q : Stmt Γ Λ σ} : q ∈ stmts₁ q := by
  cases q <;> simp only [Finset.mem_insert_self, Finset.mem_singleton_self, stmts₁]
/-
**Turing.TM2.stmts** 是 Mathlib 中的一个定义，位于命名空间 `Turing.TM2`。
形式化陈述：stmts (M : Λ -> Stmt Γ Λ σ) (S : Finset Λ) : Finset (Option (Stmt Γ Λ σ))
参数：M : Λ -> Stmt Γ Λ σ；S : Finset Λ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem stmts₁_trans {q₁ q₂ : Stmt Γ Λ σ} : q₁ ∈ stmts₁ q₂ → stmts₁ q₁ ⊆ stmts₁ q₂ := by
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
/-
**Turing.TM2.stmts** 是 Mathlib 中的一个定义，位于命名空间 `Turing.TM2`。
形式化陈述：stmts (M : Λ -> Stmt Γ Λ σ) (S : Finset Λ) : Finset (Option (Stmt Γ Λ σ))
参数：M : Λ -> Stmt Γ Λ σ；S : Finset Λ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem stmts₁_supportsStmt_mono {S : Finset Λ} {q₁ q₂ : Stmt Γ Λ σ} (h : q₁ ∈ stmts₁ q₂)
    (hs : SupportsStmt S q₂) : SupportsStmt S q₁ := by
  induction q₂ with
    simp only [stmts₁, SupportsStmt, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
      at h hs
  | branch f q₁ q₂ IH₁ IH₂ => rcases h with (rfl | h | h); exacts [hs, IH₁ h hs.1, IH₂ h hs.2]
  | goto l => subst h; exact hs
  | halt => subst h; trivial
  | load _ _ IH | _ _ _ _ IH => rcases h with (rfl | h) <;> [exact hs; exact IH h hs]

open scoped Classical in
/-- The set of statements accessible from initial set `S` of labels. -/
/-
**Turing.TM2.stmts** 是 Mathlib 中的一个定义，位于命名空间 `Turing.TM2`。
形式化陈述：stmts (M : Λ -> Stmt Γ Λ σ) (S : Finset Λ) : Finset (Option (Stmt Γ Λ σ))
参数：M : Λ -> Stmt Γ Λ σ；S : Finset Λ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of statements accessible from initial set `S` of labels.
-/
noncomputable def stmts (M : Λ → Stmt Γ Λ σ) (S : Finset Λ) : Finset (Option (Stmt Γ Λ σ)) :=
  Finset.insertNone (S.biUnion fun q ↦ stmts₁ (M q))
/-
**Turing.TM2.stmts_trans** 是 Mathlib 中的一个定理，位于命名空间 `Turing.TM2`。
形式化陈述：stmts_trans {M : Λ -> Stmt Γ Λ σ} {S : Finset Λ} {q₁ q₂ : Stmt Γ Λ σ} (h₁ 
: q₁ in stmts₁ q₂) : some q₂ in stmts M S -> some q₁ in stmts M S
参数：h₁ : q₁ in stmts₁ q₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `Turing.TM2.stmts₁_trans`：stmts₁_trans {q₁ q₂ : Stmt Γ Λ σ} : q₁ in stmts
₁ q₂ -> stmts₁ q₁ subseteq stmts₁ q₂
-/
theorem stmts_trans {M : Λ → Stmt Γ Λ σ} {S : Finset Λ} {q₁ q₂ : Stmt Γ Λ σ} (h₁ : q₁ ∈ stmts₁ q₂) :
    some q₂ ∈ stmts M S → some q₁ ∈ stmts M S := by
  simp only [stmts, Finset.mem_insertNone, Finset.mem_biUnion, Option.mem_def, Option.some.injEq,
    forall_eq', exists_imp, and_imp]
  exact fun l ls h₂ ↦ ⟨_, ls, stmts₁_trans h₂ h₁⟩

end

variable [Inhabited Λ]

/-- Given a TM2 machine `M` and a set `S` of states, `Supports M S` means that all states in
`S` jump only to other states in `S`. -/
/-
**Turing.TM2.Supports** 是 Mathlib 中的一个定义，位于命名空间 `Turing.TM2`。
形式化陈述：Supports (M : Λ -> Stmt Γ Λ σ) (S : Finset Λ)
参数：M : Λ -> Stmt Γ Λ σ；S : Finset Λ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a TM2 machine `M` and a set `S` of states, `Supports M S` means that all s
tates in
`S` jump only to other states in `S`.
-/
def Supports (M : Λ → Stmt Γ Λ σ) (S : Finset Λ) :=
  default ∈ S ∧ ∀ q ∈ S, SupportsStmt S (M q)
/-
**Turing.TM2.stmts_supportsStmt** 是 Mathlib 中的一个定理，位于命名空间 `Turing.TM2`。
形式化陈述：stmts_supportsStmt {M : Λ -> Stmt Γ Λ σ} {S : Finset Λ} {q : Stmt Γ Λ σ} (
ss : Supports M S) : some q in stmts M S -> SupportsStmt S q
参数：ss : Supports M S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `Turing.TM2.stmts₁_supportsStmt_mono`：stmts₁_supportsStmt_mono {S : Finse
t Λ} {q₁ q₂ : Stmt Γ Λ σ} (h : q₁ in stmts₁ q₂) (hs : SupportsStmt S q₂) : Suppo
rtsStmt S q₁
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem stmts_supportsStmt {M : Λ → Stmt Γ Λ σ} {S : Finset Λ} {q : Stmt Γ Λ σ}
    (ss : Supports M S) : some q ∈ stmts M S → SupportsStmt S q := by
  simp only [stmts, Finset.mem_insertNone, Finset.mem_biUnion, Option.mem_def, Option.some.injEq,
    forall_eq', exists_imp, and_imp]
  exact fun l ls h ↦ stmts₁_supportsStmt_mono h (ss.2 _ ls)

variable [DecidableEq K]
/-
**Turing.TM2.step_supports** 是 Mathlib 中的一个定理，位于命名空间 `Turing.TM2`。
形式化陈述：step_supports (M : Λ -> Stmt Γ Λ σ) {S : Finset Λ} (ss : Supports M S) : f
orall {c c' : Cfg Γ Λ σ}, c' in step M c -> c.l in Finset.insertNone S -> c'.l i
n Finset.insertNone S | ⟨some l₁, v, T⟩, c', h₁, h₂ => by replace h₂
参数：M : Λ -> Stmt Γ Λ σ；ss : Supports M S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.some_mem_insertNone`：some_mem_insertNone {s : Finset α} {a : α} :
 some a in insertNone s ↔ a in s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Turing.TM2.stepAux.eq_def`：∀ {K : Type u_1} {Γ : K → Type u_2} {Λ : Type
 u_3} {σ : Type u_4} [inst : DecidableEq K] (x : Turing.TM2.Stmt Γ Λ σ)   (x_1 :
 σ) (x_2 : (k :…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.mem_cons_self`：mem_cons_self (a : α) (s : Multiset α) : a in a 
::ₘ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
-/
theorem step_supports (M : Λ → Stmt Γ Λ σ) {S : Finset Λ} (ss : Supports M S) :
    ∀ {c c' : Cfg Γ Λ σ}, c' ∈ step M c → c.l ∈ Finset.insertNone S → c'.l ∈ Finset.insertNone S
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

/-- The initial state of the TM2 model. The input is provided on a designated stack. -/
/-
**Turing.TM2.init** 是 Mathlib 中的一个定义，位于命名空间 `Turing.TM2`。
形式化陈述：init (k : K) (L : List (Γ k)) : Cfg Γ Λ σ
参数：k : K；L : List (Γ k)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The initial state of the TM2 model. The input is provided on a designated stack.
-/
def init (k : K) (L : List (Γ k)) : Cfg Γ Λ σ :=
  ⟨some default, default, update (fun _ ↦ []) k L⟩

/-- Evaluates a TM2 program to completion, with the output on the same stack as the input. -/
/-
**Turing.TM2.eval** 是 Mathlib 中的一个定义，位于命名空间 `Turing.TM2`。
形式化陈述：eval (M : Λ -> Stmt Γ Λ σ) (k : K) (L : List (Γ k)) : Part (List (Γ k))
参数：M : Λ -> Stmt Γ Λ σ；k : K；L : List (Γ k)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluates a TM2 program to completion, with the output on the same stack as the 
input.
-/
def eval (M : Λ → Stmt Γ Λ σ) (k : K) (L : List (Γ k)) : Part (List (Γ k)) :=
  (StateTransition.eval (step M) (init k L)).map fun c ↦ c.stk k

end TM2

/-!
## TM2 emulator in TM1

To prove that TM2 computable functions are TM1 computable, we need to reduce each TM2 program to a
TM1 program. So suppose a TM2 program is given. This program has to maintain a whole collection of
stacks, but we have only one tape, so we must "multiplex" them all together. Pictorially, if stack
1 contains `[a, b]` and stack 2 contains `[c, d, e, f]` then the tape looks like this:

```
bottom:  ... | _ | T | _ | _ | _ | _ | ...
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
/-
**Turing.TM2to1.stk_nth_val** 是 Mathlib 中的一个定理，位于命名空间 `Turing.TM2to1`。
形式化陈述：stk_nth_val {K : Type*} {Γ : K -> Type*} {L : ListBlank (forall k, Option 
(Γ k))} {k S} (n) (hL : ListBlank.map (proj k) L = ListBlank.mk (List.map some S
).reverse) : L.nth n k = S.reverse[n]?
参数：forall k, Option (Γ k)；n；hL : ListBlank.map (proj k) L = ListBlank.mk (List.m
ap some S).reverse。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Turing.proj_map_nth`：proj_map_nth {ι : Type*} {Γ : ι -> Type*} [forall i
, Inhabited (Γ i)] (i : ι) (L n) : (ListBlank.map (@proj ι Γ _ i) L).nth n = L.n
th n i
· 使用定理 `List.map_reverse`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : List 
α}, List.map f l.reverse = (List.map f l).reverse
· 使用定理 `Turing.ListBlank.nth_mk`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (l : List
 Γ) (n : ℕ), (Turing.ListBlank.mk l).nth n = l.getI n
· 使用定理 `List.getI_eq_getElem?_getD`：∀ {α : Type u} (l : List α) [inst : Inhabite
d α] (n : ℕ), l.getI n = l[n]?.getD default
· 使用定理 `List.getElem?_map`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : List
 α} {i : ℕ}, (List.map f l)[i]? = Option.map f l[i]?
-/
theorem stk_nth_val {K : Type*} {Γ : K → Type*} {L : ListBlank (∀ k, Option (Γ k))} {k S} (n)
    (hL : ListBlank.map (proj k) L = ListBlank.mk (List.map some S).reverse) :
    L.nth n k = S.reverse[n]? := by
  rw [← proj_map_nth, hL, ← List.map_reverse, ListBlank.nth_mk,
    List.getI_eq_getElem?_getD, List.getElem?_map]
  cases S.reverse[n]? <;> rfl

variable (K : Type*)
variable (Γ : K → Type*)
variable {Λ σ : Type*}

/-- The alphabet of the TM2 simulator on TM1 is a marker for the stack bottom,
plus a vector of stack elements for each stack, or none if the stack does not extend this far. -/
/-
**Turing.TM2to1.** 是 Mathlib 中的一个定义，位于命名空间 `Turing.TM2to1`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The alphabet of the TM2 simulator on TM1 is a marker for the stack bottom,
plus a vector of stack elements for each stack, or none if the stack does not ex
tend this far.
-/
def Γ' :=
  Bool × ∀ k, Option (Γ k)

variable {K Γ}
/-
**Turing.TM2to1.** 是 Mathlib 中的一个实例，位于命名空间 `Turing.TM2to1`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Γ'.inhabited : Inhabited (Γ' K Γ) :=
  ⟨⟨false, fun _ ↦ none⟩⟩
/-
**Turing.TM2to1.** 是 Mathlib 中的一个实例，位于命名空间 `Turing.TM2to1`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Γ'.fintype [DecidableEq K] [Fintype K] [∀ k, Fintype (Γ k)] : Fintype (Γ' K Γ) :=
  instFintypeProd _ _

/-- The bottom marker is fixed throughout the calculation, so we use the `addBottom` function
to express the program state in terms of a tape with only the stacks themselves. -/
/-
**Turing.TM2to1.addBottom** 是 Mathlib 中的一个定义，位于命名空间 `Turing.TM2to1`。
形式化陈述：addBottom (L : ListBlank (forall k, Option (Γ k))) : ListBlank (Γ' K Γ)
参数：L : ListBlank (forall k, Option (Γ k))。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bottom marker is fixed throughout the calculation, so we use the `addBottom`
 function
to express the program state in terms of a tape with only the stacks themselves.
-/
def addBottom (L : ListBlank (∀ k, Option (Γ k))) : ListBlank (Γ' K Γ) :=
  ListBlank.cons (true, L.head) (L.tail.map ⟨Prod.mk false, rfl⟩)

set_option backward.isDefEq.respectTransparency false in
/-
**Turing.TM2to1.addBottom_map** 是 Mathlib 中的一个定理，位于命名空间 `Turing.TM2to1`。
形式化陈述：addBottom_map (L : ListBlank (forall k, Option (Γ k))) : (addBottom L).map
 ⟨Prod.snd, by rfl⟩ = L
参数：L : ListBlank (forall k, Option (Γ k))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Turing.ListBlank.map_cons`：∀ {Γ : Type u_1} {Γ' : Type u_2} [inst : Inha
bited Γ] [inst_1 : Inhabited Γ'] (f : Turing.PointedMap Γ Γ')   (l : Turing.List
Blank Γ) (a : Γ…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Turing.ListBlank.induction_on`：∀ {Γ : Type u_1} [inst : Inhabited Γ] {p 
: Turing.ListBlank Γ → Prop} (q : Turing.ListBlank Γ),   (∀ (a : List Γ), p (Tur
ing.ListBlank.mk a)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `List.map_id_fun`：∀ {α : Type u_1}, List.map id = id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Turing.ListBlank.cons_head_tail`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (
l : Turing.ListBlank Γ), Turing.ListBlank.cons l.head l.tail = l
-/
theorem addBottom_map (L : ListBlank (∀ k, Option (Γ k))) :
    (addBottom L).map ⟨Prod.snd, by rfl⟩ = L := by
  simp only [addBottom, ListBlank.map_cons]
  convert! ListBlank.cons_head_tail L
  generalize ListBlank.tail L = L'
  refine L'.induction_on fun l ↦ ?_; simp

set_option backward.isDefEq.respectTransparency false in
/-
**Turing.TM2to1.addBottom_modifyNth** 是 Mathlib 中的一个定理，位于命名空间 `Turing.TM2to1`。
形式化陈述：addBottom_modifyNth (f : (forall k, Option (Γ k)) -> forall k, Option (Γ k
)) (L : ListBlank (forall k, Option (Γ k))) (n : Nat) : (addBottom L).modifyNth 
(fun a => (a.1, f a.2)) n = addBottom (L.modifyNth f n)
参数：f : (forall k, Option (Γ k)) -> forall k, Option (Γ k)；L : ListBlank (forall 
k, Option (Γ k))；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Turing.ListBlank.head_cons`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (a : Γ
) (l : Turing.ListBlank Γ), (Turing.ListBlank.cons a l).head = a
· 使用定理 `Turing.ListBlank.tail_cons`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (a : Γ
) (l : Turing.ListBlank Γ), (Turing.ListBlank.cons a l).tail = l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Turing.ListBlank.map_modifyNth`：∀ {Γ : Type u_1} {Γ' : Type u_2} [inst :
 Inhabited Γ] [inst_1 : Inhabited Γ'] (F : Turing.PointedMap Γ Γ') (f : Γ → Γ)  
 (f' : Γ' → Γ'),   (…
-/
theorem addBottom_modifyNth (f : (∀ k, Option (Γ k)) → ∀ k, Option (Γ k))
    (L : ListBlank (∀ k, Option (Γ k))) (n : ℕ) :
    (addBottom L).modifyNth (fun a ↦ (a.1, f a.2)) n = addBottom (L.modifyNth f n) := by
  cases n <;>
    simp only [addBottom, ListBlank.head_cons, ListBlank.modifyNth, ListBlank.tail_cons]
  congr; symm; apply ListBlank.map_modifyNth; intro; rfl

set_option backward.isDefEq.respectTransparency false in
/-
**Turing.TM2to1.addBottom_nth_snd** 是 Mathlib 中的一个定理，位于命名空间 `Turing.TM2to1`。
形式化陈述：addBottom_nth_snd (L : ListBlank (forall k, Option (Γ k))) (n : Nat) : ((a
ddBottom L).nth n).2 = L.nth n
参数：L : ListBlank (forall k, Option (Γ k))；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Turing.TM2to1.addBottom_map`：addBottom_map (L : ListBlank (forall k, Opt
ion (Γ k))) : (addBottom L).map ⟨Prod.snd, by rfl⟩ = L
· 使用定理 `Turing.ListBlank.nth_map`：∀ {Γ : Type u_1} {Γ' : Type u_2} [inst : Inhab
ited Γ] [inst_1 : Inhabited Γ'] (f : Turing.PointedMap Γ Γ')   (l : Turing.ListB
lank Γ) (n : ℕ…
-/
theorem addBottom_nth_snd (L : ListBlank (∀ k, Option (Γ k))) (n : ℕ) :
    ((addBottom L).nth n).2 = L.nth n := by
  conv => rhs; rw [← addBottom_map L, ListBlank.nth_map]

set_option backward.isDefEq.respectTransparency false in
/-
**Turing.TM2to1.addBottom_nth_succ_fst** 是 Mathlib 中的一个定理，位于命名空间 `Turing.TM2to1`
。
形式化陈述：addBottom_nth_succ_fst (L : ListBlank (forall k, Option (Γ k))) (n : Nat) 
: ((addBottom L).nth (n + 1)).1 = false
参数：L : ListBlank (forall k, Option (Γ k))；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Turing.ListBlank.nth_succ`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (l : Tu
ring.ListBlank Γ) (n : ℕ), l.nth (n + 1) = l.tail.nth n
· 使用定理 `Turing.TM2to1.addBottom.eq_1`：∀ {K : Type u_1} {Γ : K → Type u_2} (L : T
uring.ListBlank ((k : K) → Option (Γ k))),   Turing.TM2to1.addBottom L =     Tur
ing.ListBlank.cons…
· 使用定理 `Turing.ListBlank.tail_cons`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (a : Γ
) (l : Turing.ListBlank Γ), (Turing.ListBlank.cons a l).tail = l
· 使用定理 `Turing.ListBlank.nth_map`：∀ {Γ : Type u_1} {Γ' : Type u_2} [inst : Inhab
ited Γ] [inst_1 : Inhabited Γ'] (f : Turing.PointedMap Γ Γ')   (l : Turing.ListB
lank Γ) (n : ℕ…
-/
theorem addBottom_nth_succ_fst (L : ListBlank (∀ k, Option (Γ k))) (n : ℕ) :
    ((addBottom L).nth (n + 1)).1 = false := by
  rw [ListBlank.nth_succ, addBottom, ListBlank.tail_cons, ListBlank.nth_map]

set_option backward.isDefEq.respectTransparency false in
/-
**Turing.TM2to1.addBottom_head_fst** 是 Mathlib 中的一个定理，位于命名空间 `Turing.TM2to1`。
形式化陈述：addBottom_head_fst (L : ListBlank (forall k, Option (Γ k))) : (addBottom L
).head.1 = true
参数：L : ListBlank (forall k, Option (Γ k))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Turing.TM2to1.addBottom.eq_1`：∀ {K : Type u_1} {Γ : K → Type u_2} (L : T
uring.ListBlank ((k : K) → Option (Γ k))),   Turing.TM2to1.addBottom L =     Tur
ing.ListBlank.cons…
· 使用定理 `Turing.ListBlank.head_cons`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (a : Γ
) (l : Turing.ListBlank Γ), (Turing.ListBlank.cons a l).head = a
-/
theorem addBottom_head_fst (L : ListBlank (∀ k, Option (Γ k))) : (addBottom L).head.1 = true := by
  rw [addBottom, ListBlank.head_cons]

variable (K Γ σ) in
/-- A stack action is a command that interacts with the top of a stack. Our default position
is at the bottom of all the stacks, so we have to hold on to this action while going to the end
to modify the stack. -/
/-
**Turing.TM2to1.StAct** 是 Mathlib 中的一个归纳类型，位于命名空间 `Turing.TM2to1`。
形式化陈述：(K : Type u_1) → (K → Type u_2) → Type u_4 → K → Type (max u_2 u_4)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A stack action is a command that interacts with the top of a stack. Our default 
position
is at the bottom of all the stacks, so we have to hold on to this action while g
oing to the end
to modify the stack.
-/
inductive StAct (k : K)
  | push : (σ → Γ k) → StAct k
  | peek : (σ → Option (Γ k) → σ) → StAct k
  | pop : (σ → Option (Γ k) → σ) → StAct k
/-
**Turing.TM2to1.StAct.inhabited** 是 Mathlib 中的一个定义，位于命名空间 `Turing.TM2to1.StAct`。
形式化陈述：{K : Type u_1} → {Γ : K → Type u_2} → {σ : Type u_4} → {k : K} → Inhabited
 (Turing.TM2to1.StAct K Γ σ k)
参数：Turing.TM2to1.StAct K Γ σ k。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance StAct.inhabited {k : K} : Inhabited (StAct K Γ σ k) :=
  ⟨StAct.peek fun s _ ↦ s⟩

section

open StAct

/-- The TM2 statement corresponding to a stack action. -/
/-
**Turing.TM2to1.stRun** 是 Mathlib 中的一个定义，位于命名空间 `Turing.TM2to1`。
形式化陈述：{K : Type u_1} →   {Γ : K → Type u_2} →     {Λ : Type u_3} →       {σ : Ty
pe u_4} → {k : K} → Turing.TM2to1.StAct K Γ σ k → Turing.TM2.Stmt Γ Λ σ → Turing
.TM2.Stmt Γ Λ σ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The TM2 statement corresponding to a stack action.
-/
def stRun {k : K} : StAct K Γ σ k → TM2.Stmt Γ Λ σ → TM2.Stmt Γ Λ σ
  | push f => TM2.Stmt.push k f
  | peek f => TM2.Stmt.peek k f
  | pop f => TM2.Stmt.pop k f

/-- The effect of a stack action on the local variables, given the value of the stack. -/
/-
**Turing.TM2to1.stVar** 是 Mathlib 中的一个定义，位于命名空间 `Turing.TM2to1`。
形式化陈述：{K : Type u_1} → {Γ : K → Type u_2} → {σ : Type u_4} → {k : K} → σ → List 
(Γ k) → Turing.TM2to1.StAct K Γ σ k → σ
参数：Γ k。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The effect of a stack action on the local variables, given the value of the stac
k.
-/
def stVar {k : K} (v : σ) (l : List (Γ k)) : StAct K Γ σ k → σ
  | push _ => v
  | peek f => f v l.head?
  | pop f => f v l.head?

/-- The effect of a stack action on the stack. -/
/-
**Turing.TM2to1.stWrite** 是 Mathlib 中的一个定义，位于命名空间 `Turing.TM2to1`。
形式化陈述：{K : Type u_1} →   {Γ : K → Type u_2} → {σ : Type u_4} → {k : K} → σ → Lis
t (Γ k) → Turing.TM2to1.StAct K Γ σ k → List (Γ k)
参数：Γ k；Γ k。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The effect of a stack action on the stack.
-/
def stWrite {k : K} (v : σ) (l : List (Γ k)) : StAct K Γ σ k → List (Γ k)
  | push f => f v :: l
  | peek _ => l
  | pop _ => l.tail

/-- We have partitioned the TM2 statements into "stack actions", which require going to the end
of the stack, and all other actions, which do not. This is a modified recursor which lumps the
stack actions into one. -/
@[elab_as_elim]
/-
**Turing.TM2to1.stmtStRec.** 是 Mathlib 中的一个定义，位于命名空间 `Turing.TM2to1`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We have partitioned the TM2 statements into "stack actions", which require going
 to the end
of the stack, and all other actions, which do not. This is a modified recursor w
hich lumps the
stack actions into one.
-/
def stmtStRec.{l} {motive : TM2.Stmt Γ Λ σ → Sort l}
    (run : ∀ (k) (s : StAct K Γ σ k) (q) (_ : motive q), motive (stRun s q))
    (load : ∀ (a q) (_ : motive q), motive (TM2.Stmt.load a q))
    (branch : ∀ (p q₁ q₂) (_ : motive q₁) (_ : motive q₂), motive (TM2.Stmt.branch p q₁ q₂))
    (goto : ∀ l, motive (TM2.Stmt.goto l)) (halt : motive TM2.Stmt.halt) : ∀ n, motive n
  | TM2.Stmt.push _ f q => run _ (push f) _ (stmtStRec run load branch goto halt q)
  | TM2.Stmt.peek _ f q => run _ (peek f) _ (stmtStRec run load branch goto halt q)
  | TM2.Stmt.pop _ f q => run _ (pop f) _ (stmtStRec run load branch goto halt q)
  | TM2.Stmt.load _ q => load _ _ (stmtStRec run load branch goto halt q)
  | TM2.Stmt.branch _ q₁ q₂ =>
    branch _ _ _ (stmtStRec run load branch goto halt q₁) (stmtStRec run load branch goto halt q₂)
  | TM2.Stmt.goto _ => goto _
  | TM2.Stmt.halt => halt
/-
**Turing.TM2to1.supports_run** 是 Mathlib 中的一个定理，位于命名空间 `Turing.TM2to1`。
形式化陈述：supports_run (S : Finset Λ) {k : K} (s : StAct K Γ σ k) (q : TM2.Stmt Γ Λ 
σ) : TM2.SupportsStmt S (stRun s q) ↔ TM2.SupportsStmt S q
参数：S : Finset Λ；s : StAct K Γ σ k；q : TM2.Stmt Γ Λ σ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem supports_run (S : Finset Λ) {k : K} (s : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ) :
    TM2.SupportsStmt S (stRun s q) ↔ TM2.SupportsStmt S q := by
  cases s <;> rfl

end

variable (K Γ Λ σ)

/-- The machine states of the TM2 emulator. We can either be in a normal state when waiting for the
next TM2 action, or we can be in the "go" and "return" states to go to the top of the stack and
return to the bottom, respectively. -/
/-
**Turing.TM2to1.** 是 Mathlib 中的一个归纳类型，位于命名空间 `Turing.TM2to1`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The machine states of the TM2 emulator. We can either be in a normal state when 
waiting for the
next TM2 action, or we can be in the "go" and "return" states to go to the top o
f the stack and
return to the bottom, respectively.
-/
inductive Λ'
  | normal : Λ → Λ'
  | go (k : K) : StAct K Γ σ k → TM2.Stmt Γ Λ σ → Λ'
  | ret : TM2.Stmt Γ Λ σ → Λ'

variable {K Γ Λ σ}

open Λ'
/-
**Turing.TM2to1.** 是 Mathlib 中的一个实例，位于命名空间 `Turing.TM2to1`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Λ'.inhabited [Inhabited Λ] : Inhabited (Λ' K Γ Λ σ) :=
  ⟨normal default⟩

open TM1.Stmt

section
variable [DecidableEq K]

/-- The program corresponding to state transitions at the end of a stack. Here we start out just
after the top of the stack, and should end just after the new top of the stack. -/
/-
**Turing.TM2to1.trStAct** 是 Mathlib 中的一个定义，位于命名空间 `Turing.TM2to1`。
形式化陈述：{K : Type u_1} →   {Γ : K → Type u_2} →     {Λ : Type u_3} →       {σ : Ty
pe u_4} →         [DecidableEq K] →           {k : K} →             Turing.TM1.S
tmt (Turing.TM2to1.Γ' K Γ) (Turing.TM2to1.Λ' K Γ Λ σ) σ →               Turing.T
M2to1.StAct K Γ σ k → Turing.TM1.Stmt (Turing.TM2to1.Γ' K Γ) (Turing.TM2to1.Λ' K
 Γ Λ σ) σ
参数：Turing.TM2to1.Γ' K Γ；Turing.TM2to1.Λ' K Γ Λ σ；Turing.TM2to1.Γ' K Γ；Turing.TM2
to1.Λ' K Γ Λ σ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The program corresponding to state transitions at the end of a stack. Here we st
art out just
after the top of the stack, and should end just after the new top of the stack.
-/
def trStAct {k : K} (q : TM1.Stmt (Γ' K Γ) (Λ' K Γ Λ σ) σ) :
    StAct K Γ σ k → TM1.Stmt (Γ' K Γ) (Λ' K Γ Λ σ) σ
  | StAct.push f => (write fun a s ↦ (a.1, update a.2 k <| some <| f s)) <| move Dir.right q
  | StAct.peek f => move Dir.left <| (load fun a s ↦ f s (a.2 k)) <| move Dir.right q
  | StAct.pop f =>
    branch (fun a _ ↦ a.1) (load (fun _ s ↦ f s none) q)
      (move Dir.left <|
        (load fun a s ↦ f s (a.2 k)) <| write (fun a _ ↦ (a.1, update a.2 k none)) q)

/-- The initial state for the TM2 emulator, given an initial TM2 state. All stacks start out empty
except for the input stack, and the stack bottom mark is set at the head. -/
/-
**Turing.TM2to1.trInit** 是 Mathlib 中的一个定义，位于命名空间 `Turing.TM2to1`。
形式化陈述：trInit (k : K) (L : List (Γ k)) : List (Γ' K Γ)
参数：k : K；L : List (Γ k)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The initial state for the TM2 emulator, given an initial TM2 state. All stacks s
tart out empty
except for the input stack, and the stack bottom mark is set at the head.
-/
def trInit (k : K) (L : List (Γ k)) : List (Γ' K Γ) :=
  let L' : List (Γ' K Γ) := L.reverse.map fun a ↦ (false, update (fun _ ↦ none) k (some a))
  (true, L'.headI.2) :: L'.tail
/-
**Turing.TM2to1.step_run** 是 Mathlib 中的一个定理，位于命名空间 `Turing.TM2to1`。
形式化陈述：∀ {K : Type u_1} {Γ : K → Type u_2} {Λ : Type u_3} {σ : Type u_4} [inst : 
DecidableEq K] {k : K}   (q : Turing.TM2.Stmt Γ Λ σ) (v : σ) (S : (k : K) → List
 (Γ k)) (s : Turing.TM2to1.StAct K Γ σ k),   Turing.TM2.stepAux (Turing.TM2to1.s
tRun s q) v S =     Turing.TM2.stepAux q (Turing.TM2to1.stVar v (S k) s) (Functi
on.update S k (Turing.TM2to1.stWrite v (S k) s))
参数：q : Turing.TM2.Stmt Γ Λ σ；v : σ；S : (k : K) → List (Γ k)；s : Turing.TM2to1.St
Act K Γ σ k；Turing.TM2to1.stRun s q；Turing.TM2to1.stVar v (S k) s；Function.updat
e S k (Turing.TM2to1.stWrite v (S k) s)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_eq_self`：update_eq_self (a : α) (f : forall a, β a) : up
date f a (f a) = f
-/
theorem step_run {k : K} (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) : ∀ s : StAct K Γ σ k,
    TM2.stepAux (stRun s q) v S = TM2.stepAux q (stVar v (S k) s) (update S k (stWrite v (S k) s))
  | StAct.push _ => rfl
  | StAct.peek f => by unfold stWrite; rw [Function.update_eq_self]; rfl
  | StAct.pop _ => rfl

end

/-- The translation of TM2 statements to TM1 statements. Regular actions have direct equivalents,
but stack actions are deferred by going to the corresponding `go` state, so that we can find the
appropriate stack top. -/
/-
**Turing.TM2to1.trNormal** 是 Mathlib 中的一个定义，位于命名空间 `Turing.TM2to1`。
形式化陈述：{K : Type u_1} →   {Γ : K → Type u_2} →     {Λ : Type u_3} →       {σ : Ty
pe u_4} → Turing.TM2.Stmt Γ Λ σ → Turing.TM1.Stmt (Turing.TM2to1.Γ' K Γ) (Turing
.TM2to1.Λ' K Γ Λ σ) σ
参数：Turing.TM2to1.Γ' K Γ；Turing.TM2to1.Λ' K Γ Λ σ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The translation of TM2 statements to TM1 statements. Regular actions have direct
 equivalents,
but stack actions are deferred by going to the corresponding `go` state, so that
 we can find the
appropriate stack top.
-/
def trNormal : TM2.Stmt Γ Λ σ → TM1.Stmt (Γ' K Γ) (Λ' K Γ Λ σ) σ
  | TM2.Stmt.push k f q => goto fun _ _ ↦ go k (StAct.push f) q
  | TM2.Stmt.peek k f q => goto fun _ _ ↦ go k (StAct.peek f) q
  | TM2.Stmt.pop k f q => goto fun _ _ ↦ go k (StAct.pop f) q
  | TM2.Stmt.load a q => load (fun _ ↦ a) (trNormal q)
  | TM2.Stmt.branch f q₁ q₂ => branch (fun _ ↦ f) (trNormal q₁) (trNormal q₂)
  | TM2.Stmt.goto l => goto fun _ s ↦ normal (l s)
  | TM2.Stmt.halt => halt
/-
**Turing.TM2to1.trNormal_run** 是 Mathlib 中的一个定理，位于命名空间 `Turing.TM2to1`。
形式化陈述：trNormal_run {k : K} (s : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ) : trNormal (
stRun s q) = goto fun _ _ => go k s q
参数：s : StAct K Γ σ k；q : TM2.Stmt Γ Λ σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem trNormal_run {k : K} (s : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ) :
    trNormal (stRun s q) = goto fun _ _ ↦ go k s q := by
  cases s <;> rfl

section

open scoped Classical in
/-- The set of machine states accessible from an initial TM2 statement. -/
/-
**Turing.TM2to1.trStmts** 是 Mathlib 中的一个定义，位于命名空间 `Turing.TM2to1`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of machine states accessible from an initial TM2 statement.
-/
noncomputable def trStmts₁ : TM2.Stmt Γ Λ σ → Finset (Λ' K Γ Λ σ)
  | TM2.Stmt.push k f q => {go k (StAct.push f) q, ret q} ∪ trStmts₁ q
  | TM2.Stmt.peek k f q => {go k (StAct.peek f) q, ret q} ∪ trStmts₁ q
  | TM2.Stmt.pop k f q => {go k (StAct.pop f) q, ret q} ∪ trStmts₁ q
  | TM2.Stmt.load _ q => trStmts₁ q
  | TM2.Stmt.branch _ q₁ q₂ => trStmts₁ q₁ ∪ trStmts₁ q₂
  | _ => ∅
/-
**Turing.TM2to1.trStmts** 是 Mathlib 中的一个定理，位于命名空间 `Turing.TM2to1`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trStmts₁_run {k : K} {s : StAct K Γ σ k} {q : TM2.Stmt Γ Λ σ} :
    open scoped Classical in
    trStmts₁ (stRun s q) = {go k s q, ret q} ∪ trStmts₁ q := by
  cases s <;> simp only [trStmts₁, stRun]
/-
**Turing.TM2to1.tr_respects_aux** 是 Mathlib 中的一个定理，位于命名空间 `Turing.TM2to1`。
形式化陈述：tr_respects_aux {q v T k} {S : forall k, List (Γ k)} (hT : forall k, ListB
lank.map (proj k) T = ListBlank.mk ((S k).map some).reverse) (o : StAct K Γ σ k)
 (IH : forall {v : σ} {S : forall k : K, List (Γ k)} {T : ListBlank (forall k, O
ption (Γ k))}, (forall k, ListBlank.map (proj k) T = ListBlank.mk ((S k).map som
e).reverse) -> exists b, TrCfg (TM2.stepAux q v S) b ∧ Reaches (TM1.step (tr M))
 (TM1.stepAux (trNormal q) v (Tape.mk' ∅ (addBottom T))) b) : exists b, TrCfg (T
M2.stepAux (stRun o q) v S
参数：Γ k；hT : forall k, ListBlank.map (proj k) T = ListBlank.mk ((S k).map some).r
everse；o : StAct K Γ σ k；IH : forall {v : σ} {S : forall k : K, List (Γ k)} {T :
 ListBlank (forall k, Option (Γ k))}, (forall k, ListBlank.map (proj k) T = List
Blank.mk ((S k).map some).reverse) -> exists b, TrCfg (TM2.stepAux q v S) b ∧ Re
aches (TM1.step (tr M)) (TM1.stepAux (trNormal q) v (Tape.mk' ∅ (addBottom T))) 
b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Turing.TM2to1.step_run`：∀ {K : Type u_1} {Γ : K → Type u_2} {Λ : Type u_
3} {σ : Type u_4} [inst : DecidableEq K] {k : K}   (q : Turing.TM2.Stmt Γ Λ σ) (
v : σ) (S : …
· 使用定理 `Turing.TM2to1.trNormal_run`：trNormal_run {k : K} (s : StAct K Γ σ k) (q 
: TM2.Stmt Γ Λ σ) : trNormal (stRun s q) = goto fun _ _ => go k s q
· 使用定理 `Turing.TM2to1.tr_respects_aux₁`：tr_respects_aux₁ {k} (o q v) {S : List (
Γ k)} {L : ListBlank (forall k, Option (Γ k))} (hL : L.map (proj k) = ListBlank.
mk (S.map some).reve…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Turing.TM2to1.tr_respects_aux₂`：tr_respects_aux₂ [DecidableEq K] {k : K}
 {q : TM1.Stmt (Γ' K Γ) (Λ' K Γ Λ σ) σ} {v : σ} {S : forall k, List (Γ k)} {L : 
ListBlank (forall k,…
· 使用定理 `StateTransition.Reaches₀.tail'`：∀ {σ : Type u_1} {f : σ → Option σ} {a b
 c : σ},   StateTransition.Reaches₀ f a b → c ∈ f b → StateTransition.Reaches₁ f
 a c
· 使用定理 `Relation.TransGen.to_reflTransGen`：to_reflTransGen {a b} : TransGen r a 
b -> ReflTransGen r a b
· 使用定理 `StateTransition.Reaches₀.trans`：∀ {σ : Type u_1} {f : σ → Option σ} {a b
 c : σ},   StateTransition.Reaches₀ f a b → StateTransition.Reaches₀ f b c → Sta
teTransition.Reaches…
· 使用定理 `StateTransition.Reaches₁.to₀`：∀ {σ : Type u_1} {f : σ → Option σ} {a b :
 σ}, StateTransition.Reaches₁ f a b → StateTransition.Reaches₀ f a b
· 使用定理 `Turing.TM1.stepAux.eq_5`：∀ {Γ : Type u_1} {Λ : Type u_2} {σ : Type u_3} 
[inst : Inhabited Γ] (x : σ) (x_1 : Turing.Tape Γ) (l : Γ → σ → Λ),   Turing.TM1
.stepAux (Tur…
· 使用定理 `cond.eq_1`：∀ {α : Sort u} (x y : α), (bif true then x else y) = x
· 使用定理 `Option.isNone.eq_2`：∀ {α : Type u_1}, none.isNone = true
· 使用定理 `List.getElem?_eq_none`：∀ {α : Type u_1} {l : List α} {i : ℕ}, l.length ≤
 i → l[i]? = none
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `List.length_reverse`：∀ {α : Type u_1} {as : List α}, as.reverse.length =
 as.length
· 使用定理 `Turing.TM2to1.stk_nth_val`：stk_nth_val {K : Type*} {Γ : K -> Type*} {L :
 ListBlank (forall k, Option (Γ k))} {k S} (n) (hL : ListBlank.map (proj k) L = 
ListBlank.mk (L…
· 使用定理 `Turing.TM2to1.addBottom_nth_snd`：addBottom_nth_snd (L : ListBlank (foral
l k, Option (Γ k))) (n : Nat) : ((addBottom L).nth n).2 = L.nth n
· 使用定理 `Turing.Tape.mk'_nth_nat`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (L R : Tu
ring.ListBlank Γ) (n : ℕ), (Turing.Tape.mk' L R).nth ↑n = R.nth n
· 使用定理 `Turing.Tape.move_right_n_head`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (T 
: Turing.Tape Γ) (i : ℕ),   ((Turing.Tape.move Turing.Dir.right)^[i] T).head = T
.nth ↑i
· 使用定理 `Turing.TM1.stepAux.eq_4`：∀ {Γ : Type u_1} {Λ : Type u_2} {σ : Type u_3} 
[inst : Inhabited Γ] (x : σ) (x_1 : Turing.Tape Γ) (p : Γ → σ → Bool)   (q₁ q₂ :
 Turing.TM1.S…
· 使用定理 `Turing.TM2to1.tr.eq_2`：∀ {K : Type u_1} {Γ : K → Type u_2} {Λ : Type u_3
} {σ : Type u_4} [inst : DecidableEq K] (M : Λ → Turing.TM2.Stmt Γ Λ σ)   (k : K
) (s : Turi…
· 使用定理 `Turing.TM2to1.tr_respects_aux₃`：tr_respects_aux₃ {q v} {L : ListBlank (f
orall k, Option (Γ k))} (n) : Reaches₀ (TM1.step (tr M)) ⟨some (ret q), v, (Tape
.move Dir.right)^[n]…
· 使用定理 `Relation.TransGen.head'`：head' (hab : r a b) (hbc : ReflTransGen r b c) 
: TransGen r a c
· 使用定理 `Turing.TM2to1.tr.eq_3`：∀ {K : Type u_1} {Γ : K → Type u_2} {Λ : Type u_3
} {σ : Type u_4} [inst : DecidableEq K] (M : Λ → Turing.TM2.Stmt Γ Λ σ)   (q : T
uring.TM2.S…
· 使用定理 `Turing.Tape.mk'_head`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (L R : Turin
g.ListBlank Γ), (Turing.Tape.mk' L R).head = R.head
· 使用定理 `Turing.TM2to1.addBottom_head_fst`：addBottom_head_fst (L : ListBlank (for
all k, Option (Γ k))) : (addBottom L).head.1 = true
-/
theorem tr_respects_aux₂ [DecidableEq K] {k : K} {q : TM1.Stmt (Γ' K Γ) (Λ' K Γ Λ σ) σ} {v : σ}
    {S : ∀ k, List (Γ k)} {L : ListBlank (∀ k, Option (Γ k))}
    (hL : ∀ k, L.map (proj k) = ListBlank.mk ((S k).map some).reverse) (o : StAct K Γ σ k) :
    let v' := stVar v (S k) o
    let Sk' := stWrite v (S k) o
    let S' := update S k Sk'
    ∃ L' : ListBlank (∀ k, Option (Γ k)),
      (∀ k, L'.map (proj k) = ListBlank.mk ((S' k).map some).reverse) ∧
        TM1.stepAux (trStAct q o) v
            ((Tape.move Dir.right)^[(S k).length] (Tape.mk' ∅ (addBottom L))) =
          TM1.stepAux q v' ((Tape.move Dir.right)^[(S' k).length] (Tape.mk' ∅ (addBottom L'))) := by
  simp only [Function.update_self]; cases o with simp only [stWrite, stVar, trStAct, TM1.stepAux]
  | push f =>
    have := Tape.write_move_right_n fun a : Γ' K Γ ↦ (a.1, update a.2 k (some (f v)))
    refine
      ⟨_, fun k' ↦ ?_, by
        -- Porting note: `rw [...]` to `erw [...]; rfl`.
        -- https://github.com/leanprover-community/mathlib4/issues/5164
        rw [Tape.move_right_n_head, List.length, Tape.mk'_nth_nat, this]
        erw [addBottom_modifyNth fun a ↦ update a k (some (f v))]
        rw [Nat.add_one, iterate_succ']
        rfl⟩
    refine ListBlank.ext fun i ↦ ?_
    rw [ListBlank.nth_map, ListBlank.nth_modifyNth, proj, PointedMap.mk_val]
    by_cases h' : k' = k
    · subst k'
      split_ifs with h
        <;> simp only [List.reverse_cons, Function.update_self, ListBlank.nth_mk, List.map]
      · rw [List.getI_eq_getElem _, List.getElem_append_right] <;>
        simp only [List.length_append, List.length_reverse, List.length_map, ← h,
          Nat.sub_self, List.length_singleton, List.getElem_singleton,
          le_refl, Nat.lt_succ_self]
      rw [← proj_map_nth, hL, ListBlank.nth_mk]
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
    rw [List.length_cons, iterate_succ', Function.comp, Tape.move_right_left,
      Tape.move_right_n_head, Tape.mk'_nth_nat, addBottom_nth_snd, stk_nth_val _ (hL k), e,
      List.reverse_cons, ← List.length_reverse, List.getElem?_concat_length]
    rfl
  | pop f =>
    rcases e : S k with - | ⟨hd, tl⟩
    · simp only [Tape.mk'_head, ListBlank.head_cons, Tape.move_left_mk', List.length,
        List.head?, iterate_zero_apply, List.tail_nil]
      rw [← e, Function.update_eq_self]
      exact ⟨L, hL, by rw [addBottom_head_fst, cond]⟩
    · refine
        ⟨_, fun k' ↦ ?_, by
          erw [List.length_cons, Tape.move_right_n_head, Tape.mk'_nth_nat, addBottom_nth_succ_fst,
            cond_false, iterate_succ', Function.comp, Tape.move_right_left, Tape.move_right_n_head,
            Tape.mk'_nth_nat, Tape.write_move_right_n fun a : Γ' K Γ ↦ (a.1, update a.2 k none),
            addBottom_modifyNth fun a ↦ update a k none, addBottom_nth_snd,
            stk_nth_val _ (hL k), e,
            show (List.cons hd tl).reverse[tl.length]? = some hd by
              rw [List.reverse_cons, ← List.length_reverse, List.getElem?_concat_length],
            List.head?, List.tail]⟩
      refine ListBlank.ext fun i ↦ ?_
      rw [ListBlank.nth_map, ListBlank.nth_modifyNth, proj, PointedMap.mk_val]
      by_cases h' : k' = k
      · subst k'
        split_ifs with h <;> simp only [Function.update_self, ListBlank.nth_mk, List.tail]
        · rw [List.getI_eq_default]
          · rfl
          rw [h, List.length_reverse, List.length_map]
        rw [← proj_map_nth, hL, ListBlank.nth_mk, e, List.map, List.reverse_cons]
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
variable (M : Λ → TM2.Stmt Γ Λ σ)

/-- The TM2 emulator machine states written as a TM1 program.
This handles the `go` and `ret` states, which shuttle to and from a stack top. -/
/-
**Turing.TM2to1.tr** 是 Mathlib 中的一个定义，位于命名空间 `Turing.TM2to1`。
形式化陈述：{K : Type u_1} →   {Γ : K → Type u_2} →     {Λ : Type u_3} →       {σ : Ty
pe u_4} →         [DecidableEq K] →           (Λ → Turing.TM2.Stmt Γ Λ σ) →     
        Turing.TM2to1.Λ' K Γ Λ σ → Turing.TM1.Stmt (Turing.TM2to1.Γ' K Γ) (Turin
g.TM2to1.Λ' K Γ Λ σ) σ
参数：Λ → Turing.TM2.Stmt Γ Λ σ；Turing.TM2to1.Γ' K Γ；Turing.TM2to1.Λ' K Γ Λ σ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The TM2 emulator machine states written as a TM1 program.
This handles the `go` and `ret` states, which shuttle to and from a stack top.
-/
def tr : Λ' K Γ Λ σ → TM1.Stmt (Γ' K Γ) (Λ' K Γ Λ σ) σ
  | normal q => trNormal (M q)
  | go k s q =>
    branch (fun a _ ↦ (a.2 k).isNone) (trStAct (goto fun _ _ ↦ ret q) s)
      (move Dir.right <| goto fun _ _ ↦ go k s q)
  | ret q => branch (fun a _ ↦ a.1) (trNormal q) (move Dir.left <| goto fun _ _ ↦ ret q)

/-- The relation between TM2 configurations and TM1 configurations of the TM2 emulator. -/
/-
**Turing.TM2to1.TrCfg** 是 Mathlib 中的一个归纳类型，位于命名空间 `Turing.TM2to1`。
形式化陈述：{K : Type u_1} →   {Γ : K → Type u_2} →     {Λ : Type u_3} →       {σ : Ty
pe u_4} → Turing.TM2.Cfg Γ Λ σ → Turing.TM1.Cfg (Turing.TM2to1.Γ' K Γ) (Turing.T
M2to1.Λ' K Γ Λ σ) σ → Prop
参数：Turing.TM2to1.Γ' K Γ；Turing.TM2to1.Λ' K Γ Λ σ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The relation between TM2 configurations and TM1 configurations of the TM2 emulat
or.
-/
inductive TrCfg : TM2.Cfg Γ Λ σ → TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ → Prop
  | mk {q : Option Λ} {v : σ} {S : ∀ k, List (Γ k)} (L : ListBlank (∀ k, Option (Γ k))) :
    (∀ k, L.map (proj k) = ListBlank.mk ((S k).map some).reverse) →
      TrCfg ⟨q, v, S⟩ ⟨q.map normal, v, Tape.mk' ∅ (addBottom L)⟩
/-
**Turing.TM2to1.tr_respects_aux** 是 Mathlib 中的一个定理，位于命名空间 `Turing.TM2to1`。
形式化陈述：tr_respects_aux {q v T k} {S : forall k, List (Γ k)} (hT : forall k, ListB
lank.map (proj k) T = ListBlank.mk ((S k).map some).reverse) (o : StAct K Γ σ k)
 (IH : forall {v : σ} {S : forall k : K, List (Γ k)} {T : ListBlank (forall k, O
ption (Γ k))}, (forall k, ListBlank.map (proj k) T = ListBlank.mk ((S k).map som
e).reverse) -> exists b, TrCfg (TM2.stepAux q v S) b ∧ Reaches (TM1.step (tr M))
 (TM1.stepAux (trNormal q) v (Tape.mk' ∅ (addBottom T))) b) : exists b, TrCfg (T
M2.stepAux (stRun o q) v S
参数：Γ k；hT : forall k, ListBlank.map (proj k) T = ListBlank.mk ((S k).map some).r
everse；o : StAct K Γ σ k；IH : forall {v : σ} {S : forall k : K, List (Γ k)} {T :
 ListBlank (forall k, Option (Γ k))}, (forall k, ListBlank.map (proj k) T = List
Blank.mk ((S k).map some).reverse) -> exists b, TrCfg (TM2.stepAux q v S) b ∧ Re
aches (TM1.step (tr M)) (TM1.stepAux (trNormal q) v (Tape.mk' ∅ (addBottom T))) 
b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Turing.TM2to1.step_run`：∀ {K : Type u_1} {Γ : K → Type u_2} {Λ : Type u_
3} {σ : Type u_4} [inst : DecidableEq K] {k : K}   (q : Turing.TM2.Stmt Γ Λ σ) (
v : σ) (S : …
· 使用定理 `Turing.TM2to1.trNormal_run`：trNormal_run {k : K} (s : StAct K Γ σ k) (q 
: TM2.Stmt Γ Λ σ) : trNormal (stRun s q) = goto fun _ _ => go k s q
· 使用定理 `Turing.TM2to1.tr_respects_aux₁`：tr_respects_aux₁ {k} (o q v) {S : List (
Γ k)} {L : ListBlank (forall k, Option (Γ k))} (hL : L.map (proj k) = ListBlank.
mk (S.map some).reve…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Turing.TM2to1.tr_respects_aux₂`：tr_respects_aux₂ [DecidableEq K] {k : K}
 {q : TM1.Stmt (Γ' K Γ) (Λ' K Γ Λ σ) σ} {v : σ} {S : forall k, List (Γ k)} {L : 
ListBlank (forall k,…
· 使用定理 `StateTransition.Reaches₀.tail'`：∀ {σ : Type u_1} {f : σ → Option σ} {a b
 c : σ},   StateTransition.Reaches₀ f a b → c ∈ f b → StateTransition.Reaches₁ f
 a c
· 使用定理 `Relation.TransGen.to_reflTransGen`：to_reflTransGen {a b} : TransGen r a 
b -> ReflTransGen r a b
· 使用定理 `StateTransition.Reaches₀.trans`：∀ {σ : Type u_1} {f : σ → Option σ} {a b
 c : σ},   StateTransition.Reaches₀ f a b → StateTransition.Reaches₀ f b c → Sta
teTransition.Reaches…
· 使用定理 `StateTransition.Reaches₁.to₀`：∀ {σ : Type u_1} {f : σ → Option σ} {a b :
 σ}, StateTransition.Reaches₁ f a b → StateTransition.Reaches₀ f a b
· 使用定理 `Turing.TM1.stepAux.eq_5`：∀ {Γ : Type u_1} {Λ : Type u_2} {σ : Type u_3} 
[inst : Inhabited Γ] (x : σ) (x_1 : Turing.Tape Γ) (l : Γ → σ → Λ),   Turing.TM1
.stepAux (Tur…
· 使用定理 `cond.eq_1`：∀ {α : Sort u} (x y : α), (bif true then x else y) = x
· 使用定理 `Option.isNone.eq_2`：∀ {α : Type u_1}, none.isNone = true
· 使用定理 `List.getElem?_eq_none`：∀ {α : Type u_1} {l : List α} {i : ℕ}, l.length ≤
 i → l[i]? = none
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `List.length_reverse`：∀ {α : Type u_1} {as : List α}, as.reverse.length =
 as.length
· 使用定理 `Turing.TM2to1.stk_nth_val`：stk_nth_val {K : Type*} {Γ : K -> Type*} {L :
 ListBlank (forall k, Option (Γ k))} {k S} (n) (hL : ListBlank.map (proj k) L = 
ListBlank.mk (L…
· 使用定理 `Turing.TM2to1.addBottom_nth_snd`：addBottom_nth_snd (L : ListBlank (foral
l k, Option (Γ k))) (n : Nat) : ((addBottom L).nth n).2 = L.nth n
· 使用定理 `Turing.Tape.mk'_nth_nat`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (L R : Tu
ring.ListBlank Γ) (n : ℕ), (Turing.Tape.mk' L R).nth ↑n = R.nth n
· 使用定理 `Turing.Tape.move_right_n_head`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (T 
: Turing.Tape Γ) (i : ℕ),   ((Turing.Tape.move Turing.Dir.right)^[i] T).head = T
.nth ↑i
· 使用定理 `Turing.TM1.stepAux.eq_4`：∀ {Γ : Type u_1} {Λ : Type u_2} {σ : Type u_3} 
[inst : Inhabited Γ] (x : σ) (x_1 : Turing.Tape Γ) (p : Γ → σ → Bool)   (q₁ q₂ :
 Turing.TM1.S…
· 使用定理 `Turing.TM2to1.tr.eq_2`：∀ {K : Type u_1} {Γ : K → Type u_2} {Λ : Type u_3
} {σ : Type u_4} [inst : DecidableEq K] (M : Λ → Turing.TM2.Stmt Γ Λ σ)   (k : K
) (s : Turi…
· 使用定理 `Turing.TM2to1.tr_respects_aux₃`：tr_respects_aux₃ {q v} {L : ListBlank (f
orall k, Option (Γ k))} (n) : Reaches₀ (TM1.step (tr M)) ⟨some (ret q), v, (Tape
.move Dir.right)^[n]…
· 使用定理 `Relation.TransGen.head'`：head' (hab : r a b) (hbc : ReflTransGen r b c) 
: TransGen r a c
· 使用定理 `Turing.TM2to1.tr.eq_3`：∀ {K : Type u_1} {Γ : K → Type u_2} {Λ : Type u_3
} {σ : Type u_4} [inst : DecidableEq K] (M : Λ → Turing.TM2.Stmt Γ Λ σ)   (q : T
uring.TM2.S…
· 使用定理 `Turing.Tape.mk'_head`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (L R : Turin
g.ListBlank Γ), (Turing.Tape.mk' L R).head = R.head
· 使用定理 `Turing.TM2to1.addBottom_head_fst`：addBottom_head_fst (L : ListBlank (for
all k, Option (Γ k))) : (addBottom L).head.1 = true
-/
theorem tr_respects_aux₁ {k} (o q v) {S : List (Γ k)} {L : ListBlank (∀ k, Option (Γ k))}
    (hL : L.map (proj k) = ListBlank.mk (S.map some).reverse) (n) (H : n ≤ S.length) :
    Reaches₀ (TM1.step (tr M)) ⟨some (go k o q), v, Tape.mk' ∅ (addBottom L)⟩
      ⟨some (go k o q), v, (Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩ := by
  induction n with
  | zero => rfl
  | succ n IH =>
    apply (IH (le_of_lt H)).tail
    rw [iterate_succ_apply']
    simp only [TM1.step, TM1.stepAux, tr, Tape.mk'_nth_nat, Tape.move_right_n_head,
      addBottom_nth_snd, Option.mem_def]
    rw [stk_nth_val _ hL, List.getElem?_eq_getElem]
    · rfl
    · rwa [List.length_reverse]
/-
**Turing.TM2to1.tr_respects_aux** 是 Mathlib 中的一个定理，位于命名空间 `Turing.TM2to1`。
形式化陈述：tr_respects_aux {q v T k} {S : forall k, List (Γ k)} (hT : forall k, ListB
lank.map (proj k) T = ListBlank.mk ((S k).map some).reverse) (o : StAct K Γ σ k)
 (IH : forall {v : σ} {S : forall k : K, List (Γ k)} {T : ListBlank (forall k, O
ption (Γ k))}, (forall k, ListBlank.map (proj k) T = ListBlank.mk ((S k).map som
e).reverse) -> exists b, TrCfg (TM2.stepAux q v S) b ∧ Reaches (TM1.step (tr M))
 (TM1.stepAux (trNormal q) v (Tape.mk' ∅ (addBottom T))) b) : exists b, TrCfg (T
M2.stepAux (stRun o q) v S
参数：Γ k；hT : forall k, ListBlank.map (proj k) T = ListBlank.mk ((S k).map some).r
everse；o : StAct K Γ σ k；IH : forall {v : σ} {S : forall k : K, List (Γ k)} {T :
 ListBlank (forall k, Option (Γ k))}, (forall k, ListBlank.map (proj k) T = List
Blank.mk ((S k).map some).reverse) -> exists b, TrCfg (TM2.stepAux q v S) b ∧ Re
aches (TM1.step (tr M)) (TM1.stepAux (trNormal q) v (Tape.mk' ∅ (addBottom T))) 
b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Turing.TM2to1.step_run`：∀ {K : Type u_1} {Γ : K → Type u_2} {Λ : Type u_
3} {σ : Type u_4} [inst : DecidableEq K] {k : K}   (q : Turing.TM2.Stmt Γ Λ σ) (
v : σ) (S : …
· 使用定理 `Turing.TM2to1.trNormal_run`：trNormal_run {k : K} (s : StAct K Γ σ k) (q 
: TM2.Stmt Γ Λ σ) : trNormal (stRun s q) = goto fun _ _ => go k s q
· 使用定理 `Turing.TM2to1.tr_respects_aux₁`：tr_respects_aux₁ {k} (o q v) {S : List (
Γ k)} {L : ListBlank (forall k, Option (Γ k))} (hL : L.map (proj k) = ListBlank.
mk (S.map some).reve…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Turing.TM2to1.tr_respects_aux₂`：tr_respects_aux₂ [DecidableEq K] {k : K}
 {q : TM1.Stmt (Γ' K Γ) (Λ' K Γ Λ σ) σ} {v : σ} {S : forall k, List (Γ k)} {L : 
ListBlank (forall k,…
· 使用定理 `StateTransition.Reaches₀.tail'`：∀ {σ : Type u_1} {f : σ → Option σ} {a b
 c : σ},   StateTransition.Reaches₀ f a b → c ∈ f b → StateTransition.Reaches₁ f
 a c
· 使用定理 `Relation.TransGen.to_reflTransGen`：to_reflTransGen {a b} : TransGen r a 
b -> ReflTransGen r a b
· 使用定理 `StateTransition.Reaches₀.trans`：∀ {σ : Type u_1} {f : σ → Option σ} {a b
 c : σ},   StateTransition.Reaches₀ f a b → StateTransition.Reaches₀ f b c → Sta
teTransition.Reaches…
· 使用定理 `StateTransition.Reaches₁.to₀`：∀ {σ : Type u_1} {f : σ → Option σ} {a b :
 σ}, StateTransition.Reaches₁ f a b → StateTransition.Reaches₀ f a b
· 使用定理 `Turing.TM1.stepAux.eq_5`：∀ {Γ : Type u_1} {Λ : Type u_2} {σ : Type u_3} 
[inst : Inhabited Γ] (x : σ) (x_1 : Turing.Tape Γ) (l : Γ → σ → Λ),   Turing.TM1
.stepAux (Tur…
· 使用定理 `cond.eq_1`：∀ {α : Sort u} (x y : α), (bif true then x else y) = x
· 使用定理 `Option.isNone.eq_2`：∀ {α : Type u_1}, none.isNone = true
· 使用定理 `List.getElem?_eq_none`：∀ {α : Type u_1} {l : List α} {i : ℕ}, l.length ≤
 i → l[i]? = none
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `List.length_reverse`：∀ {α : Type u_1} {as : List α}, as.reverse.length =
 as.length
· 使用定理 `Turing.TM2to1.stk_nth_val`：stk_nth_val {K : Type*} {Γ : K -> Type*} {L :
 ListBlank (forall k, Option (Γ k))} {k S} (n) (hL : ListBlank.map (proj k) L = 
ListBlank.mk (L…
· 使用定理 `Turing.TM2to1.addBottom_nth_snd`：addBottom_nth_snd (L : ListBlank (foral
l k, Option (Γ k))) (n : Nat) : ((addBottom L).nth n).2 = L.nth n
· 使用定理 `Turing.Tape.mk'_nth_nat`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (L R : Tu
ring.ListBlank Γ) (n : ℕ), (Turing.Tape.mk' L R).nth ↑n = R.nth n
· 使用定理 `Turing.Tape.move_right_n_head`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (T 
: Turing.Tape Γ) (i : ℕ),   ((Turing.Tape.move Turing.Dir.right)^[i] T).head = T
.nth ↑i
· 使用定理 `Turing.TM1.stepAux.eq_4`：∀ {Γ : Type u_1} {Λ : Type u_2} {σ : Type u_3} 
[inst : Inhabited Γ] (x : σ) (x_1 : Turing.Tape Γ) (p : Γ → σ → Bool)   (q₁ q₂ :
 Turing.TM1.S…
· 使用定理 `Turing.TM2to1.tr.eq_2`：∀ {K : Type u_1} {Γ : K → Type u_2} {Λ : Type u_3
} {σ : Type u_4} [inst : DecidableEq K] (M : Λ → Turing.TM2.Stmt Γ Λ σ)   (k : K
) (s : Turi…
· 使用定理 `Turing.TM2to1.tr_respects_aux₃`：tr_respects_aux₃ {q v} {L : ListBlank (f
orall k, Option (Γ k))} (n) : Reaches₀ (TM1.step (tr M)) ⟨some (ret q), v, (Tape
.move Dir.right)^[n]…
· 使用定理 `Relation.TransGen.head'`：head' (hab : r a b) (hbc : ReflTransGen r b c) 
: TransGen r a c
· 使用定理 `Turing.TM2to1.tr.eq_3`：∀ {K : Type u_1} {Γ : K → Type u_2} {Λ : Type u_3
} {σ : Type u_4} [inst : DecidableEq K] (M : Λ → Turing.TM2.Stmt Γ Λ σ)   (q : T
uring.TM2.S…
· 使用定理 `Turing.Tape.mk'_head`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (L R : Turin
g.ListBlank Γ), (Turing.Tape.mk' L R).head = R.head
· 使用定理 `Turing.TM2to1.addBottom_head_fst`：addBottom_head_fst (L : ListBlank (for
all k, Option (Γ k))) : (addBottom L).head.1 = true
-/
theorem tr_respects_aux₃ {q v} {L : ListBlank (∀ k, Option (Γ k))} (n) : Reaches₀ (TM1.step (tr M))
    ⟨some (ret q), v, (Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩
    ⟨some (ret q), v, Tape.mk' ∅ (addBottom L)⟩ := by
  induction n with
  | zero => rfl
  | succ n IH =>
    refine Reaches₀.head ?_ IH
    simp only [Option.mem_def, TM1.step]
    rw [Option.some_inj, tr, TM1.stepAux, Tape.move_right_n_head, Tape.mk'_nth_nat,
      addBottom_nth_succ_fst, TM1.stepAux, iterate_succ', Function.comp_apply, Tape.move_right_left]
    rfl
/-
**Turing.TM2to1.tr_respects_aux** 是 Mathlib 中的一个定理，位于命名空间 `Turing.TM2to1`。
形式化陈述：tr_respects_aux {q v T k} {S : forall k, List (Γ k)} (hT : forall k, ListB
lank.map (proj k) T = ListBlank.mk ((S k).map some).reverse) (o : StAct K Γ σ k)
 (IH : forall {v : σ} {S : forall k : K, List (Γ k)} {T : ListBlank (forall k, O
ption (Γ k))}, (forall k, ListBlank.map (proj k) T = ListBlank.mk ((S k).map som
e).reverse) -> exists b, TrCfg (TM2.stepAux q v S) b ∧ Reaches (TM1.step (tr M))
 (TM1.stepAux (trNormal q) v (Tape.mk' ∅ (addBottom T))) b) : exists b, TrCfg (T
M2.stepAux (stRun o q) v S
参数：Γ k；hT : forall k, ListBlank.map (proj k) T = ListBlank.mk ((S k).map some).r
everse；o : StAct K Γ σ k；IH : forall {v : σ} {S : forall k : K, List (Γ k)} {T :
 ListBlank (forall k, Option (Γ k))}, (forall k, ListBlank.map (proj k) T = List
Blank.mk ((S k).map some).reverse) -> exists b, TrCfg (TM2.stepAux q v S) b ∧ Re
aches (TM1.step (tr M)) (TM1.stepAux (trNormal q) v (Tape.mk' ∅ (addBottom T))) 
b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Turing.TM2to1.step_run`：∀ {K : Type u_1} {Γ : K → Type u_2} {Λ : Type u_
3} {σ : Type u_4} [inst : DecidableEq K] {k : K}   (q : Turing.TM2.Stmt Γ Λ σ) (
v : σ) (S : …
· 使用定理 `Turing.TM2to1.trNormal_run`：trNormal_run {k : K} (s : StAct K Γ σ k) (q 
: TM2.Stmt Γ Λ σ) : trNormal (stRun s q) = goto fun _ _ => go k s q
· 使用定理 `Turing.TM2to1.tr_respects_aux₁`：tr_respects_aux₁ {k} (o q v) {S : List (
Γ k)} {L : ListBlank (forall k, Option (Γ k))} (hL : L.map (proj k) = ListBlank.
mk (S.map some).reve…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Turing.TM2to1.tr_respects_aux₂`：tr_respects_aux₂ [DecidableEq K] {k : K}
 {q : TM1.Stmt (Γ' K Γ) (Λ' K Γ Λ σ) σ} {v : σ} {S : forall k, List (Γ k)} {L : 
ListBlank (forall k,…
· 使用定理 `StateTransition.Reaches₀.tail'`：∀ {σ : Type u_1} {f : σ → Option σ} {a b
 c : σ},   StateTransition.Reaches₀ f a b → c ∈ f b → StateTransition.Reaches₁ f
 a c
· 使用定理 `Relation.TransGen.to_reflTransGen`：to_reflTransGen {a b} : TransGen r a 
b -> ReflTransGen r a b
· 使用定理 `StateTransition.Reaches₀.trans`：∀ {σ : Type u_1} {f : σ → Option σ} {a b
 c : σ},   StateTransition.Reaches₀ f a b → StateTransition.Reaches₀ f b c → Sta
teTransition.Reaches…
· 使用定理 `StateTransition.Reaches₁.to₀`：∀ {σ : Type u_1} {f : σ → Option σ} {a b :
 σ}, StateTransition.Reaches₁ f a b → StateTransition.Reaches₀ f a b
· 使用定理 `Turing.TM1.stepAux.eq_5`：∀ {Γ : Type u_1} {Λ : Type u_2} {σ : Type u_3} 
[inst : Inhabited Γ] (x : σ) (x_1 : Turing.Tape Γ) (l : Γ → σ → Λ),   Turing.TM1
.stepAux (Tur…
· 使用定理 `cond.eq_1`：∀ {α : Sort u} (x y : α), (bif true then x else y) = x
· 使用定理 `Option.isNone.eq_2`：∀ {α : Type u_1}, none.isNone = true
· 使用定理 `List.getElem?_eq_none`：∀ {α : Type u_1} {l : List α} {i : ℕ}, l.length ≤
 i → l[i]? = none
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `List.length_reverse`：∀ {α : Type u_1} {as : List α}, as.reverse.length =
 as.length
· 使用定理 `Turing.TM2to1.stk_nth_val`：stk_nth_val {K : Type*} {Γ : K -> Type*} {L :
 ListBlank (forall k, Option (Γ k))} {k S} (n) (hL : ListBlank.map (proj k) L = 
ListBlank.mk (L…
· 使用定理 `Turing.TM2to1.addBottom_nth_snd`：addBottom_nth_snd (L : ListBlank (foral
l k, Option (Γ k))) (n : Nat) : ((addBottom L).nth n).2 = L.nth n
· 使用定理 `Turing.Tape.mk'_nth_nat`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (L R : Tu
ring.ListBlank Γ) (n : ℕ), (Turing.Tape.mk' L R).nth ↑n = R.nth n
· 使用定理 `Turing.Tape.move_right_n_head`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (T 
: Turing.Tape Γ) (i : ℕ),   ((Turing.Tape.move Turing.Dir.right)^[i] T).head = T
.nth ↑i
· 使用定理 `Turing.TM1.stepAux.eq_4`：∀ {Γ : Type u_1} {Λ : Type u_2} {σ : Type u_3} 
[inst : Inhabited Γ] (x : σ) (x_1 : Turing.Tape Γ) (p : Γ → σ → Bool)   (q₁ q₂ :
 Turing.TM1.S…
· 使用定理 `Turing.TM2to1.tr.eq_2`：∀ {K : Type u_1} {Γ : K → Type u_2} {Λ : Type u_3
} {σ : Type u_4} [inst : DecidableEq K] (M : Λ → Turing.TM2.Stmt Γ Λ σ)   (k : K
) (s : Turi…
· 使用定理 `Turing.TM2to1.tr_respects_aux₃`：tr_respects_aux₃ {q v} {L : ListBlank (f
orall k, Option (Γ k))} (n) : Reaches₀ (TM1.step (tr M)) ⟨some (ret q), v, (Tape
.move Dir.right)^[n]…
· 使用定理 `Relation.TransGen.head'`：head' (hab : r a b) (hbc : ReflTransGen r b c) 
: TransGen r a c
· 使用定理 `Turing.TM2to1.tr.eq_3`：∀ {K : Type u_1} {Γ : K → Type u_2} {Λ : Type u_3
} {σ : Type u_4} [inst : DecidableEq K] (M : Λ → Turing.TM2.Stmt Γ Λ σ)   (q : T
uring.TM2.S…
· 使用定理 `Turing.Tape.mk'_head`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (L R : Turin
g.ListBlank Γ), (Turing.Tape.mk' L R).head = R.head
· 使用定理 `Turing.TM2to1.addBottom_head_fst`：addBottom_head_fst (L : ListBlank (for
all k, Option (Γ k))) : (addBottom L).head.1 = true
-/
theorem tr_respects_aux {q v T k} {S : ∀ k, List (Γ k)}
    (hT : ∀ k, ListBlank.map (proj k) T = ListBlank.mk ((S k).map some).reverse)
    (o : StAct K Γ σ k)
    (IH : ∀ {v : σ} {S : ∀ k : K, List (Γ k)} {T : ListBlank (∀ k, Option (Γ k))},
      (∀ k, ListBlank.map (proj k) T = ListBlank.mk ((S k).map some).reverse) →
      ∃ b, TrCfg (TM2.stepAux q v S) b ∧
        Reaches (TM1.step (tr M)) (TM1.stepAux (trNormal q) v (Tape.mk' ∅ (addBottom T))) b) :
    ∃ b, TrCfg (TM2.stepAux (stRun o q) v S) b ∧ Reaches (TM1.step (tr M))
      (TM1.stepAux (trNormal (stRun o q)) v (Tape.mk' ∅ (addBottom T))) b := by
  simp only [trNormal_run, step_run]
  have hgo := tr_respects_aux₁ M o q v (hT k) _ le_rfl
  obtain ⟨T', hT', hrun⟩ := tr_respects_aux₂ (Λ := Λ) hT o
  have := hgo.tail' rfl
  rw [tr, TM1.stepAux, Tape.move_right_n_head, Tape.mk'_nth_nat, addBottom_nth_snd,
    stk_nth_val _ (hT k), List.getElem?_eq_none (le_of_eq List.length_reverse),
    Option.isNone, cond, hrun, TM1.stepAux] at this
  obtain ⟨c, gc, rc⟩ := IH hT'
  refine ⟨c, gc, (this.to₀.trans (tr_respects_aux₃ M _) c (TransGen.head' rfl ?_)).to_reflTransGen⟩
  rw [tr, TM1.stepAux, Tape.mk'_head, addBottom_head_fst]
  exact rc

attribute [local simp] Respects TM2.step TM2.stepAux trNormal
/-
**Turing.TM2to1.tr_respects** 是 Mathlib 中的一个定理，位于命名空间 `Turing.TM2to1`。
形式化陈述：tr_respects : Respects (TM2.step M) (TM1.step (tr M)) TrCfg
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Turing.TM2to1.tr_respects_aux`：tr_respects_aux {q v T k} {S : forall k, 
List (Γ k)} (hT : forall k, ListBlank.map (proj k) T = ListBlank.mk ((S k).map s
ome).reverse) (o : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Turing.TM2.stepAux.eq_def`：∀ {K : Type u_1} {Γ : K → Type u_2} {Λ : Type
 u_3} {σ : Type u_4} [inst : DecidableEq K] (x : Turing.TM2.Stmt Γ Λ σ)   (x_1 :
 σ) (x_2 : (k :…
· 使用定理 `Turing.TM2to1.trNormal.eq_def`：∀ {K : Type u_1} {Γ : K → Type u_2} {Λ : 
Type u_3} {σ : Type u_4} (x : Turing.TM2.Stmt Γ Λ σ),   Turing.TM2to1.trNormal x
 =     match x with…
· 使用定理 `Turing.TM1.stepAux.eq_def`：∀ {Γ : Type u_1} {Λ : Type u_2} {σ : Type u_3
} [inst : Inhabited Γ] (x : Turing.TM1.Stmt Γ Λ σ) (x_1 : σ)   (x_2 : Turing.Tap
e Γ),   Turing.…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Relation.TransGen.head'`：head' (hab : r a b) (hbc : ReflTransGen r b c) 
: TransGen r a c
-/
theorem tr_respects : Respects (TM2.step M) (TM1.step (tr M)) TrCfg := by
  intro c₁ c₂ h
  obtain @⟨- | l, v, S, L, hT⟩ := h; · constructor
  rsuffices ⟨b, c, r⟩ : ∃ b, _ ∧ Reaches (TM1.step (tr M)) _ _
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
/-
**Turing.TM2to1.trCfg_init** 是 Mathlib 中的一个定理，位于命名空间 `Turing.TM2to1`。
形式化陈述：trCfg_init (k) (L : List (Γ k)) : TrCfg (TM2.init k L) (TM1.init (trInit k
 L) : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ)
参数：k；L : List (Γ k)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Turing.TM2to1.trInit.eq_1`：∀ {K : Type u_1} {Γ : K → Type u_2} [inst : D
ecidableEq K] (k : K) (L : List (Γ k)),   Turing.TM2to1.trInit k L =     (true, 
(List.map (fun …
· 使用定理 `Turing.TM1.init.eq_1`：∀ {Γ : Type u_1} {Λ : Type u_2} {σ : Type u_3} [in
st : Inhabited Λ] [inst_1 : Inhabited Γ] [inst_2 : Inhabited σ]   (l : List Γ), 
Turing.TM1…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `Turing.ListBlank.ext`：∀ {Γ : Type u_1} [i : Inhabited Γ] {L₁ L₂ : Turing
.ListBlank Γ}, (∀ (i_1 : ℕ), L₁.nth i_1 = L₂.nth i_1) → L₁ = L₂
· 使用定理 `Turing.ListBlank.map_mk`：∀ {Γ : Type u_1} {Γ' : Type u_2} [inst : Inhabi
ted Γ] [inst_1 : Inhabited Γ'] (f : Turing.PointedMap Γ Γ') (l : List Γ),   Turi
ng.ListBlank.…
· 使用定理 `Turing.ListBlank.nth_mk`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (l : List
 Γ) (n : ℕ), (Turing.ListBlank.mk l).nth n = l.getI n
· 使用定理 `List.getI_eq_getElem?_getD`：∀ {α : Type u} (l : List α) [inst : Inhabite
d α] (n : ℕ), l.getI n = l[n]?.getD default
· 使用定理 `List.getElem?_map`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : List
 α} {i : ℕ}, (List.map f l)[i]? = Option.map f l[i]?
· 使用定理 `Turing.proj.eq_1`：∀ {ι : Type u_1} {Γ : ι → Type u_2} [inst : (i : ι) → 
Inhabited (Γ i)] (i : ι),   Turing.proj i = { f := fun a => a i, map_pt' := ⋯ }
· 使用定理 `Turing.PointedMap.mk_val`：∀ {Γ : Type u_1} {Γ' : Type u_2} [inst : Inhab
ited Γ] [inst_1 : Inhabited Γ'] (f : Γ → Γ') (pt : f default = default),   { f :
= f, map_pt' :…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `List.map_reverse`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : List 
α}, List.map f l.reverse = (List.map f l).reverse
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `List.map.eq_1`：∀ {α : Type u_1} {β : Type u_2} (f : α → β), List.map f [
] = []
· 使用定理 `List.reverse_nil`：∀ {α : Type u}, [].reverse = []
-/
theorem trCfg_init (k) (L : List (Γ k)) : TrCfg (TM2.init k L)
    (TM1.init (trInit k L) : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ) := by
  rw [(_ : TM1.init _ = _)]
  · refine ⟨ListBlank.mk (L.reverse.map fun a ↦ update default k (some a)), fun k' ↦ ?_⟩
    refine ListBlank.ext fun i ↦ ?_
    rw [ListBlank.map_mk, ListBlank.nth_mk, List.getI_eq_getElem?_getD, List.map_map]
    have : ((proj k').f ∘ fun a => update (β := fun k => Option (Γ k)) default k (some a))
      = fun a => (proj k').f (update (β := fun k => Option (Γ k)) default k (some a)) := rfl
    rw [this, List.getElem?_map, proj, PointedMap.mk_val]
    by_cases h : k' = k
    · subst k'
      simp only [Function.update_self]
      rw [ListBlank.nth_mk, List.getI_eq_getElem?_getD, ← List.map_reverse, List.getElem?_map]
    · simp only [Function.update_of_ne h]
      rw [ListBlank.nth_mk, List.getI_eq_getElem?_getD, List.map, List.reverse_nil]
      cases L.reverse[i]? <;> rfl
  · rw [trInit, TM1.init]
    congr <;> cases L.reverse <;> try rfl
    simp only [List.map_map, List.tail_cons, List.map]
    rfl
/-
**Turing.TM2to1.tr_eval_dom** 是 Mathlib 中的一个定理，位于命名空间 `Turing.TM2to1`。
形式化陈述：tr_eval_dom (k) (L : List (Γ k)) : (TM1.eval (tr M) (trInit k L)).Dom ↔ (T
M2.eval M k L).Dom
参数：k；L : List (Γ k)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StateTransition.tr_eval_dom`：tr_eval_dom {σ₁ σ₂ f₁ f₂} {tr : σ₁ -> σ₂ ->
 Prop} (H : Respects f₁ f₂ tr) {a₁ a₂} (aa : tr a₁ a₂) : (eval f₂ a₂).Dom ↔ (eva
l f₁ a₁).Dom
· 使用定理 `Turing.TM2to1.tr_respects`：tr_respects : Respects (TM2.step M) (TM1.step
 (tr M)) TrCfg
· 使用定理 `Turing.TM2to1.trCfg_init`：trCfg_init (k) (L : List (Γ k)) : TrCfg (TM2.i
nit k L) (TM1.init (trInit k L) : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ)
-/
theorem tr_eval_dom (k) (L : List (Γ k)) :
    (TM1.eval (tr M) (trInit k L)).Dom ↔ (TM2.eval M k L).Dom :=
  StateTransition.tr_eval_dom (tr_respects M) (trCfg_init k L)
/-
**Turing.TM2to1.tr_eval** 是 Mathlib 中的一个定理，位于命名空间 `Turing.TM2to1`。
形式化陈述：tr_eval (k) (L : List (Γ k)) {L₁ L₂} (H₁ : L₁ in TM1.eval (tr M) (trInit k
 L)) (H₂ : L₂ in TM2.eval M k L) : exists (S : forall k, List (Γ k)) (L' : ListB
lank (forall k, Option (Γ k))), addBottom L' = L₁ ∧ (forall k, L'.map (proj k) =
 ListBlank.mk ((S k).map some).reverse) ∧ S k = L₂
参数：k；L : List (Γ k)；H₁ : L₁ in TM1.eval (tr M) (trInit k L)；H₂ : L₂ in TM2.eval 
M k L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Part.mem_map_iff`：mem_map_iff (f : α -> β) {o : Part α} {b} : b in map f
 o ↔ exists a in o, f a = b
· 使用定理 `StateTransition.tr_eval`：tr_eval {σ₁ σ₂ f₁ f₂} {tr : σ₁ -> σ₂ -> Prop} (
H : Respects f₁ f₂ tr) {a₁ b₁ a₂} (aa : tr a₁ a₂) (ab : b₁ in eval f₁ a₁) : exis
ts b₂, tr b₁ …
· 使用定理 `Turing.TM2to1.tr_respects`：tr_respects : Respects (TM2.step M) (TM1.step
 (tr M)) TrCfg
· 使用定理 `Turing.TM2to1.trCfg_init`：trCfg_init (k) (L : List (Γ k)) : TrCfg (TM2.i
nit k L) (TM1.init (trInit k L) : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ)
· 使用定理 `Part.mem_unique`：∀ {α : Type u_1} {a b : α} {o : Part α}, a ∈ o → b ∈ o 
→ a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Turing.Tape.mk'_right₀`：∀ {Γ : Type u_1} [inst : Inhabited Γ] (L R : Tur
ing.ListBlank Γ), (Turing.Tape.mk' L R).right₀ = R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem tr_eval (k) (L : List (Γ k)) {L₁ L₂} (H₁ : L₁ ∈ TM1.eval (tr M) (trInit k L))
    (H₂ : L₂ ∈ TM2.eval M k L) :
    ∃ (S : ∀ k, List (Γ k)) (L' : ListBlank (∀ k, Option (Γ k))),
      addBottom L' = L₁ ∧
        (∀ k, L'.map (proj k) = ListBlank.mk ((S k).map some).reverse) ∧ S k = L₂ := by
  obtain ⟨c₁, h₁, rfl⟩ := (Part.mem_map_iff _).1 H₁
  obtain ⟨c₂, h₂, rfl⟩ := (Part.mem_map_iff _).1 H₂
  obtain ⟨_, ⟨L', hT⟩, h₃⟩ := StateTransition.tr_eval (tr_respects M) (trCfg_init k L) h₂
  cases Part.mem_unique h₁ h₃
  exact ⟨_, L', by simp only [Tape.mk'_right₀], hT, rfl⟩

end

section

variable [Inhabited Λ]

open scoped Classical in
/-- The support of a set of TM2 states in the TM2 emulator. -/
/-
**Turing.TM2to1.trSupp** 是 Mathlib 中的一个定义，位于命名空间 `Turing.TM2to1`。
形式化陈述：trSupp (S : Finset Λ) : Finset (Λ' K Γ Λ σ)
参数：S : Finset Λ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The support of a set of TM2 states in the TM2 emulator.
-/
noncomputable def trSupp (S : Finset Λ) : Finset (Λ' K Γ Λ σ) :=
  S.biUnion fun l ↦ insert (normal l) (trStmts₁ (M l))

open scoped Classical in
/-
**Turing.TM2to1.tr_supports** 是 Mathlib 中的一个定理，位于命名空间 `Turing.TM2to1`。
形式化陈述：tr_supports {S} (ss : TM2.Supports M S) : TM1.Supports (tr M) (trSupp M S)
参数：ss : TM2.Supports M S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_biUnion`：∀ {α : Type u_1} {β : Type u_2} {s : Finset α} {t : 
α → Finset β} [inst : DecidableEq β] {b : β},   b ∈ s.biUnion t ↔ ∃ a ∈ s, b ∈ t
 a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.mem_insert`：mem_insert : a in insert b s ↔ a = b ∨ a in s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Turing.TM2to1.trStmts₁_run`：trStmts₁_run {k : K} {s : StAct K Γ σ k} {q 
: TM2.Stmt Γ Λ σ} : open scoped Classical in trStmts₁ (stRun s q) = {go k s q, r
et q} union trSt…
· 使用定理 `Turing.TM2to1.supports_run`：supports_run (S : Finset Λ) {k : K} (s : StA
ct K Γ σ k) (q : TM2.Stmt Γ Λ σ) : TM2.SupportsStmt S (stRun s q) ↔ TM2.Supports
Stmt S q
· 使用定理 `Turing.TM2to1.trNormal_run`：trNormal_run {k : K} (s : StAct K Γ σ k) (q 
: TM2.Stmt Γ Λ σ) : trNormal (stRun s q) = goto fun _ _ => go k s q
· 使用定理 `Turing.TM1.SupportsStmt.eq_5`：∀ {Γ : Type u_1} {Λ : Type u_2} {σ : Type 
u_3} (S : Finset Λ) (l : Γ → σ → Λ),   Turing.TM1.SupportsStmt S (Turing.TM1.Stm
t.goto l) = ∀ (a :…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Turing.TM1.SupportsStmt.eq_def`：∀ {Γ : Type u_1} {Λ : Type u_2} {σ : Typ
e u_3} (S : Finset Λ) (x : Turing.TM1.Stmt Γ Λ σ),   Turing.TM1.SupportsStmt S x
 =     match x with …
· 使用定理 `Turing.TM2to1.trStmts₁.eq_def`：∀ {K : Type u_1} {Γ : K → Type u_2} {Λ : 
Type u_3} {σ : Type u_4} (x : Turing.TM2.Stmt Γ Λ σ),   Turing.TM2to1.trStmts₁ x
 =     match x with…
· 使用定理 `Finset.mem_union_left`：mem_union_left (t : Finset α) (h : a in s) : a in
 s union t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.mem_union_right`：mem_union_right (s : Finset α) (h : a in t) : a 
in s union t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_union`：mem_union : a in s union t ↔ a in s ∨ a in t
· 使用定理 `Turing.TM2to1.trStmts₁.eq_5`：∀ {K : Type u_1} {Γ : K → Type u_2} {Λ : Ty
pe u_3} {σ : Type u_4} (a : σ → Bool) (q₁ q₂ : Turing.TM2.Stmt Γ Λ σ),   Turing.
TM2to1.trStmts₁ (…
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `trivial`：True
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
-/
theorem tr_supports {S} (ss : TM2.Supports M S) : TM1.Supports (tr M) (trSupp M S) :=
  ⟨Finset.mem_biUnion.2 ⟨_, ss.1, Finset.mem_insert.2 <| Or.inl rfl⟩, fun l' h ↦ by
    suffices ∀ (q) (_ : TM2.SupportsStmt S q) (_ : ∀ x ∈ trStmts₁ q, x ∈ trSupp M S),
        TM1.SupportsStmt (trSupp M S) (trNormal q) ∧
        ∀ l' ∈ trStmts₁ q, TM1.SupportsStmt (trSupp M S) (tr M l') by
      rcases Finset.mem_biUnion.1 h with ⟨l, lS, h⟩
      have :=
        this _ (ss.2 l lS) fun x hx ↦ Finset.mem_biUnion.2 ⟨_, lS, Finset.mem_insert_of_mem hx⟩
      rcases Finset.mem_insert.1 h with (rfl | h) <;> [exact this.1; exact this.2 _ h]
    clear h l'
    refine stmtStRec ?_ ?_ ?_ ?_ ?_
    · intro _ s _ IH ss' sub -- stack op
      rw [TM2to1.supports_run] at ss'
      simp only [TM2to1.trStmts₁_run, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        at sub
      have hgo := sub _ (Or.inl <| Or.inl rfl)
      have hret := sub _ (Or.inl <| Or.inr rfl)
      obtain ⟨IH₁, IH₂⟩ := IH ss' fun x hx ↦ sub x <| Or.inr hx
      refine ⟨by simp only [trNormal_run, TM1.SupportsStmt]; intros; exact hgo, fun l h ↦ ?_⟩
      rw [trStmts₁_run] at h
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
        at h
      rcases h with (⟨rfl | rfl⟩ | h)
      · cases s
        · exact ⟨fun _ _ ↦ hret, fun _ _ ↦ hgo⟩
        · exact ⟨fun _ _ ↦ hret, fun _ _ ↦ hgo⟩
        · exact ⟨⟨fun _ _ ↦ hret, fun _ _ ↦ hret⟩, fun _ _ ↦ hgo⟩
      · unfold TM1.SupportsStmt TM2to1.tr
        exact ⟨IH₁, fun _ _ ↦ hret⟩
      · exact IH₂ _ h
    · intro _ _ IH ss' sub -- load
      unfold TM2to1.trStmts₁ at sub ⊢
      exact IH ss' sub
    · intro _ _ _ IH₁ IH₂ ss' sub -- branch
      unfold TM2to1.trStmts₁ at sub
      obtain ⟨IH₁₁, IH₁₂⟩ := IH₁ ss'.1 fun x hx ↦ sub x <| Finset.mem_union_left _ hx
      obtain ⟨IH₂₁, IH₂₂⟩ := IH₂ ss'.2 fun x hx ↦ sub x <| Finset.mem_union_right _ hx
      refine ⟨⟨IH₁₁, IH₂₁⟩, fun l h ↦ ?_⟩
      rw [trStmts₁] at h
      rcases Finset.mem_union.1 h with (h | h) <;> [exact IH₁₂ _ h; exact IH₂₂ _ h]
    · intro _ ss' _ -- goto
      simp only [trStmts₁, Finset.notMem_empty]; refine ⟨?_, fun _ ↦ False.elim⟩
      exact fun _ v ↦ Finset.mem_biUnion.2 ⟨_, ss' v, Finset.mem_insert_self _ _⟩
    · intro _ _ -- halt
      simp only [trStmts₁, Finset.notMem_empty]
      exact ⟨trivial, fun _ ↦ False.elim⟩⟩

end

end TM2to1

end Turing

