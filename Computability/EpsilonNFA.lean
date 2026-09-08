/-
Copyright (c) 2021 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Yaël Dillies, Anthony DeRossi
-/
module

public import Mathlib.Computability.NFA
public import Mathlib.Data.List.ReduceOption

/-!
# Epsilon Nondeterministic Finite Automata

This file contains the definition of an epsilon Nondeterministic Finite Automaton (`εNFA`), a state
machine which determines whether a string (implemented as a list over an arbitrary alphabet) is in a
regular set by evaluating the string over every possible path, also having access to ε-transitions,
which can be followed without reading a character.
Since this definition allows for automata with infinite states, a `Fintype` instance must be
supplied for true `εNFA`'s.
-/

@[expose] public section


open Set

open Computability

-- "ε_NFA"

universe u v

/-- An `εNFA` is a set of states (`σ`), a transition function from state to state labelled by the
  alphabet (`step`), a starting state (`start`) and a set of acceptance states (`accept`).
  Note the transition function sends a state to a `Set` of states and can make ε-transitions by
  inputting `none`.
  Since this definition allows for Automata with infinite states, a `Fintype` instance must be
  supplied for true `εNFA`'s. -/
/-
**** 是 Mathlib 中的一个结构，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `εNFA` is a set of states (`σ`), a transition function from state to state la
belled by the
  alphabet (`step`), a starting state (`start`) and a set of acceptance states (
`accept`).
  Note the transition function sends a state to a `Set` of states and can make ε
-transitions by
  inputting `none`.
  Since this definition allows for Automata with infinite states, a `Fintype` in
stance must be
  supplied for true `εNFA`'s.
-/
structure εNFA (α : Type u) (σ : Type v) where
  /-- Transition function. The automaton is rendered non-deterministic by this transition function
  returning `Set σ` (rather than `σ`), and ε-transitions are made possible by taking `Option α`
  (rather than `α`). -/
  step : σ → Option α → Set σ
  /-- Starting states. -/
  start : Set σ
  /-- Set of acceptance states. -/
  accept : Set σ

variable {α : Type u} {σ : Type v} (M : εNFA α σ) {S : Set σ} {s t u : σ} {a : α}

namespace εNFA

/-- The `εClosure` of a set is the set of states which can be reached by taking a finite string of
ε-transitions from an element of the set. -/
/-
**εNFA.** 是 Mathlib 中的一个归纳类型，位于命名空间 `εNFA`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `εClosure` of a set is the set of states which can be reached by taking a fi
nite string of
ε-transitions from an element of the set.
-/
inductive εClosure (S : Set σ) : Set σ
  | base : ∀ s ∈ S, εClosure S s
  | step : ∀ (s), ∀ t ∈ M.step s none, εClosure S s → εClosure S t

@[simp]
/-
**εNFA.subset_** 是 Mathlib 中的一个定理，位于命名空间 `εNFA`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subset_εClosure (S : Set σ) : S ⊆ M.εClosure S :=
  εClosure.base

@[simp]
/-
**εNFA.** 是 Mathlib 中的一个定理，位于命名空间 `εNFA`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem εClosure_empty : M.εClosure ∅ = ∅ :=
  eq_empty_of_forall_notMem fun s hs ↦ by induction hs <;> assumption

@[simp]
/-
**εNFA.** 是 Mathlib 中的一个定理，位于命名空间 `εNFA`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem εClosure_univ : M.εClosure univ = univ :=
  eq_univ_of_univ_subset <| subset_εClosure _ _
/-
**εNFA.mem_** 是 Mathlib 中的一个定理，位于命名空间 `εNFA`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_εClosure_iff_exists : s ∈ M.εClosure S ↔ ∃ t ∈ S, s ∈ M.εClosure {t} where
  mp h := by
    induction h with
    | base => tauto
    | step _ _ _ _ ih =>
      obtain ⟨s, _, _⟩ := ih
      use s
      solve_by_elim [εClosure.step]
  mpr := by
    intro ⟨t, _, h⟩
    induction h <;> subst_vars <;> solve_by_elim [εClosure.step]

/-- `M.stepSet S a` is the union of the ε-closure of `M.step s a` for all `s ∈ S`. -/
/-
**εNFA.stepSet** 是 Mathlib 中的一个定义，位于命名空间 `εNFA`。
形式化陈述：stepSet (S : Set σ) (a : α) : Set σ
参数：S : Set σ；a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`M.stepSet S a` is the union of the ε-closure of `M.step s a` for all `s ∈ S`.
-/
def stepSet (S : Set σ) (a : α) : Set σ :=
  ⋃ s ∈ S, M.εClosure (M.step s a)

variable {M}

@[simp]
/-
**εNFA.mem_stepSet_iff** 是 Mathlib 中的一个定理，位于命名空间 `εNFA`。
形式化陈述：mem_stepSet_iff : s in M.stepSet S a ↔ exists t in S, s in M.εClosure (M.s
tep t a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_stepSet_iff : s ∈ M.stepSet S a ↔ ∃ t ∈ S, s ∈ M.εClosure (M.step t a) := by
  simp_rw [stepSet, mem_iUnion₂, exists_prop]

@[simp]
/-
**εNFA.stepSet_empty** 是 Mathlib 中的一个定理，位于命名空间 `εNFA`。
形式化陈述：stepSet_empty (a : α) : M.stepSet ∅ a = ∅
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_false`：iUnion_false {s : False -> Set α} : iUnion s = ∅
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.iUnion_empty`：iUnion_empty : (⋃ _ : ι, ∅ : Set α) = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem stepSet_empty (a : α) : M.stepSet ∅ a = ∅ := by
  simp_rw [stepSet, mem_empty_iff_false, iUnion_false, iUnion_empty]

variable (M)

/-- `M.evalFrom S x` computes all possible paths through `M` with input `x` starting at an element
of `S`. -/
/-
**εNFA.evalFrom** 是 Mathlib 中的一个定义，位于命名空间 `εNFA`。
形式化陈述：evalFrom (start : Set σ) : List α -> Set σ
参数：start : Set σ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`M.evalFrom S x` computes all possible paths through `M` with input `x` starting
 at an element
of `S`.
-/
def evalFrom (start : Set σ) : List α → Set σ :=
  List.foldl M.stepSet (M.εClosure start)

@[simp]
/-
**εNFA.evalFrom_nil** 是 Mathlib 中的一个定理，位于命名空间 `εNFA`。
形式化陈述：evalFrom_nil (S : Set σ) : M.evalFrom S [] = M.εClosure S
参数：S : Set σ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem evalFrom_nil (S : Set σ) : M.evalFrom S [] = M.εClosure S :=
  rfl

@[simp]
/-
**εNFA.evalFrom_singleton** 是 Mathlib 中的一个定理，位于命名空间 `εNFA`。
形式化陈述：evalFrom_singleton (S : Set σ) (a : α) : M.evalFrom S [a] = M.stepSet (M.ε
Closure S) a
参数：S : Set σ；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem evalFrom_singleton (S : Set σ) (a : α) : M.evalFrom S [a] = M.stepSet (M.εClosure S) a :=
  rfl

@[simp]
/-
**εNFA.evalFrom_append_singleton** 是 Mathlib 中的一个定理，位于命名空间 `εNFA`。
形式化陈述：evalFrom_append_singleton (S : Set σ) (x : List α) (a : α) : M.evalFrom S 
(x ++ [a]) = M.stepSet (M.evalFrom S x) a
参数：S : Set σ；x : List α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `εNFA.evalFrom.eq_1`：∀ {α : Type u} {σ : Type v} (M : εNFA α σ) (start : 
Set σ), M.evalFrom start = List.foldl M.stepSet (M.εClosure start)
· 使用定理 `List.foldl_append`：∀ {α : Type u_1} {β : Type u_2} {f : β → α → β} {b : 
β} {l l' : List α},   List.foldl f b (l ++ l') = List.foldl f (List.foldl f b l)
 l'
· 使用定理 `List.foldl_cons`：∀ {α : Type u} {β : Type v} {a : α} {l : List α} {f : β
 → α → β} {b : β},   List.foldl f b (a :: l) = List.foldl f (f b a) l
· 使用定理 `List.foldl_nil`：∀ {α : Type u_1} {β : Type u_2} {f : α → β → α} {b : α},
 List.foldl f b [] = b
-/
theorem evalFrom_append_singleton (S : Set σ) (x : List α) (a : α) :
    M.evalFrom S (x ++ [a]) = M.stepSet (M.evalFrom S x) a := by
  rw [evalFrom, List.foldl_append, List.foldl_cons, List.foldl_nil]

@[simp]
/-
**εNFA.evalFrom_empty** 是 Mathlib 中的一个定理，位于命名空间 `εNFA`。
形式化陈述：evalFrom_empty (x : List α) : M.evalFrom ∅ x = ∅
参数：x : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `εNFA.evalFrom_nil`：evalFrom_nil (S : Set σ) : M.evalFrom S [] = M.εClosu
re S
· 使用定理 `εNFA.εClosure_empty`：εClosure_empty : M.εClosure ∅ = ∅
· 使用定理 `εNFA.evalFrom_append_singleton`：evalFrom_append_singleton (S : Set σ) (x
 : List α) (a : α) : M.evalFrom S (x ++ [a]) = M.stepSet (M.evalFrom S x) a
· 使用定理 `εNFA.stepSet_empty`：stepSet_empty (a : α) : M.stepSet ∅ a = ∅
-/
theorem evalFrom_empty (x : List α) : M.evalFrom ∅ x = ∅ := by
  induction x using List.reverseRecOn with
  | nil => rw [evalFrom_nil, εClosure_empty]
  | append_singleton x a ih => rw [evalFrom_append_singleton, ih, stepSet_empty]
/-
**εNFA.mem_evalFrom_iff_exists** 是 Mathlib 中的一个定理，位于命名空间 `εNFA`。
形式化陈述：mem_evalFrom_iff_exists {s : σ} {S : Set σ} {x : List α} : s in M.evalFrom
 S x ↔ exists t in S, s in M.evalFrom {t} x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `εNFA.mem_εClosure_iff_exists`：mem_εClosure_iff_exists : s in M.εClosure 
S ↔ exists t in S, s in M.εClosure {t} where mp h
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `εNFA.evalFrom_append_singleton`：evalFrom_append_singleton (S : Set σ) (x
 : List α) (a : α) : M.evalFrom S (x ++ [a]) = M.stepSet (M.evalFrom S x) a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem mem_evalFrom_iff_exists {s : σ} {S : Set σ} {x : List α} :
    s ∈ M.evalFrom S x ↔ ∃ t ∈ S, s ∈ M.evalFrom {t} x := by
  induction x using List.reverseRecOn generalizing s with
  | nil => apply mem_εClosure_iff_exists
  | append_singleton _ _ ih =>
    simp_rw [evalFrom_append_singleton, mem_stepSet_iff, ih]
    tauto

/-- `M.eval x` computes all possible paths through `M` with input `x` starting at an element of
`M.start`. -/
/-
**εNFA.eval** 是 Mathlib 中的一个定义，位于命名空间 `εNFA`。
形式化陈述：eval
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`M.eval x` computes all possible paths through `M` with input `x` starting at an
 element of
`M.start`.
-/
def eval :=
  M.evalFrom M.start

@[simp]
/-
**εNFA.eval_nil** 是 Mathlib 中的一个定理，位于命名空间 `εNFA`。
形式化陈述：eval_nil : M.eval [] = M.εClosure M.start
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval_nil : M.eval [] = M.εClosure M.start :=
  rfl

@[simp]
/-
**εNFA.eval_singleton** 是 Mathlib 中的一个定理，位于命名空间 `εNFA`。
形式化陈述：eval_singleton (a : α) : M.eval [a] = M.stepSet (M.εClosure M.start) a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval_singleton (a : α) : M.eval [a] = M.stepSet (M.εClosure M.start) a :=
  rfl

@[simp]
/-
**εNFA.eval_append_singleton** 是 Mathlib 中的一个定理，位于命名空间 `εNFA`。
形式化陈述：eval_append_singleton (x : List α) (a : α) : M.eval (x ++ [a]) = M.stepSet
 (M.eval x) a
参数：x : List α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `εNFA.evalFrom_append_singleton`：evalFrom_append_singleton (S : Set σ) (x
 : List α) (a : α) : M.evalFrom S (x ++ [a]) = M.stepSet (M.evalFrom S x) a
-/
theorem eval_append_singleton (x : List α) (a : α) : M.eval (x ++ [a]) = M.stepSet (M.eval x) a :=
  evalFrom_append_singleton _ _ _ _

/-- `M.accepts` is the language of `x` such that there is an accept state in `M.eval x`. -/
/-
**εNFA.accepts** 是 Mathlib 中的一个定义，位于命名空间 `εNFA`。
形式化陈述：accepts : Language α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`M.accepts` is the language of `x` such that there is an accept state in `M.eval
 x`.
-/
def accepts : Language α :=
  { x | ∃ S ∈ M.accept, S ∈ M.eval x }

/-- `M.IsPath` represents a traversal in `M` from a start state to an end state by following a list
of transitions in order. -/
@[mk_iff]
/-
**εNFA.IsPath** 是 Mathlib 中的一个归纳类型，位于命名空间 `εNFA`。
形式化陈述：{α : Type u} → {σ : Type v} → εNFA α σ → σ → σ → List (Option α) → Prop
参数：Option α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`M.IsPath` represents a traversal in `M` from a start state to an end state by f
ollowing a list
of transitions in order.
-/
inductive IsPath : σ → σ → List (Option α) → Prop
  | nil (s : σ) : IsPath s s []
  | cons (t s u : σ) (a : Option α) (x : List (Option α)) :
      t ∈ M.step s a → IsPath t u x → IsPath s u (a :: x)

@[simp]
/-
**εNFA.isPath_nil** 是 Mathlib 中的一个定理，位于命名空间 `εNFA`。
形式化陈述：isPath_nil : M.IsPath s t [] ↔ s = t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `εNFA.isPath_iff`：∀ {α : Type u} {σ : Type v} (M : εNFA α σ) (a a_1 : σ) 
(a_2 : List (Option α)),   M.IsPath a a_1 a_2 ↔ a_1 = a ∧ a_2 = [] ∨ ∃ t a_3 x, 
t ∈ M…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `instNonemptyOfMonad`：∀ {m : Type u_1 → Type u_2} {α : Type u_1} [Monad m
] [Nonempty α], Nonempty (m α)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isPath_nil : M.IsPath s t [] ↔ s = t := by
  rw [isPath_iff]
  simp [eq_comm]

alias ⟨IsPath.eq_of_nil, _⟩ := isPath_nil

@[simp]
/-
**εNFA.isPath_singleton** 是 Mathlib 中的一个定理，位于命名空间 `εNFA`。
形式化陈述：isPath_singleton {a : Option α} : M.IsPath s t [a] ↔ t in M.step s a where
 mp
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem isPath_singleton {a : Option α} : M.IsPath s t [a] ↔ t ∈ M.step s a where
  mp := by
    rintro (_ | ⟨_, _, _, _, _, _, ⟨⟩⟩)
    assumption
  mpr := by tauto

alias ⟨_, IsPath.singleton⟩ := isPath_singleton
/-
**εNFA.isPath_append** 是 Mathlib 中的一个定理，位于命名空间 `εNFA`。
形式化陈述：isPath_append {x y : List (Option α)} : M.IsPath s u (x ++ y) ↔ exists t, 
M.IsPath s t x ∧ M.IsPath t u y where mp
参数：Option α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.nil_append`：∀ {α : Type u} (as : List α), [] ++ as = as
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem isPath_append {x y : List (Option α)} :
    M.IsPath s u (x ++ y) ↔ ∃ t, M.IsPath s t x ∧ M.IsPath t u y where
  mp := by
    induction x generalizing s with
    | nil =>
      rw [List.nil_append]
      tauto
    | cons x a ih =>
      rintro (_ | ⟨t, _, _, _, _, _, h⟩)
      apply ih at h
      tauto
  mpr := by
    intro ⟨t, hx, _⟩
    induction x generalizing s <;> cases hx <;> tauto
/-
**εNFA.mem_** 是 Mathlib 中的一个定理，位于命名空间 `εNFA`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_εClosure_iff_exists_path {s₁ s₂ : σ} :
    s₂ ∈ M.εClosure {s₁} ↔ ∃ n, M.IsPath s₁ s₂ (.replicate n none) where
  mp h := by
    induction h with
    | base t =>
      use 0
      subst t
      apply IsPath.nil
    | step _ _ _ _ ih =>
      obtain ⟨n, _⟩ := ih
      use n + 1
      rw [List.replicate_add, isPath_append]
      tauto
  mpr := by
    intro ⟨n, h⟩
    induction n generalizing s₂
    · rw [List.replicate_zero] at h
      apply IsPath.eq_of_nil at h
      solve_by_elim
    · simp_rw [List.replicate_add, isPath_append, List.replicate_one, isPath_singleton] at h
      obtain ⟨t, _, _⟩ := h
      solve_by_elim [εClosure.step]
/-
**εNFA.mem_evalFrom_iff_exists_path** 是 Mathlib 中的一个定理，位于命名空间 `εNFA`。
形式化陈述：mem_evalFrom_iff_exists_path {s₁ s₂ : σ} {x : List α} : s₂ in M.evalFrom {
s₁} x ↔ exists x', x'.reduceOption = x ∧ M.IsPath s₁ s₂ x'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `εNFA.evalFrom_nil`：evalFrom_nil (S : Set σ) : M.evalFrom S [] = M.εClosu
re S
· 使用定理 `εNFA.mem_εClosure_iff_exists_path`：mem_εClosure_iff_exists_path {s₁ s₂ :
 σ} : s₂ in M.εClosure {s₁} ↔ exists n, M.IsPath s₁ s₂ (.replicate n none) where
 mp h
· 使用定理 `List.reduceOption_replicate_none`：reduceOption_replicate_none {n : Nat} 
: (replicate n (@none α)).reduceOption = []
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `εNFA.evalFrom_append_singleton`：evalFrom_append_singleton (S : Set σ) (x
 : List α) (a : α) : M.evalFrom S (x ++ [a]) = M.stepSet (M.evalFrom S x) a
· 使用定理 `εNFA.mem_stepSet_iff`：mem_stepSet_iff : s in M.stepSet S a ↔ exists t in
 S, s in M.εClosure (M.step t a)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `εNFA.mem_εClosure_iff_exists`：mem_εClosure_iff_exists : s in M.εClosure 
S ↔ exists t in S, s in M.εClosure {t} where mp h
· 使用定理 `List.reduceOption_append`：reduceOption_append (l l' : List (Option α)) :
 (l ++ l').reduceOption = l.reduceOption ++ l'.reduceOption
· 使用定理 `List.reduceOption_cons_of_some`：reduceOption_cons_of_some (x : α) (l : L
ist (Option α)) : reduceOption (some x :: l) = x :: l.reduceOption
· 使用定理 `εNFA.isPath_append`：isPath_append {x y : List (Option α)} : M.IsPath s u
 (x ++ y) ↔ exists t, M.IsPath s t x ∧ M.IsPath t u y where mp
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem mem_evalFrom_iff_exists_path {s₁ s₂ : σ} {x : List α} :
    s₂ ∈ M.evalFrom {s₁} x ↔ ∃ x', x'.reduceOption = x ∧ M.IsPath s₁ s₂ x' := by
  induction x using List.reverseRecOn generalizing s₂ with
  | nil =>
    rw [evalFrom_nil, mem_εClosure_iff_exists_path]
    constructor
    · intro ⟨n, _⟩
      use List.replicate n none
      rw [List.reduceOption_replicate_none]
      trivial
    · simp_rw [List.reduceOption_eq_nil_iff]
      intro ⟨_, ⟨n, rfl⟩, h⟩
      exact ⟨n, h⟩
  | append_singleton x a ih =>
    rw [evalFrom_append_singleton, mem_stepSet_iff]
    constructor
    · intro ⟨t, ht, h⟩
      obtain ⟨x', _, _⟩ := ih.mp ht
      rw [mem_εClosure_iff_exists] at h
      simp_rw [mem_εClosure_iff_exists_path] at h
      obtain ⟨u, _, n, _⟩ := h
      use x' ++ some a :: List.replicate n none
      rw [List.reduceOption_append, List.reduceOption_cons_of_some,
        List.reduceOption_replicate_none, isPath_append]
      tauto
    · simp_rw [← List.concat_eq_append, List.reduceOption_eq_concat_iff,
        List.reduceOption_eq_nil_iff]
      intro ⟨_, ⟨x', _, rfl, _, n, rfl⟩, h⟩
      rw [isPath_append] at h
      obtain ⟨t, _, _ | u⟩ := h
      use t
      rw [mem_εClosure_iff_exists, ih]
      simp_rw [mem_εClosure_iff_exists_path]
      tauto
/-
**εNFA.mem_accepts_iff_exists_path** 是 Mathlib 中的一个定理，位于命名空间 `εNFA`。
形式化陈述：mem_accepts_iff_exists_path {x : List α} : x in M.accepts ↔ exists s₁ s₂ x
', s₁ in M.start ∧ s₂ in M.accept ∧ x'.reduceOption = x ∧ M.IsPath s₁ s₂ x' wher
e mp
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `εNFA.mem_evalFrom_iff_exists`：mem_evalFrom_iff_exists {s : σ} {S : Set σ
} {x : List α} : s in M.evalFrom S x ↔ exists t in S, s in M.evalFrom {t} x
· 使用定理 `εNFA.eval.eq_1`：∀ {α : Type u} {σ : Type v} (M : εNFA α σ), M.eval = M.e
valFrom M.start
· 使用定理 `εNFA.mem_evalFrom_iff_exists_path`：mem_evalFrom_iff_exists_path {s₁ s₂ :
 σ} {x : List α} : s₂ in M.evalFrom {s₁} x ↔ exists x', x'.reduceOption = x ∧ M.
IsPath s₁ s₂ x'
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem mem_accepts_iff_exists_path {x : List α} :
    x ∈ M.accepts ↔
      ∃ s₁ s₂ x', s₁ ∈ M.start ∧ s₂ ∈ M.accept ∧ x'.reduceOption = x ∧ M.IsPath s₁ s₂ x' where
  mp := by
    intro ⟨s₂, _, h⟩
    rw [eval, mem_evalFrom_iff_exists] at h
    obtain ⟨s₁, _, h⟩ := h
    rw [mem_evalFrom_iff_exists_path] at h
    tauto
  mpr := by
    intro ⟨s₁, s₂, x', hs₁, hs₂, h⟩
    have := M.mem_evalFrom_iff_exists.mpr ⟨_, hs₁, M.mem_evalFrom_iff_exists_path.mpr ⟨_, h⟩⟩
    exact ⟨s₂, hs₂, this⟩

/-! ### Conversions between `εNFA` and `NFA` -/


/-- `M.toNFA` is an `NFA` constructed from an `εNFA` `M`. -/
/-
**εNFA.toNFA** 是 Mathlib 中的一个定义，位于命名空间 `εNFA`。
形式化陈述：toNFA : NFA α σ where step S a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`M.toNFA` is an `NFA` constructed from an `εNFA` `M`.
-/
def toNFA : NFA α σ where
  step S a := M.εClosure (M.step S a)
  start := M.εClosure M.start
  accept := M.accept

@[simp]
/-
**εNFA.toNFA_evalFrom_match** 是 Mathlib 中的一个定理，位于命名空间 `εNFA`。
形式化陈述：toNFA_evalFrom_match (start : Set σ) : M.toNFA.evalFrom (M.εClosure start)
 = M.evalFrom start
参数：start : Set σ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toNFA_evalFrom_match (start : Set σ) :
    M.toNFA.evalFrom (M.εClosure start) = M.evalFrom start :=
  rfl

@[simp]
/-
**εNFA.toNFA_correct** 是 Mathlib 中的一个定理，位于命名空间 `εNFA`。
形式化陈述：toNFA_correct : M.toNFA.accepts = M.accepts
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toNFA_correct : M.toNFA.accepts = M.accepts :=
  rfl
/-
**εNFA.pumping_lemma** 是 Mathlib 中的一个定理，位于命名空间 `εNFA`。
形式化陈述：pumping_lemma [Fintype σ] {x : List α} (hx : x in M.accepts) (hlen : Finty
pe.card (Set σ) <= List.length x) : exists a b c, x = a ++ b ++ c ∧ a.length + b
.length <= Fintype.card (Set σ) ∧ b != [] ∧ {a} * {b}∗ * {c} <= M.accepts
参数：hx : x in M.accepts；hlen : Fintype.card (Set σ) <= List.length x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NFA.pumping_lemma`：pumping_lemma [Fintype σ] {x : List α} (hx : x in M.a
ccepts) (hlen : Fintype.card (Set σ) <= List.length x) : exists a b c, x = a ++ 
b ++ c …
-/
theorem pumping_lemma [Fintype σ] {x : List α} (hx : x ∈ M.accepts)
    (hlen : Fintype.card (Set σ) ≤ List.length x) :
    ∃ a b c, x = a ++ b ++ c ∧
      a.length + b.length ≤ Fintype.card (Set σ) ∧ b ≠ [] ∧ {a} * {b}∗ * {c} ≤ M.accepts :=
  M.toNFA.pumping_lemma hx hlen

end εNFA

namespace NFA

/-- `M.toεNFA` is an `εNFA` constructed from an `NFA` `M` by using the same start and accept
  states and transition functions. -/
/-
**NFA.to** 是 Mathlib 中的一个定义，位于命名空间 `NFA`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`M.toεNFA` is an `εNFA` constructed from an `NFA` `M` by using the same start an
d accept
  states and transition functions.
-/
def toεNFA (M : NFA α σ) : εNFA α σ where
  step s a := a.casesOn' ∅ fun a ↦ M.step s a
  start := M.start
  accept := M.accept

@[simp]
/-
**NFA.to** 是 Mathlib 中的一个定理，位于命名空间 `NFA`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toεNFA_εClosure (M : NFA α σ) (S : Set σ) : M.toεNFA.εClosure S = S := by
  ext a
  refine ⟨?_, εNFA.εClosure.base _⟩
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩)
  · exact h
  · cases h

@[simp]
/-
**NFA.to** 是 Mathlib 中的一个定理，位于命名空间 `NFA`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toεNFA_evalFrom_match (M : NFA α σ) (start : Set σ) :
    M.toεNFA.evalFrom start = M.evalFrom start := by
  rw [evalFrom, εNFA.evalFrom, toεNFA_εClosure]
  suffices εNFA.stepSet (toεNFA M) = stepSet M by rw [this]
  ext S s
  simp only [stepSet, εNFA.stepSet, exists_prop, Set.mem_iUnion]
  apply exists_congr
  simp only [and_congr_right_iff]
  intro _ _
  rw [M.toεNFA_εClosure]
  rfl

@[simp]
/-
**NFA.to** 是 Mathlib 中的一个定理，位于命名空间 `NFA`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toεNFA_correct (M : NFA α σ) : M.toεNFA.accepts = M.accepts := by
  rw [εNFA.accepts, εNFA.eval, toεNFA_evalFrom_match]
  rfl

end NFA

/-! ### Regex-like operations -/


namespace εNFA

/-
**εNFA.** 是 Mathlib 中的一个实例，位于命名空间 `εNFA`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (εNFA α σ) :=
  ⟨⟨fun _ _ ↦ ∅, ∅, ∅⟩⟩
/-
**εNFA.** 是 Mathlib 中的一个实例，位于命名空间 `εNFA`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (εNFA α σ) :=
  ⟨⟨fun _ _ ↦ ∅, univ, univ⟩⟩
/-
**εNFA.** 是 Mathlib 中的一个实例，位于命名空间 `εNFA`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (εNFA α σ) :=
  ⟨0⟩

@[simp]
/-
**εNFA.step_zero** 是 Mathlib 中的一个定理，位于命名空间 `εNFA`。
形式化陈述：step_zero (s a) : (0 : εNFA α σ).step s a = ∅
参数：s a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem step_zero (s a) : (0 : εNFA α σ).step s a = ∅ :=
  rfl

@[simp]
/-
**εNFA.step_one** 是 Mathlib 中的一个定理，位于命名空间 `εNFA`。
形式化陈述：step_one (s a) : (1 : εNFA α σ).step s a = ∅
参数：s a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem step_one (s a) : (1 : εNFA α σ).step s a = ∅ :=
  rfl

@[simp]
/-
**εNFA.start_zero** 是 Mathlib 中的一个定理，位于命名空间 `εNFA`。
形式化陈述：start_zero : (0 : εNFA α σ).start = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem start_zero : (0 : εNFA α σ).start = ∅ :=
  rfl

@[simp]
/-
**εNFA.start_one** 是 Mathlib 中的一个定理，位于命名空间 `εNFA`。
形式化陈述：start_one : (1 : εNFA α σ).start = univ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem start_one : (1 : εNFA α σ).start = univ :=
  rfl

@[simp]
/-
**εNFA.accept_zero** 是 Mathlib 中的一个定理，位于命名空间 `εNFA`。
形式化陈述：accept_zero : (0 : εNFA α σ).accept = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem accept_zero : (0 : εNFA α σ).accept = ∅ :=
  rfl

@[simp]
/-
**εNFA.accept_one** 是 Mathlib 中的一个定理，位于命名空间 `εNFA`。
形式化陈述：accept_one : (1 : εNFA α σ).accept = univ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem accept_one : (1 : εNFA α σ).accept = univ :=
  rfl

end εNFA

