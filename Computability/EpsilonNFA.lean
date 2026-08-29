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

/--
Definition of `εNFA` / `εNFA` 的定义

English:
structure εNFA
  parameters: (α : Type u) (σ : Type v)
  axioms and operations (3):
    - step : σ -> Option α -> Set σ
    - start : Set σ
    - accept : Set σ

中文:
结构 εNFA
  参数: (α : 类型u) (σ : 类型v)
  公理与运算 (3 个):
    - step : σ -> Option α -> Set σ
    - start : Set σ
    - accept : Set σ
-/
structure εNFA (α : Type u) (σ : Type v) where
  /-- Transition function. The automaton is rendered non-deterministic by this transition function
  returning `Set σ` (rather than `σ`), and ε-transitions are made possible by taking `Option α`
  (rather than `α`). -/
  step : σ -> Option α -> Set σ
  /-- Starting states. -/
  start : Set σ
  /-- Set of acceptance states. -/
  accept : Set σ

variable {α : Type u} {σ : Type v} (M : εNFA α σ) {S : Set σ} {s t u : σ} {a : α}

namespace εNFA

/--
Inductive type `εClosure` / 归纳类型 `εClosure`

English:
inductive εClosure
  parameters: (S : Set σ)
  constructors (2):
    - base: forall s in S, εClosure S s
    - step: forall (s), forall t in M.step s none, εClosure S s -> εClosure S t

中文:
归纳类型 εClosure
  参数: (S : Set σ)
  构造子 (2 个):
    - base: 对任意 s in S, εClosure S s
    - step: 对任意 (s), 对任意 t in M.step s none, εClosure S s -> εClosure S t
-/
inductive εClosure (S : Set σ) : Set σ
  | base : forall s in S, εClosure S s
  | step : forall (s), forall t in M.step s none, εClosure S s -> εClosure S t

@[simp]
/--
theorem `subset_εClosure` / 定理 `subset_εClosure`

English:
theorem subset_εClosure
  given: (S : Set σ)
  statement: S subseteq M.εClosure S
  proof: εClosure.base

@[simp]

中文:
定理 subset_εClosure
  条件: (S : Set σ)
  结论: S subseteq M.εClosure S
  证明: εClosure.base

@[simp]

Depends on / 依赖: Closure.base
-/
theorem subset_εClosure (S : Set σ) : S subseteq M.εClosure S :=
  εClosure.base

@[simp]
/--
theorem `εClosure_empty` / 定理 `εClosure_empty`

English:
theorem εClosure_empty
  statement: M.εClosure ∅ = ∅
  proof: eq_empty_of_forall_notMem fun s hs => by induction hs <;> assumption

@[simp]

中文:
定理 εClosure_empty
  结论: M.εClosure ∅ = ∅
  证明: eq_empty_of_forall_notMem fun s hs => by induction hs <;> assumption

@[simp]

Depends on / 依赖: eq_empty_of_forall_notMem
-/
theorem εClosure_empty : M.εClosure ∅ = ∅ :=
  eq_empty_of_forall_notMem fun s hs => by induction hs <;> assumption

@[simp]
/--
theorem `εClosure_univ` / 定理 `εClosure_univ`

English:
theorem εClosure_univ
  statement: M.εClosure univ = univ
  proof: eq_univ_of_univ_subset subset_εClosure _ _

中文:
定理 εClosure_univ
  结论: M.εClosure univ = univ
  证明: eq_univ_of_univ_subset subset_εClosure _ _

Depends on / 依赖: eq_univ_of_univ_subset
-/
theorem εClosure_univ : M.εClosure univ = univ :=
eq_univ_of_univ_subset subset_εClosure _ _

/--
theorem `mem_εClosure_iff_exists` / 定理 `mem_εClosure_iff_exists`

English:
theorem mem_εClosure_iff_exists
  statement: s in M.εClosure S ↔ exists t in S, s in M.εClosure {t} where
  proof: by
    induction h with
    | base => tauto
    | step _ _ _ _ ih =>
      obtain ⟨s, _, _⟩ := ih
      use s
      solve_by_elim [εClosure.step]
  mpr := by
    intro ⟨t, _, h⟩
    induction h <;> subst_vars <;> solve_by_elim [εClosure.step]

中文:
定理 mem_εClosure_iff_exists
  结论: s in M.εClosure S ↔ 存在 t in S, s in M.εClosure {t} where
  证明: by
    induction h with
    | base => tauto
    | step _ _ _ _ ih =>
      obtain ⟨s, _, _⟩ := ih
      use s
      solve_by_elim [εClosure.step]
  mpr := by
    intro ⟨t, _, h⟩
    induction h <;> subst_vars <;> solve_by_elim [εClosure.step]

Depends on / 依赖: Closure.step, solve_by_elim
-/
theorem mem_εClosure_iff_exists : s in M.εClosure S ↔ exists t in S, s in M.εClosure {t} where
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

/--
Definition of `stepSet` / `stepSet` 的定义

English:
definition stepSet
  signature: (S : Set σ) (a : α)
  body: ⋃ s in S, M.εClosure (M.step s a)

中文:
定义 stepSet
  签名: (S : Set σ) (a : α)
  定义体: ⋃ s in S, M.εClosure (M.step s a)

Depends on / 依赖: M.step
-/
def stepSet (S : Set σ) (a : α) : Set σ :=
  ⋃ s in S, M.εClosure (M.step s a)

variable {M}

@[simp]
/--
theorem `mem_stepSet_iff` / 定理 `mem_stepSet_iff`

English:
theorem mem_stepSet_iff
  statement: s in M.stepSet S a ↔ exists t in S, s in M.εClosure (M.step t a)
  proof: by
  simp_rw [stepSet, mem_iUnion₂, exists_prop]

@[simp]

中文:
定理 mem_stepSet_iff
  结论: s in M.stepSet S a ↔ 存在 t in S, s in M.εClosure (M.step t a)
  证明: by
  simp_rw [stepSet, mem_iUnion₂, exists_prop]

@[simp]

Depends on / 依赖: exists_prop, simp_rw, stepSet
-/
theorem mem_stepSet_iff : s in M.stepSet S a ↔ exists t in S, s in M.εClosure (M.step t a) := by
  simp_rw [stepSet, mem_iUnion₂, exists_prop]

@[simp]
/--
theorem `stepSet_empty` / 定理 `stepSet_empty`

English:
theorem stepSet_empty
  given: (a : α)
  statement: M.stepSet ∅ a = ∅
  proof: by
  simp_rw [stepSet, mem_empty_iff_false, iUnion_false, iUnion_empty]

中文:
定理 stepSet_empty
  条件: (a : α)
  结论: M.stepSet ∅ a = ∅
  证明: by
  simp_rw [stepSet, mem_empty_iff_false, iUnion_false, iUnion_empty]

Depends on / 依赖: iUnion_empty, iUnion_false, mem_empty_iff_false, simp_rw, stepSet
-/
theorem stepSet_empty (a : α) : M.stepSet ∅ a = ∅ := by
  simp_rw [stepSet, mem_empty_iff_false, iUnion_false, iUnion_empty]

variable (M)

/--
Definition of `evalFrom` / `evalFrom` 的定义

English:
definition evalFrom
  signature: (start : Set σ)
  body: List.foldl M.stepSet (M.εClosure start)

@[simp]

中文:
定义 evalFrom
  签名: (start : Set σ)
  定义体: List.foldl M.stepSet (M.εClosure start)

@[simp]

Depends on / 依赖: List.foldl, M.stepSet, stepSet
-/
def evalFrom (start : Set σ) : List α -> Set σ :=
  List.foldl M.stepSet (M.εClosure start)

@[simp]
/--
theorem `evalFrom_nil` / 定理 `evalFrom_nil`

English:
theorem evalFrom_nil
  given: (S : Set σ)
  statement: M.evalFrom S [] = M.εClosure S
  proof: rfl

@[simp]

中文:
定理 evalFrom_nil
  条件: (S : Set σ)
  结论: M.evalFrom S [] = M.εClosure S
  证明: rfl

@[simp]
-/
theorem evalFrom_nil (S : Set σ) : M.evalFrom S [] = M.εClosure S :=
  rfl

@[simp]
/--
theorem `evalFrom_singleton` / 定理 `evalFrom_singleton`

English:
theorem evalFrom_singleton
  given: (S : Set σ) (a : α)
  statement: M.evalFrom S [a] = M.stepSet (M.εClosure S) a
  proof: rfl

@[simp]

中文:
定理 evalFrom_singleton
  条件: (S : Set σ) (a : α)
  结论: M.evalFrom S [a] = M.stepSet (M.εClosure S) a
  证明: rfl

@[simp]
-/
theorem evalFrom_singleton (S : Set σ) (a : α) : M.evalFrom S [a] = M.stepSet (M.εClosure S) a :=
  rfl

@[simp]
/--
theorem `evalFrom_append_singleton` / 定理 `evalFrom_append_singleton`

English:
theorem evalFrom_append_singleton
  given: (S : Set σ) (x : List α) (a : α)
  proof: by
  rw [evalFrom]; rw [List.foldl_append]; rw [List.foldl_cons]; rw [List.foldl_nil]

@[simp]

中文:
定理 evalFrom_append_singleton
  条件: (S : Set σ) (x : List α) (a : α)
  证明: by
  rw [evalFrom]; rw [List.foldl_append]; rw [List.foldl_cons]; rw [List.foldl_nil]

@[simp]

Depends on / 依赖: List.foldl_append, List.foldl_cons, List.foldl_nil, evalFrom, foldl_append, foldl_cons, foldl_nil
-/
theorem evalFrom_append_singleton (S : Set σ) (x : List α) (a : α) :
    M.evalFrom S (x ++ [a]) = M.stepSet (M.evalFrom S x) a := by
  rw [evalFrom]; rw [List.foldl_append]; rw [List.foldl_cons]; rw [List.foldl_nil]

@[simp]
/--
theorem `evalFrom_empty` / 定理 `evalFrom_empty`

English:
theorem evalFrom_empty
  given: (x : List α)
  statement: M.evalFrom ∅ x = ∅
  proof: by
  induction x using List.reverseRecOn with
  | nil => rw [evalFrom_nil, εClosure_empty]
  | append_singleton x a ih => rw [evalFrom_append_singleton, ih, stepSet_empty]

中文:
定理 evalFrom_empty
  条件: (x : List α)
  结论: M.evalFrom ∅ x = ∅
  证明: by
  induction x using List.reverseRecOn with
  | nil => rw [evalFrom_nil, εClosure_empty]
  | append_singleton x a ih => rw [evalFrom_append_singleton, ih, stepSet_empty]

Depends on / 依赖: List.reverseRecOn, append_singleton, evalFrom_append_singleton, evalFrom_nil, reverseRecOn, stepSet_empty
-/
theorem evalFrom_empty (x : List α) : M.evalFrom ∅ x = ∅ := by
  induction x using List.reverseRecOn with
  | nil => rw [evalFrom_nil, εClosure_empty]
  | append_singleton x a ih => rw [evalFrom_append_singleton, ih, stepSet_empty]

/--
theorem `mem_evalFrom_iff_exists` / 定理 `mem_evalFrom_iff_exists`

English:
theorem mem_evalFrom_iff_exists
  given: {s : σ} {S : Set σ} {x : List α}
  proof: by
  induction x using List.reverseRecOn generalizing s with
  | nil => apply mem_εClosure_iff_exists
  | append_singleton _ _ ih =>
    simp_rw [evalFrom_append_singleton, mem_stepSet_iff, ih]
    tauto

中文:
定理 mem_evalFrom_iff_exists
  条件: {s : σ} {S : Set σ} {x : List α}
  证明: by
  induction x using List.reverseRecOn generalizing s with
  | nil => apply mem_εClosure_iff_exists
  | append_singleton _ _ ih =>
    simp_rw [evalFrom_append_singleton, mem_stepSet_iff, ih]
    tauto

Depends on / 依赖: List.reverseRecOn, append_singleton, evalFrom_append_singleton, generalizing, mem_stepSet_iff, reverseRecOn, simp_rw
-/
theorem mem_evalFrom_iff_exists {s : σ} {S : Set σ} {x : List α} :
    s in M.evalFrom S x ↔ exists t in S, s in M.evalFrom {t} x := by
  induction x using List.reverseRecOn generalizing s with
  | nil => apply mem_εClosure_iff_exists
  | append_singleton _ _ ih =>
    simp_rw [evalFrom_append_singleton, mem_stepSet_iff, ih]
    tauto

/--
Definition of `eval` / `eval` 的定义

English:
definition eval
  body: M.evalFrom M.start

@[simp]

中文:
定义 eval
  定义体: M.evalFrom M.start

@[simp]

Depends on / 依赖: M.evalFrom, M.start, evalFrom
-/
def eval :=
  M.evalFrom M.start

@[simp]
/--
theorem `eval_nil` / 定理 `eval_nil`

English:
theorem eval_nil
  statement: M.eval [] = M.εClosure M.start
  proof: rfl

@[simp]

中文:
定理 eval_nil
  结论: M.eval [] = M.εClosure M.start
  证明: rfl

@[simp]
-/
theorem eval_nil : M.eval [] = M.εClosure M.start :=
  rfl

@[simp]
/--
theorem `eval_singleton` / 定理 `eval_singleton`

English:
theorem eval_singleton
  given: (a : α)
  statement: M.eval [a] = M.stepSet (M.εClosure M.start) a
  proof: rfl

@[simp]

中文:
定理 eval_singleton
  条件: (a : α)
  结论: M.eval [a] = M.stepSet (M.εClosure M.start) a
  证明: rfl

@[simp]
-/
theorem eval_singleton (a : α) : M.eval [a] = M.stepSet (M.εClosure M.start) a :=
  rfl

@[simp]
/--
theorem `eval_append_singleton` / 定理 `eval_append_singleton`

English:
theorem eval_append_singleton
  given: (x : List α) (a : α)
  statement: M.eval (x ++ [a]) = M.stepSet (M.eval x) a
  proof: evalFrom_append_singleton _ _ _ _

中文:
定理 eval_append_singleton
  条件: (x : List α) (a : α)
  结论: M.eval (x ++ [a]) = M.stepSet (M.eval x) a
  证明: evalFrom_append_singleton _ _ _ _

Depends on / 依赖: evalFrom_append_singleton
-/
theorem eval_append_singleton (x : List α) (a : α) : M.eval (x ++ [a]) = M.stepSet (M.eval x) a :=
  evalFrom_append_singleton _ _ _ _

/--
Definition of `accepts` / `accepts` 的定义

English:
definition accepts
  signature: : Language α
  body: { x | exists S in M.accept, S in M.eval x }

中文:
定义 accepts
  签名: : Language α
  定义体: { x | exists S in M.accept, S in M.eval x }

Depends on / 依赖: M.accept, M.eval, accept
-/
def accepts : Language α :=
  { x | exists S in M.accept, S in M.eval x }

/-- `M.IsPath` represents a traversal in `M` from a start state to an end state by following a list
of transitions in order. -/
@[mk_iff]
/--
Inductive type `IsPath` / 归纳类型 `IsPath`

English:
inductive IsPath
  parameters: : σ -> σ -> List (Option α) -> Prop
  constructors (2):
    - nil: (s : σ) : IsPath s s []
    - cons: (t s u : σ) (a : Option α) (x : List (Option α)) : t in M.step s a -> IsPath t u x -> IsPath s u (a :: x)

中文:
归纳类型 IsPath
  参数: : σ -> σ -> List (Option α) -> 命题
  构造子 (2 个):
    - nil: (s : σ) : IsPath s s []
    - cons: (t s u : σ) (a : Option α) (x : List (Option α)) : t in M.step s a -> IsPath t u x -> IsPath s u (a :: x)
-/
inductive IsPath : σ -> σ -> List (Option α) -> Prop
  | nil (s : σ) : IsPath s s []
  | cons (t s u : σ) (a : Option α) (x : List (Option α)) :
      t in M.step s a -> IsPath t u x -> IsPath s u (a :: x)

@[simp]
/--
theorem `isPath_nil` / 定理 `isPath_nil`

English:
theorem isPath_nil
  statement: M.IsPath s t [] ↔ s = t
  proof: by
  rw [isPath_iff]
  simp [eq_comm]

alias ⟨IsPath.eq_of_nil, _⟩ := isPath_nil

@[simp]

中文:
定理 isPath_nil
  结论: M.IsPath s t [] ↔ s = t
  证明: by
  rw [isPath_iff]
  simp [eq_comm]

alias ⟨IsPath.eq_of_nil, _⟩ := isPath_nil

@[simp]

Depends on / 依赖: eq_comm, isPath_iff
-/
theorem isPath_nil : M.IsPath s t [] ↔ s = t := by
  rw [isPath_iff]
  simp [eq_comm]

alias ⟨IsPath.eq_of_nil, _⟩ := isPath_nil

@[simp]
/--
theorem `isPath_singleton` / 定理 `isPath_singleton`

English:
theorem isPath_singleton
  given: {a : Option α}
  statement: M.IsPath s t [a] ↔ t in M.step s a where
  proof: by
    rintro (_ | ⟨_, _, _, _, _, _, ⟨⟩⟩)
    assumption
  mpr := by tauto

alias ⟨_, IsPath.singleton⟩ := isPath_singleton

中文:
定理 isPath_singleton
  条件: {a : Option α}
  结论: M.IsPath s t [a] ↔ t in M.step s a where
  证明: by
    rintro (_ | ⟨_, _, _, _, _, _, ⟨⟩⟩)
    assumption
  mpr := by tauto

alias ⟨_, IsPath.singleton⟩ := isPath_singleton
-/
theorem isPath_singleton {a : Option α} : M.IsPath s t [a] ↔ t in M.step s a where
  mp := by
    rintro (_ | ⟨_, _, _, _, _, _, ⟨⟩⟩)
    assumption
  mpr := by tauto

alias ⟨_, IsPath.singleton⟩ := isPath_singleton

/--
theorem `isPath_append` / 定理 `isPath_append`

English:
theorem isPath_append
  given: {x y : List (Option α)}
  proof: by
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

中文:
定理 isPath_append
  条件: {x y : List (Option α)}
  证明: by
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

Depends on / 依赖: List.nil_append, generalizing, nil_append
-/
theorem isPath_append {x y : List (Option α)} :
    M.IsPath s u (x ++ y) ↔ exists t, M.IsPath s t x ∧ M.IsPath t u y where
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

/--
theorem `mem_εClosure_iff_exists_path` / 定理 `mem_εClosure_iff_exists_path`

English:
theorem mem_εClosure_iff_exists_path
  given: {s₁ s₂ : σ}
  proof: by
    induction h with
    | base t =>
      use 0
      subst t
      apply IsPath.nil
    | step _ _ _ _ ih =>
      obtain ⟨n, _⟩ := ih
      use n + 1
      rw [List.replicate_add]; rw [isPath_append]
      tauto
  mpr := by
    intro ⟨n, h⟩
    induction n generalizing s₂
    · rw [List.replic

中文:
定理 mem_εClosure_iff_exists_path
  条件: {s₁ s₂ : σ}
  证明: by
    induction h with
    | base t =>
      use 0
      subst t
      apply IsPath.nil
    | step _ _ _ _ ih =>
      obtain ⟨n, _⟩ := ih
      use n + 1
      rw [List.replicate_add]; rw [isPath_append]
      tauto
  mpr := by
    intro ⟨n, h⟩
    induction n generalizing s₂
    · rw [List.replic

Depends on / 依赖: Closure.step, IsPath, IsPath.eq_of_nil, IsPath.nil, List.replicate_add, List.replicate_one, List.replicate_zero, eq_of_nil, generalizing, isPath_append, isPath_singleton, replicate_add, replicate_one, replicate_zero, simp_rw, solve_by_elim
-/
theorem mem_εClosure_iff_exists_path {s₁ s₂ : σ} :
    s₂ in M.εClosure {s₁} ↔ exists n, M.IsPath s₁ s₂ (.replicate n none) where
  mp h := by
    induction h with
    | base t =>
      use 0
      subst t
      apply IsPath.nil
    | step _ _ _ _ ih =>
      obtain ⟨n, _⟩ := ih
      use n + 1
      rw [List.replicate_add]; rw [isPath_append]
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

/--
theorem `mem_evalFrom_iff_exists_path` / 定理 `mem_evalFrom_iff_exists_path`

English:
theorem mem_evalFrom_iff_exists_path
  given: {s₁ s₂ : σ} {x : List α}
  proof: by
  induction x using List.reverseRecOn generalizing s₂ with
  | nil =>
    rw [evalFrom_nil]; rw [mem_εClosure_iff_exists_path]
    constructor
    · intro ⟨n, _⟩
      use List.replicate n none
      rw [List.reduceOption_replicate_none]
      trivial
    · simp_rw [List.reduceOption_eq_nil_iff]


中文:
定理 mem_evalFrom_iff_exists_path
  条件: {s₁ s₂ : σ} {x : List α}
  证明: by
  induction x using List.reverseRecOn generalizing s₂ with
  | nil =>
    rw [evalFrom_nil]; rw [mem_εClosure_iff_exists_path]
    constructor
    · intro ⟨n, _⟩
      use List.replicate n none
      rw [List.reduceOption_replicate_none]
      trivial
    · simp_rw [List.reduceOption_eq_nil_iff]


Depends on / 依赖: List.reduceOption_eq_nil_iff, List.reduceOption_replicate_none, List.replicate, List.reverseRecOn, append_singleton, evalFrom_append_singleton, evalFrom_nil, generalizing, ih.mp, mem_stepSet_iff, reduceOption_eq_nil_iff, reduceOption_replicate_none, replicate, reverseRecOn, simp_rw
-/
theorem mem_evalFrom_iff_exists_path {s₁ s₂ : σ} {x : List α} :
    s₂ in M.evalFrom {s₁} x ↔ exists x', x'.reduceOption = x ∧ M.IsPath s₁ s₂ x' := by
  induction x using List.reverseRecOn generalizing s₂ with
  | nil =>
    rw [evalFrom_nil]; rw [mem_εClosure_iff_exists_path]
    constructor
    · intro ⟨n, _⟩
      use List.replicate n none
      rw [List.reduceOption_replicate_none]
      trivial
    · simp_rw [List.reduceOption_eq_nil_iff]
      intro ⟨_, ⟨n, rfl⟩, h⟩
      exact ⟨n, h⟩
  | append_singleton x a ih =>
    rw [evalFrom_append_singleton]; rw [mem_stepSet_iff]
    constructor
    · intro ⟨t, ht, h⟩
      obtain ⟨x', _, _⟩ := ih.mp ht
      rw [mem_εClosure_iff_exists] at h
      simp_rw [mem_εClosure_iff_exists_path] at h
      obtain ⟨u, _, n, _⟩ := h
      use x' ++ some a :: List.replicate n none
      rw [List.reduceOption_append]; rw [List.reduceOption_cons_of_some]; rw [List.reduceOption_replicate_none]; rw [isPath_append]
      tauto
    · simp_rw [← List.concat_eq_append, List.reduceOption_eq_concat_iff,
        List.reduceOption_eq_nil_iff]
      intro ⟨_, ⟨x', _, rfl, _, n, rfl⟩, h⟩
      rw [isPath_append] at h
      obtain ⟨t, _, _ | u⟩ := h
      use t
      rw [mem_εClosure_iff_exists]; rw [ih]
      simp_rw [mem_εClosure_iff_exists_path]
      tauto

/--
theorem `mem_accepts_iff_exists_path` / 定理 `mem_accepts_iff_exists_path`

English:
theorem mem_accepts_iff_exists_path
  given: {x : List α}
  proof: by
    intro ⟨s₂, _, h⟩
    rw [eval]; rw [mem_evalFrom_iff_exists] at h
    obtain ⟨s₁, _, h⟩ := h
    rw [mem_evalFrom_iff_exists_path] at h
    tauto
  mpr := by
    intro ⟨s₁, s₂, x', hs₁, hs₂, h⟩
    have := M.mem_evalFrom_iff_exists.mpr ⟨_, hs₁, M.mem_evalFrom_iff_exists_path.mpr ⟨_, h⟩⟩
    e

中文:
定理 mem_accepts_iff_exists_path
  条件: {x : List α}
  证明: by
    intro ⟨s₂, _, h⟩
    rw [eval]; rw [mem_evalFrom_iff_exists] at h
    obtain ⟨s₁, _, h⟩ := h
    rw [mem_evalFrom_iff_exists_path] at h
    tauto
  mpr := by
    intro ⟨s₁, s₂, x', hs₁, hs₂, h⟩
    have := M.mem_evalFrom_iff_exists.mpr ⟨_, hs₁, M.mem_evalFrom_iff_exists_path.mpr ⟨_, h⟩⟩
    e

Depends on / 依赖: M.mem_evalFrom_iff_exists.mpr, M.mem_evalFrom_iff_exists_path.mpr, mem_evalFrom_iff_exists, mem_evalFrom_iff_exists_path
-/
theorem mem_accepts_iff_exists_path {x : List α} :
    x in M.accepts ↔
      exists s₁ s₂ x', s₁ in M.start ∧ s₂ in M.accept ∧ x'.reduceOption = x ∧ M.IsPath s₁ s₂ x' where
  mp := by
    intro ⟨s₂, _, h⟩
    rw [eval]; rw [mem_evalFrom_iff_exists] at h
    obtain ⟨s₁, _, h⟩ := h
    rw [mem_evalFrom_iff_exists_path] at h
    tauto
  mpr := by
    intro ⟨s₁, s₂, x', hs₁, hs₂, h⟩
    have := M.mem_evalFrom_iff_exists.mpr ⟨_, hs₁, M.mem_evalFrom_iff_exists_path.mpr ⟨_, h⟩⟩
    exact ⟨s₂, hs₂, this⟩

/-! ### Conversions between `εNFA` and `NFA` -/


/--
Definition of `toNFA` / `toNFA` 的定义

English:
definition toNFA
  signature: : NFA α σ where
  body: M.εClosure (M.step S a)
  start := M.εClosure M.start
  accept := M.accept

@[simp]

中文:
定义 toNFA
  签名: : NFA α σ where
  定义体: M.εClosure (M.step S a)
  start := M.εClosure M.start
  accept := M.accept

@[simp]

Depends on / 依赖: M.step
-/
def toNFA : NFA α σ where
  step S a := M.εClosure (M.step S a)
  start := M.εClosure M.start
  accept := M.accept

@[simp]
/--
theorem `toNFA_evalFrom_match` / 定理 `toNFA_evalFrom_match`

English:
theorem toNFA_evalFrom_match
  given: (start : Set σ)
  proof: rfl

@[simp]

中文:
定理 toNFA_evalFrom_match
  条件: (start : Set σ)
  证明: rfl

@[simp]
-/
theorem toNFA_evalFrom_match (start : Set σ) :
    M.toNFA.evalFrom (M.εClosure start) = M.evalFrom start :=
  rfl

@[simp]
/--
theorem `toNFA_correct` / 定理 `toNFA_correct`

English:
theorem toNFA_correct
  statement: M.toNFA.accepts = M.accepts
  proof: rfl

中文:
定理 toNFA_correct
  结论: M.toNFA.accepts = M.accepts
  证明: rfl
-/
theorem toNFA_correct : M.toNFA.accepts = M.accepts :=
  rfl

/--
theorem `pumping_lemma` / 定理 `pumping_lemma`

English:
theorem pumping_lemma
  statement: [Fintype σ] {x : List α} (hx : x in M.accepts)
  proof: M.toNFA.pumping_lemma hx hlen

中文:
定理 pumping_lemma
  结论: [Fintype σ] {x : List α} (hx : x in M.accepts)
  证明: M.toNFA.pumping_lemma hx hlen

Depends on / 依赖: M.toNFA.pumping_lemma, pumping_lemma
-/
theorem pumping_lemma [Fintype σ] {x : List α} (hx : x in M.accepts)
    (hlen : Fintype.card (Set σ) <= List.length x) :
    exists a b c, x = a ++ b ++ c ∧
      a.length + b.length <= Fintype.card (Set σ) ∧ b != [] ∧ {a} * {b}∗ * {c} <= M.accepts :=
  M.toNFA.pumping_lemma hx hlen

end εNFA

namespace NFA

/--
Definition of `toεNFA` / `toεNFA` 的定义

English:
definition toεNFA
  signature: (M : NFA α σ)
  body: a.casesOn' ∅ fun a => M.step s a
  start := M.start
  accept := M.accept

@[simp]

中文:
定义 toεNFA
  签名: (M : NFA α σ)
  定义体: a.casesOn' ∅ fun a => M.step s a
  start := M.start
  accept := M.accept

@[simp]

Depends on / 依赖: M.step, a.casesOn, casesOn
-/
def toεNFA (M : NFA α σ) : εNFA α σ where
  step s a := a.casesOn' ∅ fun a => M.step s a
  start := M.start
  accept := M.accept

@[simp]
/--
theorem `toεNFA_εClosure` / 定理 `toεNFA_εClosure`

English:
theorem toεNFA_εClosure
  given: (M : NFA α σ) (S : Set σ)
  statement: M.toεNFA.εClosure S = S
  proof: by
  ext a
  refine ⟨?_, εNFA.εClosure.base _⟩
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩)
  · exact h
  · cases h

@[simp]

中文:
定理 toεNFA_εClosure
  条件: (M : NFA α σ) (S : Set σ)
  结论: M.toεNFA.εClosure S = S
  证明: by
  ext a
  refine ⟨?_, εNFA.εClosure.base _⟩
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩)
  · exact h
  · cases h

@[simp]

Depends on / 依赖: Closure.base
-/
theorem toεNFA_εClosure (M : NFA α σ) (S : Set σ) : M.toεNFA.εClosure S = S := by
  ext a
  refine ⟨?_, εNFA.εClosure.base _⟩
  rintro (⟨_, h⟩ | ⟨_, _, h, _⟩)
  · exact h
  · cases h

@[simp]
/--
theorem `toεNFA_evalFrom_match` / 定理 `toεNFA_evalFrom_match`

English:
theorem toεNFA_evalFrom_match
  given: (M : NFA α σ) (start : Set σ)
  proof: by
  rw [evalFrom]; rw [εNFA.evalFrom]; rw [toεNFA_εClosure]
  suffices εNFA.stepSet (toεNFA M) = stepSet M by rw [this]
  ext S s
  simp only [stepSet, εNFA.stepSet, exists_prop, Set.mem_iUnion]
  apply exists_congr
  simp only [and_congr_right_iff]
  intro _ _
  rw [M.toεNFA_εClosure]
  rfl

@[sim

中文:
定理 toεNFA_evalFrom_match
  条件: (M : NFA α σ) (start : Set σ)
  证明: by
  rw [evalFrom]; rw [εNFA.evalFrom]; rw [toεNFA_εClosure]
  suffices εNFA.stepSet (toεNFA M) = stepSet M by rw [this]
  ext S s
  simp only [stepSet, εNFA.stepSet, exists_prop, Set.mem_iUnion]
  apply exists_congr
  simp only [and_congr_right_iff]
  intro _ _
  rw [M.toεNFA_εClosure]
  rfl

@[sim

Depends on / 依赖: M.to, NFA.evalFrom, NFA.stepSet, Set.mem_iUnion, and_congr_right_iff, evalFrom, exists_congr, exists_prop, mem_iUnion, stepSet
-/
theorem toεNFA_evalFrom_match (M : NFA α σ) (start : Set σ) :
    M.toεNFA.evalFrom start = M.evalFrom start := by
  rw [evalFrom]; rw [εNFA.evalFrom]; rw [toεNFA_εClosure]
  suffices εNFA.stepSet (toεNFA M) = stepSet M by rw [this]
  ext S s
  simp only [stepSet, εNFA.stepSet, exists_prop, Set.mem_iUnion]
  apply exists_congr
  simp only [and_congr_right_iff]
  intro _ _
  rw [M.toεNFA_εClosure]
  rfl

@[simp]
/--
theorem `toεNFA_correct` / 定理 `toεNFA_correct`

English:
theorem toεNFA_correct
  given: (M : NFA α σ)
  statement: M.toεNFA.accepts = M.accepts
  proof: by
  rw [εNFA.accepts]; rw [εNFA.eval]; rw [toεNFA_evalFrom_match]
  rfl

中文:
定理 toεNFA_correct
  条件: (M : NFA α σ)
  结论: M.toεNFA.accepts = M.accepts
  证明: by
  rw [εNFA.accepts]; rw [εNFA.eval]; rw [toεNFA_evalFrom_match]
  rfl

Depends on / 依赖: NFA.accepts, NFA.eval, accepts
-/
theorem toεNFA_correct (M : NFA α σ) : M.toεNFA.accepts = M.accepts := by
  rw [εNFA.accepts]; rw [εNFA.eval]; rw [toεNFA_evalFrom_match]
  rfl

end NFA

/-! ### Regex-like operations -/


namespace εNFA

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (εNFA α σ)
  body: ⟨⟨fun _ _ => ∅, ∅, ∅⟩⟩

中文:
实例 :
  签名: Zero (εNFA α σ)
  定义体: ⟨⟨fun _ _ => ∅, ∅, ∅⟩⟩
-/
instance : Zero (εNFA α σ) :=
  ⟨⟨fun _ _ => ∅, ∅, ∅⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (εNFA α σ)
  body: ⟨⟨fun _ _ => ∅, univ, univ⟩⟩

中文:
实例 :
  签名: One (εNFA α σ)
  定义体: ⟨⟨fun _ _ => ∅, univ, univ⟩⟩
-/
instance : One (εNFA α σ) :=
  ⟨⟨fun _ _ => ∅, univ, univ⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (εNFA α σ)
  body: ⟨0⟩

@[simp]

中文:
实例 :
  签名: Inhabited (εNFA α σ)
  定义体: ⟨0⟩

@[simp]
-/
instance : Inhabited (εNFA α σ) :=
  ⟨0⟩

@[simp]
/--
theorem `step_zero` / 定理 `step_zero`

English:
theorem step_zero
  given: (s a)
  statement: (0 : εNFA α σ).step s a = ∅
  proof: rfl

@[simp]

中文:
定理 step_zero
  条件: (s a)
  结论: (0 : εNFA α σ).step s a = ∅
  证明: rfl

@[simp]
-/
theorem step_zero (s a) : (0 : εNFA α σ).step s a = ∅ :=
  rfl

@[simp]
/--
theorem `step_one` / 定理 `step_one`

English:
theorem step_one
  given: (s a)
  statement: (1 : εNFA α σ).step s a = ∅
  proof: rfl

@[simp]

中文:
定理 step_one
  条件: (s a)
  结论: (1 : εNFA α σ).step s a = ∅
  证明: rfl

@[simp]
-/
theorem step_one (s a) : (1 : εNFA α σ).step s a = ∅ :=
  rfl

@[simp]
/--
theorem `start_zero` / 定理 `start_zero`

English:
theorem start_zero
  statement: (0 : εNFA α σ).start = ∅
  proof: rfl

@[simp]

中文:
定理 start_zero
  结论: (0 : εNFA α σ).start = ∅
  证明: rfl

@[simp]
-/
theorem start_zero : (0 : εNFA α σ).start = ∅ :=
  rfl

@[simp]
/--
theorem `start_one` / 定理 `start_one`

English:
theorem start_one
  statement: (1 : εNFA α σ).start = univ
  proof: rfl

@[simp]

中文:
定理 start_one
  结论: (1 : εNFA α σ).start = univ
  证明: rfl

@[simp]
-/
theorem start_one : (1 : εNFA α σ).start = univ :=
  rfl

@[simp]
/--
theorem `accept_zero` / 定理 `accept_zero`

English:
theorem accept_zero
  statement: (0 : εNFA α σ).accept = ∅
  proof: rfl

@[simp]

中文:
定理 accept_zero
  结论: (0 : εNFA α σ).accept = ∅
  证明: rfl

@[simp]
-/
theorem accept_zero : (0 : εNFA α σ).accept = ∅ :=
  rfl

@[simp]
/--
theorem `accept_one` / 定理 `accept_one`

English:
theorem accept_one
  statement: (1 : εNFA α σ).accept = univ
  proof: rfl

中文:
定理 accept_one
  结论: (1 : εNFA α σ).accept = univ
  证明: rfl
-/
theorem accept_one : (1 : εNFA α σ).accept = univ :=
  rfl

end εNFA
