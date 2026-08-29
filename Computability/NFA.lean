/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Maja Kądziołka, Chris Wong, Rudy Peterson
-/
module

public import Mathlib.Computability.DFA
public import Mathlib.Data.Fintype.Powerset

/-!
# Nondeterministic Finite Automata

A Nondeterministic Finite Automaton (NFA) is a state machine which
decides membership in a particular `Language`, by following every
possible path that describes an input string.

We show that DFAs and NFAs can decide the same languages, by constructing
an equivalent DFA for every NFA, and vice versa.

As constructing a DFA from an NFA uses an exponential number of states,
we re-prove the pumping lemma instead of lifting `DFA.pumping_lemma`,
in order to obtain the optimal bound on the minimal length of the string.

Like `DFA`, this definition allows for automata with infinite states;
a `Fintype` instance must be supplied for true NFAs.

## Main definitions

* `NFA α σ`: automaton over alphabet `α` and set of states `σ`
* `NFA.evalFrom M S x`: set of possible ending states for an input word `x`
  and set of initial states `S`
* `NFA.accepts M`: the language accepted by the NFA `M`
* `NFA.Path M s t x`: a specific path from `s` to `t` for an input word `x`
* `NFA.Path.supp p`: set of states visited by the path `p`

## Main theorems

* `NFA.pumping_lemma`: every sufficiently long string accepted by the NFA has a substring that can
  be repeated arbitrarily many times (and have the overall string still be accepted)
-/

@[expose] public section

open Set

open Computability

universe u v

/--
Definition of `NFA` / `NFA` 的定义

English:
structure NFA
  parameters: (α : Type u) (σ : Type v)
  axioms and operations (3):
    - step : σ -> α -> Set σ
    - start : Set σ
    - accept : Set σ

中文:
结构 NFA
  参数: (α : 类型u) (σ : 类型v)
  公理与运算 (3 个):
    - step : σ -> α -> 集合 σ
    - start : 集合 σ
    - accept : 集合 σ
-/
structure NFA (α : Type u) (σ : Type v) where
  /-- The NFA's transition function -/
  step : σ -> α -> Set σ
  /-- Set of starting states -/
  start : Set σ
  /-- Set of accepting states -/
  accept : Set σ

variable {α : Type u} {σ : Type v} {M : NFA α σ}

namespace NFA

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (NFA α σ)
  body: ⟨NFA.mk (fun _ _ => ∅) ∅ ∅⟩

中文:
实例 :
  签名: 可居 (NFA α σ)
  定义体: ⟨NFA.mk (fun _ _ => ∅) ∅ ∅⟩

Depends on / 依赖: NFA.mk
-/
instance : Inhabited (NFA α σ) :=
  ⟨NFA.mk (fun _ _ => ∅) ∅ ∅⟩

variable (M) in
/--
Definition of `stepSet` / `stepSet` 的定义

English:
definition stepSet
  signature: (S : Set σ) (a : α)
  body: ⋃ s in S, M.step s a

中文:
定义 stepSet
  签名: (S : 集合 σ) (a : α)
  定义体: ⋃ s in S, M.step s a

Depends on / 依赖: M.step
-/
def stepSet (S : Set σ) (a : α) : Set σ :=
  ⋃ s in S, M.step s a

/--
theorem `mem_stepSet` / 定理 `mem_stepSet`

English:
theorem mem_stepSet
  given: {s : σ} {S : Set σ} {a : α}
  statement: s in M.stepSet S a ↔ exists t in S, s in M.step t a
  proof: by
  simp [stepSet]

中文:
定理 mem_stepSet
  条件: {s : σ} {S : 集合 σ} {a : α}
  结论: s in M.stepSet S a ↔ 存在 t in S, s in M.step t a
  证明: by
  simp [stepSet]

Depends on / 依赖: stepSet
-/
theorem mem_stepSet {s : σ} {S : Set σ} {a : α} : s in M.stepSet S a ↔ exists t in S, s in M.step t a := by
  simp [stepSet]

variable (M) in
@[simp]
/--
theorem `stepSet_empty` / 定理 `stepSet_empty`

English:
theorem stepSet_empty
  given: (a : α)
  statement: M.stepSet ∅ a = ∅
  proof: by simp [stepSet]

中文:
定理 stepSet_empty
  条件: (a : α)
  结论: M.stepSet ∅ a = ∅
  证明: by simp [stepSet]

Depends on / 依赖: stepSet
-/
theorem stepSet_empty (a : α) : M.stepSet ∅ a = ∅ := by simp [stepSet]

variable (M) in
@[simp]
/--
theorem `stepSet_singleton` / 定理 `stepSet_singleton`

English:
theorem stepSet_singleton
  given: (s : σ) (a : α)
  statement: M.stepSet {s} a = M.step s a
  proof: by
  simp [stepSet]

中文:
定理 stepSet_singleton
  条件: (s : σ) (a : α)
  结论: M.stepSet {s} a = M.step s a
  证明: by
  simp [stepSet]

Depends on / 依赖: stepSet
-/
theorem stepSet_singleton (s : σ) (a : α) : M.stepSet {s} a = M.step s a := by
  simp [stepSet]

variable (M) in
@[simp]
/--
theorem `stepSet_union` / 定理 `stepSet_union`

English:
theorem stepSet_union
  given: {S T : Set σ} {a : α}
  proof: by
  ext s
  simp [mem_stepSet, or_and_right, exists_or]

中文:
定理 stepSet_union
  条件: {S T : 集合 σ} {a : α}
  证明: by
  ext s
  simp [mem_stepSet, or_and_right, exists_or]

Depends on / 依赖: exists_or, mem_stepSet, or_and_right
-/
theorem stepSet_union {S T : Set σ} {a : α} :
    M.stepSet (S union T) a = M.stepSet S a union M.stepSet T a := by
  ext s
  simp [mem_stepSet, or_and_right, exists_or]

variable (M) in
/--
Definition of `evalFrom` / `evalFrom` 的定义

English:
definition evalFrom
  signature: (S : Set σ)
  body: List.foldl M.stepSet S

中文:
定义 evalFrom
  签名: (S : 集合 σ)
  定义体: List.foldl M.stepSet S

Depends on / 依赖: List.foldl, M.stepSet, stepSet
-/
def evalFrom (S : Set σ) : List α -> Set σ :=
  List.foldl M.stepSet S

variable (M) in
@[simp]
/--
theorem `evalFrom_nil` / 定理 `evalFrom_nil`

English:
theorem evalFrom_nil
  given: (S : Set σ)
  statement: M.evalFrom S [] = S
  proof: rfl

中文:
定理 evalFrom_nil
  条件: (S : 集合 σ)
  结论: M.evalFrom S [] = S
  证明: rfl
-/
theorem evalFrom_nil (S : Set σ) : M.evalFrom S [] = S :=
  rfl

variable (M) in
@[simp]
/--
theorem `evalFrom_singleton` / 定理 `evalFrom_singleton`

English:
theorem evalFrom_singleton
  given: (S : Set σ) (a : α)
  statement: M.evalFrom S [a] = M.stepSet S a
  proof: rfl

中文:
定理 evalFrom_singleton
  条件: (S : 集合 σ) (a : α)
  结论: M.evalFrom S [a] = M.stepSet S a
  证明: rfl
-/
theorem evalFrom_singleton (S : Set σ) (a : α) : M.evalFrom S [a] = M.stepSet S a :=
  rfl

variable (M) in
@[simp]
/--
theorem `evalFrom_cons` / 定理 `evalFrom_cons`

English:
theorem evalFrom_cons
  given: (S : Set σ) (a : α) (x : List α)
  proof: rfl

中文:
定理 evalFrom_cons
  条件: (S : 集合 σ) (a : α) (x : 列表 α)
  证明: rfl
-/
theorem evalFrom_cons (S : Set σ) (a : α) (x : List α) :
    M.evalFrom S (a :: x) = M.evalFrom (M.stepSet S a) x :=
  rfl

variable (M) in
@[simp]
/--
theorem `evalFrom_append` / 定理 `evalFrom_append`

English:
theorem evalFrom_append
  given: (S : Set σ) (x y : List α)
  proof: by
  simp only [evalFrom, List.foldl_append]

中文:
定理 evalFrom_append
  条件: (S : 集合 σ) (x y : 列表 α)
  证明: by
  simp only [evalFrom, List.foldl_append]

Depends on / 依赖: List.foldl_append, evalFrom, foldl_append
-/
theorem evalFrom_append (S : Set σ) (x y : List α) :
    M.evalFrom S (x ++ y) = M.evalFrom (M.evalFrom S x) y := by
  simp only [evalFrom, List.foldl_append]

variable (M) in
@[simp]
/--
theorem `evalFrom_union` / 定理 `evalFrom_union`

English:
theorem evalFrom_union
  given: (S T : Set σ) (x : List α)
  proof: by
  induction x generalizing S T with
  | nil => simp
  | cons a x ih => simp [ih]

中文:
定理 evalFrom_union
  条件: (S T : 集合 σ) (x : 列表 α)
  证明: by
  induction x generalizing S T with
  | nil => simp
  | cons a x ih => simp [ih]

Depends on / 依赖: generalizing
-/
theorem evalFrom_union (S T : Set σ) (x : List α) :
    M.evalFrom (S union T) x = M.evalFrom S x union M.evalFrom T x := by
  induction x generalizing S T with
  | nil => simp
  | cons a x ih => simp [ih]

variable (M) in
@[simp]
/--
theorem `evalFrom_iUnion` / 定理 `evalFrom_iUnion`

English:
theorem evalFrom_iUnion
  given: {ι : Sort*} (s : ι -> Set σ) (x : List α)
  proof: by
  induction x generalizing s with
  | nil => simp
  | cons a x ih => simp [stepSet, Set.iUnion_comm (ι := σ) (ι' := ι), ih]

中文:
定理 evalFrom_iUnion
  条件: {ι : 类型层*} (s : ι -> 集合 σ) (x : 列表 α)
  证明: by
  induction x generalizing s with
  | nil => simp
  | cons a x ih => simp [stepSet, Set.iUnion_comm (ι := σ) (ι' := ι), ih]

Depends on / 依赖: Set.iUnion_comm, generalizing, iUnion_comm, stepSet
-/
theorem evalFrom_iUnion {ι : Sort*} (s : ι -> Set σ) (x : List α) :
    M.evalFrom (⋃ i, s i) x = ⋃ i, M.evalFrom (s i) x := by
  induction x generalizing s with
  | nil => simp
  | cons a x ih => simp [stepSet, Set.iUnion_comm (ι := σ) (ι' := ι), ih]

variable (M) in
/--
theorem `evalFrom_iUnion₂` / 定理 `evalFrom_iUnion₂`

English:
theorem evalFrom_iUnion₂
  given: {ι : Sort*} {κ : ι -> Sort*} (f : forall i, κ i -> Set σ) (x : List α)
  proof: by
  simp

中文:
定理 evalFrom_iUnion₂
  条件: {ι : 类型层*} {κ : ι -> 类型层*} (f : 对任意 i, κ i -> 集合 σ) (x : 列表 α)
  证明: by
  simp
-/
theorem evalFrom_iUnion₂ {ι : Sort*} {κ : ι -> Sort*} (f : forall i, κ i -> Set σ) (x : List α) :
    M.evalFrom (⋃ (i) (j), f i j) x = ⋃ (i) (j), M.evalFrom (f i j) x := by
  simp

variable (M) in
/--
theorem `evalFrom_eq_biUnion_singleton` / 定理 `evalFrom_eq_biUnion_singleton`

English:
theorem evalFrom_eq_biUnion_singleton
  given: (S : Set σ) (x : List α)
  proof: by
  simp [← evalFrom_iUnion₂]

中文:
定理 evalFrom_eq_biUnion_singleton
  条件: (S : 集合 σ) (x : 列表 α)
  证明: by
  simp [← evalFrom_iUnion₂]
-/
theorem evalFrom_eq_biUnion_singleton (S : Set σ) (x : List α) :
    M.evalFrom S x = ⋃ s in S, M.evalFrom {s} x := by
  simp [← evalFrom_iUnion₂]

/--
theorem `mem_evalFrom_iff_exists` / 定理 `mem_evalFrom_iff_exists`

English:
theorem mem_evalFrom_iff_exists
  given: {s : σ} {S : Set σ} {x : List α}
  proof: by
  rw [evalFrom_eq_biUnion_singleton]
  simp

中文:
定理 mem_evalFrom_iff_存在
  条件: {s : σ} {S : 集合 σ} {x : 列表 α}
  证明: by
  rw [evalFrom_eq_biUnion_singleton]
  simp

Depends on / 依赖: evalFrom_eq_biUnion_singleton
-/
theorem mem_evalFrom_iff_exists {s : σ} {S : Set σ} {x : List α} :
    s in M.evalFrom S x ↔ exists t in S, s in M.evalFrom {t} x := by
  rw [evalFrom_eq_biUnion_singleton]
  simp

variable (M) in
/--
Definition of `acceptsFrom` / `acceptsFrom` 的定义

English:
definition acceptsFrom
  signature: (S : Set σ)
  body: {x | exists s in M.accept, s in M.evalFrom S x}

中文:
定义 acceptsFrom
  签名: (S : 集合 σ)
  定义体: {x | exists s in M.accept, s in M.evalFrom S x}

Depends on / 依赖: M.accept, M.evalFrom, accept, evalFrom
-/
def acceptsFrom (S : Set σ) : Language α := {x | exists s in M.accept, s in M.evalFrom S x}

/--
theorem `mem_acceptsFrom` / 定理 `mem_acceptsFrom`

English:
theorem mem_acceptsFrom
  given: {S : Set σ} {x : List α}
  proof: by
  rfl

中文:
定理 mem_acceptsFrom
  条件: {S : 集合 σ} {x : 列表 α}
  证明: by
  rfl
-/
theorem mem_acceptsFrom {S : Set σ} {x : List α} :
    x in M.acceptsFrom S ↔ exists s in M.accept, s in M.evalFrom S x := by
  rfl

variable (M) in
@[simp]
/--
theorem `nil_mem_acceptsFrom` / 定理 `nil_mem_acceptsFrom`

English:
theorem nil_mem_acceptsFrom
  given: {S : Set σ}
  statement: [] in M.acceptsFrom S ↔ exists s in S, s in M.accept
  proof: by
  simp only [mem_acceptsFrom, evalFrom_nil]; tauto

中文:
定理 nil_mem_acceptsFrom
  条件: {S : 集合 σ}
  结论: [] in M.acceptsFrom S ↔ 存在 s in S, s in M.accept
  证明: by
  simp only [mem_acceptsFrom, evalFrom_nil]; tauto

Depends on / 依赖: evalFrom_nil, mem_acceptsFrom
-/
theorem nil_mem_acceptsFrom {S : Set σ} : [] in M.acceptsFrom S ↔ exists s in S, s in M.accept := by
  simp only [mem_acceptsFrom, evalFrom_nil]; tauto

variable (M) in
@[simp]
/--
theorem `cons_mem_acceptsFrom` / 定理 `cons_mem_acceptsFrom`

English:
theorem cons_mem_acceptsFrom
  given: {S : Set σ} {a : α} {x : List α}
  proof: by
  simp [mem_acceptsFrom]

中文:
定理 cons_mem_acceptsFrom
  条件: {S : 集合 σ} {a : α} {x : 列表 α}
  证明: by
  simp [mem_acceptsFrom]

Depends on / 依赖: mem_acceptsFrom
-/
theorem cons_mem_acceptsFrom {S : Set σ} {a : α} {x : List α} :
    a :: x in M.acceptsFrom S ↔ x in M.acceptsFrom (M.stepSet S a) := by
  simp [mem_acceptsFrom]

set_option backward.isDefEq.respectTransparency false in
variable (M) in
/--
theorem `cons_preimage_acceptsFrom` / 定理 `cons_preimage_acceptsFrom`

English:
theorem cons_preimage_acceptsFrom
  given: {S : Set σ} {a : α}
  proof: by
  ext x; simp [cons_mem_acceptsFrom M]

中文:
定理 cons_preimage_acceptsFrom
  条件: {S : 集合 σ} {a : α}
  证明: by
  ext x; simp [cons_mem_acceptsFrom M]

Depends on / 依赖: cons_mem_acceptsFrom
-/
theorem cons_preimage_acceptsFrom {S : Set σ} {a : α} :
    (a :: ·) ⁻¹' M.acceptsFrom S = M.acceptsFrom (M.stepSet S a) := by
  ext x; simp [cons_mem_acceptsFrom M]

variable (M) in
@[simp]
/--
theorem `append_mem_acceptsFrom` / 定理 `append_mem_acceptsFrom`

English:
theorem append_mem_acceptsFrom
  given: {S : Set σ} {x y : List α}
  proof: by
  simp [mem_acceptsFrom]

中文:
定理 append_mem_acceptsFrom
  条件: {S : 集合 σ} {x y : 列表 α}
  证明: by
  simp [mem_acceptsFrom]

Depends on / 依赖: mem_acceptsFrom
-/
theorem append_mem_acceptsFrom {S : Set σ} {x y : List α} :
    x ++ y in M.acceptsFrom S ↔ y in M.acceptsFrom (M.evalFrom S x) := by
  simp [mem_acceptsFrom]

set_option backward.isDefEq.respectTransparency false in
variable (M) in
/--
theorem `append_preimage_acceptsFrom` / 定理 `append_preimage_acceptsFrom`

English:
theorem append_preimage_acceptsFrom
  given: {S : Set σ} {x : List α}
  proof: by
  ext y; simp [append_mem_acceptsFrom M]

中文:
定理 append_preimage_acceptsFrom
  条件: {S : 集合 σ} {x : 列表 α}
  证明: by
  ext y; simp [append_mem_acceptsFrom M]

Depends on / 依赖: append_mem_acceptsFrom
-/
theorem append_preimage_acceptsFrom {S : Set σ} {x : List α} :
    (x ++ ·) ⁻¹' M.acceptsFrom S = M.acceptsFrom (M.evalFrom S x) := by
  ext y; simp [append_mem_acceptsFrom M]

variable (M) in
@[simp]
/--
theorem `acceptsFrom_union` / 定理 `acceptsFrom_union`

English:
theorem acceptsFrom_union
  given: {S T : Set σ}
  proof: by
  rw [Language.add_def]; ext x
  simp only [mem_acceptsFrom, evalFrom_union, mem_union]
  constructor
  · rintro ⟨s, hs, h | h⟩
    · left; tauto
    · right; tauto
  · rintro (⟨s, hs, h⟩ | ⟨s, hs, h⟩) <;> exists s <;> tauto

中文:
定理 acceptsFrom_union
  条件: {S T : 集合 σ}
  证明: by
  rw [Language.add_def]; ext x
  simp only [mem_acceptsFrom, evalFrom_union, mem_union]
  constructor
  · rintro ⟨s, hs, h | h⟩
    · left; tauto
    · right; tauto
  · rintro (⟨s, hs, h⟩ | ⟨s, hs, h⟩) <;> exists s <;> tauto

Depends on / 依赖: Language, Language.add_def, add_def, evalFrom_union, mem_acceptsFrom, mem_union
-/
theorem acceptsFrom_union {S T : Set σ} :
    M.acceptsFrom (S union T) = M.acceptsFrom S + M.acceptsFrom T := by
  rw [Language.add_def]; ext x
  simp only [mem_acceptsFrom, evalFrom_union, mem_union]
  constructor
  · rintro ⟨s, hs, h | h⟩
    · left; tauto
    · right; tauto
  · rintro (⟨s, hs, h⟩ | ⟨s, hs, h⟩) <;> exists s <;> tauto

set_option backward.isDefEq.respectTransparency false in
variable (M) in
@[simp]
/--
theorem `acceptsFrom_iUnion` / 定理 `acceptsFrom_iUnion`

English:
theorem acceptsFrom_iUnion
  given: {ι : Sort*} (s : ι -> Set σ)
  proof: by
  ext x
  simp only [acceptsFrom, evalFrom_iUnion, mem_iUnion]
  simp_rw [↑mem_iUnion, ↑mem_ofPred_eq]; tauto

中文:
定理 acceptsFrom_iUnion
  条件: {ι : 类型层*} (s : ι -> 集合 σ)
  证明: by
  ext x
  simp only [acceptsFrom, evalFrom_iUnion, mem_iUnion]
  simp_rw [↑mem_iUnion, ↑mem_ofPred_eq]; tauto

Depends on / 依赖: acceptsFrom, evalFrom_iUnion, mem_iUnion, mem_ofPred_eq, simp_rw
-/
theorem acceptsFrom_iUnion {ι : Sort*} (s : ι -> Set σ) :
    M.acceptsFrom (⋃ i, s i) = ⋃ i, M.acceptsFrom (s i) := by
  ext x
  simp only [acceptsFrom, evalFrom_iUnion, mem_iUnion]
  simp_rw [↑mem_iUnion, ↑mem_ofPred_eq]; tauto

set_option backward.isDefEq.respectTransparency false in
variable (M) in
/--
theorem `acceptsFrom_iUnion₂` / 定理 `acceptsFrom_iUnion₂`

English:
theorem acceptsFrom_iUnion₂
  given: {ι : Sort*} {κ : ι -> Sort*} (f : forall i, κ i -> Set σ)
  proof: by
  simp

中文:
定理 acceptsFrom_iUnion₂
  条件: {ι : 类型层*} {κ : ι -> 类型层*} (f : 对任意 i, κ i -> 集合 σ)
  证明: by
  simp
-/
theorem acceptsFrom_iUnion₂ {ι : Sort*} {κ : ι -> Sort*} (f : forall i, κ i -> Set σ) :
    M.acceptsFrom (⋃ (i) (j), f i j) = ⋃ (i) (j), M.acceptsFrom (f i j) := by
  simp

variable (M) in
@[simp]
/--
theorem `mem_acceptsFrom_sep_fact` / 定理 `mem_acceptsFrom_sep_fact`

English:
theorem mem_acceptsFrom_sep_fact
  given: {S : Set σ} {p : Prop} {x : List α}
  proof: by
  induction x generalizing S with
  | nil => simp only [nil_mem_acceptsFrom, mem_ofPred_eq]; tauto
  | cons a x ih =>
    have h : M.stepSet {s in S | p} a = {s in M.stepSet S a | p} := by
      ext s; simp only [stepSet, mem_ofPred_eq, mem_iUnion, exists_prop]; tauto
    simp [h, ih]

中文:
定理 mem_acceptsFrom_sep_fact
  条件: {S : 集合 σ} {p : 命题} {x : 列表 α}
  证明: by
  induction x generalizing S with
  | nil => simp only [nil_mem_acceptsFrom, mem_ofPred_eq]; tauto
  | cons a x ih =>
    have h : M.stepSet {s in S | p} a = {s in M.stepSet S a | p} := by
      ext s; simp only [stepSet, mem_ofPred_eq, mem_iUnion, exists_prop]; tauto
    simp [h, ih]
-/
private theorem mem_acceptsFrom_sep_fact {S : Set σ} {p : Prop} {x : List α} :
    x in M.acceptsFrom {s in S | p} ↔ x in M.acceptsFrom S ∧ p := by
  induction x generalizing S with
  | nil => simp only [nil_mem_acceptsFrom, mem_ofPred_eq]; tauto
  | cons a x ih =>
    have h : M.stepSet {s in S | p} a = {s in M.stepSet S a | p} := by
      ext s; simp only [stepSet, mem_ofPred_eq, mem_iUnion, exists_prop]; tauto
    simp [h, ih]

variable (M) in
/--
Definition of `eval` / `eval` 的定义

English:
definition eval
  signature: : List α -> Set σ
  body: M.evalFrom M.start

中文:
定义 eval
  签名: : 列表 α -> 集合 σ
  定义体: M.evalFrom M.start

Depends on / 依赖: M.evalFrom, M.start, evalFrom
-/
def eval : List α -> Set σ :=
  M.evalFrom M.start

variable (M) in
@[simp]
/--
theorem `eval_nil` / 定理 `eval_nil`

English:
theorem eval_nil
  statement: M.eval [] = M.start
  proof: rfl

中文:
定理 eval_nil
  结论: M.eval [] = M.start
  证明: rfl
-/
theorem eval_nil : M.eval [] = M.start :=
  rfl

variable (M) in
@[simp]
/--
theorem `eval_singleton` / 定理 `eval_singleton`

English:
theorem eval_singleton
  given: (a : α)
  statement: M.eval [a] = M.stepSet M.start a
  proof: rfl

中文:
定理 eval_singleton
  条件: (a : α)
  结论: M.eval [a] = M.stepSet M.start a
  证明: rfl
-/
theorem eval_singleton (a : α) : M.eval [a] = M.stepSet M.start a :=
  rfl

variable (M) in
@[simp]
/--
theorem `eval_append_singleton` / 定理 `eval_append_singleton`

English:
theorem eval_append_singleton
  given: (x : List α) (a : α)
  proof: by
  simp [eval]

中文:
定理 eval_append_singleton
  条件: (x : 列表 α) (a : α)
  证明: by
  simp [eval]
-/
theorem eval_append_singleton (x : List α) (a : α) :
    M.eval (x ++ [a]) = M.stepSet (M.eval x) a := by
  simp [eval]

variable (M) in
/--
Definition of `accepts` / `accepts` 的定义

English:
definition accepts
  signature: : Language α
  body: {x | exists S in M.accept, S in M.eval x}

中文:
定义 accepts
  签名: : Language α
  定义体: {x | exists S in M.accept, S in M.eval x}

Depends on / 依赖: M.accept, M.eval, accept
-/
def accepts : Language α := {x | exists S in M.accept, S in M.eval x}

/--
theorem `mem_accepts` / 定理 `mem_accepts`

English:
theorem mem_accepts
  given: {x : List α}
  statement: x in M.accepts ↔ exists S in M.accept, S in M.evalFrom M.start x
  proof: by
  rfl

中文:
定理 mem_accepts
  条件: {x : 列表 α}
  结论: x in M.accepts ↔ 存在 S in M.accept, S in M.evalFrom M.start x
  证明: by
  rfl
-/
theorem mem_accepts {x : List α} : x in M.accepts ↔ exists S in M.accept, S in M.evalFrom M.start x := by
  rfl

/--
theorem `accepts_eq_acceptsFrom_start` / 定理 `accepts_eq_acceptsFrom_start`

English:
theorem accepts_eq_acceptsFrom_start
  statement: M.accepts = M.acceptsFrom M.start
  proof: rfl

中文:
定理 accepts_eq_acceptsFrom_start
  结论: M.accepts = M.acceptsFrom M.start
  证明: rfl
-/
theorem accepts_eq_acceptsFrom_start : M.accepts = M.acceptsFrom M.start := rfl

variable (M) in
/--
Inductive type `Path` / 归纳类型 `Path`

English:
inductive Path
  parameters: : σ -> σ -> List α -> Type (max u v)
  constructors (2):
    - nil: (s : σ) : Path s s []
    - cons: (t s u : σ) (a : α) (x : List α) : t in M.step s a -> Path t u x -> Path s u (a :: x)

中文:
归纳类型 道路
  参数: : σ -> σ -> 列表 α -> 类型 (最大值 u v)
  构造子 (2 个):
    - nil: (s : σ) : 道路 s s []
    - cons: (t s u : σ) (a : α) (x : 列表 α) : t in M.step s a -> 道路 t u x -> 道路 s u (a :: x)
-/
inductive Path : σ -> σ -> List α -> Type (max u v)
  | nil (s : σ) : Path s s []
  | cons (t s u : σ) (a : α) (x : List α) :
      t in M.step s a -> Path t u x -> Path s u (a :: x)

/-- Set of states visited by a path. -/
@[simp]
/--
Definition of `Path.supp` / `Path.supp` 的定义

English:
definition Path.supp
  signature: [DecidableEq σ] {s t : σ} {x : List α}

中文:
定义 道路.supp
  签名: [DecidableEq σ] {s t : σ} {x : 列表 α}
-/
def Path.supp [DecidableEq σ] {s t : σ} {x : List α} : M.Path s t x -> Finset σ
  | nil s => {s}
  | cons _ _ _ _ _ _ p => {s} union p.supp

/--
theorem `mem_evalFrom_iff_nonempty_path` / 定理 `mem_evalFrom_iff_nonempty_path`

English:
theorem mem_evalFrom_iff_nonempty_path
  given: {s t : σ} {x : List α}
  proof: match x with
    | [] =>
      have h : s = t := by simp at h; tauto
      ⟨h ▸ Path.nil s⟩
    | a :: x =>
      have h : exists s' in M.step s a, t in M.evalFrom {s'} x := by
        rw [evalFrom_cons]; rw [mem_evalFrom_iff_exists]; rw [stepSet_singleton] at h; exact h
      let ⟨s', h₁, h₂⟩ := h


中文:
定理 mem_evalFrom_iff_nonempty_path
  条件: {s t : σ} {x : 列表 α}
  证明: match x with
    | [] =>
      have h : s = t := by simp at h; tauto
      ⟨h ▸ Path.nil s⟩
    | a :: x =>
      have h : exists s' in M.step s a, t in M.evalFrom {s'} x := by
        rw [evalFrom_cons]; rw [mem_evalFrom_iff_exists]; rw [stepSet_singleton] at h; exact h
      let ⟨s', h₁, h₂⟩ := h

-/
theorem mem_evalFrom_iff_nonempty_path {s t : σ} {x : List α} :
    t in M.evalFrom {s} x ↔ Nonempty (M.Path s t x) where
  mp h := match x with
    | [] =>
      have h : s = t := by simp at h; tauto
      ⟨h ▸ Path.nil s⟩
    | a :: x =>
      have h : exists s' in M.step s a, t in M.evalFrom {s'} x := by
        rw [evalFrom_cons]; rw [mem_evalFrom_iff_exists]; rw [stepSet_singleton] at h; exact h
      let ⟨s', h₁, h₂⟩ := h
      let ⟨p'⟩ := mem_evalFrom_iff_nonempty_path.1 h₂
      ⟨Path.cons s' _ _ _ _ h₁ p'⟩
  mpr p := match p with
    | ⟨Path.nil s⟩ => by simp
    | ⟨Path.cons s' s t a x h₁ h₂⟩ => by
      rw [evalFrom_cons]; rw [stepSet_singleton]; rw [mem_evalFrom_iff_exists]
      exact ⟨s', h₁, mem_evalFrom_iff_nonempty_path.2 ⟨h₂⟩⟩

/--
theorem `accepts_iff_exists_path` / 定理 `accepts_iff_exists_path`

English:
theorem accepts_iff_exists_path
  given: {x : List α}
  proof: by
  simp only [← mem_evalFrom_iff_nonempty_path, mem_accepts, mem_evalFrom_iff_exists (S := M.start)]
  tauto

中文:
定理 accepts_iff_存在_path
  条件: {x : 列表 α}
  证明: by
  simp only [← mem_evalFrom_iff_nonempty_path, mem_accepts, mem_evalFrom_iff_exists (S := M.start)]
  tauto

Depends on / 依赖: M.start, mem_accepts, mem_evalFrom_iff_exists, mem_evalFrom_iff_nonempty_path
-/
theorem accepts_iff_exists_path {x : List α} :
    x in M.accepts ↔ exists s in M.start, exists t in M.accept, Nonempty (M.Path s t x) := by
  simp only [← mem_evalFrom_iff_nonempty_path, mem_accepts, mem_evalFrom_iff_exists (S := M.start)]
  tauto

variable (M) in
/--
Definition of `toDFA` / `toDFA` 的定义

English:
definition toDFA
  signature: : DFA α (Set σ) where
  body: M.stepSet
  start := M.start
  accept := { S | exists s in S, s in M.accept }

@[simp]

中文:
定义 toDFA
  签名: : DFA α (集合 σ) where
  定义体: M.stepSet
  start := M.start
  accept := { S | exists s in S, s in M.accept }

@[simp]

Depends on / 依赖: M.stepSet, stepSet
-/
def toDFA : DFA α (Set σ) where
  step := M.stepSet
  start := M.start
  accept := { S | exists s in S, s in M.accept }

@[simp]
/--
theorem `toDFA_correct` / 定理 `toDFA_correct`

English:
theorem toDFA_correct
  statement: M.toDFA.accepts = M.accepts
  proof: by
  ext x
  rw [mem_accepts]; rw [DFA.mem_accepts]
  constructor <;> · exact fun ⟨w, h2, h3⟩ => ⟨w, h3, h2⟩

中文:
定理 toDFA_correct
  结论: M.toDFA.accepts = M.accepts
  证明: by
  ext x
  rw [mem_accepts]; rw [DFA.mem_accepts]
  constructor <;> · exact fun ⟨w, h2, h3⟩ => ⟨w, h3, h2⟩

Depends on / 依赖: DFA.mem_accepts, mem_accepts
-/
theorem toDFA_correct : M.toDFA.accepts = M.accepts := by
  ext x
  rw [mem_accepts]; rw [DFA.mem_accepts]
  constructor <;> · exact fun ⟨w, h2, h3⟩ => ⟨w, h3, h2⟩

/--
theorem `pumping_lemma` / 定理 `pumping_lemma`

English:
theorem pumping_lemma
  statement: [Fintype σ] {x : List α} (hx : x in M.accepts)
  proof: by
  rw [← toDFA_correct] at hx ⊢
  exact M.toDFA.pumping_lemma hx hlen

中文:
定理 pumping_lemma
  结论: [有限类型 σ] {x : 列表 α} (hx : x in M.accepts)
  证明: by
  rw [← toDFA_correct] at hx ⊢
  exact M.toDFA.pumping_lemma hx hlen

Depends on / 依赖: M.toDFA.pumping_lemma, pumping_lemma, toDFA_correct
-/
theorem pumping_lemma [Fintype σ] {x : List α} (hx : x in M.accepts)
    (hlen : Fintype.card (Set σ) <= List.length x) :
    exists a b c,
      x = a ++ b ++ c ∧
        a.length + b.length <= Fintype.card (Set σ) ∧ b != [] ∧ {a} * {b}∗ * {c} <= M.accepts := by
  rw [← toDFA_correct] at hx ⊢
  exact M.toDFA.pumping_lemma hx hlen

end NFA

namespace DFA

/--
Definition of `toNFA` / `toNFA` 的定义

English:
definition toNFA
  signature: (M : DFA α σ)
  body: {M.step s a}
  start := {M.start}
  accept := M.accept

@[simp]

中文:
定义 toNFA
  签名: (M : DFA α σ)
  定义体: {M.step s a}
  start := {M.start}
  accept := M.accept

@[simp]
-/
@[simps] def toNFA (M : DFA α σ) : NFA α σ where
  step s a := {M.step s a}
  start := {M.start}
  accept := M.accept

@[simp]
/--
theorem `toNFA_evalFrom_match` / 定理 `toNFA_evalFrom_match`

English:
theorem toNFA_evalFrom_match
  given: (M : DFA α σ) (start : σ) (s : List α)
  proof: by
  change List.foldl M.toNFA.stepSet {start} s = {List.foldl M.step start s}
  induction s generalizing start with
  | nil => tauto
  | cons a s ih =>
    rw [List.foldl]; rw [List.foldl]; rw [show M.toNFA.stepSet {start} a = {M.step start a} by simp [NFA.stepSet]]
    tauto

@[simp]

中文:
定理 toNFA_evalFrom_match
  条件: (M : DFA α σ) (start : σ) (s : 列表 α)
  证明: by
  change List.foldl M.toNFA.stepSet {start} s = {List.foldl M.step start s}
  induction s generalizing start with
  | nil => tauto
  | cons a s ih =>
    rw [List.foldl]; rw [List.foldl]; rw [show M.toNFA.stepSet {start} a = {M.step start a} by simp [NFA.stepSet]]
    tauto

@[simp]

Depends on / 依赖: List.foldl, M.step, M.toNFA.stepSet, NFA.stepSet, generalizing, stepSet
-/
theorem toNFA_evalFrom_match (M : DFA α σ) (start : σ) (s : List α) :
    M.toNFA.evalFrom {start} s = {M.evalFrom start s} := by
  change List.foldl M.toNFA.stepSet {start} s = {List.foldl M.step start s}
  induction s generalizing start with
  | nil => tauto
  | cons a s ih =>
    rw [List.foldl]; rw [List.foldl]; rw [show M.toNFA.stepSet {start} a = {M.step start a} by simp [NFA.stepSet]]
    tauto

@[simp]
/--
theorem `toNFA_correct` / 定理 `toNFA_correct`

English:
theorem toNFA_correct
  given: (M : DFA α σ)
  statement: M.toNFA.accepts = M.accepts
  proof: by
  ext x
  rw [NFA.mem_accepts]; rw [toNFA_start]; rw [toNFA_evalFrom_match]
  constructor
  · rintro ⟨S, hS₁, hS₂⟩
    rwa [Set.mem_singleton_iff.mp hS₂] at hS₁
  · exact fun h => ⟨M.eval x, h, rfl⟩

中文:
定理 toNFA_correct
  条件: (M : DFA α σ)
  结论: M.toNFA.accepts = M.accepts
  证明: by
  ext x
  rw [NFA.mem_accepts]; rw [toNFA_start]; rw [toNFA_evalFrom_match]
  constructor
  · rintro ⟨S, hS₁, hS₂⟩
    rwa [Set.mem_singleton_iff.mp hS₂] at hS₁
  · exact fun h => ⟨M.eval x, h, rfl⟩

Depends on / 依赖: M.eval, NFA.mem_accepts, Set.mem_singleton_iff.mp, mem_accepts, mem_singleton_iff, toNFA_evalFrom_match, toNFA_start
-/
theorem toNFA_correct (M : DFA α σ) : M.toNFA.accepts = M.accepts := by
  ext x
  rw [NFA.mem_accepts]; rw [toNFA_start]; rw [toNFA_evalFrom_match]
  constructor
  · rintro ⟨S, hS₁, hS₂⟩
    rwa [Set.mem_singleton_iff.mp hS₂] at hS₁
  · exact fun h => ⟨M.eval x, h, rfl⟩

end DFA

namespace NFA

variable (M) in
/-- `M.reverse` constructs an NFA with the same states as `M`, but all the transitions reversed. The
resulting automaton accepts a word `x` if and only if `M` accepts `List.reverse x`. -/
@[simps]
/--
Definition of `reverse` / `reverse` 的定义

English:
definition reverse
  signature: : NFA α σ where
  body: { s' | s in M.step s' a }
  start := M.accept
  accept := M.start

中文:
定义 reverse
  签名: : NFA α σ where
  定义体: { s' | s in M.step s' a }
  start := M.accept
  accept := M.start

Depends on / 依赖: M.step
-/
def reverse : NFA α σ where
  step s a := { s' | s in M.step s' a }
  start := M.accept
  accept := M.start

variable (M) in
@[simp]
/--
theorem `reverse_reverse` / 定理 `reverse_reverse`

English:
theorem reverse_reverse
  statement: M.reverse.reverse = M
  proof: by
  simp [reverse]

中文:
定理 reverse_reverse
  结论: M.reverse.reverse = M
  证明: by
  simp [reverse]

Depends on / 依赖: reverse
-/
theorem reverse_reverse : M.reverse.reverse = M := by
  simp [reverse]

/--
theorem `disjoint_stepSet_reverse` / 定理 `disjoint_stepSet_reverse`

English:
theorem disjoint_stepSet_reverse
  given: {a : α} {S S' : Set σ}
  proof: by
  rw [← not_iff_not]
  simp only [Set.not_disjoint_iff, mem_stepSet, reverse_step, Set.mem_ofPred_eq]
  tauto

中文:
定理 disjoint_stepSet_reverse
  条件: {a : α} {S S' : 集合 σ}
  证明: by
  rw [← not_iff_not]
  simp only [Set.not_disjoint_iff, mem_stepSet, reverse_step, Set.mem_ofPred_eq]
  tauto

Depends on / 依赖: Set.mem_ofPred_eq, Set.not_disjoint_iff, mem_ofPred_eq, mem_stepSet, not_disjoint_iff, not_iff_not, reverse_step
-/
theorem disjoint_stepSet_reverse {a : α} {S S' : Set σ} :
    Disjoint S (M.reverse.stepSet S' a) ↔ Disjoint S' (M.stepSet S a) := by
  rw [← not_iff_not]
  simp only [Set.not_disjoint_iff, mem_stepSet, reverse_step, Set.mem_ofPred_eq]
  tauto

/--
theorem `disjoint_evalFrom_reverse` / 定理 `disjoint_evalFrom_reverse`

English:
theorem disjoint_evalFrom_reverse
  statement: {x : List α} {S S' : Set σ}
  proof: by
  simp only [evalFrom, List.foldl_reverse] at h ⊢
  induction x generalizing S S' with
  | nil =>
    rw [disjoint_comm]
    exact h
  | cons x xs ih =>
    rw [List.foldl_cons] at h
    rw [List.foldr_cons]; rw [← NFA.disjoint_stepSet_reverse]; rw [disjoint_comm]
    exact ih h

中文:
定理 disjoint_evalFrom_reverse
  结论: {x : 列表 α} {S S' : 集合 σ}
  证明: by
  simp only [evalFrom, List.foldl_reverse] at h ⊢
  induction x generalizing S S' with
  | nil =>
    rw [disjoint_comm]
    exact h
  | cons x xs ih =>
    rw [List.foldl_cons] at h
    rw [List.foldr_cons]; rw [← NFA.disjoint_stepSet_reverse]; rw [disjoint_comm]
    exact ih h

Depends on / 依赖: List.foldl_cons, List.foldl_reverse, List.foldr_cons, NFA.disjoint_stepSet_reverse, disjoint_comm, disjoint_stepSet_reverse, evalFrom, foldl_cons, foldl_reverse, foldr_cons, generalizing
-/
theorem disjoint_evalFrom_reverse {x : List α} {S S' : Set σ}
    (h : Disjoint S (M.reverse.evalFrom S' x)) : Disjoint S' (M.evalFrom S x.reverse) := by
  simp only [evalFrom, List.foldl_reverse] at h ⊢
  induction x generalizing S S' with
  | nil =>
    rw [disjoint_comm]
    exact h
  | cons x xs ih =>
    rw [List.foldl_cons] at h
    rw [List.foldr_cons]; rw [← NFA.disjoint_stepSet_reverse]; rw [disjoint_comm]
    exact ih h

/--
theorem `disjoint_evalFrom_reverse_iff` / 定理 `disjoint_evalFrom_reverse_iff`

English:
theorem disjoint_evalFrom_reverse_iff
  given: {x : List α} {S S' : Set σ}
  proof: ⟨disjoint_evalFrom_reverse, fun h => List.reverse_reverse x ▸ disjoint_evalFrom_reverse h⟩

@[simp]

中文:
定理 disjoint_evalFrom_reverse_iff
  条件: {x : 列表 α} {S S' : 集合 σ}
  证明: ⟨disjoint_evalFrom_reverse, fun h => List.reverse_reverse x ▸ disjoint_evalFrom_reverse h⟩

@[simp]

Depends on / 依赖: List.reverse_reverse, disjoint_evalFrom_reverse, reverse_reverse
-/
theorem disjoint_evalFrom_reverse_iff {x : List α} {S S' : Set σ} :
    Disjoint S (M.reverse.evalFrom S' x) ↔ Disjoint S' (M.evalFrom S x.reverse) :=
  ⟨disjoint_evalFrom_reverse, fun h => List.reverse_reverse x ▸ disjoint_evalFrom_reverse h⟩

@[simp]
/--
theorem `mem_accepts_reverse` / 定理 `mem_accepts_reverse`

English:
theorem mem_accepts_reverse
  given: {x : List α}
  statement: x in M.reverse.accepts ↔ x.reverse in M.accepts
  proof: by
  simp [mem_accepts, ← Set.not_disjoint_iff, disjoint_evalFrom_reverse_iff]

中文:
定理 mem_accepts_reverse
  条件: {x : 列表 α}
  结论: x in M.reverse.accepts ↔ x.reverse in M.accepts
  证明: by
  simp [mem_accepts, ← Set.not_disjoint_iff, disjoint_evalFrom_reverse_iff]

Depends on / 依赖: Set.not_disjoint_iff, disjoint_evalFrom_reverse_iff, mem_accepts, not_disjoint_iff
-/
theorem mem_accepts_reverse {x : List α} : x in M.reverse.accepts ↔ x.reverse in M.accepts := by
  simp [mem_accepts, ← Set.not_disjoint_iff, disjoint_evalFrom_reverse_iff]

end NFA

namespace Language

/--
theorem `IsRegular.reverse` / 定理 `IsRegular.reverse`

English:
theorem IsRegular.reverse
  given: {L : Language α} (h : L.IsRegular)
  statement: L.reverse.IsRegular
  proof: have ⟨σ, _, M, hM⟩ := h
  ⟨_, inferInstance, M.toNFA.reverse.toDFA, by ext; simp [hM]⟩

中文:
定理 是正则.reverse
  条件: {L : Language α} (h : L.是正则)
  结论: L.reverse.是正则
  证明: have ⟨σ, _, M, hM⟩ := h
  ⟨_, inferInstance, M.toNFA.reverse.toDFA, by ext; simp [hM]⟩
-/
protected theorem IsRegular.reverse {L : Language α} (h : L.IsRegular) : L.reverse.IsRegular :=
  have ⟨σ, _, M, hM⟩ := h
  ⟨_, inferInstance, M.toNFA.reverse.toDFA, by ext; simp [hM]⟩

/--
theorem `IsRegular.of_reverse` / 定理 `IsRegular.of_reverse`

English:
theorem IsRegular.of_reverse
  given: {L : Language α} (h : L.reverse.IsRegular)
  statement: L.IsRegular
  proof: L.reverse_reverse ▸ h.reverse

中文:
定理 是正则.of_reverse
  条件: {L : Language α} (h : L.reverse.是正则)
  结论: L.是正则
  证明: L.reverse_reverse ▸ h.reverse
-/
protected theorem IsRegular.of_reverse {L : Language α} (h : L.reverse.IsRegular) : L.IsRegular :=
  L.reverse_reverse ▸ h.reverse

/-- Regular languages are closed under reversal. -/
@[simp]
/--
theorem `isRegular_reverse_iff` / 定理 `isRegular_reverse_iff`

English:
theorem isRegular_reverse_iff
  given: {L : Language α}
  statement: L.reverse.IsRegular ↔ L.IsRegular
  proof: ⟨.of_reverse, .reverse⟩

中文:
定理 isRegular_reverse_iff
  条件: {L : Language α}
  结论: L.reverse.是正则 ↔ L.是正则
  证明: ⟨.of_reverse, .reverse⟩

Depends on / 依赖: of_reverse, reverse
-/
theorem isRegular_reverse_iff {L : Language α} : L.reverse.IsRegular ↔ L.IsRegular :=
  ⟨.of_reverse, .reverse⟩

end Language
