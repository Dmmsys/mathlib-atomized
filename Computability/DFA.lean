/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson, Chris Wong, Rudy Peterson
-/
module

public import Mathlib.Computability.Language
public import Mathlib.Data.Countable.Small
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.NormNum

/-!
# Deterministic Finite Automata

A Deterministic Finite Automaton (DFA) is a state machine which
decides membership in a particular `Language`, by following a path
uniquely determined by an input string.

We define regular languages to be ones for which a DFA exists, other formulations
are later proved equivalent.

Note that this definition allows for automata with infinite states,
a `Fintype` instance must be supplied for true DFAs.

## Main definitions

- `DFA α σ`: automaton over alphabet `α` and set of states `σ`
- `M.accepts`: the language accepted by the DFA `M`
- `Language.IsRegular L`: a predicate stating that `L` is a regular language, i.e. there exists
  a DFA that recognizes the language

## Main theorems

- `DFA.pumping_lemma` : every sufficiently long string accepted by the DFA has a substring that can
  be repeated arbitrarily many times (and have the overall string still be accepted)

## Implementation notes

Currently, there are two disjoint sets of simp lemmas: one for `DFA.eval`, and another for
`DFA.evalFrom`. You can switch from the former to the latter using `simp [eval]`.

## TODO

- Should we unify these simp sets, such that `eval` is rewritten to `evalFrom` automatically?
- Should `mem_accepts` and `mem_acceptsFrom` be marked `@[simp]`?
-/

@[expose] public section

universe u v

open Computability

/--
Definition of `DFA` / `DFA` 的定义

English:
structure DFA
  parameters: (α : Type u) (σ : Type v)
  axioms and operations (3):
    - step : σ -> α -> σ
    - start : σ
    - accept : Set σ

中文:
结构 DFA
  参数: (α : 类型u) (σ : 类型v)
  公理与运算 (3 个):
    - step : σ -> α -> σ
    - start : σ
    - accept : 集合 σ
-/
structure DFA (α : Type u) (σ : Type v) where
  /-- A transition function from state to state labelled by the alphabet. -/
  step : σ -> α -> σ
  /-- Starting state. -/
  start : σ
  /-- Set of acceptance states. -/
  accept : Set σ

namespace DFA

variable {α : Type u} {σ : Type v} (M : DFA α σ)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: σ] : Inhabited (DFA α σ)
  body: ⟨DFA.mk (fun _ _ => default) default ∅⟩

中文:
实例 [可居
  签名: σ] : 可居 (DFA α σ)
  定义体: ⟨DFA.mk (fun _ _ => default) default ∅⟩

Depends on / 依赖: DFA.mk, Finset, Finset.sup_lt_iff, WithBot, WithBot.bot_lt_coe, WithBot.coe_lt_coe, bot_lt_coe, coe_lt_coe, coe_sup, sup_lt_iff
-/
instance [Inhabited σ] : Inhabited (DFA α σ) :=
  ⟨DFA.mk (fun _ _ => default) default ∅⟩

/--
Definition of `evalFrom` / `evalFrom` 的定义

English:
definition evalFrom
  signature: (s : σ)
  body: List.foldl M.step s

@[simp]

中文:
定义 evalFrom
  签名: (s : σ)
  定义体: List.foldl M.step s

@[simp]

Depends on / 依赖: List.foldl, M.step
-/
def evalFrom (s : σ) : List α -> σ :=
  List.foldl M.step s

@[simp]
/--
theorem `evalFrom_nil` / 定理 `evalFrom_nil`

English:
theorem evalFrom_nil
  given: (s : σ)
  statement: M.evalFrom s [] = s
  proof: rfl

@[simp]

中文:
定理 evalFrom_nil
  条件: (s : σ)
  结论: M.evalFrom s [] = s
  证明: rfl

@[simp]
-/
theorem evalFrom_nil (s : σ) : M.evalFrom s [] = s :=
  rfl

@[simp]
/--
theorem `evalFrom_cons` / 定理 `evalFrom_cons`

English:
theorem evalFrom_cons
  given: (s : σ) (a : α) (x : List α)
  proof: rfl

@[simp]

中文:
定理 evalFrom_cons
  条件: (s : σ) (a : α) (x : 列表 α)
  证明: rfl

@[simp]
-/
theorem evalFrom_cons (s : σ) (a : α) (x : List α) :
    M.evalFrom s (a :: x) = M.evalFrom (M.step s a) x :=
  rfl

@[simp]
/--
theorem `evalFrom_singleton` / 定理 `evalFrom_singleton`

English:
theorem evalFrom_singleton
  given: (s : σ) (a : α)
  statement: M.evalFrom s [a] = M.step s a
  proof: rfl

@[simp]

中文:
定理 evalFrom_singleton
  条件: (s : σ) (a : α)
  结论: M.evalFrom s [a] = M.step s a
  证明: rfl

@[simp]
-/
theorem evalFrom_singleton (s : σ) (a : α) : M.evalFrom s [a] = M.step s a :=
  rfl

@[simp]
/--
theorem `evalFrom_append_singleton` / 定理 `evalFrom_append_singleton`

English:
theorem evalFrom_append_singleton
  given: (s : σ) (x : List α) (a : α)
  proof: by
  simp only [evalFrom, List.foldl_append, List.foldl_cons, List.foldl_nil]

中文:
定理 evalFrom_append_singleton
  条件: (s : σ) (x : 列表 α) (a : α)
  证明: by
  simp only [evalFrom, List.foldl_append, List.foldl_cons, List.foldl_nil]

Depends on / 依赖: List.foldl_append, List.foldl_cons, List.foldl_nil, evalFrom, foldl_append, foldl_cons, foldl_nil
-/
theorem evalFrom_append_singleton (s : σ) (x : List α) (a : α) :
    M.evalFrom s (x ++ [a]) = M.step (M.evalFrom s x) a := by
  simp only [evalFrom, List.foldl_append, List.foldl_cons, List.foldl_nil]

/--
Definition of `eval` / `eval` 的定义

English:
definition eval
  signature: : List α -> σ
  body: M.evalFrom M.start

@[simp]

中文:
定义 eval
  签名: : 列表 α -> σ
  定义体: M.evalFrom M.start

@[simp]

Depends on / 依赖: M.evalFrom, M.start, evalFrom
-/
def eval : List α -> σ :=
  M.evalFrom M.start

@[simp]
/--
theorem `eval_nil` / 定理 `eval_nil`

English:
theorem eval_nil
  statement: M.eval [] = M.start
  proof: rfl

@[simp]

中文:
定理 eval_nil
  结论: M.eval [] = M.start
  证明: rfl

@[simp]
-/
theorem eval_nil : M.eval [] = M.start :=
  rfl

@[simp]
/--
theorem `eval_singleton` / 定理 `eval_singleton`

English:
theorem eval_singleton
  given: (a : α)
  statement: M.eval [a] = M.step M.start a
  proof: rfl

@[simp]

中文:
定理 eval_singleton
  条件: (a : α)
  结论: M.eval [a] = M.step M.start a
  证明: rfl

@[simp]
-/
theorem eval_singleton (a : α) : M.eval [a] = M.step M.start a :=
  rfl

@[simp]
/--
theorem `eval_append_singleton` / 定理 `eval_append_singleton`

English:
theorem eval_append_singleton
  given: (x : List α) (a : α)
  statement: M.eval (x ++ [a]) = M.step (M.eval x) a
  proof: evalFrom_append_singleton _ _ _ _

中文:
定理 eval_append_singleton
  条件: (x : 列表 α) (a : α)
  结论: M.eval (x ++ [a]) = M.step (M.eval x) a
  证明: evalFrom_append_singleton _ _ _ _

Depends on / 依赖: evalFrom_append_singleton
-/
theorem eval_append_singleton (x : List α) (a : α) : M.eval (x ++ [a]) = M.step (M.eval x) a :=
  evalFrom_append_singleton _ _ _ _

/--
theorem `evalFrom_of_append` / 定理 `evalFrom_of_append`

English:
theorem evalFrom_of_append
  given: (start : σ) (x y : List α)
  proof: List.foldl_append

中文:
定理 evalFrom_of_append
  条件: (start : σ) (x y : 列表 α)
  证明: List.foldl_append

Depends on / 依赖: List.foldl_append, foldl_append
-/
theorem evalFrom_of_append (start : σ) (x y : List α) :
    M.evalFrom start (x ++ y) = M.evalFrom (M.evalFrom start x) y :=
  List.foldl_append

/--
Definition of `acceptsFrom` / `acceptsFrom` 的定义

English:
definition acceptsFrom
  signature: (s : σ)
  body: {x | M.evalFrom s x in M.accept}

中文:
定义 acceptsFrom
  签名: (s : σ)
  定义体: {x | M.evalFrom s x in M.accept}

Depends on / 依赖: M.accept, M.evalFrom, accept, evalFrom
-/
def acceptsFrom (s : σ) : Language α := {x | M.evalFrom s x in M.accept}

/--
theorem `mem_acceptsFrom` / 定理 `mem_acceptsFrom`

English:
theorem mem_acceptsFrom
  given: {s : σ} {x : List α}
  proof: by rfl

中文:
定理 mem_acceptsFrom
  条件: {s : σ} {x : 列表 α}
  证明: by rfl
-/
theorem mem_acceptsFrom {s : σ} {x : List α} :
    x in M.acceptsFrom s ↔ M.evalFrom s x in M.accept := by rfl

/--
Definition of `accepts` / `accepts` 的定义

English:
definition accepts
  signature: : Language α
  body: M.acceptsFrom M.start

中文:
定义 accepts
  签名: : Language α
  定义体: M.acceptsFrom M.start

Depends on / 依赖: M.acceptsFrom, M.start, acceptsFrom
-/
def accepts : Language α := M.acceptsFrom M.start

/--
theorem `mem_accepts` / 定理 `mem_accepts`

English:
theorem mem_accepts
  given: {x : List α}
  statement: x in M.accepts ↔ M.eval x in M.accept
  proof: by rfl

中文:
定理 mem_accepts
  条件: {x : 列表 α}
  结论: x in M.accepts ↔ M.eval x in M.accept
  证明: by rfl
-/
theorem mem_accepts {x : List α} : x in M.accepts ↔ M.eval x in M.accept := by rfl

/--
theorem `evalFrom_split` / 定理 `evalFrom_split`

English:
theorem evalFrom_split
  statement: [Fintype σ] {x : List α} {s t : σ} (hlen : Fintype.card σ <= x.length)
  proof: by
  obtain ⟨n, m, hneq, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt
      (fun n : Fin (Fintype.card σ + 1) => M.evalFrom s (x.take n)) (by simp)
  wlog hle : (n : Nat) <= m generalizing n m
  · exact this m n hneq.symm heq.symm (le_of_not_ge hle)
  refine
    ⟨M.evalFrom s ((x.take m).take n),

中文:
定理 evalFrom_split
  结论: [有限类型 σ] {x : 列表 α} {s t : σ} (hlen : 有限类型.card σ <= x.length)
  证明: by
  obtain ⟨n, m, hneq, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt
      (fun n : Fin (Fintype.card σ + 1) => M.evalFrom s (x.take n)) (by simp)
  wlog hle : (n : Nat) <= m generalizing n m
  · exact this m n hneq.symm heq.symm (le_of_not_ge hle)
  refine
    ⟨M.evalFrom s ((x.take m).take n),

Depends on / 依赖: Fintype, Fintype.card, Fintype.exists_ne_map_eq_of_card_lt, List.len, List.length_drop, List.length_take, List.take_append_drop, M.evalFrom, congr_arg, evalFrom, exists_ne_map_eq_of_card_lt, generalizing, heq.symm, hneq.symm, le_of_not_ge, length_drop, length_take, take_append_drop, x.drop, x.take
-/
theorem evalFrom_split [Fintype σ] {x : List α} {s t : σ} (hlen : Fintype.card σ <= x.length)
    (hx : M.evalFrom s x = t) :
    exists q a b c,
      x = a ++ b ++ c ∧
        a.length + b.length <= Fintype.card σ ∧
          b != [] ∧ M.evalFrom s a = q ∧ M.evalFrom q b = q ∧ M.evalFrom q c = t := by
  obtain ⟨n, m, hneq, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt
      (fun n : Fin (Fintype.card σ + 1) => M.evalFrom s (x.take n)) (by simp)
  wlog hle : (n : Nat) <= m generalizing n m
  · exact this m n hneq.symm heq.symm (le_of_not_ge hle)
  refine
    ⟨M.evalFrom s ((x.take m).take n), (x.take m).take n, (x.take m).drop n,
                    x.drop m, ?_, ?_, ?_, by rfl, ?_⟩
  · rw [List.take_append_drop, List.take_append_drop]
  · simp only [List.length_drop, List.length_take]
    omega
  · intro h
    have hlen' := congr_arg List.length h
    simp only [List.length_drop, List.length, List.length_take] at hlen'
    omega
  have hq : M.evalFrom (M.evalFrom s ((x.take m).take n)) ((x.take m).drop n) =
      M.evalFrom s ((x.take m).take n) := by
    rw [List.take_take]; rw [min_eq_left hle]; rw [← evalFrom_of_append]; rw [heq]; rw [← min_eq_left hle]; rw [←
      List.take_take]; rw [min_eq_left hle]; rw [List.take_append_drop]
  use hq
  rwa [← hq, ← evalFrom_of_append, ← evalFrom_of_append, ← List.append_assoc,
    List.take_append_drop, List.take_append_drop]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `evalFrom_of_pow` / 定理 `evalFrom_of_pow`

English:
theorem evalFrom_of_pow
  statement: {x y : List α} {s : σ} (hx : M.evalFrom s x = s)
  proof: by
  rw [Language.mem_kstar] at hy
  rcases hy with ⟨S, rfl, hS⟩
  induction S with
  | nil => rfl
  | cons a S ih =>
    have ha := hS a List.mem_cons_self
    rw [Set.mem_singleton_iff] at ha
    rw [List.flatten_cons]; rw [evalFrom_of_append]; rw [ha]; rw [hx]
    apply ih
    intro z hz
    exac

中文:
定理 evalFrom_of_pow
  结论: {x y : 列表 α} {s : σ} (hx : M.evalFrom s x = s)
  证明: by
  rw [Language.mem_kstar] at hy
  rcases hy with ⟨S, rfl, hS⟩
  induction S with
  | nil => rfl
  | cons a S ih =>
    have ha := hS a List.mem_cons_self
    rw [Set.mem_singleton_iff] at ha
    rw [List.flatten_cons]; rw [evalFrom_of_append]; rw [ha]; rw [hx]
    apply ih
    intro z hz
    exac

Depends on / 依赖: Language, Language.mem_kstar, List.flatten_cons, List.mem_cons_of_mem, List.mem_cons_self, Set.mem_singleton_iff, evalFrom_of_append, flatten_cons, mem_cons_of_mem, mem_cons_self, mem_kstar, mem_singleton_iff
-/
theorem evalFrom_of_pow {x y : List α} {s : σ} (hx : M.evalFrom s x = s)
    (hy : y in ({x} : Language α)∗) : M.evalFrom s y = s := by
  rw [Language.mem_kstar] at hy
  rcases hy with ⟨S, rfl, hS⟩
  induction S with
  | nil => rfl
  | cons a S ih =>
    have ha := hS a List.mem_cons_self
    rw [Set.mem_singleton_iff] at ha
    rw [List.flatten_cons]; rw [evalFrom_of_append]; rw [ha]; rw [hx]
    apply ih
    intro z hz
    exact hS z (List.mem_cons_of_mem a hz)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `pumping_lemma` / 定理 `pumping_lemma`

English:
theorem pumping_lemma
  statement: [Fintype σ] {x : List α} (hx : x in M.accepts)
  proof: by
  obtain ⟨_, a, b, c, hx, hlen, hnil, rfl, hb, hc⟩ := M.evalFrom_split (s := M.start) hlen rfl
  use a, b, c, hx, hlen, hnil
  intro y hy
  rw [Language.mem_mul] at hy
  rcases hy with ⟨ab, hab, c', hc', rfl⟩
  rw [Language.mem_mul] at hab
  rcases hab with ⟨a', ha', b', hb', rfl⟩
  rw [Set.mem_s

中文:
定理 pumping_lemma
  结论: [有限类型 σ] {x : 列表 α} (hx : x in M.accepts)
  证明: by
  obtain ⟨_, a, b, c, hx, hlen, hnil, rfl, hb, hc⟩ := M.evalFrom_split (s := M.start) hlen rfl
  use a, b, c, hx, hlen, hnil
  intro y hy
  rw [Language.mem_mul] at hy
  rcases hy with ⟨ab, hab, c', hc', rfl⟩
  rw [Language.mem_mul] at hab
  rcases hab with ⟨a', ha', b', hb', rfl⟩
  rw [Set.mem_s

Depends on / 依赖: Language, Language.mem_mul, M.evalFrom_of_pow, M.evalFrom_split, M.start, Set.mem_singleton_iff, evalFrom_of_append, evalFrom_of_pow, evalFrom_split, mem_accepts, mem_mul, mem_singleton_iff
-/
theorem pumping_lemma [Fintype σ] {x : List α} (hx : x in M.accepts)
    (hlen : Fintype.card σ <= List.length x) :
    exists a b c,
      x = a ++ b ++ c ∧
        a.length + b.length <= Fintype.card σ ∧ b != [] ∧ {a} * {b}∗ * {c} <= M.accepts := by
  obtain ⟨_, a, b, c, hx, hlen, hnil, rfl, hb, hc⟩ := M.evalFrom_split (s := M.start) hlen rfl
  use a, b, c, hx, hlen, hnil
  intro y hy
  rw [Language.mem_mul] at hy
  rcases hy with ⟨ab, hab, c', hc', rfl⟩
  rw [Language.mem_mul] at hab
  rcases hab with ⟨a', ha', b', hb', rfl⟩
  rw [Set.mem_singleton_iff] at ha' hc'
  subst ha' hc'
  have h := M.evalFrom_of_pow hb hb'
  rwa [mem_accepts, eval, evalFrom_of_append, evalFrom_of_append, h, hc]

section Maps

variable {α' σ' : Type*}

/--
`M.comap f` pulls back the alphabet of `M` along `f`. In other words, it applies `f` to the input
before passing it to `M`.
-/
@[simps]
/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (f : α' -> α) (M : DFA α σ)
  body: M.step s (f a)
  start := M.start
  accept := M.accept

@[simp]

中文:
定义 comap
  签名: (f : α' -> α) (M : DFA α σ)
  定义体: M.step s (f a)
  start := M.start
  accept := M.accept

@[simp]

Depends on / 依赖: M.step
-/
def comap (f : α' -> α) (M : DFA α σ) : DFA α' σ where
  step s a := M.step s (f a)
  start := M.start
  accept := M.accept

@[simp]
/--
theorem `comap_id` / 定理 `comap_id`

English:
theorem comap_id
  statement: M.comap id = M
  proof: rfl

@[simp]

中文:
定理 comap_id
  结论: M.comap id = M
  证明: rfl

@[simp]
-/
theorem comap_id : M.comap id = M := rfl

@[simp]
/--
theorem `evalFrom_comap` / 定理 `evalFrom_comap`

English:
theorem evalFrom_comap
  given: (f : α' -> α) (s : σ) (x : List α')
  proof: by
  induction x using List.reverseRecOn with
  | nil => simp
  | append_singleton x a ih => simp [ih]

@[simp]

中文:
定理 evalFrom_comap
  条件: (f : α' -> α) (s : σ) (x : 列表 α')
  证明: by
  induction x using List.reverseRecOn with
  | nil => simp
  | append_singleton x a ih => simp [ih]

@[simp]

Depends on / 依赖: List.reverseRecOn, append_singleton, reverseRecOn
-/
theorem evalFrom_comap (f : α' -> α) (s : σ) (x : List α') :
    (M.comap f).evalFrom s x = M.evalFrom s (x.map f) := by
  induction x using List.reverseRecOn with
  | nil => simp
  | append_singleton x a ih => simp [ih]

@[simp]
/--
theorem `eval_comap` / 定理 `eval_comap`

English:
theorem eval_comap
  given: (f : α' -> α) (x : List α')
  statement: (M.comap f).eval x = M.eval (x.map f)
  proof: by
  simp [eval]

中文:
定理 eval_comap
  条件: (f : α' -> α) (x : 列表 α')
  结论: (M.comap f).eval x = M.eval (x.map f)
  证明: by
  simp [eval]
-/
theorem eval_comap (f : α' -> α) (x : List α') : (M.comap f).eval x = M.eval (x.map f) := by
  simp [eval]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `accepts_comap` / 定理 `accepts_comap`

English:
theorem accepts_comap
  given: (f : α' -> α)
  statement: (M.comap f).accepts = List.map f ⁻¹' M.accepts
  proof: by
  ext x
  conv =>
    rhs
    rw [Set.mem_preimage]; rw [mem_accepts]
  simp [mem_accepts]

中文:
定理 accepts_comap
  条件: (f : α' -> α)
  结论: (M.comap f).accepts = 列表.map f ⁻¹' M.accepts
  证明: by
  ext x
  conv =>
    rhs
    rw [Set.mem_preimage]; rw [mem_accepts]
  simp [mem_accepts]

Depends on / 依赖: Set.mem_preimage, mem_accepts, mem_preimage
-/
theorem accepts_comap (f : α' -> α) : (M.comap f).accepts = List.map f ⁻¹' M.accepts := by
  ext x
  conv =>
    rhs
    rw [Set.mem_preimage]; rw [mem_accepts]
  simp [mem_accepts]

/-- Lifts an equivalence on states to an equivalence on DFAs. -/
@[simps apply_step apply_start apply_accept]
/--
Definition of `reindex` / `reindex` 的定义

English:
definition reindex
  signature: (g : σ ≃ σ')
  body: {
    step := fun s a => g (M.step (g.symm s) a)
    start := g M.start
    accept := g.symm ⁻¹' M.accept
  }
  invFun M := {
    step := fun s a => g.symm (M.step (g s) a)
    start := g.symm M.start
    accept := g ⁻¹' M.accept
  }
  left_inv M := by simp
  right_inv M := by simp

@[simp]

中文:
定义 reindex
  签名: (g : σ ≃ σ')
  定义体: {
    step := fun s a => g (M.step (g.symm s) a)
    start := g M.start
    accept := g.symm ⁻¹' M.accept
  }
  invFun M := {
    step := fun s a => g.symm (M.step (g s) a)
    start := g.symm M.start
    accept := g ⁻¹' M.accept
  }
  left_inv M := by simp
  right_inv M := by simp

@[simp]
-/
def reindex (g : σ ≃ σ') : DFA α σ ≃ DFA α σ' where
  toFun M := {
    step := fun s a => g (M.step (g.symm s) a)
    start := g M.start
    accept := g.symm ⁻¹' M.accept
  }
  invFun M := {
    step := fun s a => g.symm (M.step (g s) a)
    start := g.symm M.start
    accept := g ⁻¹' M.accept
  }
  left_inv M := by simp
  right_inv M := by simp

@[simp]
/--
theorem `reindex_refl` / 定理 `reindex_refl`

English:
theorem reindex_refl
  statement: reindex (Equiv.refl σ) M = M
  proof: rfl

@[simp]

中文:
定理 reindex_refl
  结论: reindex (等价.refl σ) M = M
  证明: rfl

@[simp]
-/
theorem reindex_refl : reindex (Equiv.refl σ) M = M := rfl

@[simp]
/--
theorem `symm_reindex` / 定理 `symm_reindex`

English:
theorem symm_reindex
  given: (g : σ ≃ σ')
  statement: (reindex (α := α) g).symm = reindex g.symm
  proof: rfl

@[simp]

中文:
定理 symm_reindex
  条件: (g : σ ≃ σ')
  结论: (reindex (α := α) g).symm = reindex g.symm
  证明: rfl

@[simp]

Depends on / 依赖: g.symm, reindex
-/
theorem symm_reindex (g : σ ≃ σ') : (reindex (α := α) g).symm = reindex g.symm := rfl

@[simp]
/--
theorem `evalFrom_reindex` / 定理 `evalFrom_reindex`

English:
theorem evalFrom_reindex
  given: (g : σ ≃ σ') (s : σ') (x : List α)
  proof: by
  induction x using List.reverseRecOn with
  | nil => simp
  | append_singleton x a ih => simp [ih]

@[simp]

中文:
定理 evalFrom_reindex
  条件: (g : σ ≃ σ') (s : σ') (x : 列表 α)
  证明: by
  induction x using List.reverseRecOn with
  | nil => simp
  | append_singleton x a ih => simp [ih]

@[simp]

Depends on / 依赖: List.reverseRecOn, append_singleton, reverseRecOn
-/
theorem evalFrom_reindex (g : σ ≃ σ') (s : σ') (x : List α) :
    (reindex g M).evalFrom s x = g (M.evalFrom (g.symm s) x) := by
  induction x using List.reverseRecOn with
  | nil => simp
  | append_singleton x a ih => simp [ih]

@[simp]
/--
theorem `eval_reindex` / 定理 `eval_reindex`

English:
theorem eval_reindex
  given: (g : σ ≃ σ') (x : List α)
  statement: (reindex g M).eval x = g (M.eval x)
  proof: by
  simp [eval]

@[simp]

中文:
定理 eval_reindex
  条件: (g : σ ≃ σ') (x : 列表 α)
  结论: (reindex g M).eval x = g (M.eval x)
  证明: by
  simp [eval]

@[simp]
-/
theorem eval_reindex (g : σ ≃ σ') (x : List α) : (reindex g M).eval x = g (M.eval x) := by
  simp [eval]

@[simp]
/--
theorem `accepts_reindex` / 定理 `accepts_reindex`

English:
theorem accepts_reindex
  given: (g : σ ≃ σ')
  statement: (reindex g M).accepts = M.accepts
  proof: by
  ext x
  simp [mem_accepts]

中文:
定理 accepts_reindex
  条件: (g : σ ≃ σ')
  结论: (reindex g M).accepts = M.accepts
  证明: by
  ext x
  simp [mem_accepts]

Depends on / 依赖: mem_accepts
-/
theorem accepts_reindex (g : σ ≃ σ') : (reindex g M).accepts = M.accepts := by
  ext x
  simp [mem_accepts]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `comap_reindex` / 定理 `comap_reindex`

English:
theorem comap_reindex
  given: (f : α' -> α) (g : σ ≃ σ')
  proof: by
  simp [comap, reindex]

中文:
定理 comap_reindex
  条件: (f : α' -> α) (g : σ ≃ σ')
  证明: by
  simp [comap, reindex]

Depends on / 依赖: reindex
-/
theorem comap_reindex (f : α' -> α) (g : σ ≃ σ') :
    (reindex g M).comap f = reindex g (M.comap f) := by
  simp [comap, reindex]

end Maps

section compl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Compl (DFA α σ)
  body: ⟨M.step, M.start, M.acceptᶜ⟩

中文:
实例 :
  签名: 补集 (DFA α σ)
  定义体: ⟨M.step, M.start, M.acceptᶜ⟩

Depends on / 依赖: M.accept, M.start, M.step
-/
instance : Compl (DFA α σ) where
  compl M := ⟨M.step, M.start, M.acceptᶜ⟩

/--
theorem `compl_def` / 定理 `compl_def`

English:
theorem compl_def
  statement: Mᶜ = ⟨M.step, M.start, M.acceptᶜ⟩
  proof: rfl

@[simp]

中文:
定理 compl_def
  结论: Mᶜ = ⟨M.step, M.start, M.acceptᶜ⟩
  证明: rfl

@[simp]
-/
theorem compl_def : Mᶜ = ⟨M.step, M.start, M.acceptᶜ⟩ :=
  rfl

@[simp]
/--
theorem `acceptsFrom_compl` / 定理 `acceptsFrom_compl`

English:
theorem acceptsFrom_compl
  given: (s : σ)
  statement: (Mᶜ).acceptsFrom s = (M.acceptsFrom s)ᶜ
  proof: rfl

@[simp]

中文:
定理 acceptsFrom_compl
  条件: (s : σ)
  结论: (Mᶜ).acceptsFrom s = (M.acceptsFrom s)ᶜ
  证明: rfl

@[simp]
-/
theorem acceptsFrom_compl (s : σ) : (Mᶜ).acceptsFrom s = (M.acceptsFrom s)ᶜ :=
  rfl

@[simp]
/--
theorem `accepts_compl` / 定理 `accepts_compl`

English:
theorem accepts_compl
  statement: (Mᶜ).accepts = (M.accepts)ᶜ
  proof: rfl

中文:
定理 accepts_compl
  结论: (Mᶜ).accepts = (M.accepts)ᶜ
  证明: rfl
-/
theorem accepts_compl : (Mᶜ).accepts = (M.accepts)ᶜ :=
  rfl

end compl

section union

variable {σ1 σ2 : Type v}

/-- DFAs are closed under union. -/
@[simps]
/--
Definition of `union` / `union` 的定义

English:
definition union
  signature: (M1 : DFA α σ1) (M2 : DFA α σ2)
  body: (M1.step s.1 a, M2.step s.2 a)
  start := (M1.start, M2.start)
  accept := {s : σ1 × σ2 | s.1 in M1.accept ∨ s.2 in M2.accept}

中文:
定义 union
  签名: (M1 : DFA α σ1) (M2 : DFA α σ2)
  定义体: (M1.step s.1 a, M2.step s.2 a)
  start := (M1.start, M2.start)
  accept := {s : σ1 × σ2 | s.1 in M1.accept ∨ s.2 in M2.accept}

Depends on / 依赖: M1.step, M2.step
-/
def union (M1 : DFA α σ1) (M2 : DFA α σ2) : DFA α (σ1 × σ2) where
  step (s : σ1 × σ2) (a : α) : σ1 × σ2 := (M1.step s.1 a, M2.step s.2 a)
  start := (M1.start, M2.start)
  accept := {s : σ1 × σ2 | s.1 in M1.accept ∨ s.2 in M2.accept}

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `acceptsFrom_union` / 定理 `acceptsFrom_union`

English:
theorem acceptsFrom_union
  given: (M1 : DFA α σ1) (M2 : DFA α σ2) (s1 : σ1) (s2 : σ2)
  proof: by
  ext x
  simp only [acceptsFrom]
  rw [Language.add_def]; rw [Set.mem_union]
  simp_rw [↑Set.mem_ofPred]
  induction x generalizing s1 s2 with
  | nil => simp
  | cons a x ih => simp only [evalFrom_cons, union_step, ih]

@[simp]

中文:
定理 acceptsFrom_union
  条件: (M1 : DFA α σ1) (M2 : DFA α σ2) (s1 : σ1) (s2 : σ2)
  证明: by
  ext x
  simp only [acceptsFrom]
  rw [Language.add_def]; rw [Set.mem_union]
  simp_rw [↑Set.mem_ofPred]
  induction x generalizing s1 s2 with
  | nil => simp
  | cons a x ih => simp only [evalFrom_cons, union_step, ih]

@[simp]

Depends on / 依赖: Language, Language.add_def, Set.mem_ofPred, Set.mem_union, acceptsFrom, add_def, evalFrom_cons, generalizing, mem_ofPred, mem_union, simp_rw, union_step
-/
theorem acceptsFrom_union (M1 : DFA α σ1) (M2 : DFA α σ2) (s1 : σ1) (s2 : σ2) :
    (M1.union M2).acceptsFrom (s1, s2) = M1.acceptsFrom s1 + M2.acceptsFrom s2 := by
  ext x
  simp only [acceptsFrom]
  rw [Language.add_def]; rw [Set.mem_union]
  simp_rw [↑Set.mem_ofPred]
  induction x generalizing s1 s2 with
  | nil => simp
  | cons a x ih => simp only [evalFrom_cons, union_step, ih]

@[simp]
/--
theorem `accepts_union` / 定理 `accepts_union`

English:
theorem accepts_union
  given: (M1 : DFA α σ1) (M2 : DFA α σ2)
  proof: by
  simp [accepts]

中文:
定理 accepts_union
  条件: (M1 : DFA α σ1) (M2 : DFA α σ2)
  证明: by
  simp [accepts]

Depends on / 依赖: accepts
-/
theorem accepts_union (M1 : DFA α σ1) (M2 : DFA α σ2) :
    (M1.union M2).accepts = M1.accepts + M2.accepts := by
  simp [accepts]

end union

section inter

variable {σ1 σ2 : Type v} (M1 : DFA α σ1) (M2 : DFA α σ2)

/-- DFAs are closed under intersection. -/
@[simps]
/--
Definition of `inter` / `inter` 的定义

English:
definition inter
  signature: : DFA α (σ1 × σ2) where
  body: (M1.step s.1 a, M2.step s.2 a)
  start := (M1.start, M2.start)
  accept := {s : σ1 × σ2 | s.1 in M1.accept ∧ s.2 in M2.accept}

中文:
定义 inter
  签名: : DFA α (σ1 × σ2) where
  定义体: (M1.step s.1 a, M2.step s.2 a)
  start := (M1.start, M2.start)
  accept := {s : σ1 × σ2 | s.1 in M1.accept ∧ s.2 in M2.accept}

Depends on / 依赖: M1.step, M2.step
-/
def inter : DFA α (σ1 × σ2) where
  step (s : σ1 × σ2) (a : α) : σ1 × σ2 := (M1.step s.1 a, M2.step s.2 a)
  start := (M1.start, M2.start)
  accept := {s : σ1 × σ2 | s.1 in M1.accept ∧ s.2 in M2.accept}

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `acceptsFrom_inter` / 定理 `acceptsFrom_inter`

English:
theorem acceptsFrom_inter
  given: (s1 : σ1) (s2 : σ2)
  proof: by
  ext x
  simp only [acceptsFrom, Language.mem_inf]
  simp_rw [↑Set.mem_ofPred]
  induction x generalizing s1 s2 with
  | nil => simp
  | cons a x ih => simp only [evalFrom_cons, inter_step, ih]

@[simp]

中文:
定理 acceptsFrom_inter
  条件: (s1 : σ1) (s2 : σ2)
  证明: by
  ext x
  simp only [acceptsFrom, Language.mem_inf]
  simp_rw [↑Set.mem_ofPred]
  induction x generalizing s1 s2 with
  | nil => simp
  | cons a x ih => simp only [evalFrom_cons, inter_step, ih]

@[simp]

Depends on / 依赖: Language, Language.mem_inf, Set.mem_ofPred, acceptsFrom, evalFrom_cons, generalizing, inter_step, mem_inf, mem_ofPred, simp_rw
-/
theorem acceptsFrom_inter (s1 : σ1) (s2 : σ2) :
    (M1.inter M2).acceptsFrom (s1, s2) = M1.acceptsFrom s1 ⊓ M2.acceptsFrom s2 := by
  ext x
  simp only [acceptsFrom, Language.mem_inf]
  simp_rw [↑Set.mem_ofPred]
  induction x generalizing s1 s2 with
  | nil => simp
  | cons a x ih => simp only [evalFrom_cons, inter_step, ih]

@[simp]
/--
theorem `accepts_inter` / 定理 `accepts_inter`

English:
theorem accepts_inter
  statement: (M1.inter M2).accepts = M1.accepts ⊓ M2.accepts
  proof: by
  simp [accepts]

中文:
定理 accepts_inter
  结论: (M1.inter M2).accepts = M1.accepts ⊓ M2.accepts
  证明: by
  simp [accepts]

Depends on / 依赖: accepts
-/
theorem accepts_inter : (M1.inter M2).accepts = M1.accepts ⊓ M2.accepts := by
  simp [accepts]

end inter

end DFA

namespace Language

/--
Definition of `IsRegular` / `IsRegular` 的定义

English:
definition IsRegular
  signature: {T : Type u} (L : Language T)
  body: exists σ : Type, exists _ : Fintype σ, exists M : DFA T σ, M.accepts = L

中文:
定义 是正则
  签名: {T : 类型u} (L : Language T)
  定义体: exists σ : Type, exists _ : Fintype σ, exists M : DFA T σ, M.accepts = L

Depends on / 依赖: Fintype, M.accepts, accepts
-/
def IsRegular {T : Type u} (L : Language T) : Prop :=
  exists σ : Type, exists _ : Fintype σ, exists M : DFA T σ, M.accepts = L

/--
lemma `isRegular_iff.helper.` / 引理 `isRegular_iff.helper.`

English:
lemma isRegular_iff.helper.{v'}
  statement: {T : Type u} {L : Language T}
  proof: have ⟨σ, _, M, hM⟩ := hL
  have ⟨σ', ⟨f⟩⟩ := Small.equiv_small.{v', v} (α := σ)
  ⟨σ', Fintype.ofEquiv σ f, M.reindex f, hM ▸ DFA.accepts_reindex M f⟩

中文:
引理 isRegular_iff.helper.{v'}
  结论: {T : 类型u} {L : Language T}
  证明: have ⟨σ, _, M, hM⟩ := hL
  have ⟨σ', ⟨f⟩⟩ := Small.equiv_small.{v', v} (α := σ)
  ⟨σ', Fintype.ofEquiv σ f, M.reindex f, hM ▸ DFA.accepts_reindex M f⟩
-/
private lemma isRegular_iff.helper.{v'} {T : Type u} {L : Language T}
    (hL : exists σ : Type v, exists _ : Fintype σ, exists M : DFA T σ, M.accepts = L) :
    exists σ' : Type v', exists _ : Fintype σ', exists M : DFA T σ', M.accepts = L :=
  have ⟨σ, _, M, hM⟩ := hL
  have ⟨σ', ⟨f⟩⟩ := Small.equiv_small.{v', v} (α := σ)
  ⟨σ', Fintype.ofEquiv σ f, M.reindex f, hM ▸ DFA.accepts_reindex M f⟩

/--
theorem `isRegular_iff` / 定理 `isRegular_iff`

English:
theorem isRegular_iff
  given: {T : Type u} {L : Language T}
  proof: ⟨Language.isRegular_iff.helper, Language.isRegular_iff.helper⟩

中文:
定理 isRegular_iff
  条件: {T : 类型u} {L : Language T}
  证明: ⟨Language.isRegular_iff.helper, Language.isRegular_iff.helper⟩

Depends on / 依赖: Language, Language.isRegular_iff.helper, eq_of_forall_ge_iff, forall_comm, helper, isRegular_iff
-/
theorem isRegular_iff {T : Type u} {L : Language T} :
    L.IsRegular ↔ exists σ : Type v, exists _ : Fintype σ, exists M : DFA T σ, M.accepts = L :=
  ⟨Language.isRegular_iff.helper, Language.isRegular_iff.helper⟩

/--
theorem `IsRegular.compl` / 定理 `IsRegular.compl`

English:
theorem IsRegular.compl
  given: {T : Type u} {L : Language T} (h : L.IsRegular)
  statement: Lᶜ.IsRegular
  proof: have ⟨σ, _, M, hM⟩ := h
  ⟨σ, inferInstance, Mᶜ, by simp [hM]⟩

中文:
定理 是正则.compl
  条件: {T : 类型u} {L : Language T} (h : L.是正则)
  结论: Lᶜ.是正则
  证明: have ⟨σ, _, M, hM⟩ := h
  ⟨σ, inferInstance, Mᶜ, by simp [hM]⟩

Depends on / 依赖: Finset, Finset.sup, _comm, _product_left
-/
protected theorem IsRegular.compl {T : Type u} {L : Language T} (h : L.IsRegular) : Lᶜ.IsRegular :=
  have ⟨σ, _, M, hM⟩ := h
  ⟨σ, inferInstance, Mᶜ, by simp [hM]⟩

/--
theorem `IsRegular.of_compl` / 定理 `IsRegular.of_compl`

English:
theorem IsRegular.of_compl
  given: {T : Type u} {L : Language T} (h : Lᶜ.IsRegular)
  proof: L.compl_compl ▸ h.compl

中文:
定理 是正则.of_compl
  条件: {T : 类型u} {L : Language T} (h : Lᶜ.是正则)
  证明: L.compl_compl ▸ h.compl
-/
protected theorem IsRegular.of_compl {T : Type u} {L : Language T} (h : Lᶜ.IsRegular) :
  L.IsRegular :=
  L.compl_compl ▸ h.compl

/-- Regular languages are closed under complement. -/
@[simp]
/--
theorem `IsRegular_compl` / 定理 `IsRegular_compl`

English:
theorem IsRegular_compl
  given: {T : Type u} {L : Language T}
  statement: Lᶜ.IsRegular ↔ L.IsRegular
  proof: ⟨.of_compl, .compl⟩

中文:
定理 IsRegular_compl
  条件: {T : 类型u} {L : Language T}
  结论: Lᶜ.是正则 ↔ L.是正则
  证明: ⟨.of_compl, .compl⟩

Depends on / 依赖: _sup, of_compl, prodMk_sup
-/
theorem IsRegular_compl {T : Type u} {L : Language T} : Lᶜ.IsRegular ↔ L.IsRegular :=
  ⟨.of_compl, .compl⟩

/--
theorem `IsRegular.add` / 定理 `IsRegular.add`

English:
theorem IsRegular.add
  given: {T : Type u} {L1 L2 : Language T} (h1 : L1.IsRegular) (h2 : L2.IsRegular)
  proof: have ⟨σ1, _, M1, hM1⟩ := h1
  have ⟨σ2, _, M2, hM2⟩ := h2
  ⟨σ1 × σ2, inferInstance, M1.union M2, by simp [hM1, hM2]⟩

中文:
定理 是正则.add
  条件: {T : 类型u} {L1 L2 : Language T} (h1 : L1.是正则) (h2 : L2.是正则)
  证明: have ⟨σ1, _, M1, hM1⟩ := h1
  have ⟨σ2, _, M2, hM2⟩ := h2
  ⟨σ1 × σ2, inferInstance, M1.union M2, by simp [hM1, hM2]⟩

Depends on / 依赖: Finset, Finset.sup, M1.union, _inf_distrib_left, _inf_distrib_right, _product_left, simp_rw
-/
theorem IsRegular.add {T : Type u} {L1 L2 : Language T} (h1 : L1.IsRegular) (h2 : L2.IsRegular) :
    (L1 + L2).IsRegular :=
  have ⟨σ1, _, M1, hM1⟩ := h1
  have ⟨σ2, _, M2, hM2⟩ := h2
  ⟨σ1 × σ2, inferInstance, M1.union M2, by simp [hM1, hM2]⟩

/--
theorem `IsRegular.inf` / 定理 `IsRegular.inf`

English:
theorem IsRegular.inf
  given: {T : Type u} {L1 L2 : Language T} (h1 : L1.IsRegular) (h2 : L2.IsRegular)
  proof: have ⟨σ1, _, M1, hM1⟩ := h1
  have ⟨σ2, _, M2, hM2⟩ := h2
  ⟨σ1 × σ2, inferInstance, M1.inter M2, by simp [hM1, hM2]⟩

中文:
定理 是正则.下确界
  条件: {T : 类型u} {L1 L2 : Language T} (h1 : L1.是正则) (h2 : L2.是正则)
  证明: have ⟨σ1, _, M1, hM1⟩ := h1
  have ⟨σ2, _, M2, hM2⟩ := h2
  ⟨σ1 × σ2, inferInstance, M1.inter M2, by simp [hM1, hM2]⟩

Depends on / 依赖: M1.inter
-/
theorem IsRegular.inf {T : Type u} {L1 L2 : Language T} (h1 : L1.IsRegular) (h2 : L2.IsRegular) :
    (L1 ⊓ L2).IsRegular :=
  have ⟨σ1, _, M1, hM1⟩ := h1
  have ⟨σ2, _, M2, hM2⟩ := h2
  ⟨σ1 × σ2, inferInstance, M1.inter M2, by simp [hM1, hM2]⟩

end Language
