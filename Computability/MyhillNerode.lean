/-
Copyright (c) 2024 Google. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Wong
-/
module

public import Mathlib.Computability.DFA
public import Mathlib.Data.Set.Finite.Basic

/-!
# Myhill–Nerode theorem

This file proves the Myhill–Nerode theorem using left quotients.

Given a language `L` and a word `x`, the *left quotient* of `L` by `x` is the set of suffixes `y`
such that `x ++ y` is in `L`. The *Myhill–Nerode theorem* shows that each left quotient, in fact,
corresponds to the state of an automaton that matches `L`, and that `L` is regular if and only if
there are finitely many such states.

## References

* <https://en.wikipedia.org/wiki/Syntactic_monoid#Myhill%E2%80%93Nerode_theorem>
-/

@[expose] public section

universe u v
variable {α : Type u} {σ : Type v} {L : Language α}

namespace Language

variable (L) in
/--
Definition of `leftQuotient` / `leftQuotient` 的定义

English:
definition leftQuotient
  signature: (x : List α)
  body: { y | x ++ y in L }

中文:
定义 leftQuotient
  签名: (x : List α)
  定义体: { y | x ++ y in L }
-/
def leftQuotient (x : List α) : Language α := { y | x ++ y in L }

variable (L) in
@[simp]
/--
theorem `leftQuotient_nil` / 定理 `leftQuotient_nil`

English:
theorem leftQuotient_nil
  statement: L.leftQuotient [] = L
  proof: rfl

中文:
定理 leftQuotient_nil
  结论: L.leftQuotient [] = L
  证明: rfl
-/
theorem leftQuotient_nil : L.leftQuotient [] = L := rfl

set_option backward.isDefEq.respectTransparency false in
variable (L) in
/--
theorem `leftQuotient_append` / 定理 `leftQuotient_append`

English:
theorem leftQuotient_append
  given: (x y : List α)
  proof: by
  simp [leftQuotient, Language]

@[simp]

中文:
定理 leftQuotient_append
  条件: (x y : List α)
  证明: by
  simp [leftQuotient, Language]

@[simp]

Depends on / 依赖: Language, leftQuotient
-/
theorem leftQuotient_append (x y : List α) :
    L.leftQuotient (x ++ y) = (L.leftQuotient x).leftQuotient y := by
  simp [leftQuotient, Language]

@[simp]
/--
theorem `mem_leftQuotient` / 定理 `mem_leftQuotient`

English:
theorem mem_leftQuotient
  given: (x y : List α)
  statement: y in L.leftQuotient x ↔ x ++ y in L
  proof: Iff.rfl

中文:
定理 mem_leftQuotient
  条件: (x y : List α)
  结论: y in L.leftQuotient x ↔ x ++ y in L
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_leftQuotient (x y : List α) : y in L.leftQuotient x ↔ x ++ y in L := Iff.rfl

/--
theorem `leftQuotient_accepts_apply` / 定理 `leftQuotient_accepts_apply`

English:
theorem leftQuotient_accepts_apply
  given: (M : DFA α σ) (x : List α)
  proof: by
  ext y
  simp [DFA.mem_accepts, DFA.mem_acceptsFrom, DFA.eval, DFA.evalFrom_of_append]

中文:
定理 leftQuotient_accepts_apply
  条件: (M : DFA α σ) (x : List α)
  证明: by
  ext y
  simp [DFA.mem_accepts, DFA.mem_acceptsFrom, DFA.eval, DFA.evalFrom_of_append]

Depends on / 依赖: DFA.eval, DFA.evalFrom_of_append, DFA.mem_accepts, DFA.mem_acceptsFrom, evalFrom_of_append, mem_accepts, mem_acceptsFrom
-/
theorem leftQuotient_accepts_apply (M : DFA α σ) (x : List α) :
    leftQuotient M.accepts x = M.acceptsFrom (M.eval x) := by
  ext y
  simp [DFA.mem_accepts, DFA.mem_acceptsFrom, DFA.eval, DFA.evalFrom_of_append]

/--
theorem `leftQuotient_accepts` / 定理 `leftQuotient_accepts`

English:
theorem leftQuotient_accepts
  given: (M : DFA α σ)
  statement: leftQuotient M.accepts = M.acceptsFrom ∘ M.eval
  proof: funext leftQuotient_accepts_apply M

中文:
定理 leftQuotient_accepts
  条件: (M : DFA α σ)
  结论: leftQuotient M.accepts = M.acceptsFrom ∘ M.eval
  证明: funext leftQuotient_accepts_apply M

Depends on / 依赖: leftQuotient_accepts_apply
-/
theorem leftQuotient_accepts (M : DFA α σ) : leftQuotient M.accepts = M.acceptsFrom ∘ M.eval :=
funext leftQuotient_accepts_apply M

/--
theorem `IsRegular.finite_range_leftQuotient` / 定理 `IsRegular.finite_range_leftQuotient`

English:
theorem IsRegular.finite_range_leftQuotient
  given: (h : L.IsRegular)
  proof: by
  have ⟨σ, x, M, hM⟩ := h
  rw [← hM]; rw [leftQuotient_accepts]
  exact Set.finite_of_finite_preimage (Set.toFinite _)
    (Set.range_comp_subset_range M.eval M.acceptsFrom)

中文:
定理 IsRegular.finite_range_leftQuotient
  条件: (h : L.IsRegular)
  证明: by
  have ⟨σ, x, M, hM⟩ := h
  rw [← hM]; rw [leftQuotient_accepts]
  exact Set.finite_of_finite_preimage (Set.toFinite _)
    (Set.range_comp_subset_range M.eval M.acceptsFrom)

Depends on / 依赖: M.acceptsFrom, M.eval, Set.finite_of_finite_preimage, Set.range_comp_subset_range, Set.toFinite, acceptsFrom, finite_of_finite_preimage, leftQuotient_accepts, range_comp_subset_range, toFinite
-/
theorem IsRegular.finite_range_leftQuotient (h : L.IsRegular) :
    (Set.range L.leftQuotient).Finite := by
  have ⟨σ, x, M, hM⟩ := h
  rw [← hM]; rw [leftQuotient_accepts]
  exact Set.finite_of_finite_preimage (Set.toFinite _)
    (Set.range_comp_subset_range M.eval M.acceptsFrom)

variable (L) in
/--
Definition of `toDFA` / `toDFA` 的定义

English:
definition toDFA
  signature: : DFA α (Set.range L.leftQuotient) where
  body: by
    refine ⟨s.val.leftQuotient [a], ?_⟩
    obtain ⟨y, hy⟩ := s.prop
    exists y ++ [a]
    rw [← hy]; rw [leftQuotient_append]
  start := ⟨L, by exists []⟩
  accept := { s | [] in s.val }

@[simp]

中文:
定义 toDFA
  签名: : DFA α (Set.range L.leftQuotient) where
  定义体: by
    refine ⟨s.val.leftQuotient [a], ?_⟩
    obtain ⟨y, hy⟩ := s.prop
    exists y ++ [a]
    rw [← hy]; rw [leftQuotient_append]
  start := ⟨L, by exists []⟩
  accept := { s | [] in s.val }

@[simp]

Depends on / 依赖: accept, leftQuotient, leftQuotient_append, s.prop, s.val, s.val.leftQuotient
-/
def toDFA : DFA α (Set.range L.leftQuotient) where
  step s a := by
    refine ⟨s.val.leftQuotient [a], ?_⟩
    obtain ⟨y, hy⟩ := s.prop
    exists y ++ [a]
    rw [← hy]; rw [leftQuotient_append]
  start := ⟨L, by exists []⟩
  accept := { s | [] in s.val }

@[simp]
/--
theorem `mem_accept_toDFA` / 定理 `mem_accept_toDFA`

English:
theorem mem_accept_toDFA
  given: (s : Set.range L.leftQuotient)
  statement: s in L.toDFA.accept ↔ [] in s.val
  proof: Iff.rfl

@[simp]

中文:
定理 mem_accept_toDFA
  条件: (s : Set.range L.leftQuotient)
  结论: s in L.toDFA.accept ↔ [] in s.val
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_accept_toDFA (s : Set.range L.leftQuotient) : s in L.toDFA.accept ↔ [] in s.val := Iff.rfl

@[simp]
/--
theorem `step_toDFA` / 定理 `step_toDFA`

English:
theorem step_toDFA
  given: (s : Set.range L.leftQuotient) (a : α)
  proof: rfl

中文:
定理 step_toDFA
  条件: (s : Set.range L.leftQuotient) (a : α)
  证明: rfl
-/
theorem step_toDFA (s : Set.range L.leftQuotient) (a : α) :
    (L.toDFA.step s a).val = s.val.leftQuotient [a] := rfl

variable (L) in
@[simp]
/--
theorem `start_toDFA` / 定理 `start_toDFA`

English:
theorem start_toDFA
  statement: L.toDFA.start.val = L
  proof: rfl

中文:
定理 start_toDFA
  结论: L.toDFA.start.val = L
  证明: rfl
-/
theorem start_toDFA : L.toDFA.start.val = L := rfl

variable (L) in
@[simp]
/--
theorem `accepts_toDFA` / 定理 `accepts_toDFA`

English:
theorem accepts_toDFA
  statement: L.toDFA.accepts = L
  proof: by
  ext x
  rw [DFA.mem_accepts]
  suffices L.toDFA.eval x = L.leftQuotient x by simp [this]
  induction x using List.reverseRecOn with
  | nil => simp
  | append_singleton x a ih => simp [ih, leftQuotient_append]

中文:
定理 accepts_toDFA
  结论: L.toDFA.accepts = L
  证明: by
  ext x
  rw [DFA.mem_accepts]
  suffices L.toDFA.eval x = L.leftQuotient x by simp [this]
  induction x using List.reverseRecOn with
  | nil => simp
  | append_singleton x a ih => simp [ih, leftQuotient_append]

Depends on / 依赖: DFA.mem_accepts, L.leftQuotient, L.toDFA.eval, List.reverseRecOn, append_singleton, leftQuotient, leftQuotient_append, mem_accepts, reverseRecOn
-/
theorem accepts_toDFA : L.toDFA.accepts = L := by
  ext x
  rw [DFA.mem_accepts]
  suffices L.toDFA.eval x = L.leftQuotient x by simp [this]
  induction x using List.reverseRecOn with
  | nil => simp
  | append_singleton x a ih => simp [ih, leftQuotient_append]

/--
theorem `IsRegular.of_finite_range_leftQuotient` / 定理 `IsRegular.of_finite_range_leftQuotient`

English:
theorem IsRegular.of_finite_range_leftQuotient
  given: (h : Set.Finite (Set.range L.leftQuotient))
  proof: Language.isRegular_iff.mpr ⟨_, h.fintype, L.toDFA, by simp⟩

中文:
定理 IsRegular.of_finite_range_leftQuotient
  条件: (h : Set.Finite (Set.range L.leftQuotient))
  证明: Language.isRegular_iff.mpr ⟨_, h.fintype, L.toDFA, by simp⟩

Depends on / 依赖: L.toDFA, Language, Language.isRegular_iff.mpr, fintype, h.fintype, isRegular_iff
-/
theorem IsRegular.of_finite_range_leftQuotient (h : Set.Finite (Set.range L.leftQuotient)) :
    L.IsRegular :=
  Language.isRegular_iff.mpr ⟨_, h.fintype, L.toDFA, by simp⟩

/--
theorem `isRegular_iff_finite_range_leftQuotient` / 定理 `isRegular_iff_finite_range_leftQuotient`

English:
theorem isRegular_iff_finite_range_leftQuotient
  proof: ⟨IsRegular.finite_range_leftQuotient, .of_finite_range_leftQuotient⟩

中文:
定理 isRegular_iff_finite_range_leftQuotient
  证明: ⟨IsRegular.finite_range_leftQuotient, .of_finite_range_leftQuotient⟩

Depends on / 依赖: IsRegular, IsRegular.finite_range_leftQuotient, finite_range_leftQuotient, of_finite_range_leftQuotient
-/
theorem isRegular_iff_finite_range_leftQuotient :
    L.IsRegular ↔ (Set.range L.leftQuotient).Finite :=
  ⟨IsRegular.finite_range_leftQuotient, .of_finite_range_leftQuotient⟩

end Language
