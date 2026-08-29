/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Group.Fin.Tuple
public import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.Order.Fin.Tuple

/-!
# Collections of tuples of naturals with the same sum

This file generalizes `List.Nat.Antidiagonal n`, `Multiset.Nat.Antidiagonal n`, and
`Finset.Nat.Antidiagonal n` from the pair of elements `x : ℕ × ℕ` such that `n = x.1 + x.2`, to
the sequence of elements `x : Fin k → ℕ` such that `n = ∑ i, x i`.

## Main definitions

* `List.Nat.antidiagonalTuple`
* `Multiset.Nat.antidiagonalTuple`
* `Finset.Nat.antidiagonalTuple`

## Main results

* `antidiagonalTuple 2 n` is analogous to `antidiagonal n`:

  * `List.Nat.antidiagonalTuple_two`
  * `Multiset.Nat.antidiagonalTuple_two`
  * `Finset.Nat.antidiagonalTuple_two`

## Implementation notes

While we could implement this by filtering `(Fintype.PiFinset fun _ ↦ range (n + 1))` or similar,
this implementation would be much slower.

In the future, we could consider generalizing `Finset.Nat.antidiagonalTuple` further to
support finitely-supported functions, as in `Finset.finsuppAntidiag` from
`Mathlib/Algebra/Order/Antidiag/Finsupp.lean`.
-/

@[expose] public section


/-! ### Lists -/


namespace List.Nat

/--
Definition of `antidiagonalTuple` / `antidiagonalTuple` 的定义

English:
definition antidiagonalTuple
  signature: : forall k, Nat -> List (Fin k -> Nat)

中文:
定义 antidiagonalTuple
  签名: : 对任意 k, 自然数 -> 列表 (有限集 k -> 自然数)
-/
def antidiagonalTuple : forall k, Nat -> List (Fin k -> Nat)
  | 0, 0 => [![]]
  | 0, _ + 1 => []
  | k + 1, n =>
    (List.Nat.antidiagonal n).flatMap fun ni =>
      (antidiagonalTuple k ni.2).map fun x => Fin.cons ni.1 x

@[simp]
/--
theorem `antidiagonalTuple_zero_zero` / 定理 `antidiagonalTuple_zero_zero`

English:
theorem antidiagonalTuple_zero_zero
  statement: antidiagonalTuple 0 0 = [![]]
  proof: rfl

@[simp]

中文:
定理 antidiagonalTuple_zero_zero
  结论: antidiagonalTuple 0 0 = [![]]
  证明: rfl

@[simp]
-/
theorem antidiagonalTuple_zero_zero : antidiagonalTuple 0 0 = [![]] :=
  rfl

@[simp]
/--
theorem `antidiagonalTuple_zero_succ` / 定理 `antidiagonalTuple_zero_succ`

English:
theorem antidiagonalTuple_zero_succ
  given: (n : Nat)
  statement: antidiagonalTuple 0 (n + 1) = []
  proof: rfl

中文:
定理 antidiagonalTuple_zero_succ
  条件: (n : 自然数)
  结论: antidiagonalTuple 0 (n + 1) = []
  证明: rfl
-/
theorem antidiagonalTuple_zero_succ (n : Nat) : antidiagonalTuple 0 (n + 1) = [] :=
  rfl

/--
theorem `mem_antidiagonalTuple` / 定理 `mem_antidiagonalTuple`

English:
theorem mem_antidiagonalTuple
  given: {n : Nat} {k : Nat} {x : Fin k -> Nat}
  proof: by
  induction x using Fin.consInduction generalizing n with
  | elim0 =>
    cases n
    · decide
    · simp
  | cons x₀ x ih =>
    simp_rw [Fin.sum_cons, antidiagonalTuple, List.mem_flatMap, List.mem_map,
      List.Nat.mem_antidiagonal, Fin.cons_inj, exists_eq_right_right, ih,
      @eq_comm _ _ (Prod.snd _), and_comm (a := Prod.snd _ = _),
      ← Prod.mk_inj (a₁ := Prod.fst _), exists_eq_right]

中文:
定理 mem_antidiagonalTuple
  条件: {n : 自然数} {k : 自然数} {x : 有限集 k -> 自然数}
  证明: by
  induction x using Fin.consInduction generalizing n with
  | elim0 =>
    cases n
    · decide
    · simp
  | cons x₀ x ih =>
    simp_rw [Fin.sum_cons, antidiagonalTuple, List.mem_flatMap, List.mem_map,
      List.Nat.mem_antidiagonal, Fin.cons_inj, exists_eq_right_right, ih,
      @eq_comm _ _ (Prod.snd _), and_comm (a := Prod.snd _ = _),
      ← Prod.mk_inj (a₁ := Prod.fst _), exists_eq_right]

Depends on / 依赖: Fin.consInduction, Fin.cons_inj, Fin.sum_cons, List.Nat.mem_antidiagonal, List.mem_flatMap, List.mem_map, Prod.fst, Prod.mk_inj, Prod.snd, and_comm, antidiagonalTuple, consInduction, cons_inj, eq_comm, exists_eq_right, exists_eq_right_right, generalizing, mem_antidiagonal, mem_flatMap, mem_map
-/
theorem mem_antidiagonalTuple {n : Nat} {k : Nat} {x : Fin k -> Nat} :
    x in antidiagonalTuple k n ↔ ∑ i, x i = n := by
  induction x using Fin.consInduction generalizing n with
  | elim0 =>
    cases n
    · decide
    · simp
  | cons x₀ x ih =>
    simp_rw [Fin.sum_cons, antidiagonalTuple, List.mem_flatMap, List.mem_map,
      List.Nat.mem_antidiagonal, Fin.cons_inj, exists_eq_right_right, ih,
      @eq_comm _ _ (Prod.snd _), and_comm (a := Prod.snd _ = _),
      ← Prod.mk_inj (a₁ := Prod.fst _), exists_eq_right]

/--
theorem `nodup_antidiagonalTuple` / 定理 `nodup_antidiagonalTuple`

English:
theorem nodup_antidiagonalTuple
  given: (k n : Nat)
  statement: List.Nodup (antidiagonalTuple k n)
  proof: by
  induction k generalizing n with
  | zero => cases n <;> simp
  | succ k ih => ?_
  simp_rw [antidiagonalTuple, List.nodup_flatMap]
  constructor
  · intro i _
    exact (ih i.snd).map (Fin.cons_right_injective (α := fun _ => Nat) i.fst)
  induction n with
  | zero => exact List.pairwise_singleton _ _
  | succ n n_ih =>
    rw [List.Nat.antidiagonal_succ]
    refine List.Pairwise.cons (fun a ha x hx₁ hx₂ => ?_) (n_ih.map _ fun a b h x hx₁ hx₂ => ?_)
    · rw [List.mem_map] at hx₁ hx₂ ha
      obtain ⟨⟨a, -, rfl⟩, ⟨x₁, -, rfl⟩, ⟨x₂, -, h⟩⟩ := ha, hx₁, hx₂
      rw [Fin.cons_inj] at h
      injection h.1
    · rw [List.mem_map] at hx₁ hx₂
      obtain ⟨⟨x₁, hx₁, rfl⟩, ⟨x₂, hx₂, h₁₂⟩⟩ := hx₁, hx₂
      dsimp at h₁₂
      rw [Fin.cons_inj]; rw [Nat.succ_inj] at h₁₂
      obtain ⟨h₁₂, rfl⟩ := h₁₂
      rw [Function.onFun]; rw [h₁₂] at h
      exact h (List.mem_map_of_mem hx₁) (List.mem_map_of_mem hx₂)

中文:
定理 nodup_antidiagonalTuple
  条件: (k n : 自然数)
  结论: 列表.Nodup (antidiagonalTuple k n)
  证明: by
  induction k generalizing n with
  | zero => cases n <;> simp
  | succ k ih => ?_
  simp_rw [antidiagonalTuple, List.nodup_flatMap]
  constructor
  · intro i _
    exact (ih i.snd).map (Fin.cons_right_injective (α := fun _ => Nat) i.fst)
  induction n with
  | zero => exact List.pairwise_singleton _ _
  | succ n n_ih =>
    rw [List.Nat.antidiagonal_succ]
    refine List.Pairwise.cons (fun a ha x hx₁ hx₂ => ?_) (n_ih.map _ fun a b h x hx₁ hx₂ => ?_)
    · rw [List.mem_map] at hx₁ hx₂ ha
      obtain ⟨⟨a, -, rfl⟩, ⟨x₁, -, rfl⟩, ⟨x₂, -, h⟩⟩ := ha, hx₁, hx₂
      rw [Fin.cons_inj] at h
      injection h.1
    · rw [List.mem_map] at hx₁ hx₂
      obtain ⟨⟨x₁, hx₁, rfl⟩, ⟨x₂, hx₂, h₁₂⟩⟩ := hx₁, hx₂
      dsimp at h₁₂
      rw [Fin.cons_inj]; rw [Nat.succ_inj] at h₁₂
      obtain ⟨h₁₂, rfl⟩ := h₁₂
      rw [Function.onFun]; rw [h₁₂] at h
      exact h (List.mem_map_of_mem hx₁) (List.mem_map_of_mem hx₂)

Depends on / 依赖: Fin.cons_right_injective, List.Nat.antidiagonal_succ, List.Pairwise.cons, List.mem_map, List.nodup_flatMap, List.pairwise_singleton, Pairwise, antidiagonalTuple, antidiagonal_succ, cons_right_injective, generalizing, i.fst, i.snd, mem_map, n_ih, n_ih.map, nodup_flatMap, pairwise_singleton, simp_rw
-/
theorem nodup_antidiagonalTuple (k n : Nat) : List.Nodup (antidiagonalTuple k n) := by
  induction k generalizing n with
  | zero => cases n <;> simp
  | succ k ih => ?_
  simp_rw [antidiagonalTuple, List.nodup_flatMap]
  constructor
  · intro i _
    exact (ih i.snd).map (Fin.cons_right_injective (α := fun _ => Nat) i.fst)
  induction n with
  | zero => exact List.pairwise_singleton _ _
  | succ n n_ih =>
    rw [List.Nat.antidiagonal_succ]
    refine List.Pairwise.cons (fun a ha x hx₁ hx₂ => ?_) (n_ih.map _ fun a b h x hx₁ hx₂ => ?_)
    · rw [List.mem_map] at hx₁ hx₂ ha
      obtain ⟨⟨a, -, rfl⟩, ⟨x₁, -, rfl⟩, ⟨x₂, -, h⟩⟩ := ha, hx₁, hx₂
      rw [Fin.cons_inj] at h
      injection h.1
    · rw [List.mem_map] at hx₁ hx₂
      obtain ⟨⟨x₁, hx₁, rfl⟩, ⟨x₂, hx₂, h₁₂⟩⟩ := hx₁, hx₂
      dsimp at h₁₂
      rw [Fin.cons_inj]; rw [Nat.succ_inj] at h₁₂
      obtain ⟨h₁₂, rfl⟩ := h₁₂
      rw [Function.onFun]; rw [h₁₂] at h
      exact h (List.mem_map_of_mem hx₁) (List.mem_map_of_mem hx₂)

/--
theorem `antidiagonalTuple_zero_right` / 定理 `antidiagonalTuple_zero_right`

English:
theorem antidiagonalTuple_zero_right
  statement: forall k, antidiagonalTuple k 0 = [0]

中文:
定理 antidiagonalTuple_zero_right
  结论: 对任意 k, antidiagonalTuple k 0 = [0]
-/
theorem antidiagonalTuple_zero_right : forall k, antidiagonalTuple k 0 = [0]
| 0 => (congr_arg fun x => [x]) Subsingleton.elim _ _
  | k + 1 => by
    rw [antidiagonalTuple]; rw [antidiagonal_zero]; rw [List.flatMap_singleton]; rw [antidiagonalTuple_zero_right k]; rw [List.map_singleton]
    exact congr_arg (fun x => [x]) Matrix.cons_zero_zero

@[simp]
/--
theorem `antidiagonalTuple_one` / 定理 `antidiagonalTuple_one`

English:
theorem antidiagonalTuple_one
  given: (n : Nat)
  statement: antidiagonalTuple 1 n = [![n]]
  proof: by
  simp_rw [antidiagonalTuple, antidiagonal, List.range_succ, List.map_append, List.map_singleton,
    Nat.sub_self, List.flatMap_append, List.flatMap_singleton, List.flatMap_map]
  conv_rhs => rw [← List.nil_append [![n]]]
  congr 1
  simp_rw [List.flatMap_eq_nil_iff, List.mem_range, List.map_eq_nil_iff]
  intro x hx
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hx
  rw [add_assoc]; rw [add_tsub_cancel_left]; rw [antidiagonalTuple_zero_succ]

中文:
定理 antidiagonalTuple_one
  条件: (n : 自然数)
  结论: antidiagonalTuple 1 n = [![n]]
  证明: by
  simp_rw [antidiagonalTuple, antidiagonal, List.range_succ, List.map_append, List.map_singleton,
    Nat.sub_self, List.flatMap_append, List.flatMap_singleton, List.flatMap_map]
  conv_rhs => rw [← List.nil_append [![n]]]
  congr 1
  simp_rw [List.flatMap_eq_nil_iff, List.mem_range, List.map_eq_nil_iff]
  intro x hx
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hx
  rw [add_assoc]; rw [add_tsub_cancel_left]; rw [antidiagonalTuple_zero_succ]

Depends on / 依赖: List.flatMap_append, List.flatMap_eq_nil_iff, List.flatMap_map, List.flatMap_singleton, List.map_append, List.map_eq_nil_iff, List.map_singleton, List.mem_range, List.nil_append, List.range_succ, Nat.exists_eq_add_of_lt, Nat.sub_self, add_assoc, add_tsub_cancel_left, antidiagonal, antidiagonalTuple, antidiagonalTuple_zero_succ, conv_rhs, exists_eq_add_of_lt, flatMap_append
-/
theorem antidiagonalTuple_one (n : Nat) : antidiagonalTuple 1 n = [![n]] := by
  simp_rw [antidiagonalTuple, antidiagonal, List.range_succ, List.map_append, List.map_singleton,
    Nat.sub_self, List.flatMap_append, List.flatMap_singleton, List.flatMap_map]
  conv_rhs => rw [← List.nil_append [![n]]]
  congr 1
  simp_rw [List.flatMap_eq_nil_iff, List.mem_range, List.map_eq_nil_iff]
  intro x hx
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hx
  rw [add_assoc]; rw [add_tsub_cancel_left]; rw [antidiagonalTuple_zero_succ]

/--
theorem `antidiagonalTuple_two` / 定理 `antidiagonalTuple_two`

English:
theorem antidiagonalTuple_two
  given: (n : Nat)
  proof: by
  rw [antidiagonalTuple]
  simp_rw [antidiagonalTuple_one, List.map_singleton]
  rw [List.map_eq_flatMap]
  rfl

中文:
定理 antidiagonalTuple_two
  条件: (n : 自然数)
  证明: by
  rw [antidiagonalTuple]
  simp_rw [antidiagonalTuple_one, List.map_singleton]
  rw [List.map_eq_flatMap]
  rfl

Depends on / 依赖: List.map_eq_flatMap, List.map_singleton, antidiagonalTuple, antidiagonalTuple_one, map_eq_flatMap, map_singleton, simp_rw
-/
theorem antidiagonalTuple_two (n : Nat) :
    antidiagonalTuple 2 n = (antidiagonal n).map fun i => ![i.1, i.2] := by
  rw [antidiagonalTuple]
  simp_rw [antidiagonalTuple_one, List.map_singleton]
  rw [List.map_eq_flatMap]
  rfl

/--
theorem `antidiagonalTuple_pairwise_pi_lex` / 定理 `antidiagonalTuple_pairwise_pi_lex`

English:
theorem antidiagonalTuple_pairwise_pi_lex

中文:
定理 antidiagonalTuple_pairwise_pi_lex
-/
theorem antidiagonalTuple_pairwise_pi_lex :
    forall k n, (antidiagonalTuple k n).Pairwise (Pi.Lex (· < ·) @fun _ => (· < ·))
  | 0, 0 => List.pairwise_singleton _ _
  | 0, _ + 1 => List.Pairwise.nil
  | k + 1, n => by
    simp_rw [antidiagonalTuple, List.pairwise_flatMap, List.pairwise_map, List.mem_map,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    simp only [mem_antidiagonal, Prod.forall]
    simp only [Fin.pi_lex_lt_cons_cons, true_and, lt_self_iff_false,
      false_or]
    refine ⟨fun _ _ _ => antidiagonalTuple_pairwise_pi_lex k _, ?_⟩
    induction n with
    | zero =>
      rw [antidiagonal_zero]
      exact List.pairwise_singleton _ _
    | succ n n_ih =>
      simp
      grind

end List.Nat

/-! ### Multisets -/


namespace Multiset.Nat

/--
Definition of `antidiagonalTuple` / `antidiagonalTuple` 的定义

English:
definition antidiagonalTuple
  signature: (k n : Nat)
  body: List.Nat.antidiagonalTuple k n

@[simp]

中文:
定义 antidiagonalTuple
  签名: (k n : 自然数)
  定义体: List.Nat.antidiagonalTuple k n

@[simp]

Depends on / 依赖: List.Nat.antidiagonalTuple, antidiagonalTuple
-/
def antidiagonalTuple (k n : Nat) : Multiset (Fin k -> Nat) :=
  List.Nat.antidiagonalTuple k n

@[simp]
/--
theorem `antidiagonalTuple_zero_zero` / 定理 `antidiagonalTuple_zero_zero`

English:
theorem antidiagonalTuple_zero_zero
  statement: antidiagonalTuple 0 0 = {![]}
  proof: rfl

@[simp]

中文:
定理 antidiagonalTuple_zero_zero
  结论: antidiagonalTuple 0 0 = {![]}
  证明: rfl

@[simp]
-/
theorem antidiagonalTuple_zero_zero : antidiagonalTuple 0 0 = {![]} :=
  rfl

@[simp]
/--
theorem `antidiagonalTuple_zero_succ` / 定理 `antidiagonalTuple_zero_succ`

English:
theorem antidiagonalTuple_zero_succ
  given: (n : Nat)
  statement: antidiagonalTuple 0 n.succ = 0
  proof: rfl

中文:
定理 antidiagonalTuple_zero_succ
  条件: (n : 自然数)
  结论: antidiagonalTuple 0 n.succ = 0
  证明: rfl
-/
theorem antidiagonalTuple_zero_succ (n : Nat) : antidiagonalTuple 0 n.succ = 0 :=
  rfl

/--
theorem `mem_antidiagonalTuple` / 定理 `mem_antidiagonalTuple`

English:
theorem mem_antidiagonalTuple
  given: {n : Nat} {k : Nat} {x : Fin k -> Nat}
  proof: List.Nat.mem_antidiagonalTuple

中文:
定理 mem_antidiagonalTuple
  条件: {n : 自然数} {k : 自然数} {x : 有限集 k -> 自然数}
  证明: List.Nat.mem_antidiagonalTuple

Depends on / 依赖: List.Nat.mem_antidiagonalTuple, mem_antidiagonalTuple
-/
theorem mem_antidiagonalTuple {n : Nat} {k : Nat} {x : Fin k -> Nat} :
    x in antidiagonalTuple k n ↔ ∑ i, x i = n :=
  List.Nat.mem_antidiagonalTuple

/--
theorem `nodup_antidiagonalTuple` / 定理 `nodup_antidiagonalTuple`

English:
theorem nodup_antidiagonalTuple
  given: (k n : Nat)
  statement: (antidiagonalTuple k n).Nodup
  proof: List.Nat.nodup_antidiagonalTuple _ _

中文:
定理 nodup_antidiagonalTuple
  条件: (k n : 自然数)
  结论: (antidiagonalTuple k n).Nodup
  证明: List.Nat.nodup_antidiagonalTuple _ _

Depends on / 依赖: List.Nat.nodup_antidiagonalTuple, nodup_antidiagonalTuple
-/
theorem nodup_antidiagonalTuple (k n : Nat) : (antidiagonalTuple k n).Nodup :=
  List.Nat.nodup_antidiagonalTuple _ _

/--
theorem `antidiagonalTuple_zero_right` / 定理 `antidiagonalTuple_zero_right`

English:
theorem antidiagonalTuple_zero_right
  given: (k : Nat)
  statement: antidiagonalTuple k 0 = {0}
  proof: congr_arg _ (List.Nat.antidiagonalTuple_zero_right k)

@[simp]

中文:
定理 antidiagonalTuple_zero_right
  条件: (k : 自然数)
  结论: antidiagonalTuple k 0 = {0}
  证明: congr_arg _ (List.Nat.antidiagonalTuple_zero_right k)

@[simp]

Depends on / 依赖: List.Nat.antidiagonalTuple_zero_right, antidiagonalTuple_zero_right, congr_arg
-/
theorem antidiagonalTuple_zero_right (k : Nat) : antidiagonalTuple k 0 = {0} :=
  congr_arg _ (List.Nat.antidiagonalTuple_zero_right k)

@[simp]
/--
theorem `antidiagonalTuple_one` / 定理 `antidiagonalTuple_one`

English:
theorem antidiagonalTuple_one
  given: (n : Nat)
  statement: antidiagonalTuple 1 n = {![n]}
  proof: congr_arg _ (List.Nat.antidiagonalTuple_one n)

中文:
定理 antidiagonalTuple_one
  条件: (n : 自然数)
  结论: antidiagonalTuple 1 n = {![n]}
  证明: congr_arg _ (List.Nat.antidiagonalTuple_one n)

Depends on / 依赖: List.Nat.antidiagonalTuple_one, antidiagonalTuple_one, congr_arg
-/
theorem antidiagonalTuple_one (n : Nat) : antidiagonalTuple 1 n = {![n]} :=
  congr_arg _ (List.Nat.antidiagonalTuple_one n)

/--
theorem `antidiagonalTuple_two` / 定理 `antidiagonalTuple_two`

English:
theorem antidiagonalTuple_two
  given: (n : Nat)
  proof: congr_arg _ (List.Nat.antidiagonalTuple_two n)

中文:
定理 antidiagonalTuple_two
  条件: (n : 自然数)
  证明: congr_arg _ (List.Nat.antidiagonalTuple_two n)

Depends on / 依赖: List.Nat.antidiagonalTuple_two, antidiagonalTuple_two, congr_arg
-/
theorem antidiagonalTuple_two (n : Nat) :
    antidiagonalTuple 2 n = (antidiagonal n).map fun i => ![i.1, i.2] :=
  congr_arg _ (List.Nat.antidiagonalTuple_two n)

end Multiset.Nat

/-! ### Finsets -/


namespace Finset.Nat

/--
Definition of `antidiagonalTuple` / `antidiagonalTuple` 的定义

English:
definition antidiagonalTuple
  signature: (k n : Nat)
  body: ⟨Multiset.Nat.antidiagonalTuple k n, Multiset.Nat.nodup_antidiagonalTuple k n⟩

@[simp]

中文:
定义 antidiagonalTuple
  签名: (k n : 自然数)
  定义体: ⟨Multiset.Nat.antidiagonalTuple k n, Multiset.Nat.nodup_antidiagonalTuple k n⟩

@[simp]

Depends on / 依赖: Multiset, Multiset.Nat.antidiagonalTuple, Multiset.Nat.nodup_antidiagonalTuple, antidiagonalTuple, nodup_antidiagonalTuple
-/
def antidiagonalTuple (k n : Nat) : Finset (Fin k -> Nat) :=
  ⟨Multiset.Nat.antidiagonalTuple k n, Multiset.Nat.nodup_antidiagonalTuple k n⟩

@[simp]
/--
theorem `antidiagonalTuple_zero_zero` / 定理 `antidiagonalTuple_zero_zero`

English:
theorem antidiagonalTuple_zero_zero
  statement: antidiagonalTuple 0 0 = {![]}
  proof: rfl

@[simp]

中文:
定理 antidiagonalTuple_zero_zero
  结论: antidiagonalTuple 0 0 = {![]}
  证明: rfl

@[simp]
-/
theorem antidiagonalTuple_zero_zero : antidiagonalTuple 0 0 = {![]} :=
  rfl

@[simp]
/--
theorem `antidiagonalTuple_zero_succ` / 定理 `antidiagonalTuple_zero_succ`

English:
theorem antidiagonalTuple_zero_succ
  given: (n : Nat)
  statement: antidiagonalTuple 0 n.succ = ∅
  proof: rfl

中文:
定理 antidiagonalTuple_zero_succ
  条件: (n : 自然数)
  结论: antidiagonalTuple 0 n.succ = ∅
  证明: rfl
-/
theorem antidiagonalTuple_zero_succ (n : Nat) : antidiagonalTuple 0 n.succ = ∅ :=
  rfl

/--
theorem `mem_antidiagonalTuple` / 定理 `mem_antidiagonalTuple`

English:
theorem mem_antidiagonalTuple
  given: {n : Nat} {k : Nat} {x : Fin k -> Nat}
  proof: List.Nat.mem_antidiagonalTuple

中文:
定理 mem_antidiagonalTuple
  条件: {n : 自然数} {k : 自然数} {x : 有限集 k -> 自然数}
  证明: List.Nat.mem_antidiagonalTuple

Depends on / 依赖: List.Nat.mem_antidiagonalTuple, mem_antidiagonalTuple
-/
theorem mem_antidiagonalTuple {n : Nat} {k : Nat} {x : Fin k -> Nat} :
    x in antidiagonalTuple k n ↔ ∑ i, x i = n :=
  List.Nat.mem_antidiagonalTuple

/--
theorem `antidiagonalTuple_zero_right` / 定理 `antidiagonalTuple_zero_right`

English:
theorem antidiagonalTuple_zero_right
  given: (k : Nat)
  statement: antidiagonalTuple k 0 = {0}
  proof: Finset.eq_of_veq (Multiset.Nat.antidiagonalTuple_zero_right k)

@[simp]

中文:
定理 antidiagonalTuple_zero_right
  条件: (k : 自然数)
  结论: antidiagonalTuple k 0 = {0}
  证明: Finset.eq_of_veq (Multiset.Nat.antidiagonalTuple_zero_right k)

@[simp]

Depends on / 依赖: Finset, Finset.eq_of_veq, Multiset, Multiset.Nat.antidiagonalTuple_zero_right, antidiagonalTuple_zero_right, eq_of_veq
-/
theorem antidiagonalTuple_zero_right (k : Nat) : antidiagonalTuple k 0 = {0} :=
  Finset.eq_of_veq (Multiset.Nat.antidiagonalTuple_zero_right k)

@[simp]
/--
theorem `antidiagonalTuple_one` / 定理 `antidiagonalTuple_one`

English:
theorem antidiagonalTuple_one
  given: (n : Nat)
  statement: antidiagonalTuple 1 n = {![n]}
  proof: Finset.eq_of_veq (Multiset.Nat.antidiagonalTuple_one n)

中文:
定理 antidiagonalTuple_one
  条件: (n : 自然数)
  结论: antidiagonalTuple 1 n = {![n]}
  证明: Finset.eq_of_veq (Multiset.Nat.antidiagonalTuple_one n)

Depends on / 依赖: Finset, Finset.eq_of_veq, Multiset, Multiset.Nat.antidiagonalTuple_one, antidiagonalTuple_one, eq_of_veq
-/
theorem antidiagonalTuple_one (n : Nat) : antidiagonalTuple 1 n = {![n]} :=
  Finset.eq_of_veq (Multiset.Nat.antidiagonalTuple_one n)

/--
theorem `antidiagonalTuple_two` / 定理 `antidiagonalTuple_two`

English:
theorem antidiagonalTuple_two
  given: (n : Nat)
  proof: Finset.eq_of_veq (Multiset.Nat.antidiagonalTuple_two n)

中文:
定理 antidiagonalTuple_two
  条件: (n : 自然数)
  证明: Finset.eq_of_veq (Multiset.Nat.antidiagonalTuple_two n)

Depends on / 依赖: Finset, Finset.eq_of_veq, Multiset, Multiset.Nat.antidiagonalTuple_two, antidiagonalTuple_two, eq_of_veq
-/
theorem antidiagonalTuple_two (n : Nat) :
    antidiagonalTuple 2 n = (antidiagonal n).map (piFinTwoEquiv fun _ => Nat).symm.toEmbedding :=
  Finset.eq_of_veq (Multiset.Nat.antidiagonalTuple_two n)

section EquivProd

/-- The disjoint union of antidiagonal tuples `Σ n, antidiagonalTuple k n` is equivalent to the
`k`-tuple `Fin k → ℕ`. This is such an equivalence, obtained by mapping `(n, x)` to `x`.

This is the tuple version of `Finset..HasAntidiagonal.sigmaAntidiagonalEquivProd`. -/
@[simps]
/--
Definition of `sigmaAntidiagonalTupleEquivTuple` / `sigmaAntidiagonalTupleEquivTuple` 的定义

English:
definition sigmaAntidiagonalTupleEquivTuple
  signature: (k : Nat)
  body: x.2
  invFun x := ⟨∑ i, x i, x, mem_antidiagonalTuple.mpr rfl⟩
  left_inv := fun ⟨_, _, h⟩ => Sigma.subtype_ext (mem_antidiagonalTuple.mp h) rfl

中文:
定义 sigmaAntidiagonalTupleEquivTuple
  签名: (k : 自然数)
  定义体: x.2
  invFun x := ⟨∑ i, x i, x, mem_antidiagonalTuple.mpr rfl⟩
  left_inv := fun ⟨_, _, h⟩ => Sigma.subtype_ext (mem_antidiagonalTuple.mp h) rfl
-/
def sigmaAntidiagonalTupleEquivTuple (k : Nat) : (Σ n, antidiagonalTuple k n) ≃ (Fin k -> Nat) where
  toFun x := x.2
  invFun x := ⟨∑ i, x i, x, mem_antidiagonalTuple.mpr rfl⟩
  left_inv := fun ⟨_, _, h⟩ => Sigma.subtype_ext (mem_antidiagonalTuple.mp h) rfl

end EquivProd

end Finset.Nat
