/-
Copyright (c) 2023 Antoine Chambert-Loir and María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández, Eric Wieser, Bhavik Mehta,
  Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
public import Mathlib.Data.Fin.Tuple.NatAntidiagonal
public import Mathlib.Data.Finset.Sym
public import Mathlib.Algebra.Group.Pi.Lemmas

/-!
# Antidiagonal of functions as finsets

This file provides the finset of functions summing to a specific value on a finset. Such finsets
should be thought of as the "antidiagonals" in the space of functions.

Precisely, for a commutative monoid `μ` with antidiagonals (see `Finset.HasAntidiagonal`),
`Finset.piAntidiag s n` is the finset of all functions `f : ι → μ` with support contained in `s` and
such that the sum of its values equals `n : μ`.

We define it recursively on `s` using `Finset.HasAntidiagonal.antidiagonal : μ → Finset (μ × μ)`.
Technically, we non-canonically identify `s` with `Fin n` where `n = s.card`, recurse on `n` using
that `(Fin (n + 1) → μ) ≃ (Fin n → μ) × μ`, and show the end result doesn't depend on our
identification. See `Finset.finAntidiag` for the details.

## Main declarations

* `Finset.piAntidiag s n`: Finset of all functions `f : ι → μ` with support contained in `s` and
  such that the sum of its values equals `n : μ`.
* `Finset.finAntidiagonal d n`: Computationally efficient special case of `Finset.piAntidiag` when
  `ι := Fin d`.

## TODO

`Finset.finAntidiagonal` is strictly more general than `Finset.Nat.antidiagonalTuple`. Deduplicate.

## See also

`Finset.finsuppAntidiag` for the `Finset (ι →₀ μ)`-valued version of `Finset.piAntidiag`.
-/

@[expose] public section

open Function

variable {ι μ μ' : Type*}

namespace Finset
section AddCommMonoid
variable [DecidableEq ι] [AddCommMonoid μ] [HasAntidiagonal μ] [DecidableEq μ] {n : μ}

/-!
### `Fin d → μ`

In this section, we define the antidiagonals in `Fin d → μ` by recursion on `d`. Note that this is
computationally efficient, although probably not as efficient as `Finset.Nat.antidiagonalTuple`.
-/

/--
Definition of `finAntidiagonal.aux` / `finAntidiagonal.aux` 的定义

English:
definition finAntidiagonal.aux
  signature: (d : Nat) (n : μ)
  body: match d with
  | 0 =>
    if h : n = 0 then
      ⟨{0}, by simp [h, Subsingleton.elim _ ![]]⟩
    else
      ⟨∅, by simp [Ne.symm h]⟩
  | d + 1 =>
    { val := (antidiagonal n).disjiUnion
        (fun ab => (aux d ab.2).1.map {
            toFun := Fin.cons (ab.1)
            inj' := Fin.cons_right_injective _ }) <| by
        intro i _ j _ hij
        simp only [Finset.disjoint_left, Finset.mem_map, Embedding.coeFn_mk]
        grind [Fin.cons_inj]
      property := fun f => by
        simp_rw [mem_disjiUnion, mem_antidiagonal, mem_map, Embedding.coeFn_mk, Prod.exists,
          (aux d _).prop, Fin.sum_univ_succ]
        constructor
        · rintro ⟨a, b, rfl, g, rfl, rfl⟩
          simp only [Fin.cons_zero, Fin.cons_succ]
        · intro hf
          exact ⟨_, _, hf, _, rfl, Fin.cons_self_tail f⟩ }

中文:
定义 finAntidiagonal.aux
  签名: (d : 自然数) (n : μ)
  定义体: match d with
  | 0 =>
    if h : n = 0 then
      ⟨{0}, by simp [h, Subsingleton.elim _ ![]]⟩
    else
      ⟨∅, by simp [Ne.symm h]⟩
  | d + 1 =>
    { val := (antidiagonal n).disjiUnion
        (fun ab => (aux d ab.2).1.map {
            toFun := Fin.cons (ab.1)
            inj' := Fin.cons_right_injective _ }) <| by
        intro i _ j _ hij
        simp only [Finset.disjoint_left, Finset.mem_map, Embedding.coeFn_mk]
        grind [Fin.cons_inj]
      property := fun f => by
        simp_rw [mem_disjiUnion, mem_antidiagonal, mem_map, Embedding.coeFn_mk, Prod.exists,
          (aux d _).prop, Fin.sum_univ_succ]
        constructor
        · rintro ⟨a, b, rfl, g, rfl, rfl⟩
          simp only [Fin.cons_zero, Fin.cons_succ]
        · intro hf
          exact ⟨_, _, hf, _, rfl, Fin.cons_self_tail f⟩ }

Depends on / 依赖: Embedding, Embedding.coeFn_mk, Fin.cons, Fin.cons_inj, Fin.cons_right_injective, Fin.su, Finset, Finset.disjoint_left, Finset.mem_map, Ne.symm, Prod.exists, Subsingleton, Subsingleton.elim, antidiagonal, coeFn_mk, cons_inj, cons_right_injective, disjiUnion, disjoint_left, mem_antidiagonal
-/
def finAntidiagonal.aux (d : Nat) (n : μ) : {s : Finset (Fin d -> μ) // forall f, f in s ↔ ∑ i, f i = n} :=
  match d with
  | 0 =>
    if h : n = 0 then
      ⟨{0}, by simp [h, Subsingleton.elim _ ![]]⟩
    else
      ⟨∅, by simp [Ne.symm h]⟩
  | d + 1 =>
    { val := (antidiagonal n).disjiUnion
        (fun ab => (aux d ab.2).1.map {
            toFun := Fin.cons (ab.1)
            inj' := Fin.cons_right_injective _ }) <| by
        intro i _ j _ hij
        simp only [Finset.disjoint_left, Finset.mem_map, Embedding.coeFn_mk]
        grind [Fin.cons_inj]
      property := fun f => by
        simp_rw [mem_disjiUnion, mem_antidiagonal, mem_map, Embedding.coeFn_mk, Prod.exists,
          (aux d _).prop, Fin.sum_univ_succ]
        constructor
        · rintro ⟨a, b, rfl, g, rfl, rfl⟩
          simp only [Fin.cons_zero, Fin.cons_succ]
        · intro hf
          exact ⟨_, _, hf, _, rfl, Fin.cons_self_tail f⟩ }

/--
Definition of `finAntidiagonal` / `finAntidiagonal` 的定义

English:
definition finAntidiagonal
  signature: (d : Nat) (n : μ)
  body: finAntidiagonal.aux d n

中文:
定义 finAntidiagonal
  签名: (d : 自然数) (n : μ)
  定义体: finAntidiagonal.aux d n

Depends on / 依赖: finAntidiagonal, finAntidiagonal.aux
-/
def finAntidiagonal (d : Nat) (n : μ) : Finset (Fin d -> μ) := finAntidiagonal.aux d n

/--
lemma `mem_finAntidiagonal` / 引理 `mem_finAntidiagonal`

English:
lemma mem_finAntidiagonal
  given: {d : Nat} {f : Fin d -> μ}
  proof: (finAntidiagonal.aux d n).prop f

中文:
引理 mem_finAntidiagonal
  条件: {d : 自然数} {f : 有限集 d -> μ}
  证明: (finAntidiagonal.aux d n).prop f
-/
@[simp] lemma mem_finAntidiagonal {d : Nat} {f : Fin d -> μ} :
    f in finAntidiagonal d n ↔ ∑ i, f i = n := (finAntidiagonal.aux d n).prop f

/-!
### `ι → μ`

In this section, we transfer the antidiagonals in `Fin s.card → μ` to antidiagonals in `ι → s` by
choosing an identification `s ≃ Fin s.card` and proving that the end result does not depend on that
choice.
-/

/--
Definition of `piAntidiag` / `piAntidiag` 的定义

English:
definition piAntidiag
  signature: (s : Finset ι) (n : μ)
  body: by
  refine (Fintype.truncEquivFinOfCardEq <| Fintype.card_coe s).lift
    (fun e => (finAntidiagonal s.card n).map ⟨fun f i => if hi : i in s then f (e ⟨i, hi⟩) else 0, ?_⟩)
    fun e₁ e₂ => ?_
  · rw [Injective]
    rintro f g hfg
    ext i
    simpa using congr_fun hfg (e.symm i)
  · ext f
    simp only [mem_map, mem_finAntidiagonal]
    refine Equiv.exists_congr ((e₁.symm.trans e₂).arrowCongr <| .refl _) fun g => ?_
    have := Fintype.sum_equiv (e₂.symm.trans e₁) _ g fun _ => rfl
    simp_all

中文:
定义 piAntidiag
  签名: (s : 有限集 ι) (n : μ)
  定义体: by
  refine (Fintype.truncEquivFinOfCardEq <| Fintype.card_coe s).lift
    (fun e => (finAntidiagonal s.card n).map ⟨fun f i => if hi : i in s then f (e ⟨i, hi⟩) else 0, ?_⟩)
    fun e₁ e₂ => ?_
  · rw [Injective]
    rintro f g hfg
    ext i
    simpa using congr_fun hfg (e.symm i)
  · ext f
    simp only [mem_map, mem_finAntidiagonal]
    refine Equiv.exists_congr ((e₁.symm.trans e₂).arrowCongr <| .refl _) fun g => ?_
    have := Fintype.sum_equiv (e₂.symm.trans e₁) _ g fun _ => rfl
    simp_all

Depends on / 依赖: Equiv.exists_congr, Fintype, Fintype.card_coe, Fintype.sum_equiv, Fintype.truncEquivFinOfCardEq, Injective, arrowCongr, card_coe, congr_fun, e.symm, exists_congr, finAntidiagonal, mem_finAntidiagonal, mem_map, s.card, sum_equiv, symm.trans, truncEquivFinOfCardEq
-/
def piAntidiag (s : Finset ι) (n : μ) : Finset (ι -> μ) := by
  refine (Fintype.truncEquivFinOfCardEq <| Fintype.card_coe s).lift
    (fun e => (finAntidiagonal s.card n).map ⟨fun f i => if hi : i in s then f (e ⟨i, hi⟩) else 0, ?_⟩)
    fun e₁ e₂ => ?_
  · rw [Injective]
    rintro f g hfg
    ext i
    simpa using congr_fun hfg (e.symm i)
  · ext f
    simp only [mem_map, mem_finAntidiagonal]
    refine Equiv.exists_congr ((e₁.symm.trans e₂).arrowCongr <| .refl _) fun g => ?_
    have := Fintype.sum_equiv (e₂.symm.trans e₁) _ g fun _ => rfl
    simp_all

variable {s : Finset ι} {n : μ} {f : ι -> μ}

/--
lemma `mem_piAntidiag` / 引理 `mem_piAntidiag`

English:
lemma mem_piAntidiag
  statement: f in piAntidiag s n ↔ s.sum f = n ∧ forall i, f i != 0 -> i in s
  proof: by
  rw [piAntidiag]
  induction Fintype.truncEquivFinOfCardEq (Fintype.card_coe s) using Trunc.ind with | _ e
  simp only [Trunc.lift_mk, mem_map, mem_finAntidiagonal, Embedding.coeFn_mk]
  constructor
  · rintro ⟨f, ⟨hf, rfl⟩, rfl⟩
    rw [sum_dite_of_true fun _ => id]
    exact ⟨Fintype.sum_equiv e _ _ (by simp), by simp +contextual⟩
  · rintro ⟨rfl, hf⟩
    refine ⟨f ∘ (↑) ∘ e.symm, ?_, by grind⟩
    rw [← sum_attach s]
    exact Fintype.sum_equiv e.symm _ _ (by simp)

中文:
引理 mem_piAntidiag
  结论: f in piAntidiag s n ↔ s.求和 f = n ∧ 对任意 i, f i != 0 -> i in s
  证明: by
  rw [piAntidiag]
  induction Fintype.truncEquivFinOfCardEq (Fintype.card_coe s) using Trunc.ind with | _ e
  simp only [Trunc.lift_mk, mem_map, mem_finAntidiagonal, Embedding.coeFn_mk]
  constructor
  · rintro ⟨f, ⟨hf, rfl⟩, rfl⟩
    rw [sum_dite_of_true fun _ => id]
    exact ⟨Fintype.sum_equiv e _ _ (by simp), by simp +contextual⟩
  · rintro ⟨rfl, hf⟩
    refine ⟨f ∘ (↑) ∘ e.symm, ?_, by grind⟩
    rw [← sum_attach s]
    exact Fintype.sum_equiv e.symm _ _ (by simp)
-/
@[simp] lemma mem_piAntidiag : f in piAntidiag s n ↔ s.sum f = n ∧ forall i, f i != 0 -> i in s := by
  rw [piAntidiag]
  induction Fintype.truncEquivFinOfCardEq (Fintype.card_coe s) using Trunc.ind with | _ e
  simp only [Trunc.lift_mk, mem_map, mem_finAntidiagonal, Embedding.coeFn_mk]
  constructor
  · rintro ⟨f, ⟨hf, rfl⟩, rfl⟩
    rw [sum_dite_of_true fun _ => id]
    exact ⟨Fintype.sum_equiv e _ _ (by simp), by simp +contextual⟩
  · rintro ⟨rfl, hf⟩
    refine ⟨f ∘ (↑) ∘ e.symm, ?_, by grind⟩
    rw [← sum_attach s]
    exact Fintype.sum_equiv e.symm _ _ (by simp)

/--
lemma `piAntidiag_empty_zero` / 引理 `piAntidiag_empty_zero`

English:
lemma piAntidiag_empty_zero
  statement: piAntidiag (∅ : Finset ι) (0 : μ) = {0}
  proof: by
  ext; simp [funext_iff]

中文:
引理 piAntidiag_empty_zero
  结论: piAntidiag (∅ : 有限集 ι) (0 : μ) = {0}
  证明: by
  ext; simp [funext_iff]
-/
@[simp] lemma piAntidiag_empty_zero : piAntidiag (∅ : Finset ι) (0 : μ) = {0} := by
  ext; simp [funext_iff]

/--
lemma `piAntidiag_empty_of_ne_zero` / 引理 `piAntidiag_empty_of_ne_zero`

English:
lemma piAntidiag_empty_of_ne_zero
  given: (hn : n != 0)
  statement: piAntidiag (∅ : Finset ι) n = ∅
  proof: eq_empty_of_forall_notMem (by simp [hn.symm])

中文:
引理 piAntidiag_empty_of_ne_zero
  条件: (hn : n != 0)
  结论: piAntidiag (∅ : 有限集 ι) n = ∅
  证明: eq_empty_of_forall_notMem (by simp [hn.symm])
-/
@[simp] lemma piAntidiag_empty_of_ne_zero (hn : n != 0) : piAntidiag (∅ : Finset ι) n = ∅ :=
  eq_empty_of_forall_notMem (by simp [hn.symm])

/--
lemma `piAntidiag_empty` / 引理 `piAntidiag_empty`

English:
lemma piAntidiag_empty
  given: (n : μ)
  statement: piAntidiag (∅ : Finset ι) n = if n = 0 then {0} else ∅
  proof: by
  split_ifs with hn <;> simp [*]

中文:
引理 piAntidiag_empty
  条件: (n : μ)
  结论: piAntidiag (∅ : 有限集 ι) n = if n = 0 then {0} else ∅
  证明: by
  split_ifs with hn <;> simp [*]

Depends on / 依赖: split_ifs
-/
lemma piAntidiag_empty (n : μ) : piAntidiag (∅ : Finset ι) n = if n = 0 then {0} else ∅ := by
  split_ifs with hn <;> simp [*]

/--
lemma `finsetCongr_piAntidiag_eq_antidiag` / 引理 `finsetCongr_piAntidiag_eq_antidiag`

English:
lemma finsetCongr_piAntidiag_eq_antidiag
  given: (n : μ)
  proof: by
  ext ⟨x₁, x₂⟩
  simp_rw [Equiv.finsetCongr_apply, mem_map, Equiv.toEmbedding, Function.Embedding.coeFn_mk,
    ← Equiv.eq_symm_apply]
  simp [add_comm]

中文:
引理 finsetCongr_piAntidiag_eq_antidiag
  条件: (n : μ)
  证明: by
  ext ⟨x₁, x₂⟩
  simp_rw [Equiv.finsetCongr_apply, mem_map, Equiv.toEmbedding, Function.Embedding.coeFn_mk,
    ← Equiv.eq_symm_apply]
  simp [add_comm]

Depends on / 依赖: Embedding, Equiv.eq_symm_apply, Equiv.finsetCongr_apply, Equiv.toEmbedding, Function, Function.Embedding.coeFn_mk, add_comm, coeFn_mk, eq_symm_apply, finsetCongr_apply, mem_map, simp_rw, toEmbedding
-/
lemma finsetCongr_piAntidiag_eq_antidiag (n : μ) :
    Equiv.finsetCongr (Equiv.boolArrowEquivProd _) (piAntidiag univ n) = antidiagonal n := by
  ext ⟨x₁, x₂⟩
  simp_rw [Equiv.finsetCongr_apply, mem_map, Equiv.toEmbedding, Function.Embedding.coeFn_mk,
    ← Equiv.eq_symm_apply]
  simp [add_comm]

end AddCommMonoid

section AddCancelCommMonoid
variable [DecidableEq ι] [AddCancelCommMonoid μ] [HasAntidiagonal μ] [DecidableEq μ] {i : ι}
  {s : Finset ι}

/--
lemma `pairwiseDisjoint_piAntidiag_map_addRightEmbedding` / 引理 `pairwiseDisjoint_piAntidiag_map_addRightEmbedding`

English:
lemma pairwiseDisjoint_piAntidiag_map_addRightEmbedding
  given: (hi : i ∉ s) (n : μ)
  proof: by
  rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd
  simp only [ne_eq, HasAntidiagonal.antidiagonal_congr' hab hcd, disjoint_left, mem_map,
    mem_piAntidiag, addRightEmbedding_apply, not_exists, not_and, and_imp, forall_exists_index]
  rintro hfg _ f rfl - rfl g rfl - hgf
exact hfg by simpa [sum_add_distrib, hi] using congr_arg (∑ j in s, · j) hgf.symm

中文:
引理 pairwiseDisjoint_piAntidiag_map_addRightEmbedding
  条件: (hi : i ∉ s) (n : μ)
  证明: by
  rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd
  simp only [ne_eq, HasAntidiagonal.antidiagonal_congr' hab hcd, disjoint_left, mem_map,
    mem_piAntidiag, addRightEmbedding_apply, not_exists, not_and, and_imp, forall_exists_index]
  rintro hfg _ f rfl - rfl g rfl - hgf
exact hfg by simpa [sum_add_distrib, hi] using congr_arg (∑ j in s, · j) hgf.symm

Depends on / 依赖: HasAntidiagonal, HasAntidiagonal.antidiagonal_congr, addRightEmbedding_apply, and_imp, antidiagonal_congr, congr_arg, disjoint_left, forall_exists_index, hgf.symm, mem_map, mem_piAntidiag, ne_eq, not_and, not_exists, sum_add_distrib
-/
lemma pairwiseDisjoint_piAntidiag_map_addRightEmbedding (hi : i ∉ s) (n : μ) :
    (antidiagonal n : Set (μ × μ)).PairwiseDisjoint fun p =>
      map (addRightEmbedding fun j => if j = i then p.1 else 0) (s.piAntidiag p.2) := by
  rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd
  simp only [ne_eq, HasAntidiagonal.antidiagonal_congr' hab hcd, disjoint_left, mem_map,
    mem_piAntidiag, addRightEmbedding_apply, not_exists, not_and, and_imp, forall_exists_index]
  rintro hfg _ f rfl - rfl g rfl - hgf
exact hfg by simpa [sum_add_distrib, hi] using congr_arg (∑ j in s, · j) hgf.symm

/--
lemma `piAntidiag_cons` / 引理 `piAntidiag_cons`

English:
lemma piAntidiag_cons
  given: (hi : i ∉ s) (n : μ)
  proof: by
  ext f
  simp only [mem_piAntidiag, sum_cons, ne_eq, mem_cons, mem_disjiUnion, mem_antidiagonal, mem_map,
    Prod.exists]
  constructor
  · rintro ⟨hn, hf⟩
    refine ⟨_, _, hn, update f i 0, ⟨sum_update_of_notMem hi _ _, fun j => ?_⟩, by aesop⟩
    grind
  · rintro ⟨a, _, hn, g, ⟨rfl, hg⟩, rfl⟩
    have := hg i
    aesop (add simp [sum_add_distrib])

中文:
引理 piAntidiag_cons
  条件: (hi : i ∉ s) (n : μ)
  证明: by
  ext f
  simp only [mem_piAntidiag, sum_cons, ne_eq, mem_cons, mem_disjiUnion, mem_antidiagonal, mem_map,
    Prod.exists]
  constructor
  · rintro ⟨hn, hf⟩
    refine ⟨_, _, hn, update f i 0, ⟨sum_update_of_notMem hi _ _, fun j => ?_⟩, by aesop⟩
    grind
  · rintro ⟨a, _, hn, g, ⟨rfl, hg⟩, rfl⟩
    have := hg i
    aesop (add simp [sum_add_distrib])

Depends on / 依赖: Prod.exists, mem_antidiagonal, mem_cons, mem_disjiUnion, mem_map, mem_piAntidiag, ne_eq, sum_add_distrib, sum_cons, sum_update_of_notMem, update
-/
lemma piAntidiag_cons (hi : i ∉ s) (n : μ) :
    piAntidiag (cons i s hi) n = (antidiagonal n).disjiUnion (fun p : μ × μ =>
      (piAntidiag s p.snd).map (addRightEmbedding fun t => if t = i then p.fst else 0))
        (pairwiseDisjoint_piAntidiag_map_addRightEmbedding hi _) := by
  ext f
  simp only [mem_piAntidiag, sum_cons, ne_eq, mem_cons, mem_disjiUnion, mem_antidiagonal, mem_map,
    Prod.exists]
  constructor
  · rintro ⟨hn, hf⟩
    refine ⟨_, _, hn, update f i 0, ⟨sum_update_of_notMem hi _ _, fun j => ?_⟩, by aesop⟩
    grind
  · rintro ⟨a, _, hn, g, ⟨rfl, hg⟩, rfl⟩
    have := hg i
    aesop (add simp [sum_add_distrib])

/--
lemma `piAntidiag_insert` / 引理 `piAntidiag_insert`

English:
lemma piAntidiag_insert
  given: [DecidableEq (ι -> μ)] (hi : i ∉ s) (n : μ)
  proof: by
  simpa [map_eq_image, addRightEmbedding] using! piAntidiag_cons hi n

中文:
引理 piAntidiag_insert
  条件: [DecidableEq (ι -> μ)] (hi : i ∉ s) (n : μ)
  证明: by
  simpa [map_eq_image, addRightEmbedding] using! piAntidiag_cons hi n

Depends on / 依赖: addRightEmbedding, map_eq_image, piAntidiag_cons
-/
lemma piAntidiag_insert [DecidableEq (ι -> μ)] (hi : i ∉ s) (n : μ) :
    piAntidiag (insert i s) n = (antidiagonal n).biUnion fun p : μ × μ => (piAntidiag s p.snd).image
      (fun f j => f j + if j = i then p.fst else 0) := by
  simpa [map_eq_image, addRightEmbedding] using! piAntidiag_cons hi n

end AddCancelCommMonoid

section CanonicallyOrderedAddCommMonoid
variable [DecidableEq ι] [AddCommMonoid μ] [PartialOrder μ]
  [CanonicallyOrderedAdd μ] [HasAntidiagonal μ] [DecidableEq μ]

/--
lemma `piAntidiag_zero` / 引理 `piAntidiag_zero`

English:
lemma piAntidiag_zero
  given: (s : Finset ι)
  statement: piAntidiag s (0 : μ) = {0}
  proof: by
  ext; simp [funext_iff, not_imp_comm, ← forall_and]

中文:
引理 piAntidiag_zero
  条件: (s : 有限集 ι)
  结论: piAntidiag s (0 : μ) = {0}
  证明: by
  ext; simp [funext_iff, not_imp_comm, ← forall_and]
-/
@[simp] lemma piAntidiag_zero (s : Finset ι) : piAntidiag s (0 : μ) = {0} := by
  ext; simp [funext_iff, not_imp_comm, ← forall_and]

end CanonicallyOrderedAddCommMonoid

section Nat
variable [DecidableEq ι]

open Pointwise

/--
lemma `piAntidiag_univ_fin_eq_antidiagonalTuple` / 引理 `piAntidiag_univ_fin_eq_antidiagonalTuple`

English:
lemma piAntidiag_univ_fin_eq_antidiagonalTuple
  given: (n k : Nat)
  proof: by
  ext; simp [Nat.mem_antidiagonalTuple]

中文:
引理 piAntidiag_univ_fin_eq_antidiagonalTuple
  条件: (n k : 自然数)
  证明: by
  ext; simp [Nat.mem_antidiagonalTuple]

Depends on / 依赖: Nat.mem_antidiagonalTuple, mem_antidiagonalTuple
-/
lemma piAntidiag_univ_fin_eq_antidiagonalTuple (n k : Nat) :
    piAntidiag univ n = Nat.antidiagonalTuple k n := by
  ext; simp [Nat.mem_antidiagonalTuple]

/--
lemma `nsmul_piAntidiag` / 引理 `nsmul_piAntidiag`

English:
lemma nsmul_piAntidiag
  given: [DecidableEq (ι -> Nat)] (s : Finset ι) (m : Nat) {n : Nat} (hn : n != 0)
  proof: by
  ext f
  refine mem_smul_finset.trans ?_
  simp only [mem_filter, mem_piAntidiag, and_assoc]
  constructor
  · rintro ⟨f, rfl, hf, rfl⟩
    simpa [← mul_sum, hn] using hf
  rintro ⟨hfsum, hfsup, hfdvd⟩
  have (i : _) : n ∣ f i := by
    by_cases hi : i in s
    · exact hfdvd _ hi
    · rw [not_imp_comm.1 (hfsup _) hi]
      exact dvd_zero _
  refine ⟨fun i => f i / n, ?_⟩
  simp [funext_iff, Nat.mul_div_cancel', ← Nat.sum_div, *]
  grind

中文:
引理 nsmul_piAntidiag
  条件: [DecidableEq (ι -> 自然数)] (s : 有限集 ι) (m : 自然数) {n : 自然数} (hn : n != 0)
  证明: by
  ext f
  refine mem_smul_finset.trans ?_
  simp only [mem_filter, mem_piAntidiag, and_assoc]
  constructor
  · rintro ⟨f, rfl, hf, rfl⟩
    simpa [← mul_sum, hn] using hf
  rintro ⟨hfsum, hfsup, hfdvd⟩
  have (i : _) : n ∣ f i := by
    by_cases hi : i in s
    · exact hfdvd _ hi
    · rw [not_imp_comm.1 (hfsup _) hi]
      exact dvd_zero _
  refine ⟨fun i => f i / n, ?_⟩
  simp [funext_iff, Nat.mul_div_cancel', ← Nat.sum_div, *]
  grind

Depends on / 依赖: Nat.mul_div_cancel, Nat.sum_div, and_assoc, dvd_zero, funext_iff, mem_filter, mem_piAntidiag, mem_smul_finset, mem_smul_finset.trans, mul_div_cancel, mul_sum, not_imp_comm, sum_div
-/
lemma nsmul_piAntidiag [DecidableEq (ι -> Nat)] (s : Finset ι) (m : Nat) {n : Nat} (hn : n != 0) :
    n • piAntidiag s m = {f in piAntidiag s (n * m) | forall i in s, n ∣ f i} := by
  ext f
  refine mem_smul_finset.trans ?_
  simp only [mem_filter, mem_piAntidiag, and_assoc]
  constructor
  · rintro ⟨f, rfl, hf, rfl⟩
    simpa [← mul_sum, hn] using hf
  rintro ⟨hfsum, hfsup, hfdvd⟩
  have (i : _) : n ∣ f i := by
    by_cases hi : i in s
    · exact hfdvd _ hi
    · rw [not_imp_comm.1 (hfsup _) hi]
      exact dvd_zero _
  refine ⟨fun i => f i / n, ?_⟩
  simp [funext_iff, Nat.mul_div_cancel', ← Nat.sum_div, *]
  grind

/--
lemma `map_nsmul_piAntidiag` / 引理 `map_nsmul_piAntidiag`

English:
lemma map_nsmul_piAntidiag
  given: (s : Finset ι) (m : Nat) {n : Nat} (hn : n != 0)
  proof: by
  classical rw [map_eq_image]; exact nsmul_piAntidiag _ _ hn

中文:
引理 map_nsmul_piAntidiag
  条件: (s : 有限集 ι) (m : 自然数) {n : 自然数} (hn : n != 0)
  证明: by
  classical rw [map_eq_image]; exact nsmul_piAntidiag _ _ hn

Depends on / 依赖: classical, map_eq_image, nsmul_piAntidiag
-/
lemma map_nsmul_piAntidiag (s : Finset ι) (m : Nat) {n : Nat} (hn : n != 0) :
    (piAntidiag s m).map ⟨(n • ·), nsmul_right_injective hn⟩ =
        {f in piAntidiag s (n * m) | forall i in s, n ∣ f i} := by
  classical rw [map_eq_image]; exact nsmul_piAntidiag _ _ hn

/--
lemma `nsmul_piAntidiag_univ` / 引理 `nsmul_piAntidiag_univ`

English:
lemma nsmul_piAntidiag_univ
  given: [Fintype ι] (m : Nat) {n : Nat} (hn : n != 0)
  proof: by
  simpa using nsmul_piAntidiag (univ : Finset ι) m hn

中文:
引理 nsmul_piAntidiag_univ
  条件: [有限类型 ι] (m : 自然数) {n : 自然数} (hn : n != 0)
  证明: by
  simpa using nsmul_piAntidiag (univ : Finset ι) m hn

Depends on / 依赖: Finset, nsmul_piAntidiag
-/
lemma nsmul_piAntidiag_univ [Fintype ι] (m : Nat) {n : Nat} (hn : n != 0) :
    n • piAntidiag univ m = {f in piAntidiag (univ : Finset ι) (n * m) | forall i, n ∣ f i} := by
  simpa using nsmul_piAntidiag (univ : Finset ι) m hn

/--
lemma `map_nsmul_piAntidiag_univ` / 引理 `map_nsmul_piAntidiag_univ`

English:
lemma map_nsmul_piAntidiag_univ
  given: [Fintype ι] (m : Nat) {n : Nat} (hn : n != 0)
  proof: by
  simpa using map_nsmul_piAntidiag (univ : Finset ι) m hn

中文:
引理 map_nsmul_piAntidiag_univ
  条件: [有限类型 ι] (m : 自然数) {n : 自然数} (hn : n != 0)
  证明: by
  simpa using map_nsmul_piAntidiag (univ : Finset ι) m hn

Depends on / 依赖: Finset, map_nsmul_piAntidiag
-/
lemma map_nsmul_piAntidiag_univ [Fintype ι] (m : Nat) {n : Nat} (hn : n != 0) :
    (piAntidiag (univ : Finset ι) m).map ⟨(n • ·), nsmul_right_injective hn⟩ =
      {f in piAntidiag (univ : Finset ι) (n * m) | forall i, n ∣ f i} := by
  simpa using map_nsmul_piAntidiag (univ : Finset ι) m hn

end Nat

/--
lemma `map_sym_eq_piAntidiag` / 引理 `map_sym_eq_piAntidiag`

English:
lemma map_sym_eq_piAntidiag
  given: [DecidableEq ι] (s : Finset ι) (n : Nat)
  proof: by
  ext f
  simp only [Sym.val_eq_coe, mem_map, mem_sym_iff, Embedding.coeFn_mk, funext_iff, Sym.exists,
    Sym.mem_mk, Sym.coe_mk, exists_and_left, exists_prop, mem_piAntidiag, ne_eq]
  constructor
  · rintro ⟨m, hm, rfl, hf⟩
    simpa [← hf, Multiset.sum_count_eq_card hm]
  · rintro ⟨rfl, hf⟩
    refine ⟨∑ a in s, f a • {a}, ?_, ?_⟩
    · simp +contextual
    · simpa [Multiset.count_sum', Multiset.count_singleton, not_imp_comm, eq_comm (a := 0)] using hf

中文:
引理 map_sym_eq_piAntidiag
  条件: [DecidableEq ι] (s : 有限集 ι) (n : 自然数)
  证明: by
  ext f
  simp only [Sym.val_eq_coe, mem_map, mem_sym_iff, Embedding.coeFn_mk, funext_iff, Sym.exists,
    Sym.mem_mk, Sym.coe_mk, exists_and_left, exists_prop, mem_piAntidiag, ne_eq]
  constructor
  · rintro ⟨m, hm, rfl, hf⟩
    simpa [← hf, Multiset.sum_count_eq_card hm]
  · rintro ⟨rfl, hf⟩
    refine ⟨∑ a in s, f a • {a}, ?_, ?_⟩
    · simp +contextual
    · simpa [Multiset.count_sum', Multiset.count_singleton, not_imp_comm, eq_comm (a := 0)] using hf

Depends on / 依赖: Embedding, Embedding.coeFn_mk, Multiset, Multiset.count_singleton, Multiset.count_sum, Multiset.sum_count_eq_card, Sym.coe_mk, Sym.exists, Sym.mem_mk, Sym.val_eq_coe, coeFn_mk, coe_mk, contextual, count_singleton, count_sum, eq_comm, exists_and_left, exists_prop, funext_iff, mem_map
-/
lemma map_sym_eq_piAntidiag [DecidableEq ι] (s : Finset ι) (n : Nat) :
    (s.sym n).map ⟨fun m a => m.1.count a, Multiset.count_injective.comp Sym.coe_injective⟩ =
      piAntidiag s n := by
  ext f
  simp only [Sym.val_eq_coe, mem_map, mem_sym_iff, Embedding.coeFn_mk, funext_iff, Sym.exists,
    Sym.mem_mk, Sym.coe_mk, exists_and_left, exists_prop, mem_piAntidiag, ne_eq]
  constructor
  · rintro ⟨m, hm, rfl, hf⟩
    simpa [← hf, Multiset.sum_count_eq_card hm]
  · rintro ⟨rfl, hf⟩
    refine ⟨∑ a in s, f a • {a}, ?_, ?_⟩
    · simp +contextual
    · simpa [Multiset.count_sum', Multiset.count_singleton, not_imp_comm, eq_comm (a := 0)] using hf

end Finset
