/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl, Sander Dahmen, Kim Morrison
-/
module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.Data.Set.Card

/-!
# Dimension of modules and vector spaces

## Main definitions

* The rank of a module is defined as `Module.rank : Cardinal`.
  This is defined as the supremum of the cardinalities of linearly independent subsets.

## Main statements

* `LinearMap.rank_le_of_injective`: the source of an injective linear map has dimension
  at most that of the target.
* `LinearMap.rank_le_of_surjective`: the target of a surjective linear map has dimension
  at most that of that source.

## Implementation notes

Many theorems in this file are not universe-generic when they relate dimensions
in different universes. They should be as general as they can be without
inserting `lift`s. The types `M`, `M'`, ... all live in different universes,
and `M₁`, `M₂`, ... all live in the same universe.
-/

@[expose] public section


noncomputable section

universe w w' u u' v v'

variable {R : Type u} {R' : Type u'} {M M₁ : Type v} {M' : Type v'}

open Cardinal Submodule Function Set

section Module

section

variable [Semiring R] [AddCommMonoid M] [Module R M]
variable (R M)

/-- The rank of a module, defined as a term of type `Cardinal`.

We define this as the supremum of the cardinalities of linearly independent subsets.
The supremum may not be attained, see https://mathoverflow.net/a/263053.

For a free module over any ring satisfying the strong rank condition
(e.g. left-Noetherian rings, commutative rings, and in particular division rings and fields),
this is the same as the dimension of the space (i.e. the cardinality of any basis).

In particular this agrees with the usual notion of the dimension of a vector space.

See also `Module.finrank` for a `ℕ`-valued function which returns the correct value
for a finite-dimensional vector space (but 0 for an infinite-dimensional vector space).
-/
@[stacks 09G3 "first part"]
protected irreducible_def Module.rank : Cardinal :=
  ⨆ ι : { s : Set M // LinearIndepOn R id s }, (#ι.1)

/--
theorem `rank_le_card` / 定理 `rank_le_card`

English:
theorem rank_le_card
  statement: Module.rank R M <= #M
  proof: (Module.rank_def _ _).trans_le (ciSup_le' fun _ => mk_set_le _)

中文:
定理 rank_le_card
  结论: 模.rank R M <= #M
  证明: (Module.rank_def _ _).trans_le (ciSup_le' fun _ => mk_set_le _)

Depends on / 依赖: Module, Module.rank_def, ciSup_le, mk_set_le, rank_def, trans_le
-/
theorem rank_le_card : Module.rank R M <= #M :=
  (Module.rank_def _ _).trans_le (ciSup_le' fun _ => mk_set_le _)

/--
Instance `nonempty_linearIndependent_set` / 实例 `nonempty_linearIndependent_set`

English:
instance nonempty_linearIndependent_set
  signature: : Nonempty {s : Set M // LinearIndepOn R id s}
  body: ⟨⟨∅, linearIndepOn_empty _ _⟩⟩

中文:
实例 nonempty_linearIndependent_set
  签名: : 非空 {s : 集合 M // LinearIndepOn R id s}
  定义体: ⟨⟨∅, linearIndepOn_empty _ _⟩⟩

Depends on / 依赖: linearIndepOn_empty
-/
instance nonempty_linearIndependent_set : Nonempty {s : Set M // LinearIndepOn R id s} :=
  ⟨⟨∅, linearIndepOn_empty _ _⟩⟩

end

namespace LinearIndependent
variable [Semiring R] [AddCommMonoid M] [Module R M]

variable [Nontrivial R]

/--
theorem `cardinal_lift_le_rank` / 定理 `cardinal_lift_le_rank`

English:
theorem cardinal_lift_le_rank
  statement: {ι : Type w} {v : ι -> M}
  proof: by
  rw [Module.rank]
  refine le_trans ?_ (lift_le.mpr <| le_ciSup bddAbove_of_small ⟨_, hv.linearIndepOn_id⟩)
  exact lift_mk_le'.mpr ⟨(Equiv.ofInjective _ hv.injective).toEmbedding⟩

中文:
定理 cardinal_lift_le_rank
  结论: {ι : 类型 w} {v : ι -> M}
  证明: by
  rw [Module.rank]
  refine le_trans ?_ (lift_le.mpr <| le_ciSup bddAbove_of_small ⟨_, hv.linearIndepOn_id⟩)
  exact lift_mk_le'.mpr ⟨(Equiv.ofInjective _ hv.injective).toEmbedding⟩

Depends on / 依赖: Equiv.ofInjective, Module, Module.rank, bddAbove_of_small, hv.injective, hv.linearIndepOn_id, injective, le_ciSup, le_trans, lift_le, lift_le.mpr, lift_mk_le, linearIndepOn_id, ofInjective, toEmbedding
-/
theorem cardinal_lift_le_rank {ι : Type w} {v : ι -> M}
    (hv : LinearIndependent R v) :
    Cardinal.lift.{v} #ι <= Cardinal.lift.{w} (Module.rank R M) := by
  rw [Module.rank]
  refine le_trans ?_ (lift_le.mpr <| le_ciSup bddAbove_of_small ⟨_, hv.linearIndepOn_id⟩)
  exact lift_mk_le'.mpr ⟨(Equiv.ofInjective _ hv.injective).toEmbedding⟩

/--
lemma `aleph0_le_rank` / 引理 `aleph0_le_rank`

English:
lemma aleph0_le_rank
  statement: {ι : Type w} [Infinite ι] {v : ι -> M}
  proof: aleph0_le_lift.mp (aleph0_le_lift.mpr <| aleph0_le_mk ι).trans hv.cardinal_lift_le_rank

中文:
引理 aleph0_le_rank
  结论: {ι : 类型 w} [无限 ι] {v : ι -> M}
  证明: aleph0_le_lift.mp (aleph0_le_lift.mpr <| aleph0_le_mk ι).trans hv.cardinal_lift_le_rank

Depends on / 依赖: aleph0_le_lift, aleph0_le_lift.mp, aleph0_le_lift.mpr, aleph0_le_mk, cardinal_lift_le_rank, hv.cardinal_lift_le_rank
-/
lemma aleph0_le_rank {ι : Type w} [Infinite ι] {v : ι -> M}
    (hv : LinearIndependent R v) : ℵ₀ <= Module.rank R M :=
aleph0_le_lift.mp (aleph0_le_lift.mpr <| aleph0_le_mk ι).trans hv.cardinal_lift_le_rank

/--
theorem `cardinal_le_rank` / 定理 `cardinal_le_rank`

English:
theorem cardinal_le_rank
  statement: {ι : Type v} {v : ι -> M}
  proof: by
  simpa using hv.cardinal_lift_le_rank

中文:
定理 cardinal_le_rank
  结论: {ι : 类型v} {v : ι -> M}
  证明: by
  simpa using hv.cardinal_lift_le_rank

Depends on / 依赖: cardinal_lift_le_rank, hv.cardinal_lift_le_rank
-/
theorem cardinal_le_rank {ι : Type v} {v : ι -> M}
    (hv : LinearIndependent R v) : #ι <= Module.rank R M := by
  simpa using hv.cardinal_lift_le_rank

/--
theorem `cardinal_le_rank'` / 定理 `cardinal_le_rank'`

English:
theorem cardinal_le_rank'
  statement: {s : Set M}
  proof: hs.cardinal_le_rank

中文:
定理 cardinal_le_rank'
  结论: {s : 集合 M}
  证明: hs.cardinal_le_rank

Depends on / 依赖: cardinal_le_rank, hs.cardinal_le_rank
-/
theorem cardinal_le_rank' {s : Set M}
    (hs : LinearIndependent R (fun x => x : s -> M)) : #s <= Module.rank R M :=
  hs.cardinal_le_rank

/--
theorem `_root_.LinearIndepOn.encard_le_toENat_rank` / 定理 `_root_.LinearIndepOn.encard_le_toENat_rank`

English:
theorem _root_.LinearIndepOn.encard_le_toENat_rank
  statement: {ι : Type*} {v : ι -> M} {s : Set ι}
  proof: by
  simpa using OrderHom.mono (β := Nat∞) Cardinal.toENat hs.linearIndependent.cardinal_lift_le_rank

中文:
定理 _root_.LinearIndepOn.encard_le_toE自然数_rank
  结论: {ι : 类型} {v : ι -> M} {s : 集合 ι}
  证明: by
  simpa using OrderHom.mono (β := Nat∞) Cardinal.toENat hs.linearIndependent.cardinal_lift_le_rank

Depends on / 依赖: Cardinal, Cardinal.toENat, OrderHom, OrderHom.mono, cardinal_lift_le_rank, hs.linearIndependent.cardinal_lift_le_rank, linearIndependent, toENat
-/
theorem _root_.LinearIndepOn.encard_le_toENat_rank {ι : Type*} {v : ι -> M} {s : Set ι}
    (hs : LinearIndepOn R v s) : s.encard <= (Module.rank R M).toENat := by
  simpa using OrderHom.mono (β := Nat∞) Cardinal.toENat hs.linearIndependent.cardinal_lift_le_rank

end LinearIndependent

namespace Module

variable [Semiring R] [AddCommMonoid M] [Module R M]

/--
theorem `exists_set_linearIndependent_of_lt_lift_rank` / 定理 `exists_set_linearIndependent_of_lt_lift_rank`

English:
theorem exists_set_linearIndependent_of_lt_lift_rank
  statement: {c : Cardinal.{w}}
  proof: by
  rcases Cardinal.lt_lift_iff.mp h with ⟨c', hc', hcc'⟩
  rcases exists_lt_of_lt_ciSup (by simpa [← hcc', Module.rank_def] using h) with ⟨⟨s, hs⟩, h⟩
  rcases Cardinal.le_mk_iff_exists_subset.mp h.le with ⟨t, hst, ht⟩
  exact ⟨t, by simp [ht, hcc'], hs.mono hst⟩

中文:
定理 存在_set_linearIndependent_of_lt_lift_rank
  结论: {c : 基数.{w}}
  证明: by
  rcases Cardinal.lt_lift_iff.mp h with ⟨c', hc', hcc'⟩
  rcases exists_lt_of_lt_ciSup (by simpa [← hcc', Module.rank_def] using h) with ⟨⟨s, hs⟩, h⟩
  rcases Cardinal.le_mk_iff_exists_subset.mp h.le with ⟨t, hst, ht⟩
  exact ⟨t, by simp [ht, hcc'], hs.mono hst⟩

Depends on / 依赖: Cardinal, Cardinal.le_mk_iff_exists_subset.mp, Cardinal.lt_lift_iff.mp, Module, Module.rank_def, exists_lt_of_lt_ciSup, h.le, hs.mono, le_mk_iff_exists_subset, lt_lift_iff, rank_def
-/
theorem exists_set_linearIndependent_of_lt_lift_rank {c : Cardinal.{w}}
    (h : Cardinal.lift.{v} c < Cardinal.lift.{w} (Module.rank R M)) :
    exists s : Set M, Cardinal.lift.{w} #s = Cardinal.lift.{v} c ∧ LinearIndepOn R id s := by
  rcases Cardinal.lt_lift_iff.mp h with ⟨c', hc', hcc'⟩
  rcases exists_lt_of_lt_ciSup (by simpa [← hcc', Module.rank_def] using h) with ⟨⟨s, hs⟩, h⟩
  rcases Cardinal.le_mk_iff_exists_subset.mp h.le with ⟨t, hst, ht⟩
  exact ⟨t, by simp [ht, hcc'], hs.mono hst⟩

/--
theorem `exists_set_linearIndependent_of_lt_rank` / 定理 `exists_set_linearIndependent_of_lt_rank`

English:
theorem exists_set_linearIndependent_of_lt_rank
  given: {c : Cardinal.{v}} (h : c < Module.rank R M)
  proof: by
  simpa using exists_set_linearIndependent_of_lt_lift_rank (Cardinal.lift_lt.mpr h)

中文:
定理 存在_set_linearIndependent_of_lt_rank
  条件: {c : 基数.{v}} (h : c < 模.rank R M)
  证明: by
  simpa using exists_set_linearIndependent_of_lt_lift_rank (Cardinal.lift_lt.mpr h)

Depends on / 依赖: Cardinal, Cardinal.lift_lt.mpr, exists_set_linearIndependent_of_lt_lift_rank, lift_lt
-/
theorem exists_set_linearIndependent_of_lt_rank {c : Cardinal.{v}} (h : c < Module.rank R M) :
    exists s : Set M, #s = c ∧ LinearIndepOn R id s := by
  simpa using exists_set_linearIndependent_of_lt_lift_rank (Cardinal.lift_lt.mpr h)

variable [Nontrivial R]

-- TODO: the forward directions of the next few theorems don't need [Nontrivial R]
/--
theorem `le_rank_iff_exists_finset` / 定理 `le_rank_iff_exists_finset`

English:
theorem le_rank_iff_exists_finset
  given: {n : Nat}
  proof: by
    contrapose! le
    obtain _ | n := n; · simp at le
    rw [Module.rank]; rw [Nat.cast_add_one]; rw [lt_natCast_add_one_iff]; rw [ciSup_le_iff bddAbove_of_small]
    intro s
    contrapose! le
    rw [← natCast_add_one_le_iff]; rw [← Nat.cast_add_one] at le
    have ⟨t, ht⟩ := exists_finset_eq

中文:
定理 le_rank_iff_存在_finset
  条件: {n : 自然数}
  证明: by
    contrapose! le
    obtain _ | n := n; · simp at le
    rw [Module.rank]; rw [Nat.cast_add_one]; rw [lt_natCast_add_one_iff]; rw [ciSup_le_iff bddAbove_of_small]
    intro s
    contrapose! le
    rw [← natCast_add_one_le_iff]; rw [← Nat.cast_add_one] at le
    have ⟨t, ht⟩ := exists_finset_eq

Depends on / 依赖: Module, Module.rank, Nat.cast_add_one, bddAbove_of_small, card_s, cardinal_le_rank, cast_add_one, ciSup_le_iff, contrapose, exists_finset_eq_card, ht.symm, ind_s, ind_s.cardinal_le_rank, lt_natCast_add_one_iff, natCast_add_one_le_iff, subtype, t.map, trans_eq
-/
theorem le_rank_iff_exists_finset {n : Nat} :
    n <= Module.rank R M ↔ exists s : Finset M, s.card = n ∧ LinearIndepOn R id (s : Set M) where
  mp le := by
    contrapose! le
    obtain _ | n := n; · simp at le
    rw [Module.rank]; rw [Nat.cast_add_one]; rw [lt_natCast_add_one_iff]; rw [ciSup_le_iff bddAbove_of_small]
    intro s
    contrapose! le
    rw [← natCast_add_one_le_iff]; rw [← Nat.cast_add_one] at le
    have ⟨t, ht⟩ := exists_finset_eq_card le
exact ⟨t.map (.subtype _), by simpa using ht.symm, s.2.mono by simp⟩
mpr := fun ⟨s, card_s, ind_s⟩ => ind_s.cardinal_le_rank'.trans_eq' by simpa using card_s

/--
theorem `le_rank_iff` / 定理 `le_rank_iff`

English:
theorem le_rank_iff
  given: {n : Nat}
  statement: n <= Module.rank R M ↔ exists v : Fin n -> M, LinearIndependent R v
  proof: by
  refine le_rank_iff_exists_finset.trans ⟨fun ⟨s, s_card, s_ind⟩ => ?_, fun ⟨v, v_ind⟩ => ?_⟩
  · exact ⟨_, s_ind.comp _ (s.equivFinOfCardEq s_card).symm.injective⟩
  · refine ⟨.map ⟨_, v_ind.injective⟩ .univ, by simp, ?_⟩
    simpa using (linearIndepOn_id_range_iff v_ind.injective).mpr v_ind

中文:
定理 le_rank_iff
  条件: {n : 自然数}
  结论: n <= 模.rank R M ↔ 存在 v : 有限集 n -> M, LinearIndependent R v
  证明: by
  refine le_rank_iff_exists_finset.trans ⟨fun ⟨s, s_card, s_ind⟩ => ?_, fun ⟨v, v_ind⟩ => ?_⟩
  · exact ⟨_, s_ind.comp _ (s.equivFinOfCardEq s_card).symm.injective⟩
  · refine ⟨.map ⟨_, v_ind.injective⟩ .univ, by simp, ?_⟩
    simpa using (linearIndepOn_id_range_iff v_ind.injective).mpr v_ind

Depends on / 依赖: equivFinOfCardEq, injective, le_rank_iff_exists_finset, le_rank_iff_exists_finset.trans, linearIndepOn_id_range_iff, s.equivFinOfCardEq, s_card, s_ind, s_ind.comp, symm.injective, v_ind, v_ind.injective
-/
theorem le_rank_iff {n : Nat} : n <= Module.rank R M ↔ exists v : Fin n -> M, LinearIndependent R v := by
  refine le_rank_iff_exists_finset.trans ⟨fun ⟨s, s_card, s_ind⟩ => ?_, fun ⟨v, v_ind⟩ => ?_⟩
  · exact ⟨_, s_ind.comp _ (s.equivFinOfCardEq s_card).symm.injective⟩
  · refine ⟨.map ⟨_, v_ind.injective⟩ .univ, by simp, ?_⟩
    simpa using (linearIndepOn_id_range_iff v_ind.injective).mpr v_ind

/--
theorem `le_rank_iff_exists_linearMap` / 定理 `le_rank_iff_exists_linearMap`

English:
theorem le_rank_iff_exists_linearMap
  given: {n : Nat}
  proof: by
  refine le_rank_iff.trans ⟨fun ⟨v, v_ind⟩ => ?_, fun ⟨f, f_inj⟩ =>
    ⟨_, (Module.Basis.ofEquivFun <| .refl ..).linearIndependent.map_injOn f f_inj.injOn⟩⟩
  have := Injective.comp v_ind (Finsupp.linearEquivFunOnFinite R ..).symm.injective
  exact ⟨Finsupp.linearCombination .. ∘ₗ _, this⟩

中文:
定理 le_rank_iff_存在_linearMap
  条件: {n : 自然数}
  证明: by
  refine le_rank_iff.trans ⟨fun ⟨v, v_ind⟩ => ?_, fun ⟨f, f_inj⟩ =>
    ⟨_, (Module.Basis.ofEquivFun <| .refl ..).linearIndependent.map_injOn f f_inj.injOn⟩⟩
  have := Injective.comp v_ind (Finsupp.linearEquivFunOnFinite R ..).symm.injective
  exact ⟨Finsupp.linearCombination .. ∘ₗ _, this⟩

Depends on / 依赖: Finsupp, Finsupp.linearCombination, Finsupp.linearEquivFunOnFinite, Injective, Injective.comp, Module, Module.Basis.ofEquivFun, f_inj, f_inj.injOn, injective, le_rank_iff, le_rank_iff.trans, linearCombination, linearEquivFunOnFinite, linearIndependent, linearIndependent.map_injOn, map_injOn, ofEquivFun, symm.injective, v_ind
-/
theorem le_rank_iff_exists_linearMap {n : Nat} :
    n <= Module.rank R M ↔ exists f : (Fin n -> R) ->ₗ[R] M, Injective f := by
  refine le_rank_iff.trans ⟨fun ⟨v, v_ind⟩ => ?_, fun ⟨f, f_inj⟩ =>
    ⟨_, (Module.Basis.ofEquivFun <| .refl ..).linearIndependent.map_injOn f f_inj.injOn⟩⟩
  have := Injective.comp v_ind (Finsupp.linearEquivFunOnFinite R ..).symm.injective
  exact ⟨Finsupp.linearCombination .. ∘ₗ _, this⟩

end Module

section SurjectiveInjective

section Semiring
variable [Semiring R] [AddCommMonoid M] [Module R M] [Semiring R']

variable (R M) in
@[nontriviality, simp]
/--
theorem `rank_subsingleton` / 定理 `rank_subsingleton`

English:
theorem rank_subsingleton
  given: [Subsingleton R]
  statement: Module.rank R M = 1
  proof: by
  rw [Module.rank_def]; rw [ciSup_eq_of_forall_le_of_forall_lt_exists_gt]
  · have := Module.subsingleton R M
    simp [Set.subsingleton_of_subsingleton]
  · intro w hw
    exact ⟨⟨{0}, LinearIndepOn.of_subsingleton⟩, hw.trans_eq (Cardinal.mk_singleton _).symm⟩

中文:
定理 rank_subsingleton
  条件: [子单例 R]
  结论: 模.rank R M = 1
  证明: by
  rw [Module.rank_def]; rw [ciSup_eq_of_forall_le_of_forall_lt_exists_gt]
  · have := Module.subsingleton R M
    simp [Set.subsingleton_of_subsingleton]
  · intro w hw
    exact ⟨⟨{0}, LinearIndepOn.of_subsingleton⟩, hw.trans_eq (Cardinal.mk_singleton _).symm⟩

Depends on / 依赖: Cardinal, Cardinal.mk_singleton, LinearIndepOn, LinearIndepOn.of_subsingleton, Module, Module.rank_def, Module.subsingleton, Set.subsingleton_of_subsingleton, ciSup_eq_of_forall_le_of_forall_lt_exists_gt, hw.trans_eq, mk_singleton, of_subsingleton, rank_def, subsingleton, subsingleton_of_subsingleton, trans_eq
-/
theorem rank_subsingleton [Subsingleton R] : Module.rank R M = 1 := by
  rw [Module.rank_def]; rw [ciSup_eq_of_forall_le_of_forall_lt_exists_gt]
  · have := Module.subsingleton R M
    simp [Set.subsingleton_of_subsingleton]
  · intro w hw
    exact ⟨⟨{0}, LinearIndepOn.of_subsingleton⟩, hw.trans_eq (Cardinal.mk_singleton _).symm⟩

/--
theorem `Module.one_le_rank_iff` / 定理 `Module.one_le_rank_iff`

English:
theorem Module.one_le_rank_iff
  statement: 1 <= Module.rank R M ↔ exists f : R ->ₗ[R] M, Injective f
  proof: by
  nontriviality R
  refine le_rank_iff_exists_linearMap.trans ⟨fun ⟨f, hf⟩ => ?_, fun ⟨f, hf⟩ => ?_⟩
  · exact ⟨f ∘ₗ _, by apply hf.comp (LinearEquiv.piUnique R ..).symm.injective⟩
  · exact ⟨f ∘ₗ _, hf.comp (LinearEquiv.piUnique R ..).injective⟩

中文:
定理 模.one_le_rank_iff
  结论: 1 <= 模.rank R M ↔ 存在 f : R ->ₗ[R] M, 单射 f
  证明: by
  nontriviality R
  refine le_rank_iff_exists_linearMap.trans ⟨fun ⟨f, hf⟩ => ?_, fun ⟨f, hf⟩ => ?_⟩
  · exact ⟨f ∘ₗ _, by apply hf.comp (LinearEquiv.piUnique R ..).symm.injective⟩
  · exact ⟨f ∘ₗ _, hf.comp (LinearEquiv.piUnique R ..).injective⟩

Depends on / 依赖: LinearEquiv, LinearEquiv.piUnique, hf.comp, injective, le_rank_iff_exists_linearMap, le_rank_iff_exists_linearMap.trans, nontriviality, piUnique, symm.injective
-/
theorem Module.one_le_rank_iff : 1 <= Module.rank R M ↔ exists f : R ->ₗ[R] M, Injective f := by
  nontriviality R
  refine le_rank_iff_exists_linearMap.trans ⟨fun ⟨f, hf⟩ => ?_, fun ⟨f, hf⟩ => ?_⟩
  · exact ⟨f ∘ₗ _, by apply hf.comp (LinearEquiv.piUnique R ..).symm.injective⟩
  · exact ⟨f ∘ₗ _, hf.comp (LinearEquiv.piUnique R ..).injective⟩

/--
theorem `Module.rank_eq_zero_of_not_faithfulSMul` / 定理 `Module.rank_eq_zero_of_not_faithfulSMul`

English:
theorem Module.rank_eq_zero_of_not_faithfulSMul
  given: (h : ¬ FaithfulSMul R M)
  statement: Module.rank R M = 0
  proof: by
  contrapose! h
  obtain ⟨f, hf⟩ := by rwa [← Cardinal.one_le_iff_ne_zero, one_le_rank_iff] at h
  exact ⟨fun {x y} hxy => hf (by simpa [← map_smul] using hxy (f 1))⟩

中文:
定理 模.rank_eq_zero_of_not_faithfulSMul
  条件: (h : ¬ 忠实标量乘法 R M)
  结论: 模.rank R M = 0
  证明: by
  contrapose! h
  obtain ⟨f, hf⟩ := by rwa [← Cardinal.one_le_iff_ne_zero, one_le_rank_iff] at h
  exact ⟨fun {x y} hxy => hf (by simpa [← map_smul] using hxy (f 1))⟩

Depends on / 依赖: Cardinal, Cardinal.one_le_iff_ne_zero, contrapose, map_smul, one_le_iff_ne_zero, one_le_rank_iff
-/
theorem Module.rank_eq_zero_of_not_faithfulSMul (h : ¬ FaithfulSMul R M) : Module.rank R M = 0 := by
  contrapose! h
  obtain ⟨f, hf⟩ := by rwa [← Cardinal.one_le_iff_ne_zero, one_le_rank_iff] at h
  exact ⟨fun {x y} hxy => hf (by simpa [← map_smul] using hxy (f 1))⟩

section
variable [AddCommMonoid M'] [Module R' M']

/--
theorem `lift_rank_le_of_injective_injectiveₛ` / 定理 `lift_rank_le_of_injective_injectiveₛ`

English:
theorem lift_rank_le_of_injective_injectiveₛ
  statement: (i : R' -> R) (j : M ->+ M')
  proof: by
  simp_rw [Module.rank, lift_iSup bddAbove_of_small]
  exact ciSup_mono_of_forall_exists' bddAbove_of_small fun ⟨s, h⟩ => ⟨⟨j '' s,
    LinearIndepOn.id_image (h.linearIndependent.map_of_injective_injectiveₛ i j hi hj hc)⟩,
    lift_mk_le'.mpr ⟨(Equiv.Set.image j s hj).toEmbedding⟩⟩

中文:
定理 lift_rank_le_of_injective_injectiveₛ
  结论: (i : R' -> R) (j : M ->+ M')
  证明: by
  simp_rw [Module.rank, lift_iSup bddAbove_of_small]
  exact ciSup_mono_of_forall_exists' bddAbove_of_small fun ⟨s, h⟩ => ⟨⟨j '' s,
    LinearIndepOn.id_image (h.linearIndependent.map_of_injective_injectiveₛ i j hi hj hc)⟩,
    lift_mk_le'.mpr ⟨(Equiv.Set.image j s hj).toEmbedding⟩⟩

Depends on / 依赖: Equiv.Set.image, LinearIndepOn, LinearIndepOn.id_image, Module, Module.rank, bddAbove_of_small, ciSup_mono_of_forall_exists, h.linearIndependent.map_of_injective_injective, id_image, lift_iSup, lift_mk_le, linearIndependent, simp_rw, toEmbedding
-/
theorem lift_rank_le_of_injective_injectiveₛ (i : R' -> R) (j : M ->+ M')
    (hi : Injective i) (hj : Injective j)
    (hc : forall (r : R') (m : M), j (i r • m) = r • j m) :
    lift.{v'} (Module.rank R M) <= lift.{v} (Module.rank R' M') := by
  simp_rw [Module.rank, lift_iSup bddAbove_of_small]
  exact ciSup_mono_of_forall_exists' bddAbove_of_small fun ⟨s, h⟩ => ⟨⟨j '' s,
    LinearIndepOn.id_image (h.linearIndependent.map_of_injective_injectiveₛ i j hi hj hc)⟩,
    lift_mk_le'.mpr ⟨(Equiv.Set.image j s hj).toEmbedding⟩⟩

/--
theorem `lift_rank_le_of_surjective_injective` / 定理 `lift_rank_le_of_surjective_injective`

English:
theorem lift_rank_le_of_surjective_injective
  statement: (i : R -> R') (j : M ->+ M')
  proof: by
  obtain ⟨i', hi'⟩ := hi.hasRightInverse
  refine lift_rank_le_of_injective_injectiveₛ i' j (fun _ _ h => ?_) hj fun r m => ?_
  · apply_fun i at h
    rwa [hi', hi'] at h
  rw [hc (i' r) m]; rw [hi']

中文:
定理 lift_rank_le_of_surjective_injective
  结论: (i : R -> R') (j : M ->+ M')
  证明: by
  obtain ⟨i', hi'⟩ := hi.hasRightInverse
  refine lift_rank_le_of_injective_injectiveₛ i' j (fun _ _ h => ?_) hj fun r m => ?_
  · apply_fun i at h
    rwa [hi', hi'] at h
  rw [hc (i' r) m]; rw [hi']

Depends on / 依赖: apply_fun, hasRightInverse, hi.hasRightInverse
-/
theorem lift_rank_le_of_surjective_injective (i : R -> R') (j : M ->+ M')
    (hi : Surjective i) (hj : Injective j) (hc : forall (r : R) (m : M), j (r • m) = i r • j m) :
    lift.{v'} (Module.rank R M) <= lift.{v} (Module.rank R' M') := by
  obtain ⟨i', hi'⟩ := hi.hasRightInverse
  refine lift_rank_le_of_injective_injectiveₛ i' j (fun _ _ h => ?_) hj fun r m => ?_
  · apply_fun i at h
    rwa [hi', hi'] at h
  rw [hc (i' r) m]; rw [hi']

/--
theorem `lift_rank_eq_of_equiv_equiv` / 定理 `lift_rank_eq_of_equiv_equiv`

English:
theorem lift_rank_eq_of_equiv_equiv
  statement: (i : R -> R') (j : M ≃+ M')
  proof: (lift_rank_le_of_surjective_injective i j hi.2 j.injective hc).antisymm
    lift_rank_le_of_injective_injectiveₛ i j.symm hi.1
j.symm.injective fun _ _ => j.symm_apply_eq.2 by simp_all

中文:
定理 lift_rank_eq_of_equiv_equiv
  结论: (i : R -> R') (j : M ≃+ M')
  证明: (lift_rank_le_of_surjective_injective i j hi.2 j.injective hc).antisymm
    lift_rank_le_of_injective_injectiveₛ i j.symm hi.1
j.symm.injective fun _ _ => j.symm_apply_eq.2 by simp_all

Depends on / 依赖: antisymm, injective, j.injective, j.symm, j.symm.injective, j.symm_apply_eq, lift_rank_le_of_surjective_injective, symm_apply_eq
-/
theorem lift_rank_eq_of_equiv_equiv (i : R -> R') (j : M ≃+ M')
    (hi : Bijective i) (hc : forall (r : R) (m : M), j (r • m) = i r • j m) :
    lift.{v'} (Module.rank R M) = lift.{v} (Module.rank R' M') :=
(lift_rank_le_of_surjective_injective i j hi.2 j.injective hc).antisymm
    lift_rank_le_of_injective_injectiveₛ i j.symm hi.1
j.symm.injective fun _ _ => j.symm_apply_eq.2 by simp_all
end

section
variable [AddCommMonoid M₁] [Module R' M₁]

/--
theorem `rank_le_of_injective_injectiveₛ` / 定理 `rank_le_of_injective_injectiveₛ`

English:
theorem rank_le_of_injective_injectiveₛ
  statement: (i : R' -> R) (j : M ->+ M₁)
  proof: by
  simpa only [lift_id] using lift_rank_le_of_injective_injectiveₛ i j hi hj hc

中文:
定理 rank_le_of_injective_injectiveₛ
  结论: (i : R' -> R) (j : M ->+ M₁)
  证明: by
  simpa only [lift_id] using lift_rank_le_of_injective_injectiveₛ i j hi hj hc

Depends on / 依赖: lift_id
-/
theorem rank_le_of_injective_injectiveₛ (i : R' -> R) (j : M ->+ M₁)
    (hi : Injective i) (hj : Injective j)
    (hc : forall (r : R') (m : M), j (i r • m) = r • j m) :
    Module.rank R M <= Module.rank R' M₁ := by
  simpa only [lift_id] using lift_rank_le_of_injective_injectiveₛ i j hi hj hc

/--
theorem `rank_le_of_surjective_injective` / 定理 `rank_le_of_surjective_injective`

English:
theorem rank_le_of_surjective_injective
  statement: (i : R -> R') (j : M ->+ M₁)
  proof: by
  simpa only [lift_id] using lift_rank_le_of_surjective_injective i j hi hj hc

中文:
定理 rank_le_of_surjective_injective
  结论: (i : R -> R') (j : M ->+ M₁)
  证明: by
  simpa only [lift_id] using lift_rank_le_of_surjective_injective i j hi hj hc

Depends on / 依赖: lift_id, lift_rank_le_of_surjective_injective
-/
theorem rank_le_of_surjective_injective (i : R -> R') (j : M ->+ M₁)
    (hi : Surjective i) (hj : Injective j)
    (hc : forall (r : R) (m : M), j (r • m) = i r • j m) :
    Module.rank R M <= Module.rank R' M₁ := by
  simpa only [lift_id] using lift_rank_le_of_surjective_injective i j hi hj hc

/--
theorem `rank_eq_of_equiv_equiv` / 定理 `rank_eq_of_equiv_equiv`

English:
theorem rank_eq_of_equiv_equiv
  statement: (i : R -> R') (j : M ≃+ M₁)
  proof: by
  simpa only [lift_id] using lift_rank_eq_of_equiv_equiv i j hi hc

中文:
定理 rank_eq_of_equiv_equiv
  结论: (i : R -> R') (j : M ≃+ M₁)
  证明: by
  simpa only [lift_id] using lift_rank_eq_of_equiv_equiv i j hi hc

Depends on / 依赖: lift_id, lift_rank_eq_of_equiv_equiv
-/
theorem rank_eq_of_equiv_equiv (i : R -> R') (j : M ≃+ M₁)
    (hi : Bijective i) (hc : forall (r : R) (m : M), j (r • m) = i r • j m) :
    Module.rank R M = Module.rank R' M₁ := by
  simpa only [lift_id] using lift_rank_eq_of_equiv_equiv i j hi hc

end
end Semiring

set_option backward.isDefEq.respectTransparency false in
/--
theorem `CommSemiring.rank_self` / 定理 `CommSemiring.rank_self`

English:
theorem CommSemiring.rank_self
  given: (R) [CommSemiring R]
  statement: Module.rank R R = 1
  proof: by
  nontriviality R
  rw [le_antisymm_iff]; rw [← not_lt]; rw [← two_le_iff_one_lt]; rw [← Nat.cast_two]; rw [Module.le_rank_iff_exists_linearMap]; rw [Module.one_le_rank_iff]
  refine ⟨fun ⟨f, inj⟩ => ?_, _, (LinearEquiv.refl ..).injective⟩
have := inj (a₁ := f ![0, 1] • ![1, 0]) (a₂ := f ![1, 0] 

中文:
定理 交换半环.rank_self
  条件: (R) [交换半环 R]
  结论: 模.rank R R = 1
  证明: by
  nontriviality R
  rw [le_antisymm_iff]; rw [← not_lt]; rw [← two_le_iff_one_lt]; rw [← Nat.cast_two]; rw [Module.le_rank_iff_exists_linearMap]; rw [Module.one_le_rank_iff]
  refine ⟨fun ⟨f, inj⟩ => ?_, _, (LinearEquiv.refl ..).injective⟩
have := inj (a₁ := f ![0, 1] • ![1, 0]) (a₂ := f ![1, 0] 

Depends on / 依赖: LinearEquiv, LinearEquiv.refl, Module, Module.le_rank_iff_exists_linearMap, Module.one_le_rank_iff, Nat.cast_two, cast_two, injective, le_antisymm_iff, le_rank_iff_exists_linearMap, map_smul, mul_comm, nontriviality, not_lt, one_le_rank_iff, simp_rw, smul_eq_mul, two_le_iff_one_lt, zero_ne_one
-/
theorem CommSemiring.rank_self (R) [CommSemiring R] : Module.rank R R = 1 := by
  nontriviality R
  rw [le_antisymm_iff]; rw [← not_lt]; rw [← two_le_iff_one_lt]; rw [← Nat.cast_two]; rw [Module.le_rank_iff_exists_linearMap]; rw [Module.one_le_rank_iff]
  refine ⟨fun ⟨f, inj⟩ => ?_, _, (LinearEquiv.refl ..).injective⟩
have := inj (a₁ := f ![0, 1] • ![1, 0]) (a₂ := f ![1, 0] • ![0, 1]) by
    simp_rw [map_smul, smul_eq_mul]; apply mul_comm
  have h₁ : f ![0, 1] = 0 := by simpa using congr($this 0)
  have h₂ : 0 = f ![1, 0] := by simpa using congr($this 1)
  exact zero_ne_one (α := R) (by simpa using congr($(inj (h₁.trans h₂)) 1))

section Ring
variable [Ring R] [AddCommGroup M] [Module R M] [Ring R']

/--
theorem `lift_rank_le_of_injective_injective` / 定理 `lift_rank_le_of_injective_injective`

English:
theorem lift_rank_le_of_injective_injective
  statement: [AddCommGroup M'] [Module R' M']
  proof: by
  simp_rw [Module.rank, lift_iSup bddAbove_of_small]
  exact ciSup_mono_of_forall_exists' bddAbove_of_small fun ⟨s, h⟩ =>
⟨⟨j '' s, LinearIndepOn.id_image h.linearIndependent.map_of_injective_injective i j hi
      (fun _ _ => hj <| by rwa [j.map_zero]) hc⟩,
    lift_mk_le'.mpr ⟨(Equiv.Set.image 

中文:
定理 lift_rank_le_of_injective_injective
  结论: [加法交换群 M'] [模 R' M']
  证明: by
  simp_rw [Module.rank, lift_iSup bddAbove_of_small]
  exact ciSup_mono_of_forall_exists' bddAbove_of_small fun ⟨s, h⟩ =>
⟨⟨j '' s, LinearIndepOn.id_image h.linearIndependent.map_of_injective_injective i j hi
      (fun _ _ => hj <| by rwa [j.map_zero]) hc⟩,
    lift_mk_le'.mpr ⟨(Equiv.Set.image 

Depends on / 依赖: Equiv.Set.image, LinearIndepOn, LinearIndepOn.id_image, Module, Module.rank, bddAbove_of_small, ciSup_mono_of_forall_exists, h.linearIndependent.map_of_injective_injective, id_image, j.map_zero, lift_iSup, lift_mk_le, linearIndependent, map_of_injective_injective, map_zero, simp_rw, toEmbedding
-/
theorem lift_rank_le_of_injective_injective [AddCommGroup M'] [Module R' M']
    (i : R' -> R) (j : M ->+ M') (hi : forall r, i r = 0 -> r = 0) (hj : Injective j)
    (hc : forall (r : R') (m : M), j (i r • m) = r • j m) :
    lift.{v'} (Module.rank R M) <= lift.{v} (Module.rank R' M') := by
  simp_rw [Module.rank, lift_iSup bddAbove_of_small]
  exact ciSup_mono_of_forall_exists' bddAbove_of_small fun ⟨s, h⟩ =>
⟨⟨j '' s, LinearIndepOn.id_image h.linearIndependent.map_of_injective_injective i j hi
      (fun _ _ => hj <| by rwa [j.map_zero]) hc⟩,
    lift_mk_le'.mpr ⟨(Equiv.Set.image j s hj).toEmbedding⟩⟩

/--
theorem `rank_le_of_injective_injective` / 定理 `rank_le_of_injective_injective`

English:
theorem rank_le_of_injective_injective
  statement: [AddCommGroup M₁] [Module R' M₁]
  proof: by
  simpa only [lift_id] using lift_rank_le_of_injective_injective i j hi hj hc

中文:
定理 rank_le_of_injective_injective
  结论: [加法交换群 M₁] [模 R' M₁]
  证明: by
  simpa only [lift_id] using lift_rank_le_of_injective_injective i j hi hj hc

Depends on / 依赖: lift_id, lift_rank_le_of_injective_injective
-/
theorem rank_le_of_injective_injective [AddCommGroup M₁] [Module R' M₁]
    (i : R' -> R) (j : M ->+ M₁) (hi : forall r, i r = 0 -> r = 0) (hj : Injective j)
    (hc : forall (r : R') (m : M), j (i r • m) = r • j m) :
    Module.rank R M <= Module.rank R' M₁ := by
  simpa only [lift_id] using lift_rank_le_of_injective_injective i j hi hj hc

end Ring

namespace Algebra

variable {R : Type w} {S : Type v} [CommSemiring R] [Semiring S] [Algebra R S]
  {R' : Type w'} {S' : Type v'} [CommSemiring R'] [Semiring S'] [Algebra R' S']

/--
theorem `lift_rank_le_of_injective_injective` / 定理 `lift_rank_le_of_injective_injective`

English:
theorem lift_rank_le_of_injective_injective
  proof: by
  refine _root_.lift_rank_le_of_injective_injectiveₛ i j hi hj fun r _ => ?_
  have := congr($hc r)
  simp only [RingHom.coe_comp, comp_apply] at this
  simp_rw [smul_def, AddMonoidHom.coe_coe, map_mul, this]

中文:
定理 lift_rank_le_of_injective_injective
  证明: by
  refine _root_.lift_rank_le_of_injective_injectiveₛ i j hi hj fun r _ => ?_
  have := congr($hc r)
  simp only [RingHom.coe_comp, comp_apply] at this
  simp_rw [smul_def, AddMonoidHom.coe_coe, map_mul, this]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.coe_coe, RingHom, RingHom.coe_comp, _root_, _root_.lift_rank_le_of_injective_injective, coe_coe, coe_comp, comp_apply, map_mul, simp_rw, smul_def
-/
theorem lift_rank_le_of_injective_injective
    (i : R' ->+* R) (j : S ->+* S') (hi : Injective i) (hj : Injective j)
    (hc : (j.comp (algebraMap R S)).comp i = algebraMap R' S') :
    lift.{v'} (Module.rank R S) <= lift.{v} (Module.rank R' S') := by
  refine _root_.lift_rank_le_of_injective_injectiveₛ i j hi hj fun r _ => ?_
  have := congr($hc r)
  simp only [RingHom.coe_comp, comp_apply] at this
  simp_rw [smul_def, AddMonoidHom.coe_coe, map_mul, this]

/--
theorem `lift_rank_le_of_surjective_injective` / 定理 `lift_rank_le_of_surjective_injective`

English:
theorem lift_rank_le_of_surjective_injective
  proof: by
  refine _root_.lift_rank_le_of_surjective_injective i j hi hj fun r _ => ?_
  have := congr($hc r)
  simp only [RingHom.coe_comp, comp_apply] at this
  simp only [smul_def, AddMonoidHom.coe_coe, map_mul, this]

中文:
定理 lift_rank_le_of_surjective_injective
  证明: by
  refine _root_.lift_rank_le_of_surjective_injective i j hi hj fun r _ => ?_
  have := congr($hc r)
  simp only [RingHom.coe_comp, comp_apply] at this
  simp only [smul_def, AddMonoidHom.coe_coe, map_mul, this]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.coe_coe, RingHom, RingHom.coe_comp, _root_, _root_.lift_rank_le_of_surjective_injective, coe_coe, coe_comp, comp_apply, lift_rank_le_of_surjective_injective, map_mul, smul_def
-/
theorem lift_rank_le_of_surjective_injective
    (i : R ->+* R') (j : S ->+* S') (hi : Surjective i) (hj : Injective j)
    (hc : (algebraMap R' S').comp i = j.comp (algebraMap R S)) :
    lift.{v'} (Module.rank R S) <= lift.{v} (Module.rank R' S') := by
  refine _root_.lift_rank_le_of_surjective_injective i j hi hj fun r _ => ?_
  have := congr($hc r)
  simp only [RingHom.coe_comp, comp_apply] at this
  simp only [smul_def, AddMonoidHom.coe_coe, map_mul, this]

/--
theorem `lift_rank_eq_of_equiv_equiv` / 定理 `lift_rank_eq_of_equiv_equiv`

English:
theorem lift_rank_eq_of_equiv_equiv
  statement: (i : R ≃+* R') (j : S ≃+* S')
  proof: by
  refine _root_.lift_rank_eq_of_equiv_equiv i j i.bijective fun r _ => ?_
  have := congr($hc r)
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, comp_apply] at this
  simp only [smul_def, RingEquiv.coe_toAddEquiv, map_mul, this]

中文:
定理 lift_rank_eq_of_equiv_equiv
  结论: (i : R ≃+* R') (j : S ≃+* S')
  证明: by
  refine _root_.lift_rank_eq_of_equiv_equiv i j i.bijective fun r _ => ?_
  have := congr($hc r)
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, comp_apply] at this
  simp only [smul_def, RingEquiv.coe_toAddEquiv, map_mul, this]

Depends on / 依赖: RingEquiv, RingEquiv.coe_toAddEquiv, RingEquiv.toRingHom_eq_coe, RingHom, RingHom.coe_coe, RingHom.coe_comp, _root_, _root_.lift_rank_eq_of_equiv_equiv, bijective, coe_coe, coe_comp, coe_toAddEquiv, comp_apply, i.bijective, lift_rank_eq_of_equiv_equiv, map_mul, smul_def, toRingHom_eq_coe
-/
theorem lift_rank_eq_of_equiv_equiv (i : R ≃+* R') (j : S ≃+* S')
    (hc : (algebraMap R' S').comp i.toRingHom = j.toRingHom.comp (algebraMap R S)) :
    lift.{v'} (Module.rank R S) = lift.{v} (Module.rank R' S') := by
  refine _root_.lift_rank_eq_of_equiv_equiv i j i.bijective fun r _ => ?_
  have := congr($hc r)
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, comp_apply] at this
  simp only [smul_def, RingEquiv.coe_toAddEquiv, map_mul, this]

variable {S' : Type v} [Semiring S'] [Algebra R' S']

/--
theorem `rank_le_of_injective_injective` / 定理 `rank_le_of_injective_injective`

English:
theorem rank_le_of_injective_injective
  proof: by
  simpa only [lift_id] using lift_rank_le_of_injective_injective i j hi hj hc

中文:
定理 rank_le_of_injective_injective
  证明: by
  simpa only [lift_id] using lift_rank_le_of_injective_injective i j hi hj hc

Depends on / 依赖: lift_id, lift_rank_le_of_injective_injective
-/
theorem rank_le_of_injective_injective
    (i : R' ->+* R) (j : S ->+* S') (hi : Injective i) (hj : Injective j)
    (hc : (j.comp (algebraMap R S)).comp i = algebraMap R' S') :
    Module.rank R S <= Module.rank R' S' := by
  simpa only [lift_id] using lift_rank_le_of_injective_injective i j hi hj hc

/--
theorem `rank_le_of_surjective_injective` / 定理 `rank_le_of_surjective_injective`

English:
theorem rank_le_of_surjective_injective
  proof: by
  simpa only [lift_id] using lift_rank_le_of_surjective_injective i j hi hj hc

中文:
定理 rank_le_of_surjective_injective
  证明: by
  simpa only [lift_id] using lift_rank_le_of_surjective_injective i j hi hj hc

Depends on / 依赖: lift_id, lift_rank_le_of_surjective_injective
-/
theorem rank_le_of_surjective_injective
    (i : R ->+* R') (j : S ->+* S') (hi : Surjective i) (hj : Injective j)
    (hc : (algebraMap R' S').comp i = j.comp (algebraMap R S)) :
    Module.rank R S <= Module.rank R' S' := by
  simpa only [lift_id] using lift_rank_le_of_surjective_injective i j hi hj hc

/--
theorem `rank_eq_of_equiv_equiv` / 定理 `rank_eq_of_equiv_equiv`

English:
theorem rank_eq_of_equiv_equiv
  statement: (i : R ≃+* R') (j : S ≃+* S')
  proof: by
  simpa only [lift_id] using lift_rank_eq_of_equiv_equiv i j hc

中文:
定理 rank_eq_of_equiv_equiv
  结论: (i : R ≃+* R') (j : S ≃+* S')
  证明: by
  simpa only [lift_id] using lift_rank_eq_of_equiv_equiv i j hc

Depends on / 依赖: lift_id, lift_rank_eq_of_equiv_equiv
-/
theorem rank_eq_of_equiv_equiv (i : R ≃+* R') (j : S ≃+* S')
    (hc : (algebraMap R' S').comp i.toRingHom = j.toRingHom.comp (algebraMap R S)) :
    Module.rank R S = Module.rank R' S' := by
  simpa only [lift_id] using lift_rank_eq_of_equiv_equiv i j hc

end Algebra

end SurjectiveInjective

variable [Semiring R] [AddCommMonoid M] [Module R M]
  [Semiring R'] [AddCommMonoid M'] [AddCommMonoid M₁]
  [Module R M'] [Module R M₁] [Module R' M'] [Module R' M₁]

section

/--
theorem `LinearMap.lift_rank_le_of_injective` / 定理 `LinearMap.lift_rank_le_of_injective`

English:
theorem LinearMap.lift_rank_le_of_injective
  given: (f : M ->ₗ[R] M') (i : Injective f)
  proof: lift_rank_le_of_injective_injectiveₛ (RingHom.id R) f (fun _ _ h => h) i f.map_smul

中文:
定理 线性映射.lift_rank_le_of_injective
  条件: (f : M ->ₗ[R] M') (i : 单射 f)
  证明: lift_rank_le_of_injective_injectiveₛ (RingHom.id R) f (fun _ _ h => h) i f.map_smul

Depends on / 依赖: RingHom, RingHom.id, f.map_smul, map_smul
-/
theorem LinearMap.lift_rank_le_of_injective (f : M ->ₗ[R] M') (i : Injective f) :
    Cardinal.lift.{v'} (Module.rank R M) <= Cardinal.lift.{v} (Module.rank R M') :=
  lift_rank_le_of_injective_injectiveₛ (RingHom.id R) f (fun _ _ h => h) i f.map_smul

/--
theorem `LinearMap.rank_le_of_injective` / 定理 `LinearMap.rank_le_of_injective`

English:
theorem LinearMap.rank_le_of_injective
  given: (f : M ->ₗ[R] M₁) (i : Injective f)
  proof: Cardinal.lift_le.1 (f.lift_rank_le_of_injective i)

中文:
定理 线性映射.rank_le_of_injective
  条件: (f : M ->ₗ[R] M₁) (i : 单射 f)
  证明: Cardinal.lift_le.1 (f.lift_rank_le_of_injective i)

Depends on / 依赖: Cardinal, Cardinal.lift_le, f.lift_rank_le_of_injective, lift_le, lift_rank_le_of_injective
-/
theorem LinearMap.rank_le_of_injective (f : M ->ₗ[R] M₁) (i : Injective f) :
    Module.rank R M <= Module.rank R M₁ :=
  Cardinal.lift_le.1 (f.lift_rank_le_of_injective i)

-- The proof is: a free submodule of the range lifts to a free submodule of the
-- source, by arbitrarily lifting a basis.
/--
theorem `lift_rank_range_le` / 定理 `lift_rank_range_le`

English:
theorem lift_rank_range_le
  given: (f : M ->ₗ[R] M')
  statement: Cardinal.lift.{v}
  proof: by
  simp only [Module.rank_def]
  rw [Cardinal.lift_iSup Cardinal.bddAbove_of_small]
  apply ciSup_le'
  rintro ⟨s, li⟩
  apply le_trans
  swap
  · apply Cardinal.lift_le.mpr
    refine le_ciSup Cardinal.bddAbove_of_small ⟨rangeSplitting f '' s, ?_⟩
    apply LinearIndependent.of_comp f.rangeRestri

中文:
定理 lift_rank_range_le
  条件: (f : M ->ₗ[R] M')
  结论: 基数.lift.{v}
  证明: by
  simp only [Module.rank_def]
  rw [Cardinal.lift_iSup Cardinal.bddAbove_of_small]
  apply ciSup_le'
  rintro ⟨s, li⟩
  apply le_trans
  swap
  · apply Cardinal.lift_le.mpr
    refine le_ciSup Cardinal.bddAbove_of_small ⟨rangeSplitting f '' s, ?_⟩
    apply LinearIndependent.of_comp f.rangeRestri

Depends on / 依赖: Cardinal, Cardinal.bddAbove_of_small, Cardinal.lift_iSup, Cardinal.lift_le.mpr, Cardinal.lift_mk_eq, Equiv.Set.rangeSplittingImageEquiv, Equiv.injective, LinearIndependent, LinearIndependent.of_comp, Module, Module.rank_def, bddAbove_of_small, ciSup_le, convert, f.rangeRestrict, injective, le_ciSup, le_trans, li.comp, lift_iSup
-/
theorem lift_rank_range_le (f : M ->ₗ[R] M') : Cardinal.lift.{v}
    (Module.rank R (LinearMap.range f)) <= Cardinal.lift.{v'} (Module.rank R M) := by
  simp only [Module.rank_def]
  rw [Cardinal.lift_iSup Cardinal.bddAbove_of_small]
  apply ciSup_le'
  rintro ⟨s, li⟩
  apply le_trans
  swap
  · apply Cardinal.lift_le.mpr
    refine le_ciSup Cardinal.bddAbove_of_small ⟨rangeSplitting f '' s, ?_⟩
    apply LinearIndependent.of_comp f.rangeRestrict
    convert! li.comp (Equiv.Set.rangeSplittingImageEquiv f s) (Equiv.injective _) using 1
  · exact (Cardinal.lift_mk_eq'.mpr ⟨Equiv.Set.rangeSplittingImageEquiv f s⟩).ge

/--
theorem `rank_range_le` / 定理 `rank_range_le`

English:
theorem rank_range_le
  given: (f : M ->ₗ[R] M₁)
  statement: Module.rank R (LinearMap.range f) <= Module.rank R M
  proof: by
  simpa using lift_rank_range_le f

中文:
定理 rank_range_le
  条件: (f : M ->ₗ[R] M₁)
  结论: 模.rank R (线性映射.range f) <= 模.rank R M
  证明: by
  simpa using lift_rank_range_le f

Depends on / 依赖: lift_rank_range_le
-/
theorem rank_range_le (f : M ->ₗ[R] M₁) : Module.rank R (LinearMap.range f) <= Module.rank R M := by
  simpa using lift_rank_range_le f

/--
theorem `lift_rank_map_le` / 定理 `lift_rank_map_le`

English:
theorem lift_rank_map_le
  given: (f : M ->ₗ[R] M') (p : Submodule R M)
  proof: by
  have h := lift_rank_range_le (f.comp (Submodule.subtype p))
  rwa [LinearMap.range_comp, range_subtype] at h

中文:
定理 lift_rank_map_le
  条件: (f : M ->ₗ[R] M') (p : 子模 R M)
  证明: by
  have h := lift_rank_range_le (f.comp (Submodule.subtype p))
  rwa [LinearMap.range_comp, range_subtype] at h

Depends on / 依赖: LinearMap, LinearMap.range_comp, Submodule, Submodule.subtype, f.comp, lift_rank_range_le, range_comp, range_subtype, subtype
-/
theorem lift_rank_map_le (f : M ->ₗ[R] M') (p : Submodule R M) :
    Cardinal.lift.{v} (Module.rank R (p.map f)) <= Cardinal.lift.{v'} (Module.rank R p) := by
  have h := lift_rank_range_le (f.comp (Submodule.subtype p))
  rwa [LinearMap.range_comp, range_subtype] at h

/--
theorem `rank_map_le` / 定理 `rank_map_le`

English:
theorem rank_map_le
  given: (f : M ->ₗ[R] M₁) (p : Submodule R M)
  proof: by simpa using lift_rank_map_le f p

中文:
定理 rank_map_le
  条件: (f : M ->ₗ[R] M₁) (p : 子模 R M)
  证明: by simpa using lift_rank_map_le f p

Depends on / 依赖: lift_rank_map_le
-/
theorem rank_map_le (f : M ->ₗ[R] M₁) (p : Submodule R M) :
    Module.rank R (p.map f) <= Module.rank R p := by simpa using lift_rank_map_le f p

/--
theorem `rank_map_eq` / 定理 `rank_map_eq`

English:
theorem rank_map_eq
  given: {f : M ->ₗ[R] M₁} (hf : Injective f) (p : Submodule R M)
  proof: le_antisymm (rank_map_le f p)
    ((f.submoduleMap p).rank_le_of_injective <| LinearMap.submoduleMap_injective hf p)

中文:
定理 rank_map_eq
  条件: {f : M ->ₗ[R] M₁} (hf : 单射 f) (p : 子模 R M)
  证明: le_antisymm (rank_map_le f p)
    ((f.submoduleMap p).rank_le_of_injective <| LinearMap.submoduleMap_injective hf p)

Depends on / 依赖: LinearMap, LinearMap.submoduleMap_injective, f.submoduleMap, le_antisymm, rank_le_of_injective, rank_map_le, submoduleMap, submoduleMap_injective
-/
theorem rank_map_eq {f : M ->ₗ[R] M₁} (hf : Injective f) (p : Submodule R M) :
    Module.rank R (p.map f) = Module.rank R p :=
  le_antisymm (rank_map_le f p)
    ((f.submoduleMap p).rank_le_of_injective <| LinearMap.submoduleMap_injective hf p)

/--
lemma `Submodule.rank_mono` / 引理 `Submodule.rank_mono`

English:
lemma Submodule.rank_mono
  given: {s t : Submodule R M} (h : s <= t)
  statement: Module.rank R s <= Module.rank R t
  proof: (Submodule.inclusion h).rank_le_of_injective fun ⟨x, _⟩ ⟨y, _⟩ eq =>
Subtype.ext show x = y from Subtype.ext_iff.1 eq

中文:
引理 子模.rank_mono
  条件: {s t : 子模 R M} (h : s <= t)
  结论: 模.rank R s <= 模.rank R t
  证明: (Submodule.inclusion h).rank_le_of_injective fun ⟨x, _⟩ ⟨y, _⟩ eq =>
Subtype.ext show x = y from Subtype.ext_iff.1 eq

Depends on / 依赖: Submodule, Submodule.inclusion, Subtype, Subtype.ext, Subtype.ext_iff, ext_iff, inclusion, rank_le_of_injective
-/
lemma Submodule.rank_mono {s t : Submodule R M} (h : s <= t) : Module.rank R s <= Module.rank R t :=
  (Submodule.inclusion h).rank_le_of_injective fun ⟨x, _⟩ ⟨y, _⟩ eq =>
Subtype.ext show x = y from Subtype.ext_iff.1 eq

/--
theorem `LinearEquiv.lift_rank_eq` / 定理 `LinearEquiv.lift_rank_eq`

English:
theorem LinearEquiv.lift_rank_eq
  given: (f : M ≃ₗ[R] M')
  proof: by
  apply le_antisymm
  · exact f.toLinearMap.lift_rank_le_of_injective f.injective
  · exact f.symm.toLinearMap.lift_rank_le_of_injective f.symm.injective

中文:
定理 线性等价.lift_rank_eq
  条件: (f : M ≃ₗ[R] M')
  证明: by
  apply le_antisymm
  · exact f.toLinearMap.lift_rank_le_of_injective f.injective
  · exact f.symm.toLinearMap.lift_rank_le_of_injective f.symm.injective

Depends on / 依赖: f.injective, f.symm.injective, f.symm.toLinearMap.lift_rank_le_of_injective, f.toLinearMap.lift_rank_le_of_injective, injective, le_antisymm, lift_rank_le_of_injective, toLinearMap
-/
theorem LinearEquiv.lift_rank_eq (f : M ≃ₗ[R] M') :
    Cardinal.lift.{v'} (Module.rank R M) = Cardinal.lift.{v} (Module.rank R M') := by
  apply le_antisymm
  · exact f.toLinearMap.lift_rank_le_of_injective f.injective
  · exact f.symm.toLinearMap.lift_rank_le_of_injective f.symm.injective

/--
theorem `LinearEquiv.rank_eq` / 定理 `LinearEquiv.rank_eq`

English:
theorem LinearEquiv.rank_eq
  given: (f : M ≃ₗ[R] M₁)
  statement: Module.rank R M = Module.rank R M₁
  proof: Cardinal.lift_inj.1 f.lift_rank_eq

中文:
定理 线性等价.rank_eq
  条件: (f : M ≃ₗ[R] M₁)
  结论: 模.rank R M = 模.rank R M₁
  证明: Cardinal.lift_inj.1 f.lift_rank_eq

Depends on / 依赖: Cardinal, Cardinal.lift_inj, f.lift_rank_eq, lift_inj, lift_rank_eq
-/
theorem LinearEquiv.rank_eq (f : M ≃ₗ[R] M₁) : Module.rank R M = Module.rank R M₁ :=
  Cardinal.lift_inj.1 f.lift_rank_eq

/--
theorem `lift_rank_range_of_injective` / 定理 `lift_rank_range_of_injective`

English:
theorem lift_rank_range_of_injective
  given: (f : M ->ₗ[R] M') (h : Injective f)
  proof: (LinearEquiv.ofInjective f h).lift_rank_eq.symm

中文:
定理 lift_rank_range_of_injective
  条件: (f : M ->ₗ[R] M') (h : 单射 f)
  证明: (LinearEquiv.ofInjective f h).lift_rank_eq.symm

Depends on / 依赖: LinearEquiv, LinearEquiv.ofInjective, lift_rank_eq, lift_rank_eq.symm, ofInjective
-/
theorem lift_rank_range_of_injective (f : M ->ₗ[R] M') (h : Injective f) :
    lift.{v} (Module.rank R (LinearMap.range f)) = lift.{v'} (Module.rank R M) :=
  (LinearEquiv.ofInjective f h).lift_rank_eq.symm

/--
theorem `rank_range_of_injective` / 定理 `rank_range_of_injective`

English:
theorem rank_range_of_injective
  given: (f : M ->ₗ[R] M₁) (h : Injective f)
  proof: (LinearEquiv.ofInjective f h).rank_eq.symm

中文:
定理 rank_range_of_injective
  条件: (f : M ->ₗ[R] M₁) (h : 单射 f)
  证明: (LinearEquiv.ofInjective f h).rank_eq.symm

Depends on / 依赖: LinearEquiv, LinearEquiv.ofInjective, ofInjective, rank_eq, rank_eq.symm
-/
theorem rank_range_of_injective (f : M ->ₗ[R] M₁) (h : Injective f) :
    Module.rank R (LinearMap.range f) = Module.rank R M :=
  (LinearEquiv.ofInjective f h).rank_eq.symm

/--
theorem `LinearEquiv.lift_rank_map_eq` / 定理 `LinearEquiv.lift_rank_map_eq`

English:
theorem LinearEquiv.lift_rank_map_eq
  given: (f : M ≃ₗ[R] M') (p : Submodule R M)
  proof: (f.submoduleMap p).lift_rank_eq.symm

中文:
定理 线性等价.lift_rank_map_eq
  条件: (f : M ≃ₗ[R] M') (p : 子模 R M)
  证明: (f.submoduleMap p).lift_rank_eq.symm

Depends on / 依赖: f.submoduleMap, lift_rank_eq, lift_rank_eq.symm, submoduleMap
-/
theorem LinearEquiv.lift_rank_map_eq (f : M ≃ₗ[R] M') (p : Submodule R M) :
    lift.{v} (Module.rank R (p.map (f : M ->ₗ[R] M'))) = lift.{v'} (Module.rank R p) :=
  (f.submoduleMap p).lift_rank_eq.symm

/--
theorem `LinearEquiv.rank_map_eq` / 定理 `LinearEquiv.rank_map_eq`

English:
theorem LinearEquiv.rank_map_eq
  given: (f : M ≃ₗ[R] M₁) (p : Submodule R M)
  proof: (f.submoduleMap p).rank_eq.symm

中文:
定理 线性等价.rank_map_eq
  条件: (f : M ≃ₗ[R] M₁) (p : 子模 R M)
  证明: (f.submoduleMap p).rank_eq.symm

Depends on / 依赖: f.submoduleMap, rank_eq, rank_eq.symm, submoduleMap
-/
theorem LinearEquiv.rank_map_eq (f : M ≃ₗ[R] M₁) (p : Submodule R M) :
    Module.rank R (p.map (f : M ->ₗ[R] M₁)) = Module.rank R p :=
  (f.submoduleMap p).rank_eq.symm

variable (R M)

@[simp]
/--
theorem `rank_top` / 定理 `rank_top`

English:
theorem rank_top
  statement: Module.rank R (⊤ : Submodule R M) = Module.rank R M
  proof: (LinearEquiv.ofTop ⊤ rfl).rank_eq

中文:
定理 rank_top
  结论: 模.rank R (⊤ : 子模 R M) = 模.rank R M
  证明: (LinearEquiv.ofTop ⊤ rfl).rank_eq

Depends on / 依赖: LinearEquiv, LinearEquiv.ofTop, rank_eq
-/
theorem rank_top : Module.rank R (⊤ : Submodule R M) = Module.rank R M :=
  (LinearEquiv.ofTop ⊤ rfl).rank_eq

variable {R M}

/--
theorem `rank_range_of_surjective` / 定理 `rank_range_of_surjective`

English:
theorem rank_range_of_surjective
  given: (f : M ->ₗ[R] M') (h : Surjective f)
  proof: by
  rw [LinearMap.range_eq_top.2 h]; rw [rank_top]

中文:
定理 rank_range_of_surjective
  条件: (f : M ->ₗ[R] M') (h : 满射 f)
  证明: by
  rw [LinearMap.range_eq_top.2 h]; rw [rank_top]

Depends on / 依赖: LinearMap, LinearMap.range_eq_top, range_eq_top, rank_top
-/
theorem rank_range_of_surjective (f : M ->ₗ[R] M') (h : Surjective f) :
    Module.rank R (LinearMap.range f) = Module.rank R M' := by
  rw [LinearMap.range_eq_top.2 h]; rw [rank_top]

/--
theorem `Submodule.rank_le` / 定理 `Submodule.rank_le`

English:
theorem Submodule.rank_le
  given: (s : Submodule R M)
  statement: Module.rank R s <= Module.rank R M
  proof: by
  rw [← rank_top R M]
  exact rank_mono le_top

中文:
定理 子模.rank_le
  条件: (s : 子模 R M)
  结论: 模.rank R s <= 模.rank R M
  证明: by
  rw [← rank_top R M]
  exact rank_mono le_top

Depends on / 依赖: le_top, rank_mono, rank_top
-/
theorem Submodule.rank_le (s : Submodule R M) : Module.rank R s <= Module.rank R M := by
  rw [← rank_top R M]
  exact rank_mono le_top

/--
theorem `LinearMap.lift_rank_le_of_surjective` / 定理 `LinearMap.lift_rank_le_of_surjective`

English:
theorem LinearMap.lift_rank_le_of_surjective
  given: (f : M ->ₗ[R] M') (h : Surjective f)
  proof: by
  rw [← rank_range_of_surjective f h]
  apply lift_rank_range_le

中文:
定理 线性映射.lift_rank_le_of_surjective
  条件: (f : M ->ₗ[R] M') (h : 满射 f)
  证明: by
  rw [← rank_range_of_surjective f h]
  apply lift_rank_range_le

Depends on / 依赖: lift_rank_range_le, rank_range_of_surjective
-/
theorem LinearMap.lift_rank_le_of_surjective (f : M ->ₗ[R] M') (h : Surjective f) :
    lift.{v} (Module.rank R M') <= lift.{v'} (Module.rank R M) := by
  rw [← rank_range_of_surjective f h]
  apply lift_rank_range_le

/--
theorem `LinearMap.rank_le_of_surjective` / 定理 `LinearMap.rank_le_of_surjective`

English:
theorem LinearMap.rank_le_of_surjective
  given: (f : M ->ₗ[R] M₁) (h : Surjective f)
  proof: by
  rw [← rank_range_of_surjective f h]
  apply rank_range_le

中文:
定理 线性映射.rank_le_of_surjective
  条件: (f : M ->ₗ[R] M₁) (h : 满射 f)
  证明: by
  rw [← rank_range_of_surjective f h]
  apply rank_range_le

Depends on / 依赖: rank_range_le, rank_range_of_surjective
-/
theorem LinearMap.rank_le_of_surjective (f : M ->ₗ[R] M₁) (h : Surjective f) :
    Module.rank R M₁ <= Module.rank R M := by
  rw [← rank_range_of_surjective f h]
  apply rank_range_le

/--
lemma `rank_le_of_isSMulRegular` / 引理 `rank_le_of_isSMulRegular`

English:
lemma rank_le_of_isSMulRegular
  statement: {S : Type*} [CommSemiring S] [Algebra S R] [Module S M]
  proof: ((Algebra.lsmul S R M s).restrict h).rank_le_of_injective
    fun _ _ h => by simpa using hr (Subtype.ext_iff.mp h)

中文:
引理 rank_le_of_isSMulRegular
  结论: {S : 类型} [交换半环 S] [代数 S R] [模 S M]
  证明: ((Algebra.lsmul S R M s).restrict h).rank_le_of_injective
    fun _ _ h => by simpa using hr (Subtype.ext_iff.mp h)

Depends on / 依赖: Algebra, Algebra.lsmul, Subtype, Subtype.ext_iff.mp, ext_iff, rank_le_of_injective, restrict
-/
lemma rank_le_of_isSMulRegular {S : Type*} [CommSemiring S] [Algebra S R] [Module S M]
    [IsScalarTower S R M] (L L' : Submodule R M) {s : S} (hr : IsSMulRegular M s)
    (h : forall x in L, s • x in L') :
    Module.rank R L <= Module.rank R L' :=
((Algebra.lsmul S R M s).restrict h).rank_le_of_injective
    fun _ _ h => by simpa using hr (Subtype.ext_iff.mp h)

variable (R R' M) in
/--
lemma `Module.rank_top_le_rank_of_isScalarTower` / 引理 `Module.rank_top_le_rank_of_isScalarTower`

English:
lemma Module.rank_top_le_rank_of_isScalarTower
  statement: [Module R' M]
  proof: by
  rw [Module.rank]; rw [Module.rank]
  exact ciSup_le' fun ⟨s, hs⟩ => le_ciSup_of_le Cardinal.bddAbove_of_small
    ⟨s, hs.restrict_scalars (by simpa [← faithfulSMul_iff_injective_smul_one])⟩ le_rfl

中文:
引理 模.rank_top_le_rank_of_isScalarTower
  结论: [模 R' M]
  证明: by
  rw [Module.rank]; rw [Module.rank]
  exact ciSup_le' fun ⟨s, hs⟩ => le_ciSup_of_le Cardinal.bddAbove_of_small
    ⟨s, hs.restrict_scalars (by simpa [← faithfulSMul_iff_injective_smul_one])⟩ le_rfl

Depends on / 依赖: Cardinal, Cardinal.bddAbove_of_small, Module, Module.rank, bddAbove_of_small, ciSup_le, faithfulSMul_iff_injective_smul_one, hs.restrict_scalars, le_ciSup_of_le, le_rfl, restrict_scalars
-/
lemma Module.rank_top_le_rank_of_isScalarTower [Module R' M]
    [SMulWithZero R R'] [IsScalarTower R R' M] [FaithfulSMul R R'] [IsScalarTower R R' R'] :
    Module.rank R' M <= Module.rank R M := by
  rw [Module.rank]; rw [Module.rank]
  exact ciSup_le' fun ⟨s, hs⟩ => le_ciSup_of_le Cardinal.bddAbove_of_small
    ⟨s, hs.restrict_scalars (by simpa [← faithfulSMul_iff_injective_smul_one])⟩ le_rfl

variable (R R') in
/--
lemma `Module.lift_rank_bot_le_lift_rank_of_isScalarTower` / 引理 `Module.lift_rank_bot_le_lift_rank_of_isScalarTower`

English:
lemma Module.lift_rank_bot_le_lift_rank_of_isScalarTower
  statement: (T : Type w) [Module R R']
  proof: LinearMap.lift_rank_le_of_injective ((LinearMap.toSpanSingleton R' T 1).restrictScalars R)
    (faithfulSMul_iff_injective_smul_one R' T).mp ‹_›

中文:
引理 模.lift_rank_bot_le_lift_rank_of_isScalarTower
  结论: (T : 类型 w) [模 R R']
  证明: LinearMap.lift_rank_le_of_injective ((LinearMap.toSpanSingleton R' T 1).restrictScalars R)
    (faithfulSMul_iff_injective_smul_one R' T).mp ‹_›

Depends on / 依赖: LinearMap, LinearMap.lift_rank_le_of_injective, LinearMap.toSpanSingleton, faithfulSMul_iff_injective_smul_one, lift_rank_le_of_injective, restrictScalars, toSpanSingleton
-/
lemma Module.lift_rank_bot_le_lift_rank_of_isScalarTower (T : Type w) [Module R R']
    [NonAssocSemiring T] [Module R T] [Module R' T] [IsScalarTower R' T T] [FaithfulSMul R' T]
    [IsScalarTower R R' T] :
    Cardinal.lift.{w} (Module.rank R R') <= Cardinal.lift (Module.rank R T) :=
LinearMap.lift_rank_le_of_injective ((LinearMap.toSpanSingleton R' T 1).restrictScalars R)
    (faithfulSMul_iff_injective_smul_one R' T).mp ‹_›

variable (R R') in
/--
lemma `Module.rank_bot_le_rank_of_isScalarTower` / 引理 `Module.rank_bot_le_rank_of_isScalarTower`

English:
lemma Module.rank_bot_le_rank_of_isScalarTower
  statement: (T : Type u') [Module R R'] [NonAssocSemiring T]
  proof: by
  simpa using Module.lift_rank_bot_le_lift_rank_of_isScalarTower R R' T

中文:
引理 模.rank_bot_le_rank_of_isScalarTower
  结论: (T : 类型u') [模 R R'] [非结合半环 T]
  证明: by
  simpa using Module.lift_rank_bot_le_lift_rank_of_isScalarTower R R' T

Depends on / 依赖: Module, Module.lift_rank_bot_le_lift_rank_of_isScalarTower, lift_rank_bot_le_lift_rank_of_isScalarTower
-/
lemma Module.rank_bot_le_rank_of_isScalarTower (T : Type u') [Module R R'] [NonAssocSemiring T]
    [Module R T] [Module R' T] [IsScalarTower R' T T] [FaithfulSMul R' T] [IsScalarTower R R' T] :
    Module.rank R R' <= Module.rank R T := by
  simpa using Module.lift_rank_bot_le_lift_rank_of_isScalarTower R R' T

end

end Module
