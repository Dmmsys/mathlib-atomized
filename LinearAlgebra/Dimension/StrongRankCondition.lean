/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.Submodule
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.LinearAlgebra.Dimension.Subsingleton

/-!
# Lemmas about rank and `finrank` in rings satisfying strong rank condition.

## Main statements

For modules over rings satisfying the rank condition

* `Basis.le_span`:
  the cardinality of a basis is bounded by the cardinality of any spanning set

For modules over rings satisfying the strong rank condition

* `linearIndependent_le_span`:
  For any linearly independent family `v : ι → M`
  and any finite spanning set `w : Set M`,
  the cardinality of `ι` is bounded by the cardinality of `w`.
* `linearIndependent_le_basis`:
  If `b` is a basis for a module `M`,
  and `s` is a linearly independent set,
  then the cardinality of `s` is bounded by the cardinality of `b`.

For modules over rings with invariant basis number
(including all commutative rings and all Noetherian rings)

* `mk_eq_mk_of_basis`: the dimension theorem, any two bases of the same vector space have the same
  cardinality.

## Additional definition

* `Algebra.IsQuadraticExtension`: An extension of rings `R ⊆ S` is quadratic if `S` is a
  free `R`-algebra of rank `2`.

-/

@[expose] public section


noncomputable section

universe u v w w'

variable {R : Type u} {S : Type*} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]
variable {ι : Type w} {ι' : Type w'}

open Cardinal Basis Submodule Function Set Module

attribute [local instance] nontrivial_of_invariantBasisNumber

section InvariantBasisNumber

variable [InvariantBasisNumber R]

/--
theorem `mk_eq_mk_of_basis` / 定理 `mk_eq_mk_of_basis`

English:
theorem mk_eq_mk_of_basis
  given: (v : Basis ι R M) (v' : Basis ι' R M)
  proof: by
  have := nontrivial_of_invariantBasisNumber R
  cases fintypeOrInfinite ι
  · -- `v` is a finite basis, so by `basis_finite_of_finite_spans` so is `v'`.
    -- haveI : Finite (range v) := Set.finite_range v
    have := basis_finite_of_finite_spans (Set.finite_range v) v.span_eq v'
    cases nonempty_fintype ι'
    -- We clean up a little:
    rw [Cardinal.mk_fintype]; rw [Cardinal.mk_fintype]
    simp only [Cardinal.lift_natCast, Nat.cast_inj]
    -- Now we can use invariant basis number to show they have the same cardinality.
    apply card_eq_of_linearEquiv R
    exact
      (Finsupp.linearEquivFunOnFinite R R ι).symm.trans v.repr.symm ≪≫ₗ v'.repr ≪≫ₗ
        Finsupp.linearEquivFunOnFinite R R ι'
  · -- `v` is an infinite basis,
    -- so by `infinite_basis_le_maximal_linearIndependent`, `v'` is at least as big,
    -- and then applying `infinite_basis_le_maximal_linearIndependent` again
    -- we see they have the same cardinality.
    have w₁ := infinite_basis_le_maximal_linearIndependent' v _ v'.linearIndependent v'.maximal
    rcases Cardinal.lift_mk_le'.mp w₁ with ⟨f⟩
    have : Infinite ι' := Infinite.of_injective f f.2
    have w₂ := infinite_basis_le_maximal_linearIndependent' v' _ v.linearIndependent v.maximal
    exact le_antisymm w₁ w₂

中文:
定理 mk_eq_mk_of_basis
  条件: (v : 基 ι R M) (v' : 基 ι' R M)
  证明: by
  have := nontrivial_of_invariantBasisNumber R
  cases fintypeOrInfinite ι
  · -- `v` is a finite basis, so by `basis_finite_of_finite_spans` so is `v'`.
    -- haveI : Finite (range v) := Set.finite_range v
    have := basis_finite_of_finite_spans (Set.finite_range v) v.span_eq v'
    cases nonempty_fintype ι'
    -- We clean up a little:
    rw [Cardinal.mk_fintype]; rw [Cardinal.mk_fintype]
    simp only [Cardinal.lift_natCast, Nat.cast_inj]
    -- Now we can use invariant basis number to show they have the same cardinality.
    apply card_eq_of_linearEquiv R
    exact
      (Finsupp.linearEquivFunOnFinite R R ι).symm.trans v.repr.symm ≪≫ₗ v'.repr ≪≫ₗ
        Finsupp.linearEquivFunOnFinite R R ι'
  · -- `v` is an infinite basis,
    -- so by `infinite_basis_le_maximal_linearIndependent`, `v'` is at least as big,
    -- and then applying `infinite_basis_le_maximal_linearIndependent` again
    -- we see they have the same cardinality.
    have w₁ := infinite_basis_le_maximal_linearIndependent' v _ v'.linearIndependent v'.maximal
    rcases Cardinal.lift_mk_le'.mp w₁ with ⟨f⟩
    have : Infinite ι' := Infinite.of_injective f f.2
    have w₂ := infinite_basis_le_maximal_linearIndependent' v' _ v.linearIndependent v.maximal
    exact le_antisymm w₁ w₂

Depends on / 依赖: basis_finite_of_finite_spans, finite, fintypeOrInfinite, nontrivial_of_invariantBasisNumber
-/
theorem mk_eq_mk_of_basis (v : Basis ι R M) (v' : Basis ι' R M) :
    Cardinal.lift.{w'} #ι = Cardinal.lift.{w} #ι' := by
  have := nontrivial_of_invariantBasisNumber R
  cases fintypeOrInfinite ι
  · -- `v` is a finite basis, so by `basis_finite_of_finite_spans` so is `v'`.
    -- haveI : Finite (range v) := Set.finite_range v
    have := basis_finite_of_finite_spans (Set.finite_range v) v.span_eq v'
    cases nonempty_fintype ι'
    -- We clean up a little:
    rw [Cardinal.mk_fintype]; rw [Cardinal.mk_fintype]
    simp only [Cardinal.lift_natCast, Nat.cast_inj]
    -- Now we can use invariant basis number to show they have the same cardinality.
    apply card_eq_of_linearEquiv R
    exact
      (Finsupp.linearEquivFunOnFinite R R ι).symm.trans v.repr.symm ≪≫ₗ v'.repr ≪≫ₗ
        Finsupp.linearEquivFunOnFinite R R ι'
  · -- `v` is an infinite basis,
    -- so by `infinite_basis_le_maximal_linearIndependent`, `v'` is at least as big,
    -- and then applying `infinite_basis_le_maximal_linearIndependent` again
    -- we see they have the same cardinality.
    have w₁ := infinite_basis_le_maximal_linearIndependent' v _ v'.linearIndependent v'.maximal
    rcases Cardinal.lift_mk_le'.mp w₁ with ⟨f⟩
    have : Infinite ι' := Infinite.of_injective f f.2
    have w₂ := infinite_basis_le_maximal_linearIndependent' v' _ v.linearIndependent v.maximal
    exact le_antisymm w₁ w₂

/--
Definition of `Module.Basis.indexEquiv` / `Module.Basis.indexEquiv` 的定义

English:
definition Module.Basis.indexEquiv
  signature: (v : Basis ι R M) (v' : Basis ι' R M)
  body: (Cardinal.lift_mk_eq'.1 <| mk_eq_mk_of_basis v v').some

中文:
定义 模.基.indexEquiv
  签名: (v : 基 ι R M) (v' : 基 ι' R M)
  定义体: (Cardinal.lift_mk_eq'.1 <| mk_eq_mk_of_basis v v').some

Depends on / 依赖: Cardinal, Cardinal.lift_mk_eq, lift_mk_eq, mk_eq_mk_of_basis
-/
def Module.Basis.indexEquiv (v : Basis ι R M) (v' : Basis ι' R M) : ι ≃ ι' :=
  (Cardinal.lift_mk_eq'.1 <| mk_eq_mk_of_basis v v').some

/--
theorem `mk_eq_mk_of_basis'` / 定理 `mk_eq_mk_of_basis'`

English:
theorem mk_eq_mk_of_basis'
  given: {ι' : Type w} (v : Basis ι R M) (v' : Basis ι' R M)
  statement: #ι = #ι'
  proof: Cardinal.lift_inj.1 mk_eq_mk_of_basis v v'

中文:
定理 mk_eq_mk_of_basis'
  条件: {ι' : 类型 w} (v : 基 ι R M) (v' : 基 ι' R M)
  结论: #ι = #ι'
  证明: Cardinal.lift_inj.1 mk_eq_mk_of_basis v v'

Depends on / 依赖: Cardinal, Cardinal.lift_inj, lift_inj, mk_eq_mk_of_basis
-/
theorem mk_eq_mk_of_basis' {ι' : Type w} (v : Basis ι R M) (v' : Basis ι' R M) : #ι = #ι' :=
Cardinal.lift_inj.1 mk_eq_mk_of_basis v v'

end InvariantBasisNumber

section RankCondition

variable [RankCondition R]

/--
theorem `Basis.le_span''` / 定理 `Basis.le_span''`

English:
theorem Basis.le_span''
  statement: {ι : Type*} [Fintype ι] (b : Basis ι R M) {w : Set M} [Fintype w]
  proof: by
  -- We construct a surjective linear map `(w → R) →ₗ[R] (ι → R)`,
  -- by expressing a linear combination in `w` as a linear combination in `ι`.
  fapply card_le_of_surjective' R
  · exact b.repr.toLinearMap.comp (Finsupp.linearCombination R (↑))
  · apply Surjective.comp (g := b.repr.toLinearMap)
    · apply LinearEquiv.surjective
    rw [← LinearMap.range_eq_top]; rw [Finsupp.range_linearCombination]
    simpa using s

中文:
定理 基.le_span''
  结论: {ι : 类型} [有限类型 ι] (b : 基 ι R M) {w : 集合 M} [有限类型 w]
  证明: by
  -- We construct a surjective linear map `(w → R) →ₗ[R] (ι → R)`,
  -- by expressing a linear combination in `w` as a linear combination in `ι`.
  fapply card_le_of_surjective' R
  · exact b.repr.toLinearMap.comp (Finsupp.linearCombination R (↑))
  · apply Surjective.comp (g := b.repr.toLinearMap)
    · apply LinearEquiv.surjective
    rw [← LinearMap.range_eq_top]; rw [Finsupp.range_linearCombination]
    simpa using s
-/
theorem Basis.le_span'' {ι : Type*} [Fintype ι] (b : Basis ι R M) {w : Set M} [Fintype w]
    (s : span R w = ⊤) : Fintype.card ι <= Fintype.card w := by
  -- We construct a surjective linear map `(w → R) →ₗ[R] (ι → R)`,
  -- by expressing a linear combination in `w` as a linear combination in `ι`.
  fapply card_le_of_surjective' R
  · exact b.repr.toLinearMap.comp (Finsupp.linearCombination R (↑))
  · apply Surjective.comp (g := b.repr.toLinearMap)
    · apply LinearEquiv.surjective
    rw [← LinearMap.range_eq_top]; rw [Finsupp.range_linearCombination]
    simpa using s

/--
theorem `basis_le_span'` / 定理 `basis_le_span'`

English:
theorem basis_le_span'
  given: {ι : Type*} (b : Basis ι R M) {w : Set M} [Fintype w] (s : span R w = ⊤)
  proof: by
  have := nontrivial_of_invariantBasisNumber R
  have := basis_finite_of_finite_spans w.toFinite s b
  cases nonempty_fintype ι
  rw [Cardinal.mk_fintype ι]
  simp only [Nat.cast_le]
  exact Basis.le_span'' b s

中文:
定理 basis_le_span'
  条件: {ι : 类型} (b : 基 ι R M) {w : 集合 M} [有限类型 w] (s : span R w = ⊤)
  证明: by
  have := nontrivial_of_invariantBasisNumber R
  have := basis_finite_of_finite_spans w.toFinite s b
  cases nonempty_fintype ι
  rw [Cardinal.mk_fintype ι]
  simp only [Nat.cast_le]
  exact Basis.le_span'' b s

Depends on / 依赖: Basis.le_span, Cardinal, Cardinal.mk_fintype, Nat.cast_le, basis_finite_of_finite_spans, cast_le, le_span, mk_fintype, nonempty_fintype, nontrivial_of_invariantBasisNumber, toFinite, w.toFinite
-/
theorem basis_le_span' {ι : Type*} (b : Basis ι R M) {w : Set M} [Fintype w] (s : span R w = ⊤) :
    #ι <= Fintype.card w := by
  have := nontrivial_of_invariantBasisNumber R
  have := basis_finite_of_finite_spans w.toFinite s b
  cases nonempty_fintype ι
  rw [Cardinal.mk_fintype ι]
  simp only [Nat.cast_le]
  exact Basis.le_span'' b s

-- Note that if `R` satisfies the strong rank condition,
-- this also follows from `linearIndependent_le_span` below.
/--
theorem `Module.Basis.le_span` / 定理 `Module.Basis.le_span`

English:
theorem Module.Basis.le_span
  given: {J : Set M} (v : Basis ι R M) (hJ : span R J = ⊤)
  proof: by
  have := nontrivial_of_invariantBasisNumber R
  cases fintypeOrInfinite J
  · rw [← Cardinal.lift_le, Cardinal.mk_range_eq_of_injective v.injective, Cardinal.mk_fintype J]
    convert! Cardinal.lift_le.{v}.2 (basis_le_span' v hJ)
    simp
  · let S : J -> Set ι := fun j => ↑(v.repr j).support
    let S' : J -> Set M := fun j => v '' S j
    have hs : range v subseteq ⋃ j, S' j := by
      intro b hb
      rcases mem_range.1 hb with ⟨i, hi⟩
      have : span R J <= comap v.repr.toLinearMap (Finsupp.supported R R (⋃ j, S j)) :=
        span_le.2 fun j hj x hx => ⟨_, ⟨⟨j, hj⟩, rfl⟩, hx⟩
      rw [hJ] at this
      replace : v.repr (v i) in Finsupp.supported R R (⋃ j, S j) := this trivial
      rw [v.repr_self]; rw [Finsupp.mem_supported]; rw [Finsupp.support_single _ one_ne_zero] at this
      · subst b
        rcases mem_iUnion.1 (this (Finset.mem_singleton_self _)) with ⟨j, hj⟩
        exact mem_iUnion.2 ⟨j, (mem_image _ _ _).2 ⟨i, hj, rfl⟩⟩
    refine le_of_not_gt fun IJ => ?_
    suffices #(⋃ j, S' j) < #(range v) by exact not_le_of_gt this ⟨Set.embeddingOfSubset _ _ hs⟩
    refine lt_of_le_of_lt (le_trans Cardinal.mk_iUnion_le_sum_mk
      (Cardinal.sum_le_sum _ (fun _ => ℵ₀) ?_)) ?_
    · exact fun j => (Cardinal.lt_aleph0_of_finite _).le
    · simpa

中文:
定理 模.基.le_span
  条件: {J : 集合 M} (v : 基 ι R M) (hJ : span R J = ⊤)
  证明: by
  have := nontrivial_of_invariantBasisNumber R
  cases fintypeOrInfinite J
  · rw [← Cardinal.lift_le, Cardinal.mk_range_eq_of_injective v.injective, Cardinal.mk_fintype J]
    convert! Cardinal.lift_le.{v}.2 (basis_le_span' v hJ)
    simp
  · let S : J -> Set ι := fun j => ↑(v.repr j).support
    let S' : J -> Set M := fun j => v '' S j
    have hs : range v subseteq ⋃ j, S' j := by
      intro b hb
      rcases mem_range.1 hb with ⟨i, hi⟩
      have : span R J <= comap v.repr.toLinearMap (Finsupp.supported R R (⋃ j, S j)) :=
        span_le.2 fun j hj x hx => ⟨_, ⟨⟨j, hj⟩, rfl⟩, hx⟩
      rw [hJ] at this
      replace : v.repr (v i) in Finsupp.supported R R (⋃ j, S j) := this trivial
      rw [v.repr_self]; rw [Finsupp.mem_supported]; rw [Finsupp.support_single _ one_ne_zero] at this
      · subst b
        rcases mem_iUnion.1 (this (Finset.mem_singleton_self _)) with ⟨j, hj⟩
        exact mem_iUnion.2 ⟨j, (mem_image _ _ _).2 ⟨i, hj, rfl⟩⟩
    refine le_of_not_gt fun IJ => ?_
    suffices #(⋃ j, S' j) < #(range v) by exact not_le_of_gt this ⟨Set.embeddingOfSubset _ _ hs⟩
    refine lt_of_le_of_lt (le_trans Cardinal.mk_iUnion_le_sum_mk
      (Cardinal.sum_le_sum _ (fun _ => ℵ₀) ?_)) ?_
    · exact fun j => (Cardinal.lt_aleph0_of_finite _).le
    · simpa

Depends on / 依赖: Cardinal, Cardinal.lift_le, Cardinal.mk_fintype, Cardinal.mk_range_eq_of_injective, Finsupp, Finsupp.supported, basis_le_span, convert, fintypeOrInfinite, injective, lift_le, mem_range, mk_fintype, mk_range_eq_of_injective, nontrivial_of_invariantBasisNumber, span_l, subseteq, support, supported, toLinearMap
-/
theorem Module.Basis.le_span {J : Set M} (v : Basis ι R M) (hJ : span R J = ⊤) :
    #(range v) <= #J := by
  have := nontrivial_of_invariantBasisNumber R
  cases fintypeOrInfinite J
  · rw [← Cardinal.lift_le, Cardinal.mk_range_eq_of_injective v.injective, Cardinal.mk_fintype J]
    convert! Cardinal.lift_le.{v}.2 (basis_le_span' v hJ)
    simp
  · let S : J -> Set ι := fun j => ↑(v.repr j).support
    let S' : J -> Set M := fun j => v '' S j
    have hs : range v subseteq ⋃ j, S' j := by
      intro b hb
      rcases mem_range.1 hb with ⟨i, hi⟩
      have : span R J <= comap v.repr.toLinearMap (Finsupp.supported R R (⋃ j, S j)) :=
        span_le.2 fun j hj x hx => ⟨_, ⟨⟨j, hj⟩, rfl⟩, hx⟩
      rw [hJ] at this
      replace : v.repr (v i) in Finsupp.supported R R (⋃ j, S j) := this trivial
      rw [v.repr_self]; rw [Finsupp.mem_supported]; rw [Finsupp.support_single _ one_ne_zero] at this
      · subst b
        rcases mem_iUnion.1 (this (Finset.mem_singleton_self _)) with ⟨j, hj⟩
        exact mem_iUnion.2 ⟨j, (mem_image _ _ _).2 ⟨i, hj, rfl⟩⟩
    refine le_of_not_gt fun IJ => ?_
    suffices #(⋃ j, S' j) < #(range v) by exact not_le_of_gt this ⟨Set.embeddingOfSubset _ _ hs⟩
    refine lt_of_le_of_lt (le_trans Cardinal.mk_iUnion_le_sum_mk
      (Cardinal.sum_le_sum _ (fun _ => ℵ₀) ?_)) ?_
    · exact fun j => (Cardinal.lt_aleph0_of_finite _).le
    · simpa

end RankCondition

section StrongRankCondition

variable [StrongRankCondition R]

open Submodule Finsupp

-- An auxiliary lemma for `linearIndependent_le_span'`,
-- with the additional assumption that the linearly independent family is finite.
/--
theorem `linearIndependent_le_span_aux'` / 定理 `linearIndependent_le_span_aux'`

English:
theorem linearIndependent_le_span_aux'
  statement: {ι : Type*} [Fintype ι] (v : ι -> M)
  proof: by
  -- We construct an injective linear map `(ι → R) →ₗ[R] (w → R)`,
  -- by thinking of `f : ι → R` as a linear combination of the finite family `v`,
  -- and expressing that (using the axiom of choice) as a linear combination over `w`.
  -- We can do this linearly by constructing the map on a basis.
  fapply card_le_of_injective' R
  · apply Finsupp.linearCombination
    exact fun i => Span.repr R w ⟨v i, s (mem_range_self i)⟩
  · intro f g h
    apply_fun linearCombination R ((↑) : w -> M) at h
    simp only [linearCombination_linearCombination,
               Span.finsupp_linearCombination_repr] at h
    exact i h

中文:
定理 linearIndependent_le_span_aux'
  结论: {ι : 类型} [有限类型 ι] (v : ι -> M)
  证明: by
  -- We construct an injective linear map `(ι → R) →ₗ[R] (w → R)`,
  -- by thinking of `f : ι → R` as a linear combination of the finite family `v`,
  -- and expressing that (using the axiom of choice) as a linear combination over `w`.
  -- We can do this linearly by constructing the map on a basis.
  fapply card_le_of_injective' R
  · apply Finsupp.linearCombination
    exact fun i => Span.repr R w ⟨v i, s (mem_range_self i)⟩
  · intro f g h
    apply_fun linearCombination R ((↑) : w -> M) at h
    simp only [linearCombination_linearCombination,
               Span.finsupp_linearCombination_repr] at h
    exact i h
-/
theorem linearIndependent_le_span_aux' {ι : Type*} [Fintype ι] (v : ι -> M)
    (i : LinearIndependent R v) (w : Set M) [Fintype w] (s : range v <= span R w) :
    Fintype.card ι <= Fintype.card w := by
  -- We construct an injective linear map `(ι → R) →ₗ[R] (w → R)`,
  -- by thinking of `f : ι → R` as a linear combination of the finite family `v`,
  -- and expressing that (using the axiom of choice) as a linear combination over `w`.
  -- We can do this linearly by constructing the map on a basis.
  fapply card_le_of_injective' R
  · apply Finsupp.linearCombination
    exact fun i => Span.repr R w ⟨v i, s (mem_range_self i)⟩
  · intro f g h
    apply_fun linearCombination R ((↑) : w -> M) at h
    simp only [linearCombination_linearCombination,
               Span.finsupp_linearCombination_repr] at h
    exact i h

/--
lemma `LinearIndependent.finite_of_le_span_finite` / 引理 `LinearIndependent.finite_of_le_span_finite`

English:
lemma LinearIndependent.finite_of_le_span_finite
  statement: {ι : Type*} (v : ι -> M) (i : LinearIndependent R v)
  proof: letI := Fintype.ofFinite w
Fintype.finite fintypeOfFinsetCardLe (Fintype.card w) fun t => by
    let v' := fun x : (t : Set ι) => v x
    have i' : LinearIndependent R v' := i.comp _ Subtype.val_injective
    have s' : range v' <= span R w := (range_comp_subset_range _ _).trans s
    simpa using linearIndependent_le_span_aux' v' i' w s'

中文:
引理 LinearIndependent.finite_of_le_span_finite
  结论: {ι : 类型} (v : ι -> M) (i : LinearIndependent R v)
  证明: letI := Fintype.ofFinite w
Fintype.finite fintypeOfFinsetCardLe (Fintype.card w) fun t => by
    let v' := fun x : (t : Set ι) => v x
    have i' : LinearIndependent R v' := i.comp _ Subtype.val_injective
    have s' : range v' <= span R w := (range_comp_subset_range _ _).trans s
    simpa using linearIndependent_le_span_aux' v' i' w s'

Depends on / 依赖: Fintype, Fintype.card, Fintype.finite, Fintype.ofFinite, LinearIndependent, Subtype, Subtype.val_injective, finite, fintypeOfFinsetCardLe, i.comp, linearIndependent_le_span_aux, ofFinite, range_comp_subset_range, val_injective
-/
lemma LinearIndependent.finite_of_le_span_finite {ι : Type*} (v : ι -> M) (i : LinearIndependent R v)
    (w : Set M) [Finite w] (s : range v <= span R w) : Finite ι :=
  letI := Fintype.ofFinite w
Fintype.finite fintypeOfFinsetCardLe (Fintype.card w) fun t => by
    let v' := fun x : (t : Set ι) => v x
    have i' : LinearIndependent R v' := i.comp _ Subtype.val_injective
    have s' : range v' <= span R w := (range_comp_subset_range _ _).trans s
    simpa using linearIndependent_le_span_aux' v' i' w s'

/--
theorem `linearIndependent_le_span'` / 定理 `linearIndependent_le_span'`

English:
theorem linearIndependent_le_span'
  statement: {ι : Type*} (v : ι -> M) (i : LinearIndependent R v) (w : Set M)
  proof: by
  have : Finite ι := i.finite_of_le_span_finite v w s
  let := Fintype.ofFinite ι
  rw [Cardinal.mk_fintype]
  simp only [Nat.cast_le]
  exact linearIndependent_le_span_aux' v i w s

中文:
定理 linearIndependent_le_span'
  结论: {ι : 类型} (v : ι -> M) (i : LinearIndependent R v) (w : 集合 M)
  证明: by
  have : Finite ι := i.finite_of_le_span_finite v w s
  let := Fintype.ofFinite ι
  rw [Cardinal.mk_fintype]
  simp only [Nat.cast_le]
  exact linearIndependent_le_span_aux' v i w s

Depends on / 依赖: Cardinal, Cardinal.mk_fintype, Finite, Fintype, Fintype.ofFinite, Nat.cast_le, cast_le, finite_of_le_span_finite, i.finite_of_le_span_finite, linearIndependent_le_span_aux, mk_fintype, ofFinite
-/
theorem linearIndependent_le_span' {ι : Type*} (v : ι -> M) (i : LinearIndependent R v) (w : Set M)
    [Fintype w] (s : range v <= span R w) : #ι <= Fintype.card w := by
  have : Finite ι := i.finite_of_le_span_finite v w s
  let := Fintype.ofFinite ι
  rw [Cardinal.mk_fintype]
  simp only [Nat.cast_le]
  exact linearIndependent_le_span_aux' v i w s

/--
theorem `linearIndependent_le_span` / 定理 `linearIndependent_le_span`

English:
theorem linearIndependent_le_span
  statement: {ι : Type*} (v : ι -> M) (i : LinearIndependent R v) (w : Set M)
  proof: by
  apply linearIndependent_le_span' v i w
  rw [s]
  exact le_top

中文:
定理 linearIndependent_le_span
  结论: {ι : 类型} (v : ι -> M) (i : LinearIndependent R v) (w : 集合 M)
  证明: by
  apply linearIndependent_le_span' v i w
  rw [s]
  exact le_top

Depends on / 依赖: le_top, linearIndependent_le_span
-/
theorem linearIndependent_le_span {ι : Type*} (v : ι -> M) (i : LinearIndependent R v) (w : Set M)
    [Fintype w] (s : span R w = ⊤) : #ι <= Fintype.card w := by
  apply linearIndependent_le_span' v i w
  rw [s]
  exact le_top

/--
theorem `linearIndependent_le_span_finset` / 定理 `linearIndependent_le_span_finset`

English:
theorem linearIndependent_le_span_finset
  statement: {ι : Type*} (v : ι -> M) (i : LinearIndependent R v)
  proof: by
  simpa only [Finset.coe_sort_coe, Fintype.card_coe] using linearIndependent_le_span v i w s

中文:
定理 linearIndependent_le_span_finset
  结论: {ι : 类型} (v : ι -> M) (i : LinearIndependent R v)
  证明: by
  simpa only [Finset.coe_sort_coe, Fintype.card_coe] using linearIndependent_le_span v i w s

Depends on / 依赖: Finset, Finset.coe_sort_coe, Fintype, Fintype.card_coe, card_coe, coe_sort_coe, linearIndependent_le_span
-/
theorem linearIndependent_le_span_finset {ι : Type*} (v : ι -> M) (i : LinearIndependent R v)
    (w : Finset M) (s : span R (w : Set M) = ⊤) : #ι <= w.card := by
  simpa only [Finset.coe_sort_coe, Fintype.card_coe] using linearIndependent_le_span v i w s

/--
theorem `linearIndependent_le_infinite_basis` / 定理 `linearIndependent_le_infinite_basis`

English:
theorem linearIndependent_le_infinite_basis
  statement: {ι : Type w} (b : Basis ι R M) [Infinite ι] {κ : Type w}
  proof: by
  classical
  by_contra h
  rw [not_le]; rw [← Cardinal.mk_finset_of_infinite ι] at h
  let Φ := fun k : κ => (b.repr (v k)).support
  obtain ⟨s, w : Infinite ↑(Φ ⁻¹' {s})⟩ := Cardinal.exists_infinite_fiber' Φ h
  let v' := fun k : Φ ⁻¹' {s} => v k
  have i' : LinearIndependent R v' := i.comp _ Subtype.val_injective
  have w' : Finite (Φ ⁻¹' {s}) := by
    apply i'.finite_of_le_span_finite v' (s.image b)
    rintro m ⟨⟨p, ⟨rfl⟩⟩, rfl⟩
    simp only [SetLike.mem_coe, Finset.coe_image]
    apply Basis.mem_span_repr_support
  exact w.false

中文:
定理 linearIndependent_le_infinite_basis
  结论: {ι : 类型 w} (b : 基 ι R M) [无限 ι] {κ : 类型 w}
  证明: by
  classical
  by_contra h
  rw [not_le]; rw [← Cardinal.mk_finset_of_infinite ι] at h
  let Φ := fun k : κ => (b.repr (v k)).support
  obtain ⟨s, w : Infinite ↑(Φ ⁻¹' {s})⟩ := Cardinal.exists_infinite_fiber' Φ h
  let v' := fun k : Φ ⁻¹' {s} => v k
  have i' : LinearIndependent R v' := i.comp _ Subtype.val_injective
  have w' : Finite (Φ ⁻¹' {s}) := by
    apply i'.finite_of_le_span_finite v' (s.image b)
    rintro m ⟨⟨p, ⟨rfl⟩⟩, rfl⟩
    simp only [SetLike.mem_coe, Finset.coe_image]
    apply Basis.mem_span_repr_support
  exact w.false

Depends on / 依赖: Basis.mem_span_repr_support, Cardinal, Cardinal.exists_infinite_fiber, Cardinal.mk_finset_of_infinite, Finite, Finset, Finset.coe_image, Infinite, LinearIndependent, SetLike, SetLike.mem_coe, Subtype, Subtype.val_injective, b.repr, classical, coe_image, exists_infinite_fiber, finite_of_le_span_finite, i.comp, mem_coe
-/
theorem linearIndependent_le_infinite_basis {ι : Type w} (b : Basis ι R M) [Infinite ι] {κ : Type w}
    (v : κ -> M) (i : LinearIndependent R v) : #κ <= #ι := by
  classical
  by_contra h
  rw [not_le]; rw [← Cardinal.mk_finset_of_infinite ι] at h
  let Φ := fun k : κ => (b.repr (v k)).support
  obtain ⟨s, w : Infinite ↑(Φ ⁻¹' {s})⟩ := Cardinal.exists_infinite_fiber' Φ h
  let v' := fun k : Φ ⁻¹' {s} => v k
  have i' : LinearIndependent R v' := i.comp _ Subtype.val_injective
  have w' : Finite (Φ ⁻¹' {s}) := by
    apply i'.finite_of_le_span_finite v' (s.image b)
    rintro m ⟨⟨p, ⟨rfl⟩⟩, rfl⟩
    simp only [SetLike.mem_coe, Finset.coe_image]
    apply Basis.mem_span_repr_support
  exact w.false

/--
theorem `linearIndependent_le_basis` / 定理 `linearIndependent_le_basis`

English:
theorem linearIndependent_le_basis
  statement: {ι : Type w} (b : Basis ι R M) {κ : Type w} (v : κ -> M)
  proof: by
  classical
  -- We split into cases depending on whether `ι` is infinite.
  cases fintypeOrInfinite ι
  · rw [Cardinal.mk_fintype ι] -- When `ι` is finite, we have `linearIndependent_le_span`,
    have : Nontrivial R := nontrivial_of_invariantBasisNumber R
    rw [Fintype.card_congr (Equiv.ofInjective b b.injective)]
    exact linearIndependent_le_span v i (range b) b.span_eq
  · -- and otherwise we have `linearIndependent_le_infinite_basis`.
    exact linearIndependent_le_infinite_basis b v i

中文:
定理 linearIndependent_le_basis
  结论: {ι : 类型 w} (b : 基 ι R M) {κ : 类型 w} (v : κ -> M)
  证明: by
  classical
  -- We split into cases depending on whether `ι` is infinite.
  cases fintypeOrInfinite ι
  · rw [Cardinal.mk_fintype ι] -- When `ι` is finite, we have `linearIndependent_le_span`,
    have : Nontrivial R := nontrivial_of_invariantBasisNumber R
    rw [Fintype.card_congr (Equiv.ofInjective b b.injective)]
    exact linearIndependent_le_span v i (range b) b.span_eq
  · -- and otherwise we have `linearIndependent_le_infinite_basis`.
    exact linearIndependent_le_infinite_basis b v i

Depends on / 依赖: classical
-/
theorem linearIndependent_le_basis {ι : Type w} (b : Basis ι R M) {κ : Type w} (v : κ -> M)
    (i : LinearIndependent R v) : #κ <= #ι := by
  classical
  -- We split into cases depending on whether `ι` is infinite.
  cases fintypeOrInfinite ι
  · rw [Cardinal.mk_fintype ι] -- When `ι` is finite, we have `linearIndependent_le_span`,
    have : Nontrivial R := nontrivial_of_invariantBasisNumber R
    rw [Fintype.card_congr (Equiv.ofInjective b b.injective)]
    exact linearIndependent_le_span v i (range b) b.span_eq
  · -- and otherwise we have `linearIndependent_le_infinite_basis`.
    exact linearIndependent_le_infinite_basis b v i

/--
theorem `card_le_of_injective''` / 定理 `card_le_of_injective''`

English:
theorem card_le_of_injective''
  statement: {α : Type v} {β : Type v} (f : (α ->₀ R) ->ₗ[R] β ->₀ R)
  proof: by
  let b : Basis β R (β ->₀ R) := ⟨1⟩
  apply linearIndependent_le_basis b (fun (i : α) => f (Finsupp.single i 1))
  rw [LinearIndependent]
  have : (linearCombination R fun i => f (Finsupp.single i 1)) = f := by ext a b; simp
  exact this.symm ▸ i

中文:
定理 card_le_of_injective''
  结论: {α : 类型v} {β : 类型v} (f : (α ->₀ R) ->ₗ[R] β ->₀ R)
  证明: by
  let b : Basis β R (β ->₀ R) := ⟨1⟩
  apply linearIndependent_le_basis b (fun (i : α) => f (Finsupp.single i 1))
  rw [LinearIndependent]
  have : (linearCombination R fun i => f (Finsupp.single i 1)) = f := by ext a b; simp
  exact this.symm ▸ i

Depends on / 依赖: Finsupp, Finsupp.single, LinearIndependent, linearCombination, linearIndependent_le_basis, single, this.symm
-/
theorem card_le_of_injective'' {α : Type v} {β : Type v} (f : (α ->₀ R) ->ₗ[R] β ->₀ R)
    (i : Injective f) : #α <= #β := by
  let b : Basis β R (β ->₀ R) := ⟨1⟩
  apply linearIndependent_le_basis b (fun (i : α) => f (Finsupp.single i 1))
  rw [LinearIndependent]
  have : (linearCombination R fun i => f (Finsupp.single i 1)) = f := by ext a b; simp
  exact this.symm ▸ i

/--
theorem `linearIndependent_le_span''` / 定理 `linearIndependent_le_span''`

English:
theorem linearIndependent_le_span''
  statement: {ι : Type v} {v : ι -> M} (i : LinearIndependent R v) (w : Set M)
  proof: by
  fapply card_le_of_injective'' (R := R)
  · apply Finsupp.linearCombination
    exact fun i => Span.repr R w ⟨v i, s ▸ trivial⟩
  · intro f g h
    apply_fun linearCombination R ((↑) : w -> M) at h
    simp only [linearCombination_linearCombination,
               Span.finsupp_linearCombination_repr] at h
    exact i h

中文:
定理 linearIndependent_le_span''
  结论: {ι : 类型v} {v : ι -> M} (i : LinearIndependent R v) (w : 集合 M)
  证明: by
  fapply card_le_of_injective'' (R := R)
  · apply Finsupp.linearCombination
    exact fun i => Span.repr R w ⟨v i, s ▸ trivial⟩
  · intro f g h
    apply_fun linearCombination R ((↑) : w -> M) at h
    simp only [linearCombination_linearCombination,
               Span.finsupp_linearCombination_repr] at h
    exact i h

Depends on / 依赖: Finsupp, Finsupp.linearCombination, Span.finsupp_linearCombination_repr, Span.repr, apply_fun, card_le_of_injective, fapply, finsupp_linearCombination_repr, linearCombination, linearCombination_linearCombination
-/
theorem linearIndependent_le_span'' {ι : Type v} {v : ι -> M} (i : LinearIndependent R v) (w : Set M)
    (s : span R w = ⊤) : #ι <= #w := by
  fapply card_le_of_injective'' (R := R)
  · apply Finsupp.linearCombination
    exact fun i => Span.repr R w ⟨v i, s ▸ trivial⟩
  · intro f g h
    apply_fun linearCombination R ((↑) : w -> M) at h
    simp only [linearCombination_linearCombination,
               Span.finsupp_linearCombination_repr] at h
    exact i h

/--
theorem `Basis.card_le_card_of_linearIndependent_aux` / 定理 `Basis.card_le_card_of_linearIndependent_aux`

English:
theorem Basis.card_le_card_of_linearIndependent_aux
  statement: {R : Type*} [Semiring R] [StrongRankCondition R]
  proof: fun h => by
  simpa using linearIndependent_le_basis (Pi.basisFun R (Fin n)) v h

中文:
定理 基.card_le_card_of_linearIndependent_aux
  结论: {R : 类型} [半环 R] [StrongRankCondition R]
  证明: fun h => by
  simpa using linearIndependent_le_basis (Pi.basisFun R (Fin n)) v h

Depends on / 依赖: Pi.basisFun, basisFun, linearIndependent_le_basis
-/
theorem Basis.card_le_card_of_linearIndependent_aux {R : Type*} [Semiring R] [StrongRankCondition R]
    (n : Nat) {m : Nat} (v : Fin m -> Fin n -> R) : LinearIndependent R v -> m <= n := fun h => by
  simpa using linearIndependent_le_basis (Pi.basisFun R (Fin n)) v h

-- When the basis is not infinite this need not be true!
/--
theorem `maximal_linearIndependent_eq_infinite_basis` / 定理 `maximal_linearIndependent_eq_infinite_basis`

English:
theorem maximal_linearIndependent_eq_infinite_basis
  statement: {ι : Type w} (b : Basis ι R M) [Infinite ι]
  proof: by
  apply le_antisymm
  · exact linearIndependent_le_basis b v i
  · have : Nontrivial R := nontrivial_of_invariantBasisNumber R
    exact infinite_basis_le_maximal_linearIndependent b v i m

中文:
定理 maximal_linearIndependent_eq_infinite_basis
  结论: {ι : 类型 w} (b : 基 ι R M) [无限 ι]
  证明: by
  apply le_antisymm
  · exact linearIndependent_le_basis b v i
  · have : Nontrivial R := nontrivial_of_invariantBasisNumber R
    exact infinite_basis_le_maximal_linearIndependent b v i m

Depends on / 依赖: Nontrivial, infinite_basis_le_maximal_linearIndependent, le_antisymm, linearIndependent_le_basis, nontrivial_of_invariantBasisNumber
-/
theorem maximal_linearIndependent_eq_infinite_basis {ι : Type w} (b : Basis ι R M) [Infinite ι]
    {κ : Type w} (v : κ -> M) (i : LinearIndependent R v) (m : i.Maximal) : #κ = #ι := by
  apply le_antisymm
  · exact linearIndependent_le_basis b v i
  · have : Nontrivial R := nontrivial_of_invariantBasisNumber R
    exact infinite_basis_le_maximal_linearIndependent b v i m

/--
theorem `Module.Basis.mk_eq_rank''` / 定理 `Module.Basis.mk_eq_rank''`

English:
theorem Module.Basis.mk_eq_rank''
  given: {ι : Type v} (v : Basis ι R M)
  statement: #ι = Module.rank R M
  proof: by
  have := nontrivial_of_invariantBasisNumber R
  rw [Module.rank_def]
  apply le_antisymm
  · trans
    swap
    · apply le_ciSup Cardinal.bddAbove_of_small
      exact
        ⟨Set.range v, by
          rw [LinearIndepOn]
          convert! v.reindexRange.linearIndependent
          simp⟩
    · exact (Cardinal.mk_range_eq v v.injective).ge
  · apply ciSup_le'
    rintro ⟨s, li⟩
    apply linearIndependent_le_basis v _ li

中文:
定理 模.基.mk_eq_rank''
  条件: {ι : 类型v} (v : 基 ι R M)
  结论: #ι = 模.rank R M
  证明: by
  have := nontrivial_of_invariantBasisNumber R
  rw [Module.rank_def]
  apply le_antisymm
  · trans
    swap
    · apply le_ciSup Cardinal.bddAbove_of_small
      exact
        ⟨Set.range v, by
          rw [LinearIndepOn]
          convert! v.reindexRange.linearIndependent
          simp⟩
    · exact (Cardinal.mk_range_eq v v.injective).ge
  · apply ciSup_le'
    rintro ⟨s, li⟩
    apply linearIndependent_le_basis v _ li

Depends on / 依赖: Cardinal, Cardinal.bddAbove_of_small, Cardinal.mk_range_eq, LinearIndepOn, Module, Module.rank_def, Set.range, bddAbove_of_small, ciSup_le, convert, injective, le_antisymm, le_ciSup, linearIndependent, linearIndependent_le_basis, mk_range_eq, nontrivial_of_invariantBasisNumber, rank_def, reindexRange, v.injective
-/
theorem Module.Basis.mk_eq_rank'' {ι : Type v} (v : Basis ι R M) : #ι = Module.rank R M := by
  have := nontrivial_of_invariantBasisNumber R
  rw [Module.rank_def]
  apply le_antisymm
  · trans
    swap
    · apply le_ciSup Cardinal.bddAbove_of_small
      exact
        ⟨Set.range v, by
          rw [LinearIndepOn]
          convert! v.reindexRange.linearIndependent
          simp⟩
    · exact (Cardinal.mk_range_eq v v.injective).ge
  · apply ciSup_le'
    rintro ⟨s, li⟩
    apply linearIndependent_le_basis v _ li

/--
theorem `Module.Basis.mk_range_eq_rank` / 定理 `Module.Basis.mk_range_eq_rank`

English:
theorem Module.Basis.mk_range_eq_rank
  given: (v : Basis ι R M)
  statement: #(range v) = Module.rank R M
  proof: v.reindexRange.mk_eq_rank''

中文:
定理 模.基.mk_range_eq_rank
  条件: (v : 基 ι R M)
  结论: #(range v) = 模.rank R M
  证明: v.reindexRange.mk_eq_rank''

Depends on / 依赖: mk_eq_rank, reindexRange, v.reindexRange.mk_eq_rank
-/
theorem Module.Basis.mk_range_eq_rank (v : Basis ι R M) : #(range v) = Module.rank R M :=
  v.reindexRange.mk_eq_rank''

/--
theorem `rank_eq_card_basis` / 定理 `rank_eq_card_basis`

English:
theorem rank_eq_card_basis
  given: {ι : Type w} [Fintype ι] (h : Basis ι R M)
  proof: by
  classical
  have := nontrivial_of_invariantBasisNumber R
  rw [← h.mk_range_eq_rank]; rw [Cardinal.mk_fintype]; rw [Set.card_range_of_injective h.injective]

中文:
定理 rank_eq_card_basis
  条件: {ι : 类型 w} [有限类型 ι] (h : 基 ι R M)
  证明: by
  classical
  have := nontrivial_of_invariantBasisNumber R
  rw [← h.mk_range_eq_rank]; rw [Cardinal.mk_fintype]; rw [Set.card_range_of_injective h.injective]

Depends on / 依赖: Cardinal, Cardinal.mk_fintype, Set.card_range_of_injective, card_range_of_injective, classical, h.injective, h.mk_range_eq_rank, injective, mk_fintype, mk_range_eq_rank, nontrivial_of_invariantBasisNumber
-/
theorem rank_eq_card_basis {ι : Type w} [Fintype ι] (h : Basis ι R M) :
    Module.rank R M = Fintype.card ι := by
  classical
  have := nontrivial_of_invariantBasisNumber R
  rw [← h.mk_range_eq_rank]; rw [Cardinal.mk_fintype]; rw [Set.card_range_of_injective h.injective]

namespace Module.Basis

/--
theorem `card_le_card_of_linearIndependent` / 定理 `card_le_card_of_linearIndependent`

English:
theorem card_le_card_of_linearIndependent
  statement: {ι : Type*} [Fintype ι] (b : Basis ι R M)
  proof: by
  simpa [rank_eq_card_basis b, Cardinal.mk_fintype] using hv.cardinal_lift_le_rank

中文:
定理 card_le_card_of_linearIndependent
  结论: {ι : 类型} [有限类型 ι] (b : 基 ι R M)
  证明: by
  simpa [rank_eq_card_basis b, Cardinal.mk_fintype] using hv.cardinal_lift_le_rank

Depends on / 依赖: Cardinal, Cardinal.mk_fintype, cardinal_lift_le_rank, hv.cardinal_lift_le_rank, mk_fintype, rank_eq_card_basis
-/
theorem card_le_card_of_linearIndependent {ι : Type*} [Fintype ι] (b : Basis ι R M)
    {ι' : Type*} [Fintype ι'] {v : ι' -> M} (hv : LinearIndependent R v) :
    Fintype.card ι' <= Fintype.card ι := by
  simpa [rank_eq_card_basis b, Cardinal.mk_fintype] using hv.cardinal_lift_le_rank

/--
theorem `card_le_card_of_submodule` / 定理 `card_le_card_of_submodule`

English:
theorem card_le_card_of_submodule
  statement: (N : Submodule R M) [Fintype ι] (b : Basis ι R M)
  proof: b.card_le_card_of_linearIndependent
    (b'.linearIndependent.map_injOn N.subtype N.injective_subtype.injOn)

中文:
定理 card_le_card_of_submodule
  结论: (N : 子模 R M) [有限类型 ι] (b : 基 ι R M)
  证明: b.card_le_card_of_linearIndependent
    (b'.linearIndependent.map_injOn N.subtype N.injective_subtype.injOn)

Depends on / 依赖: N.injective_subtype.injOn, N.subtype, b.card_le_card_of_linearIndependent, card_le_card_of_linearIndependent, injective_subtype, linearIndependent, linearIndependent.map_injOn, map_injOn, subtype
-/
theorem card_le_card_of_submodule (N : Submodule R M) [Fintype ι] (b : Basis ι R M)
    [Fintype ι'] (b' : Basis ι' R N) : Fintype.card ι' <= Fintype.card ι :=
  b.card_le_card_of_linearIndependent
    (b'.linearIndependent.map_injOn N.subtype N.injective_subtype.injOn)

/--
theorem `card_le_card_of_le` / 定理 `card_le_card_of_le`

English:
theorem card_le_card_of_le
  statement: {N O : Submodule R M} (hNO : N <= O) [Fintype ι]
  proof: b.card_le_card_of_linearIndependent
    (b'.linearIndependent.map_injOn (inclusion hNO) (N.inclusion_injective _).injOn)

中文:
定理 card_le_card_of_le
  结论: {N O : 子模 R M} (hNO : N <= O) [有限类型 ι]
  证明: b.card_le_card_of_linearIndependent
    (b'.linearIndependent.map_injOn (inclusion hNO) (N.inclusion_injective _).injOn)

Depends on / 依赖: N.inclusion_injective, b.card_le_card_of_linearIndependent, card_le_card_of_linearIndependent, inclusion, inclusion_injective, linearIndependent, linearIndependent.map_injOn, map_injOn
-/
theorem card_le_card_of_le {N O : Submodule R M} (hNO : N <= O) [Fintype ι]
    (b : Basis ι R O) [Fintype ι'] (b' : Basis ι' R N) : Fintype.card ι' <= Fintype.card ι :=
  b.card_le_card_of_linearIndependent
    (b'.linearIndependent.map_injOn (inclusion hNO) (N.inclusion_injective _).injOn)

/--
theorem `mk_eq_rank` / 定理 `mk_eq_rank`

English:
theorem mk_eq_rank
  given: (v : Basis ι R M)
  proof: by
  have := nontrivial_of_invariantBasisNumber R
  rw [← v.mk_range_eq_rank]; rw [Cardinal.mk_range_eq_of_injective v.injective]

中文:
定理 mk_eq_rank
  条件: (v : 基 ι R M)
  证明: by
  have := nontrivial_of_invariantBasisNumber R
  rw [← v.mk_range_eq_rank]; rw [Cardinal.mk_range_eq_of_injective v.injective]

Depends on / 依赖: Cardinal, Cardinal.mk_range_eq_of_injective, injective, mk_range_eq_of_injective, mk_range_eq_rank, nontrivial_of_invariantBasisNumber, v.injective, v.mk_range_eq_rank
-/
theorem mk_eq_rank (v : Basis ι R M) :
    Cardinal.lift.{v} #ι = Cardinal.lift.{w} (Module.rank R M) := by
  have := nontrivial_of_invariantBasisNumber R
  rw [← v.mk_range_eq_rank]; rw [Cardinal.mk_range_eq_of_injective v.injective]

/--
theorem `mk_eq_rank'.` / 定理 `mk_eq_rank'.`

English:
theorem mk_eq_rank'.{m}
  given: (v : Basis ι R M)
  proof: Cardinal.lift_umax_eq.{w, v, m}.mpr v.mk_eq_rank

中文:
定理 mk_eq_rank'.{m}
  条件: (v : 基 ι R M)
  证明: Cardinal.lift_umax_eq.{w, v, m}.mpr v.mk_eq_rank

Depends on / 依赖: Cardinal, Cardinal.lift_umax_eq, lift_umax_eq, mk_eq_rank, v.mk_eq_rank
-/
theorem mk_eq_rank'.{m} (v : Basis ι R M) :
    Cardinal.lift.{max v m} #ι = Cardinal.lift.{max w m} (Module.rank R M) :=
  Cardinal.lift_umax_eq.{w, v, m}.mpr v.mk_eq_rank

end Module.Basis

/--
theorem `rank_span` / 定理 `rank_span`

English:
theorem rank_span
  given: {v : ι -> M} (hv : LinearIndependent R v)
  proof: by
  have := nontrivial_of_invariantBasisNumber R
  rw [← Cardinal.lift_inj]; rw [← (Basis.span hv).mk_eq_rank]; rw [Cardinal.mk_range_eq_of_injective (@LinearIndependent.injective ι R M v _ _ _ _ hv)]

中文:
定理 rank_span
  条件: {v : ι -> M} (hv : LinearIndependent R v)
  证明: by
  have := nontrivial_of_invariantBasisNumber R
  rw [← Cardinal.lift_inj]; rw [← (Basis.span hv).mk_eq_rank]; rw [Cardinal.mk_range_eq_of_injective (@LinearIndependent.injective ι R M v _ _ _ _ hv)]

Depends on / 依赖: Basis.span, Cardinal, Cardinal.lift_inj, Cardinal.mk_range_eq_of_injective, LinearIndependent, LinearIndependent.injective, injective, lift_inj, mk_eq_rank, mk_range_eq_of_injective, nontrivial_of_invariantBasisNumber
-/
theorem rank_span {v : ι -> M} (hv : LinearIndependent R v) :
    Module.rank R ↑(span R (range v)) = #(range v) := by
  have := nontrivial_of_invariantBasisNumber R
  rw [← Cardinal.lift_inj]; rw [← (Basis.span hv).mk_eq_rank]; rw [Cardinal.mk_range_eq_of_injective (@LinearIndependent.injective ι R M v _ _ _ _ hv)]

/--
theorem `rank_span_set` / 定理 `rank_span_set`

English:
theorem rank_span_set
  given: {s : Set M} (hs : LinearIndepOn R id s)
  statement: Module.rank R ↑(span R s) = #s
  proof: by
  rw [← @ofPred_mem_eq _ s]; rw [← Subtype.range_coe_subtype]
  exact rank_span hs

中文:
定理 rank_span_set
  条件: {s : 集合 M} (hs : LinearIndepOn R id s)
  结论: 模.rank R ↑(span R s) = #s
  证明: by
  rw [← @ofPred_mem_eq _ s]; rw [← Subtype.range_coe_subtype]
  exact rank_span hs

Depends on / 依赖: Subtype, Subtype.range_coe_subtype, ofPred_mem_eq, range_coe_subtype, rank_span
-/
theorem rank_span_set {s : Set M} (hs : LinearIndepOn R id s) : Module.rank R ↑(span R s) = #s := by
  rw [← @ofPred_mem_eq _ s]; rw [← Subtype.range_coe_subtype]
  exact rank_span hs

/--
theorem `toENat_rank_span_set` / 定理 `toENat_rank_span_set`

English:
theorem toENat_rank_span_set
  given: {v : ι -> M} {s : Set ι} (hs : LinearIndepOn R v s)
  proof: by
  rw [image_eq_range]; rw [← hs.injOn.encard_image]; rw [← toENat_cardinalMk]; rw [image_eq_range]; rw [← rank_span hs.linearIndependent]

中文:
定理 toE自然数_rank_span_set
  条件: {v : ι -> M} {s : 集合 ι} (hs : LinearIndepOn R v s)
  证明: by
  rw [image_eq_range]; rw [← hs.injOn.encard_image]; rw [← toENat_cardinalMk]; rw [image_eq_range]; rw [← rank_span hs.linearIndependent]

Depends on / 依赖: encard_image, hs.injOn.encard_image, hs.linearIndependent, image_eq_range, linearIndependent, rank_span, toENat_cardinalMk
-/
theorem toENat_rank_span_set {v : ι -> M} {s : Set ι} (hs : LinearIndepOn R v s) :
    (Module.rank R <| span R <| v '' s).toENat = s.encard := by
  rw [image_eq_range]; rw [← hs.injOn.encard_image]; rw [← toENat_cardinalMk]; rw [image_eq_range]; rw [← rank_span hs.linearIndependent]

/--
Definition of `Submodule.inductionOnRank` / `Submodule.inductionOnRank` 的定义

English:
definition Submodule.inductionOnRank
  signature: {R M} [Ring R] [StrongRankCondition R] [AddCommGroup M] [Module R M]
  body: letI := Fintype.ofFinite ι
  Submodule.inductionOnRankAux b P ih (Fintype.card ι) N fun hs hli => by
    simpa using b.card_le_card_of_linearIndependent hli

中文:
定义 子模.inductionOnRank
  签名: {R M} [环 R] [StrongRankCondition R] [加法交换群 M] [模 R M]
  定义体: letI := Fintype.ofFinite ι
  Submodule.inductionOnRankAux b P ih (Fintype.card ι) N fun hs hli => by
    simpa using b.card_le_card_of_linearIndependent hli

Depends on / 依赖: Fintype, Fintype.card, Fintype.ofFinite, Submodule, Submodule.inductionOnRankAux, b.card_le_card_of_linearIndependent, card_le_card_of_linearIndependent, inductionOnRankAux, ofFinite
-/
def Submodule.inductionOnRank {R M} [Ring R] [StrongRankCondition R] [AddCommGroup M] [Module R M]
    [IsDomain R] [Finite ι] (b : Basis ι R M) (P : Submodule R M -> Sort*)
    (ih : forall N : Submodule R M,
      (forall N' <= N, forall x in N, (forall (c : R), forall y in N', c • x + y = (0 : M) -> c = 0) -> P N') -> P N)
    (N : Submodule R M) : P N :=
  letI := Fintype.ofFinite ι
  Submodule.inductionOnRankAux b P ih (Fintype.card ι) N fun hs hli => by
    simpa using b.card_le_card_of_linearIndependent hli

/--
theorem `Ideal.rank_eq` / 定理 `Ideal.rank_eq`

English:
theorem Ideal.rank_eq
  statement: {R S : Type*} [CommRing R] [StrongRankCondition R] [Ring S] [IsDomain S]
  proof: by
  obtain ⟨a, ha⟩ := Submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr hI)
  have : LinearIndependent R fun i => b i • a := by
    have hb := b.linearIndependent
    rw [Fintype.linearIndependent_iff] at hb ⊢
    intro g hg
    apply hb g
    simp only [← smul_assoc, ← Finset.sum_smul, smul_eq_zero] at hg
    exact hg.resolve_right ha
  exact le_antisymm
    (b.card_le_card_of_linearIndependent (c.linearIndependent.map' (Submodule.subtype I)
      ((LinearMap.ker_eq_bot (f := (Submodule.subtype I : I ->ₗ[R] S))).mpr Subtype.coe_injective)))
    (c.card_le_card_of_linearIndependent this)

中文:
定理 理想.rank_eq
  结论: {R S : 类型} [交换环 R] [StrongRankCondition R] [环 S] [是整环 S]
  证明: by
  obtain ⟨a, ha⟩ := Submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr hI)
  have : LinearIndependent R fun i => b i • a := by
    have hb := b.linearIndependent
    rw [Fintype.linearIndependent_iff] at hb ⊢
    intro g hg
    apply hb g
    simp only [← smul_assoc, ← Finset.sum_smul, smul_eq_zero] at hg
    exact hg.resolve_right ha
  exact le_antisymm
    (b.card_le_card_of_linearIndependent (c.linearIndependent.map' (Submodule.subtype I)
      ((LinearMap.ker_eq_bot (f := (Submodule.subtype I : I ->ₗ[R] S))).mpr Subtype.coe_injective)))
    (c.card_le_card_of_linearIndependent this)

Depends on / 依赖: Finset, Finset.sum_smul, Fintype, Fintype.linearIndependent_iff, LinearIndependent, LinearMap, LinearMap.ker_eq_bot, Submodule, Submodule.nonzero_mem_of_bot_lt, Submodule.subtype, Subtype, Subtype.coe, b.card_le_card_of_linearIndependent, b.linearIndependent, bot_lt_iff_ne_bot, bot_lt_iff_ne_bot.mpr, c.linearIndependent.map, card_le_card_of_linearIndependent, hg.resolve_right, ker_eq_bot
-/
theorem Ideal.rank_eq {R S : Type*} [CommRing R] [StrongRankCondition R] [Ring S] [IsDomain S]
    [Algebra R S] {n m : Type*} [Fintype n] [Fintype m] (b : Basis n R S) {I : Ideal S}
    (hI : I != ⊥) (c : Basis m R I) : Fintype.card m = Fintype.card n := by
  obtain ⟨a, ha⟩ := Submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr hI)
  have : LinearIndependent R fun i => b i • a := by
    have hb := b.linearIndependent
    rw [Fintype.linearIndependent_iff] at hb ⊢
    intro g hg
    apply hb g
    simp only [← smul_assoc, ← Finset.sum_smul, smul_eq_zero] at hg
    exact hg.resolve_right ha
  exact le_antisymm
    (b.card_le_card_of_linearIndependent (c.linearIndependent.map' (Submodule.subtype I)
      ((LinearMap.ker_eq_bot (f := (Submodule.subtype I : I ->ₗ[R] S))).mpr Subtype.coe_injective)))
    (c.card_le_card_of_linearIndependent this)

namespace Module

omit [StrongRankCondition R] in
/--
theorem `rank_pos_of_free` / 定理 `rank_pos_of_free`

English:
theorem rank_pos_of_free
  given: [Module.Free R M] [Nontrivial M]
  proof: have := Module.nontrivial R M
  (pos_of_ne_zero <| Cardinal.mk_ne_zero _).trans_le
    (Free.chooseBasis R M).linearIndependent.cardinal_le_rank

中文:
定理 rank_pos_of_free
  条件: [模.自由 R M] [非平凡 M]
  证明: have := Module.nontrivial R M
  (pos_of_ne_zero <| Cardinal.mk_ne_zero _).trans_le
    (Free.chooseBasis R M).linearIndependent.cardinal_le_rank

Depends on / 依赖: Cardinal, Cardinal.mk_ne_zero, Free.chooseBasis, Module, Module.nontrivial, cardinal_le_rank, chooseBasis, linearIndependent, linearIndependent.cardinal_le_rank, mk_ne_zero, nontrivial, pos_of_ne_zero, trans_le
-/
theorem rank_pos_of_free [Module.Free R M] [Nontrivial M] :
    0 < Module.rank R M :=
  have := Module.nontrivial R M
  (pos_of_ne_zero <| Cardinal.mk_ne_zero _).trans_le
    (Free.chooseBasis R M).linearIndependent.cardinal_le_rank

/--
theorem `rank_pos_iff_of_free` / 定理 `rank_pos_iff_of_free`

English:
theorem rank_pos_iff_of_free
  given: [Module.Free R M]
  proof: by
  refine ⟨fun h => ?_, fun _ => rank_pos_of_free⟩
  rw [← not_subsingleton_iff_nontrivial]
  intro h'
  simp only [rank_subsingleton', lt_self_iff_false] at h

中文:
定理 rank_pos_iff_of_free
  条件: [模.自由 R M]
  证明: by
  refine ⟨fun h => ?_, fun _ => rank_pos_of_free⟩
  rw [← not_subsingleton_iff_nontrivial]
  intro h'
  simp only [rank_subsingleton', lt_self_iff_false] at h

Depends on / 依赖: lt_self_iff_false, not_subsingleton_iff_nontrivial, rank_pos_of_free, rank_subsingleton
-/
theorem rank_pos_iff_of_free [Module.Free R M] :
    0 < Module.rank R M ↔ Nontrivial M := by
  refine ⟨fun h => ?_, fun _ => rank_pos_of_free⟩
  rw [← not_subsingleton_iff_nontrivial]
  intro h'
  simp only [rank_subsingleton', lt_self_iff_false] at h

/--
theorem `rank_zero_iff_of_free` / 定理 `rank_zero_iff_of_free`

English:
theorem rank_zero_iff_of_free
  given: [Module.Free R M]
  proof: by
  rw [← not_nontrivial_iff_subsingleton]; rw [iff_not_comm]; rw [← Module.rank_pos_iff_of_free (R := R)]; rw [pos_iff_ne_zero]

中文:
定理 rank_zero_iff_of_free
  条件: [模.自由 R M]
  证明: by
  rw [← not_nontrivial_iff_subsingleton]; rw [iff_not_comm]; rw [← Module.rank_pos_iff_of_free (R := R)]; rw [pos_iff_ne_zero]

Depends on / 依赖: Module, Module.rank_pos_iff_of_free, iff_not_comm, not_nontrivial_iff_subsingleton, pos_iff_ne_zero, rank_pos_iff_of_free
-/
theorem rank_zero_iff_of_free [Module.Free R M] :
    Module.rank R M = 0 ↔ Subsingleton M := by
  rw [← not_nontrivial_iff_subsingleton]; rw [iff_not_comm]; rw [← Module.rank_pos_iff_of_free (R := R)]; rw [pos_iff_ne_zero]

/--
theorem `finrank_eq_nat_card_basis` / 定理 `finrank_eq_nat_card_basis`

English:
theorem finrank_eq_nat_card_basis
  given: (h : Basis ι R M)
  proof: by
  rw [Nat.card]; rw [← toNat_lift.{v}]; rw [h.mk_eq_rank]; rw [toNat_lift]; rw [finrank]

中文:
定理 finrank_eq_nat_card_basis
  条件: (h : 基 ι R M)
  证明: by
  rw [Nat.card]; rw [← toNat_lift.{v}]; rw [h.mk_eq_rank]; rw [toNat_lift]; rw [finrank]

Depends on / 依赖: Nat.card, _eq_lintegral_enorm, eLpNorm, finrank, h.mk_eq_rank, hp0_lt, mk_eq_rank, toNat_lift
-/
theorem finrank_eq_nat_card_basis (h : Basis ι R M) :
    finrank R M = Nat.card ι := by
  rw [Nat.card]; rw [← toNat_lift.{v}]; rw [h.mk_eq_rank]; rw [toNat_lift]; rw [finrank]

/--
theorem `finrank_eq_card_basis` / 定理 `finrank_eq_card_basis`

English:
theorem finrank_eq_card_basis
  given: {ι : Type w} [Fintype ι] (h : Basis ι R M)
  proof: finrank_eq_of_rank_eq (rank_eq_card_basis h)

中文:
定理 finrank_eq_card_basis
  条件: {ι : 类型 w} [有限类型 ι] (h : 基 ι R M)
  证明: finrank_eq_of_rank_eq (rank_eq_card_basis h)

Depends on / 依赖: _eq_lintegral_enorm, _zero, eLpNorm, finrank_eq_of_rank_eq, hq0_ne, hq0_ne.symm, hq_neg, le_or_gt, lt_of_le_of_ne, rank_eq_card_basis
-/
theorem finrank_eq_card_basis {ι : Type w} [Fintype ι] (h : Basis ι R M) :
    finrank R M = Fintype.card ι :=
  finrank_eq_of_rank_eq (rank_eq_card_basis h)

/--
theorem `mk_finrank_eq_card_basis` / 定理 `mk_finrank_eq_card_basis`

English:
theorem mk_finrank_eq_card_basis
  given: [Module.Finite R M] {ι : Type w} (h : Basis ι R M)
  proof: by
  cases @nonempty_fintype _ (Module.Finite.finite_basis h)
  rw [Cardinal.mk_fintype]; rw [finrank_eq_card_basis h]

中文:
定理 mk_finrank_eq_card_basis
  条件: [模.有限 R M] {ι : 类型 w} (h : 基 ι R M)
  证明: by
  cases @nonempty_fintype _ (Module.Finite.finite_basis h)
  rw [Cardinal.mk_fintype]; rw [finrank_eq_card_basis h]

Depends on / 依赖: Cardinal, Cardinal.mk_fintype, Finite, Module, Module.Finite.finite_basis, finite_basis, finrank_eq_card_basis, mk_fintype, nonempty_fintype
-/
theorem mk_finrank_eq_card_basis [Module.Finite R M] {ι : Type w} (h : Basis ι R M) :
    (finrank R M : Cardinal.{w}) = #ι := by
  cases @nonempty_fintype _ (Module.Finite.finite_basis h)
  rw [Cardinal.mk_fintype]; rw [finrank_eq_card_basis h]

/--
theorem `finrank_eq_card_finset_basis` / 定理 `finrank_eq_card_finset_basis`

English:
theorem finrank_eq_card_finset_basis
  given: {ι : Type w} {b : Finset ι} (h : Basis b R M)
  proof: by rw [finrank_eq_card_basis h, Fintype.card_coe]

中文:
定理 finrank_eq_card_finset_basis
  条件: {ι : 类型 w} {b : 有限集 ι} (h : 基 b R M)
  证明: by rw [finrank_eq_card_basis h, Fintype.card_coe]

Depends on / 依赖: Fintype, Fintype.card_coe, card_coe, finrank_eq_card_basis
-/
theorem finrank_eq_card_finset_basis {ι : Type w} {b : Finset ι} (h : Basis b R M) :
    finrank R M = Finset.card b := by rw [finrank_eq_card_basis h, Fintype.card_coe]

variable (R)

@[simp]
/--
theorem `rank_self` / 定理 `rank_self`

English:
theorem rank_self
  statement: Module.rank R R = 1
  proof: by
  rw [← Cardinal.lift_inj]; rw [← (Basis.singleton PUnit R).mk_eq_rank]; rw [Cardinal.mk_punit]

中文:
定理 rank_self
  结论: 模.rank R R = 1
  证明: by
  rw [← Cardinal.lift_inj]; rw [← (Basis.singleton PUnit R).mk_eq_rank]; rw [Cardinal.mk_punit]

Depends on / 依赖: Basis.singleton, Cardinal, Cardinal.lift_inj, Cardinal.mk_punit, lift_inj, mk_eq_rank, mk_punit, singleton
-/
theorem rank_self : Module.rank R R = 1 := by
  rw [← Cardinal.lift_inj]; rw [← (Basis.singleton PUnit R).mk_eq_rank]; rw [Cardinal.mk_punit]

/-- A ring satisfying `StrongRankCondition` (such as a `DivisionRing`) is one-dimensional as a
module over itself. -/
@[simp]
/--
theorem `finrank_self` / 定理 `finrank_self`

English:
theorem finrank_self
  statement: finrank R R = 1
  proof: finrank_eq_of_rank_eq (by simp)

中文:
定理 finrank_self
  结论: finrank R R = 1
  证明: finrank_eq_of_rank_eq (by simp)

Depends on / 依赖: eLpNorm, finrank_eq_of_rank_eq, hq_pos
-/
theorem finrank_self : finrank R R = 1 :=
  finrank_eq_of_rank_eq (by simp)

variable {R} in
/--
theorem `finrank_of_bijective_toSpanSingleton` / 定理 `finrank_of_bijective_toSpanSingleton`

English:
theorem finrank_of_bijective_toSpanSingleton
  statement: {x : M}
  proof: by
  rw [← (LinearEquiv.ofBijective _ h).finrank_eq]; rw [finrank_self]

中文:
定理 finrank_of_bijective_toSpanSingleton
  结论: {x : M}
  证明: by
  rw [← (LinearEquiv.ofBijective _ h).finrank_eq]; rw [finrank_self]

Depends on / 依赖: LinearEquiv, LinearEquiv.ofBijective, eLpNorm, finrank_eq, finrank_self, ofBijective
-/
theorem finrank_of_bijective_toSpanSingleton {x : M}
    (h : Bijective (LinearMap.toSpanSingleton R M x)) : finrank R M = 1 := by
  rw [← (LinearEquiv.ofBijective _ h).finrank_eq]; rw [finrank_self]

variable {R} in
/--
theorem `rank_of_bijective_toSpanSingleton` / 定理 `rank_of_bijective_toSpanSingleton`

English:
theorem rank_of_bijective_toSpanSingleton
  statement: {x : M}
  proof: by
  rw [rank_eq_one_iff_finrank_eq_one]; rw [finrank_of_bijective_toSpanSingleton h]

中文:
定理 rank_of_bijective_toSpanSingleton
  结论: {x : M}
  证明: by
  rw [rank_eq_one_iff_finrank_eq_one]; rw [finrank_of_bijective_toSpanSingleton h]

Depends on / 依赖: eLpNorm, finrank_of_bijective_toSpanSingleton, hq_neg, rank_eq_one_iff_finrank_eq_one
-/
theorem rank_of_bijective_toSpanSingleton {x : M}
    (h : Bijective (LinearMap.toSpanSingleton R M x)) : Module.rank R M = 1 := by
  rw [rank_eq_one_iff_finrank_eq_one]; rw [finrank_of_bijective_toSpanSingleton h]

/--
theorem `finrank_of_bijective_algebraMap` / 定理 `finrank_of_bijective_algebraMap`

English:
theorem finrank_of_bijective_algebraMap
  statement: {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
  proof: by
  rw [← (AlgEquiv.ofBijective (Algebra.ofId R S) h).toLinearEquiv.finrank_eq]; rw [finrank_self]

中文:
定理 finrank_of_bijective_algebraMap
  结论: {R S : 类型} [交换半环 R] [半环 S] [代数 R S]
  证明: by
  rw [← (AlgEquiv.ofBijective (Algebra.ofId R S) h).toLinearEquiv.finrank_eq]; rw [finrank_self]

Depends on / 依赖: AlgEquiv, AlgEquiv.ofBijective, Algebra, Algebra.ofId, finrank_eq, finrank_self, ofBijective, toLinearEquiv, toLinearEquiv.finrank_eq
-/
theorem finrank_of_bijective_algebraMap {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    [StrongRankCondition R] (h : Bijective (algebraMap R S)) : finrank R S = 1 := by
  rw [← (AlgEquiv.ofBijective (Algebra.ofId R S) h).toLinearEquiv.finrank_eq]; rw [finrank_self]

/--
theorem `rank_of_bijective_algebraMap` / 定理 `rank_of_bijective_algebraMap`

English:
theorem rank_of_bijective_algebraMap
  statement: {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
  proof: by
  rw [rank_eq_one_iff_finrank_eq_one]; rw [finrank_of_bijective_algebraMap h]

中文:
定理 rank_of_bijective_algebraMap
  结论: {R S : 类型} [交换半环 R] [半环 S] [代数 R S]
  证明: by
  rw [rank_eq_one_iff_finrank_eq_one]; rw [finrank_of_bijective_algebraMap h]

Depends on / 依赖: finrank_of_bijective_algebraMap, rank_eq_one_iff_finrank_eq_one
-/
theorem rank_of_bijective_algebraMap {R S : Type*} [CommSemiring R] [Semiring S] [Algebra R S]
    [StrongRankCondition R] (h : Bijective (algebraMap R S)) : Module.rank R S = 1 := by
  rw [rank_eq_one_iff_finrank_eq_one]; rw [finrank_of_bijective_algebraMap h]

/-- Given a basis of a ring over itself indexed by a type `ι`, then `ι` is `Unique`. -/
@[instance_reducible]
/--
Definition of `_root_.Module.Basis.unique` / `_root_.Module.Basis.unique` 的定义

English:
definition _root_.Module.Basis.unique
  signature: {ι : Type*} (b : Basis ι R R)
  body: by
  have : Cardinal.mk ι = ↑(Module.finrank R R) := (Module.mk_finrank_eq_card_basis b).symm
  have : Subsingleton ι ∧ Nonempty ι := by simpa [Cardinal.eq_one_iff_unique]
  exact Nonempty.some ((unique_iff_subsingleton_and_nonempty _).2 this)

中文:
定义 _root_.模.基.unique
  签名: {ι : 类型} (b : 基 ι R R)
  定义体: by
  have : Cardinal.mk ι = ↑(Module.finrank R R) := (Module.mk_finrank_eq_card_basis b).symm
  have : Subsingleton ι ∧ Nonempty ι := by simpa [Cardinal.eq_one_iff_unique]
  exact Nonempty.some ((unique_iff_subsingleton_and_nonempty _).2 this)

Depends on / 依赖: Cardinal, Cardinal.eq_one_iff_unique, Cardinal.mk, Module, Module.finrank, Module.mk_finrank_eq_card_basis, Nonempty, Nonempty.some, Subsingleton, _eq_lintegral_enorm, eLpNorm, eq_one_iff_unique, finrank, mk_finrank_eq_card_basis, unique_iff_subsingleton_and_nonempty
-/
noncomputable def _root_.Module.Basis.unique {ι : Type*} (b : Basis ι R R) : Unique ι := by
  have : Cardinal.mk ι = ↑(Module.finrank R R) := (Module.mk_finrank_eq_card_basis b).symm
  have : Subsingleton ι ∧ Nonempty ι := by simpa [Cardinal.eq_one_iff_unique]
  exact Nonempty.some ((unique_iff_subsingleton_and_nonempty _).2 this)

variable (M)

/--
theorem `rank_lt_aleph0` / 定理 `rank_lt_aleph0`

English:
theorem rank_lt_aleph0
  given: [Module.Finite R M]
  statement: Module.rank R M < ℵ₀
  proof: by
  simp only [Module.rank_def]
  obtain ⟨S, hS⟩ := Module.finite_def.mp ‹_›
  exact (ciSup_le' fun i => linearIndependent_le_span_finset _ i.prop S hS).trans_lt
    natCast_lt_aleph0

中文:
定理 rank_lt_aleph0
  条件: [模.有限 R M]
  结论: 模.rank R M < ℵ₀
  证明: by
  simp only [Module.rank_def]
  obtain ⟨S, hS⟩ := Module.finite_def.mp ‹_›
  exact (ciSup_le' fun i => linearIndependent_le_span_finset _ i.prop S hS).trans_lt
    natCast_lt_aleph0

Depends on / 依赖: Module, Module.finite_def.mp, Module.rank_def, ciSup_le, finite_def, i.prop, linearIndependent_le_span_finset, natCast_lt_aleph0, rank_def, trans_lt
-/
theorem rank_lt_aleph0 [Module.Finite R M] : Module.rank R M < ℵ₀ := by
  simp only [Module.rank_def]
  obtain ⟨S, hS⟩ := Module.finite_def.mp ‹_›
  exact (ciSup_le' fun i => linearIndependent_le_span_finset _ i.prop S hS).trans_lt
    natCast_lt_aleph0

noncomputable instance {R M : Type*} [DivisionRing R] [AddCommGroup M] [Module R M]
    {s t : Set M} [Module.Finite R (span R t)]
    (hs : LinearIndepOn R id s) (hst : s subseteq t) :
    Fintype (hs.extend hst) := by
  refine Classical.choice (Cardinal.lt_aleph0_iff_fintype.1 ?_)
  rw [← rank_span_set (hs.linearIndepOn_extend hst)]; rw [hs.span_extend_eq_span]
  exact Module.rank_lt_aleph0 ..

/-- If `M` is finite, `finrank M = rank M`. -/
@[simp]
/--
theorem `finrank_eq_rank` / 定理 `finrank_eq_rank`

English:
theorem finrank_eq_rank
  given: [Module.Finite R M]
  statement: ↑(finrank R M) = Module.rank R M
  proof: by
  rw [Module.finrank]; rw [cast_toNat_of_lt_aleph0 (rank_lt_aleph0 R M)]

中文:
定理 finrank_eq_rank
  条件: [模.有限 R M]
  结论: ↑(finrank R M) = 模.rank R M
  证明: by
  rw [Module.finrank]; rw [cast_toNat_of_lt_aleph0 (rank_lt_aleph0 R M)]

Depends on / 依赖: Module, Module.finrank, cast_toNat_of_lt_aleph0, finrank, rank_lt_aleph0
-/
theorem finrank_eq_rank [Module.Finite R M] : ↑(finrank R M) = Module.rank R M := by
  rw [Module.finrank]; rw [cast_toNat_of_lt_aleph0 (rank_lt_aleph0 R M)]

/--
theorem `finrank_eq_zero_iff_of_free` / 定理 `finrank_eq_zero_iff_of_free`

English:
theorem finrank_eq_zero_iff_of_free
  given: [Module.Free R M] [Module.Finite R M]
  proof: by
  have := Module.rank_lt_aleph0 R M
  rw [← not_le] at this
  simp [Module.finrank, this, Module.rank_zero_iff_of_free]

@[nontriviality]

中文:
定理 finrank_eq_zero_iff_of_free
  条件: [模.自由 R M] [模.有限 R M]
  证明: by
  have := Module.rank_lt_aleph0 R M
  rw [← not_le] at this
  simp [Module.finrank, this, Module.rank_zero_iff_of_free]

@[nontriviality]

Depends on / 依赖: Module, Module.finrank, Module.rank_lt_aleph0, Module.rank_zero_iff_of_free, finrank, not_le, rank_lt_aleph0, rank_zero_iff_of_free
-/
theorem finrank_eq_zero_iff_of_free [Module.Free R M] [Module.Finite R M] :
    Module.finrank R M = 0 ↔ Subsingleton M := by
  have := Module.rank_lt_aleph0 R M
  rw [← not_le] at this
  simp [Module.finrank, this, Module.rank_zero_iff_of_free]

@[nontriviality]
/--
theorem `finrank_eq_zero_of_subsingleton` / 定理 `finrank_eq_zero_of_subsingleton`

English:
theorem finrank_eq_zero_of_subsingleton
  given: [Module.Free R M] [Subsingleton M]
  proof: (finrank_eq_zero_iff_of_free R M).mpr inferInstance

中文:
定理 finrank_eq_zero_of_subsingleton
  条件: [模.自由 R M] [子单例 M]
  证明: (finrank_eq_zero_iff_of_free R M).mpr inferInstance

Depends on / 依赖: finrank_eq_zero_iff_of_free
-/
theorem finrank_eq_zero_of_subsingleton [Module.Free R M] [Subsingleton M] :
    Module.finrank R M = 0 :=
  (finrank_eq_zero_iff_of_free R M).mpr inferInstance

/--
theorem `finrank_pos_iff_of_free` / 定理 `finrank_pos_iff_of_free`

English:
theorem finrank_pos_iff_of_free
  given: [Module.Free R M] [Module.Finite R M]
  proof: by
  rw [← not_subsingleton_iff_nontrivial]; rw [← iff_not_comm]
  simp [Module.finrank_eq_zero_iff_of_free]

中文:
定理 finrank_pos_iff_of_free
  条件: [模.自由 R M] [模.有限 R M]
  证明: by
  rw [← not_subsingleton_iff_nontrivial]; rw [← iff_not_comm]
  simp [Module.finrank_eq_zero_iff_of_free]

Depends on / 依赖: ENNReal, ENNReal.mul_rpow_of_nonneg, ENNReal.rpow_mul, ENNReal.rpow_one, Module, Module.finrank_eq_zero_iff_of_free, _eq_lintegral_enorm, eLpNorm, finrank_eq_zero_iff_of_free, hq_cancel, hq_pos, hq_pos.le, iff_not_comm, lintegral_const, mul_rpow_of_nonneg, ne_of_lt, not_subsingleton_iff_nontrivial, one_div, rpow_mul, rpow_one
-/
theorem finrank_pos_iff_of_free [Module.Free R M] [Module.Finite R M] :
    0 < Module.finrank R M ↔ Nontrivial M := by
  rw [← not_subsingleton_iff_nontrivial]; rw [← iff_not_comm]
  simp [Module.finrank_eq_zero_iff_of_free]

/--
theorem `_root_.Submodule.finrank_eq_rank` / 定理 `_root_.Submodule.finrank_eq_rank`

English:
theorem _root_.Submodule.finrank_eq_rank
  given: [Module.Finite R M] (N : Submodule R M)
  proof: by
  rw [finrank]; rw [Cardinal.cast_toNat_of_lt_aleph0]
  exact lt_of_le_of_lt (Submodule.rank_le N) (rank_lt_aleph0 R M)

中文:
定理 _root_.子模.finrank_eq_rank
  条件: [模.有限 R M] (N : 子模 R M)
  证明: by
  rw [finrank]; rw [Cardinal.cast_toNat_of_lt_aleph0]
  exact lt_of_le_of_lt (Submodule.rank_le N) (rank_lt_aleph0 R M)

Depends on / 依赖: ENNReal, ENNReal.mul_rpow_of_ne_top, ENNReal.rpow_mul, ENNReal.rpow_one, _eq_lintegral_enorm, eLpNorm, finiteness, hc_ne_zero, hp_cancel, hq_ne_zero, lintegral_const, mul_rpow_of_ne_top, one_div, rpow_mul, rpow_one
-/
protected theorem _root_.Submodule.finrank_eq_rank [Module.Finite R M] (N : Submodule R M) :
    finrank R N = Module.rank R N := by
  rw [finrank]; rw [Cardinal.cast_toNat_of_lt_aleph0]
  exact lt_of_le_of_lt (Submodule.rank_le N) (rank_lt_aleph0 R M)

end Module

variable {M'} [AddCommMonoid M'] [Module R M']

/--
theorem `LinearMap.finrank_le_finrank_of_injective` / 定理 `LinearMap.finrank_le_finrank_of_injective`

English:
theorem LinearMap.finrank_le_finrank_of_injective
  statement: [Module.Finite R M'] {f : M ->ₗ[R] M'}
  proof: finrank_le_finrank_of_rank_le_rank (lift_rank_le_of_injective _ hf) (rank_lt_aleph0 _ _)

中文:
定理 线性映射.finrank_le_finrank_of_injective
  结论: [模.有限 R M'] {f : M ->ₗ[R] M'}
  证明: finrank_le_finrank_of_rank_le_rank (lift_rank_le_of_injective _ hf) (rank_lt_aleph0 _ _)

Depends on / 依赖: finrank_le_finrank_of_rank_le_rank, lift_rank_le_of_injective, rank_lt_aleph0
-/
theorem LinearMap.finrank_le_finrank_of_injective [Module.Finite R M'] {f : M ->ₗ[R] M'}
    (hf : Function.Injective f) : finrank R M <= finrank R M' :=
  finrank_le_finrank_of_rank_le_rank (lift_rank_le_of_injective _ hf) (rank_lt_aleph0 _ _)

/--
theorem `LinearMap.finrank_le_finrank_of_surjective` / 定理 `LinearMap.finrank_le_finrank_of_surjective`

English:
theorem LinearMap.finrank_le_finrank_of_surjective
  statement: [Module.Finite R M] {f : M ->ₗ[R] M'}
  proof: finrank_le_finrank_of_rank_le_rank (lift_rank_le_of_surjective _ hf) (rank_lt_aleph0 _ _)

中文:
定理 线性映射.finrank_le_finrank_of_surjective
  结论: [模.有限 R M] {f : M ->ₗ[R] M'}
  证明: finrank_le_finrank_of_rank_le_rank (lift_rank_le_of_surjective _ hf) (rank_lt_aleph0 _ _)

Depends on / 依赖: _const, eLpNorm, finrank_le_finrank_of_rank_le_rank, hq_pos, lift_rank_le_of_surjective, measure_univ, rank_lt_aleph0
-/
theorem LinearMap.finrank_le_finrank_of_surjective [Module.Finite R M] {f : M ->ₗ[R] M'}
    (hf : Function.Surjective f) : Module.finrank R M' <= Module.finrank R M :=
  finrank_le_finrank_of_rank_le_rank (lift_rank_le_of_surjective _ hf) (rank_lt_aleph0 _ _)

/--
theorem `LinearMap.finrank_range_le` / 定理 `LinearMap.finrank_range_le`

English:
theorem LinearMap.finrank_range_le
  given: [Module.Finite R M] (f : M ->ₗ[R] M')
  proof: finrank_le_finrank_of_rank_le_rank (lift_rank_range_le f) (rank_lt_aleph0 _ _)

中文:
定理 线性映射.finrank_range_le
  条件: [模.有限 R M] (f : M ->ₗ[R] M')
  证明: finrank_le_finrank_of_rank_le_rank (lift_rank_range_le f) (rank_lt_aleph0 _ _)

Depends on / 依赖: finrank_le_finrank_of_rank_le_rank, lift_rank_range_le, rank_lt_aleph0
-/
theorem LinearMap.finrank_range_le [Module.Finite R M] (f : M ->ₗ[R] M') :
    finrank R (LinearMap.range f) <= finrank R M :=
  finrank_le_finrank_of_rank_le_rank (lift_rank_range_le f) (rank_lt_aleph0 _ _)

/--
theorem `LinearMap.finrank_le_of_isSMulRegular` / 定理 `LinearMap.finrank_le_of_isSMulRegular`

English:
theorem LinearMap.finrank_le_of_isSMulRegular
  statement: {S : Type*} [CommSemiring S] [Algebra S R]
  proof: by
  refine finrank_le_finrank_of_rank_le_rank (lift_le.mpr <| rank_le_of_isSMulRegular L L' hr h) ?_
  rw [← Module.finrank_eq_rank R L']
  exact natCast_lt_aleph0

中文:
定理 线性映射.finrank_le_of_isSMulRegular
  结论: {S : 类型} [交换半环 S] [代数 S R]
  证明: by
  refine finrank_le_finrank_of_rank_le_rank (lift_le.mpr <| rank_le_of_isSMulRegular L L' hr h) ?_
  rw [← Module.finrank_eq_rank R L']
  exact natCast_lt_aleph0

Depends on / 依赖: Module, Module.finrank_eq_rank, finrank_eq_rank, finrank_le_finrank_of_rank_le_rank, lift_le, lift_le.mpr, natCast_lt_aleph0, rank_le_of_isSMulRegular
-/
theorem LinearMap.finrank_le_of_isSMulRegular {S : Type*} [CommSemiring S] [Algebra S R]
    [Module S M] [IsScalarTower S R M] (L L' : Submodule R M) [Module.Finite R L'] {s : S}
    (hr : IsSMulRegular M s) (h : forall x in L, s • x in L') :
    Module.finrank R L <= Module.finrank R L' := by
  refine finrank_le_finrank_of_rank_le_rank (lift_le.mpr <| rank_le_of_isSMulRegular L L' hr h) ?_
  rw [← Module.finrank_eq_rank R L']
  exact natCast_lt_aleph0

variable (R S M) in
/--
lemma `Module.finrank_top_le_finrank_of_isScalarTower` / 引理 `Module.finrank_top_le_finrank_of_isScalarTower`

English:
lemma Module.finrank_top_le_finrank_of_isScalarTower
  statement: [Module.Finite R M] [Semiring S]
  proof: by
  rw [finrank]; rw [finrank]; rw [Cardinal.toNat_le_iff_le_of_lt_aleph0]
  · exact rank_top_le_rank_of_isScalarTower R S M
  · exact lt_of_le_of_lt (rank_top_le_rank_of_isScalarTower R S M) (Module.rank_lt_aleph0 R M)
  · exact Module.rank_lt_aleph0 _ _

中文:
引理 模.finrank_top_le_finrank_of_isScalarTower
  结论: [模.有限 R M] [半环 S]
  证明: by
  rw [finrank]; rw [finrank]; rw [Cardinal.toNat_le_iff_le_of_lt_aleph0]
  · exact rank_top_le_rank_of_isScalarTower R S M
  · exact lt_of_le_of_lt (rank_top_le_rank_of_isScalarTower R S M) (Module.rank_lt_aleph0 R M)
  · exact Module.rank_lt_aleph0 _ _

Depends on / 依赖: Cardinal, Cardinal.toNat_le_iff_le_of_lt_aleph0, Module, Module.rank_lt_aleph0, finrank, lt_of_le_of_lt, rank_lt_aleph0, rank_top_le_rank_of_isScalarTower, toNat_le_iff_le_of_lt_aleph0
-/
lemma Module.finrank_top_le_finrank_of_isScalarTower [Module.Finite R M] [Semiring S]
    [Module S M] [Module R S] [IsScalarTower R S S] [FaithfulSMul R S] [IsScalarTower R S M] :
    finrank S M <= finrank R M := by
  rw [finrank]; rw [finrank]; rw [Cardinal.toNat_le_iff_le_of_lt_aleph0]
  · exact rank_top_le_rank_of_isScalarTower R S M
  · exact lt_of_le_of_lt (rank_top_le_rank_of_isScalarTower R S M) (Module.rank_lt_aleph0 R M)
  · exact Module.rank_lt_aleph0 _ _

variable (R) in
/--
lemma `Module.finrank_bot_le_finrank_of_isScalarTower` / 引理 `Module.finrank_bot_le_finrank_of_isScalarTower`

English:
lemma Module.finrank_bot_le_finrank_of_isScalarTower
  statement: (S T : Type*) [Semiring S] [Semiring T]
  proof: finrank_le_finrank_of_rank_le_rank (lift_rank_bot_le_lift_rank_of_isScalarTower R S T)
    (Module.rank_lt_aleph0 _ _)

omit [StrongRankCondition R]

中文:
引理 模.finrank_bot_le_finrank_of_isScalarTower
  结论: (S T : 类型) [半环 S] [半环 T]
  证明: finrank_le_finrank_of_rank_le_rank (lift_rank_bot_le_lift_rank_of_isScalarTower R S T)
    (Module.rank_lt_aleph0 _ _)

omit [StrongRankCondition R]

Depends on / 依赖: Module, Module.rank_lt_aleph0, finrank_le_finrank_of_rank_le_rank, lift_rank_bot_le_lift_rank_of_isScalarTower, rank_lt_aleph0
-/
lemma Module.finrank_bot_le_finrank_of_isScalarTower (S T : Type*) [Semiring S] [Semiring T]
    [Module R T] [Module S T] [Module R S] [IsScalarTower R S T]
    [IsScalarTower S T T] [FaithfulSMul S T] [Module.Finite R T] :
    finrank R S <= finrank R T :=
  finrank_le_finrank_of_rank_le_rank (lift_rank_bot_le_lift_rank_of_isScalarTower R S T)
    (Module.rank_lt_aleph0 _ _)

omit [StrongRankCondition R]

/--
theorem `strongRankCondition_iff_forall_rank_lt_aleph0` / 定理 `strongRankCondition_iff_forall_rank_lt_aleph0`

English:
theorem strongRankCondition_iff_forall_rank_lt_aleph0
  given: [Nontrivial R]
  proof: (strongRankCondition_iff_succ R).trans not_iff_not.mp by
    push Not
    refine ⟨fun ⟨n, f, inj⟩ => ⟨n, ?_⟩, fun ⟨n, le⟩ =>
      ⟨n, le_rank_iff_exists_linearMap.mp (natCast_le_aleph0.trans le)⟩⟩
    have ⟨g, hg⟩ := f.exists_finsupp_nat_of_fin_fun_injective inj
    convert! (Finsupp.basisSingleOne.linearIndependent.map_injOn _ hg.injOn).cardinal_lift_le_rank
    simp

中文:
定理 strongRankCondition_iff_对任意_rank_lt_aleph0
  条件: [非平凡 R]
  证明: (strongRankCondition_iff_succ R).trans not_iff_not.mp by
    push Not
    refine ⟨fun ⟨n, f, inj⟩ => ⟨n, ?_⟩, fun ⟨n, le⟩ =>
      ⟨n, le_rank_iff_exists_linearMap.mp (natCast_le_aleph0.trans le)⟩⟩
    have ⟨g, hg⟩ := f.exists_finsupp_nat_of_fin_fun_injective inj
    convert! (Finsupp.basisSingleOne.linearIndependent.map_injOn _ hg.injOn).cardinal_lift_le_rank
    simp

Depends on / 依赖: Finsupp, Finsupp.basisSingleOne.linearIndependent.map_injOn, basisSingleOne, cardinal_lift_le_rank, convert, exists_finsupp_nat_of_fin_fun_injective, f.exists_finsupp_nat_of_fin_fun_injective, hg.injOn, le_rank_iff_exists_linearMap, le_rank_iff_exists_linearMap.mp, linearIndependent, map_injOn, natCast_le_aleph0, natCast_le_aleph0.trans, not_iff_not, not_iff_not.mp, strongRankCondition_iff_succ
-/
theorem strongRankCondition_iff_forall_rank_lt_aleph0 [Nontrivial R] :
    StrongRankCondition R ↔ forall n : Nat, Module.rank R (Fin n -> R) < ℵ₀ :=
(strongRankCondition_iff_succ R).trans not_iff_not.mp by
    push Not
    refine ⟨fun ⟨n, f, inj⟩ => ⟨n, ?_⟩, fun ⟨n, le⟩ =>
      ⟨n, le_rank_iff_exists_linearMap.mp (natCast_le_aleph0.trans le)⟩⟩
    have ⟨g, hg⟩ := f.exists_finsupp_nat_of_fin_fun_injective inj
    convert! (Finsupp.basisSingleOne.linearIndependent.map_injOn _ hg.injOn).cardinal_lift_le_rank
    simp

/--
theorem `strongRankCondition_iff_forall_zero_lt_finrank` / 定理 `strongRankCondition_iff_forall_zero_lt_finrank`

English:
theorem strongRankCondition_iff_forall_zero_lt_finrank
  given: [Nontrivial R]
  proof: by
  rw [strongRankCondition_iff_forall_rank_lt_aleph0]; rw [← not_iff_not]
  push Not
  simp_rw [finrank, Nat.le_zero, toNat_eq_zero]
  refine ⟨fun ⟨n, le⟩ => ⟨n + 1, n.succ_pos, ?_⟩, fun ⟨n, pos, eq⟩ => ⟨n, ?_⟩⟩
· exact .inr le.trans LinearMap.rank_le_of_injective
(ExtendByZero.linearMap R _) extend_injective (Fin.castSucc_injective n) _
  · rw [or_iff_not_imp_left, ← Ne, ← Cardinal.one_le_iff_ne_zero, one_le_rank_iff] at eq
    rw [← n.succ_pred_eq_of_pos pos] at eq ⊢
    exact eq ⟨.single R (fun _ => _) 0, Pi.single_injective (M := fun _ => _) _⟩

中文:
定理 strongRankCondition_iff_对任意_zero_lt_finrank
  条件: [非平凡 R]
  证明: by
  rw [strongRankCondition_iff_forall_rank_lt_aleph0]; rw [← not_iff_not]
  push Not
  simp_rw [finrank, Nat.le_zero, toNat_eq_zero]
  refine ⟨fun ⟨n, le⟩ => ⟨n + 1, n.succ_pos, ?_⟩, fun ⟨n, pos, eq⟩ => ⟨n, ?_⟩⟩
· exact .inr le.trans LinearMap.rank_le_of_injective
(ExtendByZero.linearMap R _) extend_injective (Fin.castSucc_injective n) _
  · rw [or_iff_not_imp_left, ← Ne, ← Cardinal.one_le_iff_ne_zero, one_le_rank_iff] at eq
    rw [← n.succ_pred_eq_of_pos pos] at eq ⊢
    exact eq ⟨.single R (fun _ => _) 0, Pi.single_injective (M := fun _ => _) _⟩

Depends on / 依赖: Cardinal, Cardinal.one_le_iff_ne_zero, ExtendByZero, ExtendByZero.linearMap, Fin.castSucc_injective, LinearMap, LinearMap.rank_le_of_injective, Nat.le_zero, castSucc_injective, extend_injective, finrank, le.trans, le_zero, linearMap, n.succ_pos, n.succ_pred_eq_of_pos, not_iff_not, one_le_iff_ne_zero, one_le_rank_iff, or_iff_not_imp_left
-/
theorem strongRankCondition_iff_forall_zero_lt_finrank [Nontrivial R] :
    StrongRankCondition R ↔ forall n > 0, 0 < finrank R (Fin n -> R) := by
  rw [strongRankCondition_iff_forall_rank_lt_aleph0]; rw [← not_iff_not]
  push Not
  simp_rw [finrank, Nat.le_zero, toNat_eq_zero]
  refine ⟨fun ⟨n, le⟩ => ⟨n + 1, n.succ_pos, ?_⟩, fun ⟨n, pos, eq⟩ => ⟨n, ?_⟩⟩
· exact .inr le.trans LinearMap.rank_le_of_injective
(ExtendByZero.linearMap R _) extend_injective (Fin.castSucc_injective n) _
  · rw [or_iff_not_imp_left, ← Ne, ← Cardinal.one_le_iff_ne_zero, one_le_rank_iff] at eq
    rw [← n.succ_pred_eq_of_pos pos] at eq ⊢
    exact eq ⟨.single R (fun _ => _) 0, Pi.single_injective (M := fun _ => _) _⟩

/--
theorem `StrongRankCondition.of_isNoetherian` / 定理 `StrongRankCondition.of_isNoetherian`

English:
theorem StrongRankCondition.of_isNoetherian
  given: [Nontrivial R] [forall n, IsNoetherian R (Fin n -> R)]
  proof: (strongRankCondition_iff_succ R).2 fun n f hf =>
    have e := LinearEquiv.piCongrLeft R (fun _ => R) (finSuccEquiv n) ≪≫ₗ .piOptionEquivProd _
not_subsingleton R IsNoetherian.subsingleton_of_injective
      (f := f ∘ₗ e.symm.toLinearMap) (hf.comp e.symm.injective)

中文:
定理 StrongRankCondition.of_isNoetherian
  条件: [非平凡 R] [对任意 n, 是Noether R (有限集 n -> R)]
  证明: (strongRankCondition_iff_succ R).2 fun n f hf =>
    have e := LinearEquiv.piCongrLeft R (fun _ => R) (finSuccEquiv n) ≪≫ₗ .piOptionEquivProd _
not_subsingleton R IsNoetherian.subsingleton_of_injective
      (f := f ∘ₗ e.symm.toLinearMap) (hf.comp e.symm.injective)

Depends on / 依赖: IsNoetherian, IsNoetherian.subsingleton_of_injective, LinearEquiv, LinearEquiv.piCongrLeft, e.symm.injective, e.symm.toLinearMap, finSuccEquiv, hf.comp, injective, not_subsingleton, piCongrLeft, piOptionEquivProd, strongRankCondition_iff_succ, subsingleton_of_injective, toLinearMap
-/
theorem StrongRankCondition.of_isNoetherian [Nontrivial R] [forall n, IsNoetherian R (Fin n -> R)] :
    StrongRankCondition R :=
  (strongRankCondition_iff_succ R).2 fun n f hf =>
    have e := LinearEquiv.piCongrLeft R (fun _ => R) (finSuccEquiv n) ≪≫ₗ .piOptionEquivProd _
not_subsingleton R IsNoetherian.subsingleton_of_injective
      (f := f ∘ₗ e.symm.toLinearMap) (hf.comp e.symm.injective)

end StrongRankCondition

namespace Submodule

variable {K M : Type*} [DivisionRing K] [AddCommGroup M] [Module K M] {s : Set M} {x : M}
  [Module.Finite K (span K s)]

variable (K s) in
/--
theorem `exists_finset_span_eq_linearIndepOn` / 定理 `exists_finset_span_eq_linearIndepOn`

English:
theorem exists_finset_span_eq_linearIndepOn
  proof: by
  rcases exists_linearIndependent K s with ⟨t, ht_sub, ht_span, ht_indep⟩
  obtain ⟨t, rfl, ht_card⟩ : exists u : Finset M, ↑u = t ∧ u.card = finrank K (span K s) := by
    rw [← Cardinal.mk_set_eq_nat_iff_finset]; rw [finrank_eq_rank]; rw [← ht_span]; rw [rank_span_set ht_indep]
  exact ⟨t, ht_sub, ht_card, ht_span, ht_indep⟩

中文:
定理 存在_finset_span_eq_linearIndepOn
  证明: by
  rcases exists_linearIndependent K s with ⟨t, ht_sub, ht_span, ht_indep⟩
  obtain ⟨t, rfl, ht_card⟩ : exists u : Finset M, ↑u = t ∧ u.card = finrank K (span K s) := by
    rw [← Cardinal.mk_set_eq_nat_iff_finset]; rw [finrank_eq_rank]; rw [← ht_span]; rw [rank_span_set ht_indep]
  exact ⟨t, ht_sub, ht_card, ht_span, ht_indep⟩

Depends on / 依赖: Cardinal, Cardinal.mk_set_eq_nat_iff_finset, Finset, exists_linearIndependent, finrank, finrank_eq_rank, ht_card, ht_indep, ht_span, ht_sub, mk_set_eq_nat_iff_finset, rank_span_set, u.card
-/
theorem exists_finset_span_eq_linearIndepOn :
    exists t : Finset M, ↑t subseteq s ∧ t.card = finrank K (span K s) ∧
      span K t = span K s ∧ LinearIndepOn K id (t : Set M) := by
  rcases exists_linearIndependent K s with ⟨t, ht_sub, ht_span, ht_indep⟩
  obtain ⟨t, rfl, ht_card⟩ : exists u : Finset M, ↑u = t ∧ u.card = finrank K (span K s) := by
    rw [← Cardinal.mk_set_eq_nat_iff_finset]; rw [finrank_eq_rank]; rw [← ht_span]; rw [rank_span_set ht_indep]
  exact ⟨t, ht_sub, ht_card, ht_span, ht_indep⟩

variable (K s) in
/--
theorem `exists_fun_fin_finrank_span_eq` / 定理 `exists_fun_fin_finrank_span_eq`

English:
theorem exists_fun_fin_finrank_span_eq
  proof: by
  rcases exists_finset_span_eq_linearIndepOn K s with ⟨t, hts, ht_card, ht_span, ht_indep⟩
  set e := (Finset.equivFinOfCardEq ht_card).symm
  exact ⟨(↑) ∘ e, fun i => hts (e i).2, by simpa, ht_indep.comp _ e.injective⟩

中文:
定理 存在_fun_fin_finrank_span_eq
  证明: by
  rcases exists_finset_span_eq_linearIndepOn K s with ⟨t, hts, ht_card, ht_span, ht_indep⟩
  set e := (Finset.equivFinOfCardEq ht_card).symm
  exact ⟨(↑) ∘ e, fun i => hts (e i).2, by simpa, ht_indep.comp _ e.injective⟩

Depends on / 依赖: Finset, Finset.equivFinOfCardEq, e.injective, equivFinOfCardEq, exists_finset_span_eq_linearIndepOn, ht_card, ht_indep, ht_indep.comp, ht_span, injective
-/
theorem exists_fun_fin_finrank_span_eq :
    exists f : Fin (finrank K (span K s)) -> M, (forall i, f i in s) ∧ span K (range f) = span K s ∧
      LinearIndependent K f := by
  rcases exists_finset_span_eq_linearIndepOn K s with ⟨t, hts, ht_card, ht_span, ht_indep⟩
  set e := (Finset.equivFinOfCardEq ht_card).symm
  exact ⟨(↑) ∘ e, fun i => hts (e i).2, by simpa, ht_indep.comp _ e.injective⟩

/--
theorem `mem_span_set_iff_exists_finsupp_le_finrank` / 定理 `mem_span_set_iff_exists_finsupp_le_finrank`

English:
theorem mem_span_set_iff_exists_finsupp_le_finrank
  proof: by
  constructor
  · intro h
    rcases exists_finset_span_eq_linearIndepOn K s with ⟨t, ht_sub, ht_card, ht_span, ht_indep⟩
    rcases mem_span_set.mp (ht_span ▸ h) with ⟨c, hct, hx⟩
    refine ⟨c, ?_, hct.trans ht_sub, hx⟩
    exact ht_card ▸ Finset.card_mono hct
  · rintro ⟨c, -, hcs, hx⟩
    exact mem_span_set.mpr ⟨c, hcs, hx⟩

中文:
定理 mem_span_set_iff_存在_finsupp_le_finrank
  证明: by
  constructor
  · intro h
    rcases exists_finset_span_eq_linearIndepOn K s with ⟨t, ht_sub, ht_card, ht_span, ht_indep⟩
    rcases mem_span_set.mp (ht_span ▸ h) with ⟨c, hct, hx⟩
    refine ⟨c, ?_, hct.trans ht_sub, hx⟩
    exact ht_card ▸ Finset.card_mono hct
  · rintro ⟨c, -, hcs, hx⟩
    exact mem_span_set.mpr ⟨c, hcs, hx⟩

Depends on / 依赖: Finset, Finset.card_mono, card_mono, exists_finset_span_eq_linearIndepOn, hct.trans, ht_card, ht_indep, ht_span, ht_sub, mem_span_set, mem_span_set.mp, mem_span_set.mpr
-/
theorem mem_span_set_iff_exists_finsupp_le_finrank :
    x in span K s ↔ exists c : M ->₀ K, c.support.card <= finrank K (span K s) ∧
      ↑c.support subseteq s ∧ c.sum (fun mi r => r • mi) = x := by
  constructor
  · intro h
    rcases exists_finset_span_eq_linearIndepOn K s with ⟨t, ht_sub, ht_card, ht_span, ht_indep⟩
    rcases mem_span_set.mp (ht_span ▸ h) with ⟨c, hct, hx⟩
    refine ⟨c, ?_, hct.trans ht_sub, hx⟩
    exact ht_card ▸ Finset.card_mono hct
  · rintro ⟨c, -, hcs, hx⟩
    exact mem_span_set.mpr ⟨c, hcs, hx⟩

end Submodule

namespace Algebra

-- TODO. use this in connection with `NumberTheory.Zsqrtd`
/--
Definition of `IsQuadraticExtension` / `IsQuadraticExtension` 的定义

English:
class IsQuadraticExtension
  parameters: (R S : Type*) [CommSemiring R] [StrongRankCondition R] [Semiring S]
  extends: Module.Free R S
  axioms and operations (1):
    - finrank_eq_two' : Module.finrank R S = 2

中文:
类 是QuadraticExtension
  参数: (R S : 类型) [交换半环 R] [StrongRankCondition R] [半环 S]
  继承: 模.自由 R S
  公理与运算 (1 个):
    - finrank_eq_two' : 模.finrank R S = 2

Depends on / 依赖: _eq_lintegral_enorm, eLpNorm, h.mono, lintegral_mono_ae
-/
class IsQuadraticExtension (R S : Type*) [CommSemiring R] [StrongRankCondition R] [Semiring S]
    [Algebra R S] extends Module.Free R S where
  finrank_eq_two' : Module.finrank R S = 2

/--
theorem `IsQuadraticExtension.finrank_eq_two` / 定理 `IsQuadraticExtension.finrank_eq_two`

English:
theorem IsQuadraticExtension.finrank_eq_two
  statement: (R S : Type*) [CommSemiring R] [StrongRankCondition R]
  proof: finrank_eq_two'

中文:
定理 是QuadraticExtension.finrank_eq_two
  结论: (R S : 类型) [交换半环 R] [StrongRankCondition R]
  证明: finrank_eq_two'

Depends on / 依赖: ENNReal, ENNReal.coe_le_coe.mpr, _mono_enorm_ae, coe_le_coe, eLpNorm, finrank_eq_two, h.mono
-/
theorem IsQuadraticExtension.finrank_eq_two (R S : Type*) [CommSemiring R] [StrongRankCondition R]
    [Semiring S] [Algebra R S] [IsQuadraticExtension R S] :
    Module.finrank R S = 2 := finrank_eq_two'

end Algebra
