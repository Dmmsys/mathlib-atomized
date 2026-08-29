/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IsAlgClosed.Classification
public import Mathlib.ModelTheory.Algebra.Field.CharP
public import Mathlib.ModelTheory.Satisfiability

/-!

# The First-Order Theory of Algebraically Closed Fields

This file defines the theory of algebraically closed fields of characteristic `p`, as well
as proving completeness of the theory and the Lefschetz Principle.

## Main definitions

* `FirstOrder.Language.Theory.ACF p` : the theory of algebraically closed fields of characteristic
  `p` as a theory over the language of rings.
* `FirstOrder.Field.ACF_isComplete` : the theory of algebraically closed fields of characteristic
  `p` is complete whenever `p` is prime or zero.
* `FirstOrder.Field.ACF_zero_realize_iff_infinite_ACF_prime_realize` : the Lefschetz principle.

## Implementation details

To apply a theorem about the model theory of algebraically closed fields to a specific
algebraically closed field `K` which does not have a `Language.ring.Structure` instance,
you must introduce the local instance `compatibleRingOfRing K`. Theorems whose statement requires
both a `Language.ring.Structure` instance and a `Field` instance will all be stated with the
assumption `Field K`, `CharP K p`, `IsAlgClosed K` and `CompatibleRing K` and there are instances
defined saying that these assumptions imply `Theory.field.Model K` and `(Theory.ACF p).Model K`

## References

The first-order theory of algebraically closed fields, along with the Lefschetz Principle and
the Ax-Grothendieck Theorem were first formalized in Lean 3 by Joseph Hua
[here](https://github.com/Jlh18/ModelTheoryInLean8) with the master's thesis
[here](https://github.com/Jlh18/ModelTheory8Report)

-/

@[expose] public section

variable {K : Type*}

namespace FirstOrder

namespace Field

open FirstOrder.Ring FreeCommRing Polynomial Language

/--
Definition of `genericMonicPoly` / `genericMonicPoly` 的定义

English:
definition genericMonicPoly
  signature: (n : Nat)
  body: of (Fin.last _) ^ n + ∑ i : Fin n, of i.castSucc * of (Fin.last _) ^ (i : Nat)

中文:
定义 genericMonicPoly
  签名: (n : 自然数)
  定义体: of (Fin.last _) ^ n + ∑ i : Fin n, of i.castSucc * of (Fin.last _) ^ (i : Nat)

Depends on / 依赖: Fin.last, castSucc, i.castSucc
-/
noncomputable def genericMonicPoly (n : Nat) : FreeCommRing (Fin (n + 1)) :=
  of (Fin.last _) ^ n + ∑ i : Fin n, of i.castSucc * of (Fin.last _) ^ (i : Nat)

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `lift_genericMonicPoly` / 定理 `lift_genericMonicPoly`

English:
theorem lift_genericMonicPoly
  given: [CommRing K] [Nontrivial K] {n : Nat} (v : Fin (n + 1) -> K)
  proof: by
  simp [genericMonicPoly, monicEquivDegreeLT, degreeLTEquiv, eval_finsetSum]

中文:
定理 lift_genericMonicPoly
  条件: [交换环 K] [非平凡 K] {n : 自然数} (v : 有限集 (n + 1) -> K)
  证明: by
  simp [genericMonicPoly, monicEquivDegreeLT, degreeLTEquiv, eval_finsetSum]

Depends on / 依赖: degreeLTEquiv, eval_finsetSum, genericMonicPoly, monicEquivDegreeLT
-/
theorem lift_genericMonicPoly [CommRing K] [Nontrivial K] {n : Nat} (v : Fin (n + 1) -> K) :
    FreeCommRing.lift v (genericMonicPoly n) =
    (((monicEquivDegreeLT n).trans (degreeLTEquiv K n).toEquiv).symm (v ∘ Fin.castSucc)).1.eval
      (v (Fin.last _)) := by
  simp [genericMonicPoly, monicEquivDegreeLT, degreeLTEquiv, eval_finsetSum]

/--
Definition of `genericMonicPolyHasRoot` / `genericMonicPolyHasRoot` 的定义

English:
definition genericMonicPolyHasRoot
  signature: (n : Nat)
  body: (exists' ((termOfFreeCommRing (genericMonicPoly n)).relabel Sum.inr =' 0)).alls

中文:
定义 genericMonicPolyHasRoot
  签名: (n : 自然数)
  定义体: (exists' ((termOfFreeCommRing (genericMonicPoly n)).relabel Sum.inr =' 0)).alls

Depends on / 依赖: Sum.inr, genericMonicPoly, relabel, termOfFreeCommRing
-/
noncomputable def genericMonicPolyHasRoot (n : Nat) : Language.ring.Sentence :=
  (exists' ((termOfFreeCommRing (genericMonicPoly n)).relabel Sum.inr =' 0)).alls

/--
theorem `realize_genericMonicPolyHasRoot` / 定理 `realize_genericMonicPolyHasRoot`

English:
theorem realize_genericMonicPolyHasRoot
  given: [Field K] [CompatibleRing K] (n : Nat)
  proof: by
  rw [Equiv.forall_congr_left ((monicEquivDegreeLT n).trans (degreeLTEquiv K n).toEquiv)]
  simp [Sentence.Realize, genericMonicPolyHasRoot, lift_genericMonicPoly]

中文:
定理 realize_genericMonicPolyHasRoot
  条件: [域 K] [余mpatible环 K] (n : 自然数)
  证明: by
  rw [Equiv.forall_congr_left ((monicEquivDegreeLT n).trans (degreeLTEquiv K n).toEquiv)]
  simp [Sentence.Realize, genericMonicPolyHasRoot, lift_genericMonicPoly]

Depends on / 依赖: Equiv.forall_congr_left, Realize, Sentence, Sentence.Realize, degreeLTEquiv, forall_congr_left, genericMonicPolyHasRoot, lift_genericMonicPoly, monicEquivDegreeLT, toEquiv
-/
theorem realize_genericMonicPolyHasRoot [Field K] [CompatibleRing K] (n : Nat) :
    K ⊨ genericMonicPolyHasRoot n ↔
      forall p : { p : K[X] // p.Monic ∧ p.natDegree = n }, exists x, p.1.eval x = 0 := by
  rw [Equiv.forall_congr_left ((monicEquivDegreeLT n).trans (degreeLTEquiv K n).toEquiv)]
  simp [Sentence.Realize, genericMonicPolyHasRoot, lift_genericMonicPoly]

-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `_root_.FirstOrder.Language.Theory.ACF` / `_root_.FirstOrder.Language.Theory.ACF` 的定义

English:
definition _root_.FirstOrder.Language.Theory.ACF
  signature: (p : Nat)
  body: Theory.fieldOfChar p union genericMonicPolyHasRoot '' {n | 0 < n}

中文:
定义 _root_.FirstOrder.Language.Theory.ACF
  签名: (p : 自然数)
  定义体: Theory.fieldOfChar p union genericMonicPolyHasRoot '' {n | 0 < n}

Depends on / 依赖: Theory, Theory.fieldOfChar, fieldOfChar, genericMonicPolyHasRoot
-/
noncomputable def _root_.FirstOrder.Language.Theory.ACF (p : Nat) : Theory .ring :=
  Theory.fieldOfChar p union genericMonicPolyHasRoot '' {n | 0 < n}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Language.ring.Structure
  signature: K] (p
  body: Theory.Model.mono h Set.subset_union_left

中文:
实例 [Language.ring.结构
  签名: K] (p
  定义体: Theory.Model.mono h Set.subset_union_left

Depends on / 依赖: Set.subset_union_left, Theory, Theory.Model.mono, subset_union_left
-/
instance [Language.ring.Structure K] (p : Nat) [h : (Theory.ACF p).Model K] :
    (Theory.fieldOfChar p).Model K :=
  Theory.Model.mono h Set.subset_union_left

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Field
  signature: K] [CompatibleRing K] {p
  body: by
  refine Theory.model_union_iff.2 ⟨inferInstance, ?_⟩
  simp only [Theory.model_iff, Set.mem_image,
    forall_exists_index, and_imp]
  rintro _ n hn0 rfl
  simp only [realize_genericMonicPolyHasRoot]
  rintro ⟨p, _, rfl⟩
  exact IsAlgClosed.exists_root p (ne_of_gt
    (natDegree_pos_iff_degree_pos.1 hn0))

中文:
实例 [域
  签名: K] [余mpatible环 K] {p
  定义体: by
  refine Theory.model_union_iff.2 ⟨inferInstance, ?_⟩
  simp only [Theory.model_iff, Set.mem_image,
    forall_exists_index, and_imp]
  rintro _ n hn0 rfl
  simp only [realize_genericMonicPolyHasRoot]
  rintro ⟨p, _, rfl⟩
  exact IsAlgClosed.exists_root p (ne_of_gt
    (natDegree_pos_iff_degree_pos.1 hn0))

Depends on / 依赖: IsAlgClosed, IsAlgClosed.exists_root, Set.mem_image, Theory, Theory.model_iff, Theory.model_union_iff, and_imp, exists_root, forall_exists_index, mem_image, model_iff, model_union_iff, natDegree_pos_iff_degree_pos, ne_of_gt, realize_genericMonicPolyHasRoot
-/
instance [Field K] [CompatibleRing K] {p : Nat} [CharP K p] [IsAlgClosed K] :
    (Theory.ACF p).Model K := by
  refine Theory.model_union_iff.2 ⟨inferInstance, ?_⟩
  simp only [Theory.model_iff, Set.mem_image,
    forall_exists_index, and_imp]
  rintro _ n hn0 rfl
  simp only [realize_genericMonicPolyHasRoot]
  rintro ⟨p, _, rfl⟩
  exact IsAlgClosed.exists_root p (ne_of_gt
    (natDegree_pos_iff_degree_pos.1 hn0))

/--
theorem `modelField_of_modelACF` / 定理 `modelField_of_modelACF`

English:
theorem modelField_of_modelACF
  statement: (p : Nat) (K : Type*) [Language.ring.Structure K]
  proof: Theory.Model.mono h (Set.subset_union_of_subset_left Set.subset_union_left _)

中文:
定理 modelField_of_modelACF
  结论: (p : 自然数) (K : 类型) [Language.ring.结构 K]
  证明: Theory.Model.mono h (Set.subset_union_of_subset_left Set.subset_union_left _)

Depends on / 依赖: Set.subset_union_left, Set.subset_union_of_subset_left, Theory, Theory.Model.mono, subset_union_left, subset_union_of_subset_left
-/
theorem modelField_of_modelACF (p : Nat) (K : Type*) [Language.ring.Structure K]
    [h : (Theory.ACF p).Model K] : Theory.field.Model K :=
  Theory.Model.mono h (Set.subset_union_of_subset_left Set.subset_union_left _)

/-- A model for the Theory of algebraically closed fields is a Field. After introducing
this as a local instance on a particular Type, you should usually also introduce
`modelField_of_modelACF p M`, `compatibleRingOfModelField` and `isAlgClosed_of_model_ACF` -/
@[reducible]
/--
Definition of `fieldOfModelACF` / `fieldOfModelACF` 的定义

English:
definition fieldOfModelACF
  signature: (p : Nat) (K : Type*)
  body: by
  have := modelField_of_modelACF p K
  exact fieldOfModelField K

中文:
定义 fieldOfModelACF
  签名: (p : 自然数) (K : 类型)
  定义体: by
  have := modelField_of_modelACF p K
  exact fieldOfModelField K

Depends on / 依赖: fieldOfModelField, modelField_of_modelACF
-/
noncomputable def fieldOfModelACF (p : Nat) (K : Type*)
    [Language.ring.Structure K]
    [h : (Theory.ACF p).Model K] : Field K := by
  have := modelField_of_modelACF p K
  exact fieldOfModelField K

/--
theorem `isAlgClosed_of_model_ACF` / 定理 `isAlgClosed_of_model_ACF`

English:
theorem isAlgClosed_of_model_ACF
  statement: (p : Nat) (K : Type*)
  proof: by
  refine IsAlgClosed.of_exists_root _ ?_
  intro p hpm hpi
  have h : K ⊨ genericMonicPolyHasRoot '' {n | 0 < n} :=
    Theory.Model.mono h (by simp [Theory.ACF])
  simp only [Theory.model_iff, Set.mem_image,
    forall_exists_index, and_imp] at h
  have := h _ p.natDegree (natDegree_pos_iff_degree_pos.2
    (degree_pos_of_irreducible hpi)) rfl
  rw [realize_genericMonicPolyHasRoot] at this
  exact this ⟨_, hpm, rfl⟩

中文:
定理 isAlgClosed_of_model_ACF
  结论: (p : 自然数) (K : 类型)
  证明: by
  refine IsAlgClosed.of_exists_root _ ?_
  intro p hpm hpi
  have h : K ⊨ genericMonicPolyHasRoot '' {n | 0 < n} :=
    Theory.Model.mono h (by simp [Theory.ACF])
  simp only [Theory.model_iff, Set.mem_image,
    forall_exists_index, and_imp] at h
  have := h _ p.natDegree (natDegree_pos_iff_degree_pos.2
    (degree_pos_of_irreducible hpi)) rfl
  rw [realize_genericMonicPolyHasRoot] at this
  exact this ⟨_, hpm, rfl⟩

Depends on / 依赖: IsAlgClosed, IsAlgClosed.of_exists_root, Set.mem_image, Theory, Theory.ACF, Theory.Model.mono, Theory.model_iff, and_imp, degree_pos_of_irreducible, forall_exists_index, genericMonicPolyHasRoot, mem_image, model_iff, natDegree, natDegree_pos_iff_degree_pos, of_exists_root, p.natDegree, realize_genericMonicPolyHasRoot
-/
theorem isAlgClosed_of_model_ACF (p : Nat) (K : Type*)
    [Field K] [CompatibleRing K] [h : (Theory.ACF p).Model K] :
    IsAlgClosed K := by
  refine IsAlgClosed.of_exists_root _ ?_
  intro p hpm hpi
  have h : K ⊨ genericMonicPolyHasRoot '' {n | 0 < n} :=
    Theory.Model.mono h (by simp [Theory.ACF])
  simp only [Theory.model_iff, Set.mem_image,
    forall_exists_index, and_imp] at h
  have := h _ p.natDegree (natDegree_pos_iff_degree_pos.2
    (degree_pos_of_irreducible hpi)) rfl
  rw [realize_genericMonicPolyHasRoot] at this
  exact this ⟨_, hpm, rfl⟩

/--
theorem `ACF_isSatisfiable` / 定理 `ACF_isSatisfiable`

English:
theorem ACF_isSatisfiable
  given: {p : Nat} (hp : p.Prime ∨ p = 0)
  proof: by
  cases hp with
  | inl hp =>
    have : Fact p.Prime := ⟨hp⟩
    let _ := compatibleRingOfRing (AlgebraicClosure (ZMod p))
    exact ⟨⟨AlgebraicClosure (ZMod p)⟩⟩
  | inr hp =>
    subst hp
    let _ := compatibleRingOfRing (AlgebraicClosure Rat)
    exact ⟨⟨AlgebraicClosure Rat⟩⟩

中文:
定理 ACF_isSatisfiable
  条件: {p : 自然数} (hp : p.素 ∨ p = 0)
  证明: by
  cases hp with
  | inl hp =>
    have : Fact p.Prime := ⟨hp⟩
    let _ := compatibleRingOfRing (AlgebraicClosure (ZMod p))
    exact ⟨⟨AlgebraicClosure (ZMod p)⟩⟩
  | inr hp =>
    subst hp
    let _ := compatibleRingOfRing (AlgebraicClosure Rat)
    exact ⟨⟨AlgebraicClosure Rat⟩⟩

Depends on / 依赖: AlgebraicClosure, compatibleRingOfRing, p.Prime
-/
theorem ACF_isSatisfiable {p : Nat} (hp : p.Prime ∨ p = 0) :
    (Theory.ACF p).IsSatisfiable := by
  cases hp with
  | inl hp =>
    have : Fact p.Prime := ⟨hp⟩
    let _ := compatibleRingOfRing (AlgebraicClosure (ZMod p))
    exact ⟨⟨AlgebraicClosure (ZMod p)⟩⟩
  | inr hp =>
    subst hp
    let _ := compatibleRingOfRing (AlgebraicClosure Rat)
    exact ⟨⟨AlgebraicClosure Rat⟩⟩

open Cardinal

/--
theorem `ACF_categorical` / 定理 `ACF_categorical`

English:
theorem ACF_categorical
  given: {p : Nat} (κ : Cardinal) (hκ : ℵ₀ < κ)
  proof: by
  rintro ⟨M⟩ ⟨N⟩ hM hN
  let _ := fieldOfModelACF p M
  have := modelField_of_modelACF p M
  let _ := compatibleRingOfModelField M
  have := isAlgClosed_of_model_ACF p M
  have := charP_of_model_fieldOfChar p M
  let _ := fieldOfModelACF p N
  have := modelField_of_modelACF p N
  let _ := compatibleRingOfModelField N
  have := isAlgClosed_of_model_ACF p N
  have := charP_of_model_fieldOfChar p N
  constructor
  refine languageEquivEquivRingEquiv.symm ?_
  apply Classical.choice
  refine IsAlgClosed.ringEquiv_of_equiv_of_char_eq p ?_ ?_
  · rw [hM]; exact hκ
  · rw [← Cardinal.eq, hM, hN]

中文:
定理 ACF_categorical
  条件: {p : 自然数} (κ : 基数) (hκ : ℵ₀ < κ)
  证明: by
  rintro ⟨M⟩ ⟨N⟩ hM hN
  let _ := fieldOfModelACF p M
  have := modelField_of_modelACF p M
  let _ := compatibleRingOfModelField M
  have := isAlgClosed_of_model_ACF p M
  have := charP_of_model_fieldOfChar p M
  let _ := fieldOfModelACF p N
  have := modelField_of_modelACF p N
  let _ := compatibleRingOfModelField N
  have := isAlgClosed_of_model_ACF p N
  have := charP_of_model_fieldOfChar p N
  constructor
  refine languageEquivEquivRingEquiv.symm ?_
  apply Classical.choice
  refine IsAlgClosed.ringEquiv_of_equiv_of_char_eq p ?_ ?_
  · rw [hM]; exact hκ
  · rw [← Cardinal.eq, hM, hN]

Depends on / 依赖: Classical, Classical.choice, IsAlgClosed, IsAlgClosed.ringEquiv_of_equiv_of_c, charP_of_model_fieldOfChar, choice, compatibleRingOfModelField, fieldOfModelACF, isAlgClosed_of_model_ACF, languageEquivEquivRingEquiv, languageEquivEquivRingEquiv.symm, modelField_of_modelACF, ringEquiv_of_equiv_of_c
-/
theorem ACF_categorical {p : Nat} (κ : Cardinal) (hκ : ℵ₀ < κ) :
    Categorical κ (Theory.ACF p) := by
  rintro ⟨M⟩ ⟨N⟩ hM hN
  let _ := fieldOfModelACF p M
  have := modelField_of_modelACF p M
  let _ := compatibleRingOfModelField M
  have := isAlgClosed_of_model_ACF p M
  have := charP_of_model_fieldOfChar p M
  let _ := fieldOfModelACF p N
  have := modelField_of_modelACF p N
  let _ := compatibleRingOfModelField N
  have := isAlgClosed_of_model_ACF p N
  have := charP_of_model_fieldOfChar p N
  constructor
  refine languageEquivEquivRingEquiv.symm ?_
  apply Classical.choice
  refine IsAlgClosed.ringEquiv_of_equiv_of_char_eq p ?_ ?_
  · rw [hM]; exact hκ
  · rw [← Cardinal.eq, hM, hN]

/--
theorem `ACF_isComplete` / 定理 `ACF_isComplete`

English:
theorem ACF_isComplete
  given: {p : Nat} (hp : p.Prime ∨ p = 0)
  proof: by
  apply Categorical.isComplete.{0, 0, 0} (Order.succ ℵ₀) _
    (ACF_categorical _ (Order.lt_succ _))
    (Order.le_succ ℵ₀)
  · simp only [card_ring, lift_id']
    exact le_trans (le_of_lt (lt_aleph0_of_finite _)) (Order.le_succ _)
  · exact ACF_isSatisfiable hp
  · rintro ⟨M⟩
    let _ := fieldOfModelACF p M
    have := modelField_of_modelACF p M
    let _ := compatibleRingOfModelField M
    have := isAlgClosed_of_model_ACF p M
    infer_instance

中文:
定理 ACF_isComplete
  条件: {p : 自然数} (hp : p.素 ∨ p = 0)
  证明: by
  apply Categorical.isComplete.{0, 0, 0} (Order.succ ℵ₀) _
    (ACF_categorical _ (Order.lt_succ _))
    (Order.le_succ ℵ₀)
  · simp only [card_ring, lift_id']
    exact le_trans (le_of_lt (lt_aleph0_of_finite _)) (Order.le_succ _)
  · exact ACF_isSatisfiable hp
  · rintro ⟨M⟩
    let _ := fieldOfModelACF p M
    have := modelField_of_modelACF p M
    let _ := compatibleRingOfModelField M
    have := isAlgClosed_of_model_ACF p M
    infer_instance

Depends on / 依赖: ACF_categorical, ACF_isSatisfiable, Categorical, Categorical.isComplete, Order.le_succ, Order.lt_succ, Order.succ, card_ring, compatibleRingOfModelField, fieldOfModelACF, infer_instance, isAlgClosed_of_model_ACF, isComplete, le_of_lt, le_succ, le_trans, lift_id, lt_aleph0_of_finite, lt_succ, modelField_of_modelACF
-/
theorem ACF_isComplete {p : Nat} (hp : p.Prime ∨ p = 0) :
    (Theory.ACF p).IsComplete := by
  apply Categorical.isComplete.{0, 0, 0} (Order.succ ℵ₀) _
    (ACF_categorical _ (Order.lt_succ _))
    (Order.le_succ ℵ₀)
  · simp only [card_ring, lift_id']
    exact le_trans (le_of_lt (lt_aleph0_of_finite _)) (Order.le_succ _)
  · exact ACF_isSatisfiable hp
  · rintro ⟨M⟩
    let _ := fieldOfModelACF p M
    have := modelField_of_modelACF p M
    let _ := compatibleRingOfModelField M
    have := isAlgClosed_of_model_ACF p M
    infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `finite_ACF_prime_not_realize_of_ACF_zero_realize` / 定理 `finite_ACF_prime_not_realize_of_ACF_zero_realize`

English:
theorem finite_ACF_prime_not_realize_of_ACF_zero_realize
  proof: by
  rw [Theory.models_iff_finset_models] at h
  rcases h with ⟨T0, hT0, h⟩
  have f : forall ψ in Theory.ACF 0,
      { s : Finset Nat.Primes // forall q : Nat.Primes, q ∉ s -> Theory.ACF q ⊨ᵇ ψ } := by
    intro ψ hψ
    rw [Theory.ACF]; rw [Theory.fieldOfChar]; rw [Set.union_right_comm]; rw [Set.mem_union]; rw [if_pos rfl]; rw [Set.mem_image] at hψ
    apply Classical.choice
    rcases hψ with h | ⟨p, hp, rfl⟩
    · refine ⟨⟨∅, ?_⟩⟩
      intro q _
      exact Theory.models_sentence_of_mem
        (by rw [Theory.ACF, Theory.fieldOfChar, Set.union_right_comm];
            exact Set.mem_union_left _ h)
    · refine ⟨⟨{⟨p, hp⟩}, ?_⟩⟩
      rintro ⟨q, _⟩ hq ⟨K⟩ _ _
      have hqp : q != p := by simpa [← Nat.Primes.coe_nat_inj] using hq
      let _ := fieldOfModelACF q K
      have := modelField_of_modelACF q K
      let _ := compatibleRingOfModelField K
      have := charP_of_model_fieldOfChar q K
      simp only [eqZero, Term.equal, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
        Term.realize_relabel, Sum.elim_comp_inl, realize_termOfFreeCommRing, map_natCast,
        realize_zero, ← CharP.charP_iff_prime_eq_zero hp]
      intro _
exact hqp CharP.eq K this inferInstance
  let s : Finset Nat.Primes := T0.attach.biUnion (fun φ => f φ.1 (hT0 φ.2))
  have hs : forall (p : Nat.Primes) ψ, ψ in T0 -> p ∉ s -> Theory.ACF p ⊨ᵇ ψ := by
    intro p ψ hψ hpψ
    simp only [s, Finset.mem_biUnion, Finset.mem_attach, true_and,
      Subtype.exists, not_exists] at hpψ
    exact (f ψ (hT0 hψ)).2 p (hpψ _ hψ)
  refine Set.Finite.subset (Finset.finite_toSet s) (Set.compl_subset_comm.2 ?_)
  intro p hp
  exact Theory.models_of_models_theory (fun ψ hψ => hs p ψ hψ hp) h

中文:
定理 finite_ACF_prime_not_realize_of_ACF_zero_realize
  证明: by
  rw [Theory.models_iff_finset_models] at h
  rcases h with ⟨T0, hT0, h⟩
  have f : forall ψ in Theory.ACF 0,
      { s : Finset Nat.Primes // forall q : Nat.Primes, q ∉ s -> Theory.ACF q ⊨ᵇ ψ } := by
    intro ψ hψ
    rw [Theory.ACF]; rw [Theory.fieldOfChar]; rw [Set.union_right_comm]; rw [Set.mem_union]; rw [if_pos rfl]; rw [Set.mem_image] at hψ
    apply Classical.choice
    rcases hψ with h | ⟨p, hp, rfl⟩
    · refine ⟨⟨∅, ?_⟩⟩
      intro q _
      exact Theory.models_sentence_of_mem
        (by rw [Theory.ACF, Theory.fieldOfChar, Set.union_right_comm];
            exact Set.mem_union_left _ h)
    · refine ⟨⟨{⟨p, hp⟩}, ?_⟩⟩
      rintro ⟨q, _⟩ hq ⟨K⟩ _ _
      have hqp : q != p := by simpa [← Nat.Primes.coe_nat_inj] using hq
      let _ := fieldOfModelACF q K
      have := modelField_of_modelACF q K
      let _ := compatibleRingOfModelField K
      have := charP_of_model_fieldOfChar q K
      simp only [eqZero, Term.equal, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
        Term.realize_relabel, Sum.elim_comp_inl, realize_termOfFreeCommRing, map_natCast,
        realize_zero, ← CharP.charP_iff_prime_eq_zero hp]
      intro _
exact hqp CharP.eq K this inferInstance
  let s : Finset Nat.Primes := T0.attach.biUnion (fun φ => f φ.1 (hT0 φ.2))
  have hs : forall (p : Nat.Primes) ψ, ψ in T0 -> p ∉ s -> Theory.ACF p ⊨ᵇ ψ := by
    intro p ψ hψ hpψ
    simp only [s, Finset.mem_biUnion, Finset.mem_attach, true_and,
      Subtype.exists, not_exists] at hpψ
    exact (f ψ (hT0 hψ)).2 p (hpψ _ hψ)
  refine Set.Finite.subset (Finset.finite_toSet s) (Set.compl_subset_comm.2 ?_)
  intro p hp
  exact Theory.models_of_models_theory (fun ψ hψ => hs p ψ hψ hp) h

Depends on / 依赖: Classical, Classical.choice, Finset, Nat.Primes, Primes, Set.mem_image, Set.mem_union, Set.un, Set.union_right_comm, Theory, Theory.ACF, Theory.fieldOfChar, Theory.models_iff_finset_models, Theory.models_sentence_of_mem, choice, fieldOfChar, if_pos, mem_image, mem_union, models_iff_finset_models
-/
theorem finite_ACF_prime_not_realize_of_ACF_zero_realize
    (φ : Language.ring.Sentence) (h : Theory.ACF 0 ⊨ᵇ φ) :
    Set.Finite { p : Nat.Primes | ¬ Theory.ACF p ⊨ᵇ φ } := by
  rw [Theory.models_iff_finset_models] at h
  rcases h with ⟨T0, hT0, h⟩
  have f : forall ψ in Theory.ACF 0,
      { s : Finset Nat.Primes // forall q : Nat.Primes, q ∉ s -> Theory.ACF q ⊨ᵇ ψ } := by
    intro ψ hψ
    rw [Theory.ACF]; rw [Theory.fieldOfChar]; rw [Set.union_right_comm]; rw [Set.mem_union]; rw [if_pos rfl]; rw [Set.mem_image] at hψ
    apply Classical.choice
    rcases hψ with h | ⟨p, hp, rfl⟩
    · refine ⟨⟨∅, ?_⟩⟩
      intro q _
      exact Theory.models_sentence_of_mem
        (by rw [Theory.ACF, Theory.fieldOfChar, Set.union_right_comm];
            exact Set.mem_union_left _ h)
    · refine ⟨⟨{⟨p, hp⟩}, ?_⟩⟩
      rintro ⟨q, _⟩ hq ⟨K⟩ _ _
      have hqp : q != p := by simpa [← Nat.Primes.coe_nat_inj] using hq
      let _ := fieldOfModelACF q K
      have := modelField_of_modelACF q K
      let _ := compatibleRingOfModelField K
      have := charP_of_model_fieldOfChar q K
      simp only [eqZero, Term.equal, BoundedFormula.realize_not, BoundedFormula.realize_bdEqual,
        Term.realize_relabel, Sum.elim_comp_inl, realize_termOfFreeCommRing, map_natCast,
        realize_zero, ← CharP.charP_iff_prime_eq_zero hp]
      intro _
exact hqp CharP.eq K this inferInstance
  let s : Finset Nat.Primes := T0.attach.biUnion (fun φ => f φ.1 (hT0 φ.2))
  have hs : forall (p : Nat.Primes) ψ, ψ in T0 -> p ∉ s -> Theory.ACF p ⊨ᵇ ψ := by
    intro p ψ hψ hpψ
    simp only [s, Finset.mem_biUnion, Finset.mem_attach, true_and,
      Subtype.exists, not_exists] at hpψ
    exact (f ψ (hT0 hψ)).2 p (hpψ _ hψ)
  refine Set.Finite.subset (Finset.finite_toSet s) (Set.compl_subset_comm.2 ?_)
  intro p hp
  exact Theory.models_of_models_theory (fun ψ hψ => hs p ψ hψ hp) h

/--
theorem `ACF_zero_realize_iff_infinite_ACF_prime_realize` / 定理 `ACF_zero_realize_iff_infinite_ACF_prime_realize`

English:
theorem ACF_zero_realize_iff_infinite_ACF_prime_realize
  given: {φ : Language.ring.Sentence}
  proof: by
  refine ⟨fun h => Set.infinite_of_finite_compl
      (finite_ACF_prime_not_realize_of_ACF_zero_realize φ h),
    not_imp_not.1 ?_⟩
  simpa [(ACF_isComplete (Or.inr rfl)).models_not_iff,
      fun p : Nat.Primes => (ACF_isComplete (Or.inl p.2)).models_not_iff] using
    finite_ACF_prime_not_realize_of_ACF_zero_realize φ.not

中文:
定理 ACF_zero_realize_iff_infinite_ACF_prime_realize
  条件: {φ : Language.ring.Sentence}
  证明: by
  refine ⟨fun h => Set.infinite_of_finite_compl
      (finite_ACF_prime_not_realize_of_ACF_zero_realize φ h),
    not_imp_not.1 ?_⟩
  simpa [(ACF_isComplete (Or.inr rfl)).models_not_iff,
      fun p : Nat.Primes => (ACF_isComplete (Or.inl p.2)).models_not_iff] using
    finite_ACF_prime_not_realize_of_ACF_zero_realize φ.not

Depends on / 依赖: ACF_isComplete, Nat.Primes, Or.inl, Or.inr, Primes, Set.infinite_of_finite_compl, finite_ACF_prime_not_realize_of_ACF_zero_realize, infinite_of_finite_compl, models_not_iff, not_imp_not
-/
theorem ACF_zero_realize_iff_infinite_ACF_prime_realize {φ : Language.ring.Sentence} :
    Theory.ACF 0 ⊨ᵇ φ ↔ Set.Infinite { p : Nat.Primes | Theory.ACF p ⊨ᵇ φ } := by
  refine ⟨fun h => Set.infinite_of_finite_compl
      (finite_ACF_prime_not_realize_of_ACF_zero_realize φ h),
    not_imp_not.1 ?_⟩
  simpa [(ACF_isComplete (Or.inr rfl)).models_not_iff,
      fun p : Nat.Primes => (ACF_isComplete (Or.inl p.2)).models_not_iff] using
    finite_ACF_prime_not_realize_of_ACF_zero_realize φ.not

/--
theorem `ACF_zero_realize_iff_finite_ACF_prime_not_realize` / 定理 `ACF_zero_realize_iff_finite_ACF_prime_not_realize`

English:
theorem ACF_zero_realize_iff_finite_ACF_prime_not_realize
  given: {φ : Language.ring.Sentence}
  proof: ⟨fun h => finite_ACF_prime_not_realize_of_ACF_zero_realize φ h,
    fun h => ACF_zero_realize_iff_infinite_ACF_prime_realize.2
      (Set.infinite_of_finite_compl h)⟩

中文:
定理 ACF_zero_realize_iff_finite_ACF_prime_not_realize
  条件: {φ : Language.ring.Sentence}
  证明: ⟨fun h => finite_ACF_prime_not_realize_of_ACF_zero_realize φ h,
    fun h => ACF_zero_realize_iff_infinite_ACF_prime_realize.2
      (Set.infinite_of_finite_compl h)⟩

Depends on / 依赖: ACF_zero_realize_iff_infinite_ACF_prime_realize, Set.infinite_of_finite_compl, finite_ACF_prime_not_realize_of_ACF_zero_realize, infinite_of_finite_compl
-/
theorem ACF_zero_realize_iff_finite_ACF_prime_not_realize {φ : Language.ring.Sentence} :
    Theory.ACF 0 ⊨ᵇ φ ↔ Set.Finite { p : Nat.Primes | Theory.ACF p ⊨ᵇ φ }ᶜ :=
  ⟨fun h => finite_ACF_prime_not_realize_of_ACF_zero_realize φ h,
    fun h => ACF_zero_realize_iff_infinite_ACF_prime_realize.2
      (Set.infinite_of_finite_compl h)⟩


end Field

end FirstOrder
