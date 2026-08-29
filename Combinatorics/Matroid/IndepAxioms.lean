/-
Copyright (c) 2023 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
module

public import Mathlib.Combinatorics.Matroid.Basic
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Matroid Independence and Basis axioms

Matroids in mathlib are defined axiomatically in terms of bases,
but can be described just as naturally via their collections of independent sets,
and in fact such a description, being more 'verbose', can often be useful.
As well as this, the definition of a `Matroid` uses an unwieldy 'maximality'
axiom that can be dropped in cases where there is some finiteness assumption.

This file provides several ways to do define a matroid in terms of its independence or base
predicates, using axiom sets that are appropriate in different settings,
and often much simpler than the general definition.
It also contains `simp` lemmas and typeclasses as appropriate.

All the independence axiom sets need nontriviality (the empty set is independent),
monotonicity (subsets of independent sets are independent),
and some form of 'augmentation' axiom, which allows one to enlarge a non-maximal independent set.
This augmentation axiom is still required when there are finiteness assumptions, but is simpler.
It just states that if `I` is a finite independent set and `J` is a larger finite
independent set, then there exists `e ∈ J \ I` for which `insert e I` is independent.
This is the axiom that appears in most of the definitions.

## Implementation Details

To facilitate building a matroid from its independent sets, we define a structure `IndepMatroid`
which has a ground set `E`, an independence predicate `Indep`, and some axioms as its fields.
This structure is another encoding of the data in a `Matroid`; the function `IndepMatroid.matroid`
constructs a `Matroid` from an `IndepMatroid`.

This is convenient because if one wants to define `M : Matroid α` from a known independence
predicate `Ind`, it is easier to define an `M' : IndepMatroid α` so that `M'.Indep = Ind` and
then set `M = M'.matroid` than it is to directly define `M` with the base axioms.
The simp lemma `IndepMatroid.matroid_indep_iff` is important here; it shows that `M.Indep = Ind`,
so the `Matroid` constructed is the right one, and the intermediate `IndepMatroid` can be
made essentially invisible by the simplifier when working with `M`.

Because of this setup, we don't define any API for `IndepMatroid`, as it would be
a redundant copy of the existing API for `Matroid.Indep`.
(In particular, one could define a natural equivalence `e : IndepMatroid α ≃ Matroid α`
with `e.toFun = IndepMatroid.matroid`, but this would be pointless, as there is no need
for the inverse of `e`).

## Main definitions


* `IndepMatroid α` is a matroid structure on `α` described in terms of its independent sets
  in full generality, using infinite versions of the axioms.

* `IndepMatroid.matroid` turns `M' : IndepMatroid α` into `M : Matroid α` with `M'.Indep = M.Indep`.

* `IndepMatroid.ofFinitary` constructs an `IndepMatroid` whose associated `Matroid` is `Finitary`
  in the special case where independence of a set is determined only by that of its
  finite subsets. This construction uses Zorn's lemma.

* `IndepMatroid.ofFinitaryCardAugment` is a variant of `IndepMatroid.ofFinitary` where the
  augmentation axiom resembles the finite augmentation axiom.

* `IndepMatroid.ofBdd` constructs an `IndepMatroid` in the case where there is some known
  absolute upper bound on the size of an independent set. This uses the infinite version of
  the augmentation axiom; the corresponding `Matroid` is `RankFinite`.

* `IndepMatroid.ofBddAugment` is the same as the above, but with a finite augmentation axiom.

* `IndepMatroid.ofFinite` constructs an `IndepMatroid` from a finite ground set in terms of
  its independent sets.

* `IndepMatroid.ofFinset` constructs an `IndepMatroid α` whose corresponding matroid is `Finitary`
  from an independence predicate on `Finset α`.

* `Matroid.ofExistsMatroid` constructs a 'copy' of a matroid that is known only
  existentially, but whose independence predicate is known explicitly.

* `Matroid.ofExistsFiniteIsBase` constructs a matroid from its bases, if it is known that one
  of them is finite. This gives a `RankFinite` matroid.

* `Matroid.ofIsBaseOfFinite` constructs a `Finite` matroid from its bases.
-/

@[expose] public section

assert_not_exists Field

open Set Matroid

variable {α : Type*}

section IndepMatroid

/--
Definition of `IndepMatroid` / `IndepMatroid` 的定义

English:
structure IndepMatroid
  parameters: (α : Type*)
  axioms and operations (7):
    - (E : Set α)
    - (Indep : Set α -> Prop)
    - (indep_empty : Indep ∅)
    - (indep_subset : forall ⦃I J⦄, Indep J -> I subseteq J -> Indep I)
    - (indep_aug : forall ⦃I B⦄, Indep I -> ¬ Maximal Indep I -> Maximal Indep B -> exists x in B \ I, Indep (insert x I))
    - (indep_maximal : forall X, X subseteq E -> ExistsMaximalSubsetProperty Indep X)
    - (subset_ground : forall I, Indep I -> I subseteq E)

中文:
结构 IndepMatroid
  参数: (α : 类型)
  公理与运算 (7 个):
    - (E : Set α)
    - (Indep : Set α -> 命题)
    - (indep_empty : Indep ∅)
    - (indep_subset : 对任意 ⦃I J⦄, Indep J -> I subseteq J -> Indep I)
    - (indep_aug : 对任意 ⦃I B⦄, Indep I -> ¬ Maximal Indep I -> Maximal Indep B -> 存在 x in B \ I, Indep (insert x I))
    - (indep_maximal : 对任意 X, X subseteq E -> ExistsMaximalSubset命题erty Indep X)
    - (subset_ground : 对任意 I, Indep I -> I subseteq E)

Depends on / 依赖: Quot.lift.decidablePred, decidablePred
-/
structure IndepMatroid (α : Type*) where
  /-- The ground set -/
  (E : Set α)
  /-- The independence predicate -/
  (Indep : Set α -> Prop)
  (indep_empty : Indep ∅)
  (indep_subset : forall ⦃I J⦄, Indep J -> I subseteq J -> Indep I)
  (indep_aug : forall ⦃I B⦄, Indep I -> ¬ Maximal Indep I ->
    Maximal Indep B -> exists x in B \ I, Indep (insert x I))
  (indep_maximal : forall X, X subseteq E -> ExistsMaximalSubsetProperty Indep X)
  (subset_ground : forall I, Indep I -> I subseteq E)

namespace IndepMatroid

/--
Definition of `matroid` / `matroid` 的定义

English:
definition matroid
  signature: (M : IndepMatroid α)
  body: M.E
  IsBase := Maximal M.Indep
  Indep := M.Indep
  indep_iff' := by
    refine fun I => ⟨fun h => ?_, fun ⟨B, ⟨h, _⟩, hIB'⟩ => M.indep_subset h hIB'⟩
    obtain ⟨J, hIJ, hmax⟩ := M.indep_maximal M.E rfl.subset I h (M.subset_ground I h)
    rw [maximal_and_iff_right_of_imp M.subset_ground] at hmax


中文:
定义 matroid
  签名: (M : IndepMatroid α)
  定义体: M.E
  IsBase := Maximal M.Indep
  Indep := M.Indep
  indep_iff' := by
    refine fun I => ⟨fun h => ?_, fun ⟨B, ⟨h, _⟩, hIB'⟩ => M.indep_subset h hIB'⟩
    obtain ⟨J, hIJ, hmax⟩ := M.indep_maximal M.E rfl.subset I h (M.subset_ground I h)
    rw [maximal_and_iff_right_of_imp M.subset_ground] at hmax


Depends on / 依赖: Quot.lift, decidablePred
-/
@[simps] protected def matroid (M : IndepMatroid α) : Matroid α where
  E := M.E
  IsBase := Maximal M.Indep
  Indep := M.Indep
  indep_iff' := by
    refine fun I => ⟨fun h => ?_, fun ⟨B, ⟨h, _⟩, hIB'⟩ => M.indep_subset h hIB'⟩
    obtain ⟨J, hIJ, hmax⟩ := M.indep_maximal M.E rfl.subset I h (M.subset_ground I h)
    rw [maximal_and_iff_right_of_imp M.subset_ground] at hmax
    exact ⟨J, hmax.1, hIJ⟩
  exists_isBase := by
obtain ⟨B, -, hB⟩ := M.indep_maximal M.E rfl.subset ∅ M.indep_empty empty_subset _
    rw [maximal_and_iff_right_of_imp M.subset_ground] at hB
    exact ⟨B, hB.1⟩
  isBase_exchange B B' hB hB' e he := by
    have hnotmax : ¬ Maximal M.Indep (B \ {e}) :=
      fun h => h.not_prop_of_ssuperset (sdiff_singleton_ssubset.2 he.1) hB.prop
    obtain ⟨f, hf, hfB⟩ := M.indep_aug (M.indep_subset hB.prop sdiff_subset) hnotmax hB'
    replace hf := show f in B' \ B by simpa [show f != e by rintro rfl; exact he.2 hf.1] using hf
    refine ⟨f, hf, by_contra fun hnot => ?_⟩
    obtain ⟨x, hxB, hind⟩ := M.indep_aug hfB hnot hB
    obtain ⟨-, rfl⟩ : _ ∧ x = e := by simpa [hxB.1] using hxB
    refine hB.not_prop_of_ssuperset ?_ hind
    rw [insert_comm]; rw [insert_sdiff_singleton]; rw [insert_eq_of_mem he.1]
    exact ssubset_insert hf.2
  maximality := M.indep_maximal
  subset_ground B hB := M.subset_ground B hB.1

/--
theorem `matroid_indep_iff` / 定理 `matroid_indep_iff`

English:
theorem matroid_indep_iff
  given: {M : IndepMatroid α} {I : Set α}
  proof: Iff.rfl

中文:
定理 matroid_indep_iff
  条件: {M : IndepMatroid α} {I : Set α}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem matroid_indep_iff {M : IndepMatroid α} {I : Set α} :
    M.matroid.Indep I ↔ M.Indep I := Iff.rfl

/--
Definition of `ofFinitary` / `ofFinitary` 的定义

English:
definition ofFinitary
  signature: (E : Set α) (Indep : Set α -> Prop)
  body: E
  Indep := Indep
  indep_empty := indep_empty
  indep_subset := indep_subset
  indep_aug := indep_aug
  indep_maximal := by
    refine fun X _ I hI hIX => zorn_subset_nonempty {Y | Indep Y ∧ Y subseteq X} ?_ I ⟨hI, hIX⟩
    refine fun Is hIs hchain _ =>
      ⟨⋃₀ Is, ⟨?_, sUnion_subset fun Y hY =>

中文:
定义 ofFinitary
  签名: (E : Set α) (Indep : Set α -> 命题)
  定义体: E
  Indep := Indep
  indep_empty := indep_empty
  indep_subset := indep_subset
  indep_aug := indep_aug
  indep_maximal := by
    refine fun X _ I hI hIX => zorn_subset_nonempty {Y | Indep Y ∧ Y subseteq X} ?_ I ⟨hI, hIX⟩
    refine fun Is hIs hchain _ =>
      ⟨⋃₀ Is, ⟨?_, sUnion_subset fun Y hY =>
-/
@[simps E] protected def ofFinitary (E : Set α) (Indep : Set α -> Prop)
    (indep_empty : Indep ∅)
    (indep_subset : forall ⦃I J⦄, Indep J -> I subseteq J -> Indep I)
    (indep_aug : forall ⦃I B⦄, Indep I -> ¬ Maximal Indep I -> Maximal Indep B ->
      exists x in B \ I, Indep (insert x I))
    (indep_compact : forall I, (forall J, J subseteq I -> J.Finite -> Indep J) -> Indep I)
    (subset_ground : forall I, Indep I -> I subseteq E) : IndepMatroid α where
  E := E
  Indep := Indep
  indep_empty := indep_empty
  indep_subset := indep_subset
  indep_aug := indep_aug
  indep_maximal := by
    refine fun X _ I hI hIX => zorn_subset_nonempty {Y | Indep Y ∧ Y subseteq X} ?_ I ⟨hI, hIX⟩
    refine fun Is hIs hchain _ =>
      ⟨⋃₀ Is, ⟨?_, sUnion_subset fun Y hY => (hIs hY).2⟩, fun _ => subset_sUnion_of_mem⟩
    refine indep_compact _ fun J hJ hJfin => ?_
have hchoose : forall e, e in J -> exists I, I in Is ∧ (e : α) in I := fun _ he => mem_sUnion.1 hJ he
    choose! f hf using hchoose
    refine J.eq_empty_or_nonempty.elim (fun hJ => hJ ▸ indep_empty) (fun hne => ?_)
    obtain ⟨x, hxJ, hxmax⟩ := Finite.exists_maximalFor f _ hJfin hne
    refine indep_subset (hIs (hf x hxJ).1).1 fun y hyJ => ?_
    obtain (hle | hle) := hchain.total (hf _ hxJ).1 (hf _ hyJ).1
· exact hxmax hyJ hle (hf _ hyJ).2
    · exact hle (hf _ hyJ).2
  subset_ground := subset_ground

/--
theorem `ofFinitary_indep` / 定理 `ofFinitary_indep`

English:
theorem ofFinitary_indep
  statement: (E : Set α) (Indep : Set α -> Prop)
  proof: rfl

中文:
定理 ofFinitary_indep
  结论: (E : Set α) (Indep : Set α -> 命题)
  证明: rfl
-/
@[simp] theorem ofFinitary_indep (E : Set α) (Indep : Set α -> Prop)
    indep_empty indep_subset indep_aug indep_compact subset_ground :
    (IndepMatroid.ofFinitary
      E Indep indep_empty indep_subset indep_aug indep_compact subset_ground).Indep = Indep := rfl

/--
Instance `ofFinitary_finitary` / 实例 `ofFinitary_finitary`

English:
instance ofFinitary_finitary
  signature: (E : Set α) (Indep : Set α -> Prop)
  body: ⟨by simpa⟩

中文:
实例 ofFinitary_finitary
  签名: (E : Set α) (Indep : Set α -> 命题)
  定义体: ⟨by simpa⟩

Depends on / 依赖: Setoid, Setoid.refl
-/
instance ofFinitary_finitary (E : Set α) (Indep : Set α -> Prop)
    indep_empty indep_subset indep_aug indep_compact subset_ground : Finitary
    (IndepMatroid.ofFinitary
      E Indep indep_empty indep_subset indep_aug indep_compact subset_ground).matroid :=
  ⟨by simpa⟩

/--
Definition of `ofFinitaryCardAugment` / `ofFinitaryCardAugment` 的定义

English:
definition ofFinitaryCardAugment
  signature: (E : Set α) (Indep : Set α -> Prop)
  body: IndepMatroid.ofFinitary
    (E := E)
    (Indep := Indep)
    (indep_empty := indep_empty)
    (indep_subset := indep_subset)
    (indep_compact := indep_compact)
    (indep_aug := by
      have htofin : forall I e, Indep I -> ¬ Indep (insert e I) ->
        exists I₀, I₀ subseteq I ∧ I₀.Finite ∧ ¬ 

中文:
定义 ofFinitaryCardAugment
  签名: (E : Set α) (Indep : Set α -> 命题)
  定义体: IndepMatroid.ofFinitary
    (E := E)
    (Indep := Indep)
    (indep_empty := indep_empty)
    (indep_subset := indep_subset)
    (indep_compact := indep_compact)
    (indep_aug := by
      have htofin : forall I e, Indep I -> ¬ Indep (insert e I) ->
        exists I₀, I₀ subseteq I ∧ I₀.Finite ∧ ¬ 
-/
@[simps! E] protected def ofFinitaryCardAugment (E : Set α) (Indep : Set α -> Prop)
    (indep_empty : Indep ∅)
    (indep_subset : forall ⦃I J⦄, Indep J -> I subseteq J -> Indep I)
    (indep_aug : forall ⦃I J⦄, Indep I -> I.Finite -> Indep J -> J.Finite -> I.ncard < J.ncard ->
      exists e in J, e ∉ I ∧ Indep (insert e I))
    (indep_compact : forall I, (forall J, J subseteq I -> J.Finite -> Indep J) -> Indep I)
    (subset_ground : forall I, Indep I -> I subseteq E) : IndepMatroid α :=
  IndepMatroid.ofFinitary
    (E := E)
    (Indep := Indep)
    (indep_empty := indep_empty)
    (indep_subset := indep_subset)
    (indep_compact := indep_compact)
    (indep_aug := by
      have htofin : forall I e, Indep I -> ¬ Indep (insert e I) ->
        exists I₀, I₀ subseteq I ∧ I₀.Finite ∧ ¬ Indep (insert e I₀) := by
        by_contra! ⟨I, e, -, hIe, h⟩
refine hIe indep_compact _ fun J hJss hJfin => ?_
        exact indep_subset (h (J \ {e}) (by rwa [sdiff_subset_iff]) hJfin.sdiff) (by simp)
      intro I B hI hImax hBmax
      obtain ⟨e, heI, hins⟩ := exists_insert_of_not_maximal indep_subset hI hImax
      by_cases heB : e in B
      · exact ⟨e, ⟨heB, heI⟩, hins⟩
      by_contra! hcon
      have heBdep := hBmax.not_prop_of_ssuperset (ssubset_insert heB)
      -- There is a finite subset `B₀` of `B` so that `B₀ + e` is dependent
      obtain ⟨B₀, hB₀B, hB₀fin, hB₀e⟩ := htofin B e hBmax.1 heBdep
      have hB₀ := indep_subset hBmax.1 hB₀B
      -- `I` has a finite subset `I₀` that doesn't extend into `B₀`
      have hexI₀ : exists I₀, I₀ subseteq I ∧ I₀.Finite ∧ forall x, x in B₀ \ I₀ -> ¬Indep (insert x I₀) := by
        have hch : forall (b : ↑(B₀ \ I)), exists Ib, Ib subseteq I ∧ Ib.Finite ∧ ¬Indep (insert (b : α) Ib) := by
          rintro ⟨b, hb⟩; exact htofin I b hI (hcon b ⟨hB₀B hb.1, hb.2⟩)
        choose! f hf using hch
        have : Finite ↑(B₀ \ I) := hB₀fin.sdiff.to_subtype
        refine ⟨iUnion f union (B₀ inter I),
          union_subset (iUnion_subset (fun i => (hf i).1)) inter_subset_right,
          (finite_iUnion fun i => (hf i).2.1).union (hB₀fin.subset inter_subset_left),
          fun x ⟨hxB₀, hxn⟩ hi => ?_⟩
have hxI : x ∉ I := fun hxI => hxn Or.inr ⟨hxB₀, hxI⟩
        refine (hf ⟨x, ⟨hxB₀, hxI⟩⟩).2.2 (indep_subset hi <| insert_subset_insert ?_)
        apply subset_union_of_subset_left
        apply subset_iUnion
      obtain ⟨I₀, hI₀I, hI₀fin, hI₀⟩ := hexI₀
      set E₀ := insert e (I₀ union B₀)
      have hE₀fin : E₀.Finite := (hI₀fin.union hB₀fin).insert e
      -- Extend `B₀` to a maximal independent subset of `I₀ ∪ B₀ + e`
      obtain ⟨J, ⟨hB₀J, hJ, hJss⟩, hJmax⟩ := Finite.exists_maximalFor (f := id)
        (s := {J | B₀ subseteq J ∧ Indep J ∧ J subseteq E₀})
        (hE₀fin.finite_subsets.subset (by simp))
        ⟨B₀, Subset.rfl, hB₀, subset_union_right.trans (subset_insert _ _)⟩
      have heI₀ : e ∉ I₀ := notMem_subset hI₀I heI
      have heI₀i : Indep (insert e I₀) := indep_subset hins (insert_subset_insert hI₀I)
      have heJ : e ∉ J := fun heJ => hB₀e (indep_subset hJ <| insert_subset heJ hB₀J)
      have hJfin := hE₀fin.subset hJss
      -- We have `|I₀ + e| ≤ |J|`, since otherwise we could extend the maximal set `J`
      have hcard : (insert e I₀).ncard <= J.ncard := by
        refine not_lt.1 fun hlt => ?_
        obtain ⟨f, hfI, hfJ, hfi⟩ := indep_aug hJ hJfin heI₀i (hI₀fin.insert e) hlt
        have hfE₀ : f in E₀ := mem_of_mem_of_subset hfI (insert_subset_insert subset_union_left)
exact hfJ insert_eq_self.1 le_imp_eq_iff_le_imp_ge'.2 (hJmax
⟨hB₀J.trans subset_insert _ _, hfi, insert_subset hfE₀ hJss⟩) (subset_insert _ _)
      -- But this means `|I₀| < |J|`, and extending `I₀` into `J` gives a contradiction
      rw [ncard_insert_of_notMem heI₀ hI₀fin]; rw [← Nat.lt_iff_add_one_le] at hcard
      obtain ⟨f, hfJ, hfI₀, hfi⟩ := indep_aug (indep_subset hI hI₀I) hI₀fin hJ hJfin hcard
      exact hI₀ f ⟨Or.elim (hJss hfJ) (fun hfe => (heJ <| hfe ▸ hfJ).elim) (by aesop), hfI₀⟩ hfi)
  (subset_ground := subset_ground)

/--
theorem `ofFinitaryCardAugment_indep` / 定理 `ofFinitaryCardAugment_indep`

English:
theorem ofFinitaryCardAugment_indep
  statement: (E : Set α) (Indep : Set α -> Prop)
  proof: rfl

中文:
定理 ofFinitaryCardAugment_indep
  结论: (E : Set α) (Indep : Set α -> 命题)
  证明: rfl
-/
@[simp] theorem ofFinitaryCardAugment_indep (E : Set α) (Indep : Set α -> Prop)
    indep_empty indep_subset indep_aug indep_compact subset_ground :
    (IndepMatroid.ofFinitaryCardAugment
      E Indep indep_empty indep_subset indep_aug indep_compact subset_ground).Indep = Indep := rfl

/--
Instance `ofFinitaryCardAugment_finitary` / 实例 `ofFinitaryCardAugment_finitary`

English:
instance ofFinitaryCardAugment_finitary
  signature: (E : Set α) (Indep : Set α -> Prop)
  body: ⟨by simpa⟩

中文:
实例 ofFinitaryCardAugment_finitary
  签名: (E : Set α) (Indep : Set α -> 命题)
  定义体: ⟨by simpa⟩

Depends on / 依赖: Quot.lift.decidablePred, decidablePred
-/
instance ofFinitaryCardAugment_finitary (E : Set α) (Indep : Set α -> Prop)
    indep_empty indep_subset indep_aug indep_compact subset_ground : Finitary
    (IndepMatroid.ofFinitaryCardAugment
      E Indep indep_empty indep_subset indep_aug indep_compact subset_ground).matroid :=
  ⟨by simpa⟩

/--
theorem `_root_.Matroid.existsMaximalSubsetProperty_of_bdd` / 定理 `_root_.Matroid.existsMaximalSubsetProperty_of_bdd`

English:
theorem _root_.Matroid.existsMaximalSubsetProperty_of_bdd
  statement: {P : Set α -> Prop}
  proof: by
  obtain ⟨n, hP⟩ := hP
  rintro I hI hIX
  have hfin : Set.Finite (ncard '' {Y | P Y ∧ I subseteq Y ∧ Y subseteq X}) := by
    rw [finite_iff_bddAbove]; rw [bddAbove_def]
    simp_rw [ENat.le_natCast_iff] at hP
    use n
    rintro x ⟨Y, ⟨hY, -, -⟩, rfl⟩
    obtain ⟨n₀, heq, hle⟩ := hP Y hY
    r

中文:
定理 _root_.Matroid.existsMaximalSubsetProperty_of_bdd
  结论: {P : Set α -> 命题}
  证明: by
  obtain ⟨n, hP⟩ := hP
  rintro I hI hIX
  have hfin : Set.Finite (ncard '' {Y | P Y ∧ I subseteq Y ∧ Y subseteq X}) := by
    rw [finite_iff_bddAbove]; rw [bddAbove_def]
    simp_rw [ENat.le_natCast_iff] at hP
    use n
    rintro x ⟨Y, ⟨hY, -, -⟩, rfl⟩
    obtain ⟨n₀, heq, hle⟩ := hP Y hY
    r

Depends on / 依赖: ENat.le_natCast_iff, ENat.toNat_natCast, Finite, Finite.exists_maximalFor, K.Finite, Quotient, Quotient.recOnSubsingleton, Set.Finite, bddAbove_def, exists_maximalFor, finite_iff_bddAbove, finite_of_e, le_natCast_iff, ncard_def, rfl.subset, simp_rw, subset, subseteq, toNat_natCast
-/
theorem _root_.Matroid.existsMaximalSubsetProperty_of_bdd {P : Set α -> Prop}
    (hP : exists (n : Nat), forall Y, P Y -> Y.encard <= n) (X : Set α) : ExistsMaximalSubsetProperty P X := by
  obtain ⟨n, hP⟩ := hP
  rintro I hI hIX
  have hfin : Set.Finite (ncard '' {Y | P Y ∧ I subseteq Y ∧ Y subseteq X}) := by
    rw [finite_iff_bddAbove]; rw [bddAbove_def]
    simp_rw [ENat.le_natCast_iff] at hP
    use n
    rintro x ⟨Y, ⟨hY, -, -⟩, rfl⟩
    obtain ⟨n₀, heq, hle⟩ := hP Y hY
    rwa [ncard_def, heq, ENat.toNat_natCast]
  obtain ⟨Y, ⟨hY, hIY, hYX⟩, hY'⟩ :=
    Finite.exists_maximalFor' ncard _ hfin ⟨I, hI, rfl.subset, hIX⟩
  refine ⟨Y, hIY, ⟨hY, hYX⟩, fun K ⟨hPK, hKX⟩ hYK => ?_⟩
  have hKfin : K.Finite := finite_of_encard_le_coe (hP K hPK)
  refine (eq_of_subset_of_ncard_le hYK ?_ hKfin).symm.subset
  exact hY' ⟨hPK, hIY.trans hYK, hKX⟩ (ncard_le_ncard hYK hKfin)

/--
Definition of `ofBdd` / `ofBdd` 的定义

English:
definition ofBdd
  signature: (E : Set α) (Indep : Set α -> Prop)
  body: E
  Indep := Indep
  indep_empty := indep_empty
  indep_subset := indep_subset
  indep_aug := indep_aug
  indep_maximal X _ := Matroid.existsMaximalSubsetProperty_of_bdd indep_bdd X
  subset_ground := subset_ground

中文:
定义 ofBdd
  签名: (E : Set α) (Indep : Set α -> 命题)
  定义体: E
  Indep := Indep
  indep_empty := indep_empty
  indep_subset := indep_subset
  indep_aug := indep_aug
  indep_maximal X _ := Matroid.existsMaximalSubsetProperty_of_bdd indep_bdd X
  subset_ground := subset_ground

Depends on / 依赖: Quotient, Quotient.lift.decidablePred, decidablePred
-/
@[simps E] protected def ofBdd (E : Set α) (Indep : Set α -> Prop)
    (indep_empty : Indep ∅)
    (indep_subset : forall ⦃I J⦄, Indep J -> I subseteq J -> Indep I)
    (indep_aug : forall ⦃I B⦄, Indep I -> ¬ Maximal Indep I -> Maximal Indep B ->
      exists x in B \ I, Indep (insert x I))
    (subset_ground : forall I, Indep I -> I subseteq E)
    (indep_bdd : exists (n : Nat), forall I, Indep I -> I.encard <= n) : IndepMatroid α where
  E := E
  Indep := Indep
  indep_empty := indep_empty
  indep_subset := indep_subset
  indep_aug := indep_aug
  indep_maximal X _ := Matroid.existsMaximalSubsetProperty_of_bdd indep_bdd X
  subset_ground := subset_ground

/--
theorem `ofBdd_indep` / 定理 `ofBdd_indep`

English:
theorem ofBdd_indep
  statement: (E : Set α) Indep indep_empty indep_subset indep_aug
  proof: rfl

中文:
定理 ofBdd_indep
  结论: (E : Set α) Indep indep_empty indep_subset indep_aug
  证明: rfl

Depends on / 依赖: Quotient, Quotient.lift, decidablePred
-/
@[simp] theorem ofBdd_indep (E : Set α) Indep indep_empty indep_subset indep_aug
    subset_ground h_bdd : (IndepMatroid.ofBdd
      E Indep indep_empty indep_subset indep_aug subset_ground h_bdd).Indep = Indep := rfl

/-- `IndepMatroid.ofBdd` constructs a `RankFinite` matroid. -/
instance (E : Set α) (Indep : Set α -> Prop) indep_empty indep_subset indep_aug subset_ground h_bdd :
    RankFinite (IndepMatroid.ofBdd
      E Indep indep_empty indep_subset indep_aug subset_ground h_bdd).matroid := by
  obtain ⟨B, hB⟩ := (IndepMatroid.ofBdd E Indep _ _ _ _ _).matroid.exists_isBase
  refine hB.rankFinite_of_finite ?_
  obtain ⟨n, hn⟩ := h_bdd
exact finite_of_encard_le_coe hn B (by simpa using hB.indep)

/--
Definition of `ofBddAugment` / `ofBddAugment` 的定义

English:
definition ofBddAugment
  signature: (E : Set α) (Indep : Set α -> Prop)
  body: IndepMatroid.ofBdd (E := E) (Indep := Indep)
    (indep_empty := indep_empty)
    (indep_subset := indep_subset)
    (indep_aug := by
      rintro I B hI hImax hBmax
      suffices hcard : I.encard < B.encard by
        obtain ⟨e, heB, heI, hi⟩ := indep_aug hI hBmax.prop hcard
        exact ⟨e, ⟨heB

中文:
定义 ofBddAugment
  签名: (E : Set α) (Indep : Set α -> 命题)
  定义体: IndepMatroid.ofBdd (E := E) (Indep := Indep)
    (indep_empty := indep_empty)
    (indep_subset := indep_subset)
    (indep_aug := by
      rintro I B hI hImax hBmax
      suffices hcard : I.encard < B.encard by
        obtain ⟨e, heB, heI, hi⟩ := indep_aug hI hBmax.prop hcard
        exact ⟨e, ⟨heB
-/
protected def ofBddAugment (E : Set α) (Indep : Set α -> Prop)
    (indep_empty : Indep ∅)
    (indep_subset : forall ⦃I J⦄, Indep J -> I subseteq J -> Indep I)
    (indep_aug : forall ⦃I J⦄, Indep I -> Indep J -> I.encard < J.encard ->
      exists e in J, e ∉ I ∧ Indep (insert e I))
    (indep_bdd : exists (n : Nat), forall I, Indep I -> I.encard <= n)
    (subset_ground : forall I, Indep I -> I subseteq E) : IndepMatroid α :=
  IndepMatroid.ofBdd (E := E) (Indep := Indep)
    (indep_empty := indep_empty)
    (indep_subset := indep_subset)
    (indep_aug := by
      rintro I B hI hImax hBmax
      suffices hcard : I.encard < B.encard by
        obtain ⟨e, heB, heI, hi⟩ := indep_aug hI hBmax.prop hcard
        exact ⟨e, ⟨heB, heI⟩, hi⟩
      refine lt_of_not_ge fun hle => ?_
      obtain ⟨x, hxnot, hxI⟩ := exists_insert_of_not_maximal indep_subset hI hImax
      have hlt : B.encard < (insert x I).encard := by
        rwa [encard_insert_of_notMem hxnot, ← not_le, ENat.add_one_le_iff, not_lt]
        rw [encard_ne_top_iff]
        obtain ⟨n, hn⟩ := indep_bdd
        exact finite_of_encard_le_coe (hn _ hI)
      obtain ⟨y, -, hyB, hi⟩ := indep_aug hBmax.prop hxI hlt
      exact hBmax.not_prop_of_ssuperset (ssubset_insert hyB) hi)
    (indep_bdd := indep_bdd) (subset_ground := subset_ground)

/--
theorem `ofBddAugment_E` / 定理 `ofBddAugment_E`

English:
theorem ofBddAugment_E
  statement: (E : Set α) Indep indep_empty indep_subset indep_aug
  proof: rfl

中文:
定理 ofBddAugment_E
  结论: (E : Set α) Indep indep_empty indep_subset indep_aug
  证明: rfl
-/
@[simp] theorem ofBddAugment_E (E : Set α) Indep indep_empty indep_subset indep_aug
    indep_bdd subset_ground : (IndepMatroid.ofBddAugment
      E Indep indep_empty indep_subset indep_aug indep_bdd subset_ground).E = E := rfl

/--
theorem `ofBddAugment_indep` / 定理 `ofBddAugment_indep`

English:
theorem ofBddAugment_indep
  statement: (E : Set α) Indep indep_empty indep_subset indep_aug
  proof: rfl

中文:
定理 ofBddAugment_indep
  结论: (E : Set α) Indep indep_empty indep_subset indep_aug
  证明: rfl
-/
@[simp] theorem ofBddAugment_indep (E : Set α) Indep indep_empty indep_subset indep_aug
    indep_bdd subset_ground : (IndepMatroid.ofBddAugment
      E Indep indep_empty indep_subset indep_aug indep_bdd subset_ground).Indep = Indep := rfl

/--
Instance `ofBddAugment_rankFinite` / 实例 `ofBddAugment_rankFinite`

English:
instance ofBddAugment_rankFinite
  signature: (E : Set α) Indep indep_empty indep_subset indep_aug
  body: by
  rw [IndepMatroid.ofBddAugment]
  infer_instance

中文:
实例 ofBddAugment_rankFinite
  签名: (E : Set α) Indep indep_empty indep_subset indep_aug
  定义体: by
  rw [IndepMatroid.ofBddAugment]
  infer_instance

Depends on / 依赖: IndepMatroid, IndepMatroid.ofBddAugment, infer_instance, ofBddAugment
-/
instance ofBddAugment_rankFinite (E : Set α) Indep indep_empty indep_subset indep_aug
    indep_bdd subset_ground : RankFinite (IndepMatroid.ofBddAugment
      E Indep indep_empty indep_subset indep_aug indep_bdd subset_ground).matroid := by
  rw [IndepMatroid.ofBddAugment]
  infer_instance

/--
Definition of `ofFinite` / `ofFinite` 的定义

English:
definition ofFinite
  signature: {E : Set α} (hE : E.Finite) (Indep : Set α -> Prop)
  body: IndepMatroid.ofBddAugment (E := E) (Indep := Indep) (indep_empty := indep_empty)
    (indep_subset := indep_subset)
    (indep_aug := by
      refine fun {I J} hI hJ hIJ => indep_aug hI hJ ?_
      rwa [← Nat.cast_lt (α := Nat∞), (hE.subset (subset_ground hJ)).cast_ncard_eq,
        (hE.subset (subs

中文:
定义 ofFinite
  签名: {E : Set α} (hE : E.Finite) (Indep : Set α -> 命题)
  定义体: IndepMatroid.ofBddAugment (E := E) (Indep := Indep) (indep_empty := indep_empty)
    (indep_subset := indep_subset)
    (indep_aug := by
      refine fun {I J} hI hJ hIJ => indep_aug hI hJ ?_
      rwa [← Nat.cast_lt (α := Nat∞), (hE.subset (subset_ground hJ)).cast_ncard_eq,
        (hE.subset (subs
-/
protected def ofFinite {E : Set α} (hE : E.Finite) (Indep : Set α -> Prop)
    (indep_empty : Indep ∅)
    (indep_subset : forall ⦃I J⦄, Indep J -> I subseteq J -> Indep I)
    (indep_aug :
      forall ⦃I J⦄, Indep I -> Indep J -> I.ncard < J.ncard -> exists e in J, e ∉ I ∧ Indep (insert e I))
    (subset_ground : forall ⦃I⦄, Indep I -> I subseteq E) : IndepMatroid α :=
  IndepMatroid.ofBddAugment (E := E) (Indep := Indep) (indep_empty := indep_empty)
    (indep_subset := indep_subset)
    (indep_aug := by
      refine fun {I J} hI hJ hIJ => indep_aug hI hJ ?_
      rwa [← Nat.cast_lt (α := Nat∞), (hE.subset (subset_ground hJ)).cast_ncard_eq,
        (hE.subset (subset_ground hI)).cast_ncard_eq])
    (indep_bdd := ⟨E.ncard, fun I hI => by
      rw [hE.cast_ncard_eq]
exact encard_le_encard subset_ground hI ⟩)
    (subset_ground := subset_ground)

/--
theorem `ofFinite_E` / 定理 `ofFinite_E`

English:
theorem ofFinite_E
  given: {E : Set α} hE Indep indep_empty indep_subset indep_aug subset_ground
  proof: rfl

中文:
定理 ofFinite_E
  条件: {E : Set α} hE Indep indep_empty indep_subset indep_aug subset_ground
  证明: rfl
-/
@[simp] theorem ofFinite_E {E : Set α} hE Indep indep_empty indep_subset indep_aug subset_ground :
    (IndepMatroid.ofFinite
      (hE : E.Finite) Indep indep_empty indep_subset indep_aug subset_ground).E = E := rfl

/--
theorem `ofFinite_indep` / 定理 `ofFinite_indep`

English:
theorem ofFinite_indep
  statement: {E : Set α} hE Indep indep_empty indep_subset indep_aug
  proof: rfl

中文:
定理 ofFinite_indep
  结论: {E : Set α} hE Indep indep_empty indep_subset indep_aug
  证明: rfl
-/
@[simp] theorem ofFinite_indep {E : Set α} hE Indep indep_empty indep_subset indep_aug
    subset_ground : (IndepMatroid.ofFinite
      (hE : E.Finite) Indep indep_empty indep_subset indep_aug subset_ground).Indep = Indep := rfl

/--
Instance `ofFinite_finite` / 实例 `ofFinite_finite`

English:
instance ofFinite_finite
  signature: {E : Set α} hE Indep indep_empty indep_subset indep_aug subset_ground
  body: ⟨hE⟩

中文:
实例 ofFinite_finite
  签名: {E : Set α} hE Indep indep_empty indep_subset indep_aug subset_ground
  定义体: ⟨hE⟩
-/
instance ofFinite_finite {E : Set α} hE Indep indep_empty indep_subset indep_aug subset_ground :
    (IndepMatroid.ofFinite
      (hE : E.Finite) Indep indep_empty indep_subset indep_aug subset_ground).matroid.Finite :=
  ⟨hE⟩

/--
Definition of `ofFinset` / `ofFinset` 的定义

English:
definition ofFinset
  signature: [DecidableEq α] (E : Set α) (Indep : Finset α -> Prop)
  body: IndepMatroid.ofFinitaryCardAugment
    (E := E)
    (Indep := (fun I => (forall (J : Finset α), (J : Set α) subseteq I -> Indep J)))
    (indep_empty := by simpa [subset_empty_iff])
    (indep_subset := (fun _ _ hJ hIJ _ hKI => hJ _ (hKI.trans hIJ)))
    (indep_aug := by
      intro I J hI hIfin hJ 

中文:
定义 ofFinset
  签名: [DecidableEq α] (E : Set α) (Indep : Finset α -> 命题)
  定义体: IndepMatroid.ofFinitaryCardAugment
    (E := E)
    (Indep := (fun I => (forall (J : Finset α), (J : Set α) subseteq I -> Indep J)))
    (indep_empty := by simpa [subset_empty_iff])
    (indep_subset := (fun _ _ hJ hIJ _ hKI => hJ _ (hKI.trans hIJ)))
    (indep_aug := by
      intro I J hI hIfin hJ 
-/
protected def ofFinset [DecidableEq α] (E : Set α) (Indep : Finset α -> Prop)
    (indep_empty : Indep ∅)
    (indep_subset : forall ⦃I J⦄, Indep J -> I subseteq J -> Indep I)
    (indep_aug : forall ⦃I J⦄, Indep I -> Indep J -> I.card < J.card -> exists e in J, e ∉ I ∧ Indep (insert e I))
    (subset_ground : forall ⦃I⦄, Indep I -> (I : Set α) subseteq E) : IndepMatroid α :=
  IndepMatroid.ofFinitaryCardAugment
    (E := E)
    (Indep := (fun I => (forall (J : Finset α), (J : Set α) subseteq I -> Indep J)))
    (indep_empty := by simpa [subset_empty_iff])
    (indep_subset := (fun _ _ hJ hIJ _ hKI => hJ _ (hKI.trans hIJ)))
    (indep_aug := by
      intro I J hI hIfin hJ hJfin hIJ
      rw [ncard_eq_toFinset_card _ hIfin]; rw [ncard_eq_toFinset_card _ hJfin] at hIJ
      have aug := indep_aug (hI _ (by simp)) (hJ _ (by simp)) hIJ
      simp only [Finite.mem_toFinset] at aug
      obtain ⟨e, heJ, heI, hi⟩ := aug
exact ⟨e, heJ, heI, fun K hK => indep_subset hi Finset.coe_subset.1 (by simpa)⟩ )
    (indep_compact := fun _ h J hJ => h _ hJ J.finite_toSet _ Subset.rfl)
    (subset_ground := fun I hI x hxI => by simpa using subset_ground <| hI {x} (by simpa))

/--
theorem `ofFinset_E` / 定理 `ofFinset_E`

English:
theorem ofFinset_E
  statement: [DecidableEq α] (E : Set α) Indep indep_empty indep_subset indep_aug
  proof: rfl

中文:
定理 ofFinset_E
  结论: [DecidableEq α] (E : Set α) Indep indep_empty indep_subset indep_aug
  证明: rfl
-/
@[simp] theorem ofFinset_E [DecidableEq α] (E : Set α) Indep indep_empty indep_subset indep_aug
    subset_ground : (IndepMatroid.ofFinset
      E Indep indep_empty indep_subset indep_aug subset_ground).E = E := rfl

/--
theorem `ofFinset_indep` / 定理 `ofFinset_indep`

English:
theorem ofFinset_indep
  statement: [DecidableEq α] (E : Set α) Indep indep_empty indep_subset indep_aug
  proof: by
  simp only [IndepMatroid.ofFinset]
  exact ⟨fun h => h _ Subset.rfl, fun h J hJI => indep_subset h hJI⟩

中文:
定理 ofFinset_indep
  结论: [DecidableEq α] (E : Set α) Indep indep_empty indep_subset indep_aug
  证明: by
  simp only [IndepMatroid.ofFinset]
  exact ⟨fun h => h _ Subset.rfl, fun h J hJI => indep_subset h hJI⟩
-/
@[simp] theorem ofFinset_indep [DecidableEq α] (E : Set α) Indep indep_empty indep_subset indep_aug
    subset_ground {I : Finset α} : (IndepMatroid.ofFinset
      E Indep indep_empty indep_subset indep_aug subset_ground).Indep I ↔ Indep I := by
  simp only [IndepMatroid.ofFinset]
  exact ⟨fun h => h _ Subset.rfl, fun h J hJI => indep_subset h hJI⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `ofFinset_indep'` / 定理 `ofFinset_indep'`

English:
theorem ofFinset_indep'
  statement: [DecidableEq α] (E : Set α) Indep indep_empty indep_subset indep_aug
  proof: by
  simp only [IndepMatroid.ofFinset, ofFinitaryCardAugment_indep]

中文:
定理 ofFinset_indep'
  结论: [DecidableEq α] (E : Set α) Indep indep_empty indep_subset indep_aug
  证明: by
  simp only [IndepMatroid.ofFinset, ofFinitaryCardAugment_indep]

Depends on / 依赖: IndepMatroid, IndepMatroid.ofFinset, ofFinitaryCardAugment_indep, ofFinset
-/
theorem ofFinset_indep' [DecidableEq α] (E : Set α) Indep indep_empty indep_subset indep_aug
    subset_ground {I : Set α} : (IndepMatroid.ofFinset
      E Indep indep_empty indep_subset indep_aug subset_ground).Indep I ↔
        forall (J : Finset α), (J : Set α) subseteq I -> Indep J := by
  simp only [IndepMatroid.ofFinset, ofFinitaryCardAugment_indep]

end IndepMatroid

section IsBase

namespace Matroid

/--
Definition of `ofExistsMatroid` / `ofExistsMatroid` 的定义

English:
definition ofExistsMatroid
  signature: (E : Set α) (Indep : Set α -> Prop)
  body: IndepMatroid.matroid
  have hex : exists (M : Matroid α), E = M.E ∧ M.Indep = Indep := by
    obtain ⟨M, rfl, h⟩ := hM; refine ⟨_, rfl, funext (by simp [h])⟩
  IndepMatroid.mk (E := E) (Indep := Indep)
  (indep_empty := by obtain ⟨M, -, rfl⟩ := hex; exact M.empty_indep)
  (indep_subset := by obtain 

中文:
定义 ofExistsMatroid
  签名: (E : Set α) (Indep : Set α -> 命题)
  定义体: IndepMatroid.matroid
  have hex : exists (M : Matroid α), E = M.E ∧ M.Indep = Indep := by
    obtain ⟨M, rfl, h⟩ := hM; refine ⟨_, rfl, funext (by simp [h])⟩
  IndepMatroid.mk (E := E) (Indep := Indep)
  (indep_empty := by obtain ⟨M, -, rfl⟩ := hex; exact M.empty_indep)
  (indep_subset := by obtain 
-/
@[simps! E] protected def ofExistsMatroid (E : Set α) (Indep : Set α -> Prop)
    (hM : exists (M : Matroid α), E = M.E ∧ forall I, M.Indep I ↔ Indep I) : Matroid α :=
IndepMatroid.matroid
  have hex : exists (M : Matroid α), E = M.E ∧ M.Indep = Indep := by
    obtain ⟨M, rfl, h⟩ := hM; refine ⟨_, rfl, funext (by simp [h])⟩
  IndepMatroid.mk (E := E) (Indep := Indep)
  (indep_empty := by obtain ⟨M, -, rfl⟩ := hex; exact M.empty_indep)
  (indep_subset := by obtain ⟨M, -, rfl⟩ := hex; exact fun I J hJ hIJ => hJ.subset hIJ)
  (indep_aug := by obtain ⟨M, -, rfl⟩ := hex; exact Indep.exists_insert_of_not_maximal M)
  (indep_maximal := by obtain ⟨M, rfl, rfl⟩ := hex; exact M.existsMaximalSubsetProperty_indep)
  (subset_ground := by obtain ⟨M, rfl, rfl⟩ := hex; exact fun I => Indep.subset_ground)

/--
Definition of `ofBase` / `ofBase` 的定义

English:
definition ofBase
  signature: (E : Set α) (IsBase : Set α -> Prop) (exists_isBase : exists B, IsBase B)
  body: E
  IsBase := IsBase
  Indep I := (exists B, IsBase B ∧ I subseteq B)
  indep_iff' _ := Iff.rfl
  exists_isBase := exists_isBase
  isBase_exchange := isBase_exchange
  maximality := maximality
  subset_ground := subset_ground

中文:
定义 ofBase
  签名: (E : Set α) (IsBase : Set α -> 命题) (存在_isBase : 存在 B, IsBase B)
  定义体: E
  IsBase := IsBase
  Indep I := (exists B, IsBase B ∧ I subseteq B)
  indep_iff' _ := Iff.rfl
  exists_isBase := exists_isBase
  isBase_exchange := isBase_exchange
  maximality := maximality
  subset_ground := subset_ground
-/
@[simps E] protected def ofBase (E : Set α) (IsBase : Set α -> Prop) (exists_isBase : exists B, IsBase B)
    (isBase_exchange : ExchangeProperty IsBase)
    (maximality : forall X, X subseteq E -> Matroid.ExistsMaximalSubsetProperty (exists B, IsBase B ∧ · subseteq B) X)
    (subset_ground : forall B, IsBase B -> B subseteq E) : Matroid α where
  E := E
  IsBase := IsBase
  Indep I := (exists B, IsBase B ∧ I subseteq B)
  indep_iff' _ := Iff.rfl
  exists_isBase := exists_isBase
  isBase_exchange := isBase_exchange
  maximality := maximality
  subset_ground := subset_ground

/--
Definition of `ofExistsFiniteIsBase` / `ofExistsFiniteIsBase` 的定义

English:
definition ofExistsFiniteIsBase
  signature: (E : Set α) (IsBase : Set α -> Prop)
  body: Matroid.ofBase
  (E := E)
  (IsBase := IsBase)
  (exists_isBase := by obtain ⟨B, h⟩ := exists_finite_base; exact ⟨B, h.1⟩)
  (isBase_exchange := isBase_exchange)
  (maximality := by
    obtain ⟨B, hB, hfin⟩ := exists_finite_base
    refine fun X _ => Matroid.existsMaximalSubsetProperty_of_bdd
      

中文:
定义 ofExistsFiniteIsBase
  签名: (E : Set α) (IsBase : Set α -> 命题)
  定义体: Matroid.ofBase
  (E := E)
  (IsBase := IsBase)
  (exists_isBase := by obtain ⟨B, h⟩ := exists_finite_base; exact ⟨B, h.1⟩)
  (isBase_exchange := isBase_exchange)
  (maximality := by
    obtain ⟨B, hB, hfin⟩ := exists_finite_base
    refine fun X _ => Matroid.existsMaximalSubsetProperty_of_bdd
      
-/
@[simps! E] protected def ofExistsFiniteIsBase (E : Set α) (IsBase : Set α -> Prop)
    (exists_finite_base : exists B, IsBase B ∧ B.Finite) (isBase_exchange : ExchangeProperty IsBase)
    (subset_ground : forall B, IsBase B -> B subseteq E) : Matroid α := Matroid.ofBase
  (E := E)
  (IsBase := IsBase)
  (exists_isBase := by obtain ⟨B, h⟩ := exists_finite_base; exact ⟨B, h.1⟩)
  (isBase_exchange := isBase_exchange)
  (maximality := by
    obtain ⟨B, hB, hfin⟩ := exists_finite_base
    refine fun X _ => Matroid.existsMaximalSubsetProperty_of_bdd
      ⟨B.ncard, fun Y ⟨B', hB', hYB'⟩ => ?_⟩ X
    rw [hfin.cast_ncard_eq]; rw [isBase_exchange.encard_isBase_eq hB hB']
    exact encard_mono hYB')
  (subset_ground := subset_ground)

/--
theorem `ofExistsFiniteIsBase_isBase` / 定理 `ofExistsFiniteIsBase_isBase`

English:
theorem ofExistsFiniteIsBase_isBase
  statement: (E : Set α) IsBase exists_finite_base
  proof: rfl

中文:
定理 ofExistsFiniteIsBase_isBase
  结论: (E : Set α) IsBase 存在_finite_base
  证明: rfl
-/
@[simp] theorem ofExistsFiniteIsBase_isBase (E : Set α) IsBase exists_finite_base
    isBase_exchange subset_ground : (Matroid.ofExistsFiniteIsBase
      E IsBase exists_finite_base isBase_exchange subset_ground).IsBase = IsBase := rfl

/--
Instance `ofExistsFiniteIsBase_rankFinite` / 实例 `ofExistsFiniteIsBase_rankFinite`

English:
instance ofExistsFiniteIsBase_rankFinite
  signature: (E : Set α) IsBase exists_finite_base
  body: by
  obtain ⟨B, hB, hfin⟩ := exists_finite_base
  exact Matroid.IsBase.rankFinite_of_finite (by simpa) hfin

中文:
实例 ofExistsFiniteIsBase_rankFinite
  签名: (E : Set α) IsBase 存在_finite_base
  定义体: by
  obtain ⟨B, hB, hfin⟩ := exists_finite_base
  exact Matroid.IsBase.rankFinite_of_finite (by simpa) hfin

Depends on / 依赖: IsBase, Matroid, Matroid.IsBase.rankFinite_of_finite, exists_finite_base, rankFinite_of_finite
-/
instance ofExistsFiniteIsBase_rankFinite (E : Set α) IsBase exists_finite_base
    isBase_exchange subset_ground : RankFinite (Matroid.ofExistsFiniteIsBase
      E IsBase exists_finite_base isBase_exchange subset_ground) := by
  obtain ⟨B, hB, hfin⟩ := exists_finite_base
  exact Matroid.IsBase.rankFinite_of_finite (by simpa) hfin

/--
Definition of `ofIsBaseOfFinite` / `ofIsBaseOfFinite` 的定义

English:
definition ofIsBaseOfFinite
  signature: {E : Set α} (hE : E.Finite) (IsBase : Set α -> Prop)
  body: Matroid.ofExistsFiniteIsBase (E := E) (IsBase := IsBase)
    (exists_finite_base :=
      let ⟨B, hB⟩ := exists_isBase
      ⟨B, hB, hE.subset (subset_ground B hB)⟩)
    (isBase_exchange := isBase_exchange)
    (subset_ground := subset_ground)

中文:
定义 ofIsBaseOfFinite
  签名: {E : Set α} (hE : E.Finite) (IsBase : Set α -> 命题)
  定义体: Matroid.ofExistsFiniteIsBase (E := E) (IsBase := IsBase)
    (exists_finite_base :=
      let ⟨B, hB⟩ := exists_isBase
      ⟨B, hB, hE.subset (subset_ground B hB)⟩)
    (isBase_exchange := isBase_exchange)
    (subset_ground := subset_ground)
-/
protected def ofIsBaseOfFinite {E : Set α} (hE : E.Finite) (IsBase : Set α -> Prop)
    (exists_isBase : exists B, IsBase B) (isBase_exchange : ExchangeProperty IsBase)
    (subset_ground : forall B, IsBase B -> B subseteq E) : Matroid α :=
  Matroid.ofExistsFiniteIsBase (E := E) (IsBase := IsBase)
    (exists_finite_base :=
      let ⟨B, hB⟩ := exists_isBase
      ⟨B, hB, hE.subset (subset_ground B hB)⟩)
    (isBase_exchange := isBase_exchange)
    (subset_ground := subset_ground)

/--
theorem `ofIsBaseOfFinite_E` / 定理 `ofIsBaseOfFinite_E`

English:
theorem ofIsBaseOfFinite_E
  statement: {E : Set α} (hE : E.Finite) IsBase exists_isBase isBase_exchange
  proof: rfl

中文:
定理 ofIsBaseOfFinite_E
  结论: {E : Set α} (hE : E.Finite) IsBase 存在_isBase isBase_exchange
  证明: rfl
-/
@[simp] theorem ofIsBaseOfFinite_E {E : Set α} (hE : E.Finite) IsBase exists_isBase isBase_exchange
    subset_ground : (Matroid.ofIsBaseOfFinite
      hE IsBase exists_isBase isBase_exchange subset_ground).E = E := rfl

/--
theorem `ofIsBaseOfFinite_isBase` / 定理 `ofIsBaseOfFinite_isBase`

English:
theorem ofIsBaseOfFinite_isBase
  statement: {E : Set α} (hE : E.Finite) IsBase exists_isBase
  proof: rfl

中文:
定理 ofIsBaseOfFinite_isBase
  结论: {E : Set α} (hE : E.Finite) IsBase 存在_isBase
  证明: rfl
-/
@[simp] theorem ofIsBaseOfFinite_isBase {E : Set α} (hE : E.Finite) IsBase exists_isBase
    isBase_exchange subset_ground : (Matroid.ofIsBaseOfFinite
      hE IsBase exists_isBase isBase_exchange subset_ground).IsBase = IsBase := rfl

/--
Instance `ofBaseOfFinite_finite` / 实例 `ofBaseOfFinite_finite`

English:
instance ofBaseOfFinite_finite
  signature: {E : Set α} (hE : E.Finite) IsBase exists_isBase
  body: ⟨hE⟩

中文:
实例 ofBaseOfFinite_finite
  签名: {E : Set α} (hE : E.Finite) IsBase 存在_isBase
  定义体: ⟨hE⟩
-/
instance ofBaseOfFinite_finite {E : Set α} (hE : E.Finite) IsBase exists_isBase
    isBase_exchange subset_ground : (Matroid.ofIsBaseOfFinite
      hE IsBase exists_isBase isBase_exchange subset_ground).Finite :=
  ⟨hE⟩

end Matroid

end IsBase

end IndepMatroid
