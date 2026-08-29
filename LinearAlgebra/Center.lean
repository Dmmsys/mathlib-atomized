/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

module

public import Mathlib.LinearAlgebra.Transvection.Basic

/-!
# Center of the algebra of linear endomorphisms

If `V` is an `R`-module, we say that an endomorphism `f : Module.End R V`
is a *homothety* with central ratio if there exists `a ∈ Set.center R`
such that `f x = a • x` for all `x`.
By `Module.End.mem_subsemiringCenter_iff`, these linear maps constitute
the center of `Module.End R V`.
(When `R` is commutative, we can write `f = a • LinearMap.id`.)

In what follows, `V` is assumed to be a free `R`-module.

* `LinearMap.commute_transvections_iff_of_basis`:
  if an endomorphism `f : V →ₗ[R] V` commutes with every elementary transvection
  (in a given basis), then it is a homothety with central ratio.
  (Assumes that the basis is provided and has a non trivial set of indices.)

* `LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent`:
  over a commutative ring `R` which is a domain, an endomorphism `f : V →ₗ[R] V`
  of a free module such that `v` and `f v` are not linearly independent,
  for all `v : V`, is a homothety.

* `LinearMap.exists_mem_center_apply_eq_smul_of_forall_notLinearIndependent`:
  a variant that does not assume that `R` is commutative.
  Then the homothety has central ratio.

* `LinearMap.exists_mem_center_apply_eq_smul_of_forall_notLinearIndependent_of_basis`:
  a variant that does not assume that `R` has the strong rank condition,
  but requires a basis.

Note. In the noncommutative case, the last two results do not hold
when the rank is equal to 1. Indeed, right multiplications
with noncentral ratio of the `R`-module `R` satisfy the property
that `f v` and `v` are linearly dependent, for all `v : V`,
but they are not left multiplication by some element.

-/

public section

open Module LinearMap LinearEquiv Set Finsupp

namespace LinearMap

variable {R V : Type*}

/--
theorem `mem_center_of_apply_eq_smul` / 定理 `mem_center_of_apply_eq_smul`

English:
theorem mem_center_of_apply_eq_smul
  statement: [Semiring R] [AddCommMonoid V]
  proof: by
  simp [mem_center_iff, isMulCentral_iff, commute_iff_eq, mul_assoc, LinearMap.ext_iff, hf]

中文:
定理 mem_center_of_apply_eq_smul
  结论: [Semiring R] [AddCommMonoid V]
  证明: by
  simp [mem_center_iff, isMulCentral_iff, commute_iff_eq, mul_assoc, LinearMap.ext_iff, hf]

Depends on / 依赖: LinearMap, LinearMap.ext_iff, commute_iff_eq, ext_iff, isMulCentral_iff, mem_center_iff, mul_assoc
-/
theorem mem_center_of_apply_eq_smul [Semiring R] [AddCommMonoid V]
    [Module R V] {f : V ->ₗ[R] V} {a : R}
    (hf : forall x, f x = a • x) :
    f in center (End R V) := by
  simp [mem_center_iff, isMulCentral_iff, commute_iff_eq, mul_assoc, LinearMap.ext_iff, hf]

/--
theorem `commute_transvections_iff_of_basis` / 定理 `commute_transvections_iff_of_basis`

English:
theorem commute_transvections_iff_of_basis
  proof: by
  simp only [SetLike.exists, Subring.mem_center_iff]
  rcases subsingleton_or_nontrivial V with hV | hV
  · refine ⟨1, by simp, ?_⟩
    ext x
    simp [Subring.smul_def, hV.allEq (f x) x]
  simp only [commute_iff_eq] at hcomm
  replace hcomm (i j : ι) (hij : i != j) (r : R) :
      r • f (b j) = 

中文:
定理 commute_transvections_iff_of_basis
  证明: by
  simp only [SetLike.exists, Subring.mem_center_iff]
  rcases subsingleton_or_nontrivial V with hV | hV
  · refine ⟨1, by simp, ?_⟩
    ext x
    simp [Subring.smul_def, hV.allEq (f x) x]
  simp only [commute_iff_eq] at hcomm
  replace hcomm (i j : ι) (hij : i != j) (r : R) :
      r • f (b j) = 

Depends on / 依赖: LinearMap, LinearMap.ext_iff, LinearMap.transvection.apply, SetLike, SetLike.exists, Subring, Subring.mem_center_iff, Subring.smul_def, b.coord, by_cas, commute_iff_eq, ext_iff, hV.allEq, h_allEq, mem_center_iff, replace, smul_def, subsingleton_or_nontrivial, transvection
-/
theorem commute_transvections_iff_of_basis
    [Ring R] [AddCommGroup V] [Module R V]
    {ι : Type*} [Nontrivial ι] (b : Basis ι R V)
    {f : V ->ₗ[R] V}
    (hcomm : forall i j (r : R) (_ : i != j), Commute f (transvection (b.coord i) (r • b j))) :
    exists a : Subring.center R, f = a • 1 := by
  simp only [SetLike.exists, Subring.mem_center_iff]
  rcases subsingleton_or_nontrivial V with hV | hV
  · refine ⟨1, by simp, ?_⟩
    ext x
    simp [Subring.smul_def, hV.allEq (f x) x]
  simp only [commute_iff_eq] at hcomm
  replace hcomm (i j : ι) (hij : i != j) (r : R) :
      r • f (b j) = b.coord i (f (b i)) • r • b j := by
    have := hcomm i j r hij
    rw [LinearMap.ext_iff] at this
    simpa [LinearMap.transvection.apply] using this (b i)
  have h_allEq (i j : ι) : b.coord i (f (b i)) = b.coord j (f (b j)) := by
    by_cases hij : j = i
    · simp [hij]
    simpa using congr_arg (b.coord i) (hcomm j i hij 1)
  replace hcomm (i : ι) (r : R) : r • f (b i) = b.coord i (f (b i)) • r • b i := by
    obtain ⟨j, hji⟩ := exists_ne i
    simpa [h_allEq j i] using hcomm j i hji r
  let i : ι := Classical.ofNonempty
  refine ⟨b.coord i (f (b i)), fun r => by simpa using congr(b.coord i $(hcomm i r)), ?_⟩
  ext x
  rw [← b.linearCombination_repr x]; rw [linearCombination_apply]; rw [map_finsuppSum]
  simp only [smul_apply, End.one_apply, smul_sum]
  apply sum_congr
  intro j _
  simp [Subring.smul_def, h_allEq i j, hcomm j]

/--
theorem `exists_mem_center_apply_eq_smul_of_forall_notLinearIndependent_of_basis` / 定理 `exists_mem_center_apply_eq_smul_of_forall_notLinearIndependent_of_basis`

English:
theorem exists_mem_center_apply_eq_smul_of_forall_notLinearIndependent_of_basis
  proof: by
  -- We make the linear dependence condition explicit
  have feq (i) : f (b i) = (b.coord i) (f (b i)) • b i := by
    classical
    rw [b.ext_elem_iff]
    intro j
    simp only [LinearIndependent.pair_iff, not_forall] at h
    obtain ⟨s, t, ⟨h, h'⟩⟩ := h (b i)
    simp only [Basis.coord_apply, 

中文:
定理 exists_mem_center_apply_eq_smul_of_forall_notLinearIndependent_of_basis
  证明: by
  -- We make the linear dependence condition explicit
  have feq (i) : f (b i) = (b.coord i) (f (b i)) • b i := by
    classical
    rw [b.ext_elem_iff]
    intro j
    simp only [LinearIndependent.pair_iff, not_forall] at h
    obtain ⟨s, t, ⟨h, h'⟩⟩ := h (b i)
    simp only [Basis.coord_apply, 
-/
theorem exists_mem_center_apply_eq_smul_of_forall_notLinearIndependent_of_basis
    [Ring R] [IsDomain R] [AddCommGroup V] [Module R V]
    {f : V ->ₗ[R] V}
    {ι : Type*} [Nontrivial ι] (b : Basis ι R V)
    (h : forall v, ¬ LinearIndependent R ![v, f v]) :
    exists a : Subring.center R, f = a • 1 := by
  -- We make the linear dependence condition explicit
  have feq (i) : f (b i) = (b.coord i) (f (b i)) • b i := by
    classical
    rw [b.ext_elem_iff]
    intro j
    simp only [LinearIndependent.pair_iff, not_forall] at h
    obtain ⟨s, t, ⟨h, h'⟩⟩ := h (b i)
    simp only [Basis.coord_apply, _root_.map_smul, Basis.repr_self, smul_single,
      smul_eq_mul, mul_one, Finsupp.single_apply]
    split_ifs with hj
    · simp [hj]
    · have : t = 0 ∨ b.repr (f (b i)) j = 0 := by
        rw [b.ext_elem_iff] at h
        simpa [single_eq_of_ne' hj] using h j
      apply Or.resolve_left this
      contrapose h'
      refine ⟨?_, h'⟩
      simp only [h', zero_smul, add_zero] at h
      contrapose hj
      apply b.linearIndependent.eq_of_smul_apply_eq_smul_apply s 0 i j hj
      simpa using h
  have h' (i j) (hij : i != j) (r : R) : b.coord i (f (b i)) * r = r * b.coord j (f (b j)) := by
    -- we use that `f (b i + r • b j)` is a multiple of `b i + r • b j`
    let x := b.repr.symm ((Finsupp.single i 1).update j r)
    specialize h x
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd,
      LinearIndependent.pair_iff, not_forall, not_and] at h
    obtain ⟨s, t, h, hst⟩ := h
    simp only [b.ext_elem_iff, map_add, _root_.map_smul, coe_add, Finsupp.coe_smul,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply] at h
    have hx : x = b i + r • b j := by
      simp only [Basis.repr_symm_apply, linearCombination_apply, x]
      rw [← add_right_cancel_iff]; rw [sum_update_add] <;>
        simp [single_eq_of_ne' hij, add_smul]
    have h1 : s + t * (b.coord i (f (b i))) = 0 := by
      suffices s + t * ((b.repr (f (b i))) i + r * (b.repr (f (b j))) i) = 0 by
        rw [mul_add]; rw [← add_assoc]; rw [← mul_assoc]; rw [add_eq_zero_iff_eq_neg] at this
        rw [Basis.coord_apply]; rw [this]; rw [feq]
        simp [single_eq_of_ne hij]
      simpa [hx, single_eq_of_ne hij] using h i
    have h2 : s * r + t * r * b.coord j (f (b j)) = 0 := by
      suffices s * r + t * ((b.repr (f (b i))) j + r * (b.repr (f (b j))) j) = 0 by
        rw [mul_add]; rw [← add_assoc]; rw [add_right_comm]; rw [add_eq_zero_iff_eq_neg]; rw [← mul_assoc] at this
        rw [Basis.coord_apply]; rw [this]; rw [feq]
        simp [single_eq_of_ne' hij]
      simpa [hx, single_eq_same, single_eq_of_ne' hij] using h j
    rw [add_eq_zero_iff_eq_neg] at h1
    rw [h1]; rw [neg_mul]; rw [neg_add_eq_sub]; rw [mul_assoc]; rw [mul_assoc]; rw [← mul_sub]; rw [mul_eq_zero]; rw [sub_eq_zero] at h2
    symm
    apply Or.resolve_left h2
    contrapose hst; simp [h1, hst]
  -- This generalizes the equality formerly known as `feq`
  replace feq (i j) : f (b j) = b.coord i (f (b i)) • b j := by
    by_cases hij : i = j
    · rw [← hij, ← feq]
    · have := h' i j hij 1
      simp only [mul_one, one_mul] at this
      rw [feq]; rw [← this]
  let i : ι := Classical.ofNonempty
  have ha (r) : Commute (b.coord i (f (b i))) r := by
    obtain ⟨j, hij⟩ := exists_ne i
    rw [commute_iff_eq]; rw [h' i j (Ne.symm hij)]; rw [feq i j]; rw [feq i i]
    simp
  refine ⟨⟨b.coord i (f (b i)), ?_⟩, ?_⟩
  · simpa [Subring.mem_center_iff, commute_iff_eq, eq_comm] using ha
  apply b.ext
  simpa only [smul_apply, End.one_apply, Subring.smul_def] using feq i

/--
theorem `exists_mem_center_apply_eq_smul_of_forall_notLinearIndependent` / 定理 `exists_mem_center_apply_eq_smul_of_forall_notLinearIndependent`

English:
theorem exists_mem_center_apply_eq_smul_of_forall_notLinearIndependent
  proof: by
  rcases subsingleton_or_nontrivial V with hV | hV
  · use 1
    ext x
    apply hV.allEq
  let ι := Free.ChooseBasisIndex R V
  let b : Basis ι R V := Free.chooseBasis R V
  rcases subsingleton_or_nontrivial ι with hι | hι
  · have : Nonempty ι := Free.instNonemptyChooseBasisIndexOfNontrivial R 

中文:
定理 exists_mem_center_apply_eq_smul_of_forall_notLinearIndependent
  证明: by
  rcases subsingleton_or_nontrivial V with hV | hV
  · use 1
    ext x
    apply hV.allEq
  let ι := Free.ChooseBasisIndex R V
  let b : Basis ι R V := Free.chooseBasis R V
  rcases subsingleton_or_nontrivial ι with hι | hι
  · have : Nonempty ι := Free.instNonemptyChooseBasisIndexOfNontrivial R 

Depends on / 依赖: ChooseBasisIndex, Fintype, Fintype.ofFinite, Free.ChooseBasisIndex, Free.chooseBasis, Free.instNonemptyChooseBasisIndexOfNontrivial, Nat.card_eq_fintype_card, Nonempty, card_eq_fintype_card, chooseBasis, exists_mem_center_apply_eq_smul_of_forall_notLinearIndependent_of_basis, finrank_eq_card_basis, hV.allEq, instNonemptyChooseBasisIndexOfNontrivial, ofFinite, subsingleton_or_nontrivial
-/
theorem exists_mem_center_apply_eq_smul_of_forall_notLinearIndependent
    [Ring R] [IsDomain R] [StrongRankCondition R]
    [AddCommGroup V] [Module R V] [Free R V]
    {f : V ->ₗ[R] V}
    (hV1 : finrank R V != 1)
    (h : forall v, ¬ LinearIndependent R ![v, f v]) :
    exists a : Subring.center R, f = a • 1 := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · use 1
    ext x
    apply hV.allEq
  let ι := Free.ChooseBasisIndex R V
  let b : Basis ι R V := Free.chooseBasis R V
  rcases subsingleton_or_nontrivial ι with hι | hι
  · have : Nonempty ι := Free.instNonemptyChooseBasisIndexOfNontrivial R V
    have : Fintype ι := Fintype.ofFinite ι
    simp_all [finrank_eq_card_basis b, ← Nat.card_eq_fintype_card]
  exact exists_mem_center_apply_eq_smul_of_forall_notLinearIndependent_of_basis b h

/--
theorem `exists_eq_smul_id_of_forall_notLinearIndependent` / 定理 `exists_eq_smul_id_of_forall_notLinearIndependent`

English:
theorem exists_eq_smul_id_of_forall_notLinearIndependent
  proof: by
  by_cases hV1 : finrank R V = 1
  · rw [finrank_eq_one_iff Unit] at hV1
    let b : Basis Unit R V := Classical.ofNonempty
    use b.coord () (f (b ()))
    apply b.ext
    intro i
    nth_rewrite 1 [← b.linearCombination_repr (f (b i))]
    simp [linearCombination_unique]
  obtain ⟨a, rfl⟩ := e

中文:
定理 exists_eq_smul_id_of_forall_notLinearIndependent
  证明: by
  by_cases hV1 : finrank R V = 1
  · rw [finrank_eq_one_iff Unit] at hV1
    let b : Basis Unit R V := Classical.ofNonempty
    use b.coord () (f (b ()))
    apply b.ext
    intro i
    nth_rewrite 1 [← b.linearCombination_repr (f (b i))]
    simp [linearCombination_unique]
  obtain ⟨a, rfl⟩ := e

Depends on / 依赖: Classical, Classical.ofNonempty, Subring, Subring.smul_def, b.coord, b.ext, b.linearCombination_repr, exists_mem_center_apply_eq_smul_of_forall_notLinearIndependent, finrank, finrank_eq_one_iff, linearCombination_repr, linearCombination_unique, nth_rewrite, ofNonempty, smul_def
-/
theorem exists_eq_smul_id_of_forall_notLinearIndependent
    [CommRing R] [IsDomain R] [AddCommGroup V] [Module R V] [Free R V] {f : V ->ₗ[R] V}
    (h : forall v, ¬ LinearIndependent R ![v, f v]) :
    exists a : R, f = a • 1 := by
  by_cases hV1 : finrank R V = 1
  · rw [finrank_eq_one_iff Unit] at hV1
    let b : Basis Unit R V := Classical.ofNonempty
    use b.coord () (f (b ()))
    apply b.ext
    intro i
    nth_rewrite 1 [← b.linearCombination_repr (f (b i))]
    simp [linearCombination_unique]
  obtain ⟨a, rfl⟩ := exists_mem_center_apply_eq_smul_of_forall_notLinearIndependent hV1 h
  refine ⟨a, by simp [Subring.smul_def]⟩

end LinearMap
