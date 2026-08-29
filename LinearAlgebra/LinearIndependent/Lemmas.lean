/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Alexander Bentkamp, Anne Baanen
-/
module

public import Mathlib.Data.Fin.Tuple.Reflection
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Finsupp.SumProd
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum.Ineq

import Mathlib.Algebra.Module.Torsion.Field

/-!
# Linear independence

This file collects consequences of linear (in)dependence and includes specialized tests for
specific families of vectors, requiring more theory to state.

## Main statements

We prove several specialized tests for linear independence of families of vectors and of sets of
vectors.

* `linearIndependent_option`, `linearIndependent_finCons`,
  `linearIndependent_finSucc`, `linearIndependent_finSnoc`: type-specific tests for linear
  independence of families of vector fields;
* `linearIndependent_insert`, `linearIndependent_pair`: linear independence tests for set operations

In many cases we additionally provide dot-style operations (e.g., `LinearIndependent.union`) to
make the linear independence tests usable as `hv.insert ha` etc.

We also prove that, when working over a division ring,
any family of vectors includes a linear independent subfamily spanning the same subspace.

## TODO

Rework proofs to hold in semirings, by avoiding the path through
`ker (Finsupp.linearCombination R v) = ⊥`.

## Tags

linearly dependent, linear dependence, linearly independent, linear independence

-/

@[expose] public section


assert_not_exists Cardinal

noncomputable section

open Function Module Set Submodule

universe u' u

variable {ι : Type u'} {ι' : Type*} {R : Type*} {K : Type*} {s : Set ι}
variable {M : Type*} {M' : Type*} {V : Type u}

section Semiring


variable {v : ι -> M}
variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M']
variable [Module R M] [Module R M']
variable (R) (v)

variable {R v}

/--
theorem `Fintype.linearIndependent_iff'ₛ` / 定理 `Fintype.linearIndependent_iff'ₛ`

English:
theorem Fintype.linearIndependent_iff'ₛ
  given: [Fintype ι] [DecidableEq ι]
  proof: by
  simp [Fintype.linearIndependent_iffₛ, Injective, funext_iff]

中文:
定理 有限类型.linearIndependent_iff'ₛ
  条件: [有限类型 ι] [DecidableEq ι]
  证明: by
  simp [Fintype.linearIndependent_iffₛ, Injective, funext_iff]

Depends on / 依赖: Fintype, Fintype.linearIndependent_iff, Injective, funext_iff
-/
theorem Fintype.linearIndependent_iff'ₛ [Fintype ι] [DecidableEq ι] :
    LinearIndependent R v ↔
      Injective (LinearMap.lsum R (fun _ => R) Nat fun i => LinearMap.id.smulRight (v i)) := by
  simp [Fintype.linearIndependent_iffₛ, Injective, funext_iff]

/--
lemma `LinearIndependent.pair_iffₛ` / 引理 `LinearIndependent.pair_iffₛ`

English:
lemma LinearIndependent.pair_iffₛ
  given: {x y : M}
  proof: by
  simp [Fintype.linearIndependent_iffₛ, Fin.forall_fin_two, ← FinVec.forall_iff]; rfl

中文:
引理 LinearIndependent.pair_iffₛ
  条件: {x y : M}
  证明: by
  simp [Fintype.linearIndependent_iffₛ, Fin.forall_fin_two, ← FinVec.forall_iff]; rfl

Depends on / 依赖: Fin.forall_fin_two, FinVec, FinVec.forall_iff, Fintype, Fintype.linearIndependent_iff, forall_fin_two, forall_iff
-/
lemma LinearIndependent.pair_iffₛ {x y : M} :
    LinearIndependent R ![x, y] ↔
      forall (s t s' t' : R), s • x + t • y = s' • x + t' • y -> s = s' ∧ t = t' := by
  simp [Fintype.linearIndependent_iffₛ, Fin.forall_fin_two, ← FinVec.forall_iff]; rfl

/--
lemma `LinearIndependent.eq_of_pair` / 引理 `LinearIndependent.eq_of_pair`

English:
lemma LinearIndependent.eq_of_pair
  statement: {x y : M} (h : LinearIndependent R ![x, y])
  proof: pair_iffₛ.mp h _ _ _ _ h'

中文:
引理 LinearIndependent.eq_of_pair
  结论: {x y : M} (h : LinearIndependent R ![x, y])
  证明: pair_iffₛ.mp h _ _ _ _ h'
-/
lemma LinearIndependent.eq_of_pair {x y : M} (h : LinearIndependent R ![x, y])
    {s t s' t' : R} (h' : s • x + t • y = s' • x + t' • y) : s = s' ∧ t = t' :=
  pair_iffₛ.mp h _ _ _ _ h'

/--
lemma `LinearIndependent.eq_zero_of_pair'` / 引理 `LinearIndependent.eq_zero_of_pair'`

English:
lemma LinearIndependent.eq_zero_of_pair'
  statement: {x y : M} (h : LinearIndependent R ![x, y])
  proof: by
  suffices H : s = 0 ∧ 0 = t from ⟨H.1, H.2.symm⟩
  exact h.eq_of_pair (by simpa using h')

中文:
引理 LinearIndependent.eq_zero_of_pair'
  结论: {x y : M} (h : LinearIndependent R ![x, y])
  证明: by
  suffices H : s = 0 ∧ 0 = t from ⟨H.1, H.2.symm⟩
  exact h.eq_of_pair (by simpa using h')

Depends on / 依赖: eq_of_pair, h.eq_of_pair
-/
lemma LinearIndependent.eq_zero_of_pair' {x y : M} (h : LinearIndependent R ![x, y])
    {s t : R} (h' : s • x = t • y) : s = 0 ∧ t = 0 := by
  suffices H : s = 0 ∧ 0 = t from ⟨H.1, H.2.symm⟩
  exact h.eq_of_pair (by simpa using h')

/--
lemma `LinearIndependent.eq_zero_of_pair` / 引理 `LinearIndependent.eq_zero_of_pair`

English:
lemma LinearIndependent.eq_zero_of_pair
  statement: {x y : M} (h : LinearIndependent R ![x, y])
  proof: by
  replace h := @h (.single 0 s + .single 1 t) 0 ?_
  · exact ⟨by simpa using congr($h 0), by simpa using congr($h 1)⟩
  simpa

中文:
引理 LinearIndependent.eq_zero_of_pair
  结论: {x y : M} (h : LinearIndependent R ![x, y])
  证明: by
  replace h := @h (.single 0 s + .single 1 t) 0 ?_
  · exact ⟨by simpa using congr($h 0), by simpa using congr($h 1)⟩
  simpa

Depends on / 依赖: replace, single
-/
lemma LinearIndependent.eq_zero_of_pair {x y : M} (h : LinearIndependent R ![x, y])
    {s t : R} (h' : s • x + t • y = 0) : s = 0 ∧ t = 0 := by
  replace h := @h (.single 0 s + .single 1 t) 0 ?_
  · exact ⟨by simpa using congr($h 0), by simpa using congr($h 1)⟩
  simpa

section Indexed

/--
theorem `linearIndepOn_iUnion_of_directed` / 定理 `linearIndepOn_iUnion_of_directed`

English:
theorem linearIndepOn_iUnion_of_directed
  statement: {η : Type*} {s : η -> Set ι} (hs : Directed (· subseteq ·) s)
  proof: by
  by_cases hη : Nonempty η
  · refine linearIndepOn_of_finite (⋃ i, s i) fun t ht ft => ?_
    rcases finite_subset_iUnion ft ht with ⟨I, fi, hI⟩
    rcases hs.finset_le fi.toFinset with ⟨i, hi⟩
    exact (h i).mono (Subset.trans hI <| iUnion₂_subset fun j hj => hi j (fi.mem_toFinset.2 hj))
  · refine (linearIndepOn_empty R v).mono (t := iUnion (s ·)) ?_
    rintro _ ⟨_, ⟨i, _⟩, _⟩
    exact hη ⟨i⟩

中文:
定理 linearIndepOn_iUnion_of_directed
  结论: {η : 类型} {s : η -> 集合 ι} (hs : Directed (· subseteq ·) s)
  证明: by
  by_cases hη : Nonempty η
  · refine linearIndepOn_of_finite (⋃ i, s i) fun t ht ft => ?_
    rcases finite_subset_iUnion ft ht with ⟨I, fi, hI⟩
    rcases hs.finset_le fi.toFinset with ⟨i, hi⟩
    exact (h i).mono (Subset.trans hI <| iUnion₂_subset fun j hj => hi j (fi.mem_toFinset.2 hj))
  · refine (linearIndepOn_empty R v).mono (t := iUnion (s ·)) ?_
    rintro _ ⟨_, ⟨i, _⟩, _⟩
    exact hη ⟨i⟩

Depends on / 依赖: Nonempty, Subset, Subset.trans, fi.mem_toFinset, fi.toFinset, finite_subset_iUnion, finset_le, hs.finset_le, iUnion, linearIndepOn_empty, linearIndepOn_of_finite, mem_toFinset, toFinset
-/
theorem linearIndepOn_iUnion_of_directed {η : Type*} {s : η -> Set ι} (hs : Directed (· subseteq ·) s)
    (h : forall i, LinearIndepOn R v (s i)) : LinearIndepOn R v (⋃ i, s i) := by
  by_cases hη : Nonempty η
  · refine linearIndepOn_of_finite (⋃ i, s i) fun t ht ft => ?_
    rcases finite_subset_iUnion ft ht with ⟨I, fi, hI⟩
    rcases hs.finset_le fi.toFinset with ⟨i, hi⟩
    exact (h i).mono (Subset.trans hI <| iUnion₂_subset fun j hj => hi j (fi.mem_toFinset.2 hj))
  · refine (linearIndepOn_empty R v).mono (t := iUnion (s ·)) ?_
    rintro _ ⟨_, ⟨i, _⟩, _⟩
    exact hη ⟨i⟩

/--
theorem `linearIndepOn_sUnion_of_directed` / 定理 `linearIndepOn_sUnion_of_directed`

English:
theorem linearIndepOn_sUnion_of_directed
  statement: {s : Set (Set ι)} (hs : DirectedOn (· subseteq ·) s)
  proof: by
  rw [sUnion_eq_iUnion]
  exact linearIndepOn_iUnion_of_directed hs.directed_val (by simpa using h)

中文:
定理 linearIndepOn_sUnion_of_directed
  结论: {s : 集合 (集合 ι)} (hs : DirectedOn (· subseteq ·) s)
  证明: by
  rw [sUnion_eq_iUnion]
  exact linearIndepOn_iUnion_of_directed hs.directed_val (by simpa using h)

Depends on / 依赖: directed_val, hs.directed_val, linearIndepOn_iUnion_of_directed, sUnion_eq_iUnion
-/
theorem linearIndepOn_sUnion_of_directed {s : Set (Set ι)} (hs : DirectedOn (· subseteq ·) s)
    (h : forall a in s, LinearIndepOn R v a) : LinearIndepOn R v (⋃₀ s) := by
  rw [sUnion_eq_iUnion]
  exact linearIndepOn_iUnion_of_directed hs.directed_val (by simpa using h)

/--
theorem `linearIndepOn_biUnion_of_directed` / 定理 `linearIndepOn_biUnion_of_directed`

English:
theorem linearIndepOn_biUnion_of_directed
  statement: {η} {s : Set η} {t : η -> Set ι}
  proof: by
  rw [biUnion_eq_iUnion]
  exact linearIndepOn_iUnion_of_directed (directed_comp.2 <| hs.directed_val) (by simpa using h)

中文:
定理 linearIndepOn_biUnion_of_directed
  结论: {η} {s : 集合 η} {t : η -> 集合 ι}
  证明: by
  rw [biUnion_eq_iUnion]
  exact linearIndepOn_iUnion_of_directed (directed_comp.2 <| hs.directed_val) (by simpa using h)

Depends on / 依赖: biUnion_eq_iUnion, directed_comp, directed_val, hs.directed_val, linearIndepOn_iUnion_of_directed
-/
theorem linearIndepOn_biUnion_of_directed {η} {s : Set η} {t : η -> Set ι}
    (hs : DirectedOn (t ⁻¹'o (· subseteq ·)) s) (h : forall a in s, LinearIndepOn R v (t a)) :
    LinearIndepOn R v (⋃ a in s, t a) := by
  rw [biUnion_eq_iUnion]
  exact linearIndepOn_iUnion_of_directed (directed_comp.2 <| hs.directed_val) (by simpa using h)

end Indexed

section repr

variable (ι R M) in
/--
theorem `iSupIndep_range_lsingle` / 定理 `iSupIndep_range_lsingle`

English:
theorem iSupIndep_range_lsingle
  proof: by
  refine fun i => disjoint_iff_inf_le.mpr ?_
  rintro x ⟨⟨m, rfl⟩, hm⟩
  suffices ⨆ j != i, LinearMap.range (Finsupp.lsingle j) <= Finsupp.supported M R {i}ᶜ by
    have := (Finsupp.mem_supported ..).mp (this hm); simp_all
  refine iSup₂_le fun j ne => ?_
  rintro _ ⟨m, rfl⟩
  simp [Finsupp.mem_supported, ne]

中文:
定理 iSupIndep_range_lsingle
  证明: by
  refine fun i => disjoint_iff_inf_le.mpr ?_
  rintro x ⟨⟨m, rfl⟩, hm⟩
  suffices ⨆ j != i, LinearMap.range (Finsupp.lsingle j) <= Finsupp.supported M R {i}ᶜ by
    have := (Finsupp.mem_supported ..).mp (this hm); simp_all
  refine iSup₂_le fun j ne => ?_
  rintro _ ⟨m, rfl⟩
  simp [Finsupp.mem_supported, ne]

Depends on / 依赖: Finsupp, Finsupp.lsingle, Finsupp.mem_supported, Finsupp.supported, LinearMap, LinearMap.range, disjoint_iff_inf_le, disjoint_iff_inf_le.mpr, lsingle, mem_supported, supported
-/
theorem iSupIndep_range_lsingle :
    iSupIndep fun i : ι => LinearMap.range (Finsupp.lsingle (R := R) (M := M) i) := by
  refine fun i => disjoint_iff_inf_le.mpr ?_
  rintro x ⟨⟨m, rfl⟩, hm⟩
  suffices ⨆ j != i, LinearMap.range (Finsupp.lsingle j) <= Finsupp.supported M R {i}ᶜ by
    have := (Finsupp.mem_supported ..).mp (this hm); simp_all
  refine iSup₂_le fun j ne => ?_
  rintro _ ⟨m, rfl⟩
  simp [Finsupp.mem_supported, ne]

/--
theorem `LinearMap.iSupIndep_map` / 定理 `LinearMap.iSupIndep_map`

English:
theorem LinearMap.iSupIndep_map
  statement: (f : M ->ₗ[R] M') (inj : Injective f) {m : ι -> Submodule R M}
  proof: by
  simp_rw [iSupIndep, disjoint_iff_inf_le] at ind ⊢
  rintro i _ ⟨⟨x, hxi, rfl⟩, hx⟩
  rw [ind i ⟨hxi]; rw [_⟩]; · simp
  simp_rw [← Submodule.map_iSup] at hx
  have ⟨y, hy, eq⟩ := hx
  simpa [← inj eq]

中文:
定理 线性映射.iSupIndep_map
  结论: (f : M ->ₗ[R] M') (inj : 单射 f) {m : ι -> 子模 R M}
  证明: by
  simp_rw [iSupIndep, disjoint_iff_inf_le] at ind ⊢
  rintro i _ ⟨⟨x, hxi, rfl⟩, hx⟩
  rw [ind i ⟨hxi]; rw [_⟩]; · simp
  simp_rw [← Submodule.map_iSup] at hx
  have ⟨y, hy, eq⟩ := hx
  simpa [← inj eq]

Depends on / 依赖: Submodule, Submodule.map_iSup, disjoint_iff_inf_le, iSupIndep, map_iSup, simp_rw
-/
theorem LinearMap.iSupIndep_map (f : M ->ₗ[R] M') (inj : Injective f) {m : ι -> Submodule R M}
    (ind : iSupIndep m) : iSupIndep fun i => (m i).map f := by
  simp_rw [iSupIndep, disjoint_iff_inf_le] at ind ⊢
  rintro i _ ⟨⟨x, hxi, rfl⟩, hx⟩
  rw [ind i ⟨hxi]; rw [_⟩]; · simp
  simp_rw [← Submodule.map_iSup] at hx
  have ⟨y, hy, eq⟩ := hx
  simpa [← inj eq]

variable (hv : LinearIndependent R v)

/--
theorem `LinearIndependent.iSupIndep_span_singleton` / 定理 `LinearIndependent.iSupIndep_span_singleton`

English:
theorem LinearIndependent.iSupIndep_span_singleton
  given: (hv : LinearIndependent R v)
  proof: by
  convert! LinearMap.iSupIndep_map _ hv (iSupIndep_range_lsingle ι R R)
  ext; simp [mem_span_singleton]

中文:
定理 LinearIndependent.iSupIndep_span_singleton
  条件: (hv : LinearIndependent R v)
  证明: by
  convert! LinearMap.iSupIndep_map _ hv (iSupIndep_range_lsingle ι R R)
  ext; simp [mem_span_singleton]

Depends on / 依赖: LinearMap, LinearMap.iSupIndep_map, convert, iSupIndep_map, iSupIndep_range_lsingle, mem_span_singleton
-/
theorem LinearIndependent.iSupIndep_span_singleton (hv : LinearIndependent R v) :
    iSupIndep fun i => R ∙ v i := by
  convert! LinearMap.iSupIndep_map _ hv (iSupIndep_range_lsingle ι R R)
  ext; simp [mem_span_singleton]

end repr

section union

open LinearMap Finsupp

/--
theorem `linearIndependent_inl_union_inr'` / 定理 `linearIndependent_inl_union_inr'`

English:
theorem linearIndependent_inl_union_inr'
  statement: {v : ι -> M} {v' : ι' -> M'}
  proof: by
  have : linearCombination R (Sum.elim (inl R M M' ∘ v) (inr R M M' ∘ v')) =
      .prodMap (linearCombination R v) (linearCombination R v') ∘ₗ
      (sumFinsuppLEquivProdFinsupp R).toLinearMap := by ext (_ | _) <;> simp
  rw [LinearIndependent]; rw [this]
  simpa [LinearMap.coe_prodMap] using ⟨hv, hv'⟩

中文:
定理 linearIndependent_inl_union_inr'
  结论: {v : ι -> M} {v' : ι' -> M'}
  证明: by
  have : linearCombination R (Sum.elim (inl R M M' ∘ v) (inr R M M' ∘ v')) =
      .prodMap (linearCombination R v) (linearCombination R v') ∘ₗ
      (sumFinsuppLEquivProdFinsupp R).toLinearMap := by ext (_ | _) <;> simp
  rw [LinearIndependent]; rw [this]
  simpa [LinearMap.coe_prodMap] using ⟨hv, hv'⟩

Depends on / 依赖: LinearIndependent, LinearMap, LinearMap.coe_prodMap, Sum.elim, coe_prodMap, linearCombination, prodMap, sumFinsuppLEquivProdFinsupp, toLinearMap
-/
theorem linearIndependent_inl_union_inr' {v : ι -> M} {v' : ι' -> M'}
    (hv : LinearIndependent R v) (hv' : LinearIndependent R v') :
    LinearIndependent R (Sum.elim (inl R M M' ∘ v) (inr R M M' ∘ v')) := by
  have : linearCombination R (Sum.elim (inl R M M' ∘ v) (inr R M M' ∘ v')) =
      .prodMap (linearCombination R v) (linearCombination R v') ∘ₗ
      (sumFinsuppLEquivProdFinsupp R).toLinearMap := by ext (_ | _) <;> simp
  rw [LinearIndependent]; rw [this]
  simpa [LinearMap.coe_prodMap] using ⟨hv, hv'⟩

/--
theorem `LinearIndependent.inl_union_inr` / 定理 `LinearIndependent.inl_union_inr`

English:
theorem LinearIndependent.inl_union_inr
  statement: {s : Set M} {t : Set M'}
  proof: by
  nontriviality R
  let e : s oplus t ≃ ↥(inl R M M' '' s union inr R M M' '' t) :=
    .ofBijective (Sum.elim (fun i => ⟨_, .inl ⟨_, i.2, rfl⟩⟩) fun i => ⟨_, .inr ⟨_, i.2, rfl⟩⟩)
      ⟨by rintro (_ | _) (_ | _) eq <;> simp [hs.ne_zero, ht.ne_zero] at eq <;> aesop,
        by rintro ⟨_, ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩⟩ <;> aesop⟩
  refine (linearIndependent_equiv' e ?_).mp (linearIndependent_inl_union_inr' hs ht)
  ext (_ | _) <;> rfl

中文:
定理 LinearIndependent.inl_union_inr
  结论: {s : 集合 M} {t : 集合 M'}
  证明: by
  nontriviality R
  let e : s oplus t ≃ ↥(inl R M M' '' s union inr R M M' '' t) :=
    .ofBijective (Sum.elim (fun i => ⟨_, .inl ⟨_, i.2, rfl⟩⟩) fun i => ⟨_, .inr ⟨_, i.2, rfl⟩⟩)
      ⟨by rintro (_ | _) (_ | _) eq <;> simp [hs.ne_zero, ht.ne_zero] at eq <;> aesop,
        by rintro ⟨_, ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩⟩ <;> aesop⟩
  refine (linearIndependent_equiv' e ?_).mp (linearIndependent_inl_union_inr' hs ht)
  ext (_ | _) <;> rfl

Depends on / 依赖: Sum.elim, hs.ne_zero, ht.ne_zero, linearIndependent_equiv, linearIndependent_inl_union_inr, ne_zero, nontriviality, ofBijective
-/
theorem LinearIndependent.inl_union_inr {s : Set M} {t : Set M'}
    (hs : LinearIndependent R (fun x => x : s -> M))
    (ht : LinearIndependent R (fun x => x : t -> M')) :
    LinearIndependent R (fun x => x : ↥(inl R M M' '' s union inr R M M' '' t) -> M × M') := by
  nontriviality R
  let e : s oplus t ≃ ↥(inl R M M' '' s union inr R M M' '' t) :=
    .ofBijective (Sum.elim (fun i => ⟨_, .inl ⟨_, i.2, rfl⟩⟩) fun i => ⟨_, .inr ⟨_, i.2, rfl⟩⟩)
      ⟨by rintro (_ | _) (_ | _) eq <;> simp [hs.ne_zero, ht.ne_zero] at eq <;> aesop,
        by rintro ⟨_, ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩⟩ <;> aesop⟩
  refine (linearIndependent_equiv' e ?_).mp (linearIndependent_inl_union_inr' hs ht)
  ext (_ | _) <;> rfl

end union

section Maximal

universe v w

variable (R)

/--
theorem `exists_maximal_linearIndepOn'` / 定理 `exists_maximal_linearIndepOn'`

English:
theorem exists_maximal_linearIndepOn'
  given: (v : ι -> M)
  proof: by
  let indep : Set ι -> Prop := fun s => LinearIndepOn R v s
  let X := { I : Set ι // indep I }
  let r : X -> X -> Prop := fun I J => I.1 subseteq J.1
  have key : forall c : Set X, IsChain r c -> indep (⋃ (I : X) (_ : I in c), I) := by
    intro c hc
    dsimp [indep]
    rw [linearIndepOn_iffₛ]
    intro f hfsupp g hgsupp hsum
    rcases eq_empty_or_nonempty c with (rfl | hn)
    · rw [show f = 0 by simpa using! hfsupp, show g = 0 by simpa using! hgsupp]
    have : Std.Refl r := ⟨fun _ => Set.Subset.refl _⟩
    classical
    obtain ⟨I, _I_mem, hI⟩ : exists I in c, (f.support union g.support : Set ι) subseteq I :=
f.support.coe_union _ ▸ hc.directedOn.exists_mem_subset_of_finset_subset_biUnion hn by
        simpa using! And.intro hfsupp hgsupp
    exact linearIndepOn_iffₛ.mp I.2 f (subset_union_left.trans hI)
      g (subset_union_right.trans hI) hsum
  obtain ⟨⟨I, hli : indep I⟩, hmax : forall a, r ⟨I, hli⟩ a -> r a ⟨I, hli⟩⟩ :=
    exists_maximal_of_chains_bounded (r := r)
      (fun c hc => ⟨⟨⋃ I in c, (I : Set ι), key c hc⟩, fun I => Set.subset_biUnion_of_mem⟩)
      Set.Subset.trans
  exact ⟨I, hli, fun J hsub hli => Set.Subset.antisymm hsub (hmax ⟨J, hli⟩ hsub)⟩

中文:
定理 存在_maximal_linearIndepOn'
  条件: (v : ι -> M)
  证明: by
  let indep : Set ι -> Prop := fun s => LinearIndepOn R v s
  let X := { I : Set ι // indep I }
  let r : X -> X -> Prop := fun I J => I.1 subseteq J.1
  have key : forall c : Set X, IsChain r c -> indep (⋃ (I : X) (_ : I in c), I) := by
    intro c hc
    dsimp [indep]
    rw [linearIndepOn_iffₛ]
    intro f hfsupp g hgsupp hsum
    rcases eq_empty_or_nonempty c with (rfl | hn)
    · rw [show f = 0 by simpa using! hfsupp, show g = 0 by simpa using! hgsupp]
    have : Std.Refl r := ⟨fun _ => Set.Subset.refl _⟩
    classical
    obtain ⟨I, _I_mem, hI⟩ : exists I in c, (f.support union g.support : Set ι) subseteq I :=
f.support.coe_union _ ▸ hc.directedOn.exists_mem_subset_of_finset_subset_biUnion hn by
        simpa using! And.intro hfsupp hgsupp
    exact linearIndepOn_iffₛ.mp I.2 f (subset_union_left.trans hI)
      g (subset_union_right.trans hI) hsum
  obtain ⟨⟨I, hli : indep I⟩, hmax : forall a, r ⟨I, hli⟩ a -> r a ⟨I, hli⟩⟩ :=
    exists_maximal_of_chains_bounded (r := r)
      (fun c hc => ⟨⟨⋃ I in c, (I : Set ι), key c hc⟩, fun I => Set.subset_biUnion_of_mem⟩)
      Set.Subset.trans
  exact ⟨I, hli, fun J hsub hli => Set.Subset.antisymm hsub (hmax ⟨J, hli⟩ hsub)⟩

Depends on / 依赖: IsChain, LinearIndepOn, Set.Subset.refl, Std.Refl, Subset, classical, eq_empty_or_nonempty, hfsupp, hgsupp, subseteq
-/
theorem exists_maximal_linearIndepOn' (v : ι -> M) :
    exists s : Set ι, (LinearIndepOn R v s) ∧ forall t : Set ι, s subseteq t -> (LinearIndepOn R v t) -> s = t := by
  let indep : Set ι -> Prop := fun s => LinearIndepOn R v s
  let X := { I : Set ι // indep I }
  let r : X -> X -> Prop := fun I J => I.1 subseteq J.1
  have key : forall c : Set X, IsChain r c -> indep (⋃ (I : X) (_ : I in c), I) := by
    intro c hc
    dsimp [indep]
    rw [linearIndepOn_iffₛ]
    intro f hfsupp g hgsupp hsum
    rcases eq_empty_or_nonempty c with (rfl | hn)
    · rw [show f = 0 by simpa using! hfsupp, show g = 0 by simpa using! hgsupp]
    have : Std.Refl r := ⟨fun _ => Set.Subset.refl _⟩
    classical
    obtain ⟨I, _I_mem, hI⟩ : exists I in c, (f.support union g.support : Set ι) subseteq I :=
f.support.coe_union _ ▸ hc.directedOn.exists_mem_subset_of_finset_subset_biUnion hn by
        simpa using! And.intro hfsupp hgsupp
    exact linearIndepOn_iffₛ.mp I.2 f (subset_union_left.trans hI)
      g (subset_union_right.trans hI) hsum
  obtain ⟨⟨I, hli : indep I⟩, hmax : forall a, r ⟨I, hli⟩ a -> r a ⟨I, hli⟩⟩ :=
    exists_maximal_of_chains_bounded (r := r)
      (fun c hc => ⟨⟨⋃ I in c, (I : Set ι), key c hc⟩, fun I => Set.subset_biUnion_of_mem⟩)
      Set.Subset.trans
  exact ⟨I, hli, fun J hsub hli => Set.Subset.antisymm hsub (hmax ⟨J, hli⟩ hsub)⟩

end Maximal

/--
lemma `Submodule.codisjoint_span_image_of_codisjoint` / 引理 `Submodule.codisjoint_span_image_of_codisjoint`

English:
lemma Submodule.codisjoint_span_image_of_codisjoint
  statement: (hv : Submodule.span R (Set.range v) = ⊤)
  proof: by
  rw [Finsupp.span_image_eq_map_linearCombination]; rw [Finsupp.span_image_eq_map_linearCombination]
  refine Submodule.codisjoint_map ?_ (Finsupp.codisjoint_supported_supported hst)
  rwa [← LinearMap.range_eq_top, Finsupp.range_linearCombination]

中文:
引理 子模.codisjoint_span_image_of_codisjoint
  结论: (hv : 子模.span R (集合.range v) = ⊤)
  证明: by
  rw [Finsupp.span_image_eq_map_linearCombination]; rw [Finsupp.span_image_eq_map_linearCombination]
  refine Submodule.codisjoint_map ?_ (Finsupp.codisjoint_supported_supported hst)
  rwa [← LinearMap.range_eq_top, Finsupp.range_linearCombination]

Depends on / 依赖: Finsupp, Finsupp.codisjoint_supported_supported, Finsupp.range_linearCombination, Finsupp.span_image_eq_map_linearCombination, LinearMap, LinearMap.range_eq_top, Submodule, Submodule.codisjoint_map, codisjoint_map, codisjoint_supported_supported, range_eq_top, range_linearCombination, span_image_eq_map_linearCombination
-/
lemma Submodule.codisjoint_span_image_of_codisjoint (hv : Submodule.span R (Set.range v) = ⊤)
    {s t : Set ι} (hst : Codisjoint s t) :
    Codisjoint (Submodule.span R (v '' s)) (Submodule.span R (v '' t)) := by
  rw [Finsupp.span_image_eq_map_linearCombination]; rw [Finsupp.span_image_eq_map_linearCombination]
  refine Submodule.codisjoint_map ?_ (Finsupp.codisjoint_supported_supported hst)
  rwa [← LinearMap.range_eq_top, Finsupp.range_linearCombination]

/--
lemma `LinearIndependent.isCompl_span_image` / 引理 `LinearIndependent.isCompl_span_image`

English:
lemma LinearIndependent.isCompl_span_image
  statement: (h₁ : LinearIndependent R v)
  proof: ⟨h₁.disjoint_span_image hst.1, Submodule.codisjoint_span_image_of_codisjoint h₂ hst.2⟩

中文:
引理 LinearIndependent.isCompl_span_image
  结论: (h₁ : LinearIndependent R v)
  证明: ⟨h₁.disjoint_span_image hst.1, Submodule.codisjoint_span_image_of_codisjoint h₂ hst.2⟩

Depends on / 依赖: Submodule, Submodule.codisjoint_span_image_of_codisjoint, codisjoint_span_image_of_codisjoint, disjoint_span_image
-/
lemma LinearIndependent.isCompl_span_image (h₁ : LinearIndependent R v)
    (h₂ : Submodule.span R (Set.range v) = ⊤) {s t : Set ι} (hst : IsCompl s t) :
    IsCompl (Submodule.span R (v '' s)) (Submodule.span R (v '' t)) :=
  ⟨h₁.disjoint_span_image hst.1, Submodule.codisjoint_span_image_of_codisjoint h₂ hst.2⟩

end Semiring

section Module

variable {v : ι -> M}
variable [Ring R] [AddCommGroup M] [AddCommGroup M']
variable [Module R M] [Module R M']

/--
theorem `Fintype.linearIndependent_iff'` / 定理 `Fintype.linearIndependent_iff'`

English:
theorem Fintype.linearIndependent_iff'
  given: [Fintype ι] [DecidableEq ι]
  proof: by
  simp [Fintype.linearIndependent_iff, LinearMap.ker_eq_bot', funext_iff]

中文:
定理 有限类型.linearIndependent_iff'
  条件: [有限类型 ι] [DecidableEq ι]
  证明: by
  simp [Fintype.linearIndependent_iff, LinearMap.ker_eq_bot', funext_iff]
-/
theorem Fintype.linearIndependent_iff' [Fintype ι] [DecidableEq ι] :
    LinearIndependent R v ↔
      LinearMap.ker (LinearMap.lsum R (fun _ => R) Nat fun i => LinearMap.id.smulRight (v i)) = ⊥ := by
  simp [Fintype.linearIndependent_iff, LinearMap.ker_eq_bot', funext_iff]

/--
lemma `LinearIndepOn.pair_iff` / 引理 `LinearIndepOn.pair_iff`

English:
lemma LinearIndepOn.pair_iff
  given: {i j : ι} (f : ι -> M) (hij : i != j)
  proof: by
  classical
  rw [linearIndepOn_iff'']
  refine ⟨fun h c d hcd => ?_, fun h t g ht hg0 h0 => ?_⟩
  · specialize h {i, j} (Pi.single i c + Pi.single j d)
    simpa +contextual [Finset.sum_pair, Pi.single_apply, hij, hij.symm, hcd] using h
  have ht' : t subseteq {i, j} := by simpa [← Finset.coe_subset]
  rw [Finset.sum_subset ht']; rw [Finset.sum_pair hij] at h0
  · obtain ⟨hi0, hj0⟩ := h _ _ h0
    exact fun k hkt => Or.elim (ht hkt) (fun h => h ▸ hi0) (fun h => h ▸ hj0)
  simp +contextual [hg0]

中文:
引理 LinearIndepOn.pair_iff
  条件: {i j : ι} (f : ι -> M) (hij : i != j)
  证明: by
  classical
  rw [linearIndepOn_iff'']
  refine ⟨fun h c d hcd => ?_, fun h t g ht hg0 h0 => ?_⟩
  · specialize h {i, j} (Pi.single i c + Pi.single j d)
    simpa +contextual [Finset.sum_pair, Pi.single_apply, hij, hij.symm, hcd] using h
  have ht' : t subseteq {i, j} := by simpa [← Finset.coe_subset]
  rw [Finset.sum_subset ht']; rw [Finset.sum_pair hij] at h0
  · obtain ⟨hi0, hj0⟩ := h _ _ h0
    exact fun k hkt => Or.elim (ht hkt) (fun h => h ▸ hi0) (fun h => h ▸ hj0)
  simp +contextual [hg0]

Depends on / 依赖: Finset, Finset.coe_subset, Finset.sum_pair, Finset.sum_subset, Or.elim, Pi.single, Pi.single_apply, classical, coe_subset, contextual, hij.symm, linearIndepOn_iff, single, single_apply, specialize, subseteq, sum_pair, sum_subset
-/
lemma LinearIndepOn.pair_iff {i j : ι} (f : ι -> M) (hij : i != j) :
    LinearIndepOn R f {i,j} ↔ forall c d : R, c • f i + d • f j = 0 -> c = 0 ∧ d = 0 := by
  classical
  rw [linearIndepOn_iff'']
  refine ⟨fun h c d hcd => ?_, fun h t g ht hg0 h0 => ?_⟩
  · specialize h {i, j} (Pi.single i c + Pi.single j d)
    simpa +contextual [Finset.sum_pair, Pi.single_apply, hij, hij.symm, hcd] using h
  have ht' : t subseteq {i, j} := by simpa [← Finset.coe_subset]
  rw [Finset.sum_subset ht']; rw [Finset.sum_pair hij] at h0
  · obtain ⟨hi0, hj0⟩ := h _ _ h0
    exact fun k hkt => Or.elim (ht hkt) (fun h => h ▸ hi0) (fun h => h ▸ hj0)
  simp +contextual [hg0]

section Pair

variable {x y : M}

/--
lemma `LinearIndependent.pair_iff` / 引理 `LinearIndependent.pair_iff`

English:
lemma LinearIndependent.pair_iff
  proof: by
  rw [← linearIndepOn_univ_iff]; rw [← Finset.coe_univ]; rw [show @Finset.univ (Fin 2) _ = {0]; rw [1} from rfl]; rw [Finset.coe_insert]; rw [Finset.coe_singleton]; rw [LinearIndepOn.pair_iff _ (by trivial)]
  simp

中文:
引理 LinearIndependent.pair_iff
  证明: by
  rw [← linearIndepOn_univ_iff]; rw [← Finset.coe_univ]; rw [show @Finset.univ (Fin 2) _ = {0]; rw [1} from rfl]; rw [Finset.coe_insert]; rw [Finset.coe_singleton]; rw [LinearIndepOn.pair_iff _ (by trivial)]
  simp

Depends on / 依赖: Finset, Finset.coe_insert, Finset.coe_singleton, Finset.coe_univ, Finset.univ, LinearIndepOn, LinearIndepOn.pair_iff, coe_insert, coe_singleton, coe_univ, linearIndepOn_univ_iff, pair_iff
-/
lemma LinearIndependent.pair_iff :
    LinearIndependent R ![x, y] ↔ forall (s t : R), s • x + t • y = 0 -> s = 0 ∧ t = 0 := by
  rw [← linearIndepOn_univ_iff]; rw [← Finset.coe_univ]; rw [show @Finset.univ (Fin 2) _ = {0]; rw [1} from rfl]; rw [Finset.coe_insert]; rw [Finset.coe_singleton]; rw [LinearIndepOn.pair_iff _ (by trivial)]
  simp

/--
lemma `LinearIndependent.pair_symm_iff` / 引理 `LinearIndependent.pair_symm_iff`

English:
lemma LinearIndependent.pair_symm_iff
  proof: by
  suffices forall x y : M, LinearIndependent R ![x, y] -> LinearIndependent R ![y, x] by tauto
  simp only [LinearIndependent.pair_iff]
  intro x y h s t
  specialize h t s
  rwa [add_comm, and_comm]

中文:
引理 LinearIndependent.pair_symm_iff
  证明: by
  suffices forall x y : M, LinearIndependent R ![x, y] -> LinearIndependent R ![y, x] by tauto
  simp only [LinearIndependent.pair_iff]
  intro x y h s t
  specialize h t s
  rwa [add_comm, and_comm]

Depends on / 依赖: LinearIndependent, LinearIndependent.pair_iff, add_comm, and_comm, pair_iff, specialize
-/
lemma LinearIndependent.pair_symm_iff :
    LinearIndependent R ![x, y] ↔ LinearIndependent R ![y, x] := by
  suffices forall x y : M, LinearIndependent R ![x, y] -> LinearIndependent R ![y, x] by tauto
  simp only [LinearIndependent.pair_iff]
  intro x y h s t
  specialize h t s
  rwa [add_comm, and_comm]

/--
lemma `LinearIndependent.pair_neg_left_iff` / 引理 `LinearIndependent.pair_neg_left_iff`

English:
lemma LinearIndependent.pair_neg_left_iff
  proof: by
  rw [pair_iff]; rw [pair_iff]
  refine ⟨fun h s t hst => ?_, fun h s t hst => ?_⟩ <;> simpa using h (-s) t (by simpa using hst)

中文:
引理 LinearIndependent.pair_neg_left_iff
  证明: by
  rw [pair_iff]; rw [pair_iff]
  refine ⟨fun h s t hst => ?_, fun h s t hst => ?_⟩ <;> simpa using h (-s) t (by simpa using hst)
-/
@[simp] lemma LinearIndependent.pair_neg_left_iff :
    LinearIndependent R ![-x, y] ↔ LinearIndependent R ![x, y] := by
  rw [pair_iff]; rw [pair_iff]
  refine ⟨fun h s t hst => ?_, fun h s t hst => ?_⟩ <;> simpa using h (-s) t (by simpa using hst)

/--
lemma `LinearIndependent.pair_neg_right_iff` / 引理 `LinearIndependent.pair_neg_right_iff`

English:
lemma LinearIndependent.pair_neg_right_iff
  proof: by
  rw [pair_symm_iff]; rw [pair_neg_left_iff]; rw [pair_symm_iff]

中文:
引理 LinearIndependent.pair_neg_right_iff
  证明: by
  rw [pair_symm_iff]; rw [pair_neg_left_iff]; rw [pair_symm_iff]
-/
@[simp] lemma LinearIndependent.pair_neg_right_iff :
    LinearIndependent R ![x, -y] ↔ LinearIndependent R ![x, y] := by
  rw [pair_symm_iff]; rw [pair_neg_left_iff]; rw [pair_symm_iff]

variable {S : Type*} [CommRing S] [IsDomain S] [Module S R] [Module S M]
  [SMulCommClass S R M] [IsScalarTower S R M] [IsTorsionFree S R]
  (a b c d : S)

/--
lemma `LinearIndependent.pair_smul_smul_iff` / 引理 `LinearIndependent.pair_smul_smul_iff`

English:
lemma LinearIndependent.pair_smul_smul_iff
  given: {u v : R} (hu : IsUnit u) (hv : IsUnit v)
  proof: by
  simp only [LinearIndependent.pair_iff]
  refine ⟨fun h s t hst => ?_, fun h s t hst => ?_⟩
  · specialize h (s * hu.unit⁻¹) (t * hv.unit⁻¹)
    simp only [Units.mul_left_eq_zero] at h
    apply h
    simpa [← mul_smul, mul_assoc]
  · specialize h (s * hu.unit) (t * hv.unit)
    simp only [Units.mul_left_eq_zero] at h
    apply h
    simpa [mul_smul]

中文:
引理 LinearIndependent.pair_smul_smul_iff
  条件: {u v : R} (hu : 是单位 u) (hv : 是单位 v)
  证明: by
  simp only [LinearIndependent.pair_iff]
  refine ⟨fun h s t hst => ?_, fun h s t hst => ?_⟩
  · specialize h (s * hu.unit⁻¹) (t * hv.unit⁻¹)
    simp only [Units.mul_left_eq_zero] at h
    apply h
    simpa [← mul_smul, mul_assoc]
  · specialize h (s * hu.unit) (t * hv.unit)
    simp only [Units.mul_left_eq_zero] at h
    apply h
    simpa [mul_smul]

Depends on / 依赖: LinearIndependent, LinearIndependent.pair_iff, Units.mul_left_eq_zero, hu.unit, hv.unit, mul_assoc, mul_left_eq_zero, mul_smul, pair_iff, specialize
-/
lemma LinearIndependent.pair_smul_smul_iff {u v : R} (hu : IsUnit u) (hv : IsUnit v) :
    LinearIndependent R ![u • x, v • y] ↔ LinearIndependent R ![x, y] := by
  simp only [LinearIndependent.pair_iff]
  refine ⟨fun h s t hst => ?_, fun h s t hst => ?_⟩
  · specialize h (s * hu.unit⁻¹) (t * hv.unit⁻¹)
    simp only [Units.mul_left_eq_zero] at h
    apply h
    simpa [← mul_smul, mul_assoc]
  · specialize h (s * hu.unit) (t * hv.unit)
    simp only [Units.mul_left_eq_zero] at h
    apply h
    simpa [mul_smul]

/--
lemma `LinearIndependent.pair_smul_iff` / 引理 `LinearIndependent.pair_smul_iff`

English:
lemma LinearIndependent.pair_smul_iff
  given: {u : S} (hu : u != 0)
  proof: by
  simp only [LinearIndependent.pair_iff]
  refine ⟨fun h s t hst => ?_, fun h s t hst => ?_⟩
  · exact h s t (by rw [← smul_comm u s, ← smul_comm u t, ← smul_add, hst, smul_zero])
  · specialize h (u • s) (u • t) (by rw [smul_assoc, smul_assoc, smul_comm u s, smul_comm u t, hst])
    exact ⟨(smul_eq_zero_iff_right hu).mp h.1, (smul_eq_zero_iff_right hu).mp h.2⟩

中文:
引理 LinearIndependent.pair_smul_iff
  条件: {u : S} (hu : u != 0)
  证明: by
  simp only [LinearIndependent.pair_iff]
  refine ⟨fun h s t hst => ?_, fun h s t hst => ?_⟩
  · exact h s t (by rw [← smul_comm u s, ← smul_comm u t, ← smul_add, hst, smul_zero])
  · specialize h (u • s) (u • t) (by rw [smul_assoc, smul_assoc, smul_comm u s, smul_comm u t, hst])
    exact ⟨(smul_eq_zero_iff_right hu).mp h.1, (smul_eq_zero_iff_right hu).mp h.2⟩

Depends on / 依赖: LinearIndependent, LinearIndependent.pair_iff, pair_iff, smul_add, smul_assoc, smul_comm, smul_eq_zero_iff_right, smul_zero, specialize
-/
lemma LinearIndependent.pair_smul_iff {u : S} (hu : u != 0) :
    LinearIndependent R ![u • x, u • y] ↔ LinearIndependent R ![x, y] := by
  simp only [LinearIndependent.pair_iff]
  refine ⟨fun h s t hst => ?_, fun h s t hst => ?_⟩
  · exact h s t (by rw [← smul_comm u s, ← smul_comm u t, ← smul_add, hst, smul_zero])
  · specialize h (u • s) (u • t) (by rw [smul_assoc, smul_assoc, smul_comm u s, smul_comm u t, hst])
    exact ⟨(smul_eq_zero_iff_right hu).mp h.1, (smul_eq_zero_iff_right hu).mp h.2⟩

/--
lemma `LinearIndependent.pair_add_smul_add_smul_iff_aux` / 引理 `LinearIndependent.pair_add_smul_add_smul_iff_aux`

English:
lemma LinearIndependent.pair_add_smul_add_smul_iff_aux
  statement: (h : a * d != b * c)
  proof: by
  simp only [LinearIndependent.pair_iff] at h' ⊢
  intro s t hst
  specialize h' (a • s + c • t) (b • s + d • t) (by simp only [← hst, smul_add, add_smul,
    smul_assoc, smul_comm a s, smul_comm c t, smul_comm b s, smul_comm d t]; abel)
  obtain ⟨h₁, h₂⟩ := h'
  constructor
  · suffices (a * d) • s = (b * c) • s by
      by_contra hs; exact h (_root_.smul_left_injective S hs ‹_›)
    calc (a * d) • s
        = d • a • s := by rw [mul_comm, mul_smul]
      _ = -(d • c • t) := by rw [eq_neg_iff_add_eq_zero, ← smul_add, h₁, smul_zero]
      _ = (b * c) • s := ?_
    · rw [mul_comm, mul_smul, neg_eq_iff_add_eq_zero, add_comm, smul_comm d c, ← smul_add, h₂,
        smul_zero]
  · suffices (a * d) • t = (b * c) • t by
      by_contra ht; exact h (_root_.smul_left_injective S ht ‹_›)
    calc (a * d) • t
        = a • d • t := by rw [mul_smul]
      _ = -(a • b • s) := by rw [eq_neg_iff_add_eq_zero, ← smul_add, add_comm, h₂, smul_zero]
      _ = (b * c) • t := ?_
    · rw [mul_smul, neg_eq_iff_add_eq_zero, smul_comm a b, ← smul_add, h₁, smul_zero]

中文:
引理 LinearIndependent.pair_add_smul_add_smul_iff_aux
  结论: (h : a * d != b * c)
  证明: by
  simp only [LinearIndependent.pair_iff] at h' ⊢
  intro s t hst
  specialize h' (a • s + c • t) (b • s + d • t) (by simp only [← hst, smul_add, add_smul,
    smul_assoc, smul_comm a s, smul_comm c t, smul_comm b s, smul_comm d t]; abel)
  obtain ⟨h₁, h₂⟩ := h'
  constructor
  · suffices (a * d) • s = (b * c) • s by
      by_contra hs; exact h (_root_.smul_left_injective S hs ‹_›)
    calc (a * d) • s
        = d • a • s := by rw [mul_comm, mul_smul]
      _ = -(d • c • t) := by rw [eq_neg_iff_add_eq_zero, ← smul_add, h₁, smul_zero]
      _ = (b * c) • s := ?_
    · rw [mul_comm, mul_smul, neg_eq_iff_add_eq_zero, add_comm, smul_comm d c, ← smul_add, h₂,
        smul_zero]
  · suffices (a * d) • t = (b * c) • t by
      by_contra ht; exact h (_root_.smul_left_injective S ht ‹_›)
    calc (a * d) • t
        = a • d • t := by rw [mul_smul]
      _ = -(a • b • s) := by rw [eq_neg_iff_add_eq_zero, ← smul_add, add_comm, h₂, smul_zero]
      _ = (b * c) • t := ?_
    · rw [mul_smul, neg_eq_iff_add_eq_zero, smul_comm a b, ← smul_add, h₁, smul_zero]
-/
private lemma LinearIndependent.pair_add_smul_add_smul_iff_aux (h : a * d != b * c)
    (h' : LinearIndependent R ![x, y]) :
    LinearIndependent R ![a • x + b • y, c • x + d • y] := by
  simp only [LinearIndependent.pair_iff] at h' ⊢
  intro s t hst
  specialize h' (a • s + c • t) (b • s + d • t) (by simp only [← hst, smul_add, add_smul,
    smul_assoc, smul_comm a s, smul_comm c t, smul_comm b s, smul_comm d t]; abel)
  obtain ⟨h₁, h₂⟩ := h'
  constructor
  · suffices (a * d) • s = (b * c) • s by
      by_contra hs; exact h (_root_.smul_left_injective S hs ‹_›)
    calc (a * d) • s
        = d • a • s := by rw [mul_comm, mul_smul]
      _ = -(d • c • t) := by rw [eq_neg_iff_add_eq_zero, ← smul_add, h₁, smul_zero]
      _ = (b * c) • s := ?_
    · rw [mul_comm, mul_smul, neg_eq_iff_add_eq_zero, add_comm, smul_comm d c, ← smul_add, h₂,
        smul_zero]
  · suffices (a * d) • t = (b * c) • t by
      by_contra ht; exact h (_root_.smul_left_injective S ht ‹_›)
    calc (a * d) • t
        = a • d • t := by rw [mul_smul]
      _ = -(a • b • s) := by rw [eq_neg_iff_add_eq_zero, ← smul_add, add_comm, h₂, smul_zero]
      _ = (b * c) • t := ?_
    · rw [mul_smul, neg_eq_iff_add_eq_zero, smul_comm a b, ← smul_add, h₁, smul_zero]

/--
lemma `LinearIndependent.pair_add_smul_add_smul_iff` / 引理 `LinearIndependent.pair_add_smul_add_smul_iff`

English:
lemma LinearIndependent.pair_add_smul_add_smul_iff
  given: [Nontrivial R]
  proof: by
  rcases eq_or_ne (a * d) (b * c) with h | h
  · suffices ¬ LinearIndependent R ![a • x + b • y, c • x + d • y] by simpa [h]
    rw [pair_iff]
    push Not
    by_cases hbd : b = 0 ∧ d = 0
    · simp only [hbd.1, hbd.2, zero_smul, add_zero]
      by_cases hac : a = 0 ∧ c = 0; · exact ⟨1, 0, by simp [hac.1, hac.2], by simp⟩
      refine ⟨c • 1, -a • 1, ?_, by aesop⟩
      simp only [smul_assoc, one_smul, neg_smul]
      module
    refine ⟨d • 1, -b • 1, ?_, by contrapose! hbd; simp_all⟩
    simp only [smul_add, smul_assoc, one_smul, smul_smul, mul_comm d, h]
    module
  refine ⟨fun h' => ⟨?_, h⟩, fun ⟨h₁, h₂⟩ => pair_add_smul_add_smul_iff_aux _ _ _ _ h₂ h₁⟩
  suffices LinearIndependent R ![(a * d - b * c) • x, (a * d - b * c) • y] by
    rwa [pair_smul_iff (sub_ne_zero_of_ne h)] at this
  convert! pair_add_smul_add_smul_iff_aux d (-b) (-c) a (by simpa [mul_comm d a]) h' using 1
  ext i; fin_cases i <;> simp <;> module

中文:
引理 LinearIndependent.pair_add_smul_add_smul_iff
  条件: [非平凡 R]
  证明: by
  rcases eq_or_ne (a * d) (b * c) with h | h
  · suffices ¬ LinearIndependent R ![a • x + b • y, c • x + d • y] by simpa [h]
    rw [pair_iff]
    push Not
    by_cases hbd : b = 0 ∧ d = 0
    · simp only [hbd.1, hbd.2, zero_smul, add_zero]
      by_cases hac : a = 0 ∧ c = 0; · exact ⟨1, 0, by simp [hac.1, hac.2], by simp⟩
      refine ⟨c • 1, -a • 1, ?_, by aesop⟩
      simp only [smul_assoc, one_smul, neg_smul]
      module
    refine ⟨d • 1, -b • 1, ?_, by contrapose! hbd; simp_all⟩
    simp only [smul_add, smul_assoc, one_smul, smul_smul, mul_comm d, h]
    module
  refine ⟨fun h' => ⟨?_, h⟩, fun ⟨h₁, h₂⟩ => pair_add_smul_add_smul_iff_aux _ _ _ _ h₂ h₁⟩
  suffices LinearIndependent R ![(a * d - b * c) • x, (a * d - b * c) • y] by
    rwa [pair_smul_iff (sub_ne_zero_of_ne h)] at this
  convert! pair_add_smul_add_smul_iff_aux d (-b) (-c) a (by simpa [mul_comm d a]) h' using 1
  ext i; fin_cases i <;> simp <;> module
-/
@[simp] lemma LinearIndependent.pair_add_smul_add_smul_iff [Nontrivial R] :
    LinearIndependent R ![a • x + b • y, c • x + d • y] ↔
      LinearIndependent R ![x, y] ∧ a * d != b * c := by
  rcases eq_or_ne (a * d) (b * c) with h | h
  · suffices ¬ LinearIndependent R ![a • x + b • y, c • x + d • y] by simpa [h]
    rw [pair_iff]
    push Not
    by_cases hbd : b = 0 ∧ d = 0
    · simp only [hbd.1, hbd.2, zero_smul, add_zero]
      by_cases hac : a = 0 ∧ c = 0; · exact ⟨1, 0, by simp [hac.1, hac.2], by simp⟩
      refine ⟨c • 1, -a • 1, ?_, by aesop⟩
      simp only [smul_assoc, one_smul, neg_smul]
      module
    refine ⟨d • 1, -b • 1, ?_, by contrapose! hbd; simp_all⟩
    simp only [smul_add, smul_assoc, one_smul, smul_smul, mul_comm d, h]
    module
  refine ⟨fun h' => ⟨?_, h⟩, fun ⟨h₁, h₂⟩ => pair_add_smul_add_smul_iff_aux _ _ _ _ h₂ h₁⟩
  suffices LinearIndependent R ![(a * d - b * c) • x, (a * d - b * c) • y] by
    rwa [pair_smul_iff (sub_ne_zero_of_ne h)] at this
  convert! pair_add_smul_add_smul_iff_aux d (-b) (-c) a (by simpa [mul_comm d a]) h' using 1
  ext i; fin_cases i <;> simp <;> module

/--
lemma `LinearIndependent.pair_add_smul_right_iff` / 引理 `LinearIndependent.pair_add_smul_right_iff`

English:
lemma LinearIndependent.pair_add_smul_right_iff
  proof: by
  rcases subsingleton_or_nontrivial S with hS | hS; · simp [hS.elim c 0]
  nontriviality R
  simpa using pair_add_smul_add_smul_iff (x := x) (y := y) 1 0 c 1

中文:
引理 LinearIndependent.pair_add_smul_right_iff
  证明: by
  rcases subsingleton_or_nontrivial S with hS | hS; · simp [hS.elim c 0]
  nontriviality R
  simpa using pair_add_smul_add_smul_iff (x := x) (y := y) 1 0 c 1
-/
@[simp] lemma LinearIndependent.pair_add_smul_right_iff :
    LinearIndependent R ![x, c • x + y] ↔ LinearIndependent R ![x, y] := by
  rcases subsingleton_or_nontrivial S with hS | hS; · simp [hS.elim c 0]
  nontriviality R
  simpa using pair_add_smul_add_smul_iff (x := x) (y := y) 1 0 c 1

/--
lemma `LinearIndependent.pair_add_smul_left_iff` / 引理 `LinearIndependent.pair_add_smul_left_iff`

English:
lemma LinearIndependent.pair_add_smul_left_iff
  proof: by
  rcases subsingleton_or_nontrivial S with hS | hS; · simp [hS.elim b 0]
  nontriviality R
  simpa using pair_add_smul_add_smul_iff (x := x) (y := y) 1 b 0 1

中文:
引理 LinearIndependent.pair_add_smul_left_iff
  证明: by
  rcases subsingleton_or_nontrivial S with hS | hS; · simp [hS.elim b 0]
  nontriviality R
  simpa using pair_add_smul_add_smul_iff (x := x) (y := y) 1 b 0 1
-/
@[simp] lemma LinearIndependent.pair_add_smul_left_iff :
    LinearIndependent R ![x + b • y, y] ↔ LinearIndependent R ![x, y] := by
  rcases subsingleton_or_nontrivial S with hS | hS; · simp [hS.elim b 0]
  nontriviality R
  simpa using pair_add_smul_add_smul_iff (x := x) (y := y) 1 b 0 1

/--
lemma `LinearIndependent.pair_add_right_iff` / 引理 `LinearIndependent.pair_add_right_iff`

English:
lemma LinearIndependent.pair_add_right_iff
  proof: by
  suffices forall x y : M, LinearIndependent R ![x, x + y] -> LinearIndependent R ![x, y] from
    ⟨this x y, fun h => by simpa using this (-x) (x + y) (by simpa)⟩
  simp only [LinearIndependent.pair_iff]
  intro x y h s t h'
  obtain ⟨h₁, h₂⟩ := h (s - t) t (by rw [sub_smul, smul_add, ← h']; abel)
  rw [h₂]; rw [sub_zero] at h₁
  tauto

中文:
引理 LinearIndependent.pair_add_right_iff
  证明: by
  suffices forall x y : M, LinearIndependent R ![x, x + y] -> LinearIndependent R ![x, y] from
    ⟨this x y, fun h => by simpa using this (-x) (x + y) (by simpa)⟩
  simp only [LinearIndependent.pair_iff]
  intro x y h s t h'
  obtain ⟨h₁, h₂⟩ := h (s - t) t (by rw [sub_smul, smul_add, ← h']; abel)
  rw [h₂]; rw [sub_zero] at h₁
  tauto
-/
@[simp] lemma LinearIndependent.pair_add_right_iff :
    LinearIndependent R ![x, x + y] ↔ LinearIndependent R ![x, y] := by
  suffices forall x y : M, LinearIndependent R ![x, x + y] -> LinearIndependent R ![x, y] from
    ⟨this x y, fun h => by simpa using this (-x) (x + y) (by simpa)⟩
  simp only [LinearIndependent.pair_iff]
  intro x y h s t h'
  obtain ⟨h₁, h₂⟩ := h (s - t) t (by rw [sub_smul, smul_add, ← h']; abel)
  rw [h₂]; rw [sub_zero] at h₁
  tauto

/--
lemma `LinearIndependent.pair_add_left_iff` / 引理 `LinearIndependent.pair_add_left_iff`

English:
lemma LinearIndependent.pair_add_left_iff
  proof: by
  rw [← pair_symm_iff]; rw [add_comm]; rw [pair_add_right_iff]; rw [pair_symm_iff]

中文:
引理 LinearIndependent.pair_add_left_iff
  证明: by
  rw [← pair_symm_iff]; rw [add_comm]; rw [pair_add_right_iff]; rw [pair_symm_iff]
-/
@[simp] lemma LinearIndependent.pair_add_left_iff :
    LinearIndependent R ![x + y, y] ↔ LinearIndependent R ![x, y] := by
  rw [← pair_symm_iff]; rw [add_comm]; rw [pair_add_right_iff]; rw [pair_symm_iff]

end Pair

end Module

/-! ### Properties which require `Ring R` -/


section Module

variable {v : ι -> M}
variable [Ring R] [AddCommGroup M] [AddCommGroup M']
variable [Module R M] [Module R M']

/--
theorem `linearIndepOn_id_iUnion_finite` / 定理 `linearIndepOn_id_iUnion_finite`

English:
theorem linearIndepOn_id_iUnion_finite
  statement: {f : ι -> Set M} (hl : forall i, LinearIndepOn R id (f i))
  proof: by
  classical
  rw [iUnion_eq_iUnion_finset f]
  apply linearIndepOn_iUnion_of_directed
  · apply directed_of_isDirected_le
    exact fun t₁ t₂ ht => iUnion_mono fun i => iUnion_subset_iUnion_const fun h => ht h
  intro t
  induction t using Finset.induction_on with
  | empty => simp
  | insert i s his ih =>
    rw [Finset.set_biUnion_insert]
    refine (hl _).id_union ih ?_
    rw [span_iUnion₂]
    exact hd i s s.finite_toSet his

中文:
定理 linearIndepOn_id_iUnion_finite
  结论: {f : ι -> 集合 M} (hl : 对任意 i, LinearIndepOn R id (f i))
  证明: by
  classical
  rw [iUnion_eq_iUnion_finset f]
  apply linearIndepOn_iUnion_of_directed
  · apply directed_of_isDirected_le
    exact fun t₁ t₂ ht => iUnion_mono fun i => iUnion_subset_iUnion_const fun h => ht h
  intro t
  induction t using Finset.induction_on with
  | empty => simp
  | insert i s his ih =>
    rw [Finset.set_biUnion_insert]
    refine (hl _).id_union ih ?_
    rw [span_iUnion₂]
    exact hd i s s.finite_toSet his

Depends on / 依赖: Finset, Finset.induction_on, Finset.set_biUnion_insert, classical, directed_of_isDirected_le, finite_toSet, iUnion_eq_iUnion_finset, iUnion_mono, iUnion_subset_iUnion_const, id_union, induction_on, insert, linearIndepOn_iUnion_of_directed, s.finite_toSet, set_biUnion_insert
-/
theorem linearIndepOn_id_iUnion_finite {f : ι -> Set M} (hl : forall i, LinearIndepOn R id (f i))
    (hd : forall i, forall t : Set ι, t.Finite -> i ∉ t -> Disjoint (span R (f i)) (⨆ i in t, span R (f i))) :
    LinearIndepOn R id (⋃ i, f i) := by
  classical
  rw [iUnion_eq_iUnion_finset f]
  apply linearIndepOn_iUnion_of_directed
  · apply directed_of_isDirected_le
    exact fun t₁ t₂ ht => iUnion_mono fun i => iUnion_subset_iUnion_const fun h => ht h
  intro t
  induction t using Finset.induction_on with
  | empty => simp
  | insert i s his ih =>
    rw [Finset.set_biUnion_insert]
    refine (hl _).id_union ih ?_
    rw [span_iUnion₂]
    exact hd i s s.finite_toSet his

/--
theorem `linearIndependent_iUnion_finite` / 定理 `linearIndependent_iUnion_finite`

English:
theorem linearIndependent_iUnion_finite
  statement: {η : Type*} {ιs : η -> Type*} {f : forall j : η, ιs j -> M}
  proof: by
  nontriviality R
  apply LinearIndependent.of_linearIndepOn_id_range
  · rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ hxy
    by_cases h_cases : x₁ = y₁
    · subst h_cases
      refine Sigma.eq rfl ?_
      rw [LinearIndependent.injective (hindep _) hxy]
    · have h0 : f x₁ x₂ = 0 := by
        apply
          disjoint_def.1 (hd x₁ {y₁} (finite_singleton y₁) fun h => h_cases (eq_of_mem_singleton h))
            (f x₁ x₂) (subset_span (mem_range_self _))
        rw [iSup_singleton]
        simp only at hxy
        rw [hxy]
        exact subset_span (mem_range_self y₂)
      exact False.elim ((hindep x₁).ne_zero _ h0)
  rw [range_sigma_eq_iUnion_range]
  apply linearIndepOn_id_iUnion_finite (fun j => (hindep j).linearIndepOn_id) hd

中文:
定理 linearIndependent_iUnion_finite
  结论: {η : 类型} {ιs : η -> 类型} {f : 对任意 j : η, ιs j -> M}
  证明: by
  nontriviality R
  apply LinearIndependent.of_linearIndepOn_id_range
  · rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ hxy
    by_cases h_cases : x₁ = y₁
    · subst h_cases
      refine Sigma.eq rfl ?_
      rw [LinearIndependent.injective (hindep _) hxy]
    · have h0 : f x₁ x₂ = 0 := by
        apply
          disjoint_def.1 (hd x₁ {y₁} (finite_singleton y₁) fun h => h_cases (eq_of_mem_singleton h))
            (f x₁ x₂) (subset_span (mem_range_self _))
        rw [iSup_singleton]
        simp only at hxy
        rw [hxy]
        exact subset_span (mem_range_self y₂)
      exact False.elim ((hindep x₁).ne_zero _ h0)
  rw [range_sigma_eq_iUnion_range]
  apply linearIndepOn_id_iUnion_finite (fun j => (hindep j).linearIndepOn_id) hd

Depends on / 依赖: False.elim, LinearIndependent, LinearIndependent.injective, LinearIndependent.of_linearIndepOn_id_range, Sigma.eq, disjoint_def, eq_of_mem_singleton, finite_singleton, h_cases, hindep, iSup_singleton, injective, mem_range_self, nontriviality, of_linearIndepOn_id_range, subset_span
-/
theorem linearIndependent_iUnion_finite {η : Type*} {ιs : η -> Type*} {f : forall j : η, ιs j -> M}
    (hindep : forall j, LinearIndependent R (f j))
    (hd : forall i, forall t : Set η,
      t.Finite -> i ∉ t -> Disjoint (span R (range (f i))) (⨆ i in t, span R (range (f i)))) :
    LinearIndependent R fun ji : Σ j, ιs j => f ji.1 ji.2 := by
  nontriviality R
  apply LinearIndependent.of_linearIndepOn_id_range
  · rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ hxy
    by_cases h_cases : x₁ = y₁
    · subst h_cases
      refine Sigma.eq rfl ?_
      rw [LinearIndependent.injective (hindep _) hxy]
    · have h0 : f x₁ x₂ = 0 := by
        apply
          disjoint_def.1 (hd x₁ {y₁} (finite_singleton y₁) fun h => h_cases (eq_of_mem_singleton h))
            (f x₁ x₂) (subset_span (mem_range_self _))
        rw [iSup_singleton]
        simp only at hxy
        rw [hxy]
        exact subset_span (mem_range_self y₂)
      exact False.elim ((hindep x₁).ne_zero _ h0)
  rw [range_sigma_eq_iUnion_range]
  apply linearIndepOn_id_iUnion_finite (fun j => (hindep j).linearIndepOn_id) hd

open LinearMap

variable (R) in
/--
theorem `exists_maximal_linearIndepOn` / 定理 `exists_maximal_linearIndepOn`

English:
theorem exists_maximal_linearIndepOn
  given: (v : ι -> M)
  proof: by
  classical
    rcases exists_maximal_linearIndepOn' R v with ⟨I, hIlinind, hImaximal⟩
    use I, hIlinind
    intro i hi
    specialize hImaximal (I union {i}) (by simp)
    set J := I union {i} with hJ
    have memJ : forall {x}, x in J ↔ x = i ∨ x in I := by simp [hJ]
    have hiJ : i in J := by simp [J]
    have h := by
      refine mt hImaximal ?_
      · intro h2
        rw [h2] at hi
        exact absurd hiJ hi
    obtain ⟨f, supp_f, sum_f, f_ne⟩ := linearDepOn_iff.mp h
    have hfi : f i != 0 := by
      contrapose hIlinind
      refine linearDepOn_iff.mpr ⟨f, ?_, sum_f, f_ne⟩
      simp only [Finsupp.mem_supported, hJ] at supp_f ⊢
      rintro x hx
      refine (memJ.mp (supp_f hx)).resolve_left ?_
      rintro rfl
      exact (Finsupp.mem_support_iff.mp hx) hIlinind
    use f i, hfi
    have hfi' : i in f.support := Finsupp.mem_support_iff.mpr hfi
    rw [← Finset.insert_erase hfi']; rw [Finset.sum_insert (Finset.notMem_erase _ _)]; rw [add_eq_zero_iff_eq_neg] at sum_f
    rw [sum_f]
    refine neg_mem (sum_mem fun c hc => smul_mem _ _ (subset_span ⟨c, ?_, rfl⟩))
    exact (memJ.mp (supp_f (Finset.erase_subset _ _ hc))).resolve_left (Finset.ne_of_mem_erase hc)

@[stacks 0CKM]

中文:
定理 存在_maximal_linearIndepOn
  条件: (v : ι -> M)
  证明: by
  classical
    rcases exists_maximal_linearIndepOn' R v with ⟨I, hIlinind, hImaximal⟩
    use I, hIlinind
    intro i hi
    specialize hImaximal (I union {i}) (by simp)
    set J := I union {i} with hJ
    have memJ : forall {x}, x in J ↔ x = i ∨ x in I := by simp [hJ]
    have hiJ : i in J := by simp [J]
    have h := by
      refine mt hImaximal ?_
      · intro h2
        rw [h2] at hi
        exact absurd hiJ hi
    obtain ⟨f, supp_f, sum_f, f_ne⟩ := linearDepOn_iff.mp h
    have hfi : f i != 0 := by
      contrapose hIlinind
      refine linearDepOn_iff.mpr ⟨f, ?_, sum_f, f_ne⟩
      simp only [Finsupp.mem_supported, hJ] at supp_f ⊢
      rintro x hx
      refine (memJ.mp (supp_f hx)).resolve_left ?_
      rintro rfl
      exact (Finsupp.mem_support_iff.mp hx) hIlinind
    use f i, hfi
    have hfi' : i in f.support := Finsupp.mem_support_iff.mpr hfi
    rw [← Finset.insert_erase hfi']; rw [Finset.sum_insert (Finset.notMem_erase _ _)]; rw [add_eq_zero_iff_eq_neg] at sum_f
    rw [sum_f]
    refine neg_mem (sum_mem fun c hc => smul_mem _ _ (subset_span ⟨c, ?_, rfl⟩))
    exact (memJ.mp (supp_f (Finset.erase_subset _ _ hc))).resolve_left (Finset.ne_of_mem_erase hc)

@[stacks 0CKM]

Depends on / 依赖: absurd, classical, contrapose, exists_maximal_linearIndepOn, f_ne, hIlinind, hImaximal, linearDepOn_iff, linearDepOn_iff.mp, linearDepOn_iff.mpr, specialize, sum_f, supp_f
-/
theorem exists_maximal_linearIndepOn (v : ι -> M) :
    exists s : Set ι, (LinearIndepOn R v s) ∧ forall i ∉ s, exists a : R, a != 0 ∧ a • v i in span R (v '' s) := by
  classical
    rcases exists_maximal_linearIndepOn' R v with ⟨I, hIlinind, hImaximal⟩
    use I, hIlinind
    intro i hi
    specialize hImaximal (I union {i}) (by simp)
    set J := I union {i} with hJ
    have memJ : forall {x}, x in J ↔ x = i ∨ x in I := by simp [hJ]
    have hiJ : i in J := by simp [J]
    have h := by
      refine mt hImaximal ?_
      · intro h2
        rw [h2] at hi
        exact absurd hiJ hi
    obtain ⟨f, supp_f, sum_f, f_ne⟩ := linearDepOn_iff.mp h
    have hfi : f i != 0 := by
      contrapose hIlinind
      refine linearDepOn_iff.mpr ⟨f, ?_, sum_f, f_ne⟩
      simp only [Finsupp.mem_supported, hJ] at supp_f ⊢
      rintro x hx
      refine (memJ.mp (supp_f hx)).resolve_left ?_
      rintro rfl
      exact (Finsupp.mem_support_iff.mp hx) hIlinind
    use f i, hfi
    have hfi' : i in f.support := Finsupp.mem_support_iff.mpr hfi
    rw [← Finset.insert_erase hfi']; rw [Finset.sum_insert (Finset.notMem_erase _ _)]; rw [add_eq_zero_iff_eq_neg] at sum_f
    rw [sum_f]
    refine neg_mem (sum_mem fun c hc => smul_mem _ _ (subset_span ⟨c, ?_, rfl⟩))
    exact (memJ.mp (supp_f (Finset.erase_subset _ _ hc))).resolve_left (Finset.ne_of_mem_erase hc)

@[stacks 0CKM]
/--
lemma `linearIndependent_algHom_toLinearMap` / 引理 `linearIndependent_algHom_toLinearMap`

English:
lemma linearIndependent_algHom_toLinearMap
  proof: by
  apply LinearIndependent.of_comp (LinearMap.ltoFun K M L L)
  exact (linearIndependent_monoidHom M L).comp
    (RingHom.toMonoidHom ∘ AlgHom.toRingHom)
    (fun _ _ e => AlgHom.ext (DFunLike.congr_fun e :))

中文:
引理 linearIndependent_algHom_toLinearMap
  证明: by
  apply LinearIndependent.of_comp (LinearMap.ltoFun K M L L)
  exact (linearIndependent_monoidHom M L).comp
    (RingHom.toMonoidHom ∘ AlgHom.toRingHom)
    (fun _ _ e => AlgHom.ext (DFunLike.congr_fun e :))

Depends on / 依赖: AlgHom, AlgHom.ext, AlgHom.toRingHom, DFunLike, DFunLike.congr_fun, LinearIndependent, LinearIndependent.of_comp, LinearMap, LinearMap.ltoFun, RingHom, RingHom.toMonoidHom, congr_fun, linearIndependent_monoidHom, ltoFun, of_comp, toMonoidHom, toRingHom
-/
lemma linearIndependent_algHom_toLinearMap
    (K M L) [CommSemiring K] [Semiring M] [Algebra K M] [CommRing L] [IsDomain L] [Algebra K L] :
    LinearIndependent L (AlgHom.toLinearMap : (M ->ₐ[K] L) -> M ->ₗ[K] L) := by
  apply LinearIndependent.of_comp (LinearMap.ltoFun K M L L)
  exact (linearIndependent_monoidHom M L).comp
    (RingHom.toMonoidHom ∘ AlgHom.toRingHom)
    (fun _ _ e => AlgHom.ext (DFunLike.congr_fun e :))

/--
lemma `linearIndependent_algHom_toLinearMap'` / 引理 `linearIndependent_algHom_toLinearMap'`

English:
lemma linearIndependent_algHom_toLinearMap'
  statement: (K M L) [CommRing K] [IsDomain K]
  proof: (linearIndependent_algHom_toLinearMap K M L).restrict_scalars' K

中文:
引理 linearIndependent_algHom_toLinearMap'
  结论: (K M L) [交换环 K] [是整环 K]
  证明: (linearIndependent_algHom_toLinearMap K M L).restrict_scalars' K

Depends on / 依赖: linearIndependent_algHom_toLinearMap, restrict_scalars
-/
lemma linearIndependent_algHom_toLinearMap' (K M L) [CommRing K] [IsDomain K]
    [Semiring M] [Algebra K M] [CommRing L] [IsDomain L] [Algebra K L] [IsTorsionFree K L] :
    LinearIndependent K (AlgHom.toLinearMap : (M ->ₐ[K] L) -> M ->ₗ[K] L) :=
  (linearIndependent_algHom_toLinearMap K M L).restrict_scalars' K

set_option backward.isDefEq.respectTransparency false in
/--
lemma `LinearMap.injective_of_linearIndependent` / 引理 `LinearMap.injective_of_linearIndependent`

English:
lemma LinearMap.injective_of_linearIndependent
  statement: {N : Type*} [AddCommGroup N] [Module R N]
  proof: by
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  have : x in Submodule.span R (.range v) := by rw [hv]; exact mem_top
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp this
  simp only [map_finsuppSum, map_smul] at hx
  obtain rfl := linearIndependent_iff.mp hli c hx
  simp

中文:
引理 线性映射.injective_of_linearIndependent
  结论: {N : 类型} [加法交换群 N] [模 R N]
  证明: by
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  have : x in Submodule.span R (.range v) := by rw [hv]; exact mem_top
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp this
  simp only [map_finsuppSum, map_smul] at hx
  obtain rfl := linearIndependent_iff.mp hli c hx
  simp

Depends on / 依赖: Finsupp, Finsupp.mem_span_range_iff_exists_finsupp.mp, Submodule, Submodule.span, injective_iff_map_eq_zero, linearIndependent_iff, linearIndependent_iff.mp, map_finsuppSum, map_smul, mem_span_range_iff_exists_finsupp, mem_top
-/
lemma LinearMap.injective_of_linearIndependent {N : Type*} [AddCommGroup N] [Module R N]
    {f : M ->ₗ[R] N} {ι : Type*} {v : ι -> M}
    (hv : Submodule.span R (.range v) = ⊤) (hli : LinearIndependent R (f ∘ v)) :
    Function.Injective f := by
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  have : x in Submodule.span R (.range v) := by rw [hv]; exact mem_top
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp this
  simp only [map_finsuppSum, map_smul] at hx
  obtain rfl := linearIndependent_iff.mp hli c hx
  simp

/--
lemma `LinearMap.bijective_of_linearIndependent_of_span_eq_top` / 引理 `LinearMap.bijective_of_linearIndependent_of_span_eq_top`

English:
lemma LinearMap.bijective_of_linearIndependent_of_span_eq_top
  statement: {N : Type*} [AddCommGroup N]
  proof: by
  refine ⟨LinearMap.injective_of_linearIndependent hv hli, ?_⟩
  rw [Set.range_comp]; rw [← Submodule.map_span]; rw [hv]; rw [Submodule.map_top] at hsp
  rwa [← range_eq_top]

中文:
引理 线性映射.bijective_of_linearIndependent_of_span_eq_top
  结论: {N : 类型} [加法交换群 N]
  证明: by
  refine ⟨LinearMap.injective_of_linearIndependent hv hli, ?_⟩
  rw [Set.range_comp]; rw [← Submodule.map_span]; rw [hv]; rw [Submodule.map_top] at hsp
  rwa [← range_eq_top]

Depends on / 依赖: LinearMap, LinearMap.injective_of_linearIndependent, Set.range_comp, Submodule, Submodule.map_span, Submodule.map_top, injective_of_linearIndependent, map_span, map_top, range_comp, range_eq_top
-/
lemma LinearMap.bijective_of_linearIndependent_of_span_eq_top {N : Type*} [AddCommGroup N]
    [Module R N] {f : M ->ₗ[R] N} {ι : Type*} {v : ι -> M} (hv : Submodule.span R (Set.range v) = ⊤)
    (hli : LinearIndependent R (f ∘ v)) (hsp : Submodule.span R (Set.range <| f ∘ v) = ⊤) :
    Function.Bijective f := by
  refine ⟨LinearMap.injective_of_linearIndependent hv hli, ?_⟩
  rw [Set.range_comp]; rw [← Submodule.map_span]; rw [hv]; rw [Submodule.map_top] at hsp
  rwa [← range_eq_top]

/--
lemma `LinearIndepOn.insert'` / 引理 `LinearIndepOn.insert'`

English:
lemma LinearIndepOn.insert'
  statement: {s : Set ι} {i : ι} (hs : LinearIndepOn R v s)
  proof: by
  rw [← Set.union_singleton]
  refine hs.union (.singleton' fun r hr => hx _ <| by simp [hr]) ?_
  simp +contextual [disjoint_span_singleton'', hx]

中文:
引理 LinearIndepOn.insert'
  结论: {s : 集合 ι} {i : ι} (hs : LinearIndepOn R v s)
  证明: by
  rw [← Set.union_singleton]
  refine hs.union (.singleton' fun r hr => hx _ <| by simp [hr]) ?_
  simp +contextual [disjoint_span_singleton'', hx]

Depends on / 依赖: Set.union_singleton, contextual, disjoint_span_singleton, hs.union, singleton, union_singleton
-/
lemma LinearIndepOn.insert' {s : Set ι} {i : ι} (hs : LinearIndepOn R v s)
    (hx : forall r : R, r • v i in Submodule.span R (v '' s) -> r = 0) :
    LinearIndepOn R v (insert i s) := by
  rw [← Set.union_singleton]
  refine hs.union (.singleton' fun r hr => hx _ <| by simp [hr]) ?_
  simp +contextual [disjoint_span_singleton'', hx]

/--
lemma `LinearIndepOn.id_insert'` / 引理 `LinearIndepOn.id_insert'`

English:
lemma LinearIndepOn.id_insert'
  statement: {s : Set M} {x : M} (hs : LinearIndepOn R id s)
  proof: hs.insert' by simpa

中文:
引理 LinearIndepOn.id_insert'
  结论: {s : 集合 M} {x : M} (hs : LinearIndepOn R id s)
  证明: hs.insert' by simpa

Depends on / 依赖: hs.insert, insert
-/
lemma LinearIndepOn.id_insert' {s : Set M} {x : M} (hs : LinearIndepOn R id s)
    (hx : forall r : R, r • x in Submodule.span R s -> r = 0) : LinearIndepOn R id (insert x s) :=
hs.insert' by simpa

/--
theorem `LinearIndependent.of_pairwise_dual_eq_zero_one` / 定理 `LinearIndependent.of_pairwise_dual_eq_zero_one`

English:
theorem LinearIndependent.of_pairwise_dual_eq_zero_one
  statement: (v : ι -> M) (f : ι -> Dual R M)
  proof: by
  refine linearIndependent_iff'.mpr fun s g hrel i hi => ?_
  have aux (j : ι) (hjs : j in s) (hji : j != i) : g j * (f i) (v j) = 0 := by simp [h1 hji.symm]
  simpa [s.sum_eq_single i aux (by lia), h2 i] using congr_arg (f i) hrel

中文:
定理 LinearIndependent.of_pairwise_dual_eq_zero_one
  结论: (v : ι -> M) (f : ι -> 对偶 R M)
  证明: by
  refine linearIndependent_iff'.mpr fun s g hrel i hi => ?_
  have aux (j : ι) (hjs : j in s) (hji : j != i) : g j * (f i) (v j) = 0 := by simp [h1 hji.symm]
  simpa [s.sum_eq_single i aux (by lia), h2 i] using congr_arg (f i) hrel

Depends on / 依赖: congr_arg, hji.symm, linearIndependent_iff, s.sum_eq_single, sum_eq_single
-/
theorem LinearIndependent.of_pairwise_dual_eq_zero_one (v : ι -> M) (f : ι -> Dual R M)
    (h1 : Pairwise fun i j => f i (v j) = 0)
    (h2 : forall i, (f i) (v i) = 1) :
    LinearIndependent R v := by
  refine linearIndependent_iff'.mpr fun s g hrel i hi => ?_
  have aux (j : ι) (hjs : j in s) (hji : j != i) : g j * (f i) (v j) = 0 := by simp [h1 hji.symm]
  simpa [s.sum_eq_single i aux (by lia), h2 i] using congr_arg (f i) hrel

end Module

open Finsupp in
/--
lemma `LinearIndependent.update` / 引理 `LinearIndependent.update`

English:
lemma LinearIndependent.update
  statement: [DecidableEq ι] [CommRing R] [AddCommGroup M] [Module R M]
  proof: by
  rw [linearIndependent_iff] at hf ⊢
  obtain ⟨r, hr, l, hl, hg⟩ := hg
  intros l' hl'
  apply_fun (r • ·) at hl'
  simp_rw [Pi.update_eq_sub_add_single, ← bilinearCombination_apply _ (S := R), map_add, map_sub,
    bilinearCombination_apply, LinearMap.add_apply, LinearMap.sub_apply,
    linearCombination_single_index, smul_add, smul_sub, smul_zero, smul_comm r (l' i) m,
    hg, ← LinearMap.map_smul, smul_smul, ← linearCombination_single, ← map_sub, ← map_add] at hl'
  replace hl' : forall j, (r * l' j - (single i (r * l' i)) j) + l' i * l j = 0 :=
    fun j => DFunLike.congr_fun (hf _ hl') j
  grind [mem_nonZeroDivisors_iff]

中文:
引理 LinearIndependent.update
  结论: [DecidableEq ι] [交换环 R] [加法交换群 M] [模 R M]
  证明: by
  rw [linearIndependent_iff] at hf ⊢
  obtain ⟨r, hr, l, hl, hg⟩ := hg
  intros l' hl'
  apply_fun (r • ·) at hl'
  simp_rw [Pi.update_eq_sub_add_single, ← bilinearCombination_apply _ (S := R), map_add, map_sub,
    bilinearCombination_apply, LinearMap.add_apply, LinearMap.sub_apply,
    linearCombination_single_index, smul_add, smul_sub, smul_zero, smul_comm r (l' i) m,
    hg, ← LinearMap.map_smul, smul_smul, ← linearCombination_single, ← map_sub, ← map_add] at hl'
  replace hl' : forall j, (r * l' j - (single i (r * l' i)) j) + l' i * l j = 0 :=
    fun j => DFunLike.congr_fun (hf _ hl') j
  grind [mem_nonZeroDivisors_iff]

Depends on / 依赖: LinearMap, LinearMap.add_apply, LinearMap.map_smul, LinearMap.sub_apply, Pi.update_eq_sub_add_single, add_apply, apply_fun, bilinearCombination_apply, intros, linearCombination_single, linearCombination_single_index, linearIndependent_iff, map_add, map_smul, map_sub, replace, simp_rw, single, smul_add, smul_comm
-/
lemma LinearIndependent.update [DecidableEq ι] [CommRing R] [AddCommGroup M] [Module R M]
    {f : ι -> M} (hf : LinearIndependent R f) (i : ι) (m : M)
    (hg : exists r in nonZeroDivisors R, exists l : ι ->₀ R,
      l i in nonZeroDivisors R ∧ r • m = linearCombination R f l) :
    LinearIndependent R (Function.update f i m) := by
  rw [linearIndependent_iff] at hf ⊢
  obtain ⟨r, hr, l, hl, hg⟩ := hg
  intros l' hl'
  apply_fun (r • ·) at hl'
  simp_rw [Pi.update_eq_sub_add_single, ← bilinearCombination_apply _ (S := R), map_add, map_sub,
    bilinearCombination_apply, LinearMap.add_apply, LinearMap.sub_apply,
    linearCombination_single_index, smul_add, smul_sub, smul_zero, smul_comm r (l' i) m,
    hg, ← LinearMap.map_smul, smul_smul, ← linearCombination_single, ← map_sub, ← map_add] at hl'
  replace hl' : forall j, (r * l' j - (single i (r * l' i)) j) + l' i * l j = 0 :=
    fun j => DFunLike.congr_fun (hf _ hl') j
  grind [mem_nonZeroDivisors_iff]

/-!
### Properties which require `DivisionRing K`

These can be considered generalizations of properties of linear independence in vector spaces.
-/


section Module

variable [DivisionRing K] [AddCommGroup V] [Module K V]
variable {v : ι -> V} {s t : Set V} {x y : V}

open Submodule


/--
theorem `mem_span_insert_exchange` / 定理 `mem_span_insert_exchange`

English:
theorem mem_span_insert_exchange
  proof: by
  simp only [mem_span_insert, forall_exists_index, and_imp]
  rintro a z hz rfl h
  refine ⟨a⁻¹, -a⁻¹ • z, smul_mem _ _ hz, ?_⟩
  have a0 : a != 0 := by
    rintro rfl
    simp_all
  match_scalars <;> simp [a0]

中文:
定理 mem_span_insert_exchange
  证明: by
  simp only [mem_span_insert, forall_exists_index, and_imp]
  rintro a z hz rfl h
  refine ⟨a⁻¹, -a⁻¹ • z, smul_mem _ _ hz, ?_⟩
  have a0 : a != 0 := by
    rintro rfl
    simp_all
  match_scalars <;> simp [a0]

Depends on / 依赖: and_imp, forall_exists_index, match_scalars, mem_span_insert, smul_mem
-/
theorem mem_span_insert_exchange :
    x in span K (insert y s) -> x ∉ span K s -> y in span K (insert x s) := by
  simp only [mem_span_insert, forall_exists_index, and_imp]
  rintro a z hz rfl h
  refine ⟨a⁻¹, -a⁻¹ • z, smul_mem _ _ hz, ?_⟩
  have a0 : a != 0 := by
    rintro rfl
    simp_all
  match_scalars <;> simp [a0]

/--
theorem `LinearIndepOn.insert` / 定理 `LinearIndepOn.insert`

English:
theorem LinearIndepOn.insert
  statement: {s : Set ι} {x : ι} (hs : LinearIndepOn K v s)
  proof: by
  rw [← union_singleton]
  have x0 : v x != 0 := fun h => hx (h ▸ zero_mem _)
  apply hs.union (LinearIndepOn.singleton x0)
  rwa [image_singleton, disjoint_span_singleton' x0]

中文:
定理 LinearIndepOn.insert
  结论: {s : 集合 ι} {x : ι} (hs : LinearIndepOn K v s)
  证明: by
  rw [← union_singleton]
  have x0 : v x != 0 := fun h => hx (h ▸ zero_mem _)
  apply hs.union (LinearIndepOn.singleton x0)
  rwa [image_singleton, disjoint_span_singleton' x0]
-/
protected theorem LinearIndepOn.insert {s : Set ι} {x : ι} (hs : LinearIndepOn K v s)
    (hx : v x ∉ span K (v '' s)) : LinearIndepOn K v (insert x s) := by
  rw [← union_singleton]
  have x0 : v x != 0 := fun h => hx (h ▸ zero_mem _)
  apply hs.union (LinearIndepOn.singleton x0)
  rwa [image_singleton, disjoint_span_singleton' x0]

/--
theorem `LinearIndepOn.id_insert` / 定理 `LinearIndepOn.id_insert`

English:
theorem LinearIndepOn.id_insert
  given: (hs : LinearIndepOn K id s) (hx : x ∉ span K s)
  proof: hs.insert ((image_id s).symm ▸ hx)

中文:
定理 LinearIndepOn.id_insert
  条件: (hs : LinearIndepOn K id s) (hx : x ∉ span K s)
  证明: hs.insert ((image_id s).symm ▸ hx)
-/
protected theorem LinearIndepOn.id_insert (hs : LinearIndepOn K id s) (hx : x ∉ span K s) :
    LinearIndepOn K id (insert x s) :=
  hs.insert ((image_id s).symm ▸ hx)

/--
theorem `linearIndependent_option'` / 定理 `linearIndependent_option'`

English:
theorem linearIndependent_option'
  proof: by
  -- Porting note: Explicit universe level is required in `Equiv.optionEquivSumPUnit`.
  rw [← linearIndependent_equiv (Equiv.optionEquivSumPUnit.{u'} ι).symm]; rw [linearIndependent_sum]; rw [@range_unique _ PUnit]; rw [@linearIndependent_unique_iff PUnit]; rw [disjoint_span_singleton]
  dsimp [(· ∘ ·)]
refine ⟨fun h => ⟨h.1, fun hx => h.2.1 h.2.2 hx⟩, fun h => ⟨h.1, ?_, fun hx => (h.2 hx).elim⟩⟩
  rintro rfl
  exact h.2 (zero_mem _)

中文:
定理 linearIndependent_option'
  证明: by
  -- Porting note: Explicit universe level is required in `Equiv.optionEquivSumPUnit`.
  rw [← linearIndependent_equiv (Equiv.optionEquivSumPUnit.{u'} ι).symm]; rw [linearIndependent_sum]; rw [@range_unique _ PUnit]; rw [@linearIndependent_unique_iff PUnit]; rw [disjoint_span_singleton]
  dsimp [(· ∘ ·)]
refine ⟨fun h => ⟨h.1, fun hx => h.2.1 h.2.2 hx⟩, fun h => ⟨h.1, ?_, fun hx => (h.2 hx).elim⟩⟩
  rintro rfl
  exact h.2 (zero_mem _)
-/
theorem linearIndependent_option' :
    LinearIndependent K (fun o => Option.casesOn' o x v : Option ι -> V) ↔
      LinearIndependent K v ∧ x ∉ Submodule.span K (range v) := by
  -- Porting note: Explicit universe level is required in `Equiv.optionEquivSumPUnit`.
  rw [← linearIndependent_equiv (Equiv.optionEquivSumPUnit.{u'} ι).symm]; rw [linearIndependent_sum]; rw [@range_unique _ PUnit]; rw [@linearIndependent_unique_iff PUnit]; rw [disjoint_span_singleton]
  dsimp [(· ∘ ·)]
refine ⟨fun h => ⟨h.1, fun hx => h.2.1 h.2.2 hx⟩, fun h => ⟨h.1, ?_, fun hx => (h.2 hx).elim⟩⟩
  rintro rfl
  exact h.2 (zero_mem _)

/--
theorem `LinearIndependent.option` / 定理 `LinearIndependent.option`

English:
theorem LinearIndependent.option
  statement: (hv : LinearIndependent K v)
  proof: linearIndependent_option'.2 ⟨hv, hx⟩

中文:
定理 LinearIndependent.option
  结论: (hv : LinearIndependent K v)
  证明: linearIndependent_option'.2 ⟨hv, hx⟩

Depends on / 依赖: linearIndependent_option
-/
theorem LinearIndependent.option (hv : LinearIndependent K v)
    (hx : x ∉ Submodule.span K (range v)) :
    LinearIndependent K (fun o => Option.casesOn' o x v : Option ι -> V) :=
  linearIndependent_option'.2 ⟨hv, hx⟩

/--
theorem `linearIndependent_option` / 定理 `linearIndependent_option`

English:
theorem linearIndependent_option
  given: {v : Option ι -> V}
  statement: LinearIndependent K v ↔
  proof: by
  simp only [← linearIndependent_option', Option.casesOn'_none_coe]

中文:
定理 linearIndependent_option
  条件: {v : 选项类型 ι -> V}
  结论: LinearIndependent K v ↔
  证明: by
  simp only [← linearIndependent_option', Option.casesOn'_none_coe]

Depends on / 依赖: Option.casesOn, _none_coe, casesOn, linearIndependent_option
-/
theorem linearIndependent_option {v : Option ι -> V} : LinearIndependent K v ↔
    LinearIndependent K (v ∘ (↑) : ι -> V) ∧
      v none ∉ Submodule.span K (range (v ∘ (↑) : ι -> V)) := by
  simp only [← linearIndependent_option', Option.casesOn'_none_coe]

/--
theorem `linearIndepOn_insert` / 定理 `linearIndepOn_insert`

English:
theorem linearIndepOn_insert
  given: {s : Set ι} {a : ι} {f : ι -> V} (has : a ∉ s)
  proof: by
  classical
  rw [LinearIndepOn]; rw [LinearIndepOn]; rw [← linearIndependent_equiv
    ((Equiv.optionEquivSumPUnit _).trans (Equiv.Set.insert has).symm)]; rw [linearIndependent_option]
  simp only [comp_def]
  rw [range_comp']
  simp

中文:
定理 linearIndepOn_insert
  条件: {s : 集合 ι} {a : ι} {f : ι -> V} (has : a ∉ s)
  证明: by
  classical
  rw [LinearIndepOn]; rw [LinearIndepOn]; rw [← linearIndependent_equiv
    ((Equiv.optionEquivSumPUnit _).trans (Equiv.Set.insert has).symm)]; rw [linearIndependent_option]
  simp only [comp_def]
  rw [range_comp']
  simp

Depends on / 依赖: Equiv.Set.insert, Equiv.optionEquivSumPUnit, LinearIndepOn, classical, comp_def, insert, linearIndependent_equiv, linearIndependent_option, optionEquivSumPUnit, range_comp
-/
theorem linearIndepOn_insert {s : Set ι} {a : ι} {f : ι -> V} (has : a ∉ s) :
    LinearIndepOn K f (insert a s) ↔ LinearIndepOn K f s ∧ f a ∉ Submodule.span K (f '' s) := by
  classical
  rw [LinearIndepOn]; rw [LinearIndepOn]; rw [← linearIndependent_equiv
    ((Equiv.optionEquivSumPUnit _).trans (Equiv.Set.insert has).symm)]; rw [linearIndependent_option]
  simp only [comp_def]
  rw [range_comp']
  simp

/--
theorem `linearIndepOn_id_insert` / 定理 `linearIndepOn_id_insert`

English:
theorem linearIndepOn_id_insert
  given: (hxs : x ∉ s)
  proof: (linearIndepOn_insert (f := id) hxs).trans by simp

中文:
定理 linearIndepOn_id_insert
  条件: (hxs : x ∉ s)
  证明: (linearIndepOn_insert (f := id) hxs).trans by simp

Depends on / 依赖: linearIndepOn_insert
-/
theorem linearIndepOn_id_insert (hxs : x ∉ s) :
    LinearIndepOn K id (insert x s) ↔ LinearIndepOn K id s ∧ x ∉ Submodule.span K s :=
(linearIndepOn_insert (f := id) hxs).trans by simp

/--
theorem `linearIndepOn_insert_iff` / 定理 `linearIndepOn_insert_iff`

English:
theorem linearIndepOn_insert_iff
  given: {s : Set ι} {a : ι} {f : ι -> V}
  proof: by
  by_cases has : a in s
  · simp [insert_eq_of_mem has, has]
  simp [linearIndepOn_insert has, has]

中文:
定理 linearIndepOn_insert_iff
  条件: {s : 集合 ι} {a : ι} {f : ι -> V}
  证明: by
  by_cases has : a in s
  · simp [insert_eq_of_mem has, has]
  simp [linearIndepOn_insert has, has]

Depends on / 依赖: insert_eq_of_mem, linearIndepOn_insert
-/
theorem linearIndepOn_insert_iff {s : Set ι} {a : ι} {f : ι -> V} :
    LinearIndepOn K f (insert a s) ↔ LinearIndepOn K f s ∧ (f a in span K (f '' s) -> a in s) := by
  by_cases has : a in s
  · simp [insert_eq_of_mem has, has]
  simp [linearIndepOn_insert has, has]

/--
theorem `linearIndepOn_id_insert_iff` / 定理 `linearIndepOn_id_insert_iff`

English:
theorem linearIndepOn_id_insert_iff
  given: {a : V} {s : Set V}
  proof: by
  simpa using linearIndepOn_insert_iff (a := a) (f := id)

中文:
定理 linearIndepOn_id_insert_iff
  条件: {a : V} {s : 集合 V}
  证明: by
  simpa using linearIndepOn_insert_iff (a := a) (f := id)

Depends on / 依赖: linearIndepOn_insert_iff
-/
theorem linearIndepOn_id_insert_iff {a : V} {s : Set V} :
    LinearIndepOn K id (insert a s) ↔ LinearIndepOn K id s ∧ (a in span K s -> a in s) := by
  simpa using linearIndepOn_insert_iff (a := a) (f := id)

/--
theorem `LinearIndepOn.mem_span_iff` / 定理 `LinearIndepOn.mem_span_iff`

English:
theorem LinearIndepOn.mem_span_iff
  given: {s : Set ι} {a : ι} {f : ι -> V} (h : LinearIndepOn K f s)
  proof: by
  by_cases has : a in s
  · exact iff_of_true (subset_span <| mem_image_of_mem f has) fun _ => has
  simp [linearIndepOn_insert_iff, h, has]

中文:
定理 LinearIndepOn.mem_span_iff
  条件: {s : 集合 ι} {a : ι} {f : ι -> V} (h : LinearIndepOn K f s)
  证明: by
  by_cases has : a in s
  · exact iff_of_true (subset_span <| mem_image_of_mem f has) fun _ => has
  simp [linearIndepOn_insert_iff, h, has]

Depends on / 依赖: iff_of_true, linearIndepOn_insert_iff, mem_image_of_mem, subset_span
-/
theorem LinearIndepOn.mem_span_iff {s : Set ι} {a : ι} {f : ι -> V} (h : LinearIndepOn K f s) :
    f a in Submodule.span K (f '' s) ↔ (LinearIndepOn K f (insert a s) -> a in s) := by
  by_cases has : a in s
  · exact iff_of_true (subset_span <| mem_image_of_mem f has) fun _ => has
  simp [linearIndepOn_insert_iff, h, has]

/--
theorem `LinearIndepOn.notMem_span_iff` / 定理 `LinearIndepOn.notMem_span_iff`

English:
theorem LinearIndepOn.notMem_span_iff
  given: {s : Set ι} {a : ι} {f : ι -> V} (h : LinearIndepOn K f s)
  proof: by
  rw [h.mem_span_iff]; rw [Classical.not_imp]

中文:
定理 LinearIndepOn.notMem_span_iff
  条件: {s : 集合 ι} {a : ι} {f : ι -> V} (h : LinearIndepOn K f s)
  证明: by
  rw [h.mem_span_iff]; rw [Classical.not_imp]

Depends on / 依赖: Classical, Classical.not_imp, h.mem_span_iff, mem_span_iff, not_imp
-/
theorem LinearIndepOn.notMem_span_iff {s : Set ι} {a : ι} {f : ι -> V} (h : LinearIndepOn K f s) :
    f a ∉ Submodule.span K (f '' s) ↔ LinearIndepOn K f (insert a s) ∧ a ∉ s := by
  rw [h.mem_span_iff]; rw [Classical.not_imp]

/--
theorem `LinearIndepOn.mem_span_iff_id` / 定理 `LinearIndepOn.mem_span_iff_id`

English:
theorem LinearIndepOn.mem_span_iff_id
  given: {s : Set V} {a : V} (h : LinearIndepOn K id s)
  proof: by
  simpa using h.mem_span_iff (a := a)

中文:
定理 LinearIndepOn.mem_span_iff_id
  条件: {s : 集合 V} {a : V} (h : LinearIndepOn K id s)
  证明: by
  simpa using h.mem_span_iff (a := a)

Depends on / 依赖: h.mem_span_iff, mem_span_iff
-/
theorem LinearIndepOn.mem_span_iff_id {s : Set V} {a : V} (h : LinearIndepOn K id s) :
    a in Submodule.span K s ↔ (LinearIndepOn K id (insert a s) -> a in s) := by
  simpa using h.mem_span_iff (a := a)

/--
theorem `LinearIndepOn.notMem_span_iff_id` / 定理 `LinearIndepOn.notMem_span_iff_id`

English:
theorem LinearIndepOn.notMem_span_iff_id
  given: {s : Set V} {a : V} (h : LinearIndepOn K id s)
  proof: by
  rw [h.mem_span_iff_id]; rw [Classical.not_imp]

中文:
定理 LinearIndepOn.notMem_span_iff_id
  条件: {s : 集合 V} {a : V} (h : LinearIndepOn K id s)
  证明: by
  rw [h.mem_span_iff_id]; rw [Classical.not_imp]

Depends on / 依赖: Classical, Classical.not_imp, h.mem_span_iff_id, mem_span_iff_id, not_imp
-/
theorem LinearIndepOn.notMem_span_iff_id {s : Set V} {a : V} (h : LinearIndepOn K id s) :
    a ∉ Submodule.span K s ↔ LinearIndepOn K id (insert a s) ∧ a ∉ s := by
  rw [h.mem_span_iff_id]; rw [Classical.not_imp]

/--
theorem `linearIndepOn_id_pair` / 定理 `linearIndepOn_id_pair`

English:
theorem linearIndepOn_id_pair
  given: {x y : V} (hx : x != 0) (hy : forall a : K, a • x != y)
  proof: by
rw [pair_comm]; exact .id_insert (.singleton hx) by simpa [mem_span_singleton]

中文:
定理 linearIndepOn_id_pair
  条件: {x y : V} (hx : x != 0) (hy : 对任意 a : K, a • x != y)
  证明: by
rw [pair_comm]; exact .id_insert (.singleton hx) by simpa [mem_span_singleton]

Depends on / 依赖: id_insert, mem_span_singleton, pair_comm, singleton
-/
theorem linearIndepOn_id_pair {x y : V} (hx : x != 0) (hy : forall a : K, a • x != y) :
    LinearIndepOn K id {x, y} := by
rw [pair_comm]; exact .id_insert (.singleton hx) by simpa [mem_span_singleton]

/--
theorem `linearIndepOn_pair_iff` / 定理 `linearIndepOn_pair_iff`

English:
theorem linearIndepOn_pair_iff
  given: {i j : ι} (v : ι -> V) (hij : i != j) (hi : v i != 0)
  proof: by
  rw [pair_comm]
  convert! linearIndepOn_insert (s := { i }) (a := j) hij.symm
  simp [hi, mem_span_singleton]

中文:
定理 linearIndepOn_pair_iff
  条件: {i j : ι} (v : ι -> V) (hij : i != j) (hi : v i != 0)
  证明: by
  rw [pair_comm]
  convert! linearIndepOn_insert (s := { i }) (a := j) hij.symm
  simp [hi, mem_span_singleton]

Depends on / 依赖: convert, hij.symm, linearIndepOn_insert, mem_span_singleton, pair_comm
-/
theorem linearIndepOn_pair_iff {i j : ι} (v : ι -> V) (hij : i != j) (hi : v i != 0) :
    LinearIndepOn K v {i, j} ↔ forall (c : K), c • v i != v j := by
  rw [pair_comm]
  convert! linearIndepOn_insert (s := { i }) (a := j) hij.symm
  simp [hi, mem_span_singleton]

/--
theorem `LinearIndependent.pair_iff'` / 定理 `LinearIndependent.pair_iff'`

English:
theorem LinearIndependent.pair_iff'
  given: {x y : V} (hx : x != 0)
  proof: by
  rw [← linearIndepOn_univ_iff]; rw [← Finset.coe_univ]; rw [show @Finset.univ (Fin 2) _ = {0]; rw [1} from rfl]; rw [Finset.coe_insert]; rw [Finset.coe_singleton]; rw [linearIndepOn_pair_iff _ (by simp) (by simpa)]
  simp

中文:
定理 LinearIndependent.pair_iff'
  条件: {x y : V} (hx : x != 0)
  证明: by
  rw [← linearIndepOn_univ_iff]; rw [← Finset.coe_univ]; rw [show @Finset.univ (Fin 2) _ = {0]; rw [1} from rfl]; rw [Finset.coe_insert]; rw [Finset.coe_singleton]; rw [linearIndepOn_pair_iff _ (by simp) (by simpa)]
  simp

Depends on / 依赖: Finset, Finset.coe_insert, Finset.coe_singleton, Finset.coe_univ, Finset.univ, coe_insert, coe_singleton, coe_univ, linearIndepOn_pair_iff, linearIndepOn_univ_iff
-/
theorem LinearIndependent.pair_iff' {x y : V} (hx : x != 0) :
    LinearIndependent K ![x, y] ↔ forall a : K, a • x != y := by
  rw [← linearIndepOn_univ_iff]; rw [← Finset.coe_univ]; rw [show @Finset.univ (Fin 2) _ = {0]; rw [1} from rfl]; rw [Finset.coe_insert]; rw [Finset.coe_singleton]; rw [linearIndepOn_pair_iff _ (by simp) (by simpa)]
  simp

/--
theorem `linearIndependent_finCons` / 定理 `linearIndependent_finCons`

English:
theorem linearIndependent_finCons
  given: {n} {v : Fin n -> V}
  proof: by
  rw [← linearIndependent_equiv (finSuccEquiv n).symm]; rw [linearIndependent_option]
  rfl

@[deprecated (since := "2026-04-07")]
alias linearIndependent_fin_cons := linearIndependent_finCons

中文:
定理 linearIndependent_finCons
  条件: {n} {v : 有限集 n -> V}
  证明: by
  rw [← linearIndependent_equiv (finSuccEquiv n).symm]; rw [linearIndependent_option]
  rfl

@[deprecated (since := "2026-04-07")]
alias linearIndependent_fin_cons := linearIndependent_finCons

Depends on / 依赖: finSuccEquiv, linearIndependent_equiv, linearIndependent_option
-/
theorem linearIndependent_finCons {n} {v : Fin n -> V} :
    LinearIndependent K (Fin.cons x v : Fin (n + 1) -> V) ↔
      LinearIndependent K v ∧ x ∉ Submodule.span K (range v) := by
  rw [← linearIndependent_equiv (finSuccEquiv n).symm]; rw [linearIndependent_option]
  rfl

@[deprecated (since := "2026-04-07")]
alias linearIndependent_fin_cons := linearIndependent_finCons

/--
theorem `linearIndependent_finSnoc` / 定理 `linearIndependent_finSnoc`

English:
theorem linearIndependent_finSnoc
  given: {n} {v : Fin n -> V}
  proof: by
  rw [Fin.snoc_eq_cons_rotate]; rw [← Function.comp_def]; rw [linearIndependent_equiv]; rw [linearIndependent_finCons]

@[deprecated (since := "2026-04-07")]
alias linearIndependent_fin_snoc := linearIndependent_finSnoc

中文:
定理 linearIndependent_finSnoc
  条件: {n} {v : 有限集 n -> V}
  证明: by
  rw [Fin.snoc_eq_cons_rotate]; rw [← Function.comp_def]; rw [linearIndependent_equiv]; rw [linearIndependent_finCons]

@[deprecated (since := "2026-04-07")]
alias linearIndependent_fin_snoc := linearIndependent_finSnoc

Depends on / 依赖: Fin.snoc_eq_cons_rotate, Function, Function.comp_def, comp_def, linearIndependent_equiv, linearIndependent_finCons, snoc_eq_cons_rotate
-/
theorem linearIndependent_finSnoc {n} {v : Fin n -> V} :
    LinearIndependent K (Fin.snoc v x : Fin (n + 1) -> V) ↔
      LinearIndependent K v ∧ x ∉ Submodule.span K (range v) := by
  rw [Fin.snoc_eq_cons_rotate]; rw [← Function.comp_def]; rw [linearIndependent_equiv]; rw [linearIndependent_finCons]

@[deprecated (since := "2026-04-07")]
alias linearIndependent_fin_snoc := linearIndependent_finSnoc

/--
theorem `LinearIndependent.finCons` / 定理 `LinearIndependent.finCons`

English:
theorem LinearIndependent.finCons
  statement: {n} {v : Fin n -> V} (hv : LinearIndependent K v)
  proof: linearIndependent_finCons.2 ⟨hv, hx⟩

@[deprecated (since := "2026-04-07")]
alias LinearIndependent.fin_cons := LinearIndependent.finCons

中文:
定理 LinearIndependent.finCons
  结论: {n} {v : 有限集 n -> V} (hv : LinearIndependent K v)
  证明: linearIndependent_finCons.2 ⟨hv, hx⟩

@[deprecated (since := "2026-04-07")]
alias LinearIndependent.fin_cons := LinearIndependent.finCons

Depends on / 依赖: linearIndependent_finCons
-/
theorem LinearIndependent.finCons {n} {v : Fin n -> V} (hv : LinearIndependent K v)
    (hx : x ∉ Submodule.span K (range v)) : LinearIndependent K (Fin.cons x v : Fin (n + 1) -> V) :=
  linearIndependent_finCons.2 ⟨hv, hx⟩

@[deprecated (since := "2026-04-07")]
alias LinearIndependent.fin_cons := LinearIndependent.finCons

/--
lemma `LinearIndependent.finSnoc` / 引理 `LinearIndependent.finSnoc`

English:
lemma LinearIndependent.finSnoc
  statement: {n} {v : Fin n -> V} (hv : LinearIndependent K v)
  proof: linearIndependent_finSnoc.2 ⟨hv, hx⟩

中文:
引理 LinearIndependent.finSnoc
  结论: {n} {v : 有限集 n -> V} (hv : LinearIndependent K v)
  证明: linearIndependent_finSnoc.2 ⟨hv, hx⟩

Depends on / 依赖: linearIndependent_finSnoc
-/
lemma LinearIndependent.finSnoc {n} {v : Fin n -> V} (hv : LinearIndependent K v)
    (hx : x ∉ Submodule.span K (range v)) : LinearIndependent K (Fin.snoc v x : Fin (n + 1) -> V) :=
  linearIndependent_finSnoc.2 ⟨hv, hx⟩

/--
theorem `LinearIndependent.finSnoc_of_not_mem_span_over` / 定理 `LinearIndependent.finSnoc_of_not_mem_span_over`

English:
theorem LinearIndependent.finSnoc_of_not_mem_span_over
  proof: by
  apply hv.finSnoc' v x
  intro c y hcy heq
  by_contra hc
  apply hx
  have hc' : algebraMap R K c != 0 := by
    rwa [ne_eq, FaithfulSMul.algebraMap_eq_zero_iff]
  rw [← algebraMap_smul K c x] at heq
  rw [(eq_inv_smul_iff₀ hc').mpr (eq_neg_of_add_eq_zero_left heq)]; rw [smul_neg]
  exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.span_subset_span R K _ hcy))

中文:
定理 LinearIndependent.finSnoc_of_not_mem_span_over
  证明: by
  apply hv.finSnoc' v x
  intro c y hcy heq
  by_contra hc
  apply hx
  have hc' : algebraMap R K c != 0 := by
    rwa [ne_eq, FaithfulSMul.algebraMap_eq_zero_iff]
  rw [← algebraMap_smul K c x] at heq
  rw [(eq_inv_smul_iff₀ hc').mpr (eq_neg_of_add_eq_zero_left heq)]; rw [smul_neg]
  exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.span_subset_span R K _ hcy))

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_eq_zero_iff, Submodule, Submodule.neg_mem, Submodule.smul_mem, Submodule.span_subset_span, algebraMap, algebraMap_eq_zero_iff, algebraMap_smul, eq_neg_of_add_eq_zero_left, finSnoc, hv.finSnoc, ne_eq, neg_mem, smul_mem, smul_neg, span_subset_span
-/
theorem LinearIndependent.finSnoc_of_not_mem_span_over
    {R : Type*} {K : Type*} {M : Type*}
    [CommRing R] [DivisionRing K] [AddCommGroup M]
    [Algebra R K] [Module K M] [Module R M] [IsScalarTower R K M] [FaithfulSMul R K]
    {n : Nat} {v : Fin n -> M} (hv : LinearIndependent R v) {x : M}
    (hx : x ∉ Submodule.span K (Set.range v)) :
    LinearIndependent R (Fin.snoc v x) := by
  apply hv.finSnoc' v x
  intro c y hcy heq
  by_contra hc
  apply hx
  have hc' : algebraMap R K c != 0 := by
    rwa [ne_eq, FaithfulSMul.algebraMap_eq_zero_iff]
  rw [← algebraMap_smul K c x] at heq
  rw [(eq_inv_smul_iff₀ hc').mpr (eq_neg_of_add_eq_zero_left heq)]; rw [smul_neg]
  exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.span_subset_span R K _ hcy))

/--
theorem `linearIndependent_finSucc` / 定理 `linearIndependent_finSucc`

English:
theorem linearIndependent_finSucc
  given: {n} {v : Fin (n + 1) -> V}
  proof: by
  rw [← linearIndependent_finCons]; rw [Fin.cons_self_tail]

@[deprecated (since := "2026-04-07")]
alias linearIndependent_fin_succ := linearIndependent_finSucc

中文:
定理 linearIndependent_finSucc
  条件: {n} {v : 有限集 (n + 1) -> V}
  证明: by
  rw [← linearIndependent_finCons]; rw [Fin.cons_self_tail]

@[deprecated (since := "2026-04-07")]
alias linearIndependent_fin_succ := linearIndependent_finSucc

Depends on / 依赖: Fin.cons_self_tail, cons_self_tail, linearIndependent_finCons
-/
theorem linearIndependent_finSucc {n} {v : Fin (n + 1) -> V} :
    LinearIndependent K v ↔
      LinearIndependent K (Fin.tail v) ∧ v 0 ∉ Submodule.span K (range <| Fin.tail v) := by
  rw [← linearIndependent_finCons]; rw [Fin.cons_self_tail]

@[deprecated (since := "2026-04-07")]
alias linearIndependent_fin_succ := linearIndependent_finSucc

/--
theorem `linearIndependent_finSucc'` / 定理 `linearIndependent_finSucc'`

English:
theorem linearIndependent_finSucc'
  given: {n} {v : Fin (n + 1) -> V}
  statement: LinearIndependent K v ↔
  proof: by
  rw [← linearIndependent_finSnoc]; rw [Fin.snoc_init_self]

@[deprecated (since := "2026-04-07")]
alias linearIndependent_fin_succ' := linearIndependent_finSucc'

中文:
定理 linearIndependent_finSucc'
  条件: {n} {v : 有限集 (n + 1) -> V}
  结论: LinearIndependent K v ↔
  证明: by
  rw [← linearIndependent_finSnoc]; rw [Fin.snoc_init_self]

@[deprecated (since := "2026-04-07")]
alias linearIndependent_fin_succ' := linearIndependent_finSucc'

Depends on / 依赖: Fin.snoc_init_self, linearIndependent_finSnoc, snoc_init_self
-/
theorem linearIndependent_finSucc' {n} {v : Fin (n + 1) -> V} : LinearIndependent K v ↔
    LinearIndependent K (Fin.init v) ∧ v (Fin.last _) ∉ Submodule.span K (range <| Fin.init v) := by
  rw [← linearIndependent_finSnoc]; rw [Fin.snoc_init_self]

@[deprecated (since := "2026-04-07")]
alias linearIndependent_fin_succ' := linearIndependent_finSucc'

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `equiv_linearIndependent` / `equiv_linearIndependent` 的定义

English:
definition equiv_linearIndependent
  signature: (n : Nat)
  body: ⟨⟨Fin.tail s.val, (linearIndependent_finSucc.mp s.property).left⟩,
    ⟨s.val 0, (linearIndependent_finSucc.mp s.property).right⟩⟩
  invFun s := ⟨Fin.cons s.2.val s.1.val,
    linearIndependent_finCons.mpr ⟨s.1.property, s.2.property⟩⟩
  left_inv _ := by simp only [Fin.cons_self_tail, Subtype.coe_eta]
  right_inv := fun ⟨_, _⟩ => by simp only [Fin.cons_zero, Subtype.coe_eta, Sigma.mk.inj_iff,
    Fin.tail_cons, heq_eq_eq, and_self]

中文:
定义 equiv_linearIndependent
  签名: (n : 自然数)
  定义体: ⟨⟨Fin.tail s.val, (linearIndependent_finSucc.mp s.property).left⟩,
    ⟨s.val 0, (linearIndependent_finSucc.mp s.property).right⟩⟩
  invFun s := ⟨Fin.cons s.2.val s.1.val,
    linearIndependent_finCons.mpr ⟨s.1.property, s.2.property⟩⟩
  left_inv _ := by simp only [Fin.cons_self_tail, Subtype.coe_eta]
  right_inv := fun ⟨_, _⟩ => by simp only [Fin.cons_zero, Subtype.coe_eta, Sigma.mk.inj_iff,
    Fin.tail_cons, heq_eq_eq, and_self]

Depends on / 依赖: Fin.tail, linearIndependent_finSucc, linearIndependent_finSucc.mp, property, s.property, s.val
-/
def equiv_linearIndependent (n : Nat) :
    { s : Fin (n + 1) -> V // LinearIndependent K s } ≃
      Σ s : { s : Fin n -> V // LinearIndependent K s },
        ((Submodule.span K (Set.range (s : Fin n -> V)))ᶜ : Set V) where
  toFun s := ⟨⟨Fin.tail s.val, (linearIndependent_finSucc.mp s.property).left⟩,
    ⟨s.val 0, (linearIndependent_finSucc.mp s.property).right⟩⟩
  invFun s := ⟨Fin.cons s.2.val s.1.val,
    linearIndependent_finCons.mpr ⟨s.1.property, s.2.property⟩⟩
  left_inv _ := by simp only [Fin.cons_self_tail, Subtype.coe_eta]
  right_inv := fun ⟨_, _⟩ => by simp only [Fin.cons_zero, Subtype.coe_eta, Sigma.mk.inj_iff,
    Fin.tail_cons, heq_eq_eq, and_self]

/--
theorem `linearIndependent_fin2` / 定理 `linearIndependent_fin2`

English:
theorem linearIndependent_fin2
  given: {f : Fin 2 -> V}
  proof: by
  rw [linearIndependent_finSucc]; rw [linearIndependent_unique_iff]; rw [range_unique]; rw [mem_span_singleton]; rw [not_exists]; rw [show Fin.tail f default = f 1 by rw [← Fin.succ_zero_eq_one]; rfl]

中文:
定理 linearIndependent_fin2
  条件: {f : 有限集 2 -> V}
  证明: by
  rw [linearIndependent_finSucc]; rw [linearIndependent_unique_iff]; rw [range_unique]; rw [mem_span_singleton]; rw [not_exists]; rw [show Fin.tail f default = f 1 by rw [← Fin.succ_zero_eq_one]; rfl]

Depends on / 依赖: Fin.succ_zero_eq_one, Fin.tail, linearIndependent_finSucc, linearIndependent_unique_iff, mem_span_singleton, not_exists, range_unique, succ_zero_eq_one
-/
theorem linearIndependent_fin2 {f : Fin 2 -> V} :
    LinearIndependent K f ↔ f 1 != 0 ∧ forall a : K, a • f 1 != f 0 := by
  rw [linearIndependent_finSucc]; rw [linearIndependent_unique_iff]; rw [range_unique]; rw [mem_span_singleton]; rw [not_exists]; rw [show Fin.tail f default = f 1 by rw [← Fin.succ_zero_eq_one]; rfl]

/--
theorem `exists_linearIndepOn_extension` / 定理 `exists_linearIndepOn_extension`

English:
theorem exists_linearIndepOn_extension
  given: {s t : Set ι} (hs : LinearIndepOn K v s) (hst : s subseteq t)
  proof: by
  obtain ⟨b, sb, h⟩ := by
    refine zorn_subset_nonempty { b | b subseteq t ∧ LinearIndepOn K v b} ?_ _ ⟨hst, hs⟩
    · refine fun c hc cc _c0 => ⟨⋃₀ c, ⟨?_, ?_⟩, fun x => ?_⟩
      · exact sUnion_subset fun x xc => (hc xc).1
      · exact linearIndepOn_sUnion_of_directed cc.directedOn fun x xc => (hc xc).2
      · exact subset_sUnion_of_mem
  refine ⟨b, h.prop.1, sb, fun _ ⟨x, hx, hvx⟩ => by_contra fun hn => hn ?_, h.prop.2⟩
  subst hvx
exact subset_span mem_image_of_mem v h.mem_of_prop_insert
    ⟨insert_subset hx h.prop.1, h.prop.2.insert hn⟩

中文:
定理 存在_linearIndepOn_extension
  条件: {s t : 集合 ι} (hs : LinearIndepOn K v s) (hst : s subseteq t)
  证明: by
  obtain ⟨b, sb, h⟩ := by
    refine zorn_subset_nonempty { b | b subseteq t ∧ LinearIndepOn K v b} ?_ _ ⟨hst, hs⟩
    · refine fun c hc cc _c0 => ⟨⋃₀ c, ⟨?_, ?_⟩, fun x => ?_⟩
      · exact sUnion_subset fun x xc => (hc xc).1
      · exact linearIndepOn_sUnion_of_directed cc.directedOn fun x xc => (hc xc).2
      · exact subset_sUnion_of_mem
  refine ⟨b, h.prop.1, sb, fun _ ⟨x, hx, hvx⟩ => by_contra fun hn => hn ?_, h.prop.2⟩
  subst hvx
exact subset_span mem_image_of_mem v h.mem_of_prop_insert
    ⟨insert_subset hx h.prop.1, h.prop.2.insert hn⟩

Depends on / 依赖: LinearIndepOn, cc.directedOn, directedOn, h.mem_of_prop_insert, h.prop, insert_subset, linearIndepOn_sUnion_of_directed, mem_image_of_mem, mem_of_prop_insert, sUnion_subset, subset_sUnion_of_mem, subset_span, subseteq, zorn_subset_nonempty
-/
theorem exists_linearIndepOn_extension {s t : Set ι} (hs : LinearIndepOn K v s) (hst : s subseteq t) :
    exists b subseteq t, s subseteq b ∧ v '' t subseteq span K (v '' b) ∧ LinearIndepOn K v b := by
  obtain ⟨b, sb, h⟩ := by
    refine zorn_subset_nonempty { b | b subseteq t ∧ LinearIndepOn K v b} ?_ _ ⟨hst, hs⟩
    · refine fun c hc cc _c0 => ⟨⋃₀ c, ⟨?_, ?_⟩, fun x => ?_⟩
      · exact sUnion_subset fun x xc => (hc xc).1
      · exact linearIndepOn_sUnion_of_directed cc.directedOn fun x xc => (hc xc).2
      · exact subset_sUnion_of_mem
  refine ⟨b, h.prop.1, sb, fun _ ⟨x, hx, hvx⟩ => by_contra fun hn => hn ?_, h.prop.2⟩
  subst hvx
exact subset_span mem_image_of_mem v h.mem_of_prop_insert
    ⟨insert_subset hx h.prop.1, h.prop.2.insert hn⟩

/--
theorem `exists_linearIndepOn_id_extension` / 定理 `exists_linearIndepOn_id_extension`

English:
theorem exists_linearIndepOn_id_extension
  given: (hs : LinearIndepOn K id s) (hst : s subseteq t)
  proof: by
  convert! exists_linearIndepOn_extension hs hst <;> simp

中文:
定理 存在_linearIndepOn_id_extension
  条件: (hs : LinearIndepOn K id s) (hst : s subseteq t)
  证明: by
  convert! exists_linearIndepOn_extension hs hst <;> simp

Depends on / 依赖: convert, exists_linearIndepOn_extension
-/
theorem exists_linearIndepOn_id_extension (hs : LinearIndepOn K id s) (hst : s subseteq t) :
    exists b subseteq t, s subseteq b ∧ t subseteq span K b ∧ LinearIndepOn K id b := by
  convert! exists_linearIndepOn_extension hs hst <;> simp

variable (K t)

/--
theorem `exists_linearIndependent` / 定理 `exists_linearIndependent`

English:
theorem exists_linearIndependent
  proof: by
  obtain ⟨b, hb₁, -, hb₂, hb₃⟩ :=
    exists_linearIndepOn_id_extension (linearIndependent_empty K V) (Set.empty_subset t)
  exact ⟨b, hb₁, (span_eq_of_le _ hb₂ (Submodule.span_mono hb₁)).symm, hb₃⟩

中文:
定理 存在_linearIndependent
  证明: by
  obtain ⟨b, hb₁, -, hb₂, hb₃⟩ :=
    exists_linearIndepOn_id_extension (linearIndependent_empty K V) (Set.empty_subset t)
  exact ⟨b, hb₁, (span_eq_of_le _ hb₂ (Submodule.span_mono hb₁)).symm, hb₃⟩

Depends on / 依赖: Set.empty_subset, Submodule, Submodule.span_mono, empty_subset, exists_linearIndepOn_id_extension, linearIndependent_empty, span_eq_of_le, span_mono
-/
theorem exists_linearIndependent :
    exists b subseteq t, span K b = span K t ∧ LinearIndependent K ((↑) : b -> V) := by
  obtain ⟨b, hb₁, -, hb₂, hb₃⟩ :=
    exists_linearIndepOn_id_extension (linearIndependent_empty K V) (Set.empty_subset t)
  exact ⟨b, hb₁, (span_eq_of_le _ hb₂ (Submodule.span_mono hb₁)).symm, hb₃⟩

/--
lemma `exists_linearIndependent'` / 引理 `exists_linearIndependent'`

English:
lemma exists_linearIndependent'
  given: (v : ι -> V)
  proof: by
  obtain ⟨t, ht, hsp, hli⟩ := exists_linearIndependent K (Set.range v)
  choose f hf using ht
  let s : Set ι := Set.range (fun a : t => f a.property)
  have hs {i : ι} (hi : i in s) : v i in t := by obtain ⟨a, rfl⟩ := hi; simp [hf]
  let f' (a : s) : t := ⟨v a.val, hs a.property⟩
  refine ⟨s, Subtype.val, Subtype.val_injective, hsp.symm ▸ by congr; aesop, ?_⟩
  · rw [← show Subtype.val ∘ f' = v ∘ Subtype.val by ext; simp [f']]
    apply hli.comp
    rintro ⟨i, x, rfl⟩ ⟨j, y, rfl⟩ hij
    simp only [Subtype.ext_iff, hf, f'] at hij
    simp [hij]

中文:
引理 存在_linearIndependent'
  条件: (v : ι -> V)
  证明: by
  obtain ⟨t, ht, hsp, hli⟩ := exists_linearIndependent K (Set.range v)
  choose f hf using ht
  let s : Set ι := Set.range (fun a : t => f a.property)
  have hs {i : ι} (hi : i in s) : v i in t := by obtain ⟨a, rfl⟩ := hi; simp [hf]
  let f' (a : s) : t := ⟨v a.val, hs a.property⟩
  refine ⟨s, Subtype.val, Subtype.val_injective, hsp.symm ▸ by congr; aesop, ?_⟩
  · rw [← show Subtype.val ∘ f' = v ∘ Subtype.val by ext; simp [f']]
    apply hli.comp
    rintro ⟨i, x, rfl⟩ ⟨j, y, rfl⟩ hij
    simp only [Subtype.ext_iff, hf, f'] at hij
    simp [hij]

Depends on / 依赖: Set.range, Subtype, Subtype.ext_iff, Subtype.val, Subtype.val_injective, a.property, a.val, exists_linearIndependent, ext_iff, hli.comp, hsp.symm, property, val_injective
-/
lemma exists_linearIndependent' (v : ι -> V) :
    exists (κ : Type u') (a : κ -> ι), Injective a ∧
      Submodule.span K (Set.range (v ∘ a)) = Submodule.span K (Set.range v) ∧
      LinearIndependent K (v ∘ a) := by
  obtain ⟨t, ht, hsp, hli⟩ := exists_linearIndependent K (Set.range v)
  choose f hf using ht
  let s : Set ι := Set.range (fun a : t => f a.property)
  have hs {i : ι} (hi : i in s) : v i in t := by obtain ⟨a, rfl⟩ := hi; simp [hf]
  let f' (a : s) : t := ⟨v a.val, hs a.property⟩
  refine ⟨s, Subtype.val, Subtype.val_injective, hsp.symm ▸ by congr; aesop, ?_⟩
  · rw [← show Subtype.val ∘ f' = v ∘ Subtype.val by ext; simp [f']]
    apply hli.comp
    rintro ⟨i, x, rfl⟩ ⟨j, y, rfl⟩ hij
    simp only [Subtype.ext_iff, hf, f'] at hij
    simp [hij]

variable {K} {s t : Set ι}

/--
Definition of `LinearIndepOn.extend` / `LinearIndepOn.extend` 的定义

English:
definition LinearIndepOn.extend
  signature: (hs : LinearIndepOn K v s) (hst : s subseteq t)
  body: Classical.choose (exists_linearIndepOn_extension hs hst)

中文:
定义 LinearIndepOn.extend
  签名: (hs : LinearIndepOn K v s) (hst : s subseteq t)
  定义体: Classical.choose (exists_linearIndepOn_extension hs hst)

Depends on / 依赖: Classical, Classical.choose, exists_linearIndepOn_extension
-/
noncomputable def LinearIndepOn.extend (hs : LinearIndepOn K v s) (hst : s subseteq t) : Set ι :=
  Classical.choose (exists_linearIndepOn_extension hs hst)

/--
theorem `LinearIndepOn.extend_subset` / 定理 `LinearIndepOn.extend_subset`

English:
theorem LinearIndepOn.extend_subset
  given: (hs : LinearIndepOn K v s) (hst : s subseteq t)
  statement: hs.extend hst subseteq t
  proof: let ⟨hbt, _hsb, _htb, _hli⟩ := Classical.choose_spec (exists_linearIndepOn_extension hs hst)
  hbt

中文:
定理 LinearIndepOn.extend_subset
  条件: (hs : LinearIndepOn K v s) (hst : s subseteq t)
  结论: hs.extend hst subseteq t
  证明: let ⟨hbt, _hsb, _htb, _hli⟩ := Classical.choose_spec (exists_linearIndepOn_extension hs hst)
  hbt

Depends on / 依赖: Classical, Classical.choose_spec, _hli, _hsb, _htb, choose_spec, exists_linearIndepOn_extension
-/
theorem LinearIndepOn.extend_subset (hs : LinearIndepOn K v s) (hst : s subseteq t) : hs.extend hst subseteq t :=
  let ⟨hbt, _hsb, _htb, _hli⟩ := Classical.choose_spec (exists_linearIndepOn_extension hs hst)
  hbt

/--
theorem `LinearIndepOn.subset_extend` / 定理 `LinearIndepOn.subset_extend`

English:
theorem LinearIndepOn.subset_extend
  given: (hs : LinearIndepOn K v s) (hst : s subseteq t)
  statement: s subseteq hs.extend hst
  proof: let ⟨_hbt, hsb, _htb, _hli⟩ := Classical.choose_spec (exists_linearIndepOn_extension hs hst)
  hsb

中文:
定理 LinearIndepOn.subset_extend
  条件: (hs : LinearIndepOn K v s) (hst : s subseteq t)
  结论: s subseteq hs.extend hst
  证明: let ⟨_hbt, hsb, _htb, _hli⟩ := Classical.choose_spec (exists_linearIndepOn_extension hs hst)
  hsb

Depends on / 依赖: Classical, Classical.choose_spec, _hbt, _hli, _htb, choose_spec, exists_linearIndepOn_extension
-/
theorem LinearIndepOn.subset_extend (hs : LinearIndepOn K v s) (hst : s subseteq t) : s subseteq hs.extend hst :=
  let ⟨_hbt, hsb, _htb, _hli⟩ := Classical.choose_spec (exists_linearIndepOn_extension hs hst)
  hsb

/--
theorem `LinearIndepOn.image_subset_span_image_extend` / 定理 `LinearIndepOn.image_subset_span_image_extend`

English:
theorem LinearIndepOn.image_subset_span_image_extend
  given: (hs : LinearIndepOn K v s) (hst : s subseteq t)
  proof: let ⟨_hbt, _hsb, htb, _hli⟩ := Classical.choose_spec (exists_linearIndepOn_extension hs hst)
  htb

中文:
定理 LinearIndepOn.image_subset_span_image_extend
  条件: (hs : LinearIndepOn K v s) (hst : s subseteq t)
  证明: let ⟨_hbt, _hsb, htb, _hli⟩ := Classical.choose_spec (exists_linearIndepOn_extension hs hst)
  htb

Depends on / 依赖: Classical, Classical.choose_spec, _hbt, _hli, _hsb, choose_spec, exists_linearIndepOn_extension
-/
theorem LinearIndepOn.image_subset_span_image_extend (hs : LinearIndepOn K v s) (hst : s subseteq t) :
    v '' t subseteq span K (v '' hs.extend hst) :=
  let ⟨_hbt, _hsb, htb, _hli⟩ := Classical.choose_spec (exists_linearIndepOn_extension hs hst)
  htb

/--
theorem `LinearIndepOn.subset_span_extend` / 定理 `LinearIndepOn.subset_span_extend`

English:
theorem LinearIndepOn.subset_span_extend
  given: {s t : Set V} (hs : LinearIndepOn K id s) (hst : s subseteq t)
  proof: by
  convert! hs.image_subset_span_image_extend hst <;> simp

中文:
定理 LinearIndepOn.subset_span_extend
  条件: {s t : 集合 V} (hs : LinearIndepOn K id s) (hst : s subseteq t)
  证明: by
  convert! hs.image_subset_span_image_extend hst <;> simp

Depends on / 依赖: convert, hs.image_subset_span_image_extend, image_subset_span_image_extend
-/
theorem LinearIndepOn.subset_span_extend {s t : Set V} (hs : LinearIndepOn K id s) (hst : s subseteq t) :
    t subseteq span K (hs.extend hst) := by
  convert! hs.image_subset_span_image_extend hst <;> simp

/--
theorem `LinearIndepOn.span_image_extend_eq_span_image` / 定理 `LinearIndepOn.span_image_extend_eq_span_image`

English:
theorem LinearIndepOn.span_image_extend_eq_span_image
  given: (hs : LinearIndepOn K v s) (hst : s subseteq t)
  proof: le_antisymm (span_mono (image_mono (hs.extend_subset hst)))
    (span_le.2 (hs.image_subset_span_image_extend hst))

中文:
定理 LinearIndepOn.span_image_extend_eq_span_image
  条件: (hs : LinearIndepOn K v s) (hst : s subseteq t)
  证明: le_antisymm (span_mono (image_mono (hs.extend_subset hst)))
    (span_le.2 (hs.image_subset_span_image_extend hst))

Depends on / 依赖: extend_subset, hs.extend_subset, hs.image_subset_span_image_extend, image_mono, image_subset_span_image_extend, le_antisymm, span_le, span_mono
-/
theorem LinearIndepOn.span_image_extend_eq_span_image (hs : LinearIndepOn K v s) (hst : s subseteq t) :
    span K (v '' hs.extend hst) = span K (v '' t) :=
  le_antisymm (span_mono (image_mono (hs.extend_subset hst)))
    (span_le.2 (hs.image_subset_span_image_extend hst))

/--
theorem `LinearIndepOn.span_extend_eq_span` / 定理 `LinearIndepOn.span_extend_eq_span`

English:
theorem LinearIndepOn.span_extend_eq_span
  given: {s t : Set V} (hs : LinearIndepOn K id s) (hst : s subseteq t)
  proof: le_antisymm (span_mono (hs.extend_subset hst)) (span_le.2 (hs.subset_span_extend hst))

中文:
定理 LinearIndepOn.span_extend_eq_span
  条件: {s t : 集合 V} (hs : LinearIndepOn K id s) (hst : s subseteq t)
  证明: le_antisymm (span_mono (hs.extend_subset hst)) (span_le.2 (hs.subset_span_extend hst))

Depends on / 依赖: extend_subset, hs.extend_subset, hs.subset_span_extend, le_antisymm, span_le, span_mono, subset_span_extend
-/
theorem LinearIndepOn.span_extend_eq_span {s t : Set V} (hs : LinearIndepOn K id s) (hst : s subseteq t) :
    span K (hs.extend hst) = span K t :=
  le_antisymm (span_mono (hs.extend_subset hst)) (span_le.2 (hs.subset_span_extend hst))

/--
theorem `LinearIndepOn.linearIndepOn_extend` / 定理 `LinearIndepOn.linearIndepOn_extend`

English:
theorem LinearIndepOn.linearIndepOn_extend
  given: (hs : LinearIndepOn K v s) (hst : s subseteq t)
  proof: let ⟨_hbt, _hsb, _htb, hli⟩ := Classical.choose_spec (exists_linearIndepOn_extension hs hst)
  hli

中文:
定理 LinearIndepOn.linearIndepOn_extend
  条件: (hs : LinearIndepOn K v s) (hst : s subseteq t)
  证明: let ⟨_hbt, _hsb, _htb, hli⟩ := Classical.choose_spec (exists_linearIndepOn_extension hs hst)
  hli

Depends on / 依赖: Classical, Classical.choose_spec, _hbt, _hsb, _htb, choose_spec, exists_linearIndepOn_extension
-/
theorem LinearIndepOn.linearIndepOn_extend (hs : LinearIndepOn K v s) (hst : s subseteq t) :
    LinearIndepOn K v (hs.extend hst) :=
  let ⟨_hbt, _hsb, _htb, hli⟩ := Classical.choose_spec (exists_linearIndepOn_extension hs hst)
  hli

-- TODO(Mario): rewrite?
/--
theorem `exists_of_linearIndepOn_of_finite_span` / 定理 `exists_of_linearIndepOn_of_finite_span`

English:
theorem exists_of_linearIndepOn_of_finite_span
  statement: {s : Set V} {t : Finset V}
  proof: by
  classical
  have :
    forall t : Finset V,
      forall s' : Finset V,
        ↑s' subseteq s ->
          s inter ↑t = ∅ ->
            s subseteq (span K ↑(s' union t) : Submodule K V) ->
              exists t' : Finset V, ↑t' subseteq s union ↑t ∧ s subseteq ↑t' ∧ t'.card = (s' union t).card :=
    fun t =>
    Finset.induction_on t
      (fun s' hs' _ hss' =>
have : s = ↑s' := eq_of_linearIndepOn_id_of_span_subtype hs hs' by simpa using hss'
        ⟨s', by simp [this]⟩)
      fun b₁ t hb₁t ih s' hs' hst hss' =>
      have hb₁s : b₁ ∉ s := fun h => by
        have : b₁ in s inter ↑(insert b₁ t) := ⟨h, Finset.mem_insert_self _ _⟩
        rwa [hst] at this
have hb₁s' : b₁ ∉ s' := fun h => hb₁s hs' h
      have hst : s inter ↑t = ∅ :=
eq_empty_of_subset_empty
          -- Porting note: `-subset_inter_iff` required.
          Subset.trans
            (by simp [inter_subset_inter, -subset_inter_iff])
            (le_of_eq hst)
      Classical.by_cases (p := s subseteq (span K ↑(s' union t) : Submodule K V))
        (fun this =>
          let ⟨u, hust, hsu, Eq⟩ := ih _ hs' hst this
          have hb₁u : b₁ ∉ u := fun h => (hust h).elim hb₁s hb₁t
          ⟨insert b₁ u, by simp [insert_subset_insert hust], Subset.trans hsu (by simp), by
            simp [Eq, hb₁t, hb₁s', hb₁u]⟩)
        fun this =>
        let ⟨b₂, hb₂s, hb₂t⟩ := not_subset.mp this
have hb₂t' : b₂ ∉ s' union t := fun h => hb₂t subset_span h
        have : s subseteq (span K ↑(insert b₂ s' union t) : Submodule K V) := fun b₃ hb₃ => by
          have : ↑(s' union insert b₁ t) subseteq insert b₁ (insert b₂ ↑(s' union t) : Set V) := by
            simp only [insert_eq, union_subset_union, Subset.refl,
              subset_union_right, Finset.union_insert, Finset.coe_insert]
          have hb₃ : b₃ in span K (insert b₁ (insert b₂ ↑(s' union t) : Set V)) :=
            span_mono this (hss' hb₃)
          have : s subseteq (span K (insert b₁ ↑(s' union t)) : Submodule K V) := by
            simpa [insert_eq, -singleton_union, -union_singleton] using hss'
          have hb₁ : b₁ in span K (insert b₂ ↑(s' union t)) :=
            mem_span_insert_exchange (this hb₂s) hb₂t
          rw [span_insert_eq_span hb₁] at hb₃; simpa using hb₃
        let ⟨u, hust, hsu, eq⟩ := ih _ (by simp [insert_subset_iff, hb₂s, hs']) hst this
⟨u, Subset.trans hust union_subset_union (Subset.refl _) (by simp [subset_insert]), hsu,
          by simp [eq, hb₂t', hb₁t, hb₁s']⟩
  have eq : ((t.filter fun x => x in s) union t.filter fun x => x ∉ s) = t := by
    ext1 x
    by_cases x in s <;> simp [*]
  apply
    Exists.elim
      (this (t.filter fun x => x ∉ s) (t.filter fun x => x in s) (by simp [Set.subset_def])
        (by simp +contextual [Set.ext_iff]) (by rwa [eq]))
  intro u h
  exact
    ⟨u, Subset.trans h.1 (by simp +contextual [subset_def, or_imp]),
      h.2.1, by simp only [h.2.2, eq]⟩

中文:
定理 存在_of_linearIndepOn_of_finite_span
  结论: {s : 集合 V} {t : 有限集 V}
  证明: by
  classical
  have :
    forall t : Finset V,
      forall s' : Finset V,
        ↑s' subseteq s ->
          s inter ↑t = ∅ ->
            s subseteq (span K ↑(s' union t) : Submodule K V) ->
              exists t' : Finset V, ↑t' subseteq s union ↑t ∧ s subseteq ↑t' ∧ t'.card = (s' union t).card :=
    fun t =>
    Finset.induction_on t
      (fun s' hs' _ hss' =>
have : s = ↑s' := eq_of_linearIndepOn_id_of_span_subtype hs hs' by simpa using hss'
        ⟨s', by simp [this]⟩)
      fun b₁ t hb₁t ih s' hs' hst hss' =>
      have hb₁s : b₁ ∉ s := fun h => by
        have : b₁ in s inter ↑(insert b₁ t) := ⟨h, Finset.mem_insert_self _ _⟩
        rwa [hst] at this
have hb₁s' : b₁ ∉ s' := fun h => hb₁s hs' h
      have hst : s inter ↑t = ∅ :=
eq_empty_of_subset_empty
          -- Porting note: `-subset_inter_iff` required.
          Subset.trans
            (by simp [inter_subset_inter, -subset_inter_iff])
            (le_of_eq hst)
      Classical.by_cases (p := s subseteq (span K ↑(s' union t) : Submodule K V))
        (fun this =>
          let ⟨u, hust, hsu, Eq⟩ := ih _ hs' hst this
          have hb₁u : b₁ ∉ u := fun h => (hust h).elim hb₁s hb₁t
          ⟨insert b₁ u, by simp [insert_subset_insert hust], Subset.trans hsu (by simp), by
            simp [Eq, hb₁t, hb₁s', hb₁u]⟩)
        fun this =>
        let ⟨b₂, hb₂s, hb₂t⟩ := not_subset.mp this
have hb₂t' : b₂ ∉ s' union t := fun h => hb₂t subset_span h
        have : s subseteq (span K ↑(insert b₂ s' union t) : Submodule K V) := fun b₃ hb₃ => by
          have : ↑(s' union insert b₁ t) subseteq insert b₁ (insert b₂ ↑(s' union t) : Set V) := by
            simp only [insert_eq, union_subset_union, Subset.refl,
              subset_union_right, Finset.union_insert, Finset.coe_insert]
          have hb₃ : b₃ in span K (insert b₁ (insert b₂ ↑(s' union t) : Set V)) :=
            span_mono this (hss' hb₃)
          have : s subseteq (span K (insert b₁ ↑(s' union t)) : Submodule K V) := by
            simpa [insert_eq, -singleton_union, -union_singleton] using hss'
          have hb₁ : b₁ in span K (insert b₂ ↑(s' union t)) :=
            mem_span_insert_exchange (this hb₂s) hb₂t
          rw [span_insert_eq_span hb₁] at hb₃; simpa using hb₃
        let ⟨u, hust, hsu, eq⟩ := ih _ (by simp [insert_subset_iff, hb₂s, hs']) hst this
⟨u, Subset.trans hust union_subset_union (Subset.refl _) (by simp [subset_insert]), hsu,
          by simp [eq, hb₂t', hb₁t, hb₁s']⟩
  have eq : ((t.filter fun x => x in s) union t.filter fun x => x ∉ s) = t := by
    ext1 x
    by_cases x in s <;> simp [*]
  apply
    Exists.elim
      (this (t.filter fun x => x ∉ s) (t.filter fun x => x in s) (by simp [Set.subset_def])
        (by simp +contextual [Set.ext_iff]) (by rwa [eq]))
  intro u h
  exact
    ⟨u, Subset.trans h.1 (by simp +contextual [subset_def, or_imp]),
      h.2.1, by simp only [h.2.2, eq]⟩

Depends on / 依赖: Finset, Finset.induction_on, Submodule, classical, eq_of_linearIndepOn_id_of_span_subtype, induction_on, subseteq
-/
theorem exists_of_linearIndepOn_of_finite_span {s : Set V} {t : Finset V}
    (hs : LinearIndepOn K id s) (hst : s subseteq (span K ↑t : Submodule K V)) :
    exists t' : Finset V, ↑t' subseteq s union ↑t ∧ s subseteq ↑t' ∧ t'.card = t.card := by
  classical
  have :
    forall t : Finset V,
      forall s' : Finset V,
        ↑s' subseteq s ->
          s inter ↑t = ∅ ->
            s subseteq (span K ↑(s' union t) : Submodule K V) ->
              exists t' : Finset V, ↑t' subseteq s union ↑t ∧ s subseteq ↑t' ∧ t'.card = (s' union t).card :=
    fun t =>
    Finset.induction_on t
      (fun s' hs' _ hss' =>
have : s = ↑s' := eq_of_linearIndepOn_id_of_span_subtype hs hs' by simpa using hss'
        ⟨s', by simp [this]⟩)
      fun b₁ t hb₁t ih s' hs' hst hss' =>
      have hb₁s : b₁ ∉ s := fun h => by
        have : b₁ in s inter ↑(insert b₁ t) := ⟨h, Finset.mem_insert_self _ _⟩
        rwa [hst] at this
have hb₁s' : b₁ ∉ s' := fun h => hb₁s hs' h
      have hst : s inter ↑t = ∅ :=
eq_empty_of_subset_empty
          -- Porting note: `-subset_inter_iff` required.
          Subset.trans
            (by simp [inter_subset_inter, -subset_inter_iff])
            (le_of_eq hst)
      Classical.by_cases (p := s subseteq (span K ↑(s' union t) : Submodule K V))
        (fun this =>
          let ⟨u, hust, hsu, Eq⟩ := ih _ hs' hst this
          have hb₁u : b₁ ∉ u := fun h => (hust h).elim hb₁s hb₁t
          ⟨insert b₁ u, by simp [insert_subset_insert hust], Subset.trans hsu (by simp), by
            simp [Eq, hb₁t, hb₁s', hb₁u]⟩)
        fun this =>
        let ⟨b₂, hb₂s, hb₂t⟩ := not_subset.mp this
have hb₂t' : b₂ ∉ s' union t := fun h => hb₂t subset_span h
        have : s subseteq (span K ↑(insert b₂ s' union t) : Submodule K V) := fun b₃ hb₃ => by
          have : ↑(s' union insert b₁ t) subseteq insert b₁ (insert b₂ ↑(s' union t) : Set V) := by
            simp only [insert_eq, union_subset_union, Subset.refl,
              subset_union_right, Finset.union_insert, Finset.coe_insert]
          have hb₃ : b₃ in span K (insert b₁ (insert b₂ ↑(s' union t) : Set V)) :=
            span_mono this (hss' hb₃)
          have : s subseteq (span K (insert b₁ ↑(s' union t)) : Submodule K V) := by
            simpa [insert_eq, -singleton_union, -union_singleton] using hss'
          have hb₁ : b₁ in span K (insert b₂ ↑(s' union t)) :=
            mem_span_insert_exchange (this hb₂s) hb₂t
          rw [span_insert_eq_span hb₁] at hb₃; simpa using hb₃
        let ⟨u, hust, hsu, eq⟩ := ih _ (by simp [insert_subset_iff, hb₂s, hs']) hst this
⟨u, Subset.trans hust union_subset_union (Subset.refl _) (by simp [subset_insert]), hsu,
          by simp [eq, hb₂t', hb₁t, hb₁s']⟩
  have eq : ((t.filter fun x => x in s) union t.filter fun x => x ∉ s) = t := by
    ext1 x
    by_cases x in s <;> simp [*]
  apply
    Exists.elim
      (this (t.filter fun x => x ∉ s) (t.filter fun x => x in s) (by simp [Set.subset_def])
        (by simp +contextual [Set.ext_iff]) (by rwa [eq]))
  intro u h
  exact
    ⟨u, Subset.trans h.1 (by simp +contextual [subset_def, or_imp]),
      h.2.1, by simp only [h.2.2, eq]⟩

/--
theorem `exists_finite_card_le_of_finite_of_linearIndependent_of_span` / 定理 `exists_finite_card_le_of_finite_of_linearIndependent_of_span`

English:
theorem exists_finite_card_le_of_finite_of_linearIndependent_of_span
  statement: {s t : Set V} (ht : t.Finite)
  proof: have : s subseteq (span K ↑ht.toFinset : Submodule K V) := by simpa
  let ⟨u, _hust, hsu, Eq⟩ := exists_of_linearIndepOn_of_finite_span hs this
  have : s.Finite := u.finite_toSet.subset hsu
⟨this, by rw [← Eq]; exact Finset.card_le_card Finset.coe_subset.mp by simp [hsu]⟩

中文:
定理 存在_finite_card_le_of_finite_of_linearIndependent_of_span
  结论: {s t : 集合 V} (ht : t.有限)
  证明: have : s subseteq (span K ↑ht.toFinset : Submodule K V) := by simpa
  let ⟨u, _hust, hsu, Eq⟩ := exists_of_linearIndepOn_of_finite_span hs this
  have : s.Finite := u.finite_toSet.subset hsu
⟨this, by rw [← Eq]; exact Finset.card_le_card Finset.coe_subset.mp by simp [hsu]⟩

Depends on / 依赖: Finite, Finset, Finset.card_le_card, Finset.coe_subset.mp, Submodule, _hust, card_le_card, coe_subset, exists_of_linearIndepOn_of_finite_span, finite_toSet, ht.toFinset, s.Finite, subset, subseteq, toFinset, u.finite_toSet.subset
-/
theorem exists_finite_card_le_of_finite_of_linearIndependent_of_span {s t : Set V} (ht : t.Finite)
    (hs : LinearIndepOn K id s) (hst : s subseteq span K t) :
    exists h : s.Finite, h.toFinset.card <= ht.toFinset.card :=
  have : s subseteq (span K ↑ht.toFinset : Submodule K V) := by simpa
  let ⟨u, _hust, hsu, Eq⟩ := exists_of_linearIndepOn_of_finite_span hs this
  have : s.Finite := u.finite_toSet.subset hsu
⟨this, by rw [← Eq]; exact Finset.card_le_card Finset.coe_subset.mp by simp [hsu]⟩

end Module
