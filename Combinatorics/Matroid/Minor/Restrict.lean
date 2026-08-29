/-
Copyright (c) 2023 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
module

public import Mathlib.Combinatorics.Matroid.Dual

/-!
# Matroid Restriction

Given `M : Matroid α` and `R : Set α`, the independent sets of `M` that are contained in `R`
are the independent sets of another matroid `M ↾ R` with ground set `R`,
called the 'restriction' of `M` to `R`.
For `I ⊆ R ⊆ M.E`, `I` is a basis of `R` in `M` if and only if `I` is a base
of the restriction `M ↾ R`, so this construction relates `Matroid.IsBasis` to `Matroid.IsBase`.

If `N M : Matroid α` satisfy `N = M ↾ R` for some `R ⊆ M.E`,
then we call `N` a 'restriction of `M`', and write `N ≤r M`. This is a partial order.

This file proves that the restriction is a matroid and that the `≤r` order is a partial order,
and gives related API.
It also proves some `Matroid.IsBasis` analogues of `Matroid.IsBase` lemmas that,
while they could be stated in `Data.Matroid.Basic`,
are hard to prove without `Matroid.restrict` API.

## Main Definitions

* `M.restrict R`, written `M ↾ R`, is the restriction of `M : Matroid α` to `R : Set α`: i.e.
  the matroid with ground set `R` whose independent sets are the `M`-independent subsets of `R`.

* `Matroid.Restriction N M`, written `N ≤r M`, means that `N = M ↾ R` for some `R ⊆ M.E`.

* `Matroid.IsStrictRestriction N M`, written `N <r M`, means that `N = M ↾ R` for some `R ⊂ M.E`.

* `Matroidᵣ α` is a type synonym for `Matroid α`, equipped with the `PartialOrder` `≤r`.

## Implementation Notes

Since `R` and `M.E` are both terms in `Set α`, to define the restriction `M ↾ R`,
we need to either insist that `R ⊆ M.E`, or to say what happens when `R` contains the junk
outside `M.E`.

It turns out that `R ⊆ M.E` is just an unnecessary hypothesis; if we say the restriction
`M ↾ R` has ground set `R` and its independent sets are the `M`-independent subsets of `R`,
we always get a matroid, in which the elements of `R \ M.E` aren't in any independent sets.
We could instead define this matroid to always be 'smaller' than `M` by setting
`(M ↾ R).E := R ∩ M.E`, but this is worse definitionally, and more generally less convenient.

This makes it possible to actually restrict a matroid 'upwards'; for instance, if `M : Matroid α`
satisfies `M.E = ∅`, then `M ↾ Set.univ` is the matroid on `α` whose ground set is all of `α`,
where the empty set is the only independent set.
(In general, elements of `R \ M.E` are all 'loops' of the matroid `M ↾ R`;
see `Matroid.loops` and `Matroid.restrict_loops_eq'` for a precise version of this statement.)
This is mathematically strange, but is useful for API building.

The cost of allowing a restriction of `M` to be 'bigger' than `M` itself is that
the statement `M ↾ R ≤r M` is only true with the hypothesis `R ⊆ M.E`
(at least, if we want `≤r` to be a partial order).
But this isn't too inconvenient in practice. Indeed `(· ⊆ M.E)` proofs
can often be automatically provided by `aesop_mat`.

We define the restriction order `≤r` to give a `PartialOrder` instance on the type synonym
`Matroidᵣ α` rather than `Matroid α` itself, because the `PartialOrder (Matroid α)` instance is
reserved for the more mathematically important 'minor' order; see `Matroid.IsMinor`.
-/

@[expose] public section

assert_not_exists Field

open Set

namespace Matroid

variable {α : Type*} {M : Matroid α} {R I X Y : Set α}

section restrict

/--
Definition of `restrictIndepMatroid` / `restrictIndepMatroid` 的定义

English:
definition restrictIndepMatroid
  signature: (M : Matroid α) (R : Set α)
  body: R
  Indep I := M.Indep I ∧ I subseteq R
  indep_empty := ⟨M.empty_indep, empty_subset _⟩
  indep_subset := fun _ _ h hIJ => ⟨h.1.subset hIJ, hIJ.trans h.2⟩
  indep_aug := by
    rintro I I' ⟨hI, hIY⟩ (hIn : ¬ M.IsBasis' I R) (hI' : M.IsBasis' I' R)
    rw [isBasis'_iff_isBasis_inter_ground] at hIn h

中文:
定义 restrictIndepMatroid
  签名: (M : 拟阵 α) (R : 集合 α)
  定义体: R
  Indep I := M.Indep I ∧ I subseteq R
  indep_empty := ⟨M.empty_indep, empty_subset _⟩
  indep_subset := fun _ _ h hIJ => ⟨h.1.subset hIJ, hIJ.trans h.2⟩
  indep_aug := by
    rintro I I' ⟨hI, hIY⟩ (hIn : ¬ M.IsBasis' I R) (hI' : M.IsBasis' I' R)
    rw [isBasis'_iff_isBasis_inter_ground] at hIn h
-/
@[simps] def restrictIndepMatroid (M : Matroid α) (R : Set α) : IndepMatroid α where
  E := R
  Indep I := M.Indep I ∧ I subseteq R
  indep_empty := ⟨M.empty_indep, empty_subset _⟩
  indep_subset := fun _ _ h hIJ => ⟨h.1.subset hIJ, hIJ.trans h.2⟩
  indep_aug := by
    rintro I I' ⟨hI, hIY⟩ (hIn : ¬ M.IsBasis' I R) (hI' : M.IsBasis' I' R)
    rw [isBasis'_iff_isBasis_inter_ground] at hIn hI'
    obtain ⟨B', hB', rfl⟩ := hI'.exists_isBase
    obtain ⟨B, hB, hIB, hBIB'⟩ := hI.exists_isBase_subset_union_isBase hB'
    rw [hB'.inter_isBasis_iff_compl_inter_isBasis_dual]; rw [sdiff_inter_sdiff] at hI'
    have hss : M.E \ (B' union (R inter M.E)) subseteq M.E \ (B union (R inter M.E)) := by
      apply sdiff_subset_sdiff_right
      rw [union_subset_iff]; rw [and_iff_left subset_union_right]; rw [union_comm]
      exact hBIB'.trans (union_subset_union_left _ (subset_inter hIY hI.subset_ground))
    have hi : M✶.Indep (M.E \ (B union (R inter M.E))) := by
      rw [dual_indep_iff_exists]
      exact ⟨B, hB, disjoint_of_subset_right subset_union_left disjoint_sdiff_left⟩
    have h_eq := hI'.eq_of_subset_indep hi hss
      (sdiff_subset_sdiff_right subset_union_right)
    rw [h_eq]; rw [← sdiff_inter_sdiff]; rw [← hB.inter_isBasis_iff_compl_inter_isBasis_dual] at hI'
    obtain ⟨J, hJ, hIJ⟩ := hI.subset_isBasis_of_subset
      (subset_inter hIB (subset_inter hIY hI.subset_ground))
    obtain rfl := hI'.indep.eq_of_isBasis hJ
    have hIJ' : I ⊂ B inter (R inter M.E) := hIJ.ssubset_of_ne (fun he => hIn (by rwa [he]))
    obtain ⟨e, he⟩ := exists_of_ssubset hIJ'
    exact ⟨e, ⟨⟨(hBIB' he.1.1).elim (fun h => (he.2 h).elim) id,he.1.2⟩, he.2⟩,
      hI'.indep.subset (insert_subset he.1 hIJ), insert_subset he.1.2.1 hIY⟩
  indep_maximal := by
    rintro A hAR I ⟨hI, _⟩ hIA
    obtain ⟨J, hJ, hIJ⟩ := hI.subset_isBasis'_of_subset hIA
    use J
    simp only [hIJ, and_assoc, maximal_subset_iff, hJ.indep, hJ.subset, and_imp, true_and,
      hJ.subset.trans hAR]
    exact fun K hK _ hKA hJK => hJ.eq_of_subset_indep hK hJK hKA
  subset_ground _ := And.right

/--
Definition of `restrict` / `restrict` 的定义

English:
definition restrict
  signature: (M : Matroid α) (R : Set α)
  body: (M.restrictIndepMatroid R).matroid

中文:
定义 restrict
  签名: (M : 拟阵 α) (R : 集合 α)
  定义体: (M.restrictIndepMatroid R).matroid

Depends on / 依赖: M.restrictIndepMatroid, matroid, restrictIndepMatroid
-/
def restrict (M : Matroid α) (R : Set α) : Matroid α := (M.restrictIndepMatroid R).matroid

/-- `M ↾ R` means `M.restrict R`. -/
scoped infixl:65 " ↾ " => Matroid.restrict

/--
theorem `restrict_indep_iff` / 定理 `restrict_indep_iff`

English:
theorem restrict_indep_iff
  statement: (M ↾ R).Indep I ↔ M.Indep I ∧ I subseteq R
  proof: Iff.rfl

中文:
定理 restrict_indep_iff
  结论: (M ↾ R).Indep I ↔ M.Indep I ∧ I subseteq R
  证明: Iff.rfl
-/
@[simp] theorem restrict_indep_iff : (M ↾ R).Indep I ↔ M.Indep I ∧ I subseteq R := Iff.rfl

/--
theorem `Indep.indep_restrict_of_subset` / 定理 `Indep.indep_restrict_of_subset`

English:
theorem Indep.indep_restrict_of_subset
  given: (h : M.Indep I) (hIR : I subseteq R)
  statement: (M ↾ R).Indep I
  proof: restrict_indep_iff.mpr ⟨h,hIR⟩

中文:
定理 Indep.indep_restrict_of_subset
  条件: (h : M.Indep I) (hIR : I subseteq R)
  结论: (M ↾ R).Indep I
  证明: restrict_indep_iff.mpr ⟨h,hIR⟩

Depends on / 依赖: restrict_indep_iff, restrict_indep_iff.mpr
-/
theorem Indep.indep_restrict_of_subset (h : M.Indep I) (hIR : I subseteq R) : (M ↾ R).Indep I :=
  restrict_indep_iff.mpr ⟨h,hIR⟩

/--
theorem `Indep.of_restrict` / 定理 `Indep.of_restrict`

English:
theorem Indep.of_restrict
  given: (hI : (M ↾ R).Indep I)
  statement: M.Indep I
  proof: (restrict_indep_iff.1 hI).1

中文:
定理 Indep.of_restrict
  条件: (hI : (M ↾ R).Indep I)
  结论: M.Indep I
  证明: (restrict_indep_iff.1 hI).1

Depends on / 依赖: restrict_indep_iff
-/
theorem Indep.of_restrict (hI : (M ↾ R).Indep I) : M.Indep I :=
  (restrict_indep_iff.1 hI).1

/--
theorem `restrict_ground_eq` / 定理 `restrict_ground_eq`

English:
theorem restrict_ground_eq
  statement: (M ↾ R).E = R
  proof: rfl

中文:
定理 restrict_ground_eq
  结论: (M ↾ R).E = R
  证明: rfl
-/
@[simp] theorem restrict_ground_eq : (M ↾ R).E = R := rfl

/--
theorem `restrict_finite` / 定理 `restrict_finite`

English:
theorem restrict_finite
  given: {R : Set α} (hR : R.Finite)
  statement: (M ↾ R).Finite
  proof: ⟨hR⟩

中文:
定理 restrict_finite
  条件: {R : 集合 α} (hR : R.有限)
  结论: (M ↾ R).有限
  证明: ⟨hR⟩
-/
theorem restrict_finite {R : Set α} (hR : R.Finite) : (M ↾ R).Finite :=
  ⟨hR⟩

/--
theorem `restrict_dep_iff` / 定理 `restrict_dep_iff`

English:
theorem restrict_dep_iff
  statement: (M ↾ R).Dep X ↔ ¬ M.Indep X ∧ X subseteq R
  proof: by
  rw [Dep]; rw [restrict_indep_iff]; rw [restrict_ground_eq]; tauto

中文:
定理 restrict_dep_iff
  结论: (M ↾ R).Dep X ↔ ¬ M.Indep X ∧ X subseteq R
  证明: by
  rw [Dep]; rw [restrict_indep_iff]; rw [restrict_ground_eq]; tauto
-/
@[simp] theorem restrict_dep_iff : (M ↾ R).Dep X ↔ ¬ M.Indep X ∧ X subseteq R := by
  rw [Dep]; rw [restrict_indep_iff]; rw [restrict_ground_eq]; tauto

/--
theorem `restrict_ground_eq_self` / 定理 `restrict_ground_eq_self`

English:
theorem restrict_ground_eq_self
  given: (M : Matroid α)
  statement: (M ↾ M.E) = M
  proof: by
  refine ext_indep rfl ?_; simp_all

中文:
定理 restrict_ground_eq_self
  条件: (M : 拟阵 α)
  结论: (M ↾ M.E) = M
  证明: by
  refine ext_indep rfl ?_; simp_all
-/
@[simp] theorem restrict_ground_eq_self (M : Matroid α) : (M ↾ M.E) = M := by
  refine ext_indep rfl ?_; simp_all

/--
theorem `restrict_restrict_eq` / 定理 `restrict_restrict_eq`

English:
theorem restrict_restrict_eq
  given: {R₁ R₂ : Set α} (M : Matroid α) (hR : R₂ subseteq R₁)
  proof: by
  refine ext_indep rfl ?_
  simp only [restrict_ground_eq, restrict_indep_iff, and_congr_left_iff, and_iff_left_iff_imp]
  exact fun _ h _ _ => h.trans hR

中文:
定理 restrict_restrict_eq
  条件: {R₁ R₂ : 集合 α} (M : 拟阵 α) (hR : R₂ subseteq R₁)
  证明: by
  refine ext_indep rfl ?_
  simp only [restrict_ground_eq, restrict_indep_iff, and_congr_left_iff, and_iff_left_iff_imp]
  exact fun _ h _ _ => h.trans hR

Depends on / 依赖: and_congr_left_iff, and_iff_left_iff_imp, ext_indep, h.trans, restrict_ground_eq, restrict_indep_iff
-/
theorem restrict_restrict_eq {R₁ R₂ : Set α} (M : Matroid α) (hR : R₂ subseteq R₁) :
    (M ↾ R₁) ↾ R₂ = M ↾ R₂ := by
  refine ext_indep rfl ?_
  simp only [restrict_ground_eq, restrict_indep_iff, and_congr_left_iff, and_iff_left_iff_imp]
  exact fun _ h _ _ => h.trans hR

/--
theorem `restrict_idem` / 定理 `restrict_idem`

English:
theorem restrict_idem
  given: (M : Matroid α) (R : Set α)
  statement: M ↾ R ↾ R = M ↾ R
  proof: by
  rw [M.restrict_restrict_eq Subset.rfl]

中文:
定理 restrict_idem
  条件: (M : 拟阵 α) (R : 集合 α)
  结论: M ↾ R ↾ R = M ↾ R
  证明: by
  rw [M.restrict_restrict_eq Subset.rfl]
-/
@[simp] theorem restrict_idem (M : Matroid α) (R : Set α) : M ↾ R ↾ R = M ↾ R := by
  rw [M.restrict_restrict_eq Subset.rfl]

/--
theorem `isBase_restrict_iff` / 定理 `isBase_restrict_iff`

English:
theorem isBase_restrict_iff
  given: (hX : X subseteq M.E := by aesop_mat)
  proof: by
  simp_rw [isBase_iff_maximal_indep, IsBasis, and_iff_left hX, maximal_iff, restrict_indep_iff]

中文:
定理 isBase_restrict_iff
  条件: (hX : X subseteq M.E := by aesop_mat)
  证明: by
  simp_rw [isBase_iff_maximal_indep, IsBasis, and_iff_left hX, maximal_iff, restrict_indep_iff]
-/
@[simp] theorem isBase_restrict_iff (hX : X subseteq M.E := by aesop_mat) :
    (M ↾ X).IsBase I ↔ M.IsBasis I X := by
  simp_rw [isBase_iff_maximal_indep, IsBasis, and_iff_left hX, maximal_iff, restrict_indep_iff]

/--
theorem `isBase_restrict_iff'` / 定理 `isBase_restrict_iff'`

English:
theorem isBase_restrict_iff'
  statement: (M ↾ X).IsBase I ↔ M.IsBasis' I X
  proof: by
  simp_rw [isBase_iff_maximal_indep, IsBasis', maximal_iff, restrict_indep_iff]

中文:
定理 isBase_restrict_iff'
  结论: (M ↾ X).IsBase I ↔ M.是基' I X
  证明: by
  simp_rw [isBase_iff_maximal_indep, IsBasis', maximal_iff, restrict_indep_iff]

Depends on / 依赖: IsBasis, isBase_iff_maximal_indep, maximal_iff, restrict_indep_iff, simp_rw
-/
theorem isBase_restrict_iff' : (M ↾ X).IsBase I ↔ M.IsBasis' I X := by
  simp_rw [isBase_iff_maximal_indep, IsBasis', maximal_iff, restrict_indep_iff]

/--
theorem `IsBasis'.isBase_restrict` / 定理 `IsBasis'.isBase_restrict`

English:
theorem IsBasis'.isBase_restrict
  given: (hI : M.IsBasis' I X)
  statement: (M ↾ X).IsBase I
  proof: isBase_restrict_iff'.1 hI

中文:
定理 是基'.isBase_restrict
  条件: (hI : M.是基' I X)
  结论: (M ↾ X).IsBase I
  证明: isBase_restrict_iff'.1 hI

Depends on / 依赖: F.toRealizer, toRealizer
-/
theorem IsBasis'.isBase_restrict (hI : M.IsBasis' I X) : (M ↾ X).IsBase I :=
  isBase_restrict_iff'.1 hI

/--
theorem `IsBasis.restrict_isBase` / 定理 `IsBasis.restrict_isBase`

English:
theorem IsBasis.restrict_isBase
  given: (h : M.IsBasis I X)
  statement: (M ↾ X).IsBase I
  proof: (isBase_restrict_iff h.subset_ground).2 h

中文:
定理 是基.restrict_isBase
  条件: (h : M.是基 I X)
  结论: (M ↾ X).IsBase I
  证明: (isBase_restrict_iff h.subset_ground).2 h

Depends on / 依赖: h.subset_ground, isBase_restrict_iff, subset_ground
-/
theorem IsBasis.restrict_isBase (h : M.IsBasis I X) : (M ↾ X).IsBase I :=
  (isBase_restrict_iff h.subset_ground).2 h

/--
Instance `restrict_rankFinite` / 实例 `restrict_rankFinite`

English:
instance restrict_rankFinite
  signature: [M.RankFinite] (R : Set α)
  body: let ⟨_, hB⟩ := (M ↾ R).exists_isBase
  hB.rankFinite_of_finite (hB.indep.of_restrict.finite)

中文:
实例 restrict_rankFinite
  签名: [M.RankFinite] (R : 集合 α)
  定义体: let ⟨_, hB⟩ := (M ↾ R).exists_isBase
  hB.rankFinite_of_finite (hB.indep.of_restrict.finite)

Depends on / 依赖: exists_isBase, finite, hB.indep.of_restrict.finite, hB.rankFinite_of_finite, of_restrict, rankFinite_of_finite
-/
instance restrict_rankFinite [M.RankFinite] (R : Set α) : (M ↾ R).RankFinite :=
  let ⟨_, hB⟩ := (M ↾ R).exists_isBase
  hB.rankFinite_of_finite (hB.indep.of_restrict.finite)

/--
Instance `restrict_finitary` / 实例 `restrict_finitary`

English:
instance restrict_finitary
  signature: [Finitary M] (R : Set α)
  body: by
  refine ⟨fun I hI => ?_⟩
  simp only [restrict_indep_iff] at *
  rw [indep_iff_forall_finite_subset_indep]
  exact ⟨fun J hJ hJfin => (hI J hJ hJfin).1,
    fun e heI => singleton_subset_iff.1 (hI _ (by simpa) (toFinite _)).2⟩

中文:
实例 restrict_finitary
  签名: [Finitary M] (R : 集合 α)
  定义体: by
  refine ⟨fun I hI => ?_⟩
  simp only [restrict_indep_iff] at *
  rw [indep_iff_forall_finite_subset_indep]
  exact ⟨fun J hJ hJfin => (hI J hJ hJfin).1,
    fun e heI => singleton_subset_iff.1 (hI _ (by simpa) (toFinite _)).2⟩

Depends on / 依赖: indep_iff_forall_finite_subset_indep, restrict_indep_iff, singleton_subset_iff, toFinite
-/
instance restrict_finitary [Finitary M] (R : Set α) : Finitary (M ↾ R) := by
  refine ⟨fun I hI => ?_⟩
  simp only [restrict_indep_iff] at *
  rw [indep_iff_forall_finite_subset_indep]
  exact ⟨fun J hJ hJfin => (hI J hJ hJfin).1,
    fun e heI => singleton_subset_iff.1 (hI _ (by simpa) (toFinite _)).2⟩

/--
theorem `IsBasis.isBase_restrict` / 定理 `IsBasis.isBase_restrict`

English:
theorem IsBasis.isBase_restrict
  given: (h : M.IsBasis I X)
  statement: (M ↾ X).IsBase I
  proof: (isBase_restrict_iff h.subset_ground).mpr h

中文:
定理 是基.isBase_restrict
  条件: (h : M.是基 I X)
  结论: (M ↾ X).IsBase I
  证明: (isBase_restrict_iff h.subset_ground).mpr h
-/
@[simp] theorem IsBasis.isBase_restrict (h : M.IsBasis I X) : (M ↾ X).IsBase I :=
  (isBase_restrict_iff h.subset_ground).mpr h

/--
theorem `IsBasis.isBasis_restrict_of_subset` / 定理 `IsBasis.isBasis_restrict_of_subset`

English:
theorem IsBasis.isBasis_restrict_of_subset
  given: (hI : M.IsBasis I X) (hXY : X subseteq Y)
  proof: by
  rwa [← isBase_restrict_iff, M.restrict_restrict_eq hXY, isBase_restrict_iff]

中文:
定理 是基.isBasis_restrict_of_subset
  条件: (hI : M.是基 I X) (hXY : X subseteq Y)
  证明: by
  rwa [← isBase_restrict_iff, M.restrict_restrict_eq hXY, isBase_restrict_iff]

Depends on / 依赖: M.restrict_restrict_eq, isBase_restrict_iff, restrict_restrict_eq
-/
theorem IsBasis.isBasis_restrict_of_subset (hI : M.IsBasis I X) (hXY : X subseteq Y) :
    (M ↾ Y).IsBasis I X := by
  rwa [← isBase_restrict_iff, M.restrict_restrict_eq hXY, isBase_restrict_iff]

/--
theorem `isBasis'_restrict_iff` / 定理 `isBasis'_restrict_iff`

English:
theorem isBasis'_restrict_iff
  statement: (M ↾ R).IsBasis' I X ↔ M.IsBasis' I (X inter R) ∧ I subseteq R
  proof: by
  simp_rw [IsBasis', maximal_iff, restrict_indep_iff, subset_inter_iff, and_imp]
  tauto

中文:
定理 isBasis'_restrict_iff
  结论: (M ↾ R).是基' I X ↔ M.是基' I (X inter R) ∧ I subseteq R
  证明: by
  simp_rw [IsBasis', maximal_iff, restrict_indep_iff, subset_inter_iff, and_imp]
  tauto
-/
theorem isBasis'_restrict_iff : (M ↾ R).IsBasis' I X ↔ M.IsBasis' I (X inter R) ∧ I subseteq R := by
  simp_rw [IsBasis', maximal_iff, restrict_indep_iff, subset_inter_iff, and_imp]
  tauto

/--
theorem `isBasis_restrict_iff'` / 定理 `isBasis_restrict_iff'`

English:
theorem isBasis_restrict_iff'
  statement: (M ↾ R).IsBasis I X ↔ M.IsBasis I (X inter M.E) ∧ X subseteq R
  proof: by
  rw [isBasis_iff_isBasis'_subset_ground]; rw [isBasis'_restrict_iff]; rw [restrict_ground_eq]; rw [and_congr_left_iff]; rw [← isBasis'_iff_isBasis_inter_ground]
  intro hXR
  rw [inter_eq_self_of_subset_left hXR]; rw [and_iff_left_iff_imp]
  exact fun h => h.subset.trans hXR

中文:
定理 isBasis_restrict_iff'
  结论: (M ↾ R).是基 I X ↔ M.是基 I (X inter M.E) ∧ X subseteq R
  证明: by
  rw [isBasis_iff_isBasis'_subset_ground]; rw [isBasis'_restrict_iff]; rw [restrict_ground_eq]; rw [and_congr_left_iff]; rw [← isBasis'_iff_isBasis_inter_ground]
  intro hXR
  rw [inter_eq_self_of_subset_left hXR]; rw [and_iff_left_iff_imp]
  exact fun h => h.subset.trans hXR

Depends on / 依赖: _iff_isBasis_inter_ground, _restrict_iff, _subset_ground, and_congr_left_iff, and_iff_left_iff_imp, h.subset.trans, inter_eq_self_of_subset_left, isBasis, isBasis_iff_isBasis, restrict_ground_eq, subset
-/
theorem isBasis_restrict_iff' : (M ↾ R).IsBasis I X ↔ M.IsBasis I (X inter M.E) ∧ X subseteq R := by
  rw [isBasis_iff_isBasis'_subset_ground]; rw [isBasis'_restrict_iff]; rw [restrict_ground_eq]; rw [and_congr_left_iff]; rw [← isBasis'_iff_isBasis_inter_ground]
  intro hXR
  rw [inter_eq_self_of_subset_left hXR]; rw [and_iff_left_iff_imp]
  exact fun h => h.subset.trans hXR

/--
theorem `isBasis_restrict_iff` / 定理 `isBasis_restrict_iff`

English:
theorem isBasis_restrict_iff
  given: (hR : R subseteq M.E := by aesop_mat)
  proof: by
  rw [isBasis_restrict_iff']; rw [and_congr_left_iff]
  intro hXR
  rw [← isBasis'_iff_isBasis_inter_ground]; rw [isBasis'_iff_isBasis]

中文:
定理 isBasis_restrict_iff
  条件: (hR : R subseteq M.E := by aesop_mat)
  证明: by
  rw [isBasis_restrict_iff']; rw [and_congr_left_iff]
  intro hXR
  rw [← isBasis'_iff_isBasis_inter_ground]; rw [isBasis'_iff_isBasis]

Depends on / 依赖: IsBasis, M.IsBasis, _iff_isBasis, _iff_isBasis_inter_ground, aesop_mat, and_congr_left_iff, isBasis, isBasis_restrict_iff, subseteq
-/
theorem isBasis_restrict_iff (hR : R subseteq M.E := by aesop_mat) :
    (M ↾ R).IsBasis I X ↔ M.IsBasis I X ∧ X subseteq R := by
  rw [isBasis_restrict_iff']; rw [and_congr_left_iff]
  intro hXR
  rw [← isBasis'_iff_isBasis_inter_ground]; rw [isBasis'_iff_isBasis]

/--
lemma `isBasis'_iff_isBasis_restrict_univ` / 引理 `isBasis'_iff_isBasis_restrict_univ`

English:
lemma isBasis'_iff_isBasis_restrict_univ
  statement: M.IsBasis' I X ↔ (M ↾ univ).IsBasis I X
  proof: by
  rw [isBasis_restrict_iff']; rw [isBasis'_iff_isBasis_inter_ground]; rw [and_iff_left (subset_univ _)]

中文:
引理 isBasis'_iff_isBasis_restrict_univ
  结论: M.是基' I X ↔ (M ↾ univ).是基 I X
  证明: by
  rw [isBasis_restrict_iff']; rw [isBasis'_iff_isBasis_inter_ground]; rw [and_iff_left (subset_univ _)]
-/
lemma isBasis'_iff_isBasis_restrict_univ : M.IsBasis' I X ↔ (M ↾ univ).IsBasis I X := by
  rw [isBasis_restrict_iff']; rw [isBasis'_iff_isBasis_inter_ground]; rw [and_iff_left (subset_univ _)]

/--
theorem `restrict_eq_restrict_iff` / 定理 `restrict_eq_restrict_iff`

English:
theorem restrict_eq_restrict_iff
  given: (M M' : Matroid α) (X : Set α)
  proof: by
  refine ⟨fun h I hIX => ?_, fun h => ext_indep rfl fun I (hI : I subseteq X) => ?_⟩
  · rw [← and_iff_left (a := (M.Indep I)) hIX, ← and_iff_left (a := (M'.Indep I)) hIX,
      ← restrict_indep_iff, h, restrict_indep_iff]
  rw [restrict_indep_iff]; rw [and_iff_left hI]; rw [restrict_indep_iff]; 

中文:
定理 restrict_eq_restrict_iff
  条件: (M M' : 拟阵 α) (X : 集合 α)
  证明: by
  refine ⟨fun h I hIX => ?_, fun h => ext_indep rfl fun I (hI : I subseteq X) => ?_⟩
  · rw [← and_iff_left (a := (M.Indep I)) hIX, ← and_iff_left (a := (M'.Indep I)) hIX,
      ← restrict_indep_iff, h, restrict_indep_iff]
  rw [restrict_indep_iff]; rw [and_iff_left hI]; rw [restrict_indep_iff]; 

Depends on / 依赖: M.Indep, and_iff_left, ext_indep, restrict_indep_iff, subseteq
-/
theorem restrict_eq_restrict_iff (M M' : Matroid α) (X : Set α) :
    M ↾ X = M' ↾ X ↔ forall I, I subseteq X -> (M.Indep I ↔ M'.Indep I) := by
  refine ⟨fun h I hIX => ?_, fun h => ext_indep rfl fun I (hI : I subseteq X) => ?_⟩
  · rw [← and_iff_left (a := (M.Indep I)) hIX, ← and_iff_left (a := (M'.Indep I)) hIX,
      ← restrict_indep_iff, h, restrict_indep_iff]
  rw [restrict_indep_iff]; rw [and_iff_left hI]; rw [restrict_indep_iff]; rw [and_iff_left hI]; rw [h _ hI]

/--
theorem `restrict_eq_self_iff` / 定理 `restrict_eq_self_iff`

English:
theorem restrict_eq_self_iff
  statement: M ↾ R = M ↔ R = M.E
  proof: ⟨fun h => by rw [← h]; rfl, fun h => by simp [h]⟩

中文:
定理 restrict_eq_self_iff
  结论: M ↾ R = M ↔ R = M.E
  证明: ⟨fun h => by rw [← h]; rfl, fun h => by simp [h]⟩
-/
@[simp] theorem restrict_eq_self_iff : M ↾ R = M ↔ R = M.E :=
  ⟨fun h => by rw [← h]; rfl, fun h => by simp [h]⟩

end restrict

section IsRestriction

variable {N : Matroid α}

/--
Definition of `IsRestriction` / `IsRestriction` 的定义

English:
definition IsRestriction
  signature: (N M : Matroid α)
  body: exists R subseteq M.E, N = M ↾ R

中文:
定义 IsRestriction
  签名: (N M : 拟阵 α)
  定义体: exists R subseteq M.E, N = M ↾ R

Depends on / 依赖: subseteq
-/
def IsRestriction (N M : Matroid α) : Prop := exists R subseteq M.E, N = M ↾ R

/--
Definition of `IsStrictRestriction` / `IsStrictRestriction` 的定义

English:
definition IsStrictRestriction
  signature: (N M : Matroid α)
  body: IsRestriction N M ∧ ¬ IsRestriction M N

中文:
定义 IsStrictRestriction
  签名: (N M : 拟阵 α)
  定义体: IsRestriction N M ∧ ¬ IsRestriction M N

Depends on / 依赖: IsRestriction
-/
def IsStrictRestriction (N M : Matroid α) : Prop := IsRestriction N M ∧ ¬ IsRestriction M N

/-- `N ≤r M` means that `N` is a `Restriction` of `M`. -/
scoped infix:50 " <=r " => IsRestriction

/-- `N <r M` means that `N` is a `IsStrictRestriction` of `M`. -/
scoped infix:50 " <r " => IsStrictRestriction

/--
Definition of `Matroidᵣ` / `Matroidᵣ` 的定义

English:
structure Matroidᵣ
  parameters: (α : Type*)
  (no additional axioms)

中文:
结构 Matroidᵣ
  参数: (α : 类型)
  (无附加公理)
-/
@[ext] structure Matroidᵣ (α : Type*) where ofMatroid ::
  /-- The underlying `Matroid` -/
  toMatroid : Matroid α

instance {α : Type*} : CoeOut (Matroidᵣ α) (Matroid α) where
  coe := Matroidᵣ.toMatroid

/--
theorem `Matroidᵣ.coe_inj` / 定理 `Matroidᵣ.coe_inj`

English:
theorem Matroidᵣ.coe_inj
  given: {M₁ M₂ : Matroidᵣ α}
  proof: Matroidᵣ.ext_iff.symm

中文:
定理 Matroidᵣ.coe_inj
  条件: {M₁ M₂ : Matroidᵣ α}
  证明: Matroidᵣ.ext_iff.symm
-/
@[simp] theorem Matroidᵣ.coe_inj {M₁ M₂ : Matroidᵣ α} :
    (M₁ : Matroid α) = (M₂ : Matroid α) ↔ M₁ = M₂ := Matroidᵣ.ext_iff.symm

instance {α : Type*} : PartialOrder (Matroidᵣ α) where
  le := (· <=r ·)
  le_refl M := ⟨(M : Matroid α).E, Subset.rfl, (M : Matroid α).restrict_ground_eq_self.symm⟩
  le_trans M₁ M₂ M₃ := by
    rintro ⟨R, hR, h₁⟩ ⟨R', hR', h₂⟩
    rw [h₂] at h₁ hR
    rw [h₁]; rw [restrict_restrict_eq _ (show R subseteq R' from hR)]
    exact ⟨R, hR.trans hR', rfl⟩
  le_antisymm M₁ M₂ := by
    rintro ⟨R, hR, h⟩ ⟨R', hR', h'⟩
    rw [h']; rw [restrict_ground_eq] at hR
    rw [h]; rw [restrict_ground_eq] at hR'
    rw [← Matroidᵣ.coe_inj]; rw [h]; rw [h']; rw [hR.antisymm hR']; rw [restrict_idem]

/--
theorem `Matroidᵣ.le_iff` / 定理 `Matroidᵣ.le_iff`

English:
theorem Matroidᵣ.le_iff
  given: {M M' : Matroidᵣ α}
  proof: Iff.rfl

中文:
定理 Matroidᵣ.le_iff
  条件: {M M' : Matroidᵣ α}
  证明: Iff.rfl
-/
@[simp] protected theorem Matroidᵣ.le_iff {M M' : Matroidᵣ α} :
    M <= M' ↔ (M : Matroid α) <=r (M' : Matroid α) := Iff.rfl

/--
theorem `Matroidᵣ.lt_iff` / 定理 `Matroidᵣ.lt_iff`

English:
theorem Matroidᵣ.lt_iff
  given: {M M' : Matroidᵣ α}
  proof: Iff.rfl

中文:
定理 Matroidᵣ.lt_iff
  条件: {M M' : Matroidᵣ α}
  证明: Iff.rfl
-/
@[simp] protected theorem Matroidᵣ.lt_iff {M M' : Matroidᵣ α} :
    M < M' ↔ (M : Matroid α) <r (M' : Matroid α) := Iff.rfl

/--
theorem `ofMatroid_le_iff` / 定理 `ofMatroid_le_iff`

English:
theorem ofMatroid_le_iff
  given: {M M' : Matroid α}
  proof: by
  simp

中文:
定理 ofMatroid_le_iff
  条件: {M M' : 拟阵 α}
  证明: by
  simp
-/
theorem ofMatroid_le_iff {M M' : Matroid α} :
    Matroidᵣ.ofMatroid M <= Matroidᵣ.ofMatroid M' ↔ M <=r M' := by
  simp

/--
theorem `ofMatroid_lt_iff` / 定理 `ofMatroid_lt_iff`

English:
theorem ofMatroid_lt_iff
  given: {M M' : Matroid α}
  proof: by
  simp

中文:
定理 ofMatroid_lt_iff
  条件: {M M' : 拟阵 α}
  证明: by
  simp
-/
theorem ofMatroid_lt_iff {M M' : Matroid α} :
    Matroidᵣ.ofMatroid M < Matroidᵣ.ofMatroid M' ↔ M <r M' := by
  simp

/--
theorem `IsRestriction.refl` / 定理 `IsRestriction.refl`

English:
theorem IsRestriction.refl
  statement: M <=r M
  proof: le_refl (Matroidᵣ.ofMatroid M)

中文:
定理 IsRestriction.refl
  结论: M <=r M
  证明: le_refl (Matroidᵣ.ofMatroid M)

Depends on / 依赖: le_refl, ofMatroid
-/
theorem IsRestriction.refl : M <=r M :=
  le_refl (Matroidᵣ.ofMatroid M)

/--
theorem `IsRestriction.antisymm` / 定理 `IsRestriction.antisymm`

English:
theorem IsRestriction.antisymm
  given: {M' : Matroid α} (h : M <=r M') (h' : M' <=r M)
  statement: M = M'
  proof: by
  simpa using (ofMatroid_le_iff.2 h).antisymm (ofMatroid_le_iff.2 h')

中文:
定理 IsRestriction.antisymm
  条件: {M' : 拟阵 α} (h : M <=r M') (h' : M' <=r M)
  结论: M = M'
  证明: by
  simpa using (ofMatroid_le_iff.2 h).antisymm (ofMatroid_le_iff.2 h')

Depends on / 依赖: antisymm, ofMatroid_le_iff
-/
theorem IsRestriction.antisymm {M' : Matroid α} (h : M <=r M') (h' : M' <=r M) : M = M' := by
  simpa using (ofMatroid_le_iff.2 h).antisymm (ofMatroid_le_iff.2 h')

/--
theorem `IsRestriction.trans` / 定理 `IsRestriction.trans`

English:
theorem IsRestriction.trans
  given: {M₁ M₂ M₃ : Matroid α} (h : M₁ <=r M₂) (h' : M₂ <=r M₃)
  statement: M₁ <=r M₃
  proof: le_trans (α := Matroidᵣ α) h h'

中文:
定理 IsRestriction.trans
  条件: {M₁ M₂ M₃ : 拟阵 α} (h : M₁ <=r M₂) (h' : M₂ <=r M₃)
  结论: M₁ <=r M₃
  证明: le_trans (α := Matroidᵣ α) h h'

Depends on / 依赖: le_trans
-/
theorem IsRestriction.trans {M₁ M₂ M₃ : Matroid α} (h : M₁ <=r M₂) (h' : M₂ <=r M₃) : M₁ <=r M₃ :=
  le_trans (α := Matroidᵣ α) h h'

/--
theorem `restrict_isRestriction` / 定理 `restrict_isRestriction`

English:
theorem restrict_isRestriction
  given: (M : Matroid α) (R : Set α) (hR : R subseteq M.E := by aesop_mat)
  proof: ⟨R, hR, rfl⟩

中文:
定理 restrict_isRestriction
  条件: (M : 拟阵 α) (R : 集合 α) (hR : R subseteq M.E := by aesop_mat)
  证明: ⟨R, hR, rfl⟩

Depends on / 依赖: aesop_mat
-/
theorem restrict_isRestriction (M : Matroid α) (R : Set α) (hR : R subseteq M.E := by aesop_mat) :
    M ↾ R <=r M :=
  ⟨R, hR, rfl⟩

/--
theorem `IsRestriction.eq_restrict` / 定理 `IsRestriction.eq_restrict`

English:
theorem IsRestriction.eq_restrict
  given: (h : N <=r M)
  statement: M ↾ N.E = N
  proof: by
  obtain ⟨R, -, rfl⟩ := h; rw [restrict_ground_eq]

中文:
定理 IsRestriction.eq_restrict
  条件: (h : N <=r M)
  结论: M ↾ N.E = N
  证明: by
  obtain ⟨R, -, rfl⟩ := h; rw [restrict_ground_eq]

Depends on / 依赖: restrict_ground_eq
-/
theorem IsRestriction.eq_restrict (h : N <=r M) : M ↾ N.E = N := by
  obtain ⟨R, -, rfl⟩ := h; rw [restrict_ground_eq]

/--
theorem `IsRestriction.subset` / 定理 `IsRestriction.subset`

English:
theorem IsRestriction.subset
  given: (h : N <=r M)
  statement: N.E subseteq M.E
  proof: by
  obtain ⟨R, hR, rfl⟩ := h; exact hR

中文:
定理 IsRestriction.subset
  条件: (h : N <=r M)
  结论: N.E subseteq M.E
  证明: by
  obtain ⟨R, hR, rfl⟩ := h; exact hR
-/
theorem IsRestriction.subset (h : N <=r M) : N.E subseteq M.E := by
  obtain ⟨R, hR, rfl⟩ := h; exact hR

/--
theorem `IsRestriction.exists_eq_restrict` / 定理 `IsRestriction.exists_eq_restrict`

English:
theorem IsRestriction.exists_eq_restrict
  given: (h : N <=r M)
  statement: exists R subseteq M.E, N = M ↾ R
  proof: h

中文:
定理 IsRestriction.存在_eq_restrict
  条件: (h : N <=r M)
  结论: 存在 R subseteq M.E, N = M ↾ R
  证明: h
-/
theorem IsRestriction.exists_eq_restrict (h : N <=r M) : exists R subseteq M.E, N = M ↾ R :=
  h

/--
theorem `IsRestriction.of_subset` / 定理 `IsRestriction.of_subset`

English:
theorem IsRestriction.of_subset
  given: {R' : Set α} (M : Matroid α) (h : R subseteq R')
  proof: by
  rw [← restrict_restrict_eq M h]; exact restrict_isRestriction _ _ h

中文:
定理 IsRestriction.of_subset
  条件: {R' : 集合 α} (M : 拟阵 α) (h : R subseteq R')
  证明: by
  rw [← restrict_restrict_eq M h]; exact restrict_isRestriction _ _ h

Depends on / 依赖: restrict_isRestriction, restrict_restrict_eq
-/
theorem IsRestriction.of_subset {R' : Set α} (M : Matroid α) (h : R subseteq R') :
    (M ↾ R) <=r (M ↾ R') := by
  rw [← restrict_restrict_eq M h]; exact restrict_isRestriction _ _ h

/--
theorem `isRestriction_iff_exists` / 定理 `isRestriction_iff_exists`

English:
theorem isRestriction_iff_exists
  statement: (N <=r M) ↔ exists R, R subseteq M.E ∧ N = M ↾ R
  proof: by
  use IsRestriction.exists_eq_restrict; rintro ⟨R, hR, rfl⟩; exact restrict_isRestriction M R hR

中文:
定理 isRestriction_iff_存在
  结论: (N <=r M) ↔ 存在 R, R subseteq M.E ∧ N = M ↾ R
  证明: by
  use IsRestriction.exists_eq_restrict; rintro ⟨R, hR, rfl⟩; exact restrict_isRestriction M R hR

Depends on / 依赖: IsRestriction, IsRestriction.exists_eq_restrict, exists_eq_restrict, restrict_isRestriction
-/
theorem isRestriction_iff_exists : (N <=r M) ↔ exists R, R subseteq M.E ∧ N = M ↾ R := by
  use IsRestriction.exists_eq_restrict; rintro ⟨R, hR, rfl⟩; exact restrict_isRestriction M R hR

/--
theorem `IsStrictRestriction.isRestriction` / 定理 `IsStrictRestriction.isRestriction`

English:
theorem IsStrictRestriction.isRestriction
  given: (h : N <r M)
  statement: N <=r M
  proof: h.1

中文:
定理 IsStrictRestriction.isRestriction
  条件: (h : N <r M)
  结论: N <=r M
  证明: h.1
-/
theorem IsStrictRestriction.isRestriction (h : N <r M) : N <=r M :=
  h.1

/--
theorem `IsStrictRestriction.ne` / 定理 `IsStrictRestriction.ne`

English:
theorem IsStrictRestriction.ne
  given: (h : N <r M)
  statement: N != M
  proof: by
  rintro rfl; rw [← ofMatroid_lt_iff] at h; simp at h

中文:
定理 IsStrictRestriction.ne
  条件: (h : N <r M)
  结论: N != M
  证明: by
  rintro rfl; rw [← ofMatroid_lt_iff] at h; simp at h

Depends on / 依赖: ofMatroid_lt_iff
-/
theorem IsStrictRestriction.ne (h : N <r M) : N != M := by
  rintro rfl; rw [← ofMatroid_lt_iff] at h; simp at h

/--
theorem `IsStrictRestriction.irrefl` / 定理 `IsStrictRestriction.irrefl`

English:
theorem IsStrictRestriction.irrefl
  given: (M : Matroid α)
  statement: ¬ (M <r M)
  proof: fun h => h.ne rfl

中文:
定理 IsStrictRestriction.irrefl
  条件: (M : 拟阵 α)
  结论: ¬ (M <r M)
  证明: fun h => h.ne rfl

Depends on / 依赖: h.ne
-/
theorem IsStrictRestriction.irrefl (M : Matroid α) : ¬ (M <r M) :=
  fun h => h.ne rfl

/--
theorem `IsStrictRestriction.ssubset` / 定理 `IsStrictRestriction.ssubset`

English:
theorem IsStrictRestriction.ssubset
  given: (h : N <r M)
  statement: N.E ⊂ M.E
  proof: by
  obtain ⟨R, -, rfl⟩ := h.1
  refine h.isRestriction.subset.ssubset_of_ne (fun h' => h.2 ⟨R, Subset.rfl, ?_⟩)
  rw [show R = M.E from h']; rw [restrict_idem]; rw [restrict_ground_eq_self]

中文:
定理 IsStrictRestriction.ssubset
  条件: (h : N <r M)
  结论: N.E ⊂ M.E
  证明: by
  obtain ⟨R, -, rfl⟩ := h.1
  refine h.isRestriction.subset.ssubset_of_ne (fun h' => h.2 ⟨R, Subset.rfl, ?_⟩)
  rw [show R = M.E from h']; rw [restrict_idem]; rw [restrict_ground_eq_self]

Depends on / 依赖: Subset, Subset.rfl, h.isRestriction.subset.ssubset_of_ne, isRestriction, restrict_ground_eq_self, restrict_idem, ssubset_of_ne, subset
-/
theorem IsStrictRestriction.ssubset (h : N <r M) : N.E ⊂ M.E := by
  obtain ⟨R, -, rfl⟩ := h.1
  refine h.isRestriction.subset.ssubset_of_ne (fun h' => h.2 ⟨R, Subset.rfl, ?_⟩)
  rw [show R = M.E from h']; rw [restrict_idem]; rw [restrict_ground_eq_self]

/--
theorem `IsStrictRestriction.eq_restrict` / 定理 `IsStrictRestriction.eq_restrict`

English:
theorem IsStrictRestriction.eq_restrict
  given: (h : N <r M)
  statement: M ↾ N.E = N
  proof: h.isRestriction.eq_restrict

中文:
定理 IsStrictRestriction.eq_restrict
  条件: (h : N <r M)
  结论: M ↾ N.E = N
  证明: h.isRestriction.eq_restrict

Depends on / 依赖: eq_restrict, h.isRestriction.eq_restrict, isRestriction
-/
theorem IsStrictRestriction.eq_restrict (h : N <r M) : M ↾ N.E = N :=
  h.isRestriction.eq_restrict

/--
theorem `IsStrictRestriction.exists_eq_restrict` / 定理 `IsStrictRestriction.exists_eq_restrict`

English:
theorem IsStrictRestriction.exists_eq_restrict
  given: (h : N <r M)
  statement: exists R, R ⊂ M.E ∧ N = M ↾ R
  proof: ⟨N.E, h.ssubset, by rw [h.eq_restrict]⟩

中文:
定理 IsStrictRestriction.存在_eq_restrict
  条件: (h : N <r M)
  结论: 存在 R, R ⊂ M.E ∧ N = M ↾ R
  证明: ⟨N.E, h.ssubset, by rw [h.eq_restrict]⟩

Depends on / 依赖: eq_restrict, h.eq_restrict, h.ssubset, ssubset
-/
theorem IsStrictRestriction.exists_eq_restrict (h : N <r M) : exists R, R ⊂ M.E ∧ N = M ↾ R :=
  ⟨N.E, h.ssubset, by rw [h.eq_restrict]⟩

/--
theorem `IsRestriction.isStrictRestriction_of_ne` / 定理 `IsRestriction.isStrictRestriction_of_ne`

English:
theorem IsRestriction.isStrictRestriction_of_ne
  given: (h : N <=r M) (hne : N != M)
  statement: N <r M
  proof: ⟨h, fun h' => hne h.antisymm h'⟩

中文:
定理 IsRestriction.isStrictRestriction_of_ne
  条件: (h : N <=r M) (hne : N != M)
  结论: N <r M
  证明: ⟨h, fun h' => hne h.antisymm h'⟩

Depends on / 依赖: antisymm, h.antisymm
-/
theorem IsRestriction.isStrictRestriction_of_ne (h : N <=r M) (hne : N != M) : N <r M :=
⟨h, fun h' => hne h.antisymm h'⟩

/--
theorem `IsRestriction.eq_or_isStrictRestriction` / 定理 `IsRestriction.eq_or_isStrictRestriction`

English:
theorem IsRestriction.eq_or_isStrictRestriction
  given: (h : N <=r M)
  statement: N = M ∨ N <r M
  proof: by
  simpa using eq_or_lt_of_le (ofMatroid_le_iff.2 h)

中文:
定理 IsRestriction.eq_or_isStrictRestriction
  条件: (h : N <=r M)
  结论: N = M ∨ N <r M
  证明: by
  simpa using eq_or_lt_of_le (ofMatroid_le_iff.2 h)

Depends on / 依赖: eq_or_lt_of_le, ofMatroid_le_iff
-/
theorem IsRestriction.eq_or_isStrictRestriction (h : N <=r M) : N = M ∨ N <r M := by
  simpa using eq_or_lt_of_le (ofMatroid_le_iff.2 h)

/--
theorem `restrict_isStrictRestriction` / 定理 `restrict_isStrictRestriction`

English:
theorem restrict_isStrictRestriction
  given: {M : Matroid α} (hR : R ⊂ M.E)
  statement: M ↾ R <r M
  proof: by
  refine (M.restrict_isRestriction R hR.subset).isStrictRestriction_of_ne (fun h => ?_)
  rw [← h]; rw [restrict_ground_eq] at hR
  exact hR.ne rfl

中文:
定理 restrict_isStrictRestriction
  条件: {M : 拟阵 α} (hR : R ⊂ M.E)
  结论: M ↾ R <r M
  证明: by
  refine (M.restrict_isRestriction R hR.subset).isStrictRestriction_of_ne (fun h => ?_)
  rw [← h]; rw [restrict_ground_eq] at hR
  exact hR.ne rfl

Depends on / 依赖: M.restrict_isRestriction, hR.ne, hR.subset, isStrictRestriction_of_ne, restrict_ground_eq, restrict_isRestriction, subset
-/
theorem restrict_isStrictRestriction {M : Matroid α} (hR : R ⊂ M.E) : M ↾ R <r M := by
  refine (M.restrict_isRestriction R hR.subset).isStrictRestriction_of_ne (fun h => ?_)
  rw [← h]; rw [restrict_ground_eq] at hR
  exact hR.ne rfl

/--
theorem `IsRestriction.isStrictRestriction_of_ground_ne` / 定理 `IsRestriction.isStrictRestriction_of_ground_ne`

English:
theorem IsRestriction.isStrictRestriction_of_ground_ne
  given: (h : N <=r M) (hne : N.E != M.E)
  statement: N <r M
  proof: by
  rw [← h.eq_restrict]
  exact restrict_isStrictRestriction (h.subset.ssubset_of_ne hne)

中文:
定理 IsRestriction.isStrictRestriction_of_ground_ne
  条件: (h : N <=r M) (hne : N.E != M.E)
  结论: N <r M
  证明: by
  rw [← h.eq_restrict]
  exact restrict_isStrictRestriction (h.subset.ssubset_of_ne hne)

Depends on / 依赖: eq_restrict, h.eq_restrict, h.subset.ssubset_of_ne, restrict_isStrictRestriction, ssubset_of_ne, subset
-/
theorem IsRestriction.isStrictRestriction_of_ground_ne (h : N <=r M) (hne : N.E != M.E) : N <r M := by
  rw [← h.eq_restrict]
  exact restrict_isStrictRestriction (h.subset.ssubset_of_ne hne)

/--
theorem `IsStrictRestriction.of_ssubset` / 定理 `IsStrictRestriction.of_ssubset`

English:
theorem IsStrictRestriction.of_ssubset
  given: {R' : Set α} (M : Matroid α) (h : R ⊂ R')
  proof: (IsRestriction.of_subset M h.subset).isStrictRestriction_of_ground_ne h.ne

中文:
定理 IsStrictRestriction.of_ssubset
  条件: {R' : 集合 α} (M : 拟阵 α) (h : R ⊂ R')
  证明: (IsRestriction.of_subset M h.subset).isStrictRestriction_of_ground_ne h.ne

Depends on / 依赖: IsRestriction, IsRestriction.of_subset, h.ne, h.subset, isStrictRestriction_of_ground_ne, of_subset, subset
-/
theorem IsStrictRestriction.of_ssubset {R' : Set α} (M : Matroid α) (h : R ⊂ R') :
    (M ↾ R) <r (M ↾ R') :=
  (IsRestriction.of_subset M h.subset).isStrictRestriction_of_ground_ne h.ne

/--
theorem `IsRestriction.finite` / 定理 `IsRestriction.finite`

English:
theorem IsRestriction.finite
  given: {M : Matroid α} [M.Finite] (h : N <=r M)
  statement: N.Finite
  proof: by
  obtain ⟨R, hR, rfl⟩ := h
exact restrict_finite M.ground_finite.subset hR

中文:
定理 IsRestriction.finite
  条件: {M : 拟阵 α} [M.有限] (h : N <=r M)
  结论: N.有限
  证明: by
  obtain ⟨R, hR, rfl⟩ := h
exact restrict_finite M.ground_finite.subset hR

Depends on / 依赖: M.ground_finite.subset, ground_finite, restrict_finite, subset
-/
theorem IsRestriction.finite {M : Matroid α} [M.Finite] (h : N <=r M) : N.Finite := by
  obtain ⟨R, hR, rfl⟩ := h
exact restrict_finite M.ground_finite.subset hR

/--
theorem `IsRestriction.rankFinite` / 定理 `IsRestriction.rankFinite`

English:
theorem IsRestriction.rankFinite
  given: {M : Matroid α} [RankFinite M] (h : N <=r M)
  statement: N.RankFinite
  proof: by
  obtain ⟨R, -, rfl⟩ := h
  infer_instance

中文:
定理 IsRestriction.rankFinite
  条件: {M : 拟阵 α} [RankFinite M] (h : N <=r M)
  结论: N.RankFinite
  证明: by
  obtain ⟨R, -, rfl⟩ := h
  infer_instance

Depends on / 依赖: infer_instance
-/
theorem IsRestriction.rankFinite {M : Matroid α} [RankFinite M] (h : N <=r M) : N.RankFinite := by
  obtain ⟨R, -, rfl⟩ := h
  infer_instance

/--
theorem `IsRestriction.finitary` / 定理 `IsRestriction.finitary`

English:
theorem IsRestriction.finitary
  given: {M : Matroid α} [Finitary M] (h : N <=r M)
  statement: N.Finitary
  proof: by
  obtain ⟨R, -, rfl⟩ := h
  infer_instance

中文:
定理 IsRestriction.finitary
  条件: {M : 拟阵 α} [Finitary M] (h : N <=r M)
  结论: N.Finitary
  证明: by
  obtain ⟨R, -, rfl⟩ := h
  infer_instance

Depends on / 依赖: infer_instance
-/
theorem IsRestriction.finitary {M : Matroid α} [Finitary M] (h : N <=r M) : N.Finitary := by
  obtain ⟨R, -, rfl⟩ := h
  infer_instance

/--
theorem `finite_setOfPred_isRestriction` / 定理 `finite_setOfPred_isRestriction`

English:
theorem finite_setOfPred_isRestriction
  given: (M : Matroid α) [M.Finite]
  statement: {N | N <=r M}.Finite
  proof: (M.ground_finite.finite_subsets.image (fun R => M ↾ R)).subset
    by rintro _ ⟨R, hR, rfl⟩; exact ⟨_, hR, rfl⟩

@[deprecated (since := "2026-07-09")]
alias finite_setOf_isRestriction := finite_setOfPred_isRestriction

中文:
定理 finite_setOfPred_isRestriction
  条件: (M : 拟阵 α) [M.有限]
  结论: {N | N <=r M}.有限
  证明: (M.ground_finite.finite_subsets.image (fun R => M ↾ R)).subset
    by rintro _ ⟨R, hR, rfl⟩; exact ⟨_, hR, rfl⟩

@[deprecated (since := "2026-07-09")]
alias finite_setOf_isRestriction := finite_setOfPred_isRestriction

Depends on / 依赖: M.ground_finite.finite_subsets.image, finite_subsets, ground_finite, subset
-/
theorem finite_setOfPred_isRestriction (M : Matroid α) [M.Finite] : {N | N <=r M}.Finite :=
(M.ground_finite.finite_subsets.image (fun R => M ↾ R)).subset
    by rintro _ ⟨R, hR, rfl⟩; exact ⟨_, hR, rfl⟩

@[deprecated (since := "2026-07-09")]
alias finite_setOf_isRestriction := finite_setOfPred_isRestriction

/--
theorem `Indep.of_isRestriction` / 定理 `Indep.of_isRestriction`

English:
theorem Indep.of_isRestriction
  given: (hI : N.Indep I) (hNM : N <=r M)
  statement: M.Indep I
  proof: by
  obtain ⟨R, -, rfl⟩ := hNM; exact hI.of_restrict

中文:
定理 Indep.of_isRestriction
  条件: (hI : N.Indep I) (hNM : N <=r M)
  结论: M.Indep I
  证明: by
  obtain ⟨R, -, rfl⟩ := hNM; exact hI.of_restrict

Depends on / 依赖: hI.of_restrict, of_restrict
-/
theorem Indep.of_isRestriction (hI : N.Indep I) (hNM : N <=r M) : M.Indep I := by
  obtain ⟨R, -, rfl⟩ := hNM; exact hI.of_restrict

/--
theorem `Indep.indep_isRestriction` / 定理 `Indep.indep_isRestriction`

English:
theorem Indep.indep_isRestriction
  given: (hI : M.Indep I) (hNM : N <=r M) (hIN : I subseteq N.E)
  statement: N.Indep I
  proof: by
  obtain ⟨R, -, rfl⟩ := hNM; simpa [hI]

中文:
定理 Indep.indep_isRestriction
  条件: (hI : M.Indep I) (hNM : N <=r M) (hIN : I subseteq N.E)
  结论: N.Indep I
  证明: by
  obtain ⟨R, -, rfl⟩ := hNM; simpa [hI]
-/
theorem Indep.indep_isRestriction (hI : M.Indep I) (hNM : N <=r M) (hIN : I subseteq N.E) : N.Indep I := by
  obtain ⟨R, -, rfl⟩ := hNM; simpa [hI]

/--
theorem `IsRestriction.indep_iff` / 定理 `IsRestriction.indep_iff`

English:
theorem IsRestriction.indep_iff
  given: (hMN : N <=r M)
  statement: N.Indep I ↔ M.Indep I ∧ I subseteq N.E
  proof: ⟨fun h => ⟨h.of_isRestriction hMN, h.subset_ground⟩, fun h => h.1.indep_isRestriction hMN h.2⟩

中文:
定理 IsRestriction.indep_iff
  条件: (hMN : N <=r M)
  结论: N.Indep I ↔ M.Indep I ∧ I subseteq N.E
  证明: ⟨fun h => ⟨h.of_isRestriction hMN, h.subset_ground⟩, fun h => h.1.indep_isRestriction hMN h.2⟩

Depends on / 依赖: h.of_isRestriction, h.subset_ground, indep_isRestriction, of_isRestriction, subset_ground
-/
theorem IsRestriction.indep_iff (hMN : N <=r M) : N.Indep I ↔ M.Indep I ∧ I subseteq N.E :=
  ⟨fun h => ⟨h.of_isRestriction hMN, h.subset_ground⟩, fun h => h.1.indep_isRestriction hMN h.2⟩

/--
theorem `IsBasis.isBasis_isRestriction` / 定理 `IsBasis.isBasis_isRestriction`

English:
theorem IsBasis.isBasis_isRestriction
  given: (hI : M.IsBasis I X) (hNM : N <=r M) (hX : X subseteq N.E)
  proof: by
  obtain ⟨R, hR, rfl⟩ := hNM; rwa [isBasis_restrict_iff, and_iff_left (show X subseteq R from hX)]

中文:
定理 是基.isBasis_isRestriction
  条件: (hI : M.是基 I X) (hNM : N <=r M) (hX : X subseteq N.E)
  证明: by
  obtain ⟨R, hR, rfl⟩ := hNM; rwa [isBasis_restrict_iff, and_iff_left (show X subseteq R from hX)]

Depends on / 依赖: and_iff_left, isBasis_restrict_iff, subseteq
-/
theorem IsBasis.isBasis_isRestriction (hI : M.IsBasis I X) (hNM : N <=r M) (hX : X subseteq N.E) :
    N.IsBasis I X := by
  obtain ⟨R, hR, rfl⟩ := hNM; rwa [isBasis_restrict_iff, and_iff_left (show X subseteq R from hX)]

/--
theorem `IsBasis.of_isRestriction` / 定理 `IsBasis.of_isRestriction`

English:
theorem IsBasis.of_isRestriction
  given: (hI : N.IsBasis I X) (hNM : N <=r M)
  statement: M.IsBasis I X
  proof: by
  obtain ⟨R, hR, rfl⟩ := hNM; exact ((isBasis_restrict_iff hR).1 hI).1

中文:
定理 是基.of_isRestriction
  条件: (hI : N.是基 I X) (hNM : N <=r M)
  结论: M.是基 I X
  证明: by
  obtain ⟨R, hR, rfl⟩ := hNM; exact ((isBasis_restrict_iff hR).1 hI).1

Depends on / 依赖: isBasis_restrict_iff
-/
theorem IsBasis.of_isRestriction (hI : N.IsBasis I X) (hNM : N <=r M) : M.IsBasis I X := by
  obtain ⟨R, hR, rfl⟩ := hNM; exact ((isBasis_restrict_iff hR).1 hI).1

/--
theorem `IsBase.isBasis_of_isRestriction` / 定理 `IsBase.isBasis_of_isRestriction`

English:
theorem IsBase.isBasis_of_isRestriction
  given: (hI : N.IsBase I) (hNM : N <=r M)
  statement: M.IsBasis I N.E
  proof: by
  obtain ⟨R, hR, rfl⟩ := hNM; rwa [isBase_restrict_iff] at hI

中文:
定理 IsBase.isBasis_of_isRestriction
  条件: (hI : N.IsBase I) (hNM : N <=r M)
  结论: M.是基 I N.E
  证明: by
  obtain ⟨R, hR, rfl⟩ := hNM; rwa [isBase_restrict_iff] at hI

Depends on / 依赖: isBase_restrict_iff
-/
theorem IsBase.isBasis_of_isRestriction (hI : N.IsBase I) (hNM : N <=r M) : M.IsBasis I N.E := by
  obtain ⟨R, hR, rfl⟩ := hNM; rwa [isBase_restrict_iff] at hI

/--
theorem `IsRestriction.base_iff` / 定理 `IsRestriction.base_iff`

English:
theorem IsRestriction.base_iff
  given: (hMN : N <=r M) {B : Set α}
  statement: N.IsBase B ↔ M.IsBasis B N.E
  proof: ⟨fun h => IsBase.isBasis_of_isRestriction h hMN,
    fun h => by simpa [hMN.eq_restrict] using h.restrict_isBase⟩

中文:
定理 IsRestriction.base_iff
  条件: (hMN : N <=r M) {B : 集合 α}
  结论: N.IsBase B ↔ M.是基 B N.E
  证明: ⟨fun h => IsBase.isBasis_of_isRestriction h hMN,
    fun h => by simpa [hMN.eq_restrict] using h.restrict_isBase⟩

Depends on / 依赖: IsBase, IsBase.isBasis_of_isRestriction, eq_restrict, h.restrict_isBase, hMN.eq_restrict, isBasis_of_isRestriction, restrict_isBase
-/
theorem IsRestriction.base_iff (hMN : N <=r M) {B : Set α} : N.IsBase B ↔ M.IsBasis B N.E :=
  ⟨fun h => IsBase.isBasis_of_isRestriction h hMN,
    fun h => by simpa [hMN.eq_restrict] using h.restrict_isBase⟩

/--
theorem `IsRestriction.isBasis_iff` / 定理 `IsRestriction.isBasis_iff`

English:
theorem IsRestriction.isBasis_iff
  given: (hMN : N <=r M)
  statement: N.IsBasis I X ↔ M.IsBasis I X ∧ X subseteq N.E
  proof: ⟨fun h => ⟨h.of_isRestriction hMN, h.subset_ground⟩, fun h => h.1.isBasis_isRestriction hMN h.2⟩

中文:
定理 IsRestriction.isBasis_iff
  条件: (hMN : N <=r M)
  结论: N.是基 I X ↔ M.是基 I X ∧ X subseteq N.E
  证明: ⟨fun h => ⟨h.of_isRestriction hMN, h.subset_ground⟩, fun h => h.1.isBasis_isRestriction hMN h.2⟩

Depends on / 依赖: h.of_isRestriction, h.subset_ground, isBasis_isRestriction, of_isRestriction, subset_ground
-/
theorem IsRestriction.isBasis_iff (hMN : N <=r M) : N.IsBasis I X ↔ M.IsBasis I X ∧ X subseteq N.E :=
  ⟨fun h => ⟨h.of_isRestriction hMN, h.subset_ground⟩, fun h => h.1.isBasis_isRestriction hMN h.2⟩

/--
theorem `Dep.of_isRestriction` / 定理 `Dep.of_isRestriction`

English:
theorem Dep.of_isRestriction
  given: (hX : N.Dep X) (hNM : N <=r M)
  statement: M.Dep X
  proof: by
  obtain ⟨R, hR, rfl⟩ := hNM
  rw [restrict_dep_iff] at hX
  exact ⟨hX.1, hX.2.trans hR⟩

中文:
定理 Dep.of_isRestriction
  条件: (hX : N.Dep X) (hNM : N <=r M)
  结论: M.Dep X
  证明: by
  obtain ⟨R, hR, rfl⟩ := hNM
  rw [restrict_dep_iff] at hX
  exact ⟨hX.1, hX.2.trans hR⟩

Depends on / 依赖: restrict_dep_iff
-/
theorem Dep.of_isRestriction (hX : N.Dep X) (hNM : N <=r M) : M.Dep X := by
  obtain ⟨R, hR, rfl⟩ := hNM
  rw [restrict_dep_iff] at hX
  exact ⟨hX.1, hX.2.trans hR⟩

/--
theorem `Dep.dep_isRestriction` / 定理 `Dep.dep_isRestriction`

English:
theorem Dep.dep_isRestriction
  given: (hX : M.Dep X) (hNM : N <=r M) (hXE : X subseteq N.E := by aesop_mat)
  proof: by
  obtain ⟨R, -, rfl⟩ := hNM; simpa [hX.not_indep]

中文:
定理 Dep.dep_isRestriction
  条件: (hX : M.Dep X) (hNM : N <=r M) (hXE : X subseteq N.E := by aesop_mat)
  证明: by
  obtain ⟨R, -, rfl⟩ := hNM; simpa [hX.not_indep]

Depends on / 依赖: N.Dep, aesop_mat, hX.not_indep, not_indep
-/
theorem Dep.dep_isRestriction (hX : M.Dep X) (hNM : N <=r M) (hXE : X subseteq N.E := by aesop_mat) :
    N.Dep X := by
  obtain ⟨R, -, rfl⟩ := hNM; simpa [hX.not_indep]

/--
theorem `IsRestriction.dep_iff` / 定理 `IsRestriction.dep_iff`

English:
theorem IsRestriction.dep_iff
  given: (hMN : N <=r M)
  statement: N.Dep X ↔ M.Dep X ∧ X subseteq N.E
  proof: ⟨fun h => ⟨h.of_isRestriction hMN, h.subset_ground⟩, fun h => h.1.dep_isRestriction hMN h.2⟩

中文:
定理 IsRestriction.dep_iff
  条件: (hMN : N <=r M)
  结论: N.Dep X ↔ M.Dep X ∧ X subseteq N.E
  证明: ⟨fun h => ⟨h.of_isRestriction hMN, h.subset_ground⟩, fun h => h.1.dep_isRestriction hMN h.2⟩

Depends on / 依赖: dep_isRestriction, h.of_isRestriction, h.subset_ground, of_isRestriction, subset_ground
-/
theorem IsRestriction.dep_iff (hMN : N <=r M) : N.Dep X ↔ M.Dep X ∧ X subseteq N.E :=
  ⟨fun h => ⟨h.of_isRestriction hMN, h.subset_ground⟩, fun h => h.1.dep_isRestriction hMN h.2⟩

end IsRestriction

/-!
### `IsBasis` and `Base`
The lemmas below exploit the fact that `(M ↾ X).Base I ↔ M.IsBasis I X` to transfer facts about
`Matroid.Base` to facts about `Matroid.IsBasis`.
Their statements thematically belong in `Data.Matroid.Basic`, but they appear here because their
proofs depend on the API for `Matroid.restrict`,
-/

section IsBasis

variable {B J : Set α} {e : α}

/--
theorem `IsBasis.transfer` / 定理 `IsBasis.transfer`

English:
theorem IsBasis.transfer
  statement: (hIX : M.IsBasis I X) (hJX : M.IsBasis J X) (hXY : X subseteq Y)
  proof: by
  rw [← isBase_restrict_iff]; rw [← isBase_restrict_iff] at hJY
  exact hJY.isBase_of_isBasis_superset hJX.subset (hIX.isBasis_restrict_of_subset hXY)

中文:
定理 是基.transfer
  结论: (hIX : M.是基 I X) (hJX : M.是基 J X) (hXY : X subseteq Y)
  证明: by
  rw [← isBase_restrict_iff]; rw [← isBase_restrict_iff] at hJY
  exact hJY.isBase_of_isBasis_superset hJX.subset (hIX.isBasis_restrict_of_subset hXY)

Depends on / 依赖: hIX.isBasis_restrict_of_subset, hJX.subset, hJY.isBase_of_isBasis_superset, isBase_of_isBasis_superset, isBase_restrict_iff, isBasis_restrict_of_subset, subset
-/
theorem IsBasis.transfer (hIX : M.IsBasis I X) (hJX : M.IsBasis J X) (hXY : X subseteq Y)
    (hJY : M.IsBasis J Y) : M.IsBasis I Y := by
  rw [← isBase_restrict_iff]; rw [← isBase_restrict_iff] at hJY
  exact hJY.isBase_of_isBasis_superset hJX.subset (hIX.isBasis_restrict_of_subset hXY)

/--
theorem `IsBasis.isBasis_of_isBasis_of_subset_of_subset` / 定理 `IsBasis.isBasis_of_isBasis_of_subset_of_subset`

English:
theorem IsBasis.isBasis_of_isBasis_of_subset_of_subset
  statement: (hI : M.IsBasis I X) (hJ : M.IsBasis J Y)
  proof: by
  have hI' := hI.isBasis_subset (subset_inter hI.subset hIY) inter_subset_left
  have hJ' := hJ.isBasis_subset (subset_inter hJX hJ.subset) inter_subset_right
  exact hI'.transfer hJ' inter_subset_right hJ

中文:
定理 是基.isBasis_of_isBasis_of_subset_of_subset
  结论: (hI : M.是基 I X) (hJ : M.是基 J Y)
  证明: by
  have hI' := hI.isBasis_subset (subset_inter hI.subset hIY) inter_subset_left
  have hJ' := hJ.isBasis_subset (subset_inter hJX hJ.subset) inter_subset_right
  exact hI'.transfer hJ' inter_subset_right hJ

Depends on / 依赖: hI.isBasis_subset, hI.subset, hJ.isBasis_subset, hJ.subset, inter_subset_left, inter_subset_right, isBasis_subset, subset, subset_inter, transfer
-/
theorem IsBasis.isBasis_of_isBasis_of_subset_of_subset (hI : M.IsBasis I X) (hJ : M.IsBasis J Y)
    (hJX : J subseteq X) (hIY : I subseteq Y) : M.IsBasis I Y := by
  have hI' := hI.isBasis_subset (subset_inter hI.subset hIY) inter_subset_left
  have hJ' := hJ.isBasis_subset (subset_inter hJX hJ.subset) inter_subset_right
  exact hI'.transfer hJ' inter_subset_right hJ

/--
theorem `Indep.exists_isBasis_subset_union_isBasis` / 定理 `Indep.exists_isBasis_subset_union_isBasis`

English:
theorem Indep.exists_isBasis_subset_union_isBasis
  statement: (hI : M.Indep I) (hIX : I subseteq X)
  proof: by
  obtain ⟨I', hI', hII', hI'IJ⟩ :=
    (hI.indep_restrict_of_subset hIX).exists_isBase_subset_union_isBase (IsBasis.isBase_restrict hJ)
  rw [isBase_restrict_iff] at hI'
  exact ⟨I', hI', hII', hI'IJ⟩

中文:
定理 Indep.存在_isBasis_subset_union_isBasis
  结论: (hI : M.Indep I) (hIX : I subseteq X)
  证明: by
  obtain ⟨I', hI', hII', hI'IJ⟩ :=
    (hI.indep_restrict_of_subset hIX).exists_isBase_subset_union_isBase (IsBasis.isBase_restrict hJ)
  rw [isBase_restrict_iff] at hI'
  exact ⟨I', hI', hII', hI'IJ⟩

Depends on / 依赖: IsBasis, IsBasis.isBase_restrict, exists_isBase_subset_union_isBase, hI.indep_restrict_of_subset, indep_restrict_of_subset, isBase_restrict, isBase_restrict_iff
-/
theorem Indep.exists_isBasis_subset_union_isBasis (hI : M.Indep I) (hIX : I subseteq X)
    (hJ : M.IsBasis J X) : exists I', M.IsBasis I' X ∧ I subseteq I' ∧ I' subseteq I union J := by
  obtain ⟨I', hI', hII', hI'IJ⟩ :=
    (hI.indep_restrict_of_subset hIX).exists_isBase_subset_union_isBase (IsBasis.isBase_restrict hJ)
  rw [isBase_restrict_iff] at hI'
  exact ⟨I', hI', hII', hI'IJ⟩

/--
theorem `Indep.exists_insert_of_not_isBasis` / 定理 `Indep.exists_insert_of_not_isBasis`

English:
theorem Indep.exists_insert_of_not_isBasis
  statement: (hI : M.Indep I) (hIX : I subseteq X) (hI' : ¬M.IsBasis I X)
  proof: by
  rw [← isBase_restrict_iff] at hI'; rw [← isBase_restrict_iff] at hJ
  obtain ⟨e, he, hi⟩ := (hI.indep_restrict_of_subset hIX).exists_insert_of_not_isBase hI' hJ
  exact ⟨e, he, (restrict_indep_iff.mp hi).1⟩

中文:
定理 Indep.存在_insert_of_not_isBasis
  结论: (hI : M.Indep I) (hIX : I subseteq X) (hI' : ¬M.是基 I X)
  证明: by
  rw [← isBase_restrict_iff] at hI'; rw [← isBase_restrict_iff] at hJ
  obtain ⟨e, he, hi⟩ := (hI.indep_restrict_of_subset hIX).exists_insert_of_not_isBase hI' hJ
  exact ⟨e, he, (restrict_indep_iff.mp hi).1⟩

Depends on / 依赖: exists_insert_of_not_isBase, hI.indep_restrict_of_subset, indep_restrict_of_subset, isBase_restrict_iff, restrict_indep_iff, restrict_indep_iff.mp
-/
theorem Indep.exists_insert_of_not_isBasis (hI : M.Indep I) (hIX : I subseteq X) (hI' : ¬M.IsBasis I X)
    (hJ : M.IsBasis J X) : exists e in J \ I, M.Indep (insert e I) := by
  rw [← isBase_restrict_iff] at hI'; rw [← isBase_restrict_iff] at hJ
  obtain ⟨e, he, hi⟩ := (hI.indep_restrict_of_subset hIX).exists_insert_of_not_isBase hI' hJ
  exact ⟨e, he, (restrict_indep_iff.mp hi).1⟩

/--
theorem `IsBasis.isBase_of_isBase_subset` / 定理 `IsBasis.isBase_of_isBase_subset`

English:
theorem IsBasis.isBase_of_isBase_subset
  given: (hIX : M.IsBasis I X) (hB : M.IsBase B) (hBX : B subseteq X)
  proof: hB.isBase_of_isBasis_superset hBX hIX

中文:
定理 是基.isBase_of_isBase_subset
  条件: (hIX : M.是基 I X) (hB : M.IsBase B) (hBX : B subseteq X)
  证明: hB.isBase_of_isBasis_superset hBX hIX

Depends on / 依赖: hB.isBase_of_isBasis_superset, isBase_of_isBasis_superset
-/
theorem IsBasis.isBase_of_isBase_subset (hIX : M.IsBasis I X) (hB : M.IsBase B) (hBX : B subseteq X) :
    M.IsBase I :=
  hB.isBase_of_isBasis_superset hBX hIX

/--
theorem `IsBasis.exchange` / 定理 `IsBasis.exchange`

English:
theorem IsBasis.exchange
  given: (hIX : M.IsBasis I X) (hJX : M.IsBasis J X) (he : e in I \ J)
  proof: by
  obtain ⟨y, hy, h⟩ := hIX.restrict_isBase.exchange hJX.restrict_isBase he
  exact ⟨y, hy, by rwa [isBase_restrict_iff] at h⟩

中文:
定理 是基.exchange
  条件: (hIX : M.是基 I X) (hJX : M.是基 J X) (he : e in I \ J)
  证明: by
  obtain ⟨y, hy, h⟩ := hIX.restrict_isBase.exchange hJX.restrict_isBase he
  exact ⟨y, hy, by rwa [isBase_restrict_iff] at h⟩

Depends on / 依赖: exchange, hIX.restrict_isBase.exchange, hJX.restrict_isBase, isBase_restrict_iff, restrict_isBase
-/
theorem IsBasis.exchange (hIX : M.IsBasis I X) (hJX : M.IsBasis J X) (he : e in I \ J) :
    exists f in J \ I, M.IsBasis (insert f (I \ {e})) X := by
  obtain ⟨y, hy, h⟩ := hIX.restrict_isBase.exchange hJX.restrict_isBase he
  exact ⟨y, hy, by rwa [isBase_restrict_iff] at h⟩

/--
theorem `IsBasis.eq_exchange_of_sdiff_eq_singleton` / 定理 `IsBasis.eq_exchange_of_sdiff_eq_singleton`

English:
theorem IsBasis.eq_exchange_of_sdiff_eq_singleton
  statement: (hI : M.IsBasis I X) (hJ : M.IsBasis J X)
  proof: by
  rw [← isBase_restrict_iff] at hI hJ; exact hI.eq_exchange_of_sdiff_eq_singleton hJ hIJ

@[deprecated (since := "2026-06-03")]
alias IsBasis.eq_exchange_of_diff_eq_singleton := IsBasis.eq_exchange_of_sdiff_eq_singleton

中文:
定理 是基.eq_exchange_of_sdiff_eq_singleton
  结论: (hI : M.是基 I X) (hJ : M.是基 J X)
  证明: by
  rw [← isBase_restrict_iff] at hI hJ; exact hI.eq_exchange_of_sdiff_eq_singleton hJ hIJ

@[deprecated (since := "2026-06-03")]
alias IsBasis.eq_exchange_of_diff_eq_singleton := IsBasis.eq_exchange_of_sdiff_eq_singleton

Depends on / 依赖: eq_exchange_of_sdiff_eq_singleton, hI.eq_exchange_of_sdiff_eq_singleton, isBase_restrict_iff
-/
theorem IsBasis.eq_exchange_of_sdiff_eq_singleton (hI : M.IsBasis I X) (hJ : M.IsBasis J X)
    (hIJ : I \ J = {e}) : exists f in J \ I, J = insert f I \ {e} := by
  rw [← isBase_restrict_iff] at hI hJ; exact hI.eq_exchange_of_sdiff_eq_singleton hJ hIJ

@[deprecated (since := "2026-06-03")]
alias IsBasis.eq_exchange_of_diff_eq_singleton := IsBasis.eq_exchange_of_sdiff_eq_singleton

/--
theorem `IsBasis'.encard_eq_encard` / 定理 `IsBasis'.encard_eq_encard`

English:
theorem IsBasis'.encard_eq_encard
  given: (hI : M.IsBasis' I X) (hJ : M.IsBasis' J X)
  proof: by
  rw [← isBase_restrict_iff'] at hI hJ; exact hI.encard_eq_encard_of_isBase hJ

中文:
定理 是基'.encard_eq_encard
  条件: (hI : M.是基' I X) (hJ : M.是基' J X)
  证明: by
  rw [← isBase_restrict_iff'] at hI hJ; exact hI.encard_eq_encard_of_isBase hJ
-/
theorem IsBasis'.encard_eq_encard (hI : M.IsBasis' I X) (hJ : M.IsBasis' J X) :
    I.encard = J.encard := by
  rw [← isBase_restrict_iff'] at hI hJ; exact hI.encard_eq_encard_of_isBase hJ

/--
theorem `IsBasis.encard_eq_encard` / 定理 `IsBasis.encard_eq_encard`

English:
theorem IsBasis.encard_eq_encard
  given: (hI : M.IsBasis I X) (hJ : M.IsBasis J X)
  statement: I.encard = J.encard
  proof: hI.isBasis'.encard_eq_encard hJ.isBasis'

中文:
定理 是基.encard_eq_encard
  条件: (hI : M.是基 I X) (hJ : M.是基 J X)
  结论: I.encard = J.encard
  证明: hI.isBasis'.encard_eq_encard hJ.isBasis'

Depends on / 依赖: encard_eq_encard, hI.isBasis, hJ.isBasis, isBasis
-/
theorem IsBasis.encard_eq_encard (hI : M.IsBasis I X) (hJ : M.IsBasis J X) : I.encard = J.encard :=
  hI.isBasis'.encard_eq_encard hJ.isBasis'

/--
theorem `Indep.augment` / 定理 `Indep.augment`

English:
theorem Indep.augment
  given: (hI : M.Indep I) (hJ : M.Indep J) (hIJ : I.encard < J.encard)
  proof: by
  by_contra! he
  have hb : M.IsBasis I (I union J) := by
    simp_rw [hI.isBasis_iff_forall_insert_dep subset_union_left, union_sdiff_left, mem_sdiff,
      and_imp, dep_iff, insert_subset_iff, and_iff_left hI.subset_ground]
    exact fun e heJ heI => ⟨he e ⟨heJ, heI⟩, hJ.subset_ground heJ⟩
  ob

中文:
定理 Indep.augment
  条件: (hI : M.Indep I) (hJ : M.Indep J) (hIJ : I.encard < J.encard)
  证明: by
  by_contra! he
  have hb : M.IsBasis I (I union J) := by
    simp_rw [hI.isBasis_iff_forall_insert_dep subset_union_left, union_sdiff_left, mem_sdiff,
      and_imp, dep_iff, insert_subset_iff, and_iff_left hI.subset_ground]
    exact fun e heJ heI => ⟨he e ⟨heJ, heI⟩, hJ.subset_ground heJ⟩
  ob

Depends on / 依赖: I.subset_union_right, IsBasis, M.IsBasis, and_iff_left, and_imp, dep_iff, encard_eq_encard, encard_mono, hI.isBasis_iff_forall_insert_dep, hI.subset_ground, hIJ.not_ge, hJ.subset_ground, hJ.subset_isBasis_of_subset, insert_subset_iff, isBasis_iff_forall_insert_dep, mem_sdiff, not_ge, simp_rw, subset_ground, subset_isBasis_of_subset
-/
theorem Indep.augment (hI : M.Indep I) (hJ : M.Indep J) (hIJ : I.encard < J.encard) :
    exists e in J \ I, M.Indep (insert e I) := by
  by_contra! he
  have hb : M.IsBasis I (I union J) := by
    simp_rw [hI.isBasis_iff_forall_insert_dep subset_union_left, union_sdiff_left, mem_sdiff,
      and_imp, dep_iff, insert_subset_iff, and_iff_left hI.subset_ground]
    exact fun e heJ heI => ⟨he e ⟨heJ, heI⟩, hJ.subset_ground heJ⟩
  obtain ⟨J', hJ', hJJ'⟩ := hJ.subset_isBasis_of_subset I.subset_union_right
  rw [← hJ'.encard_eq_encard hb] at hIJ
  exact hIJ.not_ge (encard_mono hJJ')

/--
lemma `Indep.augment_finset` / 引理 `Indep.augment_finset`

English:
lemma Indep.augment_finset
  statement: {I J : Finset α} (hI : M.Indep I) (hJ : M.Indep J)
  proof: by
  obtain ⟨x, hx, hxI⟩ := hI.augment hJ (by simpa [encard_eq_coe_toFinset_card])
  simp only [mem_sdiff, Finset.mem_coe] at hx
  exact ⟨x, hx.1, hx.2, hxI⟩

中文:
引理 Indep.augment_finset
  结论: {I J : 有限集 α} (hI : M.Indep I) (hJ : M.Indep J)
  证明: by
  obtain ⟨x, hx, hxI⟩ := hI.augment hJ (by simpa [encard_eq_coe_toFinset_card])
  simp only [mem_sdiff, Finset.mem_coe] at hx
  exact ⟨x, hx.1, hx.2, hxI⟩

Depends on / 依赖: Finset, Finset.mem_coe, augment, encard_eq_coe_toFinset_card, hI.augment, mem_coe, mem_sdiff
-/
lemma Indep.augment_finset {I J : Finset α} (hI : M.Indep I) (hJ : M.Indep J)
    (hIJ : I.card < J.card) : exists e in J, e ∉ I ∧ M.Indep (insert e I) := by
  obtain ⟨x, hx, hxI⟩ := hI.augment hJ (by simpa [encard_eq_coe_toFinset_card])
  simp only [mem_sdiff, Finset.mem_coe] at hx
  exact ⟨x, hx.1, hx.2, hxI⟩

end IsBasis

end Matroid
