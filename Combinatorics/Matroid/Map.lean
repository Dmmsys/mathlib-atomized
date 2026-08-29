/-
Copyright (c) 2024 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson
-/
module

public import Mathlib.Combinatorics.Matroid.Constructions
public import Mathlib.Data.Set.Notation

/-!
# Maps between matroids

This file defines maps and comaps, which move a matroid on one type to a matroid on another
using a function between the types. The constructions are (up to isomorphism)
just combinations of restrictions and parallel extensions, so are not mathematically difficult.

Because a matroid `M : Matroid α` is defined with am embedded ground set `M.E : Set α`
which contains all the structure of `M`, there are several types of map and comap
one could reasonably ask for;
for instance, we could map `M : Matroid α` to a `Matroid β` using either
a function `f : α → β`, a function `f : ↑M.E → β` or indeed a function `f : ↑M.E → ↑E`
for some `E : Set β`. We attempt to give definitions that capture most reasonable use cases.

`Matroid.map` and `Matroid.comap` are defined in terms of bare functions rather than
functions defined on subtypes, so are often easier to work in practice than the subtype variants.
In fact, the statement that `N = Matroid.map M f _` for some `f : α → β`
is equivalent to the existence of an isomorphism from `M` to `N`,
except in the trivial degenerate case where `M` is an empty matroid on a nonempty type and `N`
is an empty matroid on an empty type.
This can be simpler to use than an actual formal isomorphism, which requires subtypes.

## Main definitions

In the definitions below, `M` and `N` are matroids on `α` and `β` respectively.

* For `f : α → β`, `Matroid.comap N f` is the matroid on `α` with ground set `f ⁻¹' N.E`
  in which each `I` is independent if and only if `f` is injective on `I` and
  `f '' I` is independent in `N`.
  (For each nonloop `x` of `N`, the set `f ⁻¹' {x}` is a parallel class of `N.comap f`)

* `Matroid.comapOn N f E` is the restriction of `N.comap f` to `E` for some `E : Set α`.

* For an embedding `f : M.E ↪ β` defined on the subtype `↑M.E`,
  `Matroid.mapSetEmbedding M f` is the matroid on `β` with ground set `range f`
  whose independent sets are the images of those in `M`. This matroid is isomorphic to `M`.

* For a function `f : α → β` and a proof `hf` that `f` is injective on `M.E`,
  `Matroid.map f hf` is the matroid on `β` with ground set `f '' M.E`
  whose independent sets are the images of those in `M`. This matroid is isomorphic to `M`,
  and does not depend on the values `f` takes outside `M.E`.

* `Matroid.mapEmbedding f` is a version of `Matroid.map` where `f : α ↪ β` is a bundled embedding.
  It is defined separately because the global injectivity of `f` gives some nicer `simp` lemmas.

* `Matroid.mapEquiv f` is a version of `Matroid.map` where `f : α ≃ β` is a bundled equivalence.
  It is defined separately because we get even nicer `simp` lemmas.

* `Matroid.mapSetEquiv f` is a version of `Matroid.map` where `f : M.E ≃ E` is an equivalence on
  subtypes. It gives a matroid on `β` with ground set `E`.

* For `X : Set α`, `Matroid.restrictSubtype M X` is the `Matroid ↥X` with ground set
  `univ : Set ↥X`. This matroid is isomorphic to `M ↾ X`.

## Implementation details

The definition of `comap` is the only place where we need to actually define a matroid from scratch.
After `comap` is defined, we can define `map` and its variants indirectly in terms of `comap`.

If `f : α → β` is injective on `M.E`, the independent sets of `M.map f hf` are the images of
the independent set of `M`; i.e. `(M.map f hf).Indep I ↔ ∃ I₀, M.Indep I₀ ∧ I = f '' I₀`.
But if `f` is globally injective, we can phrase this more directly;
indeed, `(M.map f _).Indep I ↔ M.Indep (f ⁻¹' I) ∧ I ⊆ range f`.
If `f` is an equivalence we have `(M.map f _).Indep I ↔ M.Indep (f.symm '' I)`.
In order that these stronger statements can be `@[simp]`,
we define `mapEmbedding` and `mapEquiv` separately from `map`.

## Notes

For finite matroids, both maps and comaps are a special case of a construction of
Perfect [perfect1969matroid] in which a matroid structure can be transported across an arbitrary
bipartite graph that may not correspond to a function at all (See [oxley2011], Theorem 11.2.12).
It would have been nice to use this more general construction as a basis for the definition
of both `Matroid.map` and `Matroid.comap`.

Unfortunately, we can't do this, because the construction doesn't extend to infinite matroids.
Specifically, if `M₁` and `M₂` are matroids on the same type `α`,
and `f` is the natural function from `α ⊕ α` to `α`,
then the images under `f` of the independent sets of the direct sum `M₁ ⊕ M₂` are
the independent sets of a matroid if and only if the union of `M₁` and `M₂` is a matroid,
and unions do not exist for some pairs of infinite matroids: see [aignerhorev2012infinite].
For this reason, `Matroid.map` requires injectivity to be well-defined in general.

## TODO

* Bundled matroid isomorphisms.
* Maps of finite matroids across bipartite graphs.

## References

* [E. Aigner-Horev, J. Carmesin, J. Fröhlich, Infinite Matroid Union][aignerhorev2012infinite]
* [H. Perfect, Independence Spaces and Combinatorial Problems][perfect1969matroid]
* [J. Oxley, Matroid Theory][oxley2011]
-/

@[expose] public section

assert_not_exists Field

open Set Function Set.Notation
namespace Matroid
variable {α β : Type*} {f : α -> β} {E I : Set α} {M : Matroid α} {N : Matroid β}

section comap

/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (N : Matroid β) (f : α -> β)
  body: IndepMatroid.matroid
  { E := f ⁻¹' N.E
    Indep := fun I => N.Indep (f '' I) ∧ InjOn f I
    indep_empty := by simp
    indep_subset := fun _ _ h hIJ => ⟨h.1.subset (image_mono hIJ), InjOn.mono hIJ h.2⟩
    indep_aug := by
      rintro I B ⟨hI, hIinj⟩ hImax hBmax
      obtain ⟨I', hII', hI', hI'in

中文:
定义 comap
  签名: (N : 拟阵 β) (f : α -> β)
  定义体: IndepMatroid.matroid
  { E := f ⁻¹' N.E
    Indep := fun I => N.Indep (f '' I) ∧ InjOn f I
    indep_empty := by simp
    indep_subset := fun _ _ h hIJ => ⟨h.1.subset (image_mono hIJ), InjOn.mono hIJ h.2⟩
    indep_aug := by
      rintro I B ⟨hI, hIinj⟩ hImax hBmax
      obtain ⟨I', hII', hI', hI'in

Depends on / 依赖: IndepMatroid, IndepMatroid.matroid, InjOn.mono, IsBase, N.Indep, eq_of_subset_indep, hB.eq_of_subset_indep, h_im, image_eq_image_iff, image_mono, indep_aug, indep_empty, indep_subset, inj.image_eq_image_iff, matroid, not_maximal_subset_iff, subset
-/
def comap (N : Matroid β) (f : α -> β) : Matroid α :=
IndepMatroid.matroid
  { E := f ⁻¹' N.E
    Indep := fun I => N.Indep (f '' I) ∧ InjOn f I
    indep_empty := by simp
    indep_subset := fun _ _ h hIJ => ⟨h.1.subset (image_mono hIJ), InjOn.mono hIJ h.2⟩
    indep_aug := by
      rintro I B ⟨hI, hIinj⟩ hImax hBmax
      obtain ⟨I', hII', hI', hI'inj⟩ := (not_maximal_subset_iff ⟨hI, hIinj⟩).1 hImax
      have h₁ : ¬(N ↾ range f).IsBase (f '' I) := by
        refine fun hB => hII'.ne ?_
        have h_im := hB.eq_of_subset_indep (by simpa) (image_mono hII'.subset)
        rwa [hI'inj.image_eq_image_iff hII'.subset Subset.rfl] at h_im
      have h₂ : (N ↾ range f).IsBase (f '' B) := by
        refine Indep.isBase_of_forall_insert (by simpa using hBmax.1.1) ?_
        rintro _ ⟨⟨e, heB, rfl⟩, hfe⟩ hi
        rw [restrict_indep_iff]; rw [← image_insert_eq] at hi
        have hinj : InjOn f (insert e B) := by
          rw [injOn_insert (fun heB => hfe (mem_image_of_mem f heB))]
          exact ⟨hBmax.1.2, hfe⟩
        refine hBmax.not_prop_of_ssuperset (t := insert e B) (ssubset_insert ?_) ⟨hi.1, hinj⟩
exact fun heB => hfe mem_image_of_mem f heB
      obtain ⟨_, ⟨⟨e, he, rfl⟩, he'⟩, hei⟩ := Indep.exists_insert_of_not_isBase (by simpa) h₁ h₂
      have heI : e ∉ I := fun heI => he' (mem_image_of_mem f heI)
      rw [← image_insert_eq]; rw [restrict_indep_iff] at hei
      exact ⟨e, ⟨he, heI⟩, hei.1, (injOn_insert heI).2 ⟨hIinj, he'⟩⟩

    indep_maximal := by
      rintro X - I ⟨hI, hIinj⟩ hIX
      obtain ⟨J, hJ⟩ := (N ↾ range f).existsMaximalSubsetProperty_indep (f '' X) (by simp)
        (f '' I) (by simpa) (image_mono hIX)
      simp only [restrict_indep_iff, image_subset_iff, maximal_subset_iff, and_imp,
        and_assoc] at hJ ⊢
      obtain ⟨hIJ, hJ, hJf, hJX, hJmax⟩ := hJ
      obtain ⟨J₀, hIJ₀, hJ₀X, hbj⟩ := hIinj.bijOn_image.exists_extend_of_subset hIX
        (image_mono hIJ) (image_subset_iff.2 <| preimage_mono hJX)
      obtain rfl : f '' J₀ = J := by rw [← image_preimage_eq_of_subset hJf, hbj.image_eq]
      refine ⟨J₀, hIJ₀, hJ, hbj.injOn, hJ₀X, fun K hK hKinj hKX hJ₀K => ?_⟩
      rw [← hKinj.image_eq_image_iff hJ₀K Subset.rfl]; rw [hJmax hK (image_subset_range _ _)
        (image_mono hKX) (image_mono hJ₀K)]
    subset_ground := fun _ hI e heI => hI.1.subset_ground ⟨e, heI, rfl⟩ }

/--
lemma `comap_indep_iff` / 引理 `comap_indep_iff`

English:
lemma comap_indep_iff
  statement: (N.comap f).Indep I ↔ N.Indep (f '' I) ∧ InjOn f I
  proof: Iff.rfl

中文:
引理 comap_indep_iff
  结论: (N.comap f).Indep I ↔ N.Indep (f '' I) ∧ 单射限制 f I
  证明: Iff.rfl
-/
@[simp] lemma comap_indep_iff : (N.comap f).Indep I ↔ N.Indep (f '' I) ∧ InjOn f I := Iff.rfl

/--
lemma `comap_ground_eq` / 引理 `comap_ground_eq`

English:
lemma comap_ground_eq
  given: (N : Matroid β) (f : α -> β)
  statement: (N.comap f).E = f ⁻¹' N.E
  proof: rfl

中文:
引理 comap_ground_eq
  条件: (N : 拟阵 β) (f : α -> β)
  结论: (N.comap f).E = f ⁻¹' N.E
  证明: rfl
-/
@[simp] lemma comap_ground_eq (N : Matroid β) (f : α -> β) : (N.comap f).E = f ⁻¹' N.E := rfl

/--
lemma `comap_dep_iff` / 引理 `comap_dep_iff`

English:
lemma comap_dep_iff
  proof: by
  rw [Dep]; rw [comap_indep_iff]; rw [not_and]; rw [comap_ground_eq]; rw [Dep]; rw [image_subset_iff]
  refine ⟨by grind, ?_⟩
  rintro (⟨hI, hIE⟩ | hI)
  · exact ⟨fun h => (hI h).elim, hIE⟩
  rw [iff_true_intro hI.1]; rw [iff_true_intro hI.2]; rw [implies_true]; rw [true_and]
  simpa using hI.1.s

中文:
引理 comap_dep_iff
  证明: by
  rw [Dep]; rw [comap_indep_iff]; rw [not_and]; rw [comap_ground_eq]; rw [Dep]; rw [image_subset_iff]
  refine ⟨by grind, ?_⟩
  rintro (⟨hI, hIE⟩ | hI)
  · exact ⟨fun h => (hI h).elim, hIE⟩
  rw [iff_true_intro hI.1]; rw [iff_true_intro hI.2]; rw [implies_true]; rw [true_and]
  simpa using hI.1.s
-/
@[simp] lemma comap_dep_iff :
    (N.comap f).Dep I ↔ N.Dep (f '' I) ∨ (N.Indep (f '' I) ∧ ¬ InjOn f I) := by
  rw [Dep]; rw [comap_indep_iff]; rw [not_and]; rw [comap_ground_eq]; rw [Dep]; rw [image_subset_iff]
  refine ⟨by grind, ?_⟩
  rintro (⟨hI, hIE⟩ | hI)
  · exact ⟨fun h => (hI h).elim, hIE⟩
  rw [iff_true_intro hI.1]; rw [iff_true_intro hI.2]; rw [implies_true]; rw [true_and]
  simpa using hI.1.subset_ground

/--
lemma `comap_id` / 引理 `comap_id`

English:
lemma comap_id
  given: (N : Matroid β)
  statement: N.comap id = N
  proof: ext_indep rfl by simp [injective_id.injOn]

中文:
引理 comap_id
  条件: (N : 拟阵 β)
  结论: N.comap id = N
  证明: ext_indep rfl by simp [injective_id.injOn]
-/
@[simp] lemma comap_id (N : Matroid β) : N.comap id = N :=
ext_indep rfl by simp [injective_id.injOn]

/--
lemma `comap_indep_iff_of_injOn` / 引理 `comap_indep_iff_of_injOn`

English:
lemma comap_indep_iff_of_injOn
  given: (hf : InjOn f (f ⁻¹' N.E))
  proof: by
  rw [comap_indep_iff]; rw [and_iff_left_iff_imp]
refine fun hi => hf.mono subset_trans ?_ (preimage_mono hi.subset_ground)
  apply subset_preimage_image

中文:
引理 comap_indep_iff_of_injOn
  条件: (hf : 单射限制 f (f ⁻¹' N.E))
  证明: by
  rw [comap_indep_iff]; rw [and_iff_left_iff_imp]
refine fun hi => hf.mono subset_trans ?_ (preimage_mono hi.subset_ground)
  apply subset_preimage_image

Depends on / 依赖: and_iff_left_iff_imp, comap_indep_iff, hf.mono, hi.subset_ground, preimage_mono, subset_ground, subset_preimage_image, subset_trans
-/
lemma comap_indep_iff_of_injOn (hf : InjOn f (f ⁻¹' N.E)) :
    (N.comap f).Indep I ↔ N.Indep (f '' I) := by
  rw [comap_indep_iff]; rw [and_iff_left_iff_imp]
refine fun hi => hf.mono subset_trans ?_ (preimage_mono hi.subset_ground)
  apply subset_preimage_image

/--
lemma `comap_emptyOn` / 引理 `comap_emptyOn`

English:
lemma comap_emptyOn
  given: (f : α -> β)
  statement: comap (emptyOn β) f = emptyOn α
  proof: by
  simp [← ground_eq_empty_iff]

中文:
引理 comap_emptyOn
  条件: (f : α -> β)
  结论: comap (emptyOn β) f = emptyOn α
  证明: by
  simp [← ground_eq_empty_iff]
-/
@[simp] lemma comap_emptyOn (f : α -> β) : comap (emptyOn β) f = emptyOn α := by
  simp [← ground_eq_empty_iff]

/--
lemma `comap_loopyOn` / 引理 `comap_loopyOn`

English:
lemma comap_loopyOn
  given: (f : α -> β) (E : Set β)
  statement: comap (loopyOn E) f = loopyOn (f ⁻¹' E)
  proof: by
  rw [eq_loopyOn_iff]; aesop

中文:
引理 comap_loopyOn
  条件: (f : α -> β) (E : 集合 β)
  结论: comap (loopyOn E) f = loopyOn (f ⁻¹' E)
  证明: by
  rw [eq_loopyOn_iff]; aesop
-/
@[simp] lemma comap_loopyOn (f : α -> β) (E : Set β) : comap (loopyOn E) f = loopyOn (f ⁻¹' E) := by
  rw [eq_loopyOn_iff]; aesop

/--
lemma `comap_isBasis_iff` / 引理 `comap_isBasis_iff`

English:
lemma comap_isBasis_iff
  given: {I X : Set α}
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨hI, hinj⟩ := comap_indep_iff.1 h.indep
    refine ⟨hI.isBasis_of_forall_insert (image_mono h.subset) fun e he => ?_, hinj, h.subset⟩
    simp only [mem_sdiff, mem_image, not_exists, not_and] at he
    obtain ⟨⟨e, heX, rfl⟩, he⟩ := he
    have heI : 

中文:
引理 comap_isBasis_iff
  条件: {I X : 集合 α}
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨hI, hinj⟩ := comap_indep_iff.1 h.indep
    refine ⟨hI.isBasis_of_forall_insert (image_mono h.subset) fun e he => ?_, hinj, h.subset⟩
    simp only [mem_sdiff, mem_image, not_exists, not_and] at he
    obtain ⟨⟨e, heX, rfl⟩, he⟩ := he
    have heI : 
-/
@[simp] lemma comap_isBasis_iff {I X : Set α} :
    (N.comap f).IsBasis I X ↔ N.IsBasis (f '' I) (f '' X) ∧ I.InjOn f ∧ I subseteq X := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨hI, hinj⟩ := comap_indep_iff.1 h.indep
    refine ⟨hI.isBasis_of_forall_insert (image_mono h.subset) fun e he => ?_, hinj, h.subset⟩
    simp only [mem_sdiff, mem_image, not_exists, not_and] at he
    obtain ⟨⟨e, heX, rfl⟩, he⟩ := he
    have heI : e ∉ I := fun heI => (he e heI rfl)
    replace h := h.insert_dep ⟨heX, heI⟩
    simp only [comap_dep_iff, image_insert_eq, or_iff_not_imp_right, injOn_insert heI,
      hinj, mem_image, not_exists, not_and, true_and, not_forall, not_not] at h
    exact h (fun _ => he)
  refine Indep.isBasis_of_forall_insert ?_ h.2.2 fun e ⟨heX, heI⟩ => ?_
  · simp [comap_indep_iff, h.1.indep, h.2]
  have hIE : insert e I subseteq (N.comap f).E := by
      simp_rw [comap_ground_eq, ← image_subset_iff]
      exact (image_mono (insert_subset heX h.2.2)).trans h.1.subset_ground
  suffices N.Indep (insert (f e) (f '' I)) -> exists x in I, f x = f e
    by simpa [← not_indep_iff hIE, injOn_insert heI, h.2.1, image_insert_eq]
  exact h.1.mem_of_insert_indep (mem_image_of_mem f heX)

/--
lemma `comap_isBase_iff` / 引理 `comap_isBase_iff`

English:
lemma comap_isBase_iff
  given: {B : Set α}
  proof: by
  rw [← isBasis_ground_iff]; rw [comap_isBasis_iff]; rfl

中文:
引理 comap_isBase_iff
  条件: {B : 集合 α}
  证明: by
  rw [← isBasis_ground_iff]; rw [comap_isBasis_iff]; rfl
-/
@[simp] lemma comap_isBase_iff {B : Set α} :
    (N.comap f).IsBase B ↔ N.IsBasis (f '' B) (f '' f ⁻¹' N.E) ∧ B.InjOn f ∧ B subseteq f ⁻¹' N.E := by
  rw [← isBasis_ground_iff]; rw [comap_isBasis_iff]; rfl

/--
lemma `comap_isBasis'_iff` / 引理 `comap_isBasis'_iff`

English:
lemma comap_isBasis'_iff
  given: {I X : Set α}
  proof: by
  simp only [isBasis'_iff_isBasis_inter_ground, comap_ground_eq, comap_isBasis_iff,
    image_inter_preimage, subset_inter_iff, ← and_assoc, and_iff_left_iff_imp,
    and_imp]
  exact fun h _ _ => (image_subset_iff.1 h.indep.subset_ground)

中文:
引理 comap_isBasis'_iff
  条件: {I X : 集合 α}
  证明: by
  simp only [isBasis'_iff_isBasis_inter_ground, comap_ground_eq, comap_isBasis_iff,
    image_inter_preimage, subset_inter_iff, ← and_assoc, and_iff_left_iff_imp,
    and_imp]
  exact fun h _ _ => (image_subset_iff.1 h.indep.subset_ground)
-/
@[simp] lemma comap_isBasis'_iff {I X : Set α} :
    (N.comap f).IsBasis' I X ↔ N.IsBasis' (f '' I) (f '' X) ∧ I.InjOn f ∧ I subseteq X := by
  simp only [isBasis'_iff_isBasis_inter_ground, comap_ground_eq, comap_isBasis_iff,
    image_inter_preimage, subset_inter_iff, ← and_assoc, and_iff_left_iff_imp,
    and_imp]
  exact fun h _ _ => (image_subset_iff.1 h.indep.subset_ground)

/--
Instance `comap_finitary` / 实例 `comap_finitary`

English:
instance comap_finitary
  signature: (N : Matroid β) [N.Finitary] (f : α -> β)
  body: by
  refine ⟨fun I hI => ?_⟩
  rw [comap_indep_iff]; rw [indep_iff_forall_finite_subset_indep]
  simp only [forall_subset_image_iff]
  refine ⟨fun J hJ hfin => ?_,
    fun x hx y hy => (hI _ (pair_subset hx hy) (by simp)).2 (by simp) (by simp)⟩
  obtain ⟨J', hJ'J, hJ'⟩ := (surjOn_image f J).exists_b

中文:
实例 comap_finitary
  签名: (N : 拟阵 β) [N.Finitary] (f : α -> β)
  定义体: by
  refine ⟨fun I hI => ?_⟩
  rw [comap_indep_iff]; rw [indep_iff_forall_finite_subset_indep]
  simp only [forall_subset_image_iff]
  refine ⟨fun J hJ hfin => ?_,
    fun x hx y hy => (hI _ (pair_subset hx hy) (by simp)).2 (by simp) (by simp)⟩
  obtain ⟨J', hJ'J, hJ'⟩ := (surjOn_image f J).exists_b

Depends on / 依赖: J.trans, comap_indep_iff, exists_bijOn_subset, forall_subset_image_iff, hfin.of_finite_image, image_eq, indep_iff_forall_finite_subset_indep, of_finite_image, pair_subset, surjOn_image
-/
instance comap_finitary (N : Matroid β) [N.Finitary] (f : α -> β) : (N.comap f).Finitary := by
  refine ⟨fun I hI => ?_⟩
  rw [comap_indep_iff]; rw [indep_iff_forall_finite_subset_indep]
  simp only [forall_subset_image_iff]
  refine ⟨fun J hJ hfin => ?_,
    fun x hx y hy => (hI _ (pair_subset hx hy) (by simp)).2 (by simp) (by simp)⟩
  obtain ⟨J', hJ'J, hJ'⟩ := (surjOn_image f J).exists_bijOn_subset
  rw [← hJ'.image_eq] at hfin ⊢
  exact (hI J' (hJ'J.trans hJ) (hfin.of_finite_image hJ'.injOn)).1

/--
Instance `comap_rankFinite` / 实例 `comap_rankFinite`

English:
instance comap_rankFinite
  signature: (N : Matroid β) [N.RankFinite] (f : α -> β)
  body: by
  obtain ⟨B, hB⟩ := (N.comap f).exists_isBase
  refine hB.rankFinite_of_finite ?_
  simp only [comap_isBase_iff] at hB
  exact (hB.1.indep.finite.of_finite_image hB.2.1)

中文:
实例 comap_rankFinite
  签名: (N : 拟阵 β) [N.RankFinite] (f : α -> β)
  定义体: by
  obtain ⟨B, hB⟩ := (N.comap f).exists_isBase
  refine hB.rankFinite_of_finite ?_
  simp only [comap_isBase_iff] at hB
  exact (hB.1.indep.finite.of_finite_image hB.2.1)

Depends on / 依赖: N.comap, comap_isBase_iff, exists_isBase, finite, hB.rankFinite_of_finite, indep.finite.of_finite_image, of_finite_image, rankFinite_of_finite
-/
instance comap_rankFinite (N : Matroid β) [N.RankFinite] (f : α -> β) : (N.comap f).RankFinite := by
  obtain ⟨B, hB⟩ := (N.comap f).exists_isBase
  refine hB.rankFinite_of_finite ?_
  simp only [comap_isBase_iff] at hB
  exact (hB.1.indep.finite.of_finite_image hB.2.1)

end comap

section comapOn

variable {E B I : Set α}

/--
Definition of `comapOn` / `comapOn` 的定义

English:
definition comapOn
  signature: (N : Matroid β) (E : Set α) (f : α -> β)
  body: (N.comap f) ↾ E

中文:
定义 comapOn
  签名: (N : 拟阵 β) (E : 集合 α) (f : α -> β)
  定义体: (N.comap f) ↾ E

Depends on / 依赖: N.comap
-/
def comapOn (N : Matroid β) (E : Set α) (f : α -> β) : Matroid α := (N.comap f) ↾ E

/--
lemma `comapOn_preimage_eq` / 引理 `comapOn_preimage_eq`

English:
lemma comapOn_preimage_eq
  given: (N : Matroid β) (f : α -> β)
  statement: N.comapOn (f ⁻¹' N.E) f = N.comap f
  proof: by
  rw [comapOn]; rw [restrict_eq_self_iff]; rfl

中文:
引理 comapOn_preimage_eq
  条件: (N : 拟阵 β) (f : α -> β)
  结论: N.comapOn (f ⁻¹' N.E) f = N.comap f
  证明: by
  rw [comapOn]; rw [restrict_eq_self_iff]; rfl

Depends on / 依赖: comapOn, restrict_eq_self_iff
-/
lemma comapOn_preimage_eq (N : Matroid β) (f : α -> β) : N.comapOn (f ⁻¹' N.E) f = N.comap f := by
  rw [comapOn]; rw [restrict_eq_self_iff]; rfl

/--
lemma `comapOn_indep_iff` / 引理 `comapOn_indep_iff`

English:
lemma comapOn_indep_iff
  proof: by
  simp [comapOn, and_assoc]

中文:
引理 comapOn_indep_iff
  证明: by
  simp [comapOn, and_assoc]
-/
@[simp] lemma comapOn_indep_iff :
    (N.comapOn E f).Indep I ↔ (N.Indep (f '' I) ∧ InjOn f I ∧ I subseteq E) := by
  simp [comapOn, and_assoc]

/--
lemma `comapOn_ground_eq` / 引理 `comapOn_ground_eq`

English:
lemma comapOn_ground_eq
  statement: (N.comapOn E f).E = E
  proof: rfl

中文:
引理 comapOn_ground_eq
  结论: (N.comapOn E f).E = E
  证明: rfl
-/
@[simp] lemma comapOn_ground_eq : (N.comapOn E f).E = E := rfl

/--
lemma `comapOn_isBase_iff` / 引理 `comapOn_isBase_iff`

English:
lemma comapOn_isBase_iff
  proof: by
  rw [comapOn]; rw [isBase_restrict_iff']; rw [comap_isBasis'_iff]

中文:
引理 comapOn_isBase_iff
  证明: by
  rw [comapOn]; rw [isBase_restrict_iff']; rw [comap_isBasis'_iff]

Depends on / 依赖: _iff, comapOn, comap_isBasis, isBase_restrict_iff
-/
lemma comapOn_isBase_iff :
    (N.comapOn E f).IsBase B ↔ N.IsBasis' (f '' B) (f '' E) ∧ B.InjOn f ∧ B subseteq E := by
  rw [comapOn]; rw [isBase_restrict_iff']; rw [comap_isBasis'_iff]

/--
lemma `comapOn_isBase_iff_of_surjOn` / 引理 `comapOn_isBase_iff_of_surjOn`

English:
lemma comapOn_isBase_iff_of_surjOn
  given: (h : SurjOn f E N.E)
  proof: by
  simp_rw [comapOn_isBase_iff, and_congr_left_iff, and_imp, isBasis'_iff_isBasis_inter_ground,
    inter_eq_self_of_subset_right h, isBasis_ground_iff, implies_true]

中文:
引理 comapOn_isBase_iff_of_surjOn
  条件: (h : 满射限制 f E N.E)
  证明: by
  simp_rw [comapOn_isBase_iff, and_congr_left_iff, and_imp, isBasis'_iff_isBasis_inter_ground,
    inter_eq_self_of_subset_right h, isBasis_ground_iff, implies_true]

Depends on / 依赖: _iff_isBasis_inter_ground, and_congr_left_iff, and_imp, comapOn_isBase_iff, implies_true, inter_eq_self_of_subset_right, isBasis, isBasis_ground_iff, simp_rw
-/
lemma comapOn_isBase_iff_of_surjOn (h : SurjOn f E N.E) :
    (N.comapOn E f).IsBase B ↔ (N.IsBase (f '' B) ∧ InjOn f B ∧ B subseteq E) := by
  simp_rw [comapOn_isBase_iff, and_congr_left_iff, and_imp, isBasis'_iff_isBasis_inter_ground,
    inter_eq_self_of_subset_right h, isBasis_ground_iff, implies_true]

/--
lemma `comapOn_isBase_iff_of_bijOn` / 引理 `comapOn_isBase_iff_of_bijOn`

English:
lemma comapOn_isBase_iff_of_bijOn
  given: (h : BijOn f E N.E)
  proof: by
  rw [← and_iff_left_of_imp (IsBase.subset_ground (M := N.comapOn E f) (B := B))]; rw [comapOn_ground_eq]; rw [and_congr_left_iff]
  suffices h' : B subseteq E -> InjOn f B from fun hB =>
    by simp [hB, comapOn_isBase_iff_of_surjOn h.surjOn, h']
  exact fun hBE => h.injOn.mono hBE

中文:
引理 comapOn_isBase_iff_of_bijOn
  条件: (h : 双射限制 f E N.E)
  证明: by
  rw [← and_iff_left_of_imp (IsBase.subset_ground (M := N.comapOn E f) (B := B))]; rw [comapOn_ground_eq]; rw [and_congr_left_iff]
  suffices h' : B subseteq E -> InjOn f B from fun hB =>
    by simp [hB, comapOn_isBase_iff_of_surjOn h.surjOn, h']
  exact fun hBE => h.injOn.mono hBE

Depends on / 依赖: IsBase, IsBase.subset_ground, N.comapOn, and_congr_left_iff, and_iff_left_of_imp, comapOn, comapOn_ground_eq, comapOn_isBase_iff_of_surjOn, h.injOn.mono, h.surjOn, subset_ground, subseteq, surjOn
-/
lemma comapOn_isBase_iff_of_bijOn (h : BijOn f E N.E) :
    (N.comapOn E f).IsBase B ↔ N.IsBase (f '' B) ∧ B subseteq E := by
  rw [← and_iff_left_of_imp (IsBase.subset_ground (M := N.comapOn E f) (B := B))]; rw [comapOn_ground_eq]; rw [and_congr_left_iff]
  suffices h' : B subseteq E -> InjOn f B from fun hB =>
    by simp [hB, comapOn_isBase_iff_of_surjOn h.surjOn, h']
  exact fun hBE => h.injOn.mono hBE

/--
lemma `comapOn_dual_eq_of_bijOn` / 引理 `comapOn_dual_eq_of_bijOn`

English:
lemma comapOn_dual_eq_of_bijOn
  given: (h : BijOn f E N.E)
  proof: by
  refine ext_isBase (by simp) (fun B hB => ?_)
  rw [comapOn_isBase_iff_of_bijOn (by simpa)]; rw [dual_isBase_iff]; rw [comapOn_isBase_iff_of_bijOn h]; rw [dual_isBase_iff _]; rw [comapOn_ground_eq]; rw [and_iff_left sdiff_subset]; rw [and_iff_left (by simpa)]; rw [h.injOn.image_sdiff_subset (by 

中文:
引理 comapOn_dual_eq_of_bijOn
  条件: (h : 双射限制 f E N.E)
  证明: by
  refine ext_isBase (by simp) (fun B hB => ?_)
  rw [comapOn_isBase_iff_of_bijOn (by simpa)]; rw [dual_isBase_iff]; rw [comapOn_isBase_iff_of_bijOn h]; rw [dual_isBase_iff _]; rw [comapOn_ground_eq]; rw [and_iff_left sdiff_subset]; rw [and_iff_left (by simpa)]; rw [h.injOn.image_sdiff_subset (by 

Depends on / 依赖: and_iff_left, comapOn_ground_eq, comapOn_isBase_iff_of_bijOn, dual_isBase_iff, ext_isBase, h.image_eq, h.injOn.image_sdiff_subset, h.mapsTo.mono_left, image_eq, image_sdiff_subset, image_subset, mapsTo, mono_left, sdiff_subset, subseteq
-/
lemma comapOn_dual_eq_of_bijOn (h : BijOn f E N.E) :
    (N.comapOn E f)✶ = N✶.comapOn E f := by
  refine ext_isBase (by simp) (fun B hB => ?_)
  rw [comapOn_isBase_iff_of_bijOn (by simpa)]; rw [dual_isBase_iff]; rw [comapOn_isBase_iff_of_bijOn h]; rw [dual_isBase_iff _]; rw [comapOn_ground_eq]; rw [and_iff_left sdiff_subset]; rw [and_iff_left (by simpa)]; rw [h.injOn.image_sdiff_subset (by simpa)]; rw [h.image_eq]
  exact (h.mapsTo.mono_left (show B subseteq E by simpa)).image_subset

/--
Instance `comapOn_finitary` / 实例 `comapOn_finitary`

English:
instance comapOn_finitary
  signature: [N.Finitary]
  body: by
  rw [comapOn]; infer_instance

中文:
实例 comapOn_finitary
  签名: [N.Finitary]
  定义体: by
  rw [comapOn]; infer_instance

Depends on / 依赖: comapOn, infer_instance
-/
instance comapOn_finitary [N.Finitary] : (N.comapOn E f).Finitary := by
  rw [comapOn]; infer_instance

/--
Instance `comapOn_rankFinite` / 实例 `comapOn_rankFinite`

English:
instance comapOn_rankFinite
  signature: [N.RankFinite]
  body: by
  rw [comapOn]; infer_instance

中文:
实例 comapOn_rankFinite
  签名: [N.RankFinite]
  定义体: by
  rw [comapOn]; infer_instance

Depends on / 依赖: comapOn, infer_instance
-/
instance comapOn_rankFinite [N.RankFinite] : (N.comapOn E f).RankFinite := by
  rw [comapOn]; infer_instance

end comapOn
section mapSetEmbedding

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `mapSetEmbedding` / `mapSetEmbedding` 的定义

English:
definition mapSetEmbedding
  signature: (M : Matroid α) (f : M.E ↪ β)
  body: Matroid.ofExistsMatroid
  (E := range f)
  (Indep := fun I => M.Indep ↑(f ⁻¹' I) ∧ I subseteq range f)
  (hM := by
    obtain (rfl | ⟨⟨e, he⟩⟩) := eq_emptyOn_or_nonempty M
    · refine ⟨emptyOn β, ?_⟩
      simp only [emptyOn_ground] at f
      simp [range_eq_empty f, subset_empty_iff]
    have _ : 

中文:
定义 mapSetEmbedding
  签名: (M : 拟阵 α) (f : M.E ↪ β)
  定义体: Matroid.ofExistsMatroid
  (E := range f)
  (Indep := fun I => M.Indep ↑(f ⁻¹' I) ∧ I subseteq range f)
  (hM := by
    obtain (rfl | ⟨⟨e, he⟩⟩) := eq_emptyOn_or_nonempty M
    · refine ⟨emptyOn β, ?_⟩
      simp only [emptyOn_ground] at f
      simp [range_eq_empty f, subset_empty_iff]
    have _ : 

Depends on / 依赖: Matroid, Matroid.ofExistsMatroid, ofExistsMatroid
-/
def mapSetEmbedding (M : Matroid α) (f : M.E ↪ β) : Matroid β := Matroid.ofExistsMatroid
  (E := range f)
  (Indep := fun I => M.Indep ↑(f ⁻¹' I) ∧ I subseteq range f)
  (hM := by
    obtain (rfl | ⟨⟨e, he⟩⟩) := eq_emptyOn_or_nonempty M
    · refine ⟨emptyOn β, ?_⟩
      simp only [emptyOn_ground] at f
      simp [range_eq_empty f, subset_empty_iff]
    have _ : Nonempty M.E := ⟨⟨e,he⟩⟩
    have _ : Nonempty α := ⟨e⟩
    refine ⟨M.comapOn (range f) (fun x => ↑(invFunOn f univ x)), rfl, ?_⟩
    simp_rw [comapOn_indep_iff, ← and_assoc, and_congr_left_iff, subset_range_iff_exists_image_eq]
    rintro _ ⟨I, rfl⟩
    rw [← image_image]; rw [InjOn.invFunOn_image f.injective.injOn (subset_univ _)]; rw [preimage_image_eq _ f.injective]; rw [and_iff_left_iff_imp]
    rintro - x hx y hy
    simp only [Subtype.val_inj]
    exact (invFunOn_injOn_image f univ) (image_mono (subset_univ I) hx)
      (image_mono (subset_univ I) hy))

/--
lemma `mapSetEmbedding_ground` / 引理 `mapSetEmbedding_ground`

English:
lemma mapSetEmbedding_ground
  given: (M : Matroid α) (f : M.E ↪ β)
  proof: rfl

中文:
引理 mapSetEmbedding_ground
  条件: (M : 拟阵 α) (f : M.E ↪ β)
  证明: rfl
-/
@[simp] lemma mapSetEmbedding_ground (M : Matroid α) (f : M.E ↪ β) :
    (M.mapSetEmbedding f).E = range f := rfl

/--
lemma `mapSetEmbedding_indep_iff` / 引理 `mapSetEmbedding_indep_iff`

English:
lemma mapSetEmbedding_indep_iff
  given: {f : M.E ↪ β} {I : Set β}
  proof: Iff.rfl

中文:
引理 mapSetEmbedding_indep_iff
  条件: {f : M.E ↪ β} {I : 集合 β}
  证明: Iff.rfl
-/
@[simp] lemma mapSetEmbedding_indep_iff {f : M.E ↪ β} {I : Set β} :
    (M.mapSetEmbedding f).Indep I ↔ M.Indep ↑(f ⁻¹' I) ∧ I subseteq range f := Iff.rfl

/--
lemma `Indep.exists_eq_image_of_mapSetEmbedding` / 引理 `Indep.exists_eq_image_of_mapSetEmbedding`

English:
lemma Indep.exists_eq_image_of_mapSetEmbedding
  statement: {f : M.E ↪ β} {I : Set β}
  proof: ⟨f ⁻¹' I, hI.1, Eq.symm image_preimage_eq_of_subset hI.2⟩

中文:
引理 Indep.存在_eq_image_of_mapSetEmbedding
  结论: {f : M.E ↪ β} {I : 集合 β}
  证明: ⟨f ⁻¹' I, hI.1, Eq.symm image_preimage_eq_of_subset hI.2⟩

Depends on / 依赖: Eq.symm, image_preimage_eq_of_subset
-/
lemma Indep.exists_eq_image_of_mapSetEmbedding {f : M.E ↪ β} {I : Set β}
    (hI : (M.mapSetEmbedding f).Indep I) : exists (I₀ : Set M.E), M.Indep I₀ ∧ I = f '' I₀ :=
⟨f ⁻¹' I, hI.1, Eq.symm image_preimage_eq_of_subset hI.2⟩

/--
lemma `mapSetEmbedding_indep_iff'` / 引理 `mapSetEmbedding_indep_iff'`

English:
lemma mapSetEmbedding_indep_iff'
  given: {f : M.E ↪ β} {I : Set β}
  proof: by
  simp only [mapSetEmbedding_indep_iff, subset_range_iff_exists_image_eq]
  constructor
  · rintro ⟨hI, I, rfl⟩
    exact ⟨I, by rwa [preimage_image_eq _ f.injective] at hI, rfl⟩
  rintro ⟨I, hI, rfl⟩
  rw [preimage_image_eq _ f.injective]
  exact ⟨hI, _, rfl⟩

中文:
引理 mapSetEmbedding_indep_iff'
  条件: {f : M.E ↪ β} {I : 集合 β}
  证明: by
  simp only [mapSetEmbedding_indep_iff, subset_range_iff_exists_image_eq]
  constructor
  · rintro ⟨hI, I, rfl⟩
    exact ⟨I, by rwa [preimage_image_eq _ f.injective] at hI, rfl⟩
  rintro ⟨I, hI, rfl⟩
  rw [preimage_image_eq _ f.injective]
  exact ⟨hI, _, rfl⟩

Depends on / 依赖: f.injective, injective, mapSetEmbedding_indep_iff, preimage_image_eq, subset_range_iff_exists_image_eq
-/
lemma mapSetEmbedding_indep_iff' {f : M.E ↪ β} {I : Set β} :
    (M.mapSetEmbedding f).Indep I ↔ exists (I₀ : Set M.E), M.Indep ↑I₀ ∧ I = f '' I₀ := by
  simp only [mapSetEmbedding_indep_iff, subset_range_iff_exists_image_eq]
  constructor
  · rintro ⟨hI, I, rfl⟩
    exact ⟨I, by rwa [preimage_image_eq _ f.injective] at hI, rfl⟩
  rintro ⟨I, hI, rfl⟩
  rw [preimage_image_eq _ f.injective]
  exact ⟨hI, _, rfl⟩

end mapSetEmbedding

section map

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (M : Matroid α) (f : α -> β) (hf : InjOn f M.E)
  body: Matroid.ofExistsMatroid
  (E := f '' M.E)
  (Indep := fun I => exists I₀, M.Indep I₀ ∧ I = f '' I₀)
  (hM := by
    refine ⟨M.mapSetEmbedding ⟨_, hf.injective⟩, by simp, fun I => ?_⟩
    simp_rw [mapSetEmbedding_indep_iff', Embedding.coeFn_mk, domRestrict_apply,
      ← image_image f Subtype.val, Su

中文:
定义 map
  签名: (M : 拟阵 α) (f : α -> β) (hf : 单射限制 f M.E)
  定义体: Matroid.ofExistsMatroid
  (E := f '' M.E)
  (Indep := fun I => exists I₀, M.Indep I₀ ∧ I = f '' I₀)
  (hM := by
    refine ⟨M.mapSetEmbedding ⟨_, hf.injective⟩, by simp, fun I => ?_⟩
    simp_rw [mapSetEmbedding_indep_iff', Embedding.coeFn_mk, domRestrict_apply,
      ← image_image f Subtype.val, Su

Depends on / 依赖: Matroid, Matroid.ofExistsMatroid, ofExistsMatroid
-/
def map (M : Matroid α) (f : α -> β) (hf : InjOn f M.E) : Matroid β := Matroid.ofExistsMatroid
  (E := f '' M.E)
  (Indep := fun I => exists I₀, M.Indep I₀ ∧ I = f '' I₀)
  (hM := by
    refine ⟨M.mapSetEmbedding ⟨_, hf.injective⟩, by simp, fun I => ?_⟩
    simp_rw [mapSetEmbedding_indep_iff', Embedding.coeFn_mk, domRestrict_apply,
      ← image_image f Subtype.val, Subtype.exists_set_subtype (p := fun J => M.Indep J ∧ I = f '' J)]
    exact ⟨fun ⟨I₀, _, hI₀⟩ => ⟨I₀, hI₀⟩, fun ⟨I₀, hI₀⟩ => ⟨I₀, hI₀.1.subset_ground, hI₀⟩⟩)

/--
lemma `map_ground` / 引理 `map_ground`

English:
lemma map_ground
  given: (M : Matroid α) (f : α -> β) (hf)
  statement: (M.map f hf).E = f '' M.E
  proof: rfl

中文:
引理 map_ground
  条件: (M : 拟阵 α) (f : α -> β) (hf)
  结论: (M.map f hf).E = f '' M.E
  证明: rfl
-/
@[simp] lemma map_ground (M : Matroid α) (f : α -> β) (hf) : (M.map f hf).E = f '' M.E := rfl

/--
lemma `map_indep_iff` / 引理 `map_indep_iff`

English:
lemma map_indep_iff
  given: {hf} {I : Set β}
  proof: Iff.rfl

中文:
引理 map_indep_iff
  条件: {hf} {I : 集合 β}
  证明: Iff.rfl
-/
@[simp] lemma map_indep_iff {hf} {I : Set β} :
    (M.map f hf).Indep I ↔ exists I₀, M.Indep I₀ ∧ I = f '' I₀ := Iff.rfl

/--
lemma `Indep.map` / 引理 `Indep.map`

English:
lemma Indep.map
  given: (hI : M.Indep I) (f : α -> β) (hf)
  statement: (M.map f hf).Indep (f '' I)
  proof: map_indep_iff.2 ⟨I, hI, rfl⟩

中文:
引理 Indep.map
  条件: (hI : M.Indep I) (f : α -> β) (hf)
  结论: (M.map f hf).Indep (f '' I)
  证明: map_indep_iff.2 ⟨I, hI, rfl⟩

Depends on / 依赖: map_indep_iff
-/
lemma Indep.map (hI : M.Indep I) (f : α -> β) (hf) : (M.map f hf).Indep (f '' I) :=
  map_indep_iff.2 ⟨I, hI, rfl⟩

/--
lemma `Indep.exists_bijOn_of_map` / 引理 `Indep.exists_bijOn_of_map`

English:
lemma Indep.exists_bijOn_of_map
  given: {I : Set β} (hf) (hI : (M.map f hf).Indep I)
  proof: by
  obtain ⟨I₀, hI₀, rfl⟩ := hI
  exact ⟨I₀, hI₀, (hf.mono hI₀.subset_ground).bijOn_image⟩

中文:
引理 Indep.存在_bijOn_of_map
  条件: {I : 集合 β} (hf) (hI : (M.map f hf).Indep I)
  证明: by
  obtain ⟨I₀, hI₀, rfl⟩ := hI
  exact ⟨I₀, hI₀, (hf.mono hI₀.subset_ground).bijOn_image⟩

Depends on / 依赖: bijOn_image, hf.mono, subset_ground
-/
lemma Indep.exists_bijOn_of_map {I : Set β} (hf) (hI : (M.map f hf).Indep I) :
    exists I₀, M.Indep I₀ ∧ BijOn f I₀ I := by
  obtain ⟨I₀, hI₀, rfl⟩ := hI
  exact ⟨I₀, hI₀, (hf.mono hI₀.subset_ground).bijOn_image⟩

/--
lemma `map_image_indep_iff` / 引理 `map_image_indep_iff`

English:
lemma map_image_indep_iff
  given: {hf} {I : Set α} (hI : I subseteq M.E)
  proof: by
  rw [map_indep_iff]
  refine ⟨fun ⟨J, hJ, hIJ⟩ => ?_, fun h => ⟨I, h, rfl⟩⟩
  rw [hf.image_eq_image_iff hI hJ.subset_ground] at hIJ; rwa [hIJ]

中文:
引理 map_image_indep_iff
  条件: {hf} {I : 集合 α} (hI : I subseteq M.E)
  证明: by
  rw [map_indep_iff]
  refine ⟨fun ⟨J, hJ, hIJ⟩ => ?_, fun h => ⟨I, h, rfl⟩⟩
  rw [hf.image_eq_image_iff hI hJ.subset_ground] at hIJ; rwa [hIJ]

Depends on / 依赖: hJ.subset_ground, hf.image_eq_image_iff, image_eq_image_iff, map_indep_iff, subset_ground
-/
lemma map_image_indep_iff {hf} {I : Set α} (hI : I subseteq M.E) :
    (M.map f hf).Indep (f '' I) ↔ M.Indep I := by
  rw [map_indep_iff]
  refine ⟨fun ⟨J, hJ, hIJ⟩ => ?_, fun h => ⟨I, h, rfl⟩⟩
  rw [hf.image_eq_image_iff hI hJ.subset_ground] at hIJ; rwa [hIJ]

/--
lemma `map_isBase_iff` / 引理 `map_isBase_iff`

English:
lemma map_isBase_iff
  given: (M : Matroid α) (f : α -> β) (hf) {B : Set β}
  proof: by
  rw [isBase_iff_maximal_indep]
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨B₀, hB₀, hbij⟩ := h.prop.exists_bijOn_of_map
    refine ⟨B₀, hB₀.isBase_of_maximal fun J hJ hB₀J => ?_, hbij.image_eq.symm⟩
    rw [← hf.image_eq_image_iff hB₀.subset_ground hJ.subset_ground]; rw [hbij.image_eq]
    exact h.eq

中文:
引理 map_isBase_iff
  条件: (M : 拟阵 α) (f : α -> β) (hf) {B : 集合 β}
  证明: by
  rw [isBase_iff_maximal_indep]
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨B₀, hB₀, hbij⟩ := h.prop.exists_bijOn_of_map
    refine ⟨B₀, hB₀.isBase_of_maximal fun J hJ hB₀J => ?_, hbij.image_eq.symm⟩
    rw [← hf.image_eq_image_iff hB₀.subset_ground hJ.subset_ground]; rw [hbij.image_eq]
    exact h.eq
-/
@[simp] lemma map_isBase_iff (M : Matroid α) (f : α -> β) (hf) {B : Set β} :
    (M.map f hf).IsBase B ↔ exists B₀, M.IsBase B₀ ∧ B = f '' B₀ := by
  rw [isBase_iff_maximal_indep]
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨B₀, hB₀, hbij⟩ := h.prop.exists_bijOn_of_map
    refine ⟨B₀, hB₀.isBase_of_maximal fun J hJ hB₀J => ?_, hbij.image_eq.symm⟩
    rw [← hf.image_eq_image_iff hB₀.subset_ground hJ.subset_ground]; rw [hbij.image_eq]
    exact h.eq_of_subset (hJ.map f hf) (hbij.image_eq ▸ image_mono hB₀J)
  rintro ⟨B, hB, rfl⟩
  rw [maximal_subset_iff]
  refine ⟨hB.indep.map f hf, fun I hI hBI => ?_⟩
  obtain ⟨I₀, hI₀, hbij⟩ := hI.exists_bijOn_of_map
  rw [← hbij.image_eq]; rw [hf.image_subset_image_iff hB.subset_ground hI₀.subset_ground] at hBI
  rw [hB.eq_of_subset_indep hI₀ hBI]; rw [hbij.image_eq]

/--
lemma `IsBase.map` / 引理 `IsBase.map`

English:
lemma IsBase.map
  given: {B : Set α} (hB : M.IsBase B) {f : α -> β} (hf)
  statement: (M.map f hf).IsBase (f '' B)
  proof: by
  rw [map_isBase_iff]; exact ⟨B, hB, rfl⟩

中文:
引理 IsBase.map
  条件: {B : 集合 α} (hB : M.IsBase B) {f : α -> β} (hf)
  结论: (M.map f hf).IsBase (f '' B)
  证明: by
  rw [map_isBase_iff]; exact ⟨B, hB, rfl⟩

Depends on / 依赖: map_isBase_iff
-/
lemma IsBase.map {B : Set α} (hB : M.IsBase B) {f : α -> β} (hf) : (M.map f hf).IsBase (f '' B) := by
  rw [map_isBase_iff]; exact ⟨B, hB, rfl⟩

/--
lemma `map_dep_iff` / 引理 `map_dep_iff`

English:
lemma map_dep_iff
  given: {hf} {D : Set β}
  proof: by
  simp only [Dep, map_indep_iff, not_exists, not_and, map_ground, subset_image_iff]
  constructor
  · rintro ⟨h, D₀, hD₀E, rfl⟩
    exact ⟨D₀, ⟨fun hd => h _ hd rfl, hD₀E⟩, rfl⟩
  rintro ⟨D₀, ⟨hD₀, hD₀E⟩, rfl⟩
  refine ⟨fun I hI h_eq => ?_, ⟨_, hD₀E, rfl⟩⟩
  rw [hf.image_eq_image_iff hD₀E hI.subs

中文:
引理 map_dep_iff
  条件: {hf} {D : 集合 β}
  证明: by
  simp only [Dep, map_indep_iff, not_exists, not_and, map_ground, subset_image_iff]
  constructor
  · rintro ⟨h, D₀, hD₀E, rfl⟩
    exact ⟨D₀, ⟨fun hd => h _ hd rfl, hD₀E⟩, rfl⟩
  rintro ⟨D₀, ⟨hD₀, hD₀E⟩, rfl⟩
  refine ⟨fun I hI h_eq => ?_, ⟨_, hD₀E, rfl⟩⟩
  rw [hf.image_eq_image_iff hD₀E hI.subs

Depends on / 依赖: hI.subset_ground, h_eq, hf.image_eq_image_iff, image_eq_image_iff, map_ground, map_indep_iff, not_and, not_exists, subset_ground, subset_image_iff
-/
lemma map_dep_iff {hf} {D : Set β} :
    (M.map f hf).Dep D ↔ exists D₀, M.Dep D₀ ∧ D = f '' D₀ := by
  simp only [Dep, map_indep_iff, not_exists, not_and, map_ground, subset_image_iff]
  constructor
  · rintro ⟨h, D₀, hD₀E, rfl⟩
    exact ⟨D₀, ⟨fun hd => h _ hd rfl, hD₀E⟩, rfl⟩
  rintro ⟨D₀, ⟨hD₀, hD₀E⟩, rfl⟩
  refine ⟨fun I hI h_eq => ?_, ⟨_, hD₀E, rfl⟩⟩
  rw [hf.image_eq_image_iff hD₀E hI.subset_ground] at h_eq
  subst h_eq; contradiction

/--
lemma `map_image_isBase_iff` / 引理 `map_image_isBase_iff`

English:
lemma map_image_isBase_iff
  given: {hf} {B : Set α} (hB : B subseteq M.E)
  proof: by
  rw [map_isBase_iff]
  refine ⟨fun ⟨J, hJ, hIJ⟩ => ?_, fun h => ⟨B, h, rfl⟩⟩
  rw [hf.image_eq_image_iff hB hJ.subset_ground] at hIJ; rwa [hIJ]

中文:
引理 map_image_isBase_iff
  条件: {hf} {B : 集合 α} (hB : B subseteq M.E)
  证明: by
  rw [map_isBase_iff]
  refine ⟨fun ⟨J, hJ, hIJ⟩ => ?_, fun h => ⟨B, h, rfl⟩⟩
  rw [hf.image_eq_image_iff hB hJ.subset_ground] at hIJ; rwa [hIJ]

Depends on / 依赖: hJ.subset_ground, hf.image_eq_image_iff, image_eq_image_iff, map_isBase_iff, subset_ground
-/
lemma map_image_isBase_iff {hf} {B : Set α} (hB : B subseteq M.E) :
    (M.map f hf).IsBase (f '' B) ↔ M.IsBase B := by
  rw [map_isBase_iff]
  refine ⟨fun ⟨J, hJ, hIJ⟩ => ?_, fun h => ⟨B, h, rfl⟩⟩
  rw [hf.image_eq_image_iff hB hJ.subset_ground] at hIJ; rwa [hIJ]

/--
lemma `IsBasis.map` / 引理 `IsBasis.map`

English:
lemma IsBasis.map
  given: {X : Set α} (hIX : M.IsBasis I X) {f : α -> β} (hf)
  proof: by
  refine (hIX.indep.map f hf).isBasis_of_forall_insert (image_mono hIX.subset) ?_
  rintro _ ⟨⟨e, he, rfl⟩, he'⟩
  have hss := insert_subset (hIX.subset_ground he) hIX.indep.subset_ground
  rw [← not_indep_iff (by simpa [← image_insert_eq] using image_mono hss)]
  simp only [map_indep_iff, not_ex

中文:
引理 是基.map
  条件: {X : 集合 α} (hIX : M.是基 I X) {f : α -> β} (hf)
  证明: by
  refine (hIX.indep.map f hf).isBasis_of_forall_insert (image_mono hIX.subset) ?_
  rintro _ ⟨⟨e, he, rfl⟩, he'⟩
  have hss := insert_subset (hIX.subset_ground he) hIX.indep.subset_ground
  rw [← not_indep_iff (by simpa [← image_insert_eq] using image_mono hss)]
  simp only [map_indep_iff, not_ex

Depends on / 依赖: hIX.indep.map, hIX.indep.subset_ground, hIX.mem_of_insert_indep, hIX.subset, hIX.subset_ground, hJ.subset_ground, hf.image_eq_image_iff, image_eq_image_iff, image_insert_eq, image_mono, insert_subset, isBasis_of_forall_insert, map_indep_iff, mem_image_of_mem, mem_of_insert_indep, not_and, not_exists, not_indep_iff, subset, subset_ground
-/
lemma IsBasis.map {X : Set α} (hIX : M.IsBasis I X) {f : α -> β} (hf) :
    (M.map f hf).IsBasis (f '' I) (f '' X) := by
  refine (hIX.indep.map f hf).isBasis_of_forall_insert (image_mono hIX.subset) ?_
  rintro _ ⟨⟨e, he, rfl⟩, he'⟩
  have hss := insert_subset (hIX.subset_ground he) hIX.indep.subset_ground
  rw [← not_indep_iff (by simpa [← image_insert_eq] using image_mono hss)]
  simp only [map_indep_iff, not_exists, not_and]
  intro J hJ hins
  rw [← image_insert_eq]; rw [hf.image_eq_image_iff hss hJ.subset_ground] at hins
  obtain rfl := hins
  exact he' (mem_image_of_mem f (hIX.mem_of_insert_indep he hJ))

/--
lemma `map_isBasis_iff` / 引理 `map_isBasis_iff`

English:
lemma map_isBasis_iff
  given: {I X : Set α} (f : α -> β) (hf) (hI : I subseteq M.E) (hX : X subseteq M.E)
  proof: by
  refine ⟨fun h => ?_, fun h => h.map hf⟩
  obtain ⟨I', hI', hII'⟩ := map_indep_iff.1 h.indep
  rw [hf.image_eq_image_iff hI hI'.subset_ground] at hII'
  obtain rfl := hII'
  have hss := (hf.image_subset_image_iff hI hX).1 h.subset
  refine hI'.isBasis_of_maximal_subset hss (fun J hJ hIJ hJX => ?

中文:
引理 map_isBasis_iff
  条件: {I X : 集合 α} (f : α -> β) (hf) (hI : I subseteq M.E) (hX : X subseteq M.E)
  证明: by
  refine ⟨fun h => ?_, fun h => h.map hf⟩
  obtain ⟨I', hI', hII'⟩ := map_indep_iff.1 h.indep
  rw [hf.image_eq_image_iff hI hI'.subset_ground] at hII'
  obtain rfl := hII'
  have hss := (hf.image_subset_image_iff hI hX).1 h.subset
  refine hI'.isBasis_of_maximal_subset hss (fun J hJ hIJ hJX => ?

Depends on / 依赖: eq_of_subset_indep, h.eq_of_subset_indep, h.indep, h.map, h.subset, hJ.map, hJ.subset_ground, hf.image_eq_image_iff, hf.image_subset_image_iff, image_eq_image_iff, image_mono, image_subset_image_iff, isBasis_of_maximal_subset, map_indep_iff, subset, subset_ground, symm.subset
-/
lemma map_isBasis_iff {I X : Set α} (f : α -> β) (hf) (hI : I subseteq M.E) (hX : X subseteq M.E) :
    (M.map f hf).IsBasis (f '' I) (f '' X) ↔ M.IsBasis I X := by
  refine ⟨fun h => ?_, fun h => h.map hf⟩
  obtain ⟨I', hI', hII'⟩ := map_indep_iff.1 h.indep
  rw [hf.image_eq_image_iff hI hI'.subset_ground] at hII'
  obtain rfl := hII'
  have hss := (hf.image_subset_image_iff hI hX).1 h.subset
  refine hI'.isBasis_of_maximal_subset hss (fun J hJ hIJ hJX => ?_)
  have hIJ' := h.eq_of_subset_indep (hJ.map f hf) (image_mono hIJ) (image_mono hJX)
  rw [hf.image_eq_image_iff hI hJ.subset_ground] at hIJ'
  exact hIJ'.symm.subset

/--
lemma `map_isBasis_iff'` / 引理 `map_isBasis_iff'`

English:
lemma map_isBasis_iff'
  given: {I X : Set β} {hf}
  proof: by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨I, hI, rfl⟩ := subset_image_iff.1 h.indep.subset_ground
    obtain ⟨X, hX, rfl⟩ := subset_image_iff.1 h.subset_ground
    rw [map_isBasis_iff _ _ hI hX] at h
    exact ⟨I, X, h, rfl, rfl⟩
  rintro ⟨I, X, hIX, rfl, rfl⟩
  exact hIX.map hf

中文:
引理 map_isBasis_iff'
  条件: {I X : 集合 β} {hf}
  证明: by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨I, hI, rfl⟩ := subset_image_iff.1 h.indep.subset_ground
    obtain ⟨X, hX, rfl⟩ := subset_image_iff.1 h.subset_ground
    rw [map_isBasis_iff _ _ hI hX] at h
    exact ⟨I, X, h, rfl, rfl⟩
  rintro ⟨I, X, hIX, rfl, rfl⟩
  exact hIX.map hf

Depends on / 依赖: h.indep.subset_ground, h.subset_ground, hIX.map, map_isBasis_iff, subset_ground, subset_image_iff
-/
lemma map_isBasis_iff' {I X : Set β} {hf} :
    (M.map f hf).IsBasis I X ↔ exists I₀ X₀, M.IsBasis I₀ X₀ ∧ I = f '' I₀ ∧ X = f '' X₀ := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨I, hI, rfl⟩ := subset_image_iff.1 h.indep.subset_ground
    obtain ⟨X, hX, rfl⟩ := subset_image_iff.1 h.subset_ground
    rw [map_isBasis_iff _ _ hI hX] at h
    exact ⟨I, X, h, rfl, rfl⟩
  rintro ⟨I, X, hIX, rfl, rfl⟩
  exact hIX.map hf

set_option backward.isDefEq.respectTransparency false in
/--
lemma `map_dual` / 引理 `map_dual`

English:
lemma map_dual
  given: {hf}
  statement: (M.map f hf)✶ = M✶.map f hf
  proof: by
  apply ext_isBase (by simp)
  simp only [dual_ground, map_ground, subset_image_iff, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, dual_isBase_iff']
  intro B hB
  simp_rw [← hf.image_sdiff_subset hB, map_image_isBase_iff sdiff_subset,
    map_image_isBase_iff (show B subseteq M✶.E 

中文:
引理 map_dual
  条件: {hf}
  结论: (M.map f hf)✶ = M✶.map f hf
  证明: by
  apply ext_isBase (by simp)
  simp only [dual_ground, map_ground, subset_image_iff, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, dual_isBase_iff']
  intro B hB
  simp_rw [← hf.image_sdiff_subset hB, map_image_isBase_iff sdiff_subset,
    map_image_isBase_iff (show B subseteq M✶.E 
-/
@[simp] lemma map_dual {hf} : (M.map f hf)✶ = M✶.map f hf := by
  apply ext_isBase (by simp)
  simp only [dual_ground, map_ground, subset_image_iff, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, dual_isBase_iff']
  intro B hB
  simp_rw [← hf.image_sdiff_subset hB, map_image_isBase_iff sdiff_subset,
    map_image_isBase_iff (show B subseteq M✶.E from hB), dual_isBase_iff hB, and_iff_left_iff_imp]
  exact fun _ => ⟨B, hB, rfl⟩

/--
lemma `map_emptyOn` / 引理 `map_emptyOn`

English:
lemma map_emptyOn
  given: (f : α -> β)
  statement: (emptyOn α).map f (by simp) = emptyOn β
  proof: by
  simp [← ground_eq_empty_iff]

中文:
引理 map_emptyOn
  条件: (f : α -> β)
  结论: (emptyOn α).map f (by simp) = emptyOn β
  证明: by
  simp [← ground_eq_empty_iff]
-/
@[simp] lemma map_emptyOn (f : α -> β) : (emptyOn α).map f (by simp) = emptyOn β := by
  simp [← ground_eq_empty_iff]

/--
lemma `map_loopyOn` / 引理 `map_loopyOn`

English:
lemma map_loopyOn
  given: (f : α -> β) (hf)
  statement: (loopyOn E).map f hf = loopyOn (f '' E)
  proof: by
  simp [eq_loopyOn_iff]

中文:
引理 map_loopyOn
  条件: (f : α -> β) (hf)
  结论: (loopyOn E).map f hf = loopyOn (f '' E)
  证明: by
  simp [eq_loopyOn_iff]
-/
@[simp] lemma map_loopyOn (f : α -> β) (hf) : (loopyOn E).map f hf = loopyOn (f '' E) := by
  simp [eq_loopyOn_iff]

/--
lemma `map_freeOn` / 引理 `map_freeOn`

English:
lemma map_freeOn
  given: (f : α -> β) (hf)
  statement: (freeOn E).map f hf = freeOn (f '' E)
  proof: by
  rw [← dual_inj]; simp

中文:
引理 map_freeOn
  条件: (f : α -> β) (hf)
  结论: (freeOn E).map f hf = freeOn (f '' E)
  证明: by
  rw [← dual_inj]; simp
-/
@[simp] lemma map_freeOn (f : α -> β) (hf) : (freeOn E).map f hf = freeOn (f '' E) := by
  rw [← dual_inj]; simp

/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  statement: M.map id (injOn_id M.E) = M
  proof: by
  simp [ext_iff_indep]

中文:
引理 map_id
  结论: M.map id (injOn_id M.E) = M
  证明: by
  simp [ext_iff_indep]
-/
@[simp] lemma map_id : M.map id (injOn_id M.E) = M := by
  simp [ext_iff_indep]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `map_comap` / 引理 `map_comap`

English:
lemma map_comap
  given: {f : α -> β} (h_range : N.E subseteq range f) (hf : InjOn f (f ⁻¹' N.E))
  proof: by
  refine ext_indep (by simpa [image_preimage_eq_iff]) ?_
  simp only [map_ground, comap_ground_eq, map_indep_iff, comap_indep_iff, forall_subset_image_iff]
  exact fun I hI => ⟨by grind, fun h => ⟨_, ⟨h, hf.mono hI⟩, rfl⟩⟩

中文:
引理 map_comap
  条件: {f : α -> β} (h_range : N.E subseteq range f) (hf : 单射限制 f (f ⁻¹' N.E))
  证明: by
  refine ext_indep (by simpa [image_preimage_eq_iff]) ?_
  simp only [map_ground, comap_ground_eq, map_indep_iff, comap_indep_iff, forall_subset_image_iff]
  exact fun I hI => ⟨by grind, fun h => ⟨_, ⟨h, hf.mono hI⟩, rfl⟩⟩

Depends on / 依赖: comap_ground_eq, comap_indep_iff, ext_indep, forall_subset_image_iff, hf.mono, image_preimage_eq_iff, map_ground, map_indep_iff
-/
lemma map_comap {f : α -> β} (h_range : N.E subseteq range f) (hf : InjOn f (f ⁻¹' N.E)) :
    (N.comap f).map f hf = N := by
  refine ext_indep (by simpa [image_preimage_eq_iff]) ?_
  simp only [map_ground, comap_ground_eq, map_indep_iff, comap_indep_iff, forall_subset_image_iff]
  exact fun I hI => ⟨by grind, fun h => ⟨_, ⟨h, hf.mono hI⟩, rfl⟩⟩

/--
lemma `comap_map` / 引理 `comap_map`

English:
lemma comap_map
  given: {f : α -> β} (hf : f.Injective)
  statement: (M.map f hf.injOn).comap f = M
  proof: by
  simp [ext_iff_indep, preimage_image_eq _ hf, and_iff_left hf.injOn,
    image_eq_image hf]

中文:
引理 comap_map
  条件: {f : α -> β} (hf : f.单射)
  结论: (M.map f hf.injOn).comap f = M
  证明: by
  simp [ext_iff_indep, preimage_image_eq _ hf, and_iff_left hf.injOn,
    image_eq_image hf]

Depends on / 依赖: and_iff_left, ext_iff_indep, hf.injOn, image_eq_image, preimage_image_eq
-/
lemma comap_map {f : α -> β} (hf : f.Injective) : (M.map f hf.injOn).comap f = M := by
  simp [ext_iff_indep, preimage_image_eq _ hf, and_iff_left hf.injOn,
    image_eq_image hf]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [M.Nonempty]
  signature: {f : α -> β} (hf)
  body: ⟨by simp [M.ground_nonempty]⟩

中文:
实例 [M.非空]
  签名: {f : α -> β} (hf)
  定义体: ⟨by simp [M.ground_nonempty]⟩

Depends on / 依赖: M.ground_nonempty, ground_nonempty
-/
instance [M.Nonempty] {f : α -> β} (hf) : (M.map f hf).Nonempty :=
  ⟨by simp [M.ground_nonempty]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [M.Finite]
  signature: {f : α -> β} (hf)
  body: ⟨M.ground_finite.image f⟩

中文:
实例 [M.有限]
  签名: {f : α -> β} (hf)
  定义体: ⟨M.ground_finite.image f⟩

Depends on / 依赖: M.ground_finite.image, ground_finite
-/
instance [M.Finite] {f : α -> β} (hf) : (M.map f hf).Finite :=
  ⟨M.ground_finite.image f⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [M.Finitary]
  signature: {f : α -> β} (hf)
  body: by
  refine ⟨fun I hI => ?_⟩
  simp only [map_indep_iff]
  have h' : I subseteq f '' M.E := by
    intro e he
    obtain ⟨I₀, hI₀, h_eq⟩ := hI {e} (by simpa) (by simp)
exact image_mono hI₀.subset_ground h_eq.subset rfl
  obtain ⟨I₀, hI₀E, rfl⟩ := subset_image_iff.1 h'
  refine ⟨I₀, indep_of_forall_f

中文:
实例 [M.Finitary]
  签名: {f : α -> β} (hf)
  定义体: by
  refine ⟨fun I hI => ?_⟩
  simp only [map_indep_iff]
  have h' : I subseteq f '' M.E := by
    intro e he
    obtain ⟨I₀, hI₀, h_eq⟩ := hI {e} (by simpa) (by simp)
exact image_mono hI₀.subset_ground h_eq.subset rfl
  obtain ⟨I₀, hI₀E, rfl⟩ := subset_image_iff.1 h'
  refine ⟨I₀, indep_of_forall_f

Depends on / 依赖: h_eq, h_eq.subset, image_mono, indep_of_forall_finite_subset_indep, map_image_indep_iff, map_indep_iff, specialize, subset, subset_ground, subset_image_iff, subseteq
-/
instance [M.Finitary] {f : α -> β} (hf) : (M.map f hf).Finitary := by
  refine ⟨fun I hI => ?_⟩
  simp only [map_indep_iff]
  have h' : I subseteq f '' M.E := by
    intro e he
    obtain ⟨I₀, hI₀, h_eq⟩ := hI {e} (by simpa) (by simp)
exact image_mono hI₀.subset_ground h_eq.subset rfl
  obtain ⟨I₀, hI₀E, rfl⟩ := subset_image_iff.1 h'
  refine ⟨I₀, indep_of_forall_finite_subset_indep _ fun J₀ hJ₀I₀ hJ₀ => ?_, rfl⟩
  specialize hI (f '' J₀) (image_mono hJ₀I₀) (hJ₀.image _)
  rwa [map_image_indep_iff (hJ₀I₀.trans hI₀E)] at hI

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [M.RankFinite]
  signature: {f : α -> β} (hf)
  body: let ⟨_, hB⟩ := M.exists_isBase
  (hB.map hf).rankFinite_of_finite (hB.finite.image _)

中文:
实例 [M.RankFinite]
  签名: {f : α -> β} (hf)
  定义体: let ⟨_, hB⟩ := M.exists_isBase
  (hB.map hf).rankFinite_of_finite (hB.finite.image _)

Depends on / 依赖: M.exists_isBase, exists_isBase, finite, hB.finite.image, hB.map, rankFinite_of_finite
-/
instance [M.RankFinite] {f : α -> β} (hf) : (M.map f hf).RankFinite :=
  let ⟨_, hB⟩ := M.exists_isBase
  (hB.map hf).rankFinite_of_finite (hB.finite.image _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [M.RankPos]
  signature: {f : α -> β} (hf)
  body: let ⟨_, hB⟩ := M.exists_isBase
  (hB.map hf).rankPos_of_nonempty (hB.nonempty.image _)

中文:
实例 [M.RankPos]
  签名: {f : α -> β} (hf)
  定义体: let ⟨_, hB⟩ := M.exists_isBase
  (hB.map hf).rankPos_of_nonempty (hB.nonempty.image _)

Depends on / 依赖: M.exists_isBase, exists_isBase, hB.map, hB.nonempty.image, nonempty, rankPos_of_nonempty
-/
instance [M.RankPos] {f : α -> β} (hf) : (M.map f hf).RankPos :=
  let ⟨_, hB⟩ := M.exists_isBase
  (hB.map hf).rankPos_of_nonempty (hB.nonempty.image _)

end map

section mapSetEquiv

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `mapSetEquiv` / `mapSetEquiv` 的定义

English:
definition mapSetEquiv
  signature: (M : Matroid α) {E : Set β} (e : M.E ≃ E)
  body: Matroid.ofExistsMatroid E (fun I => (M.Indep ↑(e.symm '' (E ↓inter I)) ∧ I subseteq E))
  ⟨M.mapSetEmbedding (e.toEmbedding.trans <| Function.Embedding.subtype _), by
    have hrw : forall I : Set β, Subtype.val ∘ ⇑e ⁻¹' I = ⇑e.symm '' E ↓inter I := fun I => by ext; simp
    simp [Equiv.toEmbedding,

中文:
定义 mapSetEquiv
  签名: (M : 拟阵 α) {E : 集合 β} (e : M.E ≃ E)
  定义体: Matroid.ofExistsMatroid E (fun I => (M.Indep ↑(e.symm '' (E ↓inter I)) ∧ I subseteq E))
  ⟨M.mapSetEmbedding (e.toEmbedding.trans <| Function.Embedding.subtype _), by
    have hrw : forall I : Set β, Subtype.val ∘ ⇑e ⁻¹' I = ⇑e.symm '' E ↓inter I := fun I => by ext; simp
    simp [Equiv.toEmbedding,

Depends on / 依赖: Embedding, Embedding.subtype, Embedding.trans, Equiv.toEmbedding, Function, Function.Embedding.subtype, M.Indep, M.mapSetEmbedding, Matroid, Matroid.ofExistsMatroid, Subtype, Subtype.val, e.symm, e.toEmbedding.trans, mapSetEmbedding, ofExistsMatroid, subseteq, subtype, toEmbedding
-/
def mapSetEquiv (M : Matroid α) {E : Set β} (e : M.E ≃ E) : Matroid β :=
  Matroid.ofExistsMatroid E (fun I => (M.Indep ↑(e.symm '' (E ↓inter I)) ∧ I subseteq E))
  ⟨M.mapSetEmbedding (e.toEmbedding.trans <| Function.Embedding.subtype _), by
    have hrw : forall I : Set β, Subtype.val ∘ ⇑e ⁻¹' I = ⇑e.symm '' E ↓inter I := fun I => by ext; simp
    simp [Equiv.toEmbedding, Embedding.subtype, Embedding.trans, hrw]⟩

/--
lemma `mapSetEquiv_indep_iff` / 引理 `mapSetEquiv_indep_iff`

English:
lemma mapSetEquiv_indep_iff
  given: (M : Matroid α) {E : Set β} (e : M.E ≃ E) {I : Set β}
  proof: Iff.rfl

中文:
引理 mapSetEquiv_indep_iff
  条件: (M : 拟阵 α) {E : 集合 β} (e : M.E ≃ E) {I : 集合 β}
  证明: Iff.rfl
-/
@[simp] lemma mapSetEquiv_indep_iff (M : Matroid α) {E : Set β} (e : M.E ≃ E) {I : Set β} :
    (M.mapSetEquiv e).Indep I ↔ M.Indep ↑(e.symm '' (E ↓inter I)) ∧ I subseteq E := Iff.rfl

/--
lemma `mapSetEquiv.ground` / 引理 `mapSetEquiv.ground`

English:
lemma mapSetEquiv.ground
  given: (M : Matroid α) {E : Set β} (e : M.E ≃ E)
  proof: rfl

中文:
引理 mapSetEquiv.ground
  条件: (M : 拟阵 α) {E : 集合 β} (e : M.E ≃ E)
  证明: rfl
-/
@[simp] lemma mapSetEquiv.ground (M : Matroid α) {E : Set β} (e : M.E ≃ E) :
    (M.mapSetEquiv e).E = E := rfl

end mapSetEquiv
section mapEmbedding

/--
Definition of `mapEmbedding` / `mapEmbedding` 的定义

English:
definition mapEmbedding
  signature: (M : Matroid α) (f : α ↪ β)
  body: M.map f f.injective.injOn

中文:
定义 mapEmbedding
  签名: (M : 拟阵 α) (f : α ↪ β)
  定义体: M.map f f.injective.injOn

Depends on / 依赖: M.map, f.injective.injOn, injective
-/
def mapEmbedding (M : Matroid α) (f : α ↪ β) : Matroid β := M.map f f.injective.injOn

/--
lemma `mapEmbedding_ground_eq` / 引理 `mapEmbedding_ground_eq`

English:
lemma mapEmbedding_ground_eq
  given: (M : Matroid α) (f : α ↪ β)
  proof: rfl

中文:
引理 mapEmbedding_ground_eq
  条件: (M : 拟阵 α) (f : α ↪ β)
  证明: rfl
-/
@[simp] lemma mapEmbedding_ground_eq (M : Matroid α) (f : α ↪ β) :
    (M.mapEmbedding f).E = f '' M.E := rfl

/--
lemma `mapEmbedding_indep_iff` / 引理 `mapEmbedding_indep_iff`

English:
lemma mapEmbedding_indep_iff
  given: {f : α ↪ β} {I : Set β}
  proof: by
  rw [mapEmbedding]; rw [map_indep_iff]
  refine ⟨?_, fun ⟨h,h'⟩ => ⟨f ⁻¹' I, h, by rwa [eq_comm, image_preimage_eq_iff]⟩⟩
  rintro ⟨I, hI, rfl⟩
  rw [preimage_image_eq _ f.injective]
  exact ⟨hI, image_subset_range _ _⟩

中文:
引理 mapEmbedding_indep_iff
  条件: {f : α ↪ β} {I : 集合 β}
  证明: by
  rw [mapEmbedding]; rw [map_indep_iff]
  refine ⟨?_, fun ⟨h,h'⟩ => ⟨f ⁻¹' I, h, by rwa [eq_comm, image_preimage_eq_iff]⟩⟩
  rintro ⟨I, hI, rfl⟩
  rw [preimage_image_eq _ f.injective]
  exact ⟨hI, image_subset_range _ _⟩
-/
@[simp] lemma mapEmbedding_indep_iff {f : α ↪ β} {I : Set β} :
    (M.mapEmbedding f).Indep I ↔ M.Indep (f ⁻¹' I) ∧ I subseteq range f := by
  rw [mapEmbedding]; rw [map_indep_iff]
  refine ⟨?_, fun ⟨h,h'⟩ => ⟨f ⁻¹' I, h, by rwa [eq_comm, image_preimage_eq_iff]⟩⟩
  rintro ⟨I, hI, rfl⟩
  rw [preimage_image_eq _ f.injective]
  exact ⟨hI, image_subset_range _ _⟩

/--
lemma `Indep.mapEmbedding` / 引理 `Indep.mapEmbedding`

English:
lemma Indep.mapEmbedding
  given: (hI : M.Indep I) (f : α ↪ β)
  statement: (M.mapEmbedding f).Indep (f '' I)
  proof: by
  simpa [preimage_image_eq I f.injective]

中文:
引理 Indep.mapEmbedding
  条件: (hI : M.Indep I) (f : α ↪ β)
  结论: (M.mapEmbedding f).Indep (f '' I)
  证明: by
  simpa [preimage_image_eq I f.injective]

Depends on / 依赖: f.injective, injective, preimage_image_eq
-/
lemma Indep.mapEmbedding (hI : M.Indep I) (f : α ↪ β) : (M.mapEmbedding f).Indep (f '' I) := by
  simpa [preimage_image_eq I f.injective]

/--
lemma `IsBase.mapEmbedding` / 引理 `IsBase.mapEmbedding`

English:
lemma IsBase.mapEmbedding
  given: {B : Set α} (hB : M.IsBase B) (f : α ↪ β)
  proof: by
  rw [Matroid.mapEmbedding]; rw [map_isBase_iff]
  exact ⟨B, hB, rfl⟩

中文:
引理 IsBase.mapEmbedding
  条件: {B : 集合 α} (hB : M.IsBase B) (f : α ↪ β)
  证明: by
  rw [Matroid.mapEmbedding]; rw [map_isBase_iff]
  exact ⟨B, hB, rfl⟩

Depends on / 依赖: Matroid, Matroid.mapEmbedding, Setoid, Setoid.mk, equivalence, mapEmbedding, map_isBase_iff
-/
lemma IsBase.mapEmbedding {B : Set α} (hB : M.IsBase B) (f : α ↪ β) :
    (M.mapEmbedding f).IsBase (f '' B) := by
  rw [Matroid.mapEmbedding]; rw [map_isBase_iff]
  exact ⟨B, hB, rfl⟩

/--
lemma `IsBasis.mapEmbedding` / 引理 `IsBasis.mapEmbedding`

English:
lemma IsBasis.mapEmbedding
  given: {X : Set α} (hIX : M.IsBasis I X) (f : α ↪ β)
  proof: by
  apply hIX.map

中文:
引理 是基.mapEmbedding
  条件: {X : 集合 α} (hIX : M.是基 I X) (f : α ↪ β)
  证明: by
  apply hIX.map

Depends on / 依赖: hIX.map
-/
lemma IsBasis.mapEmbedding {X : Set α} (hIX : M.IsBasis I X) (f : α ↪ β) :
    (M.mapEmbedding f).IsBasis (f '' I) (f '' X) := by
  apply hIX.map

/--
lemma `mapEmbedding_isBase_iff` / 引理 `mapEmbedding_isBase_iff`

English:
lemma mapEmbedding_isBase_iff
  given: {f : α ↪ β} {B : Set β}
  proof: by
  rw [mapEmbedding]; rw [map_isBase_iff]
  refine ⟨?_, fun ⟨h,h'⟩ => ⟨f ⁻¹' B, h, by rwa [eq_comm, image_preimage_eq_iff]⟩⟩
  rintro ⟨B, hB, rfl⟩
  rw [preimage_image_eq _ f.injective]
  exact ⟨hB, image_subset_range _ _⟩

中文:
引理 mapEmbedding_isBase_iff
  条件: {f : α ↪ β} {B : 集合 β}
  证明: by
  rw [mapEmbedding]; rw [map_isBase_iff]
  refine ⟨?_, fun ⟨h,h'⟩ => ⟨f ⁻¹' B, h, by rwa [eq_comm, image_preimage_eq_iff]⟩⟩
  rintro ⟨B, hB, rfl⟩
  rw [preimage_image_eq _ f.injective]
  exact ⟨hB, image_subset_range _ _⟩
-/
@[simp] lemma mapEmbedding_isBase_iff {f : α ↪ β} {B : Set β} :
    (M.mapEmbedding f).IsBase B ↔ M.IsBase (f ⁻¹' B) ∧ B subseteq range f := by
  rw [mapEmbedding]; rw [map_isBase_iff]
  refine ⟨?_, fun ⟨h,h'⟩ => ⟨f ⁻¹' B, h, by rwa [eq_comm, image_preimage_eq_iff]⟩⟩
  rintro ⟨B, hB, rfl⟩
  rw [preimage_image_eq _ f.injective]
  exact ⟨hB, image_subset_range _ _⟩

/--
lemma `mapEmbedding_isBasis_iff` / 引理 `mapEmbedding_isBasis_iff`

English:
lemma mapEmbedding_isBasis_iff
  given: {f : α ↪ β} {I X : Set β}
  proof: by
  rw [mapEmbedding]; rw [map_isBasis_iff']
  refine ⟨?_, fun ⟨hb, hIX, hX⟩ => ?_⟩
  · rintro ⟨I, X, hIX, rfl, rfl⟩
    simp [preimage_image_eq _ f.injective, image_mono hIX.subset, hIX]
  obtain ⟨X, rfl⟩ := subset_range_iff_exists_image_eq.1 hX
  obtain ⟨I, -, rfl⟩ := subset_image_iff.1 hIX
  exa

中文:
引理 mapEmbedding_isBasis_iff
  条件: {f : α ↪ β} {I X : 集合 β}
  证明: by
  rw [mapEmbedding]; rw [map_isBasis_iff']
  refine ⟨?_, fun ⟨hb, hIX, hX⟩ => ?_⟩
  · rintro ⟨I, X, hIX, rfl, rfl⟩
    simp [preimage_image_eq _ f.injective, image_mono hIX.subset, hIX]
  obtain ⟨X, rfl⟩ := subset_range_iff_exists_image_eq.1 hX
  obtain ⟨I, -, rfl⟩ := subset_image_iff.1 hIX
  exa
-/
@[simp] lemma mapEmbedding_isBasis_iff {f : α ↪ β} {I X : Set β} :
    (M.mapEmbedding f).IsBasis I X ↔ M.IsBasis (f ⁻¹' I) (f ⁻¹' X) ∧ I subseteq X ∧ X subseteq range f := by
  rw [mapEmbedding]; rw [map_isBasis_iff']
  refine ⟨?_, fun ⟨hb, hIX, hX⟩ => ?_⟩
  · rintro ⟨I, X, hIX, rfl, rfl⟩
    simp [preimage_image_eq _ f.injective, image_mono hIX.subset, hIX]
  obtain ⟨X, rfl⟩ := subset_range_iff_exists_image_eq.1 hX
  obtain ⟨I, -, rfl⟩ := subset_image_iff.1 hIX
  exact ⟨I, X, by simpa [preimage_image_eq _ f.injective] using hb⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [M.Nonempty]
  signature: {f : α ↪ β}
  body: inferInstanceAs (M.map f f.injective.injOn).Nonempty

中文:
实例 [M.非空]
  签名: {f : α ↪ β}
  定义体: inferInstanceAs (M.map f f.injective.injOn).Nonempty

Depends on / 依赖: M.map, Nonempty, f.injective.injOn, injective
-/
instance [M.Nonempty] {f : α ↪ β} : (M.mapEmbedding f).Nonempty :=
  inferInstanceAs (M.map f f.injective.injOn).Nonempty

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [M.Finite]
  signature: {f : α ↪ β}
  body: inferInstanceAs (M.map f f.injective.injOn).Finite

中文:
实例 [M.有限]
  签名: {f : α ↪ β}
  定义体: inferInstanceAs (M.map f f.injective.injOn).Finite

Depends on / 依赖: Finite, M.map, f.injective.injOn, injective
-/
instance [M.Finite] {f : α ↪ β} : (M.mapEmbedding f).Finite :=
  inferInstanceAs (M.map f f.injective.injOn).Finite

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [M.Finitary]
  signature: {f : α ↪ β}
  body: inferInstanceAs (M.map f f.injective.injOn).Finitary

中文:
实例 [M.Finitary]
  签名: {f : α ↪ β}
  定义体: inferInstanceAs (M.map f f.injective.injOn).Finitary

Depends on / 依赖: Finitary, M.map, f.injective.injOn, injective
-/
instance [M.Finitary] {f : α ↪ β} : (M.mapEmbedding f).Finitary :=
  inferInstanceAs (M.map f f.injective.injOn).Finitary

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [M.RankFinite]
  signature: {f : α ↪ β}
  body: inferInstanceAs (M.map f f.injective.injOn).RankFinite

中文:
实例 [M.RankFinite]
  签名: {f : α ↪ β}
  定义体: inferInstanceAs (M.map f f.injective.injOn).RankFinite

Depends on / 依赖: M.map, RankFinite, f.injective.injOn, injective
-/
instance [M.RankFinite] {f : α ↪ β} : (M.mapEmbedding f).RankFinite :=
  inferInstanceAs (M.map f f.injective.injOn).RankFinite

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [M.RankPos]
  signature: {f : α ↪ β}
  body: inferInstanceAs (M.map f f.injective.injOn).RankPos

中文:
实例 [M.RankPos]
  签名: {f : α ↪ β}
  定义体: inferInstanceAs (M.map f f.injective.injOn).RankPos

Depends on / 依赖: M.map, RankPos, f.injective.injOn, injective
-/
instance [M.RankPos] {f : α ↪ β} : (M.mapEmbedding f).RankPos :=
  inferInstanceAs (M.map f f.injective.injOn).RankPos

end mapEmbedding

section mapEquiv

variable {f : α ≃ β}

/--
Definition of `mapEquiv` / `mapEquiv` 的定义

English:
definition mapEquiv
  signature: (M : Matroid α) (f : α ≃ β)
  body: M.mapEmbedding f.toEmbedding

中文:
定义 mapEquiv
  签名: (M : 拟阵 α) (f : α ≃ β)
  定义体: M.mapEmbedding f.toEmbedding

Depends on / 依赖: M.mapEmbedding, f.toEmbedding, mapEmbedding, toEmbedding
-/
def mapEquiv (M : Matroid α) (f : α ≃ β) : Matroid β := M.mapEmbedding f.toEmbedding

/--
lemma `mapEquiv_ground_eq` / 引理 `mapEquiv_ground_eq`

English:
lemma mapEquiv_ground_eq
  given: (M : Matroid α) (f : α ≃ β)
  proof: rfl

中文:
引理 mapEquiv_ground_eq
  条件: (M : 拟阵 α) (f : α ≃ β)
  证明: rfl
-/
@[simp] lemma mapEquiv_ground_eq (M : Matroid α) (f : α ≃ β) :
    (M.mapEquiv f).E = f '' M.E := rfl

/--
lemma `mapEquiv_eq_map` / 引理 `mapEquiv_eq_map`

English:
lemma mapEquiv_eq_map
  given: (f : α ≃ β)
  statement: M.mapEquiv f = M.map f f.injective.injOn
  proof: rfl

中文:
引理 mapEquiv_eq_map
  条件: (f : α ≃ β)
  结论: M.mapEquiv f = M.map f f.injective.injOn
  证明: rfl
-/
lemma mapEquiv_eq_map (f : α ≃ β) : M.mapEquiv f = M.map f f.injective.injOn := rfl

/--
lemma `mapEquiv_indep_iff` / 引理 `mapEquiv_indep_iff`

English:
lemma mapEquiv_indep_iff
  given: {I : Set β}
  statement: (M.mapEquiv f).Indep I ↔ M.Indep (f.symm '' I)
  proof: by
  rw [mapEquiv_eq_map]; rw [map_indep_iff]
  exact ⟨by rintro ⟨I, hI, rfl⟩; simpa, fun h => ⟨_, h, by simp⟩⟩

中文:
引理 mapEquiv_indep_iff
  条件: {I : 集合 β}
  结论: (M.mapEquiv f).Indep I ↔ M.Indep (f.symm '' I)
  证明: by
  rw [mapEquiv_eq_map]; rw [map_indep_iff]
  exact ⟨by rintro ⟨I, hI, rfl⟩; simpa, fun h => ⟨_, h, by simp⟩⟩
-/
@[simp] lemma mapEquiv_indep_iff {I : Set β} : (M.mapEquiv f).Indep I ↔ M.Indep (f.symm '' I) := by
  rw [mapEquiv_eq_map]; rw [map_indep_iff]
  exact ⟨by rintro ⟨I, hI, rfl⟩; simpa, fun h => ⟨_, h, by simp⟩⟩

/--
lemma `mapEquiv_dep_iff` / 引理 `mapEquiv_dep_iff`

English:
lemma mapEquiv_dep_iff
  given: {D : Set β}
  statement: (M.mapEquiv f).Dep D ↔ M.Dep (f.symm '' D)
  proof: by
  rw [mapEquiv_eq_map]; rw [map_dep_iff]
  exact ⟨by rintro ⟨I, hI, rfl⟩; simpa, fun h => ⟨_, h, by simp⟩⟩

中文:
引理 mapEquiv_dep_iff
  条件: {D : 集合 β}
  结论: (M.mapEquiv f).Dep D ↔ M.Dep (f.symm '' D)
  证明: by
  rw [mapEquiv_eq_map]; rw [map_dep_iff]
  exact ⟨by rintro ⟨I, hI, rfl⟩; simpa, fun h => ⟨_, h, by simp⟩⟩
-/
@[simp] lemma mapEquiv_dep_iff {D : Set β} : (M.mapEquiv f).Dep D ↔ M.Dep (f.symm '' D) := by
  rw [mapEquiv_eq_map]; rw [map_dep_iff]
  exact ⟨by rintro ⟨I, hI, rfl⟩; simpa, fun h => ⟨_, h, by simp⟩⟩

/--
lemma `mapEquiv_isBase_iff` / 引理 `mapEquiv_isBase_iff`

English:
lemma mapEquiv_isBase_iff
  given: {B : Set β}
  proof: by
  rw [mapEquiv_eq_map]; rw [map_isBase_iff]
  exact ⟨by rintro ⟨I, hI, rfl⟩; simpa, fun h => ⟨_, h, by simp⟩⟩

中文:
引理 mapEquiv_isBase_iff
  条件: {B : 集合 β}
  证明: by
  rw [mapEquiv_eq_map]; rw [map_isBase_iff]
  exact ⟨by rintro ⟨I, hI, rfl⟩; simpa, fun h => ⟨_, h, by simp⟩⟩
-/
@[simp] lemma mapEquiv_isBase_iff {B : Set β} :
    (M.mapEquiv f).IsBase B ↔ M.IsBase (f.symm '' B) := by
  rw [mapEquiv_eq_map]; rw [map_isBase_iff]
  exact ⟨by rintro ⟨I, hI, rfl⟩; simpa, fun h => ⟨_, h, by simp⟩⟩

/--
lemma `mapEquiv_isBasis_iff` / 引理 `mapEquiv_isBasis_iff`

English:
lemma mapEquiv_isBasis_iff
  given: {α β : Type*} {M : Matroid α} (f : α ≃ β) {I X : Set β}
  proof: by
  rw [mapEquiv_eq_map]; rw [map_isBasis_iff']
  refine ⟨fun h => ?_, fun h => ⟨_, _, h, by simp, by simp⟩⟩
  obtain ⟨I, X, hIX, rfl, rfl⟩ := h
  simpa

中文:
引理 mapEquiv_isBasis_iff
  条件: {α β : 类型} {M : 拟阵 α} (f : α ≃ β) {I X : 集合 β}
  证明: by
  rw [mapEquiv_eq_map]; rw [map_isBasis_iff']
  refine ⟨fun h => ?_, fun h => ⟨_, _, h, by simp, by simp⟩⟩
  obtain ⟨I, X, hIX, rfl, rfl⟩ := h
  simpa
-/
@[simp] lemma mapEquiv_isBasis_iff {α β : Type*} {M : Matroid α} (f : α ≃ β) {I X : Set β} :
    (M.mapEquiv f).IsBasis I X ↔ M.IsBasis (f.symm '' I) (f.symm '' X) := by
  rw [mapEquiv_eq_map]; rw [map_isBasis_iff']
  refine ⟨fun h => ?_, fun h => ⟨_, _, h, by simp, by simp⟩⟩
  obtain ⟨I, X, hIX, rfl, rfl⟩ := h
  simpa

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [M.Nonempty]
  signature: {f : α ≃ β}
  body: inferInstanceAs (M.map f f.injective.injOn).Nonempty

中文:
实例 [M.非空]
  签名: {f : α ≃ β}
  定义体: inferInstanceAs (M.map f f.injective.injOn).Nonempty

Depends on / 依赖: M.map, Nonempty, f.injective.injOn, injective
-/
instance [M.Nonempty] {f : α ≃ β} : (M.mapEquiv f).Nonempty :=
  inferInstanceAs (M.map f f.injective.injOn).Nonempty

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [M.Finite]
  signature: {f : α ≃ β}
  body: inferInstanceAs (M.map f f.injective.injOn).Finite

中文:
实例 [M.有限]
  签名: {f : α ≃ β}
  定义体: inferInstanceAs (M.map f f.injective.injOn).Finite

Depends on / 依赖: Finite, M.map, f.injective.injOn, injective
-/
instance [M.Finite] {f : α ≃ β} : (M.mapEquiv f).Finite :=
  inferInstanceAs (M.map f f.injective.injOn).Finite

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [M.Finitary]
  signature: {f : α ≃ β}
  body: inferInstanceAs (M.map f f.injective.injOn).Finitary

中文:
实例 [M.Finitary]
  签名: {f : α ≃ β}
  定义体: inferInstanceAs (M.map f f.injective.injOn).Finitary

Depends on / 依赖: Finitary, M.map, f.injective.injOn, injective
-/
instance [M.Finitary] {f : α ≃ β} : (M.mapEquiv f).Finitary :=
  inferInstanceAs (M.map f f.injective.injOn).Finitary

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [M.RankFinite]
  signature: {f : α ≃ β}
  body: inferInstanceAs (M.map f f.injective.injOn).RankFinite

中文:
实例 [M.RankFinite]
  签名: {f : α ≃ β}
  定义体: inferInstanceAs (M.map f f.injective.injOn).RankFinite

Depends on / 依赖: M.map, RankFinite, f.injective.injOn, injective
-/
instance [M.RankFinite] {f : α ≃ β} : (M.mapEquiv f).RankFinite :=
  inferInstanceAs (M.map f f.injective.injOn).RankFinite

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [M.RankPos]
  signature: {f : α ≃ β}
  body: inferInstanceAs (M.map f f.injective.injOn).RankPos

中文:
实例 [M.RankPos]
  签名: {f : α ≃ β}
  定义体: inferInstanceAs (M.map f f.injective.injOn).RankPos

Depends on / 依赖: M.map, RankPos, f.injective.injOn, injective
-/
instance [M.RankPos] {f : α ≃ β} : (M.mapEquiv f).RankPos :=
  inferInstanceAs (M.map f f.injective.injOn).RankPos

end mapEquiv

section restrictSubtype

variable {E X I : Set α} {M : Matroid α}

/--
Definition of `restrictSubtype` / `restrictSubtype` 的定义

English:
definition restrictSubtype
  signature: (M : Matroid α) (X : Set α)
  body: (M ↾ X).comap (↑)

中文:
定义 restrictSubtype
  签名: (M : 拟阵 α) (X : 集合 α)
  定义体: (M ↾ X).comap (↑)
-/
def restrictSubtype (M : Matroid α) (X : Set α) : Matroid X := (M ↾ X).comap (↑)

/--
lemma `restrictSubtype_ground` / 引理 `restrictSubtype_ground`

English:
lemma restrictSubtype_ground
  statement: (M.restrictSubtype X).E = univ
  proof: by
  simp [restrictSubtype]

中文:
引理 restrictSubtype_ground
  结论: (M.restrictSubtype X).E = univ
  证明: by
  simp [restrictSubtype]
-/
@[simp] lemma restrictSubtype_ground : (M.restrictSubtype X).E = univ := by
  simp [restrictSubtype]

/--
lemma `restrictSubtype_indep_iff` / 引理 `restrictSubtype_indep_iff`

English:
lemma restrictSubtype_indep_iff
  given: {I : Set X}
  proof: by
  simp [restrictSubtype, Subtype.val_injective.injOn]

中文:
引理 restrictSubtype_indep_iff
  条件: {I : 集合 X}
  证明: by
  simp [restrictSubtype, Subtype.val_injective.injOn]
-/
@[simp] lemma restrictSubtype_indep_iff {I : Set X} :
    (M.restrictSubtype X).Indep I ↔ M.Indep ((↑) '' I) := by
  simp [restrictSubtype, Subtype.val_injective.injOn]

/--
lemma `restrictSubtype_indep_iff_of_subset` / 引理 `restrictSubtype_indep_iff_of_subset`

English:
lemma restrictSubtype_indep_iff_of_subset
  given: (hIX : I subseteq X)
  proof: by
  rw [restrictSubtype_indep_iff]; rw [image_preimage_eq_iff.2]; simpa

中文:
引理 restrictSubtype_indep_iff_of_subset
  条件: (hIX : I subseteq X)
  证明: by
  rw [restrictSubtype_indep_iff]; rw [image_preimage_eq_iff.2]; simpa

Depends on / 依赖: image_preimage_eq_iff, restrictSubtype_indep_iff
-/
lemma restrictSubtype_indep_iff_of_subset (hIX : I subseteq X) :
    (M.restrictSubtype X).Indep (X ↓inter I) ↔ M.Indep I := by
  rw [restrictSubtype_indep_iff]; rw [image_preimage_eq_iff.2]; simpa

/--
lemma `restrictSubtype_inter_indep_iff` / 引理 `restrictSubtype_inter_indep_iff`

English:
lemma restrictSubtype_inter_indep_iff
  proof: by
  simp [restrictSubtype, Subtype.val_injective.injOn]

中文:
引理 restrictSubtype_inter_indep_iff
  证明: by
  simp [restrictSubtype, Subtype.val_injective.injOn]

Depends on / 依赖: Subtype, Subtype.val_injective.injOn, restrictSubtype, val_injective
-/
lemma restrictSubtype_inter_indep_iff :
    (M.restrictSubtype X).Indep (X ↓inter I) ↔ M.Indep (X inter I) := by
  simp [restrictSubtype, Subtype.val_injective.injOn]

/--
lemma `restrictSubtype_isBasis_iff` / 引理 `restrictSubtype_isBasis_iff`

English:
lemma restrictSubtype_isBasis_iff
  given: {Y : Set α} {I X : Set Y}
  proof: by
  rw [restrictSubtype]; rw [comap_isBasis_iff]; rw [and_iff_right Subtype.val_injective.injOn]; rw [and_iff_left_of_imp]; rw [isBasis_restrict_iff']; rw [isBasis'_iff_isBasis_inter_ground]
  · simp
  exact fun h => (image_subset_image_iff Subtype.val_injective).1 h.subset

中文:
引理 restrictSubtype_isBasis_iff
  条件: {Y : 集合 α} {I X : 集合 Y}
  证明: by
  rw [restrictSubtype]; rw [comap_isBasis_iff]; rw [and_iff_right Subtype.val_injective.injOn]; rw [and_iff_left_of_imp]; rw [isBasis_restrict_iff']; rw [isBasis'_iff_isBasis_inter_ground]
  · simp
  exact fun h => (image_subset_image_iff Subtype.val_injective).1 h.subset

Depends on / 依赖: Subtype, Subtype.val_injective, Subtype.val_injective.injOn, _iff_isBasis_inter_ground, and_iff_left_of_imp, and_iff_right, comap_isBasis_iff, h.subset, image_subset_image_iff, isBasis, isBasis_restrict_iff, restrictSubtype, subset, val_injective
-/
lemma restrictSubtype_isBasis_iff {Y : Set α} {I X : Set Y} :
    (M.restrictSubtype Y).IsBasis I X ↔ M.IsBasis' I X := by
  rw [restrictSubtype]; rw [comap_isBasis_iff]; rw [and_iff_right Subtype.val_injective.injOn]; rw [and_iff_left_of_imp]; rw [isBasis_restrict_iff']; rw [isBasis'_iff_isBasis_inter_ground]
  · simp
  exact fun h => (image_subset_image_iff Subtype.val_injective).1 h.subset

/--
lemma `restrictSubtype_isBase_iff` / 引理 `restrictSubtype_isBase_iff`

English:
lemma restrictSubtype_isBase_iff
  given: {B : Set X}
  statement: (M.restrictSubtype X).IsBase B ↔ M.IsBasis' B X
  proof: by
  rw [restrictSubtype]; rw [comap_isBase_iff]
  simp [Subtype.val_injective.injOn, isBasis_restrict_iff',
    isBasis'_iff_isBasis_inter_ground]

中文:
引理 restrictSubtype_isBase_iff
  条件: {B : 集合 X}
  结论: (M.restrictSubtype X).IsBase B ↔ M.是基' B X
  证明: by
  rw [restrictSubtype]; rw [comap_isBase_iff]
  simp [Subtype.val_injective.injOn, isBasis_restrict_iff',
    isBasis'_iff_isBasis_inter_ground]

Depends on / 依赖: Subtype, Subtype.val_injective.injOn, _iff_isBasis_inter_ground, comap_isBase_iff, isBasis, isBasis_restrict_iff, restrictSubtype, val_injective
-/
lemma restrictSubtype_isBase_iff {B : Set X} : (M.restrictSubtype X).IsBase B ↔ M.IsBasis' B X := by
  rw [restrictSubtype]; rw [comap_isBase_iff]
  simp [Subtype.val_injective.injOn, isBasis_restrict_iff',
    isBasis'_iff_isBasis_inter_ground]

/--
lemma `restrictSubtype_ground_isBase_iff` / 引理 `restrictSubtype_ground_isBase_iff`

English:
lemma restrictSubtype_ground_isBase_iff
  given: {B : Set M.E}
  proof: by
  rw [restrictSubtype_isBase_iff]; rw [isBasis'_iff_isBasis]; rw [isBasis_ground_iff]

中文:
引理 restrictSubtype_ground_isBase_iff
  条件: {B : 集合 M.E}
  证明: by
  rw [restrictSubtype_isBase_iff]; rw [isBasis'_iff_isBasis]; rw [isBasis_ground_iff]
-/
@[simp] lemma restrictSubtype_ground_isBase_iff {B : Set M.E} :
    (M.restrictSubtype M.E).IsBase B ↔ M.IsBase B := by
  rw [restrictSubtype_isBase_iff]; rw [isBasis'_iff_isBasis]; rw [isBasis_ground_iff]

/--
lemma `restrictSubtype_ground_isBasis_iff` / 引理 `restrictSubtype_ground_isBasis_iff`

English:
lemma restrictSubtype_ground_isBasis_iff
  given: {I X : Set M.E}
  proof: by
  rw [restrictSubtype_isBasis_iff]; rw [isBasis'_iff_isBasis]

中文:
引理 restrictSubtype_ground_isBasis_iff
  条件: {I X : 集合 M.E}
  证明: by
  rw [restrictSubtype_isBasis_iff]; rw [isBasis'_iff_isBasis]
-/
@[simp] lemma restrictSubtype_ground_isBasis_iff {I X : Set M.E} :
    (M.restrictSubtype M.E).IsBasis I X ↔ M.IsBasis I X := by
  rw [restrictSubtype_isBasis_iff]; rw [isBasis'_iff_isBasis]

/--
lemma `eq_of_restrictSubtype_eq` / 引理 `eq_of_restrictSubtype_eq`

English:
lemma eq_of_restrictSubtype_eq
  statement: {N : Matroid α} (hM : M.E = E) (hN : N.E = E)
  proof: by
  subst hM
  refine ext_indep (by rw [hN]) (fun I hI => ?_)
  rwa [← restrictSubtype_indep_iff_of_subset hI, h, restrictSubtype_indep_iff_of_subset]

中文:
引理 eq_of_restrictSubtype_eq
  结论: {N : 拟阵 α} (hM : M.E = E) (hN : N.E = E)
  证明: by
  subst hM
  refine ext_indep (by rw [hN]) (fun I hI => ?_)
  rwa [← restrictSubtype_indep_iff_of_subset hI, h, restrictSubtype_indep_iff_of_subset]

Depends on / 依赖: ext_indep, restrictSubtype_indep_iff_of_subset
-/
lemma eq_of_restrictSubtype_eq {N : Matroid α} (hM : M.E = E) (hN : N.E = E)
    (h : M.restrictSubtype E = N.restrictSubtype E) : M = N := by
  subst hM
  refine ext_indep (by rw [hN]) (fun I hI => ?_)
  rwa [← restrictSubtype_indep_iff_of_subset hI, h, restrictSubtype_indep_iff_of_subset]

/--
lemma `restrictSubtype_dual` / 引理 `restrictSubtype_dual`

English:
lemma restrictSubtype_dual
  statement: (M.restrictSubtype M.E)✶ = M✶.restrictSubtype M.E
  proof: by
  rw [restrictSubtype]; rw [← comapOn_preimage_eq]; rw [comapOn_dual_eq_of_bijOn]; rw [restrict_ground_eq_self]; rw [← dual_ground]; rw [comapOn_preimage_eq]; rw [restrictSubtype]; rw [restrict_ground_eq_self]
  exact ⟨by simp [MapsTo], Subtype.val_injective.injOn, by simp [SurjOn]⟩

中文:
引理 restrictSubtype_dual
  结论: (M.restrictSubtype M.E)✶ = M✶.restrictSubtype M.E
  证明: by
  rw [restrictSubtype]; rw [← comapOn_preimage_eq]; rw [comapOn_dual_eq_of_bijOn]; rw [restrict_ground_eq_self]; rw [← dual_ground]; rw [comapOn_preimage_eq]; rw [restrictSubtype]; rw [restrict_ground_eq_self]
  exact ⟨by simp [MapsTo], Subtype.val_injective.injOn, by simp [SurjOn]⟩
-/
@[simp] lemma restrictSubtype_dual : (M.restrictSubtype M.E)✶ = M✶.restrictSubtype M.E := by
  rw [restrictSubtype]; rw [← comapOn_preimage_eq]; rw [comapOn_dual_eq_of_bijOn]; rw [restrict_ground_eq_self]; rw [← dual_ground]; rw [comapOn_preimage_eq]; rw [restrictSubtype]; rw [restrict_ground_eq_self]
  exact ⟨by simp [MapsTo], Subtype.val_injective.injOn, by simp [SurjOn]⟩

/--
lemma `restrictSubtype_dual'` / 引理 `restrictSubtype_dual'`

English:
lemma restrictSubtype_dual'
  given: (hM : M.E = E)
  statement: (M.restrictSubtype E)✶ = M✶.restrictSubtype E
  proof: by
  rw [← hM]; rw [restrictSubtype_dual]

中文:
引理 restrictSubtype_dual'
  条件: (hM : M.E = E)
  结论: (M.restrictSubtype E)✶ = M✶.restrictSubtype E
  证明: by
  rw [← hM]; rw [restrictSubtype_dual]

Depends on / 依赖: restrictSubtype_dual
-/
lemma restrictSubtype_dual' (hM : M.E = E) : (M.restrictSubtype E)✶ = M✶.restrictSubtype E := by
  rw [← hM]; rw [restrictSubtype_dual]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `map_val_restrictSubtype_eq` / 引理 `map_val_restrictSubtype_eq`

English:
lemma map_val_restrictSubtype_eq
  given: (M : Matroid α) (X : Set α)
  proof: by
  simp [restrictSubtype, map_comap]

中文:
引理 map_val_restrictSubtype_eq
  条件: (M : 拟阵 α) (X : 集合 α)
  证明: by
  simp [restrictSubtype, map_comap]
-/
@[simp] lemma map_val_restrictSubtype_eq (M : Matroid α) (X : Set α) :
    (M.restrictSubtype X).map (↑) Subtype.val_injective.injOn = M ↾ X := by
  simp [restrictSubtype, map_comap]

/--
lemma `map_val_restrictSubtype_ground_eq` / 引理 `map_val_restrictSubtype_ground_eq`

English:
lemma map_val_restrictSubtype_ground_eq
  given: (M : Matroid α)
  proof: by
  simp

中文:
引理 map_val_restrictSubtype_ground_eq
  条件: (M : 拟阵 α)
  证明: by
  simp
-/
lemma map_val_restrictSubtype_ground_eq (M : Matroid α) :
    (M.restrictSubtype M.E).map (↑) Subtype.val_injective.injOn = M := by
  simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [M.Finitary]
  signature: {X : Set α}
  body: by
  rw [restrictSubtype]; infer_instance

中文:
实例 [M.Finitary]
  签名: {X : 集合 α}
  定义体: by
  rw [restrictSubtype]; infer_instance

Depends on / 依赖: infer_instance, restrictSubtype
-/
instance [M.Finitary] {X : Set α} : (M.restrictSubtype X).Finitary := by
  rw [restrictSubtype]; infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [M.RankFinite]
  signature: {X : Set α}
  body: by
  rw [restrictSubtype]; infer_instance

中文:
实例 [M.RankFinite]
  签名: {X : 集合 α}
  定义体: by
  rw [restrictSubtype]; infer_instance

Depends on / 依赖: infer_instance, restrictSubtype
-/
instance [M.RankFinite] {X : Set α} : (M.restrictSubtype X).RankFinite := by
  rw [restrictSubtype]; infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [M.Finite]
  signature: : (M.restrictSubtype M.E).Finite
  body: have := M.ground_finite.to_subtype
  ⟨Finite.ground_finite⟩

中文:
实例 [M.有限]
  签名: : (M.restrictSubtype M.E).有限
  定义体: have := M.ground_finite.to_subtype
  ⟨Finite.ground_finite⟩

Depends on / 依赖: Finite, Finite.ground_finite, M.ground_finite.to_subtype, ground_finite, to_subtype
-/
instance [M.Finite] : (M.restrictSubtype M.E).Finite :=
  have := M.ground_finite.to_subtype
  ⟨Finite.ground_finite⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [M.Nonempty]
  signature: : (M.restrictSubtype M.E).Nonempty
  body: have := M.ground_nonempty.coe_sort
  ⟨by simp⟩

中文:
实例 [M.非空]
  签名: : (M.restrictSubtype M.E).非空
  定义体: have := M.ground_nonempty.coe_sort
  ⟨by simp⟩

Depends on / 依赖: M.ground_nonempty.coe_sort, coe_sort, ground_nonempty
-/
instance [M.Nonempty] : (M.restrictSubtype M.E).Nonempty :=
  have := M.ground_nonempty.coe_sort
  ⟨by simp⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [M.RankPos]
  signature: : (M.restrictSubtype M.E).RankPos
  body: by
  obtain ⟨B, hB⟩ := (M.restrictSubtype M.E).exists_isBase
  have hB' : M.IsBase ↑B := by simpa using hB.map Subtype.val_injective.injOn
exact hB.rankPos_of_nonempty by simpa using hB'.nonempty

中文:
实例 [M.RankPos]
  签名: : (M.restrictSubtype M.E).RankPos
  定义体: by
  obtain ⟨B, hB⟩ := (M.restrictSubtype M.E).exists_isBase
  have hB' : M.IsBase ↑B := by simpa using hB.map Subtype.val_injective.injOn
exact hB.rankPos_of_nonempty by simpa using hB'.nonempty

Depends on / 依赖: IsBase, M.IsBase, M.restrictSubtype, Subtype, Subtype.val_injective.injOn, exists_isBase, hB.map, hB.rankPos_of_nonempty, nonempty, rankPos_of_nonempty, restrictSubtype, val_injective
-/
instance [M.RankPos] : (M.restrictSubtype M.E).RankPos := by
  obtain ⟨B, hB⟩ := (M.restrictSubtype M.E).exists_isBase
  have hB' : M.IsBase ↑B := by simpa using hB.map Subtype.val_injective.injOn
exact hB.rankPos_of_nonempty by simpa using hB'.nonempty

end restrictSubtype

end Matroid
