/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jeremy Avigad
-/
module

public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Order.CompleteLattice.Finset
public import Mathlib.Order.Filter.Basic

/-!
# Results relating filters to finiteness

This file proves that finitely many conditions eventually hold if each of them eventually holds.
-/

public section

open Function Set Order
open scoped symmDiff

universe u v w x y

namespace Filter

variable {α : Type u} {f g : Filter α} {s t : Set α}

@[simp]
/--
theorem `biInter_mem` / 定理 `biInter_mem`

English:
theorem biInter_mem
  given: {β : Type v} {s : β -> Set α} {is : Set β} (hf : is.Finite)
  proof: by
  induction is, hf using Set.Finite.induction_on with
  | empty => simp
  | insert _ _ hs => simp [hs]

@[simp]

中文:
定理 bi整数er_mem
  条件: {β : 类型v} {s : β -> 集合 α} {is : 集合 β} (hf : is.有限)
  证明: by
  induction is, hf using Set.Finite.induction_on with
  | empty => simp
  | insert _ _ hs => simp [hs]

@[simp]

Depends on / 依赖: Finite, Set.Finite.induction_on, induction_on, insert
-/
theorem biInter_mem {β : Type v} {s : β -> Set α} {is : Set β} (hf : is.Finite) :
    (⋂ i in is, s i) in f ↔ forall i in is, s i in f := by
  induction is, hf using Set.Finite.induction_on with
  | empty => simp
  | insert _ _ hs => simp [hs]

@[simp]
/--
theorem `biInter_finset_mem` / 定理 `biInter_finset_mem`

English:
theorem biInter_finset_mem
  given: {β : Type v} {s : β -> Set α} (is : Finset β)
  proof: biInter_mem is.finite_toSet

protected alias _root_.Finset.iInter_mem_sets := biInter_finset_mem

@[simp]

中文:
定理 bi整数er_finset_mem
  条件: {β : 类型v} {s : β -> 集合 α} (is : 有限集 β)
  证明: biInter_mem is.finite_toSet

protected alias _root_.Finset.iInter_mem_sets := biInter_finset_mem

@[simp]

Depends on / 依赖: biInter_mem, finite_toSet, is.finite_toSet
-/
theorem biInter_finset_mem {β : Type v} {s : β -> Set α} (is : Finset β) :
    (⋂ i in is, s i) in f ↔ forall i in is, s i in f :=
  biInter_mem is.finite_toSet

protected alias _root_.Finset.iInter_mem_sets := biInter_finset_mem

@[simp]
/--
theorem `sInter_mem` / 定理 `sInter_mem`

English:
theorem sInter_mem
  given: {s : Set (Set α)} (hfin : s.Finite)
  statement: ⋂₀ s in f ↔ forall U in s, U in f
  proof: by
  rw [sInter_eq_biInter]; rw [biInter_mem hfin]

@[simp]

中文:
定理 s整数er_mem
  条件: {s : 集合 (集合 α)} (hfin : s.有限)
  结论: ⋂₀ s in f ↔ 对任意 U in s, U in f
  证明: by
  rw [sInter_eq_biInter]; rw [biInter_mem hfin]

@[simp]

Depends on / 依赖: biInter_mem, sInter_eq_biInter
-/
theorem sInter_mem {s : Set (Set α)} (hfin : s.Finite) : ⋂₀ s in f ↔ forall U in s, U in f := by
  rw [sInter_eq_biInter]; rw [biInter_mem hfin]

@[simp]
/--
theorem `iInter_mem` / 定理 `iInter_mem`

English:
theorem iInter_mem
  given: {β : Sort v} {s : β -> Set α} [Finite β]
  statement: (⋂ i, s i) in f ↔ forall i, s i in f
  proof: (sInter_mem (finite_range _)).trans forall_mem_range

中文:
定理 i整数er_mem
  条件: {β : 类型层 v} {s : β -> 集合 α} [有限 β]
  结论: (⋂ i, s i) in f ↔ 对任意 i, s i in f
  证明: (sInter_mem (finite_range _)).trans forall_mem_range

Depends on / 依赖: finite_range, forall_mem_range, sInter_mem
-/
theorem iInter_mem {β : Sort v} {s : β -> Set α} [Finite β] : (⋂ i, s i) in f ↔ forall i, s i in f :=
  (sInter_mem (finite_range _)).trans forall_mem_range

end Filter


namespace Filter

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type*} {ι : Sort x}

section Lattice

variable {f g : Filter α} {s t : Set α}

/--
theorem `mem_generate_iff` / 定理 `mem_generate_iff`

English:
theorem mem_generate_iff
  given: {s : Set <| Set α} {U : Set α}
  proof: by
  constructor <;> intro h
  · induction h with
    | @basic V V_in =>
      exact ⟨{V}, singleton_subset_iff.2 V_in, finite_singleton _, (sInter_singleton _).subset⟩
    | univ => exact ⟨∅, empty_subset _, finite_empty, subset_univ _⟩
    | superset _ hVW hV =>
      rcases hV with ⟨t, hts, ht, h

中文:
定理 mem_generate_iff
  条件: {s : 集合 <| 集合 α} {U : 集合 α}
  证明: by
  constructor <;> intro h
  · induction h with
    | @basic V V_in =>
      exact ⟨{V}, singleton_subset_iff.2 V_in, finite_singleton _, (sInter_singleton _).subset⟩
    | univ => exact ⟨∅, empty_subset _, finite_empty, subset_univ _⟩
    | superset _ hVW hV =>
      rcases hV with ⟨t, hts, ht, h

Depends on / 依赖: V_in, empty_subset, finite_empty, finite_singleton, ht.union, htV.trans, inter_subset_inter, sInter_singleton, sInter_union, singleton_subset_iff, subset, subset.trans, subset_univ, superset, union_subset
-/
theorem mem_generate_iff {s : Set <| Set α} {U : Set α} :
    U in generate s ↔ exists t subseteq s, Set.Finite t ∧ ⋂₀ t subseteq U := by
  constructor <;> intro h
  · induction h with
    | @basic V V_in =>
      exact ⟨{V}, singleton_subset_iff.2 V_in, finite_singleton _, (sInter_singleton _).subset⟩
    | univ => exact ⟨∅, empty_subset _, finite_empty, subset_univ _⟩
    | superset _ hVW hV =>
      rcases hV with ⟨t, hts, ht, htV⟩
      exact ⟨t, hts, ht, htV.trans hVW⟩
    | inter _ _ hV hW =>
      rcases hV, hW with ⟨⟨t, hts, ht, htV⟩, u, hus, hu, huW⟩
      exact
        ⟨t union u, union_subset hts hus, ht.union hu,
(sInter_union _ _).subset.trans inter_subset_inter htV huW⟩
  · rcases h with ⟨t, hts, tfin, h⟩
    exact mem_of_superset ((sInter_mem tfin).2 fun V hV => GenerateSets.basic <| hts hV) h

/--
theorem `mem_iInf_of_iInter` / 定理 `mem_iInf_of_iInter`

English:
theorem mem_iInf_of_iInter
  statement: {ι} {s : ι -> Filter α} {U : Set α} {I : Set ι} (I_fin : I.Finite)
  proof: by
  have := I_fin.fintype
  refine mem_of_superset (iInter_mem.2 fun i => ?_) hU
  exact mem_iInf_of_mem (i : ι) (hV _)

中文:
定理 mem_iInf_of_i整数er
  结论: {ι} {s : ι -> 滤子 α} {U : 集合 α} {I : 集合 ι} (I_fin : I.有限)
  证明: by
  have := I_fin.fintype
  refine mem_of_superset (iInter_mem.2 fun i => ?_) hU
  exact mem_iInf_of_mem (i : ι) (hV _)

Depends on / 依赖: I_fin, I_fin.fintype, fintype, iInter_mem, mem_iInf_of_mem, mem_of_superset
-/
theorem mem_iInf_of_iInter {ι} {s : ι -> Filter α} {U : Set α} {I : Set ι} (I_fin : I.Finite)
    {V : I -> Set α} (hV : forall (i : I), V i in s i) (hU : ⋂ i, V i subseteq U) : U in ⨅ i, s i := by
  have := I_fin.fintype
  refine mem_of_superset (iInter_mem.2 fun i => ?_) hU
  exact mem_iInf_of_mem (i : ι) (hV _)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mem_iInf` / 定理 `mem_iInf`

English:
theorem mem_iInf
  given: {ι} {s : ι -> Filter α} {U : Set α}
  proof: by
  constructor
  · rw [iInf_eq_generate, mem_generate_iff]
    rintro ⟨t, tsub, tfin, tinter⟩
    rcases eq_finite_iUnion_of_finite_subset_iUnion tfin tsub with ⟨I, Ifin, σ, σfin, σsub, rfl⟩
    rw [sInter_iUnion] at tinter
    set V := fun i => U union ⋂₀ σ i with hV
    have V_in : forall (i : I

中文:
定理 mem_iInf
  条件: {ι} {s : ι -> 滤子 α} {U : 集合 α}
  证明: by
  constructor
  · rw [iInf_eq_generate, mem_generate_iff]
    rintro ⟨t, tsub, tfin, tinter⟩
    rcases eq_finite_iUnion_of_finite_subset_iUnion tfin tsub with ⟨I, Ifin, σ, σfin, σsub, rfl⟩
    rw [sInter_iUnion] at tinter
    set V := fun i => U union ⋂₀ σ i with hV
    have V_in : forall (i : I

Depends on / 依赖: V_in, eq_finite_iUnion_of_finite_subset_iUnion, iInf_eq_generate, mem_generate_iff, mem_of_superset, sInter_iUnion, sInter_mem, subset_union_right, tinter, union_eq_self_of_subset_right, union_iInter
-/
theorem mem_iInf {ι} {s : ι -> Filter α} {U : Set α} :
    (U in ⨅ i, s i) ↔
      exists I : Set ι, I.Finite ∧ exists V : I -> Set α, (forall (i : I), V i in s i) ∧ U = ⋂ i, V i := by
  constructor
  · rw [iInf_eq_generate, mem_generate_iff]
    rintro ⟨t, tsub, tfin, tinter⟩
    rcases eq_finite_iUnion_of_finite_subset_iUnion tfin tsub with ⟨I, Ifin, σ, σfin, σsub, rfl⟩
    rw [sInter_iUnion] at tinter
    set V := fun i => U union ⋂₀ σ i with hV
    have V_in : forall (i : I), V i in s i := by
      rintro i
      have : ⋂₀ σ i in s i := by
        rw [sInter_mem (σfin _)]
        apply σsub
      exact mem_of_superset this subset_union_right
    refine ⟨I, Ifin, V, V_in, ?_⟩
    rwa [hV, ← union_iInter, union_eq_self_of_subset_right]
  · rintro ⟨I, Ifin, V, V_in, rfl⟩
    exact mem_iInf_of_iInter Ifin V_in Subset.rfl

/--
theorem `mem_iInf'` / 定理 `mem_iInf'`

English:
theorem mem_iInf'
  given: {ι} {s : ι -> Filter α} {U : Set α}
  proof: by
  classical
  simp only [mem_iInf, biInter_eq_iInter]
  refine ⟨?_, fun ⟨I, If, V, hVs, _, hVU, _⟩ => ⟨I, If, fun i => V i, fun i => hVs i, hVU⟩⟩
  rintro ⟨I, If, V, hV, rfl⟩
  refine ⟨I, If, fun i => if hi : i in I then V ⟨i, hi⟩ else univ, fun i => ?_, fun i hi => ?_, ?_⟩
  · dsimp only
    spl

中文:
定理 mem_iInf'
  条件: {ι} {s : ι -> 滤子 α} {U : 集合 α}
  证明: by
  classical
  simp only [mem_iInf, biInter_eq_iInter]
  refine ⟨?_, fun ⟨I, If, V, hVs, _, hVU, _⟩ => ⟨I, If, fun i => V i, fun i => hVs i, hVU⟩⟩
  rintro ⟨I, If, V, hV, rfl⟩
  refine ⟨I, If, fun i => if hi : i in I then V ⟨i, hi⟩ else univ, fun i => ?_, fun i hi => ?_, ?_⟩
  · dsimp only
    spl

Depends on / 依赖: Subtype, Subtype.coe_eta, Subtype.coe_prop, biInter_eq_iInter, classical, coe_eta, coe_prop, dif_neg, dif_pos, exacts, iInter_dite, iInter_univ, inter_univ, mem_iInf, split_ifs, true_and, univ_mem
-/
theorem mem_iInf' {ι} {s : ι -> Filter α} {U : Set α} :
    (U in ⨅ i, s i) ↔
      exists I : Set ι, I.Finite ∧ exists V : ι -> Set α, (forall i, V i in s i) ∧
        (forall i ∉ I, V i = univ) ∧ (U = ⋂ i in I, V i) ∧ U = ⋂ i, V i := by
  classical
  simp only [mem_iInf, biInter_eq_iInter]
  refine ⟨?_, fun ⟨I, If, V, hVs, _, hVU, _⟩ => ⟨I, If, fun i => V i, fun i => hVs i, hVU⟩⟩
  rintro ⟨I, If, V, hV, rfl⟩
  refine ⟨I, If, fun i => if hi : i in I then V ⟨i, hi⟩ else univ, fun i => ?_, fun i hi => ?_, ?_⟩
  · dsimp only
    split_ifs
    exacts [hV ⟨i,_⟩, univ_mem]
  · exact dif_neg hi
  · simp only [iInter_dite, biInter_eq_iInter, dif_pos (Subtype.coe_prop _), Subtype.coe_eta,
      iInter_univ, inter_univ, true_and]

/--
theorem `exists_iInter_of_mem_iInf` / 定理 `exists_iInter_of_mem_iInf`

English:
theorem exists_iInter_of_mem_iInf
  statement: {ι : Sort*} {α : Type*} {f : ι -> Filter α} {s}
  proof: by
  rw [← iInf_range' (g := (·))] at hs
  let ⟨_, _, V, hVs, _, _, hVU'⟩ := mem_iInf'.1 hs
  use V ∘ rangeFactorization f, fun i => hVs (rangeFactorization f i)
  rw [hVU']; rw [← rangeFactorization_surjective.iInter_comp]; rw [comp_def]

中文:
定理 存在_i整数er_of_mem_iInf
  结论: {ι : 类型层*} {α : 类型} {f : ι -> 滤子 α} {s}
  证明: by
  rw [← iInf_range' (g := (·))] at hs
  let ⟨_, _, V, hVs, _, _, hVU'⟩ := mem_iInf'.1 hs
  use V ∘ rangeFactorization f, fun i => hVs (rangeFactorization f i)
  rw [hVU']; rw [← rangeFactorization_surjective.iInter_comp]; rw [comp_def]

Depends on / 依赖: comp_def, iInf_range, iInter_comp, mem_iInf, rangeFactorization, rangeFactorization_surjective, rangeFactorization_surjective.iInter_comp
-/
theorem exists_iInter_of_mem_iInf {ι : Sort*} {α : Type*} {f : ι -> Filter α} {s}
    (hs : s in ⨅ i, f i) : exists t : ι -> Set α, (forall i, t i in f i) ∧ s = ⋂ i, t i := by
  rw [← iInf_range' (g := (·))] at hs
  let ⟨_, _, V, hVs, _, _, hVU'⟩ := mem_iInf'.1 hs
  use V ∘ rangeFactorization f, fun i => hVs (rangeFactorization f i)
  rw [hVU']; rw [← rangeFactorization_surjective.iInter_comp]; rw [comp_def]

/--
theorem `mem_iInf_of_finite` / 定理 `mem_iInf_of_finite`

English:
theorem mem_iInf_of_finite
  given: {ι : Sort*} [Finite ι] {α : Type*} {f : ι -> Filter α} (s)
  proof: by
  refine ⟨exists_iInter_of_mem_iInf, ?_⟩
  rintro ⟨t, ht, rfl⟩
  exact iInter_mem.2 fun i => mem_iInf_of_mem i (ht i)

中文:
定理 mem_iInf_of_finite
  条件: {ι : 类型层*} [有限 ι] {α : 类型} {f : ι -> 滤子 α} (s)
  证明: by
  refine ⟨exists_iInter_of_mem_iInf, ?_⟩
  rintro ⟨t, ht, rfl⟩
  exact iInter_mem.2 fun i => mem_iInf_of_mem i (ht i)

Depends on / 依赖: exists_iInter_of_mem_iInf, iInter_mem, mem_iInf_of_mem
-/
theorem mem_iInf_of_finite {ι : Sort*} [Finite ι] {α : Type*} {f : ι -> Filter α} (s) :
    (s in ⨅ i, f i) ↔ exists t : ι -> Set α, (forall i, t i in f i) ∧ s = ⋂ i, t i := by
  refine ⟨exists_iInter_of_mem_iInf, ?_⟩
  rintro ⟨t, ht, rfl⟩
  exact iInter_mem.2 fun i => mem_iInf_of_mem i (ht i)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mem_biInf_principal` / 定理 `mem_biInf_principal`

English:
theorem mem_biInf_principal
  given: {ι : Type*} {p : ι -> Prop} {s : ι -> Set α} {t : Set α}
  proof: by
  constructor
  · simp only [mem_iInf (ι := ι), mem_iInf_of_finite, mem_principal]
    rintro ⟨I, hIf, V, hV₁, hV₂, rfl⟩
    choose! t ht₁ ht₂ using hV₁
    refine ⟨I inter {i | p i}, hIf.inter_of_left _, fun i => And.right, ?_⟩
    simp only [mem_inter_iff, iInter_and, biInter_eq_iInter, ht₂, me

中文:
定理 mem_biInf_principal
  条件: {ι : 类型} {p : ι -> 命题} {s : ι -> 集合 α} {t : 集合 α}
  证明: by
  constructor
  · simp only [mem_iInf (ι := ι), mem_iInf_of_finite, mem_principal]
    rintro ⟨I, hIf, V, hV₁, hV₂, rfl⟩
    choose! t ht₁ ht₂ using hV₁
    refine ⟨I inter {i | p i}, hIf.inter_of_left _, fun i => And.right, ?_⟩
    simp only [mem_inter_iff, iInter_and, biInter_eq_iInter, ht₂, me

Depends on / 依赖: And.right, biInter_eq_iInter, hIf.inter_of_left, iInter_and, inter_of_left, mem_iInf, mem_iInf_of_finite, mem_iInf_of_iInter, mem_inter_iff, mem_ofPred_eq, mem_principal
-/
theorem mem_biInf_principal {ι : Type*} {p : ι -> Prop} {s : ι -> Set α} {t : Set α} :
    t in ⨅ (i : ι) (_ : p i), 𝓟 (s i) ↔
      exists I : Set ι, I.Finite ∧ (forall i in I, p i) ∧ ⋂ i in I, s i subseteq t := by
  constructor
  · simp only [mem_iInf (ι := ι), mem_iInf_of_finite, mem_principal]
    rintro ⟨I, hIf, V, hV₁, hV₂, rfl⟩
    choose! t ht₁ ht₂ using hV₁
    refine ⟨I inter {i | p i}, hIf.inter_of_left _, fun i => And.right, ?_⟩
    simp only [mem_inter_iff, iInter_and, biInter_eq_iInter, ht₂, mem_ofPred_eq]
    gcongr with i hpi
    exact ht₁ i hpi
  · rintro ⟨I, hIf, hpI, hst⟩
    rw [biInter_eq_iInter] at hst
    refine mem_iInf_of_iInter hIf (fun i => ?_) hst
    simp [hpI i i.2]


/--
theorem `_root_.Pairwise.exists_mem_filter_of_disjoint` / 定理 `_root_.Pairwise.exists_mem_filter_of_disjoint`

English:
theorem _root_.Pairwise.exists_mem_filter_of_disjoint
  statement: {ι : Type*} [Finite ι] {l : ι -> Filter α}
  proof: by
  have : Pairwise fun i j => exists (s : {s // s in l i}) (t : {t // t in l j}), Disjoint s.1 t.1 := by
    simpa only [Pairwise, Function.onFun, Filter.disjoint_iff, exists_prop, Subtype.exists] using hd
  choose! s t hst using this
  refine ⟨fun i => ⋂ j, @s i j inter @t j i, fun i => ?_, fun i

中文:
定理 _root_.两两.存在_mem_filter_of_disjoint
  结论: {ι : 类型} [有限 ι] {l : ι -> 滤子 α}
  证明: by
  have : Pairwise fun i j => exists (s : {s // s in l i}) (t : {t // t in l j}), Disjoint s.1 t.1 := by
    simpa only [Pairwise, Function.onFun, Filter.disjoint_iff, exists_prop, Subtype.exists] using hd
  choose! s t hst using this
  refine ⟨fun i => ⋂ j, @s i j inter @t j i, fun i => ?_, fun i

Depends on / 依赖: CommRing, Disjoint, Filter, Filter.disjoint_iff, Function, Function.onFun, IsArtinianRing, IsLocalRing, Pairwise, Subtype, Subtype.exists, disjoint_iff, exacts, exists_prop, iInter_mem, iInter_subset, inter_mem, inter_subset_left, inter_subset_right
-/
theorem _root_.Pairwise.exists_mem_filter_of_disjoint {ι : Type*} [Finite ι] {l : ι -> Filter α}
    (hd : Pairwise (Disjoint on l)) :
    exists s : ι -> Set α, (forall i, s i in l i) ∧ Pairwise (Disjoint on s) := by
  have : Pairwise fun i j => exists (s : {s // s in l i}) (t : {t // t in l j}), Disjoint s.1 t.1 := by
    simpa only [Pairwise, Function.onFun, Filter.disjoint_iff, exists_prop, Subtype.exists] using hd
  choose! s t hst using this
  refine ⟨fun i => ⋂ j, @s i j inter @t j i, fun i => ?_, fun i j hij => ?_⟩
  exacts [iInter_mem.2 fun j => inter_mem (@s i j).2 (@t j i).2,
    (hst hij).mono ((iInter_subset _ j).trans inter_subset_left)
      ((iInter_subset _ i).trans inter_subset_right)]

/--
theorem `_root_.Set.PairwiseDisjoint.exists_mem_filter` / 定理 `_root_.Set.PairwiseDisjoint.exists_mem_filter`

English:
theorem _root_.Set.PairwiseDisjoint.exists_mem_filter
  statement: {ι : Type*} {l : ι -> Filter α} {t : Set ι}
  proof: by
  have := ht.to_subtype
  rcases (hd.subtype _ _).exists_mem_filter_of_disjoint with ⟨s, hsl, hsd⟩
  lift s to (i : t) -> {s // s in l i} using hsl
  rcases @Subtype.exists_pi_extension ι (fun i => { s // s in l i }) _ _ s with ⟨s, rfl⟩
  exact ⟨fun i => s i, fun i => (s i).2, hsd.set_of_subtype 

中文:
定理 _root_.集合.PairwiseDisjoint.存在_mem_filter
  结论: {ι : 类型} {l : ι -> 滤子 α} {t : 集合 ι}
  证明: by
  have := ht.to_subtype
  rcases (hd.subtype _ _).exists_mem_filter_of_disjoint with ⟨s, hsl, hsd⟩
  lift s to (i : t) -> {s // s in l i} using hsl
  rcases @Subtype.exists_pi_extension ι (fun i => { s // s in l i }) _ _ s with ⟨s, rfl⟩
  exact ⟨fun i => s i, fun i => (s i).2, hsd.set_of_subtype 

Depends on / 依赖: Subtype, Subtype.exists_pi_extension, exists_mem_filter_of_disjoint, exists_pi_extension, hd.subtype, hsd.set_of_subtype, ht.to_subtype, set_of_subtype, subtype, to_subtype
-/
theorem _root_.Set.PairwiseDisjoint.exists_mem_filter {ι : Type*} {l : ι -> Filter α} {t : Set ι}
    (hd : t.PairwiseDisjoint l) (ht : t.Finite) :
    exists s : ι -> Set α, (forall i, s i in l i) ∧ t.PairwiseDisjoint s := by
  have := ht.to_subtype
  rcases (hd.subtype _ _).exists_mem_filter_of_disjoint with ⟨s, hsl, hsd⟩
  lift s to (i : t) -> {s // s in l i} using hsl
  rcases @Subtype.exists_pi_extension ι (fun i => { s // s in l i }) _ _ s with ⟨s, rfl⟩
  exact ⟨fun i => s i, fun i => (s i).2, hsd.set_of_subtype _ _⟩


/--
theorem `iInf_sets_eq_finite` / 定理 `iInf_sets_eq_finite`

English:
theorem iInf_sets_eq_finite
  given: {ι : Type*} (f : ι -> Filter α)
  proof: by
  rw [iInf_eq_iInf_finset]; rw [iInf_sets_eq]
  exact directed_of_isDirected_le fun _ _ => biInf_mono

中文:
定理 iInf_sets_eq_finite
  条件: {ι : 类型} (f : ι -> 滤子 α)
  证明: by
  rw [iInf_eq_iInf_finset]; rw [iInf_sets_eq]
  exact directed_of_isDirected_le fun _ _ => biInf_mono

Depends on / 依赖: biInf_mono, directed_of_isDirected_le, iInf_eq_iInf_finset, iInf_sets_eq
-/
theorem iInf_sets_eq_finite {ι : Type*} (f : ι -> Filter α) :
    (⨅ i, f i).sets = ⋃ t : Finset ι, (⨅ i in t, f i).sets := by
  rw [iInf_eq_iInf_finset]; rw [iInf_sets_eq]
  exact directed_of_isDirected_le fun _ _ => biInf_mono

/--
theorem `iInf_sets_eq_finite'` / 定理 `iInf_sets_eq_finite'`

English:
theorem iInf_sets_eq_finite'
  given: (f : ι -> Filter α)
  proof: by
  rw [← iInf_sets_eq_finite]; rw [← Equiv.plift.surjective.iInf_comp]; rw [Equiv.plift_apply]

中文:
定理 iInf_sets_eq_finite'
  条件: (f : ι -> 滤子 α)
  证明: by
  rw [← iInf_sets_eq_finite]; rw [← Equiv.plift.surjective.iInf_comp]; rw [Equiv.plift_apply]

Depends on / 依赖: Equiv.plift.surjective.iInf_comp, Equiv.plift_apply, iInf_comp, iInf_sets_eq_finite, plift_apply, surjective
-/
theorem iInf_sets_eq_finite' (f : ι -> Filter α) :
    (⨅ i, f i).sets = ⋃ t : Finset (PLift ι), (⨅ i in t, f (PLift.down i)).sets := by
  rw [← iInf_sets_eq_finite]; rw [← Equiv.plift.surjective.iInf_comp]; rw [Equiv.plift_apply]

/--
theorem `mem_iInf_finite` / 定理 `mem_iInf_finite`

English:
theorem mem_iInf_finite
  given: {ι : Type*} {f : ι -> Filter α} (s)
  proof: (Set.ext_iff.1 (iInf_sets_eq_finite f) s).trans mem_iUnion

中文:
定理 mem_iInf_finite
  条件: {ι : 类型} {f : ι -> 滤子 α} (s)
  证明: (Set.ext_iff.1 (iInf_sets_eq_finite f) s).trans mem_iUnion

Depends on / 依赖: Set.ext_iff, ext_iff, iInf_sets_eq_finite, mem_iUnion
-/
theorem mem_iInf_finite {ι : Type*} {f : ι -> Filter α} (s) :
    s in iInf f ↔ exists t : Finset ι, s in ⨅ i in t, f i :=
  (Set.ext_iff.1 (iInf_sets_eq_finite f) s).trans mem_iUnion

/--
theorem `mem_iInf_finite'` / 定理 `mem_iInf_finite'`

English:
theorem mem_iInf_finite'
  given: {f : ι -> Filter α} (s)
  proof: (Set.ext_iff.1 (iInf_sets_eq_finite' f) s).trans mem_iUnion

中文:
定理 mem_iInf_finite'
  条件: {f : ι -> 滤子 α} (s)
  证明: (Set.ext_iff.1 (iInf_sets_eq_finite' f) s).trans mem_iUnion

Depends on / 依赖: Set.ext_iff, ext_iff, iInf_sets_eq_finite, mem_iUnion
-/
theorem mem_iInf_finite' {f : ι -> Filter α} (s) :
    s in iInf f ↔ exists t : Finset (PLift ι), s in ⨅ i in t, f (PLift.down i) :=
  (Set.ext_iff.1 (iInf_sets_eq_finite' f) s).trans mem_iUnion

/--
theorem `mem_iInf_finset` / 定理 `mem_iInf_finset`

English:
theorem mem_iInf_finset
  given: {s : Finset α} {f : α -> Filter β} {t : Set β}
  proof: by
  classical
  simp only [← Finset.set_biInter_coe, biInter_eq_iInter, iInf_subtype']
  refine ⟨fun h => ?_, ?_⟩
  · rcases (mem_iInf_of_finite _).1 h with ⟨p, hp, rfl⟩
    refine ⟨fun a => if h : a in s then p ⟨a, h⟩ else univ,
            fun a ha => by simpa [ha] using hp ⟨a, ha⟩, ?_⟩
    refin

中文:
定理 mem_iInf_finset
  条件: {s : 有限集 α} {f : α -> 滤子 β} {t : 集合 β}
  证明: by
  classical
  simp only [← Finset.set_biInter_coe, biInter_eq_iInter, iInf_subtype']
  refine ⟨fun h => ?_, ?_⟩
  · rcases (mem_iInf_of_finite _).1 h with ⟨p, hp, rfl⟩
    refine ⟨fun a => if h : a in s then p ⟨a, h⟩ else univ,
            fun a ha => by simpa [ha] using hp ⟨a, ha⟩, ?_⟩
    refin

Depends on / 依赖: Finset, Finset.set_biInter_coe, biInter_eq_iInter, classical, iInf_subtype, iInter_congr_of_surjective, iInter_mem, mem_iInf_of_finite, mem_iInf_of_mem, set_biInter_coe, surjective_id
-/
theorem mem_iInf_finset {s : Finset α} {f : α -> Filter β} {t : Set β} :
    (t in ⨅ a in s, f a) ↔ exists p : α -> Set β, (forall a in s, p a in f a) ∧ t = ⋂ a in s, p a := by
  classical
  simp only [← Finset.set_biInter_coe, biInter_eq_iInter, iInf_subtype']
  refine ⟨fun h => ?_, ?_⟩
  · rcases (mem_iInf_of_finite _).1 h with ⟨p, hp, rfl⟩
    refine ⟨fun a => if h : a in s then p ⟨a, h⟩ else univ,
            fun a ha => by simpa [ha] using hp ⟨a, ha⟩, ?_⟩
    refine iInter_congr_of_surjective id surjective_id ?_
    rintro ⟨a, ha⟩
    simp [ha]
  · rintro ⟨p, hpf, rfl⟩
    exact iInter_mem.2 fun a => mem_iInf_of_mem a (hpf a a.2)

/-! #### `principal` equations -/

@[simp]
/--
theorem `iInf_principal_finset` / 定理 `iInf_principal_finset`

English:
theorem iInf_principal_finset
  given: {ι : Type w} (s : Finset ι) (f : ι -> Set α)
  proof: by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s _ hs => rw [Finset.iInf_insert, Finset.set_biInter_insert, hs, inf_principal]

中文:
定理 iInf_principal_finset
  条件: {ι : 类型 w} (s : 有限集 ι) (f : ι -> 集合 α)
  证明: by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s _ hs => rw [Finset.iInf_insert, Finset.set_biInter_insert, hs, inf_principal]

Depends on / 依赖: Finset, Finset.iInf_insert, Finset.induction_on, Finset.set_biInter_insert, classical, iInf_insert, induction_on, inf_principal, insert, set_biInter_insert
-/
theorem iInf_principal_finset {ι : Type w} (s : Finset ι) (f : ι -> Set α) :
    ⨅ i in s, 𝓟 (f i) = 𝓟 (⋂ i in s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s _ hs => rw [Finset.iInf_insert, Finset.set_biInter_insert, hs, inf_principal]

/--
theorem `iInf_principal` / 定理 `iInf_principal`

English:
theorem iInf_principal
  given: {ι : Sort w} [Finite ι] (f : ι -> Set α)
  statement: ⨅ i, 𝓟 (f i) = 𝓟 (⋂ i, f i)
  proof: by
  cases nonempty_fintype (PLift ι)
  rw [← iInf_plift_down]; rw [← iInter_plift_down]
  simpa using iInf_principal_finset Finset.univ (f <| PLift.down ·)

中文:
定理 iInf_principal
  条件: {ι : 类型层 w} [有限 ι] (f : ι -> 集合 α)
  结论: ⨅ i, 𝓟 (f i) = 𝓟 (⋂ i, f i)
  证明: by
  cases nonempty_fintype (PLift ι)
  rw [← iInf_plift_down]; rw [← iInter_plift_down]
  simpa using iInf_principal_finset Finset.univ (f <| PLift.down ·)

Depends on / 依赖: Finset, Finset.univ, PLift.down, iInf_plift_down, iInf_principal_finset, iInter_plift_down, nonempty_fintype
-/
theorem iInf_principal {ι : Sort w} [Finite ι] (f : ι -> Set α) : ⨅ i, 𝓟 (f i) = 𝓟 (⋂ i, f i) := by
  cases nonempty_fintype (PLift ι)
  rw [← iInf_plift_down]; rw [← iInter_plift_down]
  simpa using iInf_principal_finset Finset.univ (f <| PLift.down ·)

/-- A special case of `iInf_principal` that is safe to mark `simp`. -/
@[simp]
/--
theorem `iInf_principal'` / 定理 `iInf_principal'`

English:
theorem iInf_principal'
  given: {ι : Type w} [Finite ι] (f : ι -> Set α)
  statement: ⨅ i, 𝓟 (f i) = 𝓟 (⋂ i, f i)
  proof: iInf_principal _

中文:
定理 iInf_principal'
  条件: {ι : 类型 w} [有限 ι] (f : ι -> 集合 α)
  结论: ⨅ i, 𝓟 (f i) = 𝓟 (⋂ i, f i)
  证明: iInf_principal _

Depends on / 依赖: iInf_principal
-/
theorem iInf_principal' {ι : Type w} [Finite ι] (f : ι -> Set α) : ⨅ i, 𝓟 (f i) = 𝓟 (⋂ i, f i) :=
  iInf_principal _

/--
theorem `iInf_principal_finite` / 定理 `iInf_principal_finite`

English:
theorem iInf_principal_finite
  given: {ι : Type w} {s : Set ι} (hs : s.Finite) (f : ι -> Set α)
  proof: by
  lift s to Finset ι using hs
  exact mod_cast iInf_principal_finset s f

中文:
定理 iInf_principal_finite
  条件: {ι : 类型 w} {s : 集合 ι} (hs : s.有限) (f : ι -> 集合 α)
  证明: by
  lift s to Finset ι using hs
  exact mod_cast iInf_principal_finset s f

Depends on / 依赖: Finset, iInf_principal_finset, mod_cast
-/
theorem iInf_principal_finite {ι : Type w} {s : Set ι} (hs : s.Finite) (f : ι -> Set α) :
    ⨅ i in s, 𝓟 (f i) = 𝓟 (⋂ i in s, f i) := by
  lift s to Finset ι using hs
  exact mod_cast iInf_principal_finset s f

/--
theorem `eq_principal_of_finite_sets` / 定理 `eq_principal_of_finite_sets`

English:
theorem eq_principal_of_finite_sets
  given: (hf : f.sets.Finite)
  statement: exists s, f = 𝓟 s
  proof: by
  use ⋂₀ f.sets
  exact Filter.ext fun B => ⟨sInter_subset_of_mem, mem_of_superset ((sInter_mem hf).2 (by simp))⟩

中文:
定理 eq_principal_of_finite_sets
  条件: (hf : f.sets.有限)
  结论: 存在 s, f = 𝓟 s
  证明: by
  use ⋂₀ f.sets
  exact Filter.ext fun B => ⟨sInter_subset_of_mem, mem_of_superset ((sInter_mem hf).2 (by simp))⟩

Depends on / 依赖: Filter, Filter.ext, f.sets, mem_of_superset, sInter_mem, sInter_subset_of_mem
-/
theorem eq_principal_of_finite_sets (hf : f.sets.Finite) : exists s, f = 𝓟 s := by
  use ⋂₀ f.sets
  exact Filter.ext fun B => ⟨sInter_subset_of_mem, mem_of_superset ((sInter_mem hf).2 (by simp))⟩

/--
theorem `eq_principal_of_finite` / 定理 `eq_principal_of_finite`

English:
theorem eq_principal_of_finite
  given: [Finite α] (f : Filter α)
  statement: exists s, f = 𝓟 s
  proof: eq_principal_of_finite_sets (finite_univ.powerset.subset (by simp))

中文:
定理 eq_principal_of_finite
  条件: [有限 α] (f : 滤子 α)
  结论: 存在 s, f = 𝓟 s
  证明: eq_principal_of_finite_sets (finite_univ.powerset.subset (by simp))

Depends on / 依赖: eq_principal_of_finite_sets, finite_univ, finite_univ.powerset.subset, powerset, subset
-/
theorem eq_principal_of_finite [Finite α] (f : Filter α) : exists s, f = 𝓟 s :=
  eq_principal_of_finite_sets (finite_univ.powerset.subset (by simp))

/--
theorem `principal_surjective` / 定理 `principal_surjective`

English:
theorem principal_surjective
  given: [Finite α]
  statement: Surjective (𝓟 : Set α -> Filter α)
  proof: fun f => (eq_principal_of_finite f).imp fun _ => .symm

中文:
定理 principal_surjective
  条件: [有限 α]
  结论: 满射 (𝓟 : 集合 α -> 滤子 α)
  证明: fun f => (eq_principal_of_finite f).imp fun _ => .symm

Depends on / 依赖: eq_principal_of_finite
-/
theorem principal_surjective [Finite α] : Surjective (𝓟 : Set α -> Filter α) :=
  fun f => (eq_principal_of_finite f).imp fun _ => .symm

end Lattice

/-! ### Eventually and Frequently -/

@[simp]
/--
theorem `eventually_all` / 定理 `eventually_all`

English:
theorem eventually_all
  given: {ι : Sort*} [Finite ι] {l} {p : ι -> α -> Prop}
  proof: by
  simpa only [Filter.Eventually, ofPred_forall] using iInter_mem

@[simp]

中文:
定理 eventually_all
  条件: {ι : 类型层*} [有限 ι] {l} {p : ι -> α -> 命题}
  证明: by
  simpa only [Filter.Eventually, ofPred_forall] using iInter_mem

@[simp]

Depends on / 依赖: Eventually, Filter, Filter.Eventually, iInter_mem, ofPred_forall
-/
theorem eventually_all {ι : Sort*} [Finite ι] {l} {p : ι -> α -> Prop} :
    (forallᶠ x in l, forall i, p i x) ↔ forall i, forallᶠ x in l, p i x := by
  simpa only [Filter.Eventually, ofPred_forall] using iInter_mem

@[simp]
/--
theorem `eventually_all_finite` / 定理 `eventually_all_finite`

English:
theorem eventually_all_finite
  given: {ι} {I : Set ι} (hI : I.Finite) {l} {p : ι -> α -> Prop}
  proof: by
  simpa only [Filter.Eventually, ofPred_forall] using biInter_mem hI

protected alias _root_.Set.Finite.eventually_all := eventually_all_finite

中文:
定理 eventually_all_finite
  条件: {ι} {I : 集合 ι} (hI : I.有限) {l} {p : ι -> α -> 命题}
  证明: by
  simpa only [Filter.Eventually, ofPred_forall] using biInter_mem hI

protected alias _root_.Set.Finite.eventually_all := eventually_all_finite

Depends on / 依赖: Eventually, Filter, Filter.Eventually, biInter_mem, ofPred_forall
-/
theorem eventually_all_finite {ι} {I : Set ι} (hI : I.Finite) {l} {p : ι -> α -> Prop} :
    (forallᶠ x in l, forall i in I, p i x) ↔ forall i in I, forallᶠ x in l, p i x := by
  simpa only [Filter.Eventually, ofPred_forall] using biInter_mem hI

protected alias _root_.Set.Finite.eventually_all := eventually_all_finite

/--
theorem `eventually_all_finset` / 定理 `eventually_all_finset`

English:
theorem eventually_all_finset
  given: {ι} (I : Finset ι) {l} {p : ι -> α -> Prop}
  proof: I.finite_toSet.eventually_all

protected alias _root_.Finset.eventually_all := eventually_all_finset

@[simp]

中文:
定理 eventually_all_finset
  条件: {ι} (I : 有限集 ι) {l} {p : ι -> α -> 命题}
  证明: I.finite_toSet.eventually_all

protected alias _root_.Finset.eventually_all := eventually_all_finset

@[simp]
-/
@[simp] theorem eventually_all_finset {ι} (I : Finset ι) {l} {p : ι -> α -> Prop} :
    (forallᶠ x in l, forall i in I, p i x) ↔ forall i in I, forallᶠ x in l, p i x :=
  I.finite_toSet.eventually_all

protected alias _root_.Finset.eventually_all := eventually_all_finset

@[simp]
/--
theorem `frequently_exists` / 定理 `frequently_exists`

English:
theorem frequently_exists
  given: {ι : Sort*} [Finite ι] {l} {p : ι -> α -> Prop}
  proof: by
  rw [← not_iff_not]
  simp

@[simp]

中文:
定理 frequently_存在
  条件: {ι : 类型层*} [有限 ι] {l} {p : ι -> α -> 命题}
  证明: by
  rw [← not_iff_not]
  simp

@[simp]

Depends on / 依赖: not_iff_not
-/
theorem frequently_exists {ι : Sort*} [Finite ι] {l} {p : ι -> α -> Prop} :
    (existsᶠ x in l, exists i, p i x) ↔ exists i, existsᶠ x in l, p i x := by
  rw [← not_iff_not]
  simp

@[simp]
/--
theorem `frequently_exists_finite` / 定理 `frequently_exists_finite`

English:
theorem frequently_exists_finite
  given: {ι} {I : Set ι} (hI : I.Finite) {l} {p : ι -> α -> Prop}
  proof: by
  rw [← not_iff_not]
  simp [hI]

protected alias _root_.Set.Finite.frequently_exists := frequently_exists_finite

中文:
定理 frequently_存在_finite
  条件: {ι} {I : 集合 ι} (hI : I.有限) {l} {p : ι -> α -> 命题}
  证明: by
  rw [← not_iff_not]
  simp [hI]

protected alias _root_.Set.Finite.frequently_exists := frequently_exists_finite

Depends on / 依赖: not_iff_not
-/
theorem frequently_exists_finite {ι} {I : Set ι} (hI : I.Finite) {l} {p : ι -> α -> Prop} :
    (existsᶠ x in l, exists i in I, p i x) ↔ exists i in I, existsᶠ x in l, p i x := by
  rw [← not_iff_not]
  simp [hI]

protected alias _root_.Set.Finite.frequently_exists := frequently_exists_finite

/--
theorem `frequently_exists_finset` / 定理 `frequently_exists_finset`

English:
theorem frequently_exists_finset
  given: {ι} (I : Finset ι) {l} {p : ι -> α -> Prop}
  proof: I.finite_toSet.frequently_exists

protected alias _root_.Finset.frequently_exists := frequently_exists_finset

中文:
定理 frequently_存在_finset
  条件: {ι} (I : 有限集 ι) {l} {p : ι -> α -> 命题}
  证明: I.finite_toSet.frequently_exists

protected alias _root_.Finset.frequently_exists := frequently_exists_finset
-/
@[simp] theorem frequently_exists_finset {ι} (I : Finset ι) {l} {p : ι -> α -> Prop} :
    (existsᶠ x in l, exists i in I, p i x) ↔ exists i in I, existsᶠ x in l, p i x :=
  I.finite_toSet.frequently_exists

protected alias _root_.Finset.frequently_exists := frequently_exists_finset

/--
lemma `eventually_subset_of_finite` / 引理 `eventually_subset_of_finite`

English:
lemma eventually_subset_of_finite
  statement: {ι : Type*} {f : Filter ι} {s : ι -> Set α} {t : Set α}
  proof: by
  simpa [Set.subset_def, eventually_all_finite ht] using hs

中文:
引理 eventually_subset_of_finite
  结论: {ι : 类型} {f : 滤子 ι} {s : ι -> 集合 α} {t : 集合 α}
  证明: by
  simpa [Set.subset_def, eventually_all_finite ht] using hs

Depends on / 依赖: Set.subset_def, eventually_all_finite, subset_def
-/
lemma eventually_subset_of_finite {ι : Type*} {f : Filter ι} {s : ι -> Set α} {t : Set α}
    (ht : t.Finite) (hs : forall a in t, forallᶠ i in f, a in s i) : forallᶠ i in f, t subseteq s i := by
  simpa [Set.subset_def, eventually_all_finite ht] using hs

/-!
### Relation “eventually equal”
-/

section EventuallyEq
variable {l : Filter α} {f g : α -> β}

variable {l : Filter α}

/--
lemma `EventuallyLE.iUnion` / 引理 `EventuallyLE.iUnion`

English:
lemma EventuallyLE.iUnion
  statement: [Finite ι] {s t : ι -> Set α}
  proof: (eventually_all.2 h).mono fun _x hx hx' =>
    let ⟨i, hi⟩ := mem_iUnion.1 hx'; mem_iUnion.2 ⟨i, hx i hi⟩

中文:
引理 EventuallyLE.iUnion
  结论: [有限 ι] {s t : ι -> 集合 α}
  证明: (eventually_all.2 h).mono fun _x hx hx' =>
    let ⟨i, hi⟩ := mem_iUnion.1 hx'; mem_iUnion.2 ⟨i, hx i hi⟩
-/
protected lemma EventuallyLE.iUnion [Finite ι] {s t : ι -> Set α}
    (h : forall i, s i <=ᶠ[l] t i) : (⋃ i, s i) <=ᶠ[l] ⋃ i, t i :=
  (eventually_all.2 h).mono fun _x hx hx' =>
    let ⟨i, hi⟩ := mem_iUnion.1 hx'; mem_iUnion.2 ⟨i, hx i hi⟩

/--
lemma `EventuallyEq.iUnion` / 引理 `EventuallyEq.iUnion`

English:
lemma EventuallyEq.iUnion
  statement: [Finite ι] {s t : ι -> Set α}
  proof: (EventuallyLE.iUnion fun i => (h i).le).antisymm .iUnion fun i => (h i).symm.le

中文:
引理 EventuallyEq.iUnion
  结论: [有限 ι] {s t : ι -> 集合 α}
  证明: (EventuallyLE.iUnion fun i => (h i).le).antisymm .iUnion fun i => (h i).symm.le
-/
protected lemma EventuallyEq.iUnion [Finite ι] {s t : ι -> Set α}
    (h : forall i, s i =ᶠ[l] t i) : (⋃ i, s i) =ᶠ[l] ⋃ i, t i :=
(EventuallyLE.iUnion fun i => (h i).le).antisymm .iUnion fun i => (h i).symm.le

/--
lemma `EventuallyLE.iInter` / 引理 `EventuallyLE.iInter`

English:
lemma EventuallyLE.iInter
  statement: [Finite ι] {s t : ι -> Set α}
  proof: (eventually_all.2 h).mono fun _x hx hx' => mem_iInter.2 fun i => hx i (mem_iInter.1 hx' i)

中文:
引理 EventuallyLE.i整数er
  结论: [有限 ι] {s t : ι -> 集合 α}
  证明: (eventually_all.2 h).mono fun _x hx hx' => mem_iInter.2 fun i => hx i (mem_iInter.1 hx' i)
-/
protected lemma EventuallyLE.iInter [Finite ι] {s t : ι -> Set α}
    (h : forall i, s i <=ᶠ[l] t i) : (⋂ i, s i) <=ᶠ[l] ⋂ i, t i :=
  (eventually_all.2 h).mono fun _x hx hx' => mem_iInter.2 fun i => hx i (mem_iInter.1 hx' i)

/--
lemma `EventuallyEq.iInter` / 引理 `EventuallyEq.iInter`

English:
lemma EventuallyEq.iInter
  statement: [Finite ι] {s t : ι -> Set α}
  proof: (EventuallyLE.iInter fun i => (h i).le).antisymm .iInter fun i => (h i).symm.le

中文:
引理 EventuallyEq.i整数er
  结论: [有限 ι] {s t : ι -> 集合 α}
  证明: (EventuallyLE.iInter fun i => (h i).le).antisymm .iInter fun i => (h i).symm.le
-/
protected lemma EventuallyEq.iInter [Finite ι] {s t : ι -> Set α}
    (h : forall i, s i =ᶠ[l] t i) : (⋂ i, s i) =ᶠ[l] ⋂ i, t i :=
(EventuallyLE.iInter fun i => (h i).le).antisymm .iInter fun i => (h i).symm.le

/--
lemma `_root_.Set.Finite.eventuallyLE_iUnion` / 引理 `_root_.Set.Finite.eventuallyLE_iUnion`

English:
lemma _root_.Set.Finite.eventuallyLE_iUnion
  statement: {ι : Type*} {s : Set ι} (hs : s.Finite)
  proof: by
  have := hs.to_subtype
  rw [biUnion_eq_iUnion]; rw [biUnion_eq_iUnion]
  exact .iUnion fun i => hle i.1 i.2

alias EventuallyLE.biUnion := Set.Finite.eventuallyLE_iUnion

中文:
引理 _root_.集合.有限.eventuallyLE_iUnion
  结论: {ι : 类型} {s : 集合 ι} (hs : s.有限)
  证明: by
  have := hs.to_subtype
  rw [biUnion_eq_iUnion]; rw [biUnion_eq_iUnion]
  exact .iUnion fun i => hle i.1 i.2

alias EventuallyLE.biUnion := Set.Finite.eventuallyLE_iUnion

Depends on / 依赖: biUnion_eq_iUnion, hs.to_subtype, iUnion, to_subtype
-/
lemma _root_.Set.Finite.eventuallyLE_iUnion {ι : Type*} {s : Set ι} (hs : s.Finite)
    {f g : ι -> Set α} (hle : forall i in s, f i <=ᶠ[l] g i) : (⋃ i in s, f i) <=ᶠ[l] (⋃ i in s, g i) := by
  have := hs.to_subtype
  rw [biUnion_eq_iUnion]; rw [biUnion_eq_iUnion]
  exact .iUnion fun i => hle i.1 i.2

alias EventuallyLE.biUnion := Set.Finite.eventuallyLE_iUnion

/--
lemma `_root_.Set.Finite.eventuallyEq_iUnion` / 引理 `_root_.Set.Finite.eventuallyEq_iUnion`

English:
lemma _root_.Set.Finite.eventuallyEq_iUnion
  statement: {ι : Type*} {s : Set ι} (hs : s.Finite)
  proof: (EventuallyLE.biUnion hs fun i hi => (heq i hi).le).antisymm
    .biUnion hs fun i hi => (heq i hi).symm.le

alias EventuallyEq.biUnion := Set.Finite.eventuallyEq_iUnion

中文:
引理 _root_.集合.有限.eventuallyEq_iUnion
  结论: {ι : 类型} {s : 集合 ι} (hs : s.有限)
  证明: (EventuallyLE.biUnion hs fun i hi => (heq i hi).le).antisymm
    .biUnion hs fun i hi => (heq i hi).symm.le

alias EventuallyEq.biUnion := Set.Finite.eventuallyEq_iUnion

Depends on / 依赖: EventuallyLE, EventuallyLE.biUnion, antisymm, biUnion, symm.le
-/
lemma _root_.Set.Finite.eventuallyEq_iUnion {ι : Type*} {s : Set ι} (hs : s.Finite)
    {f g : ι -> Set α} (heq : forall i in s, f i =ᶠ[l] g i) : (⋃ i in s, f i) =ᶠ[l] (⋃ i in s, g i) :=
(EventuallyLE.biUnion hs fun i hi => (heq i hi).le).antisymm
    .biUnion hs fun i hi => (heq i hi).symm.le

alias EventuallyEq.biUnion := Set.Finite.eventuallyEq_iUnion

/--
lemma `_root_.Set.Finite.eventuallyLE_iInter` / 引理 `_root_.Set.Finite.eventuallyLE_iInter`

English:
lemma _root_.Set.Finite.eventuallyLE_iInter
  statement: {ι : Type*} {s : Set ι} (hs : s.Finite)
  proof: by
  have := hs.to_subtype
  rw [biInter_eq_iInter]; rw [biInter_eq_iInter]
  exact .iInter fun i => hle i.1 i.2

alias EventuallyLE.biInter := Set.Finite.eventuallyLE_iInter

中文:
引理 _root_.集合.有限.eventuallyLE_i整数er
  结论: {ι : 类型} {s : 集合 ι} (hs : s.有限)
  证明: by
  have := hs.to_subtype
  rw [biInter_eq_iInter]; rw [biInter_eq_iInter]
  exact .iInter fun i => hle i.1 i.2

alias EventuallyLE.biInter := Set.Finite.eventuallyLE_iInter

Depends on / 依赖: biInter_eq_iInter, hs.to_subtype, iInter, to_subtype
-/
lemma _root_.Set.Finite.eventuallyLE_iInter {ι : Type*} {s : Set ι} (hs : s.Finite)
    {f g : ι -> Set α} (hle : forall i in s, f i <=ᶠ[l] g i) : (⋂ i in s, f i) <=ᶠ[l] (⋂ i in s, g i) := by
  have := hs.to_subtype
  rw [biInter_eq_iInter]; rw [biInter_eq_iInter]
  exact .iInter fun i => hle i.1 i.2

alias EventuallyLE.biInter := Set.Finite.eventuallyLE_iInter

/--
lemma `_root_.Set.Finite.eventuallyEq_iInter` / 引理 `_root_.Set.Finite.eventuallyEq_iInter`

English:
lemma _root_.Set.Finite.eventuallyEq_iInter
  statement: {ι : Type*} {s : Set ι} (hs : s.Finite)
  proof: (EventuallyLE.biInter hs fun i hi => (heq i hi).le).antisymm
    .biInter hs fun i hi => (heq i hi).symm.le

alias EventuallyEq.biInter := Set.Finite.eventuallyEq_iInter

中文:
引理 _root_.集合.有限.eventuallyEq_i整数er
  结论: {ι : 类型} {s : 集合 ι} (hs : s.有限)
  证明: (EventuallyLE.biInter hs fun i hi => (heq i hi).le).antisymm
    .biInter hs fun i hi => (heq i hi).symm.le

alias EventuallyEq.biInter := Set.Finite.eventuallyEq_iInter

Depends on / 依赖: EventuallyLE, EventuallyLE.biInter, antisymm, biInter, symm.le
-/
lemma _root_.Set.Finite.eventuallyEq_iInter {ι : Type*} {s : Set ι} (hs : s.Finite)
    {f g : ι -> Set α} (heq : forall i in s, f i =ᶠ[l] g i) : (⋂ i in s, f i) =ᶠ[l] (⋂ i in s, g i) :=
(EventuallyLE.biInter hs fun i hi => (heq i hi).le).antisymm
    .biInter hs fun i hi => (heq i hi).symm.le

alias EventuallyEq.biInter := Set.Finite.eventuallyEq_iInter

/--
lemma `_root_.Finset.eventuallyLE_iUnion` / 引理 `_root_.Finset.eventuallyLE_iUnion`

English:
lemma _root_.Finset.eventuallyLE_iUnion
  statement: {ι : Type*} (s : Finset ι) {f g : ι -> Set α}
  proof: .biUnion s.finite_toSet hle

中文:
引理 _root_.有限集.eventuallyLE_iUnion
  结论: {ι : 类型} (s : 有限集 ι) {f g : ι -> 集合 α}
  证明: .biUnion s.finite_toSet hle

Depends on / 依赖: biUnion, finite_toSet, s.finite_toSet
-/
lemma _root_.Finset.eventuallyLE_iUnion {ι : Type*} (s : Finset ι) {f g : ι -> Set α}
    (hle : forall i in s, f i <=ᶠ[l] g i) : (⋃ i in s, f i) <=ᶠ[l] (⋃ i in s, g i) :=
  .biUnion s.finite_toSet hle

/--
lemma `_root_.Finset.eventuallyEq_iUnion` / 引理 `_root_.Finset.eventuallyEq_iUnion`

English:
lemma _root_.Finset.eventuallyEq_iUnion
  statement: {ι : Type*} (s : Finset ι) {f g : ι -> Set α}
  proof: .biUnion s.finite_toSet heq

中文:
引理 _root_.有限集.eventuallyEq_iUnion
  结论: {ι : 类型} (s : 有限集 ι) {f g : ι -> 集合 α}
  证明: .biUnion s.finite_toSet heq

Depends on / 依赖: biUnion, finite_toSet, s.finite_toSet
-/
lemma _root_.Finset.eventuallyEq_iUnion {ι : Type*} (s : Finset ι) {f g : ι -> Set α}
    (heq : forall i in s, f i =ᶠ[l] g i) : (⋃ i in s, f i) =ᶠ[l] (⋃ i in s, g i) :=
  .biUnion s.finite_toSet heq

/--
lemma `_root_.Finset.eventuallyLE_iInter` / 引理 `_root_.Finset.eventuallyLE_iInter`

English:
lemma _root_.Finset.eventuallyLE_iInter
  statement: {ι : Type*} (s : Finset ι) {f g : ι -> Set α}
  proof: .biInter s.finite_toSet hle

中文:
引理 _root_.有限集.eventuallyLE_i整数er
  结论: {ι : 类型} (s : 有限集 ι) {f g : ι -> 集合 α}
  证明: .biInter s.finite_toSet hle

Depends on / 依赖: biInter, finite_toSet, s.finite_toSet
-/
lemma _root_.Finset.eventuallyLE_iInter {ι : Type*} (s : Finset ι) {f g : ι -> Set α}
    (hle : forall i in s, f i <=ᶠ[l] g i) : (⋂ i in s, f i) <=ᶠ[l] (⋂ i in s, g i) :=
  .biInter s.finite_toSet hle

/--
lemma `_root_.Finset.eventuallyEq_iInter` / 引理 `_root_.Finset.eventuallyEq_iInter`

English:
lemma _root_.Finset.eventuallyEq_iInter
  statement: {ι : Type*} (s : Finset ι) {f g : ι -> Set α}
  proof: .biInter s.finite_toSet heq

中文:
引理 _root_.有限集.eventuallyEq_i整数er
  结论: {ι : 类型} (s : 有限集 ι) {f g : ι -> 集合 α}
  证明: .biInter s.finite_toSet heq

Depends on / 依赖: biInter, finite_toSet, s.finite_toSet
-/
lemma _root_.Finset.eventuallyEq_iInter {ι : Type*} (s : Finset ι) {f g : ι -> Set α}
    (heq : forall i in s, f i =ᶠ[l] g i) : (⋂ i in s, f i) =ᶠ[l] (⋂ i in s, g i) :=
  .biInter s.finite_toSet heq

end EventuallyEq

end Filter
