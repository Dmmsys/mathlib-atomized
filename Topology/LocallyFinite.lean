/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Order.Filter.SmallSets
public import Mathlib.Topology.ContinuousOn

/-!
### Locally finite families of sets

We say that a family of sets in a topological space is *locally finite* if at every point `x : X`,
there is a neighborhood of `x` which meets only finitely many sets in the family.

In this file we give the definition and prove basic properties of locally finite families of sets.
-/

@[expose] public section

-- locally finite family [General Topology (Bourbaki, 1995)]
open Set Function Filter Topology

variable {ι ι' α X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f g : ι -> Set X}

/--
Definition of `LocallyFinite` / `LocallyFinite` 的定义

English:
definition LocallyFinite
  signature: (f : ι -> Set X)
  body: forall x : X, exists t in 𝓝 x, { i | (f i inter t).Nonempty }.Finite

中文:
定义 LocallyFinite
  签名: (f : ι -> Set X)
  定义体: forall x : X, exists t in 𝓝 x, { i | (f i inter t).Nonempty }.Finite

Depends on / 依赖: Finite, Nonempty
-/
def LocallyFinite (f : ι -> Set X) :=
  forall x : X, exists t in 𝓝 x, { i | (f i inter t).Nonempty }.Finite

/--
theorem `locallyFinite_of_finite` / 定理 `locallyFinite_of_finite`

English:
theorem locallyFinite_of_finite
  given: [Finite ι] (f : ι -> Set X)
  statement: LocallyFinite f
  proof: fun _ =>
  ⟨univ, univ_mem, toFinite _⟩

中文:
定理 locallyFinite_of_finite
  条件: [Finite ι] (f : ι -> Set X)
  结论: LocallyFinite f
  证明: fun _ =>
  ⟨univ, univ_mem, toFinite _⟩
-/
theorem locallyFinite_of_finite [Finite ι] (f : ι -> Set X) : LocallyFinite f := fun _ =>
  ⟨univ, univ_mem, toFinite _⟩

namespace LocallyFinite

/--
theorem `point_finite` / 定理 `point_finite`

English:
theorem point_finite
  given: (hf : LocallyFinite f) (x : X)
  statement: { b | x in f b }.Finite
  proof: let ⟨_t, hxt, ht⟩ := hf x
  ht.subset fun _b hb => ⟨x, hb, mem_of_mem_nhds hxt⟩

中文:
定理 point_finite
  条件: (hf : LocallyFinite f) (x : X)
  结论: { b | x in f b }.Finite
  证明: let ⟨_t, hxt, ht⟩ := hf x
  ht.subset fun _b hb => ⟨x, hb, mem_of_mem_nhds hxt⟩

Depends on / 依赖: ht.subset, mem_of_mem_nhds, subset
-/
theorem point_finite (hf : LocallyFinite f) (x : X) : { b | x in f b }.Finite :=
  let ⟨_t, hxt, ht⟩ := hf x
  ht.subset fun _b hb => ⟨x, hb, mem_of_mem_nhds hxt⟩

/--
theorem `subset` / 定理 `subset`

English:
theorem subset
  given: (hf : LocallyFinite f) (hg : forall i, g i subseteq f i)
  statement: LocallyFinite g
  proof: fun a =>
  let ⟨t, ht₁, ht₂⟩ := hf a
⟨t, ht₁, ht₂.subset fun i hi => hi.mono inter_subset_inter (hg i) Subset.rfl⟩

中文:
定理 subset
  条件: (hf : LocallyFinite f) (hg : 对任意 i, g i subseteq f i)
  结论: LocallyFinite g
  证明: fun a =>
  let ⟨t, ht₁, ht₂⟩ := hf a
⟨t, ht₁, ht₂.subset fun i hi => hi.mono inter_subset_inter (hg i) Subset.rfl⟩
-/
protected theorem subset (hf : LocallyFinite f) (hg : forall i, g i subseteq f i) : LocallyFinite g := fun a =>
  let ⟨t, ht₁, ht₂⟩ := hf a
⟨t, ht₁, ht₂.subset fun i hi => hi.mono inter_subset_inter (hg i) Subset.rfl⟩

/--
theorem `comp_injOn` / 定理 `comp_injOn`

English:
theorem comp_injOn
  given: {g : ι' -> ι} (hf : LocallyFinite f) (hg : InjOn g { i | (f (g i)).Nonempty })
  proof: fun x => by
  let ⟨t, htx, htf⟩ := hf x
refine ⟨t, htx, htf.preimage ?_⟩
  exact hg.mono fun i (hi : Set.Nonempty _) => hi.left

中文:
定理 comp_injOn
  条件: {g : ι' -> ι} (hf : LocallyFinite f) (hg : InjOn g { i | (f (g i)).Nonempty })
  证明: fun x => by
  let ⟨t, htx, htf⟩ := hf x
refine ⟨t, htx, htf.preimage ?_⟩
  exact hg.mono fun i (hi : Set.Nonempty _) => hi.left

Depends on / 依赖: Nonempty, Set.Nonempty, hg.mono, hi.left, htf.preimage, preimage
-/
theorem comp_injOn {g : ι' -> ι} (hf : LocallyFinite f) (hg : InjOn g { i | (f (g i)).Nonempty }) :
    LocallyFinite (f ∘ g) := fun x => by
  let ⟨t, htx, htf⟩ := hf x
refine ⟨t, htx, htf.preimage ?_⟩
  exact hg.mono fun i (hi : Set.Nonempty _) => hi.left

/--
theorem `comp_injective` / 定理 `comp_injective`

English:
theorem comp_injective
  given: {g : ι' -> ι} (hf : LocallyFinite f) (hg : Injective g)
  proof: hf.comp_injOn hg.injOn

中文:
定理 comp_injective
  条件: {g : ι' -> ι} (hf : LocallyFinite f) (hg : Injective g)
  证明: hf.comp_injOn hg.injOn

Depends on / 依赖: comp_injOn, hf.comp_injOn, hg.injOn
-/
theorem comp_injective {g : ι' -> ι} (hf : LocallyFinite f) (hg : Injective g) :
    LocallyFinite (f ∘ g) :=
  hf.comp_injOn hg.injOn

/--
theorem `of_comp_surjective` / 定理 `of_comp_surjective`

English:
theorem of_comp_surjective
  given: {g : ι' -> ι} (hg : Surjective g) (hfg : LocallyFinite (f ∘ g))
  proof: by
  simpa only [comp_def, surjInv_eq hg] using hfg.comp_injective (injective_surjInv hg)

中文:
定理 of_comp_surjective
  条件: {g : ι' -> ι} (hg : Surjective g) (hfg : LocallyFinite (f ∘ g))
  证明: by
  simpa only [comp_def, surjInv_eq hg] using hfg.comp_injective (injective_surjInv hg)

Depends on / 依赖: comp_def, comp_injective, hfg.comp_injective, injective_surjInv, surjInv_eq
-/
theorem of_comp_surjective {g : ι' -> ι} (hg : Surjective g) (hfg : LocallyFinite (f ∘ g)) :
    LocallyFinite f := by
  simpa only [comp_def, surjInv_eq hg] using hfg.comp_injective (injective_surjInv hg)

/--
theorem `on_range` / 定理 `on_range`

English:
theorem on_range
  given: (hf : LocallyFinite f)
  statement: LocallyFinite ((↑) : range f -> Set X)
  proof: of_comp_surjective rangeFactorization_surjective hf

中文:
定理 on_range
  条件: (hf : LocallyFinite f)
  结论: LocallyFinite ((↑) : range f -> Set X)
  证明: of_comp_surjective rangeFactorization_surjective hf

Depends on / 依赖: of_comp_surjective, rangeFactorization_surjective
-/
theorem on_range (hf : LocallyFinite f) : LocallyFinite ((↑) : range f -> Set X) :=
  of_comp_surjective rangeFactorization_surjective hf

/--
theorem `_root_.locallyFinite_iff_smallSets` / 定理 `_root_.locallyFinite_iff_smallSets`

English:
theorem _root_.locallyFinite_iff_smallSets
  proof: forall_congr' fun _ => Iff.symm
    eventually_smallSets' fun _s _t hst ht =>
ht.subset fun _i hi => hi.mono inter_subset_inter_right _ hst

中文:
定理 _root_.locallyFinite_iff_smallSets
  证明: forall_congr' fun _ => Iff.symm
    eventually_smallSets' fun _s _t hst ht =>
ht.subset fun _i hi => hi.mono inter_subset_inter_right _ hst

Depends on / 依赖: Iff.symm, eventually_smallSets, forall_congr, hi.mono, ht.subset, inter_subset_inter_right, subset
-/
theorem _root_.locallyFinite_iff_smallSets :
    LocallyFinite f ↔ forall x, forallᶠ s in (𝓝 x).smallSets, { i | (f i inter s).Nonempty }.Finite :=
forall_congr' fun _ => Iff.symm
    eventually_smallSets' fun _s _t hst ht =>
ht.subset fun _i hi => hi.mono inter_subset_inter_right _ hst

/--
theorem `eventually_smallSets` / 定理 `eventually_smallSets`

English:
theorem eventually_smallSets
  given: (hf : LocallyFinite f) (x : X)
  proof: locallyFinite_iff_smallSets.mp hf x

中文:
定理 eventually_smallSets
  条件: (hf : LocallyFinite f) (x : X)
  证明: locallyFinite_iff_smallSets.mp hf x
-/
protected theorem eventually_smallSets (hf : LocallyFinite f) (x : X) :
    forallᶠ s in (𝓝 x).smallSets, { i | (f i inter s).Nonempty }.Finite :=
  locallyFinite_iff_smallSets.mp hf x

/--
theorem `exists_mem_basis` / 定理 `exists_mem_basis`

English:
theorem exists_mem_basis
  statement: {ι' : Sort*} (hf : LocallyFinite f) {p : ι' -> Prop} {s : ι' -> Set X}
  proof: let ⟨i, hpi, hi⟩ := hb.smallSets.eventually_iff.mp (hf.eventually_smallSets x)
  ⟨i, hpi, hi Subset.rfl⟩

中文:
定理 exists_mem_basis
  结论: {ι' : Sort*} (hf : LocallyFinite f) {p : ι' -> 命题} {s : ι' -> Set X}
  证明: let ⟨i, hpi, hi⟩ := hb.smallSets.eventually_iff.mp (hf.eventually_smallSets x)
  ⟨i, hpi, hi Subset.rfl⟩

Depends on / 依赖: Subset, Subset.rfl, eventually_iff, eventually_smallSets, hb.smallSets.eventually_iff.mp, hf.eventually_smallSets, smallSets
-/
theorem exists_mem_basis {ι' : Sort*} (hf : LocallyFinite f) {p : ι' -> Prop} {s : ι' -> Set X}
    {x : X} (hb : (𝓝 x).HasBasis p s) : exists i, p i ∧ { j | (f j inter s i).Nonempty }.Finite :=
  let ⟨i, hpi, hi⟩ := hb.smallSets.eventually_iff.mp (hf.eventually_smallSets x)
  ⟨i, hpi, hi Subset.rfl⟩

/--
theorem `nhdsWithin_iUnion` / 定理 `nhdsWithin_iUnion`

English:
theorem nhdsWithin_iUnion
  given: (hf : LocallyFinite f) (a : X)
  proof: by
  rcases hf a with ⟨U, haU, hfin⟩
  refine le_antisymm ?_ (Monotone.le_map_iSup fun _ _ => nhdsWithin_mono _)
  calc
    𝓝[⋃ i, f i] a = 𝓝[⋃ i, f i inter U] a := by
      rw [← iUnion_inter]; rw [← nhdsWithin_inter_of_mem' (nhdsWithin_le_nhds haU)]
    _ = 𝓝[⋃ i in {j | (f j inter U).Nonempty}, (

中文:
定理 nhdsWithin_iUnion
  条件: (hf : LocallyFinite f) (a : X)
  证明: by
  rcases hf a with ⟨U, haU, hfin⟩
  refine le_antisymm ?_ (Monotone.le_map_iSup fun _ _ => nhdsWithin_mono _)
  calc
    𝓝[⋃ i, f i] a = 𝓝[⋃ i, f i inter U] a := by
      rw [← iUnion_inter]; rw [← nhdsWithin_inter_of_mem' (nhdsWithin_le_nhds haU)]
    _ = 𝓝[⋃ i in {j | (f j inter U).Nonempty}, (
-/
protected theorem nhdsWithin_iUnion (hf : LocallyFinite f) (a : X) :
    𝓝[⋃ i, f i] a = ⨆ i, 𝓝[f i] a := by
  rcases hf a with ⟨U, haU, hfin⟩
  refine le_antisymm ?_ (Monotone.le_map_iSup fun _ _ => nhdsWithin_mono _)
  calc
    𝓝[⋃ i, f i] a = 𝓝[⋃ i, f i inter U] a := by
      rw [← iUnion_inter]; rw [← nhdsWithin_inter_of_mem' (nhdsWithin_le_nhds haU)]
    _ = 𝓝[⋃ i in {j | (f j inter U).Nonempty}, (f i inter U)] a := by
      simp only [mem_ofPred_eq, iUnion_nonempty_self]
    _ = ⨆ i in {j | (f j inter U).Nonempty}, 𝓝[f i inter U] a := nhdsWithin_biUnion hfin _ _
    _ <= ⨆ i, 𝓝[f i inter U] a := iSup₂_le_iSup _ _
    _ <= ⨆ i, 𝓝[f i] a := iSup_mono fun i => nhdsWithin_mono _ inter_subset_left

/--
theorem `continuousOn_iUnion'` / 定理 `continuousOn_iUnion'`

English:
theorem continuousOn_iUnion'
  statement: {g : X -> Y} (hf : LocallyFinite f)
  proof: by
  rintro x -
  rw [ContinuousWithinAt]; rw [hf.nhdsWithin_iUnion]; rw [tendsto_iSup]
  intro i
  by_cases hx : x in closure (f i)
  · exact hc i _ hx
  · rw [mem_closure_iff_nhdsWithin_neBot, not_neBot] at hx
    rw [hx]
    exact tendsto_bot

中文:
定理 continuousOn_iUnion'
  结论: {g : X -> Y} (hf : LocallyFinite f)
  证明: by
  rintro x -
  rw [ContinuousWithinAt]; rw [hf.nhdsWithin_iUnion]; rw [tendsto_iSup]
  intro i
  by_cases hx : x in closure (f i)
  · exact hc i _ hx
  · rw [mem_closure_iff_nhdsWithin_neBot, not_neBot] at hx
    rw [hx]
    exact tendsto_bot

Depends on / 依赖: ContinuousWithinAt, closure, hf.nhdsWithin_iUnion, mem_closure_iff_nhdsWithin_neBot, nhdsWithin_iUnion, not_neBot, tendsto_bot, tendsto_iSup
-/
theorem continuousOn_iUnion' {g : X -> Y} (hf : LocallyFinite f)
    (hc : forall i x, x in closure (f i) -> ContinuousWithinAt g (f i) x) :
    ContinuousOn g (⋃ i, f i) := by
  rintro x -
  rw [ContinuousWithinAt]; rw [hf.nhdsWithin_iUnion]; rw [tendsto_iSup]
  intro i
  by_cases hx : x in closure (f i)
  · exact hc i _ hx
  · rw [mem_closure_iff_nhdsWithin_neBot, not_neBot] at hx
    rw [hx]
    exact tendsto_bot

/--
theorem `continuousOn_iUnion` / 定理 `continuousOn_iUnion`

English:
theorem continuousOn_iUnion
  statement: {g : X -> Y} (hf : LocallyFinite f) (h_cl : forall i, IsClosed (f i))
  proof: hf.continuousOn_iUnion' fun i x hx => h_cont i x (h_cl i).closure_subset hx

中文:
定理 continuousOn_iUnion
  结论: {g : X -> Y} (hf : LocallyFinite f) (h_cl : 对任意 i, IsClosed (f i))
  证明: hf.continuousOn_iUnion' fun i x hx => h_cont i x (h_cl i).closure_subset hx

Depends on / 依赖: closure_subset, continuousOn_iUnion, h_cl, h_cont, hf.continuousOn_iUnion
-/
theorem continuousOn_iUnion {g : X -> Y} (hf : LocallyFinite f) (h_cl : forall i, IsClosed (f i))
    (h_cont : forall i, ContinuousOn g (f i)) : ContinuousOn g (⋃ i, f i) :=
hf.continuousOn_iUnion' fun i x hx => h_cont i x (h_cl i).closure_subset hx

/--
theorem `continuous'` / 定理 `continuous'`

English:
theorem continuous'
  statement: {g : X -> Y} (hf : LocallyFinite f) (h_cov : ⋃ i, f i = univ)
  proof: continuousOn_univ.1 h_cov ▸ hf.continuousOn_iUnion' hc

中文:
定理 continuous'
  结论: {g : X -> Y} (hf : LocallyFinite f) (h_cov : ⋃ i, f i = univ)
  证明: continuousOn_univ.1 h_cov ▸ hf.continuousOn_iUnion' hc
-/
protected theorem continuous' {g : X -> Y} (hf : LocallyFinite f) (h_cov : ⋃ i, f i = univ)
    (hc : forall i x, x in closure (f i) -> ContinuousWithinAt g (f i) x) :
    Continuous g :=
continuousOn_univ.1 h_cov ▸ hf.continuousOn_iUnion' hc

/--
theorem `continuous` / 定理 `continuous`

English:
theorem continuous
  statement: {g : X -> Y} (hf : LocallyFinite f) (h_cov : ⋃ i, f i = univ)
  proof: continuousOn_univ.1 h_cov ▸ hf.continuousOn_iUnion h_cl h_cont

中文:
定理 continuous
  结论: {g : X -> Y} (hf : LocallyFinite f) (h_cov : ⋃ i, f i = univ)
  证明: continuousOn_univ.1 h_cov ▸ hf.continuousOn_iUnion h_cl h_cont
-/
protected theorem continuous {g : X -> Y} (hf : LocallyFinite f) (h_cov : ⋃ i, f i = univ)
    (h_cl : forall i, IsClosed (f i)) (h_cont : forall i, ContinuousOn g (f i)) :
    Continuous g :=
continuousOn_univ.1 h_cov ▸ hf.continuousOn_iUnion h_cl h_cont

/--
theorem `closure` / 定理 `closure`

English:
theorem closure
  given: (hf : LocallyFinite f)
  statement: LocallyFinite fun i => closure (f i)
  proof: by
  intro x
  rcases hf x with ⟨s, hsx, hsf⟩
  refine ⟨interior s, interior_mem_nhds.2 hsx, hsf.subset fun i hi => ?_⟩
  exact (hi.mono isOpen_interior.closure_inter).of_closure.mono
    (inter_subset_inter_right _ interior_subset)

中文:
定理 closure
  条件: (hf : LocallyFinite f)
  结论: LocallyFinite fun i => closure (f i)
  证明: by
  intro x
  rcases hf x with ⟨s, hsx, hsf⟩
  refine ⟨interior s, interior_mem_nhds.2 hsx, hsf.subset fun i hi => ?_⟩
  exact (hi.mono isOpen_interior.closure_inter).of_closure.mono
    (inter_subset_inter_right _ interior_subset)
-/
protected theorem closure (hf : LocallyFinite f) : LocallyFinite fun i => closure (f i) := by
  intro x
  rcases hf x with ⟨s, hsx, hsf⟩
  refine ⟨interior s, interior_mem_nhds.2 hsx, hsf.subset fun i hi => ?_⟩
  exact (hi.mono isOpen_interior.closure_inter).of_closure.mono
    (inter_subset_inter_right _ interior_subset)

/--
theorem `closure_iUnion` / 定理 `closure_iUnion`

English:
theorem closure_iUnion
  given: (h : LocallyFinite f)
  statement: closure (⋃ i, f i) = ⋃ i, closure (f i)
  proof: by
  ext x
  simp only [mem_closure_iff_nhdsWithin_neBot, h.nhdsWithin_iUnion, iSup_neBot, mem_iUnion]

中文:
定理 closure_iUnion
  条件: (h : LocallyFinite f)
  结论: closure (⋃ i, f i) = ⋃ i, closure (f i)
  证明: by
  ext x
  simp only [mem_closure_iff_nhdsWithin_neBot, h.nhdsWithin_iUnion, iSup_neBot, mem_iUnion]

Depends on / 依赖: h.nhdsWithin_iUnion, iSup_neBot, mem_closure_iff_nhdsWithin_neBot, mem_iUnion, nhdsWithin_iUnion
-/
theorem closure_iUnion (h : LocallyFinite f) : closure (⋃ i, f i) = ⋃ i, closure (f i) := by
  ext x
  simp only [mem_closure_iff_nhdsWithin_neBot, h.nhdsWithin_iUnion, iSup_neBot, mem_iUnion]

/--
theorem `isClosed_iUnion` / 定理 `isClosed_iUnion`

English:
theorem isClosed_iUnion
  given: (hf : LocallyFinite f) (hc : forall i, IsClosed (f i))
  proof: by
  simp only [← closure_eq_iff_isClosed, hf.closure_iUnion, (hc _).closure_eq]

中文:
定理 isClosed_iUnion
  条件: (hf : LocallyFinite f) (hc : 对任意 i, IsClosed (f i))
  证明: by
  simp only [← closure_eq_iff_isClosed, hf.closure_iUnion, (hc _).closure_eq]

Depends on / 依赖: closure_eq, closure_eq_iff_isClosed, closure_iUnion, hf.closure_iUnion
-/
theorem isClosed_iUnion (hf : LocallyFinite f) (hc : forall i, IsClosed (f i)) :
    IsClosed (⋃ i, f i) := by
  simp only [← closure_eq_iff_isClosed, hf.closure_iUnion, (hc _).closure_eq]

/--
theorem `iInter_compl_mem_nhds` / 定理 `iInter_compl_mem_nhds`

English:
theorem iInter_compl_mem_nhds
  given: (hf : LocallyFinite f) (hc : forall i, IsClosed (f i)) (x : X)
  proof: by
  refine IsOpen.mem_nhds ?_ (mem_iInter₂.2 fun i => id)
  suffices IsClosed (⋃ i : { i // x ∉ f i }, f i) by
    rwa [← isOpen_compl_iff, compl_iUnion, iInter_subtype] at this
  exact (hf.comp_injective Subtype.val_injective).isClosed_iUnion fun i => hc _

中文:
定理 iInter_compl_mem_nhds
  条件: (hf : LocallyFinite f) (hc : 对任意 i, IsClosed (f i)) (x : X)
  证明: by
  refine IsOpen.mem_nhds ?_ (mem_iInter₂.2 fun i => id)
  suffices IsClosed (⋃ i : { i // x ∉ f i }, f i) by
    rwa [← isOpen_compl_iff, compl_iUnion, iInter_subtype] at this
  exact (hf.comp_injective Subtype.val_injective).isClosed_iUnion fun i => hc _

Depends on / 依赖: IsClosed, IsOpen, IsOpen.mem_nhds, Subtype, Subtype.val_injective, comp_injective, compl_iUnion, hf.comp_injective, iInter_subtype, isClosed_iUnion, isOpen_compl_iff, mem_nhds, val_injective
-/
theorem iInter_compl_mem_nhds (hf : LocallyFinite f) (hc : forall i, IsClosed (f i)) (x : X) :
    (⋂ (i) (_ : x ∉ f i), (f i)ᶜ) in 𝓝 x := by
  refine IsOpen.mem_nhds ?_ (mem_iInter₂.2 fun i => id)
  suffices IsClosed (⋃ i : { i // x ∉ f i }, f i) by
    rwa [← isOpen_compl_iff, compl_iUnion, iInter_subtype] at this
  exact (hf.comp_injective Subtype.val_injective).isClosed_iUnion fun i => hc _

/--
theorem `exists_forall_eventually_eq_prod` / 定理 `exists_forall_eventually_eq_prod`

English:
theorem exists_forall_eventually_eq_prod
  statement: {π : X -> Sort*} {f : Nat -> forall x : X, π x}
  proof: by
  choose U hUx hU using hf
  choose N hN using fun x => (hU x).bddAbove
  replace hN : forall (x), forall n > N x, forall y in U x, f (n + 1) y = f n y :=
fun x n hn y hy => by_contra fun hne => hn.lt.not_ge hN x ⟨y, hne, hy⟩
  replace hN : forall (x), forall n >= N x + 1, forall y in U x, f n y 

中文:
定理 exists_forall_eventually_eq_prod
  结论: {π : X -> Sort*} {f : 自然数 -> 对任意 x : X, π x}
  证明: by
  choose U hUx hU using hf
  choose N hN using fun x => (hU x).bddAbove
  replace hN : forall (x), forall n > N x, forall y in U x, f (n + 1) y = f n y :=
fun x n hn y hy => by_contra fun hne => hn.lt.not_ge hN x ⟨y, hne, hy⟩
  replace hN : forall (x), forall n >= N x + 1, forall y in U x, f n y 

Depends on / 依赖: Filter, Filter.prod_mem_prod, Nat.le_induction, bddAbove, eventually_gt_atTop, filter_upwards, hn.lt.not_ge, le_induction, not_ge, prod_mem_prod, replace
-/
theorem exists_forall_eventually_eq_prod {π : X -> Sort*} {f : Nat -> forall x : X, π x}
    (hf : LocallyFinite fun n => { x | f (n + 1) x != f n x }) :
    exists F : forall x : X, π x, forall x, forallᶠ p : Nat × X in atTop ×ˢ 𝓝 x, f p.1 p.2 = F p.2 := by
  choose U hUx hU using hf
  choose N hN using fun x => (hU x).bddAbove
  replace hN : forall (x), forall n > N x, forall y in U x, f (n + 1) y = f n y :=
fun x n hn y hy => by_contra fun hne => hn.lt.not_ge hN x ⟨y, hne, hy⟩
  replace hN : forall (x), forall n >= N x + 1, forall y in U x, f n y = f (N x + 1) y :=
    fun x n hn y hy => Nat.le_induction rfl (fun k hle => (hN x _ hle _ hy).trans) n hn
  refine ⟨fun x => f (N x + 1) x, fun x => ?_⟩
  filter_upwards [Filter.prod_mem_prod (eventually_gt_atTop (N x)) (hUx x)]
  rintro ⟨n, y⟩ ⟨hn : N x < n, hy : y in U x⟩
  calc
    f n y = f (N x + 1) y := hN _ _ hn _ hy
    _ = f (max (N x + 1) (N y + 1)) y := (hN _ _ (le_max_left _ _) _ hy).symm
    _ = f (N y + 1) y := hN _ _ (le_max_right _ _) _ (mem_of_mem_nhds <| hUx y)

/--
theorem `exists_forall_eventually_atTop_eventually_eq'` / 定理 `exists_forall_eventually_atTop_eventually_eq'`

English:
theorem exists_forall_eventually_atTop_eventually_eq'
  statement: {π : X -> Sort*} {f : Nat -> forall x : X, π x}
  proof: hf.exists_forall_eventually_eq_prod.imp fun _F hF x => (hF x).curry

中文:
定理 exists_forall_eventually_atTop_eventually_eq'
  结论: {π : X -> Sort*} {f : 自然数 -> 对任意 x : X, π x}
  证明: hf.exists_forall_eventually_eq_prod.imp fun _F hF x => (hF x).curry

Depends on / 依赖: exists_forall_eventually_eq_prod, hf.exists_forall_eventually_eq_prod.imp
-/
theorem exists_forall_eventually_atTop_eventually_eq' {π : X -> Sort*} {f : Nat -> forall x : X, π x}
    (hf : LocallyFinite fun n => { x | f (n + 1) x != f n x }) :
    exists F : forall x : X, π x, forall x, forallᶠ n : Nat in atTop, forallᶠ y : X in 𝓝 x, f n y = F y :=
  hf.exists_forall_eventually_eq_prod.imp fun _F hF x => (hF x).curry

/--
theorem `exists_forall_eventually_atTop_eventuallyEq` / 定理 `exists_forall_eventually_atTop_eventuallyEq`

English:
theorem exists_forall_eventually_atTop_eventuallyEq
  statement: {f : Nat -> X -> α}
  proof: hf.exists_forall_eventually_atTop_eventually_eq'

中文:
定理 exists_forall_eventually_atTop_eventuallyEq
  结论: {f : 自然数 -> X -> α}
  证明: hf.exists_forall_eventually_atTop_eventually_eq'

Depends on / 依赖: exists_forall_eventually_atTop_eventually_eq, hf.exists_forall_eventually_atTop_eventually_eq
-/
theorem exists_forall_eventually_atTop_eventuallyEq {f : Nat -> X -> α}
    (hf : LocallyFinite fun n => { x | f (n + 1) x != f n x }) :
    exists F : X -> α, forall x, forallᶠ n : Nat in atTop, f n =ᶠ[𝓝 x] F :=
  hf.exists_forall_eventually_atTop_eventually_eq'

/--
theorem `preimage_continuous` / 定理 `preimage_continuous`

English:
theorem preimage_continuous
  given: {g : Y -> X} (hf : LocallyFinite f) (hg : Continuous g)
  proof: fun x =>
  let ⟨s, hsx, hs⟩ := hf (g x)
  ⟨g ⁻¹' s, hg.continuousAt hsx, hs.subset fun _ ⟨y, hy⟩ => ⟨g y, hy⟩⟩

中文:
定理 preimage_continuous
  条件: {g : Y -> X} (hf : LocallyFinite f) (hg : Continuous g)
  证明: fun x =>
  let ⟨s, hsx, hs⟩ := hf (g x)
  ⟨g ⁻¹' s, hg.continuousAt hsx, hs.subset fun _ ⟨y, hy⟩ => ⟨g y, hy⟩⟩
-/
theorem preimage_continuous {g : Y -> X} (hf : LocallyFinite f) (hg : Continuous g) :
    LocallyFinite (g ⁻¹' f ·) := fun x =>
  let ⟨s, hsx, hs⟩ := hf (g x)
  ⟨g ⁻¹' s, hg.continuousAt hsx, hs.subset fun _ ⟨y, hy⟩ => ⟨g y, hy⟩⟩

/--
theorem `prod_right` / 定理 `prod_right`

English:
theorem prod_right
  given: (hf : LocallyFinite f) (g : ι -> Set Y)
  statement: LocallyFinite (fun i => f i ×ˢ g i)
  proof: (hf.preimage_continuous continuous_fst).subset fun _ => prod_subset_preimage_fst _ _

中文:
定理 prod_right
  条件: (hf : LocallyFinite f) (g : ι -> Set Y)
  结论: LocallyFinite (fun i => f i ×ˢ g i)
  证明: (hf.preimage_continuous continuous_fst).subset fun _ => prod_subset_preimage_fst _ _

Depends on / 依赖: continuous_fst, hf.preimage_continuous, preimage_continuous, prod_subset_preimage_fst, subset
-/
theorem prod_right (hf : LocallyFinite f) (g : ι -> Set Y) : LocallyFinite (fun i => f i ×ˢ g i) :=
  (hf.preimage_continuous continuous_fst).subset fun _ => prod_subset_preimage_fst _ _

/--
theorem `prod_left` / 定理 `prod_left`

English:
theorem prod_left
  given: {g : ι -> Set Y} (hg : LocallyFinite g) (f : ι -> Set X)
  proof: (hg.preimage_continuous continuous_snd).subset fun _ => prod_subset_preimage_snd _ _

中文:
定理 prod_left
  条件: {g : ι -> Set Y} (hg : LocallyFinite g) (f : ι -> Set X)
  证明: (hg.preimage_continuous continuous_snd).subset fun _ => prod_subset_preimage_snd _ _

Depends on / 依赖: continuous_snd, hg.preimage_continuous, preimage_continuous, prod_subset_preimage_snd, subset
-/
theorem prod_left {g : ι -> Set Y} (hg : LocallyFinite g) (f : ι -> Set X) :
    LocallyFinite (fun i => f i ×ˢ g i) :=
  (hg.preimage_continuous continuous_snd).subset fun _ => prod_subset_preimage_snd _ _

end LocallyFinite

@[simp]
/--
theorem `Equiv.locallyFinite_comp_iff` / 定理 `Equiv.locallyFinite_comp_iff`

English:
theorem Equiv.locallyFinite_comp_iff
  given: (e : ι' ≃ ι)
  statement: LocallyFinite (f ∘ e) ↔ LocallyFinite f
  proof: ⟨fun h => by simpa only [comp_def, e.apply_symm_apply] using h.comp_injective e.symm.injective,
    fun h => h.comp_injective e.injective⟩

中文:
定理 Equiv.locallyFinite_comp_iff
  条件: (e : ι' ≃ ι)
  结论: LocallyFinite (f ∘ e) ↔ LocallyFinite f
  证明: ⟨fun h => by simpa only [comp_def, e.apply_symm_apply] using h.comp_injective e.symm.injective,
    fun h => h.comp_injective e.injective⟩

Depends on / 依赖: apply_symm_apply, comp_def, comp_injective, e.apply_symm_apply, e.injective, e.symm.injective, h.comp_injective, injective
-/
theorem Equiv.locallyFinite_comp_iff (e : ι' ≃ ι) : LocallyFinite (f ∘ e) ↔ LocallyFinite f :=
  ⟨fun h => by simpa only [comp_def, e.apply_symm_apply] using h.comp_injective e.symm.injective,
    fun h => h.comp_injective e.injective⟩

/--
theorem `locallyFinite_sum` / 定理 `locallyFinite_sum`

English:
theorem locallyFinite_sum
  given: {f : ι oplus ι' -> Set X}
  proof: by
  simp only [locallyFinite_iff_smallSets, ← forall_and, ← finite_preimage_inl_and_inr,
    preimage_ofPred_eq, (· ∘ ·), eventually_and]

中文:
定理 locallyFinite_sum
  条件: {f : ι oplus ι' -> Set X}
  证明: by
  simp only [locallyFinite_iff_smallSets, ← forall_and, ← finite_preimage_inl_and_inr,
    preimage_ofPred_eq, (· ∘ ·), eventually_and]

Depends on / 依赖: eventually_and, finite_preimage_inl_and_inr, forall_and, locallyFinite_iff_smallSets, preimage_ofPred_eq
-/
theorem locallyFinite_sum {f : ι oplus ι' -> Set X} :
    LocallyFinite f ↔ LocallyFinite (f ∘ Sum.inl) ∧ LocallyFinite (f ∘ Sum.inr) := by
  simp only [locallyFinite_iff_smallSets, ← forall_and, ← finite_preimage_inl_and_inr,
    preimage_ofPred_eq, (· ∘ ·), eventually_and]

/--
theorem `LocallyFinite.sumElim` / 定理 `LocallyFinite.sumElim`

English:
theorem LocallyFinite.sumElim
  given: {g : ι' -> Set X} (hf : LocallyFinite f) (hg : LocallyFinite g)
  proof: locallyFinite_sum.mpr ⟨hf, hg⟩

中文:
定理 LocallyFinite.sumElim
  条件: {g : ι' -> Set X} (hf : LocallyFinite f) (hg : LocallyFinite g)
  证明: locallyFinite_sum.mpr ⟨hf, hg⟩

Depends on / 依赖: locallyFinite_sum, locallyFinite_sum.mpr
-/
theorem LocallyFinite.sumElim {g : ι' -> Set X} (hf : LocallyFinite f) (hg : LocallyFinite g) :
    LocallyFinite (Sum.elim f g) :=
  locallyFinite_sum.mpr ⟨hf, hg⟩

/--
theorem `locallyFinite_option` / 定理 `locallyFinite_option`

English:
theorem locallyFinite_option
  given: {f : Option ι -> Set X}
  proof: by
  rw [← (Equiv.optionEquivSumPUnit.{0]; rw [_} ι).symm.locallyFinite_comp_iff]; rw [locallyFinite_sum]
  simp only [locallyFinite_of_finite, and_true]
  rfl

中文:
定理 locallyFinite_option
  条件: {f : Option ι -> Set X}
  证明: by
  rw [← (Equiv.optionEquivSumPUnit.{0]; rw [_} ι).symm.locallyFinite_comp_iff]; rw [locallyFinite_sum]
  simp only [locallyFinite_of_finite, and_true]
  rfl

Depends on / 依赖: Equiv.optionEquivSumPUnit, and_true, locallyFinite_comp_iff, locallyFinite_of_finite, locallyFinite_sum, optionEquivSumPUnit, symm.locallyFinite_comp_iff
-/
theorem locallyFinite_option {f : Option ι -> Set X} :
    LocallyFinite f ↔ LocallyFinite (f ∘ some) := by
  rw [← (Equiv.optionEquivSumPUnit.{0]; rw [_} ι).symm.locallyFinite_comp_iff]; rw [locallyFinite_sum]
  simp only [locallyFinite_of_finite, and_true]
  rfl

/--
theorem `LocallyFinite.option_elim'` / 定理 `LocallyFinite.option_elim'`

English:
theorem LocallyFinite.option_elim'
  given: (hf : LocallyFinite f) (s : Set X)
  proof: locallyFinite_option.2 hf

中文:
定理 LocallyFinite.option_elim'
  条件: (hf : LocallyFinite f) (s : Set X)
  证明: locallyFinite_option.2 hf

Depends on / 依赖: locallyFinite_option
-/
theorem LocallyFinite.option_elim' (hf : LocallyFinite f) (s : Set X) :
    LocallyFinite (Option.elim' s f) :=
  locallyFinite_option.2 hf

/--
theorem `LocallyFinite.eventually_subset` / 定理 `LocallyFinite.eventually_subset`

English:
theorem LocallyFinite.eventually_subset
  statement: {s : ι -> Set X}
  proof: by
  filter_upwards [hs.iInter_compl_mem_nhds hs' x] with y hy i hi
  push _ in _ at hy
  exact not_imp_not.mp (hy i) hi

中文:
定理 LocallyFinite.eventually_subset
  结论: {s : ι -> Set X}
  证明: by
  filter_upwards [hs.iInter_compl_mem_nhds hs' x] with y hy i hi
  push _ in _ at hy
  exact not_imp_not.mp (hy i) hi

Depends on / 依赖: filter_upwards, hs.iInter_compl_mem_nhds, iInter_compl_mem_nhds, not_imp_not, not_imp_not.mp
-/
theorem LocallyFinite.eventually_subset {s : ι -> Set X}
    (hs : LocallyFinite s) (hs' : forall i, IsClosed (s i)) (x : X) :
    forallᶠ y in 𝓝 x, {i | y in s i} subseteq {i | x in s i} := by
  filter_upwards [hs.iInter_compl_mem_nhds hs' x] with y hy i hi
  push _ in _ at hy
  exact not_imp_not.mp (hy i) hi
