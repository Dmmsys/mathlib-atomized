/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Yury Kudryashov
-/
module

public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.UniformSpace.Compact
public import Mathlib.Topology.UniformSpace.Equicontinuity

/-!
# Compact separated uniform spaces

## Main statement

* **Heine-Cantor** theorem: continuous functions on compact uniform spaces with values in uniform
  spaces are automatically uniformly continuous. There are several variations, the main one is
  `CompactSpace.uniformContinuous_of_continuous`.

## Tags

uniform space, uniform continuity, compact space
-/

public section

open Uniformity Topology Filter UniformSpace Set

variable {α β γ : Type*} [UniformSpace α] [UniformSpace β]

/-!
### Heine-Cantor theorem
-/

/--
theorem `CompactSpace.uniformContinuous_of_continuous` / 定理 `CompactSpace.uniformContinuous_of_continuous`

English:
theorem CompactSpace.uniformContinuous_of_continuous
  statement: [CompactSpace α] {f : α -> β}
  proof: calc map (Prod.map f f) (𝓤 α)
    = map (Prod.map f f) (𝓝ˢ (diagonal α)) := by rw [nhdsSet_diagonal_eq_uniformity]
  _ <= 𝓝ˢ (diagonal β) := (h.prodMap h).tendsto_nhdsSet mapsTo_prodMap_diagonal
  _ <= 𝓤 β := nhdsSet_diagonal_le_uniformity

中文:
定理 紧空间.uniformContinuous_of_continuous
  结论: [紧空间 α] {f : α -> β}
  证明: calc map (Prod.map f f) (𝓤 α)
    = map (Prod.map f f) (𝓝ˢ (diagonal α)) := by rw [nhdsSet_diagonal_eq_uniformity]
  _ <= 𝓝ˢ (diagonal β) := (h.prodMap h).tendsto_nhdsSet mapsTo_prodMap_diagonal
  _ <= 𝓤 β := nhdsSet_diagonal_le_uniformity

Depends on / 依赖: Prod.map, diagonal, h.prodMap, mapsTo_prodMap_diagonal, nhdsSet_diagonal_eq_uniformity, nhdsSet_diagonal_le_uniformity, prodMap, tendsto_nhdsSet
-/
theorem CompactSpace.uniformContinuous_of_continuous [CompactSpace α] {f : α -> β}
    (h : Continuous f) : UniformContinuous f :=
  calc map (Prod.map f f) (𝓤 α)
    = map (Prod.map f f) (𝓝ˢ (diagonal α)) := by rw [nhdsSet_diagonal_eq_uniformity]
  _ <= 𝓝ˢ (diagonal β) := (h.prodMap h).tendsto_nhdsSet mapsTo_prodMap_diagonal
  _ <= 𝓤 β := nhdsSet_diagonal_le_uniformity

/--
theorem `IsCompact.uniformContinuousOn_of_continuous` / 定理 `IsCompact.uniformContinuousOn_of_continuous`

English:
theorem IsCompact.uniformContinuousOn_of_continuous
  statement: {s : Set α} {f : α -> β} (hs : IsCompact s)
  proof: by
  rw [uniformContinuousOn_iff_restrict]
  rw [isCompact_iff_compactSpace] at hs
  rw [continuousOn_iff_continuous_domRestrict] at hf
  exact CompactSpace.uniformContinuous_of_continuous hf

中文:
定理 是紧集.uniformContinuousOn_of_continuous
  结论: {s : 集合 α} {f : α -> β} (hs : 是紧集 s)
  证明: by
  rw [uniformContinuousOn_iff_restrict]
  rw [isCompact_iff_compactSpace] at hs
  rw [continuousOn_iff_continuous_domRestrict] at hf
  exact CompactSpace.uniformContinuous_of_continuous hf

Depends on / 依赖: CompactSpace, CompactSpace.uniformContinuous_of_continuous, continuousOn_iff_continuous_domRestrict, isCompact_iff_compactSpace, uniformContinuousOn_iff_restrict, uniformContinuous_of_continuous
-/
theorem IsCompact.uniformContinuousOn_of_continuous {s : Set α} {f : α -> β} (hs : IsCompact s)
    (hf : ContinuousOn f s) : UniformContinuousOn f s := by
  rw [uniformContinuousOn_iff_restrict]
  rw [isCompact_iff_compactSpace] at hs
  rw [continuousOn_iff_continuous_domRestrict] at hf
  exact CompactSpace.uniformContinuous_of_continuous hf

/--
theorem `IsCompact.uniformContinuousAt_of_continuousAt` / 定理 `IsCompact.uniformContinuousAt_of_continuousAt`

English:
theorem IsCompact.uniformContinuousAt_of_continuousAt
  statement: {r : Set (β × β)} {s : Set α}
  proof: by
  obtain ⟨t, ht, htsymm, htr⟩ := comp_symm_mem_uniformity_sets hr
  choose U hU T hT hb using fun a ha =>
    exists_mem_nhds_ball_subset_of_mem_nhds ((hf a ha).preimage_mem_nhds <| mem_nhds_left _ ht)
  obtain ⟨fs, hsU⟩ := hs.elim_nhds_subcover' U hU
  apply mem_of_superset ((biInter_finset_mem fs).2 fun a _ => hT a a.2)
  rintro ⟨a₁, a₂⟩ h h₁
  obtain ⟨a, ha, haU⟩ := Set.mem_iUnion₂.1 (hsU h₁)
  apply htr
refine ⟨f a, SetRel.symm t hb _ _ _ haU ?_, hb _ _ _ haU ?_⟩
  exacts [mem_ball_self _ (hT a a.2), mem_iInter₂.1 h a ha]

中文:
定理 是紧集.uniformContinuousAt_of_continuousAt
  结论: {r : 集合 (β × β)} {s : 集合 α}
  证明: by
  obtain ⟨t, ht, htsymm, htr⟩ := comp_symm_mem_uniformity_sets hr
  choose U hU T hT hb using fun a ha =>
    exists_mem_nhds_ball_subset_of_mem_nhds ((hf a ha).preimage_mem_nhds <| mem_nhds_left _ ht)
  obtain ⟨fs, hsU⟩ := hs.elim_nhds_subcover' U hU
  apply mem_of_superset ((biInter_finset_mem fs).2 fun a _ => hT a a.2)
  rintro ⟨a₁, a₂⟩ h h₁
  obtain ⟨a, ha, haU⟩ := Set.mem_iUnion₂.1 (hsU h₁)
  apply htr
refine ⟨f a, SetRel.symm t hb _ _ _ haU ?_, hb _ _ _ haU ?_⟩
  exacts [mem_ball_self _ (hT a a.2), mem_iInter₂.1 h a ha]

Depends on / 依赖: Set.mem_iUnion, SetRel, SetRel.symm, biInter_finset_mem, comp_symm_mem_uniformity_sets, elim_nhds_subcover, exacts, exists_mem_nhds_ball_subset_of_mem_nhds, hs.elim_nhds_subcover, htsymm, mem_ball_self, mem_iIn, mem_nhds_left, mem_of_superset, preimage_mem_nhds
-/
theorem IsCompact.uniformContinuousAt_of_continuousAt {r : Set (β × β)} {s : Set α}
    (hs : IsCompact s) (f : α -> β) (hf : forall a in s, ContinuousAt f a) (hr : r in 𝓤 β) :
    { x : α × α | x.1 in s -> (f x.1, f x.2) in r } in 𝓤 α := by
  obtain ⟨t, ht, htsymm, htr⟩ := comp_symm_mem_uniformity_sets hr
  choose U hU T hT hb using fun a ha =>
    exists_mem_nhds_ball_subset_of_mem_nhds ((hf a ha).preimage_mem_nhds <| mem_nhds_left _ ht)
  obtain ⟨fs, hsU⟩ := hs.elim_nhds_subcover' U hU
  apply mem_of_superset ((biInter_finset_mem fs).2 fun a _ => hT a a.2)
  rintro ⟨a₁, a₂⟩ h h₁
  obtain ⟨a, ha, haU⟩ := Set.mem_iUnion₂.1 (hsU h₁)
  apply htr
refine ⟨f a, SetRel.symm t hb _ _ _ haU ?_, hb _ _ _ haU ?_⟩
  exacts [mem_ball_self _ (hT a a.2), mem_iInter₂.1 h a ha]

/--
theorem `Continuous.uniformContinuous_of_tendsto_cocompact` / 定理 `Continuous.uniformContinuous_of_tendsto_cocompact`

English:
theorem Continuous.uniformContinuous_of_tendsto_cocompact
  statement: {f : α -> β} {x : β}
  proof: uniformContinuous_def.2 fun r hr => by
    obtain ⟨t, ht, htsymm, htr⟩ := comp_symm_mem_uniformity_sets hr
    obtain ⟨s, hs, hst⟩ := mem_cocompact.1 (hx <| mem_nhds_left _ ht)
    apply
      mem_of_superset
        (symmetrize_mem_uniformity <|
(hs.uniformContinuousAt_of_continuousAt f fun _ _ => h_cont.continuousAt)
            symmetrize_mem_uniformity hr)
    rintro ⟨b₁, b₂⟩ h
    by_cases h₁ : b₁ in s; · exact (h.1 h₁).1
    by_cases h₂ : b₂ in s; · exact (h.2 h₂).2
    apply htr
exact ⟨x, SetRel.symm t hst h₁, hst h₂⟩

@[to_additive]

中文:
定理 连续.uniformContinuous_of_tendsto_cocompact
  结论: {f : α -> β} {x : β}
  证明: uniformContinuous_def.2 fun r hr => by
    obtain ⟨t, ht, htsymm, htr⟩ := comp_symm_mem_uniformity_sets hr
    obtain ⟨s, hs, hst⟩ := mem_cocompact.1 (hx <| mem_nhds_left _ ht)
    apply
      mem_of_superset
        (symmetrize_mem_uniformity <|
(hs.uniformContinuousAt_of_continuousAt f fun _ _ => h_cont.continuousAt)
            symmetrize_mem_uniformity hr)
    rintro ⟨b₁, b₂⟩ h
    by_cases h₁ : b₁ in s; · exact (h.1 h₁).1
    by_cases h₂ : b₂ in s; · exact (h.2 h₂).2
    apply htr
exact ⟨x, SetRel.symm t hst h₁, hst h₂⟩

@[to_additive]

Depends on / 依赖: SetRel, SetRel.symm, comp_symm_mem_uniformity_sets, continuousAt, h_cont, h_cont.continuousAt, hs.uniformContinuousAt_of_continuousAt, htsymm, mem_cocompact, mem_nhds_left, mem_of_superset, symmetrize_mem_uniformity, uniformContinuousAt_of_continuousAt, uniformContinuous_def
-/
theorem Continuous.uniformContinuous_of_tendsto_cocompact {f : α -> β} {x : β}
    (h_cont : Continuous f) (hx : Tendsto f (cocompact α) (𝓝 x)) : UniformContinuous f :=
  uniformContinuous_def.2 fun r hr => by
    obtain ⟨t, ht, htsymm, htr⟩ := comp_symm_mem_uniformity_sets hr
    obtain ⟨s, hs, hst⟩ := mem_cocompact.1 (hx <| mem_nhds_left _ ht)
    apply
      mem_of_superset
        (symmetrize_mem_uniformity <|
(hs.uniformContinuousAt_of_continuousAt f fun _ _ => h_cont.continuousAt)
            symmetrize_mem_uniformity hr)
    rintro ⟨b₁, b₂⟩ h
    by_cases h₁ : b₁ in s; · exact (h.1 h₁).1
    by_cases h₂ : b₂ in s; · exact (h.2 h₂).2
    apply htr
exact ⟨x, SetRel.symm t hst h₁, hst h₂⟩

@[to_additive]
/--
theorem `HasCompactMulSupport.uniformContinuous_of_continuous` / 定理 `HasCompactMulSupport.uniformContinuous_of_continuous`

English:
theorem HasCompactMulSupport.uniformContinuous_of_continuous
  statement: {f : α -> β} [One β]
  proof: h2.uniformContinuous_of_tendsto_cocompact h1.is_one_at_infty

中文:
定理 HasCompactMulSupport.uniformContinuous_of_continuous
  结论: {f : α -> β} [幺 β]
  证明: h2.uniformContinuous_of_tendsto_cocompact h1.is_one_at_infty

Depends on / 依赖: h1.is_one_at_infty, h2.uniformContinuous_of_tendsto_cocompact, is_one_at_infty, uniformContinuous_of_tendsto_cocompact
-/
theorem HasCompactMulSupport.uniformContinuous_of_continuous {f : α -> β} [One β]
    (h1 : HasCompactMulSupport f) (h2 : Continuous f) : UniformContinuous f :=
  h2.uniformContinuous_of_tendsto_cocompact h1.is_one_at_infty

/--
theorem `ContinuousOn.tendstoUniformly` / 定理 `ContinuousOn.tendstoUniformly`

English:
theorem ContinuousOn.tendstoUniformly
  statement: [LocallyCompactSpace α] [CompactSpace β] [UniformSpace γ]
  proof: by
  rcases LocallyCompactSpace.local_compact_nhds _ _ hxU with ⟨K, hxK, hKU, hK⟩
  have : UniformContinuousOn ↿f (K ×ˢ univ) :=
    IsCompact.uniformContinuousOn_of_continuous (hK.prod isCompact_univ)
      (h.mono <| prod_mono hKU Subset.rfl)
  exact this.tendstoUniformly hxK

中文:
定理 ContinuousOn.tendstoUniformly
  结论: [局部紧空间 α] [紧空间 β] [一致空间 γ]
  证明: by
  rcases LocallyCompactSpace.local_compact_nhds _ _ hxU with ⟨K, hxK, hKU, hK⟩
  have : UniformContinuousOn ↿f (K ×ˢ univ) :=
    IsCompact.uniformContinuousOn_of_continuous (hK.prod isCompact_univ)
      (h.mono <| prod_mono hKU Subset.rfl)
  exact this.tendstoUniformly hxK

Depends on / 依赖: IsCompact, IsCompact.uniformContinuousOn_of_continuous, LocallyCompactSpace, LocallyCompactSpace.local_compact_nhds, Subset, Subset.rfl, UniformContinuousOn, h.mono, hK.prod, isCompact_univ, local_compact_nhds, prod_mono, tendstoUniformly, this.tendstoUniformly, uniformContinuousOn_of_continuous
-/
theorem ContinuousOn.tendstoUniformly [LocallyCompactSpace α] [CompactSpace β] [UniformSpace γ]
    {f : α -> β -> γ} {x : α} {U : Set α} (hxU : U in 𝓝 x) (h : ContinuousOn ↿f (U ×ˢ univ)) :
    TendstoUniformly f (f x) (𝓝 x) := by
  rcases LocallyCompactSpace.local_compact_nhds _ _ hxU with ⟨K, hxK, hKU, hK⟩
  have : UniformContinuousOn ↿f (K ×ˢ univ) :=
    IsCompact.uniformContinuousOn_of_continuous (hK.prod isCompact_univ)
      (h.mono <| prod_mono hKU Subset.rfl)
  exact this.tendstoUniformly hxK

/--
theorem `Continuous.tendstoUniformly` / 定理 `Continuous.tendstoUniformly`

English:
theorem Continuous.tendstoUniformly
  statement: [WeaklyLocallyCompactSpace α] [CompactSpace β] [UniformSpace γ]
  proof: let ⟨K, hK, hxK⟩ := exists_compact_mem_nhds x
  have : UniformContinuousOn ↿f (K ×ˢ univ) :=
    IsCompact.uniformContinuousOn_of_continuous (hK.prod isCompact_univ) h.continuousOn
  this.tendstoUniformly hxK

中文:
定理 连续.tendstoUniformly
  结论: [WeaklyLocallyCompact空间 α] [紧空间 β] [一致空间 γ]
  证明: let ⟨K, hK, hxK⟩ := exists_compact_mem_nhds x
  have : UniformContinuousOn ↿f (K ×ˢ univ) :=
    IsCompact.uniformContinuousOn_of_continuous (hK.prod isCompact_univ) h.continuousOn
  this.tendstoUniformly hxK

Depends on / 依赖: IsCompact, IsCompact.uniformContinuousOn_of_continuous, UniformContinuousOn, continuousOn, exists_compact_mem_nhds, h.continuousOn, hK.prod, isCompact_univ, tendstoUniformly, this.tendstoUniformly, uniformContinuousOn_of_continuous
-/
theorem Continuous.tendstoUniformly [WeaklyLocallyCompactSpace α] [CompactSpace β] [UniformSpace γ]
    (f : α -> β -> γ) (h : Continuous ↿f) (x : α) : TendstoUniformly f (f x) (𝓝 x) :=
  let ⟨K, hK, hxK⟩ := exists_compact_mem_nhds x
  have : UniformContinuousOn ↿f (K ×ˢ univ) :=
    IsCompact.uniformContinuousOn_of_continuous (hK.prod isCompact_univ) h.continuousOn
  this.tendstoUniformly hxK

/--
lemma `IsCompact.mem_uniformity_of_prod` / 引理 `IsCompact.mem_uniformity_of_prod`

English:
lemma IsCompact.mem_uniformity_of_prod
  proof: by
  apply hk.induction_on (p := fun t => exists v in 𝓝[s] q, forall p in v, forall x in t, (f p x, f q x) in u)
  · exact ⟨univ, univ_mem, by simp⟩
  · intro t' t ht't ⟨v, v_mem, hv⟩
    exact ⟨v, v_mem, fun p hp x hx => hv p hp x (ht't hx)⟩
  · intro t t' ⟨v, v_mem, hv⟩ ⟨v', v'_mem, hv'⟩
    refine ⟨v inter v', inter_mem v_mem v'_mem, fun p hp x hx => ?_⟩
    rcases hx with h'x | h'x
    · exact hv p hp.1 x h'x
    · exact hv' p hp.2 x h'x
  · rcases comp_symm_of_uniformity hu with ⟨u', u'_mem, u'_symm, hu'⟩
    intro x hx
    obtain ⟨v, hv, w, hw, hvw⟩ :
      exists v in 𝓝[s] q, exists w in 𝓝[k] x, v ×ˢ w subseteq f.uncurry ⁻¹' {z | (f q x, z) in u'} :=
        mem_nhdsWithin_prod_iff.1 (hf (q, x) ⟨hq, hx⟩ (mem_nhds_left (f q x) u'_mem))
    refine ⟨w, hw, v, hv, fun p hp y hy => ?_⟩
    have A : (f q x, f p y) in u' := hvw (⟨hp, hy⟩ : (p, y) in v ×ˢ w)
    have B : (f q x, f q y) in u' := hvw (⟨mem_of_mem_nhdsWithin hq hv, hy⟩ : (q, y) in v ×ˢ w)
exact hu' SetRel.prodMk_mem_comp (u'_symm A) B

中文:
引理 是紧集.mem_uniformity_of_prod
  证明: by
  apply hk.induction_on (p := fun t => exists v in 𝓝[s] q, forall p in v, forall x in t, (f p x, f q x) in u)
  · exact ⟨univ, univ_mem, by simp⟩
  · intro t' t ht't ⟨v, v_mem, hv⟩
    exact ⟨v, v_mem, fun p hp x hx => hv p hp x (ht't hx)⟩
  · intro t t' ⟨v, v_mem, hv⟩ ⟨v', v'_mem, hv'⟩
    refine ⟨v inter v', inter_mem v_mem v'_mem, fun p hp x hx => ?_⟩
    rcases hx with h'x | h'x
    · exact hv p hp.1 x h'x
    · exact hv' p hp.2 x h'x
  · rcases comp_symm_of_uniformity hu with ⟨u', u'_mem, u'_symm, hu'⟩
    intro x hx
    obtain ⟨v, hv, w, hw, hvw⟩ :
      exists v in 𝓝[s] q, exists w in 𝓝[k] x, v ×ˢ w subseteq f.uncurry ⁻¹' {z | (f q x, z) in u'} :=
        mem_nhdsWithin_prod_iff.1 (hf (q, x) ⟨hq, hx⟩ (mem_nhds_left (f q x) u'_mem))
    refine ⟨w, hw, v, hv, fun p hp y hy => ?_⟩
    have A : (f q x, f p y) in u' := hvw (⟨hp, hy⟩ : (p, y) in v ×ˢ w)
    have B : (f q x, f q y) in u' := hvw (⟨mem_of_mem_nhdsWithin hq hv, hy⟩ : (q, y) in v ×ˢ w)
exact hu' SetRel.prodMk_mem_comp (u'_symm A) B

Depends on / 依赖: _mem, _symm, comp_symm_of_uniformity, hk.induction_on, induction_on, inter_mem, univ_mem, v_mem
-/
lemma IsCompact.mem_uniformity_of_prod
    {α β E : Type*} [TopologicalSpace α] [TopologicalSpace β] [UniformSpace E]
    {f : α -> β -> E} {s : Set α} {k : Set β} {q : α} {u : Set (E × E)}
    (hk : IsCompact k) (hf : ContinuousOn f.uncurry (s ×ˢ k)) (hq : q in s) (hu : u in 𝓤 E) :
    exists v in 𝓝[s] q, forall p in v, forall x in k, (f p x, f q x) in u := by
  apply hk.induction_on (p := fun t => exists v in 𝓝[s] q, forall p in v, forall x in t, (f p x, f q x) in u)
  · exact ⟨univ, univ_mem, by simp⟩
  · intro t' t ht't ⟨v, v_mem, hv⟩
    exact ⟨v, v_mem, fun p hp x hx => hv p hp x (ht't hx)⟩
  · intro t t' ⟨v, v_mem, hv⟩ ⟨v', v'_mem, hv'⟩
    refine ⟨v inter v', inter_mem v_mem v'_mem, fun p hp x hx => ?_⟩
    rcases hx with h'x | h'x
    · exact hv p hp.1 x h'x
    · exact hv' p hp.2 x h'x
  · rcases comp_symm_of_uniformity hu with ⟨u', u'_mem, u'_symm, hu'⟩
    intro x hx
    obtain ⟨v, hv, w, hw, hvw⟩ :
      exists v in 𝓝[s] q, exists w in 𝓝[k] x, v ×ˢ w subseteq f.uncurry ⁻¹' {z | (f q x, z) in u'} :=
        mem_nhdsWithin_prod_iff.1 (hf (q, x) ⟨hq, hx⟩ (mem_nhds_left (f q x) u'_mem))
    refine ⟨w, hw, v, hv, fun p hp y hy => ?_⟩
    have A : (f q x, f p y) in u' := hvw (⟨hp, hy⟩ : (p, y) in v ×ˢ w)
    have B : (f q x, f q y) in u' := hvw (⟨mem_of_mem_nhdsWithin hq hv, hy⟩ : (q, y) in v ×ˢ w)
exact hu' SetRel.prodMk_mem_comp (u'_symm A) B

section UniformConvergence

/--
theorem `CompactSpace.uniformEquicontinuous_of_equicontinuous` / 定理 `CompactSpace.uniformEquicontinuous_of_equicontinuous`

English:
theorem CompactSpace.uniformEquicontinuous_of_equicontinuous
  statement: {ι : Type*} {F : ι -> β -> α}
  proof: by
  rw [equicontinuous_iff_continuous] at h
  rw [uniformEquicontinuous_iff_uniformContinuous]
  exact CompactSpace.uniformContinuous_of_continuous h

中文:
定理 紧空间.uniformEquicontinuous_of_equicontinuous
  结论: {ι : 类型} {F : ι -> β -> α}
  证明: by
  rw [equicontinuous_iff_continuous] at h
  rw [uniformEquicontinuous_iff_uniformContinuous]
  exact CompactSpace.uniformContinuous_of_continuous h

Depends on / 依赖: CompactSpace, CompactSpace.uniformContinuous_of_continuous, equicontinuous_iff_continuous, uniformContinuous_of_continuous, uniformEquicontinuous_iff_uniformContinuous
-/
theorem CompactSpace.uniformEquicontinuous_of_equicontinuous {ι : Type*} {F : ι -> β -> α}
    [CompactSpace β] (h : Equicontinuous F) : UniformEquicontinuous F := by
  rw [equicontinuous_iff_continuous] at h
  rw [uniformEquicontinuous_iff_uniformContinuous]
  exact CompactSpace.uniformContinuous_of_continuous h

end UniformConvergence
