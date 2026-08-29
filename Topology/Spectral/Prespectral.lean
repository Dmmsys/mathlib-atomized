/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Order.Ideal
public import Mathlib.Topology.Sets.Compacts
public import Mathlib.Topology.Sets.OpenCover
public import Mathlib.Topology.Spectral.Hom

/-!

# Prespectral spaces

In this file, we define prespectral spaces as spaces whose lattice of compact opens forms a basis.

-/

@[expose] public section

open TopologicalSpace Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A space is prespectral if the lattice of compact opens forms a basis. -/
@[stacks 08YG "The last condition for spectral spaces", mk_iff]
/--
Definition of `PrespectralSpace` / `PrespectralSpace` 的定义

English:
class PrespectralSpace
  parameters: (X : Type*) [TopologicalSpace X]
  axioms and operations (1):
    - isTopologicalBasis : IsTopologicalBasis { U : Set X | IsOpen U ∧ IsCompact U }

中文:
类 PrespectralSpace
  参数: (X : 类型) [TopologicalSpace X]
  公理与运算 (1 个):
    - isTopologicalBasis : IsTopologicalBasis { U : Set X | IsOpen U ∧ IsCompact U }
-/
class PrespectralSpace (X : Type*) [TopologicalSpace X] : Prop where
  isTopologicalBasis : IsTopologicalBasis { U : Set X | IsOpen U ∧ IsCompact U }

/--
lemma `PrespectralSpace.of_isTopologicalBasis` / 引理 `PrespectralSpace.of_isTopologicalBasis`

English:
lemma PrespectralSpace.of_isTopologicalBasis
  statement: {B : Set (Set X)}
  proof: basis.of_isOpen_of_subset (fun _ h => h.1)
    fun s hs => ⟨basis.isOpen hs, isCompact_basis s hs⟩

中文:
引理 PrespectralSpace.of_isTopologicalBasis
  结论: {B : Set (Set X)}
  证明: basis.of_isOpen_of_subset (fun _ h => h.1)
    fun s hs => ⟨basis.isOpen hs, isCompact_basis s hs⟩

Depends on / 依赖: basis.of_isOpen_of_subset, of_isOpen_of_subset
-/
lemma PrespectralSpace.of_isTopologicalBasis {B : Set (Set X)}
    (basis : IsTopologicalBasis B) (isCompact_basis : forall U in B, IsCompact U) :
    PrespectralSpace X where
  isTopologicalBasis := basis.of_isOpen_of_subset (fun _ h => h.1)
    fun s hs => ⟨basis.isOpen hs, isCompact_basis s hs⟩

/--
lemma `PrespectralSpace.of_isTopologicalBasis'` / 引理 `PrespectralSpace.of_isTopologicalBasis'`

English:
lemma PrespectralSpace.of_isTopologicalBasis'
  statement: {ι : Type*} {b : ι -> Set X}
  proof: .of_isTopologicalBasis basis (by simp_all)

中文:
引理 PrespectralSpace.of_isTopologicalBasis'
  结论: {ι : 类型} {b : ι -> Set X}
  证明: .of_isTopologicalBasis basis (by simp_all)

Depends on / 依赖: of_isTopologicalBasis
-/
lemma PrespectralSpace.of_isTopologicalBasis' {ι : Type*} {b : ι -> Set X}
    (basis : IsTopologicalBasis (Set.range b)) (isCompact_basis : forall i, IsCompact (b i)) :
    PrespectralSpace X :=
  .of_isTopologicalBasis basis (by simp_all)

instance (priority := low) [NoetherianSpace X] : PrespectralSpace X :=
  .of_isTopologicalBasis isTopologicalBasis_opens fun _ _ => NoetherianSpace.isCompact _

instance (priority := low) [PrespectralSpace X] : LocallyCompactSpace X where
  local_compact_nhds _ _ hn :=
    have ⟨V, ⟨hV₁, hV₂⟩, hxV, hVn⟩ := PrespectralSpace.isTopologicalBasis.mem_nhds_iff.mp hn
    ⟨V, hV₁.mem_nhds hxV, hVn, hV₂⟩

open PrespectralSpace in
instance (priority := low) [T2Space X] [PrespectralSpace X] : TotallySeparatedSpace X :=
  totallySeparatedSpace_iff_exists_isClopen.mpr fun _ _ hxy =>
    have ⟨U, ⟨hU₁, hU₂⟩, hxU, hyU⟩ :=
      isTopologicalBasis.exists_subset_of_mem_open hxy isClosed_singleton.isOpen_compl
    ⟨U, ⟨hU₂.isClosed, hU₁⟩, hxU, fun h => hyU h rfl⟩

/--
lemma `PrespectralSpace.of_isOpenCover` / 引理 `PrespectralSpace.of_isOpenCover`

English:
lemma PrespectralSpace.of_isOpenCover
  proof: by
  refine .of_isTopologicalBasis (hU.isTopologicalBasis fun i => isTopologicalBasis) ?_
  simp only [Set.mem_iUnion, Set.mem_image, Set.mem_ofPred_eq, forall_exists_index, and_imp,
    forall_comm (α := Set _), forall_apply_eq_imp_iff₂]
  exact fun i V hV hV' => hV'.image continuous_subtype_val

中文:
引理 PrespectralSpace.of_isOpenCover
  证明: by
  refine .of_isTopologicalBasis (hU.isTopologicalBasis fun i => isTopologicalBasis) ?_
  simp only [Set.mem_iUnion, Set.mem_image, Set.mem_ofPred_eq, forall_exists_index, and_imp,
    forall_comm (α := Set _), forall_apply_eq_imp_iff₂]
  exact fun i V hV hV' => hV'.image continuous_subtype_val

Depends on / 依赖: Set.mem_iUnion, Set.mem_image, Set.mem_ofPred_eq, and_imp, continuous_subtype_val, forall_comm, forall_exists_index, hU.isTopologicalBasis, isTopologicalBasis, mem_iUnion, mem_image, mem_ofPred_eq, of_isTopologicalBasis
-/
lemma PrespectralSpace.of_isOpenCover
    {ι : Type*} {U : ι -> Opens X} (hU : IsOpenCover U) [forall i, PrespectralSpace (U i)] :
    PrespectralSpace X := by
  refine .of_isTopologicalBasis (hU.isTopologicalBasis fun i => isTopologicalBasis) ?_
  simp only [Set.mem_iUnion, Set.mem_image, Set.mem_ofPred_eq, forall_exists_index, and_imp,
    forall_comm (α := Set _), forall_apply_eq_imp_iff₂]
  exact fun i V hV hV' => hV'.image continuous_subtype_val

/--
lemma `PrespectralSpace.of_isInducing` / 引理 `PrespectralSpace.of_isInducing`

English:
lemma PrespectralSpace.of_isInducing
  statement: [PrespectralSpace Y]
  proof: .of_isTopologicalBasis (PrespectralSpace.isTopologicalBasis.isInducing hf) (by
    simp only [Set.mem_image, Set.mem_ofPred_eq, forall_exists_index, and_imp]
    rintro _ U h₁ h₂ rfl
    exact hf'.isCompact_preimage_of_isOpen h₁ h₂)

中文:
引理 PrespectralSpace.of_isInducing
  结论: [PrespectralSpace Y]
  证明: .of_isTopologicalBasis (PrespectralSpace.isTopologicalBasis.isInducing hf) (by
    simp only [Set.mem_image, Set.mem_ofPred_eq, forall_exists_index, and_imp]
    rintro _ U h₁ h₂ rfl
    exact hf'.isCompact_preimage_of_isOpen h₁ h₂)

Depends on / 依赖: PrespectralSpace, PrespectralSpace.isTopologicalBasis.isInducing, Set.mem_image, Set.mem_ofPred_eq, and_imp, forall_exists_index, isCompact_preimage_of_isOpen, isInducing, isTopologicalBasis, mem_image, mem_ofPred_eq, of_isTopologicalBasis
-/
lemma PrespectralSpace.of_isInducing [PrespectralSpace Y]
    (f : X -> Y) (hf : IsInducing f) (hf' : IsSpectralMap f) : PrespectralSpace X :=
  .of_isTopologicalBasis (PrespectralSpace.isTopologicalBasis.isInducing hf) (by
    simp only [Set.mem_image, Set.mem_ofPred_eq, forall_exists_index, and_imp]
    rintro _ U h₁ h₂ rfl
    exact hf'.isCompact_preimage_of_isOpen h₁ h₂)

/--
lemma `PrespectralSpace.of_isClosedEmbedding` / 引理 `PrespectralSpace.of_isClosedEmbedding`

English:
lemma PrespectralSpace.of_isClosedEmbedding
  statement: [PrespectralSpace Y]
  proof: .of_isInducing f hf.isInducing hf.isProperMap.isSpectralMap

中文:
引理 PrespectralSpace.of_isClosedEmbedding
  结论: [PrespectralSpace Y]
  证明: .of_isInducing f hf.isInducing hf.isProperMap.isSpectralMap

Depends on / 依赖: hf.isInducing, hf.isProperMap.isSpectralMap, isInducing, isProperMap, isSpectralMap, of_isInducing
-/
lemma PrespectralSpace.of_isClosedEmbedding [PrespectralSpace Y]
    (f : X -> Y) (hf : IsClosedEmbedding f) : PrespectralSpace X :=
  .of_isInducing f hf.isInducing hf.isProperMap.isSpectralMap

/--
lemma `Topology.IsOpenEmbedding.prespectralSpace` / 引理 `Topology.IsOpenEmbedding.prespectralSpace`

English:
lemma Topology.IsOpenEmbedding.prespectralSpace
  statement: [PrespectralSpace Y]
  proof: by
apply isTopologicalBasis_of_isOpen_of_nhds (fun U hU => hU.1) fun x U hx hU => ?_
    obtain ⟨V, ⟨hoV, hcV⟩, hfx, hVf⟩ : exists V in {V | IsOpen V ∧ IsCompact V}, f x in V ∧ V subseteq f '' U :=
      (PrespectralSpace.isTopologicalBasis (X := Y)).isOpen_iff.mp
        (hf.isOpen_iff_image_isOpen

中文:
引理 Topology.IsOpenEmbedding.prespectralSpace
  结论: [PrespectralSpace Y]
  证明: by
apply isTopologicalBasis_of_isOpen_of_nhds (fun U hU => hU.1) fun x U hx hU => ?_
    obtain ⟨V, ⟨hoV, hcV⟩, hfx, hVf⟩ : exists V in {V | IsOpen V ∧ IsCompact V}, f x in V ∧ V subseteq f '' U :=
      (PrespectralSpace.isTopologicalBasis (X := Y)).isOpen_iff.mp
        (hf.isOpen_iff_image_isOpen

Depends on / 依赖: IsCompact, IsOpen, PrespectralSpace, PrespectralSpace.isTopologicalBasis, Set.SurjOn.subset_range, SurjOn, continuous, hf.continuous, hf.injective.mem_set_image.mp, hf.isOpen_iff_image_isOpen.mp, hf.toIsInducing.isCompact_preimage, hoV.preimage, injective, isCompact_preimage, isOpen_iff, isOpen_iff.mp, isOpen_iff_image_isOpen, isTopologicalBasis, isTopologicalBasis_of_isOpen_of_nhds, mem_set_image
-/
lemma Topology.IsOpenEmbedding.prespectralSpace [PrespectralSpace Y]
    {f : X -> Y} (hf : IsOpenEmbedding f) :
    PrespectralSpace X where
  isTopologicalBasis := by
apply isTopologicalBasis_of_isOpen_of_nhds (fun U hU => hU.1) fun x U hx hU => ?_
    obtain ⟨V, ⟨hoV, hcV⟩, hfx, hVf⟩ : exists V in {V | IsOpen V ∧ IsCompact V}, f x in V ∧ V subseteq f '' U :=
      (PrespectralSpace.isTopologicalBasis (X := Y)).isOpen_iff.mp
        (hf.isOpen_iff_image_isOpen.mp hU) (f x) ⟨x, hx, rfl⟩
    refine ⟨f ⁻¹' V, ⟨hoV.preimage hf.continuous, ?_⟩, ⟨hfx, fun y hy => ?_⟩⟩
· exact hf.toIsInducing.isCompact_preimage' hcV Set.SurjOn.subset_range hVf
    · exact hf.injective.mem_set_image.mp (hVf hy)

/--
Instance `PrespectralSpace.sigma` / 实例 `PrespectralSpace.sigma`

English:
instance PrespectralSpace.sigma
  signature: {ι : Type*} (X : ι -> Type*) [forall i, TopologicalSpace (X i)]
  body: .of_isTopologicalBasis (IsTopologicalBasis.sigma fun i => isTopologicalBasis) fun U hU => by
    simp_rw [Set.mem_iUnion] at hU
    obtain ⟨i, V, hV, rfl⟩ := hU
    exact hV.2.image continuous_sigmaMk

中文:
实例 PrespectralSpace.sigma
  签名: {ι : 类型} (X : ι -> 类型) [对任意 i, TopologicalSpace (X i)]
  定义体: .of_isTopologicalBasis (IsTopologicalBasis.sigma fun i => isTopologicalBasis) fun U hU => by
    simp_rw [Set.mem_iUnion] at hU
    obtain ⟨i, V, hV, rfl⟩ := hU
    exact hV.2.image continuous_sigmaMk

Depends on / 依赖: IsTopologicalBasis, IsTopologicalBasis.sigma, Set.mem_iUnion, continuous_sigmaMk, isTopologicalBasis, mem_iUnion, of_isTopologicalBasis, simp_rw
-/
instance PrespectralSpace.sigma {ι : Type*} (X : ι -> Type*) [forall i, TopologicalSpace (X i)]
    [forall i, PrespectralSpace (X i)] : PrespectralSpace (Σ i, X i) :=
  .of_isTopologicalBasis (IsTopologicalBasis.sigma fun i => isTopologicalBasis) fun U hU => by
    simp_rw [Set.mem_iUnion] at hU
    obtain ⟨i, V, hV, rfl⟩ := hU
    exact hV.2.image continuous_sigmaMk

variable (X) in
/--
lemma `PrespectralSpace.isBasis_opens` / 引理 `PrespectralSpace.isBasis_opens`

English:
lemma PrespectralSpace.isBasis_opens
  given: [PrespectralSpace X]
  proof: by
  dsimp only [TopologicalSpace.Opens.IsBasis]
  convert! isTopologicalBasis (X := X)
  ext s
  exact ⟨fun ⟨V, hV, heq⟩ => heq ▸ ⟨V.2, hV⟩, fun h => ⟨⟨s, h.1⟩, h.2, rfl⟩⟩

中文:
引理 PrespectralSpace.isBasis_opens
  条件: [PrespectralSpace X]
  证明: by
  dsimp only [TopologicalSpace.Opens.IsBasis]
  convert! isTopologicalBasis (X := X)
  ext s
  exact ⟨fun ⟨V, hV, heq⟩ => heq ▸ ⟨V.2, hV⟩, fun h => ⟨⟨s, h.1⟩, h.2, rfl⟩⟩

Depends on / 依赖: IsBasis, TopologicalSpace, TopologicalSpace.Opens.IsBasis, convert, isTopologicalBasis
-/
lemma PrespectralSpace.isBasis_opens [PrespectralSpace X] :
    TopologicalSpace.Opens.IsBasis { U : Opens X | IsCompact (U : Set X) } := by
  dsimp only [TopologicalSpace.Opens.IsBasis]
  convert! isTopologicalBasis (X := X)
  ext s
  exact ⟨fun ⟨V, hV, heq⟩ => heq ▸ ⟨V.2, hV⟩, fun h => ⟨⟨s, h.1⟩, h.2, rfl⟩⟩

/--
Definition of `PrespectralSpace.opensEquiv` / `PrespectralSpace.opensEquiv` 的定义

English:
definition PrespectralSpace.opensEquiv
  signature: [PrespectralSpace X]
  body: ⟨⟨{ V | (V : Set X) subseteq U }, fun U₁ U₂ h₁ h₂ => subset_trans (α := Set X) h₁ h₂⟩,
    ⟨⊥, by simp⟩, fun U₁ h₁ U₂ h₂ => ⟨U₁ ⊔ U₂, by aesop, le_sup_left, le_sup_right⟩⟩
  invFun I := ⨆ U in I, U.toOpens
  left_inv U := by
    apply le_antisymm
    · simp only [iSup_le_iff]
      exact fun _ => id

中文:
定义 PrespectralSpace.opensEquiv
  签名: [PrespectralSpace X]
  定义体: ⟨⟨{ V | (V : Set X) subseteq U }, fun U₁ U₂ h₁ h₂ => subset_trans (α := Set X) h₁ h₂⟩,
    ⟨⊥, by simp⟩, fun U₁ h₁ U₂ h₂ => ⟨U₁ ⊔ U₂, by aesop, le_sup_left, le_sup_right⟩⟩
  invFun I := ⨆ U in I, U.toOpens
  left_inv U := by
    apply le_antisymm
    · simp only [iSup_le_iff]
      exact fun _ => id

Depends on / 依赖: subset_trans, subseteq
-/
def PrespectralSpace.opensEquiv [PrespectralSpace X] :
    Opens X ≃o Order.Ideal (CompactOpens X) where
  toFun U := ⟨⟨{ V | (V : Set X) subseteq U }, fun U₁ U₂ h₁ h₂ => subset_trans (α := Set X) h₁ h₂⟩,
    ⟨⊥, by simp⟩, fun U₁ h₁ U₂ h₂ => ⟨U₁ ⊔ U₂, by aesop, le_sup_left, le_sup_right⟩⟩
  invFun I := ⨆ U in I, U.toOpens
  left_inv U := by
    apply le_antisymm
    · simp only [iSup_le_iff]
      exact fun _ => id
    · intro x hxU
      obtain ⟨V, ⟨h₁, h₂⟩, hxV, hVU⟩ := isTopologicalBasis.exists_subset_of_mem_open hxU U.2
      simp only [Opens.mem_iSup]
      exact ⟨⟨⟨_, h₂⟩, h₁⟩, hVU, hxV⟩
  right_inv I := by
    ext U
    dsimp
    change U.toOpens <= _ ↔ _
    refine ⟨fun H => ?_, fun h => le_iSup₂ (f := fun U (h : U in I) => U.toOpens) U h⟩
    simp only [← SetLike.coe_subset_coe, Opens.iSup_mk, Opens.carrier_eq_coe, Opens.coe_mk] at H
    obtain ⟨s, hsI, hs, hU⟩ := U.isCompact.elim_finite_subcover_image (fun U _ => U.2) H
    exact I.lower (a := hs.toFinset.sup fun i => i) (by simpa [← SetLike.coe_subset_coe]) (by simpa)
  map_rel_iff' {U V} := by
    change (forall (W : CompactOpens X), (W : Set X) subseteq U -> (W : Set X) subseteq V) ↔ U <= V
    refine ⟨?_, fun H W => (le_trans · H)⟩
    intro H x hxU
    obtain ⟨W, ⟨h₁, h₂⟩, hxW, hWU⟩ := isTopologicalBasis.exists_subset_of_mem_open hxU U.2
    exact H ⟨⟨W, h₂⟩, h₁⟩ hWU hxW

open TopologicalSpace Opens in
/--
lemma `IsOpenMap.exists_opens_image_eq_of_prespectralSpace` / 引理 `IsOpenMap.exists_opens_image_eq_of_prespectralSpace`

English:
lemma IsOpenMap.exists_opens_image_eq_of_prespectralSpace
  statement: [PrespectralSpace X] {f : X -> Y}
  proof: by
  obtain ⟨Us, hUs, heq⟩ := TopologicalSpace.Opens.isBasis_iff_cover.mp
    (PrespectralSpace.isBasis_opens X) ⟨f ⁻¹' U, hU.preimage hfc⟩
  obtain ⟨t, ht⟩ := by
    refine hc.elim_finite_subcover (fun s : Us => f '' s.1) (fun s => h _ s.1.2) (fun x hx => ?_)
    obtain ⟨x, rfl⟩ := hs hx
obtain ⟨i,

中文:
引理 IsOpenMap.exists_opens_image_eq_of_prespectralSpace
  结论: [PrespectralSpace X] {f : X -> Y}
  证明: by
  obtain ⟨Us, hUs, heq⟩ := TopologicalSpace.Opens.isBasis_iff_cover.mp
    (PrespectralSpace.isBasis_opens X) ⟨f ⁻¹' U, hU.preimage hfc⟩
  obtain ⟨t, ht⟩ := by
    refine hc.elim_finite_subcover (fun s : Us => f '' s.1) (fun s => h _ s.1.2) (fun x hx => ?_)
    obtain ⟨x, rfl⟩ := hs hx
obtain ⟨i,

Depends on / 依赖: PrespectralSpace, PrespectralSpace.isBasis_opens, Set.mem_iUnion.mpr, TopologicalSpace, TopologicalSpace.Opens.isBasis_iff_cover.mp, carrier_eq_coe, coe_mk, elim_finite_subcover, finite_toSet, hU.preimage, hc.elim_finite_subcover, iSup_mk, isBasis_iff_cover, isBasis_opens, isCompact_biUnion, mem_iUnion, mem_sSup, mem_sSup.mp, preimage, t.finite_toSet.isCompact_biUnion
-/
lemma IsOpenMap.exists_opens_image_eq_of_prespectralSpace [PrespectralSpace X] {f : X -> Y}
    (hfc : Continuous f) (h : IsOpenMap f) {U : Set Y} (hs : U subseteq Set.range f) (hU : IsOpen U)
    (hc : IsCompact U) : exists (V : Opens X), IsCompact V.1 ∧ f '' V = U := by
  obtain ⟨Us, hUs, heq⟩ := TopologicalSpace.Opens.isBasis_iff_cover.mp
    (PrespectralSpace.isBasis_opens X) ⟨f ⁻¹' U, hU.preimage hfc⟩
  obtain ⟨t, ht⟩ := by
    refine hc.elim_finite_subcover (fun s : Us => f '' s.1) (fun s => h _ s.1.2) (fun x hx => ?_)
    obtain ⟨x, rfl⟩ := hs hx
obtain ⟨i, hi, hx⟩ := mem_sSup.mp by rwa [← heq]
    exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, x, hx, rfl⟩
  refine ⟨⨆ s in t, s.1, ?_, ?_⟩
  · simp only [iSup_mk, carrier_eq_coe, coe_mk]
    exact t.finite_toSet.isCompact_biUnion fun i _ => hUs i.2
  · simp only [iSup_mk, carrier_eq_coe, Set.iUnion_coe_set, coe_mk, Set.image_iUnion]
    convert_to ⋃ i in t, f '' i.1 = U
    · simp
    · refine subset_antisymm (fun x => ?_) ht
      simp_rw [Set.mem_iUnion]
      rintro ⟨i, hi, x, hx, rfl⟩
      have := heq ▸ mem_sSup.mpr ⟨i.1, i.2, hx⟩
      exact this

/--
lemma `PrespectralSpace.exists_isCompact_and_isOpen_between` / 引理 `PrespectralSpace.exists_isCompact_and_isOpen_between`

English:
lemma PrespectralSpace.exists_isCompact_and_isOpen_between
  statement: [PrespectralSpace X] {K U : Set X}
  proof: by
  refine hK.induction_on ⟨∅, by simp⟩ (fun s t hst ⟨W, Wc, Wo, hKW, hWU⟩ => ?_) ?_ ?_
  · use W, Wc, Wo, subset_trans hst hKW, hWU
  · intro s t ⟨W₁, Wc₁, Wo₁, hKW₁, hWU₁⟩ ⟨W₂, Wc₂, Wo₂, hKW₂, hWU₂⟩
    exact ⟨W₁ union W₂, Wc₁.union Wc₂, Wo₁.union Wo₂, Set.union_subset_union hKW₁ hKW₂,
      Set.

中文:
引理 PrespectralSpace.exists_isCompact_and_isOpen_between
  结论: [PrespectralSpace X] {K U : Set X}
  证明: by
  refine hK.induction_on ⟨∅, by simp⟩ (fun s t hst ⟨W, Wc, Wo, hKW, hWU⟩ => ?_) ?_ ?_
  · use W, Wc, Wo, subset_trans hst hKW, hWU
  · intro s t ⟨W₁, Wc₁, Wo₁, hKW₁, hWU₁⟩ ⟨W₂, Wc₂, Wo₂, hKW₂, hWU₂⟩
    exact ⟨W₁ union W₂, Wc₁.union Wc₂, Wo₁.union Wo₂, Set.union_subset_union hKW₁ hKW₂,
      Set.

Depends on / 依赖: PrespectralSpace, PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open, Set.inter_subset_left, Set.union_subset, Set.union_subset_union, exists_subset_of_mem_open, hK.induction_on, induction_on, inter_subset_left, isTopologicalBasis, mem_nhdsWithin, mem_nhdsWithin.mpr, subset_trans, union_subset, union_subset_union
-/
lemma PrespectralSpace.exists_isCompact_and_isOpen_between [PrespectralSpace X] {K U : Set X}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K subseteq U) :
    exists (W : Set X), IsCompact W ∧ IsOpen W ∧ K subseteq W ∧ W subseteq U := by
  refine hK.induction_on ⟨∅, by simp⟩ (fun s t hst ⟨W, Wc, Wo, hKW, hWU⟩ => ?_) ?_ ?_
  · use W, Wc, Wo, subset_trans hst hKW, hWU
  · intro s t ⟨W₁, Wc₁, Wo₁, hKW₁, hWU₁⟩ ⟨W₂, Wc₂, Wo₂, hKW₂, hWU₂⟩
    exact ⟨W₁ union W₂, Wc₁.union Wc₂, Wo₁.union Wo₂, Set.union_subset_union hKW₁ hKW₂,
      Set.union_subset hWU₁ hWU₂⟩
  · intro x hx
    obtain ⟨V, h, hxV, hVU⟩ :=
      PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open (hKU hx) hU
    exact ⟨V, mem_nhdsWithin.mpr ⟨V, h.1, hxV, Set.inter_subset_left⟩, V, h.2, h.1, subset_rfl, hVU⟩

/--
lemma `PrespectralSpace.exists_isClosed_of_not_isPreirreducible` / 引理 `PrespectralSpace.exists_isClosed_of_not_isPreirreducible`

English:
lemma PrespectralSpace.exists_isClosed_of_not_isPreirreducible
  statement: [PrespectralSpace X] (Z : Set X)
  proof: by
  simp only [IsPreirreducible, not_forall] at hZ
  rcases hZ with ⟨U₁, U₂, hU₁, hU₂, hU₁Z, hU₂Z, hU₁₂⟩
  rw [Set.not_nonempty_iff_eq_empty]; rw [← Set.subset_empty_iff] at hU₁₂
  obtain ⟨x₁, hx₁⟩ : exists x₁ in U₁, x₁ in Z ∧ x₁ ∉ U₂ := by
    obtain ⟨x, hx⟩ := hU₁Z
    use x, hx.2, hx.1, fun h₂ =

中文:
引理 PrespectralSpace.exists_isClosed_of_not_isPreirreducible
  结论: [PrespectralSpace X] (Z : Set X)
  证明: by
  simp only [IsPreirreducible, not_forall] at hZ
  rcases hZ with ⟨U₁, U₂, hU₁, hU₂, hU₁Z, hU₂Z, hU₁₂⟩
  rw [Set.not_nonempty_iff_eq_empty]; rw [← Set.subset_empty_iff] at hU₁₂
  obtain ⟨x₁, hx₁⟩ : exists x₁ in U₁, x₁ in Z ∧ x₁ ∉ U₂ := by
    obtain ⟨x, hx⟩ := hU₁Z
    use x, hx.2, hx.1, fun h₂ =

Depends on / 依赖: IsPreirreducible, PrespectralSpace, PrespectralSpace.isTopologicalBasis.isOpen_iff, Set.not_nonempty_iff_eq_empty, Set.subset_empty_iff, isOpen_iff, isTopologicalBasis, not_forall, not_nonempty_iff_eq_empty, subset_empty_iff
-/
lemma PrespectralSpace.exists_isClosed_of_not_isPreirreducible [PrespectralSpace X] (Z : Set X)
    (hZ : ¬ IsPreirreducible Z) :
    exists (A B : Set X), IsClosed A ∧ IsClosed B ∧ IsCompact Aᶜ ∧ IsCompact Bᶜ ∧
      Z subseteq A union B ∧ (Z inter Aᶜ).Nonempty ∧ (Z inter Bᶜ).Nonempty := by
  simp only [IsPreirreducible, not_forall] at hZ
  rcases hZ with ⟨U₁, U₂, hU₁, hU₂, hU₁Z, hU₂Z, hU₁₂⟩
  rw [Set.not_nonempty_iff_eq_empty]; rw [← Set.subset_empty_iff] at hU₁₂
  obtain ⟨x₁, hx₁⟩ : exists x₁ in U₁, x₁ in Z ∧ x₁ ∉ U₂ := by
    obtain ⟨x, hx⟩ := hU₁Z
    use x, hx.2, hx.1, fun h₂ => hU₁₂ ⟨hx.1, hx.2, h₂⟩
  obtain ⟨x₂, hx₂⟩ : exists x₂ in U₂, x₂ in Z ∧ x₂ ∉ U₁ := by
    obtain ⟨x, hx⟩ := hU₂Z
    use x, hx.2, hx.1, fun h₁ => hU₁₂ ⟨hx.1, h₁, hx.2⟩
  rw [PrespectralSpace.isTopologicalBasis.isOpen_iff] at hU₁ hU₂
  obtain ⟨W₁, hW₁⟩ := hU₁ x₁ hx₁.1
  obtain ⟨W₂, hW₂⟩ := hU₂ x₂ hx₂.1
  refine ⟨W₁ᶜ, W₂ᶜ, by simpa using hW₁.1.1, by simpa using hW₂.1.1, by simp [hW₁.1.2],
    by simp [hW₂.1.2], fun z hz => ?_, ⟨x₁, by grind⟩, ⟨x₂, by grind⟩⟩
  · by_contra! hc
    simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not] at hc
    exact hU₁₂ ⟨hz, hW₁.2.2 hc.1, hW₂.2.2 hc.2⟩
