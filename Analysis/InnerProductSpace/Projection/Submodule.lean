/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Frédéric Dupuis, Heather Macbeth
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Subspaces associated with orthogonal projections

Here, the orthogonal projection is used to prove a series of more subtle lemmas about the
orthogonal complement of subspaces of `E` (the orthogonal complement itself was
defined in `Mathlib/Analysis/InnerProductSpace/Orthogonal.lean`) such that they admit
orthogonal projections; the lemma
`Submodule.sup_orthogonal_of_hasOrthogonalProjection`,
stating that for a subspace `K` of `E` such that `K` admits an orthogonal projection we have
`K ⊔ Kᗮ = ⊤`, is a typical example.
-/

public section

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [InnerProductSpace 𝕜 E] [InnerProductSpace Real F]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

variable (K : Submodule 𝕜 E)

namespace Submodule

/--
theorem `sup_orthogonal_inf_of_hasOrthogonalProjection` / 定理 `sup_orthogonal_inf_of_hasOrthogonalProjection`

English:
theorem sup_orthogonal_inf_of_hasOrthogonalProjection
  statement: {K₁ K₂ : Submodule 𝕜 E} (h : K₁ <= K₂)
  proof: by
  ext x
  rw [Submodule.mem_sup]
  let v : K₁ := orthogonalProjectionOnto K₁ x
  have hvm : x - v in K₁ᗮ := sub_starProjection_mem_orthogonal x
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    exact K₂.add_mem (h hy) hz.2
  · exact fun hx => ⟨v, v.prop, x - v, ⟨hvm, K₂.sub_mem hx (h v.prop)⟩, add_sub_cancel _ _⟩

中文:
定理 sup_orthogonal_inf_of_hasOrthogonalProjection
  结论: {K₁ K₂ : 子模 𝕜 E} (h : K₁ <= K₂)
  证明: by
  ext x
  rw [Submodule.mem_sup]
  let v : K₁ := orthogonalProjectionOnto K₁ x
  have hvm : x - v in K₁ᗮ := sub_starProjection_mem_orthogonal x
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    exact K₂.add_mem (h hy) hz.2
  · exact fun hx => ⟨v, v.prop, x - v, ⟨hvm, K₂.sub_mem hx (h v.prop)⟩, add_sub_cancel _ _⟩

Depends on / 依赖: Submodule, Submodule.mem_sup, add_mem, add_sub_cancel, mem_sup, orthogonalProjectionOnto, sub_mem, sub_starProjection_mem_orthogonal, v.prop
-/
theorem sup_orthogonal_inf_of_hasOrthogonalProjection {K₁ K₂ : Submodule 𝕜 E} (h : K₁ <= K₂)
    [K₁.HasOrthogonalProjection] : K₁ ⊔ K₁ᗮ ⊓ K₂ = K₂ := by
  ext x
  rw [Submodule.mem_sup]
  let v : K₁ := orthogonalProjectionOnto K₁ x
  have hvm : x - v in K₁ᗮ := sub_starProjection_mem_orthogonal x
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    exact K₂.add_mem (h hy) hz.2
  · exact fun hx => ⟨v, v.prop, x - v, ⟨hvm, K₂.sub_mem hx (h v.prop)⟩, add_sub_cancel _ _⟩

variable {K} in
/--
theorem `sup_orthogonal_of_hasOrthogonalProjection` / 定理 `sup_orthogonal_of_hasOrthogonalProjection`

English:
theorem sup_orthogonal_of_hasOrthogonalProjection
  given: [K.HasOrthogonalProjection]
  statement: K ⊔ Kᗮ = ⊤
  proof: by
  convert Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection (le_top : K <= ⊤)
  simp

中文:
定理 sup_orthogonal_of_hasOrthogonalProjection
  条件: [K.有OrthogonalProjection]
  结论: K ⊔ Kᗮ = ⊤
  证明: by
  convert Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection (le_top : K <= ⊤)
  simp

Depends on / 依赖: Submodule, Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection, convert, le_top, sup_orthogonal_inf_of_hasOrthogonalProjection
-/
theorem sup_orthogonal_of_hasOrthogonalProjection [K.HasOrthogonalProjection] : K ⊔ Kᗮ = ⊤ := by
  convert Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection (le_top : K <= ⊤)
  simp

/-- If `K` admits an orthogonal projection, then the orthogonal complement of its orthogonal
complement is itself. -/
@[simp]
/--
theorem `orthogonal_orthogonal` / 定理 `orthogonal_orthogonal`

English:
theorem orthogonal_orthogonal
  given: [K.HasOrthogonalProjection]
  statement: Kᗮᗮ = K
  proof: by
  ext v
  constructor
  · obtain ⟨y, hy, z, hz, rfl⟩ := K.exists_add_mem_mem_orthogonal v
    intro hv
    have hz' : z = 0 := by
      have hyz : ⟪z, y⟫ = 0 := by simp [hz y hy, inner_eq_zero_symm]
      simpa [inner_add_right, hyz] using hv z hz
    simp [hy, hz']
  · intro hv w hw
    rw [inner_eq_zero_symm]
    exact hw v hv

中文:
定理 orthogonal_orthogonal
  条件: [K.有OrthogonalProjection]
  结论: Kᗮᗮ = K
  证明: by
  ext v
  constructor
  · obtain ⟨y, hy, z, hz, rfl⟩ := K.exists_add_mem_mem_orthogonal v
    intro hv
    have hz' : z = 0 := by
      have hyz : ⟪z, y⟫ = 0 := by simp [hz y hy, inner_eq_zero_symm]
      simpa [inner_add_right, hyz] using hv z hz
    simp [hy, hz']
  · intro hv w hw
    rw [inner_eq_zero_symm]
    exact hw v hv

Depends on / 依赖: K.exists_add_mem_mem_orthogonal, exists_add_mem_mem_orthogonal, inner_add_right, inner_eq_zero_symm
-/
theorem orthogonal_orthogonal [K.HasOrthogonalProjection] : Kᗮᗮ = K := by
  ext v
  constructor
  · obtain ⟨y, hy, z, hz, rfl⟩ := K.exists_add_mem_mem_orthogonal v
    intro hv
    have hz' : z = 0 := by
      have hyz : ⟪z, y⟫ = 0 := by simp [hz y hy, inner_eq_zero_symm]
      simpa [inner_add_right, hyz] using hv z hz
    simp [hy, hz']
  · intro hv w hw
    rw [inner_eq_zero_symm]
    exact hw v hv

/--
lemma `orthogonal_le_orthogonal_iff` / 引理 `orthogonal_le_orthogonal_iff`

English:
lemma orthogonal_le_orthogonal_iff
  statement: {K₀ K₁ : Submodule 𝕜 E} [K₀.HasOrthogonalProjection]
  proof: ⟨fun h => by simpa using orthogonal_le h, orthogonal_le⟩

中文:
引理 orthogonal_le_orthogonal_iff
  结论: {K₀ K₁ : 子模 𝕜 E} [K₀.有OrthogonalProjection]
  证明: ⟨fun h => by simpa using orthogonal_le h, orthogonal_le⟩

Depends on / 依赖: orthogonal_le
-/
lemma orthogonal_le_orthogonal_iff {K₀ K₁ : Submodule 𝕜 E} [K₀.HasOrthogonalProjection]
    [K₁.HasOrthogonalProjection] : K₀ᗮ <= K₁ᗮ ↔ K₁ <= K₀ :=
  ⟨fun h => by simpa using orthogonal_le h, orthogonal_le⟩

/--
lemma `orthogonal_le_iff_orthogonal_le` / 引理 `orthogonal_le_iff_orthogonal_le`

English:
lemma orthogonal_le_iff_orthogonal_le
  statement: {K₀ K₁ : Submodule 𝕜 E} [K₀.HasOrthogonalProjection]
  proof: by
  rw [← orthogonal_le_orthogonal_iff]; rw [orthogonal_orthogonal]

中文:
引理 orthogonal_le_iff_orthogonal_le
  结论: {K₀ K₁ : 子模 𝕜 E} [K₀.有OrthogonalProjection]
  证明: by
  rw [← orthogonal_le_orthogonal_iff]; rw [orthogonal_orthogonal]

Depends on / 依赖: orthogonal_le_orthogonal_iff, orthogonal_orthogonal
-/
lemma orthogonal_le_iff_orthogonal_le {K₀ K₁ : Submodule 𝕜 E} [K₀.HasOrthogonalProjection]
    [K₁.HasOrthogonalProjection] : K₀ᗮ <= K₁ ↔ K₁ᗮ <= K₀ := by
  rw [← orthogonal_le_orthogonal_iff]; rw [orthogonal_orthogonal]

/--
lemma `le_orthogonal_iff_le_orthogonal` / 引理 `le_orthogonal_iff_le_orthogonal`

English:
lemma le_orthogonal_iff_le_orthogonal
  statement: {K₀ K₁ : Submodule 𝕜 E} [K₀.HasOrthogonalProjection]
  proof: by
  rw [← orthogonal_le_orthogonal_iff]; rw [orthogonal_orthogonal]

中文:
引理 le_orthogonal_iff_le_orthogonal
  结论: {K₀ K₁ : 子模 𝕜 E} [K₀.有OrthogonalProjection]
  证明: by
  rw [← orthogonal_le_orthogonal_iff]; rw [orthogonal_orthogonal]

Depends on / 依赖: orthogonal_le_orthogonal_iff, orthogonal_orthogonal
-/
lemma le_orthogonal_iff_le_orthogonal {K₀ K₁ : Submodule 𝕜 E} [K₀.HasOrthogonalProjection]
    [K₁.HasOrthogonalProjection] : K₀ <= K₁ᗮ ↔ K₁ <= K₀ᗮ := by
  rw [← orthogonal_le_orthogonal_iff]; rw [orthogonal_orthogonal]

/--
theorem `orthogonal_orthogonal_eq_closure` / 定理 `orthogonal_orthogonal_eq_closure`

English:
theorem orthogonal_orthogonal_eq_closure
  given: [CompleteSpace E]
  proof: by
  refine le_antisymm ?_ ?_
  · convert Submodule.orthogonal_orthogonal_monotone K.le_topologicalClosure
    rw [K.topologicalClosure.orthogonal_orthogonal]
  · exact K.topologicalClosure_minimal K.le_orthogonal_orthogonal Kᗮ.isClosed_orthogonal

中文:
定理 orthogonal_orthogonal_eq_closure
  条件: [完备空间 E]
  证明: by
  refine le_antisymm ?_ ?_
  · convert Submodule.orthogonal_orthogonal_monotone K.le_topologicalClosure
    rw [K.topologicalClosure.orthogonal_orthogonal]
  · exact K.topologicalClosure_minimal K.le_orthogonal_orthogonal Kᗮ.isClosed_orthogonal

Depends on / 依赖: K.le_orthogonal_orthogonal, K.le_topologicalClosure, K.topologicalClosure.orthogonal_orthogonal, K.topologicalClosure_minimal, Submodule, Submodule.orthogonal_orthogonal_monotone, convert, isClosed_orthogonal, le_antisymm, le_orthogonal_orthogonal, le_topologicalClosure, orthogonal_orthogonal, orthogonal_orthogonal_monotone, topologicalClosure, topologicalClosure_minimal
-/
theorem orthogonal_orthogonal_eq_closure [CompleteSpace E] :
    Kᗮᗮ = K.topologicalClosure := by
  refine le_antisymm ?_ ?_
  · convert Submodule.orthogonal_orthogonal_monotone K.le_topologicalClosure
    rw [K.topologicalClosure.orthogonal_orthogonal]
  · exact K.topologicalClosure_minimal K.le_orthogonal_orthogonal Kᗮ.isClosed_orthogonal

variable {K}

@[deprecated isCompl_orthogonal (since := "2026-05-07")]
/--
theorem `isCompl_orthogonal_of_hasOrthogonalProjection` / 定理 `isCompl_orthogonal_of_hasOrthogonalProjection`

English:
theorem isCompl_orthogonal_of_hasOrthogonalProjection
  given: [K.HasOrthogonalProjection]
  statement: IsCompl K Kᗮ
  proof: K.isCompl_orthogonal

@[simp]

中文:
定理 isCompl_orthogonal_of_hasOrthogonalProjection
  条件: [K.有OrthogonalProjection]
  结论: 是补集 K Kᗮ
  证明: K.isCompl_orthogonal

@[simp]

Depends on / 依赖: K.isCompl_orthogonal, isCompl_orthogonal
-/
theorem isCompl_orthogonal_of_hasOrthogonalProjection [K.HasOrthogonalProjection] : IsCompl K Kᗮ :=
  K.isCompl_orthogonal

@[simp]
/--
theorem `orthogonalComplement_eq_orthogonalComplement` / 定理 `orthogonalComplement_eq_orthogonalComplement`

English:
theorem orthogonalComplement_eq_orthogonalComplement
  statement: {L : Submodule 𝕜 E} [K.HasOrthogonalProjection]
  proof: ⟨fun h => by simpa using congr(Submodule.orthogonal $(h)),
    fun h => congr(Submodule.orthogonal $(h))⟩

@[simp]

中文:
定理 orthogonalComplement_eq_orthogonalComplement
  结论: {L : 子模 𝕜 E} [K.有OrthogonalProjection]
  证明: ⟨fun h => by simpa using congr(Submodule.orthogonal $(h)),
    fun h => congr(Submodule.orthogonal $(h))⟩

@[simp]

Depends on / 依赖: Submodule, Submodule.orthogonal, orthogonal
-/
theorem orthogonalComplement_eq_orthogonalComplement {L : Submodule 𝕜 E} [K.HasOrthogonalProjection]
    [L.HasOrthogonalProjection] : Kᗮ = Lᗮ ↔ K = L :=
  ⟨fun h => by simpa using congr(Submodule.orthogonal $(h)),
    fun h => congr(Submodule.orthogonal $(h))⟩

@[simp]
/--
theorem `orthogonal_eq_bot_iff` / 定理 `orthogonal_eq_bot_iff`

English:
theorem orthogonal_eq_bot_iff
  given: [K.HasOrthogonalProjection]
  statement: Kᗮ = ⊥ ↔ K = ⊤
  proof: by
  refine ⟨?_, fun h => by rw [h, Submodule.top_orthogonal_eq_bot]⟩
  intro h
  have : K ⊔ Kᗮ = ⊤ := Submodule.sup_orthogonal_of_hasOrthogonalProjection
  rwa [h, sup_comm, bot_sup_eq] at this

中文:
定理 orthogonal_eq_bot_iff
  条件: [K.有OrthogonalProjection]
  结论: Kᗮ = ⊥ ↔ K = ⊤
  证明: by
  refine ⟨?_, fun h => by rw [h, Submodule.top_orthogonal_eq_bot]⟩
  intro h
  have : K ⊔ Kᗮ = ⊤ := Submodule.sup_orthogonal_of_hasOrthogonalProjection
  rwa [h, sup_comm, bot_sup_eq] at this

Depends on / 依赖: Submodule, Submodule.sup_orthogonal_of_hasOrthogonalProjection, Submodule.top_orthogonal_eq_bot, bot_sup_eq, sup_comm, sup_orthogonal_of_hasOrthogonalProjection, top_orthogonal_eq_bot
-/
theorem orthogonal_eq_bot_iff [K.HasOrthogonalProjection] : Kᗮ = ⊥ ↔ K = ⊤ := by
  refine ⟨?_, fun h => by rw [h, Submodule.top_orthogonal_eq_bot]⟩
  intro h
  have : K ⊔ Kᗮ = ⊤ := Submodule.sup_orthogonal_of_hasOrthogonalProjection
  rwa [h, sup_comm, bot_sup_eq] at this

open Topology Finsupp RCLike Real Filter

/--
theorem `starProjection_tendsto_closure_iSup` / 定理 `starProjection_tendsto_closure_iSup`

English:
theorem starProjection_tendsto_closure_iSup
  statement: {ι : Type*} [Preorder ι]
  proof: by
  refine .of_neBot_imp fun h => ?_
  cases atTop_neBot_iff.mp h
  let y := (⨆ i, U i).topologicalClosure.starProjection x
  have proj_x : forall i, (U i).orthogonalProjectionOnto x = (U i).orthogonalProjectionOnto y := fun i =>
    (orthogonalProjectionOnto_starProjection_of_le
        ((le_iSup U i).trans (iSup U).le_topologicalClosure) _).symm
  suffices forall ε > 0, exists I, forall i >= I, ‖(U i).starProjection y - y‖ < ε by
    simpa only [starProjection_apply, proj_x, NormedAddCommGroup.tendsto_atTop] using! this
  intro ε hε
  obtain ⟨a, ha, hay⟩ : exists a in ⨆ i, U i, dist y a < ε := by
    have y_mem : y in (⨆ i, U i).topologicalClosure := Submodule.coe_mem _
    rw [← SetLike.mem_coe]; rw [Submodule.topologicalClosure_coe]; rw [Metric.mem_closure_iff] at y_mem
    exact y_mem ε hε
  rw [dist_eq_norm] at hay
  obtain ⟨I, hI⟩ : exists I, a in U I := by rwa [Submodule.mem_iSup_of_directed _ hU.directed_le] at ha
  refine ⟨I, fun i (hi : I <= i) => ?_⟩
  rw [norm_sub_rev]; rw [starProjection_minimal]
  refine lt_of_le_of_lt ?_ hay
  change _ <= ‖y - (⟨a, hU hi hI⟩ : U i)‖
  exact ciInf_le ⟨0, Set.forall_mem_range.mpr fun _ => norm_nonneg _⟩ _

中文:
定理 starProjection_tendsto_closure_iSup
  结论: {ι : 类型} [预序 ι]
  证明: by
  refine .of_neBot_imp fun h => ?_
  cases atTop_neBot_iff.mp h
  let y := (⨆ i, U i).topologicalClosure.starProjection x
  have proj_x : forall i, (U i).orthogonalProjectionOnto x = (U i).orthogonalProjectionOnto y := fun i =>
    (orthogonalProjectionOnto_starProjection_of_le
        ((le_iSup U i).trans (iSup U).le_topologicalClosure) _).symm
  suffices forall ε > 0, exists I, forall i >= I, ‖(U i).starProjection y - y‖ < ε by
    simpa only [starProjection_apply, proj_x, NormedAddCommGroup.tendsto_atTop] using! this
  intro ε hε
  obtain ⟨a, ha, hay⟩ : exists a in ⨆ i, U i, dist y a < ε := by
    have y_mem : y in (⨆ i, U i).topologicalClosure := Submodule.coe_mem _
    rw [← SetLike.mem_coe]; rw [Submodule.topologicalClosure_coe]; rw [Metric.mem_closure_iff] at y_mem
    exact y_mem ε hε
  rw [dist_eq_norm] at hay
  obtain ⟨I, hI⟩ : exists I, a in U I := by rwa [Submodule.mem_iSup_of_directed _ hU.directed_le] at ha
  refine ⟨I, fun i (hi : I <= i) => ?_⟩
  rw [norm_sub_rev]; rw [starProjection_minimal]
  refine lt_of_le_of_lt ?_ hay
  change _ <= ‖y - (⟨a, hU hi hI⟩ : U i)‖
  exact ciInf_le ⟨0, Set.forall_mem_range.mpr fun _ => norm_nonneg _⟩ _

Depends on / 依赖: NormedAddCommGroup, NormedAddCommGroup.tendsto_atTop, atTop_neBot_iff, atTop_neBot_iff.mp, le_iSup, le_topologicalClosure, of_neBot_imp, orthogonalProjectionOnto, orthogonalProjectionOnto_starProjection_of_le, proj_x, starProjection, starProjection_apply, tendsto_atTop, topologicalClosure, topologicalClosure.starProjection
-/
theorem starProjection_tendsto_closure_iSup {ι : Type*} [Preorder ι]
    (U : ι -> Submodule 𝕜 E) [forall i, (U i).HasOrthogonalProjection]
    [(⨆ i, U i).topologicalClosure.HasOrthogonalProjection] (hU : Monotone U) (x : E) :
    Filter.Tendsto (fun i => (U i).starProjection x) atTop
      (𝓝 ((⨆ i, U i).topologicalClosure.starProjection x)) := by
  refine .of_neBot_imp fun h => ?_
  cases atTop_neBot_iff.mp h
  let y := (⨆ i, U i).topologicalClosure.starProjection x
  have proj_x : forall i, (U i).orthogonalProjectionOnto x = (U i).orthogonalProjectionOnto y := fun i =>
    (orthogonalProjectionOnto_starProjection_of_le
        ((le_iSup U i).trans (iSup U).le_topologicalClosure) _).symm
  suffices forall ε > 0, exists I, forall i >= I, ‖(U i).starProjection y - y‖ < ε by
    simpa only [starProjection_apply, proj_x, NormedAddCommGroup.tendsto_atTop] using! this
  intro ε hε
  obtain ⟨a, ha, hay⟩ : exists a in ⨆ i, U i, dist y a < ε := by
    have y_mem : y in (⨆ i, U i).topologicalClosure := Submodule.coe_mem _
    rw [← SetLike.mem_coe]; rw [Submodule.topologicalClosure_coe]; rw [Metric.mem_closure_iff] at y_mem
    exact y_mem ε hε
  rw [dist_eq_norm] at hay
  obtain ⟨I, hI⟩ : exists I, a in U I := by rwa [Submodule.mem_iSup_of_directed _ hU.directed_le] at ha
  refine ⟨I, fun i (hi : I <= i) => ?_⟩
  rw [norm_sub_rev]; rw [starProjection_minimal]
  refine lt_of_le_of_lt ?_ hay
  change _ <= ‖y - (⟨a, hU hi hI⟩ : U i)‖
  exact ciInf_le ⟨0, Set.forall_mem_range.mpr fun _ => norm_nonneg _⟩ _

/--
theorem `starProjection_tendsto_self` / 定理 `starProjection_tendsto_self`

English:
theorem starProjection_tendsto_self
  statement: {ι : Type*} [Preorder ι]
  proof: by
  have : (⨆ i, U i).topologicalClosure.HasOrthogonalProjection := by
    rw [top_unique hU']
    infer_instance
  convert! starProjection_tendsto_closure_iSup U hU x
  rw [eq_comm]; rw [starProjection_eq_self_iff]; rw [top_unique hU']
  trivial

中文:
定理 starProjection_tendsto_self
  结论: {ι : 类型} [预序 ι]
  证明: by
  have : (⨆ i, U i).topologicalClosure.HasOrthogonalProjection := by
    rw [top_unique hU']
    infer_instance
  convert! starProjection_tendsto_closure_iSup U hU x
  rw [eq_comm]; rw [starProjection_eq_self_iff]; rw [top_unique hU']
  trivial

Depends on / 依赖: HasOrthogonalProjection, convert, eq_comm, infer_instance, starProjection_eq_self_iff, starProjection_tendsto_closure_iSup, top_unique, topologicalClosure, topologicalClosure.HasOrthogonalProjection
-/
theorem starProjection_tendsto_self {ι : Type*} [Preorder ι]
    (U : ι -> Submodule 𝕜 E) [forall t, (U t).HasOrthogonalProjection] (hU : Monotone U) (x : E)
    (hU' : ⊤ <= (⨆ t, U t).topologicalClosure) :
    Filter.Tendsto (fun t => (U t).starProjection x) atTop (𝓝 x) := by
  have : (⨆ i, U i).topologicalClosure.HasOrthogonalProjection := by
    rw [top_unique hU']
    infer_instance
  convert! starProjection_tendsto_closure_iSup U hU x
  rw [eq_comm]; rw [starProjection_eq_self_iff]; rw [top_unique hU']
  trivial

/--
theorem `triorthogonal_eq_orthogonal` / 定理 `triorthogonal_eq_orthogonal`

English:
theorem triorthogonal_eq_orthogonal
  statement: Kᗮᗮᗮ = Kᗮ
  proof: (orthogonal_gc 𝕜 E).u_l_u_eq_u K

中文:
定理 triorthogonal_eq_orthogonal
  结论: Kᗮᗮᗮ = Kᗮ
  证明: (orthogonal_gc 𝕜 E).u_l_u_eq_u K

Depends on / 依赖: orthogonal_gc, u_l_u_eq_u
-/
theorem triorthogonal_eq_orthogonal : Kᗮᗮᗮ = Kᗮ :=
  (orthogonal_gc 𝕜 E).u_l_u_eq_u K

/--
theorem `topologicalClosure_eq_top_iff` / 定理 `topologicalClosure_eq_top_iff`

English:
theorem topologicalClosure_eq_top_iff
  given: [CompleteSpace E]
  proof: by
  rw [← K.orthogonal_orthogonal_eq_closure]
  constructor <;> intro h
  · rw [← Submodule.triorthogonal_eq_orthogonal, h, Submodule.top_orthogonal_eq_bot]
  · rw [h, Submodule.bot_orthogonal_eq_top]

中文:
定理 topologicalClosure_eq_top_iff
  条件: [完备空间 E]
  证明: by
  rw [← K.orthogonal_orthogonal_eq_closure]
  constructor <;> intro h
  · rw [← Submodule.triorthogonal_eq_orthogonal, h, Submodule.top_orthogonal_eq_bot]
  · rw [h, Submodule.bot_orthogonal_eq_top]

Depends on / 依赖: K.orthogonal_orthogonal_eq_closure, Submodule, Submodule.bot_orthogonal_eq_top, Submodule.top_orthogonal_eq_bot, Submodule.triorthogonal_eq_orthogonal, bot_orthogonal_eq_top, orthogonal_orthogonal_eq_closure, top_orthogonal_eq_bot, triorthogonal_eq_orthogonal
-/
theorem topologicalClosure_eq_top_iff [CompleteSpace E] :
    K.topologicalClosure = ⊤ ↔ Kᗮ = ⊥ := by
  rw [← K.orthogonal_orthogonal_eq_closure]
  constructor <;> intro h
  · rw [← Submodule.triorthogonal_eq_orthogonal, h, Submodule.top_orthogonal_eq_bot]
  · rw [h, Submodule.bot_orthogonal_eq_top]

/--
theorem `orthogonalProjectionOnto_apply_eq_projectionOnto` / 定理 `orthogonalProjectionOnto_apply_eq_projectionOnto`

English:
theorem orthogonalProjectionOnto_apply_eq_projectionOnto
  given: [K.HasOrthogonalProjection] (x : E)
  proof: rfl

@[deprecated (since := "2026-05-05")]
alias orthogonalProjection_apply_eq_linearProjOfIsCompl :=
  orthogonalProjectionOnto_apply_eq_projectionOnto

中文:
定理 orthogonalProjectionOnto_apply_eq_projectionOnto
  条件: [K.有OrthogonalProjection] (x : E)
  证明: rfl

@[deprecated (since := "2026-05-05")]
alias orthogonalProjection_apply_eq_linearProjOfIsCompl :=
  orthogonalProjectionOnto_apply_eq_projectionOnto
-/
theorem orthogonalProjectionOnto_apply_eq_projectionOnto [K.HasOrthogonalProjection] (x : E) :
    K.orthogonalProjectionOnto x = K.projectionOnto _ K.isCompl_orthogonal x := rfl

@[deprecated (since := "2026-05-05")]
alias orthogonalProjection_apply_eq_linearProjOfIsCompl :=
  orthogonalProjectionOnto_apply_eq_projectionOnto

/--
theorem `toLinearMap_orthogonalProjectionOnto_eq_projectionOnto` / 定理 `toLinearMap_orthogonalProjectionOnto_eq_projectionOnto`

English:
theorem toLinearMap_orthogonalProjectionOnto_eq_projectionOnto
  given: [K.HasOrthogonalProjection]
  proof: rfl

@[deprecated (since := "2026-05-05")]
alias toLinearMap_orthogonalProjection_eq_linearProjOfIsCompl :=
  toLinearMap_orthogonalProjectionOnto_eq_projectionOnto

中文:
定理 toLinearMap_orthogonalProjectionOnto_eq_projectionOnto
  条件: [K.有OrthogonalProjection]
  证明: rfl

@[deprecated (since := "2026-05-05")]
alias toLinearMap_orthogonalProjection_eq_linearProjOfIsCompl :=
  toLinearMap_orthogonalProjectionOnto_eq_projectionOnto
-/
theorem toLinearMap_orthogonalProjectionOnto_eq_projectionOnto [K.HasOrthogonalProjection] :
    (K.orthogonalProjectionOnto : E ->ₗ[𝕜] K) = K.projectionOnto _ K.isCompl_orthogonal := rfl

@[deprecated (since := "2026-05-05")]
alias toLinearMap_orthogonalProjection_eq_linearProjOfIsCompl :=
  toLinearMap_orthogonalProjectionOnto_eq_projectionOnto

open Submodule in
/--
theorem `toLinearMap_starProjection_eq_isComplProjection` / 定理 `toLinearMap_starProjection_eq_isComplProjection`

English:
theorem toLinearMap_starProjection_eq_isComplProjection
  given: [K.HasOrthogonalProjection]
  proof: rfl

中文:
定理 toLinearMap_starProjection_eq_isComplProjection
  条件: [K.有OrthogonalProjection]
  证明: rfl
-/
theorem toLinearMap_starProjection_eq_isComplProjection [K.HasOrthogonalProjection] :
    K.starProjection.toLinearMap = K.projection Kᗮ K.isCompl_orthogonal := rfl

open Submodule in
/--
theorem `starProjection_apply_eq_isComplProjection` / 定理 `starProjection_apply_eq_isComplProjection`

English:
theorem starProjection_apply_eq_isComplProjection
  given: [K.HasOrthogonalProjection] (x : E)
  proof: rfl

中文:
定理 starProjection_apply_eq_isComplProjection
  条件: [K.有OrthogonalProjection] (x : E)
  证明: rfl
-/
theorem starProjection_apply_eq_isComplProjection [K.HasOrthogonalProjection] (x : E) :
    K.starProjection x = K.projection Kᗮ K.isCompl_orthogonal x := rfl

end Submodule

namespace Dense

open Submodule

variable {K} {x y : E}

/--
theorem `eq_zero_of_mem_orthogonal` / 定理 `eq_zero_of_mem_orthogonal`

English:
theorem eq_zero_of_mem_orthogonal
  given: (hK : Dense (K : Set E)) (h : x in Kᗮ)
  statement: x = 0
  proof: eq_zero_of_inner_left 𝕜 hK fun _ => (mem_orthogonal' _ _).1 h _

中文:
定理 eq_zero_of_mem_orthogonal
  条件: (hK : 稠密 (K : 集合 E)) (h : x in Kᗮ)
  结论: x = 0
  证明: eq_zero_of_inner_left 𝕜 hK fun _ => (mem_orthogonal' _ _).1 h _

Depends on / 依赖: eq_zero_of_inner_left, mem_orthogonal
-/
theorem eq_zero_of_mem_orthogonal (hK : Dense (K : Set E)) (h : x in Kᗮ) : x = 0 :=
  eq_zero_of_inner_left 𝕜 hK fun _ => (mem_orthogonal' _ _).1 h _

/--
theorem `eq_of_sub_mem_orthogonal` / 定理 `eq_of_sub_mem_orthogonal`

English:
theorem eq_of_sub_mem_orthogonal
  given: (hK : Dense (K : Set E)) (h : x - y in Kᗮ)
  statement: x = y
  proof: sub_eq_zero.1 eq_zero_of_mem_orthogonal hK h

中文:
定理 eq_of_sub_mem_orthogonal
  条件: (hK : 稠密 (K : 集合 E)) (h : x - y in Kᗮ)
  结论: x = y
  证明: sub_eq_zero.1 eq_zero_of_mem_orthogonal hK h

Depends on / 依赖: eq_zero_of_mem_orthogonal, sub_eq_zero
-/
theorem eq_of_sub_mem_orthogonal (hK : Dense (K : Set E)) (h : x - y in Kᗮ) : x = y :=
sub_eq_zero.1 eq_zero_of_mem_orthogonal hK h

end Dense

namespace ClosedSubmodule

@[simp]
/--
theorem `orthogonal_orthogonal_eq` / 定理 `orthogonal_orthogonal_eq`

English:
theorem orthogonal_orthogonal_eq
  given: (K : ClosedSubmodule 𝕜 E) [K.HasOrthogonalProjection]
  proof: by ext x; simp

中文:
定理 orthogonal_orthogonal_eq
  条件: (K : 闭子模 𝕜 E) [K.有OrthogonalProjection]
  证明: by ext x; simp
-/
theorem orthogonal_orthogonal_eq (K : ClosedSubmodule 𝕜 E) [K.HasOrthogonalProjection] :
    (Kᗮ)ᗮ = K := by ext x; simp

/--
theorem `orthogonal_eq_orthogonal_iff` / 定理 `orthogonal_eq_orthogonal_iff`

English:
theorem orthogonal_eq_orthogonal_iff
  statement: (K₁ K₂ : ClosedSubmodule 𝕜 E) [K₁.HasOrthogonalProjection]
  proof: ⟨fun h => by simpa using congr($hᗮ), fun h => congr($hᗮ)⟩

中文:
定理 orthogonal_eq_orthogonal_iff
  结论: (K₁ K₂ : 闭子模 𝕜 E) [K₁.有OrthogonalProjection]
  证明: ⟨fun h => by simpa using congr($hᗮ), fun h => congr($hᗮ)⟩
-/
theorem orthogonal_eq_orthogonal_iff (K₁ K₂ : ClosedSubmodule 𝕜 E) [K₁.HasOrthogonalProjection]
    [K₂.HasOrthogonalProjection] : K₁ᗮ = K₂ᗮ ↔ K₁ = K₂ :=
  ⟨fun h => by simpa using congr($hᗮ), fun h => congr($hᗮ)⟩

/--
theorem `orthogonal_injective` / 定理 `orthogonal_injective`

English:
theorem orthogonal_injective
  given: [CompleteSpace E]
  proof: (orthogonal_eq_orthogonal_iff · · |>.mp)

中文:
定理 orthogonal_injective
  条件: [完备空间 E]
  证明: (orthogonal_eq_orthogonal_iff · · |>.mp)

Depends on / 依赖: orthogonal_eq_orthogonal_iff
-/
theorem orthogonal_injective [CompleteSpace E] :
    Function.Injective (fun K : ClosedSubmodule 𝕜 E => Kᗮ) :=
  (orthogonal_eq_orthogonal_iff · · |>.mp)

/--
theorem `sup_orthogonal` / 定理 `sup_orthogonal`

English:
theorem sup_orthogonal
  given: [CompleteSpace E] (K₁ K₂ : ClosedSubmodule 𝕜 E)
  proof: by
  simpa using congr($(inf_orthogonal K₁ᗮ K₂ᗮ)ᗮ).symm

中文:
定理 sup_orthogonal
  条件: [完备空间 E] (K₁ K₂ : 闭子模 𝕜 E)
  证明: by
  simpa using congr($(inf_orthogonal K₁ᗮ K₂ᗮ)ᗮ).symm

Depends on / 依赖: inf_orthogonal
-/
theorem sup_orthogonal [CompleteSpace E] (K₁ K₂ : ClosedSubmodule 𝕜 E) :
    K₁ᗮ ⊔ K₂ᗮ = (K₁ ⊓ K₂)ᗮ := by
  simpa using congr($(inf_orthogonal K₁ᗮ K₂ᗮ)ᗮ).symm

end ClosedSubmodule
