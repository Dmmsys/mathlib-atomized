/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl, Yaël Dillies
-/
module

public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Order.Filter.Pointwise

/-!
# Boundedness in normed groups

This file rephrases metric boundedness in terms of norms.

## Tags

normed group
-/

public section

open Filter Metric Bornology
open scoped Pointwise Topology

variable {α E F G : Type*}

section SeminormedGroup
variable [SeminormedGroup E] [SeminormedGroup F] [SeminormedGroup G] {s : Set E}

@[to_additive (attr := simp) comap_norm_atTop]
/--
lemma `comap_norm_atTop'` / 引理 `comap_norm_atTop'`

English:
lemma comap_norm_atTop'
  statement: comap norm atTop = cobounded E
  proof: by
  simpa only [dist_one_right] using comap_dist_right_atTop (1 : E)

@[to_additive Filter.HasBasis.cobounded_of_norm]

中文:
引理 comap_norm_atTop'
  结论: comap norm atTop = cobounded E
  证明: by
  simpa only [dist_one_right] using comap_dist_right_atTop (1 : E)

@[to_additive Filter.HasBasis.cobounded_of_norm]

Depends on / 依赖: comap_dist_right_atTop, dist_one_right
-/
lemma comap_norm_atTop' : comap norm atTop = cobounded E := by
  simpa only [dist_one_right] using comap_dist_right_atTop (1 : E)

@[to_additive Filter.HasBasis.cobounded_of_norm]
/--
lemma `Filter.HasBasis.cobounded_of_norm'` / 引理 `Filter.HasBasis.cobounded_of_norm'`

English:
lemma Filter.HasBasis.cobounded_of_norm'
  statement: {ι : Sort*} {p : ι -> Prop} {s : ι -> Set Real}
  proof: comap_norm_atTop' (E := E) ▸ h.comap _

@[to_additive Filter.hasBasis_cobounded_norm]

中文:
引理 Filter.HasBasis.cobounded_of_norm'
  结论: {ι : Sort*} {p : ι -> 命题} {s : ι -> Set 实数}
  证明: comap_norm_atTop' (E := E) ▸ h.comap _

@[to_additive Filter.hasBasis_cobounded_norm]

Depends on / 依赖: comap_norm_atTop, h.comap
-/
lemma Filter.HasBasis.cobounded_of_norm' {ι : Sort*} {p : ι -> Prop} {s : ι -> Set Real}
    (h : HasBasis atTop p s) : HasBasis (cobounded E) p fun i => norm ⁻¹' s i :=
  comap_norm_atTop' (E := E) ▸ h.comap _

@[to_additive Filter.hasBasis_cobounded_norm]
/--
lemma `Filter.hasBasis_cobounded_norm'` / 引理 `Filter.hasBasis_cobounded_norm'`

English:
lemma Filter.hasBasis_cobounded_norm'
  statement: HasBasis (cobounded E) (fun _ => True) ({x | · <= ‖x‖})
  proof: atTop_basis.cobounded_of_norm'

@[to_additive (attr := simp) tendsto_norm_atTop_iff_cobounded]

中文:
引理 Filter.hasBasis_cobounded_norm'
  结论: HasBasis (cobounded E) (fun _ => True) ({x | · <= ‖x‖})
  证明: atTop_basis.cobounded_of_norm'

@[to_additive (attr := simp) tendsto_norm_atTop_iff_cobounded]

Depends on / 依赖: atTop_basis, atTop_basis.cobounded_of_norm, cobounded_of_norm
-/
lemma Filter.hasBasis_cobounded_norm' : HasBasis (cobounded E) (fun _ => True) ({x | · <= ‖x‖}) :=
  atTop_basis.cobounded_of_norm'

@[to_additive (attr := simp) tendsto_norm_atTop_iff_cobounded]
/--
lemma `tendsto_norm_atTop_iff_cobounded'` / 引理 `tendsto_norm_atTop_iff_cobounded'`

English:
lemma tendsto_norm_atTop_iff_cobounded'
  given: {f : α -> E} {l : Filter α}
  proof: by
  rw [← comap_norm_atTop']; rw [tendsto_comap_iff]; rfl

@[to_additive tendsto_norm_cobounded_atTop]

中文:
引理 tendsto_norm_atTop_iff_cobounded'
  条件: {f : α -> E} {l : Filter α}
  证明: by
  rw [← comap_norm_atTop']; rw [tendsto_comap_iff]; rfl

@[to_additive tendsto_norm_cobounded_atTop]

Depends on / 依赖: comap_norm_atTop, tendsto_comap_iff
-/
lemma tendsto_norm_atTop_iff_cobounded' {f : α -> E} {l : Filter α} :
    Tendsto (‖f ·‖) l atTop ↔ Tendsto f l (cobounded E) := by
  rw [← comap_norm_atTop']; rw [tendsto_comap_iff]; rfl

@[to_additive tendsto_norm_cobounded_atTop]
/--
lemma `tendsto_norm_cobounded_atTop'` / 引理 `tendsto_norm_cobounded_atTop'`

English:
lemma tendsto_norm_cobounded_atTop'
  statement: Tendsto norm (cobounded E) atTop
  proof: tendsto_norm_atTop_iff_cobounded'.2 tendsto_id

@[to_additive eventually_cobounded_le_norm]

中文:
引理 tendsto_norm_cobounded_atTop'
  结论: Tendsto norm (cobounded E) atTop
  证明: tendsto_norm_atTop_iff_cobounded'.2 tendsto_id

@[to_additive eventually_cobounded_le_norm]

Depends on / 依赖: tendsto_id, tendsto_norm_atTop_iff_cobounded
-/
lemma tendsto_norm_cobounded_atTop' : Tendsto norm (cobounded E) atTop :=
  tendsto_norm_atTop_iff_cobounded'.2 tendsto_id

@[to_additive eventually_cobounded_le_norm]
/--
lemma `eventually_cobounded_le_norm'` / 引理 `eventually_cobounded_le_norm'`

English:
lemma eventually_cobounded_le_norm'
  given: (a : Real)
  statement: forallᶠ x in cobounded E, a <= ‖x‖
  proof: tendsto_norm_cobounded_atTop'.eventually_ge_atTop a

@[to_additive tendsto_norm_cocompact_atTop]

中文:
引理 eventually_cobounded_le_norm'
  条件: (a : 实数)
  结论: 对任意ᶠ x in cobounded E, a <= ‖x‖
  证明: tendsto_norm_cobounded_atTop'.eventually_ge_atTop a

@[to_additive tendsto_norm_cocompact_atTop]

Depends on / 依赖: eventually_ge_atTop, tendsto_norm_cobounded_atTop
-/
lemma eventually_cobounded_le_norm' (a : Real) : forallᶠ x in cobounded E, a <= ‖x‖ :=
  tendsto_norm_cobounded_atTop'.eventually_ge_atTop a

@[to_additive tendsto_norm_cocompact_atTop]
/--
lemma `tendsto_norm_cocompact_atTop'` / 引理 `tendsto_norm_cocompact_atTop'`

English:
lemma tendsto_norm_cocompact_atTop'
  given: [ProperSpace E]
  statement: Tendsto norm (cocompact E) atTop
  proof: cobounded_eq_cocompact (α := E) ▸ tendsto_norm_cobounded_atTop'

@[to_additive (attr := simp)]

中文:
引理 tendsto_norm_cocompact_atTop'
  条件: [命题erSpace E]
  结论: Tendsto norm (cocompact E) atTop
  证明: cobounded_eq_cocompact (α := E) ▸ tendsto_norm_cobounded_atTop'

@[to_additive (attr := simp)]

Depends on / 依赖: cobounded_eq_cocompact, tendsto_norm_cobounded_atTop
-/
lemma tendsto_norm_cocompact_atTop' [ProperSpace E] : Tendsto norm (cocompact E) atTop :=
  cobounded_eq_cocompact (α := E) ▸ tendsto_norm_cobounded_atTop'

@[to_additive (attr := simp)]
/--
lemma `Filter.inv_cobounded` / 引理 `Filter.inv_cobounded`

English:
lemma Filter.inv_cobounded
  statement: (cobounded E)⁻¹ = cobounded E
  proof: by
  simp only [← comap_norm_atTop', ← Filter.comap_inv, comap_comap, Function.comp_def, norm_inv']

中文:
引理 Filter.inv_cobounded
  结论: (cobounded E)⁻¹ = cobounded E
  证明: by
  simp only [← comap_norm_atTop', ← Filter.comap_inv, comap_comap, Function.comp_def, norm_inv']

Depends on / 依赖: Filter, Filter.comap_inv, Function, Function.comp_def, comap_comap, comap_inv, comap_norm_atTop, comp_def, norm_inv
-/
lemma Filter.inv_cobounded : (cobounded E)⁻¹ = cobounded E := by
  simp only [← comap_norm_atTop', ← Filter.comap_inv, comap_comap, Function.comp_def, norm_inv']

/-- In a (semi)normed group, inversion `x ↦ x⁻¹` tends to infinity at infinity. -/
@[to_additive /-- In a (semi)normed group, negation `x ↦ -x` tends to infinity at infinity. -/]
/--
theorem `Filter.tendsto_inv_cobounded` / 定理 `Filter.tendsto_inv_cobounded`

English:
theorem Filter.tendsto_inv_cobounded
  statement: Tendsto Inv.inv (cobounded E) (cobounded E)
  proof: inv_cobounded.le

@[to_additive isBounded_iff_forall_norm_le]

中文:
定理 Filter.tendsto_inv_cobounded
  结论: Tendsto Inv.inv (cobounded E) (cobounded E)
  证明: inv_cobounded.le

@[to_additive isBounded_iff_forall_norm_le]

Depends on / 依赖: inv_cobounded, inv_cobounded.le
-/
theorem Filter.tendsto_inv_cobounded : Tendsto Inv.inv (cobounded E) (cobounded E) :=
  inv_cobounded.le

@[to_additive isBounded_iff_forall_norm_le]
/--
lemma `isBounded_iff_forall_norm_le'` / 引理 `isBounded_iff_forall_norm_le'`

English:
lemma isBounded_iff_forall_norm_le'
  statement: Bornology.IsBounded s ↔ exists C, forall x in s, ‖x‖ <= C
  proof: by
  simpa only [Set.subset_def, mem_closedBall_one_iff] using isBounded_iff_subset_closedBall (1 : E)

alias ⟨Bornology.IsBounded.exists_norm_le', _⟩ := isBounded_iff_forall_norm_le'

alias ⟨Bornology.IsBounded.exists_norm_le, _⟩ := isBounded_iff_forall_norm_le

中文:
引理 isBounded_iff_forall_norm_le'
  结论: Bornology.IsBounded s ↔ 存在 C, 对任意 x in s, ‖x‖ <= C
  证明: by
  simpa only [Set.subset_def, mem_closedBall_one_iff] using isBounded_iff_subset_closedBall (1 : E)

alias ⟨Bornology.IsBounded.exists_norm_le', _⟩ := isBounded_iff_forall_norm_le'

alias ⟨Bornology.IsBounded.exists_norm_le, _⟩ := isBounded_iff_forall_norm_le

Depends on / 依赖: Set.subset_def, isBounded_iff_subset_closedBall, mem_closedBall_one_iff, subset_def
-/
lemma isBounded_iff_forall_norm_le' : Bornology.IsBounded s ↔ exists C, forall x in s, ‖x‖ <= C := by
  simpa only [Set.subset_def, mem_closedBall_one_iff] using isBounded_iff_subset_closedBall (1 : E)

alias ⟨Bornology.IsBounded.exists_norm_le', _⟩ := isBounded_iff_forall_norm_le'

alias ⟨Bornology.IsBounded.exists_norm_le, _⟩ := isBounded_iff_forall_norm_le

attribute [to_additive existing exists_norm_le] Bornology.IsBounded.exists_norm_le'

@[to_additive exists_pos_norm_le]
/--
lemma `Bornology.IsBounded.exists_pos_norm_le'` / 引理 `Bornology.IsBounded.exists_pos_norm_le'`

English:
lemma Bornology.IsBounded.exists_pos_norm_le'
  given: (hs : IsBounded s)
  statement: exists R > 0, forall x in s, ‖x‖ <= R
  proof: let ⟨R₀, hR₀⟩ := hs.exists_norm_le'
⟨max R₀ 1, by positivity, fun x hx => (hR₀ x hx).trans le_max_left _ _⟩

@[to_additive Bornology.IsBounded.exists_pos_norm_lt]

中文:
引理 Bornology.IsBounded.exists_pos_norm_le'
  条件: (hs : IsBounded s)
  结论: 存在 R > 0, 对任意 x in s, ‖x‖ <= R
  证明: let ⟨R₀, hR₀⟩ := hs.exists_norm_le'
⟨max R₀ 1, by positivity, fun x hx => (hR₀ x hx).trans le_max_left _ _⟩

@[to_additive Bornology.IsBounded.exists_pos_norm_lt]

Depends on / 依赖: exists_norm_le, hs.exists_norm_le, le_max_left
-/
lemma Bornology.IsBounded.exists_pos_norm_le' (hs : IsBounded s) : exists R > 0, forall x in s, ‖x‖ <= R :=
  let ⟨R₀, hR₀⟩ := hs.exists_norm_le'
⟨max R₀ 1, by positivity, fun x hx => (hR₀ x hx).trans le_max_left _ _⟩

@[to_additive Bornology.IsBounded.exists_pos_norm_lt]
/--
lemma `Bornology.IsBounded.exists_pos_norm_lt'` / 引理 `Bornology.IsBounded.exists_pos_norm_lt'`

English:
lemma Bornology.IsBounded.exists_pos_norm_lt'
  given: (hs : IsBounded s)
  statement: exists R > 0, forall x in s, ‖x‖ < R
  proof: let ⟨R, hR₀, hR⟩ := hs.exists_pos_norm_le'
  ⟨R + 1, by positivity, fun x hx => (hR x hx).trans_lt (lt_add_one _)⟩

@[to_additive]

中文:
引理 Bornology.IsBounded.exists_pos_norm_lt'
  条件: (hs : IsBounded s)
  结论: 存在 R > 0, 对任意 x in s, ‖x‖ < R
  证明: let ⟨R, hR₀, hR⟩ := hs.exists_pos_norm_le'
  ⟨R + 1, by positivity, fun x hx => (hR x hx).trans_lt (lt_add_one _)⟩

@[to_additive]

Depends on / 依赖: exists_pos_norm_le, hs.exists_pos_norm_le, lt_add_one, trans_lt
-/
lemma Bornology.IsBounded.exists_pos_norm_lt' (hs : IsBounded s) : exists R > 0, forall x in s, ‖x‖ < R :=
  let ⟨R, hR₀, hR⟩ := hs.exists_pos_norm_le'
  ⟨R + 1, by positivity, fun x hx => (hR x hx).trans_lt (lt_add_one _)⟩

@[to_additive]
/--
lemma `NormedCommGroup.cauchySeq_iff` / 引理 `NormedCommGroup.cauchySeq_iff`

English:
lemma NormedCommGroup.cauchySeq_iff
  given: [Nonempty α] [SemilatticeSup α] {u : α -> E}
  proof: by
  simp [Metric.cauchySeq_iff, dist_eq_norm_inv_mul]

@[to_additive IsCompact.exists_bound_of_continuousOn]

中文:
引理 NormedCommGroup.cauchySeq_iff
  条件: [Nonempty α] [SemilatticeSup α] {u : α -> E}
  证明: by
  simp [Metric.cauchySeq_iff, dist_eq_norm_inv_mul]

@[to_additive IsCompact.exists_bound_of_continuousOn]

Depends on / 依赖: Metric, Metric.cauchySeq_iff, cauchySeq_iff, dist_eq_norm_inv_mul
-/
lemma NormedCommGroup.cauchySeq_iff [Nonempty α] [SemilatticeSup α] {u : α -> E} :
    CauchySeq u ↔ forall ε > 0, exists N, forall m, N <= m -> forall n, N <= n -> ‖(u m)⁻¹ * u n‖ < ε := by
  simp [Metric.cauchySeq_iff, dist_eq_norm_inv_mul]

@[to_additive IsCompact.exists_bound_of_continuousOn]
/--
lemma `IsCompact.exists_bound_of_continuousOn'` / 引理 `IsCompact.exists_bound_of_continuousOn'`

English:
lemma IsCompact.exists_bound_of_continuousOn'
  statement: [TopologicalSpace α] {s : Set α} (hs : IsCompact s)
  proof: (isBounded_iff_forall_norm_le'.1 (hs.image_of_continuousOn hf).isBounded).imp fun _C hC _x hx =>
hC _ Set.mem_image_of_mem _ hx

@[to_additive]

中文:
引理 IsCompact.exists_bound_of_continuousOn'
  结论: [TopologicalSpace α] {s : Set α} (hs : IsCompact s)
  证明: (isBounded_iff_forall_norm_le'.1 (hs.image_of_continuousOn hf).isBounded).imp fun _C hC _x hx =>
hC _ Set.mem_image_of_mem _ hx

@[to_additive]

Depends on / 依赖: Set.mem_image_of_mem, hs.image_of_continuousOn, image_of_continuousOn, isBounded, isBounded_iff_forall_norm_le, mem_image_of_mem
-/
lemma IsCompact.exists_bound_of_continuousOn' [TopologicalSpace α] {s : Set α} (hs : IsCompact s)
    {f : α -> E} (hf : ContinuousOn f s) : exists C, forall x in s, ‖f x‖ <= C :=
  (isBounded_iff_forall_norm_le'.1 (hs.image_of_continuousOn hf).isBounded).imp fun _C hC _x hx =>
hC _ Set.mem_image_of_mem _ hx

@[to_additive]
/--
lemma `HasCompactMulSupport.exists_bound_of_continuous` / 引理 `HasCompactMulSupport.exists_bound_of_continuous`

English:
lemma HasCompactMulSupport.exists_bound_of_continuous
  statement: [TopologicalSpace α]
  proof: by
  simpa using (hf.isCompact_range h'f).isBounded.exists_norm_le'

中文:
引理 HasCompactMulSupport.exists_bound_of_continuous
  结论: [TopologicalSpace α]
  证明: by
  simpa using (hf.isCompact_range h'f).isBounded.exists_norm_le'

Depends on / 依赖: exists_norm_le, hf.isCompact_range, isBounded, isBounded.exists_norm_le, isCompact_range
-/
lemma HasCompactMulSupport.exists_bound_of_continuous [TopologicalSpace α]
    {f : α -> E} (hf : HasCompactMulSupport f) (h'f : Continuous f) : exists C, forall x, ‖f x‖ <= C := by
  simpa using (hf.isCompact_range h'f).isBounded.exists_norm_le'

/-- A helper lemma used to prove that the (scalar or usual) product of a function that tends to one
and a bounded function tends to one. This lemma is formulated for any binary operation
`op : E → F → G` with an estimate `‖op x y‖ ≤ A * ‖x‖ * ‖y‖` for some constant A instead of
multiplication so that it can be applied to `(*)`, `flip (*)`, `(•)`, and `flip (•)`. -/
@[to_additive /-- A helper lemma used to prove that the (scalar or usual) product of a function that
tends to zero and a bounded function tends to zero. This lemma is formulated for any binary
operation `op : E → F → G` with an estimate `‖op x y‖ ≤ A * ‖x‖ * ‖y‖` for some constant A instead
of multiplication so that it can be applied to `(*)`, `flip (*)`, `(•)`, and `flip (•)`. -/]
/--
lemma `Filter.Tendsto.op_one_isBoundedUnder_le'` / 引理 `Filter.Tendsto.op_one_isBoundedUnder_le'`

English:
lemma Filter.Tendsto.op_one_isBoundedUnder_le'
  statement: {f : α -> E} {g : α -> F} {l : Filter α}
  proof: by
  obtain ⟨A, h_op⟩ := h_op
  rcases hg with ⟨C, hC⟩; rw [eventually_map] at hC
  rw [NormedGroup.tendsto_nhds_one] at hf ⊢
  intro ε ε₀
  rcases exists_pos_mul_lt ε₀ (A * C) with ⟨δ, δ₀, hδ⟩
  filter_upwards [hf δ δ₀, hC] with i hf hg
  refine (h_op _ _).trans_lt ?_
  rcases le_total A 0 with hA 

中文:
引理 Filter.Tendsto.op_one_isBoundedUnder_le'
  结论: {f : α -> E} {g : α -> F} {l : Filter α}
  证明: by
  obtain ⟨A, h_op⟩ := h_op
  rcases hg with ⟨C, hC⟩; rw [eventually_map] at hC
  rw [NormedGroup.tendsto_nhds_one] at hf ⊢
  intro ε ε₀
  rcases exists_pos_mul_lt ε₀ (A * C) with ⟨δ, δ₀, hδ⟩
  filter_upwards [hf δ δ₀, hC] with i hf hg
  refine (h_op _ _).trans_lt ?_
  rcases le_total A 0 with hA 

Depends on / 依赖: NormedGroup, NormedGroup.tendsto_nhds_one, eventually_map, exists_pos_mul_lt, filter_upwards, h_op, le_total, mul_nonpos_of_nonpos_of_nonneg, mul_right_, norm_nonneg, tendsto_nhds_one, trans_lt
-/
lemma Filter.Tendsto.op_one_isBoundedUnder_le' {f : α -> E} {g : α -> F} {l : Filter α}
    (hf : Tendsto f l (𝓝 1)) (hg : IsBoundedUnder (· <= ·) l (Norm.norm ∘ g)) (op : E -> F -> G)
    (h_op : exists A, forall x y, ‖op x y‖ <= A * ‖x‖ * ‖y‖) : Tendsto (fun x => op (f x) (g x)) l (𝓝 1) := by
  obtain ⟨A, h_op⟩ := h_op
  rcases hg with ⟨C, hC⟩; rw [eventually_map] at hC
  rw [NormedGroup.tendsto_nhds_one] at hf ⊢
  intro ε ε₀
  rcases exists_pos_mul_lt ε₀ (A * C) with ⟨δ, δ₀, hδ⟩
  filter_upwards [hf δ δ₀, hC] with i hf hg
  refine (h_op _ _).trans_lt ?_
  rcases le_total A 0 with hA | hA
  · exact (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hA <| norm_nonneg' _) <|
      norm_nonneg' _).trans_lt ε₀
  calc
    A * ‖f i‖ * ‖g i‖ <= A * δ * C := by gcongr; exact hg
    _ = A * C * δ := mul_right_comm _ _ _
    _ < ε := hδ

/-- A helper lemma used to prove that the (scalar or usual) product of a function that tends to one
and a bounded function tends to one. This lemma is formulated for any binary operation
`op : E → F → G` with an estimate `‖op x y‖ ≤ ‖x‖ * ‖y‖` instead of multiplication so that it
can be applied to `(*)`, `flip (*)`, `(•)`, and `flip (•)`. -/
@[to_additive /-- A helper lemma used to prove that the (scalar or usual) product of a function that
tends to zero and a bounded function tends to zero. This lemma is formulated for any binary
operation `op : E → F → G` with an estimate `‖op x y‖ ≤ ‖x‖ * ‖y‖` instead of multiplication so
that it can be applied to `(*)`, `flip (*)`, `(•)`, and `flip (•)`. -/]
/--
theorem `Filter.Tendsto.op_one_isBoundedUnder_le` / 定理 `Filter.Tendsto.op_one_isBoundedUnder_le`

English:
theorem Filter.Tendsto.op_one_isBoundedUnder_le
  statement: {f : α -> E} {g : α -> F} {l : Filter α}
  proof: hf.op_one_isBoundedUnder_le' hg op ⟨1, fun x y => (one_mul ‖x‖).symm ▸ h_op x y⟩

@[to_additive tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding]

中文:
定理 Filter.Tendsto.op_one_isBoundedUnder_le
  结论: {f : α -> E} {g : α -> F} {l : Filter α}
  证明: hf.op_one_isBoundedUnder_le' hg op ⟨1, fun x y => (one_mul ‖x‖).symm ▸ h_op x y⟩

@[to_additive tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding]

Depends on / 依赖: h_op, hf.op_one_isBoundedUnder_le, one_mul, op_one_isBoundedUnder_le
-/
theorem Filter.Tendsto.op_one_isBoundedUnder_le {f : α -> E} {g : α -> F} {l : Filter α}
    (hf : Tendsto f l (𝓝 1)) (hg : IsBoundedUnder (· <= ·) l (Norm.norm ∘ g)) (op : E -> F -> G)
    (h_op : forall x y, ‖op x y‖ <= ‖x‖ * ‖y‖) : Tendsto (fun x => op (f x) (g x)) l (𝓝 1) :=
  hf.op_one_isBoundedUnder_le' hg op ⟨1, fun x y => (one_mul ‖x‖).symm ▸ h_op x y⟩

@[to_additive tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding]
/--
lemma `tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding'` / 引理 `tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding'`

English:
lemma tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding'
  statement: {X : Type*} [TopologicalSpace X]
  proof: by
  rw [← Filter.cocompact_eq_cofinite X]
  apply tendsto_norm_cocompact_atTop'.comp (Topology.IsClosedEmbedding.tendsto_cocompact he)

中文:
引理 tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding'
  结论: {X : 类型} [TopologicalSpace X]
  证明: by
  rw [← Filter.cocompact_eq_cofinite X]
  apply tendsto_norm_cocompact_atTop'.comp (Topology.IsClosedEmbedding.tendsto_cocompact he)

Depends on / 依赖: Filter, Filter.cocompact_eq_cofinite, IsClosedEmbedding, Topology, Topology.IsClosedEmbedding.tendsto_cocompact, cocompact_eq_cofinite, tendsto_cocompact, tendsto_norm_cocompact_atTop
-/
lemma tendsto_norm_comp_cofinite_atTop_of_isClosedEmbedding' {X : Type*} [TopologicalSpace X]
    [DiscreteTopology X] [ProperSpace E] {e : X -> E}
    (he : Topology.IsClosedEmbedding e) : Tendsto (norm ∘ e) cofinite atTop := by
  rw [← Filter.cocompact_eq_cofinite X]
  apply tendsto_norm_cocompact_atTop'.comp (Topology.IsClosedEmbedding.tendsto_cocompact he)

end SeminormedGroup

section NormedAddGroup
variable [NormedAddGroup E] [TopologicalSpace α] {f : α -> E}

/--
lemma `Continuous.bounded_above_of_compact_support` / 引理 `Continuous.bounded_above_of_compact_support`

English:
lemma Continuous.bounded_above_of_compact_support
  given: (hf : Continuous f) (h : HasCompactSupport f)
  proof: by
  simpa [bddAbove_def] using hf.norm.bddAbove_range_of_hasCompactSupport h.norm

中文:
引理 Continuous.bounded_above_of_compact_support
  条件: (hf : Continuous f) (h : HasCompactSupport f)
  证明: by
  simpa [bddAbove_def] using hf.norm.bddAbove_range_of_hasCompactSupport h.norm

Depends on / 依赖: bddAbove_def, bddAbove_range_of_hasCompactSupport, h.norm, hf.norm.bddAbove_range_of_hasCompactSupport
-/
lemma Continuous.bounded_above_of_compact_support (hf : Continuous f) (h : HasCompactSupport f) :
    exists C, forall x, ‖f x‖ <= C := by
  simpa [bddAbove_def] using hf.norm.bddAbove_range_of_hasCompactSupport h.norm

end NormedAddGroup

section NormedAddGroupSource
variable [NormedAddGroup α] {f : α -> E}

@[to_additive]
/--
lemma `HasCompactMulSupport.exists_pos_le_norm` / 引理 `HasCompactMulSupport.exists_pos_le_norm`

English:
lemma HasCompactMulSupport.exists_pos_le_norm
  given: [One E] (hf : HasCompactMulSupport f)
  proof: by
  obtain ⟨K, ⟨hK1, hK2⟩⟩ := exists_compact_iff_hasCompactMulSupport.mpr hf
  obtain ⟨S, hS, hS'⟩ := hK1.isBounded.exists_pos_norm_le
  refine ⟨S + 1, by positivity, fun x hx => hK2 x ((mt <| hS' x) ?_)⟩
  contrapose! hx
  exact lt_add_of_le_of_pos hx zero_lt_one

中文:
引理 HasCompactMulSupport.exists_pos_le_norm
  条件: [One E] (hf : HasCompactMulSupport f)
  证明: by
  obtain ⟨K, ⟨hK1, hK2⟩⟩ := exists_compact_iff_hasCompactMulSupport.mpr hf
  obtain ⟨S, hS, hS'⟩ := hK1.isBounded.exists_pos_norm_le
  refine ⟨S + 1, by positivity, fun x hx => hK2 x ((mt <| hS' x) ?_)⟩
  contrapose! hx
  exact lt_add_of_le_of_pos hx zero_lt_one

Depends on / 依赖: contrapose, exists_compact_iff_hasCompactMulSupport, exists_compact_iff_hasCompactMulSupport.mpr, exists_pos_norm_le, hK1.isBounded.exists_pos_norm_le, isBounded, lt_add_of_le_of_pos, zero_lt_one
-/
lemma HasCompactMulSupport.exists_pos_le_norm [One E] (hf : HasCompactMulSupport f) :
    exists R : Real, 0 < R ∧ forall x : α, R <= ‖x‖ -> f x = 1 := by
  obtain ⟨K, ⟨hK1, hK2⟩⟩ := exists_compact_iff_hasCompactMulSupport.mpr hf
  obtain ⟨S, hS, hS'⟩ := hK1.isBounded.exists_pos_norm_le
  refine ⟨S + 1, by positivity, fun x hx => hK2 x ((mt <| hS' x) ?_)⟩
  contrapose! hx
  exact lt_add_of_le_of_pos hx zero_lt_one

end NormedAddGroupSource
