/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Antoine Chambert-Loir, Anatole Dedecker
-/
module

public import Mathlib.Topology.Semicontinuity.Defs
public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.Topology.Piecewise
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Lower and Upper Semicontinuity

This file develops key properties of upper and lower semicontinuous functions.

## Main definitions and results

We have some equivalent definitions of lower- and upper-semicontinuity (under certain
restrictions on the order on the codomain):
* `lowerSemicontinuous_iff_isOpen_preimage` in a linear order;
* `lowerSemicontinuous_iff_isClosed_preimage` in a linear order;
* `lowerSemicontinuousAt_iff_le_liminf` in a complete linear order;
* `lowerSemicontinuous_iff_isClosed_epigraph` in a linear order with the order
  topology.

We also prove:

* `indicator s (fun _ ↦ y)` is lower semicontinuous when `s` is open and `0 ≤ y`,
  or when `s` is closed and `y ≤ 0`;
* continuous functions are lower semicontinuous;
* left composition with a continuous monotone functions maps lower semicontinuous functions to lower
  semicontinuous functions. If the function is anti-monotone, it instead maps lower semicontinuous
  functions to upper semicontinuous functions;
* a sum of two (or finitely many) lower semicontinuous functions is lower semicontinuous;
* a supremum of a family of lower semicontinuous functions is lower semicontinuous;
* An infinite sum of `ℝ≥0∞`-valued lower semicontinuous functions is lower semicontinuous.

Similar results are stated and proved for upper semicontinuity.

We also prove that a function is continuous if and only if it is both lower and upper
semicontinuous.

## Implementation details

All the nontrivial results for upper semicontinuous functions are deduced from the corresponding
ones for lower semicontinuous functions using `OrderDual`.

## References

* <https://en.wikipedia.org/wiki/Closed_convex_function>
* <https://en.wikipedia.org/wiki/Semi-continuity>


+ lower and upper semicontinuity correspond to `r := (f · > ·)` and `r := (f · < ·)`;
+ lower and upper hemicontinuity correspond to `r := (fun x s ↦ IsOpen s ∧ ((f x) ∩ s).Nonempty)`
  and `r := (fun x s ↦ s ∈ 𝓝ˢ (f x))`, respectively.
-/

public section

open Topology ENNReal

open Set Function Filter

variable {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace γ] {f : α -> β} {s t : Set α}
  {x : α} {y z : β}

/-! ### lower bounds -/

section

variable [LinearOrder β]

/--
theorem `LowerSemicontinuousOn.exists_isMinOn` / 定理 `LowerSemicontinuousOn.exists_isMinOn`

English:
theorem LowerSemicontinuousOn.exists_isMinOn
  statement: {s : Set α} (ne_s : s.Nonempty)
  proof: by
  simp only [isMinOn_iff]
  have _ : Nonempty α := Exists.nonempty ne_s
  have _ : Nonempty s := Nonempty.to_subtype ne_s
  let φ : β -> Filter α := fun b => 𝓟 (s inter f ⁻¹' Iic b)
  let ℱ : Filter α := ⨅ a : s, φ (f a)
  have : ℱ.NeBot := by
    apply iInf_neBot_of_directed _ _
    · change Dir

中文:
定理 LowerSemicontinuousOn.存在_isMinOn
  结论: {s : 集合 α} (ne_s : s.非空)
  证明: by
  simp only [isMinOn_iff]
  have _ : Nonempty α := Exists.nonempty ne_s
  have _ : Nonempty s := Nonempty.to_subtype ne_s
  let φ : β -> Filter α := fun b => 𝓟 (s inter f ⁻¹' Iic b)
  let ℱ : Filter α := ⨅ a : s, φ (f a)
  have : ℱ.NeBot := by
    apply iInf_neBot_of_directed _ _
    · change Dir

Depends on / 依赖: Directed, Directed.mono_comp, Exists, Exists.nonempty, Filter, GE.ge, Iic_subset_Iic, Iic_subset_Iic.mpr, Nonempty, Nonempty.to_subtype, Std.Total.directed, directed, iInf_neBot_of_directed, inter_subset_inter_right, isMinOn_iff, mono_comp, ne_s, nonempty, preimage_mono, principal_mono
-/
theorem LowerSemicontinuousOn.exists_isMinOn {s : Set α} (ne_s : s.Nonempty)
    (hs : IsCompact s) (hf : LowerSemicontinuousOn f s) :
    exists a in s, IsMinOn f s a := by
  simp only [isMinOn_iff]
  have _ : Nonempty α := Exists.nonempty ne_s
  have _ : Nonempty s := Nonempty.to_subtype ne_s
  let φ : β -> Filter α := fun b => 𝓟 (s inter f ⁻¹' Iic b)
  let ℱ : Filter α := ⨅ a : s, φ (f a)
  have : ℱ.NeBot := by
    apply iInf_neBot_of_directed _ _
    · change Directed GE.ge (fun x => (φ ∘ (fun (a : s) => f ↑a)) x)
      exact Directed.mono_comp GE.ge (fun x y hxy =>
        principal_mono.mpr (inter_subset_inter_right _ (preimage_mono <| Iic_subset_Iic.mpr hxy)))
        (Std.Total.directed _)
    · intro x
      have : (pure x : Filter α) <= φ (f x) := le_principal_iff.mpr ⟨x.2, le_refl (f x)⟩
      exact neBot_of_le this
  have hℱs : ℱ <= 𝓟 s :=
    iInf_le_of_le (Classical.choice inferInstance) (principal_mono.mpr <| inter_subset_left)
  have hℱ (x) (hx : x in s) : forallᶠ y in ℱ, f y <= f x :=
    mem_iInf_of_mem ⟨x, hx⟩ (by apply inter_subset_right)
  obtain ⟨a, ha, h⟩ := hs hℱs
  refine ⟨a, ha, fun x hx => le_of_not_gt fun hxa => ?_⟩
  let _ : (𝓝 a ⊓ ℱ).NeBot := h
  suffices forallᶠ _ in 𝓝 a ⊓ ℱ, False by rwa [eventually_const] at this
  filter_upwards [(hf a ha (f x) hxa).filter_mono (inf_le_inf_left _ hℱs),
    (hℱ x hx).filter_mono (inf_le_right : 𝓝 a ⊓ ℱ <= ℱ)] using fun y h₁ h₂ => not_le_of_gt h₁ h₂

/--
theorem `LowerSemicontinuousOn.bddBelow_of_isCompact` / 定理 `LowerSemicontinuousOn.bddBelow_of_isCompact`

English:
theorem LowerSemicontinuousOn.bddBelow_of_isCompact
  statement: [Nonempty β] {s : Set α} (hs : IsCompact s)
  proof: by
  cases s.eq_empty_or_nonempty with
  | inl h =>
      simp only [h, Set.image_empty]
      exact bddBelow_empty
  | inr h =>
      obtain ⟨a, _, has⟩ := LowerSemicontinuousOn.exists_isMinOn h hs hf
      exact has.bddBelow

中文:
定理 LowerSemicontinuousOn.bddBelow_of_isCompact
  结论: [非空 β] {s : 集合 α} (hs : 是紧集 s)
  证明: by
  cases s.eq_empty_or_nonempty with
  | inl h =>
      simp only [h, Set.image_empty]
      exact bddBelow_empty
  | inr h =>
      obtain ⟨a, _, has⟩ := LowerSemicontinuousOn.exists_isMinOn h hs hf
      exact has.bddBelow

Depends on / 依赖: LowerSemicontinuousOn, LowerSemicontinuousOn.exists_isMinOn, Set.image_empty, bddBelow, bddBelow_empty, eq_empty_or_nonempty, exists_isMinOn, has.bddBelow, image_empty, s.eq_empty_or_nonempty
-/
theorem LowerSemicontinuousOn.bddBelow_of_isCompact [Nonempty β] {s : Set α} (hs : IsCompact s)
    (hf : LowerSemicontinuousOn f s) : BddBelow (f '' s) := by
  cases s.eq_empty_or_nonempty with
  | inl h =>
      simp only [h, Set.image_empty]
      exact bddBelow_empty
  | inr h =>
      obtain ⟨a, _, has⟩ := LowerSemicontinuousOn.exists_isMinOn h hs hf
      exact has.bddBelow

end

/-! #### Indicators -/


section

variable [Zero β] [Preorder β]

/--
theorem `IsOpen.lowerSemicontinuous_indicator` / 定理 `IsOpen.lowerSemicontinuous_indicator`

English:
theorem IsOpen.lowerSemicontinuous_indicator
  given: (hs : IsOpen s) (hy : 0 <= y)
  proof: by
  intro x z hz
  by_cases h : x in s <;> simp [h] at hz
  · filter_upwards [hs.mem_nhds h]
    simp +contextual [hz]
  · refine Filter.Eventually.of_forall fun x' => ?_
    by_cases h' : x' in s <;> simp [h', hz.trans_le hy, hz]

中文:
定理 是开集.lowerSemicontinuous_indicator
  条件: (hs : 是开集 s) (hy : 0 <= y)
  证明: by
  intro x z hz
  by_cases h : x in s <;> simp [h] at hz
  · filter_upwards [hs.mem_nhds h]
    simp +contextual [hz]
  · refine Filter.Eventually.of_forall fun x' => ?_
    by_cases h' : x' in s <;> simp [h', hz.trans_le hy, hz]

Depends on / 依赖: Eventually, Filter, Filter.Eventually.of_forall, contextual, filter_upwards, hs.mem_nhds, hz.trans_le, mem_nhds, of_forall, trans_le
-/
theorem IsOpen.lowerSemicontinuous_indicator (hs : IsOpen s) (hy : 0 <= y) :
    LowerSemicontinuous (indicator s fun _x => y) := by
  intro x z hz
  by_cases h : x in s <;> simp [h] at hz
  · filter_upwards [hs.mem_nhds h]
    simp +contextual [hz]
  · refine Filter.Eventually.of_forall fun x' => ?_
    by_cases h' : x' in s <;> simp [h', hz.trans_le hy, hz]

/--
theorem `IsOpen.lowerSemicontinuousOn_indicator` / 定理 `IsOpen.lowerSemicontinuousOn_indicator`

English:
theorem IsOpen.lowerSemicontinuousOn_indicator
  given: (hs : IsOpen s) (hy : 0 <= y)
  proof: (hs.lowerSemicontinuous_indicator hy).lowerSemicontinuousOn t

中文:
定理 是开集.lowerSemicontinuousOn_indicator
  条件: (hs : 是开集 s) (hy : 0 <= y)
  证明: (hs.lowerSemicontinuous_indicator hy).lowerSemicontinuousOn t

Depends on / 依赖: hs.lowerSemicontinuous_indicator, lowerSemicontinuousOn, lowerSemicontinuous_indicator
-/
theorem IsOpen.lowerSemicontinuousOn_indicator (hs : IsOpen s) (hy : 0 <= y) :
    LowerSemicontinuousOn (indicator s fun _x => y) t :=
  (hs.lowerSemicontinuous_indicator hy).lowerSemicontinuousOn t

/--
theorem `IsOpen.lowerSemicontinuousAt_indicator` / 定理 `IsOpen.lowerSemicontinuousAt_indicator`

English:
theorem IsOpen.lowerSemicontinuousAt_indicator
  given: (hs : IsOpen s) (hy : 0 <= y)
  proof: (hs.lowerSemicontinuous_indicator hy).lowerSemicontinuousAt x

中文:
定理 是开集.lowerSemicontinuousAt_indicator
  条件: (hs : 是开集 s) (hy : 0 <= y)
  证明: (hs.lowerSemicontinuous_indicator hy).lowerSemicontinuousAt x

Depends on / 依赖: hs.lowerSemicontinuous_indicator, lowerSemicontinuousAt, lowerSemicontinuous_indicator
-/
theorem IsOpen.lowerSemicontinuousAt_indicator (hs : IsOpen s) (hy : 0 <= y) :
    LowerSemicontinuousAt (indicator s fun _x => y) x :=
  (hs.lowerSemicontinuous_indicator hy).lowerSemicontinuousAt x

/--
theorem `IsOpen.lowerSemicontinuousWithinAt_indicator` / 定理 `IsOpen.lowerSemicontinuousWithinAt_indicator`

English:
theorem IsOpen.lowerSemicontinuousWithinAt_indicator
  given: (hs : IsOpen s) (hy : 0 <= y)
  proof: (hs.lowerSemicontinuous_indicator hy).lowerSemicontinuousWithinAt t x

中文:
定理 是开集.lowerSemicontinuousWithinAt_indicator
  条件: (hs : 是开集 s) (hy : 0 <= y)
  证明: (hs.lowerSemicontinuous_indicator hy).lowerSemicontinuousWithinAt t x

Depends on / 依赖: hs.lowerSemicontinuous_indicator, lowerSemicontinuousWithinAt, lowerSemicontinuous_indicator
-/
theorem IsOpen.lowerSemicontinuousWithinAt_indicator (hs : IsOpen s) (hy : 0 <= y) :
    LowerSemicontinuousWithinAt (indicator s fun _x => y) t x :=
  (hs.lowerSemicontinuous_indicator hy).lowerSemicontinuousWithinAt t x

/--
theorem `IsClosed.lowerSemicontinuous_indicator` / 定理 `IsClosed.lowerSemicontinuous_indicator`

English:
theorem IsClosed.lowerSemicontinuous_indicator
  given: (hs : IsClosed s) (hy : y <= 0)
  proof: by
  intro x z hz
  by_cases h : x in s <;> simp [h] at hz
  · refine Filter.Eventually.of_forall fun x' => ?_
    by_cases h' : x' in s <;> simp [h', hz, hz.trans_le hy]
  · filter_upwards [hs.isOpen_compl.mem_nhds h]
    simp +contextual [hz]

中文:
定理 是闭集.lowerSemicontinuous_indicator
  条件: (hs : 是闭集 s) (hy : y <= 0)
  证明: by
  intro x z hz
  by_cases h : x in s <;> simp [h] at hz
  · refine Filter.Eventually.of_forall fun x' => ?_
    by_cases h' : x' in s <;> simp [h', hz, hz.trans_le hy]
  · filter_upwards [hs.isOpen_compl.mem_nhds h]
    simp +contextual [hz]

Depends on / 依赖: Eventually, Filter, Filter.Eventually.of_forall, contextual, filter_upwards, hs.isOpen_compl.mem_nhds, hz.trans_le, isOpen_compl, mem_nhds, of_forall, trans_le
-/
theorem IsClosed.lowerSemicontinuous_indicator (hs : IsClosed s) (hy : y <= 0) :
    LowerSemicontinuous (indicator s fun _x => y) := by
  intro x z hz
  by_cases h : x in s <;> simp [h] at hz
  · refine Filter.Eventually.of_forall fun x' => ?_
    by_cases h' : x' in s <;> simp [h', hz, hz.trans_le hy]
  · filter_upwards [hs.isOpen_compl.mem_nhds h]
    simp +contextual [hz]

/--
theorem `IsClosed.lowerSemicontinuousOn_indicator` / 定理 `IsClosed.lowerSemicontinuousOn_indicator`

English:
theorem IsClosed.lowerSemicontinuousOn_indicator
  given: (hs : IsClosed s) (hy : y <= 0)
  proof: (hs.lowerSemicontinuous_indicator hy).lowerSemicontinuousOn t

中文:
定理 是闭集.lowerSemicontinuousOn_indicator
  条件: (hs : 是闭集 s) (hy : y <= 0)
  证明: (hs.lowerSemicontinuous_indicator hy).lowerSemicontinuousOn t

Depends on / 依赖: hs.lowerSemicontinuous_indicator, lowerSemicontinuousOn, lowerSemicontinuous_indicator
-/
theorem IsClosed.lowerSemicontinuousOn_indicator (hs : IsClosed s) (hy : y <= 0) :
    LowerSemicontinuousOn (indicator s fun _x => y) t :=
  (hs.lowerSemicontinuous_indicator hy).lowerSemicontinuousOn t

/--
theorem `IsClosed.lowerSemicontinuousAt_indicator` / 定理 `IsClosed.lowerSemicontinuousAt_indicator`

English:
theorem IsClosed.lowerSemicontinuousAt_indicator
  given: (hs : IsClosed s) (hy : y <= 0)
  proof: (hs.lowerSemicontinuous_indicator hy).lowerSemicontinuousAt x

中文:
定理 是闭集.lowerSemicontinuousAt_indicator
  条件: (hs : 是闭集 s) (hy : y <= 0)
  证明: (hs.lowerSemicontinuous_indicator hy).lowerSemicontinuousAt x

Depends on / 依赖: hs.lowerSemicontinuous_indicator, lowerSemicontinuousAt, lowerSemicontinuous_indicator
-/
theorem IsClosed.lowerSemicontinuousAt_indicator (hs : IsClosed s) (hy : y <= 0) :
    LowerSemicontinuousAt (indicator s fun _x => y) x :=
  (hs.lowerSemicontinuous_indicator hy).lowerSemicontinuousAt x

/--
theorem `IsClosed.lowerSemicontinuousWithinAt_indicator` / 定理 `IsClosed.lowerSemicontinuousWithinAt_indicator`

English:
theorem IsClosed.lowerSemicontinuousWithinAt_indicator
  given: (hs : IsClosed s) (hy : y <= 0)
  proof: (hs.lowerSemicontinuous_indicator hy).lowerSemicontinuousWithinAt t x

中文:
定理 是闭集.lowerSemicontinuousWithinAt_indicator
  条件: (hs : 是闭集 s) (hy : y <= 0)
  证明: (hs.lowerSemicontinuous_indicator hy).lowerSemicontinuousWithinAt t x

Depends on / 依赖: hs.lowerSemicontinuous_indicator, lowerSemicontinuousWithinAt, lowerSemicontinuous_indicator
-/
theorem IsClosed.lowerSemicontinuousWithinAt_indicator (hs : IsClosed s) (hy : y <= 0) :
    LowerSemicontinuousWithinAt (indicator s fun _x => y) t x :=
  (hs.lowerSemicontinuous_indicator hy).lowerSemicontinuousWithinAt t x

end

/-! #### Relationship with continuity -/

section

variable [Preorder β]

/--
theorem `lowerSemicontinuous_iff_isOpen_preimage` / 定理 `lowerSemicontinuous_iff_isOpen_preimage`

English:
theorem lowerSemicontinuous_iff_isOpen_preimage
  proof: ⟨fun H y => isOpen_iff_mem_nhds.2 fun x hx => H x y hx, fun H _x y y_lt =>
    IsOpen.mem_nhds (H y) y_lt⟩

中文:
定理 lowerSemicontinuous_iff_isOpen_preimage
  证明: ⟨fun H y => isOpen_iff_mem_nhds.2 fun x hx => H x y hx, fun H _x y y_lt =>
    IsOpen.mem_nhds (H y) y_lt⟩

Depends on / 依赖: IsOpen, IsOpen.mem_nhds, isOpen_iff_mem_nhds, mem_nhds, y_lt
-/
theorem lowerSemicontinuous_iff_isOpen_preimage :
    LowerSemicontinuous f ↔ forall y, IsOpen (f ⁻¹' Ioi y) :=
  ⟨fun H y => isOpen_iff_mem_nhds.2 fun x hx => H x y hx, fun H _x y y_lt =>
    IsOpen.mem_nhds (H y) y_lt⟩

/--
theorem `LowerSemicontinuous.isOpen_preimage` / 定理 `LowerSemicontinuous.isOpen_preimage`

English:
theorem LowerSemicontinuous.isOpen_preimage
  given: (hf : LowerSemicontinuous f) (y : β)
  proof: lowerSemicontinuous_iff_isOpen_preimage.1 hf y

中文:
定理 LowerSemicontinuous.isOpen_preimage
  条件: (hf : LowerSemicontinuous f) (y : β)
  证明: lowerSemicontinuous_iff_isOpen_preimage.1 hf y

Depends on / 依赖: lowerSemicontinuous_iff_isOpen_preimage
-/
theorem LowerSemicontinuous.isOpen_preimage (hf : LowerSemicontinuous f) (y : β) :
    IsOpen (f ⁻¹' Ioi y) :=
  lowerSemicontinuous_iff_isOpen_preimage.1 hf y

/--
theorem `lowerSemicontinuousOn_iff_preimage_Ioi` / 定理 `lowerSemicontinuousOn_iff_preimage_Ioi`

English:
theorem lowerSemicontinuousOn_iff_preimage_Ioi
  proof: by
  simp only [← lowerSemicontinuous_restrict_iff, domRestrict_eq,
    lowerSemicontinuous_iff_isOpen_preimage, preimage_comp, isOpen_induced_iff,
    Subtype.preimage_coe_eq_preimage_coe_iff, eq_comm]

中文:
定理 lowerSemicontinuousOn_iff_preimage_Ioi
  证明: by
  simp only [← lowerSemicontinuous_restrict_iff, domRestrict_eq,
    lowerSemicontinuous_iff_isOpen_preimage, preimage_comp, isOpen_induced_iff,
    Subtype.preimage_coe_eq_preimage_coe_iff, eq_comm]

Depends on / 依赖: Subtype, Subtype.preimage_coe_eq_preimage_coe_iff, domRestrict_eq, eq_comm, isOpen_induced_iff, lowerSemicontinuous_iff_isOpen_preimage, lowerSemicontinuous_restrict_iff, preimage_coe_eq_preimage_coe_iff, preimage_comp
-/
theorem lowerSemicontinuousOn_iff_preimage_Ioi :
    LowerSemicontinuousOn f s ↔ forall b, exists u, IsOpen u ∧ s inter f ⁻¹' Set.Ioi b = s inter u := by
  simp only [← lowerSemicontinuous_restrict_iff, domRestrict_eq,
    lowerSemicontinuous_iff_isOpen_preimage, preimage_comp, isOpen_induced_iff,
    Subtype.preimage_coe_eq_preimage_coe_iff, eq_comm]

end

section

variable {ι : Type*} {f : ι -> α -> β} [Preorder β] {I : Set ι}

/--
theorem `lowerSemicontinuousOn_of_forall_isMaxOn_and_mem` / 定理 `lowerSemicontinuousOn_of_forall_isMaxOn_and_mem`

English:
theorem lowerSemicontinuousOn_of_forall_isMaxOn_and_mem
  proof: by
  intro x hx b hb
apply Filter.Eventually.mp hfy (M x) (M_mem x hx) x hx b hb
  apply eventually_nhdsWithin_of_forall
  intro z hz h
  exact lt_of_lt_of_le h (M_max z hz (M_mem x hx))

中文:
定理 lowerSemicontinuousOn_of_对任意_isMaxOn_and_mem
  证明: by
  intro x hx b hb
apply Filter.Eventually.mp hfy (M x) (M_mem x hx) x hx b hb
  apply eventually_nhdsWithin_of_forall
  intro z hz h
  exact lt_of_lt_of_le h (M_max z hz (M_mem x hx))

Depends on / 依赖: Eventually, Filter, Filter.Eventually.mp, M_max, M_mem, eventually_nhdsWithin_of_forall, lt_of_lt_of_le
-/
theorem lowerSemicontinuousOn_of_forall_isMaxOn_and_mem
    (hfy : forall i in I, LowerSemicontinuousOn (f i) s)
    {M : α -> ι}
    (M_mem : forall x in s, M x in I)
    (M_max : forall x in s, IsMaxOn (fun y => f y x) I (M x)) :
    LowerSemicontinuousOn (fun x => f (M x) x) s := by
  intro x hx b hb
apply Filter.Eventually.mp hfy (M x) (M_mem x hx) x hx b hb
  apply eventually_nhdsWithin_of_forall
  intro z hz h
  exact lt_of_lt_of_le h (M_max z hz (M_mem x hx))

/--
theorem `upperSemicontinuousOn_of_forall_isMinOn_and_mem` / 定理 `upperSemicontinuousOn_of_forall_isMinOn_and_mem`

English:
theorem upperSemicontinuousOn_of_forall_isMinOn_and_mem
  proof: lowerSemicontinuousOn_of_forall_isMaxOn_and_mem (β := βᵒᵈ) hfy m_mem m_min

中文:
定理 upperSemicontinuousOn_of_对任意_isMinOn_and_mem
  证明: lowerSemicontinuousOn_of_forall_isMaxOn_and_mem (β := βᵒᵈ) hfy m_mem m_min

Depends on / 依赖: lowerSemicontinuousOn_of_forall_isMaxOn_and_mem, m_mem, m_min
-/
theorem upperSemicontinuousOn_of_forall_isMinOn_and_mem
    (hfy : forall i in I, UpperSemicontinuousOn (f i) s)
    {m : α -> ι}
    (m_mem : forall x in s, m x in I)
    (m_min : forall x in s, IsMinOn (fun i => f i x) I (m x)) :
    UpperSemicontinuousOn (fun x => f (m x) x) s :=
  lowerSemicontinuousOn_of_forall_isMaxOn_and_mem (β := βᵒᵈ) hfy m_mem m_min

end

section

variable {γ : Type*} [LinearOrder γ]

/--
theorem `lowerSemicontinuous_iff_isClosed_preimage` / 定理 `lowerSemicontinuous_iff_isClosed_preimage`

English:
theorem lowerSemicontinuous_iff_isClosed_preimage
  given: {f : α -> γ}
  proof: by
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  simp only [← isOpen_compl_iff, ← preimage_compl, compl_Iic]

中文:
定理 lowerSemicontinuous_iff_isClosed_preimage
  条件: {f : α -> γ}
  证明: by
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  simp only [← isOpen_compl_iff, ← preimage_compl, compl_Iic]

Depends on / 依赖: compl_Iic, isOpen_compl_iff, lowerSemicontinuous_iff_isOpen_preimage, preimage_compl
-/
theorem lowerSemicontinuous_iff_isClosed_preimage {f : α -> γ} :
    LowerSemicontinuous f ↔ forall y, IsClosed (f ⁻¹' Iic y) := by
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  simp only [← isOpen_compl_iff, ← preimage_compl, compl_Iic]

/--
theorem `LowerSemicontinuous.isClosed_preimage` / 定理 `LowerSemicontinuous.isClosed_preimage`

English:
theorem LowerSemicontinuous.isClosed_preimage
  given: {f : α -> γ} (hf : LowerSemicontinuous f) (y : γ)
  proof: lowerSemicontinuous_iff_isClosed_preimage.1 hf y

中文:
定理 LowerSemicontinuous.isClosed_preimage
  条件: {f : α -> γ} (hf : LowerSemicontinuous f) (y : γ)
  证明: lowerSemicontinuous_iff_isClosed_preimage.1 hf y

Depends on / 依赖: lowerSemicontinuous_iff_isClosed_preimage
-/
theorem LowerSemicontinuous.isClosed_preimage {f : α -> γ} (hf : LowerSemicontinuous f) (y : γ) :
    IsClosed (f ⁻¹' Iic y) :=
  lowerSemicontinuous_iff_isClosed_preimage.1 hf y

/--
theorem `lowerSemicontinuousOn_iff_preimage_Iic` / 定理 `lowerSemicontinuousOn_iff_preimage_Iic`

English:
theorem lowerSemicontinuousOn_iff_preimage_Iic
  given: {f : α -> γ}
  proof: by
  simp only [← lowerSemicontinuous_restrict_iff, domRestrict_eq,
      lowerSemicontinuous_iff_isClosed_preimage, preimage_comp,
      isClosed_induced_iff, Subtype.preimage_coe_eq_preimage_coe_iff, eq_comm]

中文:
定理 lowerSemicontinuousOn_iff_preimage_Iic
  条件: {f : α -> γ}
  证明: by
  simp only [← lowerSemicontinuous_restrict_iff, domRestrict_eq,
      lowerSemicontinuous_iff_isClosed_preimage, preimage_comp,
      isClosed_induced_iff, Subtype.preimage_coe_eq_preimage_coe_iff, eq_comm]

Depends on / 依赖: Subtype, Subtype.preimage_coe_eq_preimage_coe_iff, domRestrict_eq, eq_comm, isClosed_induced_iff, lowerSemicontinuous_iff_isClosed_preimage, lowerSemicontinuous_restrict_iff, preimage_coe_eq_preimage_coe_iff, preimage_comp
-/
theorem lowerSemicontinuousOn_iff_preimage_Iic {f : α -> γ} :
    LowerSemicontinuousOn f s ↔ forall b, exists v, IsClosed v ∧ s inter f ⁻¹' Set.Iic b = s inter v := by
  simp only [← lowerSemicontinuous_restrict_iff, domRestrict_eq,
      lowerSemicontinuous_iff_isClosed_preimage, preimage_comp,
      isClosed_induced_iff, Subtype.preimage_coe_eq_preimage_coe_iff, eq_comm]

variable [TopologicalSpace γ] [OrderTopology γ]

/--
theorem `ContinuousWithinAt.lowerSemicontinuousWithinAt` / 定理 `ContinuousWithinAt.lowerSemicontinuousWithinAt`

English:
theorem ContinuousWithinAt.lowerSemicontinuousWithinAt
  given: {f : α -> γ} (h : ContinuousWithinAt f s x)
  proof: fun _y hy => h (Ioi_mem_nhds hy)

中文:
定理 ContinuousWithinAt.lowerSemicontinuousWithinAt
  条件: {f : α -> γ} (h : ContinuousWithinAt f s x)
  证明: fun _y hy => h (Ioi_mem_nhds hy)

Depends on / 依赖: Ioi_mem_nhds
-/
theorem ContinuousWithinAt.lowerSemicontinuousWithinAt {f : α -> γ} (h : ContinuousWithinAt f s x) :
    LowerSemicontinuousWithinAt f s x := fun _y hy => h (Ioi_mem_nhds hy)

/--
theorem `ContinuousAt.lowerSemicontinuousAt` / 定理 `ContinuousAt.lowerSemicontinuousAt`

English:
theorem ContinuousAt.lowerSemicontinuousAt
  given: {f : α -> γ} (h : ContinuousAt f x)
  proof: fun _y hy => h (Ioi_mem_nhds hy)

中文:
定理 ContinuousAt.lowerSemicontinuousAt
  条件: {f : α -> γ} (h : ContinuousAt f x)
  证明: fun _y hy => h (Ioi_mem_nhds hy)

Depends on / 依赖: Ioi_mem_nhds
-/
theorem ContinuousAt.lowerSemicontinuousAt {f : α -> γ} (h : ContinuousAt f x) :
    LowerSemicontinuousAt f x := fun _y hy => h (Ioi_mem_nhds hy)

/--
theorem `ContinuousOn.lowerSemicontinuousOn` / 定理 `ContinuousOn.lowerSemicontinuousOn`

English:
theorem ContinuousOn.lowerSemicontinuousOn
  given: {f : α -> γ} (h : ContinuousOn f s)
  proof: fun x hx => (h x hx).lowerSemicontinuousWithinAt

中文:
定理 ContinuousOn.lowerSemicontinuousOn
  条件: {f : α -> γ} (h : ContinuousOn f s)
  证明: fun x hx => (h x hx).lowerSemicontinuousWithinAt

Depends on / 依赖: lowerSemicontinuousWithinAt
-/
theorem ContinuousOn.lowerSemicontinuousOn {f : α -> γ} (h : ContinuousOn f s) :
    LowerSemicontinuousOn f s := fun x hx => (h x hx).lowerSemicontinuousWithinAt

/--
theorem `Continuous.lowerSemicontinuous` / 定理 `Continuous.lowerSemicontinuous`

English:
theorem Continuous.lowerSemicontinuous
  given: {f : α -> γ} (h : Continuous f)
  statement: LowerSemicontinuous f
  proof: fun _x => h.continuousAt.lowerSemicontinuousAt

中文:
定理 连续.lowerSemicontinuous
  条件: {f : α -> γ} (h : 连续 f)
  结论: LowerSemicontinuous f
  证明: fun _x => h.continuousAt.lowerSemicontinuousAt

Depends on / 依赖: continuousAt, h.continuousAt.lowerSemicontinuousAt, lowerSemicontinuousAt
-/
theorem Continuous.lowerSemicontinuous {f : α -> γ} (h : Continuous f) : LowerSemicontinuous f :=
  fun _x => h.continuousAt.lowerSemicontinuousAt

end

/-! #### Equivalent definitions -/

section

variable {γ : Type*} [CompleteLinearOrder γ]

/--
theorem `lowerSemicontinuousWithinAt_iff_le_liminf` / 定理 `lowerSemicontinuousWithinAt_iff_le_liminf`

English:
theorem lowerSemicontinuousWithinAt_iff_le_liminf
  given: {f : α -> γ}
  proof: by
  constructor
  · intro h; unfold LowerSemicontinuousWithinAt at h
    by_contra! hf
    obtain ⟨z, ltz, y, ylt, h₁⟩ := hf.exists_disjoint_Iio_Ioi
    exact ltz.not_ge
      (le_liminf_of_le (by isBoundedDefault) ((h y ylt).mono fun _ h₂ =>
        le_of_not_gt fun h₃ => (h₁ _ h₃ _ h₂).false))
  

中文:
定理 lowerSemicontinuousWithinAt_iff_le_liminf
  条件: {f : α -> γ}
  证明: by
  constructor
  · intro h; unfold LowerSemicontinuousWithinAt at h
    by_contra! hf
    obtain ⟨z, ltz, y, ylt, h₁⟩ := hf.exists_disjoint_Iio_Ioi
    exact ltz.not_ge
      (le_liminf_of_le (by isBoundedDefault) ((h y ylt).mono fun _ h₂ =>
        le_of_not_gt fun h₃ => (h₁ _ h₃ _ h₂).false))
  

Depends on / 依赖: LowerSemicontinuousWithinAt, eventually_lt_of_lt_liminf, exists_disjoint_Iio_Ioi, hf.exists_disjoint_Iio_Ioi, isBoundedDefault, le_liminf_of_le, le_of_not_gt, ltz.not_ge, not_ge, trans_le, ylt.trans_le
-/
theorem lowerSemicontinuousWithinAt_iff_le_liminf {f : α -> γ} :
    LowerSemicontinuousWithinAt f s x ↔ f x <= liminf f (𝓝[s] x) := by
  constructor
  · intro h; unfold LowerSemicontinuousWithinAt at h
    by_contra! hf
    obtain ⟨z, ltz, y, ylt, h₁⟩ := hf.exists_disjoint_Iio_Ioi
    exact ltz.not_ge
      (le_liminf_of_le (by isBoundedDefault) ((h y ylt).mono fun _ h₂ =>
        le_of_not_gt fun h₃ => (h₁ _ h₃ _ h₂).false))
  exact fun hf y ylt => eventually_lt_of_lt_liminf (ylt.trans_le hf)

alias ⟨LowerSemicontinuousWithinAt.le_liminf, _⟩ := lowerSemicontinuousWithinAt_iff_le_liminf

/--
theorem `lowerSemicontinuousAt_iff_le_liminf` / 定理 `lowerSemicontinuousAt_iff_le_liminf`

English:
theorem lowerSemicontinuousAt_iff_le_liminf
  given: {f : α -> γ}
  proof: by
  rw [← lowerSemicontinuousWithinAt_univ_iff]; rw [lowerSemicontinuousWithinAt_iff_le_liminf]; rw [← nhdsWithin_univ]

alias ⟨LowerSemicontinuousAt.le_liminf, _⟩ := lowerSemicontinuousAt_iff_le_liminf

中文:
定理 lowerSemicontinuousAt_iff_le_liminf
  条件: {f : α -> γ}
  证明: by
  rw [← lowerSemicontinuousWithinAt_univ_iff]; rw [lowerSemicontinuousWithinAt_iff_le_liminf]; rw [← nhdsWithin_univ]

alias ⟨LowerSemicontinuousAt.le_liminf, _⟩ := lowerSemicontinuousAt_iff_le_liminf

Depends on / 依赖: lowerSemicontinuousWithinAt_iff_le_liminf, lowerSemicontinuousWithinAt_univ_iff, nhdsWithin_univ
-/
theorem lowerSemicontinuousAt_iff_le_liminf {f : α -> γ} :
    LowerSemicontinuousAt f x ↔ f x <= liminf f (𝓝 x) := by
  rw [← lowerSemicontinuousWithinAt_univ_iff]; rw [lowerSemicontinuousWithinAt_iff_le_liminf]; rw [← nhdsWithin_univ]

alias ⟨LowerSemicontinuousAt.le_liminf, _⟩ := lowerSemicontinuousAt_iff_le_liminf

/--
theorem `lowerSemicontinuous_iff_le_liminf` / 定理 `lowerSemicontinuous_iff_le_liminf`

English:
theorem lowerSemicontinuous_iff_le_liminf
  given: {f : α -> γ}
  proof: by
  simp only [← lowerSemicontinuousAt_iff_le_liminf, lowerSemicontinuous_iff]

alias ⟨LowerSemicontinuous.le_liminf, _⟩ := lowerSemicontinuous_iff_le_liminf

中文:
定理 lowerSemicontinuous_iff_le_liminf
  条件: {f : α -> γ}
  证明: by
  simp only [← lowerSemicontinuousAt_iff_le_liminf, lowerSemicontinuous_iff]

alias ⟨LowerSemicontinuous.le_liminf, _⟩ := lowerSemicontinuous_iff_le_liminf

Depends on / 依赖: lowerSemicontinuousAt_iff_le_liminf, lowerSemicontinuous_iff
-/
theorem lowerSemicontinuous_iff_le_liminf {f : α -> γ} :
    LowerSemicontinuous f ↔ forall x, f x <= liminf f (𝓝 x) := by
  simp only [← lowerSemicontinuousAt_iff_le_liminf, lowerSemicontinuous_iff]

alias ⟨LowerSemicontinuous.le_liminf, _⟩ := lowerSemicontinuous_iff_le_liminf

/--
theorem `lowerSemicontinuousOn_iff_le_liminf` / 定理 `lowerSemicontinuousOn_iff_le_liminf`

English:
theorem lowerSemicontinuousOn_iff_le_liminf
  given: {f : α -> γ}
  proof: by
  simp only [← lowerSemicontinuousWithinAt_iff_le_liminf, lowerSemicontinuousOn_iff]

alias ⟨LowerSemicontinuousOn.le_liminf, _⟩ := lowerSemicontinuousOn_iff_le_liminf

中文:
定理 lowerSemicontinuousOn_iff_le_liminf
  条件: {f : α -> γ}
  证明: by
  simp only [← lowerSemicontinuousWithinAt_iff_le_liminf, lowerSemicontinuousOn_iff]

alias ⟨LowerSemicontinuousOn.le_liminf, _⟩ := lowerSemicontinuousOn_iff_le_liminf

Depends on / 依赖: lowerSemicontinuousOn_iff, lowerSemicontinuousWithinAt_iff_le_liminf
-/
theorem lowerSemicontinuousOn_iff_le_liminf {f : α -> γ} :
    LowerSemicontinuousOn f s ↔ forall x in s, f x <= liminf f (𝓝[s] x) := by
  simp only [← lowerSemicontinuousWithinAt_iff_le_liminf, lowerSemicontinuousOn_iff]

alias ⟨LowerSemicontinuousOn.le_liminf, _⟩ := lowerSemicontinuousOn_iff_le_liminf

end

section

variable {γ : Type*} [LinearOrder γ]

/--
theorem `LowerSemicontinuousOn.isCompact_inter_preimage_Iic` / 定理 `LowerSemicontinuousOn.isCompact_inter_preimage_Iic`

English:
theorem LowerSemicontinuousOn.isCompact_inter_preimage_Iic
  statement: {f : α -> γ}
  proof: by
  rw [lowerSemicontinuousOn_iff_preimage_Iic] at hfs
  obtain ⟨v, hv, hv'⟩ := hfs c
  exact hv' ▸ ks.inter_right hv

中文:
定理 LowerSemicontinuousOn.isCompact_inter_preimage_Iic
  结论: {f : α -> γ}
  证明: by
  rw [lowerSemicontinuousOn_iff_preimage_Iic] at hfs
  obtain ⟨v, hv, hv'⟩ := hfs c
  exact hv' ▸ ks.inter_right hv

Depends on / 依赖: inter_right, ks.inter_right, lowerSemicontinuousOn_iff_preimage_Iic
-/
theorem LowerSemicontinuousOn.isCompact_inter_preimage_Iic {f : α -> γ}
    (hfs : LowerSemicontinuousOn f s) (ks : IsCompact s) (c : γ) :
    IsCompact (s inter f ⁻¹' Iic c) := by
  rw [lowerSemicontinuousOn_iff_preimage_Iic] at hfs
  obtain ⟨v, hv, hv'⟩ := hfs c
  exact hv' ▸ ks.inter_right hv

open scoped Set.Notation in
/--
theorem `LowerSemicontinuousOn.inter_biInter_preimage_Iic_eq_empty_iff_exists_finset` / 定理 `LowerSemicontinuousOn.inter_biInter_preimage_Iic_eq_empty_iff_exists_finset`

English:
theorem LowerSemicontinuousOn.inter_biInter_preimage_Iic_eq_empty_iff_exists_finset
  proof: by
  refine ⟨fun H => ?_, fun ⟨u, hu⟩ => ?_⟩
  · suffices forall i in I, IsClosed (s ↓inter (fun i => f i ⁻¹' Iic c) i) by
      simpa [Set.eq_empty_iff_forall_notMem] using
        ks.elim_finite_subfamily_isClosed_subtype _ this H
.isClosed_preimage c exact fun i hi => lowerSemicontinuous_restrict

中文:
定理 LowerSemicontinuousOn.inter_bi整数er_preimage_Iic_eq_empty_iff_存在_finset
  证明: by
  refine ⟨fun H => ?_, fun ⟨u, hu⟩ => ?_⟩
  · suffices forall i in I, IsClosed (s ↓inter (fun i => f i ⁻¹' Iic c) i) by
      simpa [Set.eq_empty_iff_forall_notMem] using
        ks.elim_finite_subfamily_isClosed_subtype _ this H
.isClosed_preimage c exact fun i hi => lowerSemicontinuous_restrict

Depends on / 依赖: IsClosed, Set.eq_empty_iff_forall_notMem, elim_finite_subfamily_isClosed_subtype, eq_empty_iff_forall_notMem, exists_prop, isClosed_preimage, ks.elim_finite_subfamily_isClosed_subtype, lowerSemicontinuous_restrict_iff, lowerSemicontinuous_restrict_iff.mpr, mem_Iic, mem_iInter, mem_inter_iff, mem_preimage, not_and, not_forall, not_le
-/
theorem LowerSemicontinuousOn.inter_biInter_preimage_Iic_eq_empty_iff_exists_finset
    {ι : Type*} {f : ι -> α -> γ}
    (ks : IsCompact s) {I : Set ι} {c : γ} (hfi : forall i in I, LowerSemicontinuousOn (f i) s) :
    s inter ⋂ i in I, (f i) ⁻¹' Iic c = ∅ ↔ exists u : Finset I, forall x in s, exists i in u, c < f i x := by
  refine ⟨fun H => ?_, fun ⟨u, hu⟩ => ?_⟩
  · suffices forall i in I, IsClosed (s ↓inter (fun i => f i ⁻¹' Iic c) i) by
      simpa [Set.eq_empty_iff_forall_notMem] using
        ks.elim_finite_subfamily_isClosed_subtype _ this H
.isClosed_preimage c exact fun i hi => lowerSemicontinuous_restrict_iff.mpr (hfi i hi)
  · rw [Set.eq_empty_iff_forall_notMem]
    simp only [mem_inter_iff, mem_iInter, mem_preimage, mem_Iic, not_and, not_forall,
      exists_prop, not_le]
    grind

variable [TopologicalSpace γ] [ClosedIciTopology γ]

/--
theorem `lowerSemicontinuousOn_iff_isClosed_epigraph` / 定理 `lowerSemicontinuousOn_iff_isClosed_epigraph`

English:
theorem lowerSemicontinuousOn_iff_isClosed_epigraph
  given: {f : α -> γ} {s : Set α} (hs : IsClosed s)
  proof: by
  simp_rw [lowerSemicontinuousOn_iff, lowerSemicontinuousWithinAt_iff,
    eventually_nhdsWithin_iff, ← isOpen_compl_iff, compl_ofPred, isOpen_iff_eventually, mem_ofPred,
    not_and, not_le]
  constructor
  · intro hf ⟨x, y⟩ h
    by_cases hx : x in s
    · have ⟨y', hy', z, hz, h₁⟩ := (h hx).ex

中文:
定理 lowerSemicontinuousOn_iff_isClosed_epigraph
  条件: {f : α -> γ} {s : 集合 α} (hs : 是闭集 s)
  证明: by
  simp_rw [lowerSemicontinuousOn_iff, lowerSemicontinuousWithinAt_iff,
    eventually_nhdsWithin_iff, ← isOpen_compl_iff, compl_ofPred, isOpen_iff_eventually, mem_ofPred,
    not_and, not_le]
  constructor
  · intro hf ⟨x, y⟩ h
    by_cases hx : x in s
    · have ⟨y', hy', z, hz, h₁⟩ := (h hx).ex

Depends on / 依赖: compl_ofPred, continuous_fst, continuous_fst.tendsto, eventually, eventually_lt_nhds, eventually_mem, eventually_nhdsWithin_iff, exists_disjoint_Iio_Ioi, filter_upwards, hs.isOpen_compl.eventually_mem, isOpen_compl, isOpen_compl_iff, isOpen_iff_eventually, lowerSemicontinuousOn_iff, lowerSemicontinuousWithinAt_iff, mem_ofPred, not_and, not_le, prodMk_nhds, simp_rw
-/
theorem lowerSemicontinuousOn_iff_isClosed_epigraph {f : α -> γ} {s : Set α} (hs : IsClosed s) :
    LowerSemicontinuousOn f s ↔ IsClosed {p : α × γ | p.1 in s ∧ f p.1 <= p.2} := by
  simp_rw [lowerSemicontinuousOn_iff, lowerSemicontinuousWithinAt_iff,
    eventually_nhdsWithin_iff, ← isOpen_compl_iff, compl_ofPred, isOpen_iff_eventually, mem_ofPred,
    not_and, not_le]
  constructor
  · intro hf ⟨x, y⟩ h
    by_cases hx : x in s
    · have ⟨y', hy', z, hz, h₁⟩ := (h hx).exists_disjoint_Iio_Ioi
      filter_upwards [(hf x hx z hz).prodMk_nhds (eventually_lt_nhds hy')]
with _ ⟨h₂, h₃⟩ h₄ using h₁ _ h₃ _ h₂ h₄
    · filter_upwards [(continuous_fst.tendsto _).eventually (hs.isOpen_compl.eventually_mem hx)]
        with _ h₁ h₂ using (h₁ h₂).elim
  · intro hf x _ y hy
    exact ((Continuous.prodMk_left y).tendsto x).eventually (hf (x, y) (fun _ => hy))

/--
theorem `lowerSemicontinuous_iff_isClosed_epigraph` / 定理 `lowerSemicontinuous_iff_isClosed_epigraph`

English:
theorem lowerSemicontinuous_iff_isClosed_epigraph
  given: {f : α -> γ}
  proof: by
  simp [← lowerSemicontinuousOn_univ_iff, lowerSemicontinuousOn_iff_isClosed_epigraph]

alias ⟨LowerSemicontinuous.isClosed_epigraph, _⟩ := lowerSemicontinuous_iff_isClosed_epigraph

中文:
定理 lowerSemicontinuous_iff_isClosed_epigraph
  条件: {f : α -> γ}
  证明: by
  simp [← lowerSemicontinuousOn_univ_iff, lowerSemicontinuousOn_iff_isClosed_epigraph]

alias ⟨LowerSemicontinuous.isClosed_epigraph, _⟩ := lowerSemicontinuous_iff_isClosed_epigraph

Depends on / 依赖: lowerSemicontinuousOn_iff_isClosed_epigraph, lowerSemicontinuousOn_univ_iff
-/
theorem lowerSemicontinuous_iff_isClosed_epigraph {f : α -> γ} :
    LowerSemicontinuous f ↔ IsClosed {p : α × γ | f p.1 <= p.2} := by
  simp [← lowerSemicontinuousOn_univ_iff, lowerSemicontinuousOn_iff_isClosed_epigraph]

alias ⟨LowerSemicontinuous.isClosed_epigraph, _⟩ := lowerSemicontinuous_iff_isClosed_epigraph

end

/-! ### Composition -/

section

variable [Preorder β]
variable {γ : Type*} [LinearOrder γ] [TopologicalSpace γ] [OrderTopology γ]
variable {δ : Type*} [LinearOrder δ] [TopologicalSpace δ] [OrderTopology δ]
variable {ι : Type*} [TopologicalSpace ι]

/--
theorem `ContinuousAt.comp_lowerSemicontinuousWithinAt` / 定理 `ContinuousAt.comp_lowerSemicontinuousWithinAt`

English:
theorem ContinuousAt.comp_lowerSemicontinuousWithinAt
  statement: {g : γ -> δ} {f : α -> γ}
  proof: by
  intro y hy
  by_cases! h : exists l, l < f x
  · obtain ⟨z, zlt, hz⟩ : exists z < f x, Ioc z (f x) subseteq g ⁻¹' Ioi y :=
      exists_Ioc_subset_of_mem_nhds (hg (Ioi_mem_nhds hy)) h
    filter_upwards [hf z zlt] with a ha
    calc
      y < g (min (f x) (f a)) := hz (by simp [zlt, ha])
      

中文:
定理 ContinuousAt.comp_lowerSemicontinuousWithinAt
  结论: {g : γ -> δ} {f : α -> γ}
  证明: by
  intro y hy
  by_cases! h : exists l, l < f x
  · obtain ⟨z, zlt, hz⟩ : exists z < f x, Ioc z (f x) subseteq g ⁻¹' Ioi y :=
      exists_Ioc_subset_of_mem_nhds (hg (Ioi_mem_nhds hy)) h
    filter_upwards [hf z zlt] with a ha
    calc
      y < g (min (f x) (f a)) := hz (by simp [zlt, ha])
      

Depends on / 依赖: Eventually, Filter, Filter.Eventually.of_forall, Ioi_mem_nhds, exists_Ioc_subset_of_mem_nhds, filter_upwards, hy.trans_le, min_le_right, of_forall, subseteq, trans_le
-/
theorem ContinuousAt.comp_lowerSemicontinuousWithinAt {g : γ -> δ} {f : α -> γ}
    (hg : ContinuousAt g (f x)) (hf : LowerSemicontinuousWithinAt f s x) (gmon : Monotone g) :
    LowerSemicontinuousWithinAt (g ∘ f) s x := by
  intro y hy
  by_cases! h : exists l, l < f x
  · obtain ⟨z, zlt, hz⟩ : exists z < f x, Ioc z (f x) subseteq g ⁻¹' Ioi y :=
      exists_Ioc_subset_of_mem_nhds (hg (Ioi_mem_nhds hy)) h
    filter_upwards [hf z zlt] with a ha
    calc
      y < g (min (f x) (f a)) := hz (by simp [zlt, ha])
      _ <= g (f a) := gmon (min_le_right _ _)
  · exact Filter.Eventually.of_forall fun a => hy.trans_le (gmon (h (f a)))

/--
theorem `ContinuousAt.comp_lowerSemicontinuousAt` / 定理 `ContinuousAt.comp_lowerSemicontinuousAt`

English:
theorem ContinuousAt.comp_lowerSemicontinuousAt
  statement: {g : γ -> δ} {f : α -> γ} (hg : ContinuousAt g (f x))
  proof: by
  simp only [← lowerSemicontinuousWithinAt_univ_iff] at hf ⊢
  exact hg.comp_lowerSemicontinuousWithinAt hf gmon

中文:
定理 ContinuousAt.comp_lowerSemicontinuousAt
  结论: {g : γ -> δ} {f : α -> γ} (hg : ContinuousAt g (f x))
  证明: by
  simp only [← lowerSemicontinuousWithinAt_univ_iff] at hf ⊢
  exact hg.comp_lowerSemicontinuousWithinAt hf gmon

Depends on / 依赖: comp_lowerSemicontinuousWithinAt, hg.comp_lowerSemicontinuousWithinAt, lowerSemicontinuousWithinAt_univ_iff
-/
theorem ContinuousAt.comp_lowerSemicontinuousAt {g : γ -> δ} {f : α -> γ} (hg : ContinuousAt g (f x))
    (hf : LowerSemicontinuousAt f x) (gmon : Monotone g) : LowerSemicontinuousAt (g ∘ f) x := by
  simp only [← lowerSemicontinuousWithinAt_univ_iff] at hf ⊢
  exact hg.comp_lowerSemicontinuousWithinAt hf gmon

/--
theorem `Continuous.comp_lowerSemicontinuousOn` / 定理 `Continuous.comp_lowerSemicontinuousOn`

English:
theorem Continuous.comp_lowerSemicontinuousOn
  statement: {g : γ -> δ} {f : α -> γ} (hg : Continuous g)
  proof: fun x hx => hg.continuousAt.comp_lowerSemicontinuousWithinAt (hf x hx) gmon

中文:
定理 连续.comp_lowerSemicontinuousOn
  结论: {g : γ -> δ} {f : α -> γ} (hg : 连续 g)
  证明: fun x hx => hg.continuousAt.comp_lowerSemicontinuousWithinAt (hf x hx) gmon

Depends on / 依赖: comp_lowerSemicontinuousWithinAt, continuousAt, hg.continuousAt.comp_lowerSemicontinuousWithinAt
-/
theorem Continuous.comp_lowerSemicontinuousOn {g : γ -> δ} {f : α -> γ} (hg : Continuous g)
    (hf : LowerSemicontinuousOn f s) (gmon : Monotone g) : LowerSemicontinuousOn (g ∘ f) s :=
  fun x hx => hg.continuousAt.comp_lowerSemicontinuousWithinAt (hf x hx) gmon

/--
theorem `Continuous.comp_lowerSemicontinuous` / 定理 `Continuous.comp_lowerSemicontinuous`

English:
theorem Continuous.comp_lowerSemicontinuous
  statement: {g : γ -> δ} {f : α -> γ} (hg : Continuous g)
  proof: fun x =>
  hg.continuousAt.comp_lowerSemicontinuousAt (hf x) gmon

中文:
定理 连续.comp_lowerSemicontinuous
  结论: {g : γ -> δ} {f : α -> γ} (hg : 连续 g)
  证明: fun x =>
  hg.continuousAt.comp_lowerSemicontinuousAt (hf x) gmon
-/
theorem Continuous.comp_lowerSemicontinuous {g : γ -> δ} {f : α -> γ} (hg : Continuous g)
    (hf : LowerSemicontinuous f) (gmon : Monotone g) : LowerSemicontinuous (g ∘ f) := fun x =>
  hg.continuousAt.comp_lowerSemicontinuousAt (hf x) gmon

/--
theorem `ContinuousAt.comp_lowerSemicontinuousWithinAt_antitone` / 定理 `ContinuousAt.comp_lowerSemicontinuousWithinAt_antitone`

English:
theorem ContinuousAt.comp_lowerSemicontinuousWithinAt_antitone
  statement: {g : γ -> δ} {f : α -> γ}
  proof: ContinuousAt.comp_lowerSemicontinuousWithinAt (δ := δᵒᵈ) hg hf gmon

中文:
定理 ContinuousAt.comp_lowerSemicontinuousWithinAt_antitone
  结论: {g : γ -> δ} {f : α -> γ}
  证明: ContinuousAt.comp_lowerSemicontinuousWithinAt (δ := δᵒᵈ) hg hf gmon

Depends on / 依赖: ContinuousAt, ContinuousAt.comp_lowerSemicontinuousWithinAt, comp_lowerSemicontinuousWithinAt
-/
theorem ContinuousAt.comp_lowerSemicontinuousWithinAt_antitone {g : γ -> δ} {f : α -> γ}
    (hg : ContinuousAt g (f x)) (hf : LowerSemicontinuousWithinAt f s x) (gmon : Antitone g) :
    UpperSemicontinuousWithinAt (g ∘ f) s x :=
  ContinuousAt.comp_lowerSemicontinuousWithinAt (δ := δᵒᵈ) hg hf gmon

/--
theorem `ContinuousAt.comp_lowerSemicontinuousAt_antitone` / 定理 `ContinuousAt.comp_lowerSemicontinuousAt_antitone`

English:
theorem ContinuousAt.comp_lowerSemicontinuousAt_antitone
  statement: {g : γ -> δ} {f : α -> γ}
  proof: ContinuousAt.comp_lowerSemicontinuousAt (δ := δᵒᵈ) hg hf gmon

中文:
定理 ContinuousAt.comp_lowerSemicontinuousAt_antitone
  结论: {g : γ -> δ} {f : α -> γ}
  证明: ContinuousAt.comp_lowerSemicontinuousAt (δ := δᵒᵈ) hg hf gmon

Depends on / 依赖: ContinuousAt, ContinuousAt.comp_lowerSemicontinuousAt, comp_lowerSemicontinuousAt
-/
theorem ContinuousAt.comp_lowerSemicontinuousAt_antitone {g : γ -> δ} {f : α -> γ}
    (hg : ContinuousAt g (f x)) (hf : LowerSemicontinuousAt f x) (gmon : Antitone g) :
    UpperSemicontinuousAt (g ∘ f) x :=
  ContinuousAt.comp_lowerSemicontinuousAt (δ := δᵒᵈ) hg hf gmon

/--
theorem `Continuous.comp_lowerSemicontinuousOn_antitone` / 定理 `Continuous.comp_lowerSemicontinuousOn_antitone`

English:
theorem Continuous.comp_lowerSemicontinuousOn_antitone
  statement: {g : γ -> δ} {f : α -> γ} (hg : Continuous g)
  proof: fun x hx => hg.continuousAt.comp_lowerSemicontinuousWithinAt_antitone (hf x hx) gmon

中文:
定理 连续.comp_lowerSemicontinuousOn_antitone
  结论: {g : γ -> δ} {f : α -> γ} (hg : 连续 g)
  证明: fun x hx => hg.continuousAt.comp_lowerSemicontinuousWithinAt_antitone (hf x hx) gmon

Depends on / 依赖: comp_lowerSemicontinuousWithinAt_antitone, continuousAt, hg.continuousAt.comp_lowerSemicontinuousWithinAt_antitone
-/
theorem Continuous.comp_lowerSemicontinuousOn_antitone {g : γ -> δ} {f : α -> γ} (hg : Continuous g)
    (hf : LowerSemicontinuousOn f s) (gmon : Antitone g) : UpperSemicontinuousOn (g ∘ f) s :=
  fun x hx => hg.continuousAt.comp_lowerSemicontinuousWithinAt_antitone (hf x hx) gmon

/--
theorem `Continuous.comp_lowerSemicontinuous_antitone` / 定理 `Continuous.comp_lowerSemicontinuous_antitone`

English:
theorem Continuous.comp_lowerSemicontinuous_antitone
  statement: {g : γ -> δ} {f : α -> γ} (hg : Continuous g)
  proof: fun x =>
  hg.continuousAt.comp_lowerSemicontinuousAt_antitone (hf x) gmon

中文:
定理 连续.comp_lowerSemicontinuous_antitone
  结论: {g : γ -> δ} {f : α -> γ} (hg : 连续 g)
  证明: fun x =>
  hg.continuousAt.comp_lowerSemicontinuousAt_antitone (hf x) gmon
-/
theorem Continuous.comp_lowerSemicontinuous_antitone {g : γ -> δ} {f : α -> γ} (hg : Continuous g)
    (hf : LowerSemicontinuous f) (gmon : Antitone g) : UpperSemicontinuous (g ∘ f) := fun x =>
  hg.continuousAt.comp_lowerSemicontinuousAt_antitone (hf x) gmon

end

/-! #### Addition -/


section

variable {ι : Type*} {γ : Type*} [AddCommMonoid γ] [LinearOrder γ] [IsOrderedAddMonoid γ]
  [TopologicalSpace γ] [OrderTopology γ]

/--
theorem `LowerSemicontinuousWithinAt.add'` / 定理 `LowerSemicontinuousWithinAt.add'`

English:
theorem LowerSemicontinuousWithinAt.add'
  statement: {f g : α -> γ} (hf : LowerSemicontinuousWithinAt f s x)
  proof: by
  intro y hy
  obtain ⟨u, v, u_open, xu, v_open, xv, h⟩ :
    exists u v : Set γ,
      IsOpen u ∧ f x in u ∧ IsOpen v ∧ g x in v ∧ u ×ˢ v subseteq { p : γ × γ | y < p.fst + p.snd } :=
    mem_nhds_prod_iff'.1 (hcont (isOpen_Ioi.mem_nhds hy))
  by_cases hx₁ : exists l, l < f x
  · obtain ⟨z₁, z₁l

中文:
定理 LowerSemicontinuousWithinAt.add'
  结论: {f g : α -> γ} (hf : LowerSemicontinuousWithinAt f s x)
  证明: by
  intro y hy
  obtain ⟨u, v, u_open, xu, v_open, xv, h⟩ :
    exists u v : Set γ,
      IsOpen u ∧ f x in u ∧ IsOpen v ∧ g x in v ∧ u ×ˢ v subseteq { p : γ × γ | y < p.fst + p.snd } :=
    mem_nhds_prod_iff'.1 (hcont (isOpen_Ioi.mem_nhds hy))
  by_cases hx₁ : exists l, l < f x
  · obtain ⟨z₁, z₁l

Depends on / 依赖: IsOpen, exists_Ioc_, exists_Ioc_subset_of_mem_nhds, isOpen_Ioi, isOpen_Ioi.mem_nhds, mem_nhds, mem_nhds_prod_iff, p.fst, p.snd, subseteq, u_open, u_open.mem_nhds, v_open
-/
theorem LowerSemicontinuousWithinAt.add' {f g : α -> γ} (hf : LowerSemicontinuousWithinAt f s x)
    (hg : LowerSemicontinuousWithinAt g s x)
    (hcont : ContinuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)) :
    LowerSemicontinuousWithinAt (fun z => f z + g z) s x := by
  intro y hy
  obtain ⟨u, v, u_open, xu, v_open, xv, h⟩ :
    exists u v : Set γ,
      IsOpen u ∧ f x in u ∧ IsOpen v ∧ g x in v ∧ u ×ˢ v subseteq { p : γ × γ | y < p.fst + p.snd } :=
    mem_nhds_prod_iff'.1 (hcont (isOpen_Ioi.mem_nhds hy))
  by_cases hx₁ : exists l, l < f x
  · obtain ⟨z₁, z₁lt, h₁⟩ : exists z₁ < f x, Ioc z₁ (f x) subseteq u :=
      exists_Ioc_subset_of_mem_nhds (u_open.mem_nhds xu) hx₁
    by_cases hx₂ : exists l, l < g x
    · obtain ⟨z₂, z₂lt, h₂⟩ : exists z₂ < g x, Ioc z₂ (g x) subseteq v :=
        exists_Ioc_subset_of_mem_nhds (v_open.mem_nhds xv) hx₂
      filter_upwards [hf z₁ z₁lt, hg z₂ z₂lt] with z h₁z h₂z
      have A1 : min (f z) (f x) in u := by
        by_cases! H : f z <= f x
        · simpa [H] using h₁ ⟨h₁z, H⟩
        · simpa [H.le]
      have A2 : min (g z) (g x) in v := by
        by_cases! H : g z <= g x
        · simpa [H] using h₂ ⟨h₂z, H⟩
        · simpa [H.le]
      have : (min (f z) (f x), min (g z) (g x)) in u ×ˢ v := ⟨A1, A2⟩
      calc
        y < min (f z) (f x) + min (g z) (g x) := h this
        _ <= f z + g z := add_le_add (min_le_left _ _) (min_le_left _ _)
    · simp only [not_exists, not_lt] at hx₂
      filter_upwards [hf z₁ z₁lt] with z h₁z
      have A1 : min (f z) (f x) in u := by
        by_cases! H : f z <= f x
        · simpa [H] using h₁ ⟨h₁z, H⟩
        · simpa [H.le]
      have : (min (f z) (f x), g x) in u ×ˢ v := ⟨A1, xv⟩
      calc
        y < min (f z) (f x) + g x := h this
        _ <= f z + g z := add_le_add (min_le_left _ _) (hx₂ (g z))
  · simp only [not_exists, not_lt] at hx₁
    by_cases hx₂ : exists l, l < g x
    · obtain ⟨z₂, z₂lt, h₂⟩ : exists z₂ < g x, Ioc z₂ (g x) subseteq v :=
        exists_Ioc_subset_of_mem_nhds (v_open.mem_nhds xv) hx₂
      filter_upwards [hg z₂ z₂lt] with z h₂z
      have A2 : min (g z) (g x) in v := by
        by_cases! H : g z <= g x
        · simpa [H] using h₂ ⟨h₂z, H⟩
        · simpa [H.le] using h₂ ⟨z₂lt, le_rfl⟩
      have : (f x, min (g z) (g x)) in u ×ˢ v := ⟨xu, A2⟩
      calc
        y < f x + min (g z) (g x) := h this
        _ <= f z + g z := add_le_add (hx₁ (f z)) (min_le_left _ _)
    · simp only [not_exists, not_lt] at hx₁ hx₂
      apply Filter.Eventually.of_forall
      intro z
      have : (f x, g x) in u ×ˢ v := ⟨xu, xv⟩
      calc
        y < f x + g x := h this
        _ <= f z + g z := add_le_add (hx₁ (f z)) (hx₂ (g z))

/--
theorem `LowerSemicontinuousAt.add'` / 定理 `LowerSemicontinuousAt.add'`

English:
theorem LowerSemicontinuousAt.add'
  statement: {f g : α -> γ} (hf : LowerSemicontinuousAt f x)
  proof: by
  simp_rw [← lowerSemicontinuousWithinAt_univ_iff] at *
  exact hf.add' hg hcont

中文:
定理 LowerSemicontinuousAt.add'
  结论: {f g : α -> γ} (hf : LowerSemicontinuousAt f x)
  证明: by
  simp_rw [← lowerSemicontinuousWithinAt_univ_iff] at *
  exact hf.add' hg hcont

Depends on / 依赖: hf.add, lowerSemicontinuousWithinAt_univ_iff, simp_rw
-/
theorem LowerSemicontinuousAt.add' {f g : α -> γ} (hf : LowerSemicontinuousAt f x)
    (hg : LowerSemicontinuousAt g x)
    (hcont : ContinuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)) :
    LowerSemicontinuousAt (fun z => f z + g z) x := by
  simp_rw [← lowerSemicontinuousWithinAt_univ_iff] at *
  exact hf.add' hg hcont

/--
theorem `LowerSemicontinuousOn.add'` / 定理 `LowerSemicontinuousOn.add'`

English:
theorem LowerSemicontinuousOn.add'
  statement: {f g : α -> γ} (hf : LowerSemicontinuousOn f s)
  proof: fun x hx =>
  LowerSemicontinuousWithinAt.add' (hf x hx) (hg x hx) (hcont x hx)

中文:
定理 LowerSemicontinuousOn.add'
  结论: {f g : α -> γ} (hf : LowerSemicontinuousOn f s)
  证明: fun x hx =>
  LowerSemicontinuousWithinAt.add' (hf x hx) (hg x hx) (hcont x hx)
-/
theorem LowerSemicontinuousOn.add' {f g : α -> γ} (hf : LowerSemicontinuousOn f s)
    (hg : LowerSemicontinuousOn g s)
    (hcont : forall x in s, ContinuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)) :
    LowerSemicontinuousOn (fun z => f z + g z) s := fun x hx =>
  LowerSemicontinuousWithinAt.add' (hf x hx) (hg x hx) (hcont x hx)

/--
theorem `LowerSemicontinuous.add'` / 定理 `LowerSemicontinuous.add'`

English:
theorem LowerSemicontinuous.add'
  statement: {f g : α -> γ} (hf : LowerSemicontinuous f)
  proof: fun x => LowerSemicontinuousAt.add' (hf x) (hg x) (hcont x)

中文:
定理 LowerSemicontinuous.add'
  结论: {f g : α -> γ} (hf : LowerSemicontinuous f)
  证明: fun x => LowerSemicontinuousAt.add' (hf x) (hg x) (hcont x)

Depends on / 依赖: LowerSemicontinuousAt, LowerSemicontinuousAt.add
-/
theorem LowerSemicontinuous.add' {f g : α -> γ} (hf : LowerSemicontinuous f)
    (hg : LowerSemicontinuous g)
    (hcont : forall x, ContinuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)) :
    LowerSemicontinuous fun z => f z + g z :=
  fun x => LowerSemicontinuousAt.add' (hf x) (hg x) (hcont x)

variable [ContinuousAdd γ]

/--
theorem `LowerSemicontinuousWithinAt.add` / 定理 `LowerSemicontinuousWithinAt.add`

English:
theorem LowerSemicontinuousWithinAt.add
  statement: {f g : α -> γ} (hf : LowerSemicontinuousWithinAt f s x)
  proof: hf.add' hg continuous_add.continuousAt

中文:
定理 LowerSemicontinuousWithinAt.add
  结论: {f g : α -> γ} (hf : LowerSemicontinuousWithinAt f s x)
  证明: hf.add' hg continuous_add.continuousAt

Depends on / 依赖: continuousAt, continuous_add, continuous_add.continuousAt, hf.add
-/
theorem LowerSemicontinuousWithinAt.add {f g : α -> γ} (hf : LowerSemicontinuousWithinAt f s x)
    (hg : LowerSemicontinuousWithinAt g s x) :
    LowerSemicontinuousWithinAt (fun z => f z + g z) s x :=
  hf.add' hg continuous_add.continuousAt

/--
theorem `LowerSemicontinuousAt.add` / 定理 `LowerSemicontinuousAt.add`

English:
theorem LowerSemicontinuousAt.add
  statement: {f g : α -> γ} (hf : LowerSemicontinuousAt f x)
  proof: hf.add' hg continuous_add.continuousAt

中文:
定理 LowerSemicontinuousAt.add
  结论: {f g : α -> γ} (hf : LowerSemicontinuousAt f x)
  证明: hf.add' hg continuous_add.continuousAt

Depends on / 依赖: continuousAt, continuous_add, continuous_add.continuousAt, hf.add
-/
theorem LowerSemicontinuousAt.add {f g : α -> γ} (hf : LowerSemicontinuousAt f x)
    (hg : LowerSemicontinuousAt g x) : LowerSemicontinuousAt (fun z => f z + g z) x :=
  hf.add' hg continuous_add.continuousAt

/--
theorem `LowerSemicontinuousOn.add` / 定理 `LowerSemicontinuousOn.add`

English:
theorem LowerSemicontinuousOn.add
  statement: {f g : α -> γ} (hf : LowerSemicontinuousOn f s)
  proof: hf.add' hg fun _x _hx => continuous_add.continuousAt

中文:
定理 LowerSemicontinuousOn.add
  结论: {f g : α -> γ} (hf : LowerSemicontinuousOn f s)
  证明: hf.add' hg fun _x _hx => continuous_add.continuousAt

Depends on / 依赖: continuousAt, continuous_add, continuous_add.continuousAt, hf.add
-/
theorem LowerSemicontinuousOn.add {f g : α -> γ} (hf : LowerSemicontinuousOn f s)
    (hg : LowerSemicontinuousOn g s) : LowerSemicontinuousOn (fun z => f z + g z) s :=
  hf.add' hg fun _x _hx => continuous_add.continuousAt

/--
theorem `LowerSemicontinuous.add` / 定理 `LowerSemicontinuous.add`

English:
theorem LowerSemicontinuous.add
  statement: {f g : α -> γ} (hf : LowerSemicontinuous f)
  proof: hf.add' hg fun _x => continuous_add.continuousAt

中文:
定理 LowerSemicontinuous.add
  结论: {f g : α -> γ} (hf : LowerSemicontinuous f)
  证明: hf.add' hg fun _x => continuous_add.continuousAt

Depends on / 依赖: continuousAt, continuous_add, continuous_add.continuousAt, hf.add
-/
theorem LowerSemicontinuous.add {f g : α -> γ} (hf : LowerSemicontinuous f)
    (hg : LowerSemicontinuous g) : LowerSemicontinuous fun z => f z + g z :=
  hf.add' hg fun _x => continuous_add.continuousAt

/--
theorem `lowerSemicontinuousWithinAt_sum` / 定理 `lowerSemicontinuousWithinAt_sum`

English:
theorem lowerSemicontinuousWithinAt_sum
  statement: {f : ι -> α -> γ} {a : Finset ι}
  proof: by
  classical
    induction a using Finset.induction_on with
    | empty => exact lowerSemicontinuousWithinAt_const
    | insert _ _ ia IH =>
      simp only [ia, Finset.sum_insert, not_false_iff]
      exact
        LowerSemicontinuousWithinAt.add (ha _ (Finset.mem_insert_self ..))
          (IH f

中文:
定理 lowerSemicontinuousWithinAt_sum
  结论: {f : ι -> α -> γ} {a : 有限集 ι}
  证明: by
  classical
    induction a using Finset.induction_on with
    | empty => exact lowerSemicontinuousWithinAt_const
    | insert _ _ ia IH =>
      simp only [ia, Finset.sum_insert, not_false_iff]
      exact
        LowerSemicontinuousWithinAt.add (ha _ (Finset.mem_insert_self ..))
          (IH f

Depends on / 依赖: Finset, Finset.induction_on, Finset.mem_insert_of_mem, Finset.mem_insert_self, Finset.sum_insert, LowerSemicontinuousWithinAt, LowerSemicontinuousWithinAt.add, classical, induction_on, insert, lowerSemicontinuousWithinAt_const, mem_insert_of_mem, mem_insert_self, not_false_iff, sum_insert
-/
theorem lowerSemicontinuousWithinAt_sum {f : ι -> α -> γ} {a : Finset ι}
    (ha : forall i in a, LowerSemicontinuousWithinAt (f i) s x) :
    LowerSemicontinuousWithinAt (fun z => ∑ i in a, f i z) s x := by
  classical
    induction a using Finset.induction_on with
    | empty => exact lowerSemicontinuousWithinAt_const
    | insert _ _ ia IH =>
      simp only [ia, Finset.sum_insert, not_false_iff]
      exact
        LowerSemicontinuousWithinAt.add (ha _ (Finset.mem_insert_self ..))
          (IH fun j ja => ha j (Finset.mem_insert_of_mem ja))

/--
theorem `lowerSemicontinuousAt_sum` / 定理 `lowerSemicontinuousAt_sum`

English:
theorem lowerSemicontinuousAt_sum
  statement: {f : ι -> α -> γ} {a : Finset ι}
  proof: by
  simp_rw [← lowerSemicontinuousWithinAt_univ_iff] at *
  exact lowerSemicontinuousWithinAt_sum ha

中文:
定理 lowerSemicontinuousAt_sum
  结论: {f : ι -> α -> γ} {a : 有限集 ι}
  证明: by
  simp_rw [← lowerSemicontinuousWithinAt_univ_iff] at *
  exact lowerSemicontinuousWithinAt_sum ha

Depends on / 依赖: lowerSemicontinuousWithinAt_sum, lowerSemicontinuousWithinAt_univ_iff, simp_rw
-/
theorem lowerSemicontinuousAt_sum {f : ι -> α -> γ} {a : Finset ι}
    (ha : forall i in a, LowerSemicontinuousAt (f i) x) :
    LowerSemicontinuousAt (fun z => ∑ i in a, f i z) x := by
  simp_rw [← lowerSemicontinuousWithinAt_univ_iff] at *
  exact lowerSemicontinuousWithinAt_sum ha

/--
theorem `lowerSemicontinuousOn_sum` / 定理 `lowerSemicontinuousOn_sum`

English:
theorem lowerSemicontinuousOn_sum
  statement: {f : ι -> α -> γ} {a : Finset ι}
  proof: fun x hx =>
  lowerSemicontinuousWithinAt_sum fun i hi => ha i hi x hx

中文:
定理 lowerSemicontinuousOn_sum
  结论: {f : ι -> α -> γ} {a : 有限集 ι}
  证明: fun x hx =>
  lowerSemicontinuousWithinAt_sum fun i hi => ha i hi x hx
-/
theorem lowerSemicontinuousOn_sum {f : ι -> α -> γ} {a : Finset ι}
    (ha : forall i in a, LowerSemicontinuousOn (f i) s) :
    LowerSemicontinuousOn (fun z => ∑ i in a, f i z) s := fun x hx =>
  lowerSemicontinuousWithinAt_sum fun i hi => ha i hi x hx

/--
theorem `lowerSemicontinuous_sum` / 定理 `lowerSemicontinuous_sum`

English:
theorem lowerSemicontinuous_sum
  statement: {f : ι -> α -> γ} {a : Finset ι}
  proof: fun x => lowerSemicontinuousAt_sum fun i hi => ha i hi x

中文:
定理 lowerSemicontinuous_sum
  结论: {f : ι -> α -> γ} {a : 有限集 ι}
  证明: fun x => lowerSemicontinuousAt_sum fun i hi => ha i hi x

Depends on / 依赖: lowerSemicontinuousAt_sum
-/
theorem lowerSemicontinuous_sum {f : ι -> α -> γ} {a : Finset ι}
    (ha : forall i in a, LowerSemicontinuous (f i)) : LowerSemicontinuous fun z => ∑ i in a, f i z :=
  fun x => lowerSemicontinuousAt_sum fun i hi => ha i hi x

end

/-! #### Supremum -/

section

variable {α : Type*} {β : Type*} [TopologicalSpace α] [LinearOrder β]
  {f g : α -> β} {s : Set α} {a : α}

/--
theorem `LowerSemicontinuousWithinAt.sup` / 定理 `LowerSemicontinuousWithinAt.sup`

English:
theorem LowerSemicontinuousWithinAt.sup
  proof: by
  intro b hb
  simp only [lt_sup_iff] at hb ⊢
  rcases hb with hb | hb
  · filter_upwards [hf b hb] with x using Or.intro_left _
  · filter_upwards [hg b hb] with x using Or.intro_right _

中文:
定理 LowerSemicontinuousWithinAt.上确界
  证明: by
  intro b hb
  simp only [lt_sup_iff] at hb ⊢
  rcases hb with hb | hb
  · filter_upwards [hf b hb] with x using Or.intro_left _
  · filter_upwards [hg b hb] with x using Or.intro_right _

Depends on / 依赖: Or.intro_left, Or.intro_right, filter_upwards, intro_left, intro_right, lt_sup_iff
-/
theorem LowerSemicontinuousWithinAt.sup
    (hf : LowerSemicontinuousWithinAt f s a) (hg : LowerSemicontinuousWithinAt g s a) :
    LowerSemicontinuousWithinAt (fun x => f x ⊔ g x) s a := by
  intro b hb
  simp only [lt_sup_iff] at hb ⊢
  rcases hb with hb | hb
  · filter_upwards [hf b hb] with x using Or.intro_left _
  · filter_upwards [hg b hb] with x using Or.intro_right _

/--
theorem `LowerSemicontinuousAt.sup` / 定理 `LowerSemicontinuousAt.sup`

English:
theorem LowerSemicontinuousAt.sup
  proof: by
  rw [← lowerSemicontinuousWithinAt_univ_iff] at *
  exact hf.sup hg

中文:
定理 LowerSemicontinuousAt.上确界
  证明: by
  rw [← lowerSemicontinuousWithinAt_univ_iff] at *
  exact hf.sup hg

Depends on / 依赖: hf.sup, lowerSemicontinuousWithinAt_univ_iff
-/
theorem LowerSemicontinuousAt.sup
    (hf : LowerSemicontinuousAt f a) (hg : LowerSemicontinuousAt g a) :
    LowerSemicontinuousAt (fun x => f x ⊔ g x) a := by
  rw [← lowerSemicontinuousWithinAt_univ_iff] at *
  exact hf.sup hg

/--
theorem `LowerSemicontinuousOn.sup` / 定理 `LowerSemicontinuousOn.sup`

English:
theorem LowerSemicontinuousOn.sup
  proof: fun a ha =>
  LowerSemicontinuousWithinAt.sup (hf a ha) (hg a ha)

中文:
定理 LowerSemicontinuousOn.上确界
  证明: fun a ha =>
  LowerSemicontinuousWithinAt.sup (hf a ha) (hg a ha)
-/
theorem LowerSemicontinuousOn.sup
    (hf : LowerSemicontinuousOn f s) (hg : LowerSemicontinuousOn g s) :
    LowerSemicontinuousOn (fun x => f x ⊔ g x) s := fun a ha =>
  LowerSemicontinuousWithinAt.sup (hf a ha) (hg a ha)

/--
theorem `LowerSemicontinuous.sup` / 定理 `LowerSemicontinuous.sup`

English:
theorem LowerSemicontinuous.sup
  proof: fun a =>
  LowerSemicontinuousAt.sup (hf a) (hg a)

中文:
定理 LowerSemicontinuous.上确界
  证明: fun a =>
  LowerSemicontinuousAt.sup (hf a) (hg a)
-/
theorem LowerSemicontinuous.sup
    (hf : LowerSemicontinuous f) (hg : LowerSemicontinuous g) :
    LowerSemicontinuous fun x => f x ⊔ g x := fun a =>
  LowerSemicontinuousAt.sup (hf a) (hg a)

/--
theorem `LowerSemicontinuousWithinAt.inf` / 定理 `LowerSemicontinuousWithinAt.inf`

English:
theorem LowerSemicontinuousWithinAt.inf
  proof: by
  intro b hb
  simp only [lt_inf_iff] at hb ⊢
  exact Eventually.and (hf b hb.1) (hg b hb.2)

中文:
定理 LowerSemicontinuousWithinAt.下确界
  证明: by
  intro b hb
  simp only [lt_inf_iff] at hb ⊢
  exact Eventually.and (hf b hb.1) (hg b hb.2)

Depends on / 依赖: Eventually, Eventually.and, lt_inf_iff
-/
theorem LowerSemicontinuousWithinAt.inf
    (hf : LowerSemicontinuousWithinAt f s a) (hg : LowerSemicontinuousWithinAt g s a) :
    LowerSemicontinuousWithinAt (fun x => f x ⊓ g x) s a := by
  intro b hb
  simp only [lt_inf_iff] at hb ⊢
  exact Eventually.and (hf b hb.1) (hg b hb.2)

/--
theorem `LowerSemicontinuousAt.inf` / 定理 `LowerSemicontinuousAt.inf`

English:
theorem LowerSemicontinuousAt.inf
  proof: by
  rw [← lowerSemicontinuousWithinAt_univ_iff] at *
  exact hf.inf hg

中文:
定理 LowerSemicontinuousAt.下确界
  证明: by
  rw [← lowerSemicontinuousWithinAt_univ_iff] at *
  exact hf.inf hg

Depends on / 依赖: hf.inf, lowerSemicontinuousWithinAt_univ_iff
-/
theorem LowerSemicontinuousAt.inf
    (hf : LowerSemicontinuousAt f a) (hg : LowerSemicontinuousAt g a) :
    LowerSemicontinuousAt (fun x => f x ⊓ g x) a := by
  rw [← lowerSemicontinuousWithinAt_univ_iff] at *
  exact hf.inf hg

/--
theorem `LowerSemicontinuousOn.inf` / 定理 `LowerSemicontinuousOn.inf`

English:
theorem LowerSemicontinuousOn.inf
  proof: fun a ha =>
  LowerSemicontinuousWithinAt.inf (hf a ha) (hg a ha)

中文:
定理 LowerSemicontinuousOn.下确界
  证明: fun a ha =>
  LowerSemicontinuousWithinAt.inf (hf a ha) (hg a ha)
-/
theorem LowerSemicontinuousOn.inf
    (hf : LowerSemicontinuousOn f s) (hg : LowerSemicontinuousOn g s) :
    LowerSemicontinuousOn (fun x => f x ⊓ g x) s := fun a ha =>
  LowerSemicontinuousWithinAt.inf (hf a ha) (hg a ha)

/--
theorem `LowerSemicontinuous.inf` / 定理 `LowerSemicontinuous.inf`

English:
theorem LowerSemicontinuous.inf
  statement: (hf : LowerSemicontinuous f)
  proof: fun a =>
  LowerSemicontinuousAt.inf (hf a) (hg a)

中文:
定理 LowerSemicontinuous.下确界
  结论: (hf : LowerSemicontinuous f)
  证明: fun a =>
  LowerSemicontinuousAt.inf (hf a) (hg a)
-/
theorem LowerSemicontinuous.inf (hf : LowerSemicontinuous f)
    (hg : LowerSemicontinuous g) :
    LowerSemicontinuous fun x => f x ⊓ g x := fun a =>
  LowerSemicontinuousAt.inf (hf a) (hg a)

end

section

variable {ι : Sort*} {δ δ' : Type*} [CompleteLinearOrder δ] [ConditionallyCompleteLinearOrder δ']

/--
theorem `lowerSemicontinuousWithinAt_ciSup` / 定理 `lowerSemicontinuousWithinAt_ciSup`

English:
theorem lowerSemicontinuousWithinAt_ciSup
  statement: {f : ι -> α -> δ'}
  proof: by
  cases isEmpty_or_nonempty ι
  · simpa only [iSup_of_empty'] using lowerSemicontinuousWithinAt_const
  · intro y hy
    rcases exists_lt_of_lt_ciSup hy with ⟨i, hi⟩
    filter_upwards [h i y hi, bdd] with y hy hy' using hy.trans_le (le_ciSup hy' i)

中文:
定理 lowerSemicontinuousWithinAt_ciSup
  结论: {f : ι -> α -> δ'}
  证明: by
  cases isEmpty_or_nonempty ι
  · simpa only [iSup_of_empty'] using lowerSemicontinuousWithinAt_const
  · intro y hy
    rcases exists_lt_of_lt_ciSup hy with ⟨i, hi⟩
    filter_upwards [h i y hi, bdd] with y hy hy' using hy.trans_le (le_ciSup hy' i)

Depends on / 依赖: exists_lt_of_lt_ciSup, filter_upwards, hy.trans_le, iSup_of_empty, isEmpty_or_nonempty, le_ciSup, lowerSemicontinuousWithinAt_const, trans_le
-/
theorem lowerSemicontinuousWithinAt_ciSup {f : ι -> α -> δ'}
    (bdd : forallᶠ y in 𝓝[s] x, BddAbove (range fun i => f i y))
    (h : forall i, LowerSemicontinuousWithinAt (f i) s x) :
    LowerSemicontinuousWithinAt (fun x' => ⨆ i, f i x') s x := by
  cases isEmpty_or_nonempty ι
  · simpa only [iSup_of_empty'] using lowerSemicontinuousWithinAt_const
  · intro y hy
    rcases exists_lt_of_lt_ciSup hy with ⟨i, hi⟩
    filter_upwards [h i y hi, bdd] with y hy hy' using hy.trans_le (le_ciSup hy' i)

/--
theorem `lowerSemicontinuousWithinAt_iSup` / 定理 `lowerSemicontinuousWithinAt_iSup`

English:
theorem lowerSemicontinuousWithinAt_iSup
  statement: {f : ι -> α -> δ}
  proof: lowerSemicontinuousWithinAt_ciSup (by simp) h

中文:
定理 lowerSemicontinuousWithinAt_iSup
  结论: {f : ι -> α -> δ}
  证明: lowerSemicontinuousWithinAt_ciSup (by simp) h

Depends on / 依赖: lowerSemicontinuousWithinAt_ciSup
-/
theorem lowerSemicontinuousWithinAt_iSup {f : ι -> α -> δ}
    (h : forall i, LowerSemicontinuousWithinAt (f i) s x) :
    LowerSemicontinuousWithinAt (fun x' => ⨆ i, f i x') s x :=
  lowerSemicontinuousWithinAt_ciSup (by simp) h

/--
theorem `lowerSemicontinuousWithinAt_biSup` / 定理 `lowerSemicontinuousWithinAt_biSup`

English:
theorem lowerSemicontinuousWithinAt_biSup
  statement: {p : ι -> Prop} {f : forall i, p i -> α -> δ}
  proof: lowerSemicontinuousWithinAt_iSup fun i => lowerSemicontinuousWithinAt_iSup fun hi => h i hi

中文:
定理 lowerSemicontinuousWithinAt_biSup
  结论: {p : ι -> 命题} {f : 对任意 i, p i -> α -> δ}
  证明: lowerSemicontinuousWithinAt_iSup fun i => lowerSemicontinuousWithinAt_iSup fun hi => h i hi

Depends on / 依赖: lowerSemicontinuousWithinAt_iSup
-/
theorem lowerSemicontinuousWithinAt_biSup {p : ι -> Prop} {f : forall i, p i -> α -> δ}
    (h : forall i hi, LowerSemicontinuousWithinAt (f i hi) s x) :
    LowerSemicontinuousWithinAt (fun x' => ⨆ (i) (hi), f i hi x') s x :=
  lowerSemicontinuousWithinAt_iSup fun i => lowerSemicontinuousWithinAt_iSup fun hi => h i hi

/--
theorem `lowerSemicontinuousAt_ciSup` / 定理 `lowerSemicontinuousAt_ciSup`

English:
theorem lowerSemicontinuousAt_ciSup
  statement: {f : ι -> α -> δ'}
  proof: by
  simp_rw [← lowerSemicontinuousWithinAt_univ_iff] at *
  rw [← nhdsWithin_univ] at bdd
  exact lowerSemicontinuousWithinAt_ciSup bdd h

中文:
定理 lowerSemicontinuousAt_ciSup
  结论: {f : ι -> α -> δ'}
  证明: by
  simp_rw [← lowerSemicontinuousWithinAt_univ_iff] at *
  rw [← nhdsWithin_univ] at bdd
  exact lowerSemicontinuousWithinAt_ciSup bdd h

Depends on / 依赖: lowerSemicontinuousWithinAt_ciSup, lowerSemicontinuousWithinAt_univ_iff, nhdsWithin_univ, simp_rw
-/
theorem lowerSemicontinuousAt_ciSup {f : ι -> α -> δ'}
    (bdd : forallᶠ y in 𝓝 x, BddAbove (range fun i => f i y)) (h : forall i, LowerSemicontinuousAt (f i) x) :
    LowerSemicontinuousAt (fun x' => ⨆ i, f i x') x := by
  simp_rw [← lowerSemicontinuousWithinAt_univ_iff] at *
  rw [← nhdsWithin_univ] at bdd
  exact lowerSemicontinuousWithinAt_ciSup bdd h

/--
theorem `lowerSemicontinuousAt_iSup` / 定理 `lowerSemicontinuousAt_iSup`

English:
theorem lowerSemicontinuousAt_iSup
  given: {f : ι -> α -> δ} (h : forall i, LowerSemicontinuousAt (f i) x)
  proof: lowerSemicontinuousAt_ciSup (by simp) h

中文:
定理 lowerSemicontinuousAt_iSup
  条件: {f : ι -> α -> δ} (h : 对任意 i, LowerSemicontinuousAt (f i) x)
  证明: lowerSemicontinuousAt_ciSup (by simp) h

Depends on / 依赖: lowerSemicontinuousAt_ciSup
-/
theorem lowerSemicontinuousAt_iSup {f : ι -> α -> δ} (h : forall i, LowerSemicontinuousAt (f i) x) :
    LowerSemicontinuousAt (fun x' => ⨆ i, f i x') x :=
  lowerSemicontinuousAt_ciSup (by simp) h

/--
theorem `lowerSemicontinuousAt_biSup` / 定理 `lowerSemicontinuousAt_biSup`

English:
theorem lowerSemicontinuousAt_biSup
  statement: {p : ι -> Prop} {f : forall i, p i -> α -> δ}
  proof: lowerSemicontinuousAt_iSup fun i => lowerSemicontinuousAt_iSup fun hi => h i hi

中文:
定理 lowerSemicontinuousAt_biSup
  结论: {p : ι -> 命题} {f : 对任意 i, p i -> α -> δ}
  证明: lowerSemicontinuousAt_iSup fun i => lowerSemicontinuousAt_iSup fun hi => h i hi

Depends on / 依赖: lowerSemicontinuousAt_iSup
-/
theorem lowerSemicontinuousAt_biSup {p : ι -> Prop} {f : forall i, p i -> α -> δ}
    (h : forall i hi, LowerSemicontinuousAt (f i hi) x) :
    LowerSemicontinuousAt (fun x' => ⨆ (i) (hi), f i hi x') x :=
  lowerSemicontinuousAt_iSup fun i => lowerSemicontinuousAt_iSup fun hi => h i hi

/--
theorem `lowerSemicontinuousOn_ciSup` / 定理 `lowerSemicontinuousOn_ciSup`

English:
theorem lowerSemicontinuousOn_ciSup
  statement: {f : ι -> α -> δ'}
  proof: fun x hx =>
  lowerSemicontinuousWithinAt_ciSup (eventually_nhdsWithin_of_forall bdd) fun i => h i x hx

中文:
定理 lowerSemicontinuousOn_ciSup
  结论: {f : ι -> α -> δ'}
  证明: fun x hx =>
  lowerSemicontinuousWithinAt_ciSup (eventually_nhdsWithin_of_forall bdd) fun i => h i x hx
-/
theorem lowerSemicontinuousOn_ciSup {f : ι -> α -> δ'}
    (bdd : forall x in s, BddAbove (range fun i => f i x)) (h : forall i, LowerSemicontinuousOn (f i) s) :
    LowerSemicontinuousOn (fun x' => ⨆ i, f i x') s := fun x hx =>
  lowerSemicontinuousWithinAt_ciSup (eventually_nhdsWithin_of_forall bdd) fun i => h i x hx

/--
theorem `lowerSemicontinuousOn_iSup` / 定理 `lowerSemicontinuousOn_iSup`

English:
theorem lowerSemicontinuousOn_iSup
  given: {f : ι -> α -> δ} (h : forall i, LowerSemicontinuousOn (f i) s)
  proof: lowerSemicontinuousOn_ciSup (by simp) h

中文:
定理 lowerSemicontinuousOn_iSup
  条件: {f : ι -> α -> δ} (h : 对任意 i, LowerSemicontinuousOn (f i) s)
  证明: lowerSemicontinuousOn_ciSup (by simp) h

Depends on / 依赖: lowerSemicontinuousOn_ciSup
-/
theorem lowerSemicontinuousOn_iSup {f : ι -> α -> δ} (h : forall i, LowerSemicontinuousOn (f i) s) :
    LowerSemicontinuousOn (fun x' => ⨆ i, f i x') s :=
  lowerSemicontinuousOn_ciSup (by simp) h

/--
theorem `lowerSemicontinuousOn_biSup` / 定理 `lowerSemicontinuousOn_biSup`

English:
theorem lowerSemicontinuousOn_biSup
  statement: {p : ι -> Prop} {f : forall i, p i -> α -> δ}
  proof: lowerSemicontinuousOn_iSup fun i => lowerSemicontinuousOn_iSup fun hi => h i hi

中文:
定理 lowerSemicontinuousOn_biSup
  结论: {p : ι -> 命题} {f : 对任意 i, p i -> α -> δ}
  证明: lowerSemicontinuousOn_iSup fun i => lowerSemicontinuousOn_iSup fun hi => h i hi

Depends on / 依赖: lowerSemicontinuousOn_iSup
-/
theorem lowerSemicontinuousOn_biSup {p : ι -> Prop} {f : forall i, p i -> α -> δ}
    (h : forall i hi, LowerSemicontinuousOn (f i hi) s) :
    LowerSemicontinuousOn (fun x' => ⨆ (i) (hi), f i hi x') s :=
  lowerSemicontinuousOn_iSup fun i => lowerSemicontinuousOn_iSup fun hi => h i hi

/--
theorem `lowerSemicontinuous_ciSup` / 定理 `lowerSemicontinuous_ciSup`

English:
theorem lowerSemicontinuous_ciSup
  statement: {f : ι -> α -> δ'} (bdd : forall x, BddAbove (range fun i => f i x))
  proof: fun x =>
  lowerSemicontinuousAt_ciSup (Eventually.of_forall bdd) fun i => h i x

中文:
定理 lowerSemicontinuous_ciSup
  结论: {f : ι -> α -> δ'} (bdd : 对任意 x, BddAbove (range fun i => f i x))
  证明: fun x =>
  lowerSemicontinuousAt_ciSup (Eventually.of_forall bdd) fun i => h i x
-/
theorem lowerSemicontinuous_ciSup {f : ι -> α -> δ'} (bdd : forall x, BddAbove (range fun i => f i x))
    (h : forall i, LowerSemicontinuous (f i)) : LowerSemicontinuous fun x' => ⨆ i, f i x' := fun x =>
  lowerSemicontinuousAt_ciSup (Eventually.of_forall bdd) fun i => h i x

/--
theorem `lowerSemicontinuous_iSup` / 定理 `lowerSemicontinuous_iSup`

English:
theorem lowerSemicontinuous_iSup
  given: {f : ι -> α -> δ} (h : forall i, LowerSemicontinuous (f i))
  proof: lowerSemicontinuous_ciSup (by simp) h

中文:
定理 lowerSemicontinuous_iSup
  条件: {f : ι -> α -> δ} (h : 对任意 i, LowerSemicontinuous (f i))
  证明: lowerSemicontinuous_ciSup (by simp) h

Depends on / 依赖: lowerSemicontinuous_ciSup
-/
theorem lowerSemicontinuous_iSup {f : ι -> α -> δ} (h : forall i, LowerSemicontinuous (f i)) :
    LowerSemicontinuous fun x' => ⨆ i, f i x' :=
  lowerSemicontinuous_ciSup (by simp) h

/--
theorem `lowerSemicontinuous_biSup` / 定理 `lowerSemicontinuous_biSup`

English:
theorem lowerSemicontinuous_biSup
  statement: {p : ι -> Prop} {f : forall i, p i -> α -> δ}
  proof: lowerSemicontinuous_iSup fun i => lowerSemicontinuous_iSup fun hi => h i hi

中文:
定理 lowerSemicontinuous_biSup
  结论: {p : ι -> 命题} {f : 对任意 i, p i -> α -> δ}
  证明: lowerSemicontinuous_iSup fun i => lowerSemicontinuous_iSup fun hi => h i hi

Depends on / 依赖: lowerSemicontinuous_iSup
-/
theorem lowerSemicontinuous_biSup {p : ι -> Prop} {f : forall i, p i -> α -> δ}
    (h : forall i hi, LowerSemicontinuous (f i hi)) :
    LowerSemicontinuous fun x' => ⨆ (i) (hi), f i hi x' :=
  lowerSemicontinuous_iSup fun i => lowerSemicontinuous_iSup fun hi => h i hi

end

/-! #### Infinite sums -/


section

variable {ι : Type*}

/--
theorem `lowerSemicontinuousWithinAt_tsum` / 定理 `lowerSemicontinuousWithinAt_tsum`

English:
theorem lowerSemicontinuousWithinAt_tsum
  statement: {f : ι -> α -> Real>=0∞}
  proof: by
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  refine lowerSemicontinuousWithinAt_iSup fun b => ?_
  exact lowerSemicontinuousWithinAt_sum fun i _hi => h i

中文:
定理 lowerSemicontinuousWithinAt_tsum
  结论: {f : ι -> α -> 实数>=0∞}
  证明: by
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  refine lowerSemicontinuousWithinAt_iSup fun b => ?_
  exact lowerSemicontinuousWithinAt_sum fun i _hi => h i

Depends on / 依赖: ENNReal, ENNReal.tsum_eq_iSup_sum, lowerSemicontinuousWithinAt_iSup, lowerSemicontinuousWithinAt_sum, simp_rw, tsum_eq_iSup_sum
-/
theorem lowerSemicontinuousWithinAt_tsum {f : ι -> α -> Real>=0∞}
    (h : forall i, LowerSemicontinuousWithinAt (f i) s x) :
    LowerSemicontinuousWithinAt (fun x' => ∑' i, f i x') s x := by
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  refine lowerSemicontinuousWithinAt_iSup fun b => ?_
  exact lowerSemicontinuousWithinAt_sum fun i _hi => h i

/--
theorem `lowerSemicontinuousAt_tsum` / 定理 `lowerSemicontinuousAt_tsum`

English:
theorem lowerSemicontinuousAt_tsum
  given: {f : ι -> α -> Real>=0∞} (h : forall i, LowerSemicontinuousAt (f i) x)
  proof: by
  simp_rw [← lowerSemicontinuousWithinAt_univ_iff] at *
  exact lowerSemicontinuousWithinAt_tsum h

中文:
定理 lowerSemicontinuousAt_tsum
  条件: {f : ι -> α -> 实数>=0∞} (h : 对任意 i, LowerSemicontinuousAt (f i) x)
  证明: by
  simp_rw [← lowerSemicontinuousWithinAt_univ_iff] at *
  exact lowerSemicontinuousWithinAt_tsum h

Depends on / 依赖: lowerSemicontinuousWithinAt_tsum, lowerSemicontinuousWithinAt_univ_iff, simp_rw
-/
theorem lowerSemicontinuousAt_tsum {f : ι -> α -> Real>=0∞} (h : forall i, LowerSemicontinuousAt (f i) x) :
    LowerSemicontinuousAt (fun x' => ∑' i, f i x') x := by
  simp_rw [← lowerSemicontinuousWithinAt_univ_iff] at *
  exact lowerSemicontinuousWithinAt_tsum h

/--
theorem `lowerSemicontinuousOn_tsum` / 定理 `lowerSemicontinuousOn_tsum`

English:
theorem lowerSemicontinuousOn_tsum
  given: {f : ι -> α -> Real>=0∞} (h : forall i, LowerSemicontinuousOn (f i) s)
  proof: fun x hx =>
  lowerSemicontinuousWithinAt_tsum fun i => h i x hx

中文:
定理 lowerSemicontinuousOn_tsum
  条件: {f : ι -> α -> 实数>=0∞} (h : 对任意 i, LowerSemicontinuousOn (f i) s)
  证明: fun x hx =>
  lowerSemicontinuousWithinAt_tsum fun i => h i x hx
-/
theorem lowerSemicontinuousOn_tsum {f : ι -> α -> Real>=0∞} (h : forall i, LowerSemicontinuousOn (f i) s) :
    LowerSemicontinuousOn (fun x' => ∑' i, f i x') s := fun x hx =>
  lowerSemicontinuousWithinAt_tsum fun i => h i x hx

/--
theorem `lowerSemicontinuous_tsum` / 定理 `lowerSemicontinuous_tsum`

English:
theorem lowerSemicontinuous_tsum
  given: {f : ι -> α -> Real>=0∞} (h : forall i, LowerSemicontinuous (f i))
  proof: fun x => lowerSemicontinuousAt_tsum fun i => h i x

中文:
定理 lowerSemicontinuous_tsum
  条件: {f : ι -> α -> 实数>=0∞} (h : 对任意 i, LowerSemicontinuous (f i))
  证明: fun x => lowerSemicontinuousAt_tsum fun i => h i x

Depends on / 依赖: lowerSemicontinuousAt_tsum
-/
theorem lowerSemicontinuous_tsum {f : ι -> α -> Real>=0∞} (h : forall i, LowerSemicontinuous (f i)) :
    LowerSemicontinuous fun x' => ∑' i, f i x' := fun x => lowerSemicontinuousAt_tsum fun i => h i x

end

/-!
### Upper semicontinuous functions
-/

/-! ### upper bounds -/

section

variable {α : Type*} [TopologicalSpace α] {β : Type*} [LinearOrder β] {f : α -> β} {s : Set α}

/--
theorem `UpperSemicontinuousOn.exists_isMaxOn` / 定理 `UpperSemicontinuousOn.exists_isMaxOn`

English:
theorem UpperSemicontinuousOn.exists_isMaxOn
  statement: {s : Set α} (ne_s : s.Nonempty)
  proof: LowerSemicontinuousOn.exists_isMinOn (β := βᵒᵈ) ne_s hs hf

中文:
定理 UpperSemicontinuousOn.存在_isMaxOn
  结论: {s : 集合 α} (ne_s : s.非空)
  证明: LowerSemicontinuousOn.exists_isMinOn (β := βᵒᵈ) ne_s hs hf

Depends on / 依赖: LowerSemicontinuousOn, LowerSemicontinuousOn.exists_isMinOn, exists_isMinOn, ne_s
-/
theorem UpperSemicontinuousOn.exists_isMaxOn {s : Set α} (ne_s : s.Nonempty)
    (hs : IsCompact s) (hf : UpperSemicontinuousOn f s) :
    exists a in s, IsMaxOn f s a :=
  LowerSemicontinuousOn.exists_isMinOn (β := βᵒᵈ) ne_s hs hf

/--
theorem `UpperSemicontinuousOn.bddAbove_of_isCompact` / 定理 `UpperSemicontinuousOn.bddAbove_of_isCompact`

English:
theorem UpperSemicontinuousOn.bddAbove_of_isCompact
  statement: [Nonempty β] {s : Set α}
  proof: LowerSemicontinuousOn.bddBelow_of_isCompact (β := βᵒᵈ) hs hf

中文:
定理 UpperSemicontinuousOn.bddAbove_of_isCompact
  结论: [非空 β] {s : 集合 α}
  证明: LowerSemicontinuousOn.bddBelow_of_isCompact (β := βᵒᵈ) hs hf

Depends on / 依赖: LowerSemicontinuousOn, LowerSemicontinuousOn.bddBelow_of_isCompact, bddBelow_of_isCompact
-/
theorem UpperSemicontinuousOn.bddAbove_of_isCompact [Nonempty β] {s : Set α}
    (hs : IsCompact s) (hf : UpperSemicontinuousOn f s) : BddAbove (f '' s) :=
  LowerSemicontinuousOn.bddBelow_of_isCompact (β := βᵒᵈ) hs hf

end

/-! #### Indicators -/


section

variable [Zero β] [Preorder β]

/--
theorem `IsOpen.upperSemicontinuous_indicator` / 定理 `IsOpen.upperSemicontinuous_indicator`

English:
theorem IsOpen.upperSemicontinuous_indicator
  given: (hs : IsOpen s) (hy : y <= 0)
  proof: IsOpen.lowerSemicontinuous_indicator (β := βᵒᵈ) hs hy

中文:
定理 是开集.upperSemicontinuous_indicator
  条件: (hs : 是开集 s) (hy : y <= 0)
  证明: IsOpen.lowerSemicontinuous_indicator (β := βᵒᵈ) hs hy

Depends on / 依赖: IsOpen, IsOpen.lowerSemicontinuous_indicator, lowerSemicontinuous_indicator
-/
theorem IsOpen.upperSemicontinuous_indicator (hs : IsOpen s) (hy : y <= 0) :
    UpperSemicontinuous (indicator s fun _x => y) :=
  IsOpen.lowerSemicontinuous_indicator (β := βᵒᵈ) hs hy

/--
theorem `IsOpen.upperSemicontinuousOn_indicator` / 定理 `IsOpen.upperSemicontinuousOn_indicator`

English:
theorem IsOpen.upperSemicontinuousOn_indicator
  given: (hs : IsOpen s) (hy : y <= 0)
  proof: (hs.upperSemicontinuous_indicator hy).upperSemicontinuousOn t

中文:
定理 是开集.upperSemicontinuousOn_indicator
  条件: (hs : 是开集 s) (hy : y <= 0)
  证明: (hs.upperSemicontinuous_indicator hy).upperSemicontinuousOn t

Depends on / 依赖: hs.upperSemicontinuous_indicator, upperSemicontinuousOn, upperSemicontinuous_indicator
-/
theorem IsOpen.upperSemicontinuousOn_indicator (hs : IsOpen s) (hy : y <= 0) :
    UpperSemicontinuousOn (indicator s fun _x => y) t :=
  (hs.upperSemicontinuous_indicator hy).upperSemicontinuousOn t

/--
theorem `IsOpen.upperSemicontinuousAt_indicator` / 定理 `IsOpen.upperSemicontinuousAt_indicator`

English:
theorem IsOpen.upperSemicontinuousAt_indicator
  given: (hs : IsOpen s) (hy : y <= 0)
  proof: (hs.upperSemicontinuous_indicator hy).upperSemicontinuousAt x

中文:
定理 是开集.upperSemicontinuousAt_indicator
  条件: (hs : 是开集 s) (hy : y <= 0)
  证明: (hs.upperSemicontinuous_indicator hy).upperSemicontinuousAt x

Depends on / 依赖: hs.upperSemicontinuous_indicator, upperSemicontinuousAt, upperSemicontinuous_indicator
-/
theorem IsOpen.upperSemicontinuousAt_indicator (hs : IsOpen s) (hy : y <= 0) :
    UpperSemicontinuousAt (indicator s fun _x => y) x :=
  (hs.upperSemicontinuous_indicator hy).upperSemicontinuousAt x

/--
theorem `IsOpen.upperSemicontinuousWithinAt_indicator` / 定理 `IsOpen.upperSemicontinuousWithinAt_indicator`

English:
theorem IsOpen.upperSemicontinuousWithinAt_indicator
  given: (hs : IsOpen s) (hy : y <= 0)
  proof: (hs.upperSemicontinuous_indicator hy).upperSemicontinuousWithinAt t x

中文:
定理 是开集.upperSemicontinuousWithinAt_indicator
  条件: (hs : 是开集 s) (hy : y <= 0)
  证明: (hs.upperSemicontinuous_indicator hy).upperSemicontinuousWithinAt t x

Depends on / 依赖: hs.upperSemicontinuous_indicator, upperSemicontinuousWithinAt, upperSemicontinuous_indicator
-/
theorem IsOpen.upperSemicontinuousWithinAt_indicator (hs : IsOpen s) (hy : y <= 0) :
    UpperSemicontinuousWithinAt (indicator s fun _x => y) t x :=
  (hs.upperSemicontinuous_indicator hy).upperSemicontinuousWithinAt t x

/--
theorem `IsClosed.upperSemicontinuous_indicator` / 定理 `IsClosed.upperSemicontinuous_indicator`

English:
theorem IsClosed.upperSemicontinuous_indicator
  given: (hs : IsClosed s) (hy : 0 <= y)
  proof: IsClosed.lowerSemicontinuous_indicator (β := βᵒᵈ) hs hy

中文:
定理 是闭集.upperSemicontinuous_indicator
  条件: (hs : 是闭集 s) (hy : 0 <= y)
  证明: IsClosed.lowerSemicontinuous_indicator (β := βᵒᵈ) hs hy

Depends on / 依赖: IsClosed, IsClosed.lowerSemicontinuous_indicator, lowerSemicontinuous_indicator
-/
theorem IsClosed.upperSemicontinuous_indicator (hs : IsClosed s) (hy : 0 <= y) :
    UpperSemicontinuous (indicator s fun _x => y) :=
  IsClosed.lowerSemicontinuous_indicator (β := βᵒᵈ) hs hy

/--
theorem `IsClosed.upperSemicontinuousOn_indicator` / 定理 `IsClosed.upperSemicontinuousOn_indicator`

English:
theorem IsClosed.upperSemicontinuousOn_indicator
  given: (hs : IsClosed s) (hy : 0 <= y)
  proof: (hs.upperSemicontinuous_indicator hy).upperSemicontinuousOn t

中文:
定理 是闭集.upperSemicontinuousOn_indicator
  条件: (hs : 是闭集 s) (hy : 0 <= y)
  证明: (hs.upperSemicontinuous_indicator hy).upperSemicontinuousOn t

Depends on / 依赖: hs.upperSemicontinuous_indicator, upperSemicontinuousOn, upperSemicontinuous_indicator
-/
theorem IsClosed.upperSemicontinuousOn_indicator (hs : IsClosed s) (hy : 0 <= y) :
    UpperSemicontinuousOn (indicator s fun _x => y) t :=
  (hs.upperSemicontinuous_indicator hy).upperSemicontinuousOn t

/--
theorem `IsClosed.upperSemicontinuousAt_indicator` / 定理 `IsClosed.upperSemicontinuousAt_indicator`

English:
theorem IsClosed.upperSemicontinuousAt_indicator
  given: (hs : IsClosed s) (hy : 0 <= y)
  proof: (hs.upperSemicontinuous_indicator hy).upperSemicontinuousAt x

中文:
定理 是闭集.upperSemicontinuousAt_indicator
  条件: (hs : 是闭集 s) (hy : 0 <= y)
  证明: (hs.upperSemicontinuous_indicator hy).upperSemicontinuousAt x

Depends on / 依赖: hs.upperSemicontinuous_indicator, upperSemicontinuousAt, upperSemicontinuous_indicator
-/
theorem IsClosed.upperSemicontinuousAt_indicator (hs : IsClosed s) (hy : 0 <= y) :
    UpperSemicontinuousAt (indicator s fun _x => y) x :=
  (hs.upperSemicontinuous_indicator hy).upperSemicontinuousAt x

/--
theorem `IsClosed.upperSemicontinuousWithinAt_indicator` / 定理 `IsClosed.upperSemicontinuousWithinAt_indicator`

English:
theorem IsClosed.upperSemicontinuousWithinAt_indicator
  given: (hs : IsClosed s) (hy : 0 <= y)
  proof: (hs.upperSemicontinuous_indicator hy).upperSemicontinuousWithinAt t x

中文:
定理 是闭集.upperSemicontinuousWithinAt_indicator
  条件: (hs : 是闭集 s) (hy : 0 <= y)
  证明: (hs.upperSemicontinuous_indicator hy).upperSemicontinuousWithinAt t x

Depends on / 依赖: hs.upperSemicontinuous_indicator, upperSemicontinuousWithinAt, upperSemicontinuous_indicator
-/
theorem IsClosed.upperSemicontinuousWithinAt_indicator (hs : IsClosed s) (hy : 0 <= y) :
    UpperSemicontinuousWithinAt (indicator s fun _x => y) t x :=
  (hs.upperSemicontinuous_indicator hy).upperSemicontinuousWithinAt t x

end

/-! #### Relationship with continuity -/

section

variable [Preorder β]

/--
theorem `upperSemicontinuous_iff_isOpen_preimage` / 定理 `upperSemicontinuous_iff_isOpen_preimage`

English:
theorem upperSemicontinuous_iff_isOpen_preimage
  proof: ⟨fun H y => isOpen_iff_mem_nhds.2 fun x hx => H x y hx, fun H _x y y_lt =>
    IsOpen.mem_nhds (H y) y_lt⟩

中文:
定理 upperSemicontinuous_iff_isOpen_preimage
  证明: ⟨fun H y => isOpen_iff_mem_nhds.2 fun x hx => H x y hx, fun H _x y y_lt =>
    IsOpen.mem_nhds (H y) y_lt⟩

Depends on / 依赖: IsOpen, IsOpen.mem_nhds, isOpen_iff_mem_nhds, mem_nhds, y_lt
-/
theorem upperSemicontinuous_iff_isOpen_preimage :
    UpperSemicontinuous f ↔ forall y, IsOpen (f ⁻¹' Iio y) :=
  ⟨fun H y => isOpen_iff_mem_nhds.2 fun x hx => H x y hx, fun H _x y y_lt =>
    IsOpen.mem_nhds (H y) y_lt⟩

/--
theorem `UpperSemicontinuous.isOpen_preimage` / 定理 `UpperSemicontinuous.isOpen_preimage`

English:
theorem UpperSemicontinuous.isOpen_preimage
  given: (hf : UpperSemicontinuous f) (y : β)
  proof: upperSemicontinuous_iff_isOpen_preimage.1 hf y

中文:
定理 UpperSemicontinuous.isOpen_preimage
  条件: (hf : UpperSemicontinuous f) (y : β)
  证明: upperSemicontinuous_iff_isOpen_preimage.1 hf y

Depends on / 依赖: upperSemicontinuous_iff_isOpen_preimage
-/
theorem UpperSemicontinuous.isOpen_preimage (hf : UpperSemicontinuous f) (y : β) :
    IsOpen (f ⁻¹' Iio y) :=
  upperSemicontinuous_iff_isOpen_preimage.1 hf y

end
section

variable {γ : Type*} [LinearOrder γ]

/--
theorem `upperSemicontinuous_iff_isClosed_preimage` / 定理 `upperSemicontinuous_iff_isClosed_preimage`

English:
theorem upperSemicontinuous_iff_isClosed_preimage
  given: {f : α -> γ}
  proof: by
  rw [upperSemicontinuous_iff_isOpen_preimage]
  simp only [← isOpen_compl_iff, ← preimage_compl, compl_Ici]

中文:
定理 upperSemicontinuous_iff_isClosed_preimage
  条件: {f : α -> γ}
  证明: by
  rw [upperSemicontinuous_iff_isOpen_preimage]
  simp only [← isOpen_compl_iff, ← preimage_compl, compl_Ici]

Depends on / 依赖: compl_Ici, isOpen_compl_iff, preimage_compl, upperSemicontinuous_iff_isOpen_preimage
-/
theorem upperSemicontinuous_iff_isClosed_preimage {f : α -> γ} :
    UpperSemicontinuous f ↔ forall y, IsClosed (f ⁻¹' Ici y) := by
  rw [upperSemicontinuous_iff_isOpen_preimage]
  simp only [← isOpen_compl_iff, ← preimage_compl, compl_Ici]

/--
theorem `UpperSemicontinuous.isClosed_preimage` / 定理 `UpperSemicontinuous.isClosed_preimage`

English:
theorem UpperSemicontinuous.isClosed_preimage
  given: {f : α -> γ} (hf : UpperSemicontinuous f) (y : γ)
  proof: upperSemicontinuous_iff_isClosed_preimage.1 hf y

中文:
定理 UpperSemicontinuous.isClosed_preimage
  条件: {f : α -> γ} (hf : UpperSemicontinuous f) (y : γ)
  证明: upperSemicontinuous_iff_isClosed_preimage.1 hf y

Depends on / 依赖: upperSemicontinuous_iff_isClosed_preimage
-/
theorem UpperSemicontinuous.isClosed_preimage {f : α -> γ} (hf : UpperSemicontinuous f) (y : γ) :
    IsClosed (f ⁻¹' Ici y) :=
  upperSemicontinuous_iff_isClosed_preimage.1 hf y

variable [TopologicalSpace γ] [OrderTopology γ]

/--
theorem `ContinuousWithinAt.upperSemicontinuousWithinAt` / 定理 `ContinuousWithinAt.upperSemicontinuousWithinAt`

English:
theorem ContinuousWithinAt.upperSemicontinuousWithinAt
  given: {f : α -> γ} (h : ContinuousWithinAt f s x)
  proof: fun _y hy => h (Iio_mem_nhds hy)

中文:
定理 ContinuousWithinAt.upperSemicontinuousWithinAt
  条件: {f : α -> γ} (h : ContinuousWithinAt f s x)
  证明: fun _y hy => h (Iio_mem_nhds hy)

Depends on / 依赖: Iio_mem_nhds
-/
theorem ContinuousWithinAt.upperSemicontinuousWithinAt {f : α -> γ} (h : ContinuousWithinAt f s x) :
    UpperSemicontinuousWithinAt f s x := fun _y hy => h (Iio_mem_nhds hy)

/--
theorem `ContinuousAt.upperSemicontinuousAt` / 定理 `ContinuousAt.upperSemicontinuousAt`

English:
theorem ContinuousAt.upperSemicontinuousAt
  given: {f : α -> γ} (h : ContinuousAt f x)
  proof: fun _y hy => h (Iio_mem_nhds hy)

中文:
定理 ContinuousAt.upperSemicontinuousAt
  条件: {f : α -> γ} (h : ContinuousAt f x)
  证明: fun _y hy => h (Iio_mem_nhds hy)

Depends on / 依赖: Iio_mem_nhds
-/
theorem ContinuousAt.upperSemicontinuousAt {f : α -> γ} (h : ContinuousAt f x) :
    UpperSemicontinuousAt f x := fun _y hy => h (Iio_mem_nhds hy)

/--
theorem `ContinuousOn.upperSemicontinuousOn` / 定理 `ContinuousOn.upperSemicontinuousOn`

English:
theorem ContinuousOn.upperSemicontinuousOn
  given: {f : α -> γ} (h : ContinuousOn f s)
  proof: fun x hx => (h x hx).upperSemicontinuousWithinAt

中文:
定理 ContinuousOn.upperSemicontinuousOn
  条件: {f : α -> γ} (h : ContinuousOn f s)
  证明: fun x hx => (h x hx).upperSemicontinuousWithinAt

Depends on / 依赖: upperSemicontinuousWithinAt
-/
theorem ContinuousOn.upperSemicontinuousOn {f : α -> γ} (h : ContinuousOn f s) :
    UpperSemicontinuousOn f s := fun x hx => (h x hx).upperSemicontinuousWithinAt

/--
theorem `Continuous.upperSemicontinuous` / 定理 `Continuous.upperSemicontinuous`

English:
theorem Continuous.upperSemicontinuous
  given: {f : α -> γ} (h : Continuous f)
  statement: UpperSemicontinuous f
  proof: fun _x => h.continuousAt.upperSemicontinuousAt

中文:
定理 连续.upperSemicontinuous
  条件: {f : α -> γ} (h : 连续 f)
  结论: UpperSemicontinuous f
  证明: fun _x => h.continuousAt.upperSemicontinuousAt

Depends on / 依赖: continuousAt, h.continuousAt.upperSemicontinuousAt, upperSemicontinuousAt
-/
theorem Continuous.upperSemicontinuous {f : α -> γ} (h : Continuous f) : UpperSemicontinuous f :=
  fun _x => h.continuousAt.upperSemicontinuousAt

end

/-! #### Equivalent definitions -/

section

variable {γ : Type*} [CompleteLinearOrder γ]

/--
theorem `upperSemicontinuousWithinAt_iff_limsup_le` / 定理 `upperSemicontinuousWithinAt_iff_limsup_le`

English:
theorem upperSemicontinuousWithinAt_iff_limsup_le
  given: {f : α -> γ}
  proof: lowerSemicontinuousWithinAt_iff_le_liminf (γ := γᵒᵈ)

alias ⟨UpperSemicontinuousWithinAt.limsup_le, _⟩ := upperSemicontinuousWithinAt_iff_limsup_le

中文:
定理 upperSemicontinuousWithinAt_iff_limsup_le
  条件: {f : α -> γ}
  证明: lowerSemicontinuousWithinAt_iff_le_liminf (γ := γᵒᵈ)

alias ⟨UpperSemicontinuousWithinAt.limsup_le, _⟩ := upperSemicontinuousWithinAt_iff_limsup_le

Depends on / 依赖: lowerSemicontinuousWithinAt_iff_le_liminf
-/
theorem upperSemicontinuousWithinAt_iff_limsup_le {f : α -> γ} :
    UpperSemicontinuousWithinAt f s x ↔ limsup f (𝓝[s] x) <= f x :=
  lowerSemicontinuousWithinAt_iff_le_liminf (γ := γᵒᵈ)

alias ⟨UpperSemicontinuousWithinAt.limsup_le, _⟩ := upperSemicontinuousWithinAt_iff_limsup_le

/--
theorem `upperSemicontinuousAt_iff_limsup_le` / 定理 `upperSemicontinuousAt_iff_limsup_le`

English:
theorem upperSemicontinuousAt_iff_limsup_le
  given: {f : α -> γ}
  proof: lowerSemicontinuousAt_iff_le_liminf (γ := γᵒᵈ)

alias ⟨UpperSemicontinuousAt.limsup_le, _⟩ := upperSemicontinuousAt_iff_limsup_le

中文:
定理 upperSemicontinuousAt_iff_limsup_le
  条件: {f : α -> γ}
  证明: lowerSemicontinuousAt_iff_le_liminf (γ := γᵒᵈ)

alias ⟨UpperSemicontinuousAt.limsup_le, _⟩ := upperSemicontinuousAt_iff_limsup_le

Depends on / 依赖: lowerSemicontinuousAt_iff_le_liminf
-/
theorem upperSemicontinuousAt_iff_limsup_le {f : α -> γ} :
    UpperSemicontinuousAt f x ↔ limsup f (𝓝 x) <= f x :=
  lowerSemicontinuousAt_iff_le_liminf (γ := γᵒᵈ)

alias ⟨UpperSemicontinuousAt.limsup_le, _⟩ := upperSemicontinuousAt_iff_limsup_le

/--
theorem `upperSemicontinuous_iff_limsup_le` / 定理 `upperSemicontinuous_iff_limsup_le`

English:
theorem upperSemicontinuous_iff_limsup_le
  given: {f : α -> γ}
  proof: lowerSemicontinuous_iff_le_liminf (γ := γᵒᵈ)

alias ⟨UpperSemicontinuous.limsup_le, _⟩ := upperSemicontinuous_iff_limsup_le

中文:
定理 upperSemicontinuous_iff_limsup_le
  条件: {f : α -> γ}
  证明: lowerSemicontinuous_iff_le_liminf (γ := γᵒᵈ)

alias ⟨UpperSemicontinuous.limsup_le, _⟩ := upperSemicontinuous_iff_limsup_le

Depends on / 依赖: lowerSemicontinuous_iff_le_liminf
-/
theorem upperSemicontinuous_iff_limsup_le {f : α -> γ} :
    UpperSemicontinuous f ↔ forall x, limsup f (𝓝 x) <= f x :=
  lowerSemicontinuous_iff_le_liminf (γ := γᵒᵈ)

alias ⟨UpperSemicontinuous.limsup_le, _⟩ := upperSemicontinuous_iff_limsup_le

/--
theorem `upperSemicontinuousOn_iff_limsup_le` / 定理 `upperSemicontinuousOn_iff_limsup_le`

English:
theorem upperSemicontinuousOn_iff_limsup_le
  given: {f : α -> γ}
  proof: lowerSemicontinuousOn_iff_le_liminf (γ := γᵒᵈ)

alias ⟨UpperSemicontinuousOn.limsup_le, _⟩ := upperSemicontinuousOn_iff_limsup_le

中文:
定理 upperSemicontinuousOn_iff_limsup_le
  条件: {f : α -> γ}
  证明: lowerSemicontinuousOn_iff_le_liminf (γ := γᵒᵈ)

alias ⟨UpperSemicontinuousOn.limsup_le, _⟩ := upperSemicontinuousOn_iff_limsup_le

Depends on / 依赖: lowerSemicontinuousOn_iff_le_liminf
-/
theorem upperSemicontinuousOn_iff_limsup_le {f : α -> γ} :
    UpperSemicontinuousOn f s ↔ forall x in s, limsup f (𝓝[s] x) <= f x :=
  lowerSemicontinuousOn_iff_le_liminf (γ := γᵒᵈ)

alias ⟨UpperSemicontinuousOn.limsup_le, _⟩ := upperSemicontinuousOn_iff_limsup_le

end

section

variable {γ : Type*} [LinearOrder γ]

/--
theorem `UpperSemicontinuousOn.isCompact_inter_preimage_Ici` / 定理 `UpperSemicontinuousOn.isCompact_inter_preimage_Ici`

English:
theorem UpperSemicontinuousOn.isCompact_inter_preimage_Ici
  statement: {f : α -> γ}
  proof: LowerSemicontinuousOn.isCompact_inter_preimage_Iic (γ := γᵒᵈ) hfs ks c

中文:
定理 UpperSemicontinuousOn.isCompact_inter_preimage_Ici
  结论: {f : α -> γ}
  证明: LowerSemicontinuousOn.isCompact_inter_preimage_Iic (γ := γᵒᵈ) hfs ks c

Depends on / 依赖: LowerSemicontinuousOn, LowerSemicontinuousOn.isCompact_inter_preimage_Iic, isCompact_inter_preimage_Iic
-/
theorem UpperSemicontinuousOn.isCompact_inter_preimage_Ici {f : α -> γ}
    (hfs : UpperSemicontinuousOn f s) (ks : IsCompact s) (c : γ) :
    IsCompact (s inter f ⁻¹' Ici c) :=
  LowerSemicontinuousOn.isCompact_inter_preimage_Iic (γ := γᵒᵈ) hfs ks c

open scoped Set.Notation in
/--
theorem `UpperSemicontinuousOn.inter_biInter_preimage_Ici_eq_empty_iff_exists_finset` / 定理 `UpperSemicontinuousOn.inter_biInter_preimage_Ici_eq_empty_iff_exists_finset`

English:
theorem UpperSemicontinuousOn.inter_biInter_preimage_Ici_eq_empty_iff_exists_finset
  proof: LowerSemicontinuousOn.inter_biInter_preimage_Iic_eq_empty_iff_exists_finset ks hfi (γ := γᵒᵈ)

中文:
定理 UpperSemicontinuousOn.inter_bi整数er_preimage_Ici_eq_empty_iff_存在_finset
  证明: LowerSemicontinuousOn.inter_biInter_preimage_Iic_eq_empty_iff_exists_finset ks hfi (γ := γᵒᵈ)

Depends on / 依赖: LowerSemicontinuousOn, LowerSemicontinuousOn.inter_biInter_preimage_Iic_eq_empty_iff_exists_finset, inter_biInter_preimage_Iic_eq_empty_iff_exists_finset
-/
theorem UpperSemicontinuousOn.inter_biInter_preimage_Ici_eq_empty_iff_exists_finset
    {ι : Type*} {f : ι -> α -> γ}
    (ks : IsCompact s) {I : Set ι} {c : γ} (hfi : forall i in I, UpperSemicontinuousOn (f i) s) :
    s inter ⋂ i in I, (f i) ⁻¹' Ici c = ∅ ↔ exists u : Finset I, forall x in s, exists i in u, f i x < c :=
  LowerSemicontinuousOn.inter_biInter_preimage_Iic_eq_empty_iff_exists_finset ks hfi (γ := γᵒᵈ)

variable [TopologicalSpace γ] [ClosedIicTopology γ]

/--
theorem `upperSemicontinuousOn_iff_isClosed_hypograph` / 定理 `upperSemicontinuousOn_iff_isClosed_hypograph`

English:
theorem upperSemicontinuousOn_iff_isClosed_hypograph
  given: {f : α -> γ} (hs : IsClosed s)
  proof: lowerSemicontinuousOn_iff_isClosed_epigraph hs (γ := γᵒᵈ)

中文:
定理 upperSemicontinuousOn_iff_isClosed_hypograph
  条件: {f : α -> γ} (hs : 是闭集 s)
  证明: lowerSemicontinuousOn_iff_isClosed_epigraph hs (γ := γᵒᵈ)

Depends on / 依赖: lowerSemicontinuousOn_iff_isClosed_epigraph
-/
theorem upperSemicontinuousOn_iff_isClosed_hypograph {f : α -> γ} (hs : IsClosed s) :
    UpperSemicontinuousOn f s ↔ IsClosed {p : α × γ | p.1 in s ∧ p.2 <= f p.1} :=
  lowerSemicontinuousOn_iff_isClosed_epigraph hs (γ := γᵒᵈ)

/--
theorem `upperSemicontinuous_iff_IsClosed_hypograph` / 定理 `upperSemicontinuous_iff_IsClosed_hypograph`

English:
theorem upperSemicontinuous_iff_IsClosed_hypograph
  given: {f : α -> γ}
  proof: lowerSemicontinuous_iff_isClosed_epigraph (γ := γᵒᵈ)

alias ⟨UpperSemicontinuous.IsClosed_hypograph, _⟩ := upperSemicontinuous_iff_IsClosed_hypograph

中文:
定理 upperSemicontinuous_iff_IsClosed_hypograph
  条件: {f : α -> γ}
  证明: lowerSemicontinuous_iff_isClosed_epigraph (γ := γᵒᵈ)

alias ⟨UpperSemicontinuous.IsClosed_hypograph, _⟩ := upperSemicontinuous_iff_IsClosed_hypograph

Depends on / 依赖: lowerSemicontinuous_iff_isClosed_epigraph
-/
theorem upperSemicontinuous_iff_IsClosed_hypograph {f : α -> γ} :
    UpperSemicontinuous f ↔ IsClosed {p : α × γ | p.2 <= f p.1} :=
  lowerSemicontinuous_iff_isClosed_epigraph (γ := γᵒᵈ)

alias ⟨UpperSemicontinuous.IsClosed_hypograph, _⟩ := upperSemicontinuous_iff_IsClosed_hypograph

end

/-! ### Composition -/

section

variable {α : Type*} [TopologicalSpace α]
variable {β : Type*}
variable {γ : Type*} [TopologicalSpace γ]
variable {f : α -> β} {g : γ -> α} {s : Set α} {a : α} {c : γ} {t : Set γ}

/--
theorem `upperSemicontinuousOn_iff_preimage_Iio` / 定理 `upperSemicontinuousOn_iff_preimage_Iio`

English:
theorem upperSemicontinuousOn_iff_preimage_Iio
  given: [Preorder β]
  proof: lowerSemicontinuousOn_iff_preimage_Ioi (β := βᵒᵈ)

中文:
定理 upperSemicontinuousOn_iff_preimage_Iio
  条件: [预序 β]
  证明: lowerSemicontinuousOn_iff_preimage_Ioi (β := βᵒᵈ)

Depends on / 依赖: lowerSemicontinuousOn_iff_preimage_Ioi
-/
theorem upperSemicontinuousOn_iff_preimage_Iio [Preorder β] :
    UpperSemicontinuousOn f s ↔ forall b, exists u : Set α, IsOpen u ∧ s inter f ⁻¹' Set.Iio b = s inter u :=
  lowerSemicontinuousOn_iff_preimage_Ioi (β := βᵒᵈ)

/--
theorem `upperSemicontinuousOn_iff_preimage_Ici` / 定理 `upperSemicontinuousOn_iff_preimage_Ici`

English:
theorem upperSemicontinuousOn_iff_preimage_Ici
  given: [LinearOrder β]
  proof: lowerSemicontinuousOn_iff_preimage_Iic (γ := βᵒᵈ)

中文:
定理 upperSemicontinuousOn_iff_preimage_Ici
  条件: [线性序 β]
  证明: lowerSemicontinuousOn_iff_preimage_Iic (γ := βᵒᵈ)

Depends on / 依赖: lowerSemicontinuousOn_iff_preimage_Iic
-/
theorem upperSemicontinuousOn_iff_preimage_Ici [LinearOrder β] :
    UpperSemicontinuousOn f s ↔ forall b, exists v : Set α, IsClosed v ∧ s inter f ⁻¹' Set.Ici b = s inter v :=
  lowerSemicontinuousOn_iff_preimage_Iic (γ := βᵒᵈ)

variable [PartialOrder β] [CommGroup β] [IsOrderedMonoid β]

@[to_additive (attr := simp)]
/--
theorem `lowerSemicontinuousWithinAt_inv_iff` / 定理 `lowerSemicontinuousWithinAt_inv_iff`

English:
theorem lowerSemicontinuousWithinAt_inv_iff
  proof: by
  rw [lowerSemicontinuousWithinAt_iff]; rw [inv_surjective.forall]; rw [upperSemicontinuousWithinAt_iff]
  simp

@[to_additive]
alias ⟨_, UpperSemicontinuousWithinAt.inv⟩ := lowerSemicontinuousWithinAt_inv_iff

@[to_additive (attr := simp)]

中文:
定理 lowerSemicontinuousWithinAt_inv_iff
  证明: by
  rw [lowerSemicontinuousWithinAt_iff]; rw [inv_surjective.forall]; rw [upperSemicontinuousWithinAt_iff]
  simp

@[to_additive]
alias ⟨_, UpperSemicontinuousWithinAt.inv⟩ := lowerSemicontinuousWithinAt_inv_iff

@[to_additive (attr := simp)]

Depends on / 依赖: inv_surjective, inv_surjective.forall, lowerSemicontinuousWithinAt_iff, upperSemicontinuousWithinAt_iff
-/
theorem lowerSemicontinuousWithinAt_inv_iff :
    LowerSemicontinuousWithinAt f⁻¹ s a ↔ UpperSemicontinuousWithinAt f s a := by
  rw [lowerSemicontinuousWithinAt_iff]; rw [inv_surjective.forall]; rw [upperSemicontinuousWithinAt_iff]
  simp

@[to_additive]
alias ⟨_, UpperSemicontinuousWithinAt.inv⟩ := lowerSemicontinuousWithinAt_inv_iff

@[to_additive (attr := simp)]
/--
theorem `upperSemicontinuousWithinAt_inv_iff` / 定理 `upperSemicontinuousWithinAt_inv_iff`

English:
theorem upperSemicontinuousWithinAt_inv_iff
  proof: by
  simp [← lowerSemicontinuousWithinAt_inv_iff]

@[to_additive]
alias ⟨_, LowerSemicontinuousWithinAt.inv⟩ := upperSemicontinuousWithinAt_inv_iff

@[to_additive (attr := simp)]

中文:
定理 upperSemicontinuousWithinAt_inv_iff
  证明: by
  simp [← lowerSemicontinuousWithinAt_inv_iff]

@[to_additive]
alias ⟨_, LowerSemicontinuousWithinAt.inv⟩ := upperSemicontinuousWithinAt_inv_iff

@[to_additive (attr := simp)]

Depends on / 依赖: lowerSemicontinuousWithinAt_inv_iff
-/
theorem upperSemicontinuousWithinAt_inv_iff :
    UpperSemicontinuousWithinAt f⁻¹ s a ↔ LowerSemicontinuousWithinAt f s a := by
  simp [← lowerSemicontinuousWithinAt_inv_iff]

@[to_additive]
alias ⟨_, LowerSemicontinuousWithinAt.inv⟩ := upperSemicontinuousWithinAt_inv_iff

@[to_additive (attr := simp)]
/--
theorem `lowerSemicontinuouAt_inv_iff` / 定理 `lowerSemicontinuouAt_inv_iff`

English:
theorem lowerSemicontinuouAt_inv_iff
  proof: by
  simp [← lowerSemicontinuousWithinAt_univ_iff, ← upperSemicontinuousWithinAt_univ_iff]

@[to_additive]
alias ⟨_, UpperSemicontinuousAt.inv⟩ := lowerSemicontinuouAt_inv_iff

@[to_additive (attr := simp)]

中文:
定理 lowerSemicontinuouAt_inv_iff
  证明: by
  simp [← lowerSemicontinuousWithinAt_univ_iff, ← upperSemicontinuousWithinAt_univ_iff]

@[to_additive]
alias ⟨_, UpperSemicontinuousAt.inv⟩ := lowerSemicontinuouAt_inv_iff

@[to_additive (attr := simp)]

Depends on / 依赖: lowerSemicontinuousWithinAt_univ_iff, upperSemicontinuousWithinAt_univ_iff
-/
theorem lowerSemicontinuouAt_inv_iff :
    LowerSemicontinuousAt f⁻¹ a ↔ UpperSemicontinuousAt f a := by
  simp [← lowerSemicontinuousWithinAt_univ_iff, ← upperSemicontinuousWithinAt_univ_iff]

@[to_additive]
alias ⟨_, UpperSemicontinuousAt.inv⟩ := lowerSemicontinuouAt_inv_iff

@[to_additive (attr := simp)]
/--
theorem `upperSemicontinuousAt_inv_iff` / 定理 `upperSemicontinuousAt_inv_iff`

English:
theorem upperSemicontinuousAt_inv_iff
  proof: by
  simp [← lowerSemicontinuousWithinAt_univ_iff, ← upperSemicontinuousWithinAt_univ_iff]

@[to_additive]
alias ⟨_, LowerSemicontinuousAt.inv⟩ := upperSemicontinuousAt_inv_iff

@[to_additive (attr := simp)]

中文:
定理 upperSemicontinuousAt_inv_iff
  证明: by
  simp [← lowerSemicontinuousWithinAt_univ_iff, ← upperSemicontinuousWithinAt_univ_iff]

@[to_additive]
alias ⟨_, LowerSemicontinuousAt.inv⟩ := upperSemicontinuousAt_inv_iff

@[to_additive (attr := simp)]

Depends on / 依赖: lowerSemicontinuousWithinAt_univ_iff, upperSemicontinuousWithinAt_univ_iff
-/
theorem upperSemicontinuousAt_inv_iff :
    UpperSemicontinuousAt f⁻¹ a ↔ LowerSemicontinuousAt f a := by
  simp [← lowerSemicontinuousWithinAt_univ_iff, ← upperSemicontinuousWithinAt_univ_iff]

@[to_additive]
alias ⟨_, LowerSemicontinuousAt.inv⟩ := upperSemicontinuousAt_inv_iff

@[to_additive (attr := simp)]
/--
theorem `lowerSemicontinuousOn_inv_iff` / 定理 `lowerSemicontinuousOn_inv_iff`

English:
theorem lowerSemicontinuousOn_inv_iff
  proof: by
  simp [lowerSemicontinuousOn_iff, upperSemicontinuousOn_iff]

@[to_additive]
alias ⟨_, UpperSemicontinuousOn.inv⟩ := lowerSemicontinuousOn_inv_iff

@[to_additive (attr := simp)]

中文:
定理 lowerSemicontinuousOn_inv_iff
  证明: by
  simp [lowerSemicontinuousOn_iff, upperSemicontinuousOn_iff]

@[to_additive]
alias ⟨_, UpperSemicontinuousOn.inv⟩ := lowerSemicontinuousOn_inv_iff

@[to_additive (attr := simp)]

Depends on / 依赖: lowerSemicontinuousOn_iff, upperSemicontinuousOn_iff
-/
theorem lowerSemicontinuousOn_inv_iff :
    LowerSemicontinuousOn f⁻¹ s ↔ UpperSemicontinuousOn f s := by
  simp [lowerSemicontinuousOn_iff, upperSemicontinuousOn_iff]

@[to_additive]
alias ⟨_, UpperSemicontinuousOn.inv⟩ := lowerSemicontinuousOn_inv_iff

@[to_additive (attr := simp)]
/--
theorem `upperSemicontinuousOn_inv_iff` / 定理 `upperSemicontinuousOn_inv_iff`

English:
theorem upperSemicontinuousOn_inv_iff
  proof: by
  simp [← lowerSemicontinuousOn_inv_iff]

@[to_additive]
alias ⟨_, LowerSemicontinuousOn.inv⟩ := upperSemicontinuousOn_inv_iff

@[to_additive (attr := simp)]

中文:
定理 upperSemicontinuousOn_inv_iff
  证明: by
  simp [← lowerSemicontinuousOn_inv_iff]

@[to_additive]
alias ⟨_, LowerSemicontinuousOn.inv⟩ := upperSemicontinuousOn_inv_iff

@[to_additive (attr := simp)]

Depends on / 依赖: lowerSemicontinuousOn_inv_iff
-/
theorem upperSemicontinuousOn_inv_iff :
    UpperSemicontinuousOn f⁻¹ s ↔ LowerSemicontinuousOn f s := by
  simp [← lowerSemicontinuousOn_inv_iff]

@[to_additive]
alias ⟨_, LowerSemicontinuousOn.inv⟩ := upperSemicontinuousOn_inv_iff

@[to_additive (attr := simp)]
/--
theorem `lowerSemiContinuous_inv_iff` / 定理 `lowerSemiContinuous_inv_iff`

English:
theorem lowerSemiContinuous_inv_iff
  proof: by
  simp [← upperSemicontinuousOn_univ_iff, ← lowerSemicontinuousOn_univ_iff]

@[to_additive]
alias ⟨_, UpperSemicontinuous.inv⟩ := lowerSemiContinuous_inv_iff

@[to_additive (attr := simp)]

中文:
定理 lowerSemiContinuous_inv_iff
  证明: by
  simp [← upperSemicontinuousOn_univ_iff, ← lowerSemicontinuousOn_univ_iff]

@[to_additive]
alias ⟨_, UpperSemicontinuous.inv⟩ := lowerSemiContinuous_inv_iff

@[to_additive (attr := simp)]

Depends on / 依赖: lowerSemicontinuousOn_univ_iff, upperSemicontinuousOn_univ_iff
-/
theorem lowerSemiContinuous_inv_iff :
    LowerSemicontinuous f⁻¹ ↔ UpperSemicontinuous f := by
  simp [← upperSemicontinuousOn_univ_iff, ← lowerSemicontinuousOn_univ_iff]

@[to_additive]
alias ⟨_, UpperSemicontinuous.inv⟩ := lowerSemiContinuous_inv_iff

@[to_additive (attr := simp)]
/--
theorem `upperSemiContinuous_inv_iff` / 定理 `upperSemiContinuous_inv_iff`

English:
theorem upperSemiContinuous_inv_iff
  proof: by
  simp [← upperSemicontinuousOn_univ_iff, ← lowerSemicontinuousOn_univ_iff]

@[to_additive]
alias ⟨_, LowerSemicontinuous.inv⟩ := upperSemiContinuous_inv_iff

中文:
定理 upperSemiContinuous_inv_iff
  证明: by
  simp [← upperSemicontinuousOn_univ_iff, ← lowerSemicontinuousOn_univ_iff]

@[to_additive]
alias ⟨_, LowerSemicontinuous.inv⟩ := upperSemiContinuous_inv_iff

Depends on / 依赖: lowerSemicontinuousOn_univ_iff, upperSemicontinuousOn_univ_iff
-/
theorem upperSemiContinuous_inv_iff :
    UpperSemicontinuous f⁻¹ ↔ LowerSemicontinuous f := by
  simp [← upperSemicontinuousOn_univ_iff, ← lowerSemicontinuousOn_univ_iff]

@[to_additive]
alias ⟨_, LowerSemicontinuous.inv⟩ := upperSemiContinuous_inv_iff

end

section

variable {γ : Type*} [LinearOrder γ] [TopologicalSpace γ] [OrderTopology γ]
variable {δ : Type*} [LinearOrder δ] [TopologicalSpace δ] [OrderTopology δ]
variable {ι : Type*} [TopologicalSpace ι]

/--
theorem `ContinuousAt.comp_upperSemicontinuousWithinAt` / 定理 `ContinuousAt.comp_upperSemicontinuousWithinAt`

English:
theorem ContinuousAt.comp_upperSemicontinuousWithinAt
  statement: {g : γ -> δ} {f : α -> γ}
  proof: ContinuousAt.comp_lowerSemicontinuousWithinAt (γ := γᵒᵈ) (δ := δᵒᵈ) hg hf gmon.dual

中文:
定理 ContinuousAt.comp_upperSemicontinuousWithinAt
  结论: {g : γ -> δ} {f : α -> γ}
  证明: ContinuousAt.comp_lowerSemicontinuousWithinAt (γ := γᵒᵈ) (δ := δᵒᵈ) hg hf gmon.dual

Depends on / 依赖: ContinuousAt, ContinuousAt.comp_lowerSemicontinuousWithinAt, comp_lowerSemicontinuousWithinAt, gmon.dual
-/
theorem ContinuousAt.comp_upperSemicontinuousWithinAt {g : γ -> δ} {f : α -> γ}
    (hg : ContinuousAt g (f x)) (hf : UpperSemicontinuousWithinAt f s x) (gmon : Monotone g) :
    UpperSemicontinuousWithinAt (g ∘ f) s x :=
  ContinuousAt.comp_lowerSemicontinuousWithinAt (γ := γᵒᵈ) (δ := δᵒᵈ) hg hf gmon.dual

/--
theorem `ContinuousAt.comp_upperSemicontinuousAt` / 定理 `ContinuousAt.comp_upperSemicontinuousAt`

English:
theorem ContinuousAt.comp_upperSemicontinuousAt
  statement: {g : γ -> δ} {f : α -> γ} (hg : ContinuousAt g (f x))
  proof: ContinuousAt.comp_lowerSemicontinuousAt (γ := γᵒᵈ) (δ := δᵒᵈ) hg hf gmon.dual

中文:
定理 ContinuousAt.comp_upperSemicontinuousAt
  结论: {g : γ -> δ} {f : α -> γ} (hg : ContinuousAt g (f x))
  证明: ContinuousAt.comp_lowerSemicontinuousAt (γ := γᵒᵈ) (δ := δᵒᵈ) hg hf gmon.dual

Depends on / 依赖: ContinuousAt, ContinuousAt.comp_lowerSemicontinuousAt, comp_lowerSemicontinuousAt, gmon.dual
-/
theorem ContinuousAt.comp_upperSemicontinuousAt {g : γ -> δ} {f : α -> γ} (hg : ContinuousAt g (f x))
    (hf : UpperSemicontinuousAt f x) (gmon : Monotone g) : UpperSemicontinuousAt (g ∘ f) x :=
  ContinuousAt.comp_lowerSemicontinuousAt (γ := γᵒᵈ) (δ := δᵒᵈ) hg hf gmon.dual

/--
theorem `Continuous.comp_upperSemicontinuousOn` / 定理 `Continuous.comp_upperSemicontinuousOn`

English:
theorem Continuous.comp_upperSemicontinuousOn
  statement: {g : γ -> δ} {f : α -> γ} (hg : Continuous g)
  proof: fun x hx => hg.continuousAt.comp_upperSemicontinuousWithinAt (hf x hx) gmon

中文:
定理 连续.comp_upperSemicontinuousOn
  结论: {g : γ -> δ} {f : α -> γ} (hg : 连续 g)
  证明: fun x hx => hg.continuousAt.comp_upperSemicontinuousWithinAt (hf x hx) gmon

Depends on / 依赖: comp_upperSemicontinuousWithinAt, continuousAt, hg.continuousAt.comp_upperSemicontinuousWithinAt
-/
theorem Continuous.comp_upperSemicontinuousOn {g : γ -> δ} {f : α -> γ} (hg : Continuous g)
    (hf : UpperSemicontinuousOn f s) (gmon : Monotone g) : UpperSemicontinuousOn (g ∘ f) s :=
  fun x hx => hg.continuousAt.comp_upperSemicontinuousWithinAt (hf x hx) gmon

/--
theorem `Continuous.comp_upperSemicontinuous` / 定理 `Continuous.comp_upperSemicontinuous`

English:
theorem Continuous.comp_upperSemicontinuous
  statement: {g : γ -> δ} {f : α -> γ} (hg : Continuous g)
  proof: fun x =>
  hg.continuousAt.comp_upperSemicontinuousAt (hf x) gmon

中文:
定理 连续.comp_upperSemicontinuous
  结论: {g : γ -> δ} {f : α -> γ} (hg : 连续 g)
  证明: fun x =>
  hg.continuousAt.comp_upperSemicontinuousAt (hf x) gmon
-/
theorem Continuous.comp_upperSemicontinuous {g : γ -> δ} {f : α -> γ} (hg : Continuous g)
    (hf : UpperSemicontinuous f) (gmon : Monotone g) : UpperSemicontinuous (g ∘ f) := fun x =>
  hg.continuousAt.comp_upperSemicontinuousAt (hf x) gmon

/--
theorem `ContinuousAt.comp_upperSemicontinuousWithinAt_antitone` / 定理 `ContinuousAt.comp_upperSemicontinuousWithinAt_antitone`

English:
theorem ContinuousAt.comp_upperSemicontinuousWithinAt_antitone
  statement: {g : γ -> δ} {f : α -> γ}
  proof: ContinuousAt.comp_upperSemicontinuousWithinAt (δ := δᵒᵈ) hg hf gmon

中文:
定理 ContinuousAt.comp_upperSemicontinuousWithinAt_antitone
  结论: {g : γ -> δ} {f : α -> γ}
  证明: ContinuousAt.comp_upperSemicontinuousWithinAt (δ := δᵒᵈ) hg hf gmon

Depends on / 依赖: ContinuousAt, ContinuousAt.comp_upperSemicontinuousWithinAt, comp_upperSemicontinuousWithinAt
-/
theorem ContinuousAt.comp_upperSemicontinuousWithinAt_antitone {g : γ -> δ} {f : α -> γ}
    (hg : ContinuousAt g (f x)) (hf : UpperSemicontinuousWithinAt f s x) (gmon : Antitone g) :
    LowerSemicontinuousWithinAt (g ∘ f) s x :=
  ContinuousAt.comp_upperSemicontinuousWithinAt (δ := δᵒᵈ) hg hf gmon

/--
theorem `ContinuousAt.comp_upperSemicontinuousAt_antitone` / 定理 `ContinuousAt.comp_upperSemicontinuousAt_antitone`

English:
theorem ContinuousAt.comp_upperSemicontinuousAt_antitone
  statement: {g : γ -> δ} {f : α -> γ}
  proof: ContinuousAt.comp_upperSemicontinuousAt (δ := δᵒᵈ) hg hf gmon

中文:
定理 ContinuousAt.comp_upperSemicontinuousAt_antitone
  结论: {g : γ -> δ} {f : α -> γ}
  证明: ContinuousAt.comp_upperSemicontinuousAt (δ := δᵒᵈ) hg hf gmon

Depends on / 依赖: ContinuousAt, ContinuousAt.comp_upperSemicontinuousAt, comp_upperSemicontinuousAt
-/
theorem ContinuousAt.comp_upperSemicontinuousAt_antitone {g : γ -> δ} {f : α -> γ}
    (hg : ContinuousAt g (f x)) (hf : UpperSemicontinuousAt f x) (gmon : Antitone g) :
    LowerSemicontinuousAt (g ∘ f) x :=
  ContinuousAt.comp_upperSemicontinuousAt (δ := δᵒᵈ) hg hf gmon

/--
theorem `Continuous.comp_upperSemicontinuousOn_antitone` / 定理 `Continuous.comp_upperSemicontinuousOn_antitone`

English:
theorem Continuous.comp_upperSemicontinuousOn_antitone
  statement: {g : γ -> δ} {f : α -> γ} (hg : Continuous g)
  proof: fun x hx => hg.continuousAt.comp_upperSemicontinuousWithinAt_antitone (hf x hx) gmon

中文:
定理 连续.comp_upperSemicontinuousOn_antitone
  结论: {g : γ -> δ} {f : α -> γ} (hg : 连续 g)
  证明: fun x hx => hg.continuousAt.comp_upperSemicontinuousWithinAt_antitone (hf x hx) gmon

Depends on / 依赖: comp_upperSemicontinuousWithinAt_antitone, continuousAt, hg.continuousAt.comp_upperSemicontinuousWithinAt_antitone
-/
theorem Continuous.comp_upperSemicontinuousOn_antitone {g : γ -> δ} {f : α -> γ} (hg : Continuous g)
    (hf : UpperSemicontinuousOn f s) (gmon : Antitone g) : LowerSemicontinuousOn (g ∘ f) s :=
  fun x hx => hg.continuousAt.comp_upperSemicontinuousWithinAt_antitone (hf x hx) gmon

/--
theorem `Continuous.comp_upperSemicontinuous_antitone` / 定理 `Continuous.comp_upperSemicontinuous_antitone`

English:
theorem Continuous.comp_upperSemicontinuous_antitone
  statement: {g : γ -> δ} {f : α -> γ} (hg : Continuous g)
  proof: fun x =>
  hg.continuousAt.comp_upperSemicontinuousAt_antitone (hf x) gmon

中文:
定理 连续.comp_upperSemicontinuous_antitone
  结论: {g : γ -> δ} {f : α -> γ} (hg : 连续 g)
  证明: fun x =>
  hg.continuousAt.comp_upperSemicontinuousAt_antitone (hf x) gmon
-/
theorem Continuous.comp_upperSemicontinuous_antitone {g : γ -> δ} {f : α -> γ} (hg : Continuous g)
    (hf : UpperSemicontinuous f) (gmon : Antitone g) : LowerSemicontinuous (g ∘ f) := fun x =>
  hg.continuousAt.comp_upperSemicontinuousAt_antitone (hf x) gmon

variable [Preorder β]

end

/-! #### Addition -/


section

variable {ι : Type*} {γ : Type*} [AddCommMonoid γ] [LinearOrder γ] [IsOrderedAddMonoid γ]
  [TopologicalSpace γ] [OrderTopology γ]

/--
theorem `UpperSemicontinuousWithinAt.add'` / 定理 `UpperSemicontinuousWithinAt.add'`

English:
theorem UpperSemicontinuousWithinAt.add'
  statement: {f g : α -> γ} (hf : UpperSemicontinuousWithinAt f s x)
  proof: LowerSemicontinuousWithinAt.add' (γ := γᵒᵈ) hf hg hcont

中文:
定理 UpperSemicontinuousWithinAt.add'
  结论: {f g : α -> γ} (hf : UpperSemicontinuousWithinAt f s x)
  证明: LowerSemicontinuousWithinAt.add' (γ := γᵒᵈ) hf hg hcont

Depends on / 依赖: LowerSemicontinuousWithinAt, LowerSemicontinuousWithinAt.add
-/
theorem UpperSemicontinuousWithinAt.add' {f g : α -> γ} (hf : UpperSemicontinuousWithinAt f s x)
    (hg : UpperSemicontinuousWithinAt g s x)
    (hcont : ContinuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)) :
    UpperSemicontinuousWithinAt (fun z => f z + g z) s x :=
  LowerSemicontinuousWithinAt.add' (γ := γᵒᵈ) hf hg hcont

/--
theorem `UpperSemicontinuousAt.add'` / 定理 `UpperSemicontinuousAt.add'`

English:
theorem UpperSemicontinuousAt.add'
  statement: {f g : α -> γ} (hf : UpperSemicontinuousAt f x)
  proof: by
  simp_rw [← upperSemicontinuousWithinAt_univ_iff] at *
  exact hf.add' hg hcont

中文:
定理 UpperSemicontinuousAt.add'
  结论: {f g : α -> γ} (hf : UpperSemicontinuousAt f x)
  证明: by
  simp_rw [← upperSemicontinuousWithinAt_univ_iff] at *
  exact hf.add' hg hcont

Depends on / 依赖: hf.add, simp_rw, upperSemicontinuousWithinAt_univ_iff
-/
theorem UpperSemicontinuousAt.add' {f g : α -> γ} (hf : UpperSemicontinuousAt f x)
    (hg : UpperSemicontinuousAt g x)
    (hcont : ContinuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)) :
    UpperSemicontinuousAt (fun z => f z + g z) x := by
  simp_rw [← upperSemicontinuousWithinAt_univ_iff] at *
  exact hf.add' hg hcont

/--
theorem `UpperSemicontinuousOn.add'` / 定理 `UpperSemicontinuousOn.add'`

English:
theorem UpperSemicontinuousOn.add'
  statement: {f g : α -> γ} (hf : UpperSemicontinuousOn f s)
  proof: fun x hx =>
  UpperSemicontinuousWithinAt.add' (hf x hx) (hg x hx) (hcont x hx)

中文:
定理 UpperSemicontinuousOn.add'
  结论: {f g : α -> γ} (hf : UpperSemicontinuousOn f s)
  证明: fun x hx =>
  UpperSemicontinuousWithinAt.add' (hf x hx) (hg x hx) (hcont x hx)
-/
theorem UpperSemicontinuousOn.add' {f g : α -> γ} (hf : UpperSemicontinuousOn f s)
    (hg : UpperSemicontinuousOn g s)
    (hcont : forall x in s, ContinuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)) :
    UpperSemicontinuousOn (fun z => f z + g z) s := fun x hx =>
  UpperSemicontinuousWithinAt.add' (hf x hx) (hg x hx) (hcont x hx)

/--
theorem `UpperSemicontinuous.add'` / 定理 `UpperSemicontinuous.add'`

English:
theorem UpperSemicontinuous.add'
  statement: {f g : α -> γ} (hf : UpperSemicontinuous f)
  proof: fun x => UpperSemicontinuousAt.add' (hf x) (hg x) (hcont x)

中文:
定理 UpperSemicontinuous.add'
  结论: {f g : α -> γ} (hf : UpperSemicontinuous f)
  证明: fun x => UpperSemicontinuousAt.add' (hf x) (hg x) (hcont x)

Depends on / 依赖: UpperSemicontinuousAt, UpperSemicontinuousAt.add
-/
theorem UpperSemicontinuous.add' {f g : α -> γ} (hf : UpperSemicontinuous f)
    (hg : UpperSemicontinuous g)
    (hcont : forall x, ContinuousAt (fun p : γ × γ => p.1 + p.2) (f x, g x)) :
    UpperSemicontinuous fun z => f z + g z :=
  fun x => UpperSemicontinuousAt.add' (hf x) (hg x) (hcont x)

variable [ContinuousAdd γ]

/--
theorem `UpperSemicontinuousWithinAt.add` / 定理 `UpperSemicontinuousWithinAt.add`

English:
theorem UpperSemicontinuousWithinAt.add
  statement: {f g : α -> γ} (hf : UpperSemicontinuousWithinAt f s x)
  proof: hf.add' hg continuous_add.continuousAt

中文:
定理 UpperSemicontinuousWithinAt.add
  结论: {f g : α -> γ} (hf : UpperSemicontinuousWithinAt f s x)
  证明: hf.add' hg continuous_add.continuousAt

Depends on / 依赖: continuousAt, continuous_add, continuous_add.continuousAt, hf.add
-/
theorem UpperSemicontinuousWithinAt.add {f g : α -> γ} (hf : UpperSemicontinuousWithinAt f s x)
    (hg : UpperSemicontinuousWithinAt g s x) :
    UpperSemicontinuousWithinAt (fun z => f z + g z) s x :=
  hf.add' hg continuous_add.continuousAt

/--
theorem `UpperSemicontinuousAt.add` / 定理 `UpperSemicontinuousAt.add`

English:
theorem UpperSemicontinuousAt.add
  statement: {f g : α -> γ} (hf : UpperSemicontinuousAt f x)
  proof: hf.add' hg continuous_add.continuousAt

中文:
定理 UpperSemicontinuousAt.add
  结论: {f g : α -> γ} (hf : UpperSemicontinuousAt f x)
  证明: hf.add' hg continuous_add.continuousAt

Depends on / 依赖: continuousAt, continuous_add, continuous_add.continuousAt, hf.add
-/
theorem UpperSemicontinuousAt.add {f g : α -> γ} (hf : UpperSemicontinuousAt f x)
    (hg : UpperSemicontinuousAt g x) : UpperSemicontinuousAt (fun z => f z + g z) x :=
  hf.add' hg continuous_add.continuousAt

/--
theorem `UpperSemicontinuousOn.add` / 定理 `UpperSemicontinuousOn.add`

English:
theorem UpperSemicontinuousOn.add
  statement: {f g : α -> γ} (hf : UpperSemicontinuousOn f s)
  proof: hf.add' hg fun _x _hx => continuous_add.continuousAt

中文:
定理 UpperSemicontinuousOn.add
  结论: {f g : α -> γ} (hf : UpperSemicontinuousOn f s)
  证明: hf.add' hg fun _x _hx => continuous_add.continuousAt

Depends on / 依赖: continuousAt, continuous_add, continuous_add.continuousAt, hf.add
-/
theorem UpperSemicontinuousOn.add {f g : α -> γ} (hf : UpperSemicontinuousOn f s)
    (hg : UpperSemicontinuousOn g s) : UpperSemicontinuousOn (fun z => f z + g z) s :=
  hf.add' hg fun _x _hx => continuous_add.continuousAt

/--
theorem `UpperSemicontinuous.add` / 定理 `UpperSemicontinuous.add`

English:
theorem UpperSemicontinuous.add
  statement: {f g : α -> γ} (hf : UpperSemicontinuous f)
  proof: hf.add' hg fun _x => continuous_add.continuousAt

中文:
定理 UpperSemicontinuous.add
  结论: {f g : α -> γ} (hf : UpperSemicontinuous f)
  证明: hf.add' hg fun _x => continuous_add.continuousAt

Depends on / 依赖: continuousAt, continuous_add, continuous_add.continuousAt, hf.add
-/
theorem UpperSemicontinuous.add {f g : α -> γ} (hf : UpperSemicontinuous f)
    (hg : UpperSemicontinuous g) : UpperSemicontinuous fun z => f z + g z :=
  hf.add' hg fun _x => continuous_add.continuousAt

/--
theorem `upperSemicontinuousWithinAt_sum` / 定理 `upperSemicontinuousWithinAt_sum`

English:
theorem upperSemicontinuousWithinAt_sum
  statement: {f : ι -> α -> γ} {a : Finset ι}
  proof: lowerSemicontinuousWithinAt_sum (γ := γᵒᵈ) ha

中文:
定理 upperSemicontinuousWithinAt_sum
  结论: {f : ι -> α -> γ} {a : 有限集 ι}
  证明: lowerSemicontinuousWithinAt_sum (γ := γᵒᵈ) ha

Depends on / 依赖: lowerSemicontinuousWithinAt_sum
-/
theorem upperSemicontinuousWithinAt_sum {f : ι -> α -> γ} {a : Finset ι}
    (ha : forall i in a, UpperSemicontinuousWithinAt (f i) s x) :
    UpperSemicontinuousWithinAt (fun z => ∑ i in a, f i z) s x :=
  lowerSemicontinuousWithinAt_sum (γ := γᵒᵈ) ha

/--
theorem `upperSemicontinuousAt_sum` / 定理 `upperSemicontinuousAt_sum`

English:
theorem upperSemicontinuousAt_sum
  statement: {f : ι -> α -> γ} {a : Finset ι}
  proof: by
  simp_rw [← upperSemicontinuousWithinAt_univ_iff] at *
  exact upperSemicontinuousWithinAt_sum ha

中文:
定理 upperSemicontinuousAt_sum
  结论: {f : ι -> α -> γ} {a : 有限集 ι}
  证明: by
  simp_rw [← upperSemicontinuousWithinAt_univ_iff] at *
  exact upperSemicontinuousWithinAt_sum ha

Depends on / 依赖: simp_rw, upperSemicontinuousWithinAt_sum, upperSemicontinuousWithinAt_univ_iff
-/
theorem upperSemicontinuousAt_sum {f : ι -> α -> γ} {a : Finset ι}
    (ha : forall i in a, UpperSemicontinuousAt (f i) x) :
    UpperSemicontinuousAt (fun z => ∑ i in a, f i z) x := by
  simp_rw [← upperSemicontinuousWithinAt_univ_iff] at *
  exact upperSemicontinuousWithinAt_sum ha

/--
theorem `upperSemicontinuousOn_sum` / 定理 `upperSemicontinuousOn_sum`

English:
theorem upperSemicontinuousOn_sum
  statement: {f : ι -> α -> γ} {a : Finset ι}
  proof: fun x hx =>
  upperSemicontinuousWithinAt_sum fun i hi => ha i hi x hx

中文:
定理 upperSemicontinuousOn_sum
  结论: {f : ι -> α -> γ} {a : 有限集 ι}
  证明: fun x hx =>
  upperSemicontinuousWithinAt_sum fun i hi => ha i hi x hx
-/
theorem upperSemicontinuousOn_sum {f : ι -> α -> γ} {a : Finset ι}
    (ha : forall i in a, UpperSemicontinuousOn (f i) s) :
    UpperSemicontinuousOn (fun z => ∑ i in a, f i z) s := fun x hx =>
  upperSemicontinuousWithinAt_sum fun i hi => ha i hi x hx

/--
theorem `upperSemicontinuous_sum` / 定理 `upperSemicontinuous_sum`

English:
theorem upperSemicontinuous_sum
  statement: {f : ι -> α -> γ} {a : Finset ι}
  proof: fun x => upperSemicontinuousAt_sum fun i hi => ha i hi x

中文:
定理 upperSemicontinuous_sum
  结论: {f : ι -> α -> γ} {a : 有限集 ι}
  证明: fun x => upperSemicontinuousAt_sum fun i hi => ha i hi x

Depends on / 依赖: upperSemicontinuousAt_sum
-/
theorem upperSemicontinuous_sum {f : ι -> α -> γ} {a : Finset ι}
    (ha : forall i in a, UpperSemicontinuous (f i)) : UpperSemicontinuous fun z => ∑ i in a, f i z :=
  fun x => upperSemicontinuousAt_sum fun i hi => ha i hi x

end

/-! #### Infimum -/

section

variable {α : Type*} {β : Type*} [TopologicalSpace α] [LinearOrder β]
    {f g : α -> β} {s : Set α} {a : α}

/--
theorem `UpperSemicontinuousWithinAt.inf` / 定理 `UpperSemicontinuousWithinAt.inf`

English:
theorem UpperSemicontinuousWithinAt.inf
  proof: LowerSemicontinuousWithinAt.sup (β := βᵒᵈ) hf hg

中文:
定理 UpperSemicontinuousWithinAt.下确界
  证明: LowerSemicontinuousWithinAt.sup (β := βᵒᵈ) hf hg

Depends on / 依赖: LowerSemicontinuousWithinAt, LowerSemicontinuousWithinAt.sup
-/
theorem UpperSemicontinuousWithinAt.inf
    (hf : UpperSemicontinuousWithinAt f s a) (hg : UpperSemicontinuousWithinAt g s a) :
    UpperSemicontinuousWithinAt (fun x => f x ⊓ g x) s a :=
  LowerSemicontinuousWithinAt.sup (β := βᵒᵈ) hf hg

/--
theorem `UpperSemicontinuousAt.inf` / 定理 `UpperSemicontinuousAt.inf`

English:
theorem UpperSemicontinuousAt.inf
  proof: LowerSemicontinuousAt.sup (β := βᵒᵈ) hf hg

中文:
定理 UpperSemicontinuousAt.下确界
  证明: LowerSemicontinuousAt.sup (β := βᵒᵈ) hf hg

Depends on / 依赖: LowerSemicontinuousAt, LowerSemicontinuousAt.sup
-/
theorem UpperSemicontinuousAt.inf
    (hf : UpperSemicontinuousAt f a) (hg : UpperSemicontinuousAt g a) :
    UpperSemicontinuousAt (fun x => f x ⊓ g x) a :=
  LowerSemicontinuousAt.sup (β := βᵒᵈ) hf hg

/--
theorem `UpperSemicontinuousOn.inf` / 定理 `UpperSemicontinuousOn.inf`

English:
theorem UpperSemicontinuousOn.inf
  proof: LowerSemicontinuousOn.sup (β := βᵒᵈ) hf hg

中文:
定理 UpperSemicontinuousOn.下确界
  证明: LowerSemicontinuousOn.sup (β := βᵒᵈ) hf hg

Depends on / 依赖: LowerSemicontinuousOn, LowerSemicontinuousOn.sup
-/
theorem UpperSemicontinuousOn.inf
    (hf : UpperSemicontinuousOn f s) (hg : UpperSemicontinuousOn g s) :
    UpperSemicontinuousOn (fun x => f x ⊓ g x) s :=
  LowerSemicontinuousOn.sup (β := βᵒᵈ) hf hg

/--
theorem `UpperSemicontinuous.inf` / 定理 `UpperSemicontinuous.inf`

English:
theorem UpperSemicontinuous.inf
  given: (hf : UpperSemicontinuous f) (hg : UpperSemicontinuous g)
  proof: LowerSemicontinuous.sup (β := βᵒᵈ) hf hg

中文:
定理 UpperSemicontinuous.下确界
  条件: (hf : UpperSemicontinuous f) (hg : UpperSemicontinuous g)
  证明: LowerSemicontinuous.sup (β := βᵒᵈ) hf hg

Depends on / 依赖: LowerSemicontinuous, LowerSemicontinuous.sup
-/
theorem UpperSemicontinuous.inf (hf : UpperSemicontinuous f) (hg : UpperSemicontinuous g) :
    UpperSemicontinuous (fun x => f x ⊓ g x) :=
  LowerSemicontinuous.sup (β := βᵒᵈ) hf hg

/--
theorem `UpperSemicontinuousWithinAt.sup` / 定理 `UpperSemicontinuousWithinAt.sup`

English:
theorem UpperSemicontinuousWithinAt.sup
  proof: LowerSemicontinuousWithinAt.inf (β := βᵒᵈ) hf hg

中文:
定理 UpperSemicontinuousWithinAt.上确界
  证明: LowerSemicontinuousWithinAt.inf (β := βᵒᵈ) hf hg

Depends on / 依赖: LowerSemicontinuousWithinAt, LowerSemicontinuousWithinAt.inf
-/
theorem UpperSemicontinuousWithinAt.sup
    (hf : UpperSemicontinuousWithinAt f s a) (hg : UpperSemicontinuousWithinAt g s a) :
    UpperSemicontinuousWithinAt (fun x => f x ⊔ g x) s a :=
  LowerSemicontinuousWithinAt.inf (β := βᵒᵈ) hf hg

/--
theorem `UpperSemicontinuousAt.sup` / 定理 `UpperSemicontinuousAt.sup`

English:
theorem UpperSemicontinuousAt.sup
  proof: LowerSemicontinuousAt.inf (β := βᵒᵈ) hf hg

中文:
定理 UpperSemicontinuousAt.上确界
  证明: LowerSemicontinuousAt.inf (β := βᵒᵈ) hf hg

Depends on / 依赖: LowerSemicontinuousAt, LowerSemicontinuousAt.inf
-/
theorem UpperSemicontinuousAt.sup
    (hf : UpperSemicontinuousAt f a) (hg : UpperSemicontinuousAt g a) :
    UpperSemicontinuousAt (fun x => f x ⊔ g x) a :=
  LowerSemicontinuousAt.inf (β := βᵒᵈ) hf hg

/--
theorem `UpperSemicontinuousOn.sup` / 定理 `UpperSemicontinuousOn.sup`

English:
theorem UpperSemicontinuousOn.sup
  proof: LowerSemicontinuousOn.inf (β := βᵒᵈ) hf hg

中文:
定理 UpperSemicontinuousOn.上确界
  证明: LowerSemicontinuousOn.inf (β := βᵒᵈ) hf hg

Depends on / 依赖: LowerSemicontinuousOn, LowerSemicontinuousOn.inf
-/
theorem UpperSemicontinuousOn.sup
    (hf : UpperSemicontinuousOn f s) (hg : UpperSemicontinuousOn g s) :
    UpperSemicontinuousOn (fun x => f x ⊔ g x) s :=
  LowerSemicontinuousOn.inf (β := βᵒᵈ) hf hg

/--
theorem `UpperSemicontinuous.sup` / 定理 `UpperSemicontinuous.sup`

English:
theorem UpperSemicontinuous.sup
  given: (hf : UpperSemicontinuous f) (hg : UpperSemicontinuous g)
  proof: LowerSemicontinuous.inf (β := βᵒᵈ) hf hg

中文:
定理 UpperSemicontinuous.上确界
  条件: (hf : UpperSemicontinuous f) (hg : UpperSemicontinuous g)
  证明: LowerSemicontinuous.inf (β := βᵒᵈ) hf hg

Depends on / 依赖: LowerSemicontinuous, LowerSemicontinuous.inf
-/
theorem UpperSemicontinuous.sup (hf : UpperSemicontinuous f) (hg : UpperSemicontinuous g) :
    UpperSemicontinuous fun x => f x ⊔ g x :=
  LowerSemicontinuous.inf (β := βᵒᵈ) hf hg


end

section

variable {ι : Sort*} {δ δ' : Type*} [CompleteLinearOrder δ] [ConditionallyCompleteLinearOrder δ']

/--
theorem `upperSemicontinuousWithinAt_ciInf` / 定理 `upperSemicontinuousWithinAt_ciInf`

English:
theorem upperSemicontinuousWithinAt_ciInf
  statement: {f : ι -> α -> δ'}
  proof: lowerSemicontinuousWithinAt_ciSup (δ' := δ'ᵒᵈ) bdd h

中文:
定理 upperSemicontinuousWithinAt_ciInf
  结论: {f : ι -> α -> δ'}
  证明: lowerSemicontinuousWithinAt_ciSup (δ' := δ'ᵒᵈ) bdd h

Depends on / 依赖: lowerSemicontinuousWithinAt_ciSup
-/
theorem upperSemicontinuousWithinAt_ciInf {f : ι -> α -> δ'}
    (bdd : forallᶠ y in 𝓝[s] x, BddBelow (range fun i => f i y))
    (h : forall i, UpperSemicontinuousWithinAt (f i) s x) :
    UpperSemicontinuousWithinAt (fun x' => ⨅ i, f i x') s x :=
  lowerSemicontinuousWithinAt_ciSup (δ' := δ'ᵒᵈ) bdd h

/--
theorem `upperSemicontinuousWithinAt_iInf` / 定理 `upperSemicontinuousWithinAt_iInf`

English:
theorem upperSemicontinuousWithinAt_iInf
  statement: {f : ι -> α -> δ}
  proof: lowerSemicontinuousWithinAt_iSup (δ := δᵒᵈ) h

中文:
定理 upperSemicontinuousWithinAt_iInf
  结论: {f : ι -> α -> δ}
  证明: lowerSemicontinuousWithinAt_iSup (δ := δᵒᵈ) h

Depends on / 依赖: lowerSemicontinuousWithinAt_iSup
-/
theorem upperSemicontinuousWithinAt_iInf {f : ι -> α -> δ}
    (h : forall i, UpperSemicontinuousWithinAt (f i) s x) :
    UpperSemicontinuousWithinAt (fun x' => ⨅ i, f i x') s x :=
  lowerSemicontinuousWithinAt_iSup (δ := δᵒᵈ) h

/--
theorem `upperSemicontinuousWithinAt_biInf` / 定理 `upperSemicontinuousWithinAt_biInf`

English:
theorem upperSemicontinuousWithinAt_biInf
  statement: {p : ι -> Prop} {f : forall i, p i -> α -> δ}
  proof: upperSemicontinuousWithinAt_iInf fun i => upperSemicontinuousWithinAt_iInf fun hi => h i hi

中文:
定理 upperSemicontinuousWithinAt_biInf
  结论: {p : ι -> 命题} {f : 对任意 i, p i -> α -> δ}
  证明: upperSemicontinuousWithinAt_iInf fun i => upperSemicontinuousWithinAt_iInf fun hi => h i hi

Depends on / 依赖: upperSemicontinuousWithinAt_iInf
-/
theorem upperSemicontinuousWithinAt_biInf {p : ι -> Prop} {f : forall i, p i -> α -> δ}
    (h : forall i hi, UpperSemicontinuousWithinAt (f i hi) s x) :
    UpperSemicontinuousWithinAt (fun x' => ⨅ (i) (hi), f i hi x') s x :=
  upperSemicontinuousWithinAt_iInf fun i => upperSemicontinuousWithinAt_iInf fun hi => h i hi

/--
theorem `upperSemicontinuousAt_ciInf` / 定理 `upperSemicontinuousAt_ciInf`

English:
theorem upperSemicontinuousAt_ciInf
  statement: {f : ι -> α -> δ'}
  proof: @lowerSemicontinuousAt_ciSup α _ x ι δ'ᵒᵈ _ f bdd h

中文:
定理 upperSemicontinuousAt_ciInf
  结论: {f : ι -> α -> δ'}
  证明: @lowerSemicontinuousAt_ciSup α _ x ι δ'ᵒᵈ _ f bdd h

Depends on / 依赖: lowerSemicontinuousAt_ciSup
-/
theorem upperSemicontinuousAt_ciInf {f : ι -> α -> δ'}
    (bdd : forallᶠ y in 𝓝 x, BddBelow (range fun i => f i y)) (h : forall i, UpperSemicontinuousAt (f i) x) :
    UpperSemicontinuousAt (fun x' => ⨅ i, f i x') x :=
  @lowerSemicontinuousAt_ciSup α _ x ι δ'ᵒᵈ _ f bdd h

/--
theorem `upperSemicontinuousAt_iInf` / 定理 `upperSemicontinuousAt_iInf`

English:
theorem upperSemicontinuousAt_iInf
  given: {f : ι -> α -> δ} (h : forall i, UpperSemicontinuousAt (f i) x)
  proof: @lowerSemicontinuousAt_iSup α _ x ι δᵒᵈ _ f h

中文:
定理 upperSemicontinuousAt_iInf
  条件: {f : ι -> α -> δ} (h : 对任意 i, UpperSemicontinuousAt (f i) x)
  证明: @lowerSemicontinuousAt_iSup α _ x ι δᵒᵈ _ f h

Depends on / 依赖: lowerSemicontinuousAt_iSup
-/
theorem upperSemicontinuousAt_iInf {f : ι -> α -> δ} (h : forall i, UpperSemicontinuousAt (f i) x) :
    UpperSemicontinuousAt (fun x' => ⨅ i, f i x') x :=
  @lowerSemicontinuousAt_iSup α _ x ι δᵒᵈ _ f h

/--
theorem `upperSemicontinuousAt_biInf` / 定理 `upperSemicontinuousAt_biInf`

English:
theorem upperSemicontinuousAt_biInf
  statement: {p : ι -> Prop} {f : forall i, p i -> α -> δ}
  proof: upperSemicontinuousAt_iInf fun i => upperSemicontinuousAt_iInf fun hi => h i hi

中文:
定理 upperSemicontinuousAt_biInf
  结论: {p : ι -> 命题} {f : 对任意 i, p i -> α -> δ}
  证明: upperSemicontinuousAt_iInf fun i => upperSemicontinuousAt_iInf fun hi => h i hi

Depends on / 依赖: upperSemicontinuousAt_iInf
-/
theorem upperSemicontinuousAt_biInf {p : ι -> Prop} {f : forall i, p i -> α -> δ}
    (h : forall i hi, UpperSemicontinuousAt (f i hi) x) :
    UpperSemicontinuousAt (fun x' => ⨅ (i) (hi), f i hi x') x :=
  upperSemicontinuousAt_iInf fun i => upperSemicontinuousAt_iInf fun hi => h i hi

/--
theorem `upperSemicontinuousOn_ciInf` / 定理 `upperSemicontinuousOn_ciInf`

English:
theorem upperSemicontinuousOn_ciInf
  statement: {f : ι -> α -> δ'}
  proof: fun x hx =>
  upperSemicontinuousWithinAt_ciInf (eventually_nhdsWithin_of_forall bdd) fun i => h i x hx

中文:
定理 upperSemicontinuousOn_ciInf
  结论: {f : ι -> α -> δ'}
  证明: fun x hx =>
  upperSemicontinuousWithinAt_ciInf (eventually_nhdsWithin_of_forall bdd) fun i => h i x hx
-/
theorem upperSemicontinuousOn_ciInf {f : ι -> α -> δ'}
    (bdd : forall x in s, BddBelow (range fun i => f i x)) (h : forall i, UpperSemicontinuousOn (f i) s) :
    UpperSemicontinuousOn (fun x' => ⨅ i, f i x') s := fun x hx =>
  upperSemicontinuousWithinAt_ciInf (eventually_nhdsWithin_of_forall bdd) fun i => h i x hx

/--
theorem `upperSemicontinuousOn_iInf` / 定理 `upperSemicontinuousOn_iInf`

English:
theorem upperSemicontinuousOn_iInf
  given: {f : ι -> α -> δ} (h : forall i, UpperSemicontinuousOn (f i) s)
  proof: fun x hx =>
  upperSemicontinuousWithinAt_iInf fun i => h i x hx

中文:
定理 upperSemicontinuousOn_iInf
  条件: {f : ι -> α -> δ} (h : 对任意 i, UpperSemicontinuousOn (f i) s)
  证明: fun x hx =>
  upperSemicontinuousWithinAt_iInf fun i => h i x hx
-/
theorem upperSemicontinuousOn_iInf {f : ι -> α -> δ} (h : forall i, UpperSemicontinuousOn (f i) s) :
    UpperSemicontinuousOn (fun x' => ⨅ i, f i x') s := fun x hx =>
  upperSemicontinuousWithinAt_iInf fun i => h i x hx

/--
theorem `upperSemicontinuousOn_biInf` / 定理 `upperSemicontinuousOn_biInf`

English:
theorem upperSemicontinuousOn_biInf
  statement: {p : ι -> Prop} {f : forall i, p i -> α -> δ}
  proof: upperSemicontinuousOn_iInf fun i => upperSemicontinuousOn_iInf fun hi => h i hi

中文:
定理 upperSemicontinuousOn_biInf
  结论: {p : ι -> 命题} {f : 对任意 i, p i -> α -> δ}
  证明: upperSemicontinuousOn_iInf fun i => upperSemicontinuousOn_iInf fun hi => h i hi

Depends on / 依赖: upperSemicontinuousOn_iInf
-/
theorem upperSemicontinuousOn_biInf {p : ι -> Prop} {f : forall i, p i -> α -> δ}
    (h : forall i hi, UpperSemicontinuousOn (f i hi) s) :
    UpperSemicontinuousOn (fun x' => ⨅ (i) (hi), f i hi x') s :=
  upperSemicontinuousOn_iInf fun i => upperSemicontinuousOn_iInf fun hi => h i hi

/--
theorem `upperSemicontinuous_ciInf` / 定理 `upperSemicontinuous_ciInf`

English:
theorem upperSemicontinuous_ciInf
  statement: {f : ι -> α -> δ'} (bdd : forall x, BddBelow (range fun i => f i x))
  proof: fun x =>
  upperSemicontinuousAt_ciInf (Eventually.of_forall bdd) fun i => h i x

中文:
定理 upperSemicontinuous_ciInf
  结论: {f : ι -> α -> δ'} (bdd : 对任意 x, BddBelow (range fun i => f i x))
  证明: fun x =>
  upperSemicontinuousAt_ciInf (Eventually.of_forall bdd) fun i => h i x
-/
theorem upperSemicontinuous_ciInf {f : ι -> α -> δ'} (bdd : forall x, BddBelow (range fun i => f i x))
    (h : forall i, UpperSemicontinuous (f i)) : UpperSemicontinuous fun x' => ⨅ i, f i x' := fun x =>
  upperSemicontinuousAt_ciInf (Eventually.of_forall bdd) fun i => h i x

/--
theorem `upperSemicontinuous_iInf` / 定理 `upperSemicontinuous_iInf`

English:
theorem upperSemicontinuous_iInf
  given: {f : ι -> α -> δ} (h : forall i, UpperSemicontinuous (f i))
  proof: fun x => upperSemicontinuousAt_iInf fun i => h i x

中文:
定理 upperSemicontinuous_iInf
  条件: {f : ι -> α -> δ} (h : 对任意 i, UpperSemicontinuous (f i))
  证明: fun x => upperSemicontinuousAt_iInf fun i => h i x

Depends on / 依赖: upperSemicontinuousAt_iInf
-/
theorem upperSemicontinuous_iInf {f : ι -> α -> δ} (h : forall i, UpperSemicontinuous (f i)) :
    UpperSemicontinuous fun x' => ⨅ i, f i x' := fun x => upperSemicontinuousAt_iInf fun i => h i x

/--
theorem `upperSemicontinuous_biInf` / 定理 `upperSemicontinuous_biInf`

English:
theorem upperSemicontinuous_biInf
  statement: {p : ι -> Prop} {f : forall i, p i -> α -> δ}
  proof: upperSemicontinuous_iInf fun i => upperSemicontinuous_iInf fun hi => h i hi

中文:
定理 upperSemicontinuous_biInf
  结论: {p : ι -> 命题} {f : 对任意 i, p i -> α -> δ}
  证明: upperSemicontinuous_iInf fun i => upperSemicontinuous_iInf fun hi => h i hi

Depends on / 依赖: upperSemicontinuous_iInf
-/
theorem upperSemicontinuous_biInf {p : ι -> Prop} {f : forall i, p i -> α -> δ}
    (h : forall i hi, UpperSemicontinuous (f i hi)) :
    UpperSemicontinuous fun x' => ⨅ (i) (hi), f i hi x' :=
  upperSemicontinuous_iInf fun i => upperSemicontinuous_iInf fun hi => h i hi

end

section

variable {γ : Type*} [LinearOrder γ] [TopologicalSpace γ] [OrderTopology γ]

/--
theorem `continuousWithinAt_iff_lower_upperSemicontinuousWithinAt` / 定理 `continuousWithinAt_iff_lower_upperSemicontinuousWithinAt`

English:
theorem continuousWithinAt_iff_lower_upperSemicontinuousWithinAt
  given: {f : α -> γ}
  proof: by
  refine ⟨fun h => ⟨h.lowerSemicontinuousWithinAt, h.upperSemicontinuousWithinAt⟩, ?_⟩
  rintro ⟨h₁, h₂⟩
  intro v hv
  simp only [Filter.mem_map]
  by_cases! Hl : exists l, l < f x
  · rcases exists_Ioc_subset_of_mem_nhds hv Hl with ⟨l, lfx, hl⟩
    by_cases! Hu : exists u, f x < u
    · rcases 

中文:
定理 continuousWithinAt_iff_lower_upperSemicontinuousWithinAt
  条件: {f : α -> γ}
  证明: by
  refine ⟨fun h => ⟨h.lowerSemicontinuousWithinAt, h.upperSemicontinuousWithinAt⟩, ?_⟩
  rintro ⟨h₁, h₂⟩
  intro v hv
  simp only [Filter.mem_map]
  by_cases! Hl : exists l, l < f x
  · rcases exists_Ioc_subset_of_mem_nhds hv Hl with ⟨l, lfx, hl⟩
    by_cases! Hu : exists u, f x < u
    · rcases 

Depends on / 依赖: Filter, Filter.mem_map, exists_Ico_subset_of_mem_nhds, exists_Ioc_subset_of_mem_nhds, filter_upwards, h.lowerSemicontinuousWithinAt, h.upperSemicontinuousWithinAt, le_of_lt, le_or_gt, lowerSemicontinuousWithinAt, mem_map, upperSemicontinuousWithinAt
-/
theorem continuousWithinAt_iff_lower_upperSemicontinuousWithinAt {f : α -> γ} :
    ContinuousWithinAt f s x ↔
      LowerSemicontinuousWithinAt f s x ∧ UpperSemicontinuousWithinAt f s x := by
  refine ⟨fun h => ⟨h.lowerSemicontinuousWithinAt, h.upperSemicontinuousWithinAt⟩, ?_⟩
  rintro ⟨h₁, h₂⟩
  intro v hv
  simp only [Filter.mem_map]
  by_cases! Hl : exists l, l < f x
  · rcases exists_Ioc_subset_of_mem_nhds hv Hl with ⟨l, lfx, hl⟩
    by_cases! Hu : exists u, f x < u
    · rcases exists_Ico_subset_of_mem_nhds hv Hu with ⟨u, fxu, hu⟩
      filter_upwards [h₁ l lfx, h₂ u fxu] with a lfa fau
      rcases le_or_gt (f a) (f x) with h | h
      · exact hl ⟨lfa, h⟩
      · exact hu ⟨le_of_lt h, fau⟩
    · filter_upwards [h₁ l lfx] with a lfa using hl ⟨lfa, Hu (f a)⟩
  · by_cases! Hu : exists u, f x < u
    · rcases exists_Ico_subset_of_mem_nhds hv Hu with ⟨u, fxu, hu⟩
      filter_upwards [h₂ u fxu] with a lfa
      apply hu
      exact ⟨Hl (f a), lfa⟩
    · apply Filter.Eventually.of_forall
      intro a
      have : f a = f x := le_antisymm (Hu _) (Hl _)
      rw [this]
      exact mem_of_mem_nhds hv

/--
theorem `continuousAt_iff_lower_upperSemicontinuousAt` / 定理 `continuousAt_iff_lower_upperSemicontinuousAt`

English:
theorem continuousAt_iff_lower_upperSemicontinuousAt
  given: {f : α -> γ}
  proof: by
  simp_rw [← continuousWithinAt_univ, ← lowerSemicontinuousWithinAt_univ_iff, ←
    upperSemicontinuousWithinAt_univ_iff, continuousWithinAt_iff_lower_upperSemicontinuousWithinAt]

中文:
定理 continuousAt_iff_lower_upperSemicontinuousAt
  条件: {f : α -> γ}
  证明: by
  simp_rw [← continuousWithinAt_univ, ← lowerSemicontinuousWithinAt_univ_iff, ←
    upperSemicontinuousWithinAt_univ_iff, continuousWithinAt_iff_lower_upperSemicontinuousWithinAt]

Depends on / 依赖: continuousWithinAt_iff_lower_upperSemicontinuousWithinAt, continuousWithinAt_univ, lowerSemicontinuousWithinAt_univ_iff, simp_rw, upperSemicontinuousWithinAt_univ_iff
-/
theorem continuousAt_iff_lower_upperSemicontinuousAt {f : α -> γ} :
    ContinuousAt f x ↔ LowerSemicontinuousAt f x ∧ UpperSemicontinuousAt f x := by
  simp_rw [← continuousWithinAt_univ, ← lowerSemicontinuousWithinAt_univ_iff, ←
    upperSemicontinuousWithinAt_univ_iff, continuousWithinAt_iff_lower_upperSemicontinuousWithinAt]

/--
theorem `continuousOn_iff_lower_upperSemicontinuousOn` / 定理 `continuousOn_iff_lower_upperSemicontinuousOn`

English:
theorem continuousOn_iff_lower_upperSemicontinuousOn
  given: {f : α -> γ}
  proof: by
  simp only [ContinuousOn, continuousWithinAt_iff_lower_upperSemicontinuousWithinAt]
  exact
    ⟨fun H => ⟨fun x hx => (H x hx).1, fun x hx => (H x hx).2⟩, fun H x hx => ⟨H.1 x hx, H.2 x hx⟩⟩

中文:
定理 continuousOn_iff_lower_upperSemicontinuousOn
  条件: {f : α -> γ}
  证明: by
  simp only [ContinuousOn, continuousWithinAt_iff_lower_upperSemicontinuousWithinAt]
  exact
    ⟨fun H => ⟨fun x hx => (H x hx).1, fun x hx => (H x hx).2⟩, fun H x hx => ⟨H.1 x hx, H.2 x hx⟩⟩

Depends on / 依赖: ContinuousOn, continuousWithinAt_iff_lower_upperSemicontinuousWithinAt
-/
theorem continuousOn_iff_lower_upperSemicontinuousOn {f : α -> γ} :
    ContinuousOn f s ↔ LowerSemicontinuousOn f s ∧ UpperSemicontinuousOn f s := by
  simp only [ContinuousOn, continuousWithinAt_iff_lower_upperSemicontinuousWithinAt]
  exact
    ⟨fun H => ⟨fun x hx => (H x hx).1, fun x hx => (H x hx).2⟩, fun H x hx => ⟨H.1 x hx, H.2 x hx⟩⟩

/--
theorem `continuous_iff_lower_upperSemicontinuous` / 定理 `continuous_iff_lower_upperSemicontinuous`

English:
theorem continuous_iff_lower_upperSemicontinuous
  given: {f : α -> γ}
  proof: by
  simp_rw [← continuousOn_univ, continuousOn_iff_lower_upperSemicontinuousOn,
    lowerSemicontinuousOn_univ_iff, upperSemicontinuousOn_univ_iff]

中文:
定理 continuous_iff_lower_upperSemicontinuous
  条件: {f : α -> γ}
  证明: by
  simp_rw [← continuousOn_univ, continuousOn_iff_lower_upperSemicontinuousOn,
    lowerSemicontinuousOn_univ_iff, upperSemicontinuousOn_univ_iff]

Depends on / 依赖: continuousOn_iff_lower_upperSemicontinuousOn, continuousOn_univ, lowerSemicontinuousOn_univ_iff, simp_rw, upperSemicontinuousOn_univ_iff
-/
theorem continuous_iff_lower_upperSemicontinuous {f : α -> γ} :
    Continuous f ↔ LowerSemicontinuous f ∧ UpperSemicontinuous f := by
  simp_rw [← continuousOn_univ, continuousOn_iff_lower_upperSemicontinuousOn,
    lowerSemicontinuousOn_univ_iff, upperSemicontinuousOn_univ_iff]

end
