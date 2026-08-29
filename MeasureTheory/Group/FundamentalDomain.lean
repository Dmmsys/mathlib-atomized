/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Alex Kontorovich, Heather Macbeth
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Fundamental domain of a group action

A set `s` is said to be a *fundamental domain* of an action of a group `G` on a measurable space `α`
with respect to a measure `μ` if

* `s` is a measurable set;

* the sets `g • s` over all `g : G` cover almost all points of the whole space;

* the sets `g • s`, are pairwise a.e. disjoint, i.e., `μ (g₁ • s ∩ g₂ • s) = 0` whenever `g₁ ≠ g₂`;
  we require this for `g₂ = 1` in the definition, then deduce it for any two `g₁ ≠ g₂`.

In this file we prove that in case of a countable group `G` and a measure-preserving action, any two
fundamental domains have the same measure, and for a `G`-invariant function, its integrals over any
two fundamental domains are equal to each other.

We also generate additive versions of all theorems in this file using the `to_additive` attribute.

* We define the `HasFundamentalDomain` typeclass, in particular to be able to define the `covolume`
  of a quotient of `α` by a group `G`, which under reasonable conditions does not depend on the
  choice of fundamental domain.

* We define the `QuotientMeasureEqMeasurePreimage` typeclass to describe a situation in which a
  measure `μ` on `α ⧸ G` can be computed by taking a measure `ν` on `α` of the intersection of the
  pullback with a fundamental domain.

## Main declarations

* `MeasureTheory.IsFundamentalDomain`: Predicate for a set to be a fundamental domain of the
  action of a group
* `MeasureTheory.fundamentalFrontier`: Fundamental frontier of a set under the action of a group.
  Elements of `s` that belong to some other translate of `s`.
* `MeasureTheory.fundamentalInterior`: Fundamental interior of a set under the action of a group.
  Elements of `s` that do not belong to any other translate of `s`.
-/

@[expose] public section


open scoped ENNReal Pointwise Topology NNReal ENNReal MeasureTheory

open MeasureTheory MeasureTheory.Measure Set Function TopologicalSpace Filter

namespace MeasureTheory

/--
Definition of `IsAddFundamentalDomain` / `IsAddFundamentalDomain` 的定义

English:
structure IsAddFundamentalDomain
  parameters: (G : Type*) {α : Type*} [Zero G] [VAdd G α] [MeasurableSpace α]
  axioms and operations (2):
    - nullMeasurableSet : NullMeasurableSet s μ
    - ae_covers : forallᵐ x ∂μ, exists g : G, g +ᵥ x in s

中文:
结构 是加法FundamentalDomain
  参数: (G : 类型) {α : 类型} [零 G] [向量加法 G α] [可测空间 α]
  公理与运算 (2 个):
    - nullMeasurableSet : NullMeasurableSet s μ
    - ae_covers : 对任意ᵐ x ∂μ, 存在 g : G, g +ᵥ x in s

Depends on / 依赖: AEDisjoint, NullMeasurableSet, Pairwise, ae_covers, aedisjoint, nullMeasurableSet, protected, volume_tac
-/
structure IsAddFundamentalDomain (G : Type*) {α : Type*} [Zero G] [VAdd G α] [MeasurableSpace α]
    (s : Set α) (μ : Measure α := by volume_tac) : Prop where
  protected nullMeasurableSet : NullMeasurableSet s μ
  protected ae_covers : forallᵐ x ∂μ, exists g : G, g +ᵥ x in s
protected aedisjoint : Pairwise (AEDisjoint μ on fun g : G => g +ᵥ s)

/-- A measurable set `s` is a *fundamental domain* for an action of a group `G` on a measurable
space `α` with respect to a measure `μ` if the sets `g • s`, `g : G`, are pairwise a.e. disjoint and
cover the whole space. -/
@[to_additive IsAddFundamentalDomain]
/--
Definition of `IsFundamentalDomain` / `IsFundamentalDomain` 的定义

English:
structure IsFundamentalDomain
  parameters: (G : Type*) {α : Type*} [One G] [SMul G α] [MeasurableSpace α]
  axioms and operations (2):
    - nullMeasurableSet : NullMeasurableSet s μ
    - ae_covers : forallᵐ x ∂μ, exists g : G, g • x in s

中文:
结构 是FundamentalDomain
  参数: (G : 类型) {α : 类型} [幺 G] [标量乘法 G α] [可测空间 α]
  公理与运算 (2 个):
    - nullMeasurableSet : NullMeasurableSet s μ
    - ae_covers : 对任意ᵐ x ∂μ, 存在 g : G, g • x in s

Depends on / 依赖: AEDisjoint, NullMeasurableSet, Pairwise, ae_covers, aedisjoint, nullMeasurableSet, protected, volume_tac
-/
structure IsFundamentalDomain (G : Type*) {α : Type*} [One G] [SMul G α] [MeasurableSpace α]
    (s : Set α) (μ : Measure α := by volume_tac) : Prop where
  protected nullMeasurableSet : NullMeasurableSet s μ
  protected ae_covers : forallᵐ x ∂μ, exists g : G, g • x in s
protected aedisjoint : Pairwise (AEDisjoint μ on fun g : G => g • s)

variable {G H α β E : Type*}

namespace IsFundamentalDomain

variable [Group G] [Group H] [MulAction G α] [MeasurableSpace α] [MulAction H β] [MeasurableSpace β]
  [NormedAddCommGroup E] {s t : Set α} {μ : Measure α}

/-- If for each `x : α`, exactly one of `g • x`, `g : G`, belongs to a measurable set `s`, then `s`
is a fundamental domain for the action of `G` on `α`. -/
@[to_additive /-- If for each `x : α`, exactly one of `g +ᵥ x`, `g : G`, belongs to a measurable set
`s`, then `s` is a fundamental domain for the additive action of `G` on `α`. -/]
/--
theorem `mk'` / 定理 `mk'`

English:
theorem mk'
  given: (h_meas : NullMeasurableSet s μ) (h_exists : forall x : α, exists! g : G, g • x in s)
  proof: h_meas
  ae_covers := Eventually.of_forall fun x => (h_exists x).exists
aedisjoint a b hab := Disjoint.aedisjoint disjoint_left.2 fun x hxa hxb => by
    rw [mem_smul_set_iff_inv_smul_mem] at hxa hxb
    exact hab (inv_injective <| (h_exists x).unique hxa hxb)

中文:
定理 mk'
  条件: (h_meas : NullMeasurableSet s μ) (h_存在 : 对任意 x : α, 存在! g : G, g • x in s)
  证明: h_meas
  ae_covers := Eventually.of_forall fun x => (h_exists x).exists
aedisjoint a b hab := Disjoint.aedisjoint disjoint_left.2 fun x hxa hxb => by
    rw [mem_smul_set_iff_inv_smul_mem] at hxa hxb
    exact hab (inv_injective <| (h_exists x).unique hxa hxb)

Depends on / 依赖: h_meas
-/
theorem mk' (h_meas : NullMeasurableSet s μ) (h_exists : forall x : α, exists! g : G, g • x in s) :
    IsFundamentalDomain G s μ where
  nullMeasurableSet := h_meas
  ae_covers := Eventually.of_forall fun x => (h_exists x).exists
aedisjoint a b hab := Disjoint.aedisjoint disjoint_left.2 fun x hxa hxb => by
    rw [mem_smul_set_iff_inv_smul_mem] at hxa hxb
    exact hab (inv_injective <| (h_exists x).unique hxa hxb)

/-- For `s` to be a fundamental domain, it's enough to check
`MeasureTheory.AEDisjoint (g • s) s` for `g ≠ 1`. -/
@[to_additive /-- For `s` to be a fundamental domain, it's enough to check
  `MeasureTheory.AEDisjoint (g +ᵥ s) s` for `g ≠ 0`. -/]
/--
theorem `mk''` / 定理 `mk''`

English:
theorem mk''
  statement: (h_meas : NullMeasurableSet s μ) (h_ae_covers : forallᵐ x ∂μ, exists g : G, g • x in s)
  proof: h_meas
  ae_covers := h_ae_covers
  aedisjoint := pairwise_aedisjoint_of_aedisjoint_forall_ne_one h_ae_disjoint h_qmp

中文:
定理 mk''
  结论: (h_meas : NullMeasurableSet s μ) (h_ae_covers : 对任意ᵐ x ∂μ, 存在 g : G, g • x in s)
  证明: h_meas
  ae_covers := h_ae_covers
  aedisjoint := pairwise_aedisjoint_of_aedisjoint_forall_ne_one h_ae_disjoint h_qmp

Depends on / 依赖: h_meas
-/
theorem mk'' (h_meas : NullMeasurableSet s μ) (h_ae_covers : forallᵐ x ∂μ, exists g : G, g • x in s)
    (h_ae_disjoint : forall g, g != (1 : G) -> AEDisjoint μ (g • s) s)
    (h_qmp : forall g : G, QuasiMeasurePreserving ((g • ·) : α -> α) μ μ) :
    IsFundamentalDomain G s μ where
  nullMeasurableSet := h_meas
  ae_covers := h_ae_covers
  aedisjoint := pairwise_aedisjoint_of_aedisjoint_forall_ne_one h_ae_disjoint h_qmp

/-- If a measurable space has a finite measure `μ` and a countable group `G` acts
quasi-measure-preservingly, then to show that a set `s` is a fundamental domain, it is sufficient
to check that its translates `g • s` are (almost) disjoint and that the sum `∑' g, μ (g • s)` is
sufficiently large. -/
@[to_additive
  /-- If a measurable space has a finite measure `μ` and a countable additive group `G` acts
  quasi-measure-preservingly, then to show that a set `s` is a fundamental domain, it is sufficient
  to check that its translates `g +ᵥ s` are (almost) disjoint and that the sum `∑' g, μ (g +ᵥ s)` is
  sufficiently large. -/]
/--
theorem `mk_of_measure_univ_le` / 定理 `mk_of_measure_univ_le`

English:
theorem mk_of_measure_univ_le
  statement: [IsFiniteMeasure μ] [Countable G] (h_meas : NullMeasurableSet s μ)
  proof: have aedisjoint : Pairwise (AEDisjoint μ on fun g : G => g • s) :=
    pairwise_aedisjoint_of_aedisjoint_forall_ne_one h_ae_disjoint h_qmp
  { nullMeasurableSet := h_meas
    aedisjoint
    ae_covers := by
      replace h_meas : forall g : G, NullMeasurableSet (g • s) μ := fun g => by
        rw [← inv_inv g]; rw [← preimage_smul]; exact h_meas.preimage (h_qmp g⁻¹)
      have h_meas' : NullMeasurableSet {a | exists g : G, g • a in s} μ := by
        rw [← iUnion_smul_eq_ofPred_exists]; exact .iUnion h_meas
      rw [ae_iff_measure_eq h_meas']; rw [← iUnion_smul_eq_ofPred_exists]
      refine le_antisymm (measure_mono <| subset_univ _) ?_
      rw [measure_iUnion₀ aedisjoint h_meas]
      exact h_measure_univ_le }

@[to_additive]

中文:
定理 mk_of_measure_univ_le
  结论: [是有限测度 μ] [可数 G] (h_meas : NullMeasurableSet s μ)
  证明: have aedisjoint : Pairwise (AEDisjoint μ on fun g : G => g • s) :=
    pairwise_aedisjoint_of_aedisjoint_forall_ne_one h_ae_disjoint h_qmp
  { nullMeasurableSet := h_meas
    aedisjoint
    ae_covers := by
      replace h_meas : forall g : G, NullMeasurableSet (g • s) μ := fun g => by
        rw [← inv_inv g]; rw [← preimage_smul]; exact h_meas.preimage (h_qmp g⁻¹)
      have h_meas' : NullMeasurableSet {a | exists g : G, g • a in s} μ := by
        rw [← iUnion_smul_eq_ofPred_exists]; exact .iUnion h_meas
      rw [ae_iff_measure_eq h_meas']; rw [← iUnion_smul_eq_ofPred_exists]
      refine le_antisymm (measure_mono <| subset_univ _) ?_
      rw [measure_iUnion₀ aedisjoint h_meas]
      exact h_measure_univ_le }

@[to_additive]

Depends on / 依赖: AEDisjoint, NullMeasurableSet, Pairwise, ae_covers, ae_iff_measure_eq, aedisjoint, h_ae_disjoint, h_meas, h_meas.preimage, h_qmp, iUnion, iUnion_smul_eq_ofPred_exists, inv_inv, nullMeasurableSet, pairwise_aedisjoint_of_aedisjoint_forall_ne_one, preimage, preimage_smul, replace
-/
theorem mk_of_measure_univ_le [IsFiniteMeasure μ] [Countable G] (h_meas : NullMeasurableSet s μ)
    (h_ae_disjoint : forall g != (1 : G), AEDisjoint μ (g • s) s)
    (h_qmp : forall g : G, QuasiMeasurePreserving (g • · : α -> α) μ μ)
    (h_measure_univ_le : μ (univ : Set α) <= ∑' g : G, μ (g • s)) : IsFundamentalDomain G s μ :=
  have aedisjoint : Pairwise (AEDisjoint μ on fun g : G => g • s) :=
    pairwise_aedisjoint_of_aedisjoint_forall_ne_one h_ae_disjoint h_qmp
  { nullMeasurableSet := h_meas
    aedisjoint
    ae_covers := by
      replace h_meas : forall g : G, NullMeasurableSet (g • s) μ := fun g => by
        rw [← inv_inv g]; rw [← preimage_smul]; exact h_meas.preimage (h_qmp g⁻¹)
      have h_meas' : NullMeasurableSet {a | exists g : G, g • a in s} μ := by
        rw [← iUnion_smul_eq_ofPred_exists]; exact .iUnion h_meas
      rw [ae_iff_measure_eq h_meas']; rw [← iUnion_smul_eq_ofPred_exists]
      refine le_antisymm (measure_mono <| subset_univ _) ?_
      rw [measure_iUnion₀ aedisjoint h_meas]
      exact h_measure_univ_le }

@[to_additive]
/--
theorem `iUnion_smul_ae_eq` / 定理 `iUnion_smul_ae_eq`

English:
theorem iUnion_smul_ae_eq
  given: (h : IsFundamentalDomain G s μ)
  statement: ⋃ g : G, g • s =ᵐ[μ] univ
  proof: eventuallyEq_univ.2 h.ae_covers.mono fun _ ⟨g, hg⟩ =>
    mem_iUnion.2 ⟨g⁻¹, _, hg, inv_smul_smul _ _⟩

@[to_additive]

中文:
定理 iUnion_smul_ae_eq
  条件: (h : 是FundamentalDomain G s μ)
  结论: ⋃ g : G, g • s =ᵐ[μ] univ
  证明: eventuallyEq_univ.2 h.ae_covers.mono fun _ ⟨g, hg⟩ =>
    mem_iUnion.2 ⟨g⁻¹, _, hg, inv_smul_smul _ _⟩

@[to_additive]

Depends on / 依赖: ae_covers, eventuallyEq_univ, h.ae_covers.mono, inv_smul_smul, mem_iUnion
-/
theorem iUnion_smul_ae_eq (h : IsFundamentalDomain G s μ) : ⋃ g : G, g • s =ᵐ[μ] univ :=
eventuallyEq_univ.2 h.ae_covers.mono fun _ ⟨g, hg⟩ =>
    mem_iUnion.2 ⟨g⁻¹, _, hg, inv_smul_smul _ _⟩

@[to_additive]
/--
theorem `measure_ne_zero` / 定理 `measure_ne_zero`

English:
theorem measure_ne_zero
  statement: [Countable G] [SMulInvariantMeasure G α μ]
  proof: by
  have hc := measure_univ_pos.mpr hμ
  contrapose! hc
  rw [← measure_congr h.iUnion_smul_ae_eq]
  refine le_trans (measure_iUnion_le _) ?_
  simp_rw [measure_smul, hc, tsum_zero, le_refl]

@[to_additive]

中文:
定理 measure_ne_zero
  结论: [可数 G] [标量乘不变测度 G α μ]
  证明: by
  have hc := measure_univ_pos.mpr hμ
  contrapose! hc
  rw [← measure_congr h.iUnion_smul_ae_eq]
  refine le_trans (measure_iUnion_le _) ?_
  simp_rw [measure_smul, hc, tsum_zero, le_refl]

@[to_additive]

Depends on / 依赖: contrapose, h.iUnion_smul_ae_eq, iUnion_smul_ae_eq, le_refl, le_trans, measure_congr, measure_iUnion_le, measure_smul, measure_univ_pos, measure_univ_pos.mpr, simp_rw, tsum_zero
-/
theorem measure_ne_zero [Countable G] [SMulInvariantMeasure G α μ]
    (hμ : μ != 0) (h : IsFundamentalDomain G s μ) : μ s != 0 := by
  have hc := measure_univ_pos.mpr hμ
  contrapose! hc
  rw [← measure_congr h.iUnion_smul_ae_eq]
  refine le_trans (measure_iUnion_le _) ?_
  simp_rw [measure_smul, hc, tsum_zero, le_refl]

@[to_additive]
/--
theorem `mono` / 定理 `mono`

English:
theorem mono
  given: (h : IsFundamentalDomain G s μ) {ν : Measure α} (hle : ν ≪ μ)
  proof: ⟨h.1.mono_ac hle, hle h.2, h.aedisjoint.mono fun _ _ h => hle h⟩

@[to_additive]

中文:
定理 mono
  条件: (h : 是FundamentalDomain G s μ) {ν : 测度 α} (hle : ν ≪ μ)
  证明: ⟨h.1.mono_ac hle, hle h.2, h.aedisjoint.mono fun _ _ h => hle h⟩

@[to_additive]

Depends on / 依赖: aedisjoint, h.aedisjoint.mono, mono_ac
-/
theorem mono (h : IsFundamentalDomain G s μ) {ν : Measure α} (hle : ν ≪ μ) :
    IsFundamentalDomain G s ν :=
  ⟨h.1.mono_ac hle, hle h.2, h.aedisjoint.mono fun _ _ h => hle h⟩

@[to_additive]
/--
theorem `preimage_of_equiv` / 定理 `preimage_of_equiv`

English:
theorem preimage_of_equiv
  statement: {ν : Measure β} (h : IsFundamentalDomain G s μ) {f : β -> α}
  proof: h.nullMeasurableSet.preimage hf
  ae_covers := (hf.ae h.ae_covers).mono fun x ⟨g, hg⟩ => ⟨e g, by rwa [mem_preimage, hef g x]⟩
  aedisjoint a b hab := by
    lift e to G ≃ H using he
    have : (e.symm a⁻¹)⁻¹ != (e.symm b⁻¹)⁻¹ := by simp [hab]
    have := (h.aedisjoint this).preimage hf
    simp only [Semiconj] at hef
    simpa only [onFun, ← preimage_smul_inv, preimage_preimage, ← hef, e.apply_symm_apply, inv_inv]
      using this

@[to_additive]

中文:
定理 preimage_of_equiv
  结论: {ν : 测度 β} (h : 是FundamentalDomain G s μ) {f : β -> α}
  证明: h.nullMeasurableSet.preimage hf
  ae_covers := (hf.ae h.ae_covers).mono fun x ⟨g, hg⟩ => ⟨e g, by rwa [mem_preimage, hef g x]⟩
  aedisjoint a b hab := by
    lift e to G ≃ H using he
    have : (e.symm a⁻¹)⁻¹ != (e.symm b⁻¹)⁻¹ := by simp [hab]
    have := (h.aedisjoint this).preimage hf
    simp only [Semiconj] at hef
    simpa only [onFun, ← preimage_smul_inv, preimage_preimage, ← hef, e.apply_symm_apply, inv_inv]
      using this

@[to_additive]

Depends on / 依赖: h.nullMeasurableSet.preimage, nullMeasurableSet, preimage
-/
theorem preimage_of_equiv {ν : Measure β} (h : IsFundamentalDomain G s μ) {f : β -> α}
    (hf : QuasiMeasurePreserving f ν μ) {e : G -> H} (he : Bijective e)
    (hef : forall g, Semiconj f (e g • ·) (g • ·)) : IsFundamentalDomain H (f ⁻¹' s) ν where
  nullMeasurableSet := h.nullMeasurableSet.preimage hf
  ae_covers := (hf.ae h.ae_covers).mono fun x ⟨g, hg⟩ => ⟨e g, by rwa [mem_preimage, hef g x]⟩
  aedisjoint a b hab := by
    lift e to G ≃ H using he
    have : (e.symm a⁻¹)⁻¹ != (e.symm b⁻¹)⁻¹ := by simp [hab]
    have := (h.aedisjoint this).preimage hf
    simp only [Semiconj] at hef
    simpa only [onFun, ← preimage_smul_inv, preimage_preimage, ← hef, e.apply_symm_apply, inv_inv]
      using this

@[to_additive]
/--
theorem `image_of_equiv` / 定理 `image_of_equiv`

English:
theorem image_of_equiv
  statement: {ν : Measure β} (h : IsFundamentalDomain G s μ) (f : α ≃ β)
  proof: by
  rw [f.image_eq_preimage_symm]
  refine h.preimage_of_equiv hf e.symm.bijective fun g x => ?_
  rcases f.surjective x with ⟨x, rfl⟩
  rw [← hef _ _]; rw [f.symm_apply_apply]; rw [f.symm_apply_apply]; rw [e.apply_symm_apply]

@[to_additive]

中文:
定理 image_of_equiv
  结论: {ν : 测度 β} (h : 是FundamentalDomain G s μ) (f : α ≃ β)
  证明: by
  rw [f.image_eq_preimage_symm]
  refine h.preimage_of_equiv hf e.symm.bijective fun g x => ?_
  rcases f.surjective x with ⟨x, rfl⟩
  rw [← hef _ _]; rw [f.symm_apply_apply]; rw [f.symm_apply_apply]; rw [e.apply_symm_apply]

@[to_additive]

Depends on / 依赖: apply_symm_apply, bijective, e.apply_symm_apply, e.symm.bijective, f.image_eq_preimage_symm, f.surjective, f.symm_apply_apply, h.preimage_of_equiv, image_eq_preimage_symm, preimage_of_equiv, surjective, symm_apply_apply
-/
theorem image_of_equiv {ν : Measure β} (h : IsFundamentalDomain G s μ) (f : α ≃ β)
    (hf : QuasiMeasurePreserving f.symm ν μ) (e : H ≃ G)
    (hef : forall g, Semiconj f (e g • ·) (g • ·)) : IsFundamentalDomain H (f '' s) ν := by
  rw [f.image_eq_preimage_symm]
  refine h.preimage_of_equiv hf e.symm.bijective fun g x => ?_
  rcases f.surjective x with ⟨x, rfl⟩
  rw [← hef _ _]; rw [f.symm_apply_apply]; rw [f.symm_apply_apply]; rw [e.apply_symm_apply]

@[to_additive]
/--
theorem `pairwise_aedisjoint_of_ac` / 定理 `pairwise_aedisjoint_of_ac`

English:
theorem pairwise_aedisjoint_of_ac
  given: {ν} (h : IsFundamentalDomain G s μ) (hν : ν ≪ μ)
  proof: h.aedisjoint.mono fun _ _ H => hν H

@[to_additive]

中文:
定理 pairwise_aedisjoint_of_ac
  条件: {ν} (h : 是FundamentalDomain G s μ) (hν : ν ≪ μ)
  证明: h.aedisjoint.mono fun _ _ H => hν H

@[to_additive]

Depends on / 依赖: aedisjoint, h.aedisjoint.mono
-/
theorem pairwise_aedisjoint_of_ac {ν} (h : IsFundamentalDomain G s μ) (hν : ν ≪ μ) :
    Pairwise fun g₁ g₂ : G => AEDisjoint ν (g₁ • s) (g₂ • s) :=
  h.aedisjoint.mono fun _ _ H => hν H

@[to_additive]
/--
theorem `smul_of_comm` / 定理 `smul_of_comm`

English:
theorem smul_of_comm
  statement: {G' : Type*} [Group G'] [MulAction G' α]
  proof: h.image_of_equiv (MulAction.toPerm g) (measurePreserving_smul _ _).quasiMeasurePreserving
(Equiv.refl _) smul_comm g

中文:
定理 smul_of_comm
  结论: {G' : 类型} [群 G'] [乘法作用 G' α]
  证明: h.image_of_equiv (MulAction.toPerm g) (measurePreserving_smul _ _).quasiMeasurePreserving
(Equiv.refl _) smul_comm g

Depends on / 依赖: Equiv.refl, MulAction, MulAction.toPerm, h.image_of_equiv, image_of_equiv, measurePreserving_smul, quasiMeasurePreserving, smul_comm, toPerm
-/
theorem smul_of_comm {G' : Type*} [Group G'] [MulAction G' α]
    [MeasurableConstSMul G' α] [SMulInvariantMeasure G' α μ] [SMulCommClass G' G α]
    (h : IsFundamentalDomain G s μ) (g : G') : IsFundamentalDomain G (g • s) μ :=
  h.image_of_equiv (MulAction.toPerm g) (measurePreserving_smul _ _).quasiMeasurePreserving
(Equiv.refl _) smul_comm g

variable [MeasurableConstSMul G α] [SMulInvariantMeasure G α μ]

@[to_additive]
/--
theorem `nullMeasurableSet_smul` / 定理 `nullMeasurableSet_smul`

English:
theorem nullMeasurableSet_smul
  given: (h : IsFundamentalDomain G s μ) (g : G)
  proof: h.nullMeasurableSet.smul g

@[to_additive]

中文:
定理 nullMeasurableSet_smul
  条件: (h : 是FundamentalDomain G s μ) (g : G)
  证明: h.nullMeasurableSet.smul g

@[to_additive]

Depends on / 依赖: h.nullMeasurableSet.smul, nullMeasurableSet
-/
theorem nullMeasurableSet_smul (h : IsFundamentalDomain G s μ) (g : G) :
    NullMeasurableSet (g • s) μ :=
  h.nullMeasurableSet.smul g

@[to_additive]
/--
theorem `restrict_restrict` / 定理 `restrict_restrict`

English:
theorem restrict_restrict
  given: (h : IsFundamentalDomain G s μ) (g : G) (t : Set α)
  proof: restrict_restrict₀ ((h.nullMeasurableSet_smul g).mono restrict_le_self)

@[to_additive]

中文:
定理 restrict_restrict
  条件: (h : 是FundamentalDomain G s μ) (g : G) (t : 集合 α)
  证明: restrict_restrict₀ ((h.nullMeasurableSet_smul g).mono restrict_le_self)

@[to_additive]

Depends on / 依赖: h.nullMeasurableSet_smul, nullMeasurableSet_smul, restrict_le_self
-/
theorem restrict_restrict (h : IsFundamentalDomain G s μ) (g : G) (t : Set α) :
    (μ.restrict t).restrict (g • s) = μ.restrict (g • s inter t) :=
  restrict_restrict₀ ((h.nullMeasurableSet_smul g).mono restrict_le_self)

@[to_additive]
/--
theorem `smul` / 定理 `smul`

English:
theorem smul
  given: (h : IsFundamentalDomain G s μ) (g : G)
  statement: IsFundamentalDomain G (g • s) μ
  proof: h.image_of_equiv (MulAction.toPerm g) (measurePreserving_smul _ _).quasiMeasurePreserving
    ⟨fun g' => g⁻¹ * g' * g, fun g' => g * g' * g⁻¹, fun g' => by simp [mul_assoc], fun g' => by
      simp [mul_assoc]⟩
    fun g' x => by simp [smul_smul, mul_assoc]

中文:
定理 smul
  条件: (h : 是FundamentalDomain G s μ) (g : G)
  结论: 是FundamentalDomain G (g • s) μ
  证明: h.image_of_equiv (MulAction.toPerm g) (measurePreserving_smul _ _).quasiMeasurePreserving
    ⟨fun g' => g⁻¹ * g' * g, fun g' => g * g' * g⁻¹, fun g' => by simp [mul_assoc], fun g' => by
      simp [mul_assoc]⟩
    fun g' x => by simp [smul_smul, mul_assoc]

Depends on / 依赖: MulAction, MulAction.toPerm, h.image_of_equiv, image_of_equiv, measurePreserving_smul, mul_assoc, quasiMeasurePreserving, smul_smul, toPerm
-/
theorem smul (h : IsFundamentalDomain G s μ) (g : G) : IsFundamentalDomain G (g • s) μ :=
  h.image_of_equiv (MulAction.toPerm g) (measurePreserving_smul _ _).quasiMeasurePreserving
    ⟨fun g' => g⁻¹ * g' * g, fun g' => g * g' * g⁻¹, fun g' => by simp [mul_assoc], fun g' => by
      simp [mul_assoc]⟩
    fun g' x => by simp [smul_smul, mul_assoc]

variable [Countable G] {ν : Measure α}

@[to_additive]
/--
theorem `sum_restrict_of_ac` / 定理 `sum_restrict_of_ac`

English:
theorem sum_restrict_of_ac
  given: (h : IsFundamentalDomain G s μ) (hν : ν ≪ μ)
  proof: by
  rw [← restrict_iUnion_ae (h.aedisjoint.mono fun i j h => hν h) fun g =>
      (h.nullMeasurableSet_smul g).mono_ac hν]; rw [restrict_congr_set (hν h.iUnion_smul_ae_eq)]; rw [restrict_univ]

@[to_additive]

中文:
定理 sum_restrict_of_ac
  条件: (h : 是FundamentalDomain G s μ) (hν : ν ≪ μ)
  证明: by
  rw [← restrict_iUnion_ae (h.aedisjoint.mono fun i j h => hν h) fun g =>
      (h.nullMeasurableSet_smul g).mono_ac hν]; rw [restrict_congr_set (hν h.iUnion_smul_ae_eq)]; rw [restrict_univ]

@[to_additive]

Depends on / 依赖: aedisjoint, h.aedisjoint.mono, h.iUnion_smul_ae_eq, h.nullMeasurableSet_smul, iUnion_smul_ae_eq, mono_ac, nullMeasurableSet_smul, restrict_congr_set, restrict_iUnion_ae, restrict_univ
-/
theorem sum_restrict_of_ac (h : IsFundamentalDomain G s μ) (hν : ν ≪ μ) :
    (sum fun g : G => ν.restrict (g • s)) = ν := by
  rw [← restrict_iUnion_ae (h.aedisjoint.mono fun i j h => hν h) fun g =>
      (h.nullMeasurableSet_smul g).mono_ac hν]; rw [restrict_congr_set (hν h.iUnion_smul_ae_eq)]; rw [restrict_univ]

@[to_additive]
/--
theorem `lintegral_eq_tsum_of_ac` / 定理 `lintegral_eq_tsum_of_ac`

English:
theorem lintegral_eq_tsum_of_ac
  given: (h : IsFundamentalDomain G s μ) (hν : ν ≪ μ) (f : α -> Real>=0∞)
  proof: by
  rw [← lintegral_sum_measure]; rw [h.sum_restrict_of_ac hν]

@[to_additive]

中文:
定理 lintegral_eq_tsum_of_ac
  条件: (h : 是FundamentalDomain G s μ) (hν : ν ≪ μ) (f : α -> 实数>=0∞)
  证明: by
  rw [← lintegral_sum_measure]; rw [h.sum_restrict_of_ac hν]

@[to_additive]

Depends on / 依赖: h.sum_restrict_of_ac, lintegral_sum_measure, sum_restrict_of_ac
-/
theorem lintegral_eq_tsum_of_ac (h : IsFundamentalDomain G s μ) (hν : ν ≪ μ) (f : α -> Real>=0∞) :
    ∫⁻ x, f x ∂ν = ∑' g : G, ∫⁻ x in g • s, f x ∂ν := by
  rw [← lintegral_sum_measure]; rw [h.sum_restrict_of_ac hν]

@[to_additive]
/--
theorem `sum_restrict` / 定理 `sum_restrict`

English:
theorem sum_restrict
  given: (h : IsFundamentalDomain G s μ)
  statement: (sum fun g : G => μ.restrict (g • s)) = μ
  proof: h.sum_restrict_of_ac (refl _)

@[to_additive]

中文:
定理 sum_restrict
  条件: (h : 是FundamentalDomain G s μ)
  结论: (求和 fun g : G => μ.restrict (g • s)) = μ
  证明: h.sum_restrict_of_ac (refl _)

@[to_additive]

Depends on / 依赖: h.sum_restrict_of_ac, sum_restrict_of_ac
-/
theorem sum_restrict (h : IsFundamentalDomain G s μ) : (sum fun g : G => μ.restrict (g • s)) = μ :=
  h.sum_restrict_of_ac (refl _)

@[to_additive]
/--
theorem `lintegral_eq_tsum` / 定理 `lintegral_eq_tsum`

English:
theorem lintegral_eq_tsum
  given: (h : IsFundamentalDomain G s μ) (f : α -> Real>=0∞)
  proof: h.lintegral_eq_tsum_of_ac (refl _) f

@[to_additive]

中文:
定理 lintegral_eq_tsum
  条件: (h : 是FundamentalDomain G s μ) (f : α -> 实数>=0∞)
  证明: h.lintegral_eq_tsum_of_ac (refl _) f

@[to_additive]

Depends on / 依赖: h.lintegral_eq_tsum_of_ac, lintegral_eq_tsum_of_ac
-/
theorem lintegral_eq_tsum (h : IsFundamentalDomain G s μ) (f : α -> Real>=0∞) :
    ∫⁻ x, f x ∂μ = ∑' g : G, ∫⁻ x in g • s, f x ∂μ :=
  h.lintegral_eq_tsum_of_ac (refl _) f

@[to_additive]
/--
theorem `lintegral_eq_tsum'` / 定理 `lintegral_eq_tsum'`

English:
theorem lintegral_eq_tsum'
  given: (h : IsFundamentalDomain G s μ) (f : α -> Real>=0∞)
  proof: calc
    ∫⁻ x, f x ∂μ = ∑' g : G, ∫⁻ x in g • s, f x ∂μ := h.lintegral_eq_tsum f
    _ = ∑' g : G, ∫⁻ x in g⁻¹ • s, f x ∂μ := ((Equiv.inv G).tsum_eq _).symm
_ = ∑' g : G, ∫⁻ x in s, f (g⁻¹ • x) ∂μ := tsum_congr fun g => Eq.symm
      (measurePreserving_smul g⁻¹ μ).setLIntegral_comp_emb (measurableEmbedding_const_smul _) _ _

中文:
定理 lintegral_eq_tsum'
  条件: (h : 是FundamentalDomain G s μ) (f : α -> 实数>=0∞)
  证明: calc
    ∫⁻ x, f x ∂μ = ∑' g : G, ∫⁻ x in g • s, f x ∂μ := h.lintegral_eq_tsum f
    _ = ∑' g : G, ∫⁻ x in g⁻¹ • s, f x ∂μ := ((Equiv.inv G).tsum_eq _).symm
_ = ∑' g : G, ∫⁻ x in s, f (g⁻¹ • x) ∂μ := tsum_congr fun g => Eq.symm
      (measurePreserving_smul g⁻¹ μ).setLIntegral_comp_emb (measurableEmbedding_const_smul _) _ _

Depends on / 依赖: Eq.symm, Equiv.inv, h.lintegral_eq_tsum, lintegral_eq_tsum, measurableEmbedding_const_smul, measurePreserving_smul, setLIntegral_comp_emb, tsum_congr, tsum_eq
-/
theorem lintegral_eq_tsum' (h : IsFundamentalDomain G s μ) (f : α -> Real>=0∞) :
    ∫⁻ x, f x ∂μ = ∑' g : G, ∫⁻ x in s, f (g⁻¹ • x) ∂μ :=
  calc
    ∫⁻ x, f x ∂μ = ∑' g : G, ∫⁻ x in g • s, f x ∂μ := h.lintegral_eq_tsum f
    _ = ∑' g : G, ∫⁻ x in g⁻¹ • s, f x ∂μ := ((Equiv.inv G).tsum_eq _).symm
_ = ∑' g : G, ∫⁻ x in s, f (g⁻¹ • x) ∂μ := tsum_congr fun g => Eq.symm
      (measurePreserving_smul g⁻¹ μ).setLIntegral_comp_emb (measurableEmbedding_const_smul _) _ _

/--
lemma `lintegral_eq_tsum''` / 引理 `lintegral_eq_tsum''`

English:
lemma lintegral_eq_tsum''
  given: (h : IsFundamentalDomain G s μ) (f : α -> Real>=0∞)
  proof: (lintegral_eq_tsum' h f).trans ((Equiv.inv G).tsum_eq (fun g => ∫⁻ (x : α) in s, f (g • x) ∂μ))

@[to_additive]

中文:
引理 lintegral_eq_tsum''
  条件: (h : 是FundamentalDomain G s μ) (f : α -> 实数>=0∞)
  证明: (lintegral_eq_tsum' h f).trans ((Equiv.inv G).tsum_eq (fun g => ∫⁻ (x : α) in s, f (g • x) ∂μ))

@[to_additive]
-/
@[to_additive] lemma lintegral_eq_tsum'' (h : IsFundamentalDomain G s μ) (f : α -> Real>=0∞) :
    ∫⁻ x, f x ∂μ = ∑' g : G, ∫⁻ x in s, f (g • x) ∂μ :=
  (lintegral_eq_tsum' h f).trans ((Equiv.inv G).tsum_eq (fun g => ∫⁻ (x : α) in s, f (g • x) ∂μ))

@[to_additive]
/--
theorem `setLIntegral_eq_tsum` / 定理 `setLIntegral_eq_tsum`

English:
theorem setLIntegral_eq_tsum
  given: (h : IsFundamentalDomain G s μ) (f : α -> Real>=0∞) (t : Set α)
  proof: calc
    ∫⁻ x in t, f x ∂μ = ∑' g : G, ∫⁻ x in g • s, f x ∂μ.restrict t :=
      h.lintegral_eq_tsum_of_ac restrict_le_self.absolutelyContinuous _
    _ = ∑' g : G, ∫⁻ x in t inter g • s, f x ∂μ := by simp only [h.restrict_restrict, inter_comm]

@[to_additive]

中文:
定理 setL整数egral_eq_tsum
  条件: (h : 是FundamentalDomain G s μ) (f : α -> 实数>=0∞) (t : 集合 α)
  证明: calc
    ∫⁻ x in t, f x ∂μ = ∑' g : G, ∫⁻ x in g • s, f x ∂μ.restrict t :=
      h.lintegral_eq_tsum_of_ac restrict_le_self.absolutelyContinuous _
    _ = ∑' g : G, ∫⁻ x in t inter g • s, f x ∂μ := by simp only [h.restrict_restrict, inter_comm]

@[to_additive]

Depends on / 依赖: absolutelyContinuous, h.lintegral_eq_tsum_of_ac, h.restrict_restrict, inter_comm, lintegral_eq_tsum_of_ac, restrict, restrict_le_self, restrict_le_self.absolutelyContinuous, restrict_restrict
-/
theorem setLIntegral_eq_tsum (h : IsFundamentalDomain G s μ) (f : α -> Real>=0∞) (t : Set α) :
    ∫⁻ x in t, f x ∂μ = ∑' g : G, ∫⁻ x in t inter g • s, f x ∂μ :=
  calc
    ∫⁻ x in t, f x ∂μ = ∑' g : G, ∫⁻ x in g • s, f x ∂μ.restrict t :=
      h.lintegral_eq_tsum_of_ac restrict_le_self.absolutelyContinuous _
    _ = ∑' g : G, ∫⁻ x in t inter g • s, f x ∂μ := by simp only [h.restrict_restrict, inter_comm]

@[to_additive]
/--
theorem `setLIntegral_eq_tsum'` / 定理 `setLIntegral_eq_tsum'`

English:
theorem setLIntegral_eq_tsum'
  given: (h : IsFundamentalDomain G s μ) (f : α -> Real>=0∞) (t : Set α)
  proof: calc
    ∫⁻ x in t, f x ∂μ = ∑' g : G, ∫⁻ x in t inter g • s, f x ∂μ := h.setLIntegral_eq_tsum f t
    _ = ∑' g : G, ∫⁻ x in t inter g⁻¹ • s, f x ∂μ := ((Equiv.inv G).tsum_eq _).symm
    _ = ∑' g : G, ∫⁻ x in g⁻¹ • (g • t inter s), f x ∂μ := by simp only [smul_set_inter, inv_smul_smul]
_ = ∑' g : G, ∫⁻ x in g • t inter s, f (g⁻¹ • x) ∂μ := tsum_congr fun g => Eq.symm
      (measurePreserving_smul g⁻¹ μ).setLIntegral_comp_emb (measurableEmbedding_const_smul _) _ _

@[to_additive]

中文:
定理 setL整数egral_eq_tsum'
  条件: (h : 是FundamentalDomain G s μ) (f : α -> 实数>=0∞) (t : 集合 α)
  证明: calc
    ∫⁻ x in t, f x ∂μ = ∑' g : G, ∫⁻ x in t inter g • s, f x ∂μ := h.setLIntegral_eq_tsum f t
    _ = ∑' g : G, ∫⁻ x in t inter g⁻¹ • s, f x ∂μ := ((Equiv.inv G).tsum_eq _).symm
    _ = ∑' g : G, ∫⁻ x in g⁻¹ • (g • t inter s), f x ∂μ := by simp only [smul_set_inter, inv_smul_smul]
_ = ∑' g : G, ∫⁻ x in g • t inter s, f (g⁻¹ • x) ∂μ := tsum_congr fun g => Eq.symm
      (measurePreserving_smul g⁻¹ μ).setLIntegral_comp_emb (measurableEmbedding_const_smul _) _ _

@[to_additive]

Depends on / 依赖: Eq.symm, Equiv.inv, h.setLIntegral_eq_tsum, inv_smul_smul, measurableEmbedding_const_smul, measurePreserving_smul, setLIntegral_comp_emb, setLIntegral_eq_tsum, smul_set_inter, tsum_congr, tsum_eq
-/
theorem setLIntegral_eq_tsum' (h : IsFundamentalDomain G s μ) (f : α -> Real>=0∞) (t : Set α) :
    ∫⁻ x in t, f x ∂μ = ∑' g : G, ∫⁻ x in g • t inter s, f (g⁻¹ • x) ∂μ :=
  calc
    ∫⁻ x in t, f x ∂μ = ∑' g : G, ∫⁻ x in t inter g • s, f x ∂μ := h.setLIntegral_eq_tsum f t
    _ = ∑' g : G, ∫⁻ x in t inter g⁻¹ • s, f x ∂μ := ((Equiv.inv G).tsum_eq _).symm
    _ = ∑' g : G, ∫⁻ x in g⁻¹ • (g • t inter s), f x ∂μ := by simp only [smul_set_inter, inv_smul_smul]
_ = ∑' g : G, ∫⁻ x in g • t inter s, f (g⁻¹ • x) ∂μ := tsum_congr fun g => Eq.symm
      (measurePreserving_smul g⁻¹ μ).setLIntegral_comp_emb (measurableEmbedding_const_smul _) _ _

@[to_additive]
/--
theorem `measure_eq_tsum_of_ac` / 定理 `measure_eq_tsum_of_ac`

English:
theorem measure_eq_tsum_of_ac
  given: (h : IsFundamentalDomain G s μ) (hν : ν ≪ μ) (t : Set α)
  proof: by
  have H : ν.restrict t ≪ μ := Measure.restrict_le_self.absolutelyContinuous.trans hν
  simpa only [setLIntegral_one, Pi.one_def,
    Measure.restrict_apply₀ ((h.nullMeasurableSet_smul _).mono_ac H), inter_comm] using
    h.lintegral_eq_tsum_of_ac H 1

@[to_additive]

中文:
定理 measure_eq_tsum_of_ac
  条件: (h : 是FundamentalDomain G s μ) (hν : ν ≪ μ) (t : 集合 α)
  证明: by
  have H : ν.restrict t ≪ μ := Measure.restrict_le_self.absolutelyContinuous.trans hν
  simpa only [setLIntegral_one, Pi.one_def,
    Measure.restrict_apply₀ ((h.nullMeasurableSet_smul _).mono_ac H), inter_comm] using
    h.lintegral_eq_tsum_of_ac H 1

@[to_additive]

Depends on / 依赖: Measure, Measure.restrict_apply, Measure.restrict_le_self.absolutelyContinuous.trans, Pi.one_def, absolutelyContinuous, h.lintegral_eq_tsum_of_ac, h.nullMeasurableSet_smul, inter_comm, lintegral_eq_tsum_of_ac, mono_ac, nullMeasurableSet_smul, one_def, restrict, restrict_le_self, setLIntegral_one
-/
theorem measure_eq_tsum_of_ac (h : IsFundamentalDomain G s μ) (hν : ν ≪ μ) (t : Set α) :
    ν t = ∑' g : G, ν (t inter g • s) := by
  have H : ν.restrict t ≪ μ := Measure.restrict_le_self.absolutelyContinuous.trans hν
  simpa only [setLIntegral_one, Pi.one_def,
    Measure.restrict_apply₀ ((h.nullMeasurableSet_smul _).mono_ac H), inter_comm] using
    h.lintegral_eq_tsum_of_ac H 1

@[to_additive]
/--
theorem `measure_eq_tsum'` / 定理 `measure_eq_tsum'`

English:
theorem measure_eq_tsum'
  given: (h : IsFundamentalDomain G s μ) (t : Set α)
  proof: h.measure_eq_tsum_of_ac AbsolutelyContinuous.rfl t

@[to_additive]

中文:
定理 measure_eq_tsum'
  条件: (h : 是FundamentalDomain G s μ) (t : 集合 α)
  证明: h.measure_eq_tsum_of_ac AbsolutelyContinuous.rfl t

@[to_additive]

Depends on / 依赖: AbsolutelyContinuous, AbsolutelyContinuous.rfl, h.measure_eq_tsum_of_ac, measure_eq_tsum_of_ac
-/
theorem measure_eq_tsum' (h : IsFundamentalDomain G s μ) (t : Set α) :
    μ t = ∑' g : G, μ (t inter g • s) :=
  h.measure_eq_tsum_of_ac AbsolutelyContinuous.rfl t

@[to_additive]
/--
theorem `measure_eq_tsum` / 定理 `measure_eq_tsum`

English:
theorem measure_eq_tsum
  given: (h : IsFundamentalDomain G s μ) (t : Set α)
  proof: by
  simpa only [setLIntegral_one] using h.setLIntegral_eq_tsum' (fun _ => 1) t

@[to_additive]

中文:
定理 measure_eq_tsum
  条件: (h : 是FundamentalDomain G s μ) (t : 集合 α)
  证明: by
  simpa only [setLIntegral_one] using h.setLIntegral_eq_tsum' (fun _ => 1) t

@[to_additive]

Depends on / 依赖: h.setLIntegral_eq_tsum, setLIntegral_eq_tsum, setLIntegral_one
-/
theorem measure_eq_tsum (h : IsFundamentalDomain G s μ) (t : Set α) :
    μ t = ∑' g : G, μ (g • t inter s) := by
  simpa only [setLIntegral_one] using h.setLIntegral_eq_tsum' (fun _ => 1) t

@[to_additive]
/--
theorem `measure_zero_of_invariant` / 定理 `measure_zero_of_invariant`

English:
theorem measure_zero_of_invariant
  statement: (h : IsFundamentalDomain G s μ) (t : Set α)
  proof: by
  rw [measure_eq_tsum h]; simp [ht, hts]

中文:
定理 measure_zero_of_invariant
  结论: (h : 是FundamentalDomain G s μ) (t : 集合 α)
  证明: by
  rw [measure_eq_tsum h]; simp [ht, hts]

Depends on / 依赖: measure_eq_tsum
-/
theorem measure_zero_of_invariant (h : IsFundamentalDomain G s μ) (t : Set α)
    (ht : forall g : G, g • t = t) (hts : μ (t inter s) = 0) : μ t = 0 := by
  rw [measure_eq_tsum h]; simp [ht, hts]

/-- Given a measure space with an action of a finite group `G`, the measure of any `G`-invariant set
is determined by the measure of its intersection with a fundamental domain for the action of `G`. -/
@[to_additive measure_eq_card_smul_of_vadd_ae_eq_self /-- Given a measure space with an action of a
  finite additive group `G`, the measure of any `G`-invariant set is determined by the measure of
  its intersection with a fundamental domain for the action of `G`. -/]
/--
theorem `measure_eq_card_smul_of_smul_ae_eq_self` / 定理 `measure_eq_card_smul_of_smul_ae_eq_self`

English:
theorem measure_eq_card_smul_of_smul_ae_eq_self
  statement: [Finite G] (h : IsFundamentalDomain G s μ)
  proof: by
  have : Fintype G := Fintype.ofFinite G
  rw [h.measure_eq_tsum]
  replace ht : forall g : G, (g • t inter s : Set α) =ᵐ[μ] (t inter s : Set α) := fun g =>
    ae_eq_set_inter (ht g) (ae_eq_refl s)
  simp_rw [measure_congr (ht _), tsum_fintype, Finset.sum_const, Nat.card_eq_fintype_card,
    Finset.card_univ]

@[to_additive]

中文:
定理 measure_eq_card_smul_of_smul_ae_eq_self
  结论: [有限 G] (h : 是FundamentalDomain G s μ)
  证明: by
  have : Fintype G := Fintype.ofFinite G
  rw [h.measure_eq_tsum]
  replace ht : forall g : G, (g • t inter s : Set α) =ᵐ[μ] (t inter s : Set α) := fun g =>
    ae_eq_set_inter (ht g) (ae_eq_refl s)
  simp_rw [measure_congr (ht _), tsum_fintype, Finset.sum_const, Nat.card_eq_fintype_card,
    Finset.card_univ]

@[to_additive]

Depends on / 依赖: Finset, Finset.card_univ, Finset.sum_const, Fintype, Fintype.ofFinite, Nat.card_eq_fintype_card, ae_eq_refl, ae_eq_set_inter, card_eq_fintype_card, card_univ, h.measure_eq_tsum, measure_congr, measure_eq_tsum, ofFinite, replace, simp_rw, sum_const, tsum_fintype
-/
theorem measure_eq_card_smul_of_smul_ae_eq_self [Finite G] (h : IsFundamentalDomain G s μ)
    (t : Set α) (ht : forall g : G, (g • t : Set α) =ᵐ[μ] t) : μ t = Nat.card G • μ (t inter s) := by
  have : Fintype G := Fintype.ofFinite G
  rw [h.measure_eq_tsum]
  replace ht : forall g : G, (g • t inter s : Set α) =ᵐ[μ] (t inter s : Set α) := fun g =>
    ae_eq_set_inter (ht g) (ae_eq_refl s)
  simp_rw [measure_congr (ht _), tsum_fintype, Finset.sum_const, Nat.card_eq_fintype_card,
    Finset.card_univ]

@[to_additive]
/--
theorem `setLIntegral_eq` / 定理 `setLIntegral_eq`

English:
theorem setLIntegral_eq
  statement: (hs : IsFundamentalDomain G s μ) (ht : IsFundamentalDomain G t μ)
  proof: calc
    ∫⁻ x in s, f x ∂μ = ∑' g : G, ∫⁻ x in s inter g • t, f x ∂μ := ht.setLIntegral_eq_tsum _ _
    _ = ∑' g : G, ∫⁻ x in g • t inter s, f (g⁻¹ • x) ∂μ := by simp only [hf, inter_comm]
    _ = ∫⁻ x in t, f x ∂μ := (hs.setLIntegral_eq_tsum' _ _).symm

@[to_additive]

中文:
定理 setL整数egral_eq
  结论: (hs : 是FundamentalDomain G s μ) (ht : 是FundamentalDomain G t μ)
  证明: calc
    ∫⁻ x in s, f x ∂μ = ∑' g : G, ∫⁻ x in s inter g • t, f x ∂μ := ht.setLIntegral_eq_tsum _ _
    _ = ∑' g : G, ∫⁻ x in g • t inter s, f (g⁻¹ • x) ∂μ := by simp only [hf, inter_comm]
    _ = ∫⁻ x in t, f x ∂μ := (hs.setLIntegral_eq_tsum' _ _).symm

@[to_additive]
-/
protected theorem setLIntegral_eq (hs : IsFundamentalDomain G s μ) (ht : IsFundamentalDomain G t μ)
    (f : α -> Real>=0∞) (hf : forall (g : G) (x), f (g • x) = f x) :
    ∫⁻ x in s, f x ∂μ = ∫⁻ x in t, f x ∂μ :=
  calc
    ∫⁻ x in s, f x ∂μ = ∑' g : G, ∫⁻ x in s inter g • t, f x ∂μ := ht.setLIntegral_eq_tsum _ _
    _ = ∑' g : G, ∫⁻ x in g • t inter s, f (g⁻¹ • x) ∂μ := by simp only [hf, inter_comm]
    _ = ∫⁻ x in t, f x ∂μ := (hs.setLIntegral_eq_tsum' _ _).symm

@[to_additive]
/--
theorem `measure_set_eq` / 定理 `measure_set_eq`

English:
theorem measure_set_eq
  statement: (hs : IsFundamentalDomain G s μ) (ht : IsFundamentalDomain G t μ) {A : Set α}
  proof: by
  have : ∫⁻ x in s, A.indicator 1 x ∂μ = ∫⁻ x in t, A.indicator 1 x ∂μ := by
    refine hs.setLIntegral_eq ht (Set.indicator A fun _ => 1) fun g x => ?_
    convert! (Set.indicator_comp_right (g • · : α -> α) (g := fun _ => (1 : Real>=0∞))).symm
    rw [hA g]
  simpa [Measure.restrict_apply hA₀, lintegral_indicator hA₀] using this

中文:
定理 measure_set_eq
  结论: (hs : 是FundamentalDomain G s μ) (ht : 是FundamentalDomain G t μ) {A : 集合 α}
  证明: by
  have : ∫⁻ x in s, A.indicator 1 x ∂μ = ∫⁻ x in t, A.indicator 1 x ∂μ := by
    refine hs.setLIntegral_eq ht (Set.indicator A fun _ => 1) fun g x => ?_
    convert! (Set.indicator_comp_right (g • · : α -> α) (g := fun _ => (1 : Real>=0∞))).symm
    rw [hA g]
  simpa [Measure.restrict_apply hA₀, lintegral_indicator hA₀] using this

Depends on / 依赖: A.indicator, Measure, Measure.restrict_apply, Set.indicator, Set.indicator_comp_right, convert, hs.setLIntegral_eq, indicator, indicator_comp_right, lintegral_indicator, restrict_apply, setLIntegral_eq
-/
theorem measure_set_eq (hs : IsFundamentalDomain G s μ) (ht : IsFundamentalDomain G t μ) {A : Set α}
    (hA₀ : MeasurableSet A) (hA : forall g : G, (fun x => g • x) ⁻¹' A = A) : μ (A inter s) = μ (A inter t) := by
  have : ∫⁻ x in s, A.indicator 1 x ∂μ = ∫⁻ x in t, A.indicator 1 x ∂μ := by
    refine hs.setLIntegral_eq ht (Set.indicator A fun _ => 1) fun g x => ?_
    convert! (Set.indicator_comp_right (g • · : α -> α) (g := fun _ => (1 : Real>=0∞))).symm
    rw [hA g]
  simpa [Measure.restrict_apply hA₀, lintegral_indicator hA₀] using this

/-- If `s` and `t` are two fundamental domains of the same action, then their measures are equal. -/
@[to_additive /-- If `s` and `t` are two fundamental domains of the same action, then their measures
  are equal. -/]
/--
theorem `measure_eq` / 定理 `measure_eq`

English:
theorem measure_eq
  given: (hs : IsFundamentalDomain G s μ) (ht : IsFundamentalDomain G t μ)
  proof: by
  simpa only [setLIntegral_one] using hs.setLIntegral_eq ht (fun _ => 1) fun _ _ => rfl

@[to_additive]

中文:
定理 measure_eq
  条件: (hs : 是FundamentalDomain G s μ) (ht : 是FundamentalDomain G t μ)
  证明: by
  simpa only [setLIntegral_one] using hs.setLIntegral_eq ht (fun _ => 1) fun _ _ => rfl

@[to_additive]
-/
protected theorem measure_eq (hs : IsFundamentalDomain G s μ) (ht : IsFundamentalDomain G t μ) :
    μ s = μ t := by
  simpa only [setLIntegral_one] using hs.setLIntegral_eq ht (fun _ => 1) fun _ _ => rfl

@[to_additive]
/--
theorem `aestronglyMeasurable_on_iff` / 定理 `aestronglyMeasurable_on_iff`

English:
theorem aestronglyMeasurable_on_iff
  statement: {β : Type*} [TopologicalSpace β]
  proof: calc
    AEStronglyMeasurable f (μ.restrict s) ↔
        AEStronglyMeasurable f (Measure.sum fun g : G => μ.restrict (g • t inter s)) := by
      simp only [← ht.restrict_restrict,
        ht.sum_restrict_of_ac restrict_le_self.absolutelyContinuous]
    _ ↔ forall g : G, AEStronglyMeasurable f (μ.restrict (g • (g⁻¹ • s inter t))) := by
      simp only [smul_set_inter, inter_comm, smul_inv_smul, aestronglyMeasurable_sum_measure_iff]
    _ ↔ forall g : G, AEStronglyMeasurable f (μ.restrict (g⁻¹ • (g⁻¹⁻¹ • s inter t))) :=
      inv_surjective.forall
    _ ↔ forall g : G, AEStronglyMeasurable f (μ.restrict (g⁻¹ • (g • s inter t))) := by simp only [inv_inv]
    _ ↔ forall g : G, AEStronglyMeasurable f (μ.restrict (g • s inter t)) := by
      refine forall_congr' fun g => ?_
      have he : MeasurableEmbedding (g⁻¹ • · : α -> α) := measurableEmbedding_const_smul _
      rw [← image_smul]; rw [← ((measurePreserving_smul g⁻¹ μ).restrict_image_emb he
        _).aestronglyMeasurable_comp_iff he]
      simp only [Function.comp_def, hf]
    _ ↔ AEStronglyMeasurable f (μ.restrict t) := by
      simp only [← aestronglyMeasurable_sum_measure_iff, ← hs.restrict_restrict,
        hs.sum_restrict_of_ac restrict_le_self.absolutelyContinuous]

@[to_additive]

中文:
定理 aestronglyMeasurable_on_iff
  结论: {β : 类型} [拓扑空间 β]
  证明: calc
    AEStronglyMeasurable f (μ.restrict s) ↔
        AEStronglyMeasurable f (Measure.sum fun g : G => μ.restrict (g • t inter s)) := by
      simp only [← ht.restrict_restrict,
        ht.sum_restrict_of_ac restrict_le_self.absolutelyContinuous]
    _ ↔ forall g : G, AEStronglyMeasurable f (μ.restrict (g • (g⁻¹ • s inter t))) := by
      simp only [smul_set_inter, inter_comm, smul_inv_smul, aestronglyMeasurable_sum_measure_iff]
    _ ↔ forall g : G, AEStronglyMeasurable f (μ.restrict (g⁻¹ • (g⁻¹⁻¹ • s inter t))) :=
      inv_surjective.forall
    _ ↔ forall g : G, AEStronglyMeasurable f (μ.restrict (g⁻¹ • (g • s inter t))) := by simp only [inv_inv]
    _ ↔ forall g : G, AEStronglyMeasurable f (μ.restrict (g • s inter t)) := by
      refine forall_congr' fun g => ?_
      have he : MeasurableEmbedding (g⁻¹ • · : α -> α) := measurableEmbedding_const_smul _
      rw [← image_smul]; rw [← ((measurePreserving_smul g⁻¹ μ).restrict_image_emb he
        _).aestronglyMeasurable_comp_iff he]
      simp only [Function.comp_def, hf]
    _ ↔ AEStronglyMeasurable f (μ.restrict t) := by
      simp only [← aestronglyMeasurable_sum_measure_iff, ← hs.restrict_restrict,
        hs.sum_restrict_of_ac restrict_le_self.absolutelyContinuous]

@[to_additive]
-/
protected theorem aestronglyMeasurable_on_iff {β : Type*} [TopologicalSpace β]
    [PseudoMetrizableSpace β] (hs : IsFundamentalDomain G s μ) (ht : IsFundamentalDomain G t μ)
    {f : α -> β} (hf : forall (g : G) (x), f (g • x) = f x) :
    AEStronglyMeasurable f (μ.restrict s) ↔ AEStronglyMeasurable f (μ.restrict t) :=
  calc
    AEStronglyMeasurable f (μ.restrict s) ↔
        AEStronglyMeasurable f (Measure.sum fun g : G => μ.restrict (g • t inter s)) := by
      simp only [← ht.restrict_restrict,
        ht.sum_restrict_of_ac restrict_le_self.absolutelyContinuous]
    _ ↔ forall g : G, AEStronglyMeasurable f (μ.restrict (g • (g⁻¹ • s inter t))) := by
      simp only [smul_set_inter, inter_comm, smul_inv_smul, aestronglyMeasurable_sum_measure_iff]
    _ ↔ forall g : G, AEStronglyMeasurable f (μ.restrict (g⁻¹ • (g⁻¹⁻¹ • s inter t))) :=
      inv_surjective.forall
    _ ↔ forall g : G, AEStronglyMeasurable f (μ.restrict (g⁻¹ • (g • s inter t))) := by simp only [inv_inv]
    _ ↔ forall g : G, AEStronglyMeasurable f (μ.restrict (g • s inter t)) := by
      refine forall_congr' fun g => ?_
      have he : MeasurableEmbedding (g⁻¹ • · : α -> α) := measurableEmbedding_const_smul _
      rw [← image_smul]; rw [← ((measurePreserving_smul g⁻¹ μ).restrict_image_emb he
        _).aestronglyMeasurable_comp_iff he]
      simp only [Function.comp_def, hf]
    _ ↔ AEStronglyMeasurable f (μ.restrict t) := by
      simp only [← aestronglyMeasurable_sum_measure_iff, ← hs.restrict_restrict,
        hs.sum_restrict_of_ac restrict_le_self.absolutelyContinuous]

@[to_additive]
/--
theorem `hasFiniteIntegral_on_iff` / 定理 `hasFiniteIntegral_on_iff`

English:
theorem hasFiniteIntegral_on_iff
  statement: (hs : IsFundamentalDomain G s μ)
  proof: by
  dsimp only [HasFiniteIntegral]
  rw [hs.setLIntegral_eq ht]
  intro g x; rw [hf]

@[to_additive]

中文:
定理 hasFinite整数egral_on_iff
  结论: (hs : 是FundamentalDomain G s μ)
  证明: by
  dsimp only [HasFiniteIntegral]
  rw [hs.setLIntegral_eq ht]
  intro g x; rw [hf]

@[to_additive]
-/
protected theorem hasFiniteIntegral_on_iff (hs : IsFundamentalDomain G s μ)
    (ht : IsFundamentalDomain G t μ) {f : α -> E} (hf : forall (g : G) (x), f (g • x) = f x) :
    HasFiniteIntegral f (μ.restrict s) ↔ HasFiniteIntegral f (μ.restrict t) := by
  dsimp only [HasFiniteIntegral]
  rw [hs.setLIntegral_eq ht]
  intro g x; rw [hf]

@[to_additive]
/--
theorem `integrableOn_iff` / 定理 `integrableOn_iff`

English:
theorem integrableOn_iff
  statement: (hs : IsFundamentalDomain G s μ) (ht : IsFundamentalDomain G t μ)
  proof: and_congr (hs.aestronglyMeasurable_on_iff ht hf) (hs.hasFiniteIntegral_on_iff ht hf)

中文:
定理 integrableOn_iff
  结论: (hs : 是FundamentalDomain G s μ) (ht : 是FundamentalDomain G t μ)
  证明: and_congr (hs.aestronglyMeasurable_on_iff ht hf) (hs.hasFiniteIntegral_on_iff ht hf)
-/
protected theorem integrableOn_iff (hs : IsFundamentalDomain G s μ) (ht : IsFundamentalDomain G t μ)
    {f : α -> E} (hf : forall (g : G) (x), f (g • x) = f x) : IntegrableOn f s μ ↔ IntegrableOn f t μ :=
  and_congr (hs.aestronglyMeasurable_on_iff ht hf) (hs.hasFiniteIntegral_on_iff ht hf)

variable [NormedSpace Real E]

@[to_additive]
/--
theorem `integral_eq_tsum_of_ac` / 定理 `integral_eq_tsum_of_ac`

English:
theorem integral_eq_tsum_of_ac
  statement: (h : IsFundamentalDomain G s μ) (hν : ν ≪ μ) (f : α -> E)
  proof: by
  rw [← MeasureTheory.integral_sum_measure]; rw [h.sum_restrict_of_ac hν]
  rw [h.sum_restrict_of_ac hν]
  exact hf

@[to_additive]

中文:
定理 integral_eq_tsum_of_ac
  结论: (h : 是FundamentalDomain G s μ) (hν : ν ≪ μ) (f : α -> E)
  证明: by
  rw [← MeasureTheory.integral_sum_measure]; rw [h.sum_restrict_of_ac hν]
  rw [h.sum_restrict_of_ac hν]
  exact hf

@[to_additive]

Depends on / 依赖: MeasureTheory, MeasureTheory.integral_sum_measure, h.sum_restrict_of_ac, integral_sum_measure, sum_restrict_of_ac
-/
theorem integral_eq_tsum_of_ac (h : IsFundamentalDomain G s μ) (hν : ν ≪ μ) (f : α -> E)
    (hf : Integrable f ν) : ∫ x, f x ∂ν = ∑' g : G, ∫ x in g • s, f x ∂ν := by
  rw [← MeasureTheory.integral_sum_measure]; rw [h.sum_restrict_of_ac hν]
  rw [h.sum_restrict_of_ac hν]
  exact hf

@[to_additive]
/--
theorem `integral_eq_tsum` / 定理 `integral_eq_tsum`

English:
theorem integral_eq_tsum
  given: (h : IsFundamentalDomain G s μ) (f : α -> E) (hf : Integrable f μ)
  proof: integral_eq_tsum_of_ac h (by rfl) f hf

@[to_additive]

中文:
定理 integral_eq_tsum
  条件: (h : 是FundamentalDomain G s μ) (f : α -> E) (hf : 可积 f μ)
  证明: integral_eq_tsum_of_ac h (by rfl) f hf

@[to_additive]

Depends on / 依赖: integral_eq_tsum_of_ac
-/
theorem integral_eq_tsum (h : IsFundamentalDomain G s μ) (f : α -> E) (hf : Integrable f μ) :
    ∫ x, f x ∂μ = ∑' g : G, ∫ x in g • s, f x ∂μ :=
  integral_eq_tsum_of_ac h (by rfl) f hf

@[to_additive]
/--
theorem `integral_eq_tsum'` / 定理 `integral_eq_tsum'`

English:
theorem integral_eq_tsum'
  given: (h : IsFundamentalDomain G s μ) (f : α -> E) (hf : Integrable f μ)
  proof: calc
    ∫ x, f x ∂μ = ∑' g : G, ∫ x in g • s, f x ∂μ := h.integral_eq_tsum f hf
    _ = ∑' g : G, ∫ x in g⁻¹ • s, f x ∂μ := ((Equiv.inv G).tsum_eq _).symm
    _ = ∑' g : G, ∫ x in s, f (g⁻¹ • x) ∂μ := tsum_congr fun g =>
      (measurePreserving_smul g⁻¹ μ).setIntegral_image_emb (measurableEmbedding_const_smul _) _ _

中文:
定理 integral_eq_tsum'
  条件: (h : 是FundamentalDomain G s μ) (f : α -> E) (hf : 可积 f μ)
  证明: calc
    ∫ x, f x ∂μ = ∑' g : G, ∫ x in g • s, f x ∂μ := h.integral_eq_tsum f hf
    _ = ∑' g : G, ∫ x in g⁻¹ • s, f x ∂μ := ((Equiv.inv G).tsum_eq _).symm
    _ = ∑' g : G, ∫ x in s, f (g⁻¹ • x) ∂μ := tsum_congr fun g =>
      (measurePreserving_smul g⁻¹ μ).setIntegral_image_emb (measurableEmbedding_const_smul _) _ _

Depends on / 依赖: Equiv.inv, h.integral_eq_tsum, integral_eq_tsum, measurableEmbedding_const_smul, measurePreserving_smul, setIntegral_image_emb, tsum_congr, tsum_eq
-/
theorem integral_eq_tsum' (h : IsFundamentalDomain G s μ) (f : α -> E) (hf : Integrable f μ) :
    ∫ x, f x ∂μ = ∑' g : G, ∫ x in s, f (g⁻¹ • x) ∂μ :=
  calc
    ∫ x, f x ∂μ = ∑' g : G, ∫ x in g • s, f x ∂μ := h.integral_eq_tsum f hf
    _ = ∑' g : G, ∫ x in g⁻¹ • s, f x ∂μ := ((Equiv.inv G).tsum_eq _).symm
    _ = ∑' g : G, ∫ x in s, f (g⁻¹ • x) ∂μ := tsum_congr fun g =>
      (measurePreserving_smul g⁻¹ μ).setIntegral_image_emb (measurableEmbedding_const_smul _) _ _

/--
lemma `integral_eq_tsum''` / 引理 `integral_eq_tsum''`

English:
lemma integral_eq_tsum''
  statement: (h : IsFundamentalDomain G s μ)
  proof: (integral_eq_tsum' h f hf).trans ((Equiv.inv G).tsum_eq (fun g => ∫ (x : α) in s, f (g • x) ∂μ))

@[to_additive]

中文:
引理 integral_eq_tsum''
  结论: (h : 是FundamentalDomain G s μ)
  证明: (integral_eq_tsum' h f hf).trans ((Equiv.inv G).tsum_eq (fun g => ∫ (x : α) in s, f (g • x) ∂μ))

@[to_additive]
-/
@[to_additive] lemma integral_eq_tsum'' (h : IsFundamentalDomain G s μ)
    (f : α -> E) (hf : Integrable f μ) : ∫ x, f x ∂μ = ∑' g : G, ∫ x in s, f (g • x) ∂μ :=
  (integral_eq_tsum' h f hf).trans ((Equiv.inv G).tsum_eq (fun g => ∫ (x : α) in s, f (g • x) ∂μ))

@[to_additive]
/--
theorem `setIntegral_eq_tsum` / 定理 `setIntegral_eq_tsum`

English:
theorem setIntegral_eq_tsum
  statement: (h : IsFundamentalDomain G s μ) {f : α -> E} {t : Set α}
  proof: calc
    ∫ x in t, f x ∂μ = ∑' g : G, ∫ x in g • s, f x ∂μ.restrict t :=
      h.integral_eq_tsum_of_ac restrict_le_self.absolutelyContinuous f hf
    _ = ∑' g : G, ∫ x in t inter g • s, f x ∂μ := by
      simp only [h.restrict_restrict, inter_comm]

@[to_additive]

中文:
定理 set整数egral_eq_tsum
  结论: (h : 是FundamentalDomain G s μ) {f : α -> E} {t : 集合 α}
  证明: calc
    ∫ x in t, f x ∂μ = ∑' g : G, ∫ x in g • s, f x ∂μ.restrict t :=
      h.integral_eq_tsum_of_ac restrict_le_self.absolutelyContinuous f hf
    _ = ∑' g : G, ∫ x in t inter g • s, f x ∂μ := by
      simp only [h.restrict_restrict, inter_comm]

@[to_additive]

Depends on / 依赖: absolutelyContinuous, h.integral_eq_tsum_of_ac, h.restrict_restrict, integral_eq_tsum_of_ac, inter_comm, restrict, restrict_le_self, restrict_le_self.absolutelyContinuous, restrict_restrict
-/
theorem setIntegral_eq_tsum (h : IsFundamentalDomain G s μ) {f : α -> E} {t : Set α}
    (hf : IntegrableOn f t μ) : ∫ x in t, f x ∂μ = ∑' g : G, ∫ x in t inter g • s, f x ∂μ :=
  calc
    ∫ x in t, f x ∂μ = ∑' g : G, ∫ x in g • s, f x ∂μ.restrict t :=
      h.integral_eq_tsum_of_ac restrict_le_self.absolutelyContinuous f hf
    _ = ∑' g : G, ∫ x in t inter g • s, f x ∂μ := by
      simp only [h.restrict_restrict, inter_comm]

@[to_additive]
/--
theorem `setIntegral_eq_tsum'` / 定理 `setIntegral_eq_tsum'`

English:
theorem setIntegral_eq_tsum'
  statement: (h : IsFundamentalDomain G s μ) {f : α -> E} {t : Set α}
  proof: calc
    ∫ x in t, f x ∂μ = ∑' g : G, ∫ x in t inter g • s, f x ∂μ := h.setIntegral_eq_tsum hf
    _ = ∑' g : G, ∫ x in t inter g⁻¹ • s, f x ∂μ := ((Equiv.inv G).tsum_eq _).symm
    _ = ∑' g : G, ∫ x in g⁻¹ • (g • t inter s), f x ∂μ := by simp only [smul_set_inter, inv_smul_smul]
    _ = ∑' g : G, ∫ x in g • t inter s, f (g⁻¹ • x) ∂μ :=
      tsum_congr fun g =>
        (measurePreserving_smul g⁻¹ μ).setIntegral_image_emb (measurableEmbedding_const_smul _) _ _

@[to_additive]

中文:
定理 set整数egral_eq_tsum'
  结论: (h : 是FundamentalDomain G s μ) {f : α -> E} {t : 集合 α}
  证明: calc
    ∫ x in t, f x ∂μ = ∑' g : G, ∫ x in t inter g • s, f x ∂μ := h.setIntegral_eq_tsum hf
    _ = ∑' g : G, ∫ x in t inter g⁻¹ • s, f x ∂μ := ((Equiv.inv G).tsum_eq _).symm
    _ = ∑' g : G, ∫ x in g⁻¹ • (g • t inter s), f x ∂μ := by simp only [smul_set_inter, inv_smul_smul]
    _ = ∑' g : G, ∫ x in g • t inter s, f (g⁻¹ • x) ∂μ :=
      tsum_congr fun g =>
        (measurePreserving_smul g⁻¹ μ).setIntegral_image_emb (measurableEmbedding_const_smul _) _ _

@[to_additive]

Depends on / 依赖: Equiv.inv, h.setIntegral_eq_tsum, inv_smul_smul, measurableEmbedding_const_smul, measurePreserving_smul, setIntegral_eq_tsum, setIntegral_image_emb, smul_set_inter, tsum_congr, tsum_eq
-/
theorem setIntegral_eq_tsum' (h : IsFundamentalDomain G s μ) {f : α -> E} {t : Set α}
    (hf : IntegrableOn f t μ) : ∫ x in t, f x ∂μ = ∑' g : G, ∫ x in g • t inter s, f (g⁻¹ • x) ∂μ :=
  calc
    ∫ x in t, f x ∂μ = ∑' g : G, ∫ x in t inter g • s, f x ∂μ := h.setIntegral_eq_tsum hf
    _ = ∑' g : G, ∫ x in t inter g⁻¹ • s, f x ∂μ := ((Equiv.inv G).tsum_eq _).symm
    _ = ∑' g : G, ∫ x in g⁻¹ • (g • t inter s), f x ∂μ := by simp only [smul_set_inter, inv_smul_smul]
    _ = ∑' g : G, ∫ x in g • t inter s, f (g⁻¹ • x) ∂μ :=
      tsum_congr fun g =>
        (measurePreserving_smul g⁻¹ μ).setIntegral_image_emb (measurableEmbedding_const_smul _) _ _

@[to_additive]
/--
theorem `setIntegral_eq` / 定理 `setIntegral_eq`

English:
theorem setIntegral_eq
  statement: (hs : IsFundamentalDomain G s μ) (ht : IsFundamentalDomain G t μ)
  proof: by
  by_cases hfs : IntegrableOn f s μ
  · have hft : IntegrableOn f t μ := by rwa [ht.integrableOn_iff hs hf]
    calc
      ∫ x in s, f x ∂μ = ∑' g : G, ∫ x in s inter g • t, f x ∂μ := ht.setIntegral_eq_tsum hfs
      _ = ∑' g : G, ∫ x in g • t inter s, f (g⁻¹ • x) ∂μ := by simp only [hf, inter_comm]
      _ = ∫ x in t, f x ∂μ := (hs.setIntegral_eq_tsum' hft).symm
  · rw [integral_undef hfs, integral_undef]
    rwa [hs.integrableOn_iff ht hf] at hfs

中文:
定理 set整数egral_eq
  结论: (hs : 是FundamentalDomain G s μ) (ht : 是FundamentalDomain G t μ)
  证明: by
  by_cases hfs : IntegrableOn f s μ
  · have hft : IntegrableOn f t μ := by rwa [ht.integrableOn_iff hs hf]
    calc
      ∫ x in s, f x ∂μ = ∑' g : G, ∫ x in s inter g • t, f x ∂μ := ht.setIntegral_eq_tsum hfs
      _ = ∑' g : G, ∫ x in g • t inter s, f (g⁻¹ • x) ∂μ := by simp only [hf, inter_comm]
      _ = ∫ x in t, f x ∂μ := (hs.setIntegral_eq_tsum' hft).symm
  · rw [integral_undef hfs, integral_undef]
    rwa [hs.integrableOn_iff ht hf] at hfs
-/
protected theorem setIntegral_eq (hs : IsFundamentalDomain G s μ) (ht : IsFundamentalDomain G t μ)
    {f : α -> E} (hf : forall (g : G) (x), f (g • x) = f x) : ∫ x in s, f x ∂μ = ∫ x in t, f x ∂μ := by
  by_cases hfs : IntegrableOn f s μ
  · have hft : IntegrableOn f t μ := by rwa [ht.integrableOn_iff hs hf]
    calc
      ∫ x in s, f x ∂μ = ∑' g : G, ∫ x in s inter g • t, f x ∂μ := ht.setIntegral_eq_tsum hfs
      _ = ∑' g : G, ∫ x in g • t inter s, f (g⁻¹ • x) ∂μ := by simp only [hf, inter_comm]
      _ = ∫ x in t, f x ∂μ := (hs.setIntegral_eq_tsum' hft).symm
  · rw [integral_undef hfs, integral_undef]
    rwa [hs.integrableOn_iff ht hf] at hfs

/-- If the action of a countable group `G` admits an invariant measure `μ` with a fundamental domain
`s`, then every null-measurable set `t` such that the sets `g • t ∩ s` are pairwise a.e.-disjoint
has measure at most `μ s`. -/
@[to_additive /-- If the additive action of a countable group `G` admits an invariant measure `μ`
  with a fundamental domain `s`, then every null-measurable set `t` such that the sets `g +ᵥ t ∩ s`
  are pairwise a.e.-disjoint has measure at most `μ s`. -/]
/--
theorem `measure_le_of_pairwise_disjoint` / 定理 `measure_le_of_pairwise_disjoint`

English:
theorem measure_le_of_pairwise_disjoint
  statement: (hs : IsFundamentalDomain G s μ)
  proof: calc
    μ t = ∑' g : G, μ (g • t inter s) := hs.measure_eq_tsum t
_ = μ (⋃ g : G, g • t inter s) := Eq.symm measure_iUnion₀ hd fun _ =>
      (ht.smul _).inter hs.nullMeasurableSet
    _ <= μ s := measure_mono (iUnion_subset fun _ => inter_subset_right)

中文:
定理 measure_le_of_pairwise_disjoint
  结论: (hs : 是FundamentalDomain G s μ)
  证明: calc
    μ t = ∑' g : G, μ (g • t inter s) := hs.measure_eq_tsum t
_ = μ (⋃ g : G, g • t inter s) := Eq.symm measure_iUnion₀ hd fun _ =>
      (ht.smul _).inter hs.nullMeasurableSet
    _ <= μ s := measure_mono (iUnion_subset fun _ => inter_subset_right)

Depends on / 依赖: Eq.symm, hs.measure_eq_tsum, hs.nullMeasurableSet, ht.smul, iUnion_subset, inter_subset_right, measure_eq_tsum, measure_mono, nullMeasurableSet
-/
theorem measure_le_of_pairwise_disjoint (hs : IsFundamentalDomain G s μ)
    (ht : NullMeasurableSet t μ) (hd : Pairwise (AEDisjoint μ on fun g : G => g • t inter s)) :
    μ t <= μ s :=
  calc
    μ t = ∑' g : G, μ (g • t inter s) := hs.measure_eq_tsum t
_ = μ (⋃ g : G, g • t inter s) := Eq.symm measure_iUnion₀ hd fun _ =>
      (ht.smul _).inter hs.nullMeasurableSet
    _ <= μ s := measure_mono (iUnion_subset fun _ => inter_subset_right)

/-- If the action of a countable group `G` admits an invariant measure `μ` with a fundamental domain
`s`, then every null-measurable set `t` of measure strictly greater than `μ s` contains two
points `x y` such that `g • x = y` for some `g ≠ 1`. -/
@[to_additive /-- If the additive action of a countable group `G` admits an invariant measure `μ`
  with a fundamental domain `s`, then every null-measurable set `t` of measure strictly greater than
  `μ s` contains two points `x y` such that `g +ᵥ x = y` for some `g ≠ 0`. -/]
/--
theorem `exists_ne_one_smul_eq` / 定理 `exists_ne_one_smul_eq`

English:
theorem exists_ne_one_smul_eq
  statement: (hs : IsFundamentalDomain G s μ) (htm : NullMeasurableSet t μ)
  proof: by
  contrapose! ht
  refine hs.measure_le_of_pairwise_disjoint htm (Pairwise.aedisjoint fun g₁ g₂ hne => ?_)
  dsimp [Function.onFun]
  refine (Disjoint.inf_left _ ?_).inf_right _
  rw [Set.disjoint_left]
  rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy : g₂ • y = g₁ • x⟩
  refine ht x hx y hy (g₂⁻¹ * g₁) (mt inv_mul_eq_one.1 hne.symm) ?_
  rw [mul_smul]; rw [← hxy]; rw [inv_smul_smul]

中文:
定理 存在_ne_one_smul_eq
  结论: (hs : 是FundamentalDomain G s μ) (htm : NullMeasurableSet t μ)
  证明: by
  contrapose! ht
  refine hs.measure_le_of_pairwise_disjoint htm (Pairwise.aedisjoint fun g₁ g₂ hne => ?_)
  dsimp [Function.onFun]
  refine (Disjoint.inf_left _ ?_).inf_right _
  rw [Set.disjoint_left]
  rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy : g₂ • y = g₁ • x⟩
  refine ht x hx y hy (g₂⁻¹ * g₁) (mt inv_mul_eq_one.1 hne.symm) ?_
  rw [mul_smul]; rw [← hxy]; rw [inv_smul_smul]

Depends on / 依赖: Disjoint, Disjoint.inf_left, Function, Function.onFun, Pairwise, Pairwise.aedisjoint, Set.disjoint_left, aedisjoint, contrapose, disjoint_left, hne.symm, hs.measure_le_of_pairwise_disjoint, inf_left, inf_right, inv_mul_eq_one, inv_smul_smul, measure_le_of_pairwise_disjoint, mul_smul
-/
theorem exists_ne_one_smul_eq (hs : IsFundamentalDomain G s μ) (htm : NullMeasurableSet t μ)
    (ht : μ s < μ t) : exists x in t, exists y in t, exists g, g != (1 : G) ∧ g • x = y := by
  contrapose! ht
  refine hs.measure_le_of_pairwise_disjoint htm (Pairwise.aedisjoint fun g₁ g₂ hne => ?_)
  dsimp [Function.onFun]
  refine (Disjoint.inf_left _ ?_).inf_right _
  rw [Set.disjoint_left]
  rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy : g₂ • y = g₁ • x⟩
  refine ht x hx y hy (g₂⁻¹ * g₁) (mt inv_mul_eq_one.1 hne.symm) ?_
  rw [mul_smul]; rw [← hxy]; rw [inv_smul_smul]

/-- If `f` is invariant under the action of a countable group `G`, and `μ` is a `G`-invariant
  measure with a fundamental domain `s`, then the `essSup` of `f` restricted to `s` is the same as
  that of `f` on all of its domain. -/
@[to_additive /-- If `f` is invariant under the action of a countable additive group `G`, and `μ`
  is a `G`-invariant measure with a fundamental domain `s`, then the `essSup` of `f` restricted to
  `s` is the same as that of `f` on all of its domain. -/]
/--
theorem `essSup_measure_restrict` / 定理 `essSup_measure_restrict`

English:
theorem essSup_measure_restrict
  statement: (hs : IsFundamentalDomain G s μ) {f : α -> Real>=0∞}
  proof: by
  refine le_antisymm (essSup_mono_measure' Measure.restrict_le_self) ?_
  rw [essSup_eq_sInf (μ.restrict s) f]; rw [essSup_eq_sInf μ f]
  refine sInf_le_sInf ?_
  rintro a (ha : (μ.restrict s) {x : α | a < f x} = 0)
  rw [Measure.restrict_apply₀' hs.nullMeasurableSet] at ha
  refine measure_zero_of_invariant hs _ ?_ ha
  intro γ
  ext x
  rw [mem_smul_set_iff_inv_smul_mem]
  simp only [mem_ofPred_eq, hf γ⁻¹ x]

中文:
定理 essSup_measure_restrict
  结论: (hs : 是FundamentalDomain G s μ) {f : α -> 实数>=0∞}
  证明: by
  refine le_antisymm (essSup_mono_measure' Measure.restrict_le_self) ?_
  rw [essSup_eq_sInf (μ.restrict s) f]; rw [essSup_eq_sInf μ f]
  refine sInf_le_sInf ?_
  rintro a (ha : (μ.restrict s) {x : α | a < f x} = 0)
  rw [Measure.restrict_apply₀' hs.nullMeasurableSet] at ha
  refine measure_zero_of_invariant hs _ ?_ ha
  intro γ
  ext x
  rw [mem_smul_set_iff_inv_smul_mem]
  simp only [mem_ofPred_eq, hf γ⁻¹ x]

Depends on / 依赖: Measure, Measure.restrict_apply, Measure.restrict_le_self, essSup_eq_sInf, essSup_mono_measure, hs.nullMeasurableSet, le_antisymm, measure_zero_of_invariant, mem_ofPred_eq, mem_smul_set_iff_inv_smul_mem, nullMeasurableSet, restrict, restrict_le_self, sInf_le_sInf
-/
theorem essSup_measure_restrict (hs : IsFundamentalDomain G s μ) {f : α -> Real>=0∞}
    (hf : forall γ : G, forall x : α, f (γ • x) = f x) : essSup f (μ.restrict s) = essSup f μ := by
  refine le_antisymm (essSup_mono_measure' Measure.restrict_le_self) ?_
  rw [essSup_eq_sInf (μ.restrict s) f]; rw [essSup_eq_sInf μ f]
  refine sInf_le_sInf ?_
  rintro a (ha : (μ.restrict s) {x : α | a < f x} = 0)
  rw [Measure.restrict_apply₀' hs.nullMeasurableSet] at ha
  refine measure_zero_of_invariant hs _ ?_ ha
  intro γ
  ext x
  rw [mem_smul_set_iff_inv_smul_mem]
  simp only [mem_ofPred_eq, hf γ⁻¹ x]

end IsFundamentalDomain

/-! ### Interior/frontier of a fundamental domain -/

section MeasurableSpace

variable (G) [Group G] [MulAction G α] (s : Set α) {x : α}

/-- The boundary of a fundamental domain, those points of the domain that also lie in a nontrivial
translate. -/
@[to_additive MeasureTheory.addFundamentalFrontier /-- The boundary of a fundamental domain, those
  points of the domain that also lie in a nontrivial translate. -/]
/--
Definition of `fundamentalFrontier` / `fundamentalFrontier` 的定义

English:
definition fundamentalFrontier
  signature: : Set α
  body: s inter ⋃ (g : G) (_ : g != 1), g • s

中文:
定义 fundamentalFrontier
  签名: : 集合 α
  定义体: s inter ⋃ (g : G) (_ : g != 1), g • s
-/
def fundamentalFrontier : Set α :=
  s inter ⋃ (g : G) (_ : g != 1), g • s

/-- The interior of a fundamental domain, those points of the domain not lying in any translate. -/
@[to_additive MeasureTheory.addFundamentalInterior /-- The interior of a fundamental domain, those
  points of the domain not lying in any translate. -/]
/--
Definition of `fundamentalInterior` / `fundamentalInterior` 的定义

English:
definition fundamentalInterior
  signature: : Set α
  body: s \ ⋃ (g : G) (_ : g != 1), g • s

中文:
定义 fundamental整数erior
  签名: : 集合 α
  定义体: s \ ⋃ (g : G) (_ : g != 1), g • s
-/
def fundamentalInterior : Set α :=
  s \ ⋃ (g : G) (_ : g != 1), g • s

variable {G s}

@[to_additive (attr := simp) MeasureTheory.mem_addFundamentalFrontier]
/--
theorem `mem_fundamentalFrontier` / 定理 `mem_fundamentalFrontier`

English:
theorem mem_fundamentalFrontier
  proof: by
  simp [fundamentalFrontier]

@[to_additive (attr := simp) MeasureTheory.mem_addFundamentalInterior]

中文:
定理 mem_fundamentalFrontier
  证明: by
  simp [fundamentalFrontier]

@[to_additive (attr := simp) MeasureTheory.mem_addFundamentalInterior]

Depends on / 依赖: fundamentalFrontier
-/
theorem mem_fundamentalFrontier :
    x in fundamentalFrontier G s ↔ x in s ∧ exists g : G, g != 1 ∧ x in g • s := by
  simp [fundamentalFrontier]

@[to_additive (attr := simp) MeasureTheory.mem_addFundamentalInterior]
/--
theorem `mem_fundamentalInterior` / 定理 `mem_fundamentalInterior`

English:
theorem mem_fundamentalInterior
  proof: by
  simp [fundamentalInterior]

@[to_additive MeasureTheory.addFundamentalFrontier_subset]

中文:
定理 mem_fundamental整数erior
  证明: by
  simp [fundamentalInterior]

@[to_additive MeasureTheory.addFundamentalFrontier_subset]

Depends on / 依赖: fundamentalInterior
-/
theorem mem_fundamentalInterior :
    x in fundamentalInterior G s ↔ x in s ∧ forall g : G, g != 1 -> x ∉ g • s := by
  simp [fundamentalInterior]

@[to_additive MeasureTheory.addFundamentalFrontier_subset]
/--
theorem `fundamentalFrontier_subset` / 定理 `fundamentalFrontier_subset`

English:
theorem fundamentalFrontier_subset
  statement: fundamentalFrontier G s subseteq s
  proof: inter_subset_left

@[to_additive MeasureTheory.addFundamentalInterior_subset]

中文:
定理 fundamentalFrontier_subset
  结论: fundamentalFrontier G s subseteq s
  证明: inter_subset_left

@[to_additive MeasureTheory.addFundamentalInterior_subset]

Depends on / 依赖: inter_subset_left
-/
theorem fundamentalFrontier_subset : fundamentalFrontier G s subseteq s :=
  inter_subset_left

@[to_additive MeasureTheory.addFundamentalInterior_subset]
/--
theorem `fundamentalInterior_subset` / 定理 `fundamentalInterior_subset`

English:
theorem fundamentalInterior_subset
  statement: fundamentalInterior G s subseteq s
  proof: sdiff_subset

中文:
定理 fundamental整数erior_subset
  结论: fundamental整数erior G s subseteq s
  证明: sdiff_subset

Depends on / 依赖: sdiff_subset
-/
theorem fundamentalInterior_subset : fundamentalInterior G s subseteq s :=
  sdiff_subset

variable (G s)

@[to_additive MeasureTheory.disjoint_addFundamentalInterior_addFundamentalFrontier]
/--
theorem `disjoint_fundamentalInterior_fundamentalFrontier` / 定理 `disjoint_fundamentalInterior_fundamentalFrontier`

English:
theorem disjoint_fundamentalInterior_fundamentalFrontier
  proof: disjoint_sdiff_self_left.mono_right inf_le_right

@[to_additive (attr := simp) MeasureTheory.addFundamentalInterior_union_addFundamentalFrontier]

中文:
定理 disjoint_fundamental整数erior_fundamentalFrontier
  证明: disjoint_sdiff_self_left.mono_right inf_le_right

@[to_additive (attr := simp) MeasureTheory.addFundamentalInterior_union_addFundamentalFrontier]

Depends on / 依赖: disjoint_sdiff_self_left, disjoint_sdiff_self_left.mono_right, inf_le_right, mono_right
-/
theorem disjoint_fundamentalInterior_fundamentalFrontier :
    Disjoint (fundamentalInterior G s) (fundamentalFrontier G s) :=
  disjoint_sdiff_self_left.mono_right inf_le_right

@[to_additive (attr := simp) MeasureTheory.addFundamentalInterior_union_addFundamentalFrontier]
/--
theorem `fundamentalInterior_union_fundamentalFrontier` / 定理 `fundamentalInterior_union_fundamentalFrontier`

English:
theorem fundamentalInterior_union_fundamentalFrontier
  proof: sdiff_union_inter _ _

@[to_additive (attr := simp) MeasureTheory.addFundamentalFrontier_union_addFundamentalInterior]

中文:
定理 fundamental整数erior_union_fundamentalFrontier
  证明: sdiff_union_inter _ _

@[to_additive (attr := simp) MeasureTheory.addFundamentalFrontier_union_addFundamentalInterior]

Depends on / 依赖: sdiff_union_inter
-/
theorem fundamentalInterior_union_fundamentalFrontier :
    fundamentalInterior G s union fundamentalFrontier G s = s :=
  sdiff_union_inter _ _

@[to_additive (attr := simp) MeasureTheory.addFundamentalFrontier_union_addFundamentalInterior]
/--
theorem `fundamentalFrontier_union_fundamentalInterior` / 定理 `fundamentalFrontier_union_fundamentalInterior`

English:
theorem fundamentalFrontier_union_fundamentalInterior
  proof: inter_union_sdiff _ _

@[to_additive (attr := simp) MeasureTheory.sdiff_addFundamentalInterior]

中文:
定理 fundamentalFrontier_union_fundamental整数erior
  证明: inter_union_sdiff _ _

@[to_additive (attr := simp) MeasureTheory.sdiff_addFundamentalInterior]

Depends on / 依赖: inter_union_sdiff
-/
theorem fundamentalFrontier_union_fundamentalInterior :
    fundamentalFrontier G s union fundamentalInterior G s = s :=
  inter_union_sdiff _ _

@[to_additive (attr := simp) MeasureTheory.sdiff_addFundamentalInterior]
/--
theorem `sdiff_fundamentalInterior` / 定理 `sdiff_fundamentalInterior`

English:
theorem sdiff_fundamentalInterior
  statement: s \ fundamentalInterior G s = fundamentalFrontier G s
  proof: sdiff_sdiff_right_self

@[to_additive (attr := simp) MeasureTheory.sdiff_addFundamentalFrontier]

中文:
定理 sdiff_fundamental整数erior
  结论: s \ fundamental整数erior G s = fundamentalFrontier G s
  证明: sdiff_sdiff_right_self

@[to_additive (attr := simp) MeasureTheory.sdiff_addFundamentalFrontier]

Depends on / 依赖: sdiff_sdiff_right_self
-/
theorem sdiff_fundamentalInterior : s \ fundamentalInterior G s = fundamentalFrontier G s :=
  sdiff_sdiff_right_self

@[to_additive (attr := simp) MeasureTheory.sdiff_addFundamentalFrontier]
/--
theorem `sdiff_fundamentalFrontier` / 定理 `sdiff_fundamentalFrontier`

English:
theorem sdiff_fundamentalFrontier
  statement: s \ fundamentalFrontier G s = fundamentalInterior G s
  proof: sdiff_self_inter

@[to_additive (attr := simp) MeasureTheory.addFundamentalFrontier_vadd]

中文:
定理 sdiff_fundamentalFrontier
  结论: s \ fundamentalFrontier G s = fundamental整数erior G s
  证明: sdiff_self_inter

@[to_additive (attr := simp) MeasureTheory.addFundamentalFrontier_vadd]

Depends on / 依赖: sdiff_self_inter
-/
theorem sdiff_fundamentalFrontier : s \ fundamentalFrontier G s = fundamentalInterior G s :=
  sdiff_self_inter

@[to_additive (attr := simp) MeasureTheory.addFundamentalFrontier_vadd]
/--
theorem `fundamentalFrontier_smul` / 定理 `fundamentalFrontier_smul`

English:
theorem fundamentalFrontier_smul
  given: [Group H] [MulAction H α] [SMulCommClass H G α] (g : H)
  proof: by
  simp_rw [fundamentalFrontier, smul_set_inter, smul_set_iUnion, smul_comm g (_ : G) (_ : Set α)]

@[to_additive (attr := simp) MeasureTheory.addFundamentalInterior_vadd]

中文:
定理 fundamentalFrontier_smul
  条件: [群 H] [乘法作用 H α] [标量交换类 H G α] (g : H)
  证明: by
  simp_rw [fundamentalFrontier, smul_set_inter, smul_set_iUnion, smul_comm g (_ : G) (_ : Set α)]

@[to_additive (attr := simp) MeasureTheory.addFundamentalInterior_vadd]

Depends on / 依赖: fundamentalFrontier, simp_rw, smul_comm, smul_set_iUnion, smul_set_inter
-/
theorem fundamentalFrontier_smul [Group H] [MulAction H α] [SMulCommClass H G α] (g : H) :
    fundamentalFrontier G (g • s) = g • fundamentalFrontier G s := by
  simp_rw [fundamentalFrontier, smul_set_inter, smul_set_iUnion, smul_comm g (_ : G) (_ : Set α)]

@[to_additive (attr := simp) MeasureTheory.addFundamentalInterior_vadd]
/--
theorem `fundamentalInterior_smul` / 定理 `fundamentalInterior_smul`

English:
theorem fundamentalInterior_smul
  given: [Group H] [MulAction H α] [SMulCommClass H G α] (g : H)
  proof: by
  simp_rw [fundamentalInterior, smul_set_sdiff, smul_set_iUnion, smul_comm g (_ : G) (_ : Set α)]

@[to_additive MeasureTheory.pairwise_disjoint_addFundamentalInterior]

中文:
定理 fundamental整数erior_smul
  条件: [群 H] [乘法作用 H α] [标量交换类 H G α] (g : H)
  证明: by
  simp_rw [fundamentalInterior, smul_set_sdiff, smul_set_iUnion, smul_comm g (_ : G) (_ : Set α)]

@[to_additive MeasureTheory.pairwise_disjoint_addFundamentalInterior]

Depends on / 依赖: fundamentalInterior, simp_rw, smul_comm, smul_set_iUnion, smul_set_sdiff
-/
theorem fundamentalInterior_smul [Group H] [MulAction H α] [SMulCommClass H G α] (g : H) :
    fundamentalInterior G (g • s) = g • fundamentalInterior G s := by
  simp_rw [fundamentalInterior, smul_set_sdiff, smul_set_iUnion, smul_comm g (_ : G) (_ : Set α)]

@[to_additive MeasureTheory.pairwise_disjoint_addFundamentalInterior]
/--
theorem `pairwise_disjoint_fundamentalInterior` / 定理 `pairwise_disjoint_fundamentalInterior`

English:
theorem pairwise_disjoint_fundamentalInterior
  proof: by
  refine fun a b hab => disjoint_left.2 ?_
  rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
  rw [mem_fundamentalInterior] at hx hy
  refine hx.2 (a⁻¹ * b) ?_ ?_
  · rwa [Ne, inv_mul_eq_iff_eq_mul, mul_one, eq_comm]
  · simpa [mul_smul, ← hxy, mem_inv_smul_set_iff] using hy.1

中文:
定理 pairwise_disjoint_fundamental整数erior
  证明: by
  refine fun a b hab => disjoint_left.2 ?_
  rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
  rw [mem_fundamentalInterior] at hx hy
  refine hx.2 (a⁻¹ * b) ?_ ?_
  · rwa [Ne, inv_mul_eq_iff_eq_mul, mul_one, eq_comm]
  · simpa [mul_smul, ← hxy, mem_inv_smul_set_iff] using hy.1

Depends on / 依赖: disjoint_left, eq_comm, inv_mul_eq_iff_eq_mul, mem_fundamentalInterior, mem_inv_smul_set_iff, mul_one, mul_smul
-/
theorem pairwise_disjoint_fundamentalInterior :
    Pairwise (Disjoint on fun g : G => g • fundamentalInterior G s) := by
  refine fun a b hab => disjoint_left.2 ?_
  rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
  rw [mem_fundamentalInterior] at hx hy
  refine hx.2 (a⁻¹ * b) ?_ ?_
  · rwa [Ne, inv_mul_eq_iff_eq_mul, mul_one, eq_comm]
  · simpa [mul_smul, ← hxy, mem_inv_smul_set_iff] using hy.1

variable [Countable G] [MeasurableSpace α] [MeasurableConstSMul G α]
  {μ : Measure α} [SMulInvariantMeasure G α μ]

@[to_additive MeasureTheory.NullMeasurableSet.addFundamentalFrontier]
/--
theorem `NullMeasurableSet.fundamentalFrontier` / 定理 `NullMeasurableSet.fundamentalFrontier`

English:
theorem NullMeasurableSet.fundamentalFrontier
  given: (hs : NullMeasurableSet s μ)
  proof: hs.inter .iUnion fun _ => .iUnion fun _ => hs.smul _

@[to_additive MeasureTheory.NullMeasurableSet.addFundamentalInterior]

中文:
定理 NullMeasurableSet.fundamentalFrontier
  条件: (hs : NullMeasurableSet s μ)
  证明: hs.inter .iUnion fun _ => .iUnion fun _ => hs.smul _

@[to_additive MeasureTheory.NullMeasurableSet.addFundamentalInterior]
-/
protected theorem NullMeasurableSet.fundamentalFrontier (hs : NullMeasurableSet s μ) :
    NullMeasurableSet (fundamentalFrontier G s) μ :=
hs.inter .iUnion fun _ => .iUnion fun _ => hs.smul _

@[to_additive MeasureTheory.NullMeasurableSet.addFundamentalInterior]
/--
theorem `NullMeasurableSet.fundamentalInterior` / 定理 `NullMeasurableSet.fundamentalInterior`

English:
theorem NullMeasurableSet.fundamentalInterior
  given: (hs : NullMeasurableSet s μ)
  proof: hs.diff .iUnion fun _ => .iUnion fun _ => hs.smul _

中文:
定理 NullMeasurableSet.fundamental整数erior
  条件: (hs : NullMeasurableSet s μ)
  证明: hs.diff .iUnion fun _ => .iUnion fun _ => hs.smul _
-/
protected theorem NullMeasurableSet.fundamentalInterior (hs : NullMeasurableSet s μ) :
    NullMeasurableSet (fundamentalInterior G s) μ :=
hs.diff .iUnion fun _ => .iUnion fun _ => hs.smul _

end MeasurableSpace

namespace IsFundamentalDomain

variable [Countable G] [Group G] [MulAction G α] [MeasurableSpace α] {μ : Measure α} {s : Set α}
  (hs : IsFundamentalDomain G s μ)
include hs

section Group


@[to_additive MeasureTheory.IsAddFundamentalDomain.measure_addFundamentalFrontier]
/--
theorem `measure_fundamentalFrontier` / 定理 `measure_fundamentalFrontier`

English:
theorem measure_fundamentalFrontier
  statement: μ (fundamentalFrontier G s) = 0
  proof: by
  simpa only [fundamentalFrontier, iUnion₂_inter, one_smul, measure_iUnion_null_iff, inter_comm s,
    Function.onFun] using! fun g (hg : g != 1) => hs.aedisjoint hg

@[to_additive MeasureTheory.IsAddFundamentalDomain.measure_addFundamentalInterior]

中文:
定理 measure_fundamentalFrontier
  结论: μ (fundamentalFrontier G s) = 0
  证明: by
  simpa only [fundamentalFrontier, iUnion₂_inter, one_smul, measure_iUnion_null_iff, inter_comm s,
    Function.onFun] using! fun g (hg : g != 1) => hs.aedisjoint hg

@[to_additive MeasureTheory.IsAddFundamentalDomain.measure_addFundamentalInterior]

Depends on / 依赖: Function, Function.onFun, aedisjoint, fundamentalFrontier, hs.aedisjoint, inter_comm, measure_iUnion_null_iff, one_smul
-/
theorem measure_fundamentalFrontier : μ (fundamentalFrontier G s) = 0 := by
  simpa only [fundamentalFrontier, iUnion₂_inter, one_smul, measure_iUnion_null_iff, inter_comm s,
    Function.onFun] using! fun g (hg : g != 1) => hs.aedisjoint hg

@[to_additive MeasureTheory.IsAddFundamentalDomain.measure_addFundamentalInterior]
/--
theorem `measure_fundamentalInterior` / 定理 `measure_fundamentalInterior`

English:
theorem measure_fundamentalInterior
  statement: μ (fundamentalInterior G s) = μ s
  proof: measure_sdiff_null' hs.measure_fundamentalFrontier

中文:
定理 measure_fundamental整数erior
  结论: μ (fundamental整数erior G s) = μ s
  证明: measure_sdiff_null' hs.measure_fundamentalFrontier

Depends on / 依赖: hs.measure_fundamentalFrontier, measure_fundamentalFrontier, measure_sdiff_null
-/
theorem measure_fundamentalInterior : μ (fundamentalInterior G s) = μ s :=
  measure_sdiff_null' hs.measure_fundamentalFrontier

end Group

variable [MeasurableConstSMul G α] [SMulInvariantMeasure G α μ]

/--
theorem `fundamentalInterior` / 定理 `fundamentalInterior`

English:
theorem fundamentalInterior
  statement: IsFundamentalDomain G (fundamentalInterior G s) μ where
  proof: hs.nullMeasurableSet.fundamentalInterior _ _
  ae_covers := by
    simp_rw [ae_iff, not_exists, ← mem_inv_smul_set_iff, ofPred_forall, ← compl_ofPred,
      ofPred_mem_eq, ← compl_iUnion]
    have :
      ((⋃ g : G, g⁻¹ • s) \ ⋃ g : G, g⁻¹ • fundamentalFrontier G s) subseteq
        ⋃ g : G, g⁻¹ • fundamentalInterior G s := by
      simp_rw [sdiff_subset_iff, ← iUnion_union_distrib, ← smul_set_union (α := G) (β := α),
        fundamentalFrontier_union_fundamentalInterior]; rfl
    refine eq_bot_mono (μ.mono <| compl_subset_compl.2 this) ?_
    simp only [iUnion_inv_smul, compl_sdiff, ENNReal.bot_eq_zero,
      @iUnion_smul_eq_ofPred_exists _ _ _ _ s]
    exact measure_union_null
      (measure_iUnion_null fun _ => measure_smul_null hs.measure_fundamentalFrontier _) hs.ae_covers
  aedisjoint := (pairwise_disjoint_fundamentalInterior _ _).mono fun _ _ => Disjoint.aedisjoint

中文:
定理 fundamental整数erior
  结论: 是FundamentalDomain G (fundamental整数erior G s) μ where
  证明: hs.nullMeasurableSet.fundamentalInterior _ _
  ae_covers := by
    simp_rw [ae_iff, not_exists, ← mem_inv_smul_set_iff, ofPred_forall, ← compl_ofPred,
      ofPred_mem_eq, ← compl_iUnion]
    have :
      ((⋃ g : G, g⁻¹ • s) \ ⋃ g : G, g⁻¹ • fundamentalFrontier G s) subseteq
        ⋃ g : G, g⁻¹ • fundamentalInterior G s := by
      simp_rw [sdiff_subset_iff, ← iUnion_union_distrib, ← smul_set_union (α := G) (β := α),
        fundamentalFrontier_union_fundamentalInterior]; rfl
    refine eq_bot_mono (μ.mono <| compl_subset_compl.2 this) ?_
    simp only [iUnion_inv_smul, compl_sdiff, ENNReal.bot_eq_zero,
      @iUnion_smul_eq_ofPred_exists _ _ _ _ s]
    exact measure_union_null
      (measure_iUnion_null fun _ => measure_smul_null hs.measure_fundamentalFrontier _) hs.ae_covers
  aedisjoint := (pairwise_disjoint_fundamentalInterior _ _).mono fun _ _ => Disjoint.aedisjoint
-/
protected theorem fundamentalInterior : IsFundamentalDomain G (fundamentalInterior G s) μ where
  nullMeasurableSet := hs.nullMeasurableSet.fundamentalInterior _ _
  ae_covers := by
    simp_rw [ae_iff, not_exists, ← mem_inv_smul_set_iff, ofPred_forall, ← compl_ofPred,
      ofPred_mem_eq, ← compl_iUnion]
    have :
      ((⋃ g : G, g⁻¹ • s) \ ⋃ g : G, g⁻¹ • fundamentalFrontier G s) subseteq
        ⋃ g : G, g⁻¹ • fundamentalInterior G s := by
      simp_rw [sdiff_subset_iff, ← iUnion_union_distrib, ← smul_set_union (α := G) (β := α),
        fundamentalFrontier_union_fundamentalInterior]; rfl
    refine eq_bot_mono (μ.mono <| compl_subset_compl.2 this) ?_
    simp only [iUnion_inv_smul, compl_sdiff, ENNReal.bot_eq_zero,
      @iUnion_smul_eq_ofPred_exists _ _ _ _ s]
    exact measure_union_null
      (measure_iUnion_null fun _ => measure_smul_null hs.measure_fundamentalFrontier _) hs.ae_covers
  aedisjoint := (pairwise_disjoint_fundamentalInterior _ _).mono fun _ _ => Disjoint.aedisjoint

end IsFundamentalDomain

section FundamentalDomainMeasure

variable (G) [Group G] [MulAction G α] [MeasurableSpace α]
  (μ : Measure α)

local notation "α_mod_G" => MulAction.orbitRel G α

local notation "π" => @Quotient.mk _ α_mod_G

variable {G}

@[to_additive addMeasure_map_restrict_apply]
/--
lemma `measure_map_restrict_apply` / 引理 `measure_map_restrict_apply`

English:
lemma measure_map_restrict_apply
  statement: (s : Set α) {U : Set (Quotient α_mod_G)}
  proof: by
  rw [map_apply (f := π) (fun V hV => measurableSet_quotient.mp hV) meas_U]; rw [Measure.restrict_apply (t := (Quotient.mk α_mod_G ⁻¹' U)) (measurableSet_quotient.mp meas_U)]

@[to_additive]

中文:
引理 measure_map_restrict_apply
  结论: (s : 集合 α) {U : 集合 (商 α_mod_G)}
  证明: by
  rw [map_apply (f := π) (fun V hV => measurableSet_quotient.mp hV) meas_U]; rw [Measure.restrict_apply (t := (Quotient.mk α_mod_G ⁻¹' U)) (measurableSet_quotient.mp meas_U)]

@[to_additive]

Depends on / 依赖: Measure, Measure.restrict_apply, Quotient, Quotient.mk, map_apply, meas_U, measurableSet_quotient, measurableSet_quotient.mp, restrict_apply
-/
lemma measure_map_restrict_apply (s : Set α) {U : Set (Quotient α_mod_G)}
    (meas_U : MeasurableSet U) :
    (μ.restrict s).map π U = μ ((π ⁻¹' U) inter s) := by
  rw [map_apply (f := π) (fun V hV => measurableSet_quotient.mp hV) meas_U]; rw [Measure.restrict_apply (t := (Quotient.mk α_mod_G ⁻¹' U)) (measurableSet_quotient.mp meas_U)]

@[to_additive]
/--
lemma `IsFundamentalDomain.quotientMeasure_eq` / 引理 `IsFundamentalDomain.quotientMeasure_eq`

English:
lemma IsFundamentalDomain.quotientMeasure_eq
  statement: [Countable G] {s t : Set α}
  proof: by
  ext U meas_U
  rw [measure_map_restrict_apply (meas_U := meas_U)]; rw [measure_map_restrict_apply (meas_U := meas_U)]
  apply MeasureTheory.IsFundamentalDomain.measure_set_eq fund_dom_s fund_dom_t
  · exact measurableSet_quotient.mp meas_U
  · intro g
    ext x
    have : Quotient.mk α_mod_G (g • x) = Quotient.mk α_mod_G x := by
      apply Quotient.sound
      use g
    simp only [mem_preimage, this]

中文:
引理 是FundamentalDomain.quotientMeasure_eq
  结论: [可数 G] {s t : 集合 α}
  证明: by
  ext U meas_U
  rw [measure_map_restrict_apply (meas_U := meas_U)]; rw [measure_map_restrict_apply (meas_U := meas_U)]
  apply MeasureTheory.IsFundamentalDomain.measure_set_eq fund_dom_s fund_dom_t
  · exact measurableSet_quotient.mp meas_U
  · intro g
    ext x
    have : Quotient.mk α_mod_G (g • x) = Quotient.mk α_mod_G x := by
      apply Quotient.sound
      use g
    simp only [mem_preimage, this]

Depends on / 依赖: IsFundamentalDomain, MeasureTheory, MeasureTheory.IsFundamentalDomain.measure_set_eq, Quotient, Quotient.mk, Quotient.sound, fund_dom_s, fund_dom_t, meas_U, measurableSet_quotient, measurableSet_quotient.mp, measure_map_restrict_apply, measure_set_eq, mem_preimage
-/
lemma IsFundamentalDomain.quotientMeasure_eq [Countable G] {s t : Set α}
    [SMulInvariantMeasure G α μ] [MeasurableConstSMul G α] (fund_dom_s : IsFundamentalDomain G s μ)
    (fund_dom_t : IsFundamentalDomain G t μ) :
    (μ.restrict s).map π = (μ.restrict t).map π := by
  ext U meas_U
  rw [measure_map_restrict_apply (meas_U := meas_U)]; rw [measure_map_restrict_apply (meas_U := meas_U)]
  apply MeasureTheory.IsFundamentalDomain.measure_set_eq fund_dom_s fund_dom_t
  · exact measurableSet_quotient.mp meas_U
  · intro g
    ext x
    have : Quotient.mk α_mod_G (g • x) = Quotient.mk α_mod_G x := by
      apply Quotient.sound
      use g
    simp only [mem_preimage, this]

end FundamentalDomainMeasure

/-! ## `HasFundamentalDomain` typeclass

We define `HasFundamentalDomain` in order to be able to define the `covolume` of a quotient of `α`
by a group `G`, which under reasonable conditions does not depend on the choice of fundamental
domain. Even though any "sensible" action should have a fundamental domain, this is a rather
delicate question which was recently addressed by Misha Kapovich: https://arxiv.org/abs/2301.05325

TODO: Formalize the existence of a Dirichlet domain as in Kapovich's paper.

-/

section HasFundamentalDomain

/--
Definition of `HasAddFundamentalDomain` / `HasAddFundamentalDomain` 的定义

English:
class HasAddFundamentalDomain
  parameters: (G α : Type*) [Zero G] [VAdd G α] [MeasurableSpace α]
  axioms and operations (1):
    - ExistsIsAddFundamentalDomain : exists s : Set α, IsAddFundamentalDomain G s ν

中文:
类 有加法FundamentalDomain
  参数: (G α : 类型) [零 G] [向量加法 G α] [可测空间 α]
  公理与运算 (1 个):
    - ExistsIsAddFundamentalDomain : 存在 s : 集合 α, 是加法FundamentalDomain G s ν

Depends on / 依赖: ExistsIsAddFundamentalDomain, IsAddFundamentalDomain, volume_tac
-/
class HasAddFundamentalDomain (G α : Type*) [Zero G] [VAdd G α] [MeasurableSpace α]
    (ν : Measure α := by volume_tac) : Prop where
  ExistsIsAddFundamentalDomain : exists s : Set α, IsAddFundamentalDomain G s ν

/--
Definition of `HasFundamentalDomain` / `HasFundamentalDomain` 的定义

English:
class HasFundamentalDomain
  parameters: (G : Type*) (α : Type*) [One G] [SMul G α] [MeasurableSpace α]
  axioms and operations (1):
    - ExistsIsFundamentalDomain : exists (s : Set α), IsFundamentalDomain G s ν

中文:
类 有FundamentalDomain
  参数: (G : 类型) (α : 类型) [幺 G] [标量乘法 G α] [可测空间 α]
  公理与运算 (1 个):
    - ExistsIsFundamentalDomain : 存在 (s : 集合 α), 是FundamentalDomain G s ν

Depends on / 依赖: ExistsIsFundamentalDomain, IsFundamentalDomain, volume_tac
-/
class HasFundamentalDomain (G : Type*) (α : Type*) [One G] [SMul G α] [MeasurableSpace α]
    (ν : Measure α := by volume_tac) : Prop where
  ExistsIsFundamentalDomain : exists (s : Set α), IsFundamentalDomain G s ν

attribute [to_additive existing] MeasureTheory.HasFundamentalDomain

open scoped Classical in
/-- The `covolume` of an action of `G` on `α` the volume of some fundamental domain, or `0` if
none exists. -/
@[to_additive addCovolume /-- The `addCovolume` of an action of `G` on `α` is the volume of some
fundamental domain, or `0` if none exists. -/]
/--
Definition of `covolume` / `covolume` 的定义

English:
definition covolume
  signature: (G α : Type*) [One G] [SMul G α] [MeasurableSpace α]
  body: if funDom : HasFundamentalDomain G α ν then ν funDom.ExistsIsFundamentalDomain.choose else 0

中文:
定义 covolume
  签名: (G α : 类型) [幺 G] [标量乘法 G α] [可测空间 α]
  定义体: if funDom : HasFundamentalDomain G α ν then ν funDom.ExistsIsFundamentalDomain.choose else 0

Depends on / 依赖: ExistsIsFundamentalDomain, HasFundamentalDomain, funDom, funDom.ExistsIsFundamentalDomain.choose, volume_tac
-/
noncomputable def covolume (G α : Type*) [One G] [SMul G α] [MeasurableSpace α]
    (ν : Measure α := by volume_tac) : Real>=0∞ :=
  if funDom : HasFundamentalDomain G α ν then ν funDom.ExistsIsFundamentalDomain.choose else 0

variable [Group G] [MulAction G α] [MeasurableSpace α]

/-- If there is a fundamental domain `s`, then `HasFundamentalDomain` holds. -/
@[to_additive /-- If there is an additive fundamental domain `s`, then `HasAddFundamentalDomain`
holds. -/]
/--
lemma `IsFundamentalDomain.hasFundamentalDomain` / 引理 `IsFundamentalDomain.hasFundamentalDomain`

English:
lemma IsFundamentalDomain.hasFundamentalDomain
  statement: (ν : Measure α) {s : Set α}
  proof: ⟨⟨s, fund_dom_s⟩⟩

中文:
引理 是FundamentalDomain.hasFundamentalDomain
  结论: (ν : 测度 α) {s : 集合 α}
  证明: ⟨⟨s, fund_dom_s⟩⟩

Depends on / 依赖: fund_dom_s
-/
lemma IsFundamentalDomain.hasFundamentalDomain (ν : Measure α) {s : Set α}
    (fund_dom_s : IsFundamentalDomain G s ν) :
    HasFundamentalDomain G α ν := ⟨⟨s, fund_dom_s⟩⟩

/-- The `covolume` can be computed by taking the `volume` of any given fundamental domain `s`. -/
@[to_additive /-- The `addCovolume` can be computed by taking the `volume` of any given additive
fundamental domain `s`. -/]
/--
lemma `IsFundamentalDomain.covolume_eq_volume` / 引理 `IsFundamentalDomain.covolume_eq_volume`

English:
lemma IsFundamentalDomain.covolume_eq_volume
  statement: (ν : Measure α) [Countable G]
  proof: by
  dsimp [covolume]
  simp only [(fund_dom_s.hasFundamentalDomain ν), ↓reduceDIte]
  rw [fund_dom_s.measure_eq]
  exact (fund_dom_s.hasFundamentalDomain ν).ExistsIsFundamentalDomain.choose_spec

中文:
引理 是FundamentalDomain.covolume_eq_volume
  结论: (ν : 测度 α) [可数 G]
  证明: by
  dsimp [covolume]
  simp only [(fund_dom_s.hasFundamentalDomain ν), ↓reduceDIte]
  rw [fund_dom_s.measure_eq]
  exact (fund_dom_s.hasFundamentalDomain ν).ExistsIsFundamentalDomain.choose_spec

Depends on / 依赖: ExistsIsFundamentalDomain, ExistsIsFundamentalDomain.choose_spec, choose_spec, covolume, fund_dom_s, fund_dom_s.hasFundamentalDomain, fund_dom_s.measure_eq, hasFundamentalDomain, measure_eq, reduceDIte
-/
lemma IsFundamentalDomain.covolume_eq_volume (ν : Measure α) [Countable G]
    [MeasurableConstSMul G α] [SMulInvariantMeasure G α ν] {s : Set α}
    (fund_dom_s : IsFundamentalDomain G s ν) : covolume G α ν = ν s := by
  dsimp [covolume]
  simp only [(fund_dom_s.hasFundamentalDomain ν), ↓reduceDIte]
  rw [fund_dom_s.measure_eq]
  exact (fund_dom_s.hasFundamentalDomain ν).ExistsIsFundamentalDomain.choose_spec

end HasFundamentalDomain

/-! ## `QuotientMeasureEqMeasurePreimage` typeclass

This typeclass describes a situation in which a measure `μ` on `α ⧸ G` can be computed by
taking a measure `ν` on `α` of the intersection of the pullback with a fundamental domain.

It's curious that in measure theory, measures can be pushed forward, while in geometry, volumes can
be pulled back. And yet here, we are describing a situation involving measures in a geometric way.

Another viewpoint is that if a set is small enough to fit in a single fundamental domain, then its
`ν` measure in `α` is the same as the `μ` measure of its pushforward in `α ⧸ G`.

-/

section QuotientMeasureEqMeasurePreimage

section additive

variable [AddGroup G] [AddAction G α] [MeasurableSpace α]

local notation "α_mod_G" => AddAction.orbitRel G α

local notation "π" => @Quotient.mk _ α_mod_G

/--
Definition of `AddQuotientMeasureEqMeasurePreimage` / `AddQuotientMeasureEqMeasurePreimage` 的定义

English:
class AddQuotientMeasureEqMeasurePreimage
  parameters: (ν : Measure α := by volume_tac)
  axioms and operations (1):
    - addProjection_respects_measure' : forall (t : Set α) (_ : IsAddFundamentalDomain G t ν), μ = (ν.restrict t).map π

中文:
类 加法QuotientMeasureEqMeasurePreimage
  参数: (ν : 测度 α := by volume_tac)
  公理与运算 (1 个):
    - addProjection_respects_measure' : 对任意 (t : 集合 α) (_ : 是加法FundamentalDomain G t ν), μ = (ν.restrict t).map π

Depends on / 依赖: IsAddFundamentalDomain, Measure, Quotient, addProjection_respects_measure, restrict, volume_tac
-/
class AddQuotientMeasureEqMeasurePreimage (ν : Measure α := by volume_tac)
    (μ : Measure (Quotient α_mod_G)) : Prop where
  addProjection_respects_measure' : forall (t : Set α) (_ : IsAddFundamentalDomain G t ν),
    μ = (ν.restrict t).map π

end additive

variable [Group G] [MulAction G α] [MeasurableSpace α]

local notation "α_mod_G" => MulAction.orbitRel G α

local notation "π" => @Quotient.mk _ α_mod_G

/--
Definition of `QuotientMeasureEqMeasurePreimage` / `QuotientMeasureEqMeasurePreimage` 的定义

English:
class QuotientMeasureEqMeasurePreimage
  parameters: (ν : Measure α := by volume_tac)
  axioms and operations (1):
    - projection_respects_measure'((t : Set α)) : IsFundamentalDomain G t ν -> μ = (ν.restrict t).map π

中文:
类 QuotientMeasureEqMeasurePreimage
  参数: (ν : 测度 α := by volume_tac)
  公理与运算 (1 个):
    - projection_respects_measure'((t : 集合 α)) : 是FundamentalDomain G t ν -> μ = (ν.restrict t).map π

Depends on / 依赖: IsFundamentalDomain, Measure, Quotient, projection_respects_measure, restrict, volume_tac
-/
class QuotientMeasureEqMeasurePreimage (ν : Measure α := by volume_tac)
    (μ : Measure (Quotient α_mod_G)) : Prop where
  projection_respects_measure' (t : Set α) : IsFundamentalDomain G t ν -> μ = (ν.restrict t).map π

attribute [to_additive]
  MeasureTheory.QuotientMeasureEqMeasurePreimage

@[to_additive addProjection_respects_measure]
/--
lemma `IsFundamentalDomain.projection_respects_measure` / 引理 `IsFundamentalDomain.projection_respects_measure`

English:
lemma IsFundamentalDomain.projection_respects_measure
  statement: {ν : Measure α}
  proof: i.projection_respects_measure' t fund_dom_t

@[to_additive addProjection_respects_measure_apply]

中文:
引理 是FundamentalDomain.projection_respects_measure
  结论: {ν : 测度 α}
  证明: i.projection_respects_measure' t fund_dom_t

@[to_additive addProjection_respects_measure_apply]

Depends on / 依赖: fund_dom_t, i.projection_respects_measure, projection_respects_measure
-/
lemma IsFundamentalDomain.projection_respects_measure {ν : Measure α}
    (μ : Measure (Quotient α_mod_G)) [i : QuotientMeasureEqMeasurePreimage ν μ] {t : Set α}
    (fund_dom_t : IsFundamentalDomain G t ν) : μ = (ν.restrict t).map π :=
  i.projection_respects_measure' t fund_dom_t

@[to_additive addProjection_respects_measure_apply]
/--
lemma `IsFundamentalDomain.projection_respects_measure_apply` / 引理 `IsFundamentalDomain.projection_respects_measure_apply`

English:
lemma IsFundamentalDomain.projection_respects_measure_apply
  statement: {ν : Measure α}
  proof: by
  rw [fund_dom_t.projection_respects_measure (μ := μ)]; rw [measure_map_restrict_apply ν t meas_U]

中文:
引理 是FundamentalDomain.projection_respects_measure_apply
  结论: {ν : 测度 α}
  证明: by
  rw [fund_dom_t.projection_respects_measure (μ := μ)]; rw [measure_map_restrict_apply ν t meas_U]

Depends on / 依赖: fund_dom_t, fund_dom_t.projection_respects_measure, meas_U, measure_map_restrict_apply, projection_respects_measure
-/
lemma IsFundamentalDomain.projection_respects_measure_apply {ν : Measure α}
    (μ : Measure (Quotient α_mod_G)) [i : QuotientMeasureEqMeasurePreimage ν μ] {t : Set α}
    (fund_dom_t : IsFundamentalDomain G t ν) {U : Set (Quotient α_mod_G)}
    (meas_U : MeasurableSet U) : μ U = ν (π ⁻¹' U inter t) := by
  rw [fund_dom_t.projection_respects_measure (μ := μ)]; rw [measure_map_restrict_apply ν t meas_U]

variable {ν : Measure α}

/-- Any two measures satisfying `QuotientMeasureEqMeasurePreimage` are equal. -/
@[to_additive /-- Any two measures satisfying `AddQuotientMeasureEqMeasurePreimage` are equal. -/]
/--
lemma `QuotientMeasureEqMeasurePreimage.unique` / 引理 `QuotientMeasureEqMeasurePreimage.unique`

English:
lemma QuotientMeasureEqMeasurePreimage.unique
  proof: by
  obtain ⟨𝓕, h𝓕⟩ := hasFun.ExistsIsFundamentalDomain
  rw [h𝓕.projection_respects_measure (μ := μ)]; rw [h𝓕.projection_respects_measure (μ := μ')]

中文:
引理 QuotientMeasureEqMeasurePreimage.unique
  证明: by
  obtain ⟨𝓕, h𝓕⟩ := hasFun.ExistsIsFundamentalDomain
  rw [h𝓕.projection_respects_measure (μ := μ)]; rw [h𝓕.projection_respects_measure (μ := μ')]

Depends on / 依赖: ExistsIsFundamentalDomain, hasFun, hasFun.ExistsIsFundamentalDomain, projection_respects_measure
-/
lemma QuotientMeasureEqMeasurePreimage.unique
    [hasFun : HasFundamentalDomain G α ν] (μ μ' : Measure (Quotient α_mod_G))
    [QuotientMeasureEqMeasurePreimage ν μ] [QuotientMeasureEqMeasurePreimage ν μ'] :
    μ = μ' := by
  obtain ⟨𝓕, h𝓕⟩ := hasFun.ExistsIsFundamentalDomain
  rw [h𝓕.projection_respects_measure (μ := μ)]; rw [h𝓕.projection_respects_measure (μ := μ')]

/-- The quotient map to `α ⧸ G` is measure-preserving between the restriction of `volume` to a
  fundamental domain in `α` and a related measure satisfying `QuotientMeasureEqMeasurePreimage`. -/
@[to_additive IsAddFundamentalDomain.measurePreserving_add_quotient_mk /-- The quotient map to
the additive quotient of `α` by `G` is measure-preserving between the restriction of `volume` to
an additive fundamental domain in `α` and a related measure satisfying
`AddQuotientMeasureEqMeasurePreimage`. -/]
/--
theorem `IsFundamentalDomain.measurePreserving_quotient_mk` / 定理 `IsFundamentalDomain.measurePreserving_quotient_mk`

English:
theorem IsFundamentalDomain.measurePreserving_quotient_mk
  proof: measurable_quotient_mk' (s := α_mod_G)
  map_eq := by
    have : HasFundamentalDomain G α ν := ⟨𝓕, h𝓕⟩
    rw [h𝓕.projection_respects_measure (μ := μ)]

中文:
定理 是FundamentalDomain.measurePreserving_quotient_mk
  证明: measurable_quotient_mk' (s := α_mod_G)
  map_eq := by
    have : HasFundamentalDomain G α ν := ⟨𝓕, h𝓕⟩
    rw [h𝓕.projection_respects_measure (μ := μ)]

Depends on / 依赖: measurable_quotient_mk
-/
theorem IsFundamentalDomain.measurePreserving_quotient_mk
    {𝓕 : Set α} (h𝓕 : IsFundamentalDomain G 𝓕 ν)
    (μ : Measure (Quotient α_mod_G)) [QuotientMeasureEqMeasurePreimage ν μ] :
    MeasurePreserving π (ν.restrict 𝓕) μ where
  measurable := measurable_quotient_mk' (s := α_mod_G)
  map_eq := by
    have : HasFundamentalDomain G α ν := ⟨𝓕, h𝓕⟩
    rw [h𝓕.projection_respects_measure (μ := μ)]

variable [SMulInvariantMeasure G α ν] [Countable G] [MeasurableConstSMul G α]

/-- Given a measure upstairs (i.e., on `α`), and a choice `s` of fundamental domain, there's always
an artificial way to generate a measure downstairs such that the pair satisfies the
`QuotientMeasureEqMeasurePreimage` typeclass. -/
@[to_additive /-- Given a measure upstairs (i.e., on `α`), and a choice `s` of additive
fundamental domain, there's always an artificial way to generate a measure downstairs such that
the pair satisfies the `AddQuotientMeasureEqMeasurePreimage` typeclass. -/]
/--
lemma `IsFundamentalDomain.quotientMeasureEqMeasurePreimage_quotientMeasure` / 引理 `IsFundamentalDomain.quotientMeasureEqMeasurePreimage_quotientMeasure`

English:
lemma IsFundamentalDomain.quotientMeasureEqMeasurePreimage_quotientMeasure
  proof: by rw [fund_dom_s.quotientMeasure_eq _ fund_dom_t]

中文:
引理 是FundamentalDomain.quotientMeasureEqMeasurePreimage_quotientMeasure
  证明: by rw [fund_dom_s.quotientMeasure_eq _ fund_dom_t]

Depends on / 依赖: fund_dom_s, fund_dom_s.quotientMeasure_eq, fund_dom_t, quotientMeasure_eq
-/
lemma IsFundamentalDomain.quotientMeasureEqMeasurePreimage_quotientMeasure
    {s : Set α} (fund_dom_s : IsFundamentalDomain G s ν) :
    QuotientMeasureEqMeasurePreimage ν ((ν.restrict s).map π) where
  projection_respects_measure' t fund_dom_t := by rw [fund_dom_s.quotientMeasure_eq _ fund_dom_t]

/-- One can prove `QuotientMeasureEqMeasurePreimage` by checking behavior with respect to a single
fundamental domain. -/
@[to_additive /-- One can prove `AddQuotientMeasureEqMeasurePreimage` by checking behavior with
respect to a single additive fundamental domain. -/]
/--
lemma `IsFundamentalDomain.quotientMeasureEqMeasurePreimage` / 引理 `IsFundamentalDomain.quotientMeasureEqMeasurePreimage`

English:
lemma IsFundamentalDomain.quotientMeasureEqMeasurePreimage
  statement: {μ : Measure (Quotient α_mod_G)}
  proof: by
  simpa [h] using fund_dom_s.quotientMeasureEqMeasurePreimage_quotientMeasure

中文:
引理 是FundamentalDomain.quotientMeasureEqMeasurePreimage
  结论: {μ : 测度 (商 α_mod_G)}
  证明: by
  simpa [h] using fund_dom_s.quotientMeasureEqMeasurePreimage_quotientMeasure

Depends on / 依赖: fund_dom_s, fund_dom_s.quotientMeasureEqMeasurePreimage_quotientMeasure, quotientMeasureEqMeasurePreimage_quotientMeasure
-/
lemma IsFundamentalDomain.quotientMeasureEqMeasurePreimage {μ : Measure (Quotient α_mod_G)}
    {s : Set α} (fund_dom_s : IsFundamentalDomain G s ν) (h : μ = (ν.restrict s).map π) :
    QuotientMeasureEqMeasurePreimage ν μ := by
  simpa [h] using fund_dom_s.quotientMeasureEqMeasurePreimage_quotientMeasure


/-- If a fundamental domain has volume 0, then `QuotientMeasureEqMeasurePreimage` holds. -/
@[to_additive /-- If an additive fundamental domain has volume 0, then
`AddQuotientMeasureEqMeasurePreimage` holds. -/]
/--
theorem `IsFundamentalDomain.quotientMeasureEqMeasurePreimage_of_zero` / 定理 `IsFundamentalDomain.quotientMeasureEqMeasurePreimage_of_zero`

English:
theorem IsFundamentalDomain.quotientMeasureEqMeasurePreimage_of_zero
  proof: by
  apply fund_dom_s.quotientMeasureEqMeasurePreimage
  ext U meas_U
  simp only [Measure.coe_zero, Pi.zero_apply]
  convert! (measure_inter_null_of_null_right (h := vol_s) (Quotient.mk α_mod_G ⁻¹' U)).symm
  rw [measure_map_restrict_apply (meas_U := meas_U)]

中文:
定理 是FundamentalDomain.quotientMeasureEqMeasurePreimage_of_zero
  证明: by
  apply fund_dom_s.quotientMeasureEqMeasurePreimage
  ext U meas_U
  simp only [Measure.coe_zero, Pi.zero_apply]
  convert! (measure_inter_null_of_null_right (h := vol_s) (Quotient.mk α_mod_G ⁻¹' U)).symm
  rw [measure_map_restrict_apply (meas_U := meas_U)]

Depends on / 依赖: Measure, Measure.coe_zero, Pi.zero_apply, Quotient, Quotient.mk, coe_zero, convert, fund_dom_s, fund_dom_s.quotientMeasureEqMeasurePreimage, meas_U, measure_inter_null_of_null_right, measure_map_restrict_apply, quotientMeasureEqMeasurePreimage, vol_s, zero_apply
-/
theorem IsFundamentalDomain.quotientMeasureEqMeasurePreimage_of_zero
    {s : Set α} (fund_dom_s : IsFundamentalDomain G s ν)
    (vol_s : ν s = 0) :
    QuotientMeasureEqMeasurePreimage ν (0 : Measure (Quotient α_mod_G)) := by
  apply fund_dom_s.quotientMeasureEqMeasurePreimage
  ext U meas_U
  simp only [Measure.coe_zero, Pi.zero_apply]
  convert! (measure_inter_null_of_null_right (h := vol_s) (Quotient.mk α_mod_G ⁻¹' U)).symm
  rw [measure_map_restrict_apply (meas_U := meas_U)]

/-- If a measure `μ` on a quotient satisfies `QuotientMeasureEqMeasurePreimage` with respect to a
sigma-finite measure `ν`, then it is itself `SigmaFinite`. -/
@[to_additive /-- If a measure `μ` on a quotient satisfies `AddQuotientMeasureEqMeasurePreimage`
with respect to a sigma-finite measure `ν`, then it is itself `SigmaFinite`. -/]
/--
lemma `QuotientMeasureEqMeasurePreimage.sigmaFiniteQuotient` / 引理 `QuotientMeasureEqMeasurePreimage.sigmaFiniteQuotient`

English:
lemma QuotientMeasureEqMeasurePreimage.sigmaFiniteQuotient
  proof: by
  rw [sigmaFinite_iff]
  obtain ⟨A, hA_meas, hA, hA'⟩ := Measure.toFiniteSpanningSetsIn (h := i)
  simp only [mem_ofPred_eq] at hA_meas
  refine ⟨⟨fun n => π '' (A n), by simp, fun n => ?_, ?_⟩⟩
  · obtain ⟨s, fund_dom_s⟩ := i'
    have : π ⁻¹' π '' (A n) = _ := MulAction.quotient_preimage_image_eq_union_mul (A n) (G := G)
    have measπAn : MeasurableSet (π '' A n) := by
      rw [measurableSet_quotient]; rw [Quotient.mk''_eq_mk]; rw [this]
      apply MeasurableSet.iUnion
      exact fun g => MeasurableSet.const_smul (hA_meas n) g
    rw [fund_dom_s.projection_respects_measure_apply (μ := μ) measπAn]; rw [this]; rw [iUnion_inter]
    refine lt_of_le_of_lt ?_ (hA n)
    rw [fund_dom_s.measure_eq_tsum (A n)]
    exact measure_iUnion_le _
  · rw [← image_iUnion, hA']
    refine image_univ_of_surjective (by convert! Quotient.mk'_surjective)

中文:
引理 QuotientMeasureEqMeasurePreimage.sigmaFiniteQuotient
  证明: by
  rw [sigmaFinite_iff]
  obtain ⟨A, hA_meas, hA, hA'⟩ := Measure.toFiniteSpanningSetsIn (h := i)
  simp only [mem_ofPred_eq] at hA_meas
  refine ⟨⟨fun n => π '' (A n), by simp, fun n => ?_, ?_⟩⟩
  · obtain ⟨s, fund_dom_s⟩ := i'
    have : π ⁻¹' π '' (A n) = _ := MulAction.quotient_preimage_image_eq_union_mul (A n) (G := G)
    have measπAn : MeasurableSet (π '' A n) := by
      rw [measurableSet_quotient]; rw [Quotient.mk''_eq_mk]; rw [this]
      apply MeasurableSet.iUnion
      exact fun g => MeasurableSet.const_smul (hA_meas n) g
    rw [fund_dom_s.projection_respects_measure_apply (μ := μ) measπAn]; rw [this]; rw [iUnion_inter]
    refine lt_of_le_of_lt ?_ (hA n)
    rw [fund_dom_s.measure_eq_tsum (A n)]
    exact measure_iUnion_le _
  · rw [← image_iUnion, hA']
    refine image_univ_of_surjective (by convert! Quotient.mk'_surjective)

Depends on / 依赖: MeasurableSet, MeasurableSet.const_smul, MeasurableSet.iUnion, Measure, Measure.toFiniteSpanningSetsIn, MulAction, MulAction.quotient_preimage_image_eq_union_mul, Quotient, Quotient.mk, _eq_mk, const_smul, fund_dom_s, hA_meas, iUnion, measurableSet_quotient, mem_ofPred_eq, quotient_preimage_image_eq_union_mul, sigmaFinite_iff, toFiniteSpanningSetsIn
-/
lemma QuotientMeasureEqMeasurePreimage.sigmaFiniteQuotient
    [i : SigmaFinite ν] [i' : HasFundamentalDomain G α ν]
    (μ : Measure (Quotient α_mod_G)) [QuotientMeasureEqMeasurePreimage ν μ] :
    SigmaFinite μ := by
  rw [sigmaFinite_iff]
  obtain ⟨A, hA_meas, hA, hA'⟩ := Measure.toFiniteSpanningSetsIn (h := i)
  simp only [mem_ofPred_eq] at hA_meas
  refine ⟨⟨fun n => π '' (A n), by simp, fun n => ?_, ?_⟩⟩
  · obtain ⟨s, fund_dom_s⟩ := i'
    have : π ⁻¹' π '' (A n) = _ := MulAction.quotient_preimage_image_eq_union_mul (A n) (G := G)
    have measπAn : MeasurableSet (π '' A n) := by
      rw [measurableSet_quotient]; rw [Quotient.mk''_eq_mk]; rw [this]
      apply MeasurableSet.iUnion
      exact fun g => MeasurableSet.const_smul (hA_meas n) g
    rw [fund_dom_s.projection_respects_measure_apply (μ := μ) measπAn]; rw [this]; rw [iUnion_inter]
    refine lt_of_le_of_lt ?_ (hA n)
    rw [fund_dom_s.measure_eq_tsum (A n)]
    exact measure_iUnion_le _
  · rw [← image_iUnion, hA']
    refine image_univ_of_surjective (by convert! Quotient.mk'_surjective)

/-- A measure `μ` on `α ⧸ G` satisfying `QuotientMeasureEqMeasurePreimage` and having finite
covolume is a finite measure. -/
@[to_additive /-- A measure `μ` on the additive quotient of `α` by `G` satisfying
`AddQuotientMeasureEqMeasurePreimage` and having finite covolume is a finite measure. -/]
/--
theorem `QuotientMeasureEqMeasurePreimage.isFiniteMeasure_quotient` / 定理 `QuotientMeasureEqMeasurePreimage.isFiniteMeasure_quotient`

English:
theorem QuotientMeasureEqMeasurePreimage.isFiniteMeasure_quotient
  proof: by
  obtain ⟨𝓕, h𝓕⟩ := hasFun.ExistsIsFundamentalDomain
  rw [h𝓕.projection_respects_measure (μ := μ)]
  have : Fact (ν 𝓕 < ∞) := by
    apply Fact.mk
    convert! Ne.lt_top h
    exact (h𝓕.covolume_eq_volume ν).symm
  infer_instance

中文:
定理 QuotientMeasureEqMeasurePreimage.isFiniteMeasure_quotient
  证明: by
  obtain ⟨𝓕, h𝓕⟩ := hasFun.ExistsIsFundamentalDomain
  rw [h𝓕.projection_respects_measure (μ := μ)]
  have : Fact (ν 𝓕 < ∞) := by
    apply Fact.mk
    convert! Ne.lt_top h
    exact (h𝓕.covolume_eq_volume ν).symm
  infer_instance

Depends on / 依赖: ExistsIsFundamentalDomain, Fact.mk, Ne.lt_top, convert, covolume_eq_volume, hasFun, hasFun.ExistsIsFundamentalDomain, infer_instance, lt_top, projection_respects_measure
-/
theorem QuotientMeasureEqMeasurePreimage.isFiniteMeasure_quotient
    (μ : Measure (Quotient α_mod_G)) [QuotientMeasureEqMeasurePreimage ν μ]
    [hasFun : HasFundamentalDomain G α ν] (h : covolume G α ν != ∞) :
    IsFiniteMeasure μ := by
  obtain ⟨𝓕, h𝓕⟩ := hasFun.ExistsIsFundamentalDomain
  rw [h𝓕.projection_respects_measure (μ := μ)]
  have : Fact (ν 𝓕 < ∞) := by
    apply Fact.mk
    convert! Ne.lt_top h
    exact (h𝓕.covolume_eq_volume ν).symm
  infer_instance

/-- A finite measure `μ` on `α ⧸ G` satisfying `QuotientMeasureEqMeasurePreimage` has finite
covolume. -/
@[to_additive /-- A finite measure `μ` on the additive quotient of `α` by `G` satisfying
`AddQuotientMeasureEqMeasurePreimage` has finite covolume. -/]
/--
theorem `QuotientMeasureEqMeasurePreimage.covolume_ne_top` / 定理 `QuotientMeasureEqMeasurePreimage.covolume_ne_top`

English:
theorem QuotientMeasureEqMeasurePreimage.covolume_ne_top
  proof: by
  by_cases hasFun : HasFundamentalDomain G α ν
  · obtain ⟨𝓕, h𝓕⟩ := hasFun.ExistsIsFundamentalDomain
    have H : μ univ < ∞ := IsFiniteMeasure.measure_univ_lt_top
    rw [h𝓕.projection_respects_measure_apply (μ := μ) MeasurableSet.univ] at H
    simpa [h𝓕.covolume_eq_volume ν] using H
  · simp [covolume, hasFun]

中文:
定理 QuotientMeasureEqMeasurePreimage.covolume_ne_top
  证明: by
  by_cases hasFun : HasFundamentalDomain G α ν
  · obtain ⟨𝓕, h𝓕⟩ := hasFun.ExistsIsFundamentalDomain
    have H : μ univ < ∞ := IsFiniteMeasure.measure_univ_lt_top
    rw [h𝓕.projection_respects_measure_apply (μ := μ) MeasurableSet.univ] at H
    simpa [h𝓕.covolume_eq_volume ν] using H
  · simp [covolume, hasFun]

Depends on / 依赖: ExistsIsFundamentalDomain, HasFundamentalDomain, IsFiniteMeasure, IsFiniteMeasure.measure_univ_lt_top, MeasurableSet, MeasurableSet.univ, covolume, covolume_eq_volume, hasFun, hasFun.ExistsIsFundamentalDomain, measure_univ_lt_top, projection_respects_measure_apply
-/
theorem QuotientMeasureEqMeasurePreimage.covolume_ne_top
    (μ : Measure (Quotient α_mod_G)) [QuotientMeasureEqMeasurePreimage ν μ] [IsFiniteMeasure μ] :
    covolume G α ν < ∞ := by
  by_cases hasFun : HasFundamentalDomain G α ν
  · obtain ⟨𝓕, h𝓕⟩ := hasFun.ExistsIsFundamentalDomain
    have H : μ univ < ∞ := IsFiniteMeasure.measure_univ_lt_top
    rw [h𝓕.projection_respects_measure_apply (μ := μ) MeasurableSet.univ] at H
    simpa [h𝓕.covolume_eq_volume ν] using H
  · simp [covolume, hasFun]

end QuotientMeasureEqMeasurePreimage

section QuotientMeasureEqMeasurePreimage


variable [Group G] [MulAction G α] [MeasureSpace α] [Countable G]
  [SMulInvariantMeasure G α volume] [MeasurableConstSMul G α]

local notation "α_mod_G" => MulAction.orbitRel G α

local notation "π" => @Quotient.mk _ α_mod_G

/-- If a measure `μ` on a quotient satisfies `QuotientMeasureEqMeasurePreimage` with respect to a
sigma-finite measure, then it is itself `SigmaFinite`. -/
@[to_additive MeasureTheory.instSigmaFiniteAddQuotientOrbitRelInstMeasurableSpaceToMeasurableSpace
/-- If a measure `μ` on a quotient satisfies `AddQuotientMeasureEqMeasurePreimage` with respect to a
sigma-finite measure, then it is itself `SigmaFinite`. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SigmaFinite
  signature: (volume : Measure α)] [HasFundamentalDomain G α]
  body: QuotientMeasureEqMeasurePreimage.sigmaFiniteQuotient (ν := (volume : Measure α)) (μ := μ)

中文:
实例 [σ有限
  签名: (volume : 测度 α)] [有FundamentalDomain G α]
  定义体: QuotientMeasureEqMeasurePreimage.sigmaFiniteQuotient (ν := (volume : Measure α)) (μ := μ)

Depends on / 依赖: Measure, QuotientMeasureEqMeasurePreimage, QuotientMeasureEqMeasurePreimage.sigmaFiniteQuotient, sigmaFiniteQuotient, volume
-/
instance [SigmaFinite (volume : Measure α)] [HasFundamentalDomain G α]
    (μ : Measure (Quotient α_mod_G)) [QuotientMeasureEqMeasurePreimage volume μ] :
    SigmaFinite μ :=
  QuotientMeasureEqMeasurePreimage.sigmaFiniteQuotient (ν := (volume : Measure α)) (μ := μ)

end QuotientMeasureEqMeasurePreimage

end MeasureTheory
