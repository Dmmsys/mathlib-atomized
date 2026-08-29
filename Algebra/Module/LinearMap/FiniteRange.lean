/-
Copyright (c) 2026 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Anatole Dedecker, Yongxi Lin
-/
module

public import Mathlib.RingTheory.Finiteness.Cofinite
public import Mathlib.Algebra.Module.Submodule.EqLocus

/-!
# `HasFiniteRange` predicate on linear maps, and the associated equivalence relation

In this file, we define:

* `LinearMap.HasFiniteRange`: a predicate expressing that a linear map has finitely generated range.
* `LinearMap.HasNoetherianRange`: a predicate expressing that a linear map has noetherian range,
  i.e, all submodules of the range are finitely generated. This should be thought of as the
  "better behaved" version of `LinearMap.HasFiniteRange`: for example, `HasNoetherianRange`
  is always stable by addition, whereas `HasFiniteRange` might not be. The two notions agree
  over noetherian rings (hence, in particular, over fields).
* `LinearMap.finiteRange`: the submodule of `E →ₗ[K] F` consisting of linear maps with
  *noetherian* ranges. We allow ourself this slightly abusive name because the more natural
  definition (the submodule of linear maps with finitely generated ranges) only makes sense over a
  noetherian ring, in which case the two notions agree.
* `LinearMap.FiniteRangeSetoid.setoid`: the setoid on `E →ₗ[K] F` associated to
  `LinearMap.finiteRange`. This identifies linear maps which differ by a linear map with
  noetherian range. Equivalently, two linear maps are equivalent for this
  relation if and only if they agree on a subspace `A` of the domain such that `E ⧸ A` is
  noetherian. As with `LinearMap.finiteRange`, we allow ourself a slightly abusive name because the
  more natural definition in terms of `LinearMap.HasFiniteRange` is only well behaved over a
  noetherian ring, in which case the two notions agree.
  This is an instance in the scope `LinearMap.FiniteRangeSetoid`,
  so opening this scope allows this relation to be denoted by `≈`.
* `LinearMap.IsQuasiInverse`: two linear maps `u` and `v` are **quasi-inverses** if we have
  `u ∘ₗ v ≈ id` and `v ∘ₗ u ≈ id` modulo linear maps with noetherian ranges.

-/

@[expose] public section

open LinearMap Submodule Module

namespace LinearMap

variable {K V V' V₂ V₂' V₃ : Type*}

section Semiring

variable [Semiring K]
  [AddCommMonoid V] [Module K V]
  [AddCommMonoid V₂] [Module K V₂]
  [AddCommMonoid V₃] [Module K V₃]

/--
Definition of `HasNoetherianRange` / `HasNoetherianRange` 的定义

English:
definition HasNoetherianRange
  signature: (f : V ->ₗ[K] V₂)
  body: IsNoetherian K f.range

中文:
定义 HasNoetherianRange
  签名: (f : V ->ₗ[K] V₂)
  定义体: IsNoetherian K f.range

Depends on / 依赖: IsNoetherian, f.range
-/
def HasNoetherianRange (f : V ->ₗ[K] V₂) : Prop :=
  IsNoetherian K f.range

/--
Definition of `HasFiniteRange` / `HasFiniteRange` 的定义

English:
definition HasFiniteRange
  signature: (f : V ->ₗ[K] V₂)
  body: f.range.FG

中文:
定义 HasFiniteRange
  签名: (f : V ->ₗ[K] V₂)
  定义体: f.range.FG

Depends on / 依赖: f.range.FG
-/
def HasFiniteRange (f : V ->ₗ[K] V₂) : Prop :=
  f.range.FG

/--
lemma `hasNoetherianRange_iff_range` / 引理 `hasNoetherianRange_iff_range`

English:
lemma hasNoetherianRange_iff_range
  given: {f : V ->ₗ[K] V₂}
  proof: Iff.rfl

中文:
引理 hasNoetherianRange_iff_range
  条件: {f : V ->ₗ[K] V₂}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma hasNoetherianRange_iff_range {f : V ->ₗ[K] V₂} :
    f.HasNoetherianRange ↔ IsNoetherian K f.range :=
  Iff.rfl

/--
lemma `hasFiniteRange_iff_range` / 引理 `hasFiniteRange_iff_range`

English:
lemma hasFiniteRange_iff_range
  given: {f : V ->ₗ[K] V₂}
  proof: Iff.rfl

alias ⟨HasNoetherianRange.isNoetherian_range, _⟩ := hasNoetherianRange_iff_range
alias ⟨HasFiniteRange.fg_range, _⟩ := hasFiniteRange_iff_range

中文:
引理 hasFiniteRange_iff_range
  条件: {f : V ->ₗ[K] V₂}
  证明: Iff.rfl

alias ⟨HasNoetherianRange.isNoetherian_range, _⟩ := hasNoetherianRange_iff_range
alias ⟨HasFiniteRange.fg_range, _⟩ := hasFiniteRange_iff_range

Depends on / 依赖: Iff.rfl
-/
lemma hasFiniteRange_iff_range {f : V ->ₗ[K] V₂} :
    f.HasFiniteRange ↔ f.range.FG :=
  Iff.rfl

alias ⟨HasNoetherianRange.isNoetherian_range, _⟩ := hasNoetherianRange_iff_range
alias ⟨HasFiniteRange.fg_range, _⟩ := hasFiniteRange_iff_range

/--
lemma `HasNoetherianRange.hasFiniteRange` / 引理 `HasNoetherianRange.hasFiniteRange`

English:
lemma HasNoetherianRange.hasFiniteRange
  given: {u : V ->ₗ[K] V₂} (h : u.HasNoetherianRange)
  proof: have := h.isNoetherian_range; FG.of_finite

中文:
引理 HasNoetherianRange.hasFiniteRange
  条件: {u : V ->ₗ[K] V₂} (h : u.HasNoetherianRange)
  证明: have := h.isNoetherian_range; FG.of_finite

Depends on / 依赖: FG.of_finite, h.isNoetherian_range, isNoetherian_range, of_finite
-/
lemma HasNoetherianRange.hasFiniteRange {u : V ->ₗ[K] V₂} (h : u.HasNoetherianRange) :
    u.HasFiniteRange :=
  have := h.isNoetherian_range; FG.of_finite

/--
lemma `HasNoetherianRange.zero` / 引理 `HasNoetherianRange.zero`

English:
lemma HasNoetherianRange.zero
  statement: (0 : V ->ₗ[K] V₂).HasNoetherianRange
  proof: by
  simp [HasNoetherianRange, isNoetherian_submodule, Submodule.fg_bot]

中文:
引理 HasNoetherianRange.zero
  结论: (0 : V ->ₗ[K] V₂).HasNoetherianRange
  证明: by
  simp [HasNoetherianRange, isNoetherian_submodule, Submodule.fg_bot]
-/
@[simp] lemma HasNoetherianRange.zero : (0 : V ->ₗ[K] V₂).HasNoetherianRange := by
  simp [HasNoetherianRange, isNoetherian_submodule, Submodule.fg_bot]

/--
lemma `HasFiniteRange.zero` / 引理 `HasFiniteRange.zero`

English:
lemma HasFiniteRange.zero
  statement: (0 : V ->ₗ[K] V₂).HasFiniteRange
  proof: HasNoetherianRange.zero.hasFiniteRange

中文:
引理 HasFiniteRange.zero
  结论: (0 : V ->ₗ[K] V₂).HasFiniteRange
  证明: HasNoetherianRange.zero.hasFiniteRange
-/
@[simp] lemma HasFiniteRange.zero : (0 : V ->ₗ[K] V₂).HasFiniteRange :=
  HasNoetherianRange.zero.hasFiniteRange

/--
lemma `HasNoetherianRange.comp_left` / 引理 `HasNoetherianRange.comp_left`

English:
lemma HasNoetherianRange.comp_left
  statement: {u : V ->ₗ[K] V₂} (h : u.HasNoetherianRange)
  proof: by
  rw [LinearMap.HasNoetherianRange]; rw [LinearMap.range_comp] at *
  infer_instance

中文:
引理 HasNoetherianRange.comp_left
  结论: {u : V ->ₗ[K] V₂} (h : u.HasNoetherianRange)
  证明: by
  rw [LinearMap.HasNoetherianRange]; rw [LinearMap.range_comp] at *
  infer_instance

Depends on / 依赖: HasNoetherianRange, LinearMap, LinearMap.HasNoetherianRange, LinearMap.range_comp, infer_instance, range_comp
-/
lemma HasNoetherianRange.comp_left {u : V ->ₗ[K] V₂} (h : u.HasNoetherianRange)
    (v : V₂ ->ₗ[K] V₃) : (v ∘ₗ u).HasNoetherianRange := by
  rw [LinearMap.HasNoetherianRange]; rw [LinearMap.range_comp] at *
  infer_instance

/--
lemma `HasFiniteRange.comp_left` / 引理 `HasFiniteRange.comp_left`

English:
lemma HasFiniteRange.comp_left
  statement: {u : V ->ₗ[K] V₂} (h : u.HasFiniteRange)
  proof: by
  rw [LinearMap.HasFiniteRange]; rw [LinearMap.range_comp] at *
  exact Submodule.FG.map v h

中文:
引理 HasFiniteRange.comp_left
  结论: {u : V ->ₗ[K] V₂} (h : u.HasFiniteRange)
  证明: by
  rw [LinearMap.HasFiniteRange]; rw [LinearMap.range_comp] at *
  exact Submodule.FG.map v h

Depends on / 依赖: HasFiniteRange, LinearMap, LinearMap.HasFiniteRange, LinearMap.range_comp, Submodule, Submodule.FG.map, range_comp
-/
lemma HasFiniteRange.comp_left {u : V ->ₗ[K] V₂} (h : u.HasFiniteRange)
    (v : V₂ ->ₗ[K] V₃) : (v ∘ₗ u).HasFiniteRange := by
  rw [LinearMap.HasFiniteRange]; rw [LinearMap.range_comp] at *
  exact Submodule.FG.map v h

/--
lemma `HasNoetherianRange.of_isNoetherian_dom` / 引理 `HasNoetherianRange.of_isNoetherian_dom`

English:
lemma HasNoetherianRange.of_isNoetherian_dom
  given: [IsNoetherian K V] {f : V ->ₗ[K] V₂}
  proof: hasNoetherianRange_iff_range.mpr inferInstance

中文:
引理 HasNoetherianRange.of_isNoetherian_dom
  条件: [是Noether K V] {f : V ->ₗ[K] V₂}
  证明: hasNoetherianRange_iff_range.mpr inferInstance
-/
@[simp] lemma HasNoetherianRange.of_isNoetherian_dom [IsNoetherian K V] {f : V ->ₗ[K] V₂} :
    f.HasNoetherianRange :=
  hasNoetherianRange_iff_range.mpr inferInstance

/--
lemma `HasFiniteRange.of_finite_dom` / 引理 `HasFiniteRange.of_finite_dom`

English:
lemma HasFiniteRange.of_finite_dom
  given: [Module.Finite K V] {f : V ->ₗ[K] V₂}
  proof: by
  simp [HasFiniteRange]

中文:
引理 HasFiniteRange.of_finite_dom
  条件: [模.有限 K V] {f : V ->ₗ[K] V₂}
  证明: by
  simp [HasFiniteRange]
-/
@[simp] lemma HasFiniteRange.of_finite_dom [Module.Finite K V] {f : V ->ₗ[K] V₂} :
    f.HasFiniteRange := by
  simp [HasFiniteRange]

/--
lemma `HasNoetherianRange.of_isNoetherian_rng` / 引理 `HasNoetherianRange.of_isNoetherian_rng`

English:
lemma HasNoetherianRange.of_isNoetherian_rng
  given: [IsNoetherian K V₂] {f : V ->ₗ[K] V₂}
  proof: hasNoetherianRange_iff_range.mpr inferInstance

中文:
引理 HasNoetherianRange.of_isNoetherian_rng
  条件: [是Noether K V₂] {f : V ->ₗ[K] V₂}
  证明: hasNoetherianRange_iff_range.mpr inferInstance
-/
@[simp] lemma HasNoetherianRange.of_isNoetherian_rng [IsNoetherian K V₂] {f : V ->ₗ[K] V₂} :
    f.HasNoetherianRange :=
  hasNoetherianRange_iff_range.mpr inferInstance

/--
lemma `HasFiniteRange.of_isNoetherian_rng` / 引理 `HasFiniteRange.of_isNoetherian_rng`

English:
lemma HasFiniteRange.of_isNoetherian_rng
  given: [IsNoetherian K V₂] {f : V ->ₗ[K] V₂}
  proof: HasNoetherianRange.of_isNoetherian_rng.hasFiniteRange

中文:
引理 HasFiniteRange.of_isNoetherian_rng
  条件: [是Noether K V₂] {f : V ->ₗ[K] V₂}
  证明: HasNoetherianRange.of_isNoetherian_rng.hasFiniteRange
-/
@[simp] lemma HasFiniteRange.of_isNoetherian_rng [IsNoetherian K V₂] {f : V ->ₗ[K] V₂} :
    f.HasFiniteRange :=
  HasNoetherianRange.of_isNoetherian_rng.hasFiniteRange

end Semiring

section Ring

variable [Ring K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup V₂] [Module K V₂]
  [AddCommGroup V₃] [Module K V₃]

/--
lemma `HasFiniteRange.hasNoetherianRange` / 引理 `HasFiniteRange.hasNoetherianRange`

English:
lemma HasFiniteRange.hasNoetherianRange
  statement: [IsNoetherianRing K] {u : V ->ₗ[K] V₂}
  proof: by
  rw [HasNoetherianRange]
  have := Finite.of_fg h.fg_range
  infer_instance

中文:
引理 HasFiniteRange.hasNoetherianRange
  结论: [是Noether环 K] {u : V ->ₗ[K] V₂}
  证明: by
  rw [HasNoetherianRange]
  have := Finite.of_fg h.fg_range
  infer_instance

Depends on / 依赖: Finite, Finite.of_fg, HasNoetherianRange, fg_range, h.fg_range, infer_instance, of_fg
-/
lemma HasFiniteRange.hasNoetherianRange [IsNoetherianRing K] {u : V ->ₗ[K] V₂}
    (h : u.HasFiniteRange) : u.HasNoetherianRange := by
  rw [HasNoetherianRange]
  have := Finite.of_fg h.fg_range
  infer_instance

/--
lemma `hasNoetherianRange_iff_hasFiniteRange` / 引理 `hasNoetherianRange_iff_hasFiniteRange`

English:
lemma hasNoetherianRange_iff_hasFiniteRange
  given: [IsNoetherianRing K] {u : V ->ₗ[K] V₂}
  proof: ⟨HasNoetherianRange.hasFiniteRange, HasFiniteRange.hasNoetherianRange⟩

中文:
引理 hasNoetherianRange_iff_hasFiniteRange
  条件: [是Noether环 K] {u : V ->ₗ[K] V₂}
  证明: ⟨HasNoetherianRange.hasFiniteRange, HasFiniteRange.hasNoetherianRange⟩

Depends on / 依赖: HasFiniteRange, HasFiniteRange.hasNoetherianRange, HasNoetherianRange, HasNoetherianRange.hasFiniteRange, hasFiniteRange, hasNoetherianRange
-/
lemma hasNoetherianRange_iff_hasFiniteRange [IsNoetherianRing K] {u : V ->ₗ[K] V₂} :
    u.HasNoetherianRange ↔ u.HasFiniteRange :=
  ⟨HasNoetherianRange.hasFiniteRange, HasFiniteRange.hasNoetherianRange⟩

/--
lemma `HasNoetherianRange.comp_right` / 引理 `HasNoetherianRange.comp_right`

English:
lemma HasNoetherianRange.comp_right
  statement: {v : V₂ ->ₗ[K] V₃} (h : v.HasNoetherianRange)
  proof: by
  rw [HasNoetherianRange]; rw [LinearMap.range_comp] at *
  exact isNoetherian_of_le map_le_range

中文:
引理 HasNoetherianRange.comp_right
  结论: {v : V₂ ->ₗ[K] V₃} (h : v.HasNoetherianRange)
  证明: by
  rw [HasNoetherianRange]; rw [LinearMap.range_comp] at *
  exact isNoetherian_of_le map_le_range

Depends on / 依赖: HasNoetherianRange, LinearMap, LinearMap.range_comp, isNoetherian_of_le, map_le_range, range_comp
-/
lemma HasNoetherianRange.comp_right {v : V₂ ->ₗ[K] V₃} (h : v.HasNoetherianRange)
    (u : V ->ₗ[K] V₂) : (v ∘ₗ u).HasNoetherianRange := by
  rw [HasNoetherianRange]; rw [LinearMap.range_comp] at *
  exact isNoetherian_of_le map_le_range

/--
lemma `HasFiniteRange.comp_right` / 引理 `HasFiniteRange.comp_right`

English:
lemma HasFiniteRange.comp_right
  statement: [IsNoetherianRing K] {v : V₂ ->ₗ[K] V₃} (h : v.HasFiniteRange)
  proof: .hasFiniteRange h.hasNoetherianRange.comp_right _

中文:
引理 HasFiniteRange.comp_right
  结论: [是Noether环 K] {v : V₂ ->ₗ[K] V₃} (h : v.HasFiniteRange)
  证明: .hasFiniteRange h.hasNoetherianRange.comp_right _

Depends on / 依赖: comp_right, h.hasNoetherianRange.comp_right, hasFiniteRange, hasNoetherianRange
-/
lemma HasFiniteRange.comp_right [IsNoetherianRing K] {v : V₂ ->ₗ[K] V₃} (h : v.HasFiniteRange)
    (u : V ->ₗ[K] V₂) : (v ∘ₗ u).HasFiniteRange :=
.hasFiniteRange h.hasNoetherianRange.comp_right _

/--
lemma `HasNoetherianRange.neg` / 引理 `HasNoetherianRange.neg`

English:
lemma HasNoetherianRange.neg
  statement: {f : V ->ₗ[K] V₂}
  proof: by
  rwa [HasNoetherianRange, LinearMap.range_neg]

中文:
引理 HasNoetherianRange.neg
  结论: {f : V ->ₗ[K] V₂}
  证明: by
  rwa [HasNoetherianRange, LinearMap.range_neg]
-/
@[simp] lemma HasNoetherianRange.neg {f : V ->ₗ[K] V₂}
    (hf : f.HasNoetherianRange) : (-f).HasNoetherianRange := by
  rwa [HasNoetherianRange, LinearMap.range_neg]

/--
lemma `HasFiniteRange.neg` / 引理 `HasFiniteRange.neg`

English:
lemma HasFiniteRange.neg
  statement: {f : V ->ₗ[K] V₂}
  proof: by
  rwa [HasFiniteRange, LinearMap.range_neg]

中文:
引理 HasFiniteRange.neg
  结论: {f : V ->ₗ[K] V₂}
  证明: by
  rwa [HasFiniteRange, LinearMap.range_neg]
-/
@[simp] lemma HasFiniteRange.neg {f : V ->ₗ[K] V₂}
    (hf : f.HasFiniteRange) : (-f).HasFiniteRange := by
  rwa [HasFiniteRange, LinearMap.range_neg]

/--
lemma `HasNoetherianRange.add` / 引理 `HasNoetherianRange.add`

English:
lemma HasNoetherianRange.add
  statement: {f g : V ->ₗ[K] V₂}
  proof: by
  rw [HasNoetherianRange] at *
  exact isNoetherian_of_le (range_add_le f g)

中文:
引理 HasNoetherianRange.add
  结论: {f g : V ->ₗ[K] V₂}
  证明: by
  rw [HasNoetherianRange] at *
  exact isNoetherian_of_le (range_add_le f g)
-/
@[simp] lemma HasNoetherianRange.add {f g : V ->ₗ[K] V₂}
    (hf : f.HasNoetherianRange) (hg : g.HasNoetherianRange) : (f + g).HasNoetherianRange := by
  rw [HasNoetherianRange] at *
  exact isNoetherian_of_le (range_add_le f g)

/--
lemma `HasFiniteRange.add` / 引理 `HasFiniteRange.add`

English:
lemma HasFiniteRange.add
  statement: [IsNoetherianRing K] {f g : V ->ₗ[K] V₂}
  proof: .hasFiniteRange hf.hasNoetherianRange.add hg.hasNoetherianRange

中文:
引理 HasFiniteRange.add
  结论: [是Noether环 K] {f g : V ->ₗ[K] V₂}
  证明: .hasFiniteRange hf.hasNoetherianRange.add hg.hasNoetherianRange
-/
@[simp] lemma HasFiniteRange.add [IsNoetherianRing K] {f g : V ->ₗ[K] V₂}
    (hf : f.HasFiniteRange) (hg : g.HasFiniteRange) : (f + g).HasFiniteRange :=
.hasFiniteRange hf.hasNoetherianRange.add hg.hasNoetherianRange

/--
lemma `HasNoetherianRange.sub` / 引理 `HasNoetherianRange.sub`

English:
lemma HasNoetherianRange.sub
  statement: {f g : V ->ₗ[K] V₂}
  proof: sub_eq_add_neg f g ▸ hf.add hg.neg

中文:
引理 HasNoetherianRange.sub
  结论: {f g : V ->ₗ[K] V₂}
  证明: sub_eq_add_neg f g ▸ hf.add hg.neg
-/
@[simp] lemma HasNoetherianRange.sub {f g : V ->ₗ[K] V₂}
    (hf : f.HasNoetherianRange) (hg : g.HasNoetherianRange) : (f - g).HasNoetherianRange :=
  sub_eq_add_neg f g ▸ hf.add hg.neg

/--
lemma `HasFiniteRange.sub` / 引理 `HasFiniteRange.sub`

English:
lemma HasFiniteRange.sub
  statement: [IsNoetherianRing K] {f g : V ->ₗ[K] V₂}
  proof: sub_eq_add_neg f g ▸ hf.add hg.neg

中文:
引理 HasFiniteRange.sub
  结论: [是Noether环 K] {f g : V ->ₗ[K] V₂}
  证明: sub_eq_add_neg f g ▸ hf.add hg.neg
-/
@[simp] lemma HasFiniteRange.sub [IsNoetherianRing K] {f g : V ->ₗ[K] V₂}
    (hf : f.HasFiniteRange) (hg : g.HasFiniteRange) : (f - g).HasFiniteRange :=
  sub_eq_add_neg f g ▸ hf.add hg.neg

/--
theorem `hasNoetherianRange_iff_quotient_ker` / 定理 `hasNoetherianRange_iff_quotient_ker`

English:
theorem hasNoetherianRange_iff_quotient_ker
  given: {f : V ->ₗ[K] V₂}
  proof: f.quotKerEquivRange.isNoetherian_iff.symm

@[simp]

中文:
定理 hasNoetherianRange_iff_quotient_ker
  条件: {f : V ->ₗ[K] V₂}
  证明: f.quotKerEquivRange.isNoetherian_iff.symm

@[simp]

Depends on / 依赖: f.quotKerEquivRange.isNoetherian_iff.symm, isNoetherian_iff, quotKerEquivRange
-/
theorem hasNoetherianRange_iff_quotient_ker {f : V ->ₗ[K] V₂} :
    f.HasNoetherianRange ↔ IsNoetherian K (V ⧸ f.ker) :=
  f.quotKerEquivRange.isNoetherian_iff.symm

@[simp]
/--
theorem `ker_coFG_iff_hasFiniteRange` / 定理 `ker_coFG_iff_hasFiniteRange`

English:
theorem ker_coFG_iff_hasFiniteRange
  given: {f : V ->ₗ[K] V₂}
  proof: range_fg_iff_ker_cofg.symm

alias ⟨HasNoetherianRange.quotient_ker, _⟩ := hasNoetherianRange_iff_quotient_ker
alias ⟨_, HasFiniteRange.cofg_ker⟩ := ker_coFG_iff_hasFiniteRange

中文:
定理 ker_coFG_iff_hasFiniteRange
  条件: {f : V ->ₗ[K] V₂}
  证明: range_fg_iff_ker_cofg.symm

alias ⟨HasNoetherianRange.quotient_ker, _⟩ := hasNoetherianRange_iff_quotient_ker
alias ⟨_, HasFiniteRange.cofg_ker⟩ := ker_coFG_iff_hasFiniteRange

Depends on / 依赖: range_fg_iff_ker_cofg, range_fg_iff_ker_cofg.symm
-/
theorem ker_coFG_iff_hasFiniteRange {f : V ->ₗ[K] V₂} :
    f.ker.CoFG ↔ f.HasFiniteRange :=
  range_fg_iff_ker_cofg.symm

alias ⟨HasNoetherianRange.quotient_ker, _⟩ := hasNoetherianRange_iff_quotient_ker
alias ⟨_, HasFiniteRange.cofg_ker⟩ := ker_coFG_iff_hasFiniteRange

end Ring

section CommRing

variable [CommRing K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup V₂] [Module K V₂]
  [AddCommGroup V₃] [Module K V₃]

/--
lemma `HasNoetherianRange.smul` / 引理 `HasNoetherianRange.smul`

English:
lemma HasNoetherianRange.smul
  statement: {f : V ->ₗ[K] V₂}
  proof: hf.comp_left (lsmul K V₂ c)

中文:
引理 HasNoetherianRange.smul
  结论: {f : V ->ₗ[K] V₂}
  证明: hf.comp_left (lsmul K V₂ c)
-/
@[simp] lemma HasNoetherianRange.smul {f : V ->ₗ[K] V₂}
    (hf : f.HasNoetherianRange) (c : K) : (c • f).HasNoetherianRange :=
  hf.comp_left (lsmul K V₂ c)

/--
lemma `HasFiniteRange.smul` / 引理 `HasFiniteRange.smul`

English:
lemma HasFiniteRange.smul
  statement: {f : V ->ₗ[K] V₂}
  proof: hf.comp_left (lsmul K V₂ c)

中文:
引理 HasFiniteRange.smul
  结论: {f : V ->ₗ[K] V₂}
  证明: hf.comp_left (lsmul K V₂ c)
-/
@[simp] lemma HasFiniteRange.smul {f : V ->ₗ[K] V₂}
    (hf : f.HasFiniteRange) (c : K) : (c • f).HasFiniteRange :=
  hf.comp_left (lsmul K V₂ c)

variable (K V V₂) in
/--
Definition of `finiteRange` / `finiteRange` 的定义

English:
definition finiteRange
  signature: : Submodule K (V ->ₗ[K] V₂) where
  body: {u | u.HasNoetherianRange}
  add_mem' hu hv := by simp_all
  zero_mem' := by simp
  smul_mem' c hu := by simp_all

中文:
定义 finiteRange
  签名: : 子模 K (V ->ₗ[K] V₂) where
  定义体: {u | u.HasNoetherianRange}
  add_mem' hu hv := by simp_all
  zero_mem' := by simp
  smul_mem' c hu := by simp_all

Depends on / 依赖: HasNoetherianRange, u.HasNoetherianRange
-/
def finiteRange : Submodule K (V ->ₗ[K] V₂) where
  carrier := {u | u.HasNoetherianRange}
  add_mem' hu hv := by simp_all
  zero_mem' := by simp
  smul_mem' c hu := by simp_all

/--
lemma `mem_finiteRange_iff_hasNoetherianRange` / 引理 `mem_finiteRange_iff_hasNoetherianRange`

English:
lemma mem_finiteRange_iff_hasNoetherianRange
  given: {f : V ->ₗ[K] V₂}
  proof: Iff.rfl

中文:
引理 mem_finiteRange_iff_hasNoetherianRange
  条件: {f : V ->ₗ[K] V₂}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_finiteRange_iff_hasNoetherianRange {f : V ->ₗ[K] V₂} :
    f in finiteRange K V V₂ ↔ f.HasNoetherianRange :=
  Iff.rfl

/--
lemma `mem_finiteRange_iff_hasFiniteRange` / 引理 `mem_finiteRange_iff_hasFiniteRange`

English:
lemma mem_finiteRange_iff_hasFiniteRange
  given: [IsNoetherianRing K] {f : V ->ₗ[K] V₂}
  proof: by
  rw [mem_finiteRange_iff_hasNoetherianRange]; rw [hasNoetherianRange_iff_hasFiniteRange]

中文:
引理 mem_finiteRange_iff_hasFiniteRange
  条件: [是Noether环 K] {f : V ->ₗ[K] V₂}
  证明: by
  rw [mem_finiteRange_iff_hasNoetherianRange]; rw [hasNoetherianRange_iff_hasFiniteRange]

Depends on / 依赖: hasNoetherianRange_iff_hasFiniteRange, mem_finiteRange_iff_hasNoetherianRange
-/
lemma mem_finiteRange_iff_hasFiniteRange [IsNoetherianRing K] {f : V ->ₗ[K] V₂} :
    f in finiteRange K V V₂ ↔ f.HasFiniteRange := by
  rw [mem_finiteRange_iff_hasNoetherianRange]; rw [hasNoetherianRange_iff_hasFiniteRange]

end CommRing

section Setoid

variable [CommRing K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup V₂] [Module K V₂]
  [AddCommGroup V₃] [Module K V₃]

namespace FiniteRangeSetoid

/-- This is the equivalence relation on linear maps such that `u ≈ v` precisely
when `u - v` is a linear map with noetherian range. We allow ourself this slightly abusive name
because the more natural definition (`u - v` has finitely generated range) only yields a
well-behaved relation (more precisely, an additive congruence relation compatible with composition
on both sides) over a noetherian ring, in which case the two notions agree.

This setoid is declared as an instance in scope `LinearMap.FiniteRangeSetoid`. -/
scoped instance setoid : Setoid (V ->ₗ[K] V₂) := (LinearMap.finiteRange K V V₂).quotientRel

/--
lemma `equiv_iff_hasNoetherianRange` / 引理 `equiv_iff_hasNoetherianRange`

English:
lemma equiv_iff_hasNoetherianRange
  given: {u v : V ->ₗ[K] V₂}
  statement: u ≈ v ↔ (u - v).HasNoetherianRange
  proof: Submodule.quotientRel_def _

中文:
引理 equiv_iff_hasNoetherianRange
  条件: {u v : V ->ₗ[K] V₂}
  结论: u ≈ v ↔ (u - v).HasNoetherianRange
  证明: Submodule.quotientRel_def _

Depends on / 依赖: Submodule, Submodule.quotientRel_def, quotientRel_def
-/
lemma equiv_iff_hasNoetherianRange {u v : V ->ₗ[K] V₂} : u ≈ v ↔ (u - v).HasNoetherianRange :=
  Submodule.quotientRel_def _

/--
lemma `equiv_iff_hasFiniteRange` / 引理 `equiv_iff_hasFiniteRange`

English:
lemma equiv_iff_hasFiniteRange
  given: [IsNoetherianRing K] {u v : V ->ₗ[K] V₂}
  proof: by
  rw [equiv_iff_hasNoetherianRange]; rw [hasNoetherianRange_iff_hasFiniteRange]

中文:
引理 equiv_iff_hasFiniteRange
  条件: [是Noether环 K] {u v : V ->ₗ[K] V₂}
  证明: by
  rw [equiv_iff_hasNoetherianRange]; rw [hasNoetherianRange_iff_hasFiniteRange]

Depends on / 依赖: equiv_iff_hasNoetherianRange, hasNoetherianRange_iff_hasFiniteRange
-/
lemma equiv_iff_hasFiniteRange [IsNoetherianRing K] {u v : V ->ₗ[K] V₂} :
    u ≈ v ↔ (u - v).HasFiniteRange := by
  rw [equiv_iff_hasNoetherianRange]; rw [hasNoetherianRange_iff_hasFiniteRange]

/--
lemma `equiv_zero_iff_hasNoetherianRange` / 引理 `equiv_zero_iff_hasNoetherianRange`

English:
lemma equiv_zero_iff_hasNoetherianRange
  given: {u : V ->ₗ[K] V₂}
  statement: u ≈ 0 ↔ u.HasNoetherianRange
  proof: by
  simp [equiv_iff_hasNoetherianRange]

中文:
引理 equiv_zero_iff_hasNoetherianRange
  条件: {u : V ->ₗ[K] V₂}
  结论: u ≈ 0 ↔ u.HasNoetherianRange
  证明: by
  simp [equiv_iff_hasNoetherianRange]

Depends on / 依赖: equiv_iff_hasNoetherianRange
-/
lemma equiv_zero_iff_hasNoetherianRange {u : V ->ₗ[K] V₂} : u ≈ 0 ↔ u.HasNoetherianRange := by
  simp [equiv_iff_hasNoetherianRange]

/--
lemma `equiv_zero_iff_hasFiniteRange` / 引理 `equiv_zero_iff_hasFiniteRange`

English:
lemma equiv_zero_iff_hasFiniteRange
  given: [IsNoetherianRing K] {u : V ->ₗ[K] V₂}
  proof: by
  simp [equiv_iff_hasFiniteRange]

中文:
引理 equiv_zero_iff_hasFiniteRange
  条件: [是Noether环 K] {u : V ->ₗ[K] V₂}
  证明: by
  simp [equiv_iff_hasFiniteRange]

Depends on / 依赖: equiv_iff_hasFiniteRange
-/
lemma equiv_zero_iff_hasFiniteRange [IsNoetherianRing K] {u : V ->ₗ[K] V₂} :
    u ≈ 0 ↔ u.HasFiniteRange := by
  simp [equiv_iff_hasFiniteRange]

/--
lemma `equiv_iff_isNoetherian_quotient_eqLocus` / 引理 `equiv_iff_isNoetherian_quotient_eqLocus`

English:
lemma equiv_iff_isNoetherian_quotient_eqLocus
  given: {u v : V ->ₗ[K] V₂}
  proof: by
  rw [equiv_iff_hasNoetherianRange]; rw [hasNoetherianRange_iff_quotient_ker]; rw [eqLocus_eq_ker_sub]

中文:
引理 equiv_iff_isNoetherian_quotient_eqLocus
  条件: {u v : V ->ₗ[K] V₂}
  证明: by
  rw [equiv_iff_hasNoetherianRange]; rw [hasNoetherianRange_iff_quotient_ker]; rw [eqLocus_eq_ker_sub]

Depends on / 依赖: eqLocus_eq_ker_sub, equiv_iff_hasNoetherianRange, hasNoetherianRange_iff_quotient_ker
-/
lemma equiv_iff_isNoetherian_quotient_eqLocus {u v : V ->ₗ[K] V₂} :
    u ≈ v ↔ IsNoetherian K (V ⧸ eqLocus u v) := by
  rw [equiv_iff_hasNoetherianRange]; rw [hasNoetherianRange_iff_quotient_ker]; rw [eqLocus_eq_ker_sub]

/--
lemma `equiv_iff_eqLocus_coFG` / 引理 `equiv_iff_eqLocus_coFG`

English:
lemma equiv_iff_eqLocus_coFG
  given: [IsNoetherianRing K] {u v : V ->ₗ[K] V₂}
  proof: by
  rw [eqLocus_eq_ker_sub]; rw [ker_coFG_iff_hasFiniteRange]; rw [equiv_iff_hasFiniteRange]

中文:
引理 equiv_iff_eqLocus_coFG
  条件: [是Noether环 K] {u v : V ->ₗ[K] V₂}
  证明: by
  rw [eqLocus_eq_ker_sub]; rw [ker_coFG_iff_hasFiniteRange]; rw [equiv_iff_hasFiniteRange]

Depends on / 依赖: eqLocus_eq_ker_sub, equiv_iff_hasFiniteRange, ker_coFG_iff_hasFiniteRange
-/
lemma equiv_iff_eqLocus_coFG [IsNoetherianRing K] {u v : V ->ₗ[K] V₂} :
    u ≈ v ↔ (eqLocus u v).CoFG := by
  rw [eqLocus_eq_ker_sub]; rw [ker_coFG_iff_hasFiniteRange]; rw [equiv_iff_hasFiniteRange]

/--
lemma `equiv_of_eqOn_of_isNoetherian` / 引理 `equiv_of_eqOn_of_isNoetherian`

English:
lemma equiv_of_eqOn_of_isNoetherian
  statement: {u v : V ->ₗ[K] V₂} (A : Submodule K V)
  proof: by
  have A_le : A <= eqLocus u v := le_eqLocus.mpr eqOn_A
  rw [equiv_iff_isNoetherian_quotient_eqLocus]
  refine isNoetherian_of_surjective (A.mapQ (eqLocus u v) id A_le) (by simp [range_mapQ])

中文:
引理 equiv_of_eqOn_of_isNoetherian
  结论: {u v : V ->ₗ[K] V₂} (A : 子模 K V)
  证明: by
  have A_le : A <= eqLocus u v := le_eqLocus.mpr eqOn_A
  rw [equiv_iff_isNoetherian_quotient_eqLocus]
  refine isNoetherian_of_surjective (A.mapQ (eqLocus u v) id A_le) (by simp [range_mapQ])

Depends on / 依赖: A.mapQ, A_le, eqLocus, eqOn_A, equiv_iff_isNoetherian_quotient_eqLocus, isNoetherian_of_surjective, le_eqLocus, le_eqLocus.mpr, range_mapQ
-/
lemma equiv_of_eqOn_of_isNoetherian {u v : V ->ₗ[K] V₂} (A : Submodule K V)
    [quot_A_noeth : IsNoetherian K (V ⧸ A)] (eqOn_A : Set.EqOn u v A) : u ≈ v := by
  have A_le : A <= eqLocus u v := le_eqLocus.mpr eqOn_A
  rw [equiv_iff_isNoetherian_quotient_eqLocus]
  refine isNoetherian_of_surjective (A.mapQ (eqLocus u v) id A_le) (by simp [range_mapQ])

/--
lemma `equiv_of_eqOn_coFG` / 引理 `equiv_of_eqOn_coFG`

English:
lemma equiv_of_eqOn_coFG
  statement: [IsNoetherianRing K] {u v : V ->ₗ[K] V₂} {A : Submodule K V}
  proof: equiv_iff_eqLocus_coFG.mpr A_coFG.of_le le_eqLocus.mpr eqOn_A

@[gcongr]

中文:
引理 equiv_of_eqOn_coFG
  结论: [是Noether环 K] {u v : V ->ₗ[K] V₂} {A : 子模 K V}
  证明: equiv_iff_eqLocus_coFG.mpr A_coFG.of_le le_eqLocus.mpr eqOn_A

@[gcongr]

Depends on / 依赖: A_coFG, A_coFG.of_le, Finsupp, Finsupp.erase_add_single, eqOn_A, equiv_iff_eqLocus_coFG, equiv_iff_eqLocus_coFG.mpr, erase_add_single, le_eqLocus, le_eqLocus.mpr, of_le
-/
lemma equiv_of_eqOn_coFG [IsNoetherianRing K] {u v : V ->ₗ[K] V₂} {A : Submodule K V}
    (A_coFG : A.CoFG) (eqOn_A : Set.EqOn u v A) : u ≈ v :=
equiv_iff_eqLocus_coFG.mpr A_coFG.of_le le_eqLocus.mpr eqOn_A

@[gcongr]
/--
lemma `equiv_comp_right` / 引理 `equiv_comp_right`

English:
lemma equiv_comp_right
  given: {u : V ->ₗ[K] V₂} {v v' : V₂ ->ₗ[K] V₃} (h' : v ≈ v')
  proof: by
  rw [equiv_iff_hasNoetherianRange] at *
  exact h'.comp_right u

@[gcongr]

中文:
引理 equiv_comp_right
  条件: {u : V ->ₗ[K] V₂} {v v' : V₂ ->ₗ[K] V₃} (h' : v ≈ v')
  证明: by
  rw [equiv_iff_hasNoetherianRange] at *
  exact h'.comp_right u

@[gcongr]

Depends on / 依赖: comp_right, equiv_iff_hasNoetherianRange
-/
lemma equiv_comp_right {u : V ->ₗ[K] V₂} {v v' : V₂ ->ₗ[K] V₃} (h' : v ≈ v') :
    v ∘ₗ u ≈ v' ∘ₗ u := by
  rw [equiv_iff_hasNoetherianRange] at *
  exact h'.comp_right u

@[gcongr]
/--
lemma `equiv_comp_left` / 引理 `equiv_comp_left`

English:
lemma equiv_comp_left
  given: {u v : V ->ₗ[K] V₂} {u' : V₂ ->ₗ[K] V₃} (h : u ≈ v)
  proof: by
  rw [equiv_iff_hasNoetherianRange] at *
  simpa only [LinearMap.comp_sub] using h.comp_left u'

中文:
引理 equiv_comp_left
  条件: {u v : V ->ₗ[K] V₂} {u' : V₂ ->ₗ[K] V₃} (h : u ≈ v)
  证明: by
  rw [equiv_iff_hasNoetherianRange] at *
  simpa only [LinearMap.comp_sub] using h.comp_left u'

Depends on / 依赖: LinearMap, LinearMap.comp_sub, comp_left, comp_sub, equiv_iff_hasNoetherianRange, h.comp_left
-/
lemma equiv_comp_left {u v : V ->ₗ[K] V₂} {u' : V₂ ->ₗ[K] V₃} (h : u ≈ v) :
    u' ∘ₗ u ≈ u' ∘ₗ v := by
  rw [equiv_iff_hasNoetherianRange] at *
  simpa only [LinearMap.comp_sub] using h.comp_left u'

/--
lemma `equiv_comp` / 引理 `equiv_comp`

English:
lemma equiv_comp
  given: {u v : V ->ₗ[K] V₂} {u' v' : V₂ ->ₗ[K] V₃} (h : u ≈ v) (h' : u' ≈ v')
  proof: by
  grw [equiv_comp_right h', equiv_comp_left h]

中文:
引理 equiv_comp
  条件: {u v : V ->ₗ[K] V₂} {u' v' : V₂ ->ₗ[K] V₃} (h : u ≈ v) (h' : u' ≈ v')
  证明: by
  grw [equiv_comp_right h', equiv_comp_left h]

Depends on / 依赖: equiv_comp_left, equiv_comp_right
-/
lemma equiv_comp {u v : V ->ₗ[K] V₂} {u' v' : V₂ ->ₗ[K] V₃} (h : u ≈ v) (h' : u' ≈ v') :
    u' ∘ₗ u ≈ v' ∘ₗ v := by
  grw [equiv_comp_right h', equiv_comp_left h]

/--
lemma `projection_equiv_zero_iff_isNoetherian` / 引理 `projection_equiv_zero_iff_isNoetherian`

English:
lemma projection_equiv_zero_iff_isNoetherian
  given: {S T : Submodule K V} (hST : IsCompl S T)
  proof: by
  rw [equiv_zero_iff_hasNoetherianRange]; rw [hasNoetherianRange_iff_range]; rw [range_projection]

中文:
引理 projection_equiv_zero_iff_isNoetherian
  条件: {S T : 子模 K V} (hST : 是补集 S T)
  证明: by
  rw [equiv_zero_iff_hasNoetherianRange]; rw [hasNoetherianRange_iff_range]; rw [range_projection]

Depends on / 依赖: equiv_zero_iff_hasNoetherianRange, hasNoetherianRange_iff_range, range_projection
-/
lemma projection_equiv_zero_iff_isNoetherian {S T : Submodule K V} (hST : IsCompl S T) :
    S.projection T hST ≈ 0 ↔ IsNoetherian K S := by
  rw [equiv_zero_iff_hasNoetherianRange]; rw [hasNoetherianRange_iff_range]; rw [range_projection]

/--
lemma `projection_equiv_zero` / 引理 `projection_equiv_zero`

English:
lemma projection_equiv_zero
  given: {S T : Submodule K V} [IsNoetherian K S] (hST : IsCompl S T)
  proof: .mpr inferInstance projection_equiv_zero_iff_isNoetherian hST

中文:
引理 projection_equiv_zero
  条件: {S T : 子模 K V} [是Noether K S] (hST : 是补集 S T)
  证明: .mpr inferInstance projection_equiv_zero_iff_isNoetherian hST

Depends on / 依赖: projection_equiv_zero_iff_isNoetherian
-/
lemma projection_equiv_zero {S T : Submodule K V} [IsNoetherian K S] (hST : IsCompl S T) :
    S.projection T hST ≈ 0 :=
.mpr inferInstance projection_equiv_zero_iff_isNoetherian hST

/--
lemma `projection_equiv_id_iff_isNoetherian` / 引理 `projection_equiv_id_iff_isNoetherian`

English:
lemma projection_equiv_id_iff_isNoetherian
  given: {S T : Submodule K V} (hST : IsCompl S T)
  proof: by
  rw [Setoid.comm]; rw [equiv_iff_hasNoetherianRange]; rw [← projection_eq_id_sub_projection]; rw [hasNoetherianRange_iff_range]; rw [range_projection]

中文:
引理 projection_equiv_id_iff_isNoetherian
  条件: {S T : 子模 K V} (hST : 是补集 S T)
  证明: by
  rw [Setoid.comm]; rw [equiv_iff_hasNoetherianRange]; rw [← projection_eq_id_sub_projection]; rw [hasNoetherianRange_iff_range]; rw [range_projection]

Depends on / 依赖: Setoid, Setoid.comm, equiv_iff_hasNoetherianRange, hasNoetherianRange_iff_range, projection_eq_id_sub_projection, range_projection
-/
lemma projection_equiv_id_iff_isNoetherian {S T : Submodule K V} (hST : IsCompl S T) :
    S.projection T hST ≈ id ↔ IsNoetherian K T := by
  rw [Setoid.comm]; rw [equiv_iff_hasNoetherianRange]; rw [← projection_eq_id_sub_projection]; rw [hasNoetherianRange_iff_range]; rw [range_projection]

/--
lemma `projection_equiv_id` / 引理 `projection_equiv_id`

English:
lemma projection_equiv_id
  given: {S T : Submodule K V} [IsNoetherian K T] (hST : IsCompl S T)
  proof: .mpr inferInstance projection_equiv_id_iff_isNoetherian hST

中文:
引理 projection_equiv_id
  条件: {S T : 子模 K V} [是Noether K T] (hST : 是补集 S T)
  证明: .mpr inferInstance projection_equiv_id_iff_isNoetherian hST

Depends on / 依赖: projection_equiv_id_iff_isNoetherian
-/
lemma projection_equiv_id {S T : Submodule K V} [IsNoetherian K T] (hST : IsCompl S T) :
    S.projection T hST ≈ id :=
.mpr inferInstance projection_equiv_id_iff_isNoetherian hST

end FiniteRangeSetoid

end Setoid

section QuasiInverse

variable [CommRing K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup V₂] [Module K V₂]
  [AddCommGroup V₃] [Module K V₃]

open scoped LinearMap.FiniteRangeSetoid

/--
Definition of `IsLeftQuasiInverse` / `IsLeftQuasiInverse` 的定义

English:
definition IsLeftQuasiInverse
  signature: (u : V ->ₗ[K] V₂) (v : V₂ ->ₗ[K] V)
  body: u ∘ₗ v ≈ .id

中文:
定义 IsLeftQuasiInverse
  签名: (u : V ->ₗ[K] V₂) (v : V₂ ->ₗ[K] V)
  定义体: u ∘ₗ v ≈ .id
-/
def IsLeftQuasiInverse (u : V ->ₗ[K] V₂) (v : V₂ ->ₗ[K] V) : Prop :=
  u ∘ₗ v ≈ .id

/--
Definition of `IsRightQuasiInverse` / `IsRightQuasiInverse` 的定义

English:
definition IsRightQuasiInverse
  signature: (u : V₃ ->ₗ[K] V₂) (v : V₂ ->ₗ[K] V₃)
  body: v ∘ₗ u ≈ .id

中文:
定义 IsRightQuasiInverse
  签名: (u : V₃ ->ₗ[K] V₂) (v : V₂ ->ₗ[K] V₃)
  定义体: v ∘ₗ u ≈ .id
-/
def IsRightQuasiInverse (u : V₃ ->ₗ[K] V₂) (v : V₂ ->ₗ[K] V₃) : Prop :=
  v ∘ₗ u ≈ .id

/--
Definition of `IsQuasiInverse` / `IsQuasiInverse` 的定义

English:
definition IsQuasiInverse
  signature: (u : V₃ ->ₗ[K] V₂) (v : V₂ ->ₗ[K] V₃)
  body: u.IsLeftQuasiInverse v ∧ u.IsRightQuasiInverse v

中文:
定义 IsQuasiInverse
  签名: (u : V₃ ->ₗ[K] V₂) (v : V₂ ->ₗ[K] V₃)
  定义体: u.IsLeftQuasiInverse v ∧ u.IsRightQuasiInverse v

Depends on / 依赖: IsLeftQuasiInverse, IsRightQuasiInverse, u.IsLeftQuasiInverse, u.IsRightQuasiInverse
-/
def IsQuasiInverse (u : V₃ ->ₗ[K] V₂) (v : V₂ ->ₗ[K] V₃) : Prop :=
  u.IsLeftQuasiInverse v ∧ u.IsRightQuasiInverse v

/--
lemma `isLeftQuasiInverse_iff_isRightQuasiInverse_swap` / 引理 `isLeftQuasiInverse_iff_isRightQuasiInverse_swap`

English:
lemma isLeftQuasiInverse_iff_isRightQuasiInverse_swap
  given: {u : V₃ ->ₗ[K] V₂} {v : V₂ ->ₗ[K] V₃}
  proof: Iff.rfl

alias ⟨IsLeftQuasiInverse.isRightQuasiInverse, IsRightQuasiInverse.isLeftQuasiInverse⟩ :=
  isLeftQuasiInverse_iff_isRightQuasiInverse_swap

中文:
引理 isLeftQuasiInverse_iff_isRightQuasiInverse_swap
  条件: {u : V₃ ->ₗ[K] V₂} {v : V₂ ->ₗ[K] V₃}
  证明: Iff.rfl

alias ⟨IsLeftQuasiInverse.isRightQuasiInverse, IsRightQuasiInverse.isLeftQuasiInverse⟩ :=
  isLeftQuasiInverse_iff_isRightQuasiInverse_swap

Depends on / 依赖: Iff.rfl
-/
lemma isLeftQuasiInverse_iff_isRightQuasiInverse_swap {u : V₃ ->ₗ[K] V₂} {v : V₂ ->ₗ[K] V₃} :
    u.IsLeftQuasiInverse v ↔ v.IsRightQuasiInverse u := Iff.rfl

alias ⟨IsLeftQuasiInverse.isRightQuasiInverse, IsRightQuasiInverse.isLeftQuasiInverse⟩ :=
  isLeftQuasiInverse_iff_isRightQuasiInverse_swap

/--
lemma `IsLeftQuasiInverse.equiv` / 引理 `IsLeftQuasiInverse.equiv`

English:
lemma IsLeftQuasiInverse.equiv
  statement: {u : V₃ ->ₗ[K] V₂} {v : V₂ ->ₗ[K] V₃}
  proof: h

中文:
引理 IsLeftQuasiInverse.equiv
  结论: {u : V₃ ->ₗ[K] V₂} {v : V₂ ->ₗ[K] V₃}
  证明: h
-/
lemma IsLeftQuasiInverse.equiv {u : V₃ ->ₗ[K] V₂} {v : V₂ ->ₗ[K] V₃}
    (h : u.IsLeftQuasiInverse v) : u ∘ₗ v ≈ .id := h

/--
lemma `IsRightQuasiInverse.equiv` / 引理 `IsRightQuasiInverse.equiv`

English:
lemma IsRightQuasiInverse.equiv
  statement: {u : V₃ ->ₗ[K] V₂} {v : V₂ ->ₗ[K] V₃}
  proof: h

中文:
引理 IsRightQuasiInverse.equiv
  结论: {u : V₃ ->ₗ[K] V₂} {v : V₂ ->ₗ[K] V₃}
  证明: h
-/
lemma IsRightQuasiInverse.equiv {u : V₃ ->ₗ[K] V₂} {v : V₂ ->ₗ[K] V₃}
    (h : u.IsRightQuasiInverse v) : v ∘ₗ u ≈ .id := h

/--
lemma `_root_.LinearEquiv.isQuasiInverse` / 引理 `_root_.LinearEquiv.isQuasiInverse`

English:
lemma _root_.LinearEquiv.isQuasiInverse
  given: (e : V ≃ₗ[K] V₂)
  proof: by
  simp [IsQuasiInverse, IsLeftQuasiInverse, IsRightQuasiInverse]

@[symm]

中文:
引理 _root_.线性等价.isQuasiInverse
  条件: (e : V ≃ₗ[K] V₂)
  证明: by
  simp [IsQuasiInverse, IsLeftQuasiInverse, IsRightQuasiInverse]

@[symm]

Depends on / 依赖: IsLeftQuasiInverse, IsQuasiInverse, IsRightQuasiInverse
-/
lemma _root_.LinearEquiv.isQuasiInverse (e : V ≃ₗ[K] V₂) :
    e.symm.IsQuasiInverse e := by
  simp [IsQuasiInverse, IsLeftQuasiInverse, IsRightQuasiInverse]

@[symm]
/--
lemma `IsQuasiInverse.symm` / 引理 `IsQuasiInverse.symm`

English:
lemma IsQuasiInverse.symm
  statement: {u : V₃ ->ₗ[K] V₂} {v : V₂ ->ₗ[K] V₃}
  proof: And.symm h

@[gcongr]

中文:
引理 IsQuasiInverse.symm
  结论: {u : V₃ ->ₗ[K] V₂} {v : V₂ ->ₗ[K] V₃}
  证明: And.symm h

@[gcongr]

Depends on / 依赖: And.symm
-/
lemma IsQuasiInverse.symm {u : V₃ ->ₗ[K] V₂} {v : V₂ ->ₗ[K] V₃}
    (h : u.IsQuasiInverse v) : v.IsQuasiInverse u :=
  And.symm h

@[gcongr]
/--
lemma `IsLeftQuasiInverse.congr` / 引理 `IsLeftQuasiInverse.congr`

English:
lemma IsLeftQuasiInverse.congr
  statement: {u u' : V₃ ->ₗ[K] V₂} {v v' : V₂ ->ₗ[K] V₃}
  proof: by
  unfold IsLeftQuasiInverse at *
  grw [hu, hv]
  assumption

@[gcongr]

中文:
引理 IsLeftQuasiInverse.congr
  结论: {u u' : V₃ ->ₗ[K] V₂} {v v' : V₂ ->ₗ[K] V₃}
  证明: by
  unfold IsLeftQuasiInverse at *
  grw [hu, hv]
  assumption

@[gcongr]

Depends on / 依赖: IsLeftQuasiInverse
-/
lemma IsLeftQuasiInverse.congr {u u' : V₃ ->ₗ[K] V₂} {v v' : V₂ ->ₗ[K] V₃}
    (h : u.IsLeftQuasiInverse v) (hu : u' ≈ u) (hv : v' ≈ v) :
    u'.IsLeftQuasiInverse v' := by
  unfold IsLeftQuasiInverse at *
  grw [hu, hv]
  assumption

@[gcongr]
/--
lemma `isLeftQuasiInverse_congr` / 引理 `isLeftQuasiInverse_congr`

English:
lemma isLeftQuasiInverse_congr
  statement: {u u' : V₃ ->ₗ[K] V₂} {v v' : V₂ ->ₗ[K] V₃}
  proof: ⟨fun H => H.congr hu hv, fun H => H.congr (Setoid.symm hu) (Setoid.symm hv)⟩

@[gcongr]

中文:
引理 isLeftQuasiInverse_congr
  结论: {u u' : V₃ ->ₗ[K] V₂} {v v' : V₂ ->ₗ[K] V₃}
  证明: ⟨fun H => H.congr hu hv, fun H => H.congr (Setoid.symm hu) (Setoid.symm hv)⟩

@[gcongr]

Depends on / 依赖: H.congr, Setoid, Setoid.symm
-/
lemma isLeftQuasiInverse_congr {u u' : V₃ ->ₗ[K] V₂} {v v' : V₂ ->ₗ[K] V₃}
    (hu : u' ≈ u) (hv : v' ≈ v) :
    u.IsLeftQuasiInverse v ↔ u'.IsLeftQuasiInverse v' :=
  ⟨fun H => H.congr hu hv, fun H => H.congr (Setoid.symm hu) (Setoid.symm hv)⟩

@[gcongr]
/--
lemma `IsRightQuasiInverse.congr` / 引理 `IsRightQuasiInverse.congr`

English:
lemma IsRightQuasiInverse.congr
  statement: {u u' : V₃ ->ₗ[K] V₂} {v v' : V₂ ->ₗ[K] V₃}
  proof: .isRightQuasiInverse h.isLeftQuasiInverse.congr hv hu

中文:
引理 IsRightQuasiInverse.congr
  结论: {u u' : V₃ ->ₗ[K] V₂} {v v' : V₂ ->ₗ[K] V₃}
  证明: .isRightQuasiInverse h.isLeftQuasiInverse.congr hv hu

Depends on / 依赖: h.isLeftQuasiInverse.congr, isLeftQuasiInverse, isRightQuasiInverse
-/
lemma IsRightQuasiInverse.congr {u u' : V₃ ->ₗ[K] V₂} {v v' : V₂ ->ₗ[K] V₃}
    (h : u.IsRightQuasiInverse v) (hu : u' ≈ u) (hv : v' ≈ v) :
    u'.IsRightQuasiInverse v' :=
.isRightQuasiInverse h.isLeftQuasiInverse.congr hv hu

/--
lemma `isRightQuasiInverse_congr` / 引理 `isRightQuasiInverse_congr`

English:
lemma isRightQuasiInverse_congr
  statement: {u u' : V₃ ->ₗ[K] V₂} {v v' : V₂ ->ₗ[K] V₃}
  proof: ⟨fun H => H.congr hu hv, fun H => H.congr (Setoid.symm hu) (Setoid.symm hv)⟩

@[gcongr]

中文:
引理 isRightQuasiInverse_congr
  结论: {u u' : V₃ ->ₗ[K] V₂} {v v' : V₂ ->ₗ[K] V₃}
  证明: ⟨fun H => H.congr hu hv, fun H => H.congr (Setoid.symm hu) (Setoid.symm hv)⟩

@[gcongr]

Depends on / 依赖: H.congr, Setoid, Setoid.symm
-/
lemma isRightQuasiInverse_congr {u u' : V₃ ->ₗ[K] V₂} {v v' : V₂ ->ₗ[K] V₃}
    (hu : u' ≈ u) (hv : v' ≈ v) :
    u.IsRightQuasiInverse v ↔ u'.IsRightQuasiInverse v' :=
  ⟨fun H => H.congr hu hv, fun H => H.congr (Setoid.symm hu) (Setoid.symm hv)⟩

@[gcongr]
/--
lemma `IsQuasiInverse.congr` / 引理 `IsQuasiInverse.congr`

English:
lemma IsQuasiInverse.congr
  statement: {u u' : V₃ ->ₗ[K] V₂} {v v' : V₂ ->ₗ[K] V₃}
  proof: ⟨h.1.congr hu hv, h.2.congr hu hv⟩

中文:
引理 IsQuasiInverse.congr
  结论: {u u' : V₃ ->ₗ[K] V₂} {v v' : V₂ ->ₗ[K] V₃}
  证明: ⟨h.1.congr hu hv, h.2.congr hu hv⟩
-/
lemma IsQuasiInverse.congr {u u' : V₃ ->ₗ[K] V₂} {v v' : V₂ ->ₗ[K] V₃}
    (h : u.IsQuasiInverse v) (hu : u' ≈ u) (hv : v' ≈ v) :
    u'.IsQuasiInverse v' :=
  ⟨h.1.congr hu hv, h.2.congr hu hv⟩

/--
lemma `isQuasiInverse_congr` / 引理 `isQuasiInverse_congr`

English:
lemma isQuasiInverse_congr
  statement: {u u' : V₃ ->ₗ[K] V₂} {v v' : V₂ ->ₗ[K] V₃}
  proof: by
  simp [IsQuasiInverse, isLeftQuasiInverse_congr hu hv, isRightQuasiInverse_congr hu hv]

中文:
引理 isQuasiInverse_congr
  结论: {u u' : V₃ ->ₗ[K] V₂} {v v' : V₂ ->ₗ[K] V₃}
  证明: by
  simp [IsQuasiInverse, isLeftQuasiInverse_congr hu hv, isRightQuasiInverse_congr hu hv]

Depends on / 依赖: IsQuasiInverse, isLeftQuasiInverse_congr, isRightQuasiInverse_congr
-/
lemma isQuasiInverse_congr {u u' : V₃ ->ₗ[K] V₂} {v v' : V₂ ->ₗ[K] V₃}
    (hu : u' ≈ u) (hv : v' ≈ v) :
    u.IsQuasiInverse v ↔ u'.IsQuasiInverse v' := by
  simp [IsQuasiInverse, isLeftQuasiInverse_congr hu hv, isRightQuasiInverse_congr hu hv]

/--
lemma `IsQuasiInverse.equiv_of_left` / 引理 `IsQuasiInverse.equiv_of_left`

English:
lemma IsQuasiInverse.equiv_of_left
  statement: {u u' : V₃ ->ₗ[K] V₂} {v v' : V₂ ->ₗ[K] V₃}
  proof: by
  calc
    v = v ∘ₗ .id := by simp
    _ ≈ v ∘ₗ (u' ∘ₗ v') := by grw [h'.1.equiv]
    _ ≈ v ∘ₗ (u ∘ₗ v') := by grw [hu]
    _ = (v ∘ₗ u) ∘ₗ v' := by rw [comp_assoc]
    _ ≈ .id ∘ₗ v' := by grw [h.2.equiv]
    _ = v' := by simp

中文:
引理 IsQuasiInverse.equiv_of_left
  结论: {u u' : V₃ ->ₗ[K] V₂} {v v' : V₂ ->ₗ[K] V₃}
  证明: by
  calc
    v = v ∘ₗ .id := by simp
    _ ≈ v ∘ₗ (u' ∘ₗ v') := by grw [h'.1.equiv]
    _ ≈ v ∘ₗ (u ∘ₗ v') := by grw [hu]
    _ = (v ∘ₗ u) ∘ₗ v' := by rw [comp_assoc]
    _ ≈ .id ∘ₗ v' := by grw [h.2.equiv]
    _ = v' := by simp

Depends on / 依赖: comp_assoc
-/
lemma IsQuasiInverse.equiv_of_left {u u' : V₃ ->ₗ[K] V₂} {v v' : V₂ ->ₗ[K] V₃}
    (h : u.IsQuasiInverse v) (h' : u'.IsQuasiInverse v') (hu : u ≈ u') :
    v ≈ v' := by
  calc
    v = v ∘ₗ .id := by simp
    _ ≈ v ∘ₗ (u' ∘ₗ v') := by grw [h'.1.equiv]
    _ ≈ v ∘ₗ (u ∘ₗ v') := by grw [hu]
    _ = (v ∘ₗ u) ∘ₗ v' := by rw [comp_assoc]
    _ ≈ .id ∘ₗ v' := by grw [h.2.equiv]
    _ = v' := by simp

/--
lemma `IsQuasiInverse.equiv_of_right` / 引理 `IsQuasiInverse.equiv_of_right`

English:
lemma IsQuasiInverse.equiv_of_right
  statement: {u u' : V₃ ->ₗ[K] V₂} {v v' : V₂ ->ₗ[K] V₃}
  proof: h.symm.equiv_of_left h'.symm hv

中文:
引理 IsQuasiInverse.equiv_of_right
  结论: {u u' : V₃ ->ₗ[K] V₂} {v v' : V₂ ->ₗ[K] V₃}
  证明: h.symm.equiv_of_left h'.symm hv

Depends on / 依赖: equiv_of_left, h.symm.equiv_of_left
-/
lemma IsQuasiInverse.equiv_of_right {u u' : V₃ ->ₗ[K] V₂} {v v' : V₂ ->ₗ[K] V₃}
    (h : u.IsQuasiInverse v) (h' : u'.IsQuasiInverse v') (hv : v ≈ v') :
    u ≈ u' :=
  h.symm.equiv_of_left h'.symm hv

/--
lemma `IsLeftQuasiInverse.comp` / 引理 `IsLeftQuasiInverse.comp`

English:
lemma IsLeftQuasiInverse.comp
  statement: {u : V ->ₗ[K] V₂} {v : V₂ ->ₗ[K] V₃} {u' : V₂ ->ₗ[K] V}
  proof: calc
    _ = u' ∘ₗ (v' ∘ₗ v) ∘ₗ u := rfl
    _ ≈ u' ∘ₗ .id ∘ₗ u := by grw [hv.equiv]
    _ ≈ .id := hu.equiv

中文:
引理 IsLeftQuasiInverse.comp
  结论: {u : V ->ₗ[K] V₂} {v : V₂ ->ₗ[K] V₃} {u' : V₂ ->ₗ[K] V}
  证明: calc
    _ = u' ∘ₗ (v' ∘ₗ v) ∘ₗ u := rfl
    _ ≈ u' ∘ₗ .id ∘ₗ u := by grw [hv.equiv]
    _ ≈ .id := hu.equiv

Depends on / 依赖: hu.equiv, hv.equiv
-/
lemma IsLeftQuasiInverse.comp {u : V ->ₗ[K] V₂} {v : V₂ ->ₗ[K] V₃} {u' : V₂ ->ₗ[K] V}
    {v' : V₃ ->ₗ[K] V₂} (hu : u'.IsLeftQuasiInverse u) (hv : v'.IsLeftQuasiInverse v) :
    (u' ∘ₗ v').IsLeftQuasiInverse (v ∘ₗ u) :=
  calc
    _ = u' ∘ₗ (v' ∘ₗ v) ∘ₗ u := rfl
    _ ≈ u' ∘ₗ .id ∘ₗ u := by grw [hv.equiv]
    _ ≈ .id := hu.equiv

/--
lemma `IsRightQuasiInverse.comp` / 引理 `IsRightQuasiInverse.comp`

English:
lemma IsRightQuasiInverse.comp
  statement: {u : V ->ₗ[K] V₂} {v : V₂ ->ₗ[K] V₃} {u' : V₂ ->ₗ[K] V}
  proof: .isRightQuasiInverse hv.isLeftQuasiInverse.comp hu.isLeftQuasiInverse

中文:
引理 IsRightQuasiInverse.comp
  结论: {u : V ->ₗ[K] V₂} {v : V₂ ->ₗ[K] V₃} {u' : V₂ ->ₗ[K] V}
  证明: .isRightQuasiInverse hv.isLeftQuasiInverse.comp hu.isLeftQuasiInverse

Depends on / 依赖: hu.isLeftQuasiInverse, hv.isLeftQuasiInverse.comp, isLeftQuasiInverse, isRightQuasiInverse
-/
lemma IsRightQuasiInverse.comp {u : V ->ₗ[K] V₂} {v : V₂ ->ₗ[K] V₃} {u' : V₂ ->ₗ[K] V}
    {v' : V₃ ->ₗ[K] V₂} (hu : u'.IsRightQuasiInverse u) (hv : v'.IsRightQuasiInverse v) :
    (u' ∘ₗ v').IsRightQuasiInverse (v ∘ₗ u) :=
.isRightQuasiInverse hv.isLeftQuasiInverse.comp hu.isLeftQuasiInverse

/--
lemma `IsQuasiInverse.comp` / 引理 `IsQuasiInverse.comp`

English:
lemma IsQuasiInverse.comp
  statement: {u : V ->ₗ[K] V₂} {v : V₂ ->ₗ[K] V₃} {u' : V₂ ->ₗ[K] V}
  proof: ⟨hu.1.comp hv.1, hu.2.comp hv.2⟩

中文:
引理 IsQuasiInverse.comp
  结论: {u : V ->ₗ[K] V₂} {v : V₂ ->ₗ[K] V₃} {u' : V₂ ->ₗ[K] V}
  证明: ⟨hu.1.comp hv.1, hu.2.comp hv.2⟩
-/
lemma IsQuasiInverse.comp {u : V ->ₗ[K] V₂} {v : V₂ ->ₗ[K] V₃} {u' : V₂ ->ₗ[K] V}
    {v' : V₃ ->ₗ[K] V₂} (hu : u'.IsQuasiInverse u) (hv : v'.IsQuasiInverse v) :
    (u' ∘ₗ v').IsQuasiInverse (v ∘ₗ u) :=
  ⟨hu.1.comp hv.1, hu.2.comp hv.2⟩

/--
lemma `IsLeftQuasiInverse.of_comp_left` / 引理 `IsLeftQuasiInverse.of_comp_left`

English:
lemma IsLeftQuasiInverse.of_comp_left
  statement: {u : V ->ₗ[K] V₂} {v : V₂ ->ₗ[K] V₃}
  proof: by
  calc
    _ = ((u ∘ₗ w) ∘ₗ v) ∘ₗ .id := rfl
    _ ≈ ((u ∘ₗ w) ∘ₗ v) ∘ₗ (u ∘ₗ u') := by grw [hu.equiv]
    _ = u ∘ₗ (w ∘ₗ (v ∘ₗ u)) ∘ₗ u' := rfl
    _ ≈ u ∘ₗ .id ∘ₗ u' := by grw [hw.equiv]
    _ ≈ .id := hu.equiv

中文:
引理 IsLeftQuasiInverse.of_comp_left
  结论: {u : V ->ₗ[K] V₂} {v : V₂ ->ₗ[K] V₃}
  证明: by
  calc
    _ = ((u ∘ₗ w) ∘ₗ v) ∘ₗ .id := rfl
    _ ≈ ((u ∘ₗ w) ∘ₗ v) ∘ₗ (u ∘ₗ u') := by grw [hu.equiv]
    _ = u ∘ₗ (w ∘ₗ (v ∘ₗ u)) ∘ₗ u' := rfl
    _ ≈ u ∘ₗ .id ∘ₗ u' := by grw [hw.equiv]
    _ ≈ .id := hu.equiv

Depends on / 依赖: hu.equiv, hw.equiv
-/
lemma IsLeftQuasiInverse.of_comp_left {u : V ->ₗ[K] V₂} {v : V₂ ->ₗ[K] V₃}
    {u' : V₂ ->ₗ[K] V} {w : V₃ ->ₗ[K] V} (hu : u'.IsRightQuasiInverse u)
    (hw : w.IsLeftQuasiInverse (v ∘ₗ u)) :
    (u ∘ₗ w).IsLeftQuasiInverse v := by
  calc
    _ = ((u ∘ₗ w) ∘ₗ v) ∘ₗ .id := rfl
    _ ≈ ((u ∘ₗ w) ∘ₗ v) ∘ₗ (u ∘ₗ u') := by grw [hu.equiv]
    _ = u ∘ₗ (w ∘ₗ (v ∘ₗ u)) ∘ₗ u' := rfl
    _ ≈ u ∘ₗ .id ∘ₗ u' := by grw [hw.equiv]
    _ ≈ .id := hu.equiv

/--
lemma `IsQuasiInverse.of_comp_left` / 引理 `IsQuasiInverse.of_comp_left`

English:
lemma IsQuasiInverse.of_comp_left
  statement: {u : V ->ₗ[K] V₂} {v : V₂ ->ₗ[K] V₃}
  proof: ⟨.of_comp_left hu.2 hw.1, hw.2⟩

中文:
引理 IsQuasiInverse.of_comp_left
  结论: {u : V ->ₗ[K] V₂} {v : V₂ ->ₗ[K] V₃}
  证明: ⟨.of_comp_left hu.2 hw.1, hw.2⟩

Depends on / 依赖: of_comp_left
-/
lemma IsQuasiInverse.of_comp_left {u : V ->ₗ[K] V₂} {v : V₂ ->ₗ[K] V₃}
    {u' : V₂ ->ₗ[K] V} {w : V₃ ->ₗ[K] V} (hu : u'.IsQuasiInverse u)
    (hw : w.IsQuasiInverse (v ∘ₗ u)) :
    (u ∘ₗ w).IsQuasiInverse v :=
  ⟨.of_comp_left hu.2 hw.1, hw.2⟩

/--
lemma `IsRightQuasiInverse.of_comp_right` / 引理 `IsRightQuasiInverse.of_comp_right`

English:
lemma IsRightQuasiInverse.of_comp_right
  statement: {u : V ->ₗ[K] V₂} {v : V₂ ->ₗ[K] V₃}
  proof: by
  calc
    _ = .id ∘ₗ (u ∘ₗ (w ∘ₗ v)) := rfl
    _ ≈ (v' ∘ₗ v) ∘ₗ (u ∘ₗ (w ∘ₗ v)) := by grw [hv.equiv]
    _ = v' ∘ₗ ((v ∘ₗ u) ∘ₗ w) ∘ₗ v := rfl
    _ ≈ v' ∘ₗ .id ∘ₗ v := by grw [hw.equiv]
    _ ≈ .id := hv.equiv

中文:
引理 IsRightQuasiInverse.of_comp_right
  结论: {u : V ->ₗ[K] V₂} {v : V₂ ->ₗ[K] V₃}
  证明: by
  calc
    _ = .id ∘ₗ (u ∘ₗ (w ∘ₗ v)) := rfl
    _ ≈ (v' ∘ₗ v) ∘ₗ (u ∘ₗ (w ∘ₗ v)) := by grw [hv.equiv]
    _ = v' ∘ₗ ((v ∘ₗ u) ∘ₗ w) ∘ₗ v := rfl
    _ ≈ v' ∘ₗ .id ∘ₗ v := by grw [hw.equiv]
    _ ≈ .id := hv.equiv

Depends on / 依赖: hv.equiv, hw.equiv
-/
lemma IsRightQuasiInverse.of_comp_right {u : V ->ₗ[K] V₂} {v : V₂ ->ₗ[K] V₃}
    {v' : V₃ ->ₗ[K] V₂} {w : V₃ ->ₗ[K] V} (hv : v'.IsLeftQuasiInverse v)
    (hw : w.IsRightQuasiInverse (v ∘ₗ u)) :
    (w ∘ₗ v).IsRightQuasiInverse u := by
  calc
    _ = .id ∘ₗ (u ∘ₗ (w ∘ₗ v)) := rfl
    _ ≈ (v' ∘ₗ v) ∘ₗ (u ∘ₗ (w ∘ₗ v)) := by grw [hv.equiv]
    _ = v' ∘ₗ ((v ∘ₗ u) ∘ₗ w) ∘ₗ v := rfl
    _ ≈ v' ∘ₗ .id ∘ₗ v := by grw [hw.equiv]
    _ ≈ .id := hv.equiv

/--
lemma `IsQuasiInverse.of_comp_right` / 引理 `IsQuasiInverse.of_comp_right`

English:
lemma IsQuasiInverse.of_comp_right
  statement: {u : V ->ₗ[K] V₂} {v : V₂ ->ₗ[K] V₃}
  proof: ⟨hw.1, IsRightQuasiInverse.of_comp_right hv.1 hw.2⟩

中文:
引理 IsQuasiInverse.of_comp_right
  结论: {u : V ->ₗ[K] V₂} {v : V₂ ->ₗ[K] V₃}
  证明: ⟨hw.1, IsRightQuasiInverse.of_comp_right hv.1 hw.2⟩

Depends on / 依赖: IsRightQuasiInverse, IsRightQuasiInverse.of_comp_right, of_comp_right
-/
lemma IsQuasiInverse.of_comp_right {u : V ->ₗ[K] V₂} {v : V₂ ->ₗ[K] V₃}
    {v' : V₃ ->ₗ[K] V₂} {w : V₃ ->ₗ[K] V} (hv : v'.IsQuasiInverse v)
    (hw : w.IsQuasiInverse (v ∘ₗ u)) :
    (w ∘ₗ v).IsQuasiInverse u :=
  ⟨hw.1, IsRightQuasiInverse.of_comp_right hv.1 hw.2⟩

/--
lemma `isQuasiInverse_subtype_projectionOnto_iff` / 引理 `isQuasiInverse_subtype_projectionOnto_iff`

English:
lemma isQuasiInverse_subtype_projectionOnto_iff
  given: {S T : Submodule K V} (hST : IsCompl S T)
  proof: by
  rw [IsQuasiInverse]; rw [and_iff_left (by simp [IsRightQuasiInverse]; rw [projectionOnto_comp_subtype]),
    IsLeftQuasiInverse, ← projection,
    FiniteRangeSetoid.projection_equiv_id_iff_isNoetherian hST]

中文:
引理 isQuasiInverse_subtype_projectionOnto_iff
  条件: {S T : 子模 K V} (hST : 是补集 S T)
  证明: by
  rw [IsQuasiInverse]; rw [and_iff_left (by simp [IsRightQuasiInverse]; rw [projectionOnto_comp_subtype]),
    IsLeftQuasiInverse, ← projection,
    FiniteRangeSetoid.projection_equiv_id_iff_isNoetherian hST]

Depends on / 依赖: FiniteRangeSetoid, FiniteRangeSetoid.projection_equiv_id_iff_isNoetherian, IsLeftQuasiInverse, IsQuasiInverse, IsRightQuasiInverse, and_iff_left, projection, projectionOnto_comp_subtype, projection_equiv_id_iff_isNoetherian
-/
lemma isQuasiInverse_subtype_projectionOnto_iff {S T : Submodule K V} (hST : IsCompl S T) :
    IsQuasiInverse S.subtype (S.projectionOnto T hST) ↔ IsNoetherian K T := by
  rw [IsQuasiInverse]; rw [and_iff_left (by simp [IsRightQuasiInverse]; rw [projectionOnto_comp_subtype]),
    IsLeftQuasiInverse, ← projection,
    FiniteRangeSetoid.projection_equiv_id_iff_isNoetherian hST]

/--
lemma `isQuasiInverse_subtype_projectionOnto` / 引理 `isQuasiInverse_subtype_projectionOnto`

English:
lemma isQuasiInverse_subtype_projectionOnto
  statement: {S T : Submodule K V} [IsNoetherian K T]
  proof: .mpr inferInstance isQuasiInverse_subtype_projectionOnto_iff hST

中文:
引理 isQuasiInverse_subtype_projectionOnto
  结论: {S T : 子模 K V} [是Noether K T]
  证明: .mpr inferInstance isQuasiInverse_subtype_projectionOnto_iff hST

Depends on / 依赖: isQuasiInverse_subtype_projectionOnto_iff
-/
lemma isQuasiInverse_subtype_projectionOnto {S T : Submodule K V} [IsNoetherian K T]
    (hST : IsCompl S T) :
    IsQuasiInverse S.subtype (S.projectionOnto T hST) :=
.mpr inferInstance isQuasiInverse_subtype_projectionOnto_iff hST

end QuasiInverse

end LinearMap
