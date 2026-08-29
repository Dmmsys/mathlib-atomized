/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Antoine Chambert-Loir, Anatole Dedecker, Jireh Loreaux
-/
module

public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.ContinuousOn

/-!
# Semicontinuous maps

A function `f` from a topological space `α` to an ordered space `β` is *lower semicontinuous* at a
point `x` if, for any `y < f x`, for any `x'` close enough to `x`, one has `f x' > y`. In other
words, `f` can jump up, but it cannot jump down.

*Upper semicontinuous* functions are defined similarly. Upper and lower hemicontinuity (of
functions `f : α → Set β`) are often defined in terms of sequential characterizations, but
here we take an equivalent approach. `f : α → Set β` is *upper hemicontinuous* at `x` if for any
neighborhood of `f x`, `f x'` is included in this neighborhood for all `x'` close enough to `x`.

Of course, one can see a superficial similarity between upper semicontinuity and upper
hemicontinuity. In fact, we can unify all of upper and lower semicontinuity and also upper and
lower hemicontinuity under one umbrella, by considering a general relation `r : α → β → Prop` and
defining semicontinuity of this relation.

This file introduces these notions, and a basic API around them mimicking the API for continuous
functions.

## Main definitions and results

We introduce 4 generic definitions related to semicontinuity:
* `SemicontinuousWithinAt r s x`
* `SemicontinuousAt r x`
* `SemicontinuousOn r s`
* `Semicontinuous r`

We build a basic API using dot notation around these notions, and we prove that
* constant functions are semicontinuous;
* right composition with continuous functions preserves semicontinuity;

We also define lower and upper semicontinuity as abbreviations of these generic definitions
and transfer the generic results to these notions.

We also define two useful notions for set-valued functions: `HasOpenLowerSections` (which says that
for `f : α → β` and for all `y ∈ β`, the set `{x | y ∈ f x}` is open. Similarly, we define
`HasOpenCGraph` which says that the set of all pairs `(x, y) : α × β` with `y ∈ f x` is open.
We show that `HasOpenCGraph` implies `HasOpenLowerSections` (`HasOpenCGraph.hasOpenLowerSections`)
which implies `LowerHemicontinuous` (`HasOpenLowerSections.lowerHemicontinuous`).

We also define variants of these two notions for `On`/`At`/`WithinAt`.

## References

* <https://en.wikipedia.org/wiki/Semi-continuity>
* <https://en.wikipedia.org/wiki/Hemicontinuity>

-/

@[expose] public section

open scoped Topology

open Set Function Filter

variable {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace γ]

/-! ## Main definitions -/

section Semicontinuous

/--
Definition of `SemicontinuousWithinAt` / `SemicontinuousWithinAt` 的定义

English:
definition SemicontinuousWithinAt
  signature: (r : α -> β -> Prop) (s : Set α) (x : α)
  body: forall y, r x y -> forallᶠ x' in 𝓝[s] x, r x' y

中文:
定义 SemicontinuousWithinAt
  签名: (r : α -> β -> 命题) (s : 集合 α) (x : α)
  定义体: forall y, r x y -> forallᶠ x' in 𝓝[s] x, r x' y
-/
def SemicontinuousWithinAt (r : α -> β -> Prop) (s : Set α) (x : α) :=
  forall y, r x y -> forallᶠ x' in 𝓝[s] x, r x' y

/--
Definition of `SemicontinuousOn` / `SemicontinuousOn` 的定义

English:
definition SemicontinuousOn
  signature: (r : α -> β -> Prop) (s : Set α)
  body: forall x in s, SemicontinuousWithinAt r s x

中文:
定义 SemicontinuousOn
  签名: (r : α -> β -> 命题) (s : 集合 α)
  定义体: forall x in s, SemicontinuousWithinAt r s x

Depends on / 依赖: SemicontinuousWithinAt
-/
def SemicontinuousOn (r : α -> β -> Prop) (s : Set α) :=
  forall x in s, SemicontinuousWithinAt r s x

/--
Definition of `SemicontinuousAt` / `SemicontinuousAt` 的定义

English:
definition SemicontinuousAt
  signature: (r : α -> β -> Prop) (x : α)
  body: forall y, r x y -> forallᶠ x' in 𝓝 x, r x' y

中文:
定义 SemicontinuousAt
  签名: (r : α -> β -> 命题) (x : α)
  定义体: forall y, r x y -> forallᶠ x' in 𝓝 x, r x' y
-/
def SemicontinuousAt (r : α -> β -> Prop) (x : α) : Prop :=
  forall y, r x y -> forallᶠ x' in 𝓝 x, r x' y

/--
Definition of `Semicontinuous` / `Semicontinuous` 的定义

English:
definition Semicontinuous
  signature: (r : α -> β -> Prop)
  body: forall x, SemicontinuousAt r x

中文:
定义 Semicontinuous
  签名: (r : α -> β -> 命题)
  定义体: forall x, SemicontinuousAt r x

Depends on / 依赖: SemicontinuousAt
-/
def Semicontinuous (r : α -> β -> Prop) : Prop :=
  forall x, SemicontinuousAt r x

variable {r r' : α -> β -> Prop} {x : α} {s t : Set α}

/--
lemma `semicontinuousWithinAt_iff_frequently` / 引理 `semicontinuousWithinAt_iff_frequently`

English:
lemma semicontinuousWithinAt_iff_frequently
  proof: by
  simp only [← not_eventually, not_imp_not, SemicontinuousWithinAt]

中文:
引理 semicontinuousWithinAt_iff_frequently
  证明: by
  simp only [← not_eventually, not_imp_not, SemicontinuousWithinAt]

Depends on / 依赖: SemicontinuousWithinAt, not_eventually, not_imp_not
-/
lemma semicontinuousWithinAt_iff_frequently :
    SemicontinuousWithinAt r s x ↔ forall y, (existsᶠ x' in 𝓝[s] x, ¬ r x' y) -> ¬ r x y := by
  simp only [← not_eventually, not_imp_not, SemicontinuousWithinAt]

/--
lemma `semicontinuousOn_iff_frequently` / 引理 `semicontinuousOn_iff_frequently`

English:
lemma semicontinuousOn_iff_frequently
  proof: by
  simp only [← not_eventually, not_imp_not, SemicontinuousWithinAt, SemicontinuousOn]

中文:
引理 semicontinuousOn_iff_frequently
  证明: by
  simp only [← not_eventually, not_imp_not, SemicontinuousWithinAt, SemicontinuousOn]

Depends on / 依赖: SemicontinuousOn, SemicontinuousWithinAt, not_eventually, not_imp_not
-/
lemma semicontinuousOn_iff_frequently :
    SemicontinuousOn r s ↔ forall x in s, forall y, (existsᶠ x' in 𝓝[s] x, ¬ r x' y) -> ¬ r x y := by
  simp only [← not_eventually, not_imp_not, SemicontinuousWithinAt, SemicontinuousOn]

/--
lemma `semicontinuousAt_iff_frequently` / 引理 `semicontinuousAt_iff_frequently`

English:
lemma semicontinuousAt_iff_frequently
  proof: by
  simp only [← not_eventually, not_imp_not, SemicontinuousAt]

中文:
引理 semicontinuousAt_iff_frequently
  证明: by
  simp only [← not_eventually, not_imp_not, SemicontinuousAt]

Depends on / 依赖: SemicontinuousAt, not_eventually, not_imp_not
-/
lemma semicontinuousAt_iff_frequently :
    SemicontinuousAt r x ↔ forall y, (existsᶠ x' in 𝓝 x, ¬ r x' y) -> ¬ r x y := by
  simp only [← not_eventually, not_imp_not, SemicontinuousAt]

/--
lemma `semicontinuous_iff_frequently` / 引理 `semicontinuous_iff_frequently`

English:
lemma semicontinuous_iff_frequently
  proof: by
  simp only [← not_eventually, not_imp_not, Semicontinuous, SemicontinuousAt]

中文:
引理 semicontinuous_iff_frequently
  证明: by
  simp only [← not_eventually, not_imp_not, Semicontinuous, SemicontinuousAt]

Depends on / 依赖: Semicontinuous, SemicontinuousAt, not_eventually, not_imp_not
-/
lemma semicontinuous_iff_frequently :
    Semicontinuous r ↔ forall x y, (existsᶠ x' in 𝓝 x, ¬ r x' y) -> ¬ r x y := by
  simp only [← not_eventually, not_imp_not, Semicontinuous, SemicontinuousAt]

/--
theorem `SemicontinuousWithinAt.mono` / 定理 `SemicontinuousWithinAt.mono`

English:
theorem SemicontinuousWithinAt.mono
  given: (h : SemicontinuousWithinAt r s x) (hst : t subseteq s)
  proof: fun y hy =>
  Filter.Eventually.filter_mono (nhdsWithin_mono _ hst) (h y hy)

中文:
定理 SemicontinuousWithinAt.mono
  条件: (h : SemicontinuousWithinAt r s x) (hst : t subseteq s)
  证明: fun y hy =>
  Filter.Eventually.filter_mono (nhdsWithin_mono _ hst) (h y hy)
-/
theorem SemicontinuousWithinAt.mono (h : SemicontinuousWithinAt r s x) (hst : t subseteq s) :
    SemicontinuousWithinAt r t x := fun y hy =>
  Filter.Eventually.filter_mono (nhdsWithin_mono _ hst) (h y hy)

/--
theorem `SemicontinuousWithinAt.congr_of_eventuallyEq` / 定理 `SemicontinuousWithinAt.congr_of_eventuallyEq`

English:
theorem SemicontinuousWithinAt.congr_of_eventuallyEq
  statement: {a : α}
  proof: by
  intro b hb
  simp_rw [← propext_iff, ← funext_iff] at hfg
  rw [← Filter.EventuallyEq.eq_of_nhdsWithin hfg has] at hb
  filter_upwards [hfg, h b hb] with x hx hxb
  exact hx ▸ hxb

中文:
定理 SemicontinuousWithinAt.congr_of_eventuallyEq
  结论: {a : α}
  证明: by
  intro b hb
  simp_rw [← propext_iff, ← funext_iff] at hfg
  rw [← Filter.EventuallyEq.eq_of_nhdsWithin hfg has] at hb
  filter_upwards [hfg, h b hb] with x hx hxb
  exact hx ▸ hxb

Depends on / 依赖: EventuallyEq, Filter, Filter.EventuallyEq.eq_of_nhdsWithin, eq_of_nhdsWithin, filter_upwards, funext_iff, propext_iff, simp_rw
-/
theorem SemicontinuousWithinAt.congr_of_eventuallyEq {a : α}
    (h : SemicontinuousWithinAt r s a)
    (has : a in s) (hfg : forallᶠ x in 𝓝[s] a, forall y, r x y ↔ r' x y) :
    SemicontinuousWithinAt r' s a := by
  intro b hb
  simp_rw [← propext_iff, ← funext_iff] at hfg
  rw [← Filter.EventuallyEq.eq_of_nhdsWithin hfg has] at hb
  filter_upwards [hfg, h b hb] with x hx hxb
  exact hx ▸ hxb

/--
theorem `semicontinuousWithinAt_univ_iff` / 定理 `semicontinuousWithinAt_univ_iff`

English:
theorem semicontinuousWithinAt_univ_iff
  proof: by
  simp [SemicontinuousWithinAt, SemicontinuousAt, nhdsWithin_univ]

中文:
定理 semicontinuousWithinAt_univ_iff
  证明: by
  simp [SemicontinuousWithinAt, SemicontinuousAt, nhdsWithin_univ]

Depends on / 依赖: SemicontinuousAt, SemicontinuousWithinAt, nhdsWithin_univ
-/
theorem semicontinuousWithinAt_univ_iff :
    SemicontinuousWithinAt r univ x ↔ SemicontinuousAt r x := by
  simp [SemicontinuousWithinAt, SemicontinuousAt, nhdsWithin_univ]

/--
theorem `SemicontinuousAt.semicontinuousWithinAt` / 定理 `SemicontinuousAt.semicontinuousWithinAt`

English:
theorem SemicontinuousAt.semicontinuousWithinAt
  statement: (s : Set α)
  proof: fun y hy =>
  Filter.Eventually.filter_mono nhdsWithin_le_nhds (h y hy)

中文:
定理 SemicontinuousAt.semicontinuousWithinAt
  结论: (s : 集合 α)
  证明: fun y hy =>
  Filter.Eventually.filter_mono nhdsWithin_le_nhds (h y hy)
-/
theorem SemicontinuousAt.semicontinuousWithinAt (s : Set α)
    (h : SemicontinuousAt r x) : SemicontinuousWithinAt r s x := fun y hy =>
  Filter.Eventually.filter_mono nhdsWithin_le_nhds (h y hy)

/--
theorem `SemicontinuousOn.semicontinuousWithinAt` / 定理 `SemicontinuousOn.semicontinuousWithinAt`

English:
theorem SemicontinuousOn.semicontinuousWithinAt
  statement: (h : SemicontinuousOn r s)
  proof: h x hx

中文:
定理 SemicontinuousOn.semicontinuousWithinAt
  结论: (h : SemicontinuousOn r s)
  证明: h x hx
-/
theorem SemicontinuousOn.semicontinuousWithinAt (h : SemicontinuousOn r s)
    (hx : x in s) : SemicontinuousWithinAt r s x :=
  h x hx

/--
theorem `SemicontinuousOn.mono` / 定理 `SemicontinuousOn.mono`

English:
theorem SemicontinuousOn.mono
  given: (h : SemicontinuousOn r s) (hst : t subseteq s)
  proof: fun x hx => (h x (hst hx)).mono hst

中文:
定理 SemicontinuousOn.mono
  条件: (h : SemicontinuousOn r s) (hst : t subseteq s)
  证明: fun x hx => (h x (hst hx)).mono hst
-/
theorem SemicontinuousOn.mono (h : SemicontinuousOn r s) (hst : t subseteq s) :
    SemicontinuousOn r t := fun x hx => (h x (hst hx)).mono hst

/--
theorem `semicontinuousOn_univ_iff` / 定理 `semicontinuousOn_univ_iff`

English:
theorem semicontinuousOn_univ_iff
  statement: SemicontinuousOn r univ ↔ Semicontinuous r
  proof: by
  simp [SemicontinuousOn, Semicontinuous, semicontinuousWithinAt_univ_iff]

中文:
定理 semicontinuousOn_univ_iff
  结论: SemicontinuousOn r univ ↔ Semicontinuous r
  证明: by
  simp [SemicontinuousOn, Semicontinuous, semicontinuousWithinAt_univ_iff]

Depends on / 依赖: Semicontinuous, SemicontinuousOn, semicontinuousWithinAt_univ_iff
-/
theorem semicontinuousOn_univ_iff : SemicontinuousOn r univ ↔ Semicontinuous r := by
  simp [SemicontinuousOn, Semicontinuous, semicontinuousWithinAt_univ_iff]

/--
theorem `semicontinuous_restrict_iff` / 定理 `semicontinuous_restrict_iff`

English:
theorem semicontinuous_restrict_iff
  proof: by
  rw [SemicontinuousOn]; rw [Semicontinuous]; rw [SetCoe.forall]
  refine forall₂_congr fun a ha => forall₂_congr fun b _ => ?_
  simp only [nhdsWithin_eq_map_subtype_coe ha, eventually_map, domRestrict]

中文:
定理 semicontinuous_restrict_iff
  证明: by
  rw [SemicontinuousOn]; rw [Semicontinuous]; rw [SetCoe.forall]
  refine forall₂_congr fun a ha => forall₂_congr fun b _ => ?_
  simp only [nhdsWithin_eq_map_subtype_coe ha, eventually_map, domRestrict]
-/
@[simp] theorem semicontinuous_restrict_iff :
    Semicontinuous (s.domRestrict r) ↔ SemicontinuousOn r s := by
  rw [SemicontinuousOn]; rw [Semicontinuous]; rw [SetCoe.forall]
  refine forall₂_congr fun a ha => forall₂_congr fun b _ => ?_
  simp only [nhdsWithin_eq_map_subtype_coe ha, eventually_map, domRestrict]

/--
theorem `Semicontinuous.semicontinuousAt` / 定理 `Semicontinuous.semicontinuousAt`

English:
theorem Semicontinuous.semicontinuousAt
  given: (h : Semicontinuous r) (x : α)
  proof: h x

中文:
定理 Semicontinuous.semicontinuousAt
  条件: (h : Semicontinuous r) (x : α)
  证明: h x
-/
theorem Semicontinuous.semicontinuousAt (h : Semicontinuous r) (x : α) :
    SemicontinuousAt r x :=
  h x

/--
theorem `Semicontinuous.semicontinuousWithinAt` / 定理 `Semicontinuous.semicontinuousWithinAt`

English:
theorem Semicontinuous.semicontinuousWithinAt
  statement: (h : Semicontinuous r) (s : Set α)
  proof: (h x).semicontinuousWithinAt s

中文:
定理 Semicontinuous.semicontinuousWithinAt
  结论: (h : Semicontinuous r) (s : 集合 α)
  证明: (h x).semicontinuousWithinAt s

Depends on / 依赖: semicontinuousWithinAt
-/
theorem Semicontinuous.semicontinuousWithinAt (h : Semicontinuous r) (s : Set α)
    (x : α) : SemicontinuousWithinAt r s x :=
  (h x).semicontinuousWithinAt s

/--
theorem `Semicontinuous.semicontinuousOn` / 定理 `Semicontinuous.semicontinuousOn`

English:
theorem Semicontinuous.semicontinuousOn
  given: (h : Semicontinuous r) (s : Set α)
  proof: fun x _hx => h.semicontinuousWithinAt s x

中文:
定理 Semicontinuous.semicontinuousOn
  条件: (h : Semicontinuous r) (s : 集合 α)
  证明: fun x _hx => h.semicontinuousWithinAt s x

Depends on / 依赖: h.semicontinuousWithinAt, semicontinuousWithinAt
-/
theorem Semicontinuous.semicontinuousOn (h : Semicontinuous r) (s : Set α) :
    SemicontinuousOn r s := fun x _hx => h.semicontinuousWithinAt s x

/--
theorem `semicontinuous_iff_isOpen` / 定理 `semicontinuous_iff_isOpen`

English:
theorem semicontinuous_iff_isOpen
  statement: Semicontinuous r ↔ forall b, IsOpen {x | r x b}
  proof: by
  exact ⟨fun h b => by simpa [isOpen_iff_mem_nhds, Filter.Eventually] using fun x hx => h x b hx,
    fun h x b hbx => (h b).mem_nhds hbx⟩

中文:
定理 semicontinuous_iff_isOpen
  结论: Semicontinuous r ↔ 对任意 b, 是开集 {x | r x b}
  证明: by
  exact ⟨fun h b => by simpa [isOpen_iff_mem_nhds, Filter.Eventually] using fun x hx => h x b hx,
    fun h x b hbx => (h b).mem_nhds hbx⟩

Depends on / 依赖: Eventually, Filter, Filter.Eventually, isOpen_iff_mem_nhds, mem_nhds
-/
theorem semicontinuous_iff_isOpen : Semicontinuous r ↔ forall b, IsOpen {x | r x b} := by
  exact ⟨fun h b => by simpa [isOpen_iff_mem_nhds, Filter.Eventually] using fun x hx => h x b hx,
    fun h x b hbx => (h b).mem_nhds hbx⟩

/--
theorem `Semicontinuous.isOpen` / 定理 `Semicontinuous.isOpen`

English:
theorem Semicontinuous.isOpen
  given: (h : Semicontinuous r) (b : β)
  statement: IsOpen {x | r x b}
  proof: semicontinuous_iff_isOpen.mp h b

中文:
定理 Semicontinuous.isOpen
  条件: (h : Semicontinuous r) (b : β)
  结论: 是开集 {x | r x b}
  证明: semicontinuous_iff_isOpen.mp h b

Depends on / 依赖: semicontinuous_iff_isOpen, semicontinuous_iff_isOpen.mp
-/
theorem Semicontinuous.isOpen (h : Semicontinuous r) (b : β) : IsOpen {x | r x b} :=
  semicontinuous_iff_isOpen.mp h b

/--
theorem `SemicontinuousWithinAt.inf` / 定理 `SemicontinuousWithinAt.inf`

English:
theorem SemicontinuousWithinAt.inf
  statement: {r' : α -> β -> Prop}
  proof: fun b ⟨hb, hb'⟩ =>
  (h b hb).and (h' b hb')

中文:
定理 SemicontinuousWithinAt.下确界
  结论: {r' : α -> β -> 命题}
  证明: fun b ⟨hb, hb'⟩ =>
  (h b hb).and (h' b hb')
-/
theorem SemicontinuousWithinAt.inf {r' : α -> β -> Prop}
    (h : SemicontinuousWithinAt r s x) (h' : SemicontinuousWithinAt r' s x) :
    SemicontinuousWithinAt (r ⊓ r') s x := fun b ⟨hb, hb'⟩ =>
  (h b hb).and (h' b hb')

/--
theorem `SemicontinuousWithinAt.sup` / 定理 `SemicontinuousWithinAt.sup`

English:
theorem SemicontinuousWithinAt.sup
  statement: {r' : α -> β -> Prop}
  proof: by
  intro b hab
  obtain hb | hb' := hab
  · exact (h b hb).mono fun _ hx => Or.inl hx
  · exact (h' b hb').mono fun _ hx => Or.inr hx

中文:
定理 SemicontinuousWithinAt.上确界
  结论: {r' : α -> β -> 命题}
  证明: by
  intro b hab
  obtain hb | hb' := hab
  · exact (h b hb).mono fun _ hx => Or.inl hx
  · exact (h' b hb').mono fun _ hx => Or.inr hx

Depends on / 依赖: Or.inl, Or.inr
-/
theorem SemicontinuousWithinAt.sup {r' : α -> β -> Prop}
    (h : SemicontinuousWithinAt r s x) (h' : SemicontinuousWithinAt r' s x) :
    SemicontinuousWithinAt (r ⊔ r') s x := by
  intro b hab
  obtain hb | hb' := hab
  · exact (h b hb).mono fun _ hx => Or.inl hx
  · exact (h' b hb').mono fun _ hx => Or.inr hx

/--
theorem `SemicontinuousAt.inf` / 定理 `SemicontinuousAt.inf`

English:
theorem SemicontinuousAt.inf
  statement: {r' : α -> β -> Prop}
  proof: fun b ⟨hb, hb'⟩ =>
  (h b hb).and (h' b hb')

中文:
定理 SemicontinuousAt.下确界
  结论: {r' : α -> β -> 命题}
  证明: fun b ⟨hb, hb'⟩ =>
  (h b hb).and (h' b hb')
-/
theorem SemicontinuousAt.inf {r' : α -> β -> Prop}
    (h : SemicontinuousAt r x) (h' : SemicontinuousAt r' x) :
    SemicontinuousAt (r ⊓ r') x := fun b ⟨hb, hb'⟩ =>
  (h b hb).and (h' b hb')

/--
theorem `SemicontinuousAt.sup` / 定理 `SemicontinuousAt.sup`

English:
theorem SemicontinuousAt.sup
  statement: {r' : α -> β -> Prop}
  proof: by
  intro b hab
  obtain hb | hb' := hab
  · exact (h b hb).mono fun _ hx => Or.inl hx
  · exact (h' b hb').mono fun _ hx => Or.inr hx

中文:
定理 SemicontinuousAt.上确界
  结论: {r' : α -> β -> 命题}
  证明: by
  intro b hab
  obtain hb | hb' := hab
  · exact (h b hb).mono fun _ hx => Or.inl hx
  · exact (h' b hb').mono fun _ hx => Or.inr hx

Depends on / 依赖: Or.inl, Or.inr
-/
theorem SemicontinuousAt.sup {r' : α -> β -> Prop}
    (h : SemicontinuousAt r x) (h' : SemicontinuousAt r' x) :
    SemicontinuousAt (r ⊔ r') x := by
  intro b hab
  obtain hb | hb' := hab
  · exact (h b hb).mono fun _ hx => Or.inl hx
  · exact (h' b hb').mono fun _ hx => Or.inr hx

/--
theorem `SemicontinuousOn.inf` / 定理 `SemicontinuousOn.inf`

English:
theorem SemicontinuousOn.inf
  statement: {r' : α -> β -> Prop}
  proof: fun x hx => (h x hx).inf (h' x hx)

中文:
定理 SemicontinuousOn.下确界
  结论: {r' : α -> β -> 命题}
  证明: fun x hx => (h x hx).inf (h' x hx)
-/
theorem SemicontinuousOn.inf {r' : α -> β -> Prop}
    (h : SemicontinuousOn r s) (h' : SemicontinuousOn r' s) :
    SemicontinuousOn (r ⊓ r') s := fun x hx => (h x hx).inf (h' x hx)

/--
theorem `SemicontinuousOn.sup` / 定理 `SemicontinuousOn.sup`

English:
theorem SemicontinuousOn.sup
  statement: {r' : α -> β -> Prop}
  proof: fun x hx => (h x hx).sup (h' x hx)

中文:
定理 SemicontinuousOn.上确界
  结论: {r' : α -> β -> 命题}
  证明: fun x hx => (h x hx).sup (h' x hx)
-/
theorem SemicontinuousOn.sup {r' : α -> β -> Prop}
    (h : SemicontinuousOn r s) (h' : SemicontinuousOn r' s) :
    SemicontinuousOn (r ⊔ r') s := fun x hx => (h x hx).sup (h' x hx)

/--
theorem `Semicontinuous.inf` / 定理 `Semicontinuous.inf`

English:
theorem Semicontinuous.inf
  given: {r' : α -> β -> Prop} (h : Semicontinuous r) (h' : Semicontinuous r')
  proof: fun a => (h a).inf (h' a)

中文:
定理 Semicontinuous.下确界
  条件: {r' : α -> β -> 命题} (h : Semicontinuous r) (h' : Semicontinuous r')
  证明: fun a => (h a).inf (h' a)
-/
theorem Semicontinuous.inf {r' : α -> β -> Prop} (h : Semicontinuous r) (h' : Semicontinuous r') :
    Semicontinuous (r ⊓ r') := fun a => (h a).inf (h' a)

/--
theorem `Semicontinuous.sup` / 定理 `Semicontinuous.sup`

English:
theorem Semicontinuous.sup
  given: {r' : α -> β -> Prop} (h : Semicontinuous r) (h' : Semicontinuous r')
  proof: fun a => (h a).sup (h' a)

中文:
定理 Semicontinuous.上确界
  条件: {r' : α -> β -> 命题} (h : Semicontinuous r) (h' : Semicontinuous r')
  证明: fun a => (h a).sup (h' a)
-/
theorem Semicontinuous.sup {r' : α -> β -> Prop} (h : Semicontinuous r) (h' : Semicontinuous r') :
    Semicontinuous (r ⊔ r') := fun a => (h a).sup (h' a)


/--
theorem `SemicontinuousWithinAt.const` / 定理 `SemicontinuousWithinAt.const`

English:
theorem SemicontinuousWithinAt.const
  given: {f : β -> Prop}
  statement: SemicontinuousWithinAt (fun _x => f) s x
  proof: fun _y hy => Filter.Eventually.of_forall fun _x => hy

中文:
定理 SemicontinuousWithinAt.const
  条件: {f : β -> 命题}
  结论: SemicontinuousWithinAt (fun _x => f) s x
  证明: fun _y hy => Filter.Eventually.of_forall fun _x => hy

Depends on / 依赖: Eventually, Filter, Filter.Eventually.of_forall, of_forall
-/
theorem SemicontinuousWithinAt.const {f : β -> Prop} : SemicontinuousWithinAt (fun _x => f) s x :=
  fun _y hy => Filter.Eventually.of_forall fun _x => hy

/--
theorem `SemicontinuousAt.const` / 定理 `SemicontinuousAt.const`

English:
theorem SemicontinuousAt.const
  given: {f : β -> Prop}
  statement: SemicontinuousAt (fun _x => f) x
  proof: fun _y hy =>
  Filter.Eventually.of_forall fun _x => hy

中文:
定理 SemicontinuousAt.const
  条件: {f : β -> 命题}
  结论: SemicontinuousAt (fun _x => f) x
  证明: fun _y hy =>
  Filter.Eventually.of_forall fun _x => hy
-/
theorem SemicontinuousAt.const {f : β -> Prop} : SemicontinuousAt (fun _x => f) x := fun _y hy =>
  Filter.Eventually.of_forall fun _x => hy

/--
theorem `SemicontinuousOn.const` / 定理 `SemicontinuousOn.const`

English:
theorem SemicontinuousOn.const
  given: {f : β -> Prop}
  statement: SemicontinuousOn (fun _x => f) s
  proof: fun _x _hx =>
  SemicontinuousWithinAt.const

中文:
定理 SemicontinuousOn.const
  条件: {f : β -> 命题}
  结论: SemicontinuousOn (fun _x => f) s
  证明: fun _x _hx =>
  SemicontinuousWithinAt.const
-/
theorem SemicontinuousOn.const {f : β -> Prop} : SemicontinuousOn (fun _x => f) s := fun _x _hx =>
  SemicontinuousWithinAt.const

/--
theorem `Semicontinuous.const` / 定理 `Semicontinuous.const`

English:
theorem Semicontinuous.const
  given: {f : β -> Prop}
  statement: Semicontinuous fun _x : α => f
  proof: fun _x =>
  SemicontinuousAt.const

中文:
定理 Semicontinuous.const
  条件: {f : β -> 命题}
  结论: Semicontinuous fun _x : α => f
  证明: fun _x =>
  SemicontinuousAt.const
-/
theorem Semicontinuous.const {f : β -> Prop} : Semicontinuous fun _x : α => f := fun _x =>
  SemicontinuousAt.const

/-! ### Precomposition with a continuous map -/

variable {x : γ} {g : γ -> α} {s : Set γ} {t : Set α}

/--
lemma `SemicontinuousWithinAt.comp` / 引理 `SemicontinuousWithinAt.comp`

English:
lemma SemicontinuousWithinAt.comp
  statement: (h : SemicontinuousWithinAt r t (g x))
  proof: (hg.tendsto_nhdsWithin hst <| h · ·)

中文:
引理 SemicontinuousWithinAt.comp
  结论: (h : SemicontinuousWithinAt r t (g x))
  证明: (hg.tendsto_nhdsWithin hst <| h · ·)

Depends on / 依赖: hg.tendsto_nhdsWithin, tendsto_nhdsWithin
-/
lemma SemicontinuousWithinAt.comp (h : SemicontinuousWithinAt r t (g x))
    (hg : ContinuousWithinAt g s x) (hst : Set.MapsTo g s t) :
    SemicontinuousWithinAt (r ∘ g) s x :=
  (hg.tendsto_nhdsWithin hst <| h · ·)

/--
lemma `SemicontinuousOn.comp` / 引理 `SemicontinuousOn.comp`

English:
lemma SemicontinuousOn.comp
  statement: {r : α -> β -> Prop} {γ : Type*}
  proof: .comp (hg x hx) hst fun x hx => h (g x) (hst hx)

中文:
引理 SemicontinuousOn.comp
  结论: {r : α -> β -> 命题} {γ : 类型}
  证明: .comp (hg x hx) hst fun x hx => h (g x) (hst hx)
-/
lemma SemicontinuousOn.comp {r : α -> β -> Prop} {γ : Type*}
    [TopologicalSpace γ] {g : γ -> α} {s : Set γ} {t : Set α}
    (h : SemicontinuousOn r t) (hg : ContinuousOn g s)
    (hst : Set.MapsTo g s t) :
    SemicontinuousOn (r ∘ g) s :=
.comp (hg x hx) hst fun x hx => h (g x) (hst hx)

/--
lemma `SemicontinuousAt.comp` / 引理 `SemicontinuousAt.comp`

English:
lemma SemicontinuousAt.comp
  statement: {r : α -> β -> Prop} {γ : Type*} [TopologicalSpace γ]
  proof: (hg <| h · ·)

中文:
引理 SemicontinuousAt.comp
  结论: {r : α -> β -> 命题} {γ : 类型} [拓扑空间 γ]
  证明: (hg <| h · ·)
-/
lemma SemicontinuousAt.comp {r : α -> β -> Prop} {γ : Type*} [TopologicalSpace γ]
    {x : γ} {g : γ -> α} (h : SemicontinuousAt r (g x)) (hg : ContinuousAt g x) :
    SemicontinuousAt (r ∘ g) x :=
  (hg <| h · ·)

/--
lemma `Semicontinuous.comp` / 引理 `Semicontinuous.comp`

English:
lemma Semicontinuous.comp
  statement: {r : α -> β -> Prop} {γ : Type*} [TopologicalSpace γ]
  proof: fun _ => (h.semicontinuousAt _).comp hg.continuousAt

中文:
引理 Semicontinuous.comp
  结论: {r : α -> β -> 命题} {γ : 类型} [拓扑空间 γ]
  证明: fun _ => (h.semicontinuousAt _).comp hg.continuousAt

Depends on / 依赖: continuousAt, h.semicontinuousAt, hg.continuousAt, semicontinuousAt
-/
lemma Semicontinuous.comp {r : α -> β -> Prop} {γ : Type*} [TopologicalSpace γ]
    {g : γ -> α} (h : Semicontinuous r) (hg : Continuous g) :
    Semicontinuous (r ∘ g) :=
  fun _ => (h.semicontinuousAt _).comp hg.continuousAt

end Semicontinuous

section Preorder

/-! ## Lower and Upper Semicontinuity -/

variable [Preorder β] {f g : α -> β} {x : α} {s t : Set α} {y z : β}

section Definitions

/- In https://leanprover.zulipchat.com/#narrow/channel/116395-maths/topic/Semicontinuity.20definition.20for.20non-linear.20orders/with/436241797
it was suggested to redefine `LowerSemicontinuous` in a way that works better for partial orders.
The following example shows that this redefinition can still take place even in light of the
refactor in terms of `Semicontinuous`. -/

example : Semicontinuous (¬ f · <= ·) ↔ forall x y, (existsᶠ x' in 𝓝 x, f x' <= y) -> f x <= y := by
  simp_rw [Semicontinuous, SemicontinuousAt, ← not_frequently, not_imp_not]

/--
Definition of `LowerSemicontinuousWithinAt` / `LowerSemicontinuousWithinAt` 的定义

English:
abbreviation LowerSemicontinuousWithinAt
  signature: (f : α -> β) (s : Set α) (x : α)
  body: SemicontinuousWithinAt (f · > ·) s x

中文:
缩写 LowerSemicontinuousWithinAt
  签名: (f : α -> β) (s : 集合 α) (x : α)
  定义体: SemicontinuousWithinAt (f · > ·) s x

Depends on / 依赖: SemicontinuousWithinAt
-/
abbrev LowerSemicontinuousWithinAt (f : α -> β) (s : Set α) (x : α) :=
  SemicontinuousWithinAt (f · > ·) s x

/--
Definition of `LowerSemicontinuousOn` / `LowerSemicontinuousOn` 的定义

English:
abbreviation LowerSemicontinuousOn
  signature: (f : α -> β) (s : Set α)
  body: SemicontinuousOn (f · > ·) s

中文:
缩写 LowerSemicontinuousOn
  签名: (f : α -> β) (s : 集合 α)
  定义体: SemicontinuousOn (f · > ·) s

Depends on / 依赖: SemicontinuousOn
-/
abbrev LowerSemicontinuousOn (f : α -> β) (s : Set α) :=
  SemicontinuousOn (f · > ·) s

/--
Definition of `LowerSemicontinuousAt` / `LowerSemicontinuousAt` 的定义

English:
abbreviation LowerSemicontinuousAt
  signature: (f : α -> β) (x : α)
  body: SemicontinuousAt (f · > ·) x

中文:
缩写 LowerSemicontinuousAt
  签名: (f : α -> β) (x : α)
  定义体: SemicontinuousAt (f · > ·) x

Depends on / 依赖: SemicontinuousAt
-/
abbrev LowerSemicontinuousAt (f : α -> β) (x : α) :=
  SemicontinuousAt (f · > ·) x

/--
Definition of `LowerSemicontinuous` / `LowerSemicontinuous` 的定义

English:
abbreviation LowerSemicontinuous
  signature: (f : α -> β)
  body: Semicontinuous (f · > ·)

中文:
缩写 LowerSemicontinuous
  签名: (f : α -> β)
  定义体: Semicontinuous (f · > ·)

Depends on / 依赖: Semicontinuous
-/
abbrev LowerSemicontinuous (f : α -> β) :=
  Semicontinuous (f · > ·)

/--
Definition of `UpperSemicontinuousWithinAt` / `UpperSemicontinuousWithinAt` 的定义

English:
abbreviation UpperSemicontinuousWithinAt
  signature: (f : α -> β) (s : Set α) (x : α)
  body: SemicontinuousWithinAt (f · < ·) s x

中文:
缩写 UpperSemicontinuousWithinAt
  签名: (f : α -> β) (s : 集合 α) (x : α)
  定义体: SemicontinuousWithinAt (f · < ·) s x

Depends on / 依赖: SemicontinuousWithinAt
-/
abbrev UpperSemicontinuousWithinAt (f : α -> β) (s : Set α) (x : α) :=
  SemicontinuousWithinAt (f · < ·) s x

/--
Definition of `UpperSemicontinuousOn` / `UpperSemicontinuousOn` 的定义

English:
abbreviation UpperSemicontinuousOn
  signature: (f : α -> β) (s : Set α)
  body: SemicontinuousOn (f · < ·) s

中文:
缩写 UpperSemicontinuousOn
  签名: (f : α -> β) (s : 集合 α)
  定义体: SemicontinuousOn (f · < ·) s

Depends on / 依赖: SemicontinuousOn
-/
abbrev UpperSemicontinuousOn (f : α -> β) (s : Set α) :=
  SemicontinuousOn (f · < ·) s

/--
Definition of `UpperSemicontinuousAt` / `UpperSemicontinuousAt` 的定义

English:
abbreviation UpperSemicontinuousAt
  signature: (f : α -> β) (x : α)
  body: SemicontinuousAt (f · < ·) x

中文:
缩写 UpperSemicontinuousAt
  签名: (f : α -> β) (x : α)
  定义体: SemicontinuousAt (f · < ·) x

Depends on / 依赖: SemicontinuousAt
-/
abbrev UpperSemicontinuousAt (f : α -> β) (x : α) :=
  SemicontinuousAt (f · < ·) x

/--
Definition of `UpperSemicontinuous` / `UpperSemicontinuous` 的定义

English:
abbreviation UpperSemicontinuous
  signature: (f : α -> β)
  body: Semicontinuous (f · < ·)

中文:
缩写 UpperSemicontinuous
  签名: (f : α -> β)
  定义体: Semicontinuous (f · < ·)

Depends on / 依赖: Semicontinuous
-/
abbrev UpperSemicontinuous (f : α -> β) :=
  Semicontinuous (f · < ·)

/--
lemma `lowerSemicontinuousWithinAt_iff` / 引理 `lowerSemicontinuousWithinAt_iff`

English:
lemma lowerSemicontinuousWithinAt_iff
  given: {f : α -> β} {s : Set α} {x : α}
  proof: Iff.rfl

中文:
引理 lowerSemicontinuousWithinAt_iff
  条件: {f : α -> β} {s : 集合 α} {x : α}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma lowerSemicontinuousWithinAt_iff {f : α -> β} {s : Set α} {x : α} :
    LowerSemicontinuousWithinAt f s x ↔ forall y, y < f x -> forallᶠ x' in 𝓝[s] x, y < f x' :=
  Iff.rfl

/--
lemma `lowerSemicontinuousOn_iff` / 引理 `lowerSemicontinuousOn_iff`

English:
lemma lowerSemicontinuousOn_iff
  given: {f : α -> β} {s : Set α}
  proof: Iff.rfl

中文:
引理 lowerSemicontinuousOn_iff
  条件: {f : α -> β} {s : 集合 α}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma lowerSemicontinuousOn_iff {f : α -> β} {s : Set α} :
    LowerSemicontinuousOn f s ↔ forall x in s, LowerSemicontinuousWithinAt f s x :=
  Iff.rfl

/--
lemma `lowerSemicontinuousAt_iff` / 引理 `lowerSemicontinuousAt_iff`

English:
lemma lowerSemicontinuousAt_iff
  given: {f : α -> β} {x : α}
  proof: Iff.rfl

中文:
引理 lowerSemicontinuousAt_iff
  条件: {f : α -> β} {x : α}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma lowerSemicontinuousAt_iff {f : α -> β} {x : α} :
    LowerSemicontinuousAt f x ↔ forall y, y < f x -> forallᶠ x' in 𝓝 x, y < f x' :=
  Iff.rfl

/--
lemma `lowerSemicontinuous_iff` / 引理 `lowerSemicontinuous_iff`

English:
lemma lowerSemicontinuous_iff
  given: {f : α -> β}
  proof: Iff.rfl

中文:
引理 lowerSemicontinuous_iff
  条件: {f : α -> β}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma lowerSemicontinuous_iff {f : α -> β} :
    LowerSemicontinuous f ↔ forall x, LowerSemicontinuousAt f x :=
  Iff.rfl

/--
lemma `upperSemicontinuousWithinAt_iff` / 引理 `upperSemicontinuousWithinAt_iff`

English:
lemma upperSemicontinuousWithinAt_iff
  given: {f : α -> β} {s : Set α} {x : α}
  proof: Iff.rfl

中文:
引理 upperSemicontinuousWithinAt_iff
  条件: {f : α -> β} {s : 集合 α} {x : α}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma upperSemicontinuousWithinAt_iff {f : α -> β} {s : Set α} {x : α} :
    UpperSemicontinuousWithinAt f s x ↔ forall y, f x < y -> forallᶠ x' in 𝓝[s] x, f x' < y :=
  Iff.rfl

/--
lemma `upperSemicontinuousOn_iff` / 引理 `upperSemicontinuousOn_iff`

English:
lemma upperSemicontinuousOn_iff
  given: {f : α -> β} {s : Set α}
  proof: Iff.rfl

中文:
引理 upperSemicontinuousOn_iff
  条件: {f : α -> β} {s : 集合 α}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma upperSemicontinuousOn_iff {f : α -> β} {s : Set α} :
    UpperSemicontinuousOn f s ↔ forall x in s, UpperSemicontinuousWithinAt f s x :=
  Iff.rfl

/--
lemma `upperSemicontinuousAt_iff` / 引理 `upperSemicontinuousAt_iff`

English:
lemma upperSemicontinuousAt_iff
  given: {f : α -> β} {x : α}
  proof: Iff.rfl

中文:
引理 upperSemicontinuousAt_iff
  条件: {f : α -> β} {x : α}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma upperSemicontinuousAt_iff {f : α -> β} {x : α} :
    UpperSemicontinuousAt f x ↔ forall y, f x < y -> forallᶠ x' in 𝓝 x, f x' < y :=
  Iff.rfl

/--
lemma `upperSemicontinuous_iff` / 引理 `upperSemicontinuous_iff`

English:
lemma upperSemicontinuous_iff
  given: {f : α -> β}
  proof: Iff.rfl

中文:
引理 upperSemicontinuous_iff
  条件: {f : α -> β}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma upperSemicontinuous_iff {f : α -> β} :
    UpperSemicontinuous f ↔ forall x, UpperSemicontinuousAt f x :=
  Iff.rfl

end Definitions

/-!
### Lower semicontinuous functions
-/


/--
theorem `LowerSemicontinuousWithinAt.mono` / 定理 `LowerSemicontinuousWithinAt.mono`

English:
theorem LowerSemicontinuousWithinAt.mono
  given: (h : LowerSemicontinuousWithinAt f s x) (hst : t subseteq s)
  proof: SemicontinuousWithinAt.mono h hst

中文:
定理 LowerSemicontinuousWithinAt.mono
  条件: (h : LowerSemicontinuousWithinAt f s x) (hst : t subseteq s)
  证明: SemicontinuousWithinAt.mono h hst

Depends on / 依赖: SemicontinuousWithinAt, SemicontinuousWithinAt.mono
-/
theorem LowerSemicontinuousWithinAt.mono (h : LowerSemicontinuousWithinAt f s x) (hst : t subseteq s) :
    LowerSemicontinuousWithinAt f t x :=
  SemicontinuousWithinAt.mono h hst

/--
theorem `LowerSemicontinuousWithinAt.congr_of_eventuallyEq` / 定理 `LowerSemicontinuousWithinAt.congr_of_eventuallyEq`

English:
theorem LowerSemicontinuousWithinAt.congr_of_eventuallyEq
  statement: {a : α}
  proof: SemicontinuousWithinAt.congr_of_eventuallyEq h has by
    filter_upwards [hfg] with x hx
    simp [hx]

中文:
定理 LowerSemicontinuousWithinAt.congr_of_eventuallyEq
  结论: {a : α}
  证明: SemicontinuousWithinAt.congr_of_eventuallyEq h has by
    filter_upwards [hfg] with x hx
    simp [hx]

Depends on / 依赖: SemicontinuousWithinAt, SemicontinuousWithinAt.congr_of_eventuallyEq, congr_of_eventuallyEq, filter_upwards
-/
theorem LowerSemicontinuousWithinAt.congr_of_eventuallyEq {a : α}
    (h : LowerSemicontinuousWithinAt f s a)
    (has : a in s) (hfg : f =ᶠ[𝓝[s] a] g) :
    LowerSemicontinuousWithinAt g s a :=
SemicontinuousWithinAt.congr_of_eventuallyEq h has by
    filter_upwards [hfg] with x hx
    simp [hx]

/--
theorem `lowerSemicontinuousWithinAt_univ_iff` / 定理 `lowerSemicontinuousWithinAt_univ_iff`

English:
theorem lowerSemicontinuousWithinAt_univ_iff
  proof: semicontinuousWithinAt_univ_iff

中文:
定理 lowerSemicontinuousWithinAt_univ_iff
  证明: semicontinuousWithinAt_univ_iff

Depends on / 依赖: semicontinuousWithinAt_univ_iff
-/
theorem lowerSemicontinuousWithinAt_univ_iff :
    LowerSemicontinuousWithinAt f univ x ↔ LowerSemicontinuousAt f x :=
  semicontinuousWithinAt_univ_iff

/--
theorem `LowerSemicontinuousAt.lowerSemicontinuousWithinAt` / 定理 `LowerSemicontinuousAt.lowerSemicontinuousWithinAt`

English:
theorem LowerSemicontinuousAt.lowerSemicontinuousWithinAt
  statement: (s : Set α)
  proof: h.semicontinuousWithinAt s

中文:
定理 LowerSemicontinuousAt.lowerSemicontinuousWithinAt
  结论: (s : 集合 α)
  证明: h.semicontinuousWithinAt s

Depends on / 依赖: h.semicontinuousWithinAt, semicontinuousWithinAt
-/
theorem LowerSemicontinuousAt.lowerSemicontinuousWithinAt (s : Set α)
    (h : LowerSemicontinuousAt f x) : LowerSemicontinuousWithinAt f s x :=
  h.semicontinuousWithinAt s

/--
theorem `LowerSemicontinuousOn.lowerSemicontinuousWithinAt` / 定理 `LowerSemicontinuousOn.lowerSemicontinuousWithinAt`

English:
theorem LowerSemicontinuousOn.lowerSemicontinuousWithinAt
  statement: (h : LowerSemicontinuousOn f s)
  proof: h.semicontinuousWithinAt hx

中文:
定理 LowerSemicontinuousOn.lowerSemicontinuousWithinAt
  结论: (h : LowerSemicontinuousOn f s)
  证明: h.semicontinuousWithinAt hx

Depends on / 依赖: h.semicontinuousWithinAt, semicontinuousWithinAt
-/
theorem LowerSemicontinuousOn.lowerSemicontinuousWithinAt (h : LowerSemicontinuousOn f s)
    (hx : x in s) : LowerSemicontinuousWithinAt f s x :=
  h.semicontinuousWithinAt hx

/--
theorem `LowerSemicontinuousOn.mono` / 定理 `LowerSemicontinuousOn.mono`

English:
theorem LowerSemicontinuousOn.mono
  given: (h : LowerSemicontinuousOn f s) (hst : t subseteq s)
  proof: SemicontinuousOn.mono h hst

中文:
定理 LowerSemicontinuousOn.mono
  条件: (h : LowerSemicontinuousOn f s) (hst : t subseteq s)
  证明: SemicontinuousOn.mono h hst

Depends on / 依赖: SemicontinuousOn, SemicontinuousOn.mono
-/
theorem LowerSemicontinuousOn.mono (h : LowerSemicontinuousOn f s) (hst : t subseteq s) :
    LowerSemicontinuousOn f t :=
  SemicontinuousOn.mono h hst

/--
theorem `lowerSemicontinuousOn_univ_iff` / 定理 `lowerSemicontinuousOn_univ_iff`

English:
theorem lowerSemicontinuousOn_univ_iff
  statement: LowerSemicontinuousOn f univ ↔ LowerSemicontinuous f
  proof: semicontinuousOn_univ_iff

中文:
定理 lowerSemicontinuousOn_univ_iff
  结论: LowerSemicontinuousOn f univ ↔ LowerSemicontinuous f
  证明: semicontinuousOn_univ_iff

Depends on / 依赖: semicontinuousOn_univ_iff
-/
theorem lowerSemicontinuousOn_univ_iff : LowerSemicontinuousOn f univ ↔ LowerSemicontinuous f :=
  semicontinuousOn_univ_iff

/--
theorem `lowerSemicontinuous_restrict_iff` / 定理 `lowerSemicontinuous_restrict_iff`

English:
theorem lowerSemicontinuous_restrict_iff
  proof: semicontinuous_restrict_iff (r := (f · > ·))

中文:
定理 lowerSemicontinuous_restrict_iff
  证明: semicontinuous_restrict_iff (r := (f · > ·))
-/
@[simp] theorem lowerSemicontinuous_restrict_iff :
    LowerSemicontinuous (s.domRestrict f) ↔ LowerSemicontinuousOn f s :=
  semicontinuous_restrict_iff (r := (f · > ·))

/--
theorem `LowerSemicontinuous.lowerSemicontinuousAt` / 定理 `LowerSemicontinuous.lowerSemicontinuousAt`

English:
theorem LowerSemicontinuous.lowerSemicontinuousAt
  given: (h : LowerSemicontinuous f) (x : α)
  proof: h x

中文:
定理 LowerSemicontinuous.lowerSemicontinuousAt
  条件: (h : LowerSemicontinuous f) (x : α)
  证明: h x
-/
theorem LowerSemicontinuous.lowerSemicontinuousAt (h : LowerSemicontinuous f) (x : α) :
    LowerSemicontinuousAt f x :=
  h x

/--
theorem `LowerSemicontinuous.lowerSemicontinuousWithinAt` / 定理 `LowerSemicontinuous.lowerSemicontinuousWithinAt`

English:
theorem LowerSemicontinuous.lowerSemicontinuousWithinAt
  statement: (h : LowerSemicontinuous f) (s : Set α)
  proof: (h x).semicontinuousWithinAt s

中文:
定理 LowerSemicontinuous.lowerSemicontinuousWithinAt
  结论: (h : LowerSemicontinuous f) (s : 集合 α)
  证明: (h x).semicontinuousWithinAt s

Depends on / 依赖: semicontinuousWithinAt
-/
theorem LowerSemicontinuous.lowerSemicontinuousWithinAt (h : LowerSemicontinuous f) (s : Set α)
    (x : α) : LowerSemicontinuousWithinAt f s x :=
  (h x).semicontinuousWithinAt s

/--
theorem `LowerSemicontinuous.lowerSemicontinuousOn` / 定理 `LowerSemicontinuous.lowerSemicontinuousOn`

English:
theorem LowerSemicontinuous.lowerSemicontinuousOn
  given: (h : LowerSemicontinuous f) (s : Set α)
  proof: h.semicontinuousOn s

中文:
定理 LowerSemicontinuous.lowerSemicontinuousOn
  条件: (h : LowerSemicontinuous f) (s : 集合 α)
  证明: h.semicontinuousOn s

Depends on / 依赖: h.semicontinuousOn, semicontinuousOn
-/
theorem LowerSemicontinuous.lowerSemicontinuousOn (h : LowerSemicontinuous f) (s : Set α) :
    LowerSemicontinuousOn f s :=
  h.semicontinuousOn s


/--
theorem `lowerSemicontinuousWithinAt_const` / 定理 `lowerSemicontinuousWithinAt_const`

English:
theorem lowerSemicontinuousWithinAt_const
  statement: LowerSemicontinuousWithinAt (fun _x => z) s x
  proof: SemicontinuousWithinAt.const

中文:
定理 lowerSemicontinuousWithinAt_const
  结论: LowerSemicontinuousWithinAt (fun _x => z) s x
  证明: SemicontinuousWithinAt.const

Depends on / 依赖: SemicontinuousWithinAt, SemicontinuousWithinAt.const
-/
theorem lowerSemicontinuousWithinAt_const : LowerSemicontinuousWithinAt (fun _x => z) s x :=
  SemicontinuousWithinAt.const

/--
theorem `lowerSemicontinuousAt_const` / 定理 `lowerSemicontinuousAt_const`

English:
theorem lowerSemicontinuousAt_const
  statement: LowerSemicontinuousAt (fun _x => z) x
  proof: SemicontinuousAt.const

中文:
定理 lowerSemicontinuousAt_const
  结论: LowerSemicontinuousAt (fun _x => z) x
  证明: SemicontinuousAt.const

Depends on / 依赖: SemicontinuousAt, SemicontinuousAt.const
-/
theorem lowerSemicontinuousAt_const : LowerSemicontinuousAt (fun _x => z) x :=
  SemicontinuousAt.const

/--
theorem `lowerSemicontinuousOn_const` / 定理 `lowerSemicontinuousOn_const`

English:
theorem lowerSemicontinuousOn_const
  statement: LowerSemicontinuousOn (fun _x => z) s
  proof: SemicontinuousOn.const

中文:
定理 lowerSemicontinuousOn_const
  结论: LowerSemicontinuousOn (fun _x => z) s
  证明: SemicontinuousOn.const

Depends on / 依赖: SemicontinuousOn, SemicontinuousOn.const
-/
theorem lowerSemicontinuousOn_const : LowerSemicontinuousOn (fun _x => z) s :=
  SemicontinuousOn.const

/--
theorem `lowerSemicontinuous_const` / 定理 `lowerSemicontinuous_const`

English:
theorem lowerSemicontinuous_const
  statement: LowerSemicontinuous fun _x : α => z
  proof: Semicontinuous.const

中文:
定理 lowerSemicontinuous_const
  结论: LowerSemicontinuous fun _x : α => z
  证明: Semicontinuous.const

Depends on / 依赖: Semicontinuous, Semicontinuous.const
-/
theorem lowerSemicontinuous_const : LowerSemicontinuous fun _x : α => z :=
  Semicontinuous.const

/-! #### Composition -/
section

variable {g : γ -> α} {x : γ} {t : Set γ}

/--
theorem `LowerSemicontinuousWithinAt.comp` / 定理 `LowerSemicontinuousWithinAt.comp`

English:
theorem LowerSemicontinuousWithinAt.comp
  proof: SemicontinuousWithinAt.comp hf hg hg'

中文:
定理 LowerSemicontinuousWithinAt.comp
  证明: SemicontinuousWithinAt.comp hf hg hg'

Depends on / 依赖: SemicontinuousWithinAt, SemicontinuousWithinAt.comp
-/
theorem LowerSemicontinuousWithinAt.comp
    (hf : LowerSemicontinuousWithinAt f s (g x)) (hg : ContinuousWithinAt g t x)
    (hg' : MapsTo g t s) :
    LowerSemicontinuousWithinAt (f ∘ g) t x :=
  SemicontinuousWithinAt.comp hf hg hg'

/--
theorem `LowerSemicontinuousAt.comp` / 定理 `LowerSemicontinuousAt.comp`

English:
theorem LowerSemicontinuousAt.comp
  proof: SemicontinuousAt.comp hf hg

中文:
定理 LowerSemicontinuousAt.comp
  证明: SemicontinuousAt.comp hf hg

Depends on / 依赖: SemicontinuousAt, SemicontinuousAt.comp
-/
theorem LowerSemicontinuousAt.comp
    (hf : LowerSemicontinuousAt f (g x)) (hg : ContinuousAt g x) :
    LowerSemicontinuousAt (f ∘ g) x :=
  SemicontinuousAt.comp hf hg

/--
theorem `LowerSemicontinuousOn.comp` / 定理 `LowerSemicontinuousOn.comp`

English:
theorem LowerSemicontinuousOn.comp
  proof: SemicontinuousOn.comp hf hg hg'

中文:
定理 LowerSemicontinuousOn.comp
  证明: SemicontinuousOn.comp hf hg hg'

Depends on / 依赖: SemicontinuousOn, SemicontinuousOn.comp
-/
theorem LowerSemicontinuousOn.comp
    (hf : LowerSemicontinuousOn f s) (hg : ContinuousOn g t) (hg' : MapsTo g t s) :
    LowerSemicontinuousOn (f ∘ g) t :=
  SemicontinuousOn.comp hf hg hg'

/--
theorem `LowerSemicontinuous.comp` / 定理 `LowerSemicontinuous.comp`

English:
theorem LowerSemicontinuous.comp
  proof: Semicontinuous.comp hf hg

中文:
定理 LowerSemicontinuous.comp
  证明: Semicontinuous.comp hf hg

Depends on / 依赖: Semicontinuous, Semicontinuous.comp
-/
theorem LowerSemicontinuous.comp
    (hf : LowerSemicontinuous f) (hg : Continuous g) : LowerSemicontinuous (f ∘ g) :=
  Semicontinuous.comp hf hg

end

/-!
### Upper semicontinuous functions
-/




/--
theorem `UpperSemicontinuousWithinAt.mono` / 定理 `UpperSemicontinuousWithinAt.mono`

English:
theorem UpperSemicontinuousWithinAt.mono
  given: (h : UpperSemicontinuousWithinAt f s x) (hst : t subseteq s)
  proof: SemicontinuousWithinAt.mono h hst

中文:
定理 UpperSemicontinuousWithinAt.mono
  条件: (h : UpperSemicontinuousWithinAt f s x) (hst : t subseteq s)
  证明: SemicontinuousWithinAt.mono h hst

Depends on / 依赖: SemicontinuousWithinAt, SemicontinuousWithinAt.mono
-/
theorem UpperSemicontinuousWithinAt.mono (h : UpperSemicontinuousWithinAt f s x) (hst : t subseteq s) :
    UpperSemicontinuousWithinAt f t x :=
  SemicontinuousWithinAt.mono h hst

/--
theorem `UpperSemicontinuousWithinAt.congr_of_eventuallyEq` / 定理 `UpperSemicontinuousWithinAt.congr_of_eventuallyEq`

English:
theorem UpperSemicontinuousWithinAt.congr_of_eventuallyEq
  statement: {a : α}
  proof: LowerSemicontinuousWithinAt.congr_of_eventuallyEq (β := βᵒᵈ) h has hfg

中文:
定理 UpperSemicontinuousWithinAt.congr_of_eventuallyEq
  结论: {a : α}
  证明: LowerSemicontinuousWithinAt.congr_of_eventuallyEq (β := βᵒᵈ) h has hfg

Depends on / 依赖: LowerSemicontinuousWithinAt, LowerSemicontinuousWithinAt.congr_of_eventuallyEq, congr_of_eventuallyEq
-/
theorem UpperSemicontinuousWithinAt.congr_of_eventuallyEq {a : α}
    (h : UpperSemicontinuousWithinAt f s a)
    (has : a in s) (hfg : forallᶠ x in nhdsWithin a s, f x = g x) :
    UpperSemicontinuousWithinAt g s a :=
  LowerSemicontinuousWithinAt.congr_of_eventuallyEq (β := βᵒᵈ) h has hfg

/--
theorem `upperSemicontinuousWithinAt_univ_iff` / 定理 `upperSemicontinuousWithinAt_univ_iff`

English:
theorem upperSemicontinuousWithinAt_univ_iff
  proof: semicontinuousWithinAt_univ_iff

中文:
定理 upperSemicontinuousWithinAt_univ_iff
  证明: semicontinuousWithinAt_univ_iff

Depends on / 依赖: semicontinuousWithinAt_univ_iff
-/
theorem upperSemicontinuousWithinAt_univ_iff :
    UpperSemicontinuousWithinAt f univ x ↔ UpperSemicontinuousAt f x :=
  semicontinuousWithinAt_univ_iff

/--
theorem `upperSemicontinuousOn_iff_restrict` / 定理 `upperSemicontinuousOn_iff_restrict`

English:
theorem upperSemicontinuousOn_iff_restrict
  given: {s : Set α}
  proof: lowerSemicontinuous_restrict_iff (β := βᵒᵈ)

中文:
定理 upperSemicontinuousOn_iff_restrict
  条件: {s : 集合 α}
  证明: lowerSemicontinuous_restrict_iff (β := βᵒᵈ)
-/
@[simp] theorem upperSemicontinuousOn_iff_restrict {s : Set α} :
    UpperSemicontinuous (s.domRestrict f) ↔ UpperSemicontinuousOn f s :=
  lowerSemicontinuous_restrict_iff (β := βᵒᵈ)

/--
theorem `UpperSemicontinuousAt.upperSemicontinuousWithinAt` / 定理 `UpperSemicontinuousAt.upperSemicontinuousWithinAt`

English:
theorem UpperSemicontinuousAt.upperSemicontinuousWithinAt
  statement: (s : Set α)
  proof: h.semicontinuousWithinAt s

中文:
定理 UpperSemicontinuousAt.upperSemicontinuousWithinAt
  结论: (s : 集合 α)
  证明: h.semicontinuousWithinAt s

Depends on / 依赖: h.semicontinuousWithinAt, semicontinuousWithinAt
-/
theorem UpperSemicontinuousAt.upperSemicontinuousWithinAt (s : Set α)
    (h : UpperSemicontinuousAt f x) : UpperSemicontinuousWithinAt f s x :=
  h.semicontinuousWithinAt s

/--
theorem `UpperSemicontinuousOn.upperSemicontinuousWithinAt` / 定理 `UpperSemicontinuousOn.upperSemicontinuousWithinAt`

English:
theorem UpperSemicontinuousOn.upperSemicontinuousWithinAt
  statement: (h : UpperSemicontinuousOn f s)
  proof: h x hx

中文:
定理 UpperSemicontinuousOn.upperSemicontinuousWithinAt
  结论: (h : UpperSemicontinuousOn f s)
  证明: h x hx
-/
theorem UpperSemicontinuousOn.upperSemicontinuousWithinAt (h : UpperSemicontinuousOn f s)
    (hx : x in s) : UpperSemicontinuousWithinAt f s x :=
  h x hx

/--
theorem `UpperSemicontinuousOn.mono` / 定理 `UpperSemicontinuousOn.mono`

English:
theorem UpperSemicontinuousOn.mono
  given: (h : UpperSemicontinuousOn f s) (hst : t subseteq s)
  proof: SemicontinuousOn.mono h hst

中文:
定理 UpperSemicontinuousOn.mono
  条件: (h : UpperSemicontinuousOn f s) (hst : t subseteq s)
  证明: SemicontinuousOn.mono h hst

Depends on / 依赖: SemicontinuousOn, SemicontinuousOn.mono
-/
theorem UpperSemicontinuousOn.mono (h : UpperSemicontinuousOn f s) (hst : t subseteq s) :
    UpperSemicontinuousOn f t :=
  SemicontinuousOn.mono h hst

/--
theorem `upperSemicontinuousOn_univ_iff` / 定理 `upperSemicontinuousOn_univ_iff`

English:
theorem upperSemicontinuousOn_univ_iff
  statement: UpperSemicontinuousOn f univ ↔ UpperSemicontinuous f
  proof: semicontinuousOn_univ_iff

中文:
定理 upperSemicontinuousOn_univ_iff
  结论: UpperSemicontinuousOn f univ ↔ UpperSemicontinuous f
  证明: semicontinuousOn_univ_iff

Depends on / 依赖: semicontinuousOn_univ_iff
-/
theorem upperSemicontinuousOn_univ_iff : UpperSemicontinuousOn f univ ↔ UpperSemicontinuous f :=
  semicontinuousOn_univ_iff

/--
theorem `UpperSemicontinuous.upperSemicontinuousAt` / 定理 `UpperSemicontinuous.upperSemicontinuousAt`

English:
theorem UpperSemicontinuous.upperSemicontinuousAt
  given: (h : UpperSemicontinuous f) (x : α)
  proof: h x

中文:
定理 UpperSemicontinuous.upperSemicontinuousAt
  条件: (h : UpperSemicontinuous f) (x : α)
  证明: h x
-/
theorem UpperSemicontinuous.upperSemicontinuousAt (h : UpperSemicontinuous f) (x : α) :
    UpperSemicontinuousAt f x :=
  h x

/--
theorem `UpperSemicontinuous.upperSemicontinuousWithinAt` / 定理 `UpperSemicontinuous.upperSemicontinuousWithinAt`

English:
theorem UpperSemicontinuous.upperSemicontinuousWithinAt
  statement: (h : UpperSemicontinuous f) (s : Set α)
  proof: (h x).semicontinuousWithinAt s

中文:
定理 UpperSemicontinuous.upperSemicontinuousWithinAt
  结论: (h : UpperSemicontinuous f) (s : 集合 α)
  证明: (h x).semicontinuousWithinAt s

Depends on / 依赖: semicontinuousWithinAt
-/
theorem UpperSemicontinuous.upperSemicontinuousWithinAt (h : UpperSemicontinuous f) (s : Set α)
    (x : α) : UpperSemicontinuousWithinAt f s x :=
  (h x).semicontinuousWithinAt s

/--
theorem `UpperSemicontinuous.upperSemicontinuousOn` / 定理 `UpperSemicontinuous.upperSemicontinuousOn`

English:
theorem UpperSemicontinuous.upperSemicontinuousOn
  given: (h : UpperSemicontinuous f) (s : Set α)
  proof: h.semicontinuousOn s

中文:
定理 UpperSemicontinuous.upperSemicontinuousOn
  条件: (h : UpperSemicontinuous f) (s : 集合 α)
  证明: h.semicontinuousOn s

Depends on / 依赖: h.semicontinuousOn, semicontinuousOn
-/
theorem UpperSemicontinuous.upperSemicontinuousOn (h : UpperSemicontinuous f) (s : Set α) :
    UpperSemicontinuousOn f s :=
  h.semicontinuousOn s


/--
theorem `upperSemicontinuousWithinAt_const` / 定理 `upperSemicontinuousWithinAt_const`

English:
theorem upperSemicontinuousWithinAt_const
  statement: UpperSemicontinuousWithinAt (fun _x => z) s x
  proof: SemicontinuousWithinAt.const

中文:
定理 upperSemicontinuousWithinAt_const
  结论: UpperSemicontinuousWithinAt (fun _x => z) s x
  证明: SemicontinuousWithinAt.const

Depends on / 依赖: SemicontinuousWithinAt, SemicontinuousWithinAt.const
-/
theorem upperSemicontinuousWithinAt_const : UpperSemicontinuousWithinAt (fun _x => z) s x :=
  SemicontinuousWithinAt.const

/--
theorem `upperSemicontinuousAt_const` / 定理 `upperSemicontinuousAt_const`

English:
theorem upperSemicontinuousAt_const
  statement: UpperSemicontinuousAt (fun _x => z) x
  proof: SemicontinuousAt.const

中文:
定理 upperSemicontinuousAt_const
  结论: UpperSemicontinuousAt (fun _x => z) x
  证明: SemicontinuousAt.const

Depends on / 依赖: SemicontinuousAt, SemicontinuousAt.const
-/
theorem upperSemicontinuousAt_const : UpperSemicontinuousAt (fun _x => z) x :=
  SemicontinuousAt.const

/--
theorem `upperSemicontinuousOn_const` / 定理 `upperSemicontinuousOn_const`

English:
theorem upperSemicontinuousOn_const
  statement: UpperSemicontinuousOn (fun _x => z) s
  proof: SemicontinuousOn.const

中文:
定理 upperSemicontinuousOn_const
  结论: UpperSemicontinuousOn (fun _x => z) s
  证明: SemicontinuousOn.const

Depends on / 依赖: SemicontinuousOn, SemicontinuousOn.const
-/
theorem upperSemicontinuousOn_const : UpperSemicontinuousOn (fun _x => z) s :=
  SemicontinuousOn.const

/--
theorem `upperSemicontinuous_const` / 定理 `upperSemicontinuous_const`

English:
theorem upperSemicontinuous_const
  statement: UpperSemicontinuous fun _x : α => z
  proof: Semicontinuous.const

中文:
定理 upperSemicontinuous_const
  结论: UpperSemicontinuous fun _x : α => z
  证明: Semicontinuous.const

Depends on / 依赖: Semicontinuous, Semicontinuous.const
-/
theorem upperSemicontinuous_const : UpperSemicontinuous fun _x : α => z :=
  Semicontinuous.const

/-! #### Composition -/

section

variable {g : γ -> α} {c : γ} {t : Set γ}

/--
theorem `UpperSemicontinuousWithinAt.comp` / 定理 `UpperSemicontinuousWithinAt.comp`

English:
theorem UpperSemicontinuousWithinAt.comp
  proof: SemicontinuousWithinAt.comp (r := (f · < ·)) hf hg hg' -- the elaboration aid is necessary.

中文:
定理 UpperSemicontinuousWithinAt.comp
  证明: SemicontinuousWithinAt.comp (r := (f · < ·)) hf hg hg' -- the elaboration aid is necessary.

Depends on / 依赖: SemicontinuousWithinAt, SemicontinuousWithinAt.comp, elaboration, necessary
-/
theorem UpperSemicontinuousWithinAt.comp
    (hf : UpperSemicontinuousWithinAt f s (g c)) (hg : ContinuousWithinAt g t c)
    (hg' : MapsTo g t s) :
    UpperSemicontinuousWithinAt (f ∘ g) t c :=
  SemicontinuousWithinAt.comp (r := (f · < ·)) hf hg hg' -- the elaboration aid is necessary.

/--
theorem `UpperSemicontinuousAt.comp` / 定理 `UpperSemicontinuousAt.comp`

English:
theorem UpperSemicontinuousAt.comp
  proof: SemicontinuousAt.comp (r := (f · < ·)) hf hg

中文:
定理 UpperSemicontinuousAt.comp
  证明: SemicontinuousAt.comp (r := (f · < ·)) hf hg

Depends on / 依赖: SemicontinuousAt, SemicontinuousAt.comp
-/
theorem UpperSemicontinuousAt.comp
    (hf : UpperSemicontinuousAt f (g c)) (hg : ContinuousAt g c) :
    UpperSemicontinuousAt (f ∘ g) c :=
  SemicontinuousAt.comp (r := (f · < ·)) hf hg

/--
theorem `UpperSemicontinuousOn.comp` / 定理 `UpperSemicontinuousOn.comp`

English:
theorem UpperSemicontinuousOn.comp
  proof: SemicontinuousOn.comp (r := (f · < ·)) hf hg hg'

中文:
定理 UpperSemicontinuousOn.comp
  证明: SemicontinuousOn.comp (r := (f · < ·)) hf hg hg'

Depends on / 依赖: SemicontinuousOn, SemicontinuousOn.comp
-/
theorem UpperSemicontinuousOn.comp
    (hf : UpperSemicontinuousOn f s) (hg : ContinuousOn g t) (hg' : MapsTo g t s) :
    UpperSemicontinuousOn (f ∘ g) t :=
  SemicontinuousOn.comp (r := (f · < ·)) hf hg hg'

/--
theorem `UpperSemicontinuous.comp` / 定理 `UpperSemicontinuous.comp`

English:
theorem UpperSemicontinuous.comp
  proof: Semicontinuous.comp (r := (f · < ·)) hf hg

中文:
定理 UpperSemicontinuous.comp
  证明: Semicontinuous.comp (r := (f · < ·)) hf hg

Depends on / 依赖: Semicontinuous, Semicontinuous.comp
-/
theorem UpperSemicontinuous.comp
    (hf : UpperSemicontinuous f) (hg : Continuous g) : UpperSemicontinuous (f ∘ g) :=
  Semicontinuous.comp (r := (f · < ·)) hf hg

end

end Preorder

section LinearOrder

variable [LinearOrder β] {f g : α -> β} {x : α} {s : Set α}

/--
lemma `lowerSemicontinuousWithinAt_iff_frequently` / 引理 `lowerSemicontinuousWithinAt_iff_frequently`

English:
lemma lowerSemicontinuousWithinAt_iff_frequently
  proof: by
  simp [semicontinuousWithinAt_iff_frequently]

alias ⟨LowerSemicontinuousWithinAt.frequently, LowerSemicontinuousWithinAt.of_frequently⟩ :=
  lowerSemicontinuousWithinAt_iff_frequently

中文:
引理 lowerSemicontinuousWithinAt_iff_frequently
  证明: by
  simp [semicontinuousWithinAt_iff_frequently]

alias ⟨LowerSemicontinuousWithinAt.frequently, LowerSemicontinuousWithinAt.of_frequently⟩ :=
  lowerSemicontinuousWithinAt_iff_frequently

Depends on / 依赖: semicontinuousWithinAt_iff_frequently
-/
lemma lowerSemicontinuousWithinAt_iff_frequently :
    LowerSemicontinuousWithinAt f s x ↔ forall y, (existsᶠ x' in 𝓝[s] x, f x' <= y) -> f x <= y := by
  simp [semicontinuousWithinAt_iff_frequently]

alias ⟨LowerSemicontinuousWithinAt.frequently, LowerSemicontinuousWithinAt.of_frequently⟩ :=
  lowerSemicontinuousWithinAt_iff_frequently

/--
lemma `lowerSemicontinuousOn_iff_frequently` / 引理 `lowerSemicontinuousOn_iff_frequently`

English:
lemma lowerSemicontinuousOn_iff_frequently
  proof: by
  simp [semicontinuousOn_iff_frequently]

alias ⟨LowerSemicontinuousOn.frequently, LowerSemicontinuousOn.of_frequently⟩ :=
  lowerSemicontinuousOn_iff_frequently

中文:
引理 lowerSemicontinuousOn_iff_frequently
  证明: by
  simp [semicontinuousOn_iff_frequently]

alias ⟨LowerSemicontinuousOn.frequently, LowerSemicontinuousOn.of_frequently⟩ :=
  lowerSemicontinuousOn_iff_frequently

Depends on / 依赖: semicontinuousOn_iff_frequently
-/
lemma lowerSemicontinuousOn_iff_frequently :
    LowerSemicontinuousOn f s ↔ forall x in s, forall y, (existsᶠ x' in 𝓝[s] x, f x' <= y) -> f x <= y := by
  simp [semicontinuousOn_iff_frequently]

alias ⟨LowerSemicontinuousOn.frequently, LowerSemicontinuousOn.of_frequently⟩ :=
  lowerSemicontinuousOn_iff_frequently

/--
lemma `lowerSemicontinuousAt_iff_frequently` / 引理 `lowerSemicontinuousAt_iff_frequently`

English:
lemma lowerSemicontinuousAt_iff_frequently
  proof: by
  simp [semicontinuousAt_iff_frequently]

alias ⟨LowerSemicontinuousAt.frequently, LowerSemicontinuousAt.of_frequently⟩ :=
  lowerSemicontinuousAt_iff_frequently

中文:
引理 lowerSemicontinuousAt_iff_frequently
  证明: by
  simp [semicontinuousAt_iff_frequently]

alias ⟨LowerSemicontinuousAt.frequently, LowerSemicontinuousAt.of_frequently⟩ :=
  lowerSemicontinuousAt_iff_frequently

Depends on / 依赖: semicontinuousAt_iff_frequently
-/
lemma lowerSemicontinuousAt_iff_frequently :
    LowerSemicontinuousAt f x ↔ forall y, (existsᶠ x' in 𝓝 x, f x' <= y) -> f x <= y := by
  simp [semicontinuousAt_iff_frequently]

alias ⟨LowerSemicontinuousAt.frequently, LowerSemicontinuousAt.of_frequently⟩ :=
  lowerSemicontinuousAt_iff_frequently

/--
lemma `lowerSemicontinuous_iff_frequently` / 引理 `lowerSemicontinuous_iff_frequently`

English:
lemma lowerSemicontinuous_iff_frequently
  proof: by
  simp [semicontinuous_iff_frequently]

alias ⟨LowerSemicontinuous.frequently, LowerSemicontinuous.of_frequently⟩ :=
  lowerSemicontinuous_iff_frequently

中文:
引理 lowerSemicontinuous_iff_frequently
  证明: by
  simp [semicontinuous_iff_frequently]

alias ⟨LowerSemicontinuous.frequently, LowerSemicontinuous.of_frequently⟩ :=
  lowerSemicontinuous_iff_frequently

Depends on / 依赖: semicontinuous_iff_frequently
-/
lemma lowerSemicontinuous_iff_frequently :
    LowerSemicontinuous f ↔ forall x y, (existsᶠ x' in 𝓝 x, f x' <= y) -> f x <= y := by
  simp [semicontinuous_iff_frequently]

alias ⟨LowerSemicontinuous.frequently, LowerSemicontinuous.of_frequently⟩ :=
  lowerSemicontinuous_iff_frequently

/--
lemma `upperSemicontinuousWithinAt_iff_frequently` / 引理 `upperSemicontinuousWithinAt_iff_frequently`

English:
lemma upperSemicontinuousWithinAt_iff_frequently
  proof: by
  simp [semicontinuousWithinAt_iff_frequently]

alias ⟨UpperSemicontinuousWithinAt.frequently, UpperSemicontinuousWithinAt.of_frequently⟩ :=
  upperSemicontinuousWithinAt_iff_frequently

中文:
引理 upperSemicontinuousWithinAt_iff_frequently
  证明: by
  simp [semicontinuousWithinAt_iff_frequently]

alias ⟨UpperSemicontinuousWithinAt.frequently, UpperSemicontinuousWithinAt.of_frequently⟩ :=
  upperSemicontinuousWithinAt_iff_frequently

Depends on / 依赖: semicontinuousWithinAt_iff_frequently
-/
lemma upperSemicontinuousWithinAt_iff_frequently :
    UpperSemicontinuousWithinAt f s x ↔ forall y, (existsᶠ x' in 𝓝[s] x, f x' >= y) -> f x >= y := by
  simp [semicontinuousWithinAt_iff_frequently]

alias ⟨UpperSemicontinuousWithinAt.frequently, UpperSemicontinuousWithinAt.of_frequently⟩ :=
  upperSemicontinuousWithinAt_iff_frequently

/--
lemma `upperSemicontinuousOn_iff_frequently` / 引理 `upperSemicontinuousOn_iff_frequently`

English:
lemma upperSemicontinuousOn_iff_frequently
  proof: by
  simp [semicontinuousOn_iff_frequently]

alias ⟨UpperSemicontinuousOn.frequently, UpperSemicontinuousOn.of_frequently⟩ :=
  upperSemicontinuousOn_iff_frequently

中文:
引理 upperSemicontinuousOn_iff_frequently
  证明: by
  simp [semicontinuousOn_iff_frequently]

alias ⟨UpperSemicontinuousOn.frequently, UpperSemicontinuousOn.of_frequently⟩ :=
  upperSemicontinuousOn_iff_frequently

Depends on / 依赖: semicontinuousOn_iff_frequently
-/
lemma upperSemicontinuousOn_iff_frequently :
    UpperSemicontinuousOn f s ↔ forall x in s, forall y, (existsᶠ x' in 𝓝[s] x, f x' >= y) -> f x >= y := by
  simp [semicontinuousOn_iff_frequently]

alias ⟨UpperSemicontinuousOn.frequently, UpperSemicontinuousOn.of_frequently⟩ :=
  upperSemicontinuousOn_iff_frequently

/--
lemma `upperSemicontinuousAt_iff_frequently` / 引理 `upperSemicontinuousAt_iff_frequently`

English:
lemma upperSemicontinuousAt_iff_frequently
  proof: by
  simp [semicontinuousAt_iff_frequently]

alias ⟨UpperSemicontinuousAt.frequently, UpperSemicontinuousAt.of_frequently⟩ :=
  upperSemicontinuousAt_iff_frequently

中文:
引理 upperSemicontinuousAt_iff_frequently
  证明: by
  simp [semicontinuousAt_iff_frequently]

alias ⟨UpperSemicontinuousAt.frequently, UpperSemicontinuousAt.of_frequently⟩ :=
  upperSemicontinuousAt_iff_frequently

Depends on / 依赖: semicontinuousAt_iff_frequently
-/
lemma upperSemicontinuousAt_iff_frequently :
    UpperSemicontinuousAt f x ↔ forall y, (existsᶠ x' in 𝓝 x, f x' >= y) -> f x >= y := by
  simp [semicontinuousAt_iff_frequently]

alias ⟨UpperSemicontinuousAt.frequently, UpperSemicontinuousAt.of_frequently⟩ :=
  upperSemicontinuousAt_iff_frequently

/--
lemma `upperSemicontinuous_iff_frequently` / 引理 `upperSemicontinuous_iff_frequently`

English:
lemma upperSemicontinuous_iff_frequently
  proof: by
  simp [semicontinuous_iff_frequently]

alias ⟨UpperSemicontinuous.frequently, UpperSemicontinuous.of_frequently⟩ :=
  upperSemicontinuous_iff_frequently

中文:
引理 upperSemicontinuous_iff_frequently
  证明: by
  simp [semicontinuous_iff_frequently]

alias ⟨UpperSemicontinuous.frequently, UpperSemicontinuous.of_frequently⟩ :=
  upperSemicontinuous_iff_frequently

Depends on / 依赖: semicontinuous_iff_frequently
-/
lemma upperSemicontinuous_iff_frequently :
    UpperSemicontinuous f ↔ forall x y, (existsᶠ x' in 𝓝 x, f x' >= y) -> f x >= y := by
  simp [semicontinuous_iff_frequently]

alias ⟨UpperSemicontinuous.frequently, UpperSemicontinuous.of_frequently⟩ :=
  upperSemicontinuous_iff_frequently

end LinearOrder

section Hemi

/-! ## Lower and Upper Hemicontinuity -/

variable [TopologicalSpace β]

section Definitions

/--
Definition of `LowerHemicontinuousWithinAt` / `LowerHemicontinuousWithinAt` 的定义

English:
abbreviation LowerHemicontinuousWithinAt
  signature: (f : α -> Set β) (s : Set α) (x : α)
  body: SemicontinuousWithinAt (fun x t => IsOpen t ∧ ((f x) inter t).Nonempty) s x

中文:
缩写 LowerHemicontinuousWithinAt
  签名: (f : α -> 集合 β) (s : 集合 α) (x : α)
  定义体: SemicontinuousWithinAt (fun x t => IsOpen t ∧ ((f x) inter t).Nonempty) s x

Depends on / 依赖: IsOpen, Nonempty, SemicontinuousWithinAt
-/
abbrev LowerHemicontinuousWithinAt (f : α -> Set β) (s : Set α) (x : α) :=
  SemicontinuousWithinAt (fun x t => IsOpen t ∧ ((f x) inter t).Nonempty) s x

/--
Definition of `LowerHemicontinuousOn` / `LowerHemicontinuousOn` 的定义

English:
abbreviation LowerHemicontinuousOn
  signature: (f : α -> Set β) (s : Set α)
  body: SemicontinuousOn (fun x t => IsOpen t ∧ ((f x) inter t).Nonempty) s

中文:
缩写 LowerHemicontinuousOn
  签名: (f : α -> 集合 β) (s : 集合 α)
  定义体: SemicontinuousOn (fun x t => IsOpen t ∧ ((f x) inter t).Nonempty) s

Depends on / 依赖: IsOpen, Nonempty, SemicontinuousOn
-/
abbrev LowerHemicontinuousOn (f : α -> Set β) (s : Set α) :=
  SemicontinuousOn (fun x t => IsOpen t ∧ ((f x) inter t).Nonempty) s

/--
Definition of `LowerHemicontinuousAt` / `LowerHemicontinuousAt` 的定义

English:
abbreviation LowerHemicontinuousAt
  signature: (f : α -> Set β) (x : α)
  body: SemicontinuousAt (fun x t => IsOpen t ∧ ((f x) inter t).Nonempty) x

中文:
缩写 LowerHemicontinuousAt
  签名: (f : α -> 集合 β) (x : α)
  定义体: SemicontinuousAt (fun x t => IsOpen t ∧ ((f x) inter t).Nonempty) x

Depends on / 依赖: IsOpen, Nonempty, SemicontinuousAt
-/
abbrev LowerHemicontinuousAt (f : α -> Set β) (x : α) :=
  SemicontinuousAt (fun x t => IsOpen t ∧ ((f x) inter t).Nonempty) x

/--
Definition of `LowerHemicontinuous` / `LowerHemicontinuous` 的定义

English:
abbreviation LowerHemicontinuous
  signature: (f : α -> Set β)
  body: Semicontinuous (fun x t => IsOpen t ∧ ((f x) inter t).Nonempty)

中文:
缩写 LowerHemicontinuous
  签名: (f : α -> 集合 β)
  定义体: Semicontinuous (fun x t => IsOpen t ∧ ((f x) inter t).Nonempty)

Depends on / 依赖: IsOpen, Nonempty, Semicontinuous
-/
abbrev LowerHemicontinuous (f : α -> Set β) :=
  Semicontinuous (fun x t => IsOpen t ∧ ((f x) inter t).Nonempty)

open scoped Topology

/--
Definition of `UpperHemicontinuousWithinAt` / `UpperHemicontinuousWithinAt` 的定义

English:
abbreviation UpperHemicontinuousWithinAt
  signature: (f : α -> Set β) (s : Set α) (x : α)
  body: SemicontinuousWithinAt (fun x t => t in 𝓝ˢ (f x)) s x

中文:
缩写 UpperHemicontinuousWithinAt
  签名: (f : α -> 集合 β) (s : 集合 α) (x : α)
  定义体: SemicontinuousWithinAt (fun x t => t in 𝓝ˢ (f x)) s x

Depends on / 依赖: SemicontinuousWithinAt
-/
abbrev UpperHemicontinuousWithinAt (f : α -> Set β) (s : Set α) (x : α) :=
  SemicontinuousWithinAt (fun x t => t in 𝓝ˢ (f x)) s x

/--
Definition of `UpperHemicontinuousOn` / `UpperHemicontinuousOn` 的定义

English:
abbreviation UpperHemicontinuousOn
  signature: (f : α -> Set β) (s : Set α)
  body: SemicontinuousOn (fun x t => t in 𝓝ˢ (f x)) s

中文:
缩写 UpperHemicontinuousOn
  签名: (f : α -> 集合 β) (s : 集合 α)
  定义体: SemicontinuousOn (fun x t => t in 𝓝ˢ (f x)) s

Depends on / 依赖: SemicontinuousOn
-/
abbrev UpperHemicontinuousOn (f : α -> Set β) (s : Set α) :=
  SemicontinuousOn (fun x t => t in 𝓝ˢ (f x)) s

/--
Definition of `UpperHemicontinuousAt` / `UpperHemicontinuousAt` 的定义

English:
abbreviation UpperHemicontinuousAt
  signature: (f : α -> Set β) (x : α)
  body: SemicontinuousAt (fun x t => t in 𝓝ˢ (f x)) x

中文:
缩写 UpperHemicontinuousAt
  签名: (f : α -> 集合 β) (x : α)
  定义体: SemicontinuousAt (fun x t => t in 𝓝ˢ (f x)) x

Depends on / 依赖: SemicontinuousAt
-/
abbrev UpperHemicontinuousAt (f : α -> Set β) (x : α) :=
  SemicontinuousAt (fun x t => t in 𝓝ˢ (f x)) x

/--
Definition of `UpperHemicontinuous` / `UpperHemicontinuous` 的定义

English:
abbreviation UpperHemicontinuous
  signature: (f : α -> Set β)
  body: Semicontinuous (fun x t => t in 𝓝ˢ (f x))

中文:
缩写 UpperHemicontinuous
  签名: (f : α -> 集合 β)
  定义体: Semicontinuous (fun x t => t in 𝓝ˢ (f x))

Depends on / 依赖: Semicontinuous
-/
abbrev UpperHemicontinuous (f : α -> Set β) :=
  Semicontinuous (fun x t => t in 𝓝ˢ (f x))

/--
lemma `lowerHemicontinuousWithinAt_iff` / 引理 `lowerHemicontinuousWithinAt_iff`

English:
lemma lowerHemicontinuousWithinAt_iff
  given: {f : α -> Set β} {s : Set α} {x : α}
  proof: by
  simp +contextual [SemicontinuousWithinAt]

中文:
引理 lowerHemicontinuousWithinAt_iff
  条件: {f : α -> 集合 β} {s : 集合 α} {x : α}
  证明: by
  simp +contextual [SemicontinuousWithinAt]

Depends on / 依赖: SemicontinuousWithinAt, contextual
-/
lemma lowerHemicontinuousWithinAt_iff {f : α -> Set β} {s : Set α} {x : α} :
    LowerHemicontinuousWithinAt f s x ↔
      forall u, IsOpen u -> ((f x) inter u).Nonempty -> forallᶠ x' in 𝓝[s] x, ((f x') inter u).Nonempty := by
  simp +contextual [SemicontinuousWithinAt]

/--
lemma `lowerHemicontinuousOn_iff` / 引理 `lowerHemicontinuousOn_iff`

English:
lemma lowerHemicontinuousOn_iff
  given: {f : α -> Set β} {s : Set α}
  proof: Iff.rfl

中文:
引理 lowerHemicontinuousOn_iff
  条件: {f : α -> 集合 β} {s : 集合 α}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma lowerHemicontinuousOn_iff {f : α -> Set β} {s : Set α} :
    LowerHemicontinuousOn f s ↔ forall x in s, LowerHemicontinuousWithinAt f s x :=
  Iff.rfl

/--
lemma `lowerHemicontinuousAt_iff` / 引理 `lowerHemicontinuousAt_iff`

English:
lemma lowerHemicontinuousAt_iff
  given: {f : α -> Set β} {x : α}
  proof: by
  simp +contextual [SemicontinuousAt]

中文:
引理 lowerHemicontinuousAt_iff
  条件: {f : α -> 集合 β} {x : α}
  证明: by
  simp +contextual [SemicontinuousAt]

Depends on / 依赖: SemicontinuousAt, contextual
-/
lemma lowerHemicontinuousAt_iff {f : α -> Set β} {x : α} :
    LowerHemicontinuousAt f x ↔
      forall u, IsOpen u -> ((f x) inter u).Nonempty -> forallᶠ x' in 𝓝 x, ((f x') inter u).Nonempty := by
  simp +contextual [SemicontinuousAt]

/--
lemma `lowerHemicontinuous_iff` / 引理 `lowerHemicontinuous_iff`

English:
lemma lowerHemicontinuous_iff
  given: {f : α -> Set β}
  proof: Iff.rfl

中文:
引理 lowerHemicontinuous_iff
  条件: {f : α -> 集合 β}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma lowerHemicontinuous_iff {f : α -> Set β} :
    LowerHemicontinuous f ↔ forall x, LowerHemicontinuousAt f x :=
  Iff.rfl

/--
lemma `upperHemicontinuousWithinAt_iff` / 引理 `upperHemicontinuousWithinAt_iff`

English:
lemma upperHemicontinuousWithinAt_iff
  given: {f : α -> Set β} {s : Set α} {x : α}
  proof: Iff.rfl

中文:
引理 upperHemicontinuousWithinAt_iff
  条件: {f : α -> 集合 β} {s : 集合 α} {x : α}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma upperHemicontinuousWithinAt_iff {f : α -> Set β} {s : Set α} {x : α} :
    UpperHemicontinuousWithinAt f s x ↔ forall t, t in 𝓝ˢ (f x) -> forallᶠ x' in 𝓝[s] x, t in 𝓝ˢ (f x') :=
  Iff.rfl

/--
lemma `upperHemicontinuousOn_iff` / 引理 `upperHemicontinuousOn_iff`

English:
lemma upperHemicontinuousOn_iff
  given: {f : α -> Set β} {s : Set α}
  proof: Iff.rfl

中文:
引理 upperHemicontinuousOn_iff
  条件: {f : α -> 集合 β} {s : 集合 α}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma upperHemicontinuousOn_iff {f : α -> Set β} {s : Set α} :
    UpperHemicontinuousOn f s ↔ forall x in s, UpperHemicontinuousWithinAt f s x :=
  Iff.rfl

/--
lemma `upperHemicontinuousAt_iff` / 引理 `upperHemicontinuousAt_iff`

English:
lemma upperHemicontinuousAt_iff
  given: {f : α -> Set β} {x : α}
  proof: Iff.rfl

中文:
引理 upperHemicontinuousAt_iff
  条件: {f : α -> 集合 β} {x : α}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma upperHemicontinuousAt_iff {f : α -> Set β} {x : α} :
    UpperHemicontinuousAt f x ↔ forall t, t in 𝓝ˢ (f x) -> forallᶠ x' in 𝓝 x, t in 𝓝ˢ (f x') :=
  Iff.rfl

/--
lemma `upperHemicontinuous_iff` / 引理 `upperHemicontinuous_iff`

English:
lemma upperHemicontinuous_iff
  given: {f : α -> Set β}
  proof: Iff.rfl

中文:
引理 upperHemicontinuous_iff
  条件: {f : α -> 集合 β}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma upperHemicontinuous_iff {f : α -> Set β} :
    UpperHemicontinuous f ↔ forall x, UpperHemicontinuousAt f x :=
  Iff.rfl

end Definitions

/-!
### Lower hemicontinuous functions
-/

/-! #### Basic dot notation interface for lower hemicontinuity -/

variable {f g : α -> Set β} {x : α} {s t : Set α} {y z : Set β}

/--
theorem `LowerHemicontinuousWithinAt.mono` / 定理 `LowerHemicontinuousWithinAt.mono`

English:
theorem LowerHemicontinuousWithinAt.mono
  given: (h : LowerHemicontinuousWithinAt f s x) (hst : t subseteq s)
  proof: SemicontinuousWithinAt.mono h hst

中文:
定理 LowerHemicontinuousWithinAt.mono
  条件: (h : LowerHemicontinuousWithinAt f s x) (hst : t subseteq s)
  证明: SemicontinuousWithinAt.mono h hst

Depends on / 依赖: SemicontinuousWithinAt, SemicontinuousWithinAt.mono
-/
theorem LowerHemicontinuousWithinAt.mono (h : LowerHemicontinuousWithinAt f s x) (hst : t subseteq s) :
    LowerHemicontinuousWithinAt f t x :=
  SemicontinuousWithinAt.mono h hst

/--
theorem `LowerHemicontinuousWithinAt.congr_of_eventuallyEq` / 定理 `LowerHemicontinuousWithinAt.congr_of_eventuallyEq`

English:
theorem LowerHemicontinuousWithinAt.congr_of_eventuallyEq
  statement: {a : α}
  proof: SemicontinuousWithinAt.congr_of_eventuallyEq h has by
    filter_upwards [hfg] with x hx
    simp [hx]

中文:
定理 LowerHemicontinuousWithinAt.congr_of_eventuallyEq
  结论: {a : α}
  证明: SemicontinuousWithinAt.congr_of_eventuallyEq h has by
    filter_upwards [hfg] with x hx
    simp [hx]

Depends on / 依赖: SemicontinuousWithinAt, SemicontinuousWithinAt.congr_of_eventuallyEq, congr_of_eventuallyEq, filter_upwards
-/
theorem LowerHemicontinuousWithinAt.congr_of_eventuallyEq {a : α}
    (h : LowerHemicontinuousWithinAt f s a)
    (has : a in s) (hfg : f =ᶠ[𝓝[s] a] g) :
    LowerHemicontinuousWithinAt g s a :=
SemicontinuousWithinAt.congr_of_eventuallyEq h has by
    filter_upwards [hfg] with x hx
    simp [hx]

/--
theorem `lowerHemicontinuousWithinAt_univ_iff` / 定理 `lowerHemicontinuousWithinAt_univ_iff`

English:
theorem lowerHemicontinuousWithinAt_univ_iff
  proof: semicontinuousWithinAt_univ_iff

中文:
定理 lowerHemicontinuousWithinAt_univ_iff
  证明: semicontinuousWithinAt_univ_iff

Depends on / 依赖: semicontinuousWithinAt_univ_iff
-/
theorem lowerHemicontinuousWithinAt_univ_iff :
    LowerHemicontinuousWithinAt f univ x ↔ LowerHemicontinuousAt f x :=
  semicontinuousWithinAt_univ_iff

/--
theorem `LowerHemicontinuousAt.lowerHemicontinuousWithinAt` / 定理 `LowerHemicontinuousAt.lowerHemicontinuousWithinAt`

English:
theorem LowerHemicontinuousAt.lowerHemicontinuousWithinAt
  statement: (s : Set α)
  proof: h.semicontinuousWithinAt s

中文:
定理 LowerHemicontinuousAt.lowerHemicontinuousWithinAt
  结论: (s : 集合 α)
  证明: h.semicontinuousWithinAt s

Depends on / 依赖: h.semicontinuousWithinAt, semicontinuousWithinAt
-/
theorem LowerHemicontinuousAt.lowerHemicontinuousWithinAt (s : Set α)
    (h : LowerHemicontinuousAt f x) : LowerHemicontinuousWithinAt f s x :=
  h.semicontinuousWithinAt s

/--
theorem `LowerHemicontinuousOn.lowerHemicontinuousWithinAt` / 定理 `LowerHemicontinuousOn.lowerHemicontinuousWithinAt`

English:
theorem LowerHemicontinuousOn.lowerHemicontinuousWithinAt
  statement: (h : LowerHemicontinuousOn f s)
  proof: h.semicontinuousWithinAt hx

中文:
定理 LowerHemicontinuousOn.lowerHemicontinuousWithinAt
  结论: (h : LowerHemicontinuousOn f s)
  证明: h.semicontinuousWithinAt hx

Depends on / 依赖: h.semicontinuousWithinAt, semicontinuousWithinAt
-/
theorem LowerHemicontinuousOn.lowerHemicontinuousWithinAt (h : LowerHemicontinuousOn f s)
    (hx : x in s) : LowerHemicontinuousWithinAt f s x :=
  h.semicontinuousWithinAt hx

/--
theorem `LowerHemicontinuousOn.mono` / 定理 `LowerHemicontinuousOn.mono`

English:
theorem LowerHemicontinuousOn.mono
  given: (h : LowerHemicontinuousOn f s) (hst : t subseteq s)
  proof: SemicontinuousOn.mono h hst

中文:
定理 LowerHemicontinuousOn.mono
  条件: (h : LowerHemicontinuousOn f s) (hst : t subseteq s)
  证明: SemicontinuousOn.mono h hst

Depends on / 依赖: SemicontinuousOn, SemicontinuousOn.mono
-/
theorem LowerHemicontinuousOn.mono (h : LowerHemicontinuousOn f s) (hst : t subseteq s) :
    LowerHemicontinuousOn f t :=
  SemicontinuousOn.mono h hst

/--
theorem `lowerHemicontinuousOn_univ_iff` / 定理 `lowerHemicontinuousOn_univ_iff`

English:
theorem lowerHemicontinuousOn_univ_iff
  statement: LowerHemicontinuousOn f univ ↔ LowerHemicontinuous f
  proof: semicontinuousOn_univ_iff

中文:
定理 lowerHemicontinuousOn_univ_iff
  结论: LowerHemicontinuousOn f univ ↔ LowerHemicontinuous f
  证明: semicontinuousOn_univ_iff

Depends on / 依赖: semicontinuousOn_univ_iff
-/
theorem lowerHemicontinuousOn_univ_iff : LowerHemicontinuousOn f univ ↔ LowerHemicontinuous f :=
  semicontinuousOn_univ_iff

/--
theorem `lowerHemicontinuous_restrict_iff` / 定理 `lowerHemicontinuous_restrict_iff`

English:
theorem lowerHemicontinuous_restrict_iff
  proof: semicontinuous_restrict_iff (r := (fun x t => IsOpen t ∧ ((f x) inter t).Nonempty))

中文:
定理 lowerHemicontinuous_restrict_iff
  证明: semicontinuous_restrict_iff (r := (fun x t => IsOpen t ∧ ((f x) inter t).Nonempty))
-/
@[simp] theorem lowerHemicontinuous_restrict_iff :
    LowerHemicontinuous (s.domRestrict f) ↔ LowerHemicontinuousOn f s :=
  semicontinuous_restrict_iff (r := (fun x t => IsOpen t ∧ ((f x) inter t).Nonempty))

/--
theorem `LowerHemicontinuous.lowerHemicontinuousAt` / 定理 `LowerHemicontinuous.lowerHemicontinuousAt`

English:
theorem LowerHemicontinuous.lowerHemicontinuousAt
  given: (h : LowerHemicontinuous f) (x : α)
  proof: h x

中文:
定理 LowerHemicontinuous.lowerHemicontinuousAt
  条件: (h : LowerHemicontinuous f) (x : α)
  证明: h x
-/
theorem LowerHemicontinuous.lowerHemicontinuousAt (h : LowerHemicontinuous f) (x : α) :
    LowerHemicontinuousAt f x :=
  h x

/--
theorem `LowerHemicontinuous.lowerHemicontinuousWithinAt` / 定理 `LowerHemicontinuous.lowerHemicontinuousWithinAt`

English:
theorem LowerHemicontinuous.lowerHemicontinuousWithinAt
  statement: (h : LowerHemicontinuous f) (s : Set α)
  proof: (h x).semicontinuousWithinAt s

中文:
定理 LowerHemicontinuous.lowerHemicontinuousWithinAt
  结论: (h : LowerHemicontinuous f) (s : 集合 α)
  证明: (h x).semicontinuousWithinAt s

Depends on / 依赖: semicontinuousWithinAt
-/
theorem LowerHemicontinuous.lowerHemicontinuousWithinAt (h : LowerHemicontinuous f) (s : Set α)
    (x : α) : LowerHemicontinuousWithinAt f s x :=
  (h x).semicontinuousWithinAt s

/--
theorem `LowerHemicontinuous.lowerHemicontinuousOn` / 定理 `LowerHemicontinuous.lowerHemicontinuousOn`

English:
theorem LowerHemicontinuous.lowerHemicontinuousOn
  given: (h : LowerHemicontinuous f) (s : Set α)
  proof: h.semicontinuousOn s

中文:
定理 LowerHemicontinuous.lowerHemicontinuousOn
  条件: (h : LowerHemicontinuous f) (s : 集合 α)
  证明: h.semicontinuousOn s

Depends on / 依赖: h.semicontinuousOn, semicontinuousOn
-/
theorem LowerHemicontinuous.lowerHemicontinuousOn (h : LowerHemicontinuous f) (s : Set α) :
    LowerHemicontinuousOn f s :=
  h.semicontinuousOn s

/--
lemma `lowerHemicontinuousWithinAt_iff_frequently` / 引理 `lowerHemicontinuousWithinAt_iff_frequently`

English:
lemma lowerHemicontinuousWithinAt_iff_frequently
  proof: by
  rw [lowerHemicontinuousWithinAt_iff]; rw [compl_surjective.forall]
  simp only [isOpen_compl_iff]
  refine forall₂_congr fun t ht => ?_
  rw [← not_imp_not]
  simp [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty, disjoint_compl_right_iff_subset]

alias ⟨LowerHemicontinuousWithinAt.fre

中文:
引理 lowerHemicontinuousWithinAt_iff_frequently
  证明: by
  rw [lowerHemicontinuousWithinAt_iff]; rw [compl_surjective.forall]
  simp only [isOpen_compl_iff]
  refine forall₂_congr fun t ht => ?_
  rw [← not_imp_not]
  simp [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty, disjoint_compl_right_iff_subset]

alias ⟨LowerHemicontinuousWithinAt.fre

Depends on / 依赖: compl_surjective, compl_surjective.forall, disjoint_compl_right_iff_subset, disjoint_iff_inter_eq_empty, isOpen_compl_iff, lowerHemicontinuousWithinAt_iff, not_imp_not, not_nonempty_iff_eq_empty
-/
lemma lowerHemicontinuousWithinAt_iff_frequently :
    LowerHemicontinuousWithinAt f s x ↔
      forall t, IsClosed t -> (existsᶠ x' in 𝓝[s] x, f x' subseteq t) -> f x subseteq t := by
  rw [lowerHemicontinuousWithinAt_iff]; rw [compl_surjective.forall]
  simp only [isOpen_compl_iff]
  refine forall₂_congr fun t ht => ?_
  rw [← not_imp_not]
  simp [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty, disjoint_compl_right_iff_subset]

alias ⟨LowerHemicontinuousWithinAt.frequently, LowerHemicontinuousWithinAt.of_frequently⟩ :=
  lowerHemicontinuousWithinAt_iff_frequently

/--
lemma `lowerHemicontinuousOn_iff_frequently` / 引理 `lowerHemicontinuousOn_iff_frequently`

English:
lemma lowerHemicontinuousOn_iff_frequently
  proof: by
  simp_rw [lowerHemicontinuousOn_iff, lowerHemicontinuousWithinAt_iff_frequently]

alias ⟨LowerHemicontinuousOn.frequently, LowerHemicontinuousOn.of_frequently⟩ :=
  lowerHemicontinuousOn_iff_frequently

中文:
引理 lowerHemicontinuousOn_iff_frequently
  证明: by
  simp_rw [lowerHemicontinuousOn_iff, lowerHemicontinuousWithinAt_iff_frequently]

alias ⟨LowerHemicontinuousOn.frequently, LowerHemicontinuousOn.of_frequently⟩ :=
  lowerHemicontinuousOn_iff_frequently

Depends on / 依赖: lowerHemicontinuousOn_iff, lowerHemicontinuousWithinAt_iff_frequently, simp_rw
-/
lemma lowerHemicontinuousOn_iff_frequently :
    LowerHemicontinuousOn f s ↔
      forall x in s, forall t, IsClosed t -> (existsᶠ x' in 𝓝[s] x, f x' subseteq t) -> f x subseteq t := by
  simp_rw [lowerHemicontinuousOn_iff, lowerHemicontinuousWithinAt_iff_frequently]

alias ⟨LowerHemicontinuousOn.frequently, LowerHemicontinuousOn.of_frequently⟩ :=
  lowerHemicontinuousOn_iff_frequently

/--
lemma `lowerHemicontinuousAt_iff_frequently` / 引理 `lowerHemicontinuousAt_iff_frequently`

English:
lemma lowerHemicontinuousAt_iff_frequently
  proof: by
  rw [← lowerHemicontinuousWithinAt_univ_iff]; rw [lowerHemicontinuousWithinAt_iff_frequently]
  simp

alias ⟨LowerHemicontinuousAt.frequently, LowerHemicontinuousAt.of_frequently⟩ :=
  lowerHemicontinuousAt_iff_frequently

中文:
引理 lowerHemicontinuousAt_iff_frequently
  证明: by
  rw [← lowerHemicontinuousWithinAt_univ_iff]; rw [lowerHemicontinuousWithinAt_iff_frequently]
  simp

alias ⟨LowerHemicontinuousAt.frequently, LowerHemicontinuousAt.of_frequently⟩ :=
  lowerHemicontinuousAt_iff_frequently

Depends on / 依赖: lowerHemicontinuousWithinAt_iff_frequently, lowerHemicontinuousWithinAt_univ_iff
-/
lemma lowerHemicontinuousAt_iff_frequently :
    LowerHemicontinuousAt f x ↔ forall t, IsClosed t -> (existsᶠ x' in 𝓝 x, f x' subseteq t) -> f x subseteq t := by
  rw [← lowerHemicontinuousWithinAt_univ_iff]; rw [lowerHemicontinuousWithinAt_iff_frequently]
  simp

alias ⟨LowerHemicontinuousAt.frequently, LowerHemicontinuousAt.of_frequently⟩ :=
  lowerHemicontinuousAt_iff_frequently

/--
lemma `lowerHemicontinuous_iff_frequently` / 引理 `lowerHemicontinuous_iff_frequently`

English:
lemma lowerHemicontinuous_iff_frequently
  proof: by
  simp_rw [lowerHemicontinuous_iff, lowerHemicontinuousAt_iff_frequently]

alias ⟨LowerHemicontinuous.frequently, LowerHemicontinuous.of_frequently⟩ :=
  lowerHemicontinuous_iff_frequently

中文:
引理 lowerHemicontinuous_iff_frequently
  证明: by
  simp_rw [lowerHemicontinuous_iff, lowerHemicontinuousAt_iff_frequently]

alias ⟨LowerHemicontinuous.frequently, LowerHemicontinuous.of_frequently⟩ :=
  lowerHemicontinuous_iff_frequently

Depends on / 依赖: lowerHemicontinuousAt_iff_frequently, lowerHemicontinuous_iff, simp_rw
-/
lemma lowerHemicontinuous_iff_frequently :
    LowerHemicontinuous f ↔ forall x t, IsClosed t -> (existsᶠ x' in 𝓝 x, f x' subseteq t) -> f x subseteq t := by
  simp_rw [lowerHemicontinuous_iff, lowerHemicontinuousAt_iff_frequently]

alias ⟨LowerHemicontinuous.frequently, LowerHemicontinuous.of_frequently⟩ :=
  lowerHemicontinuous_iff_frequently


/--
theorem `LowerHemicontinuousWithinAt.const` / 定理 `LowerHemicontinuousWithinAt.const`

English:
theorem LowerHemicontinuousWithinAt.const
  statement: LowerHemicontinuousWithinAt (fun _x => z) s x
  proof: SemicontinuousWithinAt.const

中文:
定理 LowerHemicontinuousWithinAt.const
  结论: LowerHemicontinuousWithinAt (fun _x => z) s x
  证明: SemicontinuousWithinAt.const

Depends on / 依赖: SemicontinuousWithinAt, SemicontinuousWithinAt.const
-/
theorem LowerHemicontinuousWithinAt.const : LowerHemicontinuousWithinAt (fun _x => z) s x :=
  SemicontinuousWithinAt.const

/--
theorem `LowerHemicontinuousAt.const` / 定理 `LowerHemicontinuousAt.const`

English:
theorem LowerHemicontinuousAt.const
  statement: LowerHemicontinuousAt (fun _x => z) x
  proof: SemicontinuousAt.const

中文:
定理 LowerHemicontinuousAt.const
  结论: LowerHemicontinuousAt (fun _x => z) x
  证明: SemicontinuousAt.const

Depends on / 依赖: SemicontinuousAt, SemicontinuousAt.const
-/
theorem LowerHemicontinuousAt.const : LowerHemicontinuousAt (fun _x => z) x :=
  SemicontinuousAt.const

/--
theorem `LowerHemicontinuousOn.const` / 定理 `LowerHemicontinuousOn.const`

English:
theorem LowerHemicontinuousOn.const
  statement: LowerHemicontinuousOn (fun _x => z) s
  proof: SemicontinuousOn.const

中文:
定理 LowerHemicontinuousOn.const
  结论: LowerHemicontinuousOn (fun _x => z) s
  证明: SemicontinuousOn.const

Depends on / 依赖: SemicontinuousOn, SemicontinuousOn.const
-/
theorem LowerHemicontinuousOn.const : LowerHemicontinuousOn (fun _x => z) s :=
  SemicontinuousOn.const

/--
theorem `LowerHemicontinuous.const` / 定理 `LowerHemicontinuous.const`

English:
theorem LowerHemicontinuous.const
  statement: LowerHemicontinuous fun _x : α => z
  proof: Semicontinuous.const

中文:
定理 LowerHemicontinuous.const
  结论: LowerHemicontinuous fun _x : α => z
  证明: Semicontinuous.const

Depends on / 依赖: Semicontinuous, Semicontinuous.const
-/
theorem LowerHemicontinuous.const : LowerHemicontinuous fun _x : α => z :=
  Semicontinuous.const

/-! #### Composition -/
section

variable {g : γ -> α} {x : γ} {t : Set γ}

/--
theorem `LowerHemicontinuousWithinAt.comp` / 定理 `LowerHemicontinuousWithinAt.comp`

English:
theorem LowerHemicontinuousWithinAt.comp
  proof: SemicontinuousWithinAt.comp hf hg hg'

中文:
定理 LowerHemicontinuousWithinAt.comp
  证明: SemicontinuousWithinAt.comp hf hg hg'

Depends on / 依赖: SemicontinuousWithinAt, SemicontinuousWithinAt.comp
-/
theorem LowerHemicontinuousWithinAt.comp
    (hf : LowerHemicontinuousWithinAt f s (g x)) (hg : ContinuousWithinAt g t x)
    (hg' : MapsTo g t s) :
    LowerHemicontinuousWithinAt (f ∘ g) t x :=
  SemicontinuousWithinAt.comp hf hg hg'

/--
theorem `LowerHemicontinuousAt.comp` / 定理 `LowerHemicontinuousAt.comp`

English:
theorem LowerHemicontinuousAt.comp
  proof: SemicontinuousAt.comp hf hg

中文:
定理 LowerHemicontinuousAt.comp
  证明: SemicontinuousAt.comp hf hg

Depends on / 依赖: SemicontinuousAt, SemicontinuousAt.comp
-/
theorem LowerHemicontinuousAt.comp
    (hf : LowerHemicontinuousAt f (g x)) (hg : ContinuousAt g x) :
    LowerHemicontinuousAt (f ∘ g) x :=
  SemicontinuousAt.comp hf hg

/--
theorem `LowerHemicontinuousOn.comp` / 定理 `LowerHemicontinuousOn.comp`

English:
theorem LowerHemicontinuousOn.comp
  proof: SemicontinuousOn.comp hf hg hg'

中文:
定理 LowerHemicontinuousOn.comp
  证明: SemicontinuousOn.comp hf hg hg'

Depends on / 依赖: SemicontinuousOn, SemicontinuousOn.comp
-/
theorem LowerHemicontinuousOn.comp
    (hf : LowerHemicontinuousOn f s) (hg : ContinuousOn g t) (hg' : MapsTo g t s) :
    LowerHemicontinuousOn (f ∘ g) t :=
  SemicontinuousOn.comp hf hg hg'

/--
theorem `LowerHemicontinuous.comp` / 定理 `LowerHemicontinuous.comp`

English:
theorem LowerHemicontinuous.comp
  proof: Semicontinuous.comp hf hg

中文:
定理 LowerHemicontinuous.comp
  证明: Semicontinuous.comp hf hg

Depends on / 依赖: Semicontinuous, Semicontinuous.comp
-/
theorem LowerHemicontinuous.comp
    (hf : LowerHemicontinuous f) (hg : Continuous g) : LowerHemicontinuous (f ∘ g) :=
  Semicontinuous.comp hf hg

end

/-!
### Upper hemicontinuous functions
-/


/--
theorem `UpperHemicontinuousWithinAt.mono` / 定理 `UpperHemicontinuousWithinAt.mono`

English:
theorem UpperHemicontinuousWithinAt.mono
  given: (h : UpperHemicontinuousWithinAt f s x) (hst : t subseteq s)
  proof: SemicontinuousWithinAt.mono h hst

中文:
定理 UpperHemicontinuousWithinAt.mono
  条件: (h : UpperHemicontinuousWithinAt f s x) (hst : t subseteq s)
  证明: SemicontinuousWithinAt.mono h hst

Depends on / 依赖: SemicontinuousWithinAt, SemicontinuousWithinAt.mono
-/
theorem UpperHemicontinuousWithinAt.mono (h : UpperHemicontinuousWithinAt f s x) (hst : t subseteq s) :
    UpperHemicontinuousWithinAt f t x :=
  SemicontinuousWithinAt.mono h hst

/--
theorem `UpperHemicontinuousWithinAt.congr_of_eventuallyEq` / 定理 `UpperHemicontinuousWithinAt.congr_of_eventuallyEq`

English:
theorem UpperHemicontinuousWithinAt.congr_of_eventuallyEq
  statement: {a : α}
  proof: SemicontinuousWithinAt.congr_of_eventuallyEq h has by
    filter_upwards [hfg] with x hx
    simp [hx]

中文:
定理 UpperHemicontinuousWithinAt.congr_of_eventuallyEq
  结论: {a : α}
  证明: SemicontinuousWithinAt.congr_of_eventuallyEq h has by
    filter_upwards [hfg] with x hx
    simp [hx]

Depends on / 依赖: SemicontinuousWithinAt, SemicontinuousWithinAt.congr_of_eventuallyEq, congr_of_eventuallyEq, filter_upwards
-/
theorem UpperHemicontinuousWithinAt.congr_of_eventuallyEq {a : α}
    (h : UpperHemicontinuousWithinAt f s a)
    (has : a in s) (hfg : forallᶠ x in nhdsWithin a s, f x = g x) :
    UpperHemicontinuousWithinAt g s a :=
SemicontinuousWithinAt.congr_of_eventuallyEq h has by
    filter_upwards [hfg] with x hx
    simp [hx]

/--
theorem `upperHemicontinuousWithinAt_univ_iff` / 定理 `upperHemicontinuousWithinAt_univ_iff`

English:
theorem upperHemicontinuousWithinAt_univ_iff
  proof: semicontinuousWithinAt_univ_iff

中文:
定理 upperHemicontinuousWithinAt_univ_iff
  证明: semicontinuousWithinAt_univ_iff

Depends on / 依赖: semicontinuousWithinAt_univ_iff
-/
theorem upperHemicontinuousWithinAt_univ_iff :
    UpperHemicontinuousWithinAt f univ x ↔ UpperHemicontinuousAt f x :=
  semicontinuousWithinAt_univ_iff

/--
theorem `upperHemicontinuousOn_iff_restrict` / 定理 `upperHemicontinuousOn_iff_restrict`

English:
theorem upperHemicontinuousOn_iff_restrict
  given: {s : Set α}
  proof: semicontinuous_restrict_iff (r := (fun x t => t in 𝓝ˢ (f x)))

中文:
定理 upperHemicontinuousOn_iff_restrict
  条件: {s : 集合 α}
  证明: semicontinuous_restrict_iff (r := (fun x t => t in 𝓝ˢ (f x)))
-/
@[simp] theorem upperHemicontinuousOn_iff_restrict {s : Set α} :
    UpperHemicontinuous (s.domRestrict f) ↔ UpperHemicontinuousOn f s :=
  semicontinuous_restrict_iff (r := (fun x t => t in 𝓝ˢ (f x)))

/--
theorem `UpperHemicontinuousAt.upperHemicontinuousWithinAt` / 定理 `UpperHemicontinuousAt.upperHemicontinuousWithinAt`

English:
theorem UpperHemicontinuousAt.upperHemicontinuousWithinAt
  statement: (s : Set α)
  proof: h.semicontinuousWithinAt s

中文:
定理 UpperHemicontinuousAt.upperHemicontinuousWithinAt
  结论: (s : 集合 α)
  证明: h.semicontinuousWithinAt s

Depends on / 依赖: h.semicontinuousWithinAt, semicontinuousWithinAt
-/
theorem UpperHemicontinuousAt.upperHemicontinuousWithinAt (s : Set α)
    (h : UpperHemicontinuousAt f x) : UpperHemicontinuousWithinAt f s x :=
  h.semicontinuousWithinAt s

/--
theorem `UpperHemicontinuousOn.upperHemicontinuousWithinAt` / 定理 `UpperHemicontinuousOn.upperHemicontinuousWithinAt`

English:
theorem UpperHemicontinuousOn.upperHemicontinuousWithinAt
  statement: (h : UpperHemicontinuousOn f s)
  proof: h x hx

中文:
定理 UpperHemicontinuousOn.upperHemicontinuousWithinAt
  结论: (h : UpperHemicontinuousOn f s)
  证明: h x hx
-/
theorem UpperHemicontinuousOn.upperHemicontinuousWithinAt (h : UpperHemicontinuousOn f s)
    (hx : x in s) : UpperHemicontinuousWithinAt f s x :=
  h x hx

/--
theorem `UpperHemicontinuousOn.mono` / 定理 `UpperHemicontinuousOn.mono`

English:
theorem UpperHemicontinuousOn.mono
  given: (h : UpperHemicontinuousOn f s) (hst : t subseteq s)
  proof: SemicontinuousOn.mono h hst

中文:
定理 UpperHemicontinuousOn.mono
  条件: (h : UpperHemicontinuousOn f s) (hst : t subseteq s)
  证明: SemicontinuousOn.mono h hst

Depends on / 依赖: SemicontinuousOn, SemicontinuousOn.mono
-/
theorem UpperHemicontinuousOn.mono (h : UpperHemicontinuousOn f s) (hst : t subseteq s) :
    UpperHemicontinuousOn f t :=
  SemicontinuousOn.mono h hst

/--
theorem `upperHemicontinuousOn_univ_iff` / 定理 `upperHemicontinuousOn_univ_iff`

English:
theorem upperHemicontinuousOn_univ_iff
  statement: UpperHemicontinuousOn f univ ↔ UpperHemicontinuous f
  proof: semicontinuousOn_univ_iff

中文:
定理 upperHemicontinuousOn_univ_iff
  结论: UpperHemicontinuousOn f univ ↔ UpperHemicontinuous f
  证明: semicontinuousOn_univ_iff

Depends on / 依赖: semicontinuousOn_univ_iff
-/
theorem upperHemicontinuousOn_univ_iff : UpperHemicontinuousOn f univ ↔ UpperHemicontinuous f :=
  semicontinuousOn_univ_iff

/--
theorem `UpperHemicontinuous.upperHemicontinuousAt` / 定理 `UpperHemicontinuous.upperHemicontinuousAt`

English:
theorem UpperHemicontinuous.upperHemicontinuousAt
  given: (h : UpperHemicontinuous f) (x : α)
  proof: h x

中文:
定理 UpperHemicontinuous.upperHemicontinuousAt
  条件: (h : UpperHemicontinuous f) (x : α)
  证明: h x
-/
theorem UpperHemicontinuous.upperHemicontinuousAt (h : UpperHemicontinuous f) (x : α) :
    UpperHemicontinuousAt f x :=
  h x

/--
theorem `UpperHemicontinuous.upperHemicontinuousWithinAt` / 定理 `UpperHemicontinuous.upperHemicontinuousWithinAt`

English:
theorem UpperHemicontinuous.upperHemicontinuousWithinAt
  statement: (h : UpperHemicontinuous f) (s : Set α)
  proof: (h x).semicontinuousWithinAt s

中文:
定理 UpperHemicontinuous.upperHemicontinuousWithinAt
  结论: (h : UpperHemicontinuous f) (s : 集合 α)
  证明: (h x).semicontinuousWithinAt s

Depends on / 依赖: semicontinuousWithinAt
-/
theorem UpperHemicontinuous.upperHemicontinuousWithinAt (h : UpperHemicontinuous f) (s : Set α)
    (x : α) : UpperHemicontinuousWithinAt f s x :=
  (h x).semicontinuousWithinAt s

/--
theorem `UpperHemicontinuous.upperHemicontinuousOn` / 定理 `UpperHemicontinuous.upperHemicontinuousOn`

English:
theorem UpperHemicontinuous.upperHemicontinuousOn
  given: (h : UpperHemicontinuous f) (s : Set α)
  proof: h.semicontinuousOn s

中文:
定理 UpperHemicontinuous.upperHemicontinuousOn
  条件: (h : UpperHemicontinuous f) (s : 集合 α)
  证明: h.semicontinuousOn s

Depends on / 依赖: h.semicontinuousOn, semicontinuousOn
-/
theorem UpperHemicontinuous.upperHemicontinuousOn (h : UpperHemicontinuous f) (s : Set α) :
    UpperHemicontinuousOn f s :=
  h.semicontinuousOn s

/--
lemma `upperHemicontinuousWithinAt_iff_frequently` / 引理 `upperHemicontinuousWithinAt_iff_frequently`

English:
lemma upperHemicontinuousWithinAt_iff_frequently
  proof: by
  rw [UpperHemicontinuousWithinAt]; rw [semicontinuousWithinAt_iff_frequently]; rw [compl_surjective.forall]
  simp [← subset_interior_iff_mem_nhdsSet, not_subset, forall_isClosed_iff, inter_nonempty]

alias ⟨UpperHemicontinuousWithinAt.frequently, UpperHemicontinuousWithinAt.of_frequently⟩ :=
  

中文:
引理 upperHemicontinuousWithinAt_iff_frequently
  证明: by
  rw [UpperHemicontinuousWithinAt]; rw [semicontinuousWithinAt_iff_frequently]; rw [compl_surjective.forall]
  simp [← subset_interior_iff_mem_nhdsSet, not_subset, forall_isClosed_iff, inter_nonempty]

alias ⟨UpperHemicontinuousWithinAt.frequently, UpperHemicontinuousWithinAt.of_frequently⟩ :=
  

Depends on / 依赖: UpperHemicontinuousWithinAt, compl_surjective, compl_surjective.forall, forall_isClosed_iff, inter_nonempty, not_subset, semicontinuousWithinAt_iff_frequently, subset_interior_iff_mem_nhdsSet
-/
lemma upperHemicontinuousWithinAt_iff_frequently :
    UpperHemicontinuousWithinAt f s x ↔
      forall t, IsClosed t -> (existsᶠ x' in 𝓝[s] x, ((f x') inter t).Nonempty) -> ((f x) inter t).Nonempty := by
  rw [UpperHemicontinuousWithinAt]; rw [semicontinuousWithinAt_iff_frequently]; rw [compl_surjective.forall]
  simp [← subset_interior_iff_mem_nhdsSet, not_subset, forall_isClosed_iff, inter_nonempty]

alias ⟨UpperHemicontinuousWithinAt.frequently, UpperHemicontinuousWithinAt.of_frequently⟩ :=
  upperHemicontinuousWithinAt_iff_frequently

/--
lemma `upperHemicontinuousOn_iff_frequently` / 引理 `upperHemicontinuousOn_iff_frequently`

English:
lemma upperHemicontinuousOn_iff_frequently
  proof: by
  simp_rw [upperHemicontinuousOn_iff, upperHemicontinuousWithinAt_iff_frequently]

alias ⟨UpperHemicontinuousOn.frequently, UpperHemicontinuousOn.of_frequently⟩ :=
  upperHemicontinuousOn_iff_frequently

中文:
引理 upperHemicontinuousOn_iff_frequently
  证明: by
  simp_rw [upperHemicontinuousOn_iff, upperHemicontinuousWithinAt_iff_frequently]

alias ⟨UpperHemicontinuousOn.frequently, UpperHemicontinuousOn.of_frequently⟩ :=
  upperHemicontinuousOn_iff_frequently

Depends on / 依赖: simp_rw, upperHemicontinuousOn_iff, upperHemicontinuousWithinAt_iff_frequently
-/
lemma upperHemicontinuousOn_iff_frequently :
    UpperHemicontinuousOn f s ↔ forall x in s, forall t, IsClosed t ->
      (existsᶠ x' in 𝓝[s] x, ((f x') inter t).Nonempty) -> ((f x) inter t).Nonempty := by
  simp_rw [upperHemicontinuousOn_iff, upperHemicontinuousWithinAt_iff_frequently]

alias ⟨UpperHemicontinuousOn.frequently, UpperHemicontinuousOn.of_frequently⟩ :=
  upperHemicontinuousOn_iff_frequently

/--
lemma `upperHemicontinuousAt_iff_frequently` / 引理 `upperHemicontinuousAt_iff_frequently`

English:
lemma upperHemicontinuousAt_iff_frequently
  proof: by
  rw [← upperHemicontinuousWithinAt_univ_iff]; rw [upperHemicontinuousWithinAt_iff_frequently]
  simp

alias ⟨UpperHemicontinuousAt.frequently, UpperHemicontinuousAt.of_frequently⟩ :=
  upperHemicontinuousAt_iff_frequently

中文:
引理 upperHemicontinuousAt_iff_frequently
  证明: by
  rw [← upperHemicontinuousWithinAt_univ_iff]; rw [upperHemicontinuousWithinAt_iff_frequently]
  simp

alias ⟨UpperHemicontinuousAt.frequently, UpperHemicontinuousAt.of_frequently⟩ :=
  upperHemicontinuousAt_iff_frequently

Depends on / 依赖: upperHemicontinuousWithinAt_iff_frequently, upperHemicontinuousWithinAt_univ_iff
-/
lemma upperHemicontinuousAt_iff_frequently :
    UpperHemicontinuousAt f x ↔
      forall t, IsClosed t -> (existsᶠ x' in 𝓝 x, ((f x') inter t).Nonempty) -> ((f x) inter t).Nonempty := by
  rw [← upperHemicontinuousWithinAt_univ_iff]; rw [upperHemicontinuousWithinAt_iff_frequently]
  simp

alias ⟨UpperHemicontinuousAt.frequently, UpperHemicontinuousAt.of_frequently⟩ :=
  upperHemicontinuousAt_iff_frequently

/--
lemma `upperHemicontinuous_iff_frequently` / 引理 `upperHemicontinuous_iff_frequently`

English:
lemma upperHemicontinuous_iff_frequently
  proof: by
  simp_rw [upperHemicontinuous_iff, upperHemicontinuousAt_iff_frequently]

alias ⟨UpperHemicontinuous.frequently, UpperHemicontinuous.of_frequently⟩ :=
  upperHemicontinuous_iff_frequently

中文:
引理 upperHemicontinuous_iff_frequently
  证明: by
  simp_rw [upperHemicontinuous_iff, upperHemicontinuousAt_iff_frequently]

alias ⟨UpperHemicontinuous.frequently, UpperHemicontinuous.of_frequently⟩ :=
  upperHemicontinuous_iff_frequently

Depends on / 依赖: simp_rw, upperHemicontinuousAt_iff_frequently, upperHemicontinuous_iff
-/
lemma upperHemicontinuous_iff_frequently :
    UpperHemicontinuous f ↔
      forall x t, IsClosed t -> (existsᶠ x' in 𝓝 x, ((f x') inter t).Nonempty) -> ((f x) inter t).Nonempty := by
  simp_rw [upperHemicontinuous_iff, upperHemicontinuousAt_iff_frequently]

alias ⟨UpperHemicontinuous.frequently, UpperHemicontinuous.of_frequently⟩ :=
  upperHemicontinuous_iff_frequently


/--
theorem `UpperHemicontinuousWithinAt.const` / 定理 `UpperHemicontinuousWithinAt.const`

English:
theorem UpperHemicontinuousWithinAt.const
  statement: UpperHemicontinuousWithinAt (fun _x => z) s x
  proof: SemicontinuousWithinAt.const

中文:
定理 UpperHemicontinuousWithinAt.const
  结论: UpperHemicontinuousWithinAt (fun _x => z) s x
  证明: SemicontinuousWithinAt.const

Depends on / 依赖: SemicontinuousWithinAt, SemicontinuousWithinAt.const
-/
theorem UpperHemicontinuousWithinAt.const : UpperHemicontinuousWithinAt (fun _x => z) s x :=
  SemicontinuousWithinAt.const

/--
theorem `UpperHemicontinuousAt.const` / 定理 `UpperHemicontinuousAt.const`

English:
theorem UpperHemicontinuousAt.const
  statement: UpperHemicontinuousAt (fun _x => z) x
  proof: SemicontinuousAt.const

中文:
定理 UpperHemicontinuousAt.const
  结论: UpperHemicontinuousAt (fun _x => z) x
  证明: SemicontinuousAt.const

Depends on / 依赖: SemicontinuousAt, SemicontinuousAt.const
-/
theorem UpperHemicontinuousAt.const : UpperHemicontinuousAt (fun _x => z) x :=
  SemicontinuousAt.const

/--
theorem `UpperHemicontinuousOn.const` / 定理 `UpperHemicontinuousOn.const`

English:
theorem UpperHemicontinuousOn.const
  statement: UpperHemicontinuousOn (fun _x => z) s
  proof: SemicontinuousOn.const

中文:
定理 UpperHemicontinuousOn.const
  结论: UpperHemicontinuousOn (fun _x => z) s
  证明: SemicontinuousOn.const

Depends on / 依赖: SemicontinuousOn, SemicontinuousOn.const
-/
theorem UpperHemicontinuousOn.const : UpperHemicontinuousOn (fun _x => z) s :=
  SemicontinuousOn.const

/--
theorem `UpperHemicontinuous.const` / 定理 `UpperHemicontinuous.const`

English:
theorem UpperHemicontinuous.const
  statement: UpperHemicontinuous fun _x : α => z
  proof: Semicontinuous.const

中文:
定理 UpperHemicontinuous.const
  结论: UpperHemicontinuous fun _x : α => z
  证明: Semicontinuous.const

Depends on / 依赖: Semicontinuous, Semicontinuous.const
-/
theorem UpperHemicontinuous.const : UpperHemicontinuous fun _x : α => z :=
  Semicontinuous.const

/-! #### Composition -/

section

variable {g : γ -> α} {c : γ} {t : Set γ}

/--
theorem `UpperHemicontinuousWithinAt.comp` / 定理 `UpperHemicontinuousWithinAt.comp`

English:
theorem UpperHemicontinuousWithinAt.comp
  proof: -- the elaboration aid is necessary.
  SemicontinuousWithinAt.comp (r := (fun x t => t in 𝓝ˢ (f x))) hf hg hg'

中文:
定理 UpperHemicontinuousWithinAt.comp
  证明: -- the elaboration aid is necessary.
  SemicontinuousWithinAt.comp (r := (fun x t => t in 𝓝ˢ (f x))) hf hg hg'
-/
theorem UpperHemicontinuousWithinAt.comp
    (hf : UpperHemicontinuousWithinAt f s (g c)) (hg : ContinuousWithinAt g t c)
    (hg' : MapsTo g t s) :
    UpperHemicontinuousWithinAt (f ∘ g) t c :=
  -- the elaboration aid is necessary.
  SemicontinuousWithinAt.comp (r := (fun x t => t in 𝓝ˢ (f x))) hf hg hg'

/--
theorem `UpperHemicontinuousAt.comp` / 定理 `UpperHemicontinuousAt.comp`

English:
theorem UpperHemicontinuousAt.comp
  proof: SemicontinuousAt.comp (r := (fun x t => t in 𝓝ˢ (f x))) hf hg

中文:
定理 UpperHemicontinuousAt.comp
  证明: SemicontinuousAt.comp (r := (fun x t => t in 𝓝ˢ (f x))) hf hg

Depends on / 依赖: SemicontinuousAt, SemicontinuousAt.comp
-/
theorem UpperHemicontinuousAt.comp
    (hf : UpperHemicontinuousAt f (g c)) (hg : ContinuousAt g c) :
    UpperHemicontinuousAt (f ∘ g) c :=
  SemicontinuousAt.comp (r := (fun x t => t in 𝓝ˢ (f x))) hf hg

/--
theorem `UpperHemicontinuousOn.comp` / 定理 `UpperHemicontinuousOn.comp`

English:
theorem UpperHemicontinuousOn.comp
  proof: SemicontinuousOn.comp (r := (fun x t => t in 𝓝ˢ (f x))) hf hg hg'

中文:
定理 UpperHemicontinuousOn.comp
  证明: SemicontinuousOn.comp (r := (fun x t => t in 𝓝ˢ (f x))) hf hg hg'

Depends on / 依赖: SemicontinuousOn, SemicontinuousOn.comp
-/
theorem UpperHemicontinuousOn.comp
    (hf : UpperHemicontinuousOn f s) (hg : ContinuousOn g t) (hg' : MapsTo g t s) :
    UpperHemicontinuousOn (f ∘ g) t :=
  SemicontinuousOn.comp (r := (fun x t => t in 𝓝ˢ (f x))) hf hg hg'

/--
theorem `UpperHemicontinuous.comp` / 定理 `UpperHemicontinuous.comp`

English:
theorem UpperHemicontinuous.comp
  proof: Semicontinuous.comp (r := (fun x t => t in 𝓝ˢ (f x))) hf hg

中文:
定理 UpperHemicontinuous.comp
  证明: Semicontinuous.comp (r := (fun x t => t in 𝓝ˢ (f x))) hf hg

Depends on / 依赖: Semicontinuous, Semicontinuous.comp
-/
theorem UpperHemicontinuous.comp
    (hf : UpperHemicontinuous f) (hg : Continuous g) : UpperHemicontinuous (f ∘ g) :=
  Semicontinuous.comp (r := (fun x t => t in 𝓝ˢ (f x))) hf hg

end

end Hemi

section Sections

/-! ## Open lower sections -/

/-! ### Definitions -/

/--
Definition of `HasOpenLowerSectionsOn` / `HasOpenLowerSectionsOn` 的定义

English:
abbreviation HasOpenLowerSectionsOn
  signature: (f : α -> Set β) (s : Set α)
  body: SemicontinuousOn (fun x b => b in f x) s

中文:
缩写 HasOpenLowerSectionsOn
  签名: (f : α -> 集合 β) (s : 集合 α)
  定义体: SemicontinuousOn (fun x b => b in f x) s

Depends on / 依赖: SemicontinuousOn
-/
abbrev HasOpenLowerSectionsOn (f : α -> Set β) (s : Set α) :=
  SemicontinuousOn (fun x b => b in f x) s

/--
Definition of `HasOpenLowerSections` / `HasOpenLowerSections` 的定义

English:
abbreviation HasOpenLowerSections
  signature: (f : α -> Set β)
  body: Semicontinuous (fun x b => b in f x)

中文:
缩写 HasOpenLowerSections
  签名: (f : α -> 集合 β)
  定义体: Semicontinuous (fun x b => b in f x)

Depends on / 依赖: Semicontinuous
-/
abbrev HasOpenLowerSections (f : α -> Set β) :=
  Semicontinuous (fun x b => b in f x)

variable {f g : α -> Set β} {x : α} {s t : Set α} {z : Set β}

/--
theorem `hasOpenLowerSections_iff_isOpen` / 定理 `hasOpenLowerSections_iff_isOpen`

English:
theorem hasOpenLowerSections_iff_isOpen
  statement: HasOpenLowerSections f ↔ forall b, IsOpen {x | b in f x}
  proof: by
  simp [semicontinuous_iff_isOpen]

中文:
定理 hasOpenLowerSections_iff_isOpen
  结论: HasOpenLowerSections f ↔ 对任意 b, 是开集 {x | b in f x}
  证明: by
  simp [semicontinuous_iff_isOpen]

Depends on / 依赖: semicontinuous_iff_isOpen
-/
theorem hasOpenLowerSections_iff_isOpen : HasOpenLowerSections f ↔ forall b, IsOpen {x | b in f x} := by
  simp [semicontinuous_iff_isOpen]


/--
theorem `HasOpenLowerSectionsOn.mono` / 定理 `HasOpenLowerSectionsOn.mono`

English:
theorem HasOpenLowerSectionsOn.mono
  given: (h : HasOpenLowerSectionsOn f s) (hst : t subseteq s)
  proof: SemicontinuousOn.mono h hst

中文:
定理 HasOpenLowerSectionsOn.mono
  条件: (h : HasOpenLowerSectionsOn f s) (hst : t subseteq s)
  证明: SemicontinuousOn.mono h hst

Depends on / 依赖: SemicontinuousOn, SemicontinuousOn.mono
-/
theorem HasOpenLowerSectionsOn.mono (h : HasOpenLowerSectionsOn f s) (hst : t subseteq s) :
    HasOpenLowerSectionsOn f t :=
  SemicontinuousOn.mono h hst

/--
theorem `hasOpenLowerSectionsOn_univ_iff` / 定理 `hasOpenLowerSectionsOn_univ_iff`

English:
theorem hasOpenLowerSectionsOn_univ_iff
  proof: semicontinuousOn_univ_iff

中文:
定理 hasOpenLowerSectionsOn_univ_iff
  证明: semicontinuousOn_univ_iff

Depends on / 依赖: semicontinuousOn_univ_iff
-/
theorem hasOpenLowerSectionsOn_univ_iff :
    HasOpenLowerSectionsOn f univ ↔ HasOpenLowerSections f :=
  semicontinuousOn_univ_iff

/--
theorem `hasOpenLowerSections_restrict_iff` / 定理 `hasOpenLowerSections_restrict_iff`

English:
theorem hasOpenLowerSections_restrict_iff
  proof: semicontinuous_restrict_iff (r := (fun x b => b in f x))

中文:
定理 hasOpenLowerSections_restrict_iff
  证明: semicontinuous_restrict_iff (r := (fun x b => b in f x))
-/
@[simp] theorem hasOpenLowerSections_restrict_iff :
    HasOpenLowerSections (s.domRestrict f) ↔ HasOpenLowerSectionsOn f s :=
  semicontinuous_restrict_iff (r := (fun x b => b in f x))

/--
theorem `HasOpenLowerSections.hasOpenLowerSectionsOn` / 定理 `HasOpenLowerSections.hasOpenLowerSectionsOn`

English:
theorem HasOpenLowerSections.hasOpenLowerSectionsOn
  given: (h : HasOpenLowerSections f) (s : Set α)
  proof: h.semicontinuousOn s

中文:
定理 HasOpenLowerSections.hasOpenLowerSectionsOn
  条件: (h : HasOpenLowerSections f) (s : 集合 α)
  证明: h.semicontinuousOn s

Depends on / 依赖: h.semicontinuousOn, semicontinuousOn
-/
theorem HasOpenLowerSections.hasOpenLowerSectionsOn (h : HasOpenLowerSections f) (s : Set α) :
    HasOpenLowerSectionsOn f s :=
  h.semicontinuousOn s


/--
theorem `HasOpenLowerSectionsOn.const` / 定理 `HasOpenLowerSectionsOn.const`

English:
theorem HasOpenLowerSectionsOn.const
  statement: HasOpenLowerSectionsOn (fun _x => z) s
  proof: SemicontinuousOn.const

中文:
定理 HasOpenLowerSectionsOn.const
  结论: HasOpenLowerSectionsOn (fun _x => z) s
  证明: SemicontinuousOn.const

Depends on / 依赖: SemicontinuousOn, SemicontinuousOn.const
-/
theorem HasOpenLowerSectionsOn.const : HasOpenLowerSectionsOn (fun _x => z) s :=
  SemicontinuousOn.const

/--
theorem `HasOpenLowerSections.const` / 定理 `HasOpenLowerSections.const`

English:
theorem HasOpenLowerSections.const
  statement: HasOpenLowerSections fun _x : α => z
  proof: Semicontinuous.const

中文:
定理 HasOpenLowerSections.const
  结论: HasOpenLowerSections fun _x : α => z
  证明: Semicontinuous.const

Depends on / 依赖: Semicontinuous, Semicontinuous.const
-/
theorem HasOpenLowerSections.const : HasOpenLowerSections fun _x : α => z :=
  Semicontinuous.const


/--
theorem `HasOpenLowerSectionsOn.inter` / 定理 `HasOpenLowerSectionsOn.inter`

English:
theorem HasOpenLowerSectionsOn.inter
  statement: {f g : α -> Set β} {s : Set α} (hf : HasOpenLowerSectionsOn f s)
  proof: hf.inf hg

中文:
定理 HasOpenLowerSectionsOn.inter
  结论: {f g : α -> 集合 β} {s : 集合 α} (hf : HasOpenLowerSectionsOn f s)
  证明: hf.inf hg

Depends on / 依赖: hf.inf
-/
theorem HasOpenLowerSectionsOn.inter {f g : α -> Set β} {s : Set α} (hf : HasOpenLowerSectionsOn f s)
  (hg : HasOpenLowerSectionsOn g s) : HasOpenLowerSectionsOn (fun x => f x inter g x) s := hf.inf hg

/--
theorem `HasOpenLowerSectionsOn.union` / 定理 `HasOpenLowerSectionsOn.union`

English:
theorem HasOpenLowerSectionsOn.union
  statement: {f g : α -> Set β} {s : Set α} (hf : HasOpenLowerSectionsOn f s)
  proof: hf.sup hg

中文:
定理 HasOpenLowerSectionsOn.union
  结论: {f g : α -> 集合 β} {s : 集合 α} (hf : HasOpenLowerSectionsOn f s)
  证明: hf.sup hg

Depends on / 依赖: hf.sup
-/
theorem HasOpenLowerSectionsOn.union {f g : α -> Set β} {s : Set α} (hf : HasOpenLowerSectionsOn f s)
  (hg : HasOpenLowerSectionsOn g s) : HasOpenLowerSectionsOn (fun x => f x union g x) s := hf.sup hg

/--
theorem `HasOpenLowerSections.inter` / 定理 `HasOpenLowerSections.inter`

English:
theorem HasOpenLowerSections.inter
  statement: {f g : α -> Set β} (hf : HasOpenLowerSections f)
  proof: hf.inf hg

中文:
定理 HasOpenLowerSections.inter
  结论: {f g : α -> 集合 β} (hf : HasOpenLowerSections f)
  证明: hf.inf hg

Depends on / 依赖: hf.inf
-/
theorem HasOpenLowerSections.inter {f g : α -> Set β} (hf : HasOpenLowerSections f)
  (hg : HasOpenLowerSections g) : HasOpenLowerSections (fun x => f x inter g x) := hf.inf hg

/--
theorem `HasOpenLowerSections.union` / 定理 `HasOpenLowerSections.union`

English:
theorem HasOpenLowerSections.union
  statement: {f g : α -> Set β} (hf : HasOpenLowerSections f)
  proof: hf.sup hg

中文:
定理 HasOpenLowerSections.union
  结论: {f g : α -> 集合 β} (hf : HasOpenLowerSections f)
  证明: hf.sup hg

Depends on / 依赖: hf.sup
-/
theorem HasOpenLowerSections.union {f g : α -> Set β} (hf : HasOpenLowerSections f)
  (hg : HasOpenLowerSections g) : HasOpenLowerSections (fun x => f x union g x) := hf.sup hg

/-! ### Composition -/

section

variable {γ : Type*} [TopologicalSpace γ] {g : γ -> α} {c : γ} {t : Set γ}

/--
theorem `HasOpenLowerSectionsOn.comp` / 定理 `HasOpenLowerSectionsOn.comp`

English:
theorem HasOpenLowerSectionsOn.comp
  proof: SemicontinuousOn.comp (r := (fun x b => b in f x)) hf hg hg'

中文:
定理 HasOpenLowerSectionsOn.comp
  证明: SemicontinuousOn.comp (r := (fun x b => b in f x)) hf hg hg'

Depends on / 依赖: SemicontinuousOn, SemicontinuousOn.comp
-/
theorem HasOpenLowerSectionsOn.comp
    (hf : HasOpenLowerSectionsOn f s) (hg : ContinuousOn g t) (hg' : MapsTo g t s) :
    HasOpenLowerSectionsOn (f ∘ g) t :=
  SemicontinuousOn.comp (r := (fun x b => b in f x)) hf hg hg'

/--
theorem `HasOpenLowerSections.comp` / 定理 `HasOpenLowerSections.comp`

English:
theorem HasOpenLowerSections.comp
  proof: Semicontinuous.comp (r := (fun x b => b in f x)) hf hg

中文:
定理 HasOpenLowerSections.comp
  证明: Semicontinuous.comp (r := (fun x b => b in f x)) hf hg

Depends on / 依赖: Semicontinuous, Semicontinuous.comp
-/
theorem HasOpenLowerSections.comp
    (hf : HasOpenLowerSections f) (hg : Continuous g) : HasOpenLowerSections (f ∘ g) :=
  Semicontinuous.comp (r := (fun x b => b in f x)) hf hg

end

end Sections

section Graph

/-! ## Correspondence Graphs (CGraph)

We define the graph of a correspondence `f : α → Set β` to be the set of all pairs
`(x, y) : α × β` such that `y ∈ f x`. We use the term `CGraph` to refer to this construct.
-/

variable [TopologicalSpace β]

/--
Definition of `HasOpenCGraph` / `HasOpenCGraph` 的定义

English:
abbreviation HasOpenCGraph
  signature: (f : α -> Set β)
  body: IsOpen {x : α × β | x.2 in f x.1}

中文:
缩写 HasOpenCGraph
  签名: (f : α -> 集合 β)
  定义体: IsOpen {x : α × β | x.2 in f x.1}

Depends on / 依赖: IsOpen
-/
abbrev HasOpenCGraph (f : α -> Set β) := IsOpen {x : α × β | x.2 in f x.1}

/--
theorem `HasOpenCGraph.const` / 定理 `HasOpenCGraph.const`

English:
theorem HasOpenCGraph.const
  given: {z : Set β} (hz : IsOpen z)
  statement: HasOpenCGraph (fun _x : α => z)
  proof: hz.preimage continuous_snd

中文:
定理 HasOpenCGraph.const
  条件: {z : 集合 β} (hz : 是开集 z)
  结论: HasOpenCGraph (fun _x : α => z)
  证明: hz.preimage continuous_snd

Depends on / 依赖: continuous_snd, hz.preimage, preimage
-/
theorem HasOpenCGraph.const {z : Set β} (hz : IsOpen z) : HasOpenCGraph (fun _x : α => z) :=
  hz.preimage continuous_snd

/--
theorem `HasOpenCGraph.inter` / 定理 `HasOpenCGraph.inter`

English:
theorem HasOpenCGraph.inter
  statement: {f g : α -> Set β} (hf : HasOpenCGraph f)
  proof: by
  have : {x : α × β | x.2 in f x.1 inter g x.1} =
      {x | x.2 in f x.1} inter {x | x.2 in g x.1} := by ext; simp
  rw [HasOpenCGraph]; rw [this]
  exact IsOpen.inter hf hg

中文:
定理 HasOpenCGraph.inter
  结论: {f g : α -> 集合 β} (hf : HasOpenCGraph f)
  证明: by
  have : {x : α × β | x.2 in f x.1 inter g x.1} =
      {x | x.2 in f x.1} inter {x | x.2 in g x.1} := by ext; simp
  rw [HasOpenCGraph]; rw [this]
  exact IsOpen.inter hf hg

Depends on / 依赖: HasOpenCGraph, IsOpen, IsOpen.inter
-/
theorem HasOpenCGraph.inter {f g : α -> Set β} (hf : HasOpenCGraph f)
    (hg : HasOpenCGraph g) : HasOpenCGraph (fun x => f x inter g x) := by
  have : {x : α × β | x.2 in f x.1 inter g x.1} =
      {x | x.2 in f x.1} inter {x | x.2 in g x.1} := by ext; simp
  rw [HasOpenCGraph]; rw [this]
  exact IsOpen.inter hf hg

section

variable {γ : Type*} [TopologicalSpace γ] {g' : γ -> α} {c : γ × β}
    {u : Set (γ × β)} {v : Set (α × β)}

/--
theorem `HasOpenCGraph.comp` / 定理 `HasOpenCGraph.comp`

English:
theorem HasOpenCGraph.comp
  given: {f : α -> Set β} (hf : HasOpenCGraph f) (hg : Continuous g')
  proof: hf.preimage (hg.prodMap continuous_id)

中文:
定理 HasOpenCGraph.comp
  条件: {f : α -> 集合 β} (hf : HasOpenCGraph f) (hg : 连续 g')
  证明: hf.preimage (hg.prodMap continuous_id)

Depends on / 依赖: continuous_id, hf.preimage, hg.prodMap, preimage, prodMap
-/
theorem HasOpenCGraph.comp {f : α -> Set β} (hf : HasOpenCGraph f) (hg : Continuous g') :
    HasOpenCGraph (f ∘ g') :=
  hf.preimage (hg.prodMap continuous_id)

end


/--
theorem `HasOpenLowerSections.lowerHemicontinuous` / 定理 `HasOpenLowerSections.lowerHemicontinuous`

English:
theorem HasOpenLowerSections.lowerHemicontinuous
  given: {f : α -> Set β} (hf : HasOpenLowerSections f)
  proof: fun x _ ⟨hopen, y, hyfx, hyt⟩ =>
      (hf x y hyfx).mono fun _ hy' => ⟨hopen, y, hy', hyt⟩

中文:
定理 HasOpenLowerSections.lowerHemicontinuous
  条件: {f : α -> 集合 β} (hf : HasOpenLowerSections f)
  证明: fun x _ ⟨hopen, y, hyfx, hyt⟩ =>
      (hf x y hyfx).mono fun _ hy' => ⟨hopen, y, hy', hyt⟩
-/
theorem HasOpenLowerSections.lowerHemicontinuous {f : α -> Set β} (hf : HasOpenLowerSections f) :
    LowerHemicontinuous f := fun x _ ⟨hopen, y, hyfx, hyt⟩ =>
      (hf x y hyfx).mono fun _ hy' => ⟨hopen, y, hy', hyt⟩

/--
theorem `HasOpenCGraph.hasOpenLowerSections` / 定理 `HasOpenCGraph.hasOpenLowerSections`

English:
theorem HasOpenCGraph.hasOpenLowerSections
  proof: by
  intro x b hb
  have hopen : IsOpen {x' : α | b in f x'} := by
    simpa using h.preimage (continuous_id.prodMk continuous_const)
  simpa [Filter.Eventually] using hopen.mem_nhds hb

中文:
定理 HasOpenCGraph.hasOpenLowerSections
  证明: by
  intro x b hb
  have hopen : IsOpen {x' : α | b in f x'} := by
    simpa using h.preimage (continuous_id.prodMk continuous_const)
  simpa [Filter.Eventually] using hopen.mem_nhds hb

Depends on / 依赖: Eventually, Filter, Filter.Eventually, IsOpen, continuous_const, continuous_id, continuous_id.prodMk, h.preimage, hopen.mem_nhds, mem_nhds, preimage, prodMk
-/
theorem HasOpenCGraph.hasOpenLowerSections
    {f : α -> Set β} (h : HasOpenCGraph f) :
    HasOpenLowerSections f := by
  intro x b hb
  have hopen : IsOpen {x' : α | b in f x'} := by
    simpa using h.preimage (continuous_id.prodMk continuous_const)
  simpa [Filter.Eventually] using hopen.mem_nhds hb

end Graph
