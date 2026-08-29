/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Asymptotics.Theta

/-!
# Asymptotic equivalence

In this file, we prove properties of the relation `IsEquivalent l u v`,
which means that `u-v` is little o of `v` along the filter `l`.

Unlike `Is(Little|Big)O` relations, this one requires `u` and `v` to have the same codomain `β`.

## Notation

We use the notation `u ~[l] v := IsEquivalent l u v`, which you can use by opening the
`Asymptotics` locale.

## Main results

If `β` is a `NormedAddCommGroup` :

- `_ ~[l] _` is an equivalence relation
- Equivalent statements for `u ~[l] const _ c` :
  - If `c ≠ 0`, this is true iff `Tendsto u l (𝓝 c)` (see `isEquivalent_const_iff_tendsto`)
  - For `c = 0`, this is true iff `u =ᶠ[l] 0` (see `isEquivalent_zero_iff_eventually_zero`)

If `β` is a `NormedField` :

- Alternative characterization of the relation (see `isEquivalent_iff_exists_eq_mul`) :

  `u ~[l] v ↔ ∃ (φ : α → β) (hφ : Tendsto φ l (𝓝 1)), u =ᶠ[l] φ * v`

- Provided some non-vanishing hypothesis, this can be seen as `u ~[l] v ↔ Tendsto (u/v) l (𝓝 1)`
  (see `isEquivalent_iff_tendsto_one`)
- For any constant `c`, `u ~[l] v` implies `Tendsto u l (𝓝 c) ↔ Tendsto v l (𝓝 c)`
  (see `IsEquivalent.tendsto_nhds_iff`)
- `*` and `/` are compatible with `_ ~[l] _` (see `IsEquivalent.mul` and `IsEquivalent.div`)

If `β` is a `NormedLinearOrderedField` :

- If `u ~[l] v`, we have `Tendsto u l atTop ↔ Tendsto v l atTop`
  (see `IsEquivalent.tendsto_atTop_iff`)

## Implementation Notes

Note that `IsEquivalent` takes the parameters `(l : Filter α) (u v : α → β)` in that order.
This is to enable `calc` support, as `calc` requires that the last two explicit arguments are `u v`.

-/

public section


namespace Asymptotics

open Filter Function

open Topology

section NormedAddCommGroup

variable {α β : Type*} [NormedAddCommGroup β]

variable {u v w : α -> β} {l : Filter α}

/--
theorem `IsEquivalent.isLittleO` / 定理 `IsEquivalent.isLittleO`

English:
theorem IsEquivalent.isLittleO
  given: (h : u ~[l] v)
  statement: (u - v) =o[l] v
  proof: h

nonrec theorem IsEquivalent.isBigO (h : u ~[l] v) : u =O[l] v :=
  (IsBigO.congr_of_sub h.isBigO.symm).mp (isBigO_refl _ _)

中文:
定理 IsEquivalent.isLittleO
  条件: (h : u ~[l] v)
  结论: (u - v) =o[l] v
  证明: h

nonrec theorem IsEquivalent.isBigO (h : u ~[l] v) : u =O[l] v :=
  (IsBigO.congr_of_sub h.isBigO.symm).mp (isBigO_refl _ _)
-/
theorem IsEquivalent.isLittleO (h : u ~[l] v) : (u - v) =o[l] v := h

nonrec theorem IsEquivalent.isBigO (h : u ~[l] v) : u =O[l] v :=
  (IsBigO.congr_of_sub h.isBigO.symm).mp (isBigO_refl _ _)

/--
theorem `IsEquivalent.isBigO_symm` / 定理 `IsEquivalent.isBigO_symm`

English:
theorem IsEquivalent.isBigO_symm
  given: (h : u ~[l] v)
  statement: v =O[l] u
  proof: by
  convert! h.isLittleO.right_isBigO_add
  simp

中文:
定理 IsEquivalent.isBigO_symm
  条件: (h : u ~[l] v)
  结论: v =O[l] u
  证明: by
  convert! h.isLittleO.right_isBigO_add
  simp

Depends on / 依赖: convert, h.isLittleO.right_isBigO_add, isLittleO, right_isBigO_add
-/
theorem IsEquivalent.isBigO_symm (h : u ~[l] v) : v =O[l] u := by
  convert! h.isLittleO.right_isBigO_add
  simp

/--
theorem `IsEquivalent.isTheta` / 定理 `IsEquivalent.isTheta`

English:
theorem IsEquivalent.isTheta
  given: (h : u ~[l] v)
  statement: u =Θ[l] v
  proof: ⟨h.isBigO, h.isBigO_symm⟩

中文:
定理 IsEquivalent.isTheta
  条件: (h : u ~[l] v)
  结论: u =Θ[l] v
  证明: ⟨h.isBigO, h.isBigO_symm⟩

Depends on / 依赖: h.isBigO, h.isBigO_symm, isBigO, isBigO_symm
-/
theorem IsEquivalent.isTheta (h : u ~[l] v) : u =Θ[l] v :=
  ⟨h.isBigO, h.isBigO_symm⟩

/--
theorem `IsEquivalent.isTheta_symm` / 定理 `IsEquivalent.isTheta_symm`

English:
theorem IsEquivalent.isTheta_symm
  given: (h : u ~[l] v)
  statement: v =Θ[l] u
  proof: ⟨h.isBigO_symm, h.isBigO⟩

@[refl]

中文:
定理 IsEquivalent.isTheta_symm
  条件: (h : u ~[l] v)
  结论: v =Θ[l] u
  证明: ⟨h.isBigO_symm, h.isBigO⟩

@[refl]

Depends on / 依赖: h.isBigO, h.isBigO_symm, isBigO, isBigO_symm
-/
theorem IsEquivalent.isTheta_symm (h : u ~[l] v) : v =Θ[l] u :=
  ⟨h.isBigO_symm, h.isBigO⟩

@[refl]
/--
theorem `IsEquivalent.refl` / 定理 `IsEquivalent.refl`

English:
theorem IsEquivalent.refl
  statement: u ~[l] u
  proof: by
  rw [IsEquivalent]; rw [sub_self]
  exact isLittleO_zero _ _

@[symm]

中文:
定理 IsEquivalent.refl
  结论: u ~[l] u
  证明: by
  rw [IsEquivalent]; rw [sub_self]
  exact isLittleO_zero _ _

@[symm]

Depends on / 依赖: IsEquivalent, isLittleO_zero, sub_self
-/
theorem IsEquivalent.refl : u ~[l] u := by
  rw [IsEquivalent]; rw [sub_self]
  exact isLittleO_zero _ _

@[symm]
/--
theorem `IsEquivalent.symm` / 定理 `IsEquivalent.symm`

English:
theorem IsEquivalent.symm
  given: (h : u ~[l] v)
  statement: v ~[l] u
  proof: (h.isLittleO.trans_isBigO h.isBigO_symm).symm

@[trans]

中文:
定理 IsEquivalent.symm
  条件: (h : u ~[l] v)
  结论: v ~[l] u
  证明: (h.isLittleO.trans_isBigO h.isBigO_symm).symm

@[trans]

Depends on / 依赖: h.isBigO_symm, h.isLittleO.trans_isBigO, isBigO_symm, isLittleO, trans_isBigO
-/
theorem IsEquivalent.symm (h : u ~[l] v) : v ~[l] u :=
  (h.isLittleO.trans_isBigO h.isBigO_symm).symm

@[trans]
/--
theorem `IsEquivalent.trans` / 定理 `IsEquivalent.trans`

English:
theorem IsEquivalent.trans
  given: {l : Filter α} {u v w : α -> β} (huv : u ~[l] v) (hvw : v ~[l] w)
  proof: (huv.isLittleO.trans_isBigO hvw.isBigO).triangle hvw.isLittleO

中文:
定理 IsEquivalent.trans
  条件: {l : 滤子 α} {u v w : α -> β} (huv : u ~[l] v) (hvw : v ~[l] w)
  证明: (huv.isLittleO.trans_isBigO hvw.isBigO).triangle hvw.isLittleO

Depends on / 依赖: huv.isLittleO.trans_isBigO, hvw.isBigO, hvw.isLittleO, isBigO, isLittleO, trans_isBigO, triangle
-/
theorem IsEquivalent.trans {l : Filter α} {u v w : α -> β} (huv : u ~[l] v) (hvw : v ~[l] w) :
    u ~[l] w :=
  (huv.isLittleO.trans_isBigO hvw.isBigO).triangle hvw.isLittleO

/--
theorem `IsEquivalent.congr_left` / 定理 `IsEquivalent.congr_left`

English:
theorem IsEquivalent.congr_left
  given: {u v w : α -> β} {l : Filter α} (huv : u ~[l] v) (huw : u =ᶠ[l] w)
  proof: huv.congr' (huw.sub (EventuallyEq.refl _ _)) (EventuallyEq.refl _ _)

中文:
定理 IsEquivalent.congr_left
  条件: {u v w : α -> β} {l : 滤子 α} (huv : u ~[l] v) (huw : u =ᶠ[l] w)
  证明: huv.congr' (huw.sub (EventuallyEq.refl _ _)) (EventuallyEq.refl _ _)

Depends on / 依赖: EventuallyEq, EventuallyEq.refl, huv.congr, huw.sub
-/
theorem IsEquivalent.congr_left {u v w : α -> β} {l : Filter α} (huv : u ~[l] v) (huw : u =ᶠ[l] w) :
    w ~[l] v :=
  huv.congr' (huw.sub (EventuallyEq.refl _ _)) (EventuallyEq.refl _ _)

/--
theorem `IsEquivalent.congr_right` / 定理 `IsEquivalent.congr_right`

English:
theorem IsEquivalent.congr_right
  given: {u v w : α -> β} {l : Filter α} (huv : u ~[l] v) (hvw : v =ᶠ[l] w)
  proof: (huv.symm.congr_left hvw).symm

中文:
定理 IsEquivalent.congr_right
  条件: {u v w : α -> β} {l : 滤子 α} (huv : u ~[l] v) (hvw : v =ᶠ[l] w)
  证明: (huv.symm.congr_left hvw).symm

Depends on / 依赖: congr_left, huv.symm.congr_left
-/
theorem IsEquivalent.congr_right {u v w : α -> β} {l : Filter α} (huv : u ~[l] v) (hvw : v =ᶠ[l] w) :
    u ~[l] w :=
  (huv.symm.congr_left hvw).symm

/--
theorem `isEquivalent_zero_iff_eventually_zero` / 定理 `isEquivalent_zero_iff_eventually_zero`

English:
theorem isEquivalent_zero_iff_eventually_zero
  statement: u ~[l] 0 ↔ u =ᶠ[l] 0
  proof: by
  rw [IsEquivalent]; rw [sub_zero]
  exact isLittleO_zero_right_iff

中文:
定理 isEquivalent_zero_iff_eventually_zero
  结论: u ~[l] 0 ↔ u =ᶠ[l] 0
  证明: by
  rw [IsEquivalent]; rw [sub_zero]
  exact isLittleO_zero_right_iff

Depends on / 依赖: IsEquivalent, isLittleO_zero_right_iff, sub_zero
-/
theorem isEquivalent_zero_iff_eventually_zero : u ~[l] 0 ↔ u =ᶠ[l] 0 := by
  rw [IsEquivalent]; rw [sub_zero]
  exact isLittleO_zero_right_iff

/--
theorem `isEquivalent_zero_iff_isBigO_zero` / 定理 `isEquivalent_zero_iff_isBigO_zero`

English:
theorem isEquivalent_zero_iff_isBigO_zero
  statement: u ~[l] 0 ↔ u =O[l] (0 : α -> β)
  proof: by
  refine ⟨IsEquivalent.isBigO, fun h => ?_⟩
  rw [isEquivalent_zero_iff_eventually_zero]; rw [eventuallyEq_iff_exists_mem]
  exact ⟨{ x : α | u x = 0 }, isBigO_zero_right_iff.mp h, fun x hx => hx⟩

中文:
定理 isEquivalent_zero_iff_isBigO_zero
  结论: u ~[l] 0 ↔ u =O[l] (0 : α -> β)
  证明: by
  refine ⟨IsEquivalent.isBigO, fun h => ?_⟩
  rw [isEquivalent_zero_iff_eventually_zero]; rw [eventuallyEq_iff_exists_mem]
  exact ⟨{ x : α | u x = 0 }, isBigO_zero_right_iff.mp h, fun x hx => hx⟩

Depends on / 依赖: IsEquivalent, IsEquivalent.isBigO, eventuallyEq_iff_exists_mem, isBigO, isBigO_zero_right_iff, isBigO_zero_right_iff.mp, isEquivalent_zero_iff_eventually_zero
-/
theorem isEquivalent_zero_iff_isBigO_zero : u ~[l] 0 ↔ u =O[l] (0 : α -> β) := by
  refine ⟨IsEquivalent.isBigO, fun h => ?_⟩
  rw [isEquivalent_zero_iff_eventually_zero]; rw [eventuallyEq_iff_exists_mem]
  exact ⟨{ x : α | u x = 0 }, isBigO_zero_right_iff.mp h, fun x hx => hx⟩

/--
theorem `isEquivalent_const_iff_tendsto` / 定理 `isEquivalent_const_iff_tendsto`

English:
theorem isEquivalent_const_iff_tendsto
  given: {c : β} (h : c != 0)
  proof: by
  simp +unfoldPartialApp only [IsEquivalent, const, isLittleO_const_iff h]
  constructor <;> intro h
  · have := h.sub (tendsto_const_nhds (x := -c))
    simp only [Pi.sub_apply, sub_neg_eq_add, sub_add_cancel, zero_add] at this
    exact this
  · have := h.sub (tendsto_const_nhds (x := c))
    r

中文:
定理 isEquivalent_const_iff_tendsto
  条件: {c : β} (h : c != 0)
  证明: by
  simp +unfoldPartialApp only [IsEquivalent, const, isLittleO_const_iff h]
  constructor <;> intro h
  · have := h.sub (tendsto_const_nhds (x := -c))
    simp only [Pi.sub_apply, sub_neg_eq_add, sub_add_cancel, zero_add] at this
    exact this
  · have := h.sub (tendsto_const_nhds (x := c))
    r

Depends on / 依赖: IsEquivalent, Pi.sub_apply, h.sub, isLittleO_const_iff, sub_add_cancel, sub_apply, sub_neg_eq_add, sub_self, tendsto_const_nhds, unfoldPartialApp, zero_add
-/
theorem isEquivalent_const_iff_tendsto {c : β} (h : c != 0) :
    u ~[l] const _ c ↔ Tendsto u l (𝓝 c) := by
  simp +unfoldPartialApp only [IsEquivalent, const, isLittleO_const_iff h]
  constructor <;> intro h
  · have := h.sub (tendsto_const_nhds (x := -c))
    simp only [Pi.sub_apply, sub_neg_eq_add, sub_add_cancel, zero_add] at this
    exact this
  · have := h.sub (tendsto_const_nhds (x := c))
    rwa [sub_self] at this

/--
theorem `IsEquivalent.tendsto_const` / 定理 `IsEquivalent.tendsto_const`

English:
theorem IsEquivalent.tendsto_const
  given: {c : β} (hu : u ~[l] const _ c)
  statement: Tendsto u l (𝓝 c)
  proof: by
rcases em c = 0 with rfl | h
  · exact (tendsto_congr' <| isEquivalent_zero_iff_eventually_zero.mp hu).mpr tendsto_const_nhds
  · exact (isEquivalent_const_iff_tendsto h).mp hu

中文:
定理 IsEquivalent.tendsto_const
  条件: {c : β} (hu : u ~[l] const _ c)
  结论: 收敛 u l (𝓝 c)
  证明: by
rcases em c = 0 with rfl | h
  · exact (tendsto_congr' <| isEquivalent_zero_iff_eventually_zero.mp hu).mpr tendsto_const_nhds
  · exact (isEquivalent_const_iff_tendsto h).mp hu

Depends on / 依赖: isEquivalent_const_iff_tendsto, isEquivalent_zero_iff_eventually_zero, isEquivalent_zero_iff_eventually_zero.mp, tendsto_congr, tendsto_const_nhds
-/
theorem IsEquivalent.tendsto_const {c : β} (hu : u ~[l] const _ c) : Tendsto u l (𝓝 c) := by
rcases em c = 0 with rfl | h
  · exact (tendsto_congr' <| isEquivalent_zero_iff_eventually_zero.mp hu).mpr tendsto_const_nhds
  · exact (isEquivalent_const_iff_tendsto h).mp hu

/--
theorem `IsEquivalent.tendsto_nhds` / 定理 `IsEquivalent.tendsto_nhds`

English:
theorem IsEquivalent.tendsto_nhds
  given: {c : β} (huv : u ~[l] v) (hu : Tendsto u l (𝓝 c))
  proof: by
  by_cases h : c = 0
  · subst c
    rw [← isLittleO_one_iff Real] at hu ⊢
    simpa using (huv.symm.isLittleO.trans hu).add hu
  · rw [← isEquivalent_const_iff_tendsto h] at hu ⊢
    exact huv.symm.trans hu

中文:
定理 IsEquivalent.tendsto_nhds
  条件: {c : β} (huv : u ~[l] v) (hu : 收敛 u l (𝓝 c))
  证明: by
  by_cases h : c = 0
  · subst c
    rw [← isLittleO_one_iff Real] at hu ⊢
    simpa using (huv.symm.isLittleO.trans hu).add hu
  · rw [← isEquivalent_const_iff_tendsto h] at hu ⊢
    exact huv.symm.trans hu

Depends on / 依赖: huv.symm.isLittleO.trans, huv.symm.trans, isEquivalent_const_iff_tendsto, isLittleO, isLittleO_one_iff
-/
theorem IsEquivalent.tendsto_nhds {c : β} (huv : u ~[l] v) (hu : Tendsto u l (𝓝 c)) :
    Tendsto v l (𝓝 c) := by
  by_cases h : c = 0
  · subst c
    rw [← isLittleO_one_iff Real] at hu ⊢
    simpa using (huv.symm.isLittleO.trans hu).add hu
  · rw [← isEquivalent_const_iff_tendsto h] at hu ⊢
    exact huv.symm.trans hu

/--
theorem `IsEquivalent.tendsto_nhds_iff` / 定理 `IsEquivalent.tendsto_nhds_iff`

English:
theorem IsEquivalent.tendsto_nhds_iff
  given: {c : β} (huv : u ~[l] v)
  proof: ⟨huv.tendsto_nhds, huv.symm.tendsto_nhds⟩

中文:
定理 IsEquivalent.tendsto_nhds_iff
  条件: {c : β} (huv : u ~[l] v)
  证明: ⟨huv.tendsto_nhds, huv.symm.tendsto_nhds⟩

Depends on / 依赖: huv.symm.tendsto_nhds, huv.tendsto_nhds, tendsto_nhds
-/
theorem IsEquivalent.tendsto_nhds_iff {c : β} (huv : u ~[l] v) :
    Tendsto u l (𝓝 c) ↔ Tendsto v l (𝓝 c) :=
  ⟨huv.tendsto_nhds, huv.symm.tendsto_nhds⟩

/--
theorem `IsEquivalent.add_isLittleO` / 定理 `IsEquivalent.add_isLittleO`

English:
theorem IsEquivalent.add_isLittleO
  given: (huv : u ~[l] v) (hwv : w =o[l] v)
  statement: u + w ~[l] v
  proof: by
  simpa only [IsEquivalent, add_sub_right_comm] using! huv.add hwv

中文:
定理 IsEquivalent.add_isLittleO
  条件: (huv : u ~[l] v) (hwv : w =o[l] v)
  结论: u + w ~[l] v
  证明: by
  simpa only [IsEquivalent, add_sub_right_comm] using! huv.add hwv

Depends on / 依赖: IsEquivalent, add_sub_right_comm, huv.add
-/
theorem IsEquivalent.add_isLittleO (huv : u ~[l] v) (hwv : w =o[l] v) : u + w ~[l] v := by
  simpa only [IsEquivalent, add_sub_right_comm] using! huv.add hwv

/--
theorem `IsEquivalent.sub_isLittleO` / 定理 `IsEquivalent.sub_isLittleO`

English:
theorem IsEquivalent.sub_isLittleO
  given: (huv : u ~[l] v) (hwv : w =o[l] v)
  statement: u - w ~[l] v
  proof: by
  simpa only [sub_eq_add_neg] using! huv.add_isLittleO hwv.neg_left

中文:
定理 IsEquivalent.sub_isLittleO
  条件: (huv : u ~[l] v) (hwv : w =o[l] v)
  结论: u - w ~[l] v
  证明: by
  simpa only [sub_eq_add_neg] using! huv.add_isLittleO hwv.neg_left

Depends on / 依赖: add_isLittleO, huv.add_isLittleO, hwv.neg_left, neg_left, sub_eq_add_neg
-/
theorem IsEquivalent.sub_isLittleO (huv : u ~[l] v) (hwv : w =o[l] v) : u - w ~[l] v := by
  simpa only [sub_eq_add_neg] using! huv.add_isLittleO hwv.neg_left

/--
theorem `IsLittleO.add_isEquivalent` / 定理 `IsLittleO.add_isEquivalent`

English:
theorem IsLittleO.add_isEquivalent
  given: (hu : u =o[l] w) (hv : v ~[l] w)
  statement: u + v ~[l] w
  proof: add_comm v u ▸ hv.add_isLittleO hu

中文:
定理 IsLittleO.add_isEquivalent
  条件: (hu : u =o[l] w) (hv : v ~[l] w)
  结论: u + v ~[l] w
  证明: add_comm v u ▸ hv.add_isLittleO hu

Depends on / 依赖: add_comm, add_isLittleO, hv.add_isLittleO
-/
theorem IsLittleO.add_isEquivalent (hu : u =o[l] w) (hv : v ~[l] w) : u + v ~[l] w :=
  add_comm v u ▸ hv.add_isLittleO hu

/--
theorem `IsEquivalent.add_const_of_norm_tendsto_atTop` / 定理 `IsEquivalent.add_const_of_norm_tendsto_atTop`

English:
theorem IsEquivalent.add_const_of_norm_tendsto_atTop
  statement: {c : β}
  proof: huv.add_isLittleO isLittleO_const_left.mpr (Or.inr hv)

中文:
定理 IsEquivalent.add_const_of_norm_tendsto_atTop
  结论: {c : β}
  证明: huv.add_isLittleO isLittleO_const_left.mpr (Or.inr hv)

Depends on / 依赖: Or.inr, add_isLittleO, huv.add_isLittleO, isLittleO_const_left, isLittleO_const_left.mpr
-/
theorem IsEquivalent.add_const_of_norm_tendsto_atTop {c : β}
    (huv : u ~[l] v) (hv : Tendsto (norm ∘ v) l atTop) :
    (u · + c) ~[l] v :=
huv.add_isLittleO isLittleO_const_left.mpr (Or.inr hv)

/--
theorem `IsEquivalent.const_add_of_norm_tendsto_atTop` / 定理 `IsEquivalent.const_add_of_norm_tendsto_atTop`

English:
theorem IsEquivalent.const_add_of_norm_tendsto_atTop
  statement: {c : β}
  proof: (isLittleO_const_left.mpr (Or.inr hv)).add_isEquivalent huv

中文:
定理 IsEquivalent.const_add_of_norm_tendsto_atTop
  结论: {c : β}
  证明: (isLittleO_const_left.mpr (Or.inr hv)).add_isEquivalent huv

Depends on / 依赖: Or.inr, add_isEquivalent, isLittleO_const_left, isLittleO_const_left.mpr
-/
theorem IsEquivalent.const_add_of_norm_tendsto_atTop {c : β}
    (huv : u ~[l] v) (hv : Tendsto (norm ∘ v) l atTop) :
    (c + u ·) ~[l] v :=
  (isLittleO_const_left.mpr (Or.inr hv)).add_isEquivalent huv

/--
theorem `IsLittleO.isEquivalent` / 定理 `IsLittleO.isEquivalent`

English:
theorem IsLittleO.isEquivalent
  given: (huv : (u - v) =o[l] v)
  statement: u ~[l] v
  proof: huv

中文:
定理 IsLittleO.isEquivalent
  条件: (huv : (u - v) =o[l] v)
  结论: u ~[l] v
  证明: huv
-/
theorem IsLittleO.isEquivalent (huv : (u - v) =o[l] v) : u ~[l] v := huv

/--
theorem `IsEquivalent.neg` / 定理 `IsEquivalent.neg`

English:
theorem IsEquivalent.neg
  given: (huv : u ~[l] v)
  statement: (fun x => -u x) ~[l] fun x => -v x
  proof: by
  rw [IsEquivalent]
  convert! huv.isLittleO.neg_left.neg_right
  simp [neg_add_eq_sub]

中文:
定理 IsEquivalent.neg
  条件: (huv : u ~[l] v)
  结论: (fun x => -u x) ~[l] fun x => -v x
  证明: by
  rw [IsEquivalent]
  convert! huv.isLittleO.neg_left.neg_right
  simp [neg_add_eq_sub]

Depends on / 依赖: IsEquivalent, convert, huv.isLittleO.neg_left.neg_right, isLittleO, neg_add_eq_sub, neg_left, neg_right
-/
theorem IsEquivalent.neg (huv : u ~[l] v) : (fun x => -u x) ~[l] fun x => -v x := by
  rw [IsEquivalent]
  convert! huv.isLittleO.neg_left.neg_right
  simp [neg_add_eq_sub]

end NormedAddCommGroup

open Asymptotics

section NormedField

variable {α β : Type*} [NormedField β] {u v : α -> β} {l : Filter α}

/--
theorem `isEquivalent_iff_exists_eq_mul` / 定理 `isEquivalent_iff_exists_eq_mul`

English:
theorem isEquivalent_iff_exists_eq_mul
  proof: by
  rw [IsEquivalent]; rw [isLittleO_iff_exists_eq_mul]
  constructor <;> rintro ⟨φ, hφ, h⟩ <;> [refine ⟨φ + 1, ?_, ?_⟩; refine ⟨φ - 1, ?_, ?_⟩]
  · conv in 𝓝 _ => rw [← zero_add (1 : β)]
    exact hφ.add tendsto_const_nhds
  · convert! h.fun_add (EventuallyEq.refl l v) <;> simp [add_mul]
  · conv 

中文:
定理 isEquivalent_iff_存在_eq_mul
  证明: by
  rw [IsEquivalent]; rw [isLittleO_iff_exists_eq_mul]
  constructor <;> rintro ⟨φ, hφ, h⟩ <;> [refine ⟨φ + 1, ?_, ?_⟩; refine ⟨φ - 1, ?_, ?_⟩]
  · conv in 𝓝 _ => rw [← zero_add (1 : β)]
    exact hφ.add tendsto_const_nhds
  · convert! h.fun_add (EventuallyEq.refl l v) <;> simp [add_mul]
  · conv 

Depends on / 依赖: EventuallyEq, EventuallyEq.refl, IsEquivalent, add_mul, convert, fun_add, fun_sub, h.fun_add, h.fun_sub, isLittleO_iff_exists_eq_mul, sub_mul, sub_self, tendsto_const_nhds, zero_add
-/
theorem isEquivalent_iff_exists_eq_mul :
    u ~[l] v ↔ exists (φ : α -> β) (_ : Tendsto φ l (𝓝 1)), u =ᶠ[l] φ * v := by
  rw [IsEquivalent]; rw [isLittleO_iff_exists_eq_mul]
  constructor <;> rintro ⟨φ, hφ, h⟩ <;> [refine ⟨φ + 1, ?_, ?_⟩; refine ⟨φ - 1, ?_, ?_⟩]
  · conv in 𝓝 _ => rw [← zero_add (1 : β)]
    exact hφ.add tendsto_const_nhds
  · convert! h.fun_add (EventuallyEq.refl l v) <;> simp [add_mul]
  · conv in 𝓝 _ => rw [← sub_self (1 : β)]
    exact hφ.sub tendsto_const_nhds
  · convert! h.fun_sub (EventuallyEq.refl l v); simp [sub_mul]

/--
theorem `IsEquivalent.exists_eq_mul` / 定理 `IsEquivalent.exists_eq_mul`

English:
theorem IsEquivalent.exists_eq_mul
  given: (huv : u ~[l] v)
  proof: isEquivalent_iff_exists_eq_mul.mp huv

中文:
定理 IsEquivalent.存在_eq_mul
  条件: (huv : u ~[l] v)
  证明: isEquivalent_iff_exists_eq_mul.mp huv

Depends on / 依赖: isEquivalent_iff_exists_eq_mul, isEquivalent_iff_exists_eq_mul.mp
-/
theorem IsEquivalent.exists_eq_mul (huv : u ~[l] v) :
    exists (φ : α -> β) (_ : Tendsto φ l (𝓝 1)), u =ᶠ[l] φ * v :=
  isEquivalent_iff_exists_eq_mul.mp huv

/--
theorem `isEquivalent_of_tendsto_one` / 定理 `isEquivalent_of_tendsto_one`

English:
theorem isEquivalent_of_tendsto_one
  given: (huv : Tendsto (u / v) l (𝓝 1))
  proof: by
  suffices forallᶠ x in l, v x = 0 -> u x = 0 by
    rw [isEquivalent_iff_exists_eq_mul]
    exact ⟨u / v, huv, this.mono fun x hz' => (div_mul_cancel_of_imp hz').symm⟩
  by_contra! h
  replace h : existsᶠ t in l, (u / v) t = 0 := h.mono fun x ⟨hv, hu⟩ => by simp [hv]
  simpa using tendsto_nhds_u

中文:
定理 isEquivalent_of_tendsto_one
  条件: (huv : 收敛 (u / v) l (𝓝 1))
  证明: by
  suffices forallᶠ x in l, v x = 0 -> u x = 0 by
    rw [isEquivalent_iff_exists_eq_mul]
    exact ⟨u / v, huv, this.mono fun x hz' => (div_mul_cancel_of_imp hz').symm⟩
  by_contra! h
  replace h : existsᶠ t in l, (u / v) t = 0 := h.mono fun x ⟨hv, hu⟩ => by simp [hv]
  simpa using tendsto_nhds_u

Depends on / 依赖: div_mul_cancel_of_imp, h.mono, isEquivalent_iff_exists_eq_mul, replace, tendsto_const_nhds, tendsto_nhds_unique_of_frequently_eq, this.mono
-/
theorem isEquivalent_of_tendsto_one (huv : Tendsto (u / v) l (𝓝 1)) :
    u ~[l] v := by
  suffices forallᶠ x in l, v x = 0 -> u x = 0 by
    rw [isEquivalent_iff_exists_eq_mul]
    exact ⟨u / v, huv, this.mono fun x hz' => (div_mul_cancel_of_imp hz').symm⟩
  by_contra! h
  replace h : existsᶠ t in l, (u / v) t = 0 := h.mono fun x ⟨hv, hu⟩ => by simp [hv]
  simpa using tendsto_nhds_unique_of_frequently_eq (b := 0) huv tendsto_const_nhds h

@[deprecated (since := "2026-01-26")] alias isEquivalent_of_tendsto_one' :=
  isEquivalent_of_tendsto_one

/--
theorem `isEquivalent_iff_tendsto_one` / 定理 `isEquivalent_iff_tendsto_one`

English:
theorem isEquivalent_iff_tendsto_one
  given: (hz : forallᶠ x in l, v x != 0)
  proof: by
  constructor
  · intro hequiv
    have := hequiv.isLittleO.tendsto_div_nhds_zero
    simp only [Pi.sub_apply, sub_div] at this
    have key : Tendsto (fun x => v x / v x) l (𝓝 1) :=
      (tendsto_congr' <| hz.mono fun x hnz => @div_self _ _ (v x) hnz).mpr tendsto_const_nhds
    convert! this.ad

中文:
定理 isEquivalent_iff_tendsto_one
  条件: (hz : 对任意ᶠ x in l, v x != 0)
  证明: by
  constructor
  · intro hequiv
    have := hequiv.isLittleO.tendsto_div_nhds_zero
    simp only [Pi.sub_apply, sub_div] at this
    have key : Tendsto (fun x => v x / v x) l (𝓝 1) :=
      (tendsto_congr' <| hz.mono fun x hnz => @div_self _ _ (v x) hnz).mpr tendsto_const_nhds
    convert! this.ad

Depends on / 依赖: Pi.sub_apply, Tendsto, convert, div_self, hequiv, hequiv.isLittleO.tendsto_div_nhds_zero, hz.mono, isEquivalent_of_tendsto_one, isLittleO, sub_apply, sub_div, tendsto_congr, tendsto_const_nhds, tendsto_div_nhds_zero, this.add
-/
theorem isEquivalent_iff_tendsto_one (hz : forallᶠ x in l, v x != 0) :
    u ~[l] v ↔ Tendsto (u / v) l (𝓝 1) := by
  constructor
  · intro hequiv
    have := hequiv.isLittleO.tendsto_div_nhds_zero
    simp only [Pi.sub_apply, sub_div] at this
    have key : Tendsto (fun x => v x / v x) l (𝓝 1) :=
      (tendsto_congr' <| hz.mono fun x hnz => @div_self _ _ (v x) hnz).mpr tendsto_const_nhds
    convert! this.add key
    · simp
    · simp
  · exact isEquivalent_of_tendsto_one

end NormedField

section SMul

/--
theorem `IsEquivalent.smul` / 定理 `IsEquivalent.smul`

English:
theorem IsEquivalent.smul
  statement: {α E 𝕜 : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  proof: by
  rcases hab.exists_eq_mul with ⟨φ, hφ, habφ⟩
  have : ((fun x => a x • u x) - (fun x => b x • v x)) =ᶠ[l] fun x => b x • (φ x • u x - v x) := by
    convert!
      (habφ.comp₂ (· • ·) <| EventuallyEq.refl _ u).fun_sub
        (EventuallyEq.refl _ fun x => b x • v x) using 1
    ext
    rw [Pi.mu

中文:
定理 IsEquivalent.smul
  结论: {α E 𝕜 : 类型} [赋范域 𝕜] [赋范交换加群 E] [赋范空间 𝕜 E]
  证明: by
  rcases hab.exists_eq_mul with ⟨φ, hφ, habφ⟩
  have : ((fun x => a x • u x) - (fun x => b x • v x)) =ᶠ[l] fun x => b x • (φ x • u x - v x) := by
    convert!
      (habφ.comp₂ (· • ·) <| EventuallyEq.refl _ u).fun_sub
        (EventuallyEq.refl _ fun x => b x • v x) using 1
    ext
    rw [Pi.mu

Depends on / 依赖: EventuallyEq, EventuallyEq.refl, EventuallyEq.rfl, IsEquivalent, Pi.mul_apply, convert, exists_eq_mul, exists_pos, fun_sub, hab.exists_eq_mul, huv.isBigO.exists_pos, isBigO, isBigO_refl, isLittleO_congr, mul_apply, mul_comm, mul_smul, smul_isLittleO, smul_sub, this.symm
-/
theorem IsEquivalent.smul {α E 𝕜 : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {a b : α -> 𝕜} {u v : α -> E} {l : Filter α} (hab : a ~[l] b) (huv : u ~[l] v) :
    (fun x => a x • u x) ~[l] fun x => b x • v x := by
  rcases hab.exists_eq_mul with ⟨φ, hφ, habφ⟩
  have : ((fun x => a x • u x) - (fun x => b x • v x)) =ᶠ[l] fun x => b x • (φ x • u x - v x) := by
    convert!
      (habφ.comp₂ (· • ·) <| EventuallyEq.refl _ u).fun_sub
        (EventuallyEq.refl _ fun x => b x • v x) using 1
    ext
    rw [Pi.mul_apply]; rw [mul_comm]; rw [mul_smul]; rw [← smul_sub]
  refine (isLittleO_congr this.symm <| EventuallyEq.rfl).mp ((isBigO_refl b l).smul_isLittleO ?_)
  rcases huv.isBigO.exists_pos with ⟨C, hC, hCuv⟩
  rw [IsEquivalent] at *
  rw [isLittleO_iff] at *
  rw [IsBigOWith] at hCuv
  simp only [Metric.tendsto_nhds, dist_eq_norm] at hφ
  intro c hc
  specialize hφ (c / 2 / C) (div_pos (div_pos hc zero_lt_two) hC)
  specialize huv (div_pos hc zero_lt_two)
  refine hφ.mp (huv.mp <| hCuv.mono fun x hCuvx huvx hφx => ?_)
  have key :=
    calc
      ‖φ x - 1‖ * ‖u x‖ <= c / 2 / C * ‖u x‖ := by gcongr
      _ <= c / 2 / C * (C * ‖v x‖) := by gcongr
      _ = c / 2 * ‖v x‖ := by field
  calc
    ‖((fun x : α => φ x • u x) - v) x‖ = ‖(φ x - 1) • u x + (u x - v x)‖ := by
      simp [sub_smul, sub_add]
    _ <= ‖(φ x - 1) • u x‖ + ‖u x - v x‖ := norm_add_le _ _
    _ = ‖φ x - 1‖ * ‖u x‖ + ‖u x - v x‖ := by rw [norm_smul]
    _ <= c / 2 * ‖v x‖ + ‖u x - v x‖ := by gcongr
    _ <= c / 2 * ‖v x‖ + c / 2 * ‖v x‖ := by gcongr; exact huvx
    _ = c * ‖v x‖ := by ring

end SMul

section mul_inv

variable {α ι β : Type*} [NormedField β] {t u v w : α -> β} {l : Filter α}

/--
theorem `IsEquivalent.mul` / 定理 `IsEquivalent.mul`

English:
theorem IsEquivalent.mul
  given: (htu : t ~[l] u) (hvw : v ~[l] w)
  statement: t * v ~[l] u * w
  proof: htu.smul hvw

中文:
定理 IsEquivalent.mul
  条件: (htu : t ~[l] u) (hvw : v ~[l] w)
  结论: t * v ~[l] u * w
  证明: htu.smul hvw
-/
protected theorem IsEquivalent.mul (htu : t ~[l] u) (hvw : v ~[l] w) : t * v ~[l] u * w :=
  htu.smul hvw

/--
theorem `IsEquivalent.listProd` / 定理 `IsEquivalent.listProd`

English:
theorem IsEquivalent.listProd
  given: {L : List ι} {f g : ι -> α -> β} (h : forall i in L, f i ~[l] g i)
  proof: by
  induction L with
  | nil => simp [IsEquivalent.refl]
  | cons i L ihL =>
    simp only [List.forall_mem_cons, List.map_cons, List.prod_cons] at h ⊢
    exact h.1.mul (ihL h.2)

中文:
定理 IsEquivalent.listProd
  条件: {L : 列表 ι} {f g : ι -> α -> β} (h : 对任意 i in L, f i ~[l] g i)
  证明: by
  induction L with
  | nil => simp [IsEquivalent.refl]
  | cons i L ihL =>
    simp only [List.forall_mem_cons, List.map_cons, List.prod_cons] at h ⊢
    exact h.1.mul (ihL h.2)

Depends on / 依赖: IsEquivalent, IsEquivalent.refl, List.forall_mem_cons, List.map_cons, List.prod_cons, forall_mem_cons, map_cons, prod_cons
-/
theorem IsEquivalent.listProd {L : List ι} {f g : ι -> α -> β} (h : forall i in L, f i ~[l] g i) :
    (fun x => (L.map (f · x)).prod) ~[l] (fun x => (L.map (g · x)).prod) := by
  induction L with
  | nil => simp [IsEquivalent.refl]
  | cons i L ihL =>
    simp only [List.forall_mem_cons, List.map_cons, List.prod_cons] at h ⊢
    exact h.1.mul (ihL h.2)

/--
theorem `IsEquivalent.multisetProd` / 定理 `IsEquivalent.multisetProd`

English:
theorem IsEquivalent.multisetProd
  given: {s : Multiset ι} {f g : ι -> α -> β} (h : forall i in s, f i ~[l] g i)
  proof: by
  obtain ⟨l, rfl⟩ : exists l : List ι, ↑l = s := Quotient.mk_surjective s
  exact listProd h

中文:
定理 IsEquivalent.multisetProd
  条件: {s : Multiset ι} {f g : ι -> α -> β} (h : 对任意 i in s, f i ~[l] g i)
  证明: by
  obtain ⟨l, rfl⟩ : exists l : List ι, ↑l = s := Quotient.mk_surjective s
  exact listProd h

Depends on / 依赖: Quotient, Quotient.mk_surjective, listProd, mk_surjective
-/
theorem IsEquivalent.multisetProd {s : Multiset ι} {f g : ι -> α -> β} (h : forall i in s, f i ~[l] g i) :
    (fun x => (s.map (f · x)).prod) ~[l] (fun x => (s.map (g · x)).prod) := by
  obtain ⟨l, rfl⟩ : exists l : List ι, ↑l = s := Quotient.mk_surjective s
  exact listProd h

/--
theorem `IsEquivalent.finsetProd` / 定理 `IsEquivalent.finsetProd`

English:
theorem IsEquivalent.finsetProd
  given: {s : Finset ι} {f g : ι -> α -> β} (h : forall i in s, f i ~[l] g i)
  proof: multisetProd h

中文:
定理 IsEquivalent.finsetProd
  条件: {s : 有限集 ι} {f g : ι -> α -> β} (h : 对任意 i in s, f i ~[l] g i)
  证明: multisetProd h

Depends on / 依赖: multisetProd
-/
theorem IsEquivalent.finsetProd {s : Finset ι} {f g : ι -> α -> β} (h : forall i in s, f i ~[l] g i) :
    (∏ i in s, f i ·) ~[l] (∏ i in s, g i ·) :=
  multisetProd h

/--
theorem `IsEquivalent.inv` / 定理 `IsEquivalent.inv`

English:
theorem IsEquivalent.inv
  given: (huv : u ~[l] v)
  statement: u⁻¹ ~[l] v⁻¹
  proof: by
  rw [isEquivalent_iff_exists_eq_mul] at *
  rcases huv with ⟨φ, hφ, h⟩
  rw [← inv_one]
  refine ⟨fun x => (φ x)⁻¹, Tendsto.inv₀ hφ (by simp), ?_⟩
  convert! h.fun_inv
  simp [mul_comm]

中文:
定理 IsEquivalent.inv
  条件: (huv : u ~[l] v)
  结论: u⁻¹ ~[l] v⁻¹
  证明: by
  rw [isEquivalent_iff_exists_eq_mul] at *
  rcases huv with ⟨φ, hφ, h⟩
  rw [← inv_one]
  refine ⟨fun x => (φ x)⁻¹, Tendsto.inv₀ hφ (by simp), ?_⟩
  convert! h.fun_inv
  simp [mul_comm]
-/
protected theorem IsEquivalent.inv (huv : u ~[l] v) : u⁻¹ ~[l] v⁻¹ := by
  rw [isEquivalent_iff_exists_eq_mul] at *
  rcases huv with ⟨φ, hφ, h⟩
  rw [← inv_one]
  refine ⟨fun x => (φ x)⁻¹, Tendsto.inv₀ hφ (by simp), ?_⟩
  convert! h.fun_inv
  simp [mul_comm]

/--
theorem `IsEquivalent.div` / 定理 `IsEquivalent.div`

English:
theorem IsEquivalent.div
  given: (htu : t ~[l] u) (hvw : v ~[l] w)
  proof: by
  simpa only [div_eq_mul_inv] using htu.mul hvw.inv

中文:
定理 IsEquivalent.div
  条件: (htu : t ~[l] u) (hvw : v ~[l] w)
  证明: by
  simpa only [div_eq_mul_inv] using htu.mul hvw.inv
-/
protected theorem IsEquivalent.div (htu : t ~[l] u) (hvw : v ~[l] w) :
    t / v ~[l] u / w := by
  simpa only [div_eq_mul_inv] using htu.mul hvw.inv

/--
theorem `IsEquivalent.pow` / 定理 `IsEquivalent.pow`

English:
theorem IsEquivalent.pow
  given: (h : t ~[l] u) (n : Nat)
  statement: t ^ n ~[l] u ^ n
  proof: by
  induction n with
  | zero => simpa using IsEquivalent.refl
  | succ _ ih => simpa [pow_succ] using ih.mul h

中文:
定理 IsEquivalent.pow
  条件: (h : t ~[l] u) (n : 自然数)
  结论: t ^ n ~[l] u ^ n
  证明: by
  induction n with
  | zero => simpa using IsEquivalent.refl
  | succ _ ih => simpa [pow_succ] using ih.mul h
-/
protected theorem IsEquivalent.pow (h : t ~[l] u) (n : Nat) : t ^ n ~[l] u ^ n := by
  induction n with
  | zero => simpa using IsEquivalent.refl
  | succ _ ih => simpa [pow_succ] using ih.mul h

/--
theorem `IsEquivalent.zpow` / 定理 `IsEquivalent.zpow`

English:
theorem IsEquivalent.zpow
  given: (h : t ~[l] u) (z : Int)
  statement: t ^ z ~[l] u ^ z
  proof: by
  match z with
  | Int.ofNat _ => simpa using h.pow _
  | Int.negSucc _ => simpa using (h.pow _).inv

中文:
定理 IsEquivalent.zpow
  条件: (h : t ~[l] u) (z : 整数)
  结论: t ^ z ~[l] u ^ z
  证明: by
  match z with
  | Int.ofNat _ => simpa using h.pow _
  | Int.negSucc _ => simpa using (h.pow _).inv
-/
protected theorem IsEquivalent.zpow (h : t ~[l] u) (z : Int) : t ^ z ~[l] u ^ z := by
  match z with
  | Int.ofNat _ => simpa using h.pow _
  | Int.negSucc _ => simpa using (h.pow _).inv

end mul_inv

section NormedLinearOrderedField

variable {α β : Type*} [NormedField β] [LinearOrder β] [IsStrictOrderedRing β]
  {u v : α -> β} {l : Filter α}

/--
theorem `IsEquivalent.tendsto_atTop` / 定理 `IsEquivalent.tendsto_atTop`

English:
theorem IsEquivalent.tendsto_atTop
  given: [OrderTopology β] (huv : u ~[l] v) (hu : Tendsto u l atTop)
  proof: let ⟨φ, hφ, h⟩ := huv.symm.exists_eq_mul
  Tendsto.congr' h.symm (mul_comm u φ ▸ hu.atTop_mul_pos zero_lt_one hφ)

中文:
定理 IsEquivalent.tendsto_atTop
  条件: [Order拓扑 β] (huv : u ~[l] v) (hu : 收敛 u l atTop)
  证明: let ⟨φ, hφ, h⟩ := huv.symm.exists_eq_mul
  Tendsto.congr' h.symm (mul_comm u φ ▸ hu.atTop_mul_pos zero_lt_one hφ)

Depends on / 依赖: Tendsto, Tendsto.congr, atTop_mul_pos, exists_eq_mul, h.symm, hu.atTop_mul_pos, huv.symm.exists_eq_mul, mul_comm, zero_lt_one
-/
theorem IsEquivalent.tendsto_atTop [OrderTopology β] (huv : u ~[l] v) (hu : Tendsto u l atTop) :
    Tendsto v l atTop :=
  let ⟨φ, hφ, h⟩ := huv.symm.exists_eq_mul
  Tendsto.congr' h.symm (mul_comm u φ ▸ hu.atTop_mul_pos zero_lt_one hφ)

/--
theorem `IsEquivalent.tendsto_atTop_iff` / 定理 `IsEquivalent.tendsto_atTop_iff`

English:
theorem IsEquivalent.tendsto_atTop_iff
  given: [OrderTopology β] (huv : u ~[l] v)
  proof: ⟨huv.tendsto_atTop, huv.symm.tendsto_atTop⟩

中文:
定理 IsEquivalent.tendsto_atTop_iff
  条件: [Order拓扑 β] (huv : u ~[l] v)
  证明: ⟨huv.tendsto_atTop, huv.symm.tendsto_atTop⟩

Depends on / 依赖: huv.symm.tendsto_atTop, huv.tendsto_atTop, tendsto_atTop
-/
theorem IsEquivalent.tendsto_atTop_iff [OrderTopology β] (huv : u ~[l] v) :
    Tendsto u l atTop ↔ Tendsto v l atTop :=
  ⟨huv.tendsto_atTop, huv.symm.tendsto_atTop⟩

/--
theorem `IsEquivalent.tendsto_atBot` / 定理 `IsEquivalent.tendsto_atBot`

English:
theorem IsEquivalent.tendsto_atBot
  given: [OrderTopology β] (huv : u ~[l] v) (hu : Tendsto u l atBot)
  proof: by
  convert! tendsto_neg_atTop_atBot.comp (huv.neg.tendsto_atTop <| tendsto_neg_atBot_atTop.comp hu)
  ext
  simp

中文:
定理 IsEquivalent.tendsto_atBot
  条件: [Order拓扑 β] (huv : u ~[l] v) (hu : 收敛 u l atBot)
  证明: by
  convert! tendsto_neg_atTop_atBot.comp (huv.neg.tendsto_atTop <| tendsto_neg_atBot_atTop.comp hu)
  ext
  simp

Depends on / 依赖: convert, huv.neg.tendsto_atTop, tendsto_atTop, tendsto_neg_atBot_atTop, tendsto_neg_atBot_atTop.comp, tendsto_neg_atTop_atBot, tendsto_neg_atTop_atBot.comp
-/
theorem IsEquivalent.tendsto_atBot [OrderTopology β] (huv : u ~[l] v) (hu : Tendsto u l atBot) :
    Tendsto v l atBot := by
  convert! tendsto_neg_atTop_atBot.comp (huv.neg.tendsto_atTop <| tendsto_neg_atBot_atTop.comp hu)
  ext
  simp

/--
theorem `IsEquivalent.tendsto_atBot_iff` / 定理 `IsEquivalent.tendsto_atBot_iff`

English:
theorem IsEquivalent.tendsto_atBot_iff
  given: [OrderTopology β] (huv : u ~[l] v)
  proof: ⟨huv.tendsto_atBot, huv.symm.tendsto_atBot⟩

中文:
定理 IsEquivalent.tendsto_atBot_iff
  条件: [Order拓扑 β] (huv : u ~[l] v)
  证明: ⟨huv.tendsto_atBot, huv.symm.tendsto_atBot⟩

Depends on / 依赖: huv.symm.tendsto_atBot, huv.tendsto_atBot, tendsto_atBot
-/
theorem IsEquivalent.tendsto_atBot_iff [OrderTopology β] (huv : u ~[l] v) :
    Tendsto u l atBot ↔ Tendsto v l atBot :=
  ⟨huv.tendsto_atBot, huv.symm.tendsto_atBot⟩

section ClosedIicTopology

variable [ClosedIicTopology β]

/--
lemma `IsEquivalent.exists_pos_eq_mul` / 引理 `IsEquivalent.exists_pos_eq_mul`

English:
lemma IsEquivalent.exists_pos_eq_mul
  given: (h : u ~[l] v)
  proof: by
  obtain ⟨φ, hφ, h_eq⟩ := h.exists_eq_mul
  exact ⟨φ, hφ.eventually_const_lt (zero_lt_one' β), h_eq⟩

中文:
引理 IsEquivalent.存在_pos_eq_mul
  条件: (h : u ~[l] v)
  证明: by
  obtain ⟨φ, hφ, h_eq⟩ := h.exists_eq_mul
  exact ⟨φ, hφ.eventually_const_lt (zero_lt_one' β), h_eq⟩

Depends on / 依赖: eventually_const_lt, exists_eq_mul, h.exists_eq_mul, h_eq, zero_lt_one
-/
lemma IsEquivalent.exists_pos_eq_mul (h : u ~[l] v) :
    exists φ, (forallᶠ x in l, 0 < φ x) ∧ (u =ᶠ[l] φ * v) := by
  obtain ⟨φ, hφ, h_eq⟩ := h.exists_eq_mul
  exact ⟨φ, hφ.eventually_const_lt (zero_lt_one' β), h_eq⟩

/--
theorem `IsEquivalent.eventually_nonneg` / 定理 `IsEquivalent.eventually_nonneg`

English:
theorem IsEquivalent.eventually_nonneg
  given: (h : u ~[l] v) (hv : forallᶠ t in l, 0 <= v t)
  proof: by
  obtain ⟨φ, hφ, h_eq⟩ := h.exists_pos_eq_mul
  exact (hφ.and (hv.and h_eq)).mono (fun x ⟨hφ, hv, h_eq⟩ => h_eq ▸ mul_nonneg hφ.le hv)

中文:
定理 IsEquivalent.eventually_nonneg
  条件: (h : u ~[l] v) (hv : 对任意ᶠ t in l, 0 <= v t)
  证明: by
  obtain ⟨φ, hφ, h_eq⟩ := h.exists_pos_eq_mul
  exact (hφ.and (hv.and h_eq)).mono (fun x ⟨hφ, hv, h_eq⟩ => h_eq ▸ mul_nonneg hφ.le hv)

Depends on / 依赖: exists_pos_eq_mul, h.exists_pos_eq_mul, h_eq, hv.and, mul_nonneg
-/
theorem IsEquivalent.eventually_nonneg (h : u ~[l] v) (hv : forallᶠ t in l, 0 <= v t) :
    forallᶠ x in l, 0 <= u x := by
  obtain ⟨φ, hφ, h_eq⟩ := h.exists_pos_eq_mul
  exact (hφ.and (hv.and h_eq)).mono (fun x ⟨hφ, hv, h_eq⟩ => h_eq ▸ mul_nonneg hφ.le hv)

/--
theorem `IsEquivalent.eventually_pos` / 定理 `IsEquivalent.eventually_pos`

English:
theorem IsEquivalent.eventually_pos
  given: (h : u ~[l] v) (hv : forallᶠ t in l, 0 < v t)
  proof: by
  obtain ⟨φ, hφ, h_eq⟩ := h.exists_pos_eq_mul
  exact (hφ.and (hv.and h_eq)).mono (fun x ⟨hφ, hv, h_eq⟩ => h_eq ▸ mul_pos hφ hv)

中文:
定理 IsEquivalent.eventually_pos
  条件: (h : u ~[l] v) (hv : 对任意ᶠ t in l, 0 < v t)
  证明: by
  obtain ⟨φ, hφ, h_eq⟩ := h.exists_pos_eq_mul
  exact (hφ.and (hv.and h_eq)).mono (fun x ⟨hφ, hv, h_eq⟩ => h_eq ▸ mul_pos hφ hv)

Depends on / 依赖: exists_pos_eq_mul, h.exists_pos_eq_mul, h_eq, hv.and, mul_pos
-/
theorem IsEquivalent.eventually_pos (h : u ~[l] v) (hv : forallᶠ t in l, 0 < v t) :
    forallᶠ x in l, 0 < u x := by
  obtain ⟨φ, hφ, h_eq⟩ := h.exists_pos_eq_mul
  exact (hφ.and (hv.and h_eq)).mono (fun x ⟨hφ, hv, h_eq⟩ => h_eq ▸ mul_pos hφ hv)

/--
theorem `IsEquivalent.eventually_nonpos` / 定理 `IsEquivalent.eventually_nonpos`

English:
theorem IsEquivalent.eventually_nonpos
  given: (h : u ~[l] v) (hv : forallᶠ t in l, v t <= 0)
  proof: by
  obtain ⟨φ, hφ, h_eq⟩ := h.exists_pos_eq_mul
  exact (hφ.and (hv.and h_eq)).mono (fun x ⟨hφ, hv, h_eq⟩ =>
    h_eq ▸ mul_nonpos_of_nonneg_of_nonpos hφ.le hv)

中文:
定理 IsEquivalent.eventually_nonpos
  条件: (h : u ~[l] v) (hv : 对任意ᶠ t in l, v t <= 0)
  证明: by
  obtain ⟨φ, hφ, h_eq⟩ := h.exists_pos_eq_mul
  exact (hφ.and (hv.and h_eq)).mono (fun x ⟨hφ, hv, h_eq⟩ =>
    h_eq ▸ mul_nonpos_of_nonneg_of_nonpos hφ.le hv)

Depends on / 依赖: exists_pos_eq_mul, h.exists_pos_eq_mul, h_eq, hv.and, mul_nonpos_of_nonneg_of_nonpos
-/
theorem IsEquivalent.eventually_nonpos (h : u ~[l] v) (hv : forallᶠ t in l, v t <= 0) :
    forallᶠ x in l, u x <= 0 := by
  obtain ⟨φ, hφ, h_eq⟩ := h.exists_pos_eq_mul
  exact (hφ.and (hv.and h_eq)).mono (fun x ⟨hφ, hv, h_eq⟩ =>
    h_eq ▸ mul_nonpos_of_nonneg_of_nonpos hφ.le hv)

/--
theorem `IsEquivalent.eventually_neg` / 定理 `IsEquivalent.eventually_neg`

English:
theorem IsEquivalent.eventually_neg
  given: (h : u ~[l] v) (hv : forallᶠ t in l, v t < 0)
  proof: by
  obtain ⟨φ, hφ, h_eq⟩ := h.exists_pos_eq_mul
  exact (hφ.and (hv.and h_eq)).mono (fun x ⟨hφ, hv, h_eq⟩ => h_eq ▸ mul_neg_of_pos_of_neg hφ hv)

中文:
定理 IsEquivalent.eventually_neg
  条件: (h : u ~[l] v) (hv : 对任意ᶠ t in l, v t < 0)
  证明: by
  obtain ⟨φ, hφ, h_eq⟩ := h.exists_pos_eq_mul
  exact (hφ.and (hv.and h_eq)).mono (fun x ⟨hφ, hv, h_eq⟩ => h_eq ▸ mul_neg_of_pos_of_neg hφ hv)

Depends on / 依赖: exists_pos_eq_mul, h.exists_pos_eq_mul, h_eq, hv.and, mul_neg_of_pos_of_neg
-/
theorem IsEquivalent.eventually_neg (h : u ~[l] v) (hv : forallᶠ t in l, v t < 0) :
    forallᶠ x in l, u x < 0 := by
  obtain ⟨φ, hφ, h_eq⟩ := h.exists_pos_eq_mul
  exact (hφ.and (hv.and h_eq)).mono (fun x ⟨hφ, hv, h_eq⟩ => h_eq ▸ mul_neg_of_pos_of_neg hφ hv)

end ClosedIicTopology

end NormedLinearOrderedField

section Real

/--
theorem `IsEquivalent.add_add_of_nonneg` / 定理 `IsEquivalent.add_add_of_nonneg`

English:
theorem IsEquivalent.add_add_of_nonneg
  statement: {α : Type*} {u v t w : α -> Real} {l : Filter α}
  proof: by
  simp only [IsEquivalent, add_sub_add_comm]
  change (fun x => (u - v) x + (t - w) x) =o[l] (fun x => v x + w x)
  conv => enter [3, x]; rw [← abs_eq_self.mpr (hu x), ← abs_eq_self.mpr (hw x)]
  simpa [← Real.norm_eq_abs] using .add_add htu hvw

中文:
定理 IsEquivalent.add_add_of_nonneg
  结论: {α : 类型} {u v t w : α -> 实数} {l : 滤子 α}
  证明: by
  simp only [IsEquivalent, add_sub_add_comm]
  change (fun x => (u - v) x + (t - w) x) =o[l] (fun x => v x + w x)
  conv => enter [3, x]; rw [← abs_eq_self.mpr (hu x), ← abs_eq_self.mpr (hw x)]
  simpa [← Real.norm_eq_abs] using .add_add htu hvw

Depends on / 依赖: IsEquivalent, Real.norm_eq_abs, abs_eq_self, abs_eq_self.mpr, add_add, add_sub_add_comm, norm_eq_abs
-/
theorem IsEquivalent.add_add_of_nonneg {α : Type*} {u v t w : α -> Real} {l : Filter α}
    (hu : 0 <= v) (hw : 0 <= w) (htu : u ~[l] v) (hvw : t ~[l] w) :
    u + t ~[l] v + w := by
  simp only [IsEquivalent, add_sub_add_comm]
  change (fun x => (u - v) x + (t - w) x) =o[l] (fun x => v x + w x)
  conv => enter [3, x]; rw [← abs_eq_self.mpr (hu x), ← abs_eq_self.mpr (hw x)]
  simpa [← Real.norm_eq_abs] using .add_add htu hvw

end Real

end Asymptotics

open Filter Asymptotics

open Asymptotics

variable {α β β₂ : Type*} [NormedAddCommGroup β] [Norm β₂] {l : Filter α}

/--
theorem `Filter.EventuallyEq.isEquivalent` / 定理 `Filter.EventuallyEq.isEquivalent`

English:
theorem Filter.EventuallyEq.isEquivalent
  given: {u v : α -> β} (h : u =ᶠ[l] v)
  statement: u ~[l] v
  proof: IsEquivalent.congr_right (isLittleO_refl_left _ _) h

@[trans]

中文:
定理 滤子.EventuallyEq.isEquivalent
  条件: {u v : α -> β} (h : u =ᶠ[l] v)
  结论: u ~[l] v
  证明: IsEquivalent.congr_right (isLittleO_refl_left _ _) h

@[trans]

Depends on / 依赖: IsEquivalent, IsEquivalent.congr_right, congr_right, isLittleO_refl_left
-/
theorem Filter.EventuallyEq.isEquivalent {u v : α -> β} (h : u =ᶠ[l] v) : u ~[l] v :=
  IsEquivalent.congr_right (isLittleO_refl_left _ _) h

@[trans]
/--
theorem `Filter.EventuallyEq.trans_isEquivalent` / 定理 `Filter.EventuallyEq.trans_isEquivalent`

English:
theorem Filter.EventuallyEq.trans_isEquivalent
  statement: {f g₁ g₂ : α -> β} (h : f =ᶠ[l] g₁)
  proof: h.isEquivalent.trans h₂

中文:
定理 滤子.EventuallyEq.trans_isEquivalent
  结论: {f g₁ g₂ : α -> β} (h : f =ᶠ[l] g₁)
  证明: h.isEquivalent.trans h₂

Depends on / 依赖: h.isEquivalent.trans, isEquivalent
-/
theorem Filter.EventuallyEq.trans_isEquivalent {f g₁ g₂ : α -> β} (h : f =ᶠ[l] g₁)
    (h₂ : g₁ ~[l] g₂) : f ~[l] g₂ :=
  h.isEquivalent.trans h₂

namespace Asymptotics

/--
Instance `transIsEquivalentIsEquivalent` / 实例 `transIsEquivalentIsEquivalent`

English:
instance transIsEquivalentIsEquivalent
  signature: :
  body: IsEquivalent.trans

中文:
实例 transIsEquivalentIsEquivalent
  签名: :
  定义体: IsEquivalent.trans

Depends on / 依赖: IsEquivalent, IsEquivalent.trans
-/
instance transIsEquivalentIsEquivalent :
    @Trans (α -> β) (α -> β) (α -> β) (IsEquivalent l) (IsEquivalent l) (IsEquivalent l) where
  trans := IsEquivalent.trans

/--
Instance `transEventuallyEqIsEquivalent` / 实例 `transEventuallyEqIsEquivalent`

English:
instance transEventuallyEqIsEquivalent
  signature: :
  body: EventuallyEq.trans_isEquivalent

@[trans]

中文:
实例 transEventuallyEqIsEquivalent
  签名: :
  定义体: EventuallyEq.trans_isEquivalent

@[trans]

Depends on / 依赖: EventuallyEq, EventuallyEq.trans_isEquivalent, trans_isEquivalent
-/
instance transEventuallyEqIsEquivalent :
    @Trans (α -> β) (α -> β) (α -> β) (EventuallyEq l) (IsEquivalent l) (IsEquivalent l) where
  trans := EventuallyEq.trans_isEquivalent

@[trans]
/--
theorem `IsEquivalent.trans_eventuallyEq` / 定理 `IsEquivalent.trans_eventuallyEq`

English:
theorem IsEquivalent.trans_eventuallyEq
  statement: {f g₁ g₂ : α -> β} (h : f ~[l] g₁)
  proof: h.trans h₂.isEquivalent

中文:
定理 IsEquivalent.trans_eventuallyEq
  结论: {f g₁ g₂ : α -> β} (h : f ~[l] g₁)
  证明: h.trans h₂.isEquivalent

Depends on / 依赖: h.trans, isEquivalent
-/
theorem IsEquivalent.trans_eventuallyEq {f g₁ g₂ : α -> β} (h : f ~[l] g₁)
    (h₂ : g₁ =ᶠ[l] g₂) : f ~[l] g₂ :=
  h.trans h₂.isEquivalent

/--
Instance `transIsEquivalentEventuallyEq` / 实例 `transIsEquivalentEventuallyEq`

English:
instance transIsEquivalentEventuallyEq
  signature: :
  body: IsEquivalent.trans_eventuallyEq

@[trans]

中文:
实例 transIsEquivalentEventuallyEq
  签名: :
  定义体: IsEquivalent.trans_eventuallyEq

@[trans]

Depends on / 依赖: IsEquivalent, IsEquivalent.trans_eventuallyEq, trans_eventuallyEq
-/
instance transIsEquivalentEventuallyEq :
    @Trans (α -> β) (α -> β) (α -> β) (IsEquivalent l) (EventuallyEq l) (IsEquivalent l) where
  trans := IsEquivalent.trans_eventuallyEq

@[trans]
/--
theorem `IsEquivalent.trans_isBigO` / 定理 `IsEquivalent.trans_isBigO`

English:
theorem IsEquivalent.trans_isBigO
  given: {f g₁ : α -> β} {g₂ : α -> β₂} (h : f ~[l] g₁) (h₂ : g₁ =O[l] g₂)
  proof: IsBigO.trans h.isBigO h₂

中文:
定理 IsEquivalent.trans_isBigO
  条件: {f g₁ : α -> β} {g₂ : α -> β₂} (h : f ~[l] g₁) (h₂ : g₁ =O[l] g₂)
  证明: IsBigO.trans h.isBigO h₂

Depends on / 依赖: IsBigO, IsBigO.trans, h.isBigO, isBigO
-/
theorem IsEquivalent.trans_isBigO {f g₁ : α -> β} {g₂ : α -> β₂} (h : f ~[l] g₁) (h₂ : g₁ =O[l] g₂) :
    f =O[l] g₂ :=
  IsBigO.trans h.isBigO h₂

/--
Instance `transIsEquivalentIsBigO` / 实例 `transIsEquivalentIsBigO`

English:
instance transIsEquivalentIsBigO
  signature: :
  body: IsEquivalent.trans_isBigO

@[trans]

中文:
实例 transIsEquivalentIsBigO
  签名: :
  定义体: IsEquivalent.trans_isBigO

@[trans]

Depends on / 依赖: IsEquivalent, IsEquivalent.trans_isBigO, trans_isBigO
-/
instance transIsEquivalentIsBigO :
    @Trans (α -> β) (α -> β) (α -> β₂) (IsEquivalent l) (IsBigO l) (IsBigO l) where
  trans := IsEquivalent.trans_isBigO

@[trans]
/--
theorem `IsBigO.trans_isEquivalent` / 定理 `IsBigO.trans_isEquivalent`

English:
theorem IsBigO.trans_isEquivalent
  given: {f : α -> β₂} {g₁ g₂ : α -> β} (h : f =O[l] g₁) (h₂ : g₁ ~[l] g₂)
  proof: IsBigO.trans h h₂.isBigO

中文:
定理 IsBigO.trans_isEquivalent
  条件: {f : α -> β₂} {g₁ g₂ : α -> β} (h : f =O[l] g₁) (h₂ : g₁ ~[l] g₂)
  证明: IsBigO.trans h h₂.isBigO

Depends on / 依赖: IsBigO, IsBigO.trans, isBigO
-/
theorem IsBigO.trans_isEquivalent {f : α -> β₂} {g₁ g₂ : α -> β} (h : f =O[l] g₁) (h₂ : g₁ ~[l] g₂) :
    f =O[l] g₂ :=
  IsBigO.trans h h₂.isBigO

/--
Instance `transIsBigOIsEquivalent` / 实例 `transIsBigOIsEquivalent`

English:
instance transIsBigOIsEquivalent
  signature: :
  body: IsBigO.trans_isEquivalent

@[trans]

中文:
实例 transIsBigOIsEquivalent
  签名: :
  定义体: IsBigO.trans_isEquivalent

@[trans]

Depends on / 依赖: IsBigO, IsBigO.trans_isEquivalent, trans_isEquivalent
-/
instance transIsBigOIsEquivalent :
    @Trans (α -> β₂) (α -> β) (α -> β) (IsBigO l) (IsEquivalent l) (IsBigO l) where
  trans := IsBigO.trans_isEquivalent

@[trans]
/--
theorem `IsEquivalent.trans_isLittleO` / 定理 `IsEquivalent.trans_isLittleO`

English:
theorem IsEquivalent.trans_isLittleO
  statement: {f g₁ : α -> β} {g₂ : α -> β₂} (h : f ~[l] g₁)
  proof: IsBigO.trans_isLittleO h.isBigO h₂

中文:
定理 IsEquivalent.trans_isLittleO
  结论: {f g₁ : α -> β} {g₂ : α -> β₂} (h : f ~[l] g₁)
  证明: IsBigO.trans_isLittleO h.isBigO h₂

Depends on / 依赖: IsBigO, IsBigO.trans_isLittleO, h.isBigO, isBigO, trans_isLittleO
-/
theorem IsEquivalent.trans_isLittleO {f g₁ : α -> β} {g₂ : α -> β₂} (h : f ~[l] g₁)
    (h₂ : g₁ =o[l] g₂) : f =o[l] g₂ :=
  IsBigO.trans_isLittleO h.isBigO h₂

/--
Instance `transIsEquivalentIsLittleO` / 实例 `transIsEquivalentIsLittleO`

English:
instance transIsEquivalentIsLittleO
  signature: :
  body: IsEquivalent.trans_isLittleO

@[trans]

中文:
实例 transIsEquivalentIsLittleO
  签名: :
  定义体: IsEquivalent.trans_isLittleO

@[trans]

Depends on / 依赖: IsEquivalent, IsEquivalent.trans_isLittleO, trans_isLittleO
-/
instance transIsEquivalentIsLittleO :
    @Trans (α -> β) (α -> β) (α -> β₂) (IsEquivalent l) (IsLittleO l) (IsLittleO l) where
  trans := IsEquivalent.trans_isLittleO

@[trans]
/--
theorem `IsLittleO.trans_isEquivalent` / 定理 `IsLittleO.trans_isEquivalent`

English:
theorem IsLittleO.trans_isEquivalent
  statement: {f : α -> β₂} {g₁ g₂ : α -> β} (h : f =o[l] g₁)
  proof: IsLittleO.trans_isBigO h h₂.isBigO

中文:
定理 IsLittleO.trans_isEquivalent
  结论: {f : α -> β₂} {g₁ g₂ : α -> β} (h : f =o[l] g₁)
  证明: IsLittleO.trans_isBigO h h₂.isBigO

Depends on / 依赖: IsLittleO, IsLittleO.trans_isBigO, isBigO, trans_isBigO
-/
theorem IsLittleO.trans_isEquivalent {f : α -> β₂} {g₁ g₂ : α -> β} (h : f =o[l] g₁)
    (h₂ : g₁ ~[l] g₂) : f =o[l] g₂ :=
  IsLittleO.trans_isBigO h h₂.isBigO

/--
Instance `transIsLittleOIsEquivalent` / 实例 `transIsLittleOIsEquivalent`

English:
instance transIsLittleOIsEquivalent
  signature: :
  body: IsLittleO.trans_isEquivalent

@[trans]

中文:
实例 transIsLittleOIsEquivalent
  签名: :
  定义体: IsLittleO.trans_isEquivalent

@[trans]

Depends on / 依赖: IsLittleO, IsLittleO.trans_isEquivalent, trans_isEquivalent
-/
instance transIsLittleOIsEquivalent :
    @Trans (α -> β₂) (α -> β) (α -> β) (IsLittleO l) (IsEquivalent l) (IsLittleO l) where
  trans := IsLittleO.trans_isEquivalent

@[trans]
/--
theorem `IsEquivalent.trans_isTheta` / 定理 `IsEquivalent.trans_isTheta`

English:
theorem IsEquivalent.trans_isTheta
  statement: {f g₁ : α -> β} {g₂ : α -> β₂} (h : f ~[l] g₁)
  proof: IsTheta.trans h.isTheta h₂

中文:
定理 IsEquivalent.trans_isTheta
  结论: {f g₁ : α -> β} {g₂ : α -> β₂} (h : f ~[l] g₁)
  证明: IsTheta.trans h.isTheta h₂

Depends on / 依赖: IsTheta, IsTheta.trans, h.isTheta, isTheta
-/
theorem IsEquivalent.trans_isTheta {f g₁ : α -> β} {g₂ : α -> β₂} (h : f ~[l] g₁)
    (h₂ : g₁ =Θ[l] g₂) : f =Θ[l] g₂ :=
  IsTheta.trans h.isTheta h₂

/--
Instance `transIsEquivalentIsTheta` / 实例 `transIsEquivalentIsTheta`

English:
instance transIsEquivalentIsTheta
  signature: :
  body: IsEquivalent.trans_isTheta

@[trans]

中文:
实例 transIsEquivalentIsTheta
  签名: :
  定义体: IsEquivalent.trans_isTheta

@[trans]

Depends on / 依赖: IsEquivalent, IsEquivalent.trans_isTheta, trans_isTheta
-/
instance transIsEquivalentIsTheta :
    @Trans (α -> β) (α -> β) (α -> β₂) (IsEquivalent l) (IsTheta l) (IsTheta l) where
  trans := IsEquivalent.trans_isTheta

@[trans]
/--
theorem `IsTheta.trans_isEquivalent` / 定理 `IsTheta.trans_isEquivalent`

English:
theorem IsTheta.trans_isEquivalent
  statement: {f : α -> β₂} {g₁ g₂ : α -> β} (h : f =Θ[l] g₁)
  proof: IsTheta.trans h h₂.isTheta

中文:
定理 IsTheta.trans_isEquivalent
  结论: {f : α -> β₂} {g₁ g₂ : α -> β} (h : f =Θ[l] g₁)
  证明: IsTheta.trans h h₂.isTheta

Depends on / 依赖: IsTheta, IsTheta.trans, isTheta
-/
theorem IsTheta.trans_isEquivalent {f : α -> β₂} {g₁ g₂ : α -> β} (h : f =Θ[l] g₁)
    (h₂ : g₁ ~[l] g₂) : f =Θ[l] g₂ :=
  IsTheta.trans h h₂.isTheta

/--
Instance `transIsThetaIsEquivalent` / 实例 `transIsThetaIsEquivalent`

English:
instance transIsThetaIsEquivalent
  signature: :
  body: IsTheta.trans_isEquivalent

中文:
实例 transIsThetaIsEquivalent
  签名: :
  定义体: IsTheta.trans_isEquivalent

Depends on / 依赖: IsTheta, IsTheta.trans_isEquivalent, trans_isEquivalent
-/
instance transIsThetaIsEquivalent :
    @Trans (α -> β₂) (α -> β) (α -> β) (IsTheta l) (IsEquivalent l) (IsTheta l) where
  trans := IsTheta.trans_isEquivalent

/--
theorem `IsEquivalent.comp_tendsto` / 定理 `IsEquivalent.comp_tendsto`

English:
theorem IsEquivalent.comp_tendsto
  statement: {α₂ : Type*} {f g : α₂ -> β} {l' : Filter α₂}
  proof: IsLittleO.comp_tendsto hfg hk

@[simp]

中文:
定理 IsEquivalent.comp_tendsto
  结论: {α₂ : 类型} {f g : α₂ -> β} {l' : 滤子 α₂}
  证明: IsLittleO.comp_tendsto hfg hk

@[simp]

Depends on / 依赖: IsLittleO, IsLittleO.comp_tendsto, comp_tendsto
-/
theorem IsEquivalent.comp_tendsto {α₂ : Type*} {f g : α₂ -> β} {l' : Filter α₂}
    (hfg : f ~[l'] g) {k : α -> α₂} (hk : Filter.Tendsto k l l') : (f ∘ k) ~[l] (g ∘ k) :=
  IsLittleO.comp_tendsto hfg hk

@[simp]
/--
theorem `isEquivalent_map` / 定理 `isEquivalent_map`

English:
theorem isEquivalent_map
  given: {α₂ : Type*} {f g : α₂ -> β} {k : α -> α₂}
  proof: isLittleO_map

中文:
定理 isEquivalent_map
  条件: {α₂ : 类型} {f g : α₂ -> β} {k : α -> α₂}
  证明: isLittleO_map

Depends on / 依赖: isLittleO_map
-/
theorem isEquivalent_map {α₂ : Type*} {f g : α₂ -> β} {k : α -> α₂} :
    f ~[Filter.map k l] g ↔ (f ∘ k) ~[l] (g ∘ k) :=
  isLittleO_map

/--
theorem `IsEquivalent.mono` / 定理 `IsEquivalent.mono`

English:
theorem IsEquivalent.mono
  given: {f g : α -> β} {l' : Filter α} (h : f ~[l'] g) (hl : l <= l')
  proof: IsLittleO.mono h hl

中文:
定理 IsEquivalent.mono
  条件: {f g : α -> β} {l' : 滤子 α} (h : f ~[l'] g) (hl : l <= l')
  证明: IsLittleO.mono h hl

Depends on / 依赖: IsLittleO, IsLittleO.mono
-/
theorem IsEquivalent.mono {f g : α -> β} {l' : Filter α} (h : f ~[l'] g) (hl : l <= l') :
    f ~[l] g :=
  IsLittleO.mono h hl

end Asymptotics
