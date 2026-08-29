/-
Copyright (c) 2023 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
module

public import Mathlib.Data.Set.Function
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.EMetricSpace.VariationOnFromTo

/-!
# Constant speed

This file defines the notion of constant (and unit) speed for a function `f : ℝ → E` with
pseudo-emetric structure on `E` with respect to a set `s : Set ℝ` and "speed" `l : ℝ≥0`, and shows
that if `f` has locally bounded variation on `s`, it can be obtained (up to distance zero, on `s`),
as a composite `φ ∘ (variationOnFromTo f s a)`, where `φ` has unit speed and `a ∈ s`.

## Main definitions

* `HasConstantSpeedOnWith f s l`, stating that the speed of `f` on `s` is `l`.
* `HasUnitSpeedOn f s`, stating that the speed of `f` on `s` is `1`.
* `naturalParameterization f s a : ℝ → E`, the unit speed reparameterization of `f` on `s` relative
  to `a`.

## Main statements

* `unique_unit_speed_on_Icc_zero` proves that if `f` and `f ∘ φ` are both naturally
  parameterized on closed intervals starting at `0`, then `φ` must be the identity on
  those intervals.
* `edist_naturalParameterization_eq_zero` proves that if `f` has locally bounded variation, then
  precomposing `naturalParameterization f s a` with `variationOnFromTo f s a` yields a function
  at distance zero from `f` on `s`.
* `has_unit_speed_naturalParameterization` proves that if `f` has locally bounded
  variation, then `naturalParameterization f s a` has unit speed on `s`.

## Tags

arc-length, parameterization
-/

@[expose] public section


open scoped NNReal ENNReal

open Set

variable {α : Type*} [LinearOrder α] {E : Type*} [PseudoEMetricSpace E]
variable (f : Real -> E) (s : Set Real) (l : Real>=0)

/--
Definition of `HasConstantSpeedOnWith` / `HasConstantSpeedOnWith` 的定义

English:
definition HasConstantSpeedOnWith
  body: forall ⦃x⦄ (_ : x in s) ⦃y⦄ (_ : y in s), eVariationOn f (s inter Icc x y) = ENNReal.ofReal (l * (y - x))

中文:
定义 HasConstantSpeedOnWith
  定义体: forall ⦃x⦄ (_ : x in s) ⦃y⦄ (_ : y in s), eVariationOn f (s inter Icc x y) = ENNReal.ofReal (l * (y - x))

Depends on / 依赖: ENNReal, ENNReal.ofReal, eVariationOn, ofReal
-/
def HasConstantSpeedOnWith :=
  forall ⦃x⦄ (_ : x in s) ⦃y⦄ (_ : y in s), eVariationOn f (s inter Icc x y) = ENNReal.ofReal (l * (y - x))

variable {f s l}

/--
theorem `HasConstantSpeedOnWith.hasLocallyBoundedVariationOn` / 定理 `HasConstantSpeedOnWith.hasLocallyBoundedVariationOn`

English:
theorem HasConstantSpeedOnWith.hasLocallyBoundedVariationOn
  given: (h : HasConstantSpeedOnWith f s l)
  proof: fun x y hx hy => by
  simp only [BoundedVariationOn, h hx hy, Ne, ENNReal.ofReal_ne_top, not_false_iff]

中文:
定理 HasConstantSpeedOnWith.hasLocallyBoundedVariationOn
  条件: (h : HasConstantSpeedOnWith f s l)
  证明: fun x y hx hy => by
  simp only [BoundedVariationOn, h hx hy, Ne, ENNReal.ofReal_ne_top, not_false_iff]

Depends on / 依赖: BoundedVariationOn, ENNReal, ENNReal.ofReal_ne_top, not_false_iff, ofReal_ne_top
-/
theorem HasConstantSpeedOnWith.hasLocallyBoundedVariationOn (h : HasConstantSpeedOnWith f s l) :
    LocallyBoundedVariationOn f s := fun x y hx hy => by
  simp only [BoundedVariationOn, h hx hy, Ne, ENNReal.ofReal_ne_top, not_false_iff]

/--
theorem `hasConstantSpeedOnWith_of_subsingleton` / 定理 `hasConstantSpeedOnWith_of_subsingleton`

English:
theorem hasConstantSpeedOnWith_of_subsingleton
  statement: (f : Real -> E) {s : Set Real} (hs : s.Subsingleton)
  proof: by
  rintro x hx y hy; cases hs hx hy
  rw [eVariationOn.subsingleton f (fun y hy z hz => hs hy.1 hz.1 : (s inter Icc x x).Subsingleton)]
  simp only [sub_self, mul_zero, ENNReal.ofReal_zero]

中文:
定理 hasConstantSpeedOnWith_of_subsingleton
  结论: (f : 实数 -> E) {s : 集合 实数} (hs : s.子单例)
  证明: by
  rintro x hx y hy; cases hs hx hy
  rw [eVariationOn.subsingleton f (fun y hy z hz => hs hy.1 hz.1 : (s inter Icc x x).Subsingleton)]
  simp only [sub_self, mul_zero, ENNReal.ofReal_zero]

Depends on / 依赖: ENNReal, ENNReal.ofReal_zero, Subsingleton, eVariationOn, eVariationOn.subsingleton, mul_zero, ofReal_zero, sub_self, subsingleton
-/
theorem hasConstantSpeedOnWith_of_subsingleton (f : Real -> E) {s : Set Real} (hs : s.Subsingleton)
    (l : Real>=0) : HasConstantSpeedOnWith f s l := by
  rintro x hx y hy; cases hs hx hy
  rw [eVariationOn.subsingleton f (fun y hy z hz => hs hy.1 hz.1 : (s inter Icc x x).Subsingleton)]
  simp only [sub_self, mul_zero, ENNReal.ofReal_zero]

/--
theorem `hasConstantSpeedOnWith_iff_ordered` / 定理 `hasConstantSpeedOnWith_iff_ordered`

English:
theorem hasConstantSpeedOnWith_iff_ordered
  proof: by
  refine ⟨fun h x xs y ys _ => h xs ys, fun h x xs y ys => ?_⟩
  rcases le_total x y with (xy | yx)
  · exact h xs ys xy
  · rw [eVariationOn.subsingleton, ENNReal.ofReal_of_nonpos]
    · exact mul_nonpos_of_nonneg_of_nonpos l.prop (sub_nonpos_of_le yx)
    · rintro z ⟨zs, xz, zy⟩ w ⟨ws, xw, wy⟩


中文:
定理 hasConstantSpeedOnWith_iff_ordered
  证明: by
  refine ⟨fun h x xs y ys _ => h xs ys, fun h x xs y ys => ?_⟩
  rcases le_total x y with (xy | yx)
  · exact h xs ys xy
  · rw [eVariationOn.subsingleton, ENNReal.ofReal_of_nonpos]
    · exact mul_nonpos_of_nonneg_of_nonpos l.prop (sub_nonpos_of_le yx)
    · rintro z ⟨zs, xz, zy⟩ w ⟨ws, xw, wy⟩


Depends on / 依赖: ENNReal, ENNReal.ofReal_of_nonpos, eVariationOn, eVariationOn.subsingleton, l.prop, le_antisymm, le_total, mul_nonpos_of_nonneg_of_nonpos, ofReal_of_nonpos, sub_nonpos_of_le, subsingleton, wy.trans, zy.trans
-/
theorem hasConstantSpeedOnWith_iff_ordered :
    HasConstantSpeedOnWith f s l ↔ forall ⦃x⦄ (_ : x in s) ⦃y⦄ (_ : y in s),
      x <= y -> eVariationOn f (s inter Icc x y) = ENNReal.ofReal (l * (y - x)) := by
  refine ⟨fun h x xs y ys _ => h xs ys, fun h x xs y ys => ?_⟩
  rcases le_total x y with (xy | yx)
  · exact h xs ys xy
  · rw [eVariationOn.subsingleton, ENNReal.ofReal_of_nonpos]
    · exact mul_nonpos_of_nonneg_of_nonpos l.prop (sub_nonpos_of_le yx)
    · rintro z ⟨zs, xz, zy⟩ w ⟨ws, xw, wy⟩
      cases le_antisymm (zy.trans yx) xz
      cases le_antisymm (wy.trans yx) xw
      rfl

/--
theorem `hasConstantSpeedOnWith_iff_variationOnFromTo_eq` / 定理 `hasConstantSpeedOnWith_iff_variationOnFromTo_eq`

English:
theorem hasConstantSpeedOnWith_iff_variationOnFromTo_eq
  proof: by
  constructor
  · rintro h; refine ⟨h.hasLocallyBoundedVariationOn, fun x xs y ys => ?_⟩
    rw [hasConstantSpeedOnWith_iff_ordered] at h
    rcases le_total x y with (xy | yx)
    · rw [variationOnFromTo.eq_of_le f s xy, h xs ys xy]
      exact ENNReal.toReal_ofReal (mul_nonneg l.prop (sub_nonne

中文:
定理 hasConstantSpeedOnWith_iff_variationOnFromTo_eq
  证明: by
  constructor
  · rintro h; refine ⟨h.hasLocallyBoundedVariationOn, fun x xs y ys => ?_⟩
    rw [hasConstantSpeedOnWith_iff_ordered] at h
    rcases le_total x y with (xy | yx)
    · rw [variationOnFromTo.eq_of_le f s xy, h xs ys xy]
      exact ENNReal.toReal_ofReal (mul_nonneg l.prop (sub_nonne

Depends on / 依赖: ENNReal, ENNReal.toReal_ofReal, NNReal, NNReal.val_eq_coe, eq_of_ge, eq_of_le, h.hasLocallyBoundedVariationOn, hasConstantSpeedOnWith_iff_ordered, hasLocallyBoundedVariationOn, l.prop, le_total, mul_nonneg, sub_nonneg, sub_nonneg.mpr, toReal_ofReal, val_eq_coe, variationOnFromTo, variationOnFromTo.eq_of_ge, variationOnFromTo.eq_of_le
-/
theorem hasConstantSpeedOnWith_iff_variationOnFromTo_eq :
    HasConstantSpeedOnWith f s l ↔ LocallyBoundedVariationOn f s ∧
      forall ⦃x⦄ (_ : x in s) ⦃y⦄ (_ : y in s), variationOnFromTo f s x y = l * (y - x) := by
  constructor
  · rintro h; refine ⟨h.hasLocallyBoundedVariationOn, fun x xs y ys => ?_⟩
    rw [hasConstantSpeedOnWith_iff_ordered] at h
    rcases le_total x y with (xy | yx)
    · rw [variationOnFromTo.eq_of_le f s xy, h xs ys xy]
      exact ENNReal.toReal_ofReal (mul_nonneg l.prop (sub_nonneg.mpr xy))
    · rw [variationOnFromTo.eq_of_ge f s yx, h ys xs yx]
      have := ENNReal.toReal_ofReal (mul_nonneg l.prop (sub_nonneg.mpr yx))
      simp_all only [NNReal.val_eq_coe]; ring
  · rw [hasConstantSpeedOnWith_iff_ordered]
    rintro h x xs y ys xy
    rw [← h.2 xs ys]; rw [variationOnFromTo.eq_of_le f s xy]; rw [ENNReal.ofReal_toReal (h.1 x y xs ys)]

/--
theorem `HasConstantSpeedOnWith.union` / 定理 `HasConstantSpeedOnWith.union`

English:
theorem HasConstantSpeedOnWith.union
  statement: {t : Set Real} (hfs : HasConstantSpeedOnWith f s l)
  proof: by
  rw [hasConstantSpeedOnWith_iff_ordered] at hfs hft ⊢
  rintro z (zs | zt) y (ys | yt) zy
  · have : (s union t) inter Icc z y = s inter Icc z y := by
      ext w; constructor
      · rintro ⟨ws | wt, zw, wy⟩
        · exact ⟨ws, zw, wy⟩
        · exact ⟨(le_antisymm (wy.trans (hs.2 ys)) (ht.2 w

中文:
定理 HasConstantSpeedOnWith.union
  结论: {t : 集合 实数} (hfs : HasConstantSpeedOnWith f s l)
  证明: by
  rw [hasConstantSpeedOnWith_iff_ordered] at hfs hft ⊢
  rintro z (zs | zt) y (ys | yt) zy
  · have : (s union t) inter Icc z y = s inter Icc z y := by
      ext w; constructor
      · rintro ⟨ws | wt, zw, wy⟩
        · exact ⟨ws, zw, wy⟩
        · exact ⟨(le_antisymm (wy.trans (hs.2 ys)) (ht.2 w

Depends on / 依赖: Or.inl, exacts, hasConstantSpeedOnWith_iff_ordered, le_antisymm, wy.trans
-/
theorem HasConstantSpeedOnWith.union {t : Set Real} (hfs : HasConstantSpeedOnWith f s l)
    (hft : HasConstantSpeedOnWith f t l) {x : Real} (hs : IsGreatest s x) (ht : IsLeast t x) :
    HasConstantSpeedOnWith f (s union t) l := by
  rw [hasConstantSpeedOnWith_iff_ordered] at hfs hft ⊢
  rintro z (zs | zt) y (ys | yt) zy
  · have : (s union t) inter Icc z y = s inter Icc z y := by
      ext w; constructor
      · rintro ⟨ws | wt, zw, wy⟩
        · exact ⟨ws, zw, wy⟩
        · exact ⟨(le_antisymm (wy.trans (hs.2 ys)) (ht.2 wt)).symm ▸ hs.1, zw, wy⟩
      · rintro ⟨ws, zwy⟩; exact ⟨Or.inl ws, zwy⟩
    rw [this]; rw [hfs zs ys zy]
  · have : (s union t) inter Icc z y = s inter Icc z x union t inter Icc x y := by
      ext w; constructor
      · rintro ⟨ws | wt, zw, wy⟩
        exacts [Or.inl ⟨ws, zw, hs.2 ws⟩, Or.inr ⟨wt, ht.2 wt, wy⟩]
      · rintro (⟨ws, zw, wx⟩ | ⟨wt, xw, wy⟩)
        exacts [⟨Or.inl ws, zw, wx.trans (ht.2 yt)⟩, ⟨Or.inr wt, (hs.2 zs).trans xw, wy⟩]
    rw [this]; rw [@eVariationOn.union _ _ _ _ f _ _ x]; rw [hfs zs hs.1 (hs.2 zs)]; rw [hft ht.1 yt (ht.2 yt)]
    · have q := ENNReal.ofReal_add (mul_nonneg l.prop (sub_nonneg.mpr (hs.2 zs)))
        (mul_nonneg l.prop (sub_nonneg.mpr (ht.2 yt)))
      simp only [NNReal.val_eq_coe] at q
      rw [← q]
      ring_nf
    exacts [⟨⟨hs.1, hs.2 zs, le_rfl⟩, fun w ⟨_, _, wx⟩ => wx⟩,
      ⟨⟨ht.1, le_rfl, ht.2 yt⟩, fun w ⟨_, xw, _⟩ => xw⟩]
  · cases le_antisymm zy ((hs.2 ys).trans (ht.2 zt))
    simp only [Icc_self, sub_self, mul_zero, ENNReal.ofReal_zero]
    exact eVariationOn.subsingleton _ fun _ ⟨_, uz⟩ _ ⟨_, vz⟩ => uz.trans vz.symm
  · have : (s union t) inter Icc z y = t inter Icc z y := by
      ext w; constructor
      · rintro ⟨ws | wt, zw, wy⟩
        · exact ⟨le_antisymm ((ht.2 zt).trans zw) (hs.2 ws) ▸ ht.1, zw, wy⟩
        · exact ⟨wt, zw, wy⟩
      · rintro ⟨wt, zwy⟩; exact ⟨Or.inr wt, zwy⟩
    rw [this]; rw [hft zt yt zy]

/--
theorem `HasConstantSpeedOnWith.Icc_Icc` / 定理 `HasConstantSpeedOnWith.Icc_Icc`

English:
theorem HasConstantSpeedOnWith.Icc_Icc
  statement: {x y z : Real} (hfs : HasConstantSpeedOnWith f (Icc x y) l)
  proof: by
  rcases le_total x y with (xy | yx)
  · rcases le_total y z with (yz | zy)
    · rw [← Set.Icc_union_Icc_eq_Icc xy yz]
      exact hfs.union hft (isGreatest_Icc xy) (isLeast_Icc yz)
    · rintro u ⟨xu, uz⟩ v ⟨xv, vz⟩
      rw [Icc_inter_Icc]; rw [sup_of_le_right xu]; rw [inf_of_le_right vz]; rw 

中文:
定理 HasConstantSpeedOnWith.Icc_Icc
  结论: {x y z : 实数} (hfs : HasConstantSpeedOnWith f (闭区间 x y) l)
  证明: by
  rcases le_total x y with (xy | yx)
  · rcases le_total y z with (yz | zy)
    · rw [← Set.Icc_union_Icc_eq_Icc xy yz]
      exact hfs.union hft (isGreatest_Icc xy) (isLeast_Icc yz)
    · rintro u ⟨xu, uz⟩ v ⟨xv, vz⟩
      rw [Icc_inter_Icc]; rw [sup_of_le_right xu]; rw [inf_of_le_right vz]; rw 

Depends on / 依赖: Icc_inter_Icc, Icc_union_Icc_eq_Icc, Set.Icc_union_Icc_eq_Icc, hfs.union, inf_of_le, inf_of_le_right, isGreatest_Icc, isLeast_Icc, le_total, sup_of_le_right, uz.trans, vz.trans
-/
theorem HasConstantSpeedOnWith.Icc_Icc {x y z : Real} (hfs : HasConstantSpeedOnWith f (Icc x y) l)
    (hft : HasConstantSpeedOnWith f (Icc y z) l) : HasConstantSpeedOnWith f (Icc x z) l := by
  rcases le_total x y with (xy | yx)
  · rcases le_total y z with (yz | zy)
    · rw [← Set.Icc_union_Icc_eq_Icc xy yz]
      exact hfs.union hft (isGreatest_Icc xy) (isLeast_Icc yz)
    · rintro u ⟨xu, uz⟩ v ⟨xv, vz⟩
      rw [Icc_inter_Icc]; rw [sup_of_le_right xu]; rw [inf_of_le_right vz]; rw [←
        hfs ⟨xu]; rw [uz.trans zy⟩ ⟨xv]; rw [vz.trans zy⟩]; rw [Icc_inter_Icc]; rw [sup_of_le_right xu]; rw [inf_of_le_right (vz.trans zy)]
  · rintro u ⟨xu, uz⟩ v ⟨xv, vz⟩
    rw [Icc_inter_Icc]; rw [sup_of_le_right xu]; rw [inf_of_le_right vz]; rw [←
      hft ⟨yx.trans xu]; rw [uz⟩ ⟨yx.trans xv]; rw [vz⟩]; rw [Icc_inter_Icc]; rw [sup_of_le_right (yx.trans xu)]; rw [inf_of_le_right vz]

/--
theorem `hasConstantSpeedOnWith_zero_iff` / 定理 `hasConstantSpeedOnWith_zero_iff`

English:
theorem hasConstantSpeedOnWith_zero_iff
  proof: by
  dsimp [HasConstantSpeedOnWith]
  simp only [zero_mul, ENNReal.ofReal_zero, ← eVariationOn.eq_zero_iff]
  constructor
  · by_contra! ⟨h, hfs⟩
    simp_rw [ne_eq, eVariationOn.eq_zero_iff] at hfs h
    push Not at hfs
    obtain ⟨x, xs, y, ys, hxy⟩ := hfs
    rcases le_total x y with (xy | yx)
  

中文:
定理 hasConstantSpeedOnWith_zero_iff
  证明: by
  dsimp [HasConstantSpeedOnWith]
  simp only [zero_mul, ENNReal.ofReal_zero, ← eVariationOn.eq_zero_iff]
  constructor
  · by_contra! ⟨h, hfs⟩
    simp_rw [ne_eq, eVariationOn.eq_zero_iff] at hfs h
    push Not at hfs
    obtain ⟨x, xs, y, ys, hxy⟩ := hfs
    rcases le_total x y with (xy | yx)
  

Depends on / 依赖: ENNReal, ENNReal.ofReal_zero, HasConstantSpeedOnWith, eVariationOn, eVariationOn.eq_zero_iff, eVariationOn.mono, edist_comm, eq_zero_iff, inter_subset_left, le_rfl, le_total, ne_eq, ofReal_zero, simp_rw, zero_mul
-/
theorem hasConstantSpeedOnWith_zero_iff :
    HasConstantSpeedOnWith f s 0 ↔ forallᵉ (x in s) (y in s), edist (f x) (f y) = 0 := by
  dsimp [HasConstantSpeedOnWith]
  simp only [zero_mul, ENNReal.ofReal_zero, ← eVariationOn.eq_zero_iff]
  constructor
  · by_contra! ⟨h, hfs⟩
    simp_rw [ne_eq, eVariationOn.eq_zero_iff] at hfs h
    push Not at hfs
    obtain ⟨x, xs, y, ys, hxy⟩ := hfs
    rcases le_total x y with (xy | yx)
    · exact hxy (h xs ys x ⟨xs, le_rfl, xy⟩ y ⟨ys, xy, le_rfl⟩)
    · rw [edist_comm] at hxy
      exact hxy (h ys xs y ⟨ys, le_rfl, yx⟩ x ⟨xs, yx, le_rfl⟩)
  · rintro h x _ y _
    simpa [h] using eVariationOn.mono (s := s) f inter_subset_left

/--
theorem `HasConstantSpeedOnWith.ratio` / 定理 `HasConstantSpeedOnWith.ratio`

English:
theorem HasConstantSpeedOnWith.ratio
  statement: {l' : Real>=0} (hl' : l' != 0) {φ : Real -> Real} (φm : MonotoneOn φ s)
  proof: by
  rintro y ys
  rw [← sub_eq_iff_eq_add]; rw [mul_comm]; rw [← mul_div_assoc]; rw [eq_div_iff (NNReal.coe_ne_zero.mpr hl')]
  rw [hasConstantSpeedOnWith_iff_variationOnFromTo_eq] at hf
  rw [hasConstantSpeedOnWith_iff_variationOnFromTo_eq] at hfφ
  symm
  calc
    (y - x) * l = l * (y - x) := by 

中文:
定理 HasConstantSpeedOnWith.ratio
  结论: {l' : 实数>=0} (hl' : l' != 0) {φ : 实数 -> 实数} (φm : MonotoneOn φ s)
  证明: by
  rintro y ys
  rw [← sub_eq_iff_eq_add]; rw [mul_comm]; rw [← mul_div_assoc]; rw [eq_div_iff (NNReal.coe_ne_zero.mpr hl')]
  rw [hasConstantSpeedOnWith_iff_variationOnFromTo_eq] at hf
  rw [hasConstantSpeedOnWith_iff_variationOnFromTo_eq] at hfφ
  symm
  calc
    (y - x) * l = l * (y - x) := by 

Depends on / 依赖: NNReal, NNReal.coe_ne_zero.mpr, coe_ne_zero, comp_eq_of_monotoneOn, eq_div_iff, hasConstantSpeedOnWith_iff_variationOnFromTo_eq, mul_comm, mul_div_assoc, sub_eq_iff_eq_add, variationOnFromTo, variationOnFromTo.comp_eq_of_monotoneOn
-/
theorem HasConstantSpeedOnWith.ratio {l' : Real>=0} (hl' : l' != 0) {φ : Real -> Real} (φm : MonotoneOn φ s)
    (hfφ : HasConstantSpeedOnWith (f ∘ φ) s l) (hf : HasConstantSpeedOnWith f (φ '' s) l') ⦃x : Real⦄
    (xs : x in s) : EqOn φ (fun y => l / l' * (y - x) + φ x) s := by
  rintro y ys
  rw [← sub_eq_iff_eq_add]; rw [mul_comm]; rw [← mul_div_assoc]; rw [eq_div_iff (NNReal.coe_ne_zero.mpr hl')]
  rw [hasConstantSpeedOnWith_iff_variationOnFromTo_eq] at hf
  rw [hasConstantSpeedOnWith_iff_variationOnFromTo_eq] at hfφ
  symm
  calc
    (y - x) * l = l * (y - x) := by rw [mul_comm]
    _ = variationOnFromTo (f ∘ φ) s x y := (hfφ.2 xs ys).symm
    _ = variationOnFromTo f (φ '' s) (φ x) (φ y) :=
      (variationOnFromTo.comp_eq_of_monotoneOn f φ φm xs ys)
    _ = l' * (φ y - φ x) := (hf.2 ⟨x, xs, rfl⟩ ⟨y, ys, rfl⟩)
    _ = (φ y - φ x) * l' := by rw [mul_comm]

/--
Definition of `HasUnitSpeedOn` / `HasUnitSpeedOn` 的定义

English:
definition HasUnitSpeedOn
  signature: (f : Real -> E) (s : Set Real)
  body: HasConstantSpeedOnWith f s 1

中文:
定义 HasUnitSpeedOn
  签名: (f : 实数 -> E) (s : 集合 实数)
  定义体: HasConstantSpeedOnWith f s 1

Depends on / 依赖: HasConstantSpeedOnWith
-/
def HasUnitSpeedOn (f : Real -> E) (s : Set Real) :=
  HasConstantSpeedOnWith f s 1

/--
theorem `HasUnitSpeedOn.union` / 定理 `HasUnitSpeedOn.union`

English:
theorem HasUnitSpeedOn.union
  statement: {t : Set Real} {x : Real} (hfs : HasUnitSpeedOn f s)
  proof: HasConstantSpeedOnWith.union hfs hft hs ht

中文:
定理 HasUnitSpeedOn.union
  结论: {t : 集合 实数} {x : 实数} (hfs : HasUnitSpeedOn f s)
  证明: HasConstantSpeedOnWith.union hfs hft hs ht

Depends on / 依赖: HasConstantSpeedOnWith, HasConstantSpeedOnWith.union
-/
theorem HasUnitSpeedOn.union {t : Set Real} {x : Real} (hfs : HasUnitSpeedOn f s)
    (hft : HasUnitSpeedOn f t) (hs : IsGreatest s x) (ht : IsLeast t x) :
    HasUnitSpeedOn f (s union t) :=
  HasConstantSpeedOnWith.union hfs hft hs ht

/--
theorem `HasUnitSpeedOn.Icc_Icc` / 定理 `HasUnitSpeedOn.Icc_Icc`

English:
theorem HasUnitSpeedOn.Icc_Icc
  statement: {x y z : Real} (hfs : HasUnitSpeedOn f (Icc x y))
  proof: HasConstantSpeedOnWith.Icc_Icc hfs hft

中文:
定理 HasUnitSpeedOn.Icc_Icc
  结论: {x y z : 实数} (hfs : HasUnitSpeedOn f (闭区间 x y))
  证明: HasConstantSpeedOnWith.Icc_Icc hfs hft

Depends on / 依赖: HasConstantSpeedOnWith, HasConstantSpeedOnWith.Icc_Icc, Icc_Icc
-/
theorem HasUnitSpeedOn.Icc_Icc {x y z : Real} (hfs : HasUnitSpeedOn f (Icc x y))
    (hft : HasUnitSpeedOn f (Icc y z)) : HasUnitSpeedOn f (Icc x z) :=
  HasConstantSpeedOnWith.Icc_Icc hfs hft

/--
theorem `unique_unit_speed` / 定理 `unique_unit_speed`

English:
theorem unique_unit_speed
  statement: {φ : Real -> Real} (φm : MonotoneOn φ s) (hfφ : HasUnitSpeedOn (f ∘ φ) s)
  proof: by
  dsimp only [HasUnitSpeedOn] at hf hfφ
  convert HasConstantSpeedOnWith.ratio one_ne_zero φm hfφ hf xs
  simp

中文:
定理 unique_unit_speed
  结论: {φ : 实数 -> 实数} (φm : MonotoneOn φ s) (hfφ : HasUnitSpeedOn (f ∘ φ) s)
  证明: by
  dsimp only [HasUnitSpeedOn] at hf hfφ
  convert HasConstantSpeedOnWith.ratio one_ne_zero φm hfφ hf xs
  simp

Depends on / 依赖: HasConstantSpeedOnWith, HasConstantSpeedOnWith.ratio, HasUnitSpeedOn, convert, one_ne_zero
-/
theorem unique_unit_speed {φ : Real -> Real} (φm : MonotoneOn φ s) (hfφ : HasUnitSpeedOn (f ∘ φ) s)
    (hf : HasUnitSpeedOn f (φ '' s)) ⦃x : Real⦄ (xs : x in s) : EqOn φ (fun y => y - x + φ x) s := by
  dsimp only [HasUnitSpeedOn] at hf hfφ
  convert HasConstantSpeedOnWith.ratio one_ne_zero φm hfφ hf xs
  simp

/--
theorem `unique_unit_speed_on_Icc_zero` / 定理 `unique_unit_speed_on_Icc_zero`

English:
theorem unique_unit_speed_on_Icc_zero
  statement: {s t : Real} (hs : 0 <= s) (ht : 0 <= t) {φ : Real -> Real}
  proof: by
  rw [← φst] at hf
  convert unique_unit_speed φm hfφ hf ⟨le_rfl, hs⟩
  have : φ 0 = 0 := by
    have hm : 0 in φ '' Icc 0 s := by simp only [φst, ht, mem_Icc, le_refl, and_self]
    obtain ⟨x, xs, hx⟩ := hm
    apply le_antisymm ((φm ⟨le_rfl, hs⟩ xs xs.1).trans_eq hx) _
    have := φst ▸ mapsTo_

中文:
定理 unique_unit_speed_on_Icc_zero
  结论: {s t : 实数} (hs : 0 <= s) (ht : 0 <= t) {φ : 实数 -> 实数}
  证明: by
  rw [← φst] at hf
  convert unique_unit_speed φm hfφ hf ⟨le_rfl, hs⟩
  have : φ 0 = 0 := by
    have hm : 0 in φ '' Icc 0 s := by simp only [φst, ht, mem_Icc, le_refl, and_self]
    obtain ⟨x, xs, hx⟩ := hm
    apply le_antisymm ((φm ⟨le_rfl, hs⟩ xs xs.1).trans_eq hx) _
    have := φst ▸ mapsTo_

Depends on / 依赖: add_zero, and_self, convert, le_antisymm, le_refl, le_rfl, mapsTo_image, mem_Icc, mem_Icc.mp, trans_eq, tsub_zero, unique_unit_speed
-/
theorem unique_unit_speed_on_Icc_zero {s t : Real} (hs : 0 <= s) (ht : 0 <= t) {φ : Real -> Real}
    (φm : MonotoneOn φ <| Icc 0 s) (φst : φ '' Icc 0 s = Icc 0 t)
    (hfφ : HasUnitSpeedOn (f ∘ φ) (Icc 0 s)) (hf : HasUnitSpeedOn f (Icc 0 t)) :
    EqOn φ id (Icc 0 s) := by
  rw [← φst] at hf
  convert unique_unit_speed φm hfφ hf ⟨le_rfl, hs⟩
  have : φ 0 = 0 := by
    have hm : 0 in φ '' Icc 0 s := by simp only [φst, ht, mem_Icc, le_refl, and_self]
    obtain ⟨x, xs, hx⟩ := hm
    apply le_antisymm ((φm ⟨le_rfl, hs⟩ xs xs.1).trans_eq hx) _
    have := φst ▸ mapsTo_image φ (Icc 0 s)
    exact (mem_Icc.mp (@this 0 (by rw [mem_Icc]; exact ⟨le_rfl, hs⟩))).1
  simp only [tsub_zero, this, add_zero]
  rfl

/--
Definition of `naturalParameterization` / `naturalParameterization` 的定义

English:
definition naturalParameterization
  signature: (f : α -> E) (s : Set α) (a : α)
  body: f ∘ @Function.invFunOn _ _ ⟨a⟩ (variationOnFromTo f s a) s

中文:
定义 naturalParameterization
  签名: (f : α -> E) (s : 集合 α) (a : α)
  定义体: f ∘ @Function.invFunOn _ _ ⟨a⟩ (variationOnFromTo f s a) s

Depends on / 依赖: Function, Function.invFunOn, invFunOn, variationOnFromTo
-/
noncomputable def naturalParameterization (f : α -> E) (s : Set α) (a : α) : Real -> E :=
  f ∘ @Function.invFunOn _ _ ⟨a⟩ (variationOnFromTo f s a) s

/--
theorem `edist_naturalParameterization_eq_zero` / 定理 `edist_naturalParameterization_eq_zero`

English:
theorem edist_naturalParameterization_eq_zero
  statement: {f : α -> E} {s : Set α}
  proof: by
  dsimp only [naturalParameterization]
  have : Nonempty α := ⟨a⟩
  obtain ⟨cs, hc⟩ := Function.invFunOn_pos (b := variationOnFromTo f s a b) ⟨b, bs, rfl⟩
  rw [variationOnFromTo.eq_left_iff hf as cs bs] at hc
  apply variationOnFromTo.edist_zero_of_eq_zero hf cs bs hc

中文:
定理 edist_naturalParameterization_eq_zero
  结论: {f : α -> E} {s : 集合 α}
  证明: by
  dsimp only [naturalParameterization]
  have : Nonempty α := ⟨a⟩
  obtain ⟨cs, hc⟩ := Function.invFunOn_pos (b := variationOnFromTo f s a b) ⟨b, bs, rfl⟩
  rw [variationOnFromTo.eq_left_iff hf as cs bs] at hc
  apply variationOnFromTo.edist_zero_of_eq_zero hf cs bs hc

Depends on / 依赖: Function, Function.invFunOn_pos, Nonempty, edist_zero_of_eq_zero, eq_left_iff, invFunOn_pos, naturalParameterization, variationOnFromTo, variationOnFromTo.edist_zero_of_eq_zero, variationOnFromTo.eq_left_iff
-/
theorem edist_naturalParameterization_eq_zero {f : α -> E} {s : Set α}
    (hf : LocallyBoundedVariationOn f s) {a : α} (as : a in s) {b : α} (bs : b in s) :
    edist (naturalParameterization f s a (variationOnFromTo f s a b)) (f b) = 0 := by
  dsimp only [naturalParameterization]
  have : Nonempty α := ⟨a⟩
  obtain ⟨cs, hc⟩ := Function.invFunOn_pos (b := variationOnFromTo f s a b) ⟨b, bs, rfl⟩
  rw [variationOnFromTo.eq_left_iff hf as cs bs] at hc
  apply variationOnFromTo.edist_zero_of_eq_zero hf cs bs hc

/--
theorem `has_unit_speed_naturalParameterization` / 定理 `has_unit_speed_naturalParameterization`

English:
theorem has_unit_speed_naturalParameterization
  statement: (f : α -> E) {s : Set α}
  proof: by
  dsimp only [HasUnitSpeedOn]
  rw [hasConstantSpeedOnWith_iff_ordered]
  rintro _ ⟨b, bs, rfl⟩ _ ⟨c, cs, rfl⟩ h
  rcases le_total c b with (cb | bc)
  · rw [NNReal.coe_one, one_mul, le_antisymm h (variationOnFromTo.monotoneOn hf as cs bs cb),
      sub_self, ENNReal.ofReal_zero, Icc_self, eVaria

中文:
定理 has_unit_speed_naturalParameterization
  结论: (f : α -> E) {s : 集合 α}
  证明: by
  dsimp only [HasUnitSpeedOn]
  rw [hasConstantSpeedOnWith_iff_ordered]
  rintro _ ⟨b, bs, rfl⟩ _ ⟨c, cs, rfl⟩ h
  rcases le_total c b with (cb | bc)
  · rw [NNReal.coe_one, one_mul, le_antisymm h (variationOnFromTo.monotoneOn hf as cs bs cb),
      sub_self, ENNReal.ofReal_zero, Icc_self, eVaria

Depends on / 依赖: ENNReal, ENNReal.ofReal_zero, HasUnitSpeedOn, Icc_self, NNReal, NNReal.coe_one, add_comm, coe_one, eVariationOn, eVariationOn.subsingleton, eq_neg_swap, hasConstantSpeedOnWith_iff_ordered, le_antisymm, le_total, monotoneOn, neg_neg, ofReal_zero, one_mul, sub_eq_add_neg, sub_self
-/
theorem has_unit_speed_naturalParameterization (f : α -> E) {s : Set α}
    (hf : LocallyBoundedVariationOn f s) {a : α} (as : a in s) :
    HasUnitSpeedOn (naturalParameterization f s a) (variationOnFromTo f s a '' s) := by
  dsimp only [HasUnitSpeedOn]
  rw [hasConstantSpeedOnWith_iff_ordered]
  rintro _ ⟨b, bs, rfl⟩ _ ⟨c, cs, rfl⟩ h
  rcases le_total c b with (cb | bc)
  · rw [NNReal.coe_one, one_mul, le_antisymm h (variationOnFromTo.monotoneOn hf as cs bs cb),
      sub_self, ENNReal.ofReal_zero, Icc_self, eVariationOn.subsingleton]
    exact fun x hx y hy => hx.2.trans hy.2.symm
  · rw [NNReal.coe_one, one_mul, sub_eq_add_neg, variationOnFromTo.eq_neg_swap, neg_neg, add_comm,
      variationOnFromTo.add hf bs as cs, ← variationOnFromTo.eq_neg_swap f]
    rw [←
      eVariationOn.comp_inter_Icc_eq_of_monotoneOn (naturalParameterization f s a) _
        (variationOnFromTo.monotoneOn hf as) bs cs]
    rw [@eVariationOn.eq_of_edist_zero_on _ _ _ _ _ f]
    · rw [variationOnFromTo.eq_of_le _ _ bc, ENNReal.ofReal_toReal (hf b c bs cs)]
    · rintro x ⟨xs, _, _⟩
      exact edist_naturalParameterization_eq_zero hf as xs
