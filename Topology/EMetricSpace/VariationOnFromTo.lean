/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# Signed variation

We define `variationOnFromTo f s a b : ℝ` as the signed variation of `f` between `a` and `b`, i.e.,
its variation if `a ≤ b`, and its opposite otherwise. We establish basic properties of this notion,
and use it to show that a bounded variation real function is the difference of two monotone
functions.
 -/

@[expose] public section

open scoped ENNReal Topology
open Set Filter

variable {α : Type*} [LinearOrder α] {E : Type*} [PseudoEMetricSpace E]

/--
Definition of `variationOnFromTo` / `variationOnFromTo` 的定义

English:
definition variationOnFromTo
  signature: (f : α -> E) (s : Set α) (a b : α)
  body: if a <= b then (eVariationOn f (s inter Icc a b)).toReal else -(eVariationOn f (s inter Icc b a)).toReal

中文:
定义 variationOnFromTo
  签名: (f : α -> E) (s : 集合 α) (a b : α)
  定义体: if a <= b then (eVariationOn f (s inter Icc a b)).toReal else -(eVariationOn f (s inter Icc b a)).toReal

Depends on / 依赖: eVariationOn, toReal
-/
noncomputable def variationOnFromTo (f : α -> E) (s : Set α) (a b : α) : Real :=
  if a <= b then (eVariationOn f (s inter Icc a b)).toReal else -(eVariationOn f (s inter Icc b a)).toReal

namespace variationOnFromTo

variable (f : α -> E) (s : Set α)

/--
theorem `self` / 定理 `self`

English:
theorem self
  given: (a : α)
  statement: variationOnFromTo f s a a = 0
  proof: by
  dsimp only [variationOnFromTo]
  rw [if_pos le_rfl]; rw [Icc_self]; rw [eVariationOn.subsingleton]; rw [ENNReal.toReal_zero]
  exact fun x hx y hy => hx.2.trans hy.2.symm

中文:
定理 self
  条件: (a : α)
  结论: variationOnFromTo f s a a = 0
  证明: by
  dsimp only [variationOnFromTo]
  rw [if_pos le_rfl]; rw [Icc_self]; rw [eVariationOn.subsingleton]; rw [ENNReal.toReal_zero]
  exact fun x hx y hy => hx.2.trans hy.2.symm
-/
protected theorem self (a : α) : variationOnFromTo f s a a = 0 := by
  dsimp only [variationOnFromTo]
  rw [if_pos le_rfl]; rw [Icc_self]; rw [eVariationOn.subsingleton]; rw [ENNReal.toReal_zero]
  exact fun x hx y hy => hx.2.trans hy.2.symm

/--
theorem `nonneg_of_le` / 定理 `nonneg_of_le`

English:
theorem nonneg_of_le
  given: {a b : α} (h : a <= b)
  statement: 0 <= variationOnFromTo f s a b
  proof: by
  simp only [variationOnFromTo, if_pos h, ENNReal.toReal_nonneg]

中文:
定理 nonneg_of_le
  条件: {a b : α} (h : a <= b)
  结论: 0 <= variationOnFromTo f s a b
  证明: by
  simp only [variationOnFromTo, if_pos h, ENNReal.toReal_nonneg]
-/
protected theorem nonneg_of_le {a b : α} (h : a <= b) : 0 <= variationOnFromTo f s a b := by
  simp only [variationOnFromTo, if_pos h, ENNReal.toReal_nonneg]

/--
theorem `eq_neg_swap` / 定理 `eq_neg_swap`

English:
theorem eq_neg_swap
  given: (a b : α)
  proof: by
  rcases lt_trichotomy a b with (ab | rfl | ba)
  · simp only [variationOnFromTo, if_pos ab.le, if_neg ab.not_ge, neg_neg]
  · simp only [variationOnFromTo.self, neg_zero]
  · simp only [variationOnFromTo, if_pos ba.le, if_neg ba.not_ge]

中文:
定理 eq_neg_swap
  条件: (a b : α)
  证明: by
  rcases lt_trichotomy a b with (ab | rfl | ba)
  · simp only [variationOnFromTo, if_pos ab.le, if_neg ab.not_ge, neg_neg]
  · simp only [variationOnFromTo.self, neg_zero]
  · simp only [variationOnFromTo, if_pos ba.le, if_neg ba.not_ge]
-/
protected theorem eq_neg_swap (a b : α) :
    variationOnFromTo f s a b = -variationOnFromTo f s b a := by
  rcases lt_trichotomy a b with (ab | rfl | ba)
  · simp only [variationOnFromTo, if_pos ab.le, if_neg ab.not_ge, neg_neg]
  · simp only [variationOnFromTo.self, neg_zero]
  · simp only [variationOnFromTo, if_pos ba.le, if_neg ba.not_ge]

/--
theorem `nonpos_of_ge` / 定理 `nonpos_of_ge`

English:
theorem nonpos_of_ge
  given: {a b : α} (h : b <= a)
  statement: variationOnFromTo f s a b <= 0
  proof: by
  rw [variationOnFromTo.eq_neg_swap]
  exact neg_nonpos_of_nonneg (variationOnFromTo.nonneg_of_le f s h)

中文:
定理 nonpos_of_ge
  条件: {a b : α} (h : b <= a)
  结论: variationOnFromTo f s a b <= 0
  证明: by
  rw [variationOnFromTo.eq_neg_swap]
  exact neg_nonpos_of_nonneg (variationOnFromTo.nonneg_of_le f s h)
-/
protected theorem nonpos_of_ge {a b : α} (h : b <= a) : variationOnFromTo f s a b <= 0 := by
  rw [variationOnFromTo.eq_neg_swap]
  exact neg_nonpos_of_nonneg (variationOnFromTo.nonneg_of_le f s h)

variable {f s} in
/--
theorem `abs_le_eVariationOn` / 定理 `abs_le_eVariationOn`

English:
theorem abs_le_eVariationOn
  given: (hf : BoundedVariationOn f s) {a b : α}
  proof: by
  by_cases hab : a <= b
  · simp only [variationOnFromTo, hab, ↓reduceIte, ENNReal.abs_toReal]
    exact ENNReal.toReal_mono hf (eVariationOn.mono _ inter_subset_left)
  · simp only [variationOnFromTo, hab, ↓reduceIte, abs_neg, ENNReal.abs_toReal]
    exact ENNReal.toReal_mono hf (eVariationOn.mo

中文:
定理 abs_le_eVariationOn
  条件: (hf : BoundedVariationOn f s) {a b : α}
  证明: by
  by_cases hab : a <= b
  · simp only [variationOnFromTo, hab, ↓reduceIte, ENNReal.abs_toReal]
    exact ENNReal.toReal_mono hf (eVariationOn.mono _ inter_subset_left)
  · simp only [variationOnFromTo, hab, ↓reduceIte, abs_neg, ENNReal.abs_toReal]
    exact ENNReal.toReal_mono hf (eVariationOn.mo

Depends on / 依赖: ENNReal, ENNReal.abs_toReal, ENNReal.toReal_mono, abs_neg, abs_toReal, eVariationOn, eVariationOn.mono, inter_subset_left, reduceIte, toReal_mono, variationOnFromTo
-/
theorem abs_le_eVariationOn (hf : BoundedVariationOn f s) {a b : α} :
    |variationOnFromTo f s a b| <= (eVariationOn f s).toReal := by
  by_cases hab : a <= b
  · simp only [variationOnFromTo, hab, ↓reduceIte, ENNReal.abs_toReal]
    exact ENNReal.toReal_mono hf (eVariationOn.mono _ inter_subset_left)
  · simp only [variationOnFromTo, hab, ↓reduceIte, abs_neg, ENNReal.abs_toReal]
    exact ENNReal.toReal_mono hf (eVariationOn.mono _ inter_subset_left)

/--
theorem `eq_of_le` / 定理 `eq_of_le`

English:
theorem eq_of_le
  given: {a b : α} (h : a <= b)
  proof: if_pos h

中文:
定理 eq_of_le
  条件: {a b : α} (h : a <= b)
  证明: if_pos h
-/
protected theorem eq_of_le {a b : α} (h : a <= b) :
    variationOnFromTo f s a b = (eVariationOn f (s inter Icc a b)).toReal :=
  if_pos h

/--
theorem `eq_of_ge` / 定理 `eq_of_ge`

English:
theorem eq_of_ge
  given: {a b : α} (h : b <= a)
  proof: by
  rw [variationOnFromTo.eq_neg_swap]; rw [neg_inj]; rw [variationOnFromTo.eq_of_le f s h]

中文:
定理 eq_of_ge
  条件: {a b : α} (h : b <= a)
  证明: by
  rw [variationOnFromTo.eq_neg_swap]; rw [neg_inj]; rw [variationOnFromTo.eq_of_le f s h]
-/
protected theorem eq_of_ge {a b : α} (h : b <= a) :
    variationOnFromTo f s a b = -(eVariationOn f (s inter Icc b a)).toReal := by
  rw [variationOnFromTo.eq_neg_swap]; rw [neg_inj]; rw [variationOnFromTo.eq_of_le f s h]

/--
theorem `add` / 定理 `add`

English:
theorem add
  statement: {f : α -> E} {s : Set α} (hf : LocallyBoundedVariationOn f s) {a b c : α}
  proof: by
  symm
  refine additive_of_total (· <= · : α -> α -> Prop) (variationOnFromTo f s) (· in s) ?_ ?_ ha hb hc
  · rintro x y _xs _ys
    simp only [variationOnFromTo.eq_neg_swap f s y x, add_neg_cancel]
  · rintro x y z xy yz xs ys zs
    rw [variationOnFromTo.eq_of_le f s xy]; rw [variationOnFromT

中文:
定理 add
  结论: {f : α -> E} {s : 集合 α} (hf : LocallyBoundedVariationOn f s) {a b c : α}
  证明: by
  symm
  refine additive_of_total (· <= · : α -> α -> Prop) (variationOnFromTo f s) (· in s) ?_ ?_ ha hb hc
  · rintro x y _xs _ys
    simp only [variationOnFromTo.eq_neg_swap f s y x, add_neg_cancel]
  · rintro x y z xy yz xs ys zs
    rw [variationOnFromTo.eq_of_le f s xy]; rw [variationOnFromT
-/
protected theorem add {f : α -> E} {s : Set α} (hf : LocallyBoundedVariationOn f s) {a b c : α}
    (ha : a in s) (hb : b in s) (hc : c in s) :
    variationOnFromTo f s a b + variationOnFromTo f s b c = variationOnFromTo f s a c := by
  symm
  refine additive_of_total (· <= · : α -> α -> Prop) (variationOnFromTo f s) (· in s) ?_ ?_ ha hb hc
  · rintro x y _xs _ys
    simp only [variationOnFromTo.eq_neg_swap f s y x, add_neg_cancel]
  · rintro x y z xy yz xs ys zs
    rw [variationOnFromTo.eq_of_le f s xy]; rw [variationOnFromTo.eq_of_le f s yz]; rw [variationOnFromTo.eq_of_le f s (xy.trans yz)]; rw [← ENNReal.toReal_add (hf x y xs ys) (hf y z ys zs)]; rw [eVariationOn.Icc_add_Icc f xy yz ys]

/--
theorem `sub_right` / 定理 `sub_right`

English:
theorem sub_right
  statement: {f : α -> E} {s : Set α} (hf : LocallyBoundedVariationOn f s) {a b c : α}
  proof: by
  rw [← variationOnFromTo.add hf ha hc hb]; rw [add_sub_cancel_left]

中文:
定理 sub_right
  结论: {f : α -> E} {s : 集合 α} (hf : LocallyBoundedVariationOn f s) {a b c : α}
  证明: by
  rw [← variationOnFromTo.add hf ha hc hb]; rw [add_sub_cancel_left]
-/
protected theorem sub_right {f : α -> E} {s : Set α} (hf : LocallyBoundedVariationOn f s) {a b c : α}
    (ha : a in s) (hb : b in s) (hc : c in s) :
    variationOnFromTo f s a b - variationOnFromTo f s a c = variationOnFromTo f s c b := by
  rw [← variationOnFromTo.add hf ha hc hb]; rw [add_sub_cancel_left]

/--
theorem `sub_left` / 定理 `sub_left`

English:
theorem sub_left
  statement: {f : α -> E} {s : Set α} (hf : LocallyBoundedVariationOn f s) {a b c : α}
  proof: by
  rw [← variationOnFromTo.add hf ha hc hb]; rw [add_sub_cancel_right]

中文:
定理 sub_left
  结论: {f : α -> E} {s : 集合 α} (hf : LocallyBoundedVariationOn f s) {a b c : α}
  证明: by
  rw [← variationOnFromTo.add hf ha hc hb]; rw [add_sub_cancel_right]
-/
protected theorem sub_left {f : α -> E} {s : Set α} (hf : LocallyBoundedVariationOn f s) {a b c : α}
    (ha : a in s) (hb : b in s) (hc : c in s) :
    variationOnFromTo f s a b - variationOnFromTo f s c b = variationOnFromTo f s a c := by
  rw [← variationOnFromTo.add hf ha hc hb]; rw [add_sub_cancel_right]

variable {f s} in
/--
theorem `edist_zero_of_eq_zero` / 定理 `edist_zero_of_eq_zero`

English:
theorem edist_zero_of_eq_zero
  statement: (hf : LocallyBoundedVariationOn f s)
  proof: by
  wlog h' : a <= b
  · rw [edist_comm]
    apply this hf hb ha _ (le_of_not_ge h')
    rw [variationOnFromTo.eq_neg_swap]; rw [h]; rw [neg_zero]
  · rw [← nonpos_iff_eq_zero, ← ENNReal.ofReal_zero, ← h, variationOnFromTo.eq_of_le f s h',
      ENNReal.ofReal_toReal (hf a b ha hb)]
    apply eVari

中文:
定理 edist_zero_of_eq_zero
  结论: (hf : LocallyBoundedVariationOn f s)
  证明: by
  wlog h' : a <= b
  · rw [edist_comm]
    apply this hf hb ha _ (le_of_not_ge h')
    rw [variationOnFromTo.eq_neg_swap]; rw [h]; rw [neg_zero]
  · rw [← nonpos_iff_eq_zero, ← ENNReal.ofReal_zero, ← h, variationOnFromTo.eq_of_le f s h',
      ENNReal.ofReal_toReal (hf a b ha hb)]
    apply eVari
-/
protected theorem edist_zero_of_eq_zero (hf : LocallyBoundedVariationOn f s)
    {a b : α} (ha : a in s) (hb : b in s) (h : variationOnFromTo f s a b = 0) :
    edist (f a) (f b) = 0 := by
  wlog h' : a <= b
  · rw [edist_comm]
    apply this hf hb ha _ (le_of_not_ge h')
    rw [variationOnFromTo.eq_neg_swap]; rw [h]; rw [neg_zero]
  · rw [← nonpos_iff_eq_zero, ← ENNReal.ofReal_zero, ← h, variationOnFromTo.eq_of_le f s h',
      ENNReal.ofReal_toReal (hf a b ha hb)]
    apply eVariationOn.edist_le
    exacts [⟨ha, ⟨le_rfl, h'⟩⟩, ⟨hb, ⟨h', le_rfl⟩⟩]

/--
theorem `eq_left_iff` / 定理 `eq_left_iff`

English:
theorem eq_left_iff
  statement: {f : α -> E} {s : Set α} (hf : LocallyBoundedVariationOn f s)
  proof: by
  simp only [← variationOnFromTo.add hf ha hb hc, left_eq_add]

中文:
定理 eq_left_iff
  结论: {f : α -> E} {s : 集合 α} (hf : LocallyBoundedVariationOn f s)
  证明: by
  simp only [← variationOnFromTo.add hf ha hb hc, left_eq_add]
-/
protected theorem eq_left_iff {f : α -> E} {s : Set α} (hf : LocallyBoundedVariationOn f s)
    {a b c : α} (ha : a in s) (hb : b in s) (hc : c in s) :
    variationOnFromTo f s a b = variationOnFromTo f s a c ↔ variationOnFromTo f s b c = 0 := by
  simp only [← variationOnFromTo.add hf ha hb hc, left_eq_add]

/--
theorem `eq_zero_iff_of_le` / 定理 `eq_zero_iff_of_le`

English:
theorem eq_zero_iff_of_le
  statement: {f : α -> E} {s : Set α} (hf : LocallyBoundedVariationOn f s)
  proof: by
  rw [variationOnFromTo.eq_of_le _ _ ab]; rw [ENNReal.toReal_eq_zero_iff]; rw [or_iff_left (hf a b ha hb)]; rw [eVariationOn.eq_zero_iff]

中文:
定理 eq_zero_iff_of_le
  结论: {f : α -> E} {s : 集合 α} (hf : LocallyBoundedVariationOn f s)
  证明: by
  rw [variationOnFromTo.eq_of_le _ _ ab]; rw [ENNReal.toReal_eq_zero_iff]; rw [or_iff_left (hf a b ha hb)]; rw [eVariationOn.eq_zero_iff]
-/
protected theorem eq_zero_iff_of_le {f : α -> E} {s : Set α} (hf : LocallyBoundedVariationOn f s)
    {a b : α} (ha : a in s) (hb : b in s) (ab : a <= b) :
    variationOnFromTo f s a b = 0 ↔
      forall ⦃x⦄ (_hx : x in s inter Icc a b) ⦃y⦄ (_hy : y in s inter Icc a b), edist (f x) (f y) = 0 := by
  rw [variationOnFromTo.eq_of_le _ _ ab]; rw [ENNReal.toReal_eq_zero_iff]; rw [or_iff_left (hf a b ha hb)]; rw [eVariationOn.eq_zero_iff]

/--
theorem `eq_zero_iff_of_ge` / 定理 `eq_zero_iff_of_ge`

English:
theorem eq_zero_iff_of_ge
  statement: {f : α -> E} {s : Set α} (hf : LocallyBoundedVariationOn f s)
  proof: by
  rw [variationOnFromTo.eq_of_ge _ _ ba]; rw [neg_eq_zero]; rw [ENNReal.toReal_eq_zero_iff]; rw [or_iff_left (hf b a hb ha)]; rw [eVariationOn.eq_zero_iff]

中文:
定理 eq_zero_iff_of_ge
  结论: {f : α -> E} {s : 集合 α} (hf : LocallyBoundedVariationOn f s)
  证明: by
  rw [variationOnFromTo.eq_of_ge _ _ ba]; rw [neg_eq_zero]; rw [ENNReal.toReal_eq_zero_iff]; rw [or_iff_left (hf b a hb ha)]; rw [eVariationOn.eq_zero_iff]
-/
protected theorem eq_zero_iff_of_ge {f : α -> E} {s : Set α} (hf : LocallyBoundedVariationOn f s)
    {a b : α} (ha : a in s) (hb : b in s) (ba : b <= a) :
    variationOnFromTo f s a b = 0 ↔
      forall ⦃x⦄ (_hx : x in s inter Icc b a) ⦃y⦄ (_hy : y in s inter Icc b a), edist (f x) (f y) = 0 := by
  rw [variationOnFromTo.eq_of_ge _ _ ba]; rw [neg_eq_zero]; rw [ENNReal.toReal_eq_zero_iff]; rw [or_iff_left (hf b a hb ha)]; rw [eVariationOn.eq_zero_iff]

/--
theorem `eq_zero_iff` / 定理 `eq_zero_iff`

English:
theorem eq_zero_iff
  statement: {f : α -> E} {s : Set α} (hf : LocallyBoundedVariationOn f s) {a b : α}
  proof: by
  rcases le_total a b with (ab | ba)
  · rw [uIcc_of_le ab]
    exact variationOnFromTo.eq_zero_iff_of_le hf ha hb ab
  · rw [uIcc_of_ge ba]
    exact variationOnFromTo.eq_zero_iff_of_ge hf ha hb ba

中文:
定理 eq_zero_iff
  结论: {f : α -> E} {s : 集合 α} (hf : LocallyBoundedVariationOn f s) {a b : α}
  证明: by
  rcases le_total a b with (ab | ba)
  · rw [uIcc_of_le ab]
    exact variationOnFromTo.eq_zero_iff_of_le hf ha hb ab
  · rw [uIcc_of_ge ba]
    exact variationOnFromTo.eq_zero_iff_of_ge hf ha hb ba
-/
protected theorem eq_zero_iff {f : α -> E} {s : Set α} (hf : LocallyBoundedVariationOn f s) {a b : α}
    (ha : a in s) (hb : b in s) :
    variationOnFromTo f s a b = 0 ↔
      forall ⦃x⦄ (_hx : x in s inter uIcc a b) ⦃y⦄ (_hy : y in s inter uIcc a b), edist (f x) (f y) = 0 := by
  rcases le_total a b with (ab | ba)
  · rw [uIcc_of_le ab]
    exact variationOnFromTo.eq_zero_iff_of_le hf ha hb ab
  · rw [uIcc_of_ge ba]
    exact variationOnFromTo.eq_zero_iff_of_ge hf ha hb ba

variable {f} {s}

/--
theorem `monotoneOn` / 定理 `monotoneOn`

English:
theorem monotoneOn
  given: (hf : LocallyBoundedVariationOn f s) {a : α} (as : a in s)
  proof: by
  rintro b bs c cs bc
  rw [← variationOnFromTo.add hf as bs cs]
  exact le_add_of_nonneg_right (variationOnFromTo.nonneg_of_le f s bc)

中文:
定理 monotoneOn
  条件: (hf : LocallyBoundedVariationOn f s) {a : α} (as : a in s)
  证明: by
  rintro b bs c cs bc
  rw [← variationOnFromTo.add hf as bs cs]
  exact le_add_of_nonneg_right (variationOnFromTo.nonneg_of_le f s bc)
-/
protected theorem monotoneOn (hf : LocallyBoundedVariationOn f s) {a : α} (as : a in s) :
    MonotoneOn (variationOnFromTo f s a) s := by
  rintro b bs c cs bc
  rw [← variationOnFromTo.add hf as bs cs]
  exact le_add_of_nonneg_right (variationOnFromTo.nonneg_of_le f s bc)

/--
theorem `antitoneOn` / 定理 `antitoneOn`

English:
theorem antitoneOn
  given: (hf : LocallyBoundedVariationOn f s) {b : α} (bs : b in s)
  proof: by
  rintro a as c cs ac
  dsimp only
  rw [← variationOnFromTo.add hf as cs bs]
  exact le_add_of_nonneg_left (variationOnFromTo.nonneg_of_le f s ac)

中文:
定理 antitoneOn
  条件: (hf : LocallyBoundedVariationOn f s) {b : α} (bs : b in s)
  证明: by
  rintro a as c cs ac
  dsimp only
  rw [← variationOnFromTo.add hf as cs bs]
  exact le_add_of_nonneg_left (variationOnFromTo.nonneg_of_le f s ac)
-/
protected theorem antitoneOn (hf : LocallyBoundedVariationOn f s) {b : α} (bs : b in s) :
    AntitoneOn (fun a => variationOnFromTo f s a b) s := by
  rintro a as c cs ac
  dsimp only
  rw [← variationOnFromTo.add hf as cs bs]
  exact le_add_of_nonneg_left (variationOnFromTo.nonneg_of_le f s ac)

/--
lemma `abs_sub_le_sub_of_le` / 引理 `abs_sub_le_sub_of_le`

English:
lemma abs_sub_le_sub_of_le
  statement: {f : α -> Real} {s : Set α} (hf : LocallyBoundedVariationOn f s)
  proof: calc
  _ = dist (f b) (f c) := by rw [dist_comm, Real.dist_eq]
  _ <= variationOnFromTo f s b c := by
    rw [variationOnFromTo.eq_of_le f s bc]; rw [dist_edist]
    apply ENNReal.toReal_mono (hf b c bs cs)
    apply eVariationOn.edist_le f
    exacts [⟨bs, le_rfl, bc⟩, ⟨cs, bc, le_rfl⟩]
  _ = varia

中文:
引理 abs_sub_le_sub_of_le
  结论: {f : α -> 实数} {s : 集合 α} (hf : LocallyBoundedVariationOn f s)
  证明: calc
  _ = dist (f b) (f c) := by rw [dist_comm, Real.dist_eq]
  _ <= variationOnFromTo f s b c := by
    rw [variationOnFromTo.eq_of_le f s bc]; rw [dist_edist]
    apply ENNReal.toReal_mono (hf b c bs cs)
    apply eVariationOn.edist_le f
    exacts [⟨bs, le_rfl, bc⟩, ⟨cs, bc, le_rfl⟩]
  _ = varia
-/
lemma abs_sub_le_sub_of_le {f : α -> Real} {s : Set α} (hf : LocallyBoundedVariationOn f s)
    {a b c : α} (as : a in s) (bs : b in s) (cs : c in s) (bc : b <= c) :
    |f c - f b| <= variationOnFromTo f s a c - variationOnFromTo f s a b := calc
  _ = dist (f b) (f c) := by rw [dist_comm, Real.dist_eq]
  _ <= variationOnFromTo f s b c := by
    rw [variationOnFromTo.eq_of_le f s bc]; rw [dist_edist]
    apply ENNReal.toReal_mono (hf b c bs cs)
    apply eVariationOn.edist_le f
    exacts [⟨bs, le_rfl, bc⟩, ⟨cs, bc, le_rfl⟩]
  _ = variationOnFromTo f s a c - variationOnFromTo f s a b := by
    rw [← variationOnFromTo.add hf as bs cs]; rw [add_sub_cancel_left]

/--
theorem `add_self_monotoneOn` / 定理 `add_self_monotoneOn`

English:
theorem add_self_monotoneOn
  statement: {f : α -> Real} {s : Set α} (hf : LocallyBoundedVariationOn f s)
  proof: by
  rintro b bs c cs bc
  suffices f b - f c <= variationOnFromTo f s a c - variationOnFromTo f s a b by simp; linarith
  calc
    f b - f c <= |f c - f b| := by grw [le_abs_self (f b - f c), abs_sub_comm (f b) (f c)]
    _ <= variationOnFromTo f s a c - variationOnFromTo f s a b := abs_sub_le_sub_

中文:
定理 add_self_monotoneOn
  结论: {f : α -> 实数} {s : 集合 α} (hf : LocallyBoundedVariationOn f s)
  证明: by
  rintro b bs c cs bc
  suffices f b - f c <= variationOnFromTo f s a c - variationOnFromTo f s a b by simp; linarith
  calc
    f b - f c <= |f c - f b| := by grw [le_abs_self (f b - f c), abs_sub_comm (f b) (f c)]
    _ <= variationOnFromTo f s a c - variationOnFromTo f s a b := abs_sub_le_sub_
-/
protected theorem add_self_monotoneOn {f : α -> Real} {s : Set α} (hf : LocallyBoundedVariationOn f s)
    {a : α} (as : a in s) : MonotoneOn (variationOnFromTo f s a + f) s := by
  rintro b bs c cs bc
  suffices f b - f c <= variationOnFromTo f s a c - variationOnFromTo f s a b by simp; linarith
  calc
    f b - f c <= |f c - f b| := by grw [le_abs_self (f b - f c), abs_sub_comm (f b) (f c)]
    _ <= variationOnFromTo f s a c - variationOnFromTo f s a b := abs_sub_le_sub_of_le hf as bs cs bc

/--
theorem `sub_self_monotoneOn` / 定理 `sub_self_monotoneOn`

English:
theorem sub_self_monotoneOn
  statement: {f : α -> Real} {s : Set α} (hf : LocallyBoundedVariationOn f s)
  proof: by
  rintro b bs c cs bc
  rw [Pi.sub_apply]; rw [Pi.sub_apply]; rw [le_sub_iff_add_le]; rw [add_comm_sub]; rw [← le_sub_iff_add_le']
  calc
    f c - f b <= |f c - f b| := le_abs_self _
    _ <= variationOnFromTo f s a c - variationOnFromTo f s a b := abs_sub_le_sub_of_le hf as bs cs bc

中文:
定理 sub_self_monotoneOn
  结论: {f : α -> 实数} {s : 集合 α} (hf : LocallyBoundedVariationOn f s)
  证明: by
  rintro b bs c cs bc
  rw [Pi.sub_apply]; rw [Pi.sub_apply]; rw [le_sub_iff_add_le]; rw [add_comm_sub]; rw [← le_sub_iff_add_le']
  calc
    f c - f b <= |f c - f b| := le_abs_self _
    _ <= variationOnFromTo f s a c - variationOnFromTo f s a b := abs_sub_le_sub_of_le hf as bs cs bc
-/
protected theorem sub_self_monotoneOn {f : α -> Real} {s : Set α} (hf : LocallyBoundedVariationOn f s)
    {a : α} (as : a in s) : MonotoneOn (variationOnFromTo f s a - f) s := by
  rintro b bs c cs bc
  rw [Pi.sub_apply]; rw [Pi.sub_apply]; rw [le_sub_iff_add_le]; rw [add_comm_sub]; rw [← le_sub_iff_add_le']
  calc
    f c - f b <= |f c - f b| := le_abs_self _
    _ <= variationOnFromTo f s a c - variationOnFromTo f s a b := abs_sub_le_sub_of_le hf as bs cs bc

/--
theorem `comp_eq_of_monotoneOn` / 定理 `comp_eq_of_monotoneOn`

English:
theorem comp_eq_of_monotoneOn
  statement: {β : Type*} [LinearOrder β] (f : α -> E) {t : Set β}
  proof: by
  rcases le_total x y with (h | h)
  · rw [variationOnFromTo.eq_of_le _ _ h, variationOnFromTo.eq_of_le _ _ (hφ hx hy h),
      eVariationOn.comp_inter_Icc_eq_of_monotoneOn f φ hφ hx hy]
  · rw [variationOnFromTo.eq_of_ge _ _ h, variationOnFromTo.eq_of_ge _ _ (hφ hy hx h),
      eVariationOn.comp

中文:
定理 comp_eq_of_monotoneOn
  结论: {β : 类型} [线性序 β] (f : α -> E) {t : 集合 β}
  证明: by
  rcases le_total x y with (h | h)
  · rw [variationOnFromTo.eq_of_le _ _ h, variationOnFromTo.eq_of_le _ _ (hφ hx hy h),
      eVariationOn.comp_inter_Icc_eq_of_monotoneOn f φ hφ hx hy]
  · rw [variationOnFromTo.eq_of_ge _ _ h, variationOnFromTo.eq_of_ge _ _ (hφ hy hx h),
      eVariationOn.comp
-/
protected theorem comp_eq_of_monotoneOn {β : Type*} [LinearOrder β] (f : α -> E) {t : Set β}
    (φ : β -> α) (hφ : MonotoneOn φ t) {x y : β} (hx : x in t) (hy : y in t) :
    variationOnFromTo (f ∘ φ) t x y = variationOnFromTo f (φ '' t) (φ x) (φ y) := by
  rcases le_total x y with (h | h)
  · rw [variationOnFromTo.eq_of_le _ _ h, variationOnFromTo.eq_of_le _ _ (hφ hx hy h),
      eVariationOn.comp_inter_Icc_eq_of_monotoneOn f φ hφ hx hy]
  · rw [variationOnFromTo.eq_of_ge _ _ h, variationOnFromTo.eq_of_ge _ _ (hφ hy hx h),
      eVariationOn.comp_inter_Icc_eq_of_monotoneOn f φ hφ hy hx]

/--
theorem `tendsto_left` / 定理 `tendsto_left`

English:
theorem tendsto_left
  statement: {E : Type*} [PseudoMetricSpace E] [TopologicalSpace α] [OrderTopology α]
  proof: by
  suffices H : Tendsto (fun x => variationOnFromTo f s a b - variationOnFromTo f s x b)
      (𝓝[s inter Iio b] b) (𝓝 (variationOnFromTo f s a b - dist (f b) l)) by
    apply Tendsto.congr' _ H
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [variationOnFromTo.sub_left hf ha hb hx.1]
  

中文:
定理 tendsto_left
  结论: {E : 类型} [伪度量空间 E] [拓扑空间 α] [Order拓扑 α]
  证明: by
  suffices H : Tendsto (fun x => variationOnFromTo f s a b - variationOnFromTo f s x b)
      (𝓝[s inter Iio b] b) (𝓝 (variationOnFromTo f s a b - dist (f b) l)) by
    apply Tendsto.congr' _ H
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [variationOnFromTo.sub_left hf ha hb hx.1]
  

Depends on / 依赖: Tendsto, Tendsto.congr, Tendsto.const_sub, const_sub, eVariationOn, filter_upwards, self_mem_nhdsWithin, sub_left, toReal, variationOnFromTo, variationOnFromTo.sub_left
-/
theorem tendsto_left {E : Type*} [PseudoMetricSpace E] [TopologicalSpace α] [OrderTopology α]
    {f : α -> E} {l : E} {a b : α} (ha : a in s) (hb : b in s)
    (hf : LocallyBoundedVariationOn f s) (h'f : Tendsto f (𝓝[s inter Iio b] b) (𝓝 l)) :
    Tendsto (variationOnFromTo f s a) (𝓝[s inter Iio b] b)
      (𝓝 (variationOnFromTo f s a b - dist (f b) l)) := by
  suffices H : Tendsto (fun x => variationOnFromTo f s a b - variationOnFromTo f s x b)
      (𝓝[s inter Iio b] b) (𝓝 (variationOnFromTo f s a b - dist (f b) l)) by
    apply Tendsto.congr' _ H
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [variationOnFromTo.sub_left hf ha hb hx.1]
  apply Tendsto.const_sub
  suffices H : Tendsto (fun x => (eVariationOn f (s inter Icc x b)).toReal) (𝓝[s inter Iio b] b)
      (𝓝 (dist (f b) l)) by
    apply Tendsto.congr' _ H
    filter_upwards [self_mem_nhdsWithin] with x hx using by simp [variationOnFromTo, hx.2.le]
  rw [dist_edist]
  exact (ENNReal.tendsto_toReal (by simp)).comp (hf.tendsto_eVariationOn_Icc_left h'f hb)

/--
theorem `tendsto_right` / 定理 `tendsto_right`

English:
theorem tendsto_right
  statement: {E : Type*} [PseudoMetricSpace E] [TopologicalSpace α] [OrderTopology α]
  proof: by
  suffices H : Tendsto (fun x => variationOnFromTo f s a b + variationOnFromTo f s b x)
      (𝓝[s inter Ioi b] b) (𝓝 (variationOnFromTo f s a b + dist (f b) l)) by
    apply Tendsto.congr' _ H
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [variationOnFromTo.add hf ha hb hx.1]
  apply

中文:
定理 tendsto_right
  结论: {E : 类型} [伪度量空间 E] [拓扑空间 α] [Order拓扑 α]
  证明: by
  suffices H : Tendsto (fun x => variationOnFromTo f s a b + variationOnFromTo f s b x)
      (𝓝[s inter Ioi b] b) (𝓝 (variationOnFromTo f s a b + dist (f b) l)) by
    apply Tendsto.congr' _ H
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [variationOnFromTo.add hf ha hb hx.1]
  apply

Depends on / 依赖: Tendsto, Tendsto.congr, Tendsto.const_add, const_add, eVariationOn, filter_upwards, self_mem_nhdsWithin, toReal, variationOnFromTo, variationOnFromTo.add
-/
theorem tendsto_right {E : Type*} [PseudoMetricSpace E] [TopologicalSpace α] [OrderTopology α]
    {f : α -> E} {l : E} {a b : α} (ha : a in s) (hb : b in s)
    (hf : LocallyBoundedVariationOn f s) (h'f : Tendsto f (𝓝[s inter Ioi b] b) (𝓝 l)) :
    Tendsto (variationOnFromTo f s a) (𝓝[s inter Ioi b] b)
      (𝓝 (variationOnFromTo f s a b + dist (f b) l)) := by
  suffices H : Tendsto (fun x => variationOnFromTo f s a b + variationOnFromTo f s b x)
      (𝓝[s inter Ioi b] b) (𝓝 (variationOnFromTo f s a b + dist (f b) l)) by
    apply Tendsto.congr' _ H
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [variationOnFromTo.add hf ha hb hx.1]
  apply Tendsto.const_add
  suffices H : Tendsto (fun x => (eVariationOn f (s inter Icc b x)).toReal) (𝓝[s inter Ioi b] b)
      (𝓝 (dist (f b) l)) by
    apply Tendsto.congr' _ H
    filter_upwards [self_mem_nhdsWithin] with x hx using by simp [variationOnFromTo, hx.2.le]
  rw [dist_edist]
  exact (ENNReal.tendsto_toReal (by simp)).comp (hf.tendsto_eVariationOn_Icc_right h'f hb)

/--
theorem `leftLim_eq` / 定理 `leftLim_eq`

English:
theorem leftLim_eq
  statement: {E : Type*} [PseudoMetricSpace E] [CompleteSpace E]
  proof: by
  let : TopologicalSpace α := Preorder.topology α
  have : OrderTopology α := ⟨rfl⟩
  rcases eq_or_neBot (𝓝[<] b) with hb | hb
  · simp [leftLim_eq_of_eq_bot _ hb]
  apply leftLim_eq_of_tendsto
  have := variationOnFromTo.tendsto_left (f := f) (l := f.leftLim b) (mem_univ a) (mem_univ b)
    hf.l

中文:
定理 leftLim_eq
  结论: {E : 类型} [伪度量空间 E] [完备空间 E]
  证明: by
  let : TopologicalSpace α := Preorder.topology α
  have : OrderTopology α := ⟨rfl⟩
  rcases eq_or_neBot (𝓝[<] b) with hb | hb
  · simp [leftLim_eq_of_eq_bot _ hb]
  apply leftLim_eq_of_tendsto
  have := variationOnFromTo.tendsto_left (f := f) (l := f.leftLim b) (mem_univ a) (mem_univ b)
    hf.l

Depends on / 依赖: OrderTopology, Preorder, Preorder.topology, TopologicalSpace, eq_or_neBot, f.leftLim, hf.locallyBoundedVariationOn, hf.tendsto_leftLim, leftLim, leftLim_eq_of_eq_bot, leftLim_eq_of_tendsto, locallyBoundedVariationOn, mem_univ, tendsto_left, tendsto_leftLim, topology, univ_inter, variationOnFromTo, variationOnFromTo.tendsto_left
-/
theorem leftLim_eq {E : Type*} [PseudoMetricSpace E] [CompleteSpace E]
    {f : α -> E} {a b : α} (hf : BoundedVariationOn f univ) :
    (variationOnFromTo f univ a).leftLim b =
      variationOnFromTo f univ a b - dist (f b) (f.leftLim b) := by
  let : TopologicalSpace α := Preorder.topology α
  have : OrderTopology α := ⟨rfl⟩
  rcases eq_or_neBot (𝓝[<] b) with hb | hb
  · simp [leftLim_eq_of_eq_bot _ hb]
  apply leftLim_eq_of_tendsto
  have := variationOnFromTo.tendsto_left (f := f) (l := f.leftLim b) (mem_univ a) (mem_univ b)
    hf.locallyBoundedVariationOn
  simp only [univ_inter] at this
  exact this (hf.tendsto_leftLim _)

/--
theorem `rightLim_eq` / 定理 `rightLim_eq`

English:
theorem rightLim_eq
  statement: {E : Type*} [PseudoMetricSpace E] [CompleteSpace E]
  proof: by
  let : TopologicalSpace α := Preorder.topology α
  have : OrderTopology α := ⟨rfl⟩
  rcases eq_or_neBot (𝓝[>] b) with hb | hb
  · simp [rightLim_eq_of_eq_bot _ hb]
  apply rightLim_eq_of_tendsto
  have := variationOnFromTo.tendsto_right (f := f) (l := f.rightLim b) (mem_univ a) (mem_univ b)
    

中文:
定理 rightLim_eq
  结论: {E : 类型} [伪度量空间 E] [完备空间 E]
  证明: by
  let : TopologicalSpace α := Preorder.topology α
  have : OrderTopology α := ⟨rfl⟩
  rcases eq_or_neBot (𝓝[>] b) with hb | hb
  · simp [rightLim_eq_of_eq_bot _ hb]
  apply rightLim_eq_of_tendsto
  have := variationOnFromTo.tendsto_right (f := f) (l := f.rightLim b) (mem_univ a) (mem_univ b)
    

Depends on / 依赖: OrderTopology, Preorder, Preorder.topology, TopologicalSpace, eq_or_neBot, f.rightLim, hf.locallyBoundedVariationOn, hf.tendsto_rightLim, locallyBoundedVariationOn, mem_univ, rightLim, rightLim_eq_of_eq_bot, rightLim_eq_of_tendsto, tendsto_right, tendsto_rightLim, topology, univ_inter, variationOnFromTo, variationOnFromTo.tendsto_right
-/
theorem rightLim_eq {E : Type*} [PseudoMetricSpace E] [CompleteSpace E]
    {f : α -> E} {a b : α} (hf : BoundedVariationOn f univ) :
    (variationOnFromTo f univ a).rightLim b =
      variationOnFromTo f univ a b + dist (f b) (f.rightLim b) := by
  let : TopologicalSpace α := Preorder.topology α
  have : OrderTopology α := ⟨rfl⟩
  rcases eq_or_neBot (𝓝[>] b) with hb | hb
  · simp [rightLim_eq_of_eq_bot _ hb]
  apply rightLim_eq_of_tendsto
  have := variationOnFromTo.tendsto_right (f := f) (l := f.rightLim b) (mem_univ a) (mem_univ b)
    hf.locallyBoundedVariationOn
  simp only [univ_inter] at this
  exact this (hf.tendsto_rightLim _)

/--
theorem `_root_.BoundedVariationOn.continuousWithinAt_variationOnFromTo_Ici` / 定理 `_root_.BoundedVariationOn.continuousWithinAt_variationOnFromTo_Ici`

English:
theorem _root_.BoundedVariationOn.continuousWithinAt_variationOnFromTo_Ici
  proof: by
  have : variationOnFromTo f univ a =
      fun y => variationOnFromTo f univ a x + variationOnFromTo f univ x y := by
    ext y
    rw [variationOnFromTo.add hf.locallyBoundedVariationOn (mem_univ _) (mem_univ _) (mem_univ _)]
  rw [this]
  apply continuousWithinAt_const.add
  suffices H : Conti

中文:
定理 _root_.BoundedVariationOn.continuousWithinAt_variationOnFromTo_Ici
  证明: by
  have : variationOnFromTo f univ a =
      fun y => variationOnFromTo f univ a x + variationOnFromTo f univ x y := by
    ext y
    rw [variationOnFromTo.add hf.locallyBoundedVariationOn (mem_univ _) (mem_univ _) (mem_univ _)]
  rw [this]
  apply continuousWithinAt_const.add
  suffices H : Conti

Depends on / 依赖: ContinuousWithinAt, H.congr_of_mem, Icc_self, congr_of_mem, continuousWithinAt_const, continuousWithinAt_const.add, eVariationOn, eVariationOn.subsingl, hf.locallyBoundedVariationOn, locallyBoundedVariationOn, mem_univ, self_mem_Iic, subsingl, toReal, variationOnFromTo, variationOnFromTo.add
-/
theorem _root_.BoundedVariationOn.continuousWithinAt_variationOnFromTo_Ici
    [TopologicalSpace α] [OrderTopology α] (hf : BoundedVariationOn f univ) {a x : α}
    (hx : ContinuousWithinAt f (Ici x) x) :
    ContinuousWithinAt (variationOnFromTo f univ a) (Ici x) x := by
  have : variationOnFromTo f univ a =
      fun y => variationOnFromTo f univ a x + variationOnFromTo f univ x y := by
    ext y
    rw [variationOnFromTo.add hf.locallyBoundedVariationOn (mem_univ _) (mem_univ _) (mem_univ _)]
  rw [this]
  apply continuousWithinAt_const.add
  suffices H : ContinuousWithinAt (fun y => (eVariationOn f (univ inter Icc x y)).toReal) (Ici x) x from
    H.congr_of_mem (fun y hy => by grind [variationOnFromTo]) self_mem_Iic
  simp only [ContinuousWithinAt, Icc_self]
  rw [eVariationOn.subsingleton _ (by grind [Set.Subsingleton])]
  apply (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
  apply Tendsto.mono_left _ (nhdsWithin_mono _ (subset_univ _))
  exact hf.tendsto_eVariationOn_Icc_zero_right _ (by simpa using hx)

/--
theorem `_root_.BoundedVariationOn.continuousWithinAt_variationOnFromTo_rightLim_Ici` / 定理 `_root_.BoundedVariationOn.continuousWithinAt_variationOnFromTo_rightLim_Ici`

English:
theorem _root_.BoundedVariationOn.continuousWithinAt_variationOnFromTo_rightLim_Ici
  proof: hf.rightLim.continuousWithinAt_variationOnFromTo_Ici hf.continuousWithinAt_rightLim

中文:
定理 _root_.BoundedVariationOn.continuousWithinAt_variationOnFromTo_rightLim_Ici
  证明: hf.rightLim.continuousWithinAt_variationOnFromTo_Ici hf.continuousWithinAt_rightLim

Depends on / 依赖: continuousWithinAt_rightLim, continuousWithinAt_variationOnFromTo_Ici, hf.continuousWithinAt_rightLim, hf.rightLim.continuousWithinAt_variationOnFromTo_Ici, rightLim
-/
theorem _root_.BoundedVariationOn.continuousWithinAt_variationOnFromTo_rightLim_Ici
    [TopologicalSpace α] [OrderTopology α] [T3Space E] [CompleteSpace E]
    (hf : BoundedVariationOn f univ) {a x : α} :
    ContinuousWithinAt (variationOnFromTo f.rightLim univ a) (Ici x) x :=
  hf.rightLim.continuousWithinAt_variationOnFromTo_Ici hf.continuousWithinAt_rightLim

end variationOnFromTo

/--
theorem `LocallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn'` / 定理 `LocallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn'`

English:
theorem LocallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn'
  statement: {f : α -> Real} {s : Set α}
  proof: by
  rcases eq_empty_or_nonempty s with (rfl | ⟨c, cs⟩)
  · refine ⟨f, 0, subsingleton_empty.monotoneOn _, subsingleton_empty.monotoneOn _,
      (sub_zero f).symm, fun x hx y hy => by simp at hx⟩
  refine ⟨fun x => (variationOnFromTo f s c x + f x) / 2,
    fun x => (variationOnFromTo f s c x - f x

中文:
定理 LocallyBoundedVariationOn.存在_monotoneOn_sub_monotoneOn'
  结论: {f : α -> 实数} {s : 集合 α}
  证明: by
  rcases eq_empty_or_nonempty s with (rfl | ⟨c, cs⟩)
  · refine ⟨f, 0, subsingleton_empty.monotoneOn _, subsingleton_empty.monotoneOn _,
      (sub_zero f).symm, fun x hx y hy => by simp at hx⟩
  refine ⟨fun x => (variationOnFromTo f s c x + f x) / 2,
    fun x => (variationOnFromTo f s c x - f x

Depends on / 依赖: add_self_monotoneOn, eq_empty_or_nonempty, monotoneOn, sub_self_monotoneOn, sub_zero, subsingleton_empty, subsingleton_empty.monotoneOn, variationOnFromTo, variationOnFromTo.add_self_monotoneOn, variationOnFromTo.sub_self_monotoneOn
-/
theorem LocallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn' {f : α -> Real} {s : Set α}
    (h : LocallyBoundedVariationOn f s) :
    exists p q : α -> Real, MonotoneOn p s ∧ MonotoneOn q s ∧ f = p - q ∧
      forall x in s, forall y in s, (p y - p x) + (q y - q x) = variationOnFromTo f s x y := by
  rcases eq_empty_or_nonempty s with (rfl | ⟨c, cs⟩)
  · refine ⟨f, 0, subsingleton_empty.monotoneOn _, subsingleton_empty.monotoneOn _,
      (sub_zero f).symm, fun x hx y hy => by simp at hx⟩
  refine ⟨fun x => (variationOnFromTo f s c x + f x) / 2,
    fun x => (variationOnFromTo f s c x - f x) / 2, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    dsimp
    gcongr 1
    simpa using variationOnFromTo.add_self_monotoneOn h cs hx hy hxy
  · intro x hx y hy hxy
    dsimp
    gcongr 1
    simpa using variationOnFromTo.sub_self_monotoneOn h cs hx hy hxy
  · ext
    simp
    ring
  · intro x hx y hy
    rw [← variationOnFromTo.add h hx cs hy]; rw [variationOnFromTo.eq_neg_swap]
    ring

/--
theorem `LocallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn` / 定理 `LocallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn`

English:
theorem LocallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn
  statement: {f : α -> Real} {s : Set α}
  proof: by
  rcases h.exists_monotoneOn_sub_monotoneOn' with ⟨p, q, hp, hq, h'f, -⟩
  exact ⟨p, q, hp, hq, h'f⟩

中文:
定理 LocallyBoundedVariationOn.存在_monotoneOn_sub_monotoneOn
  结论: {f : α -> 实数} {s : 集合 α}
  证明: by
  rcases h.exists_monotoneOn_sub_monotoneOn' with ⟨p, q, hp, hq, h'f, -⟩
  exact ⟨p, q, hp, hq, h'f⟩

Depends on / 依赖: exists_monotoneOn_sub_monotoneOn, h.exists_monotoneOn_sub_monotoneOn
-/
theorem LocallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn {f : α -> Real} {s : Set α}
    (h : LocallyBoundedVariationOn f s) :
    exists p q : α -> Real, MonotoneOn p s ∧ MonotoneOn q s ∧ f = p - q := by
  rcases h.exists_monotoneOn_sub_monotoneOn' with ⟨p, q, hp, hq, h'f, -⟩
  exact ⟨p, q, hp, hq, h'f⟩
