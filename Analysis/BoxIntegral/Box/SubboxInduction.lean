/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.BoxIntegral.Box.Basic
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Induction on subboxes

In this file we prove the following induction principle for `BoxIntegral.Box`, see
`BoxIntegral.Box.subbox_induction_on`. Let `p` be a predicate on `BoxIntegral.Box ι`, let `I` be a
box. Suppose that the following two properties hold true.

* Consider a smaller box `J ≤ I`. The hyperplanes passing through the center of `J` split it into
  `2 ^ n` boxes. If `p` holds true on each of these boxes, then it is true on `J`.
* For each `z` in the closed box `I.Icc` there exists a neighborhood `U` of `z` within `I.Icc` such
  that for every box `J ≤ I` such that `z ∈ J.Icc ⊆ U`, if `J` is homothetic to `I` with a
  coefficient of the form `1 / 2 ^ m`, then `p` is true on `J`.

Then `p I` is true.

## Tags

rectangular box, induction
-/

@[expose] public section

open Set Function Filter Topology

noncomputable section

namespace BoxIntegral

namespace Box

variable {ι : Type*} {I J : Box ι}

open scoped Classical in
/--
Definition of `splitCenterBox` / `splitCenterBox` 的定义

English:
definition splitCenterBox
  signature: (I : Box ι) (s : Set ι)
  body: s.piecewise (fun i => (I.lower i + I.upper i) / 2) I.lower
  upper := s.piecewise I.upper fun i => (I.lower i + I.upper i) / 2
  lower_lt_upper i := by
    dsimp only [Set.piecewise]
    split_ifs <;> simp only [left_lt_add_div_two, add_div_two_lt_right, I.lower_lt_upper]

中文:
定义 splitCenterBox
  签名: (I : Box ι) (s : 集合 ι)
  定义体: s.piecewise (fun i => (I.lower i + I.upper i) / 2) I.lower
  upper := s.piecewise I.upper fun i => (I.lower i + I.upper i) / 2
  lower_lt_upper i := by
    dsimp only [Set.piecewise]
    split_ifs <;> simp only [left_lt_add_div_two, add_div_two_lt_right, I.lower_lt_upper]

Depends on / 依赖: I.lower, I.upper, piecewise, s.piecewise
-/
def splitCenterBox (I : Box ι) (s : Set ι) : Box ι where
  lower := s.piecewise (fun i => (I.lower i + I.upper i) / 2) I.lower
  upper := s.piecewise I.upper fun i => (I.lower i + I.upper i) / 2
  lower_lt_upper i := by
    dsimp only [Set.piecewise]
    split_ifs <;> simp only [left_lt_add_div_two, add_div_two_lt_right, I.lower_lt_upper]

/--
theorem `mem_splitCenterBox` / 定理 `mem_splitCenterBox`

English:
theorem mem_splitCenterBox
  given: {s : Set ι} {y : ι -> Real}
  proof: by
  simp only [splitCenterBox, mem_def, ← forall_and]
  refine forall_congr' fun i => ?_
  dsimp only [Set.piecewise]
  split_ifs with hs <;> simp only [hs, iff_true, iff_false, not_lt]
  exacts [⟨fun H => ⟨⟨(left_lt_add_div_two.2 (I.lower_lt_upper i)).trans H.1, H.2⟩, H.1⟩,
      fun H => ⟨H.2, H.1.2⟩⟩,
    ⟨fun H => ⟨⟨H.1, H.2.trans (add_div_two_lt_right.2 (I.lower_lt_upper i)).le⟩, H.2⟩,
      fun H => ⟨H.1.1, H.2⟩⟩]

中文:
定理 mem_splitCenterBox
  条件: {s : 集合 ι} {y : ι -> 实数}
  证明: by
  simp only [splitCenterBox, mem_def, ← forall_and]
  refine forall_congr' fun i => ?_
  dsimp only [Set.piecewise]
  split_ifs with hs <;> simp only [hs, iff_true, iff_false, not_lt]
  exacts [⟨fun H => ⟨⟨(left_lt_add_div_two.2 (I.lower_lt_upper i)).trans H.1, H.2⟩, H.1⟩,
      fun H => ⟨H.2, H.1.2⟩⟩,
    ⟨fun H => ⟨⟨H.1, H.2.trans (add_div_two_lt_right.2 (I.lower_lt_upper i)).le⟩, H.2⟩,
      fun H => ⟨H.1.1, H.2⟩⟩]

Depends on / 依赖: I.lower_lt_upper, Set.piecewise, add_div_two_lt_right, exacts, forall_and, forall_congr, iff_false, iff_true, left_lt_add_div_two, lower_lt_upper, mem_def, not_lt, piecewise, splitCenterBox, split_ifs
-/
theorem mem_splitCenterBox {s : Set ι} {y : ι -> Real} :
    y in I.splitCenterBox s ↔ y in I ∧ forall i, (I.lower i + I.upper i) / 2 < y i ↔ i in s := by
  simp only [splitCenterBox, mem_def, ← forall_and]
  refine forall_congr' fun i => ?_
  dsimp only [Set.piecewise]
  split_ifs with hs <;> simp only [hs, iff_true, iff_false, not_lt]
  exacts [⟨fun H => ⟨⟨(left_lt_add_div_two.2 (I.lower_lt_upper i)).trans H.1, H.2⟩, H.1⟩,
      fun H => ⟨H.2, H.1.2⟩⟩,
    ⟨fun H => ⟨⟨H.1, H.2.trans (add_div_two_lt_right.2 (I.lower_lt_upper i)).le⟩, H.2⟩,
      fun H => ⟨H.1.1, H.2⟩⟩]

/--
theorem `splitCenterBox_le` / 定理 `splitCenterBox_le`

English:
theorem splitCenterBox_le
  given: (I : Box ι) (s : Set ι)
  statement: I.splitCenterBox s <= I
  proof: fun _ hx => (mem_splitCenterBox.1 hx).1

中文:
定理 splitCenterBox_le
  条件: (I : Box ι) (s : 集合 ι)
  结论: I.splitCenterBox s <= I
  证明: fun _ hx => (mem_splitCenterBox.1 hx).1

Depends on / 依赖: mem_splitCenterBox
-/
theorem splitCenterBox_le (I : Box ι) (s : Set ι) : I.splitCenterBox s <= I :=
  fun _ hx => (mem_splitCenterBox.1 hx).1

/--
theorem `disjoint_splitCenterBox` / 定理 `disjoint_splitCenterBox`

English:
theorem disjoint_splitCenterBox
  given: (I : Box ι) {s t : Set ι} (h : s != t)
  proof: by
  rw [disjoint_iff_inf_le]
  rintro y ⟨hs, ht⟩; apply h
  ext i
  rw [mem_coe]; rw [mem_splitCenterBox] at hs ht
  rw [← hs.2]; rw [← ht.2]

中文:
定理 disjoint_splitCenterBox
  条件: (I : Box ι) {s t : 集合 ι} (h : s != t)
  证明: by
  rw [disjoint_iff_inf_le]
  rintro y ⟨hs, ht⟩; apply h
  ext i
  rw [mem_coe]; rw [mem_splitCenterBox] at hs ht
  rw [← hs.2]; rw [← ht.2]

Depends on / 依赖: disjoint_iff_inf_le, mem_coe, mem_splitCenterBox
-/
theorem disjoint_splitCenterBox (I : Box ι) {s t : Set ι} (h : s != t) :
    Disjoint (I.splitCenterBox s : Set (ι -> Real)) (I.splitCenterBox t) := by
  rw [disjoint_iff_inf_le]
  rintro y ⟨hs, ht⟩; apply h
  ext i
  rw [mem_coe]; rw [mem_splitCenterBox] at hs ht
  rw [← hs.2]; rw [← ht.2]

/--
theorem `injective_splitCenterBox` / 定理 `injective_splitCenterBox`

English:
theorem injective_splitCenterBox
  given: (I : Box ι)
  statement: Injective I.splitCenterBox
  proof: fun _ _ H =>
  by_contra fun Hne => (I.disjoint_splitCenterBox Hne).ne (nonempty_coe _).ne_empty (H ▸ rfl)

@[simp]

中文:
定理 injective_splitCenterBox
  条件: (I : Box ι)
  结论: 单射 I.splitCenterBox
  证明: fun _ _ H =>
  by_contra fun Hne => (I.disjoint_splitCenterBox Hne).ne (nonempty_coe _).ne_empty (H ▸ rfl)

@[simp]
-/
theorem injective_splitCenterBox (I : Box ι) : Injective I.splitCenterBox := fun _ _ H =>
  by_contra fun Hne => (I.disjoint_splitCenterBox Hne).ne (nonempty_coe _).ne_empty (H ▸ rfl)

@[simp]
/--
theorem `exists_mem_splitCenterBox` / 定理 `exists_mem_splitCenterBox`

English:
theorem exists_mem_splitCenterBox
  given: {I : Box ι} {x : ι -> Real}
  statement: (exists s, x in I.splitCenterBox s) ↔ x in I
  proof: ⟨fun ⟨s, hs⟩ => I.splitCenterBox_le s hs, fun hx =>
    ⟨{ i | (I.lower i + I.upper i) / 2 < x i }, mem_splitCenterBox.2 ⟨hx, fun _ => Iff.rfl⟩⟩⟩

中文:
定理 存在_mem_splitCenterBox
  条件: {I : Box ι} {x : ι -> 实数}
  结论: (存在 s, x in I.splitCenterBox s) ↔ x in I
  证明: ⟨fun ⟨s, hs⟩ => I.splitCenterBox_le s hs, fun hx =>
    ⟨{ i | (I.lower i + I.upper i) / 2 < x i }, mem_splitCenterBox.2 ⟨hx, fun _ => Iff.rfl⟩⟩⟩

Depends on / 依赖: I.lower, I.splitCenterBox_le, I.upper, Iff.rfl, mem_splitCenterBox, splitCenterBox_le
-/
theorem exists_mem_splitCenterBox {I : Box ι} {x : ι -> Real} : (exists s, x in I.splitCenterBox s) ↔ x in I :=
  ⟨fun ⟨s, hs⟩ => I.splitCenterBox_le s hs, fun hx =>
    ⟨{ i | (I.lower i + I.upper i) / 2 < x i }, mem_splitCenterBox.2 ⟨hx, fun _ => Iff.rfl⟩⟩⟩

/-- `BoxIntegral.Box.splitCenterBox` bundled as a `Function.Embedding`. -/
@[simps]
/--
Definition of `splitCenterBoxEmb` / `splitCenterBoxEmb` 的定义

English:
definition splitCenterBoxEmb
  signature: (I : Box ι)
  body: ⟨splitCenterBox I, injective_splitCenterBox I⟩

@[simp]

中文:
定义 splitCenterBoxEmb
  签名: (I : Box ι)
  定义体: ⟨splitCenterBox I, injective_splitCenterBox I⟩

@[simp]

Depends on / 依赖: injective_splitCenterBox, splitCenterBox
-/
def splitCenterBoxEmb (I : Box ι) : Set ι ↪ Box ι :=
  ⟨splitCenterBox I, injective_splitCenterBox I⟩

@[simp]
/--
theorem `iUnion_coe_splitCenterBox` / 定理 `iUnion_coe_splitCenterBox`

English:
theorem iUnion_coe_splitCenterBox
  given: (I : Box ι)
  statement: ⋃ s, (I.splitCenterBox s : Set (ι -> Real)) = I
  proof: by
  ext x
  simp

@[simp]

中文:
定理 iUnion_coe_splitCenterBox
  条件: (I : Box ι)
  结论: ⋃ s, (I.splitCenterBox s : 集合 (ι -> 实数)) = I
  证明: by
  ext x
  simp

@[simp]
-/
theorem iUnion_coe_splitCenterBox (I : Box ι) : ⋃ s, (I.splitCenterBox s : Set (ι -> Real)) = I := by
  ext x
  simp

@[simp]
/--
theorem `upper_sub_lower_splitCenterBox` / 定理 `upper_sub_lower_splitCenterBox`

English:
theorem upper_sub_lower_splitCenterBox
  given: (I : Box ι) (s : Set ι) (i : ι)
  proof: by
  by_cases i in s <;> simp [field, splitCenterBox, *] <;> ring

中文:
定理 upper_sub_lower_splitCenterBox
  条件: (I : Box ι) (s : 集合 ι) (i : ι)
  证明: by
  by_cases i in s <;> simp [field, splitCenterBox, *] <;> ring

Depends on / 依赖: splitCenterBox
-/
theorem upper_sub_lower_splitCenterBox (I : Box ι) (s : Set ι) (i : ι) :
    (I.splitCenterBox s).upper i - (I.splitCenterBox s).lower i = (I.upper i - I.lower i) / 2 := by
  by_cases i in s <;> simp [field, splitCenterBox, *] <;> ring

/-- Let `p` be a predicate on `Box ι`, let `I` be a box. Suppose that the following two properties
hold true.

* `H_ind` : Consider a smaller box `J ≤ I`. The hyperplanes passing through the center of `J` split
  it into `2 ^ n` boxes. If `p` holds true on each of these boxes, then it true on `J`.

* `H_nhds` : For each `z` in the closed box `I.Icc` there exists a neighborhood `U` of `z` within
  `I.Icc` such that for every box `J ≤ I` such that `z ∈ J.Icc ⊆ U`, if `J` is homothetic to `I`
  with a coefficient of the form `1 / 2 ^ m`, then `p` is true on `J`.

Then `p I` is true. See also `BoxIntegral.Box.subbox_induction_on` for a version using
`BoxIntegral.Prepartition.splitCenter` instead of `BoxIntegral.Box.splitCenterBox`.

The proof still works if we assume `H_ind` only for subboxes `J ≤ I` that are homothetic to `I` with
a coefficient of the form `2⁻ᵐ` but we do not need this generalization yet. -/
@[elab_as_elim]
/--
theorem `subbox_induction_on'` / 定理 `subbox_induction_on'`

English:
theorem subbox_induction_on'
  statement: {p : Box ι -> Prop} (I : Box ι)
  proof: by
  by_contra hpI
  -- First we use `H_ind` to construct a decreasing sequence of boxes such that `∀ m, ¬p (J m)`.
  replace H_ind := fun J hJ => not_imp_not.2 (H_ind J hJ)
  simp only [not_forall] at H_ind
  choose! s hs using H_ind
  set J : Nat -> Box ι := fun m => (fun J => splitCenterBox J (s J))^[m] I
  have J_succ : forall m, J (m + 1) = splitCenterBox (J m) (s <| J m) :=
    fun m => iterate_succ_apply' _ _ _
  -- Now we prove some properties of `J`
  have hJmono : Antitone J :=
    antitone_nat_of_succ_le fun n => by simpa [J_succ] using splitCenterBox_le _ _
  have hJle (m) : J m <= I := hJmono zero_le
  have hJp (m) : ¬p (J m) := Nat.recOn m hpI fun m => by simpa only [J_succ] using hs (J m) (hJle m)
  have hJsub (m i) : (J m).upper i - (J m).lower i = (I.upper i - I.lower i) / 2 ^ m := by
    induction m with
    | zero => simp [J]
    | succ m ihm => simp only [pow_succ, J_succ, upper_sub_lower_splitCenterBox, ihm, div_div]
  have h0 : J 0 = I := rfl
  clear_value J
  clear hpI hs J_succ s
  -- Let `z` be the unique common point of all `(J m).Icc`. Then `H_nhds` proves `p (J m)` for
  -- sufficiently large `m`. This contradicts `hJp`.
  set z : ι -> Real := ⨆ m, (J m).lower
  have hzJ : forall m, z in Box.Icc (J m) :=
    mem_iInter.1 (ciSup_mem_iInter_Icc_of_antitone_Icc
      ((@Box.Icc ι).monotone.comp_antitone hJmono) fun m => (J m).lower_le_upper)
  have hJl_mem : forall m, (J m).lower in Box.Icc I := fun m => le_iff_Icc.1 (hJle m) (J m).lower_mem_Icc
  have hJu_mem : forall m, (J m).upper in Box.Icc I := fun m => le_iff_Icc.1 (hJle m) (J m).upper_mem_Icc
  have hJlz : Tendsto (fun m => (J m).lower) atTop (𝓝 z) :=
    tendsto_atTop_ciSup (antitone_lower.comp hJmono) ⟨I.upper, fun x ⟨m, hm⟩ => hm ▸ (hJl_mem m).2⟩
  have hJuz : Tendsto (fun m => (J m).upper) atTop (𝓝 z) := by
    suffices Tendsto (fun m => (J m).upper - (J m).lower) atTop (𝓝 0) by simpa using hJlz.add this
    refine tendsto_pi_nhds.2 fun i => ?_
    simpa [hJsub] using
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt _root_.one_lt_two)
  replace hJlz : Tendsto (fun m => (J m).lower) atTop (𝓝[Icc I.lower I.upper] z) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hJlz (Eventually.of_forall hJl_mem)
  replace hJuz : Tendsto (fun m => (J m).upper) atTop (𝓝[Icc I.lower I.upper] z) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hJuz (Eventually.of_forall hJu_mem)
  rcases H_nhds z (h0 ▸ hzJ 0) with ⟨U, hUz, hU⟩
  rcases (tendsto_lift'.1 (hJlz.Icc hJuz) U hUz).exists with ⟨m, hUm⟩
  exact hJp m (hU (J m) (hJle m) m (hzJ m) hUm (hJsub m))

中文:
定理 subbox_induction_on'
  结论: {p : Box ι -> 命题} (I : Box ι)
  证明: by
  by_contra hpI
  -- First we use `H_ind` to construct a decreasing sequence of boxes such that `∀ m, ¬p (J m)`.
  replace H_ind := fun J hJ => not_imp_not.2 (H_ind J hJ)
  simp only [not_forall] at H_ind
  choose! s hs using H_ind
  set J : Nat -> Box ι := fun m => (fun J => splitCenterBox J (s J))^[m] I
  have J_succ : forall m, J (m + 1) = splitCenterBox (J m) (s <| J m) :=
    fun m => iterate_succ_apply' _ _ _
  -- Now we prove some properties of `J`
  have hJmono : Antitone J :=
    antitone_nat_of_succ_le fun n => by simpa [J_succ] using splitCenterBox_le _ _
  have hJle (m) : J m <= I := hJmono zero_le
  have hJp (m) : ¬p (J m) := Nat.recOn m hpI fun m => by simpa only [J_succ] using hs (J m) (hJle m)
  have hJsub (m i) : (J m).upper i - (J m).lower i = (I.upper i - I.lower i) / 2 ^ m := by
    induction m with
    | zero => simp [J]
    | succ m ihm => simp only [pow_succ, J_succ, upper_sub_lower_splitCenterBox, ihm, div_div]
  have h0 : J 0 = I := rfl
  clear_value J
  clear hpI hs J_succ s
  -- Let `z` be the unique common point of all `(J m).Icc`. Then `H_nhds` proves `p (J m)` for
  -- sufficiently large `m`. This contradicts `hJp`.
  set z : ι -> Real := ⨆ m, (J m).lower
  have hzJ : forall m, z in Box.Icc (J m) :=
    mem_iInter.1 (ciSup_mem_iInter_Icc_of_antitone_Icc
      ((@Box.Icc ι).monotone.comp_antitone hJmono) fun m => (J m).lower_le_upper)
  have hJl_mem : forall m, (J m).lower in Box.Icc I := fun m => le_iff_Icc.1 (hJle m) (J m).lower_mem_Icc
  have hJu_mem : forall m, (J m).upper in Box.Icc I := fun m => le_iff_Icc.1 (hJle m) (J m).upper_mem_Icc
  have hJlz : Tendsto (fun m => (J m).lower) atTop (𝓝 z) :=
    tendsto_atTop_ciSup (antitone_lower.comp hJmono) ⟨I.upper, fun x ⟨m, hm⟩ => hm ▸ (hJl_mem m).2⟩
  have hJuz : Tendsto (fun m => (J m).upper) atTop (𝓝 z) := by
    suffices Tendsto (fun m => (J m).upper - (J m).lower) atTop (𝓝 0) by simpa using hJlz.add this
    refine tendsto_pi_nhds.2 fun i => ?_
    simpa [hJsub] using
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt _root_.one_lt_two)
  replace hJlz : Tendsto (fun m => (J m).lower) atTop (𝓝[Icc I.lower I.upper] z) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hJlz (Eventually.of_forall hJl_mem)
  replace hJuz : Tendsto (fun m => (J m).upper) atTop (𝓝[Icc I.lower I.upper] z) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hJuz (Eventually.of_forall hJu_mem)
  rcases H_nhds z (h0 ▸ hzJ 0) with ⟨U, hUz, hU⟩
  rcases (tendsto_lift'.1 (hJlz.Icc hJuz) U hUz).exists with ⟨m, hUm⟩
  exact hJp m (hU (J m) (hJle m) m (hzJ m) hUm (hJsub m))
-/
theorem subbox_induction_on' {p : Box ι -> Prop} (I : Box ι)
    (H_ind : forall J <= I, (forall s, p (splitCenterBox J s)) -> p J)
    (H_nhds : forall z in Box.Icc I, exists U in 𝓝[Box.Icc I] z, forall J <= I, forall (m : Nat), z in Box.Icc J ->
      Box.Icc J subseteq U -> (forall i, J.upper i - J.lower i = (I.upper i - I.lower i) / 2 ^ m) -> p J) :
    p I := by
  by_contra hpI
  -- First we use `H_ind` to construct a decreasing sequence of boxes such that `∀ m, ¬p (J m)`.
  replace H_ind := fun J hJ => not_imp_not.2 (H_ind J hJ)
  simp only [not_forall] at H_ind
  choose! s hs using H_ind
  set J : Nat -> Box ι := fun m => (fun J => splitCenterBox J (s J))^[m] I
  have J_succ : forall m, J (m + 1) = splitCenterBox (J m) (s <| J m) :=
    fun m => iterate_succ_apply' _ _ _
  -- Now we prove some properties of `J`
  have hJmono : Antitone J :=
    antitone_nat_of_succ_le fun n => by simpa [J_succ] using splitCenterBox_le _ _
  have hJle (m) : J m <= I := hJmono zero_le
  have hJp (m) : ¬p (J m) := Nat.recOn m hpI fun m => by simpa only [J_succ] using hs (J m) (hJle m)
  have hJsub (m i) : (J m).upper i - (J m).lower i = (I.upper i - I.lower i) / 2 ^ m := by
    induction m with
    | zero => simp [J]
    | succ m ihm => simp only [pow_succ, J_succ, upper_sub_lower_splitCenterBox, ihm, div_div]
  have h0 : J 0 = I := rfl
  clear_value J
  clear hpI hs J_succ s
  -- Let `z` be the unique common point of all `(J m).Icc`. Then `H_nhds` proves `p (J m)` for
  -- sufficiently large `m`. This contradicts `hJp`.
  set z : ι -> Real := ⨆ m, (J m).lower
  have hzJ : forall m, z in Box.Icc (J m) :=
    mem_iInter.1 (ciSup_mem_iInter_Icc_of_antitone_Icc
      ((@Box.Icc ι).monotone.comp_antitone hJmono) fun m => (J m).lower_le_upper)
  have hJl_mem : forall m, (J m).lower in Box.Icc I := fun m => le_iff_Icc.1 (hJle m) (J m).lower_mem_Icc
  have hJu_mem : forall m, (J m).upper in Box.Icc I := fun m => le_iff_Icc.1 (hJle m) (J m).upper_mem_Icc
  have hJlz : Tendsto (fun m => (J m).lower) atTop (𝓝 z) :=
    tendsto_atTop_ciSup (antitone_lower.comp hJmono) ⟨I.upper, fun x ⟨m, hm⟩ => hm ▸ (hJl_mem m).2⟩
  have hJuz : Tendsto (fun m => (J m).upper) atTop (𝓝 z) := by
    suffices Tendsto (fun m => (J m).upper - (J m).lower) atTop (𝓝 0) by simpa using hJlz.add this
    refine tendsto_pi_nhds.2 fun i => ?_
    simpa [hJsub] using
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt _root_.one_lt_two)
  replace hJlz : Tendsto (fun m => (J m).lower) atTop (𝓝[Icc I.lower I.upper] z) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hJlz (Eventually.of_forall hJl_mem)
  replace hJuz : Tendsto (fun m => (J m).upper) atTop (𝓝[Icc I.lower I.upper] z) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hJuz (Eventually.of_forall hJu_mem)
  rcases H_nhds z (h0 ▸ hzJ 0) with ⟨U, hUz, hU⟩
  rcases (tendsto_lift'.1 (hJlz.Icc hJuz) U hUz).exists with ⟨m, hUm⟩
  exact hJp m (hU (J m) (hJle m) m (hzJ m) hUm (hJsub m))

end Box

end BoxIntegral
