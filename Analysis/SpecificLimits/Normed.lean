/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Sébastien Gouëzel, Yury Kudryashov, Dylan MacKenzie, Patrick Massot
-/
module

public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.List.TFAE
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Order.Filter.AtTopBot.ModEq
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Tactic.NoncommRing

/-!
# A collection of specific limit computations

This file contains important specific limit computations in (semi-)normed groups/rings/spaces, as
well as such computations in `ℝ` when the natural proof passes through a fact about normed spaces.
-/

@[expose] public section

noncomputable section

open Set Function Filter Finset Metric Module Asymptotics Topology Nat NNReal ENNReal
open scoped Ring

variable {α : Type*}

/--
theorem `tendsto_natCast_atTop_cobounded` / 定理 `tendsto_natCast_atTop_cobounded`

English:
theorem tendsto_natCast_atTop_cobounded
  proof: by
  rw [← tendsto_norm_atTop_iff_cobounded]
  simpa [norm_natCast_eq_mul_norm_one] using tendsto_natCast_atTop_atTop
.atTop_mul_const (norm_pos_iff.mpr one_ne_zero)

中文:
定理 tendsto_natCast_atTop_cobounded
  证明: by
  rw [← tendsto_norm_atTop_iff_cobounded]
  simpa [norm_natCast_eq_mul_norm_one] using tendsto_natCast_atTop_atTop
.atTop_mul_const (norm_pos_iff.mpr one_ne_zero)

Depends on / 依赖: atTop_mul_const, norm_natCast_eq_mul_norm_one, norm_pos_iff, norm_pos_iff.mpr, one_ne_zero, tendsto_natCast_atTop_atTop, tendsto_norm_atTop_iff_cobounded
-/
theorem tendsto_natCast_atTop_cobounded
    [NormedRing α] [NormSMulClass Int α] [Nontrivial α] :
    Tendsto Nat.cast atTop (Bornology.cobounded α) := by
  rw [← tendsto_norm_atTop_iff_cobounded]
  simpa [norm_natCast_eq_mul_norm_one] using tendsto_natCast_atTop_atTop
.atTop_mul_const (norm_pos_iff.mpr one_ne_zero)

/--
theorem `tendsto_intCast_atBot_sup_atTop_cobounded` / 定理 `tendsto_intCast_atBot_sup_atTop_cobounded`

English:
theorem tendsto_intCast_atBot_sup_atTop_cobounded
  proof: by
  rw [← tendsto_norm_atTop_iff_cobounded]
  simpa [norm_intCast_eq_abs_mul_norm_one] using tendsto_intCast_atTop_atTop
.comp (tendsto_abs_atBot_atTop.sup tendsto_abs_atTop_atTop)
.atTop_mul_const (norm_pos_iff.mpr one_ne_zero)

中文:
定理 tendsto_intCast_atBot_sup_atTop_cobounded
  证明: by
  rw [← tendsto_norm_atTop_iff_cobounded]
  simpa [norm_intCast_eq_abs_mul_norm_one] using tendsto_intCast_atTop_atTop
.comp (tendsto_abs_atBot_atTop.sup tendsto_abs_atTop_atTop)
.atTop_mul_const (norm_pos_iff.mpr one_ne_zero)

Depends on / 依赖: atTop_mul_const, norm_intCast_eq_abs_mul_norm_one, norm_pos_iff, norm_pos_iff.mpr, one_ne_zero, tendsto_abs_atBot_atTop, tendsto_abs_atBot_atTop.sup, tendsto_abs_atTop_atTop, tendsto_intCast_atTop_atTop, tendsto_norm_atTop_iff_cobounded
-/
theorem tendsto_intCast_atBot_sup_atTop_cobounded
    [NormedRing α] [NormSMulClass Int α] [Nontrivial α] :
    Tendsto Int.cast (atBot ⊔ atTop) (Bornology.cobounded α) := by
  rw [← tendsto_norm_atTop_iff_cobounded]
  simpa [norm_intCast_eq_abs_mul_norm_one] using tendsto_intCast_atTop_atTop
.comp (tendsto_abs_atBot_atTop.sup tendsto_abs_atTop_atTop)
.atTop_mul_const (norm_pos_iff.mpr one_ne_zero)

/--
theorem `tendsto_intCast_atBot_cobounded` / 定理 `tendsto_intCast_atBot_cobounded`

English:
theorem tendsto_intCast_atBot_cobounded
  proof: tendsto_intCast_atBot_sup_atTop_cobounded.mono_left le_sup_left

中文:
定理 tendsto_intCast_atBot_cobounded
  证明: tendsto_intCast_atBot_sup_atTop_cobounded.mono_left le_sup_left

Depends on / 依赖: le_sup_left, mono_left, tendsto_intCast_atBot_sup_atTop_cobounded, tendsto_intCast_atBot_sup_atTop_cobounded.mono_left
-/
theorem tendsto_intCast_atBot_cobounded
    [NormedRing α] [NormSMulClass Int α] [Nontrivial α] :
    Tendsto Int.cast atBot (Bornology.cobounded α) :=
  tendsto_intCast_atBot_sup_atTop_cobounded.mono_left le_sup_left

/--
theorem `tendsto_intCast_atTop_cobounded` / 定理 `tendsto_intCast_atTop_cobounded`

English:
theorem tendsto_intCast_atTop_cobounded
  proof: tendsto_intCast_atBot_sup_atTop_cobounded.mono_left le_sup_right

中文:
定理 tendsto_intCast_atTop_cobounded
  证明: tendsto_intCast_atBot_sup_atTop_cobounded.mono_left le_sup_right

Depends on / 依赖: le_sup_right, mono_left, tendsto_intCast_atBot_sup_atTop_cobounded, tendsto_intCast_atBot_sup_atTop_cobounded.mono_left
-/
theorem tendsto_intCast_atTop_cobounded
    [NormedRing α] [NormSMulClass Int α] [Nontrivial α] :
    Tendsto Int.cast atTop (Bornology.cobounded α) :=
  tendsto_intCast_atBot_sup_atTop_cobounded.mono_left le_sup_right


/--
theorem `isLittleO_pow_pow_of_lt_left` / 定理 `isLittleO_pow_pow_of_lt_left`

English:
theorem isLittleO_pow_pow_of_lt_left
  given: {r₁ r₂ : Real} (h₁ : 0 <= r₁) (h₂ : r₁ < r₂)
  proof: have H : 0 < r₂ := h₁.trans_lt h₂
(isLittleO_of_tendsto fun _ hn => False.elim <| H.ne' <| eq_zero_of_pow_eq_zero hn)
    (tendsto_pow_atTop_nhds_zero_of_lt_one
      (div_nonneg h₁ (h₁.trans h₂.le)) ((div_lt_one H).2 h₂)).congr fun _ => div_pow _ _ _

中文:
定理 isLittleO_pow_pow_of_lt_left
  条件: {r₁ r₂ : 实数} (h₁ : 0 <= r₁) (h₂ : r₁ < r₂)
  证明: have H : 0 < r₂ := h₁.trans_lt h₂
(isLittleO_of_tendsto fun _ hn => False.elim <| H.ne' <| eq_zero_of_pow_eq_zero hn)
    (tendsto_pow_atTop_nhds_zero_of_lt_one
      (div_nonneg h₁ (h₁.trans h₂.le)) ((div_lt_one H).2 h₂)).congr fun _ => div_pow _ _ _

Depends on / 依赖: False.elim, H.ne, div_lt_one, div_nonneg, div_pow, eq_zero_of_pow_eq_zero, isLittleO_of_tendsto, tendsto_pow_atTop_nhds_zero_of_lt_one, trans_lt
-/
theorem isLittleO_pow_pow_of_lt_left {r₁ r₂ : Real} (h₁ : 0 <= r₁) (h₂ : r₁ < r₂) :
    (fun n : Nat => r₁ ^ n) =o[atTop] fun n => r₂ ^ n :=
  have H : 0 < r₂ := h₁.trans_lt h₂
(isLittleO_of_tendsto fun _ hn => False.elim <| H.ne' <| eq_zero_of_pow_eq_zero hn)
    (tendsto_pow_atTop_nhds_zero_of_lt_one
      (div_nonneg h₁ (h₁.trans h₂.le)) ((div_lt_one H).2 h₂)).congr fun _ => div_pow _ _ _

/--
theorem `isBigO_pow_pow_of_le_left` / 定理 `isBigO_pow_pow_of_le_left`

English:
theorem isBigO_pow_pow_of_le_left
  given: {r₁ r₂ : Real} (h₁ : 0 <= r₁) (h₂ : r₁ <= r₂)
  proof: h₂.eq_or_lt.elim (fun h => h ▸ isBigO_refl _ _) fun h => (isLittleO_pow_pow_of_lt_left h₁ h).isBigO

中文:
定理 isBigO_pow_pow_of_le_left
  条件: {r₁ r₂ : 实数} (h₁ : 0 <= r₁) (h₂ : r₁ <= r₂)
  证明: h₂.eq_or_lt.elim (fun h => h ▸ isBigO_refl _ _) fun h => (isLittleO_pow_pow_of_lt_left h₁ h).isBigO

Depends on / 依赖: eq_or_lt, eq_or_lt.elim, isBigO, isBigO_refl, isLittleO_pow_pow_of_lt_left
-/
theorem isBigO_pow_pow_of_le_left {r₁ r₂ : Real} (h₁ : 0 <= r₁) (h₂ : r₁ <= r₂) :
    (fun n : Nat => r₁ ^ n) =O[atTop] fun n => r₂ ^ n :=
  h₂.eq_or_lt.elim (fun h => h ▸ isBigO_refl _ _) fun h => (isLittleO_pow_pow_of_lt_left h₁ h).isBigO

/--
theorem `isLittleO_pow_pow_of_abs_lt_left` / 定理 `isLittleO_pow_pow_of_abs_lt_left`

English:
theorem isLittleO_pow_pow_of_abs_lt_left
  given: {r₁ r₂ : Real} (h : |r₁| < |r₂|)
  proof: by
  refine (IsLittleO.of_norm_left ?_).of_norm_right
  exact (isLittleO_pow_pow_of_lt_left (abs_nonneg r₁) h).congr (pow_abs r₁) (pow_abs r₂)

中文:
定理 isLittleO_pow_pow_of_abs_lt_left
  条件: {r₁ r₂ : 实数} (h : |r₁| < |r₂|)
  证明: by
  refine (IsLittleO.of_norm_left ?_).of_norm_right
  exact (isLittleO_pow_pow_of_lt_left (abs_nonneg r₁) h).congr (pow_abs r₁) (pow_abs r₂)

Depends on / 依赖: IsLittleO, IsLittleO.of_norm_left, abs_nonneg, isLittleO_pow_pow_of_lt_left, of_norm_left, of_norm_right, pow_abs
-/
theorem isLittleO_pow_pow_of_abs_lt_left {r₁ r₂ : Real} (h : |r₁| < |r₂|) :
    (fun n : Nat => r₁ ^ n) =o[atTop] fun n => r₂ ^ n := by
  refine (IsLittleO.of_norm_left ?_).of_norm_right
  exact (isLittleO_pow_pow_of_lt_left (abs_nonneg r₁) h).congr (pow_abs r₁) (pow_abs r₂)

open List in
/--
theorem `TFAE_exists_lt_isLittleO_pow` / 定理 `TFAE_exists_lt_isLittleO_pow`

English:
theorem TFAE_exists_lt_isLittleO_pow
  given: (f : Nat -> Real) (R : Real)
  proof: by
  have A : Ico 0 R subseteq Ioo (-R) R :=
    fun x hx => ⟨(neg_lt_zero.2 (hx.1.trans_lt hx.2)).trans_le hx.1, hx.2⟩
  have B : Ioo 0 R subseteq Ioo (-R) R := Subset.trans Ioo_subset_Ico_self A
  -- First we prove that 1-4 are equivalent using 2 → 3 → 4, 1 → 3, and 2 → 1
  tfae_have 1 -> 3 := fun

中文:
定理 TFAE_存在_lt_isLittleO_pow
  条件: (f : 自然数 -> 实数) (R : 实数)
  证明: by
  have A : Ico 0 R subseteq Ioo (-R) R :=
    fun x hx => ⟨(neg_lt_zero.2 (hx.1.trans_lt hx.2)).trans_le hx.1, hx.2⟩
  have B : Ioo 0 R subseteq Ioo (-R) R := Subset.trans Ioo_subset_Ico_self A
  -- First we prove that 1-4 are equivalent using 2 → 3 → 4, 1 → 3, and 2 → 1
  tfae_have 1 -> 3 := fun

Depends on / 依赖: Ioo_subset_Ico_self, Subset, Subset.trans, neg_lt_zero, subseteq, trans_le, trans_lt
-/
theorem TFAE_exists_lt_isLittleO_pow (f : Nat -> Real) (R : Real) :
    TFAE
      [exists a in Ioo (-R) R, f =o[atTop] (a ^ ·), exists a in Ioo 0 R, f =o[atTop] (a ^ ·),
        exists a in Ioo (-R) R, f =O[atTop] (a ^ ·), exists a in Ioo 0 R, f =O[atTop] (a ^ ·),
        exists a < R, exists C : Real, (0 < C ∨ 0 < R) ∧ forall n, |f n| <= C * a ^ n,
        exists a in Ioo 0 R, exists C > 0, forall n, |f n| <= C * a ^ n, exists a < R, forallᶠ n in atTop, |f n| <= a ^ n,
        exists a in Ioo 0 R, forallᶠ n in atTop, |f n| <= a ^ n] := by
  have A : Ico 0 R subseteq Ioo (-R) R :=
    fun x hx => ⟨(neg_lt_zero.2 (hx.1.trans_lt hx.2)).trans_le hx.1, hx.2⟩
  have B : Ioo 0 R subseteq Ioo (-R) R := Subset.trans Ioo_subset_Ico_self A
  -- First we prove that 1-4 are equivalent using 2 → 3 → 4, 1 → 3, and 2 → 1
  tfae_have 1 -> 3 := fun ⟨a, ha, H⟩ => ⟨a, ha, H.isBigO⟩
  tfae_have 2 -> 1 := fun ⟨a, ha, H⟩ => ⟨a, B ha, H⟩
  tfae_have 3 -> 2
  | ⟨a, ha, H⟩ => by
    rcases exists_between (abs_lt.2 ha) with ⟨b, hab, hbR⟩
    exact ⟨b, ⟨(abs_nonneg a).trans_lt hab, hbR⟩,
      H.trans_isLittleO (isLittleO_pow_pow_of_abs_lt_left (hab.trans_le (le_abs_self b)))⟩
  tfae_have 2 -> 4 := fun ⟨a, ha, H⟩ => ⟨a, ha, H.isBigO⟩
  tfae_have 4 -> 3 := fun ⟨a, ha, H⟩ => ⟨a, B ha, H⟩
  -- Add 5 and 6 using 4 → 6 → 5 → 3
  tfae_have 4 -> 6
  | ⟨a, ha, H⟩ => by
    rcases bound_of_isBigO_nat_atTop H with ⟨C, hC₀, hC⟩
    refine ⟨a, ha, C, hC₀, fun n => ?_⟩
    simpa only [Real.norm_eq_abs, abs_pow, abs_of_nonneg ha.1.le] using hC (pow_ne_zero n ha.1.ne')
  tfae_have 6 -> 5 := fun ⟨a, ha, C, H₀, H⟩ => ⟨a, ha.2, C, Or.inl H₀, H⟩
  tfae_have 5 -> 3
  | ⟨a, ha, C, h₀, H⟩ => by
    rcases sign_cases_of_C_mul_pow_nonneg fun n => (abs_nonneg _).trans (H n) with (rfl | ⟨hC₀, ha₀⟩)
    · obtain rfl : f = 0 := by
        ext n
        simpa using H n
      simp only [lt_irrefl, false_or] at h₀
      exact ⟨0, ⟨neg_lt_zero.2 h₀, h₀⟩, isBigO_zero _ _⟩
    exact ⟨a, A ⟨ha₀, ha⟩,
isBigO_of_le' _ fun n => (H n).trans mul_le_mul_of_nonneg_left (le_abs_self _) hC₀.le⟩
  -- Add 7 and 8 using 2 → 8 → 7 → 3
  tfae_have 2 -> 8
  | ⟨a, ha, H⟩ => by
    refine ⟨a, ha, (H.def zero_lt_one).mono fun n hn => ?_⟩
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, one_mul, abs_pow, abs_of_pos ha.1] at hn
  tfae_have 8 -> 7 := fun ⟨a, ha, H⟩ => ⟨a, ha.2, H⟩
  tfae_have 7 -> 3
  | ⟨a, ha, H⟩ => by
    refine ⟨a, A ⟨?_, ha⟩, .of_norm_eventuallyLE H⟩
    exact nonneg_of_eventually_pow_nonneg (H.mono fun n => (abs_nonneg _).trans)
  tfae_finish

/--
theorem `isLittleO_pow_const_const_pow_of_one_lt` / 定理 `isLittleO_pow_const_const_pow_of_one_lt`

English:
theorem isLittleO_pow_const_const_pow_of_one_lt
  statement: {R : Type*} [NormedRing R] (k : Nat) {r : Real}
  proof: by
  have : Tendsto (fun x : Real => x ^ k) (𝓝[>] 1) (𝓝 1) :=
    ((continuous_id.pow k).tendsto' (1 : Real) 1 (one_pow _)).mono_left inf_le_left
  obtain ⟨r' : Real, hr' : r' ^ k < r, h1 : 1 < r'⟩ :=
    ((this.eventually (gt_mem_nhds hr)).and self_mem_nhdsWithin).exists
  have h0 : 0 <= r' := zero

中文:
定理 isLittleO_pow_const_const_pow_of_one_lt
  结论: {R : 类型} [赋范环 R] (k : 自然数) {r : 实数}
  证明: by
  have : Tendsto (fun x : Real => x ^ k) (𝓝[>] 1) (𝓝 1) :=
    ((continuous_id.pow k).tendsto' (1 : Real) 1 (one_pow _)).mono_left inf_le_left
  obtain ⟨r' : Real, hr' : r' ^ k < r, h1 : 1 < r'⟩ :=
    ((this.eventually (gt_mem_nhds hr)).and self_mem_nhdsWithin).exists
  have h0 : 0 <= r' := zero

Depends on / 依赖: Tendsto, continuous_id, continuous_id.pow, eventually, gt_mem_nhds, h1.le, inf_le_left, isLittleO_pow_pow_of_lt_left, mono_left, one_pow, pow_, pow_nonneg, self_mem_nhdsWithin, tendsto, this.eventually, this.trans_isLittleO, trans_isLittleO, zero_le_one, zero_le_one.trans
-/
theorem isLittleO_pow_const_const_pow_of_one_lt {R : Type*} [NormedRing R] (k : Nat) {r : Real}
    (hr : 1 < r) : (fun n => (n : R) ^ k : Nat -> R) =o[atTop] fun n => r ^ n := by
  have : Tendsto (fun x : Real => x ^ k) (𝓝[>] 1) (𝓝 1) :=
    ((continuous_id.pow k).tendsto' (1 : Real) 1 (one_pow _)).mono_left inf_le_left
  obtain ⟨r' : Real, hr' : r' ^ k < r, h1 : 1 < r'⟩ :=
    ((this.eventually (gt_mem_nhds hr)).and self_mem_nhdsWithin).exists
  have h0 : 0 <= r' := zero_le_one.trans h1.le
  suffices (fun n => (n : R) ^ k : Nat -> R) =O[atTop] fun n : Nat => (r' ^ k) ^ n from
    this.trans_isLittleO (isLittleO_pow_pow_of_lt_left (pow_nonneg h0 _) hr')
  conv in (r' ^ _) ^ _ => rw [← pow_mul, mul_comm, pow_mul]
  suffices forall n : Nat, ‖(n : R)‖ <= (r' - 1)⁻¹ * ‖(1 : R)‖ * ‖r' ^ n‖ from
    (isBigO_of_le' _ this).pow _
  intro n
  rw [mul_right_comm]
  refine n.norm_cast_le.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  simpa [_root_.div_eq_inv_mul, Real.norm_eq_abs, abs_of_nonneg h0] using n.cast_le_pow_div_sub h1

/--
theorem `isLittleO_coe_const_pow_of_one_lt` / 定理 `isLittleO_coe_const_pow_of_one_lt`

English:
theorem isLittleO_coe_const_pow_of_one_lt
  given: {R : Type*} [NormedRing R] {r : Real} (hr : 1 < r)
  proof: by
  simpa only [pow_one] using @isLittleO_pow_const_const_pow_of_one_lt R _ 1 _ hr

中文:
定理 isLittleO_coe_const_pow_of_one_lt
  条件: {R : 类型} [赋范环 R] {r : 实数} (hr : 1 < r)
  证明: by
  simpa only [pow_one] using @isLittleO_pow_const_const_pow_of_one_lt R _ 1 _ hr

Depends on / 依赖: isLittleO_pow_const_const_pow_of_one_lt, pow_one
-/
theorem isLittleO_coe_const_pow_of_one_lt {R : Type*} [NormedRing R] {r : Real} (hr : 1 < r) :
    ((↑) : Nat -> R) =o[atTop] fun n => r ^ n := by
  simpa only [pow_one] using @isLittleO_pow_const_const_pow_of_one_lt R _ 1 _ hr

/--
theorem `isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt` / 定理 `isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt`

English:
theorem isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt
  statement: {R : Type*} [NormedRing R] (k : Nat)
  proof: by
  by_cases h0 : r₁ = 0
  · refine (isLittleO_zero _ _).congr' (mem_atTop_sets.2 <| ⟨1, fun n hn => ?_⟩) EventuallyEq.rfl
    simp [zero_pow (one_le_iff_ne_zero.1 hn), h0]
  rw [← Ne]; rw [← norm_pos_iff] at h0
  have A : (fun n => (n : R) ^ k : Nat -> R) =o[atTop] fun n => (r₂ / ‖r₁‖) ^ n :=
    

中文:
定理 isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt
  结论: {R : 类型} [赋范环 R] (k : 自然数)
  证明: by
  by_cases h0 : r₁ = 0
  · refine (isLittleO_zero _ _).congr' (mem_atTop_sets.2 <| ⟨1, fun n hn => ?_⟩) EventuallyEq.rfl
    simp [zero_pow (one_le_iff_ne_zero.1 hn), h0]
  rw [← Ne]; rw [← norm_pos_iff] at h0
  have A : (fun n => (n : R) ^ k : Nat -> R) =o[atTop] fun n => (r₂ / ‖r₁‖) ^ n :=
    

Depends on / 依赖: A.mul_isBigO, EventuallyEq, EventuallyEq.rfl, div_pow, isLittleO_pow_const_const_pow_of_one_lt, isLittleO_zero, mem_atTop_sets, mul_isBigO, norm_pos_iff, of_norm_e, one_le_iff_ne_zero, one_lt_div, pow_pos, zero_pow
-/
theorem isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt {R : Type*} [NormedRing R] (k : Nat)
    {r₁ : R} {r₂ : Real} (h : ‖r₁‖ < r₂) :
    (fun n => (n : R) ^ k * r₁ ^ n : Nat -> R) =o[atTop] fun n => r₂ ^ n := by
  by_cases h0 : r₁ = 0
  · refine (isLittleO_zero _ _).congr' (mem_atTop_sets.2 <| ⟨1, fun n hn => ?_⟩) EventuallyEq.rfl
    simp [zero_pow (one_le_iff_ne_zero.1 hn), h0]
  rw [← Ne]; rw [← norm_pos_iff] at h0
  have A : (fun n => (n : R) ^ k : Nat -> R) =o[atTop] fun n => (r₂ / ‖r₁‖) ^ n :=
    isLittleO_pow_const_const_pow_of_one_lt k ((one_lt_div h0).2 h)
  suffices (fun n => r₁ ^ n) =O[atTop] fun n => ‖r₁‖ ^ n by
    simpa [div_mul_cancel₀ _ (pow_pos h0 _).ne', div_pow] using A.mul_isBigO this
exact .of_norm_eventuallyLE eventually_norm_pow_le r₁

/--
theorem `tendsto_pow_const_div_const_pow_of_one_lt` / 定理 `tendsto_pow_const_div_const_pow_of_one_lt`

English:
theorem tendsto_pow_const_div_const_pow_of_one_lt
  given: (k : Nat) {r : Real} (hr : 1 < r)
  proof: (isLittleO_pow_const_const_pow_of_one_lt k hr).tendsto_div_nhds_zero

中文:
定理 tendsto_pow_const_div_const_pow_of_one_lt
  条件: (k : 自然数) {r : 实数} (hr : 1 < r)
  证明: (isLittleO_pow_const_const_pow_of_one_lt k hr).tendsto_div_nhds_zero

Depends on / 依赖: isLittleO_pow_const_const_pow_of_one_lt, tendsto_div_nhds_zero
-/
theorem tendsto_pow_const_div_const_pow_of_one_lt (k : Nat) {r : Real} (hr : 1 < r) :
    Tendsto (fun n => (n : Real) ^ k / r ^ n : Nat -> Real) atTop (𝓝 0) :=
  (isLittleO_pow_const_const_pow_of_one_lt k hr).tendsto_div_nhds_zero

/--
theorem `tendsto_pow_const_mul_const_pow_of_abs_lt_one` / 定理 `tendsto_pow_const_mul_const_pow_of_abs_lt_one`

English:
theorem tendsto_pow_const_mul_const_pow_of_abs_lt_one
  given: (k : Nat) {r : Real} (hr : |r| < 1)
  proof: by
  by_cases h0 : r = 0
  · exact tendsto_const_nhds.congr'
      (mem_atTop_sets.2 ⟨1, fun n hn => by simp [zero_lt_one.trans_le hn |>.ne', h0]⟩)
  have hr' : 1 < |r|⁻¹ := (one_lt_inv₀ (abs_pos.2 h0)).2 hr
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa [div_eq_mul_inv] using tendsto_pow_const_d

中文:
定理 tendsto_pow_const_mul_const_pow_of_abs_lt_one
  条件: (k : 自然数) {r : 实数} (hr : |r| < 1)
  证明: by
  by_cases h0 : r = 0
  · exact tendsto_const_nhds.congr'
      (mem_atTop_sets.2 ⟨1, fun n hn => by simp [zero_lt_one.trans_le hn |>.ne', h0]⟩)
  have hr' : 1 < |r|⁻¹ := (one_lt_inv₀ (abs_pos.2 h0)).2 hr
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa [div_eq_mul_inv] using tendsto_pow_const_d

Depends on / 依赖: abs_pos, div_eq_mul_inv, mem_atTop_sets, tendsto_const_nhds, tendsto_const_nhds.congr, tendsto_pow_const_div_const_pow_of_one_lt, tendsto_zero_iff_norm_tendsto_zero, trans_le, zero_lt_one, zero_lt_one.trans_le
-/
theorem tendsto_pow_const_mul_const_pow_of_abs_lt_one (k : Nat) {r : Real} (hr : |r| < 1) :
    Tendsto (fun n => (n : Real) ^ k * r ^ n : Nat -> Real) atTop (𝓝 0) := by
  by_cases h0 : r = 0
  · exact tendsto_const_nhds.congr'
      (mem_atTop_sets.2 ⟨1, fun n hn => by simp [zero_lt_one.trans_le hn |>.ne', h0]⟩)
  have hr' : 1 < |r|⁻¹ := (one_lt_inv₀ (abs_pos.2 h0)).2 hr
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa [div_eq_mul_inv] using tendsto_pow_const_div_const_pow_of_one_lt k hr'

/--
lemma `tendsto_const_div_pow` / 引理 `tendsto_const_div_pow`

English:
lemma tendsto_const_div_pow
  given: (r : Real) (k : Nat) (hk : k != 0)
  proof: by
  simpa using Filter.Tendsto.const_div_atTop (tendsto_natCast_atTop_atTop (R := Real).comp
    (tendsto_pow_atTop hk)) r

中文:
引理 tendsto_const_div_pow
  条件: (r : 实数) (k : 自然数) (hk : k != 0)
  证明: by
  simpa using Filter.Tendsto.const_div_atTop (tendsto_natCast_atTop_atTop (R := Real).comp
    (tendsto_pow_atTop hk)) r

Depends on / 依赖: Filter, Filter.Tendsto.const_div_atTop, Tendsto, const_div_atTop, tendsto_natCast_atTop_atTop, tendsto_pow_atTop
-/
lemma tendsto_const_div_pow (r : Real) (k : Nat) (hk : k != 0) :
    Tendsto (fun n : Nat => r / n ^ k) atTop (𝓝 0) := by
  simpa using Filter.Tendsto.const_div_atTop (tendsto_natCast_atTop_atTop (R := Real).comp
    (tendsto_pow_atTop hk)) r

/--
theorem `tendsto_pow_const_mul_const_pow_of_lt_one` / 定理 `tendsto_pow_const_mul_const_pow_of_lt_one`

English:
theorem tendsto_pow_const_mul_const_pow_of_lt_one
  given: (k : Nat) {r : Real} (hr : 0 <= r) (h'r : r < 1)
  proof: tendsto_pow_const_mul_const_pow_of_abs_lt_one k (abs_lt.2 ⟨neg_one_lt_zero.trans_le hr, h'r⟩)

中文:
定理 tendsto_pow_const_mul_const_pow_of_lt_one
  条件: (k : 自然数) {r : 实数} (hr : 0 <= r) (h'r : r < 1)
  证明: tendsto_pow_const_mul_const_pow_of_abs_lt_one k (abs_lt.2 ⟨neg_one_lt_zero.trans_le hr, h'r⟩)

Depends on / 依赖: abs_lt, neg_one_lt_zero, neg_one_lt_zero.trans_le, tendsto_pow_const_mul_const_pow_of_abs_lt_one, trans_le
-/
theorem tendsto_pow_const_mul_const_pow_of_lt_one (k : Nat) {r : Real} (hr : 0 <= r) (h'r : r < 1) :
    Tendsto (fun n => (n : Real) ^ k * r ^ n : Nat -> Real) atTop (𝓝 0) :=
  tendsto_pow_const_mul_const_pow_of_abs_lt_one k (abs_lt.2 ⟨neg_one_lt_zero.trans_le hr, h'r⟩)

/--
theorem `tendsto_self_mul_const_pow_of_abs_lt_one` / 定理 `tendsto_self_mul_const_pow_of_abs_lt_one`

English:
theorem tendsto_self_mul_const_pow_of_abs_lt_one
  given: {r : Real} (hr : |r| < 1)
  proof: by
  simpa only [pow_one] using tendsto_pow_const_mul_const_pow_of_abs_lt_one 1 hr

中文:
定理 tendsto_self_mul_const_pow_of_abs_lt_one
  条件: {r : 实数} (hr : |r| < 1)
  证明: by
  simpa only [pow_one] using tendsto_pow_const_mul_const_pow_of_abs_lt_one 1 hr

Depends on / 依赖: pow_one, tendsto_pow_const_mul_const_pow_of_abs_lt_one
-/
theorem tendsto_self_mul_const_pow_of_abs_lt_one {r : Real} (hr : |r| < 1) :
    Tendsto (fun n => n * r ^ n : Nat -> Real) atTop (𝓝 0) := by
  simpa only [pow_one] using tendsto_pow_const_mul_const_pow_of_abs_lt_one 1 hr

/--
theorem `tendsto_self_mul_const_pow_of_lt_one` / 定理 `tendsto_self_mul_const_pow_of_lt_one`

English:
theorem tendsto_self_mul_const_pow_of_lt_one
  given: {r : Real} (hr : 0 <= r) (h'r : r < 1)
  proof: by
  simpa only [pow_one] using tendsto_pow_const_mul_const_pow_of_lt_one 1 hr h'r

中文:
定理 tendsto_self_mul_const_pow_of_lt_one
  条件: {r : 实数} (hr : 0 <= r) (h'r : r < 1)
  证明: by
  simpa only [pow_one] using tendsto_pow_const_mul_const_pow_of_lt_one 1 hr h'r

Depends on / 依赖: pow_one, tendsto_pow_const_mul_const_pow_of_lt_one
-/
theorem tendsto_self_mul_const_pow_of_lt_one {r : Real} (hr : 0 <= r) (h'r : r < 1) :
    Tendsto (fun n => n * r ^ n : Nat -> Real) atTop (𝓝 0) := by
  simpa only [pow_one] using tendsto_pow_const_mul_const_pow_of_lt_one 1 hr h'r

/--
theorem `tendsto_pow_atTop_nhds_zero_of_norm_lt_one` / 定理 `tendsto_pow_atTop_nhds_zero_of_norm_lt_one`

English:
theorem tendsto_pow_atTop_nhds_zero_of_norm_lt_one
  statement: {R : Type*} [SeminormedRing R] {x : R}
  proof: by
  apply squeeze_zero_norm' (eventually_norm_pow_le x)
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) h

中文:
定理 tendsto_pow_atTop_nhds_zero_of_norm_lt_one
  结论: {R : 类型} [Seminormed环 R] {x : R}
  证明: by
  apply squeeze_zero_norm' (eventually_norm_pow_le x)
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) h

Depends on / 依赖: eventually_norm_pow_le, norm_nonneg, squeeze_zero_norm, tendsto_pow_atTop_nhds_zero_of_lt_one
-/
theorem tendsto_pow_atTop_nhds_zero_of_norm_lt_one {R : Type*} [SeminormedRing R] {x : R}
    (h : ‖x‖ < 1) :
    Tendsto (fun n : Nat => x ^ n) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (eventually_norm_pow_le x)
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) h

/--
theorem `tendsto_pow_atTop_nhds_zero_of_abs_lt_one` / 定理 `tendsto_pow_atTop_nhds_zero_of_abs_lt_one`

English:
theorem tendsto_pow_atTop_nhds_zero_of_abs_lt_one
  given: {r : Real} (h : |r| < 1)
  proof: tendsto_pow_atTop_nhds_zero_of_norm_lt_one h

中文:
定理 tendsto_pow_atTop_nhds_zero_of_abs_lt_one
  条件: {r : 实数} (h : |r| < 1)
  证明: tendsto_pow_atTop_nhds_zero_of_norm_lt_one h

Depends on / 依赖: tendsto_pow_atTop_nhds_zero_of_norm_lt_one
-/
theorem tendsto_pow_atTop_nhds_zero_of_abs_lt_one {r : Real} (h : |r| < 1) :
    Tendsto (fun n : Nat => r ^ n) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_norm_lt_one h

/--
lemma `tendsto_pow_atTop_nhds_zero_iff_norm_lt_one` / 引理 `tendsto_pow_atTop_nhds_zero_iff_norm_lt_one`

English:
lemma tendsto_pow_atTop_nhds_zero_iff_norm_lt_one
  statement: {R : Type*} [SeminormedRing R] [NormMulClass R]
  proof: by
  -- this proof is slightly fiddly since `‖x ^ n‖ = ‖x‖ ^ n` might not hold for `n = 0`
  refine ⟨?_, tendsto_pow_atTop_nhds_zero_of_norm_lt_one⟩
  rw [← abs_of_nonneg (norm_nonneg _)]; rw [← tendsto_pow_atTop_nhds_zero_iff]; rw [tendsto_zero_iff_norm_tendsto_zero]
  apply Tendsto.congr'
  filter

中文:
引理 tendsto_pow_atTop_nhds_zero_iff_norm_lt_one
  结论: {R : 类型} [Seminormed环 R] [NormMul类 R]
  证明: by
  -- this proof is slightly fiddly since `‖x ^ n‖ = ‖x‖ ^ n` might not hold for `n = 0`
  refine ⟨?_, tendsto_pow_atTop_nhds_zero_of_norm_lt_one⟩
  rw [← abs_of_nonneg (norm_nonneg _)]; rw [← tendsto_pow_atTop_nhds_zero_iff]; rw [tendsto_zero_iff_norm_tendsto_zero]
  apply Tendsto.congr'
  filter
-/
lemma tendsto_pow_atTop_nhds_zero_iff_norm_lt_one {R : Type*} [SeminormedRing R] [NormMulClass R]
    {x : R} : Tendsto (fun n : Nat => x ^ n) atTop (𝓝 0) ↔ ‖x‖ < 1 := by
  -- this proof is slightly fiddly since `‖x ^ n‖ = ‖x‖ ^ n` might not hold for `n = 0`
  refine ⟨?_, tendsto_pow_atTop_nhds_zero_of_norm_lt_one⟩
  rw [← abs_of_nonneg (norm_nonneg _)]; rw [← tendsto_pow_atTop_nhds_zero_iff]; rw [tendsto_zero_iff_norm_tendsto_zero]
  apply Tendsto.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn IH => simp [pow_succ, IH]

variable {R S : Type*} [Field R] [Field S] [LinearOrder S] {v w : AbsoluteValue R S}
  [TopologicalSpace S] [IsStrictOrderedRing S] [Archimedean S] [_i : OrderTopology S]

/--
theorem `AbsoluteValue.tendsto_div_one_add_pow_nhds_one` / 定理 `AbsoluteValue.tendsto_div_one_add_pow_nhds_one`

English:
theorem AbsoluteValue.tendsto_div_one_add_pow_nhds_one
  statement: {v : AbsoluteValue R S} {a : R}
  proof: by
  simp_rw [map_div₀ v, v.map_one]
  apply one_div_one (G := S) ▸ Tendsto.div tendsto_const_nhds _ one_ne_zero
  have h_add := (tendsto_pow_atTop_nhds_zero_of_lt_one (v.nonneg _) ha).const_add 1
  have h_sub := (tendsto_pow_atTop_nhds_zero_of_lt_one (v.nonneg _) ha).const_sub 1
  exact tendsto_of_

中文:
定理 绝对值.tendsto_div_one_add_pow_nhds_one
  结论: {v : 绝对值 R S} {a : R}
  证明: by
  simp_rw [map_div₀ v, v.map_one]
  apply one_div_one (G := S) ▸ Tendsto.div tendsto_const_nhds _ one_ne_zero
  have h_add := (tendsto_pow_atTop_nhds_zero_of_lt_one (v.nonneg _) ha).const_add 1
  have h_sub := (tendsto_pow_atTop_nhds_zero_of_lt_one (v.nonneg _) ha).const_sub 1
  exact tendsto_of_

Depends on / 依赖: Tendsto, Tendsto.div, add_le, const_add, const_sub, h_add, h_sub, le_add, le_trans, map_one, nonneg, one_div_one, one_ne_zero, simp_rw, tendsto_const_nhds, tendsto_of_tendsto_of_tendsto_of_le_of_le, tendsto_pow_atTop_nhds_zero_of_lt_one, v.add_le, v.le_add, v.map_one
-/
theorem AbsoluteValue.tendsto_div_one_add_pow_nhds_one {v : AbsoluteValue R S} {a : R}
    (ha : v a < 1) : atTop.Tendsto (fun (n : Nat) => v (1 / (1 + a ^ n))) (𝓝 1) := by
  simp_rw [map_div₀ v, v.map_one]
  apply one_div_one (G := S) ▸ Tendsto.div tendsto_const_nhds _ one_ne_zero
  have h_add := (tendsto_pow_atTop_nhds_zero_of_lt_one (v.nonneg _) ha).const_add 1
  have h_sub := (tendsto_pow_atTop_nhds_zero_of_lt_one (v.nonneg _) ha).const_sub 1
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le (by simpa using h_sub) (by simpa using h_add)
    (fun n => le_trans (by simp) (v.le_add _ _))
    (fun n => le_trans (v.add_le _ _) (by simp))

/--
theorem `AbsoluteValue.tendsto_div_one_add_pow_nhds_zero` / 定理 `AbsoluteValue.tendsto_div_one_add_pow_nhds_zero`

English:
theorem AbsoluteValue.tendsto_div_one_add_pow_nhds_zero
  statement: {v : AbsoluteValue R S} {a : R}
  proof: by
  simp_rw [div_eq_mul_inv, one_mul, map_inv₀, fun n => add_comm 1 (a ^ n)]
  refine (tendsto_atTop_mono (fun n => v.le_add _ _) ?_).inv_tendsto_atTop
  simpa using (tendsto_atTop_add_right_of_le _ _ (tendsto_pow_atTop_atTop_of_one_lt ha)
    (fun _ => le_rfl)).congr fun n => (sub_eq_add_neg (v a 

中文:
定理 绝对值.tendsto_div_one_add_pow_nhds_zero
  结论: {v : 绝对值 R S} {a : R}
  证明: by
  simp_rw [div_eq_mul_inv, one_mul, map_inv₀, fun n => add_comm 1 (a ^ n)]
  refine (tendsto_atTop_mono (fun n => v.le_add _ _) ?_).inv_tendsto_atTop
  simpa using (tendsto_atTop_add_right_of_le _ _ (tendsto_pow_atTop_atTop_of_one_lt ha)
    (fun _ => le_rfl)).congr fun n => (sub_eq_add_neg (v a 

Depends on / 依赖: add_comm, div_eq_mul_inv, inv_tendsto_atTop, le_add, le_rfl, one_mul, simp_rw, sub_eq_add_neg, tendsto_atTop_add_right_of_le, tendsto_atTop_mono, tendsto_pow_atTop_atTop_of_one_lt, v.le_add
-/
theorem AbsoluteValue.tendsto_div_one_add_pow_nhds_zero {v : AbsoluteValue R S} {a : R}
    (ha : 1 < v a) : Filter.Tendsto (fun (n : Nat) => v (1 / (1 + a ^ n))) Filter.atTop (𝓝 0) := by
  simp_rw [div_eq_mul_inv, one_mul, map_inv₀, fun n => add_comm 1 (a ^ n)]
  refine (tendsto_atTop_mono (fun n => v.le_add _ _) ?_).inv_tendsto_atTop
  simpa using (tendsto_atTop_add_right_of_le _ _ (tendsto_pow_atTop_atTop_of_one_lt ha)
    (fun _ => le_rfl)).congr fun n => (sub_eq_add_neg (v a ^ n) 1).symm

/-! ### Geometric series -/

/--
Definition of `HasSummableGeomSeries` / `HasSummableGeomSeries` 的定义

English:
class HasSummableGeomSeries
  parameters: (K : Type*) [NormedRing K]
  axioms and operations (1):
    - summable_geometric_of_norm_lt_one : forall (ξ : K), ‖ξ‖ < 1 -> Summable (fun n => ξ ^ n)

中文:
类 有SummableGeomSeries
  参数: (K : 类型) [赋范环 K]
  公理与运算 (1 个):
    - summable_geometric_of_norm_lt_one : 对任意 (ξ : K), ‖ξ‖ < 1 -> Summable (fun n => ξ ^ n)
-/
class HasSummableGeomSeries (K : Type*) [NormedRing K] : Prop where
  summable_geometric_of_norm_lt_one : forall (ξ : K), ‖ξ‖ < 1 -> Summable (fun n => ξ ^ n)

/--
lemma `summable_geometric_of_norm_lt_one` / 引理 `summable_geometric_of_norm_lt_one`

English:
lemma summable_geometric_of_norm_lt_one
  statement: {K : Type*} [NormedRing K] [HasSummableGeomSeries K]
  proof: HasSummableGeomSeries.summable_geometric_of_norm_lt_one x h

中文:
引理 summable_geometric_of_norm_lt_one
  结论: {K : 类型} [赋范环 K] [有SummableGeomSeries K]
  证明: HasSummableGeomSeries.summable_geometric_of_norm_lt_one x h

Depends on / 依赖: HasSummableGeomSeries, HasSummableGeomSeries.summable_geometric_of_norm_lt_one, summable_geometric_of_norm_lt_one
-/
lemma summable_geometric_of_norm_lt_one {K : Type*} [NormedRing K] [HasSummableGeomSeries K]
    {x : K} (h : ‖x‖ < 1) : Summable (fun n => x ^ n) :=
  HasSummableGeomSeries.summable_geometric_of_norm_lt_one x h

instance {R : Type*} [NormedRing R] [CompleteSpace R] : HasSummableGeomSeries R := by
  constructor
  intro x hx
  have h1 : Summable fun n : Nat => ‖x‖ ^ n := summable_geometric_of_lt_one (norm_nonneg _) hx
  exact h1.of_norm_bounded_eventually_nat (eventually_norm_pow_le x)

section HasSummableGeometricSeries

variable {R : Type*} [NormedRing R]

open NormedSpace

/--
theorem `tsum_geometric_le_of_norm_lt_one` / 定理 `tsum_geometric_le_of_norm_lt_one`

English:
theorem tsum_geometric_le_of_norm_lt_one
  given: (x : R) (h : ‖x‖ < 1)
  proof: by
  by_cases hx : Summable (fun n => x ^ n)
  · rw [hx.tsum_eq_zero_add]
    simp only [_root_.pow_zero]
    refine le_trans (norm_add_le _ _) ?_
    have : ‖∑' b : Nat, (fun n => x ^ (n + 1)) b‖ <= (1 - ‖x‖)⁻¹ - 1 := by
      refine tsum_of_norm_bounded ?_ fun b => norm_pow_le' _ (Nat.succ_pos b)


中文:
定理 tsum_geometric_le_of_norm_lt_one
  条件: (x : R) (h : ‖x‖ < 1)
  证明: by
  by_cases hx : Summable (fun n => x ^ n)
  · rw [hx.tsum_eq_zero_add]
    simp only [_root_.pow_zero]
    refine le_trans (norm_add_le _ _) ?_
    have : ‖∑' b : Nat, (fun n => x ^ (n + 1)) b‖ <= (1 - ‖x‖)⁻¹ - 1 := by
      refine tsum_of_norm_bounded ?_ fun b => norm_pow_le' _ (Nat.succ_pos b)


Depends on / 依赖: Nat.succ_pos, Summable, _root_, _root_.pow_zero, convert, hasSum_geometric_of_lt_one, hasSum_nat_add_iff, hx.tsum_eq_zero_add, le_trans, nontriviality, norm_add_le, norm_nonneg, norm_pow_le, norm_zero, one_le_norm_one, pow_zero, succ_pos, tsum_eq_zero_add, tsum_eq_zero_of_not_summable, tsum_of_norm_bounded
-/
theorem tsum_geometric_le_of_norm_lt_one (x : R) (h : ‖x‖ < 1) :
    ‖∑' n : Nat, x ^ n‖ <= ‖(1 : R)‖ - 1 + (1 - ‖x‖)⁻¹ := by
  by_cases hx : Summable (fun n => x ^ n)
  · rw [hx.tsum_eq_zero_add]
    simp only [_root_.pow_zero]
    refine le_trans (norm_add_le _ _) ?_
    have : ‖∑' b : Nat, (fun n => x ^ (n + 1)) b‖ <= (1 - ‖x‖)⁻¹ - 1 := by
      refine tsum_of_norm_bounded ?_ fun b => norm_pow_le' _ (Nat.succ_pos b)
      convert! (hasSum_nat_add_iff' 1).mpr (hasSum_geometric_of_lt_one (norm_nonneg x) h)
      simp
    linarith
  · simp only [tsum_eq_zero_of_not_summable hx, norm_zero]
    nontriviality R
    have : 1 <= ‖(1 : R)‖ := one_le_norm_one R
    have : 0 <= (1 - ‖x‖)⁻¹ := inv_nonneg.2 (by linarith)
    linarith

variable [HasSummableGeomSeries R]

/--
theorem `geom_series_mul_neg` / 定理 `geom_series_mul_neg`

English:
theorem geom_series_mul_neg
  given: (x : R) (h : ‖x‖ < 1)
  statement: (∑' i : Nat, x ^ i) * (1 - x) = 1
  proof: (summable_geometric_of_norm_lt_one h).tsum_pow_mul_one_sub

中文:
定理 geom_series_mul_neg
  条件: (x : R) (h : ‖x‖ < 1)
  结论: (∑' i : 自然数, x ^ i) * (1 - x) = 1
  证明: (summable_geometric_of_norm_lt_one h).tsum_pow_mul_one_sub

Depends on / 依赖: summable_geometric_of_norm_lt_one, tsum_pow_mul_one_sub
-/
theorem geom_series_mul_neg (x : R) (h : ‖x‖ < 1) : (∑' i : Nat, x ^ i) * (1 - x) = 1 :=
  (summable_geometric_of_norm_lt_one h).tsum_pow_mul_one_sub

/--
theorem `mul_neg_geom_series` / 定理 `mul_neg_geom_series`

English:
theorem mul_neg_geom_series
  given: (x : R) (h : ‖x‖ < 1)
  statement: (1 - x) * ∑' i : Nat, x ^ i = 1
  proof: (summable_geometric_of_norm_lt_one h).one_sub_mul_tsum_pow

中文:
定理 mul_neg_geom_series
  条件: (x : R) (h : ‖x‖ < 1)
  结论: (1 - x) * ∑' i : 自然数, x ^ i = 1
  证明: (summable_geometric_of_norm_lt_one h).one_sub_mul_tsum_pow

Depends on / 依赖: one_sub_mul_tsum_pow, summable_geometric_of_norm_lt_one
-/
theorem mul_neg_geom_series (x : R) (h : ‖x‖ < 1) : (1 - x) * ∑' i : Nat, x ^ i = 1 :=
  (summable_geometric_of_norm_lt_one h).one_sub_mul_tsum_pow

/--
theorem `geom_series_succ` / 定理 `geom_series_succ`

English:
theorem geom_series_succ
  given: (x : R) (h : ‖x‖ < 1)
  statement: ∑' i : Nat, x ^ (i + 1) = ∑' i : Nat, x ^ i - 1
  proof: by
  rw [eq_sub_iff_add_eq]; rw [(summable_geometric_of_norm_lt_one h).tsum_eq_zero_add]; rw [pow_zero]; rw [add_comm]

中文:
定理 geom_series_succ
  条件: (x : R) (h : ‖x‖ < 1)
  结论: ∑' i : 自然数, x ^ (i + 1) = ∑' i : 自然数, x ^ i - 1
  证明: by
  rw [eq_sub_iff_add_eq]; rw [(summable_geometric_of_norm_lt_one h).tsum_eq_zero_add]; rw [pow_zero]; rw [add_comm]

Depends on / 依赖: add_comm, eq_sub_iff_add_eq, pow_zero, summable_geometric_of_norm_lt_one, tsum_eq_zero_add
-/
theorem geom_series_succ (x : R) (h : ‖x‖ < 1) : ∑' i : Nat, x ^ (i + 1) = ∑' i : Nat, x ^ i - 1 := by
  rw [eq_sub_iff_add_eq]; rw [(summable_geometric_of_norm_lt_one h).tsum_eq_zero_add]; rw [pow_zero]; rw [add_comm]

/--
theorem `geom_series_mul_shift` / 定理 `geom_series_mul_shift`

English:
theorem geom_series_mul_shift
  given: (x : R) (h : ‖x‖ < 1)
  proof: by
  simp_rw [← (summable_geometric_of_norm_lt_one h).tsum_mul_left, ← _root_.pow_succ']

中文:
定理 geom_series_mul_shift
  条件: (x : R) (h : ‖x‖ < 1)
  证明: by
  simp_rw [← (summable_geometric_of_norm_lt_one h).tsum_mul_left, ← _root_.pow_succ']

Depends on / 依赖: _root_, _root_.pow_succ, pow_succ, simp_rw, summable_geometric_of_norm_lt_one, tsum_mul_left
-/
theorem geom_series_mul_shift (x : R) (h : ‖x‖ < 1) :
    x * ∑' i : Nat, x ^ i = ∑' i : Nat, x ^ (i + 1) := by
  simp_rw [← (summable_geometric_of_norm_lt_one h).tsum_mul_left, ← _root_.pow_succ']

/--
theorem `geom_series_mul_one_add` / 定理 `geom_series_mul_one_add`

English:
theorem geom_series_mul_one_add
  given: (x : R) (h : ‖x‖ < 1)
  proof: by
  rw [add_mul]; rw [one_mul]; rw [geom_series_mul_shift x h]; rw [geom_series_succ x h]; rw [two_mul]; rw [add_sub_assoc]

中文:
定理 geom_series_mul_one_add
  条件: (x : R) (h : ‖x‖ < 1)
  证明: by
  rw [add_mul]; rw [one_mul]; rw [geom_series_mul_shift x h]; rw [geom_series_succ x h]; rw [two_mul]; rw [add_sub_assoc]

Depends on / 依赖: add_mul, add_sub_assoc, geom_series_mul_shift, geom_series_succ, one_mul, two_mul
-/
theorem geom_series_mul_one_add (x : R) (h : ‖x‖ < 1) :
    (1 + x) * ∑' i : Nat, x ^ i = 2 * ∑' i : Nat, x ^ i - 1 := by
  rw [add_mul]; rw [one_mul]; rw [geom_series_mul_shift x h]; rw [geom_series_succ x h]; rw [two_mul]; rw [add_sub_assoc]

/-- In a normed ring with summable geometric series, a perturbation of `1` by an element `t`
of distance less than `1` from `1` is a unit. Here we construct its `Units` structure. -/
@[simps val]
/--
Definition of `Units.oneSub` / `Units.oneSub` 的定义

English:
definition Units.oneSub
  signature: (t : R) (h : ‖t‖ < 1)
  body: 1 - t
  inv := ∑' n : Nat, t ^ n
  val_inv := mul_neg_geom_series t h
  inv_val := geom_series_mul_neg t h

中文:
定义 单位群.oneSub
  签名: (t : R) (h : ‖t‖ < 1)
  定义体: 1 - t
  inv := ∑' n : Nat, t ^ n
  val_inv := mul_neg_geom_series t h
  inv_val := geom_series_mul_neg t h
-/
def Units.oneSub (t : R) (h : ‖t‖ < 1) : Rˣ where
  val := 1 - t
  inv := ∑' n : Nat, t ^ n
  val_inv := mul_neg_geom_series t h
  inv_val := geom_series_mul_neg t h

/--
theorem `geom_series_eq_inverse` / 定理 `geom_series_eq_inverse`

English:
theorem geom_series_eq_inverse
  given: (x : R) (h : ‖x‖ < 1)
  proof: by
  change (Units.oneSub x h)⁻¹ = (1 - x)⁻¹ʳ
  rw [← Ring.inverse_unit]
  rfl

中文:
定理 geom_series_eq_inverse
  条件: (x : R) (h : ‖x‖ < 1)
  证明: by
  change (Units.oneSub x h)⁻¹ = (1 - x)⁻¹ʳ
  rw [← Ring.inverse_unit]
  rfl

Depends on / 依赖: Ring.inverse_unit, Units.oneSub, inverse_unit, oneSub
-/
theorem geom_series_eq_inverse (x : R) (h : ‖x‖ < 1) :
    ∑' i, x ^ i = (1 - x)⁻¹ʳ := by
  change (Units.oneSub x h)⁻¹ = (1 - x)⁻¹ʳ
  rw [← Ring.inverse_unit]
  rfl

/--
theorem `hasSum_geom_series_inverse` / 定理 `hasSum_geom_series_inverse`

English:
theorem hasSum_geom_series_inverse
  given: (x : R) (h : ‖x‖ < 1)
  proof: by
  convert! (summable_geometric_of_norm_lt_one h).hasSum
  exact (geom_series_eq_inverse x h).symm

中文:
定理 hasSum_geom_series_inverse
  条件: (x : R) (h : ‖x‖ < 1)
  证明: by
  convert! (summable_geometric_of_norm_lt_one h).hasSum
  exact (geom_series_eq_inverse x h).symm

Depends on / 依赖: convert, geom_series_eq_inverse, hasSum, summable_geometric_of_norm_lt_one
-/
theorem hasSum_geom_series_inverse (x : R) (h : ‖x‖ < 1) :
    HasSum (fun i => x ^ i) (1 - x)⁻¹ʳ := by
  convert! (summable_geometric_of_norm_lt_one h).hasSum
  exact (geom_series_eq_inverse x h).symm

/--
lemma `isUnit_one_sub_of_norm_lt_one` / 引理 `isUnit_one_sub_of_norm_lt_one`

English:
lemma isUnit_one_sub_of_norm_lt_one
  given: {x : R} (h : ‖x‖ < 1)
  statement: IsUnit (1 - x)
  proof: ⟨Units.oneSub x h, rfl⟩

中文:
引理 isUnit_one_sub_of_norm_lt_one
  条件: {x : R} (h : ‖x‖ < 1)
  结论: 是单位 (1 - x)
  证明: ⟨Units.oneSub x h, rfl⟩

Depends on / 依赖: Units.oneSub, oneSub
-/
lemma isUnit_one_sub_of_norm_lt_one {x : R} (h : ‖x‖ < 1) : IsUnit (1 - x) :=
  ⟨Units.oneSub x h, rfl⟩

end HasSummableGeometricSeries

section Geometric

variable {K : Type*} [NormedDivisionRing K] {ξ : K}

/--
theorem `hasSum_geometric_of_norm_lt_one` / 定理 `hasSum_geometric_of_norm_lt_one`

English:
theorem hasSum_geometric_of_norm_lt_one
  given: (h : ‖ξ‖ < 1)
  statement: HasSum (fun n : Nat => ξ ^ n) (1 - ξ)⁻¹
  proof: by
  have xi_ne_one : ξ != 1 := by
    contrapose! h
    simp [h]
  have A : Tendsto (fun n => (ξ ^ n - 1) * (ξ - 1)⁻¹) atTop (𝓝 ((0 - 1) * (ξ - 1)⁻¹)) :=
    ((tendsto_pow_atTop_nhds_zero_of_norm_lt_one h).sub tendsto_const_nhds).mul tendsto_const_nhds
  rw [hasSum_iff_tendsto_nat_of_summable_norm]

中文:
定理 hasSum_geometric_of_norm_lt_one
  条件: (h : ‖ξ‖ < 1)
  结论: HasSum (fun n : 自然数 => ξ ^ n) (1 - ξ)⁻¹
  证明: by
  have xi_ne_one : ξ != 1 := by
    contrapose! h
    simp [h]
  have A : Tendsto (fun n => (ξ ^ n - 1) * (ξ - 1)⁻¹) atTop (𝓝 ((0 - 1) * (ξ - 1)⁻¹)) :=
    ((tendsto_pow_atTop_nhds_zero_of_norm_lt_one h).sub tendsto_const_nhds).mul tendsto_const_nhds
  rw [hasSum_iff_tendsto_nat_of_summable_norm]

Depends on / 依赖: Tendsto, contrapose, div_eq_mul_inv, geom_sum_eq, hasSum_iff_tendsto_nat_of_summable_norm, neg_inv, norm_nonneg, norm_pow, summable_geometric_of_lt_one, tendsto_const_nhds, tendsto_pow_atTop_nhds_zero_of_norm_lt_one, xi_ne_one
-/
theorem hasSum_geometric_of_norm_lt_one (h : ‖ξ‖ < 1) : HasSum (fun n : Nat => ξ ^ n) (1 - ξ)⁻¹ := by
  have xi_ne_one : ξ != 1 := by
    contrapose! h
    simp [h]
  have A : Tendsto (fun n => (ξ ^ n - 1) * (ξ - 1)⁻¹) atTop (𝓝 ((0 - 1) * (ξ - 1)⁻¹)) :=
    ((tendsto_pow_atTop_nhds_zero_of_norm_lt_one h).sub tendsto_const_nhds).mul tendsto_const_nhds
  rw [hasSum_iff_tendsto_nat_of_summable_norm]
  · simpa [geom_sum_eq, xi_ne_one, neg_inv, div_eq_mul_inv] using A
  · simp [norm_pow, summable_geometric_of_lt_one (norm_nonneg _) h]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasSummableGeomSeries K
  body: ⟨fun _ h => (hasSum_geometric_of_norm_lt_one h).summable⟩

中文:
实例 :
  签名: 有SummableGeomSeries K
  定义体: ⟨fun _ h => (hasSum_geometric_of_norm_lt_one h).summable⟩

Depends on / 依赖: hasSum_geometric_of_norm_lt_one, infer_instance, map_id, p.map_id, summable
-/
instance : HasSummableGeomSeries K :=
  ⟨fun _ h => (hasSum_geometric_of_norm_lt_one h).summable⟩

/--
theorem `tsum_geometric_of_norm_lt_one` / 定理 `tsum_geometric_of_norm_lt_one`

English:
theorem tsum_geometric_of_norm_lt_one
  given: (h : ‖ξ‖ < 1)
  statement: ∑' n : Nat, ξ ^ n = (1 - ξ)⁻¹
  proof: (hasSum_geometric_of_norm_lt_one h).tsum_eq

中文:
定理 tsum_geometric_of_norm_lt_one
  条件: (h : ‖ξ‖ < 1)
  结论: ∑' n : 自然数, ξ ^ n = (1 - ξ)⁻¹
  证明: (hasSum_geometric_of_norm_lt_one h).tsum_eq

Depends on / 依赖: hasSum_geometric_of_norm_lt_one, tsum_eq
-/
theorem tsum_geometric_of_norm_lt_one (h : ‖ξ‖ < 1) : ∑' n : Nat, ξ ^ n = (1 - ξ)⁻¹ :=
  (hasSum_geometric_of_norm_lt_one h).tsum_eq

/--
theorem `hasSum_geometric_of_abs_lt_one` / 定理 `hasSum_geometric_of_abs_lt_one`

English:
theorem hasSum_geometric_of_abs_lt_one
  given: {r : Real} (h : |r| < 1)
  proof: hasSum_geometric_of_norm_lt_one h

中文:
定理 hasSum_geometric_of_abs_lt_one
  条件: {r : 实数} (h : |r| < 1)
  证明: hasSum_geometric_of_norm_lt_one h

Depends on / 依赖: hasSum_geometric_of_norm_lt_one
-/
theorem hasSum_geometric_of_abs_lt_one {r : Real} (h : |r| < 1) :
    HasSum (fun n : Nat => r ^ n) (1 - r)⁻¹ :=
  hasSum_geometric_of_norm_lt_one h

/--
theorem `summable_geometric_of_abs_lt_one` / 定理 `summable_geometric_of_abs_lt_one`

English:
theorem summable_geometric_of_abs_lt_one
  given: {r : Real} (h : |r| < 1)
  statement: Summable fun n : Nat => r ^ n
  proof: summable_geometric_of_norm_lt_one h

中文:
定理 summable_geometric_of_abs_lt_one
  条件: {r : 实数} (h : |r| < 1)
  结论: Summable fun n : 自然数 => r ^ n
  证明: summable_geometric_of_norm_lt_one h

Depends on / 依赖: summable_geometric_of_norm_lt_one
-/
theorem summable_geometric_of_abs_lt_one {r : Real} (h : |r| < 1) : Summable fun n : Nat => r ^ n :=
  summable_geometric_of_norm_lt_one h

/--
theorem `tsum_geometric_of_abs_lt_one` / 定理 `tsum_geometric_of_abs_lt_one`

English:
theorem tsum_geometric_of_abs_lt_one
  given: {r : Real} (h : |r| < 1)
  statement: ∑' n : Nat, r ^ n = (1 - r)⁻¹
  proof: tsum_geometric_of_norm_lt_one h

中文:
定理 tsum_geometric_of_abs_lt_one
  条件: {r : 实数} (h : |r| < 1)
  结论: ∑' n : 自然数, r ^ n = (1 - r)⁻¹
  证明: tsum_geometric_of_norm_lt_one h

Depends on / 依赖: tsum_geometric_of_norm_lt_one
-/
theorem tsum_geometric_of_abs_lt_one {r : Real} (h : |r| < 1) : ∑' n : Nat, r ^ n = (1 - r)⁻¹ :=
  tsum_geometric_of_norm_lt_one h

/-- A geometric series in a normed field is summable iff the norm of the common ratio is less than
one. -/
@[simp]
/--
theorem `summable_geometric_iff_norm_lt_one` / 定理 `summable_geometric_iff_norm_lt_one`

English:
theorem summable_geometric_iff_norm_lt_one
  statement: (Summable fun n : Nat => ξ ^ n) ↔ ‖ξ‖ < 1
  proof: by
  refine ⟨fun h => ?_, summable_geometric_of_norm_lt_one⟩
  obtain ⟨k : Nat, hk : dist (ξ ^ k) 0 < 1⟩ :=
    (h.tendsto_cofinite_zero.eventually (ball_mem_nhds _ zero_lt_one)).exists
  simp only [norm_pow, dist_zero_right] at hk
  rw [← one_pow k] at hk
  exact lt_of_pow_lt_pow_left₀ _ zero_le_on

中文:
定理 summable_geometric_iff_norm_lt_one
  结论: (Summable fun n : 自然数 => ξ ^ n) ↔ ‖ξ‖ < 1
  证明: by
  refine ⟨fun h => ?_, summable_geometric_of_norm_lt_one⟩
  obtain ⟨k : Nat, hk : dist (ξ ^ k) 0 < 1⟩ :=
    (h.tendsto_cofinite_zero.eventually (ball_mem_nhds _ zero_lt_one)).exists
  simp only [norm_pow, dist_zero_right] at hk
  rw [← one_pow k] at hk
  exact lt_of_pow_lt_pow_left₀ _ zero_le_on

Depends on / 依赖: ball_mem_nhds, dist_zero_right, eventually, h.tendsto_cofinite_zero.eventually, norm_pow, one_pow, summable_geometric_of_norm_lt_one, tendsto_cofinite_zero, zero_le_one, zero_lt_one
-/
theorem summable_geometric_iff_norm_lt_one : (Summable fun n : Nat => ξ ^ n) ↔ ‖ξ‖ < 1 := by
  refine ⟨fun h => ?_, summable_geometric_of_norm_lt_one⟩
  obtain ⟨k : Nat, hk : dist (ξ ^ k) 0 < 1⟩ :=
    (h.tendsto_cofinite_zero.eventually (ball_mem_nhds _ zero_lt_one)).exists
  simp only [norm_pow, dist_zero_right] at hk
  rw [← one_pow k] at hk
  exact lt_of_pow_lt_pow_left₀ _ zero_le_one hk

end Geometric

section MulGeometric

variable {R : Type*} [NormedRing R] {𝕜 : Type*} [NormedDivisionRing 𝕜]

/--
theorem `summable_norm_mul_geometric_of_norm_lt_one` / 定理 `summable_norm_mul_geometric_of_norm_lt_one`

English:
theorem summable_norm_mul_geometric_of_norm_lt_one
  statement: {k : Nat} {r : R}
  proof: by
  rcases exists_between hr with ⟨r', hrr', h⟩
  rw [← norm_norm] at hrr'
  apply summable_of_isBigO_nat (summable_geometric_of_lt_one ((norm_nonneg _).trans hrr'.le) h)
  calc
  fun n => ‖↑(u n) * r ^ n‖
  _ =O[atTop] fun n => u n * ‖r‖ ^ n := by
      apply (IsBigOWith.of_bound (c := ‖(1 : R)‖) 

中文:
定理 summable_norm_mul_geometric_of_norm_lt_one
  结论: {k : 自然数} {r : R}
  证明: by
  rcases exists_between hr with ⟨r', hrr', h⟩
  rw [← norm_norm] at hrr'
  apply summable_of_isBigO_nat (summable_geometric_of_lt_one ((norm_nonneg _).trans hrr'.le) h)
  calc
  fun n => ‖↑(u n) * r ^ n‖
  _ =O[atTop] fun n => u n * ‖r‖ ^ n := by
      apply (IsBigOWith.of_bound (c := ‖(1 : R)‖) 

Depends on / 依赖: IsBigOWith, IsBigOWith.of_bound, Real.norm_eq_abs, abs_cast, abs_norm, eventually_norm_pow_le, exists_between, filter_upwards, isBigO, norm_eq_abs, norm_mul, norm_mul_le, norm_nonneg, norm_norm, norm_pow, of_bound, summable_geometric_of_lt_one, summable_of_isBigO_nat
-/
theorem summable_norm_mul_geometric_of_norm_lt_one {k : Nat} {r : R}
    (hr : ‖r‖ < 1) {u : Nat -> Nat} (hu : (fun n => (u n : Real)) =O[atTop] (fun n => (↑(n ^ k) : Real))) :
    Summable fun n : Nat => ‖(u n * r ^ n : R)‖ := by
  rcases exists_between hr with ⟨r', hrr', h⟩
  rw [← norm_norm] at hrr'
  apply summable_of_isBigO_nat (summable_geometric_of_lt_one ((norm_nonneg _).trans hrr'.le) h)
  calc
  fun n => ‖↑(u n) * r ^ n‖
  _ =O[atTop] fun n => u n * ‖r‖ ^ n := by
      apply (IsBigOWith.of_bound (c := ‖(1 : R)‖) ?_).isBigO
      filter_upwards [eventually_norm_pow_le r] with n hn
      simp only [norm_mul, Real.norm_eq_abs, abs_cast, norm_pow, abs_norm]
      apply (norm_mul_le _ _).trans
      have : ‖(u n : R)‖ * ‖r ^ n‖ <= (u n * ‖(1 : R)‖) * ‖r‖ ^ n := by
        gcongr; exact norm_cast_le (u n)
      exact this.trans (le_of_eq (by ring))
  _ =O[atTop] fun n => ↑(n ^ k) * ‖r‖ ^ n := hu.mul (isBigO_refl _ _)
  _ =O[atTop] fun n => r' ^ n := by
      simp only [cast_pow]
      exact (isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt k hrr').isBigO

/--
theorem `summable_norm_pow_mul_geometric_of_norm_lt_one` / 定理 `summable_norm_pow_mul_geometric_of_norm_lt_one`

English:
theorem summable_norm_pow_mul_geometric_of_norm_lt_one
  statement: (k : Nat) {r : R}
  proof: by
  simp only [← cast_pow]
  exact summable_norm_mul_geometric_of_norm_lt_one (k := k) (u := fun n => n ^ k) hr
    (isBigO_refl _ _)

中文:
定理 summable_norm_pow_mul_geometric_of_norm_lt_one
  结论: (k : 自然数) {r : R}
  证明: by
  simp only [← cast_pow]
  exact summable_norm_mul_geometric_of_norm_lt_one (k := k) (u := fun n => n ^ k) hr
    (isBigO_refl _ _)

Depends on / 依赖: cast_pow, isBigO_refl, summable_norm_mul_geometric_of_norm_lt_one
-/
theorem summable_norm_pow_mul_geometric_of_norm_lt_one (k : Nat) {r : R}
    (hr : ‖r‖ < 1) : Summable fun n : Nat => ‖((n : R) ^ k * r ^ n : R)‖ := by
  simp only [← cast_pow]
  exact summable_norm_mul_geometric_of_norm_lt_one (k := k) (u := fun n => n ^ k) hr
    (isBigO_refl _ _)

/--
theorem `summable_norm_geometric_of_norm_lt_one` / 定理 `summable_norm_geometric_of_norm_lt_one`

English:
theorem summable_norm_geometric_of_norm_lt_one
  statement: {r : R}
  proof: by
  simpa using summable_norm_pow_mul_geometric_of_norm_lt_one 0 hr

中文:
定理 summable_norm_geometric_of_norm_lt_one
  结论: {r : R}
  证明: by
  simpa using summable_norm_pow_mul_geometric_of_norm_lt_one 0 hr

Depends on / 依赖: summable_norm_pow_mul_geometric_of_norm_lt_one
-/
theorem summable_norm_geometric_of_norm_lt_one {r : R}
    (hr : ‖r‖ < 1) : Summable fun n : Nat => ‖(r ^ n : R)‖ := by
  simpa using summable_norm_pow_mul_geometric_of_norm_lt_one 0 hr

variable [HasSummableGeomSeries R]

/--
lemma `hasSum_choose_mul_geometric_of_norm_lt_one'` / 引理 `hasSum_choose_mul_geometric_of_norm_lt_one'`

English:
lemma hasSum_choose_mul_geometric_of_norm_lt_one'
  proof: by
  induction k with
  | zero => simpa using hasSum_geom_series_inverse r hr
  | succ k ih =>
      have I1 : Summable (fun (n : Nat) => ‖(n + k).choose k * r ^ n‖) := by
        apply summable_norm_mul_geometric_of_norm_lt_one (k := k) hr
        apply isBigO_iff.2 ⟨2 ^ k, ?_⟩
        filter_upwar

中文:
引理 hasSum_choose_mul_geometric_of_norm_lt_one'
  证明: by
  induction k with
  | zero => simpa using hasSum_geom_series_inverse r hr
  | succ k ih =>
      have I1 : Summable (fun (n : Nat) => ‖(n + k).choose k * r ^ n‖) := by
        apply summable_norm_mul_geometric_of_norm_lt_one (k := k) hr
        apply isBigO_iff.2 ⟨2 ^ k, ?_⟩
        filter_upwar

Depends on / 依赖: Ioi_mem_atTop, Nat.choose_le_pow, Real.norm_eq_abs, Summable, abs_cast, cast_pow, choose_le_choose, choose_le_pow, filter_upwards, hasSum_geom_series_inverse, isBigO_iff, norm_eq_abs, norm_pow, summable_norm_mul_geometric_of_norm_lt_one
-/
lemma hasSum_choose_mul_geometric_of_norm_lt_one'
    (k : Nat) {r : R} (hr : ‖r‖ < 1) :
    HasSum (fun n => (n + k).choose k * r ^ n) ((1 - r)⁻¹ʳ ^ (k + 1)) := by
  induction k with
  | zero => simpa using hasSum_geom_series_inverse r hr
  | succ k ih =>
      have I1 : Summable (fun (n : Nat) => ‖(n + k).choose k * r ^ n‖) := by
        apply summable_norm_mul_geometric_of_norm_lt_one (k := k) hr
        apply isBigO_iff.2 ⟨2 ^ k, ?_⟩
        filter_upwards [Ioi_mem_atTop k] with n (hn : k < n)
        simp only [Real.norm_eq_abs, abs_cast, cast_pow, norm_pow]
        norm_cast
        calc (n + k).choose k
          _ <= (2 * n).choose k := choose_le_choose k (by lia)
          _ <= (2 * n) ^ k := Nat.choose_le_pow _ _
          _ = 2 ^ k * n ^ k := Nat.mul_pow 2 n k
      convert!
        hasSum_sum_range_mul_of_summable_norm' I1 ih.summable
          (summable_norm_geometric_of_norm_lt_one hr) (summable_geometric_of_norm_lt_one hr) with
        n
      · have : ∑ i in Finset.range (n + 1), ↑((i + k).choose k) * r ^ i * r ^ (n - i) =
            ∑ i in Finset.range (n + 1), ↑((i + k).choose k) * r ^ n := by
          apply Finset.sum_congr rfl (fun i hi => ?_)
          simp only [Finset.mem_range] at hi
          rw [mul_assoc]; rw [← pow_add]; rw [show i + (n - i) = n by lia]
        simp [this, ← sum_mul, ← Nat.cast_sum, sum_range_add_choose n k, add_assoc]
      · rw [ih.tsum_eq, (hasSum_geom_series_inverse r hr).tsum_eq, pow_succ]

/--
lemma `summable_choose_mul_geometric_of_norm_lt_one` / 引理 `summable_choose_mul_geometric_of_norm_lt_one`

English:
lemma summable_choose_mul_geometric_of_norm_lt_one
  given: (k : Nat) {r : R} (hr : ‖r‖ < 1)
  proof: (hasSum_choose_mul_geometric_of_norm_lt_one' k hr).summable

中文:
引理 summable_choose_mul_geometric_of_norm_lt_one
  条件: (k : 自然数) {r : R} (hr : ‖r‖ < 1)
  证明: (hasSum_choose_mul_geometric_of_norm_lt_one' k hr).summable

Depends on / 依赖: hasSum_choose_mul_geometric_of_norm_lt_one, summable
-/
lemma summable_choose_mul_geometric_of_norm_lt_one (k : Nat) {r : R} (hr : ‖r‖ < 1) :
    Summable (fun n => (n + k).choose k * r ^ n) :=
  (hasSum_choose_mul_geometric_of_norm_lt_one' k hr).summable

/--
lemma `tsum_choose_mul_geometric_of_norm_lt_one'` / 引理 `tsum_choose_mul_geometric_of_norm_lt_one'`

English:
lemma tsum_choose_mul_geometric_of_norm_lt_one'
  given: (k : Nat) {r : R} (hr : ‖r‖ < 1)
  proof: (hasSum_choose_mul_geometric_of_norm_lt_one' k hr).tsum_eq

中文:
引理 tsum_choose_mul_geometric_of_norm_lt_one'
  条件: (k : 自然数) {r : R} (hr : ‖r‖ < 1)
  证明: (hasSum_choose_mul_geometric_of_norm_lt_one' k hr).tsum_eq

Depends on / 依赖: hasSum_choose_mul_geometric_of_norm_lt_one, tsum_eq
-/
lemma tsum_choose_mul_geometric_of_norm_lt_one' (k : Nat) {r : R} (hr : ‖r‖ < 1) :
    ∑' n, (n + k).choose k * r ^ n = ((1 - r)⁻¹ʳ) ^ (k + 1) :=
  (hasSum_choose_mul_geometric_of_norm_lt_one' k hr).tsum_eq

/--
lemma `hasSum_choose_mul_geometric_of_norm_lt_one` / 引理 `hasSum_choose_mul_geometric_of_norm_lt_one`

English:
lemma hasSum_choose_mul_geometric_of_norm_lt_one
  proof: by
  convert! hasSum_choose_mul_geometric_of_norm_lt_one' k hr
  simp

中文:
引理 hasSum_choose_mul_geometric_of_norm_lt_one
  证明: by
  convert! hasSum_choose_mul_geometric_of_norm_lt_one' k hr
  simp

Depends on / 依赖: convert, hasSum_choose_mul_geometric_of_norm_lt_one
-/
lemma hasSum_choose_mul_geometric_of_norm_lt_one
    (k : Nat) {r : 𝕜} (hr : ‖r‖ < 1) :
    HasSum (fun n => (n + k).choose k * r ^ n) (1 / (1 - r) ^ (k + 1)) := by
  convert! hasSum_choose_mul_geometric_of_norm_lt_one' k hr
  simp

/--
lemma `tsum_choose_mul_geometric_of_norm_lt_one` / 引理 `tsum_choose_mul_geometric_of_norm_lt_one`

English:
lemma tsum_choose_mul_geometric_of_norm_lt_one
  given: (k : Nat) {r : 𝕜} (hr : ‖r‖ < 1)
  proof: (hasSum_choose_mul_geometric_of_norm_lt_one k hr).tsum_eq

中文:
引理 tsum_choose_mul_geometric_of_norm_lt_one
  条件: (k : 自然数) {r : 𝕜} (hr : ‖r‖ < 1)
  证明: (hasSum_choose_mul_geometric_of_norm_lt_one k hr).tsum_eq

Depends on / 依赖: hasSum_choose_mul_geometric_of_norm_lt_one, tsum_eq
-/
lemma tsum_choose_mul_geometric_of_norm_lt_one (k : Nat) {r : 𝕜} (hr : ‖r‖ < 1) :
    ∑' n, (n + k).choose k * r ^ n = 1 / (1 - r) ^ (k + 1) :=
  (hasSum_choose_mul_geometric_of_norm_lt_one k hr).tsum_eq

/--
lemma `summable_descFactorial_mul_geometric_of_norm_lt_one` / 引理 `summable_descFactorial_mul_geometric_of_norm_lt_one`

English:
lemma summable_descFactorial_mul_geometric_of_norm_lt_one
  given: (k : Nat) {r : R} (hr : ‖r‖ < 1)
  proof: by
  convert! (summable_choose_mul_geometric_of_norm_lt_one k hr).mul_left (k.factorial : R) using
    2 with n
  simp [← mul_assoc, descFactorial_eq_factorial_mul_choose (n + k) k]

中文:
引理 summable_descFactorial_mul_geometric_of_norm_lt_one
  条件: (k : 自然数) {r : R} (hr : ‖r‖ < 1)
  证明: by
  convert! (summable_choose_mul_geometric_of_norm_lt_one k hr).mul_left (k.factorial : R) using
    2 with n
  simp [← mul_assoc, descFactorial_eq_factorial_mul_choose (n + k) k]

Depends on / 依赖: convert, descFactorial_eq_factorial_mul_choose, factorial, k.factorial, mul_assoc, mul_left, summable_choose_mul_geometric_of_norm_lt_one
-/
lemma summable_descFactorial_mul_geometric_of_norm_lt_one (k : Nat) {r : R} (hr : ‖r‖ < 1) :
    Summable (fun n => (n + k).descFactorial k * r ^ n) := by
  convert! (summable_choose_mul_geometric_of_norm_lt_one k hr).mul_left (k.factorial : R) using
    2 with n
  simp [← mul_assoc, descFactorial_eq_factorial_mul_choose (n + k) k]

open Polynomial in
/--
theorem `summable_pow_mul_geometric_of_norm_lt_one` / 定理 `summable_pow_mul_geometric_of_norm_lt_one`

English:
theorem summable_pow_mul_geometric_of_norm_lt_one
  given: (k : Nat) {r : R} (hr : ‖r‖ < 1)
  proof: by
  refine Nat.strong_induction_on k fun k hk => ?_
  obtain ⟨a, ha⟩ : exists (a : Nat -> Nat), forall n, (n + k).descFactorial k
      = n ^ k + ∑ i in range k, a i * n ^ i := by
    let P : Polynomial Nat := (ascPochhammer Nat k).comp (Polynomial.X + C 1)
    refine ⟨fun i => P.coeff i, fun n => 

中文:
定理 summable_pow_mul_geometric_of_norm_lt_one
  条件: (k : 自然数) {r : R} (hr : ‖r‖ < 1)
  证明: by
  refine Nat.strong_induction_on k fun k hk => ?_
  obtain ⟨a, ha⟩ : exists (a : Nat -> Nat), forall n, (n + k).descFactorial k
      = n ^ k + ∑ i in range k, a i * n ^ i := by
    let P : Polynomial Nat := (ascPochhammer Nat k).comp (Polynomial.X + C 1)
    refine ⟨fun i => P.coeff i, fun n => 

Depends on / 依赖: Monic.comp_X_add_C, Nat.strong_induction_on, P.coeff, P.natDegree, Polynomial, Polynomial.X, ascPochhammer, ascPochhammer_natDegree, comp_X_add_C, descFactoria, descFactorial, monic_ascPochhammer, mul_one, natDegree, natDegree_X_add_C, natDegree_comp, strong_induction_on
-/
theorem summable_pow_mul_geometric_of_norm_lt_one (k : Nat) {r : R} (hr : ‖r‖ < 1) :
    Summable (fun n => (n : R) ^ k * r ^ n : Nat -> R) := by
  refine Nat.strong_induction_on k fun k hk => ?_
  obtain ⟨a, ha⟩ : exists (a : Nat -> Nat), forall n, (n + k).descFactorial k
      = n ^ k + ∑ i in range k, a i * n ^ i := by
    let P : Polynomial Nat := (ascPochhammer Nat k).comp (Polynomial.X + C 1)
    refine ⟨fun i => P.coeff i, fun n => ?_⟩
    have mP : Monic P := Monic.comp_X_add_C (monic_ascPochhammer Nat k) _
    have dP : P.natDegree = k := by
      simp only [P, natDegree_comp, ascPochhammer_natDegree, mul_one, natDegree_X_add_C]
    have A : (n + k).descFactorial k = P.eval n := by
      have : n + 1 + k - 1 = n + k := by lia
      simp [P, ascPochhammer_nat_eq_descFactorial, this]
    conv_lhs => rw [A, mP.as_sum, dP]
    simp [eval_finsetSum]
  have : Summable (fun n => (n + k).descFactorial k * r ^ n
      - ∑ i in range k, a i * n ^ (i : Nat) * r ^ n) := by
    apply (summable_descFactorial_mul_geometric_of_norm_lt_one k hr).sub
    apply summable_sum (fun i hi => ?_)
    simp_rw [mul_assoc]
    simp only [Finset.mem_range] at hi
    exact (hk _ hi).mul_left _
  convert! this using 1
  ext n
  simp [ha n, add_mul, sum_mul]

/--
theorem `hasSum_coe_mul_geometric_of_norm_lt_one'` / 定理 `hasSum_coe_mul_geometric_of_norm_lt_one'`

English:
theorem hasSum_coe_mul_geometric_of_norm_lt_one'
  proof: by
  have A : HasSum (fun (n : Nat) => (n + 1) * x ^ n) ((1 - x)⁻¹ʳ ^ 2) := by
    convert! hasSum_choose_mul_geometric_of_norm_lt_one' 1 h with n
    simp
  have B : HasSum (fun (n : Nat) => x ^ n) ((1 - x)⁻¹ʳ) := hasSum_geom_series_inverse x h
  convert! A.sub B using 1
  · ext n
    simp [add_mul

中文:
定理 hasSum_coe_mul_geometric_of_norm_lt_one'
  证明: by
  have A : HasSum (fun (n : Nat) => (n + 1) * x ^ n) ((1 - x)⁻¹ʳ ^ 2) := by
    convert! hasSum_choose_mul_geometric_of_norm_lt_one' 1 h with n
    simp
  have B : HasSum (fun (n : Nat) => x ^ n) ((1 - x)⁻¹ʳ) := hasSum_geom_series_inverse x h
  convert! A.sub B using 1
  · ext n
    simp [add_mul

Depends on / 依赖: A.sub, HasSum, Ring.mul_inverse_cancel, add_mul, convert, hasSum_choose_mul_geometric_of_norm_lt_one, hasSum_geom_series_inverse, isUnit_one_sub_of_norm_lt_one, mul_inverse_cancel, noncomm_ring
-/
theorem hasSum_coe_mul_geometric_of_norm_lt_one'
    {x : R} (h : ‖x‖ < 1) :
    HasSum (fun n => n * x ^ n : Nat -> R) (x * ((1 - x)⁻¹ʳ) ^ 2) := by
  have A : HasSum (fun (n : Nat) => (n + 1) * x ^ n) ((1 - x)⁻¹ʳ ^ 2) := by
    convert! hasSum_choose_mul_geometric_of_norm_lt_one' 1 h with n
    simp
  have B : HasSum (fun (n : Nat) => x ^ n) ((1 - x)⁻¹ʳ) := hasSum_geom_series_inverse x h
  convert! A.sub B using 1
  · ext n
    simp [add_mul]
  · symm
    calc (1 - x)⁻¹ʳ ^ 2 - (1 - x)⁻¹ʳ
    _ = (1 - x)⁻¹ʳ ^ 2 - ((1 - x) * (1 - x)⁻¹ʳ) * (1 - x)⁻¹ʳ := by
      simp [Ring.mul_inverse_cancel (1 - x) (isUnit_one_sub_of_norm_lt_one h)]
    _ = x * (1 - x)⁻¹ʳ ^ 2 := by noncomm_ring

/--
theorem `tsum_coe_mul_geometric_of_norm_lt_one'` / 定理 `tsum_coe_mul_geometric_of_norm_lt_one'`

English:
theorem tsum_coe_mul_geometric_of_norm_lt_one'
  proof: (hasSum_coe_mul_geometric_of_norm_lt_one' hr).tsum_eq

中文:
定理 tsum_coe_mul_geometric_of_norm_lt_one'
  证明: (hasSum_coe_mul_geometric_of_norm_lt_one' hr).tsum_eq

Depends on / 依赖: hasSum_coe_mul_geometric_of_norm_lt_one, tsum_eq
-/
theorem tsum_coe_mul_geometric_of_norm_lt_one'
    {r : 𝕜} (hr : ‖r‖ < 1) : (∑' n : Nat, n * r ^ n : 𝕜) = r * (1 - r)⁻¹ʳ ^ 2 :=
  (hasSum_coe_mul_geometric_of_norm_lt_one' hr).tsum_eq

/--
theorem `hasSum_coe_mul_geometric_of_norm_lt_one` / 定理 `hasSum_coe_mul_geometric_of_norm_lt_one`

English:
theorem hasSum_coe_mul_geometric_of_norm_lt_one
  given: {r : 𝕜} (hr : ‖r‖ < 1)
  proof: by
  convert! hasSum_coe_mul_geometric_of_norm_lt_one' hr using 1
  simp [div_eq_mul_inv]

中文:
定理 hasSum_coe_mul_geometric_of_norm_lt_one
  条件: {r : 𝕜} (hr : ‖r‖ < 1)
  证明: by
  convert! hasSum_coe_mul_geometric_of_norm_lt_one' hr using 1
  simp [div_eq_mul_inv]

Depends on / 依赖: convert, div_eq_mul_inv, hasSum_coe_mul_geometric_of_norm_lt_one
-/
theorem hasSum_coe_mul_geometric_of_norm_lt_one {r : 𝕜} (hr : ‖r‖ < 1) :
    HasSum (fun n => n * r ^ n : Nat -> 𝕜) (r / (1 - r) ^ 2) := by
  convert! hasSum_coe_mul_geometric_of_norm_lt_one' hr using 1
  simp [div_eq_mul_inv]

/--
theorem `tsum_coe_mul_geometric_of_norm_lt_one` / 定理 `tsum_coe_mul_geometric_of_norm_lt_one`

English:
theorem tsum_coe_mul_geometric_of_norm_lt_one
  given: {r : 𝕜} (hr : ‖r‖ < 1)
  proof: (hasSum_coe_mul_geometric_of_norm_lt_one hr).tsum_eq

中文:
定理 tsum_coe_mul_geometric_of_norm_lt_one
  条件: {r : 𝕜} (hr : ‖r‖ < 1)
  证明: (hasSum_coe_mul_geometric_of_norm_lt_one hr).tsum_eq

Depends on / 依赖: hasSum_coe_mul_geometric_of_norm_lt_one, tsum_eq
-/
theorem tsum_coe_mul_geometric_of_norm_lt_one {r : 𝕜} (hr : ‖r‖ < 1) :
    (∑' n : Nat, n * r ^ n : 𝕜) = r / (1 - r) ^ 2 :=
  (hasSum_coe_mul_geometric_of_norm_lt_one hr).tsum_eq

end MulGeometric

section SummableLeGeometric

variable [SeminormedAddCommGroup α] {r C : Real} {f : Nat -> α}

nonrec theorem SeminormedAddCommGroup.cauchySeq_of_le_geometric {C : Real} {r : Real} (hr : r < 1)
    {u : Nat -> α} (h : forall n, ‖u n - u (n + 1)‖ <= C * r ^ n) : CauchySeq u :=
  cauchySeq_of_le_geometric r C hr (by simpa [dist_eq_norm] using h)

/--
theorem `dist_partial_sum_le_of_le_geometric` / 定理 `dist_partial_sum_le_of_le_geometric`

English:
theorem dist_partial_sum_le_of_le_geometric
  given: (hf : forall n, ‖f n‖ <= C * r ^ n) (n : Nat)
  proof: by
  rw [sum_range_succ]; rw [dist_eq_norm]; rw [← norm_neg]; rw [neg_sub]; rw [add_sub_cancel_left]
  exact hf n

中文:
定理 dist_partial_sum_le_of_le_geometric
  条件: (hf : 对任意 n, ‖f n‖ <= C * r ^ n) (n : 自然数)
  证明: by
  rw [sum_range_succ]; rw [dist_eq_norm]; rw [← norm_neg]; rw [neg_sub]; rw [add_sub_cancel_left]
  exact hf n

Depends on / 依赖: add_sub_cancel_left, dist_eq_norm, neg_sub, norm_neg, sum_range_succ
-/
theorem dist_partial_sum_le_of_le_geometric (hf : forall n, ‖f n‖ <= C * r ^ n) (n : Nat) :
    dist (∑ i in range n, f i) (∑ i in range (n + 1), f i) <= C * r ^ n := by
  rw [sum_range_succ]; rw [dist_eq_norm]; rw [← norm_neg]; rw [neg_sub]; rw [add_sub_cancel_left]
  exact hf n

/--
theorem `cauchySeq_finset_of_geometric_bound` / 定理 `cauchySeq_finset_of_geometric_bound`

English:
theorem cauchySeq_finset_of_geometric_bound
  given: (hr : r < 1) (hf : forall n, ‖f n‖ <= C * r ^ n)
  proof: cauchySeq_finset_of_norm_bounded
    (aux_hasSum_of_le_geometric hr (dist_partial_sum_le_of_le_geometric hf)).summable hf

中文:
定理 cauchySeq_finset_of_geometric_bound
  条件: (hr : r < 1) (hf : 对任意 n, ‖f n‖ <= C * r ^ n)
  证明: cauchySeq_finset_of_norm_bounded
    (aux_hasSum_of_le_geometric hr (dist_partial_sum_le_of_le_geometric hf)).summable hf

Depends on / 依赖: aux_hasSum_of_le_geometric, cauchySeq_finset_of_norm_bounded, dist_partial_sum_le_of_le_geometric, summable
-/
theorem cauchySeq_finset_of_geometric_bound (hr : r < 1) (hf : forall n, ‖f n‖ <= C * r ^ n) :
    CauchySeq fun s : Finset Nat => ∑ x in s, f x :=
  cauchySeq_finset_of_norm_bounded
    (aux_hasSum_of_le_geometric hr (dist_partial_sum_le_of_le_geometric hf)).summable hf

/--
theorem `norm_sub_le_of_geometric_bound_of_hasSum` / 定理 `norm_sub_le_of_geometric_bound_of_hasSum`

English:
theorem norm_sub_le_of_geometric_bound_of_hasSum
  statement: (hr : r < 1) (hf : forall n, ‖f n‖ <= C * r ^ n) {a : α}
  proof: by
  rw [← dist_eq_norm]
  apply dist_le_of_le_geometric_of_tendsto r C hr (dist_partial_sum_le_of_le_geometric hf)
  exact ha.tendsto_sum_nat

@[simp]

中文:
定理 norm_sub_le_of_geometric_bound_of_hasSum
  结论: (hr : r < 1) (hf : 对任意 n, ‖f n‖ <= C * r ^ n) {a : α}
  证明: by
  rw [← dist_eq_norm]
  apply dist_le_of_le_geometric_of_tendsto r C hr (dist_partial_sum_le_of_le_geometric hf)
  exact ha.tendsto_sum_nat

@[simp]

Depends on / 依赖: dist_eq_norm, dist_le_of_le_geometric_of_tendsto, dist_partial_sum_le_of_le_geometric, ha.tendsto_sum_nat, tendsto_sum_nat
-/
theorem norm_sub_le_of_geometric_bound_of_hasSum (hr : r < 1) (hf : forall n, ‖f n‖ <= C * r ^ n) {a : α}
    (ha : HasSum f a) (n : Nat) : ‖(∑ x in Finset.range n, f x) - a‖ <= C * r ^ n / (1 - r) := by
  rw [← dist_eq_norm]
  apply dist_le_of_le_geometric_of_tendsto r C hr (dist_partial_sum_le_of_le_geometric hf)
  exact ha.tendsto_sum_nat

@[simp]
/--
theorem `dist_partial_sum` / 定理 `dist_partial_sum`

English:
theorem dist_partial_sum
  given: (u : Nat -> α) (n : Nat)
  proof: by
  simp [dist_eq_norm, sum_range_succ]

@[simp]

中文:
定理 dist_partial_sum
  条件: (u : 自然数 -> α) (n : 自然数)
  证明: by
  simp [dist_eq_norm, sum_range_succ]

@[simp]

Depends on / 依赖: dist_eq_norm, sum_range_succ
-/
theorem dist_partial_sum (u : Nat -> α) (n : Nat) :
    dist (∑ k in range (n + 1), u k) (∑ k in range n, u k) = ‖u n‖ := by
  simp [dist_eq_norm, sum_range_succ]

@[simp]
/--
theorem `dist_partial_sum'` / 定理 `dist_partial_sum'`

English:
theorem dist_partial_sum'
  given: (u : Nat -> α) (n : Nat)
  proof: by
  simp [dist_eq_norm', sum_range_succ]

中文:
定理 dist_partial_sum'
  条件: (u : 自然数 -> α) (n : 自然数)
  证明: by
  simp [dist_eq_norm', sum_range_succ]

Depends on / 依赖: dist_eq_norm, sum_range_succ
-/
theorem dist_partial_sum' (u : Nat -> α) (n : Nat) :
    dist (∑ k in range n, u k) (∑ k in range (n + 1), u k) = ‖u n‖ := by
  simp [dist_eq_norm', sum_range_succ]

/--
theorem `cauchy_series_of_le_geometric` / 定理 `cauchy_series_of_le_geometric`

English:
theorem cauchy_series_of_le_geometric
  statement: {C : Real} {u : Nat -> α} {r : Real} (hr : r < 1)
  proof: cauchySeq_of_le_geometric r C hr (by simp [h])

中文:
定理 cauchy_series_of_le_geometric
  结论: {C : 实数} {u : 自然数 -> α} {r : 实数} (hr : r < 1)
  证明: cauchySeq_of_le_geometric r C hr (by simp [h])

Depends on / 依赖: cauchySeq_of_le_geometric
-/
theorem cauchy_series_of_le_geometric {C : Real} {u : Nat -> α} {r : Real} (hr : r < 1)
    (h : forall n, ‖u n‖ <= C * r ^ n) : CauchySeq fun n => ∑ k in range n, u k :=
  cauchySeq_of_le_geometric r C hr (by simp [h])

/--
theorem `NormedAddCommGroup.cauchy_series_of_le_geometric'` / 定理 `NormedAddCommGroup.cauchy_series_of_le_geometric'`

English:
theorem NormedAddCommGroup.cauchy_series_of_le_geometric'
  statement: {C : Real} {u : Nat -> α} {r : Real} (hr : r < 1)
  proof: (cauchy_series_of_le_geometric hr h).comp_tendsto tendsto_add_atTop_nat 1

中文:
定理 赋范交换加群.cauchy_series_of_le_geometric'
  结论: {C : 实数} {u : 自然数 -> α} {r : 实数} (hr : r < 1)
  证明: (cauchy_series_of_le_geometric hr h).comp_tendsto tendsto_add_atTop_nat 1

Depends on / 依赖: cauchy_series_of_le_geometric, comp_tendsto, tendsto_add_atTop_nat
-/
theorem NormedAddCommGroup.cauchy_series_of_le_geometric' {C : Real} {u : Nat -> α} {r : Real} (hr : r < 1)
    (h : forall n, ‖u n‖ <= C * r ^ n) : CauchySeq fun n => ∑ k in range (n + 1), u k :=
(cauchy_series_of_le_geometric hr h).comp_tendsto tendsto_add_atTop_nat 1

/--
theorem `NormedAddCommGroup.cauchy_series_of_le_geometric''` / 定理 `NormedAddCommGroup.cauchy_series_of_le_geometric''`

English:
theorem NormedAddCommGroup.cauchy_series_of_le_geometric''
  statement: {C : Real} {u : Nat -> α} {N : Nat} {r : Real}
  proof: by
  set v : Nat -> α := fun n => if n < N then 0 else u n
  have hC : 0 <= C :=
    (mul_nonneg_iff_of_pos_right <| pow_pos hr₀ N).mp ((norm_nonneg _).trans <| h N <| le_refl N)
  have : forall n >= N, u n = v n := by
    intro n hn
    simp [v, if_neg (not_lt.mpr hn)]
  apply cauchySeq_sum_of_even

中文:
定理 赋范交换加群.cauchy_series_of_le_geometric''
  结论: {C : 实数} {u : 自然数 -> α} {N : 自然数} {r : 实数}
  证明: by
  set v : Nat -> α := fun n => if n < N then 0 else u n
  have hC : 0 <= C :=
    (mul_nonneg_iff_of_pos_right <| pow_pos hr₀ N).mp ((norm_nonneg _).trans <| h N <| le_refl N)
  have : forall n >= N, u n = v n := by
    intro n hn
    simp [v, if_neg (not_lt.mpr hn)]
  apply cauchySeq_sum_of_even

Depends on / 依赖: NormedAddCommGroup, NormedAddCommGroup.cauchy_series_of_le_geometric, cauchySeq_sum_of_eventually_eq, cauchy_series_of_le_geometric, if_neg, le_refl, mul_nonneg, mul_nonneg_iff_of_pos_right, norm_nonneg, norm_zero, not_lt, not_lt.mpr, pow_nonneg, pow_pos, split_ifs
-/
theorem NormedAddCommGroup.cauchy_series_of_le_geometric'' {C : Real} {u : Nat -> α} {N : Nat} {r : Real}
    (hr₀ : 0 < r) (hr₁ : r < 1) (h : forall n >= N, ‖u n‖ <= C * r ^ n) :
    CauchySeq fun n => ∑ k in range (n + 1), u k := by
  set v : Nat -> α := fun n => if n < N then 0 else u n
  have hC : 0 <= C :=
    (mul_nonneg_iff_of_pos_right <| pow_pos hr₀ N).mp ((norm_nonneg _).trans <| h N <| le_refl N)
  have : forall n >= N, u n = v n := by
    intro n hn
    simp [v, if_neg (not_lt.mpr hn)]
  apply cauchySeq_sum_of_eventually_eq this
    (NormedAddCommGroup.cauchy_series_of_le_geometric' hr₁ _)
  · exact C
  intro n
  simp only [v]
  split_ifs with H
  · rw [norm_zero]
    exact mul_nonneg hC (pow_nonneg hr₀.le _)
  · push Not at H
    exact h _ H

/--
lemma `exists_norm_le_of_cauchySeq` / 引理 `exists_norm_le_of_cauchySeq`

English:
lemma exists_norm_le_of_cauchySeq
  given: (h : CauchySeq fun n => ∑ k in range n, f k)
  proof: by
  obtain ⟨b, ⟨_, key, _⟩⟩ := cauchySeq_iff_le_tendsto_0.mp h
  refine ⟨b 0, fun n => ?_⟩
  simpa only [dist_partial_sum'] using key n (n + 1) 0 zero_le zero_le

中文:
引理 存在_norm_le_of_cauchySeq
  条件: (h : CauchySeq fun n => ∑ k in range n, f k)
  证明: by
  obtain ⟨b, ⟨_, key, _⟩⟩ := cauchySeq_iff_le_tendsto_0.mp h
  refine ⟨b 0, fun n => ?_⟩
  simpa only [dist_partial_sum'] using key n (n + 1) 0 zero_le zero_le

Depends on / 依赖: cauchySeq_iff_le_tendsto_0, cauchySeq_iff_le_tendsto_0.mp, dist_partial_sum, zero_le
-/
lemma exists_norm_le_of_cauchySeq (h : CauchySeq fun n => ∑ k in range n, f k) :
    exists C, forall n, ‖f n‖ <= C := by
  obtain ⟨b, ⟨_, key, _⟩⟩ := cauchySeq_iff_le_tendsto_0.mp h
  refine ⟨b 0, fun n => ?_⟩
  simpa only [dist_partial_sum'] using key n (n + 1) 0 zero_le zero_le

end SummableLeGeometric


/--
theorem `summable_of_ratio_norm_eventually_le` / 定理 `summable_of_ratio_norm_eventually_le`

English:
theorem summable_of_ratio_norm_eventually_le
  statement: {α : Type*} [SeminormedAddCommGroup α]
  proof: by
  by_cases! hr₀ : 0 <= r
  · rw [eventually_atTop] at h
    rcases h with ⟨N, hN⟩
    rw [← @summable_nat_add_iff α _ _ _ _ N]
    refine .of_norm_bounded (g := fun n => ‖f N‖ * r ^ n)
      (Summable.mul_left _ <| summable_geometric_of_lt_one hr₀ hr₁) fun n => ?_
    conv_rhs => rw [mul_comm, ← 

中文:
定理 summable_of_ratio_norm_eventually_le
  结论: {α : 类型} [SeminormedAddComm群 α]
  证明: by
  by_cases! hr₀ : 0 <= r
  · rw [eventually_atTop] at h
    rcases h with ⟨N, hN⟩
    rw [← @summable_nat_add_iff α _ _ _ _ N]
    refine .of_norm_bounded (g := fun n => ‖f N‖ * r ^ n)
      (Summable.mul_left _ <| summable_geometric_of_lt_one hr₀ hr₁) fun n => ?_
    conv_rhs => rw [mul_comm, ← 

Depends on / 依赖: N.le_add_left, Summable, Summable.mul_left, conv_rhs, convert, eventually_atTop, filter_upwards, le_add_left, le_geom, mul_comm, mul_left, of_norm_bounded, of_norm_bounded_eventually_nat, summable_geometric_of_lt_one, summable_nat_add_iff, summable_zero, zero_add
-/
theorem summable_of_ratio_norm_eventually_le {α : Type*} [SeminormedAddCommGroup α]
    [CompleteSpace α] {f : Nat -> α} {r : Real} (hr₁ : r < 1)
    (h : forallᶠ n in atTop, ‖f (n + 1)‖ <= r * ‖f n‖) : Summable f := by
  by_cases! hr₀ : 0 <= r
  · rw [eventually_atTop] at h
    rcases h with ⟨N, hN⟩
    rw [← @summable_nat_add_iff α _ _ _ _ N]
    refine .of_norm_bounded (g := fun n => ‖f N‖ * r ^ n)
      (Summable.mul_left _ <| summable_geometric_of_lt_one hr₀ hr₁) fun n => ?_
    conv_rhs => rw [mul_comm, ← zero_add N]
    refine le_geom (u := fun n => ‖f (n + N)‖) hr₀ n fun i _ => ?_
    convert! hN (i + N) (N.le_add_left i) using 3
    ac_rfl
  · refine .of_norm_bounded_eventually_nat summable_zero ?_
    filter_upwards [h] with _ hn
    by_contra! h
    exact not_lt.mpr (norm_nonneg _) (lt_of_le_of_lt hn <| mul_neg_of_neg_of_pos hr₀ h)

/--
theorem `summable_of_ratio_test_tendsto_lt_one` / 定理 `summable_of_ratio_test_tendsto_lt_one`

English:
theorem summable_of_ratio_test_tendsto_lt_one
  statement: {α : Type*} [NormedAddCommGroup α] [CompleteSpace α]
  proof: by
  rcases exists_between hl₁ with ⟨r, hr₀, hr₁⟩
  refine summable_of_ratio_norm_eventually_le hr₁ ?_
  filter_upwards [h.eventually_le_const hr₀, hf] with _ _ h₁
  rwa [← div_le_iff₀ (norm_pos_iff.mpr h₁)]

中文:
定理 summable_of_ratio_test_tendsto_lt_one
  结论: {α : 类型} [赋范交换加群 α] [完备空间 α]
  证明: by
  rcases exists_between hl₁ with ⟨r, hr₀, hr₁⟩
  refine summable_of_ratio_norm_eventually_le hr₁ ?_
  filter_upwards [h.eventually_le_const hr₀, hf] with _ _ h₁
  rwa [← div_le_iff₀ (norm_pos_iff.mpr h₁)]

Depends on / 依赖: eventually_le_const, exists_between, filter_upwards, h.eventually_le_const, norm_pos_iff, norm_pos_iff.mpr, summable_of_ratio_norm_eventually_le
-/
theorem summable_of_ratio_test_tendsto_lt_one {α : Type*} [NormedAddCommGroup α] [CompleteSpace α]
    {f : Nat -> α} {l : Real} (hl₁ : l < 1) (hf : forallᶠ n in atTop, f n != 0)
    (h : Tendsto (fun n => ‖f (n + 1)‖ / ‖f n‖) atTop (𝓝 l)) : Summable f := by
  rcases exists_between hl₁ with ⟨r, hr₀, hr₁⟩
  refine summable_of_ratio_norm_eventually_le hr₁ ?_
  filter_upwards [h.eventually_le_const hr₀, hf] with _ _ h₁
  rwa [← div_le_iff₀ (norm_pos_iff.mpr h₁)]

/--
theorem `not_summable_of_ratio_norm_eventually_ge` / 定理 `not_summable_of_ratio_norm_eventually_ge`

English:
theorem not_summable_of_ratio_norm_eventually_ge
  statement: {α : Type*} [SeminormedAddCommGroup α] {f : Nat -> α}
  proof: by
  rw [eventually_atTop] at h
  rcases h with ⟨N₀, hN₀⟩
  rw [frequently_atTop] at hf
  rcases hf N₀ with ⟨N, hNN₀ : N₀ <= N, hN⟩
  rw [← @summable_nat_add_iff α _ _ _ _ N]
  refine mt Summable.tendsto_atTop_zero
    fun h' => not_tendsto_atTop_of_tendsto_nhds (tendsto_norm_zero.comp h') ?_
  conv

中文:
定理 not_summable_of_ratio_norm_eventually_ge
  结论: {α : 类型} [SeminormedAddComm群 α] {f : 自然数 -> α}
  证明: by
  rw [eventually_atTop] at h
  rcases h with ⟨N₀, hN₀⟩
  rw [frequently_atTop] at hf
  rcases hf N₀ with ⟨N, hNN₀ : N₀ <= N, hN⟩
  rw [← @summable_nat_add_iff α _ _ _ _ N]
  refine mt Summable.tendsto_atTop_zero
    fun h' => not_tendsto_atTop_of_tendsto_nhds (tendsto_norm_zero.comp h') ?_
  conv

Depends on / 依赖: Summable, Summable.tendsto_atTop_zero, comp_apply, convert, eventually_atTop, frequently_atTop, lt_of_le_of_ne, norm_nonneg, not_tendsto_atTop_of_tendsto_nhds, specialize, summable_nat_add_iff, tendsto_atTop_of_geom_le, tendsto_atTop_zero, tendsto_norm_zero, tendsto_norm_zero.comp, zero_add
-/
theorem not_summable_of_ratio_norm_eventually_ge {α : Type*} [SeminormedAddCommGroup α] {f : Nat -> α}
    {r : Real} (hr : 1 < r) (hf : existsᶠ n in atTop, ‖f n‖ != 0)
    (h : forallᶠ n in atTop, r * ‖f n‖ <= ‖f (n + 1)‖) : ¬Summable f := by
  rw [eventually_atTop] at h
  rcases h with ⟨N₀, hN₀⟩
  rw [frequently_atTop] at hf
  rcases hf N₀ with ⟨N, hNN₀ : N₀ <= N, hN⟩
  rw [← @summable_nat_add_iff α _ _ _ _ N]
  refine mt Summable.tendsto_atTop_zero
    fun h' => not_tendsto_atTop_of_tendsto_nhds (tendsto_norm_zero.comp h') ?_
  convert! tendsto_atTop_of_geom_le _ hr _
  · refine lt_of_le_of_ne (norm_nonneg _) ?_
    intro h''
    specialize hN₀ N hNN₀
    simp only [comp_apply, zero_add] at h''
    exact hN h''.symm
  · grind

/--
theorem `not_summable_of_ratio_test_tendsto_gt_one` / 定理 `not_summable_of_ratio_test_tendsto_gt_one`

English:
theorem not_summable_of_ratio_test_tendsto_gt_one
  statement: {α : Type*} [SeminormedAddCommGroup α]
  proof: by
  have key : forallᶠ n in atTop, ‖f n‖ != 0 := by
    filter_upwards [h.eventually_const_le hl] with _ hn hc
    rw [hc]; rw [_root_.div_zero] at hn
    linarith
  rcases exists_between hl with ⟨r, hr₀, hr₁⟩
  refine not_summable_of_ratio_norm_eventually_ge hr₀ key.frequently ?_
  filter_upwards 

中文:
定理 not_summable_of_ratio_test_tendsto_gt_one
  结论: {α : 类型} [SeminormedAddComm群 α]
  证明: by
  have key : forallᶠ n in atTop, ‖f n‖ != 0 := by
    filter_upwards [h.eventually_const_le hl] with _ hn hc
    rw [hc]; rw [_root_.div_zero] at hn
    linarith
  rcases exists_between hl with ⟨r, hr₀, hr₁⟩
  refine not_summable_of_ratio_norm_eventually_ge hr₀ key.frequently ?_
  filter_upwards 

Depends on / 依赖: _root_, _root_.div_zero, div_zero, eventually_const_le, exists_between, filter_upwards, frequently, h.eventually_const_le, key.frequently, lt_of_le_of_ne, norm_nonneg, not_summable_of_ratio_norm_eventually_ge
-/
theorem not_summable_of_ratio_test_tendsto_gt_one {α : Type*} [SeminormedAddCommGroup α]
    {f : Nat -> α} {l : Real} (hl : 1 < l) (h : Tendsto (fun n => ‖f (n + 1)‖ / ‖f n‖) atTop (𝓝 l)) :
    ¬Summable f := by
  have key : forallᶠ n in atTop, ‖f n‖ != 0 := by
    filter_upwards [h.eventually_const_le hl] with _ hn hc
    rw [hc]; rw [_root_.div_zero] at hn
    linarith
  rcases exists_between hl with ⟨r, hr₀, hr₁⟩
  refine not_summable_of_ratio_norm_eventually_ge hr₀ key.frequently ?_
  filter_upwards [h.eventually_const_le hr₁, key] with _ _ h₁
  rwa [← le_div_iff₀ (lt_of_le_of_ne (norm_nonneg _) h₁.symm)]

section NormedDivisionRing

variable [NormedDivisionRing α] [CompleteSpace α] {f : Nat -> α}

/--
theorem `summable_powerSeries_of_norm_lt` / 定理 `summable_powerSeries_of_norm_lt`

English:
theorem summable_powerSeries_of_norm_lt
  statement: {w z : α}
  proof: by
  have hw : 0 < ‖w‖ := (norm_nonneg z).trans_lt hz
  obtain ⟨C, hC⟩ := exists_norm_le_of_cauchySeq h
  rw [summable_iff_cauchySeq_finset]
  refine cauchySeq_finset_of_geometric_bound (r := ‖z‖ / ‖w‖) (C := C) ((div_lt_one hw).mpr hz)
    (fun n => ?_)
  rw [norm_mul]; rw [norm_pow]; rw [div_pow];

中文:
定理 summable_powerSeries_of_norm_lt
  结论: {w z : α}
  证明: by
  have hw : 0 < ‖w‖ := (norm_nonneg z).trans_lt hz
  obtain ⟨C, hC⟩ := exists_norm_le_of_cauchySeq h
  rw [summable_iff_cauchySeq_finset]
  refine cauchySeq_finset_of_geometric_bound (r := ‖z‖ / ‖w‖) (C := C) ((div_lt_one hw).mpr hz)
    (fun n => ?_)
  rw [norm_mul]; rw [norm_pow]; rw [div_pow];

Depends on / 依赖: _root_, _root_.le_div_iff, cauchySeq_finset_of_geometric_bound, div_lt_one, div_pow, exists_norm_le_of_cauchySeq, mul_comm_div, norm_mul, norm_nonneg, norm_pow, summable_iff_cauchySeq_finset, trans_lt
-/
theorem summable_powerSeries_of_norm_lt {w z : α}
    (h : CauchySeq fun n => ∑ i in range n, f i * w ^ i) (hz : ‖z‖ < ‖w‖) :
    Summable fun n => f n * z ^ n := by
  have hw : 0 < ‖w‖ := (norm_nonneg z).trans_lt hz
  obtain ⟨C, hC⟩ := exists_norm_le_of_cauchySeq h
  rw [summable_iff_cauchySeq_finset]
  refine cauchySeq_finset_of_geometric_bound (r := ‖z‖ / ‖w‖) (C := C) ((div_lt_one hw).mpr hz)
    (fun n => ?_)
  rw [norm_mul]; rw [norm_pow]; rw [div_pow]; rw [← mul_comm_div]
  conv at hC => enter [n]; rw [norm_mul, norm_pow, ← _root_.le_div_iff₀ (by positivity)]
  gcongr
  exact hC n

/--
theorem `summable_powerSeries_of_norm_lt_one` / 定理 `summable_powerSeries_of_norm_lt_one`

English:
theorem summable_powerSeries_of_norm_lt_one
  statement: {z : α}
  proof: summable_powerSeries_of_norm_lt (w := 1) (by simp [h]) (by simp [hz])

中文:
定理 summable_powerSeries_of_norm_lt_one
  结论: {z : α}
  证明: summable_powerSeries_of_norm_lt (w := 1) (by simp [h]) (by simp [hz])

Depends on / 依赖: summable_powerSeries_of_norm_lt
-/
theorem summable_powerSeries_of_norm_lt_one {z : α}
    (h : CauchySeq fun n => ∑ i in range n, f i) (hz : ‖z‖ < 1) :
    Summable fun n => f n * z ^ n :=
  summable_powerSeries_of_norm_lt (w := 1) (by simp [h]) (by simp [hz])

end NormedDivisionRing

section

/-! ### Dirichlet and alternating series tests -/


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {b : Real} {f : Nat -> Real} {z : Nat -> E}

/--
theorem `Monotone.cauchySeq_series_mul_of_tendsto_zero_of_bounded` / 定理 `Monotone.cauchySeq_series_mul_of_tendsto_zero_of_bounded`

English:
theorem Monotone.cauchySeq_series_mul_of_tendsto_zero_of_bounded
  statement: (hfa : Monotone f)
  proof: by
  rw [← cauchySeq_shift 1]
  simp_rw [Finset.sum_range_by_parts _ _ (Nat.succ _), sub_eq_add_neg, Nat.succ_sub_succ_eq_sub,
    tsub_zero]
  apply (NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded hf0
⟨b, eventually_map.mpr Eventually.of_forall fun n => hgb n + 1⟩).cauchySeq.add
  refine 

中文:
定理 递增.cauchySeq_series_mul_of_tendsto_zero_of_bounded
  结论: (hfa : 递增 f)
  证明: by
  rw [← cauchySeq_shift 1]
  simp_rw [Finset.sum_range_by_parts _ _ (Nat.succ _), sub_eq_add_neg, Nat.succ_sub_succ_eq_sub,
    tsub_zero]
  apply (NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded hf0
⟨b, eventually_map.mpr Eventually.of_forall fun n => hgb n + 1⟩).cauchySeq.add
  refine 

Depends on / 依赖: CauchySeq, CauchySeq.neg, Eventually, Eventually.of_forall, Finset, Finset.range, Finset.sum_range_by_parts, Nat.succ, Nat.succ_sub_succ_eq_sub, NormedField, NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded, abs_of_nonneg, cauchySeq, cauchySeq.add, cauchySeq_range_of_norm_bounded, cauchySeq_shift, eventually_map, eventually_map.mpr, of_forall, simp_rw
-/
theorem Monotone.cauchySeq_series_mul_of_tendsto_zero_of_bounded (hfa : Monotone f)
    (hf0 : Tendsto f atTop (𝓝 0)) (hgb : forall n, ‖∑ i in range n, z i‖ <= b) :
    CauchySeq fun n => ∑ i in range n, f i • z i := by
  rw [← cauchySeq_shift 1]
  simp_rw [Finset.sum_range_by_parts _ _ (Nat.succ _), sub_eq_add_neg, Nat.succ_sub_succ_eq_sub,
    tsub_zero]
  apply (NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded hf0
⟨b, eventually_map.mpr Eventually.of_forall fun n => hgb n + 1⟩).cauchySeq.add
  refine CauchySeq.neg ?_
  refine cauchySeq_range_of_norm_bounded ?_
    (fun n => ?_ : forall n, ‖(f (n + 1) + -f n) • (Finset.range (n + 1)).sum z‖ <= b * |f (n + 1) - f n|)
  · simp_rw [abs_of_nonneg (sub_nonneg_of_le (hfa (Nat.le_succ _))), ← mul_sum]
    apply Real.uniformContinuous_const_mul.comp_cauchySeq
    simp_rw [sum_range_sub, sub_eq_add_neg]
    exact (Tendsto.cauchySeq hf0).add_const
  · rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hgb _) (abs_nonneg _)

/--
theorem `Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded` / 定理 `Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded`

English:
theorem Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded
  statement: (hfa : Antitone f)
  proof: by
have hfa' : Monotone fun n => -f n := fun _ _ hab => neg_le_neg hfa hab
  have hf0' : Tendsto (fun n => -f n) atTop (𝓝 0) := by
    convert! hf0.neg
    simp
  convert! (hfa'.cauchySeq_series_mul_of_tendsto_zero_of_bounded hf0' hzb).neg
  simp

中文:
定理 递减.cauchySeq_series_mul_of_tendsto_zero_of_bounded
  结论: (hfa : 递减 f)
  证明: by
have hfa' : Monotone fun n => -f n := fun _ _ hab => neg_le_neg hfa hab
  have hf0' : Tendsto (fun n => -f n) atTop (𝓝 0) := by
    convert! hf0.neg
    simp
  convert! (hfa'.cauchySeq_series_mul_of_tendsto_zero_of_bounded hf0' hzb).neg
  simp

Depends on / 依赖: Monotone, Tendsto, cauchySeq_series_mul_of_tendsto_zero_of_bounded, convert, hf0.neg, neg_le_neg
-/
theorem Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded (hfa : Antitone f)
    (hf0 : Tendsto f atTop (𝓝 0)) (hzb : forall n, ‖∑ i in range n, z i‖ <= b) :
    CauchySeq fun n => ∑ i in range n, f i • z i := by
have hfa' : Monotone fun n => -f n := fun _ _ hab => neg_le_neg hfa hab
  have hf0' : Tendsto (fun n => -f n) atTop (𝓝 0) := by
    convert! hf0.neg
    simp
  convert! (hfa'.cauchySeq_series_mul_of_tendsto_zero_of_bounded hf0' hzb).neg
  simp

/--
theorem `norm_sum_neg_one_pow_le` / 定理 `norm_sum_neg_one_pow_le`

English:
theorem norm_sum_neg_one_pow_le
  given: (n : Nat)
  statement: ‖∑ i in range n, (-1 : Real) ^ i‖ <= 1
  proof: by
  rw [neg_one_geom_sum]
  split_ifs <;> norm_num

中文:
定理 norm_sum_neg_one_pow_le
  条件: (n : 自然数)
  结论: ‖∑ i in range n, (-1 : 实数) ^ i‖ <= 1
  证明: by
  rw [neg_one_geom_sum]
  split_ifs <;> norm_num

Depends on / 依赖: neg_one_geom_sum, split_ifs
-/
theorem norm_sum_neg_one_pow_le (n : Nat) : ‖∑ i in range n, (-1 : Real) ^ i‖ <= 1 := by
  rw [neg_one_geom_sum]
  split_ifs <;> norm_num

/--
theorem `Monotone.cauchySeq_alternating_series_of_tendsto_zero` / 定理 `Monotone.cauchySeq_alternating_series_of_tendsto_zero`

English:
theorem Monotone.cauchySeq_alternating_series_of_tendsto_zero
  statement: (hfa : Monotone f)
  proof: by
  simp_rw [mul_comm]
  exact hfa.cauchySeq_series_mul_of_tendsto_zero_of_bounded hf0 norm_sum_neg_one_pow_le

中文:
定理 递增.cauchySeq_alternating_series_of_tendsto_zero
  结论: (hfa : 递增 f)
  证明: by
  simp_rw [mul_comm]
  exact hfa.cauchySeq_series_mul_of_tendsto_zero_of_bounded hf0 norm_sum_neg_one_pow_le

Depends on / 依赖: cauchySeq_series_mul_of_tendsto_zero_of_bounded, hfa.cauchySeq_series_mul_of_tendsto_zero_of_bounded, mul_comm, norm_sum_neg_one_pow_le, simp_rw
-/
theorem Monotone.cauchySeq_alternating_series_of_tendsto_zero (hfa : Monotone f)
    (hf0 : Tendsto f atTop (𝓝 0)) : CauchySeq fun n => ∑ i in range n, (-1) ^ i * f i := by
  simp_rw [mul_comm]
  exact hfa.cauchySeq_series_mul_of_tendsto_zero_of_bounded hf0 norm_sum_neg_one_pow_le

/--
theorem `Monotone.tendsto_alternating_series_of_tendsto_zero` / 定理 `Monotone.tendsto_alternating_series_of_tendsto_zero`

English:
theorem Monotone.tendsto_alternating_series_of_tendsto_zero
  statement: (hfa : Monotone f)
  proof: cauchySeq_tendsto_of_complete hfa.cauchySeq_alternating_series_of_tendsto_zero hf0

中文:
定理 递增.tendsto_alternating_series_of_tendsto_zero
  结论: (hfa : 递增 f)
  证明: cauchySeq_tendsto_of_complete hfa.cauchySeq_alternating_series_of_tendsto_zero hf0

Depends on / 依赖: cauchySeq_alternating_series_of_tendsto_zero, cauchySeq_tendsto_of_complete, hfa.cauchySeq_alternating_series_of_tendsto_zero
-/
theorem Monotone.tendsto_alternating_series_of_tendsto_zero (hfa : Monotone f)
    (hf0 : Tendsto f atTop (𝓝 0)) :
    exists l, Tendsto (fun n => ∑ i in range n, (-1) ^ i * f i) atTop (𝓝 l) :=
cauchySeq_tendsto_of_complete hfa.cauchySeq_alternating_series_of_tendsto_zero hf0

/--
theorem `Antitone.cauchySeq_alternating_series_of_tendsto_zero` / 定理 `Antitone.cauchySeq_alternating_series_of_tendsto_zero`

English:
theorem Antitone.cauchySeq_alternating_series_of_tendsto_zero
  statement: (hfa : Antitone f)
  proof: by
  simp_rw [mul_comm]
  exact hfa.cauchySeq_series_mul_of_tendsto_zero_of_bounded hf0 norm_sum_neg_one_pow_le

中文:
定理 递减.cauchySeq_alternating_series_of_tendsto_zero
  结论: (hfa : 递减 f)
  证明: by
  simp_rw [mul_comm]
  exact hfa.cauchySeq_series_mul_of_tendsto_zero_of_bounded hf0 norm_sum_neg_one_pow_le

Depends on / 依赖: cauchySeq_series_mul_of_tendsto_zero_of_bounded, hfa.cauchySeq_series_mul_of_tendsto_zero_of_bounded, mul_comm, norm_sum_neg_one_pow_le, simp_rw
-/
theorem Antitone.cauchySeq_alternating_series_of_tendsto_zero (hfa : Antitone f)
    (hf0 : Tendsto f atTop (𝓝 0)) : CauchySeq fun n => ∑ i in range n, (-1) ^ i * f i := by
  simp_rw [mul_comm]
  exact hfa.cauchySeq_series_mul_of_tendsto_zero_of_bounded hf0 norm_sum_neg_one_pow_le

/--
theorem `Antitone.tendsto_alternating_series_of_tendsto_zero` / 定理 `Antitone.tendsto_alternating_series_of_tendsto_zero`

English:
theorem Antitone.tendsto_alternating_series_of_tendsto_zero
  statement: (hfa : Antitone f)
  proof: cauchySeq_tendsto_of_complete hfa.cauchySeq_alternating_series_of_tendsto_zero hf0

中文:
定理 递减.tendsto_alternating_series_of_tendsto_zero
  结论: (hfa : 递减 f)
  证明: cauchySeq_tendsto_of_complete hfa.cauchySeq_alternating_series_of_tendsto_zero hf0

Depends on / 依赖: SemilatticeSup, cauchySeq_alternating_series_of_tendsto_zero, cauchySeq_tendsto_of_complete, hfa.cauchySeq_alternating_series_of_tendsto_zero, isFilteredOrEmpty_of_semilatticeSup
-/
theorem Antitone.tendsto_alternating_series_of_tendsto_zero (hfa : Antitone f)
    (hf0 : Tendsto f atTop (𝓝 0)) :
    exists l, Tendsto (fun n => ∑ i in range n, (-1) ^ i * f i) atTop (𝓝 l) :=
cauchySeq_tendsto_of_complete hfa.cauchySeq_alternating_series_of_tendsto_zero hf0

end

/-! ### Partial sum bounds on alternating convergent series -/

section

variable {E : Type*} [Ring E] [PartialOrder E] [IsOrderedRing E]
  [TopologicalSpace E] [OrderClosedTopology E]
  {l : E} {f : Nat -> E}

/--
theorem `Monotone.tendsto_le_alternating_series` / 定理 `Monotone.tendsto_le_alternating_series`

English:
theorem Monotone.tendsto_le_alternating_series
  proof: by
  have ha : Antitone (fun n => ∑ i in range (2 * n), (-1) ^ i * f i) := by
    refine antitone_nat_of_succ_le (fun n => ?_)
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring]; rw [sum_range_succ]; rw [sum_range_succ]
    simp_rw [_root_.pow_succ', show (-1 : E) ^ (2 * n) = 1 by simp, neg_one_mul, 

中文:
定理 递增.tendsto_le_alternating_series
  证明: by
  have ha : Antitone (fun n => ∑ i in range (2 * n), (-1) ^ i * f i) := by
    refine antitone_nat_of_succ_le (fun n => ?_)
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring]; rw [sum_range_succ]; rw [sum_range_succ]
    simp_rw [_root_.pow_succ', show (-1 : E) ^ (2 * n) = 1 by simp, neg_one_mul, 

Depends on / 依赖: Antitone, SemilatticeSup, _root_, _root_.pow_succ, antitone_nat_of_succ_le, ha.le_of_tendsto, hfl.comp, isFiltered_of_semilatticeSup_nonempty, le_of_tendsto, neg_one_mul, one_mul, pow_succ, simp_rw, sub_eq_add_neg, sub_le_iff_le_add, sum_range_succ, tendsto_atTop_mono, tendsto_id
-/
theorem Monotone.tendsto_le_alternating_series
    (hfl : Tendsto (fun n => ∑ i in range n, (-1) ^ i * f i) atTop (𝓝 l))
    (hfm : Monotone f) (k : Nat) : l <= ∑ i in range (2 * k), (-1) ^ i * f i := by
  have ha : Antitone (fun n => ∑ i in range (2 * n), (-1) ^ i * f i) := by
    refine antitone_nat_of_succ_le (fun n => ?_)
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring]; rw [sum_range_succ]; rw [sum_range_succ]
    simp_rw [_root_.pow_succ', show (-1 : E) ^ (2 * n) = 1 by simp, neg_one_mul, one_mul,
      ← sub_eq_add_neg, sub_le_iff_le_add]
    gcongr
    exact hfm (by lia)
  exact ha.le_of_tendsto (hfl.comp (tendsto_atTop_mono (fun n => by dsimp; lia) tendsto_id)) _

/--
theorem `Monotone.alternating_series_le_tendsto` / 定理 `Monotone.alternating_series_le_tendsto`

English:
theorem Monotone.alternating_series_le_tendsto
  proof: by
  have hm : Monotone (fun n => ∑ i in range (2 * n + 1), (-1) ^ i * f i) := by
    refine monotone_nat_of_le_succ (fun n => ?_)
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring]; rw [sum_range_succ _ (2 * n + 1 + 1)]; rw [sum_range_succ _ (2 * n + 1)]
    simp_rw [_root_.pow_succ', show (-1 : E) 

中文:
定理 递增.alternating_series_le_tendsto
  证明: by
  have hm : Monotone (fun n => ∑ i in range (2 * n + 1), (-1) ^ i * f i) := by
    refine monotone_nat_of_le_succ (fun n => ?_)
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring]; rw [sum_range_succ _ (2 * n + 1 + 1)]; rw [sum_range_succ _ (2 * n + 1)]
    simp_rw [_root_.pow_succ', show (-1 : E) 

Depends on / 依赖: Monotone, Preorder, _root_, _root_.pow_succ, ge_of_tendsto, hfl.comp, hm.ge_of_tendsto, isFilteredOrEmpty_of_directed_le, le_sub_iff_add_le, monotone_nat_of_le_succ, neg_neg, neg_one_mul, one_mul, pow_succ, simp_rw, sub_add_eq_add_sub, sub_eq_add_neg, sum_range_succ, tendsto_atTop_mono
-/
theorem Monotone.alternating_series_le_tendsto
    (hfl : Tendsto (fun n => ∑ i in range n, (-1) ^ i * f i) atTop (𝓝 l))
    (hfm : Monotone f) (k : Nat) : ∑ i in range (2 * k + 1), (-1) ^ i * f i <= l := by
  have hm : Monotone (fun n => ∑ i in range (2 * n + 1), (-1) ^ i * f i) := by
    refine monotone_nat_of_le_succ (fun n => ?_)
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring]; rw [sum_range_succ _ (2 * n + 1 + 1)]; rw [sum_range_succ _ (2 * n + 1)]
    simp_rw [_root_.pow_succ', show (-1 : E) ^ (2 * n) = 1 by simp, neg_one_mul, neg_neg, one_mul,
      ← sub_eq_add_neg, sub_add_eq_add_sub, le_sub_iff_add_le]
    gcongr
    exact hfm (by lia)
  exact hm.ge_of_tendsto (hfl.comp (tendsto_atTop_mono (fun n => by dsimp; lia) tendsto_id)) _

/--
theorem `Antitone.alternating_series_le_tendsto` / 定理 `Antitone.alternating_series_le_tendsto`

English:
theorem Antitone.alternating_series_le_tendsto
  proof: by
  have hm : Monotone (fun n => ∑ i in range (2 * n), (-1) ^ i * f i) := by
    refine monotone_nat_of_le_succ (fun n => ?_)
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring]; rw [sum_range_succ]; rw [sum_range_succ]
    simp_rw [_root_.pow_succ', show (-1 : E) ^ (2 * n) = 1 by simp, neg_one_mul, 

中文:
定理 递减.alternating_series_le_tendsto
  证明: by
  have hm : Monotone (fun n => ∑ i in range (2 * n), (-1) ^ i * f i) := by
    refine monotone_nat_of_le_succ (fun n => ?_)
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring]; rw [sum_range_succ]; rw [sum_range_succ]
    simp_rw [_root_.pow_succ', show (-1 : E) ^ (2 * n) = 1 by simp, neg_one_mul, 

Depends on / 依赖: Monotone, Preorder, _root_, _root_.pow_succ, ge_of_tendsto, hfl.comp, hm.ge_of_tendsto, isFiltered_of_directed_le_nonempty, le_sub_iff_add_le, monotone_nat_of_le_succ, neg_one_mul, one_mul, pow_succ, simp_rw, sub_eq_add_neg, sum_range_succ, tendsto_atTop_mono, tendsto_id
-/
theorem Antitone.alternating_series_le_tendsto
    (hfl : Tendsto (fun n => ∑ i in range n, (-1) ^ i * f i) atTop (𝓝 l))
    (hfa : Antitone f) (k : Nat) : ∑ i in range (2 * k), (-1) ^ i * f i <= l := by
  have hm : Monotone (fun n => ∑ i in range (2 * n), (-1) ^ i * f i) := by
    refine monotone_nat_of_le_succ (fun n => ?_)
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring]; rw [sum_range_succ]; rw [sum_range_succ]
    simp_rw [_root_.pow_succ', show (-1 : E) ^ (2 * n) = 1 by simp, neg_one_mul, one_mul,
      ← sub_eq_add_neg, le_sub_iff_add_le]
    gcongr
    exact hfa (by lia)
  exact hm.ge_of_tendsto (hfl.comp (tendsto_atTop_mono (fun n => by dsimp; lia) tendsto_id)) _

/--
theorem `Antitone.tendsto_le_alternating_series` / 定理 `Antitone.tendsto_le_alternating_series`

English:
theorem Antitone.tendsto_le_alternating_series
  proof: by
  have ha : Antitone (fun n => ∑ i in range (2 * n + 1), (-1) ^ i * f i) := by
    refine antitone_nat_of_succ_le (fun n => ?_)
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring]; rw [sum_range_succ]; rw [sum_range_succ]
    simp_rw [_root_.pow_succ', show (-1 : E) ^ (2 * n) = 1 by simp, neg_one_m

中文:
定理 递减.tendsto_le_alternating_series
  证明: by
  have ha : Antitone (fun n => ∑ i in range (2 * n + 1), (-1) ^ i * f i) := by
    refine antitone_nat_of_succ_le (fun n => ?_)
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring]; rw [sum_range_succ]; rw [sum_range_succ]
    simp_rw [_root_.pow_succ', show (-1 : E) ^ (2 * n) = 1 by simp, neg_one_m

Depends on / 依赖: Antitone, PUnit.unit, _root_, _root_.pow_succ, antitone_nat_of_succ_le, ha.le_of_tendsto, hfl.comp, le_of_tendsto, neg_neg, neg_one_mul, one_mul, pow_succ, simp_rw, sub_add_eq_add_sub, sub_eq_add_neg, sub_le_iff_le_add, subsingleton, sum_range_succ, tendsto_atTop_mono, tendsto_id
-/
theorem Antitone.tendsto_le_alternating_series
    (hfl : Tendsto (fun n => ∑ i in range n, (-1) ^ i * f i) atTop (𝓝 l))
    (hfa : Antitone f) (k : Nat) : l <= ∑ i in range (2 * k + 1), (-1) ^ i * f i := by
  have ha : Antitone (fun n => ∑ i in range (2 * n + 1), (-1) ^ i * f i) := by
    refine antitone_nat_of_succ_le (fun n => ?_)
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring]; rw [sum_range_succ]; rw [sum_range_succ]
    simp_rw [_root_.pow_succ', show (-1 : E) ^ (2 * n) = 1 by simp, neg_one_mul, neg_neg, one_mul,
      ← sub_eq_add_neg, sub_add_eq_add_sub, sub_le_iff_le_add]
    gcongr
    exact hfa (by lia)
  exact ha.le_of_tendsto (hfl.comp (tendsto_atTop_mono (fun n => by dsimp; lia) tendsto_id)) _

/--
theorem `Summable.tendsto_alternating_series_tsum` / 定理 `Summable.tendsto_alternating_series_tsum`

English:
theorem Summable.tendsto_alternating_series_tsum
  proof: Summable.tendsto_sum_tsum_nat hfs.alternating

中文:
定理 Summable.tendsto_alternating_series_tsum
  证明: Summable.tendsto_sum_tsum_nat hfs.alternating

Depends on / 依赖: Summable, Summable.tendsto_sum_tsum_nat, alternating, hfs.alternating, tendsto_sum_tsum_nat
-/
theorem Summable.tendsto_alternating_series_tsum
    {E} [Ring E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E]
    {f : Nat -> E} (hfs : Summable f) :
    Tendsto (fun n => (∑ i in range n, (-1) ^ i * f i)) atTop (𝓝 (∑' i : Nat, (-1) ^ i * f i)) :=
  Summable.tendsto_sum_tsum_nat hfs.alternating

-- TODO: generalize to conditionally-convergent sums
-- see https://github.com/leanprover-community/mathlib4/pull/29577#discussion_r2343447344
/--
theorem `alternating_series_error_bound` / 定理 `alternating_series_error_bound`

English:
theorem alternating_series_error_bound
  proof: by
  obtain h := hfs.tendsto_alternating_series_tsum
  have upper := hfa.alternating_series_le_tendsto h
  have lower := hfa.tendsto_le_alternating_series h
  have I (n : Nat) : 0 <= f n := by
    apply le_of_tendsto hfs.tendsto_atTop_zero
    filter_upwards [Ici_mem_atTop n] with m hm using hfa hm


中文:
定理 alternating_series_error_bound
  证明: by
  obtain h := hfs.tendsto_alternating_series_tsum
  have upper := hfa.alternating_series_le_tendsto h
  have lower := hfa.tendsto_le_alternating_series h
  have I (n : Nat) : 0 <= f n := by
    apply le_of_tendsto hfs.tendsto_atTop_zero
    filter_upwards [Ici_mem_atTop n] with m hm using hfa hm


Depends on / 依赖: Even.mul_right, Even.neg_pow, Ici_mem_atTop, alternating_series_le_tendsto, even_iff_exists_two_mul, even_iff_exists_two_mul.mp, even_or_odd, even_two, filter_upwards, hfa.alternating_series_le_tendsto, hfa.tendsto_le_alternating_series, hfs.tendsto_alternating_series_tsum, hfs.tendsto_atTop_zero, le_of_tendsto, mul_right, neg_pow, one_mul, one_pow, specialize, sum_range_succ
-/
theorem alternating_series_error_bound
    {E} [Ring E] [LinearOrder E] [IsOrderedRing E]
    [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E] [OrderClosedTopology E]
    (f : Nat -> E) (hfa : Antitone f) (hfs : Summable f) (n : Nat) :
    |(∑' i : Nat, (-1) ^ i * f i) - (∑ i in range n, (-1) ^ i * f i)| <= f n := by
  obtain h := hfs.tendsto_alternating_series_tsum
  have upper := hfa.alternating_series_le_tendsto h
  have lower := hfa.tendsto_le_alternating_series h
  have I (n : Nat) : 0 <= f n := by
    apply le_of_tendsto hfs.tendsto_atTop_zero
    filter_upwards [Ici_mem_atTop n] with m hm using hfa hm
  obtain (h | h) := even_or_odd n
  · obtain ⟨n, rfl⟩ := even_iff_exists_two_mul.mp h
    specialize upper n
    specialize lower n
    simp only [sum_range_succ, even_two, Even.mul_right, Even.neg_pow, one_pow, one_mul] at lower
    rw [abs_sub_le_iff]
    constructor
    · rwa [sub_le_iff_le_add, add_comm]
    · rw [sub_le_iff_le_add, add_comm]
      exact upper.trans (le_add_of_nonneg_right (I (2 * n)))
  · obtain ⟨n, rfl⟩ := odd_iff_exists_bit1.mp h
    specialize upper (n + 1)
    specialize lower n
    rw [Nat.mul_add]; rw [Finset.sum_range_succ] at upper
    rw [abs_sub_le_iff]
    constructor
    · rw [sub_le_iff_le_add, add_comm]
      exact lower.trans (le_add_of_nonneg_right (I (2 * n + 1)))
    · simpa [Finset.sum_range_succ, add_comm, pow_add] using upper

end

/-!
### Factorial
-/

/--
theorem `Real.summable_pow_div_factorial` / 定理 `Real.summable_pow_div_factorial`

English:
theorem Real.summable_pow_div_factorial
  given: (x : Real)
  statement: Summable (fun n => x ^ n / n ! : Nat -> Real)
  proof: by
  -- We start with trivial estimates
  have A : (0 : Real) < ⌊‖x‖⌋₊ + 1 := zero_lt_one.trans_le (by simp)
  have B : ‖x‖ / (⌊‖x‖⌋₊ + 1) < 1 := (div_lt_one A).2 (Nat.lt_floor_add_one _)
  -- Then we apply the ratio test. The estimate works for `n ≥ ⌊‖x‖⌋₊`.
  suffices forall n >= ⌊‖x‖⌋₊, ‖x ^ (n +

中文:
定理 实数.summable_pow_div_factorial
  条件: (x : 实数)
  结论: Summable (fun n => x ^ n / n ! : 自然数 -> 实数)
  证明: by
  -- We start with trivial estimates
  have A : (0 : Real) < ⌊‖x‖⌋₊ + 1 := zero_lt_one.trans_le (by simp)
  have B : ‖x‖ / (⌊‖x‖⌋₊ + 1) < 1 := (div_lt_one A).2 (Nat.lt_floor_add_one _)
  -- Then we apply the ratio test. The estimate works for `n ≥ ⌊‖x‖⌋₊`.
  suffices forall n >= ⌊‖x‖⌋₊, ‖x ^ (n +
-/
theorem Real.summable_pow_div_factorial (x : Real) : Summable (fun n => x ^ n / n ! : Nat -> Real) := by
  -- We start with trivial estimates
  have A : (0 : Real) < ⌊‖x‖⌋₊ + 1 := zero_lt_one.trans_le (by simp)
  have B : ‖x‖ / (⌊‖x‖⌋₊ + 1) < 1 := (div_lt_one A).2 (Nat.lt_floor_add_one _)
  -- Then we apply the ratio test. The estimate works for `n ≥ ⌊‖x‖⌋₊`.
  suffices forall n >= ⌊‖x‖⌋₊, ‖x ^ (n + 1) / (n + 1)!‖ <= ‖x‖ / (⌊‖x‖⌋₊ + 1) * ‖x ^ n / ↑n !‖ from
    summable_of_ratio_norm_eventually_le B (eventually_atTop.2 ⟨⌊‖x‖⌋₊, this⟩)
  -- Finally, we prove the upper estimate
  intro n hn
  calc
    ‖x ^ (n + 1) / (n + 1)!‖ = ‖x‖ / (n + 1) * ‖x ^ n / (n !)‖ := by
      rw [_root_.pow_succ']; rw [Nat.factorial_succ]; rw [Nat.cast_mul]; rw [← _root_.div_mul_div_comm]; rw [norm_mul]; rw [norm_div]; rw [Real.norm_natCast]; rw [Nat.cast_succ]
    _ <= ‖x‖ / (⌊‖x‖⌋₊ + 1) * ‖x ^ n / (n !)‖ := by gcongr

section

/-! Limits when `f x * g x` is bounded or convergent and `f` tends to the `cobounded` filter. -/

open Bornology

variable {R K : Type*}

section NormedAddCommGroup
variable [NormedRing K] [IsDomain K] [NormedAddCommGroup R]
variable [Module K R] [IsTorsionFree K R] [NormSMulClass K R]

/--
lemma `tendsto_zero_of_isBoundedUnder_smul_of_tendsto_cobounded` / 引理 `tendsto_zero_of_isBoundedUnder_smul_of_tendsto_cobounded`

English:
lemma tendsto_zero_of_isBoundedUnder_smul_of_tendsto_cobounded
  statement: {f : α -> K} {g : α -> R}
  proof: by
  obtain ⟨c, hc⟩ := hmul.eventually_le
  refine Metric.nhds_basis_closedBall.tendsto_right_iff.mpr fun ε hε0 => ?_
  filter_upwards [hc, hasBasis_cobounded_norm.tendsto_right_iff.mp hf (c / ε) trivial,
    hf.eventually_ne_cobounded 0] with x hfgc hεf hf0
  rcases eq_or_lt_of_le ((norm_nonneg _).

中文:
引理 tendsto_zero_of_isBoundedUnder_smul_of_tendsto_cobounded
  结论: {f : α -> K} {g : α -> R}
  证明: by
  obtain ⟨c, hc⟩ := hmul.eventually_le
  refine Metric.nhds_basis_closedBall.tendsto_right_iff.mpr fun ε hε0 => ?_
  filter_upwards [hc, hasBasis_cobounded_norm.tendsto_right_iff.mp hf (c / ε) trivial,
    hf.eventually_ne_cobounded 0] with x hfgc hεf hf0
  rcases eq_or_lt_of_le ((norm_nonneg _).

Depends on / 依赖: Metric, Metric.nhds_basis_closedBall.tendsto_right_iff.mpr, eq_or_lt_of_le, eventually_le, eventually_ne_cobounded, filter_upwards, hasBasis_cobounded_norm, hasBasis_cobounded_norm.tendsto_right_iff.mp, hf.eventually_ne_cobounded, hmul.eventually_le, nhds_basis_closedBall, norm_le_zero_iff, norm_le_zero_iff.mp, norm_nonneg, norm_smul, smul_eq_zero_iff_right, tendsto_right_iff
-/
lemma tendsto_zero_of_isBoundedUnder_smul_of_tendsto_cobounded {f : α -> K} {g : α -> R}
    {l : Filter α} (hmul : IsBoundedUnder (· <= ·) l fun x => ‖f x • g x‖)
    (hf : Tendsto f l (cobounded K)) :
    Tendsto g l (𝓝 0) := by
  obtain ⟨c, hc⟩ := hmul.eventually_le
  refine Metric.nhds_basis_closedBall.tendsto_right_iff.mpr fun ε hε0 => ?_
  filter_upwards [hc, hasBasis_cobounded_norm.tendsto_right_iff.mp hf (c / ε) trivial,
    hf.eventually_ne_cobounded 0] with x hfgc hεf hf0
  rcases eq_or_lt_of_le ((norm_nonneg _).trans hfgc) with rfl | hc0
  · simpa [(smul_eq_zero_iff_right hf0).mp (norm_le_zero_iff.mp hfgc)] using hε0.le
  calc
    _ = ‖g x‖ := by simp
    _ <= c / ‖f x‖ := by rwa [norm_smul, ← le_div_iff₀' (by positivity)] at hfgc
    _ <= c / (c / ε) := by gcongr
    _ = ε := div_div_cancel₀ hc0.ne'

/--
lemma `tendsto_smul_congr_of_tendsto_left_cobounded_of_isBoundedUnder` / 引理 `tendsto_smul_congr_of_tendsto_left_cobounded_of_isBoundedUnder`

English:
lemma tendsto_smul_congr_of_tendsto_left_cobounded_of_isBoundedUnder
  proof: by
  apply hmul.congr_dist
  simp_rw [dist_eq_norm, ← sub_smul, norm_smul]
  apply isBoundedUnder_le_mul_tendsto_zero
  · change IsBoundedUnder _ _ fun _ => _
    simpa using hbdd
  · rw [← tendsto_zero_iff_norm_tendsto_zero]
    exact tendsto_zero_of_isBoundedUnder_smul_of_tendsto_cobounded hmul.no

中文:
引理 tendsto_smul_congr_of_tendsto_left_cobounded_of_isBoundedUnder
  证明: by
  apply hmul.congr_dist
  simp_rw [dist_eq_norm, ← sub_smul, norm_smul]
  apply isBoundedUnder_le_mul_tendsto_zero
  · change IsBoundedUnder _ _ fun _ => _
    simpa using hbdd
  · rw [← tendsto_zero_iff_norm_tendsto_zero]
    exact tendsto_zero_of_isBoundedUnder_smul_of_tendsto_cobounded hmul.no

Depends on / 依赖: IsBoundedUnder, congr_dist, dist_eq_norm, hmul.congr_dist, hmul.norm.isBoundedUnder_le, isBoundedUnder_le, isBoundedUnder_le_mul_tendsto_zero, norm_smul, simp_rw, sub_smul, tendsto_zero_iff_norm_tendsto_zero, tendsto_zero_of_isBoundedUnder_smul_of_tendsto_cobounded
-/
lemma tendsto_smul_congr_of_tendsto_left_cobounded_of_isBoundedUnder
    {f₁ f₂ : α -> K} {g : α -> R} {t : R} {l : Filter α}
    (hmul : Tendsto (fun x => f₁ x • g x) l (𝓝 t))
    (hf₁ : Tendsto f₁ l (cobounded K))
    (hbdd : IsBoundedUnder (· <= ·) l fun x => ‖f₁ x - f₂ x‖) :
    Tendsto (fun x => f₂ x • g x) l (𝓝 t) := by
  apply hmul.congr_dist
  simp_rw [dist_eq_norm, ← sub_smul, norm_smul]
  apply isBoundedUnder_le_mul_tendsto_zero
  · change IsBoundedUnder _ _ fun _ => _
    simpa using hbdd
  · rw [← tendsto_zero_iff_norm_tendsto_zero]
    exact tendsto_zero_of_isBoundedUnder_smul_of_tendsto_cobounded hmul.norm.isBoundedUnder_le hf₁

set_option linter.overlappingInstances false in
-- The use case in mind for this is when `K = ℝ`, and `R = ℝ` or `ℂ`
/--
lemma `tendsto_smul_comp_nat_floor_of_tendsto_nsmul` / 引理 `tendsto_smul_comp_nat_floor_of_tendsto_nsmul`

English:
lemma tendsto_smul_comp_nat_floor_of_tendsto_nsmul
  statement: [NormSMulClass Int K] [LinearOrder K]
  proof: by
  replace hg : Tendsto (fun n : Nat => (n : K) • g n) atTop (𝓝 t) := mod_cast hg
  apply tendsto_smul_congr_of_tendsto_left_cobounded_of_isBoundedUnder
    (hg.comp tendsto_nat_floor_atTop)
  · exact tendsto_natCast_atTop_cobounded.comp tendsto_nat_floor_atTop
  · apply isBoundedUnder_of_eventual

中文:
引理 tendsto_smul_comp_nat_floor_of_tendsto_nsmul
  结论: [NormSMul类 整数 K] [线性序 K]
  证明: by
  replace hg : Tendsto (fun n : Nat => (n : K) • g n) atTop (𝓝 t) := mod_cast hg
  apply tendsto_smul_congr_of_tendsto_left_cobounded_of_isBoundedUnder
    (hg.comp tendsto_nat_floor_atTop)
  · exact tendsto_natCast_atTop_cobounded.comp tendsto_nat_floor_atTop
  · apply isBoundedUnder_of_eventual

Depends on / 依赖: Eventually, Eventually.mono, Nat.abs_floor_sub_le, Tendsto, abs_floor_sub_le, hg.comp, isBoundedUnder_of_eventually_le, mod_cast, norm_le_norm_of_abs_le_abs, replace, tendsto_natCast_atTop_cobounded, tendsto_natCast_atTop_cobounded.comp, tendsto_nat_floor_atTop, tendsto_smul_congr_of_tendsto_left_cobounded_of_isBoundedUnder
-/
lemma tendsto_smul_comp_nat_floor_of_tendsto_nsmul [NormSMulClass Int K] [LinearOrder K]
    [IsStrictOrderedRing K] [FloorSemiring K] [HasSolidNorm K] {g : Nat -> R} {t : R}
    (hg : Tendsto (fun n : Nat => n • g n) atTop (𝓝 t)) :
    Tendsto (fun x : K => x • g ⌊x⌋₊) atTop (𝓝 t) := by
  replace hg : Tendsto (fun n : Nat => (n : K) • g n) atTop (𝓝 t) := mod_cast hg
  apply tendsto_smul_congr_of_tendsto_left_cobounded_of_isBoundedUnder
    (hg.comp tendsto_nat_floor_atTop)
  · exact tendsto_natCast_atTop_cobounded.comp tendsto_nat_floor_atTop
  · apply isBoundedUnder_of_eventually_le (a := ‖(1 : K)‖)
    apply Eventually.mono _ (fun x h => norm_le_norm_of_abs_le_abs h)
    simpa using ⟨0, fun _ h => mod_cast Nat.abs_floor_sub_le h⟩

end NormedAddCommGroup

/--
lemma `tendsto_smul_comp_nat_floor_of_tendsto_mul` / 引理 `tendsto_smul_comp_nat_floor_of_tendsto_mul`

English:
lemma tendsto_smul_comp_nat_floor_of_tendsto_mul
  statement: [NormedRing K] [NormedRing R]
  proof: tendsto_smul_comp_nat_floor_of_tendsto_nsmul (by simpa only [nsmul_eq_mul] using hg)

中文:
引理 tendsto_smul_comp_nat_floor_of_tendsto_mul
  结论: [赋范环 K] [赋范环 R]
  证明: tendsto_smul_comp_nat_floor_of_tendsto_nsmul (by simpa only [nsmul_eq_mul] using hg)

Depends on / 依赖: nsmul_eq_mul, tendsto_smul_comp_nat_floor_of_tendsto_nsmul
-/
lemma tendsto_smul_comp_nat_floor_of_tendsto_mul [NormedRing K] [NormedRing R]
    [Module K R] [IsTorsionFree K R] [NormSMulClass K R] [NormSMulClass Int K] [LinearOrder K]
    [IsStrictOrderedRing K] [FloorSemiring K] [HasSolidNorm K] {g : Nat -> R} {t : R}
    (hg : Tendsto (fun n : Nat => (n : R) * g n) atTop (𝓝 t)) :
    Tendsto (fun x : K => x • g ⌊x⌋₊) atTop (𝓝 t) :=
  tendsto_smul_comp_nat_floor_of_tendsto_nsmul (by simpa only [nsmul_eq_mul] using hg)

end
