/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Order.Filter.AtTopBot.Ring

/-!
# Convergence to ±infinity in linear ordered (semi)fields
-/

public section

namespace Filter

variable {α β : Type*}

section LinearOrderedSemifield

variable [Semifield α] [LinearOrder α] [IsStrictOrderedRing α]
  {l : Filter β} {f : β -> α} {r c : α} {n : Nat}

/-!
### Multiplication by constant: iff lemmas
-/

/--
theorem `tendsto_const_mul_atTop_of_pos` / 定理 `tendsto_const_mul_atTop_of_pos`

English:
theorem tendsto_const_mul_atTop_of_pos
  given: (hr : 0 < r)
  proof: ⟨fun h => h.atTop_of_const_mul₀ hr, fun h =>
Tendsto.atTop_of_const_mul₀ (inv_pos.2 hr) by simpa only [inv_mul_cancel_left₀ hr.ne'] ⟩

中文:
定理 tendsto_const_mul_atTop_of_pos
  条件: (hr : 0 < r)
  证明: ⟨fun h => h.atTop_of_const_mul₀ hr, fun h =>
Tendsto.atTop_of_const_mul₀ (inv_pos.2 hr) by simpa only [inv_mul_cancel_left₀ hr.ne'] ⟩

Depends on / 依赖: Tendsto, Tendsto.atTop_of_const_mul, h.atTop_of_const_mul, hr.ne, inv_pos
-/
theorem tendsto_const_mul_atTop_of_pos (hr : 0 < r) :
    Tendsto (fun x => r * f x) l atTop ↔ Tendsto f l atTop :=
  ⟨fun h => h.atTop_of_const_mul₀ hr, fun h =>
Tendsto.atTop_of_const_mul₀ (inv_pos.2 hr) by simpa only [inv_mul_cancel_left₀ hr.ne'] ⟩

/--
theorem `tendsto_mul_const_atTop_of_pos` / 定理 `tendsto_mul_const_atTop_of_pos`

English:
theorem tendsto_mul_const_atTop_of_pos
  given: (hr : 0 < r)
  proof: by
  simpa only [mul_comm] using tendsto_const_mul_atTop_of_pos hr

中文:
定理 tendsto_mul_const_atTop_of_pos
  条件: (hr : 0 < r)
  证明: by
  simpa only [mul_comm] using tendsto_const_mul_atTop_of_pos hr

Depends on / 依赖: mul_comm, tendsto_const_mul_atTop_of_pos
-/
theorem tendsto_mul_const_atTop_of_pos (hr : 0 < r) :
    Tendsto (fun x => f x * r) l atTop ↔ Tendsto f l atTop := by
  simpa only [mul_comm] using tendsto_const_mul_atTop_of_pos hr

/--
lemma `tendsto_div_const_atTop_of_pos` / 引理 `tendsto_div_const_atTop_of_pos`

English:
lemma tendsto_div_const_atTop_of_pos
  given: (hr : 0 < r)
  proof: by
  simpa only [div_eq_mul_inv] using tendsto_mul_const_atTop_of_pos (inv_pos.2 hr)

中文:
引理 tendsto_div_const_atTop_of_pos
  条件: (hr : 0 < r)
  证明: by
  simpa only [div_eq_mul_inv] using tendsto_mul_const_atTop_of_pos (inv_pos.2 hr)

Depends on / 依赖: div_eq_mul_inv, inv_pos, tendsto_mul_const_atTop_of_pos
-/
lemma tendsto_div_const_atTop_of_pos (hr : 0 < r) :
    Tendsto (fun x => f x / r) l atTop ↔ Tendsto f l atTop := by
  simpa only [div_eq_mul_inv] using tendsto_mul_const_atTop_of_pos (inv_pos.2 hr)

/--
theorem `tendsto_const_mul_atTop_iff_pos` / 定理 `tendsto_const_mul_atTop_iff_pos`

English:
theorem tendsto_const_mul_atTop_iff_pos
  given: [NeBot l] (h : Tendsto f l atTop)
  proof: by
  refine ⟨fun hrf => not_le.mp fun hr => ?_, fun hr => (tendsto_const_mul_atTop_of_pos hr).mpr h⟩
  rcases ((h.eventually_ge_atTop 0).and (hrf.eventually_gt_atTop 0)).exists with ⟨x, hx, hrx⟩
  exact (mul_nonpos_of_nonpos_of_nonneg hr hx).not_gt hrx

中文:
定理 tendsto_const_mul_atTop_iff_pos
  条件: [NeBot l] (h : Tendsto f l atTop)
  证明: by
  refine ⟨fun hrf => not_le.mp fun hr => ?_, fun hr => (tendsto_const_mul_atTop_of_pos hr).mpr h⟩
  rcases ((h.eventually_ge_atTop 0).and (hrf.eventually_gt_atTop 0)).exists with ⟨x, hx, hrx⟩
  exact (mul_nonpos_of_nonpos_of_nonneg hr hx).not_gt hrx

Depends on / 依赖: eventually_ge_atTop, eventually_gt_atTop, h.eventually_ge_atTop, hrf.eventually_gt_atTop, mul_nonpos_of_nonpos_of_nonneg, not_gt, not_le, not_le.mp, tendsto_const_mul_atTop_of_pos
-/
theorem tendsto_const_mul_atTop_iff_pos [NeBot l] (h : Tendsto f l atTop) :
    Tendsto (fun x => r * f x) l atTop ↔ 0 < r := by
  refine ⟨fun hrf => not_le.mp fun hr => ?_, fun hr => (tendsto_const_mul_atTop_of_pos hr).mpr h⟩
  rcases ((h.eventually_ge_atTop 0).and (hrf.eventually_gt_atTop 0)).exists with ⟨x, hx, hrx⟩
  exact (mul_nonpos_of_nonpos_of_nonneg hr hx).not_gt hrx

/--
theorem `tendsto_mul_const_atTop_iff_pos` / 定理 `tendsto_mul_const_atTop_iff_pos`

English:
theorem tendsto_mul_const_atTop_iff_pos
  given: [NeBot l] (h : Tendsto f l atTop)
  proof: by
  simp only [mul_comm _ r, tendsto_const_mul_atTop_iff_pos h]

中文:
定理 tendsto_mul_const_atTop_iff_pos
  条件: [NeBot l] (h : Tendsto f l atTop)
  证明: by
  simp only [mul_comm _ r, tendsto_const_mul_atTop_iff_pos h]

Depends on / 依赖: mul_comm, tendsto_const_mul_atTop_iff_pos
-/
theorem tendsto_mul_const_atTop_iff_pos [NeBot l] (h : Tendsto f l atTop) :
    Tendsto (fun x => f x * r) l atTop ↔ 0 < r := by
  simp only [mul_comm _ r, tendsto_const_mul_atTop_iff_pos h]

/--
lemma `tendsto_div_const_atTop_iff_pos` / 引理 `tendsto_div_const_atTop_iff_pos`

English:
lemma tendsto_div_const_atTop_iff_pos
  given: [NeBot l] (h : Tendsto f l atTop)
  proof: by
  simp only [div_eq_mul_inv, tendsto_mul_const_atTop_iff_pos h, inv_pos]

中文:
引理 tendsto_div_const_atTop_iff_pos
  条件: [NeBot l] (h : Tendsto f l atTop)
  证明: by
  simp only [div_eq_mul_inv, tendsto_mul_const_atTop_iff_pos h, inv_pos]

Depends on / 依赖: div_eq_mul_inv, inv_pos, tendsto_mul_const_atTop_iff_pos
-/
lemma tendsto_div_const_atTop_iff_pos [NeBot l] (h : Tendsto f l atTop) :
    Tendsto (fun x => f x / r) l atTop ↔ 0 < r := by
  simp only [div_eq_mul_inv, tendsto_mul_const_atTop_iff_pos h, inv_pos]

/--
theorem `Tendsto.const_mul_atTop` / 定理 `Tendsto.const_mul_atTop`

English:
theorem Tendsto.const_mul_atTop
  given: (hr : 0 < r) (hf : Tendsto f l atTop)
  proof: (tendsto_const_mul_atTop_of_pos hr).2 hf

中文:
定理 Tendsto.const_mul_atTop
  条件: (hr : 0 < r) (hf : Tendsto f l atTop)
  证明: (tendsto_const_mul_atTop_of_pos hr).2 hf

Depends on / 依赖: tendsto_const_mul_atTop_of_pos
-/
theorem Tendsto.const_mul_atTop (hr : 0 < r) (hf : Tendsto f l atTop) :
    Tendsto (fun x => r * f x) l atTop :=
  (tendsto_const_mul_atTop_of_pos hr).2 hf

/--
theorem `Tendsto.atTop_mul_const` / 定理 `Tendsto.atTop_mul_const`

English:
theorem Tendsto.atTop_mul_const
  given: (hr : 0 < r) (hf : Tendsto f l atTop)
  proof: (tendsto_mul_const_atTop_of_pos hr).2 hf

中文:
定理 Tendsto.atTop_mul_const
  条件: (hr : 0 < r) (hf : Tendsto f l atTop)
  证明: (tendsto_mul_const_atTop_of_pos hr).2 hf

Depends on / 依赖: tendsto_mul_const_atTop_of_pos
-/
theorem Tendsto.atTop_mul_const (hr : 0 < r) (hf : Tendsto f l atTop) :
    Tendsto (fun x => f x * r) l atTop :=
  (tendsto_mul_const_atTop_of_pos hr).2 hf

/--
theorem `Tendsto.atTop_div_const` / 定理 `Tendsto.atTop_div_const`

English:
theorem Tendsto.atTop_div_const
  given: (hr : 0 < r) (hf : Tendsto f l atTop)
  proof: by
  simpa only [div_eq_mul_inv] using hf.atTop_mul_const (inv_pos.2 hr)

中文:
定理 Tendsto.atTop_div_const
  条件: (hr : 0 < r) (hf : Tendsto f l atTop)
  证明: by
  simpa only [div_eq_mul_inv] using hf.atTop_mul_const (inv_pos.2 hr)

Depends on / 依赖: atTop_mul_const, div_eq_mul_inv, hf.atTop_mul_const, inv_pos
-/
theorem Tendsto.atTop_div_const (hr : 0 < r) (hf : Tendsto f l atTop) :
    Tendsto (fun x => f x / r) l atTop := by
  simpa only [div_eq_mul_inv] using hf.atTop_mul_const (inv_pos.2 hr)

/--
theorem `tendsto_const_mul_pow_atTop` / 定理 `tendsto_const_mul_pow_atTop`

English:
theorem tendsto_const_mul_pow_atTop
  given: (hn : n != 0) (hc : 0 < c)
  proof: Tendsto.const_mul_atTop hc (tendsto_pow_atTop hn)

中文:
定理 tendsto_const_mul_pow_atTop
  条件: (hn : n != 0) (hc : 0 < c)
  证明: Tendsto.const_mul_atTop hc (tendsto_pow_atTop hn)

Depends on / 依赖: DivisionRing, Finite, Tendsto, Tendsto.const_mul_atTop, const_mul_atTop, littleWedderburn, tendsto_pow_atTop
-/
theorem tendsto_const_mul_pow_atTop (hn : n != 0) (hc : 0 < c) :
    Tendsto (fun x => c * x ^ n) atTop atTop :=
  Tendsto.const_mul_atTop hc (tendsto_pow_atTop hn)

/--
theorem `tendsto_const_mul_pow_atTop_iff` / 定理 `tendsto_const_mul_pow_atTop_iff`

English:
theorem tendsto_const_mul_pow_atTop_iff
  proof: by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => tendsto_const_mul_pow_atTop h.1 h.2⟩
  · rintro rfl
    simp only [pow_zero, not_tendsto_const_atTop] at h
  · rcases ((h.eventually_gt_atTop 0).and (eventually_ge_atTop 0)).exists with ⟨k, hck, hk⟩
    exact pos_of_mul_pos_left hck (pow_nonneg hk _)

中文:
定理 tendsto_const_mul_pow_atTop_iff
  证明: by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => tendsto_const_mul_pow_atTop h.1 h.2⟩
  · rintro rfl
    simp only [pow_zero, not_tendsto_const_atTop] at h
  · rcases ((h.eventually_gt_atTop 0).and (eventually_ge_atTop 0)).exists with ⟨k, hck, hk⟩
    exact pos_of_mul_pos_left hck (pow_nonneg hk _)

Depends on / 依赖: eventually_ge_atTop, eventually_gt_atTop, h.eventually_gt_atTop, not_tendsto_const_atTop, pos_of_mul_pos_left, pow_nonneg, pow_zero, tendsto_const_mul_pow_atTop
-/
theorem tendsto_const_mul_pow_atTop_iff :
    Tendsto (fun x => c * x ^ n) atTop atTop ↔ n != 0 ∧ 0 < c := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => tendsto_const_mul_pow_atTop h.1 h.2⟩
  · rintro rfl
    simp only [pow_zero, not_tendsto_const_atTop] at h
  · rcases ((h.eventually_gt_atTop 0).and (eventually_ge_atTop 0)).exists with ⟨k, hck, hk⟩
    exact pos_of_mul_pos_left hck (pow_nonneg hk _)

/--
lemma `tendsto_zpow_atTop_atTop` / 引理 `tendsto_zpow_atTop_atTop`

English:
lemma tendsto_zpow_atTop_atTop
  given: {n : Int} (hn : 0 < n)
  statement: Tendsto (fun x : α => x ^ n) atTop atTop
  proof: by
  lift n to Nat using hn.le; simp [(Int.natCast_pos.mp hn).ne']

中文:
引理 tendsto_zpow_atTop_atTop
  条件: {n : 整数} (hn : 0 < n)
  结论: Tendsto (fun x : α => x ^ n) atTop atTop
  证明: by
  lift n to Nat using hn.le; simp [(Int.natCast_pos.mp hn).ne']

Depends on / 依赖: Int.natCast_pos.mp, hn.le, natCast_pos
-/
lemma tendsto_zpow_atTop_atTop {n : Int} (hn : 0 < n) : Tendsto (fun x : α => x ^ n) atTop atTop := by
  lift n to Nat using hn.le; simp [(Int.natCast_pos.mp hn).ne']

/--
theorem `map_div_atTop_eq` / 定理 `map_div_atTop_eq`

English:
theorem map_div_atTop_eq
  given: (k : α) (hk : 0 < k)
  statement: map (fun a => a / k) atTop = atTop
  proof: map_atTop_eq_of_gc (fun b => k * b) 1 (fun _ _ h => div_le_div_of_nonneg_right h (le_of_lt hk))
    (fun a b _ => (by rw [div_le_iff₀' hk]))
    fun b _ => (by rw [mul_div_assoc, mul_div_cancel₀]; exact ne_of_gt hk)

中文:
定理 map_div_atTop_eq
  条件: (k : α) (hk : 0 < k)
  结论: map (fun a => a / k) atTop = atTop
  证明: map_atTop_eq_of_gc (fun b => k * b) 1 (fun _ _ h => div_le_div_of_nonneg_right h (le_of_lt hk))
    (fun a b _ => (by rw [div_le_iff₀' hk]))
    fun b _ => (by rw [mul_div_assoc, mul_div_cancel₀]; exact ne_of_gt hk)

Depends on / 依赖: div_le_div_of_nonneg_right, le_of_lt, map_atTop_eq_of_gc, mul_div_assoc, ne_of_gt
-/
theorem map_div_atTop_eq (k : α) (hk : 0 < k) : map (fun a => a / k) atTop = atTop :=
  map_atTop_eq_of_gc (fun b => k * b) 1 (fun _ _ h => div_le_div_of_nonneg_right h (le_of_lt hk))
    (fun a b _ => (by rw [div_le_iff₀' hk]))
    fun b _ => (by rw [mul_div_assoc, mul_div_cancel₀]; exact ne_of_gt hk)

end LinearOrderedSemifield


section LinearOrderedField

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {l : Filter β} {f : β -> α} {r : α}

/--
theorem `tendsto_const_mul_atBot_of_pos` / 定理 `tendsto_const_mul_atBot_of_pos`

English:
theorem tendsto_const_mul_atBot_of_pos
  given: (hr : 0 < r)
  proof: by
  simpa only [← mul_neg, ← tendsto_neg_atTop_iff] using tendsto_const_mul_atTop_of_pos hr

中文:
定理 tendsto_const_mul_atBot_of_pos
  条件: (hr : 0 < r)
  证明: by
  simpa only [← mul_neg, ← tendsto_neg_atTop_iff] using tendsto_const_mul_atTop_of_pos hr

Depends on / 依赖: IsLocalIso, IsStandardOpenImmersion, mul_neg, tendsto_const_mul_atTop_of_pos, tendsto_neg_atTop_iff
-/
theorem tendsto_const_mul_atBot_of_pos (hr : 0 < r) :
    Tendsto (fun x => r * f x) l atBot ↔ Tendsto f l atBot := by
  simpa only [← mul_neg, ← tendsto_neg_atTop_iff] using tendsto_const_mul_atTop_of_pos hr

/--
theorem `tendsto_mul_const_atBot_of_pos` / 定理 `tendsto_mul_const_atBot_of_pos`

English:
theorem tendsto_mul_const_atBot_of_pos
  given: (hr : 0 < r)
  proof: by
  simpa only [mul_comm] using tendsto_const_mul_atBot_of_pos hr

中文:
定理 tendsto_mul_const_atBot_of_pos
  条件: (hr : 0 < r)
  证明: by
  simpa only [mul_comm] using tendsto_const_mul_atBot_of_pos hr

Depends on / 依赖: mul_comm, tendsto_const_mul_atBot_of_pos
-/
theorem tendsto_mul_const_atBot_of_pos (hr : 0 < r) :
    Tendsto (fun x => f x * r) l atBot ↔ Tendsto f l atBot := by
  simpa only [mul_comm] using tendsto_const_mul_atBot_of_pos hr

/--
lemma `tendsto_div_const_atBot_of_pos` / 引理 `tendsto_div_const_atBot_of_pos`

English:
lemma tendsto_div_const_atBot_of_pos
  given: (hr : 0 < r)
  proof: by
  simp [div_eq_mul_inv, tendsto_mul_const_atBot_of_pos, hr]

中文:
引理 tendsto_div_const_atBot_of_pos
  条件: (hr : 0 < r)
  证明: by
  simp [div_eq_mul_inv, tendsto_mul_const_atBot_of_pos, hr]

Depends on / 依赖: div_eq_mul_inv, tendsto_mul_const_atBot_of_pos
-/
lemma tendsto_div_const_atBot_of_pos (hr : 0 < r) :
    Tendsto (fun x => f x / r) l atBot ↔ Tendsto f l atBot := by
  simp [div_eq_mul_inv, tendsto_mul_const_atBot_of_pos, hr]

/--
theorem `tendsto_const_mul_atTop_of_neg` / 定理 `tendsto_const_mul_atTop_of_neg`

English:
theorem tendsto_const_mul_atTop_of_neg
  given: (hr : r < 0)
  proof: by
  simpa only [neg_mul, tendsto_neg_atBot_iff] using tendsto_const_mul_atBot_of_pos (neg_pos.2 hr)

中文:
定理 tendsto_const_mul_atTop_of_neg
  条件: (hr : r < 0)
  证明: by
  simpa only [neg_mul, tendsto_neg_atBot_iff] using tendsto_const_mul_atBot_of_pos (neg_pos.2 hr)

Depends on / 依赖: neg_mul, neg_pos, tendsto_const_mul_atBot_of_pos, tendsto_neg_atBot_iff
-/
theorem tendsto_const_mul_atTop_of_neg (hr : r < 0) :
    Tendsto (fun x => r * f x) l atTop ↔ Tendsto f l atBot := by
  simpa only [neg_mul, tendsto_neg_atBot_iff] using tendsto_const_mul_atBot_of_pos (neg_pos.2 hr)

/--
theorem `tendsto_mul_const_atTop_of_neg` / 定理 `tendsto_mul_const_atTop_of_neg`

English:
theorem tendsto_mul_const_atTop_of_neg
  given: (hr : r < 0)
  proof: by
  simpa only [mul_comm] using tendsto_const_mul_atTop_of_neg hr

中文:
定理 tendsto_mul_const_atTop_of_neg
  条件: (hr : r < 0)
  证明: by
  simpa only [mul_comm] using tendsto_const_mul_atTop_of_neg hr

Depends on / 依赖: mul_comm, tendsto_const_mul_atTop_of_neg
-/
theorem tendsto_mul_const_atTop_of_neg (hr : r < 0) :
    Tendsto (fun x => f x * r) l atTop ↔ Tendsto f l atBot := by
  simpa only [mul_comm] using tendsto_const_mul_atTop_of_neg hr

/--
lemma `tendsto_div_const_atTop_of_neg` / 引理 `tendsto_div_const_atTop_of_neg`

English:
lemma tendsto_div_const_atTop_of_neg
  given: (hr : r < 0)
  proof: by
  simp [div_eq_mul_inv, tendsto_mul_const_atTop_of_neg, hr]

中文:
引理 tendsto_div_const_atTop_of_neg
  条件: (hr : r < 0)
  证明: by
  simp [div_eq_mul_inv, tendsto_mul_const_atTop_of_neg, hr]

Depends on / 依赖: div_eq_mul_inv, tendsto_mul_const_atTop_of_neg
-/
lemma tendsto_div_const_atTop_of_neg (hr : r < 0) :
    Tendsto (fun x => f x / r) l atTop ↔ Tendsto f l atBot := by
  simp [div_eq_mul_inv, tendsto_mul_const_atTop_of_neg, hr]

/--
theorem `tendsto_const_mul_atBot_of_neg` / 定理 `tendsto_const_mul_atBot_of_neg`

English:
theorem tendsto_const_mul_atBot_of_neg
  given: (hr : r < 0)
  proof: by
  simpa only [neg_mul, tendsto_neg_atTop_iff] using tendsto_const_mul_atTop_of_pos (neg_pos.2 hr)

中文:
定理 tendsto_const_mul_atBot_of_neg
  条件: (hr : r < 0)
  证明: by
  simpa only [neg_mul, tendsto_neg_atTop_iff] using tendsto_const_mul_atTop_of_pos (neg_pos.2 hr)

Depends on / 依赖: neg_mul, neg_pos, tendsto_const_mul_atTop_of_pos, tendsto_neg_atTop_iff
-/
theorem tendsto_const_mul_atBot_of_neg (hr : r < 0) :
    Tendsto (fun x => r * f x) l atBot ↔ Tendsto f l atTop := by
  simpa only [neg_mul, tendsto_neg_atTop_iff] using tendsto_const_mul_atTop_of_pos (neg_pos.2 hr)

/--
theorem `tendsto_mul_const_atBot_of_neg` / 定理 `tendsto_mul_const_atBot_of_neg`

English:
theorem tendsto_mul_const_atBot_of_neg
  given: (hr : r < 0)
  proof: by
  simpa only [mul_comm] using tendsto_const_mul_atBot_of_neg hr

中文:
定理 tendsto_mul_const_atBot_of_neg
  条件: (hr : r < 0)
  证明: by
  simpa only [mul_comm] using tendsto_const_mul_atBot_of_neg hr

Depends on / 依赖: mul_comm, tendsto_const_mul_atBot_of_neg
-/
theorem tendsto_mul_const_atBot_of_neg (hr : r < 0) :
    Tendsto (fun x => f x * r) l atBot ↔ Tendsto f l atTop := by
  simpa only [mul_comm] using tendsto_const_mul_atBot_of_neg hr

/--
lemma `tendsto_div_const_atBot_of_neg` / 引理 `tendsto_div_const_atBot_of_neg`

English:
lemma tendsto_div_const_atBot_of_neg
  given: (hr : r < 0)
  proof: by
  simp [div_eq_mul_inv, tendsto_mul_const_atBot_of_neg, hr]

中文:
引理 tendsto_div_const_atBot_of_neg
  条件: (hr : r < 0)
  证明: by
  simp [div_eq_mul_inv, tendsto_mul_const_atBot_of_neg, hr]

Depends on / 依赖: div_eq_mul_inv, tendsto_mul_const_atBot_of_neg
-/
lemma tendsto_div_const_atBot_of_neg (hr : r < 0) :
    Tendsto (fun x => f x / r) l atBot ↔ Tendsto f l atTop := by
  simp [div_eq_mul_inv, tendsto_mul_const_atBot_of_neg, hr]

/--
theorem `tendsto_const_mul_atTop_iff` / 定理 `tendsto_const_mul_atTop_iff`

English:
theorem tendsto_const_mul_atTop_iff
  given: [NeBot l]
  proof: by
  rcases lt_trichotomy r 0 with (hr | rfl | hr)
  · simp [hr, hr.not_gt, tendsto_const_mul_atTop_of_neg]
  · simp [not_tendsto_const_atTop]
  · simp [hr, hr.not_gt, tendsto_const_mul_atTop_of_pos]

中文:
定理 tendsto_const_mul_atTop_iff
  条件: [NeBot l]
  证明: by
  rcases lt_trichotomy r 0 with (hr | rfl | hr)
  · simp [hr, hr.not_gt, tendsto_const_mul_atTop_of_neg]
  · simp [not_tendsto_const_atTop]
  · simp [hr, hr.not_gt, tendsto_const_mul_atTop_of_pos]

Depends on / 依赖: hr.not_gt, lt_trichotomy, not_gt, not_tendsto_const_atTop, tendsto_const_mul_atTop_of_neg, tendsto_const_mul_atTop_of_pos
-/
theorem tendsto_const_mul_atTop_iff [NeBot l] :
    Tendsto (fun x => r * f x) l atTop ↔ 0 < r ∧ Tendsto f l atTop ∨ r < 0 ∧ Tendsto f l atBot := by
  rcases lt_trichotomy r 0 with (hr | rfl | hr)
  · simp [hr, hr.not_gt, tendsto_const_mul_atTop_of_neg]
  · simp [not_tendsto_const_atTop]
  · simp [hr, hr.not_gt, tendsto_const_mul_atTop_of_pos]

/--
theorem `tendsto_mul_const_atTop_iff` / 定理 `tendsto_mul_const_atTop_iff`

English:
theorem tendsto_mul_const_atTop_iff
  given: [NeBot l]
  proof: by
  simp only [mul_comm _ r, tendsto_const_mul_atTop_iff]

中文:
定理 tendsto_mul_const_atTop_iff
  条件: [NeBot l]
  证明: by
  simp only [mul_comm _ r, tendsto_const_mul_atTop_iff]

Depends on / 依赖: mul_comm, tendsto_const_mul_atTop_iff
-/
theorem tendsto_mul_const_atTop_iff [NeBot l] :
    Tendsto (fun x => f x * r) l atTop ↔ 0 < r ∧ Tendsto f l atTop ∨ r < 0 ∧ Tendsto f l atBot := by
  simp only [mul_comm _ r, tendsto_const_mul_atTop_iff]

/--
lemma `tendsto_div_const_atTop_iff` / 引理 `tendsto_div_const_atTop_iff`

English:
lemma tendsto_div_const_atTop_iff
  given: [NeBot l]
  proof: by
  simp [div_eq_mul_inv, tendsto_mul_const_atTop_iff]

中文:
引理 tendsto_div_const_atTop_iff
  条件: [NeBot l]
  证明: by
  simp [div_eq_mul_inv, tendsto_mul_const_atTop_iff]

Depends on / 依赖: div_eq_mul_inv, tendsto_mul_const_atTop_iff
-/
lemma tendsto_div_const_atTop_iff [NeBot l] :
    Tendsto (fun x => f x / r) l atTop ↔ 0 < r ∧ Tendsto f l atTop ∨ r < 0 ∧ Tendsto f l atBot := by
  simp [div_eq_mul_inv, tendsto_mul_const_atTop_iff]

/--
theorem `tendsto_const_mul_atBot_iff` / 定理 `tendsto_const_mul_atBot_iff`

English:
theorem tendsto_const_mul_atBot_iff
  given: [NeBot l]
  proof: by
  simp only [← tendsto_neg_atTop_iff, ← mul_neg, tendsto_const_mul_atTop_iff, neg_neg]

中文:
定理 tendsto_const_mul_atBot_iff
  条件: [NeBot l]
  证明: by
  simp only [← tendsto_neg_atTop_iff, ← mul_neg, tendsto_const_mul_atTop_iff, neg_neg]

Depends on / 依赖: mul_neg, neg_neg, tendsto_const_mul_atTop_iff, tendsto_neg_atTop_iff
-/
theorem tendsto_const_mul_atBot_iff [NeBot l] :
    Tendsto (fun x => r * f x) l atBot ↔ 0 < r ∧ Tendsto f l atBot ∨ r < 0 ∧ Tendsto f l atTop := by
  simp only [← tendsto_neg_atTop_iff, ← mul_neg, tendsto_const_mul_atTop_iff, neg_neg]

/--
theorem `tendsto_mul_const_atBot_iff` / 定理 `tendsto_mul_const_atBot_iff`

English:
theorem tendsto_mul_const_atBot_iff
  given: [NeBot l]
  proof: by
  simp only [mul_comm _ r, tendsto_const_mul_atBot_iff]

中文:
定理 tendsto_mul_const_atBot_iff
  条件: [NeBot l]
  证明: by
  simp only [mul_comm _ r, tendsto_const_mul_atBot_iff]

Depends on / 依赖: mul_comm, tendsto_const_mul_atBot_iff
-/
theorem tendsto_mul_const_atBot_iff [NeBot l] :
    Tendsto (fun x => f x * r) l atBot ↔ 0 < r ∧ Tendsto f l atBot ∨ r < 0 ∧ Tendsto f l atTop := by
  simp only [mul_comm _ r, tendsto_const_mul_atBot_iff]

/--
lemma `tendsto_div_const_atBot_iff` / 引理 `tendsto_div_const_atBot_iff`

English:
lemma tendsto_div_const_atBot_iff
  given: [NeBot l]
  proof: by
  simp [div_eq_mul_inv, tendsto_mul_const_atBot_iff]

中文:
引理 tendsto_div_const_atBot_iff
  条件: [NeBot l]
  证明: by
  simp [div_eq_mul_inv, tendsto_mul_const_atBot_iff]

Depends on / 依赖: div_eq_mul_inv, tendsto_mul_const_atBot_iff
-/
lemma tendsto_div_const_atBot_iff [NeBot l] :
    Tendsto (fun x => f x / r) l atBot ↔ 0 < r ∧ Tendsto f l atBot ∨ r < 0 ∧ Tendsto f l atTop := by
  simp [div_eq_mul_inv, tendsto_mul_const_atBot_iff]

/--
theorem `tendsto_const_mul_atTop_iff_neg` / 定理 `tendsto_const_mul_atTop_iff_neg`

English:
theorem tendsto_const_mul_atTop_iff_neg
  given: [NeBot l] (h : Tendsto f l atBot)
  proof: by
  simp [tendsto_const_mul_atTop_iff, h, h.not_tendsto disjoint_atBot_atTop]

中文:
定理 tendsto_const_mul_atTop_iff_neg
  条件: [NeBot l] (h : Tendsto f l atBot)
  证明: by
  simp [tendsto_const_mul_atTop_iff, h, h.not_tendsto disjoint_atBot_atTop]

Depends on / 依赖: disjoint_atBot_atTop, h.not_tendsto, not_tendsto, tendsto_const_mul_atTop_iff
-/
theorem tendsto_const_mul_atTop_iff_neg [NeBot l] (h : Tendsto f l atBot) :
    Tendsto (fun x => r * f x) l atTop ↔ r < 0 := by
  simp [tendsto_const_mul_atTop_iff, h, h.not_tendsto disjoint_atBot_atTop]

/--
theorem `tendsto_mul_const_atTop_iff_neg` / 定理 `tendsto_mul_const_atTop_iff_neg`

English:
theorem tendsto_mul_const_atTop_iff_neg
  given: [NeBot l] (h : Tendsto f l atBot)
  proof: by
  simp only [mul_comm _ r, tendsto_const_mul_atTop_iff_neg h]

中文:
定理 tendsto_mul_const_atTop_iff_neg
  条件: [NeBot l] (h : Tendsto f l atBot)
  证明: by
  simp only [mul_comm _ r, tendsto_const_mul_atTop_iff_neg h]

Depends on / 依赖: mul_comm, tendsto_const_mul_atTop_iff_neg
-/
theorem tendsto_mul_const_atTop_iff_neg [NeBot l] (h : Tendsto f l atBot) :
    Tendsto (fun x => f x * r) l atTop ↔ r < 0 := by
  simp only [mul_comm _ r, tendsto_const_mul_atTop_iff_neg h]

/--
lemma `tendsto_div_const_atTop_iff_neg` / 引理 `tendsto_div_const_atTop_iff_neg`

English:
lemma tendsto_div_const_atTop_iff_neg
  given: [NeBot l] (h : Tendsto f l atBot)
  proof: by
  simp [div_eq_mul_inv, tendsto_mul_const_atTop_iff_neg h]

中文:
引理 tendsto_div_const_atTop_iff_neg
  条件: [NeBot l] (h : Tendsto f l atBot)
  证明: by
  simp [div_eq_mul_inv, tendsto_mul_const_atTop_iff_neg h]

Depends on / 依赖: div_eq_mul_inv, tendsto_mul_const_atTop_iff_neg
-/
lemma tendsto_div_const_atTop_iff_neg [NeBot l] (h : Tendsto f l atBot) :
    Tendsto (fun x => f x / r) l atTop ↔ r < 0 := by
  simp [div_eq_mul_inv, tendsto_mul_const_atTop_iff_neg h]

/--
theorem `tendsto_const_mul_atBot_iff_pos` / 定理 `tendsto_const_mul_atBot_iff_pos`

English:
theorem tendsto_const_mul_atBot_iff_pos
  given: [NeBot l] (h : Tendsto f l atBot)
  proof: by
  simp [tendsto_const_mul_atBot_iff, h, h.not_tendsto disjoint_atBot_atTop]

中文:
定理 tendsto_const_mul_atBot_iff_pos
  条件: [NeBot l] (h : Tendsto f l atBot)
  证明: by
  simp [tendsto_const_mul_atBot_iff, h, h.not_tendsto disjoint_atBot_atTop]

Depends on / 依赖: disjoint_atBot_atTop, h.not_tendsto, not_tendsto, tendsto_const_mul_atBot_iff
-/
theorem tendsto_const_mul_atBot_iff_pos [NeBot l] (h : Tendsto f l atBot) :
    Tendsto (fun x => r * f x) l atBot ↔ 0 < r := by
  simp [tendsto_const_mul_atBot_iff, h, h.not_tendsto disjoint_atBot_atTop]

/--
theorem `tendsto_mul_const_atBot_iff_pos` / 定理 `tendsto_mul_const_atBot_iff_pos`

English:
theorem tendsto_mul_const_atBot_iff_pos
  given: [NeBot l] (h : Tendsto f l atBot)
  proof: by
  simp only [mul_comm _ r, tendsto_const_mul_atBot_iff_pos h]

中文:
定理 tendsto_mul_const_atBot_iff_pos
  条件: [NeBot l] (h : Tendsto f l atBot)
  证明: by
  simp only [mul_comm _ r, tendsto_const_mul_atBot_iff_pos h]

Depends on / 依赖: mul_comm, tendsto_const_mul_atBot_iff_pos
-/
theorem tendsto_mul_const_atBot_iff_pos [NeBot l] (h : Tendsto f l atBot) :
    Tendsto (fun x => f x * r) l atBot ↔ 0 < r := by
  simp only [mul_comm _ r, tendsto_const_mul_atBot_iff_pos h]

/--
lemma `tendsto_div_const_atBot_iff_pos` / 引理 `tendsto_div_const_atBot_iff_pos`

English:
lemma tendsto_div_const_atBot_iff_pos
  given: [NeBot l] (h : Tendsto f l atBot)
  proof: by
  simp [div_eq_mul_inv, tendsto_mul_const_atBot_iff_pos h]

中文:
引理 tendsto_div_const_atBot_iff_pos
  条件: [NeBot l] (h : Tendsto f l atBot)
  证明: by
  simp [div_eq_mul_inv, tendsto_mul_const_atBot_iff_pos h]

Depends on / 依赖: div_eq_mul_inv, tendsto_mul_const_atBot_iff_pos
-/
lemma tendsto_div_const_atBot_iff_pos [NeBot l] (h : Tendsto f l atBot) :
    Tendsto (fun x => f x / r) l atBot ↔ 0 < r := by
  simp [div_eq_mul_inv, tendsto_mul_const_atBot_iff_pos h]

/--
theorem `tendsto_const_mul_atBot_iff_neg` / 定理 `tendsto_const_mul_atBot_iff_neg`

English:
theorem tendsto_const_mul_atBot_iff_neg
  given: [NeBot l] (h : Tendsto f l atTop)
  proof: by
  simp [tendsto_const_mul_atBot_iff, h, h.not_tendsto disjoint_atTop_atBot]

中文:
定理 tendsto_const_mul_atBot_iff_neg
  条件: [NeBot l] (h : Tendsto f l atTop)
  证明: by
  simp [tendsto_const_mul_atBot_iff, h, h.not_tendsto disjoint_atTop_atBot]

Depends on / 依赖: disjoint_atTop_atBot, h.not_tendsto, not_tendsto, tendsto_const_mul_atBot_iff
-/
theorem tendsto_const_mul_atBot_iff_neg [NeBot l] (h : Tendsto f l atTop) :
    Tendsto (fun x => r * f x) l atBot ↔ r < 0 := by
  simp [tendsto_const_mul_atBot_iff, h, h.not_tendsto disjoint_atTop_atBot]

/--
theorem `tendsto_mul_const_atBot_iff_neg` / 定理 `tendsto_mul_const_atBot_iff_neg`

English:
theorem tendsto_mul_const_atBot_iff_neg
  given: [NeBot l] (h : Tendsto f l atTop)
  proof: by
  simp only [mul_comm _ r, tendsto_const_mul_atBot_iff_neg h]

中文:
定理 tendsto_mul_const_atBot_iff_neg
  条件: [NeBot l] (h : Tendsto f l atTop)
  证明: by
  simp only [mul_comm _ r, tendsto_const_mul_atBot_iff_neg h]

Depends on / 依赖: mul_comm, tendsto_const_mul_atBot_iff_neg
-/
theorem tendsto_mul_const_atBot_iff_neg [NeBot l] (h : Tendsto f l atTop) :
    Tendsto (fun x => f x * r) l atBot ↔ r < 0 := by
  simp only [mul_comm _ r, tendsto_const_mul_atBot_iff_neg h]

/--
lemma `tendsto_div_const_atBot_iff_neg` / 引理 `tendsto_div_const_atBot_iff_neg`

English:
lemma tendsto_div_const_atBot_iff_neg
  given: [NeBot l] (h : Tendsto f l atTop)
  proof: by
  simp [div_eq_mul_inv, tendsto_mul_const_atBot_iff_neg h]

中文:
引理 tendsto_div_const_atBot_iff_neg
  条件: [NeBot l] (h : Tendsto f l atTop)
  证明: by
  simp [div_eq_mul_inv, tendsto_mul_const_atBot_iff_neg h]

Depends on / 依赖: div_eq_mul_inv, tendsto_mul_const_atBot_iff_neg
-/
lemma tendsto_div_const_atBot_iff_neg [NeBot l] (h : Tendsto f l atTop) :
    Tendsto (fun x => f x / r) l atBot ↔ r < 0 := by
  simp [div_eq_mul_inv, tendsto_mul_const_atBot_iff_neg h]

/--
theorem `Tendsto.const_mul_atTop_of_neg` / 定理 `Tendsto.const_mul_atTop_of_neg`

English:
theorem Tendsto.const_mul_atTop_of_neg
  given: (hr : r < 0) (hf : Tendsto f l atTop)
  proof: (tendsto_const_mul_atBot_of_neg hr).2 hf

中文:
定理 Tendsto.const_mul_atTop_of_neg
  条件: (hr : r < 0) (hf : Tendsto f l atTop)
  证明: (tendsto_const_mul_atBot_of_neg hr).2 hf

Depends on / 依赖: tendsto_const_mul_atBot_of_neg
-/
theorem Tendsto.const_mul_atTop_of_neg (hr : r < 0) (hf : Tendsto f l atTop) :
    Tendsto (fun x => r * f x) l atBot :=
  (tendsto_const_mul_atBot_of_neg hr).2 hf

/--
theorem `Tendsto.atTop_mul_const_of_neg` / 定理 `Tendsto.atTop_mul_const_of_neg`

English:
theorem Tendsto.atTop_mul_const_of_neg
  given: (hr : r < 0) (hf : Tendsto f l atTop)
  proof: (tendsto_mul_const_atBot_of_neg hr).2 hf

中文:
定理 Tendsto.atTop_mul_const_of_neg
  条件: (hr : r < 0) (hf : Tendsto f l atTop)
  证明: (tendsto_mul_const_atBot_of_neg hr).2 hf

Depends on / 依赖: tendsto_mul_const_atBot_of_neg
-/
theorem Tendsto.atTop_mul_const_of_neg (hr : r < 0) (hf : Tendsto f l atTop) :
    Tendsto (fun x => f x * r) l atBot :=
  (tendsto_mul_const_atBot_of_neg hr).2 hf

/--
lemma `Tendsto.atTop_div_const_of_neg` / 引理 `Tendsto.atTop_div_const_of_neg`

English:
lemma Tendsto.atTop_div_const_of_neg
  given: (hr : r < 0) (hf : Tendsto f l atTop)
  proof: (tendsto_div_const_atBot_of_neg hr).2 hf

中文:
引理 Tendsto.atTop_div_const_of_neg
  条件: (hr : r < 0) (hf : Tendsto f l atTop)
  证明: (tendsto_div_const_atBot_of_neg hr).2 hf

Depends on / 依赖: tendsto_div_const_atBot_of_neg
-/
lemma Tendsto.atTop_div_const_of_neg (hr : r < 0) (hf : Tendsto f l atTop) :
    Tendsto (fun x => f x / r) l atBot := (tendsto_div_const_atBot_of_neg hr).2 hf

/--
theorem `Tendsto.const_mul_atBot` / 定理 `Tendsto.const_mul_atBot`

English:
theorem Tendsto.const_mul_atBot
  given: (hr : 0 < r) (hf : Tendsto f l atBot)
  proof: (tendsto_const_mul_atBot_of_pos hr).2 hf

中文:
定理 Tendsto.const_mul_atBot
  条件: (hr : 0 < r) (hf : Tendsto f l atBot)
  证明: (tendsto_const_mul_atBot_of_pos hr).2 hf

Depends on / 依赖: tendsto_const_mul_atBot_of_pos
-/
theorem Tendsto.const_mul_atBot (hr : 0 < r) (hf : Tendsto f l atBot) :
    Tendsto (fun x => r * f x) l atBot :=
  (tendsto_const_mul_atBot_of_pos hr).2 hf

/--
theorem `Tendsto.atBot_mul_const` / 定理 `Tendsto.atBot_mul_const`

English:
theorem Tendsto.atBot_mul_const
  given: (hr : 0 < r) (hf : Tendsto f l atBot)
  proof: (tendsto_mul_const_atBot_of_pos hr).2 hf

中文:
定理 Tendsto.atBot_mul_const
  条件: (hr : 0 < r) (hf : Tendsto f l atBot)
  证明: (tendsto_mul_const_atBot_of_pos hr).2 hf

Depends on / 依赖: tendsto_mul_const_atBot_of_pos
-/
theorem Tendsto.atBot_mul_const (hr : 0 < r) (hf : Tendsto f l atBot) :
    Tendsto (fun x => f x * r) l atBot :=
  (tendsto_mul_const_atBot_of_pos hr).2 hf

/--
theorem `Tendsto.atBot_div_const` / 定理 `Tendsto.atBot_div_const`

English:
theorem Tendsto.atBot_div_const
  given: (hr : 0 < r) (hf : Tendsto f l atBot)
  proof: (tendsto_div_const_atBot_of_pos hr).2 hf

中文:
定理 Tendsto.atBot_div_const
  条件: (hr : 0 < r) (hf : Tendsto f l atBot)
  证明: (tendsto_div_const_atBot_of_pos hr).2 hf

Depends on / 依赖: tendsto_div_const_atBot_of_pos
-/
theorem Tendsto.atBot_div_const (hr : 0 < r) (hf : Tendsto f l atBot) :
    Tendsto (fun x => f x / r) l atBot := (tendsto_div_const_atBot_of_pos hr).2 hf

/--
theorem `Tendsto.const_mul_atBot_of_neg` / 定理 `Tendsto.const_mul_atBot_of_neg`

English:
theorem Tendsto.const_mul_atBot_of_neg
  given: (hr : r < 0) (hf : Tendsto f l atBot)
  proof: (tendsto_const_mul_atTop_of_neg hr).2 hf

中文:
定理 Tendsto.const_mul_atBot_of_neg
  条件: (hr : r < 0) (hf : Tendsto f l atBot)
  证明: (tendsto_const_mul_atTop_of_neg hr).2 hf

Depends on / 依赖: tendsto_const_mul_atTop_of_neg
-/
theorem Tendsto.const_mul_atBot_of_neg (hr : r < 0) (hf : Tendsto f l atBot) :
    Tendsto (fun x => r * f x) l atTop :=
  (tendsto_const_mul_atTop_of_neg hr).2 hf

/--
theorem `Tendsto.atBot_mul_const_of_neg` / 定理 `Tendsto.atBot_mul_const_of_neg`

English:
theorem Tendsto.atBot_mul_const_of_neg
  given: (hr : r < 0) (hf : Tendsto f l atBot)
  proof: (tendsto_mul_const_atTop_of_neg hr).2 hf

中文:
定理 Tendsto.atBot_mul_const_of_neg
  条件: (hr : r < 0) (hf : Tendsto f l atBot)
  证明: (tendsto_mul_const_atTop_of_neg hr).2 hf

Depends on / 依赖: tendsto_mul_const_atTop_of_neg
-/
theorem Tendsto.atBot_mul_const_of_neg (hr : r < 0) (hf : Tendsto f l atBot) :
    Tendsto (fun x => f x * r) l atTop :=
  (tendsto_mul_const_atTop_of_neg hr).2 hf

/--
theorem `tendsto_neg_const_mul_pow_atTop` / 定理 `tendsto_neg_const_mul_pow_atTop`

English:
theorem tendsto_neg_const_mul_pow_atTop
  given: {c : α} {n : Nat} (hn : n != 0) (hc : c < 0)
  proof: (tendsto_pow_atTop hn).const_mul_atTop_of_neg hc

中文:
定理 tendsto_neg_const_mul_pow_atTop
  条件: {c : α} {n : 自然数} (hn : n != 0) (hc : c < 0)
  证明: (tendsto_pow_atTop hn).const_mul_atTop_of_neg hc

Depends on / 依赖: const_mul_atTop_of_neg, tendsto_pow_atTop
-/
theorem tendsto_neg_const_mul_pow_atTop {c : α} {n : Nat} (hn : n != 0) (hc : c < 0) :
    Tendsto (fun x => c * x ^ n) atTop atBot :=
  (tendsto_pow_atTop hn).const_mul_atTop_of_neg hc

/--
theorem `tendsto_const_mul_pow_atBot_iff` / 定理 `tendsto_const_mul_pow_atBot_iff`

English:
theorem tendsto_const_mul_pow_atBot_iff
  given: {c : α} {n : Nat}
  proof: by
  simp only [← tendsto_neg_atTop_iff, ← neg_mul, tendsto_const_mul_pow_atTop_iff, neg_pos]

中文:
定理 tendsto_const_mul_pow_atBot_iff
  条件: {c : α} {n : 自然数}
  证明: by
  simp only [← tendsto_neg_atTop_iff, ← neg_mul, tendsto_const_mul_pow_atTop_iff, neg_pos]

Depends on / 依赖: neg_mul, neg_pos, tendsto_const_mul_pow_atTop_iff, tendsto_neg_atTop_iff
-/
theorem tendsto_const_mul_pow_atBot_iff {c : α} {n : Nat} :
    Tendsto (fun x => c * x ^ n) atTop atBot ↔ n != 0 ∧ c < 0 := by
  simp only [← tendsto_neg_atTop_iff, ← neg_mul, tendsto_const_mul_pow_atTop_iff, neg_pos]

end LinearOrderedField
end Filter
