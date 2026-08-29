/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Order.Filter.AtTopBot.Group

/-!
# Convergence to ±infinity in ordered rings
-/

public section

variable {α β : Type*}

namespace Filter

section OrderedSemiring

variable [Semiring α] [PartialOrder α] [IsOrderedRing α] {l : Filter β} {f g : β -> α}

/--
theorem `Tendsto.atTop_mul_atTop₀` / 定理 `Tendsto.atTop_mul_atTop₀`

English:
theorem Tendsto.atTop_mul_atTop₀
  given: (hf : Tendsto f l atTop) (hg : Tendsto g l atTop)
  proof: by
  refine tendsto_atTop_mono' _ ?_ hg
  filter_upwards [hg.eventually (eventually_ge_atTop 0),
    hf.eventually (eventually_ge_atTop 1)] with _ using le_mul_of_one_le_left

中文:
定理 收敛.atTop_mul_atTop₀
  条件: (hf : 收敛 f l atTop) (hg : 收敛 g l atTop)
  证明: by
  refine tendsto_atTop_mono' _ ?_ hg
  filter_upwards [hg.eventually (eventually_ge_atTop 0),
    hf.eventually (eventually_ge_atTop 1)] with _ using le_mul_of_one_le_left

Depends on / 依赖: eventually, eventually_ge_atTop, filter_upwards, hf.eventually, hg.eventually, le_mul_of_one_le_left, tendsto_atTop_mono
-/
theorem Tendsto.atTop_mul_atTop₀ (hf : Tendsto f l atTop) (hg : Tendsto g l atTop) :
    Tendsto (fun x => f x * g x) l atTop := by
  refine tendsto_atTop_mono' _ ?_ hg
  filter_upwards [hg.eventually (eventually_ge_atTop 0),
    hf.eventually (eventually_ge_atTop 1)] with _ using le_mul_of_one_le_left

/--
theorem `tendsto_mul_self_atTop` / 定理 `tendsto_mul_self_atTop`

English:
theorem tendsto_mul_self_atTop
  statement: Tendsto (fun x : α => x * x) atTop atTop
  proof: tendsto_id.atTop_mul_atTop₀ tendsto_id

中文:
定理 tendsto_mul_self_atTop
  结论: 收敛 (fun x : α => x * x) atTop atTop
  证明: tendsto_id.atTop_mul_atTop₀ tendsto_id

Depends on / 依赖: tendsto_id, tendsto_id.atTop_mul_atTop
-/
theorem tendsto_mul_self_atTop : Tendsto (fun x : α => x * x) atTop atTop :=
  tendsto_id.atTop_mul_atTop₀ tendsto_id

/--
theorem `tendsto_pow_atTop` / 定理 `tendsto_pow_atTop`

English:
theorem tendsto_pow_atTop
  given: {n : Nat} (hn : n != 0)
  statement: Tendsto (fun x : α => x ^ n) atTop atTop
  proof: tendsto_atTop_mono' _ ((eventually_ge_atTop 1).mono fun _x hx => le_self_pow₀ hx hn) tendsto_id

中文:
定理 tendsto_pow_atTop
  条件: {n : 自然数} (hn : n != 0)
  结论: 收敛 (fun x : α => x ^ n) atTop atTop
  证明: tendsto_atTop_mono' _ ((eventually_ge_atTop 1).mono fun _x hx => le_self_pow₀ hx hn) tendsto_id

Depends on / 依赖: eventually_ge_atTop, tendsto_atTop_mono, tendsto_id
-/
theorem tendsto_pow_atTop {n : Nat} (hn : n != 0) : Tendsto (fun x : α => x ^ n) atTop atTop :=
  tendsto_atTop_mono' _ ((eventually_ge_atTop 1).mono fun _x hx => le_self_pow₀ hx hn) tendsto_id

end OrderedSemiring

/--
theorem `zero_pow_eventuallyEq` / 定理 `zero_pow_eventuallyEq`

English:
theorem zero_pow_eventuallyEq
  given: [MonoidWithZero α]
  proof: eventually_atTop.2 ⟨1, fun _n hn => zero_pow Nat.one_le_iff_ne_zero.1 hn⟩

中文:
定理 zero_pow_eventuallyEq
  条件: [带零幺半群 α]
  证明: eventually_atTop.2 ⟨1, fun _n hn => zero_pow Nat.one_le_iff_ne_zero.1 hn⟩

Depends on / 依赖: Nat.one_le_iff_ne_zero, eventually_atTop, one_le_iff_ne_zero, zero_pow
-/
theorem zero_pow_eventuallyEq [MonoidWithZero α] :
    (fun n : Nat => (0 : α) ^ n) =ᶠ[atTop] fun _ => 0 :=
eventually_atTop.2 ⟨1, fun _n hn => zero_pow Nat.one_le_iff_ne_zero.1 hn⟩

section OrderedRing

variable [Ring α] [PartialOrder α] [IsOrderedRing α] {l : Filter β} {f g : β -> α}

/--
theorem `Tendsto.atTop_mul_atBot₀` / 定理 `Tendsto.atTop_mul_atBot₀`

English:
theorem Tendsto.atTop_mul_atBot₀
  given: (hf : Tendsto f l atTop) (hg : Tendsto g l atBot)
  proof: by
have := hf.atTop_mul_atTop₀ tendsto_neg_atBot_atTop.comp hg
  simpa only [Function.comp_def, neg_mul_eq_mul_neg, neg_neg] using
    tendsto_neg_atTop_atBot.comp this

中文:
定理 收敛.atTop_mul_atBot₀
  条件: (hf : 收敛 f l atTop) (hg : 收敛 g l atBot)
  证明: by
have := hf.atTop_mul_atTop₀ tendsto_neg_atBot_atTop.comp hg
  simpa only [Function.comp_def, neg_mul_eq_mul_neg, neg_neg] using
    tendsto_neg_atTop_atBot.comp this

Depends on / 依赖: Function, Function.comp_def, comp_def, hf.atTop_mul_atTop, neg_mul_eq_mul_neg, neg_neg, tendsto_neg_atBot_atTop, tendsto_neg_atBot_atTop.comp, tendsto_neg_atTop_atBot, tendsto_neg_atTop_atBot.comp
-/
theorem Tendsto.atTop_mul_atBot₀ (hf : Tendsto f l atTop) (hg : Tendsto g l atBot) :
    Tendsto (fun x => f x * g x) l atBot := by
have := hf.atTop_mul_atTop₀ tendsto_neg_atBot_atTop.comp hg
  simpa only [Function.comp_def, neg_mul_eq_mul_neg, neg_neg] using
    tendsto_neg_atTop_atBot.comp this

/--
theorem `Tendsto.atBot_mul_atTop₀` / 定理 `Tendsto.atBot_mul_atTop₀`

English:
theorem Tendsto.atBot_mul_atTop₀
  given: (hf : Tendsto f l atBot) (hg : Tendsto g l atTop)
  proof: by
  have : Tendsto (fun x => -f x * g x) l atTop :=
    (tendsto_neg_atBot_atTop.comp hf).atTop_mul_atTop₀ hg
  simpa only [Function.comp_def, neg_mul_eq_neg_mul, neg_neg] using
    tendsto_neg_atTop_atBot.comp this

中文:
定理 收敛.atBot_mul_atTop₀
  条件: (hf : 收敛 f l atBot) (hg : 收敛 g l atTop)
  证明: by
  have : Tendsto (fun x => -f x * g x) l atTop :=
    (tendsto_neg_atBot_atTop.comp hf).atTop_mul_atTop₀ hg
  simpa only [Function.comp_def, neg_mul_eq_neg_mul, neg_neg] using
    tendsto_neg_atTop_atBot.comp this

Depends on / 依赖: Function, Function.comp_def, Tendsto, comp_def, neg_mul_eq_neg_mul, neg_neg, tendsto_neg_atBot_atTop, tendsto_neg_atBot_atTop.comp, tendsto_neg_atTop_atBot, tendsto_neg_atTop_atBot.comp
-/
theorem Tendsto.atBot_mul_atTop₀ (hf : Tendsto f l atBot) (hg : Tendsto g l atTop) :
    Tendsto (fun x => f x * g x) l atBot := by
  have : Tendsto (fun x => -f x * g x) l atTop :=
    (tendsto_neg_atBot_atTop.comp hf).atTop_mul_atTop₀ hg
  simpa only [Function.comp_def, neg_mul_eq_neg_mul, neg_neg] using
    tendsto_neg_atTop_atBot.comp this

/--
theorem `Tendsto.atBot_mul_atBot₀` / 定理 `Tendsto.atBot_mul_atBot₀`

English:
theorem Tendsto.atBot_mul_atBot₀
  given: (hf : Tendsto f l atBot) (hg : Tendsto g l atBot)
  proof: by
  have : Tendsto (fun x => -f x * -g x) l atTop :=
    (tendsto_neg_atBot_atTop.comp hf).atTop_mul_atTop₀ (tendsto_neg_atBot_atTop.comp hg)
  simpa only [neg_mul_neg] using this

中文:
定理 收敛.atBot_mul_atBot₀
  条件: (hf : 收敛 f l atBot) (hg : 收敛 g l atBot)
  证明: by
  have : Tendsto (fun x => -f x * -g x) l atTop :=
    (tendsto_neg_atBot_atTop.comp hf).atTop_mul_atTop₀ (tendsto_neg_atBot_atTop.comp hg)
  simpa only [neg_mul_neg] using this

Depends on / 依赖: Tendsto, neg_mul_neg, tendsto_neg_atBot_atTop, tendsto_neg_atBot_atTop.comp
-/
theorem Tendsto.atBot_mul_atBot₀ (hf : Tendsto f l atBot) (hg : Tendsto g l atBot) :
    Tendsto (fun x => f x * g x) l atTop := by
  have : Tendsto (fun x => -f x * -g x) l atTop :=
    (tendsto_neg_atBot_atTop.comp hf).atTop_mul_atTop₀ (tendsto_neg_atBot_atTop.comp hg)
  simpa only [neg_mul_neg] using this

end OrderedRing

section LinearOrderedSemiring

variable [Semiring α] [LinearOrder α] [IsStrictOrderedRing α] {l : Filter β} {f : β -> α}

/--
theorem `Tendsto.atTop_of_const_mul₀` / 定理 `Tendsto.atTop_of_const_mul₀`

English:
theorem Tendsto.atTop_of_const_mul₀
  given: {c : α} (hc : 0 < c) (hf : Tendsto (fun x => c * f x) l atTop)
  proof: tendsto_atTop.2 fun b => (tendsto_atTop.1 hf (c * b)).mono
    fun _x hx => le_of_mul_le_mul_left hx hc

中文:
定理 收敛.atTop_of_const_mul₀
  条件: {c : α} (hc : 0 < c) (hf : 收敛 (fun x => c * f x) l atTop)
  证明: tendsto_atTop.2 fun b => (tendsto_atTop.1 hf (c * b)).mono
    fun _x hx => le_of_mul_le_mul_left hx hc

Depends on / 依赖: le_of_mul_le_mul_left, tendsto_atTop
-/
theorem Tendsto.atTop_of_const_mul₀ {c : α} (hc : 0 < c) (hf : Tendsto (fun x => c * f x) l atTop) :
    Tendsto f l atTop :=
  tendsto_atTop.2 fun b => (tendsto_atTop.1 hf (c * b)).mono
    fun _x hx => le_of_mul_le_mul_left hx hc

/--
theorem `Tendsto.atTop_of_mul_const₀` / 定理 `Tendsto.atTop_of_mul_const₀`

English:
theorem Tendsto.atTop_of_mul_const₀
  given: {c : α} (hc : 0 < c) (hf : Tendsto (fun x => f x * c) l atTop)
  proof: tendsto_atTop.2 fun b => (tendsto_atTop.1 hf (b * c)).mono
    fun _x hx => le_of_mul_le_mul_right hx hc

@[simp]

中文:
定理 收敛.atTop_of_mul_const₀
  条件: {c : α} (hc : 0 < c) (hf : 收敛 (fun x => f x * c) l atTop)
  证明: tendsto_atTop.2 fun b => (tendsto_atTop.1 hf (b * c)).mono
    fun _x hx => le_of_mul_le_mul_right hx hc

@[simp]

Depends on / 依赖: le_of_mul_le_mul_right, tendsto_atTop
-/
theorem Tendsto.atTop_of_mul_const₀ {c : α} (hc : 0 < c) (hf : Tendsto (fun x => f x * c) l atTop) :
    Tendsto f l atTop :=
  tendsto_atTop.2 fun b => (tendsto_atTop.1 hf (b * c)).mono
    fun _x hx => le_of_mul_le_mul_right hx hc

@[simp]
/--
theorem `tendsto_pow_atTop_iff` / 定理 `tendsto_pow_atTop_iff`

English:
theorem tendsto_pow_atTop_iff
  given: {n : Nat}
  statement: Tendsto (fun x : α => x ^ n) atTop atTop ↔ n != 0
  proof: ⟨fun h hn => by simp only [hn, pow_zero, not_tendsto_const_atTop] at h, tendsto_pow_atTop⟩

中文:
定理 tendsto_pow_atTop_iff
  条件: {n : 自然数}
  结论: 收敛 (fun x : α => x ^ n) atTop atTop ↔ n != 0
  证明: ⟨fun h hn => by simp only [hn, pow_zero, not_tendsto_const_atTop] at h, tendsto_pow_atTop⟩

Depends on / 依赖: not_tendsto_const_atTop, pow_zero, tendsto_pow_atTop
-/
theorem tendsto_pow_atTop_iff {n : Nat} : Tendsto (fun x : α => x ^ n) atTop atTop ↔ n != 0 :=
  ⟨fun h hn => by simp only [hn, pow_zero, not_tendsto_const_atTop] at h, tendsto_pow_atTop⟩

end LinearOrderedSemiring

/--
theorem `not_tendsto_pow_atTop_atBot` / 定理 `not_tendsto_pow_atTop_atBot`

English:
theorem not_tendsto_pow_atTop_atBot
  given: [Ring α] [LinearOrder α] [IsStrictOrderedRing α]

中文:
定理 not_tendsto_pow_atTop_atBot
  条件: [环 α] [线性序 α] [是StrictOrdered环 α]
-/
theorem not_tendsto_pow_atTop_atBot [Ring α] [LinearOrder α] [IsStrictOrderedRing α] :
    forall {n : Nat}, ¬Tendsto (fun x : α => x ^ n) atTop atBot
  | 0 => by simp [not_tendsto_const_atBot]
  | n + 1 => (tendsto_pow_atTop n.succ_ne_zero).not_tendsto disjoint_atTop_atBot

end Filter

open Filter

variable {R : Type*} [Semiring R] [LinearOrder R] [IsStrictOrderedRing R]

/--
theorem `exists_lt_mul_self` / 定理 `exists_lt_mul_self`

English:
theorem exists_lt_mul_self
  given: (a : R)
  statement: exists x >= 0, a < x * x
  proof: ((eventually_ge_atTop 0).and (tendsto_mul_self_atTop.eventually (eventually_gt_atTop a))).exists

中文:
定理 存在_lt_mul_self
  条件: (a : R)
  结论: 存在 x >= 0, a < x * x
  证明: ((eventually_ge_atTop 0).and (tendsto_mul_self_atTop.eventually (eventually_gt_atTop a))).exists

Depends on / 依赖: eventually, eventually_ge_atTop, eventually_gt_atTop, tendsto_mul_self_atTop, tendsto_mul_self_atTop.eventually
-/
theorem exists_lt_mul_self (a : R) : exists x >= 0, a < x * x :=
  ((eventually_ge_atTop 0).and (tendsto_mul_self_atTop.eventually (eventually_gt_atTop a))).exists

/--
theorem `exists_le_mul_self` / 定理 `exists_le_mul_self`

English:
theorem exists_le_mul_self
  given: (a : R)
  statement: exists x >= 0, a <= x * x
  proof: let ⟨x, hx0, hxa⟩ := exists_lt_mul_self a
  ⟨x, hx0, hxa.le⟩

中文:
定理 存在_le_mul_self
  条件: (a : R)
  结论: 存在 x >= 0, a <= x * x
  证明: let ⟨x, hx0, hxa⟩ := exists_lt_mul_self a
  ⟨x, hx0, hxa.le⟩

Depends on / 依赖: exists_lt_mul_self, hxa.le
-/
theorem exists_le_mul_self (a : R) : exists x >= 0, a <= x * x :=
  let ⟨x, hx0, hxa⟩ := exists_lt_mul_self a
  ⟨x, hx0, hxa.le⟩
