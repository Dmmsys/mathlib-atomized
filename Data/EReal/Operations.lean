/-
Copyright (c) 2019 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.Data.EReal.Basic
public import Batteries.Util.ProofWanted

/-!
# Addition, negation, subtraction and multiplication on extended real numbers

Addition and multiplication in `EReal` are problematic in the presence of `±∞`, but negation has
a natural definition and satisfies the usual properties. In particular, it is an order-reversing
isomorphism.

The construction of `EReal` as `WithBot (WithTop ℝ)` endows a `LinearOrderedAddCommMonoid` structure
on it. However, addition is badly behaved at `(⊥, ⊤)` and `(⊤, ⊥)`, so this cannot be upgraded to a
group structure. Our choice is that `⊥ + ⊤ = ⊤ + ⊥ = ⊥`, to make sure that the exponential and
logarithm between `EReal` and `ℝ≥0∞` respect the operations. Note that the convention `0 * ∞ = 0`
on `ℝ≥0∞` is enforced by measure theory. Subtraction, defined as `x - y = x + (-y)`, does not have
nice properties but is sometimes convenient to have.

There is also a `CommMonoidWithZero` structure on `EReal`, but `Mathlib/Data/EReal/Basic.lean` only
provides `MulZeroOneClass` because a proof of associativity by hand would have 125 cases.
The `CommMonoidWithZero` instance is instead delivered in `Mathlib/Data/EReal/Inv.lean`.

We define `0 * x = x * 0 = 0` for any `x`, with the other cases defined non-ambiguously.
This does not distribute with addition, as `⊥ = ⊥ + ⊤ = 1 * ⊥ + (-1) * ⊥ ≠ (1 - 1) * ⊥ = 0 * ⊥ = 0`.
Distributivity `x * (y + z) = x * y + x * z` is recovered in the case where either `0 ≤ x < ⊤`,
see `EReal.left_distrib_of_nonneg_of_ne_top`, or `0 ≤ y, z`. See `EReal.left_distrib_of_nonneg`
(similarly for right distributivity).
-/

@[expose] public section

open ENNReal NNReal

noncomputable section

namespace EReal

/-! ### Addition -/

@[simp]
/--
theorem `add_bot` / 定理 `add_bot`

English:
theorem add_bot
  given: (x : EReal)
  statement: x + ⊥ = ⊥
  proof: WithBot.add_bot _

@[simp]

中文:
定理 add_bot
  条件: (x : E实数)
  结论: x + ⊥ = ⊥
  证明: WithBot.add_bot _

@[simp]

Depends on / 依赖: WithBot, WithBot.add_bot, add_bot
-/
theorem add_bot (x : EReal) : x + ⊥ = ⊥ :=
  WithBot.add_bot _

@[simp]
/--
theorem `bot_add` / 定理 `bot_add`

English:
theorem bot_add
  given: (x : EReal)
  statement: ⊥ + x = ⊥
  proof: WithBot.bot_add _

@[simp]

中文:
定理 bot_add
  条件: (x : E实数)
  结论: ⊥ + x = ⊥
  证明: WithBot.bot_add _

@[simp]

Depends on / 依赖: WithBot, WithBot.bot_add, bot_add
-/
theorem bot_add (x : EReal) : ⊥ + x = ⊥ :=
  WithBot.bot_add _

@[simp]
/--
theorem `add_eq_bot_iff` / 定理 `add_eq_bot_iff`

English:
theorem add_eq_bot_iff
  given: {x y : EReal}
  statement: x + y = ⊥ ↔ x = ⊥ ∨ y = ⊥
  proof: WithBot.add_eq_bot

中文:
定理 add_eq_bot_iff
  条件: {x y : E实数}
  结论: x + y = ⊥ ↔ x = ⊥ ∨ y = ⊥
  证明: WithBot.add_eq_bot

Depends on / 依赖: WithBot, WithBot.add_eq_bot, add_eq_bot
-/
theorem add_eq_bot_iff {x y : EReal} : x + y = ⊥ ↔ x = ⊥ ∨ y = ⊥ :=
  WithBot.add_eq_bot

/--
lemma `add_ne_bot_iff` / 引理 `add_ne_bot_iff`

English:
lemma add_ne_bot_iff
  given: {x y : EReal}
  statement: x + y != ⊥ ↔ x != ⊥ ∧ y != ⊥
  proof: WithBot.add_ne_bot

@[simp]

中文:
引理 add_ne_bot_iff
  条件: {x y : E实数}
  结论: x + y != ⊥ ↔ x != ⊥ ∧ y != ⊥
  证明: WithBot.add_ne_bot

@[simp]

Depends on / 依赖: WithBot, WithBot.add_ne_bot, add_ne_bot
-/
lemma add_ne_bot_iff {x y : EReal} : x + y != ⊥ ↔ x != ⊥ ∧ y != ⊥ := WithBot.add_ne_bot

@[simp]
/--
theorem `bot_lt_add_iff` / 定理 `bot_lt_add_iff`

English:
theorem bot_lt_add_iff
  given: {x y : EReal}
  statement: ⊥ < x + y ↔ ⊥ < x ∧ ⊥ < y
  proof: by
  simp [bot_lt_iff_ne_bot]

@[simp]

中文:
定理 bot_lt_add_iff
  条件: {x y : E实数}
  结论: ⊥ < x + y ↔ ⊥ < x ∧ ⊥ < y
  证明: by
  simp [bot_lt_iff_ne_bot]

@[simp]

Depends on / 依赖: bot_lt_iff_ne_bot
-/
theorem bot_lt_add_iff {x y : EReal} : ⊥ < x + y ↔ ⊥ < x ∧ ⊥ < y := by
  simp [bot_lt_iff_ne_bot]

@[simp]
/--
theorem `top_add_top` / 定理 `top_add_top`

English:
theorem top_add_top
  statement: (⊤ : EReal) + ⊤ = ⊤
  proof: rfl

@[simp]

中文:
定理 top_add_top
  结论: (⊤ : E实数) + ⊤ = ⊤
  证明: rfl

@[simp]
-/
theorem top_add_top : (⊤ : EReal) + ⊤ = ⊤ :=
  rfl

@[simp]
/--
theorem `top_add_coe` / 定理 `top_add_coe`

English:
theorem top_add_coe
  given: (x : Real)
  statement: (⊤ : EReal) + x = ⊤
  proof: rfl

中文:
定理 top_add_coe
  条件: (x : 实数)
  结论: (⊤ : E实数) + x = ⊤
  证明: rfl
-/
theorem top_add_coe (x : Real) : (⊤ : EReal) + x = ⊤ :=
  rfl

/-- For any extended real number `x` which is not `⊥`, the sum of `⊤` and `x` is equal to `⊤`. -/
@[simp]
/--
theorem `top_add_of_ne_bot` / 定理 `top_add_of_ne_bot`

English:
theorem top_add_of_ne_bot
  given: {x : EReal} (h : x != ⊥)
  statement: ⊤ + x = ⊤
  proof: by
  induction x
  · exfalso; exact h (Eq.refl ⊥)
  · exact top_add_coe _
  · exact top_add_top

中文:
定理 top_add_of_ne_bot
  条件: {x : E实数} (h : x != ⊥)
  结论: ⊤ + x = ⊤
  证明: by
  induction x
  · exfalso; exact h (Eq.refl ⊥)
  · exact top_add_coe _
  · exact top_add_top

Depends on / 依赖: Eq.refl, top_add_coe, top_add_top
-/
theorem top_add_of_ne_bot {x : EReal} (h : x != ⊥) : ⊤ + x = ⊤ := by
  induction x
  · exfalso; exact h (Eq.refl ⊥)
  · exact top_add_coe _
  · exact top_add_top

/--
theorem `top_add_iff_ne_bot` / 定理 `top_add_iff_ne_bot`

English:
theorem top_add_iff_ne_bot
  given: {x : EReal}
  statement: ⊤ + x = ⊤ ↔ x != ⊥
  proof: by
  constructor <;> intro h
  · rintro rfl
    rw [add_bot] at h
    exact bot_ne_top h
  · cases x with
    | bot => contradiction
    | top => rfl
    | coe r => exact top_add_of_ne_bot h

中文:
定理 top_add_iff_ne_bot
  条件: {x : E实数}
  结论: ⊤ + x = ⊤ ↔ x != ⊥
  证明: by
  constructor <;> intro h
  · rintro rfl
    rw [add_bot] at h
    exact bot_ne_top h
  · cases x with
    | bot => contradiction
    | top => rfl
    | coe r => exact top_add_of_ne_bot h

Depends on / 依赖: add_bot, bot_ne_top, top_add_of_ne_bot
-/
theorem top_add_iff_ne_bot {x : EReal} : ⊤ + x = ⊤ ↔ x != ⊥ := by
  constructor <;> intro h
  · rintro rfl
    rw [add_bot] at h
    exact bot_ne_top h
  · cases x with
    | bot => contradiction
    | top => rfl
    | coe r => exact top_add_of_ne_bot h

/-- For any extended real number `x` which is not `⊥`, the sum of `x` and `⊤` is equal to `⊤`. -/
@[simp]
/--
theorem `add_top_of_ne_bot` / 定理 `add_top_of_ne_bot`

English:
theorem add_top_of_ne_bot
  given: {x : EReal} (h : x != ⊥)
  statement: x + ⊤ = ⊤
  proof: by
  rw [add_comm]; rw [top_add_of_ne_bot h]

中文:
定理 add_top_of_ne_bot
  条件: {x : E实数} (h : x != ⊥)
  结论: x + ⊤ = ⊤
  证明: by
  rw [add_comm]; rw [top_add_of_ne_bot h]

Depends on / 依赖: add_comm, top_add_of_ne_bot
-/
theorem add_top_of_ne_bot {x : EReal} (h : x != ⊥) : x + ⊤ = ⊤ := by
  rw [add_comm]; rw [top_add_of_ne_bot h]

/--
theorem `add_top_iff_ne_bot` / 定理 `add_top_iff_ne_bot`

English:
theorem add_top_iff_ne_bot
  given: {x : EReal}
  statement: x + ⊤ = ⊤ ↔ x != ⊥
  proof: by rw [add_comm, top_add_iff_ne_bot]

中文:
定理 add_top_iff_ne_bot
  条件: {x : E实数}
  结论: x + ⊤ = ⊤ ↔ x != ⊥
  证明: by rw [add_comm, top_add_iff_ne_bot]

Depends on / 依赖: add_comm, top_add_iff_ne_bot
-/
theorem add_top_iff_ne_bot {x : EReal} : x + ⊤ = ⊤ ↔ x != ⊥ := by rw [add_comm, top_add_iff_ne_bot]

/--
theorem `add_pos_of_pos_of_nonneg` / 定理 `add_pos_of_pos_of_nonneg`

English:
theorem add_pos_of_pos_of_nonneg
  given: {a b : EReal} (ha : 0 < a) (hb : 0 <= b)
  statement: 0 < a + b
  proof: add_comm a b ▸ Right.add_pos_of_nonneg_of_pos hb ha

中文:
定理 add_pos_of_pos_of_nonneg
  条件: {a b : E实数} (ha : 0 < a) (hb : 0 <= b)
  结论: 0 < a + b
  证明: add_comm a b ▸ Right.add_pos_of_nonneg_of_pos hb ha
-/
protected theorem add_pos_of_pos_of_nonneg {a b : EReal} (ha : 0 < a) (hb : 0 <= b) : 0 < a + b :=
  add_comm a b ▸ Right.add_pos_of_nonneg_of_pos hb ha

/--
theorem `add_pos` / 定理 `add_pos`

English:
theorem add_pos
  given: {a b : EReal} (ha : 0 < a) (hb : 0 < b)
  statement: 0 < a + b
  proof: Right.add_pos_of_nonneg_of_pos ha.le hb

@[simp]

中文:
定理 add_pos
  条件: {a b : E实数} (ha : 0 < a) (hb : 0 < b)
  结论: 0 < a + b
  证明: Right.add_pos_of_nonneg_of_pos ha.le hb

@[simp]
-/
protected theorem add_pos {a b : EReal} (ha : 0 < a) (hb : 0 < b) : 0 < a + b :=
  Right.add_pos_of_nonneg_of_pos ha.le hb

@[simp]
/--
theorem `coe_add_top` / 定理 `coe_add_top`

English:
theorem coe_add_top
  given: (x : Real)
  statement: (x : EReal) + ⊤ = ⊤
  proof: rfl

中文:
定理 coe_add_top
  条件: (x : 实数)
  结论: (x : E实数) + ⊤ = ⊤
  证明: rfl
-/
theorem coe_add_top (x : Real) : (x : EReal) + ⊤ = ⊤ :=
  rfl

/--
theorem `toReal_add` / 定理 `toReal_add`

English:
theorem toReal_add
  given: {x y : EReal} (hx : x != ⊤) (h'x : x != ⊥) (hy : y != ⊤) (h'y : y != ⊥)
  proof: by
  lift x to Real using ⟨hx, h'x⟩
  lift y to Real using ⟨hy, h'y⟩
  rfl

中文:
定理 to实数_add
  条件: {x y : E实数} (hx : x != ⊤) (h'x : x != ⊥) (hy : y != ⊤) (h'y : y != ⊥)
  证明: by
  lift x to Real using ⟨hx, h'x⟩
  lift y to Real using ⟨hy, h'y⟩
  rfl
-/
theorem toReal_add {x y : EReal} (hx : x != ⊤) (h'x : x != ⊥) (hy : y != ⊤) (h'y : y != ⊥) :
    toReal (x + y) = toReal x + toReal y := by
  lift x to Real using ⟨hx, h'x⟩
  lift y to Real using ⟨hy, h'y⟩
  rfl

/--
lemma `toENNReal_add` / 引理 `toENNReal_add`

English:
lemma toENNReal_add
  given: {x y : EReal} (hx : 0 <= x) (hy : 0 <= y)
  proof: by
  induction x <;> induction y <;> try {· simp_all}
  norm_cast
  simp_rw [real_coe_toENNReal]
  simp_all [ENNReal.ofReal_add]

中文:
引理 toENN实数_add
  条件: {x y : E实数} (hx : 0 <= x) (hy : 0 <= y)
  证明: by
  induction x <;> induction y <;> try {· simp_all}
  norm_cast
  simp_rw [real_coe_toENNReal]
  simp_all [ENNReal.ofReal_add]

Depends on / 依赖: ENNReal, ENNReal.ofReal_add, ofReal_add, real_coe_toENNReal, simp_rw
-/
lemma toENNReal_add {x y : EReal} (hx : 0 <= x) (hy : 0 <= y) :
    (x + y).toENNReal = x.toENNReal + y.toENNReal := by
  induction x <;> induction y <;> try {· simp_all}
  norm_cast
  simp_rw [real_coe_toENNReal]
  simp_all [ENNReal.ofReal_add]

/--
lemma `toENNReal_add_le` / 引理 `toENNReal_add_le`

English:
lemma toENNReal_add_le
  given: {x y : EReal}
  statement: (x + y).toENNReal <= x.toENNReal + y.toENNReal
  proof: by
  induction x <;> induction y <;> try {· simp}
  exact ENNReal.ofReal_add_le

中文:
引理 toENN实数_add_le
  条件: {x y : E实数}
  结论: (x + y).toENN实数 <= x.toENN实数 + y.toENN实数
  证明: by
  induction x <;> induction y <;> try {· simp}
  exact ENNReal.ofReal_add_le

Depends on / 依赖: ENNReal, ENNReal.ofReal_add_le, ofReal_add_le
-/
lemma toENNReal_add_le {x y : EReal} : (x + y).toENNReal <= x.toENNReal + y.toENNReal := by
  induction x <;> induction y <;> try {· simp}
  exact ENNReal.ofReal_add_le

/--
theorem `addLECancellable_coe` / 定理 `addLECancellable_coe`

English:
theorem addLECancellable_coe
  given: (x : Real)
  statement: AddLECancellable (x : EReal)

中文:
定理 addLECancellable_coe
  条件: (x : 实数)
  结论: AddLECancellable (x : E实数)
-/
theorem addLECancellable_coe (x : Real) : AddLECancellable (x : EReal)
  | _, ⊤, _ => le_top
  | ⊥, _, _ => bot_le
  | ⊤, (z : Real), h => by simp only [coe_add_top, ← coe_add, top_le_iff, coe_ne_top] at h
  | _, ⊥, h => by simpa using h
  | (y : Real), (z : Real), h => by
    simpa only [← coe_add, EReal.coe_le_coe_iff, add_le_add_iff_left] using h

-- TODO: add `MulLECancellable.strictMono*` etc
/--
theorem `add_lt_add_right_coe` / 定理 `add_lt_add_right_coe`

English:
theorem add_lt_add_right_coe
  given: {x y : EReal} (h : x < y) (z : Real)
  statement: x + z < y + z
  proof: not_le.1 mt (addLECancellable_coe z).add_le_add_iff_right.1 h.not_ge

中文:
定理 add_lt_add_right_coe
  条件: {x y : E实数} (h : x < y) (z : 实数)
  结论: x + z < y + z
  证明: not_le.1 mt (addLECancellable_coe z).add_le_add_iff_right.1 h.not_ge

Depends on / 依赖: addLECancellable_coe, add_le_add_iff_right, h.not_ge, not_ge, not_le
-/
theorem add_lt_add_right_coe {x y : EReal} (h : x < y) (z : Real) : x + z < y + z :=
not_le.1 mt (addLECancellable_coe z).add_le_add_iff_right.1 h.not_ge

/--
theorem `add_lt_add_left_coe` / 定理 `add_lt_add_left_coe`

English:
theorem add_lt_add_left_coe
  given: {x y : EReal} (h : x < y) (z : Real)
  statement: (z : EReal) + x < z + y
  proof: by
  simpa [add_comm] using add_lt_add_right_coe h z

中文:
定理 add_lt_add_left_coe
  条件: {x y : E实数} (h : x < y) (z : 实数)
  结论: (z : E实数) + x < z + y
  证明: by
  simpa [add_comm] using add_lt_add_right_coe h z

Depends on / 依赖: add_comm, add_lt_add_right_coe
-/
theorem add_lt_add_left_coe {x y : EReal} (h : x < y) (z : Real) : (z : EReal) + x < z + y := by
  simpa [add_comm] using add_lt_add_right_coe h z

/--
theorem `add_lt_add` / 定理 `add_lt_add`

English:
theorem add_lt_add
  given: {x y z t : EReal} (h1 : x < y) (h2 : z < t)
  statement: x + z < y + t
  proof: by
  rcases eq_or_ne x ⊥ with (rfl | hx)
  · simp [h1, bot_le.trans_lt h2]
  · lift x to Real using ⟨h1.ne_top, hx⟩
    calc (x : EReal) + z < x + t := add_lt_add_left_coe h2 _
    _ <= y + t := by gcongr

中文:
定理 add_lt_add
  条件: {x y z t : E实数} (h1 : x < y) (h2 : z < t)
  结论: x + z < y + t
  证明: by
  rcases eq_or_ne x ⊥ with (rfl | hx)
  · simp [h1, bot_le.trans_lt h2]
  · lift x to Real using ⟨h1.ne_top, hx⟩
    calc (x : EReal) + z < x + t := add_lt_add_left_coe h2 _
    _ <= y + t := by gcongr

Depends on / 依赖: add_lt_add_left_coe, bot_le, bot_le.trans_lt, eq_or_ne, h1.ne_top, ne_top, trans_lt
-/
theorem add_lt_add {x y z t : EReal} (h1 : x < y) (h2 : z < t) : x + z < y + t := by
  rcases eq_or_ne x ⊥ with (rfl | hx)
  · simp [h1, bot_le.trans_lt h2]
  · lift x to Real using ⟨h1.ne_top, hx⟩
    calc (x : EReal) + z < x + t := add_lt_add_left_coe h2 _
    _ <= y + t := by gcongr

/--
theorem `add_lt_add_of_lt_of_le'` / 定理 `add_lt_add_of_lt_of_le'`

English:
theorem add_lt_add_of_lt_of_le'
  statement: {x y z t : EReal} (h : x < y) (h' : z <= t) (hbot : t != ⊥)
  proof: by
  rcases h'.eq_or_lt with (rfl | hlt)
  · rcases eq_or_ne z ⊤ with (rfl | hz)
    · obtain rfl := htop rfl rfl
      simpa
    lift z to Real using ⟨hz, hbot⟩
    exact add_lt_add_right_coe h z
  · exact add_lt_add h hlt

中文:
定理 add_lt_add_of_lt_of_le'
  结论: {x y z t : E实数} (h : x < y) (h' : z <= t) (hbot : t != ⊥)
  证明: by
  rcases h'.eq_or_lt with (rfl | hlt)
  · rcases eq_or_ne z ⊤ with (rfl | hz)
    · obtain rfl := htop rfl rfl
      simpa
    lift z to Real using ⟨hz, hbot⟩
    exact add_lt_add_right_coe h z
  · exact add_lt_add h hlt

Depends on / 依赖: add_lt_add, add_lt_add_right_coe, eq_or_lt, eq_or_ne
-/
theorem add_lt_add_of_lt_of_le' {x y z t : EReal} (h : x < y) (h' : z <= t) (hbot : t != ⊥)
    (htop : t = ⊤ -> z = ⊤ -> x = ⊥) : x + z < y + t := by
  rcases h'.eq_or_lt with (rfl | hlt)
  · rcases eq_or_ne z ⊤ with (rfl | hz)
    · obtain rfl := htop rfl rfl
      simpa
    lift z to Real using ⟨hz, hbot⟩
    exact add_lt_add_right_coe h z
  · exact add_lt_add h hlt

/--
theorem `add_lt_add_of_lt_of_le` / 定理 `add_lt_add_of_lt_of_le`

English:
theorem add_lt_add_of_lt_of_le
  statement: {x y z t : EReal} (h : x < y) (h' : z <= t) (hz : z != ⊥)
  proof: add_lt_add_of_lt_of_le' h h' (ne_bot_of_le_ne_bot hz h') fun ht' => (ht ht').elim

中文:
定理 add_lt_add_of_lt_of_le
  结论: {x y z t : E实数} (h : x < y) (h' : z <= t) (hz : z != ⊥)
  证明: add_lt_add_of_lt_of_le' h h' (ne_bot_of_le_ne_bot hz h') fun ht' => (ht ht').elim

Depends on / 依赖: add_lt_add_of_lt_of_le, ne_bot_of_le_ne_bot
-/
theorem add_lt_add_of_lt_of_le {x y z t : EReal} (h : x < y) (h' : z <= t) (hz : z != ⊥)
    (ht : t != ⊤) : x + z < y + t :=
  add_lt_add_of_lt_of_le' h h' (ne_bot_of_le_ne_bot hz h') fun ht' => (ht ht').elim

/--
theorem `add_lt_top` / 定理 `add_lt_top`

English:
theorem add_lt_top
  given: {x y : EReal} (hx : x != ⊤) (hy : y != ⊤)
  statement: x + y < ⊤
  proof: add_lt_add hx.lt_top hy.lt_top

中文:
定理 add_lt_top
  条件: {x y : E实数} (hx : x != ⊤) (hy : y != ⊤)
  结论: x + y < ⊤
  证明: add_lt_add hx.lt_top hy.lt_top

Depends on / 依赖: add_lt_add, hx.lt_top, hy.lt_top, lt_top
-/
theorem add_lt_top {x y : EReal} (hx : x != ⊤) (hy : y != ⊤) : x + y < ⊤ :=
  add_lt_add hx.lt_top hy.lt_top

/--
lemma `add_ne_top` / 引理 `add_ne_top`

English:
lemma add_ne_top
  given: {x y : EReal} (hx : x != ⊤) (hy : y != ⊤)
  statement: x + y != ⊤
  proof: lt_top_iff_ne_top.mp add_lt_top hx hy

中文:
引理 add_ne_top
  条件: {x y : E实数} (hx : x != ⊤) (hy : y != ⊤)
  结论: x + y != ⊤
  证明: lt_top_iff_ne_top.mp add_lt_top hx hy

Depends on / 依赖: add_lt_top, lt_top_iff_ne_top, lt_top_iff_ne_top.mp
-/
lemma add_ne_top {x y : EReal} (hx : x != ⊤) (hy : y != ⊤) : x + y != ⊤ :=
lt_top_iff_ne_top.mp add_lt_top hx hy

/--
lemma `add_ne_top_iff_ne_top₂` / 引理 `add_ne_top_iff_ne_top₂`

English:
lemma add_ne_top_iff_ne_top₂
  given: {x y : EReal} (hx : x != ⊥) (hy : y != ⊥)
  proof: by
  refine ⟨?_, fun h => add_ne_top h.1 h.2⟩
  cases x <;> simp_all only [ne_eq, not_false_eq_true, top_add_of_ne_bot, not_true_eq_false,
    IsEmpty.forall_iff]
  cases y <;> simp_all only [not_false_eq_true, ne_eq, add_top_of_ne_bot, not_true_eq_false,
    coe_ne_top, and_self, implies_true]

中文:
引理 add_ne_top_iff_ne_top₂
  条件: {x y : E实数} (hx : x != ⊥) (hy : y != ⊥)
  证明: by
  refine ⟨?_, fun h => add_ne_top h.1 h.2⟩
  cases x <;> simp_all only [ne_eq, not_false_eq_true, top_add_of_ne_bot, not_true_eq_false,
    IsEmpty.forall_iff]
  cases y <;> simp_all only [not_false_eq_true, ne_eq, add_top_of_ne_bot, not_true_eq_false,
    coe_ne_top, and_self, implies_true]

Depends on / 依赖: IsEmpty, IsEmpty.forall_iff, add_ne_top, add_top_of_ne_bot, and_self, coe_ne_top, forall_iff, implies_true, ne_eq, not_false_eq_true, not_true_eq_false, top_add_of_ne_bot
-/
lemma add_ne_top_iff_ne_top₂ {x y : EReal} (hx : x != ⊥) (hy : y != ⊥) :
    x + y != ⊤ ↔ x != ⊤ ∧ y != ⊤ := by
  refine ⟨?_, fun h => add_ne_top h.1 h.2⟩
  cases x <;> simp_all only [ne_eq, not_false_eq_true, top_add_of_ne_bot, not_true_eq_false,
    IsEmpty.forall_iff]
  cases y <;> simp_all only [not_false_eq_true, ne_eq, add_top_of_ne_bot, not_true_eq_false,
    coe_ne_top, and_self, implies_true]

/--
lemma `add_ne_top_iff_ne_top_left` / 引理 `add_ne_top_iff_ne_top_left`

English:
lemma add_ne_top_iff_ne_top_left
  given: {x y : EReal} (hy : y != ⊥) (hy' : y != ⊤)
  proof: by
  cases x <;> simp [add_ne_top_iff_ne_top₂, hy, hy']

中文:
引理 add_ne_top_iff_ne_top_left
  条件: {x y : E实数} (hy : y != ⊥) (hy' : y != ⊤)
  证明: by
  cases x <;> simp [add_ne_top_iff_ne_top₂, hy, hy']
-/
lemma add_ne_top_iff_ne_top_left {x y : EReal} (hy : y != ⊥) (hy' : y != ⊤) :
    x + y != ⊤ ↔ x != ⊤ := by
  cases x <;> simp [add_ne_top_iff_ne_top₂, hy, hy']

/--
lemma `add_ne_top_iff_ne_top_right` / 引理 `add_ne_top_iff_ne_top_right`

English:
lemma add_ne_top_iff_ne_top_right
  given: {x y : EReal} (hx : x != ⊥) (hx' : x != ⊤)
  proof: add_comm x y ▸ add_ne_top_iff_ne_top_left hx hx'

中文:
引理 add_ne_top_iff_ne_top_right
  条件: {x y : E实数} (hx : x != ⊥) (hx' : x != ⊤)
  证明: add_comm x y ▸ add_ne_top_iff_ne_top_left hx hx'

Depends on / 依赖: add_comm, add_ne_top_iff_ne_top_left
-/
lemma add_ne_top_iff_ne_top_right {x y : EReal} (hx : x != ⊥) (hx' : x != ⊤) :
    x + y != ⊤ ↔ y != ⊤ := add_comm x y ▸ add_ne_top_iff_ne_top_left hx hx'

/--
lemma `add_ne_top_iff_of_ne_bot_of_ne_top` / 引理 `add_ne_top_iff_of_ne_bot_of_ne_top`

English:
lemma add_ne_top_iff_of_ne_bot_of_ne_top
  given: {x y : EReal} (hy : y != ⊥) (hy' : y != ⊤)
  proof: by
  induction x <;> simp [EReal.add_ne_top_iff_ne_top₂, hy, hy']

中文:
引理 add_ne_top_iff_of_ne_bot_of_ne_top
  条件: {x y : E实数} (hy : y != ⊥) (hy' : y != ⊤)
  证明: by
  induction x <;> simp [EReal.add_ne_top_iff_ne_top₂, hy, hy']

Depends on / 依赖: EReal.add_ne_top_iff_ne_top
-/
lemma add_ne_top_iff_of_ne_bot_of_ne_top {x y : EReal} (hy : y != ⊥) (hy' : y != ⊤) :
    x + y != ⊤ ↔ x != ⊤ := by
  induction x <;> simp [EReal.add_ne_top_iff_ne_top₂, hy, hy']

/-! ### Negation -/

/--
Definition of `neg` / `neg` 的定义

English:
definition neg
  signature: : EReal -> EReal

中文:
定义 neg
  签名: : E实数 -> E实数
-/
protected def neg : EReal -> EReal
  | ⊥ => ⊤
  | ⊤ => ⊥
  | (x : Real) => (-x : Real)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg EReal
  body: ⟨EReal.neg⟩

中文:
实例 :
  签名: 取负 E实数
  定义体: ⟨EReal.neg⟩

Depends on / 依赖: EReal.neg
-/
instance : Neg EReal := ⟨EReal.neg⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SubNegZeroMonoid EReal
  body: congr_arg Real.toEReal neg_zero
  zsmul := zsmulRec

@[simp]

中文:
实例 :
  签名: SubNegZero幺半群 E实数
  定义体: congr_arg Real.toEReal neg_zero
  zsmul := zsmulRec

@[simp]

Depends on / 依赖: Real.toEReal, congr_arg, neg_zero, toEReal
-/
instance : SubNegZeroMonoid EReal where
  neg_zero := congr_arg Real.toEReal neg_zero
  zsmul := zsmulRec

@[simp]
/--
theorem `neg_top` / 定理 `neg_top`

English:
theorem neg_top
  statement: -(⊤ : EReal) = ⊥
  proof: rfl

@[simp]

中文:
定理 neg_top
  结论: -(⊤ : E实数) = ⊥
  证明: rfl

@[simp]
-/
theorem neg_top : -(⊤ : EReal) = ⊥ :=
  rfl

@[simp]
/--
theorem `neg_bot` / 定理 `neg_bot`

English:
theorem neg_bot
  statement: -(⊥ : EReal) = ⊤
  proof: rfl

中文:
定理 neg_bot
  结论: -(⊥ : E实数) = ⊤
  证明: rfl
-/
theorem neg_bot : -(⊥ : EReal) = ⊤ :=
  rfl

/--
theorem `coe_neg` / 定理 `coe_neg`

English:
theorem coe_neg
  given: (x : Real)
  statement: (↑(-x) : EReal) = -↑x
  proof: rfl

中文:
定理 coe_neg
  条件: (x : 实数)
  结论: (↑(-x) : E实数) = -↑x
  证明: rfl
-/
@[simp, norm_cast] theorem coe_neg (x : Real) : (↑(-x) : EReal) = -↑x := rfl

/--
theorem `coe_sub` / 定理 `coe_sub`

English:
theorem coe_sub
  given: (x y : Real)
  statement: (↑(x - y) : EReal) = x - y
  proof: rfl

@[norm_cast]

中文:
定理 coe_sub
  条件: (x y : 实数)
  结论: (↑(x - y) : E实数) = x - y
  证明: rfl

@[norm_cast]
-/
@[simp, norm_cast] theorem coe_sub (x y : Real) : (↑(x - y) : EReal) = x - y := rfl

@[norm_cast]
/--
theorem `coe_zsmul` / 定理 `coe_zsmul`

English:
theorem coe_zsmul
  given: (n : Int) (x : Real)
  statement: (↑(n • x) : EReal) = n • (x : EReal)
  proof: map_zsmul' (⟨⟨(↑), coe_zero⟩, coe_add⟩ : Real ->+ EReal) coe_neg _ _

中文:
定理 coe_zsmul
  条件: (n : 整数) (x : 实数)
  结论: (↑(n • x) : E实数) = n • (x : E实数)
  证明: map_zsmul' (⟨⟨(↑), coe_zero⟩, coe_add⟩ : Real ->+ EReal) coe_neg _ _

Depends on / 依赖: coe_add, coe_neg, coe_zero, map_zsmul
-/
theorem coe_zsmul (n : Int) (x : Real) : (↑(n • x) : EReal) = n • (x : EReal) :=
  map_zsmul' (⟨⟨(↑), coe_zero⟩, coe_add⟩ : Real ->+ EReal) coe_neg _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InvolutiveNeg EReal
  body: match a with
    | ⊥ => rfl
    | ⊤ => rfl
    | (a : Real) => congr_arg Real.toEReal (neg_neg a)

@[simp]

中文:
实例 :
  签名: InvolutiveNeg E实数
  定义体: match a with
    | ⊥ => rfl
    | ⊤ => rfl
    | (a : Real) => congr_arg Real.toEReal (neg_neg a)

@[simp]

Depends on / 依赖: Real.toEReal, congr_arg, neg_neg, toEReal
-/
instance : InvolutiveNeg EReal where
  neg_neg a :=
    match a with
    | ⊥ => rfl
    | ⊤ => rfl
    | (a : Real) => congr_arg Real.toEReal (neg_neg a)

@[simp]
/--
theorem `toReal_neg_eq` / 定理 `toReal_neg_eq`

English:
theorem toReal_neg_eq
  statement: forall {a : EReal}, toReal (-a) = -toReal a

中文:
定理 to实数_neg_eq
  结论: 对任意 {a : E实数}, to实数 (-a) = -to实数 a
-/
theorem toReal_neg_eq : forall {a : EReal}, toReal (-a) = -toReal a
  | ⊤ => by simp
  | ⊥ => by simp
  | (x : Real) => rfl

@[simp]
/--
theorem `neg_eq_top_iff` / 定理 `neg_eq_top_iff`

English:
theorem neg_eq_top_iff
  given: {x : EReal}
  statement: -x = ⊤ ↔ x = ⊥
  proof: neg_injective.eq_iff' rfl

@[simp]

中文:
定理 neg_eq_top_iff
  条件: {x : E实数}
  结论: -x = ⊤ ↔ x = ⊥
  证明: neg_injective.eq_iff' rfl

@[simp]

Depends on / 依赖: eq_iff, neg_injective, neg_injective.eq_iff
-/
theorem neg_eq_top_iff {x : EReal} : -x = ⊤ ↔ x = ⊥ :=
  neg_injective.eq_iff' rfl

@[simp]
/--
theorem `neg_eq_bot_iff` / 定理 `neg_eq_bot_iff`

English:
theorem neg_eq_bot_iff
  given: {x : EReal}
  statement: -x = ⊥ ↔ x = ⊤
  proof: neg_injective.eq_iff' rfl

@[simp]

中文:
定理 neg_eq_bot_iff
  条件: {x : E实数}
  结论: -x = ⊥ ↔ x = ⊤
  证明: neg_injective.eq_iff' rfl

@[simp]

Depends on / 依赖: eq_iff, neg_injective, neg_injective.eq_iff
-/
theorem neg_eq_bot_iff {x : EReal} : -x = ⊥ ↔ x = ⊤ :=
  neg_injective.eq_iff' rfl

@[simp]
/--
theorem `neg_eq_zero_iff` / 定理 `neg_eq_zero_iff`

English:
theorem neg_eq_zero_iff
  given: {x : EReal}
  statement: -x = 0 ↔ x = 0
  proof: neg_injective.eq_iff' neg_zero

中文:
定理 neg_eq_zero_iff
  条件: {x : E实数}
  结论: -x = 0 ↔ x = 0
  证明: neg_injective.eq_iff' neg_zero

Depends on / 依赖: eq_iff, neg_injective, neg_injective.eq_iff, neg_zero
-/
theorem neg_eq_zero_iff {x : EReal} : -x = 0 ↔ x = 0 :=
  neg_injective.eq_iff' neg_zero

/--
theorem `neg_strictAnti` / 定理 `neg_strictAnti`

English:
theorem neg_strictAnti
  statement: StrictAnti (- · : EReal -> EReal)
  proof: WithBot.strictAnti_iff.2 ⟨WithTop.strictAnti_iff.2
    ⟨coe_strictMono.comp_strictAnti fun _ _ => neg_lt_neg, fun _ => bot_lt_coe _⟩,
      WithTop.forall.2 ⟨bot_lt_top, fun _ => coe_lt_top _⟩⟩

中文:
定理 neg_strictAnti
  结论: 严格递减 (- · : E实数 -> E实数)
  证明: WithBot.strictAnti_iff.2 ⟨WithTop.strictAnti_iff.2
    ⟨coe_strictMono.comp_strictAnti fun _ _ => neg_lt_neg, fun _ => bot_lt_coe _⟩,
      WithTop.forall.2 ⟨bot_lt_top, fun _ => coe_lt_top _⟩⟩

Depends on / 依赖: WithBot, WithBot.strictAnti_iff, WithTop, WithTop.forall, WithTop.strictAnti_iff, bot_lt_coe, bot_lt_top, coe_lt_top, coe_strictMono, coe_strictMono.comp_strictAnti, comp_strictAnti, neg_lt_neg, strictAnti_iff
-/
theorem neg_strictAnti : StrictAnti (- · : EReal -> EReal) :=
  WithBot.strictAnti_iff.2 ⟨WithTop.strictAnti_iff.2
    ⟨coe_strictMono.comp_strictAnti fun _ _ => neg_lt_neg, fun _ => bot_lt_coe _⟩,
      WithTop.forall.2 ⟨bot_lt_top, fun _ => coe_lt_top _⟩⟩

/--
theorem `neg_le_neg_iff` / 定理 `neg_le_neg_iff`

English:
theorem neg_le_neg_iff
  given: {a b : EReal}
  statement: -a <= -b ↔ b <= a
  proof: neg_strictAnti.le_iff_ge

中文:
定理 neg_le_neg_iff
  条件: {a b : E实数}
  结论: -a <= -b ↔ b <= a
  证明: neg_strictAnti.le_iff_ge
-/
@[simp] theorem neg_le_neg_iff {a b : EReal} : -a <= -b ↔ b <= a := neg_strictAnti.le_iff_ge

/--
theorem `neg_lt_neg_iff` / 定理 `neg_lt_neg_iff`

English:
theorem neg_lt_neg_iff
  given: {a b : EReal}
  statement: -a < -b ↔ b < a
  proof: neg_strictAnti.lt_iff_gt

中文:
定理 neg_lt_neg_iff
  条件: {a b : E实数}
  结论: -a < -b ↔ b < a
  证明: neg_strictAnti.lt_iff_gt
-/
@[simp] theorem neg_lt_neg_iff {a b : EReal} : -a < -b ↔ b < a := neg_strictAnti.lt_iff_gt

/--
theorem `neg_le` / 定理 `neg_le`

English:
theorem neg_le
  given: {a b : EReal}
  statement: -a <= b ↔ -b <= a
  proof: by
  rw [← neg_le_neg_iff]; rw [neg_neg]

中文:
定理 neg_le
  条件: {a b : E实数}
  结论: -a <= b ↔ -b <= a
  证明: by
  rw [← neg_le_neg_iff]; rw [neg_neg]
-/
protected theorem neg_le {a b : EReal} : -a <= b ↔ -b <= a := by
  rw [← neg_le_neg_iff]; rw [neg_neg]

/--
theorem `neg_le_of_neg_le` / 定理 `neg_le_of_neg_le`

English:
theorem neg_le_of_neg_le
  given: {a b : EReal} (h : -a <= b)
  statement: -b <= a
  proof: EReal.neg_le.mp h

中文:
定理 neg_le_of_neg_le
  条件: {a b : E实数} (h : -a <= b)
  结论: -b <= a
  证明: EReal.neg_le.mp h
-/
protected theorem neg_le_of_neg_le {a b : EReal} (h : -a <= b) : -b <= a := EReal.neg_le.mp h

/--
theorem `le_neg` / 定理 `le_neg`

English:
theorem le_neg
  given: {a b : EReal}
  statement: a <= -b ↔ b <= -a
  proof: by
  rw [← neg_le_neg_iff]; rw [neg_neg]

中文:
定理 le_neg
  条件: {a b : E实数}
  结论: a <= -b ↔ b <= -a
  证明: by
  rw [← neg_le_neg_iff]; rw [neg_neg]
-/
protected theorem le_neg {a b : EReal} : a <= -b ↔ b <= -a := by
  rw [← neg_le_neg_iff]; rw [neg_neg]

/--
theorem `le_neg_of_le_neg` / 定理 `le_neg_of_le_neg`

English:
theorem le_neg_of_le_neg
  given: {a b : EReal} (h : a <= -b)
  statement: b <= -a
  proof: EReal.le_neg.mp h

中文:
定理 le_neg_of_le_neg
  条件: {a b : E实数} (h : a <= -b)
  结论: b <= -a
  证明: EReal.le_neg.mp h
-/
protected theorem le_neg_of_le_neg {a b : EReal} (h : a <= -b) : b <= -a := EReal.le_neg.mp h

/--
theorem `neg_lt_comm` / 定理 `neg_lt_comm`

English:
theorem neg_lt_comm
  given: {a b : EReal}
  statement: -a < b ↔ -b < a
  proof: by rw [← neg_lt_neg_iff, neg_neg]

中文:
定理 neg_lt_comm
  条件: {a b : E实数}
  结论: -a < b ↔ -b < a
  证明: by rw [← neg_lt_neg_iff, neg_neg]

Depends on / 依赖: neg_lt_neg_iff, neg_neg
-/
theorem neg_lt_comm {a b : EReal} : -a < b ↔ -b < a := by rw [← neg_lt_neg_iff, neg_neg]

/--
theorem `neg_lt_of_neg_lt` / 定理 `neg_lt_of_neg_lt`

English:
theorem neg_lt_of_neg_lt
  given: {a b : EReal} (h : -a < b)
  statement: -b < a
  proof: neg_lt_comm.mp h

中文:
定理 neg_lt_of_neg_lt
  条件: {a b : E实数} (h : -a < b)
  结论: -b < a
  证明: neg_lt_comm.mp h
-/
protected theorem neg_lt_of_neg_lt {a b : EReal} (h : -a < b) : -b < a := neg_lt_comm.mp h

/--
theorem `lt_neg_comm` / 定理 `lt_neg_comm`

English:
theorem lt_neg_comm
  given: {a b : EReal}
  statement: a < -b ↔ b < -a
  proof: by
  rw [← neg_lt_neg_iff]; rw [neg_neg]

中文:
定理 lt_neg_comm
  条件: {a b : E实数}
  结论: a < -b ↔ b < -a
  证明: by
  rw [← neg_lt_neg_iff]; rw [neg_neg]

Depends on / 依赖: neg_lt_neg_iff, neg_neg
-/
theorem lt_neg_comm {a b : EReal} : a < -b ↔ b < -a := by
  rw [← neg_lt_neg_iff]; rw [neg_neg]

/--
theorem `neg_lt_zero` / 定理 `neg_lt_zero`

English:
theorem neg_lt_zero
  given: {a : EReal}
  statement: -a < 0 ↔ 0 < a
  proof: by rw [neg_lt_comm, neg_zero]

中文:
定理 neg_lt_zero
  条件: {a : E实数}
  结论: -a < 0 ↔ 0 < a
  证明: by rw [neg_lt_comm, neg_zero]
-/
@[simp] protected theorem neg_lt_zero {a : EReal} : -a < 0 ↔ 0 < a := by rw [neg_lt_comm, neg_zero]
/--
theorem `neg_le_zero` / 定理 `neg_le_zero`

English:
theorem neg_le_zero
  given: {a : EReal}
  statement: -a <= 0 ↔ 0 <= a
  proof: by rw [EReal.neg_le, neg_zero]

中文:
定理 neg_le_zero
  条件: {a : E实数}
  结论: -a <= 0 ↔ 0 <= a
  证明: by rw [EReal.neg_le, neg_zero]
-/
@[simp] protected theorem neg_le_zero {a : EReal} : -a <= 0 ↔ 0 <= a := by rw [EReal.neg_le, neg_zero]
/--
theorem `neg_pos` / 定理 `neg_pos`

English:
theorem neg_pos
  given: {a : EReal}
  statement: 0 < -a ↔ a < 0
  proof: by rw [lt_neg_comm, neg_zero]

中文:
定理 neg_pos
  条件: {a : E实数}
  结论: 0 < -a ↔ a < 0
  证明: by rw [lt_neg_comm, neg_zero]
-/
@[simp] protected theorem neg_pos {a : EReal} : 0 < -a ↔ a < 0 := by rw [lt_neg_comm, neg_zero]
/--
theorem `neg_nonneg` / 定理 `neg_nonneg`

English:
theorem neg_nonneg
  given: {a : EReal}
  statement: 0 <= -a ↔ a <= 0
  proof: by rw [EReal.le_neg, neg_zero]

中文:
定理 neg_nonneg
  条件: {a : E实数}
  结论: 0 <= -a ↔ a <= 0
  证明: by rw [EReal.le_neg, neg_zero]
-/
@[simp] protected theorem neg_nonneg {a : EReal} : 0 <= -a ↔ a <= 0 := by rw [EReal.le_neg, neg_zero]

/--
theorem `lt_neg_of_lt_neg` / 定理 `lt_neg_of_lt_neg`

English:
theorem lt_neg_of_lt_neg
  given: {a b : EReal} (h : a < -b)
  statement: b < -a
  proof: lt_neg_comm.mp h

中文:
定理 lt_neg_of_lt_neg
  条件: {a b : E实数} (h : a < -b)
  结论: b < -a
  证明: lt_neg_comm.mp h
-/
protected theorem lt_neg_of_lt_neg {a b : EReal} (h : a < -b) : b < -a := lt_neg_comm.mp h

/--
Definition of `negOrderIso` / `negOrderIso` 的定义

English:
definition negOrderIso
  signature: : EReal ≃o ERealᵒᵈ
  body: { Equiv.neg EReal with
    toFun := fun x => OrderDual.toDual (-x)
    invFun := fun x => -OrderDual.ofDual x
    map_rel_iff' := neg_le_neg_iff }

中文:
定义 negOrderIso
  签名: : E实数 ≃o E实数ᵒᵈ
  定义体: { Equiv.neg EReal with
    toFun := fun x => OrderDual.toDual (-x)
    invFun := fun x => -OrderDual.ofDual x
    map_rel_iff' := neg_le_neg_iff }

Depends on / 依赖: Equiv.neg, OrderDual, OrderDual.ofDual, OrderDual.toDual, invFun, map_rel_iff, neg_le_neg_iff, ofDual, toDual
-/
def negOrderIso : EReal ≃o ERealᵒᵈ :=
  { Equiv.neg EReal with
    toFun := fun x => OrderDual.toDual (-x)
    invFun := fun x => -OrderDual.ofDual x
    map_rel_iff' := neg_le_neg_iff }

/--
lemma `neg_add` / 引理 `neg_add`

English:
lemma neg_add
  given: {x y : EReal} (h1 : x != ⊥ ∨ y != ⊤) (h2 : x != ⊤ ∨ y != ⊥)
  proof: by
  induction x <;> induction y <;> try tauto
  rw [← coe_add]; rw [← coe_neg]; rw [← coe_neg]; rw [← coe_sub]; rw [neg_add']

中文:
引理 neg_add
  条件: {x y : E实数} (h1 : x != ⊥ ∨ y != ⊤) (h2 : x != ⊤ ∨ y != ⊥)
  证明: by
  induction x <;> induction y <;> try tauto
  rw [← coe_add]; rw [← coe_neg]; rw [← coe_neg]; rw [← coe_sub]; rw [neg_add']

Depends on / 依赖: coe_add, coe_neg, coe_sub, neg_add
-/
lemma neg_add {x y : EReal} (h1 : x != ⊥ ∨ y != ⊤) (h2 : x != ⊤ ∨ y != ⊥) :
    -(x + y) = -x - y := by
  induction x <;> induction y <;> try tauto
  rw [← coe_add]; rw [← coe_neg]; rw [← coe_neg]; rw [← coe_sub]; rw [neg_add']

/--
lemma `neg_sub` / 引理 `neg_sub`

English:
lemma neg_sub
  given: {x y : EReal} (h1 : x != ⊥ ∨ y != ⊥) (h2 : x != ⊤ ∨ y != ⊤)
  proof: by
  rw [sub_eq_add_neg]; rw [neg_add _ _]; rw [sub_eq_add_neg]; rw [neg_neg] <;> simp_all

中文:
引理 neg_sub
  条件: {x y : E实数} (h1 : x != ⊥ ∨ y != ⊥) (h2 : x != ⊤ ∨ y != ⊤)
  证明: by
  rw [sub_eq_add_neg]; rw [neg_add _ _]; rw [sub_eq_add_neg]; rw [neg_neg] <;> simp_all

Depends on / 依赖: neg_add, neg_neg, sub_eq_add_neg
-/
lemma neg_sub {x y : EReal} (h1 : x != ⊥ ∨ y != ⊥) (h2 : x != ⊤ ∨ y != ⊤) :
    -(x - y) = -x + y := by
  rw [sub_eq_add_neg]; rw [neg_add _ _]; rw [sub_eq_add_neg]; rw [neg_neg] <;> simp_all

/-- Induction principle for `EReal`s splitting into cases `↑(x : ℝ≥0∞)` and `-↑(x : ℝ≥0∞)`.
In the latter case, we additionally assume `0 < x`. -/
@[elab_as_elim]
/--
Definition of `recENNReal` / `recENNReal` 的定义

English:
definition recENNReal
  signature: {motive : EReal -> Sort*} (coe : forall x : Real>=0∞, motive x)
  body: if hx : 0 <= x then coe_toENNReal hx ▸ coe _
  else
    haveI H₁ : 0 < -x := by simpa using hx
    haveI H₂ : x = -(-x).toENNReal := by rw [coe_toENNReal H₁.le, neg_neg]
H₂ ▸ neg_coe _ by positivity

@[simp]

中文:
定义 recENN实数
  签名: {motive : E实数 -> 类型层*} (coe : 对任意 x : 实数>=0∞, motive x)
  定义体: if hx : 0 <= x then coe_toENNReal hx ▸ coe _
  else
    haveI H₁ : 0 < -x := by simpa using hx
    haveI H₂ : x = -(-x).toENNReal := by rw [coe_toENNReal H₁.le, neg_neg]
H₂ ▸ neg_coe _ by positivity

@[simp]

Depends on / 依赖: coe_toENNReal, neg_coe, neg_neg, toENNReal
-/
def recENNReal {motive : EReal -> Sort*} (coe : forall x : Real>=0∞, motive x)
    (neg_coe : forall x : Real>=0∞, 0 < x -> motive (-x)) (x : EReal) : motive x :=
  if hx : 0 <= x then coe_toENNReal hx ▸ coe _
  else
    haveI H₁ : 0 < -x := by simpa using hx
    haveI H₂ : x = -(-x).toENNReal := by rw [coe_toENNReal H₁.le, neg_neg]
H₂ ▸ neg_coe _ by positivity

@[simp]
/--
theorem `recENNReal_coe_ennreal` / 定理 `recENNReal_coe_ennreal`

English:
theorem recENNReal_coe_ennreal
  statement: {motive : EReal -> Sort*} (coe : forall x : Real>=0∞, motive x)
  proof: by
  suffices forall y : EReal, x = y -> (recENNReal coe neg_coe y : motive y) ≍ coe x from
    heq_iff_eq.mp (this x rfl)
  intro y hy
  have H₁ : 0 <= y := hy ▸ coe_ennreal_nonneg x
  obtain rfl : y.toENNReal = x := by simp [← hy]
  simp [recENNReal, H₁]

proof_wanted recENNReal_neg_coe_ennreal {m

中文:
定理 recENN实数_coe_ennreal
  结论: {motive : E实数 -> 类型层*} (coe : 对任意 x : 实数>=0∞, motive x)
  证明: by
  suffices forall y : EReal, x = y -> (recENNReal coe neg_coe y : motive y) ≍ coe x from
    heq_iff_eq.mp (this x rfl)
  intro y hy
  have H₁ : 0 <= y := hy ▸ coe_ennreal_nonneg x
  obtain rfl : y.toENNReal = x := by simp [← hy]
  simp [recENNReal, H₁]

proof_wanted recENNReal_neg_coe_ennreal {m

Depends on / 依赖: coe_ennreal_nonneg, heq_iff_eq, heq_iff_eq.mp, motive, neg_coe, recENNReal, toENNReal, y.toENNReal
-/
theorem recENNReal_coe_ennreal {motive : EReal -> Sort*} (coe : forall x : Real>=0∞, motive x)
    (neg_coe : forall x : Real>=0∞, 0 < x -> motive (-x)) (x : Real>=0∞) : recENNReal coe neg_coe x = coe x := by
  suffices forall y : EReal, x = y -> (recENNReal coe neg_coe y : motive y) ≍ coe x from
    heq_iff_eq.mp (this x rfl)
  intro y hy
  have H₁ : 0 <= y := hy ▸ coe_ennreal_nonneg x
  obtain rfl : y.toENNReal = x := by simp [← hy]
  simp [recENNReal, H₁]

proof_wanted recENNReal_neg_coe_ennreal {motive : EReal -> Sort*} (coe : forall x : Real>=0∞, motive x)
    (neg_coe : forall x : Real>=0∞, 0 < x -> motive (-x)) {x : Real>=0∞} (hx : 0 < x) :
    recENNReal coe neg_coe (-x) = neg_coe x hx

/-!
### Subtraction

Subtraction on `EReal` is defined by `x - y = x + (-y)`. Since addition is badly behaved at some
points, so is subtraction. There is no standard algebraic typeclass involving subtraction that is
registered on `EReal`, beyond `SubNegZeroMonoid`, because of this bad behavior.
-/

@[simp]
/--
theorem `bot_sub` / 定理 `bot_sub`

English:
theorem bot_sub
  given: (x : EReal)
  statement: ⊥ - x = ⊥
  proof: bot_add x

@[simp]

中文:
定理 bot_sub
  条件: (x : E实数)
  结论: ⊥ - x = ⊥
  证明: bot_add x

@[simp]

Depends on / 依赖: bot_add
-/
theorem bot_sub (x : EReal) : ⊥ - x = ⊥ :=
  bot_add x

@[simp]
/--
theorem `sub_top` / 定理 `sub_top`

English:
theorem sub_top
  given: (x : EReal)
  statement: x - ⊤ = ⊥
  proof: add_bot x

@[simp]

中文:
定理 sub_top
  条件: (x : E实数)
  结论: x - ⊤ = ⊥
  证明: add_bot x

@[simp]

Depends on / 依赖: add_bot
-/
theorem sub_top (x : EReal) : x - ⊤ = ⊥ :=
  add_bot x

@[simp]
/--
theorem `top_sub_bot` / 定理 `top_sub_bot`

English:
theorem top_sub_bot
  statement: (⊤ : EReal) - ⊥ = ⊤
  proof: rfl

@[simp]

中文:
定理 top_sub_bot
  结论: (⊤ : E实数) - ⊥ = ⊤
  证明: rfl

@[simp]
-/
theorem top_sub_bot : (⊤ : EReal) - ⊥ = ⊤ :=
  rfl

@[simp]
/--
theorem `top_sub_coe` / 定理 `top_sub_coe`

English:
theorem top_sub_coe
  given: (x : Real)
  statement: (⊤ : EReal) - x = ⊤
  proof: rfl

@[simp]

中文:
定理 top_sub_coe
  条件: (x : 实数)
  结论: (⊤ : E实数) - x = ⊤
  证明: rfl

@[simp]
-/
theorem top_sub_coe (x : Real) : (⊤ : EReal) - x = ⊤ :=
  rfl

@[simp]
/--
theorem `coe_sub_bot` / 定理 `coe_sub_bot`

English:
theorem coe_sub_bot
  given: (x : Real)
  statement: (x : EReal) - ⊥ = ⊤
  proof: rfl

@[simp]

中文:
定理 coe_sub_bot
  条件: (x : 实数)
  结论: (x : E实数) - ⊥ = ⊤
  证明: rfl

@[simp]
-/
theorem coe_sub_bot (x : Real) : (x : EReal) - ⊥ = ⊤ :=
  rfl

@[simp]
/--
lemma `sub_bot` / 引理 `sub_bot`

English:
lemma sub_bot
  given: {x : EReal} (h : x != ⊥)
  statement: x - ⊥ = ⊤
  proof: by
  cases x <;> tauto

@[simp]

中文:
引理 sub_bot
  条件: {x : E实数} (h : x != ⊥)
  结论: x - ⊥ = ⊤
  证明: by
  cases x <;> tauto

@[simp]
-/
lemma sub_bot {x : EReal} (h : x != ⊥) : x - ⊥ = ⊤ := by
  cases x <;> tauto

@[simp]
/--
lemma `top_sub` / 引理 `top_sub`

English:
lemma top_sub
  given: {x : EReal} (hx : x != ⊤)
  statement: ⊤ - x = ⊤
  proof: by
  cases x <;> tauto

@[simp]

中文:
引理 top_sub
  条件: {x : E实数} (hx : x != ⊤)
  结论: ⊤ - x = ⊤
  证明: by
  cases x <;> tauto

@[simp]
-/
lemma top_sub {x : EReal} (hx : x != ⊤) : ⊤ - x = ⊤ := by
  cases x <;> tauto

@[simp]
/--
lemma `sub_self` / 引理 `sub_self`

English:
lemma sub_self
  given: {x : EReal} (h_top : x != ⊤) (h_bot : x != ⊥)
  statement: x - x = 0
  proof: by
  cases x <;> simp_all [← coe_sub]

中文:
引理 sub_self
  条件: {x : E实数} (h_top : x != ⊤) (h_bot : x != ⊥)
  结论: x - x = 0
  证明: by
  cases x <;> simp_all [← coe_sub]

Depends on / 依赖: coe_sub
-/
lemma sub_self {x : EReal} (h_top : x != ⊤) (h_bot : x != ⊥) : x - x = 0 := by
  cases x <;> simp_all [← coe_sub]

/--
lemma `sub_self_le_zero` / 引理 `sub_self_le_zero`

English:
lemma sub_self_le_zero
  given: {x : EReal}
  statement: x - x <= 0
  proof: by
  cases x <;> simp

中文:
引理 sub_self_le_zero
  条件: {x : E实数}
  结论: x - x <= 0
  证明: by
  cases x <;> simp
-/
lemma sub_self_le_zero {x : EReal} : x - x <= 0 := by
  cases x <;> simp

/--
lemma `sub_nonneg` / 引理 `sub_nonneg`

English:
lemma sub_nonneg
  given: {x y : EReal} (h_top : x != ⊤ ∨ y != ⊤) (h_bot : x != ⊥ ∨ y != ⊥)
  proof: by
  cases x <;> cases y <;> simp_all [← EReal.coe_sub]

中文:
引理 sub_nonneg
  条件: {x y : E实数} (h_top : x != ⊤ ∨ y != ⊤) (h_bot : x != ⊥ ∨ y != ⊥)
  证明: by
  cases x <;> cases y <;> simp_all [← EReal.coe_sub]

Depends on / 依赖: EReal.coe_sub, coe_sub
-/
lemma sub_nonneg {x y : EReal} (h_top : x != ⊤ ∨ y != ⊤) (h_bot : x != ⊥ ∨ y != ⊥) :
    0 <= x - y ↔ y <= x := by
  cases x <;> cases y <;> simp_all [← EReal.coe_sub]

/--
lemma `sub_nonpos` / 引理 `sub_nonpos`

English:
lemma sub_nonpos
  given: {x y : EReal}
  statement: x - y <= 0 ↔ x <= y
  proof: by
  cases x <;> cases y <;> simp [← EReal.coe_sub]

中文:
引理 sub_nonpos
  条件: {x y : E实数}
  结论: x - y <= 0 ↔ x <= y
  证明: by
  cases x <;> cases y <;> simp [← EReal.coe_sub]

Depends on / 依赖: EReal.coe_sub, coe_sub
-/
lemma sub_nonpos {x y : EReal} : x - y <= 0 ↔ x <= y := by
  cases x <;> cases y <;> simp [← EReal.coe_sub]

/--
lemma `sub_pos` / 引理 `sub_pos`

English:
lemma sub_pos
  given: {x y : EReal}
  statement: 0 < x - y ↔ y < x
  proof: by
  cases x <;> cases y <;> simp [← EReal.coe_sub]

中文:
引理 sub_pos
  条件: {x y : E实数}
  结论: 0 < x - y ↔ y < x
  证明: by
  cases x <;> cases y <;> simp [← EReal.coe_sub]

Depends on / 依赖: EReal.coe_sub, coe_sub
-/
lemma sub_pos {x y : EReal} : 0 < x - y ↔ y < x := by
  cases x <;> cases y <;> simp [← EReal.coe_sub]

/--
lemma `sub_neg` / 引理 `sub_neg`

English:
lemma sub_neg
  given: {x y : EReal} (h_top : x != ⊤ ∨ y != ⊤) (h_bot : x != ⊥ ∨ y != ⊥)
  proof: by
  cases x <;> cases y <;> simp_all [← EReal.coe_sub]

中文:
引理 sub_neg
  条件: {x y : E实数} (h_top : x != ⊤ ∨ y != ⊤) (h_bot : x != ⊥ ∨ y != ⊥)
  证明: by
  cases x <;> cases y <;> simp_all [← EReal.coe_sub]

Depends on / 依赖: EReal.coe_sub, coe_sub
-/
lemma sub_neg {x y : EReal} (h_top : x != ⊤ ∨ y != ⊤) (h_bot : x != ⊥ ∨ y != ⊥) :
    x - y < 0 ↔ x < y := by
  cases x <;> cases y <;> simp_all [← EReal.coe_sub]

/--
theorem `sub_le_sub` / 定理 `sub_le_sub`

English:
theorem sub_le_sub
  given: {x y z t : EReal} (h : x <= y) (h' : t <= z)
  statement: x - z <= y - t
  proof: add_le_add h (neg_le_neg_iff.2 h')

中文:
定理 sub_le_sub
  条件: {x y z t : E实数} (h : x <= y) (h' : t <= z)
  结论: x - z <= y - t
  证明: add_le_add h (neg_le_neg_iff.2 h')

Depends on / 依赖: add_le_add, neg_le_neg_iff
-/
theorem sub_le_sub {x y z t : EReal} (h : x <= y) (h' : t <= z) : x - z <= y - t :=
  add_le_add h (neg_le_neg_iff.2 h')

/--
theorem `sub_lt_sub_of_lt_of_le` / 定理 `sub_lt_sub_of_lt_of_le`

English:
theorem sub_lt_sub_of_lt_of_le
  statement: {x y z t : EReal} (h : x < y) (h' : z <= t) (hz : z != ⊥)
  proof: add_lt_add_of_lt_of_le h (neg_le_neg_iff.2 h') (by simp [ht]) (by simp [hz])

中文:
定理 sub_lt_sub_of_lt_of_le
  结论: {x y z t : E实数} (h : x < y) (h' : z <= t) (hz : z != ⊥)
  证明: add_lt_add_of_lt_of_le h (neg_le_neg_iff.2 h') (by simp [ht]) (by simp [hz])

Depends on / 依赖: add_lt_add_of_lt_of_le, neg_le_neg_iff
-/
theorem sub_lt_sub_of_lt_of_le {x y z t : EReal} (h : x < y) (h' : z <= t) (hz : z != ⊥)
    (ht : t != ⊤) : x - t < y - z :=
  add_lt_add_of_lt_of_le h (neg_le_neg_iff.2 h') (by simp [ht]) (by simp [hz])

/--
theorem `coe_real_ereal_eq_coe_toNNReal_sub_coe_toNNReal` / 定理 `coe_real_ereal_eq_coe_toNNReal_sub_coe_toNNReal`

English:
theorem coe_real_ereal_eq_coe_toNNReal_sub_coe_toNNReal
  given: (x : Real)
  proof: by
  rcases le_total 0 x with (h | h)
  · lift x to Real>=0 using h
    rw [Real.toNNReal_of_nonpos (neg_nonpos.mpr x.coe_nonneg)]; rw [Real.toNNReal_coe]; rw [ENNReal.coe_zero]; rw [coe_ennreal_zero]; rw [sub_zero]
    rfl
  · rw [Real.toNNReal_of_nonpos h, ENNReal.coe_zero, coe_ennreal_zero, coe_n

中文:
定理 coe_real_ereal_eq_coe_toNN实数_sub_coe_toNN实数
  条件: (x : 实数)
  证明: by
  rcases le_total 0 x with (h | h)
  · lift x to Real>=0 using h
    rw [Real.toNNReal_of_nonpos (neg_nonpos.mpr x.coe_nonneg)]; rw [Real.toNNReal_coe]; rw [ENNReal.coe_zero]; rw [coe_ennreal_zero]; rw [sub_zero]
    rfl
  · rw [Real.toNNReal_of_nonpos h, ENNReal.coe_zero, coe_ennreal_zero, coe_n

Depends on / 依赖: ENNReal, ENNReal.coe_zero, Real.coe_toNNReal, Real.toNNReal_coe, Real.toNNReal_of_nonpos, coe_ennreal_zero, coe_neg, coe_nnreal_eq_coe_real, coe_nonneg, coe_toNNReal, coe_zero, le_total, neg_neg, neg_nonneg, neg_nonpos, neg_nonpos.mpr, sub_zero, toNNReal_coe, toNNReal_of_nonpos, x.coe_nonneg
-/
theorem coe_real_ereal_eq_coe_toNNReal_sub_coe_toNNReal (x : Real) :
    (x : EReal) = Real.toNNReal x - Real.toNNReal (-x) := by
  rcases le_total 0 x with (h | h)
  · lift x to Real>=0 using h
    rw [Real.toNNReal_of_nonpos (neg_nonpos.mpr x.coe_nonneg)]; rw [Real.toNNReal_coe]; rw [ENNReal.coe_zero]; rw [coe_ennreal_zero]; rw [sub_zero]
    rfl
  · rw [Real.toNNReal_of_nonpos h, ENNReal.coe_zero, coe_ennreal_zero, coe_nnreal_eq_coe_real,
      Real.coe_toNNReal, zero_sub, coe_neg, neg_neg]
    exact neg_nonneg.2 h

/--
theorem `toReal_sub` / 定理 `toReal_sub`

English:
theorem toReal_sub
  given: {x y : EReal} (hx : x != ⊤) (h'x : x != ⊥) (hy : y != ⊤) (h'y : y != ⊥)
  proof: by
  lift x to Real using ⟨hx, h'x⟩
  lift y to Real using ⟨hy, h'y⟩
  rfl

中文:
定理 to实数_sub
  条件: {x y : E实数} (hx : x != ⊤) (h'x : x != ⊥) (hy : y != ⊤) (h'y : y != ⊥)
  证明: by
  lift x to Real using ⟨hx, h'x⟩
  lift y to Real using ⟨hy, h'y⟩
  rfl
-/
theorem toReal_sub {x y : EReal} (hx : x != ⊤) (h'x : x != ⊥) (hy : y != ⊤) (h'y : y != ⊥) :
    toReal (x - y) = toReal x - toReal y := by
  lift x to Real using ⟨hx, h'x⟩
  lift y to Real using ⟨hy, h'y⟩
  rfl

/--
lemma `toENNReal_sub` / 引理 `toENNReal_sub`

English:
lemma toENNReal_sub
  given: {x y : EReal} (hy : 0 <= y)
  proof: by
  induction x <;> induction y <;> try {· simp_all [zero_tsub, ENNReal.sub_top]}
  rename_i x y
  by_cases hxy : x <= y
  · rw [toENNReal_of_nonpos <| sub_nonpos.mpr <| EReal.coe_le_coe_iff.mpr hxy]
    exact (tsub_eq_zero_of_le <| toENNReal_le_toENNReal <| EReal.coe_le_coe_iff.mpr hxy).symm
  · r

中文:
引理 toENN实数_sub
  条件: {x y : E实数} (hy : 0 <= y)
  证明: by
  induction x <;> induction y <;> try {· simp_all [zero_tsub, ENNReal.sub_top]}
  rename_i x y
  by_cases hxy : x <= y
  · rw [toENNReal_of_nonpos <| sub_nonpos.mpr <| EReal.coe_le_coe_iff.mpr hxy]
    exact (tsub_eq_zero_of_le <| toENNReal_le_toENNReal <| EReal.coe_le_coe_iff.mpr hxy).symm
  · r

Depends on / 依赖: ENNReal, ENNReal.sub_top, EReal.coe_le_coe_iff.mpr, EReal.coe_nonneg.mp, coe_le_coe_iff, coe_nonneg, coe_sub, ne_of_beq_false, ofReal_sub, rename_i, sub_nonpos, sub_nonpos.mpr, sub_top, toENNReal_le_toENNReal, toENNReal_of_ne_top, toENNReal_of_nonpos, toReal_coe, tsub_eq_zero_of_le, zero_tsub
-/
lemma toENNReal_sub {x y : EReal} (hy : 0 <= y) :
    (x - y).toENNReal = x.toENNReal - y.toENNReal := by
  induction x <;> induction y <;> try {· simp_all [zero_tsub, ENNReal.sub_top]}
  rename_i x y
  by_cases hxy : x <= y
  · rw [toENNReal_of_nonpos <| sub_nonpos.mpr <| EReal.coe_le_coe_iff.mpr hxy]
    exact (tsub_eq_zero_of_le <| toENNReal_le_toENNReal <| EReal.coe_le_coe_iff.mpr hxy).symm
  · rw [toENNReal_of_ne_top (ne_of_beq_false rfl).symm, ← coe_sub, toReal_coe,
      ofReal_sub x (EReal.coe_nonneg.mp hy)]
    simp

/--
lemma `add_sub_add_comm` / 引理 `add_sub_add_comm`

English:
lemma add_sub_add_comm
  given: {a b c d : EReal} (h1 : c != ⊥ ∨ d != ⊤) (h2 : c != ⊤ ∨ d != ⊥)
  proof: by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [EReal.neg_add h1 h2]; rw [sub_eq_add_neg]
  grind

中文:
引理 add_sub_add_comm
  条件: {a b c d : E实数} (h1 : c != ⊥ ∨ d != ⊤) (h2 : c != ⊤ ∨ d != ⊥)
  证明: by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [EReal.neg_add h1 h2]; rw [sub_eq_add_neg]
  grind

Depends on / 依赖: EReal.neg_add, neg_add, sub_eq_add_neg
-/
lemma add_sub_add_comm {a b c d : EReal} (h1 : c != ⊥ ∨ d != ⊤) (h2 : c != ⊤ ∨ d != ⊥) :
    a + b - (c + d) = (a - c) + (b - d) := by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [EReal.neg_add h1 h2]; rw [sub_eq_add_neg]
  grind

/--
lemma `add_sub_cancel_right` / 引理 `add_sub_cancel_right`

English:
lemma add_sub_cancel_right
  given: {a : EReal} {b : Real}
  statement: a + b - b = a
  proof: by
  cases a <;> norm_cast
  exact _root_.add_sub_cancel_right _ _

中文:
引理 add_sub_cancel_right
  条件: {a : E实数} {b : 实数}
  结论: a + b - b = a
  证明: by
  cases a <;> norm_cast
  exact _root_.add_sub_cancel_right _ _

Depends on / 依赖: _root_, _root_.add_sub_cancel_right, add_sub_cancel_right
-/
lemma add_sub_cancel_right {a : EReal} {b : Real} : a + b - b = a := by
  cases a <;> norm_cast
  exact _root_.add_sub_cancel_right _ _

/--
lemma `add_sub_cancel_left` / 引理 `add_sub_cancel_left`

English:
lemma add_sub_cancel_left
  given: {a : EReal} {b : Real}
  statement: b + a - b = a
  proof: by
  rw [add_comm]; rw [EReal.add_sub_cancel_right]

中文:
引理 add_sub_cancel_left
  条件: {a : E实数} {b : 实数}
  结论: b + a - b = a
  证明: by
  rw [add_comm]; rw [EReal.add_sub_cancel_right]

Depends on / 依赖: EReal.add_sub_cancel_right, add_comm, add_sub_cancel_right
-/
lemma add_sub_cancel_left {a : EReal} {b : Real} : b + a - b = a := by
  rw [add_comm]; rw [EReal.add_sub_cancel_right]

/--
lemma `sub_add_cancel` / 引理 `sub_add_cancel`

English:
lemma sub_add_cancel
  given: {a : EReal} {b : Real}
  statement: a - b + b = a
  proof: by
  rw [add_comm]; rw [← add_sub_assoc]; rw [add_sub_cancel_left]

中文:
引理 sub_add_cancel
  条件: {a : E实数} {b : 实数}
  结论: a - b + b = a
  证明: by
  rw [add_comm]; rw [← add_sub_assoc]; rw [add_sub_cancel_left]

Depends on / 依赖: add_comm, add_sub_assoc, add_sub_cancel_left
-/
lemma sub_add_cancel {a : EReal} {b : Real} : a - b + b = a := by
  rw [add_comm]; rw [← add_sub_assoc]; rw [add_sub_cancel_left]

/--
lemma `sub_add_cancel_right` / 引理 `sub_add_cancel_right`

English:
lemma sub_add_cancel_right
  given: {a : EReal} {b : Real}
  statement: b - (a + b) = -a
  proof: by
  cases a <;> norm_cast
  exact _root_.sub_add_cancel_right _ _

中文:
引理 sub_add_cancel_right
  条件: {a : E实数} {b : 实数}
  结论: b - (a + b) = -a
  证明: by
  cases a <;> norm_cast
  exact _root_.sub_add_cancel_right _ _

Depends on / 依赖: _root_, _root_.sub_add_cancel_right, sub_add_cancel_right
-/
lemma sub_add_cancel_right {a : EReal} {b : Real} : b - (a + b) = -a := by
  cases a <;> norm_cast
  exact _root_.sub_add_cancel_right _ _

/--
lemma `sub_add_cancel_left` / 引理 `sub_add_cancel_left`

English:
lemma sub_add_cancel_left
  given: {a : EReal} {b : Real}
  statement: b - (b + a) = -a
  proof: by
  rw [add_comm]; rw [sub_add_cancel_right]

中文:
引理 sub_add_cancel_left
  条件: {a : E实数} {b : 实数}
  结论: b - (b + a) = -a
  证明: by
  rw [add_comm]; rw [sub_add_cancel_right]

Depends on / 依赖: add_comm, sub_add_cancel_right
-/
lemma sub_add_cancel_left {a : EReal} {b : Real} : b - (b + a) = -a := by
  rw [add_comm]; rw [sub_add_cancel_right]

/--
lemma `le_sub_iff_add_le` / 引理 `le_sub_iff_add_le`

English:
lemma le_sub_iff_add_le
  given: {a b c : EReal} (hb : b != ⊥ ∨ c != ⊥) (ht : b != ⊤ ∨ c != ⊤)
  proof: by
  induction b with
  | bot =>
    simp only [ne_eq, not_true_eq_false, false_or] at hb
    simp only [sub_bot hb, le_top, add_bot, bot_le]
  | coe b =>
    rw [← (addLECancellable_coe b).add_le_add_iff_right]; rw [sub_add_cancel]
  | top =>
    simp only [ne_eq, not_true_eq_false, false_or, sub_t

中文:
引理 le_sub_iff_add_le
  条件: {a b c : E实数} (hb : b != ⊥ ∨ c != ⊥) (ht : b != ⊤ ∨ c != ⊤)
  证明: by
  induction b with
  | bot =>
    simp only [ne_eq, not_true_eq_false, false_or] at hb
    simp only [sub_bot hb, le_top, add_bot, bot_le]
  | coe b =>
    rw [← (addLECancellable_coe b).add_le_add_iff_right]; rw [sub_add_cancel]
  | top =>
    simp only [ne_eq, not_true_eq_false, false_or, sub_t

Depends on / 依赖: Ne.lt_top, addLECancellable_coe, add_bot, add_le_add_iff_right, add_top_iff_ne_bot, bot_add, bot_le, false_or, h.trans_lt, le_bot_iff, le_top, lt_top, ne_eq, not_true_eq_false, sub_add_cancel, sub_bot, sub_top, trans_lt
-/
lemma le_sub_iff_add_le {a b c : EReal} (hb : b != ⊥ ∨ c != ⊥) (ht : b != ⊤ ∨ c != ⊤) :
    a <= c - b ↔ a + b <= c := by
  induction b with
  | bot =>
    simp only [ne_eq, not_true_eq_false, false_or] at hb
    simp only [sub_bot hb, le_top, add_bot, bot_le]
  | coe b =>
    rw [← (addLECancellable_coe b).add_le_add_iff_right]; rw [sub_add_cancel]
  | top =>
    simp only [ne_eq, not_true_eq_false, false_or, sub_top, le_bot_iff] at ht ⊢
    refine ⟨fun h => h ▸ (bot_add ⊤).symm ▸ bot_le, fun h => ?_⟩
    by_contra ha
    exact (h.trans_lt (Ne.lt_top ht)).ne (add_top_iff_ne_bot.2 ha)

/--
lemma `sub_le_iff_le_add` / 引理 `sub_le_iff_le_add`

English:
lemma sub_le_iff_le_add
  given: {a b c : EReal} (h₁ : b != ⊥ ∨ c != ⊤) (h₂ : b != ⊤ ∨ c != ⊥)
  proof: by
  suffices a + (-b) <= c ↔ a <= c - (-b) by simpa [sub_eq_add_neg]
  refine (le_sub_iff_add_le ?_ ?_).symm <;> simpa

中文:
引理 sub_le_iff_le_add
  条件: {a b c : E实数} (h₁ : b != ⊥ ∨ c != ⊤) (h₂ : b != ⊤ ∨ c != ⊥)
  证明: by
  suffices a + (-b) <= c ↔ a <= c - (-b) by simpa [sub_eq_add_neg]
  refine (le_sub_iff_add_le ?_ ?_).symm <;> simpa

Depends on / 依赖: le_sub_iff_add_le, sub_eq_add_neg
-/
lemma sub_le_iff_le_add {a b c : EReal} (h₁ : b != ⊥ ∨ c != ⊤) (h₂ : b != ⊤ ∨ c != ⊥) :
    a - b <= c ↔ a <= c + b := by
  suffices a + (-b) <= c ↔ a <= c - (-b) by simpa [sub_eq_add_neg]
  refine (le_sub_iff_add_le ?_ ?_).symm <;> simpa

/--
theorem `lt_sub_iff_add_lt` / 定理 `lt_sub_iff_add_lt`

English:
theorem lt_sub_iff_add_lt
  given: {a b c : EReal} (h₁ : b != ⊥ ∨ c != ⊤) (h₂ : b != ⊤ ∨ c != ⊥)
  proof: lt_iff_lt_of_le_iff_le (sub_le_iff_le_add h₁ h₂)

中文:
定理 lt_sub_iff_add_lt
  条件: {a b c : E实数} (h₁ : b != ⊥ ∨ c != ⊤) (h₂ : b != ⊤ ∨ c != ⊥)
  证明: lt_iff_lt_of_le_iff_le (sub_le_iff_le_add h₁ h₂)
-/
protected theorem lt_sub_iff_add_lt {a b c : EReal} (h₁ : b != ⊥ ∨ c != ⊤) (h₂ : b != ⊤ ∨ c != ⊥) :
    c < a - b ↔ c + b < a :=
  lt_iff_lt_of_le_iff_le (sub_le_iff_le_add h₁ h₂)

/--
theorem `sub_le_of_le_add` / 定理 `sub_le_of_le_add`

English:
theorem sub_le_of_le_add
  given: {a b c : EReal} (h : a <= b + c)
  statement: a - c <= b
  proof: by
  induction c with
  | bot => rw [add_bot, le_bot_iff] at h; simp only [h, bot_sub, bot_le]
  | coe c => exact (sub_le_iff_le_add (.inl (coe_ne_bot c)) (.inl (coe_ne_top c))).2 h
  | top => simp only [sub_top, bot_le]

中文:
定理 sub_le_of_le_add
  条件: {a b c : E实数} (h : a <= b + c)
  结论: a - c <= b
  证明: by
  induction c with
  | bot => rw [add_bot, le_bot_iff] at h; simp only [h, bot_sub, bot_le]
  | coe c => exact (sub_le_iff_le_add (.inl (coe_ne_bot c)) (.inl (coe_ne_top c))).2 h
  | top => simp only [sub_top, bot_le]

Depends on / 依赖: add_bot, bot_le, bot_sub, coe_ne_bot, coe_ne_top, le_bot_iff, sub_le_iff_le_add, sub_top
-/
theorem sub_le_of_le_add {a b c : EReal} (h : a <= b + c) : a - c <= b := by
  induction c with
  | bot => rw [add_bot, le_bot_iff] at h; simp only [h, bot_sub, bot_le]
  | coe c => exact (sub_le_iff_le_add (.inl (coe_ne_bot c)) (.inl (coe_ne_top c))).2 h
  | top => simp only [sub_top, bot_le]

/--
theorem `sub_le_of_le_add'` / 定理 `sub_le_of_le_add'`

English:
theorem sub_le_of_le_add'
  given: {a b c : EReal} (h : a <= b + c)
  statement: a - b <= c
  proof: sub_le_of_le_add (add_comm b c ▸ h)

中文:
定理 sub_le_of_le_add'
  条件: {a b c : E实数} (h : a <= b + c)
  结论: a - b <= c
  证明: sub_le_of_le_add (add_comm b c ▸ h)

Depends on / 依赖: add_comm, sub_le_of_le_add
-/
theorem sub_le_of_le_add' {a b c : EReal} (h : a <= b + c) : a - b <= c :=
  sub_le_of_le_add (add_comm b c ▸ h)

/--
lemma `add_le_of_le_sub` / 引理 `add_le_of_le_sub`

English:
lemma add_le_of_le_sub
  given: {a b c : EReal} (h : a <= b - c)
  statement: a + c <= b
  proof: by
  rw [← neg_neg c]
  exact sub_le_of_le_add h

中文:
引理 add_le_of_le_sub
  条件: {a b c : E实数} (h : a <= b - c)
  结论: a + c <= b
  证明: by
  rw [← neg_neg c]
  exact sub_le_of_le_add h

Depends on / 依赖: neg_neg, sub_le_of_le_add
-/
lemma add_le_of_le_sub {a b c : EReal} (h : a <= b - c) : a + c <= b := by
  rw [← neg_neg c]
  exact sub_le_of_le_add h

/--
lemma `sub_lt_iff` / 引理 `sub_lt_iff`

English:
lemma sub_lt_iff
  given: {a b c : EReal} (h₁ : b != ⊥ ∨ c != ⊥) (h₂ : b != ⊤ ∨ c != ⊤)
  proof: lt_iff_lt_of_le_iff_le (le_sub_iff_add_le h₁ h₂)

中文:
引理 sub_lt_iff
  条件: {a b c : E实数} (h₁ : b != ⊥ ∨ c != ⊥) (h₂ : b != ⊤ ∨ c != ⊤)
  证明: lt_iff_lt_of_le_iff_le (le_sub_iff_add_le h₁ h₂)

Depends on / 依赖: le_sub_iff_add_le, lt_iff_lt_of_le_iff_le
-/
lemma sub_lt_iff {a b c : EReal} (h₁ : b != ⊥ ∨ c != ⊥) (h₂ : b != ⊤ ∨ c != ⊤) :
    c - b < a ↔ c < a + b :=
  lt_iff_lt_of_le_iff_le (le_sub_iff_add_le h₁ h₂)

/--
lemma `add_lt_of_lt_sub` / 引理 `add_lt_of_lt_sub`

English:
lemma add_lt_of_lt_sub
  given: {a b c : EReal} (h : a < b - c)
  statement: a + c < b
  proof: by
  contrapose! h
  exact sub_le_of_le_add h

中文:
引理 add_lt_of_lt_sub
  条件: {a b c : E实数} (h : a < b - c)
  结论: a + c < b
  证明: by
  contrapose! h
  exact sub_le_of_le_add h

Depends on / 依赖: contrapose, sub_le_of_le_add
-/
lemma add_lt_of_lt_sub {a b c : EReal} (h : a < b - c) : a + c < b := by
  contrapose! h
  exact sub_le_of_le_add h

/--
lemma `sub_lt_of_lt_add` / 引理 `sub_lt_of_lt_add`

English:
lemma sub_lt_of_lt_add
  given: {a b c : EReal} (h : a < b + c)
  statement: a - c < b
  proof: add_lt_of_lt_sub by rwa [sub_eq_add_neg, neg_neg]

中文:
引理 sub_lt_of_lt_add
  条件: {a b c : E实数} (h : a < b + c)
  结论: a - c < b
  证明: add_lt_of_lt_sub by rwa [sub_eq_add_neg, neg_neg]

Depends on / 依赖: add_lt_of_lt_sub, neg_neg, sub_eq_add_neg
-/
lemma sub_lt_of_lt_add {a b c : EReal} (h : a < b + c) : a - c < b :=
add_lt_of_lt_sub by rwa [sub_eq_add_neg, neg_neg]

/--
lemma `sub_lt_of_lt_add'` / 引理 `sub_lt_of_lt_add'`

English:
lemma sub_lt_of_lt_add'
  given: {a b c : EReal} (h : a < b + c)
  statement: a - b < c
  proof: sub_lt_of_lt_add by rwa [add_comm]

中文:
引理 sub_lt_of_lt_add'
  条件: {a b c : E实数} (h : a < b + c)
  结论: a - b < c
  证明: sub_lt_of_lt_add by rwa [add_comm]

Depends on / 依赖: add_comm, sub_lt_of_lt_add
-/
lemma sub_lt_of_lt_add' {a b c : EReal} (h : a < b + c) : a - b < c :=
sub_lt_of_lt_add by rwa [add_comm]

/--
lemma `sub_lt_sub_of_le_of_gt` / 引理 `sub_lt_sub_of_le_of_gt`

English:
lemma sub_lt_sub_of_le_of_gt
  statement: {x y z t : EReal} (h : x <= y) (h' : z < t)
  proof: by
  refine sub_lt_of_lt_add' ?_
  rw [add_sub_assoc']; rw [add_comm]; rw [add_sub_assoc]
  by_cases hy_top : y = ⊤
  · rw [hy_top, top_add_of_ne_bot]
    · exact hx_top.lt_top
    · exact ne_bot_of_le_ne_bot (by simp) (sub_pos.mpr h').le
  by_cases hxy : x = y
  · rw [hxy]
    lift y to Real using 

中文:
引理 sub_lt_sub_of_le_of_gt
  结论: {x y z t : E实数} (h : x <= y) (h' : z < t)
  证明: by
  refine sub_lt_of_lt_add' ?_
  rw [add_sub_assoc']; rw [add_comm]; rw [add_sub_assoc]
  by_cases hy_top : y = ⊤
  · rw [hy_top, top_add_of_ne_bot]
    · exact hx_top.lt_top
    · exact ne_bot_of_le_ne_bot (by simp) (sub_pos.mpr h').le
  by_cases hxy : x = y
  · rw [hxy]
    lift y to Real using 

Depends on / 依赖: EReal.toReal_pos, add_comm, add_sub_assoc, coe_toReal, htz_to, htz_top, hx_top, hx_top.lt_top, hy_bot, hy_top, lt_add_of_pos_right, lt_top, ne_bot_of_le_ne_bot, sub_lt_of_lt_add, sub_pos, sub_pos.mpr, toReal_pos, top_add_of_ne_bot
-/
lemma sub_lt_sub_of_le_of_gt {x y z t : EReal} (h : x <= y) (h' : z < t)
    (hx_top : x != ⊤) (hy_bot : y != ⊥) :
    x - t < y - z := by
  refine sub_lt_of_lt_add' ?_
  rw [add_sub_assoc']; rw [add_comm]; rw [add_sub_assoc]
  by_cases hy_top : y = ⊤
  · rw [hy_top, top_add_of_ne_bot]
    · exact hx_top.lt_top
    · exact ne_bot_of_le_ne_bot (by simp) (sub_pos.mpr h').le
  by_cases hxy : x = y
  · rw [hxy]
    lift y to Real using ⟨hy_top, hy_bot⟩
    by_cases htz_top : t - z = ⊤
    · simp_all
    rw [← coe_toReal htz_top <| ne_bot_of_le_ne_bot (by simp) (sub_pos.mpr h').le]
    norm_cast
    refine lt_add_of_pos_right y ?_
    exact EReal.toReal_pos (sub_pos.mpr h') htz_top
  · rw [← add_zero x]
    exact add_lt_add (by grind) (sub_pos.mpr h')

/-! ### Addition and order -/

set_option backward.isDefEq.respectTransparency false in
/--
lemma `le_of_forall_lt_iff_le` / 引理 `le_of_forall_lt_iff_le`

English:
lemma le_of_forall_lt_iff_le
  given: {x y : EReal}
  statement: (forall z : Real, x < z -> y <= z) ↔ y <= x
  proof: by
  refine ⟨fun h => WithBot.le_of_forall_lt_iff_le.1 ?_, fun h _ x_z => h.trans x_z.le⟩
  rw [WithTop.forall]
  aesop

中文:
引理 le_of_对任意_lt_iff_le
  条件: {x y : E实数}
  结论: (对任意 z : 实数, x < z -> y <= z) ↔ y <= x
  证明: by
  refine ⟨fun h => WithBot.le_of_forall_lt_iff_le.1 ?_, fun h _ x_z => h.trans x_z.le⟩
  rw [WithTop.forall]
  aesop

Depends on / 依赖: WithBot, WithBot.le_of_forall_lt_iff_le, WithTop, WithTop.forall, h.trans, le_of_forall_lt_iff_le, x_z.le
-/
lemma le_of_forall_lt_iff_le {x y : EReal} : (forall z : Real, x < z -> y <= z) ↔ y <= x := by
  refine ⟨fun h => WithBot.le_of_forall_lt_iff_le.1 ?_, fun h _ x_z => h.trans x_z.le⟩
  rw [WithTop.forall]
  aesop

set_option backward.isDefEq.respectTransparency false in
/--
lemma `ge_of_forall_gt_iff_ge` / 引理 `ge_of_forall_gt_iff_ge`

English:
lemma ge_of_forall_gt_iff_ge
  given: {x y : EReal}
  statement: (forall z : Real, z < y -> z <= x) ↔ y <= x
  proof: by
  refine ⟨fun h => WithBot.ge_of_forall_gt_iff_ge.1 ?_, fun h _ x_z => x_z.le.trans h⟩
  rw [WithTop.forall]
  aesop

中文:
引理 ge_of_对任意_gt_iff_ge
  条件: {x y : E实数}
  结论: (对任意 z : 实数, z < y -> z <= x) ↔ y <= x
  证明: by
  refine ⟨fun h => WithBot.ge_of_forall_gt_iff_ge.1 ?_, fun h _ x_z => x_z.le.trans h⟩
  rw [WithTop.forall]
  aesop

Depends on / 依赖: WithBot, WithBot.ge_of_forall_gt_iff_ge, WithTop, WithTop.forall, ge_of_forall_gt_iff_ge, x_z.le.trans
-/
lemma ge_of_forall_gt_iff_ge {x y : EReal} : (forall z : Real, z < y -> z <= x) ↔ y <= x := by
  refine ⟨fun h => WithBot.ge_of_forall_gt_iff_ge.1 ?_, fun h _ x_z => x_z.le.trans h⟩
  rw [WithTop.forall]
  aesop

/--
lemma `exists_lt_add_left` / 引理 `exists_lt_add_left`

English:
lemma exists_lt_add_left
  given: {a b c : EReal} (hc : c < a + b)
  statement: exists a' < a, c < a' + b
  proof: by
  obtain ⟨a', hc', ha'⟩ := exists_between (sub_lt_of_lt_add hc)
  refine ⟨a', ha', (sub_lt_iff (.inl ?_) (.inr hc.ne_top)).1 hc'⟩
  contrapose! hc
  exact hc ▸ (add_bot a).symm ▸ bot_le

中文:
引理 存在_lt_add_left
  条件: {a b c : E实数} (hc : c < a + b)
  结论: 存在 a' < a, c < a' + b
  证明: by
  obtain ⟨a', hc', ha'⟩ := exists_between (sub_lt_of_lt_add hc)
  refine ⟨a', ha', (sub_lt_iff (.inl ?_) (.inr hc.ne_top)).1 hc'⟩
  contrapose! hc
  exact hc ▸ (add_bot a).symm ▸ bot_le
-/
private lemma exists_lt_add_left {a b c : EReal} (hc : c < a + b) : exists a' < a, c < a' + b := by
  obtain ⟨a', hc', ha'⟩ := exists_between (sub_lt_of_lt_add hc)
  refine ⟨a', ha', (sub_lt_iff (.inl ?_) (.inr hc.ne_top)).1 hc'⟩
  contrapose! hc
  exact hc ▸ (add_bot a).symm ▸ bot_le

/--
lemma `exists_lt_add_right` / 引理 `exists_lt_add_right`

English:
lemma exists_lt_add_right
  given: {a b c : EReal} (hc : c < a + b)
  statement: exists b' < b, c < a + b'
  proof: by
  simp_rw [add_comm a] at hc ⊢; exact exists_lt_add_left hc

中文:
引理 存在_lt_add_right
  条件: {a b c : E实数} (hc : c < a + b)
  结论: 存在 b' < b, c < a + b'
  证明: by
  simp_rw [add_comm a] at hc ⊢; exact exists_lt_add_left hc
-/
private lemma exists_lt_add_right {a b c : EReal} (hc : c < a + b) : exists b' < b, c < a + b' := by
  simp_rw [add_comm a] at hc ⊢; exact exists_lt_add_left hc

/--
lemma `add_le_of_forall_lt` / 引理 `add_le_of_forall_lt`

English:
lemma add_le_of_forall_lt
  given: {a b c : EReal} (h : forall a' < a, forall b' < b, a' + b' <= c)
  statement: a + b <= c
  proof: by
  refine le_of_forall_lt_imp_le_of_dense fun d hd => ?_
  obtain ⟨a', ha', hd⟩ := exists_lt_add_left hd
  obtain ⟨b', hb', hd⟩ := exists_lt_add_right hd
  exact hd.le.trans (h _ ha' _ hb')

中文:
引理 add_le_of_对任意_lt
  条件: {a b c : E实数} (h : 对任意 a' < a, 对任意 b' < b, a' + b' <= c)
  结论: a + b <= c
  证明: by
  refine le_of_forall_lt_imp_le_of_dense fun d hd => ?_
  obtain ⟨a', ha', hd⟩ := exists_lt_add_left hd
  obtain ⟨b', hb', hd⟩ := exists_lt_add_right hd
  exact hd.le.trans (h _ ha' _ hb')

Depends on / 依赖: exists_lt_add_left, exists_lt_add_right, hd.le.trans, le_of_forall_lt_imp_le_of_dense
-/
lemma add_le_of_forall_lt {a b c : EReal} (h : forall a' < a, forall b' < b, a' + b' <= c) : a + b <= c := by
  refine le_of_forall_lt_imp_le_of_dense fun d hd => ?_
  obtain ⟨a', ha', hd⟩ := exists_lt_add_left hd
  obtain ⟨b', hb', hd⟩ := exists_lt_add_right hd
  exact hd.le.trans (h _ ha' _ hb')

/--
lemma `le_add_of_forall_gt` / 引理 `le_add_of_forall_gt`

English:
lemma le_add_of_forall_gt
  statement: {a b c : EReal} (h₁ : a != ⊥ ∨ b != ⊤) (h₂ : a != ⊤ ∨ b != ⊥)
  proof: by
  rw [← neg_le_neg_iff]; rw [neg_add h₁ h₂]
  refine add_le_of_forall_lt fun a' ha' b' hb' => EReal.le_neg_of_le_neg ?_
  rw [neg_add (.inr hb'.ne_top) (.inl ha'.ne_top)]
  exact h _ (EReal.lt_neg_of_lt_neg ha') _ (EReal.lt_neg_of_lt_neg hb')

中文:
引理 le_add_of_对任意_gt
  结论: {a b c : E实数} (h₁ : a != ⊥ ∨ b != ⊤) (h₂ : a != ⊤ ∨ b != ⊥)
  证明: by
  rw [← neg_le_neg_iff]; rw [neg_add h₁ h₂]
  refine add_le_of_forall_lt fun a' ha' b' hb' => EReal.le_neg_of_le_neg ?_
  rw [neg_add (.inr hb'.ne_top) (.inl ha'.ne_top)]
  exact h _ (EReal.lt_neg_of_lt_neg ha') _ (EReal.lt_neg_of_lt_neg hb')

Depends on / 依赖: EReal.le_neg_of_le_neg, EReal.lt_neg_of_lt_neg, add_le_of_forall_lt, le_neg_of_le_neg, lt_neg_of_lt_neg, ne_top, neg_add, neg_le_neg_iff
-/
lemma le_add_of_forall_gt {a b c : EReal} (h₁ : a != ⊥ ∨ b != ⊤) (h₂ : a != ⊤ ∨ b != ⊥)
    (h : forall a' > a, forall b' > b, c <= a' + b') : c <= a + b := by
  rw [← neg_le_neg_iff]; rw [neg_add h₁ h₂]
  refine add_le_of_forall_lt fun a' ha' b' hb' => EReal.le_neg_of_le_neg ?_
  rw [neg_add (.inr hb'.ne_top) (.inl ha'.ne_top)]
  exact h _ (EReal.lt_neg_of_lt_neg ha') _ (EReal.lt_neg_of_lt_neg hb')

/--
lemma `_root_.ENNReal.toEReal_sub` / 引理 `_root_.ENNReal.toEReal_sub`

English:
lemma _root_.ENNReal.toEReal_sub
  given: {x y : Real>=0∞} (hy_top : y != ∞) (h_le : y <= x)
  proof: by
  lift y to Real>=0 using hy_top
  cases x with
  | top => simp [coe_nnreal_eq_coe_real]
  | coe x =>
    simp only [coe_nnreal_eq_coe_real, ← ENNReal.coe_sub, NNReal.coe_sub (mod_cast h_le), coe_sub]

中文:
引理 _root_.广义非负实数.toE实数_sub
  条件: {x y : 实数>=0∞} (hy_top : y != ∞) (h_le : y <= x)
  证明: by
  lift y to Real>=0 using hy_top
  cases x with
  | top => simp [coe_nnreal_eq_coe_real]
  | coe x =>
    simp only [coe_nnreal_eq_coe_real, ← ENNReal.coe_sub, NNReal.coe_sub (mod_cast h_le), coe_sub]

Depends on / 依赖: ENNReal, ENNReal.coe_sub, NNReal, NNReal.coe_sub, coe_nnreal_eq_coe_real, coe_sub, h_le, hy_top, mod_cast
-/
lemma _root_.ENNReal.toEReal_sub {x y : Real>=0∞} (hy_top : y != ∞) (h_le : y <= x) :
    (x - y).toEReal = x.toEReal - y.toEReal := by
  lift y to Real>=0 using hy_top
  cases x with
  | top => simp [coe_nnreal_eq_coe_real]
  | coe x =>
    simp only [coe_nnreal_eq_coe_real, ← ENNReal.coe_sub, NNReal.coe_sub (mod_cast h_le), coe_sub]


/--
lemma `top_mul_top` / 引理 `top_mul_top`

English:
lemma top_mul_top
  statement: (⊤ : EReal) * ⊤ = ⊤
  proof: rfl

中文:
引理 top_mul_top
  结论: (⊤ : E实数) * ⊤ = ⊤
  证明: rfl
-/
@[simp] lemma top_mul_top : (⊤ : EReal) * ⊤ = ⊤ := rfl

/--
lemma `top_mul_bot` / 引理 `top_mul_bot`

English:
lemma top_mul_bot
  statement: (⊤ : EReal) * ⊥ = ⊥
  proof: rfl

中文:
引理 top_mul_bot
  结论: (⊤ : E实数) * ⊥ = ⊥
  证明: rfl
-/
@[simp] lemma top_mul_bot : (⊤ : EReal) * ⊥ = ⊥ := rfl

/--
lemma `bot_mul_top` / 引理 `bot_mul_top`

English:
lemma bot_mul_top
  statement: (⊥ : EReal) * ⊤ = ⊥
  proof: rfl

中文:
引理 bot_mul_top
  结论: (⊥ : E实数) * ⊤ = ⊥
  证明: rfl
-/
@[simp] lemma bot_mul_top : (⊥ : EReal) * ⊤ = ⊥ := rfl

/--
lemma `bot_mul_bot` / 引理 `bot_mul_bot`

English:
lemma bot_mul_bot
  statement: (⊥ : EReal) * ⊥ = ⊤
  proof: rfl

中文:
引理 bot_mul_bot
  结论: (⊥ : E实数) * ⊥ = ⊤
  证明: rfl
-/
@[simp] lemma bot_mul_bot : (⊥ : EReal) * ⊥ = ⊤ := rfl

/--
lemma `coe_mul_top_of_pos` / 引理 `coe_mul_top_of_pos`

English:
lemma coe_mul_top_of_pos
  given: {x : Real} (h : 0 < x)
  statement: (x : EReal) * ⊤ = ⊤
  proof: if_pos h

中文:
引理 coe_mul_top_of_pos
  条件: {x : 实数} (h : 0 < x)
  结论: (x : E实数) * ⊤ = ⊤
  证明: if_pos h

Depends on / 依赖: if_pos
-/
lemma coe_mul_top_of_pos {x : Real} (h : 0 < x) : (x : EReal) * ⊤ = ⊤ :=
  if_pos h

/--
lemma `coe_mul_top_of_neg` / 引理 `coe_mul_top_of_neg`

English:
lemma coe_mul_top_of_neg
  given: {x : Real} (h : x < 0)
  statement: (x : EReal) * ⊤ = ⊥
  proof: (if_neg h.not_gt).trans (if_neg h.ne)

中文:
引理 coe_mul_top_of_neg
  条件: {x : 实数} (h : x < 0)
  结论: (x : E实数) * ⊤ = ⊥
  证明: (if_neg h.not_gt).trans (if_neg h.ne)

Depends on / 依赖: h.ne, h.not_gt, if_neg, not_gt
-/
lemma coe_mul_top_of_neg {x : Real} (h : x < 0) : (x : EReal) * ⊤ = ⊥ :=
  (if_neg h.not_gt).trans (if_neg h.ne)

/--
lemma `top_mul_coe_of_pos` / 引理 `top_mul_coe_of_pos`

English:
lemma top_mul_coe_of_pos
  given: {x : Real} (h : 0 < x)
  statement: (⊤ : EReal) * x = ⊤
  proof: if_pos h

中文:
引理 top_mul_coe_of_pos
  条件: {x : 实数} (h : 0 < x)
  结论: (⊤ : E实数) * x = ⊤
  证明: if_pos h

Depends on / 依赖: if_pos
-/
lemma top_mul_coe_of_pos {x : Real} (h : 0 < x) : (⊤ : EReal) * x = ⊤ :=
  if_pos h

/--
lemma `top_mul_coe_of_neg` / 引理 `top_mul_coe_of_neg`

English:
lemma top_mul_coe_of_neg
  given: {x : Real} (h : x < 0)
  statement: (⊤ : EReal) * x = ⊥
  proof: (if_neg h.not_gt).trans (if_neg h.ne)

中文:
引理 top_mul_coe_of_neg
  条件: {x : 实数} (h : x < 0)
  结论: (⊤ : E实数) * x = ⊥
  证明: (if_neg h.not_gt).trans (if_neg h.ne)

Depends on / 依赖: h.ne, h.not_gt, if_neg, not_gt
-/
lemma top_mul_coe_of_neg {x : Real} (h : x < 0) : (⊤ : EReal) * x = ⊥ :=
  (if_neg h.not_gt).trans (if_neg h.ne)

/--
lemma `mul_top_of_pos` / 引理 `mul_top_of_pos`

English:
lemma mul_top_of_pos
  statement: forall {x : EReal}, 0 < x -> x * ⊤ = ⊤

中文:
引理 mul_top_of_pos
  结论: 对任意 {x : E实数}, 0 < x -> x * ⊤ = ⊤
-/
lemma mul_top_of_pos : forall {x : EReal}, 0 < x -> x * ⊤ = ⊤
  | ⊥, h => absurd h not_lt_bot
  | (x : Real), h => coe_mul_top_of_pos (EReal.coe_pos.1 h)
  | ⊤, _ => rfl

/--
lemma `mul_top_of_neg` / 引理 `mul_top_of_neg`

English:
lemma mul_top_of_neg
  statement: forall {x : EReal}, x < 0 -> x * ⊤ = ⊥

中文:
引理 mul_top_of_neg
  结论: 对任意 {x : E实数}, x < 0 -> x * ⊤ = ⊥
-/
lemma mul_top_of_neg : forall {x : EReal}, x < 0 -> x * ⊤ = ⊥
  | ⊥, _ => rfl
  | (x : Real), h => coe_mul_top_of_neg (EReal.coe_neg'.1 h)
  | ⊤, h => absurd h not_top_lt

/--
lemma `top_mul_of_pos` / 引理 `top_mul_of_pos`

English:
lemma top_mul_of_pos
  given: {x : EReal} (h : 0 < x)
  statement: ⊤ * x = ⊤
  proof: by
  rw [EReal.mul_comm]
  exact mul_top_of_pos h

中文:
引理 top_mul_of_pos
  条件: {x : E实数} (h : 0 < x)
  结论: ⊤ * x = ⊤
  证明: by
  rw [EReal.mul_comm]
  exact mul_top_of_pos h

Depends on / 依赖: EReal.mul_comm, mul_comm, mul_top_of_pos
-/
lemma top_mul_of_pos {x : EReal} (h : 0 < x) : ⊤ * x = ⊤ := by
  rw [EReal.mul_comm]
  exact mul_top_of_pos h

/--
lemma `top_mul_of_neg` / 引理 `top_mul_of_neg`

English:
lemma top_mul_of_neg
  given: {x : EReal} (h : x < 0)
  statement: ⊤ * x = ⊥
  proof: by
  rw [EReal.mul_comm]
  exact mul_top_of_neg h

中文:
引理 top_mul_of_neg
  条件: {x : E实数} (h : x < 0)
  结论: ⊤ * x = ⊥
  证明: by
  rw [EReal.mul_comm]
  exact mul_top_of_neg h

Depends on / 依赖: EReal.mul_comm, mul_comm, mul_top_of_neg
-/
lemma top_mul_of_neg {x : EReal} (h : x < 0) : ⊤ * x = ⊥ := by
  rw [EReal.mul_comm]
  exact mul_top_of_neg h

/--
lemma `top_mul_coe_ennreal` / 引理 `top_mul_coe_ennreal`

English:
lemma top_mul_coe_ennreal
  given: {x : Real>=0∞} (hx : x != 0)
  statement: ⊤ * (x : EReal) = ⊤
  proof: top_mul_of_pos coe_ennreal_pos.mpr pos_iff_ne_zero.mpr hx

中文:
引理 top_mul_coe_ennreal
  条件: {x : 实数>=0∞} (hx : x != 0)
  结论: ⊤ * (x : E实数) = ⊤
  证明: top_mul_of_pos coe_ennreal_pos.mpr pos_iff_ne_zero.mpr hx

Depends on / 依赖: coe_ennreal_pos, coe_ennreal_pos.mpr, pos_iff_ne_zero, pos_iff_ne_zero.mpr, top_mul_of_pos
-/
lemma top_mul_coe_ennreal {x : Real>=0∞} (hx : x != 0) : ⊤ * (x : EReal) = ⊤ :=
top_mul_of_pos coe_ennreal_pos.mpr pos_iff_ne_zero.mpr hx

/--
lemma `coe_ennreal_mul_top` / 引理 `coe_ennreal_mul_top`

English:
lemma coe_ennreal_mul_top
  given: {x : Real>=0∞} (hx : x != 0)
  statement: (x : EReal) * ⊤ = ⊤
  proof: by
  rw [EReal.mul_comm]; rw [top_mul_coe_ennreal hx]

中文:
引理 coe_ennreal_mul_top
  条件: {x : 实数>=0∞} (hx : x != 0)
  结论: (x : E实数) * ⊤ = ⊤
  证明: by
  rw [EReal.mul_comm]; rw [top_mul_coe_ennreal hx]

Depends on / 依赖: EReal.mul_comm, mul_comm, top_mul_coe_ennreal
-/
lemma coe_ennreal_mul_top {x : Real>=0∞} (hx : x != 0) : (x : EReal) * ⊤ = ⊤ := by
  rw [EReal.mul_comm]; rw [top_mul_coe_ennreal hx]

/--
lemma `coe_mul_bot_of_pos` / 引理 `coe_mul_bot_of_pos`

English:
lemma coe_mul_bot_of_pos
  given: {x : Real} (h : 0 < x)
  statement: (x : EReal) * ⊥ = ⊥
  proof: if_pos h

中文:
引理 coe_mul_bot_of_pos
  条件: {x : 实数} (h : 0 < x)
  结论: (x : E实数) * ⊥ = ⊥
  证明: if_pos h

Depends on / 依赖: if_pos
-/
lemma coe_mul_bot_of_pos {x : Real} (h : 0 < x) : (x : EReal) * ⊥ = ⊥ :=
  if_pos h

/--
lemma `coe_mul_bot_of_neg` / 引理 `coe_mul_bot_of_neg`

English:
lemma coe_mul_bot_of_neg
  given: {x : Real} (h : x < 0)
  statement: (x : EReal) * ⊥ = ⊤
  proof: (if_neg h.not_gt).trans (if_neg h.ne)

中文:
引理 coe_mul_bot_of_neg
  条件: {x : 实数} (h : x < 0)
  结论: (x : E实数) * ⊥ = ⊤
  证明: (if_neg h.not_gt).trans (if_neg h.ne)

Depends on / 依赖: h.ne, h.not_gt, if_neg, not_gt
-/
lemma coe_mul_bot_of_neg {x : Real} (h : x < 0) : (x : EReal) * ⊥ = ⊤ :=
  (if_neg h.not_gt).trans (if_neg h.ne)

/--
lemma `bot_mul_coe_of_pos` / 引理 `bot_mul_coe_of_pos`

English:
lemma bot_mul_coe_of_pos
  given: {x : Real} (h : 0 < x)
  statement: (⊥ : EReal) * x = ⊥
  proof: if_pos h

中文:
引理 bot_mul_coe_of_pos
  条件: {x : 实数} (h : 0 < x)
  结论: (⊥ : E实数) * x = ⊥
  证明: if_pos h

Depends on / 依赖: if_pos
-/
lemma bot_mul_coe_of_pos {x : Real} (h : 0 < x) : (⊥ : EReal) * x = ⊥ :=
  if_pos h

/--
lemma `bot_mul_coe_of_neg` / 引理 `bot_mul_coe_of_neg`

English:
lemma bot_mul_coe_of_neg
  given: {x : Real} (h : x < 0)
  statement: (⊥ : EReal) * x = ⊤
  proof: (if_neg h.not_gt).trans (if_neg h.ne)

中文:
引理 bot_mul_coe_of_neg
  条件: {x : 实数} (h : x < 0)
  结论: (⊥ : E实数) * x = ⊤
  证明: (if_neg h.not_gt).trans (if_neg h.ne)

Depends on / 依赖: h.ne, h.not_gt, if_neg, not_gt
-/
lemma bot_mul_coe_of_neg {x : Real} (h : x < 0) : (⊥ : EReal) * x = ⊤ :=
  (if_neg h.not_gt).trans (if_neg h.ne)

/--
lemma `mul_bot_of_pos` / 引理 `mul_bot_of_pos`

English:
lemma mul_bot_of_pos
  statement: forall {x : EReal}, 0 < x -> x * ⊥ = ⊥

中文:
引理 mul_bot_of_pos
  结论: 对任意 {x : E实数}, 0 < x -> x * ⊥ = ⊥
-/
lemma mul_bot_of_pos : forall {x : EReal}, 0 < x -> x * ⊥ = ⊥
  | ⊥, h => absurd h not_lt_bot
  | (x : Real), h => coe_mul_bot_of_pos (EReal.coe_pos.1 h)
  | ⊤, _ => rfl

/--
lemma `mul_bot_of_neg` / 引理 `mul_bot_of_neg`

English:
lemma mul_bot_of_neg
  statement: forall {x : EReal}, x < 0 -> x * ⊥ = ⊤

中文:
引理 mul_bot_of_neg
  结论: 对任意 {x : E实数}, x < 0 -> x * ⊥ = ⊤
-/
lemma mul_bot_of_neg : forall {x : EReal}, x < 0 -> x * ⊥ = ⊤
  | ⊥, _ => rfl
  | (x : Real), h => coe_mul_bot_of_neg (EReal.coe_neg'.1 h)
  | ⊤, h => absurd h not_top_lt

/--
lemma `bot_mul_of_pos` / 引理 `bot_mul_of_pos`

English:
lemma bot_mul_of_pos
  given: {x : EReal} (h : 0 < x)
  statement: ⊥ * x = ⊥
  proof: by
  rw [EReal.mul_comm]
  exact mul_bot_of_pos h

中文:
引理 bot_mul_of_pos
  条件: {x : E实数} (h : 0 < x)
  结论: ⊥ * x = ⊥
  证明: by
  rw [EReal.mul_comm]
  exact mul_bot_of_pos h

Depends on / 依赖: EReal.mul_comm, mul_bot_of_pos, mul_comm
-/
lemma bot_mul_of_pos {x : EReal} (h : 0 < x) : ⊥ * x = ⊥ := by
  rw [EReal.mul_comm]
  exact mul_bot_of_pos h

/--
lemma `bot_mul_of_neg` / 引理 `bot_mul_of_neg`

English:
lemma bot_mul_of_neg
  given: {x : EReal} (h : x < 0)
  statement: ⊥ * x = ⊤
  proof: by
  rw [EReal.mul_comm]
  exact mul_bot_of_neg h

中文:
引理 bot_mul_of_neg
  条件: {x : E实数} (h : x < 0)
  结论: ⊥ * x = ⊤
  证明: by
  rw [EReal.mul_comm]
  exact mul_bot_of_neg h

Depends on / 依赖: EReal.mul_comm, mul_bot_of_neg, mul_comm
-/
lemma bot_mul_of_neg {x : EReal} (h : x < 0) : ⊥ * x = ⊤ := by
  rw [EReal.mul_comm]
  exact mul_bot_of_neg h

/--
lemma `toReal_mul` / 引理 `toReal_mul`

English:
lemma toReal_mul
  given: {x y : EReal}
  statement: toReal (x * y) = toReal x * toReal y
  proof: by
  induction x, y using induction₂_symm with
  | top_zero | zero_bot | top_top | top_bot | bot_bot => simp
  | symm h => rwa [mul_comm, EReal.mul_comm]
  | coe_coe => norm_cast
  | top_pos _ h => simp [top_mul_coe_of_pos h]
  | top_neg _ h => simp [top_mul_coe_of_neg h]
  | pos_bot _ h => simp [co

中文:
引理 to实数_mul
  条件: {x y : E实数}
  结论: to实数 (x * y) = to实数 x * to实数 y
  证明: by
  induction x, y using induction₂_symm with
  | top_zero | zero_bot | top_top | top_bot | bot_bot => simp
  | symm h => rwa [mul_comm, EReal.mul_comm]
  | coe_coe => norm_cast
  | top_pos _ h => simp [top_mul_coe_of_pos h]
  | top_neg _ h => simp [top_mul_coe_of_neg h]
  | pos_bot _ h => simp [co

Depends on / 依赖: EReal.mul_comm, bot_bot, coe_coe, coe_mul_bot_of_neg, coe_mul_bot_of_pos, mul_comm, neg_bot, pos_bot, top_bot, top_mul_coe_of_neg, top_mul_coe_of_pos, top_neg, top_pos, top_top, top_zero, zero_bot
-/
lemma toReal_mul {x y : EReal} : toReal (x * y) = toReal x * toReal y := by
  induction x, y using induction₂_symm with
  | top_zero | zero_bot | top_top | top_bot | bot_bot => simp
  | symm h => rwa [mul_comm, EReal.mul_comm]
  | coe_coe => norm_cast
  | top_pos _ h => simp [top_mul_coe_of_pos h]
  | top_neg _ h => simp [top_mul_coe_of_neg h]
  | pos_bot _ h => simp [coe_mul_bot_of_pos h]
  | neg_bot _ h => simp [coe_mul_bot_of_neg h]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NoZeroDivisors EReal
  body: by
    intro a b h
    contrapose! h
    cases a <;> cases b <;> try {· simp_all [← EReal.coe_mul]}
    · rcases lt_or_gt_of_ne h.2 with (h | h)
        <;> simp [EReal.bot_mul_of_neg, EReal.bot_mul_of_pos, h]
    · rcases lt_or_gt_of_ne h.1 with (h | h)
        <;> simp [EReal.mul_bot_of_pos, EReal

中文:
实例 :
  签名: 无零因子 E实数
  定义体: by
    intro a b h
    contrapose! h
    cases a <;> cases b <;> try {· simp_all [← EReal.coe_mul]}
    · rcases lt_or_gt_of_ne h.2 with (h | h)
        <;> simp [EReal.bot_mul_of_neg, EReal.bot_mul_of_pos, h]
    · rcases lt_or_gt_of_ne h.1 with (h | h)
        <;> simp [EReal.mul_bot_of_pos, EReal

Depends on / 依赖: EReal.bot_mul_of_neg, EReal.bot_mul_of_pos, EReal.coe_mul, EReal.mul_bot_of_neg, EReal.mul_bot_of_pos, EReal.mul_top_of_neg, EReal.mul_top_of_pos, EReal.top_mul_of_neg, EReal.top_mul_of_pos, bot_mul_of_neg, bot_mul_of_pos, coe_mul, contrapose, lt_or_gt_of_ne, mul_bot_of_neg, mul_bot_of_pos, mul_top_of_neg, mul_top_of_pos, top_mul_of_neg, top_mul_of_pos
-/
instance : NoZeroDivisors EReal where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    intro a b h
    contrapose! h
    cases a <;> cases b <;> try {· simp_all [← EReal.coe_mul]}
    · rcases lt_or_gt_of_ne h.2 with (h | h)
        <;> simp [EReal.bot_mul_of_neg, EReal.bot_mul_of_pos, h]
    · rcases lt_or_gt_of_ne h.1 with (h | h)
        <;> simp [EReal.mul_bot_of_pos, EReal.mul_bot_of_neg, h]
    · rcases lt_or_gt_of_ne h.1 with (h | h)
        <;> simp [EReal.mul_top_of_neg, EReal.mul_top_of_pos, h]
    · rcases lt_or_gt_of_ne h.2 with (h | h)
        <;> simp [EReal.top_mul_of_pos, EReal.top_mul_of_neg, h]

/--
lemma `mul_pos_iff` / 引理 `mul_pos_iff`

English:
lemma mul_pos_iff
  given: {a b : EReal}
  statement: 0 < a * b ↔ 0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0
  proof: by
  induction a, b using EReal.induction₂_symm with
  | symm h => simp [EReal.mul_comm, h, and_comm]
  | top_top => simp
  | top_pos _ hx => simp [EReal.top_mul_coe_of_pos hx, hx]
  | top_zero => simp
  | top_neg _ hx => simp [hx, EReal.top_mul_coe_of_neg hx, le_of_lt]
  | top_bot => simp
  | pos_b

中文:
引理 mul_pos_iff
  条件: {a b : E实数}
  结论: 0 < a * b ↔ 0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0
  证明: by
  induction a, b using EReal.induction₂_symm with
  | symm h => simp [EReal.mul_comm, h, and_comm]
  | top_top => simp
  | top_pos _ hx => simp [EReal.top_mul_coe_of_pos hx, hx]
  | top_zero => simp
  | top_neg _ hx => simp [hx, EReal.top_mul_coe_of_neg hx, le_of_lt]
  | top_bot => simp
  | pos_b

Depends on / 依赖: EReal.coe_mul_bot_of_neg, EReal.coe_mul_bot_of_pos, EReal.induction, EReal.mul_comm, EReal.top_mul_coe_of_neg, EReal.top_mul_coe_of_pos, _root_, _root_.mul_pos_iff, and_comm, bot_bot, coe_coe, coe_mul, coe_mul_bot_of_neg, coe_mul_bot_of_pos, le_of_lt, mul_comm, mul_pos_iff, neg_bot, pos_bot, top_bot
-/
lemma mul_pos_iff {a b : EReal} : 0 < a * b ↔ 0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 := by
  induction a, b using EReal.induction₂_symm with
  | symm h => simp [EReal.mul_comm, h, and_comm]
  | top_top => simp
  | top_pos _ hx => simp [EReal.top_mul_coe_of_pos hx, hx]
  | top_zero => simp
  | top_neg _ hx => simp [hx, EReal.top_mul_coe_of_neg hx, le_of_lt]
  | top_bot => simp
  | pos_bot _ hx => simp [hx, EReal.coe_mul_bot_of_pos hx, le_of_lt]
  | coe_coe x y => simp [← coe_mul, _root_.mul_pos_iff]
  | zero_bot => simp
  | neg_bot _ hx => simp [hx, EReal.coe_mul_bot_of_neg hx]
  | bot_bot => simp

/--
lemma `mul_nonneg_iff` / 引理 `mul_nonneg_iff`

English:
lemma mul_nonneg_iff
  given: {a b : EReal}
  statement: 0 <= a * b ↔ 0 <= a ∧ 0 <= b ∨ a <= 0 ∧ b <= 0
  proof: by
  simp_rw [le_iff_lt_or_eq, mul_pos_iff, zero_eq_mul (a := a)]
  rcases lt_trichotomy a 0 with (h | h | h) <;> rcases lt_trichotomy b 0 with (h' | h' | h')
    <;> simp only [h, h', true_or, true_and, or_true, and_true] <;> tauto

中文:
引理 mul_nonneg_iff
  条件: {a b : E实数}
  结论: 0 <= a * b ↔ 0 <= a ∧ 0 <= b ∨ a <= 0 ∧ b <= 0
  证明: by
  simp_rw [le_iff_lt_or_eq, mul_pos_iff, zero_eq_mul (a := a)]
  rcases lt_trichotomy a 0 with (h | h | h) <;> rcases lt_trichotomy b 0 with (h' | h' | h')
    <;> simp only [h, h', true_or, true_and, or_true, and_true] <;> tauto

Depends on / 依赖: and_true, le_iff_lt_or_eq, lt_trichotomy, mul_pos_iff, or_true, simp_rw, true_and, true_or, zero_eq_mul
-/
lemma mul_nonneg_iff {a b : EReal} : 0 <= a * b ↔ 0 <= a ∧ 0 <= b ∨ a <= 0 ∧ b <= 0 := by
  simp_rw [le_iff_lt_or_eq, mul_pos_iff, zero_eq_mul (a := a)]
  rcases lt_trichotomy a 0 with (h | h | h) <;> rcases lt_trichotomy b 0 with (h' | h' | h')
    <;> simp only [h, h', true_or, true_and, or_true, and_true] <;> tauto

/--
lemma `mul_nonneg` / 引理 `mul_nonneg`

English:
lemma mul_nonneg
  given: {a b : EReal} (ha : 0 <= a) (hb : 0 <= b)
  statement: 0 <= a * b
  proof: mul_nonneg_iff.mpr .inl ⟨ha, hb⟩

中文:
引理 mul_nonneg
  条件: {a b : E实数} (ha : 0 <= a) (hb : 0 <= b)
  结论: 0 <= a * b
  证明: mul_nonneg_iff.mpr .inl ⟨ha, hb⟩
-/
protected lemma mul_nonneg {a b : EReal} (ha : 0 <= a) (hb : 0 <= b) : 0 <= a * b :=
mul_nonneg_iff.mpr .inl ⟨ha, hb⟩

/--
lemma `mul_pos` / 引理 `mul_pos`

English:
lemma mul_pos
  given: {a b : EReal} (ha : 0 < a) (hb : 0 < b)
  statement: 0 < a * b
  proof: mul_pos_iff.mpr (Or.inl ⟨ha, hb⟩)

中文:
引理 mul_pos
  条件: {a b : E实数} (ha : 0 < a) (hb : 0 < b)
  结论: 0 < a * b
  证明: mul_pos_iff.mpr (Or.inl ⟨ha, hb⟩)
-/
protected lemma mul_pos {a b : EReal} (ha : 0 < a) (hb : 0 < b) : 0 < a * b :=
  mul_pos_iff.mpr (Or.inl ⟨ha, hb⟩)

/-- Induct on two ereals by performing case splits on the sign of one whenever the other is
infinite. This version eliminates some cases by assuming that `P x y` implies `P (-x) y` for all
`x`, `y`. -/
@[elab_as_elim]
/--
lemma `induction₂_neg_left` / 引理 `induction₂_neg_left`

English:
lemma induction₂_neg_left
  statement: {P : EReal -> EReal -> Prop} (neg_left : forall {x y}, P x y -> P (-x) y)
  proof: have : forall y, (forall x : Real, 0 < x -> P x y) -> forall x : Real, x < 0 -> P x y := fun _ h x hx =>
neg_neg (x : EReal) ▸ neg_left h _ (neg_pos_of_neg hx)
  @induction₂ P top_top top_pos top_zero top_neg top_bot pos_top pos_bot zero_top
    coe_coe zero_bot (this _ pos_top) (this _ pos_bot) (ne

中文:
引理 induction₂_neg_left
  结论: {P : E实数 -> E实数 -> 命题} (neg_left : 对任意 {x y}, P x y -> P (-x) y)
  证明: have : forall y, (forall x : Real, 0 < x -> P x y) -> forall x : Real, x < 0 -> P x y := fun _ h x hx =>
neg_neg (x : EReal) ▸ neg_left h _ (neg_pos_of_neg hx)
  @induction₂ P top_top top_pos top_zero top_neg top_bot pos_top pos_bot zero_top
    coe_coe zero_bot (this _ pos_top) (this _ pos_bot) (ne

Depends on / 依赖: coe_coe, neg_left, neg_neg, neg_pos_of_neg, pos_bot, pos_top, top_bot, top_neg, top_pos, top_top, top_zero, zero_bot, zero_top
-/
lemma induction₂_neg_left {P : EReal -> EReal -> Prop} (neg_left : forall {x y}, P x y -> P (-x) y)
    (top_top : P ⊤ ⊤) (top_pos : forall x : Real, 0 < x -> P ⊤ x)
    (top_zero : P ⊤ 0) (top_neg : forall x : Real, x < 0 -> P ⊤ x) (top_bot : P ⊤ ⊥)
    (zero_top : P 0 ⊤) (zero_bot : P 0 ⊥)
    (pos_top : forall x : Real, 0 < x -> P x ⊤) (pos_bot : forall x : Real, 0 < x -> P x ⊥)
    (coe_coe : forall x y : Real, P x y) : forall x y, P x y :=
  have : forall y, (forall x : Real, 0 < x -> P x y) -> forall x : Real, x < 0 -> P x y := fun _ h x hx =>
neg_neg (x : EReal) ▸ neg_left h _ (neg_pos_of_neg hx)
  @induction₂ P top_top top_pos top_zero top_neg top_bot pos_top pos_bot zero_top
    coe_coe zero_bot (this _ pos_top) (this _ pos_bot) (neg_left top_top)
    (fun x hx => neg_left <| top_pos x hx) (neg_left top_zero)
    (fun x hx => neg_left <| top_neg x hx) (neg_left top_bot)

/-- Induct on two ereals by performing case splits on the sign of one whenever the other is
infinite. This version eliminates some cases by assuming that `P` is symmetric and `P x y` implies
`P (-x) y` for all `x`, `y`. -/
@[elab_as_elim]
/--
lemma `induction₂_symm_neg` / 引理 `induction₂_symm_neg`

English:
lemma induction₂_symm_neg
  statement: {P : EReal -> EReal -> Prop}
  proof: have neg_right : forall {x y}, P x y -> P x (-y) := fun h => symm neg_left symm h
  have : forall x, (forall y : Real, 0 < y -> P x y) -> forall y : Real, y < 0 -> P x y := fun _ h y hy =>
    neg_neg (y : EReal) ▸ neg_right (h _ (neg_pos_of_neg hy))
  @induction₂_neg_left P neg_left top_top top_pos

中文:
引理 induction₂_symm_neg
  结论: {P : E实数 -> E实数 -> 命题}
  证明: have neg_right : forall {x y}, P x y -> P x (-y) := fun h => symm neg_left symm h
  have : forall x, (forall y : Real, 0 < y -> P x y) -> forall y : Real, y < 0 -> P x y := fun _ h y hy =>
    neg_neg (y : EReal) ▸ neg_right (h _ (neg_pos_of_neg hy))
  @induction₂_neg_left P neg_left top_top top_pos

Depends on / 依赖: coe_coe, neg_left, neg_neg, neg_pos_of_neg, neg_right, top_pos, top_top, top_zero
-/
lemma induction₂_symm_neg {P : EReal -> EReal -> Prop}
    (symm : forall {x y}, P x y -> P y x)
    (neg_left : forall {x y}, P x y -> P (-x) y) (top_top : P ⊤ ⊤)
    (top_pos : forall x : Real, 0 < x -> P ⊤ x) (top_zero : P ⊤ 0) (coe_coe : forall x y : Real, P x y) :
    forall x y, P x y :=
have neg_right : forall {x y}, P x y -> P x (-y) := fun h => symm neg_left symm h
  have : forall x, (forall y : Real, 0 < y -> P x y) -> forall y : Real, y < 0 -> P x y := fun _ h y hy =>
    neg_neg (y : EReal) ▸ neg_right (h _ (neg_pos_of_neg hy))
  @induction₂_neg_left P neg_left top_top top_pos top_zero (this _ top_pos) (neg_right top_top)
    (symm top_zero) (symm <| neg_left top_zero) (fun x hx => symm <| top_pos x hx)
    (fun x hx => symm <| neg_left <| top_pos x hx) coe_coe

/--
lemma `neg_mul` / 引理 `neg_mul`

English:
lemma neg_mul
  given: (x y : EReal)
  statement: -x * y = -(x * y)
  proof: by
  induction x, y using induction₂_neg_left with
  | top_zero | zero_top | zero_bot => simp only [zero_mul, mul_zero, neg_zero]
  | top_top | top_bot => rfl
  | neg_left h => rw [h, neg_neg, neg_neg]
  | coe_coe => norm_cast; exact neg_mul _ _
  | top_pos _ h => rw [top_mul_coe_of_pos h, neg_top, 

中文:
引理 neg_mul
  条件: (x y : E实数)
  结论: -x * y = -(x * y)
  证明: by
  induction x, y using induction₂_neg_left with
  | top_zero | zero_top | zero_bot => simp only [zero_mul, mul_zero, neg_zero]
  | top_top | top_bot => rfl
  | neg_left h => rw [h, neg_neg, neg_neg]
  | coe_coe => norm_cast; exact neg_mul _ _
  | top_pos _ h => rw [top_mul_coe_of_pos h, neg_top, 
-/
protected lemma neg_mul (x y : EReal) : -x * y = -(x * y) := by
  induction x, y using induction₂_neg_left with
  | top_zero | zero_top | zero_bot => simp only [zero_mul, mul_zero, neg_zero]
  | top_top | top_bot => rfl
  | neg_left h => rw [h, neg_neg, neg_neg]
  | coe_coe => norm_cast; exact neg_mul _ _
  | top_pos _ h => rw [top_mul_coe_of_pos h, neg_top, bot_mul_coe_of_pos h]
  | pos_top _ h => rw [coe_mul_top_of_pos h, neg_top, ← coe_neg,
    coe_mul_top_of_neg (neg_neg_of_pos h)]
  | top_neg _ h => rw [top_mul_coe_of_neg h, neg_top, bot_mul_coe_of_neg h, neg_bot]
  | pos_bot _ h => rw [coe_mul_bot_of_pos h, neg_bot, ← coe_neg,
    coe_mul_bot_of_neg (neg_neg_of_pos h)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasDistribNeg EReal
  body: EReal.neg_mul
  mul_neg := fun x y => by
    rw [x.mul_comm]; rw [x.mul_comm]
    exact y.neg_mul x

中文:
实例 :
  签名: 有DistribNeg E实数
  定义体: EReal.neg_mul
  mul_neg := fun x y => by
    rw [x.mul_comm]; rw [x.mul_comm]
    exact y.neg_mul x

Depends on / 依赖: EReal.neg_mul, neg_mul
-/
instance : HasDistribNeg EReal where
  neg_mul := EReal.neg_mul
  mul_neg := fun x y => by
    rw [x.mul_comm]; rw [x.mul_comm]
    exact y.neg_mul x

/--
lemma `mul_neg_iff` / 引理 `mul_neg_iff`

English:
lemma mul_neg_iff
  given: {a b : EReal}
  statement: a * b < 0 ↔ 0 < a ∧ b < 0 ∨ a < 0 ∧ 0 < b
  proof: by
  nth_rw 1 [← neg_zero]
  rw [lt_neg_comm]; rw [← mul_neg a]; rw [mul_pos_iff]; rw [neg_lt_comm]; rw [lt_neg_comm]; rw [neg_zero]

中文:
引理 mul_neg_iff
  条件: {a b : E实数}
  结论: a * b < 0 ↔ 0 < a ∧ b < 0 ∨ a < 0 ∧ 0 < b
  证明: by
  nth_rw 1 [← neg_zero]
  rw [lt_neg_comm]; rw [← mul_neg a]; rw [mul_pos_iff]; rw [neg_lt_comm]; rw [lt_neg_comm]; rw [neg_zero]

Depends on / 依赖: lt_neg_comm, mul_neg, mul_pos_iff, neg_lt_comm, neg_zero, nth_rw
-/
lemma mul_neg_iff {a b : EReal} : a * b < 0 ↔ 0 < a ∧ b < 0 ∨ a < 0 ∧ 0 < b := by
  nth_rw 1 [← neg_zero]
  rw [lt_neg_comm]; rw [← mul_neg a]; rw [mul_pos_iff]; rw [neg_lt_comm]; rw [lt_neg_comm]; rw [neg_zero]

/--
lemma `mul_nonpos_iff` / 引理 `mul_nonpos_iff`

English:
lemma mul_nonpos_iff
  given: {a b : EReal}
  statement: a * b <= 0 ↔ 0 <= a ∧ b <= 0 ∨ a <= 0 ∧ 0 <= b
  proof: by
  nth_rw 1 [← neg_zero]
  rw [EReal.le_neg]; rw [← mul_neg]; rw [mul_nonneg_iff]; rw [EReal.neg_le]; rw [EReal.le_neg]; rw [neg_zero]

中文:
引理 mul_nonpos_iff
  条件: {a b : E实数}
  结论: a * b <= 0 ↔ 0 <= a ∧ b <= 0 ∨ a <= 0 ∧ 0 <= b
  证明: by
  nth_rw 1 [← neg_zero]
  rw [EReal.le_neg]; rw [← mul_neg]; rw [mul_nonneg_iff]; rw [EReal.neg_le]; rw [EReal.le_neg]; rw [neg_zero]

Depends on / 依赖: EReal.le_neg, EReal.neg_le, le_neg, mul_neg, mul_nonneg_iff, neg_le, neg_zero, nth_rw
-/
lemma mul_nonpos_iff {a b : EReal} : a * b <= 0 ↔ 0 <= a ∧ b <= 0 ∨ a <= 0 ∧ 0 <= b := by
  nth_rw 1 [← neg_zero]
  rw [EReal.le_neg]; rw [← mul_neg]; rw [mul_nonneg_iff]; rw [EReal.neg_le]; rw [EReal.le_neg]; rw [neg_zero]

/--
lemma `mul_eq_top` / 引理 `mul_eq_top`

English:
lemma mul_eq_top
  given: (a b : EReal)
  proof: by
  induction a, b using EReal.induction₂_symm with
  | symm h => grind [EReal.mul_comm]
  | top_top => simp
  | top_pos _ hx => simp [EReal.top_mul_coe_of_pos hx, hx]
  | top_zero => simp
  | top_neg _ hx => simp [hx.le, EReal.top_mul_coe_of_neg hx]
  | top_bot => simp
  | pos_bot _ hx => simp [hx

中文:
引理 mul_eq_top
  条件: (a b : E实数)
  证明: by
  induction a, b using EReal.induction₂_symm with
  | symm h => grind [EReal.mul_comm]
  | top_top => simp
  | top_pos _ hx => simp [EReal.top_mul_coe_of_pos hx, hx]
  | top_zero => simp
  | top_neg _ hx => simp [hx.le, EReal.top_mul_coe_of_neg hx]
  | top_bot => simp
  | pos_bot _ hx => simp [hx

Depends on / 依赖: EReal.coe_mul, EReal.coe_mul_bot_of_pos, EReal.coe_ne_bot, EReal.coe_ne_top, EReal.coe_neg, EReal.coe_pos, EReal.induction, EReal.mul_comm, EReal.top_mul_coe_of_neg, EReal.top_mul_coe_of_pos, and_false, coe_coe, coe_mul, coe_mul_bot_of_pos, coe_ne_bot, coe_ne_top, coe_neg, coe_pos, false_and, hx.le
-/
lemma mul_eq_top (a b : EReal) :
    a * b = ⊤ ↔ (a = ⊥ ∧ b < 0) ∨ (a < 0 ∧ b = ⊥) ∨ (a = ⊤ ∧ 0 < b) ∨ (0 < a ∧ b = ⊤) := by
  induction a, b using EReal.induction₂_symm with
  | symm h => grind [EReal.mul_comm]
  | top_top => simp
  | top_pos _ hx => simp [EReal.top_mul_coe_of_pos hx, hx]
  | top_zero => simp
  | top_neg _ hx => simp [hx.le, EReal.top_mul_coe_of_neg hx]
  | top_bot => simp
  | pos_bot _ hx => simp [hx.le, EReal.coe_mul_bot_of_pos hx]
  | coe_coe x y =>
    simpa only [EReal.coe_ne_bot, EReal.coe_neg', false_and, and_false, EReal.coe_ne_top,
      EReal.coe_pos, or_self, iff_false, EReal.coe_mul] using! EReal.coe_ne_top _
  | zero_bot => simp
  | neg_bot _ hx => simp [hx, EReal.coe_mul_bot_of_neg hx]
  | bot_bot => simp

/--
lemma `mul_ne_top` / 引理 `mul_ne_top`

English:
lemma mul_ne_top
  given: (a b : EReal)
  proof: by
  rw [ne_eq]; rw [mul_eq_top]
  -- push the negation while keeping the disjunctions, that is converting `¬(p ∧ q)` into `¬p ∨ ¬q`
  -- rather than `p → ¬q`, since we already have disjunctions in the rhs
  push +distrib Not
  rfl

中文:
引理 mul_ne_top
  条件: (a b : E实数)
  证明: by
  rw [ne_eq]; rw [mul_eq_top]
  -- push the negation while keeping the disjunctions, that is converting `¬(p ∧ q)` into `¬p ∨ ¬q`
  -- rather than `p → ¬q`, since we already have disjunctions in the rhs
  push +distrib Not
  rfl

Depends on / 依赖: mul_eq_top, ne_eq
-/
lemma mul_ne_top (a b : EReal) :
    a * b != ⊤ ↔ (a != ⊥ ∨ 0 <= b) ∧ (0 <= a ∨ b != ⊥) ∧ (a != ⊤ ∨ b <= 0) ∧ (a <= 0 ∨ b != ⊤) := by
  rw [ne_eq]; rw [mul_eq_top]
  -- push the negation while keeping the disjunctions, that is converting `¬(p ∧ q)` into `¬p ∨ ¬q`
  -- rather than `p → ¬q`, since we already have disjunctions in the rhs
  push +distrib Not
  rfl

/--
lemma `mul_eq_bot` / 引理 `mul_eq_bot`

English:
lemma mul_eq_bot
  given: (a b : EReal)
  proof: by
  rw [← neg_eq_top_iff]; rw [← EReal.neg_mul]; rw [mul_eq_top]; rw [neg_eq_bot_iff]; rw [neg_eq_top_iff]; rw [neg_lt_comm]; rw [lt_neg_comm]; rw [neg_zero]
  tauto

中文:
引理 mul_eq_bot
  条件: (a b : E实数)
  证明: by
  rw [← neg_eq_top_iff]; rw [← EReal.neg_mul]; rw [mul_eq_top]; rw [neg_eq_bot_iff]; rw [neg_eq_top_iff]; rw [neg_lt_comm]; rw [lt_neg_comm]; rw [neg_zero]
  tauto

Depends on / 依赖: EReal.neg_mul, lt_neg_comm, mul_eq_top, neg_eq_bot_iff, neg_eq_top_iff, neg_lt_comm, neg_mul, neg_zero
-/
lemma mul_eq_bot (a b : EReal) :
    a * b = ⊥ ↔ (a = ⊥ ∧ 0 < b) ∨ (0 < a ∧ b = ⊥) ∨ (a = ⊤ ∧ b < 0) ∨ (a < 0 ∧ b = ⊤) := by
  rw [← neg_eq_top_iff]; rw [← EReal.neg_mul]; rw [mul_eq_top]; rw [neg_eq_bot_iff]; rw [neg_eq_top_iff]; rw [neg_lt_comm]; rw [lt_neg_comm]; rw [neg_zero]
  tauto

/--
lemma `mul_ne_bot` / 引理 `mul_ne_bot`

English:
lemma mul_ne_bot
  given: (a b : EReal)
  proof: by
  rw [ne_eq]; rw [mul_eq_bot]
  push +distrib Not
  rfl

中文:
引理 mul_ne_bot
  条件: (a b : E实数)
  证明: by
  rw [ne_eq]; rw [mul_eq_bot]
  push +distrib Not
  rfl

Depends on / 依赖: distrib, mul_eq_bot, ne_eq
-/
lemma mul_ne_bot (a b : EReal) :
    a * b != ⊥ ↔ (a != ⊥ ∨ b <= 0) ∧ (a <= 0 ∨ b != ⊥) ∧ (a != ⊤ ∨ 0 <= b) ∧ (0 <= a ∨ b != ⊤) := by
  rw [ne_eq]; rw [mul_eq_bot]
  push +distrib Not
  rfl

/--
lemma `toENNReal_mul` / 引理 `toENNReal_mul`

English:
lemma toENNReal_mul
  given: {x y : EReal} (hx : 0 <= x)
  proof: by
  induction x <;> induction y
    <;> try {· simp_all [mul_nonpos_iff, ofReal_mul, ← coe_mul]}
  · rcases eq_or_lt_of_le hx with (hx | hx)
    · simp [← hx]
    · simp_all [mul_top_of_pos hx]
  · rename_i a
    rcases lt_trichotomy a 0 with (ha | ha | ha)
    · simp_all [le_of_lt, top_mul_of_neg 

中文:
引理 toENN实数_mul
  条件: {x y : E实数} (hx : 0 <= x)
  证明: by
  induction x <;> induction y
    <;> try {· simp_all [mul_nonpos_iff, ofReal_mul, ← coe_mul]}
  · rcases eq_or_lt_of_le hx with (hx | hx)
    · simp [← hx]
    · simp_all [mul_top_of_pos hx]
  · rename_i a
    rcases lt_trichotomy a 0 with (ha | ha | ha)
    · simp_all [le_of_lt, top_mul_of_neg 

Depends on / 依赖: EReal.coe_neg, EReal.coe_pos.mpr, coe_mul, coe_neg, coe_pos, eq_or_lt_of_le, le_of_lt, lt_trichotomy, mul_nonpos_iff, mul_top_of_pos, ofReal_mul, rename_i, top_mul_of_neg, top_mul_of_pos
-/
lemma toENNReal_mul {x y : EReal} (hx : 0 <= x) :
    (x * y).toENNReal = x.toENNReal * y.toENNReal := by
  induction x <;> induction y
    <;> try {· simp_all [mul_nonpos_iff, ofReal_mul, ← coe_mul]}
  · rcases eq_or_lt_of_le hx with (hx | hx)
    · simp [← hx]
    · simp_all [mul_top_of_pos hx]
  · rename_i a
    rcases lt_trichotomy a 0 with (ha | ha | ha)
    · simp_all [le_of_lt, top_mul_of_neg (EReal.coe_neg'.mpr ha)]
    · simp [ha]
    · simp_all [top_mul_of_pos (EReal.coe_pos.mpr ha)]

/--
lemma `toENNReal_mul'` / 引理 `toENNReal_mul'`

English:
lemma toENNReal_mul'
  given: {x y : EReal} (hy : 0 <= y)
  proof: by
  rw [EReal.mul_comm]; rw [toENNReal_mul hy]; rw [mul_comm]

中文:
引理 toENN实数_mul'
  条件: {x y : E实数} (hy : 0 <= y)
  证明: by
  rw [EReal.mul_comm]; rw [toENNReal_mul hy]; rw [mul_comm]

Depends on / 依赖: EReal.mul_comm, mul_comm, toENNReal_mul
-/
lemma toENNReal_mul' {x y : EReal} (hy : 0 <= y) :
    (x * y).toENNReal = x.toENNReal * y.toENNReal := by
  rw [EReal.mul_comm]; rw [toENNReal_mul hy]; rw [mul_comm]

/--
lemma `right_distrib_of_nonneg` / 引理 `right_distrib_of_nonneg`

English:
lemma right_distrib_of_nonneg
  given: {a b c : EReal} (ha : 0 <= a) (hb : 0 <= b)
  proof: by
  lift a to Real>=0∞ using ha
  lift b to Real>=0∞ using hb
  cases c using recENNReal with
  | coe c => exact_mod_cast add_mul a b c
  | neg_coe c hc =>
    simp only [mul_neg, ← coe_ennreal_add, ← coe_ennreal_mul, add_mul]
    rw [coe_ennreal_add]; rw [EReal.neg_add (.inl (coe_ennreal_ne_bot _)

中文:
引理 right_distrib_of_nonneg
  条件: {a b c : E实数} (ha : 0 <= a) (hb : 0 <= b)
  证明: by
  lift a to Real>=0∞ using ha
  lift b to Real>=0∞ using hb
  cases c using recENNReal with
  | coe c => exact_mod_cast add_mul a b c
  | neg_coe c hc =>
    simp only [mul_neg, ← coe_ennreal_add, ← coe_ennreal_mul, add_mul]
    rw [coe_ennreal_add]; rw [EReal.neg_add (.inl (coe_ennreal_ne_bot _)

Depends on / 依赖: EReal.neg_add, add_mul, coe_ennreal_add, coe_ennreal_mul, coe_ennreal_ne_bot, mul_neg, neg_add, neg_coe, recENNReal, sub_eq_add_neg
-/
lemma right_distrib_of_nonneg {a b c : EReal} (ha : 0 <= a) (hb : 0 <= b) :
    (a + b) * c = a * c + b * c := by
  lift a to Real>=0∞ using ha
  lift b to Real>=0∞ using hb
  cases c using recENNReal with
  | coe c => exact_mod_cast add_mul a b c
  | neg_coe c hc =>
    simp only [mul_neg, ← coe_ennreal_add, ← coe_ennreal_mul, add_mul]
    rw [coe_ennreal_add]; rw [EReal.neg_add (.inl (coe_ennreal_ne_bot _)) (.inr (coe_ennreal_ne_bot _))]; rw [sub_eq_add_neg]

/--
lemma `left_distrib_of_nonneg` / 引理 `left_distrib_of_nonneg`

English:
lemma left_distrib_of_nonneg
  given: {a b c : EReal} (ha : 0 <= a) (hb : 0 <= b)
  proof: by
  nth_rewrite 1 [EReal.mul_comm]; nth_rewrite 2 [EReal.mul_comm]; nth_rewrite 3 [EReal.mul_comm]
  exact right_distrib_of_nonneg ha hb

中文:
引理 left_distrib_of_nonneg
  条件: {a b c : E实数} (ha : 0 <= a) (hb : 0 <= b)
  证明: by
  nth_rewrite 1 [EReal.mul_comm]; nth_rewrite 2 [EReal.mul_comm]; nth_rewrite 3 [EReal.mul_comm]
  exact right_distrib_of_nonneg ha hb

Depends on / 依赖: EReal.mul_comm, mul_comm, nth_rewrite, right_distrib_of_nonneg
-/
lemma left_distrib_of_nonneg {a b c : EReal} (ha : 0 <= a) (hb : 0 <= b) :
    c * (a + b) = c * a + c * b := by
  nth_rewrite 1 [EReal.mul_comm]; nth_rewrite 2 [EReal.mul_comm]; nth_rewrite 3 [EReal.mul_comm]
  exact right_distrib_of_nonneg ha hb

/--
lemma `mul_sub_of_nonneg_of_nonpos` / 引理 `mul_sub_of_nonneg_of_nonpos`

English:
lemma mul_sub_of_nonneg_of_nonpos
  given: {a b c : EReal} (hb : 0 <= b) (hc : c <= 0)
  proof: by
  rw [sub_eq_add_neg]; rw [left_distrib_of_nonneg hb (by simpa)]
  simp [← neg_mul, sub_eq_add_neg]

中文:
引理 mul_sub_of_nonneg_of_nonpos
  条件: {a b c : E实数} (hb : 0 <= b) (hc : c <= 0)
  证明: by
  rw [sub_eq_add_neg]; rw [left_distrib_of_nonneg hb (by simpa)]
  simp [← neg_mul, sub_eq_add_neg]

Depends on / 依赖: left_distrib_of_nonneg, neg_mul, sub_eq_add_neg
-/
lemma mul_sub_of_nonneg_of_nonpos {a b c : EReal} (hb : 0 <= b) (hc : c <= 0) :
    a * (b - c) = a * b - a * c := by
  rw [sub_eq_add_neg]; rw [left_distrib_of_nonneg hb (by simpa)]
  simp [← neg_mul, sub_eq_add_neg]

/--
lemma `left_distrib_of_nonneg_of_ne_top` / 引理 `left_distrib_of_nonneg_of_ne_top`

English:
lemma left_distrib_of_nonneg_of_ne_top
  statement: {x : EReal} (hx_nonneg : 0 <= x)
  proof: by
  cases hx_nonneg.eq_or_lt' with
  | inl hx0 => simp [hx0]
  | inr hx0 =>
  lift x to Real using ⟨hx_ne_top, hx0.ne_bot⟩
  cases y <;> cases z <;>
    simp [mul_bot_of_pos hx0, mul_top_of_pos hx0, ← coe_mul, ← coe_add, mul_add]

中文:
引理 left_distrib_of_nonneg_of_ne_top
  结论: {x : E实数} (hx_nonneg : 0 <= x)
  证明: by
  cases hx_nonneg.eq_or_lt' with
  | inl hx0 => simp [hx0]
  | inr hx0 =>
  lift x to Real using ⟨hx_ne_top, hx0.ne_bot⟩
  cases y <;> cases z <;>
    simp [mul_bot_of_pos hx0, mul_top_of_pos hx0, ← coe_mul, ← coe_add, mul_add]

Depends on / 依赖: coe_add, coe_mul, eq_or_lt, hx0.ne_bot, hx_ne_top, hx_nonneg, hx_nonneg.eq_or_lt, mul_add, mul_bot_of_pos, mul_top_of_pos, ne_bot
-/
lemma left_distrib_of_nonneg_of_ne_top {x : EReal} (hx_nonneg : 0 <= x)
    (hx_ne_top : x != ⊤) (y z : EReal) :
    x * (y + z) = x * y + x * z := by
  cases hx_nonneg.eq_or_lt' with
  | inl hx0 => simp [hx0]
  | inr hx0 =>
  lift x to Real using ⟨hx_ne_top, hx0.ne_bot⟩
  cases y <;> cases z <;>
    simp [mul_bot_of_pos hx0, mul_top_of_pos hx0, ← coe_mul, ← coe_add, mul_add]

/--
lemma `right_distrib_of_nonneg_of_ne_top` / 引理 `right_distrib_of_nonneg_of_ne_top`

English:
lemma right_distrib_of_nonneg_of_ne_top
  statement: {x : EReal} (hx_nonneg : 0 <= x)
  proof: by
  simpa only [EReal.mul_comm] using left_distrib_of_nonneg_of_ne_top hx_nonneg hx_ne_top y z

中文:
引理 right_distrib_of_nonneg_of_ne_top
  结论: {x : E实数} (hx_nonneg : 0 <= x)
  证明: by
  simpa only [EReal.mul_comm] using left_distrib_of_nonneg_of_ne_top hx_nonneg hx_ne_top y z

Depends on / 依赖: EReal.mul_comm, hx_ne_top, hx_nonneg, left_distrib_of_nonneg_of_ne_top, mul_comm
-/
lemma right_distrib_of_nonneg_of_ne_top {x : EReal} (hx_nonneg : 0 <= x)
    (hx_ne_top : x != ⊤) (y z : EReal) :
    (y + z) * x = y * x + z * x := by
  simpa only [EReal.mul_comm] using left_distrib_of_nonneg_of_ne_top hx_nonneg hx_ne_top y z

/--
lemma `mul_sub_of_nonneg_of_ne_top` / 引理 `mul_sub_of_nonneg_of_ne_top`

English:
lemma mul_sub_of_nonneg_of_ne_top
  given: {a b c : EReal} (ha : 0 <= a) (ha' : a != ⊤)
  proof: by
  rw [sub_eq_add_neg]; rw [left_distrib_of_nonneg_of_ne_top ha ha']
  simp [← neg_mul, sub_eq_add_neg]

中文:
引理 mul_sub_of_nonneg_of_ne_top
  条件: {a b c : E实数} (ha : 0 <= a) (ha' : a != ⊤)
  证明: by
  rw [sub_eq_add_neg]; rw [left_distrib_of_nonneg_of_ne_top ha ha']
  simp [← neg_mul, sub_eq_add_neg]

Depends on / 依赖: left_distrib_of_nonneg_of_ne_top, neg_mul, sub_eq_add_neg
-/
lemma mul_sub_of_nonneg_of_ne_top {a b c : EReal} (ha : 0 <= a) (ha' : a != ⊤) :
    a * (b - c) = a * b - a * c := by
  rw [sub_eq_add_neg]; rw [left_distrib_of_nonneg_of_ne_top ha ha']
  simp [← neg_mul, sub_eq_add_neg]

/--
lemma `sub_mul_of_nonneg_of_ne_top` / 引理 `sub_mul_of_nonneg_of_ne_top`

English:
lemma sub_mul_of_nonneg_of_ne_top
  given: {a b c : EReal} (ha : 0 <= a) (ha' : a != ⊤)
  proof: by
  rw [sub_eq_add_neg]; rw [right_distrib_of_nonneg_of_ne_top ha ha']
  simp [← neg_mul, sub_eq_add_neg]

@[simp]

中文:
引理 sub_mul_of_nonneg_of_ne_top
  条件: {a b c : E实数} (ha : 0 <= a) (ha' : a != ⊤)
  证明: by
  rw [sub_eq_add_neg]; rw [right_distrib_of_nonneg_of_ne_top ha ha']
  simp [← neg_mul, sub_eq_add_neg]

@[simp]

Depends on / 依赖: neg_mul, right_distrib_of_nonneg_of_ne_top, sub_eq_add_neg
-/
lemma sub_mul_of_nonneg_of_ne_top {a b c : EReal} (ha : 0 <= a) (ha' : a != ⊤) :
    (b - c) * a = b * a - c * a := by
  rw [sub_eq_add_neg]; rw [right_distrib_of_nonneg_of_ne_top ha ha']
  simp [← neg_mul, sub_eq_add_neg]

@[simp]
/--
lemma `nsmul_eq_mul` / 引理 `nsmul_eq_mul`

English:
lemma nsmul_eq_mul
  given: (n : Nat) (x : EReal)
  statement: n • x = n * x
  proof: by
  induction n with
  | zero => rw [zero_smul, Nat.cast_zero, zero_mul]
  | succ n ih =>
    rw [succ_nsmul]; rw [ih]; rw [Nat.cast_succ]
    convert! (EReal.right_distrib_of_nonneg _ _).symm <;> simp

中文:
引理 nsmul_eq_mul
  条件: (n : 自然数) (x : E实数)
  结论: n • x = n * x
  证明: by
  induction n with
  | zero => rw [zero_smul, Nat.cast_zero, zero_mul]
  | succ n ih =>
    rw [succ_nsmul]; rw [ih]; rw [Nat.cast_succ]
    convert! (EReal.right_distrib_of_nonneg _ _).symm <;> simp

Depends on / 依赖: EReal.right_distrib_of_nonneg, Nat.cast_succ, Nat.cast_zero, cast_succ, cast_zero, convert, right_distrib_of_nonneg, succ_nsmul, zero_mul, zero_smul
-/
lemma nsmul_eq_mul (n : Nat) (x : EReal) : n • x = n * x := by
  induction n with
  | zero => rw [zero_smul, Nat.cast_zero, zero_mul]
  | succ n ih =>
    rw [succ_nsmul]; rw [ih]; rw [Nat.cast_succ]
    convert! (EReal.right_distrib_of_nonneg _ _).symm <;> simp

end EReal

namespace Mathlib.Meta.Positivity

open Lean Meta Qq Function

/-- Extension for the `positivity` tactic: sum of two `EReal`s. -/
@[positivity (_ + _ : EReal)]
meta def evalERealAdd : PositivityExt where eval {u α} zα pα? e :=
  match pα? with | none => pure .none | some pα => do
  match u, α, e with
  | 0, ~q(EReal), ~q($a + $b) =>
    assertInstancesCommute
    match ← core zα pα a with
    | .positive pa =>
      match (← core zα pα b).toNonneg with
      | some pb => pure (.positive q(EReal.add_pos_of_pos_of_nonneg $pa $pb))
      | _ => pure .none
    | .nonnegative pa =>
      match ← core zα pα b with
      | .positive pb => pure (.positive q(Right.add_pos_of_nonneg_of_pos $pa $pb))
      | .nonnegative pb => pure (.nonnegative q(add_nonneg $pa $pb))
      | _ => pure .none
    | _ => pure .none
  | _, _, _ => throwError "not a sum of 2 `EReal`s"

/-- Extension for the `positivity` tactic: product of two `EReal`s. -/
@[positivity (_ * _ : EReal)]
meta def evalERealMul : PositivityExt where eval {u α} zα pα? e :=
  match pα? with | none => pure .none | some pα => do
  match u, α, e with
  | 0, ~q(EReal), ~q($a * $b) =>
    assertInstancesCommute
    match ← core zα pα a with
    | .positive pa =>
      match ← core zα pα b with
| .positive pb => pure .positive q(EReal.mul_pos $pa $pb)
| .nonnegative pb => pure .nonnegative q(EReal.mul_nonneg (le_of_lt $pa) $pb)
| .nonzero pb => pure .nonzero q(mul_ne_zero (ne_of_gt $pa) $pb)
      | _ => pure .none
    | .nonnegative pa =>
      match (← core zα pα b).toNonneg with
      | some pb => pure (.nonnegative q(EReal.mul_nonneg $pa $pb))
      | none => pure .none
    | .nonzero pa =>
      match (← core zα pα b).toNonzero with
      | some pb => pure (.nonzero q(mul_ne_zero $pa $pb))
      | none => pure .none
    | _ => pure .none
  | _, _, _ => throwError "not a product of 2 `EReal`s"

end Mathlib.Meta.Positivity
