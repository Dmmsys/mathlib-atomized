/-
Copyright (c) 2025 Yongshun Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongshun Ye
-/
module

public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Nat.Prime.Defs

/-!
# Lemmas related to `Nat.Prime` and `lcm`

This file contains lemmas related to `Nat.Prime`.
These lemmas are kept separate from `Mathlib/Data/Nat/GCD/Basic.lean` in order to minimize imports.

## Main results

- `Nat.Prime.dvd_or_dvd_of_dvd_lcm`: If `p ∣ lcm a b`, then `p ∣ a ∨ p ∣ b`.
- `Nat.Prime.dvd_lcm`: `p ∣ lcm a b ↔ p ∣ a ∨ p ∣ b`.
- `Nat.Prime.not_dvd_lcm`: If `p ∤ a` and `p ∤ b`, then `p ∤ lcm a b`.

-/

public section

namespace Nat

namespace Prime
variable {p a b : Nat} (hp : Prime p)

include hp

/--
theorem `dvd_or_dvd_of_dvd_lcm` / 定理 `dvd_or_dvd_of_dvd_lcm`

English:
theorem dvd_or_dvd_of_dvd_lcm
  given: (h : p ∣ lcm a b)
  statement: p ∣ a ∨ p ∣ b
  proof: dvd_or_dvd hp (h.trans (lcm_dvd_mul a b))

中文:
定理 dvd_or_dvd_of_dvd_lcm
  条件: (h : p ∣ 最小公倍数 a b)
  结论: p ∣ a ∨ p ∣ b
  证明: dvd_or_dvd hp (h.trans (lcm_dvd_mul a b))

Depends on / 依赖: dvd_or_dvd, h.trans, lcm_dvd_mul
-/
theorem dvd_or_dvd_of_dvd_lcm (h : p ∣ lcm a b) : p ∣ a ∨ p ∣ b :=
  dvd_or_dvd hp (h.trans (lcm_dvd_mul a b))

/--
theorem `dvd_lcm` / 定理 `dvd_lcm`

English:
theorem dvd_lcm
  statement: p ∣ lcm a b ↔ p ∣ a ∨ p ∣ b
  proof: ⟨hp.dvd_or_dvd_of_dvd_lcm, (Or.elim · (dvd_lcm_of_dvd_left · _) (dvd_lcm_of_dvd_right · _))⟩

中文:
定理 dvd_lcm
  结论: p ∣ 最小公倍数 a b ↔ p ∣ a ∨ p ∣ b
  证明: ⟨hp.dvd_or_dvd_of_dvd_lcm, (Or.elim · (dvd_lcm_of_dvd_left · _) (dvd_lcm_of_dvd_right · _))⟩

Depends on / 依赖: Or.elim, dvd_lcm_of_dvd_left, dvd_lcm_of_dvd_right, dvd_or_dvd_of_dvd_lcm, hp.dvd_or_dvd_of_dvd_lcm
-/
theorem dvd_lcm : p ∣ lcm a b ↔ p ∣ a ∨ p ∣ b :=
  ⟨hp.dvd_or_dvd_of_dvd_lcm, (Or.elim · (dvd_lcm_of_dvd_left · _) (dvd_lcm_of_dvd_right · _))⟩

/--
theorem `not_dvd_lcm` / 定理 `not_dvd_lcm`

English:
theorem not_dvd_lcm
  given: (ha : ¬ p ∣ a) (hb : ¬ p ∣ b)
  statement: ¬ p ∣ lcm a b
  proof: hp.dvd_lcm.not.mpr not_or.mpr ⟨ha, hb⟩

中文:
定理 not_dvd_lcm
  条件: (ha : ¬ p ∣ a) (hb : ¬ p ∣ b)
  结论: ¬ p ∣ 最小公倍数 a b
  证明: hp.dvd_lcm.not.mpr not_or.mpr ⟨ha, hb⟩

Depends on / 依赖: dvd_lcm, hp.dvd_lcm.not.mpr, not_or, not_or.mpr
-/
theorem not_dvd_lcm (ha : ¬ p ∣ a) (hb : ¬ p ∣ b) : ¬ p ∣ lcm a b :=
hp.dvd_lcm.not.mpr not_or.mpr ⟨ha, hb⟩

end Prime

end Nat
