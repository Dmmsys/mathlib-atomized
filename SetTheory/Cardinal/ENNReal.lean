/-
Copyright (c) 2026 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Real.ENatENNReal
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Lemmas about `Nat.card` and `ENNReal`
-/

public section

namespace ENNReal

/--
lemma `toReal_enatCard` / 引理 `toReal_enatCard`

English:
lemma toReal_enatCard
  given: (α : Type*)
  statement: ENNReal.toReal (ENat.card α) = Nat.card α
  proof: by
  cases finite_or_infinite α <;> simp [ENat.card_eq_coe_natCard]

中文:
引理 toReal_enatCard
  条件: (α : 类型)
  结论: ENN实数.to实数 (E自然数.card α) = 自然数.card α
  证明: by
  cases finite_or_infinite α <;> simp [ENat.card_eq_coe_natCard]
-/
@[simp] lemma toReal_enatCard (α : Type*) : ENNReal.toReal (ENat.card α) = Nat.card α := by
  cases finite_or_infinite α <;> simp [ENat.card_eq_coe_natCard]

end ENNReal
