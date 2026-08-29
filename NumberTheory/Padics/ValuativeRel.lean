/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.Valuation.RankOne

/-!
# p-adic numbers with a valuative relation

## Tags

p-adic, p adic, padic, norm, valuation, cauchy, completion, p-adic completion
-/

public section

variable {p : Nat} [hp : Fact p.Prime] {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀]
    (v : Valuation Rat_[p] Γ₀)

open ValuativeRel WithZero

namespace Padic

-- TODO: should this be automatic from a nonarchimedean nontrivially normed field?
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ValuativeRel Rat_[p]
  body: .ofValuation mulValuation

中文:
实例 :
  签名: ValuativeRel Rat_[p]
  定义体: .ofValuation mulValuation

Depends on / 依赖: mulValuation, ofValuation
-/
noncomputable instance : ValuativeRel Rat_[p] := .ofValuation mulValuation

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Valuation.Compatible (mulValuation (p := p))
  body: .ofValuation _

中文:
实例 :
  签名: Valuation.Compatible (mulValuation (p := p))
  定义体: .ofValuation _

Depends on / 依赖: ofValuation
-/
instance : Valuation.Compatible (mulValuation (p := p)) := .ofValuation _

variable [v.Compatible]

/--
lemma `valuation_p_ne_zero` / 引理 `valuation_p_ne_zero`

English:
lemma valuation_p_ne_zero
  statement: v p != 0
  proof: by
  simp [(isEquiv v (Padic.mulValuation)).eq_zero, hp.out.ne_zero]

@[simp]

中文:
引理 valuation_p_ne_zero
  结论: v p != 0
  证明: by
  simp [(isEquiv v (Padic.mulValuation)).eq_zero, hp.out.ne_zero]

@[simp]

Depends on / 依赖: Padic.mulValuation, eq_zero, hp.out.ne_zero, isEquiv, mulValuation, ne_zero
-/
lemma valuation_p_ne_zero : v p != 0 := by
  simp [(isEquiv v (Padic.mulValuation)).eq_zero, hp.out.ne_zero]

@[simp]
/--
lemma `valuation_p_lt_one` / 引理 `valuation_p_lt_one`

English:
lemma valuation_p_lt_one
  statement: v p < 1
  proof: by
  simp [(isEquiv v (Padic.mulValuation)).lt_one_iff_lt_one, hp.out.ne_zero, inv_lt_one₀,
    ← log_lt_iff_lt_exp]

中文:
引理 valuation_p_lt_one
  结论: v p < 1
  证明: by
  simp [(isEquiv v (Padic.mulValuation)).lt_one_iff_lt_one, hp.out.ne_zero, inv_lt_one₀,
    ← log_lt_iff_lt_exp]

Depends on / 依赖: Padic.mulValuation, hp.out.ne_zero, isEquiv, log_lt_iff_lt_exp, lt_one_iff_lt_one, mulValuation, ne_zero
-/
lemma valuation_p_lt_one : v p < 1 := by
  simp [(isEquiv v (Padic.mulValuation)).lt_one_iff_lt_one, hp.out.ne_zero, inv_lt_one₀,
    ← log_lt_iff_lt_exp]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsNontrivial Rat_[p]
  body: ⟨ValuativeRel.valuation _ p, valuation_p_ne_zero _, (valuation_p_lt_one _).ne⟩

中文:
实例 :
  签名: IsNontrivial Rat_[p]
  定义体: ⟨ValuativeRel.valuation _ p, valuation_p_ne_zero _, (valuation_p_lt_one _).ne⟩

Depends on / 依赖: ValuativeRel, ValuativeRel.valuation, valuation, valuation_p_lt_one, valuation_p_ne_zero
-/
instance : IsNontrivial Rat_[p] where
  condition := ⟨ValuativeRel.valuation _ p, valuation_p_ne_zero _, (valuation_p_lt_one _).ne⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsRankLeOne Rat_[p]
  body: .of_compatible_mulArchimedean mulValuation

中文:
实例 :
  签名: IsRankLeOne Rat_[p]
  定义体: .of_compatible_mulArchimedean mulValuation

Depends on / 依赖: mulValuation, of_compatible_mulArchimedean
-/
instance : IsRankLeOne Rat_[p] := .of_compatible_mulArchimedean mulValuation

end Padic
