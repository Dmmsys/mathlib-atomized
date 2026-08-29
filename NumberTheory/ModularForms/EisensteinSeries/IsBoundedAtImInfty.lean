/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Defs
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
public import Mathlib.NumberTheory.ModularForms.Identities

/-!
# Boundedness of Eisenstein series

We show that Eisenstein series of weight `k` and level `Γ(N)` with congruence condition
`a : Fin 2 → ZMod N` are bounded at infinity.

## Outline of argument

We need to bound the value of the Eisenstein series (acted on by `A : SL(2,ℤ)`)
at a given point `z` in the upper half plane. Since these are modular forms of level `Γ(N)`,
it suffices to prove this for `z ∈ verticalStrip N z.im`.

We can then, first observe that the slash action just changes our `a` to `(a ᵥ* A)` and
we then use our bounds for Eisenstein series in these vertical strips to get the result.
-/

public section

noncomputable section

open ModularForm UpperHalfPlane Matrix SlashInvariantForm CongruenceSubgroup

open scoped MatrixGroups

namespace EisensteinSeries

/--
lemma `summable_norm_eisSummand` / 引理 `summable_norm_eisSummand`

English:
lemma summable_norm_eisSummand
  given: {k : Int} (hk : 3 <= k) (z : ℍ)
  proof: by
  have hk' : (2 : Real) < k := by norm_cast
  apply ((summable_one_div_norm_rpow hk').mul_left <| r z ^ (-k : Real)).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro b
  simp only [eisSummand, norm_zpow]
  exact_mod_cast summand_bound z (show 0 <= (k : Real) by positivity) b

中文:
引理 summable_norm_eisSummand
  条件: {k : 整数} (hk : 3 <= k) (z : ℍ)
  证明: by
  have hk' : (2 : Real) < k := by norm_cast
  apply ((summable_one_div_norm_rpow hk').mul_left <| r z ^ (-k : Real)).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro b
  simp only [eisSummand, norm_zpow]
  exact_mod_cast summand_bound z (show 0 <= (k : Real) by positivity) b

Depends on / 依赖: eisSummand, mul_left, norm_nonneg, norm_zpow, of_nonneg_of_le, summable_one_div_norm_rpow, summand_bound
-/
lemma summable_norm_eisSummand {k : Int} (hk : 3 <= k) (z : ℍ) :
    Summable fun (x : Fin 2 -> Int) => ‖(eisSummand k x z)‖ := by
  have hk' : (2 : Real) < k := by norm_cast
  apply ((summable_one_div_norm_rpow hk').mul_left <| r z ^ (-k : Real)).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro b
  simp only [eisSummand, norm_zpow]
  exact_mod_cast summand_bound z (show 0 <= (k : Real) by positivity) b

/--
lemma `norm_le_tsum_norm` / 引理 `norm_le_tsum_norm`

English:
lemma norm_le_tsum_norm
  given: (N : Nat) (a : Fin 2 -> ZMod N) (k : Int) (hk : 3 <= k) (z : ℍ)
  proof: by
  simp_rw [eisensteinSeries]
  apply le_trans (norm_tsum_le_tsum_norm ((summable_norm_eisSummand hk z).subtype _))
    (Summable.tsum_subtype_le (fun (x : Fin 2 -> Int) => ‖(eisSummand k x z)‖) _ (fun _ => norm_nonneg _)
      (summable_norm_eisSummand hk z))

中文:
引理 norm_le_tsum_norm
  条件: (N : 自然数) (a : 有限集 2 -> ZMod N) (k : 整数) (hk : 3 <= k) (z : ℍ)
  证明: by
  simp_rw [eisensteinSeries]
  apply le_trans (norm_tsum_le_tsum_norm ((summable_norm_eisSummand hk z).subtype _))
    (Summable.tsum_subtype_le (fun (x : Fin 2 -> Int) => ‖(eisSummand k x z)‖) _ (fun _ => norm_nonneg _)
      (summable_norm_eisSummand hk z))

Depends on / 依赖: Summable, Summable.tsum_subtype_le, eisSummand, eisensteinSeries, le_trans, norm_nonneg, norm_tsum_le_tsum_norm, simp_rw, subtype, summable_norm_eisSummand, tsum_subtype_le
-/
lemma norm_le_tsum_norm (N : Nat) (a : Fin 2 -> ZMod N) (k : Int) (hk : 3 <= k) (z : ℍ) :
    ‖eisensteinSeries a k z‖ <= ∑' (x : Fin 2 -> Int), ‖eisSummand k x z‖ := by
  simp_rw [eisensteinSeries]
  apply le_trans (norm_tsum_le_tsum_norm ((summable_norm_eisSummand hk z).subtype _))
    (Summable.tsum_subtype_le (fun (x : Fin 2 -> Int) => ‖(eisSummand k x z)‖) _ (fun _ => norm_nonneg _)
      (summable_norm_eisSummand hk z))

/--
theorem `isBoundedAtImInfty_eisensteinSeriesSIF` / 定理 `isBoundedAtImInfty_eisensteinSeriesSIF`

English:
theorem isBoundedAtImInfty_eisensteinSeriesSIF
  statement: {N : Nat} [NeZero N] (a : Fin 2 -> ZMod N) {k : Int}
  proof: by
  simp_rw [UpperHalfPlane.isBoundedAtImInfty_iff, eisensteinSeriesSIF] at *
  refine ⟨∑'(x : Fin 2 -> Int), r ⟨⟨N, 2⟩, Nat.ofNat_pos⟩ ^ (-k) * ‖x‖ ^ (-k), 2, ?_⟩
  intro z hz
  obtain ⟨n, hn⟩ := (ModularGroup_T_zpow_mem_verticalStrip z (NeZero.pos N))
  rw [SlashInvariantForm.coe_mk]; rw [eisensteinSeries_slash_apply]; rw [← eisensteinSeriesSIF_apply]; rw [← T_zpow_width_invariant N k n (eisensteinSeriesSIF (a ᵥ* A) k) z]
  apply le_trans (norm_le_tsum_norm N (a ᵥ* A) k hk _)
  have hk' : (2 : Real) < k := by norm_cast
  apply (summable_norm_eisSummand hk _).tsum_le_tsum _
· exact_mod_cast (summable_one_div_norm_rpow hk').mul_left r ⟨⟨N, 2⟩, Nat.ofNat_pos⟩ ^ (-k)
  · intro x
    simp_rw [eisSummand, norm_zpow]
    exact_mod_cast
      summand_bound_of_mem_verticalStrip (lt_trans two_pos hk').le x two_pos
      (verticalStrip_anti_right N hz hn)

@[deprecated (since := "2026-02-10")]
alias isBoundedAtImInfty_eisensteinSeries_SIF := isBoundedAtImInfty_eisensteinSeriesSIF

中文:
定理 isBoundedAtImInfty_eisensteinSeriesSIF
  结论: {N : 自然数} [NeZero N] (a : 有限集 2 -> ZMod N) {k : 整数}
  证明: by
  simp_rw [UpperHalfPlane.isBoundedAtImInfty_iff, eisensteinSeriesSIF] at *
  refine ⟨∑'(x : Fin 2 -> Int), r ⟨⟨N, 2⟩, Nat.ofNat_pos⟩ ^ (-k) * ‖x‖ ^ (-k), 2, ?_⟩
  intro z hz
  obtain ⟨n, hn⟩ := (ModularGroup_T_zpow_mem_verticalStrip z (NeZero.pos N))
  rw [SlashInvariantForm.coe_mk]; rw [eisensteinSeries_slash_apply]; rw [← eisensteinSeriesSIF_apply]; rw [← T_zpow_width_invariant N k n (eisensteinSeriesSIF (a ᵥ* A) k) z]
  apply le_trans (norm_le_tsum_norm N (a ᵥ* A) k hk _)
  have hk' : (2 : Real) < k := by norm_cast
  apply (summable_norm_eisSummand hk _).tsum_le_tsum _
· exact_mod_cast (summable_one_div_norm_rpow hk').mul_left r ⟨⟨N, 2⟩, Nat.ofNat_pos⟩ ^ (-k)
  · intro x
    simp_rw [eisSummand, norm_zpow]
    exact_mod_cast
      summand_bound_of_mem_verticalStrip (lt_trans two_pos hk').le x two_pos
      (verticalStrip_anti_right N hz hn)

@[deprecated (since := "2026-02-10")]
alias isBoundedAtImInfty_eisensteinSeries_SIF := isBoundedAtImInfty_eisensteinSeriesSIF

Depends on / 依赖: ModularGroup_T_zpow_mem_verticalStrip, Nat.ofNat_pos, NeZero, NeZero.pos, SlashInvariantForm, SlashInvariantForm.coe_mk, T_zpow_width_invariant, UpperHalfPlane, UpperHalfPlane.isBoundedAtImInfty_iff, coe_mk, eisensteinSeriesSIF, eisensteinSeriesSIF_apply, eisensteinSeries_slash_apply, isBoundedAtImInfty_iff, le_trans, norm_le_tsum_norm, ofNat_pos, simp_rw
-/
theorem isBoundedAtImInfty_eisensteinSeriesSIF {N : Nat} [NeZero N] (a : Fin 2 -> ZMod N) {k : Int}
    (hk : 3 <= k) (A : SL(2, Int)) : IsBoundedAtImInfty (eisensteinSeriesSIF a k ∣[k] A) := by
  simp_rw [UpperHalfPlane.isBoundedAtImInfty_iff, eisensteinSeriesSIF] at *
  refine ⟨∑'(x : Fin 2 -> Int), r ⟨⟨N, 2⟩, Nat.ofNat_pos⟩ ^ (-k) * ‖x‖ ^ (-k), 2, ?_⟩
  intro z hz
  obtain ⟨n, hn⟩ := (ModularGroup_T_zpow_mem_verticalStrip z (NeZero.pos N))
  rw [SlashInvariantForm.coe_mk]; rw [eisensteinSeries_slash_apply]; rw [← eisensteinSeriesSIF_apply]; rw [← T_zpow_width_invariant N k n (eisensteinSeriesSIF (a ᵥ* A) k) z]
  apply le_trans (norm_le_tsum_norm N (a ᵥ* A) k hk _)
  have hk' : (2 : Real) < k := by norm_cast
  apply (summable_norm_eisSummand hk _).tsum_le_tsum _
· exact_mod_cast (summable_one_div_norm_rpow hk').mul_left r ⟨⟨N, 2⟩, Nat.ofNat_pos⟩ ^ (-k)
  · intro x
    simp_rw [eisSummand, norm_zpow]
    exact_mod_cast
      summand_bound_of_mem_verticalStrip (lt_trans two_pos hk').le x two_pos
      (verticalStrip_anti_right N hz hn)

@[deprecated (since := "2026-02-10")]
alias isBoundedAtImInfty_eisensteinSeries_SIF := isBoundedAtImInfty_eisensteinSeriesSIF

end EisensteinSeries
