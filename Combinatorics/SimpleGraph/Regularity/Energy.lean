/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.SimpleGraph.Density
public import Mathlib.Data.Rat.BigOperators

/-!
# Energy of a partition

This file defines the energy of a partition.

The energy is the auxiliary quantity that drives the induction process in the proof of Szemerédi's
Regularity Lemma. As long as we do not have a suitable equipartition, we will find a new one that
has an energy greater than the previous one plus some fixed constant.

## References

[Yaël Dillies, Bhavik Mehta, *Formalising Szemerédi’s Regularity Lemma in Lean*][srl_itp]
-/

@[expose] public section


open Finset

variable {α : Type*} [DecidableEq α] {s : Finset α} (P : Finpartition s) (G : SimpleGraph α)
  [DecidableRel G.Adj]

namespace Finpartition

/--
Definition of `energy` / `energy` 的定义

English:
definition energy
  signature: : Rat
  body: ((∑ uv in P.parts.offDiag, G.edgeDensity uv.1 uv.2 ^ 2) : Rat) / (#P.parts : Rat) ^ 2

中文:
定义 energy
  签名: : Rat
  定义体: ((∑ uv in P.parts.offDiag, G.edgeDensity uv.1 uv.2 ^ 2) : Rat) / (#P.parts : Rat) ^ 2

Depends on / 依赖: G.edgeDensity, P.parts, P.parts.offDiag, edgeDensity, offDiag
-/
def energy : Rat :=
  ((∑ uv in P.parts.offDiag, G.edgeDensity uv.1 uv.2 ^ 2) : Rat) / (#P.parts : Rat) ^ 2

/--
theorem `energy_nonneg` / 定理 `energy_nonneg`

English:
theorem energy_nonneg
  statement: 0 <= P.energy G
  proof: by
exact div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) sq_nonneg _

中文:
定理 energy_nonneg
  结论: 0 <= P.energy G
  证明: by
exact div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) sq_nonneg _

Depends on / 依赖: Finset, Finset.sum_nonneg, div_nonneg, sq_nonneg, sum_nonneg
-/
theorem energy_nonneg : 0 <= P.energy G := by
exact div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) sq_nonneg _

/--
theorem `energy_le_one` / 定理 `energy_le_one`

English:
theorem energy_le_one
  statement: P.energy G <= 1
  proof: div_le_of_le_mul₀ (sq_nonneg _) zero_le_one
    calc
      ∑ uv in P.parts.offDiag, G.edgeDensity uv.1 uv.2 ^ 2 <= #P.parts.offDiag • (1 : Rat) :=
        sum_le_card_nsmul _ _ 1 fun _ _ =>
(sq_le_one_iff₀ <| G.edgeDensity_nonneg _ _).2 G.edgeDensity_le_one _ _
      _ = #P.parts.offDiag := Nat.smul

中文:
定理 energy_le_one
  结论: P.energy G <= 1
  证明: div_le_of_le_mul₀ (sq_nonneg _) zero_le_one
    calc
      ∑ uv in P.parts.offDiag, G.edgeDensity uv.1 uv.2 ^ 2 <= #P.parts.offDiag • (1 : Rat) :=
        sum_le_card_nsmul _ _ 1 fun _ _ =>
(sq_le_one_iff₀ <| G.edgeDensity_nonneg _ _).2 G.edgeDensity_le_one _ _
      _ = #P.parts.offDiag := Nat.smul

Depends on / 依赖: G.edgeDensity, G.edgeDensity_le_one, G.edgeDensity_nonneg, Nat.smul_one_eq_cast, P.parts.offDiag, edgeDensity, edgeDensity_le_one, edgeDensity_nonneg, offDiag, offDiag_card, one_mul, smul_one_eq_cast, sq_nonneg, sum_le_card_nsmul, tsub_le_self, zero_le_one
-/
theorem energy_le_one : P.energy G <= 1 :=
div_le_of_le_mul₀ (sq_nonneg _) zero_le_one
    calc
      ∑ uv in P.parts.offDiag, G.edgeDensity uv.1 uv.2 ^ 2 <= #P.parts.offDiag • (1 : Rat) :=
        sum_le_card_nsmul _ _ 1 fun _ _ =>
(sq_le_one_iff₀ <| G.edgeDensity_nonneg _ _).2 G.edgeDensity_le_one _ _
      _ = #P.parts.offDiag := Nat.smul_one_eq_cast _
      _ <= _ := by
        rw [offDiag_card]; rw [one_mul]
        norm_cast
        rw [sq]
        exact tsub_le_self

@[simp, norm_cast]
/--
theorem `coe_energy` / 定理 `coe_energy`

English:
theorem coe_energy
  given: {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  proof: by
  rw [energy]; norm_cast

中文:
定理 coe_energy
  条件: {𝕜 : 类型} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  证明: by
  rw [energy]; norm_cast

Depends on / 依赖: energy
-/
theorem coe_energy {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] :
    (P.energy G : 𝕜) =
      (∑ uv in P.parts.offDiag, (G.edgeDensity uv.1 uv.2 : 𝕜) ^ 2) / (#P.parts : 𝕜) ^ 2 := by
  rw [energy]; norm_cast

end Finpartition
