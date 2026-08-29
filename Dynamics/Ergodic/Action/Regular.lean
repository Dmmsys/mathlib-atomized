/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Dynamics.Ergodic.Action.Basic
public import Mathlib.MeasureTheory.Group.Prod

/-!
# Regular action of a group on itself is ergodic

In this file we prove that the left and right actions of a group on itself are ergodic.
-/

public section

open MeasureTheory Measure Filter Set
open scoped Pointwise

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  {μ : Measure G} [SFinite μ]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [μ.IsMulLeftInvariant]
  signature: : ErgodicSMul G G μ
  body: by
  refine ⟨fun {s} hsm hs => ?_⟩
  suffices (existsᵐ x ∂μ, x in s) -> forallᵐ x ∂μ, x in s by
    simp only [eventuallyConst_set, ← not_frequently]
    exact or_not_of_imp this
  intro hμs
  obtain ⟨a, has, ha⟩ : exists a in s, forallᵐ b ∂μ, (b * a in s ↔ a in s) := by
    refine (hμs.and_eventual

中文:
实例 [μ.是MulLeftInvariant]
  签名: : ErgodicSMul G G μ
  定义体: by
  refine ⟨fun {s} hsm hs => ?_⟩
  suffices (existsᵐ x ∂μ, x in s) -> forallᵐ x ∂μ, x in s by
    simp only [eventuallyConst_set, ← not_frequently]
    exact or_not_of_imp this
  intro hμs
  obtain ⟨a, has, ha⟩ : exists a in s, forallᵐ b ∂μ, (b * a in s ↔ a in s) := by
    refine (hμs.and_eventual

Depends on / 依赖: MeasureTheory, MeasureTheory.qua, ae_ae_comm, ae_of_all, and_eventually, eventuallyConst_set, hsm.preimage, measurable_fst, measurable_snd, measurable_snd.mul, mem.iff, mem_iff, not_frequently, or_not_of_imp, preimage, s.and_eventually
-/
instance [μ.IsMulLeftInvariant] : ErgodicSMul G G μ := by
  refine ⟨fun {s} hsm hs => ?_⟩
  suffices (existsᵐ x ∂μ, x in s) -> forallᵐ x ∂μ, x in s by
    simp only [eventuallyConst_set, ← not_frequently]
    exact or_not_of_imp this
  intro hμs
  obtain ⟨a, has, ha⟩ : exists a in s, forallᵐ b ∂μ, (b * a in s ↔ a in s) := by
    refine (hμs.and_eventually ?_).exists
    rw [ae_ae_comm]
    · exact ae_of_all _ fun b => (hs b).mem_iff
    · exact ((hsm.preimage <| measurable_snd.mul measurable_fst).mem.iff
        (hsm.preimage measurable_fst).mem).setOf
  simpa [has] using (MeasureTheory.quasiMeasurePreserving_mul_right μ a⁻¹).ae ha

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [μ.IsMulRightInvariant]
  signature: : ErgodicSMul Gᵐᵒᵖ G μ
  body: by
  refine ⟨fun {s} hsm hs => ?_⟩
  suffices (existsᵐ x ∂μ, x in s) -> forallᵐ x ∂μ, x in s by
    simp only [eventuallyConst_set, ← not_frequently]
    exact or_not_of_imp this
  intro hμs
  obtain ⟨a, has, ha⟩ : exists a in s, forallᵐ b ∂μ, (a * b in s ↔ a in s) := by
    refine (hμs.and_eventual

中文:
实例 [μ.是MulRightInvariant]
  签名: : ErgodicSMul Gᵐᵒᵖ G μ
  定义体: by
  refine ⟨fun {s} hsm hs => ?_⟩
  suffices (existsᵐ x ∂μ, x in s) -> forallᵐ x ∂μ, x in s by
    simp only [eventuallyConst_set, ← not_frequently]
    exact or_not_of_imp this
  intro hμs
  obtain ⟨a, has, ha⟩ : exists a in s, forallᵐ b ∂μ, (a * b in s ↔ a in s) := by
    refine (hμs.and_eventual

Depends on / 依赖: ae_ae_comm, ae_of_all, and_eventually, eventuallyConst_set, hsm.preimage, measurable_fst, measurable_fst.mul, measurable_snd, mem.iff, mem_iff, not_frequently, or_not_of_imp, preimage, quasiMeasurePre, s.and_eventually
-/
instance [μ.IsMulRightInvariant] : ErgodicSMul Gᵐᵒᵖ G μ := by
  refine ⟨fun {s} hsm hs => ?_⟩
  suffices (existsᵐ x ∂μ, x in s) -> forallᵐ x ∂μ, x in s by
    simp only [eventuallyConst_set, ← not_frequently]
    exact or_not_of_imp this
  intro hμs
  obtain ⟨a, has, ha⟩ : exists a in s, forallᵐ b ∂μ, (a * b in s ↔ a in s) := by
    refine (hμs.and_eventually ?_).exists
    rw [ae_ae_comm]
    · exact ae_of_all _ fun b => (hs ⟨b⟩).mem_iff
    · exact ((hsm.preimage <| measurable_fst.mul measurable_snd).mem.iff
        (hsm.preimage measurable_fst).mem).setOf
  simpa [has] using (quasiMeasurePreserving_mul_left μ a⁻¹).ae ha
