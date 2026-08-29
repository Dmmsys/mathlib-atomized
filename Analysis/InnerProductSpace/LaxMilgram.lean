/-
Copyright (c) 2022 Daniel Roca González. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Roca González
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# The Lax-Milgram Theorem

We consider a Hilbert space `V` over `ℝ`
equipped with a bounded bilinear form `B : V →L[ℝ] V →L[ℝ] ℝ`.

Recall that a bilinear form `B : V →L[ℝ] V →L[ℝ] ℝ` is *coercive*
iff `∃ C, (0 < C) ∧ ∀ u, C * ‖u‖ * ‖u‖ ≤ B u u`.
Under the hypothesis that `B` is coercive we prove the Lax-Milgram theorem:
that is, the map `InnerProductSpace.continuousLinearMapOfBilin` from
`Analysis.InnerProductSpace.Dual` can be upgraded to a continuous equivalence
`IsCoercive.continuousLinearEquivOfBilin : V ≃L[ℝ] V`.

## References

* We follow the notes of Peter Howard's Spring 2020 *M612: Partial Differential Equations* lecture,
  see[howard]

## Tags

dual, Lax-Milgram
-/

@[expose] public section


noncomputable section

open RCLike LinearMap ContinuousLinearMap InnerProductSpace

open LinearMap (ker range)

open RealInnerProductSpace NNReal

universe u

namespace IsCoercive

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace Real V] [CompleteSpace V]
variable {B : V ->L[Real] V ->L[Real] Real}

local postfix:1024 "♯" => continuousLinearMapOfBilin (𝕜 := Real)

/--
theorem `bounded_below` / 定理 `bounded_below`

English:
theorem bounded_below
  given: (coercive : IsCoercive B)
  statement: exists C, 0 < C ∧ forall v, C * ‖v‖ <= ‖B♯ v‖
  proof: by
  rcases coercive with ⟨C, C_ge_0, coercivity⟩
  refine ⟨C, C_ge_0, ?_⟩
  intro v
  by_cases h : 0 < ‖v‖
  · refine (mul_le_mul_iff_left₀ h).mp ?_
    calc
      C * ‖v‖ * ‖v‖ <= B v v := coercivity v
      _ = ⟪B♯ v, v⟫_Real := (continuousLinearMapOfBilin_apply B v v).symm
      _ <= ‖B♯ v‖ * ‖v‖ := real_inner_le_norm (B♯ v) v
  · have : v = 0 := by simpa using h
    simp [this]

中文:
定理 bounded_below
  条件: (coercive : IsCoercive B)
  结论: 存在 C, 0 < C ∧ 对任意 v, C * ‖v‖ <= ‖B♯ v‖
  证明: by
  rcases coercive with ⟨C, C_ge_0, coercivity⟩
  refine ⟨C, C_ge_0, ?_⟩
  intro v
  by_cases h : 0 < ‖v‖
  · refine (mul_le_mul_iff_left₀ h).mp ?_
    calc
      C * ‖v‖ * ‖v‖ <= B v v := coercivity v
      _ = ⟪B♯ v, v⟫_Real := (continuousLinearMapOfBilin_apply B v v).symm
      _ <= ‖B♯ v‖ * ‖v‖ := real_inner_le_norm (B♯ v) v
  · have : v = 0 := by simpa using h
    simp [this]

Depends on / 依赖: C_ge_0, _Real, coercive, coercivity, continuousLinearMapOfBilin_apply, real_inner_le_norm
-/
theorem bounded_below (coercive : IsCoercive B) : exists C, 0 < C ∧ forall v, C * ‖v‖ <= ‖B♯ v‖ := by
  rcases coercive with ⟨C, C_ge_0, coercivity⟩
  refine ⟨C, C_ge_0, ?_⟩
  intro v
  by_cases h : 0 < ‖v‖
  · refine (mul_le_mul_iff_left₀ h).mp ?_
    calc
      C * ‖v‖ * ‖v‖ <= B v v := coercivity v
      _ = ⟪B♯ v, v⟫_Real := (continuousLinearMapOfBilin_apply B v v).symm
      _ <= ‖B♯ v‖ * ‖v‖ := real_inner_le_norm (B♯ v) v
  · have : v = 0 := by simpa using h
    simp [this]

/--
theorem `antilipschitz` / 定理 `antilipschitz`

English:
theorem antilipschitz
  given: (coercive : IsCoercive B)
  statement: exists C : Real>=0, 0 < C ∧ AntilipschitzWith C B♯
  proof: by
  rcases coercive.bounded_below with ⟨C, C_pos, below_bound⟩
  refine ⟨C⁻¹.toNNReal, Real.toNNReal_pos.mpr (inv_pos.mpr C_pos), ?_⟩
  refine ContinuousLinearMap.antilipschitz_of_bound B♯ ?_
  simp_rw [Real.coe_toNNReal', max_eq_left_of_lt (inv_pos.mpr C_pos), ←
    inv_mul_le_iff₀ (inv_pos.mpr C_pos)]
  simpa using below_bound

中文:
定理 antilipschitz
  条件: (coercive : IsCoercive B)
  结论: 存在 C : 实数>=0, 0 < C ∧ AntilipschitzWith C B♯
  证明: by
  rcases coercive.bounded_below with ⟨C, C_pos, below_bound⟩
  refine ⟨C⁻¹.toNNReal, Real.toNNReal_pos.mpr (inv_pos.mpr C_pos), ?_⟩
  refine ContinuousLinearMap.antilipschitz_of_bound B♯ ?_
  simp_rw [Real.coe_toNNReal', max_eq_left_of_lt (inv_pos.mpr C_pos), ←
    inv_mul_le_iff₀ (inv_pos.mpr C_pos)]
  simpa using below_bound

Depends on / 依赖: C_pos, ContinuousLinearMap, ContinuousLinearMap.antilipschitz_of_bound, Real.coe_toNNReal, Real.toNNReal_pos.mpr, antilipschitz_of_bound, below_bound, bounded_below, coe_toNNReal, coercive, coercive.bounded_below, inv_pos, inv_pos.mpr, max_eq_left_of_lt, simp_rw, toNNReal, toNNReal_pos
-/
theorem antilipschitz (coercive : IsCoercive B) : exists C : Real>=0, 0 < C ∧ AntilipschitzWith C B♯ := by
  rcases coercive.bounded_below with ⟨C, C_pos, below_bound⟩
  refine ⟨C⁻¹.toNNReal, Real.toNNReal_pos.mpr (inv_pos.mpr C_pos), ?_⟩
  refine ContinuousLinearMap.antilipschitz_of_bound B♯ ?_
  simp_rw [Real.coe_toNNReal', max_eq_left_of_lt (inv_pos.mpr C_pos), ←
    inv_mul_le_iff₀ (inv_pos.mpr C_pos)]
  simpa using below_bound

/--
theorem `ker_eq_bot` / 定理 `ker_eq_bot`

English:
theorem ker_eq_bot
  given: (coercive : IsCoercive B)
  statement: B♯.ker = ⊥
  proof: by
  rw [LinearMap.ker_eq_bot]
  rcases coercive.antilipschitz with ⟨_, _, antilipschitz⟩
  exact antilipschitz.injective

中文:
定理 ker_eq_bot
  条件: (coercive : IsCoercive B)
  结论: B♯.ker = ⊥
  证明: by
  rw [LinearMap.ker_eq_bot]
  rcases coercive.antilipschitz with ⟨_, _, antilipschitz⟩
  exact antilipschitz.injective

Depends on / 依赖: LinearMap, LinearMap.ker_eq_bot, antilipschitz, antilipschitz.injective, coercive, coercive.antilipschitz, injective, ker_eq_bot
-/
theorem ker_eq_bot (coercive : IsCoercive B) : B♯.ker = ⊥ := by
  rw [LinearMap.ker_eq_bot]
  rcases coercive.antilipschitz with ⟨_, _, antilipschitz⟩
  exact antilipschitz.injective

/--
theorem `isClosed_range` / 定理 `isClosed_range`

English:
theorem isClosed_range
  given: (coercive : IsCoercive B)
  statement: IsClosed (B♯.range : Set V)
  proof: by
  rcases coercive.antilipschitz with ⟨_, _, antilipschitz⟩
  exact antilipschitz.isClosed_range B♯.uniformContinuous

中文:
定理 isClosed_range
  条件: (coercive : IsCoercive B)
  结论: 是闭集 (B♯.range : 集合 V)
  证明: by
  rcases coercive.antilipschitz with ⟨_, _, antilipschitz⟩
  exact antilipschitz.isClosed_range B♯.uniformContinuous

Depends on / 依赖: antilipschitz, antilipschitz.isClosed_range, coercive, coercive.antilipschitz, isClosed_range, uniformContinuous
-/
theorem isClosed_range (coercive : IsCoercive B) : IsClosed (B♯.range : Set V) := by
  rcases coercive.antilipschitz with ⟨_, _, antilipschitz⟩
  exact antilipschitz.isClosed_range B♯.uniformContinuous

/--
theorem `range_eq_top` / 定理 `range_eq_top`

English:
theorem range_eq_top
  given: (coercive : IsCoercive B)
  statement: B♯.range = ⊤
  proof: by
  have := coercive.isClosed_range.completeSpace_coe
  rw [← B♯.range.orthogonal_orthogonal]
  rw [Submodule.eq_top_iff']
  intro v w mem_w_orthogonal
  rcases coercive with ⟨C, C_pos, coercivity⟩
  obtain rfl : w = 0 := by
    rw [← norm_eq_zero]; rw [← mul_self_eq_zero]; rw [← mul_right_inj' C_pos.ne']; rw [mul_zero]; rw [←
      mul_assoc]
    apply le_antisymm
    · calc
        C * ‖w‖ * ‖w‖ <= B w w := coercivity w
        _ = ⟪B♯ w, w⟫_Real := (continuousLinearMapOfBilin_apply B w w).symm
        _ = 0 := mem_w_orthogonal _ ⟨w, rfl⟩
    · positivity
  exact inner_zero_left _

中文:
定理 range_eq_top
  条件: (coercive : IsCoercive B)
  结论: B♯.range = ⊤
  证明: by
  have := coercive.isClosed_range.completeSpace_coe
  rw [← B♯.range.orthogonal_orthogonal]
  rw [Submodule.eq_top_iff']
  intro v w mem_w_orthogonal
  rcases coercive with ⟨C, C_pos, coercivity⟩
  obtain rfl : w = 0 := by
    rw [← norm_eq_zero]; rw [← mul_self_eq_zero]; rw [← mul_right_inj' C_pos.ne']; rw [mul_zero]; rw [←
      mul_assoc]
    apply le_antisymm
    · calc
        C * ‖w‖ * ‖w‖ <= B w w := coercivity w
        _ = ⟪B♯ w, w⟫_Real := (continuousLinearMapOfBilin_apply B w w).symm
        _ = 0 := mem_w_orthogonal _ ⟨w, rfl⟩
    · positivity
  exact inner_zero_left _

Depends on / 依赖: C_pos, C_pos.ne, Submodule, Submodule.eq_top_iff, _Real, coercive, coercive.isClosed_range.completeSpace_coe, coercivity, completeSpace_coe, continuousLinearMapOfBilin_apply, eq_top_iff, isClosed_range, le_antisymm, mem_w_orthogonal, mul_assoc, mul_right_inj, mul_self_eq_zero, mul_zero, norm_eq_zero, orthogonal_orthogonal
-/
theorem range_eq_top (coercive : IsCoercive B) : B♯.range = ⊤ := by
  have := coercive.isClosed_range.completeSpace_coe
  rw [← B♯.range.orthogonal_orthogonal]
  rw [Submodule.eq_top_iff']
  intro v w mem_w_orthogonal
  rcases coercive with ⟨C, C_pos, coercivity⟩
  obtain rfl : w = 0 := by
    rw [← norm_eq_zero]; rw [← mul_self_eq_zero]; rw [← mul_right_inj' C_pos.ne']; rw [mul_zero]; rw [←
      mul_assoc]
    apply le_antisymm
    · calc
        C * ‖w‖ * ‖w‖ <= B w w := coercivity w
        _ = ⟪B♯ w, w⟫_Real := (continuousLinearMapOfBilin_apply B w w).symm
        _ = 0 := mem_w_orthogonal _ ⟨w, rfl⟩
    · positivity
  exact inner_zero_left _

/--
Definition of `continuousLinearEquivOfBilin` / `continuousLinearEquivOfBilin` 的定义

English:
definition continuousLinearEquivOfBilin
  signature: (coercive : IsCoercive B)
  body: ContinuousLinearEquiv.ofBijective B♯ coercive.ker_eq_bot coercive.range_eq_top

@[simp]

中文:
定义 continuousLinearEquivOfBilin
  签名: (coercive : IsCoercive B)
  定义体: ContinuousLinearEquiv.ofBijective B♯ coercive.ker_eq_bot coercive.range_eq_top

@[simp]

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.ofBijective, coercive, coercive.ker_eq_bot, coercive.range_eq_top, ker_eq_bot, ofBijective, range_eq_top
-/
def continuousLinearEquivOfBilin (coercive : IsCoercive B) : V ≃L[Real] V :=
  ContinuousLinearEquiv.ofBijective B♯ coercive.ker_eq_bot coercive.range_eq_top

@[simp]
/--
theorem `continuousLinearEquivOfBilin_apply` / 定理 `continuousLinearEquivOfBilin_apply`

English:
theorem continuousLinearEquivOfBilin_apply
  given: (coercive : IsCoercive B) (v w : V)
  proof: continuousLinearMapOfBilin_apply B v w

中文:
定理 continuousLinearEquivOfBilin_apply
  条件: (coercive : IsCoercive B) (v w : V)
  证明: continuousLinearMapOfBilin_apply B v w

Depends on / 依赖: continuousLinearMapOfBilin_apply
-/
theorem continuousLinearEquivOfBilin_apply (coercive : IsCoercive B) (v w : V) :
    ⟪coercive.continuousLinearEquivOfBilin v, w⟫_Real = B v w :=
  continuousLinearMapOfBilin_apply B v w

/--
theorem `unique_continuousLinearEquivOfBilin` / 定理 `unique_continuousLinearEquivOfBilin`

English:
theorem unique_continuousLinearEquivOfBilin
  statement: (coercive : IsCoercive B) {v f : V}
  proof: unique_continuousLinearMapOfBilin B is_lax_milgram

中文:
定理 unique_continuousLinearEquivOfBilin
  结论: (coercive : IsCoercive B) {v f : V}
  证明: unique_continuousLinearMapOfBilin B is_lax_milgram

Depends on / 依赖: is_lax_milgram, unique_continuousLinearMapOfBilin
-/
theorem unique_continuousLinearEquivOfBilin (coercive : IsCoercive B) {v f : V}
    (is_lax_milgram : forall w, ⟪f, w⟫_Real = B v w) : f = coercive.continuousLinearEquivOfBilin v :=
  unique_continuousLinearMapOfBilin B is_lax_milgram

end IsCoercive
