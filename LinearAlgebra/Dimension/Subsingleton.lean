/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kim Morrison, Eric Wieser, Junyan Xu, Andrew Yang
-/
module

public import Mathlib.LinearAlgebra.Dimension.Basic

/-!
# Dimension of trivial modules
-/

public section

variable (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M]

section

variable [Nontrivial R]

/--
theorem `rank_subsingleton'` / 定理 `rank_subsingleton'`

English:
theorem rank_subsingleton'
  given: [Subsingleton M]
  statement: Module.rank R M = 0
  proof: by
  rw [Module.rank]; rw [← bot_eq_zero]; rw [eq_bot_iff]
  exact ciSup_le fun s => by simp [(linearIndependent_subsingleton_iff _).mp s.2]

中文:
定理 rank_subsingleton'
  条件: [Subsingleton M]
  结论: Module.rank R M = 0
  证明: by
  rw [Module.rank]; rw [← bot_eq_zero]; rw [eq_bot_iff]
  exact ciSup_le fun s => by simp [(linearIndependent_subsingleton_iff _).mp s.2]

Depends on / 依赖: _mono_enorm_ae, eLpNorm, enorm_le_iff_norm_le
-/
@[simp, nontriviality] theorem rank_subsingleton' [Subsingleton M] : Module.rank R M = 0 := by
  rw [Module.rank]; rw [← bot_eq_zero]; rw [eq_bot_iff]
  exact ciSup_le fun s => by simp [(linearIndependent_subsingleton_iff _).mp s.2]

/--
theorem `rank_punit` / 定理 `rank_punit`

English:
theorem rank_punit
  statement: Module.rank R PUnit = 0
  proof: rank_subsingleton' _ _

中文:
定理 rank_punit
  结论: Module.rank R PUnit = 0
  证明: rank_subsingleton' _ _

Depends on / 依赖: _eq_lintegral_enorm, eLpNorm, hfg.mono, lintegral_congr_ae, rank_subsingleton
-/
theorem rank_punit : Module.rank R PUnit = 0 := rank_subsingleton' _ _

/--
theorem `rank_bot` / 定理 `rank_bot`

English:
theorem rank_bot
  statement: Module.rank R (⊥ : Submodule R M) = 0
  proof: rank_subsingleton' _ _

中文:
定理 rank_bot
  结论: Module.rank R (⊥ : Submodule R M) = 0
  证明: rank_subsingleton' _ _

Depends on / 依赖: _eq_lintegral_enorm, eLpNorm, hfg.mono, lintegral_congr_ae, rank_subsingleton
-/
theorem rank_bot : Module.rank R (⊥ : Submodule R M) = 0 := rank_subsingleton' _ _

end
