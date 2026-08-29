/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Smooth bump functions in inner product spaces

In this file we prove that a real inner product space has smooth bump functions,
see `hasContDiffBump_of_innerProductSpace`.

## Keywords

smooth function, bump function, inner product space
-/

@[expose] public section

open Function Real
open scoped Topology

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace Real E]

/--
Definition of `ContDiffBumpBase.ofInnerProductSpace` / `ContDiffBumpBase.ofInnerProductSpace` 的定义

English:
definition ContDiffBumpBase.ofInnerProductSpace
  signature: : ContDiffBumpBase E where
  body: smoothTransition ((R - ‖x‖) / (R - 1))
  mem_Icc _ _ := ⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩
  symmetric _ _ := by simp only [norm_neg]
  smooth := by
    rintro ⟨R, x⟩ ⟨hR : 1 < R, -⟩
    apply ContDiffAt.contDiffWithinAt
    rw [← sub_pos] at hR
    rcases eq_or_ne x 0 with rfl |

中文:
定义 ContDiffBumpBase.ofInnerProductSpace
  签名: : ContDiffBumpBase E where
  定义体: smoothTransition ((R - ‖x‖) / (R - 1))
  mem_Icc _ _ := ⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩
  symmetric _ _ := by simp only [norm_neg]
  smooth := by
    rintro ⟨R, x⟩ ⟨hR : 1 < R, -⟩
    apply ContDiffAt.contDiffWithinAt
    rw [← sub_pos] at hR
    rcases eq_or_ne x 0 with rfl |

Depends on / 依赖: smoothTransition
-/
noncomputable def ContDiffBumpBase.ofInnerProductSpace : ContDiffBumpBase E where
  toFun R x := smoothTransition ((R - ‖x‖) / (R - 1))
  mem_Icc _ _ := ⟨smoothTransition.nonneg _, smoothTransition.le_one _⟩
  symmetric _ _ := by simp only [norm_neg]
  smooth := by
    rintro ⟨R, x⟩ ⟨hR : 1 < R, -⟩
    apply ContDiffAt.contDiffWithinAt
    rw [← sub_pos] at hR
    rcases eq_or_ne x 0 with rfl | hx
    · have A : ContinuousAt (fun p : Real × E => (p.1 - ‖p.2‖) / (p.1 - 1)) (R, 0) := by
        fun_prop (disch := positivity)
      have B : forallᶠ p in 𝓝 (R, (0 : E)), 1 <= (p.1 - ‖p.2‖) / (p.1 - 1) :=
A.eventually le_mem_nhds (one_lt_div hR).2 sub_lt_sub_left (by simp) _
refine (contDiffAt_const (c := 1)).congr_of_eventuallyEq B.mono fun _ =>
        smoothTransition.one_of_one_le
    · refine smoothTransition.contDiffAt.comp _ (ContDiffAt.div ?_ (by fun_prop) hR.ne')
      exact contDiffAt_fst.sub (contDiffAt_snd.norm Real hx)
eq_one _ hR _ hx := smoothTransition.one_of_one_le (one_le_div <| sub_pos.2 hR).2
    sub_le_sub_left hx _
  support R hR := by
    ext x
    rw [mem_support]; rw [Ne]; rw [smoothTransition.zero_iff_nonpos]; rw [not_le]; rw [mem_ball_zero_iff]
    simp [hR]

/-- Any inner product space has smooth bump functions. -/
instance (priority := 100) hasContDiffBump_of_innerProductSpace : HasContDiffBump E :=
  ⟨⟨.ofInnerProductSpace E⟩⟩
