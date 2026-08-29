/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Analysis.Normed.Algebra.TrivSqZeroExt

/-!
# Results on `DualNumber R` related to the norm

These are just restatements of similar statements about `TrivSqZeroExt R M`.

## Main results

* `exp_eps`

-/

public section

open NormedSpace -- For `NormedSpace.exp`.

namespace DualNumber

open TrivSqZeroExt

variable {R : Type*}
variable [CommRing R] [Algebra Rat R]
variable [UniformSpace R] [IsTopologicalRing R] [T2Space R]

@[simp]
/--
theorem `exp_eps` / 定理 `exp_eps`

English:
theorem exp_eps
  statement: exp (eps : DualNumber R) = 1 + eps
  proof: exp_inr _

@[simp]

中文:
定理 exp_eps
  结论: exp (eps : DualNumber R) = 1 + eps
  证明: exp_inr _

@[simp]

Depends on / 依赖: exp_inr
-/
theorem exp_eps : exp (eps : DualNumber R) = 1 + eps :=
  exp_inr _

@[simp]
/--
theorem `exp_smul_eps` / 定理 `exp_smul_eps`

English:
theorem exp_smul_eps
  given: (r : R)
  statement: exp (r • eps : DualNumber R) = 1 + r • eps
  proof: by
  rw [eps]; rw [← inr_smul]; rw [exp_inr]

中文:
定理 exp_smul_eps
  条件: (r : R)
  结论: exp (r • eps : DualNumber R) = 1 + r • eps
  证明: by
  rw [eps]; rw [← inr_smul]; rw [exp_inr]

Depends on / 依赖: exp_inr, inr_smul
-/
theorem exp_smul_eps (r : R) : exp (r • eps : DualNumber R) = 1 + r • eps := by
  rw [eps]; rw [← inr_smul]; rw [exp_inr]

end DualNumber
