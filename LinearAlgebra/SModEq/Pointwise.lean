/-
Copyright (c) 2025 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/
module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.LinearAlgebra.SModEq.Basic

/-!
# Pointwise lemmas for modular equivalence

In this file, we record more lemmas about `SModEq` on elements
of modules or rings.
-/

public section

open Submodule

open Polynomial

variable {R : Type*} [Ring R] {I : Ideal R}
variable {M : Type*} [AddCommGroup M] [Module R M] {U : Submodule R M}
variable {x y : M}

namespace SModEq

/--
theorem `smul'` / 定理 `smul'`

English:
theorem smul'
  statement: (hxy : x ≡ y [SMOD U])
  proof: by
  rw [SModEq.sub_mem] at hxy ⊢
  rw [← smul_sub]
  exact smul_mem_smul hc hxy

中文:
定理 smul'
  结论: (hxy : x ≡ y [SMOD U])
  证明: by
  rw [SModEq.sub_mem] at hxy ⊢
  rw [← smul_sub]
  exact smul_mem_smul hc hxy

Depends on / 依赖: SModEq, SModEq.sub_mem, smul_mem_smul, smul_sub, sub_mem
-/
theorem smul' (hxy : x ≡ y [SMOD U])
    {c : R} (hc : c in I) : c • x ≡ c • y [SMOD (I • U)] := by
  rw [SModEq.sub_mem] at hxy ⊢
  rw [← smul_sub]
  exact smul_mem_smul hc hxy

end SModEq
