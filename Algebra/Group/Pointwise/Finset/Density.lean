/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Pointwise.Finset.Scalar
public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Finset.Density

/-!
# Theorems about the density of pointwise operations on finsets.
-/

public section

open scoped Pointwise

variable {α β : Type*}

namespace Finset

variable [DecidableEq α] [InvolutiveInv α] {s : Finset α} {a : α} in
@[to_additive (attr := simp)]
/--
lemma `dens_inv` / 引理 `dens_inv`

English:
lemma dens_inv
  given: [Fintype α] (s : Finset α)
  statement: s⁻¹.dens = s.dens
  proof: by simp [dens]

中文:
引理 dens_inv
  条件: [有限类型 α] (s : 有限集 α)
  结论: s⁻¹.dens = s.dens
  证明: by simp [dens]
-/
lemma dens_inv [Fintype α] (s : Finset α) : s⁻¹.dens = s.dens := by simp [dens]

variable [DecidableEq β] [Group α] [MulAction α β] {s t : Finset β} {a : α} {b : β} in
@[to_additive (attr := simp)]
/--
lemma `dens_smul_finset` / 引理 `dens_smul_finset`

English:
lemma dens_smul_finset
  given: [Fintype β] (a : α) (s : Finset β)
  statement: (a • s).dens = s.dens
  proof: by simp [dens]

中文:
引理 dens_smul_finset
  条件: [有限类型 β] (a : α) (s : 有限集 β)
  结论: (a • s).dens = s.dens
  证明: by simp [dens]
-/
lemma dens_smul_finset [Fintype β] (a : α) (s : Finset β) : (a • s).dens = s.dens := by simp [dens]

end Finset
