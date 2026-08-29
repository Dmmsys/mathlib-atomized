/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set
public import Mathlib.Algebra.Notation.Support

/-!
# Support of a function composed with a scalar action

We show that the support of `x ↦ f (c⁻¹ • x)` is equal to `c • support f`.
-/

public section


open scoped Pointwise

open Function Set

section Group

variable {α β γ : Type*} [Group α] [MulAction α β]

/--
theorem `mulSupport_comp_inv_smul` / 定理 `mulSupport_comp_inv_smul`

English:
theorem mulSupport_comp_inv_smul
  given: [One γ] (c : α) (f : β -> γ)
  proof: by
  ext x
  simp only [mem_smul_set_iff_inv_smul_mem, mem_mulSupport]

中文:
定理 mulSupport_comp_inv_smul
  条件: [One γ] (c : α) (f : β -> γ)
  证明: by
  ext x
  simp only [mem_smul_set_iff_inv_smul_mem, mem_mulSupport]

Depends on / 依赖: mem_mulSupport, mem_smul_set_iff_inv_smul_mem
-/
theorem mulSupport_comp_inv_smul [One γ] (c : α) (f : β -> γ) :
    (mulSupport fun x => f (c⁻¹ • x)) = c • mulSupport f := by
  ext x
  simp only [mem_smul_set_iff_inv_smul_mem, mem_mulSupport]

/--
theorem `support_comp_inv_smul` / 定理 `support_comp_inv_smul`

English:
theorem support_comp_inv_smul
  given: [Zero γ] (c : α) (f : β -> γ)
  proof: by
  ext x
  simp only [mem_smul_set_iff_inv_smul_mem, mem_support]

中文:
定理 support_comp_inv_smul
  条件: [Zero γ] (c : α) (f : β -> γ)
  证明: by
  ext x
  simp only [mem_smul_set_iff_inv_smul_mem, mem_support]

Depends on / 依赖: mem_smul_set_iff_inv_smul_mem, mem_support
-/
theorem support_comp_inv_smul [Zero γ] (c : α) (f : β -> γ) :
    (support fun x => f (c⁻¹ • x)) = c • support f := by
  ext x
  simp only [mem_smul_set_iff_inv_smul_mem, mem_support]

end Group

section GroupWithZero

variable {α β γ : Type*} [GroupWithZero α] [MulAction α β]

/--
theorem `mulSupport_comp_inv_smul₀` / 定理 `mulSupport_comp_inv_smul₀`

English:
theorem mulSupport_comp_inv_smul₀
  given: [One γ] {c : α} (hc : c != 0) (f : β -> γ)
  proof: by
  ext x
  simp only [mem_smul_set_iff_inv_smul_mem₀ hc, mem_mulSupport]

中文:
定理 mulSupport_comp_inv_smul₀
  条件: [One γ] {c : α} (hc : c != 0) (f : β -> γ)
  证明: by
  ext x
  simp only [mem_smul_set_iff_inv_smul_mem₀ hc, mem_mulSupport]

Depends on / 依赖: mem_mulSupport
-/
theorem mulSupport_comp_inv_smul₀ [One γ] {c : α} (hc : c != 0) (f : β -> γ) :
    (mulSupport fun x => f (c⁻¹ • x)) = c • mulSupport f := by
  ext x
  simp only [mem_smul_set_iff_inv_smul_mem₀ hc, mem_mulSupport]

/--
theorem `support_comp_inv_smul₀` / 定理 `support_comp_inv_smul₀`

English:
theorem support_comp_inv_smul₀
  given: [Zero γ] {c : α} (hc : c != 0) (f : β -> γ)
  proof: by
  ext x
  simp only [mem_smul_set_iff_inv_smul_mem₀ hc, mem_support]

中文:
定理 support_comp_inv_smul₀
  条件: [Zero γ] {c : α} (hc : c != 0) (f : β -> γ)
  证明: by
  ext x
  simp only [mem_smul_set_iff_inv_smul_mem₀ hc, mem_support]

Depends on / 依赖: mem_support
-/
theorem support_comp_inv_smul₀ [Zero γ] {c : α} (hc : c != 0) (f : β -> γ) :
    (support fun x => f (c⁻¹ • x)) = c • support f := by
  ext x
  simp only [mem_smul_set_iff_inv_smul_mem₀ hc, mem_support]

end GroupWithZero
