/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Support of the derivative of a function

In this file we prove that the (topological) support of a function includes the support of its
derivative. As a corollary, we show that the derivative of a function with compact support has
compact support.

## Keywords

derivative, support
-/

public section


universe u v

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {f : 𝕜 -> E} {x : 𝕜}

/-! ### Support of derivatives -/


section Support

open Function

/--
theorem `HasStrictDerivAt.of_notMem_tsupport` / 定理 `HasStrictDerivAt.of_notMem_tsupport`

English:
theorem HasStrictDerivAt.of_notMem_tsupport
  given: (h : x ∉ tsupport f)
  statement: HasStrictDerivAt f 0 x
  proof: by
  rw [notMem_tsupport_iff_eventuallyEq] at h
  exact (hasStrictDerivAt_const x 0).congr_of_eventuallyEq h.symm

中文:
定理 HasStrictDerivAt.of_notMem_tsupport
  条件: (h : x ∉ tsupport f)
  结论: HasStrictDerivAt f 0 x
  证明: by
  rw [notMem_tsupport_iff_eventuallyEq] at h
  exact (hasStrictDerivAt_const x 0).congr_of_eventuallyEq h.symm

Depends on / 依赖: congr_of_eventuallyEq, h.symm, hasStrictDerivAt_const, notMem_tsupport_iff_eventuallyEq
-/
theorem HasStrictDerivAt.of_notMem_tsupport (h : x ∉ tsupport f) : HasStrictDerivAt f 0 x := by
  rw [notMem_tsupport_iff_eventuallyEq] at h
  exact (hasStrictDerivAt_const x 0).congr_of_eventuallyEq h.symm

/--
theorem `HasDerivAt.of_notMem_tsupport` / 定理 `HasDerivAt.of_notMem_tsupport`

English:
theorem HasDerivAt.of_notMem_tsupport
  given: (h : x ∉ tsupport f)
  statement: HasDerivAt f 0 x
  proof: (HasStrictDerivAt.of_notMem_tsupport h).hasDerivAt

中文:
定理 HasDerivAt.of_notMem_tsupport
  条件: (h : x ∉ tsupport f)
  结论: HasDerivAt f 0 x
  证明: (HasStrictDerivAt.of_notMem_tsupport h).hasDerivAt

Depends on / 依赖: HasStrictDerivAt, HasStrictDerivAt.of_notMem_tsupport, hasDerivAt, of_notMem_tsupport
-/
theorem HasDerivAt.of_notMem_tsupport (h : x ∉ tsupport f) : HasDerivAt f 0 x :=
  (HasStrictDerivAt.of_notMem_tsupport h).hasDerivAt

/--
theorem `HasDerivWithinAt.of_notMem_tsupport` / 定理 `HasDerivWithinAt.of_notMem_tsupport`

English:
theorem HasDerivWithinAt.of_notMem_tsupport
  given: {s : Set 𝕜} (h : x ∉ tsupport f)
  proof: (HasDerivAt.of_notMem_tsupport h).hasDerivWithinAt

中文:
定理 HasDerivWithinAt.of_notMem_tsupport
  条件: {s : Set 𝕜} (h : x ∉ tsupport f)
  证明: (HasDerivAt.of_notMem_tsupport h).hasDerivWithinAt

Depends on / 依赖: HasDerivAt, HasDerivAt.of_notMem_tsupport, hasDerivWithinAt, of_notMem_tsupport
-/
theorem HasDerivWithinAt.of_notMem_tsupport {s : Set 𝕜} (h : x ∉ tsupport f) :
    HasDerivWithinAt f 0 s x :=
  (HasDerivAt.of_notMem_tsupport h).hasDerivWithinAt

/--
theorem `deriv_of_notMem_tsupport` / 定理 `deriv_of_notMem_tsupport`

English:
theorem deriv_of_notMem_tsupport
  given: (h : x ∉ tsupport f)
  statement: deriv f x = 0
  proof: by
  rw [notMem_tsupport_iff_eventuallyEq] at h
  simp [h.deriv_eq]

中文:
定理 deriv_of_notMem_tsupport
  条件: (h : x ∉ tsupport f)
  结论: deriv f x = 0
  证明: by
  rw [notMem_tsupport_iff_eventuallyEq] at h
  simp [h.deriv_eq]

Depends on / 依赖: deriv_eq, h.deriv_eq, notMem_tsupport_iff_eventuallyEq
-/
theorem deriv_of_notMem_tsupport (h : x ∉ tsupport f) : deriv f x = 0 := by
  rw [notMem_tsupport_iff_eventuallyEq] at h
  simp [h.deriv_eq]

/--
theorem `support_deriv_subset` / 定理 `support_deriv_subset`

English:
theorem support_deriv_subset
  statement: support (deriv f) subseteq tsupport f
  proof: fun x => by
  rw [← not_imp_not]; rw [notMem_support]
  exact deriv_of_notMem_tsupport

中文:
定理 support_deriv_subset
  结论: support (deriv f) subseteq tsupport f
  证明: fun x => by
  rw [← not_imp_not]; rw [notMem_support]
  exact deriv_of_notMem_tsupport

Depends on / 依赖: deriv_of_notMem_tsupport, notMem_support, not_imp_not
-/
theorem support_deriv_subset : support (deriv f) subseteq tsupport f := fun x => by
  rw [← not_imp_not]; rw [notMem_support]
  exact deriv_of_notMem_tsupport

/--
theorem `tsupport_deriv_subset` / 定理 `tsupport_deriv_subset`

English:
theorem tsupport_deriv_subset
  statement: tsupport (deriv f) subseteq tsupport f
  proof: closure_minimal support_deriv_subset isClosed_closure

中文:
定理 tsupport_deriv_subset
  结论: tsupport (deriv f) subseteq tsupport f
  证明: closure_minimal support_deriv_subset isClosed_closure

Depends on / 依赖: closure_minimal, isClosed_closure, support_deriv_subset
-/
theorem tsupport_deriv_subset : tsupport (deriv f) subseteq tsupport f :=
  closure_minimal support_deriv_subset isClosed_closure

/--
theorem `HasCompactSupport.deriv` / 定理 `HasCompactSupport.deriv`

English:
theorem HasCompactSupport.deriv
  given: (hf : HasCompactSupport f)
  proof: hf.mono' support_deriv_subset

中文:
定理 HasCompactSupport.deriv
  条件: (hf : HasCompactSupport f)
  证明: hf.mono' support_deriv_subset
-/
protected theorem HasCompactSupport.deriv (hf : HasCompactSupport f) :
    HasCompactSupport (deriv f) :=
  hf.mono' support_deriv_subset

end Support
