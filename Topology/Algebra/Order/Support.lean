/-
Copyright (c) 2025 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
module

public import Mathlib.Algebra.Order.Group.Indicator
public import Mathlib.Topology.Algebra.Support

/-!
# The topological support of sup and inf of functions

In a topological space `X` and a space `M` with `Sup` structure, for `f g : X → M` with compact
support, we show that `f ⊔ g` has compact support. Similarly, in `β` with `Inf` structure, `f ⊓ g`
has compact support if so do `f` and `g`.

-/

public section

variable {X M : Type*} [TopologicalSpace X] [One M]

section SemilatticeSup

variable [SemilatticeSup M]

@[to_additive]
/--
theorem `HasCompactMulSupport.sup` / 定理 `HasCompactMulSupport.sup`

English:
theorem HasCompactMulSupport.sup
  statement: {f g : X -> M} (hf : HasCompactMulSupport f)
  proof: by
  apply IsCompact.of_isClosed_subset (IsCompact.union hf hg) (isClosed_mulTSupport _)
  rw [mulTSupport]; rw [mulTSupport]; rw [mulTSupport]; rw [← closure_union]
  apply closure_mono
  exact Function.mulSupport_sup f g

中文:
定理 HasCompactMulSupport.上确界
  结论: {f g : X -> M} (hf : HasCompactMulSupport f)
  证明: by
  apply IsCompact.of_isClosed_subset (IsCompact.union hf hg) (isClosed_mulTSupport _)
  rw [mulTSupport]; rw [mulTSupport]; rw [mulTSupport]; rw [← closure_union]
  apply closure_mono
  exact Function.mulSupport_sup f g

Depends on / 依赖: Function, Function.mulSupport_sup, IsCompact, IsCompact.of_isClosed_subset, IsCompact.union, closure_mono, closure_union, isClosed_mulTSupport, mulSupport_sup, mulTSupport, of_isClosed_subset
-/
theorem HasCompactMulSupport.sup {f g : X -> M} (hf : HasCompactMulSupport f)
    (hg : HasCompactMulSupport g) : HasCompactMulSupport (f ⊔ g) := by
  apply IsCompact.of_isClosed_subset (IsCompact.union hf hg) (isClosed_mulTSupport _)
  rw [mulTSupport]; rw [mulTSupport]; rw [mulTSupport]; rw [← closure_union]
  apply closure_mono
  exact Function.mulSupport_sup f g

end SemilatticeSup

section SemilatticeInf

variable [SemilatticeInf M]

@[to_additive]
/--
theorem `HasCompactMulSupport.inf` / 定理 `HasCompactMulSupport.inf`

English:
theorem HasCompactMulSupport.inf
  statement: {f g : X -> M} (hf : HasCompactMulSupport f)
  proof: by
  apply IsCompact.of_isClosed_subset (IsCompact.union hf hg) (isClosed_mulTSupport _)
  rw [mulTSupport]; rw [mulTSupport]; rw [mulTSupport]; rw [← closure_union]
  apply closure_mono
  exact Function.mulSupport_inf f g

中文:
定理 HasCompactMulSupport.下确界
  结论: {f g : X -> M} (hf : HasCompactMulSupport f)
  证明: by
  apply IsCompact.of_isClosed_subset (IsCompact.union hf hg) (isClosed_mulTSupport _)
  rw [mulTSupport]; rw [mulTSupport]; rw [mulTSupport]; rw [← closure_union]
  apply closure_mono
  exact Function.mulSupport_inf f g

Depends on / 依赖: Function, Function.mulSupport_inf, IsCompact, IsCompact.of_isClosed_subset, IsCompact.union, closure_mono, closure_union, isClosed_mulTSupport, mulSupport_inf, mulTSupport, of_isClosed_subset
-/
theorem HasCompactMulSupport.inf {f g : X -> M} (hf : HasCompactMulSupport f)
    (hg : HasCompactMulSupport g) : HasCompactMulSupport (f ⊓ g) := by
  apply IsCompact.of_isClosed_subset (IsCompact.union hf hg) (isClosed_mulTSupport _)
  rw [mulTSupport]; rw [mulTSupport]; rw [mulTSupport]; rw [← closure_union]
  apply closure_mono
  exact Function.mulSupport_inf f g

end SemilatticeInf
