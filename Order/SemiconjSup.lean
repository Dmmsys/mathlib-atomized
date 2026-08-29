/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.Order.Group.End
public import Mathlib.Logic.Function.Conjugate
public import Mathlib.Order.Bounds.OrderIso
public import Mathlib.Order.OrdContinuous

/-!
# Semiconjugate by `sSup`

In this file we prove two facts about semiconjugate (families of) functions.

First, if an order isomorphism `fa : α → α` is semiconjugate to an order embedding `fb : β → β` by
`g : α → β`, then `fb` is semiconjugate to `fa` by `y ↦ sSup {x | g x ≤ y}`, see
`Semiconj.symm_adjoint`.

Second, consider two actions `f₁ f₂ : G → α → α` of a group on a complete lattice by order
isomorphisms. Then the map `x ↦ ⨆ g : G, (f₁ g)⁻¹ (f₂ g x)` semiconjugates each `f₁ g'` to `f₂ g'`,
see `Function.sSup_div_semiconj`. In the case of a conditionally complete lattice, a similar
statement holds true under an additional assumption that each set `{(f₁ g)⁻¹ (f₂ g x) | g : G}` is
bounded above, see `Function.csSup_div_semiconj`.

The lemmas come from [Étienne Ghys, Groupes d'homéomorphismes du cercle et cohomologie
bornée][ghys87:groupes], Proposition 2.1 and 5.4 respectively. In the paper they are formulated for
homeomorphisms of the circle, so in order to apply results from this file one has to lift these
homeomorphisms to the real line first.
-/

@[expose] public section

-- Guard against import creep
assert_not_exists Finset

variable {α β γ : Type*}

open Set

/--
Definition of `IsOrderRightAdjoint` / `IsOrderRightAdjoint` 的定义

English:
definition IsOrderRightAdjoint
  signature: [Preorder α] [Preorder β] (f : α -> β) (g : β -> α)
  body: forall y, IsLUB { x | f x <= y } (g y)

中文:
定义 IsOrderRightAdjoint
  签名: [Preorder α] [Preorder β] (f : α -> β) (g : β -> α)
  定义体: forall y, IsLUB { x | f x <= y } (g y)
-/
def IsOrderRightAdjoint [Preorder α] [Preorder β] (f : α -> β) (g : β -> α) :=
  forall y, IsLUB { x | f x <= y } (g y)

/--
theorem `isOrderRightAdjoint_sSup` / 定理 `isOrderRightAdjoint_sSup`

English:
theorem isOrderRightAdjoint_sSup
  given: [CompleteSemilatticeSup α] [Preorder β] (f : α -> β)
  proof: fun _ => isLUB_sSup _

中文:
定理 isOrderRightAdjoint_sSup
  条件: [CompleteSemilatticeSup α] [Preorder β] (f : α -> β)
  证明: fun _ => isLUB_sSup _

Depends on / 依赖: isLUB_sSup
-/
theorem isOrderRightAdjoint_sSup [CompleteSemilatticeSup α] [Preorder β] (f : α -> β) :
    IsOrderRightAdjoint f fun y => sSup { x | f x <= y } := fun _ => isLUB_sSup _

/--
theorem `isOrderRightAdjoint_csSup` / 定理 `isOrderRightAdjoint_csSup`

English:
theorem isOrderRightAdjoint_csSup
  statement: [ConditionallyCompleteLattice α] [Preorder β] (f : α -> β)
  proof: fun y => isLUB_csSup (hne y) (hbdd y)

中文:
定理 isOrderRightAdjoint_csSup
  结论: [ConditionallyCompleteLattice α] [Preorder β] (f : α -> β)
  证明: fun y => isLUB_csSup (hne y) (hbdd y)

Depends on / 依赖: isLUB_csSup
-/
theorem isOrderRightAdjoint_csSup [ConditionallyCompleteLattice α] [Preorder β] (f : α -> β)
    (hne : forall y, exists x, f x <= y) (hbdd : forall y, BddAbove { x | f x <= y }) :
    IsOrderRightAdjoint f fun y => sSup { x | f x <= y } := fun y => isLUB_csSup (hne y) (hbdd y)

namespace IsOrderRightAdjoint

/--
theorem `unique` / 定理 `unique`

English:
theorem unique
  statement: [PartialOrder α] [Preorder β] {f : α -> β} {g₁ g₂ : β -> α}
  proof: funext fun y => (h₁ y).unique (h₂ y)

中文:
定理 unique
  结论: [PartialOrder α] [Preorder β] {f : α -> β} {g₁ g₂ : β -> α}
  证明: funext fun y => (h₁ y).unique (h₂ y)
-/
protected theorem unique [PartialOrder α] [Preorder β] {f : α -> β} {g₁ g₂ : β -> α}
    (h₁ : IsOrderRightAdjoint f g₁) (h₂ : IsOrderRightAdjoint f g₂) : g₁ = g₂ :=
  funext fun y => (h₁ y).unique (h₂ y)

/--
theorem `right_mono` / 定理 `right_mono`

English:
theorem right_mono
  given: [Preorder α] [Preorder β] {f : α -> β} {g : β -> α} (h : IsOrderRightAdjoint f g)
  proof: fun y₁ y₂ hy => ((h y₁).mono (h y₂)) fun _ hx => le_trans hx hy

中文:
定理 right_mono
  条件: [Preorder α] [Preorder β] {f : α -> β} {g : β -> α} (h : IsOrderRightAdjoint f g)
  证明: fun y₁ y₂ hy => ((h y₁).mono (h y₂)) fun _ hx => le_trans hx hy

Depends on / 依赖: le_trans
-/
theorem right_mono [Preorder α] [Preorder β] {f : α -> β} {g : β -> α} (h : IsOrderRightAdjoint f g) :
    Monotone g := fun y₁ y₂ hy => ((h y₁).mono (h y₂)) fun _ hx => le_trans hx hy

/--
theorem `orderIso_comp` / 定理 `orderIso_comp`

English:
theorem orderIso_comp
  statement: [Preorder α] [Preorder β] [Preorder γ] {f : α -> β} {g : β -> α}
  proof: fun y => by simpa [e.le_symm_apply] using h (e.symm y)

中文:
定理 orderIso_comp
  结论: [Preorder α] [Preorder β] [Preorder γ] {f : α -> β} {g : β -> α}
  证明: fun y => by simpa [e.le_symm_apply] using h (e.symm y)

Depends on / 依赖: e.le_symm_apply, e.symm, le_symm_apply
-/
theorem orderIso_comp [Preorder α] [Preorder β] [Preorder γ] {f : α -> β} {g : β -> α}
    (h : IsOrderRightAdjoint f g) (e : β ≃o γ) : IsOrderRightAdjoint (e ∘ f) (g ∘ e.symm) :=
  fun y => by simpa [e.le_symm_apply] using h (e.symm y)

/--
theorem `comp_orderIso` / 定理 `comp_orderIso`

English:
theorem comp_orderIso
  statement: [Preorder α] [Preorder β] [Preorder γ] {f : α -> β} {g : β -> α}
  proof: by
  intro y
  change IsLUB (e ⁻¹' { x | f x <= y }) (e.symm (g y))
  rw [e.isLUB_preimage]; rw [e.apply_symm_apply]
  exact h y

中文:
定理 comp_orderIso
  结论: [Preorder α] [Preorder β] [Preorder γ] {f : α -> β} {g : β -> α}
  证明: by
  intro y
  change IsLUB (e ⁻¹' { x | f x <= y }) (e.symm (g y))
  rw [e.isLUB_preimage]; rw [e.apply_symm_apply]
  exact h y

Depends on / 依赖: apply_symm_apply, e.apply_symm_apply, e.isLUB_preimage, e.symm, isLUB_preimage
-/
theorem comp_orderIso [Preorder α] [Preorder β] [Preorder γ] {f : α -> β} {g : β -> α}
    (h : IsOrderRightAdjoint f g) (e : γ ≃o α) : IsOrderRightAdjoint (f ∘ e) (e.symm ∘ g) := by
  intro y
  change IsLUB (e ⁻¹' { x | f x <= y }) (e.symm (g y))
  rw [e.isLUB_preimage]; rw [e.apply_symm_apply]
  exact h y

end IsOrderRightAdjoint

namespace Function

/--
theorem `Semiconj.symm_adjoint` / 定理 `Semiconj.symm_adjoint`

English:
theorem Semiconj.symm_adjoint
  statement: [PartialOrder α] [Preorder β] {fa : α ≃o α} {fb : β ↪o β} {g : α -> β}
  proof: by
  refine fun y => (hg' _).unique ?_
  rw [← fa.surjective.image_preimage { x | g x <= fb y }]; rw [preimage_ofPred_eq]
  simp only [h.eq, fb.le_iff_le, fa.isLUB_image'.mpr (hg' _)]

中文:
定理 Semiconj.symm_adjoint
  结论: [PartialOrder α] [Preorder β] {fa : α ≃o α} {fb : β ↪o β} {g : α -> β}
  证明: by
  refine fun y => (hg' _).unique ?_
  rw [← fa.surjective.image_preimage { x | g x <= fb y }]; rw [preimage_ofPred_eq]
  simp only [h.eq, fb.le_iff_le, fa.isLUB_image'.mpr (hg' _)]

Depends on / 依赖: fa.isLUB_image, fa.surjective.image_preimage, fb.le_iff_le, h.eq, image_preimage, isLUB_image, le_iff_le, preimage_ofPred_eq, surjective, unique
-/
theorem Semiconj.symm_adjoint [PartialOrder α] [Preorder β] {fa : α ≃o α} {fb : β ↪o β} {g : α -> β}
    (h : Function.Semiconj g fa fb) {g' : β -> α} (hg' : IsOrderRightAdjoint g g') :
    Function.Semiconj g' fb fa := by
  refine fun y => (hg' _).unique ?_
  rw [← fa.surjective.image_preimage { x | g x <= fb y }]; rw [preimage_ofPred_eq]
  simp only [h.eq, fb.le_iff_le, fa.isLUB_image'.mpr (hg' _)]

variable {G : Type*}

/--
theorem `semiconj_of_isLUB` / 定理 `semiconj_of_isLUB`

English:
theorem semiconj_of_isLUB
  statement: [PartialOrder α] [Group G] (f₁ f₂ : G ->* α ≃o α) {h : α -> α}
  proof: by
  refine fun y => (H _).unique ?_
  have := (f₁ g).isLUB_image'.mpr (H y)
  rw [← range_comp]; rw [← (Equiv.mulRight g).surjective.range_comp _] at this
  simpa [comp_def] using this

中文:
定理 semiconj_of_isLUB
  结论: [PartialOrder α] [Group G] (f₁ f₂ : G ->* α ≃o α) {h : α -> α}
  证明: by
  refine fun y => (H _).unique ?_
  have := (f₁ g).isLUB_image'.mpr (H y)
  rw [← range_comp]; rw [← (Equiv.mulRight g).surjective.range_comp _] at this
  simpa [comp_def] using this

Depends on / 依赖: Equiv.mulRight, comp_def, isLUB_image, mulRight, range_comp, surjective, surjective.range_comp, unique
-/
theorem semiconj_of_isLUB [PartialOrder α] [Group G] (f₁ f₂ : G ->* α ≃o α) {h : α -> α}
    (H : forall x, IsLUB (range fun g' => (f₁ g')⁻¹ (f₂ g' x)) (h x)) (g : G) :
    Function.Semiconj h (f₂ g) (f₁ g) := by
  refine fun y => (H _).unique ?_
  have := (f₁ g).isLUB_image'.mpr (H y)
  rw [← range_comp]; rw [← (Equiv.mulRight g).surjective.range_comp _] at this
  simpa [comp_def] using this

/--
theorem `sSup_div_semiconj` / 定理 `sSup_div_semiconj`

English:
theorem sSup_div_semiconj
  given: [CompleteLattice α] [Group G] (f₁ f₂ : G ->* α ≃o α) (g : G)
  proof: semiconj_of_isLUB f₁ f₂ (fun _ => isLUB_iSup) _

中文:
定理 sSup_div_semiconj
  条件: [CompleteLattice α] [Group G] (f₁ f₂ : G ->* α ≃o α) (g : G)
  证明: semiconj_of_isLUB f₁ f₂ (fun _ => isLUB_iSup) _

Depends on / 依赖: isLUB_iSup, semiconj_of_isLUB
-/
theorem sSup_div_semiconj [CompleteLattice α] [Group G] (f₁ f₂ : G ->* α ≃o α) (g : G) :
    Function.Semiconj (fun x => ⨆ g' : G, (f₁ g')⁻¹ (f₂ g' x)) (f₂ g) (f₁ g) :=
  semiconj_of_isLUB f₁ f₂ (fun _ => isLUB_iSup) _

/--
theorem `csSup_div_semiconj` / 定理 `csSup_div_semiconj`

English:
theorem csSup_div_semiconj
  statement: [ConditionallyCompleteLattice α] [Group G] (f₁ f₂ : G ->* α ≃o α)
  proof: semiconj_of_isLUB f₁ f₂ (fun x => isLUB_csSup (range_nonempty _) (hbdd x)) _

中文:
定理 csSup_div_semiconj
  结论: [ConditionallyCompleteLattice α] [Group G] (f₁ f₂ : G ->* α ≃o α)
  证明: semiconj_of_isLUB f₁ f₂ (fun x => isLUB_csSup (range_nonempty _) (hbdd x)) _

Depends on / 依赖: isLUB_csSup, range_nonempty, semiconj_of_isLUB
-/
theorem csSup_div_semiconj [ConditionallyCompleteLattice α] [Group G] (f₁ f₂ : G ->* α ≃o α)
    (hbdd : forall x, BddAbove (range fun g => (f₁ g)⁻¹ (f₂ g x))) (g : G) :
    Function.Semiconj (fun x => ⨆ g' : G, (f₁ g')⁻¹ (f₂ g' x)) (f₂ g) (f₁ g) :=
  semiconj_of_isLUB f₁ f₂ (fun x => isLUB_csSup (range_nonempty _) (hbdd x)) _

end Function
