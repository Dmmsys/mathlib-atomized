/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Monoid.OrderDual
public import Mathlib.Order.Monotone.Union

/-!
# Monotonicity of odd functions

An odd function on a linear ordered additive commutative group `G` is monotone on the whole group
provided that it is monotone on `Set.Ici 0`, see `monotone_of_odd_of_monotoneOn_nonneg`. We also
prove versions of this lemma for `Antitone`, `StrictMono`, and `StrictAnti`.
-/

public section


open Set

variable {G H : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [AddCommGroup H] [PartialOrder H] [IsOrderedAddMonoid H]

/--
theorem `strictMono_of_odd_strictMonoOn_nonneg` / 定理 `strictMono_of_odd_strictMonoOn_nonneg`

English:
theorem strictMono_of_odd_strictMonoOn_nonneg
  statement: {f : G -> H} (h₁ : forall x, f (-x) = -f x)
  proof: by
  refine StrictMonoOn.Iic_union_Ici (fun x hx y hy hxy => neg_lt_neg_iff.1 ?_) h₂
  rw [← h₁]; rw [← h₁]
  exact h₂ (neg_nonneg.2 hy) (neg_nonneg.2 hx) (neg_lt_neg hxy)

中文:
定理 strictMono_of_odd_strictMonoOn_nonneg
  结论: {f : G -> H} (h₁ : 对任意 x, f (-x) = -f x)
  证明: by
  refine StrictMonoOn.Iic_union_Ici (fun x hx y hy hxy => neg_lt_neg_iff.1 ?_) h₂
  rw [← h₁]; rw [← h₁]
  exact h₂ (neg_nonneg.2 hy) (neg_nonneg.2 hx) (neg_lt_neg hxy)

Depends on / 依赖: Iic_union_Ici, StrictMonoOn, StrictMonoOn.Iic_union_Ici, neg_lt_neg, neg_lt_neg_iff, neg_nonneg
-/
theorem strictMono_of_odd_strictMonoOn_nonneg {f : G -> H} (h₁ : forall x, f (-x) = -f x)
    (h₂ : StrictMonoOn f (Ici 0)) : StrictMono f := by
  refine StrictMonoOn.Iic_union_Ici (fun x hx y hy hxy => neg_lt_neg_iff.1 ?_) h₂
  rw [← h₁]; rw [← h₁]
  exact h₂ (neg_nonneg.2 hy) (neg_nonneg.2 hx) (neg_lt_neg hxy)

/--
theorem `strictAnti_of_odd_strictAntiOn_nonneg` / 定理 `strictAnti_of_odd_strictAntiOn_nonneg`

English:
theorem strictAnti_of_odd_strictAntiOn_nonneg
  statement: {f : G -> H} (h₁ : forall x, f (-x) = -f x)
  proof: strictMono_of_odd_strictMonoOn_nonneg (H := Hᵒᵈ) h₁ h₂

中文:
定理 strictAnti_of_odd_strictAntiOn_nonneg
  结论: {f : G -> H} (h₁ : 对任意 x, f (-x) = -f x)
  证明: strictMono_of_odd_strictMonoOn_nonneg (H := Hᵒᵈ) h₁ h₂

Depends on / 依赖: strictMono_of_odd_strictMonoOn_nonneg
-/
theorem strictAnti_of_odd_strictAntiOn_nonneg {f : G -> H} (h₁ : forall x, f (-x) = -f x)
    (h₂ : StrictAntiOn f (Ici 0)) : StrictAnti f :=
  strictMono_of_odd_strictMonoOn_nonneg (H := Hᵒᵈ) h₁ h₂

/--
theorem `monotone_of_odd_of_monotoneOn_nonneg` / 定理 `monotone_of_odd_of_monotoneOn_nonneg`

English:
theorem monotone_of_odd_of_monotoneOn_nonneg
  statement: {f : G -> H} (h₁ : forall x, f (-x) = -f x)
  proof: by
  refine MonotoneOn.Iic_union_Ici (fun x hx y hy hxy => neg_le_neg_iff.1 ?_) h₂
  rw [← h₁]; rw [← h₁]
  exact h₂ (neg_nonneg.2 hy) (neg_nonneg.2 hx) (neg_le_neg hxy)

中文:
定理 monotone_of_odd_of_monotoneOn_nonneg
  结论: {f : G -> H} (h₁ : 对任意 x, f (-x) = -f x)
  证明: by
  refine MonotoneOn.Iic_union_Ici (fun x hx y hy hxy => neg_le_neg_iff.1 ?_) h₂
  rw [← h₁]; rw [← h₁]
  exact h₂ (neg_nonneg.2 hy) (neg_nonneg.2 hx) (neg_le_neg hxy)

Depends on / 依赖: Iic_union_Ici, MonotoneOn, MonotoneOn.Iic_union_Ici, neg_le_neg, neg_le_neg_iff, neg_nonneg
-/
theorem monotone_of_odd_of_monotoneOn_nonneg {f : G -> H} (h₁ : forall x, f (-x) = -f x)
    (h₂ : MonotoneOn f (Ici 0)) : Monotone f := by
  refine MonotoneOn.Iic_union_Ici (fun x hx y hy hxy => neg_le_neg_iff.1 ?_) h₂
  rw [← h₁]; rw [← h₁]
  exact h₂ (neg_nonneg.2 hy) (neg_nonneg.2 hx) (neg_le_neg hxy)

/--
theorem `antitone_of_odd_of_monotoneOn_nonneg` / 定理 `antitone_of_odd_of_monotoneOn_nonneg`

English:
theorem antitone_of_odd_of_monotoneOn_nonneg
  statement: {f : G -> H} (h₁ : forall x, f (-x) = -f x)
  proof: monotone_of_odd_of_monotoneOn_nonneg (H := Hᵒᵈ) h₁ h₂

中文:
定理 antitone_of_odd_of_monotoneOn_nonneg
  结论: {f : G -> H} (h₁ : 对任意 x, f (-x) = -f x)
  证明: monotone_of_odd_of_monotoneOn_nonneg (H := Hᵒᵈ) h₁ h₂

Depends on / 依赖: monotone_of_odd_of_monotoneOn_nonneg
-/
theorem antitone_of_odd_of_monotoneOn_nonneg {f : G -> H} (h₁ : forall x, f (-x) = -f x)
    (h₂ : AntitoneOn f (Ici 0)) : Antitone f :=
  monotone_of_odd_of_monotoneOn_nonneg (H := Hᵒᵈ) h₁ h₂
