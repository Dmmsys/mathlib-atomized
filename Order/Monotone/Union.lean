/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Sébastien Gouëzel
-/
module

public import Mathlib.Order.Bounds.Basic
public import Mathlib.Order.Interval.Set.LinearOrder

/-!
# Monotonicity on intervals

In this file we prove that a function is (strictly) monotone (or antitone) on a linear order `α`
provided that it is (strictly) monotone on `(-∞, a]` and on `[a, +∞)`. This is a special case
of a more general statement where one deduces monotonicity on a union from monotonicity on each
set.
-/

public section


open Set

variable {α β : Type*} [LinearOrder α] [Preorder β] {a : α} {f : α -> β}

/--
theorem `StrictMonoOn.union` / 定理 `StrictMonoOn.union`

English:
theorem StrictMonoOn.union
  statement: {s t : Set α} {c : α} (h₁ : StrictMonoOn f s)
  proof: by
  have A : forall x, x in s union t -> x <= c -> x in s := by
    intro x hx hxc
    cases hx
    · assumption
    rcases eq_or_lt_of_le hxc with (rfl | h'x)
    · exact hs.1
    exact (lt_irrefl _ (h'x.trans_le (ht.2 (by assumption)))).elim
  have B : forall x, x in s union t -> c <= x -> x in t

中文:
定理 StrictMonoOn.union
  结论: {s t : 集合 α} {c : α} (h₁ : StrictMonoOn f s)
  证明: by
  have A : forall x, x in s union t -> x <= c -> x in s := by
    intro x hx hxc
    cases hx
    · assumption
    rcases eq_or_lt_of_le hxc with (rfl | h'x)
    · exact hs.1
    exact (lt_irrefl _ (h'x.trans_le (ht.2 (by assumption)))).elim
  have B : forall x, x in s union t -> c <= x -> x in t
-/
protected theorem StrictMonoOn.union {s t : Set α} {c : α} (h₁ : StrictMonoOn f s)
    (h₂ : StrictMonoOn f t) (hs : IsGreatest s c) (ht : IsLeast t c) : StrictMonoOn f (s union t) := by
  have A : forall x, x in s union t -> x <= c -> x in s := by
    intro x hx hxc
    cases hx
    · assumption
    rcases eq_or_lt_of_le hxc with (rfl | h'x)
    · exact hs.1
    exact (lt_irrefl _ (h'x.trans_le (ht.2 (by assumption)))).elim
  have B : forall x, x in s union t -> c <= x -> x in t := by
    intro x hx hxc
    match hx with
    | Or.inr hx => exact hx
    | Or.inl hx =>
      rcases eq_or_lt_of_le hxc with (rfl | h'x)
      · exact ht.1
      exact (lt_irrefl _ (h'x.trans_le (hs.2 hx))).elim
  intro x hx y hy hxy
  rcases lt_or_ge x c with (hxc | hcx)
  · have xs : x in s := A _ hx hxc.le
    rcases lt_or_ge y c with (hyc | hcy)
    · exact h₁ xs (A _ hy hyc.le) hxy
    · exact (h₁ xs hs.1 hxc).trans_le (h₂.monotoneOn ht.1 (B _ hy hcy) hcy)
  · have xt : x in t := B _ hx hcx
    have yt : y in t := B _ hy (hcx.trans hxy.le)
    exact h₂ xt yt hxy

/--
theorem `StrictMonoOn.Iic_union_Ici` / 定理 `StrictMonoOn.Iic_union_Ici`

English:
theorem StrictMonoOn.Iic_union_Ici
  statement: (h₁ : StrictMonoOn f (Iic a))
  proof: by
  rw [← strictMonoOn_univ]; rw [← @Iic_union_Ici _ _ a]
  exact StrictMonoOn.union h₁ h₂ isGreatest_Iic isLeast_Ici

中文:
定理 StrictMonoOn.Iic_union_Ici
  结论: (h₁ : StrictMonoOn f (左无界右闭区间 a))
  证明: by
  rw [← strictMonoOn_univ]; rw [← @Iic_union_Ici _ _ a]
  exact StrictMonoOn.union h₁ h₂ isGreatest_Iic isLeast_Ici
-/
protected theorem StrictMonoOn.Iic_union_Ici (h₁ : StrictMonoOn f (Iic a))
    (h₂ : StrictMonoOn f (Ici a)) : StrictMono f := by
  rw [← strictMonoOn_univ]; rw [← @Iic_union_Ici _ _ a]
  exact StrictMonoOn.union h₁ h₂ isGreatest_Iic isLeast_Ici

/--
theorem `StrictAntiOn.union` / 定理 `StrictAntiOn.union`

English:
theorem StrictAntiOn.union
  statement: {s t : Set α} {c : α} (h₁ : StrictAntiOn f s)
  proof: (h₁.dual_right.union h₂.dual_right hs ht).dual_right

中文:
定理 StrictAntiOn.union
  结论: {s t : 集合 α} {c : α} (h₁ : StrictAntiOn f s)
  证明: (h₁.dual_right.union h₂.dual_right hs ht).dual_right
-/
protected theorem StrictAntiOn.union {s t : Set α} {c : α} (h₁ : StrictAntiOn f s)
    (h₂ : StrictAntiOn f t) (hs : IsGreatest s c) (ht : IsLeast t c) : StrictAntiOn f (s union t) :=
  (h₁.dual_right.union h₂.dual_right hs ht).dual_right

/--
theorem `StrictAntiOn.Iic_union_Ici` / 定理 `StrictAntiOn.Iic_union_Ici`

English:
theorem StrictAntiOn.Iic_union_Ici
  statement: (h₁ : StrictAntiOn f (Iic a))
  proof: (h₁.dual_right.Iic_union_Ici h₂.dual_right).dual_right

中文:
定理 StrictAntiOn.Iic_union_Ici
  结论: (h₁ : StrictAntiOn f (左无界右闭区间 a))
  证明: (h₁.dual_right.Iic_union_Ici h₂.dual_right).dual_right
-/
protected theorem StrictAntiOn.Iic_union_Ici (h₁ : StrictAntiOn f (Iic a))
    (h₂ : StrictAntiOn f (Ici a)) : StrictAnti f :=
  (h₁.dual_right.Iic_union_Ici h₂.dual_right).dual_right

/--
theorem `MonotoneOn.union_right` / 定理 `MonotoneOn.union_right`

English:
theorem MonotoneOn.union_right
  statement: {s t : Set α} {c : α} (h₁ : MonotoneOn f s)
  proof: by
  have A : forall x, x in s union t -> x <= c -> x in s := by
    intro x hx hxc
    cases hx
    · assumption
    rcases eq_or_lt_of_le hxc with (rfl | h'x)
    · exact hs.1
    exact (lt_irrefl _ (h'x.trans_le (ht.2 (by assumption)))).elim
  have B : forall x, x in s union t -> c <= x -> x in t

中文:
定理 MonotoneOn.union_right
  结论: {s t : 集合 α} {c : α} (h₁ : MonotoneOn f s)
  证明: by
  have A : forall x, x in s union t -> x <= c -> x in s := by
    intro x hx hxc
    cases hx
    · assumption
    rcases eq_or_lt_of_le hxc with (rfl | h'x)
    · exact hs.1
    exact (lt_irrefl _ (h'x.trans_le (ht.2 (by assumption)))).elim
  have B : forall x, x in s union t -> c <= x -> x in t
-/
protected theorem MonotoneOn.union_right {s t : Set α} {c : α} (h₁ : MonotoneOn f s)
    (h₂ : MonotoneOn f t) (hs : IsGreatest s c) (ht : IsLeast t c) : MonotoneOn f (s union t) := by
  have A : forall x, x in s union t -> x <= c -> x in s := by
    intro x hx hxc
    cases hx
    · assumption
    rcases eq_or_lt_of_le hxc with (rfl | h'x)
    · exact hs.1
    exact (lt_irrefl _ (h'x.trans_le (ht.2 (by assumption)))).elim
  have B : forall x, x in s union t -> c <= x -> x in t := by
    intro x hx hxc
    match hx with
    | Or.inr hx => exact hx
    | Or.inl hx =>
      rcases eq_or_lt_of_le hxc with (rfl | h'x)
      · exact ht.1
      exact (lt_irrefl _ (h'x.trans_le (hs.2 hx))).elim
  intro x hx y hy hxy
  rcases lt_or_ge x c with (hxc | hcx)
  · have xs : x in s := A _ hx hxc.le
    rcases lt_or_ge y c with (hyc | hcy)
    · exact h₁ xs (A _ hy hyc.le) hxy
    · exact (h₁ xs hs.1 hxc.le).trans (h₂ ht.1 (B _ hy hcy) hcy)
  · have xt : x in t := B _ hx hcx
    have yt : y in t := B _ hy (hcx.trans hxy)
    exact h₂ xt yt hxy

/--
theorem `MonotoneOn.Iic_union_Ici` / 定理 `MonotoneOn.Iic_union_Ici`

English:
theorem MonotoneOn.Iic_union_Ici
  given: (h₁ : MonotoneOn f (Iic a)) (h₂ : MonotoneOn f (Ici a))
  proof: by
  rw [← monotoneOn_univ]; rw [← @Iic_union_Ici _ _ a]
  exact MonotoneOn.union_right h₁ h₂ isGreatest_Iic isLeast_Ici

中文:
定理 MonotoneOn.Iic_union_Ici
  条件: (h₁ : MonotoneOn f (左无界右闭区间 a)) (h₂ : MonotoneOn f (左闭右无界区间 a))
  证明: by
  rw [← monotoneOn_univ]; rw [← @Iic_union_Ici _ _ a]
  exact MonotoneOn.union_right h₁ h₂ isGreatest_Iic isLeast_Ici
-/
protected theorem MonotoneOn.Iic_union_Ici (h₁ : MonotoneOn f (Iic a)) (h₂ : MonotoneOn f (Ici a)) :
    Monotone f := by
  rw [← monotoneOn_univ]; rw [← @Iic_union_Ici _ _ a]
  exact MonotoneOn.union_right h₁ h₂ isGreatest_Iic isLeast_Ici

/--
theorem `AntitoneOn.union_right` / 定理 `AntitoneOn.union_right`

English:
theorem AntitoneOn.union_right
  statement: {s t : Set α} {c : α} (h₁ : AntitoneOn f s)
  proof: (h₁.dual_right.union_right h₂.dual_right hs ht).dual_right

中文:
定理 AntitoneOn.union_right
  结论: {s t : 集合 α} {c : α} (h₁ : AntitoneOn f s)
  证明: (h₁.dual_right.union_right h₂.dual_right hs ht).dual_right
-/
protected theorem AntitoneOn.union_right {s t : Set α} {c : α} (h₁ : AntitoneOn f s)
    (h₂ : AntitoneOn f t) (hs : IsGreatest s c) (ht : IsLeast t c) : AntitoneOn f (s union t) :=
  (h₁.dual_right.union_right h₂.dual_right hs ht).dual_right

/--
theorem `AntitoneOn.Iic_union_Ici` / 定理 `AntitoneOn.Iic_union_Ici`

English:
theorem AntitoneOn.Iic_union_Ici
  given: (h₁ : AntitoneOn f (Iic a)) (h₂ : AntitoneOn f (Ici a))
  proof: (h₁.dual_right.Iic_union_Ici h₂.dual_right).dual_right

中文:
定理 AntitoneOn.Iic_union_Ici
  条件: (h₁ : AntitoneOn f (左无界右闭区间 a)) (h₂ : AntitoneOn f (左闭右无界区间 a))
  证明: (h₁.dual_right.Iic_union_Ici h₂.dual_right).dual_right
-/
protected theorem AntitoneOn.Iic_union_Ici (h₁ : AntitoneOn f (Iic a)) (h₂ : AntitoneOn f (Ici a)) :
    Antitone f :=
  (h₁.dual_right.Iic_union_Ici h₂.dual_right).dual_right
