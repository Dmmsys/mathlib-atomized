/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.Order.ExtendFrom
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.LocalExtr
public import Mathlib.Topology.Order.T5

/-!
# Rolle's Theorem (topological part)

In this file we prove the purely topological part of Rolle's Theorem:
a function that is continuous on an interval $[a, b]$, $a < b$,
has a local extremum at a point $x ∈ (a, b)$ provided that $f(a)=f(b)$.
We also prove several variations of this statement.

In `Mathlib/Analysis/Calculus/LocalExtr/Rolle` we use these lemmas
to prove several versions of Rolle's Theorem from calculus.

## Keywords
local minimum, local maximum, extremum, Rolle's Theorem
-/

public section

open Filter Set Topology

variable {X Y : Type*}
  [ConditionallyCompleteLinearOrder X] [DenselyOrdered X] [TopologicalSpace X] [OrderTopology X]
  [LinearOrder Y] [TopologicalSpace Y] [OrderTopology Y]
  {f : X -> Y} {a b : X} {l : Y}

/--
theorem `exists_Ioo_extr_on_Icc` / 定理 `exists_Ioo_extr_on_Icc`

English:
theorem exists_Ioo_extr_on_Icc
  given: (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b)
  proof: by
  have ne : (Icc a b).Nonempty := nonempty_Icc.2 (le_of_lt hab)
  -- Consider absolute min and max points
  obtain ⟨c, cmem, cle⟩ : exists c in Icc a b, forall x in Icc a b, f c <= f x :=
    isCompact_Icc.exists_isMinOn ne hfc
  obtain ⟨C, Cmem, Cge⟩ : exists C in Icc a b, forall x in Icc a b, f x <= f C :=
    isCompact_Icc.exists_isMaxOn ne hfc
  by_cases hc : f c = f a
  · by_cases hC : f C = f a
    · have : forall x in Icc a b, f x = f a := fun x hx => le_antisymm (hC ▸ Cge x hx) (hc ▸ cle x hx)
      -- `f` is a constant, so we can take any point in `Ioo a b`
      rcases nonempty_Ioo.2 hab with ⟨c', hc'⟩
      refine ⟨c', hc', Or.inl fun x hx => ?_⟩
      simp only [mem_ofPred_eq, this x hx, this c' (Ioo_subset_Icc_self hc'), le_rfl]
· refine ⟨C, ⟨lt_of_le_of_ne Cmem.1 mt ?_ hC, lt_of_le_of_ne Cmem.2 mt ?_ hC⟩, Or.inr Cge⟩
      exacts [fun h => by rw [h], fun h => by rw [h, hfI]]
· refine ⟨c, ⟨lt_of_le_of_ne cmem.1 mt ?_ hc, lt_of_le_of_ne cmem.2 mt ?_ hc⟩, Or.inl cle⟩
    exacts [fun h => by rw [h], fun h => by rw [h, hfI]]

中文:
定理 存在_Ioo_extr_on_Icc
  条件: (hab : a < b) (hfc : ContinuousOn f (闭区间 a b)) (hfI : f a = f b)
  证明: by
  have ne : (Icc a b).Nonempty := nonempty_Icc.2 (le_of_lt hab)
  -- Consider absolute min and max points
  obtain ⟨c, cmem, cle⟩ : exists c in Icc a b, forall x in Icc a b, f c <= f x :=
    isCompact_Icc.exists_isMinOn ne hfc
  obtain ⟨C, Cmem, Cge⟩ : exists C in Icc a b, forall x in Icc a b, f x <= f C :=
    isCompact_Icc.exists_isMaxOn ne hfc
  by_cases hc : f c = f a
  · by_cases hC : f C = f a
    · have : forall x in Icc a b, f x = f a := fun x hx => le_antisymm (hC ▸ Cge x hx) (hc ▸ cle x hx)
      -- `f` is a constant, so we can take any point in `Ioo a b`
      rcases nonempty_Ioo.2 hab with ⟨c', hc'⟩
      refine ⟨c', hc', Or.inl fun x hx => ?_⟩
      simp only [mem_ofPred_eq, this x hx, this c' (Ioo_subset_Icc_self hc'), le_rfl]
· refine ⟨C, ⟨lt_of_le_of_ne Cmem.1 mt ?_ hC, lt_of_le_of_ne Cmem.2 mt ?_ hC⟩, Or.inr Cge⟩
      exacts [fun h => by rw [h], fun h => by rw [h, hfI]]
· refine ⟨c, ⟨lt_of_le_of_ne cmem.1 mt ?_ hc, lt_of_le_of_ne cmem.2 mt ?_ hc⟩, Or.inl cle⟩
    exacts [fun h => by rw [h], fun h => by rw [h, hfI]]

Depends on / 依赖: Nonempty, le_of_lt, nonempty_Icc
-/
theorem exists_Ioo_extr_on_Icc (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b) :
    exists c in Ioo a b, IsExtrOn f (Icc a b) c := by
  have ne : (Icc a b).Nonempty := nonempty_Icc.2 (le_of_lt hab)
  -- Consider absolute min and max points
  obtain ⟨c, cmem, cle⟩ : exists c in Icc a b, forall x in Icc a b, f c <= f x :=
    isCompact_Icc.exists_isMinOn ne hfc
  obtain ⟨C, Cmem, Cge⟩ : exists C in Icc a b, forall x in Icc a b, f x <= f C :=
    isCompact_Icc.exists_isMaxOn ne hfc
  by_cases hc : f c = f a
  · by_cases hC : f C = f a
    · have : forall x in Icc a b, f x = f a := fun x hx => le_antisymm (hC ▸ Cge x hx) (hc ▸ cle x hx)
      -- `f` is a constant, so we can take any point in `Ioo a b`
      rcases nonempty_Ioo.2 hab with ⟨c', hc'⟩
      refine ⟨c', hc', Or.inl fun x hx => ?_⟩
      simp only [mem_ofPred_eq, this x hx, this c' (Ioo_subset_Icc_self hc'), le_rfl]
· refine ⟨C, ⟨lt_of_le_of_ne Cmem.1 mt ?_ hC, lt_of_le_of_ne Cmem.2 mt ?_ hC⟩, Or.inr Cge⟩
      exacts [fun h => by rw [h], fun h => by rw [h, hfI]]
· refine ⟨c, ⟨lt_of_le_of_ne cmem.1 mt ?_ hc, lt_of_le_of_ne cmem.2 mt ?_ hc⟩, Or.inl cle⟩
    exacts [fun h => by rw [h], fun h => by rw [h, hfI]]

/--
theorem `exists_isLocalExtr_Ioo` / 定理 `exists_isLocalExtr_Ioo`

English:
theorem exists_isLocalExtr_Ioo
  given: (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b)
  proof: let ⟨c, cmem, hc⟩ := exists_Ioo_extr_on_Icc hab hfc hfI
⟨c, cmem, hc.isLocalExtr Icc_mem_nhds cmem.1 cmem.2⟩

中文:
定理 存在_isLocalExtr_Ioo
  条件: (hab : a < b) (hfc : ContinuousOn f (闭区间 a b)) (hfI : f a = f b)
  证明: let ⟨c, cmem, hc⟩ := exists_Ioo_extr_on_Icc hab hfc hfI
⟨c, cmem, hc.isLocalExtr Icc_mem_nhds cmem.1 cmem.2⟩

Depends on / 依赖: Icc_mem_nhds, exists_Ioo_extr_on_Icc, hc.isLocalExtr, isLocalExtr
-/
theorem exists_isLocalExtr_Ioo (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b) :
    exists c in Ioo a b, IsLocalExtr f c :=
  let ⟨c, cmem, hc⟩ := exists_Ioo_extr_on_Icc hab hfc hfI
⟨c, cmem, hc.isLocalExtr Icc_mem_nhds cmem.1 cmem.2⟩

/--
lemma `exists_isExtrOn_Ioo_of_tendsto` / 引理 `exists_isExtrOn_Ioo_of_tendsto`

English:
lemma exists_isExtrOn_Ioo_of_tendsto
  statement: (hab : a < b) (hfc : ContinuousOn f (Ioo a b))
  proof: by
  have h : EqOn (extendFrom (Ioo a b) f) f (Ioo a b) := extendFrom_extends hfc
  obtain ⟨c, hc, hfc⟩ : exists c in Ioo a b, IsExtrOn (extendFrom (Ioo a b) f) (Icc a b) c :=
    exists_Ioo_extr_on_Icc hab (continuousOn_Icc_extendFrom_Ioo hfc ha hb)
      ((eq_lim_at_left_extendFrom_Ioo hab ha).trans (eq_lim_at_right_extendFrom_Ioo hab hb).symm)
  exact ⟨c, hc, (hfc.on_subset Ioo_subset_Icc_self).congr h (h hc)⟩

中文:
引理 存在_isExtrOn_Ioo_of_tendsto
  结论: (hab : a < b) (hfc : ContinuousOn f (开区间 a b))
  证明: by
  have h : EqOn (extendFrom (Ioo a b) f) f (Ioo a b) := extendFrom_extends hfc
  obtain ⟨c, hc, hfc⟩ : exists c in Ioo a b, IsExtrOn (extendFrom (Ioo a b) f) (Icc a b) c :=
    exists_Ioo_extr_on_Icc hab (continuousOn_Icc_extendFrom_Ioo hfc ha hb)
      ((eq_lim_at_left_extendFrom_Ioo hab ha).trans (eq_lim_at_right_extendFrom_Ioo hab hb).symm)
  exact ⟨c, hc, (hfc.on_subset Ioo_subset_Icc_self).congr h (h hc)⟩

Depends on / 依赖: Ioo_subset_Icc_self, IsExtrOn, continuousOn_Icc_extendFrom_Ioo, eq_lim_at_left_extendFrom_Ioo, eq_lim_at_right_extendFrom_Ioo, exists_Ioo_extr_on_Icc, extendFrom, extendFrom_extends, hfc.on_subset, on_subset
-/
lemma exists_isExtrOn_Ioo_of_tendsto (hab : a < b) (hfc : ContinuousOn f (Ioo a b))
    (ha : Tendsto f (𝓝[>] a) (𝓝 l)) (hb : Tendsto f (𝓝[<] b) (𝓝 l)) :
    exists c in Ioo a b, IsExtrOn f (Ioo a b) c := by
  have h : EqOn (extendFrom (Ioo a b) f) f (Ioo a b) := extendFrom_extends hfc
  obtain ⟨c, hc, hfc⟩ : exists c in Ioo a b, IsExtrOn (extendFrom (Ioo a b) f) (Icc a b) c :=
    exists_Ioo_extr_on_Icc hab (continuousOn_Icc_extendFrom_Ioo hfc ha hb)
      ((eq_lim_at_left_extendFrom_Ioo hab ha).trans (eq_lim_at_right_extendFrom_Ioo hab hb).symm)
  exact ⟨c, hc, (hfc.on_subset Ioo_subset_Icc_self).congr h (h hc)⟩

/--
lemma `exists_isLocalExtr_Ioo_of_tendsto` / 引理 `exists_isLocalExtr_Ioo_of_tendsto`

English:
lemma exists_isLocalExtr_Ioo_of_tendsto
  statement: (hab : a < b) (hfc : ContinuousOn f (Ioo a b))
  proof: let ⟨c, cmem, hc⟩ := exists_isExtrOn_Ioo_of_tendsto hab hfc ha hb
⟨c, cmem, hc.isLocalExtr Ioo_mem_nhds cmem.1 cmem.2⟩

中文:
引理 存在_isLocalExtr_Ioo_of_tendsto
  结论: (hab : a < b) (hfc : ContinuousOn f (开区间 a b))
  证明: let ⟨c, cmem, hc⟩ := exists_isExtrOn_Ioo_of_tendsto hab hfc ha hb
⟨c, cmem, hc.isLocalExtr Ioo_mem_nhds cmem.1 cmem.2⟩

Depends on / 依赖: Ioo_mem_nhds, exists_isExtrOn_Ioo_of_tendsto, hc.isLocalExtr, isLocalExtr
-/
lemma exists_isLocalExtr_Ioo_of_tendsto (hab : a < b) (hfc : ContinuousOn f (Ioo a b))
    (ha : Tendsto f (𝓝[>] a) (𝓝 l)) (hb : Tendsto f (𝓝[<] b) (𝓝 l)) :
    exists c in Ioo a b, IsLocalExtr f c :=
  let ⟨c, cmem, hc⟩ := exists_isExtrOn_Ioo_of_tendsto hab hfc ha hb
⟨c, cmem, hc.isLocalExtr Ioo_mem_nhds cmem.1 cmem.2⟩

/--
theorem `exists_uIoo_isExtrOn_uIcc` / 定理 `exists_uIoo_isExtrOn_uIcc`

English:
theorem exists_uIoo_isExtrOn_uIcc
  statement: (hab : a != b) (hfc : ContinuousOn f (uIcc a b))
  proof: exists_Ioo_extr_on_Icc (by simp [hab.symm]) hfc (by grind)

中文:
定理 存在_uIoo_isExtrOn_uIcc
  结论: (hab : a != b) (hfc : ContinuousOn f (uIcc a b))
  证明: exists_Ioo_extr_on_Icc (by simp [hab.symm]) hfc (by grind)

Depends on / 依赖: exists_Ioo_extr_on_Icc, hab.symm
-/
theorem exists_uIoo_isExtrOn_uIcc (hab : a != b) (hfc : ContinuousOn f (uIcc a b))
    (hfI : f a = f b) :
    exists c in uIoo a b, IsExtrOn f (uIcc a b) c :=
  exists_Ioo_extr_on_Icc (by simp [hab.symm]) hfc (by grind)

/--
theorem `exists_isLocalExtr_uIoo` / 定理 `exists_isLocalExtr_uIoo`

English:
theorem exists_isLocalExtr_uIoo
  given: (hab : a != b) (hfc : ContinuousOn f (uIcc a b)) (hfI : f a = f b)
  proof: exists_isLocalExtr_Ioo (by simp [hab.symm]) hfc (by grind)

中文:
定理 存在_isLocalExtr_uIoo
  条件: (hab : a != b) (hfc : ContinuousOn f (uIcc a b)) (hfI : f a = f b)
  证明: exists_isLocalExtr_Ioo (by simp [hab.symm]) hfc (by grind)

Depends on / 依赖: exists_isLocalExtr_Ioo, hab.symm
-/
theorem exists_isLocalExtr_uIoo (hab : a != b) (hfc : ContinuousOn f (uIcc a b)) (hfI : f a = f b) :
    exists c in uIoo a b, IsLocalExtr f c :=
  exists_isLocalExtr_Ioo (by simp [hab.symm]) hfc (by grind)

/--
lemma `exists_isExtrOn_uIoo_of_tendsto` / 引理 `exists_isExtrOn_uIoo_of_tendsto`

English:
lemma exists_isExtrOn_uIoo_of_tendsto
  statement: (hab : a != b) (hfc : ContinuousOn f (uIoo a b))
  proof: by
  have h : EqOn (extendFrom (uIoo a b) f) f (uIoo a b) := extendFrom_extends hfc
  obtain ⟨c, hc, hfc⟩ : exists c in uIoo a b, IsExtrOn (extendFrom (uIoo a b) f) (uIcc a b) c :=
    exists_uIoo_isExtrOn_uIcc hab (continuousOn_uIcc_extendFrom_uIoo hfc ha hb)
      ((eq_lim_at_left_extendFrom_uIoo hab ha).trans (eq_lim_at_right_extendFrom_uIoo hab hb).symm)
  exact ⟨c, hc, (hfc.on_subset uIoo_subset_uIcc_self).congr h (h hc)⟩

中文:
引理 存在_isExtrOn_uIoo_of_tendsto
  结论: (hab : a != b) (hfc : ContinuousOn f (uIoo a b))
  证明: by
  have h : EqOn (extendFrom (uIoo a b) f) f (uIoo a b) := extendFrom_extends hfc
  obtain ⟨c, hc, hfc⟩ : exists c in uIoo a b, IsExtrOn (extendFrom (uIoo a b) f) (uIcc a b) c :=
    exists_uIoo_isExtrOn_uIcc hab (continuousOn_uIcc_extendFrom_uIoo hfc ha hb)
      ((eq_lim_at_left_extendFrom_uIoo hab ha).trans (eq_lim_at_right_extendFrom_uIoo hab hb).symm)
  exact ⟨c, hc, (hfc.on_subset uIoo_subset_uIcc_self).congr h (h hc)⟩

Depends on / 依赖: IsExtrOn, continuousOn_uIcc_extendFrom_uIoo, eq_lim_at_left_extendFrom_uIoo, eq_lim_at_right_extendFrom_uIoo, exists_uIoo_isExtrOn_uIcc, extendFrom, extendFrom_extends, hfc.on_subset, on_subset, uIoo_subset_uIcc_self
-/
lemma exists_isExtrOn_uIoo_of_tendsto (hab : a != b) (hfc : ContinuousOn f (uIoo a b))
    (ha : Tendsto f (𝓝[uIoo a b] a) (𝓝 l)) (hb : Tendsto f (𝓝[uIoo a b] b) (𝓝 l)) :
    exists c in uIoo a b, IsExtrOn f (uIoo a b) c := by
  have h : EqOn (extendFrom (uIoo a b) f) f (uIoo a b) := extendFrom_extends hfc
  obtain ⟨c, hc, hfc⟩ : exists c in uIoo a b, IsExtrOn (extendFrom (uIoo a b) f) (uIcc a b) c :=
    exists_uIoo_isExtrOn_uIcc hab (continuousOn_uIcc_extendFrom_uIoo hfc ha hb)
      ((eq_lim_at_left_extendFrom_uIoo hab ha).trans (eq_lim_at_right_extendFrom_uIoo hab hb).symm)
  exact ⟨c, hc, (hfc.on_subset uIoo_subset_uIcc_self).congr h (h hc)⟩

/--
lemma `exists_isLocalExtr_uIoo_of_tendsto` / 引理 `exists_isLocalExtr_uIoo_of_tendsto`

English:
lemma exists_isLocalExtr_uIoo_of_tendsto
  statement: (hab : a != b) (hfc : ContinuousOn f (uIoo a b))
  proof: let ⟨c, cmem, hc⟩ := exists_isExtrOn_uIoo_of_tendsto hab hfc ha hb
⟨c, cmem, hc.isLocalExtr Ioo_mem_nhds cmem.1 cmem.2⟩

中文:
引理 存在_isLocalExtr_uIoo_of_tendsto
  结论: (hab : a != b) (hfc : ContinuousOn f (uIoo a b))
  证明: let ⟨c, cmem, hc⟩ := exists_isExtrOn_uIoo_of_tendsto hab hfc ha hb
⟨c, cmem, hc.isLocalExtr Ioo_mem_nhds cmem.1 cmem.2⟩

Depends on / 依赖: Ioo_mem_nhds, exists_isExtrOn_uIoo_of_tendsto, hc.isLocalExtr, isLocalExtr
-/
lemma exists_isLocalExtr_uIoo_of_tendsto (hab : a != b) (hfc : ContinuousOn f (uIoo a b))
    (ha : Tendsto f (𝓝[uIoo a b] a) (𝓝 l)) (hb : Tendsto f (𝓝[uIoo a b] b) (𝓝 l)) :
    exists c in uIoo a b, IsLocalExtr f c :=
  let ⟨c, cmem, hc⟩ := exists_isExtrOn_uIoo_of_tendsto hab hfc ha hb
⟨c, cmem, hc.isLocalExtr Ioo_mem_nhds cmem.1 cmem.2⟩
