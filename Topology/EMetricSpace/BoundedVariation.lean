/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Order.Interval.Set.ProjIcc
public import Mathlib.Data.Finset.Sort
public import Mathlib.Tactic.Finiteness
public import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Topology.Order.LeftRightLim
public import Mathlib.Topology.Semicontinuity.Defs
public import Mathlib.Tactic.Bound

/-!
# Functions of bounded variation

We study functions of bounded variation. In particular, we show that a bounded variation function
is a difference of monotone functions, and differentiable almost everywhere. This implies that
Lipschitz functions from the real line into finite-dimensional vector space are also differentiable
almost everywhere.

## Main definitions and results

* `eVariationOn f s` is the total variation of the function `f` on the set `s`, in `ℝ≥0∞`.
* `BoundedVariationOn f s` registers that the variation of `f` on `s` is finite.
* `LocallyBoundedVariationOn f s` registers that `f` has finite variation on any compact
  subinterval of `s`.
* `variationOnFromTo f s a b` is the signed variation of `f` on `s ∩ Icc a b`, converted to `ℝ`.

* `eVariationOn.Icc_add_Icc` states that the variation of `f` on `[a, c]` is the sum of its
  variations on `[a, b]` and `[b, c]`.
* `LocallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn` proves that a function
  with locally bounded variation is the difference of two monotone functions.
* `LipschitzWith.locallyBoundedVariationOn` shows that a Lipschitz function has locally
  bounded variation.

We also give several variations around these results.

## Implementation

We define the variation as an extended nonnegative real, to allow for infinite variation. This makes
it possible to use the complete linear order structure of `ℝ≥0∞`. The proofs would be much
more tedious with an `ℝ`-valued or `ℝ≥0`-valued variation, since one would always need to check
that the sets one uses are nonempty and bounded above as these are only conditionally complete.
-/

@[expose] public section

open scoped NNReal ENNReal Topology UniformConvergence
open Set Filter OrderDual

variable {α : Type*} [LinearOrder α] {E : Type*} [PseudoEMetricSpace E]

/--
Definition of `eVariationOn` / `eVariationOn` 的定义

English:
definition eVariationOn
  signature: (f : α -> E) (s : Set α)
  body: ⨆ p : Nat × { u : Nat -> α // Monotone u ∧ forall i, u i in s },
    ∑ i in Finset.range p.1, edist (f (p.2.1 (i + 1))) (f (p.2.1 i))

中文:
定义 eVariationOn
  签名: (f : α -> E) (s : 集合 α)
  定义体: ⨆ p : Nat × { u : Nat -> α // Monotone u ∧ forall i, u i in s },
    ∑ i in Finset.range p.1, edist (f (p.2.1 (i + 1))) (f (p.2.1 i))

Depends on / 依赖: Finset, Finset.range, Monotone
-/
noncomputable def eVariationOn (f : α -> E) (s : Set α) : Real>=0∞ :=
  ⨆ p : Nat × { u : Nat -> α // Monotone u ∧ forall i, u i in s },
    ∑ i in Finset.range p.1, edist (f (p.2.1 (i + 1))) (f (p.2.1 i))

/--
Definition of `BoundedVariationOn` / `BoundedVariationOn` 的定义

English:
definition BoundedVariationOn
  signature: (f : α -> E) (s : Set α)
  body: eVariationOn f s != ∞

中文:
定义 BoundedVariationOn
  签名: (f : α -> E) (s : 集合 α)
  定义体: eVariationOn f s != ∞

Depends on / 依赖: eVariationOn
-/
def BoundedVariationOn (f : α -> E) (s : Set α) :=
  eVariationOn f s != ∞

/--
Definition of `LocallyBoundedVariationOn` / `LocallyBoundedVariationOn` 的定义

English:
definition LocallyBoundedVariationOn
  signature: (f : α -> E) (s : Set α)
  body: forall a b, a in s -> b in s -> BoundedVariationOn f (s inter Icc a b)

中文:
定义 LocallyBoundedVariationOn
  签名: (f : α -> E) (s : 集合 α)
  定义体: forall a b, a in s -> b in s -> BoundedVariationOn f (s inter Icc a b)

Depends on / 依赖: BoundedVariationOn
-/
def LocallyBoundedVariationOn (f : α -> E) (s : Set α) :=
  forall a b, a in s -> b in s -> BoundedVariationOn f (s inter Icc a b)

/-! ### Basic computations of variation -/

namespace eVariationOn

/--
theorem `nonempty_monotone_mem` / 定理 `nonempty_monotone_mem`

English:
theorem nonempty_monotone_mem
  given: {s : Set α} (hs : s.Nonempty)
  proof: by
  obtain ⟨x, hx⟩ := hs
  exact ⟨⟨fun _ => x, fun i j _ => le_rfl, fun _ => hx⟩⟩

中文:
定理 nonempty_monotone_mem
  条件: {s : 集合 α} (hs : s.非空)
  证明: by
  obtain ⟨x, hx⟩ := hs
  exact ⟨⟨fun _ => x, fun i j _ => le_rfl, fun _ => hx⟩⟩

Depends on / 依赖: le_rfl
-/
theorem nonempty_monotone_mem {s : Set α} (hs : s.Nonempty) :
    Nonempty { u // Monotone u ∧ forall i : Nat, u i in s } := by
  obtain ⟨x, hx⟩ := hs
  exact ⟨⟨fun _ => x, fun i j _ => le_rfl, fun _ => hx⟩⟩

/--
theorem `eq_of_edist_zero_on` / 定理 `eq_of_edist_zero_on`

English:
theorem eq_of_edist_zero_on
  given: {f f' : α -> E} {s : Set α} (h : forall ⦃x⦄, x in s -> edist (f x) (f' x) = 0)
  proof: by
  dsimp only [eVariationOn]
  congr 1 with p : 1
  congr 1 with i : 1
  rw [edist_congr_right (h <| p.snd.prop.2 (i + 1))]; rw [edist_congr_left (h <| p.snd.prop.2 i)]

中文:
定理 eq_of_edist_zero_on
  条件: {f f' : α -> E} {s : 集合 α} (h : 对任意 ⦃x⦄, x in s -> edist (f x) (f' x) = 0)
  证明: by
  dsimp only [eVariationOn]
  congr 1 with p : 1
  congr 1 with i : 1
  rw [edist_congr_right (h <| p.snd.prop.2 (i + 1))]; rw [edist_congr_left (h <| p.snd.prop.2 i)]

Depends on / 依赖: eVariationOn, edist_congr_left, edist_congr_right, p.snd.prop
-/
theorem eq_of_edist_zero_on {f f' : α -> E} {s : Set α} (h : forall ⦃x⦄, x in s -> edist (f x) (f' x) = 0) :
    eVariationOn f s = eVariationOn f' s := by
  dsimp only [eVariationOn]
  congr 1 with p : 1
  congr 1 with i : 1
  rw [edist_congr_right (h <| p.snd.prop.2 (i + 1))]; rw [edist_congr_left (h <| p.snd.prop.2 i)]

/--
theorem `eq_of_eqOn` / 定理 `eq_of_eqOn`

English:
theorem eq_of_eqOn
  given: {f f' : α -> E} {s : Set α} (h : EqOn f f' s)
  proof: eq_of_edist_zero_on fun x xs => by rw [h xs, edist_self]

中文:
定理 eq_of_eqOn
  条件: {f f' : α -> E} {s : 集合 α} (h : EqOn f f' s)
  证明: eq_of_edist_zero_on fun x xs => by rw [h xs, edist_self]

Depends on / 依赖: edist_self, eq_of_edist_zero_on
-/
theorem eq_of_eqOn {f f' : α -> E} {s : Set α} (h : EqOn f f' s) :
    eVariationOn f s = eVariationOn f' s :=
  eq_of_edist_zero_on fun x xs => by rw [h xs, edist_self]

/--
theorem `sum_le` / 定理 `sum_le`

English:
theorem sum_le
  given: {f : α -> E} {s : Set α} {n : Nat} {u : Nat -> α} (hu : Monotone u) (us : forall i, u i in s)
  proof: le_iSup_of_le ⟨n, u, hu, us⟩ le_rfl

中文:
定理 sum_le
  条件: {f : α -> E} {s : 集合 α} {n : 自然数} {u : 自然数 -> α} (hu : 递增 u) (us : 对任意 i, u i in s)
  证明: le_iSup_of_le ⟨n, u, hu, us⟩ le_rfl

Depends on / 依赖: le_iSup_of_le, le_rfl
-/
theorem sum_le {f : α -> E} {s : Set α} {n : Nat} {u : Nat -> α} (hu : Monotone u) (us : forall i, u i in s) :
    (∑ i in Finset.range n, edist (f (u (i + 1))) (f (u i))) <= eVariationOn f s :=
  le_iSup_of_le ⟨n, u, hu, us⟩ le_rfl

/--
theorem `sum_le_of_monotoneOn_Icc` / 定理 `sum_le_of_monotoneOn_Icc`

English:
theorem sum_le_of_monotoneOn_Icc
  statement: {f : α -> E} {s : Set α} {m n : Nat} {u : Nat -> α}
  proof: by
  rcases le_total n m with hnm | hmn
  · simp [Finset.Ico_eq_empty_of_le hnm]
  let π := projIcc m n hmn
  let v i := u (π i)
  calc
    ∑ i in Finset.Ico m n, edist (f (u (i + 1))) (f (u i))
        = ∑ i in Finset.Ico m n, edist (f (v (i + 1))) (f (v i)) :=
      Finset.sum_congr rfl fun i hi =

中文:
定理 sum_le_of_monotoneOn_Icc
  结论: {f : α -> E} {s : 集合 α} {m n : 自然数} {u : 自然数 -> α}
  证明: by
  rcases le_total n m with hnm | hmn
  · simp [Finset.Ico_eq_empty_of_le hnm]
  let π := projIcc m n hmn
  let v i := u (π i)
  calc
    ∑ i in Finset.Ico m n, edist (f (u (i + 1))) (f (u i))
        = ∑ i in Finset.Ico m n, edist (f (v (i + 1))) (f (v i)) :=
      Finset.sum_congr rfl fun i hi =

Depends on / 依赖: Finset, Finset.Ico, Finset.Ico_eq_empty_of_le, Finset.mem_Ico, Finset.range, Finset.sum_congr, Finset.sum_mono_set, Ico_eq_empty_of_le, Iio_e, Nat.Iio_e, i.le_succ, le_succ, le_total, mem_Ico, projIcc, projIcc_of_mem, sum_congr, sum_mono_set
-/
theorem sum_le_of_monotoneOn_Icc {f : α -> E} {s : Set α} {m n : Nat} {u : Nat -> α}
    (hu : MonotoneOn u (Icc m n)) (us : forall i in Icc m n, u i in s) :
    (∑ i in Finset.Ico m n, edist (f (u (i + 1))) (f (u i))) <= eVariationOn f s := by
  rcases le_total n m with hnm | hmn
  · simp [Finset.Ico_eq_empty_of_le hnm]
  let π := projIcc m n hmn
  let v i := u (π i)
  calc
    ∑ i in Finset.Ico m n, edist (f (u (i + 1))) (f (u i))
        = ∑ i in Finset.Ico m n, edist (f (v (i + 1))) (f (v i)) :=
      Finset.sum_congr rfl fun i hi => by
        rw [Finset.mem_Ico] at hi
        simp only [v, π, projIcc_of_mem hmn ⟨hi.1, hi.2.le⟩,
          projIcc_of_mem hmn ⟨hi.1.trans i.le_succ, hi.2⟩]
    _ <= ∑ i in Finset.range n, edist (f (v (i + 1))) (f (v i)) :=
      Finset.sum_mono_set _ (Nat.Iio_eq_range n ▸ Finset.Ico_subset_Iio_self)
    _ <= eVariationOn f s :=
      sum_le (fun i j h => hu (π i).2 (π j).2 (monotone_projIcc hmn h)) fun i => us _ (π i).2

/--
theorem `sum_le_of_monotoneOn_Iic` / 定理 `sum_le_of_monotoneOn_Iic`

English:
theorem sum_le_of_monotoneOn_Iic
  statement: {f : α -> E} {s : Set α} {n : Nat} {u : Nat -> α}
  proof: by
  simpa using sum_le_of_monotoneOn_Icc (m := 0) (hu.mono Icc_subset_Iic_self) fun i hi => us i hi.2

中文:
定理 sum_le_of_monotoneOn_Iic
  结论: {f : α -> E} {s : 集合 α} {n : 自然数} {u : 自然数 -> α}
  证明: by
  simpa using sum_le_of_monotoneOn_Icc (m := 0) (hu.mono Icc_subset_Iic_self) fun i hi => us i hi.2

Depends on / 依赖: Icc_subset_Iic_self, hu.mono, sum_le_of_monotoneOn_Icc
-/
theorem sum_le_of_monotoneOn_Iic {f : α -> E} {s : Set α} {n : Nat} {u : Nat -> α}
    (hu : MonotoneOn u (Iic n)) (us : forall i <= n, u i in s) :
    (∑ i in Finset.range n, edist (f (u (i + 1))) (f (u i))) <= eVariationOn f s := by
  simpa using sum_le_of_monotoneOn_Icc (m := 0) (hu.mono Icc_subset_Iic_self) fun i hi => us i hi.2

/--
theorem `eVariationOn_eq_strictMonoOn` / 定理 `eVariationOn_eq_strictMonoOn`

English:
theorem eVariationOn_eq_strictMonoOn
  given: (f : α -> E) (s : Set α)
  proof: by
  apply le_antisymm
  · apply iSup_le
    rintro ⟨n, u, u_mono, u_mem⟩
    have : exists p : (n : Nat) × { u : Nat -> α // StrictMonoOn u (Iic n) ∧ forall i in Iic n, u i in s },
        (p.2 : Nat -> α) p.1 = u n ∧
        ∑ x in Finset.range n, edist (f (u (x + 1))) (f (u x)) =
        ∑ i in F

中文:
定理 eVariationOn_eq_strictMonoOn
  条件: (f : α -> E) (s : 集合 α)
  证明: by
  apply le_antisymm
  · apply iSup_le
    rintro ⟨n, u, u_mono, u_mem⟩
    have : exists p : (n : Nat) × { u : Nat -> α // StrictMonoOn u (Iic n) ∧ forall i in Iic n, u i in s },
        (p.2 : Nat -> α) p.1 = u n ∧
        ∑ x in Finset.range n, edist (f (u (x + 1))) (f (u x)) =
        ∑ i in F

Depends on / 依赖: Finset, Finset.range, StrictMonoOn, iSup_le, le_antisymm, u_mem, u_mono, v_mem, v_mono
-/
theorem eVariationOn_eq_strictMonoOn (f : α -> E) (s : Set α) :
    eVariationOn f s =
      ⨆ p : (n : Nat) × { u : Nat -> α // StrictMonoOn u (Iic n) ∧ forall i in Iic n, u i in s },
        ∑ i in Finset.range p.1, edist (f (p.2.1 (i + 1))) (f (p.2.1 i)) := by
  apply le_antisymm
  · apply iSup_le
    rintro ⟨n, u, u_mono, u_mem⟩
    have : exists p : (n : Nat) × { u : Nat -> α // StrictMonoOn u (Iic n) ∧ forall i in Iic n, u i in s },
        (p.2 : Nat -> α) p.1 = u n ∧
        ∑ x in Finset.range n, edist (f (u (x + 1))) (f (u x)) =
        ∑ i in Finset.range p.1, edist (f ((p.2 : Nat -> α) (i + 1))) (f ((p.2 : Nat -> α) i)) := by
      induction n with
      | zero => exact ⟨⟨0, ⟨u, by grind [StrictMonoOn], fun i hi => u_mem _⟩⟩, by simp⟩
      | succ n ih =>
        rcases ih with ⟨⟨m, v, v_mono, v_mem⟩, hv, h'v⟩
        simp only [Finset.sum_range_succ, Sigma.exists, Subtype.exists, mem_Iic, exists_and_left,
          exists_prop]
        rcases (u_mono (Nat.le_add_right n 1)).eq_or_lt with hn | hn
        · simp only [← hn, edist_self, add_zero]
          exact ⟨m, v, hv, ⟨v_mono, v_mem⟩, h'v⟩
        · refine ⟨m + 1, fun i => if i <= m then v i else u (n + 1), by simp,
            by grind [StrictMonoOn], ?_⟩
          simp only [h'v, ← hv, Order.add_one_le_iff, Finset.sum_range_succ, lt_self_iff_false,
            ↓reduceIte, le_refl]
          congr 1
          exact Finset.sum_congr rfl (by grind)
    rcases this with ⟨p, -, hp⟩
    rw [hp]
    apply le_iSup _ p
  · apply iSup_le
    rintro ⟨n, u, u_mono, u_mem⟩
    apply sum_le_of_monotoneOn_Iic (by grind [MonotoneOn, StrictMonoOn]) (by grind)

/--
theorem `mono` / 定理 `mono`

English:
theorem mono
  given: (f : α -> E) {s t : Set α} (hst : t subseteq s)
  statement: eVariationOn f t <= eVariationOn f s
  proof: by
  apply iSup_le _
  rintro ⟨n, ⟨u, hu, ut⟩⟩
  exact sum_le hu fun i => hst (ut i)

中文:
定理 mono
  条件: (f : α -> E) {s t : 集合 α} (hst : t subseteq s)
  结论: eVariationOn f t <= eVariationOn f s
  证明: by
  apply iSup_le _
  rintro ⟨n, ⟨u, hu, ut⟩⟩
  exact sum_le hu fun i => hst (ut i)

Depends on / 依赖: iSup_le, sum_le
-/
theorem mono (f : α -> E) {s t : Set α} (hst : t subseteq s) : eVariationOn f t <= eVariationOn f s := by
  apply iSup_le _
  rintro ⟨n, ⟨u, hu, ut⟩⟩
  exact sum_le hu fun i => hst (ut i)

/--
theorem `eq_biSup_inter_Icc` / 定理 `eq_biSup_inter_Icc`

English:
theorem eq_biSup_inter_Icc
  given: {f : α -> E} {s : Set α}
  statement: eVariationOn f s =
  proof: by
  apply le_antisymm ?_ (by simp [iSup_le_iff, mono f inter_subset_left])
  rw [eVariationOn]
  simp only [iSup_le_iff, Prod.forall, Subtype.forall, and_imp]
  intro n u hu hus
  calc ∑ x in Finset.range n, edist (f (u (x + 1))) (f (u x))
  _ <= eVariationOn f (s inter Icc (u 0) (u n)) :=
      su

中文:
定理 eq_biSup_inter_Icc
  条件: {f : α -> E} {s : 集合 α}
  结论: eVariationOn f s =
  证明: by
  apply le_antisymm ?_ (by simp [iSup_le_iff, mono f inter_subset_left])
  rw [eVariationOn]
  simp only [iSup_le_iff, Prod.forall, Subtype.forall, and_imp]
  intro n u hu hus
  calc ∑ x in Finset.range n, edist (f (u (x + 1))) (f (u x))
  _ <= eVariationOn f (s inter Icc (u 0) (u n)) :=
      su

Depends on / 依赖: Finset, Finset.range, Monotone, Prod.forall, Subtype, Subtype.forall, and_imp, eVariationOn, hu.monotoneOn, iSup_le_iff, inter_subset_left, le_antisymm, le_biSup, monotoneOn, sum_le_of_monotoneOn_Iic
-/
theorem eq_biSup_inter_Icc {f : α -> E} {s : Set α} : eVariationOn f s =
    ⨆ p in {p : α × α | p.1 in s ∧ p.2 in s ∧ p.1 <= p.2}, eVariationOn f (s inter Icc p.1 p.2) := by
  apply le_antisymm ?_ (by simp [iSup_le_iff, mono f inter_subset_left])
  rw [eVariationOn]
  simp only [iSup_le_iff, Prod.forall, Subtype.forall, and_imp]
  intro n u hu hus
  calc ∑ x in Finset.range n, edist (f (u (x + 1))) (f (u x))
  _ <= eVariationOn f (s inter Icc (u 0) (u n)) :=
      sum_le_of_monotoneOn_Iic (hu.monotoneOn _) (by grind [Monotone])
  _ <= ⨆ p in {p : α × α | p.1 in s ∧ p.2 in s ∧ p.1 <= p.2}, eVariationOn f (s inter Icc p.1 p.2) := by
    apply le_biSup (f := fun (p : α × α) => eVariationOn f (s inter Icc p.1 p.2)) (i := (u 0, u n))
    grind [Monotone]

/--
theorem `_root_.BoundedVariationOn.mono` / 定理 `_root_.BoundedVariationOn.mono`

English:
theorem _root_.BoundedVariationOn.mono
  statement: {f : α -> E} {s : Set α} (h : BoundedVariationOn f s)
  proof: ne_top_of_le_ne_top h (eVariationOn.mono f ht)

中文:
定理 _root_.BoundedVariationOn.mono
  结论: {f : α -> E} {s : 集合 α} (h : BoundedVariationOn f s)
  证明: ne_top_of_le_ne_top h (eVariationOn.mono f ht)

Depends on / 依赖: eVariationOn, eVariationOn.mono, ne_top_of_le_ne_top
-/
theorem _root_.BoundedVariationOn.mono {f : α -> E} {s : Set α} (h : BoundedVariationOn f s)
    {t : Set α} (ht : t subseteq s) : BoundedVariationOn f t :=
  ne_top_of_le_ne_top h (eVariationOn.mono f ht)

/--
theorem `_root_.BoundedVariationOn.locallyBoundedVariationOn` / 定理 `_root_.BoundedVariationOn.locallyBoundedVariationOn`

English:
theorem _root_.BoundedVariationOn.locallyBoundedVariationOn
  statement: {f : α -> E} {s : Set α}
  proof: fun _ _ _ _ =>
  h.mono inter_subset_left

中文:
定理 _root_.BoundedVariationOn.locallyBoundedVariationOn
  结论: {f : α -> E} {s : 集合 α}
  证明: fun _ _ _ _ =>
  h.mono inter_subset_left
-/
theorem _root_.BoundedVariationOn.locallyBoundedVariationOn {f : α -> E} {s : Set α}
    (h : BoundedVariationOn f s) : LocallyBoundedVariationOn f s := fun _ _ _ _ =>
  h.mono inter_subset_left

/--
theorem `congr` / 定理 `congr`

English:
theorem congr
  given: {f g : α -> E} {s : Set α} (h : EqOn f g s)
  statement: eVariationOn f s = eVariationOn g s
  proof: by
  grind [eVariationOn]

中文:
定理 congr
  条件: {f g : α -> E} {s : 集合 α} (h : EqOn f g s)
  结论: eVariationOn f s = eVariationOn g s
  证明: by
  grind [eVariationOn]

Depends on / 依赖: eVariationOn
-/
theorem congr {f g : α -> E} {s : Set α} (h : EqOn f g s) : eVariationOn f s = eVariationOn g s := by
  grind [eVariationOn]

/--
theorem `edist_le` / 定理 `edist_le`

English:
theorem edist_le
  given: (f : α -> E) {s : Set α} {x y : α} (hx : x in s) (hy : y in s)
  proof: by
  wlog hxy : y <= x generalizing x y
  · rw [edist_comm]
    exact this hy hx (le_of_not_ge hxy)
  let u : Nat -> α := fun n => if n = 0 then y else x
  have hu : Monotone u := monotone_nat_of_le_succ fun
  | 0 => hxy
  | (_ + 1) => le_rfl
  have us : forall i, u i in s := fun
  | 0 => hy
  | (_ 

中文:
定理 edist_le
  条件: (f : α -> E) {s : 集合 α} {x y : α} (hx : x in s) (hy : y in s)
  证明: by
  wlog hxy : y <= x generalizing x y
  · rw [edist_comm]
    exact this hy hx (le_of_not_ge hxy)
  let u : Nat -> α := fun n => if n = 0 then y else x
  have hu : Monotone u := monotone_nat_of_le_succ fun
  | 0 => hxy
  | (_ + 1) => le_rfl
  have us : forall i, u i in s := fun
  | 0 => hy
  | (_ 

Depends on / 依赖: Finset, Finset.sum_range_one, Monotone, edist_comm, generalizing, le_of_not_ge, le_rfl, monotone_nat_of_le_succ, sum_le, sum_range_one
-/
theorem edist_le (f : α -> E) {s : Set α} {x y : α} (hx : x in s) (hy : y in s) :
    edist (f x) (f y) <= eVariationOn f s := by
  wlog hxy : y <= x generalizing x y
  · rw [edist_comm]
    exact this hy hx (le_of_not_ge hxy)
  let u : Nat -> α := fun n => if n = 0 then y else x
  have hu : Monotone u := monotone_nat_of_le_succ fun
  | 0 => hxy
  | (_ + 1) => le_rfl
  have us : forall i, u i in s := fun
  | 0 => hy
  | (_ + 1) => hx
  simpa only [Finset.sum_range_one] using! sum_le (n := 1) hu us

/--
theorem `eq_zero_iff` / 定理 `eq_zero_iff`

English:
theorem eq_zero_iff
  given: (f : α -> E) {s : Set α}
  proof: by
  constructor
  · rintro h x xs y ys
    rw [← nonpos_iff_eq_zero]; rw [← h]
    exact edist_le f xs ys
  · rintro h
    dsimp only [eVariationOn]
    rw [ENNReal.iSup_eq_zero]
    rintro ⟨n, u, um, us⟩
    exact Finset.sum_eq_zero fun i _ => h _ (us i.succ) _ (us i)

中文:
定理 eq_zero_iff
  条件: (f : α -> E) {s : 集合 α}
  证明: by
  constructor
  · rintro h x xs y ys
    rw [← nonpos_iff_eq_zero]; rw [← h]
    exact edist_le f xs ys
  · rintro h
    dsimp only [eVariationOn]
    rw [ENNReal.iSup_eq_zero]
    rintro ⟨n, u, um, us⟩
    exact Finset.sum_eq_zero fun i _ => h _ (us i.succ) _ (us i)

Depends on / 依赖: ENNReal, ENNReal.iSup_eq_zero, Finset, Finset.sum_eq_zero, eVariationOn, edist_le, i.succ, iSup_eq_zero, nonpos_iff_eq_zero, sum_eq_zero
-/
theorem eq_zero_iff (f : α -> E) {s : Set α} :
    eVariationOn f s = 0 ↔ forall x in s, forall y in s, edist (f x) (f y) = 0 := by
  constructor
  · rintro h x xs y ys
    rw [← nonpos_iff_eq_zero]; rw [← h]
    exact edist_le f xs ys
  · rintro h
    dsimp only [eVariationOn]
    rw [ENNReal.iSup_eq_zero]
    rintro ⟨n, u, um, us⟩
    exact Finset.sum_eq_zero fun i _ => h _ (us i.succ) _ (us i)

/--
theorem `constant_on` / 定理 `constant_on`

English:
theorem constant_on
  given: {f : α -> E} {s : Set α} (hf : (f '' s).Subsingleton)
  proof: by
  rw [eq_zero_iff]
  rintro x xs y ys
  rw [hf ⟨x]; rw [xs]; rw [rfl⟩ ⟨y]; rw [ys]; rw [rfl⟩]; rw [edist_self]

@[simp]

中文:
定理 constant_on
  条件: {f : α -> E} {s : 集合 α} (hf : (f '' s).子单例)
  证明: by
  rw [eq_zero_iff]
  rintro x xs y ys
  rw [hf ⟨x]; rw [xs]; rw [rfl⟩ ⟨y]; rw [ys]; rw [rfl⟩]; rw [edist_self]

@[simp]

Depends on / 依赖: edist_self, eq_zero_iff
-/
theorem constant_on {f : α -> E} {s : Set α} (hf : (f '' s).Subsingleton) :
    eVariationOn f s = 0 := by
  rw [eq_zero_iff]
  rintro x xs y ys
  rw [hf ⟨x]; rw [xs]; rw [rfl⟩ ⟨y]; rw [ys]; rw [rfl⟩]; rw [edist_self]

@[simp]
/--
theorem `subsingleton` / 定理 `subsingleton`

English:
theorem subsingleton
  given: (f : α -> E) {s : Set α} (hs : s.Subsingleton)
  proof: constant_on (hs.image f)

@[simp]

中文:
定理 subsingleton
  条件: (f : α -> E) {s : 集合 α} (hs : s.子单例)
  证明: constant_on (hs.image f)

@[simp]
-/
protected theorem subsingleton (f : α -> E) {s : Set α} (hs : s.Subsingleton) :
    eVariationOn f s = 0 :=
  constant_on (hs.image f)

@[simp]
/--
theorem `_root_.BoundedVariationOn.of_subsingleton` / 定理 `_root_.BoundedVariationOn.of_subsingleton`

English:
theorem _root_.BoundedVariationOn.of_subsingleton
  given: {f : α -> E} {s : Set α} (hs : s.Subsingleton)
  proof: by
  simp [BoundedVariationOn, hs]

中文:
定理 _root_.BoundedVariationOn.of_subsingleton
  条件: {f : α -> E} {s : 集合 α} (hs : s.子单例)
  证明: by
  simp [BoundedVariationOn, hs]

Depends on / 依赖: BoundedVariationOn
-/
theorem _root_.BoundedVariationOn.of_subsingleton {f : α -> E} {s : Set α} (hs : s.Subsingleton) :
    BoundedVariationOn f s := by
  simp [BoundedVariationOn, hs]

/--
theorem `lowerSemicontinuous_aux` / 定理 `lowerSemicontinuous_aux`

English:
theorem lowerSemicontinuous_aux
  statement: {ι : Type*} {F : ι -> α -> E} {p : Filter ι} {f : α -> E} {s : Set α}
  proof: by
  obtain ⟨⟨n, ⟨u, um, us⟩⟩, hlt⟩ :
    exists p : Nat × { u : Nat -> α // Monotone u ∧ forall i, u i in s },
      v < ∑ i in Finset.range p.1, edist (f ((p.2 : Nat -> α) (i + 1))) (f ((p.2 : Nat -> α) i)) :=
    lt_iSup_iff.mp hv
  have : Tendsto (fun j => ∑ i in Finset.range n, edist (F j (u (i

中文:
定理 lowerSemicontinuous_aux
  结论: {ι : 类型} {F : ι -> α -> E} {p : 滤子 ι} {f : α -> E} {s : 集合 α}
  证明: by
  obtain ⟨⟨n, ⟨u, um, us⟩⟩, hlt⟩ :
    exists p : Nat × { u : Nat -> α // Monotone u ∧ forall i, u i in s },
      v < ∑ i in Finset.range p.1, edist (f ((p.2 : Nat -> α) (i + 1))) (f ((p.2 : Nat -> α) i)) :=
    lt_iSup_iff.mp hv
  have : Tendsto (fun j => ∑ i in Finset.range n, edist (F j (u (i

Depends on / 依赖: Finset, Finset.range, Monotone, Tendsto, Tendsto.edist, eventually_co, i.succ, lt_iSup_iff, lt_iSup_iff.mp, tendsto_finsetSum, this.eventually_co
-/
theorem lowerSemicontinuous_aux {ι : Type*} {F : ι -> α -> E} {p : Filter ι} {f : α -> E} {s : Set α}
    (Ffs : forall x in s, Tendsto (fun i => F i x) p (𝓝 (f x))) {v : Real>=0∞} (hv : v < eVariationOn f s) :
    forallᶠ n : ι in p, v < eVariationOn (F n) s := by
  obtain ⟨⟨n, ⟨u, um, us⟩⟩, hlt⟩ :
    exists p : Nat × { u : Nat -> α // Monotone u ∧ forall i, u i in s },
      v < ∑ i in Finset.range p.1, edist (f ((p.2 : Nat -> α) (i + 1))) (f ((p.2 : Nat -> α) i)) :=
    lt_iSup_iff.mp hv
  have : Tendsto (fun j => ∑ i in Finset.range n, edist (F j (u (i + 1))) (F j (u i))) p
      (𝓝 (∑ i in Finset.range n, edist (f (u (i + 1))) (f (u i)))) := by
    apply tendsto_finsetSum
    exact fun i _ => Tendsto.edist (Ffs (u i.succ) (us i.succ)) (Ffs (u i) (us i))
  exact (this.eventually_const_lt hlt).mono fun i h => h.trans_le (sum_le um us)

/--
theorem `lowerSemicontinuous` / 定理 `lowerSemicontinuous`

English:
theorem lowerSemicontinuous
  given: (s : Set α)
  proof: fun f => by
  apply @lowerSemicontinuous_aux _ _ _ _ (UniformOnFun α E (s.image singleton)) id (𝓝 f) f s _
  simpa only [UniformOnFun.tendsto_iff_tendstoUniformlyOn, mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, tendstoUniformlyOn_singleton_iff_tendsto] using! @tendsto_id _ 

中文:
定理 lowerSemicontinuous
  条件: (s : 集合 α)
  证明: fun f => by
  apply @lowerSemicontinuous_aux _ _ _ _ (UniformOnFun α E (s.image singleton)) id (𝓝 f) f s _
  simpa only [UniformOnFun.tendsto_iff_tendstoUniformlyOn, mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, tendstoUniformlyOn_singleton_iff_tendsto] using! @tendsto_id _ 
-/
protected theorem lowerSemicontinuous (s : Set α) :
    LowerSemicontinuous fun f : α ->ᵤ[s.image singleton] E => eVariationOn f s := fun f => by
  apply @lowerSemicontinuous_aux _ _ _ _ (UniformOnFun α E (s.image singleton)) id (𝓝 f) f s _
  simpa only [UniformOnFun.tendsto_iff_tendstoUniformlyOn, mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, tendstoUniformlyOn_singleton_iff_tendsto] using! @tendsto_id _ (𝓝 f)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lowerSemicontinuous_uniformOn` / 定理 `lowerSemicontinuous_uniformOn`

English:
theorem lowerSemicontinuous_uniformOn
  given: (s : Set α)
  proof: fun f => by
  apply @lowerSemicontinuous_aux _ _ _ _ (UniformOnFun α E {s}) id (𝓝 f) f s _
  have := @tendsto_id _ (𝓝 f)
  rw [UniformOnFun.tendsto_iff_tendstoUniformlyOn] at this
  simp_rw [← tendstoUniformlyOn_singleton_iff_tendsto]
  exact fun x xs => (this s rfl).mono (singleton_subset_iff.mpr x

中文:
定理 lowerSemicontinuous_uniformOn
  条件: (s : 集合 α)
  证明: fun f => by
  apply @lowerSemicontinuous_aux _ _ _ _ (UniformOnFun α E {s}) id (𝓝 f) f s _
  have := @tendsto_id _ (𝓝 f)
  rw [UniformOnFun.tendsto_iff_tendstoUniformlyOn] at this
  simp_rw [← tendstoUniformlyOn_singleton_iff_tendsto]
  exact fun x xs => (this s rfl).mono (singleton_subset_iff.mpr x

Depends on / 依赖: UniformOnFun, UniformOnFun.tendsto_iff_tendstoUniformlyOn, lowerSemicontinuous_aux, simp_rw, singleton_subset_iff, singleton_subset_iff.mpr, tendstoUniformlyOn_singleton_iff_tendsto, tendsto_id, tendsto_iff_tendstoUniformlyOn
-/
theorem lowerSemicontinuous_uniformOn (s : Set α) :
    LowerSemicontinuous fun f : α ->ᵤ[{s}] E => eVariationOn f s := fun f => by
  apply @lowerSemicontinuous_aux _ _ _ _ (UniformOnFun α E {s}) id (𝓝 f) f s _
  have := @tendsto_id _ (𝓝 f)
  rw [UniformOnFun.tendsto_iff_tendstoUniformlyOn] at this
  simp_rw [← tendstoUniformlyOn_singleton_iff_tendsto]
  exact fun x xs => (this s rfl).mono (singleton_subset_iff.mpr xs)

/--
theorem `_root_.BoundedVariationOn.dist_le` / 定理 `_root_.BoundedVariationOn.dist_le`

English:
theorem _root_.BoundedVariationOn.dist_le
  statement: {E : Type*} [PseudoMetricSpace E] {f : α -> E}
  proof: by
  rw [← ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg]; rw [ENNReal.ofReal_toReal h]; rw [← edist_dist]
  exact edist_le f hx hy

中文:
定理 _root_.BoundedVariationOn.dist_le
  结论: {E : 类型} [伪度量空间 E] {f : α -> E}
  证明: by
  rw [← ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg]; rw [ENNReal.ofReal_toReal h]; rw [← edist_dist]
  exact edist_le f hx hy

Depends on / 依赖: ENNReal, ENNReal.ofReal_le_ofReal_iff, ENNReal.ofReal_toReal, ENNReal.toReal_nonneg, edist_dist, edist_le, ofReal_le_ofReal_iff, ofReal_toReal, toReal_nonneg
-/
theorem _root_.BoundedVariationOn.dist_le {E : Type*} [PseudoMetricSpace E] {f : α -> E}
    {s : Set α} (h : BoundedVariationOn f s) {x y : α} (hx : x in s) (hy : y in s) :
    dist (f x) (f y) <= (eVariationOn f s).toReal := by
  rw [← ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg]; rw [ENNReal.ofReal_toReal h]; rw [← edist_dist]
  exact edist_le f hx hy

/--
theorem `_root_.BoundedVariationOn.sub_le` / 定理 `_root_.BoundedVariationOn.sub_le`

English:
theorem _root_.BoundedVariationOn.sub_le
  statement: {f : α -> Real} {s : Set α} (h : BoundedVariationOn f s)
  proof: by
  apply (le_abs_self _).trans
  rw [← Real.dist_eq]
  exact h.dist_le hx hy

中文:
定理 _root_.BoundedVariationOn.sub_le
  结论: {f : α -> 实数} {s : 集合 α} (h : BoundedVariationOn f s)
  证明: by
  apply (le_abs_self _).trans
  rw [← Real.dist_eq]
  exact h.dist_le hx hy

Depends on / 依赖: Real.dist_eq, dist_eq, dist_le, h.dist_le, le_abs_self
-/
theorem _root_.BoundedVariationOn.sub_le {f : α -> Real} {s : Set α} (h : BoundedVariationOn f s)
    {x y : α} (hx : x in s) (hy : y in s) : f x - f y <= (eVariationOn f s).toReal := by
  apply (le_abs_self _).trans
  rw [← Real.dist_eq]
  exact h.dist_le hx hy

/--
theorem `add_point` / 定理 `add_point`

English:
theorem add_point
  statement: (f : α -> E) {s : Set α} {x : α} (hx : x in s) (u : Nat -> α) (hu : Monotone u)
  proof: by
  rcases le_or_gt (u n) x with (h | h)
  · let v i := if i <= n then u i else x
    refine ⟨v, n + 2, by grind [Monotone], by grind, (mem_image _ _ _).2 ⟨n + 1, by grind⟩, ?_⟩
    calc
      (∑ i in Finset.range n, edist (f (u (i + 1))) (f (u i))) =
          ∑ i in Finset.range n, edist (f (v (i

中文:
定理 add_point
  结论: (f : α -> E) {s : 集合 α} {x : α} (hx : x in s) (u : 自然数 -> α) (hu : 递增 u)
  证明: by
  rcases le_or_gt (u n) x with (h | h)
  · let v i := if i <= n then u i else x
    refine ⟨v, n + 2, by grind [Monotone], by grind, (mem_image _ _ _).2 ⟨n + 1, by grind⟩, ?_⟩
    calc
      (∑ i in Finset.range n, edist (f (u (i + 1))) (f (u i))) =
          ∑ i in Finset.range n, edist (f (v (i

Depends on / 依赖: Finset, Finset.range, Finset.sum_congr, Monotone, Nat.fin, Nat.le_add_right, exists_N, le_add_right, le_or_gt, le_rfl, mem_image, sum_congr
-/
theorem add_point (f : α -> E) {s : Set α} {x : α} (hx : x in s) (u : Nat -> α) (hu : Monotone u)
    (us : forall i, u i in s) (n : Nat) :
    exists (v : Nat -> α) (m : Nat), Monotone v ∧ (forall i, v i in s) ∧ x in v '' Iio m ∧
      (∑ i in Finset.range n, edist (f (u (i + 1))) (f (u i))) <=
        ∑ j in Finset.range m, edist (f (v (j + 1))) (f (v j)) := by
  rcases le_or_gt (u n) x with (h | h)
  · let v i := if i <= n then u i else x
    refine ⟨v, n + 2, by grind [Monotone], by grind, (mem_image _ _ _).2 ⟨n + 1, by grind⟩, ?_⟩
    calc
      (∑ i in Finset.range n, edist (f (u (i + 1))) (f (u i))) =
          ∑ i in Finset.range n, edist (f (v (i + 1))) (f (v i)) := by grind [Finset.sum_congr]
      _ <= ∑ j in Finset.range (n + 2), edist (f (v (j + 1))) (f (v j)) := by
        gcongr
        apply Nat.le_add_right
  have exists_N : exists N, N <= n ∧ x < u N := ⟨n, le_rfl, h⟩
  let N := Nat.find exists_N
  have hN : N <= n ∧ x < u N := Nat.find_spec exists_N
  let w : Nat -> α := fun i => if i < N then u i else if i = N then x else u (i - 1)
  have hw : Monotone w := by
    apply monotone_nat_of_le_succ fun i => ?_
    rcases lt_trichotomy (i + 1) N with (hi | hi | hi)
    · grind [Monotone]
    · have A : i < N := hi ▸ i.lt_succ_self
      have := Nat.find_min exists_N A
      grind
    · grind [Monotone]
  refine ⟨w, n + 1, hw, by grind, (mem_image _ _ _).2 ⟨N, by grind⟩, ?_⟩
  rcases eq_zero_or_pos N with (Npos | Npos)
  · calc
      (∑ i in Finset.range n, edist (f (u (i + 1))) (f (u i))) =
          ∑ i in Finset.range n, edist (f (w (1 + i + 1))) (f (w (1 + i))) := by grind
      _ = ∑ i in Finset.Ico 1 (n + 1), edist (f (w (i + 1))) (f (w i)) := by
        rw [Finset.range_eq_Ico]
        exact Finset.sum_Ico_add (fun i => edist (f (w (i + 1))) (f (w i))) 0 n 1
      _ <= ∑ j in Finset.range (n + 1), edist (f (w (j + 1))) (f (w j)) := by
        rw [Finset.range_eq_Ico]
        gcongr
        exact zero_le_one
  · calc
      (∑ i in Finset.range n, edist (f (u (i + 1))) (f (u i))) =
          ((∑ i in Finset.Ico 0 (N - 1), edist (f (u (i + 1))) (f (u i))) +
              ∑ i in Finset.Ico (N - 1) N, edist (f (u (i + 1))) (f (u i))) +
            ∑ i in Finset.Ico N n, edist (f (u (i + 1))) (f (u i)) := by
        rw [Finset.sum_Ico_consecutive]; rw [Finset.sum_Ico_consecutive]; rw [Finset.range_eq_Ico] <;> grind
      _ = (∑ i in Finset.Ico 0 (N - 1), edist (f (w (i + 1))) (f (w i))) +
              edist (f (u N)) (f (u (N - 1))) +
            ∑ i in Finset.Ico N n, edist (f (w (1 + i + 1))) (f (w (1 + i))) := by
        congr 1
        · congr 1
          · grind [Finset.sum_congr]
          · have A : N - 1 + 1 = N := Nat.succ_pred_eq_of_pos Npos
            have : Finset.Ico (N - 1) N = {N - 1} := by rw [← Nat.Ico_succ_singleton, A]
            simp only [this, A, Finset.sum_singleton]
        · grind [Finset.sum_congr]
      _ = (∑ i in Finset.Ico 0 (N - 1), edist (f (w (i + 1))) (f (w i))) +
              edist (f (w (N + 1))) (f (w (N - 1))) +
            ∑ i in Finset.Ico (N + 1) (n + 1), edist (f (w (i + 1))) (f (w i)) := by
        congr 1
        · grind
        · exact Finset.sum_Ico_add (fun i => edist (f (w (i + 1))) (f (w i))) N n 1
      _ <= ((∑ i in Finset.Ico 0 (N - 1), edist (f (w (i + 1))) (f (w i))) +
              ∑ i in Finset.Ico (N - 1) (N + 1), edist (f (w (i + 1))) (f (w i))) +
            ∑ i in Finset.Ico (N + 1) (n + 1), edist (f (w (i + 1))) (f (w i)) := by
        refine add_le_add (add_le_add le_rfl ?_) le_rfl
        have A : N - 1 + 1 = N := Nat.succ_pred_eq_of_pos Npos
        have B : N - 1 + 1 < N + 1 := A.symm ▸ N.lt_succ_self
        have C : N - 1 < N + 1 := lt_of_le_of_lt N.pred_le N.lt_succ_self
        rw [Finset.sum_eq_sum_Ico_succ_bot C]; rw [Finset.sum_eq_sum_Ico_succ_bot B]; rw [A]; rw [Finset.Ico_self]; rw [Finset.sum_empty]; rw [add_zero]; rw [add_comm (edist _ _)]
        exact edist_triangle _ _ _
      _ = ∑ j in Finset.range (n + 1), edist (f (w (j + 1))) (f (w j)) := by
        rw [Finset.sum_Ico_consecutive]; rw [Finset.sum_Ico_consecutive]; rw [Finset.range_eq_Ico] <;> grind

/--
theorem `add_le_union` / 定理 `add_le_union`

English:
theorem add_le_union
  given: (f : α -> E) {s t : Set α} (h : forall x in s, forall y in t, x <= y)
  proof: by
  by_cases hs : s = ∅
  · simp [hs]
  have : Nonempty { u // Monotone u ∧ forall i : Nat, u i in s } :=
    nonempty_monotone_mem (nonempty_iff_ne_empty.2 hs)
  by_cases ht : t = ∅
  · simp [ht]
  have : Nonempty { u // Monotone u ∧ forall i : Nat, u i in t } :=
    nonempty_monotone_mem (nonempt

中文:
定理 add_le_union
  条件: (f : α -> E) {s t : 集合 α} (h : 对任意 x in s, 对任意 y in t, x <= y)
  证明: by
  by_cases hs : s = ∅
  · simp [hs]
  have : Nonempty { u // Monotone u ∧ forall i : Nat, u i in s } :=
    nonempty_monotone_mem (nonempty_iff_ne_empty.2 hs)
  by_cases ht : t = ∅
  · simp [ht]
  have : Nonempty { u // Monotone u ∧ forall i : Nat, u i in t } :=
    nonempty_monotone_mem (nonempt

Depends on / 依赖: ENNReal, ENNReal.iSup_add_iSup_le, Monotone, Nonempty, iSup_add_iSup_le, nonempty_iff_ne_empty, nonempty_monotone_mem
-/
theorem add_le_union (f : α -> E) {s t : Set α} (h : forall x in s, forall y in t, x <= y) :
    eVariationOn f s + eVariationOn f t <= eVariationOn f (s union t) := by
  by_cases hs : s = ∅
  · simp [hs]
  have : Nonempty { u // Monotone u ∧ forall i : Nat, u i in s } :=
    nonempty_monotone_mem (nonempty_iff_ne_empty.2 hs)
  by_cases ht : t = ∅
  · simp [ht]
  have : Nonempty { u // Monotone u ∧ forall i : Nat, u i in t } :=
    nonempty_monotone_mem (nonempty_iff_ne_empty.2 ht)
  refine ENNReal.iSup_add_iSup_le ?_
  /- We start from two sequences `u` and `v` along `s` and `t` respectively, and we build a new
    sequence `w` along `s ∪ t` by juxtaposing them. Its variation is larger than the sum of the
    variations. -/
  rintro ⟨n, ⟨u, hu, us⟩⟩ ⟨m, ⟨v, hv, vt⟩⟩
  let w i := if i <= n then u i else v (i - (n + 1))
  calc
    ((∑ i in Finset.range n, edist (f (u (i + 1))) (f (u i))) +
          ∑ i in Finset.range m, edist (f (v (i + 1))) (f (v i))) =
        (∑ i in Finset.range n, edist (f (w (i + 1))) (f (w i))) +
          ∑ i in Finset.range m, edist (f (w (n + 1 + i + 1))) (f (w (n + 1 + i))) := by
      dsimp only [w]
      congr 1
      · grind [Finset.sum_congr]
      · grind
    _ = (∑ i in Finset.range n, edist (f (w (i + 1))) (f (w i))) +
          ∑ i in Finset.Ico (n + 1) (n + 1 + m), edist (f (w (i + 1))) (f (w i)) := by
      congr 1
      rw [Finset.range_eq_Ico]
      convert!
          Finset.sum_Ico_add (fun i : Nat => edist (f (w (i + 1))) (f (w i))) 0 m (n + 1) using 3 <;>
        abel
    _ <= ∑ i in Finset.range (n + 1 + m), edist (f (w (i + 1))) (f (w i)) := by
      rw [← Finset.sum_union]
      · gcongr; grind
      · exact Finset.disjoint_left.2 (by grind)
    _ <= eVariationOn f (s union t) := sum_le (by grind [Monotone]) (by grind)

/--
theorem `union` / 定理 `union`

English:
theorem union
  given: (f : α -> E) {s t : Set α} {x : α} (hs : IsGreatest s x) (ht : IsLeast t x)
  proof: by
  apply (eVariationOn.add_le_union f fun a ha b hb => (hs.2 ha).trans (ht.2 hb)).antisymm'
  refine iSup_le fun ⟨n, ⟨u, hu, ust⟩⟩ => ?_
  obtain ⟨v, m, hv, vst, ⟨N, hN, rfl⟩, huv⟩ :=
    eVariationOn.add_point f (mem_union_left t hs.1) u hu ust n
  apply huv.trans
  rw [Finset.range_eq_Ico]; rw [

中文:
定理 union
  条件: (f : α -> E) {s t : 集合 α} {x : α} (hs : IsGreatest s x) (ht : IsLeast t x)
  证明: by
  apply (eVariationOn.add_le_union f fun a ha b hb => (hs.2 ha).trans (ht.2 hb)).antisymm'
  refine iSup_le fun ⟨n, ⟨u, hu, ust⟩⟩ => ?_
  obtain ⟨v, m, hv, vst, ⟨N, hN, rfl⟩, huv⟩ :=
    eVariationOn.add_point f (mem_union_left t hs.1) u hu ust n
  apply huv.trans
  rw [Finset.range_eq_Ico]; rw [

Depends on / 依赖: Finset, Finset.range_eq_Ico, Finset.sum_Ico_consecutive, add_le_add, add_le_union, add_point, antisymm, eVariationOn, eVariationOn.add_le_union, eVariationOn.add_point, hN.le, huv.trans, hv.monotoneOn, iSup_le, mem_union_left, monotoneOn, range_eq_Ico, sum_Ico_consecutive, sum_le_of_monotoneOn_Icc, zero_le
-/
theorem union (f : α -> E) {s t : Set α} {x : α} (hs : IsGreatest s x) (ht : IsLeast t x) :
    eVariationOn f (s union t) = eVariationOn f s + eVariationOn f t := by
  apply (eVariationOn.add_le_union f fun a ha b hb => (hs.2 ha).trans (ht.2 hb)).antisymm'
  refine iSup_le fun ⟨n, ⟨u, hu, ust⟩⟩ => ?_
  obtain ⟨v, m, hv, vst, ⟨N, hN, rfl⟩, huv⟩ :=
    eVariationOn.add_point f (mem_union_left t hs.1) u hu ust n
  apply huv.trans
  rw [Finset.range_eq_Ico]; rw [← Finset.sum_Ico_consecutive _ zero_le hN.le]
  apply add_le_add <;> refine sum_le_of_monotoneOn_Icc (hv.monotoneOn _) fun i hi => ?_
  · exact (vst i).elim id (fun h => (hv hi.2).antisymm (ht.2 h) ▸ hs.1)
  · exact (vst i).elim (fun h => (hs.2 h).antisymm (hv hi.1) ▸ ht.1) id

/--
theorem `Icc_add_Icc` / 定理 `Icc_add_Icc`

English:
theorem Icc_add_Icc
  given: (f : α -> E) {s : Set α} {a b c : α} (hab : a <= b) (hbc : b <= c) (hb : b in s)
  proof: by
  have A : IsGreatest (s inter Icc a b) b :=
    ⟨⟨hb, hab, le_rfl⟩, inter_subset_right.trans Icc_subset_Iic_self⟩
  have B : IsLeast (s inter Icc b c) b :=
    ⟨⟨hb, le_rfl, hbc⟩, inter_subset_right.trans Icc_subset_Ici_self⟩
  rw [← eVariationOn.union f A B]; rw [← inter_union_distrib_left]; rw

中文:
定理 Icc_add_Icc
  条件: (f : α -> E) {s : 集合 α} {a b c : α} (hab : a <= b) (hbc : b <= c) (hb : b in s)
  证明: by
  have A : IsGreatest (s inter Icc a b) b :=
    ⟨⟨hb, hab, le_rfl⟩, inter_subset_right.trans Icc_subset_Iic_self⟩
  have B : IsLeast (s inter Icc b c) b :=
    ⟨⟨hb, le_rfl, hbc⟩, inter_subset_right.trans Icc_subset_Ici_self⟩
  rw [← eVariationOn.union f A B]; rw [← inter_union_distrib_left]; rw

Depends on / 依赖: Icc_subset_Ici_self, Icc_subset_Iic_self, Icc_union_Icc_eq_Icc, IsGreatest, IsLeast, eVariationOn, eVariationOn.union, inter_subset_right, inter_subset_right.trans, inter_union_distrib_left, le_rfl
-/
theorem Icc_add_Icc (f : α -> E) {s : Set α} {a b c : α} (hab : a <= b) (hbc : b <= c) (hb : b in s) :
    eVariationOn f (s inter Icc a b) + eVariationOn f (s inter Icc b c) = eVariationOn f (s inter Icc a c) := by
  have A : IsGreatest (s inter Icc a b) b :=
    ⟨⟨hb, hab, le_rfl⟩, inter_subset_right.trans Icc_subset_Iic_self⟩
  have B : IsLeast (s inter Icc b c) b :=
    ⟨⟨hb, le_rfl, hbc⟩, inter_subset_right.trans Icc_subset_Ici_self⟩
  rw [← eVariationOn.union f A B]; rw [← inter_union_distrib_left]; rw [Icc_union_Icc_eq_Icc hab hbc]

/--
theorem `sum` / 定理 `sum`

English:
theorem sum
  statement: (f : α -> E) {s : Set α} {E : Nat -> α} (hE : Monotone E) {n : Nat}
  proof: by
  induction n with
  | zero => simp [Subsingleton.inter_singleton]
  | succ n ih =>
    by_cases hn₀ : n = 0
    · simp [hn₀]
    rw [← Icc_add_Icc (b := E n)]
    · rw [← ih (by intros; apply hn <;> omega), Finset.sum_range_succ]
    · apply hE; lia
    · apply hE; lia
    · apply hn <;> omega

中文:
定理 求和
  结论: (f : α -> E) {s : 集合 α} {E : 自然数 -> α} (hE : 递增 E) {n : 自然数}
  证明: by
  induction n with
  | zero => simp [Subsingleton.inter_singleton]
  | succ n ih =>
    by_cases hn₀ : n = 0
    · simp [hn₀]
    rw [← Icc_add_Icc (b := E n)]
    · rw [← ih (by intros; apply hn <;> omega), Finset.sum_range_succ]
    · apply hE; lia
    · apply hE; lia
    · apply hn <;> omega

Depends on / 依赖: Finset, Finset.sum_range_succ, Icc_add_Icc, Subsingleton, Subsingleton.inter_singleton, inter_singleton, intros, sum_range_succ
-/
theorem sum (f : α -> E) {s : Set α} {E : Nat -> α} (hE : Monotone E) {n : Nat}
    (hn : forall i, 0 < i -> i < n -> E i in s) :
    ∑ i in Finset.range n, eVariationOn f (s inter Icc (E i) (E (i + 1))) =
      eVariationOn f (s inter Icc (E 0) (E n)) := by
  induction n with
  | zero => simp [Subsingleton.inter_singleton]
  | succ n ih =>
    by_cases hn₀ : n = 0
    · simp [hn₀]
    rw [← Icc_add_Icc (b := E n)]
    · rw [← ih (by intros; apply hn <;> omega), Finset.sum_range_succ]
    · apply hE; lia
    · apply hE; lia
    · apply hn <;> omega

/--
theorem `sum'` / 定理 `sum'`

English:
theorem sum'
  given: (f : α -> E) {I : Nat -> α} (hI : Monotone I) {n : Nat}
  proof: by
  convert!
      sum f hI (s := Icc (I 0) (I n)) (n := n)
        (hn := by intros; rw [mem_Icc]; constructor <;> (apply hI; lia))
    with i hi
  · simp only [right_eq_inter]
    gcongr <;> (apply hI; rw [Finset.mem_range] at hi; lia)
  · simp

中文:
定理 求和'
  条件: (f : α -> E) {I : 自然数 -> α} (hI : 递增 I) {n : 自然数}
  证明: by
  convert!
      sum f hI (s := Icc (I 0) (I n)) (n := n)
        (hn := by intros; rw [mem_Icc]; constructor <;> (apply hI; lia))
    with i hi
  · simp only [right_eq_inter]
    gcongr <;> (apply hI; rw [Finset.mem_range] at hi; lia)
  · simp

Depends on / 依赖: Finset, Finset.mem_range, convert, intros, mem_Icc, mem_range, right_eq_inter
-/
theorem sum' (f : α -> E) {I : Nat -> α} (hI : Monotone I) {n : Nat} :
    ∑ i in Finset.range n, eVariationOn f (Icc (I i) (I (i + 1)))
     = eVariationOn f (Icc (I 0) (I n)) := by
  convert!
      sum f hI (s := Icc (I 0) (I n)) (n := n)
        (hn := by intros; rw [mem_Icc]; constructor <;> (apply hI; lia))
    with i hi
  · simp only [right_eq_inter]
    gcongr <;> (apply hI; rw [Finset.mem_range] at hi; lia)
  · simp

/-- The variation of `f` on a two-point set `{a, b}` is the distance between its two values. -/
@[simp]
/--
theorem `pair` / 定理 `pair`

English:
theorem pair
  given: (f : α -> E) (a b : α)
  statement: eVariationOn f {a, b} = edist (f a) (f b)
  proof: by
  wlog hab : a <= b generalizing a b
  · simpa [edist_comm, pair_comm] using this b a (le_of_not_ge hab)
  · apply le_antisymm _ (edist_le f (by simp) (by simp))
    simp only [eVariationOn_eq_strictMonoOn, iSup_le_iff]
    rintro ⟨n, u, hmono, hi⟩
    rcases (by omega : n = 0 ∨ n = 1 ∨ 2 <= n) w

中文:
定理 pair
  条件: (f : α -> E) (a b : α)
  结论: eVariationOn f {a, b} = edist (f a) (f b)
  证明: by
  wlog hab : a <= b generalizing a b
  · simpa [edist_comm, pair_comm] using this b a (le_of_not_ge hab)
  · apply le_antisymm _ (edist_le f (by simp) (by simp))
    simp only [eVariationOn_eq_strictMonoOn, iSup_le_iff]
    rintro ⟨n, u, hmono, hi⟩
    rcases (by omega : n = 0 ∨ n = 1 ∨ 2 <= n) w

Depends on / 依赖: eVariationOn_eq_strictMonoOn, edist_comm, edist_le, generalizing, iSup_le_iff, le_antisymm, le_of_not_ge, pair_comm, zero_lt_one
-/
theorem pair (f : α -> E) (a b : α) : eVariationOn f {a, b} = edist (f a) (f b) := by
  wlog hab : a <= b generalizing a b
  · simpa [edist_comm, pair_comm] using this b a (le_of_not_ge hab)
  · apply le_antisymm _ (edist_le f (by simp) (by simp))
    simp only [eVariationOn_eq_strictMonoOn, iSup_le_iff]
    rintro ⟨n, u, hmono, hi⟩
    rcases (by omega : n = 0 ∨ n = 1 ∨ 2 <= n) with rfl | rfl | hn
    · simp
    · have := hmono (by simp) (by simp) zero_lt_one
      simp [(by grind : u 0 = a), (by grind : u 1 = b), edist_comm]
    · have := hmono (by simp) (by grind) zero_lt_one
      have := hmono (by grind) (by grind) one_lt_two
      grind

/--
theorem `union'` / 定理 `union'`

English:
theorem union'
  statement: (f : α -> E) {s t : Set α} {x y : α} (hs : IsGreatest s x) (ht : IsLeast t y)
  proof: by
  rw [(by grind [hs.1]; rw [ht.1] : s union t = (s union {x, y}) union t), union f _ ht, union f hs]
  <;> simp [IsLeast, IsGreatest, hxy, upperBounds_mono_mem hxy hs.2]

中文:
定理 union'
  结论: (f : α -> E) {s t : 集合 α} {x y : α} (hs : IsGreatest s x) (ht : IsLeast t y)
  证明: by
  rw [(by grind [hs.1]; rw [ht.1] : s union t = (s union {x, y}) union t), union f _ ht, union f hs]
  <;> simp [IsLeast, IsGreatest, hxy, upperBounds_mono_mem hxy hs.2]

Depends on / 依赖: IsGreatest, IsLeast, upperBounds_mono_mem
-/
theorem union' (f : α -> E) {s t : Set α} {x y : α} (hs : IsGreatest s x) (ht : IsLeast t y)
    (hxy : x <= y) :
    eVariationOn f (s union t) = eVariationOn f s + edist (f x) (f y) + eVariationOn f t := by
  rw [(by grind [hs.1]; rw [ht.1] : s union t = (s union {x, y}) union t), union f _ ht, union f hs]
  <;> simp [IsLeast, IsGreatest, hxy, upperBounds_mono_mem hxy hs.2]

/--
theorem `image_range_of_monotone` / 定理 `image_range_of_monotone`

English:
theorem image_range_of_monotone
  given: (f : α -> E) {u : Nat -> α} (hu : Monotone u) (n : Nat)
  proof: by
  induction n with
  | zero => simp [Iic]
  | succ n ih =>
    rw [(by grind : u '' Iic (n + 1) = u '' Iic n union {u n]; rw [u (n + 1)})]; rw [union f]
    · simp [Finset.sum_range_succ, ih]
    · simpa [IsGreatest, upperBounds] using ⟨⟨n, by simp⟩, fun a ha => hu ha⟩
    · simp [IsLeast, hu n.l

中文:
定理 image_range_of_monotone
  条件: (f : α -> E) {u : 自然数 -> α} (hu : 递增 u) (n : 自然数)
  证明: by
  induction n with
  | zero => simp [Iic]
  | succ n ih =>
    rw [(by grind : u '' Iic (n + 1) = u '' Iic n union {u n]; rw [u (n + 1)})]; rw [union f]
    · simp [Finset.sum_range_succ, ih]
    · simpa [IsGreatest, upperBounds] using ⟨⟨n, by simp⟩, fun a ha => hu ha⟩
    · simp [IsLeast, hu n.l

Depends on / 依赖: Finset, Finset.sum_range_succ, IsGreatest, IsLeast, le_succ, n.le_succ, sum_range_succ, upperBounds
-/
theorem image_range_of_monotone (f : α -> E) {u : Nat -> α} (hu : Monotone u) (n : Nat) :
    eVariationOn f (u '' Iic n) = ∑ i in .range n, edist (f (u i)) (f (u (i + 1))) := by
  induction n with
  | zero => simp [Iic]
  | succ n ih =>
    rw [(by grind : u '' Iic (n + 1) = u '' Iic n union {u n]; rw [u (n + 1)})]; rw [union f]
    · simp [Finset.sum_range_succ, ih]
    · simpa [IsGreatest, upperBounds] using ⟨⟨n, by simp⟩, fun a ha => hu ha⟩
    · simp [IsLeast, hu n.le_succ]

/--
theorem `_root_.BoundedVariationOn.of_finset` / 定理 `_root_.BoundedVariationOn.of_finset`

English:
theorem _root_.BoundedVariationOn.of_finset
  statement: {E} [PseudoMetricSpace E] (f : α -> E)
  proof: by
  obtain rfl | hne := s.eq_empty_or_nonempty
  · simp [BoundedVariationOn]
  have := s.card_pos.2 hne
  let u : Nat -> α := fun n => s.orderEmbOfFin rfl ⟨min n (s.card - 1), by grind⟩
  have : s = u '' Iic (s.card - 1) := by
    ext
    simp only [← s.range_orderEmbOfFin rfl, mem_image, mem_Iic, 

中文:
定理 _root_.BoundedVariationOn.of_finset
  结论: {E} [伪度量空间 E] (f : α -> E)
  证明: by
  obtain rfl | hne := s.eq_empty_or_nonempty
  · simp [BoundedVariationOn]
  have := s.card_pos.2 hne
  let u : Nat -> α := fun n => s.orderEmbOfFin rfl ⟨min n (s.card - 1), by grind⟩
  have : s = u '' Iic (s.card - 1) := by
    ext
    simp only [← s.range_orderEmbOfFin rfl, mem_image, mem_Iic, 
-/
private theorem _root_.BoundedVariationOn.of_finset {E} [PseudoMetricSpace E] (f : α -> E)
    (s : Finset α) : BoundedVariationOn f s := by
  obtain rfl | hne := s.eq_empty_or_nonempty
  · simp [BoundedVariationOn]
  have := s.card_pos.2 hne
  let u : Nat -> α := fun n => s.orderEmbOfFin rfl ⟨min n (s.card - 1), by grind⟩
  have : s = u '' Iic (s.card - 1) := by
    ext
    simp only [← s.range_orderEmbOfFin rfl, mem_image, mem_Iic, mem_range, u]
    constructor
    · rintro ⟨i, rfl⟩; exact ⟨i.val, by grind⟩
    · rintro ⟨i, hi, rfl⟩; use ⟨i, by omega⟩; congr; omega
  have hmono : Monotone u := fun _ _ _ => OrderEmbedding.monotone _ (by grind)
  simp [BoundedVariationOn, this, image_range_of_monotone f hmono _]

/-- A function valued in a metric space has bounded variation on any `Finset` (the finiteness of
the space's distances makes the total variation finite). -/
@[simp]
/--
theorem `_root_.BoundedVariationOn.of_finite` / 定理 `_root_.BoundedVariationOn.of_finite`

English:
theorem _root_.BoundedVariationOn.of_finite
  statement: {E} [PseudoMetricSpace E] (f : α -> E) (s : Set α)
  proof: by
  simpa using BoundedVariationOn.of_finset f s.toFinite.toFinset

中文:
定理 _root_.BoundedVariationOn.of_finite
  结论: {E} [伪度量空间 E] (f : α -> E) (s : 集合 α)
  证明: by
  simpa using BoundedVariationOn.of_finset f s.toFinite.toFinset

Depends on / 依赖: BoundedVariationOn, BoundedVariationOn.of_finset, of_finset, s.toFinite.toFinset, toFinite, toFinset
-/
theorem _root_.BoundedVariationOn.of_finite {E} [PseudoMetricSpace E] (f : α -> E) (s : Set α)
[Finite s] : BoundedVariationOn f s := by
  simpa using BoundedVariationOn.of_finset f s.toFinite.toFinset

/-! ### Composition of bounded variation functions with monotone functions -/

section Monotone

variable {β : Type*} [LinearOrder β]

/--
theorem `comp_le_of_monotoneOn` / 定理 `comp_le_of_monotoneOn`

English:
theorem comp_le_of_monotoneOn
  statement: (f : α -> E) {s : Set α} {t : Set β} (φ : β -> α) (hφ : MonotoneOn φ t)
  proof: iSup_le fun ⟨n, u, hu, ut⟩ =>
    le_iSup_of_le ⟨n, φ ∘ u, fun x y xy => hφ (ut x) (ut y) (hu xy), fun i => φst (ut i)⟩ le_rfl

中文:
定理 comp_le_of_monotoneOn
  结论: (f : α -> E) {s : 集合 α} {t : 集合 β} (φ : β -> α) (hφ : MonotoneOn φ t)
  证明: iSup_le fun ⟨n, u, hu, ut⟩ =>
    le_iSup_of_le ⟨n, φ ∘ u, fun x y xy => hφ (ut x) (ut y) (hu xy), fun i => φst (ut i)⟩ le_rfl

Depends on / 依赖: iSup_le, le_iSup_of_le, le_rfl
-/
theorem comp_le_of_monotoneOn (f : α -> E) {s : Set α} {t : Set β} (φ : β -> α) (hφ : MonotoneOn φ t)
    (φst : MapsTo φ t s) : eVariationOn (f ∘ φ) t <= eVariationOn f s :=
  iSup_le fun ⟨n, u, hu, ut⟩ =>
    le_iSup_of_le ⟨n, φ ∘ u, fun x y xy => hφ (ut x) (ut y) (hu xy), fun i => φst (ut i)⟩ le_rfl

/--
theorem `comp_le_of_antitoneOn` / 定理 `comp_le_of_antitoneOn`

English:
theorem comp_le_of_antitoneOn
  statement: (f : α -> E) {s : Set α} {t : Set β} (φ : β -> α) (hφ : AntitoneOn φ t)
  proof: by
  refine iSup_le ?_
  rintro ⟨n, u, hu, ut⟩
  rw [← Finset.sum_range_reflect]
refine (Finset.sum_congr rfl fun x hx => ?_).trans_le le_iSup_of_le
    ⟨n, fun i => φ (u <| n - i), fun x y xy => hφ (ut _) (ut _) (hu <| Nat.sub_le_sub_left xy n),
      fun i => φst (ut _)⟩
    le_rfl
  rw [Finset.me

中文:
定理 comp_le_of_antitoneOn
  结论: (f : α -> E) {s : 集合 α} {t : 集合 β} (φ : β -> α) (hφ : AntitoneOn φ t)
  证明: by
  refine iSup_le ?_
  rintro ⟨n, u, hu, ut⟩
  rw [← Finset.sum_range_reflect]
refine (Finset.sum_congr rfl fun x hx => ?_).trans_le le_iSup_of_le
    ⟨n, fun i => φ (u <| n - i), fun x y xy => hφ (ut _) (ut _) (hu <| Nat.sub_le_sub_left xy n),
      fun i => φst (ut _)⟩
    le_rfl
  rw [Finset.me

Depends on / 依赖: Finset, Finset.mem_range, Finset.sum_congr, Finset.sum_range_reflect, Function, Function.comp_apply, Nat.sub_le_sub_left, Subtype, Subtype.coe_mk, coe_mk, comp_apply, edist_comm, iSup_le, le_iSup_of_le, le_rfl, mem_range, sub_le_sub_left, sum_congr, sum_range_reflect, trans_le
-/
theorem comp_le_of_antitoneOn (f : α -> E) {s : Set α} {t : Set β} (φ : β -> α) (hφ : AntitoneOn φ t)
    (φst : MapsTo φ t s) : eVariationOn (f ∘ φ) t <= eVariationOn f s := by
  refine iSup_le ?_
  rintro ⟨n, u, hu, ut⟩
  rw [← Finset.sum_range_reflect]
refine (Finset.sum_congr rfl fun x hx => ?_).trans_le le_iSup_of_le
    ⟨n, fun i => φ (u <| n - i), fun x y xy => hφ (ut _) (ut _) (hu <| Nat.sub_le_sub_left xy n),
      fun i => φst (ut _)⟩
    le_rfl
  rw [Finset.mem_range] at hx
  dsimp only [Subtype.coe_mk, Function.comp_apply]
  rw [edist_comm]
  congr 4 <;> lia

/--
theorem `comp_eq_of_monotoneOn` / 定理 `comp_eq_of_monotoneOn`

English:
theorem comp_eq_of_monotoneOn
  given: (f : α -> E) {t : Set β} (φ : β -> α) (hφ : MonotoneOn φ t)
  proof: by
  apply le_antisymm (comp_le_of_monotoneOn f φ hφ (mapsTo_image φ t))
  cases isEmpty_or_nonempty β
  · simp [Set.eq_empty_of_isEmpty]
  let ψ := φ.invFunOn t
  have ψφs : EqOn (φ ∘ ψ) id (φ '' t) := (surjOn_image φ t).rightInvOn_invFunOn
  have ψts : MapsTo ψ (φ '' t) t := (surjOn_image φ t).map

中文:
定理 comp_eq_of_monotoneOn
  条件: (f : α -> E) {t : 集合 β} (φ : β -> α) (hφ : MonotoneOn φ t)
  证明: by
  apply le_antisymm (comp_le_of_monotoneOn f φ hφ (mapsTo_image φ t))
  cases isEmpty_or_nonempty β
  · simp [Set.eq_empty_of_isEmpty]
  let ψ := φ.invFunOn t
  have ψφs : EqOn (φ ∘ ψ) id (φ '' t) := (surjOn_image φ t).rightInvOn_invFunOn
  have ψts : MapsTo ψ (φ '' t) t := (surjOn_image φ t).map

Depends on / 依赖: Function, Function.monotoneOn_of_rightInvOn_of_mapsTo, MapsTo, MonotoneOn, Set.eq_empty_of_isEmpty, comp_le_of_monotoneOn, comp_left, eVariationOn, eq_empty_of_isEmpty, eq_of_eqOn, invFunOn, isEmpty_or_nonempty, le_antisymm, mapsTo_image, mapsTo_invFunOn, monotoneOn_of_rightInvOn_of_mapsTo, rightInvOn_invFunOn, s.comp_left, surjOn_image
-/
theorem comp_eq_of_monotoneOn (f : α -> E) {t : Set β} (φ : β -> α) (hφ : MonotoneOn φ t) :
    eVariationOn (f ∘ φ) t = eVariationOn f (φ '' t) := by
  apply le_antisymm (comp_le_of_monotoneOn f φ hφ (mapsTo_image φ t))
  cases isEmpty_or_nonempty β
  · simp [Set.eq_empty_of_isEmpty]
  let ψ := φ.invFunOn t
  have ψφs : EqOn (φ ∘ ψ) id (φ '' t) := (surjOn_image φ t).rightInvOn_invFunOn
  have ψts : MapsTo ψ (φ '' t) t := (surjOn_image φ t).mapsTo_invFunOn
  have hψ : MonotoneOn ψ (φ '' t) := Function.monotoneOn_of_rightInvOn_of_mapsTo hφ ψφs ψts
  change eVariationOn (f ∘ id) (φ '' t) <= eVariationOn (f ∘ φ) t
  rw [← eq_of_eqOn (ψφs.comp_left : EqOn (f ∘ φ ∘ ψ) (f ∘ id) (φ '' t))]
  exact comp_le_of_monotoneOn _ ψ hψ ψts

/--
theorem `comp_inter_Icc_eq_of_monotoneOn` / 定理 `comp_inter_Icc_eq_of_monotoneOn`

English:
theorem comp_inter_Icc_eq_of_monotoneOn
  statement: (f : α -> E) {t : Set β} (φ : β -> α) (hφ : MonotoneOn φ t)
  proof: by
  rcases le_total x y with (h | h)
  · convert! comp_eq_of_monotoneOn f φ (hφ.mono Set.inter_subset_left)
    apply le_antisymm
    · rintro _ ⟨⟨u, us, rfl⟩, vφx, vφy⟩
      rcases le_total x u with (xu | ux)
      · rcases le_total u y with (uy | yu)
        · exact ⟨u, ⟨us, ⟨xu, uy⟩⟩, rfl⟩
    

中文:
定理 comp_inter_Icc_eq_of_monotoneOn
  结论: (f : α -> E) {t : 集合 β} (φ : β -> α) (hφ : MonotoneOn φ t)
  证明: by
  rcases le_total x y with (h | h)
  · convert! comp_eq_of_monotoneOn f φ (hφ.mono Set.inter_subset_left)
    apply le_antisymm
    · rintro _ ⟨⟨u, us, rfl⟩, vφx, vφy⟩
      rcases le_total x u with (xu | ux)
      · rcases le_total u y with (uy | yu)
        · exact ⟨u, ⟨us, ⟨xu, uy⟩⟩, rfl⟩
    

Depends on / 依赖: Set.inter_subset_left, comp_eq_of_monotoneOn, convert, inter_subset_left, le_antisymm, le_rfl, le_total
-/
theorem comp_inter_Icc_eq_of_monotoneOn (f : α -> E) {t : Set β} (φ : β -> α) (hφ : MonotoneOn φ t)
    {x y : β} (hx : x in t) (hy : y in t) :
    eVariationOn (f ∘ φ) (t inter Icc x y) = eVariationOn f (φ '' t inter Icc (φ x) (φ y)) := by
  rcases le_total x y with (h | h)
  · convert! comp_eq_of_monotoneOn f φ (hφ.mono Set.inter_subset_left)
    apply le_antisymm
    · rintro _ ⟨⟨u, us, rfl⟩, vφx, vφy⟩
      rcases le_total x u with (xu | ux)
      · rcases le_total u y with (uy | yu)
        · exact ⟨u, ⟨us, ⟨xu, uy⟩⟩, rfl⟩
        · rw [le_antisymm vφy (hφ hy us yu)]
          exact ⟨y, ⟨hy, ⟨h, le_rfl⟩⟩, rfl⟩
      · rw [← le_antisymm vφx (hφ us hx ux)]
        exact ⟨x, ⟨hx, ⟨le_rfl, h⟩⟩, rfl⟩
    · rintro _ ⟨u, ⟨⟨hu, xu, uy⟩, rfl⟩⟩
      exact ⟨⟨u, hu, rfl⟩, ⟨hφ hx hu xu, hφ hu hy uy⟩⟩
  · rw [eVariationOn.subsingleton, eVariationOn.subsingleton]
    exacts [(Set.subsingleton_Icc_of_ge (hφ hy hx h)).anti Set.inter_subset_right,
      (Set.subsingleton_Icc_of_ge h).anti Set.inter_subset_right]

/--
theorem `comp_eq_of_antitoneOn` / 定理 `comp_eq_of_antitoneOn`

English:
theorem comp_eq_of_antitoneOn
  given: (f : α -> E) {t : Set β} (φ : β -> α) (hφ : AntitoneOn φ t)
  proof: by
  apply le_antisymm (comp_le_of_antitoneOn f φ hφ (mapsTo_image φ t))
  cases isEmpty_or_nonempty β
  · simp [Set.eq_empty_of_isEmpty]
  let ψ := φ.invFunOn t
  have ψφs : EqOn (φ ∘ ψ) id (φ '' t) := (surjOn_image φ t).rightInvOn_invFunOn
  have ψts := (surjOn_image φ t).mapsTo_invFunOn
  have hψ

中文:
定理 comp_eq_of_antitoneOn
  条件: (f : α -> E) {t : 集合 β} (φ : β -> α) (hφ : AntitoneOn φ t)
  证明: by
  apply le_antisymm (comp_le_of_antitoneOn f φ hφ (mapsTo_image φ t))
  cases isEmpty_or_nonempty β
  · simp [Set.eq_empty_of_isEmpty]
  let ψ := φ.invFunOn t
  have ψφs : EqOn (φ ∘ ψ) id (φ '' t) := (surjOn_image φ t).rightInvOn_invFunOn
  have ψts := (surjOn_image φ t).mapsTo_invFunOn
  have hψ

Depends on / 依赖: AntitoneOn, Function, Function.antitoneOn_of_rightInvOn_of_mapsTo, Set.eq_empty_of_isEmpty, antitoneOn_of_rightInvOn_of_mapsTo, comp_le_of_antitoneOn, comp_left, eVariationOn, eq_empty_of_isEmpty, eq_of_eqOn, invFunOn, isEmpty_or_nonempty, le_antisymm, mapsTo_image, mapsTo_invFunOn, rightInvOn_invFunOn, s.comp_left, surjOn_image
-/
theorem comp_eq_of_antitoneOn (f : α -> E) {t : Set β} (φ : β -> α) (hφ : AntitoneOn φ t) :
    eVariationOn (f ∘ φ) t = eVariationOn f (φ '' t) := by
  apply le_antisymm (comp_le_of_antitoneOn f φ hφ (mapsTo_image φ t))
  cases isEmpty_or_nonempty β
  · simp [Set.eq_empty_of_isEmpty]
  let ψ := φ.invFunOn t
  have ψφs : EqOn (φ ∘ ψ) id (φ '' t) := (surjOn_image φ t).rightInvOn_invFunOn
  have ψts := (surjOn_image φ t).mapsTo_invFunOn
  have hψ : AntitoneOn ψ (φ '' t) := Function.antitoneOn_of_rightInvOn_of_mapsTo hφ ψφs ψts
  change eVariationOn (f ∘ id) (φ '' t) <= eVariationOn (f ∘ φ) t
  rw [← eq_of_eqOn (ψφs.comp_left : EqOn (f ∘ φ ∘ ψ) (f ∘ id) (φ '' t))]
  exact comp_le_of_antitoneOn _ ψ hψ ψts

open OrderDual

/--
theorem `comp_ofDual` / 定理 `comp_ofDual`

English:
theorem comp_ofDual
  given: (f : α -> E) (s : Set α)
  proof: by
  convert! comp_eq_of_antitoneOn f ofDual fun _ _ _ _ => id
  simp only [Equiv.image_preimage]

中文:
定理 comp_ofDual
  条件: (f : α -> E) (s : 集合 α)
  证明: by
  convert! comp_eq_of_antitoneOn f ofDual fun _ _ _ _ => id
  simp only [Equiv.image_preimage]
-/
@[simp] theorem comp_ofDual (f : α -> E) (s : Set α) :
    eVariationOn (f ∘ ofDual) (ofDual ⁻¹' s) = eVariationOn f s := by
  convert! comp_eq_of_antitoneOn f ofDual fun _ _ _ _ => id
  simp only [Equiv.image_preimage]

/--
lemma `_root_.BoundedVariationOn.ofDual` / 引理 `_root_.BoundedVariationOn.ofDual`

English:
lemma _root_.BoundedVariationOn.ofDual
  proof: by
  simpa [BoundedVariationOn] using hf

中文:
引理 _root_.BoundedVariationOn.ofDual
  证明: by
  simpa [BoundedVariationOn] using hf
-/
protected lemma _root_.BoundedVariationOn.ofDual
    {f : α -> E} {s : Set α} (hf : BoundedVariationOn f s) :
    BoundedVariationOn (f ∘ ofDual) (ofDual ⁻¹' s) := by
  simpa [BoundedVariationOn] using hf

/--
lemma `boundedVariation_ofDual` / 引理 `boundedVariation_ofDual`

English:
lemma boundedVariation_ofDual
  given: {f : α -> E} {s : Set α}
  proof: ⟨fun h => h.ofDual, fun h => h.ofDual⟩

中文:
引理 boundedVariation_ofDual
  条件: {f : α -> E} {s : 集合 α}
  证明: ⟨fun h => h.ofDual, fun h => h.ofDual⟩
-/
@[simp] lemma boundedVariation_ofDual {f : α -> E} {s : Set α} :
    BoundedVariationOn (f ∘ ofDual) (ofDual ⁻¹' s) ↔ BoundedVariationOn f s :=
  ⟨fun h => h.ofDual, fun h => h.ofDual⟩

/--
lemma `_root_.LocallyBoundedVariationOn.ofDual` / 引理 `_root_.LocallyBoundedVariationOn.ofDual`

English:
lemma _root_.LocallyBoundedVariationOn.ofDual
  statement: {f : α -> E} {s : Set α}
  proof: by
  intro x y hx hy
  rw [← toDual_ofDual x]; rw [← toDual_ofDual y]; rw [Icc_toDual]; rw [← preimage_inter]
  apply BoundedVariationOn.ofDual (hf (ofDual y) (ofDual x) hy hx)

中文:
引理 _root_.LocallyBoundedVariationOn.ofDual
  结论: {f : α -> E} {s : 集合 α}
  证明: by
  intro x y hx hy
  rw [← toDual_ofDual x]; rw [← toDual_ofDual y]; rw [Icc_toDual]; rw [← preimage_inter]
  apply BoundedVariationOn.ofDual (hf (ofDual y) (ofDual x) hy hx)
-/
protected lemma _root_.LocallyBoundedVariationOn.ofDual {f : α -> E} {s : Set α}
    (hf : LocallyBoundedVariationOn f s) :
    LocallyBoundedVariationOn (f ∘ ofDual) (ofDual ⁻¹' s) := by
  intro x y hx hy
  rw [← toDual_ofDual x]; rw [← toDual_ofDual y]; rw [Icc_toDual]; rw [← preimage_inter]
  apply BoundedVariationOn.ofDual (hf (ofDual y) (ofDual x) hy hx)

/--
lemma `locallyBoundedVariation_ofDual` / 引理 `locallyBoundedVariation_ofDual`

English:
lemma locallyBoundedVariation_ofDual
  given: {f : α -> E} {s : Set α}
  proof: ⟨fun h => h.ofDual, fun h => h.ofDual⟩

中文:
引理 locallyBoundedVariation_ofDual
  条件: {f : α -> E} {s : 集合 α}
  证明: ⟨fun h => h.ofDual, fun h => h.ofDual⟩
-/
@[simp] lemma locallyBoundedVariation_ofDual {f : α -> E} {s : Set α} :
    LocallyBoundedVariationOn (f ∘ ofDual) (ofDual ⁻¹' s) ↔ LocallyBoundedVariationOn f s :=
  ⟨fun h => h.ofDual, fun h => h.ofDual⟩

end Monotone

/-! ### Left and right limits of bounded variation functions -/

/--
theorem `eVariationOn_on_inter_Iic_eq_Iio_add_edist` / 定理 `eVariationOn_on_inter_Iic_eq_Iio_add_edist`

English:
theorem eVariationOn_on_inter_Iic_eq_Iio_add_edist
  proof: by
  refine le_antisymm ?_ ?_
  · rw [eVariationOn_eq_strictMonoOn]
    apply iSup_le
    rintro ⟨n, u, u_mono, u_mem⟩
    have : u n <= a := (u_mem n (by simp)).2
    rcases this.eq_or_lt with hn | hn; swap
    · exact (sum_le_of_monotoneOn_Iic u_mono.monotoneOn (by grind [StrictMonoOn])).trans le_

中文:
定理 eVariationOn_on_inter_Iic_eq_Iio_add_edist
  证明: by
  refine le_antisymm ?_ ?_
  · rw [eVariationOn_eq_strictMonoOn]
    apply iSup_le
    rintro ⟨n, u, u_mono, u_mem⟩
    have : u n <= a := (u_mem n (by simp)).2
    rcases this.eq_or_lt with hn | hn; swap
    · exact (sum_le_of_monotoneOn_Iic u_mono.monotoneOn (by grind [StrictMonoOn])).trans le_

Depends on / 依赖: StrictMonoOn, Tendsto, Tendsto.edist, eVariationOn, eVariationOn_eq_strictMonoOn, eq_or_lt, iSup_le, le_antisymm, le_self_add, monotoneOn, sum_le_of_monotoneOn_Iic, tendst, this.eq_or_lt, u_mem, u_mono, u_mono.monotoneOn
-/
theorem eVariationOn_on_inter_Iic_eq_Iio_add_edist
    [TopologicalSpace α] [OrderTopology α] {f : α -> E} {s : Set α} {a : α} {l : E}
    (h : (𝓝[s inter Iio a] a).NeBot) (ha : a in s)
    (h'f : Tendsto f (𝓝[s inter Iio a] a) (𝓝 l)) :
    eVariationOn f (s inter Iic a) = eVariationOn f (s inter Iio a) + edist (f a) l := by
  refine le_antisymm ?_ ?_
  · rw [eVariationOn_eq_strictMonoOn]
    apply iSup_le
    rintro ⟨n, u, u_mono, u_mem⟩
    have : u n <= a := (u_mem n (by simp)).2
    rcases this.eq_or_lt with hn | hn; swap
    · exact (sum_le_of_monotoneOn_Iic u_mono.monotoneOn (by grind [StrictMonoOn])).trans le_self_add
    cases n with
    | zero => simp
    | succ n =>
      have : Tendsto (fun y => eVariationOn f (s inter Iio a) + edist (f a) (f y)) (𝓝[s inter Iio a] a)
          (𝓝 (eVariationOn f (s inter Iio a) + edist (f a) l)) :=
        (Tendsto.edist tendsto_const_nhds h'f).const_add _
      apply ge_of_tendsto this
      have : s inter Ioo (u n) a in 𝓝[s inter Iio a] a :=
        inter_mem_nhdsWithin_inter self_mem_nhdsWithin (Ioo_mem_nhdsLT (by grind [StrictMonoOn]))
      filter_upwards [this] with y hy
      let v i := if i <= n then u i else if i = n + 1 then y else a
      have A : ∑ i in Finset.range (n + 1), edist (f (u (i + 1))) (f (u i))
          <= ∑ i in Finset.range (n + 2), edist (f (v (i + 1))) (f (v i)) := by
        simp only [Finset.sum_range_succ, add_assoc]
        gcongr with i h
        · grind
        · grw [add_comm (edist _ _), ← edist_triangle]
          grind
      have B : ∑ i in Finset.range (n + 2), edist (f (v (i + 1))) (f (v i)) <=
            eVariationOn f (s inter Iio a) + edist (f a) (f y) := by
        rw [Finset.sum_range_succ]
        gcongr
        · apply sum_le_of_monotoneOn_Iic <;> grind [MonotoneOn, StrictMonoOn]
        · grind
      exact A.trans B
  · obtain ⟨b, hb⟩ : (s inter Iio a).Nonempty := by contrapose! h; simp [h]
    have : Nonempty ((n : Nat) × { u // StrictMonoOn u (Iic n) ∧ forall i in Iic n, u i in s inter Iio a }) :=
      ⟨0, ⟨fun i => b, by grind [StrictMonoOn]⟩⟩
    rw [eVariationOn_eq_strictMonoOn]; rw [ENNReal.iSup_add]
    apply iSup_le
    rintro ⟨n, u, u_mono, u_mem⟩
    have : Tendsto (fun y => ∑ i in Finset.range n,
        edist (f (u (i + 1))) (f (u i)) + edist (f a) (f y)) (𝓝[s inter Iio a] a)
        (𝓝 (∑ i in Finset.range n, edist (f (u (i + 1))) (f (u i)) + edist (f a) l)) :=
      (Tendsto.edist tendsto_const_nhds h'f).const_add _
    apply le_of_tendsto this
    have : s inter Ioo (u n) a in 𝓝[s inter Iio a] a :=
      inter_mem_nhdsWithin_inter self_mem_nhdsWithin (Ioo_mem_nhdsLT (by grind [StrictMonoOn]))
    filter_upwards [this, self_mem_nhdsWithin] with y hy h'y
    let v i := if i <= n then u i else if i = n + 1 then y else a
    have A : ∑ i in Finset.range n, edist (f (u (i + 1))) (f (u i)) + edist (f a) (f y)
        <= ∑ i in Finset.range (n + 2), edist (f (v (i + 1))) (f (v i)) := by
      simp only [Finset.sum_range_succ, add_assoc]
      gcongr with i h
      · grind
      · exact le_add_left (by grind)
    have B : ∑ i in Finset.range (n + 2), edist (f (v (i + 1))) (f (v i)) <=
        eVariationOn f (s inter Iic a) :=
      sum_le_of_monotoneOn_Iic (by grind [MonotoneOn, StrictMonoOn]) (by grind)
    exact A.trans B

/--
theorem `eVariationOn_on_inter_Ici_eq_Ioi_add_edist` / 定理 `eVariationOn_on_inter_Ici_eq_Ioi_add_edist`

English:
theorem eVariationOn_on_inter_Ici_eq_Ioi_add_edist
  proof: by
  rw [← comp_ofDual f]; rw [← comp_ofDual f]
  exact eVariationOn_on_inter_Iic_eq_Iio_add_edist h ha h'f

中文:
定理 eVariationOn_on_inter_Ici_eq_Ioi_add_edist
  证明: by
  rw [← comp_ofDual f]; rw [← comp_ofDual f]
  exact eVariationOn_on_inter_Iic_eq_Iio_add_edist h ha h'f

Depends on / 依赖: comp_ofDual, eVariationOn_on_inter_Iic_eq_Iio_add_edist
-/
theorem eVariationOn_on_inter_Ici_eq_Ioi_add_edist
    [TopologicalSpace α] [OrderTopology α] {f : α -> E} {s : Set α} {a : α} {l : E}
    (h : (𝓝[s inter Ioi a] a).NeBot) (ha : a in s)
    (h'f : Tendsto f (𝓝[s inter Ioi a] a) (𝓝 l)) :
    eVariationOn f (s inter Ici a) = eVariationOn f (s inter Ioi a) + edist (f a) l := by
  rw [← comp_ofDual f]; rw [← comp_ofDual f]
  exact eVariationOn_on_inter_Iic_eq_Iio_add_edist h ha h'f

/--
lemma `eVariationOn_inter_Iio_eq_inter_Iic_of_continuousWithinAt` / 引理 `eVariationOn_inter_Iio_eq_inter_Iic_of_continuousWithinAt`

English:
lemma eVariationOn_inter_Iio_eq_inter_Iic_of_continuousWithinAt
  proof: by
  by_cases ha : a in s
  · have : Tendsto f (𝓝[s inter Iio a] a) (𝓝 (f a)) := h'.mono (by grind)
    simp [eVariationOn_on_inter_Iic_eq_Iio_add_edist h ha this]
  · congr 1
    grind

中文:
引理 eVariationOn_inter_Iio_eq_inter_Iic_of_continuousWithinAt
  证明: by
  by_cases ha : a in s
  · have : Tendsto f (𝓝[s inter Iio a] a) (𝓝 (f a)) := h'.mono (by grind)
    simp [eVariationOn_on_inter_Iic_eq_Iio_add_edist h ha this]
  · congr 1
    grind

Depends on / 依赖: Tendsto, eVariationOn_on_inter_Iic_eq_Iio_add_edist
-/
lemma eVariationOn_inter_Iio_eq_inter_Iic_of_continuousWithinAt
    [TopologicalSpace α] [OrderTopology α] {f : α -> E} {s : Set α} {a : α}
    (h : (𝓝[s inter Iio a] a).NeBot) (h' : ContinuousWithinAt f (s inter Iic a) a) :
    eVariationOn f (s inter Iio a) = eVariationOn f (s inter Iic a) := by
  by_cases ha : a in s
  · have : Tendsto f (𝓝[s inter Iio a] a) (𝓝 (f a)) := h'.mono (by grind)
    simp [eVariationOn_on_inter_Iic_eq_Iio_add_edist h ha this]
  · congr 1
    grind

/--
lemma `eVariationOn_inter_Ioi_eq_inter_Ici_of_continuousWithinAt` / 引理 `eVariationOn_inter_Ioi_eq_inter_Ici_of_continuousWithinAt`

English:
lemma eVariationOn_inter_Ioi_eq_inter_Ici_of_continuousWithinAt
  proof: by
  rw [← comp_ofDual f]; rw [← comp_ofDual f]
  exact eVariationOn_inter_Iio_eq_inter_Iic_of_continuousWithinAt h h'

中文:
引理 eVariationOn_inter_Ioi_eq_inter_Ici_of_continuousWithinAt
  证明: by
  rw [← comp_ofDual f]; rw [← comp_ofDual f]
  exact eVariationOn_inter_Iio_eq_inter_Iic_of_continuousWithinAt h h'

Depends on / 依赖: comp_ofDual, eVariationOn_inter_Iio_eq_inter_Iic_of_continuousWithinAt
-/
lemma eVariationOn_inter_Ioi_eq_inter_Ici_of_continuousWithinAt
    [TopologicalSpace α] [OrderTopology α] {f : α -> E} {s : Set α} {a : α}
    (h : (𝓝[s inter Ioi a] a).NeBot) (h' : ContinuousWithinAt f (s inter Ici a) a) :
    eVariationOn f (s inter Ioi a) = eVariationOn f (s inter Ici a) := by
  rw [← comp_ofDual f]; rw [← comp_ofDual f]
  exact eVariationOn_inter_Iio_eq_inter_Iic_of_continuousWithinAt h h'

/--
lemma `eVariationOn_Ioc_eq_Icc_of_continuousWithinAt'` / 引理 `eVariationOn_Ioc_eq_Icc_of_continuousWithinAt'`

English:
lemma eVariationOn_Ioc_eq_Icc_of_continuousWithinAt'
  proof: by
  rcases le_or_gt b a with hab | hab
  · simp [hab]
  have : (𝓝[Iic b inter Ioi a] a).NeBot := by
    convert h using 1
    exact nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds hab))
  convert eVariationOn_inter_Ioi_eq_inter_Ici_of_continuousWithinAt this
    (h'.mono inter_sub

中文:
引理 eVariationOn_Ioc_eq_Icc_of_continuousWithinAt'
  证明: by
  rcases le_or_gt b a with hab | hab
  · simp [hab]
  have : (𝓝[Iic b inter Ioi a] a).NeBot := by
    convert h using 1
    exact nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds hab))
  convert eVariationOn_inter_Ioi_eq_inter_Ici_of_continuousWithinAt this
    (h'.mono inter_sub

Depends on / 依赖: Iic_mem_nhds, convert, eVariationOn_inter_Ioi_eq_inter_Ici_of_continuousWithinAt, inter_subset_right, le_or_gt, mem_nhdsWithin_of_mem_nhds, nhdsWithin_inter_of_mem
-/
lemma eVariationOn_Ioc_eq_Icc_of_continuousWithinAt'
    [TopologicalSpace α] [OrderTopology α] {f : α -> E} {a b : α}
    [h : (𝓝[>] a).NeBot] (h' : ContinuousWithinAt f (Ici a) a) :
    eVariationOn f (Ioc a b) = eVariationOn f (Icc a b) := by
  rcases le_or_gt b a with hab | hab
  · simp [hab]
  have : (𝓝[Iic b inter Ioi a] a).NeBot := by
    convert h using 1
    exact nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds hab))
  convert eVariationOn_inter_Ioi_eq_inter_Ici_of_continuousWithinAt this
    (h'.mono inter_subset_right) <;> grind

/--
lemma `eVariationOn_Ioc_eq_Icc_of_continuousWithinAt` / 引理 `eVariationOn_Ioc_eq_Icc_of_continuousWithinAt`

English:
lemma eVariationOn_Ioc_eq_Icc_of_continuousWithinAt
  proof: by
  rcases le_or_gt b a with hab | hab
  · simp [hab]
  have : (𝓝[Ioi a] a).NeBot := nhdsGT_neBot_of_exists_gt ⟨b, hab⟩
  exact eVariationOn_Ioc_eq_Icc_of_continuousWithinAt' h'

中文:
引理 eVariationOn_Ioc_eq_Icc_of_continuousWithinAt
  证明: by
  rcases le_or_gt b a with hab | hab
  · simp [hab]
  have : (𝓝[Ioi a] a).NeBot := nhdsGT_neBot_of_exists_gt ⟨b, hab⟩
  exact eVariationOn_Ioc_eq_Icc_of_continuousWithinAt' h'

Depends on / 依赖: eVariationOn_Ioc_eq_Icc_of_continuousWithinAt, le_or_gt, nhdsGT_neBot_of_exists_gt
-/
lemma eVariationOn_Ioc_eq_Icc_of_continuousWithinAt
    [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α] {f : α -> E} {a b : α}
    (h' : ContinuousWithinAt f (Ici a) a) :
    eVariationOn f (Ioc a b) = eVariationOn f (Icc a b) := by
  rcases le_or_gt b a with hab | hab
  · simp [hab]
  have : (𝓝[Ioi a] a).NeBot := nhdsGT_neBot_of_exists_gt ⟨b, hab⟩
  exact eVariationOn_Ioc_eq_Icc_of_continuousWithinAt' h'

/--
lemma `eVariationOn_Ico_eq_Icc_of_continuousWithinAt'` / 引理 `eVariationOn_Ico_eq_Icc_of_continuousWithinAt'`

English:
lemma eVariationOn_Ico_eq_Icc_of_continuousWithinAt'
  proof: by
  rw [← comp_ofDual f]; rw [← comp_ofDual f]; rw [← Ioc_toDual]; rw [← Icc_toDual]
  exact eVariationOn_Ioc_eq_Icc_of_continuousWithinAt' h'

中文:
引理 eVariationOn_Ico_eq_Icc_of_continuousWithinAt'
  证明: by
  rw [← comp_ofDual f]; rw [← comp_ofDual f]; rw [← Ioc_toDual]; rw [← Icc_toDual]
  exact eVariationOn_Ioc_eq_Icc_of_continuousWithinAt' h'

Depends on / 依赖: Icc_toDual, Ioc_toDual, comp_ofDual, eVariationOn_Ioc_eq_Icc_of_continuousWithinAt
-/
lemma eVariationOn_Ico_eq_Icc_of_continuousWithinAt'
    [TopologicalSpace α] [OrderTopology α] {f : α -> E} {a b : α}
    [h : (𝓝[<] a).NeBot] (h' : ContinuousWithinAt f (Iic a) a) :
    eVariationOn f (Ico b a) = eVariationOn f (Icc b a) := by
  rw [← comp_ofDual f]; rw [← comp_ofDual f]; rw [← Ioc_toDual]; rw [← Icc_toDual]
  exact eVariationOn_Ioc_eq_Icc_of_continuousWithinAt' h'

/--
lemma `eVariationOn_Ico_eq_Icc_of_continuousWithinAt` / 引理 `eVariationOn_Ico_eq_Icc_of_continuousWithinAt`

English:
lemma eVariationOn_Ico_eq_Icc_of_continuousWithinAt
  proof: by
  rw [← comp_ofDual f]; rw [← comp_ofDual f]; rw [← Ioc_toDual]; rw [← Icc_toDual]
  exact eVariationOn_Ioc_eq_Icc_of_continuousWithinAt h'

中文:
引理 eVariationOn_Ico_eq_Icc_of_continuousWithinAt
  证明: by
  rw [← comp_ofDual f]; rw [← comp_ofDual f]; rw [← Ioc_toDual]; rw [← Icc_toDual]
  exact eVariationOn_Ioc_eq_Icc_of_continuousWithinAt h'

Depends on / 依赖: Icc_toDual, Ioc_toDual, comp_ofDual, eVariationOn_Ioc_eq_Icc_of_continuousWithinAt
-/
lemma eVariationOn_Ico_eq_Icc_of_continuousWithinAt
    [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α] {f : α -> E} {a b : α}
    (h' : ContinuousWithinAt f (Iic a) a) :
    eVariationOn f (Ico b a) = eVariationOn f (Icc b a) := by
  rw [← comp_ofDual f]; rw [← comp_ofDual f]; rw [← Ioc_toDual]; rw [← Icc_toDual]
  exact eVariationOn_Ioc_eq_Icc_of_continuousWithinAt h'

/--
lemma `exists_lt_eVariationOn_inter_Icc` / 引理 `exists_lt_eVariationOn_inter_Icc`

English:
lemma exists_lt_eVariationOn_inter_Icc
  statement: {f : α -> E} {ε : Real>=0∞} {s : Set α}
  proof: by
  obtain ⟨n, u, ⟨u_mono, u_mem⟩, hu⟩ : exists n u, (Monotone u ∧ forall (i : Nat), u i in s) ∧
      ε < ∑ x in Finset.range n, edist (f (u (x + 1))) (f (u x)) := by
    simpa [eVariationOn, lt_iSup_iff] using h
  have A : ε < eVariationOn f (s inter Icc (u 0) (u n)) := by
    apply hu.trans_le
 

中文:
引理 存在_lt_eVariationOn_inter_Icc
  结论: {f : α -> E} {ε : 实数>=0∞} {s : 集合 α}
  证明: by
  obtain ⟨n, u, ⟨u_mono, u_mem⟩, hu⟩ : exists n u, (Monotone u ∧ forall (i : Nat), u i in s) ∧
      ε < ∑ x in Finset.range n, edist (f (u (x + 1))) (f (u x)) := by
    simpa [eVariationOn, lt_iSup_iff] using h
  have A : ε < eVariationOn f (s inter Icc (u 0) (u n)) := by
    apply hu.trans_le
 

Depends on / 依赖: Finset, Finset.range, Finset.sum_congr, Monotone, eVariationOn, hu.trans_le, lt_iSup_iff, sum_congr, trans_le, u_mem, u_mono
-/
lemma exists_lt_eVariationOn_inter_Icc {f : α -> E} {ε : Real>=0∞} {s : Set α}
    (h : ε < eVariationOn f s) : exists a in s, exists b in s, a < b ∧ ε < eVariationOn f (s inter Icc a b) := by
  obtain ⟨n, u, ⟨u_mono, u_mem⟩, hu⟩ : exists n u, (Monotone u ∧ forall (i : Nat), u i in s) ∧
      ε < ∑ x in Finset.range n, edist (f (u (x + 1))) (f (u x)) := by
    simpa [eVariationOn, lt_iSup_iff] using h
  have A : ε < eVariationOn f (s inter Icc (u 0) (u n)) := by
    apply hu.trans_le
    simp only [Monotone] at u_mono
    let v (i : Nat) := min (u i) (u n)
    calc ∑ x in Finset.range n, edist (f (u (x + 1))) (f (u x))
    _ = ∑ i in Finset.range n, edist (f (v (i + 1))) (f (v i)) := by grind [Finset.sum_congr]
    _ <= eVariationOn f (s inter Icc (u 0) (u n)) :=
      sum_le_of_monotoneOn_Iic (by grind [MonotoneOn]) (by grind)
  refine ⟨u 0, u_mem _, u n, u_mem _, ?_, A⟩
  by_contra!
  have : Set.Subsingleton (s inter Icc (u 0) (u n)) := by
    intro a ha b hb
    simp only [mem_inter_iff, mem_Icc] at ha hb
    order
  simp [this] at A

/--
theorem `_root_.BoundedVariationOn.tendsto_eVariationOn_Ici_zero_of_filter` / 定理 `_root_.BoundedVariationOn.tendsto_eVariationOn_Ici_zero_of_filter`

English:
theorem _root_.BoundedVariationOn.tendsto_eVariationOn_Ici_zero_of_filter
  proof: by
  rcases eq_empty_or_nonempty s with rfl | ⟨x₀, hx₀⟩
  · simpa using tendsto_const_nhds
  /- The variation is monotone, therefore it converges. If the limit were positive, say `ε`,
  then one would get variation `ε` between two points `x₀` and `x₁`. But also between two points
  `x₁` and `x₂`, an

中文:
定理 _root_.BoundedVariationOn.tendsto_eVariationOn_Ici_zero_of_filter
  证明: by
  rcases eq_empty_or_nonempty s with rfl | ⟨x₀, hx₀⟩
  · simpa using tendsto_const_nhds
  /- The variation is monotone, therefore it converges. If the limit were positive, say `ε`,
  then one would get variation `ε` between two points `x₀` and `x₁`. But also between two points
  `x₁` and `x₂`, an

Depends on / 依赖: eq_empty_or_nonempty, tendsto_const_nhds
-/
theorem _root_.BoundedVariationOn.tendsto_eVariationOn_Ici_zero_of_filter
    {f : α -> E} {s : Set α} (hf : BoundedVariationOn f s)
    (L : Filter α) (hL : forall y in s, s inter Ici y in L) :
    Tendsto (fun y => eVariationOn f (s inter Ici y)) L (𝓝 0) := by
  rcases eq_empty_or_nonempty s with rfl | ⟨x₀, hx₀⟩
  · simpa using tendsto_const_nhds
  /- The variation is monotone, therefore it converges. If the limit were positive, say `ε`,
  then one would get variation `ε` between two points `x₀` and `x₁`. But also between two points
  `x₁` and `x₂`, and so on. Adding up these variations would be arbitrarily large, contradicting
  the finite variation of the function. -/
  apply tendsto_order.2 ⟨by simp, fun ε εpos => ?_⟩
  obtain ⟨δ, δpos, hδ⟩ : exists δ, δ in Ioo 0 ε := exists_between εpos
  by_contra! H
  have B (y) (hy : y in s) : exists y' in s inter Ici y, δ <= eVariationOn f (s inter Icc y y') := by
    obtain ⟨y', hy', y'_mem⟩ : exists y', ε <= eVariationOn f (s inter Ici y') ∧ y' in s inter Ici y :=
      (H.and_eventually (hL y hy)).exists
    obtain ⟨a, ha, b, hb, hab, h⟩ : exists a in s inter Ici y', exists b in s inter Ici y', a < b ∧
      δ < eVariationOn f ((s inter Ici y') inter Icc a b) :=
        exists_lt_eVariationOn_inter_Icc (hδ.trans_le hy')
    refine ⟨b, ⟨hb.1, le_trans y'_mem.2 hb.2⟩, ?_⟩
    have : Ici y' inter Icc a b = Icc a b := by grind
    rw [inter_assoc]; rw [this] at h
    exact h.le.trans (mono _ (by grind))
  choose! y y_mem le_y using B
  let v (n : Nat) := y^[n] x₀
  have I n : v n in s := by
    induction n with
    | zero => simpa [v] using hx₀
    | succ n ih =>
      simp only [Function.iterate_succ', Function.comp_apply, v]
      exact (y_mem _ ih).1
  have J (n : Nat) : n * δ <= eVariationOn f s := calc
    n * δ
    _ = ∑ i in Finset.range n, δ := by simp
    _ <= ∑ i in Finset.range n, eVariationOn f (s inter Icc (v i) (v (i + 1))) := by
      gcongr with i hi
      simp only [Function.iterate_succ', Function.comp_apply, v]
      grind
    _ = eVariationOn f (s inter Icc (v 0) (v n)) := by
      apply eVariationOn.sum
      · apply monotone_nat_of_le_succ (fun n => ?_)
        simp only [Function.iterate_succ', Function.comp_apply, v]
        exact (y_mem _ (I n)).2
      · grind
    _ <= eVariationOn f s := mono _ inter_subset_left
  have : Tendsto (fun (n : Nat) => n * δ) atTop (𝓝 (∞ * δ)) :=
    ENNReal.Tendsto.mul_const ENNReal.tendsto_nat_nhds_top (by simp)
  rw [ENNReal.top_mul δpos.ne'] at this
  have : ∞ <= eVariationOn f s := le_of_tendsto this (Eventually.of_forall J)
  simp only [BoundedVariationOn] at hf
  order

/--
theorem `_root_.BoundedVariationOn.exists_tendsto_left_of_filter` / 定理 `_root_.BoundedVariationOn.exists_tendsto_left_of_filter`

English:
theorem _root_.BoundedVariationOn.exists_tendsto_left_of_filter
  statement: [CompleteSpace E]
  proof: by
  rcases hs with ⟨x₀, hx₀⟩
  rcases Filter.eq_or_neBot L with h | h
  · simp only [h, tendsto_bot, exists_const_iff, and_true]
    exact ⟨f x₀⟩
  apply CompleteSpace.complete
  apply EMetric.cauchy_iff.2 ⟨by simp [neBot_iff.mp h], fun ε εpos => ?_⟩
  obtain ⟨y, y_mem, hy⟩ : exists y in s, eVariat

中文:
定理 _root_.BoundedVariationOn.存在_tendsto_left_of_filter
  结论: [完备空间 E]
  证明: by
  rcases hs with ⟨x₀, hx₀⟩
  rcases Filter.eq_or_neBot L with h | h
  · simp only [h, tendsto_bot, exists_const_iff, and_true]
    exact ⟨f x₀⟩
  apply CompleteSpace.complete
  apply EMetric.cauchy_iff.2 ⟨by simp [neBot_iff.mp h], fun ε εpos => ?_⟩
  obtain ⟨y, y_mem, hy⟩ : exists y in s, eVariat

Depends on / 依赖: CompleteSpace, CompleteSpace.complete, EMetric, EMetric.cauchy_iff, Filter, Filter.eq_or_neBot, and_true, cauchy_iff, complete, eVariationOn, eq_or_neBot, exists_const_iff, hf.tendsto_eVariationOn_Ici_zero_of_filter, neBot_iff, neBot_iff.mp, tendsto_bot, tendsto_eVariationOn_Ici_zero_of_filter, tendsto_order, y_mem
-/
theorem _root_.BoundedVariationOn.exists_tendsto_left_of_filter [CompleteSpace E]
    {f : α -> E} {s : Set α} (hf : BoundedVariationOn f s)
    (L : Filter α) (hL : forall y in s, s inter Ici y in L) (hs : s.Nonempty) :
    exists l, Tendsto f L (𝓝 l) := by
  rcases hs with ⟨x₀, hx₀⟩
  rcases Filter.eq_or_neBot L with h | h
  · simp only [h, tendsto_bot, exists_const_iff, and_true]
    exact ⟨f x₀⟩
  apply CompleteSpace.complete
  apply EMetric.cauchy_iff.2 ⟨by simp [neBot_iff.mp h], fun ε εpos => ?_⟩
  obtain ⟨y, y_mem, hy⟩ : exists y in s, eVariationOn f (s inter Ici y) < ε := by
    have W := hf.tendsto_eVariationOn_Ici_zero_of_filter L hL
    rcases (((tendsto_order.1 W).2 ε εpos).and (hL x₀ hx₀)).exists with ⟨y, hy, h'y⟩
    exact ⟨y, h'y.1, hy⟩
  refine ⟨f '' (s inter Ici y), ?_, ?_⟩
  · simp only [mem_map]
    apply mem_of_superset (hL y y_mem) (subset_preimage_image _ _)
  · rintro - ⟨a, ha, rfl⟩ - ⟨b, hb, rfl⟩
    exact (eVariationOn.edist_le _ ha hb).trans_lt hy

/--
theorem `_root_.BoundedVariationOn.tendsto_eVariationOn_Ico_zero` / 定理 `_root_.BoundedVariationOn.tendsto_eVariationOn_Ico_zero`

English:
theorem _root_.BoundedVariationOn.tendsto_eVariationOn_Ico_zero
  proof: by
  have A : Tendsto (fun y => eVariationOn f (s inter Ico y x)) (𝓝[s inter Iio x] x) (𝓝 0) := by
    simp_rw [← Iio_inter_Ici, ← inter_assoc]
    exact (hf.mono inter_subset_left).tendsto_eVariationOn_Ici_zero_of_filter (𝓝[s inter Iio x] x)
      (fun y hy => inter_mem_nhdsWithin _ (Ici_mem_nhds h

中文:
定理 _root_.BoundedVariationOn.tendsto_eVariationOn_Ico_zero
  证明: by
  have A : Tendsto (fun y => eVariationOn f (s inter Ico y x)) (𝓝[s inter Iio x] x) (𝓝 0) := by
    simp_rw [← Iio_inter_Ici, ← inter_assoc]
    exact (hf.mono inter_subset_left).tendsto_eVariationOn_Ici_zero_of_filter (𝓝[s inter Iio x] x)
      (fun y hy => inter_mem_nhdsWithin _ (Ici_mem_nhds h

Depends on / 依赖: Ici_mem_nhds, Iio_inter_Ici, Tendsto, eVariationOn, filter_upwards, hf.mono, inter_assoc, inter_mem_nhdsWithin, inter_subset_left, self_mem_nhdsWithin, simp_rw, tendsto_const_nhds, tendsto_const_nhds.congr, tendsto_eVariationOn_Ici_zero_of_filter
-/
theorem _root_.BoundedVariationOn.tendsto_eVariationOn_Ico_zero
    [TopologicalSpace α] [OrderTopology α]
    {f : α -> E} {s : Set α} (hf : BoundedVariationOn f s) (x : α) :
    Tendsto (fun y => eVariationOn f (s inter Ico y x)) (𝓝[s] x) (𝓝 0) := by
  have A : Tendsto (fun y => eVariationOn f (s inter Ico y x)) (𝓝[s inter Iio x] x) (𝓝 0) := by
    simp_rw [← Iio_inter_Ici, ← inter_assoc]
    exact (hf.mono inter_subset_left).tendsto_eVariationOn_Ici_zero_of_filter (𝓝[s inter Iio x] x)
      (fun y hy => inter_mem_nhdsWithin _ (Ici_mem_nhds hy.2))
  have B : Tendsto (fun y => eVariationOn f (s inter Ico y x)) (𝓝[s inter Ici x] x) (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with a ha using by simp [show Ico a x = ∅ by grind]
  nth_rewrite 2 [show s = (s inter Iio x) union (s inter Ici x) by grind]
  rw [nhdsWithin_union]; rw [tendsto_sup]
  simp [A, B]

/--
theorem `_root_.BoundedVariationOn.tendsto_eVariationOn_Ioc_zero` / 定理 `_root_.BoundedVariationOn.tendsto_eVariationOn_Ioc_zero`

English:
theorem _root_.BoundedVariationOn.tendsto_eVariationOn_Ioc_zero
  statement: [TopologicalSpace α]
  proof: by
  have : (fun y => eVariationOn f (s inter Ioc x y)) =
      (fun y => eVariationOn (f ∘ ofDual) (ofDual ⁻¹' s inter Ico (toDual y) (toDual x))) := by
    ext y
    rw [Ico_toDual]; rw [← preimage_inter]; rw [comp_ofDual]
  rw [this]
  exact hf.ofDual.tendsto_eVariationOn_Ico_zero (toDual x)

中文:
定理 _root_.BoundedVariationOn.tendsto_eVariationOn_Ioc_zero
  结论: [拓扑空间 α]
  证明: by
  have : (fun y => eVariationOn f (s inter Ioc x y)) =
      (fun y => eVariationOn (f ∘ ofDual) (ofDual ⁻¹' s inter Ico (toDual y) (toDual x))) := by
    ext y
    rw [Ico_toDual]; rw [← preimage_inter]; rw [comp_ofDual]
  rw [this]
  exact hf.ofDual.tendsto_eVariationOn_Ico_zero (toDual x)

Depends on / 依赖: Ico_toDual, comp_ofDual, eVariationOn, hf.ofDual.tendsto_eVariationOn_Ico_zero, ofDual, preimage_inter, tendsto_eVariationOn_Ico_zero, toDual
-/
theorem _root_.BoundedVariationOn.tendsto_eVariationOn_Ioc_zero [TopologicalSpace α]
    [OrderTopology α] {f : α -> E} {s : Set α} (hf : BoundedVariationOn f s) (x : α) :
    Tendsto (fun y => eVariationOn f (s inter Ioc x y)) (𝓝[s] x) (𝓝 0) := by
  have : (fun y => eVariationOn f (s inter Ioc x y)) =
      (fun y => eVariationOn (f ∘ ofDual) (ofDual ⁻¹' s inter Ico (toDual y) (toDual x))) := by
    ext y
    rw [Ico_toDual]; rw [← preimage_inter]; rw [comp_ofDual]
  rw [this]
  exact hf.ofDual.tendsto_eVariationOn_Ico_zero (toDual x)

/--
theorem `_root_.BoundedVariationOn.exists_tendsto_left` / 定理 `_root_.BoundedVariationOn.exists_tendsto_left`

English:
theorem _root_.BoundedVariationOn.exists_tendsto_left
  statement: [CompleteSpace E] [TopologicalSpace α]
  proof: by
  rcases eq_empty_or_nonempty (s inter Iio x) with hs | hs
  · simp only [hs, nhdsWithin_empty, tendsto_bot, exists_const_iff, and_true]
    exact ⟨f x⟩
  exact BoundedVariationOn.exists_tendsto_left_of_filter (s := s inter Iio x)
    (hf.mono inter_subset_left) _ (fun y hy => inter_mem_nhdsWithi

中文:
定理 _root_.BoundedVariationOn.存在_tendsto_left
  结论: [完备空间 E] [拓扑空间 α]
  证明: by
  rcases eq_empty_or_nonempty (s inter Iio x) with hs | hs
  · simp only [hs, nhdsWithin_empty, tendsto_bot, exists_const_iff, and_true]
    exact ⟨f x⟩
  exact BoundedVariationOn.exists_tendsto_left_of_filter (s := s inter Iio x)
    (hf.mono inter_subset_left) _ (fun y hy => inter_mem_nhdsWithi

Depends on / 依赖: BoundedVariationOn, BoundedVariationOn.exists_tendsto_left_of_filter, Ici_mem_nhds, and_true, eq_empty_or_nonempty, exists_const_iff, exists_tendsto_left_of_filter, hf.mono, inter_mem_nhdsWithin, inter_subset_left, nhdsWithin_empty, tendsto_bot
-/
theorem _root_.BoundedVariationOn.exists_tendsto_left [CompleteSpace E] [TopologicalSpace α]
    [OrderTopology α] {f : α -> E} {s : Set α} (hf : BoundedVariationOn f s) (x : α) :
    exists l, Tendsto f (𝓝[s inter Iio x] x) (𝓝 l) := by
  rcases eq_empty_or_nonempty (s inter Iio x) with hs | hs
  · simp only [hs, nhdsWithin_empty, tendsto_bot, exists_const_iff, and_true]
    exact ⟨f x⟩
  exact BoundedVariationOn.exists_tendsto_left_of_filter (s := s inter Iio x)
    (hf.mono inter_subset_left) _ (fun y hy => inter_mem_nhdsWithin _ (Ici_mem_nhds hy.2)) hs

/--
theorem `_root_.BoundedVariationOn.exists_tendsto_right` / 定理 `_root_.BoundedVariationOn.exists_tendsto_right`

English:
theorem _root_.BoundedVariationOn.exists_tendsto_right
  statement: [CompleteSpace E] [TopologicalSpace α]
  proof: hf.ofDual.exists_tendsto_left (toDual x)

中文:
定理 _root_.BoundedVariationOn.存在_tendsto_right
  结论: [完备空间 E] [拓扑空间 α]
  证明: hf.ofDual.exists_tendsto_left (toDual x)

Depends on / 依赖: exists_tendsto_left, hf.ofDual.exists_tendsto_left, ofDual, toDual
-/
theorem _root_.BoundedVariationOn.exists_tendsto_right [CompleteSpace E] [TopologicalSpace α]
    [OrderTopology α] {f : α -> E} {s : Set α} (hf : BoundedVariationOn f s) (x : α) :
    exists l, Tendsto f (𝓝[s inter Ioi x] x) (𝓝 l) :=
  hf.ofDual.exists_tendsto_left (toDual x)

/--
theorem `_root_.BoundedVariationOn.tendsto_leftLim` / 定理 `_root_.BoundedVariationOn.tendsto_leftLim`

English:
theorem _root_.BoundedVariationOn.tendsto_leftLim
  statement: [CompleteSpace E] [TopologicalSpace α]
  proof: by
  apply tendsto_leftLim_of_tendsto
  convert! hf.exists_tendsto_left x
  simp

中文:
定理 _root_.BoundedVariationOn.tendsto_leftLim
  结论: [完备空间 E] [拓扑空间 α]
  证明: by
  apply tendsto_leftLim_of_tendsto
  convert! hf.exists_tendsto_left x
  simp

Depends on / 依赖: convert, exists_tendsto_left, hf.exists_tendsto_left, tendsto_leftLim_of_tendsto
-/
theorem _root_.BoundedVariationOn.tendsto_leftLim [CompleteSpace E] [TopologicalSpace α]
    [OrderTopology α] {f : α -> E} (hf : BoundedVariationOn f univ) (x : α) :
    Tendsto f (𝓝[<] x) (𝓝 (f.leftLim x)) := by
  apply tendsto_leftLim_of_tendsto
  convert! hf.exists_tendsto_left x
  simp

/--
theorem `_root_.BoundedVariationOn.tendsto_rightLim` / 定理 `_root_.BoundedVariationOn.tendsto_rightLim`

English:
theorem _root_.BoundedVariationOn.tendsto_rightLim
  statement: [CompleteSpace E] [TopologicalSpace α]
  proof: hf.ofDual.tendsto_leftLim x

中文:
定理 _root_.BoundedVariationOn.tendsto_rightLim
  结论: [完备空间 E] [拓扑空间 α]
  证明: hf.ofDual.tendsto_leftLim x

Depends on / 依赖: hf.ofDual.tendsto_leftLim, ofDual, tendsto_leftLim
-/
theorem _root_.BoundedVariationOn.tendsto_rightLim [CompleteSpace E] [TopologicalSpace α]
    [OrderTopology α] {f : α -> E} (hf : BoundedVariationOn f univ) (x : α) :
    Tendsto f (𝓝[>] x) (𝓝 (f.rightLim x)) :=
  hf.ofDual.tendsto_leftLim x

/--
theorem `_root_.BoundedVariationOn.eVariationOn_Iic_eq_Iio_add_edist` / 定理 `_root_.BoundedVariationOn.eVariationOn_Iic_eq_Iio_add_edist`

English:
theorem _root_.BoundedVariationOn.eVariationOn_Iic_eq_Iio_add_edist
  statement: [CompleteSpace E]
  proof: by
  let : TopologicalSpace α := Preorder.topology α
  have : OrderTopology α := ⟨rfl⟩
  by_cases ha : IsBot a
  · have A : Iic a = {a} := by ext x; grind [ha x]
    have B : Iio a = ∅ := by simp [ha.isMin]
    simp [A, B, leftLim_eq_of_isBot ha]
  have : (𝓝[<] a).NeBot := nhdsLT_neBot_of_exists_lt 

中文:
定理 _root_.BoundedVariationOn.eVariationOn_Iic_eq_Iio_add_edist
  结论: [完备空间 E]
  证明: by
  let : TopologicalSpace α := Preorder.topology α
  have : OrderTopology α := ⟨rfl⟩
  by_cases ha : IsBot a
  · have A : Iic a = {a} := by ext x; grind [ha x]
    have B : Iio a = ∅ := by simp [ha.isMin]
    simp [A, B, leftLim_eq_of_isBot ha]
  have : (𝓝[<] a).NeBot := nhdsLT_neBot_of_exists_lt 

Depends on / 依赖: OrderTopology, Preorder, Preorder.topology, TopologicalSpace, eVariationOn, eVariationOn_on_inter_Iic_eq_Iio_add_edist, f.leftLim, ha.isMin, leftLim, leftLim_eq_of_isBot, mem_univ, nhdsLT_neBot_of_exists_lt, topology
-/
theorem _root_.BoundedVariationOn.eVariationOn_Iic_eq_Iio_add_edist [CompleteSpace E]
    [DenselyOrdered α] {f : α -> E} {a : α} (hf : BoundedVariationOn f univ) :
    eVariationOn f (Iic a) = eVariationOn f (Iio a) + edist (f a) (f.leftLim a) := by
  let : TopologicalSpace α := Preorder.topology α
  have : OrderTopology α := ⟨rfl⟩
  by_cases ha : IsBot a
  · have A : Iic a = {a} := by ext x; grind [ha x]
    have B : Iio a = ∅ := by simp [ha.isMin]
    simp [A, B, leftLim_eq_of_isBot ha]
  have : (𝓝[<] a).NeBot := nhdsLT_neBot_of_exists_lt (by simpa [IsBot] using ha)
  have : eVariationOn f (univ inter Iic a) = eVariationOn f (univ inter Iio a)
      + edist (f a) (f.leftLim a) := by
    apply eVariationOn_on_inter_Iic_eq_Iio_add_edist (by simpa) (mem_univ _)
    simpa only [univ_inter] using hf.tendsto_leftLim _
  simpa using this

/--
theorem `_root_.BoundedVariationOn.eVariationOn_Ici_eq_Ioi_add_edist` / 定理 `_root_.BoundedVariationOn.eVariationOn_Ici_eq_Ioi_add_edist`

English:
theorem _root_.BoundedVariationOn.eVariationOn_Ici_eq_Ioi_add_edist
  statement: [CompleteSpace E]
  proof: by
  rw [← eVariationOn.comp_ofDual f]; rw [← eVariationOn.comp_ofDual f]
  exact hf.ofDual.eVariationOn_Iic_eq_Iio_add_edist (a := toDual a)

中文:
定理 _root_.BoundedVariationOn.eVariationOn_Ici_eq_Ioi_add_edist
  结论: [完备空间 E]
  证明: by
  rw [← eVariationOn.comp_ofDual f]; rw [← eVariationOn.comp_ofDual f]
  exact hf.ofDual.eVariationOn_Iic_eq_Iio_add_edist (a := toDual a)

Depends on / 依赖: comp_ofDual, eVariationOn, eVariationOn.comp_ofDual, eVariationOn_Iic_eq_Iio_add_edist, hf.ofDual.eVariationOn_Iic_eq_Iio_add_edist, ofDual, toDual
-/
theorem _root_.BoundedVariationOn.eVariationOn_Ici_eq_Ioi_add_edist [CompleteSpace E]
    [DenselyOrdered α] {f : α -> E} {a : α} (hf : BoundedVariationOn f univ) :
    eVariationOn f (Ici a) = eVariationOn f (Ioi a) + edist (f a) (f.rightLim a) := by
  rw [← eVariationOn.comp_ofDual f]; rw [← eVariationOn.comp_ofDual f]
  exact hf.ofDual.eVariationOn_Iic_eq_Iio_add_edist (a := toDual a)

/--
theorem `_root_.BoundedVariationOn.tendsto_eVariationOn_Icc_left` / 定理 `_root_.BoundedVariationOn.tendsto_eVariationOn_Icc_left`

English:
theorem _root_.BoundedVariationOn.tendsto_eVariationOn_Icc_left
  proof: by
  rcases eq_or_neBot (𝓝[s inter Iio x] x) with h | h
  · simp [h]
  suffices H : Tendsto (fun y => eVariationOn f (s inter Ico y x) + edist (f x) l)
      (𝓝[s inter Iio x] x) (𝓝 (0 + edist (f x) l)) by
    simp only [zero_add] at H
    apply Tendsto.congr' _ H
    filter_upwards [self_mem_nhdsWi

中文:
定理 _root_.BoundedVariationOn.tendsto_eVariationOn_Icc_left
  证明: by
  rcases eq_or_neBot (𝓝[s inter Iio x] x) with h | h
  · simp [h]
  suffices H : Tendsto (fun y => eVariationOn f (s inter Ico y x) + edist (f x) l)
      (𝓝[s inter Iio x] x) (𝓝 (0 + edist (f x) l)) by
    simp only [zero_add] at H
    apply Tendsto.congr' _ H
    filter_upwards [self_mem_nhdsWi

Depends on / 依赖: Tendsto, Tendsto.congr, eVariationOn, eq_or_neBot, filter_upwards, mem_nhdsWithin_of_mem_nhds, nhdsWithin_inter_of_mem, self_mem_nhdsWithin, zero_add
-/
theorem _root_.BoundedVariationOn.tendsto_eVariationOn_Icc_left
    [TopologicalSpace α] [OrderTopology α] {f : α -> E} {s : Set α} {l : E}
    (hf : BoundedVariationOn f s) {x : α} (h'f : Tendsto f (𝓝[s inter Iio x] x) (𝓝 l)) (hx : x in s) :
    Tendsto (fun y => eVariationOn f (s inter Icc y x)) (𝓝[s inter Iio x] x) (𝓝 (edist (f x) l)) := by
  rcases eq_or_neBot (𝓝[s inter Iio x] x) with h | h
  · simp [h]
  suffices H : Tendsto (fun y => eVariationOn f (s inter Ico y x) + edist (f x) l)
      (𝓝[s inter Iio x] x) (𝓝 (0 + edist (f x) l)) by
    simp only [zero_add] at H
    apply Tendsto.congr' _ H
    filter_upwards [self_mem_nhdsWithin] with y hy
    have N : 𝓝[s inter Ici y inter Iio x] x = 𝓝[s inter Iio x] x := by
      rw [show s inter Ici y inter Iio x = s inter Iio x inter Ici y by grind]; rw [nhdsWithin_inter_of_mem']
      exact mem_nhdsWithin_of_mem_nhds (Ici_mem_nhds hy.2)
    rw [show s inter Icc y x = (s inter Ici y) inter Iic x by grind]; rw [eVariationOn_on_inter_Iic_eq_Iio_add_edist (l := l)]
    · congr 2; grind
    · convert h using 1
    · exact ⟨hx, hy.2.le⟩
    · convert h'f
  apply Tendsto.add ?_ tendsto_const_nhds
  exact (hf.tendsto_eVariationOn_Ico_zero x).mono_left (nhdsWithin_mono _ inter_subset_left)

/--
theorem `_root_.BoundedVariationOn.tendsto_eVariationOn_Icc_right` / 定理 `_root_.BoundedVariationOn.tendsto_eVariationOn_Icc_right`

English:
theorem _root_.BoundedVariationOn.tendsto_eVariationOn_Icc_right
  proof: by
  have : (fun y => eVariationOn f (s inter Icc x y)) =
      (fun y => eVariationOn (f ∘ ofDual) (ofDual ⁻¹' s inter Icc (toDual y) (toDual x))) := by
    ext y
    rw [Icc_toDual]; rw [← preimage_inter]; rw [comp_ofDual]
  rw [this]
  exact hf.ofDual.tendsto_eVariationOn_Icc_left h'f hx

中文:
定理 _root_.BoundedVariationOn.tendsto_eVariationOn_Icc_right
  证明: by
  have : (fun y => eVariationOn f (s inter Icc x y)) =
      (fun y => eVariationOn (f ∘ ofDual) (ofDual ⁻¹' s inter Icc (toDual y) (toDual x))) := by
    ext y
    rw [Icc_toDual]; rw [← preimage_inter]; rw [comp_ofDual]
  rw [this]
  exact hf.ofDual.tendsto_eVariationOn_Icc_left h'f hx

Depends on / 依赖: Icc_toDual, comp_ofDual, eVariationOn, hf.ofDual.tendsto_eVariationOn_Icc_left, ofDual, preimage_inter, tendsto_eVariationOn_Icc_left, toDual
-/
theorem _root_.BoundedVariationOn.tendsto_eVariationOn_Icc_right
    [TopologicalSpace α] [OrderTopology α] {f : α -> E} {s : Set α} {l : E}
    (hf : BoundedVariationOn f s) {x : α} (h'f : Tendsto f (𝓝[s inter Ioi x] x) (𝓝 l)) (hx : x in s) :
    Tendsto (fun y => eVariationOn f (s inter Icc x y)) (𝓝[s inter Ioi x] x) (𝓝 (edist (f x) l)) := by
  have : (fun y => eVariationOn f (s inter Icc x y)) =
      (fun y => eVariationOn (f ∘ ofDual) (ofDual ⁻¹' s inter Icc (toDual y) (toDual x))) := by
    ext y
    rw [Icc_toDual]; rw [← preimage_inter]; rw [comp_ofDual]
  rw [this]
  exact hf.ofDual.tendsto_eVariationOn_Icc_left h'f hx

/--
theorem `_root_.LocallyBoundedVariationOn.tendsto_eVariationOn_Icc_left` / 定理 `_root_.LocallyBoundedVariationOn.tendsto_eVariationOn_Icc_left`

English:
theorem _root_.LocallyBoundedVariationOn.tendsto_eVariationOn_Icc_left
  proof: by
  rcases eq_or_neBot (𝓝[s inter Iio x] x) with h | h
  · simp [h]
  obtain ⟨y, hy⟩ : (s inter Iio x).Nonempty := by contrapose! h; simp [h]
  have : 𝓝[s inter Iio x] x = 𝓝[(s inter Icc y x) inter Iio x] x := by
    rw [show (s inter Icc y x) inter Iio x = (s inter Iio x) inter Icc y x by grind]; 

中文:
定理 _root_.LocallyBoundedVariationOn.tendsto_eVariationOn_Icc_left
  证明: by
  rcases eq_or_neBot (𝓝[s inter Iio x] x) with h | h
  · simp [h]
  obtain ⟨y, hy⟩ : (s inter Iio x).Nonempty := by contrapose! h; simp [h]
  have : 𝓝[s inter Iio x] x = 𝓝[(s inter Icc y x) inter Iio x] x := by
    rw [show (s inter Icc y x) inter Iio x = (s inter Iio x) inter Icc y x by grind]; 

Depends on / 依赖: BoundedVariationOn, Icc_mem_nhdsLT, Nonempty, Tendsto, Tendsto.congr, contrapose, eq_comm, eq_or_neBot, inter_subset_right, nhdsWithin_inter_of_mem, nhdsWithin_mono
-/
theorem _root_.LocallyBoundedVariationOn.tendsto_eVariationOn_Icc_left
    [TopologicalSpace α] [OrderTopology α] {f : α -> E} {s : Set α} {l : E}
    (hf : LocallyBoundedVariationOn f s) {x : α}
    (h'f : Tendsto f (𝓝[s inter Iio x] x) (𝓝 l)) (hx : x in s) :
    Tendsto (fun y => eVariationOn f (s inter Icc y x)) (𝓝[s inter Iio x] x) (𝓝 (edist (f x) l)) := by
  rcases eq_or_neBot (𝓝[s inter Iio x] x) with h | h
  · simp [h]
  obtain ⟨y, hy⟩ : (s inter Iio x).Nonempty := by contrapose! h; simp [h]
  have : 𝓝[s inter Iio x] x = 𝓝[(s inter Icc y x) inter Iio x] x := by
    rw [show (s inter Icc y x) inter Iio x = (s inter Iio x) inter Icc y x by grind]; rw [eq_comm]
    apply nhdsWithin_inter_of_mem' (nhdsWithin_mono _ inter_subset_right (Icc_mem_nhdsLT hy.2))
  rw [this] at h'f ⊢
  have : BoundedVariationOn f (s inter Icc y x) := hf _ _ hy.1 hx
  apply Tendsto.congr' _ (this.tendsto_eVariationOn_Icc_left h'f ⟨hx, by grind⟩)
  filter_upwards [self_mem_nhdsWithin] with z hz
  congr 1
  grind

/--
theorem `_root_.LocallyBoundedVariationOn.tendsto_eVariationOn_Icc_right` / 定理 `_root_.LocallyBoundedVariationOn.tendsto_eVariationOn_Icc_right`

English:
theorem _root_.LocallyBoundedVariationOn.tendsto_eVariationOn_Icc_right
  proof: by
  have : (fun y => eVariationOn f (s inter Icc x y)) =
      (fun y => eVariationOn (f ∘ ofDual) (ofDual ⁻¹' s inter Icc (toDual y) (toDual x))) := by
    ext y
    rw [Icc_toDual]; rw [← preimage_inter]; rw [comp_ofDual]
  rw [this]
  exact hf.ofDual.tendsto_eVariationOn_Icc_left h'f hx

中文:
定理 _root_.LocallyBoundedVariationOn.tendsto_eVariationOn_Icc_right
  证明: by
  have : (fun y => eVariationOn f (s inter Icc x y)) =
      (fun y => eVariationOn (f ∘ ofDual) (ofDual ⁻¹' s inter Icc (toDual y) (toDual x))) := by
    ext y
    rw [Icc_toDual]; rw [← preimage_inter]; rw [comp_ofDual]
  rw [this]
  exact hf.ofDual.tendsto_eVariationOn_Icc_left h'f hx

Depends on / 依赖: Icc_toDual, comp_ofDual, eVariationOn, hf.ofDual.tendsto_eVariationOn_Icc_left, ofDual, preimage_inter, tendsto_eVariationOn_Icc_left, toDual
-/
theorem _root_.LocallyBoundedVariationOn.tendsto_eVariationOn_Icc_right
    [TopologicalSpace α] [OrderTopology α] {f : α -> E} {s : Set α} {l : E}
    (hf : LocallyBoundedVariationOn f s) {x : α}
    (h'f : Tendsto f (𝓝[s inter Ioi x] x) (𝓝 l)) (hx : x in s) :
    Tendsto (fun y => eVariationOn f (s inter Icc x y)) (𝓝[s inter Ioi x] x) (𝓝 (edist (f x) l)) := by
  have : (fun y => eVariationOn f (s inter Icc x y)) =
      (fun y => eVariationOn (f ∘ ofDual) (ofDual ⁻¹' s inter Icc (toDual y) (toDual x))) := by
    ext y
    rw [Icc_toDual]; rw [← preimage_inter]; rw [comp_ofDual]
  rw [this]
  exact hf.ofDual.tendsto_eVariationOn_Icc_left h'f hx

/--
theorem `_root_.BoundedVariationOn.tendsto_eVariationOn_Icc_zero_left` / 定理 `_root_.BoundedVariationOn.tendsto_eVariationOn_Icc_zero_left`

English:
theorem _root_.BoundedVariationOn.tendsto_eVariationOn_Icc_zero_left
  proof: by
  rcases eq_or_neBot (𝓝[s inter Iio x] x) with h' | h'
  · apply tendsto_const_nhds.congr'
    have : s = (s inter Iio x) union (s inter Ici x) := by grind
    nth_rewrite 1 [this]
    simp only [nhdsWithin_union, h', bot_le, sup_of_le_right]
    filter_upwards [self_mem_nhdsWithin] with y hy
   

中文:
定理 _root_.BoundedVariationOn.tendsto_eVariationOn_Icc_zero_left
  证明: by
  rcases eq_or_neBot (𝓝[s inter Iio x] x) with h' | h'
  · apply tendsto_const_nhds.congr'
    have : s = (s inter Iio x) union (s inter Ici x) := by grind
    nth_rewrite 1 [this]
    simp only [nhdsWithin_union, h', bot_le, sup_of_le_right]
    filter_upwards [self_mem_nhdsWithin] with y hy
   

Depends on / 依赖: Set.Subsingleton, Subsingleton, bot_le, eVariationOn, eVariationOn.subsinglet, eVariationOn.subsingleton, eq_or_neBot, filter_upwards, hf.tendsto_eVariationOn_Ico_zero, le_or_gt, nhdsWithin_union, nth_rewrite, self_mem_nhdsWithin, subsinglet, subsingleton, sup_of_le_right, tendsto_const_nhds, tendsto_const_nhds.congr, tendsto_eVariationOn_Ico_zero
-/
theorem _root_.BoundedVariationOn.tendsto_eVariationOn_Icc_zero_left
    [TopologicalSpace α] [OrderTopology α] {f : α -> E} {s : Set α}
    (hf : BoundedVariationOn f s) {x : α} (h : ContinuousWithinAt f (s inter Iic x) x) :
    Tendsto (fun y => eVariationOn f (s inter Icc y x)) (𝓝[s] x) (𝓝 0) := by
  rcases eq_or_neBot (𝓝[s inter Iio x] x) with h' | h'
  · apply tendsto_const_nhds.congr'
    have : s = (s inter Iio x) union (s inter Ici x) := by grind
    nth_rewrite 1 [this]
    simp only [nhdsWithin_union, h', bot_le, sup_of_le_right]
    filter_upwards [self_mem_nhdsWithin] with y hy
    apply (eVariationOn.subsingleton _ (by grind [Set.Subsingleton])).symm
  apply (hf.tendsto_eVariationOn_Ico_zero x).congr (fun y => ?_)
  rcases le_or_gt x y with hy | hy
  · rw [eVariationOn.subsingleton, eVariationOn.subsingleton] <;>
      grind [Set.Subsingleton]
  have W := eVariationOn_inter_Iio_eq_inter_Iic_of_continuousWithinAt (f := f)
    (s := s inter Icc y x) (a := x) ?_ ?_
  · convert! W using 2 <;> grind
  · rwa [show s inter Icc y x inter Iio x = (s inter Iio x) inter Ici y by grind, nhdsWithin_inter_of_mem']
    apply mem_nhdsWithin_of_mem_nhds
    exact Ici_mem_nhds hy
  · apply h.mono (by grind)

/--
theorem `_root_.BoundedVariationOn.tendsto_eVariationOn_Icc_zero_right` / 定理 `_root_.BoundedVariationOn.tendsto_eVariationOn_Icc_zero_right`

English:
theorem _root_.BoundedVariationOn.tendsto_eVariationOn_Icc_zero_right
  proof: by
  have : (fun y => eVariationOn f (s inter Icc x y)) =
      (fun y => eVariationOn (f ∘ ofDual) (ofDual ⁻¹' s inter Icc (toDual y) (toDual x))) := by
    ext y
    rw [Icc_toDual]; rw [← preimage_inter]; rw [comp_ofDual]
  rw [this]
  exact hf.ofDual.tendsto_eVariationOn_Icc_zero_left h

中文:
定理 _root_.BoundedVariationOn.tendsto_eVariationOn_Icc_zero_right
  证明: by
  have : (fun y => eVariationOn f (s inter Icc x y)) =
      (fun y => eVariationOn (f ∘ ofDual) (ofDual ⁻¹' s inter Icc (toDual y) (toDual x))) := by
    ext y
    rw [Icc_toDual]; rw [← preimage_inter]; rw [comp_ofDual]
  rw [this]
  exact hf.ofDual.tendsto_eVariationOn_Icc_zero_left h

Depends on / 依赖: Icc_toDual, comp_ofDual, eVariationOn, hf.ofDual.tendsto_eVariationOn_Icc_zero_left, ofDual, preimage_inter, tendsto_eVariationOn_Icc_zero_left, toDual
-/
theorem _root_.BoundedVariationOn.tendsto_eVariationOn_Icc_zero_right
    [TopologicalSpace α] [OrderTopology α] {f : α -> E} {s : Set α}
    (hf : BoundedVariationOn f s) (x : α) (h : ContinuousWithinAt f (s inter Ici x) x) :
    Tendsto (fun y => eVariationOn f (s inter Icc x y)) (𝓝[s] x) (𝓝 0) := by
  have : (fun y => eVariationOn f (s inter Icc x y)) =
      (fun y => eVariationOn (f ∘ ofDual) (ofDual ⁻¹' s inter Icc (toDual y) (toDual x))) := by
    ext y
    rw [Icc_toDual]; rw [← preimage_inter]; rw [comp_ofDual]
  rw [this]
  exact hf.ofDual.tendsto_eVariationOn_Icc_zero_left h

/--
lemma `eVariationOn_le_of_mapClusterPt` / 引理 `eVariationOn_le_of_mapClusterPt`

English:
lemma eVariationOn_le_of_mapClusterPt
  proof: by
  rw [eVariationOn_eq_strictMonoOn]
  apply iSup_le
  rintro ⟨n, u, u_mono, u_mem⟩
  simp only
  have : Nonempty α := ⟨u 0⟩
  apply le_of_forall_lt (fun c hc => ?_)
  have : forallᶠ (b : Nat -> E) in 𝓝 (fun i => g (u i)),
      c < ∑ i in Finset.range n, edist (b (i + 1)) (b i) := by
    have : C

中文:
引理 eVariationOn_le_of_mapClusterPt
  证明: by
  rw [eVariationOn_eq_strictMonoOn]
  apply iSup_le
  rintro ⟨n, u, u_mono, u_mem⟩
  simp only
  have : Nonempty α := ⟨u 0⟩
  apply le_of_forall_lt (fun c hc => ?_)
  have : forallᶠ (b : Nat -> E) in 𝓝 (fun i => g (u i)),
      c < ∑ i in Finset.range n, edist (b (i + 1)) (b i) := by
    have : C
-/
private lemma eVariationOn_le_of_mapClusterPt
    [TopologicalSpace α] [OrderTopology α] {f g : α -> E}
    {s : Set α} (hg : forall x in s, MapClusterPt (g x) (𝓝[s] x) f) :
    eVariationOn g s <= eVariationOn f s := by
  rw [eVariationOn_eq_strictMonoOn]
  apply iSup_le
  rintro ⟨n, u, u_mono, u_mem⟩
  simp only
  have : Nonempty α := ⟨u 0⟩
  apply le_of_forall_lt (fun c hc => ?_)
  have : forallᶠ (b : Nat -> E) in 𝓝 (fun i => g (u i)),
      c < ∑ i in Finset.range n, edist (b (i + 1)) (b i) := by
    have : Continuous (fun (v : Nat -> E) => ∑ i in Finset.range n, edist (v (i + 1)) (v i)) := by
      fun_prop
    exact (tendsto_order.1 (this.continuousAt (x := fun i => g (u i))).tendsto).1 c hc
  rw [nhds_pi] at this
  obtain ⟨I, I_fin, t, t_mem, ht⟩ : exists (I : Set Nat), I.Finite ∧ exists t, (forall (i : Nat), t i in 𝓝 (g (u i))) ∧
      I.pi t subseteq {b : Nat -> E | c < ∑ i in Finset.range n, edist (b (i + 1)) (b i)} := mem_pi.1 this
  have : forallᶠ b in 𝓝 u, forall i in ((Finset.Iic n) ×ˢ (Finset.Iic n)).filter
      (fun i => i.1 < i.2), b i.1 < b i.2 := by
    rw [Filter.eventually_all_finset]
    intro i hi
    apply IsOpen.mem_nhds ?_ (by grind [StrictMonoOn])
    exact isOpen_lt (by fun_prop) (by fun_prop)
  rw [nhds_pi] at this
  obtain ⟨J, J_fin, k, k_mem, hk⟩ : exists (J : Set Nat), J.Finite ∧ exists k, (forall (i : Nat), k i in 𝓝 (u i)) ∧
    J.pi k subseteq _ := mem_pi.1 this
  have A i (hi : i in Iic n) : exists x, (f x in t i ∧ x in k i) ∧ x in s :=
    ((((mapClusterPt_iff_frequently.1 (hg (u i) (u_mem i hi)) (t i) (t_mem i))).and_eventually
      (mem_nhdsWithin_of_mem_nhds (k_mem i))).and_eventually self_mem_nhdsWithin).exists
  choose! v hv h'v using A
  have : c < ∑ i in Finset.range n, edist (f (v (i + 1))) (f (v i)) := by
    let f' i := if i in Iic n then f (v i) else g (u i)
    have : ∑ i in Finset.range n, edist (f (v (i + 1))) (f (v i)) =
        ∑ i in Finset.range n, edist (f' (i + 1)) (f' i) :=
      Finset.sum_congr rfl (fun i hi => by grind)
    rw [this]
    suffices H : f' in I.pi t from ht H
    have A i : g (u i) in t i := mem_of_mem_nhds (t_mem i)
    grind
  apply this.trans_le
  have v_mono : StrictMonoOn v (Iic n) := by
    let w i := if i in Iic n then v i else u i
    suffices w in J.pi k by
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Iic, and_imp, Prod.forall] at hk
      grind [StrictMonoOn]
    have A i : u i in k i := mem_of_mem_nhds (k_mem i)
    grind
  exact sum_le_of_monotoneOn_Iic v_mono.monotoneOn (by grind)

/--
lemma `eVariationOn_leftLim_le` / 引理 `eVariationOn_leftLim_le`

English:
lemma eVariationOn_leftLim_le
  statement: [TopologicalSpace α] [OrderTopology α] {f : α -> E}
  proof: by
  apply eVariationOn_le_of_mapClusterPt (fun x hx => ?_)
  rw [IsOpen.nhdsWithin_eq hs hx]
  exact (mapClusterPt_leftLim f x).mono nhdsWithin_le_nhds

中文:
引理 eVariationOn_leftLim_le
  结论: [拓扑空间 α] [Order拓扑 α] {f : α -> E}
  证明: by
  apply eVariationOn_le_of_mapClusterPt (fun x hx => ?_)
  rw [IsOpen.nhdsWithin_eq hs hx]
  exact (mapClusterPt_leftLim f x).mono nhdsWithin_le_nhds

Depends on / 依赖: IsOpen, IsOpen.nhdsWithin_eq, eVariationOn_le_of_mapClusterPt, mapClusterPt_leftLim, nhdsWithin_eq, nhdsWithin_le_nhds
-/
lemma eVariationOn_leftLim_le [TopologicalSpace α] [OrderTopology α] {f : α -> E}
    {s : Set α} (hs : IsOpen s) :
    eVariationOn f.leftLim s <= eVariationOn f s := by
  apply eVariationOn_le_of_mapClusterPt (fun x hx => ?_)
  rw [IsOpen.nhdsWithin_eq hs hx]
  exact (mapClusterPt_leftLim f x).mono nhdsWithin_le_nhds

/--
lemma `eVariationOn_rightLim_le` / 引理 `eVariationOn_rightLim_le`

English:
lemma eVariationOn_rightLim_le
  statement: [TopologicalSpace α] [OrderTopology α] {f : α -> E}
  proof: by
  apply eVariationOn_le_of_mapClusterPt (fun x hx => ?_)
  rw [IsOpen.nhdsWithin_eq hs hx]
  exact (mapClusterPt_rightLim f x).mono nhdsWithin_le_nhds

中文:
引理 eVariationOn_rightLim_le
  结论: [拓扑空间 α] [Order拓扑 α] {f : α -> E}
  证明: by
  apply eVariationOn_le_of_mapClusterPt (fun x hx => ?_)
  rw [IsOpen.nhdsWithin_eq hs hx]
  exact (mapClusterPt_rightLim f x).mono nhdsWithin_le_nhds

Depends on / 依赖: IsOpen, IsOpen.nhdsWithin_eq, eVariationOn_le_of_mapClusterPt, mapClusterPt_rightLim, nhdsWithin_eq, nhdsWithin_le_nhds
-/
lemma eVariationOn_rightLim_le [TopologicalSpace α] [OrderTopology α] {f : α -> E}
    {s : Set α} (hs : IsOpen s) :
    eVariationOn f.rightLim s <= eVariationOn f s := by
  apply eVariationOn_le_of_mapClusterPt (fun x hx => ?_)
  rw [IsOpen.nhdsWithin_eq hs hx]
  exact (mapClusterPt_rightLim f x).mono nhdsWithin_le_nhds

/--
lemma `_root_.BoundedVariationOn.leftLim` / 引理 `_root_.BoundedVariationOn.leftLim`

English:
lemma _root_.BoundedVariationOn.leftLim
  statement: [TopologicalSpace α] [OrderTopology α] {f : α -> E}
  proof: ((eVariationOn_leftLim_le isOpen_univ).trans_lt hf.lt_top).ne

中文:
引理 _root_.BoundedVariationOn.leftLim
  结论: [拓扑空间 α] [Order拓扑 α] {f : α -> E}
  证明: ((eVariationOn_leftLim_le isOpen_univ).trans_lt hf.lt_top).ne

Depends on / 依赖: eVariationOn_leftLim_le, hf.lt_top, isOpen_univ, lt_top, trans_lt
-/
lemma _root_.BoundedVariationOn.leftLim [TopologicalSpace α] [OrderTopology α] {f : α -> E}
    (hf : BoundedVariationOn f univ) : BoundedVariationOn f.leftLim univ :=
  ((eVariationOn_leftLim_le isOpen_univ).trans_lt hf.lt_top).ne

/--
lemma `_root_.BoundedVariationOn.rightLim` / 引理 `_root_.BoundedVariationOn.rightLim`

English:
lemma _root_.BoundedVariationOn.rightLim
  statement: [TopologicalSpace α] [OrderTopology α] {f : α -> E}
  proof: ((eVariationOn_rightLim_le isOpen_univ).trans_lt hf.lt_top).ne

中文:
引理 _root_.BoundedVariationOn.rightLim
  结论: [拓扑空间 α] [Order拓扑 α] {f : α -> E}
  证明: ((eVariationOn_rightLim_le isOpen_univ).trans_lt hf.lt_top).ne

Depends on / 依赖: eVariationOn_rightLim_le, hf.lt_top, isOpen_univ, lt_top, trans_lt
-/
lemma _root_.BoundedVariationOn.rightLim [TopologicalSpace α] [OrderTopology α] {f : α -> E}
    (hf : BoundedVariationOn f univ) : BoundedVariationOn f.rightLim univ :=
  ((eVariationOn_rightLim_le isOpen_univ).trans_lt hf.lt_top).ne

/--
lemma `_root_.BoundedVariationOn.continuousWithinAt_leftLim` / 引理 `_root_.BoundedVariationOn.continuousWithinAt_leftLim`

English:
lemma _root_.BoundedVariationOn.continuousWithinAt_leftLim
  statement: [TopologicalSpace α] [OrderTopology α]
  proof: by
  have : Tendsto f.leftLim (𝓝[<] x) (𝓝 (f.leftLim.leftLim x)) := hf.leftLim.tendsto_leftLim x
  rw [leftLim_leftLim (hf.tendsto_leftLim x)] at this
  exact continuousWithinAt_Iio_iff_Iic.1 this

中文:
引理 _root_.BoundedVariationOn.continuousWithinAt_leftLim
  结论: [拓扑空间 α] [Order拓扑 α]
  证明: by
  have : Tendsto f.leftLim (𝓝[<] x) (𝓝 (f.leftLim.leftLim x)) := hf.leftLim.tendsto_leftLim x
  rw [leftLim_leftLim (hf.tendsto_leftLim x)] at this
  exact continuousWithinAt_Iio_iff_Iic.1 this

Depends on / 依赖: Tendsto, continuousWithinAt_Iio_iff_Iic, f.leftLim, f.leftLim.leftLim, hf.leftLim.tendsto_leftLim, hf.tendsto_leftLim, leftLim, leftLim_leftLim, tendsto_leftLim
-/
lemma _root_.BoundedVariationOn.continuousWithinAt_leftLim [TopologicalSpace α] [OrderTopology α]
    [CompleteSpace E] [T3Space E] {f : α -> E} (hf : BoundedVariationOn f univ) {x : α} :
    ContinuousWithinAt f.leftLim (Iic x) x := by
  have : Tendsto f.leftLim (𝓝[<] x) (𝓝 (f.leftLim.leftLim x)) := hf.leftLim.tendsto_leftLim x
  rw [leftLim_leftLim (hf.tendsto_leftLim x)] at this
  exact continuousWithinAt_Iio_iff_Iic.1 this

/--
lemma `_root_.BoundedVariationOn.continuousWithinAt_rightLim` / 引理 `_root_.BoundedVariationOn.continuousWithinAt_rightLim`

English:
lemma _root_.BoundedVariationOn.continuousWithinAt_rightLim
  statement: [TopologicalSpace α] [OrderTopology α]
  proof: BoundedVariationOn.continuousWithinAt_leftLim hf.ofDual

中文:
引理 _root_.BoundedVariationOn.continuousWithinAt_rightLim
  结论: [拓扑空间 α] [Order拓扑 α]
  证明: BoundedVariationOn.continuousWithinAt_leftLim hf.ofDual

Depends on / 依赖: BoundedVariationOn, BoundedVariationOn.continuousWithinAt_leftLim, continuousWithinAt_leftLim, hf.ofDual, ofDual
-/
lemma _root_.BoundedVariationOn.continuousWithinAt_rightLim [TopologicalSpace α] [OrderTopology α]
    [CompleteSpace E] [T3Space E] {f : α -> E} (hf : BoundedVariationOn f univ) {x : α} :
    ContinuousWithinAt f.rightLim (Ici x) x :=
  BoundedVariationOn.continuousWithinAt_leftLim hf.ofDual

/-! ### Limits of bounded variation functions as `± ∞` -/

/--
theorem `_root_.BoundedVariationOn.tendsto_eVariationOn_Ici_zero` / 定理 `_root_.BoundedVariationOn.tendsto_eVariationOn_Ici_zero`

English:
theorem _root_.BoundedVariationOn.tendsto_eVariationOn_Ici_zero
  proof: hf.tendsto_eVariationOn_Ici_zero_of_filter _
    (fun y _ => inter_mem_inf (mem_principal_self s) (Ici_mem_atTop y))

中文:
定理 _root_.BoundedVariationOn.tendsto_eVariationOn_Ici_zero
  证明: hf.tendsto_eVariationOn_Ici_zero_of_filter _
    (fun y _ => inter_mem_inf (mem_principal_self s) (Ici_mem_atTop y))

Depends on / 依赖: Ici_mem_atTop, hf.tendsto_eVariationOn_Ici_zero_of_filter, inter_mem_inf, mem_principal_self, tendsto_eVariationOn_Ici_zero_of_filter
-/
theorem _root_.BoundedVariationOn.tendsto_eVariationOn_Ici_zero
    {f : α -> E} {s : Set α} (hf : BoundedVariationOn f s) :
    Tendsto (fun y => eVariationOn f (s inter Ici y)) (𝓟 s ⊓ atTop) (𝓝 0) :=
  hf.tendsto_eVariationOn_Ici_zero_of_filter _
    (fun y _ => inter_mem_inf (mem_principal_self s) (Ici_mem_atTop y))

/--
theorem `_root_.BoundedVariationOn.tendsto_eVariationOn_Iic_zero` / 定理 `_root_.BoundedVariationOn.tendsto_eVariationOn_Iic_zero`

English:
theorem _root_.BoundedVariationOn.tendsto_eVariationOn_Iic_zero
  proof: by
  have : (fun y => eVariationOn f (s inter Iic y)) =
      (fun y => eVariationOn (f ∘ ofDual) (ofDual ⁻¹' s inter Ici (toDual y))) := by
    ext y
    rw [Ici_toDual]; rw [← preimage_inter]; rw [comp_ofDual]
  rw [this]
  exact hf.ofDual.tendsto_eVariationOn_Ici_zero

中文:
定理 _root_.BoundedVariationOn.tendsto_eVariationOn_Iic_zero
  证明: by
  have : (fun y => eVariationOn f (s inter Iic y)) =
      (fun y => eVariationOn (f ∘ ofDual) (ofDual ⁻¹' s inter Ici (toDual y))) := by
    ext y
    rw [Ici_toDual]; rw [← preimage_inter]; rw [comp_ofDual]
  rw [this]
  exact hf.ofDual.tendsto_eVariationOn_Ici_zero

Depends on / 依赖: Ici_toDual, comp_ofDual, eVariationOn, hf.ofDual.tendsto_eVariationOn_Ici_zero, ofDual, preimage_inter, tendsto_eVariationOn_Ici_zero, toDual
-/
theorem _root_.BoundedVariationOn.tendsto_eVariationOn_Iic_zero
    {f : α -> E} {s : Set α} (hf : BoundedVariationOn f s) :
    Tendsto (fun y => eVariationOn f (s inter Iic y)) (𝓟 s ⊓ atBot) (𝓝 0) := by
  have : (fun y => eVariationOn f (s inter Iic y)) =
      (fun y => eVariationOn (f ∘ ofDual) (ofDual ⁻¹' s inter Ici (toDual y))) := by
    ext y
    rw [Ici_toDual]; rw [← preimage_inter]; rw [comp_ofDual]
  rw [this]
  exact hf.ofDual.tendsto_eVariationOn_Ici_zero

/--
theorem `_root_.BoundedVariationOn.exists_tendsto_atTop` / 定理 `_root_.BoundedVariationOn.exists_tendsto_atTop`

English:
theorem _root_.BoundedVariationOn.exists_tendsto_atTop
  statement: [CompleteSpace E] [hE : Nonempty E]
  proof: by
  rcases eq_empty_or_nonempty s with rfl | hs
  · simp
  · exact hf.exists_tendsto_left_of_filter _
      (fun y hy => inter_mem_inf (mem_principal_self s) (Ici_mem_atTop _)) hs

中文:
定理 _root_.BoundedVariationOn.存在_tendsto_atTop
  结论: [完备空间 E] [hE : 非空 E]
  证明: by
  rcases eq_empty_or_nonempty s with rfl | hs
  · simp
  · exact hf.exists_tendsto_left_of_filter _
      (fun y hy => inter_mem_inf (mem_principal_self s) (Ici_mem_atTop _)) hs

Depends on / 依赖: Ici_mem_atTop, eq_empty_or_nonempty, exists_tendsto_left_of_filter, hf.exists_tendsto_left_of_filter, inter_mem_inf, mem_principal_self
-/
theorem _root_.BoundedVariationOn.exists_tendsto_atTop [CompleteSpace E] [hE : Nonempty E]
    {f : α -> E} {s : Set α} (hf : BoundedVariationOn f s) :
    exists l, Tendsto f (𝓟 s ⊓ atTop) (𝓝 l) := by
  rcases eq_empty_or_nonempty s with rfl | hs
  · simp
  · exact hf.exists_tendsto_left_of_filter _
      (fun y hy => inter_mem_inf (mem_principal_self s) (Ici_mem_atTop _)) hs

/--
theorem `_root_.BoundedVariationOn.exists_tendsto_atBot` / 定理 `_root_.BoundedVariationOn.exists_tendsto_atBot`

English:
theorem _root_.BoundedVariationOn.exists_tendsto_atBot
  statement: [CompleteSpace E] [hE : Nonempty E]
  proof: hf.ofDual.exists_tendsto_atTop

中文:
定理 _root_.BoundedVariationOn.存在_tendsto_atBot
  结论: [完备空间 E] [hE : 非空 E]
  证明: hf.ofDual.exists_tendsto_atTop

Depends on / 依赖: exists_tendsto_atTop, hf.ofDual.exists_tendsto_atTop, ofDual
-/
theorem _root_.BoundedVariationOn.exists_tendsto_atBot [CompleteSpace E] [hE : Nonempty E]
    {f : α -> E} {s : Set α} (hf : BoundedVariationOn f s) :
    exists l, Tendsto f (𝓟 s ⊓ atBot) (𝓝 l) :=
  hf.ofDual.exists_tendsto_atTop

/--
theorem `_root_.BoundedVariationOn.tendsto_atTop_limUnder` / 定理 `_root_.BoundedVariationOn.tendsto_atTop_limUnder`

English:
theorem _root_.BoundedVariationOn.tendsto_atTop_limUnder
  statement: [CompleteSpace E] [hE : Nonempty E]
  proof: tendsto_nhds_limUnder (by simpa using hf.exists_tendsto_atTop)

中文:
定理 _root_.BoundedVariationOn.tendsto_atTop_limUnder
  结论: [完备空间 E] [hE : 非空 E]
  证明: tendsto_nhds_limUnder (by simpa using hf.exists_tendsto_atTop)

Depends on / 依赖: exists_tendsto_atTop, hf.exists_tendsto_atTop, tendsto_nhds_limUnder
-/
theorem _root_.BoundedVariationOn.tendsto_atTop_limUnder [CompleteSpace E] [hE : Nonempty E]
    {f : α -> E} (hf : BoundedVariationOn f univ) :
    Tendsto f atTop (𝓝 (limUnder atTop f)) :=
  tendsto_nhds_limUnder (by simpa using hf.exists_tendsto_atTop)

/--
theorem `_root_.BoundedVariationOn.tendsto_atBot_limUnder` / 定理 `_root_.BoundedVariationOn.tendsto_atBot_limUnder`

English:
theorem _root_.BoundedVariationOn.tendsto_atBot_limUnder
  statement: [CompleteSpace E] [hE : Nonempty E]
  proof: tendsto_nhds_limUnder (by simpa using hf.exists_tendsto_atBot)

中文:
定理 _root_.BoundedVariationOn.tendsto_atBot_limUnder
  结论: [完备空间 E] [hE : 非空 E]
  证明: tendsto_nhds_limUnder (by simpa using hf.exists_tendsto_atBot)

Depends on / 依赖: exists_tendsto_atBot, hf.exists_tendsto_atBot, tendsto_nhds_limUnder
-/
theorem _root_.BoundedVariationOn.tendsto_atBot_limUnder [CompleteSpace E] [hE : Nonempty E]
    {f : α -> E} (hf : BoundedVariationOn f univ) :
    Tendsto f atBot (𝓝 (limUnder atBot f)) :=
  tendsto_nhds_limUnder (by simpa using hf.exists_tendsto_atBot)

end eVariationOn

section Monotone

/-! ### Variation of monotone functions -/

open ENNReal Finset

variable {f : α -> Real} {s : Set α} {C : Real} {a b : α}

/--
theorem `MonotoneOn.eVariationOn_eq` / 定理 `MonotoneOn.eVariationOn_eq`

English:
theorem MonotoneOn.eVariationOn_eq
  given: (hf : MonotoneOn f s) (as : a in s) (bs : b in s)
  proof: by
  rcases le_or_gt a b with hab | hab
  · have hle : eVariationOn f (s inter Icc a b) <= .ofReal (f b - f a) := by
      apply iSup_le _
      rintro ⟨n, ⟨u, hu, us⟩⟩
      calc
        _ = ∑ i in range n, .ofReal (f (u (i + 1)) - f (u i)) := by
          refine sum_congr rfl fun i hi => ?_
      

中文:
定理 MonotoneOn.eVariationOn_eq
  条件: (hf : MonotoneOn f s) (as : a in s) (bs : b in s)
  证明: by
  rcases le_or_gt a b with hab | hab
  · have hle : eVariationOn f (s inter Icc a b) <= .ofReal (f b - f a) := by
      apply iSup_le _
      rintro ⟨n, ⟨u, hu, us⟩⟩
      calc
        _ = ∑ i in range n, .ofReal (f (u (i + 1)) - f (u i)) := by
          refine sum_congr rfl fun i hi => ?_
      

Depends on / 依赖: Finset, Finset.mem_range, Nat.le_succ, Real.dist_eq, abs_of_nonneg, dist_eq, eVariationOn, edist_dist, iSup_le, le_or_gt, le_succ, mem_range, ofReal, ofReal_sum_of_non, sub_nonneg_of_le, sum_congr
-/
theorem MonotoneOn.eVariationOn_eq (hf : MonotoneOn f s) (as : a in s) (bs : b in s) :
    eVariationOn f (s inter Icc a b) = .ofReal (f b - f a) := by
  rcases le_or_gt a b with hab | hab
  · have hle : eVariationOn f (s inter Icc a b) <= .ofReal (f b - f a) := by
      apply iSup_le _
      rintro ⟨n, ⟨u, hu, us⟩⟩
      calc
        _ = ∑ i in range n, .ofReal (f (u (i + 1)) - f (u i)) := by
          refine sum_congr rfl fun i hi => ?_
          simp only [Finset.mem_range] at hi
          rw [edist_dist]; rw [Real.dist_eq]; rw [abs_of_nonneg]
          exact sub_nonneg_of_le (hf (us i).1 (us (i + 1)).1 (hu (Nat.le_succ _)))
        _ = .ofReal (∑ i in range n, (f (u (i + 1)) - f (u i))) := by
          rw [ofReal_sum_of_nonneg]
          exact fun i _ => sub_nonneg_of_le (hf (us i).1 (us (i + 1)).1 (hu (Nat.le_succ _)))
        _ = .ofReal (f (u n) - f (u 0)) := by rw [sum_range_sub (f <| u ·)]
        _ <= _ :=
          ofReal_le_ofReal (sub_le_sub (hf (us n).1 bs (us n).2.2) (hf as (us 0).1 (us 0).2.1))
    have h : BoundedVariationOn f (s inter Icc a b) := (hle.trans_lt ofReal_lt_top).ne
    apply eq_of_le_of_ge hle (ofReal_le_of_le_toReal _)
    grw [← h.dist_le (x := a) (y := b)] <;> grind [Real.dist_eq]
  · simp [hab, hf bs as hab.le]

@[deprecated MonotoneOn.eVariationOn_eq (since := "2026-07-08")]
/--
theorem `MonotoneOn.eVariationOn_le` / 定理 `MonotoneOn.eVariationOn_le`

English:
theorem MonotoneOn.eVariationOn_le
  given: (hf : MonotoneOn f s) (as : a in s) (bs : b in s)
  proof: (hf.eVariationOn_eq as bs).le

中文:
定理 MonotoneOn.eVariationOn_le
  条件: (hf : MonotoneOn f s) (as : a in s) (bs : b in s)
  证明: (hf.eVariationOn_eq as bs).le

Depends on / 依赖: eVariationOn_eq, hf.eVariationOn_eq
-/
theorem MonotoneOn.eVariationOn_le (hf : MonotoneOn f s) (as : a in s) (bs : b in s) :
    eVariationOn f (s inter Icc a b) <= .ofReal (f b - f a) := (hf.eVariationOn_eq as bs).le

/--
theorem `MonotoneOn.locallyBoundedVariationOn` / 定理 `MonotoneOn.locallyBoundedVariationOn`

English:
theorem MonotoneOn.locallyBoundedVariationOn
  given: (hf : MonotoneOn f s)
  proof: fun _ _ as bs =>
  ((hf.eVariationOn_eq as bs) ▸ ofReal_lt_top).ne

中文:
定理 MonotoneOn.locallyBoundedVariationOn
  条件: (hf : MonotoneOn f s)
  证明: fun _ _ as bs =>
  ((hf.eVariationOn_eq as bs) ▸ ofReal_lt_top).ne
-/
theorem MonotoneOn.locallyBoundedVariationOn (hf : MonotoneOn f s) :
    LocallyBoundedVariationOn f s := fun _ _ as bs =>
  ((hf.eVariationOn_eq as bs) ▸ ofReal_lt_top).ne

/--
theorem `MonotoneOn.boundedVariationOn` / 定理 `MonotoneOn.boundedVariationOn`

English:
theorem MonotoneOn.boundedVariationOn
  given: (hf : MonotoneOn f s) (h : forall x in s, |f x| <= C)
  proof: by
  suffices eVariationOn f s <= .ofReal (2 * C) from
    ne_of_lt (this.trans_lt (by simp [mul_lt_top]))
  rw [eVariationOn.eq_biSup_inter_Icc]
  simp only [mem_ofPred_eq, iSup_le_iff, and_imp, Prod.forall]
  intro a b as bs hab
  grw [hf.eVariationOn_eq as bs]
  exact ofReal_mono (by grind)

中文:
定理 MonotoneOn.boundedVariationOn
  条件: (hf : MonotoneOn f s) (h : 对任意 x in s, |f x| <= C)
  证明: by
  suffices eVariationOn f s <= .ofReal (2 * C) from
    ne_of_lt (this.trans_lt (by simp [mul_lt_top]))
  rw [eVariationOn.eq_biSup_inter_Icc]
  simp only [mem_ofPred_eq, iSup_le_iff, and_imp, Prod.forall]
  intro a b as bs hab
  grw [hf.eVariationOn_eq as bs]
  exact ofReal_mono (by grind)

Depends on / 依赖: Prod.forall, and_imp, eVariationOn, eVariationOn.eq_biSup_inter_Icc, eVariationOn_eq, eq_biSup_inter_Icc, hf.eVariationOn_eq, iSup_le_iff, mem_ofPred_eq, mul_lt_top, ne_of_lt, ofReal, ofReal_mono, this.trans_lt, trans_lt
-/
theorem MonotoneOn.boundedVariationOn (hf : MonotoneOn f s) (h : forall x in s, |f x| <= C) :
    BoundedVariationOn f s := by
  suffices eVariationOn f s <= .ofReal (2 * C) from
    ne_of_lt (this.trans_lt (by simp [mul_lt_top]))
  rw [eVariationOn.eq_biSup_inter_Icc]
  simp only [mem_ofPred_eq, iSup_le_iff, and_imp, Prod.forall]
  intro a b as bs hab
  grw [hf.eVariationOn_eq as bs]
  exact ofReal_mono (by grind)

/--
lemma `eVariationOn_id` / 引理 `eVariationOn_id`

English:
lemma eVariationOn_id
  given: {a b : Real} {s : Set Real} (as : a in s) (bs : b in s)
  proof: (monotone_id.monotoneOn _).eVariationOn_eq as bs

中文:
引理 eVariationOn_id
  条件: {a b : 实数} {s : 集合 实数} (as : a in s) (bs : b in s)
  证明: (monotone_id.monotoneOn _).eVariationOn_eq as bs

Depends on / 依赖: eVariationOn_eq, monotoneOn, monotone_id, monotone_id.monotoneOn
-/
lemma eVariationOn_id {a b : Real} {s : Set Real} (as : a in s) (bs : b in s) :
    eVariationOn id (s inter Icc a b) = .ofReal (b - a) :=
  (monotone_id.monotoneOn _).eVariationOn_eq as bs

/-- The variation of the identity on `Icc a b` is `b - a`. -/
@[simp]
/--
lemma `eVariationOn_id_Icc` / 引理 `eVariationOn_id_Icc`

English:
lemma eVariationOn_id_Icc
  given: (a b : Real)
  statement: eVariationOn id (Icc a b) = .ofReal (b - a)
  proof: by
  simpa using eVariationOn_id (s := univ) (by simp) (by simp)

中文:
引理 eVariationOn_id_Icc
  条件: (a b : 实数)
  结论: eVariationOn id (闭区间 a b) = .of实数 (b - a)
  证明: by
  simpa using eVariationOn_id (s := univ) (by simp) (by simp)

Depends on / 依赖: eVariationOn_id
-/
lemma eVariationOn_id_Icc (a b : Real) : eVariationOn id (Icc a b) = .ofReal (b - a) := by
  simpa using eVariationOn_id (s := univ) (by simp) (by simp)

/-- The identity function has bounded variation on every interval `Icc a b`. -/
@[simp]
/--
lemma `BoundedVariationOn.id_Icc` / 引理 `BoundedVariationOn.id_Icc`

English:
lemma BoundedVariationOn.id_Icc
  given: (a b : Real)
  statement: BoundedVariationOn id (Icc a b)
  proof: by
  simp [BoundedVariationOn]

中文:
引理 BoundedVariationOn.id_Icc
  条件: (a b : 实数)
  结论: BoundedVariationOn id (闭区间 a b)
  证明: by
  simp [BoundedVariationOn]

Depends on / 依赖: BoundedVariationOn
-/
lemma BoundedVariationOn.id_Icc (a b : Real) : BoundedVariationOn id (Icc a b) := by
  simp [BoundedVariationOn]

end Monotone

/-! ### Lipschitz functions and bounded variation -/

section LipschitzOnWith

variable {F : Type*} [PseudoEMetricSpace F]

/--
theorem `LipschitzOnWith.comp_eVariationOn_le` / 定理 `LipschitzOnWith.comp_eVariationOn_le`

English:
theorem LipschitzOnWith.comp_eVariationOn_le
  statement: {f : E -> F} {C : Real>=0} {t : Set E}
  proof: by
  apply iSup_le _
  rintro ⟨n, ⟨u, hu, us⟩⟩
  calc
    (∑ i in Finset.range n, edist (f (g (u (i + 1)))) (f (g (u i)))) <=
        ∑ i in Finset.range n, C * edist (g (u (i + 1))) (g (u i)) :=
      Finset.sum_le_sum fun i _ => h (hg (us _)) (hg (us _))
    _ = C * ∑ i in Finset.range n, edist (g

中文:
定理 LipschitzOnWith.comp_eVariationOn_le
  结论: {f : E -> F} {C : 实数>=0} {t : 集合 E}
  证明: by
  apply iSup_le _
  rintro ⟨n, ⟨u, hu, us⟩⟩
  calc
    (∑ i in Finset.range n, edist (f (g (u (i + 1)))) (f (g (u i)))) <=
        ∑ i in Finset.range n, C * edist (g (u (i + 1))) (g (u i)) :=
      Finset.sum_le_sum fun i _ => h (hg (us _)) (hg (us _))
    _ = C * ∑ i in Finset.range n, edist (g

Depends on / 依赖: Finset, Finset.mul_sum, Finset.range, Finset.sum_le_sum, eVariationOn, eVariationOn.sum_le, iSup_le, mul_sum, sum_le, sum_le_sum
-/
theorem LipschitzOnWith.comp_eVariationOn_le {f : E -> F} {C : Real>=0} {t : Set E}
    (h : LipschitzOnWith C f t) {g : α -> E} {s : Set α} (hg : MapsTo g s t) :
    eVariationOn (f ∘ g) s <= C * eVariationOn g s := by
  apply iSup_le _
  rintro ⟨n, ⟨u, hu, us⟩⟩
  calc
    (∑ i in Finset.range n, edist (f (g (u (i + 1)))) (f (g (u i)))) <=
        ∑ i in Finset.range n, C * edist (g (u (i + 1))) (g (u i)) :=
      Finset.sum_le_sum fun i _ => h (hg (us _)) (hg (us _))
    _ = C * ∑ i in Finset.range n, edist (g (u (i + 1))) (g (u i)) := by rw [Finset.mul_sum]
    _ <= C * eVariationOn g s := by grw [eVariationOn.sum_le hu us]

/--
theorem `LipschitzOnWith.comp_boundedVariationOn` / 定理 `LipschitzOnWith.comp_boundedVariationOn`

English:
theorem LipschitzOnWith.comp_boundedVariationOn
  statement: {f : E -> F} {C : Real>=0} {t : Set E}
  proof: ne_top_of_le_ne_top (by finiteness) (hf.comp_eVariationOn_le hg)

中文:
定理 LipschitzOnWith.comp_boundedVariationOn
  结论: {f : E -> F} {C : 实数>=0} {t : 集合 E}
  证明: ne_top_of_le_ne_top (by finiteness) (hf.comp_eVariationOn_le hg)

Depends on / 依赖: comp_eVariationOn_le, finiteness, hf.comp_eVariationOn_le, ne_top_of_le_ne_top
-/
theorem LipschitzOnWith.comp_boundedVariationOn {f : E -> F} {C : Real>=0} {t : Set E}
    (hf : LipschitzOnWith C f t) {g : α -> E} {s : Set α} (hg : MapsTo g s t)
    (h : BoundedVariationOn g s) : BoundedVariationOn (f ∘ g) s :=
  ne_top_of_le_ne_top (by finiteness) (hf.comp_eVariationOn_le hg)

/--
theorem `LipschitzOnWith.comp_locallyBoundedVariationOn` / 定理 `LipschitzOnWith.comp_locallyBoundedVariationOn`

English:
theorem LipschitzOnWith.comp_locallyBoundedVariationOn
  statement: {f : E -> F} {C : Real>=0} {t : Set E}
  proof: fun x y xs ys =>
  hf.comp_boundedVariationOn (hg.mono_left inter_subset_left) (h x y xs ys)

中文:
定理 LipschitzOnWith.comp_locallyBoundedVariationOn
  结论: {f : E -> F} {C : 实数>=0} {t : 集合 E}
  证明: fun x y xs ys =>
  hf.comp_boundedVariationOn (hg.mono_left inter_subset_left) (h x y xs ys)

Depends on / 依赖: comp_boundedVariationOn, hf.comp_boundedVariationOn, hg.mono_left, inter_subset_left, mono_left
-/
theorem LipschitzOnWith.comp_locallyBoundedVariationOn {f : E -> F} {C : Real>=0} {t : Set E}
    (hf : LipschitzOnWith C f t) {g : α -> E} {s : Set α} (hg : MapsTo g s t)
    (h : LocallyBoundedVariationOn g s) : LocallyBoundedVariationOn (f ∘ g) s :=
  fun x y xs ys =>
  hf.comp_boundedVariationOn (hg.mono_left inter_subset_left) (h x y xs ys)

/--
theorem `LipschitzWith.comp_boundedVariationOn` / 定理 `LipschitzWith.comp_boundedVariationOn`

English:
theorem LipschitzWith.comp_boundedVariationOn
  statement: {f : E -> F} {C : Real>=0} (hf : LipschitzWith C f)
  proof: hf.lipschitzOnWith.comp_boundedVariationOn (mapsTo_univ _ _) h

中文:
定理 LipschitzWith.comp_boundedVariationOn
  结论: {f : E -> F} {C : 实数>=0} (hf : LipschitzWith C f)
  证明: hf.lipschitzOnWith.comp_boundedVariationOn (mapsTo_univ _ _) h

Depends on / 依赖: comp_boundedVariationOn, hf.lipschitzOnWith.comp_boundedVariationOn, lipschitzOnWith, mapsTo_univ
-/
theorem LipschitzWith.comp_boundedVariationOn {f : E -> F} {C : Real>=0} (hf : LipschitzWith C f)
    {g : α -> E} {s : Set α} (h : BoundedVariationOn g s) : BoundedVariationOn (f ∘ g) s :=
  hf.lipschitzOnWith.comp_boundedVariationOn (mapsTo_univ _ _) h

/--
theorem `LipschitzWith.comp_locallyBoundedVariationOn` / 定理 `LipschitzWith.comp_locallyBoundedVariationOn`

English:
theorem LipschitzWith.comp_locallyBoundedVariationOn
  statement: {f : E -> F} {C : Real>=0}
  proof: hf.lipschitzOnWith.comp_locallyBoundedVariationOn (mapsTo_univ _ _) h

中文:
定理 LipschitzWith.comp_locallyBoundedVariationOn
  结论: {f : E -> F} {C : 实数>=0}
  证明: hf.lipschitzOnWith.comp_locallyBoundedVariationOn (mapsTo_univ _ _) h

Depends on / 依赖: comp_locallyBoundedVariationOn, hf.lipschitzOnWith.comp_locallyBoundedVariationOn, lipschitzOnWith, mapsTo_univ
-/
theorem LipschitzWith.comp_locallyBoundedVariationOn {f : E -> F} {C : Real>=0}
    (hf : LipschitzWith C f) {g : α -> E} {s : Set α} (h : LocallyBoundedVariationOn g s) :
    LocallyBoundedVariationOn (f ∘ g) s :=
  hf.lipschitzOnWith.comp_locallyBoundedVariationOn (mapsTo_univ _ _) h

/--
theorem `LipschitzOnWith.locallyBoundedVariationOn` / 定理 `LipschitzOnWith.locallyBoundedVariationOn`

English:
theorem LipschitzOnWith.locallyBoundedVariationOn
  statement: {f : Real -> E} {C : Real>=0} {s : Set Real}
  proof: hf.comp_locallyBoundedVariationOn (mapsTo_id _)
    (@monotoneOn_id Real _ s).locallyBoundedVariationOn

中文:
定理 LipschitzOnWith.locallyBoundedVariationOn
  结论: {f : 实数 -> E} {C : 实数>=0} {s : 集合 实数}
  证明: hf.comp_locallyBoundedVariationOn (mapsTo_id _)
    (@monotoneOn_id Real _ s).locallyBoundedVariationOn

Depends on / 依赖: comp_locallyBoundedVariationOn, hf.comp_locallyBoundedVariationOn, locallyBoundedVariationOn, mapsTo_id, monotoneOn_id
-/
theorem LipschitzOnWith.locallyBoundedVariationOn {f : Real -> E} {C : Real>=0} {s : Set Real}
    (hf : LipschitzOnWith C f s) : LocallyBoundedVariationOn f s :=
  hf.comp_locallyBoundedVariationOn (mapsTo_id _)
    (@monotoneOn_id Real _ s).locallyBoundedVariationOn

/--
theorem `LipschitzWith.locallyBoundedVariationOn` / 定理 `LipschitzWith.locallyBoundedVariationOn`

English:
theorem LipschitzWith.locallyBoundedVariationOn
  statement: {f : Real -> E} {C : Real>=0} (hf : LipschitzWith C f)
  proof: hf.lipschitzOnWith.locallyBoundedVariationOn

中文:
定理 LipschitzWith.locallyBoundedVariationOn
  结论: {f : 实数 -> E} {C : 实数>=0} (hf : LipschitzWith C f)
  证明: hf.lipschitzOnWith.locallyBoundedVariationOn

Depends on / 依赖: hf.lipschitzOnWith.locallyBoundedVariationOn, lipschitzOnWith, locallyBoundedVariationOn
-/
theorem LipschitzWith.locallyBoundedVariationOn {f : Real -> E} {C : Real>=0} (hf : LipschitzWith C f)
    (s : Set Real) : LocallyBoundedVariationOn f s :=
  hf.lipschitzOnWith.locallyBoundedVariationOn

end LipschitzOnWith
