/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Logic.Encodable.Pi
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.MeasurableSpace.Pi

/-!
# Indexed product measures

In this file we define and prove properties about finite products of measures
(and at some point, countable products of measures).

## Main definition

* `MeasureTheory.Measure.pi`: The product of finitely many σ-finite measures.
  Given `μ : (i : ι) → Measure (α i)` for `[Fintype ι]` it has type `Measure ((i : ι) → α i)`.

To apply Fubini's theorem or Tonelli's theorem along some subset, we recommend using the marginal
construction `MeasureTheory.lmarginal` and (todo) `MeasureTheory.marginal`. This allows you to
apply these theorems without any bookkeeping with measurable equivalences.

## Implementation Notes

We define `MeasureTheory.OuterMeasure.pi`, the product of finitely many outer measures, as the
maximal outer measure `n` with the property that `n (pi univ s) ≤ ∏ i, m i (s i)`,
where `pi univ s` is the product of the sets `{s i | i : ι}`.

We then show that this induces a product of measures, called `MeasureTheory.Measure.pi`.
For a collection of σ-finite measures `μ` and a collection of measurable sets `s` we show that
`Measure.pi μ (pi univ s) = ∏ i, m i (s i)`. To do this, we follow the following steps:
* We know that there is some ordering on `ι`, given by an element of `[Countable ι]`.
* Using this, we have an equivalence `MeasurableEquiv.piMeasurableEquivTProd` between
  `∀ i, α i` and an iterated product of `α i`, called `List.tprod α l` for some list `l`.
* On this iterated product we can easily define a product measure `MeasureTheory.Measure.tprod`
  by iterating `MeasureTheory.Measure.prod`
* Using the previous two steps we construct `MeasureTheory.Measure.pi'` on `(i : ι) → α i` for
  countable `ι`.
* We know that `MeasureTheory.Measure.pi'` sends products of sets to products of measures, and
  since `MeasureTheory.Measure.pi` is the maximal such measure (or at least, it comes from an outer
  measure which is the maximal such outer measure), we get the same rule for
  `MeasureTheory.Measure.pi`.

## Tags

finitary product measure

-/

@[expose] public section

noncomputable section

open Function Set MeasureTheory.OuterMeasure Filter MeasurableSpace Encodable

open scoped Topology ENNReal

universe u v

variable {ι ι' : Type*} {α : ι -> Type*}

namespace MeasureTheory

variable [Fintype ι] {m : forall i, OuterMeasure (α i)}

/--
Definition of `piPremeasure` / `piPremeasure` 的定义

English:
definition piPremeasure
  signature: (m : forall i, OuterMeasure (α i)) (s : Set (forall i, α i))
  body: ∏ i, m i (eval i '' s)

中文:
定义 piPremeasure
  签名: (m : 对任意 i, 外测度 (α i)) (s : 集合 (对任意 i, α i))
  定义体: ∏ i, m i (eval i '' s)
-/
def piPremeasure (m : forall i, OuterMeasure (α i)) (s : Set (forall i, α i)) : Real>=0∞ :=
  ∏ i, m i (eval i '' s)

/--
theorem `piPremeasure_pi` / 定理 `piPremeasure_pi`

English:
theorem piPremeasure_pi
  given: {s : forall i, Set (α i)} (hs : (pi univ s).Nonempty)
  proof: by simp [hs, piPremeasure]

中文:
定理 piPremeasure_pi
  条件: {s : 对任意 i, 集合 (α i)} (hs : (pi univ s).非空)
  证明: by simp [hs, piPremeasure]

Depends on / 依赖: piPremeasure
-/
theorem piPremeasure_pi {s : forall i, Set (α i)} (hs : (pi univ s).Nonempty) :
    piPremeasure m (pi univ s) = ∏ i, m i (s i) := by simp [hs, piPremeasure]

/--
theorem `piPremeasure_pi'` / 定理 `piPremeasure_pi'`

English:
theorem piPremeasure_pi'
  given: {s : forall i, Set (α i)}
  statement: piPremeasure m (pi univ s) = ∏ i, m i (s i)
  proof: by
  cases isEmpty_or_nonempty ι
  · simp [piPremeasure]
  rcases (pi univ s).eq_empty_or_nonempty with h | h
  · rcases univ_pi_eq_empty_iff.mp h with ⟨i, hi⟩
    have : exists i, m i (s i) = 0 := ⟨i, by simp [hi]⟩
    simpa [h, Finset.card_univ, zero_pow Fintype.card_ne_zero, @eq_comm _ (0 : Real>

中文:
定理 piPremeasure_pi'
  条件: {s : 对任意 i, 集合 (α i)}
  结论: piPremeasure m (pi univ s) = ∏ i, m i (s i)
  证明: by
  cases isEmpty_or_nonempty ι
  · simp [piPremeasure]
  rcases (pi univ s).eq_empty_or_nonempty with h | h
  · rcases univ_pi_eq_empty_iff.mp h with ⟨i, hi⟩
    have : exists i, m i (s i) = 0 := ⟨i, by simp [hi]⟩
    simpa [h, Finset.card_univ, zero_pow Fintype.card_ne_zero, @eq_comm _ (0 : Real>

Depends on / 依赖: Finset, Finset.card_univ, Finset.prod_eq_zero_iff, Fintype, Fintype.card_ne_zero, card_ne_zero, card_univ, eq_comm, eq_empty_or_nonempty, isEmpty_or_nonempty, piPremeasure, prod_eq_zero_iff, univ_pi_eq_empty_iff, univ_pi_eq_empty_iff.mp, zero_pow
-/
theorem piPremeasure_pi' {s : forall i, Set (α i)} : piPremeasure m (pi univ s) = ∏ i, m i (s i) := by
  cases isEmpty_or_nonempty ι
  · simp [piPremeasure]
  rcases (pi univ s).eq_empty_or_nonempty with h | h
  · rcases univ_pi_eq_empty_iff.mp h with ⟨i, hi⟩
    have : exists i, m i (s i) = 0 := ⟨i, by simp [hi]⟩
    simpa [h, Finset.card_univ, zero_pow Fintype.card_ne_zero, @eq_comm _ (0 : Real>=0∞),
      Finset.prod_eq_zero_iff, piPremeasure]
  · simp [h, piPremeasure]

/--
theorem `piPremeasure_pi_mono` / 定理 `piPremeasure_pi_mono`

English:
theorem piPremeasure_pi_mono
  given: {s t : Set (forall i, α i)} (h : s subseteq t)
  proof: Finset.prod_le_prod' fun _ _ => measure_mono (Set.image_mono h)

中文:
定理 piPremeasure_pi_mono
  条件: {s t : 集合 (对任意 i, α i)} (h : s subseteq t)
  证明: Finset.prod_le_prod' fun _ _ => measure_mono (Set.image_mono h)

Depends on / 依赖: Finset, Finset.prod_le_prod, Set.image_mono, image_mono, measure_mono, prod_le_prod
-/
theorem piPremeasure_pi_mono {s t : Set (forall i, α i)} (h : s subseteq t) :
    piPremeasure m s <= piPremeasure m t :=
  Finset.prod_le_prod' fun _ _ => measure_mono (Set.image_mono h)

/--
theorem `piPremeasure_pi_eval` / 定理 `piPremeasure_pi_eval`

English:
theorem piPremeasure_pi_eval
  given: {s : Set (forall i, α i)}
  proof: by
  simp only [eval, piPremeasure_pi']; rfl

中文:
定理 piPremeasure_pi_eval
  条件: {s : 集合 (对任意 i, α i)}
  证明: by
  simp only [eval, piPremeasure_pi']; rfl

Depends on / 依赖: piPremeasure_pi
-/
theorem piPremeasure_pi_eval {s : Set (forall i, α i)} :
    piPremeasure m (pi univ fun i => eval i '' s) = piPremeasure m s := by
  simp only [eval, piPremeasure_pi']; rfl

namespace OuterMeasure

/--
Definition of `pi` / `pi` 的定义

English:
definition pi
  signature: (m : forall i, OuterMeasure (α i))
  body: boundedBy (piPremeasure m)

中文:
定义 pi
  签名: (m : 对任意 i, 外测度 (α i))
  定义体: boundedBy (piPremeasure m)
-/
protected def pi (m : forall i, OuterMeasure (α i)) : OuterMeasure (forall i, α i) :=
  boundedBy (piPremeasure m)

/--
theorem `pi_pi_le` / 定理 `pi_pi_le`

English:
theorem pi_pi_le
  given: (m : forall i, OuterMeasure (α i)) (s : forall i, Set (α i))
  proof: by
  rcases (pi univ s).eq_empty_or_nonempty with h | h
  · simp [h]
  exact (boundedBy_le _).trans_eq (piPremeasure_pi h)

中文:
定理 pi_pi_le
  条件: (m : 对任意 i, 外测度 (α i)) (s : 对任意 i, 集合 (α i))
  证明: by
  rcases (pi univ s).eq_empty_or_nonempty with h | h
  · simp [h]
  exact (boundedBy_le _).trans_eq (piPremeasure_pi h)

Depends on / 依赖: boundedBy_le, eq_empty_or_nonempty, piPremeasure_pi, trans_eq
-/
theorem pi_pi_le (m : forall i, OuterMeasure (α i)) (s : forall i, Set (α i)) :
    OuterMeasure.pi m (pi univ s) <= ∏ i, m i (s i) := by
  rcases (pi univ s).eq_empty_or_nonempty with h | h
  · simp [h]
  exact (boundedBy_le _).trans_eq (piPremeasure_pi h)

/--
theorem `le_pi` / 定理 `le_pi`

English:
theorem le_pi
  given: {m : forall i, OuterMeasure (α i)} {n : OuterMeasure (forall i, α i)}
  proof: by
  rw [OuterMeasure.pi]; rw [le_boundedBy']; constructor
  · intro h s hs; refine (h _ hs).trans_eq (piPremeasure_pi hs)
  · intro h s hs; refine le_trans (n.mono <| subset_pi_eval_image univ s) (h _ ?_)
    simp [univ_pi_nonempty_iff, hs]

中文:
定理 le_pi
  条件: {m : 对任意 i, 外测度 (α i)} {n : 外测度 (对任意 i, α i)}
  证明: by
  rw [OuterMeasure.pi]; rw [le_boundedBy']; constructor
  · intro h s hs; refine (h _ hs).trans_eq (piPremeasure_pi hs)
  · intro h s hs; refine le_trans (n.mono <| subset_pi_eval_image univ s) (h _ ?_)
    simp [univ_pi_nonempty_iff, hs]

Depends on / 依赖: OuterMeasure, OuterMeasure.pi, le_boundedBy, le_trans, n.mono, piPremeasure_pi, subset_pi_eval_image, trans_eq, univ_pi_nonempty_iff
-/
theorem le_pi {m : forall i, OuterMeasure (α i)} {n : OuterMeasure (forall i, α i)} :
    n <= OuterMeasure.pi m ↔
      forall s : forall i, Set (α i), (pi univ s).Nonempty -> n (pi univ s) <= ∏ i, m i (s i) := by
  rw [OuterMeasure.pi]; rw [le_boundedBy']; constructor
  · intro h s hs; refine (h _ hs).trans_eq (piPremeasure_pi hs)
  · intro h s hs; refine le_trans (n.mono <| subset_pi_eval_image univ s) (h _ ?_)
    simp [univ_pi_nonempty_iff, hs]

end OuterMeasure

namespace Measure

variable [forall i, MeasurableSpace (α i)] (μ : forall i, Measure (α i))

section Tprod

open List

variable {δ : Type*} {X : δ -> Type*} [forall i, MeasurableSpace (X i)]

-- for some reason the equation compiler doesn't like this definition
/--
Definition of `tprod` / `tprod` 的定义

English:
definition tprod
  signature: (l : List δ) (μ : forall i, Measure (X i))
  body: by
  induction l with
  | nil => exact dirac PUnit.unit
  | cons i l ih => exact (μ i).prod (α := X i) ih

@[simp]

中文:
定义 tprod
  签名: (l : 列表 δ) (μ : 对任意 i, 测度 (X i))
  定义体: by
  induction l with
  | nil => exact dirac PUnit.unit
  | cons i l ih => exact (μ i).prod (α := X i) ih

@[simp]
-/
protected def tprod (l : List δ) (μ : forall i, Measure (X i)) : Measure (TProd X l) := by
  induction l with
  | nil => exact dirac PUnit.unit
  | cons i l ih => exact (μ i).prod (α := X i) ih

@[simp]
/--
theorem `tprod_nil` / 定理 `tprod_nil`

English:
theorem tprod_nil
  given: (μ : forall i, Measure (X i))
  statement: Measure.tprod [] μ = dirac PUnit.unit
  proof: rfl

@[simp]

中文:
定理 tprod_nil
  条件: (μ : 对任意 i, 测度 (X i))
  结论: 测度.tprod [] μ = dirac 命题单元.unit
  证明: rfl

@[simp]
-/
theorem tprod_nil (μ : forall i, Measure (X i)) : Measure.tprod [] μ = dirac PUnit.unit :=
  rfl

@[simp]
/--
theorem `tprod_cons` / 定理 `tprod_cons`

English:
theorem tprod_cons
  given: (i : δ) (l : List δ) (μ : forall i, Measure (X i))
  proof: rfl

中文:
定理 tprod_cons
  条件: (i : δ) (l : 列表 δ) (μ : 对任意 i, 测度 (X i))
  证明: rfl
-/
theorem tprod_cons (i : δ) (l : List δ) (μ : forall i, Measure (X i)) :
    Measure.tprod (i :: l) μ = (μ i).prod (Measure.tprod l μ) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
Instance `sigmaFinite_tprod` / 实例 `sigmaFinite_tprod`

English:
instance sigmaFinite_tprod
  signature: (l : List δ) (μ : forall i, Measure (X i)) [forall i, SigmaFinite (μ i)]
  body: by
  induction l with
  | nil => rw [tprod_nil]; infer_instance
  | cons i l ih => rw [tprod_cons]; exact @prod.instSigmaFinite _ _ _ _ _ _ _ ih

中文:
实例 sigmaFinite_tprod
  签名: (l : 列表 δ) (μ : 对任意 i, 测度 (X i)) [对任意 i, σ有限 (μ i)]
  定义体: by
  induction l with
  | nil => rw [tprod_nil]; infer_instance
  | cons i l ih => rw [tprod_cons]; exact @prod.instSigmaFinite _ _ _ _ _ _ _ ih

Depends on / 依赖: infer_instance, instSigmaFinite, prod.instSigmaFinite, tprod_cons, tprod_nil
-/
instance sigmaFinite_tprod (l : List δ) (μ : forall i, Measure (X i)) [forall i, SigmaFinite (μ i)] :
    SigmaFinite (Measure.tprod l μ) := by
  induction l with
  | nil => rw [tprod_nil]; infer_instance
  | cons i l ih => rw [tprod_cons]; exact @prod.instSigmaFinite _ _ _ _ _ _ _ ih

set_option backward.isDefEq.respectTransparency false in
/--
theorem `tprod_tprod` / 定理 `tprod_tprod`

English:
theorem tprod_tprod
  statement: (l : List δ) (μ : forall i, Measure (X i)) [forall i, SigmaFinite (μ i)]
  proof: by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [tprod_cons]; rw [Set.tprod]
    simp only [foldr_cons, prod_cons, map_cons]
    rw [prod_prod]; rw [ih]

中文:
定理 tprod_tprod
  结论: (l : 列表 δ) (μ : 对任意 i, 测度 (X i)) [对任意 i, σ有限 (μ i)]
  证明: by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [tprod_cons]; rw [Set.tprod]
    simp only [foldr_cons, prod_cons, map_cons]
    rw [prod_prod]; rw [ih]

Depends on / 依赖: Set.tprod, foldr_cons, map_cons, prod_cons, prod_prod, tprod_cons
-/
theorem tprod_tprod (l : List δ) (μ : forall i, Measure (X i)) [forall i, SigmaFinite (μ i)]
    (s : forall i, Set (X i)) :
    Measure.tprod l μ (Set.tprod l s) = (l.map fun i => (μ i) (s i)).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [tprod_cons]; rw [Set.tprod]
    simp only [foldr_cons, prod_cons, map_cons]
    rw [prod_prod]; rw [ih]

end Tprod

section Encodable

open List

variable [Encodable ι]

open scoped Classical in
/--
Definition of `pi'` / `pi'` 的定义

English:
definition pi'
  signature: : Measure (forall i, α i)
  body: Measure.map (TProd.elim' mem_sortedUniv) (Measure.tprod (sortedUniv ι) μ)

中文:
定义 pi'
  签名: : 测度 (对任意 i, α i)
  定义体: Measure.map (TProd.elim' mem_sortedUniv) (Measure.tprod (sortedUniv ι) μ)

Depends on / 依赖: Measure, Measure.map, Measure.tprod, TProd.elim, mem_sortedUniv, sortedUniv
-/
def pi' : Measure (forall i, α i) :=
  Measure.map (TProd.elim' mem_sortedUniv) (Measure.tprod (sortedUniv ι) μ)

/--
theorem `pi'_pi` / 定理 `pi'_pi`

English:
theorem pi'_pi
  given: [forall i, SigmaFinite (μ i)] (s : forall i, Set (α i))
  proof: by
  classical
  rw [pi']
  rw [← MeasurableEquiv.piMeasurableEquivTProd_symm_apply]; rw [MeasurableEquiv.map_apply]; rw [MeasurableEquiv.piMeasurableEquivTProd_symm_apply]; rw [elim_preimage_pi]; rw [tprod_tprod _ μ]; rw [←
    List.prod_toFinset]; rw [sortedUniv_toFinset] <;>
  exact sortedUniv_no

中文:
定理 pi'_pi
  条件: [对任意 i, σ有限 (μ i)] (s : 对任意 i, 集合 (α i))
  证明: by
  classical
  rw [pi']
  rw [← MeasurableEquiv.piMeasurableEquivTProd_symm_apply]; rw [MeasurableEquiv.map_apply]; rw [MeasurableEquiv.piMeasurableEquivTProd_symm_apply]; rw [elim_preimage_pi]; rw [tprod_tprod _ μ]; rw [←
    List.prod_toFinset]; rw [sortedUniv_toFinset] <;>
  exact sortedUniv_no
-/
theorem pi'_pi [forall i, SigmaFinite (μ i)] (s : forall i, Set (α i)) :
    pi' μ (pi univ s) = ∏ i, μ i (s i) := by
  classical
  rw [pi']
  rw [← MeasurableEquiv.piMeasurableEquivTProd_symm_apply]; rw [MeasurableEquiv.map_apply]; rw [MeasurableEquiv.piMeasurableEquivTProd_symm_apply]; rw [elim_preimage_pi]; rw [tprod_tprod _ μ]; rw [←
    List.prod_toFinset]; rw [sortedUniv_toFinset] <;>
  exact sortedUniv_nodup ι

end Encodable

/--
theorem `pi_caratheodory` / 定理 `pi_caratheodory`

English:
theorem pi_caratheodory
  proof: by
  refine iSup_le ?_
  intro i s hs
  rw [MeasurableSpace.comap] at hs
  rcases hs with ⟨s, hs, rfl⟩
  apply boundedBy_caratheodory
  intro t
  simp_rw [piPremeasure]
  refine Finset.prod_add_prod_le' (Finset.mem_univ i) ?_ ?_ ?_
  · simp [image_inter_preimage, image_sdiff_preimage, measure_inter_

中文:
定理 pi_caratheodory
  证明: by
  refine iSup_le ?_
  intro i s hs
  rw [MeasurableSpace.comap] at hs
  rcases hs with ⟨s, hs, rfl⟩
  apply boundedBy_caratheodory
  intro t
  simp_rw [piPremeasure]
  refine Finset.prod_add_prod_le' (Finset.mem_univ i) ?_ ?_ ?_
  · simp [image_inter_preimage, image_sdiff_preimage, measure_inter_

Depends on / 依赖: Finset, Finset.mem_univ, Finset.prod_add_prod_le, MeasurableSpace, MeasurableSpace.comap, boundedBy_caratheodory, iSup_le, image_inter_preimage, image_sdiff_preimage, inter_subset_left, measure_inter_add_sdiff, mem_univ, piPremeasure, prod_add_prod_le, sdiff_subset, simp_rw
-/
theorem pi_caratheodory :
    MeasurableSpace.pi <= (OuterMeasure.pi fun i => (μ i).toOuterMeasure).caratheodory := by
  refine iSup_le ?_
  intro i s hs
  rw [MeasurableSpace.comap] at hs
  rcases hs with ⟨s, hs, rfl⟩
  apply boundedBy_caratheodory
  intro t
  simp_rw [piPremeasure]
  refine Finset.prod_add_prod_le' (Finset.mem_univ i) ?_ ?_ ?_
  · simp [image_inter_preimage, image_sdiff_preimage, measure_inter_add_sdiff _ hs]
  · rintro j - _; gcongr; apply inter_subset_left
  · rintro j - _; gcongr; apply sdiff_subset

/-- `Measure.pi μ` is the finite product of the measures `{μ i | i : ι}`.
  It is defined to be measure corresponding to `MeasureTheory.OuterMeasure.pi`. -/
protected irreducible_def pi : Measure (forall i, α i) :=
  toMeasure (OuterMeasure.pi fun i => (μ i).toOuterMeasure) (pi_caratheodory μ)

/--
Instance `_root_.MeasureTheory.MeasureSpace.pi` / 实例 `_root_.MeasureTheory.MeasureSpace.pi`

English:
instance _root_.MeasureTheory.MeasureSpace.pi
  signature: {α : ι -> Type*} [forall i, MeasureSpace (α i)]
  body: ⟨Measure.pi fun _ => volume⟩

中文:
实例 _root_.测度论.测度空间.pi
  签名: {α : ι -> 类型} [对任意 i, 测度空间 (α i)]
  定义体: ⟨Measure.pi fun _ => volume⟩

Depends on / 依赖: Measure, Measure.pi, volume
-/
instance _root_.MeasureTheory.MeasureSpace.pi {α : ι -> Type*} [forall i, MeasureSpace (α i)] :
    MeasureSpace (forall i, α i) :=
  ⟨Measure.pi fun _ => volume⟩

/--
theorem `pi_pi_aux` / 定理 `pi_pi_aux`

English:
theorem pi_pi_aux
  given: [forall i, SigmaFinite (μ i)] (s : forall i, Set (α i)) (hs : forall i, MeasurableSet (s i))
  proof: by
  refine le_antisymm ?_ ?_
  · rw [Measure.pi, toMeasure_apply _ _ (MeasurableSet.pi countable_univ fun i _ => hs i)]
    apply OuterMeasure.pi_pi_le
  · have : Encodable ι := Fintype.toEncodable ι
    simp_rw [← pi'_pi μ s, Measure.pi,
      toMeasure_apply _ _ (MeasurableSet.pi countable_univ f

中文:
定理 pi_pi_aux
  条件: [对任意 i, σ有限 (μ i)] (s : 对任意 i, 集合 (α i)) (hs : 对任意 i, 可测集 (s i))
  证明: by
  refine le_antisymm ?_ ?_
  · rw [Measure.pi, toMeasure_apply _ _ (MeasurableSet.pi countable_univ fun i _ => hs i)]
    apply OuterMeasure.pi_pi_le
  · have : Encodable ι := Fintype.toEncodable ι
    simp_rw [← pi'_pi μ s, Measure.pi,
      toMeasure_apply _ _ (MeasurableSet.pi countable_univ f

Depends on / 依赖: Encodable, Fintype, Fintype.toEncodable, MeasurableSet, MeasurableSet.pi, Measure, Measure.pi, OuterMeasure, OuterMeasure.le_pi, OuterMeasure.pi, OuterMeasure.pi_pi_le, countable_univ, le_antisymm, le_pi, pi_pi_le, simp_rw, toEncodable, toMeasure_apply, toOuterMeasure
-/
theorem pi_pi_aux [forall i, SigmaFinite (μ i)] (s : forall i, Set (α i)) (hs : forall i, MeasurableSet (s i)) :
    Measure.pi μ (pi univ s) = ∏ i, μ i (s i) := by
  refine le_antisymm ?_ ?_
  · rw [Measure.pi, toMeasure_apply _ _ (MeasurableSet.pi countable_univ fun i _ => hs i)]
    apply OuterMeasure.pi_pi_le
  · have : Encodable ι := Fintype.toEncodable ι
    simp_rw [← pi'_pi μ s, Measure.pi,
      toMeasure_apply _ _ (MeasurableSet.pi countable_univ fun i _ => hs i)]
    suffices (pi' μ).toOuterMeasure <= OuterMeasure.pi fun i => (μ i).toOuterMeasure by exact this _
    clear hs s
    rw [OuterMeasure.le_pi]
    intro s _
    exact (pi'_pi μ s).le

variable {μ}

/--
Definition of `FiniteSpanningSetsIn.pi` / `FiniteSpanningSetsIn.pi` 的定义

English:
definition FiniteSpanningSetsIn.pi
  signature: {C : forall i, Set (Set (α i))}
  body: by
  haveI := fun i => (hμ i).sigmaFinite
  haveI := Fintype.toEncodable ι
  refine ⟨fun n => Set.pi univ fun i => (hμ i).set ((@decode (ι -> Nat) _ n).getD default i),
    fun n => ?_, fun n => ?_, ?_⟩ <;>
  -- TODO (kmill) If this let comes before the refine, while the noncomputability checker
  -

中文:
定义 FiniteSpanningSetsIn.pi
  签名: {C : 对任意 i, 集合 (集合 (α i))}
  定义体: by
  haveI := fun i => (hμ i).sigmaFinite
  haveI := Fintype.toEncodable ι
  refine ⟨fun n => Set.pi univ fun i => (hμ i).set ((@decode (ι -> Nat) _ n).getD default i),
    fun n => ?_, fun n => ?_, ?_⟩ <;>
  -- TODO (kmill) If this let comes before the refine, while the noncomputability checker
  -

Depends on / 依赖: Fintype, Fintype.toEncodable, Set.pi, decode, sigmaFinite, toEncodable
-/
def FiniteSpanningSetsIn.pi {C : forall i, Set (Set (α i))}
    (hμ : forall i, (μ i).FiniteSpanningSetsIn (C i)) :
    (Measure.pi μ).FiniteSpanningSetsIn (pi univ '' pi univ C) := by
  haveI := fun i => (hμ i).sigmaFinite
  haveI := Fintype.toEncodable ι
  refine ⟨fun n => Set.pi univ fun i => (hμ i).set ((@decode (ι -> Nat) _ n).getD default i),
    fun n => ?_, fun n => ?_, ?_⟩ <;>
  -- TODO (kmill) If this let comes before the refine, while the noncomputability checker
  -- correctly sees this definition is computable, the Lean VM fails to see the binding is
  -- computationally irrelevant. The `noncomputable section` doesn't help because all it does
  -- is insert `noncomputable` for you when necessary.
  let e : Nat -> ι -> Nat := fun n => (@decode (ι -> Nat) _ n).getD default
  · refine mem_image_of_mem _ fun i _ => (hμ i).set_mem _
  · calc
      Measure.pi μ (Set.pi univ fun i => (hμ i).set (e n i)) <=
          Measure.pi μ (Set.pi univ fun i => toMeasurable (μ i) ((hμ i).set (e n i))) :=
        measure_mono (pi_mono fun i _ => subset_toMeasurable _ _)
      _ = ∏ i, μ i (toMeasurable (μ i) ((hμ i).set (e n i))) :=
        (pi_pi_aux μ _ fun i => measurableSet_toMeasurable _ _)
      _ = ∏ i, μ i ((hμ i).set (e n i)) := by simp only [measure_toMeasurable]
      _ < ∞ := ENNReal.prod_lt_top fun i _ => (hμ i).finite _
  · simp_rw [(surjective_decode_getD (ι -> Nat) default).iUnion_comp fun x =>
        Set.pi univ fun i => (hμ i).set (x i),
      iUnion_univ_pi fun i => (hμ i).set, (hμ _).spanning, Set.pi_univ]

/--
theorem `pi_eq_generateFrom` / 定理 `pi_eq_generateFrom`

English:
theorem pi_eq_generateFrom
  statement: {C : forall i, Set (Set (α i))}
  proof: by
  have h4C : forall (i) (s : Set (α i)), s in C i -> MeasurableSet s := by
    intro i s hs; rw [← hC]; exact measurableSet_generateFrom hs
  refine
    (FiniteSpanningSetsIn.pi h3C).ext
      (generateFrom_eq_pi hC fun i => (h3C i).isCountablySpanning).symm (IsPiSystem.pi h2C) ?_
  rintro _ ⟨s, 

中文:
定理 pi_eq_generateFrom
  结论: {C : 对任意 i, 集合 (集合 (α i))}
  证明: by
  have h4C : forall (i) (s : Set (α i)), s in C i -> MeasurableSet s := by
    intro i s hs; rw [← hC]; exact measurableSet_generateFrom hs
  refine
    (FiniteSpanningSetsIn.pi h3C).ext
      (generateFrom_eq_pi hC fun i => (h3C i).isCountablySpanning).symm (IsPiSystem.pi h2C) ?_
  rintro _ ⟨s, 

Depends on / 依赖: FiniteSpanningSetsIn, FiniteSpanningSetsIn.pi, IsPiSystem, IsPiSystem.pi, MeasurableSet, generateFrom_eq_pi, isCountablySpanning, measurableSet_generateFrom, mem_univ_pi, pi_pi_aux, sigmaFinite, simp_rw
-/
theorem pi_eq_generateFrom {C : forall i, Set (Set (α i))}
    (hC : forall i, generateFrom (C i) = by apply_assumption) (h2C : forall i, IsPiSystem (C i))
    (h3C : forall i, (μ i).FiniteSpanningSetsIn (C i)) {μν : Measure (forall i, α i)}
    (h₁ : forall s : forall i, Set (α i), (forall i, s i in C i) -> μν (pi univ s) = ∏ i, μ i (s i)) :
    Measure.pi μ = μν := by
  have h4C : forall (i) (s : Set (α i)), s in C i -> MeasurableSet s := by
    intro i s hs; rw [← hC]; exact measurableSet_generateFrom hs
  refine
    (FiniteSpanningSetsIn.pi h3C).ext
      (generateFrom_eq_pi hC fun i => (h3C i).isCountablySpanning).symm (IsPiSystem.pi h2C) ?_
  rintro _ ⟨s, hs, rfl⟩
  rw [mem_univ_pi] at hs
  have := fun i => (h3C i).sigmaFinite
  simp_rw [h₁ s hs, pi_pi_aux μ s fun i => h4C i _ (hs i)]

/--
theorem `pi_eq` / 定理 `pi_eq`

English:
theorem pi_eq
  statement: [forall i, SigmaFinite (μ i)] {μ' : Measure (forall i, α i)}
  proof: pi_eq_generateFrom (fun _ => generateFrom_measurableSet) (fun _ => isPiSystem_measurableSet)
    (fun i => (μ i).toFiniteSpanningSetsIn) h

中文:
定理 pi_eq
  结论: [对任意 i, σ有限 (μ i)] {μ' : 测度 (对任意 i, α i)}
  证明: pi_eq_generateFrom (fun _ => generateFrom_measurableSet) (fun _ => isPiSystem_measurableSet)
    (fun i => (μ i).toFiniteSpanningSetsIn) h

Depends on / 依赖: generateFrom_measurableSet, isPiSystem_measurableSet, pi_eq_generateFrom, toFiniteSpanningSetsIn
-/
theorem pi_eq [forall i, SigmaFinite (μ i)] {μ' : Measure (forall i, α i)}
    (h : forall s : forall i, Set (α i), (forall i, MeasurableSet (s i)) -> μ' (pi univ s) = ∏ i, μ i (s i)) :
    Measure.pi μ = μ' :=
  pi_eq_generateFrom (fun _ => generateFrom_measurableSet) (fun _ => isPiSystem_measurableSet)
    (fun i => (μ i).toFiniteSpanningSetsIn) h

variable (μ)

/--
theorem `pi'_eq_pi` / 定理 `pi'_eq_pi`

English:
theorem pi'_eq_pi
  given: [Encodable ι] [forall i, SigmaFinite (μ i)]
  statement: pi' μ = Measure.pi μ
  proof: Eq.symm pi_eq fun s _ => pi'_pi μ s

@[simp]

中文:
定理 pi'_eq_pi
  条件: [可编码 ι] [对任意 i, σ有限 (μ i)]
  结论: pi' μ = 测度.pi μ
  证明: Eq.symm pi_eq fun s _ => pi'_pi μ s

@[simp]
-/
theorem pi'_eq_pi [Encodable ι] [forall i, SigmaFinite (μ i)] : pi' μ = Measure.pi μ :=
Eq.symm pi_eq fun s _ => pi'_pi μ s

@[simp]
/--
theorem `pi_pi` / 定理 `pi_pi`

English:
theorem pi_pi
  given: [forall i, SigmaFinite (μ i)] (s : (i : ι) -> Set (α i))
  proof: by
  have : Encodable ι := Fintype.toEncodable ι
  rw [← pi'_eq_pi]; rw [pi'_pi]

nonrec theorem pi_univ [forall i, SigmaFinite (μ i)] : Measure.pi μ univ = ∏ i, μ i univ := by
  rw [← pi_univ]; rw [pi_pi μ]

中文:
定理 pi_pi
  条件: [对任意 i, σ有限 (μ i)] (s : (i : ι) -> 集合 (α i))
  证明: by
  have : Encodable ι := Fintype.toEncodable ι
  rw [← pi'_eq_pi]; rw [pi'_pi]

nonrec theorem pi_univ [forall i, SigmaFinite (μ i)] : Measure.pi μ univ = ∏ i, μ i univ := by
  rw [← pi_univ]; rw [pi_pi μ]

Depends on / 依赖: Encodable, Fintype, Fintype.toEncodable, _eq_pi, toEncodable
-/
theorem pi_pi [forall i, SigmaFinite (μ i)] (s : (i : ι) -> Set (α i)) :
    Measure.pi μ (pi univ s) = ∏ i, μ i (s i) := by
  have : Encodable ι := Fintype.toEncodable ι
  rw [← pi'_eq_pi]; rw [pi'_pi]

nonrec theorem pi_univ [forall i, SigmaFinite (μ i)] : Measure.pi μ univ = ∏ i, μ i univ := by
  rw [← pi_univ]; rw [pi_pi μ]

/--
lemma `pi_singleton` / 引理 `pi_singleton`

English:
lemma pi_singleton
  given: [forall i, SigmaFinite (μ i)] (f : forall i, α i)
  proof: by
  simpa [Set.univ_pi_singleton, -pi_pi] using pi_pi μ fun i => {f i}

中文:
引理 pi_singleton
  条件: [对任意 i, σ有限 (μ i)] (f : 对任意 i, α i)
  证明: by
  simpa [Set.univ_pi_singleton, -pi_pi] using pi_pi μ fun i => {f i}
-/
@[simp] lemma pi_singleton [forall i, SigmaFinite (μ i)] (f : forall i, α i) :
    Measure.pi μ {f} = ∏ i, μ i {f i} := by
  simpa [Set.univ_pi_singleton, -pi_pi] using pi_pi μ fun i => {f i}

/--
Instance `pi.instIsFiniteMeasure` / 实例 `pi.instIsFiniteMeasure`

English:
instance pi.instIsFiniteMeasure
  signature: [forall i, IsFiniteMeasure (μ i)]
  body: ⟨Measure.pi_univ μ ▸ ENNReal.prod_lt_top (fun i _ => measure_lt_top (μ i) _)⟩

中文:
实例 pi.instIsFiniteMeasure
  签名: [对任意 i, 是有限测度 (μ i)]
  定义体: ⟨Measure.pi_univ μ ▸ ENNReal.prod_lt_top (fun i _ => measure_lt_top (μ i) _)⟩

Depends on / 依赖: ENNReal, ENNReal.prod_lt_top, Measure, Measure.pi_univ, measure_lt_top, pi_univ, prod_lt_top
-/
instance pi.instIsFiniteMeasure [forall i, IsFiniteMeasure (μ i)] :
    IsFiniteMeasure (Measure.pi μ) :=
  ⟨Measure.pi_univ μ ▸ ENNReal.prod_lt_top (fun i _ => measure_lt_top (μ i) _)⟩

instance {α : ι -> Type*} [forall i, MeasureSpace (α i)] [forall i, IsFiniteMeasure (volume : Measure (α i))] :
    IsFiniteMeasure (volume : Measure (forall i, α i)) :=
  pi.instIsFiniteMeasure _

/--
Instance `pi.instIsProbabilityMeasure` / 实例 `pi.instIsProbabilityMeasure`

English:
instance pi.instIsProbabilityMeasure
  signature: [forall i, IsProbabilityMeasure (μ i)]
  body: ⟨by simp only [Measure.pi_univ, measure_univ, Finset.prod_const_one]⟩

@[simp]

中文:
实例 pi.instIsProbabilityMeasure
  签名: [对任意 i, 是概率测度 (μ i)]
  定义体: ⟨by simp only [Measure.pi_univ, measure_univ, Finset.prod_const_one]⟩

@[simp]

Depends on / 依赖: Finset, Finset.prod_const_one, Measure, Measure.pi_univ, measure_univ, pi_univ, prod_const_one
-/
instance pi.instIsProbabilityMeasure [forall i, IsProbabilityMeasure (μ i)] :
    IsProbabilityMeasure (Measure.pi μ) :=
  ⟨by simp only [Measure.pi_univ, measure_univ, Finset.prod_const_one]⟩

@[simp]
/--
theorem `pi_pi_finset` / 定理 `pi_pi_finset`

English:
theorem pi_pi_finset
  given: [forall i, IsProbabilityMeasure (μ i)] (f : (i : ι) -> Set (α i)) (s : Finset ι)
  proof: by
  classical simp [← Set.univ_pi_ite, pi_pi, apply_ite]

中文:
定理 pi_pi_finset
  条件: [对任意 i, 是概率测度 (μ i)] (f : (i : ι) -> 集合 (α i)) (s : 有限集 ι)
  证明: by
  classical simp [← Set.univ_pi_ite, pi_pi, apply_ite]

Depends on / 依赖: Set.univ_pi_ite, apply_ite, classical, pi_pi, univ_pi_ite
-/
theorem pi_pi_finset [forall i, IsProbabilityMeasure (μ i)] (f : (i : ι) -> Set (α i)) (s : Finset ι) :
    Measure.pi μ ((s : Set ι).pi f) = ∏ i in s, μ i (f i) := by
  classical simp [← Set.univ_pi_ite, pi_pi, apply_ite]

instance {α : ι -> Type*} [forall i, MeasureSpace (α i)]
    [forall i, IsProbabilityMeasure (volume : Measure (α i))] :
    IsProbabilityMeasure (volume : Measure (forall i, α i)) :=
  pi.instIsProbabilityMeasure _

variable [forall i, SigmaFinite (μ i)]

/--
theorem `pi_ball` / 定理 `pi_ball`

English:
theorem pi_ball
  given: [forall i, MetricSpace (α i)] (x : forall i, α i) {r : Real} (hr : 0 < r)
  proof: by rw [ball_pi _ hr, pi_pi]

中文:
定理 pi_ball
  条件: [对任意 i, 度量空间 (α i)] (x : 对任意 i, α i) {r : 实数} (hr : 0 < r)
  证明: by rw [ball_pi _ hr, pi_pi]

Depends on / 依赖: ball_pi, pi_pi
-/
theorem pi_ball [forall i, MetricSpace (α i)] (x : forall i, α i) {r : Real} (hr : 0 < r) :
    Measure.pi μ (Metric.ball x r) = ∏ i, μ i (Metric.ball (x i) r) := by rw [ball_pi _ hr, pi_pi]

/--
theorem `pi_closedBall` / 定理 `pi_closedBall`

English:
theorem pi_closedBall
  given: [forall i, MetricSpace (α i)] (x : forall i, α i) {r : Real} (hr : 0 <= r)
  proof: by
  rw [closedBall_pi _ hr]; rw [pi_pi]

中文:
定理 pi_closedBall
  条件: [对任意 i, 度量空间 (α i)] (x : 对任意 i, α i) {r : 实数} (hr : 0 <= r)
  证明: by
  rw [closedBall_pi _ hr]; rw [pi_pi]

Depends on / 依赖: closedBall_pi, pi_pi
-/
theorem pi_closedBall [forall i, MetricSpace (α i)] (x : forall i, α i) {r : Real} (hr : 0 <= r) :
    Measure.pi μ (Metric.closedBall x r) = ∏ i, μ i (Metric.closedBall (x i) r) := by
  rw [closedBall_pi _ hr]; rw [pi_pi]

/--
Instance `pi.sigmaFinite` / 实例 `pi.sigmaFinite`

English:
instance pi.sigmaFinite
  signature: : SigmaFinite (Measure.pi μ)
  body: (FiniteSpanningSetsIn.pi fun i => (μ i).toFiniteSpanningSetsIn).sigmaFinite

中文:
实例 pi.sigmaFinite
  签名: : σ有限 (测度.pi μ)
  定义体: (FiniteSpanningSetsIn.pi fun i => (μ i).toFiniteSpanningSetsIn).sigmaFinite

Depends on / 依赖: FiniteSpanningSetsIn, FiniteSpanningSetsIn.pi, sigmaFinite, toFiniteSpanningSetsIn
-/
instance pi.sigmaFinite : SigmaFinite (Measure.pi μ) :=
  (FiniteSpanningSetsIn.pi fun i => (μ i).toFiniteSpanningSetsIn).sigmaFinite

instance {α : ι -> Type*} [forall i, MeasureSpace (α i)] [forall i, SigmaFinite (volume : Measure (α i))] :
    SigmaFinite (volume : Measure (forall i, α i)) :=
  pi.sigmaFinite _

/--
theorem `pi_of_empty` / 定理 `pi_of_empty`

English:
theorem pi_of_empty
  statement: {α : Type*} [Fintype α] [IsEmpty α] {β : α -> Type*}
  proof: by
  have : forall a, SigmaFinite (μ a) := isEmptyElim
  refine pi_eq fun s _ => ?_
  rw [Fintype.prod_empty]; rw [dirac_apply_of_mem]
  exact isEmptyElim (α := α)

中文:
定理 pi_of_empty
  结论: {α : 类型} [有限类型 α] [是空 α] {β : α -> 类型}
  证明: by
  have : forall a, SigmaFinite (μ a) := isEmptyElim
  refine pi_eq fun s _ => ?_
  rw [Fintype.prod_empty]; rw [dirac_apply_of_mem]
  exact isEmptyElim (α := α)

Depends on / 依赖: isEmptyElim
-/
theorem pi_of_empty {α : Type*} [Fintype α] [IsEmpty α] {β : α -> Type*}
    {m : forall a, MeasurableSpace (β a)} (μ : forall a : α, Measure (β a)) (x : forall a, β a := isEmptyElim) :
    Measure.pi μ = dirac x := by
  have : forall a, SigmaFinite (μ a) := isEmptyElim
  refine pi_eq fun s _ => ?_
  rw [Fintype.prod_empty]; rw [dirac_apply_of_mem]
  exact isEmptyElim (α := α)

/--
lemma `volume_pi_eq_dirac` / 引理 `volume_pi_eq_dirac`

English:
lemma volume_pi_eq_dirac
  statement: {ι : Type*} [Fintype ι] [IsEmpty ι]
  proof: Measure.pi_of_empty _ _

@[simp]

中文:
引理 volume_pi_eq_dirac
  结论: {ι : 类型} [有限类型 ι] [是空 ι]
  证明: Measure.pi_of_empty _ _

@[simp]

Depends on / 依赖: isEmptyElim
-/
lemma volume_pi_eq_dirac {ι : Type*} [Fintype ι] [IsEmpty ι]
    {α : ι -> Type*} [forall i, MeasureSpace (α i)] (x : forall a, α a := isEmptyElim) :
    (volume : Measure (forall i, α i)) = Measure.dirac x :=
  Measure.pi_of_empty _ _

@[simp]
/--
theorem `pi_empty_univ` / 定理 `pi_empty_univ`

English:
theorem pi_empty_univ
  statement: {α : Type*} [Fintype α] [IsEmpty α] {β : α -> Type*}
  proof: by
  rw [pi_of_empty]; rw [measure_univ]

中文:
定理 pi_empty_univ
  结论: {α : 类型} [有限类型 α] [是空 α] {β : α -> 类型}
  证明: by
  rw [pi_of_empty]; rw [measure_univ]

Depends on / 依赖: measure_univ, pi_of_empty
-/
theorem pi_empty_univ {α : Type*} [Fintype α] [IsEmpty α] {β : α -> Type*}
    {m : forall α, MeasurableSpace (β α)} (μ : forall a : α, Measure (β a)) :
    Measure.pi μ (Set.univ) = 1 := by
  rw [pi_of_empty]; rw [measure_univ]

/--
theorem `pi_eval_preimage_null` / 定理 `pi_eval_preimage_null`

English:
theorem pi_eval_preimage_null
  given: {i : ι} {s : Set (α i)} (hs : μ i s = 0)
  proof: by
  classical
  -- WLOG, `s` is measurable
  rcases exists_measurable_superset_of_null hs with ⟨t, hst, _, hμt⟩
  suffices Measure.pi μ (eval i ⁻¹' t) = 0 from measure_mono_null (preimage_mono hst) this
  -- Now rewrite it as `Set.pi`, and apply `pi_pi`
  rw [← univ_pi_update_univ]; rw [pi_pi]
  ap

中文:
定理 pi_eval_preimage_null
  条件: {i : ι} {s : 集合 (α i)} (hs : μ i s = 0)
  证明: by
  classical
  -- WLOG, `s` is measurable
  rcases exists_measurable_superset_of_null hs with ⟨t, hst, _, hμt⟩
  suffices Measure.pi μ (eval i ⁻¹' t) = 0 from measure_mono_null (preimage_mono hst) this
  -- Now rewrite it as `Set.pi`, and apply `pi_pi`
  rw [← univ_pi_update_univ]; rw [pi_pi]
  ap

Depends on / 依赖: classical
-/
theorem pi_eval_preimage_null {i : ι} {s : Set (α i)} (hs : μ i s = 0) :
    Measure.pi μ (eval i ⁻¹' s) = 0 := by
  classical
  -- WLOG, `s` is measurable
  rcases exists_measurable_superset_of_null hs with ⟨t, hst, _, hμt⟩
  suffices Measure.pi μ (eval i ⁻¹' t) = 0 from measure_mono_null (preimage_mono hst) this
  -- Now rewrite it as `Set.pi`, and apply `pi_pi`
  rw [← univ_pi_update_univ]; rw [pi_pi]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [hμt]

/--
theorem `quasiMeasurePreserving_eval` / 定理 `quasiMeasurePreserving_eval`

English:
theorem quasiMeasurePreserving_eval
  given: (i : ι)
  proof: by
  refine ⟨by fun_prop, AbsolutelyContinuous.mk fun s hs h2s => ?_⟩
  rw [map_apply (by fun_prop) hs]; rw [pi_eval_preimage_null μ h2s]

中文:
定理 quasiMeasurePreserving_eval
  条件: (i : ι)
  证明: by
  refine ⟨by fun_prop, AbsolutelyContinuous.mk fun s hs h2s => ?_⟩
  rw [map_apply (by fun_prop) hs]; rw [pi_eval_preimage_null μ h2s]

Depends on / 依赖: AbsolutelyContinuous, AbsolutelyContinuous.mk, fun_prop, map_apply, pi_eval_preimage_null
-/
theorem quasiMeasurePreserving_eval (i : ι) :
    QuasiMeasurePreserving (Function.eval i) (Measure.pi μ) (μ i) := by
  refine ⟨by fun_prop, AbsolutelyContinuous.mk fun s hs h2s => ?_⟩
  rw [map_apply (by fun_prop) hs]; rw [pi_eval_preimage_null μ h2s]

/--
lemma `pi_map_eval` / 引理 `pi_map_eval`

English:
lemma pi_map_eval
  given: [DecidableEq ι] (i : ι)
  proof: by
  ext s hs
  rw [Measure.map_apply (measurable_pi_apply i) hs]; rw [← Set.univ_pi_update_univ]; rw [Measure.pi_pi]; rw [Measure.smul_apply]; rw [smul_eq_mul]; rw [← Finset.prod_erase_mul _ _ (a := i) (by simp)]
  congrm ?_ * ?_
  swap; · simp
  refine Finset.prod_congr rfl fun j hj => ?_
  simp [

中文:
引理 pi_map_eval
  条件: [DecidableEq ι] (i : ι)
  证明: by
  ext s hs
  rw [Measure.map_apply (measurable_pi_apply i) hs]; rw [← Set.univ_pi_update_univ]; rw [Measure.pi_pi]; rw [Measure.smul_apply]; rw [smul_eq_mul]; rw [← Finset.prod_erase_mul _ _ (a := i) (by simp)]
  congrm ?_ * ?_
  swap; · simp
  refine Finset.prod_congr rfl fun j hj => ?_
  simp [

Depends on / 依赖: Finset, Finset.ne_of_mem_erase, Finset.prod_congr, Finset.prod_erase_mul, Function, Function.update, Measure, Measure.map_apply, Measure.pi_pi, Measure.smul_apply, Set.univ_pi_update_univ, congrm, map_apply, measurable_pi_apply, ne_of_mem_erase, pi_pi, prod_congr, prod_erase_mul, smul_apply, smul_eq_mul
-/
lemma pi_map_eval [DecidableEq ι] (i : ι) :
     (Measure.pi μ).map (Function.eval i) = (∏ j in Finset.univ.erase i, μ j Set.univ) • (μ i) := by
  ext s hs
  rw [Measure.map_apply (measurable_pi_apply i) hs]; rw [← Set.univ_pi_update_univ]; rw [Measure.pi_pi]; rw [Measure.smul_apply]; rw [smul_eq_mul]; rw [← Finset.prod_erase_mul _ _ (a := i) (by simp)]
  congrm ?_ * ?_
  swap; · simp
  refine Finset.prod_congr rfl fun j hj => ?_
  simp [Function.update, Finset.ne_of_mem_erase hj]

/--
lemma `pi_map_pi` / 引理 `pi_map_pi`

English:
lemma pi_map_pi
  statement: {X Y : ι -> Type*} {mX : forall i, MeasurableSpace (X i)} {μ : (i : ι) -> Measure (X i)}
  proof: by
  have (i : ι) := (hμ i).of_map _ (hf i)
  refine (pi_eq fun s hs => ?_).symm
  rw [map_apply_of_aemeasurable _ (.univ_pi hs)]
  swap
  · exact aemeasurable_pi_lambda _
      fun i => (hf i).comp_quasiMeasurePreserving (quasiMeasurePreserving_eval _ i)
  have : (fun (x : Π i, X i) i => f i (x i))

中文:
引理 pi_map_pi
  结论: {X Y : ι -> 类型} {mX : 对任意 i, 可测空间 (X i)} {μ : (i : ι) -> 测度 (X i)}
  证明: by
  have (i : ι) := (hμ i).of_map _ (hf i)
  refine (pi_eq fun s hs => ?_).symm
  rw [map_apply_of_aemeasurable _ (.univ_pi hs)]
  swap
  · exact aemeasurable_pi_lambda _
      fun i => (hf i).comp_quasiMeasurePreserving (quasiMeasurePreserving_eval _ i)
  have : (fun (x : Π i, X i) i => f i (x i))

Depends on / 依赖: Set.univ.pi, aemeasurable_pi_lambda, comp_quasiMeasurePreserving, map_apply_of_aemeasurable, of_map, pi_eq, pi_pi, quasiMeasurePreserving_eval, univ_pi
-/
lemma pi_map_pi {X Y : ι -> Type*} {mX : forall i, MeasurableSpace (X i)} {μ : (i : ι) -> Measure (X i)}
    [forall i, MeasurableSpace (Y i)] {f : (i : ι) -> X i -> Y i} [hμ : forall i, SigmaFinite ((μ i).map (f i))]
    (hf : forall i, AEMeasurable (f i) (μ i)) :
    (Measure.pi μ).map (fun x i => (f i (x i))) = Measure.pi (fun i => (μ i).map (f i)) := by
  have (i : ι) := (hμ i).of_map _ (hf i)
  refine (pi_eq fun s hs => ?_).symm
  rw [map_apply_of_aemeasurable _ (.univ_pi hs)]
  swap
  · exact aemeasurable_pi_lambda _
      fun i => (hf i).comp_quasiMeasurePreserving (quasiMeasurePreserving_eval _ i)
  have : (fun (x : Π i, X i) i => f i (x i)) ⁻¹' (Set.univ.pi s) =
      Set.univ.pi (fun i => (f i) ⁻¹' (s i)) := by ext x; simp
  rw [this]; rw [pi_pi]
  congr with i
  rw [map_apply_of_aemeasurable (hf i) (hs i)]

omit [forall i, SigmaFinite (μ i)] in
/--
lemma `_root_.MeasureTheory.measurePreserving_eval` / 引理 `_root_.MeasureTheory.measurePreserving_eval`

English:
lemma _root_.MeasureTheory.measurePreserving_eval
  given: [forall i, IsProbabilityMeasure (μ i)] (i : ι)
  proof: by
  refine ⟨measurable_pi_apply i, ?_⟩
  classical
  rw [Measure.pi_map_eval]; rw [Finset.prod_eq_one]; rw [one_smul]
  exact fun _ _ => measure_univ

中文:
引理 _root_.测度论.measurePreserving_eval
  条件: [对任意 i, 是概率测度 (μ i)] (i : ι)
  证明: by
  refine ⟨measurable_pi_apply i, ?_⟩
  classical
  rw [Measure.pi_map_eval]; rw [Finset.prod_eq_one]; rw [one_smul]
  exact fun _ _ => measure_univ

Depends on / 依赖: Finset, Finset.prod_eq_one, Measure, Measure.pi_map_eval, classical, measurable_pi_apply, measure_univ, one_smul, pi_map_eval, prod_eq_one
-/
lemma _root_.MeasureTheory.measurePreserving_eval [forall i, IsProbabilityMeasure (μ i)] (i : ι) :
    MeasurePreserving (Function.eval i) (Measure.pi μ) (μ i) := by
  refine ⟨measurable_pi_apply i, ?_⟩
  classical
  rw [Measure.pi_map_eval]; rw [Finset.prod_eq_one]; rw [one_smul]
  exact fun _ _ => measure_univ

/--
theorem `pi_hyperplane` / 定理 `pi_hyperplane`

English:
theorem pi_hyperplane
  given: (i : ι) [NullSingletonClass (μ i)] (x : α i)
  proof: show Measure.pi μ (eval i ⁻¹' {x}) = 0 from pi_eval_preimage_null _ (measure_singleton x)

中文:
定理 pi_hyperplane
  条件: (i : ι) [NullSingleton类 (μ i)] (x : α i)
  证明: show Measure.pi μ (eval i ⁻¹' {x}) = 0 from pi_eval_preimage_null _ (measure_singleton x)

Depends on / 依赖: Measure, Measure.pi, measure_singleton, pi_eval_preimage_null
-/
theorem pi_hyperplane (i : ι) [NullSingletonClass (μ i)] (x : α i) :
    Measure.pi μ { f : forall i, α i | f i = x } = 0 :=
  show Measure.pi μ (eval i ⁻¹' {x}) = 0 from pi_eval_preimage_null _ (measure_singleton x)

/--
theorem `ae_eval_ne` / 定理 `ae_eval_ne`

English:
theorem ae_eval_ne
  given: (i : ι) [NullSingletonClass (μ i)] (x : α i)
  proof: compl_mem_ae_iff.2 (pi_hyperplane μ i x)

中文:
定理 ae_eval_ne
  条件: (i : ι) [NullSingleton类 (μ i)] (x : α i)
  证明: compl_mem_ae_iff.2 (pi_hyperplane μ i x)

Depends on / 依赖: compl_mem_ae_iff, pi_hyperplane
-/
theorem ae_eval_ne (i : ι) [NullSingletonClass (μ i)] (x : α i) :
    forallᵐ y : forall i, α i ∂Measure.pi μ, y i != x :=
  compl_mem_ae_iff.2 (pi_hyperplane μ i x)

/--
theorem `restrict_pi_pi` / 定理 `restrict_pi_pi`

English:
theorem restrict_pi_pi
  given: (s : (i : ι) -> Set (α i))
  proof: by
  refine (pi_eq fun _ h => ?_).symm
  simp_rw [restrict_apply (MeasurableSet.univ_pi h), restrict_apply (h _),
    ← Set.pi_inter_distrib, pi_pi]

中文:
定理 restrict_pi_pi
  条件: (s : (i : ι) -> 集合 (α i))
  证明: by
  refine (pi_eq fun _ h => ?_).symm
  simp_rw [restrict_apply (MeasurableSet.univ_pi h), restrict_apply (h _),
    ← Set.pi_inter_distrib, pi_pi]

Depends on / 依赖: MeasurableSet, MeasurableSet.univ_pi, Set.pi_inter_distrib, pi_eq, pi_inter_distrib, pi_pi, restrict_apply, simp_rw, univ_pi
-/
theorem restrict_pi_pi (s : (i : ι) -> Set (α i)) :
    (Measure.pi μ).restrict (Set.univ.pi fun i => s i) = .pi (fun i => (μ i).restrict (s i)) := by
  refine (pi_eq fun _ h => ?_).symm
  simp_rw [restrict_apply (MeasurableSet.univ_pi h), restrict_apply (h _),
    ← Set.pi_inter_distrib, pi_pi]

variable {μ}

/--
theorem `tendsto_eval_ae_ae` / 定理 `tendsto_eval_ae_ae`

English:
theorem tendsto_eval_ae_ae
  given: {i : ι}
  statement: Tendsto (eval i) (ae (Measure.pi μ)) (ae (μ i))
  proof: fun _ hs =>
  pi_eval_preimage_null μ hs

中文:
定理 tendsto_eval_ae_ae
  条件: {i : ι}
  结论: 收敛 (eval i) (ae (测度.pi μ)) (ae (μ i))
  证明: fun _ hs =>
  pi_eval_preimage_null μ hs
-/
theorem tendsto_eval_ae_ae {i : ι} : Tendsto (eval i) (ae (Measure.pi μ)) (ae (μ i)) := fun _ hs =>
  pi_eval_preimage_null μ hs

/--
theorem `ae_pi_le_pi` / 定理 `ae_pi_le_pi`

English:
theorem ae_pi_le_pi
  statement: ae (Measure.pi μ) <= Filter.pi fun i => ae (μ i)
  proof: le_iInf fun _ => tendsto_eval_ae_ae.le_comap

中文:
定理 ae_pi_le_pi
  结论: ae (测度.pi μ) <= 滤子.pi fun i => ae (μ i)
  证明: le_iInf fun _ => tendsto_eval_ae_ae.le_comap

Depends on / 依赖: le_comap, le_iInf, tendsto_eval_ae_ae, tendsto_eval_ae_ae.le_comap
-/
theorem ae_pi_le_pi : ae (Measure.pi μ) <= Filter.pi fun i => ae (μ i) :=
  le_iInf fun _ => tendsto_eval_ae_ae.le_comap

/--
theorem `ae_eq_pi` / 定理 `ae_eq_pi`

English:
theorem ae_eq_pi
  given: {β : ι -> Type*} {f f' : forall i, α i -> β i} (h : forall i, f i =ᵐ[μ i] f' i)
  proof: (eventually_all.2 fun i => tendsto_eval_ae_ae.eventually (h i)).mono fun _ hx => funext hx

中文:
定理 ae_eq_pi
  条件: {β : ι -> 类型} {f f' : 对任意 i, α i -> β i} (h : 对任意 i, f i =ᵐ[μ i] f' i)
  证明: (eventually_all.2 fun i => tendsto_eval_ae_ae.eventually (h i)).mono fun _ hx => funext hx

Depends on / 依赖: eventually, eventually_all, tendsto_eval_ae_ae, tendsto_eval_ae_ae.eventually
-/
theorem ae_eq_pi {β : ι -> Type*} {f f' : forall i, α i -> β i} (h : forall i, f i =ᵐ[μ i] f' i) :
    (fun (x : forall i, α i) i => f i (x i)) =ᵐ[Measure.pi μ] fun x i => f' i (x i) :=
  (eventually_all.2 fun i => tendsto_eval_ae_ae.eventually (h i)).mono fun _ hx => funext hx

/--
theorem `ae_le_pi` / 定理 `ae_le_pi`

English:
theorem ae_le_pi
  statement: {β : ι -> Type*} [forall i, Preorder (β i)] {f f' : forall i, α i -> β i}
  proof: (eventually_all.2 fun i => tendsto_eval_ae_ae.eventually (h i)).mono fun _ hx => hx

中文:
定理 ae_le_pi
  结论: {β : ι -> 类型} [对任意 i, 预序 (β i)] {f f' : 对任意 i, α i -> β i}
  证明: (eventually_all.2 fun i => tendsto_eval_ae_ae.eventually (h i)).mono fun _ hx => hx

Depends on / 依赖: Int.emod_emod_of_dvd, Int.emod_lt_abs, Int.emod_nonneg, ZMod.intCast_mod, emod_emod_of_dvd, emod_lt_abs, emod_nonneg, eventually, eventually_all, intCast_mod, tendsto_eval_ae_ae, tendsto_eval_ae_ae.eventually
-/
theorem ae_le_pi {β : ι -> Type*} [forall i, Preorder (β i)] {f f' : forall i, α i -> β i}
    (h : forall i, f i <=ᵐ[μ i] f' i) :
    (fun (x : forall i, α i) i => f i (x i)) <=ᵐ[Measure.pi μ] fun x i => f' i (x i) :=
  (eventually_all.2 fun i => tendsto_eval_ae_ae.eventually (h i)).mono fun _ hx => hx

/--
theorem `ae_le_set_pi` / 定理 `ae_le_set_pi`

English:
theorem ae_le_set_pi
  given: {I : Set ι} {s t : forall i, Set (α i)} (h : forall i in I, s i <=ᵐ[μ i] t i)
  proof: ((eventually_all_finite I.toFinite).2 fun i hi => tendsto_eval_ae_ae.eventually (h i hi)).mono
fun _ hst hx i hi => hst i hi hx i hi

中文:
定理 ae_le_set_pi
  条件: {I : 集合 ι} {s t : 对任意 i, 集合 (α i)} (h : 对任意 i in I, s i <=ᵐ[μ i] t i)
  证明: ((eventually_all_finite I.toFinite).2 fun i hi => tendsto_eval_ae_ae.eventually (h i hi)).mono
fun _ hst hx i hi => hst i hi hx i hi

Depends on / 依赖: I.toFinite, _int_eq_if_mod_eight, eventually, eventually_all_finite, mod_cast, tendsto_eval_ae_ae, tendsto_eval_ae_ae.eventually, toFinite
-/
theorem ae_le_set_pi {I : Set ι} {s t : forall i, Set (α i)} (h : forall i in I, s i <=ᵐ[μ i] t i) :
    Set.pi I s <=ᵐ[Measure.pi μ] Set.pi I t :=
  ((eventually_all_finite I.toFinite).2 fun i hi => tendsto_eval_ae_ae.eventually (h i hi)).mono
fun _ hst hx i hi => hst i hi hx i hi

/--
theorem `ae_eq_set_pi` / 定理 `ae_eq_set_pi`

English:
theorem ae_eq_set_pi
  given: {I : Set ι} {s t : forall i, Set (α i)} (h : forall i in I, s i =ᵐ[μ i] t i)
  proof: (ae_le_set_pi fun i hi => (h i hi).le).antisymm (ae_le_set_pi fun i hi => (h i hi).symm.le)

中文:
定理 ae_eq_set_pi
  条件: {I : 集合 ι} {s t : 对任意 i, 集合 (α i)} (h : 对任意 i in I, s i =ᵐ[μ i] t i)
  证明: (ae_le_set_pi fun i hi => (h i hi).le).antisymm (ae_le_set_pi fun i hi => (h i hi).symm.le)

Depends on / 依赖: ae_le_set_pi, antisymm, symm.le
-/
theorem ae_eq_set_pi {I : Set ι} {s t : forall i, Set (α i)} (h : forall i in I, s i =ᵐ[μ i] t i) :
    Set.pi I s =ᵐ[Measure.pi μ] Set.pi I t :=
  (ae_le_set_pi fun i hi => (h i hi).le).antisymm (ae_le_set_pi fun i hi => (h i hi).symm.le)

/--
lemma `pi_map_piOptionEquivProd` / 引理 `pi_map_piOptionEquivProd`

English:
lemma pi_map_piOptionEquivProd
  statement: {β : Option ι -> Type*} [forall i, MeasurableSpace (β i)]
  proof: by
.symm refine pi_eq (fun s _ => ?_)
  let e_meas : ((i : ι) -> β (some i)) × β none ≃ᵐ ((i : Option ι) -> β i) :=
.symm MeasurableEquiv.piOptionEquivProd β
  have me := MeasurableEquiv.measurableEmbedding e_meas
  have : e_meas ⁻¹' pi univ s = (pi univ (fun i => s (some i))) ×ˢ (s none) := by
    

中文:
引理 pi_map_piOptionEquivProd
  结论: {β : 选项类型 ι -> 类型} [对任意 i, 可测空间 (β i)]
  证明: by
.symm refine pi_eq (fun s _ => ?_)
  let e_meas : ((i : ι) -> β (some i)) × β none ≃ᵐ ((i : Option ι) -> β i) :=
.symm MeasurableEquiv.piOptionEquivProd β
  have me := MeasurableEquiv.measurableEmbedding e_meas
  have : e_meas ⁻¹' pi univ s = (pi univ (fun i => s (some i))) ×ˢ (s none) := by
    

Depends on / 依赖: Finset, Finset.prod_insertNone, MeasurableEquiv, MeasurableEquiv.measurableEmbedding, MeasurableEquiv.piOptionEquivProd, Set.mem_pi, cast_intCast, e_meas, forall_true_left, map_apply, me.map_apply, measurableEmbedding, mem_pi, mem_preimage, mem_prod, mem_univ, piOptionEquivProd, pi_eq, prod_insertNone, univ_option
-/
lemma pi_map_piOptionEquivProd {β : Option ι -> Type*} [forall i, MeasurableSpace (β i)]
    (μ : (i : Option ι) -> Measure (β i)) [forall (i : Option ι), SigmaFinite (μ i)] :
    ((Measure.pi fun i => μ (some i)).prod (μ none)).map
      (MeasurableEquiv.piOptionEquivProd β).symm = Measure.pi μ := by
.symm refine pi_eq (fun s _ => ?_)
  let e_meas : ((i : ι) -> β (some i)) × β none ≃ᵐ ((i : Option ι) -> β i) :=
.symm MeasurableEquiv.piOptionEquivProd β
  have me := MeasurableEquiv.measurableEmbedding e_meas
  have : e_meas ⁻¹' pi univ s = (pi univ (fun i => s (some i))) ×ˢ (s none) := by
    ext x
    simp only [mem_preimage, Set.mem_pi, mem_univ, forall_true_left, mem_prod]
    refine ⟨by tauto, fun _ i => ?_⟩
    rcases i <;> tauto
  simp only [e_meas, me.map_apply, univ_option, Finset.prod_insertNone, this,
    prod_prod, pi_pi, mul_comm]

section Intervals

variable [forall i, PartialOrder (α i)] [forall i, NullSingletonClass (μ i)]

/--
theorem `pi_Iio_ae_eq_pi_Iic` / 定理 `pi_Iio_ae_eq_pi_Iic`

English:
theorem pi_Iio_ae_eq_pi_Iic
  given: {s : Set ι} {f : forall i, α i}
  proof: ae_eq_set_pi fun _ _ => Iio_ae_eq_Iic

中文:
定理 pi_Iio_ae_eq_pi_Iic
  条件: {s : 集合 ι} {f : 对任意 i, α i}
  证明: ae_eq_set_pi fun _ _ => Iio_ae_eq_Iic

Depends on / 依赖: Iio_ae_eq_Iic, ae_eq_set_pi
-/
theorem pi_Iio_ae_eq_pi_Iic {s : Set ι} {f : forall i, α i} :
    (pi s fun i => Iio (f i)) =ᵐ[Measure.pi μ] pi s fun i => Iic (f i) :=
  ae_eq_set_pi fun _ _ => Iio_ae_eq_Iic

/--
theorem `pi_Ioi_ae_eq_pi_Ici` / 定理 `pi_Ioi_ae_eq_pi_Ici`

English:
theorem pi_Ioi_ae_eq_pi_Ici
  given: {s : Set ι} {f : forall i, α i}
  proof: ae_eq_set_pi fun _ _ => Ioi_ae_eq_Ici

中文:
定理 pi_Ioi_ae_eq_pi_Ici
  条件: {s : 集合 ι} {f : 对任意 i, α i}
  证明: ae_eq_set_pi fun _ _ => Ioi_ae_eq_Ici

Depends on / 依赖: Ioi_ae_eq_Ici, ae_eq_set_pi
-/
theorem pi_Ioi_ae_eq_pi_Ici {s : Set ι} {f : forall i, α i} :
    (pi s fun i => Ioi (f i)) =ᵐ[Measure.pi μ] pi s fun i => Ici (f i) :=
  ae_eq_set_pi fun _ _ => Ioi_ae_eq_Ici

/--
theorem `univ_pi_Iio_ae_eq_Iic` / 定理 `univ_pi_Iio_ae_eq_Iic`

English:
theorem univ_pi_Iio_ae_eq_Iic
  given: {f : forall i, α i}
  proof: by
  rw [← pi_univ_Iic]; exact pi_Iio_ae_eq_pi_Iic

中文:
定理 univ_pi_Iio_ae_eq_Iic
  条件: {f : 对任意 i, α i}
  证明: by
  rw [← pi_univ_Iic]; exact pi_Iio_ae_eq_pi_Iic

Depends on / 依赖: pi_Iio_ae_eq_pi_Iic, pi_univ_Iic
-/
theorem univ_pi_Iio_ae_eq_Iic {f : forall i, α i} :
    (pi univ fun i => Iio (f i)) =ᵐ[Measure.pi μ] Iic f := by
  rw [← pi_univ_Iic]; exact pi_Iio_ae_eq_pi_Iic

/--
theorem `univ_pi_Ioi_ae_eq_Ici` / 定理 `univ_pi_Ioi_ae_eq_Ici`

English:
theorem univ_pi_Ioi_ae_eq_Ici
  given: {f : forall i, α i}
  proof: by
  rw [← pi_univ_Ici]; exact pi_Ioi_ae_eq_pi_Ici

中文:
定理 univ_pi_Ioi_ae_eq_Ici
  条件: {f : 对任意 i, α i}
  证明: by
  rw [← pi_univ_Ici]; exact pi_Ioi_ae_eq_pi_Ici

Depends on / 依赖: pi_Ioi_ae_eq_pi_Ici, pi_univ_Ici
-/
theorem univ_pi_Ioi_ae_eq_Ici {f : forall i, α i} :
    (pi univ fun i => Ioi (f i)) =ᵐ[Measure.pi μ] Ici f := by
  rw [← pi_univ_Ici]; exact pi_Ioi_ae_eq_pi_Ici

/--
theorem `pi_Ioo_ae_eq_pi_Icc` / 定理 `pi_Ioo_ae_eq_pi_Icc`

English:
theorem pi_Ioo_ae_eq_pi_Icc
  given: {s : Set ι} {f g : forall i, α i}
  proof: ae_eq_set_pi fun _ _ => Ioo_ae_eq_Icc

中文:
定理 pi_Ioo_ae_eq_pi_Icc
  条件: {s : 集合 ι} {f g : 对任意 i, α i}
  证明: ae_eq_set_pi fun _ _ => Ioo_ae_eq_Icc

Depends on / 依赖: Ioo_ae_eq_Icc, ae_eq_set_pi
-/
theorem pi_Ioo_ae_eq_pi_Icc {s : Set ι} {f g : forall i, α i} :
    (pi s fun i => Ioo (f i) (g i)) =ᵐ[Measure.pi μ] pi s fun i => Icc (f i) (g i) :=
  ae_eq_set_pi fun _ _ => Ioo_ae_eq_Icc

/--
theorem `pi_Ioo_ae_eq_pi_Ioc` / 定理 `pi_Ioo_ae_eq_pi_Ioc`

English:
theorem pi_Ioo_ae_eq_pi_Ioc
  given: {s : Set ι} {f g : forall i, α i}
  proof: ae_eq_set_pi fun _ _ => Ioo_ae_eq_Ioc

中文:
定理 pi_Ioo_ae_eq_pi_Ioc
  条件: {s : 集合 ι} {f g : 对任意 i, α i}
  证明: ae_eq_set_pi fun _ _ => Ioo_ae_eq_Ioc

Depends on / 依赖: Ioo_ae_eq_Ioc, ae_eq_set_pi
-/
theorem pi_Ioo_ae_eq_pi_Ioc {s : Set ι} {f g : forall i, α i} :
    (pi s fun i => Ioo (f i) (g i)) =ᵐ[Measure.pi μ] pi s fun i => Ioc (f i) (g i) :=
  ae_eq_set_pi fun _ _ => Ioo_ae_eq_Ioc

/--
theorem `univ_pi_Ioo_ae_eq_Icc` / 定理 `univ_pi_Ioo_ae_eq_Icc`

English:
theorem univ_pi_Ioo_ae_eq_Icc
  given: {f g : forall i, α i}
  proof: by
  rw [← pi_univ_Icc]; exact pi_Ioo_ae_eq_pi_Icc

中文:
定理 univ_pi_Ioo_ae_eq_Icc
  条件: {f g : 对任意 i, α i}
  证明: by
  rw [← pi_univ_Icc]; exact pi_Ioo_ae_eq_pi_Icc

Depends on / 依赖: pi_Ioo_ae_eq_pi_Icc, pi_univ_Icc
-/
theorem univ_pi_Ioo_ae_eq_Icc {f g : forall i, α i} :
    (pi univ fun i => Ioo (f i) (g i)) =ᵐ[Measure.pi μ] Icc f g := by
  rw [← pi_univ_Icc]; exact pi_Ioo_ae_eq_pi_Icc

/--
theorem `pi_Ioc_ae_eq_pi_Icc` / 定理 `pi_Ioc_ae_eq_pi_Icc`

English:
theorem pi_Ioc_ae_eq_pi_Icc
  given: {s : Set ι} {f g : forall i, α i}
  proof: ae_eq_set_pi fun _ _ => Ioc_ae_eq_Icc

中文:
定理 pi_Ioc_ae_eq_pi_Icc
  条件: {s : 集合 ι} {f g : 对任意 i, α i}
  证明: ae_eq_set_pi fun _ _ => Ioc_ae_eq_Icc

Depends on / 依赖: Ioc_ae_eq_Icc, ae_eq_set_pi
-/
theorem pi_Ioc_ae_eq_pi_Icc {s : Set ι} {f g : forall i, α i} :
    (pi s fun i => Ioc (f i) (g i)) =ᵐ[Measure.pi μ] pi s fun i => Icc (f i) (g i) :=
  ae_eq_set_pi fun _ _ => Ioc_ae_eq_Icc

/--
theorem `univ_pi_Ioc_ae_eq_Icc` / 定理 `univ_pi_Ioc_ae_eq_Icc`

English:
theorem univ_pi_Ioc_ae_eq_Icc
  given: {f g : forall i, α i}
  proof: by
  rw [← pi_univ_Icc]; exact pi_Ioc_ae_eq_pi_Icc

中文:
定理 univ_pi_Ioc_ae_eq_Icc
  条件: {f g : 对任意 i, α i}
  证明: by
  rw [← pi_univ_Icc]; exact pi_Ioc_ae_eq_pi_Icc

Depends on / 依赖: pi_Ioc_ae_eq_pi_Icc, pi_univ_Icc
-/
theorem univ_pi_Ioc_ae_eq_Icc {f g : forall i, α i} :
    (pi univ fun i => Ioc (f i) (g i)) =ᵐ[Measure.pi μ] Icc f g := by
  rw [← pi_univ_Icc]; exact pi_Ioc_ae_eq_pi_Icc

/--
theorem `pi_Ico_ae_eq_pi_Icc` / 定理 `pi_Ico_ae_eq_pi_Icc`

English:
theorem pi_Ico_ae_eq_pi_Icc
  given: {s : Set ι} {f g : forall i, α i}
  proof: ae_eq_set_pi fun _ _ => Ico_ae_eq_Icc

中文:
定理 pi_Ico_ae_eq_pi_Icc
  条件: {s : 集合 ι} {f g : 对任意 i, α i}
  证明: ae_eq_set_pi fun _ _ => Ico_ae_eq_Icc

Depends on / 依赖: Ico_ae_eq_Icc, ae_eq_set_pi
-/
theorem pi_Ico_ae_eq_pi_Icc {s : Set ι} {f g : forall i, α i} :
    (pi s fun i => Ico (f i) (g i)) =ᵐ[Measure.pi μ] pi s fun i => Icc (f i) (g i) :=
  ae_eq_set_pi fun _ _ => Ico_ae_eq_Icc

/--
theorem `univ_pi_Ico_ae_eq_Icc` / 定理 `univ_pi_Ico_ae_eq_Icc`

English:
theorem univ_pi_Ico_ae_eq_Icc
  given: {f g : forall i, α i}
  proof: by
  rw [← pi_univ_Icc]; exact pi_Ico_ae_eq_pi_Icc

中文:
定理 univ_pi_Ico_ae_eq_Icc
  条件: {f g : 对任意 i, α i}
  证明: by
  rw [← pi_univ_Icc]; exact pi_Ico_ae_eq_pi_Icc

Depends on / 依赖: pi_Ico_ae_eq_pi_Icc, pi_univ_Icc
-/
theorem univ_pi_Ico_ae_eq_Icc {f g : forall i, α i} :
    (pi univ fun i => Ico (f i) (g i)) =ᵐ[Measure.pi μ] Icc f g := by
  rw [← pi_univ_Icc]; exact pi_Ico_ae_eq_pi_Icc

end Intervals

/--
theorem `pi_nullSingletonClass` / 定理 `pi_nullSingletonClass`

English:
theorem pi_nullSingletonClass
  given: (i : ι) [NullSingletonClass (μ i)]
  proof: ⟨fun x => flip measure_mono_null (pi_hyperplane μ i (x i)) (singleton_subset_iff.2 rfl)⟩

@[deprecated (since := "2026-06-09")]
alias pi_noAtoms := pi_nullSingletonClass

中文:
定理 pi_nullSingletonClass
  条件: (i : ι) [NullSingleton类 (μ i)]
  证明: ⟨fun x => flip measure_mono_null (pi_hyperplane μ i (x i)) (singleton_subset_iff.2 rfl)⟩

@[deprecated (since := "2026-06-09")]
alias pi_noAtoms := pi_nullSingletonClass

Depends on / 依赖: measure_mono_null, pi_hyperplane, singleton_subset_iff
-/
theorem pi_nullSingletonClass (i : ι) [NullSingletonClass (μ i)] :
    NullSingletonClass (Measure.pi μ) :=
  ⟨fun x => flip measure_mono_null (pi_hyperplane μ i (x i)) (singleton_subset_iff.2 rfl)⟩

@[deprecated (since := "2026-06-09")]
alias pi_noAtoms := pi_nullSingletonClass

/--
Instance `pi_nullSingletonClass'` / 实例 `pi_nullSingletonClass'`

English:
instance pi_nullSingletonClass'
  signature: [h : Nonempty ι] [forall i, NullSingletonClass (μ i)]
  body: h.elim fun i => pi_nullSingletonClass i

@[deprecated (since := "2026-06-09")]
alias pi_noAtoms' := pi_nullSingletonClass'

中文:
实例 pi_nullSingletonClass'
  签名: [h : 非空 ι] [对任意 i, NullSingleton类 (μ i)]
  定义体: h.elim fun i => pi_nullSingletonClass i

@[deprecated (since := "2026-06-09")]
alias pi_noAtoms' := pi_nullSingletonClass'

Depends on / 依赖: h.elim, pi_nullSingletonClass
-/
instance pi_nullSingletonClass' [h : Nonempty ι] [forall i, NullSingletonClass (μ i)] :
    NullSingletonClass (Measure.pi μ) :=
  h.elim fun i => pi_nullSingletonClass i

@[deprecated (since := "2026-06-09")]
alias pi_noAtoms' := pi_nullSingletonClass'

instance {α : ι -> Type*} [Nonempty ι] [forall i, MeasureSpace (α i)]
    [forall i, SigmaFinite (volume : Measure (α i))] [forall i, NullSingletonClass (volume : Measure (α i))] :
    NullSingletonClass (volume : Measure (forall i, α i)) :=
  pi_nullSingletonClass'

/--
Instance `pi.isLocallyFiniteMeasure` / 实例 `pi.isLocallyFiniteMeasure`

English:
instance pi.isLocallyFiniteMeasure
  body: by
  refine ⟨fun x => ?_⟩
  choose s hxs ho hμ using fun i => (μ i).exists_isOpen_measure_lt_top (x i)
  refine ⟨pi univ s, set_pi_mem_nhds finite_univ fun i _ => IsOpen.mem_nhds (ho i) (hxs i), ?_⟩
  rw [pi_pi]
  exact ENNReal.prod_lt_top fun i _ => hμ i

中文:
实例 pi.isLocallyFiniteMeasure
  定义体: by
  refine ⟨fun x => ?_⟩
  choose s hxs ho hμ using fun i => (μ i).exists_isOpen_measure_lt_top (x i)
  refine ⟨pi univ s, set_pi_mem_nhds finite_univ fun i _ => IsOpen.mem_nhds (ho i) (hxs i), ?_⟩
  rw [pi_pi]
  exact ENNReal.prod_lt_top fun i _ => hμ i

Depends on / 依赖: ENNReal, ENNReal.prod_lt_top, IsOpen, IsOpen.mem_nhds, exists_isOpen_measure_lt_top, finite_univ, mem_nhds, pi_pi, prod_lt_top, set_pi_mem_nhds
-/
instance pi.isLocallyFiniteMeasure
    [forall i, TopologicalSpace (α i)] [forall i, IsLocallyFiniteMeasure (μ i)] :
    IsLocallyFiniteMeasure (Measure.pi μ) := by
  refine ⟨fun x => ?_⟩
  choose s hxs ho hμ using fun i => (μ i).exists_isOpen_measure_lt_top (x i)
  refine ⟨pi univ s, set_pi_mem_nhds finite_univ fun i _ => IsOpen.mem_nhds (ho i) (hxs i), ?_⟩
  rw [pi_pi]
  exact ENNReal.prod_lt_top fun i _ => hμ i

instance {X : ι -> Type*} [forall i, TopologicalSpace (X i)] [forall i, MeasureSpace (X i)]
    [forall i, SigmaFinite (volume : Measure (X i))]
    [forall i, IsLocallyFiniteMeasure (volume : Measure (X i))] :
    IsLocallyFiniteMeasure (volume : Measure (forall i, X i)) :=
  pi.isLocallyFiniteMeasure

/--
Instance `_root_.IsUnifLocDoublingMeasure.pi` / 实例 `_root_.IsUnifLocDoublingMeasure.pi`

English:
instance _root_.IsUnifLocDoublingMeasure.pi
  signature: {ι : Type*} [Fintype ι] {X : ι -> Type*}
  body: by
  use ∏ i, IsUnifLocDoublingMeasure.doublingConstant (μ i)
  filter_upwards [Filter.eventually_all.mpr fun i =>
      IsUnifLocDoublingMeasure.eventually_measure_le_doublingConstant_mul (μ i),
    eventually_mem_nhdsWithin] with r hr (hr₀ : 0 < r) x
  simpa (disch := positivity) [Finset.prod_mul_

中文:
实例 _root_.是UnifLocDoublingMeasure.pi
  签名: {ι : 类型} [有限类型 ι] {X : ι -> 类型}
  定义体: by
  use ∏ i, IsUnifLocDoublingMeasure.doublingConstant (μ i)
  filter_upwards [Filter.eventually_all.mpr fun i =>
      IsUnifLocDoublingMeasure.eventually_measure_le_doublingConstant_mul (μ i),
    eventually_mem_nhdsWithin] with r hr (hr₀ : 0 < r) x
  simpa (disch := positivity) [Finset.prod_mul_

Depends on / 依赖: Filter, Filter.eventually_all.mpr, Finset, Finset.prod_mul_distrib, Fintype, Fintype.prod_mono, IsUnifLocDoublingMeasure, IsUnifLocDoublingMeasure.doublingConstant, IsUnifLocDoublingMeasure.eventually_measure_le_doublingConstant_mul, closedBall_pi, doublingConstant, eventually_all, eventually_measure_le_doublingConstant_mul, eventually_mem_nhdsWithin, filter_upwards, pi_pi, prod_mono, prod_mul_distrib
-/
instance _root_.IsUnifLocDoublingMeasure.pi {ι : Type*} [Fintype ι] {X : ι -> Type*}
    [forall i, PseudoMetricSpace (X i)] [forall i, MeasurableSpace (X i)] (μ : forall i, Measure (X i))
    [forall i, SigmaFinite (μ i)] [forall i, IsUnifLocDoublingMeasure (μ i)] :
    IsUnifLocDoublingMeasure (Measure.pi μ) := by
  use ∏ i, IsUnifLocDoublingMeasure.doublingConstant (μ i)
  filter_upwards [Filter.eventually_all.mpr fun i =>
      IsUnifLocDoublingMeasure.eventually_measure_le_doublingConstant_mul (μ i),
    eventually_mem_nhdsWithin] with r hr (hr₀ : 0 < r) x
  simpa (disch := positivity) [Finset.prod_mul_distrib, closedBall_pi, pi_pi]
    using Fintype.prod_mono' fun i => hr i (x i)

/--
Instance `IsUnifLocDoublingMeasure.volume_pi` / 实例 `IsUnifLocDoublingMeasure.volume_pi`

English:
instance IsUnifLocDoublingMeasure.volume_pi
  signature: {ι : Type*} [Fintype ι] {X : ι -> Type*}
  body: .pi _

中文:
实例 是UnifLocDoublingMeasure.volume_pi
  签名: {ι : 类型} [有限类型 ι] {X : ι -> 类型}
  定义体: .pi _
-/
instance IsUnifLocDoublingMeasure.volume_pi {ι : Type*} [Fintype ι] {X : ι -> Type*}
    [forall i, PseudoMetricSpace (X i)] [forall i, MeasureSpace (X i)]
    [forall i, SigmaFinite (volume : Measure (X i))]
    [forall i, IsUnifLocDoublingMeasure (volume : Measure (X i))] :
    IsUnifLocDoublingMeasure (volume : Measure (forall i, X i)) :=
  .pi _

variable (μ)

@[to_additive]
/--
Instance `pi.isMulLeftInvariant` / 实例 `pi.isMulLeftInvariant`

English:
instance pi.isMulLeftInvariant
  signature: [forall i, Group (α i)] [forall i, MeasurableMul (α i)]
  body: by
  refine ⟨fun v => (pi_eq fun s hs => ?_).symm⟩
  rw [map_apply (measurable_const_mul _) (MeasurableSet.univ_pi hs)]; rw [show (v * ·) ⁻¹' univ.pi s = univ.pi fun i => (v i * ·) ⁻¹' s i by rfl]; rw [pi_pi]
  simp_rw [measure_preimage_mul]

@[to_additive]

中文:
实例 pi.isMulLeftInvariant
  签名: [对任意 i, 群 (α i)] [对任意 i, MeasurableMul (α i)]
  定义体: by
  refine ⟨fun v => (pi_eq fun s hs => ?_).symm⟩
  rw [map_apply (measurable_const_mul _) (MeasurableSet.univ_pi hs)]; rw [show (v * ·) ⁻¹' univ.pi s = univ.pi fun i => (v i * ·) ⁻¹' s i by rfl]; rw [pi_pi]
  simp_rw [measure_preimage_mul]

@[to_additive]

Depends on / 依赖: MeasurableSet, MeasurableSet.univ_pi, map_apply, measurable_const_mul, measure_preimage_mul, pi_eq, pi_pi, simp_rw, univ.pi, univ_pi
-/
instance pi.isMulLeftInvariant [forall i, Group (α i)] [forall i, MeasurableMul (α i)]
    [forall i, IsMulLeftInvariant (μ i)] : IsMulLeftInvariant (Measure.pi μ) := by
  refine ⟨fun v => (pi_eq fun s hs => ?_).symm⟩
  rw [map_apply (measurable_const_mul _) (MeasurableSet.univ_pi hs)]; rw [show (v * ·) ⁻¹' univ.pi s = univ.pi fun i => (v i * ·) ⁻¹' s i by rfl]; rw [pi_pi]
  simp_rw [measure_preimage_mul]

@[to_additive]
instance {G : ι -> Type*} [forall i, Group (G i)] [forall i, MeasureSpace (G i)] [forall i, MeasurableMul (G i)]
    [forall i, SigmaFinite (volume : Measure (G i))] [forall i, IsMulLeftInvariant (volume : Measure (G i))] :
    IsMulLeftInvariant (volume : Measure (forall i, G i)) :=
  pi.isMulLeftInvariant _

@[to_additive]
/--
Instance `pi.isMulRightInvariant` / 实例 `pi.isMulRightInvariant`

English:
instance pi.isMulRightInvariant
  signature: [forall i, Group (α i)] [forall i, MeasurableMul (α i)]
  body: by
  refine ⟨fun v => (pi_eq fun s hs => ?_).symm⟩
  rw [map_apply (measurable_mul_const _) (MeasurableSet.univ_pi hs)]; rw [show (· * v) ⁻¹' univ.pi s = univ.pi fun i => (· * v i) ⁻¹' s i by rfl]; rw [pi_pi]
  simp_rw [measure_preimage_mul_right]

@[to_additive]

中文:
实例 pi.isMulRightInvariant
  签名: [对任意 i, 群 (α i)] [对任意 i, MeasurableMul (α i)]
  定义体: by
  refine ⟨fun v => (pi_eq fun s hs => ?_).symm⟩
  rw [map_apply (measurable_mul_const _) (MeasurableSet.univ_pi hs)]; rw [show (· * v) ⁻¹' univ.pi s = univ.pi fun i => (· * v i) ⁻¹' s i by rfl]; rw [pi_pi]
  simp_rw [measure_preimage_mul_right]

@[to_additive]

Depends on / 依赖: MeasurableSet, MeasurableSet.univ_pi, map_apply, measurable_mul_const, measure_preimage_mul_right, pi_eq, pi_pi, simp_rw, univ.pi, univ_pi
-/
instance pi.isMulRightInvariant [forall i, Group (α i)] [forall i, MeasurableMul (α i)]
    [forall i, IsMulRightInvariant (μ i)] : IsMulRightInvariant (Measure.pi μ) := by
  refine ⟨fun v => (pi_eq fun s hs => ?_).symm⟩
  rw [map_apply (measurable_mul_const _) (MeasurableSet.univ_pi hs)]; rw [show (· * v) ⁻¹' univ.pi s = univ.pi fun i => (· * v i) ⁻¹' s i by rfl]; rw [pi_pi]
  simp_rw [measure_preimage_mul_right]

@[to_additive]
instance {G : ι -> Type*} [forall i, Group (G i)] [forall i, MeasureSpace (G i)] [forall i, MeasurableMul (G i)]
    [forall i, SigmaFinite (volume : Measure (G i))]
    [forall i, IsMulRightInvariant (volume : Measure (G i))] :
    IsMulRightInvariant (volume : Measure (forall i, G i)) :=
  pi.isMulRightInvariant _

@[to_additive]
/--
Instance `pi.isInvInvariant` / 实例 `pi.isInvInvariant`

English:
instance pi.isInvInvariant
  signature: [forall i, Group (α i)] [forall i, MeasurableInv (α i)]
  body: by
  refine ⟨(Measure.pi_eq fun s hs => ?_).symm⟩
  have A : Inv.inv ⁻¹' pi univ s = Set.pi univ fun i => Inv.inv ⁻¹' s i := by ext; simp
  simp_rw [Measure.inv, Measure.map_apply measurable_inv (MeasurableSet.univ_pi hs), A, pi_pi,
    measure_preimage_inv]

@[to_additive]

中文:
实例 pi.isInvInvariant
  签名: [对任意 i, 群 (α i)] [对任意 i, MeasurableInv (α i)]
  定义体: by
  refine ⟨(Measure.pi_eq fun s hs => ?_).symm⟩
  have A : Inv.inv ⁻¹' pi univ s = Set.pi univ fun i => Inv.inv ⁻¹' s i := by ext; simp
  simp_rw [Measure.inv, Measure.map_apply measurable_inv (MeasurableSet.univ_pi hs), A, pi_pi,
    measure_preimage_inv]

@[to_additive]

Depends on / 依赖: Inv.inv, MeasurableSet, MeasurableSet.univ_pi, Measure, Measure.inv, Measure.map_apply, Measure.pi_eq, Set.pi, map_apply, measurable_inv, measure_preimage_inv, pi_eq, pi_pi, simp_rw, univ_pi
-/
instance pi.isInvInvariant [forall i, Group (α i)] [forall i, MeasurableInv (α i)]
    [forall i, IsInvInvariant (μ i)] : IsInvInvariant (Measure.pi μ) := by
  refine ⟨(Measure.pi_eq fun s hs => ?_).symm⟩
  have A : Inv.inv ⁻¹' pi univ s = Set.pi univ fun i => Inv.inv ⁻¹' s i := by ext; simp
  simp_rw [Measure.inv, Measure.map_apply measurable_inv (MeasurableSet.univ_pi hs), A, pi_pi,
    measure_preimage_inv]

@[to_additive]
instance {G : ι -> Type*} [forall i, Group (G i)] [forall i, MeasureSpace (G i)] [forall i, MeasurableInv (G i)]
    [forall i, SigmaFinite (volume : Measure (G i))] [forall i, IsInvInvariant (volume : Measure (G i))] :
    IsInvInvariant (volume : Measure (forall i, G i)) :=
  pi.isInvInvariant _

/--
Instance `pi.isOpenPosMeasure` / 实例 `pi.isOpenPosMeasure`

English:
instance pi.isOpenPosMeasure
  signature: [forall i, TopologicalSpace (α i)] [forall i, IsOpenPosMeasure (μ i)]
  body: by
  constructor
  rintro U U_open ⟨a, ha⟩
  obtain ⟨s, ⟨hs, hsU⟩⟩ := isOpen_pi_iff'.1 U_open a ha
  refine ne_of_gt (lt_of_lt_of_le ?_ (measure_mono hsU))
  simp only [pi_pi]
  rw [CanonicallyOrderedAdd.prod_pos]
  intro i _
  apply (hs i).1.measure_pos (μ i) ⟨a i, (hs i).2⟩

中文:
实例 pi.isOpenPosMeasure
  签名: [对任意 i, 拓扑空间 (α i)] [对任意 i, 是OpenPosMeasure (μ i)]
  定义体: by
  constructor
  rintro U U_open ⟨a, ha⟩
  obtain ⟨s, ⟨hs, hsU⟩⟩ := isOpen_pi_iff'.1 U_open a ha
  refine ne_of_gt (lt_of_lt_of_le ?_ (measure_mono hsU))
  simp only [pi_pi]
  rw [CanonicallyOrderedAdd.prod_pos]
  intro i _
  apply (hs i).1.measure_pos (μ i) ⟨a i, (hs i).2⟩

Depends on / 依赖: CanonicallyOrderedAdd, CanonicallyOrderedAdd.prod_pos, U_open, isOpen_pi_iff, lt_of_lt_of_le, measure_mono, measure_pos, ne_of_gt, pi_pi, prod_pos
-/
instance pi.isOpenPosMeasure [forall i, TopologicalSpace (α i)] [forall i, IsOpenPosMeasure (μ i)] :
    IsOpenPosMeasure (MeasureTheory.Measure.pi μ) := by
  constructor
  rintro U U_open ⟨a, ha⟩
  obtain ⟨s, ⟨hs, hsU⟩⟩ := isOpen_pi_iff'.1 U_open a ha
  refine ne_of_gt (lt_of_lt_of_le ?_ (measure_mono hsU))
  simp only [pi_pi]
  rw [CanonicallyOrderedAdd.prod_pos]
  intro i _
  apply (hs i).1.measure_pos (μ i) ⟨a i, (hs i).2⟩

instance {X : ι -> Type*} [forall i, TopologicalSpace (X i)] [forall i, MeasureSpace (X i)]
    [forall i, IsOpenPosMeasure (volume : Measure (X i))] [forall i, SigmaFinite (volume : Measure (X i))] :
    IsOpenPosMeasure (volume : Measure (forall i, X i)) :=
  pi.isOpenPosMeasure _

/--
Instance `pi.isFiniteMeasureOnCompacts` / 实例 `pi.isFiniteMeasureOnCompacts`

English:
instance pi.isFiniteMeasureOnCompacts
  signature: [forall i, TopologicalSpace (α i)]
  body: by
  constructor
  intro K hK
  suffices Measure.pi μ (Set.univ.pi fun j => Function.eval j '' K) < ⊤ by
    exact lt_of_le_of_lt (measure_mono (univ.subset_pi_eval_image K)) this
  rw [Measure.pi_pi]
  refine WithTop.prod_lt_top ?_
  exact fun i _ => IsCompact.measure_lt_top (IsCompact.image hK (co

中文:
实例 pi.isFiniteMeasureOnCompacts
  签名: [对任意 i, 拓扑空间 (α i)]
  定义体: by
  constructor
  intro K hK
  suffices Measure.pi μ (Set.univ.pi fun j => Function.eval j '' K) < ⊤ by
    exact lt_of_le_of_lt (measure_mono (univ.subset_pi_eval_image K)) this
  rw [Measure.pi_pi]
  refine WithTop.prod_lt_top ?_
  exact fun i _ => IsCompact.measure_lt_top (IsCompact.image hK (co

Depends on / 依赖: Function, Function.eval, IsCompact, IsCompact.image, IsCompact.measure_lt_top, Measure, Measure.pi, Measure.pi_pi, Set.univ.pi, WithTop, WithTop.prod_lt_top, continuous_apply, lt_of_le_of_lt, measure_lt_top, measure_mono, pi_pi, prod_lt_top, subset_pi_eval_image, univ.subset_pi_eval_image
-/
instance pi.isFiniteMeasureOnCompacts [forall i, TopologicalSpace (α i)]
    [forall i, IsFiniteMeasureOnCompacts (μ i)] :
    IsFiniteMeasureOnCompacts (MeasureTheory.Measure.pi μ) := by
  constructor
  intro K hK
  suffices Measure.pi μ (Set.univ.pi fun j => Function.eval j '' K) < ⊤ by
    exact lt_of_le_of_lt (measure_mono (univ.subset_pi_eval_image K)) this
  rw [Measure.pi_pi]
  refine WithTop.prod_lt_top ?_
  exact fun i _ => IsCompact.measure_lt_top (IsCompact.image hK (continuous_apply i))

instance {X : ι -> Type*} [forall i, MeasureSpace (X i)] [forall i, TopologicalSpace (X i)]
    [forall i, SigmaFinite (volume : Measure (X i))]
    [forall i, IsFiniteMeasureOnCompacts (volume : Measure (X i))] :
    IsFiniteMeasureOnCompacts (volume : Measure (forall i, X i)) :=
  pi.isFiniteMeasureOnCompacts _

@[to_additive]
/--
Instance `pi.isHaarMeasure` / 实例 `pi.isHaarMeasure`

English:
instance pi.isHaarMeasure
  signature: [forall i, Group (α i)] [forall i, TopologicalSpace (α i)]

中文:
实例 pi.isHaarMeasure
  签名: [对任意 i, 群 (α i)] [对任意 i, 拓扑空间 (α i)]
-/
instance pi.isHaarMeasure [forall i, Group (α i)] [forall i, TopologicalSpace (α i)]
    [forall i, IsHaarMeasure (μ i)] [forall i, MeasurableMul (α i)] : IsHaarMeasure (Measure.pi μ) where

@[to_additive]
instance {G : ι -> Type*} [forall i, Group (G i)] [forall i, MeasureSpace (G i)] [forall i, MeasurableMul (G i)]
    [forall i, TopologicalSpace (G i)] [forall i, SigmaFinite (volume : Measure (G i))]
    [forall i, IsHaarMeasure (volume : Measure (G i))] : IsHaarMeasure (volume : Measure (forall i, G i)) :=
  pi.isHaarMeasure _

end Measure

/--
theorem `volume_pi` / 定理 `volume_pi`

English:
theorem volume_pi
  given: [forall i, MeasureSpace (α i)]
  proof: rfl

中文:
定理 volume_pi
  条件: [对任意 i, 测度空间 (α i)]
  证明: rfl
-/
theorem volume_pi [forall i, MeasureSpace (α i)] :
    (volume : Measure (forall i, α i)) = Measure.pi fun _ => volume :=
  rfl

/--
theorem `volume_pi_pi` / 定理 `volume_pi_pi`

English:
theorem volume_pi_pi
  statement: [forall i, MeasureSpace (α i)] [forall i, SigmaFinite (volume : Measure (α i))]
  proof: Measure.pi_pi (fun _ => volume) s

中文:
定理 volume_pi_pi
  结论: [对任意 i, 测度空间 (α i)] [对任意 i, σ有限 (volume : 测度 (α i))]
  证明: Measure.pi_pi (fun _ => volume) s

Depends on / 依赖: Measure, Measure.pi_pi, pi_pi, volume
-/
theorem volume_pi_pi [forall i, MeasureSpace (α i)] [forall i, SigmaFinite (volume : Measure (α i))]
    (s : forall i, Set (α i)) : volume (pi univ s) = ∏ i, volume (s i) :=
  Measure.pi_pi (fun _ => volume) s

/--
theorem `volume_pi_ball` / 定理 `volume_pi_ball`

English:
theorem volume_pi_ball
  statement: [forall i, MeasureSpace (α i)] [forall i, SigmaFinite (volume : Measure (α i))]
  proof: Measure.pi_ball _ _ hr

中文:
定理 volume_pi_ball
  结论: [对任意 i, 测度空间 (α i)] [对任意 i, σ有限 (volume : 测度 (α i))]
  证明: Measure.pi_ball _ _ hr

Depends on / 依赖: Measure, Measure.pi_ball, pi_ball
-/
theorem volume_pi_ball [forall i, MeasureSpace (α i)] [forall i, SigmaFinite (volume : Measure (α i))]
    [forall i, MetricSpace (α i)] (x : forall i, α i) {r : Real} (hr : 0 < r) :
    volume (Metric.ball x r) = ∏ i, volume (Metric.ball (x i) r) :=
  Measure.pi_ball _ _ hr

/--
theorem `volume_pi_closedBall` / 定理 `volume_pi_closedBall`

English:
theorem volume_pi_closedBall
  statement: [forall i, MeasureSpace (α i)] [forall i, SigmaFinite (volume : Measure (α i))]
  proof: Measure.pi_closedBall _ _ hr

中文:
定理 volume_pi_closedBall
  结论: [对任意 i, 测度空间 (α i)] [对任意 i, σ有限 (volume : 测度 (α i))]
  证明: Measure.pi_closedBall _ _ hr

Depends on / 依赖: Measure, Measure.pi_closedBall, pi_closedBall
-/
theorem volume_pi_closedBall [forall i, MeasureSpace (α i)] [forall i, SigmaFinite (volume : Measure (α i))]
    [forall i, MetricSpace (α i)] (x : forall i, α i) {r : Real} (hr : 0 <= r) :
    volume (Metric.closedBall x r) = ∏ i, volume (Metric.closedBall (x i) r) :=
  Measure.pi_closedBall _ _ hr

open Measure

/-- We intentionally restrict this only to the nondependent function space, since type-class
inference cannot find an instance for `ι → ℝ` when this is stated for dependent function spaces. -/
@[to_additive /-- We intentionally restrict this only to the nondependent function space, since
type-class inference cannot find an instance for `ι → ℝ` when this is stated for dependent function
spaces. -/]
/--
Instance `Pi.isMulLeftInvariant_volume` / 实例 `Pi.isMulLeftInvariant_volume`

English:
instance Pi.isMulLeftInvariant_volume
  signature: {α} [Group α] [MeasureSpace α]
  body: pi.isMulLeftInvariant _

中文:
实例 依赖函数类型.isMulLeftInvariant_volume
  签名: {α} [群 α] [测度空间 α]
  定义体: pi.isMulLeftInvariant _

Depends on / 依赖: isMulLeftInvariant, pi.isMulLeftInvariant
-/
instance Pi.isMulLeftInvariant_volume {α} [Group α] [MeasureSpace α]
    [SigmaFinite (volume : Measure α)] [MeasurableMul α] [IsMulLeftInvariant (volume : Measure α)] :
    IsMulLeftInvariant (volume : Measure (ι -> α)) :=
  pi.isMulLeftInvariant _

/-- We intentionally restrict this only to the nondependent function space, since type-class
inference cannot find an instance for `ι → ℝ` when this is stated for dependent function spaces. -/
@[to_additive /-- We intentionally restrict this only to the nondependent function space, since
type-class inference cannot find an instance for `ι → ℝ` when this is stated for dependent function
spaces. -/]
/--
Instance `Pi.isInvInvariant_volume` / 实例 `Pi.isInvInvariant_volume`

English:
instance Pi.isInvInvariant_volume
  signature: {α} [Group α] [MeasureSpace α] [SigmaFinite (volume : Measure α)]
  body: pi.isInvInvariant _

中文:
实例 依赖函数类型.isInvInvariant_volume
  签名: {α} [群 α] [测度空间 α] [σ有限 (volume : 测度 α)]
  定义体: pi.isInvInvariant _

Depends on / 依赖: isInvInvariant, pi.isInvInvariant
-/
instance Pi.isInvInvariant_volume {α} [Group α] [MeasureSpace α] [SigmaFinite (volume : Measure α)]
    [MeasurableInv α] [IsInvInvariant (volume : Measure α)] :
    IsInvInvariant (volume : Measure (ι -> α)) :=
  pi.isInvInvariant _

/-!
### Measure-preserving equivalences

In this section we prove that some measurable equivalences (e.g., between `Fin 1 → α` and `α` or
between `Fin 2 → α` and `α × α`) preserve measure or volume. These lemmas can be used to prove that
measures of corresponding sets (images or preimages) have equal measures and functions `f ∘ e` and
`f` have equal integrals, see lemmas in the `MeasureTheory.measurePreserving` prefix.
-/


section MeasurePreserving

variable {m : forall i, MeasurableSpace (α i)} (μ : forall i, Measure (α i)) [forall i, SigmaFinite (μ i)]
variable [Fintype ι']

/--
theorem `measurePreserving_piEquivPiSubtypeProd` / 定理 `measurePreserving_piEquivPiSubtypeProd`

English:
theorem measurePreserving_piEquivPiSubtypeProd
  given: (p : ι -> Prop) [DecidablePred p]
  proof: by
  set e := (MeasurableEquiv.piEquivPiSubtypeProd α p).symm
  refine MeasurePreserving.symm e ?_
  refine ⟨e.measurable, (pi_eq fun s _ => ?_).symm⟩
  have : e ⁻¹' pi univ s =
      (pi univ fun i : { i // p i } => s i) ×ˢ pi univ fun i : { i // ¬p i } => s i :=
    Equiv.preimage_piEquivPiSubtype

中文:
定理 measurePreserving_piEquivPiSubtypeProd
  条件: (p : ι -> 命题) [DecidablePred p]
  证明: by
  set e := (MeasurableEquiv.piEquivPiSubtypeProd α p).symm
  refine MeasurePreserving.symm e ?_
  refine ⟨e.measurable, (pi_eq fun s _ => ?_).symm⟩
  have : e ⁻¹' pi univ s =
      (pi univ fun i : { i // p i } => s i) ×ˢ pi univ fun i : { i // ¬p i } => s i :=
    Equiv.preimage_piEquivPiSubtype

Depends on / 依赖: Equiv.preimage_piEquivPiSubtypeProd_symm_pi, Fintype, Fintype.prod_subtype_mul_prod_subtype, MeasurableEquiv, MeasurableEquiv.piEquivPiSubtypeProd, MeasurePreserving, MeasurePreserving.symm, e.map_apply, e.measurable, map_apply, measurable, piEquivPiSubtypeProd, pi_eq, pi_pi, preimage_piEquivPiSubtypeProd_symm_pi, prod_prod, prod_subtype_mul_prod_subtype
-/
theorem measurePreserving_piEquivPiSubtypeProd (p : ι -> Prop) [DecidablePred p] :
    MeasurePreserving (MeasurableEquiv.piEquivPiSubtypeProd α p) (Measure.pi μ)
      ((Measure.pi fun i : Subtype p => μ i).prod (Measure.pi fun i => μ i)) := by
  set e := (MeasurableEquiv.piEquivPiSubtypeProd α p).symm
  refine MeasurePreserving.symm e ?_
  refine ⟨e.measurable, (pi_eq fun s _ => ?_).symm⟩
  have : e ⁻¹' pi univ s =
      (pi univ fun i : { i // p i } => s i) ×ˢ pi univ fun i : { i // ¬p i } => s i :=
    Equiv.preimage_piEquivPiSubtypeProd_symm_pi p s
  rw [e.map_apply]; rw [this]; rw [prod_prod]; rw [pi_pi]; rw [pi_pi]
  exact Fintype.prod_subtype_mul_prod_subtype p fun i => μ i (s i)

/--
theorem `volume_preserving_piEquivPiSubtypeProd` / 定理 `volume_preserving_piEquivPiSubtypeProd`

English:
theorem volume_preserving_piEquivPiSubtypeProd
  statement: (α : ι -> Type*)
  proof: measurePreserving_piEquivPiSubtypeProd (fun _ => volume) p

中文:
定理 volume_preserving_piEquivPiSubtypeProd
  结论: (α : ι -> 类型)
  证明: measurePreserving_piEquivPiSubtypeProd (fun _ => volume) p

Depends on / 依赖: measurePreserving_piEquivPiSubtypeProd, volume
-/
theorem volume_preserving_piEquivPiSubtypeProd (α : ι -> Type*)
    [forall i, MeasureSpace (α i)] [forall i, SigmaFinite (volume : Measure (α i))] (p : ι -> Prop)
    [DecidablePred p] : MeasurePreserving (MeasurableEquiv.piEquivPiSubtypeProd α p) :=
  measurePreserving_piEquivPiSubtypeProd (fun _ => volume) p

/--
theorem `measurePreserving_piCongrLeft` / 定理 `measurePreserving_piCongrLeft`

English:
theorem measurePreserving_piCongrLeft
  given: (f : ι' ≃ ι)
  proof: (MeasurableEquiv.piCongrLeft α f).measurable
  map_eq := by
    refine (pi_eq fun s _ => ?_).symm
    rw [MeasurableEquiv.map_apply]; rw [MeasurableEquiv.coe_piCongrLeft f]; rw [Equiv.piCongrLeft_preimage_univ_pi]; rw [pi_pi _ _]; rw [f.prod_comp (fun i => μ i (s i))]

中文:
定理 measurePreserving_piCongrLeft
  条件: (f : ι' ≃ ι)
  证明: (MeasurableEquiv.piCongrLeft α f).measurable
  map_eq := by
    refine (pi_eq fun s _ => ?_).symm
    rw [MeasurableEquiv.map_apply]; rw [MeasurableEquiv.coe_piCongrLeft f]; rw [Equiv.piCongrLeft_preimage_univ_pi]; rw [pi_pi _ _]; rw [f.prod_comp (fun i => μ i (s i))]

Depends on / 依赖: MeasurableEquiv, MeasurableEquiv.piCongrLeft, measurable, piCongrLeft
-/
theorem measurePreserving_piCongrLeft (f : ι' ≃ ι) :
    MeasurePreserving (MeasurableEquiv.piCongrLeft α f)
      (Measure.pi fun i' => μ (f i')) (Measure.pi μ) where
  measurable := (MeasurableEquiv.piCongrLeft α f).measurable
  map_eq := by
    refine (pi_eq fun s _ => ?_).symm
    rw [MeasurableEquiv.map_apply]; rw [MeasurableEquiv.coe_piCongrLeft f]; rw [Equiv.piCongrLeft_preimage_univ_pi]; rw [pi_pi _ _]; rw [f.prod_comp (fun i => μ i (s i))]

/--
theorem `volume_measurePreserving_piCongrLeft` / 定理 `volume_measurePreserving_piCongrLeft`

English:
theorem volume_measurePreserving_piCongrLeft
  statement: (α : ι -> Type*) (f : ι' ≃ ι)
  proof: measurePreserving_piCongrLeft (fun _ => volume) f

中文:
定理 volume_measurePreserving_piCongrLeft
  结论: (α : ι -> 类型) (f : ι' ≃ ι)
  证明: measurePreserving_piCongrLeft (fun _ => volume) f

Depends on / 依赖: measurePreserving_piCongrLeft, volume
-/
theorem volume_measurePreserving_piCongrLeft (α : ι -> Type*) (f : ι' ≃ ι)
    [forall i, MeasureSpace (α i)] [forall i, SigmaFinite (volume : Measure (α i))] :
    MeasurePreserving (MeasurableEquiv.piCongrLeft α f) volume volume :=
  measurePreserving_piCongrLeft (fun _ => volume) f

/--
lemma `Measure.pi_map_piCongrLeft` / 引理 `Measure.pi_map_piCongrLeft`

English:
lemma Measure.pi_map_piCongrLeft
  statement: (e : ι ≃ ι') {β : ι' -> Type*} [forall i, MeasurableSpace (β i)]
  proof: (measurePreserving_piCongrLeft (α := fun i => β i) μ e).map_eq

中文:
引理 测度.pi_map_piCongrLeft
  结论: (e : ι ≃ ι') {β : ι' -> 类型} [对任意 i, 可测空间 (β i)]
  证明: (measurePreserving_piCongrLeft (α := fun i => β i) μ e).map_eq

Depends on / 依赖: map_eq, measurePreserving_piCongrLeft
-/
lemma Measure.pi_map_piCongrLeft (e : ι ≃ ι') {β : ι' -> Type*} [forall i, MeasurableSpace (β i)]
    (μ : (i : ι') -> Measure (β i)) [forall i, SigmaFinite (μ i)] :
    (Measure.pi fun i => μ (e i)).map (MeasurableEquiv.piCongrLeft (fun i => β i) e) =
      Measure.pi μ :=
  (measurePreserving_piCongrLeft (α := fun i => β i) μ e).map_eq

/--
theorem `measurePreserving_arrowProdEquivProdArrow` / 定理 `measurePreserving_arrowProdEquivProdArrow`

English:
theorem measurePreserving_arrowProdEquivProdArrow
  statement: (α β γ : Type*) [MeasurableSpace α]
  proof: (MeasurableEquiv.arrowProdEquivProdArrow α β γ).measurable
  map_eq := by
    refine (FiniteSpanningSetsIn.ext ?_ (isPiSystem_pi.prod isPiSystem_pi)
      ((FiniteSpanningSetsIn.pi fun i => (μ i).toFiniteSpanningSetsIn).prod
      (FiniteSpanningSetsIn.pi (fun i => (ν i).toFiniteSpanningSetsIn))) ?_

中文:
定理 measurePreserving_arrowProdEquivProdArrow
  结论: (α β γ : 类型) [可测空间 α]
  证明: (MeasurableEquiv.arrowProdEquivProdArrow α β γ).measurable
  map_eq := by
    refine (FiniteSpanningSetsIn.ext ?_ (isPiSystem_pi.prod isPiSystem_pi)
      ((FiniteSpanningSetsIn.pi fun i => (μ i).toFiniteSpanningSetsIn).prod
      (FiniteSpanningSetsIn.pi (fun i => (ν i).toFiniteSpanningSetsIn))) ?_

Depends on / 依赖: MeasurableEquiv, MeasurableEquiv.arrowProdEquivProdArrow, arrowProdEquivProdArrow, measurable
-/
theorem measurePreserving_arrowProdEquivProdArrow (α β γ : Type*) [MeasurableSpace α]
    [MeasurableSpace β] [Fintype γ] (μ : γ -> Measure α) (ν : γ -> Measure β) [forall i, SigmaFinite (μ i)]
    [forall i, SigmaFinite (ν i)] :
    MeasurePreserving (MeasurableEquiv.arrowProdEquivProdArrow α β γ)
      (.pi fun i => (μ i).prod (ν i))
        ((Measure.pi fun i => μ i).prod (Measure.pi fun i => ν i)) where
  measurable := (MeasurableEquiv.arrowProdEquivProdArrow α β γ).measurable
  map_eq := by
    refine (FiniteSpanningSetsIn.ext ?_ (isPiSystem_pi.prod isPiSystem_pi)
      ((FiniteSpanningSetsIn.pi fun i => (μ i).toFiniteSpanningSetsIn).prod
      (FiniteSpanningSetsIn.pi (fun i => (ν i).toFiniteSpanningSetsIn))) ?_).symm
    · refine (generateFrom_eq_prod generateFrom_pi generateFrom_pi ?_ ?_).symm
      · exact (FiniteSpanningSetsIn.pi (fun i => (μ i).toFiniteSpanningSetsIn)).isCountablySpanning
      · exact (FiniteSpanningSetsIn.pi (fun i => (ν i).toFiniteSpanningSetsIn)).isCountablySpanning
    · rintro _ ⟨s, ⟨s, _, rfl⟩, ⟨_, ⟨t, _, rfl⟩, rfl⟩⟩
      rw [MeasurableEquiv.map_apply]; rw [MeasurableEquiv.arrowProdEquivProdArrow]; rw [MeasurableEquiv.coe_mk]
      rw [show Equiv.arrowProdEquivProdArrow γ _ _ ⁻¹' (univ.pi s ×ˢ univ.pi t) =
          (univ.pi fun i => s i ×ˢ t i) by
          ext; simp [Set.mem_pi]; rw [forall_and]]
      simp_rw [pi_pi, prod_prod, pi_pi, Finset.prod_mul_distrib]

/--
theorem `volume_measurePreserving_arrowProdEquivProdArrow` / 定理 `volume_measurePreserving_arrowProdEquivProdArrow`

English:
theorem volume_measurePreserving_arrowProdEquivProdArrow
  statement: (α β γ : Type*) [MeasureSpace α]
  proof: measurePreserving_arrowProdEquivProdArrow α β γ (fun _ => volume) (fun _ => volume)

中文:
定理 volume_measurePreserving_arrowProdEquivProdArrow
  结论: (α β γ : 类型) [测度空间 α]
  证明: measurePreserving_arrowProdEquivProdArrow α β γ (fun _ => volume) (fun _ => volume)

Depends on / 依赖: measurePreserving_arrowProdEquivProdArrow, volume
-/
theorem volume_measurePreserving_arrowProdEquivProdArrow (α β γ : Type*) [MeasureSpace α]
    [MeasureSpace β] [Fintype γ] [SigmaFinite (volume : Measure α)]
    [SigmaFinite (volume : Measure β)] :
    MeasurePreserving (MeasurableEquiv.arrowProdEquivProdArrow α β γ) :=
  measurePreserving_arrowProdEquivProdArrow α β γ (fun _ => volume) (fun _ => volume)

/--
theorem `measurePreserving_sumPiEquivProdPi_symm` / 定理 `measurePreserving_sumPiEquivProdPi_symm`

English:
theorem measurePreserving_sumPiEquivProdPi_symm
  statement: {X : ι oplus ι' -> Type*}
  proof: (MeasurableEquiv.sumPiEquivProdPi X).symm.measurable
  map_eq := by
    refine (pi_eq fun s _ => ?_).symm
    simp_rw [MeasurableEquiv.map_apply, MeasurableEquiv.coe_sumPiEquivProdPi_symm,
      Equiv.sumPiEquivProdPi_symm_preimage_univ_pi, Measure.prod_prod, Measure.pi_pi,
      Fintype.prod_sum_ty

中文:
定理 measurePreserving_sumPiEquivProdPi_symm
  结论: {X : ι oplus ι' -> 类型}
  证明: (MeasurableEquiv.sumPiEquivProdPi X).symm.measurable
  map_eq := by
    refine (pi_eq fun s _ => ?_).symm
    simp_rw [MeasurableEquiv.map_apply, MeasurableEquiv.coe_sumPiEquivProdPi_symm,
      Equiv.sumPiEquivProdPi_symm_preimage_univ_pi, Measure.prod_prod, Measure.pi_pi,
      Fintype.prod_sum_ty

Depends on / 依赖: MeasurableEquiv, MeasurableEquiv.sumPiEquivProdPi, measurable, sumPiEquivProdPi, symm.measurable
-/
theorem measurePreserving_sumPiEquivProdPi_symm {X : ι oplus ι' -> Type*}
    {m : forall i, MeasurableSpace (X i)} (μ : forall i, Measure (X i)) [forall i, SigmaFinite (μ i)] :
    MeasurePreserving (MeasurableEquiv.sumPiEquivProdPi X).symm
      ((Measure.pi fun i => μ (.inl i)).prod (Measure.pi fun i => μ (.inr i))) (Measure.pi μ) where
  measurable := (MeasurableEquiv.sumPiEquivProdPi X).symm.measurable
  map_eq := by
    refine (pi_eq fun s _ => ?_).symm
    simp_rw [MeasurableEquiv.map_apply, MeasurableEquiv.coe_sumPiEquivProdPi_symm,
      Equiv.sumPiEquivProdPi_symm_preimage_univ_pi, Measure.prod_prod, Measure.pi_pi,
      Fintype.prod_sum_type]

/--
theorem `volume_measurePreserving_sumPiEquivProdPi_symm` / 定理 `volume_measurePreserving_sumPiEquivProdPi_symm`

English:
theorem volume_measurePreserving_sumPiEquivProdPi_symm
  statement: (X : ι oplus ι' -> Type*)
  proof: measurePreserving_sumPiEquivProdPi_symm (fun _ => volume)

中文:
定理 volume_measurePreserving_sumPiEquivProdPi_symm
  结论: (X : ι oplus ι' -> 类型)
  证明: measurePreserving_sumPiEquivProdPi_symm (fun _ => volume)

Depends on / 依赖: measurePreserving_sumPiEquivProdPi_symm, volume
-/
theorem volume_measurePreserving_sumPiEquivProdPi_symm (X : ι oplus ι' -> Type*)
    [forall i, MeasureSpace (X i)] [forall i, SigmaFinite (volume : Measure (X i))] :
    MeasurePreserving (MeasurableEquiv.sumPiEquivProdPi X).symm volume volume :=
  measurePreserving_sumPiEquivProdPi_symm (fun _ => volume)

/--
theorem `measurePreserving_sumPiEquivProdPi` / 定理 `measurePreserving_sumPiEquivProdPi`

English:
theorem measurePreserving_sumPiEquivProdPi
  statement: {X : ι oplus ι' -> Type*} {_m : forall i, MeasurableSpace (X i)}
  proof: .symm measurePreserving_sumPiEquivProdPi_symm μ

中文:
定理 measurePreserving_sumPiEquivProdPi
  结论: {X : ι oplus ι' -> 类型} {_m : 对任意 i, 可测空间 (X i)}
  证明: .symm measurePreserving_sumPiEquivProdPi_symm μ

Depends on / 依赖: Compatible, ValueGroupWithZero, measurePreserving_sumPiEquivProdPi_symm
-/
theorem measurePreserving_sumPiEquivProdPi {X : ι oplus ι' -> Type*} {_m : forall i, MeasurableSpace (X i)}
    (μ : forall i, Measure (X i)) [forall i, SigmaFinite (μ i)] :
    MeasurePreserving (MeasurableEquiv.sumPiEquivProdPi X)
      (Measure.pi μ) ((Measure.pi fun i => μ (.inl i)).prod (Measure.pi fun i => μ (.inr i))) :=
.symm measurePreserving_sumPiEquivProdPi_symm μ

/--
theorem `volume_measurePreserving_sumPiEquivProdPi` / 定理 `volume_measurePreserving_sumPiEquivProdPi`

English:
theorem volume_measurePreserving_sumPiEquivProdPi
  statement: (X : ι oplus ι' -> Type*)
  proof: measurePreserving_sumPiEquivProdPi (fun _ => volume)

中文:
定理 volume_measurePreserving_sumPiEquivProdPi
  结论: (X : ι oplus ι' -> 类型)
  证明: measurePreserving_sumPiEquivProdPi (fun _ => volume)

Depends on / 依赖: measurePreserving_sumPiEquivProdPi, volume
-/
theorem volume_measurePreserving_sumPiEquivProdPi (X : ι oplus ι' -> Type*)
    [forall i, MeasureSpace (X i)] [forall i, SigmaFinite (volume : Measure (X i))] :
    MeasurePreserving (MeasurableEquiv.sumPiEquivProdPi X) volume volume :=
  measurePreserving_sumPiEquivProdPi (fun _ => volume)

/--
theorem `measurePreserving_piFinSuccAbove` / 定理 `measurePreserving_piFinSuccAbove`

English:
theorem measurePreserving_piFinSuccAbove
  statement: {n : Nat} {α : Fin (n + 1) -> Type u}
  proof: by
  set e := (MeasurableEquiv.piFinSuccAbove α i).symm
  refine MeasurePreserving.symm e ?_
  refine ⟨e.measurable, (pi_eq fun s _ => ?_).symm⟩
  rw [e.map_apply]; rw [i.prod_univ_succAbove _]; rw [← pi_pi]; rw [← prod_prod]
  congr 1 with ⟨x, f⟩
  simp [e, i.forall_iff_succAbove]

中文:
定理 measurePreserving_piFinSuccAbove
  结论: {n : 自然数} {α : 有限集 (n + 1) -> 类型u}
  证明: by
  set e := (MeasurableEquiv.piFinSuccAbove α i).symm
  refine MeasurePreserving.symm e ?_
  refine ⟨e.measurable, (pi_eq fun s _ => ?_).symm⟩
  rw [e.map_apply]; rw [i.prod_univ_succAbove _]; rw [← pi_pi]; rw [← prod_prod]
  congr 1 with ⟨x, f⟩
  simp [e, i.forall_iff_succAbove]

Depends on / 依赖: MeasurableEquiv, MeasurableEquiv.piFinSuccAbove, MeasurePreserving, MeasurePreserving.symm, e.map_apply, e.measurable, forall_iff_succAbove, i.forall_iff_succAbove, i.prod_univ_succAbove, map_apply, measurable, piFinSuccAbove, pi_eq, pi_pi, prod_prod, prod_univ_succAbove
-/
theorem measurePreserving_piFinSuccAbove {n : Nat} {α : Fin (n + 1) -> Type u}
    {m : forall i, MeasurableSpace (α i)} (μ : forall i, Measure (α i)) [forall i, SigmaFinite (μ i)]
    (i : Fin (n + 1)) :
    MeasurePreserving (MeasurableEquiv.piFinSuccAbove α i) (Measure.pi μ)
      ((μ i).prod <| Measure.pi fun j => μ (i.succAbove j)) := by
  set e := (MeasurableEquiv.piFinSuccAbove α i).symm
  refine MeasurePreserving.symm e ?_
  refine ⟨e.measurable, (pi_eq fun s _ => ?_).symm⟩
  rw [e.map_apply]; rw [i.prod_univ_succAbove _]; rw [← pi_pi]; rw [← prod_prod]
  congr 1 with ⟨x, f⟩
  simp [e, i.forall_iff_succAbove]

/--
theorem `volume_preserving_piFinSuccAbove` / 定理 `volume_preserving_piFinSuccAbove`

English:
theorem volume_preserving_piFinSuccAbove
  statement: {n : Nat} (α : Fin (n + 1) -> Type u)
  proof: measurePreserving_piFinSuccAbove (fun _ => volume) i

中文:
定理 volume_preserving_piFinSuccAbove
  结论: {n : 自然数} (α : 有限集 (n + 1) -> 类型u)
  证明: measurePreserving_piFinSuccAbove (fun _ => volume) i

Depends on / 依赖: measurePreserving_piFinSuccAbove, volume
-/
theorem volume_preserving_piFinSuccAbove {n : Nat} (α : Fin (n + 1) -> Type u)
    [forall i, MeasureSpace (α i)] [forall i, SigmaFinite (volume : Measure (α i))] (i : Fin (n + 1)) :
    MeasurePreserving (MeasurableEquiv.piFinSuccAbove α i) :=
  measurePreserving_piFinSuccAbove (fun _ => volume) i

/--
theorem `measurePreserving_piUnique` / 定理 `measurePreserving_piUnique`

English:
theorem measurePreserving_piUnique
  statement: {X : ι -> Type*} [Unique ι] {m : forall i, MeasurableSpace (X i)}
  proof: (MeasurableEquiv.piUnique X).measurable
  map_eq := by
    set e := MeasurableEquiv.piUnique X
    have : (piPremeasure fun i => (μ i).toOuterMeasure) = Measure.map e.symm (μ default) := by
      ext1 s
      rw [piPremeasure]; rw [Fintype.prod_unique]; rw [e.symm.map_apply]; rw [coe_toOuterMeasure]

中文:
定理 measurePreserving_piUnique
  结论: {X : ι -> 类型} [唯一 ι] {m : 对任意 i, 可测空间 (X i)}
  证明: (MeasurableEquiv.piUnique X).measurable
  map_eq := by
    set e := MeasurableEquiv.piUnique X
    have : (piPremeasure fun i => (μ i).toOuterMeasure) = Measure.map e.symm (μ default) := by
      ext1 s
      rw [piPremeasure]; rw [Fintype.prod_unique]; rw [e.symm.map_apply]; rw [coe_toOuterMeasure]

Depends on / 依赖: MeasurableEquiv, MeasurableEquiv.piUnique, measurable, piUnique
-/
theorem measurePreserving_piUnique {X : ι -> Type*} [Unique ι] {m : forall i, MeasurableSpace (X i)}
    (μ : forall i, Measure (X i)) :
    MeasurePreserving (MeasurableEquiv.piUnique X) (Measure.pi μ) (μ default) where
  measurable := (MeasurableEquiv.piUnique X).measurable
  map_eq := by
    set e := MeasurableEquiv.piUnique X
    have : (piPremeasure fun i => (μ i).toOuterMeasure) = Measure.map e.symm (μ default) := by
      ext1 s
      rw [piPremeasure]; rw [Fintype.prod_unique]; rw [e.symm.map_apply]; rw [coe_toOuterMeasure]
      congr 1; exact e.toEquiv.image_eq_preimage_symm s
    simp_rw [Measure.pi, OuterMeasure.pi, this, ← coe_toOuterMeasure, boundedBy_eq_self,
      toOuterMeasure_toMeasure, MeasurableEquiv.map_map_symm]

/--
theorem `volume_preserving_piUnique` / 定理 `volume_preserving_piUnique`

English:
theorem volume_preserving_piUnique
  given: (X : ι -> Type*) [Unique ι] [forall i, MeasureSpace (X i)]
  proof: measurePreserving_piUnique _

中文:
定理 volume_preserving_piUnique
  条件: (X : ι -> 类型) [唯一 ι] [对任意 i, 测度空间 (X i)]
  证明: measurePreserving_piUnique _

Depends on / 依赖: measurePreserving_piUnique
-/
theorem volume_preserving_piUnique (X : ι -> Type*) [Unique ι] [forall i, MeasureSpace (X i)] :
    MeasurePreserving (MeasurableEquiv.piUnique X) volume volume :=
  measurePreserving_piUnique _

/--
theorem `measurePreserving_funUnique` / 定理 `measurePreserving_funUnique`

English:
theorem measurePreserving_funUnique
  statement: {β : Type u} {_m : MeasurableSpace β} (μ : Measure β)
  proof: measurePreserving_piUnique _

中文:
定理 measurePreserving_funUnique
  结论: {β : 类型u} {_m : 可测空间 β} (μ : 测度 β)
  证明: measurePreserving_piUnique _

Depends on / 依赖: measurePreserving_piUnique
-/
theorem measurePreserving_funUnique {β : Type u} {_m : MeasurableSpace β} (μ : Measure β)
    (α : Type v) [Unique α] :
    MeasurePreserving (MeasurableEquiv.funUnique α β) (Measure.pi fun _ : α => μ) μ :=
  measurePreserving_piUnique _

/--
theorem `volume_preserving_funUnique` / 定理 `volume_preserving_funUnique`

English:
theorem volume_preserving_funUnique
  given: (α : Type u) (β : Type v) [Unique α] [MeasureSpace β]
  proof: measurePreserving_funUnique volume α

中文:
定理 volume_preserving_funUnique
  条件: (α : 类型u) (β : 类型v) [唯一 α] [测度空间 β]
  证明: measurePreserving_funUnique volume α

Depends on / 依赖: measurePreserving_funUnique, volume
-/
theorem volume_preserving_funUnique (α : Type u) (β : Type v) [Unique α] [MeasureSpace β] :
    MeasurePreserving (MeasurableEquiv.funUnique α β) volume volume :=
  measurePreserving_funUnique volume α

/--
theorem `measurePreserving_piFinTwo` / 定理 `measurePreserving_piFinTwo`

English:
theorem measurePreserving_piFinTwo
  statement: {α : Fin 2 -> Type u} {m : forall i, MeasurableSpace (α i)}
  proof: by
  refine ⟨MeasurableEquiv.measurable _, (Measure.prod_eq fun s t _ _ => ?_).symm⟩
  rw [MeasurableEquiv.map_apply]; rw [MeasurableEquiv.piFinTwo_apply]; rw [Fin.preimage_apply_01_prod]; rw [Measure.pi_pi]; rw [Fin.prod_univ_two]
  rfl

中文:
定理 measurePreserving_piFinTwo
  结论: {α : 有限集 2 -> 类型u} {m : 对任意 i, 可测空间 (α i)}
  证明: by
  refine ⟨MeasurableEquiv.measurable _, (Measure.prod_eq fun s t _ _ => ?_).symm⟩
  rw [MeasurableEquiv.map_apply]; rw [MeasurableEquiv.piFinTwo_apply]; rw [Fin.preimage_apply_01_prod]; rw [Measure.pi_pi]; rw [Fin.prod_univ_two]
  rfl

Depends on / 依赖: Fin.preimage_apply_01_prod, Fin.prod_univ_two, MeasurableEquiv, MeasurableEquiv.map_apply, MeasurableEquiv.measurable, MeasurableEquiv.piFinTwo_apply, Measure, Measure.pi_pi, Measure.prod_eq, map_apply, measurable, piFinTwo_apply, pi_pi, preimage_apply_01_prod, prod_eq, prod_univ_two
-/
theorem measurePreserving_piFinTwo {α : Fin 2 -> Type u} {m : forall i, MeasurableSpace (α i)}
    (μ : forall i, Measure (α i)) [forall i, SigmaFinite (μ i)] :
    MeasurePreserving (MeasurableEquiv.piFinTwo α) (Measure.pi μ) ((μ 0).prod (μ 1)) := by
  refine ⟨MeasurableEquiv.measurable _, (Measure.prod_eq fun s t _ _ => ?_).symm⟩
  rw [MeasurableEquiv.map_apply]; rw [MeasurableEquiv.piFinTwo_apply]; rw [Fin.preimage_apply_01_prod]; rw [Measure.pi_pi]; rw [Fin.prod_univ_two]
  rfl

/--
theorem `volume_preserving_piFinTwo` / 定理 `volume_preserving_piFinTwo`

English:
theorem volume_preserving_piFinTwo
  statement: (α : Fin 2 -> Type u) [forall i, MeasureSpace (α i)]
  proof: measurePreserving_piFinTwo _

中文:
定理 volume_preserving_piFinTwo
  结论: (α : 有限集 2 -> 类型u) [对任意 i, 测度空间 (α i)]
  证明: measurePreserving_piFinTwo _

Depends on / 依赖: measurePreserving_piFinTwo
-/
theorem volume_preserving_piFinTwo (α : Fin 2 -> Type u) [forall i, MeasureSpace (α i)]
    [forall i, SigmaFinite (volume : Measure (α i))] :
    MeasurePreserving (MeasurableEquiv.piFinTwo α) volume volume :=
  measurePreserving_piFinTwo _

/--
theorem `measurePreserving_finTwoArrow_vec` / 定理 `measurePreserving_finTwoArrow_vec`

English:
theorem measurePreserving_finTwoArrow_vec
  statement: {α : Type u} {_ : MeasurableSpace α} (μ ν : Measure α)
  proof: haveI : forall i, SigmaFinite (![μ, ν] i) := Fin.forall_fin_two.2 ⟨‹_›, ‹_›⟩
  measurePreserving_piFinTwo _

中文:
定理 measurePreserving_finTwoArrow_vec
  结论: {α : 类型u} {_ : 可测空间 α} (μ ν : 测度 α)
  证明: haveI : forall i, SigmaFinite (![μ, ν] i) := Fin.forall_fin_two.2 ⟨‹_›, ‹_›⟩
  measurePreserving_piFinTwo _

Depends on / 依赖: Fin.forall_fin_two, SigmaFinite, forall_fin_two, measurePreserving_piFinTwo
-/
theorem measurePreserving_finTwoArrow_vec {α : Type u} {_ : MeasurableSpace α} (μ ν : Measure α)
    [SigmaFinite μ] [SigmaFinite ν] :
    MeasurePreserving MeasurableEquiv.finTwoArrow (Measure.pi ![μ, ν]) (μ.prod ν) :=
  haveI : forall i, SigmaFinite (![μ, ν] i) := Fin.forall_fin_two.2 ⟨‹_›, ‹_›⟩
  measurePreserving_piFinTwo _

/--
theorem `measurePreserving_finTwoArrow` / 定理 `measurePreserving_finTwoArrow`

English:
theorem measurePreserving_finTwoArrow
  statement: {α : Type u} {m : MeasurableSpace α} (μ : Measure α)
  proof: by
  simpa only [Matrix.vec_single_eq_const, Matrix.vecCons_const] using
    measurePreserving_finTwoArrow_vec μ μ

中文:
定理 measurePreserving_finTwoArrow
  结论: {α : 类型u} {m : 可测空间 α} (μ : 测度 α)
  证明: by
  simpa only [Matrix.vec_single_eq_const, Matrix.vecCons_const] using
    measurePreserving_finTwoArrow_vec μ μ

Depends on / 依赖: Matrix, Matrix.vecCons_const, Matrix.vec_single_eq_const, measurePreserving_finTwoArrow_vec, vecCons_const, vec_single_eq_const
-/
theorem measurePreserving_finTwoArrow {α : Type u} {m : MeasurableSpace α} (μ : Measure α)
    [SigmaFinite μ] :
    MeasurePreserving MeasurableEquiv.finTwoArrow (Measure.pi fun _ => μ) (μ.prod μ) := by
  simpa only [Matrix.vec_single_eq_const, Matrix.vecCons_const] using
    measurePreserving_finTwoArrow_vec μ μ

/--
theorem `volume_preserving_finTwoArrow` / 定理 `volume_preserving_finTwoArrow`

English:
theorem volume_preserving_finTwoArrow
  statement: (α : Type u) [MeasureSpace α]
  proof: measurePreserving_finTwoArrow volume

中文:
定理 volume_preserving_finTwoArrow
  结论: (α : 类型u) [测度空间 α]
  证明: measurePreserving_finTwoArrow volume

Depends on / 依赖: measurePreserving_finTwoArrow, volume
-/
theorem volume_preserving_finTwoArrow (α : Type u) [MeasureSpace α]
    [SigmaFinite (volume : Measure α)] :
    MeasurePreserving (@MeasurableEquiv.finTwoArrow α _) volume volume :=
  measurePreserving_finTwoArrow volume

/--
theorem `measurePreserving_pi_empty` / 定理 `measurePreserving_pi_empty`

English:
theorem measurePreserving_pi_empty
  statement: {ι : Type u} {α : ι -> Type v} [Fintype ι] [IsEmpty ι]
  proof: by
  set e := MeasurableEquiv.ofUniqueOfUnique (forall i, α i) Unit
  refine ⟨e.measurable, ?_⟩
  rw [Measure.pi_of_empty]; rw [Measure.map_dirac' e.measurable]

中文:
定理 measurePreserving_pi_empty
  结论: {ι : 类型u} {α : ι -> 类型v} [有限类型 ι] [是空 ι]
  证明: by
  set e := MeasurableEquiv.ofUniqueOfUnique (forall i, α i) Unit
  refine ⟨e.measurable, ?_⟩
  rw [Measure.pi_of_empty]; rw [Measure.map_dirac' e.measurable]

Depends on / 依赖: MeasurableEquiv, MeasurableEquiv.ofUniqueOfUnique, Measure, Measure.map_dirac, Measure.pi_of_empty, e.measurable, map_dirac, measurable, ofUniqueOfUnique, pi_of_empty
-/
theorem measurePreserving_pi_empty {ι : Type u} {α : ι -> Type v} [Fintype ι] [IsEmpty ι]
    {m : forall i, MeasurableSpace (α i)} (μ : forall i, Measure (α i)) :
    MeasurePreserving (MeasurableEquiv.ofUniqueOfUnique (forall i, α i) Unit) (Measure.pi μ)
      (Measure.dirac ()) := by
  set e := MeasurableEquiv.ofUniqueOfUnique (forall i, α i) Unit
  refine ⟨e.measurable, ?_⟩
  rw [Measure.pi_of_empty]; rw [Measure.map_dirac' e.measurable]

/--
theorem `volume_preserving_pi_empty` / 定理 `volume_preserving_pi_empty`

English:
theorem volume_preserving_pi_empty
  statement: {ι : Type u} (α : ι -> Type v) [Fintype ι] [IsEmpty ι]
  proof: measurePreserving_pi_empty fun _ => volume

中文:
定理 volume_preserving_pi_empty
  结论: {ι : 类型u} (α : ι -> 类型v) [有限类型 ι] [是空 ι]
  证明: measurePreserving_pi_empty fun _ => volume

Depends on / 依赖: measurePreserving_pi_empty, volume
-/
theorem volume_preserving_pi_empty {ι : Type u} (α : ι -> Type v) [Fintype ι] [IsEmpty ι]
    [forall i, MeasureSpace (α i)] :
    MeasurePreserving (MeasurableEquiv.ofUniqueOfUnique (forall i, α i) Unit) volume volume :=
  measurePreserving_pi_empty fun _ => volume

/--
theorem `measurePreserving_piFinsetUnion` / 定理 `measurePreserving_piFinsetUnion`

English:
theorem measurePreserving_piFinsetUnion
  statement: {ι : Type*} {α : ι -> Type*}
  proof: let e := Equiv.Finset.union s t h
.comp measurePreserving_piCongrLeft (fun i : ↥(s union t) => μ i) e
    measurePreserving_sumPiEquivProdPi_symm fun b => μ (e b)

中文:
定理 measurePreserving_piFinsetUnion
  结论: {ι : 类型} {α : ι -> 类型}
  证明: let e := Equiv.Finset.union s t h
.comp measurePreserving_piCongrLeft (fun i : ↥(s union t) => μ i) e
    measurePreserving_sumPiEquivProdPi_symm fun b => μ (e b)

Depends on / 依赖: Equiv.Finset.union, Finset, measurePreserving_piCongrLeft, measurePreserving_sumPiEquivProdPi_symm
-/
theorem measurePreserving_piFinsetUnion {ι : Type*} {α : ι -> Type*}
    {_ : forall i, MeasurableSpace (α i)} [DecidableEq ι] {s t : Finset ι} (h : Disjoint s t)
    (μ : forall i, Measure (α i)) [forall i, SigmaFinite (μ i)] :
    MeasurePreserving (MeasurableEquiv.piFinsetUnion α h)
      ((Measure.pi fun i : s => μ i).prod (Measure.pi fun i : t => μ i))
      (Measure.pi fun i : ↥(s union t) => μ i) :=
  let e := Equiv.Finset.union s t h
.comp measurePreserving_piCongrLeft (fun i : ↥(s union t) => μ i) e
    measurePreserving_sumPiEquivProdPi_symm fun b => μ (e b)

/--
theorem `volume_preserving_piFinsetUnion` / 定理 `volume_preserving_piFinsetUnion`

English:
theorem volume_preserving_piFinsetUnion
  statement: {ι : Type*} [DecidableEq ι] (α : ι -> Type*) {s t : Finset ι}
  proof: measurePreserving_piFinsetUnion h (fun _ => volume)

中文:
定理 volume_preserving_piFinsetUnion
  结论: {ι : 类型} [DecidableEq ι] (α : ι -> 类型) {s t : 有限集 ι}
  证明: measurePreserving_piFinsetUnion h (fun _ => volume)

Depends on / 依赖: measurePreserving_piFinsetUnion, volume
-/
theorem volume_preserving_piFinsetUnion {ι : Type*} [DecidableEq ι] (α : ι -> Type*) {s t : Finset ι}
    (h : Disjoint s t) [forall i, MeasureSpace (α i)] [forall i, SigmaFinite (volume : Measure (α i))] :
    MeasurePreserving (MeasurableEquiv.piFinsetUnion α h) volume volume :=
  measurePreserving_piFinsetUnion h (fun _ => volume)

/--
theorem `measurePreserving_pi` / 定理 `measurePreserving_pi`

English:
theorem measurePreserving_pi
  statement: {ι : Type*} [Fintype ι] {α : ι -> Type v} {β : ι -> Type*}
  proof: measurable_pi_iff.mpr fun i => (hf i).measurable.comp (measurable_pi_apply i)
  map_eq := by
    have (i : ι) : SigmaFinite ((μ i).map (f i)) := (hf i).map_eq ▸ hν i
    rw [pi_map_pi (fun i => (hf i).aemeasurable)]
exact congrArg _ funext fun i => (hf i).map_eq

中文:
定理 measurePreserving_pi
  结论: {ι : 类型} [有限类型 ι] {α : ι -> 类型v} {β : ι -> 类型}
  证明: measurable_pi_iff.mpr fun i => (hf i).measurable.comp (measurable_pi_apply i)
  map_eq := by
    have (i : ι) : SigmaFinite ((μ i).map (f i)) := (hf i).map_eq ▸ hν i
    rw [pi_map_pi (fun i => (hf i).aemeasurable)]
exact congrArg _ funext fun i => (hf i).map_eq

Depends on / 依赖: SigmaFinite, aemeasurable, map_eq, measurable, measurable.comp, measurable_pi_apply, measurable_pi_iff, measurable_pi_iff.mpr, pi_map_pi
-/
theorem measurePreserving_pi {ι : Type*} [Fintype ι] {α : ι -> Type v} {β : ι -> Type*}
    [forall i, MeasurableSpace (α i)] [forall i, MeasurableSpace (β i)]
    (μ : (i : ι) -> Measure (α i)) (ν : (i : ι) -> Measure (β i))
    {f : (i : ι) -> (α i) -> (β i)} [hν : forall i, SigmaFinite (ν i)]
    (hf : forall i, MeasurePreserving (f i) (μ i) (ν i)) :
    MeasurePreserving (fun a i => f i (a i)) (Measure.pi μ) (Measure.pi ν) where
  measurable :=
measurable_pi_iff.mpr fun i => (hf i).measurable.comp (measurable_pi_apply i)
  map_eq := by
    have (i : ι) : SigmaFinite ((μ i).map (f i)) := (hf i).map_eq ▸ hν i
    rw [pi_map_pi (fun i => (hf i).aemeasurable)]
exact congrArg _ funext fun i => (hf i).map_eq

/--
theorem `volume_preserving_pi` / 定理 `volume_preserving_pi`

English:
theorem volume_preserving_pi
  statement: {α' β' : ι -> Type*} [forall i, MeasureSpace (α' i)]
  proof: measurePreserving_pi _ _ hf

中文:
定理 volume_preserving_pi
  结论: {α' β' : ι -> 类型} [对任意 i, 测度空间 (α' i)]
  证明: measurePreserving_pi _ _ hf

Depends on / 依赖: measurePreserving_pi
-/
theorem volume_preserving_pi {α' β' : ι -> Type*} [forall i, MeasureSpace (α' i)]
    [forall i, MeasureSpace (β' i)] [forall i, SigmaFinite (volume : Measure (β' i))]
    {f : (i : ι) -> (α' i) -> (β' i)} (hf : forall i, MeasurePreserving (f i)) :
    MeasurePreserving (fun (a : (i : ι) -> α' i) (i : ι) => (f i) (a i)) :=
  measurePreserving_pi _ _ hf

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `measurePreserving_arrowCongr'` / 定理 `measurePreserving_arrowCongr'`

English:
theorem measurePreserving_arrowCongr'
  statement: {α₁ β₁ α₂ β₂ : Type*} [Fintype α₁] [Fintype α₂]
  proof: by
  convert!
    (measurePreserving_piCongrLeft (fun i : α₂ => ν i) eα).comp
      (measurePreserving_pi μ (fun i : α₁ => ν (eα i)) hm)
  simp only [MeasurableEquiv.arrowCongr', Equiv.arrowCongr', Equiv.arrowCongr, EquivLike.coe_coe,
    comp_def, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, Measurable

中文:
定理 measurePreserving_arrowCongr'
  结论: {α₁ β₁ α₂ β₂ : 类型} [有限类型 α₁] [有限类型 α₂]
  证明: by
  convert!
    (measurePreserving_piCongrLeft (fun i : α₂ => ν i) eα).comp
      (measurePreserving_pi μ (fun i : α₁ => ν (eα i)) hm)
  simp only [MeasurableEquiv.arrowCongr', Equiv.arrowCongr', Equiv.arrowCongr, EquivLike.coe_coe,
    comp_def, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, Measurable

Depends on / 依赖: Equiv.arrowCongr, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, Equiv.piCongrLeft, Equiv.symm_symm, EquivLike, EquivLike.coe_coe, MeasurableEquiv, MeasurableEquiv.arrowCongr, MeasurableEquiv.coe_mk, MeasurableEquiv.piCongrLeft, arrowCongr, coe_coe, coe_fn_mk, coe_fn_symm_mk, coe_mk, comp_def, convert, eq_rec_constant, measurePreserving_pi
-/
theorem measurePreserving_arrowCongr' {α₁ β₁ α₂ β₂ : Type*} [Fintype α₁] [Fintype α₂]
    [MeasurableSpace β₁] [MeasurableSpace β₂] (μ : α₁ -> Measure β₁) (ν : α₂ -> Measure β₂)
    [forall i, SigmaFinite (ν i)] (eα : α₁ ≃ α₂) (eβ : β₁ ≃ᵐ β₂)
    (hm : forall i, MeasurePreserving eβ (μ i) (ν (eα i))) :
    MeasurePreserving (MeasurableEquiv.arrowCongr' eα eβ) (Measure.pi fun i => μ i)
      (Measure.pi fun i => ν i) := by
  convert!
    (measurePreserving_piCongrLeft (fun i : α₂ => ν i) eα).comp
      (measurePreserving_pi μ (fun i : α₁ => ν (eα i)) hm)
  simp only [MeasurableEquiv.arrowCongr', Equiv.arrowCongr', Equiv.arrowCongr, EquivLike.coe_coe,
    comp_def, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, MeasurableEquiv.piCongrLeft,
    Equiv.piCongrLeft, Equiv.symm_symm, Equiv.piCongrLeft', eq_rec_constant, Equiv.coe_fn_symm_mk]

/--
theorem `volume_preserving_arrowCongr'` / 定理 `volume_preserving_arrowCongr'`

English:
theorem volume_preserving_arrowCongr'
  statement: {α₁ β₁ α₂ β₂ : Type*} [Fintype α₁] [Fintype α₂]
  proof: measurePreserving_arrowCongr' (fun _ => volume) (fun _ => volume) hα hβ (fun _ => hm)

中文:
定理 volume_preserving_arrowCongr'
  结论: {α₁ β₁ α₂ β₂ : 类型} [有限类型 α₁] [有限类型 α₂]
  证明: measurePreserving_arrowCongr' (fun _ => volume) (fun _ => volume) hα hβ (fun _ => hm)

Depends on / 依赖: measurePreserving_arrowCongr, volume
-/
theorem volume_preserving_arrowCongr' {α₁ β₁ α₂ β₂ : Type*} [Fintype α₁] [Fintype α₂]
    [MeasureSpace β₁] [MeasureSpace β₂] [SigmaFinite (volume : Measure β₂)]
    (hα : α₁ ≃ α₂) (hβ : β₁ ≃ᵐ β₂) (hm : MeasurePreserving hβ) :
    MeasurePreserving (MeasurableEquiv.arrowCongr' hα hβ) :=
  measurePreserving_arrowCongr' (fun _ => volume) (fun _ => volume) hα hβ (fun _ => hm)

end MeasurePreserving

end MeasureTheory
