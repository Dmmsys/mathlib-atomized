/-
Copyright (c) 2023 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Marginals of multivariate functions

In this file, we define a convenient way to compute integrals of multivariate functions, especially
if you want to write expressions where you integrate only over some of the variables that the
function depends on. This is common in induction arguments involving integrals of multivariate
functions.
This constructions allows working with iterated integrals and applying Tonelli's theorem
and Fubini's theorem, without using measurable equivalences by changing the representation of your
space (e.g. `((ι ⊕ ι') → ℝ) ≃ (ι → ℝ) × (ι' → ℝ)`).

## Main Definitions

* Assume that `∀ i : ι, X i` is a product of measurable spaces with measures `μ i` on `X i`,
  `f : (∀ i, X i) → ℝ≥0∞` is a function and `s : Finset ι`.
  Then `lmarginal μ s f` or `∫⋯∫⁻_s, f ∂μ` is the function that integrates `f`
  over all variables in `s`. It returns a function that still takes the same variables as `f`,
  but is constant in the variables in `s`. Mathematically, if `s = {i₁, ..., iₖ}`,
  then `lmarginal μ s f` is the expression
  $$
  \vec{x}\mapsto \int\!\!\cdots\!\!\int f(\vec{x}[\vec{y}])dy_{i_1}\cdots dy_{i_k}.
  $$
  where $\vec{x}[\vec{y}]$ is the vector $\vec{x}$ with $x_{i_j}$ replaced by $y_{i_j}$ for all
  $1 \le j \le k$.
  If `f` is the distribution of a random variable, this is the marginal distribution of all
  variables not in `s` (but not the most general notion, since we only consider product measures
  here).
  Note that the notation `∫⋯∫⁻_s, f ∂μ` is not a binder, and returns a function.

## Main Results

* `lmarginal_union` is the analogue of Tonelli's theorem for iterated integrals. It states that
  for measurable functions `f` and disjoint finsets `s` and `t` we have
  `∫⋯∫⁻_s ∪ t, f ∂μ = ∫⋯∫⁻_s, ∫⋯∫⁻_t, f ∂μ ∂μ`.

## Implementation notes

The function `f` can have an arbitrary product as its domain (even infinite products), but the
set `s` of integration variables is a `Finset`. We are assuming that the function `f` is measurable
for most of this file. Note that asking whether it is `AEMeasurable` is not even well-posed,
since there is no well-behaved measure on the domain of `f`.

## TODO

* Define the marginal function for functions taking values in a Banach space.

-/

@[expose] public section


open scoped ENNReal
open Set Function Equiv Finset

noncomputable section

namespace MeasureTheory

section LMarginal

variable {δ δ' : Type*} {X : δ -> Type*} [forall i, MeasurableSpace (X i)]
variable {μ : forall i, Measure (X i)} [DecidableEq δ]
variable {s t : Finset δ} {f : (forall i, X i) -> Real>=0∞} {x : forall i, X i}

/--
Definition of `lmarginal` / `lmarginal` 的定义

English:
definition lmarginal
  signature: (μ : forall i, Measure (X i)) (s : Finset δ) (f : (forall i, X i) -> Real>=0∞)
  body: ∫⁻ y : forall i : s, X i, f (updateFinset x s y) ∂Measure.pi fun i : s => μ i

中文:
定义 lmarginal
  签名: (μ : 对任意 i, 测度 (X i)) (s : 有限集 δ) (f : (对任意 i, X i) -> 实数>=0∞)
  定义体: ∫⁻ y : forall i : s, X i, f (updateFinset x s y) ∂Measure.pi fun i : s => μ i

Depends on / 依赖: Measure, Measure.pi, updateFinset
-/
def lmarginal (μ : forall i, Measure (X i)) (s : Finset δ) (f : (forall i, X i) -> Real>=0∞)
    (x : forall i, X i) : Real>=0∞ :=
  ∫⁻ y : forall i : s, X i, f (updateFinset x s y) ∂Measure.pi fun i : s => μ i

-- Note: this notation is not a binder. This is more convenient since it returns a function.
@[inherit_doc]
notation "∫⋯∫⁻_" s ", " f " ∂" μ:70 => lmarginal μ s f

@[inherit_doc lmarginal]
notation3 "∫⋯∫⁻_" s ", " f => lmarginal (fun _ => volume) s f

variable (μ)

/--
theorem `_root_.Measurable.lmarginal` / 定理 `_root_.Measurable.lmarginal`

English:
theorem _root_.Measurable.lmarginal
  given: [forall i, SigmaFinite (μ i)] (hf : Measurable f)
  proof: Measurable.lintegral_prod_right (hf.comp measurable_updateFinset')

中文:
定理 _root_.可测.lmarginal
  条件: [对任意 i, σ有限 (μ i)] (hf : 可测 f)
  证明: Measurable.lintegral_prod_right (hf.comp measurable_updateFinset')

Depends on / 依赖: Measurable, Measurable.lintegral_prod_right, hf.comp, lintegral_prod_right, measurable_updateFinset
-/
theorem _root_.Measurable.lmarginal [forall i, SigmaFinite (μ i)] (hf : Measurable f) :
    Measurable (∫⋯∫⁻_s, f ∂μ) :=
  Measurable.lintegral_prod_right (hf.comp measurable_updateFinset')

/--
theorem `lmarginal_empty` / 定理 `lmarginal_empty`

English:
theorem lmarginal_empty
  given: (f : (forall i, X i) -> Real>=0∞)
  statement: ∫⋯∫⁻_∅, f ∂μ = f
  proof: by
  ext1 x
  simp_rw [lmarginal, Measure.pi_of_empty fun i : (∅ : Finset δ) => μ i]
  apply lintegral_dirac'
  exact Subsingleton.measurable

中文:
定理 lmarginal_empty
  条件: (f : (对任意 i, X i) -> 实数>=0∞)
  结论: ∫⋯∫⁻_∅, f ∂μ = f
  证明: by
  ext1 x
  simp_rw [lmarginal, Measure.pi_of_empty fun i : (∅ : Finset δ) => μ i]
  apply lintegral_dirac'
  exact Subsingleton.measurable
-/
@[simp] theorem lmarginal_empty (f : (forall i, X i) -> Real>=0∞) : ∫⋯∫⁻_∅, f ∂μ = f := by
  ext1 x
  simp_rw [lmarginal, Measure.pi_of_empty fun i : (∅ : Finset δ) => μ i]
  apply lintegral_dirac'
  exact Subsingleton.measurable

/--
theorem `lmarginal_congr` / 定理 `lmarginal_congr`

English:
theorem lmarginal_congr
  statement: {x y : forall i, X i} (f : (forall i, X i) -> Real>=0∞)
  proof: by
  dsimp [lmarginal, updateFinset_def]; rcongr; exact h _ ‹_›

中文:
定理 lmarginal_congr
  结论: {x y : 对任意 i, X i} (f : (对任意 i, X i) -> 实数>=0∞)
  证明: by
  dsimp [lmarginal, updateFinset_def]; rcongr; exact h _ ‹_›

Depends on / 依赖: lmarginal, rcongr, updateFinset_def
-/
theorem lmarginal_congr {x y : forall i, X i} (f : (forall i, X i) -> Real>=0∞)
    (h : forall i ∉ s, x i = y i) :
    (∫⋯∫⁻_s, f ∂μ) x = (∫⋯∫⁻_s, f ∂μ) y := by
  dsimp [lmarginal, updateFinset_def]; rcongr; exact h _ ‹_›

/--
theorem `lmarginal_update_of_mem` / 定理 `lmarginal_update_of_mem`

English:
theorem lmarginal_update_of_mem
  statement: {i : δ} (hi : i in s)
  proof: by
  grind [MeasureTheory.lmarginal_congr]

中文:
定理 lmarginal_update_of_mem
  结论: {i : δ} (hi : i in s)
  证明: by
  grind [MeasureTheory.lmarginal_congr]

Depends on / 依赖: MeasureTheory, MeasureTheory.lmarginal_congr, lmarginal_congr
-/
theorem lmarginal_update_of_mem {i : δ} (hi : i in s)
    (f : (forall i, X i) -> Real>=0∞) (x : forall i, X i) (y : X i) :
    (∫⋯∫⁻_s, f ∂μ) (Function.update x i y) = (∫⋯∫⁻_s, f ∂μ) x := by
  grind [MeasureTheory.lmarginal_congr]

variable {μ} in
/--
theorem `lmarginal_singleton` / 定理 `lmarginal_singleton`

English:
theorem lmarginal_singleton
  given: (f : (forall i, X i) -> Real>=0∞) (i : δ)
  proof: by
  let α : Type _ := ({i} : Finset δ)
  let e := (MeasurableEquiv.piUnique fun j : α => X j).symm
  ext1 x
  calc (∫⋯∫⁻_{i}, f ∂μ) x
      = ∫⁻ (y : X (default : α)), f (updateFinset x {i} (e y)) ∂μ (default : α) := by
        simp_rw [lmarginal,
.symm _ measurePreserving_piUnique (fun j : ({i} : 

中文:
定理 lmarginal_singleton
  条件: (f : (对任意 i, X i) -> 实数>=0∞) (i : δ)
  证明: by
  let α : Type _ := ({i} : Finset δ)
  let e := (MeasurableEquiv.piUnique fun j : α => X j).symm
  ext1 x
  calc (∫⋯∫⁻_{i}, f ∂μ) x
      = ∫⁻ (y : X (default : α)), f (updateFinset x {i} (e y)) ∂μ (default : α) := by
        simp_rw [lmarginal,
.symm _ measurePreserving_piUnique (fun j : ({i} : 

Depends on / 依赖: Finset, Function, Function.update, MeasurableEquiv, MeasurableEquiv.piUnique, lintegral_map_equiv, lmarginal, measurePreserving_piUnique, piUnique, simp_rw, update, updateFinset, update_eq_updateFinset
-/
theorem lmarginal_singleton (f : (forall i, X i) -> Real>=0∞) (i : δ) :
    ∫⋯∫⁻_{i}, f ∂μ = fun x => ∫⁻ xᵢ, f (Function.update x i xᵢ) ∂μ i := by
  let α : Type _ := ({i} : Finset δ)
  let e := (MeasurableEquiv.piUnique fun j : α => X j).symm
  ext1 x
  calc (∫⋯∫⁻_{i}, f ∂μ) x
      = ∫⁻ (y : X (default : α)), f (updateFinset x {i} (e y)) ∂μ (default : α) := by
        simp_rw [lmarginal,
.symm _ measurePreserving_piUnique (fun j : ({i} : Finset δ) => μ j)
.lintegral_map_equiv, e, α]
    _ = ∫⁻ xᵢ, f (Function.update x i xᵢ) ∂μ i := by simp [update_eq_updateFinset]; rfl

variable {μ} in
@[gcongr]
/--
theorem `lmarginal_mono` / 定理 `lmarginal_mono`

English:
theorem lmarginal_mono
  given: {f g : (forall i, X i) -> Real>=0∞} (hfg : f <= g)
  statement: ∫⋯∫⁻_s, f ∂μ <= ∫⋯∫⁻_s, g ∂μ
  proof: fun _ => lintegral_mono fun _ => hfg _

中文:
定理 lmarginal_mono
  条件: {f g : (对任意 i, X i) -> 实数>=0∞} (hfg : f <= g)
  结论: ∫⋯∫⁻_s, f ∂μ <= ∫⋯∫⁻_s, g ∂μ
  证明: fun _ => lintegral_mono fun _ => hfg _

Depends on / 依赖: lintegral_mono
-/
theorem lmarginal_mono {f g : (forall i, X i) -> Real>=0∞} (hfg : f <= g) : ∫⋯∫⁻_s, f ∂μ <= ∫⋯∫⁻_s, g ∂μ :=
  fun _ => lintegral_mono fun _ => hfg _

variable [forall i, SigmaFinite (μ i)]

/--
theorem `lmarginal_union` / 定理 `lmarginal_union`

English:
theorem lmarginal_union
  statement: (f : (forall i, X i) -> Real>=0∞) (hf : Measurable f)
  proof: by
  ext1 x
  let e := MeasurableEquiv.piFinsetUnion X hst
  calc (∫⋯∫⁻_s union t, f ∂μ) x
      = ∫⁻ (y : (i : ↥(s union t)) -> X i), f (updateFinset x (s union t) y)
          ∂.pi fun i' : ↥(s union t) => μ i' := rfl
    _ = ∫⁻ (y : ((i : s) -> X i) × ((j : t) -> X j)), f (updateFinset x (s union

中文:
定理 lmarginal_union
  结论: (f : (对任意 i, X i) -> 实数>=0∞) (hf : 可测 f)
  证明: by
  ext1 x
  let e := MeasurableEquiv.piFinsetUnion X hst
  calc (∫⋯∫⁻_s union t, f ∂μ) x
      = ∫⁻ (y : (i : ↥(s union t)) -> X i), f (updateFinset x (s union t) y)
          ∂.pi fun i' : ↥(s union t) => μ i' := rfl
    _ = ∫⁻ (y : ((i : s) -> X i) × ((j : t) -> X j)), f (updateFinset x (s union

Depends on / 依赖: MeasurableEquiv, MeasurableEquiv.piFinsetUnion, Measure, Measure.pi, lintegral_map_equiv, measurePreserving_piFinsetUnion, piFinsetUnion, updateFinset
-/
theorem lmarginal_union (f : (forall i, X i) -> Real>=0∞) (hf : Measurable f)
    (hst : Disjoint s t) : ∫⋯∫⁻_s union t, f ∂μ = ∫⋯∫⁻_s, ∫⋯∫⁻_t, f ∂μ ∂μ := by
  ext1 x
  let e := MeasurableEquiv.piFinsetUnion X hst
  calc (∫⋯∫⁻_s union t, f ∂μ) x
      = ∫⁻ (y : (i : ↥(s union t)) -> X i), f (updateFinset x (s union t) y)
          ∂.pi fun i' : ↥(s union t) => μ i' := rfl
    _ = ∫⁻ (y : ((i : s) -> X i) × ((j : t) -> X j)), f (updateFinset x (s union t) _)
          ∂(Measure.pi fun i : s => μ i).prod (.pi fun j : t => μ j) := by
        rw [measurePreserving_piFinsetUnion hst μ |>.lintegral_map_equiv]
    _ = ∫⁻ (y : (i : s) -> X i), ∫⁻ (z : (j : t) -> X j), f (updateFinset x (s union t) (e (y, z)))
          ∂.pi fun j : t => μ j ∂.pi fun i : s => μ i := by
        apply lintegral_prod
        apply Measurable.aemeasurable
exact hf.comp measurable_updateFinset.comp e.measurable
    _ = (∫⋯∫⁻_s, ∫⋯∫⁻_t, f ∂μ ∂μ) x := by
        simp_rw [lmarginal, updateFinset_updateFinset hst]
        rfl

/--
theorem `lmarginal_union'` / 定理 `lmarginal_union'`

English:
theorem lmarginal_union'
  statement: (f : (forall i, X i) -> Real>=0∞) (hf : Measurable f) {s t : Finset δ}
  proof: by
  rw [Finset.union_comm]; rw [lmarginal_union μ f hf hst.symm]

中文:
定理 lmarginal_union'
  结论: (f : (对任意 i, X i) -> 实数>=0∞) (hf : 可测 f) {s t : 有限集 δ}
  证明: by
  rw [Finset.union_comm]; rw [lmarginal_union μ f hf hst.symm]

Depends on / 依赖: Finset, Finset.union_comm, hst.symm, lmarginal_union, union_comm
-/
theorem lmarginal_union' (f : (forall i, X i) -> Real>=0∞) (hf : Measurable f) {s t : Finset δ}
    (hst : Disjoint s t) : ∫⋯∫⁻_s union t, f ∂μ = ∫⋯∫⁻_t, ∫⋯∫⁻_s, f ∂μ ∂μ := by
  rw [Finset.union_comm]; rw [lmarginal_union μ f hf hst.symm]

variable {μ}

/--
theorem `lmarginal_insert` / 定理 `lmarginal_insert`

English:
theorem lmarginal_insert
  statement: (f : (forall i, X i) -> Real>=0∞) (hf : Measurable f) {i : δ}
  proof: by
  rw [Finset.insert_eq]; rw [lmarginal_union μ f hf (Finset.disjoint_singleton_left.mpr hi)]; rw [lmarginal_singleton]

中文:
定理 lmarginal_insert
  结论: (f : (对任意 i, X i) -> 实数>=0∞) (hf : 可测 f) {i : δ}
  证明: by
  rw [Finset.insert_eq]; rw [lmarginal_union μ f hf (Finset.disjoint_singleton_left.mpr hi)]; rw [lmarginal_singleton]

Depends on / 依赖: Finset, Finset.disjoint_singleton_left.mpr, Finset.insert_eq, disjoint_singleton_left, insert_eq, lmarginal_singleton, lmarginal_union
-/
theorem lmarginal_insert (f : (forall i, X i) -> Real>=0∞) (hf : Measurable f) {i : δ}
    (hi : i ∉ s) (x : forall i, X i) :
    (∫⋯∫⁻_insert i s, f ∂μ) x = ∫⁻ xᵢ, (∫⋯∫⁻_s, f ∂μ) (Function.update x i xᵢ) ∂μ i := by
  rw [Finset.insert_eq]; rw [lmarginal_union μ f hf (Finset.disjoint_singleton_left.mpr hi)]; rw [lmarginal_singleton]

/--
theorem `lmarginal_erase` / 定理 `lmarginal_erase`

English:
theorem lmarginal_erase
  statement: (f : (forall i, X i) -> Real>=0∞) (hf : Measurable f) {i : δ}
  proof: by
  simpa [insert_erase hi] using lmarginal_insert _ hf (notMem_erase i s) x

中文:
定理 lmarginal_erase
  结论: (f : (对任意 i, X i) -> 实数>=0∞) (hf : 可测 f) {i : δ}
  证明: by
  simpa [insert_erase hi] using lmarginal_insert _ hf (notMem_erase i s) x

Depends on / 依赖: insert_erase, lmarginal_insert, notMem_erase
-/
theorem lmarginal_erase (f : (forall i, X i) -> Real>=0∞) (hf : Measurable f) {i : δ}
    (hi : i in s) (x : forall i, X i) :
    (∫⋯∫⁻_s, f ∂μ) x = ∫⁻ xᵢ, (∫⋯∫⁻_(erase s i), f ∂μ) (Function.update x i xᵢ) ∂μ i := by
  simpa [insert_erase hi] using lmarginal_insert _ hf (notMem_erase i s) x

/--
theorem `lmarginal_insert'` / 定理 `lmarginal_insert'`

English:
theorem lmarginal_insert'
  statement: (f : (forall i, X i) -> Real>=0∞) (hf : Measurable f) {i : δ}
  proof: by
  rw [Finset.insert_eq]; rw [Finset.union_comm]; rw [lmarginal_union (s := s) μ f hf (Finset.disjoint_singleton_right.mpr hi)]; rw [lmarginal_singleton]

中文:
定理 lmarginal_insert'
  结论: (f : (对任意 i, X i) -> 实数>=0∞) (hf : 可测 f) {i : δ}
  证明: by
  rw [Finset.insert_eq]; rw [Finset.union_comm]; rw [lmarginal_union (s := s) μ f hf (Finset.disjoint_singleton_right.mpr hi)]; rw [lmarginal_singleton]

Depends on / 依赖: Finset, Finset.disjoint_singleton_right.mpr, Finset.insert_eq, Finset.union_comm, disjoint_singleton_right, insert_eq, lmarginal_singleton, lmarginal_union, union_comm
-/
theorem lmarginal_insert' (f : (forall i, X i) -> Real>=0∞) (hf : Measurable f) {i : δ}
    (hi : i ∉ s) :
    ∫⋯∫⁻_insert i s, f ∂μ = ∫⋯∫⁻_s, (fun x => ∫⁻ xᵢ, f (Function.update x i xᵢ) ∂μ i) ∂μ := by
  rw [Finset.insert_eq]; rw [Finset.union_comm]; rw [lmarginal_union (s := s) μ f hf (Finset.disjoint_singleton_right.mpr hi)]; rw [lmarginal_singleton]

/--
theorem `lmarginal_erase'` / 定理 `lmarginal_erase'`

English:
theorem lmarginal_erase'
  statement: (f : (forall i, X i) -> Real>=0∞) (hf : Measurable f) {i : δ}
  proof: by
  simpa [insert_erase hi] using lmarginal_insert' _ hf (notMem_erase i s)

中文:
定理 lmarginal_erase'
  结论: (f : (对任意 i, X i) -> 实数>=0∞) (hf : 可测 f) {i : δ}
  证明: by
  simpa [insert_erase hi] using lmarginal_insert' _ hf (notMem_erase i s)

Depends on / 依赖: insert_erase, lmarginal_insert, notMem_erase
-/
theorem lmarginal_erase' (f : (forall i, X i) -> Real>=0∞) (hf : Measurable f) {i : δ}
    (hi : i in s) :
    ∫⋯∫⁻_s, f ∂μ = ∫⋯∫⁻_(erase s i), (fun x => ∫⁻ xᵢ, f (Function.update x i xᵢ) ∂μ i) ∂μ := by
  simpa [insert_erase hi] using lmarginal_insert' _ hf (notMem_erase i s)

/--
theorem `lmarginal_univ` / 定理 `lmarginal_univ`

English:
theorem lmarginal_univ
  given: [Fintype δ] {f : (forall i, X i) -> Real>=0∞}
  proof: by
  let e : { j // j in Finset.univ } ≃ δ := Equiv.subtypeUnivEquiv mem_univ
  ext1 x
  simp_rw [lmarginal, measurePreserving_piCongrLeft μ e |>.lintegral_map_equiv, updateFinset_def]
  simp
  rfl

中文:
定理 lmarginal_univ
  条件: [有限类型 δ] {f : (对任意 i, X i) -> 实数>=0∞}
  证明: by
  let e : { j // j in Finset.univ } ≃ δ := Equiv.subtypeUnivEquiv mem_univ
  ext1 x
  simp_rw [lmarginal, measurePreserving_piCongrLeft μ e |>.lintegral_map_equiv, updateFinset_def]
  simp
  rfl
-/
@[simp] theorem lmarginal_univ [Fintype δ] {f : (forall i, X i) -> Real>=0∞} :
    ∫⋯∫⁻_univ, f ∂μ = fun _ => ∫⁻ x, f x ∂Measure.pi μ := by
  let e : { j // j in Finset.univ } ≃ δ := Equiv.subtypeUnivEquiv mem_univ
  ext1 x
  simp_rw [lmarginal, measurePreserving_piCongrLeft μ e |>.lintegral_map_equiv, updateFinset_def]
  simp
  rfl

/--
theorem `lintegral_eq_lmarginal_univ` / 定理 `lintegral_eq_lmarginal_univ`

English:
theorem lintegral_eq_lmarginal_univ
  given: [Fintype δ] {f : (forall i, X i) -> Real>=0∞} (x : forall i, X i)
  proof: by simp

中文:
定理 lintegral_eq_lmarginal_univ
  条件: [有限类型 δ] {f : (对任意 i, X i) -> 实数>=0∞} (x : 对任意 i, X i)
  证明: by simp
-/
theorem lintegral_eq_lmarginal_univ [Fintype δ] {f : (forall i, X i) -> Real>=0∞} (x : forall i, X i) :
    ∫⁻ x, f x ∂Measure.pi μ = (∫⋯∫⁻_univ, f ∂μ) x := by simp

/--
theorem `lmarginal_image` / 定理 `lmarginal_image`

English:
theorem lmarginal_image
  statement: [DecidableEq δ'] {e : δ' -> δ} (he : Injective e) (s : Finset δ')
  proof: by
  have h : Measurable ((· ∘' e) : (forall i, X i) -> _) :=
measurable_pi_iff.mpr fun i => measurable_pi_apply (e i)
  induction s using Finset.induction generalizing x with
  | empty => simp
  | insert _ _ hi ih =>
    rw [image_insert]; rw [lmarginal_insert _ (hf.comp h) (he.mem_finset_image.not

中文:
定理 lmarginal_image
  结论: [DecidableEq δ'] {e : δ' -> δ} (he : 单射 e) (s : 有限集 δ')
  证明: by
  have h : Measurable ((· ∘' e) : (forall i, X i) -> _) :=
measurable_pi_iff.mpr fun i => measurable_pi_apply (e i)
  induction s using Finset.induction generalizing x with
  | empty => simp
  | insert _ _ hi ih =>
    rw [image_insert]; rw [lmarginal_insert _ (hf.comp h) (he.mem_finset_image.not

Depends on / 依赖: Finset, Finset.induction, Measurable, generalizing, he.mem_finset_image.not.mpr, hf.comp, image_insert, insert, lmarginal_insert, measurable_pi_apply, measurable_pi_iff, measurable_pi_iff.mpr, mem_finset_image, simp_rw, update_comp_eq_of_injective
-/
theorem lmarginal_image [DecidableEq δ'] {e : δ' -> δ} (he : Injective e) (s : Finset δ')
    {f : (forall i, X (e i)) -> Real>=0∞} (hf : Measurable f) (x : forall i, X i) :
      (∫⋯∫⁻_s.image e, f ∘ (· ∘' e) ∂μ) x = (∫⋯∫⁻_s, f ∂μ ∘' e) (x ∘' e) := by
  have h : Measurable ((· ∘' e) : (forall i, X i) -> _) :=
measurable_pi_iff.mpr fun i => measurable_pi_apply (e i)
  induction s using Finset.induction generalizing x with
  | empty => simp
  | insert _ _ hi ih =>
    rw [image_insert]; rw [lmarginal_insert _ (hf.comp h) (he.mem_finset_image.not.mpr hi)]; rw [lmarginal_insert _ hf hi]
    simp_rw [ih, ← update_comp_eq_of_injective' x he]

/--
theorem `lmarginal_update_of_notMem` / 定理 `lmarginal_update_of_notMem`

English:
theorem lmarginal_update_of_notMem
  statement: {i : δ}
  proof: by
  induction s using Finset.induction generalizing x with
  | empty => simp
  | insert i' s hi' ih =>
    rw [lmarginal_insert _ hf hi']; rw [lmarginal_insert _ (hf.comp measurable_update_left) hi']
    have hii' : i != i' := mt (by rintro rfl; exact mem_insert_self i s) hi
    simp_rw [update_com

中文:
定理 lmarginal_update_of_notMem
  结论: {i : δ}
  证明: by
  induction s using Finset.induction generalizing x with
  | empty => simp
  | insert i' s hi' ih =>
    rw [lmarginal_insert _ hf hi']; rw [lmarginal_insert _ (hf.comp measurable_update_left) hi']
    have hii' : i != i' := mt (by rintro rfl; exact mem_insert_self i s) hi
    simp_rw [update_com

Depends on / 依赖: Finset, Finset.induction, Finset.mem_insert_of_mem, generalizing, hf.comp, insert, lmarginal_insert, measurable_update_left, mem_insert_of_mem, mem_insert_self, simp_rw, update_comm
-/
theorem lmarginal_update_of_notMem {i : δ}
    {f : (forall i, X i) -> Real>=0∞} (hf : Measurable f) (hi : i ∉ s) (x : forall i, X i) (y : X i) :
    (∫⋯∫⁻_s, f ∂μ) (Function.update x i y) = (∫⋯∫⁻_s, f ∘ (Function.update · i y) ∂μ) x := by
  induction s using Finset.induction generalizing x with
  | empty => simp
  | insert i' s hi' ih =>
    rw [lmarginal_insert _ hf hi']; rw [lmarginal_insert _ (hf.comp measurable_update_left) hi']
    have hii' : i != i' := mt (by rintro rfl; exact mem_insert_self i s) hi
    simp_rw [update_comm hii', ih (mt Finset.mem_insert_of_mem hi)]

/--
theorem `lmarginal_eq_of_subset` / 定理 `lmarginal_eq_of_subset`

English:
theorem lmarginal_eq_of_subset
  statement: {f g : (forall i, X i) -> Real>=0∞} (hst : s subseteq t)
  proof: by
  rw [← union_sdiff_of_subset hst]; rw [lmarginal_union' μ f hf disjoint_sdiff]; rw [lmarginal_union' μ g hg disjoint_sdiff]; rw [hfg]

中文:
定理 lmarginal_eq_of_subset
  结论: {f g : (对任意 i, X i) -> 实数>=0∞} (hst : s subseteq t)
  证明: by
  rw [← union_sdiff_of_subset hst]; rw [lmarginal_union' μ f hf disjoint_sdiff]; rw [lmarginal_union' μ g hg disjoint_sdiff]; rw [hfg]

Depends on / 依赖: disjoint_sdiff, lmarginal_union, union_sdiff_of_subset
-/
theorem lmarginal_eq_of_subset {f g : (forall i, X i) -> Real>=0∞} (hst : s subseteq t)
    (hf : Measurable f) (hg : Measurable g) (hfg : ∫⋯∫⁻_s, f ∂μ = ∫⋯∫⁻_s, g ∂μ) :
    ∫⋯∫⁻_t, f ∂μ = ∫⋯∫⁻_t, g ∂μ := by
  rw [← union_sdiff_of_subset hst]; rw [lmarginal_union' μ f hf disjoint_sdiff]; rw [lmarginal_union' μ g hg disjoint_sdiff]; rw [hfg]

/--
theorem `lmarginal_le_of_subset` / 定理 `lmarginal_le_of_subset`

English:
theorem lmarginal_le_of_subset
  statement: {f g : (forall i, X i) -> Real>=0∞} (hst : s subseteq t)
  proof: by
  rw [← union_sdiff_of_subset hst]; rw [lmarginal_union' μ f hf disjoint_sdiff]; rw [lmarginal_union' μ g hg disjoint_sdiff]
  exact lmarginal_mono hfg

中文:
定理 lmarginal_le_of_subset
  结论: {f g : (对任意 i, X i) -> 实数>=0∞} (hst : s subseteq t)
  证明: by
  rw [← union_sdiff_of_subset hst]; rw [lmarginal_union' μ f hf disjoint_sdiff]; rw [lmarginal_union' μ g hg disjoint_sdiff]
  exact lmarginal_mono hfg

Depends on / 依赖: disjoint_sdiff, lmarginal_mono, lmarginal_union, union_sdiff_of_subset
-/
theorem lmarginal_le_of_subset {f g : (forall i, X i) -> Real>=0∞} (hst : s subseteq t)
    (hf : Measurable f) (hg : Measurable g) (hfg : ∫⋯∫⁻_s, f ∂μ <= ∫⋯∫⁻_s, g ∂μ) :
    ∫⋯∫⁻_t, f ∂μ <= ∫⋯∫⁻_t, g ∂μ := by
  rw [← union_sdiff_of_subset hst]; rw [lmarginal_union' μ f hf disjoint_sdiff]; rw [lmarginal_union' μ g hg disjoint_sdiff]
  exact lmarginal_mono hfg

/--
theorem `lintegral_eq_of_lmarginal_eq` / 定理 `lintegral_eq_of_lmarginal_eq`

English:
theorem lintegral_eq_of_lmarginal_eq
  statement: [Fintype δ] (s : Finset δ) {f g : (forall i, X i) -> Real>=0∞}
  proof: by
  rcases isEmpty_or_nonempty (forall i, X i) with h | ⟨⟨x⟩⟩
  · simp_rw [lintegral_of_isEmpty]
  simp_rw [lintegral_eq_lmarginal_univ x, lmarginal_eq_of_subset (Finset.subset_univ s) hf hg hfg]

中文:
定理 lintegral_eq_of_lmarginal_eq
  结论: [有限类型 δ] (s : 有限集 δ) {f g : (对任意 i, X i) -> 实数>=0∞}
  证明: by
  rcases isEmpty_or_nonempty (forall i, X i) with h | ⟨⟨x⟩⟩
  · simp_rw [lintegral_of_isEmpty]
  simp_rw [lintegral_eq_lmarginal_univ x, lmarginal_eq_of_subset (Finset.subset_univ s) hf hg hfg]

Depends on / 依赖: Finset, Finset.subset_univ, isEmpty_or_nonempty, lintegral_eq_lmarginal_univ, lintegral_of_isEmpty, lmarginal_eq_of_subset, simp_rw, subset_univ
-/
theorem lintegral_eq_of_lmarginal_eq [Fintype δ] (s : Finset δ) {f g : (forall i, X i) -> Real>=0∞}
    (hf : Measurable f) (hg : Measurable g) (hfg : ∫⋯∫⁻_s, f ∂μ = ∫⋯∫⁻_s, g ∂μ) :
    ∫⁻ x, f x ∂Measure.pi μ = ∫⁻ x, g x ∂Measure.pi μ := by
  rcases isEmpty_or_nonempty (forall i, X i) with h | ⟨⟨x⟩⟩
  · simp_rw [lintegral_of_isEmpty]
  simp_rw [lintegral_eq_lmarginal_univ x, lmarginal_eq_of_subset (Finset.subset_univ s) hf hg hfg]

/--
theorem `lintegral_le_of_lmarginal_le` / 定理 `lintegral_le_of_lmarginal_le`

English:
theorem lintegral_le_of_lmarginal_le
  statement: [Fintype δ] (s : Finset δ) {f g : (forall i, X i) -> Real>=0∞}
  proof: by
  rcases isEmpty_or_nonempty (forall i, X i) with h | ⟨⟨x⟩⟩
  · simp_rw [lintegral_of_isEmpty, le_rfl]
  simp_rw [lintegral_eq_lmarginal_univ x, lmarginal_le_of_subset (Finset.subset_univ s) hf hg hfg x]

中文:
定理 lintegral_le_of_lmarginal_le
  结论: [有限类型 δ] (s : 有限集 δ) {f g : (对任意 i, X i) -> 实数>=0∞}
  证明: by
  rcases isEmpty_or_nonempty (forall i, X i) with h | ⟨⟨x⟩⟩
  · simp_rw [lintegral_of_isEmpty, le_rfl]
  simp_rw [lintegral_eq_lmarginal_univ x, lmarginal_le_of_subset (Finset.subset_univ s) hf hg hfg x]

Depends on / 依赖: Finset, Finset.subset_univ, IsDirected, Std.Total, Std.Total.to_isDirected, isEmpty_or_nonempty, le_rfl, lintegral_eq_lmarginal_univ, lintegral_of_isEmpty, lmarginal_le_of_subset, simp_rw, subset_univ, to_isDirected
-/
theorem lintegral_le_of_lmarginal_le [Fintype δ] (s : Finset δ) {f g : (forall i, X i) -> Real>=0∞}
    (hf : Measurable f) (hg : Measurable g) (hfg : ∫⋯∫⁻_s, f ∂μ <= ∫⋯∫⁻_s, g ∂μ) :
    ∫⁻ x, f x ∂Measure.pi μ <= ∫⁻ x, g x ∂Measure.pi μ := by
  rcases isEmpty_or_nonempty (forall i, X i) with h | ⟨⟨x⟩⟩
  · simp_rw [lintegral_of_isEmpty, le_rfl]
  simp_rw [lintegral_eq_lmarginal_univ x, lmarginal_le_of_subset (Finset.subset_univ s) hf hg hfg x]

end LMarginal

end MeasureTheory
