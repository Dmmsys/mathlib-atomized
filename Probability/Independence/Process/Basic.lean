/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.MeasureTheory.Constructions.Cylinders
public import Mathlib.Probability.Independence.Basic

/-!
# Independence of stochastic processes

We prove that a stochastic process $(X_s)_{s \in S}$ is independent from a random variable $Y$ if
for all $s_1, ..., s_p \in S$ the family $(X_{s_1}, ..., X_{s_p})$ is independent from $Y$.

We prove that two stochastic processes $(X_s)_{s \in S}$ and $(Y_t)_{t \in T}$ are independent if
for all $s_1, ..., s_p \in S$ and $t_1, ..., t_q \in T$ the two families
$(X_{s_1}, ..., X_{s_p})$ and $(Y_{t_1}, ..., Y_{t_q})$ are independent.
We prove an analogous condition for a family of stochastic processes.

## Tags

independence, stochastic processes
-/

public section

open MeasureTheory MeasurableSpace Set

namespace ProbabilityTheory

variable {S T Ω : Type*} {mΩ : MeasurableSpace Ω}

namespace Kernel

variable {α : Type*} {mα : MeasurableSpace α} {κ : Kernel α Ω} {P : Measure α}

/--
lemma `IndepFun.process_congr_left` / 引理 `IndepFun.process_congr_left`

English:
lemma IndepFun.process_congr_left
  statement: {𝓧 : S -> Type*} {𝓨 : Type*}
  proof: by
  rintro - - ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
  have : forallᵐ a ∂P, κ a (((fun ω i => X i ω) ⁻¹' s) inter (Y ⁻¹' t)) =
      κ a ((fun ω i => X i ω) ⁻¹' s) * κ a (Y ⁻¹' t) :=
    h1 ((fun ω i => X i ω) ⁻¹' s) (Y ⁻¹' t) ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
  obtain ⟨I, u, hI, rfl⟩ : exists (I : Set S) (u : Set (Π 

中文:
引理 IndepFun.process_congr_left
  结论: {𝓧 : S -> 类型} {𝓨 : 类型}
  证明: by
  rintro - - ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
  have : forallᵐ a ∂P, κ a (((fun ω i => X i ω) ⁻¹' s) inter (Y ⁻¹' t)) =
      κ a ((fun ω i => X i ω) ⁻¹' s) * κ a (Y ⁻¹' t) :=
    h1 ((fun ω i => X i ω) ⁻¹' s) (Y ⁻¹' t) ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
  obtain ⟨I, u, hI, rfl⟩ : exists (I : Set S) (u : Set (Π 

Depends on / 依赖: Countable, I.Countable, I.domRestrict, domRestrict, eq_preimage_restrict_countable, hs.eq_preimage_restrict_countable, simp_rw
-/
lemma IndepFun.process_congr_left {𝓧 : S -> Type*} {𝓨 : Type*}
    [forall i, MeasurableSpace (𝓧 i)] [MeasurableSpace 𝓨] {X X' : (i : S) -> Ω -> 𝓧 i}
    {Y : Ω -> 𝓨} (h1 : IndepFun (fun ω i => X i ω) Y κ P) (h2 : forall i, forallᵐ a ∂P, X i =ᵐ[κ a] X' i) :
    IndepFun (fun ω i => X' i ω) Y κ P := by
  rintro - - ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
  have : forallᵐ a ∂P, κ a (((fun ω i => X i ω) ⁻¹' s) inter (Y ⁻¹' t)) =
      κ a ((fun ω i => X i ω) ⁻¹' s) * κ a (Y ⁻¹' t) :=
    h1 ((fun ω i => X i ω) ⁻¹' s) (Y ⁻¹' t) ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
  obtain ⟨I, u, hI, rfl⟩ : exists (I : Set S) (u : Set (Π i : I, 𝓧 i)),
      I.Countable ∧ s = I.domRestrict ⁻¹' u := hs.eq_preimage_restrict_countable
  have aux (f : (i : S) -> Ω -> 𝓧 i) : (fun ω i => f i ω) ⁻¹' I.domRestrict ⁻¹' u =
      (fun ω (i : I) => f i ω) ⁻¹' u := rfl
  simp_rw [aux] at *
  have _ : Countable I := hI.to_subtype
  have h : forallᵐ a ∂P, (fun ω (i : I) => X i ω) =ᵐ[κ a] (fun ω (i : I) => X' i ω) := by
    filter_upwards [ae_all_iff.2 fun (i : I) => h2 i] with
      a (ha : forall (i : I), forallᵐ ω ∂κ a, X i ω = X' i ω)
    filter_upwards [ae_all_iff.2 ha] with ω hω using by simp [hω]
  filter_upwards [this, h] with a ha1 ha2
  refine .trans (measure_congr (ae_eq_set_inter (ha2.symm.preimage _) .rfl)) (ha1.trans ?_)
  congr 1
  exact measure_congr (ha2.preimage _)

/--
lemma `IndepFun.process_congr_right` / 引理 `IndepFun.process_congr_right`

English:
lemma IndepFun.process_congr_right
  statement: {𝓧 : S -> Type*} {𝓨 : Type*}
  proof: (h1.symm.process_congr_left h2).symm

中文:
引理 IndepFun.process_congr_right
  结论: {𝓧 : S -> 类型} {𝓨 : 类型}
  证明: (h1.symm.process_congr_left h2).symm

Depends on / 依赖: h1.symm.process_congr_left, process_congr_left
-/
lemma IndepFun.process_congr_right {𝓧 : S -> Type*} {𝓨 : Type*}
    [forall i, MeasurableSpace (𝓧 i)] [MeasurableSpace 𝓨] {X X' : (i : S) -> Ω -> 𝓧 i}
    {Y : Ω -> 𝓨} (h1 : IndepFun Y (fun ω i => X i ω) κ P) (h2 : forall i, forallᵐ a ∂P, X i =ᵐ[κ a] X' i) :
    IndepFun Y (fun ω i => X' i ω) κ P :=
  (h1.symm.process_congr_left h2).symm

/--
lemma `IndepFun.process_congr` / 引理 `IndepFun.process_congr`

English:
lemma IndepFun.process_congr
  statement: {𝓧 : S -> Type*} {𝓨 : T -> Type*}
  proof: (hXY.process_congr_right hY).process_congr_left hX

中文:
引理 IndepFun.process_congr
  结论: {𝓧 : S -> 类型} {𝓨 : T -> 类型}
  证明: (hXY.process_congr_right hY).process_congr_left hX

Depends on / 依赖: hXY.process_congr_right, process_congr_left, process_congr_right
-/
lemma IndepFun.process_congr {𝓧 : S -> Type*} {𝓨 : T -> Type*}
    [forall i, MeasurableSpace (𝓧 i)] [forall j, MeasurableSpace (𝓨 j)] {X X' : (i : S) -> Ω -> 𝓧 i}
    {Y Y' : (j : T) -> Ω -> (𝓨 j)} (hXY : IndepFun (fun ω i => X i ω) (fun ω j => Y j ω) κ P)
    (hX : forall i, forallᵐ a ∂P, X i =ᵐ[κ a] X' i) (hY : forall j, forallᵐ a ∂P, Y j =ᵐ[κ a] Y' j) :
    IndepFun (fun ω i => X' i ω) (fun ω j => Y' j ω) κ P :=
  (hXY.process_congr_right hY).process_congr_left hX

/--
lemma `IndepFun.process_indepFun` / 引理 `IndepFun.process_indepFun`

English:
lemma IndepFun.process_indepFun
  statement: {𝓧 : S -> Type*} {𝓨 : Type*}
  proof: by
  -- The π-system obtained by pulling back the π-system of square cylinders by `X`.
  let πX := {s : Set Ω | exists t in squareCylinders (fun i => {s : Set (𝓧 i) | MeasurableSet s}),
      (fun ω i => X i ω) ⁻¹' t = s}
  have πX_pi : IsPiSystem πX :=
    IsPiSystem.comap (isPiSystem_squareCylinde

中文:
引理 IndepFun.process_indepFun
  结论: {𝓧 : S -> 类型} {𝓨 : 类型}
  证明: by
  -- The π-system obtained by pulling back the π-system of square cylinders by `X`.
  let πX := {s : Set Ω | exists t in squareCylinders (fun i => {s : Set (𝓧 i) | MeasurableSet s}),
      (fun ω i => X i ω) ⁻¹' t = s}
  have πX_pi : IsPiSystem πX :=
    IsPiSystem.comap (isPiSystem_squareCylinde
-/
lemma IndepFun.process_indepFun {𝓧 : S -> Type*} {𝓨 : Type*}
    [forall i, MeasurableSpace (𝓧 i)] [MeasurableSpace 𝓨] {X : (i : S) -> Ω -> 𝓧 i}
    {Y : Ω -> 𝓨} (hX : forall i, Measurable (X i)) (hY : Measurable Y)
    (h : forall (I : Finset S),
      IndepFun (fun ω (i : I) => X i ω) Y κ P) [IsZeroOrMarkovKernel κ] :
    IndepFun (fun ω i => X i ω) Y κ P := by
  -- The π-system obtained by pulling back the π-system of square cylinders by `X`.
  let πX := {s : Set Ω | exists t in squareCylinders (fun i => {s : Set (𝓧 i) | MeasurableSet s}),
      (fun ω i => X i ω) ⁻¹' t = s}
  have πX_pi : IsPiSystem πX :=
    IsPiSystem.comap (isPiSystem_squareCylinders (fun _ => isPiSystem_measurableSet) (by simp)) _
  have πX_gen : (MeasurableSpace.pi.comap fun ω i => X i ω) = generateFrom πX := by
    rw [generateFrom_squareCylinders.symm]; rw [MeasurableSpace.comap_generateFrom]
    rfl
  -- To prove independence, we prove independence of the generating π-system with the `σ`-algebra.
  refine IndepSets.indep (measurable_pi_iff.2 hX).comap_le hY.comap_le
    πX_pi (@isPiSystem_measurableSet Ω (.comap Y inferInstance)) πX_gen
    (@generateFrom_measurableSet Ω (.comap Y inferInstance)).symm ?_
  rintro - - ⟨-, ⟨I, s, hs, rfl⟩, rfl⟩ ⟨t, ht, rfl⟩
  simp only [Set.mem_pi, Set.mem_univ, Set.mem_ofPred_eq, forall_const] at hs
  have : (fun ω i => X i ω) ⁻¹' .pi I s =
      (fun ω (i : I) => X i ω) ⁻¹' .pi (SetLike.coe Finset.univ) (fun i => s i)
       := by
    ext; simp
have h1 : MeasurableSet .pi (SetLike.coe Finset.univ) (fun (i : I) => s i) :=
    .pi (Finset.countable_toSet _) (fun _ _ => hs _)
  filter_upwards [(h I).measure_inter_preimage_eq_mul _ _ h1 ht] with ω hω
  rw [this]; rw [hω]

/--
lemma `IndepFun.process_indepFun₀` / 引理 `IndepFun.process_indepFun₀`

English:
lemma IndepFun.process_indepFun₀
  statement: {𝓧 : S -> Type*} {𝓨 : Type*}
  proof: by
  refine .congr' ?_ (ae_of_all _ fun _ => .rfl) (Measure.ae_ae_of_ae_comp hY.ae_eq_mk.symm)
  apply process_congr_left (X := fun i => (hX i).mk (X i))
  · refine IndepFun.process_indepFun (fun i => (hX i).measurable_mk) hY.measurable_mk
      fun I => process_congr_left (X := fun (i : I) => X i) 

中文:
引理 IndepFun.process_indepFun₀
  结论: {𝓧 : S -> 类型} {𝓨 : 类型}
  证明: by
  refine .congr' ?_ (ae_of_all _ fun _ => .rfl) (Measure.ae_ae_of_ae_comp hY.ae_eq_mk.symm)
  apply process_congr_left (X := fun i => (hX i).mk (X i))
  · refine IndepFun.process_indepFun (fun i => (hX i).measurable_mk) hY.measurable_mk
      fun I => process_congr_left (X := fun (i : I) => X i) 

Depends on / 依赖: IndepFun, IndepFun.process_indepFun, Measure, Measure.ae_ae_of_ae_comp, ae_ae_of_ae_comp, ae_eq_mk, ae_eq_mk.sy, ae_of_all, hY.ae_eq_mk, hY.ae_eq_mk.symm, hY.measurable_mk, measurable_mk, process_congr_left, process_indepFun
-/
lemma IndepFun.process_indepFun₀ {𝓧 : S -> Type*} {𝓨 : Type*}
    [forall i, MeasurableSpace (𝓧 i)] [MeasurableSpace 𝓨] {X : (i : S) -> Ω -> 𝓧 i}
    {Y : Ω -> 𝓨} (hX : forall i, AEMeasurable (X i) (κ ∘ₘ P)) (hY : AEMeasurable Y (κ ∘ₘ P))
    (h : forall (I : Finset S), IndepFun (fun ω (i : I) => X i ω) Y κ P) [IsZeroOrMarkovKernel κ] :
    IndepFun (fun ω i => X i ω) Y κ P := by
  refine .congr' ?_ (ae_of_all _ fun _ => .rfl) (Measure.ae_ae_of_ae_comp hY.ae_eq_mk.symm)
  apply process_congr_left (X := fun i => (hX i).mk (X i))
  · refine IndepFun.process_indepFun (fun i => (hX i).measurable_mk) hY.measurable_mk
      fun I => process_congr_left (X := fun (i : I) => X i) ?_ (fun i => ?_)
    · exact (h I).congr' (ae_of_all _ fun _ => .rfl) (Measure.ae_ae_of_ae_comp hY.ae_eq_mk)
    · exact Measure.ae_ae_of_ae_comp (hX i).ae_eq_mk
  exact fun i => Measure.ae_ae_of_ae_comp (hX i).ae_eq_mk.symm

/--
lemma `IndepFun.indepFun_process` / 引理 `IndepFun.indepFun_process`

English:
lemma IndepFun.indepFun_process
  statement: {𝓧 : Type*} {𝓨 : S -> Type*}
  proof: (IndepFun.process_indepFun hY hX (fun I => (h I).symm)).symm

中文:
引理 IndepFun.indepFun_process
  结论: {𝓧 : 类型} {𝓨 : S -> 类型}
  证明: (IndepFun.process_indepFun hY hX (fun I => (h I).symm)).symm

Depends on / 依赖: IndepFun, IndepFun.process_indepFun, process_indepFun
-/
lemma IndepFun.indepFun_process {𝓧 : Type*} {𝓨 : S -> Type*}
    [MeasurableSpace 𝓧] [forall i, MeasurableSpace (𝓨 i)] {X : Ω -> 𝓧}
    {Y : (i : S) -> Ω -> 𝓨 i} (hX : Measurable X) (hY : forall i, Measurable (Y i))
    (h : forall (I : Finset S),
      IndepFun X (fun ω (i : I) => Y i ω) κ P) [IsZeroOrMarkovKernel κ] :
    IndepFun X (fun ω i => Y i ω) κ P :=
  (IndepFun.process_indepFun hY hX (fun I => (h I).symm)).symm

/--
lemma `IndepFun.indepFun_process₀` / 引理 `IndepFun.indepFun_process₀`

English:
lemma IndepFun.indepFun_process₀
  statement: {𝓧 : Type*} {𝓨 : S -> Type*}
  proof: (IndepFun.process_indepFun₀ hY hX (fun I => (h I).symm)).symm

中文:
引理 IndepFun.indepFun_process₀
  结论: {𝓧 : 类型} {𝓨 : S -> 类型}
  证明: (IndepFun.process_indepFun₀ hY hX (fun I => (h I).symm)).symm

Depends on / 依赖: IndepFun, IndepFun.process_indepFun
-/
lemma IndepFun.indepFun_process₀ {𝓧 : Type*} {𝓨 : S -> Type*}
    [MeasurableSpace 𝓧] [forall i, MeasurableSpace (𝓨 i)] {X : Ω -> 𝓧}
    {Y : (i : S) -> Ω -> 𝓨 i} (hX : AEMeasurable X (κ ∘ₘ P)) (hY : forall i, AEMeasurable (Y i) (κ ∘ₘ P))
    (h : forall (I : Finset S),
      IndepFun X (fun ω (i : I) => Y i ω) κ P) [IsZeroOrMarkovKernel κ] :
    IndepFun X (fun ω i => Y i ω) κ P :=
  (IndepFun.process_indepFun₀ hY hX (fun I => (h I).symm)).symm

/--
lemma `IndepFun.process_indepFun_process` / 引理 `IndepFun.process_indepFun_process`

English:
lemma IndepFun.process_indepFun_process
  statement: {T : Type*} {𝓧 : S -> Type*} {𝓨 : T -> Type*}
  proof: by
  refine IndepFun.process_indepFun hX (measurable_pi_lambda _ hY) fun I => ?_
  exact IndepFun.indepFun_process (measurable_pi_lambda _ fun _ => hX _) hY fun J => h I J

中文:
引理 IndepFun.process_indepFun_process
  结论: {T : 类型} {𝓧 : S -> 类型} {𝓨 : T -> 类型}
  证明: by
  refine IndepFun.process_indepFun hX (measurable_pi_lambda _ hY) fun I => ?_
  exact IndepFun.indepFun_process (measurable_pi_lambda _ fun _ => hX _) hY fun J => h I J

Depends on / 依赖: IndepFun, IndepFun.indepFun_process, IndepFun.process_indepFun, indepFun_process, measurable_pi_lambda, process_indepFun
-/
lemma IndepFun.process_indepFun_process {T : Type*} {𝓧 : S -> Type*} {𝓨 : T -> Type*}
    [forall i, MeasurableSpace (𝓧 i)] [forall j, MeasurableSpace (𝓨 j)] {X : (i : S) -> Ω -> 𝓧 i}
    {Y : (j : T) -> Ω -> 𝓨 j} (hX : forall i, Measurable (X i)) (hY : forall j, Measurable (Y j))
    (h : forall (I : Finset S) (J : Finset T),
      IndepFun (fun ω (i : I) => X i ω) (fun ω (j : J) => Y j ω) κ P) [IsZeroOrMarkovKernel κ] :
    IndepFun (fun ω i => X i ω) (fun ω j => Y j ω) κ P := by
  refine IndepFun.process_indepFun hX (measurable_pi_lambda _ hY) fun I => ?_
  exact IndepFun.indepFun_process (measurable_pi_lambda _ fun _ => hX _) hY fun J => h I J

/--
lemma `IndepFun.process_indepFun_process₀` / 引理 `IndepFun.process_indepFun_process₀`

English:
lemma IndepFun.process_indepFun_process₀
  statement: {T : Type*} {𝓧 : S -> Type*} {𝓨 : T -> Type*}
  proof: by
  refine process_congr ?_ (fun i => Measure.ae_ae_of_ae_comp (hX i).ae_eq_mk.symm)
    (fun j => Measure.ae_ae_of_ae_comp (hY j).ae_eq_mk.symm)
  refine process_indepFun_process
    (fun i => (hX i).measurable_mk) (fun j => (hY j).measurable_mk) fun I J => ?_
  exact process_congr (h I J) (fun i 

中文:
引理 IndepFun.process_indepFun_process₀
  结论: {T : 类型} {𝓧 : S -> 类型} {𝓨 : T -> 类型}
  证明: by
  refine process_congr ?_ (fun i => Measure.ae_ae_of_ae_comp (hX i).ae_eq_mk.symm)
    (fun j => Measure.ae_ae_of_ae_comp (hY j).ae_eq_mk.symm)
  refine process_indepFun_process
    (fun i => (hX i).measurable_mk) (fun j => (hY j).measurable_mk) fun I J => ?_
  exact process_congr (h I J) (fun i 

Depends on / 依赖: Measure, Measure.ae_ae_of_ae_comp, ae_ae_of_ae_comp, ae_eq_mk, ae_eq_mk.symm, measurable_mk, process_congr, process_indepFun_process
-/
lemma IndepFun.process_indepFun_process₀ {T : Type*} {𝓧 : S -> Type*} {𝓨 : T -> Type*}
    [forall i, MeasurableSpace (𝓧 i)] [forall j, MeasurableSpace (𝓨 j)] {X : (i : S) -> Ω -> 𝓧 i}
    {Y : (j : T) -> Ω -> 𝓨 j} (hX : forall i, AEMeasurable (X i) (κ ∘ₘ P))
    (hY : forall j, AEMeasurable (Y j) (κ ∘ₘ P))
    (h : forall (I : Finset S) (J : Finset T),
      IndepFun (fun ω (i : I) => X i ω) (fun ω (j : J) => Y j ω) κ P) [IsZeroOrMarkovKernel κ] :
    IndepFun (fun ω i => X i ω) (fun ω j => Y j ω) κ P := by
  refine process_congr ?_ (fun i => Measure.ae_ae_of_ae_comp (hX i).ae_eq_mk.symm)
    (fun j => Measure.ae_ae_of_ae_comp (hY j).ae_eq_mk.symm)
  refine process_indepFun_process
    (fun i => (hX i).measurable_mk) (fun j => (hY j).measurable_mk) fun I J => ?_
  exact process_congr (h I J) (fun i => Measure.ae_ae_of_ae_comp (hX i).ae_eq_mk)
    (fun j => Measure.ae_ae_of_ae_comp (hY j).ae_eq_mk)

/--
lemma `iIndepFun.process_congr` / 引理 `iIndepFun.process_congr`

English:
lemma iIndepFun.process_congr
  statement: {T : S -> Type*} {𝓧 : (i : S) -> (j : T i) -> Type*}
  proof: by
  intro s f hf
  choose! g mg hg using hf
  have h3 : ⋂ i in s, f i = ⋂ i in s, (fun i ω j => X' i j ω) i ⁻¹' g i := (biInf_congr hg).symm
  have h3' a : ∏ i in s, κ a (f i) = ∏ i in s, κ a ((fun i ω j => X' i j ω) i ⁻¹' g i) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [hg i hi]


中文:
引理 iIndepFun.process_congr
  结论: {T : S -> 类型} {𝓧 : (i : S) -> (j : T i) -> 类型}
  证明: by
  intro s f hf
  choose! g mg hg using hf
  have h3 : ⋂ i in s, f i = ⋂ i in s, (fun i ω j => X' i j ω) i ⁻¹' g i := (biInf_congr hg).symm
  have h3' a : ∏ i in s, κ a (f i) = ∏ i in s, κ a ((fun i ω j => X' i j ω) i ⁻¹' g i) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [hg i hi]


Depends on / 依赖: Finset, Finset.prod_congr, biInf_congr, eq_preimage_restrict_countable, prod_congr, simp_rw
-/
lemma iIndepFun.process_congr {T : S -> Type*} {𝓧 : (i : S) -> (j : T i) -> Type*}
    [forall i j, MeasurableSpace (𝓧 i j)] {X X' : (i : S) -> (j : T i) -> Ω -> 𝓧 i j}
    (h1 : iIndepFun (fun i ω j => X i j ω) κ P) (h2 : forall i j, forallᵐ a ∂P, X i j =ᵐ[κ a] X' i j) :
    iIndepFun (fun i ω j => X' i j ω) κ P := by
  intro s f hf
  choose! g mg hg using hf
  have h3 : ⋂ i in s, f i = ⋂ i in s, (fun i ω j => X' i j ω) i ⁻¹' g i := (biInf_congr hg).symm
  have h3' a : ∏ i in s, κ a (f i) = ∏ i in s, κ a ((fun i ω j => X' i j ω) i ⁻¹' g i) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [hg i hi]
  simp_rw [h3, h3']
  choose! I u hI hu using fun i hi => (mg i hi).eq_preimage_restrict_countable
  have h4 (f : (i : S) -> (j : T i) -> Ω -> 𝓧 i j) : ⋂ i in s, (fun i ω j => f i j ω) i ⁻¹' g i =
      ⋂ i in s, (fun i ω j => f i j ω) i ⁻¹' (I i).domRestrict ⁻¹' u i :=
      (biInf_congr (fun i hi => by rw [hu i hi])).symm
  have h4' a (f : (i : S) -> (j : T i) -> Ω -> 𝓧 i j) :
      ∏ i in s, κ a ((fun i ω j => f i j ω) i ⁻¹' g i) =
      ∏ i in s, κ a ((fun i ω j => f i j ω) i ⁻¹' (I i).domRestrict ⁻¹' u i) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [hu i hi]
  have h5 := h1 s (fun i hi => ⟨g i, mg i hi, rfl⟩)
  simp_rw [h4, h4'] at h5 ⊢
  have h6 i (f : (j : T i) -> Ω -> 𝓧 i j) : (fun ω j => f j ω) ⁻¹' (I i).domRestrict ⁻¹' (u i) =
      (fun ω (j : I i) => f j ω) ⁻¹' (u i) := rfl
  simp_rw [h6] at h5 ⊢
  have h :
      forallᵐ a ∂P, forall i in s, (fun ω (j : I i) => X i j ω) =ᵐ[κ a] (fun ω (j : I i) => X' i j ω) := by
    refine (ae_ball_iff s.countable_toSet).2 fun i hi => ?_
    have := (hI i hi).to_subtype
    filter_upwards [ae_all_iff.2 fun (j : I i) => h2 i j] with
      a (ha : forall (j : I i), forallᵐ ω ∂κ a, X i j ω = X' i j ω)
    filter_upwards [ae_all_iff.2 ha] with ω hω using by simp [hω]
  filter_upwards [h5, h] with a ha1 ha2
  refine .trans (measure_congr (ae_eq_set_biInter s.countable_toSet
    (fun i hi => ((ha2 i hi).preimage _).symm))) (ha1.trans ?_)
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [measure_congr ((ha2 i hi).preimage _)]

/--
lemma `iIndepFun.iIndepFun_process` / 引理 `iIndepFun.iIndepFun_process`

English:
lemma iIndepFun.iIndepFun_process
  statement: {T : S -> Type*} {𝓧 : (i : S) -> (j : T i) -> Type*}
  proof: by
  obtain rfl | hμ := eq_or_ne P 0
  · simp
  obtain ⟨η, η_eq, hη⟩ : exists (η : Kernel α Ω), κ =ᵐ[P] η ∧ IsMarkovKernel η :=
    exists_ae_eq_isMarkovKernel (h ∅ fun _ => ∅).ae_isProbabilityMeasure hμ
  apply iIndepFun.congr (Filter.EventuallyEq.symm η_eq)
  let π i := {s : Set Ω | exists t in sq

中文:
引理 iIndepFun.iIndepFun_process
  结论: {T : S -> 类型} {𝓧 : (i : S) -> (j : T i) -> 类型}
  证明: by
  obtain rfl | hμ := eq_or_ne P 0
  · simp
  obtain ⟨η, η_eq, hη⟩ : exists (η : Kernel α Ω), κ =ᵐ[P] η ∧ IsMarkovKernel η :=
    exists_ae_eq_isMarkovKernel (h ∅ fun _ => ∅).ae_isProbabilityMeasure hμ
  apply iIndepFun.congr (Filter.EventuallyEq.symm η_eq)
  let π i := {s : Set Ω | exists t in sq

Depends on / 依赖: EventuallyEq, Filter, Filter.EventuallyEq.symm, IsMarkovKernel, IsPiSystem, Kernel, MeasurableSet, ae_isProbabilityMeasure, eq_or_ne, exists_ae_eq_isMarkovKernel, iIndepFun, iIndepFun.congr, isPiSystem_measurableSet, isPiSystem_squareCylinders, squareCylinders
-/
lemma iIndepFun.iIndepFun_process {T : S -> Type*} {𝓧 : (i : S) -> (j : T i) -> Type*}
    [forall i j, MeasurableSpace (𝓧 i j)] {X : (i : S) -> (j : T i) -> Ω -> 𝓧 i j}
    (hX : forall i j, Measurable (X i j))
    (h : forall (I : Finset S) (J : (i : I) -> Finset (T i)),
      iIndepFun (fun i ω (j : J i) => X i j ω) κ P) :
    iIndepFun (fun i ω j => X i j ω) κ P := by
  obtain rfl | hμ := eq_or_ne P 0
  · simp
  obtain ⟨η, η_eq, hη⟩ : exists (η : Kernel α Ω), κ =ᵐ[P] η ∧ IsMarkovKernel η :=
    exists_ae_eq_isMarkovKernel (h ∅ fun _ => ∅).ae_isProbabilityMeasure hμ
  apply iIndepFun.congr (Filter.EventuallyEq.symm η_eq)
  let π i := {s : Set Ω | exists t in squareCylinders (fun j => {s : Set (𝓧 i j) | MeasurableSet s}),
    (fun ω j => X i j ω) ⁻¹' t = s}
  have π_pi i : IsPiSystem (π i) :=
    (isPiSystem_squareCylinders (fun _ => isPiSystem_measurableSet) (by simp)).comap _
  have π_gen i : (MeasurableSpace.pi.comap fun ω j => X i j ω) = generateFrom (π i) := by
    rw [generateFrom_squareCylinders.symm]; rw [MeasurableSpace.comap_generateFrom]
    rfl
  refine iIndepSets.iIndep _ (fun i => (measurable_pi_iff.2 (hX i)).comap_le) π π_pi π_gen
    fun I s hs => ?_
  simp only [squareCylinders, Set.mem_pi, Set.mem_univ, Set.mem_ofPred_eq, forall_const,
    ↓existsAndEq, and_true, π] at hs
  choose! J t ht hs using hs
  simp_rw [Set.iInter₂_congr (fun i hi => (hs i hi).symm),
    I.prod_congr rfl (fun i hi => congrArg _ (hs i hi).symm)]
  have : (⋂ i in I, (fun ω j => X i j ω) ⁻¹' .pi (J i) (t i)) =
      (⋂ i in (.univ : Finset I), (fun ω (j : J i) => X i j ω) ⁻¹'
        .pi (SetLike.coe Finset.univ) (fun j => t i j)) := by
    ext; simp
  have h' (i : I) (hi : i in Finset.univ) :
MeasurableSet (SetLike.coe Finset.univ).pi fun (j : J i) => t i j :=
    .pi (Finset.countable_toSet _) (fun _ _ => ht _ i.2 _)
  filter_upwards [(h I (fun i => J i)).measure_inter_preimage_eq_mul _ _ .univ h',
    η_eq] with ω hω hη
  rw [this]; rw [← hη]; rw [hω]; rw [← I.prod_coe_sort]
  congrm ∏ _, κ ω ?_
  ext; simp

/--
lemma `iIndepFun.iIndepFun_process₀` / 引理 `iIndepFun.iIndepFun_process₀`

English:
lemma iIndepFun.iIndepFun_process₀
  statement: {T : S -> Type*} {𝓧 : (i : S) -> (j : T i) -> Type*}
  proof: by
  refine process_congr ?_ (fun i j => Measure.ae_ae_of_ae_comp (hX i j).ae_eq_mk.symm)
  refine iIndepFun_process (fun i j => (hX i j).measurable_mk) fun I J => ?_
  exact (h I J).process_congr (fun i j => Measure.ae_ae_of_ae_comp (hX i j).ae_eq_mk)

中文:
引理 iIndepFun.iIndepFun_process₀
  结论: {T : S -> 类型} {𝓧 : (i : S) -> (j : T i) -> 类型}
  证明: by
  refine process_congr ?_ (fun i j => Measure.ae_ae_of_ae_comp (hX i j).ae_eq_mk.symm)
  refine iIndepFun_process (fun i j => (hX i j).measurable_mk) fun I J => ?_
  exact (h I J).process_congr (fun i j => Measure.ae_ae_of_ae_comp (hX i j).ae_eq_mk)

Depends on / 依赖: Measure, Measure.ae_ae_of_ae_comp, ae_ae_of_ae_comp, ae_eq_mk, ae_eq_mk.symm, iIndepFun_process, measurable_mk, process_congr
-/
lemma iIndepFun.iIndepFun_process₀ {T : S -> Type*} {𝓧 : (i : S) -> (j : T i) -> Type*}
    [forall i j, MeasurableSpace (𝓧 i j)] {X : (i : S) -> (j : T i) -> Ω -> 𝓧 i j}
    (hX : forall i j, AEMeasurable (X i j) (κ ∘ₘ P))
    (h : forall (I : Finset S) (J : (i : I) -> Finset (T i)),
      iIndepFun (fun i ω (j : J i) => X i j ω) κ P) :
    iIndepFun (fun i ω j => X i j ω) κ P := by
  refine process_congr ?_ (fun i j => Measure.ae_ae_of_ae_comp (hX i j).ae_eq_mk.symm)
  refine iIndepFun_process (fun i j => (hX i j).measurable_mk) fun I J => ?_
  exact (h I J).process_congr (fun i j => Measure.ae_ae_of_ae_comp (hX i j).ae_eq_mk)

end Kernel

variable {P : Measure Ω}

/--
lemma `IndepFun.process_congr_left` / 引理 `IndepFun.process_congr_left`

English:
lemma IndepFun.process_congr_left
  statement: {𝓧 : S -> Type*} {𝓨 : Type*}
  proof: Kernel.IndepFun.process_congr_left h1 (by simpa)

中文:
引理 IndepFun.process_congr_left
  结论: {𝓧 : S -> 类型} {𝓨 : 类型}
  证明: Kernel.IndepFun.process_congr_left h1 (by simpa)
-/
lemma IndepFun.process_congr_left {𝓧 : S -> Type*} {𝓨 : Type*}
    [forall i, MeasurableSpace (𝓧 i)] [MeasurableSpace 𝓨] {X X' : (i : S) -> Ω -> 𝓧 i}
    {Y : Ω -> 𝓨} (h1 : (fun ω i => X i ω) ⟂ᵢ[P] Y) (h2 : forall i, X i =ᵐ[P] X' i) :
    (fun ω i => X' i ω) ⟂ᵢ[P] Y :=
  Kernel.IndepFun.process_congr_left h1 (by simpa)

/--
lemma `IndepFun.process_congr_right` / 引理 `IndepFun.process_congr_right`

English:
lemma IndepFun.process_congr_right
  statement: {𝓧 : S -> Type*} {𝓨 : Type*}
  proof: Kernel.IndepFun.process_congr_right h1 (by simpa)

中文:
引理 IndepFun.process_congr_right
  结论: {𝓧 : S -> 类型} {𝓨 : 类型}
  证明: Kernel.IndepFun.process_congr_right h1 (by simpa)
-/
lemma IndepFun.process_congr_right {𝓧 : S -> Type*} {𝓨 : Type*}
    [forall i, MeasurableSpace (𝓧 i)] [MeasurableSpace 𝓨] {X X' : (i : S) -> Ω -> 𝓧 i}
    {Y : Ω -> 𝓨} (h1 : Y ⟂ᵢ[P] (fun ω i => X i ω)) (h2 : forall i, X i =ᵐ[P] X' i) :
    Y ⟂ᵢ[P] (fun ω i => X' i ω) :=
  Kernel.IndepFun.process_congr_right h1 (by simpa)

/--
lemma `IndepFun.process_congr` / 引理 `IndepFun.process_congr`

English:
lemma IndepFun.process_congr
  statement: {𝓧 : S -> Type*} {𝓨 : T -> Type*}
  proof: Kernel.IndepFun.process_congr hXY (by simpa) (by simpa)

中文:
引理 IndepFun.process_congr
  结论: {𝓧 : S -> 类型} {𝓨 : T -> 类型}
  证明: Kernel.IndepFun.process_congr hXY (by simpa) (by simpa)
-/
lemma IndepFun.process_congr {𝓧 : S -> Type*} {𝓨 : T -> Type*}
    [forall i, MeasurableSpace (𝓧 i)] [forall j, MeasurableSpace (𝓨 j)] {X X' : (i : S) -> Ω -> 𝓧 i}
    {Y Y' : (j : T) -> Ω -> (𝓨 j)} (hXY : (fun ω i => X i ω) ⟂ᵢ[P] (fun ω j => Y j ω))
    (hX : forall i, X i =ᵐ[P] X' i) (hY : forall j, Y j =ᵐ[P] Y' j) :
    (fun ω i => X' i ω) ⟂ᵢ[P] (fun ω j => Y' j ω) :=
  Kernel.IndepFun.process_congr hXY (by simpa) (by simpa)

/--
lemma `IndepFun.process_indepFun` / 引理 `IndepFun.process_indepFun`

English:
lemma IndepFun.process_indepFun
  statement: {𝓧 : S -> Type*} {𝓨 : Type*}
  proof: Kernel.IndepFun.process_indepFun hX hY h

中文:
引理 IndepFun.process_indepFun
  结论: {𝓧 : S -> 类型} {𝓨 : 类型}
  证明: Kernel.IndepFun.process_indepFun hX hY h
-/
lemma IndepFun.process_indepFun {𝓧 : S -> Type*} {𝓨 : Type*}
    [forall i, MeasurableSpace (𝓧 i)] [MeasurableSpace 𝓨] {X : (i : S) -> Ω -> 𝓧 i}
    {Y : Ω -> 𝓨} (hX : forall i, Measurable (X i)) (hY : Measurable Y)
    (h : forall (I : Finset S), (fun ω (i : I) => X i ω) ⟂ᵢ[P] Y) [IsZeroOrProbabilityMeasure P] :
    IndepFun (fun ω i => X i ω) Y P :=
  Kernel.IndepFun.process_indepFun hX hY h

/--
lemma `IndepFun.process_indepFun₀` / 引理 `IndepFun.process_indepFun₀`

English:
lemma IndepFun.process_indepFun₀
  statement: {𝓧 : S -> Type*} {𝓨 : Type*}
  proof: Kernel.IndepFun.process_indepFun₀ (by simpa) (by simpa) h

中文:
引理 IndepFun.process_indepFun₀
  结论: {𝓧 : S -> 类型} {𝓨 : 类型}
  证明: Kernel.IndepFun.process_indepFun₀ (by simpa) (by simpa) h
-/
lemma IndepFun.process_indepFun₀ {𝓧 : S -> Type*} {𝓨 : Type*}
    [forall i, MeasurableSpace (𝓧 i)] [MeasurableSpace 𝓨] {X : (i : S) -> Ω -> 𝓧 i}
    {Y : Ω -> 𝓨} (hX : forall i, AEMeasurable (X i) P) (hY : AEMeasurable Y P)
    (h : forall (I : Finset S), (fun ω (i : I) => X i ω) ⟂ᵢ[P] Y) [IsZeroOrProbabilityMeasure P] :
    IndepFun (fun ω i => X i ω) Y P :=
  Kernel.IndepFun.process_indepFun₀ (by simpa) (by simpa) h

/--
lemma `IndepFun.indepFun_process` / 引理 `IndepFun.indepFun_process`

English:
lemma IndepFun.indepFun_process
  statement: {𝓧 : Type*} {𝓨 : S -> Type*}
  proof: Kernel.IndepFun.indepFun_process hX hY h

中文:
引理 IndepFun.indepFun_process
  结论: {𝓧 : 类型} {𝓨 : S -> 类型}
  证明: Kernel.IndepFun.indepFun_process hX hY h
-/
lemma IndepFun.indepFun_process {𝓧 : Type*} {𝓨 : S -> Type*}
    [MeasurableSpace 𝓧] [forall i, MeasurableSpace (𝓨 i)] {X : Ω -> 𝓧}
    {Y : (i : S) -> Ω -> 𝓨 i} (hX : Measurable X) (hY : forall i, Measurable (Y i))
    (h : forall (I : Finset S), X ⟂ᵢ[P] (fun ω (i : I) => Y i ω)) [IsZeroOrProbabilityMeasure P] :
    IndepFun X (fun ω i => Y i ω) P :=
  Kernel.IndepFun.indepFun_process hX hY h

/--
lemma `IndepFun.indepFun_process₀` / 引理 `IndepFun.indepFun_process₀`

English:
lemma IndepFun.indepFun_process₀
  statement: {𝓧 : Type*} {𝓨 : S -> Type*}
  proof: Kernel.IndepFun.indepFun_process₀ (by simpa) (by simpa) h

中文:
引理 IndepFun.indepFun_process₀
  结论: {𝓧 : 类型} {𝓨 : S -> 类型}
  证明: Kernel.IndepFun.indepFun_process₀ (by simpa) (by simpa) h
-/
lemma IndepFun.indepFun_process₀ {𝓧 : Type*} {𝓨 : S -> Type*}
    [MeasurableSpace 𝓧] [forall i, MeasurableSpace (𝓨 i)] {X : Ω -> 𝓧}
    {Y : (i : S) -> Ω -> 𝓨 i} (hX : AEMeasurable X P) (hY : forall i, AEMeasurable (Y i) P)
    (h : forall (I : Finset S), X ⟂ᵢ[P] (fun ω (i : I) => Y i ω)) [IsZeroOrProbabilityMeasure P] :
    IndepFun X (fun ω i => Y i ω) P :=
  Kernel.IndepFun.indepFun_process₀ (by simpa) (by simpa) h

/--
lemma `IndepFun.process_indepFun_process` / 引理 `IndepFun.process_indepFun_process`

English:
lemma IndepFun.process_indepFun_process
  statement: {T : Type*} {𝓧 : S -> Type*} {𝓨 : T -> Type*}
  proof: Kernel.IndepFun.process_indepFun_process hX hY h

中文:
引理 IndepFun.process_indepFun_process
  结论: {T : 类型} {𝓧 : S -> 类型} {𝓨 : T -> 类型}
  证明: Kernel.IndepFun.process_indepFun_process hX hY h
-/
lemma IndepFun.process_indepFun_process {T : Type*} {𝓧 : S -> Type*} {𝓨 : T -> Type*}
    [forall i, MeasurableSpace (𝓧 i)] [forall j, MeasurableSpace (𝓨 j)] {X : (i : S) -> Ω -> 𝓧 i}
    {Y : (j : T) -> Ω -> 𝓨 j} (hX : forall i, Measurable (X i)) (hY : forall j, Measurable (Y j))
    (h : forall (I : Finset S) (J : Finset T),
      (fun ω (i : I) => X i ω) ⟂ᵢ[P] (fun ω (j : J) => Y j ω)) [IsZeroOrProbabilityMeasure P] :
    IndepFun (fun ω i => X i ω) (fun ω j => Y j ω) P :=
  Kernel.IndepFun.process_indepFun_process hX hY h

/--
lemma `IndepFun.process_indepFun_process₀` / 引理 `IndepFun.process_indepFun_process₀`

English:
lemma IndepFun.process_indepFun_process₀
  statement: {T : Type*} {𝓧 : S -> Type*} {𝓨 : T -> Type*}
  proof: Kernel.IndepFun.process_indepFun_process₀ (by simpa) (by simpa) h

中文:
引理 IndepFun.process_indepFun_process₀
  结论: {T : 类型} {𝓧 : S -> 类型} {𝓨 : T -> 类型}
  证明: Kernel.IndepFun.process_indepFun_process₀ (by simpa) (by simpa) h
-/
lemma IndepFun.process_indepFun_process₀ {T : Type*} {𝓧 : S -> Type*} {𝓨 : T -> Type*}
    [forall i, MeasurableSpace (𝓧 i)] [forall j, MeasurableSpace (𝓨 j)] {X : (i : S) -> Ω -> 𝓧 i}
    {Y : (j : T) -> Ω -> 𝓨 j} (hX : forall i, AEMeasurable (X i) P) (hY : forall j, AEMeasurable (Y j) P)
    (h : forall (I : Finset S) (J : Finset T),
      (fun ω (i : I) => X i ω) ⟂ᵢ[P] (fun ω (j : J) => Y j ω)) [IsZeroOrProbabilityMeasure P] :
    IndepFun (fun ω i => X i ω) (fun ω j => Y j ω) P :=
  Kernel.IndepFun.process_indepFun_process₀ (by simpa) (by simpa) h

/--
lemma `iIndepFun.process_congr` / 引理 `iIndepFun.process_congr`

English:
lemma iIndepFun.process_congr
  statement: {T : S -> Type*} {𝓧 : (i : S) -> (j : T i) -> Type*}
  proof: Kernel.iIndepFun.process_congr h1 (by simpa)

中文:
引理 iIndepFun.process_congr
  结论: {T : S -> 类型} {𝓧 : (i : S) -> (j : T i) -> 类型}
  证明: Kernel.iIndepFun.process_congr h1 (by simpa)
-/
lemma iIndepFun.process_congr {T : S -> Type*} {𝓧 : (i : S) -> (j : T i) -> Type*}
    [forall i j, MeasurableSpace (𝓧 i j)] {X X' : (i : S) -> (j : T i) -> Ω -> 𝓧 i j}
    (h1 : iIndepFun (fun i ω j => X i j ω) P) (h2 : forall i j, X i j =ᵐ[P] X' i j) :
    iIndepFun (fun i ω j => X' i j ω) P :=
  Kernel.iIndepFun.process_congr h1 (by simpa)

/--
lemma `iIndepFun.iIndepFun_process` / 引理 `iIndepFun.iIndepFun_process`

English:
lemma iIndepFun.iIndepFun_process
  statement: {T : S -> Type*} {𝓧 : (i : S) -> (j : T i) -> Type*}
  proof: Kernel.iIndepFun.iIndepFun_process hX h

中文:
引理 iIndepFun.iIndepFun_process
  结论: {T : S -> 类型} {𝓧 : (i : S) -> (j : T i) -> 类型}
  证明: Kernel.iIndepFun.iIndepFun_process hX h
-/
lemma iIndepFun.iIndepFun_process {T : S -> Type*} {𝓧 : (i : S) -> (j : T i) -> Type*}
    [forall i j, MeasurableSpace (𝓧 i j)] {X : (i : S) -> (j : T i) -> Ω -> 𝓧 i j}
    (hX : forall i j, Measurable (X i j))
    (h : forall (I : Finset S) (J : (i : I) -> Finset (T i)), iIndepFun (fun i ω (j : J i) => X i j ω) P) :
    iIndepFun (fun i ω j => X i j ω) P :=
  Kernel.iIndepFun.iIndepFun_process hX h

/--
lemma `iIndepFun.iIndepFun_process₀` / 引理 `iIndepFun.iIndepFun_process₀`

English:
lemma iIndepFun.iIndepFun_process₀
  statement: {T : S -> Type*} {𝓧 : (i : S) -> (j : T i) -> Type*}
  proof: Kernel.iIndepFun.iIndepFun_process₀ (by simpa) h

中文:
引理 iIndepFun.iIndepFun_process₀
  结论: {T : S -> 类型} {𝓧 : (i : S) -> (j : T i) -> 类型}
  证明: Kernel.iIndepFun.iIndepFun_process₀ (by simpa) h
-/
lemma iIndepFun.iIndepFun_process₀ {T : S -> Type*} {𝓧 : (i : S) -> (j : T i) -> Type*}
    [forall i j, MeasurableSpace (𝓧 i j)] {X : (i : S) -> (j : T i) -> Ω -> 𝓧 i j}
    (hX : forall i j, AEMeasurable (X i j) P)
    (h : forall (I : Finset S) (J : (i : I) -> Finset (T i)), iIndepFun (fun i ω (j : J i) => X i j ω) P) :
    iIndepFun (fun i ω j => X i j ω) P :=
  Kernel.iIndepFun.iIndepFun_process₀ (by simpa) h

end ProbabilityTheory
