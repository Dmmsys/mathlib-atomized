/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Infinite product of probability measures

This file provides a definition for the product measure of an arbitrary family of probability
measures. Given `μ : (i : ι) → Measure (X i)` such that each `μ i` is a probability measure,
`Measure.infinitePi μ` is the only probability measure `ν` over `Π i, X i` such that
`ν (Set.pi s t) = ∏ i ∈ s, μ i (t i)`, with `s : Finset ι` and
such that `∀ i ∈ s, MeasurableSet (t i)` (see `eq_infinitePi` and `infinitePi_pi`).
We also provide a few results regarding integration against this measure.

## Main definition

* `Measure.infinitePi μ`: The product measure of the family of probability measures `μ`.

## Main statements

* `eq_infinitePi`: Any measure which gives to a finite product of sets the mass which is the
  product of their measures is the product measure.
* `infinitePi_pi`: the product measure gives to finite products of sets a mass which is
  the product of their masses.
* `infinitePi_cylinder`: `infinitePi μ (cylinder s S) = Measure.pi (fun i : s ↦ μ i) S`

## Implementation notes

To construct the product measure we first use the kernel `traj` obtained via the Ionescu-Tulcea
theorem to construct the measure over a product indexed by `ℕ`, which is `infinitePiNat`. This
is an implementation detail and should not be used directly. Then we construct the product measure
over an arbitrary type by extending `piContent μ` thanks to Carathéodory's theorem. The key lemma
to do so is `piContent_tendsto_zero`, which states that `piContent μ (A n)` tends to zero if
`A` is a nonincreasing sequence of sets satisfying `⋂ n, A n = ∅`.
We prove this lemma by reducing to the case of an at most countable product,
in which case `piContent μ` is known to be a true measure (see `piContent_eq_measure_pi` and
`piContent_eq_infinitePiNat`).

## Tags

infinite product measure
-/

@[expose] public section

open ProbabilityTheory Finset Filter Preorder MeasurableEquiv

open scoped ENNReal Topology

namespace MeasureTheory

section Preliminaries

variable {ι : Type*} {X : ι -> Type*} {mX : forall i, MeasurableSpace (X i)}
variable (μ : (i : ι) -> Measure (X i)) [hμ : forall i, IsProbabilityMeasure (μ i)]

/--
lemma `isProjectiveMeasureFamily_pi` / 引理 `isProjectiveMeasureFamily_pi`

English:
lemma isProjectiveMeasureFamily_pi
  proof: by
  refine fun I J hJI => Measure.pi_eq (fun s ms => ?_)
  classical
  simp_rw [Measure.map_apply (measurable_restrict₂ hJI) (.univ_pi ms), restrict₂_preimage hJI,
    Measure.pi_pi, prod_eq_prod_extend]
  refine (prod_subset_one_on_sdiff hJI (fun x hx => ?_) (fun x hx => ?_)).symm
  · rw [Function.extend_val_apply (mem_sdiff.1 hx).1, dif_neg (mem_sdiff.1 hx).2, measure_univ]
  · rw [Function.extend_val_apply hx, Function.extend_val_apply (hJI hx), dif_pos hx]

中文:
引理 isProjectiveMeasureFamily_pi
  证明: by
  refine fun I J hJI => Measure.pi_eq (fun s ms => ?_)
  classical
  simp_rw [Measure.map_apply (measurable_restrict₂ hJI) (.univ_pi ms), restrict₂_preimage hJI,
    Measure.pi_pi, prod_eq_prod_extend]
  refine (prod_subset_one_on_sdiff hJI (fun x hx => ?_) (fun x hx => ?_)).symm
  · rw [Function.extend_val_apply (mem_sdiff.1 hx).1, dif_neg (mem_sdiff.1 hx).2, measure_univ]
  · rw [Function.extend_val_apply hx, Function.extend_val_apply (hJI hx), dif_pos hx]

Depends on / 依赖: Function, Function.extend_val_apply, Measure, Measure.map_apply, Measure.pi_eq, Measure.pi_pi, classical, dif_neg, dif_pos, extend_val_apply, map_apply, measure_univ, mem_sdiff, pi_eq, pi_pi, prod_eq_prod_extend, prod_subset_one_on_sdiff, simp_rw, univ_pi
-/
lemma isProjectiveMeasureFamily_pi :
    IsProjectiveMeasureFamily (fun I : Finset ι => (Measure.pi (fun i : I => μ i))) := by
  refine fun I J hJI => Measure.pi_eq (fun s ms => ?_)
  classical
  simp_rw [Measure.map_apply (measurable_restrict₂ hJI) (.univ_pi ms), restrict₂_preimage hJI,
    Measure.pi_pi, prod_eq_prod_extend]
  refine (prod_subset_one_on_sdiff hJI (fun x hx => ?_) (fun x hx => ?_)).symm
  · rw [Function.extend_val_apply (mem_sdiff.1 hx).1, dif_neg (mem_sdiff.1 hx).2, measure_univ]
  · rw [Function.extend_val_apply hx, Function.extend_val_apply (hJI hx), dif_pos hx]

/--
Definition of `piContent` / `piContent` 的定义

English:
definition piContent
  signature: : AddContent Real>=0∞ (measurableCylinders X)
  body: projectiveFamilyContent (isProjectiveMeasureFamily_pi μ)

中文:
定义 piContent
  签名: : 加法内容 实数>=0∞ (measurableCylinders X)
  定义体: projectiveFamilyContent (isProjectiveMeasureFamily_pi μ)

Depends on / 依赖: isProjectiveMeasureFamily_pi, projectiveFamilyContent
-/
noncomputable def piContent : AddContent Real>=0∞ (measurableCylinders X) :=
  projectiveFamilyContent (isProjectiveMeasureFamily_pi μ)

/--
lemma `piContent_cylinder` / 引理 `piContent_cylinder`

English:
lemma piContent_cylinder
  given: {I : Finset ι} {S : Set (Π i : I, X i)} (hS : MeasurableSet S)
  proof: projectiveFamilyContent_cylinder _ hS

中文:
引理 piContent_cylinder
  条件: {I : 有限集 ι} {S : 集合 (Π i : I, X i)} (hS : 可测集 S)
  证明: projectiveFamilyContent_cylinder _ hS

Depends on / 依赖: projectiveFamilyContent_cylinder
-/
lemma piContent_cylinder {I : Finset ι} {S : Set (Π i : I, X i)} (hS : MeasurableSet S) :
    piContent μ (cylinder I S) = Measure.pi (fun i : I => μ i) S :=
  projectiveFamilyContent_cylinder _ hS

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `piContent_eq_measure_pi` / 定理 `piContent_eq_measure_pi`

English:
theorem piContent_eq_measure_pi
  given: [Fintype ι] {s : Set (Π i, X i)} (hs : MeasurableSet s)
  proof: by
  let e : @Finset.univ ι _ ≃ ι :=
    { toFun i := i
      invFun i := ⟨i, mem_univ i⟩ }
  have : s = cylinder univ (MeasurableEquiv.piCongrLeft X e ⁻¹' s) := rfl
  nth_rw 1 [this]
  dsimp [e]
  rw [piContent_cylinder _ (hs.preimage (by fun_prop))]; rw [← Measure.pi_map_piCongrLeft e]; rw [← Measure.map_apply (by fun_prop) hs]; rfl

中文:
定理 piContent_eq_measure_pi
  条件: [有限类型 ι] {s : 集合 (Π i, X i)} (hs : 可测集 s)
  证明: by
  let e : @Finset.univ ι _ ≃ ι :=
    { toFun i := i
      invFun i := ⟨i, mem_univ i⟩ }
  have : s = cylinder univ (MeasurableEquiv.piCongrLeft X e ⁻¹' s) := rfl
  nth_rw 1 [this]
  dsimp [e]
  rw [piContent_cylinder _ (hs.preimage (by fun_prop))]; rw [← Measure.pi_map_piCongrLeft e]; rw [← Measure.map_apply (by fun_prop) hs]; rfl

Depends on / 依赖: Finset, Finset.univ, MeasurableEquiv, MeasurableEquiv.piCongrLeft, Measure, Measure.map_apply, Measure.pi_map_piCongrLeft, cylinder, fun_prop, hs.preimage, invFun, map_apply, mem_univ, nth_rw, piCongrLeft, piContent_cylinder, pi_map_piCongrLeft, preimage
-/
theorem piContent_eq_measure_pi [Fintype ι] {s : Set (Π i, X i)} (hs : MeasurableSet s) :
    piContent μ s = Measure.pi μ s := by
  let e : @Finset.univ ι _ ≃ ι :=
    { toFun i := i
      invFun i := ⟨i, mem_univ i⟩ }
  have : s = cylinder univ (MeasurableEquiv.piCongrLeft X e ⁻¹' s) := rfl
  nth_rw 1 [this]
  dsimp [e]
  rw [piContent_cylinder _ (hs.preimage (by fun_prop))]; rw [← Measure.pi_map_piCongrLeft e]; rw [← Measure.map_apply (by fun_prop) hs]; rfl

end Preliminaries

section Nat

open Kernel

/-! ### Product of measures indexed by `ℕ` -/

variable {X : Nat -> Type*}

variable {mX : forall n, MeasurableSpace (X n)}
  (μ : (n : Nat) -> Measure (X n)) [hμ : forall n, IsProbabilityMeasure (μ n)]

namespace Measure

/--
Definition of `infinitePiNat` / `infinitePiNat` 的定义

English:
definition infinitePiNat
  signature: : Measure (Π n, X n)
  body: (traj (fun n => const _ (μ (n + 1))) 0) ∘ₘ (Measure.pi (fun i : Iic 0 => μ i))

中文:
定义 infinitePi自然数
  签名: : 测度 (Π n, X n)
  定义体: (traj (fun n => const _ (μ (n + 1))) 0) ∘ₘ (Measure.pi (fun i : Iic 0 => μ i))

Depends on / 依赖: Measure, Measure.pi
-/
noncomputable def infinitePiNat : Measure (Π n, X n) :=
  (traj (fun n => const _ (μ (n + 1))) 0) ∘ₘ (Measure.pi (fun i : Iic 0 => μ i))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsProbabilityMeasure (Measure.infinitePiNat μ)
  body: by
  rw [Measure.infinitePiNat]; infer_instance

中文:
实例 :
  签名: 是概率测度 (测度.infinitePi自然数 μ)
  定义体: by
  rw [Measure.infinitePiNat]; infer_instance

Depends on / 依赖: Measure, Measure.infinitePiNat, infer_instance, infinitePiNat
-/
instance : IsProbabilityMeasure (Measure.infinitePiNat μ) := by
  rw [Measure.infinitePiNat]; infer_instance

/--
lemma `pi_prod_map_IocProdIoc` / 引理 `pi_prod_map_IocProdIoc`

English:
lemma pi_prod_map_IocProdIoc
  given: {a b c : Nat} (hab : a <= b) (hbc : b <= c)
  proof: by
  refine (Measure.pi_eq fun s ms => ?_).symm
  simp_rw [Measure.map_apply measurable_IocProdIoc (.univ_pi ms), IocProdIoc_preimage hab hbc,
    Measure.prod_prod, Measure.pi_pi, prod_eq_prod_extend]
  nth_rw 1 [Eq.comm, ← Ioc_union_Ioc_eq_Ioc hab hbc, prod_union (Ioc_disjoint_Ioc_of_le le_rfl)]
  congr 1 <;> refine prod_congr rfl fun x hx => ?_
  · rw [Function.extend_val_apply hx, Function.extend_val_apply (Ioc_subset_Ioc_right hbc hx),
      restrict₂]
  · rw [Function.extend_val_apply hx, Function.extend_val_apply (Ioc_subset_Ioc_left hab hx),
      restrict₂]

中文:
引理 pi_prod_map_IocProdIoc
  条件: {a b c : 自然数} (hab : a <= b) (hbc : b <= c)
  证明: by
  refine (Measure.pi_eq fun s ms => ?_).symm
  simp_rw [Measure.map_apply measurable_IocProdIoc (.univ_pi ms), IocProdIoc_preimage hab hbc,
    Measure.prod_prod, Measure.pi_pi, prod_eq_prod_extend]
  nth_rw 1 [Eq.comm, ← Ioc_union_Ioc_eq_Ioc hab hbc, prod_union (Ioc_disjoint_Ioc_of_le le_rfl)]
  congr 1 <;> refine prod_congr rfl fun x hx => ?_
  · rw [Function.extend_val_apply hx, Function.extend_val_apply (Ioc_subset_Ioc_right hbc hx),
      restrict₂]
  · rw [Function.extend_val_apply hx, Function.extend_val_apply (Ioc_subset_Ioc_left hab hx),
      restrict₂]

Depends on / 依赖: Eq.comm, Function, Function.extend_val_ap, Function.extend_val_apply, IocProdIoc_preimage, Ioc_disjoint_Ioc_of_le, Ioc_subset_Ioc_right, Ioc_union_Ioc_eq_Ioc, Measure, Measure.map_apply, Measure.pi_eq, Measure.pi_pi, Measure.prod_prod, extend_val_ap, extend_val_apply, le_rfl, map_apply, measurable_IocProdIoc, nth_rw, pi_eq
-/
lemma pi_prod_map_IocProdIoc {a b c : Nat} (hab : a <= b) (hbc : b <= c) :
    ((Measure.pi (fun i : Ioc a b => μ i)).prod (Measure.pi (fun i : Ioc b c => μ i))).map
      (IocProdIoc a b c) = Measure.pi (fun i : Ioc a c => μ i) := by
  refine (Measure.pi_eq fun s ms => ?_).symm
  simp_rw [Measure.map_apply measurable_IocProdIoc (.univ_pi ms), IocProdIoc_preimage hab hbc,
    Measure.prod_prod, Measure.pi_pi, prod_eq_prod_extend]
  nth_rw 1 [Eq.comm, ← Ioc_union_Ioc_eq_Ioc hab hbc, prod_union (Ioc_disjoint_Ioc_of_le le_rfl)]
  congr 1 <;> refine prod_congr rfl fun x hx => ?_
  · rw [Function.extend_val_apply hx, Function.extend_val_apply (Ioc_subset_Ioc_right hbc hx),
      restrict₂]
  · rw [Function.extend_val_apply hx, Function.extend_val_apply (Ioc_subset_Ioc_left hab hx),
      restrict₂]

/--
lemma `pi_prod_map_IicProdIoc` / 引理 `pi_prod_map_IicProdIoc`

English:
lemma pi_prod_map_IicProdIoc
  given: {a b : Nat}
  proof: by
  obtain hab | hba := le_total a b
  · refine (Measure.pi_eq fun s ms => ?_).symm
    simp_rw [Measure.map_apply measurable_IicProdIoc (.univ_pi ms), IicProdIoc_preimage hab,
      Measure.prod_prod, Measure.pi_pi, prod_eq_prod_extend]
    nth_rw 1 [Eq.comm, ← Iic_union_Ioc_eq_Iic hab, prod_union (Iic_disjoint_Ioc le_rfl)]
    congr 1 <;> refine prod_congr rfl fun x hx => ?_
    · rw [Function.extend_val_apply hx, Function.extend_val_apply (Iic_subset_Iic.2 hab hx),
        frestrictLe₂, restrict₂]
    · rw [Function.extend_val_apply hx, Function.extend_val_apply (Ioc_subset_Iic_self hx),
        restrict₂]
  · rw [IicProdIoc_le hba, ← Measure.map_map, ← Measure.fst, Measure.fst_prod]
.symm · exact isProjectiveMeasureFamily_pi μ (Iic a) (Iic b) (Iic_subset_Iic.2 hba)
    all_goals fun_prop

中文:
引理 pi_prod_map_IicProdIoc
  条件: {a b : 自然数}
  证明: by
  obtain hab | hba := le_total a b
  · refine (Measure.pi_eq fun s ms => ?_).symm
    simp_rw [Measure.map_apply measurable_IicProdIoc (.univ_pi ms), IicProdIoc_preimage hab,
      Measure.prod_prod, Measure.pi_pi, prod_eq_prod_extend]
    nth_rw 1 [Eq.comm, ← Iic_union_Ioc_eq_Iic hab, prod_union (Iic_disjoint_Ioc le_rfl)]
    congr 1 <;> refine prod_congr rfl fun x hx => ?_
    · rw [Function.extend_val_apply hx, Function.extend_val_apply (Iic_subset_Iic.2 hab hx),
        frestrictLe₂, restrict₂]
    · rw [Function.extend_val_apply hx, Function.extend_val_apply (Ioc_subset_Iic_self hx),
        restrict₂]
  · rw [IicProdIoc_le hba, ← Measure.map_map, ← Measure.fst, Measure.fst_prod]
.symm · exact isProjectiveMeasureFamily_pi μ (Iic a) (Iic b) (Iic_subset_Iic.2 hba)
    all_goals fun_prop

Depends on / 依赖: Eq.comm, Function, Function.extend_val_a, Function.extend_val_apply, IicProdIoc_preimage, Iic_disjoint_Ioc, Iic_subset_Iic, Iic_union_Ioc_eq_Iic, Measure, Measure.map_apply, Measure.pi_eq, Measure.pi_pi, Measure.prod_prod, extend_val_a, extend_val_apply, le_rfl, le_total, map_apply, measurable_IicProdIoc, nth_rw
-/
lemma pi_prod_map_IicProdIoc {a b : Nat} :
    ((Measure.pi (fun i : Iic a => μ i)).prod (Measure.pi (fun i : Ioc a b => μ i))).map
      (IicProdIoc a b) = Measure.pi (fun i : Iic b => μ i) := by
  obtain hab | hba := le_total a b
  · refine (Measure.pi_eq fun s ms => ?_).symm
    simp_rw [Measure.map_apply measurable_IicProdIoc (.univ_pi ms), IicProdIoc_preimage hab,
      Measure.prod_prod, Measure.pi_pi, prod_eq_prod_extend]
    nth_rw 1 [Eq.comm, ← Iic_union_Ioc_eq_Iic hab, prod_union (Iic_disjoint_Ioc le_rfl)]
    congr 1 <;> refine prod_congr rfl fun x hx => ?_
    · rw [Function.extend_val_apply hx, Function.extend_val_apply (Iic_subset_Iic.2 hab hx),
        frestrictLe₂, restrict₂]
    · rw [Function.extend_val_apply hx, Function.extend_val_apply (Ioc_subset_Iic_self hx),
        restrict₂]
  · rw [IicProdIoc_le hba, ← Measure.map_map, ← Measure.fst, Measure.fst_prod]
.symm · exact isProjectiveMeasureFamily_pi μ (Iic a) (Iic b) (Iic_subset_Iic.2 hba)
    all_goals fun_prop

/--
lemma `map_piSingleton` / 引理 `map_piSingleton`

English:
lemma map_piSingleton
  given: (μ : (n : Nat) -> Measure (X n)) [forall n, SigmaFinite (μ n)] (n : Nat)
  proof: by
  refine (Measure.pi_eq fun s hs => ?_).symm
  have : Subsingleton (Ioc n (n + 1)) := by rw [Nat.Ioc_succ_singleton]; infer_instance
  rw [Fintype.prod_subsingleton _ ⟨n + 1]; rw [mem_Ioc.2 (by lia)⟩]; rw [Measure.map_apply (by fun_prop) (.univ_pi hs)]
  congr 1 with x
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const, Subtype.forall,
    Nat.Ioc_succ_singleton, mem_singleton]
  exact ⟨fun h => h (n + 1) rfl, fun h a b => b.symm ▸ h⟩

中文:
引理 map_piSingleton
  条件: (μ : (n : 自然数) -> 测度 (X n)) [对任意 n, σ有限 (μ n)] (n : 自然数)
  证明: by
  refine (Measure.pi_eq fun s hs => ?_).symm
  have : Subsingleton (Ioc n (n + 1)) := by rw [Nat.Ioc_succ_singleton]; infer_instance
  rw [Fintype.prod_subsingleton _ ⟨n + 1]; rw [mem_Ioc.2 (by lia)⟩]; rw [Measure.map_apply (by fun_prop) (.univ_pi hs)]
  congr 1 with x
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const, Subtype.forall,
    Nat.Ioc_succ_singleton, mem_singleton]
  exact ⟨fun h => h (n + 1) rfl, fun h a b => b.symm ▸ h⟩

Depends on / 依赖: Fintype, Fintype.prod_subsingleton, Ioc_succ_singleton, Measure, Measure.map_apply, Measure.pi_eq, Nat.Ioc_succ_singleton, Set.mem_pi, Set.mem_preimage, Set.mem_univ, Subsingleton, Subtype, Subtype.forall, b.symm, forall_const, fun_prop, infer_instance, map_apply, mem_Ioc, mem_pi
-/
lemma map_piSingleton (μ : (n : Nat) -> Measure (X n)) [forall n, SigmaFinite (μ n)] (n : Nat) :
    (μ (n + 1)).map (piSingleton n) = Measure.pi (fun i : Ioc n (n + 1) => μ i) := by
  refine (Measure.pi_eq fun s hs => ?_).symm
  have : Subsingleton (Ioc n (n + 1)) := by rw [Nat.Ioc_succ_singleton]; infer_instance
  rw [Fintype.prod_subsingleton _ ⟨n + 1]; rw [mem_Ioc.2 (by lia)⟩]; rw [Measure.map_apply (by fun_prop) (.univ_pi hs)]
  congr 1 with x
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const, Subtype.forall,
    Nat.Ioc_succ_singleton, mem_singleton]
  exact ⟨fun h => h (n + 1) rfl, fun h a b => b.symm ▸ h⟩

end Measure

/--
theorem `partialTraj_const_restrict₂` / 定理 `partialTraj_const_restrict₂`

English:
theorem partialTraj_const_restrict₂
  given: {a b : Nat}
  proof: by
  obtain hab | hba := lt_or_ge a b
  · refine Nat.le_induction ?_ (fun n hn hind => ?_) b (Nat.succ_le_of_lt hab) <;> ext1 x₀
    · rw [partialTraj_succ_self, ← map_comp_right, map_apply, prod_apply, map_apply, const_apply,
        const_apply, Measure.map_piSingleton, restrict₂_comp_IicProdIoc, Measure.map_snd_prod,
        measure_univ, one_smul]
      all_goals fun_prop
    · have : (restrict₂ (Ioc_subset_Iic_self (a := a))) ∘ (IicProdIoc (X := X) n (n + 1)) =
          (IocProdIoc a n (n + 1)) ∘ (Prod.map (restrict₂ Ioc_subset_Iic_self) id) := rfl
      rw [const_apply]; rw [partialTraj_succ_of_le (by lia)]; rw [map_const]; rw [prod_const_comp]; rw [id_comp]; rw [← map_comp_right]; rw [this]; rw [map_comp_right]; rw [← map_prod_map]; rw [hind]; rw [Kernel.map_id]; rw [map_apply]; rw [prod_apply]; rw [const_apply]; rw [const_apply]; rw [Measure.map_piSingleton]; rw [Measure.pi_prod_map_IocProdIoc]
      any_goals fun_prop
      all_goals lia
  · have : IsEmpty (Ioc a b) := by simpa [hba] using Subtype.isEmpty_false
    ext x s ms
    by_cases hs : s.Nonempty
    · rw [Subsingleton.eq_univ_of_nonempty hs, @measure_univ .., measure_univ]
.isProbabilityMeasure x exact (IsMarkovKernel.map _ (measurable_restrict₂ _))
    · rw [Set.not_nonempty_iff_eq_empty.1 hs]
      simp

中文:
定理 partialTraj_const_restrict₂
  条件: {a b : 自然数}
  证明: by
  obtain hab | hba := lt_or_ge a b
  · refine Nat.le_induction ?_ (fun n hn hind => ?_) b (Nat.succ_le_of_lt hab) <;> ext1 x₀
    · rw [partialTraj_succ_self, ← map_comp_right, map_apply, prod_apply, map_apply, const_apply,
        const_apply, Measure.map_piSingleton, restrict₂_comp_IicProdIoc, Measure.map_snd_prod,
        measure_univ, one_smul]
      all_goals fun_prop
    · have : (restrict₂ (Ioc_subset_Iic_self (a := a))) ∘ (IicProdIoc (X := X) n (n + 1)) =
          (IocProdIoc a n (n + 1)) ∘ (Prod.map (restrict₂ Ioc_subset_Iic_self) id) := rfl
      rw [const_apply]; rw [partialTraj_succ_of_le (by lia)]; rw [map_const]; rw [prod_const_comp]; rw [id_comp]; rw [← map_comp_right]; rw [this]; rw [map_comp_right]; rw [← map_prod_map]; rw [hind]; rw [Kernel.map_id]; rw [map_apply]; rw [prod_apply]; rw [const_apply]; rw [const_apply]; rw [Measure.map_piSingleton]; rw [Measure.pi_prod_map_IocProdIoc]
      any_goals fun_prop
      all_goals lia
  · have : IsEmpty (Ioc a b) := by simpa [hba] using Subtype.isEmpty_false
    ext x s ms
    by_cases hs : s.Nonempty
    · rw [Subsingleton.eq_univ_of_nonempty hs, @measure_univ .., measure_univ]
.isProbabilityMeasure x exact (IsMarkovKernel.map _ (measurable_restrict₂ _))
    · rw [Set.not_nonempty_iff_eq_empty.1 hs]
      simp

Depends on / 依赖: IicProdIoc, IocProdIoc, Ioc_subset_Iic_, Ioc_subset_Iic_self, Measure, Measure.map_piSingleton, Measure.map_snd_prod, Nat.le_induction, Nat.succ_le_of_lt, Prod.map, all_goals, const_apply, fun_prop, le_induction, lt_or_ge, map_apply, map_comp_right, map_piSingleton, map_snd_prod, measure_univ
-/
theorem partialTraj_const_restrict₂ {a b : Nat} :
    (partialTraj (fun n => const _ (μ (n + 1))) a b).map (restrict₂ Ioc_subset_Iic_self) =
    const _ (Measure.pi (fun i : Ioc a b => μ i)) := by
  obtain hab | hba := lt_or_ge a b
  · refine Nat.le_induction ?_ (fun n hn hind => ?_) b (Nat.succ_le_of_lt hab) <;> ext1 x₀
    · rw [partialTraj_succ_self, ← map_comp_right, map_apply, prod_apply, map_apply, const_apply,
        const_apply, Measure.map_piSingleton, restrict₂_comp_IicProdIoc, Measure.map_snd_prod,
        measure_univ, one_smul]
      all_goals fun_prop
    · have : (restrict₂ (Ioc_subset_Iic_self (a := a))) ∘ (IicProdIoc (X := X) n (n + 1)) =
          (IocProdIoc a n (n + 1)) ∘ (Prod.map (restrict₂ Ioc_subset_Iic_self) id) := rfl
      rw [const_apply]; rw [partialTraj_succ_of_le (by lia)]; rw [map_const]; rw [prod_const_comp]; rw [id_comp]; rw [← map_comp_right]; rw [this]; rw [map_comp_right]; rw [← map_prod_map]; rw [hind]; rw [Kernel.map_id]; rw [map_apply]; rw [prod_apply]; rw [const_apply]; rw [const_apply]; rw [Measure.map_piSingleton]; rw [Measure.pi_prod_map_IocProdIoc]
      any_goals fun_prop
      all_goals lia
  · have : IsEmpty (Ioc a b) := by simpa [hba] using Subtype.isEmpty_false
    ext x s ms
    by_cases hs : s.Nonempty
    · rw [Subsingleton.eq_univ_of_nonempty hs, @measure_univ .., measure_univ]
.isProbabilityMeasure x exact (IsMarkovKernel.map _ (measurable_restrict₂ _))
    · rw [Set.not_nonempty_iff_eq_empty.1 hs]
      simp

/--
theorem `partialTraj_const` / 定理 `partialTraj_const`

English:
theorem partialTraj_const
  given: {a b : Nat}
  proof: by
  rw [partialTraj_eq_prod]; rw [partialTraj_const_restrict₂]

中文:
定理 partialTraj_const
  条件: {a b : 自然数}
  证明: by
  rw [partialTraj_eq_prod]; rw [partialTraj_const_restrict₂]

Depends on / 依赖: partialTraj_eq_prod
-/
theorem partialTraj_const {a b : Nat} :
    partialTraj (fun n => const _ (μ (n + 1))) a b =
      (Kernel.id ×ₖ (const _ (Measure.pi (fun i : Ioc a b => μ i)))).map (IicProdIoc a b) := by
  rw [partialTraj_eq_prod]; rw [partialTraj_const_restrict₂]

namespace Measure

/--
theorem `isProjectiveLimit_infinitePiNat` / 定理 `isProjectiveLimit_infinitePiNat`

English:
theorem isProjectiveLimit_infinitePiNat
  proof: by
  intro I
  rw [isProjectiveMeasureFamily_pi μ _ _ I.subset_Iic_sup_id]; rw [← restrict₂_comp_restrict I.subset_Iic_sup_id]; rw [← map_map]; rw [← frestrictLe]; rw [infinitePiNat]; rw [map_comp]; rw [traj_map_frestrictLe]; rw [partialTraj_const]; rw [← map_comp]; rw [← compProd_eq_comp_prod]; rw [compProd_const]; rw [pi_prod_map_IicProdIoc]
  all_goals fun_prop

中文:
定理 isProjectiveLimit_infinitePi自然数
  证明: by
  intro I
  rw [isProjectiveMeasureFamily_pi μ _ _ I.subset_Iic_sup_id]; rw [← restrict₂_comp_restrict I.subset_Iic_sup_id]; rw [← map_map]; rw [← frestrictLe]; rw [infinitePiNat]; rw [map_comp]; rw [traj_map_frestrictLe]; rw [partialTraj_const]; rw [← map_comp]; rw [← compProd_eq_comp_prod]; rw [compProd_const]; rw [pi_prod_map_IicProdIoc]
  all_goals fun_prop

Depends on / 依赖: I.subset_Iic_sup_id, all_goals, compProd_const, compProd_eq_comp_prod, frestrictLe, fun_prop, infinitePiNat, isProjectiveMeasureFamily_pi, map_comp, map_map, partialTraj_const, pi_prod_map_IicProdIoc, subset_Iic_sup_id, traj_map_frestrictLe
-/
theorem isProjectiveLimit_infinitePiNat :
    IsProjectiveLimit (infinitePiNat μ) (fun I : Finset Nat => (Measure.pi (fun i : I => μ i))) := by
  intro I
  rw [isProjectiveMeasureFamily_pi μ _ _ I.subset_Iic_sup_id]; rw [← restrict₂_comp_restrict I.subset_Iic_sup_id]; rw [← map_map]; rw [← frestrictLe]; rw [infinitePiNat]; rw [map_comp]; rw [traj_map_frestrictLe]; rw [partialTraj_const]; rw [← map_comp]; rw [← compProd_eq_comp_prod]; rw [compProd_const]; rw [pi_prod_map_IicProdIoc]
  all_goals fun_prop

/--
lemma `infinitePiNat_map_restrict` / 引理 `infinitePiNat_map_restrict`

English:
lemma infinitePiNat_map_restrict
  given: (I : Finset Nat)
  proof: isProjectiveLimit_infinitePiNat μ I

中文:
引理 infinitePi自然数_map_restrict
  条件: (I : 有限集 自然数)
  证明: isProjectiveLimit_infinitePiNat μ I

Depends on / 依赖: isProjectiveLimit_infinitePiNat
-/
lemma infinitePiNat_map_restrict (I : Finset Nat) :
    (infinitePiNat μ).map I.restrict = Measure.pi fun i : I => μ i :=
  isProjectiveLimit_infinitePiNat μ I

/--
theorem `piContent_eq_infinitePiNat` / 定理 `piContent_eq_infinitePiNat`

English:
theorem piContent_eq_infinitePiNat
  given: {A : Set (Π n, X n)} (hA : A in measurableCylinders X)
  proof: by
  obtain ⟨s, S, mS, rfl⟩ : exists s S, MeasurableSet S ∧ A = cylinder s S := by
    simpa [mem_measurableCylinders] using hA
  rw [piContent_cylinder _ mS]; rw [cylinder]; rw [← map_apply (measurable_restrict _) mS]; rw [infinitePiNat_map_restrict]

中文:
定理 piContent_eq_infinitePi自然数
  条件: {A : 集合 (Π n, X n)} (hA : A in measurableCylinders X)
  证明: by
  obtain ⟨s, S, mS, rfl⟩ : exists s S, MeasurableSet S ∧ A = cylinder s S := by
    simpa [mem_measurableCylinders] using hA
  rw [piContent_cylinder _ mS]; rw [cylinder]; rw [← map_apply (measurable_restrict _) mS]; rw [infinitePiNat_map_restrict]

Depends on / 依赖: MeasurableSet, cylinder, infinitePiNat_map_restrict, map_apply, measurable_restrict, mem_measurableCylinders, piContent_cylinder
-/
theorem piContent_eq_infinitePiNat {A : Set (Π n, X n)} (hA : A in measurableCylinders X) :
    piContent μ A = infinitePiNat μ A := by
  obtain ⟨s, S, mS, rfl⟩ : exists s S, MeasurableSet S ∧ A = cylinder s S := by
    simpa [mem_measurableCylinders] using hA
  rw [piContent_cylinder _ mS]; rw [cylinder]; rw [← map_apply (measurable_restrict _) mS]; rw [infinitePiNat_map_restrict]

end Measure

end Nat

section InfinitePi

open Measure

/-! ### Product of infinitely many probability measures -/

variable {ι : Type*} {X : ι -> Type*} {mX : forall i, MeasurableSpace (X i)}
  (μ : (i : ι) -> Measure (X i)) [hμ : forall i, IsProbabilityMeasure (μ i)]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `Measure.infinitePiNat_map_piCongrLeft` / 引理 `Measure.infinitePiNat_map_piCongrLeft`

English:
lemma Measure.infinitePiNat_map_piCongrLeft
  statement: (e : Nat ≃ ι) {s : Set (Π i, X i)}
  proof: by
  obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders s).1 hs
  rw [map_apply _ hS.cylinder]; rw [cylinder]; rw [← Set.preimage_comp]; rw [coe_piCongrLeft]; rw [restrict_comp_piCongrLeft]; rw [Set.preimage_comp]; rw [← map_apply]; rw [infinitePiNat_map_restrict (fun n => μ (e n))]; rw [← cylinder]; rw [piContent_cylinder μ hS]; rw [← pi_map_piCongrLeft (e.restrictPreimageFinset I)]; rw [map_apply _ hS]; rw [coe_piCongrLeft]
  · simp
  any_goals fun_prop
  exact hS.preimage (by fun_prop)

中文:
引理 测度.infinitePi自然数_map_piCongrLeft
  结论: (e : 自然数 ≃ ι) {s : 集合 (Π i, X i)}
  证明: by
  obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders s).1 hs
  rw [map_apply _ hS.cylinder]; rw [cylinder]; rw [← Set.preimage_comp]; rw [coe_piCongrLeft]; rw [restrict_comp_piCongrLeft]; rw [Set.preimage_comp]; rw [← map_apply]; rw [infinitePiNat_map_restrict (fun n => μ (e n))]; rw [← cylinder]; rw [piContent_cylinder μ hS]; rw [← pi_map_piCongrLeft (e.restrictPreimageFinset I)]; rw [map_apply _ hS]; rw [coe_piCongrLeft]
  · simp
  any_goals fun_prop
  exact hS.preimage (by fun_prop)

Depends on / 依赖: Set.preimage_comp, any_goals, coe_piCongrLeft, cylinder, e.restrictPreimageFinset, fun_prop, hS.cylinder, hS.preimage, infinitePiNat_map_restrict, map_apply, mem_measurableCylinders, piContent_cylinder, pi_map_piCongrLeft, preimage, preimage_comp, restrictPreimageFinset, restrict_comp_piCongrLeft
-/
lemma Measure.infinitePiNat_map_piCongrLeft (e : Nat ≃ ι) {s : Set (Π i, X i)}
    (hs : s in measurableCylinders X) :
    (infinitePiNat (fun n => μ (e n))).map (piCongrLeft X e) s = piContent μ s := by
  obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders s).1 hs
  rw [map_apply _ hS.cylinder]; rw [cylinder]; rw [← Set.preimage_comp]; rw [coe_piCongrLeft]; rw [restrict_comp_piCongrLeft]; rw [Set.preimage_comp]; rw [← map_apply]; rw [infinitePiNat_map_restrict (fun n => μ (e n))]; rw [← cylinder]; rw [piContent_cylinder μ hS]; rw [← pi_map_piCongrLeft (e.restrictPreimageFinset I)]; rw [map_apply _ hS]; rw [coe_piCongrLeft]
  · simp
  any_goals fun_prop
  exact hS.preimage (by fun_prop)

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `piContent_tendsto_zero` / 定理 `piContent_tendsto_zero`

English:
theorem piContent_tendsto_zero
  statement: {A : Nat -> Set (Π i, X i)} (A_mem : forall n, A n in measurableCylinders X)
  proof: by
  have : forall i, Nonempty (X i) := fun i => nonempty_of_isProbabilityMeasure (μ i)
  have A_cyl n : exists s S, MeasurableSet S ∧ A n = cylinder s S :=
    (mem_measurableCylinders _).1 (A_mem n)
  choose s S mS A_eq using A_cyl
  -- The family `(Aₙ)` only depends on a countable set of coordinates, called `u`. Therefore our
  -- goal is to see it as a family indexed by this countable set, because on the product indexed
  -- by this countable set we can build a measure. To do so we have to pull back our cylinders
  -- along the injection from `Π i : u, X i` to `Π i, X i`.
  let u := ⋃ n, (s n : Set ι)
  -- `tₙ` will be `sₙ` seen as a subset of `u`.
  let t n : Finset u := (s n).preimage Subtype.val Subtype.val_injective.injOn
  classical
  -- The map `f` allows to pull back `Aₙ`
  let f : (Π i : u, X i) -> Π i, X i :=
    fun x i => if hi : i in u then x ⟨i, hi⟩ else Classical.ofNonempty
  -- `aux` is the obvious equivalence between `sₙ` and `tₙ`
  let aux n : t n ≃ s n :=
    { toFun := fun i => ⟨i.1.1, mem_preimage.1 i.2⟩
      invFun := fun i => ⟨⟨i.1, Set.mem_iUnion.2 ⟨n, i.2⟩⟩, mem_preimage.2 i.2⟩
      left_inv := fun i => by simp
      right_inv := fun i => by simp }
  -- Finally `gₙ` is the equivalence between the product indexed by `tₙ` and the one indexed by `sₙ`
  let g n := (aux n).piCongrLeft (fun i : s n => X i)
  -- Mapping from the product indexed by `u` by `f` and then restricting to `sₙ` is the same as
  -- first restricting to `tₙ` and then mapping by `gₙ`
  have r_comp_f n : (s n).restrict ∘ f = (g n) ∘ (fun (x : Π i : u, X i) i => x i) := by
    ext x i
    simp only [Function.comp_apply, Finset.restrict,
      Equiv.piCongrLeft_apply, Equiv.coe_fn_symm_mk, f, aux, g, t]
    rw [dif_pos (Set.mem_iUnion.2 ⟨n]; rw [i.2⟩)]
  -- `Bₙ` is the same as `Aₙ` but in the product indexed by `u`
  let B n := f ⁻¹' (A n)
  -- `Tₙ` is the same as `Sₙ` but in the product indexed by `u`
  let T n := (g n) ⁻¹' (S n)
  -- We now transfer the properties of `Aₙ` and `Sₙ` to `Bₙ` and `Tₙ`
  have B_eq n : B n = cylinder (t n) (T n) := by
    simp_rw [B, A_eq, cylinder, ← Set.preimage_comp, r_comp_f]; rfl
  have mT n : MeasurableSet (T n) := (mS n).preimage (by fun_prop)
  have B_mem n : B n in measurableCylinders (fun i : u => X i) :=
    (mem_measurableCylinders (B n)).2 ⟨t n, T n, mT n, B_eq n⟩
  have mB n : MeasurableSet (B n) := .of_mem_measurableCylinders (B_mem n)
have B_anti : Antitone B := fun m n hmn => Set.preimage_mono A_anti hmn
  have B_inter : ⋂ n, B n = ∅ := by
    simp_rw [B, ← Set.preimage_iInter, A_inter, Set.preimage_empty]
  -- We now rewrite `piContent μ (A n)` as `piContent (fun i : u ↦ μ i) (B n)`. Then there are two
  -- cases: either `u` is finite and we rewrite it to the finite product measure, either
  -- it is countable and we rewrite it to the pushforward measure of `infinitePiNat`. In both cases
  -- we have an actual measure and we can conclude with `tendsto_measure_iInter_atTop`.
  conv =>
    enter [1]; ext n
    rw [A_eq]; rw [piContent_cylinder μ (mS n)]; rw [← pi_map_piCongrLeft (aux n)]; rw [map_apply (by fun_prop) (mS n)]
    change (Measure.pi (fun i : t n => μ i)) (T n)
    rw [← piContent_cylinder (fun i : u => μ i) (mT n)]; rw [← B_eq n]
  obtain u_fin | u_inf := finite_or_infinite u
  · let _ := Fintype.ofFinite u
    simp_rw [fun n => piContent_eq_measure_pi (fun i : u => μ i) (mB n)]
    convert!
      tendsto_measure_iInter_atTop (fun n => (mB n).nullMeasurableSet) B_anti ⟨0, measure_ne_top _ _⟩
    · rw [B_inter, measure_empty]
    · infer_instance
  · -- If `u` is infinite, then we have an equivalence with `ℕ` so we can apply `secondLemma`.
    have count_u : Countable u := Set.countable_iUnion (fun n => (s n).countable_toSet)
    obtain ⟨φ, -⟩ := Classical.exists_true_of_nonempty (α := Nat ≃ u) nonempty_equiv_of_countable
    conv => enter [1]; ext n; rw [← infinitePiNat_map_piCongrLeft _ φ (B_mem n)]
    convert!
      tendsto_measure_iInter_atTop (fun n => (mB n).nullMeasurableSet) B_anti ⟨0, measure_ne_top _ _⟩
    · rw [B_inter, measure_empty]
    · infer_instance

中文:
定理 piContent_tendsto_zero
  结论: {A : 自然数 -> 集合 (Π i, X i)} (A_mem : 对任意 n, A n in measurableCylinders X)
  证明: by
  have : forall i, Nonempty (X i) := fun i => nonempty_of_isProbabilityMeasure (μ i)
  have A_cyl n : exists s S, MeasurableSet S ∧ A n = cylinder s S :=
    (mem_measurableCylinders _).1 (A_mem n)
  choose s S mS A_eq using A_cyl
  -- The family `(Aₙ)` only depends on a countable set of coordinates, called `u`. Therefore our
  -- goal is to see it as a family indexed by this countable set, because on the product indexed
  -- by this countable set we can build a measure. To do so we have to pull back our cylinders
  -- along the injection from `Π i : u, X i` to `Π i, X i`.
  let u := ⋃ n, (s n : Set ι)
  -- `tₙ` will be `sₙ` seen as a subset of `u`.
  let t n : Finset u := (s n).preimage Subtype.val Subtype.val_injective.injOn
  classical
  -- The map `f` allows to pull back `Aₙ`
  let f : (Π i : u, X i) -> Π i, X i :=
    fun x i => if hi : i in u then x ⟨i, hi⟩ else Classical.ofNonempty
  -- `aux` is the obvious equivalence between `sₙ` and `tₙ`
  let aux n : t n ≃ s n :=
    { toFun := fun i => ⟨i.1.1, mem_preimage.1 i.2⟩
      invFun := fun i => ⟨⟨i.1, Set.mem_iUnion.2 ⟨n, i.2⟩⟩, mem_preimage.2 i.2⟩
      left_inv := fun i => by simp
      right_inv := fun i => by simp }
  -- Finally `gₙ` is the equivalence between the product indexed by `tₙ` and the one indexed by `sₙ`
  let g n := (aux n).piCongrLeft (fun i : s n => X i)
  -- Mapping from the product indexed by `u` by `f` and then restricting to `sₙ` is the same as
  -- first restricting to `tₙ` and then mapping by `gₙ`
  have r_comp_f n : (s n).restrict ∘ f = (g n) ∘ (fun (x : Π i : u, X i) i => x i) := by
    ext x i
    simp only [Function.comp_apply, Finset.restrict,
      Equiv.piCongrLeft_apply, Equiv.coe_fn_symm_mk, f, aux, g, t]
    rw [dif_pos (Set.mem_iUnion.2 ⟨n]; rw [i.2⟩)]
  -- `Bₙ` is the same as `Aₙ` but in the product indexed by `u`
  let B n := f ⁻¹' (A n)
  -- `Tₙ` is the same as `Sₙ` but in the product indexed by `u`
  let T n := (g n) ⁻¹' (S n)
  -- We now transfer the properties of `Aₙ` and `Sₙ` to `Bₙ` and `Tₙ`
  have B_eq n : B n = cylinder (t n) (T n) := by
    simp_rw [B, A_eq, cylinder, ← Set.preimage_comp, r_comp_f]; rfl
  have mT n : MeasurableSet (T n) := (mS n).preimage (by fun_prop)
  have B_mem n : B n in measurableCylinders (fun i : u => X i) :=
    (mem_measurableCylinders (B n)).2 ⟨t n, T n, mT n, B_eq n⟩
  have mB n : MeasurableSet (B n) := .of_mem_measurableCylinders (B_mem n)
have B_anti : Antitone B := fun m n hmn => Set.preimage_mono A_anti hmn
  have B_inter : ⋂ n, B n = ∅ := by
    simp_rw [B, ← Set.preimage_iInter, A_inter, Set.preimage_empty]
  -- We now rewrite `piContent μ (A n)` as `piContent (fun i : u ↦ μ i) (B n)`. Then there are two
  -- cases: either `u` is finite and we rewrite it to the finite product measure, either
  -- it is countable and we rewrite it to the pushforward measure of `infinitePiNat`. In both cases
  -- we have an actual measure and we can conclude with `tendsto_measure_iInter_atTop`.
  conv =>
    enter [1]; ext n
    rw [A_eq]; rw [piContent_cylinder μ (mS n)]; rw [← pi_map_piCongrLeft (aux n)]; rw [map_apply (by fun_prop) (mS n)]
    change (Measure.pi (fun i : t n => μ i)) (T n)
    rw [← piContent_cylinder (fun i : u => μ i) (mT n)]; rw [← B_eq n]
  obtain u_fin | u_inf := finite_or_infinite u
  · let _ := Fintype.ofFinite u
    simp_rw [fun n => piContent_eq_measure_pi (fun i : u => μ i) (mB n)]
    convert!
      tendsto_measure_iInter_atTop (fun n => (mB n).nullMeasurableSet) B_anti ⟨0, measure_ne_top _ _⟩
    · rw [B_inter, measure_empty]
    · infer_instance
  · -- If `u` is infinite, then we have an equivalence with `ℕ` so we can apply `secondLemma`.
    have count_u : Countable u := Set.countable_iUnion (fun n => (s n).countable_toSet)
    obtain ⟨φ, -⟩ := Classical.exists_true_of_nonempty (α := Nat ≃ u) nonempty_equiv_of_countable
    conv => enter [1]; ext n; rw [← infinitePiNat_map_piCongrLeft _ φ (B_mem n)]
    convert!
      tendsto_measure_iInter_atTop (fun n => (mB n).nullMeasurableSet) B_anti ⟨0, measure_ne_top _ _⟩
    · rw [B_inter, measure_empty]
    · infer_instance

Depends on / 依赖: A_cyl, A_eq, A_mem, MeasurableSet, Nonempty, cylinder, mem_measurableCylinders, nonempty_of_isProbabilityMeasure
-/
theorem piContent_tendsto_zero {A : Nat -> Set (Π i, X i)} (A_mem : forall n, A n in measurableCylinders X)
    (A_anti : Antitone A) (A_inter : ⋂ n, A n = ∅) :
    Tendsto (fun n => piContent μ (A n)) atTop (𝓝 0) := by
  have : forall i, Nonempty (X i) := fun i => nonempty_of_isProbabilityMeasure (μ i)
  have A_cyl n : exists s S, MeasurableSet S ∧ A n = cylinder s S :=
    (mem_measurableCylinders _).1 (A_mem n)
  choose s S mS A_eq using A_cyl
  -- The family `(Aₙ)` only depends on a countable set of coordinates, called `u`. Therefore our
  -- goal is to see it as a family indexed by this countable set, because on the product indexed
  -- by this countable set we can build a measure. To do so we have to pull back our cylinders
  -- along the injection from `Π i : u, X i` to `Π i, X i`.
  let u := ⋃ n, (s n : Set ι)
  -- `tₙ` will be `sₙ` seen as a subset of `u`.
  let t n : Finset u := (s n).preimage Subtype.val Subtype.val_injective.injOn
  classical
  -- The map `f` allows to pull back `Aₙ`
  let f : (Π i : u, X i) -> Π i, X i :=
    fun x i => if hi : i in u then x ⟨i, hi⟩ else Classical.ofNonempty
  -- `aux` is the obvious equivalence between `sₙ` and `tₙ`
  let aux n : t n ≃ s n :=
    { toFun := fun i => ⟨i.1.1, mem_preimage.1 i.2⟩
      invFun := fun i => ⟨⟨i.1, Set.mem_iUnion.2 ⟨n, i.2⟩⟩, mem_preimage.2 i.2⟩
      left_inv := fun i => by simp
      right_inv := fun i => by simp }
  -- Finally `gₙ` is the equivalence between the product indexed by `tₙ` and the one indexed by `sₙ`
  let g n := (aux n).piCongrLeft (fun i : s n => X i)
  -- Mapping from the product indexed by `u` by `f` and then restricting to `sₙ` is the same as
  -- first restricting to `tₙ` and then mapping by `gₙ`
  have r_comp_f n : (s n).restrict ∘ f = (g n) ∘ (fun (x : Π i : u, X i) i => x i) := by
    ext x i
    simp only [Function.comp_apply, Finset.restrict,
      Equiv.piCongrLeft_apply, Equiv.coe_fn_symm_mk, f, aux, g, t]
    rw [dif_pos (Set.mem_iUnion.2 ⟨n]; rw [i.2⟩)]
  -- `Bₙ` is the same as `Aₙ` but in the product indexed by `u`
  let B n := f ⁻¹' (A n)
  -- `Tₙ` is the same as `Sₙ` but in the product indexed by `u`
  let T n := (g n) ⁻¹' (S n)
  -- We now transfer the properties of `Aₙ` and `Sₙ` to `Bₙ` and `Tₙ`
  have B_eq n : B n = cylinder (t n) (T n) := by
    simp_rw [B, A_eq, cylinder, ← Set.preimage_comp, r_comp_f]; rfl
  have mT n : MeasurableSet (T n) := (mS n).preimage (by fun_prop)
  have B_mem n : B n in measurableCylinders (fun i : u => X i) :=
    (mem_measurableCylinders (B n)).2 ⟨t n, T n, mT n, B_eq n⟩
  have mB n : MeasurableSet (B n) := .of_mem_measurableCylinders (B_mem n)
have B_anti : Antitone B := fun m n hmn => Set.preimage_mono A_anti hmn
  have B_inter : ⋂ n, B n = ∅ := by
    simp_rw [B, ← Set.preimage_iInter, A_inter, Set.preimage_empty]
  -- We now rewrite `piContent μ (A n)` as `piContent (fun i : u ↦ μ i) (B n)`. Then there are two
  -- cases: either `u` is finite and we rewrite it to the finite product measure, either
  -- it is countable and we rewrite it to the pushforward measure of `infinitePiNat`. In both cases
  -- we have an actual measure and we can conclude with `tendsto_measure_iInter_atTop`.
  conv =>
    enter [1]; ext n
    rw [A_eq]; rw [piContent_cylinder μ (mS n)]; rw [← pi_map_piCongrLeft (aux n)]; rw [map_apply (by fun_prop) (mS n)]
    change (Measure.pi (fun i : t n => μ i)) (T n)
    rw [← piContent_cylinder (fun i : u => μ i) (mT n)]; rw [← B_eq n]
  obtain u_fin | u_inf := finite_or_infinite u
  · let _ := Fintype.ofFinite u
    simp_rw [fun n => piContent_eq_measure_pi (fun i : u => μ i) (mB n)]
    convert!
      tendsto_measure_iInter_atTop (fun n => (mB n).nullMeasurableSet) B_anti ⟨0, measure_ne_top _ _⟩
    · rw [B_inter, measure_empty]
    · infer_instance
  · -- If `u` is infinite, then we have an equivalence with `ℕ` so we can apply `secondLemma`.
    have count_u : Countable u := Set.countable_iUnion (fun n => (s n).countable_toSet)
    obtain ⟨φ, -⟩ := Classical.exists_true_of_nonempty (α := Nat ≃ u) nonempty_equiv_of_countable
    conv => enter [1]; ext n; rw [← infinitePiNat_map_piCongrLeft _ φ (B_mem n)]
    convert!
      tendsto_measure_iInter_atTop (fun n => (mB n).nullMeasurableSet) B_anti ⟨0, measure_ne_top _ _⟩
    · rw [B_inter, measure_empty]
    · infer_instance

/--
theorem `isSigmaSubadditive_piContent` / 定理 `isSigmaSubadditive_piContent`

English:
theorem isSigmaSubadditive_piContent
  statement: (piContent μ).IsSigmaSubadditive
  proof: by
  refine isSigmaSubadditive_of_addContent_iUnion_eq_tsum
    isSetRing_measurableCylinders (fun f hf hf_Union hf' => ?_)
  exact addContent_iUnion_eq_sum_of_tendsto_zero isSetRing_measurableCylinders
    (piContent μ) (fun s hs => projectiveFamilyContent_ne_top _)
    (fun _ => piContent_tendsto_zero μ) hf hf_Union hf'

中文:
定理 isSigmaSubadditive_piContent
  结论: (piContent μ).IsSigmaSubadditive
  证明: by
  refine isSigmaSubadditive_of_addContent_iUnion_eq_tsum
    isSetRing_measurableCylinders (fun f hf hf_Union hf' => ?_)
  exact addContent_iUnion_eq_sum_of_tendsto_zero isSetRing_measurableCylinders
    (piContent μ) (fun s hs => projectiveFamilyContent_ne_top _)
    (fun _ => piContent_tendsto_zero μ) hf hf_Union hf'

Depends on / 依赖: addContent_iUnion_eq_sum_of_tendsto_zero, hf_Union, isSetRing_measurableCylinders, isSigmaSubadditive_of_addContent_iUnion_eq_tsum, piContent, piContent_tendsto_zero, projectiveFamilyContent_ne_top
-/
theorem isSigmaSubadditive_piContent : (piContent μ).IsSigmaSubadditive := by
  refine isSigmaSubadditive_of_addContent_iUnion_eq_tsum
    isSetRing_measurableCylinders (fun f hf hf_Union hf' => ?_)
  exact addContent_iUnion_eq_sum_of_tendsto_zero isSetRing_measurableCylinders
    (piContent μ) (fun s hs => projectiveFamilyContent_ne_top _)
    (fun _ => piContent_tendsto_zero μ) hf hf_Union hf'

namespace Measure

open scoped Classical in
/--
Definition of `infinitePi` / `infinitePi` 的定义

English:
definition infinitePi
  signature: : Measure (Π i, X i)
  body: if h : forall i, IsProbabilityMeasure (μ i) then
    (piContent μ).measure isSetSemiring_measurableCylinders
      generateFrom_measurableCylinders.ge (isSigmaSubadditive_piContent (hμ := h) μ)
    else 0

中文:
定义 infinitePi
  签名: : 测度 (Π i, X i)
  定义体: if h : forall i, IsProbabilityMeasure (μ i) then
    (piContent μ).measure isSetSemiring_measurableCylinders
      generateFrom_measurableCylinders.ge (isSigmaSubadditive_piContent (hμ := h) μ)
    else 0

Depends on / 依赖: IsProbabilityMeasure, generateFrom_measurableCylinders, generateFrom_measurableCylinders.ge, isSetSemiring_measurableCylinders, isSigmaSubadditive_piContent, measure, piContent
-/
noncomputable def infinitePi : Measure (Π i, X i) :=
  if h : forall i, IsProbabilityMeasure (μ i) then
    (piContent μ).measure isSetSemiring_measurableCylinders
      generateFrom_measurableCylinders.ge (isSigmaSubadditive_piContent (hμ := h) μ)
    else 0

/--
theorem `isProjectiveLimit_infinitePi` / 定理 `isProjectiveLimit_infinitePi`

English:
theorem isProjectiveLimit_infinitePi
  proof: by
  intro I
  ext s hs
  rw [map_apply (measurable_restrict I) hs]; rw [infinitePi]; rw [dif_pos hμ]; rw [AddContent.measure_eq]; rw [← cylinder]; rw [piContent_cylinder μ hs]
  · exact generateFrom_measurableCylinders.symm
  · exact cylinder_mem_measurableCylinders _ _ hs

中文:
定理 isProjectiveLimit_infinitePi
  证明: by
  intro I
  ext s hs
  rw [map_apply (measurable_restrict I) hs]; rw [infinitePi]; rw [dif_pos hμ]; rw [AddContent.measure_eq]; rw [← cylinder]; rw [piContent_cylinder μ hs]
  · exact generateFrom_measurableCylinders.symm
  · exact cylinder_mem_measurableCylinders _ _ hs

Depends on / 依赖: AddContent, AddContent.measure_eq, cylinder, cylinder_mem_measurableCylinders, dif_pos, generateFrom_measurableCylinders, generateFrom_measurableCylinders.symm, infinitePi, map_apply, measurable_restrict, measure_eq, piContent_cylinder
-/
theorem isProjectiveLimit_infinitePi :
    IsProjectiveLimit (infinitePi μ) (fun I : Finset ι => (Measure.pi (fun i : I => μ i))) := by
  intro I
  ext s hs
  rw [map_apply (measurable_restrict I) hs]; rw [infinitePi]; rw [dif_pos hμ]; rw [AddContent.measure_eq]; rw [← cylinder]; rw [piContent_cylinder μ hs]
  · exact generateFrom_measurableCylinders.symm
  · exact cylinder_mem_measurableCylinders _ _ hs

/--
theorem `infinitePi_map_restrict` / 定理 `infinitePi_map_restrict`

English:
theorem infinitePi_map_restrict
  given: {I : Finset ι}
  proof: isProjectiveLimit_infinitePi μ I

中文:
定理 infinitePi_map_restrict
  条件: {I : 有限集 ι}
  证明: isProjectiveLimit_infinitePi μ I

Depends on / 依赖: isProjectiveLimit_infinitePi
-/
theorem infinitePi_map_restrict {I : Finset ι} :
    (Measure.infinitePi μ).map I.restrict = Measure.pi fun i : I => μ i :=
  isProjectiveLimit_infinitePi μ I

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsProbabilityMeasure (infinitePi μ)
  body: by
  constructor
  rw [← cylinder_univ ∅]; rw [cylinder]; rw [← map_apply (measurable_restrict _) .univ]; rw [infinitePi_map_restrict]; rw [measure_univ]

中文:
实例 :
  签名: 是概率测度 (infinitePi μ)
  定义体: by
  constructor
  rw [← cylinder_univ ∅]; rw [cylinder]; rw [← map_apply (measurable_restrict _) .univ]; rw [infinitePi_map_restrict]; rw [measure_univ]

Depends on / 依赖: cylinder, cylinder_univ, infinitePi_map_restrict, map_apply, measurable_restrict, measure_univ
-/
instance : IsProbabilityMeasure (infinitePi μ) := by
  constructor
  rw [← cylinder_univ ∅]; rw [cylinder]; rw [← map_apply (measurable_restrict _) .univ]; rw [infinitePi_map_restrict]; rw [measure_univ]

/--
theorem `eq_infinitePi` / 定理 `eq_infinitePi`

English:
theorem eq_infinitePi
  statement: {ν : Measure (Π i, X i)}
  proof: by
.symm refine (isProjectiveLimit_infinitePi μ).unique ?_
  refine fun s => (pi_eq fun t ht => ?_).symm
  classical
  rw [Measure.map_apply]; rw [restrict_preimage_univ]; rw [hν]; rw [← prod_attach]; rw [univ_eq_attach]
  · congr with i
    rw [dif_pos i.2]
  any_goals fun_prop
  · rintro i
    split_ifs with hi
    · exact ht ⟨i, hi⟩
    · exact .univ
  · exact .univ_pi ht

中文:
定理 eq_infinitePi
  结论: {ν : 测度 (Π i, X i)}
  证明: by
.symm refine (isProjectiveLimit_infinitePi μ).unique ?_
  refine fun s => (pi_eq fun t ht => ?_).symm
  classical
  rw [Measure.map_apply]; rw [restrict_preimage_univ]; rw [hν]; rw [← prod_attach]; rw [univ_eq_attach]
  · congr with i
    rw [dif_pos i.2]
  any_goals fun_prop
  · rintro i
    split_ifs with hi
    · exact ht ⟨i, hi⟩
    · exact .univ
  · exact .univ_pi ht

Depends on / 依赖: Measure, Measure.map_apply, any_goals, classical, dif_pos, fun_prop, isProjectiveLimit_infinitePi, map_apply, pi_eq, prod_attach, restrict_preimage_univ, split_ifs, unique, univ_eq_attach, univ_pi
-/
theorem eq_infinitePi {ν : Measure (Π i, X i)}
    (hν : forall s : Finset ι, forall t : (i : ι) -> Set (X i),
      (forall i, MeasurableSet (t i)) -> ν (Set.pi s t) = ∏ i in s, μ i (t i)) :
    ν = infinitePi μ := by
.symm refine (isProjectiveLimit_infinitePi μ).unique ?_
  refine fun s => (pi_eq fun t ht => ?_).symm
  classical
  rw [Measure.map_apply]; rw [restrict_preimage_univ]; rw [hν]; rw [← prod_attach]; rw [univ_eq_attach]
  · congr with i
    rw [dif_pos i.2]
  any_goals fun_prop
  · rintro i
    split_ifs with hi
    · exact ht ⟨i, hi⟩
    · exact .univ
  · exact .univ_pi ht

/--
lemma `infinitePi_pi` / 引理 `infinitePi_pi`

English:
lemma infinitePi_pi
  statement: {s : Finset ι} {t : (i : ι) -> Set (X i)}
  proof: by
  have : Set.pi s t = cylinder s ((@Set.univ s).pi (fun i : s => t i)) := by
    ext x
    simp
  rw [this]; rw [cylinder]; rw [← map_apply]; rw [infinitePi_map_restrict]; rw [pi_pi]
  · rw [univ_eq_attach, prod_attach _ (fun i => (μ i) (t i))]
  · exact measurable_restrict _
  · exact .univ_pi fun i => mt i.1 i.2

中文:
引理 infinitePi_pi
  结论: {s : 有限集 ι} {t : (i : ι) -> 集合 (X i)}
  证明: by
  have : Set.pi s t = cylinder s ((@Set.univ s).pi (fun i : s => t i)) := by
    ext x
    simp
  rw [this]; rw [cylinder]; rw [← map_apply]; rw [infinitePi_map_restrict]; rw [pi_pi]
  · rw [univ_eq_attach, prod_attach _ (fun i => (μ i) (t i))]
  · exact measurable_restrict _
  · exact .univ_pi fun i => mt i.1 i.2

Depends on / 依赖: Set.pi, Set.univ, cylinder, infinitePi_map_restrict, map_apply, measurable_restrict, pi_pi, prod_attach, univ_eq_attach, univ_pi
-/
lemma infinitePi_pi {s : Finset ι} {t : (i : ι) -> Set (X i)}
    (mt : forall i in s, MeasurableSet (t i)) :
    infinitePi μ (Set.pi s t) = ∏ i in s, μ i (t i) := by
  have : Set.pi s t = cylinder s ((@Set.univ s).pi (fun i : s => t i)) := by
    ext x
    simp
  rw [this]; rw [cylinder]; rw [← map_apply]; rw [infinitePi_map_restrict]; rw [pi_pi]
  · rw [univ_eq_attach, prod_attach _ (fun i => (μ i) (t i))]
  · exact measurable_restrict _
  · exact .univ_pi fun i => mt i.1 i.2

/--
theorem `infinitePi_map_restrict'` / 定理 `infinitePi_map_restrict'`

English:
theorem infinitePi_map_restrict'
  given: {I : Set ι}
  proof: by
  apply eq_infinitePi
  intro s t ht
  classical
  rw [map_apply (by fun_prop)]; rw [domRestrict_preimage]; rw [infinitePi_pi _ (by measurability)]
  · simp
  · exact .pi s.countable_toSet (by measurability)

中文:
定理 infinitePi_map_restrict'
  条件: {I : 集合 ι}
  证明: by
  apply eq_infinitePi
  intro s t ht
  classical
  rw [map_apply (by fun_prop)]; rw [domRestrict_preimage]; rw [infinitePi_pi _ (by measurability)]
  · simp
  · exact .pi s.countable_toSet (by measurability)

Depends on / 依赖: classical, countable_toSet, domRestrict_preimage, eq_infinitePi, fun_prop, infinitePi_pi, map_apply, measurability, s.countable_toSet
-/
theorem infinitePi_map_restrict' {I : Set ι} :
    (infinitePi μ).map I.domRestrict = infinitePi fun i : I => μ i := by
  apply eq_infinitePi
  intro s t ht
  classical
  rw [map_apply (by fun_prop)]; rw [domRestrict_preimage]; rw [infinitePi_pi _ (by measurability)]
  · simp
  · exact .pi s.countable_toSet (by measurability)

/--
lemma `infinitePi_pi_of_countable` / 引理 `infinitePi_pi_of_countable`

English:
lemma infinitePi_pi_of_countable
  statement: {s : Set ι} (hs : Countable s) {t : (i : ι) -> Set (X i)}
  proof: by
  wlog s_ne : Nonempty s
  · simp [Set.not_nonempty_iff_eq_empty'.mp s_ne]
  apply tendsto_nhds_unique (f := fun s' : Finset s => ∏ i in s', μ i (t i)) (l := atTop)
  classical
  · conv in ∏ _ in _, _ =>
      rw [← infinitePi_pi _ (by measurability)]; rw [← infinitePi_map_restrict']; rw [map_apply
        (by fun_prop) (by apply MeasurableSet.pi (countable_toSet _) (by measurability))]; rw [domRestrict_preimage]
      simp only [coe_image, dite_eq_ite]
    have : s.pi t
      = ⋂ s' : Finset s,
        (Subtype.val '' (s' : Set s)).pi (fun i => if i in s then t i else Set.univ) := by
      rw [← Set.pi_iUnion_eq_iInter_pi]; rw [Set.iUnion_finset_eq_set]
      grind
    rw [this]
    apply tendsto_measure_iInter_atTop
    · refine fun s' => MeasurableSet.nullMeasurableSet (MeasurableSet.pi ?_ (by measurability))
      exact (Finset.countable_toSet _).image _
    · intro _ _ h
      simpa using Set.pi_mono' (by simp) (Set.image_mono h)
    · exact ⟨{Nonempty.some s_ne}, by simp⟩
  · rw [ENNReal.tprod_eq_iInf_prod (by simp [prob_le_one])]
    exact tendsto_atTop_iInf (prod_anti_set_of_le_one' (by simp [prob_le_one]))

中文:
引理 infinitePi_pi_of_countable
  结论: {s : 集合 ι} (hs : 可数 s) {t : (i : ι) -> 集合 (X i)}
  证明: by
  wlog s_ne : Nonempty s
  · simp [Set.not_nonempty_iff_eq_empty'.mp s_ne]
  apply tendsto_nhds_unique (f := fun s' : Finset s => ∏ i in s', μ i (t i)) (l := atTop)
  classical
  · conv in ∏ _ in _, _ =>
      rw [← infinitePi_pi _ (by measurability)]; rw [← infinitePi_map_restrict']; rw [map_apply
        (by fun_prop) (by apply MeasurableSet.pi (countable_toSet _) (by measurability))]; rw [domRestrict_preimage]
      simp only [coe_image, dite_eq_ite]
    have : s.pi t
      = ⋂ s' : Finset s,
        (Subtype.val '' (s' : Set s)).pi (fun i => if i in s then t i else Set.univ) := by
      rw [← Set.pi_iUnion_eq_iInter_pi]; rw [Set.iUnion_finset_eq_set]
      grind
    rw [this]
    apply tendsto_measure_iInter_atTop
    · refine fun s' => MeasurableSet.nullMeasurableSet (MeasurableSet.pi ?_ (by measurability))
      exact (Finset.countable_toSet _).image _
    · intro _ _ h
      simpa using Set.pi_mono' (by simp) (Set.image_mono h)
    · exact ⟨{Nonempty.some s_ne}, by simp⟩
  · rw [ENNReal.tprod_eq_iInf_prod (by simp [prob_le_one])]
    exact tendsto_atTop_iInf (prod_anti_set_of_le_one' (by simp [prob_le_one]))

Depends on / 依赖: Finset, MeasurableSet, MeasurableSet.pi, Nonempty, Set.not_nonempty_iff_eq_empty, Subtype, Subtype.val, classical, coe_image, countable_toSet, dite_eq_ite, domRestrict_preimage, fun_prop, infinitePi_map_restrict, infinitePi_pi, map_apply, measurability, not_nonempty_iff_eq_empty, s.pi, s_ne
-/
lemma infinitePi_pi_of_countable {s : Set ι} (hs : Countable s) {t : (i : ι) -> Set (X i)}
    (mt : forall i in s, MeasurableSet (t i)) :
    infinitePi μ (Set.pi s t) = ∏' i : s, μ i (t i) := by
  wlog s_ne : Nonempty s
  · simp [Set.not_nonempty_iff_eq_empty'.mp s_ne]
  apply tendsto_nhds_unique (f := fun s' : Finset s => ∏ i in s', μ i (t i)) (l := atTop)
  classical
  · conv in ∏ _ in _, _ =>
      rw [← infinitePi_pi _ (by measurability)]; rw [← infinitePi_map_restrict']; rw [map_apply
        (by fun_prop) (by apply MeasurableSet.pi (countable_toSet _) (by measurability))]; rw [domRestrict_preimage]
      simp only [coe_image, dite_eq_ite]
    have : s.pi t
      = ⋂ s' : Finset s,
        (Subtype.val '' (s' : Set s)).pi (fun i => if i in s then t i else Set.univ) := by
      rw [← Set.pi_iUnion_eq_iInter_pi]; rw [Set.iUnion_finset_eq_set]
      grind
    rw [this]
    apply tendsto_measure_iInter_atTop
    · refine fun s' => MeasurableSet.nullMeasurableSet (MeasurableSet.pi ?_ (by measurability))
      exact (Finset.countable_toSet _).image _
    · intro _ _ h
      simpa using Set.pi_mono' (by simp) (Set.image_mono h)
    · exact ⟨{Nonempty.some s_ne}, by simp⟩
  · rw [ENNReal.tprod_eq_iInf_prod (by simp [prob_le_one])]
    exact tendsto_atTop_iInf (prod_anti_set_of_le_one' (by simp [prob_le_one]))

/--
lemma `infinitePi_pi_univ` / 引理 `infinitePi_pi_univ`

English:
lemma infinitePi_pi_univ
  statement: [Countable ι] {t : (i : ι) -> Set (X i)}
  proof: by
  rw [infinitePi_pi_of_countable]; rw [tprod_univ (f := fun i => μ i (t i))]
  · simpa [Set.countable_univ_iff]
  · measurability

@[simp]

中文:
引理 infinitePi_pi_univ
  结论: [可数 ι] {t : (i : ι) -> 集合 (X i)}
  证明: by
  rw [infinitePi_pi_of_countable]; rw [tprod_univ (f := fun i => μ i (t i))]
  · simpa [Set.countable_univ_iff]
  · measurability

@[simp]

Depends on / 依赖: Set.countable_univ_iff, countable_univ_iff, infinitePi_pi_of_countable, measurability, tprod_univ
-/
lemma infinitePi_pi_univ [Countable ι] {t : (i : ι) -> Set (X i)}
    (mt : forall i : ι, MeasurableSet (t i)) :
    infinitePi μ (Set.univ.pi t) = ∏' i, μ i (t i) := by
  rw [infinitePi_pi_of_countable]; rw [tprod_univ (f := fun i => μ i (t i))]
  · simpa [Set.countable_univ_iff]
  · measurability

@[simp]
/--
lemma `infinitePi_singleton` / 引理 `infinitePi_singleton`

English:
lemma infinitePi_singleton
  statement: [Countable ι] [forall i, MeasurableSingletonClass (X i)]
  proof: by
  rw [← Set.univ_pi_singleton]; rw [infinitePi_pi_univ _ (by measurability)]

中文:
引理 infinitePi_singleton
  结论: [可数 ι] [对任意 i, MeasurableSingleton类 (X i)]
  证明: by
  rw [← Set.univ_pi_singleton]; rw [infinitePi_pi_univ _ (by measurability)]

Depends on / 依赖: Set.univ_pi_singleton, infinitePi_pi_univ, measurability, univ_pi_singleton
-/
lemma infinitePi_singleton [Countable ι] [forall i, MeasurableSingletonClass (X i)]
    (f : forall i, X i) : infinitePi μ {f} = ∏' i, μ i {f i} := by
  rw [← Set.univ_pi_singleton]; rw [infinitePi_pi_univ _ (by measurability)]

/--
lemma `infinitePi_singleton_of_fintype` / 引理 `infinitePi_singleton_of_fintype`

English:
lemma infinitePi_singleton_of_fintype
  statement: [Fintype ι] [forall i, MeasurableSingletonClass (X i)]
  proof: by simp

中文:
引理 infinitePi_singleton_of_fintype
  结论: [有限类型 ι] [对任意 i, MeasurableSingleton类 (X i)]
  证明: by simp
-/
lemma infinitePi_singleton_of_fintype [Fintype ι] [forall i, MeasurableSingletonClass (X i)]
    (f : forall i, X i) : infinitePi μ {f} = ∏ i, μ i {f i} := by simp

/--
lemma `infinitePi_dirac` / 引理 `infinitePi_dirac`

English:
lemma infinitePi_dirac
  given: (f : forall i, X i)
  statement: infinitePi (fun i => dirac (f i)) = dirac f
  proof: .symm eq_infinitePi _ by simp +contextual [MeasurableSet.pi, Finset.countable_toSet]

中文:
引理 infinitePi_dirac
  条件: (f : 对任意 i, X i)
  结论: infinitePi (fun i => dirac (f i)) = dirac f
  证明: .symm eq_infinitePi _ by simp +contextual [MeasurableSet.pi, Finset.countable_toSet]
-/
@[simp] lemma infinitePi_dirac (f : forall i, X i) : infinitePi (fun i => dirac (f i)) = dirac f :=
.symm eq_infinitePi _ by simp +contextual [MeasurableSet.pi, Finset.countable_toSet]

/--
lemma `_root_.measurePreserving_eval_infinitePi` / 引理 `_root_.measurePreserving_eval_infinitePi`

English:
lemma _root_.measurePreserving_eval_infinitePi
  given: (i : ι)
  proof: by fun_prop
  map_eq := by
    ext s hs
    have : @Function.eval ι X i =
        (@Function.eval ({i} : Finset ι) (fun j => X j) ⟨i, by simp⟩) ∘
        (Finset.restrict {i}) := by ext; simp
    rw [this]; rw [← map_map]; rw [infinitePi_map_restrict]; rw [(measurePreserving_eval _ _).map_eq]
    all_goals fun_prop

中文:
引理 _root_.measurePreserving_eval_infinitePi
  条件: (i : ι)
  证明: by fun_prop
  map_eq := by
    ext s hs
    have : @Function.eval ι X i =
        (@Function.eval ({i} : Finset ι) (fun j => X j) ⟨i, by simp⟩) ∘
        (Finset.restrict {i}) := by ext; simp
    rw [this]; rw [← map_map]; rw [infinitePi_map_restrict]; rw [(measurePreserving_eval _ _).map_eq]
    all_goals fun_prop

Depends on / 依赖: Finset, Finset.restrict, Function, Function.eval, all_goals, fun_prop, infinitePi_map_restrict, map_eq, map_map, measurePreserving_eval, restrict
-/
lemma _root_.measurePreserving_eval_infinitePi (i : ι) :
    MeasurePreserving (Function.eval i) (infinitePi μ) (μ i) where
  measurable := by fun_prop
  map_eq := by
    ext s hs
    have : @Function.eval ι X i =
        (@Function.eval ({i} : Finset ι) (fun j => X j) ⟨i, by simp⟩) ∘
        (Finset.restrict {i}) := by ext; simp
    rw [this]; rw [← map_map]; rw [infinitePi_map_restrict]; rw [(measurePreserving_eval _ _).map_eq]
    all_goals fun_prop

/--
lemma `infinitePi_map_eval` / 引理 `infinitePi_map_eval`

English:
lemma infinitePi_map_eval
  given: (i : ι)
  proof: (measurePreserving_eval_infinitePi μ i).map_eq

中文:
引理 infinitePi_map_eval
  条件: (i : ι)
  证明: (measurePreserving_eval_infinitePi μ i).map_eq

Depends on / 依赖: map_eq, measurePreserving_eval_infinitePi
-/
lemma infinitePi_map_eval (i : ι) :
    (infinitePi μ).map (fun x => x i) = μ i :=
  (measurePreserving_eval_infinitePi μ i).map_eq

/--
lemma `infinitePi_map_pi` / 引理 `infinitePi_map_pi`

English:
lemma infinitePi_map_pi
  statement: {Y : ι -> Type*} [forall i, MeasurableSpace (Y i)] {f : (i : ι) -> X i -> Y i}
  proof: by
  have (i : ι) : IsProbabilityMeasure ((μ i).map (f i)) :=
    isProbabilityMeasure_map (hf i).aemeasurable
  refine eq_infinitePi _ fun s t ht => ?_
  rw [map_apply (by fun_prop) (.pi s.countable_toSet fun _ _ => ht _)]
  have : (fun (x : Π i, X i) i => f i (x i)) ⁻¹' ((s : Set ι).pi t) =
      (s : Set ι).pi (fun i => (f i) ⁻¹' (t i)) := by ext x; simp
  rw [this]; rw [infinitePi_pi _ (fun i _ => hf i (ht i))]
  congr! with i hi
  rw [map_apply (by fun_prop) (ht i)]

中文:
引理 infinitePi_map_pi
  结论: {Y : ι -> 类型} [对任意 i, 可测空间 (Y i)] {f : (i : ι) -> X i -> Y i}
  证明: by
  have (i : ι) : IsProbabilityMeasure ((μ i).map (f i)) :=
    isProbabilityMeasure_map (hf i).aemeasurable
  refine eq_infinitePi _ fun s t ht => ?_
  rw [map_apply (by fun_prop) (.pi s.countable_toSet fun _ _ => ht _)]
  have : (fun (x : Π i, X i) i => f i (x i)) ⁻¹' ((s : Set ι).pi t) =
      (s : Set ι).pi (fun i => (f i) ⁻¹' (t i)) := by ext x; simp
  rw [this]; rw [infinitePi_pi _ (fun i _ => hf i (ht i))]
  congr! with i hi
  rw [map_apply (by fun_prop) (ht i)]

Depends on / 依赖: IsProbabilityMeasure, aemeasurable, countable_toSet, eq_infinitePi, fun_prop, infinitePi_pi, isProbabilityMeasure_map, map_apply, s.countable_toSet
-/
lemma infinitePi_map_pi {Y : ι -> Type*} [forall i, MeasurableSpace (Y i)] {f : (i : ι) -> X i -> Y i}
    (hf : forall i, Measurable (f i)) :
    (infinitePi μ).map (fun x i => f i (x i)) = infinitePi (fun i => (μ i).map (f i)) := by
  have (i : ι) : IsProbabilityMeasure ((μ i).map (f i)) :=
    isProbabilityMeasure_map (hf i).aemeasurable
  refine eq_infinitePi _ fun s t ht => ?_
  rw [map_apply (by fun_prop) (.pi s.countable_toSet fun _ _ => ht _)]
  have : (fun (x : Π i, X i) i => f i (x i)) ⁻¹' ((s : Set ι).pi t) =
      (s : Set ι).pi (fun i => (f i) ⁻¹' (t i)) := by ext x; simp
  rw [this]; rw [infinitePi_pi _ (fun i _ => hf i (ht i))]
  congr! with i hi
  rw [map_apply (by fun_prop) (ht i)]

/--
theorem `infinitePi_map_piCongrLeft` / 定理 `infinitePi_map_piCongrLeft`

English:
theorem infinitePi_map_piCongrLeft
  given: {α : Type*} (e : α ≃ ι)
  proof: by
  refine eq_infinitePi μ fun s t ht => ?_
  conv_lhs => enter [2, 1]; rw [← e.image_preimage s, ← coe_preimage _ e.injective.injOn]
  rw [map_apply]; rw [coe_piCongrLeft]; rw [Equiv.piCongrLeft_preimage_pi]; rw [infinitePi_pi]; rw [prod_equiv e]
  · simp
  · simp
  · simp_all
  · fun_prop
  · exact .pi ((countable_toSet _).image e) (by simp_all)

中文:
定理 infinitePi_map_piCongrLeft
  条件: {α : 类型} (e : α ≃ ι)
  证明: by
  refine eq_infinitePi μ fun s t ht => ?_
  conv_lhs => enter [2, 1]; rw [← e.image_preimage s, ← coe_preimage _ e.injective.injOn]
  rw [map_apply]; rw [coe_piCongrLeft]; rw [Equiv.piCongrLeft_preimage_pi]; rw [infinitePi_pi]; rw [prod_equiv e]
  · simp
  · simp
  · simp_all
  · fun_prop
  · exact .pi ((countable_toSet _).image e) (by simp_all)

Depends on / 依赖: Equiv.piCongrLeft_preimage_pi, coe_piCongrLeft, coe_preimage, conv_lhs, countable_toSet, e.image_preimage, e.injective.injOn, eq_infinitePi, fun_prop, image_preimage, infinitePi_pi, injective, map_apply, piCongrLeft_preimage_pi, prod_equiv
-/
theorem infinitePi_map_piCongrLeft {α : Type*} (e : α ≃ ι) :
    (infinitePi (fun i => μ (e i))).map (piCongrLeft X e) = infinitePi μ := by
  refine eq_infinitePi μ fun s t ht => ?_
  conv_lhs => enter [2, 1]; rw [← e.image_preimage s, ← coe_preimage _ e.injective.injOn]
  rw [map_apply]; rw [coe_piCongrLeft]; rw [Equiv.piCongrLeft_preimage_pi]; rw [infinitePi_pi]; rw [prod_equiv e]
  · simp
  · simp
  · simp_all
  · fun_prop
  · exact .pi ((countable_toSet _).image e) (by simp_all)

/--
theorem `infinitePi_eq_pi` / 定理 `infinitePi_eq_pi`

English:
theorem infinitePi_eq_pi
  given: [Fintype ι]
  statement: infinitePi μ = Measure.pi μ
  proof: by
  refine (pi_eq fun s hs => ?_).symm
  rw [← coe_univ]; rw [infinitePi_pi]
  simpa

中文:
定理 infinitePi_eq_pi
  条件: [有限类型 ι]
  结论: infinitePi μ = 测度.pi μ
  证明: by
  refine (pi_eq fun s hs => ?_).symm
  rw [← coe_univ]; rw [infinitePi_pi]
  simpa

Depends on / 依赖: coe_univ, infinitePi_pi, pi_eq
-/
theorem infinitePi_eq_pi [Fintype ι] : infinitePi μ = Measure.pi μ := by
  refine (pi_eq fun s hs => ?_).symm
  rw [← coe_univ]; rw [infinitePi_pi]
  simpa

/--
lemma `infinitePi_cylinder` / 引理 `infinitePi_cylinder`

English:
lemma infinitePi_cylinder
  given: {s : Finset ι} {S : Set (Π i : s, X i)} (mS : MeasurableSet S)
  proof: by
  rw [cylinder]; rw [← Measure.map_apply (measurable_restrict _) mS]; rw [infinitePi_map_restrict]

中文:
引理 infinitePi_cylinder
  条件: {s : 有限集 ι} {S : 集合 (Π i : s, X i)} (mS : 可测集 S)
  证明: by
  rw [cylinder]; rw [← Measure.map_apply (measurable_restrict _) mS]; rw [infinitePi_map_restrict]

Depends on / 依赖: Measure, Measure.map_apply, cylinder, infinitePi_map_restrict, map_apply, measurable_restrict
-/
lemma infinitePi_cylinder {s : Finset ι} {S : Set (Π i : s, X i)} (mS : MeasurableSet S) :
    infinitePi μ (cylinder s S) = Measure.pi (fun i : s => μ i) S := by
  rw [cylinder]; rw [← Measure.map_apply (measurable_restrict _) mS]; rw [infinitePi_map_restrict]

section curry

variable {ι : Type*} {κ : ι -> Type*} {X : (i : ι) -> κ i -> Type*}
  {mX : forall i, forall j, MeasurableSpace (X i j)} (μ : (i : ι) -> (j : κ i) -> Measure (X i j))
  [hμ : forall i j, IsProbabilityMeasure (μ i j)]

/--
lemma `infinitePi_map_piCurry_symm` / 引理 `infinitePi_map_piCurry_symm`

English:
lemma infinitePi_map_piCurry_symm
  proof: by
  apply eq_infinitePi
  intro s t ht
  classical
  rw [map_apply (by fun_prop) (.pi (countable_toSet _) fun _ _ => ht _)]; rw [← Finset.sigma_image_fst_preimage_mk s]; rw [coe_piCurry_symm]; rw [Finset.coe_sigma]; rw [Set.uncurry_preimage_sigma_pi]; rw [infinitePi_pi]; rw [Finset.prod_sigma]
  · exact Finset.prod_congr rfl (fun _ _ => infinitePi_pi _ fun _ _ => ht _)
  · simp only [mem_image, Sigma.exists, exists_and_right, exists_eq_right, forall_exists_index]
    exact fun i j hij => MeasurableSet.pi (countable_toSet _) fun k hk => by simp_all

中文:
引理 infinitePi_map_piCurry_symm
  证明: by
  apply eq_infinitePi
  intro s t ht
  classical
  rw [map_apply (by fun_prop) (.pi (countable_toSet _) fun _ _ => ht _)]; rw [← Finset.sigma_image_fst_preimage_mk s]; rw [coe_piCurry_symm]; rw [Finset.coe_sigma]; rw [Set.uncurry_preimage_sigma_pi]; rw [infinitePi_pi]; rw [Finset.prod_sigma]
  · exact Finset.prod_congr rfl (fun _ _ => infinitePi_pi _ fun _ _ => ht _)
  · simp only [mem_image, Sigma.exists, exists_and_right, exists_eq_right, forall_exists_index]
    exact fun i j hij => MeasurableSet.pi (countable_toSet _) fun k hk => by simp_all

Depends on / 依赖: Finset, Finset.coe_sigma, Finset.prod_congr, Finset.prod_sigma, Finset.sigma_image_fst_preimage_mk, MeasurableSet, MeasurableSet.pi, Set.uncurry_preimage_sigma_pi, Sigma.exists, classical, coe_piCurry_symm, coe_sigma, countable_toSet, eq_infinitePi, exists_and_right, exists_eq_right, forall_exists_index, fun_prop, infinitePi_pi, map_apply
-/
lemma infinitePi_map_piCurry_symm :
    (infinitePi fun i : ι => infinitePi fun j : κ i => μ i j).map (piCurry X).symm =
      infinitePi fun p : (i : ι) × κ i => μ p.1 p.2 := by
  apply eq_infinitePi
  intro s t ht
  classical
  rw [map_apply (by fun_prop) (.pi (countable_toSet _) fun _ _ => ht _)]; rw [← Finset.sigma_image_fst_preimage_mk s]; rw [coe_piCurry_symm]; rw [Finset.coe_sigma]; rw [Set.uncurry_preimage_sigma_pi]; rw [infinitePi_pi]; rw [Finset.prod_sigma]
  · exact Finset.prod_congr rfl (fun _ _ => infinitePi_pi _ fun _ _ => ht _)
  · simp only [mem_image, Sigma.exists, exists_and_right, exists_eq_right, forall_exists_index]
    exact fun i j hij => MeasurableSet.pi (countable_toSet _) fun k hk => by simp_all

/--
lemma `infinitePi_map_piCurry` / 引理 `infinitePi_map_piCurry`

English:
lemma infinitePi_map_piCurry
  proof: by
  rw [MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq]; rw [infinitePi_map_piCurry_symm]

中文:
引理 infinitePi_map_piCurry
  证明: by
  rw [MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq]; rw [infinitePi_map_piCurry_symm]

Depends on / 依赖: MeasurableEquiv, MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq, infinitePi_map_piCurry_symm, map_apply_eq_iff_map_symm_apply_eq
-/
lemma infinitePi_map_piCurry :
    (infinitePi fun p : (i : ι) × κ i => μ p.1 p.2).map (piCurry X) =
      infinitePi fun i : ι => infinitePi fun j : κ i => μ i j := by
  rw [MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq]; rw [infinitePi_map_piCurry_symm]

variable {ι κ X : Type*} {mX : MeasurableSpace X} (μ : ι -> κ -> Measure X)
  [hμ : forall i j, IsProbabilityMeasure (μ i j)]

/--
lemma `infinitePi_map_curry_symm` / 引理 `infinitePi_map_curry_symm`

English:
lemma infinitePi_map_curry_symm
  proof: by
  rw [← (MeasurableEquiv.piCongrLeft (fun _ => X)
    (Equiv.sigmaEquivProd ι κ).symm).map_measurableEquiv_injective.eq_iff]; rw [map_map]
  · have : (MeasurableEquiv.piCongrLeft (fun _ => X) (Equiv.sigmaEquivProd ι κ).symm) ∘
        (MeasurableEquiv.curry ι κ X).symm = ⇑(MeasurableEquiv.piCurry (fun _ _ => X)).symm := by
      ext; simp [piCongrLeft, Equiv.piCongrLeft, Sigma.uncurry]
    rw [this]; rw [infinitePi_map_piCurry_symm]
.symm convert! infinitePi_map_piCongrLeft (fun p => μ p.1 p.2) (Equiv.sigmaEquivProd ι κ).symm
  all_goals fun_prop

中文:
引理 infinitePi_map_curry_symm
  证明: by
  rw [← (MeasurableEquiv.piCongrLeft (fun _ => X)
    (Equiv.sigmaEquivProd ι κ).symm).map_measurableEquiv_injective.eq_iff]; rw [map_map]
  · have : (MeasurableEquiv.piCongrLeft (fun _ => X) (Equiv.sigmaEquivProd ι κ).symm) ∘
        (MeasurableEquiv.curry ι κ X).symm = ⇑(MeasurableEquiv.piCurry (fun _ _ => X)).symm := by
      ext; simp [piCongrLeft, Equiv.piCongrLeft, Sigma.uncurry]
    rw [this]; rw [infinitePi_map_piCurry_symm]
.symm convert! infinitePi_map_piCongrLeft (fun p => μ p.1 p.2) (Equiv.sigmaEquivProd ι κ).symm
  all_goals fun_prop

Depends on / 依赖: Equiv.piCongrLeft, Equiv.sigmaEquivProd, MeasurableEquiv, MeasurableEquiv.curry, MeasurableEquiv.piCongrLeft, MeasurableEquiv.piCurry, Sigma.uncurry, convert, eq_iff, infinitePi_map_piCongrLeft, infinitePi_map_piCurry_symm, map_map, map_measurableEquiv_injective, map_measurableEquiv_injective.eq_iff, piCongrLeft, piCurry, sigmaEquivProd, uncurry
-/
lemma infinitePi_map_curry_symm :
    (infinitePi fun i : ι => infinitePi fun j : κ => μ i j).map (curry ι κ X).symm =
      infinitePi fun p : ι × κ => μ p.1 p.2 := by
  rw [← (MeasurableEquiv.piCongrLeft (fun _ => X)
    (Equiv.sigmaEquivProd ι κ).symm).map_measurableEquiv_injective.eq_iff]; rw [map_map]
  · have : (MeasurableEquiv.piCongrLeft (fun _ => X) (Equiv.sigmaEquivProd ι κ).symm) ∘
        (MeasurableEquiv.curry ι κ X).symm = ⇑(MeasurableEquiv.piCurry (fun _ _ => X)).symm := by
      ext; simp [piCongrLeft, Equiv.piCongrLeft, Sigma.uncurry]
    rw [this]; rw [infinitePi_map_piCurry_symm]
.symm convert! infinitePi_map_piCongrLeft (fun p => μ p.1 p.2) (Equiv.sigmaEquivProd ι κ).symm
  all_goals fun_prop

/--
lemma `infinitePi_map_curry` / 引理 `infinitePi_map_curry`

English:
lemma infinitePi_map_curry
  proof: by
  rw [MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq]; rw [infinitePi_map_curry_symm]

中文:
引理 infinitePi_map_curry
  证明: by
  rw [MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq]; rw [infinitePi_map_curry_symm]

Depends on / 依赖: MeasurableEquiv, MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq, infinitePi_map_curry_symm, map_apply_eq_iff_map_symm_apply_eq
-/
lemma infinitePi_map_curry :
    (infinitePi fun p : ι × κ => μ p.1 p.2).map (curry ι κ X) =
      infinitePi fun i : ι => infinitePi fun j : κ => μ i j := by
  rw [MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq]; rw [infinitePi_map_curry_symm]

end curry

end Measure

section Integral

/--
theorem `integral_restrict_infinitePi` / 定理 `integral_restrict_infinitePi`

English:
theorem integral_restrict_infinitePi
  statement: {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  proof: by
  rw [← integral_map]; rw [infinitePi_map_restrict]
  · fun_prop
  · rwa [infinitePi_map_restrict]

中文:
定理 integral_restrict_infinitePi
  结论: {E : 类型} [赋范交换加群 E] [赋范空间 实数 E]
  证明: by
  rw [← integral_map]; rw [infinitePi_map_restrict]
  · fun_prop
  · rwa [infinitePi_map_restrict]

Depends on / 依赖: fun_prop, infinitePi_map_restrict, integral_map
-/
theorem integral_restrict_infinitePi {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {s : Finset ι} {f : (Π i : s, X i) -> E}
    (hf : AEStronglyMeasurable f (Measure.pi (fun i : s => μ i))) :
    ∫ y, f (s.restrict y) ∂infinitePi μ = ∫ y, f y ∂Measure.pi (fun i : s => μ i) := by
  rw [← integral_map]; rw [infinitePi_map_restrict]
  · fun_prop
  · rwa [infinitePi_map_restrict]

/--
theorem `lintegral_restrict_infinitePi` / 定理 `lintegral_restrict_infinitePi`

English:
theorem lintegral_restrict_infinitePi
  statement: {s : Finset ι}
  proof: by
  rw [← lintegral_map hf (measurable_restrict _)]; rw [isProjectiveLimit_infinitePi μ]

中文:
定理 lintegral_restrict_infinitePi
  结论: {s : 有限集 ι}
  证明: by
  rw [← lintegral_map hf (measurable_restrict _)]; rw [isProjectiveLimit_infinitePi μ]

Depends on / 依赖: isProjectiveLimit_infinitePi, lintegral_map, measurable_restrict
-/
theorem lintegral_restrict_infinitePi {s : Finset ι}
    {f : (Π i : s, X i) -> Real>=0∞} (hf : Measurable f) :
    ∫⁻ y, f (s.restrict y) ∂infinitePi μ = ∫⁻ y, f y ∂Measure.pi (fun i : s => μ i) := by
  rw [← lintegral_map hf (measurable_restrict _)]; rw [isProjectiveLimit_infinitePi μ]

open Filtration

/--
theorem `integral_infinitePi_of_piFinset` / 定理 `integral_infinitePi_of_piFinset`

English:
theorem integral_infinitePi_of_piFinset
  statement: [DecidableEq ι] {E : Type*} [NormedAddCommGroup E]
  proof: by
  let g : (Π i : s, X i) -> E := fun y => f (Function.updateFinset x _ y)
  have this y : g (s.restrict y) = f y :=
    mf.dependsOn_of_piFinset fun i hi => by simp_all [Function.updateFinset]
  rw [← integral_congr_ae <| ae_of_all _ this]; rw [integral_restrict_infinitePi]
  exact mf.comp_measurable (measurable_updateFinset.mono le_rfl (piFinset.le s))
.aestronglyMeasurable

中文:
定理 integral_infinitePi_of_piFinset
  结论: [DecidableEq ι] {E : 类型} [赋范交换加群 E]
  证明: by
  let g : (Π i : s, X i) -> E := fun y => f (Function.updateFinset x _ y)
  have this y : g (s.restrict y) = f y :=
    mf.dependsOn_of_piFinset fun i hi => by simp_all [Function.updateFinset]
  rw [← integral_congr_ae <| ae_of_all _ this]; rw [integral_restrict_infinitePi]
  exact mf.comp_measurable (measurable_updateFinset.mono le_rfl (piFinset.le s))
.aestronglyMeasurable

Depends on / 依赖: Function, Function.updateFinset, ae_of_all, aestronglyMeasurable, comp_measurable, dependsOn_of_piFinset, integral_congr_ae, integral_restrict_infinitePi, le_rfl, measurable_updateFinset, measurable_updateFinset.mono, mf.comp_measurable, mf.dependsOn_of_piFinset, piFinset, piFinset.le, restrict, s.restrict, updateFinset
-/
theorem integral_infinitePi_of_piFinset [DecidableEq ι] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace Real E] {s : Finset ι} {f : (Π i, X i) -> E}
    (mf : StronglyMeasurable[piFinset s] f) (x : Π i, X i) :
    ∫ y, f y ∂infinitePi μ =
    ∫ y, f (Function.updateFinset x s y) ∂Measure.pi (fun i : s => μ i) := by
  let g : (Π i : s, X i) -> E := fun y => f (Function.updateFinset x _ y)
  have this y : g (s.restrict y) = f y :=
    mf.dependsOn_of_piFinset fun i hi => by simp_all [Function.updateFinset]
  rw [← integral_congr_ae <| ae_of_all _ this]; rw [integral_restrict_infinitePi]
  exact mf.comp_measurable (measurable_updateFinset.mono le_rfl (piFinset.le s))
.aestronglyMeasurable

/--
theorem `lintegral_infinitePi_of_piFinset` / 定理 `lintegral_infinitePi_of_piFinset`

English:
theorem lintegral_infinitePi_of_piFinset
  statement: [DecidableEq ι] {s : Finset ι}
  proof: by
  let g : (Π i : s, X i) -> Real>=0∞ := fun y => f (Function.updateFinset x _ y)
  have this y : g (s.restrict y) = f y :=
    mf.dependsOn_of_piFinset fun i hi => by simp_all [Function.updateFinset]
  rw [← lintegral_congr_ae <| ae_of_all _ this]; rw [lintegral_restrict_infinitePi]
  · rfl
  · exact mf.comp (measurable_updateFinset.mono le_rfl (piFinset.le s))

中文:
定理 lintegral_infinitePi_of_piFinset
  结论: [DecidableEq ι] {s : 有限集 ι}
  证明: by
  let g : (Π i : s, X i) -> Real>=0∞ := fun y => f (Function.updateFinset x _ y)
  have this y : g (s.restrict y) = f y :=
    mf.dependsOn_of_piFinset fun i hi => by simp_all [Function.updateFinset]
  rw [← lintegral_congr_ae <| ae_of_all _ this]; rw [lintegral_restrict_infinitePi]
  · rfl
  · exact mf.comp (measurable_updateFinset.mono le_rfl (piFinset.le s))

Depends on / 依赖: Function, Function.updateFinset, ae_of_all, dependsOn_of_piFinset, le_rfl, lintegral_congr_ae, lintegral_restrict_infinitePi, measurable_updateFinset, measurable_updateFinset.mono, mf.comp, mf.dependsOn_of_piFinset, piFinset, piFinset.le, restrict, s.restrict, updateFinset
-/
theorem lintegral_infinitePi_of_piFinset [DecidableEq ι] {s : Finset ι}
    {f : (Π i, X i) -> Real>=0∞} (mf : Measurable[piFinset s] f)
    (x : Π i, X i) : ∫⁻ y, f y ∂infinitePi μ = (∫⋯∫⁻_s, f ∂μ) x := by
  let g : (Π i : s, X i) -> Real>=0∞ := fun y => f (Function.updateFinset x _ y)
  have this y : g (s.restrict y) = f y :=
    mf.dependsOn_of_piFinset fun i hi => by simp_all [Function.updateFinset]
  rw [← lintegral_congr_ae <| ae_of_all _ this]; rw [lintegral_restrict_infinitePi]
  · rfl
  · exact mf.comp (measurable_updateFinset.mono le_rfl (piFinset.le s))

end Integral

end InfinitePi

end MeasureTheory
