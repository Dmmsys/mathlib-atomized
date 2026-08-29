/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.Prod
public import Mathlib.Probability.Kernel.Basic

/-!
# Measurability of the integral against a kernel

The Lebesgue integral of a measurable function against a kernel is measurable.

## Main statements

* `Measurable.lintegral_kernel_prod_right`: the function `a ↦ ∫⁻ b, f a b ∂(κ a)` is measurable,
  for an s-finite kernel `κ : Kernel α β` and a function `f : α → β → ℝ≥0∞` such that `uncurry f`
  is measurable.

-/

public section


open MeasureTheory ProbabilityTheory Function Set Filter

open scoped MeasureTheory ENNReal Topology

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {κ : Kernel α β} {η : Kernel (α × β) γ} {a : α}

namespace ProbabilityTheory

namespace Kernel

/--
theorem `measurable_kernel_prodMk_left_of_finite` / 定理 `measurable_kernel_prodMk_left_of_finite`

English:
theorem measurable_kernel_prodMk_left_of_finite
  statement: {t : Set (α × β)} (ht : MeasurableSet t)
  proof: by
  -- `t` is a measurable set in the product `α × β`: we use that the product σ-algebra is generated
  -- by boxes to prove the result by induction.
  induction t, ht
    using MeasurableSpace.induction_on_inter generateFrom_prod.symm isPiSystem_prod with
  | empty => simp only [preimage_empty, me

中文:
定理 measurable_kernel_prodMk_left_of_finite
  结论: {t : 集合 (α × β)} (ht : 可测集 t)
  证明: by
  -- `t` is a measurable set in the product `α × β`: we use that the product σ-algebra is generated
  -- by boxes to prove the result by induction.
  induction t, ht
    using MeasurableSpace.induction_on_inter generateFrom_prod.symm isPiSystem_prod with
  | empty => simp only [preimage_empty, me
-/
theorem measurable_kernel_prodMk_left_of_finite {t : Set (α × β)} (ht : MeasurableSet t)
    (hκs : forall a, IsFiniteMeasure (κ a)) : Measurable fun a => κ a (Prod.mk a ⁻¹' t) := by
  -- `t` is a measurable set in the product `α × β`: we use that the product σ-algebra is generated
  -- by boxes to prove the result by induction.
  induction t, ht
    using MeasurableSpace.induction_on_inter generateFrom_prod.symm isPiSystem_prod with
  | empty => simp only [preimage_empty, measure_empty, measurable_const]
  | basic t ht =>
    simp only [Set.mem_image2, Set.mem_ofPred_eq] at ht
    obtain ⟨t₁, ht₁, t₂, ht₂, rfl⟩ := ht
    classical
    simp_rw [mk_preimage_prod_right_eq_if]
    have h_eq_ite : (fun a => κ a (ite (a in t₁) t₂ ∅)) = fun a => ite (a in t₁) (κ a t₂) 0 := by
      ext1 a
      split_ifs
      exacts [rfl, measure_empty]
    rw [h_eq_ite]
    exact Measurable.ite ht₁ (Kernel.measurable_coe κ ht₂) measurable_const
  | compl t htm iht =>
    have h_eq_sdiff : forall a, Prod.mk a ⁻¹' tᶜ = Set.univ \ Prod.mk a ⁻¹' t := by
      intro a
      ext1 b
      simp only [mem_compl_iff, mem_preimage, Set.mem_sdiff, mem_univ, true_and]
    simp_rw [h_eq_sdiff]
    have : (fun a => κ a (Set.univ \ Prod.mk a ⁻¹' t)) =
        fun a => κ a Set.univ - κ a (Prod.mk a ⁻¹' t) := by
      ext1 a
      rw [← Set.sdiff_inter_self_eq_sdiff]; rw [Set.inter_univ]; rw [measure_sdiff (Set.subset_univ _)]
      · exact (measurable_prodMk_left htm).nullMeasurableSet
      · exact measure_ne_top _ _
    rw [this]
    exact Measurable.sub (Kernel.measurable_coe κ MeasurableSet.univ) iht
  | iUnion f h_disj hf_meas hf =>
    have (a : α) : κ a (Prod.mk a ⁻¹' ⋃ i, f i) = ∑' i, κ a (Prod.mk a ⁻¹' f i) := by
      rw [preimage_iUnion]; rw [measure_iUnion]
      · exact h_disj.mono fun _ _ => .preimage _
      · exact fun i => measurable_prodMk_left (hf_meas i)
    simpa only [this] using Measurable.tsum hf

/--
theorem `measurable_kernel_prodMk_left` / 定理 `measurable_kernel_prodMk_left`

English:
theorem measurable_kernel_prodMk_left
  statement: [IsSFiniteKernel κ] {t : Set (α × β)}
  proof: by
  rw [← Kernel.kernel_sum_seq κ]
  have (a : _) : Kernel.sum (Kernel.seq κ) a (Prod.mk a ⁻¹' t) =
      ∑' n, Kernel.seq κ n a (Prod.mk a ⁻¹' t) :=
    Kernel.sum_apply' _ _ (measurable_prodMk_left ht)
  simp_rw [this]
  refine Measurable.tsum fun n => ?_
  exact measurable_kernel_prodMk_left_of_

中文:
定理 measurable_kernel_prodMk_left
  结论: [是SFiniteKernel κ] {t : 集合 (α × β)}
  证明: by
  rw [← Kernel.kernel_sum_seq κ]
  have (a : _) : Kernel.sum (Kernel.seq κ) a (Prod.mk a ⁻¹' t) =
      ∑' n, Kernel.seq κ n a (Prod.mk a ⁻¹' t) :=
    Kernel.sum_apply' _ _ (measurable_prodMk_left ht)
  simp_rw [this]
  refine Measurable.tsum fun n => ?_
  exact measurable_kernel_prodMk_left_of_

Depends on / 依赖: Kernel, Kernel.kernel_sum_seq, Kernel.seq, Kernel.sum, Kernel.sum_apply, Measurable, Measurable.tsum, Prod.mk, kernel_sum_seq, measurable_kernel_prodMk_left_of_finite, measurable_prodMk_left, simp_rw, sum_apply
-/
theorem measurable_kernel_prodMk_left [IsSFiniteKernel κ] {t : Set (α × β)}
    (ht : MeasurableSet t) : Measurable fun a => κ a (Prod.mk a ⁻¹' t) := by
  rw [← Kernel.kernel_sum_seq κ]
  have (a : _) : Kernel.sum (Kernel.seq κ) a (Prod.mk a ⁻¹' t) =
      ∑' n, Kernel.seq κ n a (Prod.mk a ⁻¹' t) :=
    Kernel.sum_apply' _ _ (measurable_prodMk_left ht)
  simp_rw [this]
  refine Measurable.tsum fun n => ?_
  exact measurable_kernel_prodMk_left_of_finite ht inferInstance

/--
theorem `measurable_kernel_prodMk_left'` / 定理 `measurable_kernel_prodMk_left'`

English:
theorem measurable_kernel_prodMk_left'
  statement: [IsSFiniteKernel η] {s : Set (β × γ)} (hs : MeasurableSet s)
  proof: by
  have (b : _) : Prod.mk b ⁻¹' s = {c | ((a, b), c) in {p : (α × β) × γ | (p.1.2, p.2) in s}} := rfl
  simp_rw [this]
  refine (measurable_kernel_prodMk_left ?_).comp measurable_prodMk_left
  exact (measurable_fst.snd.prodMk measurable_snd) hs

中文:
定理 measurable_kernel_prodMk_left'
  结论: [是SFiniteKernel η] {s : 集合 (β × γ)} (hs : 可测集 s)
  证明: by
  have (b : _) : Prod.mk b ⁻¹' s = {c | ((a, b), c) in {p : (α × β) × γ | (p.1.2, p.2) in s}} := rfl
  simp_rw [this]
  refine (measurable_kernel_prodMk_left ?_).comp measurable_prodMk_left
  exact (measurable_fst.snd.prodMk measurable_snd) hs

Depends on / 依赖: Prod.mk, measurable_fst, measurable_fst.snd.prodMk, measurable_kernel_prodMk_left, measurable_prodMk_left, measurable_snd, prodMk, simp_rw
-/
theorem measurable_kernel_prodMk_left' [IsSFiniteKernel η] {s : Set (β × γ)} (hs : MeasurableSet s)
    (a : α) : Measurable fun b => η (a, b) (Prod.mk b ⁻¹' s) := by
  have (b : _) : Prod.mk b ⁻¹' s = {c | ((a, b), c) in {p : (α × β) × γ | (p.1.2, p.2) in s}} := rfl
  simp_rw [this]
  refine (measurable_kernel_prodMk_left ?_).comp measurable_prodMk_left
  exact (measurable_fst.snd.prodMk measurable_snd) hs

/--
theorem `measurable_kernel_prodMk_right` / 定理 `measurable_kernel_prodMk_right`

English:
theorem measurable_kernel_prodMk_right
  statement: [IsSFiniteKernel κ] {s : Set (β × α)}
  proof: measurable_kernel_prodMk_left (measurableSet_swap_iff.mpr hs)

中文:
定理 measurable_kernel_prodMk_right
  结论: [是SFiniteKernel κ] {s : 集合 (β × α)}
  证明: measurable_kernel_prodMk_left (measurableSet_swap_iff.mpr hs)

Depends on / 依赖: measurableSet_swap_iff, measurableSet_swap_iff.mpr, measurable_kernel_prodMk_left
-/
theorem measurable_kernel_prodMk_right [IsSFiniteKernel κ] {s : Set (β × α)}
    (hs : MeasurableSet s) : Measurable fun y => κ y ((fun x => (x, y)) ⁻¹' s) :=
  measurable_kernel_prodMk_left (measurableSet_swap_iff.mpr hs)

end Kernel

open ProbabilityTheory.Kernel

section Lintegral

variable [IsSFiniteKernel κ] [IsSFiniteKernel η]

/--
theorem `Kernel.measurable_lintegral_indicator_const` / 定理 `Kernel.measurable_lintegral_indicator_const`

English:
theorem Kernel.measurable_lintegral_indicator_const
  statement: {t : Set (α × β)} (ht : MeasurableSet t)
  proof: by
  unfold Function.const
  simp_rw [lintegral_indicator_const_comp measurable_prodMk_left ht _]
  exact Measurable.const_mul (measurable_kernel_prodMk_left ht) c

中文:
定理 核.measurable_lintegral_indicator_const
  结论: {t : 集合 (α × β)} (ht : 可测集 t)
  证明: by
  unfold Function.const
  simp_rw [lintegral_indicator_const_comp measurable_prodMk_left ht _]
  exact Measurable.const_mul (measurable_kernel_prodMk_left ht) c

Depends on / 依赖: Function, Function.const, Measurable, Measurable.const_mul, const_mul, lintegral_indicator_const_comp, measurable_kernel_prodMk_left, measurable_prodMk_left, simp_rw
-/
theorem Kernel.measurable_lintegral_indicator_const {t : Set (α × β)} (ht : MeasurableSet t)
    (c : Real>=0∞) : Measurable fun a => ∫⁻ b, t.indicator (Function.const (α × β) c) (a, b) ∂κ a := by
  unfold Function.const
  simp_rw [lintegral_indicator_const_comp measurable_prodMk_left ht _]
  exact Measurable.const_mul (measurable_kernel_prodMk_left ht) c

/-- For an s-finite kernel `κ` and a function `f : α → β → ℝ≥0∞` which is measurable when seen as a
map from `α × β` (hypothesis `Measurable (uncurry f)`), the integral `a ↦ ∫⁻ b, f a b ∂(κ a)` is
measurable. -/
@[fun_prop]
/--
theorem `_root_.Measurable.lintegral_kernel_prod_right` / 定理 `_root_.Measurable.lintegral_kernel_prod_right`

English:
theorem _root_.Measurable.lintegral_kernel_prod_right
  statement: {f : α -> β -> Real>=0∞}
  proof: by
  let F : Nat -> SimpleFunc (α × β) Real>=0∞ := SimpleFunc.eapprox (uncurry f)
  have h : forall a, ⨆ n, F n a = uncurry f a := SimpleFunc.iSup_eapprox_apply hf
  simp only [Prod.forall, uncurry_apply_pair] at h
  simp_rw [← h]
  have : forall a, (∫⁻ b, ⨆ n, F n (a, b) ∂κ a) = ⨆ n, ∫⁻ b, F n (a, 

中文:
定理 _root_.可测.lintegral_kernel_prod_right
  结论: {f : α -> β -> 实数>=0∞}
  证明: by
  let F : Nat -> SimpleFunc (α × β) Real>=0∞ := SimpleFunc.eapprox (uncurry f)
  have h : forall a, ⨆ n, F n a = uncurry f a := SimpleFunc.iSup_eapprox_apply hf
  simp only [Prod.forall, uncurry_apply_pair] at h
  simp_rw [← h]
  have : forall a, (∫⁻ b, ⨆ n, F n (a, b) ∂κ a) = ⨆ n, ∫⁻ b, F n (a, 

Depends on / 依赖: Prod.forall, SimpleFunc, SimpleFunc.eapprox, SimpleFunc.iSup_eapprox_apply, SimpleFunc.monotone_eapprox, eapprox, iSup_eapprox_apply, lintegral_iSup, measurable, measurable.comp, measurable_prodMk_left, monotone_eapprox, simp_rw, uncurry, uncurry_apply_pair
-/
theorem _root_.Measurable.lintegral_kernel_prod_right {f : α -> β -> Real>=0∞}
    (hf : Measurable (uncurry f)) : Measurable fun a => ∫⁻ b, f a b ∂κ a := by
  let F : Nat -> SimpleFunc (α × β) Real>=0∞ := SimpleFunc.eapprox (uncurry f)
  have h : forall a, ⨆ n, F n a = uncurry f a := SimpleFunc.iSup_eapprox_apply hf
  simp only [Prod.forall, uncurry_apply_pair] at h
  simp_rw [← h]
  have : forall a, (∫⁻ b, ⨆ n, F n (a, b) ∂κ a) = ⨆ n, ∫⁻ b, F n (a, b) ∂κ a := by
    intro a
    rw [lintegral_iSup]
    · exact fun n => (F n).measurable.comp measurable_prodMk_left
    · exact fun i j hij b => SimpleFunc.monotone_eapprox (uncurry f) hij _
  simp_rw [this]
  refine .iSup fun n => ?_
  refine SimpleFunc.induction
    (motive := fun f => Measurable (fun (a : α) => ∫⁻ (b : β), f (a, b) ∂κ a)) ?_ ?_ (F n)
  · intro c t ht
    simp only [SimpleFunc.const_zero, SimpleFunc.coe_piecewise, SimpleFunc.coe_const,
      SimpleFunc.coe_zero, Set.piecewise_eq_indicator]
    exact Kernel.measurable_lintegral_indicator_const (κ := κ) ht c
  · intro g₁ g₂ _ hm₁ hm₂
    simp only [SimpleFunc.coe_add, Pi.add_apply]
    have h_add :
      (fun a => ∫⁻ b, g₁ (a, b) + g₂ (a, b) ∂κ a) =
        (fun a => ∫⁻ b, g₁ (a, b) ∂κ a) + fun a => ∫⁻ b, g₂ (a, b) ∂κ a := by
      ext1 a
      rw [Pi.add_apply]; rw [lintegral_add_left (by fun_prop)]
    rw [h_add]
    exact Measurable.add hm₁ hm₂

@[fun_prop]
/--
theorem `_root_.Measurable.lintegral_kernel_prod_right'` / 定理 `_root_.Measurable.lintegral_kernel_prod_right'`

English:
theorem _root_.Measurable.lintegral_kernel_prod_right'
  given: {f : α × β -> Real>=0∞} (hf : Measurable f)
  proof: by fun_prop

@[fun_prop]

中文:
定理 _root_.可测.lintegral_kernel_prod_right'
  条件: {f : α × β -> 实数>=0∞} (hf : 可测 f)
  证明: by fun_prop

@[fun_prop]

Depends on / 依赖: fun_prop
-/
theorem _root_.Measurable.lintegral_kernel_prod_right' {f : α × β -> Real>=0∞} (hf : Measurable f) :
    Measurable fun a => ∫⁻ b, f (a, b) ∂κ a := by fun_prop

@[fun_prop]
/--
theorem `_root_.Measurable.lintegral_kernel_prod_right''` / 定理 `_root_.Measurable.lintegral_kernel_prod_right''`

English:
theorem _root_.Measurable.lintegral_kernel_prod_right''
  given: {f : β × γ -> Real>=0∞} (hf : Measurable f)
  proof: by
  change
    Measurable
      ((fun x => ∫⁻ y, (fun u : (α × β) × γ => f (u.1.2, u.2)) (x, y) ∂η x) ∘ fun x => (a, x))
  -- Porting note: specified `κ`, `f`.
  refine (Measurable.lintegral_kernel_prod_right' (κ := η)
    (f := (fun u => f (u.fst.snd, u.snd))) ?_).comp measurable_prodMk_left
  fun

中文:
定理 _root_.可测.lintegral_kernel_prod_right''
  条件: {f : β × γ -> 实数>=0∞} (hf : 可测 f)
  证明: by
  change
    Measurable
      ((fun x => ∫⁻ y, (fun u : (α × β) × γ => f (u.1.2, u.2)) (x, y) ∂η x) ∘ fun x => (a, x))
  -- Porting note: specified `κ`, `f`.
  refine (Measurable.lintegral_kernel_prod_right' (κ := η)
    (f := (fun u => f (u.fst.snd, u.snd))) ?_).comp measurable_prodMk_left
  fun

Depends on / 依赖: Measurable
-/
theorem _root_.Measurable.lintegral_kernel_prod_right'' {f : β × γ -> Real>=0∞} (hf : Measurable f) :
    Measurable fun x => ∫⁻ y, f (x, y) ∂η (a, x) := by
  change
    Measurable
      ((fun x => ∫⁻ y, (fun u : (α × β) × γ => f (u.1.2, u.2)) (x, y) ∂η x) ∘ fun x => (a, x))
  -- Porting note: specified `κ`, `f`.
  refine (Measurable.lintegral_kernel_prod_right' (κ := η)
    (f := (fun u => f (u.fst.snd, u.snd))) ?_).comp measurable_prodMk_left
  fun_prop

/--
theorem `_root_.Measurable.setLIntegral_kernel_prod_right` / 定理 `_root_.Measurable.setLIntegral_kernel_prod_right`

English:
theorem _root_.Measurable.setLIntegral_kernel_prod_right
  statement: {f : α -> β -> Real>=0∞}
  proof: by
  simp_rw [← lintegral_restrict κ hs]; fun_prop

@[fun_prop]

中文:
定理 _root_.可测.setL整数egral_kernel_prod_right
  结论: {f : α -> β -> 实数>=0∞}
  证明: by
  simp_rw [← lintegral_restrict κ hs]; fun_prop

@[fun_prop]

Depends on / 依赖: fun_prop, lintegral_restrict, simp_rw
-/
theorem _root_.Measurable.setLIntegral_kernel_prod_right {f : α -> β -> Real>=0∞}
    (hf : Measurable (uncurry f)) {s : Set β} (hs : MeasurableSet s) :
    Measurable fun a => ∫⁻ b in s, f a b ∂κ a := by
  simp_rw [← lintegral_restrict κ hs]; fun_prop

@[fun_prop]
/--
theorem `_root_.Measurable.lintegral_kernel_prod_left'` / 定理 `_root_.Measurable.lintegral_kernel_prod_left'`

English:
theorem _root_.Measurable.lintegral_kernel_prod_left'
  given: {f : β × α -> Real>=0∞} (hf : Measurable f)
  proof: by fun_prop

@[fun_prop]

中文:
定理 _root_.可测.lintegral_kernel_prod_left'
  条件: {f : β × α -> 实数>=0∞} (hf : 可测 f)
  证明: by fun_prop

@[fun_prop]

Depends on / 依赖: fun_prop
-/
theorem _root_.Measurable.lintegral_kernel_prod_left' {f : β × α -> Real>=0∞} (hf : Measurable f) :
    Measurable fun y => ∫⁻ x, f (x, y) ∂κ y := by fun_prop

@[fun_prop]
/--
theorem `_root_.Measurable.lintegral_kernel_prod_left` / 定理 `_root_.Measurable.lintegral_kernel_prod_left`

English:
theorem _root_.Measurable.lintegral_kernel_prod_left
  statement: {f : β -> α -> Real>=0∞}
  proof: by fun_prop

中文:
定理 _root_.可测.lintegral_kernel_prod_left
  结论: {f : β -> α -> 实数>=0∞}
  证明: by fun_prop

Depends on / 依赖: fun_prop
-/
theorem _root_.Measurable.lintegral_kernel_prod_left {f : β -> α -> Real>=0∞}
    (hf : Measurable (uncurry f)) : Measurable fun y => ∫⁻ x, f x y ∂κ y := by fun_prop

/--
theorem `_root_.Measurable.setLIntegral_kernel_prod_left` / 定理 `_root_.Measurable.setLIntegral_kernel_prod_left`

English:
theorem _root_.Measurable.setLIntegral_kernel_prod_left
  statement: {f : β -> α -> Real>=0∞}
  proof: by
  simp_rw [← lintegral_restrict κ hs]; fun_prop

@[fun_prop]

中文:
定理 _root_.可测.setL整数egral_kernel_prod_left
  结论: {f : β -> α -> 实数>=0∞}
  证明: by
  simp_rw [← lintegral_restrict κ hs]; fun_prop

@[fun_prop]

Depends on / 依赖: fun_prop, lintegral_restrict, simp_rw
-/
theorem _root_.Measurable.setLIntegral_kernel_prod_left {f : β -> α -> Real>=0∞}
    (hf : Measurable (uncurry f)) {s : Set β} (hs : MeasurableSet s) :
    Measurable fun b => ∫⁻ a in s, f a b ∂κ b := by
  simp_rw [← lintegral_restrict κ hs]; fun_prop

@[fun_prop]
/--
theorem `_root_.Measurable.lintegral_kernel` / 定理 `_root_.Measurable.lintegral_kernel`

English:
theorem _root_.Measurable.lintegral_kernel
  given: {κ : Kernel α β} {f : β -> Real>=0∞} (hf : Measurable f)
  proof: by fun_prop

中文:
定理 _root_.可测.lintegral_kernel
  条件: {κ : 核 α β} {f : β -> 实数>=0∞} (hf : 可测 f)
  证明: by fun_prop

Depends on / 依赖: fun_prop
-/
theorem _root_.Measurable.lintegral_kernel {κ : Kernel α β} {f : β -> Real>=0∞} (hf : Measurable f) :
    Measurable fun a => ∫⁻ b, f b ∂κ a := by fun_prop

/--
theorem `_root_.Measurable.setLIntegral_kernel` / 定理 `_root_.Measurable.setLIntegral_kernel`

English:
theorem _root_.Measurable.setLIntegral_kernel
  statement: {f : β -> Real>=0∞} (hf : Measurable f) {s : Set β}
  proof: Measurable.setLIntegral_kernel_prod_right (by fun_prop) hs

中文:
定理 _root_.可测.setL整数egral_kernel
  结论: {f : β -> 实数>=0∞} (hf : 可测 f) {s : 集合 β}
  证明: Measurable.setLIntegral_kernel_prod_right (by fun_prop) hs

Depends on / 依赖: Measurable, Measurable.setLIntegral_kernel_prod_right, fun_prop, setLIntegral_kernel_prod_right
-/
theorem _root_.Measurable.setLIntegral_kernel {f : β -> Real>=0∞} (hf : Measurable f) {s : Set β}
    (hs : MeasurableSet s) : Measurable fun a => ∫⁻ b in s, f b ∂κ a :=
  Measurable.setLIntegral_kernel_prod_right (by fun_prop) hs

end Lintegral

end ProbabilityTheory
