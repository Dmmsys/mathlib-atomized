/-
Copyright (c) 2025 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.PreorderRestrict
public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.Probability.Kernel.IonescuTulcea.Maps

/-!
# Consecutive composition of kernels

This file is the first step towards Ionescu-Tulcea theorem, which allows for instance to construct
the product of an infinite family of probability measures. The idea of the statement is as follows:
consider a family of kernels `κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1))`.
One can interpret `κ n` as a kernel which takes as an input the trajectory of a point started in
`X 0` and moving `X 0 → X 1 → X 2 → ... → X n` and which outputs the distribution of the next
position of the point in `X (n + 1)`. If `a b : ℕ` and `a < b`, we can compose the kernels,
and `κ a ⊗ₖ κ (a + 1) ⊗ₖ ... ⊗ₖ κ b` takes the trajectory up to time `a` as input and outputs
the distribution of the trajectory in `X (a + 1) × ... × X (b + 1)`.

The Ionescu-Tulcea theorem then tells us that these compositions can be extended into a kernel
`η : Kernel (Π i : Iic a, X i) → Π n > a, X n` which given the trajectory up to time `a` outputs
the distribution of the infinite trajectory started in `X (a + 1)`. In other words this theorem
makes sense of composing infinitely many kernels together.

To be able to even state the theorem we want to take the composition-product
(see `ProbabilityTheory.Kernel.compProd`) of consecutive kernels.
This however is not straightforward.

Consider `n : ℕ`. We cannot write `(κ n) ⊗ₖ (κ (n + 1))` directly, we need to first
introduce an equivalence to see `κ (n + 1)` as a kernel with codomain
`(Π i : Iic n, X i) × X (n + 1)`, and we get a `Kernel (Π i : Iic n, X i) (X (n + 1) × (X (n + 2))`.
However we want to do multiple composition at once, i.e. write
`(κ n) ⊗ₖ ... ⊗ₖ (κ m)` for `n < m`. This requires even more equivalences to make sense of, and at
the end of the day we get kernels which still cannot be composed together.

To tackle this issue, we decide here to only consider kernels of the form
`Kernel (Π i : Iic a, X i) (Π i : Iic b, X i)`. In other words these kernels take as input
a trajectory up to time `a` and output the distribution of the full trajectory up to time `b`.
This is captured in the definition `partialTraj κ a b`
(`partialTraj` stands for "partial trajectory").
The advantage of this approach is that it allows us to write for instance
`partialTraj κ b c ∘ₖ partialTraj κ a b = partialTraj κ a c` (see `partialTraj_comp_partialTraj`.)

In this file we therefore define this family of kernels and prove some properties of it.
In particular we provide at the end of the file some results to compute the integral of a function
against `partialTraj κ a b`, taking inspiration from `MeasureTheory.lmarginal`.

## Main definitions

* `partialTraj κ a b`: Given the trajectory of a point up to time `a`, returns the distribution
  of the trajectory up to time `b`.
* `lmarginalPartialTraj κ a b f`: The integral of `f` against `partialTraj κ a b`.
  This is essentially the integral of `f` against `κ (a + 1) ⊗ₖ ... ⊗ₖ κ b` but seen as depending
  on all the variables, mimicking `MeasureTheory.lmarginal`. This allows to write
  `lmarginalPartialTraj κ b c (lmarginalPartialTraj κ a b f)`.

## Main statements

* `partialTraj_comp_partialTraj`: if `a ≤ b` and `b ≤ c` then
  `partialTraj κ b c ∘ₖ partialTraj κ a b = partialTraj κ a c`.
* `map_partialTraj_succ_self a`: the pushforward of `partialTraj κ a (a + 1)` along the point at
  time `a + 1` is the kernel `κ a`.
* `lmarginalPartialTraj_self` : if `a ≤ b` and `b ≤ c` then
  `lmarginalPartialTraj κ b c (lmarginalPartialTraj κ a b f) = lmarginalPartialTraj κ a c`.

## Tags

Ionescu-Tulcea theorem, composition of kernels
-/

@[expose] public section

open Finset Function MeasureTheory Preorder ProbabilityTheory

open scoped ENNReal

variable {X : Nat -> Type*} {mX : forall n, MeasurableSpace (X n)} {a b c : Nat}
  {κ : (n : Nat) -> Kernel (Π i : Iic n, X i) (X (n + 1))}

section partialTraj

/-! ### Definition of `partialTraj` -/

namespace ProbabilityTheory.Kernel

open MeasurableEquiv

variable (κ) in
/--
Definition of `partialTraj` / `partialTraj` 的定义

English:
definition partialTraj
  signature: (a b : Nat)
  body: if h : b <= a then deterministic (frestrictLe₂ h) (measurable_frestrictLe₂ h)
  else @Nat.leRec a (fun b _ => Kernel (Π i : Iic a, X i) (Π i : Iic b, X i)) Kernel.id
    (fun k _ κ_k => ((Kernel.id ×ₖ ((κ k).map (piSingleton k))) ∘ₖ κ_k).map (IicProdIoc k (k + 1)))
    b (Nat.le_of_not_ge h)

中文:
定义 partialTraj
  签名: (a b : 自然数)
  定义体: if h : b <= a then deterministic (frestrictLe₂ h) (measurable_frestrictLe₂ h)
  else @Nat.leRec a (fun b _ => Kernel (Π i : Iic a, X i) (Π i : Iic b, X i)) Kernel.id
    (fun k _ κ_k => ((Kernel.id ×ₖ ((κ k).map (piSingleton k))) ∘ₖ κ_k).map (IicProdIoc k (k + 1)))
    b (Nat.le_of_not_ge h)

Depends on / 依赖: IicProdIoc, Kernel, Kernel.id, Nat.leRec, Nat.le_of_not_ge, deterministic, le_of_not_ge, piSingleton
-/
noncomputable def partialTraj (a b : Nat) : Kernel (Π i : Iic a, X i) (Π i : Iic b, X i) :=
  if h : b <= a then deterministic (frestrictLe₂ h) (measurable_frestrictLe₂ h)
  else @Nat.leRec a (fun b _ => Kernel (Π i : Iic a, X i) (Π i : Iic b, X i)) Kernel.id
    (fun k _ κ_k => ((Kernel.id ×ₖ ((κ k).map (piSingleton k))) ∘ₖ κ_k).map (IicProdIoc k (k + 1)))
    b (Nat.le_of_not_ge h)

section Basic

/--
lemma `partialTraj_le` / 引理 `partialTraj_le`

English:
lemma partialTraj_le
  given: (hba : b <= a)
  proof: by
  rw [partialTraj]; rw [dif_pos hba]

@[simp]

中文:
引理 partialTraj_le
  条件: (hba : b <= a)
  证明: by
  rw [partialTraj]; rw [dif_pos hba]

@[simp]

Depends on / 依赖: dif_pos, partialTraj
-/
lemma partialTraj_le (hba : b <= a) :
    partialTraj κ a b = deterministic (frestrictLe₂ hba) (measurable_frestrictLe₂ _) := by
  rw [partialTraj]; rw [dif_pos hba]

@[simp]
/--
lemma `partialTraj_self` / 引理 `partialTraj_self`

English:
lemma partialTraj_self
  given: (a : Nat)
  statement: partialTraj κ a a = Kernel.id
  proof: by rw [partialTraj_le le_rfl]; rfl

@[simp]

中文:
引理 partialTraj_self
  条件: (a : 自然数)
  结论: partialTraj κ a a = 核.id
  证明: by rw [partialTraj_le le_rfl]; rfl

@[simp]

Depends on / 依赖: le_rfl, partialTraj_le
-/
lemma partialTraj_self (a : Nat) : partialTraj κ a a = Kernel.id := by rw [partialTraj_le le_rfl]; rfl

@[simp]
/--
lemma `partialTraj_zero` / 引理 `partialTraj_zero`

English:
lemma partialTraj_zero
  proof: by
  rw [partialTraj_le zero_le]

中文:
引理 partialTraj_zero
  证明: by
  rw [partialTraj_le zero_le]

Depends on / 依赖: partialTraj_le, zero_le
-/
lemma partialTraj_zero :
    partialTraj κ a 0 = deterministic (frestrictLe₂ zero_le) (measurable_frestrictLe₂ _) := by
  rw [partialTraj_le zero_le]

/--
lemma `partialTraj_le_def` / 引理 `partialTraj_le_def`

English:
lemma partialTraj_le_def
  given: (hab : a <= b)
  statement: partialTraj κ a b =
  proof: by
  obtain rfl | hab := eq_or_lt_of_le hab
  · simp
  · rw [partialTraj, dif_neg (not_le.2 hab)]

中文:
引理 partialTraj_le_def
  条件: (hab : a <= b)
  结论: partialTraj κ a b =
  证明: by
  obtain rfl | hab := eq_or_lt_of_le hab
  · simp
  · rw [partialTraj, dif_neg (not_le.2 hab)]

Depends on / 依赖: dif_neg, eq_or_lt_of_le, not_le, partialTraj
-/
lemma partialTraj_le_def (hab : a <= b) : partialTraj κ a b =
    @Nat.leRec a (fun b _ => Kernel (Π i : Iic a, X i) (Π i : Iic b, X i)) Kernel.id
    (fun k _ κ_k => ((Kernel.id ×ₖ ((κ k).map (piSingleton k))) ∘ₖ κ_k).map (IicProdIoc k (k + 1)))
    b hab := by
  obtain rfl | hab := eq_or_lt_of_le hab
  · simp
  · rw [partialTraj, dif_neg (not_le.2 hab)]

/--
lemma `partialTraj_succ_of_le` / 引理 `partialTraj_succ_of_le`

English:
lemma partialTraj_succ_of_le
  given: (hab : a <= b)
  statement: partialTraj κ a (b + 1) =
  proof: by
  rw [partialTraj]; rw [dif_neg (by lia)]
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ k hak hk => rw [Nat.leRec_succ, ← partialTraj_le_def]; lia

中文:
引理 partialTraj_succ_of_le
  条件: (hab : a <= b)
  结论: partialTraj κ a (b + 1) =
  证明: by
  rw [partialTraj]; rw [dif_neg (by lia)]
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ k hak hk => rw [Nat.leRec_succ, ← partialTraj_le_def]; lia

Depends on / 依赖: Nat.leRec_succ, Nat.le_induction, dif_neg, leRec_succ, le_induction, partialTraj, partialTraj_le_def
-/
lemma partialTraj_succ_of_le (hab : a <= b) : partialTraj κ a (b + 1) =
    ((Kernel.id ×ₖ ((κ b).map (piSingleton b))) ∘ₖ partialTraj κ a b).map
    (IicProdIoc b (b + 1)) := by
  rw [partialTraj]; rw [dif_neg (by lia)]
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ k hak hk => rw [Nat.leRec_succ, ← partialTraj_le_def]; lia

instance (a b : Nat) : IsSFiniteKernel (partialTraj κ a b) := by
  obtain hab | hba := le_total a b
  · induction b, hab using Nat.le_induction with
    | base => rw [partialTraj_self]; infer_instance
    | succ k hak => rw [partialTraj_succ_of_le hak]; infer_instance
  · rw [partialTraj_le hba]; infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: n, IsFiniteKernel (κ n)] (a b
  body: by
  obtain hab | hba := le_total a b
  · induction b, hab using Nat.le_induction with
    | base => rw [partialTraj_self]; infer_instance
    | succ k hak => rw [partialTraj_succ_of_le hak]; infer_instance
  · rw [partialTraj_le hba]; infer_instance

中文:
实例 [对任意
  签名: n, 是FiniteKernel (κ n)] (a b
  定义体: by
  obtain hab | hba := le_total a b
  · induction b, hab using Nat.le_induction with
    | base => rw [partialTraj_self]; infer_instance
    | succ k hak => rw [partialTraj_succ_of_le hak]; infer_instance
  · rw [partialTraj_le hba]; infer_instance

Depends on / 依赖: Nat.le_induction, infer_instance, le_induction, le_total, partialTraj_le, partialTraj_self, partialTraj_succ_of_le
-/
instance [forall n, IsFiniteKernel (κ n)] (a b : Nat) : IsFiniteKernel (partialTraj κ a b) := by
  obtain hab | hba := le_total a b
  · induction b, hab using Nat.le_induction with
    | base => rw [partialTraj_self]; infer_instance
    | succ k hak => rw [partialTraj_succ_of_le hak]; infer_instance
  · rw [partialTraj_le hba]; infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: n, IsZeroOrMarkovKernel (κ n)] (a b
  body: by
  obtain hab | hba := le_total a b
  · induction b, hab using Nat.le_induction with
    | base => rw [partialTraj_self]; infer_instance
    | succ k hak => rw [partialTraj_succ_of_le hak]; infer_instance
  · rw [partialTraj_le hba]; infer_instance

中文:
实例 [对任意
  签名: n, 是ZeroOrMarkovKernel (κ n)] (a b
  定义体: by
  obtain hab | hba := le_total a b
  · induction b, hab using Nat.le_induction with
    | base => rw [partialTraj_self]; infer_instance
    | succ k hak => rw [partialTraj_succ_of_le hak]; infer_instance
  · rw [partialTraj_le hba]; infer_instance

Depends on / 依赖: Nat.le_induction, infer_instance, le_induction, le_total, partialTraj_le, partialTraj_self, partialTraj_succ_of_le
-/
instance [forall n, IsZeroOrMarkovKernel (κ n)] (a b : Nat) :
    IsZeroOrMarkovKernel (partialTraj κ a b) := by
  obtain hab | hba := le_total a b
  · induction b, hab using Nat.le_induction with
    | base => rw [partialTraj_self]; infer_instance
    | succ k hak => rw [partialTraj_succ_of_le hak]; infer_instance
  · rw [partialTraj_le hba]; infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: n, IsMarkovKernel (κ n)] (a b
  body: by
  obtain hab | hba := le_total a b
  · induction b, hab using Nat.le_induction with
    | base => rw [partialTraj_self]; infer_instance
    | succ k hak =>
      rw [partialTraj_succ_of_le hak]
      have := IsMarkovKernel.map (κ k) (piSingleton k).measurable
      exact IsMarkovKernel.map _ meas

中文:
实例 [对任意
  签名: n, 是MarkovKernel (κ n)] (a b
  定义体: by
  obtain hab | hba := le_total a b
  · induction b, hab using Nat.le_induction with
    | base => rw [partialTraj_self]; infer_instance
    | succ k hak =>
      rw [partialTraj_succ_of_le hak]
      have := IsMarkovKernel.map (κ k) (piSingleton k).measurable
      exact IsMarkovKernel.map _ meas

Depends on / 依赖: IsMarkovKernel, IsMarkovKernel.map, Nat.le_induction, infer_instance, le_induction, le_total, measurable, measurable_IicProdIoc, partialTraj_le, partialTraj_self, partialTraj_succ_of_le, piSingleton
-/
instance [forall n, IsMarkovKernel (κ n)] (a b : Nat) :
    IsMarkovKernel (partialTraj κ a b) := by
  obtain hab | hba := le_total a b
  · induction b, hab using Nat.le_induction with
    | base => rw [partialTraj_self]; infer_instance
    | succ k hak =>
      rw [partialTraj_succ_of_le hak]
      have := IsMarkovKernel.map (κ k) (piSingleton k).measurable
      exact IsMarkovKernel.map _ measurable_IicProdIoc
  · rw [partialTraj_le hba]; infer_instance

/--
lemma `partialTraj_succ_self` / 引理 `partialTraj_succ_self`

English:
lemma partialTraj_succ_self
  given: (a : Nat)
  proof: by
  rw [partialTraj_succ_of_le le_rfl]; rw [partialTraj_self]; rw [comp_id]

中文:
引理 partialTraj_succ_self
  条件: (a : 自然数)
  证明: by
  rw [partialTraj_succ_of_le le_rfl]; rw [partialTraj_self]; rw [comp_id]

Depends on / 依赖: comp_id, le_rfl, partialTraj_self, partialTraj_succ_of_le
-/
lemma partialTraj_succ_self (a : Nat) :
    partialTraj κ a (a + 1) =
    (Kernel.id ×ₖ ((κ a).map (piSingleton a))).map (IicProdIoc a (a + 1)) := by
  rw [partialTraj_succ_of_le le_rfl]; rw [partialTraj_self]; rw [comp_id]

/--
lemma `partialTraj_succ_eq_comp` / 引理 `partialTraj_succ_eq_comp`

English:
lemma partialTraj_succ_eq_comp
  given: (hab : a <= b)
  proof: by
  rw [partialTraj_succ_self]; rw [← map_comp]; rw [partialTraj_succ_of_le hab]

中文:
引理 partialTraj_succ_eq_comp
  条件: (hab : a <= b)
  证明: by
  rw [partialTraj_succ_self]; rw [← map_comp]; rw [partialTraj_succ_of_le hab]

Depends on / 依赖: map_comp, partialTraj_succ_of_le, partialTraj_succ_self
-/
lemma partialTraj_succ_eq_comp (hab : a <= b) :
    partialTraj κ a (b + 1) = partialTraj κ b (b + 1) ∘ₖ partialTraj κ a b := by
  rw [partialTraj_succ_self]; rw [← map_comp]; rw [partialTraj_succ_of_le hab]

/--
theorem `partialTraj_comp_partialTraj` / 定理 `partialTraj_comp_partialTraj`

English:
theorem partialTraj_comp_partialTraj
  given: (hab : a <= b) (hbc : b <= c)
  proof: by
  induction c, hbc using Nat.le_induction with
  | base => simp
  | succ k h hk => rw [partialTraj_succ_eq_comp h, comp_assoc, hk,
      ← partialTraj_succ_eq_comp (hab.trans h)]

中文:
定理 partialTraj_comp_partialTraj
  条件: (hab : a <= b) (hbc : b <= c)
  证明: by
  induction c, hbc using Nat.le_induction with
  | base => simp
  | succ k h hk => rw [partialTraj_succ_eq_comp h, comp_assoc, hk,
      ← partialTraj_succ_eq_comp (hab.trans h)]

Depends on / 依赖: Nat.le_induction, comp_assoc, hab.trans, le_induction, partialTraj_succ_eq_comp
-/
theorem partialTraj_comp_partialTraj (hab : a <= b) (hbc : b <= c) :
    partialTraj κ b c ∘ₖ partialTraj κ a b = partialTraj κ a c := by
  induction c, hbc using Nat.le_induction with
  | base => simp
  | succ k h hk => rw [partialTraj_succ_eq_comp h, comp_assoc, hk,
      ← partialTraj_succ_eq_comp (hab.trans h)]

/--
lemma `fst_prod_comp_id_prod` / 引理 `fst_prod_comp_id_prod`

English:
lemma fst_prod_comp_id_prod
  statement: {X Y Z : Type*} {mX : MeasurableSpace X}
  proof: by
  ext x s ms
  simp_rw [comp_apply' _ _ _ ms, lintegral_id_prod (Kernel.measurable_coe _ ms),
    deterministic_prod_apply' _ _ _ ms, id_prod_apply' _ _ ms,
    comp_apply' _ _ _ (measurable_prodMk_left ms),
    lintegral_id_prod (η.measurable_coe (measurable_prodMk_left ms))]

中文:
引理 fst_prod_comp_id_prod
  结论: {X Y Z : 类型} {mX : 可测空间 X}
  证明: by
  ext x s ms
  simp_rw [comp_apply' _ _ _ ms, lintegral_id_prod (Kernel.measurable_coe _ ms),
    deterministic_prod_apply' _ _ _ ms, id_prod_apply' _ _ ms,
    comp_apply' _ _ _ (measurable_prodMk_left ms),
    lintegral_id_prod (η.measurable_coe (measurable_prodMk_left ms))]
-/
private lemma fst_prod_comp_id_prod {X Y Z : Type*} {mX : MeasurableSpace X}
    {mY : MeasurableSpace Y} {mZ : MeasurableSpace Z} (κ : Kernel X Y) [IsSFiniteKernel κ]
    (η : Kernel (X × Y) Z) [IsSFiniteKernel η] :
    ((deterministic Prod.fst measurable_fst) ×ₖ η) ∘ₖ (Kernel.id ×ₖ κ) =
    Kernel.id ×ₖ (η ∘ₖ (Kernel.id ×ₖ κ)) := by
  ext x s ms
  simp_rw [comp_apply' _ _ _ ms, lintegral_id_prod (Kernel.measurable_coe _ ms),
    deterministic_prod_apply' _ _ _ ms, id_prod_apply' _ _ ms,
    comp_apply' _ _ _ (measurable_prodMk_left ms),
    lintegral_id_prod (η.measurable_coe (measurable_prodMk_left ms))]

/--
lemma `partialTraj_eq_prod` / 引理 `partialTraj_eq_prod`

English:
lemma partialTraj_eq_prod
  given: [forall n, IsSFiniteKernel (κ n)] (a b : Nat)
  proof: by
  obtain hba | hab := le_total b a
  · rw [partialTraj_le hba, IicProdIoc_le hba, map_comp_right, ← fst_eq, deterministic_map,
      fst_prod, id_map]
    all_goals fun_prop
  induction b, hab using Nat.le_induction with
  | base =>
    ext1 x
    rw [partialTraj_self]; rw [id_map]; rw [map_apply

中文:
引理 partialTraj_eq_prod
  条件: [对任意 n, 是SFiniteKernel (κ n)] (a b : 自然数)
  证明: by
  obtain hba | hab := le_total b a
  · rw [partialTraj_le hba, IicProdIoc_le hba, map_comp_right, ← fst_eq, deterministic_map,
      fst_prod, id_map]
    all_goals fun_prop
  induction b, hab using Nat.le_induction with
  | base =>
    ext1 x
    rw [partialTraj_self]; rw [id_map]; rw [map_apply

Depends on / 依赖: IicProdIoc, IicProdIoc_le, IicProdIoc_self, Measure, Measure.fst, Measure.fst_prod, Nat.le_induction, Prod.map, all_goals, deterministic_map, fst_eq, fst_prod, fun_prop, h.trans, id_map, k.le_succ, le_induction, le_succ, le_total, map_apply
-/
lemma partialTraj_eq_prod [forall n, IsSFiniteKernel (κ n)] (a b : Nat) :
    partialTraj κ a b =
    (Kernel.id ×ₖ (partialTraj κ a b).map (restrict₂ Ioc_subset_Iic_self)).map
    (IicProdIoc a b) := by
  obtain hba | hab := le_total b a
  · rw [partialTraj_le hba, IicProdIoc_le hba, map_comp_right, ← fst_eq, deterministic_map,
      fst_prod, id_map]
    all_goals fun_prop
  induction b, hab using Nat.le_induction with
  | base =>
    ext1 x
    rw [partialTraj_self]; rw [id_map]; rw [map_apply]; rw [prod_apply]; rw [IicProdIoc_self]; rw [← Measure.fst]; rw [Measure.fst_prod]
    all_goals fun_prop
  | succ k h hk =>
    have : (IicProdIoc (X := X) k (k + 1)) ∘ (Prod.map (IicProdIoc a k) id) =
        (IicProdIoc (h.trans k.le_succ) ∘ (Prod.map id (IocProdIoc a k (k + 1)))) ∘
        prodAssoc := by
      ext x i
      simp only [IicProdIoc_def, MeasurableEquiv.IicProdIoc, MeasurableEquiv.coe_mk,
        Equiv.coe_fn_mk, Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq,
        Nat.succ_eq_add_one, IocProdIoc]
      split_ifs <;> try rfl
      lia
    nth_rw 1 [← partialTraj_comp_partialTraj h k.le_succ, hk, partialTraj_succ_self, comp_map,
      comap_map_comm, comap_prod, id_comap, ← id_map, map_prod_eq, ← map_comp_right, this,
      map_comp_right, id_prod_eq, prodAssoc_prod, map_comp_right, ← map_prod_map, map_id,
      ← map_comp, map_apply_eq_iff_map_symm_apply_eq, fst_prod_comp_id_prod, ← map_comp_right,
      ← coe_IicProdIoc (h.trans k.le_succ), symm_comp_self, map_id,
      deterministic_congr IicProdIoc_comp_restrict₂.symm, ← deterministic_comp_deterministic,
      comp_deterministic_eq_comap, ← comap_prod, ← map_comp, ← comp_map, ← hk,
      ← partialTraj_comp_partialTraj h k.le_succ, partialTraj_succ_self, map_comp, map_comp,
      ← map_comp_right, ← id_map, map_prod_eq, ← map_comp_right]
    · rfl
    all_goals fun_prop

variable [forall n, IsMarkovKernel (κ n)]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `map_partialTraj_succ_self` / 引理 `map_partialTraj_succ_self`

English:
lemma map_partialTraj_succ_self
  given: (a : Nat)
  proof: by
  have hp : (fun x : Π n : Iic (a + 1), X n => x ⟨a + 1, mem_Iic.2 le_rfl⟩) ∘ IicProdIoc a (a + 1) =
      (piSingleton a).symm ∘ Prod.snd := by
    ext
    simp [_root_.IicProdIoc, piSingleton]
  rw [partialTraj_succ_self]; rw [← map_comp_right _ (by fun_prop) (by fun_prop)]; rw [hp]; rw [map_co

中文:
引理 map_partialTraj_succ_self
  条件: (a : 自然数)
  证明: by
  have hp : (fun x : Π n : Iic (a + 1), X n => x ⟨a + 1, mem_Iic.2 le_rfl⟩) ∘ IicProdIoc a (a + 1) =
      (piSingleton a).symm ∘ Prod.snd := by
    ext
    simp [_root_.IicProdIoc, piSingleton]
  rw [partialTraj_succ_self]; rw [← map_comp_right _ (by fun_prop) (by fun_prop)]; rw [hp]; rw [map_co

Depends on / 依赖: IicProdIoc, Prod.snd, _root_, _root_.IicProdIoc, fun_prop, le_rfl, map_comp_right, map_id, mem_Iic, partialTraj_succ_self, piSingleton, snd_eq, snd_prod, symm_comp_self
-/
lemma map_partialTraj_succ_self (a : Nat) :
    (partialTraj κ a (a + 1)).map (fun x => x ⟨a + 1, mem_Iic.2 le_rfl⟩) = κ a := by
  have hp : (fun x : Π n : Iic (a + 1), X n => x ⟨a + 1, mem_Iic.2 le_rfl⟩) ∘ IicProdIoc a (a + 1) =
      (piSingleton a).symm ∘ Prod.snd := by
    ext
    simp [_root_.IicProdIoc, piSingleton]
  rw [partialTraj_succ_self]; rw [← map_comp_right _ (by fun_prop) (by fun_prop)]; rw [hp]; rw [map_comp_right _ (by fun_prop) (by fun_prop)]; rw [← snd_eq]; rw [snd_prod]; rw [← map_comp_right _ (by fun_prop) (by fun_prop)]; rw [symm_comp_self]; rw [map_id]

/--
lemma `partialTraj_succ_map_frestrictLe₂` / 引理 `partialTraj_succ_map_frestrictLe₂`

English:
lemma partialTraj_succ_map_frestrictLe₂
  given: (a b : Nat)
  proof: by
  obtain hab | hba := le_or_gt a b
  · have := IsMarkovKernel.map (κ b) (piSingleton b).measurable
    rw [partialTraj_succ_eq_comp hab]; rw [map_comp]; rw [partialTraj_succ_self]; rw [← map_comp_right]; rw [frestrictLe₂_comp_IicProdIoc]; rw [← fst_eq]; rw [fst_prod]; rw [id_comp]
    all_goals f

中文:
引理 partialTraj_succ_map_frestrictLe₂
  条件: (a b : 自然数)
  证明: by
  obtain hab | hba := le_or_gt a b
  · have := IsMarkovKernel.map (κ b) (piSingleton b).measurable
    rw [partialTraj_succ_eq_comp hab]; rw [map_comp]; rw [partialTraj_succ_self]; rw [← map_comp_right]; rw [frestrictLe₂_comp_IicProdIoc]; rw [← fst_eq]; rw [fst_prod]; rw [id_comp]
    all_goals f

Depends on / 依赖: IsMarkovKernel, IsMarkovKernel.map, Nat.succ_le_of_lt, all_goals, deterministic_map, fst_eq, fst_prod, fun_prop, hba.le, id_comp, le_or_gt, map_comp, map_comp_right, measurable, partialTraj_le, partialTraj_succ_eq_comp, partialTraj_succ_self, piSingleton, succ_le_of_lt
-/
lemma partialTraj_succ_map_frestrictLe₂ (a b : Nat) :
    (partialTraj κ a (b + 1)).map (frestrictLe₂ b.le_succ) = partialTraj κ a b := by
  obtain hab | hba := le_or_gt a b
  · have := IsMarkovKernel.map (κ b) (piSingleton b).measurable
    rw [partialTraj_succ_eq_comp hab]; rw [map_comp]; rw [partialTraj_succ_self]; rw [← map_comp_right]; rw [frestrictLe₂_comp_IicProdIoc]; rw [← fst_eq]; rw [fst_prod]; rw [id_comp]
    all_goals fun_prop
  · rw [partialTraj_le (Nat.succ_le_of_lt hba), partialTraj_le hba.le, deterministic_map]
    · rfl
    · fun_prop

/--
theorem `partialTraj_map_frestrictLe₂` / 定理 `partialTraj_map_frestrictLe₂`

English:
theorem partialTraj_map_frestrictLe₂
  given: (a : Nat) (hbc : b <= c)
  proof: by
  induction c, hbc using Nat.le_induction with
  | base => exact map_id ..
  | succ k h hk =>
    rw [← hk]; rw [← frestrictLe₂_comp_frestrictLe₂ h k.le_succ]; rw [map_comp_right]; rw [partialTraj_succ_map_frestrictLe₂]
    all_goals fun_prop

中文:
定理 partialTraj_map_frestrictLe₂
  条件: (a : 自然数) (hbc : b <= c)
  证明: by
  induction c, hbc using Nat.le_induction with
  | base => exact map_id ..
  | succ k h hk =>
    rw [← hk]; rw [← frestrictLe₂_comp_frestrictLe₂ h k.le_succ]; rw [map_comp_right]; rw [partialTraj_succ_map_frestrictLe₂]
    all_goals fun_prop

Depends on / 依赖: Nat.le_induction, all_goals, fun_prop, k.le_succ, le_induction, le_succ, map_comp_right, map_id
-/
theorem partialTraj_map_frestrictLe₂ (a : Nat) (hbc : b <= c) :
    (partialTraj κ a c).map (frestrictLe₂ hbc) = partialTraj κ a b := by
  induction c, hbc using Nat.le_induction with
  | base => exact map_id ..
  | succ k h hk =>
    rw [← hk]; rw [← frestrictLe₂_comp_frestrictLe₂ h k.le_succ]; rw [map_comp_right]; rw [partialTraj_succ_map_frestrictLe₂]
    all_goals fun_prop

/--
lemma `partialTraj_map_frestrictLe₂_apply` / 引理 `partialTraj_map_frestrictLe₂_apply`

English:
lemma partialTraj_map_frestrictLe₂_apply
  given: (x₀ : Π i : Iic a, X i) (hbc : b <= c)
  proof: by
  rw [← map_apply _ (by fun_prop)]; rw [partialTraj_map_frestrictLe₂]

中文:
引理 partialTraj_map_frestrictLe₂_apply
  条件: (x₀ : Π i : 左无界右闭区间 a, X i) (hbc : b <= c)
  证明: by
  rw [← map_apply _ (by fun_prop)]; rw [partialTraj_map_frestrictLe₂]

Depends on / 依赖: fun_prop, map_apply
-/
lemma partialTraj_map_frestrictLe₂_apply (x₀ : Π i : Iic a, X i) (hbc : b <= c) :
    (partialTraj κ a c x₀).map (frestrictLe₂ hbc) = partialTraj κ a b x₀ := by
  rw [← map_apply _ (by fun_prop)]; rw [partialTraj_map_frestrictLe₂]

/--
lemma `partialTraj_comp_partialTraj'` / 引理 `partialTraj_comp_partialTraj'`

English:
lemma partialTraj_comp_partialTraj'
  given: (c : Nat) (hab : a <= b)
  proof: by
  obtain hbc | hcb := le_total b c
  · rw [partialTraj_comp_partialTraj hab hbc]
  · rw [partialTraj_le hcb, deterministic_comp_eq_map, partialTraj_map_frestrictLe₂]

中文:
引理 partialTraj_comp_partialTraj'
  条件: (c : 自然数) (hab : a <= b)
  证明: by
  obtain hbc | hcb := le_total b c
  · rw [partialTraj_comp_partialTraj hab hbc]
  · rw [partialTraj_le hcb, deterministic_comp_eq_map, partialTraj_map_frestrictLe₂]

Depends on / 依赖: deterministic_comp_eq_map, le_total, partialTraj_comp_partialTraj, partialTraj_le
-/
lemma partialTraj_comp_partialTraj' (c : Nat) (hab : a <= b) :
    partialTraj κ b c ∘ₖ partialTraj κ a b = partialTraj κ a c := by
  obtain hbc | hcb := le_total b c
  · rw [partialTraj_comp_partialTraj hab hbc]
  · rw [partialTraj_le hcb, deterministic_comp_eq_map, partialTraj_map_frestrictLe₂]

/--
lemma `partialTraj_comp_partialTraj''` / 引理 `partialTraj_comp_partialTraj''`

English:
lemma partialTraj_comp_partialTraj''
  given: {b c : Nat} (hcb : c <= b)
  proof: by
  rw [partialTraj_le hcb]; rw [deterministic_comp_eq_map]; rw [partialTraj_map_frestrictLe₂]

中文:
引理 partialTraj_comp_partialTraj''
  条件: {b c : 自然数} (hcb : c <= b)
  证明: by
  rw [partialTraj_le hcb]; rw [deterministic_comp_eq_map]; rw [partialTraj_map_frestrictLe₂]

Depends on / 依赖: deterministic_comp_eq_map, partialTraj_le
-/
lemma partialTraj_comp_partialTraj'' {b c : Nat} (hcb : c <= b) :
    partialTraj κ b c ∘ₖ partialTraj κ a b = partialTraj κ a c := by
  rw [partialTraj_le hcb]; rw [deterministic_comp_eq_map]; rw [partialTraj_map_frestrictLe₂]

end Basic

section lmarginalPartialTraj

/-! ### Integrating against `partialTraj` -/

variable (κ)

/--
Definition of `lmarginalPartialTraj` / `lmarginalPartialTraj` 的定义

English:
definition lmarginalPartialTraj
  signature: (a b : Nat) (f : (Π n, X n) -> Real>=0∞) (x₀ : Π n, X n)
  body: ∫⁻ z : (i : Iic b) -> X i, f (updateFinset x₀ _ z) ∂(partialTraj κ a b (frestrictLe a x₀))

中文:
定义 lmarginalPartialTraj
  签名: (a b : 自然数) (f : (Π n, X n) -> 实数>=0∞) (x₀ : Π n, X n)
  定义体: ∫⁻ z : (i : Iic b) -> X i, f (updateFinset x₀ _ z) ∂(partialTraj κ a b (frestrictLe a x₀))

Depends on / 依赖: frestrictLe, partialTraj, updateFinset
-/
noncomputable def lmarginalPartialTraj (a b : Nat) (f : (Π n, X n) -> Real>=0∞) (x₀ : Π n, X n) : Real>=0∞ :=
  ∫⁻ z : (i : Iic b) -> X i, f (updateFinset x₀ _ z) ∂(partialTraj κ a b (frestrictLe a x₀))

/--
lemma `lmarginalPartialTraj_le` / 引理 `lmarginalPartialTraj_le`

English:
lemma lmarginalPartialTraj_le
  given: (hba : b <= a) {f : (Π n, X n) -> Real>=0∞} (mf : Measurable f)
  proof: by
  ext x₀
  rw [lmarginalPartialTraj]; rw [partialTraj_le hba]; rw [Kernel.lintegral_deterministic']
  · congr with i
    simp [updateFinset]
  · exact mf.comp measurable_updateFinset

中文:
引理 lmarginalPartialTraj_le
  条件: (hba : b <= a) {f : (Π n, X n) -> 实数>=0∞} (mf : 可测 f)
  证明: by
  ext x₀
  rw [lmarginalPartialTraj]; rw [partialTraj_le hba]; rw [Kernel.lintegral_deterministic']
  · congr with i
    simp [updateFinset]
  · exact mf.comp measurable_updateFinset

Depends on / 依赖: Kernel, Kernel.lintegral_deterministic, lintegral_deterministic, lmarginalPartialTraj, measurable_updateFinset, mf.comp, partialTraj_le, updateFinset
-/
lemma lmarginalPartialTraj_le (hba : b <= a) {f : (Π n, X n) -> Real>=0∞} (mf : Measurable f) :
    lmarginalPartialTraj κ a b f = f := by
  ext x₀
  rw [lmarginalPartialTraj]; rw [partialTraj_le hba]; rw [Kernel.lintegral_deterministic']
  · congr with i
    simp [updateFinset]
  · exact mf.comp measurable_updateFinset

variable {κ}

/--
lemma `lmarginalPartialTraj_mono` / 引理 `lmarginalPartialTraj_mono`

English:
lemma lmarginalPartialTraj_mono
  given: (a b : Nat) {f g : (Π n, X n) -> Real>=0∞} (hfg : f <= g) (x₀ : Π n, X n)
  proof: lintegral_mono fun _ => hfg _

中文:
引理 lmarginalPartialTraj_mono
  条件: (a b : 自然数) {f g : (Π n, X n) -> 实数>=0∞} (hfg : f <= g) (x₀ : Π n, X n)
  证明: lintegral_mono fun _ => hfg _

Depends on / 依赖: lintegral_mono
-/
lemma lmarginalPartialTraj_mono (a b : Nat) {f g : (Π n, X n) -> Real>=0∞} (hfg : f <= g) (x₀ : Π n, X n) :
    lmarginalPartialTraj κ a b f x₀ <= lmarginalPartialTraj κ a b g x₀ :=
  lintegral_mono fun _ => hfg _

/--
lemma `lmarginalPartialTraj_eq_lintegral_map` / 引理 `lmarginalPartialTraj_eq_lintegral_map`

English:
lemma lmarginalPartialTraj_eq_lintegral_map
  statement: [forall n, IsSFiniteKernel (κ n)] {f : (Π n, X n) -> Real>=0∞}
  proof: by
  nth_rw 1 [lmarginalPartialTraj, partialTraj_eq_prod, lintegral_map, lintegral_id_prod]
  · congrm ∫⁻ _, f (fun i => ?_) ∂_
    simp only [updateFinset, mem_Iic, IicProdIoc_def,
      frestrictLe_apply, mem_Ioc]
    split_ifs <;> try rfl
    all_goals lia
  all_goals fun_prop

中文:
引理 lmarginalPartialTraj_eq_lintegral_map
  结论: [对任意 n, 是SFiniteKernel (κ n)] {f : (Π n, X n) -> 实数>=0∞}
  证明: by
  nth_rw 1 [lmarginalPartialTraj, partialTraj_eq_prod, lintegral_map, lintegral_id_prod]
  · congrm ∫⁻ _, f (fun i => ?_) ∂_
    simp only [updateFinset, mem_Iic, IicProdIoc_def,
      frestrictLe_apply, mem_Ioc]
    split_ifs <;> try rfl
    all_goals lia
  all_goals fun_prop

Depends on / 依赖: IicProdIoc_def, all_goals, congrm, frestrictLe_apply, fun_prop, lintegral_id_prod, lintegral_map, lmarginalPartialTraj, mem_Iic, mem_Ioc, nth_rw, partialTraj_eq_prod, split_ifs, updateFinset
-/
lemma lmarginalPartialTraj_eq_lintegral_map [forall n, IsSFiniteKernel (κ n)] {f : (Π n, X n) -> Real>=0∞}
    (mf : Measurable f) (x₀ : Π n, X n) :
    lmarginalPartialTraj κ a b f x₀ =
    ∫⁻ x : (Π i : Ioc a b, X i), f (updateFinset x₀ _ x)
      ∂(partialTraj κ a b).map (restrict₂ Ioc_subset_Iic_self) (frestrictLe a x₀) := by
  nth_rw 1 [lmarginalPartialTraj, partialTraj_eq_prod, lintegral_map, lintegral_id_prod]
  · congrm ∫⁻ _, f (fun i => ?_) ∂_
    simp only [updateFinset, mem_Iic, IicProdIoc_def,
      frestrictLe_apply, mem_Ioc]
    split_ifs <;> try rfl
    all_goals lia
  all_goals fun_prop

/--
lemma `lmarginalPartialTraj_succ` / 引理 `lmarginalPartialTraj_succ`

English:
lemma lmarginalPartialTraj_succ
  statement: [forall n, IsSFiniteKernel (κ n)] (a : Nat)
  proof: by
  rw [lmarginalPartialTraj]; rw [partialTraj_succ_self]; rw [lintegral_map]; rw [lintegral_id_prod]; rw [lintegral_map]
  · congrm ∫⁻ x, f (fun i => ?_) ∂_
    simp only [updateFinset, mem_Iic, IicProdIoc_def, frestrictLe_apply, piSingleton,
      MeasurableEquiv.coe_mk, update]
    split_ifs wit

中文:
引理 lmarginalPartialTraj_succ
  结论: [对任意 n, 是SFiniteKernel (κ n)] (a : 自然数)
  证明: by
  rw [lmarginalPartialTraj]; rw [partialTraj_succ_self]; rw [lintegral_map]; rw [lintegral_id_prod]; rw [lintegral_map]
  · congrm ∫⁻ x, f (fun i => ?_) ∂_
    simp only [updateFinset, mem_Iic, IicProdIoc_def, frestrictLe_apply, piSingleton,
      MeasurableEquiv.coe_mk, update]
    split_ifs wit

Depends on / 依赖: IicProdIoc_def, MeasurableEquiv, MeasurableEquiv.coe_mk, all_goals, coe_mk, congrm, frestrictLe_apply, fun_prop, lintegral_id_prod, lintegral_map, lmarginalPartialTraj, mem_Iic, partialTraj_succ_self, piSingleton, split_ifs, update, updateFinset
-/
lemma lmarginalPartialTraj_succ [forall n, IsSFiniteKernel (κ n)] (a : Nat)
    {f : (Π n, X n) -> Real>=0∞} (mf : Measurable f) (x₀ : Π n, X n) :
    lmarginalPartialTraj κ a (a + 1) f x₀ =
      ∫⁻ x : X (a + 1), f (update x₀ _ x) ∂κ a (frestrictLe a x₀) := by
  rw [lmarginalPartialTraj]; rw [partialTraj_succ_self]; rw [lintegral_map]; rw [lintegral_id_prod]; rw [lintegral_map]
  · congrm ∫⁻ x, f (fun i => ?_) ∂_
    simp only [updateFinset, mem_Iic, IicProdIoc_def, frestrictLe_apply, piSingleton,
      MeasurableEquiv.coe_mk, update]
    split_ifs with h1 h2 h3 <;> try rfl
    all_goals lia
  all_goals fun_prop

@[fun_prop]
/--
lemma `measurable_lmarginalPartialTraj` / 引理 `measurable_lmarginalPartialTraj`

English:
lemma measurable_lmarginalPartialTraj
  given: (a b : Nat) {f : (Π n, X n) -> Real>=0∞} (hf : Measurable f)
  proof: by
  unfold lmarginalPartialTraj
  let g : ((i : Iic b) -> X i) × (Π n, X n) -> Real>=0∞ := fun c => f (updateFinset c.2 _ c.1)
  let η : Kernel (Π n, X n) (Π i : Iic b, X i) :=
    (partialTraj κ a b).comap (frestrictLe a) (measurable_frestrictLe _)
  change Measurable fun x₀ => ∫⁻ z : (i : Iic b) 

中文:
引理 measurable_lmarginalPartialTraj
  条件: (a b : 自然数) {f : (Π n, X n) -> 实数>=0∞} (hf : 可测 f)
  证明: by
  unfold lmarginalPartialTraj
  let g : ((i : Iic b) -> X i) × (Π n, X n) -> Real>=0∞ := fun c => f (updateFinset c.2 _ c.1)
  let η : Kernel (Π n, X n) (Π i : Iic b, X i) :=
    (partialTraj κ a b).comap (frestrictLe a) (measurable_frestrictLe _)
  change Measurable fun x₀ => ∫⁻ z : (i : Iic b) 

Depends on / 依赖: Kernel, Measurable, frestrictLe, fun_prop, lmarginalPartialTraj, measurable_frestrictLe, partialTraj, updateFinset
-/
lemma measurable_lmarginalPartialTraj (a b : Nat) {f : (Π n, X n) -> Real>=0∞} (hf : Measurable f) :
    Measurable (lmarginalPartialTraj κ a b f) := by
  unfold lmarginalPartialTraj
  let g : ((i : Iic b) -> X i) × (Π n, X n) -> Real>=0∞ := fun c => f (updateFinset c.2 _ c.1)
  let η : Kernel (Π n, X n) (Π i : Iic b, X i) :=
    (partialTraj κ a b).comap (frestrictLe a) (measurable_frestrictLe _)
  change Measurable fun x₀ => ∫⁻ z : (i : Iic b) -> X i, g (z, x₀) ∂η x₀
  fun_prop

/--
theorem `lmarginalPartialTraj_self` / 定理 `lmarginalPartialTraj_self`

English:
theorem lmarginalPartialTraj_self
  statement: (hab : a <= b) (hbc : b <= c)
  proof: by
  ext x₀
  obtain rfl | hab := eq_or_lt_of_le hab <;> obtain rfl | hbc := eq_or_lt_of_le hbc
  · rw [lmarginalPartialTraj_le κ le_rfl (measurable_lmarginalPartialTraj _ _ hf)]
  · rw [lmarginalPartialTraj_le κ le_rfl (measurable_lmarginalPartialTraj _ _ hf)]
  · rw [lmarginalPartialTraj_le κ le_r

中文:
定理 lmarginalPartialTraj_self
  结论: (hab : a <= b) (hbc : b <= c)
  证明: by
  ext x₀
  obtain rfl | hab := eq_or_lt_of_le hab <;> obtain rfl | hbc := eq_or_lt_of_le hbc
  · rw [lmarginalPartialTraj_le κ le_rfl (measurable_lmarginalPartialTraj _ _ hf)]
  · rw [lmarginalPartialTraj_le κ le_rfl (measurable_lmarginalPartialTraj _ _ hf)]
  · rw [lmarginalPartialTraj_le κ le_r

Depends on / 依赖: Iic_subset_Iic, eq_or_lt_of_le, frestrictLe, hab.le, hbc.le, le_rfl, lintegral_comp, lmarginalPartialTraj, lmarginalPartialTraj_le, measurable_lmarginalPartialTraj, partialTraj_comp_partialTraj, restrict_updateFinset, simp_rw, updateFinset_updateFinset_of_subset
-/
theorem lmarginalPartialTraj_self (hab : a <= b) (hbc : b <= c)
    {f : (Π n, X n) -> Real>=0∞} (hf : Measurable f) :
    lmarginalPartialTraj κ a b (lmarginalPartialTraj κ b c f) = lmarginalPartialTraj κ a c f := by
  ext x₀
  obtain rfl | hab := eq_or_lt_of_le hab <;> obtain rfl | hbc := eq_or_lt_of_le hbc
  · rw [lmarginalPartialTraj_le κ le_rfl (measurable_lmarginalPartialTraj _ _ hf)]
  · rw [lmarginalPartialTraj_le κ le_rfl (measurable_lmarginalPartialTraj _ _ hf)]
  · rw [lmarginalPartialTraj_le κ le_rfl hf]
  simp_rw [lmarginalPartialTraj, frestrictLe, restrict_updateFinset,
    updateFinset_updateFinset_of_subset (Iic_subset_Iic.2 hbc.le)]
  rw [← lintegral_comp]; rw [partialTraj_comp_partialTraj hab.le hbc.le]
  fun_prop

end lmarginalPartialTraj

end ProbabilityTheory.Kernel

open ProbabilityTheory Kernel

namespace DependsOn

/-! ### Lemmas about `lmarginalPartialTraj` and `DependsOn` -/

/--
theorem `lmarginalPartialTraj_of_le` / 定理 `lmarginalPartialTraj_of_le`

English:
theorem lmarginalPartialTraj_of_le
  statement: [forall n, IsMarkovKernel (κ n)] (c : Nat) {f : (Π n, X n) -> Real>=0∞}
  proof: by
  ext x
  rw [lmarginalPartialTraj_eq_lintegral_map mf]
  refine @lintegral_eq_const _ _ _ ?_ _ _ (ae_of_all _ fun y => hf fun i hi => ?_)
  · refine @IsMarkovKernel.isProbabilityMeasure _ _ _ _ _ ?_ _
    exact IsMarkovKernel.map _ (by fun_prop)
  · simp_all only [coe_Iic, Set.mem_Iic, Function.

中文:
定理 lmarginalPartialTraj_of_le
  结论: [对任意 n, 是MarkovKernel (κ n)] (c : 自然数) {f : (Π n, X n) -> 实数>=0∞}
  证明: by
  ext x
  rw [lmarginalPartialTraj_eq_lintegral_map mf]
  refine @lintegral_eq_const _ _ _ ?_ _ _ (ae_of_all _ fun y => hf fun i hi => ?_)
  · refine @IsMarkovKernel.isProbabilityMeasure _ _ _ _ _ ?_ _
    exact IsMarkovKernel.map _ (by fun_prop)
  · simp_all only [coe_Iic, Set.mem_Iic, Function.

Depends on / 依赖: Function, Function.updateFinset, IsMarkovKernel, IsMarkovKernel.isProbabilityMeasure, IsMarkovKernel.map, Set.mem_Iic, ae_of_all, coe_Iic, dite_eq_right_iff, fun_prop, isProbabilityMeasure, lintegral_eq_const, lmarginalPartialTraj_eq_lintegral_map, mem_Iic, mem_Ioc, updateFinset
-/
theorem lmarginalPartialTraj_of_le [forall n, IsMarkovKernel (κ n)] (c : Nat) {f : (Π n, X n) -> Real>=0∞}
    (mf : Measurable f) (hf : DependsOn f (Iic a)) (hab : a <= b) :
    lmarginalPartialTraj κ b c f = f := by
  ext x
  rw [lmarginalPartialTraj_eq_lintegral_map mf]
  refine @lintegral_eq_const _ _ _ ?_ _ _ (ae_of_all _ fun y => hf fun i hi => ?_)
  · refine @IsMarkovKernel.isProbabilityMeasure _ _ _ _ _ ?_ _
    exact IsMarkovKernel.map _ (by fun_prop)
  · simp_all only [coe_Iic, Set.mem_Iic, Function.updateFinset, mem_Ioc, dite_eq_right_iff]
    lia

/--
theorem `lmarginalPartialTraj_const_right` / 定理 `lmarginalPartialTraj_const_right`

English:
theorem lmarginalPartialTraj_const_right
  statement: [forall n, IsMarkovKernel (κ n)] {d : Nat} {f : (Π n, X n) -> Real>=0∞}
  proof: by
  wlog hcd : c <= d generalizing c d
  · rw [this had hac (le_of_not_ge hcd)]
  obtain hbc | hcb := le_total b c
  · rw [← lmarginalPartialTraj_self hbc hcd mf, hf.lmarginalPartialTraj_of_le d mf hac]
  · rw [hf.lmarginalPartialTraj_of_le c mf (hac.trans hcb),
      hf.lmarginalPartialTraj_of_le 

中文:
定理 lmarginalPartialTraj_const_right
  结论: [对任意 n, 是MarkovKernel (κ n)] {d : 自然数} {f : (Π n, X n) -> 实数>=0∞}
  证明: by
  wlog hcd : c <= d generalizing c d
  · rw [this had hac (le_of_not_ge hcd)]
  obtain hbc | hcb := le_total b c
  · rw [← lmarginalPartialTraj_self hbc hcd mf, hf.lmarginalPartialTraj_of_le d mf hac]
  · rw [hf.lmarginalPartialTraj_of_le c mf (hac.trans hcb),
      hf.lmarginalPartialTraj_of_le 

Depends on / 依赖: generalizing, hac.trans, hf.lmarginalPartialTraj_of_le, le_of_not_ge, le_total, lmarginalPartialTraj_of_le, lmarginalPartialTraj_self
-/
theorem lmarginalPartialTraj_const_right [forall n, IsMarkovKernel (κ n)] {d : Nat} {f : (Π n, X n) -> Real>=0∞}
    (mf : Measurable f) (hf : DependsOn f (Iic a)) (hac : a <= c) (had : a <= d) :
    lmarginalPartialTraj κ b c f = lmarginalPartialTraj κ b d f := by
  wlog hcd : c <= d generalizing c d
  · rw [this had hac (le_of_not_ge hcd)]
  obtain hbc | hcb := le_total b c
  · rw [← lmarginalPartialTraj_self hbc hcd mf, hf.lmarginalPartialTraj_of_le d mf hac]
  · rw [hf.lmarginalPartialTraj_of_le c mf (hac.trans hcb),
      hf.lmarginalPartialTraj_of_le d mf (hac.trans hcb)]

/--
theorem `dependsOn_lmarginalPartialTraj` / 定理 `dependsOn_lmarginalPartialTraj`

English:
theorem dependsOn_lmarginalPartialTraj
  statement: [forall n, IsSFiniteKernel (κ n)] (a : Nat) {f : (Π n, X n) -> Real>=0∞}
  proof: by
  intro x y hxy
  obtain hba | hab := le_total b a
  · rw [Kernel.lmarginalPartialTraj_le κ hba mf]
    exact hf fun i hi => hxy i (Iic_subset_Iic.2 hba hi)
  rw [lmarginalPartialTraj_eq_lintegral_map mf]; rw [lmarginalPartialTraj_eq_lintegral_map mf]
  congrm ∫⁻ z : _, ?_ ∂(partialTraj κ a b).ma

中文:
定理 dependsOn_lmarginalPartialTraj
  结论: [对任意 n, 是SFiniteKernel (κ n)] (a : 自然数) {f : (Π n, X n) -> 实数>=0∞}
  证明: by
  intro x y hxy
  obtain hba | hab := le_total b a
  · rw [Kernel.lmarginalPartialTraj_le κ hba mf]
    exact hf fun i hi => hxy i (Iic_subset_Iic.2 hba hi)
  rw [lmarginalPartialTraj_eq_lintegral_map mf]; rw [lmarginalPartialTraj_eq_lintegral_map mf]
  congrm ∫⁻ z : _, ?_ ∂(partialTraj κ a b).ma

Depends on / 依赖: Iic_sdiff_Ioc_self_of_le, Iic_subset_Iic, Kernel, Kernel.lmarginalPartialTraj_le, coe_sdiff, congrm, hf.updateFinset, le_total, lmarginalPartialTraj_eq_lintegral_map, lmarginalPartialTraj_le, partialTraj, updateFinset
-/
theorem dependsOn_lmarginalPartialTraj [forall n, IsSFiniteKernel (κ n)] (a : Nat) {f : (Π n, X n) -> Real>=0∞}
    (hf : DependsOn f (Iic b)) (mf : Measurable f) :
    DependsOn (lmarginalPartialTraj κ a b f) (Iic a) := by
  intro x y hxy
  obtain hba | hab := le_total b a
  · rw [Kernel.lmarginalPartialTraj_le κ hba mf]
    exact hf fun i hi => hxy i (Iic_subset_Iic.2 hba hi)
  rw [lmarginalPartialTraj_eq_lintegral_map mf]; rw [lmarginalPartialTraj_eq_lintegral_map mf]
  congrm ∫⁻ z : _, ?_ ∂(partialTraj κ a b).map _ (fun i => ?_)
  · exact hxy i.1 i.2
  · refine hf.updateFinset _ ?_
    rwa [← coe_sdiff, Iic_sdiff_Ioc_self_of_le hab]

end DependsOn

end partialTraj
