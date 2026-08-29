/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Sequence of measurable functions associated to a sequence of a.e.-measurable functions

We define here tools to prove statements about limits (infi, supr...) of sequences of
`AEMeasurable` functions.
Given a sequence of a.e.-measurable functions `f : ι → α → β` with hypothesis
`hf : ∀ i, AEMeasurable (f i) μ`, and a pointwise property `p : α → (ι → β) → Prop` such that we
have `hp : ∀ᵐ x ∂μ, p x (fun n ↦ f n x)`, we define a sequence of measurable functions `aeSeq hf p`
and a measurable set `aeSeqSet hf p`, such that
* `μ (aeSeqSet hf p)ᶜ = 0`
* `x ∈ aeSeqSet hf p → ∀ i : ι, aeSeq hf hp i x = f i x`
* `x ∈ aeSeqSet hf p → p x (fun n ↦ f n x)`
-/

@[expose] public noncomputable section


open MeasureTheory

variable {ι : Sort*} {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] {f : ι -> α -> β}
  {μ : Measure α} {p : α -> (ι -> β) -> Prop}

/--
Definition of `aeSeqSet` / `aeSeqSet` 的定义

English:
definition aeSeqSet
  signature: (hf : forall i, AEMeasurable (f i) μ) (p : α -> (ι -> β) -> Prop)
  body: (toMeasurable μ { x | (forall i, f i x = (hf i).mk (f i) x) ∧ p x fun n => f n x }ᶜ)ᶜ

中文:
定义 aeSeqSet
  签名: (hf : 对任意 i, 几乎处处可测 (f i) μ) (p : α -> (ι -> β) -> 命题)
  定义体: (toMeasurable μ { x | (forall i, f i x = (hf i).mk (f i) x) ∧ p x fun n => f n x }ᶜ)ᶜ

Depends on / 依赖: toMeasurable
-/
def aeSeqSet (hf : forall i, AEMeasurable (f i) μ) (p : α -> (ι -> β) -> Prop) : Set α :=
  (toMeasurable μ { x | (forall i, f i x = (hf i).mk (f i) x) ∧ p x fun n => f n x }ᶜ)ᶜ

open scoped Classical in
/--
Definition of `aeSeq` / `aeSeq` 的定义

English:
definition aeSeq
  signature: (hf : forall i, AEMeasurable (f i) μ) (p : α -> (ι -> β) -> Prop)
  body: fun i x => ite (x in aeSeqSet hf p) ((hf i).mk (f i) x) (⟨f i x⟩ : Nonempty β).some

中文:
定义 aeSeq
  签名: (hf : 对任意 i, 几乎处处可测 (f i) μ) (p : α -> (ι -> β) -> 命题)
  定义体: fun i x => ite (x in aeSeqSet hf p) ((hf i).mk (f i) x) (⟨f i x⟩ : Nonempty β).some

Depends on / 依赖: Nonempty, aeSeqSet
-/
def aeSeq (hf : forall i, AEMeasurable (f i) μ) (p : α -> (ι -> β) -> Prop) : ι -> α -> β :=
  fun i x => ite (x in aeSeqSet hf p) ((hf i).mk (f i) x) (⟨f i x⟩ : Nonempty β).some

namespace aeSeq

section MemAESeqSet

/--
theorem `mk_eq_fun_of_mem_aeSeqSet` / 定理 `mk_eq_fun_of_mem_aeSeqSet`

English:
theorem mk_eq_fun_of_mem_aeSeqSet
  statement: (hf : forall i, AEMeasurable (f i) μ) {x : α} (hx : x in aeSeqSet hf p)
  proof: haveI h_ss : aeSeqSet hf p subseteq { x | forall i, f i x = (hf i).mk (f i) x } := by
    rw [aeSeqSet]; rw [← compl_compl { x | forall i]; rw [f i x = (hf i).mk (f i) x }]; rw [Set.compl_subset_compl]
    refine Set.Subset.trans (Set.compl_subset_compl.mpr fun x h => ?_) (subset_toMeasurable _ _)
    exact h.1
  (h_ss hx i).symm

中文:
定理 mk_eq_fun_of_mem_aeSeqSet
  结论: (hf : 对任意 i, 几乎处处可测 (f i) μ) {x : α} (hx : x in aeSeqSet hf p)
  证明: haveI h_ss : aeSeqSet hf p subseteq { x | forall i, f i x = (hf i).mk (f i) x } := by
    rw [aeSeqSet]; rw [← compl_compl { x | forall i]; rw [f i x = (hf i).mk (f i) x }]; rw [Set.compl_subset_compl]
    refine Set.Subset.trans (Set.compl_subset_compl.mpr fun x h => ?_) (subset_toMeasurable _ _)
    exact h.1
  (h_ss hx i).symm

Depends on / 依赖: Set.Subset.trans, Set.compl_subset_compl, Set.compl_subset_compl.mpr, Subset, aeSeqSet, compl_compl, compl_subset_compl, h_ss, subset_toMeasurable, subseteq
-/
theorem mk_eq_fun_of_mem_aeSeqSet (hf : forall i, AEMeasurable (f i) μ) {x : α} (hx : x in aeSeqSet hf p)
    (i : ι) : (hf i).mk (f i) x = f i x :=
  haveI h_ss : aeSeqSet hf p subseteq { x | forall i, f i x = (hf i).mk (f i) x } := by
    rw [aeSeqSet]; rw [← compl_compl { x | forall i]; rw [f i x = (hf i).mk (f i) x }]; rw [Set.compl_subset_compl]
    refine Set.Subset.trans (Set.compl_subset_compl.mpr fun x h => ?_) (subset_toMeasurable _ _)
    exact h.1
  (h_ss hx i).symm

/--
theorem `aeSeq_eq_mk_of_mem_aeSeqSet` / 定理 `aeSeq_eq_mk_of_mem_aeSeqSet`

English:
theorem aeSeq_eq_mk_of_mem_aeSeqSet
  statement: (hf : forall i, AEMeasurable (f i) μ) {x : α}
  proof: by
  simp only [aeSeq, hx, if_true]

中文:
定理 aeSeq_eq_mk_of_mem_aeSeqSet
  结论: (hf : 对任意 i, 几乎处处可测 (f i) μ) {x : α}
  证明: by
  simp only [aeSeq, hx, if_true]

Depends on / 依赖: if_true, isArithmetic_iff_finiteIndex, isArithmetic_iff_finiteIndex.mpr
-/
theorem aeSeq_eq_mk_of_mem_aeSeqSet (hf : forall i, AEMeasurable (f i) μ) {x : α}
    (hx : x in aeSeqSet hf p) (i : ι) : aeSeq hf p i x = (hf i).mk (f i) x := by
  simp only [aeSeq, hx, if_true]

/--
theorem `aeSeq_eq_fun_of_mem_aeSeqSet` / 定理 `aeSeq_eq_fun_of_mem_aeSeqSet`

English:
theorem aeSeq_eq_fun_of_mem_aeSeqSet
  statement: (hf : forall i, AEMeasurable (f i) μ) {x : α}
  proof: by
  simp only [aeSeq_eq_mk_of_mem_aeSeqSet hf hx i, mk_eq_fun_of_mem_aeSeqSet hf hx i]

中文:
定理 aeSeq_eq_fun_of_mem_aeSeqSet
  结论: (hf : 对任意 i, 几乎处处可测 (f i) μ) {x : α}
  证明: by
  simp only [aeSeq_eq_mk_of_mem_aeSeqSet hf hx i, mk_eq_fun_of_mem_aeSeqSet hf hx i]

Depends on / 依赖: aeSeq_eq_mk_of_mem_aeSeqSet, mk_eq_fun_of_mem_aeSeqSet
-/
theorem aeSeq_eq_fun_of_mem_aeSeqSet (hf : forall i, AEMeasurable (f i) μ) {x : α}
    (hx : x in aeSeqSet hf p) (i : ι) : aeSeq hf p i x = f i x := by
  simp only [aeSeq_eq_mk_of_mem_aeSeqSet hf hx i, mk_eq_fun_of_mem_aeSeqSet hf hx i]

/--
theorem `prop_of_mem_aeSeqSet` / 定理 `prop_of_mem_aeSeqSet`

English:
theorem prop_of_mem_aeSeqSet
  given: (hf : forall i, AEMeasurable (f i) μ) {x : α} (hx : x in aeSeqSet hf p)
  proof: by
  simp only [aeSeq, hx, if_true]
  rw [funext fun n => mk_eq_fun_of_mem_aeSeqSet hf hx n]
  have h_ss : aeSeqSet hf p subseteq { x | p x fun n => f n x } := by
    rw [← compl_compl { x | p x fun n => f n x }]; rw [aeSeqSet]; rw [Set.compl_subset_compl]
    refine Set.Subset.trans (Set.compl_subset_compl.mpr ?_) (subset_toMeasurable _ _)
    exact fun x hx => hx.2
  have hx' := Set.mem_of_subset_of_mem h_ss hx
  exact hx'

中文:
定理 prop_of_mem_aeSeqSet
  条件: (hf : 对任意 i, 几乎处处可测 (f i) μ) {x : α} (hx : x in aeSeqSet hf p)
  证明: by
  simp only [aeSeq, hx, if_true]
  rw [funext fun n => mk_eq_fun_of_mem_aeSeqSet hf hx n]
  have h_ss : aeSeqSet hf p subseteq { x | p x fun n => f n x } := by
    rw [← compl_compl { x | p x fun n => f n x }]; rw [aeSeqSet]; rw [Set.compl_subset_compl]
    refine Set.Subset.trans (Set.compl_subset_compl.mpr ?_) (subset_toMeasurable _ _)
    exact fun x hx => hx.2
  have hx' := Set.mem_of_subset_of_mem h_ss hx
  exact hx'

Depends on / 依赖: GeneralLinearGroup, IsArithmetic, Matrix, Matrix.GeneralLinearGroup.det, Matrix.SpecialLinearGroup.det_mapGL, Nat.ne_zero_of_lt, Set.Subset.trans, Set.compl_subset_compl, Set.compl_subset_compl.mpr, Set.mem_of_subset_of_mem, SpecialLinearGroup, Subgroup, Subgroup.IsArithmetic.is_commensurable, Subgroup.exists_pow_mem_of_relIndex_ne_zero, Subset, abs_pow, abs_pow_eq_one, aeSeqSet, compl_compl, compl_subset_compl
-/
theorem prop_of_mem_aeSeqSet (hf : forall i, AEMeasurable (f i) μ) {x : α} (hx : x in aeSeqSet hf p) :
    p x fun n => aeSeq hf p n x := by
  simp only [aeSeq, hx, if_true]
  rw [funext fun n => mk_eq_fun_of_mem_aeSeqSet hf hx n]
  have h_ss : aeSeqSet hf p subseteq { x | p x fun n => f n x } := by
    rw [← compl_compl { x | p x fun n => f n x }]; rw [aeSeqSet]; rw [Set.compl_subset_compl]
    refine Set.Subset.trans (Set.compl_subset_compl.mpr ?_) (subset_toMeasurable _ _)
    exact fun x hx => hx.2
  have hx' := Set.mem_of_subset_of_mem h_ss hx
  exact hx'

/--
theorem `fun_prop_of_mem_aeSeqSet` / 定理 `fun_prop_of_mem_aeSeqSet`

English:
theorem fun_prop_of_mem_aeSeqSet
  given: (hf : forall i, AEMeasurable (f i) μ) {x : α} (hx : x in aeSeqSet hf p)
  proof: by
  have h_eq : (fun n => f n x) = fun n => aeSeq hf p n x :=
    funext fun n => (aeSeq_eq_fun_of_mem_aeSeqSet hf hx n).symm
  rw [h_eq]
  exact prop_of_mem_aeSeqSet hf hx

中文:
定理 fun_prop_of_mem_aeSeqSet
  条件: (hf : 对任意 i, 几乎处处可测 (f i) μ) {x : α} (hx : x in aeSeqSet hf p)
  证明: by
  have h_eq : (fun n => f n x) = fun n => aeSeq hf p n x :=
    funext fun n => (aeSeq_eq_fun_of_mem_aeSeqSet hf hx n).symm
  rw [h_eq]
  exact prop_of_mem_aeSeqSet hf hx

Depends on / 依赖: aeSeq_eq_fun_of_mem_aeSeqSet, h_eq, prop_of_mem_aeSeqSet
-/
theorem fun_prop_of_mem_aeSeqSet (hf : forall i, AEMeasurable (f i) μ) {x : α} (hx : x in aeSeqSet hf p) :
    p x fun n => f n x := by
  have h_eq : (fun n => f n x) = fun n => aeSeq hf p n x :=
    funext fun n => (aeSeq_eq_fun_of_mem_aeSeqSet hf hx n).symm
  rw [h_eq]
  exact prop_of_mem_aeSeqSet hf hx

end MemAESeqSet

/--
theorem `aeSeqSet_measurableSet` / 定理 `aeSeqSet_measurableSet`

English:
theorem aeSeqSet_measurableSet
  given: {hf : forall i, AEMeasurable (f i) μ}
  statement: MeasurableSet (aeSeqSet hf p)
  proof: (measurableSet_toMeasurable _ _).compl

中文:
定理 aeSeqSet_measurableSet
  条件: {hf : 对任意 i, 几乎处处可测 (f i) μ}
  结论: 可测集 (aeSeqSet hf p)
  证明: (measurableSet_toMeasurable _ _).compl

Depends on / 依赖: measurableSet_toMeasurable
-/
theorem aeSeqSet_measurableSet {hf : forall i, AEMeasurable (f i) μ} : MeasurableSet (aeSeqSet hf p) :=
  (measurableSet_toMeasurable _ _).compl

/--
theorem `measurable` / 定理 `measurable`

English:
theorem measurable
  given: (hf : forall i, AEMeasurable (f i) μ) (p : α -> (ι -> β) -> Prop) (i : ι)
  proof: Measurable.ite aeSeqSet_measurableSet (hf i).measurable_mk measurable_const' fun _ _ => rfl

中文:
定理 measurable
  条件: (hf : 对任意 i, 几乎处处可测 (f i) μ) (p : α -> (ι -> β) -> 命题) (i : ι)
  证明: Measurable.ite aeSeqSet_measurableSet (hf i).measurable_mk measurable_const' fun _ _ => rfl

Depends on / 依赖: Measurable, Measurable.ite, aeSeqSet_measurableSet, measurable_const, measurable_mk
-/
theorem measurable (hf : forall i, AEMeasurable (f i) μ) (p : α -> (ι -> β) -> Prop) (i : ι) :
    Measurable (aeSeq hf p i) :=
Measurable.ite aeSeqSet_measurableSet (hf i).measurable_mk measurable_const' fun _ _ => rfl

/--
theorem `measure_compl_aeSeqSet_eq_zero` / 定理 `measure_compl_aeSeqSet_eq_zero`

English:
theorem measure_compl_aeSeqSet_eq_zero
  statement: [Countable ι] (hf : forall i, AEMeasurable (f i) μ)
  proof: by
  rw [aeSeqSet]; rw [compl_compl]; rw [measure_toMeasurable]
  have hf_eq := fun i => (hf i).ae_eq_mk
  simp_rw [Filter.EventuallyEq, ← ae_all_iff] at hf_eq
  exact Filter.Eventually.and hf_eq hp

中文:
定理 measure_compl_aeSeqSet_eq_zero
  结论: [可数 ι] (hf : 对任意 i, 几乎处处可测 (f i) μ)
  证明: by
  rw [aeSeqSet]; rw [compl_compl]; rw [measure_toMeasurable]
  have hf_eq := fun i => (hf i).ae_eq_mk
  simp_rw [Filter.EventuallyEq, ← ae_all_iff] at hf_eq
  exact Filter.Eventually.and hf_eq hp

Depends on / 依赖: Eventually, EventuallyEq, Filter, Filter.Eventually.and, Filter.EventuallyEq, aeSeqSet, ae_all_iff, ae_eq_mk, compl_compl, hf_eq, measure_toMeasurable, simp_rw
-/
theorem measure_compl_aeSeqSet_eq_zero [Countable ι] (hf : forall i, AEMeasurable (f i) μ)
    (hp : forallᵐ x ∂μ, p x fun n => f n x) : μ (aeSeqSet hf p)ᶜ = 0 := by
  rw [aeSeqSet]; rw [compl_compl]; rw [measure_toMeasurable]
  have hf_eq := fun i => (hf i).ae_eq_mk
  simp_rw [Filter.EventuallyEq, ← ae_all_iff] at hf_eq
  exact Filter.Eventually.and hf_eq hp

/--
theorem `aeSeq_eq_mk_ae` / 定理 `aeSeq_eq_mk_ae`

English:
theorem aeSeq_eq_mk_ae
  statement: [Countable ι] (hf : forall i, AEMeasurable (f i) μ)
  proof: have h_ss : aeSeqSet hf p subseteq { a : α | forall i, aeSeq hf p i a = (hf i).mk (f i) a } := fun x hx i =>
    by simp only [aeSeq, hx, if_true]
  (ae_iff.2 (measure_compl_aeSeqSet_eq_zero hf hp)).mono h_ss

中文:
定理 aeSeq_eq_mk_ae
  结论: [可数 ι] (hf : 对任意 i, 几乎处处可测 (f i) μ)
  证明: have h_ss : aeSeqSet hf p subseteq { a : α | forall i, aeSeq hf p i a = (hf i).mk (f i) a } := fun x hx i =>
    by simp only [aeSeq, hx, if_true]
  (ae_iff.2 (measure_compl_aeSeqSet_eq_zero hf hp)).mono h_ss

Depends on / 依赖: aeSeqSet, ae_iff, h_ss, if_true, measure_compl_aeSeqSet_eq_zero, subseteq
-/
theorem aeSeq_eq_mk_ae [Countable ι] (hf : forall i, AEMeasurable (f i) μ)
    (hp : forallᵐ x ∂μ, p x fun n => f n x) : forallᵐ a : α ∂μ, forall i : ι, aeSeq hf p i a = (hf i).mk (f i) a :=
  have h_ss : aeSeqSet hf p subseteq { a : α | forall i, aeSeq hf p i a = (hf i).mk (f i) a } := fun x hx i =>
    by simp only [aeSeq, hx, if_true]
  (ae_iff.2 (measure_compl_aeSeqSet_eq_zero hf hp)).mono h_ss

/--
theorem `aeSeq_eq_fun_ae` / 定理 `aeSeq_eq_fun_ae`

English:
theorem aeSeq_eq_fun_ae
  statement: [Countable ι] (hf : forall i, AEMeasurable (f i) μ)
  proof: haveI h_ss : { a : α | ¬forall i : ι, aeSeq hf p i a = f i a } subseteq (aeSeqSet hf p)ᶜ := fun _ =>
    mt fun hx i => aeSeq_eq_fun_of_mem_aeSeqSet hf hx i
  measure_mono_null h_ss (measure_compl_aeSeqSet_eq_zero hf hp)

中文:
定理 aeSeq_eq_fun_ae
  结论: [可数 ι] (hf : 对任意 i, 几乎处处可测 (f i) μ)
  证明: haveI h_ss : { a : α | ¬forall i : ι, aeSeq hf p i a = f i a } subseteq (aeSeqSet hf p)ᶜ := fun _ =>
    mt fun hx i => aeSeq_eq_fun_of_mem_aeSeqSet hf hx i
  measure_mono_null h_ss (measure_compl_aeSeqSet_eq_zero hf hp)

Depends on / 依赖: aeSeqSet, aeSeq_eq_fun_of_mem_aeSeqSet, h_ss, measure_compl_aeSeqSet_eq_zero, measure_mono_null, subseteq
-/
theorem aeSeq_eq_fun_ae [Countable ι] (hf : forall i, AEMeasurable (f i) μ)
    (hp : forallᵐ x ∂μ, p x fun n => f n x) : forallᵐ a : α ∂μ, forall i : ι, aeSeq hf p i a = f i a :=
  haveI h_ss : { a : α | ¬forall i : ι, aeSeq hf p i a = f i a } subseteq (aeSeqSet hf p)ᶜ := fun _ =>
    mt fun hx i => aeSeq_eq_fun_of_mem_aeSeqSet hf hx i
  measure_mono_null h_ss (measure_compl_aeSeqSet_eq_zero hf hp)

/--
theorem `aeSeq_n_eq_fun_n_ae` / 定理 `aeSeq_n_eq_fun_n_ae`

English:
theorem aeSeq_n_eq_fun_n_ae
  statement: [Countable ι] (hf : forall i, AEMeasurable (f i) μ)
  proof: ae_all_iff.mp (aeSeq_eq_fun_ae hf hp) n

中文:
定理 aeSeq_n_eq_fun_n_ae
  结论: [可数 ι] (hf : 对任意 i, 几乎处处可测 (f i) μ)
  证明: ae_all_iff.mp (aeSeq_eq_fun_ae hf hp) n

Depends on / 依赖: aeSeq_eq_fun_ae, ae_all_iff, ae_all_iff.mp
-/
theorem aeSeq_n_eq_fun_n_ae [Countable ι] (hf : forall i, AEMeasurable (f i) μ)
    (hp : forallᵐ x ∂μ, p x fun n => f n x) (n : ι) : aeSeq hf p n =ᵐ[μ] f n :=
  ae_all_iff.mp (aeSeq_eq_fun_ae hf hp) n

/--
theorem `iSup` / 定理 `iSup`

English:
theorem iSup
  statement: [SupSet β] [Countable ι] (hf : forall i, AEMeasurable (f i) μ)
  proof: by
  filter_upwards [aeSeq_eq_fun_ae hf hp] with x hx
  simp [iSup_apply, hx]

中文:
定理 iSup
  结论: [上确界集 β] [可数 ι] (hf : 对任意 i, 几乎处处可测 (f i) μ)
  证明: by
  filter_upwards [aeSeq_eq_fun_ae hf hp] with x hx
  simp [iSup_apply, hx]

Depends on / 依赖: aeSeq_eq_fun_ae, filter_upwards, iSup_apply
-/
theorem iSup [SupSet β] [Countable ι] (hf : forall i, AEMeasurable (f i) μ)
    (hp : forallᵐ x ∂μ, p x fun n => f n x) : ⨆ n, aeSeq hf p n =ᵐ[μ] ⨆ n, f n := by
  filter_upwards [aeSeq_eq_fun_ae hf hp] with x hx
  simp [iSup_apply, hx]

/--
theorem `iInf` / 定理 `iInf`

English:
theorem iInf
  statement: [InfSet β] [Countable ι] (hf : forall i, AEMeasurable (f i) μ)
  proof: iSup (β := βᵒᵈ) hf hp

中文:
定理 iInf
  结论: [下确界集 β] [可数 ι] (hf : 对任意 i, 几乎处处可测 (f i) μ)
  证明: iSup (β := βᵒᵈ) hf hp
-/
theorem iInf [InfSet β] [Countable ι] (hf : forall i, AEMeasurable (f i) μ)
    (hp : forallᵐ x ∂μ, p x fun n => f n x) : ⨅ n, aeSeq hf p n =ᵐ[μ] ⨅ n, f n :=
  iSup (β := βᵒᵈ) hf hp

end aeSeq
