/-
Copyright (c) 2023 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
module

public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Topology.Separation.Basic

/-!
# Pointwise convergence of indicator functions

In this file, we prove the equivalence of three different ways to phrase that the indicator
functions of sets converge pointwise.

## Main results

For `A` a set, `(Asᵢ)` an indexed collection of sets, under mild conditions, the following are
equivalent:

(a) the indicator functions of `Asᵢ` tend to the indicator function of `A` pointwise;

(b) for every `x`, we eventually have that `x ∈ Asᵢ` holds iff `x ∈ A` holds;

(c) `Tendsto As _ <| Filter.pi (pure <| · ∈ A)`.

The results stating these in the case when the indicators take values in a Fréchet space are:
* `tendsto_indicator_const_iff_forall_eventually` is the equivalence (a) ↔ (b);
* `tendsto_indicator_const_iff_tendsto_pi_pure` is the equivalence (a) ↔ (c).

-/

public section


open Filter Topology

variable {α : Type*} {A : Set α}
variable {β : Type*} [Zero β] [TopologicalSpace β]
variable {ι : Type*} (L : Filter ι) {As : ι -> Set α}

/--
lemma `tendsto_ite` / 引理 `tendsto_ite`

English:
lemma tendsto_ite
  statement: {β : Type*} {p : ι -> Prop} [DecidablePred p] {q : Prop} [Decidable q]
  proof: by
  constructor <;> intro h
  · by_cases hq : q
    · simp only [hq, ite_true] at h
      filter_upwards [mem_map.mp (h hbF)] with i hi
      simp only [Set.preimage_compl, Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff,
        ite_eq_right_iff, not_forall, exists_prop] at hi
      tau

中文:
引理 tendsto_ite
  结论: {β : 类型} {p : ι -> 命题} [DecidablePred p] {q : 命题} [Decidable q]
  证明: by
  constructor <;> intro h
  · by_cases hq : q
    · simp only [hq, ite_true] at h
      filter_upwards [mem_map.mp (h hbF)] with i hi
      simp only [Set.preimage_compl, Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff,
        ite_eq_right_iff, not_forall, exists_prop] at hi
      tau

Depends on / 依赖: Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.preimage_compl, exists_prop, filter_upwards, ite_eq_left_iff, ite_eq_right_iff, ite_false, ite_true, mem_compl_iff, mem_map, mem_map.mp, mem_preimage, mem_singleton_iff, not_forall, preimage_compl
-/
lemma tendsto_ite {β : Type*} {p : ι -> Prop} [DecidablePred p] {q : Prop} [Decidable q]
    {a b : β} {F G : Filter β}
    (haG : {a}ᶜ in G) (hbF : {b}ᶜ in F) (haF : principal {a} <= F) (hbG : principal {b} <= G) :
    Tendsto (fun i => if p i then a else b) L (if q then F else G) ↔ forallᶠ i in L, p i ↔ q := by
  constructor <;> intro h
  · by_cases hq : q
    · simp only [hq, ite_true] at h
      filter_upwards [mem_map.mp (h hbF)] with i hi
      simp only [Set.preimage_compl, Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff,
        ite_eq_right_iff, not_forall, exists_prop] at hi
      tauto
    · simp only [hq, ite_false] at h
      filter_upwards [mem_map.mp (h haG)] with i hi
      simp only [Set.preimage_compl, Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff,
        ite_eq_left_iff, not_forall, exists_prop] at hi
      tauto
  · have obs : (fun _ => if q then a else b) =ᶠ[L] (fun i => if p i then a else b) := by
      filter_upwards [h] with i hi
      simp only [hi]
    apply Tendsto.congr' obs
    by_cases hq : q
    · simp only [hq, ite_true]
      apply le_trans _ haF
      simp
    · simp only [hq, ite_false]
      apply le_trans _ hbG
      simp only [principal_singleton, le_pure_iff, mem_map, Set.mem_singleton_iff,
        Set.preimage_const_of_mem, univ_mem]

/--
lemma `tendsto_indicator_const_apply_iff_eventually'` / 引理 `tendsto_indicator_const_apply_iff_eventually'`

English:
lemma tendsto_indicator_const_apply_iff_eventually'
  statement: (b : β)
  proof: by
  classical
  have heart := @tendsto_ite ι L β (fun i => x in As i) _ (x in A) _ b 0 (𝓝 b) (𝓝 (0 : β))
                nhds_o nhds_b ?_ ?_
  · convert! heart
    by_cases hxA : x in A <;> simp [hxA]
  · simp only [principal_singleton, le_def, mem_pure]
    exact fun s s_nhds => mem_of_mem_nhds s_

中文:
引理 tendsto_indicator_const_apply_iff_eventually'
  结论: (b : β)
  证明: by
  classical
  have heart := @tendsto_ite ι L β (fun i => x in As i) _ (x in A) _ b 0 (𝓝 b) (𝓝 (0 : β))
                nhds_o nhds_b ?_ ?_
  · convert! heart
    by_cases hxA : x in A <;> simp [hxA]
  · simp only [principal_singleton, le_def, mem_pure]
    exact fun s s_nhds => mem_of_mem_nhds s_

Depends on / 依赖: classical, convert, le_def, mem_of_mem_nhds, mem_pure, nhds_b, nhds_o, principal_singleton, s_nhds, tendsto_ite
-/
lemma tendsto_indicator_const_apply_iff_eventually' (b : β)
    (nhds_b : {0}ᶜ in 𝓝 b) (nhds_o : {b}ᶜ in 𝓝 0) (x : α) :
    Tendsto (fun i => (As i).indicator (fun (_ : α) => b) x) L (𝓝 (A.indicator (fun (_ : α) => b) x))
      ↔ forallᶠ i in L, (x in As i ↔ x in A) := by
  classical
  have heart := @tendsto_ite ι L β (fun i => x in As i) _ (x in A) _ b 0 (𝓝 b) (𝓝 (0 : β))
                nhds_o nhds_b ?_ ?_
  · convert! heart
    by_cases hxA : x in A <;> simp [hxA]
  · simp only [principal_singleton, le_def, mem_pure]
    exact fun s s_nhds => mem_of_mem_nhds s_nhds
  · simp only [principal_singleton, le_def, mem_pure]
    exact fun s s_nhds => mem_of_mem_nhds s_nhds

/--
lemma `tendsto_indicator_const_iff_forall_eventually'` / 引理 `tendsto_indicator_const_iff_forall_eventually'`

English:
lemma tendsto_indicator_const_iff_forall_eventually'
  proof: by
  simp_rw [tendsto_pi_nhds]
  apply forall_congr'
  exact tendsto_indicator_const_apply_iff_eventually' L b nhds_b nhds_o

中文:
引理 tendsto_indicator_const_iff_forall_eventually'
  证明: by
  simp_rw [tendsto_pi_nhds]
  apply forall_congr'
  exact tendsto_indicator_const_apply_iff_eventually' L b nhds_b nhds_o

Depends on / 依赖: forall_congr, nhds_b, nhds_o, simp_rw, tendsto_indicator_const_apply_iff_eventually, tendsto_pi_nhds
-/
lemma tendsto_indicator_const_iff_forall_eventually'
    (b : β) (nhds_b : {0}ᶜ in 𝓝 b) (nhds_o : {b}ᶜ in 𝓝 0) :
    Tendsto (fun i => (As i).indicator (fun (_ : α) => b)) L (𝓝 (A.indicator (fun (_ : α) => b)))
      ↔ forall x, forallᶠ i in L, (x in As i ↔ x in A) := by
  simp_rw [tendsto_pi_nhds]
  apply forall_congr'
  exact tendsto_indicator_const_apply_iff_eventually' L b nhds_b nhds_o

/--
lemma `tendsto_indicator_const_apply_iff_eventually` / 引理 `tendsto_indicator_const_apply_iff_eventually`

English:
lemma tendsto_indicator_const_apply_iff_eventually
  statement: [T1Space β] (b : β) [NeZero b]
  proof: by
  apply tendsto_indicator_const_apply_iff_eventually' _ b
  · simp only [compl_singleton_mem_nhds_iff, ne_eq, NeZero.ne, not_false_eq_true]
  · simp only [compl_singleton_mem_nhds_iff, ne_eq, (NeZero.ne b).symm, not_false_eq_true]

中文:
引理 tendsto_indicator_const_apply_iff_eventually
  结论: [T1Space β] (b : β) [NeZero b]
  证明: by
  apply tendsto_indicator_const_apply_iff_eventually' _ b
  · simp only [compl_singleton_mem_nhds_iff, ne_eq, NeZero.ne, not_false_eq_true]
  · simp only [compl_singleton_mem_nhds_iff, ne_eq, (NeZero.ne b).symm, not_false_eq_true]
-/
@[simp] lemma tendsto_indicator_const_apply_iff_eventually [T1Space β] (b : β) [NeZero b]
    (x : α) :
    Tendsto (fun i => (As i).indicator (fun (_ : α) => b) x) L (𝓝 (A.indicator (fun (_ : α) => b) x))
      ↔ forallᶠ i in L, (x in As i ↔ x in A) := by
  apply tendsto_indicator_const_apply_iff_eventually' _ b
  · simp only [compl_singleton_mem_nhds_iff, ne_eq, NeZero.ne, not_false_eq_true]
  · simp only [compl_singleton_mem_nhds_iff, ne_eq, (NeZero.ne b).symm, not_false_eq_true]

/--
lemma `tendsto_indicator_const_iff_forall_eventually` / 引理 `tendsto_indicator_const_iff_forall_eventually`

English:
lemma tendsto_indicator_const_iff_forall_eventually
  given: [T1Space β] (b : β) [NeZero b]
  proof: by
  apply tendsto_indicator_const_iff_forall_eventually' _ b
  · simp only [compl_singleton_mem_nhds_iff, ne_eq, NeZero.ne, not_false_eq_true]
  · simp only [compl_singleton_mem_nhds_iff, ne_eq, (NeZero.ne b).symm, not_false_eq_true]

中文:
引理 tendsto_indicator_const_iff_forall_eventually
  条件: [T1Space β] (b : β) [NeZero b]
  证明: by
  apply tendsto_indicator_const_iff_forall_eventually' _ b
  · simp only [compl_singleton_mem_nhds_iff, ne_eq, NeZero.ne, not_false_eq_true]
  · simp only [compl_singleton_mem_nhds_iff, ne_eq, (NeZero.ne b).symm, not_false_eq_true]
-/
@[simp] lemma tendsto_indicator_const_iff_forall_eventually [T1Space β] (b : β) [NeZero b] :
    Tendsto (fun i => (As i).indicator (fun (_ : α) => b)) L (𝓝 (A.indicator (fun (_ : α) => b)))
      ↔ forall x, forallᶠ i in L, (x in As i ↔ x in A) := by
  apply tendsto_indicator_const_iff_forall_eventually' _ b
  · simp only [compl_singleton_mem_nhds_iff, ne_eq, NeZero.ne, not_false_eq_true]
  · simp only [compl_singleton_mem_nhds_iff, ne_eq, (NeZero.ne b).symm, not_false_eq_true]

/--
lemma `tendsto_indicator_const_iff_tendsto_pi_pure'` / 引理 `tendsto_indicator_const_iff_tendsto_pi_pure'`

English:
lemma tendsto_indicator_const_iff_tendsto_pi_pure'
  proof: by
  rw [tendsto_indicator_const_iff_forall_eventually' _ b nhds_b nhds_o]; rw [tendsto_pi]
  simp_rw [tendsto_pure]
  aesop

中文:
引理 tendsto_indicator_const_iff_tendsto_pi_pure'
  证明: by
  rw [tendsto_indicator_const_iff_forall_eventually' _ b nhds_b nhds_o]; rw [tendsto_pi]
  simp_rw [tendsto_pure]
  aesop

Depends on / 依赖: nhds_b, nhds_o, simp_rw, tendsto_indicator_const_iff_forall_eventually, tendsto_pi, tendsto_pure
-/
lemma tendsto_indicator_const_iff_tendsto_pi_pure'
    (b : β) (nhds_b : {0}ᶜ in 𝓝 b) (nhds_o : {b}ᶜ in 𝓝 0) :
    Tendsto (fun i => (As i).indicator (fun (_ : α) => b)) L (𝓝 (A.indicator (fun (_ : α) => b)))
      ↔ (Tendsto (fun i x => x in As i) L <| Filter.pi (pure <| · in A)) := by
  rw [tendsto_indicator_const_iff_forall_eventually' _ b nhds_b nhds_o]; rw [tendsto_pi]
  simp_rw [tendsto_pure]
  aesop

/--
lemma `tendsto_indicator_const_iff_tendsto_pi_pure` / 引理 `tendsto_indicator_const_iff_tendsto_pi_pure`

English:
lemma tendsto_indicator_const_iff_tendsto_pi_pure
  given: [T1Space β] (b : β) [NeZero b]
  proof: by
  rw [tendsto_indicator_const_iff_forall_eventually _ b]; rw [tendsto_pi]
  simp_rw [tendsto_pure]
  aesop

中文:
引理 tendsto_indicator_const_iff_tendsto_pi_pure
  条件: [T1Space β] (b : β) [NeZero b]
  证明: by
  rw [tendsto_indicator_const_iff_forall_eventually _ b]; rw [tendsto_pi]
  simp_rw [tendsto_pure]
  aesop

Depends on / 依赖: simp_rw, tendsto_indicator_const_iff_forall_eventually, tendsto_pi, tendsto_pure
-/
lemma tendsto_indicator_const_iff_tendsto_pi_pure [T1Space β] (b : β) [NeZero b] :
    Tendsto (fun i => (As i).indicator (fun (_ : α) => b)) L (𝓝 (A.indicator (fun (_ : α) => b)))
      ↔ (Tendsto (fun i x => x in As i) L <| Filter.pi (pure <| · in A)) := by
  rw [tendsto_indicator_const_iff_forall_eventually _ b]; rw [tendsto_pi]
  simp_rw [tendsto_pure]
  aesop
