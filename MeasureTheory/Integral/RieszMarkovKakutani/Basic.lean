/-
Copyright (c) 2022 Jesse Reimann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Reimann, Kalle Kytölä
-/
module

public import Mathlib.MeasureTheory.Measure.Content
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Mathlib.Topology.PartitionOfUnity

/-!
# Riesz–Markov–Kakutani representation theorem

This file prepares technical definitions and results for the Riesz-Markov-Kakutani representation
theorem on a locally compact T2 space `X`. As a special case, the statements about linear
functionals on bounded continuous functions follows. Actual theorems, depending on the
linearity (`ℝ`, `ℝ≥0` or `ℂ`), are proven in separate files
(`Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/Real.lean`,
`Mathlib/MeasureTheory/Integral/RieszMarkovKakutani/NNReal.lean`...)

To make use of the existing API, the measure is constructed from a content `λ` on the
compact subsets of a locally compact space X, rather than the usual construction of open sets in the
literature.

## References

* [Walter Rudin, Real and Complex Analysis.][Rud87]

-/

@[expose] public section


noncomputable section

open scoped BoundedContinuousFunction NNReal ENNReal
open Set Function TopologicalSpace CompactlySupported CompactlySupportedContinuousMap
  MeasureTheory

variable {X : Type*} [TopologicalSpace X]
variable (Λ : C_c(X, Real>=0) ->ₗ[Real>=0] Real>=0)

/-! ### Construction of the content: -/

section Monotone

/--
lemma `CompactlySupportedContinuousMap.monotone_of_nnreal` / 引理 `CompactlySupportedContinuousMap.monotone_of_nnreal`

English:
lemma CompactlySupportedContinuousMap.monotone_of_nnreal
  statement: Monotone Λ
  proof: by
  intro f₁ f₂ h
  obtain ⟨g, hg⟩ := CompactlySupportedContinuousMap.exists_add_of_le h
  rw [← hg]
  simp

中文:
引理 余mpactlySupportedContinuous映射.monotone_of_nnreal
  结论: 递增 Λ
  证明: by
  intro f₁ f₂ h
  obtain ⟨g, hg⟩ := CompactlySupportedContinuousMap.exists_add_of_le h
  rw [← hg]
  simp

Depends on / 依赖: CompactlySupportedContinuousMap, CompactlySupportedContinuousMap.exists_add_of_le, exists_add_of_le
-/
lemma CompactlySupportedContinuousMap.monotone_of_nnreal : Monotone Λ := by
  intro f₁ f₂ h
  obtain ⟨g, hg⟩ := CompactlySupportedContinuousMap.exists_add_of_le h
  rw [← hg]
  simp

end Monotone

/--
Definition of `rieszContentAux` / `rieszContentAux` 的定义

English:
definition rieszContentAux
  signature: : Compacts X -> Real>=0
  body: fun K =>
  sInf (Λ '' { f : C_c(X, Real>=0) | forall x in K, (1 : Real>=0) <= f x })

中文:
定义 rieszContentAux
  签名: : 余mpacts X -> 实数>=0
  定义体: fun K =>
  sInf (Λ '' { f : C_c(X, Real>=0) | forall x in K, (1 : Real>=0) <= f x })
-/
def rieszContentAux : Compacts X -> Real>=0 := fun K =>
  sInf (Λ '' { f : C_c(X, Real>=0) | forall x in K, (1 : Real>=0) <= f x })

section RieszMonotone

variable [T2Space X] [LocallyCompactSpace X]

/--
theorem `rieszContentAux_image_nonempty` / 定理 `rieszContentAux_image_nonempty`

English:
theorem rieszContentAux_image_nonempty
  given: (K : Compacts X)
  proof: by
  rw [image_nonempty]
  obtain ⟨V, hVcp, hKsubintV⟩ := exists_compact_superset K.2
  have hIsCompact_closure_interior : IsCompact (closure (interior V)) := by
    apply IsCompact.of_isClosed_subset hVcp isClosed_closure
    nth_rw 2 [← closure_eq_iff_isClosed.mpr (IsCompact.isClosed hVcp)]
    ex

中文:
定理 rieszContentAux_image_nonempty
  条件: (K : 余mpacts X)
  证明: by
  rw [image_nonempty]
  obtain ⟨V, hVcp, hKsubintV⟩ := exists_compact_superset K.2
  have hIsCompact_closure_interior : IsCompact (closure (interior V)) := by
    apply IsCompact.of_isClosed_subset hVcp isClosed_closure
    nth_rw 2 [← closure_eq_iff_isClosed.mpr (IsCompact.isClosed hVcp)]
    ex

Depends on / 依赖: IsCompact, IsCompact.isClosed, IsCompact.of_isClosed_subset, closure, closure_eq_iff_isClosed, closure_eq_iff_isClosed.mpr, closure_mono, exists_compact_superset, exists_tsupport_one_of_isOpen_isClosed, hIsCompact_closure_interior, hKsubintV, hfHasCompactSuppo, hfeq1onK, hfinicc, hsuppfsubV, image_nonempty, interior, interior_subset, isClosed, isClosed_closure
-/
theorem rieszContentAux_image_nonempty (K : Compacts X) :
    (Λ '' { f : C_c(X, Real>=0) | forall x in K, (1 : Real>=0) <= f x }).Nonempty := by
  rw [image_nonempty]
  obtain ⟨V, hVcp, hKsubintV⟩ := exists_compact_superset K.2
  have hIsCompact_closure_interior : IsCompact (closure (interior V)) := by
    apply IsCompact.of_isClosed_subset hVcp isClosed_closure
    nth_rw 2 [← closure_eq_iff_isClosed.mpr (IsCompact.isClosed hVcp)]
    exact closure_mono interior_subset
  obtain ⟨f, hsuppfsubV, hfeq1onK, hfinicc⟩ :=
    exists_tsupport_one_of_isOpen_isClosed isOpen_interior hIsCompact_closure_interior
      (IsCompact.isClosed K.2) hKsubintV
  have hfHasCompactSupport : HasCompactSupport f :=
    IsCompact.of_isClosed_subset hVcp (isClosed_tsupport f)
      (Set.Subset.trans hsuppfsubV interior_subset)
  use nnrealPart ⟨f, hfHasCompactSupport⟩
  intro x hx
  apply le_of_eq
  simp only [nnrealPart_apply, CompactlySupportedContinuousMap.coe_mk]
  rw [← Real.toNNReal_one]; rw [Real.toNNReal_eq_toNNReal_iff (zero_le_one' Real) (hfinicc x).1]
  exact hfeq1onK.symm hx

/--
theorem `rieszContentAux_mono` / 定理 `rieszContentAux_mono`

English:
theorem rieszContentAux_mono
  given: {K₁ K₂ : Compacts X} (h : K₁ <= K₂)
  proof: by
  unfold rieszContentAux
  gcongr
  apply rieszContentAux_image_nonempty

中文:
定理 rieszContentAux_mono
  条件: {K₁ K₂ : 余mpacts X} (h : K₁ <= K₂)
  证明: by
  unfold rieszContentAux
  gcongr
  apply rieszContentAux_image_nonempty

Depends on / 依赖: rieszContentAux, rieszContentAux_image_nonempty
-/
theorem rieszContentAux_mono {K₁ K₂ : Compacts X} (h : K₁ <= K₂) :
    rieszContentAux Λ K₁ <= rieszContentAux Λ K₂ := by
  unfold rieszContentAux
  gcongr
  apply rieszContentAux_image_nonempty

end RieszMonotone

section RieszSubadditive

/--
theorem `rieszContentAux_le` / 定理 `rieszContentAux_le`

English:
theorem rieszContentAux_le
  given: {K : Compacts X} {f : C_c(X, Real>=0)} (h : forall x in K, (1 : Real>=0) <= f x)
  proof: csInf_le (OrderBot.bddBelow _) ⟨f, ⟨h, rfl⟩⟩

中文:
定理 rieszContentAux_le
  条件: {K : 余mpacts X} {f : C_c(X, 实数>=0)} (h : 对任意 x in K, (1 : 实数>=0) <= f x)
  证明: csInf_le (OrderBot.bddBelow _) ⟨f, ⟨h, rfl⟩⟩

Depends on / 依赖: OrderBot, OrderBot.bddBelow, bddBelow, csInf_le
-/
theorem rieszContentAux_le {K : Compacts X} {f : C_c(X, Real>=0)} (h : forall x in K, (1 : Real>=0) <= f x) :
    rieszContentAux Λ K <= Λ f :=
  csInf_le (OrderBot.bddBelow _) ⟨f, ⟨h, rfl⟩⟩

variable [T2Space X] [LocallyCompactSpace X]

/--
theorem `exists_lt_rieszContentAux_add_pos` / 定理 `exists_lt_rieszContentAux_add_pos`

English:
theorem exists_lt_rieszContentAux_add_pos
  given: (K : Compacts X) {ε : Real>=0} (εpos : 0 < ε)
  proof: by
  --choose a test function `f` s.t. `Λf = α < λ(K) + ε`
  obtain ⟨α, ⟨⟨f, f_hyp⟩, α_hyp⟩⟩ :=
    exists_lt_of_csInf_lt (rieszContentAux_image_nonempty Λ K)
      (lt_add_of_pos_right (rieszContentAux Λ K) εpos)
  refine ⟨f, f_hyp.left, ?_⟩
  rw [f_hyp.right]
  exact α_hyp

中文:
定理 存在_lt_rieszContentAux_add_pos
  条件: (K : 余mpacts X) {ε : 实数>=0} (εpos : 0 < ε)
  证明: by
  --choose a test function `f` s.t. `Λf = α < λ(K) + ε`
  obtain ⟨α, ⟨⟨f, f_hyp⟩, α_hyp⟩⟩ :=
    exists_lt_of_csInf_lt (rieszContentAux_image_nonempty Λ K)
      (lt_add_of_pos_right (rieszContentAux Λ K) εpos)
  refine ⟨f, f_hyp.left, ?_⟩
  rw [f_hyp.right]
  exact α_hyp
-/
theorem exists_lt_rieszContentAux_add_pos (K : Compacts X) {ε : Real>=0} (εpos : 0 < ε) :
    exists f : C_c(X, Real>=0), (forall x in K, (1 : Real>=0) <= f x) ∧ Λ f < rieszContentAux Λ K + ε := by
  --choose a test function `f` s.t. `Λf = α < λ(K) + ε`
  obtain ⟨α, ⟨⟨f, f_hyp⟩, α_hyp⟩⟩ :=
    exists_lt_of_csInf_lt (rieszContentAux_image_nonempty Λ K)
      (lt_add_of_pos_right (rieszContentAux Λ K) εpos)
  refine ⟨f, f_hyp.left, ?_⟩
  rw [f_hyp.right]
  exact α_hyp

/--
theorem `rieszContentAux_sup_le` / 定理 `rieszContentAux_sup_le`

English:
theorem rieszContentAux_sup_le
  given: (K1 K2 : Compacts X)
  proof: by
  apply _root_.le_of_forall_pos_le_add
  intro ε εpos
  --get test functions s.t. `λ(Ki) ≤ Λfi ≤ λ(Ki) + ε/2, i=1,2`
  obtain ⟨f1, f_test_function_K1⟩ := exists_lt_rieszContentAux_add_pos Λ K1 (half_pos εpos)
  obtain ⟨f2, f_test_function_K2⟩ := exists_lt_rieszContentAux_add_pos Λ K2 (half_pos εp

中文:
定理 rieszContentAux_sup_le
  条件: (K1 K2 : 余mpacts X)
  证明: by
  apply _root_.le_of_forall_pos_le_add
  intro ε εpos
  --get test functions s.t. `λ(Ki) ≤ Λfi ≤ λ(Ki) + ε/2, i=1,2`
  obtain ⟨f1, f_test_function_K1⟩ := exists_lt_rieszContentAux_add_pos Λ K1 (half_pos εpos)
  obtain ⟨f2, f_test_function_K2⟩ := exists_lt_rieszContentAux_add_pos Λ K2 (half_pos εp

Depends on / 依赖: _root_, _root_.le_of_forall_pos_le_add, le_of_forall_pos_le_add
-/
theorem rieszContentAux_sup_le (K1 K2 : Compacts X) :
    rieszContentAux Λ (K1 ⊔ K2) <= rieszContentAux Λ K1 + rieszContentAux Λ K2 := by
  apply _root_.le_of_forall_pos_le_add
  intro ε εpos
  --get test functions s.t. `λ(Ki) ≤ Λfi ≤ λ(Ki) + ε/2, i=1,2`
  obtain ⟨f1, f_test_function_K1⟩ := exists_lt_rieszContentAux_add_pos Λ K1 (half_pos εpos)
  obtain ⟨f2, f_test_function_K2⟩ := exists_lt_rieszContentAux_add_pos Λ K2 (half_pos εpos)
  --let `f := f1 + f2` test function for the content of `K`
  have f_test_function_union : forall x in K1 ⊔ K2, (1 : Real>=0) <= (f1 + f2) x := by
    rintro x (x_in_K1 | x_in_K2)
    · exact le_add_right (f_test_function_K1.left x x_in_K1)
    · exact le_add_left (f_test_function_K2.left x x_in_K2)
  --use that `Λf` is an upper bound for `λ(K1⊔K2)`
  apply (rieszContentAux_le Λ f_test_function_union).trans (le_of_lt _)
  rw [map_add]
  --use that `Λfi` are lower bounds for `λ(Ki) + ε/2`
  apply lt_of_lt_of_le (_root_.add_lt_add f_test_function_K1.right f_test_function_K2.right)
    (le_of_eq _)
  rw [add_assoc]; rw [add_comm (ε / 2)]; rw [add_assoc]; rw [add_halves ε]; rw [add_assoc]

end RieszSubadditive


section PartitionOfUnity

variable [T2Space X] [LocallyCompactSpace X]

/--
lemma `exists_continuous_add_one_of_isCompact_nnreal` / 引理 `exists_continuous_add_one_of_isCompact_nnreal`

English:
lemma exists_continuous_add_one_of_isCompact_nnreal
  proof: by
  set so : Fin 2 -> Set X := fun j => if j = 0 then s₀ᶜ else s₁ᶜ with hso
  have soopen (j : Fin 2) : IsOpen (so j) := by
    fin_cases j
    · simp only [hso, Fin.zero_eta, Fin.isValue, ↓reduceIte, isOpen_compl_iff]
exact IsCompact.isClosed s₀_compact
    · simp only [hso, Fin.isValue, Fin.mk_on

中文:
引理 存在_continuous_add_one_of_isCompact_nnreal
  证明: by
  set so : Fin 2 -> Set X := fun j => if j = 0 then s₀ᶜ else s₁ᶜ with hso
  have soopen (j : Fin 2) : IsOpen (so j) := by
    fin_cases j
    · simp only [hso, Fin.zero_eta, Fin.isValue, ↓reduceIte, isOpen_compl_iff]
exact IsCompact.isClosed s₀_compact
    · simp only [hso, Fin.isValue, Fin.mk_on

Depends on / 依赖: Fin.isValue, Fin.mk_one, Fin.zero_eta, IsCompact, IsCompact.isClosed, IsOpen, fin_cases, isClosed, isOpen_compl_iff, isValue, mem_iUnion, mk_one, one_ne_zero, reduceIte, soopen, subset_compl_iff_disjoint_rig, subseteq, zero_eta
-/
lemma exists_continuous_add_one_of_isCompact_nnreal
    {s₀ s₁ : Set X} {t : Set X} (s₀_compact : IsCompact s₀) (s₁_compact : IsCompact s₁)
    (t_compact : IsCompact t) (disj : Disjoint s₀ s₁) (hst : s₀ union s₁ subseteq t) :
    exists (f₀ f₁ : C_c(X, Real>=0)), EqOn f₀ 1 s₀ ∧ EqOn f₁ 1 s₁ ∧ EqOn (f₀ + f₁) 1 t := by
  set so : Fin 2 -> Set X := fun j => if j = 0 then s₀ᶜ else s₁ᶜ with hso
  have soopen (j : Fin 2) : IsOpen (so j) := by
    fin_cases j
    · simp only [hso, Fin.zero_eta, Fin.isValue, ↓reduceIte, isOpen_compl_iff]
exact IsCompact.isClosed s₀_compact
    · simp only [hso, Fin.isValue, Fin.mk_one, one_ne_zero, ↓reduceIte, isOpen_compl_iff]
exact IsCompact.isClosed s₁_compact
  have hsot : t subseteq ⋃ j, so j := by
    rw [hso]
    simp only [Fin.isValue]
    intro x hx
    rw [mem_iUnion]
    rw [← subset_compl_iff_disjoint_right]; rw [← compl_compl s₀]; rw [compl_subset_iff_union] at disj
    have h : x in s₀ᶜ ∨ x in s₁ᶜ := by
      rw [← mem_union]; rw [disj]
      exact mem_univ _
    apply Or.elim h
    · intro h0
      use 0
      simp only [Fin.isValue, ↓reduceIte]
      exact h0
    · intro h1
      use 1
      simp only [Fin.isValue, one_ne_zero, ↓reduceIte]
      exact h1
  obtain ⟨f, f_supp_in_so, sum_f_one_on_t, f_in_icc, f_hcs⟩ :=
    exists_continuous_sum_one_of_isOpen_isCompact soopen t_compact hsot
  use (nnrealPart (⟨f 1, f_hcs 1⟩ : C_c(X, Real))),
    (nnrealPart (⟨f 0, f_hcs 0⟩ : C_c(X, Real)))
  simp only [Fin.isValue, CompactlySupportedContinuousMap.coe_add]
  have sum_one_x (x : X) (hx : x in t) : (f 0) x + (f 1) x = 1 := by
    simpa only [Finset.sum_apply, Fin.sum_univ_two, Fin.isValue, Pi.one_apply]
      using sum_f_one_on_t hx
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simp only [Fin.isValue, nnrealPart_apply,
      CompactlySupportedContinuousMap.coe_mk, Pi.one_apply, Real.toNNReal_eq_one]
    have : (f 0) x = 0 := by
      rw [← notMem_support]
      have : s₀ subseteq (tsupport (f 0))ᶜ := by
        apply subset_trans _ (compl_subset_compl.mpr (f_supp_in_so 0))
        rw [hso]
        simp only [Fin.isValue, ↓reduceIte, compl_compl, subset_refl]
      apply notMem_of_mem_compl
      exact mem_of_subset_of_mem (subset_trans this (compl_subset_compl_of_subset subset_closure))
        hx
    rw [union_subset_iff] at hst
    rw [← sum_one_x x (mem_of_subset_of_mem hst.1 hx)]; rw [this]
    exact Eq.symm (AddZeroClass.zero_add ((f 1) x))
  · intro x hx
    simp only [Fin.isValue, nnrealPart_apply,
      CompactlySupportedContinuousMap.coe_mk, Pi.one_apply, Real.toNNReal_eq_one]
    have : (f 1) x = 0 := by
      rw [← notMem_support]
      have : s₁ subseteq (tsupport (f 1))ᶜ := by
        apply subset_trans _ (compl_subset_compl.mpr (f_supp_in_so 1))
        rw [hso]
        simp only [Fin.isValue, one_ne_zero, ↓reduceIte, compl_compl, subset_refl]
      apply notMem_of_mem_compl
      exact mem_of_subset_of_mem (subset_trans this (compl_subset_compl_of_subset subset_closure))
        hx
    rw [union_subset_iff] at hst
    rw [← sum_one_x x (mem_of_subset_of_mem hst.2 hx)]; rw [this]
    exact Eq.symm (AddMonoid.add_zero ((f 0) x))
  · intro x hx
    simp only [Fin.isValue, Pi.add_apply, nnrealPart_apply,
      CompactlySupportedContinuousMap.coe_mk, Pi.one_apply]
    rw [Real.toNNReal_add_toNNReal (f_in_icc 1 x).1 (f_in_icc 0 x).1]; rw [add_comm]
    simp only [Fin.isValue, Real.toNNReal_eq_one]
    exact sum_one_x x hx

end PartitionOfUnity

section RieszContentAdditive

variable [T2Space X] [LocallyCompactSpace X]

/--
lemma `rieszContentAux_union` / 引理 `rieszContentAux_union`

English:
lemma rieszContentAux_union
  statement: {K₁ K₂ : TopologicalSpace.Compacts X}
  proof: by
  refine le_antisymm (rieszContentAux_sup_le Λ K₁ K₂) ?_
  refine le_csInf (rieszContentAux_image_nonempty Λ (K₁ ⊔ K₂)) ?_
  intro b ⟨f, ⟨hf, Λf_eq_b⟩⟩
  have hsuppf : forall x in K₁ ⊔ K₂, x in support f := by
    intro x hx
    rw [mem_support]
exact ne_of_gt lt_of_lt_of_le (zero_lt_one' Real>=0

中文:
引理 rieszContentAux_union
  结论: {K₁ K₂ : 拓扑空间.余mpacts X}
  证明: by
  refine le_antisymm (rieszContentAux_sup_le Λ K₁ K₂) ?_
  refine le_csInf (rieszContentAux_image_nonempty Λ (K₁ ⊔ K₂)) ?_
  intro b ⟨f, ⟨hf, Λf_eq_b⟩⟩
  have hsuppf : forall x in K₁ ⊔ K₂, x in support f := by
    intro x hx
    rw [mem_support]
exact ne_of_gt lt_of_lt_of_le (zero_lt_one' Real>=0

Depends on / 依赖: exists_continuous_add_one_of_isCompact_nnreal, hsubsuppf, hsuppf, isCompact, le_antisymm, le_csInf, lt_of_lt_of_le, mem_support, ne_of_gt, rieszContentAux_image_nonempty, rieszContentAux_sup_le, subset_closure, subset_trans, subseteq, sum_g, support, tsupport, zero_lt_one
-/
lemma rieszContentAux_union {K₁ K₂ : TopologicalSpace.Compacts X}
    (disj : Disjoint (K₁ : Set X) K₂) :
    rieszContentAux Λ (K₁ ⊔ K₂) = rieszContentAux Λ K₁ + rieszContentAux Λ K₂ := by
  refine le_antisymm (rieszContentAux_sup_le Λ K₁ K₂) ?_
  refine le_csInf (rieszContentAux_image_nonempty Λ (K₁ ⊔ K₂)) ?_
  intro b ⟨f, ⟨hf, Λf_eq_b⟩⟩
  have hsuppf : forall x in K₁ ⊔ K₂, x in support f := by
    intro x hx
    rw [mem_support]
exact ne_of_gt lt_of_lt_of_le (zero_lt_one' Real>=0) (hf x hx)
  have hsubsuppf : (K₁ : Set X) union (K₂ : Set X) subseteq tsupport f := subset_trans hsuppf subset_closure
  obtain ⟨g₁, g₂, hg₁, hg₂, sum_g⟩ := exists_continuous_add_one_of_isCompact_nnreal K₁.isCompact'
    K₂.isCompact' f.hasCompactSupport'.isCompact disj hsubsuppf
  have f_eq_sum : f = g₁ * f + g₂ * f := by
    ext x
    simp only [CompactlySupportedContinuousMap.coe_add, CompactlySupportedContinuousMap.coe_mul,
      Pi.mul_apply, NNReal.coe_mul,
      Eq.symm (RightDistribClass.right_distrib _ _ _)]
    by_cases h : f x = 0
    · rw [h]
      simp only [NNReal.coe_zero, mul_zero]
    · simp only [CompactlySupportedContinuousMap.coe_add, ContinuousMap.toFun_eq_coe,
        CompactlySupportedContinuousMap.coe_toContinuousMap] at sum_g
      rw [sum_g (mem_of_subset_of_mem subset_closure (mem_support.mpr h))]
      simp only [Pi.one_apply, NNReal.coe_one, one_mul]
  rw [← Λf_eq_b]; rw [f_eq_sum]; rw [map_add]
  have aux₁ : forall x in K₁, 1 <= (g₁ * f) x := by
    intro x x_in_K₁
    simp [hg₁ x_in_K₁, hf x (mem_union_left _ x_in_K₁)]
  have aux₂ : forall x in K₂, 1 <= (g₂ * f) x := by
    intro x x_in_K₂
    simp [hg₂ x_in_K₂, hf x (mem_union_right _ x_in_K₂)]
  exact add_le_add (rieszContentAux_le Λ aux₁) (rieszContentAux_le Λ aux₂)

end RieszContentAdditive

section RieszContentRegular

variable [T2Space X] [LocallyCompactSpace X]

/--
Definition of `rieszContent` / `rieszContent` 的定义

English:
definition rieszContent
  signature: (Λ : C_c(X, Real>=0) ->ₗ[Real>=0] Real>=0)
  body: rieszContentAux Λ
  mono' := fun _ _ => rieszContentAux_mono Λ
  sup_disjoint' := fun _ _ disj _ _ => rieszContentAux_union Λ disj
  sup_le' := rieszContentAux_sup_le Λ

中文:
定义 rieszContent
  签名: (Λ : C_c(X, 实数>=0) ->ₗ[实数>=0] 实数>=0)
  定义体: rieszContentAux Λ
  mono' := fun _ _ => rieszContentAux_mono Λ
  sup_disjoint' := fun _ _ disj _ _ => rieszContentAux_union Λ disj
  sup_le' := rieszContentAux_sup_le Λ

Depends on / 依赖: rieszContentAux
-/
noncomputable def rieszContent (Λ : C_c(X, Real>=0) ->ₗ[Real>=0] Real>=0) : Content X where
  toFun := rieszContentAux Λ
  mono' := fun _ _ => rieszContentAux_mono Λ
  sup_disjoint' := fun _ _ disj _ _ => rieszContentAux_union Λ disj
  sup_le' := rieszContentAux_sup_le Λ

/--
lemma `rieszContent_ne_top` / 引理 `rieszContent_ne_top`

English:
lemma rieszContent_ne_top
  given: {K : Compacts X}
  statement: rieszContent Λ K != ⊤
  proof: by
  simp [rieszContent, ne_eq, not_false_eq_true]

中文:
引理 rieszContent_ne_top
  条件: {K : 余mpacts X}
  结论: rieszContent Λ K != ⊤
  证明: by
  simp [rieszContent, ne_eq, not_false_eq_true]

Depends on / 依赖: ne_eq, not_false_eq_true, rieszContent
-/
lemma rieszContent_ne_top {K : Compacts X} : rieszContent Λ K != ⊤ := by
  simp [rieszContent, ne_eq, not_false_eq_true]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `contentRegular_rieszContent` / 引理 `contentRegular_rieszContent`

English:
lemma contentRegular_rieszContent
  statement: (rieszContent Λ).ContentRegular
  proof: by
  intro K
  simp only [rieszContent, le_antisymm_iff, le_iInf_iff, ENNReal.coe_le_coe, Content.mk_apply]
  refine ⟨fun K' hK' => rieszContentAux_mono Λ (hK'.trans interior_subset), ?_⟩
  rw [iInf_le_iff]
  intro b hb
  rw [rieszContentAux]; rw [ENNReal.le_coe_iff]
  have : b < ⊤ := by
    obtain 

中文:
引理 contentRegular_rieszContent
  结论: (rieszContent Λ).ContentRegular
  证明: by
  intro K
  simp only [rieszContent, le_antisymm_iff, le_iInf_iff, ENNReal.coe_le_coe, Content.mk_apply]
  refine ⟨fun K' hK' => rieszContentAux_mono Λ (hK'.trans interior_subset), ?_⟩
  rw [iInf_le_iff]
  intro b hb
  rw [rieszContentAux]; rw [ENNReal.le_coe_iff]
  have : b < ⊤ := by
    obtain 

Depends on / 依赖: Content, Content.mk_apply, ENNReal, ENNReal.coe_le_coe, ENNReal.coe_lt_top, ENNReal.coe_toNNReal, ENNReal.le_coe_iff, NNReal, NNReal.coe_le_coe.mp, b.toNNReal, coe_le_coe, coe_lt_top, coe_toNNReal, exists_compact_superset, iInf_le_iff, interior_subset, le_antisymm_iff, le_coe_iff, le_iInf_iff, le_iInf_iff.mp
-/
lemma contentRegular_rieszContent : (rieszContent Λ).ContentRegular := by
  intro K
  simp only [rieszContent, le_antisymm_iff, le_iInf_iff, ENNReal.coe_le_coe, Content.mk_apply]
  refine ⟨fun K' hK' => rieszContentAux_mono Λ (hK'.trans interior_subset), ?_⟩
  rw [iInf_le_iff]
  intro b hb
  rw [rieszContentAux]; rw [ENNReal.le_coe_iff]
  have : b < ⊤ := by
    obtain ⟨F, hF⟩ := exists_compact_superset K.2
    exact (le_iInf_iff.mp (hb ⟨F, hF.1⟩) hF.2).trans_lt ENNReal.coe_lt_top
  refine ⟨b.toNNReal, (ENNReal.coe_toNNReal this.ne).symm, NNReal.coe_le_coe.mp ?_⟩
  apply le_iff_forall_pos_le_add.mpr
  intro ε hε
  lift ε to Real>=0 using hε.le
  obtain ⟨f, hfleoneonK, hfle⟩ := exists_lt_rieszContentAux_add_pos Λ K (Real.toNNReal_pos.mpr hε)
  rw [rieszContentAux]; rw [Real.toNNReal_of_nonneg hε.le]; rw [← NNReal.coe_lt_coe] at hfle
  refine ((le_iff_forall_one_lt_le_mul₀ (zero_le (a := Λ f))).mpr fun α hα => ?_).trans hfle.le
  rw [mul_comm]; rw [← smul_eq_mul]; rw [← map_smul]
  set K' := f ⁻¹' Ici α⁻¹
  have hKK' : ↑K subseteq interior K' :=
    subset_interior_iff.2 ⟨f ⁻¹' Ioi α⁻¹, isOpen_Ioi.preimage f.1.2,
      fun x hx => (inv_lt_one_of_one_lt₀ hα).trans_le (hfleoneonK x hx),
      preimage_mono Ioi_subset_Ici_self⟩
  have hK'cp : IsCompact K' := .of_isClosed_subset f.2 (isClosed_Ici.preimage f.1.2) fun x hx =>
    subset_closure ((inv_pos_of_pos <| zero_lt_one.trans hα).trans_le hx).ne'
  set hb' := hb ⟨K', hK'cp⟩
  simp only [Compacts.coe_mk, le_iInf_iff] at hb'
exact (ENNReal.toNNReal_mono (by simp) <| hb' hKK').trans csInf_le'
    ⟨α • f, fun x => (inv_le_iff_one_le_mul₀' (zero_lt_one.trans hα)).mp, by simp⟩

end RieszContentRegular

namespace NNRealRMK

variable [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]

/--
Definition of `rieszMeasure` / `rieszMeasure` 的定义

English:
definition rieszMeasure
  body: (rieszContent Λ).measure

中文:
定义 rieszMeasure
  定义体: (rieszContent Λ).measure

Depends on / 依赖: measure, rieszContent
-/
def rieszMeasure := (rieszContent Λ).measure

set_option backward.isDefEq.respectTransparency false in
/--
lemma `le_rieszMeasure_of_isCompact_tsupport_subset` / 引理 `le_rieszMeasure_of_isCompact_tsupport_subset`

English:
lemma le_rieszMeasure_of_isCompact_tsupport_subset
  statement: {f : C_c(X, Real>=0)} (hf : forall x, f x <= 1)
  proof: by
  rw [← TopologicalSpace.Compacts.coe_mk K hK]
  simp only [rieszMeasure, Content.measure_eq_content_of_regular (rieszContent Λ)
    (contentRegular_rieszContent Λ)]
  simp only [rieszContent, ENNReal.coe_le_coe, Content.mk_apply]
  apply le_iff_forall_pos_le_add.mpr
  intro ε hε
  obtain ⟨g, hg⟩

中文:
引理 le_rieszMeasure_of_isCompact_tsupport_subset
  结论: {f : C_c(X, 实数>=0)} (hf : 对任意 x, f x <= 1)
  证明: by
  rw [← TopologicalSpace.Compacts.coe_mk K hK]
  simp only [rieszMeasure, Content.measure_eq_content_of_regular (rieszContent Λ)
    (contentRegular_rieszContent Λ)]
  simp only [rieszContent, ENNReal.coe_le_coe, Content.mk_apply]
  apply le_iff_forall_pos_le_add.mpr
  intro ε hε
  obtain ⟨g, hg⟩

Depends on / 依赖: Compacts, Content, Content.measure_eq_content_of_regular, Content.mk_apply, ENNReal, ENNReal.coe_le_coe, Set.mem_of_subset_of_mem, TopologicalSpace, TopologicalSpace.Compacts.coe_mk, coe_le_coe, coe_mk, contentRegular_rieszContent, exists_lt_rieszContentAux_add_pos, le_iff_forall_pos_le_add, le_iff_forall_pos_le_add.mpr, le_trans, measure_eq_content_of_regular, mem_of_subset_of_mem, mk_apply, monotone_of_nnreal
-/
lemma le_rieszMeasure_of_isCompact_tsupport_subset {f : C_c(X, Real>=0)} (hf : forall x, f x <= 1)
    {K : Set X} (hK : IsCompact K) (h : tsupport f subseteq K) : .ofNNReal (Λ f) <= rieszMeasure Λ K := by
  rw [← TopologicalSpace.Compacts.coe_mk K hK]
  simp only [rieszMeasure, Content.measure_eq_content_of_regular (rieszContent Λ)
    (contentRegular_rieszContent Λ)]
  simp only [rieszContent, ENNReal.coe_le_coe, Content.mk_apply]
  apply le_iff_forall_pos_le_add.mpr
  intro ε hε
  obtain ⟨g, hg⟩ := exists_lt_rieszContentAux_add_pos Λ ⟨K, hK⟩ hε
  apply le_trans _ hg.2.le
  apply monotone_of_nnreal Λ
  intro x
  simp only
  by_cases hx : x in tsupport f
  · exact le_trans (hf x) (hg.1 x (Set.mem_of_subset_of_mem h hx))
  · rw [image_eq_zero_of_notMem_tsupport hx]
    exact zero_le

/--
lemma `le_rieszMeasure_of_tsupport_subset` / 引理 `le_rieszMeasure_of_tsupport_subset`

English:
lemma le_rieszMeasure_of_tsupport_subset
  statement: {f : C_c(X, Real>=0)} (hf : forall x, f x <= 1) {V : Set X}
  proof: by
  apply le_trans _ (measure_mono h)
  apply le_rieszMeasure_of_isCompact_tsupport_subset Λ hf f.hasCompactSupport
  exact subset_rfl

中文:
引理 le_rieszMeasure_of_tsupport_subset
  结论: {f : C_c(X, 实数>=0)} (hf : 对任意 x, f x <= 1) {V : 集合 X}
  证明: by
  apply le_trans _ (measure_mono h)
  apply le_rieszMeasure_of_isCompact_tsupport_subset Λ hf f.hasCompactSupport
  exact subset_rfl

Depends on / 依赖: f.hasCompactSupport, hasCompactSupport, le_rieszMeasure_of_isCompact_tsupport_subset, le_trans, measure_mono, subset_rfl
-/
lemma le_rieszMeasure_of_tsupport_subset {f : C_c(X, Real>=0)} (hf : forall x, f x <= 1) {V : Set X}
    (h : tsupport f subseteq V) : .ofNNReal (Λ f) <= rieszMeasure Λ V := by
  apply le_trans _ (measure_mono h)
  apply le_rieszMeasure_of_isCompact_tsupport_subset Λ hf f.hasCompactSupport
  exact subset_rfl

end NNRealRMK
