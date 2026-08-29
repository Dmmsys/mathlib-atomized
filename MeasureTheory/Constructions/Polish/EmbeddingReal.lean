/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# A Polish Borel space is measurably equivalent to a set of reals
-/

@[expose] public section

open Set Function PolishSpace PiNat TopologicalSpace Bornology Metric Filter Topology MeasureTheory

namespace MeasureTheory
variable (α : Type*) [MeasurableSpace α] [StandardBorelSpace α]

/--
theorem `exists_nat_measurableEquiv_range_coe_fin_of_finite` / 定理 `exists_nat_measurableEquiv_range_coe_fin_of_finite`

English:
theorem exists_nat_measurableEquiv_range_coe_fin_of_finite
  given: [Finite α]
  proof: by
  obtain ⟨n, ⟨n_equiv⟩⟩ := Finite.exists_equiv_fin α
  refine ⟨n, ⟨PolishSpace.Equiv.measurableEquiv (n_equiv.trans ?_)⟩⟩
  exact Equiv.ofInjective _ (Nat.cast_injective.comp Fin.val_injective)

中文:
定理 存在_nat_measurableEquiv_range_coe_fin_of_finite
  条件: [有限 α]
  证明: by
  obtain ⟨n, ⟨n_equiv⟩⟩ := Finite.exists_equiv_fin α
  refine ⟨n, ⟨PolishSpace.Equiv.measurableEquiv (n_equiv.trans ?_)⟩⟩
  exact Equiv.ofInjective _ (Nat.cast_injective.comp Fin.val_injective)

Depends on / 依赖: Equiv.ofInjective, Fin.val_injective, Finite, Finite.exists_equiv_fin, Nat.cast_injective.comp, PolishSpace, PolishSpace.Equiv.measurableEquiv, cast_injective, exists_equiv_fin, measurableEquiv, n_equiv, n_equiv.trans, ofInjective, val_injective
-/
theorem exists_nat_measurableEquiv_range_coe_fin_of_finite [Finite α] :
    exists n : Nat, Nonempty (α ≃ᵐ range ((↑) : Fin n -> Real)) := by
  obtain ⟨n, ⟨n_equiv⟩⟩ := Finite.exists_equiv_fin α
  refine ⟨n, ⟨PolishSpace.Equiv.measurableEquiv (n_equiv.trans ?_)⟩⟩
  exact Equiv.ofInjective _ (Nat.cast_injective.comp Fin.val_injective)

/--
theorem `measurableEquiv_range_coe_nat_of_infinite_of_countable` / 定理 `measurableEquiv_range_coe_nat_of_infinite_of_countable`

English:
theorem measurableEquiv_range_coe_nat_of_infinite_of_countable
  given: [Infinite α] [Countable α]
  proof: by
  have : PolishSpace (range ((↑) : Nat -> Real)) :=
    Nat.isClosedEmbedding_coe_real.isClosedMap.isClosed_range.polishSpace
  refine ⟨PolishSpace.Equiv.measurableEquiv ?_⟩
  refine (nonempty_equiv_of_countable.some : α ≃ Nat).trans ?_
  exact Equiv.ofInjective ((↑) : Nat -> Real) Nat.cast_injec

中文:
定理 measurableEquiv_range_coe_nat_of_infinite_of_countable
  条件: [无限 α] [可数 α]
  证明: by
  have : PolishSpace (range ((↑) : Nat -> Real)) :=
    Nat.isClosedEmbedding_coe_real.isClosedMap.isClosed_range.polishSpace
  refine ⟨PolishSpace.Equiv.measurableEquiv ?_⟩
  refine (nonempty_equiv_of_countable.some : α ≃ Nat).trans ?_
  exact Equiv.ofInjective ((↑) : Nat -> Real) Nat.cast_injec

Depends on / 依赖: Equiv.ofInjective, Nat.cast_injective, Nat.isClosedEmbedding_coe_real.isClosedMap.isClosed_range.polishSpace, PolishSpace, PolishSpace.Equiv.measurableEquiv, cast_injective, isClosedEmbedding_coe_real, isClosedMap, isClosed_range, measurableEquiv, nonempty_equiv_of_countable, nonempty_equiv_of_countable.some, ofInjective, polishSpace
-/
theorem measurableEquiv_range_coe_nat_of_infinite_of_countable [Infinite α] [Countable α] :
    Nonempty (α ≃ᵐ range ((↑) : Nat -> Real)) := by
  have : PolishSpace (range ((↑) : Nat -> Real)) :=
    Nat.isClosedEmbedding_coe_real.isClosedMap.isClosed_range.polishSpace
  refine ⟨PolishSpace.Equiv.measurableEquiv ?_⟩
  refine (nonempty_equiv_of_countable.some : α ≃ Nat).trans ?_
  exact Equiv.ofInjective ((↑) : Nat -> Real) Nat.cast_injective

/--
theorem `exists_subset_real_measurableEquiv` / 定理 `exists_subset_real_measurableEquiv`

English:
theorem exists_subset_real_measurableEquiv
  statement: exists s : Set Real, MeasurableSet s ∧ Nonempty (α ≃ᵐ s)
  proof: by
  by_cases hα : Countable α
  · cases finite_or_infinite α
    · obtain ⟨n, h_nonempty_equiv⟩ := exists_nat_measurableEquiv_range_coe_fin_of_finite α
      refine ⟨_, ?_, h_nonempty_equiv⟩
      exact (Set.finite_range ((↑) : Fin n -> Real)).measurableSet
    · refine ⟨_, ?_, measurableEquiv_rang

中文:
定理 存在_subset_real_measurableEquiv
  结论: 存在 s : 集合 实数, 可测集 s ∧ 非空 (α ≃ᵐ s)
  证明: by
  by_cases hα : Countable α
  · cases finite_or_infinite α
    · obtain ⟨n, h_nonempty_equiv⟩ := exists_nat_measurableEquiv_range_coe_fin_of_finite α
      refine ⟨_, ?_, h_nonempty_equiv⟩
      exact (Set.finite_range ((↑) : Fin n -> Real)).measurableSet
    · refine ⟨_, ?_, measurableEquiv_rang

Depends on / 依赖: Countable, MeasurableSet, MeasurableSet.univ, Nat.isClosedEmbedding_coe_real.isClosed_range.measurableSet, PolishSpace, PolishSpace.measurableEquivOfNotCountable, Set.finite_range, exists_nat_measurableEquiv_range_coe_fin_of_finite, finite_or_infinite, finite_range, h_nonempty_equiv, isClosedEmbedding_coe_real, isClosed_range, measurableEquivOfNotCountable, measurableEquiv_range_coe_nat_of_infinite_of_countable, measurableSet
-/
theorem exists_subset_real_measurableEquiv : exists s : Set Real, MeasurableSet s ∧ Nonempty (α ≃ᵐ s) := by
  by_cases hα : Countable α
  · cases finite_or_infinite α
    · obtain ⟨n, h_nonempty_equiv⟩ := exists_nat_measurableEquiv_range_coe_fin_of_finite α
      refine ⟨_, ?_, h_nonempty_equiv⟩
      exact (Set.finite_range ((↑) : Fin n -> Real)).measurableSet
    · refine ⟨_, ?_, measurableEquiv_range_coe_nat_of_infinite_of_countable α⟩
      exact Nat.isClosedEmbedding_coe_real.isClosed_range.measurableSet
  · refine
      ⟨univ, MeasurableSet.univ,
        ⟨(PolishSpace.measurableEquivOfNotCountable hα ?_ : α ≃ᵐ (univ : Set Real))⟩⟩
    rw [countable_coe_iff]
    exact Cardinal.not_countable_real

/--
theorem `exists_measurableEmbedding_real` / 定理 `exists_measurableEmbedding_real`

English:
theorem exists_measurableEmbedding_real
  statement: exists f : α -> Real, MeasurableEmbedding f
  proof: by
  obtain ⟨s, hs, ⟨e⟩⟩ := exists_subset_real_measurableEquiv α
  exact ⟨(↑) ∘ e, (MeasurableEmbedding.subtype_coe hs).comp e.measurableEmbedding⟩

中文:
定理 存在_measurableEmbedding_real
  结论: 存在 f : α -> 实数, 可测嵌入 f
  证明: by
  obtain ⟨s, hs, ⟨e⟩⟩ := exists_subset_real_measurableEquiv α
  exact ⟨(↑) ∘ e, (MeasurableEmbedding.subtype_coe hs).comp e.measurableEmbedding⟩

Depends on / 依赖: MeasurableEmbedding, MeasurableEmbedding.subtype_coe, e.measurableEmbedding, exists_subset_real_measurableEquiv, measurableEmbedding, subtype_coe
-/
theorem exists_measurableEmbedding_real : exists f : α -> Real, MeasurableEmbedding f := by
  obtain ⟨s, hs, ⟨e⟩⟩ := exists_subset_real_measurableEquiv α
  exact ⟨(↑) ∘ e, (MeasurableEmbedding.subtype_coe hs).comp e.measurableEmbedding⟩

/-- A measurable embedding of a standard Borel space into `ℝ`. -/
noncomputable
/--
Definition of `embeddingReal` / `embeddingReal` 的定义

English:
definition embeddingReal
  signature: (Ω : Type*) [MeasurableSpace Ω] [StandardBorelSpace Ω]
  body: (exists_measurableEmbedding_real Ω).choose

中文:
定义 embedding实数
  签名: (Ω : 类型) [可测空间 Ω] [StandardBorel空间 Ω]
  定义体: (exists_measurableEmbedding_real Ω).choose

Depends on / 依赖: exists_measurableEmbedding_real
-/
def embeddingReal (Ω : Type*) [MeasurableSpace Ω] [StandardBorelSpace Ω] : Ω -> Real :=
  (exists_measurableEmbedding_real Ω).choose

/--
lemma `measurableEmbedding_embeddingReal` / 引理 `measurableEmbedding_embeddingReal`

English:
lemma measurableEmbedding_embeddingReal
  given: (Ω : Type*) [MeasurableSpace Ω] [StandardBorelSpace Ω]
  proof: (exists_measurableEmbedding_real Ω).choose_spec

@[fun_prop]

中文:
引理 measurableEmbedding_embedding实数
  条件: (Ω : 类型) [可测空间 Ω] [StandardBorel空间 Ω]
  证明: (exists_measurableEmbedding_real Ω).choose_spec

@[fun_prop]

Depends on / 依赖: choose_spec, exists_measurableEmbedding_real
-/
lemma measurableEmbedding_embeddingReal (Ω : Type*) [MeasurableSpace Ω] [StandardBorelSpace Ω] :
    MeasurableEmbedding (embeddingReal Ω) :=
  (exists_measurableEmbedding_real Ω).choose_spec

@[fun_prop]
/--
lemma `measurable_embeddingReal` / 引理 `measurable_embeddingReal`

English:
lemma measurable_embeddingReal
  given: (Ω : Type*) [MeasurableSpace Ω] [StandardBorelSpace Ω]
  proof: (measurableEmbedding_embeddingReal Ω).measurable

中文:
引理 measurable_embedding实数
  条件: (Ω : 类型) [可测空间 Ω] [StandardBorel空间 Ω]
  证明: (measurableEmbedding_embeddingReal Ω).measurable

Depends on / 依赖: measurable, measurableEmbedding_embeddingReal
-/
lemma measurable_embeddingReal (Ω : Type*) [MeasurableSpace Ω] [StandardBorelSpace Ω] :
    Measurable (embeddingReal Ω) :=
  (measurableEmbedding_embeddingReal Ω).measurable

end MeasureTheory
