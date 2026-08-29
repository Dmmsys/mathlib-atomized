/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Order.KrullDimension
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.LinearAlgebra.Dimension.Free

/-!

# Length of modules

## Main results
- `Module.length`: `Module.length R M` is the length of `M` as an `R`-module.
- `Module.length_pos`: The length of a nontrivial module is positive
- `Module.length_ne_top`: The length of an Artinian and Noetherian module is finite.
- `Module.length_eq_add_of_exact`: Length is additive in exact sequences.

-/

@[expose] public section

variable (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]

/-- The length of a module, defined as the krull dimension of its submodule lattice. -/
noncomputable
/--
Definition of `Module.length` / `Module.length` 的定义

English:
definition Module.length
  signature: : Nat∞
  body: (Order.krullDim (Submodule R M)).unbot (by simp [Order.krullDim_eq_bot_iff])

中文:
定义 模.length
  签名: : 自然数∞
  定义体: (Order.krullDim (Submodule R M)).unbot (by simp [Order.krullDim_eq_bot_iff])

Depends on / 依赖: Order.krullDim, Order.krullDim_eq_bot_iff, Submodule, krullDim, krullDim_eq_bot_iff
-/
def Module.length : Nat∞ :=
  (Order.krullDim (Submodule R M)).unbot (by simp [Order.krullDim_eq_bot_iff])

/--
lemma `Module.coe_length` / 引理 `Module.coe_length`

English:
lemma Module.coe_length
  proof: WithBot.coe_unbot _ _

中文:
引理 模.coe_length
  证明: WithBot.coe_unbot _ _

Depends on / 依赖: WithBot, WithBot.coe_unbot, coe_unbot
-/
lemma Module.coe_length :
    (Module.length R M : WithBot Nat∞) = Order.krullDim (Submodule R M) :=
  WithBot.coe_unbot _ _

/--
lemma `Module.length_eq_height` / 引理 `Module.length_eq_height`

English:
lemma Module.length_eq_height
  statement: Module.length R M = Order.height (⊤ : Submodule R M)
  proof: by
  apply WithBot.coe_injective
  rw [Module.coe_length]; rw [Order.height_top_eq_krullDim]

中文:
引理 模.length_eq_height
  结论: 模.length R M = Order.height (⊤ : 子模 R M)
  证明: by
  apply WithBot.coe_injective
  rw [Module.coe_length]; rw [Order.height_top_eq_krullDim]

Depends on / 依赖: Module, Module.coe_length, Order.height_top_eq_krullDim, WithBot, WithBot.coe_injective, coe_injective, coe_length, height_top_eq_krullDim
-/
lemma Module.length_eq_height : Module.length R M = Order.height (⊤ : Submodule R M) := by
  apply WithBot.coe_injective
  rw [Module.coe_length]; rw [Order.height_top_eq_krullDim]

/--
lemma `Module.length_eq_coheight` / 引理 `Module.length_eq_coheight`

English:
lemma Module.length_eq_coheight
  statement: Module.length R M = Order.coheight (⊥ : Submodule R M)
  proof: by
  apply WithBot.coe_injective
  rw [Module.coe_length]; rw [Order.coheight_bot_eq_krullDim]

中文:
引理 模.length_eq_coheight
  结论: 模.length R M = Order.coheight (⊥ : 子模 R M)
  证明: by
  apply WithBot.coe_injective
  rw [Module.coe_length]; rw [Order.coheight_bot_eq_krullDim]

Depends on / 依赖: Module, Module.coe_length, Order.coheight_bot_eq_krullDim, WithBot, WithBot.coe_injective, coe_injective, coe_length, coheight_bot_eq_krullDim
-/
lemma Module.length_eq_coheight : Module.length R M = Order.coheight (⊥ : Submodule R M) := by
  apply WithBot.coe_injective
  rw [Module.coe_length]; rw [Order.coheight_bot_eq_krullDim]

variable {R M}

/--
lemma `Module.length_eq_zero_iff` / 引理 `Module.length_eq_zero_iff`

English:
lemma Module.length_eq_zero_iff
  statement: Module.length R M = 0 ↔ Subsingleton M
  proof: by
  rw [← WithBot.coe_inj]; rw [Module.coe_length]; rw [WithBot.coe_zero]; rw [Order.krullDim_eq_zero_iff_of_orderTop]; rw [Submodule.subsingleton_iff]

@[simp, nontriviality]

中文:
引理 模.length_eq_zero_iff
  结论: 模.length R M = 0 ↔ 子单例 M
  证明: by
  rw [← WithBot.coe_inj]; rw [Module.coe_length]; rw [WithBot.coe_zero]; rw [Order.krullDim_eq_zero_iff_of_orderTop]; rw [Submodule.subsingleton_iff]

@[simp, nontriviality]

Depends on / 依赖: Module, Module.coe_length, Order.krullDim_eq_zero_iff_of_orderTop, Submodule, Submodule.subsingleton_iff, WithBot, WithBot.coe_inj, WithBot.coe_zero, coe_inj, coe_length, coe_zero, krullDim_eq_zero_iff_of_orderTop, subsingleton_iff
-/
lemma Module.length_eq_zero_iff : Module.length R M = 0 ↔ Subsingleton M := by
  rw [← WithBot.coe_inj]; rw [Module.coe_length]; rw [WithBot.coe_zero]; rw [Order.krullDim_eq_zero_iff_of_orderTop]; rw [Submodule.subsingleton_iff]

@[simp, nontriviality]
/--
lemma `Module.length_eq_zero` / 引理 `Module.length_eq_zero`

English:
lemma Module.length_eq_zero
  given: [Subsingleton M]
  statement: Module.length R M = 0
  proof: Module.length_eq_zero_iff.mpr ‹_›

@[simp, nontriviality]

中文:
引理 模.length_eq_zero
  条件: [子单例 M]
  结论: 模.length R M = 0
  证明: Module.length_eq_zero_iff.mpr ‹_›

@[simp, nontriviality]

Depends on / 依赖: Module, Module.length_eq_zero_iff.mpr, length_eq_zero_iff
-/
lemma Module.length_eq_zero [Subsingleton M] : Module.length R M = 0 :=
  Module.length_eq_zero_iff.mpr ‹_›

@[simp, nontriviality]
/--
lemma `Module.length_eq_zero_of_subsingleton_ring` / 引理 `Module.length_eq_zero_of_subsingleton_ring`

English:
lemma Module.length_eq_zero_of_subsingleton_ring
  given: [Subsingleton R]
  statement: Module.length R M = 0
  proof: have := Module.subsingleton R M
  Module.length_eq_zero

中文:
引理 模.length_eq_zero_of_subsingleton_ring
  条件: [子单例 R]
  结论: 模.length R M = 0
  证明: have := Module.subsingleton R M
  Module.length_eq_zero

Depends on / 依赖: Module, Module.length_eq_zero, Module.subsingleton, length_eq_zero, subsingleton
-/
lemma Module.length_eq_zero_of_subsingleton_ring [Subsingleton R] : Module.length R M = 0 :=
  have := Module.subsingleton R M
  Module.length_eq_zero

/--
lemma `Module.length_pos_iff` / 引理 `Module.length_pos_iff`

English:
lemma Module.length_pos_iff
  statement: 0 < Module.length R M ↔ Nontrivial M
  proof: by
  rw [pos_iff_ne_zero]; rw [ne_eq]; rw [Module.length_eq_zero_iff]; rw [not_subsingleton_iff_nontrivial]

中文:
引理 模.length_pos_iff
  结论: 0 < 模.length R M ↔ 非平凡 M
  证明: by
  rw [pos_iff_ne_zero]; rw [ne_eq]; rw [Module.length_eq_zero_iff]; rw [not_subsingleton_iff_nontrivial]

Depends on / 依赖: Module, Module.length_eq_zero_iff, length_eq_zero_iff, ne_eq, not_subsingleton_iff_nontrivial, pos_iff_ne_zero
-/
lemma Module.length_pos_iff : 0 < Module.length R M ↔ Nontrivial M := by
  rw [pos_iff_ne_zero]; rw [ne_eq]; rw [Module.length_eq_zero_iff]; rw [not_subsingleton_iff_nontrivial]

/--
lemma `Module.length_pos` / 引理 `Module.length_pos`

English:
lemma Module.length_pos
  given: [Nontrivial M]
  statement: 0 < Module.length R M
  proof: Module.length_pos_iff.mpr ‹_›

中文:
引理 模.length_pos
  条件: [非平凡 M]
  结论: 0 < 模.length R M
  证明: Module.length_pos_iff.mpr ‹_›

Depends on / 依赖: Module, Module.length_pos_iff.mpr, length_pos_iff
-/
lemma Module.length_pos [Nontrivial M] : 0 < Module.length R M :=
  Module.length_pos_iff.mpr ‹_›

/--
lemma `Module.length_compositionSeries` / 引理 `Module.length_compositionSeries`

English:
lemma Module.length_compositionSeries
  statement: (s : CompositionSeries (Submodule R M)) (h₁ : s.head = ⊥)
  proof: by
  have H := isFiniteLength_of_exists_compositionSeries ⟨s, h₁, h₂⟩
  have := (isFiniteLength_iff_isNoetherian_isArtinian.mp H).1
  have := (isFiniteLength_iff_isNoetherian_isArtinian.mp H).2
  rw [← WithBot.coe_inj]; rw [Module.coe_length]
  apply le_antisymm
  · exact (Order.LTSeries.length_le_k

中文:
引理 模.length_compositionSeries
  结论: (s : 合成列 (子模 R M)) (h₁ : s.head = ⊥)
  证明: by
  have H := isFiniteLength_of_exists_compositionSeries ⟨s, h₁, h₂⟩
  have := (isFiniteLength_iff_isNoetherian_isArtinian.mp H).1
  have := (isFiniteLength_iff_isNoetherian_isArtinian.mp H).2
  rw [← WithBot.coe_inj]; rw [Module.coe_length]
  apply le_antisymm
  · exact (Order.LTSeries.length_le_k

Depends on / 依赖: LTSeries, Module, Module.coe_length, Order.LTSeries.length_le_krullDim, Order.krullDim, WithBot, WithBot.coe_inj, WithBot.coe_le_coe.mpr, coe_inj, coe_le_coe, coe_length, exists_relSeries_covBy_and_head_eq_bot_and_last_eq_bot, iSup_le_iff, isFiniteLength_iff_isNoetherian_isArtinian, isFiniteLength_iff_isNoetherian_isArtinian.mp, isFiniteLength_of_exists_compositionSeries, krullDim, le_antisymm, length_le_krullDim, s.map
-/
lemma Module.length_compositionSeries (s : CompositionSeries (Submodule R M)) (h₁ : s.head = ⊥)
    (h₂ : s.last = ⊤) : s.length = Module.length R M := by
  have H := isFiniteLength_of_exists_compositionSeries ⟨s, h₁, h₂⟩
  have := (isFiniteLength_iff_isNoetherian_isArtinian.mp H).1
  have := (isFiniteLength_iff_isNoetherian_isArtinian.mp H).2
  rw [← WithBot.coe_inj]; rw [Module.coe_length]
  apply le_antisymm
  · exact (Order.LTSeries.length_le_krullDim <| s.map ⟨id, fun h => h.1⟩)
  · rw [Order.krullDim, iSup_le_iff]
    intro t
    refine WithBot.coe_le_coe.mpr ?_
    obtain ⟨t', i, hi, ht₁, ht₂⟩ := t.exists_relSeries_covBy_and_head_eq_bot_and_last_eq_bot
    have := (s.jordan_holder t' (h₁.trans ht₁.symm) (h₂.trans ht₂.symm)).choose
    have h : t.length <= t'.length := by simpa using Fintype.card_le_of_embedding i
    have h' : t'.length = s.length := by simpa using Fintype.card_congr this.symm
    simpa using h.trans h'.le

/--
lemma `Module.length_eq_top_iff_infiniteDimensionalOrder` / 引理 `Module.length_eq_top_iff_infiniteDimensionalOrder`

English:
lemma Module.length_eq_top_iff_infiniteDimensionalOrder
  proof: by
  rw [← WithBot.coe_inj]; rw [WithBot.coe_top]; rw [coe_length]; rw [Order.krullDim_eq_top_iff]; rw [← not_finiteDimensionalOrder_iff]

中文:
引理 模.length_eq_top_iff_infiniteDimensionalOrder
  证明: by
  rw [← WithBot.coe_inj]; rw [WithBot.coe_top]; rw [coe_length]; rw [Order.krullDim_eq_top_iff]; rw [← not_finiteDimensionalOrder_iff]

Depends on / 依赖: Order.krullDim_eq_top_iff, WithBot, WithBot.coe_inj, WithBot.coe_top, coe_inj, coe_length, coe_top, krullDim_eq_top_iff, not_finiteDimensionalOrder_iff
-/
lemma Module.length_eq_top_iff_infiniteDimensionalOrder :
    length R M = ⊤ ↔ InfiniteDimensionalOrder (Submodule R M) := by
  rw [← WithBot.coe_inj]; rw [WithBot.coe_top]; rw [coe_length]; rw [Order.krullDim_eq_top_iff]; rw [← not_finiteDimensionalOrder_iff]

/--
lemma `Module.length_ne_top_iff_finiteDimensionalOrder` / 引理 `Module.length_ne_top_iff_finiteDimensionalOrder`

English:
lemma Module.length_ne_top_iff_finiteDimensionalOrder
  proof: by
  rw [Ne]; rw [length_eq_top_iff_infiniteDimensionalOrder]; rw [← not_finiteDimensionalOrder_iff]; rw [not_not]

中文:
引理 模.length_ne_top_iff_finiteDimensionalOrder
  证明: by
  rw [Ne]; rw [length_eq_top_iff_infiniteDimensionalOrder]; rw [← not_finiteDimensionalOrder_iff]; rw [not_not]

Depends on / 依赖: length_eq_top_iff_infiniteDimensionalOrder, not_finiteDimensionalOrder_iff, not_not
-/
lemma Module.length_ne_top_iff_finiteDimensionalOrder :
    length R M != ⊤ ↔ FiniteDimensionalOrder (Submodule R M) := by
  rw [Ne]; rw [length_eq_top_iff_infiniteDimensionalOrder]; rw [← not_finiteDimensionalOrder_iff]; rw [not_not]

/--
lemma `Module.length_ne_top_iff` / 引理 `Module.length_ne_top_iff`

English:
lemma Module.length_ne_top_iff
  statement: Module.length R M != ⊤ ↔ IsFiniteLength R M
  proof: by
  refine ⟨fun h => ?_, fun H => ?_⟩
  · rw [length_ne_top_iff_finiteDimensionalOrder] at h
    rw [isFiniteLength_iff_isNoetherian_isArtinian]; rw [isNoetherian_iff]; rw [isArtinian_iff]
    let R : SetRel (Submodule R M) (Submodule R M) :=
      {(N₁, N₂) : Submodule R M × Submodule R M | N₁ < N

中文:
引理 模.length_ne_top_iff
  结论: 模.length R M != ⊤ ↔ 是FiniteLength R M
  证明: by
  refine ⟨fun h => ?_, fun H => ?_⟩
  · rw [length_ne_top_iff_finiteDimensionalOrder] at h
    rw [isFiniteLength_iff_isNoetherian_isArtinian]; rw [isNoetherian_iff]; rw [isArtinian_iff]
    let R : SetRel (Submodule R M) (Submodule R M) :=
      {(N₁, N₂) : Submodule R M × Submodule R M | N₁ < N

Depends on / 依赖: IsWellFounded, R.IsWellFounded, R.inv, R.inv.IsWellFounded, SetRel, Submodule, isArtinian_iff, isFiniteLength_iff_exists_compositionSeries, isFiniteLength_iff_exists_compositionSeries.mp, isFiniteLength_iff_isNoetherian_isArtinian, isNoetherian_iff, length_compositionSeries, length_ne_top_iff_finiteDimensionalOrder, of_finiteDimensional
-/
lemma Module.length_ne_top_iff : Module.length R M != ⊤ ↔ IsFiniteLength R M := by
  refine ⟨fun h => ?_, fun H => ?_⟩
  · rw [length_ne_top_iff_finiteDimensionalOrder] at h
    rw [isFiniteLength_iff_isNoetherian_isArtinian]; rw [isNoetherian_iff]; rw [isArtinian_iff]
    let R : SetRel (Submodule R M) (Submodule R M) :=
      {(N₁, N₂) : Submodule R M × Submodule R M | N₁ < N₂}
    change R.inv.IsWellFounded ∧ R.IsWellFounded
    exact ⟨.of_finiteDimensional R.inv, .of_finiteDimensional R⟩
  · obtain ⟨s, hs₁, hs₂⟩ := isFiniteLength_iff_exists_compositionSeries.mp H
    rw [← length_compositionSeries s hs₁ hs₂]
    simp

/--
lemma `Module.length_ne_top` / 引理 `Module.length_ne_top`

English:
lemma Module.length_ne_top
  given: [IsArtinian R M] [IsNoetherian R M]
  statement: Module.length R M != ⊤
  proof: by
  rw [length_ne_top_iff]; rw [isFiniteLength_iff_isNoetherian_isArtinian]
  exact ⟨‹_›, ‹_›⟩

@[simp]

中文:
引理 模.length_ne_top
  条件: [是Artin R M] [是Noether R M]
  结论: 模.length R M != ⊤
  证明: by
  rw [length_ne_top_iff]; rw [isFiniteLength_iff_isNoetherian_isArtinian]
  exact ⟨‹_›, ‹_›⟩

@[simp]

Depends on / 依赖: isFiniteLength_iff_isNoetherian_isArtinian, length_ne_top_iff
-/
lemma Module.length_ne_top [IsArtinian R M] [IsNoetherian R M] : Module.length R M != ⊤ := by
  rw [length_ne_top_iff]; rw [isFiniteLength_iff_isNoetherian_isArtinian]
  exact ⟨‹_›, ‹_›⟩

@[simp]
/--
lemma `Module.finiteDimensionalOrder_submodule_iff` / 引理 `Module.finiteDimensionalOrder_submodule_iff`

English:
lemma Module.finiteDimensionalOrder_submodule_iff
  proof: by
  rw [← Module.length_ne_top_iff_finiteDimensionalOrder]; rw [Module.length_ne_top_iff]

中文:
引理 模.finiteDimensionalOrder_submodule_iff
  证明: by
  rw [← Module.length_ne_top_iff_finiteDimensionalOrder]; rw [Module.length_ne_top_iff]

Depends on / 依赖: Module, Module.length_ne_top_iff, Module.length_ne_top_iff_finiteDimensionalOrder, length_ne_top_iff, length_ne_top_iff_finiteDimensionalOrder
-/
lemma Module.finiteDimensionalOrder_submodule_iff :
    FiniteDimensionalOrder (Submodule R M) ↔ IsFiniteLength R M := by
  rw [← Module.length_ne_top_iff_finiteDimensionalOrder]; rw [Module.length_ne_top_iff]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsArtinian
  signature: R M] [IsNoetherian R M] : FiniteDimensionalOrder (Submodule R M)
  body: by
  rw [Module.finiteDimensionalOrder_submodule_iff]; rw [isFiniteLength_iff_isNoetherian_isArtinian]
  tauto

中文:
实例 [是Artin
  签名: R M] [是Noether R M] : FiniteDimensionalOrder (子模 R M)
  定义体: by
  rw [Module.finiteDimensionalOrder_submodule_iff]; rw [isFiniteLength_iff_isNoetherian_isArtinian]
  tauto

Depends on / 依赖: Module, Module.finiteDimensionalOrder_submodule_iff, finiteDimensionalOrder_submodule_iff, isFiniteLength_iff_isNoetherian_isArtinian
-/
instance [IsArtinian R M] [IsNoetherian R M] : FiniteDimensionalOrder (Submodule R M) := by
  rw [Module.finiteDimensionalOrder_submodule_iff]; rw [isFiniteLength_iff_isNoetherian_isArtinian]
  tauto

/--
lemma `Module.length_submodule` / 引理 `Module.length_submodule`

English:
lemma Module.length_submodule
  given: {N : Submodule R M}
  proof: by
  apply WithBot.coe_injective
  rw [Order.height_eq_krullDim_Iic]; rw [coe_length]; rw [Order.krullDim_eq_of_orderIso (Submodule.mapIic _)]

中文:
引理 模.length_submodule
  条件: {N : 子模 R M}
  证明: by
  apply WithBot.coe_injective
  rw [Order.height_eq_krullDim_Iic]; rw [coe_length]; rw [Order.krullDim_eq_of_orderIso (Submodule.mapIic _)]

Depends on / 依赖: Order.height_eq_krullDim_Iic, Order.krullDim_eq_of_orderIso, Submodule, Submodule.mapIic, WithBot, WithBot.coe_injective, coe_injective, coe_length, height_eq_krullDim_Iic, krullDim_eq_of_orderIso, mapIic
-/
lemma Module.length_submodule {N : Submodule R M} :
    Module.length R N = Order.height N := by
  apply WithBot.coe_injective
  rw [Order.height_eq_krullDim_Iic]; rw [coe_length]; rw [Order.krullDim_eq_of_orderIso (Submodule.mapIic _)]

/--
lemma `Module.length_quotient` / 引理 `Module.length_quotient`

English:
lemma Module.length_quotient
  given: {N : Submodule R M}
  proof: by
  apply WithBot.coe_injective
  rw [Order.coheight_eq_krullDim_Ici]; rw [coe_length]; rw [Order.krullDim_eq_of_orderIso (Submodule.comapMkQRelIso N)]

中文:
引理 模.length_quotient
  条件: {N : 子模 R M}
  证明: by
  apply WithBot.coe_injective
  rw [Order.coheight_eq_krullDim_Ici]; rw [coe_length]; rw [Order.krullDim_eq_of_orderIso (Submodule.comapMkQRelIso N)]

Depends on / 依赖: Order.coheight_eq_krullDim_Ici, Order.krullDim_eq_of_orderIso, Submodule, Submodule.comapMkQRelIso, WithBot, WithBot.coe_injective, coe_injective, coe_length, coheight_eq_krullDim_Ici, comapMkQRelIso, krullDim_eq_of_orderIso
-/
lemma Module.length_quotient {N : Submodule R M} :
    Module.length R (M ⧸ N) = Order.coheight N := by
  apply WithBot.coe_injective
  rw [Order.coheight_eq_krullDim_Ici]; rw [coe_length]; rw [Order.krullDim_eq_of_orderIso (Submodule.comapMkQRelIso N)]

/--
lemma `LinearEquiv.length_eq` / 引理 `LinearEquiv.length_eq`

English:
lemma LinearEquiv.length_eq
  given: {N : Type*} [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N)
  proof: by
  apply WithBot.coe_injective
  rw [Module.coe_length]; rw [Module.coe_length]; rw [Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComap e)]

中文:
引理 线性等价.length_eq
  条件: {N : 类型} [加法交换群 N] [模 R N] (e : M ≃ₗ[R] N)
  证明: by
  apply WithBot.coe_injective
  rw [Module.coe_length]; rw [Module.coe_length]; rw [Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComap e)]

Depends on / 依赖: Module, Module.coe_length, Order.krullDim_eq_of_orderIso, Submodule, Submodule.orderIsoMapComap, WithBot, WithBot.coe_injective, coe_injective, coe_length, krullDim_eq_of_orderIso, orderIsoMapComap
-/
lemma LinearEquiv.length_eq {N : Type*} [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) :
    Module.length R M = Module.length R N := by
  apply WithBot.coe_injective
  rw [Module.coe_length]; rw [Module.coe_length]; rw [Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComap e)]

/--
theorem `Module.length_eq_of_surjective` / 定理 `Module.length_eq_of_surjective`

English:
theorem Module.length_eq_of_surjective
  statement: {S : Type*} [CommRing S] [Algebra S R] [Module S M]
  proof: by
  have : RingHomSurjective (algebraMap S R) := ⟨h⟩
  let f : M ->ₛₗ[algebraMap S R] M := ⟨AddHom.id M, by simp⟩
  rw [Module.length]; rw [Module.length]; rw [WithBot.unbot_inj]; rw [Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f Function.bijective_id)]

中文:
定理 模.length_eq_of_surjective
  结论: {S : 类型} [交换环 S] [代数 S R] [模 S M]
  证明: by
  have : RingHomSurjective (algebraMap S R) := ⟨h⟩
  let f : M ->ₛₗ[algebraMap S R] M := ⟨AddHom.id M, by simp⟩
  rw [Module.length]; rw [Module.length]; rw [WithBot.unbot_inj]; rw [Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f Function.bijective_id)]

Depends on / 依赖: AddHom, AddHom.id, Function, Function.bijective_id, Module, Module.length, Order.krullDim_eq_of_orderIso, RingHomSurjective, Submodule, Submodule.orderIsoMapComapOfBijective, WithBot, WithBot.unbot_inj, algebraMap, bijective_id, krullDim_eq_of_orderIso, length, orderIsoMapComapOfBijective, unbot_inj
-/
theorem Module.length_eq_of_surjective {S : Type*} [CommRing S] [Algebra S R] [Module S M]
    [IsScalarTower S R M] (h : Function.Surjective (algebraMap S R)) :
    Module.length S M = Module.length R M := by
  have : RingHomSurjective (algebraMap S R) := ⟨h⟩
  let f : M ->ₛₗ[algebraMap S R] M := ⟨AddHom.id M, by simp⟩
  rw [Module.length]; rw [Module.length]; rw [WithBot.unbot_inj]; rw [Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f Function.bijective_id)]

/--
lemma `Module.length_bot` / 引理 `Module.length_bot`

English:
lemma Module.length_bot
  proof: Module.length_eq_zero

中文:
引理 模.length_bot
  证明: Module.length_eq_zero

Depends on / 依赖: Module, Module.length_eq_zero, length_eq_zero
-/
lemma Module.length_bot :
    Module.length R (⊥ : Submodule R M) = 0 :=
  Module.length_eq_zero

/--
lemma `Module.length_top` / 引理 `Module.length_top`

English:
lemma Module.length_top
  proof: by
  rw [Module.length_submodule]; rw [Module.length_eq_height]

中文:
引理 模.length_top
  证明: by
  rw [Module.length_submodule]; rw [Module.length_eq_height]
-/
@[simp] lemma Module.length_top :
    Module.length R (⊤ : Submodule R M) = Module.length R M := by
  rw [Module.length_submodule]; rw [Module.length_eq_height]

/--
lemma `Submodule.height_lt_top` / 引理 `Submodule.height_lt_top`

English:
lemma Submodule.height_lt_top
  given: [IsArtinian R M] [IsNoetherian R M] (N : Submodule R M)
  proof: by
  simpa only [← Module.length_submodule] using Module.length_ne_top.lt_top

中文:
引理 子模.height_lt_top
  条件: [是Artin R M] [是Noether R M] (N : 子模 R M)
  证明: by
  simpa only [← Module.length_submodule] using Module.length_ne_top.lt_top

Depends on / 依赖: Module, Module.length_ne_top.lt_top, Module.length_submodule, length_ne_top, length_submodule, lt_top
-/
lemma Submodule.height_lt_top [IsArtinian R M] [IsNoetherian R M] (N : Submodule R M) :
    Order.height N < ⊤ := by
  simpa only [← Module.length_submodule] using Module.length_ne_top.lt_top

/--
lemma `Submodule.height_strictMono` / 引理 `Submodule.height_strictMono`

English:
lemma Submodule.height_strictMono
  given: [IsArtinian R M] [IsNoetherian R M]
  proof: fun N _ h => Order.height_strictMono h N.height_lt_top

中文:
引理 子模.height_strictMono
  条件: [是Artin R M] [是Noether R M]
  证明: fun N _ h => Order.height_strictMono h N.height_lt_top

Depends on / 依赖: N.height_lt_top, Order.height_strictMono, height_lt_top, height_strictMono
-/
lemma Submodule.height_strictMono [IsArtinian R M] [IsNoetherian R M] :
    StrictMono (Order.height : Submodule R M -> Nat∞) :=
  fun N _ h => Order.height_strictMono h N.height_lt_top

/--
lemma `Submodule.length_lt` / 引理 `Submodule.length_lt`

English:
lemma Submodule.length_lt
  given: [IsArtinian R M] [IsNoetherian R M] {N : Submodule R M} (h : N != ⊤)
  proof: by
  simpa [← Module.length_top (M := M), Module.length_submodule] using height_strictMono h.lt_top

中文:
引理 子模.length_lt
  条件: [是Artin R M] [是Noether R M] {N : 子模 R M} (h : N != ⊤)
  证明: by
  simpa [← Module.length_top (M := M), Module.length_submodule] using height_strictMono h.lt_top

Depends on / 依赖: Module, Module.length_submodule, Module.length_top, h.lt_top, height_strictMono, length_submodule, length_top, lt_top
-/
lemma Submodule.length_lt [IsArtinian R M] [IsNoetherian R M] {N : Submodule R M} (h : N != ⊤) :
    Module.length R N < Module.length R M := by
  simpa [← Module.length_top (M := M), Module.length_submodule] using height_strictMono h.lt_top

variable {N P : Type*} [AddCommGroup N] [AddCommGroup P] [Module R N] [Module R P]
variable (f : N ->ₗ[R] M) (g : M ->ₗ[R] P) (hf : Function.Injective f) (hg : Function.Surjective g)
variable (H : Function.Exact f g)

set_option backward.isDefEq.respectTransparency false in
include hf hg H in
/--
lemma `Module.length_eq_add_of_exact` / 引理 `Module.length_eq_add_of_exact`

English:
lemma Module.length_eq_add_of_exact
  proof: by
  by_cases hP : IsFiniteLength R P
  · by_cases hN : IsFiniteLength R N
    · obtain ⟨s, hs₁, hs₂⟩ := isFiniteLength_iff_exists_compositionSeries.mp hP
      obtain ⟨t, ht₁, ht₂⟩ := isFiniteLength_iff_exists_compositionSeries.mp hN
      let s' : CompositionSeries (Submodule R M) :=
        s.map

中文:
引理 模.length_eq_add_of_exact
  证明: by
  by_cases hP : IsFiniteLength R P
  · by_cases hN : IsFiniteLength R N
    · obtain ⟨s, hs₁, hs₂⟩ := isFiniteLength_iff_exists_compositionSeries.mp hP
      obtain ⟨t, ht₁, ht₂⟩ := isFiniteLength_iff_exists_compositionSeries.mp hN
      let s' : CompositionSeries (Submodule R M) :=
        s.map

Depends on / 依赖: CompositionSeries, IsFiniteLength, Submodule, Submodule.comap, Submodule.comap_covBy_of_surjective, Submodule.map, Submodule.map_covBy_of_injective, comap_covBy_of_surjective, isFiniteLength_iff_exists_compositionSeries, isFiniteLength_iff_exists_compositionSeries.mp, map_covBy_of_injective, s.map, t.map
-/
lemma Module.length_eq_add_of_exact :
    Module.length R M = Module.length R N + Module.length R P := by
  by_cases hP : IsFiniteLength R P
  · by_cases hN : IsFiniteLength R N
    · obtain ⟨s, hs₁, hs₂⟩ := isFiniteLength_iff_exists_compositionSeries.mp hP
      obtain ⟨t, ht₁, ht₂⟩ := isFiniteLength_iff_exists_compositionSeries.mp hN
      let s' : CompositionSeries (Submodule R M) :=
        s.map ⟨Submodule.comap g, Submodule.comap_covBy_of_surjective hg⟩
      let t' : CompositionSeries (Submodule R M) :=
        t.map ⟨Submodule.map f, Submodule.map_covBy_of_injective hf⟩
      have hfg : Submodule.map f ⊤ = Submodule.comap g ⊥ := by
        rw [Submodule.map_top]; rw [Submodule.comap_bot]; rw [LinearMap.exact_iff.mp H]
      let r := t'.smash s' (by simpa [s', t', hs₁, ht₂] using hfg)
      rw [← Module.length_compositionSeries s hs₁ hs₂]; rw [← Module.length_compositionSeries t ht₁ ht₂]; rw [← Module.length_compositionSeries r
          (by simpa [r]; rw [t']; rw [ht₁]; rw [-Submodule.map_bot] using Submodule.map_bot f)
          (by simpa [r, s', hs₂, -Submodule.comap_top] using Submodule.comap_top g)]
      simp_rw [r, RelSeries.smash_length, Nat.cast_add, s', t', RelSeries.map_length]
    · have := mt (IsFiniteLength.of_injective · hf) hN
      rw [← Module.length_ne_top_iff]; rw [ne_eq]; rw [not_not] at hN this
      rw [hN]; rw [this]; rw [top_add]
  · have := mt (IsFiniteLength.of_surjective · hg) hP
    rw [← Module.length_ne_top_iff]; rw [ne_eq]; rw [not_not] at hP this
    rw [hP]; rw [this]; rw [add_top]

include hf in
/--
lemma `Module.length_le_of_injective` / 引理 `Module.length_le_of_injective`

English:
lemma Module.length_le_of_injective
  statement: Module.length R N <= Module.length R M
  proof: by
  rw [Module.length_eq_add_of_exact f (LinearMap.range f).mkQ hf
    (Submodule.mkQ_surjective _) (LinearMap.exact_map_mkQ_range f)]
  exact le_self_add

include hg in

中文:
引理 模.length_le_of_injective
  结论: 模.length R N <= 模.length R M
  证明: by
  rw [Module.length_eq_add_of_exact f (LinearMap.range f).mkQ hf
    (Submodule.mkQ_surjective _) (LinearMap.exact_map_mkQ_range f)]
  exact le_self_add

include hg in

Depends on / 依赖: LinearMap, LinearMap.exact_map_mkQ_range, LinearMap.range, Module, Module.length_eq_add_of_exact, Submodule, Submodule.mkQ_surjective, exact_map_mkQ_range, le_self_add, length_eq_add_of_exact, mkQ_surjective
-/
lemma Module.length_le_of_injective : Module.length R N <= Module.length R M := by
  rw [Module.length_eq_add_of_exact f (LinearMap.range f).mkQ hf
    (Submodule.mkQ_surjective _) (LinearMap.exact_map_mkQ_range f)]
  exact le_self_add

include hg in
/--
lemma `Module.length_le_of_surjective` / 引理 `Module.length_le_of_surjective`

English:
lemma Module.length_le_of_surjective
  statement: Module.length R P <= Module.length R M
  proof: by
  rw [Module.length_eq_add_of_exact (LinearMap.ker g).subtype g (Submodule.subtype_injective _) hg
    (LinearMap.exact_subtype_ker_map g)]
  exact le_add_self

中文:
引理 模.length_le_of_surjective
  结论: 模.length R P <= 模.length R M
  证明: by
  rw [Module.length_eq_add_of_exact (LinearMap.ker g).subtype g (Submodule.subtype_injective _) hg
    (LinearMap.exact_subtype_ker_map g)]
  exact le_add_self

Depends on / 依赖: LinearMap, LinearMap.exact_subtype_ker_map, LinearMap.ker, Module, Module.length_eq_add_of_exact, Submodule, Submodule.subtype_injective, exact_subtype_ker_map, le_add_self, length_eq_add_of_exact, subtype, subtype_injective
-/
lemma Module.length_le_of_surjective : Module.length R P <= Module.length R M := by
  rw [Module.length_eq_add_of_exact (LinearMap.ker g).subtype g (Submodule.subtype_injective _) hg
    (LinearMap.exact_subtype_ker_map g)]
  exact le_add_self

variable (R M N) in
@[simp]
/--
lemma `Module.length_prod` / 引理 `Module.length_prod`

English:
lemma Module.length_prod
  proof: Module.length_eq_add_of_exact _ _ LinearMap.inl_injective LinearMap.snd_surjective .inl_snd

中文:
引理 模.length_prod
  证明: Module.length_eq_add_of_exact _ _ LinearMap.inl_injective LinearMap.snd_surjective .inl_snd

Depends on / 依赖: LinearMap, LinearMap.inl_injective, LinearMap.snd_surjective, Module, Module.length_eq_add_of_exact, inl_injective, inl_snd, length_eq_add_of_exact, snd_surjective
-/
lemma Module.length_prod :
    Module.length R (M × N) = Module.length R M + Module.length R N :=
  Module.length_eq_add_of_exact _ _ LinearMap.inl_injective LinearMap.snd_surjective .inl_snd

variable (R) in
@[simp]
/--
lemma `Module.length_pi_of_fintype` / 引理 `Module.length_pi_of_fintype`

English:
lemma Module.length_pi_of_fintype
  statement: forall {ι : Type*} [Fintype ι]
  proof: by
  apply Fintype.induction_empty_option
  · intro α β _ e IH M _ _
    let _ : Fintype α := .ofEquiv β e.symm
    rw [← (LinearEquiv.piCongrLeft R M e).length_eq]; rw [IH]; rw [e.sum_comp (length R <| M ·)]
  · intro M _ _
    simp [Module.length_eq_zero]
  · intro ι _ IH M _ _
    rw [(LinearEqui

中文:
引理 模.length_pi_of_fintype
  结论: 对任意 {ι : 类型} [有限类型 ι]
  证明: by
  apply Fintype.induction_empty_option
  · intro α β _ e IH M _ _
    let _ : Fintype α := .ofEquiv β e.symm
    rw [← (LinearEquiv.piCongrLeft R M e).length_eq]; rw [IH]; rw [e.sum_comp (length R <| M ·)]
  · intro M _ _
    simp [Module.length_eq_zero]
  · intro ι _ IH M _ _
    rw [(LinearEqui

Depends on / 依赖: Fintype, Fintype.induction_empty_option, Fintype.sum_option, LinearEquiv, LinearEquiv.piCongrLeft, LinearEquiv.piOptionEquivProd, Module, Module.length_eq_zero, Module.length_prod, add_comm, e.sum_comp, e.symm, induction_empty_option, length, length_eq, length_eq_zero, length_prod, ofEquiv, piCongrLeft, piOptionEquivProd
-/
lemma Module.length_pi_of_fintype : forall {ι : Type*} [Fintype ι]
    (M : ι -> Type*) [forall i, AddCommGroup (M i)] [forall i, Module R (M i)],
    Module.length R (Π i, M i) = ∑ i, Module.length R (M i) := by
  apply Fintype.induction_empty_option
  · intro α β _ e IH M _ _
    let _ : Fintype α := .ofEquiv β e.symm
    rw [← (LinearEquiv.piCongrLeft R M e).length_eq]; rw [IH]; rw [e.sum_comp (length R <| M ·)]
  · intro M _ _
    simp [Module.length_eq_zero]
  · intro ι _ IH M _ _
    rw [(LinearEquiv.piOptionEquivProd _).length_eq]; rw [Module.length_prod]; rw [IH]; rw [add_comm]; rw [Fintype.sum_option]; rw [add_comm]

@[simp]
/--
lemma `Module.length_finsupp` / 引理 `Module.length_finsupp`

English:
lemma Module.length_finsupp
  given: {ι : Type*}
  proof: by
  cases finite_or_infinite ι
  · cases nonempty_fintype ι
    simp [(Finsupp.linearEquivFunOnFinite R M ι).length_eq]
  nontriviality M
  rw [ENat.card_eq_top_of_infinite]; rw [ENat.top_mul length_pos.ne']; rw [ENat.eq_top_iff_forall_ge]
  intro m
  obtain ⟨s, hs⟩ := Infinite.exists_subset_card_e

中文:
引理 模.length_finsupp
  条件: {ι : 类型}
  证明: by
  cases finite_or_infinite ι
  · cases nonempty_fintype ι
    simp [(Finsupp.linearEquivFunOnFinite R M ι).length_eq]
  nontriviality M
  rw [ENat.card_eq_top_of_infinite]; rw [ENat.top_mul length_pos.ne']; rw [ENat.eq_top_iff_forall_ge]
  intro m
  obtain ⟨s, hs⟩ := Infinite.exists_subset_card_e

Depends on / 依赖: ENat.card_eq_top_of_infinite, ENat.eq_top_iff_forall_ge, ENat.top_mul, Finsupp, Finsupp.linearEquivFunOnFinite, Finsupp.lmapDomain, Finsupp.m, Infinite, Infinite.exists_subset_card_eq, Module, Module.length_le_of_injective, card_eq_top_of_infinite, eq_top_iff_forall_ge, exists_subset_card_eq, finite_or_infinite, le_trans, length, length_eq, length_le_of_injective, length_pos
-/
lemma Module.length_finsupp {ι : Type*} :
    Module.length R (ι ->₀ M) = ENat.card ι * Module.length R M := by
  cases finite_or_infinite ι
  · cases nonempty_fintype ι
    simp [(Finsupp.linearEquivFunOnFinite R M ι).length_eq]
  nontriviality M
  rw [ENat.card_eq_top_of_infinite]; rw [ENat.top_mul length_pos.ne']; rw [ENat.eq_top_iff_forall_ge]
  intro m
  obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq ι m
  have : length R (s ->₀ M) = ↑m * length R M := by
    simp [(Finsupp.linearEquivFunOnFinite R M _).length_eq, hs]
  refine le_trans ?_ (Module.length_le_of_injective (Finsupp.lmapDomain M R ((↑) : s -> ι))
    (Finsupp.mapDomain_injective Subtype.val_injective))
  rw [this]
  exact ENat.self_le_mul_right _ length_pos.ne'

@[simp]
/--
lemma `Module.length_pi` / 引理 `Module.length_pi`

English:
lemma Module.length_pi
  given: {ι : Type*}
  proof: by
  cases finite_or_infinite ι
  · cases nonempty_fintype ι
    simp
  nontriviality M
  rw [ENat.card_eq_top_of_infinite]; rw [ENat.top_mul length_pos.ne']; rw [← top_le_iff]
  refine le_trans ?_ (Module.length_le_of_injective Finsupp.lcoeFun DFunLike.coe_injective)
  simp [ENat.top_mul length_pos

中文:
引理 模.length_pi
  条件: {ι : 类型}
  证明: by
  cases finite_or_infinite ι
  · cases nonempty_fintype ι
    simp
  nontriviality M
  rw [ENat.card_eq_top_of_infinite]; rw [ENat.top_mul length_pos.ne']; rw [← top_le_iff]
  refine le_trans ?_ (Module.length_le_of_injective Finsupp.lcoeFun DFunLike.coe_injective)
  simp [ENat.top_mul length_pos

Depends on / 依赖: DFunLike, DFunLike.coe_injective, ENat.card_eq_top_of_infinite, ENat.top_mul, Finsupp, Finsupp.lcoeFun, Module, Module.length_le_of_injective, card_eq_top_of_infinite, coe_injective, finite_or_infinite, lcoeFun, le_trans, length_le_of_injective, length_pos, length_pos.ne, nonempty_fintype, nontriviality, top_le_iff, top_mul
-/
lemma Module.length_pi {ι : Type*} :
    Module.length R (ι -> M) = ENat.card ι * Module.length R M := by
  cases finite_or_infinite ι
  · cases nonempty_fintype ι
    simp
  nontriviality M
  rw [ENat.card_eq_top_of_infinite]; rw [ENat.top_mul length_pos.ne']; rw [← top_le_iff]
  refine le_trans ?_ (Module.length_le_of_injective Finsupp.lcoeFun DFunLike.coe_injective)
  simp [ENat.top_mul length_pos.ne']

attribute [nontriviality] rank_subsingleton'

variable (R M) in
/--
lemma `Module.length_of_free` / 引理 `Module.length_of_free`

English:
lemma Module.length_of_free
  given: [Module.Free R M]
  proof: by
  let b := Module.Free.chooseBasis R M
  nontriviality R
  nontriviality M
  by_cases H : Module.length R R = ⊤
  · simp [b.repr.length_eq, H, rank_pos_of_free.ne']
  rw [← ne_eq]; rw [Module.length_ne_top_iff]; rw [isFiniteLength_iff_isNoetherian_isArtinian] at H
  cases H
  let b := Module.Free

中文:
引理 模.length_of_free
  条件: [模.自由 R M]
  证明: by
  let b := Module.Free.chooseBasis R M
  nontriviality R
  nontriviality M
  by_cases H : Module.length R R = ⊤
  · simp [b.repr.length_eq, H, rank_pos_of_free.ne']
  rw [← ne_eq]; rw [Module.length_ne_top_iff]; rw [isFiniteLength_iff_isNoetherian_isArtinian] at H
  cases H
  let b := Module.Free

Depends on / 依赖: ENat.card, Free.rank_eq_card_chooseBasisIndex, Module, Module.Free.chooseBasis, Module.length, Module.length_finsupp, Module.length_ne_top_iff, b.repr.length_eq, chooseBasis, isFiniteLength_iff_isNoetherian_isArtinian, length, length_eq, length_finsupp, length_ne_top_iff, ne_eq, nontriviality, rank_eq_card_chooseBasisIndex, rank_pos_of_free, rank_pos_of_free.ne
-/
lemma Module.length_of_free [Module.Free R M] :
    Module.length R M = (Module.rank R M).toENat * Module.length R R := by
  let b := Module.Free.chooseBasis R M
  nontriviality R
  nontriviality M
  by_cases H : Module.length R R = ⊤
  · simp [b.repr.length_eq, H, rank_pos_of_free.ne']
  rw [← ne_eq]; rw [Module.length_ne_top_iff]; rw [isFiniteLength_iff_isNoetherian_isArtinian] at H
  cases H
  let b := Module.Free.chooseBasis R M
  rw [b.repr.length_eq]; rw [Module.length_finsupp]; rw [Free.rank_eq_card_chooseBasisIndex]; rw [ENat.card]

variable (R M) in
/--
lemma `Module.length_of_free_of_finite` / 引理 `Module.length_of_free_of_finite`

English:
lemma Module.length_of_free_of_finite
  proof: by
  rw [length_of_free]; rw [Cardinal.toENat_eq_natCast.mpr (finrank_eq_rank _ _).symm]

中文:
引理 模.length_of_free_of_finite
  证明: by
  rw [length_of_free]; rw [Cardinal.toENat_eq_natCast.mpr (finrank_eq_rank _ _).symm]

Depends on / 依赖: Cardinal, Cardinal.toENat_eq_natCast.mpr, finrank_eq_rank, length_of_free, toENat_eq_natCast
-/
lemma Module.length_of_free_of_finite
    [StrongRankCondition R] [Module.Free R M] [Module.Finite R M] :
    Module.length R M = Module.finrank R M * Module.length R R := by
  rw [length_of_free]; rw [Cardinal.toENat_eq_natCast.mpr (finrank_eq_rank _ _).symm]

/--
lemma `Module.length_eq_one_iff` / 引理 `Module.length_eq_one_iff`

English:
lemma Module.length_eq_one_iff
  proof: by
  rw [← WithBot.coe_inj]; rw [Module.coe_length]; rw [WithBot.coe_one]; rw [Order.krullDim_eq_one_iff_of_boundedOrder]; rw [isSimpleModule_iff]

中文:
引理 模.length_eq_one_iff
  证明: by
  rw [← WithBot.coe_inj]; rw [Module.coe_length]; rw [WithBot.coe_one]; rw [Order.krullDim_eq_one_iff_of_boundedOrder]; rw [isSimpleModule_iff]

Depends on / 依赖: Module, Module.coe_length, Order.krullDim_eq_one_iff_of_boundedOrder, WithBot, WithBot.coe_inj, WithBot.coe_one, coe_inj, coe_length, coe_one, isSimpleModule_iff, krullDim_eq_one_iff_of_boundedOrder
-/
lemma Module.length_eq_one_iff :
    Module.length R M = 1 ↔ IsSimpleModule R M := by
  rw [← WithBot.coe_inj]; rw [Module.coe_length]; rw [WithBot.coe_one]; rw [Order.krullDim_eq_one_iff_of_boundedOrder]; rw [isSimpleModule_iff]

variable (R M) in
@[simp]
/--
lemma `Module.length_eq_one` / 引理 `Module.length_eq_one`

English:
lemma Module.length_eq_one
  given: [IsSimpleModule R M]
  proof: Module.length_eq_one_iff.mpr ‹_›

中文:
引理 模.length_eq_one
  条件: [是单模 R M]
  证明: Module.length_eq_one_iff.mpr ‹_›

Depends on / 依赖: Module, Module.length_eq_one_iff.mpr, length_eq_one_iff
-/
lemma Module.length_eq_one [IsSimpleModule R M] :
    Module.length R M = 1 :=
  Module.length_eq_one_iff.mpr ‹_›

/--
lemma `Module.length_eq_rank` / 引理 `Module.length_eq_rank`

English:
lemma Module.length_eq_rank
  proof: by
  simp [Module.length_of_free]

中文:
引理 模.length_eq_rank
  证明: by
  simp [Module.length_of_free]

Depends on / 依赖: Module, Module.length_of_free, length_of_free
-/
lemma Module.length_eq_rank
    (K M : Type*) [DivisionRing K] [AddCommGroup M] [Module K M] :
    Module.length K M = (Module.rank K M).toENat := by
  simp [Module.length_of_free]

/--
lemma `Module.length_eq_finrank` / 引理 `Module.length_eq_finrank`

English:
lemma Module.length_eq_finrank
  proof: by
  simp [Module.length_of_free]

中文:
引理 模.length_eq_finrank
  证明: by
  simp [Module.length_of_free]

Depends on / 依赖: Module, Module.length_of_free, length_of_free
-/
lemma Module.length_eq_finrank
    (K M : Type*) [DivisionRing K] [AddCommGroup M] [Module K M] [Module.Finite K M] :
    Module.length K M = Module.finrank K M := by
  simp [Module.length_of_free]

/--
theorem `Submodule.length_le_length_restrictScalars` / 定理 `Submodule.length_le_length_restrictScalars`

English:
theorem Submodule.length_le_length_restrictScalars
  statement: (A : Type*) [Ring A] [SMul A R] [Module A M]
  proof: by
  rw [← WithBot.coe_le_coe]; rw [Module.coe_length]; rw [Module.coe_length]
  exact Order.krullDim_le_of_orderEmbedding (restrictScalarsEmbedding A R p)

中文:
定理 子模.length_le_length_restrictScalars
  结论: (A : 类型) [环 A] [标量乘法 A R] [模 A M]
  证明: by
  rw [← WithBot.coe_le_coe]; rw [Module.coe_length]; rw [Module.coe_length]
  exact Order.krullDim_le_of_orderEmbedding (restrictScalarsEmbedding A R p)

Depends on / 依赖: Module, Module.coe_length, Order.krullDim_le_of_orderEmbedding, WithBot, WithBot.coe_le_coe, coe_le_coe, coe_length, krullDim_le_of_orderEmbedding, restrictScalarsEmbedding
-/
theorem Submodule.length_le_length_restrictScalars (A : Type*) [Ring A] [SMul A R] [Module A M]
    [IsScalarTower A R M] (p : Submodule R M) :
    Module.length R p <= Module.length A (p.restrictScalars A) := by
  rw [← WithBot.coe_le_coe]; rw [Module.coe_length]; rw [Module.coe_length]
  exact Order.krullDim_le_of_orderEmbedding (restrictScalarsEmbedding A R p)

/--
theorem `Submodule.length_quotient_lt` / 定理 `Submodule.length_quotient_lt`

English:
theorem Submodule.length_quotient_lt
  statement: [IsArtinian R M] [IsNoetherian R M] (p : Submodule R M)
  proof: by
  rw [Module.length_quotient]; rw [Module.length]; rw [WithBot.lt_unbot_iff]; rw [← Order.coheight_bot_eq_krullDim]; rw [WithBot.coe_lt_coe]
  exact Order.coheight_strictAnti (bot_lt_iff_ne_bot.mpr h) (Order.coheight_lt_top p)

中文:
定理 子模.length_quotient_lt
  结论: [是Artin R M] [是Noether R M] (p : 子模 R M)
  证明: by
  rw [Module.length_quotient]; rw [Module.length]; rw [WithBot.lt_unbot_iff]; rw [← Order.coheight_bot_eq_krullDim]; rw [WithBot.coe_lt_coe]
  exact Order.coheight_strictAnti (bot_lt_iff_ne_bot.mpr h) (Order.coheight_lt_top p)

Depends on / 依赖: Module, Module.length, Module.length_quotient, Order.coheight_bot_eq_krullDim, Order.coheight_lt_top, Order.coheight_strictAnti, WithBot, WithBot.coe_lt_coe, WithBot.lt_unbot_iff, bot_lt_iff_ne_bot, bot_lt_iff_ne_bot.mpr, coe_lt_coe, coheight_bot_eq_krullDim, coheight_lt_top, coheight_strictAnti, length, length_quotient, lt_unbot_iff
-/
theorem Submodule.length_quotient_lt [IsArtinian R M] [IsNoetherian R M] (p : Submodule R M)
    (h : p != ⊥) : Module.length R (M ⧸ p) < Module.length R M := by
  rw [Module.length_quotient]; rw [Module.length]; rw [WithBot.lt_unbot_iff]; rw [← Order.coheight_bot_eq_krullDim]; rw [WithBot.coe_lt_coe]
  exact Order.coheight_strictAnti (bot_lt_iff_ne_bot.mpr h) (Order.coheight_lt_top p)
