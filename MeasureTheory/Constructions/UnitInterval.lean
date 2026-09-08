/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Gaëtan Serré
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# The canonical measure on the unit interval

This file provides a `MeasureTheory.MeasureSpace` instance on `unitInterval`,
and shows it is a probability measure with value zero on singletons.

It also contains some basic results on the volume of various interval sets.
-/

@[expose] public section

open scoped unitInterval
open MeasureTheory Measure Set

namespace unitInterval

/-
**unitInterval.** 是 Mathlib 中的一个实例，位于命名空间 `unitInterval`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : MeasureSpace I := Measure.Subtype.measureSpace
/-
**unitInterval.volume_def** 是 Mathlib 中的一个定理，位于命名空间 `unitInterval`。
形式化陈述：volume_def : (volume : Measure I) = volume.comap Subtype.val
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem volume_def : (volume : Measure I) = volume.comap Subtype.val := rfl
/-
**unitInterval.** 是 Mathlib 中的一个实例，位于命名空间 `unitInterval`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsProbabilityMeasure (volume : Measure I) where
  measure_univ := by
    rw [Measure.Subtype.volume_univ nullMeasurableSet_Icc, Real.volume_Icc, sub_zero,
      ENNReal.ofReal_one]
/-
**unitInterval.measurableEmbedding_coe** 是 Mathlib 中的一个引理，位于命名空间 `unitInterval`。
形式化陈述：measurableEmbedding_coe : MeasurableEmbedding ((↑) : I -> Real) where inje
ctive
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `measurable_subtype_coe`：measurable_subtype_coe {p : α -> Prop} : Measura
ble ((↑) : Subtype p -> α)
· 使用定理 `MeasurableSet.subtype_image`：MeasurableSet.subtype_image {s : Set α} {t 
: Set s} (hs : MeasurableSet s) : MeasurableSet t -> MeasurableSet (((↑) : s -> 
α) '' t)
· 使用定理 `measurableSet_Icc`：measurableSet_Icc [OrderClosedTopology α] : Measurabl
eSet (Icc a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
-/
lemma measurableEmbedding_coe : MeasurableEmbedding ((↑) : I → ℝ) where
  injective := Subtype.val_injective
  measurable := measurable_subtype_coe
  measurableSet_image' _ := measurableSet_Icc.subtype_image
/-
**unitInterval.volume_apply** 是 Mathlib 中的一个引理，位于命名空间 `unitInterval`。
形式化陈述：volume_apply {s : Set I} : volume s = volume (Subtype.val '' s)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableEmbedding.comap_apply`：comap_apply (μ : Measure β) (s : Set α)
 : comap f μ s = μ (f '' s)
· 使用引理 `unitInterval.measurableEmbedding_coe`：measurableEmbedding_coe : Measurab
leEmbedding ((↑) : I -> Real) where injective
-/
lemma volume_apply {s : Set I} : volume s = volume (Subtype.val '' s) :=
  measurableEmbedding_coe.comap_apply ..
/-
**unitInterval.measurePreserving_coe** 是 Mathlib 中的一个引理，位于命名空间 `unitInterval`。
形式化陈述：measurePreserving_coe : MeasurePreserving ((↑) : I -> Real) volume (volume
.restrict I)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.measurePreserving_subtype_coe`：measurePreserving_subtype_c
oe {s : Set α} (hs : MeasurableSet s) : MeasurePreserving (Subtype.val : s -> α)
 (μa.comap Subtype.val) (μa.restr…
· 使用定理 `measurableSet_Icc`：measurableSet_Icc [OrderClosedTopology α] : Measurabl
eSet (Icc a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
-/
lemma measurePreserving_coe : MeasurePreserving ((↑) : I → ℝ) volume (volume.restrict I) :=
  measurePreserving_subtype_coe measurableSet_Icc
/-
**unitInterval.** 是 Mathlib 中的一个实例，位于命名空间 `unitInterval`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NullSingletonClass (volume : Measure I) where
  measure_singleton x := by simp [volume_apply]

@[fun_prop]
/-
**unitInterval.measurable_symm** 是 Mathlib 中的一个定理，位于命名空间 `unitInterval`。
形式化陈述：measurable_symm : Measurable σ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `unitInterval.continuous_symm`：continuous_symm : Continuous σ
-/
theorem measurable_symm : Measurable σ := continuous_symm.measurable

set_option backward.isDefEq.respectTransparency.types false in
/-- `unitInterval.symm` bundled as a measurable equivalence. -/
@[simps apply]
/-
**unitInterval.symmMeasurableEquiv** 是 Mathlib 中的一个定义，位于命名空间 `unitInterval`。
形式化陈述：symmMeasurableEquiv : I ≃ᵐ I where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `unitInterval.symm_symm`：symm_symm (x : I) : σ (σ x) = x

--- 原说明 ---
`unitInterval.symm` bundled as a measurable equivalence.
-/
def symmMeasurableEquiv : I ≃ᵐ I where
  toFun := σ
  invFun := σ
  left_inv := symm_symm
  right_inv := symm_symm

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**unitInterval.symm_symmMeasurableEquiv** 是 Mathlib 中的一个引理，位于命名空间 `unitInterval`
。
形式化陈述：symm_symmMeasurableEquiv : symmMeasurableEquiv.symm = symmMeasurableEquiv
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma symm_symmMeasurableEquiv : symmMeasurableEquiv.symm = symmMeasurableEquiv := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**unitInterval.coe_symmMeasurableEquiv** 是 Mathlib 中的一个引理，位于命名空间 `unitInterval`。
形式化陈述：coe_symmMeasurableEquiv : symmMeasurableEquiv = σ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_symmMeasurableEquiv : symmMeasurableEquiv = σ := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**unitInterval.measurePreserving_symm** 是 Mathlib 中的一个引理，位于命名空间 `unitInterval`。
形式化陈述：measurePreserving_symm : MeasurePreserving symm volume volume where measur
able
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `unitInterval.measurable_symm`：measurable_symm : Measurable σ
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasurableEquiv.map_apply`：∀ {α : Type u_1} {β : Type u_2} {x : Measurab
leSpace α} [inst : MeasurableSpace β] {μ : MeasureTheory.Measure α}   (f : α ≃ᵐ 
β) (s : Set β),…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `unitInterval.coe_symmMeasurableEquiv`：coe_symmMeasurableEquiv : symmMeas
urableEquiv = σ
· 使用引理 `unitInterval.volume_apply`：volume_apply {s : Set I} : volume s = volume 
(Subtype.val '' s)
· 使用引理 `unitInterval.image_coe_preimage_symm`：image_coe_preimage_symm {s : Set I
} : Subtype.val '' σ ⁻¹' s = (1 - ·) ⁻¹' Subtype.val '' s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `Measurable.const_sub`：∀ {G : Type u_2} {α : Type u_3} [inst : Measurable
Space G] [inst_1 : Sub G] {m : MeasurableSpace α} {f : α → G}   [MeasurableSub G
], Measura…
· 使用定理 `ContinuousSub.measurableSub`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Sub γ]   [ContinuousSub 
γ], MeasurableSub…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `measurable_id'`：measurable_id' {_ : MeasurableSpace α} : Measurable fun 
a : α => a
· 使用定理 `MeasurableSet.subtype_image`：MeasurableSet.subtype_image {s : Set α} {t 
: Set s} (hs : MeasurableSet s) : MeasurableSet t -> MeasurableSet (((↑) : s -> 
α) '' t)
· 使用定理 `measurableSet_Icc`：measurableSet_Icc [OrderClosedTopology α] : Measurabl
eSet (Icc a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
· 使用定理 `MeasureTheory.Measure.measurePreserving_sub_left`：∀ {G : Type u_1} [inst
 : MeasurableSpace G] [inst_1 : SubtractionMonoid G] [MeasurableAdd G] [Measurab
leNeg G]   (μ : MeasureTheory.Measure …
· 使用定理 `ContinuousAdd.measurableAdd`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Add γ]   [SeparatelyCont
inuousAdd γ], Mea…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `ContinuousNeg.measurableNeg`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Neg γ]   [ContinuousNeg 
γ], MeasurableNeg…
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
（共 42 条，此处仅展示前 30 条）
-/
lemma measurePreserving_symm : MeasurePreserving symm volume volume where
  measurable := measurable_symm
  map_eq := by
    ext s hs
    apply symmMeasurableEquiv.map_apply _ |>.trans
    conv_lhs => rw [coe_symmMeasurableEquiv, volume_apply, image_coe_preimage_symm,
      ← map_apply (by fun_prop) (measurableSet_Icc.subtype_image hs),
      volume.measurePreserving_sub_left 1 |>.map_eq, ← volume_apply]

open Set

variable (x : I)

@[simp]
/-
**unitInterval.volume_Iic** 是 Mathlib 中的一个引理，位于命名空间 `unitInterval`。
形式化陈述：volume_Iic : volume (Iic x) = .ofReal x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `unitInterval.volume_apply`：volume_apply {s : Set I} : volume s = volume 
(Subtype.val '' s)
· 使用引理 `Set.image_subtype_val_Icc_Iic`：image_subtype_val_Icc_Iic {a b : α} (c : 
Icc a b) : Subtype.val '' Iic c = Icc a c
· 使用定理 `Real.volume_Icc`：volume_Icc {a b : Real} : volume (Icc a b) = ofReal (b 
- a)
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma volume_Iic : volume (Iic x) = .ofReal x := by
  simp only [volume_apply, image_subtype_val_Icc_Iic, Real.volume_Icc, sub_zero]

@[simp]
/-
**unitInterval.volume_Iio** 是 Mathlib 中的一个引理，位于命名空间 `unitInterval`。
形式化陈述：volume_Iio : volume (Iio x) = .ofReal x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `volume_image_subtype_coe`：volume_image_subtype_coe {s : Set α} (hs : Mea
surableSet s) (t : Set s) : volume ((↑) '' t : Set α) = volume t
· 使用定理 `measurableSet_Icc`：measurableSet_Icc [OrderClosedTopology α] : Measurabl
eSet (Icc a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用引理 `Set.image_subtype_val_Icc_Iio`：image_subtype_val_Icc_Iio {a b : α} (c : 
Icc a b) : Subtype.val '' Iio c = Ico a c
· 使用定理 `Real.volume_Ico`：volume_Ico {a b : Real} : volume (Ico a b) = ofReal (b 
- a)
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma volume_Iio : volume (Iio x) = .ofReal x := by
  simp only [← volume_image_subtype_coe measurableSet_Icc, image_subtype_val_Icc_Iio,
    Real.volume_Ico, sub_zero]

@[simp]
/-
**unitInterval.volume_Ici** 是 Mathlib 中的一个引理，位于命名空间 `unitInterval`。
形式化陈述：volume_Ici : volume (Ici x) = .ofReal (1 - x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `unitInterval.volume_apply`：volume_apply {s : Set I} : volume s = volume 
(Subtype.val '' s)
· 使用引理 `Set.image_subtype_val_Icc_Ici`：image_subtype_val_Icc_Ici {a b : α} (c : 
Icc a b) : Subtype.val '' Ici c = Icc c.1 b
· 使用定理 `Real.volume_Icc`：volume_Icc {a b : Real} : volume (Icc a b) = ofReal (b 
- a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma volume_Ici : volume (Ici x) = .ofReal (1 - x) := by
  simp only [volume_apply, image_subtype_val_Icc_Ici, Real.volume_Icc]

@[simp]
/-
**unitInterval.volume_Ioi** 是 Mathlib 中的一个引理，位于命名空间 `unitInterval`。
形式化陈述：volume_Ioi : volume (Ioi x) = .ofReal (1 - x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `unitInterval.volume_apply`：volume_apply {s : Set I} : volume s = volume 
(Subtype.val '' s)
· 使用引理 `Set.image_subtype_val_Icc_Ioi`：image_subtype_val_Icc_Ioi {a b : α} (c : 
Icc a b) : Subtype.val '' Ioi c = Ioc c.1 b
· 使用定理 `Real.volume_Ioc`：volume_Ioc {a b : Real} : volume (Ioc a b) = ofReal (b 
- a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma volume_Ioi : volume (Ioi x) = .ofReal (1 - x) := by
  simp only [volume_apply, image_subtype_val_Icc_Ioi, Real.volume_Ioc]

variable (y : I)

@[simp]
/-
**unitInterval.volume_Icc** 是 Mathlib 中的一个引理，位于命名空间 `unitInterval`。
形式化陈述：volume_Icc : volume (Icc x y) = .ofReal (y - x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `unitInterval.volume_apply`：volume_apply {s : Set I} : volume s = volume 
(Subtype.val '' s)
· 使用引理 `Set.image_subtype_val_Icc`：image_subtype_val_Icc {s : Set α} [OrdConnect
ed s] (x y : s) : Subtype.val '' Icc x y = Icc x.1 y
· 使用定理 `Real.volume_Icc`：volume_Icc {a b : Real} : volume (Icc a b) = ofReal (b 
- a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma volume_Icc : volume (Icc x y) = .ofReal (y - x) := by
  simp only [volume_apply, image_subtype_val_Icc, Real.volume_Icc]

@[simp]
/-
**unitInterval.volume_uIcc** 是 Mathlib 中的一个引理，位于命名空间 `unitInterval`。
形式化陈述：volume_uIcc : volume (uIcc x y) = edist y x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `unitInterval.volume_apply`：volume_apply {s : Set I} : volume s = volume 
(Subtype.val '' s)
· 使用引理 `Set.image_subtype_val_Icc`：image_subtype_val_Icc {s : Set α} [OrdConnect
ed s] (x y : s) : Subtype.val '' Icc x y = Icc x.1 y
· 使用定理 `Real.volume_Icc`：volume_Icc {a b : Real} : volume (Icc a b) = ofReal (b 
- a)
· 使用定理 `max_sub_min_eq_abs`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : Linea
rOrder α] [AddLeftMono α] [AddRightMono α] (a b : α),   max a b - min a b = |b -
 a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `edist_dist`：edist_dist (x y : α) : edist x y = ENNReal.ofReal (dist x y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma volume_uIcc : volume (uIcc x y) = edist y x := by
  simp only [uIcc, volume_apply, image_subtype_val_Icc, Icc.coe_inf, Icc.coe_sup, Real.volume_Icc,
    max_sub_min_eq_abs, edist_dist, Subtype.dist_eq, Real.dist_eq]

@[simp]
/-
**unitInterval.volume_Ico** 是 Mathlib 中的一个引理，位于命名空间 `unitInterval`。
形式化陈述：volume_Ico : volume (Ico x y) = .ofReal (y - x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `unitInterval.volume_apply`：volume_apply {s : Set I} : volume s = volume 
(Subtype.val '' s)
· 使用引理 `Set.image_subtype_val_Ico`：image_subtype_val_Ico {s : Set α} [OrdConnect
ed s] (x y : s) : Subtype.val '' Ico x y = Ico x.1 y
· 使用定理 `Real.volume_Ico`：volume_Ico {a b : Real} : volume (Ico a b) = ofReal (b 
- a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma volume_Ico : volume (Ico x y) = .ofReal (y - x) := by
  simp only [volume_apply, image_subtype_val_Ico, Real.volume_Ico]

@[simp]
/-
**unitInterval.volume_Ioc** 是 Mathlib 中的一个引理，位于命名空间 `unitInterval`。
形式化陈述：volume_Ioc : volume (Ioc x y) = .ofReal (y - x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `unitInterval.volume_apply`：volume_apply {s : Set I} : volume s = volume 
(Subtype.val '' s)
· 使用引理 `Set.image_subtype_val_Ioc`：image_subtype_val_Ioc {s : Set α} [OrdConnect
ed s] (x y : s) : Subtype.val '' Ioc x y = Ioc x.1 y
· 使用定理 `Real.volume_Ioc`：volume_Ioc {a b : Real} : volume (Ioc a b) = ofReal (b 
- a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma volume_Ioc : volume (Ioc x y) = .ofReal (y - x) := by
  simp only [volume_apply, image_subtype_val_Ioc, Real.volume_Ioc]

@[simp]
/-
**unitInterval.volume_uIoc** 是 Mathlib 中的一个引理，位于命名空间 `unitInterval`。
形式化陈述：volume_uIoc : volume (uIoc x y) = edist y x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `unitInterval.volume_apply`：volume_apply {s : Set I} : volume s = volume 
(Subtype.val '' s)
· 使用引理 `Set.image_subtype_val_Ioc`：image_subtype_val_Ioc {s : Set α} [OrdConnect
ed s] (x y : s) : Subtype.val '' Ioc x y = Ioc x.1 y
· 使用定理 `Real.volume_Ioc`：volume_Ioc {a b : Real} : volume (Ioc a b) = ofReal (b 
- a)
· 使用定理 `max_sub_min_eq_abs`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : Linea
rOrder α] [AddLeftMono α] [AddRightMono α] (a b : α),   max a b - min a b = |b -
 a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `edist_dist`：edist_dist (x y : α) : edist x y = ENNReal.ofReal (dist x y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma volume_uIoc : volume (uIoc x y) = edist y x := by
  simp only [uIoc, volume_apply, image_subtype_val_Ioc, Icc.coe_inf, Icc.coe_sup, Real.volume_Ioc,
    max_sub_min_eq_abs, edist_dist, Subtype.dist_eq, Real.dist_eq]


@[simp]
/-
**unitInterval.volume_Ioo** 是 Mathlib 中的一个引理，位于命名空间 `unitInterval`。
形式化陈述：volume_Ioo : volume (Ioo x y) = .ofReal (y - x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `unitInterval.volume_apply`：volume_apply {s : Set I} : volume s = volume 
(Subtype.val '' s)
· 使用引理 `Set.image_subtype_val_Ioo`：image_subtype_val_Ioo {s : Set α} [OrdConnect
ed s] (x y : s) : Subtype.val '' Ioo x y = Ioo x.1 y
· 使用定理 `Real.volume_Ioo`：volume_Ioo {a b : Real} : volume (Ioo a b) = ofReal (b 
- a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma volume_Ioo : volume (Ioo x y) = .ofReal (y - x) := by
  simp only [volume_apply, image_subtype_val_Ioo, Real.volume_Ioo]

@[simp]
/-
**unitInterval.volume_uIoo** 是 Mathlib 中的一个引理，位于命名空间 `unitInterval`。
形式化陈述：volume_uIoo : volume (uIoo x y) = edist y x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `unitInterval.volume_apply`：volume_apply {s : Set I} : volume s = volume 
(Subtype.val '' s)
· 使用引理 `Set.image_subtype_val_Ioo`：image_subtype_val_Ioo {s : Set α} [OrdConnect
ed s] (x y : s) : Subtype.val '' Ioo x y = Ioo x.1 y
· 使用定理 `Real.volume_Ioo`：volume_Ioo {a b : Real} : volume (Ioo a b) = ofReal (b 
- a)
· 使用定理 `max_sub_min_eq_abs`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : Linea
rOrder α] [AddLeftMono α] [AddRightMono α] (a b : α),   max a b - min a b = |b -
 a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `edist_dist`：edist_dist (x y : α) : edist x y = ENNReal.ofReal (dist x y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma volume_uIoo : volume (uIoo x y) = edist y x := by
  simp only [uIoo, volume_apply, image_subtype_val_Ioo, Icc.coe_inf, Icc.coe_sup, Real.volume_Ioo,
    max_sub_min_eq_abs, edist_dist, Subtype.dist_eq, Real.dist_eq]

end unitInterval

