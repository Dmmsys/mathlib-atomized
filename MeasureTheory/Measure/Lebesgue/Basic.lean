/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.LinearAlgebra.Matrix.Diagonal
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.MeasureTheory.Integral.Marginal
public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# Lebesgue measure on the real line and on `ℝⁿ`

We show that the Lebesgue measure on the real line (constructed as a particular case of additive
Haar measure on inner product spaces) coincides with the Stieltjes measure associated
to the function `x ↦ x`. We deduce properties of this measure on `ℝ`, and then of the product
Lebesgue measure on `ℝⁿ`. In particular, we prove that they are translation invariant.

We show that, on `ℝⁿ`, a linear map acts on Lebesgue measure by rescaling it through the absolute
value of its determinant, in `Real.map_linearMap_volume_pi_eq_smul_volume_pi`.

More properties of the Lebesgue measure are deduced from this in
`Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean`, where they are proved more generally for any
additive Haar measure on a finite-dimensional real vector space.
-/

@[expose] public section


assert_not_exists MeasureTheory.integral

noncomputable section

open Set Filter MeasureTheory MeasureTheory.Measure TopologicalSpace Metric

open ENNReal (ofReal)

open scoped ENNReal NNReal Topology

/-!
### Definition of the Lebesgue measure and lengths of intervals
-/


namespace Real

variable {ι : Type*} [Fintype ι]

/-- The volume on the real line (as a particular case of the volume on a finite-dimensional
inner product space) coincides with the Stieltjes measure coming from the identity function. -/
/-
**Real.volume_eq_stieltjes_id** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：volume_eq_stieltjes_id : (volume : Measure Real) = StieltjesFunction.id.me
asure
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.measure_ext_Ioo_rat`：measure_ext_Ioo_rat {μ ν : Measure Real} [IsLo
callyFiniteMeasure μ] (h : forall a b : Rat, μ (Ioo a b) = ν (Ioo a b)) : μ = ν
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StieltjesFunction.measure_Ioo`：measure_Ioo {a b : R} : f.measure (Ioo a 
b) = ofReal (leftLim f b - f a)
· 使用定理 `StieltjesFunction.id_leftLim`：id_leftLim (x : Real) : leftLim StieltjesF
unction.id x = x
· 使用定理 `StieltjesFunction.id_apply`：∀ (a : ℝ), ↑StieltjesFunction.id a = id a
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `MeasurableAdd.measurable_const_add`：∀ {M : Type u_2} {inst : MeasurableS
pace M} {inst_1 : Add M} [self : MeasurableAdd M] (c : M), Measurable fun x => c
 + x
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
· 使用定理 `measurableSet_Ioo`：measurableSet_Ioo [OrderClosedTopology α] : Measurabl
eSet (Ioo a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Set.preimage_const_add_Ioo`：∀ {α : Type u_1} [inst : AddCommGroup α] [in
st_1 : PartialOrder α] [IsOrderedAddMonoid α] (a b c : α),   (fun x => a + x) ⁻¹
' Set.Ioo b c = …
· 使用定理 `sub_sub_sub_cancel_right`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : 
G), a - c - (b - c) = a - b
（共 47 条，此处仅展示前 30 条）

--- 原说明 ---
The volume on the real line (as a particular case of the volume on a finite-dime
nsional
inner product space) coincides with the Stieltjes measure coming from the identi
ty function.
-/
theorem volume_eq_stieltjes_id : (volume : Measure ℝ) = StieltjesFunction.id.measure := by
  have : IsAddLeftInvariant StieltjesFunction.id.measure :=
    ⟨fun a =>
      Eq.symm <|
        Real.measure_ext_Ioo_rat fun p q => by
          simp only [Measure.map_apply (measurable_const_add a) measurableSet_Ioo,
            sub_sub_sub_cancel_right, StieltjesFunction.measure_Ioo, StieltjesFunction.id_leftLim,
            StieltjesFunction.id_apply, id, preimage_const_add_Ioo]⟩
  have A : StieltjesFunction.id.measure (stdOrthonormalBasis ℝ ℝ).toBasis.parallelepiped = 1 := by
    change StieltjesFunction.id.measure (parallelepiped (stdOrthonormalBasis ℝ ℝ)) = 1
    rcases parallelepiped_orthonormalBasis_one_dim (stdOrthonormalBasis ℝ ℝ) with (H | H) <;>
      simp only [H, StieltjesFunction.measure_Icc, StieltjesFunction.id_apply, id, tsub_zero,
        StieltjesFunction.id_leftLim, sub_neg_eq_add, zero_add, ENNReal.ofReal_one]
  conv_rhs =>
    rw [addHaarMeasure_unique StieltjesFunction.id.measure
        (stdOrthonormalBasis ℝ ℝ).toBasis.parallelepiped, A]
  simp only [volume, Module.Basis.addHaar, one_smul]
/-
**Real.volume_val** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：volume_val (s) : volume s = StieltjesFunction.id.measure s
参数：s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.volume_eq_stieltjes_id`：volume_eq_stieltjes_id : (volume : Measure 
Real) = StieltjesFunction.id.measure
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem volume_val (s) : volume s = StieltjesFunction.id.measure s := by
  simp [volume_eq_stieltjes_id]

@[simp]
/-
**Real.volume_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：volume_Ico {a b : Real} : volume (Ico a b) = ofReal (b - a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Real.volume_val`：volume_val (s) : volume s = StieltjesFunction.id.measur
e s
· 使用定理 `StieltjesFunction.measure_Ico`：measure_Ico (a b : R) : f.measure (Ico a 
b) = ofReal (leftLim f b - leftLim f a)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `StieltjesFunction.id_leftLim`：id_leftLim (x : Real) : leftLim StieltjesF
unction.id x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem volume_Ico {a b : ℝ} : volume (Ico a b) = ofReal (b - a) := by simp [volume_val]

@[simp]
/-
**Real.volume_real_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：volume_real_Ico {a b : Real} : volume.real (Ico a b) = max (b - a) 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.volume_Ico`：volume_Ico {a b : Real} : volume (Ico a b) = ofReal (b 
- a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem volume_real_Ico {a b : ℝ} : volume.real (Ico a b) = max (b - a) 0 := by
  simp [measureReal_def, ENNReal.toReal_ofReal']
/-
**Real.volume_real_Ico_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：volume_real_Ico_of_le {a b : Real} (hab : a <= b) : volume.real (Ico a b) 
= b - a
参数：hab : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.volume_real_Ico`：volume_real_Ico {a b : Real} : volume.real (Ico a 
b) = max (b - a) 0
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem volume_real_Ico_of_le {a b : ℝ} (hab : a ≤ b) : volume.real (Ico a b) = b - a := by
  simp [hab]

@[simp]
/-
**Real.volume_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：volume_Icc {a b : Real} : volume (Icc a b) = ofReal (b - a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Real.volume_val`：volume_val (s) : volume s = StieltjesFunction.id.measur
e s
· 使用定理 `StieltjesFunction.measure_Icc`：measure_Icc (a b : R) : f.measure (Icc a 
b) = ofReal (f b - leftLim f a)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `StieltjesFunction.id_apply`：∀ (a : ℝ), ↑StieltjesFunction.id a = id a
· 使用定理 `StieltjesFunction.id_leftLim`：id_leftLim (x : Real) : leftLim StieltjesF
unction.id x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem volume_Icc {a b : ℝ} : volume (Icc a b) = ofReal (b - a) := by simp [volume_val]

@[simp]
/-
**Real.volume_real_Icc** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：volume_real_Icc {a b : Real} : volume.real (Icc a b) = max (b - a) 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.volume_Icc`：volume_Icc {a b : Real} : volume (Icc a b) = ofReal (b 
- a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem volume_real_Icc {a b : ℝ} : volume.real (Icc a b) = max (b - a) 0 := by
  simp [measureReal_def, ENNReal.toReal_ofReal']
/-
**Real.volume_real_Icc_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：volume_real_Icc_of_le {a b : Real} (hab : a <= b) : volume.real (Icc a b) 
= b - a
参数：hab : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.volume_real_Icc`：volume_real_Icc {a b : Real} : volume.real (Icc a 
b) = max (b - a) 0
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem volume_real_Icc_of_le {a b : ℝ} (hab : a ≤ b) : volume.real (Icc a b) = b - a := by
  simp [hab]

@[simp]
/-
**Real.volume_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：volume_Ioo {a b : Real} : volume (Ioo a b) = ofReal (b - a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Real.volume_val`：volume_val (s) : volume s = StieltjesFunction.id.measur
e s
· 使用定理 `StieltjesFunction.measure_Ioo`：measure_Ioo {a b : R} : f.measure (Ioo a 
b) = ofReal (leftLim f b - f a)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `StieltjesFunction.id_leftLim`：id_leftLim (x : Real) : leftLim StieltjesF
unction.id x = x
· 使用定理 `StieltjesFunction.id_apply`：∀ (a : ℝ), ↑StieltjesFunction.id a = id a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem volume_Ioo {a b : ℝ} : volume (Ioo a b) = ofReal (b - a) := by simp [volume_val]

@[simp]
/-
**Real.volume_uIoo** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：volume_uIoo {a b : Real} : volume (uIoo a b) = ofReal |b - a|
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem volume_uIoo {a b : ℝ} : volume (uIoo a b) = ofReal |b - a| := by
  simp [uIoo, volume_Ioo, max_sub_min_eq_abs]

@[simp]
/-
**Real.volume_real_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：volume_real_Ioo {a b : Real} : volume.real (Ioo a b) = max (b - a) 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.volume_Ioo`：volume_Ioo {a b : Real} : volume (Ioo a b) = ofReal (b 
- a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem volume_real_Ioo {a b : ℝ} : volume.real (Ioo a b) = max (b - a) 0 := by
  simp [measureReal_def, ENNReal.toReal_ofReal']
/-
**Real.volume_real_Ioo_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：volume_real_Ioo_of_le {a b : Real} (hab : a <= b) : volume.real (Ioo a b) 
= b - a
参数：hab : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.volume_real_Ioo`：volume_real_Ioo {a b : Real} : volume.real (Ioo a 
b) = max (b - a) 0
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem volume_real_Ioo_of_le {a b : ℝ} (hab : a ≤ b) : volume.real (Ioo a b) = b - a := by
  simp [hab]

@[simp]
/-
**Real.volume_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：volume_Ioc {a b : Real} : volume (Ioc a b) = ofReal (b - a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Real.volume_val`：volume_val (s) : volume s = StieltjesFunction.id.measur
e s
· 使用定理 `StieltjesFunction.measure_Ioc`：measure_Ioc (a b : R) : f.measure (Ioc a 
b) = ofReal (f b - f a)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `StieltjesFunction.id_apply`：∀ (a : ℝ), ↑StieltjesFunction.id a = id a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem volume_Ioc {a b : ℝ} : volume (Ioc a b) = ofReal (b - a) := by simp [volume_val]

@[simp]
/-
**Real.volume_uIoc** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：volume_uIoc {a b : Real} : volume (uIoc a b) = ofReal |b - a|
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem volume_uIoc {a b : ℝ} : volume (uIoc a b) = ofReal |b - a| := by
  simp [uIoc, volume_Ioc, max_sub_min_eq_abs]

@[simp]
/-
**Real.volume_real_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：volume_real_Ioc {a b : Real} : volume.real (Ioc a b) = max (b - a) 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.volume_Ioc`：volume_Ioc {a b : Real} : volume (Ioc a b) = ofReal (b 
- a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem volume_real_Ioc {a b : ℝ} : volume.real (Ioc a b) = max (b - a) 0 := by
  simp [measureReal_def, ENNReal.toReal_ofReal']
/-
**Real.volume_real_Ioc_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：volume_real_Ioc_of_le {a b : Real} (hab : a <= b) : volume.real (Ioc a b) 
= b - a
参数：hab : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.volume_real_Ioc`：volume_real_Ioc {a b : Real} : volume.real (Ioc a 
b) = max (b - a) 0
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem volume_real_Ioc_of_le {a b : ℝ} (hab : a ≤ b) : volume.real (Ioc a b) = b - a := by
  simp [hab]
/-
**Real.volume_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：volume_singleton {a : Real} : volume ({a} : Set Real) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.NullSingletonClass.measure_singleton`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.NullSi
ngletonClass μ]   (x : α), μ {x} = 0
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.nullSingletonClass`：∀ {G : Type u
_1} [inst : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace 
G]   [IsTopologicalAddGroup G] [BorelSpace G] […
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
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
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem volume_singleton {a : ℝ} : volume ({a} : Set ℝ) = 0 := by simp
/-
**Real.volume_univ** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：volume_univ : volume (univ : Set Real) = ∞
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.eq_top_of_forall_nnreal_le`：eq_top_of_forall_nnreal_le {x : Real
>=0∞} (h : forall r : Real>=0, ↑r <= x) : x = ∞
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.volume_Icc`：volume_Icc {a b : Real} : volume (Icc a b) = ofReal (b 
- a)
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `ENNReal.ofReal_coe_nnreal`：∀ {p : NNReal}, ENNReal.ofReal ↑p = ↑p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem volume_univ : volume (univ : Set ℝ) = ∞ :=
  ENNReal.eq_top_of_forall_nnreal_le fun r =>
    calc
      (r : ℝ≥0∞) = volume (Icc (0 : ℝ) r) := by simp
      _ ≤ volume univ := measure_mono (subset_univ _)

@[simp]
/-
**Real.volume_ball** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：volume_ball (a r : Real) : volume (Metric.ball a r) = ofReal (2 * r)
参数：a r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.ball_eq_Ioo`：Real.ball_eq_Ioo (x r : Real) : ball x r = Ioo (x - r)
 (x + r)
· 使用定理 `Real.volume_Ioo`：volume_Ioo {a b : Real} : volume (Ioo a b) = ofReal (b 
- a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b + c = a - (b - c)
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
-/
theorem volume_ball (a r : ℝ) : volume (Metric.ball a r) = ofReal (2 * r) := by
  rw [ball_eq_Ioo, volume_Ioo, ← sub_add, add_sub_cancel_left, two_mul]

@[simp]
/-
**Real.volume_real_ball** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：volume_real_ball {a r : Real} (hr : 0 <= r) : volume.real (Metric.ball a r
) = 2 * r
参数：hr : 0 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.volume_ball`：volume_ball (a r : Real) : volume (Metric.ball a r) = 
ofReal (2 * r)
· 使用定理 `ENNReal.ofReal_mul`：ofReal_mul {p q : Real} (hp : 0 <= p) : ENNReal.ofRe
al (p * q) = ENNReal.ofReal p * ENNReal.ofReal q
· 使用定理 `ENNReal.ofReal_ofNat`：∀ (n : ℕ) [inst : n.AtLeastTwo], ENNReal.ofReal (O
fNat.ofNat n) = OfNat.ofNat n
· 使用定理 `ENNReal.toReal_mul`：toReal_mul : (a * b).toReal = a.toReal * b.toReal
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ENNReal.toReal_ofNat`：∀ (n : ℕ) [inst : n.AtLeastTwo], (OfNat.ofNat n).t
oReal = OfNat.ofNat n
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem volume_real_ball {a r : ℝ} (hr : 0 ≤ r) : volume.real (Metric.ball a r) = 2 * r := by
  simp [measureReal_def, hr]

@[simp]
/-
**Real.volume_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：volume_closedBall (a r : Real) : volume (Metric.closedBall a r) = ofReal (
2 * r)
参数：a r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.closedBall_eq_Icc`：Real.closedBall_eq_Icc {x r : Real} : closedBall
 x r = Icc (x - r) (x + r)
· 使用定理 `Real.volume_Icc`：volume_Icc {a b : Real} : volume (Icc a b) = ofReal (b 
- a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b + c = a - (b - c)
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
-/
theorem volume_closedBall (a r : ℝ) : volume (Metric.closedBall a r) = ofReal (2 * r) := by
  rw [closedBall_eq_Icc, volume_Icc, ← sub_add, add_sub_cancel_left, two_mul]

@[simp]
/-
**Real.volume_real_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：volume_real_closedBall {a r : Real} (hr : 0 <= r) : volume.real (Metric.cl
osedBall a r) = 2 * r
参数：hr : 0 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.volume_closedBall`：volume_closedBall (a r : Real) : volume (Metric.
closedBall a r) = ofReal (2 * r)
· 使用定理 `ENNReal.ofReal_mul`：ofReal_mul {p q : Real} (hp : 0 <= p) : ENNReal.ofRe
al (p * q) = ENNReal.ofReal p * ENNReal.ofReal q
· 使用定理 `ENNReal.ofReal_ofNat`：∀ (n : ℕ) [inst : n.AtLeastTwo], ENNReal.ofReal (O
fNat.ofNat n) = OfNat.ofNat n
· 使用定理 `ENNReal.toReal_mul`：toReal_mul : (a * b).toReal = a.toReal * b.toReal
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ENNReal.toReal_ofNat`：∀ (n : ℕ) [inst : n.AtLeastTwo], (OfNat.ofNat n).t
oReal = OfNat.ofNat n
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem volume_real_closedBall {a r : ℝ} (hr : 0 ≤ r) :
    volume.real (Metric.closedBall a r) = 2 * r := by
  simp [measureReal_def, hr]

@[simp]
/-
**Real.volume_eball** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：volume_eball (a : Real) (r : Real>=0∞) : volume (Metric.eball a r) = 2 * r
参数：a : Real；r : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.eball_top`：Metric.eball_top (x : α) : eball x ⊤ = univ
· 使用定理 `Real.volume_univ`：volume_univ : volume (univ : Set Real) = ∞
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `top_add`：top_add (a : α) : ⊤ + a = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Metric.eball_coe`：Metric.eball_coe {x : α} {ε : Real>=0} : eball x ε = b
all x ε
· 使用定理 `Real.volume_ball`：volume_ball (a r : Real) : volume (Metric.ball a r) = 
ofReal (2 * r)
· 使用定理 `NNReal.coe_add`：∀ (r₁ r₂ : NNReal), ↑(r₁ + r₂) = ↑r₁ + ↑r₂
· 使用定理 `ENNReal.ofReal_coe_nnreal`：∀ {p : NNReal}, ENNReal.ofReal ↑p = ↑p
· 使用定理 `ENNReal.coe_add`：∀ (x y : NNReal), ↑(x + y) = ↑x + ↑y
-/
theorem volume_eball (a : ℝ) (r : ℝ≥0∞) : volume (Metric.eball a r) = 2 * r := by
  rcases eq_or_ne r ∞ with (rfl | hr)
  · rw [Metric.eball_top, volume_univ, two_mul, _root_.top_add]
  · lift r to ℝ≥0 using hr
    rw [Metric.eball_coe, volume_ball, two_mul, ← NNReal.coe_add,
      ENNReal.ofReal_coe_nnreal, ENNReal.coe_add, two_mul]

@[deprecated (since := "2026-01-24")]
alias volume_emetric_ball := volume_eball

@[simp]
/-
**Real.volume_closedEBall** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：volume_closedEBall (a : Real) (r : Real>=0∞) : volume (Metric.closedEBall 
a r) = 2 * r
参数：a : Real；r : Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.closedEBall_top`：closedEBall_top (x : α) : closedEBall x ∞ = univ
· 使用定理 `Real.volume_univ`：volume_univ : volume (univ : Set Real) = ∞
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `top_add`：top_add (a : α) : ⊤ + a = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Metric.closedEBall_coe`：Metric.closedEBall_coe {x : α} {ε : Real>=0} : c
losedEBall x ε = closedBall x ε
· 使用定理 `Real.volume_closedBall`：volume_closedBall (a r : Real) : volume (Metric.
closedBall a r) = ofReal (2 * r)
· 使用定理 `NNReal.coe_add`：∀ (r₁ r₂ : NNReal), ↑(r₁ + r₂) = ↑r₁ + ↑r₂
· 使用定理 `ENNReal.ofReal_coe_nnreal`：∀ {p : NNReal}, ENNReal.ofReal ↑p = ↑p
· 使用定理 `ENNReal.coe_add`：∀ (x y : NNReal), ↑(x + y) = ↑x + ↑y
-/
theorem volume_closedEBall (a : ℝ) (r : ℝ≥0∞) : volume (Metric.closedEBall a r) = 2 * r := by
  rcases eq_or_ne r ∞ with (rfl | hr)
  · rw [Metric.closedEBall_top, volume_univ, two_mul, _root_.top_add]
  · lift r to ℝ≥0 using hr
    rw [Metric.closedEBall_coe, volume_closedBall, two_mul, ← NNReal.coe_add,
      ENNReal.ofReal_coe_nnreal, ENNReal.coe_add, two_mul]

@[deprecated (since := "2026-01-24")]
alias volume_emetric_closedBall := volume_closedEBall
/-
**Real.nullSingletonClass_volume** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
形式化陈述：nullSingletonClass_volume : NullSingletonClass (volume : Measure Real)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.volume_singleton`：volume_singleton {a : Real} : volume ({a} : Set R
eal) = 0
-/
instance nullSingletonClass_volume : NullSingletonClass (volume : Measure ℝ) :=
  ⟨fun _ => volume_singleton⟩

@[deprecated (since := "2026-06-09")]
alias noAtoms_volume := nullSingletonClass_volume

@[simp]
/-
**Real.volume_interval** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：volume_interval {a b : Real} : volume (uIcc a b) = ofReal |b - a|
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Icc_min_max`：Icc_min_max : Icc (min a b) (max a b) = [[a, b]]
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
-/
theorem volume_interval {a b : ℝ} : volume (uIcc a b) = ofReal |b - a| := by
  rw [← Icc_min_max, volume_Icc, max_sub_min_eq_abs]

@[simp]
/-
**Real.volume_real_interval** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：volume_real_interval {a b : Real} : volume.real (uIcc a b) = |b - a|
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.volume_interval`：volume_interval {a b : Real} : volume (uIcc a b) =
 ofReal |b - a|
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem volume_real_interval {a b : ℝ} : volume.real (uIcc a b) = |b - a| := by
  simp [measureReal_def]

@[simp]
/-
**Real.volume_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：volume_Ioi {a : Real} : volume (Ioi a) = ∞
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `le_of_tendsto'`：le_of_tendsto' {x : Filter β} [hx : NeBot x] (lim : Tend
sto f x (𝓝 a)) (h : forall c, f c <= b) : a <= b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `ENNReal.tendsto_nat_nhds_top`：tendsto_nat_nhds_top : Tendsto (fun n : Na
t => ↑n) atTop (𝓝 ∞)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.volume_Ioo`：volume_Ioo {a b : Real} : volume (Ioo a b) = ofReal (b 
- a)
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `ENNReal.ofReal_natCast`：∀ (n : ℕ), ENNReal.ofReal ↑n = ↑n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.Ioo_subset_Ioi_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo b a ⊆ Set.Ioi b
-/
theorem volume_Ioi {a : ℝ} : volume (Ioi a) = ∞ :=
  top_unique <|
    le_of_tendsto' ENNReal.tendsto_nat_nhds_top fun n =>
      calc
        (n : ℝ≥0∞) = volume (Ioo a (a + n)) := by simp
        _ ≤ volume (Ioi a) := measure_mono Ioo_subset_Ioi_self

@[simp]
/-
**Real.volume_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：volume_Ici {a : Real} : volume (Ici a) = ∞
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_congr`：measure_congr (H : s =ᵐ[μ] t) : μ s = μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Ioi_ae_eq_Ici`：Ioi_ae_eq_Ici : Ioi a =ᵐ[μ] Ici a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.volume_Ioi`：volume_Ioi {a : Real} : volume (Ioi a) = ∞
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem volume_Ici {a : ℝ} : volume (Ici a) = ∞ := by rw [← measure_congr Ioi_ae_eq_Ici]; simp

@[simp]
/-
**Real.volume_Iio** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：volume_Iio {a : Real} : volume (Iio a) = ∞
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `le_of_tendsto'`：le_of_tendsto' {x : Filter β} [hx : NeBot x] (lim : Tend
sto f x (𝓝 a)) (h : forall c, f c <= b) : a <= b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `ENNReal.tendsto_nat_nhds_top`：tendsto_nat_nhds_top : Tendsto (fun n : Na
t => ↑n) atTop (𝓝 ∞)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.volume_Ioo`：volume_Ioo {a b : Real} : volume (Ioo a b) = ofReal (b 
- a)
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用定理 `ENNReal.ofReal_natCast`：∀ (n : ℕ), ENNReal.ofReal ↑n = ↑n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.Ioo_subset_Iio_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo a b ⊆ Set.Iio b
-/
theorem volume_Iio {a : ℝ} : volume (Iio a) = ∞ :=
  top_unique <|
    le_of_tendsto' ENNReal.tendsto_nat_nhds_top fun n =>
      calc
        (n : ℝ≥0∞) = volume (Ioo (a - n) a) := by simp
        _ ≤ volume (Iio a) := measure_mono Ioo_subset_Iio_self

@[simp]
/-
**Real.volume_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：volume_Iic {a : Real} : volume (Iic a) = ∞
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_congr`：measure_congr (H : s =ᵐ[μ] t) : μ s = μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Iio_ae_eq_Iic`：Iio_ae_eq_Iic : Iio a =ᵐ[μ] Iic a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.volume_Iio`：volume_Iio {a : Real} : volume (Iio a) = ∞
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem volume_Iic {a : ℝ} : volume (Iic a) = ∞ := by rw [← measure_congr Iio_ae_eq_Iic]; simp
/-
**Real.locallyFinite_volume** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
形式化陈述：locallyFinite_volume : IsLocallyFiniteMeasure (volume : Measure Real)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `isOpen_Ioo`：isOpen_Ioo : IsOpen (Ioo a b)
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `sub_lt_self`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeft
StrictMono α] (a : α) {b : α}, 0 < b → a - b < a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `lt_add_of_pos_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : 
LT α] [AddLeftStrictMono α] (a : α) {b : α}, 0 < b → a < a + b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.volume_Ioo`：volume_Ioo {a b : Real} : volume (Ioo a b) = ofReal (b 
- a)
-/
instance locallyFinite_volume : IsLocallyFiniteMeasure (volume : Measure ℝ) :=
  ⟨fun x =>
    ⟨Ioo (x - 1) (x + 1),
      IsOpen.mem_nhds isOpen_Ioo ⟨sub_lt_self _ zero_lt_one, lt_add_of_pos_right _ zero_lt_one⟩, by
      simp only [Real.volume_Ioo, ENNReal.ofReal_lt_top]⟩⟩
/-
**Real.isFiniteMeasure_restrict_Icc** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
形式化陈述：isFiniteMeasure_restrict_Icc (x y : Real) : IsFiniteMeasure (volume.restri
ct (Icc x y))
参数：x y : Real。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `Real.volume_Icc`：volume_Icc {a b : Real} : volume (Icc a b) = ofReal (b 
- a)
-/
instance isFiniteMeasure_restrict_Icc (x y : ℝ) : IsFiniteMeasure (volume.restrict (Icc x y)) :=
  ⟨by simp⟩
/-
**Real.isFiniteMeasure_restrict_Ico** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
形式化陈述：isFiniteMeasure_restrict_Ico (x y : Real) : IsFiniteMeasure (volume.restri
ct (Ico x y))
参数：x y : Real。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `Real.volume_Ico`：volume_Ico {a b : Real} : volume (Ico a b) = ofReal (b 
- a)
-/
instance isFiniteMeasure_restrict_Ico (x y : ℝ) : IsFiniteMeasure (volume.restrict (Ico x y)) :=
  ⟨by simp⟩
/-
**Real.isFiniteMeasure_restrict_Ioc** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
形式化陈述：isFiniteMeasure_restrict_Ioc (x y : Real) : IsFiniteMeasure (volume.restri
ct (Ioc x y))
参数：x y : Real。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `Real.volume_Ioc`：volume_Ioc {a b : Real} : volume (Ioc a b) = ofReal (b 
- a)
-/
instance isFiniteMeasure_restrict_Ioc (x y : ℝ) : IsFiniteMeasure (volume.restrict (Ioc x y)) :=
  ⟨by simp⟩
/-
**Real.isFiniteMeasure_restrict_Ioo** 是 Mathlib 中的一个实例，位于命名空间 `Real`。
形式化陈述：isFiniteMeasure_restrict_Ioo (x y : Real) : IsFiniteMeasure (volume.restri
ct (Ioo x y))
参数：x y : Real。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `Real.volume_Ioo`：volume_Ioo {a b : Real} : volume (Ioo a b) = ofReal (b 
- a)
-/
instance isFiniteMeasure_restrict_Ioo (x y : ℝ) : IsFiniteMeasure (volume.restrict (Ioo x y)) :=
  ⟨by simp⟩
/-
**Real.volume_le_diam** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：volume_le_diam (s : Set Real) : volume s <= ediam s
参数：s : Set Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.ediam_eq`：ediam_eq {s : Set Real} (h : Bornology.IsBounded s) : Met
ric.ediam s = ENNReal.ofReal (sSup s - sInf s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.volume_Icc`：volume_Icc {a b : Real} : volume (Icc a b) = ofReal (b 
- a)
· 使用定理 `MeasureTheory.OuterMeasure.mono`：∀ {α : Type u_2} (self : MeasureTheory.
OuterMeasure α) {s₁ s₂ : Set α}, s₁ ⊆ s₂ → self.measureOf s₁ ≤ self.measureOf s₂
· 使用定理 `Bornology.IsBounded.subset_Icc_sInf_sSup`：∀ {α : Type u_1} [inst : Borno
logy α] [inst_1 : ConditionallyCompleteLattice α] [IsOrderBornology α] {s : Set 
α},   Bornology.IsBounded s → …
· 使用定理 `Metric.ediam_of_unbounded`：ediam_of_unbounded (h : ¬IsBounded s) : ediam
 s = ∞
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem volume_le_diam (s : Set ℝ) : volume s ≤ ediam s := by
  by_cases hs : Bornology.IsBounded s
  · rw [Real.ediam_eq hs, ← volume_Icc]
    exact volume.mono hs.subset_Icc_sInf_sSup
  · rw [Metric.ediam_of_unbounded hs]; exact le_top
/-
**Real._root_.Filter.Eventually.volume_pos_of_nhds_real** 是 Mathlib 中的一个定理，位于命名空
间 `Real`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Filter.Eventually.volume_pos_of_nhds_real {p : ℝ → Prop} {a : ℝ}
    (h : ∀ᶠ x in 𝓝 a, p x) : (0 : ℝ≥0∞) < volume { x | p x } := by
  rcases h.exists_Ioo_subset with ⟨l, u, hx, hs⟩
  grw [← hs]
  simpa [-mem_Ioo] using hx.1.trans hx.2

/-!
### Volume of a box in `ℝⁿ`
-/


/-
**Real.volume_Icc_pi** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：volume_Icc_pi {a b : ι -> Real} : volume (Icc a b) = ∏ i, ENNReal.ofReal (
b i - a i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.pi_univ_Icc`：pi_univ_Icc : (pi univ fun i => Icc (x i) (y i)) = Icc 
x y
· 使用定理 `MeasureTheory.volume_pi_pi`：volume_pi_pi [forall i, MeasureSpace (α i)] 
[forall i, SigmaFinite (volume : Measure (α i))] (s : forall i, Set (α i)) : vol
ume (pi univ s) …
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Real.volume_Icc`：volume_Icc {a b : Real} : volume (Icc a b) = ofReal (b 
- a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### Volume of a box in `ℝⁿ`
-/
theorem volume_Icc_pi {a b : ι → ℝ} : volume (Icc a b) = ∏ i, ENNReal.ofReal (b i - a i) := by
  rw [← pi_univ_Icc, volume_pi_pi]
  simp only [Real.volume_Icc]

@[simp]
/-
**Real.volume_Icc_pi_toReal** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：volume_Icc_pi_toReal {a b : ι -> Real} (h : a <= b) : (volume (Icc a b)).t
oReal = ∏ i, (b i - a i)
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.volume_Icc_pi`：volume_Icc_pi {a b : ι -> Real} : volume (Icc a b) =
 ∏ i, ENNReal.ofReal (b i - a i)
· 使用定理 `ENNReal.toReal_prod`：toReal_prod (s : Finset ι) (f : ι -> Real>=0∞) : (∏
 i in s, f i).toReal = ∏ i in s, (f i).toReal
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem volume_Icc_pi_toReal {a b : ι → ℝ} (h : a ≤ b) :
    (volume (Icc a b)).toReal = ∏ i, (b i - a i) := by
  simp only [volume_Icc_pi, ENNReal.toReal_prod, ENNReal.toReal_ofReal (sub_nonneg.2 (h _))]
/-
**Real.volume_pi_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：volume_pi_Ioo {a b : ι -> Real} : volume (pi univ fun i => Ioo (a i) (b i)
) = ∏ i, ENNReal.ofReal (b i - a i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.measure_congr`：measure_congr (H : s =ᵐ[μ] t) : μ s = μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.univ_pi_Ioo_ae_eq_Icc`：univ_pi_Ioo_ae_eq_Icc {f g 
: forall i, α i} : (pi univ fun i => Ioo (f i) (g i)) =ᵐ[Measure.pi μ] Icc f g
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `Real.volume_Icc_pi`：volume_Icc_pi {a b : ι -> Real} : volume (Icc a b) =
 ∏ i, ENNReal.ofReal (b i - a i)
-/
theorem volume_pi_Ioo {a b : ι → ℝ} :
    volume (pi univ fun i => Ioo (a i) (b i)) = ∏ i, ENNReal.ofReal (b i - a i) :=
  (measure_congr Measure.univ_pi_Ioo_ae_eq_Icc).trans volume_Icc_pi

@[simp]
/-
**Real.volume_pi_Ioo_toReal** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：volume_pi_Ioo_toReal {a b : ι -> Real} (h : a <= b) : (volume (pi univ fun
 i => Ioo (a i) (b i))).toReal = ∏ i, (b i - a i)
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.volume_pi_Ioo`：volume_pi_Ioo {a b : ι -> Real} : volume (pi univ fu
n i => Ioo (a i) (b i)) = ∏ i, ENNReal.ofReal (b i - a i)
· 使用定理 `ENNReal.toReal_prod`：toReal_prod (s : Finset ι) (f : ι -> Real>=0∞) : (∏
 i in s, f i).toReal = ∏ i in s, (f i).toReal
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem volume_pi_Ioo_toReal {a b : ι → ℝ} (h : a ≤ b) :
    (volume (pi univ fun i => Ioo (a i) (b i))).toReal = ∏ i, (b i - a i) := by
  simp only [volume_pi_Ioo, ENNReal.toReal_prod, ENNReal.toReal_ofReal (sub_nonneg.2 (h _))]
/-
**Real.volume_pi_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：volume_pi_Ioc {a b : ι -> Real} : volume (pi univ fun i => Ioc (a i) (b i)
) = ∏ i, ENNReal.ofReal (b i - a i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.measure_congr`：measure_congr (H : s =ᵐ[μ] t) : μ s = μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.univ_pi_Ioc_ae_eq_Icc`：univ_pi_Ioc_ae_eq_Icc {f g 
: forall i, α i} : (pi univ fun i => Ioc (f i) (g i)) =ᵐ[Measure.pi μ] Icc f g
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `Real.volume_Icc_pi`：volume_Icc_pi {a b : ι -> Real} : volume (Icc a b) =
 ∏ i, ENNReal.ofReal (b i - a i)
-/
theorem volume_pi_Ioc {a b : ι → ℝ} :
    volume (pi univ fun i => Ioc (a i) (b i)) = ∏ i, ENNReal.ofReal (b i - a i) :=
  (measure_congr Measure.univ_pi_Ioc_ae_eq_Icc).trans volume_Icc_pi

@[simp]
/-
**Real.volume_pi_Ioc_toReal** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：volume_pi_Ioc_toReal {a b : ι -> Real} (h : a <= b) : (volume (pi univ fun
 i => Ioc (a i) (b i))).toReal = ∏ i, (b i - a i)
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.volume_pi_Ioc`：volume_pi_Ioc {a b : ι -> Real} : volume (pi univ fu
n i => Ioc (a i) (b i)) = ∏ i, ENNReal.ofReal (b i - a i)
· 使用定理 `ENNReal.toReal_prod`：toReal_prod (s : Finset ι) (f : ι -> Real>=0∞) : (∏
 i in s, f i).toReal = ∏ i in s, (f i).toReal
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem volume_pi_Ioc_toReal {a b : ι → ℝ} (h : a ≤ b) :
    (volume (pi univ fun i => Ioc (a i) (b i))).toReal = ∏ i, (b i - a i) := by
  simp only [volume_pi_Ioc, ENNReal.toReal_prod, ENNReal.toReal_ofReal (sub_nonneg.2 (h _))]
/-
**Real.volume_pi_Ico** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：volume_pi_Ico {a b : ι -> Real} : volume (pi univ fun i => Ico (a i) (b i)
) = ∏ i, ENNReal.ofReal (b i - a i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.measure_congr`：measure_congr (H : s =ᵐ[μ] t) : μ s = μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.univ_pi_Ico_ae_eq_Icc`：univ_pi_Ico_ae_eq_Icc {f g 
: forall i, α i} : (pi univ fun i => Ico (f i) (g i)) =ᵐ[Measure.pi μ] Icc f g
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `Real.volume_Icc_pi`：volume_Icc_pi {a b : ι -> Real} : volume (Icc a b) =
 ∏ i, ENNReal.ofReal (b i - a i)
-/
theorem volume_pi_Ico {a b : ι → ℝ} :
    volume (pi univ fun i => Ico (a i) (b i)) = ∏ i, ENNReal.ofReal (b i - a i) :=
  (measure_congr Measure.univ_pi_Ico_ae_eq_Icc).trans volume_Icc_pi

@[simp]
/-
**Real.volume_pi_Ico_toReal** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：volume_pi_Ico_toReal {a b : ι -> Real} (h : a <= b) : (volume (pi univ fun
 i => Ico (a i) (b i))).toReal = ∏ i, (b i - a i)
参数：h : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.volume_pi_Ico`：volume_pi_Ico {a b : ι -> Real} : volume (pi univ fu
n i => Ico (a i) (b i)) = ∏ i, ENNReal.ofReal (b i - a i)
· 使用定理 `ENNReal.toReal_prod`：toReal_prod (s : Finset ι) (f : ι -> Real>=0∞) : (∏
 i in s, f i).toReal = ∏ i in s, (f i).toReal
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `ENNReal.toReal_ofReal`：toReal_ofReal {r : Real} (h : 0 <= r) : (ENNReal.
ofReal r).toReal = r
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem volume_pi_Ico_toReal {a b : ι → ℝ} (h : a ≤ b) :
    (volume (pi univ fun i => Ico (a i) (b i))).toReal = ∏ i, (b i - a i) := by
  simp only [volume_pi_Ico, ENNReal.toReal_prod, ENNReal.toReal_ofReal (sub_nonneg.2 (h _))]

@[simp]
nonrec theorem volume_pi_ball (a : ι → ℝ) {r : ℝ} (hr : 0 < r) :
    volume (Metric.ball a r) = ENNReal.ofReal ((2 * r) ^ Fintype.card ι) := by
  simp only [MeasureTheory.volume_pi_ball a hr, volume_ball, Finset.prod_const]
  exact (ENNReal.ofReal_pow (mul_nonneg zero_le_two hr.le) _).symm

@[simp]
nonrec theorem volume_pi_closedBall (a : ι → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    volume (Metric.closedBall a r) = ENNReal.ofReal ((2 * r) ^ Fintype.card ι) := by
  simp only [MeasureTheory.volume_pi_closedBall a hr, volume_closedBall, Finset.prod_const]
  exact (ENNReal.ofReal_pow (mul_nonneg zero_le_two hr) _).symm
/-
**Real.volume_pi_le_prod_diam** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：volume_pi_le_prod_diam (s : Set (ι -> Real)) : volume s <= ∏ i : ι, ediam 
(Function.eval i '' s)
参数：s : Set (ι -> Real)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.OuterMeasure.mono`：∀ {α : Type u_2} (self : MeasureTheory.
OuterMeasure α) {s₁ s₂ : Set α}, s₁ ⊆ s₂ → self.measureOf s₁ ≤ self.measureOf s₂
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.subset_pi_eval_image`：subset_pi_eval_image (s : Set ι) (u : Set (for
all i, α i)) : u subseteq pi s fun i => eval i '' u
· 使用定理 `Set.pi_mono`：pi_mono (h : forall i in s, t₁ i subseteq t₂ i) : pi s t₁ s
ubseteq pi s t₂
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `MeasureTheory.volume_pi_pi`：volume_pi_pi [forall i, MeasureSpace (α i)] 
[forall i, SigmaFinite (volume : Measure (α i))] (s : forall i, Set (α i)) : vol
ume (pi univ s) …
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `Finset.prod_le_prod'`：prod_le_prod' [MulLeftMono N] (h : forall i in s, 
f i <= g i) : ∏ i in s, f i <= ∏ i in s, g i
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Real.volume_le_diam`：volume_le_diam (s : Set Real) : volume s <= ediam s
· 使用定理 `Metric.ediam_closure`：Metric.ediam_closure (s : Set α) : ediam (closure 
s) = ediam s
-/
theorem volume_pi_le_prod_diam (s : Set (ι → ℝ)) :
    volume s ≤ ∏ i : ι, ediam (Function.eval i '' s) :=
  calc
    volume s ≤ volume (pi univ fun i => closure (Function.eval i '' s)) :=
      volume.mono <|
        Subset.trans (subset_pi_eval_image univ s) <| pi_mono fun _ _ => subset_closure
    _ = ∏ i, volume (closure <| Function.eval i '' s) := volume_pi_pi _
    _ ≤ ∏ i : ι, ediam (Function.eval i '' s) :=
      Finset.prod_le_prod' fun _ _ => (volume_le_diam _).trans_eq (ediam_closure _)
/-
**Real.volume_pi_le_diam_pow** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：volume_pi_le_diam_pow (s : Set (ι -> Real)) : volume s <= ediam s ^ Fintyp
e.card ι
参数：s : Set (ι -> Real)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.volume_pi_le_prod_diam`：volume_pi_le_prod_diam (s : Set (ι -> Real)
) : volume s <= ∏ i : ι, ediam (Function.eval i '' s)
· 使用定理 `Finset.prod_le_prod'`：prod_le_prod' [MulLeftMono N] (h : forall i in s, 
f i <= g i) : ∏ i in s, f i <= ∏ i in s, g i
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `LipschitzWith.ediam_image_le`：ediam_image_le (hf : LipschitzWith K f) (s
 : Set α) : Metric.ediam (f '' s) <= K * Metric.ediam s
· 使用定理 `LipschitzWith.eval`：∀ {ι : Type x} {α : ι → Type u} [inst : (i : ι) → Ps
eudoEMetricSpace (α i)] [inst_1 : Fintype ι] (i : ι),   LipschitzWith 1 (Functio
n.eval i…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem volume_pi_le_diam_pow (s : Set (ι → ℝ)) : volume s ≤ ediam s ^ Fintype.card ι :=
  calc
    volume s ≤ ∏ i : ι, ediam (Function.eval i '' s) := volume_pi_le_prod_diam s
    _ ≤ ∏ _i : ι, (1 : ℝ≥0) * ediam s :=
      (Finset.prod_le_prod' fun i _ => (LipschitzWith.eval i).ediam_image_le s)
    _ = ediam s ^ Fintype.card ι := by
      simp only [ENNReal.coe_one, one_mul, Finset.prod_const, Fintype.card]

/-!
### Images of the Lebesgue measure under multiplication in ℝ
-/


/-
**Real.smul_map_volume_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：smul_map_volume_mul_left {a : Real} (h : a != 0) : ENNReal.ofReal |a| • Me
asure.map (a * ·) volume = volume
参数：h : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Real.measure_ext_Ioo_rat`：measure_ext_Ioo_rat {μ ν : Measure Real} [IsLo
callyFiniteMeasure μ] (h : forall a b : Rat, μ (Ioo a b) = ν (Ioo a b)) : μ = ν
· 使用引理 `lt_or_gt_of_ne`：lt_or_gt_of_ne (h : a != b) : a < b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.volume_Ioo`：volume_Ioo {a b : Real} : volume (Ioo a b) = ofReal (b 
- a)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `abs_of_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], a < 0 → |a| = -a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `MeasurableMul.measurable_const_mul`：∀ {M : Type u_2} {inst : MeasurableS
pace M} {inst_1 : Mul M} [self : MeasurableMul M] (c : M), Measurable fun x => c
 * x
· 使用定理 `ContinuousMul.measurableMul`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Mul γ]   [SeparatelyCont
inuousMul γ], Mea…
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `measurableSet_Ioo`：measurableSet_Ioo [OrderClosedTopology α] : Measurabl
eSet (Ioo a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Set.preimage_const_mul_Ioo_of_neg`：preimage_const_mul_Ioo_of_neg (a b : 
α) {c : α} (h : c < 0) : (c * ·) ⁻¹' Ioo a b = Ioo (b / c) (a / c)
· 使用定理 `ENNReal.ofReal_mul`：ofReal_mul {p q : Real} (hp : 0 <= p) : ENNReal.ofRe
al (p * q) = ENNReal.ofReal p * ENNReal.ofReal q
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStri
ctMono α] {a : α}, 0 < -a ↔ a < 0
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
（共 43 条，此处仅展示前 30 条）

--- 原说明 ---
### Images of the Lebesgue measure under multiplication in ℝ
-/
theorem smul_map_volume_mul_left {a : ℝ} (h : a ≠ 0) :
    ENNReal.ofReal |a| • Measure.map (a * ·) volume = volume := by
  refine (Real.measure_ext_Ioo_rat fun p q => ?_).symm
  rcases lt_or_gt_of_ne h with h | h
  · simp only [Real.volume_Ioo, Measure.smul_apply, ← ENNReal.ofReal_mul (le_of_lt <| neg_pos.2 h),
      Measure.map_apply (measurable_const_mul a) measurableSet_Ioo, neg_sub_neg, neg_mul,
      preimage_const_mul_Ioo_of_neg _ _ h, abs_of_neg h, mul_sub, smul_eq_mul,
      mul_div_cancel₀ _ (ne_of_lt h)]
  · simp only [Real.volume_Ioo, Measure.smul_apply, ← ENNReal.ofReal_mul (le_of_lt h),
      Measure.map_apply (measurable_const_mul a) measurableSet_Ioo, preimage_const_mul_Ioo₀ _ _ h,
      abs_of_pos h, mul_sub, mul_div_cancel₀ _ (ne_of_gt h), smul_eq_mul]
/-
**Real.map_volume_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：map_volume_mul_left {a : Real} (h : a != 0) : Measure.map (a * ·) volume =
 ENNReal.ofReal |a⁻¹| • volume
参数：h : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.smul_map_volume_mul_left`：smul_map_volume_mul_left {a : Real} (h : 
a != 0) : ENNReal.ofReal |a| • Measure.map (a * ·) volume = volume
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `ENNReal.ofReal_mul`：ofReal_mul {p q : Real} (hp : 0 <= p) : ENNReal.ofRe
al (p * q) = ENNReal.ofReal p * ENNReal.ofReal q
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `ENNReal.ofReal_one`：ENNReal.ofReal 1 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem map_volume_mul_left {a : ℝ} (h : a ≠ 0) :
    Measure.map (a * ·) volume = ENNReal.ofReal |a⁻¹| • volume := by
  conv_rhs =>
    rw [← Real.smul_map_volume_mul_left h, smul_smul, ← ENNReal.ofReal_mul (abs_nonneg _), ←
      abs_mul, inv_mul_cancel₀ h, abs_one, ENNReal.ofReal_one, one_smul]

@[simp]
/-
**Real.volume_preimage_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：volume_preimage_mul_left {a : Real} (h : a != 0) (s : Set Real) : volume (
(a * ·) ⁻¹' s) = ENNReal.ofReal (abs a⁻¹) * volume s
参数：h : a != 0；s : Set Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasurableEquiv.map_apply`：∀ {α : Type u_1} {β : Type u_2} {x : Measurab
leSpace α} [inst : MeasurableSpace β] {μ : MeasureTheory.Measure α}   (f : α ≃ᵐ 
β) (s : Set β),…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.map_volume_mul_left`：map_volume_mul_left {a : Real} (h : a != 0) : 
Measure.map (a * ·) volume = ENNReal.ofReal |a⁻¹| • volume
-/
theorem volume_preimage_mul_left {a : ℝ} (h : a ≠ 0) (s : Set ℝ) :
    volume ((a * ·) ⁻¹' s) = ENNReal.ofReal (abs a⁻¹) * volume s :=
  calc
    volume ((a * ·) ⁻¹' s) = Measure.map (a * ·) volume s :=
      ((Homeomorph.mulLeft₀ a h).toMeasurableEquiv.map_apply s).symm
    _ = ENNReal.ofReal (abs a⁻¹) * volume s := by rw [map_volume_mul_left h]; rfl
/-
**Real.smul_map_volume_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：smul_map_volume_mul_right {a : Real} (h : a != 0) : ENNReal.ofReal |a| • M
easure.map (· * a) volume = volume
参数：h : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Real.smul_map_volume_mul_left`：smul_map_volume_mul_left {a : Real} (h : 
a != 0) : ENNReal.ofReal |a| • Measure.map (a * ·) volume = volume
-/
theorem smul_map_volume_mul_right {a : ℝ} (h : a ≠ 0) :
    ENNReal.ofReal |a| • Measure.map (· * a) volume = volume := by
  simpa only [mul_comm] using Real.smul_map_volume_mul_left h
/-
**Real.map_volume_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：map_volume_mul_right {a : Real} (h : a != 0) : Measure.map (· * a) volume 
= ENNReal.ofReal |a⁻¹| • volume
参数：h : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Real.map_volume_mul_left`：map_volume_mul_left {a : Real} (h : a != 0) : 
Measure.map (a * ·) volume = ENNReal.ofReal |a⁻¹| • volume
-/
theorem map_volume_mul_right {a : ℝ} (h : a ≠ 0) :
    Measure.map (· * a) volume = ENNReal.ofReal |a⁻¹| • volume := by
  simpa only [mul_comm] using Real.map_volume_mul_left h

@[simp]
/-
**Real.volume_preimage_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：volume_preimage_mul_right {a : Real} (h : a != 0) (s : Set Real) : volume 
((· * a) ⁻¹' s) = ENNReal.ofReal (abs a⁻¹) * volume s
参数：h : a != 0；s : Set Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasurableEquiv.map_apply`：∀ {α : Type u_1} {β : Type u_2} {x : Measurab
leSpace α} [inst : MeasurableSpace β] {μ : MeasureTheory.Measure α}   (f : α ≃ᵐ 
β) (s : Set β),…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.map_volume_mul_right`：map_volume_mul_right {a : Real} (h : a != 0) 
: Measure.map (· * a) volume = ENNReal.ofReal |a⁻¹| • volume
-/
theorem volume_preimage_mul_right {a : ℝ} (h : a ≠ 0) (s : Set ℝ) :
    volume ((· * a) ⁻¹' s) = ENNReal.ofReal (abs a⁻¹) * volume s :=
  calc
    volume ((· * a) ⁻¹' s) = Measure.map (· * a) volume s :=
      ((Homeomorph.mulRight₀ a h).toMeasurableEquiv.map_apply s).symm
    _ = ENNReal.ofReal (abs a⁻¹) * volume s := by rw [map_volume_mul_right h]; rfl

/-!
### Images of the Lebesgue measure under translation/linear maps in ℝⁿ
-/


open Matrix

/-- A diagonal matrix rescales Lebesgue according to its determinant. This is a special case of
`Real.map_matrix_volume_pi_eq_smul_volume_pi`, that one should use instead (and whose proof
uses this particular case). -/
/-
**Real.smul_map_diagonal_volume_pi** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：smul_map_diagonal_volume_pi [DecidableEq ι] {D : ι -> Real} (h : det (diag
onal D) != 0) : ENNReal.ofReal (abs (det (diagonal D))) • Measure.map (toLin' (d
iagonal D)) volume = volume
参数：h : det (diagonal D) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `MeasureTheory.Measure.pi_eq`：pi_eq [forall i, SigmaFinite (μ i)] {μ' : M
easure (forall i, α i)} (h : forall s : forall i, Set (α i), (forall i, Measurab
leSet (s i)) -> μ…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.det_diagonal`：det_diagonal {d : n -> R} : det (diagonal d) = ∏ i,
 d i
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `MeasureTheory.Measure.map_apply`：map_apply (hf : Measurable f) {s : Set 
β} (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `LinearMap.continuous_on_pi`：LinearMap.continuous_on_pi {ι : Type*} {R : 
Type*} {M : Type*} [Finite ι] [Semiring R] [TopologicalSpace R] [AddCommMonoid M
] [Module R M] […
· 使用定理 `Pi.continuousAdd'`：∀ {ι : Type u_1} {M : Type u_3} [inst : TopologicalSp
ace M] [inst_1 : Add M] [ContinuousAdd M], ContinuousAdd (ι → M)
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
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
（共 59 条，此处仅展示前 30 条）

--- 原说明 ---
A diagonal matrix rescales Lebesgue according to its determinant. This is a spec
ial case of
`Real.map_matrix_volume_pi_eq_smul_volume_pi`, that one should use instead (and 
whose proof
uses this particular case).
-/
theorem smul_map_diagonal_volume_pi [DecidableEq ι] {D : ι → ℝ} (h : det (diagonal D) ≠ 0) :
    ENNReal.ofReal (abs (det (diagonal D))) • Measure.map (toLin' (diagonal D)) volume =
      volume := by
  refine (Measure.pi_eq fun s hs => ?_).symm
  simp only [det_diagonal, Measure.coe_smul, smul_eq_mul, Pi.smul_apply]
  rw [Measure.map_apply _ (MeasurableSet.univ_pi hs)]
  swap; · exact Continuous.measurable (LinearMap.continuous_on_pi _)
  have :
    (Matrix.toLin' (diagonal D) ⁻¹' Set.pi Set.univ fun i : ι => s i) =
      Set.pi Set.univ fun i : ι => (D i * ·) ⁻¹' s i := by
    ext f
    simp only [LinearMap.coe_proj, smul_eq_mul, LinearMap.smul_apply, mem_univ_pi,
      mem_preimage, LinearMap.pi_apply, diagonal_toLin']
  have B : ∀ i, ofReal (abs (D i)) * volume ((D i * ·) ⁻¹' s i) = volume (s i) := by
    intro i
    have A : D i ≠ 0 := by
      simp only [det_diagonal, Ne] at h
      exact Finset.prod_ne_zero_iff.1 h i (Finset.mem_univ i)
    rw [volume_preimage_mul_left A, ← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _), ← abs_mul,
      mul_inv_cancel₀ A, abs_one, ENNReal.ofReal_one, one_mul]
  rw [this, volume_pi_pi, Finset.abs_prod,
    ENNReal.ofReal_prod_of_nonneg fun i _ => abs_nonneg (D i), ← Finset.prod_mul_distrib]
  simp only [B]

/-- A transvection preserves Lebesgue measure. -/
/-
**Real.volume_preserving_transvectionStruct** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：volume_preserving_transvectionStruct [DecidableEq ι] (t : TransvectionStru
ct ι Real) : MeasurePreserving (toLin' t.toMatrix)
参数：t : TransvectionStruct ι Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `LinearMap.continuous_of_finiteDimensional`：LinearMap.continuous_of_finit
eDimensional [T2Space E] [FiniteDimensional 𝕜 E] (f : E ->ₗ[𝕜] F') : Continuous 
f
· 使用定理 `Pi.topologicalAddGroup`：∀ {β : Type v} {C : β → Type u_1} [inst : (b : β
) → TopologicalSpace (C b)] [inst_1 : (b : β) → AddGroup (C b)]   [∀ (b : β), Is
TopologicalA…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `instContinuousSMulForall`：∀ {M : Type u_1} [inst : TopologicalSpace M] {
ι : Type u_5} {γ : ι → Type u_6}   [inst_1 : (i : ι) → TopologicalSpace (γ i)] [
inst_2 : (i : …
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.pi_eq`：pi_eq [forall i, SigmaFinite (μ i)] {μ' : M
easure (forall i, α i)} (h : forall s : forall i, Set (α i), (forall i, Measurab
leSet (s i)) -> μ…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `MeasurableSet.pi`：∀ {δ : Type u_4} {X : δ → Type u_6} [inst : (a : δ) → 
MeasurableSpace (X a)] {s : Set δ} {t : (i : δ) → Set (X i)},   s.Countable → (∀
 i ∈ s…
· 使用定理 `Set.countable_univ`：countable_univ [Countable α] : (univ : Set α).Counta
ble
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.lintegral_indicator_one`：lintegral_indicator_one {s : Set 
α} (hs : MeasurableSet s) : ∫⁻ a, s.indicator 1 a ∂μ = μ s
（共 61 条，此处仅展示前 30 条）

--- 原说明 ---
A transvection preserves Lebesgue measure.
-/
theorem volume_preserving_transvectionStruct [DecidableEq ι] (t : TransvectionStruct ι ℝ) :
    MeasurePreserving (toLin' t.toMatrix) := by
  /- We use `lmarginal` to conveniently use Fubini's theorem.
    Along the coordinate where there is a shearing, it acts like a
    translation, and therefore preserves Lebesgue. -/
  have ht : Measurable (toLin' t.toMatrix) :=
    (toLin' t.toMatrix).continuous_of_finiteDimensional.measurable
  refine ⟨ht, ?_⟩
  refine (pi_eq fun s hs ↦ ?_).symm
  have h2s : MeasurableSet (univ.pi s) := .pi countable_univ fun i _ ↦ hs i
  simp_rw [← pi_pi, ← lintegral_indicator_one h2s]
  rw [lintegral_map (measurable_one.indicator h2s) ht, volume_pi]
  refine lintegral_eq_of_lmarginal_eq {t.i} ((measurable_one.indicator h2s).comp ht)
    (measurable_one.indicator h2s) ?_
  simp_rw [lmarginal_singleton]
  ext x
  cases t with | mk t_i t_j t_hij t_c =>
  simp [transvection, single_mulVec, t_hij.symm, ← Function.update_add,
    lintegral_add_right_eq_self fun xᵢ ↦ indicator (univ.pi s) 1 (Function.update x t_i xᵢ)]

/-- Any invertible matrix rescales Lebesgue measure through the absolute value of its
determinant. -/
/-
**Real.map_matrix_volume_pi_eq_smul_volume_pi** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：map_matrix_volume_pi_eq_smul_volume_pi [DecidableEq ι] {M : Matrix ι ι Rea
l} (hM : det M != 0) : Measure.map (toLin' M) volume = ENNReal.ofReal (abs (det 
M)⁻¹) • volume
参数：hM : det M != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.diagonal_transvection_induction_of_det_ne_zero`：diagonal_transvec
tion_induction_of_det_ne_zero (P : Matrix n n 𝕜 -> Prop) (M : Matrix n n 𝕜) (hMd
et : det M != 0) (hdiag : forall D : n -> 𝕜…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.smul_map_diagonal_volume_pi`：smul_map_diagonal_volume_pi [Decidable
Eq ι] {D : ι -> Real} (h : det (diagonal D) != 0) : ENNReal.ofReal (abs (det (di
agonal D))) • Measure.…
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `ENNReal.ofReal_mul`：ofReal_mul {p q : Real} (hp : 0 <= p) : ENNReal.ofRe
al (p * q) = ENNReal.ofReal p * ENNReal.ofReal q
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `ENNReal.ofReal_one`：ENNReal.ofReal 1 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.TransvectionStruct.det`：∀ {n : Type u_1} {R : Type u₂} [inst : De
cidableEq n] [inst_1 : CommRing R] [inst_2 : Fintype n]   (t : Matrix.Transvecti
onStruct n R), t.to…
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.MeasurePreserving.map_eq`：∀ {α : Type u_1} {β : Type u_2} 
[inst : MeasurableSpace α] [inst_1 : MeasurableSpace β] {f : α → β}   {μa : auto
Param (MeasureTheory.Measure…
· 使用定理 `Real.volume_preserving_transvectionStruct`：volume_preserving_transvectio
nStruct [DecidableEq ι] (t : TransvectionStruct ι Real) : MeasurePreserving (toL
in' t.toMatrix)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.toLin'_mul`：∀ {R : Type u_1} [inst : CommSemiring R] {l : Type u_
3} {m : Type u_4} {n : Type u_5} [inst_1 : DecidableEq n]   [inst_2 : Fintype n]
 [inst_…
· 使用定理 `Matrix.det_mul`：det_mul (M N : Matrix n n R) : det (M * N) = det M * det
 N
· 使用定理 `LinearMap.coe_comp`：coe_comp : (f.comp g : M₁ -> M₃) = f ∘ g
· 使用定理 `MeasureTheory.Measure.map_map`：map_map {g : β -> γ} {f : α -> β} (hg : M
easurable g) (hf : Measurable f) : (μ.map f).map g = μ.map (g ∘ f)
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
（共 45 条，此处仅展示前 30 条）

--- 原说明 ---
Any invertible matrix rescales Lebesgue measure through the absolute value of it
s
determinant.
-/
theorem map_matrix_volume_pi_eq_smul_volume_pi [DecidableEq ι] {M : Matrix ι ι ℝ} (hM : det M ≠ 0) :
    Measure.map (toLin' M) volume = ENNReal.ofReal (abs (det M)⁻¹) • volume := by
  -- This follows from the cases we have already proved, of diagonal matrices and transvections,
  -- as these matrices generate all invertible matrices.
  apply diagonal_transvection_induction_of_det_ne_zero _ M hM
  · intro D hD
    conv_rhs => rw [← smul_map_diagonal_volume_pi hD]
    rw [smul_smul, ← ENNReal.ofReal_mul (abs_nonneg _), ← abs_mul, inv_mul_cancel₀ hD, abs_one,
      ENNReal.ofReal_one, one_smul]
  · intro t
    simp_rw [Matrix.TransvectionStruct.det, _root_.inv_one, abs_one, ENNReal.ofReal_one, one_smul,
      (volume_preserving_transvectionStruct _).map_eq]
  · intro A B _ _ IHA IHB
    rw [toLin'_mul, det_mul, LinearMap.coe_comp, ← Measure.map_map, IHB, Measure.map_smul, IHA,
      smul_smul, ← ENNReal.ofReal_mul (abs_nonneg _), ← abs_mul, mul_comm, mul_inv]
    · apply Continuous.measurable
      apply LinearMap.continuous_on_pi
    · apply Continuous.measurable
      apply LinearMap.continuous_on_pi

/-- Any invertible linear map rescales Lebesgue measure through the absolute value of its
determinant. -/
/-
**Real.map_linearMap_volume_pi_eq_smul_volume_pi** 是 Mathlib 中的一个定理，位于命名空间 `Real
`。
形式化陈述：map_linearMap_volume_pi_eq_smul_volume_pi {f : (ι -> Real) ->ₗ[Real] ι -> 
Real} (hf : LinearMap.det f != 0) : Measure.map f volume = ENNReal.ofReal (abs (
LinearMap.det f)⁻¹) • volume
参数：ι -> Real；hf : LinearMap.det f != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.toMatrix'`：toMatrix'_intrinsicStar (f : WithConv ((m -> R) ->ₗ
[R] (n -> R))) : (star f).ofConv.toMatrix' = f.ofConv.toMatrix'.map star
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.det_toMatrix'`：det_toMatrix' {ι : Type*} [Fintype ι] [Decidabl
eEq ι] (f : (ι -> A) ->ₗ[A] ι -> A) : Matrix.det (LinearMap.toMatrix' f) = Linea
rMap.det f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.toLin'_toMatrix'`：∀ {R : Type u_1} [inst : CommSemiring R] {m : T
ype u_4} {n : Type u_5} [inst_1 : DecidableEq n] [inst_2 : Fintype n]   (f : (n 
→ R) →ₗ[R] m …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Real.map_matrix_volume_pi_eq_smul_volume_pi`：map_matrix_volume_pi_eq_smu
l_volume_pi [DecidableEq ι] {M : Matrix ι ι Real} (hM : det M != 0) : Measure.ma
p (toLin' M) volume = ENNReal.ofR…

--- 原说明 ---
Any invertible linear map rescales Lebesgue measure through the absolute value o
f its
determinant.
-/
theorem map_linearMap_volume_pi_eq_smul_volume_pi {f : (ι → ℝ) →ₗ[ℝ] ι → ℝ}
    (hf : LinearMap.det f ≠ 0) : Measure.map f volume =
      ENNReal.ofReal (abs (LinearMap.det f)⁻¹) • volume := by
  classical
    -- this is deduced from the matrix case
    let M := LinearMap.toMatrix' f
    have A : LinearMap.det f = det M := by simp only [M, LinearMap.det_toMatrix']
    have B : f = toLin' M := by simp only [M, toLin'_toMatrix']
    rw [A, B]
    apply map_matrix_volume_pi_eq_smul_volume_pi
    rwa [A] at hf

end Real

section regionBetween

variable {α : Type*}

/-- The region between two real-valued functions on an arbitrary set. -/
/-
**regionBetween** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：regionBetween (f g : α -> Real) (s : Set α) : Set (α × Real)
参数：f g : α -> Real；s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The region between two real-valued functions on an arbitrary set.
-/
def regionBetween (f g : α → ℝ) (s : Set α) : Set (α × ℝ) :=
  { p : α × ℝ | p.1 ∈ s ∧ p.2 ∈ Ioo (f p.1) (g p.1) }
/-
**regionBetween_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：regionBetween_subset (f g : α -> Real) (s : Set α) : regionBetween f g s s
ubseteq s ×ˢ univ
参数：f g : α -> Real；s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.prod_univ`：prod_univ {s : Set α} : s ×ˢ (univ : Set β) = Prod.fst ⁻¹
' s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem regionBetween_subset (f g : α → ℝ) (s : Set α) : regionBetween f g s ⊆ s ×ˢ univ := by
  simpa only [prod_univ, regionBetween, Set.preimage, ofPred_subset_ofPred] using fun a => And.left

variable [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ} {s : Set α}

/-- The region between two measurable functions on a measurable set is measurable. -/
/-
**measurableSet_regionBetween** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurableSet_regionBetween (hf : Measurable f) (hg : Measurable g) (hs : 
MeasurableSet s) : MeasurableSet (regionBetween f g s)
参数：hf : Measurable f；hg : Measurable g；hs : MeasurableSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
· 使用定理 `measurableSet_lt`：measurableSet_lt [SecondCountableTopology α] [OrderClo
sedTopology α] {f g : δ -> α} (hf : Measurable f) (hg : Measurable g) : Measurab
leSet …
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)

--- 原说明 ---
The region between two measurable functions on a measurable set is measurable.
-/
theorem measurableSet_regionBetween (hf : Measurable f) (hg : Measurable g) (hs : MeasurableSet s) :
    MeasurableSet (regionBetween f g s) := by
  dsimp only [regionBetween, Ioo, mem_ofPred_eq, ofPred_and]
  refine
    MeasurableSet.inter ?_
      ((measurableSet_lt (hf.comp measurable_fst) measurable_snd).inter
        (measurableSet_lt measurable_snd (hg.comp measurable_fst)))
  exact measurable_fst hs

/-- The region between two measurable functions on a measurable set is measurable;
a version for the region together with the graph of the upper function. -/
/-
**measurableSet_region_between_oc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurableSet_region_between_oc (hf : Measurable f) (hg : Measurable g) (h
s : MeasurableSet s) : MeasurableSet { p : α × Real | p.fst in s ∧ p.snd in Ioc 
(f p.fst) (g p.fst) }
参数：hf : Measurable f；hg : Measurable g；hs : MeasurableSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
· 使用定理 `measurableSet_lt`：measurableSet_lt [SecondCountableTopology α] [OrderClo
sedTopology α] {f g : δ -> α} (hf : Measurable f) (hg : Measurable g) : Measurab
leSet …
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用定理 `measurableSet_le`：measurableSet_le {f g : δ -> α} (hf : Measurable f) (h
g : Measurable g) : MeasurableSet { a | f a <= g a }

--- 原说明 ---
The region between two measurable functions on a measurable set is measurable;
a version for the region together with the graph of the upper function.
-/
theorem measurableSet_region_between_oc (hf : Measurable f) (hg : Measurable g)
    (hs : MeasurableSet s) :
    MeasurableSet { p : α × ℝ | p.fst ∈ s ∧ p.snd ∈ Ioc (f p.fst) (g p.fst) } := by
  dsimp only [regionBetween, Ioc, mem_ofPred_eq, ofPred_and]
  refine
    MeasurableSet.inter ?_
      ((measurableSet_lt (hf.comp measurable_fst) measurable_snd).inter
        (measurableSet_le measurable_snd (hg.comp measurable_fst)))
  exact measurable_fst hs

/-- The region between two measurable functions on a measurable set is measurable;
a version for the region together with the graph of the lower function. -/
/-
**measurableSet_region_between_co** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurableSet_region_between_co (hf : Measurable f) (hg : Measurable g) (h
s : MeasurableSet s) : MeasurableSet { p : α × Real | p.fst in s ∧ p.snd in Ico 
(f p.fst) (g p.fst) }
参数：hf : Measurable f；hg : Measurable g；hs : MeasurableSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
· 使用定理 `measurableSet_le`：measurableSet_le {f g : δ -> α} (hf : Measurable f) (h
g : Measurable g) : MeasurableSet { a | f a <= g a }
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用定理 `measurableSet_lt`：measurableSet_lt [SecondCountableTopology α] [OrderClo
sedTopology α] {f g : δ -> α} (hf : Measurable f) (hg : Measurable g) : Measurab
leSet …

--- 原说明 ---
The region between two measurable functions on a measurable set is measurable;
a version for the region together with the graph of the lower function.
-/
theorem measurableSet_region_between_co (hf : Measurable f) (hg : Measurable g)
    (hs : MeasurableSet s) :
    MeasurableSet { p : α × ℝ | p.fst ∈ s ∧ p.snd ∈ Ico (f p.fst) (g p.fst) } := by
  dsimp only [regionBetween, Ico, mem_ofPred_eq, ofPred_and]
  refine
    MeasurableSet.inter ?_
      ((measurableSet_le (hf.comp measurable_fst) measurable_snd).inter
        (measurableSet_lt measurable_snd (hg.comp measurable_fst)))
  exact measurable_fst hs

/-- The region between two measurable functions on a measurable set is measurable;
a version for the region together with the graphs of both functions. -/
/-
**measurableSet_region_between_cc** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurableSet_region_between_cc (hf : Measurable f) (hg : Measurable g) (h
s : MeasurableSet s) : MeasurableSet { p : α × Real | p.fst in s ∧ p.snd in Icc 
(f p.fst) (g p.fst) }
参数：hf : Measurable f；hg : Measurable g；hs : MeasurableSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `measurable_fst`：measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.fst : α × β -> α)
· 使用定理 `measurableSet_le`：measurableSet_le {f g : δ -> α} (hf : Measurable f) (h
g : Measurable g) : MeasurableSet { a | f a <= g a }
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)

--- 原说明 ---
The region between two measurable functions on a measurable set is measurable;
a version for the region together with the graphs of both functions.
-/
theorem measurableSet_region_between_cc (hf : Measurable f) (hg : Measurable g)
    (hs : MeasurableSet s) :
    MeasurableSet { p : α × ℝ | p.fst ∈ s ∧ p.snd ∈ Icc (f p.fst) (g p.fst) } := by
  dsimp only [regionBetween, Icc, mem_ofPred_eq, ofPred_and]
  refine
    MeasurableSet.inter ?_
      ((measurableSet_le (hf.comp measurable_fst) measurable_snd).inter
        (measurableSet_le measurable_snd (hg.comp measurable_fst)))
  exact measurable_fst hs

/-- The graph of a measurable function is a measurable set. -/
/-
**measurableSet_graph** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurableSet_graph (hf : Measurable f) : MeasurableSet { p : α × Real | p
.snd = f p.fst }
参数：hf : Measurable f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.Icc_self`：Icc_self (a : α) : Icc a a = {a}
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `measurableSet_region_between_cc`：measurableSet_region_between_cc (hf : M
easurable f) (hg : Measurable g) (hs : MeasurableSet s) : MeasurableSet { p : α 
× Real | p.fst in s ∧…
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ

--- 原说明 ---
The graph of a measurable function is a measurable set.
-/
theorem measurableSet_graph (hf : Measurable f) :
    MeasurableSet { p : α × ℝ | p.snd = f p.fst } := by
  simpa using measurableSet_region_between_cc hf hf MeasurableSet.univ
/-
**volume_regionBetween_eq_lintegral'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：volume_regionBetween_eq_lintegral' (hf : Measurable f) (hg : Measurable g)
 (hs : MeasurableSet s) : μ.prod volume (regionBetween f g s) = ∫⁻ y in s, ENNRe
al.ofReal ((g - f) y) ∂μ
参数：hf : Measurable f；hg : Measurable g；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.prod_apply`：prod_apply {s : Set (α × β)} (hs : Mea
surableSet s) : μ.prod ν s = ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `measurableSet_regionBetween`：measurableSet_regionBetween (hf : Measurabl
e f) (hg : Measurable g) (hs : MeasurableSet s) : MeasurableSet (regionBetween f
 g s)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.indicator_apply`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (s 
: Set α) (f : α → M) (a : α) [inst_1 : Decidable (a ∈ s)],   s.indicator f a = i
f a ∈ s t…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Real.volume_Ioo`：volume_Ioo {a b : Real} : volume (Ioo a b) = ofReal (b 
- a)
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.lintegral_indicator`：lintegral_indicator {s : Set α} (hs :
 MeasurableSet s) (f : α -> Real>=0∞) : ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f 
a ∂μ
-/
theorem volume_regionBetween_eq_lintegral' (hf : Measurable f) (hg : Measurable g)
    (hs : MeasurableSet s) :
    μ.prod volume (regionBetween f g s) = ∫⁻ y in s, ENNReal.ofReal ((g - f) y) ∂μ := by
  classical
    rw [Measure.prod_apply]
    · have h :
        (fun x => volume { a | x ∈ s ∧ a ∈ Ioo (f x) (g x) }) =
          s.indicator fun x => ENNReal.ofReal (g x - f x) := by
        funext x
        rw [indicator_apply]
        split_ifs with h
        · have hx : { a | x ∈ s ∧ a ∈ Ioo (f x) (g x) } = Ioo (f x) (g x) := by simp [h, Ioo]
          simp only [hx, Real.volume_Ioo]
        · have hx : { a | x ∈ s ∧ a ∈ Ioo (f x) (g x) } = ∅ := by simp [h]
          simp only [hx, measure_empty]
      dsimp only [regionBetween, preimage_ofPred_eq]
      rw [h, lintegral_indicator] <;> simp only [hs, Pi.sub_apply]
    · exact measurableSet_regionBetween hf hg hs

/-- The volume of the region between two almost everywhere measurable functions on a measurable set
can be represented as a Lebesgue integral. -/
/-
**volume_regionBetween_eq_lintegral** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：volume_regionBetween_eq_lintegral [SFinite μ] (hf : AEMeasurable f (μ.rest
rict s)) (hg : AEMeasurable g (μ.restrict s)) (hs : MeasurableSet s) : μ.prod vo
lume (regionBetween f g s) = ∫⁻ y in s, ENNReal.ofReal ((g - f) y) ∂μ
参数：hf : AEMeasurable f (μ.restrict s)；hg : AEMeasurable g (μ.restrict s)；hs : Me
asurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.EventuallyEq.fun_comp`：∀ {α : Type u} {β : Type v} {γ : Type w} {
f g : α → β} {l : Filter α}, f =ᶠ[l] g → ∀ (h : β → γ), h ∘ f =ᶠ[l] h ∘ g
· 使用定理 `Filter.EventuallyEq.sub`：∀ {α : Type u} {β : Type v} [inst : Sub β] {f f
' g g' : α → β} {l : Filter α},   f =ᶠ[l] g → f' =ᶠ[l] g' → f - f' =ᶠ[l] g - g'
· 使用定理 `AEMeasurable.ae_eq_mk`：ae_eq_mk (h : AEMeasurable f μ) : f =ᵐ[μ] h.mk f
· 使用定理 `MeasureTheory.measure_congr`：measure_congr (H : s =ᵐ[μ] t) : μ s = μ t
· 使用定理 `Filter.EventuallyEq.inter`：∀ {α : Type u} {s t s' t' : Set α} {l : Filte
r α}, s =ᶠ[l] t → s' =ᶠ[l] t' → s ∩ s' =ᶠ[l] t ∩ t'
· 使用定理 `Filter.EventuallyEq.rfl`：∀ {α : Type u} {β : Type v} {l : Filter α} {f :
 α → β}, f =ᶠ[l] f
· 使用定理 `Filter.EventuallyEq.comp₂`：∀ {α : Type u} {β : Type v} {γ : Type w} {δ :
 Type u_2} {f f' : α → β} {g g' : α → γ} {l : Filter α},   f =ᶠ[l] f' → ∀ (h : β
 → γ → δ), g =ᶠ…
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.ae_eq_comp`：∀ {α : Type u_2
} {β : Type u_3} {δ : Type u_4} {m0 : MeasurableSpace α} [inst : MeasurableSpace
 β]   {μ : MeasureTheory.Measure α} {ν : Meas…
· 使用定理 `MeasureTheory.Measure.quasiMeasurePreserving_fst`：quasiMeasurePreserving
_fst : QuasiMeasurePreserving Prod.fst (μ.prod ν) μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_congr_ae`：lintegral_congr_ae {f g : α -> Real>=0
∞} (h : f =ᵐ[μ] g) : ∫⁻ a, f a ∂μ = ∫⁻ a, g a ∂μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `volume_regionBetween_eq_lintegral'`：volume_regionBetween_eq_lintegral' (
hf : Measurable f) (hg : Measurable g) (hs : MeasurableSet s) : μ.prod volume (r
egionBetween f g s) = ∫⁻…
· 使用定理 `AEMeasurable.measurable_mk`：measurable_mk (h : AEMeasurable f μ) : Measu
rable (h.mk f)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `MeasureTheory.Measure.restrict_prod_eq_prod_univ`：restrict_prod_eq_prod_
univ (s : Set α) : (μ.restrict s).prod ν = (μ.prod ν).restrict (s ×ˢ univ)
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `MeasureTheory.Measure.restrict_eq_self`：restrict_eq_self (h : s subseteq
 t) : μ.restrict t s = μ s
· 使用定理 `regionBetween_subset`：regionBetween_subset (f g : α -> Real) (s : Set α)
 : regionBetween f g s subseteq s ×ˢ univ

--- 原说明 ---
The volume of the region between two almost everywhere measurable functions on a
 measurable set
can be represented as a Lebesgue integral.
-/
theorem volume_regionBetween_eq_lintegral [SFinite μ] (hf : AEMeasurable f (μ.restrict s))
    (hg : AEMeasurable g (μ.restrict s)) (hs : MeasurableSet s) :
    μ.prod volume (regionBetween f g s) = ∫⁻ y in s, ENNReal.ofReal ((g - f) y) ∂μ := by
  have h₁ :
    (fun y => ENNReal.ofReal ((g - f) y)) =ᵐ[μ.restrict s] fun y =>
      ENNReal.ofReal ((AEMeasurable.mk g hg - AEMeasurable.mk f hf) y) :=
    (hg.ae_eq_mk.sub hf.ae_eq_mk).fun_comp ENNReal.ofReal
  have h₂ :
    (μ.restrict s).prod volume (regionBetween f g s) =
      (μ.restrict s).prod volume
        (regionBetween (AEMeasurable.mk f hf) (AEMeasurable.mk g hg) s) := by
    apply measure_congr
    apply EventuallyEq.rfl.inter
    exact
      ((quasiMeasurePreserving_fst.ae_eq_comp hf.ae_eq_mk).comp₂ _ EventuallyEq.rfl).inter
        (EventuallyEq.rfl.comp₂ _ <| quasiMeasurePreserving_fst.ae_eq_comp hg.ae_eq_mk)
  rw [lintegral_congr_ae h₁, ←
    volume_regionBetween_eq_lintegral' hf.measurable_mk hg.measurable_mk hs]
  convert! h₂ using 1
  · rw [Measure.restrict_prod_eq_prod_univ]
    exact (Measure.restrict_eq_self _ (regionBetween_subset f g s)).symm
  · rw [Measure.restrict_prod_eq_prod_univ]
    exact
      (Measure.restrict_eq_self _
          (regionBetween_subset (AEMeasurable.mk f hf) (AEMeasurable.mk g hg) s)).symm

/-- The region between two a.e.-measurable functions on a null-measurable set is null-measurable. -/
/-
**nullMeasurableSet_regionBetween** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nullMeasurableSet_regionBetween (μ : Measure α) {f g : α -> Real} (f_mble 
: AEMeasurable f μ) (g_mble : AEMeasurable g μ) {s : Set α} (s_mble : NullMeasur
ableSet s μ) : NullMeasurableSet {p : α × Real | p.1 in s ∧ p.snd in Ioo (f p.fs
t) (g p.fst)} (μ.prod volume)
参数：μ : Measure α；f_mble : AEMeasurable f μ；g_mble : AEMeasurable g μ；s_mble : Nu
llMeasurableSet s μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.NullMeasurableSet.inter`：∀ {α : Type u_2} {m0 : Measurable
Space α} {μ : MeasureTheory.Measure α} {s t : Set α},   MeasureTheory.NullMeasur
ableSet s μ → MeasureTheory…
· 使用定理 `MeasureTheory.NullMeasurableSet.preimage`：∀ {α : Type u_1} {β : Type u_2
} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μa : MeasureTheory.Measure 
α}   {μb : MeasureTheory.Measu…
· 使用定理 `MeasureTheory.Measure.quasiMeasurePreserving_fst`：quasiMeasurePreserving
_fst : QuasiMeasurePreserving Prod.fst (μ.prod ν) μ
· 使用定理 `nullMeasurableSet_lt`：nullMeasurableSet_lt [SecondCountableTopology α] [
OrderClosedTopology α] {μ : Measure δ} {f g : δ -> α} (hf : AEMeasurable f μ) (h
g : AEMeas…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `AEMeasurable.comp_quasiMeasurePreserving`：comp_quasiMeasurePreserving {ν
 : Measure δ} {f : α -> δ} {g : δ -> β} (hg : AEMeasurable g ν) (hf : QuasiMeasu
rePreserving f μ ν) : AEMeasur…
· 使用定理 `MeasureTheory.QuasiMeasurePreserving.fst`：∀ {α : Type u_1} {β : Type u_2
} {γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst
_2 : MeasurableSpace γ] {μ : M…
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.id`：∀ {α : Type u_1} {_m0 :
 MeasurableSpace α} (μ : MeasureTheory.Measure α),   MeasureTheory.Measure.Quasi
MeasurePreserving id μ μ
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)

--- 原说明 ---
The region between two a.e.-measurable functions on a null-measurable set is nul
l-measurable.
-/
lemma nullMeasurableSet_regionBetween (μ : Measure α)
    {f g : α → ℝ} (f_mble : AEMeasurable f μ) (g_mble : AEMeasurable g μ)
    {s : Set α} (s_mble : NullMeasurableSet s μ) :
    NullMeasurableSet {p : α × ℝ | p.1 ∈ s ∧ p.snd ∈ Ioo (f p.fst) (g p.fst)} (μ.prod volume) := by
  refine NullMeasurableSet.inter
          (s_mble.preimage quasiMeasurePreserving_fst) (NullMeasurableSet.inter ?_ ?_)
  · exact nullMeasurableSet_lt (by fun_prop) measurable_snd.aemeasurable
  · exact nullMeasurableSet_lt measurable_snd.aemeasurable (by fun_prop)

/-- The region between two a.e.-measurable functions on a null-measurable set is null-measurable;
a version for the region together with the graph of the upper function. -/
/-
**nullMeasurableSet_region_between_oc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nullMeasurableSet_region_between_oc (μ : Measure α) {f g : α -> Real} (f_m
ble : AEMeasurable f μ) (g_mble : AEMeasurable g μ) {s : Set α} (s_mble : NullMe
asurableSet s μ) : NullMeasurableSet {p : α × Real | p.1 in s ∧ p.snd in Ioc (f 
p.fst) (g p.fst)} (μ.prod volume)
参数：μ : Measure α；f_mble : AEMeasurable f μ；g_mble : AEMeasurable g μ；s_mble : Nu
llMeasurableSet s μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.NullMeasurableSet.inter`：∀ {α : Type u_2} {m0 : Measurable
Space α} {μ : MeasureTheory.Measure α} {s t : Set α},   MeasureTheory.NullMeasur
ableSet s μ → MeasureTheory…
· 使用定理 `MeasureTheory.NullMeasurableSet.preimage`：∀ {α : Type u_1} {β : Type u_2
} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μa : MeasureTheory.Measure 
α}   {μb : MeasureTheory.Measu…
· 使用定理 `MeasureTheory.Measure.quasiMeasurePreserving_fst`：quasiMeasurePreserving
_fst : QuasiMeasurePreserving Prod.fst (μ.prod ν) μ
· 使用定理 `nullMeasurableSet_lt`：nullMeasurableSet_lt [SecondCountableTopology α] [
OrderClosedTopology α] {μ : Measure δ} {f g : δ -> α} (hf : AEMeasurable f μ) (h
g : AEMeas…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `AEMeasurable.comp_quasiMeasurePreserving`：comp_quasiMeasurePreserving {ν
 : Measure δ} {f : α -> δ} {g : δ -> β} (hg : AEMeasurable g ν) (hf : QuasiMeasu
rePreserving f μ ν) : AEMeasur…
· 使用定理 `MeasureTheory.QuasiMeasurePreserving.fst`：∀ {α : Type u_1} {β : Type u_2
} {γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst
_2 : MeasurableSpace γ] {μ : M…
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.id`：∀ {α : Type u_1} {_m0 :
 MeasurableSpace α} (μ : MeasureTheory.Measure α),   MeasureTheory.Measure.Quasi
MeasurePreserving id μ μ
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `MeasureTheory.NullMeasurableSet.compl`：compl (h : NullMeasurableSet s μ)
 : NullMeasurableSet sᶜ μ

--- 原说明 ---
The region between two a.e.-measurable functions on a null-measurable set is nul
l-measurable;
a version for the region together with the graph of the upper function.
-/
lemma nullMeasurableSet_region_between_oc (μ : Measure α)
    {f g : α → ℝ} (f_mble : AEMeasurable f μ) (g_mble : AEMeasurable g μ)
    {s : Set α} (s_mble : NullMeasurableSet s μ) :
    NullMeasurableSet {p : α × ℝ | p.1 ∈ s ∧ p.snd ∈ Ioc (f p.fst) (g p.fst)} (μ.prod volume) := by
  refine NullMeasurableSet.inter
          (s_mble.preimage quasiMeasurePreserving_fst) (NullMeasurableSet.inter ?_ ?_)
  · exact nullMeasurableSet_lt (by fun_prop) measurable_snd.aemeasurable
  · change NullMeasurableSet {p : α × ℝ | p.snd ≤ g p.fst} (μ.prod volume)
    rw [show {p : α × ℝ | p.snd ≤ g p.fst} = {p : α × ℝ | g p.fst < p.snd}ᶜ by
          ext p
          simp]
    exact (nullMeasurableSet_lt (by fun_prop) measurable_snd.aemeasurable).compl

/-- The region between two a.e.-measurable functions on a null-measurable set is null-measurable;
a version for the region together with the graph of the lower function. -/
/-
**nullMeasurableSet_region_between_co** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nullMeasurableSet_region_between_co (μ : Measure α) {f g : α -> Real} (f_m
ble : AEMeasurable f μ) (g_mble : AEMeasurable g μ) {s : Set α} (s_mble : NullMe
asurableSet s μ) : NullMeasurableSet {p : α × Real | p.1 in s ∧ p.snd in Ico (f 
p.fst) (g p.fst)} (μ.prod volume)
参数：μ : Measure α；f_mble : AEMeasurable f μ；g_mble : AEMeasurable g μ；s_mble : Nu
llMeasurableSet s μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.NullMeasurableSet.inter`：∀ {α : Type u_2} {m0 : Measurable
Space α} {μ : MeasureTheory.Measure α} {s t : Set α},   MeasureTheory.NullMeasur
ableSet s μ → MeasureTheory…
· 使用定理 `MeasureTheory.NullMeasurableSet.preimage`：∀ {α : Type u_1} {β : Type u_2
} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μa : MeasureTheory.Measure 
α}   {μb : MeasureTheory.Measu…
· 使用定理 `MeasureTheory.Measure.quasiMeasurePreserving_fst`：quasiMeasurePreserving
_fst : QuasiMeasurePreserving Prod.fst (μ.prod ν) μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `MeasureTheory.NullMeasurableSet.compl`：compl (h : NullMeasurableSet s μ)
 : NullMeasurableSet sᶜ μ
· 使用定理 `nullMeasurableSet_lt`：nullMeasurableSet_lt [SecondCountableTopology α] [
OrderClosedTopology α] {μ : Measure δ} {f g : δ -> α} (hf : AEMeasurable f μ) (h
g : AEMeas…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用定理 `AEMeasurable.comp_quasiMeasurePreserving`：comp_quasiMeasurePreserving {ν
 : Measure δ} {f : α -> δ} {g : δ -> β} (hg : AEMeasurable g ν) (hf : QuasiMeasu
rePreserving f μ ν) : AEMeasur…
· 使用定理 `MeasureTheory.QuasiMeasurePreserving.fst`：∀ {α : Type u_1} {β : Type u_2
} {γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst
_2 : MeasurableSpace γ] {μ : M…
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.id`：∀ {α : Type u_1} {_m0 :
 MeasurableSpace α} (μ : MeasureTheory.Measure α),   MeasureTheory.Measure.Quasi
MeasurePreserving id μ μ

--- 原说明 ---
The region between two a.e.-measurable functions on a null-measurable set is nul
l-measurable;
a version for the region together with the graph of the lower function.
-/
lemma nullMeasurableSet_region_between_co (μ : Measure α)
    {f g : α → ℝ} (f_mble : AEMeasurable f μ) (g_mble : AEMeasurable g μ)
    {s : Set α} (s_mble : NullMeasurableSet s μ) :
    NullMeasurableSet {p : α × ℝ | p.1 ∈ s ∧ p.snd ∈ Ico (f p.fst) (g p.fst)} (μ.prod volume) := by
  refine NullMeasurableSet.inter
          (s_mble.preimage quasiMeasurePreserving_fst) (NullMeasurableSet.inter ?_ ?_)
  · change NullMeasurableSet {p : α × ℝ | f p.fst ≤ p.snd} (μ.prod volume)
    rw [show {p : α × ℝ | f p.fst ≤ p.snd} = {p : α × ℝ | p.snd < f p.fst}ᶜ by
          ext p
          simp]
    exact (nullMeasurableSet_lt measurable_snd.aemeasurable (by fun_prop)).compl
  · exact nullMeasurableSet_lt measurable_snd.aemeasurable (by fun_prop)

/-- The region between two a.e.-measurable functions on a null-measurable set is null-measurable;
a version for the region together with the graphs of both functions. -/
/-
**nullMeasurableSet_region_between_cc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nullMeasurableSet_region_between_cc (μ : Measure α) {f g : α -> Real} (f_m
ble : AEMeasurable f μ) (g_mble : AEMeasurable g μ) {s : Set α} (s_mble : NullMe
asurableSet s μ) : NullMeasurableSet {p : α × Real | p.1 in s ∧ p.snd in Icc (f 
p.fst) (g p.fst)} (μ.prod volume)
参数：μ : Measure α；f_mble : AEMeasurable f μ；g_mble : AEMeasurable g μ；s_mble : Nu
llMeasurableSet s μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.NullMeasurableSet.inter`：∀ {α : Type u_2} {m0 : Measurable
Space α} {μ : MeasureTheory.Measure α} {s t : Set α},   MeasureTheory.NullMeasur
ableSet s μ → MeasureTheory…
· 使用定理 `MeasureTheory.NullMeasurableSet.preimage`：∀ {α : Type u_1} {β : Type u_2
} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μa : MeasureTheory.Measure 
α}   {μb : MeasureTheory.Measu…
· 使用定理 `MeasureTheory.Measure.quasiMeasurePreserving_fst`：quasiMeasurePreserving
_fst : QuasiMeasurePreserving Prod.fst (μ.prod ν) μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `MeasureTheory.NullMeasurableSet.compl`：compl (h : NullMeasurableSet s μ)
 : NullMeasurableSet sᶜ μ
· 使用定理 `nullMeasurableSet_lt`：nullMeasurableSet_lt [SecondCountableTopology α] [
OrderClosedTopology α] {μ : Measure δ} {f g : δ -> α} (hf : AEMeasurable f μ) (h
g : AEMeas…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Measurable.aemeasurable`：Measurable.aemeasurable (h : Measurable f) : AE
Measurable f μ
· 使用定理 `measurable_snd`：measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSp
ace β} : Measurable (Prod.snd : α × β -> β)
· 使用定理 `AEMeasurable.comp_quasiMeasurePreserving`：comp_quasiMeasurePreserving {ν
 : Measure δ} {f : α -> δ} {g : δ -> β} (hg : AEMeasurable g ν) (hf : QuasiMeasu
rePreserving f μ ν) : AEMeasur…
· 使用定理 `MeasureTheory.QuasiMeasurePreserving.fst`：∀ {α : Type u_1} {β : Type u_2
} {γ : Type u_3} [inst : MeasurableSpace α] [inst_1 : MeasurableSpace β]   [inst
_2 : MeasurableSpace γ] {μ : M…
· 使用定理 `MeasureTheory.Measure.QuasiMeasurePreserving.id`：∀ {α : Type u_1} {_m0 :
 MeasurableSpace α} (μ : MeasureTheory.Measure α),   MeasureTheory.Measure.Quasi
MeasurePreserving id μ μ

--- 原说明 ---
The region between two a.e.-measurable functions on a null-measurable set is nul
l-measurable;
a version for the region together with the graphs of both functions.
-/
lemma nullMeasurableSet_region_between_cc (μ : Measure α)
    {f g : α → ℝ} (f_mble : AEMeasurable f μ) (g_mble : AEMeasurable g μ)
    {s : Set α} (s_mble : NullMeasurableSet s μ) :
    NullMeasurableSet {p : α × ℝ | p.1 ∈ s ∧ p.snd ∈ Icc (f p.fst) (g p.fst)} (μ.prod volume) := by
  refine NullMeasurableSet.inter
          (s_mble.preimage quasiMeasurePreserving_fst) (NullMeasurableSet.inter ?_ ?_)
  · change NullMeasurableSet {p : α × ℝ | f p.fst ≤ p.snd} (μ.prod volume)
    rw [show {p : α × ℝ | f p.fst ≤ p.snd} = {p : α × ℝ | p.snd < f p.fst}ᶜ by
          ext p
          simp]
    exact (nullMeasurableSet_lt measurable_snd.aemeasurable (by fun_prop)).compl
  · change NullMeasurableSet {p : α × ℝ | p.snd ≤ g p.fst} (μ.prod volume)
    rw [show {p : α × ℝ | p.snd ≤ g p.fst} = {p : α × ℝ | g p.fst < p.snd}ᶜ by
          ext p
          simp]
    exact (nullMeasurableSet_lt (by fun_prop) measurable_snd.aemeasurable).compl

end regionBetween

/-- Consider a real set `s`. If a property is true almost everywhere in `s ∩ (a, b)` for
all `a, b ∈ s`, then it is true almost everywhere in `s`. Formulated with `μ.restrict`.
See also `ae_of_mem_of_ae_of_mem_inter_Ioo`. -/
/-
**ae_restrict_of_ae_restrict_inter_Ioo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ae_restrict_of_ae_restrict_inter_Ioo {μ : Measure Real} [NullSingletonClas
s μ] {s : Set Real} {p : Real -> Prop} (h : forall a b, a in s -> b in s -> a < 
b -> forallᵐ x ∂μ.restrict (s inter Ioo a b), p x) : forallᵐ x ∂μ.restrict s, p 
x
参数：h : forall a b, a in s -> b in s -> a < b -> forallᵐ x ∂μ.restrict (s inter I
oo a b), p x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `Set.finite_sdiff_iUnion_Ioo'`：Set.finite_sdiff_iUnion_Ioo' (s : Set α) :
 (s \ ⋃ x : s × s, Ioo x.1 x.2).Finite
· 使用定理 `TopologicalSpace.isOpen_iUnion_countable`：isOpen_iUnion_countable [Secon
dCountableTopology α] {ι} (s : ι -> Set α) (H : forall i, IsOpen (s i)) : exists
 T : Set ι, T.Countable ∧ ⋃ i …
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `isOpen_Ioo`：isOpen_Ioo : IsOpen (Ioo a b)
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_biUnion`：mem_biUnion {s : Set α} {t : α -> Set β} {x : α} {y : β
} (xs : x in s) (ytx : y in t x) : y in ⋃ x in s, t x
· 使用定理 `MeasureTheory.ae_restrict_of_ae_restrict_of_subset`：ae_restrict_of_ae_re
strict_of_subset {s t : Set α} {p : α -> Prop} (hst : s subseteq t) (h : forallᵐ
 x ∂μ.restrict t, p x) : forallᵐ x ∂μ.re…
· 使用定理 `MeasureTheory.ae_restrict_union_iff`：ae_restrict_union_iff (s t : Set α)
 (p : α -> Prop) : (forallᵐ x ∂μ.restrict (s union t), p x) ↔ (forallᵐ x ∂μ.rest
rict s, p x) ∧ forallᵐ x …
· 使用定理 `MeasureTheory.ae_restrict_biUnion_iff`：ae_restrict_biUnion_iff (s : ι ->
 Set α) {t : Set ι} (ht : t.Countable) (p : α -> Prop) : (forallᵐ x ∂μ.restrict 
(⋃ i in t, s i), p x) ↔ for…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.Finite.measure_zero`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {s : 
Set α},   s.Finite → ∀ (μ : MeasureTheory.Measure α) [MeasureTheory.NullSingleto
nClass μ], μ …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.ae.congr_simp`：∀ {α : Type u_1} {F : Type u_3} [inst : Fun
Like F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F α]   (μ μ_1 
: F), μ = μ_1 → M…
· 使用定理 `MeasureTheory.ae_zero`：ae_zero {_m0 : MeasurableSpace α} : ae (0 : Measu
re α) = ⊥
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Set.Ioo_eq_empty_of_le`：Ioo_eq_empty_of_le (h : b <= a) : Ioo a b = ∅
· 使用定理 `Set.inter_empty`：inter_empty (a : Set α) : a inter ∅ = ∅
· 使用定理 `MeasureTheory.Measure.restrict_empty`：restrict_empty : μ.restrict ∅ = 0

--- 原说明 ---
Consider a real set `s`. If a property is true almost everywhere in `s ∩ (a, b)`
 for
all `a, b ∈ s`, then it is true almost everywhere in `s`. Formulated with `μ.res
trict`.
See also `ae_of_mem_of_ae_of_mem_inter_Ioo`.
-/
theorem ae_restrict_of_ae_restrict_inter_Ioo {μ : Measure ℝ} [NullSingletonClass μ] {s : Set ℝ}
    {p : ℝ → Prop} (h : ∀ a b, a ∈ s → b ∈ s → a < b → ∀ᵐ x ∂μ.restrict (s ∩ Ioo a b), p x) :
    ∀ᵐ x ∂μ.restrict s, p x := by
  /- By second-countability, we cover `s` by countably many intervals `(a, b)` (except maybe for
    two endpoints, which don't matter since `μ` does not have any atom). -/
  let T : s × s → Set ℝ := fun p => Ioo p.1 p.2
  let u := ⋃ i : ↥s × ↥s, T i
  have hfinite : (s \ u).Finite := s.finite_sdiff_iUnion_Ioo'
  obtain ⟨A, A_count, hA⟩ :
    ∃ A : Set (↥s × ↥s), A.Countable ∧ ⋃ i ∈ A, T i = ⋃ i : ↥s × ↥s, T i :=
    isOpen_iUnion_countable _ fun p => isOpen_Ioo
  have : s ⊆ s \ u ∪ ⋃ p ∈ A, s ∩ T p := by
    intro x hx
    by_cases h'x : x ∈ ⋃ i : ↥s × ↥s, T i
    · rw [← hA] at h'x
      obtain ⟨p, pA, xp⟩ : ∃ p : ↥s × ↥s, p ∈ A ∧ x ∈ T p := by
        simpa only [mem_iUnion, exists_prop, SetCoe.exists, exists_and_right] using h'x
      right
      exact mem_biUnion pA ⟨hx, xp⟩
    · exact Or.inl ⟨hx, h'x⟩
  apply ae_restrict_of_ae_restrict_of_subset this
  rw [ae_restrict_union_iff, ae_restrict_biUnion_iff _ A_count]
  constructor
  · have : μ.restrict (s \ u) = 0 := by simp only [restrict_eq_zero, hfinite.measure_zero]
    simp only [this, ae_zero, eventually_bot]
  · rintro ⟨⟨a, as⟩, ⟨b, bs⟩⟩ -
    dsimp [T]
    rcases le_or_gt b a with (hba | hab)
    · simp only [Ioo_eq_empty_of_le hba, inter_empty, restrict_empty, ae_zero, eventually_bot]
    · exact h a b as bs hab

/-- Consider a real set `s`. If a property is true almost everywhere in `s ∩ (a, b)` for
all `a, b ∈ s`, then it is true almost everywhere in `s`. Formulated with bare membership.
See also `ae_restrict_of_ae_restrict_inter_Ioo`. -/
/-
**ae_of_mem_of_ae_of_mem_inter_Ioo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ae_of_mem_of_ae_of_mem_inter_Ioo {μ : Measure Real} [NullSingletonClass μ]
 {s : Set Real} {p : Real -> Prop} (h : forall a b, a in s -> b in s -> a < b ->
 forallᵐ x ∂μ, x in s inter Ioo a b -> p x) : forallᵐ x ∂μ, x in s -> p x
参数：h : forall a b, a in s -> b in s -> a < b -> forallᵐ x ∂μ, x in s inter Ioo a
 b -> p x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `Set.finite_sdiff_iUnion_Ioo'`：Set.finite_sdiff_iUnion_Ioo' (s : Set α) :
 (s \ ⋃ x : s × s, Ioo x.1 x.2).Finite
· 使用定理 `TopologicalSpace.isOpen_iUnion_countable`：isOpen_iUnion_countable [Secon
dCountableTopology α] {ι} (s : ι -> Set α) (H : forall i, IsOpen (s i)) : exists
 T : Set ι, T.Countable ∧ ⋃ i …
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `isOpen_Ioo`：isOpen_Ioo : IsOpen (Ioo a b)
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Set.Countable.ae_notMem`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {s : 
Set α},   s.Countable → ∀ (μ : MeasureTheory.Measure α) [MeasureTheory.NullSingl
etonClass μ],…
· 使用定理 `Set.Finite.countable`：∀ {α : Type u} {s : Set α}, s.Finite → s.Countable
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_ball_iff`：ae_ball_iff {ι : Type*} {S : Set ι} (hS : S.C
ountable) {p : α -> forall i in S, Prop} : (forallᵐ x ∂μ, forall i (hi : i in S)
, p x i hi) ↔ f…
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.Ioo_eq_empty_of_le`：Ioo_eq_empty_of_le (h : b <= a) : Ioo a b = ∅
· 使用定理 `Set.inter_empty`：inter_empty (a : Set α) : a inter ∅ = ∅
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Consider a real set `s`. If a property is true almost everywhere in `s ∩ (a, b)`
 for
all `a, b ∈ s`, then it is true almost everywhere in `s`. Formulated with bare m
embership.
See also `ae_restrict_of_ae_restrict_inter_Ioo`.
-/
theorem ae_of_mem_of_ae_of_mem_inter_Ioo {μ : Measure ℝ} [NullSingletonClass μ] {s : Set ℝ}
    {p : ℝ → Prop} (h : ∀ a b, a ∈ s → b ∈ s → a < b → ∀ᵐ x ∂μ, x ∈ s ∩ Ioo a b → p x) :
    ∀ᵐ x ∂μ, x ∈ s → p x := by
  /- By second-countability, we cover `s` by countably many intervals `(a, b)` (except maybe for
    two endpoints, which don't matter since `μ` does not have any atom). -/
  let T : s × s → Set ℝ := fun p => Ioo p.1 p.2
  let u := ⋃ i : ↥s × ↥s, T i
  have hfinite : (s \ u).Finite := s.finite_sdiff_iUnion_Ioo'
  obtain ⟨A, A_count, hA⟩ :
    ∃ A : Set (↥s × ↥s), A.Countable ∧ ⋃ i ∈ A, T i = ⋃ i : ↥s × ↥s, T i :=
    isOpen_iUnion_countable _ fun p => isOpen_Ioo
  have M : ∀ᵐ x ∂μ, x ∉ s \ u := hfinite.countable.ae_notMem _
  have M' : ∀ᵐ x ∂μ, ∀ (i : ↥s × ↥s), i ∈ A → x ∈ s ∩ T i → p x := by
    rw [ae_ball_iff A_count]
    rintro ⟨⟨a, as⟩, ⟨b, bs⟩⟩ -
    change ∀ᵐ x : ℝ ∂μ, x ∈ s ∩ Ioo a b → p x
    rcases le_or_gt b a with (hba | hab)
    · simp only [Ioo_eq_empty_of_le hba, inter_empty, IsEmpty.forall_iff, eventually_true,
        mem_empty_iff_false]
    · exact h a b as bs hab
  filter_upwards [M, M'] with x hx h'x
  intro xs
  by_cases Hx : x ∈ ⋃ i : ↥s × ↥s, T i
  · rw [← hA] at Hx
    obtain ⟨p, pA, xp⟩ : ∃ p : ↥s × ↥s, p ∈ A ∧ x ∈ T p := by
      simpa only [mem_iUnion, exists_prop, SetCoe.exists, exists_and_right] using Hx
    apply h'x p pA ⟨xs, xp⟩
  · exact False.elim (hx ⟨xs, Hx⟩)
