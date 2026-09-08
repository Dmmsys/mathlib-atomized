/-
Copyright (c) 2025 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto, Yongxi Lin, Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.SetToL1
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic

/-!
# Integral of vector-valued function against vector measure

We extend the definition of the Bochner integral (of vector-valued function against `ℝ≥0∞`-valued
measure) to vector measures through a bilinear pairing.
Let `E`, `F` be normed vector spaces, and `G` be a Banach space (complete normed vector space).
We fix a continuous linear pairing `B : E →L[ℝ] F →L[ℝ] G` and an `F`-valued vector measure `μ`
on a measurable space `X`.
For an integrable function `f : X → E` with respect to the total variation of the vector measure
on `X` informally written `μ ∘ B.flip`, we define the `G`-valued integral, which is informally
written `∫ B (f x) ∂μ x`.

Such integral is defined through the general setting `setToFun` which sends a set function to the
integral of integrable functions, see the file
`Mathlib/MeasureTheory/Integral/SetToL1.lean`.

## Main definitions

The integral against vector measures is defined through the extension process described in the file
`Mathlib/MeasureTheory/Integral/SetToL1.lean`, which follows these steps:

1. Define the integral of the indicator of a set. This is `cbmApplyMeasure B μ s x = B x (μ s)`.
  `cbmApplyMeasure B μ` is shown to be linear in the value `x` and `DominatedFinMeasAdditive`
  (defined in the file `Mathlib/MeasureTheory/Integral/SetToL1.lean`) with respect to the set `s`.

2. Define the integral on integrable functions `f` as `setToFun (...) f`.

## Notations

* `∫ᵛ x, f x ∂[B; μ]`: the `G`-valued integral of an `E`-valued function `f` against the `F`-valued
  vector measure `μ` paired through `B`.
* `∫ᵛ x, f x ∂•μ`: the special case where `f` is a real-valued function and `μ` is an `F`-valued
  vector measure, with the pairing being the scalar multiplication by `ℝ`.
* `∫ᵛ x, f x ∂<•μ`: the special case where `f` is an `E`-valued function and `μ` is a signed
  measure, with the pairing being the flip of scalar multiplication.
* `∫ᵛ x in s, f x ∂[B; μ]`: the `G`-valued integral of an `E`-valued function `f` against
  the `F`-valued vector measure `μ` paired through `B`, on the set `s`.
* `∫ᵛ x in s, f x ∂•μ`: the special case where `f` is a real-valued function and `μ` is
  an `F`-valued vector measure, with the pairing being the scalar multiplication by `ℝ`.
* `∫ᵛ x in s, f x ∂<•μ`: the special case where `f` is an `E`-valued function and `μ` is a signed
  measure, with the pairing being the flip of scalar multiplication.

## Note

Let `μ` be a vector measure and `B` be a continuous linear pairing.
We often consider integrable functions with respect to the total variation of
`μ.transpose B` = `μ.mapRange B.flip.toAddMonoidHom B.flip.continuous`, which is the reference
measure for the pairing integral.

When `f` is not integrable with respect to `μ.variation`, the value of
`μ.integral B f` is set to `0`. This is an analogous convention to the Bochner integral. However,
there are cases where a natural definition of the integral as an unconditional sum exists, but `f`
is not integrable in this sense: Let `μ` be the `L∞(ℕ)`-valued measure on `ℕ` defined by extending
`{n} ↦ (0,0,..., 1/(n+1),0,0,...)` and `B` be the trivial coupling (the scalar multiplication by
`ℝ`). The total variation is `∑ n, 1/(n+1) = ∞`, but the sum of `(0,...,0,1/n,0,...)` in `L∞(ℕ)` is
unconditionally convergent.

-/

public section

open Set MeasureTheory VectorMeasure ContinuousLinearMap Filter Topology
open scoped ENNReal NNReal

variable {ι X Y E F G H : Type*} {mX : MeasurableSpace X} [MeasurableSpace Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

namespace MeasureTheory

section cbmApplyMeasure

/-- The composition of the vector measure with the linear pairing, giving the reference
vector measure. -/
@[expose]
/-
**MeasureTheory.VectorMeasure.transpose** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory
.VectorMeasure`。
形式化陈述：{X : Type u_2} →   {E : Type u_4} →     {F : Type u_5} →       {G : Type u
_6} →         {mX : MeasurableSpace X} →           [inst : NormedAddCommGroup E]
 →             [inst_1 : NormedSpace ℝ E] →               [inst_2 : NormedAddCom
mGroup F] →                 [inst_3 : NormedSpace ℝ F] →                   [inst
_4 : NormedAddCommGroup G] →                     [inst_5 : NormedSpace ℝ G] →   
                    MeasureTheory.VectorMeasure X F → (E →L[ℝ] F →L[ℝ] G) → Meas
ureTheory.VectorMeasure X (E →L[ℝ] G)
参数：E →L[ℝ] F →L[ℝ] G；E →L[ℝ] G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of the vector measure with the linear pairing, giving the refere
nce
vector measure.
-/
noncomputable def VectorMeasure.transpose (μ : VectorMeasure X F) (B : E →L[ℝ] F →L[ℝ] G) :
    VectorMeasure X (E →L[ℝ] G) := μ.mapRange B.flip.toAddMonoidHom B.flip.continuous

/-- Given a set `s`, return the continuous linear map `fun x : E ↦ B x (μ s)` (actually defined
using `transpose` through `mapRange`), where the `B` is a `G`-valued bilinear form on `E × F` and
`μ` is an `F`-valued vector measure. The extension of that set function through `setToFun` gives the
pairing integral of `E`-valued integrable functions. -/
/-
**MeasureTheory.cbmApplyMeasure** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：cbmApplyMeasure (μ : VectorMeasure X F) (B : E ->L[Real] F ->L[Real] G) (s
 : Set X) : E ->L[Real] G where toFun x
参数：μ : VectorMeasure X F；B : E ->L[Real] F ->L[Real] G；s : Set X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a set `s`, return the continuous linear map `fun x : E ↦ B x (μ s)` (actua
lly defined
using `transpose` through `mapRange`), where the `B` is a `G`-valued bilinear fo
rm on `E × F` and
`μ` is an `F`-valued vector measure. The extension of that set function through 
`setToFun` gives the
pairing integral of `E`-valued integrable functions.
-/
noncomputable def cbmApplyMeasure (μ : VectorMeasure X F) (B : E →L[ℝ] F →L[ℝ] G) (s : Set X) :
    E →L[ℝ] G where
  toFun x := μ.transpose B s x
  map_add' _ _ := map_add₂ ..
  map_smul' _ _ := map_smulₛₗ₂ ..
/-
**MeasureTheory.transpose_eq_cbmApplyMeasure** 是 Mathlib 中的一个引理，位于命名空间 `MeasureT
heory`。
形式化陈述：transpose_eq_cbmApplyMeasure (μ : VectorMeasure X F) (B : E ->L[Real] F ->
L[Real] G) : μ.transpose B = cbmApplyMeasure μ B
参数：μ : VectorMeasure X F；B : E ->L[Real] F ->L[Real] G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
lemma transpose_eq_cbmApplyMeasure (μ : VectorMeasure X F) (B : E →L[ℝ] F →L[ℝ] G) :
    μ.transpose B = cbmApplyMeasure μ B := by rfl

@[simp]
/-
**MeasureTheory.cbmApplyMeasure_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：cbmApplyMeasure_apply (μ : VectorMeasure X F) (B : E ->L[Real] F ->L[Real]
 G) (s : Set X) (x : E) : cbmApplyMeasure μ B s x = B x (μ s)
参数：μ : VectorMeasure X F；B : E ->L[Real] F ->L[Real] G；s : Set X；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem cbmApplyMeasure_apply (μ : VectorMeasure X F) (B : E →L[ℝ] F →L[ℝ] G) (s : Set X) (x : E) :
    cbmApplyMeasure μ B s x = B x (μ s) := by
  rfl
/-
**MeasureTheory.cbmApplyMeasure_union** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：cbmApplyMeasure_union (μ : VectorMeasure X F) (B : E ->L[Real] F ->L[Real]
 G) {s t : Set X} (hs : MeasurableSet s) (ht : MeasurableSet t) (hdisj : Disjoin
t s t) : cbmApplyMeasure μ B (s union t) = cbmApplyMeasure μ B s + cbmApplyMeasu
re μ B t
参数：μ : VectorMeasure X F；B : E ->L[Real] F ->L[Real] G；hs : MeasurableSet s；ht :
 MeasurableSet t；hdisj : Disjoint s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.cbmApplyMeasure_apply`：cbmApplyMeasure_apply (μ : VectorMe
asure X F) (B : E ->L[Real] F ->L[Real] G) (s : Set X) (x : E) : cbmApplyMeasure
 μ B s x = B x (μ s)
· 使用定理 `MeasureTheory.VectorMeasure.of_union`：of_union {A B : Set α} (h : Disjoi
nt A B) (hA : MeasurableSet A) (hB : MeasurableSet B) : v (A union B) = v A + v 
B
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cbmApplyMeasure_union (μ : VectorMeasure X F) (B : E →L[ℝ] F →L[ℝ] G) {s t : Set X}
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hdisj : Disjoint s t) :
    cbmApplyMeasure μ B (s ∪ t) = cbmApplyMeasure μ B s + cbmApplyMeasure μ B t := by
  ext x
  simp [of_union hdisj hs ht]
/-
**MeasureTheory.norm_cbmApplyMeasure_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：norm_cbmApplyMeasure_le (μ : VectorMeasure X F) (B : E ->L[Real] F ->L[Rea
l] G) (s : Set X) : ‖cbmApplyMeasure μ B s‖ <= ‖B‖ * ‖μ s‖
参数：μ : VectorMeasure X F；B : E ->L[Real] F ->L[Real] G；s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.opNorm_le_iff`：opNorm_le_iff {f : E ->SL[σ₁₂] F} {M 
: Real} (hMp : 0 <= M) : ‖f‖ <= M ↔ forall x, ‖f x‖ <= M * ‖x‖
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `MeasureTheory.cbmApplyMeasure_apply`：cbmApplyMeasure_apply (μ : VectorMe
asure X F) (B : E ->L[Real] F ->L[Real] G) (s : Set X) (x : E) : cbmApplyMeasure
 μ B s x = B x (μ s)
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `ContinuousLinearMap.le_opNorm₂`：le_opNorm₂ [RingHomIsometric σ₁₃] (f : E
 ->SL[σ₁₃] F ->SL[σ₂₃] G) (x : E) (y : F) : ‖f x y‖ <= ‖f‖ * ‖x‖ * ‖y‖
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
-/
theorem norm_cbmApplyMeasure_le (μ : VectorMeasure X F) (B : E →L[ℝ] F →L[ℝ] G) (s : Set X) :
    ‖cbmApplyMeasure μ B s‖ ≤ ‖B‖ * ‖μ s‖ := by
  rw [opNorm_le_iff (by positivity)]
  intro x
  grw [cbmApplyMeasure_apply, le_opNorm₂, mul_right_comm]
/-
**MeasureTheory.dominatedFinMeasAdditive_cbmApplyMeasure** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory`。
形式化陈述：dominatedFinMeasAdditive_cbmApplyMeasure (μ : VectorMeasure X F) (B : E ->
L[Real] F ->L[Real] G) : DominatedFinMeasAdditive μ.variation (μ.transpose B) ‖B
‖
参数：μ : VectorMeasure X F；B : E ->L[Real] F ->L[Real] G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `MeasureTheory.cbmApplyMeasure_union`：cbmApplyMeasure_union (μ : VectorMe
asure X F) (B : E ->L[Real] F ->L[Real] G) {s t : Set X} (hs : MeasurableSet s) 
(ht : MeasurableSet t) (h…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.norm_cbmApplyMeasure_le`：norm_cbmApplyMeasure_le (μ : Vect
orMeasure X F) (B : E ->L[Real] F ->L[Real] G) (s : Set X) : ‖cbmApplyMeasure μ 
B s‖ <= ‖B‖ * ‖μ s‖
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `MeasureTheory.VectorMeasure.norm_measure_le_variation`：norm_measure_le_v
ariation {E : Set X} (hE : μ.variation E != ∞
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem dominatedFinMeasAdditive_cbmApplyMeasure (μ : VectorMeasure X F) (B : E →L[ℝ] F →L[ℝ] G) :
    DominatedFinMeasAdditive μ.variation (μ.transpose B) ‖B‖ := by
  refine ⟨fun s t hs ht _ _ hdisj ↦ cbmApplyMeasure_union μ B hs ht hdisj, fun s hs hsf ↦ ?_⟩
  apply (norm_cbmApplyMeasure_le _ _ _).trans
  gcongr
  exact norm_measure_le_variation hsf.ne
/-
**MeasureTheory.dominatedFinMeasAdditive_transpose_cbmApplyMeasure** 是 Mathlib 中
的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：dominatedFinMeasAdditive_transpose_cbmApplyMeasure (μ : VectorMeasure X F)
 (B : E ->L[Real] F ->L[Real] G) : DominatedFinMeasAdditive (μ.transpose B).vari
ation (μ.transpose B) 1
参数：μ : VectorMeasure X F；B : E ->L[Real] F ->L[Real] G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `MeasureTheory.cbmApplyMeasure_union`：cbmApplyMeasure_union (μ : VectorMe
asure X F) (B : E ->L[Real] F ->L[Real] G) {s t : Set X} (hs : MeasurableSet s) 
(ht : MeasurableSet t) (h…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MeasureTheory.VectorMeasure.norm_measure_le_variation`：norm_measure_le_v
ariation {E : Set X} (hE : μ.variation E != ∞
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
-/
theorem dominatedFinMeasAdditive_transpose_cbmApplyMeasure
    (μ : VectorMeasure X F) (B : E →L[ℝ] F →L[ℝ] G) :
    DominatedFinMeasAdditive (μ.transpose B).variation (μ.transpose B) 1 := by
  refine ⟨fun s t hs ht _ _ hdisj ↦ cbmApplyMeasure_union μ B hs ht hdisj, fun s hs hsf ↦ ?_⟩
  simpa using! norm_measure_le_variation hsf.ne

end cbmApplyMeasure

namespace VectorMeasure

variable (μ ν : VectorMeasure X F) (B : E →L[ℝ] F →L[ℝ] G) {C : E →L[ℝ] F →L[ℝ] G}
  {f g : X → E} {φ : X → Y}

set_option backward.isDefEq.respectTransparency.types false in
/-
**MeasureTheory.VectorMeasure.transpose_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.VectorMeasure`。
形式化陈述：∀ {X : Type u_2} {E : Type u_4} {F : Type u_5} {G : Type u_6} {mX : Measur
ableSpace X} [inst : NormedAddCommGroup E]   [inst_1 : NormedSpace ℝ E] [inst_2 
: NormedAddCommGroup F] [inst_3 : NormedSpace ℝ F] [inst_4 : NormedAddCommGroup 
G]   [inst_5 : NormedSpace ℝ G] (B : E →L[ℝ] F →L[ℝ] G), MeasureTheory.VectorMea
sure.transpose 0 B = 0
参数：B : E →L[ℝ] F →L[ℝ] G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.mapRange_zero`：mapRange_zero {f : M ->+ N} (
hf : Continuous f) : mapRange (0 : VectorMeasure α M) f hf = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma transpose_zero : (0 : VectorMeasure X F).transpose B = 0 := by
  simp [transpose]

set_option backward.isDefEq.respectTransparency.types false in
/-
**MeasureTheory.VectorMeasure.transpose_restrict** 是 Mathlib 中的一个引理，位于命名空间 `Meas
ureTheory.VectorMeasure`。
形式化陈述：transpose_restrict (s : Set X) : (μ.restrict s).transpose B = (μ.transpose
 B).restrict s
参数：s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.restrict_apply`：restrict_apply {i : Set α} (
hi : MeasurableSet i) {j : Set α} (hj : MeasurableSet j) : v.restrict i j = v (j
 inter i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.VectorMeasure.restrict_not_measurable`：restrict_not_measur
able {i : Set α} (hi : ¬MeasurableSet i) : v.restrict i = 0
· 使用定理 `MeasureTheory.VectorMeasure.transpose_zero`：∀ {X : Type u_2} {E : Type u
_4} {F : Type u_5} {G : Type u_6} {mX : MeasurableSpace X} [inst : NormedAddComm
Group E]   [inst_1 : NormedSpace…
-/
lemma transpose_restrict (s : Set X) :
    (μ.restrict s).transpose B = (μ.transpose B).restrict s := by
  by_cases hs : MeasurableSet s
  · ext t ht : 1
    simp [VectorMeasure.restrict_apply, hs, ht, transpose]
  · simp [restrict_not_measurable _ hs]

set_option backward.isDefEq.respectTransparency.types false in
/-
**MeasureTheory.VectorMeasure.transpose_map** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTh
eory.VectorMeasure`。
形式化陈述：transpose_map : (μ.map φ).transpose B = (μ.transpose B).map φ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.VectorMeasure.map_apply`：map_apply {f : α -> β} (hf : Meas
urable f) {s : Set β} (hs : MeasurableSet s) : v.map f s = v (f ⁻¹' s)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `MeasureTheory.VectorMeasure.transpose_zero`：∀ {X : Type u_2} {E : Type u
_4} {F : Type u_5} {G : Type u_6} {mX : MeasurableSpace X} [inst : NormedAddComm
Group E]   [inst_1 : NormedSpace…
-/
lemma transpose_map : (μ.map φ).transpose B = (μ.transpose B).map φ := by
  by_cases hφ : Measurable φ; swap
  · simp [map, hφ]
  ext s hs
  simp [transpose, map_apply, hs, hφ]

set_option backward.isDefEq.respectTransparency.types false in
/-
**MeasureTheory.VectorMeasure.transpose_add** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTh
eory.VectorMeasure`。
形式化陈述：transpose_add : (μ + ν).transpose B = μ.transpose B + ν.transpose B
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.mapRange_add`：mapRange_add {v w : VectorMeas
ure α M} {f : M ->+ N} (hf : Continuous f) : (v + w).mapRange f hf = v.mapRange 
f hf + w.mapRange f hf
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma transpose_add :
    (μ + ν).transpose B = μ.transpose B + ν.transpose B := by
  simp [transpose]
/-
**MeasureTheory.VectorMeasure.transpose_smul** 是 Mathlib 中的一个引理，位于命名空间 `MeasureT
heory.VectorMeasure`。
形式化陈述：transpose_smul (c : Real) : (c • μ).transpose B = c • μ.transpose B
参数：c : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.mapRange_smul`：mapRange_smul {v : VectorMeas
ure α M} {f : M ->ₗ[R] N} (hf : Continuous f) {c : R} : (c • v).mapRange f.toAdd
MonoidHom hf = c • (v.mapRange …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma transpose_smul (c : ℝ) :
    (c • μ).transpose B = c • μ.transpose B := by
  simp [transpose, mapRange_smul]

set_option backward.isDefEq.respectTransparency.types false in
/-
**MeasureTheory.VectorMeasure.transpose_dirac** 是 Mathlib 中的一个引理，位于命名空间 `Measure
Theory.VectorMeasure`。
形式化陈述：transpose_dirac (x : X) (v : F) : (dirac x v).transpose B = dirac x (B.fli
p v)
参数：x : X；v : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.dirac_apply_of_mem`：∀ {β : Type u_2} {M : Ty
pe u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSpace M] [inst_2 : Measura
bleSpace β]   {x : β} {v : M} {s : S…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.VectorMeasure.dirac_apply_of_notMem`：∀ {β : Type u_2} {M :
 Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSpace M] [inst_2 : Meas
urableSpace β]   {x : β} {v : M} {s : S…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
-/
lemma transpose_dirac (x : X) (v : F) :
    (dirac x v).transpose B = dirac x (B.flip v) := by
  ext s hs : 1
  by_cases hx : x ∈ s <;> simp [transpose, hx, hs]

set_option backward.isDefEq.respectTransparency.types false in
/-
**MeasureTheory.VectorMeasure.variation_transpose_le** 是 Mathlib 中的一个引理，位于命名空间 `
MeasureTheory.VectorMeasure`。
形式化陈述：variation_transpose_le : (μ.transpose B).variation <= ‖B‖₊ • μ.variation
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用引理 `MeasureTheory.VectorMeasure.variation_le_of_forall_enorm_le`：variation_l
e_of_forall_enorm_le {m : Measure X} (h : forall E, MeasurableSet E -> ‖μ E‖ₑ <=
 m E) : μ.variation <= m
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `ContinuousLinearMap.opENorm_le_bound`：opENorm_le_bound (f : E ->SL[σ₁₂] 
F) {M : Real>=0∞} (hM : forall x, ‖f x‖ₑ <= M * ‖x‖ₑ) : ‖f‖ₑ <= M
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用引理 `ContinuousLinearMap.le_opENorm`：le_opENorm (f : E ->SL[σ₁₂] F) (x : E) :
 ‖f x‖ₑ <= ‖f‖ₑ * ‖x‖ₑ
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `MeasureTheory.VectorMeasure.enorm_measure_le_variation`：enorm_measure_le
_variation (μ : VectorMeasure X V) (E : Set X) : ‖μ E‖ₑ <= variation μ E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `enorm_eq_nnnorm`：enorm_eq_nnnorm (x : E) : ‖x‖ₑ = ‖x‖₊
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
（共 34 条，此处仅展示前 30 条）
-/
lemma variation_transpose_le :
    (μ.transpose B).variation ≤ ‖B‖₊ • μ.variation := by
  apply variation_le_of_forall_enorm_le (fun s hs ↦ ?_)
  apply opENorm_le_bound _ (fun x ↦ ?_)
  simp only [transpose, mapRange_apply, LinearMap.toAddMonoidHom_coe, coe_coe, flip_apply,
    Measure.smul_apply, Measure.nnreal_smul_coe_apply]
  grw [le_opENorm, le_opENorm, enorm_measure_le_variation, ← enorm_eq_nnnorm]
  exact le_of_eq (by ring)
/-
**MeasureTheory.VectorMeasure.absolutelyContinuous_variation_transpose** 是 Mathl
ib 中的一个引理，位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：absolutelyContinuous_variation_transpose (μ : VectorMeasure X F) (B : E ->
L[Real] F ->L[Real] G) : (μ.transpose B).variation ≪ μ.variation
参数：μ : VectorMeasure X F；B : E ->L[Real] F ->L[Real] G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.Measure.absolutelyContinuous_of_le_smul`：absolutelyContinu
ous_of_le_smul {μ' : Measure α} {c : Real>=0∞} (hμ'_le : μ' <= c • μ) : μ' ≪ μ
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用引理 `MeasureTheory.VectorMeasure.variation_transpose_le`：variation_transpose_
le : (μ.transpose B).variation <= ‖B‖₊ • μ.variation
-/
lemma absolutelyContinuous_variation_transpose (μ : VectorMeasure X F) (B : E →L[ℝ] F →L[ℝ] G) :
    (μ.transpose B).variation ≪ μ.variation :=
  Measure.absolutelyContinuous_of_le_smul (variation_transpose_le μ B)
/-
**MeasureTheory.VectorMeasure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.VectorMe
asure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsFiniteMeasure μ.variation] :
    IsFiniteMeasure (μ.transpose B).variation :=
  isFiniteMeasure_of_le _ (variation_transpose_le μ B)

set_option backward.isDefEq.respectTransparency.types false in
/-
**MeasureTheory.VectorMeasure.variation_transpose_eq_smul** 是 Mathlib 中的一个引理，位于命
名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：variation_transpose_eq_smul [Nontrivial E] {C : Real>=0} (hB : forall x y,
 ‖B x y‖₊ = C * ‖x‖₊ * ‖y‖₊) : (μ.transpose B).variation = C • μ.variation
参数：hB : forall x y, ‖B x y‖₊ = C * ‖x‖₊ * ‖y‖₊。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `MeasureTheory.VectorMeasure.variation_transpose_le`：variation_transpose_
le : (μ.transpose B).variation <= ‖B‖₊ • μ.variation
· 使用定理 `IsOrderedSMul.smul_le_smul`：IsOrderedSMul.smul_le_smul [LE G] [Preorder 
P] [SMul G P] [IsOrderedSMul G P] {a b : G} {c d : P} (hab : a <= b) (hcd : c <=
 d) : a • c <= b…
· 使用定理 `MeasureTheory.Measure.instIsOrderedSMulOfENNReal`：∀ {α : Type u_1} {R : 
Type u_6} {m0 : MeasurableSpace α} [inst : SMul R ENNReal] [inst_1 : LE R]   [in
st_2 : IsScalarTower R ENNReal ENNReal…
· 使用定理 `ENNReal.instIsOrderedSMulNNReal`：IsOrderedSMul NNReal ENNReal
· 使用定理 `ContinuousLinearMap.opNNNorm_le_bound`：opNNNorm_le_bound (f : E ->SL[σ₁₂
] F) (M : Real>=0) (hM : forall x, ‖f x‖₊ <= M * ‖x‖₊) : ‖f‖₊ <= M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.VectorMeasure.variation_le_of_forall_enorm_le`：variation_l
e_of_forall_enorm_le {m : Measure X} (h : forall E, MeasurableSet E -> ‖μ E‖ₑ <=
 m E) : μ.variation <= m
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `ContinuousLinearMap.le_opNNNorm`：le_opNNNorm (f : E ->SL[σ₁₂] F) (x : E)
 : ‖f x‖₊ <= ‖f‖₊ * ‖x‖₊
· 使用定理 `ENNReal.coe_le_coe._gcongr_2`：∀ {r q : NNReal}, r ≤ q → ↑r ≤ ↑q
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用引理 `le_div_iff₀'`：le_div_iff₀' (hc : 0 < c) : a <= b / c ↔ c * a <= b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
（共 52 条，此处仅展示前 30 条）
-/
lemma variation_transpose_eq_smul [Nontrivial E] {C : ℝ≥0}
    (hB : ∀ x y, ‖B x y‖₊ = C * ‖x‖₊ * ‖y‖₊) :
    (μ.transpose B).variation = C • μ.variation := by
  apply le_antisymm
  · apply (variation_transpose_le _ _).trans
    gcongr
    apply opNNNorm_le_bound _ _ (fun x ↦ opNNNorm_le_bound _ _ (fun y ↦ by simp [hB]))
  · rcases eq_or_ne C 0 with rfl | hC
    · simp [Measure.zero_le]
    suffices μ.variation ≤ C⁻¹ • (μ.transpose B).variation by
      grw [this, smul_smul, mul_inv_cancel₀ hC, one_smul]
    apply variation_le_of_forall_enorm_le (fun s hs ↦ ?_)
    have : ‖μ s‖ₑ ≤ C⁻¹ • ‖(μ.transpose B) s‖ₑ := by
      simp only [transpose, mapRange_apply, LinearMap.toAddMonoidHom_coe, coe_coe]
      obtain ⟨x, hx⟩ : ∃ (x : E), x ≠ 0 := exists_ne 0
      have : ‖B.flip (μ s) x‖₊ ≤ ‖B.flip (μ s)‖₊ * ‖x‖₊ := le_opNNNorm _ _
      simp only [flip_apply, hB] at this
      rw [mul_right_comm, mul_le_mul_iff_left₀ (by simpa), ← le_div_iff₀' (by positivity),
        div_eq_inv_mul] at this
      change ENNReal.ofNNReal _ ≤ ENNReal.ofNNReal _
      gcongr
    grw [this, enorm_measure_le_variation, Measure.smul_apply]
/-
**MeasureTheory.VectorMeasure.variation_transpose_eq** 是 Mathlib 中的一个引理，位于命名空间 `
MeasureTheory.VectorMeasure`。
形式化陈述：variation_transpose_eq [Nontrivial E] (hB : forall x y, ‖B x y‖₊ = ‖x‖₊ * 
‖y‖₊) : (μ.transpose B).variation = μ.variation
参数：hB : forall x y, ‖B x y‖₊ = ‖x‖₊ * ‖y‖₊。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用引理 `MeasureTheory.VectorMeasure.variation_transpose_eq_smul`：variation_trans
pose_eq_smul [Nontrivial E] {C : Real>=0} (hB : forall x y, ‖B x y‖₊ = C * ‖x‖₊ 
* ‖y‖₊) : (μ.transpose B).variation = C • μ.v…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
lemma variation_transpose_eq [Nontrivial E] (hB : ∀ x y, ‖B x y‖₊ = ‖x‖₊ * ‖y‖₊) :
    (μ.transpose B).variation = μ.variation := by
  have : μ.variation = (1 : ℝ≥0) • μ.variation := by simp
  rw [this]
  apply variation_transpose_eq_smul
  simpa using hB

/-- Control of the variation of the vector measure which appears in the integral of scalar functions
with respect to a vector measure. -/
/-
**MeasureTheory.VectorMeasure.variation_transpose_lsmul** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.VectorMeasure`。
形式化陈述：∀ {X : Type u_2} {F : Type u_5} {mX : MeasurableSpace X} [inst : NormedAdd
CommGroup F] [inst_1 : NormedSpace ℝ F]   (μ : MeasureTheory.VectorMeasure X F),
 (μ.transpose (ContinuousLinearMap.lsmul ℝ ℝ)).variation = μ.variation
参数：μ : MeasureTheory.VectorMeasure X F；μ.transpose (ContinuousLinearMap.lsmul ℝ 
ℝ)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.VectorMeasure.variation_transpose_eq`：variation_transpose_
eq [Nontrivial E] (hB : forall x y, ‖B x y‖₊ = ‖x‖₊ * ‖y‖₊) : (μ.transpose B).va
riation = μ.variation
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nnnorm_smul`：nnnorm_smul (r : α) (x : β) : ‖r • x‖₊ = ‖r‖₊ * ‖x‖₊
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
Control of the variation of the vector measure which appears in the integral of 
scalar functions
with respect to a vector measure.
-/
@[simp] lemma variation_transpose_lsmul :
    (μ.transpose (ContinuousLinearMap.lsmul ℝ ℝ)).variation = μ.variation := by
  apply variation_transpose_eq
  simp [nnnorm_smul, mul_comm]

/-- Control of the variation of the vector measure which appears in the integral of a vector
function with respect to a signed measure. -/
/-
**MeasureTheory.VectorMeasure.variation_transpose_lsmul_flip** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：∀ {X : Type u_2} {E : Type u_4} {mX : MeasurableSpace X} [inst : NormedAdd
CommGroup E] [inst_1 : NormedSpace ℝ E]   [Nontrivial E] {μ : MeasureTheory.Sign
edMeasure X},   (MeasureTheory.VectorMeasure.transpose μ (ContinuousLinearMap.ls
mul ℝ ℝ).flip).variation =     MeasureTheory.VectorMeasure.variation μ
参数：MeasureTheory.VectorMeasure.transpose μ (ContinuousLinearMap.lsmul ℝ ℝ).flip。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.VectorMeasure.variation_transpose_eq`：variation_transpose_
eq [Nontrivial E] (hB : forall x y, ‖B x y‖₊ = ‖x‖₊ * ‖y‖₊) : (μ.transpose B).va
riation = μ.variation
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nnnorm_smul`：nnnorm_smul (r : α) (x : β) : ‖r • x‖₊ = ‖r‖₊ * ‖x‖₊
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
Control of the variation of the vector measure which appears in the integral of 
a vector
function with respect to a signed measure.
-/
@[simp] lemma variation_transpose_lsmul_flip [Nontrivial E] {μ : SignedMeasure X} :
    (μ.transpose (ContinuousLinearMap.lsmul ℝ ℝ (E := E)).flip).variation = μ.variation := by
  apply variation_transpose_eq
  simp [nnnorm_smul, mul_comm]

/-- `f : X → E` is said to be integrable with respect to `μ` and `B` if it is integrable with
respect to `(μ.transpose B).variation`. -/
/-
**MeasureTheory.VectorMeasure.Integrable** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheor
y.VectorMeasure`。
形式化陈述：{X : Type u_2} →   {E : Type u_4} →     {F : Type u_5} →       {mX : Measu
rableSpace X} →         [NormedAddCommGroup E] → [inst : NormedAddCommGroup F] →
 MeasureTheory.VectorMeasure X F → (X → E) → Prop
参数：X → E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f : X → E` is said to be integrable with respect to `μ` and `B` if it is integr
able with
respect to `(μ.transpose B).variation`.
-/
protected abbrev Integrable (μ : VectorMeasure X F) (f : X → E) : Prop :=
  MeasureTheory.Integrable f μ.variation

/-- `f : X → E` is said to be integrable with respect to `μ` and `B` on `s` if it is integrable with
respect to the vector measure `μ.restrict s`. When `s` is measurable, this is equivalent to
integrability with respect to `(μ.transpose B).variation.restrict s`. -/
/-
**MeasureTheory.VectorMeasure.IntegrableOn** 是 Mathlib 中的一个定义，位于命名空间 `MeasureThe
ory.VectorMeasure`。
形式化陈述：{X : Type u_2} →   {E : Type u_4} →     {F : Type u_5} →       {mX : Measu
rableSpace X} →         [NormedAddCommGroup E] →           [inst : NormedAddComm
Group F] → MeasureTheory.VectorMeasure X F → (X → E) → Set X → Prop
参数：X → E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f : X → E` is said to be integrable with respect to `μ` and `B` on `s` if it is
 integrable with
respect to the vector measure `μ.restrict s`. When `s` is measurable, this is eq
uivalent to
integrability with respect to `(μ.transpose B).variation.restrict s`.
-/
protected abbrev IntegrableOn
    (μ : VectorMeasure X F) (f : X → E) (s : Set X) : Prop :=
  (μ.restrict s).Integrable f

/-- The `G`-valued integral of `E`-valued function and the `F`-valued vector measure `μ` with linear
paring `B : E →L[ℝ] F →L[ℝ] G` . This is set to be `0` if `G` is not complete or if `f` is not
integrable with respect to `(μ.transpose B).variation`. Notation `∫ᵛ x, f x ∂[B; μ]`.

When `μ` is `G`-valued, to get the integral in `G` of a real-valued function, take
`B = ContinousLinearMap.lsmul ℝ ℝ`. Notation `∫ᵛ x, f x ∂•μ`.
When `μ` is a signed measure, to get the integral in `G` of a `G`-valued function, take
`B = (ContinousLinearMap.lsmul ℝ ℝ).flip`. Notation `∫ᵛ x, f x ∂<•μ`.
-/
/-
**MeasureTheory.VectorMeasure.integral** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.
VectorMeasure`。
形式化陈述：integral (μ : VectorMeasure X F) (f : X -> E) (B : E ->L[Real] F ->L[Real]
 G) : G
参数：μ : VectorMeasure X F；f : X -> E；B : E ->L[Real] F ->L[Real] G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_cbmApplyMeasure`：dominatedFinMeas
Additive_cbmApplyMeasure (μ : VectorMeasure X F) (B : E ->L[Real] F ->L[Real] G)
 : DominatedFinMeasAdditive μ.variation (μ.t…

--- 原说明 ---
The `G`-valued integral of `E`-valued function and the `F`-valued vector measure
 `μ` with linear
paring `B : E →L[ℝ] F →L[ℝ] G` . This is set to be `0` if `G` is not complete or
 if `f` is not
integrable with respect to `(μ.transpose B).variation`. Notation `∫ᵛ x, f x ∂[B;
 μ]`.

When `μ` is `G`-valued, to get the integral in `G` of a real-valued function, ta
ke
`B = ContinousLinearMap.lsmul ℝ ℝ`. Notation `∫ᵛ x, f x ∂•μ`.
When `μ` is a signed measure, to get the integral in `G` of a `G`-valued functio
n, take
`B = (ContinousLinearMap.lsmul ℝ ℝ).flip`. Notation `∫ᵛ x, f x ∂<•μ`.
-/
noncomputable def integral (μ : VectorMeasure X F) (f : X → E) (B : E →L[ℝ] F →L[ℝ] G) : G :=
  setToFun μ.variation (μ.transpose B)
    (dominatedFinMeasAdditive_cbmApplyMeasure μ B) f

@[inherit_doc integral]
notation3 "∫ᵛ "(...)", "r:60:(scoped f => f)" ∂["B:65"; "μ:65"]" => integral μ r B

/-- The special case of the pairing integral where the pairing is just the scalar multiplication by
`ℝ` on `F` and `f` is real-valued. The resulting integral is `F`-valued.-/
notation3 "∫ᵛ "(...)", "r:60:(scoped f => f)" ∂•"μ:70 => integral μ r (lsmul ℝ ℝ)

/-- The special case of the pairing integral where the pairing is just the flip of scalar
multiplication by `ℝ` on `F` and `f` is `F`-valued and `μ` is a signed measure.
The resulting integral is `F`-valued.-/
notation3 "∫ᵛ "(...)", "r:60:(scoped f => f)" ∂<•"μ:70 => integral μ r (lsmul ℝ ℝ).flip

@[inherit_doc integral]
notation3 "∫ᵛ "(...)" in "s", "r:60:(scoped f => f)" ∂["B:70"; "μ:70"]" =>
  integral (VectorMeasure.restrict μ s) r B

/-- The special case of the pairing integral in a set where the pairing is just the scalar
multiplication by `ℝ` on `F` and `f` is real-valued. The resulting integral is `F`-valued.-/
notation3 "∫ᵛ "(...)" in "s", "r:60:(scoped f => f)" ∂•"μ:70 =>
  integral (VectorMeasure.restrict μ s) r (lsmul ℝ ℝ)

/-- The special case of the pairing integral in a set where the pairing is just the flip of the
scalar multiplication by `ℝ` on `F` and `f` is `F`-valued and `μ` is a signed measure.
The resulting integral is `F`-valued.-/
notation3 "∫ᵛ "(...)" in "s", "r:60:(scoped f => f)" ∂<•"μ:70 =>
  integral (VectorMeasure.restrict μ s) r (lsmul ℝ ℝ).flip

variable {μ ν B}

/-
**MeasureTheory.VectorMeasure.integral_eq_setToFun** 是 Mathlib 中的一个引理，位于命名空间 `Me
asureTheory.VectorMeasure`。
形式化陈述：integral_eq_setToFun : ∫ᵛ x, f x ∂[B; μ] = setToFun μ.variation (μ.transpo
se B) (dominatedFinMeasAdditive_cbmApplyMeasure μ B) f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
lemma integral_eq_setToFun : ∫ᵛ x, f x ∂[B; μ] = setToFun μ.variation (μ.transpose B)
    (dominatedFinMeasAdditive_cbmApplyMeasure μ B) f := by rfl
/-
**MeasureTheory.VectorMeasure.integral_eq_setToFun_transpose** 是 Mathlib 中的一个引理，
位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：integral_eq_setToFun_transpose (hf : μ.Integrable f) : ∫ᵛ x, f x ∂[B; μ] =
 setToFun (μ.transpose B).variation (μ.transpose B) (dominatedFinMeasAdditive_tr
anspose_cbmApplyMeasure μ B) f
参数：hf : μ.Integrable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.setToFun_congr_measure_of_integrable`：setToFun_congr_measu
re_of_integrable {μ' : Measure α} (c' : Real>=0∞) (hc' : c' != ∞) (hμ'_le : μ' <
= c' • μ) (hT : DominatedFinMeasAdditive…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `MeasureTheory.VectorMeasure.variation_transpose_le`：variation_transpose_
le : (μ.transpose B).variation <= ‖B‖₊ • μ.variation
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_cbmApplyMeasure`：dominatedFinMeas
Additive_cbmApplyMeasure (μ : VectorMeasure X F) (B : E ->L[Real] F ->L[Real] G)
 : DominatedFinMeasAdditive μ.variation (μ.t…
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_transpose_cbmApplyMeasure`：domina
tedFinMeasAdditive_transpose_cbmApplyMeasure (μ : VectorMeasure X F) (B : E ->L[
Real] F ->L[Real] G) : DominatedFinMeasAdditive (μ.tra…
-/
lemma integral_eq_setToFun_transpose (hf : μ.Integrable f) :
    ∫ᵛ x, f x ∂[B; μ] = setToFun (μ.transpose B).variation (μ.transpose B)
      (dominatedFinMeasAdditive_transpose_cbmApplyMeasure μ B) f :=
  setToFun_congr_measure_of_integrable _ (by simp) (variation_transpose_le _ _) _ _ _ hf
/-
**MeasureTheory.VectorMeasure.integral_of_not_completeSpace** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：integral_of_not_completeSpace (hG : ¬CompleteSpace G) : ∫ᵛ x, f x ∂[B; μ] 
= 0
参数：hG : ¬CompleteSpace G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_cbmApplyMeasure`：dominatedFinMeas
Additive_cbmApplyMeasure (μ : VectorMeasure X F) (B : E ->L[Real] F ->L[Real] G)
 : DominatedFinMeasAdditive μ.variation (μ.t…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_of_not_completeSpace (hG : ¬CompleteSpace G) :
    ∫ᵛ x, f x ∂[B; μ] = 0 := by
  simp [integral, setToFun, hG]

variable {f g : X → E} {μ ν : VectorMeasure X F} {B C : E →L[ℝ] F →L[ℝ] G}

@[simp]
/-
**MeasureTheory.VectorMeasure.transpose_zero_cbm** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.VectorMeasure`。
形式化陈述：transpose_zero_cbm (μ : VectorMeasure X F) : μ.transpose (0 : E ->L[Real] 
F ->L[Real] G) = 0
参数：μ : VectorMeasure X F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.VectorMeasure.instIsZeroApplySet`：∀ {α : Type u_1} {m : Me
asurableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSp
ace M],   IsZeroApply (MeasureTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem transpose_zero_cbm (μ : VectorMeasure X F) :
    μ.transpose (0 : E →L[ℝ] F →L[ℝ] G) = 0 := by
  ext
  simp [transpose]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**MeasureTheory.VectorMeasure.transpose_add_vectorMeasure** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：transpose_add_vectorMeasure (μ ν : VectorMeasure X F) (B : E ->L[Real] F -
>L[Real] G) : (μ + ν).transpose B = μ.transpose B + ν.transpose B
参数：μ ν : VectorMeasure X F；B : E ->L[Real] F ->L[Real] G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.mapRange_add`：mapRange_add {v w : VectorMeas
ure α M} {f : M ->+ N} (hf : Continuous f) : (v + w).mapRange f hf = v.mapRange 
f hf + w.mapRange f hf
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem transpose_add_vectorMeasure (μ ν : VectorMeasure X F) (B : E →L[ℝ] F →L[ℝ] G) :
    (μ + ν).transpose B = μ.transpose B + ν.transpose B := by
  simp [transpose]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**MeasureTheory.VectorMeasure.transpose_add_cbm** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.VectorMeasure`。
形式化陈述：transpose_add_cbm (μ : VectorMeasure X F) (B C : E ->L[Real] F ->L[Real] G
) : μ.transpose (B + C) = μ.transpose B + μ.transpose C
参数：μ : VectorMeasure X F；B C : E ->L[Real] F ->L[Real] G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.VectorMeasure.instIsAddApplySet`：∀ {α : Type u_1} {m : Mea
surableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSpa
ce M]   [inst_2 : ContinuousAdd M],…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem transpose_add_cbm (μ : VectorMeasure X F) (B C : E →L[ℝ] F →L[ℝ] G) :
    μ.transpose (B + C) = μ.transpose B + μ.transpose C := by
  ext
  simp [transpose]

@[simp]
/-
**MeasureTheory.VectorMeasure.transpose_finsetSum_vectorMeasure** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：transpose_finsetSum_vectorMeasure (μ : ι -> VectorMeasure X F) (B : E ->L[
Real] F ->L[Real] G) (s : Finset ι) : (∑ i in s, μ i).transpose B = ∑ i in s, (μ
 i).transpose B
参数：μ : ι -> VectorMeasure X F；B : E ->L[Real] F ->L[Real] G；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.transpose_zero`：∀ {X : Type u_2} {E : Type u
_4} {F : Type u_5} {G : Type u_6} {mX : MeasurableSpace X} [inst : NormedAddComm
Group E]   [inst_1 : NormedSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MeasureTheory.VectorMeasure.transpose_add_vectorMeasure`：transpose_add_v
ectorMeasure (μ ν : VectorMeasure X F) (B : E ->L[Real] F ->L[Real] G) : (μ + ν)
.transpose B = μ.transpose B + ν.transpose B
-/
theorem transpose_finsetSum_vectorMeasure (μ : ι → VectorMeasure X F) (B : E →L[ℝ] F →L[ℝ] G)
    (s : Finset ι) :
    (∑ i ∈ s, μ i).transpose B = ∑ i ∈ s, (μ i).transpose B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s his ih => simp [Finset.sum_insert, his, ih]

@[simp]
/-
**MeasureTheory.VectorMeasure.transpose_finsetSum_cbm** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.VectorMeasure`。
形式化陈述：transpose_finsetSum_cbm (μ : VectorMeasure X F) (B : ι -> E ->L[Real] F ->
L[Real] G) (s : Finset ι) : μ.transpose (∑ i in s, B i) = ∑ i in s, μ.transpose 
(B i)
参数：μ : VectorMeasure X F；B : ι -> E ->L[Real] F ->L[Real] G；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.transpose_zero_cbm`：transpose_zero_cbm (μ : 
VectorMeasure X F) : μ.transpose (0 : E ->L[Real] F ->L[Real] G) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MeasureTheory.VectorMeasure.transpose_add_cbm`：transpose_add_cbm (μ : Ve
ctorMeasure X F) (B C : E ->L[Real] F ->L[Real] G) : μ.transpose (B + C) = μ.tra
nspose B + μ.transpose C
-/
theorem transpose_finsetSum_cbm (μ : VectorMeasure X F) (B : ι → E →L[ℝ] F →L[ℝ] G) (s : Finset ι) :
    μ.transpose (∑ i ∈ s, B i) = ∑ i ∈ s, μ.transpose (B i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s his ih => simp [Finset.sum_insert, his, ih]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**MeasureTheory.VectorMeasure.transpose_neg_vectorMeasure** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：transpose_neg_vectorMeasure (μ : VectorMeasure X F) (B : E ->L[Real] F ->L
[Real] G) : (-μ).transpose B = - (μ.transpose B)
参数：μ : VectorMeasure X F；B : E ->L[Real] F ->L[Real] G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `MeasureTheory.VectorMeasure.instIsNegApplySet`：∀ {α : Type u_1} {m : Mea
surableSpace α} {M : Type u_3} [inst : AddCommGroup M] [inst_1 : TopologicalSpac
e M]   [inst_2 : IsTopologicalAddGr…
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `ContinuousLinearMap.instIsNegApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem transpose_neg_vectorMeasure (μ : VectorMeasure X F) (B : E →L[ℝ] F →L[ℝ] G) :
    (-μ).transpose B = - (μ.transpose B) := by
  ext
  simp [transpose]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**MeasureTheory.VectorMeasure.transpose_neg_cbm** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.VectorMeasure`。
形式化陈述：transpose_neg_cbm (μ : VectorMeasure X F) (B : E ->L[Real] F ->L[Real] G) 
: μ.transpose (-B) = - (μ.transpose B)
参数：μ : VectorMeasure X F；B : E ->L[Real] F ->L[Real] G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Neg β}   {inst_2 : Neg F} [self : IsNe…
· 使用定理 `ContinuousLinearMap.instIsNegApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `MeasureTheory.VectorMeasure.instIsNegApplySet`：∀ {α : Type u_1} {m : Mea
surableSpace α} {M : Type u_3} [inst : AddCommGroup M] [inst_1 : TopologicalSpac
e M]   [inst_2 : IsTopologicalAddGr…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem transpose_neg_cbm (μ : VectorMeasure X F) (B : E →L[ℝ] F →L[ℝ] G) :
    μ.transpose (-B) = - (μ.transpose B) := by
  ext
  simp [transpose]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**MeasureTheory.VectorMeasure.transpose_sub_vectorMeasure** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：transpose_sub_vectorMeasure (μ ν : VectorMeasure X F) (B : E ->L[Real] F -
>L[Real] G) : (μ - ν).transpose B = μ.transpose B - ν.transpose B
参数：μ ν : VectorMeasure X F；B : E ->L[Real] F ->L[Real] G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Sub β}   {inst_2 : Sub F} [self : IsSu…
· 使用定理 `MeasureTheory.VectorMeasure.instIsSubApplySet`：∀ {α : Type u_1} {m : Mea
surableSpace α} {M : Type u_3} [inst : AddCommGroup M] [inst_1 : TopologicalSpac
e M]   [inst_2 : IsTopologicalAddGr…
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `ContinuousLinearMap.instIsSubApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem transpose_sub_vectorMeasure (μ ν : VectorMeasure X F) (B : E →L[ℝ] F →L[ℝ] G) :
    (μ - ν).transpose B = μ.transpose B - ν.transpose B := by
  ext
  simp [transpose]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**MeasureTheory.VectorMeasure.transpose_sub_cbm** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.VectorMeasure`。
形式化陈述：transpose_sub_cbm (μ : VectorMeasure X F) (B C : E ->L[Real] F ->L[Real] G
) : μ.transpose (B - C) = μ.transpose B - μ.transpose C
参数：μ : VectorMeasure X F；B C : E ->L[Real] F ->L[Real] G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Sub β}   {inst_2 : Sub F} [self : IsSu…
· 使用定理 `ContinuousLinearMap.instIsSubApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `MeasureTheory.VectorMeasure.instIsSubApplySet`：∀ {α : Type u_1} {m : Mea
surableSpace α} {M : Type u_3} [inst : AddCommGroup M] [inst_1 : TopologicalSpac
e M]   [inst_2 : IsTopologicalAddGr…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem transpose_sub_cbm (μ : VectorMeasure X F) (B C : E →L[ℝ] F →L[ℝ] G) :
    μ.transpose (B - C) = μ.transpose B - μ.transpose C := by
  ext
  simp [transpose]

section Function

set_option backward.isDefEq.respectTransparency.types false in
/-
**MeasureTheory.VectorMeasure.integral_undef** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.VectorMeasure`。
形式化陈述：integral_undef (h : ¬ μ.Integrable f) : ∫ᵛ x, f x ∂[B; μ] = 0
参数：h : ¬ μ.Integrable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setToFun_undef`：setToFun_undef (hT : DominatedFinMeasAddit
ive μ T C) (hf : ¬Integrable f μ) : setToFun μ T hT f = 0
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_cbmApplyMeasure`：dominatedFinMeas
Additive_cbmApplyMeasure (μ : VectorMeasure X F) (B : E ->L[Real] F ->L[Real] G)
 : DominatedFinMeasAdditive μ.variation (μ.t…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_undef (h : ¬ μ.Integrable f) :
    ∫ᵛ x, f x ∂[B; μ] = 0 := by
  simp [integral, setToFun_undef _ h]

@[simp]
/-
**MeasureTheory.VectorMeasure.integral_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.VectorMeasure`。
形式化陈述：integral_zero : ∫ᵛ _, 0 ∂[B; μ] = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.setToFun_zero`：setToFun_zero (hT : DominatedFinMeasAdditiv
e μ T C) : setToFun μ T hT (0 : α -> E) = 0
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_cbmApplyMeasure`：dominatedFinMeas
Additive_cbmApplyMeasure (μ : VectorMeasure X F) (B : E ->L[Real] F ->L[Real] G)
 : DominatedFinMeasAdditive μ.variation (μ.t…
-/
theorem integral_zero : ∫ᵛ _, 0 ∂[B; μ] = 0 :=
  setToFun_zero _
/-
**MeasureTheory.VectorMeasure.integral_congr_ae** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.VectorMeasure`。
形式化陈述：integral_congr_ae (h : f =ᵐ[μ.variation] g) : ∫ᵛ x, f x ∂[B; μ] = ∫ᵛ x, g 
x ∂[B; μ]
参数：h : f =ᵐ[μ.variation] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `MeasureTheory.setToFun_congr_ae`：setToFun_congr_ae (hT : DominatedFinMea
sAdditive μ T C) (h : f =ᵐ[μ] g) : setToFun μ T hT f = setToFun μ T hT g
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_cbmApplyMeasure`：dominatedFinMeas
Additive_cbmApplyMeasure (μ : VectorMeasure X F) (B : E ->L[Real] F ->L[Real] G)
 : DominatedFinMeasAdditive μ.variation (μ.t…
-/
theorem integral_congr_ae (h : f =ᵐ[μ.variation] g) :
    ∫ᵛ x, f x ∂[B; μ] = ∫ᵛ x, g x ∂[B; μ] :=
  setToFun_congr_ae _ h
/-
**MeasureTheory.VectorMeasure.integral_eq_zero_of_ae** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.VectorMeasure`。
形式化陈述：integral_eq_zero_of_ae (hf : f =ᵐ[μ.variation] 0) : ∫ᵛ x, f x ∂[B; μ] = 0
参数：hf : f =ᵐ[μ.variation] 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.integral_congr_ae`：integral_congr_ae (h : f 
=ᵐ[μ.variation] g) : ∫ᵛ x, f x ∂[B; μ] = ∫ᵛ x, g x ∂[B; μ]
· 使用定理 `MeasureTheory.VectorMeasure.integral_zero`：integral_zero : ∫ᵛ _, 0 ∂[B; 
μ] = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_eq_zero_of_ae (hf : f =ᵐ[μ.variation] 0) :
    ∫ᵛ x, f x ∂[B; μ] = 0 := by
  simp [integral_congr_ae hf]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-
**MeasureTheory.VectorMeasure.Integrable.add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.VectorMeasure.Integrable`。
形式化陈述：∀ {X : Type u_2} {E : Type u_4} {F : Type u_5} {mX : MeasurableSpace X} [i
nst : NormedAddCommGroup E]   [inst_1 : NormedAddCommGroup F] {f g : X → E} {μ :
 MeasureTheory.VectorMeasure X F},   μ.Integrable f → μ.Integrable g → μ.Integra
ble (f + g)
参数：f + g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.add`：∀ {α : Type u_1} {m : MeasurableSpace α} {
μ : MeasureTheory.Measure α} {ε' : Type u_8} [inst : TopologicalSpace ε']   [ins
t_1 : ESeminormedA…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
@[to_fun] lemma Integrable.add (hf : μ.Integrable f) (hg : μ.Integrable g) :
    μ.Integrable (f + g) :=
  MeasureTheory.Integrable.add hf hg

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-
**MeasureTheory.VectorMeasure.Integrable.neg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.VectorMeasure.Integrable`。
形式化陈述：∀ {X : Type u_2} {E : Type u_4} {F : Type u_5} {mX : MeasurableSpace X} [i
nst : NormedAddCommGroup E]   [inst_1 : NormedAddCommGroup F] {f : X → E} {μ : M
easureTheory.VectorMeasure X F}, μ.Integrable f → μ.Integrable (-f)
参数：-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.neg`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f :
 α → β}, MeasureTh…
-/
@[to_fun] lemma Integrable.neg (hf : μ.Integrable f) :
    μ.Integrable (-f) :=
  MeasureTheory.Integrable.neg hf

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-
**MeasureTheory.VectorMeasure.Integrable.sub** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.VectorMeasure.Integrable`。
形式化陈述：∀ {X : Type u_2} {E : Type u_4} {F : Type u_5} {mX : MeasurableSpace X} [i
nst : NormedAddCommGroup E]   [inst_1 : NormedAddCommGroup F] {f g : X → E} {μ :
 MeasureTheory.VectorMeasure X F},   μ.Integrable f → μ.Integrable g → μ.Integra
ble (f - g)
参数：f - g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.sub`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f g
 : α → β}, Measure…
-/
@[to_fun] lemma Integrable.sub (hf : μ.Integrable f) (hg : μ.Integrable g) :
    μ.Integrable (f - g) :=
  MeasureTheory.Integrable.sub hf hg

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-
**MeasureTheory.VectorMeasure.Integrable.smul** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.VectorMeasure.Integrable`。
形式化陈述：∀ {X : Type u_2} {E : Type u_4} {F : Type u_5} {mX : MeasurableSpace X} [i
nst : NormedAddCommGroup E]   [inst_1 : NormedAddCommGroup F] {f : X → E} {μ : M
easureTheory.VectorMeasure X F} {𝕜 : Type u_8}   [inst_2 : NormedAddCommGroup 𝕜]
 [inst_3 : SMulZeroClass 𝕜 E] [IsBoundedSMul 𝕜 E] (c : 𝕜),   μ.Integrable f → μ.
Integrable (c • f)
参数：c : 𝕜；c • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.smul`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {𝕜 
: Type u_8} [inst_1…
-/
@[to_fun] lemma Integrable.smul {𝕜 : Type*} [NormedAddCommGroup 𝕜] [SMulZeroClass 𝕜 E]
    [IsBoundedSMul 𝕜 E] (c : 𝕜) (hf : μ.Integrable f) :
    μ.Integrable (c • f) :=
  MeasureTheory.Integrable.smul c hf

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-
**MeasureTheory.VectorMeasure.Integrable.finsetSum** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.VectorMeasure.Integrable`。
形式化陈述：∀ {X : Type u_2} {E : Type u_4} {F : Type u_5} {mX : MeasurableSpace X} [i
nst : NormedAddCommGroup E]   [inst_1 : NormedAddCommGroup F] {μ : MeasureTheory
.VectorMeasure X F} {ι : Type u_8} (s : Finset ι) {f : ι → X → E},   (∀ i ∈ s, μ
.Integrable (f i)) → μ.Integrable (∑ i ∈ s, f i)
参数：s : Finset ι；∀ i ∈ s, μ.Integrable (f i)；∑ i ∈ s, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integrable_finsetSum'`：integrable_finsetSum' {ι} (s : Fins
et ι) {f : ι -> α -> ε'} (hf : forall i in s, Integrable (f i) μ) : Integrable (
∑ i in s, f i) μ
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem Integrable.finsetSum {ι : Type*} (s : Finset ι) {f : ι → X → E}
    (hf : ∀ i ∈ s, μ.Integrable (f i)) : μ.Integrable (∑ i ∈ s, f i) :=
  integrable_finsetSum' s hf

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-
**MeasureTheory.VectorMeasure.Integrable.fun_finsetSum** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.VectorMeasure.Integrable`。
形式化陈述：∀ {X : Type u_2} {E : Type u_4} {F : Type u_5} {mX : MeasurableSpace X} [i
nst : NormedAddCommGroup E]   [inst_1 : NormedAddCommGroup F] {μ : MeasureTheory
.VectorMeasure X F} {ι : Type u_8} (s : Finset ι) {f : ι → X → E},   (∀ i ∈ s, μ
.Integrable (f i)) → μ.Integrable fun x => ∑ i ∈ s, f i x
参数：s : Finset ι；∀ i ∈ s, μ.Integrable (f i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integrable_finsetSum`：integrable_finsetSum {ι} (s : Finset
 ι) {f : ι -> α -> ε'} (hf : forall i in s, Integrable (f i) μ) : Integrable (fu
n a => ∑ i in s, f i a) …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem Integrable.fun_finsetSum {ι : Type*} (s : Finset ι) {f : ι → X → E}
    (hf : ∀ i ∈ s, μ.Integrable (f i)) : μ.Integrable (fun x ↦ ∑ i ∈ s, f i x) :=
  integrable_finsetSum s hf
/-
**MeasureTheory.VectorMeasure.integral_fun_add** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.VectorMeasure`。
形式化陈述：integral_fun_add (hf : μ.Integrable f) (hg : μ.Integrable g) : ∫ᵛ x, f x +
 g x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ] + ∫ᵛ x, g x ∂[B; μ]
参数：hf : μ.Integrable f；hg : μ.Integrable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.setToFun_add`：setToFun_add (hT : DominatedFinMeasAdditive 
μ T C) (hf : Integrable f μ) (hg : Integrable g μ) : setToFun μ T hT (f + g) = s
etToFun μ T hT f…
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_cbmApplyMeasure`：dominatedFinMeas
Additive_cbmApplyMeasure (μ : VectorMeasure X F) (B : E ->L[Real] F ->L[Real] G)
 : DominatedFinMeasAdditive μ.variation (μ.t…
-/
theorem integral_fun_add (hf : μ.Integrable f) (hg : μ.Integrable g) :
    ∫ᵛ x, f x + g x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ] + ∫ᵛ x, g x ∂[B; μ] :=
  setToFun_add _ hf hg
/-
**MeasureTheory.VectorMeasure.integral_add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.VectorMeasure`。
形式化陈述：integral_add (hf : μ.Integrable f) (hg : μ.Integrable g) : ∫ᵛ x, (f + g) x
 ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ] + ∫ᵛ x, g x ∂[B; μ]
参数：hf : μ.Integrable f；hg : μ.Integrable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.VectorMeasure.integral_fun_add`：integral_fun_add (hf : μ.I
ntegrable f) (hg : μ.Integrable g) : ∫ᵛ x, f x + g x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ]
 + ∫ᵛ x, g x ∂[B; μ]
-/
theorem integral_add (hf : μ.Integrable f) (hg : μ.Integrable g) :
    ∫ᵛ x, (f + g) x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ] + ∫ᵛ x, g x ∂[B; μ] := integral_fun_add hf hg
/-
**MeasureTheory.VectorMeasure.integral_finsetSum** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.VectorMeasure`。
形式化陈述：integral_finsetSum (s : Finset ι) {f : ι -> X -> E} (hf : forall i in s, μ
.Integrable (f i)) : ∫ᵛ x, ∑ i in s, f i x ∂[B; μ] = ∑ i in s, ∫ᵛ x, f i x ∂[B; 
μ]
参数：s : Finset ι；hf : forall i in s, μ.Integrable (f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.setToFun_finsetSum`：setToFun_finsetSum (hT : DominatedFinM
easAdditive μ T C) {ι} (s : Finset ι) {f : ι -> α -> E} (hf : forall i in s, Int
egrable (f i) μ) : (se…
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_cbmApplyMeasure`：dominatedFinMeas
Additive_cbmApplyMeasure (μ : VectorMeasure X F) (B : E ->L[Real] F ->L[Real] G)
 : DominatedFinMeasAdditive μ.variation (μ.t…
-/
theorem integral_finsetSum (s : Finset ι) {f : ι → X → E}
    (hf : ∀ i ∈ s, μ.Integrable (f i)) :
    ∫ᵛ x, ∑ i ∈ s, f i x ∂[B; μ] = ∑ i ∈ s, ∫ᵛ x, f i x ∂[B; μ] :=
  setToFun_finsetSum _ s hf

variable (f μ B) in
@[integral_simps]
/-
**MeasureTheory.VectorMeasure.integral_fun_neg** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.VectorMeasure`。
形式化陈述：integral_fun_neg (f : X -> E) : ∫ᵛ x, -f x ∂[B; μ]= -∫ᵛ x, f x ∂[B; μ]
参数：f : X -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.setToFun_neg`：setToFun_neg (hT : DominatedFinMeasAdditive 
μ T C) (f : α -> E) : setToFun μ T hT (-f) = -setToFun μ T hT f
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_cbmApplyMeasure`：dominatedFinMeas
Additive_cbmApplyMeasure (μ : VectorMeasure X F) (B : E ->L[Real] F ->L[Real] G)
 : DominatedFinMeasAdditive μ.variation (μ.t…
-/
theorem integral_fun_neg (f : X → E) :
    ∫ᵛ x, -f x ∂[B; μ]= -∫ᵛ x, f x ∂[B; μ] :=
  setToFun_neg _ f

variable (f μ B) in
@[integral_simps]
/-
**MeasureTheory.VectorMeasure.integral_neg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.VectorMeasure`。
形式化陈述：integral_neg : ∫ᵛ x, (-f) x ∂[B; μ] = -∫ᵛ x, f x ∂[B; μ]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.VectorMeasure.integral_fun_neg`：integral_fun_neg (f : X ->
 E) : ∫ᵛ x, -f x ∂[B; μ]= -∫ᵛ x, f x ∂[B; μ]
-/
theorem integral_neg :
    ∫ᵛ x, (-f) x ∂[B; μ] = -∫ᵛ x, f x ∂[B; μ] := integral_fun_neg μ B f
/-
**MeasureTheory.VectorMeasure.integral_fun_sub** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.VectorMeasure`。
形式化陈述：integral_fun_sub (hf : μ.Integrable f) (hg : μ.Integrable g) : ∫ᵛ x, f x -
 g x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ] - ∫ᵛ x, g x ∂[B; μ]
参数：hf : μ.Integrable f；hg : μ.Integrable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.setToFun_sub`：setToFun_sub (hT : DominatedFinMeasAdditive 
μ T C) (hf : Integrable f μ) (hg : Integrable g μ) : setToFun μ T hT (f - g) = s
etToFun μ T hT f…
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_cbmApplyMeasure`：dominatedFinMeas
Additive_cbmApplyMeasure (μ : VectorMeasure X F) (B : E ->L[Real] F ->L[Real] G)
 : DominatedFinMeasAdditive μ.variation (μ.t…
-/
theorem integral_fun_sub (hf : μ.Integrable f) (hg : μ.Integrable g) :
    ∫ᵛ x, f x - g x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ] - ∫ᵛ x, g x ∂[B; μ] :=
  setToFun_sub _ hf hg
/-
**MeasureTheory.VectorMeasure.integral_sub** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.VectorMeasure`。
形式化陈述：integral_sub (hf : μ.Integrable f) (hg : μ.Integrable g) : ∫ᵛ x, (f - g) x
 ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ] - ∫ᵛ x, g x ∂[B; μ]
参数：hf : μ.Integrable f；hg : μ.Integrable g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.VectorMeasure.integral_fun_sub`：integral_fun_sub (hf : μ.I
ntegrable f) (hg : μ.Integrable g) : ∫ᵛ x, f x - g x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ]
 - ∫ᵛ x, g x ∂[B; μ]
-/
theorem integral_sub (hf : μ.Integrable f) (hg : μ.Integrable g) :
    ∫ᵛ x, (f - g) x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ] - ∫ᵛ x, g x ∂[B; μ] := integral_fun_sub hf hg

variable (f μ B) in
@[integral_simps]
/-
**MeasureTheory.VectorMeasure.integral_fun_smul** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.VectorMeasure`。
形式化陈述：integral_fun_smul (c : Real) (f : X -> E) : ∫ᵛ x, c • f x ∂[B; μ] = c • ∫ᵛ
 x, f x ∂[B; μ]
参数：c : Real；f : X -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.setToFun_smul`：setToFun_smul [NormedDivisionRing 𝕜] [Modul
e 𝕜 E] [NormSMulClass 𝕜 E] [Module 𝕜 F] [NormSMulClass 𝕜 F] (hT : DominatedFinMe
asAdditive μ T C)…
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_cbmApplyMeasure`：dominatedFinMeas
Additive_cbmApplyMeasure (μ : VectorMeasure X F) (B : E ->L[Real] F ->L[Real] G)
 : DominatedFinMeasAdditive μ.variation (μ.t…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem integral_fun_smul (c : ℝ) (f : X → E) :
    ∫ᵛ x, c • f x ∂[B; μ] = c • ∫ᵛ x, f x ∂[B; μ] :=
  setToFun_smul _ (by simp) c f

variable (f μ B) in
@[integral_simps]
/-
**MeasureTheory.VectorMeasure.integral_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.VectorMeasure`。
形式化陈述：integral_smul (c : Real) : ∫ᵛ x, (c • f) x ∂[B; μ] = c • ∫ᵛ x, f x ∂[B; μ]
参数：c : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.VectorMeasure.integral_fun_smul`：integral_fun_smul (c : Re
al) (f : X -> E) : ∫ᵛ x, c • f x ∂[B; μ] = c • ∫ᵛ x, f x ∂[B; μ]
-/
theorem integral_smul (c : ℝ) :
    ∫ᵛ x, (c • f) x ∂[B; μ] = c • ∫ᵛ x, f x ∂[B; μ] := integral_fun_smul μ B c f

@[simp]
/-
**MeasureTheory.VectorMeasure.integral_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.VectorMeasure`。
形式化陈述：integral_const [CompleteSpace G] [IsFiniteMeasure μ.variation] (c : E) : ∫
ᵛ _ : X, c ∂[B; μ] = B c (μ univ)
参数：c : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `MeasureTheory.setToFun_const`：setToFun_const [CompleteSpace F] [IsFinite
Measure μ] (hT : DominatedFinMeasAdditive μ T C) (x : E) : (setToFun μ T hT fun 
_ => x) = T univ x
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_cbmApplyMeasure`：dominatedFinMeas
Additive_cbmApplyMeasure (μ : VectorMeasure X F) (B : E ->L[Real] F ->L[Real] G)
 : DominatedFinMeasAdditive μ.variation (μ.t…
-/
theorem integral_const [CompleteSpace G] [IsFiniteMeasure μ.variation] (c : E) :
    ∫ᵛ _ : X, c ∂[B; μ] = B c (μ univ) :=
  setToFun_const _ _

end Function

section VectorMeasure

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/- `simpNF` complains that this lemma can be proved by `simp`, because the `simp`-generated lemma
unfolds the abbrev `VectorMeasure.Integrable`. TODO: fix `simp`. See lean4#13958. -/
@[nolint simpNF, simp]
/-
**MeasureTheory.VectorMeasure.Integrable.zero_vectorMeasure** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.VectorMeasure.Integrable`。
形式化陈述：∀ {X : Type u_2} {E : Type u_4} {F : Type u_5} {mX : MeasurableSpace X} [i
nst : NormedAddCommGroup E]   [inst_1 : NormedAddCommGroup F] {f : X → E}, Measu
reTheory.VectorMeasure.Integrable 0 f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.VectorMeasure.variation_zero`：variation_zero : (0 : Vector
Measure X V).variation = 0

--- 原说明 ---
`simpNF` complains that this lemma can be proved by `simp`, because the `simp`-g
enerated lemma
unfolds the abbrev `VectorMeasure.Integrable`. TODO: fix `simp`. See lean4#13958
.
-/
lemma Integrable.zero_vectorMeasure : (0 : VectorMeasure X F).Integrable f := by
  simp [VectorMeasure.Integrable]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-
**MeasureTheory.VectorMeasure.Integrable.add_vectorMeasure** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.VectorMeasure.Integrable`。
形式化陈述：∀ {X : Type u_2} {E : Type u_4} {F : Type u_5} {mX : MeasurableSpace X} [i
nst : NormedAddCommGroup E]   [inst_1 : NormedAddCommGroup F] {f : X → E} {μ ν :
 MeasureTheory.VectorMeasure X F},   μ.Integrable f → ν.Integrable f → (μ + ν).I
ntegrable f
参数：μ + ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.mono_measure`：∀ {α : Type u_1} {ε : Type u_5} {
m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [inst : TopologicalSpace 
ε]   [inst_1 : ContinuousEN…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.integrable_add_measure`：integrable_add_measure [PseudoMetr
izableSpace ε] {f : α -> ε} : Integrable f (μ + ν) ↔ Integrable f μ ∧ Integrable
 f ν
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用引理 `MeasureTheory.VectorMeasure.variation_add_le`：variation_add_le [Continuo
usAdd V] : variation (μ + ν) <= variation μ + variation ν
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma Integrable.add_vectorMeasure (hμ : μ.Integrable f) (hν : ν.Integrable f) :
    (μ + ν).Integrable f := by
  apply Integrable.mono_measure (integrable_add_measure.2 ⟨hμ, hν⟩)
  grw [variation_add_le]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-
**MeasureTheory.VectorMeasure.Integrable.neg_vectorMeasure** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.VectorMeasure.Integrable`。
形式化陈述：∀ {X : Type u_2} {E : Type u_4} {F : Type u_5} {mX : MeasurableSpace X} [i
nst : NormedAddCommGroup E]   [inst_1 : NormedAddCommGroup F] {f : X → E} {μ : M
easureTheory.VectorMeasure X F}, μ.Integrable f → (-μ).Integrable f
参数：-μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.mono_measure`：∀ {α : Type u_1} {ε : Type u_5} {
m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [inst : TopologicalSpace 
ε]   [inst_1 : ContinuousEN…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.VectorMeasure.variation_neg`：variation_neg : (-μ).variatio
n = μ.variation
-/
lemma Integrable.neg_vectorMeasure (hμ : μ.Integrable f) :
    (-μ).Integrable f :=
  Integrable.mono_measure hμ (by simp)

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-
**MeasureTheory.VectorMeasure.Integrable.sub_vectorMeasure** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.VectorMeasure.Integrable`。
形式化陈述：∀ {X : Type u_2} {E : Type u_4} {F : Type u_5} {mX : MeasurableSpace X} [i
nst : NormedAddCommGroup E]   [inst_1 : NormedAddCommGroup F] {f : X → E} {μ ν :
 MeasureTheory.VectorMeasure X F},   μ.Integrable f → ν.Integrable f → (μ - ν).I
ntegrable f
参数：μ - ν。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `MeasureTheory.VectorMeasure.Integrable.add_vectorMeasure`：∀ {X : Type u_
2} {E : Type u_4} {F : Type u_5} {mX : MeasurableSpace X} [inst : NormedAddCommG
roup E]   [inst_1 : NormedAddCommGroup F] {f :…
· 使用定理 `MeasureTheory.VectorMeasure.Integrable.neg_vectorMeasure`：∀ {X : Type u_
2} {E : Type u_4} {F : Type u_5} {mX : MeasurableSpace X} [inst : NormedAddCommG
roup E]   [inst_1 : NormedAddCommGroup F] {f :…
-/
lemma Integrable.sub_vectorMeasure (hμ : μ.Integrable f) (hν : ν.Integrable f) :
    (μ - ν).Integrable f := by
  convert hμ.add_vectorMeasure hν.neg_vectorMeasure using 1
  exact sub_eq_add_neg μ ν

omit [NormedSpace ℝ E] in
/-
**MeasureTheory.VectorMeasure.Integrable.smul_vectorMeasure** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.VectorMeasure.Integrable`。
形式化陈述：∀ {X : Type u_2} {E : Type u_4} {F : Type u_5} {mX : MeasurableSpace X} [i
nst : NormedAddCommGroup E]   [inst_1 : NormedAddCommGroup F] [inst_2 : NormedSp
ace ℝ F] {f : X → E} {μ : MeasureTheory.VectorMeasure X F},   μ.Integrable f → ∀
 (c : ℝ), (c • μ).Integrable f
参数：c : ℝ；c • μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.mono_measure`：∀ {α : Type u_1} {ε : Type u_5} {
m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [inst : TopologicalSpace 
ε]   [inst_1 : ContinuousEN…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MeasureTheory.Integrable.smul_measure_nnreal`：∀ {α : Type u_1} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} {ε : Type u_8} [inst : TopologicalS
pace ε]   [inst_1 : ESeminormedAdd…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.VectorMeasure.variation_smul`：variation_smul {𝕜 : Type*} [
NormedField 𝕜] [NormedSpace 𝕜 V] {c : 𝕜} : (c • μ).variation = ‖c‖₊ • μ.variatio
n
-/
lemma Integrable.smul_vectorMeasure (hμ : μ.Integrable f) (c : ℝ) :
    (c • μ).Integrable f := by
  apply Integrable.mono_measure (Integrable.smul_measure_nnreal hμ (c := ‖c‖₊))
  simp [variation_smul]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-
**MeasureTheory.VectorMeasure.Integrable.finsetSum_vectorMeasure** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory.VectorMeasure.Integrable`。
形式化陈述：∀ {X : Type u_2} {E : Type u_4} {F : Type u_5} {mX : MeasurableSpace X} [i
nst : NormedAddCommGroup E]   [inst_1 : NormedAddCommGroup F] {f : X → E} {ι : T
ype u_8} {μ : ι → MeasureTheory.VectorMeasure X F} {s : Finset ι},   (∀ i ∈ s, (
μ i).Integrable f) → (∑ i ∈ s, μ i).Integrable f
参数：∀ i ∈ s, (μ i).Integrable f；∑ i ∈ s, μ i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MeasureTheory.VectorMeasure.Integrable.add_vectorMeasure`：∀ {X : Type u_
2} {E : Type u_4} {F : Type u_5} {mX : MeasurableSpace X} [inst : NormedAddCommG
roup E]   [inst_1 : NormedAddCommGroup F] {f :…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma Integrable.finsetSum_vectorMeasure {ι : Type*} {μ : ι → VectorMeasure X F} {s : Finset ι}
    (h : ∀ i ∈ s, (μ i).Integrable f) :
    (∑ i ∈ s, μ i).Integrable f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      simp only [Finset.mem_insert, forall_eq_or_imp, ha, not_false_eq_true,
        Finset.sum_insert] at h ⊢
      exact h.1.add_vectorMeasure (ih h.2)

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-
**MeasureTheory.VectorMeasure.Integrable.restrict** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.VectorMeasure.Integrable`。
形式化陈述：∀ {X : Type u_2} {E : Type u_4} {F : Type u_5} {mX : MeasurableSpace X} [i
nst : NormedAddCommGroup E]   [inst_1 : NormedAddCommGroup F] {f : X → E} {μ : M
easureTheory.VectorMeasure X F},   μ.Integrable f → ∀ {s : Set X}, (μ.restrict s
).Integrable f
参数：μ.restrict s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.VectorMeasure.variation_restrict`：variation_restrict (hs :
 MeasurableSet s) : (μ.restrict s).variation = μ.variation.restrict s
· 使用定理 `MeasureTheory.Integrable.restrict`：∀ {α : Type u_1} {m : MeasurableSpace
 α} {μ : MeasureTheory.Measure α} {ε : Type u_8} [inst : TopologicalSpace ε]   [
inst_1 : ContinuousENor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.VectorMeasure.restrict_not_measurable`：restrict_not_measur
able {i : Set α} (hi : ¬MeasurableSet i) : v.restrict i = 0
-/
lemma Integrable.restrict (hf : μ.Integrable f) {s : Set X} :
    (μ.restrict s).Integrable f := by
  by_cases hs : MeasurableSet s
  · simpa [VectorMeasure.Integrable, transpose_restrict, variation_restrict hs] using
      MeasureTheory.Integrable.restrict hf
  · simp [restrict_not_measurable _ hs]

@[simp]
/-
**MeasureTheory.VectorMeasure.integral_zero_vectorMeasure** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：integral_zero_vectorMeasure : ∫ᵛ x, f x ∂[B; (0 : VectorMeasure X F)] = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_cbmApplyMeasure`：dominatedFinMeas
Additive_cbmApplyMeasure (μ : VectorMeasure X F) (B : E ->L[Real] F ->L[Real] G)
 : DominatedFinMeasAdditive μ.variation (μ.t…
· 使用定理 `MeasureTheory.VectorMeasure.transpose_zero`：∀ {X : Type u_2} {E : Type u
_4} {F : Type u_5} {G : Type u_6} {mX : MeasurableSpace X} [inst : NormedAddComm
Group E]   [inst_1 : NormedSpace…
· 使用定理 `FunLike.coe_zero`：∀ {F : Type u_3} {α : Type u_5} {β : Type u_6} [inst :
 FunLike F α β] [inst_1 : Zero F] [inst_2 : Zero β]   [IsZeroApply F α β], ⇑0 = 
0
· 使用定理 `MeasureTheory.VectorMeasure.instIsZeroApplySet`：∀ {α : Type u_1} {m : Me
asurableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSp
ace M],   IsZeroApply (MeasureTheory…
· 使用引理 `MeasureTheory.VectorMeasure.variation_zero`：variation_zero : (0 : Vector
Measure X V).variation = 0
· 使用定理 `MeasureTheory.setToFun.congr_simp`：∀ {α : Type u_1} {E : Type u_2} {F : 
Type u_3} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : N
ormedAddCommGroup F] [i…
· 使用定理 `MeasureTheory.setToFun_zero_left`：setToFun_zero_left {hT : DominatedFinM
easAdditive μ (0 : Set α -> E ->L[Real] F) C} : setToFun μ 0 hT f = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_zero_vectorMeasure :
    ∫ᵛ x, f x ∂[B; (0 : VectorMeasure X F)] = 0 := by simp [integral, FunLike.coe_zero]
/-
**MeasureTheory.VectorMeasure.integral_of_isEmpty** 是 Mathlib 中的一个引理，位于命名空间 `Mea
sureTheory.VectorMeasure`。
形式化陈述：integral_of_isEmpty [IsEmpty X] : ∫ᵛ x, f x ∂[B; μ] = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.eq_zero_of_isEmpty`：eq_zero_of_isEmpty [IsEm
pty α] (μ : VectorMeasure α M) : μ = 0
· 使用定理 `MeasureTheory.VectorMeasure.integral_zero_vectorMeasure`：integral_zero_v
ectorMeasure : ∫ᵛ x, f x ∂[B; (0 : VectorMeasure X F)] = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma integral_of_isEmpty [IsEmpty X] : ∫ᵛ x, f x ∂[B; μ] = 0 := by simp [eq_zero_of_isEmpty]

@[simp]
/-
**MeasureTheory.VectorMeasure.integral_smul_vectorMeasure** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：integral_smul_vectorMeasure (f : X -> E) (c : Real) : ∫ᵛ x, f x ∂[B; c • μ
] = c • ∫ᵛ x, f x ∂[B; μ]
参数：f : X -> E；c : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_cbmApplyMeasure`：dominatedFinMeas
Additive_cbmApplyMeasure (μ : VectorMeasure X F) (B : E ->L[Real] F ->L[Real] G)
 : DominatedFinMeasAdditive μ.variation (μ.t…
· 使用定理 `MeasureTheory.DominatedFinMeasAdditive.smul`：smul [SeminormedAddGroup 𝕜]
 [DistribSMul 𝕜 β] [IsBoundedSMul 𝕜 β] (hT : DominatedFinMeasAdditive μ T C) (c 
: 𝕜) : DominatedFinMeasAdditive μ…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MeasureTheory.VectorMeasure.variation_smul`：variation_smul {𝕜 : Type*} [
NormedField 𝕜] [NormedSpace 𝕜 V] {c : 𝕜} : (c • μ).variation = ‖c‖₊ • μ.variatio
n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.setToFun.congr_simp`：∀ {α : Type u_1} {E : Type u_2} {F : 
Type u_3} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : N
ormedAddCommGroup F] [i…
· 使用引理 `MeasureTheory.VectorMeasure.transpose_smul`：transpose_smul (c : Real) : 
(c • μ).transpose B = c • μ.transpose B
· 使用定理 `FunLike.coe_smul`：coe_smul [SMul M F] [SMul M β] [IsSMulApply M F α β] (
n : M) (f : F) : ↑(n • f) = n • (f : α -> β)
· 使用定理 `MeasureTheory.VectorMeasure.instIsSMulApplySet`：∀ {α : Type u_1} {m : Me
asurableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSp
ace M]   {R : Type u_4} [inst_2 : Se…
· 使用定理 `Mathlib.Tactic.DepRewrite.eq_of_heq`：eq_of_heq.{u} {α : Sort u} {a a' : 
α} (h : a ≍ a') : a = a'
· 使用定理 `Mathlib.Tactic.DepRewrite.hdcongrArg`：hdcongrArg.{u, v} {α : Sort u} {a 
a' : α} {β : (a' : α) -> a = a' -> Sort v} (h : a = a') (f : (a' : α) -> (h : a 
= a') -> β a' h) : f a rfl…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setToFun_congr_smul_measure'`：setToFun_congr_smul_measure'
 (c : Real>=0) (hT : DominatedFinMeasAdditive μ T C) (hT_smul : DominatedFinMeas
Additive (c • μ) T C') (f : α ->…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem integral_smul_vectorMeasure (f : X → E) (c : ℝ) :
    ∫ᵛ x, f x ∂[B; c • μ] = c • ∫ᵛ x, f x ∂[B; μ] := by
  by_cases hG : CompleteSpace G; swap
  · simp [integral, setToFun, hG]
  simp_rw [integral, ← setToFun_smul_left]
  have : (c • μ).variation = ‖c‖₊ • μ.variation := by
    simp [variation_smul]
  simp only [this]
  have : DominatedFinMeasAdditive μ.variation ((c • μ).transpose B) (‖c‖ * ‖B‖) := by
    simp only [transpose_smul, FunLike.coe_smul]
    exact (dominatedFinMeasAdditive_cbmApplyMeasure μ B).smul c
  rw! [← setToFun_congr_smul_measure' _ this, transpose_smul]
  rfl

@[simp]
/-
**MeasureTheory.VectorMeasure.integral_smul_nnreal_vectorMeasure** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：integral_smul_nnreal_vectorMeasure (f : X -> E) (c : Real>=0) : ∫ᵛ x, f x 
∂[B; c • μ] = c • ∫ᵛ x, f x ∂[B; μ]
参数：f : X -> E；c : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.VectorMeasure.integral_smul_vectorMeasure`：integral_smul_v
ectorMeasure (f : X -> E) (c : Real) : ∫ᵛ x, f x ∂[B; c • μ] = c • ∫ᵛ x, f x ∂[B
; μ]
-/
theorem integral_smul_nnreal_vectorMeasure (f : X → E) (c : ℝ≥0) :
    ∫ᵛ x, f x ∂[B; c • μ] = c • ∫ᵛ x, f x ∂[B; μ] :=
  integral_smul_vectorMeasure f (c : ℝ)

set_option backward.isDefEq.respectTransparency.types false in
/-
**MeasureTheory.VectorMeasure.integral_add_vectorMeasure** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.VectorMeasure`。
形式化陈述：integral_add_vectorMeasure (hμ : μ.Integrable f) (hν : ν.Integrable f) : ∫
ᵛ x, f x ∂[B; μ + ν] = ∫ᵛ x, f x ∂[B; μ] + ∫ᵛ x, f x ∂[B; ν]
参数：hμ : μ.Integrable f；hν : ν.Integrable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.setToFun_add_left''`：setToFun_add_left'' {hT : DominatedFi
nMeasAdditive μ T C} {hT' : DominatedFinMeasAdditive μ' T' C'} {hT'' : Dominated
FinMeasAdditive μ'' T''…
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_cbmApplyMeasure`：dominatedFinMeas
Additive_cbmApplyMeasure (μ : VectorMeasure X F) (B : E ->L[Real] F ->L[Real] G)
 : DominatedFinMeasAdditive μ.variation (μ.t…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.mapRange_add`：mapRange_add {v w : VectorMeas
ure α M} {f : M ->+ N} (hf : Continuous f) : (v + w).mapRange f hf = v.mapRange 
f hf + w.mapRange f hf
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `MeasureTheory.VectorMeasure.instIsAddApplySet`：∀ {α : Type u_1} {m : Mea
surableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSpa
ce M]   [inst_2 : ContinuousAdd M],…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用引理 `MeasureTheory.VectorMeasure.variation_add_le`：variation_add_le [Continuo
usAdd V] : variation (μ + ν) <= variation μ + variation ν
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem integral_add_vectorMeasure (hμ : μ.Integrable f) (hν : ν.Integrable f) :
    ∫ᵛ x, f x ∂[B; μ + ν] = ∫ᵛ x, f x ∂[B; μ] + ∫ᵛ x, f x ∂[B; ν] :=
  setToFun_add_left'' (by simp [transpose]) hμ hν (by grw [variation_add_le])
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
/-
**MeasureTheory.VectorMeasure.integral_finsetSum_vectorMeasure** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：integral_finsetSum_vectorMeasure {μ : ι -> VectorMeasure X F} {s : Finset 
ι} (hf : forall i in s, (μ i).Integrable f) : ∫ᵛ x, f x ∂[B; ∑ i in s, μ i] = ∑ 
i in s, ∫ᵛ x, f x ∂[B; μ i]
参数：hf : forall i in s, (μ i).Integrable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.integral_zero_vectorMeasure`：integral_zero_v
ectorMeasure : ∫ᵛ x, f x ∂[B; (0 : VectorMeasure X F)] = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MeasureTheory.VectorMeasure.integral_add_vectorMeasure`：integral_add_vec
torMeasure (hμ : μ.Integrable f) (hν : ν.Integrable f) : ∫ᵛ x, f x ∂[B; μ + ν] =
 ∫ᵛ x, f x ∂[B; μ] + ∫ᵛ x, f x ∂[B; ν]
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `MeasureTheory.VectorMeasure.Integrable.finsetSum_vectorMeasure`：∀ {X : T
ype u_2} {E : Type u_4} {F : Type u_5} {mX : MeasurableSpace X} [inst : NormedAd
dCommGroup E]   [inst_1 : NormedAddCommGroup F] {f :…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem integral_finsetSum_vectorMeasure {μ : ι → VectorMeasure X F}
    {s : Finset ι} (hf : ∀ i ∈ s, (μ i).Integrable f) :
    ∫ᵛ x, f x ∂[B; ∑ i ∈ s, μ i] = ∑ i ∈ s, ∫ᵛ x, f x ∂[B; μ i] := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.mem_insert, forall_eq_or_imp, ha, not_false_eq_true,
      Finset.sum_insert] at hf ⊢
    rw [integral_add_vectorMeasure hf.1 (Integrable.finsetSum_vectorMeasure hf.2), ih hf.2]

set_option backward.isDefEq.respectTransparency.types false in
@[integral_simps]
/-
**MeasureTheory.VectorMeasure.integral_neg_vectorMeasure** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.VectorMeasure`。
形式化陈述：integral_neg_vectorMeasure : ∫ᵛ x, f x ∂[B; -μ] = -∫ᵛ x, f x ∂[B; μ]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_cbmApplyMeasure`：dominatedFinMeas
Additive_cbmApplyMeasure (μ : VectorMeasure X F) (B : E ->L[Real] F ->L[Real] G)
 : DominatedFinMeasAdditive μ.variation (μ.t…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.transpose_neg_vectorMeasure`：transpose_neg_v
ectorMeasure (μ : VectorMeasure X F) (B : E ->L[Real] F ->L[Real] G) : (-μ).tran
spose B = - (μ.transpose B)
· 使用定理 `FunLike.coe_neg`：∀ {F : Type u_3} {α : Type u_5} {β : Type u_6} [inst : 
FunLike F α β] [inst_1 : Neg F] [inst_2 : Neg β]   [IsNegApply F α β] (f : F), ⇑
(-f) …
· 使用定理 `MeasureTheory.VectorMeasure.instIsNegApplySet`：∀ {α : Type u_1} {m : Mea
surableSpace α} {M : Type u_3} [inst : AddCommGroup M] [inst_1 : TopologicalSpac
e M]   [inst_2 : IsTopologicalAddGr…
· 使用引理 `MeasureTheory.VectorMeasure.variation_neg`：variation_neg : (-μ).variatio
n = μ.variation
· 使用定理 `MeasureTheory.DominatedFinMeasAdditive.neg`：neg (hT : DominatedFinMeasAd
ditive μ T C) : DominatedFinMeasAdditive μ (-T) C
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.setToFun.congr_simp`：∀ {α : Type u_1} {E : Type u_2} {F : 
Type u_3} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]   [inst_2 : N
ormedAddCommGroup F] [i…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_neg_vectorMeasure :
    ∫ᵛ x, f x ∂[B; -μ] = -∫ᵛ x, f x ∂[B; μ] := by
  simp [integral, ← setToFun_neg', FunLike.coe_neg]
/-
**MeasureTheory.VectorMeasure.integral_sub_vectorMeasure** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.VectorMeasure`。
形式化陈述：integral_sub_vectorMeasure (hμ : μ.Integrable f) (hν : ν.Integrable f) : ∫
ᵛ x, f x ∂[B; μ - ν] = ∫ᵛ x, f x ∂[B; μ] - ∫ᵛ x, f x ∂[B; ν]
参数：hμ : μ.Integrable f；hν : ν.Integrable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `MeasureTheory.VectorMeasure.integral_add_vectorMeasure`：integral_add_vec
torMeasure (hμ : μ.Integrable f) (hν : ν.Integrable f) : ∫ᵛ x, f x ∂[B; μ + ν] =
 ∫ᵛ x, f x ∂[B; μ] + ∫ᵛ x, f x ∂[B; ν]
· 使用定理 `MeasureTheory.VectorMeasure.Integrable.neg_vectorMeasure`：∀ {X : Type u_
2} {E : Type u_4} {F : Type u_5} {mX : MeasurableSpace X} [inst : NormedAddCommG
roup E]   [inst_1 : NormedAddCommGroup F] {f :…
· 使用定理 `MeasureTheory.VectorMeasure.integral_neg_vectorMeasure`：integral_neg_vec
torMeasure : ∫ᵛ x, f x ∂[B; -μ] = -∫ᵛ x, f x ∂[B; μ]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem integral_sub_vectorMeasure (hμ : μ.Integrable f) (hν : ν.Integrable f) :
    ∫ᵛ x, f x ∂[B; μ - ν] = ∫ᵛ x, f x ∂[B; μ] - ∫ᵛ x, f x ∂[B; ν] := by
  rw [sub_eq_add_neg, integral_add_vectorMeasure hμ hν.neg_vectorMeasure,
    integral_neg_vectorMeasure, ← sub_eq_add_neg]

end VectorMeasure

section cbm

variable (f μ) in
@[simp]
/-
**MeasureTheory.integral_zero_cbm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem integral_zero_cbm :
    ∫ᵛ x, f x ∂[(0 : E →L[ℝ] F →L[ℝ] G); μ] = 0 := by
  simp [integral, FunLike.coe_zero]

set_option backward.isDefEq.respectTransparency.types false in
/-
**MeasureTheory.integral_add_cbm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem integral_add_cbm (hB : μ.Integrable f) :
    ∫ᵛ x, f x ∂[B + C; μ] = ∫ᵛ x, f x ∂[B; μ] + ∫ᵛ x, f x ∂[C; μ] := by
  refine setToFun_add_left'' (by simp [transpose]) hB hB ?_
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
  nth_rw 1 [← add_zero μ.variation]
  gcongr
  exact Measure.zero_le μ.variation
/-
**MeasureTheory.integral_finsetSum_cbm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem integral_finsetSum_cbm {B : ι → E →L[ℝ] F →L[ℝ] G}
    {s : Finset ι} (hf : μ.Integrable f) :
    ∫ᵛ x, f x ∂[∑ i ∈ s, B i; μ] = ∑ i ∈ s, ∫ᵛ x, f x ∂[B i; μ] := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [ha, not_false_eq_true, Finset.sum_insert]
    rw [integral_add_cbm hf, ih]

set_option backward.isDefEq.respectTransparency.types false in
@[integral_simps]
/-
**MeasureTheory.integral_neg_cbm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem integral_neg_cbm :
    ∫ᵛ x, f x ∂[-B; μ] = -∫ᵛ x, f x ∂[B; μ] := by
  simp [integral, ← setToFun_neg', FunLike.coe_neg]
/-
**MeasureTheory.integral_sub_cbm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem integral_sub_cbm (hB : μ.Integrable f) :
    ∫ᵛ x, f x ∂[B - C; μ] = ∫ᵛ x, f x ∂[B; μ] - ∫ᵛ x, f x ∂[C; μ] := by
  rw [sub_eq_add_neg, integral_add_cbm hB, integral_neg_cbm, ← sub_eq_add_neg]

end cbm

/-
**MeasureTheory.Integrable.of_integral_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.Integrable`。
形式化陈述：∀ {α : Type u_1} {G : Type u_5} [inst : NormedAddCommGroup G] [inst_1 : No
rmedSpace ℝ G] {m : MeasurableSpace α}   {μ : MeasureTheory.Measure α} {f : α → 
G}, ∫ (a : α), f a ∂μ ≠ 0 → MeasureTheory.Integrable f μ
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Not.imp_symm`：Not.imp_symm : (¬a -> b) -> ¬b -> a
· 使用定理 `MeasureTheory.integral_undef`：integral_undef {f : α -> G} (h : ¬Integrab
le f μ) : ∫ a, f a ∂μ = 0
-/
theorem Integrable.of_integral_ne_zero (h : ∫ᵛ a, f a ∂[B; μ] ≠ 0) : μ.Integrable f :=
  Not.imp_symm integral_undef h
/-
**MeasureTheory.integral_non_aestronglyMeasurable** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：integral_non_aestronglyMeasurable {f : α -> G} (h : ¬AEStronglyMeasurable 
f μ) : ∫ a, f a ∂μ = 0
参数：h : ¬AEStronglyMeasurable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_undef`：integral_undef {f : α -> G} (h : ¬Integrab
le f μ) : ∫ a, f a ∂μ = 0
· 使用定理 `not_and_of_not_left`：∀ {a : Prop} (b : Prop), ¬a → ¬(a ∧ b)
-/
theorem integral_non_aestronglyMeasurable {f : X → E}
    (h : ¬AEStronglyMeasurable f μ.variation) :
    ∫ᵛ a, f a ∂[B; μ] = 0 :=
  integral_undef <| not_and_of_not_left _ h
/-
**MeasureTheory.integral_indicator** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_indicator (hs : MeasurableSet s) : ∫ x, indicator s f x ∂μ = ∫ x 
in s, f x ∂μ
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_add_compl`：integral_add_compl (hs : MeasurableSet
 s) (hfi : Integrable f μ) : ∫ x in s, f x ∂μ + ∫ x in sᶜ, f x ∂μ = ∫ x, f x ∂μ
· 使用定理 `MeasureTheory.IntegrableOn.integrable_indicator`：∀ {α : Type u_1} {ε' : 
Type u_4} {mα : MeasurableSpace α} {s : Set α} {μ : MeasureTheory.Measure α}   [
inst : TopologicalSpace ε'] [inst_1 :…
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `indicator_ae_eq_restrict`：indicator_ae_eq_restrict (hs : MeasurableSet s
) : indicator s f =ᵐ[μ.restrict s] f
· 使用定理 `indicator_ae_eq_restrict_compl`：indicator_ae_eq_restrict_compl (hs : Mea
surableSet s) : indicator s f =ᵐ[μ.restrict sᶜ] 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_zero`：integral_zero : ∫ _ : α, (0 : G) ∂μ = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.integral_undef`：integral_undef {f : α -> G} (h : ¬Integrab
le f μ) : ∫ a, f a ∂μ = 0
· 使用定理 `MeasureTheory.integrable_indicator_iff`：integrable_indicator_iff (hs : M
easurableSet s) : Integrable (indicator s f) μ ↔ IntegrableOn f s μ
-/
lemma integral_indicator₂ {β : Type*} (f : β → X → E) (s : Set β) (b : β) :
    ∫ᵛ y, s.indicator (f · y) b ∂[B; μ] = s.indicator (fun x ↦ ∫ᵛ y, f x y ∂[B; μ]) b := by
  by_cases hb : b ∈ s <;> simp [hb]

@[fun_prop]
/-
**MeasureTheory.continuous_integral** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：continuous_integral : Continuous fun f : α ->₁[μ] G => ∫ a, f a ∂μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_weightedSMul`：dominatedFinMeasAdd
itive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) : DominatedFinMeasAdd
itive μ (weightedSMul μ : Set α -> F ->L[…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_eq_setToFun`：integral_eq_setToFun (f : α -> E) : 
∫ a, f a ∂μ = setToFun μ (weightedSMul μ) (dominatedFinMeasAdditive_weightedSMul
 μ) f
· 使用定理 `MeasureTheory.continuous_setToFun`：continuous_setToFun (hT : DominatedFi
nMeasAdditive μ T C) : Continuous fun f : α ->₁[μ] E => setToFun μ T hT f
-/
theorem continuous_integral : Continuous fun f : X →₁[μ.variation] E => ∫ᵛ a, f a ∂[B; μ] := by
  simp only [integral_eq_setToFun]
  exact continuous_setToFun _
/-
**MeasureTheory.norm_integral_le_lintegral_norm** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：norm_integral_le_lintegral_norm (f : α -> G) : ‖∫ a, f a ∂μ‖ <= ENNReal.to
Real (∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ)
参数：f : α -> G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_weightedSMul`：dominatedFinMeasAdd
itive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) : DominatedFinMeasAdd
itive μ (weightedSMul μ : Set α -> F ->L[…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_eq_setToFun`：integral_eq_setToFun (f : α -> E) : 
∫ a, f a ∂μ = setToFun μ (weightedSMul μ) (dominatedFinMeasAdditive_weightedSMul
 μ) f
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.norm_setToFun_le_toReal`：norm_setToFun_le_toReal (hT : Dom
inatedFinMeasAdditive μ T C) (hC : 0 <= C) : ‖setToFun μ T hT f‖ <= NNReal.mk C 
hC * ENNReal.toReal (∫⁻ a, …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ofReal_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (x : E), ENN
Real.ofReal ‖x‖ = ‖x‖ₑ
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem norm_integral_le_lintegral_norm :
    ‖∫ᵛ a, f a ∂[B; μ]‖ ≤ ‖B‖ * ENNReal.toReal (∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ.variation) :=
  (norm_setToFun_le_toReal _ (by simp)).trans (by simp)
/-
**MeasureTheory.norm_integral_le_integral_norm** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：norm_integral_le_integral_norm (f : α -> G) : ‖∫ a, f a ∂μ‖ <= ∫ a, ‖f a‖ 
∂μ
参数：f : α -> G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `MeasureTheory.norm_integral_le_lintegral_norm`：norm_integral_le_lintegra
l_norm (f : α -> G) : ‖∫ a, f a ∂μ‖ <= ENNReal.toReal (∫⁻ a, ENNReal.ofReal ‖f a
‖ ∂μ)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_eq_lintegral_of_nonneg_ae`：integral_eq_lintegral_
of_nonneg_ae {f : α -> Real} (hf : 0 <=ᵐ[μ] f) (hfm : AEStronglyMeasurable f μ) 
: ∫ a, f a ∂μ = ENNReal.toReal (∫⁻ a, …
· 使用定理 `MeasureTheory.AEStronglyMeasurable.norm`：∀ {α : Type u_1} {m₀ : Measurab
leSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : SeminormedAddCom
mGroup β]   {f : α → β}, Meas…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_non_aestronglyMeasurable`：integral_non_aestrongly
Measurable {f : α -> G} (h : ¬AEStronglyMeasurable f μ) : ∫ a, f a ∂μ = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用引理 `MeasureTheory.integral_nonneg_of_ae`：integral_nonneg_of_ae {f : α -> E} 
(hf : 0 <=ᵐ[μ] f) : 0 <= ∫ x, f x ∂μ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
-/
theorem norm_integral_le_integral_norm :
    ‖∫ᵛ a, f a ∂[B; μ]‖ ≤ ‖B‖ * ∫ a, ‖f a‖ ∂μ.variation := by
  have le_ae : ∀ᵐ a ∂μ.variation, 0 ≤ ‖f a‖ :=
    Eventually.of_forall fun a => norm_nonneg _
  by_cases h : AEStronglyMeasurable f μ.variation
  · calc ‖∫ᵛ a, f a ∂[B; μ]‖
    _ ≤ ‖B‖ * ENNReal.toReal (∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ.variation) :=
      norm_integral_le_lintegral_norm
    _ = ‖B‖ * ∫ a, ‖f a‖ ∂μ.variation := by
      rw [integral_eq_lintegral_of_nonneg_ae le_ae <| h.norm]
  · rw [integral_non_aestronglyMeasurable h, norm_zero]
    positivity
/-
**MeasureTheory.enorm_integral_le_lintegral_enorm** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：enorm_integral_le_lintegral_enorm (f : α -> G) : ‖∫ a, f a ∂μ‖ₑ <= ∫⁻ a, ‖
f a‖ₑ ∂μ
参数：f : α -> G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_weightedSMul`：dominatedFinMeasAdd
itive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) : DominatedFinMeasAdd
itive μ (weightedSMul μ : Set α -> F ->L[…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_eq_setToFun`：integral_eq_setToFun (f : α -> E) : 
∫ a, f a ∂μ = setToFun μ (weightedSMul μ) (dominatedFinMeasAdditive_weightedSMul
 μ) f
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.enorm_setToFun_le`：enorm_setToFun_le (hT : DominatedFinMea
sAdditive μ T C) (hC : 0 <= C) : ‖setToFun μ T hT f‖ₑ <= NNReal.mk C hC * ∫⁻ x, 
‖f x‖ₑ ∂μ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem enorm_integral_le_lintegral_enorm :
    ‖∫ᵛ a, f a ∂[B; μ]‖ₑ ≤ ‖B‖ₑ * ∫⁻ a, ‖f a‖ₑ ∂μ.variation := by
  apply (enorm_setToFun_le _ (by simp)).trans
  gcongr
  simp [← coe_nnnorm]
/-
**MeasureTheory.enorm_integral_le_lintegral_enorm_transpose** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem enorm_integral_le_lintegral_enorm_transpose :
    ‖∫ᵛ a, f a ∂[B; μ]‖ₑ ≤ ∫⁻ a, ‖f a‖ₑ ∂(μ.transpose B).variation := by
  by_cases hf : μ.Integrable f
  · rw [integral_eq_setToFun_transpose hf]
    apply (enorm_setToFun_le _ (by simp)).trans (by simp)
  · simp [integral_undef hf]
/-
**MeasureTheory.dist_integral_le_lintegral_edist** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：dist_integral_le_lintegral_edist {f g : α -> G} (hf : Integrable f μ) (hg 
: Integrable g μ) : dist (∫ a, f a ∂μ) (∫ a, g a ∂μ) <= (∫⁻ a, edist (f a) (g a)
 ∂μ).toReal
参数：hf : Integrable f μ；hg : Integrable g μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_sub`：integral_sub {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a - g a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `MeasureTheory.norm_integral_le_lintegral_norm`：norm_integral_le_lintegra
l_norm (f : α -> G) : ‖∫ a, f a ∂μ‖ <= ENNReal.toReal (∫⁻ a, ENNReal.ofReal ‖f a
‖ ∂μ)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ofReal_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (x : E), ENN
Real.ofReal ‖x‖ = ‖x‖ₑ
· 使用定理 `edist_eq_enorm_sub`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (
a b : E), edist a b = ‖a - b‖ₑ
-/
theorem dist_integral_le_lintegral_edist (hf : μ.Integrable f) (hg : μ.Integrable g) :
    dist (∫ᵛ a, f a ∂[B; μ]) (∫ᵛ a, g a ∂[B; μ]) ≤
      ‖B‖ * (∫⁻ a, edist (f a) (g a) ∂μ.variation).toReal := by
  grw [dist_eq_norm, ← integral_sub hf hg, norm_integral_le_lintegral_norm]
  simp [edist_eq_enorm_sub]
/-
**MeasureTheory.edist_integral_le_lintegral_edist** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：edist_integral_le_lintegral_edist {f g : α -> G} (hf : Integrable f μ) (hg
 : Integrable g μ) : edist (∫ a, f a ∂μ) (∫ a, g a ∂μ) <= ∫⁻ a, edist (f a) (g a
) ∂μ
参数：hf : Integrable f μ；hg : Integrable g μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `edist_dist`：edist_dist (x y : α) : edist x y = ENNReal.ofReal (dist x y)
· 使用定理 `ENNReal.ofReal_le_of_le_toReal`：ofReal_le_of_le_toReal {a : Real} {b : R
eal>=0∞} (h : a <= ENNReal.toReal b) : ENNReal.ofReal a <= b
· 使用定理 `MeasureTheory.dist_integral_le_lintegral_edist`：dist_integral_le_lintegr
al_edist {f g : α -> G} (hf : Integrable f μ) (hg : Integrable g μ) : dist (∫ a,
 f a ∂μ) (∫ a, g a ∂μ) <= (∫⁻ a, edi…
-/
theorem edist_integral_le_lintegral_edist (hf : μ.Integrable f) (hg : μ.Integrable g) :
    edist (∫ᵛ a, f a ∂[B; μ]) (∫ᵛ a, g a ∂[B; μ]) ≤
      ‖B‖ₑ * ∫⁻ a, edist (f a) (g a) ∂μ.variation := by
  rw [edist_dist]
  apply ENNReal.ofReal_le_of_le_toReal
  grw [dist_integral_le_lintegral_edist hf hg, ENNReal.toReal_mul, toReal_enorm]
/-
**MeasureTheory.frequently_ae_ne_zero_of_integral_ne_zero** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory`。
形式化陈述：frequently_ae_ne_zero_of_integral_ne_zero {f : α -> G} (h : ∫ a, f a ∂μ !=
 0) : existsᶠ a in ae μ, f a != 0
参数：h : ∫ a, f a ∂μ != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.integral_eq_zero_of_ae`：integral_eq_zero_of_ae {f : α -> G
} (hf : f =ᵐ[μ] 0) : ∫ a, f a ∂μ = 0
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
-/
theorem frequently_ae_ne_zero_of_integral_ne_zero
    (h : ∫ᵛ a, f a ∂[B; μ] ≠ 0) : ∃ᶠ a in ae μ.variation, f a ≠ 0 :=
  fun h' ↦ h (integral_eq_zero_of_ae (h'.mono fun _ ↦ not_not.mp))
/-
**MeasureTheory.exists_ne_zero_of_integral_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory`。
形式化陈述：exists_ne_zero_of_integral_ne_zero {f : α -> G} (h : ∫ a, f a ∂μ != 0) : e
xists a, f a != 0
参数：h : ∫ a, f a ∂μ != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Frequently.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.frequently_ae_ne_zero_of_integral_ne_zero`：frequently_ae_n
e_zero_of_integral_ne_zero {f : α -> G} (h : ∫ a, f a ∂μ != 0) : existsᶠ a in ae
 μ, f a != 0
-/
theorem exists_ne_zero_of_integral_ne_zero
    (h : ∫ᵛ a, f a ∂[B; μ] ≠ 0) : ∃ a, f a ≠ 0 :=
  (frequently_ae_ne_zero_of_integral_ne_zero h).exists
/-
**MeasureTheory.integral_toSignedMeasure** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheor
y`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma integral_toSignedMeasure {μ : Measure X} [IsFiniteMeasure μ] {f : X → G} :
    ∫ᵛ x, f x ∂<•μ.toSignedMeasure = ∫ x, f x ∂μ := by
  rcases subsingleton_or_nontrivial G with h'G | h'G
  · apply Subsingleton.elim
  rw [integral_eq_setToFun, MeasureTheory.integral_eq_setToFun]
  simp only [Measure.variation_toSignedMeasure]
  apply setToFun_congr_left' _ _ (fun s hs h's ↦ ?_)
  simp only [transpose, ContinuousLinearMap.flip_flip, mapRange_apply,
    Measure.toSignedMeasure_apply_measurable hs, LinearMap.toAddMonoidHom_coe,
    ContinuousLinearMap.coe_coe, weightedSMul]
  rfl

@[simp]
/-
**MeasureTheory.integral_dirac'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_dirac' [MeasurableSpace α] (f : α -> E) (a : α) (hfm : StronglyMe
asurable f) : ∫ x, f x ∂Measure.dirac a = f a
参数：f : α -> E；a : α；hfm : StronglyMeasurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.ae_eq_dirac'`：ae_eq_dirac' [MeasurableSingletonClass β] {a
 : α} {f : α -> β} (hf : Measurable f) : f =ᵐ[dirac a] const α (f a)
· 使用定理 `OpensMeasurableSpace.toMeasurableSingletonClass`：∀ {α : Type u_1} [inst 
: TopologicalSpace α] [inst_1 : MeasurableSpace α] [OpensMeasurableSpace α] [T1S
pace α],   MeasurableSingletonClass α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_const`：integral_const (c : E) : ∫ _ : α, c ∂μ = μ
.real univ • c
· 使用定理 `MeasureTheory.probReal_univ`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {
μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ],   μ.real Se
t.univ = 1
· 使用定理 `MeasureTheory.Measure.dirac.isProbabilityMeasure`：∀ {α : Type u_1} [inst
 : MeasurableSpace α] {x : α}, MeasureTheory.IsProbabilityMeasure (MeasureTheory
.Measure.dirac x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_dirac' [MeasurableSpace X] [CompleteSpace G] {a : X} {v : F}
    (hfm : StronglyMeasurable f) :
    ∫ᵛ x, f x ∂[B; VectorMeasure.dirac a v] = B (f a) v := by
  borelize E
  have : IsFiniteMeasure ((dirac a v).transpose B).variation := by
    have : ‖B.flip v‖ₑ • Measure.dirac a = ‖B.flip v‖₊ • Measure.dirac a := rfl
    simp only [transpose_dirac, variation_dirac, this]
    infer_instance
  calc
    ∫ᵛ x, f x ∂[B; VectorMeasure.dirac a v] = ∫ᵛ _, f a ∂[B; VectorMeasure.dirac a v] := by
      apply integral_congr_ae
      simp only [variation_dirac]
      exact Measure.ae_smul_measure (ae_eq_dirac' hfm.measurable) _
    _ = B (f a) v := by simp

@[simp]
/-
**MeasureTheory.integral_dirac** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_dirac [MeasurableSpace α] [MeasurableSingletonClass α] (f : α -> 
E) (a : α) : ∫ x, f x ∂Measure.dirac a = f a
参数：f : α -> E；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.ae_eq_dirac`：ae_eq_dirac [MeasurableSingletonClass α] {a :
 α} (f : α -> δ) : f =ᵐ[dirac a] const α (f a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_const`：integral_const (c : E) : ∫ _ : α, c ∂μ = μ
.real univ • c
· 使用定理 `MeasureTheory.probReal_univ`：∀ {α : Type u_1} {m0 : MeasurableSpace α} {
μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ],   μ.real Se
t.univ = 1
· 使用定理 `MeasureTheory.Measure.dirac.isProbabilityMeasure`：∀ {α : Type u_1} [inst
 : MeasurableSpace α] {x : α}, MeasureTheory.IsProbabilityMeasure (MeasureTheory
.Measure.dirac x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_dirac [MeasurableSpace X] [MeasurableSingletonClass X] [CompleteSpace G]
    {a : X} {v : F} :
    ∫ᵛ x, f x ∂[B; VectorMeasure.dirac a v] = B (f a) v := by
  have : IsFiniteMeasure ((dirac a v).transpose B).variation := by
    have : ‖B.flip v‖ₑ • Measure.dirac a = ‖B.flip v‖₊ • Measure.dirac a := rfl
    simp only [transpose_dirac, variation_dirac, this]
    infer_instance
  calc
    ∫ᵛ x, f x ∂[B; VectorMeasure.dirac a v] = ∫ᵛ _, f a ∂[B; VectorMeasure.dirac a v] := by
      apply integral_congr_ae
      simp only [variation_dirac]
      exact Measure.ae_smul_measure (ae_eq_dirac f) _
    _ = B (f a) v := by simp
/-
**MeasureTheory.integral_unique** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_unique [Unique α] (f : α -> E) : ∫ x, f x ∂μ = μ.real univ • f de
fault
参数：f : α -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Unique.uniq`：∀ {α : Sort u} (self : Unique α) (a : α), a = default
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_const`：integral_const (c : E) : ∫ _ : α, c ∂μ = μ
.real univ • c
-/
theorem integral_unique [Unique X] [CompleteSpace G] :
    ∫ᵛ x, f x ∂[B; μ] = B (f default) (μ univ) :=
  calc
    ∫ᵛ x, f x ∂[B; μ] = ∫ᵛ _, f default ∂[B; μ] := by congr with x; congr; exact Unique.uniq _ x
    _ = B (f default) (μ univ) := by rw [integral_const]

/-- If `F i → f` in `L1`, then `∫ᵛ x, F i x ∂[B; μ] → ∫ᵛ x, f x ∂[B; μ]`. -/
/-
**MeasureTheory.tendsto_integral_of_L1** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：tendsto_integral_of_L1 {ι} (f : α -> G) (hfi : AEStronglyMeasurable f μ) {
F : ι -> α -> G} {l : Filter ι} (hFi : forallᶠ i in l, Integrable (F i) μ) (hF :
 Tendsto (fun i => ∫⁻ x, ‖F i x - f x‖ₑ ∂μ) l (𝓝 0)) : Tendsto (fun i => ∫ x, F 
i x ∂μ) l (𝓝 <| ∫ x, f x ∂μ)
参数：f : α -> G；hfi : AEStronglyMeasurable f μ；hFi : forallᶠ i in l, Integrable (F
 i) μ；hF : Tendsto (fun i => ∫⁻ x, ‖F i x - f x‖ₑ ∂μ) l (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_weightedSMul`：dominatedFinMeasAdd
itive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) : DominatedFinMeasAdd
itive μ (weightedSMul μ : Set α -> F ->L[…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_eq_setToFun`：integral_eq_setToFun (f : α -> E) : 
∫ a, f a ∂μ = setToFun μ (weightedSMul μ) (dominatedFinMeasAdditive_weightedSMul
 μ) f
· 使用定理 `MeasureTheory.tendsto_setToFun_of_L1`：tendsto_setToFun_of_L1 (hT : Domin
atedFinMeasAdditive μ T C) {ι} (f : α -> E) (hf : AEStronglyMeasurable f μ) {fs 
: ι -> α -> E} {l : Filter…

--- 原说明 ---
If `F i → f` in `L1`, then `∫ᵛ x, F i x ∂[B; μ] → ∫ᵛ x, f x ∂[B; μ]`.
-/
theorem tendsto_integral_of_L1 {ι} (f : X → E)
    (hfi : AEStronglyMeasurable f μ.variation) {F : ι → X → E}
    {l : Filter ι} (hFi : ∀ᶠ i in l, μ.Integrable (F i))
    (hF : Tendsto (fun i ↦ ∫⁻ x, ‖F i x - f x‖ₑ ∂μ.variation) l (𝓝 0)) :
    Tendsto (fun i ↦ ∫ᵛ x, F i x ∂[B; μ]) l (𝓝 <| ∫ᵛ x, f x ∂[B; μ]) :=
  tendsto_setToFun_of_L1 _ f hfi hFi hF

/-- If `F i → f` in `L1`, then `∫ᵛ x, F i x ∂[B; μ] → ∫ᵛ x, f x ∂[B; μ]`. -/
/-
**MeasureTheory.tendsto_integral_of_L1'** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory
`。
形式化陈述：tendsto_integral_of_L1' {ι} (f : α -> G) (hfi : AEStronglyMeasurable f μ) 
{F : ι -> α -> G} {l : Filter ι} (hFi : forallᶠ i in l, Integrable (F i) μ) (hF 
: Tendsto (fun i => eLpNorm (F i - f) 1 μ) l (𝓝 0)) : Tendsto (fun i => ∫ x, F i
 x ∂μ) l (𝓝 (∫ x, f x ∂μ))
参数：f : α -> G；hfi : AEStronglyMeasurable f μ；hFi : forallᶠ i in l, Integrable (F
 i) μ；hF : Tendsto (fun i => eLpNorm (F i - f) 1 μ) l (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.tendsto_integral_of_L1`：tendsto_integral_of_L1 {ι} (f : α 
-> G) (hfi : AEStronglyMeasurable f μ) {F : ι -> α -> G} {l : Filter ι} (hFi : f
orallᶠ i in l, Integrable …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.eLpNorm_one_eq_lintegral_enorm`：eLpNorm_one_eq_lintegral_e
norm {f : α -> ε} : eLpNorm f 1 μ = ∫⁻ x, ‖f x‖ₑ ∂μ

--- 原说明 ---
If `F i → f` in `L1`, then `∫ᵛ x, F i x ∂[B; μ] → ∫ᵛ x, f x ∂[B; μ]`.
-/
lemma tendsto_integral_of_L1' {ι} (f : X → E)
    (hfi : AEStronglyMeasurable f μ.variation) {F : ι → X → E}
    {l : Filter ι} (hFi : ∀ᶠ i in l, μ.Integrable (F i))
    (hF : Tendsto (fun i ↦ eLpNorm (F i - f) 1 μ.variation) l (𝓝 0)) :
    Tendsto (fun i ↦ ∫ᵛ x, F i x ∂[B; μ]) l (𝓝 (∫ᵛ x, f x ∂[B; μ])) := by
  refine tendsto_integral_of_L1 f hfi hFi ?_
  simp_rw [eLpNorm_one_eq_lintegral_enorm, Pi.sub_apply] at hF
  exact hF

variable {Y : Type*} [TopologicalSpace Y] [FirstCountableTopology Y]
/-
**MeasureTheory.continuousWithinAt_of_dominated** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：continuousWithinAt_of_dominated {F : X -> α -> G} {x₀ : X} {bound : α -> R
eal} {s : Set X} (hF_meas : forallᶠ x in 𝓝[s] x₀, AEStronglyMeasurable (F x) μ) 
(h_bound : forallᶠ x in 𝓝[s] x₀, forallᵐ a ∂μ, ‖F x a‖ <= bound a) (bound_integr
able : Integrable bound μ) (h_cont : forallᵐ a ∂μ, ContinuousWithinAt (fun x => 
F x a) s x₀) : ContinuousWithinAt (fun x => ∫ a, F x a ∂μ) s x₀
参数：hF_meas : forallᶠ x in 𝓝[s] x₀, AEStronglyMeasurable (F x) μ；h_bound : forall
ᶠ x in 𝓝[s] x₀, forallᵐ a ∂μ, ‖F x a‖ <= bound a；bound_integrable : Integrable b
ound μ；h_cont : forallᵐ a ∂μ, ContinuousWithinAt (fun x => F x a) s x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_weightedSMul`：dominatedFinMeasAdd
itive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) : DominatedFinMeasAdd
itive μ (weightedSMul μ : Set α -> F ->L[…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_eq_setToFun`：integral_eq_setToFun (f : α -> E) : 
∫ a, f a ∂μ = setToFun μ (weightedSMul μ) (dominatedFinMeasAdditive_weightedSMul
 μ) f
· 使用定理 `MeasureTheory.continuousWithinAt_setToFun_of_dominated`：continuousWithin
At_setToFun_of_dominated (hT : DominatedFinMeasAdditive μ T C) {fs : X -> α -> E
} {x₀ : X} {bound : α -> Real} {s : Set X} (…
-/
theorem continuousWithinAt_of_dominated {F : Y → X → E} {x₀ : Y} {bound : X → ℝ} {s : Set Y}
    (hF_meas : ∀ᶠ x in 𝓝[s] x₀, AEStronglyMeasurable (F x) μ.variation)
    (h_bound : ∀ᶠ x in 𝓝[s] x₀, ∀ᵐ a ∂μ.variation, ‖F x a‖ ≤ bound a)
    (bound_integrable : Integrable bound μ.variation)
    (h_cont : ∀ᵐ a ∂μ.variation, ContinuousWithinAt (fun x ↦ F x a) s x₀) :
    ContinuousWithinAt (fun x ↦ ∫ᵛ a, F x a ∂[B; μ]) s x₀ :=
  continuousWithinAt_setToFun_of_dominated _ hF_meas h_bound bound_integrable h_cont
/-
**MeasureTheory.continuousAt_of_dominated** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：continuousAt_of_dominated {F : X -> α -> G} {x₀ : X} {bound : α -> Real} (
hF_meas : forallᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) μ) (h_bound : forallᶠ x 
in 𝓝 x₀, forallᵐ a ∂μ, ‖F x a‖ <= bound a) (bound_integrable : Integrable bound 
μ) (h_cont : forallᵐ a ∂μ, ContinuousAt (fun x => F x a) x₀) : ContinuousAt (fun
 x => ∫ a, F x a ∂μ) x₀
参数：hF_meas : forallᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) μ；h_bound : forallᶠ x
 in 𝓝 x₀, forallᵐ a ∂μ, ‖F x a‖ <= bound a；bound_integrable : Integrable bound μ
；h_cont : forallᵐ a ∂μ, ContinuousAt (fun x => F x a) x₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_weightedSMul`：dominatedFinMeasAdd
itive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) : DominatedFinMeasAdd
itive μ (weightedSMul μ : Set α -> F ->L[…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_eq_setToFun`：integral_eq_setToFun (f : α -> E) : 
∫ a, f a ∂μ = setToFun μ (weightedSMul μ) (dominatedFinMeasAdditive_weightedSMul
 μ) f
· 使用定理 `MeasureTheory.continuousAt_setToFun_of_dominated`：continuousAt_setToFun_
of_dominated (hT : DominatedFinMeasAdditive μ T C) {fs : X -> α -> E} {x₀ : X} {
bound : α -> Real} (hfs_meas : forallᶠ…
-/
theorem continuousAt_of_dominated {F : Y → X → E} {x₀ : Y} {bound : X → ℝ}
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) μ.variation)
    (h_bound : ∀ᶠ x in 𝓝 x₀, ∀ᵐ a ∂μ.variation, ‖F x a‖ ≤ bound a)
    (bound_integrable : Integrable bound μ.variation)
    (h_cont : ∀ᵐ a ∂μ.variation, ContinuousAt (fun x ↦ F x a) x₀) :
    ContinuousAt (fun x ↦ ∫ᵛ a, F x a ∂[B; μ]) x₀ :=
  continuousAt_setToFun_of_dominated _ hF_meas h_bound bound_integrable h_cont
/-
**MeasureTheory.continuousOn_of_dominated** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：continuousOn_of_dominated {F : X -> α -> G} {bound : α -> Real} {s : Set X
} (hF_meas : forall x in s, AEStronglyMeasurable (F x) μ) (h_bound : forall x in
 s, forallᵐ a ∂μ, ‖F x a‖ <= bound a) (bound_integrable : Integrable bound μ) (h
_cont : forallᵐ a ∂μ, ContinuousOn (fun x => F x a) s) : ContinuousOn (fun x => 
∫ a, F x a ∂μ) s
参数：hF_meas : forall x in s, AEStronglyMeasurable (F x) μ；h_bound : forall x in s
, forallᵐ a ∂μ, ‖F x a‖ <= bound a；bound_integrable : Integrable bound μ；h_cont 
: forallᵐ a ∂μ, ContinuousOn (fun x => F x a) s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_weightedSMul`：dominatedFinMeasAdd
itive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) : DominatedFinMeasAdd
itive μ (weightedSMul μ : Set α -> F ->L[…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_eq_setToFun`：integral_eq_setToFun (f : α -> E) : 
∫ a, f a ∂μ = setToFun μ (weightedSMul μ) (dominatedFinMeasAdditive_weightedSMul
 μ) f
· 使用定理 `MeasureTheory.continuousOn_setToFun_of_dominated`：continuousOn_setToFun_
of_dominated (hT : DominatedFinMeasAdditive μ T C) {fs : X -> α -> E} {bound : α
 -> Real} {s : Set X} (hfs_meas : fora…
-/
theorem continuousOn_of_dominated {F : Y → X → E} {bound : X → ℝ} {s : Set Y}
    (hF_meas : ∀ x ∈ s, AEStronglyMeasurable (F x) μ.variation)
    (h_bound : ∀ x ∈ s, ∀ᵐ a ∂μ.variation, ‖F x a‖ ≤ bound a)
    (bound_integrable : Integrable bound μ.variation)
    (h_cont : ∀ᵐ a ∂μ.variation, ContinuousOn (fun x ↦ F x a) s) :
    ContinuousOn (fun x ↦ ∫ᵛ a, F x a ∂[B; μ]) s :=
  continuousOn_setToFun_of_dominated _ hF_meas h_bound bound_integrable h_cont
/-
**MeasureTheory.continuous_of_dominated** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：continuous_of_dominated {F : X -> α -> G} {bound : α -> Real} (hF_meas : f
orall x, AEStronglyMeasurable (F x) μ) (h_bound : forall x, forallᵐ a ∂μ, ‖F x a
‖ <= bound a) (bound_integrable : Integrable bound μ) (h_cont : forallᵐ a ∂μ, Co
ntinuous fun x => F x a) : Continuous fun x => ∫ a, F x a ∂μ
参数：hF_meas : forall x, AEStronglyMeasurable (F x) μ；h_bound : forall x, forallᵐ 
a ∂μ, ‖F x a‖ <= bound a；bound_integrable : Integrable bound μ；h_cont : forallᵐ 
a ∂μ, Continuous fun x => F x a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_weightedSMul`：dominatedFinMeasAdd
itive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) : DominatedFinMeasAdd
itive μ (weightedSMul μ : Set α -> F ->L[…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_eq_setToFun`：integral_eq_setToFun (f : α -> E) : 
∫ a, f a ∂μ = setToFun μ (weightedSMul μ) (dominatedFinMeasAdditive_weightedSMul
 μ) f
· 使用定理 `MeasureTheory.continuous_setToFun_of_dominated`：continuous_setToFun_of_d
ominated (hT : DominatedFinMeasAdditive μ T C) {fs : X -> α -> E} {bound : α -> 
Real} (hfs_meas : forall x, AEStrong…
-/
theorem continuous_of_dominated {F : Y → X → E} {bound : X → ℝ}
    (hF_meas : ∀ x, AEStronglyMeasurable (F x) μ.variation)
    (h_bound : ∀ x, ∀ᵐ a ∂μ.variation, ‖F x a‖ ≤ bound a)
    (bound_integrable : Integrable bound μ.variation)
    (h_cont : ∀ᵐ a ∂μ.variation, Continuous fun x ↦ F x a) :
    Continuous fun x ↦ ∫ᵛ a, F x a ∂[B; μ] :=
  continuous_setToFun_of_dominated _ hF_meas h_bound bound_integrable h_cont
/-
**MeasureTheory.norm_integral_le_of_norm_le_const** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：norm_integral_le_of_norm_le_const [IsFiniteMeasure μ] {f : α -> G} {C : Re
al} (h : forallᵐ x ∂μ, ‖f x‖ <= C) : ‖∫ x, f x ∂μ‖ <= C * μ.real univ
参数：h : forallᵐ x ∂μ, ‖f x‖ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.norm_integral_le_of_norm_le`：norm_integral_le_of_norm_le {
f : α -> G} {g : α -> Real} (hg : Integrable g μ) (h : forallᵐ x ∂μ, ‖f x‖ <= g 
x) : ‖∫ x, f x ∂μ‖ <= ∫ x, g x …
· 使用定理 `MeasureTheory.integrable_const`：integrable_const [IsFiniteMeasure μ] (c 
: β) : Integrable (fun _ : α => c) μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_const`：integral_const (c : E) : ∫ _ : α, c ∂μ = μ
.real univ • c
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem norm_integral_le_of_norm_le_const [IsFiniteMeasure μ.variation]
    {C : ℝ} (h : ∀ᵐ x ∂μ.variation, ‖f x‖ ≤ C) :
    ‖∫ᵛ x, f x ∂[B; μ]‖ ≤ C * ‖B‖ * μ.variation.real univ := calc
  ‖∫ᵛ x, f x ∂[B; μ]‖
  _ ≤ ‖B‖ * (∫⁻ a, ENNReal.ofReal ‖f a‖ ∂μ.variation).toReal :=
    norm_integral_le_lintegral_norm
  _ ≤ ‖B‖ * (∫⁻ a, ENNReal.ofReal C ∂μ.variation).toReal := by
    gcongr 1
    apply ENNReal.toReal_mono
    · simp only [lintegral_const, ne_eq]
      finiteness
    · apply lintegral_mono_ae
      filter_upwards [h] with x hx using ENNReal.ofReal_mono hx
  _ = ‖B‖ * (C * μ.variation.real univ) := by
    by_cases hμ : μ.variation = 0
    · simp [hμ]
    have : (ae μ.variation).NeBot := ae_neBot.mpr hμ
    have hC : 0 ≤ C := by
      obtain ⟨x, hx⟩ := h.exists
      exact (norm_nonneg _).trans hx
    simp [ENNReal.toReal_ofReal hC, Measure.real]
  _ = C * ‖B‖ * μ.variation.real univ := by ring
/-
**MeasureTheory.enorm_integral_le_of_enorm_le_const** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem enorm_integral_le_of_enorm_le_const
    {C : ℝ≥0∞} (h : ∀ᵐ x ∂μ.variation, ‖f x‖ₑ ≤ C) :
    ‖∫ᵛ x, f x ∂[B; μ]‖ₑ ≤ C * ‖B‖ₑ * μ.variation univ := by
  apply enorm_integral_le_lintegral_enorm.trans
  rw [mul_comm C, mul_assoc]
  gcongr
  exact (lintegral_mono_ae h).trans (by simp)
/-
**MeasureTheory.nndist_integral_add_vectorMeasure_le_lintegral** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nndist_integral_add_vectorMeasure_le_lintegral
    (h₁ : μ.Integrable f) (h₂ : ν.Integrable f) :
    (nndist (∫ᵛ x, f x ∂[B; μ]) (∫ᵛ x, f x ∂[B; (μ + ν)]) : ℝ≥0∞) ≤
      ‖B‖ₑ * ∫⁻ x, ‖f x‖ₑ ∂ν.variation := by
  rw [integral_add_vectorMeasure h₁ h₂, nndist_comm, nndist_eq_nnnorm, add_sub_cancel_left]
  exact enorm_integral_le_lintegral_enorm

variable {β : Type*} [MeasurableSpace β] {φ : X → β} {a : X} {v : F}
/-
**MeasureTheory.variation_transpose_map_le** 是 Mathlib 中的一个引理，位于命名空间 `MeasureThe
ory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma variation_transpose_map_le :
    ((μ.map φ).transpose B).variation ≤ Measure.map φ (μ.transpose B).variation := by
  grw [transpose_map, variation_map_le]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-
**MeasureTheory.Integrable.map** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Integrable.map {β : Type*} [MeasurableSpace β] {φ : X → β}
    {f : β → E} (hfm : AEStronglyMeasurable f (μ.variation.map φ))
    (h : μ.Integrable (f ∘ φ)) : (μ.map φ).Integrable f := by
  by_cases hφ : Measurable φ; swap
  · simp [VectorMeasure.map, hφ]
  simp_rw [VectorMeasure.Integrable] at h ⊢
  apply ((integrable_map_measure hfm hφ.aemeasurable).2 h).mono_measure
  apply variation_map_le

set_option backward.isDefEq.respectTransparency.types false in
/-
**MeasureTheory.integral_map** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_map {β} [MeasurableSpace β] {φ : α -> β} (hφ : AEMeasurable φ μ) 
{f : β -> G} (hfm : AEStronglyMeasurable f (Measure.map φ μ)) : ∫ y, f y ∂Measur
e.map φ μ = ∫ x, f (φ x) ∂μ
参数：hφ : AEMeasurable φ μ；hfm : AEStronglyMeasurable f (Measure.map φ μ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
· 使用定理 `MeasureTheory.Measure.map_congr`：map_congr {f g : α -> β} (h : f =ᵐ[μ] g
) : Measure.map f μ = Measure.map g μ
· 使用定理 `AEMeasurable.ae_eq_mk`：ae_eq_mk (h : AEMeasurable f μ) : f =ᵐ[μ] h.mk f
· 使用定理 `MeasureTheory.integral_map_of_stronglyMeasurable`：integral_map_of_strong
lyMeasurable {β} [MeasurableSpace β] {φ : α -> β} (hφ : Measurable φ) {f : β -> 
G} (hfm : StronglyMeasurable f) : ∫ y,…
· 使用定理 `AEMeasurable.measurable_mk`：measurable_mk (h : AEMeasurable f μ) : Measu
rable (h.mk f)
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
· 使用定理 `Filter.EventuallyEq.fun_comp`：∀ {α : Type u} {β : Type v} {γ : Type w} {
f g : α → β} {l : Filter α}, f =ᶠ[l] g → ∀ (h : β → γ), h ∘ f =ᶠ[l] h ∘ g
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.ae_eq_comp`：ae_eq_comp {f : α -> β} {g g' : β -> δ} (hf : 
AEMeasurable f μ) (h : g =ᵐ[μ.map f] g') : g ∘ f =ᵐ[μ] g' ∘ f
-/
theorem integral_map {β : Type*} [MeasurableSpace β]
    {φ : X → β} (hφ : Measurable φ) {f : β → E}
    (hfm : AEStronglyMeasurable f (μ.variation.map φ))
    (hfi' : μ.Integrable (f ∘ φ)) :
    ∫ᵛ y, f y ∂[B; μ.map φ] = ∫ᵛ x, f (φ x) ∂[B; μ] := by
  apply setToFun_of_le_map _ _ hfi' hfm hφ variation_map_le
  intro s x hs
  simp [hs, VectorMeasure.map, transpose, hφ]
/-
**MeasureTheory._root_.MeasurableEmbedding.variation_transpose_map** 是 Mathlib 中
的一个定理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasurableEmbedding.variation_transpose_map (hφ : MeasurableEmbedding φ) :
    ((μ.map φ).transpose B).variation = (μ.transpose B).variation.map φ := by
  rw [transpose_map, hφ.variation_map]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-
**MeasureTheory._root_.MeasurableEmbedding.integrable_map_vectorMeasure** 是 Math
lib 中的一个定理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasurableEmbedding.integrable_map_vectorMeasure
    (hφ : MeasurableEmbedding φ) {f : β → E} :
    (μ.map φ).Integrable f ↔ μ.Integrable (f ∘ φ) := by
  simp_rw [VectorMeasure.Integrable, ← hφ.integrable_map_iff, hφ.variation_map]
/-
**MeasureTheory._root_.MeasurableEmbedding.integral_map_vectorMeasure** 是 Mathli
b 中的一个定理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasurableEmbedding.integral_map_vectorMeasure
    (hφ : MeasurableEmbedding φ) {f : β → E} :
    ∫ᵛ y, f y ∂[B; μ.map φ] = ∫ᵛ x, f (φ x) ∂[B; μ] := by
  by_cases hfm : AEStronglyMeasurable f (μ.variation.map φ)
  · by_cases h'fm : μ.Integrable (f ∘ φ)
    · apply integral_map hφ.measurable hfm h'fm
    · rw [integral_undef, integral_undef]
      · exact h'fm
      · rwa [hφ.integrable_map_vectorMeasure]
  · rw [integral_non_aestronglyMeasurable, integral_non_aestronglyMeasurable]
    · rwa [hφ.aestronglyMeasurable_map_iff] at hfm
    · rwa [hφ.variation_map]
/-
**MeasureTheory._root_.Topology.IsClosedEmbedding.integral_map_vectorMeasure** 是
 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Topology.IsClosedEmbedding.integral_map_vectorMeasure
    [TopologicalSpace X] [BorelSpace X]
    [TopologicalSpace β] [BorelSpace β] (hφ : IsClosedEmbedding φ)
    {f : β → E} : ∫ᵛ y, f y ∂[B; μ.map φ] = ∫ᵛ x, f (φ x) ∂[B; μ] :=
  hφ.measurableEmbedding.integral_map_vectorMeasure
/-
**MeasureTheory.integral_map_equiv** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_map_equiv {β} [MeasurableSpace β] (e : α ≃ᵐ β) (f : β -> G) : ∫ y
, f y ∂Measure.map e μ = ∫ x, f (e x) ∂μ
参数：e : α ≃ᵐ β；f : β -> G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableEmbedding.integral_map`：∀ {α : Type u_1} {G : Type u_5} [inst 
: NormedAddCommGroup G] [inst_1 : NormedSpace ℝ G] {m : MeasurableSpace α}   {μ 
: MeasureTheory.Measur…
· 使用定理 `MeasurableEquiv.measurableEmbedding`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β),   MeasurableE
mbedding ⇑e
-/
theorem integral_map_equiv {β} [MeasurableSpace β] (e : X ≃ᵐ β) (f : β → E) :
    ∫ᵛ y, f y ∂[B; μ.map e] = ∫ᵛ x, f (e x) ∂[B; μ] :=
  e.measurableEmbedding.integral_map_vectorMeasure

/-- **Lebesgue dominated convergence theorem** provides sufficient conditions under which almost
  everywhere convergence of a sequence of functions implies the convergence of their integrals.
  We could weaken the condition `bound_integrable` to require
  `HasFiniteIntegral bound μ.variation` instead (i.e. not requiring that `bound` is
  measurable), but in all applications proving integrability is easier. -/
/-
**MeasureTheory.tendsto_integral_of_dominated_convergence** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory`。
形式化陈述：tendsto_integral_of_dominated_convergence {F : Nat -> α -> G} {f : α -> G}
 (bound : α -> Real) (F_measurable : forall n, AEStronglyMeasurable (F n) μ) (bo
und_integrable : Integrable bound μ) (h_bound : forall n, forallᵐ a ∂μ, ‖F n a‖ 
<= bound a) (h_lim : forallᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))) : T
endsto (fun n => ∫ a, F n a ∂μ) atTop (𝓝 <| ∫ a, f a ∂μ)
参数：bound : α -> Real；F_measurable : forall n, AEStronglyMeasurable (F n) μ；bound
_integrable : Integrable bound μ；h_bound : forall n, forallᵐ a ∂μ, ‖F n a‖ <= bo
und a；h_lim : forallᵐ a ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_weightedSMul`：dominatedFinMeasAdd
itive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) : DominatedFinMeasAdd
itive μ (weightedSMul μ : Set α -> F ->L[…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_eq_setToFun`：integral_eq_setToFun (f : α -> E) : 
∫ a, f a ∂μ = setToFun μ (weightedSMul μ) (dominatedFinMeasAdditive_weightedSMul
 μ) f
· 使用定理 `MeasureTheory.tendsto_setToFun_of_dominated_convergence`：tendsto_setToFu
n_of_dominated_convergence (hT : DominatedFinMeasAdditive μ T C) {fs : Nat -> α 
-> E} {f : α -> E} (bound : α -> Real) (fs_me…

--- 原说明 ---
**Lebesgue dominated convergence theorem** provides sufficient conditions under 
which almost
  everywhere convergence of a sequence of functions implies the convergence of t
heir integrals.
  We could weaken the condition `bound_integrable` to require
  `HasFiniteIntegral bound μ.variation` instead (i.e. not requiring that `bound`
 is
  measurable), but in all applications proving integrability is easier.
-/
theorem tendsto_integral_of_dominated_convergence {F : ℕ → X → E} {f : X → E} (bound : X → ℝ)
    (F_measurable : ∀ n, AEStronglyMeasurable (F n) μ.variation)
    (bound_integrable : Integrable bound μ.variation)
    (h_bound : ∀ n, ∀ᵐ a ∂μ.variation, ‖F n a‖ ≤ bound a)
    (h_lim : ∀ᵐ a ∂μ.variation, Tendsto (fun n ↦ F n a) atTop (𝓝 (f a))) :
    Tendsto (fun n ↦ ∫ᵛ a, F n a ∂[B; μ]) atTop (𝓝 <| ∫ᵛ a, f a ∂[B; μ]) :=
  tendsto_setToFun_of_dominated_convergence _ bound F_measurable bound_integrable h_bound h_lim

/-- Lebesgue dominated convergence theorem for filters with a countable basis -/
/-
**MeasureTheory.tendsto_integral_filter_of_dominated_convergence** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory`。
形式化陈述：tendsto_integral_filter_of_dominated_convergence {ι} {l : Filter ι} [l.IsC
ountablyGenerated] {F : ι -> α -> G} {f : α -> G} (bound : α -> Real) (hF_meas :
 forallᶠ n in l, AEStronglyMeasurable (F n) μ) (h_bound : forallᶠ n in l, forall
ᵐ a ∂μ, ‖F n a‖ <= bound a) (bound_integrable : Integrable bound μ) (h_lim : for
allᵐ a ∂μ, Tendsto (fun n => F n a) l (𝓝 (f a))) : Tendsto (fun n => ∫ a, F n a 
∂μ) l (𝓝 <| ∫ a, f a ∂μ)
参数：bound : α -> Real；hF_meas : forallᶠ n in l, AEStronglyMeasurable (F n) μ；h_bo
und : forallᶠ n in l, forallᵐ a ∂μ, ‖F n a‖ <= bound a；bound_integrable : Integr
able bound μ；h_lim : forallᵐ a ∂μ, Tendsto (fun n => F n a) l (𝓝 (f a))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_weightedSMul`：dominatedFinMeasAdd
itive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) : DominatedFinMeasAdd
itive μ (weightedSMul μ : Set α -> F ->L[…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_eq_setToFun`：integral_eq_setToFun (f : α -> E) : 
∫ a, f a ∂μ = setToFun μ (weightedSMul μ) (dominatedFinMeasAdditive_weightedSMul
 μ) f
· 使用定理 `MeasureTheory.tendsto_setToFun_filter_of_dominated_convergence`：tendsto_
setToFun_filter_of_dominated_convergence (hT : DominatedFinMeasAdditive μ T C) {
ι} {l : Filter ι} [l.IsCountablyGenerated] {fs : ι -…

--- 原说明 ---
Lebesgue dominated convergence theorem for filters with a countable basis
-/
theorem tendsto_integral_filter_of_dominated_convergence {l : Filter ι} [l.IsCountablyGenerated]
    {F : ι → X → E} {f : X → E} (bound : X → ℝ)
    (hF_meas : ∀ᶠ n in l, AEStronglyMeasurable (F n) μ.variation)
    (h_bound : ∀ᶠ n in l, ∀ᵐ a ∂μ.variation, ‖F n a‖ ≤ bound a)
    (bound_integrable : Integrable bound μ.variation)
    (h_lim : ∀ᵐ a ∂μ.variation, Tendsto (fun n ↦ F n a) l (𝓝 (f a))) :
    Tendsto (fun n ↦ ∫ᵛ a, F n a ∂[B; μ]) l (𝓝 <| ∫ᵛ a, f a ∂[B; μ]) :=
  tendsto_setToFun_filter_of_dominated_convergence _ bound hF_meas h_bound bound_integrable h_lim

/-- Lebesgue dominated convergence theorem for series. -/
/-
**MeasureTheory.hasSum_integral_of_dominated_convergence** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory`。
形式化陈述：hasSum_integral_of_dominated_convergence {ι} [Countable ι] {F : ι -> α -> 
G} {f : α -> G} (bound : ι -> α -> Real) (hF_meas : forall n, AEStronglyMeasurab
le (F n) μ) (h_bound : forall n, forallᵐ a ∂μ, ‖F n a‖ <= bound n a) (bound_summ
able : forallᵐ a ∂μ, Summable fun n => bound n a) (bound_integrable : Integrable
 (fun a => ∑' n, bound n a) μ) (h_lim : forallᵐ a ∂μ, HasSum (fun n => F n a) (f
 a)) : HasSum (fun n => ∫ a, F n a ∂μ) (∫ a, f a ∂μ)
参数：bound : ι -> α -> Real；hF_meas : forall n, AEStronglyMeasurable (F n) μ；h_bou
nd : forall n, forallᵐ a ∂μ, ‖F n a‖ <= bound n a；bound_summable : forallᵐ a ∂μ,
 Summable fun n => bound n a；bound_integrable : Integrable (fun a => ∑' n, bound
 n a) μ；h_lim : forallᵐ a ∂μ, HasSum (fun n => F n a) (f a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_weightedSMul`：dominatedFinMeasAdd
itive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) : DominatedFinMeasAdd
itive μ (weightedSMul μ : Set α -> F ->L[…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_eq_setToFun`：integral_eq_setToFun (f : α -> E) : 
∫ a, f a ∂μ = setToFun μ (weightedSMul μ) (dominatedFinMeasAdditive_weightedSMul
 μ) f
· 使用定理 `MeasureTheory.hasSum_setToFun_of_dominated_convergence`：hasSum_setToFun_
of_dominated_convergence (hT : DominatedFinMeasAdditive μ T C) {ι} [Countable ι]
 {F : ι -> α -> E} {f : α -> E} (bound : ι -…

--- 原说明 ---
Lebesgue dominated convergence theorem for series.
-/
theorem hasSum_integral_of_dominated_convergence [Countable ι] {F : ι → X → E} {f : X → E}
    (bound : ι → X → ℝ) (hF_meas : ∀ n, AEStronglyMeasurable (F n) μ.variation)
    (h_bound : ∀ n, ∀ᵐ a ∂μ.variation, ‖F n a‖ ≤ bound n a)
    (bound_summable : ∀ᵐ a ∂μ.variation, Summable fun n ↦ bound n a)
    (bound_integrable : Integrable (fun a ↦ ∑' n, bound n a) μ.variation)
    (h_lim : ∀ᵐ a ∂μ.variation, HasSum (fun n ↦ F n a) (f a)) :
    HasSum (fun n ↦ ∫ᵛ a, F n a ∂[B; μ]) (∫ᵛ a, f a ∂[B; μ]) :=
  hasSum_setToFun_of_dominated_convergence _ bound hF_meas h_bound bound_summable bound_integrable
    h_lim
/-
**MeasureTheory.integral_tsum** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_tsum {ι} [Countable ι] {f : ι -> α -> G} (hf : forall i, AEStrong
lyMeasurable (f i) μ) (hf' : ∑' i, ∫⁻ a : α, ‖f i a‖ₑ ∂μ != ∞) : ∫ a, ∑' i, f i 
a ∂μ = ∑' i, ∫ a, f i a ∂μ
参数：hf : forall i, AEStronglyMeasurable (f i) μ；hf' : ∑' i, ∫⁻ a : α, ‖f i a‖ₑ ∂μ
 != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_weightedSMul`：dominatedFinMeasAdd
itive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) : DominatedFinMeasAdd
itive μ (weightedSMul μ : Set α -> F ->L[…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_eq_setToFun`：integral_eq_setToFun (f : α -> E) : 
∫ a, f a ∂μ = setToFun μ (weightedSMul μ) (dominatedFinMeasAdditive_weightedSMul
 μ) f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.setToFun_tsum`：setToFun_tsum [CompleteSpace E] (hT : Domin
atedFinMeasAdditive μ T C) {ι} [Countable ι] {f : ι -> α -> E} (hf : forall i, A
EStronglyMeasurab…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.integral_def`：∀ {α : Type u_6} {G : Type u_7} [inst : Norm
edAddCommGroup G] [inst_1 : NormedSpace ℝ G] {x : MeasurableSpace α}   (μ : Meas
ureTheory.Measur…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `tsum_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [ins
t_1 : TopologicalSpace α] {L : SummationFilter β},   ∑'[L] (x : β), 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_tsum [CompleteSpace E] [Countable ι]
    {f : ι → X → E} (hf : ∀ i, AEStronglyMeasurable (f i) μ.variation)
    (hf' : ∑' i, ∫⁻ a : X, ‖f i a‖ₑ ∂μ.variation ≠ ∞) :
    ∫ᵛ a, ∑' i, f i a ∂[B; μ] = ∑' i, ∫ᵛ a, f i a ∂[B; μ] :=
  setToFun_tsum _ hf hf'

/-- Corollary of the Lebesgue dominated convergence theorem: If a sequence of functions `F n` is
(eventually) uniformly bounded by a constant and converges (eventually) pointwise to a
function `f`, then the integrals of `F n` with respect to a vector measure `μ` with finite
variation converge to the integral of `f`. -/
/-
**MeasureTheory.tendsto_integral_filter_of_norm_le_const** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory`。
形式化陈述：tendsto_integral_filter_of_norm_le_const {ι} {l : Filter ι} [l.IsCountably
Generated] {F : ι -> α -> G} [IsFiniteMeasure μ] {f : α -> G} (h_meas : forallᶠ 
n in l, AEStronglyMeasurable (F n) μ) (h_bound : exists C, forallᶠ n in l, (fora
llᵐ ω ∂μ, ‖F n ω‖ <= C)) (h_lim : forallᵐ ω ∂μ, Tendsto (fun n => F n ω) l (𝓝 (f
 ω))) : Tendsto (fun n => ∫ ω, F n ω ∂μ) l (nhds (∫ ω, f ω ∂μ))
参数：h_meas : forallᶠ n in l, AEStronglyMeasurable (F n) μ；h_bound : exists C, for
allᶠ n in l, (forallᵐ ω ∂μ, ‖F n ω‖ <= C)；h_lim : forallᵐ ω ∂μ, Tendsto (fun n =
> F n ω) l (𝓝 (f ω))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.dominatedFinMeasAdditive_weightedSMul`：dominatedFinMeasAdd
itive_weightedSMul {_ : MeasurableSpace α} (μ : Measure α) : DominatedFinMeasAdd
itive μ (weightedSMul μ : Set α -> F ->L[…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.integral_eq_setToFun`：integral_eq_setToFun (f : α -> E) : 
∫ a, f a ∂μ = setToFun μ (weightedSMul μ) (dominatedFinMeasAdditive_weightedSMul
 μ) f
· 使用定理 `MeasureTheory.tendsto_setToFun_filter_of_norm_le_const`：tendsto_setToFun
_filter_of_norm_le_const (hT : DominatedFinMeasAdditive μ T C) {ι} {l : Filter ι
} [l.IsCountablyGenerated] {F : ι -> α -> E}…

--- 原说明 ---
Corollary of the Lebesgue dominated convergence theorem: If a sequence of functi
ons `F n` is
(eventually) uniformly bounded by a constant and converges (eventually) pointwis
e to a
function `f`, then the integrals of `F n` with respect to a vector measure `μ` w
ith finite
variation converge to the integral of `f`.
-/
theorem tendsto_integral_filter_of_norm_le_const {l : Filter ι} [l.IsCountablyGenerated]
    {F : ι → X → E} [IsFiniteMeasure μ.variation] {f : X → E}
    (h_meas : ∀ᶠ n in l, AEStronglyMeasurable (F n) μ.variation)
    (h_bound : ∃ C, ∀ᶠ n in l, ∀ᵐ a ∂μ.variation, ‖F n a‖ ≤ C)
    (h_lim : ∀ᵐ a ∂μ.variation, Tendsto (fun n ↦ F n a) l (𝓝 (f a))) :
    Tendsto (fun n ↦ ∫ᵛ a, F n a ∂[B; μ]) l (𝓝 (∫ᵛ a, f a ∂[B; μ])) :=
  tendsto_setToFun_filter_of_norm_le_const _ h_meas h_bound h_lim

end VectorMeasure

end MeasureTheory

