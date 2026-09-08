/-
Copyright (c) 2024 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Field.TransferInstance
public import Mathlib.Analysis.Normed.Ring.WithAbs
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Topology.MetricSpace.Completion

/-!
# WithAbs for fields

This extends the `WithAbs` mechanism to fields, providing a type synonym for a field which depends
on an absolute value. This is useful when dealing with several absolute values on the same field.

In particular this allows us to define the completion of a field at a given absolute value.
-/

public section

open Topology

namespace WithAbs

variable {R S : Type*} [Semiring S] [PartialOrder S]

section Field

variable [Field R] {T : Type*} [Field T] (v : AbsoluteValue R S)

/-
**WithAbs.** 是 Mathlib 中的一个实例，位于命名空间 `WithAbs`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Field (WithAbs v) := fast_instance% (equiv v).field
/-
**WithAbs.normedField** 是 Mathlib 中的一个实例，位于命名空间 `WithAbs`。
形式化陈述：normedField (v : AbsoluteValue R Real) : NormedField (WithAbs v)
参数：v : AbsoluteValue R Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance normedField (v : AbsoluteValue R ℝ) : NormedField (WithAbs v) :=
  letI := v.toNormedField
  fast_instance% (equiv v).normedField
/-
**WithAbs.** 是 Mathlib 中的一个实例，位于命名空间 `WithAbs`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Module R T] [FiniteDimensional R T] :
    FiniteDimensional (WithAbs v) T :=
  Module.Finite.of_restrictScalars_finite R (WithAbs v) T
/-
**WithAbs.** 是 Mathlib 中的一个实例，位于命名空间 `WithAbs`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Module T R] [FiniteDimensional T R] :
    FiniteDimensional T (WithAbs v) :=
  Module.Finite.equiv (linearEquiv T v).symm
/-
**WithAbs.** 是 Mathlib 中的一个实例，位于命名空间 `WithAbs`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Algebra R T] [Algebra.IsSeparable R T] :
    Algebra.IsSeparable (WithAbs v) T :=
  .of_equiv_equiv (equiv v).symm (.refl T) (by ext; simp [algebraMap_left_apply])
/-
**WithAbs.** 是 Mathlib 中的一个实例，位于命名空间 `WithAbs`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Algebra T R] [Algebra.IsSeparable T R] :
    Algebra.IsSeparable T (WithAbs v) :=
  AlgEquiv.Algebra.isSeparable (algEquiv T v).symm
/-
**WithAbs.toAbs_div** 是 Mathlib 中的一个定理，位于命名空间 `WithAbs`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : Semiring S] [inst_1 : PartialOrder
 S] [inst_2 : Field R] (v : AbsoluteValue R S)   (x y : R), WithAbs.toAbs v (x /
 y) = WithAbs.toAbs v x / WithAbs.toAbs v y
参数：v : AbsoluteValue R S；x y : R；x / y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toAbs_div (x y : R) : toAbs v (x / y) = toAbs v x / toAbs v y := rfl
/-
**WithAbs.ofAbs_div** 是 Mathlib 中的一个定理，位于命名空间 `WithAbs`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : Semiring S] [inst_1 : PartialOrder
 S] [inst_2 : Field R] (v : AbsoluteValue R S)   (x y : WithAbs v), (x / y).ofAb
s = x.ofAbs / y.ofAbs
参数：v : AbsoluteValue R S；x y : WithAbs v；x / y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofAbs_div (x y : WithAbs v) : ofAbs (x / y) = ofAbs x / ofAbs y := rfl
/-
**WithAbs.toAbs_inv** 是 Mathlib 中的一个定理，位于命名空间 `WithAbs`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : Semiring S] [inst_1 : PartialOrder
 S] [inst_2 : Field R] (v : AbsoluteValue R S)   (x : R), WithAbs.toAbs v x⁻¹ = 
(WithAbs.toAbs v x)⁻¹
参数：v : AbsoluteValue R S；x : R；WithAbs.toAbs v x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toAbs_inv (x : R) : toAbs v x⁻¹ = (toAbs v x)⁻¹ := rfl
/-
**WithAbs.ofAbs_inv** 是 Mathlib 中的一个定理，位于命名空间 `WithAbs`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : Semiring S] [inst_1 : PartialOrder
 S] [inst_2 : Field R] (v : AbsoluteValue R S)   (x : WithAbs v), x⁻¹.ofAbs = x.
ofAbs⁻¹
参数：v : AbsoluteValue R S；x : WithAbs v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofAbs_inv (x : WithAbs v) : ofAbs (x⁻¹) = (ofAbs x)⁻¹ := rfl

/- Note that `AbsoluteValue.tendsto_div_one_add_pow_nhds_one` would follow from the below
result if `WithAbs v` had a topology for general value rings `S`. Currently `WithAbs v` only has
a topology when `S = ℝ`. -/
/-
**WithAbs.tendsto_one_div_one_add_pow_nhds_one** 是 Mathlib 中的一个定理，位于命名空间 `WithAb
s`。
形式化陈述：tendsto_one_div_one_add_pow_nhds_one {v : AbsoluteValue R Real} {a : R} (h
a : v a < 1) : Filter.atTop.Tendsto (fun n => (equiv v).symm (1 / (1 + a ^ n))) 
(𝓝 1)
参数：ha : v a < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `WithAbs.equiv_symm_apply`：∀ {R : Type u_1} {S : Type u_2} [inst : Semiri
ng S] [inst_1 : PartialOrder S] [inst_2 : Semiring R]   (v : AbsoluteValue R S) 
(ofAbs : R), (…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `tendsto_inv_iff₀`：tendsto_inv_iff₀ {l : Filter α} {f : α -> G₀} (hx : x 
!= 0) : Tendsto (fun x => (f x)⁻¹) l (𝓝 x⁻¹) ↔ Tendsto f l (𝓝 x)
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `WithAbs.instNontrivial`：∀ {R : Type u_1} {S : Type u_2} [inst : Semiring
 S] [inst_1 : PartialOrder S] [inst_2 : Semiring R]   (v : AbsoluteValue R S) [N
ontrivial R]…
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `tendsto_iff_norm_sub_tendsto_zero`：∀ {α : Type u_1} {E : Type u_4} [inst
 : SeminormedAddCommGroup E] {f : α → E} {a : Filter α} {b : E},   Filter.Tendst
o f a (nhds b) ↔ Filter…
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `abs_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (z : E), |‖z‖| 
= ‖z‖

--- 原说明 ---
Note that `AbsoluteValue.tendsto_div_one_add_pow_nhds_one` would follow from the
 below
result if `WithAbs v` had a topology for general value rings `S`. Currently `Wit
hAbs v` only has
a topology when `S = ℝ`.
-/
theorem tendsto_one_div_one_add_pow_nhds_one {v : AbsoluteValue R ℝ} {a : R} (ha : v a < 1) :
    Filter.atTop.Tendsto (fun n ↦ (equiv v).symm (1 / (1 + a ^ n))) (𝓝 1) := by
  simpa using! inv_one (G := WithAbs v) ▸ (tendsto_inv_iff₀ one_ne_zero).2
    (tendsto_iff_norm_sub_tendsto_zero.2 <| by simpa using! ha)

end Field

section CommRing

variable [CommRing R] {T : Type*} [Field T] [Algebra R T] (w : AbsoluteValue T ℝ)

/-
**WithAbs.** 是 Mathlib 中的一个实例，位于命名空间 `WithAbs`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : UniformContinuousConstSMul R (WithAbs w) where
  uniformContinuous_const_smul r := by
    simp_rw [Algebra.smul_def]
    exact (Ring.uniformContinuousConstSMul _).uniformContinuous_const_smul _

end CommRing

/-!
### The completion of a field at an absolute value.
-/

variable {K : Type*} [Field K] {v : AbsoluteValue K ℝ} {L : Type*} [NormedField L]
  {f : WithAbs v →+* L}

end WithAbs

namespace AbsoluteValue

open WithAbs

variable {K : Type*} [Field K] (v : AbsoluteValue K ℝ)

/-- The completion of a field with respect to a real absolute value. -/
/-
**AbsoluteValue.Completion** 是 Mathlib 中的一个缩写定义，位于命名空间 `AbsoluteValue`。
形式化陈述：Completion
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The completion of a field with respect to a real absolute value.
-/
abbrev Completion := UniformSpace.Completion (WithAbs v)

namespace Completion

/-
**AbsoluteValue.Completion.** 是 Mathlib 中的一个实例，位于命名空间 `AbsoluteValue.Completion`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Coe K v.Completion where
  coe k : v.Completion := ↑(toAbs v k)

variable {L : Type*} [NormedField L] [CompleteSpace L] {f : WithAbs v →+* L} {v}

/-- If the absolute value of a normed field factors through an embedding into another normed field
that is locally compact, then the completion of the first normed field is also locally compact. -/
/-
**AbsoluteValue.Completion.locallyCompactSpace** 是 Mathlib 中的一个定理，位于命名空间 `Absolu
teValue.Completion`。
形式化陈述：locallyCompactSpace [LocallyCompactSpace L] (h : Isometry f) : LocallyComp
actSpace v.Completion
参数：h : Isometry f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsClosedEmbedding.locallyCompactSpace`：∀ {X : Type u_1} {Y : Ty
pe u_2} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] [LocallyCompac
tSpace Y]   {f : X → Y}, Topology.Is…
· 使用定理 `Isometry.isClosedEmbedding`：isClosedEmbedding [CompleteSpace α] [EMetric
Space γ] {f : α -> γ} (hf : Isometry f) : IsClosedEmbedding f
· 使用定理 `Isometry.completion_extension`：Isometry.completion_extension [PseudoMetr
icSpace β] [CompleteSpace β] [T0Space β] {f : α -> β} (h : Isometry f) : Isometr
y (Completion.exten…
· 使用定理 `CompletableTopField.toT0Space`：∀ {K : Type u_1} {inst : Field K} {inst_1
 : UniformSpace K} [self : CompletableTopField K], T0Space K
· 使用定理 `completableTopField_of_complete`：∀ (L : Type u_3) [inst : Field L] [inst
_1 : UniformSpace L] [IsTopologicalDivisionRing L] [T0Space L] [CompleteSpace L]
,   CompletableTopFie…
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `T3Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T3
Space X], T0Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `instT4SpaceOfT1SpaceOfNormalSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [T1Space X] [NormalSpace X], T4Space X
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `CompletelyNormalSpace.toNormalSpace`：∀ {X : Type u_1} [inst : Topologica
lSpace X] [CompletelyNormalSpace X], NormalSpace X
· 使用定理 `UniformSpace.completelyNormalSpace_of_isCountablyGenerated_uniformity`：∀
 {α : Type u} [inst : UniformSpace α] [(uniformity α).IsCountablyGenerated], Com
pletelyNormalSpace α
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated

--- 原说明 ---
If the absolute value of a normed field factors through an embedding into anothe
r normed field
that is locally compact, then the completion of the first normed field is also l
ocally compact.
-/
theorem locallyCompactSpace [LocallyCompactSpace L] (h : Isometry f) :
    LocallyCompactSpace v.Completion :=
  h.completion_extension.isClosedEmbedding.locallyCompactSpace

end AbsoluteValue.Completion

