/-
Copyright (c) 2020 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde
-/
module

public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.RCLike.Extend

/-!
# Norm properties of the extension of continuous `ℝ`-linear functionals to `𝕜`-linear functionals

This file shows that `StrongDual.extendRCLike` preserves the norm of the functional.
-/

public section

open RCLike ContinuousLinearMap Module
open scoped ComplexConjugate

variable {𝕜 E F : Type*} [RCLike 𝕜]

/-- If a real-linear functional is bounded by a `𝕜`-seminorm, then its `𝕜`-linear extension
is bounded by the same seminorm. -/
/-
**Module.Dual.norm_extendRCLike_le_seminorm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.Dual.norm_extendRCLike_le_seminorm [AddCommGroup E] [Module 𝕜 E] [M
odule Real E] [IsScalarTower Real 𝕜 E] (fr : Dual Real E) {p : Seminorm 𝕜 E} (hp
 : forall x, |fr x| <= p x) (x : E) : ‖(fr.extendRCLike x : 𝕜)‖ <= p x
参数：fr : Dual Real E；hp : forall x, |fr x| <= p x；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `AddGroupSeminormClass.toNonnegHomClass`：∀ {F : Type u_2} {α : Type u_3} 
{β : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMon
oid β]   [inst_3 : LinearOrd…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
· 使用定理 `Module.Dual.norm_extendRCLike_apply_sq`：norm_extendRCLike_apply_sq (fr :
 Dual Real F) (x : F) : ‖(fr.extendRCLike x : 𝕜)‖ ^ 2 = fr (conj (fr.extendRCLik
e x : 𝕜) • x)
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
· 使用定理 `SeminormClass.map_smul_eq_mul`：∀ {F : Type u_12} {𝕜 : outParam (Type u_1
3)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGroup E}  
 {inst_2 : SMul 𝕜 E…
· 使用定理 `RCLike.norm_conj`：norm_conj (z : K) : ‖conj z‖ = ‖z‖
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_le_mul_iff_left₀`：mul_le_mul_iff_left₀ [MulPosMono α] [MulPosReflect
LE α] (a0 : 0 < a) : b * a <= c * a ↔ b <= c
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a

--- 原说明 ---
If a real-linear functional is bounded by a `𝕜`-seminorm, then its `𝕜`-linear ex
tension
is bounded by the same seminorm.
-/
theorem Module.Dual.norm_extendRCLike_le_seminorm [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
    [IsScalarTower ℝ 𝕜 E] (fr : Dual ℝ E) {p : Seminorm 𝕜 E} (hp : ∀ x, |fr x| ≤ p x) (x : E) :
    ‖(fr.extendRCLike x : 𝕜)‖ ≤ p x := by
  by_cases hx : fr.extendRCLike (𝕜 := 𝕜) x = 0
  · simp [hx]
  have hsq : ‖fr.extendRCLike (𝕜 := 𝕜) x‖ ^ 2 ≤ ‖fr.extendRCLike (𝕜 := 𝕜) x‖ * p x := calc
    _ = fr (conj (fr.extendRCLike x) • x) := fr.norm_extendRCLike_apply_sq x
    _ ≤ |fr (conj (fr.extendRCLike x) • x)| := le_abs_self _
    _ ≤ p (conj (fr.extendRCLike x) • x) := hp _
    _ = ‖conj (fr.extendRCLike x)‖ * p x := map_smul_eq_mul _ _ _
    _ = ‖(fr.extendRCLike x)‖ * p x := by rw [norm_conj]
  exact (mul_le_mul_iff_left₀ (norm_pos_iff.2 hx)).1 <| by simpa [pow_two, mul_comm] using hsq

namespace StrongDual

/-- The extension `StrongDual.extendRCLike` as a continuous linear equivalence between
the strong duals when scalar multiplication (by `𝕜`) is jointly continuous. -/
@[expose, simps! -isSimp apply symm_apply]
/-
**StrongDual.extendRCLikeL** 是 Mathlib 中的一个定义，位于命名空间 `StrongDual`。
形式化陈述：extendRCLikeL {𝕜 F : Type*} [RCLike 𝕜] [TopologicalSpace F] [AddCommGroup 
F] [Module 𝕜 F] [ContinuousSMul 𝕜 F] [Module Real F] [IsScalarTower Real 𝕜 F] : 
StrongDual Real F ≃L[Real] StrongDual 𝕜 F where toLinearEquiv
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ

--- 原说明 ---
The extension `StrongDual.extendRCLike` as a continuous linear equivalence betwe
en
the strong duals when scalar multiplication (by `𝕜`) is jointly continuous.
-/
noncomputable def extendRCLikeL {𝕜 F : Type*} [RCLike 𝕜] [TopologicalSpace F]
    [AddCommGroup F] [Module 𝕜 F] [ContinuousSMul 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F] :
    StrongDual ℝ F ≃L[ℝ] StrongDual 𝕜 F where
  toLinearEquiv := extendRCLikeₗ
  continuous_toFun := by
    rw [(ContinuousLinearMap.isEmbedding_restrictScalars ℝ).continuous_iff]
    let smulI : F →L[ℝ] F := (I : 𝕜) • ContinuousLinearMap.id 𝕜 F |>.restrictScalars ℝ
    let mulI : 𝕜 →L[ℝ] 𝕜 := ContinuousLinearMap.mul ℝ 𝕜 (I : 𝕜)
    exact ofRealCLM.postcomp F - mulI.postcomp F ∘L smulI.precomp 𝕜 ∘L ofRealCLM.postcomp F
      |>.continuous
  continuous_invFun := reCLM.postcomp F |>.continuous.comp <|
    (ContinuousLinearMap.isEmbedding_restrictScalars ℝ).continuous

@[simp]
/-
**StrongDual.toLinearEquiv_extendRCLikeL** 是 Mathlib 中的一个引理，位于命名空间 `StrongDual`。
形式化陈述：toLinearEquiv_extendRCLikeL {𝕜 F : Type*} [RCLike 𝕜] [TopologicalSpace F] 
[AddCommGroup F] [Module 𝕜 F] [ContinuousSMul 𝕜 F] [Module Real F] [IsScalarTowe
r Real 𝕜 F] : (extendRCLikeL (𝕜
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
lemma toLinearEquiv_extendRCLikeL {𝕜 F : Type*} [RCLike 𝕜] [TopologicalSpace F]
    [AddCommGroup F] [Module 𝕜 F] [ContinuousSMul 𝕜 F] [Module ℝ F] [IsScalarTower ℝ 𝕜 F] :
    (extendRCLikeL (𝕜 := 𝕜) (F := F)).toLinearEquiv = extendRCLikeₗ :=
  rfl

/-- If a continuous real-linear functional is bounded by a `𝕜`-seminorm, then its `𝕜`-linear
extension is bounded by the same seminorm. -/
/-
**StrongDual.norm_extendRCLike_le_seminorm** 是 Mathlib 中的一个定理，位于命名空间 `StrongDual
`。
形式化陈述：norm_extendRCLike_le_seminorm [AddCommGroup E] [Module 𝕜 E] [Module Real E
] [IsScalarTower Real 𝕜 E] [TopologicalSpace E] [ContinuousConstSMul 𝕜 E] (fr : 
StrongDual Real E) {p : Seminorm 𝕜 E} (hp : forall x, |fr x| <= p x) (x : E) : ‖
(fr.extendRCLike x : 𝕜)‖ <= p x
参数：fr : StrongDual Real E；hp : forall x, |fr x| <= p x；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Dual.norm_extendRCLike_le_seminorm`：Module.Dual.norm_extendRCLike
_le_seminorm [AddCommGroup E] [Module 𝕜 E] [Module Real E] [IsScalarTower Real 𝕜
 E] (fr : Dual Real E) {p : Sem…

--- 原说明 ---
If a continuous real-linear functional is bounded by a `𝕜`-seminorm, then its `𝕜
`-linear
extension is bounded by the same seminorm.
-/
theorem norm_extendRCLike_le_seminorm [AddCommGroup E] [Module 𝕜 E] [Module ℝ E]
    [IsScalarTower ℝ 𝕜 E] [TopologicalSpace E] [ContinuousConstSMul 𝕜 E] (fr : StrongDual ℝ E)
    {p : Seminorm 𝕜 E} (hp : ∀ x, |fr x| ≤ p x) (x : E) :
    ‖(fr.extendRCLike x : 𝕜)‖ ≤ p x :=
  Dual.norm_extendRCLike_le_seminorm fr hp x

variable [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace ℝ F] [IsScalarTower ℝ 𝕜 F]

/-- The norm of the extension is bounded by `‖fr‖`. -/
/-
**StrongDual.norm_extendRCLike_bound** 是 Mathlib 中的一个定理，位于命名空间 `StrongDual`。
形式化陈述：norm_extendRCLike_bound (fr : StrongDual Real F) (x : F) : ‖(fr.extendRCLi
ke x : 𝕜)‖ <= ‖fr‖ * ‖x‖
参数：fr : StrongDual Real F；x : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Dual.norm_extendRCLike_le_seminorm`：Module.Dual.norm_extendRCLike
_le_seminorm [AddCommGroup E] [Module 𝕜 E] [Module Real E] [IsScalarTower Real 𝕜
 E] (fr : Dual Real E) {p : Sem…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
· 使用定理 `Seminorm.instIsSMulApplyReal`：∀ {R : Type u_1} {𝕜 : Type u_3} {E : Type 
u_7} [inst : SeminormedRing 𝕜] [inst_1 : AddGroup E] [inst_2 : SMul 𝕜 E]   [inst
_3 : SMul R ℝ] [in…
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
The norm of the extension is bounded by `‖fr‖`.
-/
theorem norm_extendRCLike_bound (fr : StrongDual ℝ F) (x : F) :
    ‖(fr.extendRCLike x : 𝕜)‖ ≤ ‖fr‖ * ‖x‖ := by
  refine Module.Dual.norm_extendRCLike_le_seminorm (p := ‖fr‖₊ • normSeminorm 𝕜 F)
    fr.toLinearMap ?_ x
  simp [← Real.norm_eq_abs, NNReal.smul_def, le_opNorm]

@[simp]
/-
**StrongDual.norm_extendRCLike** 是 Mathlib 中的一个定理，位于命名空间 `StrongDual`。
形式化陈述：norm_extendRCLike (fr : StrongDual Real F) : ‖(fr.extendRCLike : StrongDua
l 𝕜 F)‖ = ‖fr‖
参数：fr : StrongDual Real F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `StrongDual.norm_extendRCLike_bound`：norm_extendRCLike_bound (fr : Strong
Dual Real F) (x : F) : ‖(fr.extendRCLike x : 𝕜)‖ <= ‖fr‖ * ‖x‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `StrongDual.re_extendRCLike_apply`：re_extendRCLike_apply (g : StrongDual 
Real F) (x : F) : re ((extendRCLike g) x : 𝕜) = g x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `RCLike.abs_re_le_norm`：abs_re_le_norm (z : K) : |re z| <= ‖z‖
· 使用定理 `ContinuousLinearMap.le_opNorm`：le_opNorm : ‖f x‖ <= ‖f‖ * ‖x‖
-/
theorem norm_extendRCLike (fr : StrongDual ℝ F) : ‖(fr.extendRCLike : StrongDual 𝕜 F)‖ = ‖fr‖ :=
  le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fr.norm_extendRCLike_bound) <|
    opNorm_le_bound _ (norm_nonneg _) fun x =>
      calc
        ‖fr x‖ = ‖re (fr.extendRCLike x : 𝕜)‖ := by simp
        _ ≤ ‖(fr.extendRCLike x : 𝕜)‖ := abs_re_le_norm _
        _ ≤ ‖(fr.extendRCLike : StrongDual 𝕜 F)‖ * ‖x‖ := le_opNorm _ _

/-- `StrongDual.extendRCLike` bundled into a linear isometry equivalence. -/
@[expose, simps! -isSimp apply symm_apply]
/-
**StrongDual.extendRCLike** 是 Mathlib 中的一个定义，位于命名空间 `StrongDual`。
形式化陈述：extendRCLike (fr : StrongDual Real F) : StrongDual 𝕜 F where __
参数：fr : StrongDual Real F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`StrongDual.extendRCLike` bundled into a linear isometry equivalence.
-/
noncomputable def extendRCLikeₗᵢ : StrongDual ℝ F ≃ₗᵢ[ℝ] StrongDual 𝕜 F where
  toLinearEquiv := StrongDual.extendRCLikeₗ
  norm_map' := norm_extendRCLike

@[simp]
/-
**StrongDual.toLinearEquiv_extendRCLike** 是 Mathlib 中的一个引理，位于命名空间 `StrongDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toLinearEquiv_extendRCLikeₗᵢ :
    (extendRCLikeₗᵢ (𝕜 := 𝕜) (F := F)).toLinearEquiv = extendRCLikeₗ :=
  rfl

@[simp]
/-
**StrongDual.toContinuousLinearEquiv_extendRCLike** 是 Mathlib 中的一个引理，位于命名空间 `Str
ongDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toContinuousLinearEquiv_extendRCLikeₗᵢ :
    (extendRCLikeₗᵢ (F := F) (𝕜 := 𝕜)).toContinuousLinearEquiv = extendRCLikeL :=
  rfl

end StrongDual

namespace ContinuousLinearMap
open StrongDual

@[deprecated (since := "2026-02-24")] alias norm_extendTo𝕜'_bound := norm_extendRCLike_bound
@[deprecated (since := "2026-02-24")] alias norm_extendTo𝕜' := norm_extendRCLike
@[deprecated (since := "2026-02-24")] alias norm_extendTo𝕜 := norm_extendRCLike

end ContinuousLinearMap

