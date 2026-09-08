/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Algebra.Unitization
/-! # The minimal unitization of a C⋆-algebra

This file shows that when `E` is a C⋆-algebra (over a densely normed field `𝕜`), that the minimal
`Unitization` is as well. In order to ensure that the norm structure is available, we must first
show that every C⋆-algebra is a `RegularNormedAlgebra`.

In addition, we show that in a `RegularNormedAlgebra` which is a `StarRing` for which the
involution is isometric, that multiplication on the right is also an isometry (i.e.,
`Isometry (ContinuousLinearMap.mul 𝕜 E).flip`).
-/

public section

open ContinuousLinearMap

local postfix:max "⋆" => star

variable (𝕜 : Type*) {E : Type*}

namespace ContinuousLinearMap

variable [NontriviallyNormedField 𝕜] [NonUnitalNormedRing E] [StarRing E] [NormedStarGroup E]
variable [NormedSpace 𝕜 E] [IsScalarTower 𝕜 E E] [SMulCommClass 𝕜 E E] [RegularNormedAlgebra 𝕜 E]

/-
**ContinuousLinearMap.opNorm_mul_flip_apply** 是 Mathlib 中的一个引理，位于命名空间 `Continuou
sLinearMap`。
形式化陈述：opNorm_mul_flip_apply (a : E) : ‖(mul 𝕜 E).flip a‖ = ‖a‖
参数：a : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
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
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `norm_mul_le`：norm_mul_le (a b : α) : ‖a * b‖ <= ‖a‖ * ‖b‖
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
· 使用引理 `norm_star`：norm_star (x : E) : ‖x⋆‖ = ‖x‖
· 使用定理 `ContinuousLinearMap.le_opNorm`：le_opNorm : ‖f x‖ <= ‖f‖ * ‖x‖
· 使用引理 `ContinuousLinearMap.opNorm_mul_apply`：opNorm_mul_apply (x : R) : ‖mul 𝕜 
R x‖ = ‖x‖
-/
lemma opNorm_mul_flip_apply (a : E) : ‖(mul 𝕜 E).flip a‖ = ‖a‖ := by
  refine le_antisymm
    (opNorm_le_bound _ (norm_nonneg _) fun b => by simpa only [mul_comm] using! norm_mul_le b a) ?_
  suffices ‖mul 𝕜 E (star a)‖ ≤ ‖(mul 𝕜 E).flip a‖ by
    simpa only [ge_iff_le, opNorm_mul_apply, norm_star] using! this
  refine opNorm_le_bound _ (norm_nonneg _) fun b => ?_
  calc ‖mul 𝕜 E (star a) b‖ = ‖(mul 𝕜 E).flip a (star b)‖ := by
        simpa only [mul_apply', flip_apply, star_mul, star_star] using! norm_star (star b * a)
    _ ≤ ‖(mul 𝕜 E).flip a‖ * ‖b‖ := by
        simpa only [flip_apply, mul_apply', norm_star] using! le_opNorm ((mul 𝕜 E).flip a) (star b)
/-
**ContinuousLinearMap.opNNNorm_mul_flip_apply** 是 Mathlib 中的一个引理，位于命名空间 `Continu
ousLinearMap`。
形式化陈述：opNNNorm_mul_flip_apply (a : E) : ‖(mul 𝕜 E).flip a‖₊ = ‖a‖₊
参数：a : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
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
· 使用引理 `ContinuousLinearMap.opNorm_mul_flip_apply`：opNorm_mul_flip_apply (a : E)
 : ‖(mul 𝕜 E).flip a‖ = ‖a‖
-/
lemma opNNNorm_mul_flip_apply (a : E) : ‖(mul 𝕜 E).flip a‖₊ = ‖a‖₊ :=
  Subtype.ext (opNorm_mul_flip_apply 𝕜 a)

variable (E)
/-
**ContinuousLinearMap.isometry_mul_flip** 是 Mathlib 中的一个引理，位于命名空间 `ContinuousLin
earMap`。
形式化陈述：isometry_mul_flip : Isometry (mul 𝕜 E).flip
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHomClass.isometry_of_norm`：∀ {𝓕 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : SeminormedAddGroup E] [inst_1 : SeminormedAddGroup F]   [inst
_2 : FunLike 𝓕 E F] [Add…
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
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用引理 `ContinuousLinearMap.opNorm_mul_flip_apply`：opNorm_mul_flip_apply (a : E)
 : ‖(mul 𝕜 E).flip a‖ = ‖a‖
-/
lemma isometry_mul_flip : Isometry (mul 𝕜 E).flip :=
  AddMonoidHomClass.isometry_of_norm _ (opNorm_mul_flip_apply 𝕜)

end ContinuousLinearMap

variable [DenselyNormedField 𝕜] [NonUnitalNormedRing E] [StarRing E] [CStarRing E]
variable [NormedSpace 𝕜 E] [IsScalarTower 𝕜 E E] [SMulCommClass 𝕜 E E]
variable (E)

set_option backward.isDefEq.respectTransparency false in
/-- A C⋆-algebra over a densely normed field is a regular normed algebra. -/
/-
**CStarRing.instRegularNormedAlgebra** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：CStarRing.instRegularNormedAlgebra : RegularNormedAlgebra 𝕜 E where isomet
ry_mul'
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHomClass.isometry_of_norm`：∀ {𝓕 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : SeminormedAddGroup E] [inst_1 : SeminormedAddGroup F]   [inst
_2 : FunLike 𝓕 E F] [Add…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NNReal.eq_iff`：∀ {n m : NNReal}, n = m ↔ ↑n = ↑m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.sSup_unitClosedBall_eq_nnnorm`：sSup_unitClosedBall_e
q_nnnorm (f : E ->SL[σ₁₂] F) : sSup ((fun x => ‖f x‖₊) '' closedBall 0 1) = ‖f‖₊
· 使用定理 `csSup_eq_of_forall_le_of_forall_lt_exists_gt`：csSup_eq_of_forall_le_of_f
orall_lt_exists_gt (hs : s.Nonempty) (H : forall a in s, a <= b) (H' : forall w,
 w < b -> exists a in s, w < a) : …
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.nonempty_closedBall`：nonempty_closedBall : (closedBall x ε).Nonem
pty ↔ 0 <= ε
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `ContinuousLinearMap.unit_le_opNorm`：unit_le_opNorm : ‖x‖ <= 1 -> ‖f x‖ <
= ‖f‖
· 使用定理 `mem_closedBall_zero_iff`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] 
{a : E} {r : ℝ}, a ∈ Metric.closedBall 0 r ↔ ‖a‖ ≤ r
· 使用定理 `ContinuousLinearMap.opNorm_mul_apply_le`：opNorm_mul_apply_le (x : R) : ‖
mul 𝕜 R x‖ <= ‖x‖
· 使用定理 `LT.lt.pos`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : Zero
 α] [IsBotZeroClass α], a < b → 0 < b
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `NormedField.exists_lt_nnnorm_lt`：exists_lt_nnnorm_lt {r₁ r₂ : Real>=0} (
h : r₁ < r₂) : exists x : α, r₁ < ‖x‖₊ ∧ ‖x‖₊ < r₂
· 使用定理 `mul_lt_mul_of_pos_right`：mul_lt_mul_of_pos_right [MulPosStrictMono α] (h
bc : b < c) (ha : 0 < a) : b * a < c * a
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
（共 59 条，此处仅展示前 30 条）

--- 原说明 ---
A C⋆-algebra over a densely normed field is a regular normed algebra.
-/
instance CStarRing.instRegularNormedAlgebra : RegularNormedAlgebra 𝕜 E where
  isometry_mul' := AddMonoidHomClass.isometry_of_norm (mul 𝕜 E) fun a => NNReal.eq_iff.mp <|
    show ‖mul 𝕜 E a‖₊ = ‖a‖₊ by
    rw [← sSup_unitClosedBall_eq_nnnorm]
    refine csSup_eq_of_forall_le_of_forall_lt_exists_gt ?_ ?_ fun r hr => ?_
    · exact (Metric.nonempty_closedBall.mpr zero_le_one).image _
    · rintro - ⟨x, hx, rfl⟩
      exact
        ((mul 𝕜 E a).unit_le_opNorm x <| mem_closedBall_zero_iff.mp hx).trans
          (opNorm_mul_apply_le 𝕜 E a)
    · have ha : 0 < ‖a‖₊ := hr.pos
      rw [← inv_inv ‖a‖₊, NNReal.lt_inv_iff_mul_lt (inv_ne_zero ha.ne')] at hr
      obtain ⟨k, hk₁, hk₂⟩ :=
        NormedField.exists_lt_nnnorm_lt 𝕜 (mul_lt_mul_of_pos_right hr <| inv_pos.2 ha)
      refine ⟨_, ⟨k • star a, ?_, rfl⟩, ?_⟩
      · simpa only [mem_closedBall_zero_iff, norm_smul, one_mul, norm_star] using!
          (NNReal.le_inv_iff_mul_le ha.ne').1 (one_mul ‖a‖₊⁻¹ ▸ hk₂.le : ‖k‖₊ ≤ ‖a‖₊⁻¹)
      · simp only [map_smul, nnnorm_smul, mul_apply', CStarRing.nnnorm_self_mul_star]
        rwa [← div_lt_iff₀ (mul_pos ha ha), div_eq_mul_inv, mul_inv, ← mul_assoc]

section CStarProperty

variable [StarRing 𝕜] [StarModule 𝕜 E]
variable {E}

/-- This is the key lemma used to establish the instance `Unitization.instCStarRing`
(i.e., proving that the norm on `Unitization 𝕜 E` satisfies the C⋆-property). We split this one
out so that declaring the `CStarRing` instance doesn't time out. -/
/-
**Unitization.norm_splitMul_snd_sq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Unitization.norm_splitMul_snd_sq (x : Unitization 𝕜 E) : ‖(Unitization.spl
itMul 𝕜 E x).snd‖ ^ 2 <= ‖(Unitization.splitMul 𝕜 E (star x * x)).snd‖
参数：x : Unitization 𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Real.le_sqrt`：le_sqrt (hx : 0 <= x) (hy : 0 <= y) : x <= √y ↔ x ^ 2 <= y
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Unitization.splitMul_apply`：splitMul_apply (x : Unitization 𝕜 A) : split
Mul 𝕜 A x = (x.fst, algebraMap 𝕜 (A ->L[𝕜] A) x.fst + mul 𝕜 A x.snd)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.sSup_unitClosedBall_eq_norm`：sSup_unitClosedBall_eq_
norm (f : E ->SL[σ₁₂] F) : sSup ((fun x => ‖f x‖) '' closedBall 0 1) = ‖f‖
· 使用定理 `csSup_le`：csSup_le (h₁ : s.Nonempty) (h₂ : forall b in s, b <= a) : sSup
 s <= a
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.nonempty_closedBall`：nonempty_closedBall : (closedBall x ε).Nonem
pty ↔ 0 <= ε
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `Real.sqrt_sq`：sqrt_sq (h : 0 <= x) : √(x ^ 2) = x
· 使用定理 `Real.sqrt_le_sqrt_iff`：sqrt_le_sqrt_iff (hy : 0 <= y) : √x <= √y ↔ x <= 
y
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `CStarRing.norm_star_mul_self`：norm_star_mul_self {x : E} : ‖x⋆ * x‖ = ‖x
‖ * ‖x‖
· 使用定理 `add_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Add β}   {inst_2 : Add F} [self : IsAd…
· 使用定理 `StarAddMonoid.star_add`：∀ {R : Type u} {inst : AddMonoid R} [self : Star
AddMonoid R] (r s : R), star (r + s) = star r + star s
· 使用定理 `ContinuousLinearMap.mul_apply'`：mul_apply' (x y : R) : mul 𝕜 R x y = x *
 y
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `smul_apply`：∀ {M : Type u_1} {F : Type u_2} {α : outParam (Type u_3)} {β
 : outParam (Type u_4)} {inst : FunLike F α β}   {inst_1 : SMul M β} {inst_2 : S
…
（共 68 条，此处仅展示前 30 条）

--- 原说明 ---
This is the key lemma used to establish the instance `Unitization.instCStarRing`
(i.e., proving that the norm on `Unitization 𝕜 E` satisfies the C⋆-property). We
 split this one
out so that declaring the `CStarRing` instance doesn't time out.
-/
theorem Unitization.norm_splitMul_snd_sq (x : Unitization 𝕜 E) :
    ‖(Unitization.splitMul 𝕜 E x).snd‖ ^ 2 ≤ ‖(Unitization.splitMul 𝕜 E (star x * x)).snd‖ := by
  /- The key idea is that we can use `sSup_unitClosedBall_eq_norm` to make this about
  applying this linear map to elements of norm at most one. There is a bit of `sqrt` and `sq`
  shuffling that needs to occur, which is primarily just an annoyance. -/
  refine (Real.le_sqrt (norm_nonneg _) (norm_nonneg _)).mp ?_
  simp only [Unitization.splitMul_apply]
  rw [← sSup_unitClosedBall_eq_norm]
  refine csSup_le ((Metric.nonempty_closedBall.2 zero_le_one).image _) ?_
  rintro - ⟨b, hb, rfl⟩
  simp only
  -- rewrite to a more convenient form; this is where we use the C⋆-property
  rw [← Real.sqrt_sq (norm_nonneg _), Real.sqrt_le_sqrt_iff (norm_nonneg _), sq,
    ← CStarRing.norm_star_mul_self, add_apply, star_add, mul_apply',
    Algebra.algebraMap_eq_smul_one, smul_apply,
    one_apply_eq_self, star_mul, star_smul, add_mul, smul_mul_assoc, ← mul_smul_comm,
    mul_assoc, ← mul_add, ← sSup_unitClosedBall_eq_norm]
  refine (norm_mul_le _ _).trans ?_
  calc
    _ ≤ ‖star x.fst • (x.fst • b + x.snd * b) + star x.snd * (x.fst • b + x.snd * b)‖ := by
      nth_rewrite 2 [← one_mul ‖_ + _‖]
      gcongr
      exact (norm_star b).symm ▸ mem_closedBall_zero_iff.1 hb
    _ ≤ sSup (_ '' Metric.closedBall 0 1) := le_csSup ?_ ⟨b, hb, ?_⟩
  -- now we just check the side conditions for `le_csSup`. There is nothing of interest here.
  · refine ⟨‖(star x * x).fst‖ + ‖(star x * x).snd‖, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    refine (norm_add_le _ _).trans ?_
    gcongr
    · rw [Algebra.algebraMap_eq_smul_one]
      refine (norm_smul _ _).trans_le ?_
      simpa only [mul_one] using!
        mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.1 hy) (norm_nonneg (star x * x).fst)
    · exact (unit_le_opNorm _ y <| mem_closedBall_zero_iff.1 hy).trans (opNorm_mul_apply_le _ _ _)
  · simp only [add_apply, mul_apply', Unitization.snd_star, Unitization.snd_mul,
      Unitization.fst_mul, Unitization.fst_star, Algebra.algebraMap_eq_smul_one, smul_apply,
      one_apply_eq_self, smul_add, mul_add, add_mul]
    simp only [smul_smul, smul_mul_assoc, ← add_assoc, ← mul_assoc, mul_smul_comm]

variable {𝕜}
variable [CStarRing 𝕜]

/-- The norm on `Unitization 𝕜 E` satisfies the C⋆-property -/
/-
**Unitization.instCStarRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Unitization.instCStarRing : CStarRing (Unitization 𝕜 E) where norm_mul_sel
f_le x
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Unitization.splitMul_apply`：splitMul_apply (x : Unitization 𝕜 A) : split
Mul 𝕜 A x = (x.fst, algebraMap 𝕜 (A ->L[𝕜] A) x.fst + mul 𝕜 A x.snd)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Unitization.norm_splitMul_snd_sq`：Unitization.norm_splitMul_snd_sq (x : 
Unitization 𝕜 E) : ‖(Unitization.splitMul 𝕜 E x).snd‖ ^ 2 <= ‖(Unitization.split
Mul 𝕜 E (star x * x)).…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `Prod.snd_mul`：snd_mul (p q : M × N) : (p * q).2 = p.2 * q.2
· 使用定理 `norm_mul_le`：norm_mul_le (a b : α) : ‖a * b‖ <= ‖a‖ * ‖b‖
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
（共 48 条，此处仅展示前 30 条）

--- 原说明 ---
The norm on `Unitization 𝕜 E` satisfies the C⋆-property
-/
instance Unitization.instCStarRing : CStarRing (Unitization 𝕜 E) where
  norm_mul_self_le x := by
    -- rewrite both sides as a `⊔`
    simp only [Unitization.norm_def, Prod.norm_def]
    -- Show that `(Unitization.splitMul 𝕜 E x).snd` satisfies the C⋆-property, in two stages:
    have h₁ : ∀ x : Unitization 𝕜 E,
        ‖(Unitization.splitMul 𝕜 E x).snd‖ ≤ ‖(Unitization.splitMul 𝕜 E (star x)).snd‖ := by
      simp only [Unitization.splitMul_apply, Unitization.snd_star, Unitization.fst_star]
      intro x
      /- split based on whether the term inside the norm is zero or not. If so, it's trivial.
      If not, then apply `norm_splitMul_snd_sq` and cancel one copy of the norm -/
      by_cases h : algebraMap 𝕜 (E →L[𝕜] E) x.fst + mul 𝕜 E x.snd = 0
      · simp only [h, norm_zero]
        exact norm_nonneg _
      · have : ‖(Unitization.splitMul 𝕜 E x).snd‖ ^ 2 ≤
          ‖(Unitization.splitMul 𝕜 E (star x)).snd‖ * ‖(Unitization.splitMul 𝕜 E x).snd‖ :=
          (norm_splitMul_snd_sq 𝕜 x).trans <| by
            rw [map_mul, Prod.snd_mul]
            exact norm_mul_le _ _
        rw [sq] at this
        rw [← Ne, ← norm_pos_iff] at h
        simp only [Unitization.splitMul_apply, Unitization.snd_star,
          Unitization.fst_star] at this
        exact (mul_le_mul_iff_left₀ h).mp this
    -- in this step we make use of the key lemma `norm_splitMul_snd_sq`
    have h₂ : ‖(Unitization.splitMul 𝕜 E (star x * x)).snd‖
        = ‖(Unitization.splitMul 𝕜 E x).snd‖ ^ 2 := by
      refine le_antisymm ?_ (norm_splitMul_snd_sq 𝕜 x)
      rw [map_mul, Prod.snd_mul]
      exact (norm_mul_le _ _).trans <| by
        rw [sq]
        gcongr
        simpa only [star_star] using h₁ (star x)
    -- Show that `(Unitization.splitMul 𝕜 E x).fst` satisfies the C⋆-property
    have h₃ : ‖(Unitization.splitMul 𝕜 E (star x * x)).fst‖
        = ‖(Unitization.splitMul 𝕜 E x).fst‖ ^ 2 := by
      simp only [Unitization.splitMul_apply, Unitization.fst_mul, Unitization.fst_star,
        norm_mul, norm_star, sq]
    rw [h₂, h₃]
    /- use the definition of the norm, and split into cases based on whether the norm in the first
    coordinate is bigger or smaller than the norm in the second coordinate. -/
    by_cases! h : ‖(Unitization.splitMul 𝕜 E x).fst‖ ≤ ‖(Unitization.splitMul 𝕜 E x).snd‖
    · rw [sq, sq, sup_eq_right.mpr h, sup_eq_right.mpr (mul_self_le_mul_self (norm_nonneg _) h)]
    · replace h := h.le
      rw [sq, sq, sup_eq_left.mpr h, sup_eq_left.mpr (mul_self_le_mul_self (norm_nonneg _) h)]

/-- The minimal unitization (over `ℂ`) of a C⋆-algebra, equipped with the C⋆-norm. When `A` is
unital, `A⁺¹ ≃⋆ₐ[ℂ] (ℂ × A)`. -/
scoped[CStarAlgebra] postfix:max "⁺¹" => Unitization ℂ

/-
**Unitization.instCStarAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `Unitization`。
形式化陈述：{A : Type u_3} → [NonUnitalCStarAlgebra A] → CStarAlgebra (Unitization ℂ A
)
参数：Unitization ℂ A。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalCStarAlgebra.toIsScalarTower`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], IsScalarTower ℂ A A
· 使用定理 `NonUnitalCStarAlgebra.toSMulCommClass`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], SMulCommClass ℂ A A
· 使用定理 `NonUnitalCStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : NonUnitalCS
tarAlgebra A], StarModule ℂ A
-/
noncomputable instance Unitization.instCStarAlgebra {A : Type*} [NonUnitalCStarAlgebra A] :
    CStarAlgebra (Unitization ℂ A) where
/-
**Unitization.instCommCStarAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `Unitization`。
形式化陈述：{A : Type u_3} → [NonUnitalCommCStarAlgebra A] → CommCStarAlgebra (Unitiza
tion ℂ A)
参数：Unitization ℂ A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance Unitization.instCommCStarAlgebra {A : Type*} [NonUnitalCommCStarAlgebra A] :
    CommCStarAlgebra (Unitization ℂ A) where

end CStarProperty

