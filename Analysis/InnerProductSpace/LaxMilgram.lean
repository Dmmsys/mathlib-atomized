/-
Copyright (c) 2022 Daniel Roca González. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Roca González
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# The Lax-Milgram Theorem

We consider a Hilbert space `V` over `ℝ`
equipped with a bounded bilinear form `B : V →L[ℝ] V →L[ℝ] ℝ`.

Recall that a bilinear form `B : V →L[ℝ] V →L[ℝ] ℝ` is *coercive*
iff `∃ C, (0 < C) ∧ ∀ u, C * ‖u‖ * ‖u‖ ≤ B u u`.
Under the hypothesis that `B` is coercive we prove the Lax-Milgram theorem:
that is, the map `InnerProductSpace.continuousLinearMapOfBilin` from
`Analysis.InnerProductSpace.Dual` can be upgraded to a continuous equivalence
`IsCoercive.continuousLinearEquivOfBilin : V ≃L[ℝ] V`.

## References

* We follow the notes of Peter Howard's Spring 2020 *M612: Partial Differential Equations* lecture,
  see[howard]

## Tags

dual, Lax-Milgram
-/

@[expose] public section


noncomputable section

open RCLike LinearMap ContinuousLinearMap InnerProductSpace

open LinearMap (ker range)

open RealInnerProductSpace NNReal

universe u

namespace IsCoercive

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable {B : V →L[ℝ] V →L[ℝ] ℝ}

local postfix:1024 "♯" => continuousLinearMapOfBilin (𝕜 := ℝ)

/-
**IsCoercive.bounded_below** 是 Mathlib 中的一个定理，位于命名空间 `IsCoercive`。
形式化陈述：bounded_below (coercive : IsCoercive B) : exists C, 0 < C ∧ forall v, C * 
‖v‖ <= ‖B♯ v‖
参数：coercive : IsCoercive B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
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
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
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
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `InnerProductSpace.continuousLinearMapOfBilin_apply`：continuousLinearMapO
fBilin_apply (v w : E) : ⟪B♯ v, w⟫ = B v w
· 使用定理 `real_inner_le_norm`：real_inner_le_norm (x y : F) : ⟪x, y⟫_Real <= ‖x‖ * 
‖y‖
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
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
theorem bounded_below (coercive : IsCoercive B) : ∃ C, 0 < C ∧ ∀ v, C * ‖v‖ ≤ ‖B♯ v‖ := by
  rcases coercive with ⟨C, C_ge_0, coercivity⟩
  refine ⟨C, C_ge_0, ?_⟩
  intro v
  by_cases h : 0 < ‖v‖
  · refine (mul_le_mul_iff_left₀ h).mp ?_
    calc
      C * ‖v‖ * ‖v‖ ≤ B v v := coercivity v
      _ = ⟪B♯ v, v⟫_ℝ := (continuousLinearMapOfBilin_apply B v v).symm
      _ ≤ ‖B♯ v‖ * ‖v‖ := real_inner_le_norm (B♯ v) v
  · have : v = 0 := by simpa using h
    simp [this]
/-
**IsCoercive.antilipschitz** 是 Mathlib 中的一个定理，位于命名空间 `IsCoercive`。
形式化陈述：antilipschitz (coercive : IsCoercive B) : exists C : Real>=0, 0 < C ∧ Anti
lipschitzWith C B♯
参数：coercive : IsCoercive B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
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
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsCoercive.bounded_below`：bounded_below (coercive : IsCoercive B) : exis
ts C, 0 < C ∧ forall v, C * ‖v‖ <= ‖B♯ v‖
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.toNNReal_pos`：toNNReal_pos {r : Real} : 0 < Real.toNNReal r ↔ 0 < r
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `ContinuousLinearMap.antilipschitz_of_bound`：antilipschitz_of_bound (f : 
E ->SL[σ] F) {K : Real>=0} (h : forall x, ‖x‖ <= K * ‖f x‖) : AntilipschitzWith 
K f
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `max_eq_left_of_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b 
< a → max a b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `inv_mul_le_iff₀`：inv_mul_le_iff₀ (hc : 0 < c) : c⁻¹ * b <= a ↔ b <= c * 
a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
theorem antilipschitz (coercive : IsCoercive B) : ∃ C : ℝ≥0, 0 < C ∧ AntilipschitzWith C B♯ := by
  rcases coercive.bounded_below with ⟨C, C_pos, below_bound⟩
  refine ⟨C⁻¹.toNNReal, Real.toNNReal_pos.mpr (inv_pos.mpr C_pos), ?_⟩
  refine ContinuousLinearMap.antilipschitz_of_bound B♯ ?_
  simp_rw [Real.coe_toNNReal', max_eq_left_of_lt (inv_pos.mpr C_pos), ←
    inv_mul_le_iff₀ (inv_pos.mpr C_pos)]
  simpa using below_bound
/-
**IsCoercive.ker_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `IsCoercive`。
形式化陈述：ker_eq_bot (coercive : IsCoercive B) : B♯.ker = ⊥
参数：coercive : IsCoercive B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
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
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `IsCoercive.antilipschitz`：antilipschitz (coercive : IsCoercive B) : exis
ts C : Real>=0, 0 < C ∧ AntilipschitzWith C B♯
· 使用定理 `AntilipschitzWith.injective`：∀ {α : Type u_4} {β : Type u_5} [inst : EMe
tricSpace α] [inst_1 : PseudoEMetricSpace β] {K : NNReal} {f : α → β},   Antilip
schitzWith K f → …
-/
theorem ker_eq_bot (coercive : IsCoercive B) : B♯.ker = ⊥ := by
  rw [LinearMap.ker_eq_bot]
  rcases coercive.antilipschitz with ⟨_, _, antilipschitz⟩
  exact antilipschitz.injective
/-
**IsCoercive.isClosed_range** 是 Mathlib 中的一个定理，位于命名空间 `IsCoercive`。
形式化陈述：isClosed_range (coercive : IsCoercive B) : IsClosed (B♯.range : Set V)
参数：coercive : IsCoercive B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
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
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsCoercive.antilipschitz`：antilipschitz (coercive : IsCoercive B) : exis
ts C : Real>=0, 0 < C ∧ AntilipschitzWith C B♯
· 使用定理 `AntilipschitzWith.isClosed_range`：isClosed_range {α β : Type*} [PseudoEM
etricSpace α] [EMetricSpace β] [CompleteSpace α] {f : α -> β} {K : Real>=0} (hf 
: AntilipschitzWith K …
· 使用定理 `ContinuousLinearMap.uniformContinuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2}
 [inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {E₁ : Type u_9}  
 {E₂ : Type u_10} [inst_2 :…
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
-/
theorem isClosed_range (coercive : IsCoercive B) : IsClosed (B♯.range : Set V) := by
  rcases coercive.antilipschitz with ⟨_, _, antilipschitz⟩
  exact antilipschitz.isClosed_range B♯.uniformContinuous
/-
**IsCoercive.range_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `IsCoercive`。
形式化陈述：range_eq_top (coercive : IsCoercive B) : B♯.range = ⊤
参数：coercive : IsCoercive B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
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
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsCoercive.isClosed_range`：isClosed_range (coercive : IsCoercive B) : Is
Closed (B♯.range : Set V)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.orthogonal_orthogonal`：orthogonal_orthogonal [K.HasOrthogonalP
rojection] : Kᗮᗮ = K
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `Submodule.eq_top_iff'`：eq_top_iff' {p : Submodule R M} : p = ⊤ ↔ forall 
x, x in p
· 使用定理 `inner_zero_left`：inner_zero_left (x : E) : ⟪0, x⟫ = 0
· 使用定理 `norm_eq_zero`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a‖ = 
0 ↔ a = 0
· 使用定理 `mul_self_eq_zero`：mul_self_eq_zero : a * a = 0 ↔ a = 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用引理 `mul_right_inj'`：mul_right_inj' (ha : a != 0) : a * b = a * c ↔ b = c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `InnerProductSpace.continuousLinearMapOfBilin_apply`：continuousLinearMapO
fBilin_apply (v w : E) : ⟪B♯ v, w⟫ = B v w
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
（共 33 条，此处仅展示前 30 条）
-/
theorem range_eq_top (coercive : IsCoercive B) : B♯.range = ⊤ := by
  have := coercive.isClosed_range.completeSpace_coe
  rw [← B♯.range.orthogonal_orthogonal]
  rw [Submodule.eq_top_iff']
  intro v w mem_w_orthogonal
  rcases coercive with ⟨C, C_pos, coercivity⟩
  obtain rfl : w = 0 := by
    rw [← norm_eq_zero, ← mul_self_eq_zero, ← mul_right_inj' C_pos.ne', mul_zero, ←
      mul_assoc]
    apply le_antisymm
    · calc
        C * ‖w‖ * ‖w‖ ≤ B w w := coercivity w
        _ = ⟪B♯ w, w⟫_ℝ := (continuousLinearMapOfBilin_apply B w w).symm
        _ = 0 := mem_w_orthogonal _ ⟨w, rfl⟩
    · positivity
  exact inner_zero_left _

/-- The Lax-Milgram equivalence of a coercive bounded bilinear operator:
for all `v : V`, `continuousLinearEquivOfBilin B v` is the unique element `V`
such that `continuousLinearEquivOfBilin B v, w⟫ = B v w`.
The Lax-Milgram theorem states that this is a continuous equivalence.
-/
/-
**IsCoercive.continuousLinearEquivOfBilin** 是 Mathlib 中的一个定义，位于命名空间 `IsCoercive`
。
形式化陈述：continuousLinearEquivOfBilin (coercive : IsCoercive B) : V ≃L[Real] V
参数：coercive : IsCoercive B。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsCoercive.ker_eq_bot`：ker_eq_bot (coercive : IsCoercive B) : B♯.ker = ⊥
· 使用定理 `IsCoercive.range_eq_top`：range_eq_top (coercive : IsCoercive B) : B♯.ran
ge = ⊤

--- 原说明 ---
The Lax-Milgram equivalence of a coercive bounded bilinear operator:
for all `v : V`, `continuousLinearEquivOfBilin B v` is the unique element `V`
such that `continuousLinearEquivOfBilin B v, w⟫ = B v w`.
The Lax-Milgram theorem states that this is a continuous equivalence.
-/
def continuousLinearEquivOfBilin (coercive : IsCoercive B) : V ≃L[ℝ] V :=
  ContinuousLinearEquiv.ofBijective B♯ coercive.ker_eq_bot coercive.range_eq_top

@[simp]
/-
**IsCoercive.continuousLinearEquivOfBilin_apply** 是 Mathlib 中的一个定理，位于命名空间 `IsCoe
rcive`。
形式化陈述：continuousLinearEquivOfBilin_apply (coercive : IsCoercive B) (v w : V) : ⟪
coercive.continuousLinearEquivOfBilin v, w⟫_Real = B v w
参数：coercive : IsCoercive B；v w : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
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
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `InnerProductSpace.continuousLinearMapOfBilin_apply`：continuousLinearMapO
fBilin_apply (v w : E) : ⟪B♯ v, w⟫ = B v w
-/
theorem continuousLinearEquivOfBilin_apply (coercive : IsCoercive B) (v w : V) :
    ⟪coercive.continuousLinearEquivOfBilin v, w⟫_ℝ = B v w :=
  continuousLinearMapOfBilin_apply B v w
/-
**IsCoercive.unique_continuousLinearEquivOfBilin** 是 Mathlib 中的一个定理，位于命名空间 `IsCo
ercive`。
形式化陈述：unique_continuousLinearEquivOfBilin (coercive : IsCoercive B) {v f : V} (i
s_lax_milgram : forall w, ⟪f, w⟫_Real = B v w) : f = coercive.continuousLinearEq
uivOfBilin v
参数：coercive : IsCoercive B；is_lax_milgram : forall w, ⟪f, w⟫_Real = B v w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
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
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `InnerProductSpace.unique_continuousLinearMapOfBilin`：unique_continuousLi
nearMapOfBilin {v f : E} (is_lax_milgram : forall w, ⟪f, w⟫ = B v w) : f = B♯ v
-/
theorem unique_continuousLinearEquivOfBilin (coercive : IsCoercive B) {v f : V}
    (is_lax_milgram : ∀ w, ⟪f, w⟫_ℝ = B v w) : f = coercive.continuousLinearEquivOfBilin v :=
  unique_continuousLinearMapOfBilin B is_lax_milgram

end IsCoercive

