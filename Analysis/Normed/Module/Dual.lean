/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Michał Świętek
-/
module

public import Mathlib.Analysis.LocallyConvex.Polar
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.Normed.Module.RCLike.Basic
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.Analysis.LocallyConvex.AbsConvex
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Analysis.LocallyConvex.SeparatingDual

/-!
# Polar sets in the strong dual of a normed space

In this file we study polar sets in the strong dual `StrongDual` of a normed space.

## Main definitions

* `polar 𝕜 s` is the subset of `StrongDual 𝕜 E` consisting of those functionals `x'` for which
  `‖x' z‖ ≤ 1` for every `z ∈ s`.

## References

* [Conway, John B., A course in functional analysis][conway1990]

## Tags

strong dual, polar
-/

public section

noncomputable section

open Topology Bornology

namespace NormedSpace

section PolarSets

open Metric Set StrongDual

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-
**NormedSpace.isClosed_polar** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：isClosed_polar (s : Set E) : IsClosed (StrongDual.polar 𝕜 s)
参数：s : Set E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.polar_eq_iInter`：polar_eq_iInter {s : Set E} : B.polar s = ⋂ x
 in s, { y : F | ‖B x y‖ <= 1 }
· 使用定理 `isClosed_biInter`：isClosed_biInter {s : Set α} {f : α -> Set X} (h : for
all i in s, IsClosed (f i)) : IsClosed (⋂ i in s, f i)
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Continuous.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAddGr
oup E] [inst_1 : TopologicalSpace α] {f : α → E},   Continuous f → Continuous fu
n x =…
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `isClosed_Iic`：isClosed_Iic : IsClosed (Iic a)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
-/
theorem isClosed_polar (s : Set E) : IsClosed (StrongDual.polar 𝕜 s) := by
  dsimp only [StrongDual.polar]
  simp only [LinearMap.polar_eq_iInter, LinearMap.flip_apply]
  refine isClosed_biInter fun z _ => ?_
  exact isClosed_Iic.preimage (ContinuousLinearMap.apply 𝕜 𝕜 z).continuous.norm

@[simp]
/-
**NormedSpace.polar_closure** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：polar_closure (s : Set E) : StrongDual.polar 𝕜 (closure s) = StrongDual.po
lar 𝕜 s
参数：s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
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
· 使用定理 `LinearMap.polar_antitone`：polar_antitone : Antitone (B.polar : Set E -> 
Set F)
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `GaloisConnection.l_le`：l_le {a : α} {b : β} : a <= u b -> l a <= b
· 使用定理 `LinearMap.polar_gc`：polar_gc : GaloisConnection (OrderDual.toDual ∘ B.po
lar) (B.flip.polar ∘ OrderDual.ofDual)
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `GaloisConnection.le_u_l`：le_u_l (a) : a <= u (l a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `LinearMap.flip_flip`：flip_flip (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) : f.flip.
flip = f
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
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
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `NormedSpace.isClosed_polar`：isClosed_polar (s : Set E) : IsClosed (Stron
gDual.polar 𝕜 s)
-/
theorem polar_closure (s : Set E) : StrongDual.polar 𝕜 (closure s) = StrongDual.polar 𝕜 s :=
  ((topDualPairing 𝕜 E).flip.polar_antitone subset_closure).antisymm <|
    (topDualPairing 𝕜 E).flip.polar_gc.l_le <|
      closure_minimal ((topDualPairing 𝕜 E).flip.polar_gc.le_u_l s) <| by
        simpa [LinearMap.flip_flip] using!
          (isClosed_polar _ _).preimage (ContinuousLinearMap.apply 𝕜 𝕜 (E := E)).continuous

variable {𝕜}

/-- If `x'` is a `StrongDual 𝕜 E` element such that the norms `‖x' z‖` are bounded for `z ∈ s`, then
a small scalar multiple of `x'` is in `polar 𝕜 s`. -/
/-
**NormedSpace.smul_mem_polar** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：smul_mem_polar {s : Set E} {x' : StrongDual 𝕜 E} {c : 𝕜} (hc : forall z, z
 in s -> ‖x' z‖ <= ‖c‖) : c⁻¹ • x' in StrongDual.polar 𝕜 s
参数：hc : forall z, z in s -> ‖x' z‖ <= ‖c‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `LinearMap.zero_mem_polar`：zero_mem_polar (s : Set E) : (0 : F) in B.pola
r s
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `x'` is a `StrongDual 𝕜 E` element such that the norms `‖x' z‖` are bounded f
or `z ∈ s`, then
a small scalar multiple of `x'` is in `polar 𝕜 s`.
-/
theorem smul_mem_polar {s : Set E} {x' : StrongDual 𝕜 E} {c : 𝕜} (hc : ∀ z, z ∈ s → ‖x' z‖ ≤ ‖c‖) :
    c⁻¹ • x' ∈ StrongDual.polar 𝕜 s := by
  by_cases c_zero : c = 0
  · simp only [c_zero, inv_zero, zero_smul]
    exact (topDualPairing 𝕜 E).flip.zero_mem_polar _
  have eq : ∀ z, ‖c⁻¹ • x' z‖ = ‖c⁻¹‖ * ‖x' z‖ := fun z => norm_smul c⁻¹ _
  have le : ∀ z, z ∈ s → ‖c⁻¹ • x' z‖ ≤ ‖c⁻¹‖ * ‖c‖ := by
    intro z hzs
    rw [eq z]
    apply mul_le_mul (le_of_eq rfl) (hc z hzs) (norm_nonneg _) (norm_nonneg _)
  have cancel : ‖c⁻¹‖ * ‖c‖ = 1 := by
    simp only [c_zero, norm_eq_zero, Ne, not_false_iff, inv_mul_cancel₀, norm_inv]
  rwa [cancel] at le
/-
**NormedSpace.polar_ball_subset_closedBall_div** 是 Mathlib 中的一个定理，位于命名空间 `Normed
Space`。
形式化陈述：polar_ball_subset_closedBall_div {c : 𝕜} (hc : 1 < ‖c‖) {r : Real} (hr : 0
 < r) : StrongDual.polar 𝕜 (ball (0 : E) r) subseteq closedBall (0 : StrongDual 
𝕜 E) (‖c‖ / r)
参数：hc : 1 < ‖c‖；hr : 0 < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `ContinuousLinearMap.opNorm_le_of_shell`：opNorm_le_of_shell {f : E ->SL[σ
₁₂] F} {ε C : Real} (ε_pos : 0 < ε) (hC : 0 <= C) {c : 𝕜} (hc : 1 < ‖c‖) (hf : f
orall x, ε / ‖c‖ <= ‖x‖ -> ‖…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StrongDual.mem_polar_iff`：mem_polar_iff {x' : StrongDual 𝕜 E} (s : Set E
) : x' in polar 𝕜 s ↔ forall z in s, ‖x' z‖ <= 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `inv_le_iff_one_le_mul₀'`：inv_le_iff_one_le_mul₀' (ha : 0 < a) : a⁻¹ <= b
 ↔ 1 <= a * b
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
-/
theorem polar_ball_subset_closedBall_div {c : 𝕜} (hc : 1 < ‖c‖) {r : ℝ} (hr : 0 < r) :
    StrongDual.polar 𝕜 (ball (0 : E) r) ⊆ closedBall (0 : StrongDual 𝕜 E) (‖c‖ / r) := by
  intro x' hx'
  rw [StrongDual.mem_polar_iff] at hx'
  simp only [mem_closedBall_zero_iff, mem_ball_zero_iff] at *
  have hcr : 0 < ‖c‖ / r := div_pos (zero_lt_one.trans hc) hr
  refine ContinuousLinearMap.opNorm_le_of_shell hr hcr.le hc fun x h₁ h₂ => ?_
  calc
    ‖x' x‖ ≤ 1 := hx' _ h₂
    _ ≤ ‖c‖ / r * ‖x‖ := (inv_le_iff_one_le_mul₀' hcr).1 (by rwa [inv_div])

variable (𝕜)
/-
**NormedSpace.closedBall_inv_subset_polar_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `
NormedSpace`。
形式化陈述：closedBall_inv_subset_polar_closedBall {r : Real} : closedBall (0 : Strong
Dual 𝕜 E) r⁻¹ subseteq StrongDual.polar 𝕜 (closedBall (0 : E) r)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.le_opNorm`：le_opNorm : ‖f x‖ <= ‖f‖ * ‖x‖
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_closedBall_zero_iff`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] 
{a : E} {r : ℝ}, a ∈ Metric.closedBall 0 r ↔ ‖a‖ ≤ r
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `inv_mul_eq_div`：inv_mul_eq_div : a⁻¹ * b = b / a
· 使用引理 `div_self_le_one`：div_self_le_one (a : G₀) : a / a <= 1
-/
theorem closedBall_inv_subset_polar_closedBall {r : ℝ} :
    closedBall (0 : StrongDual 𝕜 E) r⁻¹ ⊆ StrongDual.polar 𝕜 (closedBall (0 : E) r) :=
  fun x' hx' x hx =>
  calc
    ‖x' x‖ ≤ ‖x'‖ * ‖x‖ := x'.le_opNorm x
    _ ≤ r⁻¹ * r :=
      (mul_le_mul (mem_closedBall_zero_iff.1 hx') (mem_closedBall_zero_iff.1 hx) (norm_nonneg _)
        (dist_nonneg.trans hx'))
    _ = r / r := inv_mul_eq_div _ _
    _ ≤ 1 := div_self_le_one r

/-- The `polar` of closed ball in a normed space `E` is the closed ball of the dual with inverse
radius. -/
/-
**NormedSpace.polar_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：polar_closedBall {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSp
ace 𝕜 E] {r : Real} (hr : 0 < r) : StrongDual.polar 𝕜 (closedBall (0 : E) r) = c
losedBall (0 : StrongDual 𝕜 E) r⁻¹
参数：hr : 0 < r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `ContinuousLinearMap.opNorm_le_of_ball`：opNorm_le_of_ball {f : E ->SL[σ₁₂
] F} {ε : Real} {C : Real} (ε_pos : 0 < ε) (hC : 0 <= C) (hf : forall x in ball 
(0 : E) ε, ‖f x‖ <= C * ‖x‖…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_nonneg`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Partia
lOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 ≤ a⁻¹ ↔ 0 ≤ a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `LinearMap.bound_of_ball_bound'`：LinearMap.bound_of_ball_bound' {r : Real
} (r_pos : 0 < r) (c : Real) (f : E ->ₗ[𝕜] 𝕜) (h : forall z in closedBall (0 : E
) r, ‖f z‖ <= c) (z …
· 使用定理 `NormedSpace.closedBall_inv_subset_polar_closedBall`：closedBall_inv_subse
t_polar_closedBall {r : Real} : closedBall (0 : StrongDual 𝕜 E) r⁻¹ subseteq Str
ongDual.polar 𝕜 (closedBall (0 : E) r)

--- 原说明 ---
The `polar` of closed ball in a normed space `E` is the closed ball of the dual 
with inverse
radius.
-/
theorem polar_closedBall {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] {r : ℝ}
    (hr : 0 < r) :
    StrongDual.polar 𝕜 (closedBall (0 : E) r) = closedBall (0 : StrongDual 𝕜 E) r⁻¹ := by
  refine Subset.antisymm ?_ (closedBall_inv_subset_polar_closedBall 𝕜)
  intro x' h
  simp only [mem_closedBall_zero_iff]
  refine ContinuousLinearMap.opNorm_le_of_ball hr (inv_nonneg.mpr hr.le) fun z _ => ?_
  simpa only [one_div] using! LinearMap.bound_of_ball_bound' hr 1 x'.toLinearMap h z
/-
**NormedSpace.polar_ball** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`。
形式化陈述：polar_ball {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 
E] {r : Real} (hr : 0 < r) : StrongDual.polar 𝕜 (ball (0 : E) r) = closedBall (0
 : StrongDual 𝕜 E) r⁻¹
参数：hr : 0 < r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NormedSpace.polar_closedBall`：polar_closedBall {𝕜 E : Type*} [RCLike 𝕜] 
[NormedAddCommGroup E] [NormedSpace 𝕜 E] {r : Real} (hr : 0 < r) : StrongDual.po
lar 𝕜 (closedBall …
· 使用定理 `closure_ball`：closure_ball (x : E) {r : Real} (hr : r != 0) : closure (b
all x r) = closedBall x r
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `NormedSpace.polar_closure`：polar_closure (s : Set E) : StrongDual.polar 
𝕜 (closure s) = StrongDual.polar 𝕜 s
-/
theorem polar_ball {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] {r : ℝ}
    (hr : 0 < r) : StrongDual.polar 𝕜 (ball (0 : E) r) = closedBall (0 : StrongDual 𝕜 E) r⁻¹ := by
  let : NormedSpace ℝ E := .restrictScalars ℝ 𝕜 E
  rw [← polar_closedBall hr, ← closure_ball _ hr.ne', polar_closure]

/-- Given a neighborhood `s` of the origin in a normed space `E`, the dual norms of all elements of
the polar `polar 𝕜 s` are bounded by a constant. -/
/-
**NormedSpace.isBounded_polar_of_mem_nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 `Normed
Space`。
形式化陈述：isBounded_polar_of_mem_nhds_zero {s : Set E} (s_nhds : s in 𝓝 (0 : E)) : I
sBounded (StrongDual.polar 𝕜 s)
参数：s_nhds : s in 𝓝 (0 : E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedField.exists_one_lt_norm`：exists_one_lt_norm : exists x : α, 1 < ‖
x‖
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists ε > 0, ball x ε su
bseteq s
· 使用定理 `Bornology.IsBounded.subset`：∀ {α : Type u_2} {x : Bornology α} {s t : Se
t α}, Bornology.IsBounded t → s ⊆ t → Bornology.IsBounded s
· 使用定理 `Metric.isBounded_closedBall`：isBounded_closedBall : IsBounded (closedBal
l x r)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
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
· 使用定理 `LinearMap.polar_antitone`：polar_antitone : Antitone (B.polar : Set E -> 
Set F)
· 使用定理 `NormedSpace.polar_ball_subset_closedBall_div`：polar_ball_subset_closedBa
ll_div {c : 𝕜} (hc : 1 < ‖c‖) {r : Real} (hr : 0 < r) : StrongDual.polar 𝕜 (ball
 (0 : E) r) subseteq closedBall (0…

--- 原说明 ---
Given a neighborhood `s` of the origin in a normed space `E`, the dual norms of 
all elements of
the polar `polar 𝕜 s` are bounded by a constant.
-/
theorem isBounded_polar_of_mem_nhds_zero {s : Set E} (s_nhds : s ∈ 𝓝 (0 : E)) :
    IsBounded (StrongDual.polar 𝕜 s) := by
  obtain ⟨a, ha⟩ : ∃ a : 𝕜, 1 < ‖a‖ := NormedField.exists_one_lt_norm 𝕜
  obtain ⟨r, r_pos, r_ball⟩ : ∃ r : ℝ, 0 < r ∧ ball 0 r ⊆ s := Metric.mem_nhds_iff.1 s_nhds
  exact isBounded_closedBall.subset
    (((topDualPairing 𝕜 E).flip.polar_antitone r_ball).trans <|
      polar_ball_subset_closedBall_div ha r_pos)
/-
**NormedSpace.sInter_polar_eq_closedBall** 是 Mathlib 中的一个定理，位于命名空间 `NormedSpace`
。
形式化陈述：sInter_polar_eq_closedBall {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
 [NormedSpace 𝕜 E] {r : Real} (hr : 0 < r) : ⋂₀ (StrongDual.polar 𝕜 '' { F | F.F
inite ∧ F subseteq closedBall (0 : E) r⁻¹ }) = closedBall 0 r
参数：hr : 0 < r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `NormedSpace.polar_closedBall`：polar_closedBall {𝕜 E : Type*} [RCLike 𝕜] 
[NormedAddCommGroup E] [NormedSpace 𝕜 E] {r : Real} (hr : 0 < r) : StrongDual.po
lar 𝕜 (closedBall …
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `StrongDual.polar.eq_1`：∀ (R : Type u_4) [inst : NormedCommRing R] {M : T
ype u_5} [inst_1 : AddCommMonoid M] [inst_2 : TopologicalSpace M]   [inst_3 : _r
oot_.Module…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
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
· 使用定理 `LinearMap.sInter_polar_finite_subset_eq_polar`：sInter_polar_finite_subse
t_eq_polar (s : Set E) : ⋂₀ (B.polar '' { F | F.Finite ∧ F subseteq s }) = B.pol
ar s
-/
theorem sInter_polar_eq_closedBall {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {r : ℝ} (hr : 0 < r) :
    ⋂₀ (StrongDual.polar 𝕜 '' { F | F.Finite ∧ F ⊆ closedBall (0 : E) r⁻¹ }) = closedBall 0 r := by
  conv_rhs => rw [← inv_inv r]
  rw [← polar_closedBall (inv_pos_of_pos hr), StrongDual.polar,
    (topDualPairing 𝕜 E).flip.sInter_polar_finite_subset_eq_polar (closedBall (0 : E) r⁻¹)]

end PolarSets

end NormedSpace

namespace LinearMap

section NormedField

variable {𝕜 E F : Type*}
variable [RCLike 𝕜] [AddCommMonoid E] [AddCommMonoid F]
variable [Module 𝕜 E] [Module 𝕜 F]

variable {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} (s : Set E)

open ComplexOrder in
/-
**LinearMap.polar_AbsConvex** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：polar_AbsConvex : AbsConvex 𝕜 (B.polar s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.polar_eq_biInter_preimage`：polar_eq_biInter_preimage (s : Set 
E) : B.polar s = ⋂ x in s, ((B x) ⁻¹' Metric.closedBall (0 : 𝕜) 1)
· 使用定理 `AbsConvex.iInter₂`：AbsConvex.iInter₂ {ι : Sort*} {κ : ι -> Sort*} {f : f
orall i, κ i -> Set E} (h : forall i j, AbsConvex 𝕜 (f i j)) : AbsConvex 𝕜 (⋂ (i
) (j), …
· 使用定理 `Balanced.mulActionHom_preimage`：Balanced.mulActionHom_preimage [SMul 𝕜 F
] {s : Set F} (hs : Balanced 𝕜 s) (f : E ->[𝕜] F) : Balanced 𝕜 (f ⁻¹' s)
· 使用定理 `balanced_closedBall_zero`：balanced_closedBall_zero : Balanced 𝕜 (Metric.
closedBall (0 : E) r)
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Convex.linear_preimage`：Convex.linear_preimage {s : Set F} (hs : Convex 
𝕜 s) (f : E ->ₗ[𝕜] F) : Convex 𝕜 (f ⁻¹' s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `convex_RCLike_iff_convex_real`：convex_RCLike_iff_convex_real [AddCommMon
oid E] [Module K E] [Module Real E] [IsScalarTower Real K E] {s : Set E} : Conve
x K s ↔ Convex Real…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `convex_closedBall`：convex_closedBall (a : E) (r : Real) : Convex Real (c
losedBall a r)
-/
theorem polar_AbsConvex : AbsConvex 𝕜 (B.polar s) := by
  rw [polar_eq_biInter_preimage]
  exact AbsConvex.iInter₂ fun i hi =>
    ⟨balanced_closedBall_zero.mulActionHom_preimage (f := (B i : (F →ₑ[(RingHom.id 𝕜)] 𝕜))),
      (convex_RCLike_iff_convex_real.mpr (convex_closedBall 0 1)).linear_preimage _⟩

end NormedField

end LinearMap

section Deprecated

variable (𝕜 : Type*) [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

@[deprecated SeparatingDual.eq_zero_of_forall_dual_eq_zero (since := "2026-03-18")]
/-
**NormedSpace.eq_zero_of_forall_dual_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NormedSpace.eq_zero_of_forall_dual_eq_zero {x : E} (h : forall f : StrongD
ual 𝕜 E, f x = 0) : x = 0
参数：h : forall f : StrongDual 𝕜 E, f x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeparatingDual.eq_zero_of_forall_dual_eq_zero`：eq_zero_of_forall_dual_eq
_zero {x : V} (h : forall f : StrongDual R V, f x = 0) : x = 0
· 使用定理 `instSeparatingDual`：∀ {E : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] [i
nst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   SeparatingDual 𝕜 E
-/
theorem NormedSpace.eq_zero_of_forall_dual_eq_zero {x : E}
    (h : ∀ f : StrongDual 𝕜 E, f x = 0) : x = 0 :=
  SeparatingDual.eq_zero_of_forall_dual_eq_zero h

@[deprecated SeparatingDual.eq_zero_iff_forall_dual_eq_zero (since := "2026-03-18")]
/-
**NormedSpace.eq_zero_iff_forall_dual_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NormedSpace.eq_zero_iff_forall_dual_eq_zero (x : E) : x = 0 ↔ forall g : S
trongDual 𝕜 E, g x = 0
参数：x : E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeparatingDual.eq_zero_iff_forall_dual_eq_zero`：eq_zero_iff_forall_dual_
eq_zero (x : V) : x = 0 ↔ forall g : StrongDual R V, g x = 0
· 使用定理 `instSeparatingDual`：∀ {E : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] [i
nst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   SeparatingDual 𝕜 E
-/
theorem NormedSpace.eq_zero_iff_forall_dual_eq_zero (x : E) :
    x = 0 ↔ ∀ g : StrongDual 𝕜 E, g x = 0 :=
  SeparatingDual.eq_zero_iff_forall_dual_eq_zero x

@[deprecated SeparatingDual.eq_iff_forall_dual_eq (since := "2026-03-18")]
/-
**NormedSpace.eq_iff_forall_dual_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NormedSpace.eq_iff_forall_dual_eq {x y : E} : x = y ↔ forall g : StrongDua
l 𝕜 E, g x = g y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeparatingDual.eq_iff_forall_dual_eq`：eq_iff_forall_dual_eq {x y : V} : 
x = y ↔ forall g : StrongDual R V, g x = g y
· 使用定理 `instSeparatingDual`：∀ {E : Type u_1} {𝕜 : Type u_2} [inst : RCLike 𝕜] [i
nst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   SeparatingDual 𝕜 E
-/
theorem NormedSpace.eq_iff_forall_dual_eq {x y : E} :
    x = y ↔ ∀ g : StrongDual 𝕜 E, g x = g y :=
  SeparatingDual.eq_iff_forall_dual_eq

end Deprecated

