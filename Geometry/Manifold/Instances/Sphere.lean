/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.Normed.Module.Ball.Action
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Tactic.Module

/-!
# Manifold structure on the sphere

This file defines stereographic projection from the sphere in an inner product space `E`, and uses
it to put an analytic manifold structure on the sphere.

## Main results

For a unit vector `v` in `E`, the definition `stereographic` gives the stereographic projection
centred at `v`, an open partial homeomorphism from the sphere to `(ℝ ∙ v)ᗮ` (the orthogonal
complement of `v`).

For finite-dimensional `E`, we then construct an analytic manifold instance on the sphere; the
charts here are obtained by composing the open partial homeomorphisms `stereographic` with arbitrary
isometries from `(ℝ ∙ v)ᗮ` to Euclidean space.

We prove two lemmas about `C^n` maps:
* `contMDiff_coe_sphere` states that the coercion map from the sphere into `E` is analytic;
  this is a useful tool for constructing smooth maps *from* the sphere.
* `contMDiff.codRestrict_sphere` states that a map from a manifold into the sphere is
  `C^m` if its lift to a map to `E` is `C^m`; this is a useful tool for constructing `C^m` maps
  *to* the sphere.

As an application we prove `contMDiffNegSphere`, that the antipodal map is analytic.

Finally, we equip the `Circle` (defined in `Analysis.Complex.Circle` to be the sphere in `ℂ`
centred at `0` of radius `1`) with the following structure:
* a charted space with model space `EuclideanSpace ℝ (Fin 1)` (inherited from `Metric.Sphere`)
* an analytic Lie group with model with corners `𝓡 1`

We furthermore show that `Circle.exp` (defined in `Analysis.Complex.Circle` to be the natural
map `fun t ↦ exp (t * I)` from `ℝ` to `Circle`) is analytic.


## Implementation notes

The model space for the charted space instance is `EuclideanSpace ℝ (Fin n)`, where `n` is a
natural number satisfying the typeclass assumption `[Fact (finrank ℝ E = n + 1)]`.  This may seem a
little awkward, but it is designed to circumvent the problem that the literal expression for the
dimension of the model space (up to definitional equality) determines the type.  If one used the
naive expression `EuclideanSpace ℝ (Fin (finrank ℝ E - 1))` for the model space, then the sphere in
`ℂ` would be a manifold with model space `EuclideanSpace ℝ (Fin (2 - 1))` but not with model space
`EuclideanSpace ℝ (Fin 1)`.

## TODO

Relate the stereographic projection to the inversion of the space.
-/

@[expose] public section


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable section

open Metric Module Function

open scoped Manifold ContDiff RealInnerProductSpace

section StereographicProjection

variable (v : E)

/-! ### Construction of the stereographic projection -/


/-- Stereographic projection, forward direction. This is a map from an inner product space `E` to
the orthogonal complement of an element `v` of `E`. It is smooth away from the affine hyperplane
through `v` parallel to the orthogonal complement.  It restricts on the sphere to the stereographic
projection. -/
/-
**stereoToFun** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：stereoToFun (x : E) : (Real ∙ v)ᗮ
参数：x : E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Stereographic projection, forward direction. This is a map from an inner product
 space `E` to
the orthogonal complement of an element `v` of `E`. It is smooth away from the a
ffine hyperplane
through `v` parallel to the orthogonal complement.  It restricts on the sphere t
o the stereographic
projection.
-/
def stereoToFun (x : E) : (ℝ ∙ v)ᗮ :=
  (2 / ((1 : ℝ) - innerSL ℝ v x)) • (ℝ ∙ v)ᗮ.orthogonalProjectionOnto x

variable {v}

@[simp]
/-
**stereoToFun_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：stereoToFun_apply (x : E) : stereoToFun v x = (2 / ((1 : Real) - innerSL R
eal v x)) • (Real ∙ v)ᗮ.orthogonalProjectionOnto x
参数：x : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem stereoToFun_apply (x : E) :
    stereoToFun v x = (2 / ((1 : ℝ) - innerSL ℝ v x)) • (ℝ ∙ v)ᗮ.orthogonalProjectionOnto x :=
  rfl
/-
**contDiffOn_stereoToFun** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffOn_stereoToFun {n : Nat∞ω} : ContDiffOn Real n (stereoToFun v) {x 
: E | innerSL _ v x != (1 : Real)}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffOn.fun_smul`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜]
 {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F :
 Type uF}…
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
· 使用定理 `ContDiffOn.div`：ContDiffOn.div {f g : E -> 𝕜} {n} (hf : ContDiffOn 𝕜 n f
 s) (hg : ContDiffOn 𝕜 n g s) (h₀ : forall x in s, g x != 0) : ContDiffOn 𝕜 n (f
 / g…
· 使用定理 `ContDiff.contDiffOn`：ContDiff.contDiffOn (h : ContDiff 𝕜 n f) : ContDiff
On 𝕜 n f s
· 使用定理 `contDiff_const`：contDiff_const {c : F} : ContDiff 𝕜 n fun _ : E => c
· 使用定理 `ContDiff.sub`：ContDiff.sub {f g : E -> F} (hf : ContDiff 𝕜 n f) (hg : Co
ntDiff 𝕜 n g) : ContDiff 𝕜 n fun x => f x - g x
· 使用定理 `ContinuousLinearMap.contDiff`：ContinuousLinearMap.contDiff (f : E ->L[𝕜]
 F) : ContDiff 𝕜 n f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Submodule.instHasOrthogonalProjectionOrthogonal`：∀ {𝕜 : Type u_1} {E : T
ype u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProduc
tSpace 𝕜 E]   (K : Submodule 𝕜 E) [K.…
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
-/
theorem contDiffOn_stereoToFun {n : ℕ∞ω} :
    ContDiffOn ℝ n (stereoToFun v) {x : E | innerSL _ v x ≠ (1 : ℝ)} := by
  refine ContDiffOn.fun_smul ?_ (ℝ ∙ v)ᗮ.orthogonalProjectionOnto.contDiff.contDiffOn
  refine contDiff_const.contDiffOn.div ?_ ?_
  · exact (contDiff_const.sub (innerSL ℝ v).contDiff).contDiffOn
  · intro x h h'
    exact h (sub_eq_zero.mp h').symm
/-
**continuousOn_stereoToFun** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_stereoToFun : ContinuousOn (stereoToFun v) {x : E | innerSL _
 v x != (1 : Real)}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffOn.continuousOn`：ContDiffOn.continuousOn (h : ContDiffOn 𝕜 n f s
) : ContinuousOn f s
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
· 使用定理 `contDiffOn_stereoToFun`：contDiffOn_stereoToFun {n : Nat∞ω} : ContDiffOn 
Real n (stereoToFun v) {x : E | innerSL _ v x != (1 : Real)}
-/
theorem continuousOn_stereoToFun :
    ContinuousOn (stereoToFun v) {x : E | innerSL _ v x ≠ (1 : ℝ)} :=
  (contDiffOn_stereoToFun (n := 0)).continuousOn

variable (v) in
/-- Auxiliary function for the construction of the reverse direction of the stereographic
projection.  This is a map from the orthogonal complement of a unit vector `v` in an inner product
space `E` to `E`; we will later prove that it takes values in the unit sphere.

For most purposes, use `stereoInvFun`, not `stereoInvFunAux`. -/
/-
**stereoInvFunAux** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：stereoInvFunAux (w : E) : E
参数：w : E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary function for the construction of the reverse direction of the stereogr
aphic
projection.  This is a map from the orthogonal complement of a unit vector `v` i
n an inner product
space `E` to `E`; we will later prove that it takes values in the unit sphere.

For most purposes, use `stereoInvFun`, not `stereoInvFunAux`.
-/
def stereoInvFunAux (w : E) : E :=
  (‖w‖ ^ 2 + 4)⁻¹ • ((4 : ℝ) • w + (‖w‖ ^ 2 - 4) • v)

@[simp]
/-
**stereoInvFunAux_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：stereoInvFunAux_apply (w : E) : stereoInvFunAux v w = (‖w‖ ^ 2 + 4)⁻¹ • ((
4 : Real) • w + (‖w‖ ^ 2 - 4) • v)
参数：w : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem stereoInvFunAux_apply (w : E) :
    stereoInvFunAux v w = (‖w‖ ^ 2 + 4)⁻¹ • ((4 : ℝ) • w + (‖w‖ ^ 2 - 4) • v) :=
  rfl
/-
**stereoInvFunAux_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：stereoInvFunAux_mem (hv : ‖v‖ = 1) {w : E} (hw : w in (Real ∙ v)ᗮ) : stere
oInvFunAux v w in sphere (0 : E) 1
参数：hv : ‖v‖ = 1；hw : w in (Real ∙ v)ᗮ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Right.add_pos_of_nonneg_of_pos`：∀ {α : Type u_1} [inst : AddZeroClass α]
 [inst_1 : Preorder α] [AddRightMono α] {a b : α}, 0 ≤ a → 0 < b → 0 < a + b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Even.pow_nonneg`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : LinearOr
der R] [IsOrderedRing R] [ExistsAddOfLE R] {n : ℕ},   Even n → ∀ (a : R), 0 ≤ a 
^ n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用引理 `even_two_mul`：even_two_mul (a : α) : Even (2 * a)
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `norm_add_sq_real`：norm_add_sq_real (x y : F) : ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2
 * ⟪x, y⟫_Real + ‖y‖ ^ 2
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `Real.norm_ofNat`：∀ (n : ℕ) [inst : n.AtLeastTwo], ‖OfNat.ofNat n‖ = OfNa
t.ofNat n
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用定理 `inner_smul_left`：inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪
x, y⟫
· 使用定理 `conj_trivial`：∀ {R : Type u} [inst : CommSemiring R] [inst_1 : StarRing 
R] [TrivialStar R] (a : R), (starRingEnd R) a = a
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `Submodule.mem_orthogonal_singleton_iff_inner_left`：mem_orthogonal_single
ton_iff_inner_left {u v : E} : v in (𝕜 ∙ u)ᗮ ↔ ⟪v, u⟫ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `sq_abs`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] (a : α
), |a| ^ 2 = a ^ 2
（共 86 条，此处仅展示前 30 条）
-/
theorem stereoInvFunAux_mem (hv : ‖v‖ = 1) {w : E} (hw : w ∈ (ℝ ∙ v)ᗮ) :
    stereoInvFunAux v w ∈ sphere (0 : E) 1 := by
  have h₁ : (0 : ℝ) < ‖w‖ ^ 2 + 4 := by positivity
  suffices ‖(4 : ℝ) • w + (‖w‖ ^ 2 - 4) • v‖ = ‖w‖ ^ 2 + 4 by
    simp only [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv, this,
      abs_of_pos h₁, stereoInvFunAux_apply, inv_mul_cancel₀ h₁.ne']
  suffices ‖(4 : ℝ) • w + (‖w‖ ^ 2 - 4) • v‖ ^ 2 = (‖w‖ ^ 2 + 4) ^ 2 by
    simpa only [sq_eq_sq_iff_abs_eq_abs, abs_norm, abs_of_pos h₁] using this
  rw [Submodule.mem_orthogonal_singleton_iff_inner_left] at hw
  simp [norm_add_sq_real, norm_smul, inner_smul_left, inner_smul_right, hw, mul_pow,
    Real.norm_eq_abs, hv]
  ring
/-
**hasFDerivAt_stereoInvFunAux** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_stereoInvFunAux (v : E) : HasFDerivAt (stereoInvFunAux v) (Con
tinuousLinearMap.id Real E) 0
参数：v : E。
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
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
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
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HasStrictFDerivAt.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 
E] [inst_3 : Topolo…
· 使用定理 `hasStrictFDerivAt_norm_sq`：hasStrictFDerivAt_norm_sq (x : F) : HasStrict
FDerivAt (fun x => ‖x‖ ^ 2) (2 • (innerSL Real x)) x
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
（共 63 条，此处仅展示前 30 条）
-/
theorem hasFDerivAt_stereoInvFunAux (v : E) :
    HasFDerivAt (stereoInvFunAux v) (ContinuousLinearMap.id ℝ E) 0 := by
  have h₀ : HasFDerivAt (fun w : E => ‖w‖ ^ 2) (0 : StrongDual ℝ E) 0 := by
    convert! (hasStrictFDerivAt_norm_sq (0 : E)).hasFDerivAt
    simp only [map_zero, smul_zero]
  have h₁ : HasFDerivAt (fun w : E => (‖w‖ ^ 2 + 4)⁻¹) (0 : StrongDual ℝ E) 0 := by
    convert! (hasFDerivAt_inv _).comp _ (h₀.add (hasFDerivAt_const 4 0)) <;> simp
  have h₂ : HasFDerivAt (fun w => (4 : ℝ) • w + (‖w‖ ^ 2 - 4) • v)
      ((4 : ℝ) • ContinuousLinearMap.id ℝ E) 0 := by
    convert!
      ((hasFDerivAt_const (4 : ℝ) 0).smul (hasFDerivAt_id 0)).add
        ((h₀.sub (hasFDerivAt_const (4 : ℝ) 0)).smul (hasFDerivAt_const v 0)) using 1
    ext w
    simp
  convert! h₁.smul h₂ using 1
  ext w
  simp
/-
**hasFDerivAt_stereoInvFunAux_comp_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_stereoInvFunAux_comp_coe (v : E) : HasFDerivAt (stereoInvFunAu
x v ∘ ((↑) : (Real ∙ v)ᗮ -> E)) (Real ∙ v)ᗮ.subtypeL 0
参数：v : E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasFDerivAt_stereoInvFunAux`：hasFDerivAt_stereoInvFunAux (v : E) : HasFD
erivAt (stereoInvFunAux v) (ContinuousLinearMap.id Real E) 0
· 使用定理 `HasFDerivAt.comp`：HasFDerivAt.comp {g : F -> G} {g' : F ->L[𝕜] G} (hg : 
HasFDerivAt g g' (f x)) (hf : HasFDerivAt f f' x) : HasFDerivAt (g ∘ f) (g'.comp
 f') x
· 使用定理 `ContinuousLinearMap.hasFDerivAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 
𝕜 E] [inst_3 : Topolo…
-/
theorem hasFDerivAt_stereoInvFunAux_comp_coe (v : E) :
    HasFDerivAt (stereoInvFunAux v ∘ ((↑) : (ℝ ∙ v)ᗮ → E)) (ℝ ∙ v)ᗮ.subtypeL 0 := by
  have : HasFDerivAt (stereoInvFunAux v) (ContinuousLinearMap.id ℝ E) ((ℝ ∙ v)ᗮ.subtypeL 0) :=
    hasFDerivAt_stereoInvFunAux v
  refine this.comp (0 : (ℝ ∙ v)ᗮ) (by apply ContinuousLinearMap.hasFDerivAt)
/-
**contDiff_stereoInvFunAux** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiff_stereoInvFunAux {m : Nat∞ω} : ContDiff Real m (stereoInvFunAux v)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contDiff_norm_sq`：contDiff_norm_sq : ContDiff Real n fun x : E => ‖x‖ ^ 
2
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ContDiff.inv`：ContDiff.inv {f : E -> 𝕜'} (hf : ContDiff 𝕜 n f) (h : fora
ll x, f x != 0) : ContDiff 𝕜 n f⁻¹
· 使用定理 `ContDiff.add`：ContDiff.add {f g : E -> F} (hf : ContDiff 𝕜 n f) (hg : Co
ntDiff 𝕜 n g) : ContDiff 𝕜 n fun x => f x + g x
· 使用定理 `contDiff_const`：contDiff_const {c : F} : ContDiff 𝕜 n fun _ : E => c
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Meta.NormNum.isInt_mul`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HMul.hMul →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
（共 72 条，此处仅展示前 30 条）
-/
theorem contDiff_stereoInvFunAux {m : ℕ∞ω} : ContDiff ℝ m (stereoInvFunAux v) := by
  have h₀ : ContDiff ℝ ω fun w : E => ‖w‖ ^ 2 := contDiff_norm_sq ℝ
  have h₁ : ContDiff ℝ ω fun w : E => (‖w‖ ^ 2 + 4)⁻¹ := by
    refine (h₀.add contDiff_const).inv ?_
    intro x
    nlinarith
  have h₂ : ContDiff ℝ ω fun w => (4 : ℝ) • w + (‖w‖ ^ 2 - 4) • v := by
    refine (contDiff_const.smul contDiff_id).add ?_
    exact (h₀.sub contDiff_const).smul contDiff_const
  exact (h₁.smul h₂).of_le le_top

/-- Stereographic projection, reverse direction.  This is a map from the orthogonal complement of a
unit vector `v` in an inner product space `E` to the unit sphere in `E`. -/
/-
**stereoInvFun** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：stereoInvFun (hv : ‖v‖ = 1) (w : (Real ∙ v)ᗮ) : sphere (0 : E) 1
参数：hv : ‖v‖ = 1；w : (Real ∙ v)ᗮ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Stereographic projection, reverse direction.  This is a map from the orthogonal 
complement of a
unit vector `v` in an inner product space `E` to the unit sphere in `E`.
-/
def stereoInvFun (hv : ‖v‖ = 1) (w : (ℝ ∙ v)ᗮ) : sphere (0 : E) 1 :=
  ⟨stereoInvFunAux v (w : E), stereoInvFunAux_mem hv w.2⟩

@[simp]
/-
**stereoInvFun_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：stereoInvFun_apply (hv : ‖v‖ = 1) (w : (Real ∙ v)ᗮ) : (stereoInvFun hv w :
 E) = (‖w‖ ^ 2 + 4)⁻¹ • ((4 : Real) • w + (‖w‖ ^ 2 - 4) • v)
参数：hv : ‖v‖ = 1；w : (Real ∙ v)ᗮ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem stereoInvFun_apply (hv : ‖v‖ = 1) (w : (ℝ ∙ v)ᗮ) :
    (stereoInvFun hv w : E) = (‖w‖ ^ 2 + 4)⁻¹ • ((4 : ℝ) • w + (‖w‖ ^ 2 - 4) • v) :=
  rfl

open scoped InnerProductSpace in
/-
**stereoInvFun_ne_north_pole** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：stereoInvFun_ne_north_pole (hv : ‖v‖ = 1) (w : (Real ∙ v)ᗮ) : stereoInvFun
 hv w != (⟨v, by simp [hv]⟩ : sphere (0 : E) 1)
参数：hv : ‖v‖ = 1；w : (Real ∙ v)ᗮ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Subtype.coe_ne_coe`：coe_ne_coe {a b : Subtype p} : (a : α) != b ↔ a != b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_lt_one_iff_real_of_norm_eq_one`：inner_lt_one_iff_real_of_norm_eq_o
ne {x y : F} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : ⟪x, y⟫_Real < 1 ↔ x != y
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `stereoInvFunAux_mem`：stereoInvFunAux_mem (hv : ‖v‖ = 1) {w : E} (hw : w 
in (Real ∙ v)ᗮ) : stereoInvFunAux v w in sphere (0 : E) 1
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Submodule.mem_orthogonal_singleton_iff_inner_right`：mem_orthogonal_singl
eton_iff_inner_right {u v : E} : v in (𝕜 ∙ u)ᗮ ↔ ⟪u, v⟫ = 0
· 使用引理 `inv_mul_lt_iff₀'`：inv_mul_lt_iff₀' (hc : 0 < c) : c⁻¹ * b < a ↔ b < a * 
c
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Right.add_pos_of_nonneg_of_pos`：∀ {α : Type u_1} [inst : AddZeroClass α]
 [inst_1 : Preorder α] [AddRightMono α] {a b : α}, 0 ≤ a → 0 < b → 0 < a + b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Even.pow_nonneg`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : LinearOr
der R] [IsOrderedRing R] [ExistsAddOfLE R] {n : ℕ},   Even n → ∀ (a : R), 0 ≤ a 
^ n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用引理 `even_two_mul`：even_two_mul (a : α) : Even (2 * a)
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
（共 91 条，此处仅展示前 30 条）
-/
theorem stereoInvFun_ne_north_pole (hv : ‖v‖ = 1) (w : (ℝ ∙ v)ᗮ) :
    stereoInvFun hv w ≠ (⟨v, by simp [hv]⟩ : sphere (0 : E) 1) := by
  refine Subtype.coe_ne_coe.1 ?_
  rw [← inner_lt_one_iff_real_of_norm_eq_one _ hv]
  · have hw : ⟪v, w⟫_ℝ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.2
    have hw' : (‖(w : E)‖ ^ 2 + 4)⁻¹ * (‖(w : E)‖ ^ 2 - 4) < 1 := by
      rw [inv_mul_lt_iff₀']
      · linarith
      positivity
    simpa [real_inner_comm, inner_add_right, inner_smul_right, real_inner_self_eq_norm_mul_norm, hw,
      hv] using hw'
  · simpa using stereoInvFunAux_mem hv w.2
/-
**continuous_stereoInvFun** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_stereoInvFun (hv : ‖v‖ = 1) : Continuous (stereoInvFun hv)
参数：hv : ‖v‖ = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_induced_rng`：continuous_induced_rng {g : γ -> α} {t₂ : Topolo
gicalSpace β} {t₁ : TopologicalSpace γ} : Continuous[t₁, induced f t₂] g ↔ Conti
nuous[t₁, t₂…
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `ContDiff.continuous`：ContDiff.continuous (h : ContDiff 𝕜 n f) : Continuo
us f
· 使用定理 `contDiff_stereoInvFunAux`：contDiff_stereoInvFunAux {m : Nat∞ω} : ContDif
f Real m (stereoInvFunAux v)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
-/
theorem continuous_stereoInvFun (hv : ‖v‖ = 1) : Continuous (stereoInvFun hv) :=
  continuous_induced_rng.2
    ((contDiff_stereoInvFunAux (m := 0)).continuous.comp continuous_subtype_val)

open scoped InnerProductSpace in
attribute [-simp] AddSubgroupClass.coe_norm Submodule.coe_norm in
/-
**stereo_left_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：stereo_left_inv (hv : ‖v‖ = 1) {x : sphere (0 : E) 1} (hx : (x : E) != v) 
: stereoInvFun hv (stereoToFun v x) = x
参数：hv : ‖v‖ = 1；0 : E；hx : (x : E) != v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
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
· 使用定理 `Submodule.instHasOrthogonalProjectionOrthogonal`：∀ {𝕜 : Type u_1} {E : T
ype u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProduc
tSpace 𝕜 E]   (K : Submodule 𝕜 E) [K.…
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.starProjection_add_starProjection_orthogonal`：starProjection_a
dd_starProjection_orthogonal [K.HasOrthogonalProjection] (w : E) : K.starProject
ion w + Kᗮ.starProjection w = w
· 使用定理 `Submodule.starProjection_unit_singleton`：starProjection_unit_singleton {
v : E} (hv : ‖v‖ = 1) (w : E) : (𝕜 ∙ v).starProjection w = ⟪v, w⟫ • v
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_orthogonal_singleton_iff_inner_right`：mem_orthogonal_singl
eton_iff_inner_right {u v : E} : v in (𝕜 ∙ u)ᗮ ↔ ⟪u, v⟫ = 0
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inner_smul_left`：inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪
x, y⟫
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
（共 178 条，此处仅展示前 30 条）
-/
theorem stereo_left_inv (hv : ‖v‖ = 1) {x : sphere (0 : E) 1} (hx : (x : E) ≠ v) :
    stereoInvFun hv (stereoToFun v x) = x := by
  ext
  simp only [stereoToFun_apply, stereoInvFun_apply, smul_add]
  -- name two frequently-occurring quantities and write down their basic properties
  set a : ℝ := innerSL _ v x
  set y := (ℝ ∙ v)ᗮ.orthogonalProjectionOnto x
  have split : ↑x = a • v + ↑y := by
    rw [← ((ℝ ∙ v).starProjection_add_starProjection_orthogonal x),
      Submodule.starProjection_unit_singleton ℝ hv x]
    rfl
  have hvy : ⟪v, y⟫_ℝ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp y.2
  have pythag : 1 = a ^ 2 + ‖y‖ ^ 2 := by
    have hvy' : ⟪a • v, y⟫_ℝ = 0 := by simp only [inner_smul_left, hvy, mul_zero]
    convert! norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hvy' using 2
    · simp [← split]
    · simp [norm_smul, hv, ← sq, sq_abs]
    · exact sq _
  -- a fact which will be helpful for clearing denominators in the main calculation
  have ha : 0 < 1 - a := by
    have : a < 1 := (inner_lt_one_iff_real_of_norm_eq_one hv (by simp)).mpr hx.symm
    linarith
  rw [split, Submodule.coe_smul_of_tower]
  simp only [norm_smul, norm_div, Real.norm_eq_abs, abs_of_nonneg ha.le]
  match_scalars
  · field_simp
    linear_combination 4 * pythag
  · field_simp
    linear_combination 4 * (a - 1) * pythag
/-
**stereo_right_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：stereo_right_inv (hv : ‖v‖ = 1) (w : (Real ∙ v)ᗮ) : stereoToFun v (stereoI
nvFun hv w) = w
参数：hv : ‖v‖ = 1；w : (Real ∙ v)ᗮ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Submodule.orthogonalProjectionOnto_mem_subspace_eq_self`：orthogonalProje
ctionOnto_mem_subspace_eq_self (v : K) : K.orthogonalProjectionOnto v = v
· 使用定理 `Submodule.instHasOrthogonalProjectionOrthogonal`：∀ {𝕜 : Type u_1} {E : T
ype u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProduc
tSpace 𝕜 E]   (K : Submodule 𝕜 E) [K.…
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用定理 `Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zer
o`：orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero (v : E) : (𝕜 
∙ v)ᗮ.orthogonalProjectionOnto v = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_orthogonal_singleton_iff_inner_right`：mem_orthogonal_singl
eton_iff_inner_right {u v : E} : v in (𝕜 ∙ u)ᗮ ↔ ⟪u, v⟫ = 0
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval`：add_eq_eval {R₁ R₂ : Type*} [AddCo
mmMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂] 
[Module R₂ M] {l₁ l₂ l : N…
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
· 使用定理 `Mathlib.Tactic.Module.NF.zero_eq_eval`：zero_eq_eval [AddMonoid M] : (0:M
) = NF.eval (R
（共 99 条，此处仅展示前 30 条）
-/
theorem stereo_right_inv (hv : ‖v‖ = 1) (w : (ℝ ∙ v)ᗮ) : stereoToFun v (stereoInvFun hv w) = w := by
  simp only [stereoToFun, stereoInvFun, stereoInvFunAux, smul_add, map_add, map_smul,
    innerSL_apply_apply, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
  have h₁ : (ℝ ∙ v)ᗮ.orthogonalProjectionOnto v = 0 :=
    Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero v
  have h₂ : ⟪v, w⟫ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.2
  have h₃ : ⟪v, v⟫ = 1 := by simp [hv]
  rw [h₁, h₂, h₃]
  match_scalars
  simp [field]
  ring

/-- Stereographic projection from the unit sphere in `E`, centred at a unit vector `v` in `E`;
this is the version as an open partial homeomorphism. -/
/-
**stereographic** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：stereographic (hv : ‖v‖ = 1) : OpenPartialHomeomorph (sphere (0 : E) 1) (R
eal ∙ v)ᗮ where toFun
参数：hv : ‖v‖ = 1。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `stereo_right_inv`：stereo_right_inv (hv : ‖v‖ = 1) (w : (Real ∙ v)ᗮ) : st
ereoToFun v (stereoInvFun hv w) = w

--- 原说明 ---
Stereographic projection from the unit sphere in `E`, centred at a unit vector `
v` in `E`;
this is the version as an open partial homeomorphism.
-/
def stereographic (hv : ‖v‖ = 1) : OpenPartialHomeomorph (sphere (0 : E) 1) (ℝ ∙ v)ᗮ where
  toFun := stereoToFun v ∘ (↑)
  invFun := stereoInvFun hv
  source := {⟨v, by simp [hv]⟩}ᶜ
  target := Set.univ
  map_source' := by simp
  map_target' {w} _ := fun h => (stereoInvFun_ne_north_pole hv w) (Set.eq_of_mem_singleton h)
  left_inv' x hx := stereo_left_inv hv fun h => hx (by
    rw [← h] at hv
    apply Subtype.ext
    dsimp
    exact h)
  right_inv' w _ := stereo_right_inv hv w
  open_source := isOpen_compl_singleton
  open_target := isOpen_univ
  continuousOn_toFun :=
    continuousOn_stereoToFun.comp continuous_subtype_val.continuousOn fun w h => by
      dsimp
      exact
        h ∘ Subtype.ext ∘ Eq.symm ∘ (inner_eq_one_iff_of_norm_eq_one hv (by simp)).mp
  continuousOn_invFun := (continuous_stereoInvFun hv).continuousOn
/-
**stereographic_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：stereographic_apply (hv : ‖v‖ = 1) (x : sphere (0 : E) 1) : stereographic 
hv x = (2 / ((1 : Real) - ⟪v, x⟫)) • (Real ∙ v)ᗮ.orthogonalProjectionOnto x
参数：hv : ‖v‖ = 1；x : sphere (0 : E) 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem stereographic_apply (hv : ‖v‖ = 1) (x : sphere (0 : E) 1) :
    stereographic hv x = (2 / ((1 : ℝ) - ⟪v, x⟫)) • (ℝ ∙ v)ᗮ.orthogonalProjectionOnto x :=
  rfl

@[simp]
/-
**stereographic_source** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：stereographic_source (hv : ‖v‖ = 1) : (stereographic hv).source = {⟨v, by 
simp [hv]⟩}ᶜ
参数：hv : ‖v‖ = 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem stereographic_source (hv : ‖v‖ = 1) : (stereographic hv).source = {⟨v, by simp [hv]⟩}ᶜ :=
  rfl

@[simp]
/-
**stereographic_target** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：stereographic_target (hv : ‖v‖ = 1) : (stereographic hv).target = Set.univ
参数：hv : ‖v‖ = 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem stereographic_target (hv : ‖v‖ = 1) : (stereographic hv).target = Set.univ :=
  rfl

@[simp]
/-
**stereographic_apply_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：stereographic_apply_neg (v : sphere (0 : E) 1) : stereographic (norm_eq_of
_mem_sphere v) (-v) = 0
参数：v : sphere (0 : E) 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `norm_eq_of_mem_sphere`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] {r
 : ℝ} (x : ↑(Metric.sphere 0 r)), ‖↑x‖ = r
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Submodule.instHasOrthogonalProjectionOrthogonal`：∀ {𝕜 : Type u_1} {E : T
ype u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProduc
tSpace 𝕜 E]   (K : Submodule 𝕜 E) [K.…
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `inner_neg_right`：inner_neg_right (x y : E) : ⟪x, -y⟫ = -⟪x, y⟫
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
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
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Submodule.orthogonal_orthogonal`：orthogonal_orthogonal [K.HasOrthogonalP
rojection] : Kᗮᗮ = K
-/
theorem stereographic_apply_neg (v : sphere (0 : E) 1) :
    stereographic (norm_eq_of_mem_sphere v) (-v) = 0 := by
  simp [stereographic_apply]

@[simp]
/-
**stereographic_neg_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：stereographic_neg_apply (v : sphere (0 : E) 1) : stereographic (norm_eq_of
_mem_sphere (-v)) v = 0
参数：v : sphere (0 : E) 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `norm_eq_of_mem_sphere`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] {r
 : ℝ} (x : ↑(Metric.sphere 0 r)), ‖↑x‖ = r
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `stereographic_apply_neg`：stereographic_apply_neg (v : sphere (0 : E) 1) 
: stereographic (norm_eq_of_mem_sphere v) (-v) = 0
-/
theorem stereographic_neg_apply (v : sphere (0 : E) 1) :
    stereographic (norm_eq_of_mem_sphere (-v)) v = 0 := by
  convert! stereographic_apply_neg (-v)
  ext1
  simp
/-
**surjective_stereographic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：surjective_stereographic (hv : ‖v‖ = 1) : Surjective (stereographic hv)
参数：hv : ‖v‖ = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PartialEquiv.surjective_of_target_eq_univ`：surjective_of_target_eq_univ 
(h : e.target = univ) : Surjective e
-/
theorem surjective_stereographic (hv : ‖v‖ = 1) :
    Surjective (stereographic hv) :=
  (stereographic hv).surjective_of_target_eq_univ rfl

@[simp]
/-
**range_stereographic_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：range_stereographic_symm (hv : ‖v‖ = 1) (hv' : v in sphere 0 1
参数：hv : ‖v‖ = 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `OpenPartialHomeomorph.map_target`：map_target {x : Y} (h : x in e.target)
 : e.symm x in e.source
· 使用定理 `PartialEquiv.target_subset_range`：target_subset_range : e.target subsete
q range e
-/
theorem range_stereographic_symm (hv : ‖v‖ = 1) (hv' : v ∈ sphere 0 1 := by simpa) :
    Set.range (stereographic hv).symm = {⟨v, hv'⟩}ᶜ := by
  refine le_antisymm ?_ (stereographic hv).symm.target_subset_range
  rintro x ⟨y, rfl⟩
  suffices y ∈ (stereographic hv).target from (fun _ ↦ (stereographic hv).map_target) y this
  simp
/-
**isOpenEmbedding_stereographic_symm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isOpenEmbedding_stereographic_symm (hv : ‖v‖ = 1) : Topology.IsOpenEmbeddi
ng (stereographic hv).symm
参数：hv : ‖v‖ = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.isOpenEmbedding`：isOpenEmbedding (h : e.source = S
et.univ) : IsOpenEmbedding e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isOpenEmbedding_stereographic_symm (hv : ‖v‖ = 1) :
    Topology.IsOpenEmbedding (stereographic hv).symm :=
  (stereographic hv).symm.isOpenEmbedding (by simp)

end StereographicProjection

section ChartedSpace

/-!
### Charted space structure on the sphere

In this section we construct a charted space structure on the unit sphere in a finite-dimensional
real inner product space `E`; that is, we show that it is locally homeomorphic to the Euclidean
space of dimension one less than `E`.

The restriction to finite dimension is for convenience.  The most natural `ChartedSpace`
structure for the sphere uses the stereographic projection from the antipodes of a point as the
canonical chart at this point.  However, the codomain of the stereographic projection constructed
in the previous section is `(ℝ ∙ v)ᗮ`, the orthogonal complement of the vector `v` in `E` which is
the "north pole" of the projection, so a priori these charts all have different codomains.

So it is necessary to prove that these codomains are all continuously linearly equivalent to a
fixed normed space.  This could be proved in general by a simple case of Gram-Schmidt
orthogonalization, but in the finite-dimensional case it follows more easily by dimension-counting.
-/

/-- Variant of the stereographic projection, for the sphere in an `n + 1`-dimensional inner product
space `E`.  This version has codomain the Euclidean space of dimension `n`, and is obtained by
composing the original stereographic projection (`stereographic`) with an arbitrary linear isometry
from `(ℝ ∙ v)ᗮ` to the Euclidean space. -/
/-
**stereographic'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：stereographic' (n : Nat) [Fact (finrank Real E = n + 1)] (v : sphere (0 : 
E) 1) : OpenPartialHomeomorph (sphere (0 : E) 1) (EuclideanSpace Real (Fin n))
参数：n : Nat；finrank Real E = n + 1；v : sphere (0 : E) 1。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)

--- 原说明 ---
Variant of the stereographic projection, for the sphere in an `n + 1`-dimensiona
l inner product
space `E`.  This version has codomain the Euclidean space of dimension `n`, and 
is obtained by
composing the original stereographic projection (`stereographic`) with an arbitr
ary linear isometry
from `(ℝ ∙ v)ᗮ` to the Euclidean space.
-/
def stereographic' (n : ℕ) [Fact (finrank ℝ E = n + 1)] (v : sphere (0 : E) 1) :
    OpenPartialHomeomorph (sphere (0 : E) 1) (EuclideanSpace ℝ (Fin n)) :=
  stereographic (norm_eq_of_mem_sphere v) ≫ₕ
    (OrthonormalBasis.fromOrthogonalSpanSingleton n
            (ne_zero_of_mem_unit_sphere v)).repr.toHomeomorph.toOpenPartialHomeomorph

@[simp]
/-
**stereographic'_source** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace
 ℝ E] {n : ℕ}   [inst_2 : Fact (Module.finrank ℝ E = n + 1)] (v : ↑(Metric.spher
e 0 1)), (stereographic' n v).source = {v}ᶜ
参数：Module.finrank ℝ E = n + 1；v : ↑(Metric.sphere 0 1)；stereographic' n v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `Homeomorph.toOpenPartialHomeomorph_source`：∀ {X : Type u_1} {Y : Type u_
3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] (e : X ≃ₜ Y),   e.t
oOpenPartialHomeomorph.source =…
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem stereographic'_source {n : ℕ} [Fact (finrank ℝ E = n + 1)] (v : sphere (0 : E) 1) :
    (stereographic' n v).source = {v}ᶜ := by simp [stereographic']

@[simp]
/-
**stereographic'_target** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace
 ℝ E] {n : ℕ}   [inst_2 : Fact (Module.finrank ℝ E = n + 1)] (v : ↑(Metric.spher
e 0 1)), (stereographic' n v).target = Set.univ
参数：Module.finrank ℝ E = n + 1；v : ↑(Metric.sphere 0 1)；stereographic' n v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Homeomorph.toOpenPartialHomeomorph_target`：∀ {X : Type u_1} {Y : Type u_
3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] (e : X ≃ₜ Y),   e.t
oOpenPartialHomeomorph.target =…
· 使用定理 `Homeomorph.toOpenPartialHomeomorph_symm_apply`：∀ {X : Type u_1} {Y : Typ
e u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] (e : X ≃ₜ Y),  
 ↑e.toOpenPartialHomeomorph.symm = …
· 使用定理 `Set.inter_self`：inter_self (a : Set α) : a inter a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem stereographic'_target {n : ℕ} [Fact (finrank ℝ E = n + 1)] (v : sphere (0 : E) 1) :
    (stereographic' n v).target = Set.univ := by simp [stereographic']

/-- The unit sphere in an `n + 1`-dimensional inner product space `E` is a charted space
modelled on the Euclidean space of dimension `n`. -/
/-
**EuclideanSpace.instChartedSpaceSphere** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：EuclideanSpace.instChartedSpaceSphere {n : Nat} [Fact (finrank Real E = n 
+ 1)] : ChartedSpace (EuclideanSpace Real (Fin n)) (sphere (0 : E) 1) where atla
s
参数：finrank Real E = n + 1。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unit sphere in an `n + 1`-dimensional inner product space `E` is a charted s
pace
modelled on the Euclidean space of dimension `n`.
-/
instance EuclideanSpace.instChartedSpaceSphere {n : ℕ} [Fact (finrank ℝ E = n + 1)] :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) (sphere (0 : E) 1) where
  atlas := {f | ∃ v : sphere (0 : E) 1, f = stereographic' n v}
  chartAt v := stereographic' n (-v)
  mem_chart_source v := by simpa using ne_neg_of_mem_unit_sphere ℝ v
  chart_mem_atlas v := ⟨-v, rfl⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℕ) :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  have := Fact.mk (@finrank_euclideanSpace_fin ℝ _ (n + 1))
  EuclideanSpace.instChartedSpaceSphere

end ChartedSpace

section ContMDiffManifold

open scoped InnerProductSpace

/-
**sphere_ext_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sphere_ext_iff (u v : sphere (0 : E) 1) : u = v ↔ ⟪(u : E), v⟫_Real = 1
参数：u v : sphere (0 : E) 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_eq_of_mem_sphere`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] {r
 : ℝ} (x : ↑(Metric.sphere 0 r)), ‖↑x‖ = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sphere_ext_iff (u v : sphere (0 : E) 1) : u = v ↔ ⟪(u : E), v⟫_ℝ = 1 := by
  simp [Subtype.ext_iff, inner_eq_one_iff_of_norm_eq_one]
/-
**stereographic'_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : InnerProductSpace
 ℝ E] {n : ℕ}   [inst_2 : Fact (Module.finrank ℝ E = n + 1)] (v : ↑(Metric.spher
e 0 1)) (x : EuclideanSpace ℝ (Fin n)),   ↑(↑(stereographic' n v).symm x) =     
have U := (OrthonormalBasis.fromOrthogonalSpanSingleton n ⋯).repr;     (‖↑(U.sym
m x)‖ ^ 2 + 4)⁻¹ • 4 • ↑(U.symm x) + (‖↑(U.symm x)‖ ^ 2 + 4)⁻¹ • (‖↑(U.symm x)‖ 
^ 2 - 4) • ↑v
参数：Module.finrank ℝ E = n + 1；v : ↑(Metric.sphere 0 1)；x : EuclideanSpace ℝ (Fin
 n)；↑(stereographic' n v).symm x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `ne_zero_of_mem_unit_sphere`：∀ {E : Type u_5} [inst : SeminormedAddGroup 
E] (x : ↑(Metric.sphere 0 1)), ↑x ≠ 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `stereo_right_inv`：stereo_right_inv (hv : ‖v‖ = 1) (w : (Real ∙ v)ᗮ) : st
ereoToFun v (stereoInvFun hv w) = w
· 使用定理 `PartialEquiv.mk.congr_simp`：∀ {α : Type u_5} {β : Type u_6} (toFun toFun
_1 : α → β) (e_toFun : toFun = toFun_1) (invFun invFun_1 : β → α)   (e_invFun : 
invFun = invFun_…
· 使用定理 `PartialHomeomorph.mk.congr_simp`：∀ {X : Type u_7} {Y : Type u_8} [inst :
 TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (toPartialEquiv toPartialEq
uiv_1 : PartialEquiv …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `OpenPartialHomeomorph.mk.congr_simp`：∀ {X : Type u_7} {Y : Type u_8} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (toPartialHomeomorph to
PartialHomeomorph_1 : Par…
· 使用定理 `Homeomorph.toOpenPartialHomeomorph_symm_apply`：∀ {X : Type u_1} {Y : Typ
e u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] (e : X ≃ₜ Y),  
 ↑e.toOpenPartialHomeomorph.symm = …
· 使用定理 `norm_map`：∀ {𝓕 : Type u_1} {E : Type u_2} {F : Type u_3} [inst : Seminor
medAddGroup E] [inst_1 : SeminormedAddGroup F]   [inst_2 : FunLike 𝓕 E F] [Iso…
· 使用定理 `SemilinearIsometryClass.toIsometryClass`：∀ {R : Type u_1} {R₂ : Type u_2
} {E : Type u_5} {E₂ : Type u_6} {𝓕 : Type u_10} [inst : Semiring R]   [inst_1 :
 Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `SemilinearIsometryEquivClass.toSemilinearIsometryClass`：∀ {R : Type u_1}
 {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} (𝓕 : Type u_10) [inst : Semiring
 R]   [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem stereographic'_symm_apply {n : ℕ} [Fact (finrank ℝ E = n + 1)] (v : sphere (0 : E) 1)
    (x : EuclideanSpace ℝ (Fin n)) :
    ((stereographic' n v).symm x : E) =
      let U : (ℝ ∙ (v : E))ᗮ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
        (OrthonormalBasis.fromOrthogonalSpanSingleton n (ne_zero_of_mem_unit_sphere v)).repr
      (‖(U.symm x : E)‖ ^ 2 + 4)⁻¹ • (4 : ℝ) • (U.symm x : E) +
        (‖(U.symm x : E)‖ ^ 2 + 4)⁻¹ • (‖(U.symm x : E)‖ ^ 2 - 4) • v.val := by
  simp [stereographic, stereographic', ← Submodule.coe_norm]

/-! ### Analytic manifold structure on the sphere -/

/-- The unit sphere in an `n + 1`-dimensional inner product space `E` is an analytic manifold,
modelled on the Euclidean space of dimension `n`. -/
/-
**EuclideanSpace.instIsManifoldSphere** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：EuclideanSpace.instIsManifoldSphere {n : Nat} [Fact (finrank Real E = n + 
1)] : IsManifold (𝓡 n) ω (sphere (0 : E) 1)
参数：finrank Real E = n + 1。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `isManifold_of_contDiffOn`：isManifold_of_contDiffOn {𝕜 : Type*} [Nontrivi
allyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Typ
e*} [Topologic…
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `ne_zero_of_mem_unit_sphere`：∀ {E : Type u_5} [inst : SeminormedAddGroup 
E] (x : ↑(Metric.sphere 0 1)), ↑x ≠ 0
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
· 使用定理 `ContDiff.comp_contDiffOn`：ContDiff.comp_contDiffOn {s : Set E} {g : F ->
 G} {f : E -> F} (hg : ContDiff 𝕜 n g) (hf : ContDiffOn 𝕜 n f s) : ContDiffOn 𝕜 
n (g ∘ f) s
· 使用定理 `LinearIsometryEquiv.contDiff`：LinearIsometryEquiv.contDiff (f : E ≃ₗᵢ[𝕜]
 F) : ContDiff 𝕜 n f
· 使用定理 `contDiffOn_stereoToFun`：contDiffOn_stereoToFun {n : Nat∞ω} : ContDiffOn 
Real n (stereoToFun v) {x : E | innerSL _ v x != (1 : Real)}
· 使用定理 `ContDiff.comp`：ContDiff.comp {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 
n g) (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n (g ∘ f)
· 使用定理 `contDiff_stereoInvFunAux`：contDiff_stereoInvFunAux {m : Nat∞ω} : ContDif
f Real m (stereoInvFunAux v)
· 使用定理 `ContinuousLinearMap.contDiff`：ContinuousLinearMap.contDiff (f : E ->L[𝕜]
 F) : ContDiff 𝕜 n f
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `stereographic'_target`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [i
nst_1 : InnerProductSpace ℝ E] {n : ℕ}   [inst_2 : Fact (Module.finrank ℝ E = n 
+ 1)] (v : …
· 使用定理 `stereographic'_source`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [i
nst_1 : InnerProductSpace ℝ E] {n : ℕ}   [inst_2 : Fact (Module.finrank ℝ E = n 
+ 1)] (v : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `Set.range_id`：range_id : range (@id α) = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `real_inner_comm`：real_inner_comm (x y : F) : ⟪y, x⟫_Real = ⟪x, y⟫_Real
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
The unit sphere in an `n + 1`-dimensional inner product space `E` is an analytic
 manifold,
modelled on the Euclidean space of dimension `n`.
-/
instance EuclideanSpace.instIsManifoldSphere
    {n : ℕ} [Fact (finrank ℝ E = n + 1)] :
    IsManifold (𝓡 n) ω (sphere (0 : E) 1) :=
  isManifold_of_contDiffOn (𝓡 n) ω (sphere (0 : E) 1)
    (by
      rintro _ _ ⟨v, rfl⟩ ⟨v', rfl⟩
      let U :=
        (-- Removed type ascription, and this helped for some reason with timeout issues?
            OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ)
            n (ne_zero_of_mem_unit_sphere v)).repr
      let U' :=
        (-- Removed type ascription, and this helped for some reason with timeout issues?
            OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ)
            n (ne_zero_of_mem_unit_sphere v')).repr
      have H₁ := U'.contDiff.comp_contDiffOn (contDiffOn_stereoToFun (n := ω))
      -- Porting note: need to help with implicit variables again
      have H₂ := (contDiff_stereoInvFunAux (m := ω) (v := v.val) |>.comp
        (ℝ ∙ (v : E))ᗮ.subtypeL.contDiff).comp U.symm.contDiff
      convert! H₁.comp_inter (H₂.contDiffOn : ContDiffOn ℝ ω _ Set.univ) using 1
        -- -- squeezed from `ext, simp [sphere_ext_iff, stereographic'_symm_apply, real_inner_comm]`

      -- -- squeezed from `ext, simp [sphere_ext_iff, stereographic'_symm_apply, real_inner_comm]`
      simp only [OpenPartialHomeomorph.trans_toPartialEquiv,
        OpenPartialHomeomorph.symm_toPartialEquiv, PartialEquiv.trans_source,
        PartialEquiv.symm_source, stereographic'_target, stereographic'_source]
      simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
        Set.range_id, Set.inter_univ, Set.univ_inter, Set.compl_singleton_eq,
        Set.preimage_ofPred_eq]
      simp only [id, comp_apply, OpenPartialHomeomorph.coe_toPartialEquiv_symm,
        innerSL_apply_apply, Ne, sphere_ext_iff, real_inner_comm (v' : E)]
      rfl)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℕ) : IsManifold (𝓡 n) ω (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  haveI := Fact.mk (@finrank_euclideanSpace_fin ℝ _ (n + 1))
  EuclideanSpace.instIsManifoldSphere

/-- The inclusion map (i.e., `coe`) from the sphere in `E` to `E` is analytic. -/
/-
**contMDiff_coe_sphere** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiff_coe_sphere {m : Nat∞ω} {n : Nat} [Fact (finrank Real E = n + 1)]
 : ContMDiff (𝓡 n) 𝓘(Real, E) m ((↑) : sphere (0 : E) 1 -> E)
参数：finrank Real E = n + 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contMDiff_iff`：contMDiff_iff [IsManifold I n M] [IsManifold I' n M'] : C
ontMDiff I I' n f ↔ Continuous f ∧ forall (x : M) (y : M'), ContDiffOn 𝕜 n (extC
har…
· 使用定理 `IsManifold.instOfTopWithTopENat`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSp
ace 𝕜 E] {H : Type u_…
· 使用定理 `ContMDiffAdd.toIsManifold`：∀ {𝕜 : Type u_1} {inst : NontriviallyNormedFi
eld 𝕜} {H : Type u_2} {inst_1 : TopologicalSpace H} {E : Type u_3}   {inst_2 : N
ormedAddCommGro…
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `ne_zero_of_mem_unit_sphere`：∀ {E : Type u_5} [inst : SeminormedAddGroup 
E] (x : ↑(Metric.sphere 0 1)), ↑x ≠ 0
· 使用定理 `ContDiff.contDiffOn`：ContDiff.contDiffOn (h : ContDiff 𝕜 n f) : ContDiff
On 𝕜 n f s
· 使用定理 `ContDiff.comp`：ContDiff.comp {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 
n g) (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n (g ∘ f)
· 使用定理 `contDiff_stereoInvFunAux`：contDiff_stereoInvFunAux {m : Nat∞ω} : ContDif
f Real m (stereoInvFunAux v)
· 使用定理 `ContinuousLinearMap.contDiff`：ContinuousLinearMap.contDiff (f : E ->L[𝕜]
 F) : ContDiff 𝕜 n f
· 使用定理 `LinearIsometryEquiv.contDiff`：LinearIsometryEquiv.contDiff (f : E ≃ₗᵢ[𝕜]
 F) : ContDiff 𝕜 n f

--- 原说明 ---
The inclusion map (i.e., `coe`) from the sphere in `E` to `E` is analytic.
-/
theorem contMDiff_coe_sphere {m : ℕ∞ω} {n : ℕ} [Fact (finrank ℝ E = n + 1)] :
    ContMDiff (𝓡 n) 𝓘(ℝ, E) m ((↑) : sphere (0 : E) 1 → E) := by
  rw [contMDiff_iff]
  constructor
  · exact continuous_subtype_val
  · intro v _
    let U : _ ≃ₗᵢ[ℝ] _ :=
      (-- Again, partially removing type ascription...
          OrthonormalBasis.fromOrthogonalSpanSingleton
          n (ne_zero_of_mem_unit_sphere (-v))).repr
    exact
      ((contDiff_stereoInvFunAux.comp (ℝ ∙ (-v : E))ᗮ.subtypeL.contDiff).comp
          U.symm.contDiff).contDiffOn

variable {m : ℕ∞ω} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I m M]

/-- If a `C^m` function `f : M → E`, where `M` is some manifold, takes values in the
sphere, then it restricts to a `C^m` function from `M` to the sphere. -/
/-
**ContMDiff.codRestrict_sphere** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiff.codRestrict_sphere {n : Nat} [Fact (finrank Real E = n + 1)] {f 
: M -> E} (hf : CMDiff m f) (hf' : forall x, f x in sphere (0 : E) 1) : CMDiff m
 (Set.codRestrict _ _ hf' : M -> sphere (0 : E) 1)
参数：finrank Real E = n + 1；hf : CMDiff m f；hf' : forall x, f x in sphere (0 : E) 
1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contMDiff_iff_target`：contMDiff_iff_target [IsManifold I n M] [IsManifol
d I' n M'] : ContMDiff I I' n f ↔ Continuous f ∧ forall y : M', ContMDiffOn I 𝓘(
𝕜, E') n (…
· 使用定理 `IsManifold.instOfTopWithTopENat`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSp
ace 𝕜 E] {H : Type u_…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_induced_rng`：continuous_induced_rng {g : γ -> α} {t₂ : Topolo
gicalSpace β} {t₁ : TopologicalSpace γ} : Continuous[t₁, induced f t₂] g ↔ Conti
nuous[t₁, t₂…
· 使用定理 `ContMDiff.continuous`：ContMDiff.continuous (hf : ContMDiff I I' n f) : C
ontinuous f
· 使用定理 `ne_zero_of_mem_unit_sphere`：∀ {E : Type u_5} [inst : SeminormedAddGroup 
E] (x : ↑(Metric.sphere 0 1)), ↑x ≠ 0
· 使用定理 `ContDiff.contDiffOn`：ContDiff.contDiffOn (h : ContDiff 𝕜 n f) : ContDiff
On 𝕜 n f s
· 使用定理 `LinearIsometryEquiv.contDiff`：LinearIsometryEquiv.contDiff (f : E ≃ₗᵢ[𝕜]
 F) : ContDiff 𝕜 n f
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
· 使用定理 `ContDiffOn.contMDiffOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{E' : Type u…
· 使用定理 `ContDiffOn.comp_inter`：ContDiffOn.comp_inter {s : Set E} {t : Set F} {g 
: F -> G} {f : E -> F} (hg : ContDiffOn 𝕜 n g t) (hf : ContDiffOn 𝕜 n f s) : Con
tDiffOn 𝕜 n…
· 使用定理 `contDiffOn_stereoToFun`：contDiffOn_stereoToFun {n : Nat∞ω} : ContDiffOn 
Real n (stereoToFun v) {x : E | innerSL _ v x != (1 : Real)}
· 使用定理 `ContMDiff.contMDiffOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
H : Type u_…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `inner_eq_one_iff_of_norm_eq_one`：inner_eq_one_iff_of_norm_eq_one {x y : 
E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : ⟪x, y⟫ = 1 ↔ x = y
· 使用定理 `norm_eq_of_mem_sphere`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] {r
 : ℝ} (x : ↑(Metric.sphere 0 r)), ‖↑x‖ = r
（共 52 条，此处仅展示前 30 条）

--- 原说明 ---
If a `C^m` function `f : M → E`, where `M` is some manifold, takes values in the
sphere, then it restricts to a `C^m` function from `M` to the sphere.
-/
theorem ContMDiff.codRestrict_sphere {n : ℕ} [Fact (finrank ℝ E = n + 1)] {f : M → E}
    (hf : CMDiff m f) (hf' : ∀ x, f x ∈ sphere (0 : E) 1) :
    CMDiff m (Set.codRestrict _ _ hf' : M → sphere (0 : E) 1) := by
  rw [contMDiff_iff_target]
  refine ⟨continuous_induced_rng.2 hf.continuous, ?_⟩
  intro v
  let U : _ ≃ₗᵢ[ℝ] _ :=
    (-- Again, partially removing type ascription... Weird that this helps!
        OrthonormalBasis.fromOrthogonalSpanSingleton
        n (ne_zero_of_mem_unit_sphere (-v))).repr
  have h : ContDiffOn ℝ ω _ Set.univ := U.contDiff.contDiffOn
  have H₁ := (h.comp_inter contDiffOn_stereoToFun).contMDiffOn
  have H₂ : CMDiff[Set.univ] m f := hf.contMDiffOn
  convert! (H₁.of_le le_top).comp' H₂ using 1
  ext x
  have hfxv : f x = -↑v ↔ ⟪f x, -↑v⟫_ℝ = 1 := by
    have hfx : ‖f x‖ = 1 := by simpa using hf' x
    rw [inner_eq_one_iff_of_norm_eq_one hfx]
    exact norm_eq_of_mem_sphere (-v)
  simp [chartAt, ChartedSpace.chartAt, Subtype.ext_iff, hfxv, real_inner_comm]

/-- The antipodal map is analytic. -/
/-
**contMDiff_neg_sphere** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiff_neg_sphere {m : Nat∞ω} {n : Nat} [Fact (finrank Real E = n + 1)]
 : CMDiff m fun x : sphere (0 : E) 1 => -x
参数：finrank Real E = n + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.codRestrict_sphere`：ContMDiff.codRestrict_sphere {n : Nat} [Fa
ct (finrank Real E = n + 1)] {f : M -> E} (hf : CMDiff m f) (hf' : forall x, f x
 in sphere (0 : E)…
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `IsManifold.instOfTopWithTopENat`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSp
ace 𝕜 E] {H : Type u_…
· 使用定理 `ContMDiff.comp`：ContMDiff.comp {g : M' -> M''} (hg : ContMDiff I' I'' n 
g) (hf : ContMDiff I I' n f) : ContMDiff I I'' n (g ∘ f)
· 使用定理 `ContDiff.contMDiff`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {E' 
: Type u…
· 使用定理 `contDiff_neg`：contDiff_neg : ContDiff 𝕜 n fun p : F => -p
· 使用定理 `contMDiff_coe_sphere`：contMDiff_coe_sphere {m : Nat∞ω} {n : Nat} [Fact (
finrank Real E = n + 1)] : ContMDiff (𝓡 n) 𝓘(Real, E) m ((↑) : sphere (0 : E) 1 
-> E)

--- 原说明 ---
The antipodal map is analytic.
-/
theorem contMDiff_neg_sphere {m : ℕ∞ω} {n : ℕ} [Fact (finrank ℝ E = n + 1)] :
    CMDiff m fun x : sphere (0 : E) 1 => -x := by
  -- this doesn't elaborate well in term mode
  apply ContMDiff.codRestrict_sphere
  apply contDiff_neg.contMDiff.comp _
  exact contMDiff_coe_sphere

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**stereographic'_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma stereographic'_neg {n : ℕ} [Fact (finrank ℝ E = n + 1)] (v : sphere (0 : E) 1) :
    stereographic' n (-v) v = 0 := by
  dsimp [stereographic']
  simp only [EmbeddingLike.map_eq_zero_iff]
  apply stereographic_neg_apply

-- Without this option, the lemmas `EmbeddingLike.map_eq_zero_iff` and `Submodule.range_subtype`
-- are not applied by simp below.
set_option backward.isDefEq.respectTransparency false in
/-- Consider the differential of the inclusion of the sphere in `E` at the point `v` as a continuous
linear map from `TangentSpace (𝓡 n) v` to `E`.  The range of this map is the orthogonal complement
of `v` in `E`.
-/
/-
**range_mvfderiv_subtypeVal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：range_mvfderiv_subtypeVal {n : Nat} [Fact (finrank Real E = n + 1)] (v : s
phere (0 : E) 1) : (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 -> E) v).range = (Rea
l ∙ (v : E))ᗮ
参数：finrank Real E = n + 1；v : sphere (0 : E) 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MDifferentiableAt.mvfderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `ContMDiffAt.mdifferentiableAt`：ContMDiffAt.mdifferentiableAt (hf : CMDif
fAt n f x) (hn : n != 0) : MDiffAt f x
· 使用定理 `contMDiff_coe_sphere`：contMDiff_coe_sphere {m : Nat∞ω} {n : Nat} [Fact (
finrank Real E = n + 1)] : ContMDiff (𝓡 n) 𝓘(Real, E) m ((↑) : sphere (0 : E) 1 
-> E)
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.range.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u
_5} {M₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCo
mmMonoid M] [ins…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.range_id`：range_id : range (@id α) = univ
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `fderivWithin_univ`：fderivWithin_univ : fderivWithin 𝕜 f univ = fderiv 𝕜 
f
· 使用定理 `ne_zero_of_mem_unit_sphere`：∀ {E : Type u_5} [inst : SeminormedAddGroup 
E] (x : ↑(Metric.sphere 0 1)), ↑x ≠ 0
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `SemilinearIsometryEquivClass.toSemilinearIsometryClass`：∀ {R : Type u_1}
 {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} (𝓕 : Type u_10) [inst : Semiring
 R]   [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `hasFDerivAt_stereoInvFunAux_comp_coe`：hasFDerivAt_stereoInvFunAux_comp_c
oe (v : E) : HasFDerivAt (stereoInvFunAux v ∘ ((↑) : (Real ∙ v)ᗮ -> E)) (Real ∙ 
v)ᗮ.subtypeL 0
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
· 使用定理 `Submodule.span_eq_span`：span_eq_span (hs : s subseteq span R t) (ht : t 
subseteq span R s) : span R s = span R t
· 使用定理 `Submodule.neg_mem_iff`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst
_1 : AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x : M
}, -x ∈ p ↔…
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
Consider the differential of the inclusion of the sphere in `E` at the point `v`
 as a continuous
linear map from `TangentSpace (𝓡 n) v` to `E`.  The range of this map is the ort
hogonal complement
of `v` in `E`.
-/
theorem range_mvfderiv_subtypeVal {n : ℕ} [Fact (finrank ℝ E = n + 1)] (v : sphere (0 : E) 1) :
    (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) v).range = (ℝ ∙ (v : E))ᗮ := by
  rw [((contMDiff_coe_sphere v).mdifferentiableAt one_ne_zero).mvfderiv]
  dsimp [chartAt]
  simp only [fderivWithin_univ, mfld_simps]
  let U := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) n
    (ne_zero_of_mem_unit_sphere (-v))).repr
  suffices
      (fderiv ℝ ((stereoInvFunAux (-v : E) ∘ (↑)) ∘ U.symm) 0).range = (ℝ ∙ (v : E))ᗮ by
    rw [← this]
    congr 3
    apply stereographic'_neg
  have :
    HasFDerivAt (stereoInvFunAux (-v : E) ∘ (Subtype.val : (ℝ ∙ (↑(-v) : E))ᗮ → E))
      (ℝ ∙ (↑(-v) : E))ᗮ.subtypeL (U.symm 0) := by
    convert! hasFDerivAt_stereoInvFunAux_comp_coe (-v : E)
    simp
  convert! congr($((this.comp 0 U.symm.toContinuousLinearEquiv.hasFDerivAt).fderiv).range)
  symm
  convert!
    (U.symm : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] (ℝ ∙ (↑(-v) : E))ᗮ).range_comp
      (ℝ ∙ (↑(-v) : E))ᗮ.subtype using 1
  simp only [Submodule.range_subtype, coe_neg_sphere]
  congr 1
  -- we must show `Submodule.span ℝ {v} = Submodule.span ℝ {-v}`
  apply Submodule.span_eq_span
  · simp only [Set.singleton_subset_iff, SetLike.mem_coe]
    rw [← Submodule.neg_mem_iff]
    exact Submodule.mem_span_singleton_self (-v : E)
  · simp only [Set.singleton_subset_iff, SetLike.mem_coe]
    rw [Submodule.neg_mem_iff]
    exact Submodule.mem_span_singleton_self (v : E)

@[deprecated range_mvfderiv_subtypeVal (since := "2026-08-02")]
/-
**range_mfderiv_coe_sphere** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：range_mfderiv_coe_sphere {n : Nat} [Fact (finrank Real E = n + 1)] (v : sp
here (0 : E) 1) : (mfderiv (𝓡 n) 𝓘(Real, E) ((↑) : sphere (0 : E) 1 -> E) v : Ta
ngentSpace (𝓡 n) v ->L[Real] E).range = (Real ∙ (v : E))ᗮ
参数：finrank Real E = n + 1；v : sphere (0 : E) 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `range_mvfderiv_subtypeVal`：range_mvfderiv_subtypeVal {n : Nat} [Fact (fi
nrank Real E = n + 1)] (v : sphere (0 : E) 1) : (mvfderiv (𝓡 n) ((↑) : sphere (0
 : E) 1 -> E) v…
-/
theorem range_mfderiv_coe_sphere {n : ℕ} [Fact (finrank ℝ E = n + 1)] (v : sphere (0 : E) 1) :
    (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) v : TangentSpace (𝓡 n) v →L[ℝ] E).range =
      (ℝ ∙ (v : E))ᗮ := by
  convert! range_mvfderiv_subtypeVal v

/-- Consider the differential of the inclusion of the sphere in `E` at the point `v` as a continuous
linear map from `TangentSpace (𝓡 n) v` to `E`.  This map is injective. -/
/-
**injective_mvfderiv_subtypeVal_sphere** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：injective_mvfderiv_subtypeVal_sphere {n : Nat} [Fact (finrank Real E = n +
 1)] (v : sphere (0 : E) 1) : Injective (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 
-> E) v)
参数：finrank Real E = n + 1；v : sphere (0 : E) 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MDifferentiableAt.mvfderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `ContMDiffAt.mdifferentiableAt`：ContMDiffAt.mdifferentiableAt (hf : CMDif
fAt n f x) (hn : n != 0) : MDiffAt f x
· 使用定理 `contMDiff_coe_sphere`：contMDiff_coe_sphere {m : Nat∞ω} {n : Nat} [Fact (
finrank Real E = n + 1)] : ContMDiff (𝓡 n) 𝓘(Real, E) m ((↑) : sphere (0 : E) 1 
-> E)
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `PartialEquiv.trans_refl`：trans_refl : e.trans (PartialEquiv.refl β) = e
· 使用定理 `Set.range_id`：range_id : range (@id α) = univ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `fderivWithin_univ`：fderivWithin_univ : fderivWithin 𝕜 f univ = fderiv 𝕜 
f
· 使用定理 `ne_zero_of_mem_unit_sphere`：∀ {E : Type u_5} [inst : SeminormedAddGroup 
E] (x : ↑(Metric.sphere 0 1)), ↑x ≠ 0
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `SemilinearIsometryEquivClass.toSemilinearIsometryClass`：∀ {R : Type u_1}
 {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} (𝓕 : Type u_10) [inst : Semiring
 R]   [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `hasFDerivAt_stereoInvFunAux_comp_coe`：hasFDerivAt_stereoInvFunAux_comp_c
oe (v : E) : HasFDerivAt (stereoInvFunAux v ∘ ((↑) : (Real ∙ v)ᗮ -> E)) (Real ∙ 
v)ᗮ.subtypeL 0
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `HasFDerivAt.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 
: Topolo…
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
Consider the differential of the inclusion of the sphere in `E` at the point `v`
 as a continuous
linear map from `TangentSpace (𝓡 n) v` to `E`.  This map is injective.
-/
theorem injective_mvfderiv_subtypeVal_sphere {n : ℕ} [Fact (finrank ℝ E = n + 1)]
    (v : sphere (0 : E) 1) :
    Injective (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) v) := by
  rw [((contMDiff_coe_sphere v).mdifferentiableAt one_ne_zero).mvfderiv]
  simp only [chartAt, fderivWithin_univ, mfld_simps]
  let U := (OrthonormalBasis.fromOrthogonalSpanSingleton
      (𝕜 := ℝ) n (ne_zero_of_mem_unit_sphere (-v))).repr
  suffices Injective (fderiv ℝ ((stereoInvFunAux (-v : E) ∘ (↑)) ∘ U.symm) 0) by
    convert! this using 3
    congr 2
    apply stereographic'_neg (v := v)
  have : HasFDerivAt (stereoInvFunAux (-v : E) ∘ (Subtype.val : (ℝ ∙ (↑(-v) : E))ᗮ → E))
      (ℝ ∙ (↑(-v) : E))ᗮ.subtypeL (U.symm 0) := by
    convert! hasFDerivAt_stereoInvFunAux_comp_coe (-v : E)
    -- Otherwise, the lemma `EmbeddingLike.map_eq_zero_iff` is not applied.
    set_option backward.isDefEq.respectTransparency false in
    simp
  have := congr_arg DFunLike.coe <| (this.comp 0 U.symm.toContinuousLinearEquiv.hasFDerivAt).fderiv
  refine Eq.subst this.symm ?_
  rw [ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe]
  set_option backward.isDefEq.respectTransparency false in
  simpa [-Subtype.val_injective] using Subtype.val_injective

@[deprecated injective_mvfderiv_subtypeVal_sphere (since := "2026-08-02")]
/-
**mfderiv_coe_sphere_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mfderiv_coe_sphere_injective {n : Nat} [Fact (finrank Real E = n + 1)] (v 
: sphere (0 : E) 1) : Injective (mfderiv (𝓡 n) 𝓘(Real, E) ((↑) : sphere (0 : E) 
1 -> E) v)
参数：finrank Real E = n + 1；v : sphere (0 : E) 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `injective_mvfderiv_subtypeVal_sphere`：injective_mvfderiv_subtypeVal_sphe
re {n : Nat} [Fact (finrank Real E = n + 1)] (v : sphere (0 : E) 1) : Injective 
(mvfderiv (𝓡 n) ((↑) : sph…
-/
theorem mfderiv_coe_sphere_injective {n : ℕ} [Fact (finrank ℝ E = n + 1)] (v : sphere (0 : E) 1) :
    Injective (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) v) := by
  convert! injective_mvfderiv_subtypeVal_sphere v

end ContMDiffManifold

section Circle

open Complex

/-- Local instance to help the typeclass system to figure out `1 + 1 = 2`. -/
/-
**finrank_real_complex_fact'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finrank_real_complex_fact' : Fact (finrank Real Complex = 1 + 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.finrank_real_complex_fact`：finrank_real_complex_fact : Fact (fin
rank Real Complex = 2)

--- 原说明 ---
Local instance to help the typeclass system to figure out `1 + 1 = 2`.
-/
theorem finrank_real_complex_fact' : Fact (finrank ℝ ℂ = 1 + 1) :=
  finrank_real_complex_fact

attribute [local instance] finrank_real_complex_fact'

/-- The unit circle in `ℂ` is a charted space modelled on `EuclideanSpace ℝ (Fin 1)`.  This
follows by definition from the corresponding result for `Metric.Sphere`. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unit circle in `ℂ` is a charted space modelled on `EuclideanSpace ℝ (Fin 1)`
.  This
follows by definition from the corresponding result for `Metric.Sphere`.
-/
instance : ChartedSpace (EuclideanSpace ℝ (Fin 1)) Circle :=
  inferInstanceAs <| ChartedSpace _ (sphere _ _)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsManifold (𝓡 1) ω Circle :=
  EuclideanSpace.instIsManifoldSphere (E := ℂ)

/-- The unit circle in `ℂ` is an analytic Lie group. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unit circle in `ℂ` is an analytic Lie group.
-/
instance : LieGroup (𝓡 1) ω Circle where
  contMDiff_mul := by
    apply ContMDiff.codRestrict_sphere
    let c : Circle → ℂ := (↑)
    have h₂ : ContMDiff (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ) ω fun z : ℂ × ℂ => z.fst * z.snd := by
      rw [contMDiff_iff]
      exact ⟨continuous_mul, fun x y => contDiff_mul.contDiffOn⟩
    -- TODO bug: filling in ω yields an error; expected type has metavariables...
    suffices h₁ : ContMDiff _ _ _ (Prod.map c c) from
      h₂.comp h₁
    apply ContMDiff.prodMap <;> exact contMDiff_coe_sphere
  contMDiff_inv := by
    apply ContMDiff.codRestrict_sphere
    simp only [← Circle.coe_inv, Circle.coe_inv_eq_conj]
    exact Complex.conjCLE.contDiff.contMDiff.comp contMDiff_coe_sphere

/-- The map `fun t ↦ exp (t * I)` from `ℝ` to the unit circle in `ℂ` is analytic. -/
/-
**contMDiff_circleExp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiff_circleExp {m : Nat∞ω} : CMDiff m Circle.exp
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.codRestrict_sphere`：ContMDiff.codRestrict_sphere {n : Nat} [Fa
ct (finrank Real E = n + 1)] {f : M -> E} (hf : CMDiff m f) (hf' : forall x, f x
 in sphere (0 : E)…
· 使用定理 `ContMDiffAdd.toIsManifold`：∀ {𝕜 : Type u_1} {inst : NontriviallyNormedFi
eld 𝕜} {H : Type u_2} {inst_1 : TopologicalSpace H} {E : Type u_3}   {inst_2 : N
ormedAddCommGro…
· 使用定理 `finrank_real_complex_fact'`：finrank_real_complex_fact' : Fact (finrank R
eal Complex = 1 + 1)
· 使用定理 `ContDiff.contMDiff`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {E' 
: Type u…
· 使用定理 `ContDiff.comp`：ContDiff.comp {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 
n g) (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n (g ∘ f)
· 使用定理 `Complex.contDiff_exp`：contDiff_exp {n : WithTop Nat∞} : ContDiff 𝕜 n exp
· 使用定理 `ContDiff.smul`：ContDiff.smul {f : E -> 𝕜'} {g : E -> F} (hf : ContDiff 𝕜
 n f) (hg : ContDiff 𝕜 n g) : ContDiff 𝕜 n (f • g)
· 使用定理 `contDiff_id`：contDiff_id : ContDiff 𝕜 n (id : E -> E)
· 使用定理 `contDiff_const`：contDiff_const {c : F} : ContDiff 𝕜 n fun _ : E => c

--- 原说明 ---
The map `fun t ↦ exp (t * I)` from `ℝ` to the unit circle in `ℂ` is analytic.
-/
theorem contMDiff_circleExp {m : ℕ∞ω} : CMDiff m Circle.exp :=
  (contDiff_exp.comp (contDiff_id.smul contDiff_const)).contMDiff.codRestrict_sphere _

end Circle

