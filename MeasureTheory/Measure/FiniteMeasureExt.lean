/-
Copyright (c) 2024 Jakob Stiefel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Stiefel
-/
module

public import Mathlib.Analysis.RCLike.BoundedContinuous
public import Mathlib.Analysis.SpecialFunctions.MulExpNegMulSqIntegral
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-!
# Extensionality of finite measures

The main result is `ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable`:
Let `A` be a StarSubalgebra of `C(E, 𝕜)` that separates points and whose elements are bounded. If
the integrals of all elements of `A` with respect to two finite measures `P, P'` coincide, then the
measures coincide. In other words: If a subalgebra separates points, it separates finite measures.
-/

public section

open MeasureTheory Filter Real RCLike BoundedContinuousFunction

open scoped Topology

variable {E 𝕜 : Type*} [RCLike 𝕜]

namespace MeasureTheory

variable [MeasurableSpace E]

/-- If the integrals of all elements of a subalgebra `A` of continuous and bounded functions with
respect to two finite measures `P, P'` coincide, then the measures coincide. In other words: If a
subalgebra separates points, it separates finite measures. -/
/-
**MeasureTheory.ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_comple
te_countable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countab
le [PseudoEMetricSpace E] [BorelSpace E] [CompleteSpace E] [SecondCountableTopol
ogy E] {P P' : Measure E} [IsFiniteMeasure P] [IsFiniteMeasure P'] {A : StarSuba
lgebra 𝕜 (E ->ᵇ 𝕜)} (hA : (A.map (toContinuousMapStarₐ 𝕜)).SeparatesPoints) (heq
 : forall g in A, ∫ x, (g : E -> 𝕜) x ∂P = ∫ x, (g : E -> 𝕜) x ∂P') : P = P'
参数：E ->ᵇ 𝕜；hA : (A.map (toContinuousMapStarₐ 𝕜)).SeparatesPoints；heq : forall g 
in A, ∫ x, (g : E -> 𝕜) x ∂P = ∫ x, (g : E -> 𝕜) x ∂P'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instBoundedMul`：∀ {R : Type u_1} [inst : NonUnitalSeminormedRing R], Bou
ndedMul R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用定理 `RCLike.instCStarRing`：∀ {K : Type u_1} [inst : RCLike K], CStarRing K
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `ContinuousMap.instStarModule`：∀ {R : Type u_1} {α : Type u_2} {β : Type 
u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst_2 : Star 
R] [inst_3 : Star …
· 使用定理 `RCLike.lipschitzWith_ofReal`：lipschitzWith_ofReal : LipschitzWith 1 (ofR
eal : Real -> K)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `RCLike.continuous_ofReal`：continuous_ofReal : Continuous (ofReal : Real 
-> K)
· 使用定理 `ContinuousMap.instIsScalarTower`：∀ {α : Type u_1} [inst : TopologicalSpa
ce α] {R : Type u_3} {R₁ : Type u_4} {M : Type u_5} [inst_1 : TopologicalSpace M
]   [inst_2 : SMul R …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.restrict_toContinuousMap_eq_toContinuousMapStar_restrict`：restric
t_toContinuousMap_eq_toContinuousMapStar_restrict {A : StarSubalgebra 𝕜 (E ->ᵇ 𝕜
)} : ((A.restrictScalars Real).comap (AlgHom.compLeft…
· 使用定理 `Subalgebra.SeparatesPoints.rclike_to_real`：Subalgebra.SeparatesPoints.rc
like_to_real {A : StarSubalgebra 𝕜 C(X, 𝕜)} (hA : A.SeparatesPoints) : ((A.restr
ictScalars Real).comap (ofRealA…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RCLike.ofReal_inj`：ofReal_inj {z w : Real} : (z : K) = (w : K) ↔ z = w
· 使用定理 `integral_ofReal`：integral_ofReal {f : X -> Real} : ∫ x, (f x : 𝕜) ∂μ = ↑
(∫ x, f x ∂μ)
· 使用定理 `MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure`：ext_of_foral
l_integral_eq_of_IsFiniteMeasure {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpa
ce Ω] [HasOuterApproxClosed Ω] [BorelSpace Ω] {μ…
· 使用定理 `instHasOuterApproxClosedOfPseudoMetrizableSpace`：∀ (X : Type u_1) [inst 
: TopologicalSpace X] [TopologicalSpace.PseudoMetrizableSpace X], HasOuterApprox
Closed X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
（共 59 条，此处仅展示前 30 条）

--- 原说明 ---
If the integrals of all elements of a subalgebra `A` of continuous and bounded f
unctions with
respect to two finite measures `P, P'` coincide, then the measures coincide. In 
other words: If a
subalgebra separates points, it separates finite measures.
-/
theorem ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable
    [PseudoEMetricSpace E] [BorelSpace E] [CompleteSpace E] [SecondCountableTopology E]
    {P P' : Measure E} [IsFiniteMeasure P] [IsFiniteMeasure P']
    {A : StarSubalgebra 𝕜 (E →ᵇ 𝕜)} (hA : (A.map (toContinuousMapStarₐ 𝕜)).SeparatesPoints)
    (heq : ∀ g ∈ A, ∫ x, (g : E → 𝕜) x ∂P = ∫ x, (g : E → 𝕜) x ∂P') : P = P' := by
  --consider the real subalgebra of the purely real-valued elements of A
  let A_toReal := (A.restrictScalars ℝ).comap
    (ofRealAm.compLeftContinuousBounded ℝ lipschitzWith_ofReal)
  --the real subalgebra separates points
  have hA_toReal : (A_toReal.map (toContinuousMapₐ ℝ)).SeparatesPoints := by
    rw [RCLike.restrict_toContinuousMap_eq_toContinuousMapStar_restrict]
    exact Subalgebra.SeparatesPoints.rclike_to_real hA
  --integrals of elements of the real subalgebra w.r.t. P, P', respectively, coincide
  have heq' : ∀ g ∈ A_toReal, ∫ x, (g : E → ℝ) x ∂P = ∫ x, (g : E → ℝ) x ∂P' := by
    intro g hgA_toReal
    rw [← @ofReal_inj 𝕜, ← integral_ofReal, ← integral_ofReal]
    exact heq _ hgA_toReal
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  have h0 : Tendsto (fun ε : ℝ => 6 * √ε) (𝓝[>] 0) (𝓝 0) := by
    nth_rewrite 3 [← mul_zero 6]
    apply tendsto_nhdsWithin_of_tendsto_nhds (Tendsto.const_mul 6 _)
    nth_rewrite 2 [← sqrt_zero]
    exact Continuous.tendsto continuous_sqrt 0
  have lim1 : Tendsto (fun ε => |∫ x, mulExpNegMulSq ε (f x) ∂P - ∫ x, mulExpNegMulSq ε (f x) ∂P'|)
      (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero' (eventually_nhdsWithin_of_forall (fun x _ => abs_nonneg _))
      (eventually_nhdsWithin_of_forall _) h0
    exact fun ε hε => dist_integral_mulExpNegMulSq_comp_le f hA_toReal heq' hε
  have lim2 : Tendsto (fun ε => |∫ x, mulExpNegMulSq ε (f x) ∂P
      - ∫ x, mulExpNegMulSq ε (f x) ∂P'|) (𝓝[>] 0)
      (𝓝 |∫ x, f x ∂↑P - ∫ x, f x ∂↑P'|) :=
    Tendsto.abs (Tendsto.sub (tendsto_integral_mulExpNegMulSq_comp f)
      (tendsto_integral_mulExpNegMulSq_comp f))
  exact eq_of_abs_sub_eq_zero (tendsto_nhds_unique lim2 lim1)
/-
**MeasureTheory.ext_of_forall_mem_subalgebra_integral_eq_of_polish** 是 Mathlib 中
的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ext_of_forall_mem_subalgebra_integral_eq_of_polish [TopologicalSpace E] [P
olishSpace E] [BorelSpace E] {P P' : Measure E} [IsFiniteMeasure P] [IsFiniteMea
sure P'] {A : StarSubalgebra 𝕜 (E ->ᵇ 𝕜)} (hA : (A.map (toContinuousMapStarₐ 𝕜))
.SeparatesPoints) (heq : forall g in A, ∫ x, (g : E -> 𝕜) x ∂P = ∫ x, (g : E -> 
𝕜) x ∂P') : P = P'
参数：E ->ᵇ 𝕜；hA : (A.map (toContinuousMapStarₐ 𝕜)).SeparatesPoints；heq : forall g 
in A, ∫ x, (g : E -> 𝕜) x ∂P = ∫ x, (g : E -> 𝕜) x ∂P'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instBoundedMul`：∀ {R : Type u_1} [inst : NonUnitalSeminormedRing R], Bou
ndedMul R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `SeminormedAddCommGroup.to_lipschitzAdd`：∀ {E : Type u_2} [inst : Seminor
medAddCommGroup E], LipschitzAdd E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用定理 `RCLike.instCStarRing`：∀ {K : Type u_1} [inst : RCLike K], CStarRing K
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `ContinuousMap.instStarModule`：∀ {R : Type u_1} {α : Type u_2} {β : Type 
u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst_2 : Star 
R] [inst_3 : Star …
· 使用定理 `PolishSpace.toIsCompletelyMetrizableSpace`：∀ {α : Type u_3} {h : Topolog
icalSpace α} [self : PolishSpace α], TopologicalSpace.IsCompletelyMetrizableSpac
e α
· 使用定理 `MeasureTheory.ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_
complete_countable`：ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_co
mplete_countable [PseudoEMetricSpace E] [BorelSpace E] [CompleteSpace E] [Second
…
· 使用定理 `TopologicalSpace.UpgradedIsCompletelyMetrizableSpace.toCompleteSpace`：∀ 
{X : Type u_3} [self : TopologicalSpace.UpgradedIsCompletelyMetrizableSpace X], 
CompleteSpace X
· 使用定理 `PolishSpace.toSecondCountableTopology`：∀ {α : Type u_3} {h : Topological
Space α} [self : PolishSpace α], SecondCountableTopology α
-/
theorem ext_of_forall_mem_subalgebra_integral_eq_of_polish [TopologicalSpace E] [PolishSpace E]
    [BorelSpace E] {P P' : Measure E} [IsFiniteMeasure P] [IsFiniteMeasure P']
    {A : StarSubalgebra 𝕜 (E →ᵇ 𝕜)} (hA : (A.map (toContinuousMapStarₐ 𝕜)).SeparatesPoints)
    (heq : ∀ g ∈ A, ∫ x, (g : E → 𝕜) x ∂P = ∫ x, (g : E → 𝕜) x ∂P') : P = P' := by
  let := TopologicalSpace.upgradeIsCompletelyMetrizable E
  exact ext_of_forall_mem_subalgebra_integral_eq_of_pseudoEMetric_complete_countable hA heq

end MeasureTheory

