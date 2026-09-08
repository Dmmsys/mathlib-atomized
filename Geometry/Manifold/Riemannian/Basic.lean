/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.Riemannian.PathELength
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

/-! # Riemannian manifolds

A Riemannian manifold `M` is a real manifold such that its tangent spaces are endowed with an
inner product, depending smoothly on the point, and such that `M` has an emetric space
structure for which the distance is the infimum of lengths of paths.

We register a Prop-valued typeclass `IsRiemannianManifold I M` recording this fact, building on top
of `[EMetricSpace M] [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]`.

We show that an inner product vector space, with the associated canonical Riemannian metric,
satisfies the predicate `IsRiemannianManifold 𝓘(ℝ, E) E`.

In a general manifold with a Riemannian metric, we define the associated extended distance in the
manifold, and show that it defines the same topology as the pre-existing one. Therefore, one
may endow the manifold with an emetric space structure, see `EMetricSpace.ofRiemannianMetric`.
By definition, it then satisfies the predicate `IsRiemannianManifold I M`.

The following code block is the standard way to say "Let `M` be a `C^∞` Riemannian manifold".
```
open scoped Bundle
variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]
```
To register a `C^n` manifold for a general `n`, one should replace `[IsManifold I ∞ M]` with
`[IsManifold I n M] [IsManifold I 1 M]`, where the second one is needed to ensure that the
tangent bundle is well behaved (not necessary when `n` is concrete like 2 or 3 as there are
automatic instances for these cases). One can require whatever regularity one wants in the
`IsContMDiffRiemannianBundle` instance above, for example
`[IsContMDiffRiemannianBundle I n E (fun (x : M) ↦ TangentSpace I x)]`, and one should also add
`[IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]` (as above, Lean cannot infer
the latter from the former as it cannot guess `n`).
-/

@[expose] public section

open Bundle Bornology Set MeasureTheory Manifold Filter
open scoped ENNReal ContDiff Topology

local notation "⟪" x ", " y "⟫" => inner ℝ x y

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

section

variable [PseudoEMetricSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace% x)]

variable (I M) in
/-- Consider a manifold in which the tangent spaces are already endowed with an inner product, and
the space is already endowed with an extended distance. We say that this is a Riemannian manifold
if the distance is given by the infimum of the lengths of `C^1` paths, measured using the norm in
the tangent spaces.

This is a `Prop`-valued typeclass, on top of existing data.

If you need to *construct* a distance using a Riemannian structure,
see `EMetricSpace.ofRiemannianMetric`. -/
/-
**IsRiemannianManifold** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{E : Type u_1} →   [inst : NormedAddCommGroup E] →     [inst_1 : NormedSpa
ce ℝ E] →       {H : Type u_2} →         [inst_2 : TopologicalSpace H] →        
   (I : ModelWithCorners ℝ E H) →             (M : Type u_3) →               [in
st_3 : TopologicalSpace M] →                 [PseudoEMetricSpace M] →           
        [inst_5 : ChartedSpace H M] → [Bundle.RiemannianBundle fun x => TangentS
pace I x] → Prop
参数：I : ModelWithCorners ℝ E H；M : Type u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Consider a manifold in which the tangent spaces are already endowed with an inne
r product, and
the space is already endowed with an extended distance. We say that this is a Ri
emannian manifold
if the distance is given by the infimum of the lengths of `C^1` paths, measured 
using the norm in
the tangent spaces.

This is a `Prop`-valued typeclass, on top of existing data.

If you need to *construct* a distance using a Riemannian structure,
see `EMetricSpace.ofRiemannianMetric`.
-/
class IsRiemannianManifold : Prop where
  out (x y : M) : edist x y = riemannianEDist I x y

end

section

/-!
### Riemannian structure on an inner product vector space

We endow an inner product vector space with the canonical Riemannian metric, given by the
inner product of the vector space in each of the tangent spaces, and we show that this construction
satisfies the `IsRiemannianManifold 𝓘(ℝ, E) E` predicate, i.e., the extended distance between
two points is the infimum of the length of paths between these points.
-/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

set_option backward.isDefEq.respectTransparency false in
variable (F) in
/-- The standard Riemannian metric on a vector space with an inner product, given by this inner
product on each tangent space. -/
/-
**riemannianMetricVectorSpace** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：riemannianMetricVectorSpace : ContMDiffRiemannianMetric 𝓘(Real, F) ω F (fu
n (x : F) => TangentSpace% x) where inner x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The standard Riemannian metric on a vector space with an inner product, given by
 this inner
product on each tangent space.
-/
noncomputable def riemannianMetricVectorSpace :
    ContMDiffRiemannianMetric 𝓘(ℝ, F) ω F (fun (x : F) ↦ TangentSpace% x) where
  inner x := (innerSL ℝ (E := F) : F →L[ℝ] F →L[ℝ] ℝ)
  symm x v w := real_inner_comm _ _
  pos x v hv := real_inner_self_pos.2 hv
  isVonNBounded x := by
    change IsVonNBounded ℝ {v : F | ⟪v, v⟫ < 1}
    have : Metric.ball (0 : F) 1 = {v : F | ⟪v, v⟫ < 1} := by
      ext v
      simp only [Metric.mem_ball, dist_zero_right, norm_eq_sqrt_re_inner (𝕜 := ℝ),
        RCLike.re_to_real, Set.mem_ofPred_eq]
      conv_lhs => rw [show (1 : ℝ) = √1 by simp]
      rw [Real.sqrt_lt_sqrt_iff]
      exact real_inner_self_nonneg
    rw [← this]
    exact NormedSpace.isVonNBounded_ball ℝ F 1
  contMDiff := by
    intro x
    rw [contMDiffAt_section]
    convert! contMDiffAt_const (c := innerSL ℝ)
    ext v w
    simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates, TangentSpace]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : RiemannianBundle (fun (x : F) ↦ TangentSpace% x) :=
  ⟨(riemannianMetricVectorSpace F).toRiemannianMetric⟩

set_option backward.isDefEq.respectTransparency false in
/-
**norm_tangentSpace_vectorSpace** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：norm_tangentSpace_vectorSpace {x : F} {v : TangentSpace% x} : ‖v‖ = ‖letI 
V : F
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupTangentSpace`：∀ {𝕜 : Type u_2} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_1} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {H : Type u_…
· 使用定理 `instContinuousConstSMulTangentSpace`：∀ {𝕜 : Type u_1} [inst : Nontrivial
lyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norm
edSpace 𝕜 E] {H : Type u_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_eq_sqrt_real_inner`：norm_eq_sqrt_real_inner (x : F) : ‖x‖ = √⟪x, x⟫
_Real
-/
lemma norm_tangentSpace_vectorSpace {x : F} {v : TangentSpace% x} :
    ‖v‖ = ‖letI V : F := v; V‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner]
/-
**nnnorm_tangentSpace_vectorSpace** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nnnorm_tangentSpace_vectorSpace {x : F} {v : TangentSpace% x} : ‖v‖₊ = ‖le
tI V : F
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instIsTopologicalAddGroupTangentSpace`：∀ {𝕜 : Type u_2} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_1} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {H : Type u_…
· 使用定理 `instContinuousConstSMulTangentSpace`：∀ {𝕜 : Type u_1} [inst : Nontrivial
lyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norm
edSpace 𝕜 E] {H : Type u_…
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `norm_tangentSpace_vectorSpace`：norm_tangentSpace_vectorSpace {x : F} {v 
: TangentSpace% x} : ‖v‖ = ‖letI V : F
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.mk.congr_simp`：∀ (x x_1 : ℝ) (e_x : x = x_1) (hx : 0 ≤ x), NNReal
.mk x hx = NNReal.mk x_1 ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma nnnorm_tangentSpace_vectorSpace {x : F} {v : TangentSpace% x} :
    ‖v‖₊ = ‖letI V : F := v; V‖₊ := by
  simp [nnnorm, norm_tangentSpace_vectorSpace]
/-
**enorm_tangentSpace_vectorSpace** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：enorm_tangentSpace_vectorSpace {x : F} {v : TangentSpace% x} : ‖v‖ₑ = ‖let
I V : F
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instIsTopologicalAddGroupTangentSpace`：∀ {𝕜 : Type u_2} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_1} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {H : Type u_…
· 使用定理 `instContinuousConstSMulTangentSpace`：∀ {𝕜 : Type u_1} [inst : Nontrivial
lyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norm
edSpace 𝕜 E] {H : Type u_…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `nnnorm_tangentSpace_vectorSpace`：nnnorm_tangentSpace_vectorSpace {x : F}
 {v : TangentSpace% x} : ‖v‖₊ = ‖letI V : F
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma enorm_tangentSpace_vectorSpace {x : F} {v : TangentSpace% x} :
    ‖v‖ₑ = ‖letI V : F := v; V‖ₑ := by
  simp [enorm, nnnorm_tangentSpace_vectorSpace]

open MeasureTheory Measure
/-
**lintegral_fderiv_lineMap_eq_edist** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lintegral_fderiv_lineMap_eq_edist {x y : E} : ∫⁻ t in Icc 0 1, ‖fderivWith
in Real (ContinuousAffineMap.lineMap (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PseudoEMetricSpace.edist_comm`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x y : α), edist x y = edist y x
· 使用定理 `edist_eq_enorm_sub`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (
a b : E), edist a b = ‖a - b‖ₑ
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `Real.volume_Icc`：volume_Icc {a b : Real} : volume (Icc a b) = ofReal (b 
- a)
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `ENNReal.ofReal_one`：ENNReal.ofReal 1 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsTopologicalAddTorsor.toContinuousVAdd`：∀ {V : Type u_1} {inst : AddGro
up V} {inst_1 : TopologicalSpace V} {P : Type u_2} {inst_2 : AddTorsor V P}   {i
nst_3 : TopologicalSpace P} […
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `MeasureTheory.setLIntegral_congr_fun`：setLIntegral_congr_fun {f g : α ->
 Real>=0∞} {s : Set α} (hs : MeasurableSet s) (hfg : EqOn f g s) : ∫⁻ x in s, f 
x ∂μ = ∫⁻ x in s, g x ∂μ
· 使用定理 `measurableSet_Icc`：measurableSet_Icc [OrderClosedTopology α] : Measurabl
eSet (Icc a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousAffineMap.fderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {F : Type u_…
· 使用定理 `AffineMap.lineMap_linear`：lineMap_linear (p₀ p₁ : P1) : (lineMap p₀ p₁ :
 k ->ᵃ[k] P1).linear = LinearMap.id.smulRight (p₁ -ᵥ p₀)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `fderivWithin_eq_fderiv`：fderivWithin_eq_fderiv [ContinuousAdd E] [Contin
uousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F] [T2Space F] (hs : UniqueDif
fWithinAt 𝕜 …
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
（共 41 条，此处仅展示前 30 条）
-/
lemma lintegral_fderiv_lineMap_eq_edist {x y : E} :
    ∫⁻ t in Icc 0 1, ‖fderivWithin ℝ (ContinuousAffineMap.lineMap (R := ℝ) x y) (Icc 0 1) t 1‖ₑ
      = edist x y := by
  have : edist x y = ∫⁻ t in Icc (0 : ℝ) 1, ‖y - x‖ₑ := by
    simp [edist_comm x y, edist_eq_enorm_sub]
  rw [this]
  apply setLIntegral_congr_fun measurableSet_Icc (fun z hz ↦ ?_)
  rw [show y - x = fderiv ℝ (ContinuousAffineMap.lineMap (R := ℝ) x y) z 1 by simp]
  congr
  exact fderivWithin_eq_fderiv (uniqueDiffOn_Icc zero_lt_one _ hz)
    (ContinuousAffineMap.differentiableAt _)

/-- An inner product vector space is a Riemannian manifold, i.e., the distance between two points
is the infimum of the lengths of paths between these points. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An inner product vector space is a Riemannian manifold, i.e., the distance betwe
en two points
is the infimum of the lengths of paths between these points.
-/
instance : IsRiemannianManifold 𝓘(ℝ, F) F := by
  refine ⟨fun x y ↦ le_antisymm ?_ ?_⟩
  · simp only [riemannianEDist, le_iInf_iff]
    intro γ hγ
    let e : ℝ → F := γ ∘ (projIcc 0 1 zero_le_one)
    have D : ContDiffOn ℝ 1 e (Icc 0 1) :=
      contMDiffOn_iff_contDiffOn.mp (hγ.comp_contMDiffOn contMDiffOn_projIcc)
    rw [lintegral_norm_mfderiv_Icc_eq_pathELength_projIcc,
      pathELength_eq_lintegral_mfderivWithin_Icc]
    simp only [mfderivWithin_eq_fderivWithin, enorm_tangentSpace_vectorSpace]
    conv_lhs =>
      rw [edist_comm, edist_eq_enorm_sub, show x = e 0 by simp [e], show y = e 1 by simp [e]]
    exact (enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc D zero_le_one).trans_eq rfl
  · let γ := ContinuousAffineMap.lineMap (R := ℝ) x y
    have : riemannianEDist 𝓘(ℝ, F) x y ≤ pathELength 𝓘(ℝ, F) γ 0 1 := by
      apply riemannianEDist_le_pathELength ?_ (by simp [γ, ContinuousAffineMap.coe_lineMap_eq])
        (by simp [γ, ContinuousAffineMap.coe_lineMap_eq]) zero_le_one
      rw [contMDiffOn_iff_contDiffOn]
      exact γ.contDiff.contDiffOn
    apply this.trans_eq
    rw [pathELength_eq_lintegral_mfderivWithin_Icc]
    simp only [mfderivWithin_eq_fderivWithin, enorm_tangentSpace_vectorSpace]
    exact lintegral_fderiv_lineMap_eq_edist

end

section

/-!
### Constructing a distance from a Riemannian structure

Let `M` be a real manifold with a Riemannian structure. We construct the associated distance and
show that the associated topology coincides with the pre-existing topology. Therefore, one may
endow `M` with an emetric space structure, called `EMetricSpace.ofRiemannianMetric`.
Moreover, we show that in this case the resulting emetric space satisfies the predicate
`IsRiemannianManifold I M`.

Showing that the distance topology coincides with the pre-existing topology is not trivial. The
two inclusions are proved respectively in `eventually_riemannianEDist_lt` and
`setOfPred_riemannianEDist_lt_subset_nhds`.

For the first one, we have to show that points which are close for the topology are at small
distance. For this, we use the path between the two points which is the pullback of the segment
in the extended chart, and argue that it is short because the images are close in the extended
chart.

For the second one, we have to show that any neighborhood of `x` contains all the points `y`
with `riemannianEDist x y < c` for some `c > 0`. For this, we argue that a short path from `x`
to `y` remains short in the extended chart, and therefore it doesn't have the time to exit
the image of the neighborhood in the extended chart.
-/

open Manifold Metric
open scoped NNReal

variable [RiemannianBundle (fun (x : M) ↦ TangentSpace% x)]
  [IsManifold I 1 M] [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace% x)]

/-- Register on the tangent space to a normed vector space the same `NormedAddCommGroup` structure
as in the vector space.

Should not be a global instance, as it does not coincide definitionally with the Riemannian
/-
**for** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：for `array` was)  2. belong in `Mathlib/Control/Traversable/Instances.lean
` instead of this file. - /  -- namespace Array'  -- open Function  -- variable 
{n : ℕ}  -- instance : Traversable (Array' n)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
structure for inner product spaces, but can be activated locally. -/
@[instance_reducible]
/-
**normedAddCommGroupTangentSpaceVectorSpace** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：normedAddCommGroupTangentSpaceVectorSpace (x : E) : NormedAddCommGroup (Ta
ngentSpace% x)
参数：x : E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Register on the tangent space to a normed vector space the same `NormedAddCommGr
oup` structure
as in the vector space.

Should not be a global instance, as it does not coincide definitionally with the
 Riemannian
structure for inner product spaces, but can be activated locally.
-/
def normedAddCommGroupTangentSpaceVectorSpace (x : E) :
    NormedAddCommGroup (TangentSpace% x) :=
  inferInstanceAs (NormedAddCommGroup E)

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace

/-- Register on the tangent space to a normed vector space the same `NormedSpace` structure
as in the vector space.

Should not be a global instance, as it does not coincide definitionally with the Riemannian
/-
**for** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：for `array` was)  2. belong in `Mathlib/Control/Traversable/Instances.lean
` instead of this file. - /  -- namespace Array'  -- open Function  -- variable 
{n : ℕ}  -- instance : Traversable (Array' n)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
structure for inner product spaces, but can be activated locally. -/
@[instance_reducible]
/-
**normedSpaceTangentSpaceVectorSpace** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：normedSpaceTangentSpaceVectorSpace (x : E) : NormedSpace Real (TangentSpac
e% x)
参数：x : E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Register on the tangent space to a normed vector space the same `NormedSpace` st
ructure
as in the vector space.

Should not be a global instance, as it does not coincide definitionally with the
 Riemannian
structure for inner product spaces, but can be activated locally.
-/
def normedSpaceTangentSpaceVectorSpace (x : E) : NormedSpace ℝ (TangentSpace% x) :=
  inferInstanceAs (NormedSpace ℝ E)

attribute [local instance] normedSpaceTangentSpaceVectorSpace

variable (I)

set_option backward.isDefEq.respectTransparency false in
/-
**eventually_norm_mfderiv_extChartAt_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eventually_norm_mfderiv_extChartAt_lt (x : M) : exists C > 0, forallᶠ y in
 𝓝 x, ‖mfderiv% (extChartAt I x) y‖ < C
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupTangentSpace`：∀ {𝕜 : Type u_2} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_1} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {H : Type u_…
· 使用定理 `instContinuousConstSMulTangentSpace`：∀ {𝕜 : Type u_1} [inst : Nontrivial
lyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norm
edSpace 𝕜 E] {H : Type u_…
· 使用定理 `trivialization_linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → AddCom
mMonoid (E …
· 使用定理 `instMemTrivializationAtlasTrivializationAt`：∀ {B : Type u_2} {F : Type u
_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {E : B → Type u_5}
   [inst_2 : TopologicalSpace (B…
· 使用引理 `eventually_norm_trivializationAt_lt`：eventually_norm_trivializationAt_lt
 (x : B) : exists C > 0, forallᶠ y in 𝓝 x, ‖(trivializationAt F E x).continuousL
inearMapAt Real y‖ < C
· 使用定理 `chart_source_mem_nhds`：chart_source_mem_nhds (x : M) : (chartAt H x).sou
rce in 𝓝 x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TangentBundle.continuousLinearMapAt_trivializationAt`：TangentBundle.cont
inuousLinearMapAt_trivializationAt {x₀ x : M} (hx : x in (chartAt H x₀).source) 
: (trivializationAt E (TangentSpace I) x₀)…
-/
lemma eventually_norm_mfderiv_extChartAt_lt (x : M) :
    ∃ C > 0, ∀ᶠ y in 𝓝 x, ‖mfderiv% (extChartAt I x) y‖ < C := by
  rcases eventually_norm_trivializationAt_lt E (fun (x : M) ↦ TangentSpace% x) x
    with ⟨C, C_pos, hC⟩
  refine ⟨C, C_pos, ?_⟩
  have hx : (chartAt H x).source ∈ 𝓝 x := chart_source_mem_nhds H x
  filter_upwards [hC, hx] with y hy h'y
  rwa [← TangentBundle.continuousLinearMapAt_trivializationAt h'y]

set_option backward.isDefEq.respectTransparency false in
/-
**eventually_enorm_mfderiv_extChartAt_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eventually_enorm_mfderiv_extChartAt_lt (x : M) : exists C > (0 : Real>=0),
 forallᶠ y in 𝓝 x, ‖mfderiv% (extChartAt I x) y‖ₑ < C
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupTangentSpace`：∀ {𝕜 : Type u_2} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_1} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {H : Type u_…
· 使用定理 `instContinuousConstSMulTangentSpace`：∀ {𝕜 : Type u_1} [inst : Nontrivial
lyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norm
edSpace 𝕜 E] {H : Type u_…
· 使用引理 `eventually_norm_mfderiv_extChartAt_lt`：eventually_norm_mfderiv_extChartA
t_lt (x : M) : exists C > 0, forallᶠ y in 𝓝 x, ‖mfderiv% (extChartAt I x) y‖ < C
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma eventually_enorm_mfderiv_extChartAt_lt (x : M) :
    ∃ C > (0 : ℝ≥0), ∀ᶠ y in 𝓝 x, ‖mfderiv% (extChartAt I x) y‖ₑ < C := by
  rcases eventually_norm_mfderiv_extChartAt_lt I x with ⟨C, C_pos, hC⟩
  lift C to ℝ≥0 using C_pos.le
  simp only [gt_iff_lt, NNReal.coe_pos] at C_pos
  refine ⟨C, C_pos, ?_⟩
  filter_upwards [hC] with y hy
  simp only [enorm, nnnorm]
  exact_mod_cast hy

set_option backward.isDefEq.respectTransparency false in
/-
**eventually_norm_mfderivWithin_symm_extChartAt_comp_lt** 是 Mathlib 中的一个引理，位于命名空
间 ``。
形式化陈述：eventually_norm_mfderivWithin_symm_extChartAt_comp_lt (x : M) : exists C >
 0, forallᶠ y in 𝓝 x, ‖mfderiv[range I] (extChartAt I x).symm (extChartAt I x y)
‖ < C
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupTangentSpace`：∀ {𝕜 : Type u_2} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_1} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {H : Type u_…
· 使用定理 `instContinuousConstSMulTangentSpace`：∀ {𝕜 : Type u_1} [inst : Nontrivial
lyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norm
edSpace 𝕜 E] {H : Type u_…
· 使用定理 `trivialization_linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → AddCom
mMonoid (E …
· 使用定理 `instMemTrivializationAtlasTrivializationAt`：∀ {B : Type u_2} {F : Type u
_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {E : B → Type u_5}
   [inst_2 : TopologicalSpace (B…
· 使用引理 `eventually_norm_symmL_trivializationAt_lt`：eventually_norm_symmL_trivial
izationAt_lt (x : B) : exists C > 0, forallᶠ y in 𝓝 x, ‖(trivializationAt F E x)
.symmL Real y‖ < C
· 使用定理 `chart_source_mem_nhds`：chart_source_mem_nhds (x : M) : (chartAt H x).sou
rce in 𝓝 x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `PartialEquiv.left_inv`：left_inv {x : α} (h : x in e.source) : e.symm (e 
x) = x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ModelWithCorners.source_eq`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `TangentBundle.symmL_trivializationAt`：TangentBundle.symmL_trivialization
At {x₀ x : M} (hx : x in (chartAt H x₀).source) : (trivializationAt E (TangentSp
ace I) x₀).symmL 𝕜 x = mfd…
-/
lemma eventually_norm_mfderivWithin_symm_extChartAt_comp_lt (x : M) :
    ∃ C > 0, ∀ᶠ y in 𝓝 x, ‖mfderiv[range I] (extChartAt I x).symm (extChartAt I x y)‖ < C := by
  rcases eventually_norm_symmL_trivializationAt_lt E (fun (x : M) ↦ TangentSpace% x) x
    with ⟨C, C_pos, hC⟩
  refine ⟨C, C_pos, ?_⟩
  have hx : (chartAt H x).source ∈ 𝓝 x := chart_source_mem_nhds H x
  filter_upwards [hC, hx] with y hy h'y
  rw [TangentBundle.symmL_trivializationAt h'y] at hy
  have A : (extChartAt I x).symm (extChartAt I x y) = y :=
    (extChartAt I x).left_inv (by simpa using h'y)
  convert! hy using 3 <;> congr

set_option backward.isDefEq.respectTransparency false in
/-
**eventually_norm_mfderivWithin_symm_extChartAt_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eventually_norm_mfderivWithin_symm_extChartAt_lt (x : M) : exists C > 0, f
orallᶠ y in 𝓝[range I] (extChartAt I x x), ‖mfderiv[range I] (extChartAt I x).sy
mm y‖ < C
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupTangentSpace`：∀ {𝕜 : Type u_2} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_1} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {H : Type u_…
· 使用定理 `instContinuousConstSMulTangentSpace`：∀ {𝕜 : Type u_1} [inst : Nontrivial
lyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norm
edSpace 𝕜 E] {H : Type u_…
· 使用引理 `eventually_norm_mfderivWithin_symm_extChartAt_comp_lt`：eventually_norm_m
fderivWithin_symm_extChartAt_comp_lt (x : M) : exists C > 0, forallᶠ y in 𝓝 x, ‖
mfderiv[range I] (extChartAt I x).symm (ext…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ModelWithCorners.left_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `continuousAt_extChartAt_symm`：continuousAt_extChartAt_symm (x : M) : Con
tinuousAt (extChartAt I x).symm ((extChartAt I x) x)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `extChartAt_target_mem_nhdsWithin`：extChartAt_target_mem_nhdsWithin (x : 
M) : (extChartAt I x).target in 𝓝[range I] extChartAt I x x
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `ContinuousAt.preimage_mem_nhds`：ContinuousAt.preimage_mem_nhds {t : Set 
Y} (h : ContinuousAt f x) (ht : t in 𝓝 (f x)) : f ⁻¹' t in 𝓝 x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `PartialEquiv.right_inv`：right_inv {x : β} (h : x in e.target) : e (e.sym
m x) = x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
-/
lemma eventually_norm_mfderivWithin_symm_extChartAt_lt (x : M) :
    ∃ C > 0, ∀ᶠ y in 𝓝[range I] (extChartAt I x x),
    ‖mfderiv[range I] (extChartAt I x).symm y‖ < C := by
  rcases eventually_norm_mfderivWithin_symm_extChartAt_comp_lt I x with ⟨C, C_pos, hC⟩
  refine ⟨C, C_pos, ?_⟩
  have : 𝓝 x = 𝓝 ((extChartAt I x).symm (extChartAt I x x)) := by simp
  rw [this] at hC
  have : ContinuousAt (extChartAt I x).symm (extChartAt I x x) := continuousAt_extChartAt_symm _
  filter_upwards [nhdsWithin_le_nhds (this.preimage_mem_nhds hC),
    extChartAt_target_mem_nhdsWithin x] with y hy h'y
  have : y = (extChartAt I x) ((extChartAt I x).symm y) := by simp [-extChartAt, h'y]
  simp only [preimage_ofPred_eq, mem_ofPred_eq] at hy
  convert! hy

set_option backward.isDefEq.respectTransparency false in
/-
**eventually_enorm_mfderivWithin_symm_extChartAt_lt** 是 Mathlib 中的一个引理，位于命名空间 ``
。
形式化陈述：eventually_enorm_mfderivWithin_symm_extChartAt_lt (x : M) : exists C > (0 
: Real>=0), forallᶠ y in 𝓝[range I] (extChartAt I x x), ‖mfderiv[range I] (extCh
artAt I x).symm y‖ₑ < C
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupTangentSpace`：∀ {𝕜 : Type u_2} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_1} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {H : Type u_…
· 使用定理 `instContinuousConstSMulTangentSpace`：∀ {𝕜 : Type u_1} [inst : Nontrivial
lyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norm
edSpace 𝕜 E] {H : Type u_…
· 使用引理 `eventually_norm_mfderivWithin_symm_extChartAt_lt`：eventually_norm_mfderi
vWithin_symm_extChartAt_lt (x : M) : exists C > 0, forallᶠ y in 𝓝[range I] (extC
hartAt I x x), ‖mfderiv[range I] (extC…
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma eventually_enorm_mfderivWithin_symm_extChartAt_lt (x : M) :
    ∃ C > (0 : ℝ≥0), ∀ᶠ y in 𝓝[range I] (extChartAt I x x),
    ‖mfderiv[range I] (extChartAt I x).symm y‖ₑ < C := by
  rcases eventually_norm_mfderivWithin_symm_extChartAt_lt I x with ⟨C, C_pos, hC⟩
  lift C to ℝ≥0 using C_pos.le
  simp only [gt_iff_lt, NNReal.coe_pos] at C_pos
  refine ⟨C, C_pos, ?_⟩
  filter_upwards [hC] with y hy
  simp only [enorm, nnnorm]
  exact_mod_cast hy

set_option backward.isDefEq.respectTransparency false in
/-- Around any point `x`, the Riemannian distance between two points is controlled by the distance
in the extended chart. In other words, the extended chart is locally Lipschitz. -/
/-
**eventually_riemannianEDist_le_edist_extChartAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eventually_riemannianEDist_le_edist_extChartAt (x : M) : exists C > (0 : R
eal>=0), forallᶠ y in 𝓝 x, riemannianEDist I x y <= C * edist (extChartAt I x x)
 (extChartAt I x y)
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupTangentSpace`：∀ {𝕜 : Type u_2} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_1} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {H : Type u_…
· 使用定理 `instContinuousConstSMulTangentSpace`：∀ {𝕜 : Type u_1} [inst : Nontrivial
lyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norm
edSpace 𝕜 E] {H : Type u_…
· 使用引理 `eventually_enorm_mfderivWithin_symm_extChartAt_lt`：eventually_enorm_mfde
rivWithin_symm_extChartAt_lt (x : M) : exists C > (0 : Real>=0), forallᶠ y in 𝓝[
range I] (extChartAt I x x), ‖mfderiv[r…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.mem_nhdsWithin_iff`：mem_nhdsWithin_iff {t : Set α} : s in 𝓝[t] x 
↔ exists ε > 0, ball x ε inter t subseteq s
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `extChartAt_target_mem_nhdsWithin`：extChartAt_target_mem_nhdsWithin (x : 
M) : (extChartAt I x).target in 𝓝[range I] extChartAt I x x
· 使用定理 `extChartAt_preimage_mem_nhds_of_mem_nhdsWithin`：extChartAt_preimage_mem_
nhds_of_mem_nhdsWithin {s : Set E} {x x' : M} (hx : x' in (extChartAt I x).sourc
e) (hs : s in 𝓝[range I] (extChartAt…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ModelWithCorners.source_eq`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `inter_mem_nhdsWithin`：inter_mem_nhdsWithin (s : Set α) {t : Set α} {a : 
α} (h : t in 𝓝 a) : s inter t in 𝓝[s] a
· 使用定理 `Metric.ball_mem_nhds`：ball_mem_nhds (x : α) {ε : Real} (ε0 : 0 < ε) : ba
ll x ε in 𝓝 x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `chart_source_mem_nhds`：chart_source_mem_nhds (x : M) : (chartAt H x).sou
rce in 𝓝 x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsTopologicalAddTorsor.toContinuousVAdd`：∀ {V : Type u_1} {inst : AddGro
up V} {inst_1 : TopologicalSpace V} {P : Type u_2} {inst_2 : AddTorsor V P}   {i
nst_3 : TopologicalSpace P} […
· 使用定理 `instIsTopologicalAddTorsor_1`：∀ {V : Type u_2} {P : Type u_3} [inst : Se
minormedAddCommGroup V] [inst_1 : PseudoMetricSpace P]   [inst_2 : NormedAddTors
or V P], IsTopolog…
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Convex.segment_subset`：Convex.segment_subset (h : Convex 𝕜 s) {x y : E} 
(hx : x in s) (hy : y in s) : [x -[𝕜] y] subseteq s
· 使用定理 `Convex.inter`：Convex.inter {t : Set E} (hs : Convex 𝕜 s) (ht : Convex 𝕜 
t) : Convex 𝕜 (s inter t)
· 使用定理 `convex_ball`：convex_ball (a : E) (r : Real) : Convex Real (ball a r)
· 使用定理 `ModelWithCorners.convex_range`：convex_range [NormedSpace Real E] : Conve
x Real (range I)
（共 79 条，此处仅展示前 30 条）

--- 原说明 ---
Around any point `x`, the Riemannian distance between two points is controlled b
y the distance
in the extended chart. In other words, the extended chart is locally Lipschitz.
-/
lemma eventually_riemannianEDist_le_edist_extChartAt (x : M) :
    ∃ C > (0 : ℝ≥0), ∀ᶠ y in 𝓝 x,
    riemannianEDist I x y ≤ C * edist (extChartAt I x x) (extChartAt I x y) := by
  /- To construct a path with controlled distance from `x` to `y`, we consider the segment from
  `extChartAt x x` to `extChartAt x y` in the chart, and we push it by `(extChartAt x).symm`. As
  the derivative of the latter is locally bounded, this only multiplies the length by a bounded
  amount. -/
  -- first start from a bound on the derivative
  rcases eventually_enorm_mfderivWithin_symm_extChartAt_lt I x with ⟨C, C_pos, hC⟩
  refine ⟨C, C_pos, ?_⟩
  -- consider a small convex set around `extChartAt x x` where everything is controlled.
  obtain ⟨r, r_pos, hr⟩ : ∃ r > 0,
      ball (extChartAt I x x) r ∩ range I ⊆ (extChartAt I x).target ∩
        {y | ‖mfderiv[range I] (extChartAt I x).symm y‖ₑ < C} :=
    mem_nhdsWithin_iff.1 (inter_mem (extChartAt_target_mem_nhdsWithin x) hC)
  -- pull this set inside `M`: this is the set where we will get the estimate.
  have A : (extChartAt I x) ⁻¹' (ball (extChartAt I x x) r ∩ range I) ∈ 𝓝 x := by
    apply extChartAt_preimage_mem_nhds_of_mem_nhdsWithin (by simp)
    rw [inter_comm]
    exact inter_mem_nhdsWithin _ (ball_mem_nhds _ r_pos)
  -- consider `y` in this good set. Let `η` be the segment in the extended chart, and
  -- `γ` its composition with `(extChartAt x).symm`.
  filter_upwards [A, chart_source_mem_nhds H x] with y hy h'y
  let η := ContinuousAffineMap.lineMap (R := ℝ) (extChartAt I x x) (extChartAt I x y)
  set γ := (extChartAt I x).symm ∘ η
  -- by convexity, the whole segment between `extChartAt x x` and `extChartAt x y` is in the
  -- controlled set.
  have hη : Icc 0 1 ⊆ ⇑η ⁻¹' ((extChartAt I x).target ∩
        {y | ‖mfderiv[range I] (extChartAt I x).symm y‖ₑ < C}) := by
    simp only [← image_subset_iff, ContinuousAffineMap.coe_lineMap_eq,
     ← segment_eq_image_lineMap, η]
    apply Subset.trans _ hr
    exact ((convex_ball _ _).inter I.convex_range).segment_subset (by simp [r_pos]) hy
  simp only [preimage_inter, subset_inter_iff] at hη
  have η_smooth : CMDiff[Icc 0 1] 1 η := by
    apply ContMDiff.contMDiffOn
    rw [contMDiff_iff_contDiff]
    exact ContinuousAffineMap.contDiff _
  -- we can bound the Riemannian distance using the specific path `γ`.
  have : riemannianEDist I x y ≤ pathELength I γ 0 1 := by
    apply riemannianEDist_le_pathELength _ _ _ zero_le_one
    · exact (contMDiffOn_extChartAt_symm x).comp η_smooth hη.1
    · simp [γ, η, ContinuousAffineMap.coe_lineMap_eq]
    · simp [γ, η, ContinuousAffineMap.coe_lineMap_eq, h'y]
  apply this.trans
  -- Finally, we control the length of `γ` thanks to the boundedness of the derivative of
  -- `(extChartAt x).symm` on the whole controlled set.
  rw [← lintegral_fderiv_lineMap_eq_edist, pathELength_eq_lintegral_mfderivWithin_Icc,
    ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  apply setLIntegral_mono' measurableSet_Icc (fun t ht ↦ ?_)
  have : mfderiv[Icc 0 1] γ t =
      (mfderiv[range I] (extChartAt I x).symm (η t)) ∘L (mfderiv[Icc 0 1] η t) := by
    apply mfderivWithin_comp
    · exact mdifferentiableWithinAt_extChartAt_symm (hη.1 ht)
    · exact η_smooth.mdifferentiableOn one_ne_zero t ht
    · exact hη.1.trans (preimage_mono (extChartAt_target_subset_range x))
    · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact uniqueDiffOn_Icc zero_lt_one t ht
  have : mfderiv[Icc 0 1] γ t 1 =
      (mfderiv[range I] (extChartAt I x).symm (η t)) (mfderiv[Icc 0 1] η t 1) := congr($this 1)
  rw [this]
  apply (ContinuousLinearMap.le_opENorm _ _).trans
  gcongr
  · exact (hη.2 ht).le
  · simp only [mfderivWithin_eq_fderivWithin]
    exact le_of_eq rfl

/-- If points are close for the topology, then their Riemannian distance is small. -/
/-
**eventually_riemannianEDist_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：eventually_riemannianEDist_lt (x : M) {c : Real>=0∞} (hc : 0 < c) : forall
ᶠ y in 𝓝 x, riemannianEDist I x y < c
参数：x : M；hc : 0 < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupTangentSpace`：∀ {𝕜 : Type u_2} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_1} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {H : Type u_…
· 使用定理 `instContinuousConstSMulTangentSpace`：∀ {𝕜 : Type u_1} [inst : Nontrivial
lyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norm
edSpace 𝕜 E] {H : Type u_…
· 使用引理 `eventually_riemannianEDist_le_edist_extChartAt`：eventually_riemannianEDi
st_le_edist_extChartAt (x : M) : exists C > (0 : Real>=0), forallᶠ y in 𝓝 x, rie
mannianEDist I x y <= C * edist (ext…
· 使用定理 `ContinuousAt.preimage_mem_nhds`：ContinuousAt.preimage_mem_nhds {t : Set 
Y} (h : ContinuousAt f x) (ht : t in 𝓝 (f x)) : f ⁻¹' t in 𝓝 x
· 使用定理 `continuousAt_extChartAt`：continuousAt_extChartAt (x : M) : ContinuousAt 
(extChartAt I x) x
· 使用定理 `Metric.eball_mem_nhds`：eball_mem_nhds (x : α) {ε : Real>=0∞} (ε0 : 0 < ε
) : eball x ε in 𝓝 x
· 使用定理 `ENNReal.div_pos`：∀ {a b : ENNReal}, a ≠ 0 → b ≠ ⊤ → 0 < a / b
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `ENNReal.lt_div_iff_mul_lt`：∀ {a b c : ENNReal}, b ≠ 0 ∨ c ≠ ⊤ → b ≠ ⊤ ∨ 
c ≠ 0 → (c < a / b ↔ c * b < a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True

--- 原说明 ---
If points are close for the topology, then their Riemannian distance is small.
-/
lemma eventually_riemannianEDist_lt (x : M) {c : ℝ≥0∞} (hc : 0 < c) :
    ∀ᶠ y in 𝓝 x, riemannianEDist I x y < c := by
  rcases eventually_riemannianEDist_le_edist_extChartAt I x with ⟨C, C_pos, hC⟩
  have : (extChartAt I x) ⁻¹' (Metric.eball (extChartAt I x x) (c / C)) ∈ 𝓝 x := by
    apply (continuousAt_extChartAt x).preimage_mem_nhds
    exact Metric.eball_mem_nhds _ (ENNReal.div_pos hc.ne' (by simp))
  filter_upwards [this, hC] with y hy h'y
  apply h'y.trans_lt
  have : edist (extChartAt I x x) (extChartAt I x y) < c / C := by
    simpa only [mem_preimage, Metric.mem_eball'] using hy
  rwa [ENNReal.lt_div_iff_mul_lt, mul_comm] at this
  · exact Or.inl (mod_cast C_pos.ne')
  · simp

set_option backward.isDefEq.respectTransparency false in
/-- Any neighborhood of `x` contains all the points which are close enough to `x` for the
Riemannian distance, `ℝ≥0` version. -/
/-
**setOfPred_riemannianEDist_lt_subset_nhds** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：setOfPred_riemannianEDist_lt_subset_nhds [RegularSpace M] {x : M} {s : Set
 M} (hs : s in 𝓝 x) : exists c > (0 : Real>=0), {y | riemannianEDist I x y < c} 
subseteq s
参数：hs : s in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupTangentSpace`：∀ {𝕜 : Type u_2} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_1} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {H : Type u_…
· 使用定理 `instContinuousConstSMulTangentSpace`：∀ {𝕜 : Type u_1} [inst : Nontrivial
lyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norm
edSpace 𝕜 E] {H : Type u_…
· 使用引理 `eventually_enorm_mfderiv_extChartAt_lt`：eventually_enorm_mfderiv_extChar
tAt_lt (x : M) : exists C > (0 : Real>=0), forallᶠ y in 𝓝 x, ‖mfderiv% (extChart
At I x) y‖ₑ < C
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `extChartAt_source_mem_nhds`：extChartAt_source_mem_nhds (x : M) : (extCha
rtAt I x).source in 𝓝 x
· 使用定理 `exists_mem_nhds_isClosed_subset`：exists_mem_nhds_isClosed_subset {x : X}
 {s : Set X} (h : s in 𝓝 x) : exists t in 𝓝 x, IsClosed t ∧ t subseteq s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ModelWithCorners.source_eq`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `nhds_basis_opens'`：nhds_basis_opens' (x : X) : (𝓝 x).HasBasis (fun s : S
et X => s in 𝓝 x ∧ IsOpen s) fun x => x
· 使用定理 `Metric.mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists ε > 0, ball x ε su
bseteq s
· 使用定理 `extChartAt_preimage_mem_nhds`：extChartAt_preimage_mem_nhds {x : M} (ht :
 t in 𝓝 x) : (extChartAt I x).symm ⁻¹' t in 𝓝 ((extChartAt I x) x)
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用引理 `Manifold.exists_lt_locally_constant_of_riemannianEDist_lt`：exists_lt_loc
ally_constant_of_riemannianEDist_lt (hr : riemannianEDist I x y < r) (hab : a < 
b) : exists γ : Real -> M, γ a = x ∧ γ b = y ∧ …
· 使用定理 `instENormSMulClass`：∀ {α : Type u_1} {β : Type u_2} [inst : SeminormedRi
ng α] [inst_1 : SeminormedAddGroup β] [inst_2 : SMul α β]   [NormSMulClass α β],
 ENormSM…
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
（共 96 条，此处仅展示前 30 条）

--- 原说明 ---
Any neighborhood of `x` contains all the points which are close enough to `x` fo
r the
Riemannian distance, `ℝ≥0` version.
-/
lemma setOfPred_riemannianEDist_lt_subset_nhds [RegularSpace M] {x : M} {s : Set M} (hs : s ∈ 𝓝 x) :
    ∃ c > (0 : ℝ≥0), {y | riemannianEDist I x y < c} ⊆ s := by
  /- Consider a closed neighborhood `u` of `x` on which the derivative of the extended chart is
  bounded by some `C`, contained in `s`, then an open neighborhood `v` of `x` inside `u`,
  and finally `r` small enough that the ball of radius `r` in the extended chart is contained in
  the image of `v`.

  We claim that points at Riemannian distance at most `r / C` of `x` are inside `u` (and therefore
  inside `s`). To prove this, consider a path of length at most `r / C` starting from `x`. While
  it stays inside `u`, then by the derivative control its image in the extended chart has length
  at most `r`, so it cannot exit the ball of radius `r`, which means that in the manifold it is
  inside `v` (which is strictly inside `u`). This means that the path will stay inside `u` for
  a little bit longer, by openness of `v`. Iterating this argument, it follows that the path will
  remain inside `u` for the whole time interval `[0, 1]`. In particular, its right endpoint is
  inside `u`, as desired.

  The formalization of this argument goes through the lemma
  `IsClosed.Icc_subset_of_forall_mem_nhdsGT_of_mem` which gives an induction-like principle over
  real intervals.
  -/
  -- first introduce a neighborhood where the derivative of the extended chart is bounded by `C`
  rcases eventually_enorm_mfderiv_extChartAt_lt I x with ⟨C, C_pos, hC⟩
  -- let `u` be a closed neighborhood, inside `s`, with the derivative control
  obtain ⟨u, u_mem, u_closed, us, hu, uc⟩ : ∃ u ∈ 𝓝 x, IsClosed u ∧ u ⊆ s
      ∧ u ⊆ {y | ‖mfderiv% (extChartAt I x) y‖ₑ < C} ∧ u ⊆ (extChartAt I x).source := by
    have := Filter.inter_mem (Filter.inter_mem hs hC) (extChartAt_source_mem_nhds (I := I) x)
    rcases exists_mem_nhds_isClosed_subset this with ⟨u, u_mem, u_closed, hu⟩
    simp only [subset_inter_iff] at hu
    exact ⟨u, u_mem, u_closed, hu.1.1, hu.1.2, hu.2⟩
  have uc' : u ⊆ (chartAt H x).source := by simpa [extChartAt_source I x] using uc
  -- let `v` be a smaller open neighborhood, inside `u`.
  obtain ⟨v, ⟨v_mem, v_open⟩, hv⟩ : ∃ v, (v ∈ 𝓝 x ∧ IsOpen v) ∧ v ⊆ u :=
    (nhds_basis_opens' x).mem_iff.1 u_mem
  -- let `r > 0` be small enough that, in the extended chart, the ball of radius `r` is contained
  -- in the image of `v`.
  obtain ⟨r, r_pos, hr⟩ : ∃ r > 0, ball (extChartAt I x x) r ⊆ (extChartAt I x).symm ⁻¹' v :=
    Metric.mem_nhds_iff.1 (extChartAt_preimage_mem_nhds v_mem)
  lift r to ℝ≥0 using r_pos.le
  simp only [gt_iff_lt, NNReal.coe_pos] at r_pos
  -- the desired constant will be `c := r / C`
  refine ⟨r / C, by positivity, ?_⟩
  intro y hy
  -- consider a path `γ` of length `< r / C` from `x` to a point `y`. We will show that `y` belongs
  -- to `u`.
  rcases exists_lt_locally_constant_of_riemannianEDist_lt hy zero_lt_one
    with ⟨γ, hγx, hγy, γ_smooth, hγ, -⟩
  let A := γ ⁻¹' u
  have zero_mem : 0 ∈ A := by simpa  [hγx, A] using mem_of_mem_nhds u_mem
  have A_closed : IsClosed (A ∩ Icc 0 1) :=
    (u_closed.preimage γ_smooth.continuous).inter isClosed_Icc
  suffices Icc 0 1 ⊆ A by
    apply us
    have : 1 ∈ A := this ⟨zero_le_one, le_rfl⟩
    simpa [A, hγy, us]
  apply A_closed.Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset zero_mem
  rintro t₁ ⟨ht₁0, ht₁1⟩ t₁_mem
  suffices γ t₁ ∈ v from
    γ_smooth.continuous.continuousWithinAt <| mem_of_superset (v_open.mem_nhds this) hv
  let γ' := extChartAt I x ∘ γ
  have hC : CMDiff[Icc 0 t₁] 1 γ' :=
    contMDiffOn_extChartAt.comp (I' := I) (t := (chartAt H x).source)
      γ_smooth.contMDiffOn (fun t' ht' ↦ uc' <| t₁_mem ht')
  have : ‖γ' t₁ - γ' 0‖ₑ < r := by
    rcases ht₁0.eq_or_lt with rfl | h't'
    · simp [r_pos]
    calc
      ‖γ' t₁ - γ' 0‖ₑ
    _ ≤ ∫⁻ t' in Icc 0 t₁, ‖derivWithin γ' (Icc 0 t₁) t'‖ₑ := by
      apply enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc _ ht₁0
      rwa [← contMDiffOn_iff_contDiffOn]
    _ = ∫⁻ t' in Icc 0 t₁, ‖mfderiv[Icc 0 t₁] γ' t' 1‖ₑ := by
      simp_rw [← fderivWithin_derivWithin, mfderivWithin_eq_fderivWithin]
      rfl
    _ ≤ ∫⁻ t' in Icc 0 t₁, C * ‖mfderiv[Icc 0 t₁] γ t' 1‖ₑ := by
      apply setLIntegral_mono' measurableSet_Icc (fun t' ht' ↦ ?_)
      have : mfderiv[Icc 0 t₁] γ' t' =
          (mfderiv% (extChartAt I x) (γ t')) ∘L (mfderiv[Icc 0 t₁] γ t') := by
        apply mfderiv_comp_mfderivWithin
        · refine mdifferentiableAt_extChartAt (uc' ?_)
          apply t₁_mem ht'
        · exact (γ_smooth.mdifferentiable one_ne_zero).mdifferentiableOn _ ht'
        · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
          exact uniqueDiffOn_Icc h't' _ ht'
      have : mfderiv[Icc 0 t₁] γ' t' 1 =
          (mfderiv% (extChartAt I x) (γ t')) (mfderiv[Icc 0 t₁] γ t' 1) :=
        congr($this 1)
      rw [this]
      apply (ContinuousLinearMap.le_opENorm _ _).trans
      gcongr
      refine (hu ?_).le
      apply t₁_mem ht'
    _ = C * pathELength I γ 0 t₁ := by
      rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top,
          pathELength_eq_lintegral_mfderivWithin_Icc]
    _ ≤ C * pathELength I γ 0 1 := by
      gcongr
    _ < C * (r / C) := by
      gcongr
      · exact ENNReal.coe_ne_top
      · exact hγ.trans_eq (ENNReal.coe_div C_pos.ne')
    _ = r := (ENNReal.eq_div_iff (by simpa using C_pos.ne') ENNReal.coe_ne_top).mp rfl
  have : γ' t₁ ∈ (extChartAt I x).symm ⁻¹' v := by
    apply hr
    rw [← Metric.eball_coe, Metric.mem_eball, edist_eq_enorm_sub]
    convert! this
    simp [γ', hγx]
  convert! mem_preimage.1 this
  simp only [Function.comp_apply, γ', (extChartAt I x).left_inv <| uc <| t₁_mem
    (right_mem_Icc.mpr ht₁0)]

@[deprecated (since := "2026-07-09")]
alias setOf_riemannianEDist_lt_subset_nhds := setOfPred_riemannianEDist_lt_subset_nhds

/-- Any neighborhood of `x` contains all the points which are close enough to `x` for the
Riemannian distance, `ℝ≥0∞` version. -/
/-
**setOfPred_riemannianEDist_lt_subset_nhds'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：setOfPred_riemannianEDist_lt_subset_nhds' [RegularSpace M] {x : M} {s : Se
t M} (hs : s in 𝓝 x) : exists c > 0, {y | riemannianEDist I x y < c} subseteq s
参数：hs : s in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupTangentSpace`：∀ {𝕜 : Type u_2} [inst : Nontrivi
allyNormedField 𝕜] {E : Type u_1} [inst_1 : NormedAddCommGroup E]   [inst_2 : No
rmedSpace 𝕜 E] {H : Type u_…
· 使用定理 `instContinuousConstSMulTangentSpace`：∀ {𝕜 : Type u_1} [inst : Nontrivial
lyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norm
edSpace 𝕜 E] {H : Type u_…
· 使用引理 `setOfPred_riemannianEDist_lt_subset_nhds`：setOfPred_riemannianEDist_lt_s
ubset_nhds [RegularSpace M] {x : M} {s : Set M} (hs : s in 𝓝 x) : exists c > (0 
: Real>=0), {y | riemannianEDi…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a

--- 原说明 ---
Any neighborhood of `x` contains all the points which are close enough to `x` fo
r the
Riemannian distance, `ℝ≥0∞` version.
-/
lemma setOfPred_riemannianEDist_lt_subset_nhds' [RegularSpace M] {x : M} {s : Set M}
    (hs : s ∈ 𝓝 x) :
    ∃ c > 0, {y | riemannianEDist I x y < c} ⊆ s := by
  rcases setOfPred_riemannianEDist_lt_subset_nhds I hs with ⟨c, c_pos, hc⟩
  exact ⟨c, mod_cast c_pos, hc⟩

@[deprecated (since := "2026-07-09")]
alias setOf_riemannianEDist_lt_subset_nhds' := setOfPred_riemannianEDist_lt_subset_nhds'

variable (M) in
/-- The pseudoemetric space structure associated to a Riemannian metric on a manifold. Designed
so that the topology is defeq to the original one.

This should only be used when constructing data in specific situations. To develop the theory,
one should rather assume that there is an already existing emetric space structure, which satisfies
additionally the predicate `IsRiemannianManifold I M`. -/
/-
**PseudoEMetricSpace.ofRiemannianMetric** 是 Mathlib 中的一个定义，位于命名空间 `PseudoEMetric
Space`。
形式化陈述：{E : Type u_1} →   [inst : NormedAddCommGroup E] →     [inst_1 : NormedSpa
ce ℝ E] →       {H : Type u_2} →         [inst_2 : TopologicalSpace H] →        
   (I : ModelWithCorners ℝ E H) →             (M : Type u_3) →               [in
st_3 : TopologicalSpace M] →                 [inst_4 : ChartedSpace H M] →      
             [inst_5 : Bundle.RiemannianBundle fun x => TangentSpace I x] →     
                [inst_6 : IsManifold I 1 M] →                       [IsContinuou
sRiemannianBundle E fun x => TangentSpace I x] →                         [Regula
rSpace M] → PseudoEMetricSpace M
参数：I : ModelWithCorners ℝ E H；M : Type u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pseudoemetric space structure associated to a Riemannian metric on a manifol
d. Designed
so that the topology is defeq to the original one.

This should only be used when constructing data in specific situations. To devel
op the theory,
one should rather assume that there is an already existing emetric space structu
re, which satisfies
additionally the predicate `IsRiemannianManifold I M`.
-/
@[reducible] def PseudoEMetricSpace.ofRiemannianMetric [RegularSpace M] : PseudoEMetricSpace M :=
  PseudoEMetricSpace.ofEDistOfTopology (riemannianEDist I (M := M))
    (fun _ ↦ riemannianEDist_self)
    (fun _ _ ↦ riemannianEDist_comm)
    (fun _ _ _ ↦ riemannianEDist_triangle)
    (fun x ↦ (basis_sets (𝓝 x)).to_hasBasis'
      (fun _ hs ↦ setOfPred_riemannianEDist_lt_subset_nhds' I hs)
      (fun _ hc ↦ eventually_riemannianEDist_lt I x hc))

@[deprecated (since := "2026-01-08")]
noncomputable alias PseudoEmetricSpace.ofRiemannianMetric := PseudoEMetricSpace.ofRiemannianMetric

/-- Given a manifold with a Riemannian metric, consider the associated Riemannian distance. Then
by definition the distance is the infimum of the length of paths between the points, i.e., the
manifold satisfies the `IsRiemannianManifold I M` predicate. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a manifold with a Riemannian metric, consider the associated Riemannian di
stance. Then
by definition the distance is the infimum of the length of paths between the poi
nts, i.e., the
manifold satisfies the `IsRiemannianManifold I M` predicate.
-/
instance [RegularSpace M] :
    letI : PseudoEMetricSpace M := .ofRiemannianMetric I M
    IsRiemannianManifold I M := by
  let : PseudoEMetricSpace M := .ofRiemannianMetric I M
  exact ⟨fun x y ↦ rfl⟩

variable (M) in
/-- The emetric space structure associated to a Riemannian metric on a manifold. Designed
so that the topology is defeq to the original one.

This should only be used when constructing data in specific situations. To develop the theory,
one should rather assume that there is an already existing emetric space structure, which satisfies
additionally the predicate `IsRiemannianManifold I M`. -/
/-
**EMetricSpace.ofRiemannianMetric** 是 Mathlib 中的一个定义，位于命名空间 `EMetricSpace`。
形式化陈述：{E : Type u_1} →   [inst : NormedAddCommGroup E] →     [inst_1 : NormedSpa
ce ℝ E] →       {H : Type u_2} →         [inst_2 : TopologicalSpace H] →        
   (I : ModelWithCorners ℝ E H) →             (M : Type u_3) →               [in
st_3 : TopologicalSpace M] →                 [inst_4 : ChartedSpace H M] →      
             [inst_5 : Bundle.RiemannianBundle fun x => TangentSpace I x] →     
                [inst_6 : IsManifold I 1 M] →                       [IsContinuou
sRiemannianBundle E fun x => TangentSpace I x] → [T3Space M] → EMetricSpace M
参数：I : ModelWithCorners ℝ E H；M : Type u_3。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `T3Space.toRegularSpace`：∀ {X : Type u} {inst : TopologicalSpace X} [self
 : T3Space X], RegularSpace X

--- 原说明 ---
The emetric space structure associated to a Riemannian metric on a manifold. Des
igned
so that the topology is defeq to the original one.

This should only be used when constructing data in specific situations. To devel
op the theory,
one should rather assume that there is an already existing emetric space structu
re, which satisfies
additionally the predicate `IsRiemannianManifold I M`.
-/
@[reducible] def EMetricSpace.ofRiemannianMetric [T3Space M] : EMetricSpace M :=
  letI : PseudoEMetricSpace M := .ofRiemannianMetric I M
  EMetricSpace.ofT0PseudoEMetricSpace M

@[deprecated (since := "2026-01-08")]
noncomputable alias EmetricSpace.ofRiemannianMetric := EMetricSpace.ofRiemannianMetric

end

