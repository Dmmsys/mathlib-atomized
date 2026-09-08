/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Geometry.Manifold.ContMDiff.Basic
public import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Notation
public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-! # Manifold structure on real intervals

The manifold structure on real intervals is defined in `Mathlib.Geometry.Manifold.Instances.Real`.
We relate it to the manifold structure on the real line, by showing that the inclusion
(`contMDiff_subtypeVal_Icc`) and projection (`contMDiffOn_projIcc`) are smooth, and showing that
a function defined on the interval is smooth iff its composition with the projection is smooth on
the interval in `ℝ` (see `contMDiffOn_comp_projIcc_iff` and friends).

We also define `1 : TangentSpace (𝓡∂ 1) z`, and relate it to `1` in the real line.

- `isSmoothEmbedding_subtypeVal_Icc`: the inclusion `Icc x y → ℝ` is a smooth embedding,
  and in particular smooth (`contMDiff_subtypeVal_Icc`)
- `contMDiff_iff_comp_subtypeVal_Icc`: a function `f : M → Icc x y` is smooth iff
  its composition with the inclusion into `ℝ` is smooth

## TODO

This file can be thoroughly rewritten once mathlib has a good theory of smooth submersions.
Once this is done,
- prove the projection `ℝ → Icc x y` is a smooth submersion, hence smooth
- use this to simplify the proof that `f : Icc x y → M` is smooth iff the composition `ℝ → M`
  with the projection `ℝ → Icc x y` is
-/

@[expose] public section

open Set WithLp
open scoped Manifold Topology

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : WithTop ℕ∞}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (x : ℝ) : One (TangentSpace 𝓘(ℝ) x) where
  one := (1 : ℝ)

/-- Unit vector in the tangent space to a segment, as the image of the unit vector in the real line
under the canonical projection. It is also mapped to the unit vector in the real line through
the canonical injection, see `mfderiv_subtypeVal_Icc_one`.

Note that one cannot abuse defeqs for this definition: this is *not* the same as the vector
`fun _ ↦ 1` in `EuclideanSpace ℝ (Fin 1)` through defeqs, as one of the charts of `Icc x y` is
orientation-reversing. -/
irreducible_def oneTangentSpaceIcc {x y : ℝ} [h : Fact (x < y)] (z : Icc x y) :
    TangentSpace (𝓡∂ 1) z :=
  mfderiv[Icc x y] (Set.projIcc x y h.out.le) z 1

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {x y : ℝ} [h : Fact (x < y)] (z : Icc x y) : One (TangentSpace (𝓡∂ 1) z) where
  one := oneTangentSpaceIcc z

variable {x y : ℝ} [h : Fact (x < y)] {n : WithTop ℕ∞}

open Manifold IsManifold

/-- The inclusion map from a closed segment to `ℝ` is a smooth immersion -/
/-
**isImmersionOfComplement_subtypeVal_Icc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isImmersionOfComplement_subtypeVal_Icc : IsImmersionOfComplement Unit (𝓡∂ 
1) 𝓘(Real) n (fun (z : Icc x y) => (z : Real))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用引理 `Manifold.IsImmersionAtOfComplement.mk_of_continuousAt`：mk_of_continuousA
t {f : M -> N} {x : M} (hf : ContinuousAt f x) (equiv : (E × F) ≃L[𝕜] E'') (domC
hart : OpenPartialHomeomorph M H) (codChart…
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
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
· 使用引理 `mem_chart_source`：mem_chart_source (H : Type*) {M : Type*} [TopologicalS
pace H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : x in (chartAt H x).sou
rce
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Homeomorph.toOpenPartialHomeomorph_source`：∀ {X : Type u_1} {Y : Type u_
3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] (e : X ≃ₜ Y),   e.t
oOpenPartialHomeomorph.source =…
· 使用定理 `IsManifold.chart_mem_maximalAtlas`：chart_mem_maximalAtlas [IsManifold I 
n M] (x : M) : chartAt H x in maximalAtlas I n M
· 使用引理 `OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn`：OpenPartialHomeom
orph.mem_maximalAtlas_of_contMDiffOn [IsManifold I n M] (φ : OpenPartialHomeomor
ph M H) (hφ : ContMDiffOn I I n φ φ.source)…
· 使用定理 `IsManifold.instOfTopWithTopENat`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSp
ace 𝕜 E] {H : Type u_…
· 使用定理 `ContDiff.add`：ContDiff.add {f g : E -> F} (hf : ContDiff 𝕜 n f) (hg : Co
ntDiff 𝕜 n g) : ContDiff 𝕜 n fun x => f x + g x
· 使用定理 `contDiff_const`：contDiff_const {c : F} : ContDiff 𝕜 n fun _ : E => c
· 使用定理 `contDiff_id`：contDiff_id : ContDiff 𝕜 n (id : E -> E)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Homeomorph.toOpenPartialHomeomorph_apply`：∀ {X : Type u_1} {Y : Type u_3
} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] (e : X ≃ₜ Y),   ↑e.t
oOpenPartialHomeomorph = ⇑e
· 使用定理 `Homeomorph.toOpenPartialHomeomorph_symm_apply`：∀ {X : Type u_1} {Y : Typ
e u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] (e : X ≃ₜ Y),  
 ↑e.toOpenPartialHomeomorph.symm = …
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.addLeft_symm`：∀ {G : Type u_5} [inst : AddGroup G] (a : G), Equiv.
symm (Equiv.addLeft a) = Equiv.addLeft (-a)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Homeomorph.toOpenPartialHomeomorph_target`：∀ {X : Type u_1} {Y : Type u_
3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] (e : X ≃ₜ Y),   e.t
oOpenPartialHomeomorph.target =…
（共 107 条，此处仅展示前 30 条）

--- 原说明 ---
The inclusion map from a closed segment to `ℝ` is a smooth immersion
-/
lemma isImmersionOfComplement_subtypeVal_Icc :
    IsImmersionOfComplement Unit (𝓡∂ 1) 𝓘(ℝ) n (fun (z : Icc x y) ↦ (z : ℝ)) := by
  intro z
  let φ₀ := ContinuousLinearEquiv.prodUnique ℝ (EuclideanSpace ℝ (Fin 1)) Unit
  let φ : (EuclideanSpace ℝ (Fin 1) × Unit) ≃L[ℝ] ℝ :=
    φ₀.trans (PiLp.equivOfUnique 2 ℝ (fun (_ : Fin 1) ↦ ℝ))
  by_cases hz : ↑z < y
  · -- At all points but `y`, the correct codomain chart maps `a` to `a + x`.
    apply IsImmersionAtOfComplement.mk_of_continuousAt (by fun_prop) φ
      (chartAt (EuclideanHalfSpace 1) z) (Homeomorph.addLeft (-x)).toOpenPartialHomeomorph
      (mem_chart_source _ z) (by simp [Homeomorph.addLeft]) (chart_mem_maximalAtlas _) ?_; swap
    · apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
      · have : ContDiff ℝ n (fun y ↦ -x + y) := by fun_prop
        simpa [contMDiffOn_iff_contDiffOn, contDiffOn_univ]
      · have : ContDiff ℝ n (fun y ↦ x + y) := by fun_prop
        simpa [contMDiffOn_iff_contDiffOn, contDiffOn_univ, Homeomorph.addLeft]
    intro z' hz'
    obtain ⟨⟨u, rfl⟩, hu⟩ :
        (∃ y, ⇑(𝓡∂ 1) y = z') ∧ ⇑(𝓡∂ 1).symm z' ∈ (IccLeftChart x y).target := by
      simpa [hz] using! hz'
    replace hu : ofLp u.val 0 ≤ y - x := by
      apply le_of_lt
      simpa [modelWithCornersEuclideanHalfSpace_symm_apply, max_eq_left u.property] using! hu
    simp [hz, φ, φ₀, modelWithCornersEuclideanHalfSpace_symm_apply, u.property,
      IccLeftChart_symm_apply_of_le hu]
  · -- At the right boundary point, the correct codomain chart is mapping `a` to `y - a`.
    apply IsImmersionAtOfComplement.mk_of_continuousAt (by fun_prop) φ
      (chartAt (EuclideanHalfSpace 1) z)
      (Homeomorph.pointReflection (y / 2)).toOpenPartialHomeomorph (mem_chart_source _ z)
      (by simp [Homeomorph.pointReflection]) (chart_mem_maximalAtlas _) ?_; swap
    · apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
      · have : ContDiff ℝ n ((fun v ↦ v + y / 2) ∘ fun x ↦ y / 2 - x) := by fun_prop
        simpa [contMDiffOn_iff_contDiffOn, contDiffOn_univ]
      · have : ContDiff ℝ n ((fun v ↦ -v + y / 2) ∘ fun p' ↦ p' - y / 2) := by fun_prop
        simpa [contMDiffOn_iff_contDiffOn, contDiffOn_univ]
    intro z' hz'
    obtain ⟨⟨u, rfl⟩, hu⟩ :
        (∃ y, ⇑(𝓡∂ 1) y = z') ∧ ⇑(𝓡∂ 1).symm z' ∈ (IccRightChart x y).target := by
      simpa [hz] using! hz'
    replace hu : ofLp u.val 0 ≤ y - x := by
      apply le_of_lt
      simpa [modelWithCornersEuclideanHalfSpace_symm_apply, max_eq_left u.property] using! hu
    simp [hz, φ, φ₀, modelWithCornersEuclideanHalfSpace_symm_apply, u.property,
      IccRightChart_symm_apply_of_le hu, Equiv.pointReflection_apply]
    linarith

/-- The inclusion map from a closed segment to `ℝ` is a smooth embedding -/
/-
**isSmoothEmbedding_subtypeVal_Icc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isSmoothEmbedding_subtypeVal_Icc : IsSmoothEmbedding (𝓡∂ 1) 𝓘(Real) n (fun
 (z : Icc x y) => (z : Real))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Manifold.IsImmersionOfComplement.isImmersion`：isImmersion (h : IsImmersi
onOfComplement F I J n f) : IsImmersion I J n f
· 使用引理 `isImmersionOfComplement_subtypeVal_Icc`：isImmersionOfComplement_subtypeV
al_Icc : IsImmersionOfComplement Unit (𝓡∂ 1) 𝓘(Real) n (fun (z : Icc x y) => (z 
: Real))
· 使用引理 `Topology.IsEmbedding.subtypeVal`：Topology.IsEmbedding.subtypeVal : IsEmb
edding ((↑) : Subtype p -> X)

--- 原说明 ---
The inclusion map from a closed segment to `ℝ` is a smooth embedding
-/
lemma isSmoothEmbedding_subtypeVal_Icc :
    IsSmoothEmbedding (𝓡∂ 1) 𝓘(ℝ) n (fun (z : Icc x y) ↦ (z : ℝ)) :=
  ⟨isImmersionOfComplement_subtypeVal_Icc.isImmersion, Topology.IsEmbedding.subtypeVal⟩

/-- The inclusion map from of a closed segment to `ℝ` is smooth in the manifold sense. -/
/-
**contMDiff_subtypeVal_Icc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：contMDiff_subtypeVal_Icc : CMDiff n (fun (z : Icc x y) => (z : Real))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.of_le`：ContMDiff.of_le (hf : ContMDiff I I' n f) (le : m <= n)
 : ContMDiff I I' m f
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Manifold.IsImmersionOfComplement.contMDiff`：contMDiff (h : IsImmersionOf
Complement F I J n f) : CMDiff n f
· 使用引理 `isImmersionOfComplement_subtypeVal_Icc`：isImmersionOfComplement_subtypeV
al_Icc : IsImmersionOfComplement Unit (𝓡∂ 1) 𝓘(Real) n (fun (z : Icc x y) => (z 
: Real))
· 使用定理 `OrderTop.le_top`：∀ {α : Type u} {inst : LE α} [self : OrderTop α] (a : α
), a ≤ ⊤

--- 原说明 ---
The inclusion map from of a closed segment to `ℝ` is smooth in the manifold sens
e.
-/
lemma contMDiff_subtypeVal_Icc : CMDiff n (fun (z : Icc x y) ↦ (z : ℝ)) :=
  isImmersionOfComplement_subtypeVal_Icc.contMDiff.of_le (OrderTop.le_top n)

@[deprecated (since := "2026-07-22")]
alias contMDiff_subtype_coe_Icc := contMDiff_subtypeVal_Icc

/-- A function `f : M → Icc x y` is smooth iff its composition with the inclusion
into `ℝ` is smooth. -/
/-
**contMDiff_iff_comp_subtypeVal_Icc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：contMDiff_iff_comp_subtypeVal_Icc {f : M -> Icc x y} : CMDiff n f ↔ Contin
uous f ∧ CMDiff n ((fun (z : Icc x y) => (z : Real)) ∘ f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContMDiff.iff_comp_isImmersionOfComplement`：∀ {𝕜 : Type u_1} [inst : Non
triviallyNormedField 𝕜] {E : Type u_2} {E''' : Type u_4} {E'' : Type u} {F : Typ
e u_5}   [inst_1 : NormedAddComm…
· 使用引理 `isImmersionOfComplement_subtypeVal_Icc`：isImmersionOfComplement_subtypeV
al_Icc : IsImmersionOfComplement Unit (𝓡∂ 1) 𝓘(Real) n (fun (z : Icc x y) => (z 
: Real))
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A function `f : M → Icc x y` is smooth iff its composition with the inclusion
into `ℝ` is smooth.
-/
lemma contMDiff_iff_comp_subtypeVal_Icc {f : M → Icc x y} :
    CMDiff n f ↔ Continuous f ∧ CMDiff n ((fun (z : Icc x y) ↦ (z : ℝ)) ∘ f) := by
  rw [← ContMDiff.iff_comp_isImmersionOfComplement isImmersionOfComplement_subtypeVal_Icc]

/-- The projection from `ℝ` to a closed segment is smooth on the segment, in the manifold sense. -/
/-
**contMDiffOn_projIcc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：contMDiffOn_projIcc : CMDiff[Icc x y] n (Set.projIcc x y h.out.le)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contMDiffWithinAt_iff`：contMDiffWithinAt_iff : ContMDiffWithinAt I I' n 
f s x ↔ ContinuousWithinAt f s x ∧ ContDiffWithinAt 𝕜 n (extChartAt I' (f x) ∘ f
 ∘ (extChar…
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `continuous_projIcc`：continuous_projIcc : Continuous (projIcc a b h)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contDiff_euclidean`：contDiff_euclidean {n : WithTop Nat∞} : ContDiff 𝕜 n
 f ↔ forall i, ContDiff 𝕜 n fun x => f x i
· 使用定理 `ContDiff.sub`：ContDiff.sub {f g : E -> F} (hf : ContDiff 𝕜 n f) (hg : Co
ntDiff 𝕜 n g) : ContDiff 𝕜 n fun x => f x - g x
· 使用定理 `contDiff_id`：contDiff_id : ContDiff 𝕜 n (id : E -> E)
· 使用定理 `contDiff_const`：contDiff_const {c : F} : ContDiff 𝕜 n fun _ : E => c
· 使用定理 `ContDiffWithinAt.congr_of_eventuallyEq_of_mem`：ContDiffWithinAt.congr_of
_eventuallyEq_of_mem (h : ContDiffWithinAt 𝕜 n f s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx
 : x in s) : ContDiffWithinAt 𝕜 n f…
· 使用定理 `ContDiff.contDiffWithinAt`：ContDiff.contDiffWithinAt (h : ContDiff 𝕜 n f
) : ContDiffWithinAt 𝕜 n f s x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `PiLp.ext`：∀ {p : ENNReal} {ι : Type u_1} {α : ι → Type u_2} {x y : PiLp 
p α}, (∀ (i : ι), x.ofLp i = y.ofLp i) → x = y
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
The projection from `ℝ` to a closed segment is smooth on the segment, in the man
ifold sense.
-/
lemma contMDiffOn_projIcc : CMDiff[Icc x y] n (Set.projIcc x y h.out.le) := by
  intro z hz
  rw [contMDiffWithinAt_iff]
  refine ⟨by apply ContinuousAt.continuousWithinAt; fun_prop, ?_⟩
  -- We come back to the definition: we should check that, in each chart, the map is smooth
  -- There are two charts, and we check things separately in each of them using the
  -- explicit formulas.
  suffices ContDiffWithinAt ℝ n _ (Icc x y) z by simpa
  split_ifs with h'z
  · have : ContDiff ℝ n (fun (w : ℝ) ↦
        (show EuclideanSpace ℝ (Fin 1) from toLp 2 fun (_ : Fin 1) ↦ w - x)) := by
      dsimp
      apply contDiff_euclidean.2 (fun i ↦ by fun_prop)
    apply this.contDiffWithinAt.congr_of_eventuallyEq_of_mem _ hz
    filter_upwards [self_mem_nhdsWithin] with w hw
    ext i
    suffices max x (min y w) - x = w - x by
      simpa [modelWithCornersEuclideanHalfSpace, IccLeftChart]
    rw [max_eq_right, min_eq_right hw.2]
    simp [hw.1, h.out.le]
  · have : ContDiff ℝ n (fun (w : ℝ) ↦
        (show EuclideanSpace ℝ (Fin 1) from toLp 2 fun (_ : Fin 1) ↦ y - w)) := by
      dsimp
      apply contDiff_euclidean.2 (fun i ↦ by fun_prop)
    apply this.contDiffWithinAt.congr_of_eventuallyEq_of_mem _ hz
    filter_upwards [self_mem_nhdsWithin] with w hw
    ext i
    suffices y - max x (min y w) = y - w by
      simpa [modelWithCornersEuclideanHalfSpace, IccRightChart]
    rw [max_eq_right, min_eq_right hw.2]
    simp [hw.1, h.out.le]
/-
**contMDiffOn_comp_projIcc_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：contMDiffOn_comp_projIcc_iff {f : Icc x y -> M} : CMDiff[Icc x y] n (f ∘ (
Set.projIcc x y h.out.le)) ↔ CMDiff n f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.projIcc_val`：projIcc_val (x : Icc a b) : projIcc a b h x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ContMDiffOn.comp_contMDiff`：ContMDiffOn.comp_contMDiff {t : Set M'} {g :
 M' -> M''} (hg : ContMDiffOn I' I'' n g t) (hf : ContMDiff I I' n f) (ht : fora
ll x, f x in t) …
· 使用引理 `contMDiff_subtypeVal_Icc`：contMDiff_subtypeVal_Icc : CMDiff n (fun (z : 
Icc x y) => (z : Real))
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `ContMDiff.comp_contMDiffOn`：ContMDiff.comp_contMDiffOn {f : M -> M'} {g 
: M' -> M''} {s : Set M} (hg : ContMDiff I' I'' n g) (hf : ContMDiffOn I I' n f 
s) : ContMDiffOn…
· 使用引理 `contMDiffOn_projIcc`：contMDiffOn_projIcc : CMDiff[Icc x y] n (Set.projIc
c x y h.out.le)
-/
lemma contMDiffOn_comp_projIcc_iff {f : Icc x y → M} :
    CMDiff[Icc x y] n (f ∘ (Set.projIcc x y h.out.le)) ↔ CMDiff n f := by
  refine ⟨fun hf ↦ ?_, fun hf ↦ hf.comp_contMDiffOn contMDiffOn_projIcc⟩
  convert! hf.comp_contMDiff (contMDiff_subtypeVal_Icc (x := x) (y := y)) (fun z ↦ z.2)
  ext z
  simp
/-
**contMDiffWithinAt_comp_projIcc_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：contMDiffWithinAt_comp_projIcc_iff {f : Icc x y -> M} {w : Icc x y} : CMDi
ffAt[Icc x y] n (f ∘ (Set.projIcc x y h.out.le)) w ↔ CMDiffAt n f w
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `contMDiff_subtypeVal_Icc`：contMDiff_subtypeVal_Icc : CMDiff n (fun (z : 
Icc x y) => (z : Real))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `contMDiffWithinAt_univ`：contMDiffWithinAt_univ : ContMDiffWithinAt I I' 
n f univ x ↔ ContMDiffAt I I' n f x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.projIcc_val`：projIcc_val (x : Icc a b) : projIcc a b h x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ContMDiffWithinAt.comp`：ContMDiffWithinAt.comp {t : Set M'} {g : M' -> M
''} (x : M) (hg : ContMDiffWithinAt I' I'' n g t (f x)) (hf : ContMDiffWithinAt 
I I' n f s x…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `ContMDiffAt.comp_contMDiffWithinAt_of_eq`：ContMDiffAt.comp_contMDiffWith
inAt_of_eq {g : M' -> M''} {x : M} {y : M'} (hg : ContMDiffAt I' I'' n g y) (hf 
: ContMDiffWithinAt I I' n f s…
· 使用引理 `contMDiffOn_projIcc`：contMDiffOn_projIcc : CMDiff[Icc x y] n (Set.projIc
c x y h.out.le)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma contMDiffWithinAt_comp_projIcc_iff {f : Icc x y → M} {w : Icc x y} :
    CMDiffAt[Icc x y] n (f ∘ (Set.projIcc x y h.out.le)) w ↔ CMDiffAt n f w := by
  refine ⟨fun hf ↦ ?_,
    fun hf ↦ hf.comp_contMDiffWithinAt_of_eq (contMDiffOn_projIcc w w.2) (by simp)⟩
  have A := contMDiff_subtypeVal_Icc (x := x) (y := y) (n := n) w
  rw [← contMDiffWithinAt_univ] at A ⊢
  convert! hf.comp _ A (fun z hz ↦ z.2)
  ext z
  simp
/-
**mdifferentiableWithinAt_comp_projIcc_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mdifferentiableWithinAt_comp_projIcc_iff {f : Icc x y -> M} {w : Icc x y} 
: MDiffAt[Icc x y] (f ∘ (Set.projIcc x y h.out.le)) w ↔ MDiffAt f w
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ContMDiffAt.mdifferentiableAt`：ContMDiffAt.mdifferentiableAt (hf : CMDif
fAt n f x) (hn : n != 0) : MDiffAt f x
· 使用引理 `contMDiff_subtypeVal_Icc`：contMDiff_subtypeVal_Icc : CMDiff n (fun (z : 
Icc x y) => (z : Real))
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mdifferentiableWithinAt_univ`：mdifferentiableWithinAt_univ : MDiffAt[uni
v] f x ↔ MDiffAt f x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.projIcc_val`：projIcc_val (x : Icc a b) : projIcc a b h x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MDifferentiableWithinAt.comp`：MDifferentiableWithinAt.comp (hg : MDiffAt
[u] g (f x)) (hf : MDiffAt[s] f x) (h : s subseteq f ⁻¹' u) : MDifferentiableWit
hinAt I I'' (g ∘ f…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `ContMDiffWithinAt.mdifferentiableWithinAt`：ContMDiffWithinAt.mdifferenti
ableWithinAt (hf : CMDiffAt[s] n f x) (hn : n != 0) : MDiffAt[s] f x
· 使用引理 `contMDiffOn_projIcc`：contMDiffOn_projIcc : CMDiff[Icc x y] n (Set.projIc
c x y h.out.le)
· 使用定理 `MDifferentiableAt.comp_mdifferentiableWithinAt_of_eq`：MDifferentiableAt.
comp_mdifferentiableWithinAt_of_eq {y : M'} (hg : MDiffAt g y) (hf : MDiffAt[s] 
f x) (hy : f x = y) : MDiffAt[s] (g ∘ f) x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma mdifferentiableWithinAt_comp_projIcc_iff {f : Icc x y → M} {w : Icc x y} :
    MDiffAt[Icc x y] (f ∘ (Set.projIcc x y h.out.le)) w ↔ MDiffAt f w := by
  refine ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩
  · have A := (contMDiff_subtypeVal_Icc (x := x) (y := y) w).mdifferentiableAt one_ne_zero
    rw [← mdifferentiableWithinAt_univ] at A ⊢
    convert! hf.comp _ A (fun z hz ↦ z.2)
    ext z
    simp
  · have := (contMDiffOn_projIcc (x := x) (y := y) w w.2).mdifferentiableWithinAt one_ne_zero
    exact MDifferentiableAt.comp_mdifferentiableWithinAt_of_eq (w : ℝ) hf this (by simp)
/-
**mfderivWithin_projIcc_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mfderivWithin_projIcc_one {z : Real} (hz : z in Icc x y) : mfderiv[Icc x y
] (Set.projIcc x y h.out.le) z 1 = 1
参数：hz : z in Icc x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `oneTangentSpaceIcc_def`：∀ {x y : ℝ} [h : Fact (x < y)] (z : ↑(Set.Icc x 
y)),   oneTangentSpaceIcc z = (mfderiv[Set.Icc x y] (Set.projIcc x y ⋯) ↑z) 1
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.projIcc_of_mem`：projIcc_of_mem (hx : x in Icc a b) : projIcc a b h x
 = ⟨x, hx⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mfderivWithin_projIcc_one {z : ℝ} (hz : z ∈ Icc x y) :
    mfderiv[Icc x y] (Set.projIcc x y h.out.le) z 1 = 1 := by
  change _ = oneTangentSpaceIcc (Set.projIcc x y h.out.le z)
  simp only [oneTangentSpaceIcc]
  congr
  simp [projIcc_of_mem h.out.le hz]
/-
**mfderivWithin_comp_projIcc_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mfderivWithin_comp_projIcc_one {f : Icc x y -> M} {w : Icc x y} : mfderiv[
Icc x y] (f ∘ (projIcc x y h.out.le)) w 1 = mfderiv% f w 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mfderiv_comp_mfderivWithin`：mfderiv_comp_mfderivWithin (hg : MDiffAt g (
f x)) (hf : MDiffAt[s] f x) (hxs : UniqueMDiffAt[s] x) : mfderiv[s] (g ∘ f) x = 
(mfderiv% g (f x…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.projIcc_val`：projIcc_val (x : Icc a b) : projIcc a b h x = x
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ContMDiffWithinAt.mdifferentiableWithinAt`：ContMDiffWithinAt.mdifferenti
ableWithinAt (hf : CMDiffAt[s] n f x) (hn : n != 0) : MDiffAt[s] f x
· 使用引理 `contMDiffOn_projIcc`：contMDiffOn_projIcc : CMDiff[Icc x y] n (Set.projIc
c x y h.out.le)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `UniqueDiffWithinAt.uniqueMDiffWithinAt`：∀ {𝕜 : Type u_1} [inst : Nontriv
iallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 E] {s : Set E} …
· 使用定理 `uniqueDiffOn_Icc`：uniqueDiffOn_Icc {a b : Real} (hab : a < b) : UniqueDi
ffOn Real (Icc a b)
· 使用定理 `Set.projIcc_of_mem`：projIcc_of_mem (hx : x in Icc a b) : projIcc a b h x
 = ⟨x, hx⟩
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `mfderivWithin_projIcc_one`：mfderivWithin_projIcc_one {z : Real} (hz : z 
in Icc x y) : mfderiv[Icc x y] (Set.projIcc x y h.out.le) z 1 = 1
· 使用定理 `mfderiv_zero_of_not_mdifferentiableAt`：mfderiv_zero_of_not_mdifferentiab
leAt (h : ¬MDiffAt f x) : mfderiv% f x = 0
· 使用定理 `mfderivWithin_zero_of_not_mdifferentiableWithinAt`：mfderivWithin_zero_of
_not_mdifferentiableWithinAt (h : ¬MDiffAt[s] f x) : mfderiv[s] f x = 0
· 使用引理 `mdifferentiableWithinAt_comp_projIcc_iff`：mdifferentiableWithinAt_comp_p
rojIcc_iff {f : Icc x y -> M} {w : Icc x y} : MDiffAt[Icc x y] (f ∘ (Set.projIcc
 x y h.out.le)) w ↔ MDiffAt f …
-/
lemma mfderivWithin_comp_projIcc_one {f : Icc x y → M} {w : Icc x y} :
    mfderiv[Icc x y] (f ∘ (projIcc x y h.out.le)) w 1 = mfderiv% f w 1 := by
  by_cases hw : MDiffAt f w; swap
  · rw [mfderiv_zero_of_not_mdifferentiableAt hw, mfderivWithin_zero_of_not_mdifferentiableWithinAt]
    · rfl
    · rwa [mdifferentiableWithinAt_comp_projIcc_iff]
  rw [mfderiv_comp_mfderivWithin (I' := 𝓡∂ 1)]; rotate_left
  · simp [hw]
  · exact (contMDiffOn_projIcc _ w.2).mdifferentiableWithinAt one_ne_zero
  · exact (uniqueDiffOn_Icc h.out _ w.2).uniqueMDiffWithinAt
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply]
  have : w = projIcc x y h.out.le (w : ℝ) := by rw [projIcc_of_mem]
  rw [projIcc_of_mem _ w.2]
  congr 1
  convert! mfderivWithin_projIcc_one w.2
/-
**mfderiv_subtypeVal_Icc_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mfderiv_subtypeVal_Icc_one (z : Icc x y) : mfderiv (𝓡∂ 1) 𝓘(Real) (Subtype
.val : Icc x y -> Real) z 1 = 1
参数：z : Icc x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `mfderivWithin_congr_of_mem`：mfderivWithin_congr_of_mem (hL : forall x in
 s, f₁ x = f x) (hx : x in s) : mfderiv[s] f₁ x = mfderiv[s] f x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.projIcc_of_mem`：projIcc_of_mem (hx : x in Icc a b) : projIcc a b h x
 = ⟨x, hx⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `mfderivWithin_comp_projIcc_one`：mfderivWithin_comp_projIcc_one {f : Icc 
x y -> M} {w : Icc x y} : mfderiv[Icc x y] (f ∘ (projIcc x y h.out.le)) w 1 = mf
deriv% f w 1
· 使用定理 `mfderivWithin_eq_fderivWithin`：mfderivWithin_eq_fderivWithin : mfderiv[s
] f x = fderivWithin 𝕜 f s x
· 使用定理 `fderivWithin_id`：fderivWithin_id [ContinuousAdd E] [ContinuousSMul 𝕜 E] 
[T2Space E] (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 id s x = .id 𝕜 E
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
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `uniqueDiffOn_Icc`：uniqueDiffOn_Icc {a b : Real} (hab : a < b) : UniqueDi
ffOn Real (Icc a b)
-/
lemma mfderiv_subtypeVal_Icc_one (z : Icc x y) :
    mfderiv (𝓡∂ 1) 𝓘(ℝ) (Subtype.val : Icc x y → ℝ) z 1 = 1 := by
  have A : mfderiv[Icc x y] (Subtype.val ∘ (projIcc x y h.out.le)) z 1
      = mfderiv[Icc x y] (@id ℝ) z 1 := by
    congr 1
    apply mfderivWithin_congr_of_mem _ z.2
    intro z hz
    simp [projIcc_of_mem h.out.le hz]
  rw [← mfderivWithin_comp_projIcc_one, A]
  simp only [id_eq, mfderivWithin_eq_fderivWithin]
  rw [fderivWithin_id (uniqueDiffOn_Icc h.out _ z.2)]
  rfl

@[deprecated (since := "2026-07-22")]
alias mfderiv_subtype_coe_Icc_one := mfderiv_subtypeVal_Icc_one
