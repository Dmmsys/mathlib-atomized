/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Geometry.Manifold.Algebra.Structures
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.Notation
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
public import Mathlib.LinearAlgebra.Complex.Determinant
public import Mathlib.RingTheory.Complex
public import Mathlib.RingTheory.Norm.Transitivity

/-!
# Manifold structure on the upper half plane.

In this file we define the complex manifold structure on the upper half-plane, and show it is
invariant under Moebius transformations. We also calculate the derivative, and give an explicit
formula for its Jacobian determinant over `ℝ` (used in proving that the action preserves
a suitable measure).
-/

@[expose] public section

open Filter

open scoped Manifold ContDiff MatrixGroups Topology

variable {n : ℕ∞ω}

namespace UpperHalfPlane

/-
**UpperHalfPlane.** 是 Mathlib 中的一个实例，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : ChartedSpace ℂ ℍ :=
  isOpenEmbedding_coe.singletonChartedSpace
/-
**UpperHalfPlane.** 是 Mathlib 中的一个实例，位于命名空间 `UpperHalfPlane`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsManifold 𝓘(ℂ) ω ℍ :=
  isOpenEmbedding_coe.isManifold_singleton

/-- The inclusion map `ℍ → ℂ` is a map of `C^n` manifolds. -/
/-
**UpperHalfPlane.contMDiff_coe** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：contMDiff_coe : CMDiff n ((↑) : ℍ -> Complex)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `contMDiffAt_extChartAt`：contMDiffAt_extChartAt : ContMDiffAt I 𝓘(𝕜, E) n
 (extChartAt I x) x

--- 原说明 ---
The inclusion map `ℍ → ℂ` is a map of `C^n` manifolds.
-/
theorem contMDiff_coe : CMDiff n ((↑) : ℍ → ℂ) :=
  fun _ => contMDiffAt_extChartAt

/-- The inclusion map `ℍ → ℂ` is a differentiable map of manifolds. -/
/-
**UpperHalfPlane.mdifferentiable_coe** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：mdifferentiable_coe : MDiff ((↑) : ℍ -> Complex)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.mdifferentiable`：ContMDiff.mdifferentiable (hf : CMDiff n f) (
hn : n != 0) : MDiff f
· 使用定理 `UpperHalfPlane.contMDiff_coe`：contMDiff_coe : CMDiff n ((↑) : ℍ -> Compl
ex)
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞

--- 原说明 ---
The inclusion map `ℍ → ℂ` is a differentiable map of manifolds.
-/
theorem mdifferentiable_coe : MDiff ((↑) : ℍ → ℂ) :=
  contMDiff_coe.mdifferentiable one_ne_zero
/-
**UpperHalfPlane.contMDiffAt_ofComplex** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane
`。
形式化陈述：contMDiffAt_ofComplex {z : Complex} (hz : 0 < z.im) : CMDiffAt n ofComplex
 z
参数：hz : 0 < z.im。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contMDiffAt_iff`：contMDiffAt_iff {n : Nat∞ω} {f : M -> M'} {x : M} : Con
tMDiffAt I I' n f x ↔ ContinuousAt f x ∧ ContDiffWithinAt 𝕜 n (extChartAt I' (f 
x) ∘ …
· 使用定理 `ContinuousAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSp
ace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (x : X),   ContinuousAt f x = F
ilter.T…
· 使用定理 `nhds_induced`：nhds_induced [T : TopologicalSpace α] (f : β -> α) (a : β)
 : @nhds β (TopologicalSpace.induced f T) a = comap f (𝓝 (f a))
· 使用定理 `Filter.tendsto_comap_iff`：tendsto_comap_iff {f : α -> β} {g : β -> γ} {a
 : Filter α} {c : Filter γ} : Tendsto f a (c.comap g) ↔ Tendsto (g ∘ f) a c
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用引理 `UpperHalfPlane.eventuallyEq_coe_comp_ofComplex`：eventuallyEq_coe_comp_of
Complex {z : Complex} (hz : 0 < z.im) : UpperHalfPlane.coe ∘ ofComplex =ᶠ[𝓝 z] i
d
· 使用引理 `UpperHalfPlane.ofComplex_apply_of_im_pos`：ofComplex_apply_of_im_pos {z :
 Complex} (hz : 0 < z.im) : ofComplex z = ⟨z, hz⟩
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `UpperHalfPlane.isOpenEmbedding_coe`：isOpenEmbedding_coe : IsOpenEmbeddin
g ((↑) : ℍ -> Complex)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `PartialEquiv.trans_refl`：trans_refl : e.trans (PartialEquiv.refl β) = e
· 使用定理 `Topology.IsOpenEmbedding.toOpenPartialHomeomorph_apply`：∀ {X : Type u_1}
 {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] (f : X
 → Y)   (h : Topology.IsOpenEmbedding f) [in…
· 使用定理 `Set.range_id`：range_id : range (@id α) = univ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContDiffAt.congr_of_eventuallyEq`：ContDiffAt.congr_of_eventuallyEq (h : 
ContDiffAt 𝕜 n f x) (hg : f₁ =ᶠ[𝓝 x] f) : ContDiffAt 𝕜 n f₁ x
· 使用定理 `contDiffAt_id`：contDiffAt_id {x} : ContDiffAt 𝕜 n (id : E -> E) x
-/
lemma contMDiffAt_ofComplex {z : ℂ} (hz : 0 < z.im) : CMDiffAt n ofComplex z := by
  rw [contMDiffAt_iff]
  constructor
  · -- continuity at z
    rw [ContinuousAt, nhds_induced, tendsto_comap_iff]
    refine Tendsto.congr' (eventuallyEq_coe_comp_ofComplex hz).symm ?_
    simpa [ofComplex_apply_of_im_pos hz] using! tendsto_id
  · -- smoothness in local chart
    simpa using! contDiffAt_id.congr_of_eventuallyEq (eventuallyEq_coe_comp_ofComplex hz)
/-
**UpperHalfPlane.mdifferentiableAt_ofComplex** 是 Mathlib 中的一个引理，位于命名空间 `UpperHal
fPlane`。
形式化陈述：mdifferentiableAt_ofComplex {z : Complex} (hz : 0 < z.im) : MDiffAt ofComp
lex z
参数：hz : 0 < z.im。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.mdifferentiableAt`：ContMDiffAt.mdifferentiableAt (hf : CMDif
fAt n f x) (hn : n != 0) : MDiffAt f x
· 使用引理 `UpperHalfPlane.contMDiffAt_ofComplex`：contMDiffAt_ofComplex {z : Complex
} (hz : 0 < z.im) : CMDiffAt n ofComplex z
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
lemma mdifferentiableAt_ofComplex {z : ℂ} (hz : 0 < z.im) : MDiffAt ofComplex z :=
  (contMDiffAt_ofComplex hz).mdifferentiableAt one_ne_zero
/-
**UpperHalfPlane.contMDiffAt_iff** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：contMDiffAt_iff {f : ℍ -> Complex} {τ : ℍ} : CMDiffAt n f τ ↔ ContDiffAt C
omplex n (f ∘ ofComplex) τ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `contMDiffAt_iff_contDiffAt`：contMDiffAt_iff_contDiffAt {f : E -> E'} {x 
: E} : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, E') n f x ↔ ContDiffAt 𝕜 n f x
· 使用定理 `ContMDiffAt.comp`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E
 : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : T
ype u_…
· 使用引理 `UpperHalfPlane.ofComplex_apply`：ofComplex_apply (z : ℍ) : ofComplex (z :
 Complex) = z
· 使用引理 `UpperHalfPlane.contMDiffAt_ofComplex`：contMDiffAt_ofComplex {z : Complex
} (hz : 0 < z.im) : CMDiffAt n ofComplex z
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `UpperHalfPlane.contMDiff_coe`：contMDiff_coe : CMDiff n ((↑) : ℍ -> Compl
ex)
-/
lemma contMDiffAt_iff {f : ℍ → ℂ} {τ : ℍ} :
    CMDiffAt n f τ ↔ ContDiffAt ℂ n (f ∘ ofComplex) τ := by
  rw [← contMDiffAt_iff_contDiffAt]
  refine ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩
  · exact (ofComplex_apply τ ▸ hf).comp _ (contMDiffAt_ofComplex τ.im_pos)
  · simpa only [Function.comp_def, ofComplex_apply] using hf.comp τ (contMDiff_coe τ)
/-
**UpperHalfPlane.mdifferentiableAt_iff** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane
`。
形式化陈述：mdifferentiableAt_iff {f : ℍ -> Complex} {τ : ℍ} : MDiffAt f τ ↔ Different
iableAt Complex (f ∘ ofComplex) ↑τ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mdifferentiableAt_iff_differentiableAt`：mdifferentiableAt_iff_differenti
ableAt : MDiffAt f x ↔ DifferentiableAt 𝕜 f x
· 使用定理 `MDifferentiableAt.comp`：MDifferentiableAt.comp (hg : MDiffAt g (f x)) (h
f : MDiffAt f x) : MDiffAt (g ∘ f) x
· 使用引理 `UpperHalfPlane.ofComplex_apply`：ofComplex_apply (z : ℍ) : ofComplex (z :
 Complex) = z
· 使用引理 `UpperHalfPlane.mdifferentiableAt_ofComplex`：mdifferentiableAt_ofComplex 
{z : Complex} (hz : 0 < z.im) : MDiffAt ofComplex z
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `UpperHalfPlane.mdifferentiable_coe`：mdifferentiable_coe : MDiff ((↑) : ℍ
 -> Complex)
-/
lemma mdifferentiableAt_iff {f : ℍ → ℂ} {τ : ℍ} :
    MDiffAt f τ ↔ DifferentiableAt ℂ (f ∘ ofComplex) ↑τ := by
  rw [← mdifferentiableAt_iff_differentiableAt]
  refine ⟨fun hf ↦ ?_, fun hf ↦ ?_⟩
  · exact (ofComplex_apply τ ▸ hf).comp _ (mdifferentiableAt_ofComplex τ.im_pos)
  · simpa only [Function.comp_def, ofComplex_apply] using hf.comp τ (mdifferentiable_coe τ)
/-
**UpperHalfPlane.mdifferentiable_iff** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：mdifferentiable_iff {f : ℍ -> Complex} : MDiff f ↔ DifferentiableOn Comple
x (f ∘ ofComplex) {z | 0 < z.im}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `UpperHalfPlane.mdifferentiableAt_iff`：mdifferentiableAt_iff {f : ℍ -> Co
mplex} {τ : ℍ} : MDiffAt f τ ↔ DifferentiableAt Complex (f ∘ ofComplex) ↑τ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `DifferentiableWithinAt.differentiableAt`：DifferentiableWithinAt.differen
tiableAt (h : DifferentiableWithinAt 𝕜 f s x) (hs : s in 𝓝 x) : DifferentiableAt
 𝕜 f x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用引理 `UpperHalfPlane.isOpen_upperHalfPlaneSet`：isOpen_upperHalfPlaneSet : IsOp
en ℍₒ
-/
lemma mdifferentiable_iff {f : ℍ → ℂ} :
    MDiff f ↔ DifferentiableOn ℂ (f ∘ ofComplex) {z | 0 < z.im} :=
  ⟨fun h z hz ↦ (mdifferentiableAt_iff.mp (h ⟨z, hz⟩)).differentiableWithinAt,
    fun h ⟨z, hz⟩ ↦ mdifferentiableAt_iff.mpr <| (h z hz).differentiableAt
     <| isOpen_upperHalfPlaneSet.mem_nhds hz⟩
/-
**UpperHalfPlane.contMDiff_num** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：contMDiff_num (g : GL (Fin 2) Real) : CMDiff n (fun τ : ℍ => num g τ)
参数：g : GL (Fin 2) Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.add`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {H : 
Type u_2} [inst_1 : TopologicalSpace H] {E : Type u_3}   [inst_2 : NormedAddComm
Gro…
· 使用定理 `ContMDiff.mul`：ContMDiff.mul (hf : CMDiff n f) (hg : CMDiff n g) : CMDif
f n (f * g)
· 使用定理 `instContMDiffMulOfTopWithTopENat`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : Type u_3}   [ins
t_2 : NormedAddCommGro…
· 使用定理 `ContMDiffRing.toContMDiffMul`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorme
dField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : Type u_3}   [inst_2 
: NormedAddCommGro…
· 使用定理 `instFieldContMDiffRing`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {n : WithTop ℕ∞}, ContMDiffRing (modelWithCornersSelf 𝕜 𝕜) n 𝕜
· 使用定理 `contMDiff_const`：contMDiff_const : ContMDiff I I' n fun _ : M => c
· 使用定理 `UpperHalfPlane.contMDiff_coe`：contMDiff_coe : CMDiff n ((↑) : ℍ -> Compl
ex)
-/
lemma contMDiff_num (g : GL (Fin 2) ℝ) : CMDiff n (fun τ : ℍ ↦ num g τ) :=
  (contMDiff_const.mul contMDiff_coe).add contMDiff_const
/-
**UpperHalfPlane.contMDiff_denom** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：contMDiff_denom (g : GL (Fin 2) Real) : CMDiff n (fun τ : ℍ => denom g τ)
参数：g : GL (Fin 2) Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.add`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {H : 
Type u_2} [inst_1 : TopologicalSpace H] {E : Type u_3}   [inst_2 : NormedAddComm
Gro…
· 使用定理 `ContMDiff.mul`：ContMDiff.mul (hf : CMDiff n f) (hg : CMDiff n g) : CMDif
f n (f * g)
· 使用定理 `instContMDiffMulOfTopWithTopENat`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : Type u_3}   [ins
t_2 : NormedAddCommGro…
· 使用定理 `ContMDiffRing.toContMDiffMul`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorme
dField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : Type u_3}   [inst_2 
: NormedAddCommGro…
· 使用定理 `instFieldContMDiffRing`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {n : WithTop ℕ∞}, ContMDiffRing (modelWithCornersSelf 𝕜 𝕜) n 𝕜
· 使用定理 `contMDiff_const`：contMDiff_const : ContMDiff I I' n fun _ : M => c
· 使用定理 `UpperHalfPlane.contMDiff_coe`：contMDiff_coe : CMDiff n ((↑) : ℍ -> Compl
ex)
-/
lemma contMDiff_denom (g : GL (Fin 2) ℝ) : CMDiff n (fun τ : ℍ ↦ denom g τ) :=
  (contMDiff_const.mul contMDiff_coe).add contMDiff_const
/-
**UpperHalfPlane.contMDiff_denom_zpow** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`
。
形式化陈述：contMDiff_denom_zpow (g : GL (Fin 2) Real) (k : Int) : CMDiff n (denom g ·
 ^ k : ℍ -> Complex)
参数：g : GL (Fin 2) Real；k : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableOn.analyticOnNhd`：∀ {E : Type u} [inst : NormedAddCommGrou
p E] [inst_1 : NormedSpace ℂ E] [CompleteSpace E] {s : Set ℂ} {f : ℂ → E},   Dif
ferentiableOn ℂ f s …
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `differentiableOn_zpow`：differentiableOn_zpow (m : Int) (s : Set 𝕜) (h : 
(0 : 𝕜) ∉ s ∨ 0 <= m) : DifferentiableOn 𝕜 (fun x => x ^ m) s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Decidable.of_not_not`：∀ {p : Prop} [Decidable p], ¬¬p → p
· 使用定理 `isOpen_compl_singleton`：isOpen_compl_singleton [T1Space X] {x : X} : IsO
pen ({x}ᶜ : Set X)
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `UpperHalfPlane.denom_ne_zero`：denom_ne_zero (g : GL (Fin 2) Real) (z : ℍ
) : denom g z != 0
· 使用定理 `ContMDiffAt.comp`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E
 : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : T
ype u_…
· 使用定理 `ContDiffAt.contMDiffAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{E' : Type u…
· 使用定理 `AnalyticAt.contDiffAt`：AnalyticAt.contDiffAt [CompleteSpace F] (h : Anal
yticAt 𝕜 f x) : ContDiffAt 𝕜 n f x
· 使用引理 `UpperHalfPlane.contMDiff_denom`：contMDiff_denom (g : GL (Fin 2) Real) : 
CMDiff n (fun τ : ℍ => denom g τ)
-/
lemma contMDiff_denom_zpow (g : GL (Fin 2) ℝ) (k : ℤ) : CMDiff n (denom g · ^ k : ℍ → ℂ) := by
  intro τ
  have : AnalyticAt ℂ (· ^ k) (denom g τ) := (differentiableOn_zpow k _ (by tauto)).analyticOnNhd
    isOpen_compl_singleton _ (denom_ne_zero g τ)
  exact this.contDiffAt.contMDiffAt.comp τ (contMDiff_denom g τ)
/-
**UpperHalfPlane.contMDiff_inv_denom** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：contMDiff_inv_denom (g : GL (Fin 2) Real) : CMDiff n (fun τ : ℍ => (denom 
g τ)⁻¹)
参数：g : GL (Fin 2) Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用引理 `UpperHalfPlane.contMDiff_denom_zpow`：contMDiff_denom_zpow (g : GL (Fin 2
) Real) (k : Int) : CMDiff n (denom g · ^ k : ℍ -> Complex)
-/
lemma contMDiff_inv_denom (g : GL (Fin 2) ℝ) : CMDiff n (fun τ : ℍ ↦ (denom g τ)⁻¹) := by
  simpa using contMDiff_denom_zpow g (-1)

/-- Each element of `GL(2, ℝ)⁺` defines a map of `C ^ n` manifolds `ℍ → ℍ`. -/
/-
**UpperHalfPlane.contMDiff_smul** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：contMDiff_smul {g : GL (Fin 2) Real} (hg : 0 < g.det.val) : CMDiff n (fun 
τ : ℍ => g • τ)
参数：Fin 2；hg : 0 < g.det.val。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `contMDiffAt_iff_target`：contMDiffAt_iff_target {x : M} : ContMDiffAt I I
' n f x ↔ ContinuousAt f x ∧ ContMDiffAt I 𝓘(𝕜, E') n (extChartAt I' (f x) ∘ f) 
x
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `ContinuousConstSMul.continuous_const_smul`：∀ {Γ : Type u_1} {T : Type u_
2} {inst : TopologicalSpace T} {inst_1 : SMul Γ T} [self : ContinuousConstSMul Γ
 T]   (γ : Γ), Continuous fun x…
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
· 使用引理 `UpperHalfPlane.coe_smul_of_det_pos`：coe_smul_of_det_pos {g : GL (Fin 2) 
Real} (hg : 0 < g.det.val) (z : ℍ) : ↑(g • z) = num g z / denom g z
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `UpperHalfPlane.isOpenEmbedding_coe`：isOpenEmbedding_coe : IsOpenEmbeddin
g ((↑) : ℍ -> Complex)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `UpperHalfPlane.glPos_smul_def`：glPos_smul_def {g : GL (Fin 2) Real} (hg 
: 0 < g.det.val) (z : ℍ) : g • z = ⟨num g z / denom g z, coe_smul_of_det_pos hg 
z ▸ (g • z).im_pos⟩
· 使用定理 `PartialEquiv.trans_refl`：trans_refl : e.trans (PartialEquiv.refl β) = e
· 使用定理 `Topology.IsOpenEmbedding.toOpenPartialHomeomorph_apply`：∀ {X : Type u_1}
 {Y : Type u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y] (f : X
 → Y)   (h : Topology.IsOpenEmbedding f) [in…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ContMDiffAt.mul`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {H 
: Type u_2} [inst_1 : TopologicalSpace H] {E : Type u_3}   [inst_2 : NormedAddCo
mmGro…
· 使用定理 `instContMDiffMulOfTopWithTopENat`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : Type u_3}   [ins
t_2 : NormedAddCommGro…
· 使用定理 `ContMDiffRing.toContMDiffMul`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorme
dField 𝕜] {H : Type u_2} [inst_1 : TopologicalSpace H] {E : Type u_3}   [inst_2 
: NormedAddCommGro…
· 使用定理 `instFieldContMDiffRing`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {n : WithTop ℕ∞}, ContMDiffRing (modelWithCornersSelf 𝕜 𝕜) n 𝕜
· 使用引理 `UpperHalfPlane.contMDiff_num`：contMDiff_num (g : GL (Fin 2) Real) : CMDi
ff n (fun τ : ℍ => num g τ)
· 使用引理 `UpperHalfPlane.contMDiff_inv_denom`：contMDiff_inv_denom (g : GL (Fin 2) 
Real) : CMDiff n (fun τ : ℍ => (denom g τ)⁻¹)

--- 原说明 ---
Each element of `GL(2, ℝ)⁺` defines a map of `C ^ n` manifolds `ℍ → ℍ`.
-/
lemma contMDiff_smul {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) : CMDiff n (fun τ : ℍ ↦ g • τ) := by
  intro τ
  refine contMDiffAt_iff_target.mpr ⟨(continuous_const_smul g).continuousAt, ?_⟩
  simpa [glPos_smul_def hg] using! (contMDiff_num g τ).mul (contMDiff_inv_denom g τ)
/-
**UpperHalfPlane.mdifferentiable_num** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：mdifferentiable_num (g : GL (Fin 2) Real) : MDiff (fun τ : ℍ => num g τ)
参数：g : GL (Fin 2) Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.mdifferentiable`：ContMDiff.mdifferentiable (hf : CMDiff n f) (
hn : n != 0) : MDiff f
· 使用引理 `UpperHalfPlane.contMDiff_num`：contMDiff_num (g : GL (Fin 2) Real) : CMDi
ff n (fun τ : ℍ => num g τ)
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
lemma mdifferentiable_num (g : GL (Fin 2) ℝ) : MDiff (fun τ : ℍ ↦ num g τ) :=
  (contMDiff_num g).mdifferentiable one_ne_zero
/-
**UpperHalfPlane.mdifferentiable_denom** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane
`。
形式化陈述：mdifferentiable_denom (g : GL (Fin 2) Real) : MDiff (fun τ : ℍ => denom g 
τ)
参数：g : GL (Fin 2) Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.mdifferentiable`：ContMDiff.mdifferentiable (hf : CMDiff n f) (
hn : n != 0) : MDiff f
· 使用引理 `UpperHalfPlane.contMDiff_denom`：contMDiff_denom (g : GL (Fin 2) Real) : 
CMDiff n (fun τ : ℍ => denom g τ)
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
lemma mdifferentiable_denom (g : GL (Fin 2) ℝ) : MDiff (fun τ : ℍ ↦ denom g τ) :=
  (contMDiff_denom g).mdifferentiable one_ne_zero
/-
**UpperHalfPlane.mdifferentiable_denom_zpow** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalf
Plane`。
形式化陈述：mdifferentiable_denom_zpow (g : GL (Fin 2) Real) (k : Int) : MDiff (denom 
g · ^ k : ℍ -> Complex)
参数：g : GL (Fin 2) Real；k : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.mdifferentiable`：ContMDiff.mdifferentiable (hf : CMDiff n f) (
hn : n != 0) : MDiff f
· 使用引理 `UpperHalfPlane.contMDiff_denom_zpow`：contMDiff_denom_zpow (g : GL (Fin 2
) Real) (k : Int) : CMDiff n (denom g · ^ k : ℍ -> Complex)
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
lemma mdifferentiable_denom_zpow (g : GL (Fin 2) ℝ) (k : ℤ) : MDiff (denom g · ^ k : ℍ → ℂ) :=
  (contMDiff_denom_zpow g k).mdifferentiable one_ne_zero
/-
**UpperHalfPlane.mdifferentiable_inv_denom** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfP
lane`。
形式化陈述：mdifferentiable_inv_denom (g : GL (Fin 2) Real) : MDiff (fun τ : ℍ => (den
om g τ)⁻¹)
参数：g : GL (Fin 2) Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.mdifferentiable`：ContMDiff.mdifferentiable (hf : CMDiff n f) (
hn : n != 0) : MDiff f
· 使用引理 `UpperHalfPlane.contMDiff_inv_denom`：contMDiff_inv_denom (g : GL (Fin 2) 
Real) : CMDiff n (fun τ : ℍ => (denom g τ)⁻¹)
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
lemma mdifferentiable_inv_denom (g : GL (Fin 2) ℝ) : MDiff (fun τ : ℍ ↦ (denom g τ)⁻¹) :=
  (contMDiff_inv_denom g).mdifferentiable one_ne_zero

/-- Each element of `GL(2, ℝ)⁺` defines a complex-differentiable map `ℍ → ℍ`. -/
/-
**UpperHalfPlane.mdifferentiable_smul** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`
。
形式化陈述：mdifferentiable_smul {g : GL (Fin 2) Real} (hg : 0 < g.det.val) : MDiff (f
un τ : ℍ => g • τ)
参数：Fin 2；hg : 0 < g.det.val。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiff.mdifferentiable`：ContMDiff.mdifferentiable (hf : CMDiff n f) (
hn : n != 0) : MDiff f
· 使用引理 `UpperHalfPlane.contMDiff_smul`：contMDiff_smul {g : GL (Fin 2) Real} (hg 
: 0 < g.det.val) : CMDiff n (fun τ : ℍ => g • τ)
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞

--- 原说明 ---
Each element of `GL(2, ℝ)⁺` defines a complex-differentiable map `ℍ → ℍ`.
-/
lemma mdifferentiable_smul {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) : MDiff (fun τ : ℍ ↦ g • τ) :=
  (contMDiff_smul hg).mdifferentiable one_ne_zero
/-
**UpperHalfPlane.eq_zero_of_frequently** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane
`。
形式化陈述：eq_zero_of_frequently {f : ℍ -> Complex} (hf : MDiff f) {τ : ℍ} (hτ : exis
tsᶠ z in 𝓝[!=] τ, f z = 0) : f = 0
参数：hf : MDiff f；hτ : existsᶠ z in 𝓝[!=] τ, f z = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableOn.analyticOnNhd`：∀ {E : Type u} [inst : NormedAddCommGrou
p E] [inst_1 : NormedSpace ℂ E] [CompleteSpace E] {s : Set ℂ} {f : ℂ → E},   Dif
ferentiableOn ℂ f s …
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `UpperHalfPlane.mdifferentiable_iff`：mdifferentiable_iff {f : ℍ -> Comple
x} : MDiff f ↔ DifferentiableOn Complex (f ∘ ofComplex) {z | 0 < z.im}
· 使用引理 `UpperHalfPlane.isOpen_upperHalfPlaneSet`：isOpen_upperHalfPlaneSet : IsOp
en ℍₒ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用引理 `UpperHalfPlane.ofComplex_apply`：ofComplex_apply (z : ℍ) : ofComplex (z :
 Complex) = z
· 使用定理 `AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero`：eqOn_zero
_of_preconnected_of_frequently_eq_zero (hf : AnalyticOnNhd 𝕜 f U) (hU : IsPrecon
nected U) (h₀ : z₀ in U) (hfw : existsᶠ z in 𝓝[!=] …
· 使用定理 `IsConnected.isPreconnected`：IsConnected.isPreconnected {s : Set α} (h : 
IsConnected s) : IsPreconnected s
· 使用引理 `Complex.isConnected_of_upperHalfPlane`：isConnected_of_upperHalfPlane {r}
 {s : Set Complex} (hs₁ : {z | r < z.im} subseteq s) (hs₂ : s subseteq {z | r <=
 z.im}) : IsConnected s
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
· 使用定理 `UpperHalfPlane.coe_im_pos`：∀ (self : UpperHalfPlane), 0 < (↑self).im
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eventually_nhdsWithin_iff`：eventually_nhdsWithin_iff {a : α} {s : Set α}
 {p : α -> Prop} : (forallᶠ x in 𝓝[s] a, p x) ↔ forallᶠ x in 𝓝 a, x in s -> p x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_map`：eventually_map {P : β -> Prop} : (forallᶠ b in ma
p m f, P b) ↔ forallᶠ a in f, P (m a)
· 使用定理 `Topology.IsOpenEmbedding.map_nhds_eq`：∀ {X : Type u_1} {Y : Type u_2} {f
 : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology.
IsOpenEmbedding f → ∀ (x :…
· 使用定理 `UpperHalfPlane.isOpenEmbedding_coe`：isOpenEmbedding_coe : IsOpenEmbeddin
g ((↑) : ℍ -> Complex)
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
-/
lemma eq_zero_of_frequently {f : ℍ → ℂ} (hf : MDiff f) {τ : ℍ} (hτ : ∃ᶠ z in 𝓝[≠] τ, f z = 0) :
    f = 0 := by
  rw [mdifferentiable_iff] at hf
  have := hf.analyticOnNhd isOpen_upperHalfPlaneSet
  ext w
  convert! this.eqOn_zero_of_preconnected_of_frequently_eq_zero (z₀ := ↑τ) ?_ τ.2 ?_ w.im_pos
  · rw [Function.comp_apply, ofComplex_apply]
  · exact (Complex.isConnected_of_upperHalfPlane subset_rfl (by grind)).isPreconnected
  · contrapose! hτ
    rw [eventually_nhdsWithin_iff, ← isOpenEmbedding_coe.map_nhds_eq, eventually_map] at hτ
    rw [eventually_nhdsWithin_iff]
    filter_upwards [hτ] with a ha
    simpa using ha
/-
**UpperHalfPlane.mul_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：mul_eq_zero_iff {f g : ℍ -> Complex} (hf : MDiff f) (hg : MDiff g) : f * g
 = 0 ↔ f = 0 ∨ g = 0
参数：hf : MDiff f；hg : MDiff g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用引理 `UpperHalfPlane.eq_zero_of_frequently`：eq_zero_of_frequently {f : ℍ -> Co
mplex} (hf : MDiff f) {τ : ℍ} (hτ : existsᶠ z in 𝓝[!=] τ, f z = 0) : f = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.frequently_or_distrib`：frequently_or_distrib {f : Filter α} {p q 
: α -> Prop} : (existsᶠ x in f, p x ∨ q x) ↔ (existsᶠ x in f, p x) ∨ existsᶠ x i
n f, q x
· 使用定理 `Filter.Frequently.of_forall`：∀ {α : Type u} {f : Filter α} [f.NeBot] {p 
: α → Prop}, (∀ (x : α), p x) → ∃ᶠ (x : α) in f, p x
· 使用定理 `instPerfectSpaceOfT1SpaceOfConnectedSpaceOfNontrivial`：∀ {α : Type u_1} 
[inst : TopologicalSpace α] [T1Space α] [ConnectedSpace α] [Nontrivial α], Perfe
ctSpace α
· 使用定理 `T4Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T4
Space X], T1Space X
· 使用定理 `UpperHalfPlane.instT4Space`：T4Space UpperHalfPlane
· 使用定理 `PathConnectedSpace.connectedSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [PathConnectedSpace X], ConnectedSpace X
· 使用定理 `ContractibleSpace.instPathConnectedSpace`：∀ {X : Type u_1} [inst : Topol
ogicalSpace X] [ContractibleSpace X], PathConnectedSpace X
· 使用定理 `UpperHalfPlane.instContractibleSpace`：ContractibleSpace UpperHalfPlane
· 使用定理 `UpperHalfPlane.instNontrivial`：Nontrivial UpperHalfPlane
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
-/
lemma mul_eq_zero_iff {f g : ℍ → ℂ} (hf : MDiff f) (hg : MDiff g) : f * g = 0 ↔ f = 0 ∨ g = 0 :=
  ⟨fun hfg ↦ (frequently_or_distrib.mp <| .of_forall <| by simpa using congrFun hfg).imp
    (eq_zero_of_frequently (τ := I) hf) (eq_zero_of_frequently hg), by grind⟩
/-
**UpperHalfPlane.prod_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：prod_eq_zero_iff {ι : Type*} {f : ι -> ℍ -> Complex} {s : Finset ι} (hf : 
forall i in s, MDiff (f i)) : ∏ i in s, f i = 0 ↔ exists i in s, f i = 0
参数：hf : forall i in s, MDiff (f i)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Frequently.of_forall`：∀ {α : Type u} {f : Filter α} [f.NeBot] {p 
: α → Prop}, (∀ (x : α), p x) → ∃ᶠ (x : α) in f, p x
· 使用定理 `instPerfectSpaceOfT1SpaceOfConnectedSpaceOfNontrivial`：∀ {α : Type u_1} 
[inst : TopologicalSpace α] [T1Space α] [ConnectedSpace α] [Nontrivial α], Perfe
ctSpace α
· 使用定理 `T4Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T4
Space X], T1Space X
· 使用定理 `UpperHalfPlane.instT4Space`：T4Space UpperHalfPlane
· 使用定理 `PathConnectedSpace.connectedSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [PathConnectedSpace X], ConnectedSpace X
· 使用定理 `ContractibleSpace.instPathConnectedSpace`：∀ {X : Type u_1} [inst : Topol
ogicalSpace X] [ContractibleSpace X], PathConnectedSpace X
· 使用定理 `UpperHalfPlane.instContractibleSpace`：ContractibleSpace UpperHalfPlane
· 使用定理 `UpperHalfPlane.instNontrivial`：Nontrivial UpperHalfPlane
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_apply`：Finset.prod_apply {α : Type*} {M : α -> Type*} [foral
l a, CommMonoid (M a)] (a : α) (s : Finset ι) (g : ι -> forall a, M a) : (∏ c in
 s, g c…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `UpperHalfPlane.eq_zero_of_frequently`：eq_zero_of_frequently {f : ℍ -> Co
mplex} (hf : MDiff f) {τ : ℍ} (hτ : existsᶠ z in 𝓝[!=] τ, f z = 0) : f = 0
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用引理 `Finset.prod_eq_zero`：prod_eq_zero (hi : i in s) (h : f i = 0) : ∏ j in s
, f j = 0
-/
lemma prod_eq_zero_iff {ι : Type*} {f : ι → ℍ → ℂ} {s : Finset ι}
    (hf : ∀ i ∈ s, MDiff (f i)) :
    ∏ i ∈ s, f i = 0 ↔ ∃ i ∈ s, f i = 0 := by
  refine ⟨fun h0 ↦ ?_, fun ⟨i, hi, hi'⟩ ↦ Finset.prod_eq_zero hi hi'⟩
  have : ∃ᶠ τ in 𝓝[≠] I, ∏ i ∈ s, f i τ = 0 := .of_forall <| by simpa using congrFun h0
  simp only [Finset.prod_eq_zero_iff, Finset.frequently_exists] at this
  exact this.imp fun i hi ↦ ⟨hi.1, eq_zero_of_frequently (hf i hi.1) hi.2⟩

section deriv
/-!
## Explicit calculations of the derivative of `τ ↦ g • τ`

TODO: would it be better to reimplement these using `mfderiv` together with a trivialization of
the tangent space of `ℍ`, rather than using `ofComplex` as we currently do? Or would that bring
more pain than gain?

TODO(MR): investigate if using `mvfderiv` can avoid the "pain" above, and be a cleaner design!
-/

section Complex

/-- Derivative of `z ↦ (denom g z) ^ k`: $\frac{d}{dz}[(cz+d)^k] = k \cdot c \cdot (cz+d)^{k-1}$. -/
/-
**UpperHalfPlane.hasDerivAt_denom_zpow** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane
`。
形式化陈述：hasDerivAt_denom_zpow (g : GL (Fin 2) Real) (k : Int) (τ : ℍ) : HasDerivAt
 (fun z => denom g z ^ k) (k * g 1 0 * denom g τ ^ (k - 1)) τ
参数：g : GL (Fin 2) Real；k : Int；τ : ℍ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `HasDerivAt.add_const`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] 
{F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f : 𝕜
 → F} {f' …
· 使用定理 `HasDerivAt.const_mul`：HasDerivAt.const_mul (c : 𝔸) (hd : HasDerivAt d d'
 x) : HasDerivAt (fun y => c * d y) (c * d') x
· 使用定理 `hasDerivAt_id`：hasDerivAt_id : HasDerivAt id 1 x
· 使用定理 `HasDerivAt.comp`：HasDerivAt.comp (hh₂ : HasDerivAt h₂ h₂' (h x)) (hh : H
asDerivAt h h' x) : HasDerivAt (h₂ ∘ h) (h₂' * h') x
· 使用定理 `hasDerivAt_zpow`：hasDerivAt_zpow (m : Int) (x : 𝕜) (h : x != 0 ∨ 0 <= m)
 : HasDerivAt (fun x => x ^ m) ((m : 𝕜) * x ^ (m - 1)) x
· 使用定理 `UpperHalfPlane.denom_ne_zero`：denom_ne_zero (g : GL (Fin 2) Real) (z : ℍ
) : denom g z != 0
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b

--- 原说明 ---
Derivative of `z ↦ (denom g z) ^ k`: $\frac{d}{dz}[(cz+d)^k] = k \cdot c \cdot (
cz+d)^{k-1}$.
-/
lemma hasDerivAt_denom_zpow (g : GL (Fin 2) ℝ) (k : ℤ) (τ : ℍ) :
    HasDerivAt (fun z ↦ denom g z ^ k) (k * g 1 0 * denom g τ ^ (k - 1)) τ := by
  have hd : HasDerivAt (denom g ·) (g 1 0) τ := by
    simpa [denom] using hasDerivAt_id _ |>.const_mul _ |>.add_const (g 1 1 : ℂ)
  have := (hasDerivAt_zpow k (denom g τ) (Or.inl (denom_ne_zero g τ))).comp _ hd
  simpa only [Function.comp_def, mul_right_comm] using this

/-- Derivative of `z ↦ (denom g z) ^ k`:
$\frac{d}{dz}[(cz+d)^k] = k \cdot c \cdot (cz+d)^{k-1}$. -/
/-
**UpperHalfPlane.deriv_denom_zpow** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：deriv_denom_zpow (g : GL (Fin 2) Real) (k : Int) (τ : ℍ) : deriv (fun z =>
 denom g z ^ k) τ = k * g 1 0 * denom g τ ^ (k - 1)
参数：g : GL (Fin 2) Real；k : Int；τ : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `UpperHalfPlane.hasDerivAt_denom_zpow`：hasDerivAt_denom_zpow (g : GL (Fin
 2) Real) (k : Int) (τ : ℍ) : HasDerivAt (fun z => denom g z ^ k) (k * g 1 0 * d
enom g τ ^ (k - 1)) τ

--- 原说明 ---
Derivative of `z ↦ (denom g z) ^ k`:
$\frac{d}{dz}[(cz+d)^k] = k \cdot c \cdot (cz+d)^{k-1}$.
-/
lemma deriv_denom_zpow (g : GL (Fin 2) ℝ) (k : ℤ) (τ : ℍ) :
    deriv (fun z ↦ denom g z ^ k) τ = k * g 1 0 * denom g τ ^ (k - 1) :=
  (hasDerivAt_denom_zpow g k τ).deriv
/-
**UpperHalfPlane.hasStrictDerivAt_smul** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane
`。
形式化陈述：hasStrictDerivAt_smul {g : GL (Fin 2) Real} (hg : 0 < g.val.det) (τ : ℍ) :
 HasStrictDerivAt (fun z => ↑(g • ofComplex z) : Complex -> Complex) (g.val.det 
/ denom g τ ^ 2) τ
参数：Fin 2；hg : 0 < g.val.det；τ : ℍ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.det_fin_two`：det_fin_two (A : Matrix (Fin 2) (Fin 2) R) : det A =
 A 0 0 * A 1 1 - A 0 1 * A 1 0
· 使用定理 `Complex.ofReal_sub`：ofReal_sub (r s : Real) : ((r - s : Real) : Complex)
 = r - s
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
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
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
（共 60 条，此处仅展示前 30 条）
-/
lemma hasStrictDerivAt_smul {g : GL (Fin 2) ℝ} (hg : 0 < g.val.det) (τ : ℍ) :
    HasStrictDerivAt (fun z ↦ ↑(g • ofComplex z) : ℂ → ℂ) (g.val.det / denom g τ ^ 2) τ := by
  suffices HasStrictDerivAt (num g / denom g) (g.val.det / denom g τ ^ 2) τ by
    refine this.congr_of_eventuallyEq ?_
    rw [← isOpenEmbedding_coe.map_nhds_eq, eventuallyEq_map]
    simp [Function.comp_def, coe_smul_of_det_pos hg]
  convert!
    ((hasStrictDerivAt_id (τ : ℂ)).const_mul _ |>.add_const _).div
      ((hasStrictDerivAt_id (τ : ℂ)).const_mul _ |>.add_const _) _ using 2
  · simp [Matrix.det_fin_two]; ring
  · apply denom_ne_zero
/-
**UpperHalfPlane.deriv_smul** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：deriv_smul {g : GL (Fin 2) Real} (hg : 0 < g.val.det) (τ : ℍ) : deriv (fun
 z => ↑(g • ofComplex z) : Complex -> Complex) τ = g.val.det / denom g τ ^ 2
参数：Fin 2；hg : 0 < g.val.det；τ : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `HasStrictDerivAt.hasDerivAt`：HasStrictDerivAt.hasDerivAt (h : HasStrictD
erivAt f f' x) : HasDerivAt f f' x
· 使用引理 `UpperHalfPlane.hasStrictDerivAt_smul`：hasStrictDerivAt_smul {g : GL (Fin
 2) Real} (hg : 0 < g.val.det) (τ : ℍ) : HasStrictDerivAt (fun z => ↑(g • ofComp
lex z) : Complex -> Comple…
-/
lemma deriv_smul {g : GL (Fin 2) ℝ} (hg : 0 < g.val.det) (τ : ℍ) :
    deriv (fun z ↦ ↑(g • ofComplex z) : ℂ → ℂ) τ = g.val.det / denom g τ ^ 2 :=
  hasStrictDerivAt_smul hg τ |>.hasDerivAt |>.deriv
/-
**UpperHalfPlane.deriv_smul_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：deriv_smul_ne_zero {g : GL (Fin 2) Real} (hg : 0 < g.val.det) (τ : ℍ) : de
riv (fun z => ↑(g • ofComplex z) : Complex -> Complex) τ != 0
参数：Fin 2；hg : 0 < g.val.det；τ : ℍ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `UpperHalfPlane.deriv_smul`：deriv_smul {g : GL (Fin 2) Real} (hg : 0 < g.
val.det) (τ : ℍ) : deriv (fun z => ↑(g • ofComplex z) : Complex -> Complex) τ = 
g.val.det / den…
· 使用定理 `div_ne_zero`：div_ne_zero (ha : a != 0) (hb : b != 0) : a / b != 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `UpperHalfPlane.denom_ne_zero`：denom_ne_zero (g : GL (Fin 2) Real) (z : ℍ
) : denom g z != 0
-/
lemma deriv_smul_ne_zero {g : GL (Fin 2) ℝ} (hg : 0 < g.val.det) (τ : ℍ) :
    deriv (fun z ↦ ↑(g • ofComplex z) : ℂ → ℂ) τ ≠ 0 := by
  rw [deriv_smul hg]
  apply div_ne_zero
  · exact_mod_cast hg.ne'
  · exact pow_ne_zero _ (denom_ne_zero g τ)
/-
**UpperHalfPlane.analyticAt_smul** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：analyticAt_smul {g : GL (Fin 2) Real} (hg : 0 < g.val.det) (τ : ℍ) : Analy
ticAt Complex (fun z => ↑(g • ofComplex z) : Complex -> Complex) τ
参数：Fin 2；hg : 0 < g.val.det；τ : ℍ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableOn.analyticAt`：∀ {E : Type u} [inst : NormedAddCommGroup E
] [inst_1 : NormedSpace ℂ E] [CompleteSpace E] {s : Set ℂ} {f : ℂ → E}   {z : ℂ}
, DifferentiableO…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `MDifferentiable.mdifferentiableAt`：MDifferentiable.mdifferentiableAt (hf
 : MDiff f) : MDiffAt f x
· 使用定理 `MDifferentiable.comp`：MDifferentiable.comp (hg : MDiff g) (hf : MDiff f)
 : MDiff (g ∘ f)
· 使用定理 `UpperHalfPlane.mdifferentiable_coe`：mdifferentiable_coe : MDiff ((↑) : ℍ
 -> Complex)
· 使用引理 `UpperHalfPlane.mdifferentiable_smul`：mdifferentiable_smul {g : GL (Fin 2
) Real} (hg : 0 < g.det.val) : MDiff (fun τ : ℍ => g • τ)
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用引理 `UpperHalfPlane.isOpen_upperHalfPlaneSet`：isOpen_upperHalfPlaneSet : IsOp
en ℍₒ
· 使用定理 `UpperHalfPlane.im_pos`：im_pos (z : ℍ) : 0 < z.im
-/
lemma analyticAt_smul {g : GL (Fin 2) ℝ} (hg : 0 < g.val.det) (τ : ℍ) :
    AnalyticAt ℂ (fun z ↦ ↑(g • ofComplex z) : ℂ → ℂ) τ := by
  refine DifferentiableOn.analyticAt (fun z hz ↦ ?_) (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)
  apply DifferentiableAt.differentiableWithinAt
  simpa [mdifferentiableAt_iff] using!
    (mdifferentiable_coe.comp <| (mdifferentiable_smul hg)).mdifferentiableAt (x := ⟨z, hz⟩)
/-
**UpperHalfPlane.meromorphicOrderAt_comp_smul** 是 Mathlib 中的一个引理，位于命名空间 `UpperHa
lfPlane`。
形式化陈述：meromorphicOrderAt_comp_smul {f : ℍ -> Complex} {τ : ℍ} {g : GL (Fin 2) Re
al} (hg : 0 < g.val.det) : meromorphicOrderAt (fun z => f (g • ofComplex z)) τ =
 meromorphicOrderAt (fun z => f (ofComplex z)) ↑(g • τ)
参数：Fin 2；hg : 0 < g.val.det。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `UpperHalfPlane.ofComplex_apply`：ofComplex_apply (z : ℍ) : ofComplex (z :
 Complex) = z
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `meromorphicOrderAt_comp_of_deriv_ne_zero`：meromorphicOrderAt_comp_of_der
iv_ne_zero (hg : AnalyticAt 𝕜 g x) (hg' : deriv g x != 0) [CompleteSpace 𝕜] [Cha
rZero 𝕜] : meromorphicOrderAt …
· 使用引理 `UpperHalfPlane.analyticAt_smul`：analyticAt_smul {g : GL (Fin 2) Real} (h
g : 0 < g.val.det) (τ : ℍ) : AnalyticAt Complex (fun z => ↑(g • ofComplex z) : C
omplex -> Complex) τ
· 使用引理 `UpperHalfPlane.deriv_smul_ne_zero`：deriv_smul_ne_zero {g : GL (Fin 2) Re
al} (hg : 0 < g.val.det) (τ : ℍ) : deriv (fun z => ↑(g • ofComplex z) : Complex 
-> Complex) τ != 0
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma meromorphicOrderAt_comp_smul {f : ℍ → ℂ} {τ : ℍ} {g : GL (Fin 2) ℝ} (hg : 0 < g.val.det) :
    meromorphicOrderAt (fun z ↦ f (g • ofComplex z)) τ =
      meromorphicOrderAt (fun z ↦ f (ofComplex z)) ↑(g • τ) := by
  let G z : ℂ := ↑(g • ofComplex z)
  let F z := f (ofComplex z)
  have : (fun z : ℂ ↦ f (g • ofComplex z)) = F ∘ G := by ext; simp [F, G]
  rw [this, meromorphicOrderAt_comp_of_deriv_ne_zero]
  · simp [F, G]
  · exact τ.analyticAt_smul hg
  · exact τ.deriv_smul_ne_zero hg

end Complex


section Real

/-- `ℝ`-linear map from `ℂ` to itself, which we shall show is the real derivative of the
`GL(2, ℝ)`-action on `ℍ`. -/
/-
**UpperHalfPlane.smulFDeriv** 是 Mathlib 中的一个定义，位于命名空间 `UpperHalfPlane`。
形式化陈述：smulFDeriv (g : GL (Fin 2) Real) (z : Complex) : Complex ->L[Real] Complex
参数：g : GL (Fin 2) Real；z : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ℝ`-linear map from `ℂ` to itself, which we shall show is the real derivative of
 the
`GL(2, ℝ)`-action on `ℍ`.
-/
noncomputable def smulFDeriv (g : GL (Fin 2) ℝ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  (σ g) ∘L (ContinuousLinearMap.toSpanSingleton ℂ (g.det.val / denom g z ^ 2)).restrictScalars ℝ

@[simp]
/-
**UpperHalfPlane.smulFDeriv_J_mul** 是 Mathlib 中的一个定理，位于命名空间 `UpperHalfPlane`。
形式化陈述：smulFDeriv_J_mul (g : GL (Fin 2) Real) (z : Complex) : smulFDeriv (J * g) 
z = -Complex.conjCLE ∘L smulFDeriv g z
参数：g : GL (Fin 2) Real；z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `UpperHalfPlane.det_J`：Matrix.GeneralLinearGroup.det UpperHalfPlane.J = -
1
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Matrix.GeneralLinearGroup.val_det_apply`：∀ {n : Type u} [inst : Decidabl
eEq n] [inst_1 : Fintype n] {R : Type v} [inst_2 : CommRing R] (A : GL n R),   ↑
(Matrix.GeneralLinearGroup.de…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
· 使用定理 `ContinuousLinearMap.restrictScalars.congr_simp`：∀ {A : Type u_1} {M₁ : T
ype u_2} {M₂ : Type u_3} (R : Type u_4) [inst : Semiring A] [inst_1 : Semiring R
]   [inst_2 : AddCommMonoid M₁] [ins…
· 使用定理 `ContinuousLinearMap.toSpanSingleton.congr_simp`：∀ (R₁ : Type u_1) [inst 
: Semiring R₁] {M₁ : Type u_4} [inst_1 : TopologicalSpace M₁] [inst_2 : AddCommM
onoid M₁]   [inst_3 : _root_.Module …
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用引理 `UpperHalfPlane.denom_J_mul`：denom_J_mul (g : GL (Fin 2) Real) (τ : Compl
ex) : denom (J * g) τ = denom g τ
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
（共 49 条，此处仅展示前 30 条）
-/
theorem smulFDeriv_J_mul (g : GL (Fin 2) ℝ) (z : ℂ) :
    smulFDeriv (J * g) z = -Complex.conjCLE ∘L smulFDeriv g z := by
  ext
  by_cases hg : 0 < g.val.det
  · simp [smulFDeriv, σ, hg, hg.not_gt, neg_div]
  · simp [smulFDeriv, σ, hg, g.det_ne_zero.lt_or_gt.resolve_right hg, neg_div]

/-- Determinant of the derivative of `g : ℍ → ℍ` considered as an `ℝ`-linear map. This is used in
the proof that the action is measure-preserving. Note this formula applies for both orientation-
preserving and orientation-reserving isometries. -/
/-
**UpperHalfPlane.det_smulFDeriv** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlane`。
形式化陈述：det_smulFDeriv (g : GL (Fin 2) Real) (z : Complex) : (smulFDeriv g z).det 
= SignType.sign g.det.val * g.det ^ 2 / ‖denom g z‖ ^ 4
参数：g : GL (Fin 2) Real；z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用引理 `Matrix.GeneralLinearGroup.det_ne_zero`：det_ne_zero [Nontrivial R] (g : G
L n R) : g.val.det != 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Matrix.GeneralLinearGroup.val_det_apply`：∀ {n : Type u} [inst : Decidabl
eEq n] [inst_1 : Fintype n] {R : Type v} [inst_2 : CommRing R] (A : GL n R),   ↑
(Matrix.GeneralLinearGroup.de…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
· 使用定理 `ContinuousLinearMap.restrictScalars.congr_simp`：∀ {A : Type u_1} {M₁ : T
ype u_2} {M₂ : Type u_3} (R : Type u_4) [inst : Semiring A] [inst_1 : Semiring R
]   [inst_2 : AddCommMonoid M₁] [ins…
· 使用定理 `ContinuousLinearMap.toSpanSingleton.congr_simp`：∀ (R₁ : Type u_1) [inst 
: Semiring R₁] {M₁ : Type u_4} [inst_1 : TopologicalSpace M₁] [inst_2 : AddCommM
onoid M₁]   [inst_3 : _root_.Module …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.det_comp`：det_comp (f g : M ->ₗ[A] M) : LinearMap.det (f.comp 
g) = LinearMap.det f * LinearMap.det g
· 使用定理 `Complex.det_conjAe`：det_conjAe : conjAe.toLinearEquiv.toLinearMap.det = 
-1
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.det_restrictScalars`：LinearMap.det_restrictScalars [AddCommGro
up A] [Module R A] [Module S A] [IsScalarTower R S A] [Module.Free S A] {f : A -
>ₗ[S] A} : (f.restr…
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `Algebra.norm_complex_eq`：Algebra.norm_complex_eq : Algebra.norm Real = n
ormSq.toMonoidHom
· 使用定理 `LinearMap.det_ring`：∀ {R : Type u_1} [inst : CommRing R] (f : R →ₗ[R] R)
, LinearMap.det f = f 1
· 使用定理 `LinearMap.toSpanSingleton_apply`：∀ (R : Type u_1) (M : Type u_4) [inst :
 Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] (x : M)   (
b : R), (LinearMap.to…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用引理 `Complex.normSq_eq_norm_sq`：normSq_eq_norm_sq (z : Complex) : normSq z = 
‖z‖ ^ 2
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
· 使用定理 `sq_abs`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] (a : α
), |a| ^ 2 = a ^ 2
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
Determinant of the derivative of `g : ℍ → ℍ` considered as an `ℝ`-linear map. Th
is is used in
the proof that the action is measure-preserving. Note this formula applies for b
oth orientation-
preserving and orientation-reserving isometries.
-/
lemma det_smulFDeriv (g : GL (Fin 2) ℝ) (z : ℂ) :
    (smulFDeriv g z).det =
      SignType.sign g.det.val * g.det ^ 2 / ‖denom g z‖ ^ 4 := by
  simp only [smulFDeriv, σ]
  rcases g.det_ne_zero.lt_or_gt with h | h
  · simp [h.not_gt, ContinuousLinearMap.det, LinearMap.det_restrictScalars,
      Algebra.norm_complex_eq, Complex.normSq_eq_norm_sq, ← pow_mul, sign_neg h, neg_div]
  · simp [ContinuousLinearMap.det, h, LinearMap.det_restrictScalars,
      Algebra.norm_complex_eq, Complex.normSq_eq_norm_sq, ← pow_mul]
/-
**UpperHalfPlane.hasStrictFDerivAt_smul** 是 Mathlib 中的一个引理，位于命名空间 `UpperHalfPlan
e`。
形式化陈述：hasStrictFDerivAt_smul (g : GL (Fin 2) Real) (τ : ℍ) : HasStrictFDerivAt (
fun z => ↑(g • ofComplex z) : Complex -> Complex) (smulFDeriv g τ) τ
参数：g : GL (Fin 2) Real；τ : ℍ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `HasStrictFDerivAt.restrictScalars`：HasStrictFDerivAt.restrictScalars (h 
: HasStrictFDerivAt f f' x) : HasStrictFDerivAt f (f'.restrictScalars 𝕜) x
· 使用定理 `HasStrictDerivAt.hasStrictFDerivAt`：∀ {𝕜 : Type u} [inst : NontriviallyN
ormedField 𝕜] {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F
]   [inst_3 : Topologica…
· 使用引理 `UpperHalfPlane.hasStrictDerivAt_smul`：hasStrictDerivAt_smul {g : GL (Fin
 2) Real} (hg : 0 < g.val.det) (τ : ℍ) : HasStrictDerivAt (fun z => ↑(g • ofComp
lex z) : Complex -> Comple…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Matrix.GeneralLinearGroup.val_det_apply`：∀ {n : Type u} [inst : Decidabl
eEq n] [inst_1 : Fintype n] {R : Type v} [inst_2 : CommRing R] (A : GL n R),   ↑
(Matrix.GeneralLinearGroup.de…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ContinuousLinearMap.restrictScalars.congr_simp`：∀ {A : Type u_1} {M₁ : T
ype u_2} {M₂ : Type u_3} (R : Type u_4) [inst : Semiring A] [inst_1 : Semiring R
]   [inst_2 : AddCommMonoid M₁] [ins…
· 使用定理 `ContinuousLinearMap.toSpanSingleton.congr_simp`：∀ (R₁ : Type u_1) [inst 
: Semiring R₁] {M₁ : Type u_4} [inst_1 : TopologicalSpace M₁] [inst_2 : AddCommM
onoid M₁]   [inst_3 : _root_.Module …
· 使用定理 `ContinuousLinearMap.id_comp`：id_comp (f : M₁ ->SL[σ₁₂] M₂) : .id R₂ M₂ ∘
SL f = f
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
（共 55 条，此处仅展示前 30 条）
-/
lemma hasStrictFDerivAt_smul (g : GL (Fin 2) ℝ) (τ : ℍ) :
    HasStrictFDerivAt (fun z ↦ ↑(g • ofComplex z) : ℂ → ℂ) (smulFDeriv g τ) τ := by
  wlog hg : 0 < g.det.val generalizing g
  · replace hg := g.det.ne_zero.lt_or_gt.resolve_right hg
    convert! Complex.conjCLE.hasStrictFDerivAt.neg.comp _ (this (J * g) (by simpa))
    · simp [mul_smul, coe_J_smul]
    · ext
      simp
  have := (hasStrictDerivAt_smul hg τ).hasStrictFDerivAt.restrictScalars ℝ
  simp_all [smulFDeriv, σ]

end Real

end deriv

end UpperHalfPlane

