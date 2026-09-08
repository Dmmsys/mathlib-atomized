/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import Mathlib.Topology.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
public import Mathlib.Geometry.Manifold.Notation

/-! # Homs of `C^n` vector bundles over the same base space

Here we show that the bundle of continuous linear maps is a `C^n` vector bundle. We also show
that applying a smooth family of linear maps to a smooth family of vectors gives a smooth
result, in several versions.

Note that we only do this for bundles of linear maps, not for bundles of arbitrary semilinear maps.
Indeed, semilinear maps are typically not smooth. For instance, complex conjugation is not
`ℂ`-differentiable.
-/

public section

noncomputable section

open Bundle Set OpenPartialHomeomorph ContinuousLinearMap Pretrivialization

open scoped Manifold Bundle Topology

section

variable {𝕜 B F₁ F₂ M : Type*} {n : WithTop ℕ∞}
  {E₁ : B → Type*} {E₂ : B → Type*} [NontriviallyNormedField 𝕜]
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)] [∀ x, AddCommGroup (E₂ x)]
  [∀ x, Module 𝕜 (E₂ x)] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  {EB : Type*}
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B] {EM : Type*}
  [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂] {e₁ e₁' : Trivialization F₁ (π F₁ E₁)}
  {e₂ e₂' : Trivialization F₂ (π F₂ E₂)}

local notation "LE₁E₂" => TotalSpace (F₁ →L[𝕜] F₂) (fun (b : B) ↦ E₁ b →L[𝕜] E₂ b)

section

/-
**contMDiffOn_continuousLinearMapCoordChange** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffOn_continuousLinearMapCoordChange [ContMDiffVectorBundle n F₁ E₁ 
IB] [ContMDiffVectorBundle n F₂ E₂ IB] [MemTrivializationAtlas e₁] [MemTrivializ
ationAtlas e₁'] [MemTrivializationAtlas e₂] [MemTrivializationAtlas e₂'] : CMDif
f[e₁.baseSet inter e₂.baseSet inter (e₁'.baseSet inter e₂'.baseSet)] n (continuo
usLinearMapCoordChange (RingHom.id 𝕜) e₁ e₁' e₂ e₂')
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `trivialization_linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → AddCom
mMonoid (E …
· 使用定理 `contMDiffOn_coordChangeL`：contMDiffOn_coordChangeL : ContMDiffOn IB 𝓘(𝕜,
 F ->L[𝕜] F) n (fun b : B => (e.coordChangeL 𝕜 e' b : F ->L[𝕜] F)) (e.baseSet in
ter e'.baseSet…
· 使用定理 `ContMDiffOn.cle_arrowCongr`：ContMDiffOn.cle_arrowCongr {f : M -> F₁ ≃L[𝕜
] F₂} {g : M -> F₃ ≃L[𝕜] F₄} {s : Set M} (hf : ContMDiffOn I 𝓘(𝕜, F₂ ->L[𝕜] F₁) 
n (fun x => ((f …
· 使用定理 `ContMDiffOn.mono`：ContMDiffOn.mono (hf : ContMDiffOn I I' n f s) (hts : 
t subseteq s) : ContMDiffOn I I' n f t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem contMDiffOn_continuousLinearMapCoordChange
    [ContMDiffVectorBundle n F₁ E₁ IB] [ContMDiffVectorBundle n F₂ E₂ IB]
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₁']
    [MemTrivializationAtlas e₂] [MemTrivializationAtlas e₂'] :
    CMDiff[e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)] n
      (continuousLinearMapCoordChange (RingHom.id 𝕜) e₁ e₁' e₂ e₂') := by
  have h₁ := contMDiffOn_coordChangeL (IB := IB) e₁' e₁ (n := n)
  have h₂ := contMDiffOn_coordChangeL (IB := IB) e₂ e₂' (n := n)
  refine (h₁.mono ?_).cle_arrowCongr (h₂.mono ?_) <;> mfld_set_tac

variable [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]

set_option backward.isDefEq.respectTransparency false in
/-
**hom_chart** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hom_chart (y₀ y : LE₁E₂) : chartAt (ModelProd HB (F₁ ->L[𝕜] F₂)) y₀ y = (c
hartAt HB y₀.1 y.1, inCoordinates F₁ E₁ F₂ E₂ y₀.1 y.1 y₀.1 y.1 y.2)
参数：y₀ y : LE₁E₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FiberBundle.chartedSpace_chartAt`：FiberBundle.chartedSpace_chartAt (x : 
TotalSpace F E) : chartAt (ModelProd HB F) x = (trivializationAt F E x.proj).toO
penPartialHomeomorph ≫…
· 使用定理 `OpenPartialHomeomorph.trans_apply`：trans_apply {x : X} : (e.trans e') x 
= e' (e x)
· 使用定理 `OpenPartialHomeomorph.prod_apply`：∀ {X : Type u_1} {X' : Type u_2} {Y : 
Type u_3} {Y' : Type u_4} [inst : TopologicalSpace X]   [inst_1 : TopologicalSpa
ce X'] [inst_2 : Topol…
· 使用定理 `Bundle.Trivialization.coe_coe`：∀ {B : Type u_1} {F : Type u_2} {Z : Type
 u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B}  
 [inst_2 : Topologi…
· 使用定理 `OpenPartialHomeomorph.refl_apply`：∀ (X : Type u_7) [inst : TopologicalSp
ace X], ↑(OpenPartialHomeomorph.refl X) = id
· 使用定理 `Function.id_def`：∀ {α : Sort u_1}, id = fun x => x
· 使用定理 `hom_trivializationAt_apply`：hom_trivializationAt_apply (x₀ : B) (x : Tot
alSpace (F₁ ->SL[σ] F₂) (fun x => E₁ x ->SL[σ] E₂ x)) : trivializationAt (F₁ ->S
L[σ] F₂) (fun x …
-/
theorem hom_chart (y₀ y : LE₁E₂) :
    chartAt (ModelProd HB (F₁ →L[𝕜] F₂)) y₀ y =
      (chartAt HB y₀.1 y.1, inCoordinates F₁ E₁ F₂ E₂ y₀.1 y.1 y₀.1 y.1 y.2) := by
  rw [FiberBundle.chartedSpace_chartAt, trans_apply, OpenPartialHomeomorph.prod_apply,
    Trivialization.coe_coe, OpenPartialHomeomorph.refl_apply, Function.id_def,
    hom_trivializationAt_apply]
/-
**contMDiffWithinAt_hom_bundle** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffWithinAt_hom_bundle (f : M -> LE₁E₂) {s : Set M} {x₀ : M} : CMDif
fAt[s] n f x₀ ↔ CMDiffAt[s] n (fun x => (f x).1) x₀ ∧ CMDiffAt[s] n (fun x => in
Coordinates F₁ E₁ F₂ E₂ (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) x₀
参数：f : M -> LE₁E₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.contMDiffWithinAt_totalSpace`：contMDiffWithinAt_totalSpace {f : M
 -> TotalSpace F E} {s : Set M} {x₀ : M} : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F)
) n f s x₀ ↔ ContMDiffWit…
-/
theorem contMDiffWithinAt_hom_bundle (f : M → LE₁E₂) {s : Set M} {x₀ : M} :
    CMDiffAt[s] n f x₀ ↔
      CMDiffAt[s] n (fun x ↦ (f x).1) x₀ ∧
        CMDiffAt[s] n
          (fun x ↦ inCoordinates F₁ E₁ F₂ E₂ (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) x₀ :=
  contMDiffWithinAt_totalSpace
/-
**contMDiffAt_hom_bundle** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiffAt_hom_bundle (f : M -> LE₁E₂) {x₀ : M} : CMDiffAt n f x₀ ↔ CMDif
fAt n (fun x => (f x).1) x₀ ∧ CMDiffAt n (fun x => inCoordinates F₁ E₁ F₂ E₂ (f 
x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) x₀
参数：f : M -> LE₁E₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.contMDiffAt_totalSpace`：contMDiffAt_totalSpace {f : M -> TotalSpa
ce F E} {x₀ : M} : ContMDiffAt IM (IB.prod 𝓘(𝕜, F)) n f x₀ ↔ ContMDiffAt IM IB n
 (fun x => (f x).pr…
-/
theorem contMDiffAt_hom_bundle (f : M → LE₁E₂) {x₀ : M} :
    CMDiffAt n f x₀ ↔
      CMDiffAt n (fun x ↦ (f x).1) x₀ ∧ CMDiffAt n
        (fun x ↦ inCoordinates F₁ E₁ F₂ E₂ (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) x₀ :=
  contMDiffAt_totalSpace

end

section

/-
**mdifferentiableOn_continuousLinearMapCoordChange** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableOn_continuousLinearMapCoordChange [ContMDiffVectorBundle 1 
F₁ E₁ IB] [ContMDiffVectorBundle 1 F₂ E₂ IB] [MemTrivializationAtlas e₁] [MemTri
vializationAtlas e₁'] [MemTrivializationAtlas e₂] [MemTrivializationAtlas e₂'] :
 MDiff[e₁.baseSet inter e₂.baseSet inter (e₁'.baseSet inter e₂'.baseSet)] (conti
nuousLinearMapCoordChange (RingHom.id 𝕜) e₁ e₁' e₂ e₂')
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `trivialization_linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → AddCom
mMonoid (E …
· 使用定理 `ContMDiffOn.mdifferentiableOn`：ContMDiffOn.mdifferentiableOn (hf : CMDif
f[s] n f) (hn : n != 0) : MDiff[s] f
· 使用定理 `contMDiffOn_coordChangeL`：contMDiffOn_coordChangeL : ContMDiffOn IB 𝓘(𝕜,
 F ->L[𝕜] F) n (fun b : B => (e.coordChangeL 𝕜 e' b : F ->L[𝕜] F)) (e.baseSet in
ter e'.baseSet…
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `MDifferentiableOn.cle_arrowCongr`：MDifferentiableOn.cle_arrowCongr {f : 
M -> F₁ ≃L[𝕜] F₂} {g : M -> F₃ ≃L[𝕜] F₄} {s : Set M} (hf : MDiff[s] (fun x => ((
f x).symm : F₂ ->L[𝕜] …
· 使用定理 `MDifferentiableOn.mono`：MDifferentiableOn.mono (h : MDiff[t] f) (st : s 
subseteq t) : MDiff[s] f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem mdifferentiableOn_continuousLinearMapCoordChange
    [ContMDiffVectorBundle 1 F₁ E₁ IB] [ContMDiffVectorBundle 1 F₂ E₂ IB]
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₁']
    [MemTrivializationAtlas e₂] [MemTrivializationAtlas e₂'] :
    MDiff[e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)]
      (continuousLinearMapCoordChange (RingHom.id 𝕜) e₁ e₁' e₂ e₂') := by
  have h₁ := contMDiffOn_coordChangeL (IB := IB) e₁' e₁ (n := 1) |>.mdifferentiableOn one_ne_zero
  have h₂ := contMDiffOn_coordChangeL (IB := IB) e₂ e₂' (n := 1) |>.mdifferentiableOn one_ne_zero
  refine (h₁.mono ?_).cle_arrowCongr (h₂.mono ?_) <;> mfld_set_tac

variable [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
/-
**mdifferentiableWithinAt_hom_bundle** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableWithinAt_hom_bundle (f : M -> LE₁E₂) {s : Set M} {x₀ : M} :
 MDiffAt[s] f x₀ ↔ MDiffAt[s] (fun x => (f x).1) x₀ ∧ MDiffAt[s] (fun x => inCoo
rdinates F₁ E₁ F₂ E₂ (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) x₀
参数：f : M -> LE₁E₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mdifferentiableWithinAt_totalSpace`：mdifferentiableWithinAt_totalSpace (
f : M -> TotalSpace F E) {s : Set M} {x₀ : M} : MDiffAt[s] f x₀ ↔ MDiffAt[s] (fu
n x => (f x).proj) x₀ ∧ …
-/
theorem mdifferentiableWithinAt_hom_bundle (f : M → LE₁E₂) {s : Set M} {x₀ : M} :
    MDiffAt[s] f x₀ ↔
      MDiffAt[s] (fun x ↦ (f x).1) x₀ ∧
        MDiffAt[s]
          (fun x ↦ inCoordinates F₁ E₁ F₂ E₂ (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) x₀ :=
  mdifferentiableWithinAt_totalSpace IB ..
/-
**mdifferentiableAt_hom_bundle** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableAt_hom_bundle (f : M -> LE₁E₂) {x₀ : M} : MDiffAt f x₀ ↔ MD
iffAt (fun x => (f x).1) x₀ ∧ MDiffAt (fun x => inCoordinates F₁ E₁ F₂ E₂ (f x₀)
.1 (f x).1 (f x₀).1 (f x).1 (f x).2) x₀
参数：f : M -> LE₁E₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mdifferentiableAt_totalSpace`：mdifferentiableAt_totalSpace (f : M -> Tot
alSpace F E) {x₀ : M} : MDiffAt f x₀ ↔ MDiffAt (fun x => (f x).proj) x₀ ∧ MDiffA
t (fun x => (trivi…
-/
theorem mdifferentiableAt_hom_bundle (f : M → LE₁E₂) {x₀ : M} :
    MDiffAt f x₀ ↔
      MDiffAt (fun x ↦ (f x).1) x₀ ∧
        MDiffAt (fun x ↦ inCoordinates F₁ E₁ F₂ E₂ (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) x₀ :=
  mdifferentiableAt_totalSpace ..

end

variable [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
  [ContMDiffVectorBundle n F₁ E₁ IB] [ContMDiffVectorBundle n F₂ E₂ IB]

/-
**Bundle.ContinuousLinearMap.vectorPrebundle.isContMDiff** 是 Mathlib 中的一个实例，位于命名
空间 ``。
形式化陈述：Bundle.ContinuousLinearMap.vectorPrebundle.isContMDiff : (Bundle.Continuou
sLinearMap.vectorPrebundle (RingHom.id 𝕜) F₁ E₁ F₂ E₂).IsContMDiff IB n where ex
ists_contMDiffCoordChange
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `trivialization_linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → AddCom
mMonoid (E …
· 使用定理 `contMDiffOn_continuousLinearMapCoordChange`：contMDiffOn_continuousLinear
MapCoordChange [ContMDiffVectorBundle n F₁ E₁ IB] [ContMDiffVectorBundle n F₂ E₂
 IB] [MemTrivializationAtlas e₁]…
· 使用定理 `Bundle.Pretrivialization.continuousLinearMapCoordChange_apply`：continuou
sLinearMapCoordChange_apply (b : B) (hb : b in e₁.baseSet inter e₂.baseSet inter
 (e₁'.baseSet inter e₂'.baseSet)) (L : F₁ ->SL[σ] F…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
instance Bundle.ContinuousLinearMap.vectorPrebundle.isContMDiff :
    (Bundle.ContinuousLinearMap.vectorPrebundle (RingHom.id 𝕜) F₁ E₁ F₂ E₂).IsContMDiff IB n where
  exists_contMDiffCoordChange := by
    rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩ _ ⟨e₁', e₂', he₁', he₂', rfl⟩
    exact ⟨continuousLinearMapCoordChange (RingHom.id 𝕜) e₁ e₁' e₂ e₂',
      contMDiffOn_continuousLinearMapCoordChange,
      continuousLinearMapCoordChange_apply (RingHom.id 𝕜) e₁ e₁' e₂ e₂'⟩
/-
**ContMDiffVectorBundle.continuousLinearMap** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：ContMDiffVectorBundle.continuousLinearMap : ContMDiffVectorBundle n (F₁ ->
L[𝕜] F₂) ((fun (b : B) => E₁ b ->L[𝕜] E₂ b)) IB
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `VectorPrebundle.contMDiffVectorBundle`：contMDiffVectorBundle : @ContMDif
fVectorBundle n _ _ F E _ _ _ _ _ _ IB _ _ _ _ _ _ a.totalSpaceTopology _ a.toFi
berBundle a.toVectorBundle
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
-/
instance ContMDiffVectorBundle.continuousLinearMap :
    ContMDiffVectorBundle n (F₁ →L[𝕜] F₂) ((fun (b : B) ↦ E₁ b →L[𝕜] E₂ b)) IB :=
  (Bundle.ContinuousLinearMap.vectorPrebundle (RingHom.id 𝕜) F₁ E₁ F₂ E₂).contMDiffVectorBundle IB

end

section symmL

variable {𝕜 B F₁ : Type*} [NontriviallyNormedField 𝕜] {n : WithTop ℕ∞}
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  {E₁ : B → Type*} [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [∀ x, IsTopologicalAddGroup (E₁ x)] [∀ x, ContinuousSMul 𝕜 (E₁ x)]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]

/-- Let `e` be a trivialization of a `C^n` vector bundle `E₁` over `B`. Then `m ↦ e.symmL 𝕜 m`
defines a section of the bundle of continuous linear maps `F₁ →L[𝕜] E₁` over `B`, and this section
is `C^n` at any point in `e.baseSet`. -/
/-
**Bundle.Trivialization.contMDiffAt_symmL** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Bundle.Trivialization.contMDiffAt_symmL [ContMDiffVectorBundle n F₁ E₁ IB]
 (e : Trivialization F₁ (TotalSpace.proj : TotalSpace F₁ E₁ -> B)) [MemTrivializ
ationAtlas e] {x : B} (hx : x in e.baseSet) : ContMDiffAt IB (IB.prod 𝓘(𝕜, F₁ ->
L[𝕜] F₁)) n (fun m => TotalSpace.mk' (F₁ ->L[𝕜] F₁) m (e.symmL 𝕜 m)) x
参数：e : Trivialization F₁ (TotalSpace.proj : TotalSpace F₁ E₁ -> B)；hx : x in e.b
aseSet。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiberBundle.mem_baseSet_trivializationAt`：mem_baseSet_trivializationAt :
 b in (trivializationAt F E b).baseSet
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `trivialization_linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → AddCom
mMonoid (E …
· 使用定理 `Bundle.contMDiffAt_totalSpace`：contMDiffAt_totalSpace {f : M -> TotalSpa
ce F E} {x₀ : M} : ContMDiffAt IM (IB.prod 𝓘(𝕜, F)) n f x₀ ↔ ContMDiffAt IM IB n
 (fun x => (f x).pr…
· 使用定理 `contMDiffAt_id`：contMDiffAt_id : ContMDiffAt I I n (id : M -> M) x
· 使用定理 `ContMDiffAt.congr_of_eventuallyEq`：ContMDiffAt.congr_of_eventuallyEq (h 
: ContMDiffAt I I' n f x) (h₁ : f₁ =ᶠ[𝓝 x] f) : ContMDiffAt I I' n f₁ x
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `instMemTrivializationAtlasTrivializationAt`：∀ {B : Type u_2} {F : Type u
_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {E : B → Type u_5}
   [inst_2 : TopologicalSpace (B…
· 使用定理 `contMDiffAt_coordChangeL`：contMDiffAt_coordChangeL {x : B} (h : x in e.b
aseSet) (h' : x in e'.baseSet) : ContMDiffAt IB 𝓘(𝕜, F ->L[𝕜] F) n (fun b : B =>
 (e.coordChang…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Bundle.Trivialization.open_baseSet`：∀ {B : Type u_1} {F : Type u_2} {Z :
 Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 :
 TopologicalSpace Z] {pr…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
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
· 使用定理 `Bundle.Trivial.symmL_trivialization`：∀ (𝕜 : Type u_1) (B : Type u_2) (F 
: Type u_3) [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup F]  
 [inst_2 : NormedSpace 𝕜 …
· 使用定理 `ContinuousLinearMap.comp_id`：comp_id (f : M₁ ->SL[σ₁₂] M₂) : f ∘SL .id R
₁ M₁ = f
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `Bundle.Trivialization.symmL_apply`：∀ {R : Type u_1} {B : Type u_2} {F : 
Type u_3} {E : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x :
 B) → AddCommMonoid (E …
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Bundle.Trivialization.continuousLinearMapAt_apply`：∀ (R : Type u_1) {B :
 Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : NontriviallyNormedField R] 
  [inst_1 : (x : B) → AddCommMonoid (E …
· 使用定理 `Bundle.Trivialization.coe_linearMapAt_of_mem`：∀ {R : Type u_1} {B : Type
 u_2} {F : Type u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : Topologica
lSpace F]   [inst_2 : TopologicalS…
· 使用定理 `Bundle.Trivialization.mk_symm`：∀ {B : Type u_1} {F : Type u_2} {E : B → 
Type u_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 : 
TopologicalSpace (B…
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `Bundle.Trivialization.coordChangeL_apply'`：∀ {R : Type u_1} {B : Type u_
2} {F : Type u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : TopologicalSp
ace F]   [inst_2 : TopologicalS…
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
Let `e` be a trivialization of a `C^n` vector bundle `E₁` over `B`. Then `m ↦ e.
symmL 𝕜 m`
defines a section of the bundle of continuous linear maps `F₁ →L[𝕜] E₁` over `B`
, and this section
is `C^n` at any point in `e.baseSet`.
-/
lemma Bundle.Trivialization.contMDiffAt_symmL [ContMDiffVectorBundle n F₁ E₁ IB]
    (e : Trivialization F₁ (TotalSpace.proj : TotalSpace F₁ E₁ → B)) [MemTrivializationAtlas e]
    {x : B} (hx : x ∈ e.baseSet) :
    ContMDiffAt IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₁)) n
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₁) m (e.symmL 𝕜 m)) x := by
  have hx' : x ∈ (trivializationAt F₁ E₁ x).baseSet := mem_baseSet_trivializationAt F₁ E₁ x
  refine contMDiffAt_totalSpace.mpr ⟨contMDiffAt_id, ?_⟩
  apply (contMDiffAt_coordChangeL hx hx').congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds hx,
    (trivializationAt F₁ E₁ x).open_baseSet.mem_nhds hx'] with b hb hb'
  ext v
  simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
    coordChangeL_apply' e _ ⟨hb, hb'⟩, coe_linearMapAt_of_mem _ hb',
    e.symmL_apply hb, e.mk_symm hb]

/-- Let `e` be a trivialization of a `C^n` vector bundle `E₁` over `B`. Then `m ↦ e.symmL 𝕜 m`
defines a section of the bundle of continuous linear maps `F₁ →L[𝕜] E₁` over `B`, and this section
is `C^n` on `e.baseSet`. -/
/-
**Bundle.Trivialization.contMDiffOn_symmL** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Bundle.Trivialization.contMDiffOn_symmL [ContMDiffVectorBundle n F₁ E₁ IB]
 (e : Trivialization F₁ (TotalSpace.proj : TotalSpace F₁ E₁ -> B)) [MemTrivializ
ationAtlas e] : ContMDiffOn IB (IB.prod 𝓘(𝕜, F₁ ->L[𝕜] F₁)) n (fun m => TotalSpa
ce.mk' (F₁ ->L[𝕜] F₁) m (e.symmL 𝕜 m)) e.baseSet
参数：e : Trivialization F₁ (TotalSpace.proj : TotalSpace F₁ E₁ -> B)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.contMDiffWithinAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
· 使用定理 `trivialization_linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → AddCom
mMonoid (E …
· 使用引理 `Bundle.Trivialization.contMDiffAt_symmL`：Bundle.Trivialization.contMDiff
At_symmL [ContMDiffVectorBundle n F₁ E₁ IB] (e : Trivialization F₁ (TotalSpace.p
roj : TotalSpace F₁ E₁ -> B))…

--- 原说明 ---
Let `e` be a trivialization of a `C^n` vector bundle `E₁` over `B`. Then `m ↦ e.
symmL 𝕜 m`
defines a section of the bundle of continuous linear maps `F₁ →L[𝕜] E₁` over `B`
, and this section
is `C^n` on `e.baseSet`.
-/
lemma Bundle.Trivialization.contMDiffOn_symmL [ContMDiffVectorBundle n F₁ E₁ IB]
    (e : Trivialization F₁ (TotalSpace.proj : TotalSpace F₁ E₁ → B)) [MemTrivializationAtlas e] :
    ContMDiffOn IB (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₁)) n
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₁) m (e.symmL 𝕜 m)) e.baseSet :=
  fun _ hx ↦ (e.contMDiffAt_symmL hx).contMDiffWithinAt

end symmL

section

/- Declare two manifolds `B₁` and `B₂` (with models `IB₁ : HB₁ → EB₁` and `IB₂ : HB₂ → EB₂`),
and two vector bundles `E₁` and `E₂` respectively over `B₁` and `B₂` (with model fibers
`F₁` and `F₂`).

Also a third manifold `M`, which will be the source of all our maps.
-/
variable {𝕜 F₁ F₂ B₁ B₂ M : Type*} {E₁ : B₁ → Type*} {E₂ : B₂ → Type*} [NontriviallyNormedField 𝕜]
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)] [∀ x, AddCommGroup (E₂ x)]
  [∀ x, Module 𝕜 (E₂ x)] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  {EB₁ : Type*}
  [NormedAddCommGroup EB₁] [NormedSpace 𝕜 EB₁] {HB₁ : Type*} [TopologicalSpace HB₁]
  {IB₁ : ModelWithCorners 𝕜 EB₁ HB₁} [TopologicalSpace B₁] [ChartedSpace HB₁ B₁]
  {EB₂ : Type*}
  [NormedAddCommGroup EB₂] [NormedSpace 𝕜 EB₂] {HB₂ : Type*} [TopologicalSpace HB₂]
  {IB₂ : ModelWithCorners 𝕜 EB₂ HB₂} [TopologicalSpace B₂] [ChartedSpace HB₂ B₂]
  {EM : Type*}
  [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  {n : WithTop ℕ∞} [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  {b₁ : M → B₁} {b₂ : M → B₂} {m₀ : M}
  {ϕ : Π (m : M), E₁ (b₁ m) →L[𝕜] E₂ (b₂ m)} {v : Π (m : M), E₁ (b₁ m)} {s : Set M}

/-- Consider a `C^n` map `v : M → E₁` to a vector bundle, over a base map `b₁ : M → B₁`, and
another base map `b₂ : M → B₂`. Given linear maps `ϕ m : E₁ (b₁ m) → E₂ (b₂ m)` depending smoothly
on `m`, one can apply `ϕ m` to `v m`, and the resulting map is `C^n`.

Note that the smoothness of `ϕ` cannot always be stated as smoothness of a map into a manifold,
as the pullback bundles `b₁ *ᵖ E₁` and `b₂ *ᵖ E₂` are smooth manifolds only when `b₁` and `b₂` are
globally smooth, but we want to apply this lemma with only local information. Therefore, we
formulate it using smoothness of `ϕ` read in coordinates.

Version for `ContMDiffWithinAt`. We also give a version for `ContMDiffAt`, but no version for
`ContMDiffOn` or `ContMDiff` as our assumption, written in coordinates, only makes sense around
a point.

For a version with `B₁ = B₂` and `b₁ = b₂`, in which smoothness can be expressed without
`inCoordinates`, see `ContMDiffWithinAt.clm_bundle_apply`.
-/
/-
**ContMDiffWithinAt.clm_apply_of_inCoordinates** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.clm_apply_of_inCoordinates (hϕ : CMDiffAt[s] n (fun m =>
 inCoordinates F₁ E₁ F₂ E₂ (b₁ m₀) (b₁ m) (b₂ m₀) (b₂ m) (ϕ m)) m₀) (hv : CMDiff
At[s] n (fun m => (v m : TotalSpace F₁ E₁)) m₀) (hb₂ : CMDiffAt[s] n b₂ m₀) : CM
DiffAt[s] n (fun m => (ϕ m (v m) : TotalSpace F₂ E₂)) m₀
参数：hϕ : CMDiffAt[s] n (fun m => inCoordinates F₁ E₁ F₂ E₂ (b₁ m₀) (b₁ m) (b₂ m₀)
 (b₂ m) (ϕ m)) m₀；hv : CMDiffAt[s] n (fun m => (v m : TotalSpace F₁ E₁)) m₀；hb₂ 
: CMDiffAt[s] n b₂ m₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `contMDiffWithinAt_insert_self`：contMDiffWithinAt_insert_self : ContMDiff
WithinAt I I' n f (insert x s) x ↔ ContMDiffWithinAt I I' n f s x
· 使用定理 `Bundle.contMDiffWithinAt_totalSpace`：contMDiffWithinAt_totalSpace {f : M
 -> TotalSpace F E} {s : Set M} {x₀ : M} : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F)
) n f s x₀ ↔ ContMDiffWit…
· 使用定理 `ContMDiffWithinAt.congr_of_eventuallyEq_of_mem`：ContMDiffWithinAt.congr_
of_eventuallyEq_of_mem (h : ContMDiffWithinAt I I' n f s x) (h₁ : f₁ =ᶠ[𝓝[s] x] 
f) (hx : x in s) : ContMDiffWithinAt…
· 使用定理 `ContMDiffWithinAt.clm_apply`：ContMDiffWithinAt.clm_apply {g : M -> F₁ ->
L[𝕜] F₂} {f : M -> F₁} {s : Set M} {x : M} (hg : ContMDiffWithinAt I 𝓘(𝕜, F₁ ->L
[𝕜] F₂) n g s x) …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ContMDiffWithinAt.continuousWithinAt`：ContMDiffWithinAt.continuousWithin
At (hf : ContMDiffWithinAt I I' n f s x) : ContinuousWithinAt f s x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Bundle.Trivialization.open_baseSet`：∀ {B : Type u_1} {F : Type u_2} {Z :
 Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 :
 TopologicalSpace Z] {pr…
· 使用定理 `FiberBundle.mem_baseSet_trivializationAt'`：∀ {B : Type u_2} {F : Type u_
3} {inst : TopologicalSpace B} {inst_1 : TopologicalSpace F} {E : B → Type u_5} 
  {inst_2 : TopologicalSpace (B…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `trivialization_linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → AddCom
mMonoid (E …
· 使用定理 `instMemTrivializationAtlasTrivializationAt`：∀ {B : Type u_2} {F : Type u
_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {E : B → Type u_5}
   [inst_2 : TopologicalSpace (B…
· 使用定理 `ContinuousLinearMap.inCoordinates_eq`：∀ {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : (x : B) → AddCommMonoid (E x)]   [inst_1 : NormedAddCom
mGroup F] [inst_2 : Topolo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Bundle.Trivialization.continuousLinearEquivAt_symm_apply`：∀ (R : Type u_
1) {B : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : NontriviallyNormedFi
eld R]   [inst_1 : (x : B) → AddCommMonoid (E …
· 使用定理 `Bundle.Trivialization.symm_apply_apply_mk`：∀ {B : Type u_1} {F : Type u_
2} {E : B → Type u_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] 
  [inst_2 : TopologicalSpace (B…
· 使用定理 `Bundle.Trivialization.continuousLinearEquivAt_apply`：∀ (R : Type u_1) {B
 : Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : NontriviallyNormedField R
]   [inst_1 : (x : B) → AddCommMonoid (E …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s

--- 原说明 ---
Consider a `C^n` map `v : M → E₁` to a vector bundle, over a base map `b₁ : M → 
B₁`, and
another base map `b₂ : M → B₂`. Given linear maps `ϕ m : E₁ (b₁ m) → E₂ (b₂ m)` 
depending smoothly
on `m`, one can apply `ϕ m` to `v m`, and the resulting map is `C^n`.

Note that the smoothness of `ϕ` cannot always be stated as smoothness of a map i
nto a manifold,
as the pullback bundles `b₁ *ᵖ E₁` and `b₂ *ᵖ E₂` are smooth manifolds only when
 `b₁` and `b₂` are
globally smooth, but we want to apply this lemma with only local information. Th
erefore, we
formulate it using smoothness of `ϕ` read in coordinates.

Version for `ContMDiffWithinAt`. We also give a version for `ContMDiffAt`, but n
o version for
`ContMDiffOn` or `ContMDiff` as our assumption, written in coordinates, only mak
es sense around
a point.

For a version with `B₁ = B₂` and `b₁ = b₂`, in which smoothness can be expressed
 without
`inCoordinates`, see `ContMDiffWithinAt.clm_bundle_apply`.
-/
lemma ContMDiffWithinAt.clm_apply_of_inCoordinates
    (hϕ : CMDiffAt[s] n
      (fun m ↦ inCoordinates F₁ E₁ F₂ E₂ (b₁ m₀) (b₁ m) (b₂ m₀) (b₂ m) (ϕ m)) m₀)
    (hv : CMDiffAt[s] n (fun m ↦ (v m : TotalSpace F₁ E₁)) m₀) (hb₂ : CMDiffAt[s] n b₂ m₀) :
    CMDiffAt[s] n (fun m ↦ (ϕ m (v m) : TotalSpace F₂ E₂)) m₀ := by
  rw [← contMDiffWithinAt_insert_self] at hϕ hv hb₂ ⊢
  rw [contMDiffWithinAt_totalSpace] at hv ⊢
  refine ⟨hb₂, ?_⟩
  apply (ContMDiffWithinAt.clm_apply hϕ hv.2).congr_of_eventuallyEq_of_mem ?_ (mem_insert m₀ s)
  have A : ∀ᶠ m in 𝓝[insert m₀ s] m₀, b₁ m ∈ (trivializationAt F₁ E₁ (b₁ m₀)).baseSet := by
    apply hv.1.continuousWithinAt
    apply (trivializationAt F₁ E₁ (b₁ m₀)).open_baseSet.mem_nhds
    exact FiberBundle.mem_baseSet_trivializationAt' (b₁ m₀)
  have A' : ∀ᶠ m in 𝓝[insert m₀ s] m₀, b₂ m ∈ (trivializationAt F₂ E₂ (b₂ m₀)).baseSet := by
    apply hb₂.continuousWithinAt
    apply (trivializationAt F₂ E₂ (b₂ m₀)).open_baseSet.mem_nhds
    exact FiberBundle.mem_baseSet_trivializationAt' (b₂ m₀)
  filter_upwards [A, A'] with m hm h'm
  rw [inCoordinates_eq hm h'm]
  simp [*]

/-- Consider a `C^n` map `v : M → E₁` to a vector bundle, over a base map `b₁ : M → B₁`, and
another base map `b₂ : M → B₂`. Given linear maps `ϕ m : E₁ (b₁ m) → E₂ (b₂ m)` depending smoothly
on `m`, one can apply `ϕ m` to `v m`, and the resulting map is `C^n`.

Note that the smoothness of `ϕ` cannot always be stated as smoothness of a map into a manifold,
as the pullback bundles `b₁ *ᵖ E₁` and `b₂ *ᵖ E₂` are smooth manifolds only when `b₁` and `b₂` are
globally smooth, but we want to apply this lemma with only local information. Therefore, we
formulate it using smoothness of `ϕ` read in coordinates.

Version for `ContMDiffAt`. We also give a version for `ContMDiffWithinAt`, but no version for
`ContMDiffOn` or `ContMDiff` as our assumption, written in coordinates, only makes sense around
a point.

For a version with `B₁ = B₂` and `b₁ = b₂`, in which smoothness can be expressed without
`inCoordinates`, see `ContMDiffAt.clm_bundle_apply`.
-/
/-
**ContMDiffAt.clm_apply_of_inCoordinates** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiffAt.clm_apply_of_inCoordinates (hϕ : CMDiffAt n (fun m => inCoordi
nates F₁ E₁ F₂ E₂ (b₁ m₀) (b₁ m) (b₂ m₀) (b₂ m) (ϕ m)) m₀) (hv : CMDiffAt n (fun
 m => (v m : TotalSpace F₁ E₁)) m₀) (hb₂ : CMDiffAt n b₂ m₀) : CMDiffAt n (fun m
 => (ϕ m (v m) : TotalSpace F₂ E₂)) m₀
参数：hϕ : CMDiffAt n (fun m => inCoordinates F₁ E₁ F₂ E₂ (b₁ m₀) (b₁ m) (b₂ m₀) (b
₂ m) (ϕ m)) m₀；hv : CMDiffAt n (fun m => (v m : TotalSpace F₁ E₁)) m₀；hb₂ : CMDi
ffAt n b₂ m₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `contMDiffWithinAt_univ`：contMDiffWithinAt_univ : ContMDiffWithinAt I I' 
n f univ x ↔ ContMDiffAt I I' n f x
· 使用引理 `ContMDiffWithinAt.clm_apply_of_inCoordinates`：ContMDiffWithinAt.clm_appl
y_of_inCoordinates (hϕ : CMDiffAt[s] n (fun m => inCoordinates F₁ E₁ F₂ E₂ (b₁ m
₀) (b₁ m) (b₂ m₀) (b₂ m) (ϕ m)) m₀…

--- 原说明 ---
Consider a `C^n` map `v : M → E₁` to a vector bundle, over a base map `b₁ : M → 
B₁`, and
another base map `b₂ : M → B₂`. Given linear maps `ϕ m : E₁ (b₁ m) → E₂ (b₂ m)` 
depending smoothly
on `m`, one can apply `ϕ m` to `v m`, and the resulting map is `C^n`.

Note that the smoothness of `ϕ` cannot always be stated as smoothness of a map i
nto a manifold,
as the pullback bundles `b₁ *ᵖ E₁` and `b₂ *ᵖ E₂` are smooth manifolds only when
 `b₁` and `b₂` are
globally smooth, but we want to apply this lemma with only local information. Th
erefore, we
formulate it using smoothness of `ϕ` read in coordinates.

Version for `ContMDiffAt`. We also give a version for `ContMDiffWithinAt`, but n
o version for
`ContMDiffOn` or `ContMDiff` as our assumption, written in coordinates, only mak
es sense around
a point.

For a version with `B₁ = B₂` and `b₁ = b₂`, in which smoothness can be expressed
 without
`inCoordinates`, see `ContMDiffAt.clm_bundle_apply`.
-/
lemma ContMDiffAt.clm_apply_of_inCoordinates
    (hϕ : CMDiffAt n (fun m ↦ inCoordinates F₁ E₁ F₂ E₂ (b₁ m₀) (b₁ m) (b₂ m₀) (b₂ m) (ϕ m)) m₀)
    (hv : CMDiffAt n (fun m ↦ (v m : TotalSpace F₁ E₁)) m₀) (hb₂ : CMDiffAt n b₂ m₀) :
    CMDiffAt n (fun m ↦ (ϕ m (v m) : TotalSpace F₂ E₂)) m₀ := by
  rw [← contMDiffWithinAt_univ] at hϕ hv hb₂ ⊢
  exact ContMDiffWithinAt.clm_apply_of_inCoordinates hϕ hv hb₂

end

section

/- Declare a manifold `B` (with model `IB : HB → EB`),
and three vector bundles `E₁`, `E₂` and `E₃` over `B` (with model fibers `F₁`, `F₂` and `F₃`).

Also a second manifold `M`, which will be the source of all our maps.
-/
variable {𝕜 B F₁ F₂ F₃ M : Type*} [NontriviallyNormedField 𝕜] {n : WithTop ℕ∞}
  {E₁ : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  {E₂ : B → Type*} [∀ x, AddCommGroup (E₂ x)]
  [∀ x, Module 𝕜 (E₂ x)] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  {E₃ : B → Type*} [∀ x, AddCommGroup (E₃ x)]
  [∀ x, Module 𝕜 (E₃ x)] [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
  [TopologicalSpace (TotalSpace F₃ E₃)] [∀ x, TopologicalSpace (E₃ x)]
  {EB : Type*}
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B] {EM : Type*}
  [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [FiberBundle F₃ E₃] [VectorBundle 𝕜 F₃ E₃]
  {b : M → B} {v : ∀ x, E₁ (b x)} {s : Set M} {x : M}

section OneVariable

variable [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
  {ϕ : ∀ x, (E₁ (b x) →L[𝕜] E₂ (b x))}

/-- Consider a `C^n` map `v : M → E₁` to a vector bundle, over a base map `b : M → B`, and
linear maps `ϕ m : E₁ (b m) → E₂ (b m)` depending smoothly on `m`.
One can apply `ϕ m` to `v m`, and the resulting map is `C^n`.

We give here a version of this statement within a set at a point. -/
/-
**ContMDiffWithinAt.clm_bundle_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.clm_bundle_apply (hϕ : CMDiffAt[s] n (fun m => TotalSpac
e.mk' (F₁ ->L[𝕜] F₂) (E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `ContMDiffWithinAt.clm_apply_of_inCoordinates`：ContMDiffWithinAt.clm_appl
y_of_inCoordinates (hϕ : CMDiffAt[s] n (fun m => inCoordinates F₁ E₁ F₂ E₂ (b₁ m
₀) (b₁ m) (b₂ m₀) (b₂ m) (ϕ m)) m₀…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
Consider a `C^n` map `v : M → E₁` to a vector bundle, over a base map `b : M → B
`, and
linear maps `ϕ m : E₁ (b m) → E₂ (b m)` depending smoothly on `m`.
One can apply `ϕ m` to `v m`, and the resulting map is `C^n`.

We give here a version of this statement within a set at a point.
-/
lemma ContMDiffWithinAt.clm_bundle_apply
    (hϕ : CMDiffAt[s] n
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ϕ m)) x)
    (hv : CMDiffAt[s] n (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) x) :
    CMDiffAt[s] n (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (v m))) x := by
  simp only [contMDiffWithinAt_hom_bundle] at hϕ
  exact hϕ.2.clm_apply_of_inCoordinates hv hϕ.1

/-- Consider a `C^n` map `v : M → E₁` to a vector bundle, over a base map `b : M → B`, and
linear maps `ϕ m : E₁ (b m) → E₂ (b m)` depending smoothly on `m`.
One can apply `ϕ m` to `v m`, and the resulting map is `C^n`.

We give here a version of this statement at a point. -/
/-
**ContMDiffAt.clm_bundle_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiffAt.clm_bundle_apply (hϕ : CMDiffAt n (fun m => TotalSpace.mk' (F₁
 ->L[𝕜] F₂) (E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `ContMDiffWithinAt.clm_bundle_apply`：ContMDiffWithinAt.clm_bundle_apply (
hϕ : CMDiffAt[s] n (fun m => TotalSpace.mk' (F₁ ->L[𝕜] F₂) (E

--- 原说明 ---
Consider a `C^n` map `v : M → E₁` to a vector bundle, over a base map `b : M → B
`, and
linear maps `ϕ m : E₁ (b m) → E₂ (b m)` depending smoothly on `m`.
One can apply `ϕ m` to `v m`, and the resulting map is `C^n`.

We give here a version of this statement at a point.
-/
lemma ContMDiffAt.clm_bundle_apply
    (hϕ : CMDiffAt n
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ϕ m)) x)
    (hv : CMDiffAt n (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) x) :
    CMDiffAt n (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (v m))) x :=
  ContMDiffWithinAt.clm_bundle_apply hϕ hv

/-- Consider a `C^n` map `v : M → E₁` to a vector bundle, over a base map `b : M → B`, and
linear maps `ϕ m : E₁ (b m) → E₂ (b m)` depending smoothly on `m`.
One can apply `ϕ m` to `v m`, and the resulting map is `C^n`.

We give here a version of this statement on a set. -/
/-
**ContMDiffOn.clm_bundle_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiffOn.clm_bundle_apply (hϕ : CMDiff[s] n (fun m => TotalSpace.mk' (F
₁ ->L[𝕜] F₂) (E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `ContMDiffWithinAt.clm_bundle_apply`：ContMDiffWithinAt.clm_bundle_apply (
hϕ : CMDiffAt[s] n (fun m => TotalSpace.mk' (F₁ ->L[𝕜] F₂) (E

--- 原说明 ---
Consider a `C^n` map `v : M → E₁` to a vector bundle, over a base map `b : M → B
`, and
linear maps `ϕ m : E₁ (b m) → E₂ (b m)` depending smoothly on `m`.
One can apply `ϕ m` to `v m`, and the resulting map is `C^n`.

We give here a version of this statement on a set.
-/
lemma ContMDiffOn.clm_bundle_apply
    (hϕ : CMDiff[s] n
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ϕ m)))
    (hv : CMDiff[s] n (fun m ↦ TotalSpace.mk' F₁ (b m) (v m))) :
    CMDiff[s] n (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (v m))) :=
  fun x hx ↦ (hϕ x hx).clm_bundle_apply (hv x hx)

/-- Consider a `C^n` map `v : M → E₁` to a vector bundle, over a base map `b : M → B`, and
linear maps `ϕ m : E₁ (b m) → E₂ (b m)` depending smoothly on `m`.
One can apply `ϕ m` to `v m`, and the resulting map is `C^n`. -/
/-
**ContMDiff.clm_bundle_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiff.clm_bundle_apply (hϕ : CMDiff n (fun m => TotalSpace.mk' (F₁ ->L
[𝕜] F₂) (E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `ContMDiffAt.clm_bundle_apply`：ContMDiffAt.clm_bundle_apply (hϕ : CMDiffA
t n (fun m => TotalSpace.mk' (F₁ ->L[𝕜] F₂) (E

--- 原说明 ---
Consider a `C^n` map `v : M → E₁` to a vector bundle, over a base map `b : M → B
`, and
linear maps `ϕ m : E₁ (b m) → E₂ (b m)` depending smoothly on `m`.
One can apply `ϕ m` to `v m`, and the resulting map is `C^n`.
-/
lemma ContMDiff.clm_bundle_apply
    (hϕ : CMDiff n
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ϕ m)))
    (hv : CMDiff n (fun m ↦ TotalSpace.mk' F₁ (b m) (v m))) :
    CMDiff n (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (v m))) :=
  fun x ↦ (hϕ x).clm_bundle_apply (hv x)

end OneVariable

section OneVariable'

variable [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
  {ϕ : ∀ x, (E₁ (b x) →L[𝕜] E₂ (b x))}

/-- Consider a differentiable map `v : M → E₁` to a vector bundle, over a base map `b : M → B`, and
linear maps `ϕ m : E₁ (b m) → E₂ (b m)` depending smoothly on `m`.
One can apply `ϕ m` to `v m`, and the resulting map is differentiable.

We give here a version of this statement within a set at a point. -/
/-
**MDifferentiableWithinAt.clm_bundle_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MDifferentiableWithinAt.clm_bundle_apply (hϕ : MDiffAt[s] (fun m => TotalS
pace.mk' (F₁ ->L[𝕜] F₂) (E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `MDifferentiableWithinAt.clm_apply_of_inCoordinates`：MDifferentiableWithi
nAt.clm_apply_of_inCoordinates (hϕ : MDiffAt[s] (fun m => inCoordinates F₁ E₁ F₂
 E₂ (b₁ m₀) (b₁ m) (b₂ m₀) (b₂ m) (ϕ m))…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
Consider a differentiable map `v : M → E₁` to a vector bundle, over a base map `
b : M → B`, and
linear maps `ϕ m : E₁ (b m) → E₂ (b m)` depending smoothly on `m`.
One can apply `ϕ m` to `v m`, and the resulting map is differentiable.

We give here a version of this statement within a set at a point.
-/
lemma MDifferentiableWithinAt.clm_bundle_apply
    (hϕ : MDiffAt[s]
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ϕ m)) x)
    (hv : MDiffAt[s] (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) x) :
    MDiffAt[s] (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (v m))) x := by
  simp only [mdifferentiableWithinAt_hom_bundle] at hϕ
  exact hϕ.2.clm_apply_of_inCoordinates hv hϕ.1

/-- Consider a differentiable map `v : M → E₁` to a vector bundle, over a base map `b : M → B`, and
linear maps `ϕ m : E₁ (b m) → E₂ (b m)` depending smoothly on `m`.
One can apply `ϕ m` to `v m`, and the resulting map is differentiable.

We give here a version of this statement at a point. -/
/-
**MDifferentiableAt.clm_bundle_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MDifferentiableAt.clm_bundle_apply (hϕ : MDiffAt (fun m => TotalSpace.mk' 
(F₁ ->L[𝕜] F₂) (E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `MDifferentiableWithinAt.clm_bundle_apply`：MDifferentiableWithinAt.clm_bu
ndle_apply (hϕ : MDiffAt[s] (fun m => TotalSpace.mk' (F₁ ->L[𝕜] F₂) (E

--- 原说明 ---
Consider a differentiable map `v : M → E₁` to a vector bundle, over a base map `
b : M → B`, and
linear maps `ϕ m : E₁ (b m) → E₂ (b m)` depending smoothly on `m`.
One can apply `ϕ m` to `v m`, and the resulting map is differentiable.

We give here a version of this statement at a point.
-/
lemma MDifferentiableAt.clm_bundle_apply
    (hϕ : MDiffAt
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ϕ m)) x)
    (hv : MDiffAt (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) x) :
    MDiffAt (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (v m))) x :=
  MDifferentiableWithinAt.clm_bundle_apply hϕ hv

/-- Consider a differentiable map `v : M → E₁` to a vector bundle, over a base map `b : M → B`, and
linear maps `ϕ m : E₁ (b m) → E₂ (b m)` depending smoothly on `m`.
One can apply `ϕ m` to `v m`, and the resulting map is differentiable.

We give here a version of this statement on a set. -/
/-
**MDifferentiableOn.clm_bundle_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MDifferentiableOn.clm_bundle_apply (hϕ : MDiff[s] (fun m => TotalSpace.mk'
 (F₁ ->L[𝕜] F₂) (E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `MDifferentiableWithinAt.clm_bundle_apply`：MDifferentiableWithinAt.clm_bu
ndle_apply (hϕ : MDiffAt[s] (fun m => TotalSpace.mk' (F₁ ->L[𝕜] F₂) (E

--- 原说明 ---
Consider a differentiable map `v : M → E₁` to a vector bundle, over a base map `
b : M → B`, and
linear maps `ϕ m : E₁ (b m) → E₂ (b m)` depending smoothly on `m`.
One can apply `ϕ m` to `v m`, and the resulting map is differentiable.

We give here a version of this statement on a set.
-/
lemma MDifferentiableOn.clm_bundle_apply
    (hϕ : MDiff[s]
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ϕ m)))
    (hv : MDiff[s] (fun m ↦ TotalSpace.mk' F₁ (b m) (v m))) :
    MDiff[s] (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (v m))) :=
  fun x hx ↦ (hϕ x hx).clm_bundle_apply (hv x hx)

/-- Consider a differentiable map `v : M → E₁` to a vector bundle, over a base map `b : M → B`, and
linear maps `ϕ m : E₁ (b m) → E₂ (b m)` depending smoothly on `m`.
One can apply `ϕ m` to `v m`, and the resulting map is differentiable. -/
/-
**MDifferentiable.clm_bundle_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MDifferentiable.clm_bundle_apply (hϕ : MDiff (fun m => TotalSpace.mk' (F₁ 
->L[𝕜] F₂) (E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `MDifferentiableAt.clm_bundle_apply`：MDifferentiableAt.clm_bundle_apply (
hϕ : MDiffAt (fun m => TotalSpace.mk' (F₁ ->L[𝕜] F₂) (E

--- 原说明 ---
Consider a differentiable map `v : M → E₁` to a vector bundle, over a base map `
b : M → B`, and
linear maps `ϕ m : E₁ (b m) → E₂ (b m)` depending smoothly on `m`.
One can apply `ϕ m` to `v m`, and the resulting map is differentiable.
-/
lemma MDifferentiable.clm_bundle_apply
    (hϕ : MDiff
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ϕ m)))
    (hv : MDiff (fun m ↦ TotalSpace.mk' F₁ (b m) (v m))) :
    MDiff (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (v m))) :=
  fun x ↦ (hϕ x).clm_bundle_apply (hv x)

end OneVariable'

section TwoVariables

variable [∀ x, IsTopologicalAddGroup (E₃ x)] [∀ x, ContinuousSMul 𝕜 (E₃ x)]
  {ψ : ∀ x, (E₁ (b x) →L[𝕜] E₂ (b x) →L[𝕜] E₃ (b x))} {w : ∀ x, E₂ (b x)}

/-- Consider `C^n` maps `v : M → E₁` and `w : M → E₂` to vector bundles, over a base map
`b : M → B`, and bilinear maps `ψ m : E₁ (b m) → E₂ (b m) → E₃ (b m)` depending smoothly on `m`.
One can apply `ψ  m` to `v m` and `w m`, and the resulting map is `C^n`.

We give here a version of this statement within a set at a point. -/
/-
**ContMDiffWithinAt.clm_bundle_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.clm_bundle_apply (hϕ : CMDiffAt[s] n (fun m => TotalSpac
e.mk' (F₁ ->L[𝕜] F₂) (E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `ContMDiffWithinAt.clm_apply_of_inCoordinates`：ContMDiffWithinAt.clm_appl
y_of_inCoordinates (hϕ : CMDiffAt[s] n (fun m => inCoordinates F₁ E₁ F₂ E₂ (b₁ m
₀) (b₁ m) (b₂ m₀) (b₂ m) (ϕ m)) m₀…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
Consider `C^n` maps `v : M → E₁` and `w : M → E₂` to vector bundles, over a base
 map
`b : M → B`, and bilinear maps `ψ m : E₁ (b m) → E₂ (b m) → E₃ (b m)` depending 
smoothly on `m`.
One can apply `ψ  m` to `v m` and `w m`, and the resulting map is `C^n`.

We give here a version of this statement within a set at a point.
-/
lemma ContMDiffWithinAt.clm_bundle_apply₂
    (hψ : CMDiffAt[s] n (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
      (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x →L[𝕜] E₃ x)) (b m) (ψ m)) x)
    (hv : CMDiffAt[s] n (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) x)
    (hw : CMDiffAt[s] n (fun m ↦ TotalSpace.mk' F₂ (b m) (w m)) x) :
    CMDiffAt[s] n (fun m ↦ TotalSpace.mk' F₃ (b m) (ψ m (v m) (w m))) x :=
  hψ.clm_bundle_apply hv |>.clm_bundle_apply hw

/-- Consider `C^n` maps `v : M → E₁` and `w : M → E₂` to vector bundles, over a base map
`b : M → B`, and bilinear maps `ψ m : E₁ (b m) → E₂ (b m) → E₃ (b m)` depending smoothly on `m`.
One can apply `ψ  m` to `v m` and `w m`, and the resulting map is `C^n`.

We give here a version of this statement at a point. -/
/-
**ContMDiffAt.clm_bundle_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiffAt.clm_bundle_apply (hϕ : CMDiffAt n (fun m => TotalSpace.mk' (F₁
 ->L[𝕜] F₂) (E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `ContMDiffWithinAt.clm_bundle_apply`：ContMDiffWithinAt.clm_bundle_apply (
hϕ : CMDiffAt[s] n (fun m => TotalSpace.mk' (F₁ ->L[𝕜] F₂) (E

--- 原说明 ---
Consider `C^n` maps `v : M → E₁` and `w : M → E₂` to vector bundles, over a base
 map
`b : M → B`, and bilinear maps `ψ m : E₁ (b m) → E₂ (b m) → E₃ (b m)` depending 
smoothly on `m`.
One can apply `ψ  m` to `v m` and `w m`, and the resulting map is `C^n`.

We give here a version of this statement at a point.
-/
lemma ContMDiffAt.clm_bundle_apply₂
    (hψ : CMDiffAt n (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
      (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x →L[𝕜] E₃ x)) (b m) (ψ m)) x)
    (hv : CMDiffAt n (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) x)
    (hw : CMDiffAt n (fun m ↦ TotalSpace.mk' F₂ (b m) (w m)) x) :
    CMDiffAt n (fun m ↦ TotalSpace.mk' F₃ (b m) (ψ m (v m) (w m))) x :=
  ContMDiffWithinAt.clm_bundle_apply₂ hψ hv hw

/-- Consider `C^n` maps `v : M → E₁` and `w : M → E₂` to vector bundles, over a base map
`b : M → B`, and bilinear maps `ψ m : E₁ (b m) → E₂ (b m) → E₃ (b m)` depending smoothly on `m`.
One can apply `ψ  m` to `v m` and `w m`, and the resulting map is `C^n`.

We give here a version of this statement on a set. -/
/-
**ContMDiffOn.clm_bundle_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiffOn.clm_bundle_apply (hϕ : CMDiff[s] n (fun m => TotalSpace.mk' (F
₁ ->L[𝕜] F₂) (E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `ContMDiffWithinAt.clm_bundle_apply`：ContMDiffWithinAt.clm_bundle_apply (
hϕ : CMDiffAt[s] n (fun m => TotalSpace.mk' (F₁ ->L[𝕜] F₂) (E

--- 原说明 ---
Consider `C^n` maps `v : M → E₁` and `w : M → E₂` to vector bundles, over a base
 map
`b : M → B`, and bilinear maps `ψ m : E₁ (b m) → E₂ (b m) → E₃ (b m)` depending 
smoothly on `m`.
One can apply `ψ  m` to `v m` and `w m`, and the resulting map is `C^n`.

We give here a version of this statement on a set.
-/
lemma ContMDiffOn.clm_bundle_apply₂
    (hψ : CMDiff[s] n (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
      (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x →L[𝕜] E₃ x)) (b m) (ψ m)))
    (hv : CMDiff[s] n (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)))
    (hw : CMDiff[s] n (fun m ↦ TotalSpace.mk' F₂ (b m) (w m))) :
    CMDiff[s] n (fun m ↦ TotalSpace.mk' F₃ (b m) (ψ m (v m) (w m))) :=
  fun x hx ↦ (hψ x hx).clm_bundle_apply₂ (hv x hx) (hw x hx)

/-- Consider `C^n` maps `v : M → E₁` and `w : M → E₂` to vector bundles, over a base map
`b : M → B`, and bilinear maps `ψ m : E₁ (b m) → E₂ (b m) → E₃ (b m)` depending smoothly on `m`.
One can apply `ψ  m` to `v m` and `w m`, and the resulting map is `C^n`. -/
/-
**ContMDiff.clm_bundle_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContMDiff.clm_bundle_apply (hϕ : CMDiff n (fun m => TotalSpace.mk' (F₁ ->L
[𝕜] F₂) (E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `ContMDiffAt.clm_bundle_apply`：ContMDiffAt.clm_bundle_apply (hϕ : CMDiffA
t n (fun m => TotalSpace.mk' (F₁ ->L[𝕜] F₂) (E

--- 原说明 ---
Consider `C^n` maps `v : M → E₁` and `w : M → E₂` to vector bundles, over a base
 map
`b : M → B`, and bilinear maps `ψ m : E₁ (b m) → E₂ (b m) → E₃ (b m)` depending 
smoothly on `m`.
One can apply `ψ  m` to `v m` and `w m`, and the resulting map is `C^n`.
-/
lemma ContMDiff.clm_bundle_apply₂
    (hψ : CMDiff n (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
      (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x →L[𝕜] E₃ x)) (b m) (ψ m)))
    (hv : CMDiff n (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)))
    (hw : CMDiff n (fun m ↦ TotalSpace.mk' F₂ (b m) (w m))) :
    CMDiff n (fun m ↦ TotalSpace.mk' F₃ (b m) (ψ m (v m) (w m))) :=
  fun x ↦ (hψ x).clm_bundle_apply₂ (hv x) (hw x)

end TwoVariables

section TwoVariables'

variable [∀ x, IsTopologicalAddGroup (E₃ x)] [∀ x, ContinuousSMul 𝕜 (E₃ x)]
  {ψ : ∀ x, (E₁ (b x) →L[𝕜] E₂ (b x) →L[𝕜] E₃ (b x))} {w : ∀ x, E₂ (b x)}

/-- Consider differentiable maps `v : M → E₁` and `w : M → E₂` to vector bundles, over a base map
`b : M → B`, and bilinear maps `ψ m : E₁ (b m) → E₂ (b m) → E₃ (b m)` depending smoothly on `m`.
One can apply `ψ  m` to `v m` and `w m`, and the resulting map is differentiable.

We give here a version of this statement within a set at a point. -/
/-
**MDifferentiableWithinAt.clm_bundle_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MDifferentiableWithinAt.clm_bundle_apply (hϕ : MDiffAt[s] (fun m => TotalS
pace.mk' (F₁ ->L[𝕜] F₂) (E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `MDifferentiableWithinAt.clm_apply_of_inCoordinates`：MDifferentiableWithi
nAt.clm_apply_of_inCoordinates (hϕ : MDiffAt[s] (fun m => inCoordinates F₁ E₁ F₂
 E₂ (b₁ m₀) (b₁ m) (b₂ m₀) (b₂ m) (ϕ m))…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
Consider differentiable maps `v : M → E₁` and `w : M → E₂` to vector bundles, ov
er a base map
`b : M → B`, and bilinear maps `ψ m : E₁ (b m) → E₂ (b m) → E₃ (b m)` depending 
smoothly on `m`.
One can apply `ψ  m` to `v m` and `w m`, and the resulting map is differentiable
.

We give here a version of this statement within a set at a point.
-/
lemma MDifferentiableWithinAt.clm_bundle_apply₂
    (hψ : MDiffAt[s] (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
      (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x →L[𝕜] E₃ x)) (b m) (ψ m)) x)
    (hv : MDiffAt[s] (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) x)
    (hw : MDiffAt[s] (fun m ↦ TotalSpace.mk' F₂ (b m) (w m)) x) :
    MDiffAt[s] (fun m ↦ TotalSpace.mk' F₃ (b m) (ψ m (v m) (w m))) x :=
  hψ.clm_bundle_apply hv |>.clm_bundle_apply hw

/-- Consider differentiable maps `v : M → E₁` and `w : M → E₂` to vector bundles, over a base map
`b : M → B`, and bilinear maps `ψ m : E₁ (b m) → E₂ (b m) → E₃ (b m)` depending smoothly on `m`.
One can apply `ψ  m` to `v m` and `w m`, and the resulting map is differentiable.

We give here a version of this statement at a point. -/
/-
**MDifferentiableAt.clm_bundle_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MDifferentiableAt.clm_bundle_apply (hϕ : MDiffAt (fun m => TotalSpace.mk' 
(F₁ ->L[𝕜] F₂) (E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `MDifferentiableWithinAt.clm_bundle_apply`：MDifferentiableWithinAt.clm_bu
ndle_apply (hϕ : MDiffAt[s] (fun m => TotalSpace.mk' (F₁ ->L[𝕜] F₂) (E

--- 原说明 ---
Consider differentiable maps `v : M → E₁` and `w : M → E₂` to vector bundles, ov
er a base map
`b : M → B`, and bilinear maps `ψ m : E₁ (b m) → E₂ (b m) → E₃ (b m)` depending 
smoothly on `m`.
One can apply `ψ  m` to `v m` and `w m`, and the resulting map is differentiable
.

We give here a version of this statement at a point.
-/
lemma MDifferentiableAt.clm_bundle_apply₂
    (hψ : MDiffAt (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
      (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x →L[𝕜] E₃ x)) (b m) (ψ m)) x)
    (hv : MDiffAt (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) x)
    (hw : MDiffAt (fun m ↦ TotalSpace.mk' F₂ (b m) (w m)) x) :
    MDiffAt (fun m ↦ TotalSpace.mk' F₃ (b m) (ψ m (v m) (w m))) x :=
  MDifferentiableWithinAt.clm_bundle_apply₂ hψ hv hw

/-- Consider differentiable maps `v : M → E₁` and `w : M → E₂` to vector bundles, over a base map
`b : M → B`, and bilinear maps `ψ m : E₁ (b m) → E₂ (b m) → E₃ (b m)` depending smoothly on `m`.
One can apply `ψ  m` to `v m` and `w m`, and the resulting map is differentiable.

We give here a version of this statement on a set. -/
/-
**MDifferentiableOn.clm_bundle_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MDifferentiableOn.clm_bundle_apply (hϕ : MDiff[s] (fun m => TotalSpace.mk'
 (F₁ ->L[𝕜] F₂) (E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `MDifferentiableWithinAt.clm_bundle_apply`：MDifferentiableWithinAt.clm_bu
ndle_apply (hϕ : MDiffAt[s] (fun m => TotalSpace.mk' (F₁ ->L[𝕜] F₂) (E

--- 原说明 ---
Consider differentiable maps `v : M → E₁` and `w : M → E₂` to vector bundles, ov
er a base map
`b : M → B`, and bilinear maps `ψ m : E₁ (b m) → E₂ (b m) → E₃ (b m)` depending 
smoothly on `m`.
One can apply `ψ  m` to `v m` and `w m`, and the resulting map is differentiable
.

We give here a version of this statement on a set.
-/
lemma MDifferentiableOn.clm_bundle_apply₂
    (hψ : MDiff[s] (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
      (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x →L[𝕜] E₃ x)) (b m) (ψ m)))
    (hv : MDiff[s] (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)))
    (hw : MDiff[s] (fun m ↦ TotalSpace.mk' F₂ (b m) (w m))) :
    MDiff[s] (fun m ↦ TotalSpace.mk' F₃ (b m) (ψ m (v m) (w m))) :=
  fun x hx ↦ (hψ x hx).clm_bundle_apply₂ (hv x hx) (hw x hx)

/-- Consider differentiable maps `v : M → E₁` and `w : M → E₂` to vector bundles, over a base map
`b : M → B`, and bilinear maps `ψ m : E₁ (b m) → E₂ (b m) → E₃ (b m)` depending smoothly on `m`.
One can apply `ψ  m` to `v m` and `w m`, and the resulting map is differentiable. -/
/-
**MDifferentiable.clm_bundle_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MDifferentiable.clm_bundle_apply (hϕ : MDiff (fun m => TotalSpace.mk' (F₁ 
->L[𝕜] F₂) (E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `MDifferentiableAt.clm_bundle_apply`：MDifferentiableAt.clm_bundle_apply (
hϕ : MDiffAt (fun m => TotalSpace.mk' (F₁ ->L[𝕜] F₂) (E

--- 原说明 ---
Consider differentiable maps `v : M → E₁` and `w : M → E₂` to vector bundles, ov
er a base map
`b : M → B`, and bilinear maps `ψ m : E₁ (b m) → E₂ (b m) → E₃ (b m)` depending 
smoothly on `m`.
One can apply `ψ  m` to `v m` and `w m`, and the resulting map is differentiable
.
-/
lemma MDifferentiable.clm_bundle_apply₂
    (hψ : MDiff (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
      (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x →L[𝕜] E₃ x)) (b m) (ψ m)))
    (hv : MDiff (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)))
    (hw : MDiff (fun m ↦ TotalSpace.mk' F₂ (b m) (w m))) :
    MDiff (fun m ↦ TotalSpace.mk' F₃ (b m) (ψ m (v m) (w m))) :=
  fun x ↦ (hψ x).clm_bundle_apply₂ (hv x) (hw x)

end TwoVariables'

end

