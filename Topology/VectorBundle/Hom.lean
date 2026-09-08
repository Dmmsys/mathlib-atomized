/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Floris van Doorn
-/
module

public import Mathlib.Topology.VectorBundle.Basic

/-!
# The vector bundle of continuous (semi)linear maps

We define the (topological) vector bundle of continuous (semi)linear maps between two vector bundles
over the same base.

Given bundles `E₁ E₂ : B → Type*`, normed spaces `F₁` and `F₂`, and a ring-homomorphism `σ` between
their respective scalar fields, we define a vector bundle with fiber `E₁ x →SL[σ] E₂ x`.
If the `E₁` and `E₂` are vector bundles with model fibers `F₁` and `F₂`, then this will be a
vector bundle with fiber `F₁ →SL[σ] F₂`.

The topology on the total space is constructed from the trivializations for `E₁` and `E₂` and the
norm-topology on the model fiber `F₁ →SL[𝕜] F₂` using the `VectorPrebundle` construction.  This is
a bit awkward because it introduces a dependence on the normed space structure of the model fibers,
rather than just their topological vector space structure; it is not clear whether this is
necessary.

Similar constructions should be possible (but are yet to be formalized) for tensor products of
topological vector bundles, exterior algebras, and so on, where again the topology can be defined
using a norm on the fiber model if this helps.
-/

@[expose] public section


noncomputable section

open Bundle Set ContinuousLinearMap Topology
open scoped Bundle

variable {𝕜₁ : Type*} [NontriviallyNormedField 𝕜₁] {𝕜₂ : Type*} [NontriviallyNormedField 𝕜₂]
  (σ : 𝕜₁ →+* 𝕜₂)

variable {B : Type*}
variable {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜₁ F₁] (E₁ : B → Type*)
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜₁ (E₁ x)] [TopologicalSpace (TotalSpace F₁ E₁)]

variable {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace 𝕜₂ F₂] (E₂ : B → Type*)
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜₂ (E₂ x)] [TopologicalSpace (TotalSpace F₂ E₂)]

variable {E₁ E₂}
variable [TopologicalSpace B] (e₁ e₁' : Trivialization F₁ (π F₁ E₁))
  (e₂ e₂' : Trivialization F₂ (π F₂ E₂))

namespace Bundle.Pretrivialization

/-- Assume `eᵢ` and `eᵢ'` are trivializations of the bundles `Eᵢ` over base `B` with fiber `Fᵢ`
(`i ∈ {1,2}`), then `Pretrivialization.continuousLinearMapCoordChange σ e₁ e₁' e₂ e₂'` is the
coordinate change function between the two induced (pre)trivializations
`Pretrivialization.continuousLinearMap σ e₁ e₂` and
`Pretrivialization.continuousLinearMap σ e₁' e₂'` of the bundle of continuous linear maps. -/
/-
**Bundle.Pretrivialization.continuousLinearMapCoordChange** 是 Mathlib 中的一个定义，位于命
名空间 `Bundle.Pretrivialization`。
形式化陈述：continuousLinearMapCoordChange [e₁.IsLinear 𝕜₁] [e₁'.IsLinear 𝕜₁] [e₂.IsLi
near 𝕜₂] [e₂'.IsLinear 𝕜₂] (b : B) : (F₁ ->SL[σ] F₂) ->L[𝕜₂] F₁ ->SL[σ] F₂
参数：b : B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Assume `eᵢ` and `eᵢ'` are trivializations of the bundles `Eᵢ` over base `B` with
 fiber `Fᵢ`
(`i ∈ {1,2}`), then `Pretrivialization.continuousLinearMapCoordChange σ e₁ e₁' e
₂ e₂'` is the
coordinate change function between the two induced (pre)trivializations
`Pretrivialization.continuousLinearMap σ e₁ e₂` and
`Pretrivialization.continuousLinearMap σ e₁' e₂'` of the bundle of continuous li
near maps.
-/
def continuousLinearMapCoordChange [e₁.IsLinear 𝕜₁] [e₁'.IsLinear 𝕜₁] [e₂.IsLinear 𝕜₂]
    [e₂'.IsLinear 𝕜₂] (b : B) : (F₁ →SL[σ] F₂) →L[𝕜₂] F₁ →SL[σ] F₂ :=
  ((e₁'.coordChangeL 𝕜₁ e₁ b).symm.arrowCongrSL (e₂.coordChangeL 𝕜₂ e₂' b) :
    (F₁ →SL[σ] F₂) ≃L[𝕜₂] F₁ →SL[σ] F₂)

variable {σ e₁ e₁' e₂ e₂'}
variable [∀ x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁]
variable [∀ x, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂]

set_option backward.defeqAttrib.useBackward true in
/-
**Bundle.Pretrivialization.continuousOn_continuousLinearMapCoordChange** 是 Mathl
ib 中的一个定理，位于命名空间 `Bundle.Pretrivialization`。
形式化陈述：continuousOn_continuousLinearMapCoordChange [RingHomIsometric σ] [VectorBu
ndle 𝕜₁ F₁ E₁] [VectorBundle 𝕜₂ F₂ E₂] [MemTrivializationAtlas e₁] [MemTrivializ
ationAtlas e₁'] [MemTrivializationAtlas e₂] [MemTrivializationAtlas e₂'] : Conti
nuousOn (continuousLinearMapCoordChange σ e₁ e₁' e₂ e₂') (e₁.baseSet inter e₂.ba
seSet inter (e₁'.baseSet inter e₂'.baseSet))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `trivialization_linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → AddCom
mMonoid (E …
· 使用定理 `continuousOn_coordChange`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3}
 {E : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → Add
CommMonoid (E …
· 使用定理 `ContinuousOn.congr`：ContinuousOn.congr (h : ContinuousOn f s) (h' : EqOn
 g f s) : ContinuousOn g s
· 使用定理 `ContinuousOn.clm_comp`：ContinuousOn.clm_comp {g : X -> F ->L[𝕜] G} {f : 
X -> E ->L[𝕜] F} {s : Set X} (hg : ContinuousOn g s) (hf : ContinuousOn f s) : C
ontinuousOn…
· 使用定理 `Continuous.comp_continuousOn`：Continuous.comp_continuousOn {g : β -> γ} 
{f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continuou
sOn (g ∘ f) s
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
-/
theorem continuousOn_continuousLinearMapCoordChange [RingHomIsometric σ]
    [VectorBundle 𝕜₁ F₁ E₁] [VectorBundle 𝕜₂ F₂ E₂]
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₁'] [MemTrivializationAtlas e₂]
    [MemTrivializationAtlas e₂'] :
    ContinuousOn (continuousLinearMapCoordChange σ e₁ e₁' e₂ e₂')
      (e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) := by
  have h₁ := (compSL F₁ F₂ F₂ σ (RingHom.id 𝕜₂)).continuous
  have h₂ := (ContinuousLinearMap.flip (compSL F₁ F₁ F₂ (RingHom.id 𝕜₁) σ)).continuous
  have h₃ := continuousOn_coordChange 𝕜₁ e₁' e₁
  have h₄ := continuousOn_coordChange 𝕜₂ e₂ e₂'
  refine ((h₁.comp_continuousOn (h₄.mono ?_)).clm_comp (h₂.comp_continuousOn (h₃.mono ?_))).congr ?_
  · mfld_set_tac
  · mfld_set_tac
  · intro b _
    ext L v
    dsimp [continuousLinearMapCoordChange]

variable (σ e₁ e₁' e₂ e₂')
variable [e₁.IsLinear 𝕜₁] [e₁'.IsLinear 𝕜₁] [e₂.IsLinear 𝕜₂] [e₂'.IsLinear 𝕜₂]

/-- Given trivializations `e₁`, `e₂` for vector bundles `E₁`, `E₂` over a base `B`,
`Pretrivialization.continuousLinearMap σ e₁ e₂` is the induced pretrivialization for the
continuous `σ`-semilinear maps from `E₁` to `E₂`. That is, the map which will later become a
trivialization, after the bundle of continuous semilinear maps is equipped with the right
topological vector bundle structure. -/
/-
**Bundle.Pretrivialization.continuousLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `Bundle
.Pretrivialization`。
形式化陈述：continuousLinearMap : Pretrivialization (F₁ ->SL[σ] F₂) (π (F₁ ->SL[σ] F₂)
 (fun x => E₁ x ->SL[σ] E₂ x)) where toFun p
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given trivializations `e₁`, `e₂` for vector bundles `E₁`, `E₂` over a base `B`,
`Pretrivialization.continuousLinearMap σ e₁ e₂` is the induced pretrivialization
 for the
continuous `σ`-semilinear maps from `E₁` to `E₂`. That is, the map which will la
ter become a
trivialization, after the bundle of continuous semilinear maps is equipped with 
the right
topological vector bundle structure.
-/
def continuousLinearMap :
    Pretrivialization (F₁ →SL[σ] F₂) (π (F₁ →SL[σ] F₂) (fun x ↦ E₁ x →SL[σ] E₂ x)) where
  toFun p := ⟨p.1, .comp (e₂.continuousLinearMapAt 𝕜₂ p.1) (p.2.comp (e₁.symmL 𝕜₁ p.1))⟩
  invFun p := ⟨p.1, .comp (e₂.symmL 𝕜₂ p.1) (p.2.comp (e₁.continuousLinearMapAt 𝕜₁ p.1))⟩
  source := Bundle.TotalSpace.proj ⁻¹' (e₁.baseSet ∩ e₂.baseSet)
  target := (e₁.baseSet ∩ e₂.baseSet) ×ˢ Set.univ
  map_source' := fun ⟨_, _⟩ h ↦ ⟨h, Set.mem_univ _⟩
  map_target' := fun ⟨_, _⟩ h ↦ h.1
  left_inv' := fun ⟨x, L⟩ ⟨h₁, h₂⟩ ↦ by
    simp only [TotalSpace.mk_inj]
    ext (v : E₁ x)
    dsimp only [comp_apply]
    rw [Trivialization.symmL_continuousLinearMapAt, Trivialization.symmL_continuousLinearMapAt]
    exacts [h₁, h₂]
  right_inv' := fun ⟨x, f⟩ ⟨⟨h₁, h₂⟩, _⟩ ↦ by
    simp only [Prod.mk_right_inj]
    ext v
    dsimp only [comp_apply]
    rw [Trivialization.continuousLinearMapAt_symmL, Trivialization.continuousLinearMapAt_symmL]
    exacts [h₁, h₂]
  open_target := (e₁.open_baseSet.inter e₂.open_baseSet).prod isOpen_univ
  baseSet := e₁.baseSet ∩ e₂.baseSet
  open_baseSet := e₁.open_baseSet.inter e₂.open_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215):
-- TODO: see if Lean 4 can generate this instance without a hint
/-
**Bundle.Pretrivialization.continuousLinearMap.isLinear** 是 Mathlib 中的一个定理，位于命名空
间 `Bundle.Pretrivialization.continuousLinearMap`。
形式化陈述：∀ {𝕜₁ : Type u_1} [inst : NontriviallyNormedField 𝕜₁] {𝕜₂ : Type u_2} [ins
t_1 : NontriviallyNormedField 𝕜₂]   (σ : 𝕜₁ →+* 𝕜₂) {B : Type u_3} {F₁ : Type u_
4} [inst_2 : NormedAddCommGroup F₁] [inst_3 : NormedSpace 𝕜₁ F₁]   {E₁ : B → Typ
e u_5} [inst_4 : (x : B) → AddCommGroup (E₁ x)] [inst_5 : (x : B) → _root_.Modul
e 𝕜₁ (E₁ x)]   [inst_6 : TopologicalSpace (Bundle.TotalSpace F₁ E₁)] {F₂ : Type 
u_6} [inst_7 : NormedAddCommGroup F₂]   [inst_8 : NormedSpace 𝕜₂ F₂] {E₂ : B → T
ype u_7} [inst_9 : (x : B) → AddCommGroup (E₂ x)]   [inst_10 : (x : B) → _root_.
Module 𝕜₂ (E₂ x)] [inst_11 : TopologicalSpace (Bundle.TotalSpace F₂ E₂)]   [inst
_12 : TopologicalSpace B] (e₁ : Bundle.Trivialization F₁ Bundle.TotalSpace.proj)
   (e₂ : Bundle.Trivialization F₂ Bundle.TotalSpace.proj) [inst_13 : (x : B) → T
opologicalSpace (E₁ x)]   [inst_14 : FiberBundle F₁ E₁] [inst_15 : (x : B) → Top
ologicalSpace (E₂ x)] [inst_16 : FiberBundle F₂ E₂]   [inst_17 : Bundle.Triviali
zation.IsLinear 𝕜₁ e₁] [inst_18 : Bundle.Trivialization.IsLinear 𝕜₂ e₂]   [inst_
19 : ∀ (x : B), ContinuousAdd (E₂ x)] [inst_20 : ∀ (x : B), ContinuousSMul 𝕜₂ (E
₂ x)],   Bundle.Pretrivialization.IsLinear 𝕜₂ (Bundle.Pretrivialization.continuo
usLinearMap σ e₁ e₂)
参数：σ : 𝕜₁ →+* 𝕜₂；x : B；E₁ x；x : B；E₁ x；Bundle.TotalSpace F₁ E₁；x : B；E₂ x；x : B；
E₂ x；Bundle.TotalSpace F₂ E₂；e₁ : Bundle.Trivialization F₁ Bundle.TotalSpace.pro
j；e₂ : Bundle.Trivialization F₂ Bundle.TotalSpace.proj；x : B；E₁ x；x : B；E₂ x；x :
 B；E₂ x；x : B；E₂ x；Bundle.Pretrivialization.continuousLinearMap σ e₁ e₂。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用定理 `ContinuousLinearMap.add_comp`：add_comp [ContinuousAdd M₃] (g₁ g₂ : M₂ ->
SL[σ₂₃] M₃) (f : M₁ ->SL[σ₁₂] M₂) : (g₁ + g₂) ∘SL f = g₁ ∘SL f + g₂ ∘SL f
· 使用定理 `ContinuousLinearMap.comp_add`：comp_add [ContinuousAdd M₂] [ContinuousAdd
 M₃] (g : M₂ ->SL[σ₂₃] M₃) (f₁ f₂ : M₁ ->SL[σ₁₂] M₂) : g ∘SL (f₁ + f₂) = g ∘SL f
₁ + g ∘SL f₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ContinuousLinearMap.comp_smulₛₗ`：comp_smulₛₗ [SMulCommClass R₂ R₂ M₂] [S
MulCommClass R₃ R₃ M₃] [ContinuousConstSMul R₂ M₂] [ContinuousConstSMul R₃ M₃] (
h : M₂ ->SL[σ₂₃] M₃) …
-/
instance continuousLinearMap.isLinear [∀ x, ContinuousAdd (E₂ x)] [∀ x, ContinuousSMul 𝕜₂ (E₂ x)] :
    (Pretrivialization.continuousLinearMap σ e₁ e₂).IsLinear 𝕜₂ where
  linear x _ :=
    { map_add L L' := by simp [continuousLinearMap, Pretrivialization.toFun']
      map_smul c L := by simp [continuousLinearMap, Pretrivialization.toFun'] }
/-
**Bundle.Pretrivialization.continuousLinearMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `
Bundle.Pretrivialization`。
形式化陈述：continuousLinearMap_apply (p : TotalSpace (F₁ ->SL[σ] F₂) fun x => E₁ x ->
SL[σ] E₂ x) : (continuousLinearMap σ e₁ e₂) p = ⟨p.1, .comp (e₂.continuousLinear
MapAt 𝕜₂ p.1) (p.2.comp (e₁.symmL 𝕜₁ p.1))⟩
参数：p : TotalSpace (F₁ ->SL[σ] F₂) fun x => E₁ x ->SL[σ] E₂ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem continuousLinearMap_apply (p : TotalSpace (F₁ →SL[σ] F₂) fun x ↦ E₁ x →SL[σ] E₂ x) :
    (continuousLinearMap σ e₁ e₂) p =
      ⟨p.1, .comp (e₂.continuousLinearMapAt 𝕜₂ p.1) (p.2.comp (e₁.symmL 𝕜₁ p.1))⟩ :=
  rfl
/-
**Bundle.Pretrivialization.continuousLinearMap_symm_apply** 是 Mathlib 中的一个定理，位于命
名空间 `Bundle.Pretrivialization`。
形式化陈述：continuousLinearMap_symm_apply (p : B × (F₁ ->SL[σ] F₂)) : (continuousLine
arMap σ e₁ e₂).toPartialEquiv.symm p = ⟨p.1, .comp (e₂.symmL 𝕜₂ p.1) (p.2.comp (
e₁.continuousLinearMapAt 𝕜₁ p.1))⟩
参数：p : B × (F₁ ->SL[σ] F₂)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem continuousLinearMap_symm_apply (p : B × (F₁ →SL[σ] F₂)) :
    (continuousLinearMap σ e₁ e₂).toPartialEquiv.symm p =
      ⟨p.1, .comp (e₂.symmL 𝕜₂ p.1) (p.2.comp (e₁.continuousLinearMapAt 𝕜₁ p.1))⟩ :=
  rfl
/-
**Bundle.Pretrivialization.continuousLinearMap_symm_apply'** 是 Mathlib 中的一个定理，位于
命名空间 `Bundle.Pretrivialization`。
形式化陈述：continuousLinearMap_symm_apply' {b : B} (hb : b in e₁.baseSet inter e₂.bas
eSet) (L : F₁ ->SL[σ] F₂) : (continuousLinearMap σ e₁ e₂).symm b L = (e₂.symmL 𝕜
₂ b).comp (L.comp <| e₁.continuousLinearMapAt 𝕜₁ b)
参数：hb : b in e₁.baseSet inter e₂.baseSet；L : F₁ ->SL[σ] F₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Bundle.Pretrivialization.symm_coe_proj`：symm_coe_proj {x : B} {y : F} (e
' : Pretrivialization F (π F E)) (h : x in e'.baseSet) : (e'.toPartialEquiv.symm
 (x, y)).1 = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Pretrivialization.symm_apply`：symm_apply (e : Pretrivialization F
 (π F E)) {b : B} (hb : b in e.baseSet) (y : F) : e.symm b y = cast (congr_arg E
 (e.symm_coe_proj hb)) (e…
-/
theorem continuousLinearMap_symm_apply' {b : B} (hb : b ∈ e₁.baseSet ∩ e₂.baseSet)
    (L : F₁ →SL[σ] F₂) :
    (continuousLinearMap σ e₁ e₂).symm b L =
      (e₂.symmL 𝕜₂ b).comp (L.comp <| e₁.continuousLinearMapAt 𝕜₁ b) := by
  rw [symm_apply]
  · rfl
  · exact hb
/-
**Bundle.Pretrivialization.continuousLinearMapCoordChange_apply** 是 Mathlib 中的一个
定理，位于命名空间 `Bundle.Pretrivialization`。
形式化陈述：continuousLinearMapCoordChange_apply (b : B) (hb : b in e₁.baseSet inter e
₂.baseSet inter (e₁'.baseSet inter e₂'.baseSet)) (L : F₁ ->SL[σ] F₂) : continuou
sLinearMapCoordChange σ e₁ e₁' e₂ e₂' b L = (continuousLinearMap σ e₁' e₂' ⟨b, (
continuousLinearMap σ e₁ e₂).symm b L⟩).2
参数：b : B；hb : b in e₁.baseSet inter e₂.baseSet inter (e₁'.baseSet inter e₂'.base
Set)；L : F₁ ->SL[σ] F₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
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
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearEquiv.arrowCongrSL_apply`：∀ {𝕜 : Type u_1} {𝕜₂ : Type u_
2} {𝕜₃ : Type u_3} {𝕜₄ : Type u_4} {E : Type u_5} {F : Type u_6} {G : Type u_7} 
  {H : Type u_8} [inst : AddCo…
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用定理 `Bundle.Pretrivialization.continuousLinearMap_symm_apply'`：continuousLine
arMap_symm_apply' {b : B} (hb : b in e₁.baseSet inter e₂.baseSet) (L : F₁ ->SL[σ
] F₂) : (continuousLinearMap σ e₁ e₂).symm b L…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Bundle.Trivialization.continuousLinearMapAt_apply`：∀ (R : Type u_1) {B :
 Type u_2} {F : Type u_3} {E : B → Type u_4} [inst : NontriviallyNormedField R] 
  [inst_1 : (x : B) → AddCommMonoid (E …
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `Bundle.Trivialization.symmL_apply`：∀ {R : Type u_1} {B : Type u_2} {F : 
Type u_3} {E : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x :
 B) → AddCommMonoid (E …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Bundle.Trivialization.coordChangeL_apply`：∀ {R : Type u_1} {B : Type u_2
} {F : Type u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : TopologicalSpa
ce F]   [inst_2 : TopologicalS…
· 使用定理 `Bundle.Trivialization.coe_linearMapAt_of_mem`：∀ {R : Type u_1} {B : Type
 u_2} {F : Type u_3} {E : B → Type u_4} [inst : Semiring R] [inst_1 : Topologica
lSpace F]   [inst_2 : TopologicalS…
-/
theorem continuousLinearMapCoordChange_apply (b : B)
    (hb : b ∈ e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) (L : F₁ →SL[σ] F₂) :
    continuousLinearMapCoordChange σ e₁ e₁' e₂ e₂' b L =
      (continuousLinearMap σ e₁' e₂' ⟨b, (continuousLinearMap σ e₁ e₂).symm b L⟩).2 := by
  ext v
  simp_rw [continuousLinearMapCoordChange, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.arrowCongrSL_apply, continuousLinearMap_apply,
    continuousLinearMap_symm_apply' σ e₁ e₂ hb.1, comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_symm, Trivialization.continuousLinearMapAt_apply]
  rw [e₂.symmL_apply hb.1.2, e₁'.symmL_apply hb.2.1, e₂.coordChangeL_apply e₂',
    e₁'.coordChangeL_apply e₁, e₁.coe_linearMapAt_of_mem hb.1.1, e₂'.coe_linearMapAt_of_mem hb.2.2]
  exacts [⟨hb.2.1, hb.1.1⟩, ⟨hb.1.2, hb.2.2⟩]

end Bundle.Pretrivialization

open Pretrivialization

variable (F₁ E₁ F₂ E₂)
variable [∀ x : B, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁] [VectorBundle 𝕜₁ F₁ E₁]
variable [∀ x : B, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂] [VectorBundle 𝕜₂ F₂ E₂]
variable [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜₂ (E₂ x)]
variable [RingHomIsometric σ]

set_option backward.defeqAttrib.useBackward true in
/-- The continuous `σ`-semilinear maps between two topological vector bundles form a
`VectorPrebundle` (this is an auxiliary construction for the
`VectorBundle` instance, in which the pretrivializations are collated but no topology
on the total space is yet provided). -/
/-
**Bundle.ContinuousLinearMap.vectorPrebundle** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Bundle.ContinuousLinearMap.vectorPrebundle : VectorPrebundle 𝕜₂ (F₁ ->SL[σ
] F₂) (fun x => E₁ x ->SL[σ] E₂ x) where pretrivializationAtlas
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The continuous `σ`-semilinear maps between two topological vector bundles form a
`VectorPrebundle` (this is an auxiliary construction for the
`VectorBundle` instance, in which the pretrivializations are collated but no top
ology
on the total space is yet provided).
-/
def Bundle.ContinuousLinearMap.vectorPrebundle :
    VectorPrebundle 𝕜₂ (F₁ →SL[σ] F₂) (fun x ↦ E₁ x →SL[σ] E₂ x) where
  pretrivializationAtlas :=
    {e | ∃ (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
      (_ : MemTrivializationAtlas e₁) (_ : MemTrivializationAtlas e₂),
        e = Pretrivialization.continuousLinearMap σ e₁ e₂}
  pretrivialization_linear' := by
    rintro _ ⟨e₁, he₁, e₂, he₂, rfl⟩
    infer_instance
  pretrivializationAt x :=
    Pretrivialization.continuousLinearMap σ (trivializationAt F₁ E₁ x) (trivializationAt F₂ E₂ x)
  mem_base_pretrivializationAt x :=
    ⟨mem_baseSet_trivializationAt F₁ E₁ x, mem_baseSet_trivializationAt F₂ E₂ x⟩
  pretrivialization_mem_atlas x :=
    ⟨trivializationAt F₁ E₁ x, trivializationAt F₂ E₂ x, inferInstance, inferInstance, rfl⟩
  exists_coordChange := by
    rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩ _ ⟨e₁', e₂', he₁', he₂', rfl⟩
    exact ⟨continuousLinearMapCoordChange σ e₁ e₁' e₂ e₂',
      continuousOn_continuousLinearMapCoordChange,
      continuousLinearMapCoordChange_apply σ e₁ e₁' e₂ e₂'⟩
  totalSpaceMk_isInducing := by
    intro b
    let L₁ : E₁ b ≃L[𝕜₁] F₁ :=
      (trivializationAt F₁ E₁ b).continuousLinearEquivAt 𝕜₁ b
        (mem_baseSet_trivializationAt _ _ _)
    let L₂ : E₂ b ≃L[𝕜₂] F₂ :=
      (trivializationAt F₂ E₂ b).continuousLinearEquivAt 𝕜₂ b
        (mem_baseSet_trivializationAt _ _ _)
    let φ : (E₁ b →SL[σ] E₂ b) ≃L[𝕜₂] F₁ →SL[σ] F₂ := L₁.arrowCongrSL L₂
    have : IsInducing fun x ↦ (b, φ x) := isInducing_const_prod.mpr φ.toHomeomorph.isInducing
    convert! this
    ext f
    dsimp [Pretrivialization.continuousLinearMap_apply]
    simp only [Trivialization.symmL_apply, mem_baseSet_trivializationAt,
      Trivialization.linearMapAt_def_of_mem]
    rfl

/-- Topology on the total space of the continuous `σ`-semilinear maps between two "normable" vector
bundles over the same base. -/
/-
**Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace** 是 Mathlib 中的一个实例，位于命名空
间 ``。
形式化陈述：Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace : TopologicalSpace (
TotalSpace (F₁ ->SL[σ] F₂) (fun x => E₁ x ->SL[σ] E₂ x))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Topology on the total space of the continuous `σ`-semilinear maps between two "n
ormable" vector
bundles over the same base.
-/
instance Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace :
    TopologicalSpace (TotalSpace (F₁ →SL[σ] F₂) (fun x ↦ E₁ x →SL[σ] E₂ x)) :=
  (Bundle.ContinuousLinearMap.vectorPrebundle σ F₁ E₁ F₂ E₂).totalSpaceTopology

/-- The continuous `σ`-semilinear maps between two vector bundles form a fiber bundle. -/
/-
**Bundle.ContinuousLinearMap.fiberBundle** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Bundle.ContinuousLinearMap.fiberBundle : FiberBundle (F₁ ->SL[σ] F₂) fun x
 => E₁ x ->SL[σ] E₂ x
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The continuous `σ`-semilinear maps between two vector bundles form a fiber bundl
e.
-/
instance Bundle.ContinuousLinearMap.fiberBundle :
    FiberBundle (F₁ →SL[σ] F₂) fun x ↦ E₁ x →SL[σ] E₂ x :=
  (Bundle.ContinuousLinearMap.vectorPrebundle σ F₁ E₁ F₂ E₂).toFiberBundle

/-- The continuous `σ`-semilinear maps between two vector bundles form a vector bundle. -/
/-
**Bundle.ContinuousLinearMap.vectorBundle** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Bundle.ContinuousLinearMap.vectorBundle : VectorBundle 𝕜₂ (F₁ ->SL[σ] F₂) 
(fun x => E₁ x ->SL[σ] E₂ x)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `VectorPrebundle.toVectorBundle`：∀ {R : Type u_1} {B : Type u_2} {F : Typ
e u_3} {E : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B)
 → AddCommMonoid (E …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…

--- 原说明 ---
The continuous `σ`-semilinear maps between two vector bundles form a vector bund
le.
-/
instance Bundle.ContinuousLinearMap.vectorBundle :
    VectorBundle 𝕜₂ (F₁ →SL[σ] F₂) (fun x ↦ E₁ x →SL[σ] E₂ x) :=
  (Bundle.ContinuousLinearMap.vectorPrebundle σ F₁ E₁ F₂ E₂).toVectorBundle

variable [he₁ : MemTrivializationAtlas e₁] [he₂ : MemTrivializationAtlas e₂] {F₁ E₁ F₂ E₂}

/-- Given trivializations `e₁`, `e₂` in the atlas for vector bundles `E₁`, `E₂` over a base `B`,
the induced trivialization for the continuous `σ`-semilinear maps from `E₁` to `E₂`,
whose base set is `e₁.baseSet ∩ e₂.baseSet`. -/
/-
**Bundle.Trivialization.continuousLinearMap** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Bundle.Trivialization.continuousLinearMap : Trivialization (F₁ ->SL[σ] F₂)
 (π (F₁ ->SL[σ] F₂) (fun x => E₁ x ->SL[σ] E₂ x))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given trivializations `e₁`, `e₂` in the atlas for vector bundles `E₁`, `E₂` over
 a base `B`,
the induced trivialization for the continuous `σ`-semilinear maps from `E₁` to `
E₂`,
whose base set is `e₁.baseSet ∩ e₂.baseSet`.
-/
def Bundle.Trivialization.continuousLinearMap :
    Trivialization (F₁ →SL[σ] F₂) (π (F₁ →SL[σ] F₂) (fun x ↦ E₁ x →SL[σ] E₂ x)) :=
  VectorPrebundle.trivializationOfMemPretrivializationAtlas _ ⟨e₁, e₂, he₁, he₂, rfl⟩
/-
**Bundle.ContinuousLinearMap.memTrivializationAtlas** 是 Mathlib 中的一个实例，位于命名空间 ``
。
形式化陈述：Bundle.ContinuousLinearMap.memTrivializationAtlas : MemTrivializationAtlas
 (e₁.continuousLinearMap σ e₂ : Trivialization (F₁ ->SL[σ] F₂) (π (F₁ ->SL[σ] F₂
) (fun x => E₁ x ->SL[σ] E₂ x))) where out
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
instance Bundle.ContinuousLinearMap.memTrivializationAtlas :
    MemTrivializationAtlas
      (e₁.continuousLinearMap σ e₂ :
        Trivialization (F₁ →SL[σ] F₂) (π (F₁ →SL[σ] F₂) (fun x ↦ E₁ x →SL[σ] E₂ x))) where
  out := ⟨_, ⟨e₁, e₂, by infer_instance, by infer_instance, rfl⟩, rfl⟩

variable {e₁ e₂}

@[simp]
/-
**Bundle.Trivialization.baseSet_continuousLinearMap** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：Bundle.Trivialization.baseSet_continuousLinearMap : (e₁.continuousLinearMa
p σ e₂).baseSet = e₁.baseSet inter e₂.baseSet
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem Bundle.Trivialization.baseSet_continuousLinearMap :
    (e₁.continuousLinearMap σ e₂).baseSet = e₁.baseSet ∩ e₂.baseSet :=
  rfl
/-
**Bundle.Trivialization.continuousLinearMap_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Bundle.Trivialization.continuousLinearMap_apply (p : TotalSpace (F₁ ->SL[σ
] F₂) (fun x => E₁ x ->SL[σ] E₂ x)) : e₁.continuousLinearMap σ e₂ p = ⟨p.1, (e₂.
continuousLinearMapAt 𝕜₂ p.1 : _ ->L[𝕜₂] _).comp (p.2.comp (e₁.symmL 𝕜₁ p.1 : F₁
 ->L[𝕜₁] E₁ p.1) : F₁ ->SL[σ] E₂ p.1)⟩
参数：p : TotalSpace (F₁ ->SL[σ] F₂) (fun x => E₁ x ->SL[σ] E₂ x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem Bundle.Trivialization.continuousLinearMap_apply
    (p : TotalSpace (F₁ →SL[σ] F₂) (fun x ↦ E₁ x →SL[σ] E₂ x)) :
    e₁.continuousLinearMap σ e₂ p =
      ⟨p.1, (e₂.continuousLinearMapAt 𝕜₂ p.1 : _ →L[𝕜₂] _).comp
        (p.2.comp (e₁.symmL 𝕜₁ p.1 : F₁ →L[𝕜₁] E₁ p.1) : F₁ →SL[σ] E₂ p.1)⟩ :=
  rfl
/-
**hom_trivializationAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hom_trivializationAt (x₀ : B) : trivializationAt (F₁ ->SL[σ] F₂) (fun x =>
 E₁ x ->SL[σ] E₂ x) x₀ = (trivializationAt F₁ E₁ x₀).continuousLinearMap σ (triv
ializationAt F₂ E₂ x₀)
参数：x₀ : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem hom_trivializationAt (x₀ : B) :
    trivializationAt (F₁ →SL[σ] F₂) (fun x ↦ E₁ x →SL[σ] E₂ x) x₀ =
    (trivializationAt F₁ E₁ x₀).continuousLinearMap σ (trivializationAt F₂ E₂ x₀) := rfl
/-
**hom_trivializationAt_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hom_trivializationAt_apply (x₀ : B) (x : TotalSpace (F₁ ->SL[σ] F₂) (fun x
 => E₁ x ->SL[σ] E₂ x)) : trivializationAt (F₁ ->SL[σ] F₂) (fun x => E₁ x ->SL[σ
] E₂ x) x₀ x = ⟨x.1, inCoordinates F₁ E₁ F₂ E₂ x₀ x.1 x₀ x.1 x.2⟩
参数：x₀ : B；x : TotalSpace (F₁ ->SL[σ] F₂) (fun x => E₁ x ->SL[σ] E₂ x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem hom_trivializationAt_apply (x₀ : B)
    (x : TotalSpace (F₁ →SL[σ] F₂) (fun x ↦ E₁ x →SL[σ] E₂ x)) :
    trivializationAt (F₁ →SL[σ] F₂) (fun x ↦ E₁ x →SL[σ] E₂ x) x₀ x =
      ⟨x.1, inCoordinates F₁ E₁ F₂ E₂ x₀ x.1 x₀ x.1 x.2⟩ :=
  rfl

@[simp, mfld_simps]
/-
**hom_trivializationAt_source** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hom_trivializationAt_source (x₀ : B) : (trivializationAt (F₁ ->SL[σ] F₂) (
fun x => E₁ x ->SL[σ] E₂ x) x₀).source = π (F₁ ->SL[σ] F₂) (fun x => E₁ x ->SL[σ
] E₂ x) ⁻¹' ((trivializationAt F₁ E₁ x₀).baseSet inter (trivializationAt F₂ E₂ x
₀).baseSet)
参数：x₀ : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem hom_trivializationAt_source (x₀ : B) :
    (trivializationAt (F₁ →SL[σ] F₂) (fun x ↦ E₁ x →SL[σ] E₂ x) x₀).source =
      π (F₁ →SL[σ] F₂) (fun x ↦ E₁ x →SL[σ] E₂ x) ⁻¹'
        ((trivializationAt F₁ E₁ x₀).baseSet ∩ (trivializationAt F₂ E₂ x₀).baseSet) :=
  rfl

@[simp, mfld_simps]
/-
**hom_trivializationAt_target** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hom_trivializationAt_target (x₀ : B) : (trivializationAt (F₁ ->SL[σ] F₂) (
fun x => E₁ x ->SL[σ] E₂ x) x₀).target = ((trivializationAt F₁ E₁ x₀).baseSet in
ter (trivializationAt F₂ E₂ x₀).baseSet) ×ˢ Set.univ
参数：x₀ : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem hom_trivializationAt_target (x₀ : B) :
    (trivializationAt (F₁ →SL[σ] F₂) (fun x ↦ E₁ x →SL[σ] E₂ x) x₀).target =
      ((trivializationAt F₁ E₁ x₀).baseSet ∩ (trivializationAt F₂ E₂ x₀).baseSet) ×ˢ Set.univ :=
  rfl

@[simp]
/-
**hom_trivializationAt_baseSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hom_trivializationAt_baseSet (x₀ : B) : (trivializationAt (F₁ ->SL[σ] F₂) 
(fun x => E₁ x ->SL[σ] E₂ x) x₀).baseSet = ((trivializationAt F₁ E₁ x₀).baseSet 
inter (trivializationAt F₂ E₂ x₀).baseSet)
参数：x₀ : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem hom_trivializationAt_baseSet (x₀ : B) :
    (trivializationAt (F₁ →SL[σ] F₂) (fun x ↦ E₁ x →SL[σ] E₂ x) x₀).baseSet =
      ((trivializationAt F₁ E₁ x₀).baseSet ∩ (trivializationAt F₂ E₂ x₀).baseSet) :=
  rfl
/-
**continuousWithinAt_hom_bundle** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousWithinAt_hom_bundle {M : Type*} [TopologicalSpace M] (f : M -> T
otalSpace (F₁ ->SL[σ] F₂) (fun x => E₁ x ->SL[σ] E₂ x)) {s : Set M} {x₀ : M} : C
ontinuousWithinAt f s x₀ ↔ ContinuousWithinAt (fun x => (f x).1) s x₀ ∧ Continuo
usWithinAt (fun x => inCoordinates F₁ E₁ F₂ E₂ (f x₀).1 (f x).1 (f x₀).1 (f x).1
 (f x).2) s x₀
参数：f : M -> TotalSpace (F₁ ->SL[σ] F₂) (fun x => E₁ x ->SL[σ] E₂ x)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiberBundle.continuousWithinAt_totalSpace`：continuousWithinAt_totalSpace
 (f : X -> TotalSpace F E) {s : Set X} {x₀ : X} : ContinuousWithinAt f s x₀ ↔ Co
ntinuousWithinAt (fun x => (f x…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem continuousWithinAt_hom_bundle {M : Type*} [TopologicalSpace M]
    (f : M → TotalSpace (F₁ →SL[σ] F₂) (fun x ↦ E₁ x →SL[σ] E₂ x)) {s : Set M} {x₀ : M} :
    ContinuousWithinAt f s x₀ ↔
      ContinuousWithinAt (fun x ↦ (f x).1) s x₀ ∧
        ContinuousWithinAt
          (fun x ↦ inCoordinates F₁ E₁ F₂ E₂ (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) s x₀ :=
  FiberBundle.continuousWithinAt_totalSpace ..
/-
**continuousAt_hom_bundle** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_hom_bundle {M : Type*} [TopologicalSpace M] (f : M -> TotalSp
ace (F₁ ->SL[σ] F₂) (fun x => E₁ x ->SL[σ] E₂ x)) {x₀ : M} : ContinuousAt f x₀ ↔
 ContinuousAt (fun x => (f x).1) x₀ ∧ ContinuousAt (fun x => inCoordinates F₁ E₁
 F₂ E₂ (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) x₀
参数：f : M -> TotalSpace (F₁ ->SL[σ] F₂) (fun x => E₁ x ->SL[σ] E₂ x)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiberBundle.continuousAt_totalSpace`：continuousAt_totalSpace (f : X -> T
otalSpace F E) {x₀ : X} : ContinuousAt f x₀ ↔ ContinuousAt (fun x => (f x).proj)
 x₀ ∧ ContinuousAt (fun x…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem continuousAt_hom_bundle {M : Type*} [TopologicalSpace M]
    (f : M → TotalSpace (F₁ →SL[σ] F₂) (fun x ↦ E₁ x →SL[σ] E₂ x)) {x₀ : M} :
    ContinuousAt f x₀ ↔
      ContinuousAt (fun x ↦ (f x).1) x₀ ∧
        ContinuousAt
          (fun x ↦ inCoordinates F₁ E₁ F₂ E₂ (f x₀).1 (f x).1 (f x₀).1 (f x).1 (f x).2) x₀ :=
  FiberBundle.continuousAt_totalSpace ..

section

/- Declare two bases spaces `B₁` and `B₂` and two vector bundles `E₁` and `E₂` respectively
over `B₁` and `B₂` (with model fibers `F₁` and `F₂`).

Also a third space `M`, which will be the source of all our maps.
-/
variable {𝕜 F₁ F₂ B₁ B₂ M : Type*} {E₁ : B₁ → Type*} {E₂ : B₂ → Type*} [NontriviallyNormedField 𝕜]
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜 (E₁ x)] [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)] [∀ x, AddCommGroup (E₂ x)]
  [∀ x, Module 𝕜 (E₂ x)] [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  [TopologicalSpace B₁] [TopologicalSpace B₂] [TopologicalSpace M]
  {n : WithTop ℕ∞} [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  {b₁ : M → B₁} {b₂ : M → B₂} {m₀ : M}
  {ϕ : Π (m : M), E₁ (b₁ m) →L[𝕜] E₂ (b₂ m)} {v : Π (m : M), E₁ (b₁ m)} {s : Set M}

/-- Consider a continuous map `v : M → E₁` to a vector bundle, over a base map `b₁ : M → B₁`, and
another basemap `b₂ : M → B₂`. Given linear maps `ϕ m : E₁ (b₁ m) → E₂ (b₂ m)` depending
continuously on `m`, one can apply `ϕ m` to `g m`, and the resulting map is continuous.

Note that the continuity of `ϕ` cannot be always be stated as continuity of a map into a bundle,
as the pullback bundles `b₁ *ᵖ E₁` and `b₂ *ᵖ E₂` only have a nice topology when `b₁` and `b₂` are
globally continuous, but we want to apply this lemma with only local information. Therefore, we
formulate it using continuity of `ϕ` read in coordinates.

Version for `ContinuousWithinAt`. We also give a version for `ContinuousAt`, but no version for
`ContinuousOn` or `Continuous` as our assumption, written in coordinates, only makes sense around
a point.

For a version with `B₁ = B₂` and `b₁ = b₂`, in which continuity can be expressed without
`inCoordinates`, see `ContinuousWithinAt.clm_bundle_apply`
-/
/-
**ContinuousWithinAt.clm_apply_of_inCoordinates** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.clm_apply_of_inCoordinates (hϕ : ContinuousWithinAt (fu
n m => inCoordinates F₁ E₁ F₂ E₂ (b₁ m₀) (b₁ m) (b₂ m₀) (b₂ m) (ϕ m)) s m₀) (hv 
: ContinuousWithinAt (fun m => (v m : TotalSpace F₁ E₁)) s m₀) (hb₂ : Continuous
WithinAt b₂ s m₀) : ContinuousWithinAt (fun m => (ϕ m (v m) : TotalSpace F₂ E₂))
 s m₀
参数：hϕ : ContinuousWithinAt (fun m => inCoordinates F₁ E₁ F₂ E₂ (b₁ m₀) (b₁ m) (b
₂ m₀) (b₂ m) (ϕ m)) s m₀；hv : ContinuousWithinAt (fun m => (v m : TotalSpace F₁ 
E₁)) s m₀；hb₂ : ContinuousWithinAt b₂ s m₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuousWithinAt_insert_self`：continuousWithinAt_insert_self : Continu
ousWithinAt f (insert x s) x ↔ ContinuousWithinAt f s x
· 使用定理 `FiberBundle.continuousWithinAt_totalSpace`：continuousWithinAt_totalSpace
 (f : X -> TotalSpace F E) {s : Set X} {x₀ : X} : ContinuousWithinAt f s x₀ ↔ Co
ntinuousWithinAt (fun x => (f x…
· 使用定理 `ContinuousWithinAt.congr_of_eventuallyEq_of_mem`：ContinuousWithinAt.cong
r_of_eventuallyEq_of_mem (h : ContinuousWithinAt f s x) (h₁ : g =ᶠ[𝓝[s] x] f) (h
x : x in s) : ContinuousWithinAt g s …
· 使用定理 `ContinuousWithinAt.clm_apply`：ContinuousWithinAt.clm_apply {X} [Topologi
calSpace X] {f : X -> E ->L[𝕜] F} {g : X -> E} {s : Set X} {x : X} (hf : Continu
ousWithinAt f s x)…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
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
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `trivialization_linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → AddCom
mMonoid (E …
· 使用定理 `instMemTrivializationAtlasTrivializationAt`：∀ {B : Type u_2} {F : Type u
_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {E : B → Type u_5}
   [inst_2 : TopologicalSpace (B…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousLinearMap.inCoordinates_eq`：∀ {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : (x : B) → AddCommMonoid (E x)]   [inst_1 : NormedAddCom
mGroup F] [inst_2 : Topolo…
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
Consider a continuous map `v : M → E₁` to a vector bundle, over a base map `b₁ :
 M → B₁`, and
another basemap `b₂ : M → B₂`. Given linear maps `ϕ m : E₁ (b₁ m) → E₂ (b₂ m)` d
epending
continuously on `m`, one can apply `ϕ m` to `g m`, and the resulting map is cont
inuous.

Note that the continuity of `ϕ` cannot be always be stated as continuity of a ma
p into a bundle,
as the pullback bundles `b₁ *ᵖ E₁` and `b₂ *ᵖ E₂` only have a nice topology when
 `b₁` and `b₂` are
globally continuous, but we want to apply this lemma with only local information
. Therefore, we
formulate it using continuity of `ϕ` read in coordinates.

Version for `ContinuousWithinAt`. We also give a version for `ContinuousAt`, but
 no version for
`ContinuousOn` or `Continuous` as our assumption, written in coordinates, only m
akes sense around
a point.

For a version with `B₁ = B₂` and `b₁ = b₂`, in which continuity can be expressed
 without
`inCoordinates`, see `ContinuousWithinAt.clm_bundle_apply`
-/
lemma ContinuousWithinAt.clm_apply_of_inCoordinates
    (hϕ : ContinuousWithinAt
      (fun m ↦ inCoordinates F₁ E₁ F₂ E₂ (b₁ m₀) (b₁ m) (b₂ m₀) (b₂ m) (ϕ m)) s m₀)
    (hv : ContinuousWithinAt (fun m ↦ (v m : TotalSpace F₁ E₁)) s m₀)
    (hb₂ : ContinuousWithinAt b₂ s m₀) :
    ContinuousWithinAt (fun m ↦ (ϕ m (v m) : TotalSpace F₂ E₂)) s m₀ := by
  rw [← continuousWithinAt_insert_self] at hϕ hv hb₂ ⊢
  rw [FiberBundle.continuousWithinAt_totalSpace] at hv ⊢
  refine ⟨hb₂, ?_⟩
  apply (ContinuousWithinAt.clm_apply hϕ hv.2).congr_of_eventuallyEq_of_mem ?_ (mem_insert m₀ s)
  have A : ∀ᶠ m in 𝓝[insert m₀ s] m₀, b₁ m ∈ (trivializationAt F₁ E₁ (b₁ m₀)).baseSet := by
    apply hv.1
    apply (trivializationAt F₁ E₁ (b₁ m₀)).open_baseSet.mem_nhds
    exact FiberBundle.mem_baseSet_trivializationAt' (b₁ m₀)
  have A' : ∀ᶠ m in 𝓝[insert m₀ s] m₀, b₂ m ∈ (trivializationAt F₂ E₂ (b₂ m₀)).baseSet := by
    apply hb₂
    apply (trivializationAt F₂ E₂ (b₂ m₀)).open_baseSet.mem_nhds
    exact FiberBundle.mem_baseSet_trivializationAt' (b₂ m₀)
  filter_upwards [A, A'] with m hm h'm using by simp [inCoordinates_eq hm h'm, hm]


/-- Consider a continuous map `v : M → E₁` to a vector bundle, over a base map `b₁ : M → B₁`, and
another basemap `b₂ : M → B₂`. Given linear maps `ϕ m : E₁ (b₁ m) → E₂ (b₂ m)` depending
continuously on `m`, one can apply `ϕ m` to `g m`, and the resulting map is continuous.

Note that the continuity of `ϕ` cannot be always be stated as continuity of a map into a bundle,
as the pullback bundles `b₁ *ᵖ E₁` and `b₂ *ᵖ E₂` only have a nice topology when `b₁` and `b₂` are
globally continuous, but we want to apply this lemma with only local information. Therefore, we
formulate it using continuity of `ϕ` read in coordinates.

Version for `ContinuousAt`. We also give a version for `ContinuousWithinAt`, but no version for
`ContinuousOn` or `Continuous` as our assumption, written in coordinates, only makes sense around
a point.

For a version with `B₁ = B₂` and `b₁ = b₂`, in which continuity can be expressed without
`inCoordinates`, see `ContinuousWithinAt.clm_bundle_apply`
-/
/-
**ContinuousAt.clm_apply_of_inCoordinates** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousAt.clm_apply_of_inCoordinates (hϕ : ContinuousAt (fun m => inCoo
rdinates F₁ E₁ F₂ E₂ (b₁ m₀) (b₁ m) (b₂ m₀) (b₂ m) (ϕ m)) m₀) (hv : ContinuousAt
 (fun m => (v m : TotalSpace F₁ E₁)) m₀) (hb₂ : ContinuousAt b₂ m₀) : Continuous
At (fun m => (ϕ m (v m) : TotalSpace F₂ E₂)) m₀
参数：hϕ : ContinuousAt (fun m => inCoordinates F₁ E₁ F₂ E₂ (b₁ m₀) (b₁ m) (b₂ m₀) 
(b₂ m) (ϕ m)) m₀；hv : ContinuousAt (fun m => (v m : TotalSpace F₁ E₁)) m₀；hb₂ : 
ContinuousAt b₂ m₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `continuousWithinAt_univ`：continuousWithinAt_univ (f : α -> β) (x : α) : 
ContinuousWithinAt f Set.univ x ↔ ContinuousAt f x
· 使用引理 `ContinuousWithinAt.clm_apply_of_inCoordinates`：ContinuousWithinAt.clm_ap
ply_of_inCoordinates (hϕ : ContinuousWithinAt (fun m => inCoordinates F₁ E₁ F₂ E
₂ (b₁ m₀) (b₁ m) (b₂ m₀) (b₂ m) (ϕ …

--- 原说明 ---
Consider a continuous map `v : M → E₁` to a vector bundle, over a base map `b₁ :
 M → B₁`, and
another basemap `b₂ : M → B₂`. Given linear maps `ϕ m : E₁ (b₁ m) → E₂ (b₂ m)` d
epending
continuously on `m`, one can apply `ϕ m` to `g m`, and the resulting map is cont
inuous.

Note that the continuity of `ϕ` cannot be always be stated as continuity of a ma
p into a bundle,
as the pullback bundles `b₁ *ᵖ E₁` and `b₂ *ᵖ E₂` only have a nice topology when
 `b₁` and `b₂` are
globally continuous, but we want to apply this lemma with only local information
. Therefore, we
formulate it using continuity of `ϕ` read in coordinates.

Version for `ContinuousAt`. We also give a version for `ContinuousWithinAt`, but
 no version for
`ContinuousOn` or `Continuous` as our assumption, written in coordinates, only m
akes sense around
a point.

For a version with `B₁ = B₂` and `b₁ = b₂`, in which continuity can be expressed
 without
`inCoordinates`, see `ContinuousWithinAt.clm_bundle_apply`
-/
lemma ContinuousAt.clm_apply_of_inCoordinates
    (hϕ : ContinuousAt
      (fun m ↦ inCoordinates F₁ E₁ F₂ E₂ (b₁ m₀) (b₁ m) (b₂ m₀) (b₂ m) (ϕ m)) m₀)
    (hv : ContinuousAt (fun m ↦ (v m : TotalSpace F₁ E₁)) m₀)
    (hb₂ : ContinuousAt b₂ m₀) :
    ContinuousAt (fun m ↦ (ϕ m (v m) : TotalSpace F₂ E₂)) m₀ := by
  rw [← continuousWithinAt_univ] at hϕ hv hb₂ ⊢
  exact hϕ.clm_apply_of_inCoordinates hv hb₂

end

section

/- Declare a base space `B` and three vector bundles `E₁`, `E₂` and `E₃` over `B`
(with model fibers `F₁`, `F₂` and `F₃`).

Also a second space `M`, which will be the source of all our maps.
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
  [TopologicalSpace B] [TopologicalSpace M]
  [FiberBundle F₁ E₁] [VectorBundle 𝕜 F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle 𝕜 F₂ E₂]
  [FiberBundle F₃ E₃] [VectorBundle 𝕜 F₃ E₃]
  {b : M → B} {v : ∀ x, E₁ (b x)} {s : Set M} {x : M}

section OneVariable

variable [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜 (E₂ x)]
  {ϕ : ∀ x, (E₁ (b x) →L[𝕜] E₂ (b x))}

/-- Consider a `C^n` map `v : M → E₁` to a vector bundle, over a basemap `b : M → B`, and
linear maps `ϕ m : E₁ (b m) → E₂ (b m)` depending smoothly on `m`.
One can apply `ϕ m` to `v m`, and the resulting map is `C^n`. -/
/-
**ContinuousWithinAt.clm_bundle_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.clm_bundle_apply (hϕ : ContinuousWithinAt (fun m => Tot
alSpace.mk' (F₁ ->L[𝕜] F₂) (E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousWithinAt.clm_apply_of_inCoordinates`：ContinuousWithinAt.clm_ap
ply_of_inCoordinates (hϕ : ContinuousWithinAt (fun m => inCoordinates F₁ E₁ F₂ E
₂ (b₁ m₀) (b₁ m) (b₂ m₀) (b₂ m) (ϕ …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
Consider a `C^n` map `v : M → E₁` to a vector bundle, over a basemap `b : M → B`
, and
linear maps `ϕ m : E₁ (b m) → E₂ (b m)` depending smoothly on `m`.
One can apply `ϕ m` to `v m`, and the resulting map is `C^n`.
-/
lemma ContinuousWithinAt.clm_bundle_apply
    (hϕ : ContinuousWithinAt
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ϕ m))
      s x)
    (hv : ContinuousWithinAt (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) s x) :
    ContinuousWithinAt
      (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (v m))) s x := by
  simp only [continuousWithinAt_hom_bundle] at hϕ
  exact hϕ.2.clm_apply_of_inCoordinates hv hϕ.1

/-- Consider a `C^n` map `v : M → E₁` to a vector bundle, over a basemap `b : M → B`, and
linear maps `ϕ m : E₁ (b m) → E₂ (b m)` depending smoothly on `m`.
One can apply `ϕ m` to `v m`, and the resulting map is `C^n`. -/
/-
**ContinuousAt.clm_bundle_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousAt.clm_bundle_apply (hϕ : ContinuousAt (fun m => TotalSpace.mk' 
(F₁ ->L[𝕜] F₂) (E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousWithinAt.clm_bundle_apply`：ContinuousWithinAt.clm_bundle_apply
 (hϕ : ContinuousWithinAt (fun m => TotalSpace.mk' (F₁ ->L[𝕜] F₂) (E

--- 原说明 ---
Consider a `C^n` map `v : M → E₁` to a vector bundle, over a basemap `b : M → B`
, and
linear maps `ϕ m : E₁ (b m) → E₂ (b m)` depending smoothly on `m`.
One can apply `ϕ m` to `v m`, and the resulting map is `C^n`.
-/
lemma ContinuousAt.clm_bundle_apply
    (hϕ : ContinuousAt
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ϕ m)) x)
    (hv : ContinuousAt (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) x) :
    ContinuousAt (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (v m))) x := by
  simp only [← continuousWithinAt_univ] at hϕ hv ⊢
  exact hϕ.clm_bundle_apply hv

/-- Consider a `C^n` map `v : M → E₁` to a vector bundle, over a basemap `b : M → B`, and
linear maps `ϕ m : E₁ (b m) → E₂ (b m)` depending smoothly on `m`.
One can apply `ϕ m` to `v m`, and the resulting map is `C^n`. -/
/-
**ContinuousOn.clm_bundle_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousOn.clm_bundle_apply (hϕ : ContinuousOn (fun m => TotalSpace.mk' 
(F₁ ->L[𝕜] F₂) (E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousWithinAt.clm_bundle_apply`：ContinuousWithinAt.clm_bundle_apply
 (hϕ : ContinuousWithinAt (fun m => TotalSpace.mk' (F₁ ->L[𝕜] F₂) (E

--- 原说明 ---
Consider a `C^n` map `v : M → E₁` to a vector bundle, over a basemap `b : M → B`
, and
linear maps `ϕ m : E₁ (b m) → E₂ (b m)` depending smoothly on `m`.
One can apply `ϕ m` to `v m`, and the resulting map is `C^n`.
-/
lemma ContinuousOn.clm_bundle_apply
    (hϕ : ContinuousOn
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ϕ m)) s)
    (hv : ContinuousOn (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) s) :
    ContinuousOn (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (v m))) s :=
  fun x hx ↦ (hϕ x hx).clm_bundle_apply (hv x hx)

/-- Consider a `C^n` map `v : M → E₁` to a vector bundle, over a basemap `b : M → B`, and
linear maps `ϕ m : E₁ (b m) → E₂ (b m)` depending smoothly on `m`.
One can apply `ϕ m` to `v m`, and the resulting map is `C^n`. -/
/-
**Continuous.clm_bundle_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Continuous.clm_bundle_apply (hϕ : Continuous (fun m => TotalSpace.mk' (F₁ 
->L[𝕜] F₂) (E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousOn.clm_bundle_apply`：ContinuousOn.clm_bundle_apply (hϕ : Conti
nuousOn (fun m => TotalSpace.mk' (F₁ ->L[𝕜] F₂) (E

--- 原说明 ---
Consider a `C^n` map `v : M → E₁` to a vector bundle, over a basemap `b : M → B`
, and
linear maps `ϕ m : E₁ (b m) → E₂ (b m)` depending smoothly on `m`.
One can apply `ϕ m` to `v m`, and the resulting map is `C^n`.
-/
lemma Continuous.clm_bundle_apply
    (hϕ : Continuous
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x)) (b m) (ϕ m)))
    (hv : Continuous (fun m ↦ TotalSpace.mk' F₁ (b m) (v m))) :
    Continuous (fun m ↦ TotalSpace.mk' F₂ (b m) (ϕ m (v m))) := by
  simp only [← continuousOn_univ] at hϕ hv ⊢
  exact hϕ.clm_bundle_apply hv

end OneVariable

section TwoVariables

variable [∀ x, IsTopologicalAddGroup (E₃ x)] [∀ x, ContinuousSMul 𝕜 (E₃ x)]
  {ψ : ∀ x, (E₁ (b x) →L[𝕜] E₂ (b x) →L[𝕜] E₃ (b x))} {w : ∀ x, E₂ (b x)}

/-- Consider `C^n` maps `v : M → E₁` and `v : M → E₂` to vector bundles, over a basemap
`b : M → B`, and bilinear maps `ψ m : E₁ (b m) → E₂ (b m) → E₃ (b m)` depending smoothly on `m`.
One can apply `ψ  m` to `v m` and `w m`, and the resulting map is `C^n`. -/
/-
**ContinuousWithinAt.clm_bundle_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.clm_bundle_apply (hϕ : ContinuousWithinAt (fun m => Tot
alSpace.mk' (F₁ ->L[𝕜] F₂) (E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousWithinAt.clm_apply_of_inCoordinates`：ContinuousWithinAt.clm_ap
ply_of_inCoordinates (hϕ : ContinuousWithinAt (fun m => inCoordinates F₁ E₁ F₂ E
₂ (b₁ m₀) (b₁ m) (b₂ m₀) (b₂ m) (ϕ …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
Consider `C^n` maps `v : M → E₁` and `v : M → E₂` to vector bundles, over a base
map
`b : M → B`, and bilinear maps `ψ m : E₁ (b m) → E₂ (b m) → E₃ (b m)` depending 
smoothly on `m`.
One can apply `ψ  m` to `v m` and `w m`, and the resulting map is `C^n`.
-/
lemma ContinuousWithinAt.clm_bundle_apply₂
    (hψ : ContinuousWithinAt (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
      (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x →L[𝕜] E₃ x)) (b m) (ψ m)) s x)
    (hv : ContinuousWithinAt (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) s x)
    (hw : ContinuousWithinAt (fun m ↦ TotalSpace.mk' F₂ (b m) (w m)) s x) :
    ContinuousWithinAt (fun m ↦ TotalSpace.mk' F₃ (b m) (ψ m (v m) (w m))) s x :=
  (hψ.clm_bundle_apply hv).clm_bundle_apply hw

/-- Consider `C^n` maps `v : M → E₁` and `v : M → E₂` to vector bundles, over a basemap
`b : M → B`, and bilinear maps `ψ m : E₁ (b m) → E₂ (b m) → E₃ (b m)` depending smoothly on `m`.
One can apply `ψ  m` to `v m` and `w m`, and the resulting map is `C^n`. -/
/-
**ContinuousAt.clm_bundle_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousAt.clm_bundle_apply (hϕ : ContinuousAt (fun m => TotalSpace.mk' 
(F₁ ->L[𝕜] F₂) (E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousWithinAt.clm_bundle_apply`：ContinuousWithinAt.clm_bundle_apply
 (hϕ : ContinuousWithinAt (fun m => TotalSpace.mk' (F₁ ->L[𝕜] F₂) (E

--- 原说明 ---
Consider `C^n` maps `v : M → E₁` and `v : M → E₂` to vector bundles, over a base
map
`b : M → B`, and bilinear maps `ψ m : E₁ (b m) → E₂ (b m) → E₃ (b m)` depending 
smoothly on `m`.
One can apply `ψ  m` to `v m` and `w m`, and the resulting map is `C^n`.
-/
lemma ContinuousAt.clm_bundle_apply₂
    (hψ : ContinuousAt (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
      (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x →L[𝕜] E₃ x)) (b m) (ψ m)) x)
    (hv : ContinuousAt (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) x)
    (hw : ContinuousAt (fun m ↦ TotalSpace.mk' F₂ (b m) (w m)) x) :
    ContinuousAt (fun m ↦ TotalSpace.mk' F₃ (b m) (ψ m (v m) (w m))) x :=
  (hψ.clm_bundle_apply hv).clm_bundle_apply hw

/-- Consider `C^n` maps `v : M → E₁` and `v : M → E₂` to vector bundles, over a basemap
`b : M → B`, and bilinear maps `ψ m : E₁ (b m) → E₂ (b m) → E₃ (b m)` depending smoothly on `m`.
One can apply `ψ  m` to `v m` and `w m`, and the resulting map is `C^n`. -/
/-
**ContinuousOn.clm_bundle_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousOn.clm_bundle_apply (hϕ : ContinuousOn (fun m => TotalSpace.mk' 
(F₁ ->L[𝕜] F₂) (E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousWithinAt.clm_bundle_apply`：ContinuousWithinAt.clm_bundle_apply
 (hϕ : ContinuousWithinAt (fun m => TotalSpace.mk' (F₁ ->L[𝕜] F₂) (E

--- 原说明 ---
Consider `C^n` maps `v : M → E₁` and `v : M → E₂` to vector bundles, over a base
map
`b : M → B`, and bilinear maps `ψ m : E₁ (b m) → E₂ (b m) → E₃ (b m)` depending 
smoothly on `m`.
One can apply `ψ  m` to `v m` and `w m`, and the resulting map is `C^n`.
-/
lemma ContinuousOn.clm_bundle_apply₂
    (hψ : ContinuousOn
      (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
      (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x →L[𝕜] E₃ x)) (b m) (ψ m)) s)
    (hv : ContinuousOn (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)) s)
    (hw : ContinuousOn (fun m ↦ TotalSpace.mk' F₂ (b m) (w m)) s) :
    ContinuousOn (fun m ↦ TotalSpace.mk' F₃ (b m) (ψ m (v m) (w m))) s :=
  fun x hx ↦ (hψ x hx).clm_bundle_apply₂ (hv x hx) (hw x hx)

/-- Consider `C^n` maps `v : M → E₁` and `v : M → E₂` to vector bundles, over a basemap
`b : M → B`, and bilinear maps `ψ m : E₁ (b m) → E₂ (b m) → E₃ (b m)` depending smoothly on `m`.
One can apply `ψ  m` to `v m` and `w m`, and the resulting map is `C^n`. -/
/-
**Continuous.clm_bundle_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Continuous.clm_bundle_apply (hϕ : Continuous (fun m => TotalSpace.mk' (F₁ 
->L[𝕜] F₂) (E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousOn.clm_bundle_apply`：ContinuousOn.clm_bundle_apply (hϕ : Conti
nuousOn (fun m => TotalSpace.mk' (F₁ ->L[𝕜] F₂) (E

--- 原说明 ---
Consider `C^n` maps `v : M → E₁` and `v : M → E₂` to vector bundles, over a base
map
`b : M → B`, and bilinear maps `ψ m : E₁ (b m) → E₂ (b m) → E₃ (b m)` depending 
smoothly on `m`.
One can apply `ψ  m` to `v m` and `w m`, and the resulting map is `C^n`.
-/
lemma Continuous.clm_bundle_apply₂
    (hψ : Continuous (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂ →L[𝕜] F₃)
      (E := fun (x : B) ↦ (E₁ x →L[𝕜] E₂ x →L[𝕜] E₃ x)) (b m) (ψ m)))
    (hv : Continuous (fun m ↦ TotalSpace.mk' F₁ (b m) (v m)))
    (hw : Continuous (fun m ↦ TotalSpace.mk' F₂ (b m) (w m))) :
    Continuous (fun m ↦ TotalSpace.mk' F₃ (b m) (ψ m (v m) (w m))) := by
  simp only [← continuousOn_univ] at hψ hv hw ⊢
  exact hψ.clm_bundle_apply₂ hv hw

/-- Rewrite `ContinuousLinearMap.inCoordinates` using continuous linear equivalences, in the
bundle of bilinear maps. -/
/-
**inCoordinates_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Rewrite `ContinuousLinearMap.inCoordinates` using continuous linear equivalences
, in the
bundle of bilinear maps.
-/
theorem inCoordinates_apply_eq₂
    {x₀ x : B} {ϕ : E₁ x →L[𝕜] E₂ x →L[𝕜] E₃ x} {v : F₁} {w : F₂}
    (h₁x : x ∈ (trivializationAt F₁ E₁ x₀).baseSet)
    (h₂x : x ∈ (trivializationAt F₂ E₂ x₀).baseSet)
    (h₃x : x ∈ (trivializationAt F₃ E₃ x₀).baseSet) :
    inCoordinates F₁ E₁ (F₂ →L[𝕜] F₃) (fun x ↦ E₂ x →L[𝕜] E₃ x) x₀ x x₀ x ϕ v w =
    (trivializationAt F₃ E₃ x₀).linearMapAt 𝕜 x
      (ϕ ((trivializationAt F₁ E₁ x₀).symm x v) ((trivializationAt F₂ E₂ x₀).symm x w)) := by
  rw [inCoordinates_eq h₁x (by simp [h₂x, h₃x])]
  simp [hom_trivializationAt, Trivialization.continuousLinearMap_apply, h₂x]

end TwoVariables

end

