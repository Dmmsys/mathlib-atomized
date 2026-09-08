/-
Copyright (c) 2022 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Sébastien Gouëzel, Heather Macbeth, Floris van Doorn
-/
module

public import Mathlib.Topology.FiberBundle.Basic

/-!
# Standard constructions on fiber bundles

This file contains several standard constructions on fiber bundles:

* `Bundle.Trivial.fiberBundle 𝕜 B F`: the trivial fiber bundle with model fiber `F` over the base
  `B`

* `FiberBundle.prod`: for fiber bundles `E₁` and `E₂` over a common base, a fiber bundle structure
  on their fiberwise product `E₁ ×ᵇ E₂` (the notation stands for `fun x ↦ E₁ x × E₂ x`).

* `FiberBundle.pullback`: for a fiber bundle `E` over `B`, a fiber bundle structure on its
  pullback `f *ᵖ E` by a map `f : B' → B` (the notation is a type synonym for `E ∘ f`).

## Tags

fiber bundle, fibre bundle, fiberwise product, pullback

-/

@[expose] public section

open Bundle Filter Set TopologicalSpace Topology

/-! ### The trivial bundle -/

namespace Bundle

namespace Trivial

variable (B : Type*) (F : Type*)

-- TODO: use `TotalSpace.toProd`
/-
**Bundle.Trivial.topologicalSpace** 是 Mathlib 中的一个实例，位于命名空间 `Bundle.Trivial`。
形式化陈述：topologicalSpace [t₁ : TopologicalSpace B] [t₂ : TopologicalSpace F] : Top
ologicalSpace (TotalSpace F (Trivial B F))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance topologicalSpace [t₁ : TopologicalSpace B]
    [t₂ : TopologicalSpace F] : TopologicalSpace (TotalSpace F (Trivial B F)) :=
  induced TotalSpace.proj t₁ ⊓ induced (TotalSpace.trivialSnd B F) t₂

variable [TopologicalSpace B] [TopologicalSpace F]
/-
**Bundle.Trivial.isInducing_toProd** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Trivial`。
形式化陈述：isInducing_toProd : IsInducing (TotalSpace.toProd B F)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `induced_inf`：induced_inf : (t₁ ⊓ t₂).induced g = t₁.induced g ⊓ t₂.induc
ed g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `induced_compose`：induced_compose {tγ : TopologicalSpace γ} {f : α -> β} 
{g : β -> γ} : (tγ.induced g).induced f = tγ.induced (g ∘ f)
-/
theorem isInducing_toProd : IsInducing (TotalSpace.toProd B F) :=
  ⟨by simp only [instTopologicalSpaceProd, induced_inf, induced_compose]; rfl⟩

/-- Homeomorphism between the total space of the trivial bundle and the Cartesian product. -/
@[simps!]
/-
**Bundle.Trivial.homeomorphProd** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Trivial`。
形式化陈述：homeomorphProd : TotalSpace F (Trivial B F) ≃ₜ B × F
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Trivial.isInducing_toProd`：isInducing_toProd : IsInducing (TotalS
pace.toProd B F)

--- 原说明 ---
Homeomorphism between the total space of the trivial bundle and the Cartesian pr
oduct.
-/
def homeomorphProd : TotalSpace F (Trivial B F) ≃ₜ B × F :=
  (TotalSpace.toProd _ _).toHomeomorphOfIsInducing (isInducing_toProd B F)

/-- Local trivialization for trivial bundle. -/
@[simps!]
/-
**Bundle.Trivial.trivialization** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Trivial`。
形式化陈述：trivialization : Trivialization F (π F (Bundle.Trivial B F)) where toOpenP
artialHomeomorph
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ

--- 原说明 ---
Local trivialization for trivial bundle.
-/
def trivialization : Trivialization F (π F (Bundle.Trivial B F)) where
  toOpenPartialHomeomorph := (homeomorphProd B F).toOpenPartialHomeomorph
  baseSet := univ
  open_baseSet := isOpen_univ
  source_eq := rfl
  target_eq := univ_prod_univ.symm
  proj_toFun _ _ := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**Bundle.Trivial.trivialization_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Tri
vial`。
形式化陈述：∀ (B : Type u_1) (F : Type u_2) [inst : TopologicalSpace B] [inst_1 : Topo
logicalSpace F] [inst_2 : Zero F] (b : B)   (f : F), (Bundle.Trivial.trivializat
ion B F).symm b f = f
参数：B : Type u_1；F : Type u_2；b : B；f : F；Bundle.Trivial.trivialization B F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma trivialization_symm_apply [Zero F] (b : B) (f : F) :
    (trivialization B F).symm b f = f := by
  simp [trivialization, homeomorphProd, TotalSpace.toProd, Trivialization.symm,
    Pretrivialization.symm, Trivialization.toPretrivialization]
/-
**Bundle.Trivial.toOpenPartialHomeomorph_trivialization_symm_apply** 是 Mathlib 中
的一个定理，位于命名空间 `Bundle.Trivial`。
形式化陈述：∀ (B : Type u_1) (F : Type u_2) [inst : TopologicalSpace B] [inst_1 : Topo
logicalSpace F] (v : B × F),   ↑(Bundle.Trivial.trivialization B F).symm v = ⟨v.
1, v.2⟩
参数：B : Type u_1；F : Type u_2；v : B × F；Bundle.Trivial.trivialization B F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toOpenPartialHomeomorph_trivialization_symm_apply (v : B × F) :
    (trivialization B F).toOpenPartialHomeomorph.symm v = ⟨v.1, v.2⟩ := rfl

/-- Fiber bundle instance on the trivial bundle. -/
/-
**Bundle.Trivial.fiberBundle** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Trivial`。
形式化陈述：(B : Type u_1) →   (F : Type u_2) → [inst : TopologicalSpace B] → [inst_1 
: TopologicalSpace F] → FiberBundle F (Bundle.Trivial B F)
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α

--- 原说明 ---
Fiber bundle instance on the trivial bundle.
-/
@[simps] instance fiberBundle : FiberBundle F (Bundle.Trivial B F) where
  trivializationAtlas' := {trivialization B F}
  trivializationAt' _ := trivialization B F
  mem_baseSet_trivializationAt' := mem_univ
  trivialization_mem_atlas' _ := mem_singleton _
  totalSpaceMk_isInducing' _ := (homeomorphProd B F).symm.isInducing.comp
    (isInducing_const_prod.2 .id)
/-
**Bundle.Trivial.eq_trivialization** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Trivial`。
形式化陈述：eq_trivialization (e : Trivialization F (π F (Bundle.Trivial B F))) [i : M
emTrivializationAtlas e] : e = trivialization B F
参数：e : Trivialization F (π F (Bundle.Trivial B F))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MemTrivializationAtlas.out`：∀ {B : Type u_2} {F : Type u_3} {inst : Topo
logicalSpace B} {inst_1 : TopologicalSpace F} {E : B → Type u_5}   {inst_2 : Top
ologicalSpace (B…
-/
theorem eq_trivialization (e : Trivialization F (π F (Bundle.Trivial B F)))
    [i : MemTrivializationAtlas e] : e = trivialization B F := i.out

end Trivial

end Bundle

/-! ### Fibrewise product of two bundles -/


section Prod

variable {B : Type*}

section Defs

variable (F₁ : Type*) (E₁ : B → Type*) (F₂ : Type*) (E₂ : B → Type*)
variable [TopologicalSpace (TotalSpace F₁ E₁)] [TopologicalSpace (TotalSpace F₂ E₂)]

/-- Equip the total space of the fiberwise product of two fiber bundles `E₁`, `E₂` with
the induced topology from the diagonal embedding into `TotalSpace F₁ E₁ × TotalSpace F₂ E₂`. -/
/-
**FiberBundle.Prod.topologicalSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：FiberBundle.Prod.topologicalSpace : TopologicalSpace (TotalSpace (F₁ × F₂)
 (E₁ ×ᵇ E₂))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equip the total space of the fiberwise product of two fiber bundles `E₁`, `E₂` w
ith
the induced topology from the diagonal embedding into `TotalSpace F₁ E₁ × TotalS
pace F₂ E₂`.
-/
instance FiberBundle.Prod.topologicalSpace : TopologicalSpace (TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂)) :=
  TopologicalSpace.induced
    (fun p ↦ ((⟨p.1, p.2.1⟩ : TotalSpace F₁ E₁), (⟨p.1, p.2.2⟩ : TotalSpace F₂ E₂)))
    inferInstance

/-- The diagonal map from the total space of the fiberwise product of two fiber bundles
`E₁`, `E₂` into `TotalSpace F₁ E₁ × TotalSpace F₂ E₂` is an inducing map. -/
/-
**FiberBundle.Prod.isInducing_diag** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FiberBundle.Prod.isInducing_diag : IsInducing (fun p => (⟨p.1, p.2.1⟩, ⟨p.
1, p.2.2⟩) : TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂) -> TotalSpace F₁ E₁ × TotalSpace F₂
 E₂)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The diagonal map from the total space of the fiberwise product of two fiber bund
les
`E₁`, `E₂` into `TotalSpace F₁ E₁ × TotalSpace F₂ E₂` is an inducing map.
-/
theorem FiberBundle.Prod.isInducing_diag :
    IsInducing (fun p ↦ (⟨p.1, p.2.1⟩, ⟨p.1, p.2.2⟩) :
      TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂) → TotalSpace F₁ E₁ × TotalSpace F₂ E₂) :=
  ⟨rfl⟩

end Defs

open FiberBundle

variable [TopologicalSpace B] (F₁ : Type*) [TopologicalSpace F₁] (E₁ : B → Type*)
  [TopologicalSpace (TotalSpace F₁ E₁)] (F₂ : Type*) [TopologicalSpace F₂] (E₂ : B → Type*)
  [TopologicalSpace (TotalSpace F₂ E₂)]

namespace Bundle.Trivialization

variable {F₁ E₁ F₂ E₂}
variable (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))

/-- Given trivializations `e₁`, `e₂` for fiber bundles `E₁`, `E₂` over a base `B`, the forward
function for the construction `Trivialization.prod`, the induced
trivialization for the fiberwise product of `E₁` and `E₂`. -/
/-
**Bundle.Trivialization.Prod.toFun'** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Trivializa
tion.Prod`。
形式化陈述：{B : Type u_1} →   [inst : TopologicalSpace B] →     {F₁ : Type u_2} →    
   [inst_1 : TopologicalSpace F₁] →         {E₁ : B → Type u_3} →           [ins
t_2 : TopologicalSpace (Bundle.TotalSpace F₁ E₁)] →             {F₂ : Type u_4} 
→               [inst_3 : TopologicalSpace F₂] →                 {E₂ : B → Type 
u_5} →                   [inst_4 : TopologicalSpace (Bundle.TotalSpace F₂ E₂)] →
                     Bundle.Trivialization F₁ Bundle.TotalSpace.proj →          
             Bundle.Trivialization F₂ Bundle.TotalSpace.proj →                  
       (Bundle.TotalSpace (F₁ × F₂) fun x => E₁ x × E₂ x) → B × F₁ × F₂
参数：Bundle.TotalSpace F₁ E₁；Bundle.TotalSpace F₂ E₂；Bundle.TotalSpace (F₁ × F₂) f
un x => E₁ x × E₂ x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given trivializations `e₁`, `e₂` for fiber bundles `E₁`, `E₂` over a base `B`, t
he forward
function for the construction `Trivialization.prod`, the induced
trivialization for the fiberwise product of `E₁` and `E₂`.
-/
def Prod.toFun' : TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂) → B × F₁ × F₂ :=
  fun p ↦ ⟨p.1, (e₁ ⟨p.1, p.2.1⟩).2, (e₂ ⟨p.1, p.2.2⟩).2⟩

variable {e₁ e₂}
/-
**Bundle.Trivialization.Prod.continuous_to_fun** 是 Mathlib 中的一个定理，位于命名空间 `Bundle
.Trivialization.Prod`。
形式化陈述：∀ {B : Type u_1} [inst : TopologicalSpace B] {F₁ : Type u_2} [inst_1 : Top
ologicalSpace F₁] {E₁ : B → Type u_3}   [inst_2 : TopologicalSpace (Bundle.Total
Space F₁ E₁)] {F₂ : Type u_4} [inst_3 : TopologicalSpace F₂]   {E₂ : B → Type u_
5} [inst_4 : TopologicalSpace (Bundle.TotalSpace F₂ E₂)]   {e₁ : Bundle.Triviali
zation F₁ Bundle.TotalSpace.proj} {e₂ : Bundle.Trivialization F₂ Bundle.TotalSpa
ce.proj},   ContinuousOn (Bundle.Trivialization.Prod.toFun' e₁ e₂) (Bundle.Total
Space.proj ⁻¹' (e₁.baseSet ∩ e₂.baseSet))
参数：Bundle.TotalSpace F₁ E₁；Bundle.TotalSpace F₂ E₂；Bundle.Trivialization.Prod.to
Fun' e₁ e₂；Bundle.TotalSpace.proj ⁻¹' (e₁.baseSet ∩ e₂.baseSet)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X →
 Y} [inst : TopologicalSpace Y] [inst_1 : TopologicalSpace X],   Topology.IsIndu
cing f → Continuous …
· 使用定理 `FiberBundle.Prod.isInducing_diag`：FiberBundle.Prod.isInducing_diag : IsI
nducing (fun p => (⟨p.1, p.2.1⟩, ⟨p.1, p.2.2⟩) : TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂)
 -> TotalSpace F₁ E₁ ×…
· 使用定理 `ContinuousOn.prodMap`：ContinuousOn.prodMap {f : α -> γ} {g : β -> δ} {s 
: Set α} {t : Set β} (hf : ContinuousOn f s) (hg : ContinuousOn g t) : Continuou
sOn (Prod.…
· 使用定理 `OpenPartialHomeomorph.continuousOn`：∀ {X : Type u_1} {Y : Type u_3} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomor
ph X Y), ContinuousOn (↑…
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
· 使用定理 `ContinuousOn.congr`：ContinuousOn.congr (h : ContinuousOn f s) (h' : EqOn
 g f s) : ContinuousOn g s
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
· 使用定理 `Continuous.comp_continuousOn`：Continuous.comp_continuousOn {g : β -> γ} 
{f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continuou
sOn (g ∘ f) s
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bundle.Trivialization.source_eq`：∀ {B : Type u_1} {F : Type u_2} {Z : Ty
pe u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 : To
pologicalSpace Z] {pr…
· 使用定理 `Set.mapsTo_preimage`：mapsTo_preimage (f : α -> β) (t : Set β) : MapsTo f
 (f ⁻¹' t) t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Bundle.Trivialization.coe_fst`：∀ {B : Type u_1} {F : Type u_2} {Z : Type
 u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B}  
 [inst_2 : Topologi…
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
-/
theorem Prod.continuous_to_fun : ContinuousOn (Prod.toFun' e₁ e₂)
    (π (F₁ × F₂) (E₁ ×ᵇ E₂) ⁻¹' (e₁.baseSet ∩ e₂.baseSet)) := by
  let f₁ : TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂) → TotalSpace F₁ E₁ × TotalSpace F₂ E₂ :=
    fun p ↦ ((⟨p.1, p.2.1⟩ : TotalSpace F₁ E₁), (⟨p.1, p.2.2⟩ : TotalSpace F₂ E₂))
  let f₂ : TotalSpace F₁ E₁ × TotalSpace F₂ E₂ → (B × F₁) × B × F₂ := fun p ↦ ⟨e₁ p.1, e₂ p.2⟩
  let f₃ : (B × F₁) × B × F₂ → B × F₁ × F₂ := fun p ↦ ⟨p.1.1, p.1.2, p.2.2⟩
  have hf₁ : Continuous f₁ := (Prod.isInducing_diag F₁ E₁ F₂ E₂).continuous
  have hf₂ : ContinuousOn f₂ (e₁.source ×ˢ e₂.source) :=
    e₁.toOpenPartialHomeomorph.continuousOn.prodMap e₂.toOpenPartialHomeomorph.continuousOn
  have hf₃ : Continuous f₃ := by fun_prop
  refine ((hf₃.comp_continuousOn hf₂).comp hf₁.continuousOn ?_).congr ?_
  · rw [e₁.source_eq, e₂.source_eq]
    exact mapsTo_preimage _ _
  rintro ⟨b, v₁, v₂⟩ ⟨hb₁, _⟩
  simp only [f₁, f₂, f₃, Prod.toFun', Prod.mk_inj, Function.comp_apply, and_true]
  rw [e₁.coe_fst]
  rw [e₁.source_eq, mem_preimage]
  exact hb₁

variable (e₁ e₂) [∀ x, Zero (E₁ x)] [∀ x, Zero (E₂ x)]

/-- Given trivializations `e₁`, `e₂` for fiber bundles `E₁`, `E₂` over a base `B`, the inverse
function for the construction `Trivialization.prod`, the induced
trivialization for the fiberwise product of `E₁` and `E₂`. -/
/-
**Bundle.Trivialization.Prod.invFun'** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Trivializ
ation.Prod`。
形式化陈述：{B : Type u_1} →   [inst : TopologicalSpace B] →     {F₁ : Type u_2} →    
   [inst_1 : TopologicalSpace F₁] →         {E₁ : B → Type u_3} →           [ins
t_2 : TopologicalSpace (Bundle.TotalSpace F₁ E₁)] →             {F₂ : Type u_4} 
→               [inst_3 : TopologicalSpace F₂] →                 {E₂ : B → Type 
u_5} →                   [inst_4 : TopologicalSpace (Bundle.TotalSpace F₂ E₂)] →
                     Bundle.Trivialization F₁ Bundle.TotalSpace.proj →          
             Bundle.Trivialization F₂ Bundle.TotalSpace.proj →                  
       [(x : B) → Zero (E₁ x)] →                           [(x : B) → Zero (E₂ x
)] → B × F₁ × F₂ → Bundle.TotalSpace (F₁ × F₂) fun x => E₁ x × E₂ x
参数：Bundle.TotalSpace F₁ E₁；Bundle.TotalSpace F₂ E₂；x : B；E₁ x；x : B；E₂ x；F₁ × F₂
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given trivializations `e₁`, `e₂` for fiber bundles `E₁`, `E₂` over a base `B`, t
he inverse
function for the construction `Trivialization.prod`, the induced
trivialization for the fiberwise product of `E₁` and `E₂`.
-/
noncomputable def Prod.invFun' (p : B × F₁ × F₂) : TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂) :=
  ⟨p.1, e₁.symm p.1 p.2.1, e₂.symm p.1 p.2.2⟩

variable {e₁ e₂}
/-
**Bundle.Trivialization.Prod.left_inv** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Triviali
zation.Prod`。
形式化陈述：∀ {B : Type u_1} [inst : TopologicalSpace B] {F₁ : Type u_2} [inst_1 : Top
ologicalSpace F₁] {E₁ : B → Type u_3}   [inst_2 : TopologicalSpace (Bundle.Total
Space F₁ E₁)] {F₂ : Type u_4} [inst_3 : TopologicalSpace F₂]   {E₂ : B → Type u_
5} [inst_4 : TopologicalSpace (Bundle.TotalSpace F₂ E₂)]   {e₁ : Bundle.Triviali
zation F₁ Bundle.TotalSpace.proj} {e₂ : Bundle.Trivialization F₂ Bundle.TotalSpa
ce.proj}   [inst_5 : (x : B) → Zero (E₁ x)] [inst_6 : (x : B) → Zero (E₂ x)]   {
x : Bundle.TotalSpace (F₁ × F₂) fun x => E₁ x × E₂ x},   x ∈ Bundle.TotalSpace.p
roj ⁻¹' (e₁.baseSet ∩ e₂.baseSet) →     Bundle.Trivialization.Prod.invFun' e₁ e₂
 (Bundle.Trivialization.Prod.toFun' e₁ e₂ x) = x
参数：Bundle.TotalSpace F₁ E₁；Bundle.TotalSpace F₂ E₂；x : B；E₁ x；x : B；E₂ x；F₁ × F₂
；e₁.baseSet ∩ e₂.baseSet；Bundle.Trivialization.Prod.toFun' e₁ e₂ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Bundle.Trivialization.symm_apply_apply_mk`：∀ {B : Type u_1} {F : Type u_
2} {E : B → Type u_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] 
  [inst_2 : TopologicalSpace (B…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Prod.left_inv {x : TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂)}
    (h : x ∈ π (F₁ × F₂) (E₁ ×ᵇ E₂) ⁻¹' (e₁.baseSet ∩ e₂.baseSet)) :
    Prod.invFun' e₁ e₂ (Prod.toFun' e₁ e₂ x) = x := by
  obtain ⟨x, v₁, v₂⟩ := x
  obtain ⟨h₁ : x ∈ e₁.baseSet, h₂ : x ∈ e₂.baseSet⟩ := h
  simp [Prod.toFun', Prod.invFun', h₁, h₂]
/-
**Bundle.Trivialization.Prod.right_inv** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Trivial
ization.Prod`。
形式化陈述：∀ {B : Type u_1} [inst : TopologicalSpace B] {F₁ : Type u_2} [inst_1 : Top
ologicalSpace F₁] {E₁ : B → Type u_3}   [inst_2 : TopologicalSpace (Bundle.Total
Space F₁ E₁)] {F₂ : Type u_4} [inst_3 : TopologicalSpace F₂]   {E₂ : B → Type u_
5} [inst_4 : TopologicalSpace (Bundle.TotalSpace F₂ E₂)]   {e₁ : Bundle.Triviali
zation F₁ Bundle.TotalSpace.proj} {e₂ : Bundle.Trivialization F₂ Bundle.TotalSpa
ce.proj}   [inst_5 : (x : B) → Zero (E₁ x)] [inst_6 : (x : B) → Zero (E₂ x)] {x 
: B × F₁ × F₂},   x ∈ (e₁.baseSet ∩ e₂.baseSet) ×ˢ Set.univ →     Bundle.Trivial
ization.Prod.toFun' e₁ e₂ (Bundle.Trivialization.Prod.invFun' e₁ e₂ x) = x
参数：Bundle.TotalSpace F₁ E₁；Bundle.TotalSpace F₂ E₂；x : B；E₁ x；x : B；E₂ x；e₁.base
Set ∩ e₂.baseSet；Bundle.Trivialization.Prod.invFun' e₁ e₂ x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Bundle.Trivialization.apply_mk_symm`：∀ {B : Type u_1} {F : Type u_2} {E 
: B → Type u_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [ins
t_2 : TopologicalSpace (B…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Prod.right_inv {x : B × F₁ × F₂}
    (h : x ∈ (e₁.baseSet ∩ e₂.baseSet) ×ˢ (univ : Set (F₁ × F₂))) :
    Prod.toFun' e₁ e₂ (Prod.invFun' e₁ e₂ x) = x := by
  obtain ⟨x, w₁, w₂⟩ := x
  obtain ⟨⟨h₁ : x ∈ e₁.baseSet, h₂ : x ∈ e₂.baseSet⟩, -⟩ := h
  simp [Prod.toFun', Prod.invFun', h₁, h₂]
/-
**Bundle.Trivialization.Prod.continuous_inv_fun** 是 Mathlib 中的一个定理，位于命名空间 `Bundl
e.Trivialization.Prod`。
形式化陈述：∀ {B : Type u_1} [inst : TopologicalSpace B] {F₁ : Type u_2} [inst_1 : Top
ologicalSpace F₁] {E₁ : B → Type u_3}   [inst_2 : TopologicalSpace (Bundle.Total
Space F₁ E₁)] {F₂ : Type u_4} [inst_3 : TopologicalSpace F₂]   {E₂ : B → Type u_
5} [inst_4 : TopologicalSpace (Bundle.TotalSpace F₂ E₂)]   {e₁ : Bundle.Triviali
zation F₁ Bundle.TotalSpace.proj} {e₂ : Bundle.Trivialization F₂ Bundle.TotalSpa
ce.proj}   [inst_5 : (x : B) → Zero (E₁ x)] [inst_6 : (x : B) → Zero (E₂ x)],   
ContinuousOn (Bundle.Trivialization.Prod.invFun' e₁ e₂) ((e₁.baseSet ∩ e₂.baseSe
t) ×ˢ Set.univ)
参数：Bundle.TotalSpace F₁ E₁；Bundle.TotalSpace F₂ E₂；x : B；E₁ x；x : B；E₂ x；Bundle.
Trivialization.Prod.invFun' e₁ e₂；(e₁.baseSet ∩ e₂.baseSet) ×ˢ Set.univ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Topology.IsInducing.continuousOn_iff`：Topology.IsInducing.continuousOn_i
ff {f : α -> β} {g : β -> γ} (hg : IsInducing g) {s : Set α} : ContinuousOn f s 
↔ ContinuousOn (g ∘ f) s
· 使用定理 `FiberBundle.Prod.isInducing_diag`：FiberBundle.Prod.isInducing_diag : IsI
nducing (fun p => (⟨p.1, p.2.1⟩, ⟨p.1, p.2.2⟩) : TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂)
 -> TotalSpace F₁ E₁ ×…
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `ContinuousOn.prodMap`：ContinuousOn.prodMap {f : α -> γ} {g : β -> δ} {s 
: Set α} {t : Set β} (hf : ContinuousOn f s) (hg : ContinuousOn g t) : Continuou
sOn (Prod.…
· 使用定理 `Bundle.Trivialization.continuousOn_symm`：∀ {B : Type u_1} {F : Type u_2}
 {E : B → Type u_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   
[inst_2 : TopologicalSpace (B…
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Prod.continuous_inv_fun :
    ContinuousOn (Prod.invFun' e₁ e₂) ((e₁.baseSet ∩ e₂.baseSet) ×ˢ univ) := by
  rw [(Prod.isInducing_diag F₁ E₁ F₂ E₂).continuousOn_iff]
  have H₁ : Continuous fun p : B × F₁ × F₂ ↦ ((p.1, p.2.1), (p.1, p.2.2)) := by fun_prop
  refine (e₁.continuousOn_symm.prodMap e₂.continuousOn_symm).comp H₁.continuousOn ?_
  exact fun x h ↦ ⟨⟨h.1.1, mem_univ _⟩, ⟨h.1.2, mem_univ _⟩⟩

variable (e₁ e₂)

/-- Given trivializations `e₁`, `e₂` for bundle types `E₁`, `E₂` over a base `B`, the induced
trivialization for the fiberwise product of `E₁` and `E₂`, whose base set is
`e₁.baseSet ∩ e₂.baseSet`. -/
@[simps!]
/-
**Bundle.Trivialization.prod** 是 Mathlib 中的一个定义，位于命名空间 `Bundle.Trivialization`。
形式化陈述：prod : Trivialization (F₁ × F₂) (π (F₁ × F₂) (E₁ ×ᵇ E₂)) where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Trivialization.Prod.left_inv`：∀ {B : Type u_1} [inst : Topologica
lSpace B] {F₁ : Type u_2} [inst_1 : TopologicalSpace F₁] {E₁ : B → Type u_3}   [
inst_2 : TopologicalSpace…
· 使用定理 `Bundle.Trivialization.Prod.right_inv`：∀ {B : Type u_1} [inst : Topologic
alSpace B] {F₁ : Type u_2} [inst_1 : TopologicalSpace F₁] {E₁ : B → Type u_3}   
[inst_2 : TopologicalSpace…
· 使用定理 `Bundle.Trivialization.Prod.continuous_to_fun`：∀ {B : Type u_1} [inst : T
opologicalSpace B] {F₁ : Type u_2} [inst_1 : TopologicalSpace F₁] {E₁ : B → Type
 u_3}   [inst_2 : TopologicalSpace…
· 使用定理 `Bundle.Trivialization.Prod.continuous_inv_fun`：∀ {B : Type u_1} [inst : 
TopologicalSpace B] {F₁ : Type u_2} [inst_1 : TopologicalSpace F₁] {E₁ : B → Typ
e u_3}   [inst_2 : TopologicalSpace…

--- 原说明 ---
Given trivializations `e₁`, `e₂` for bundle types `E₁`, `E₂` over a base `B`, th
e induced
trivialization for the fiberwise product of `E₁` and `E₂`, whose base set is
`e₁.baseSet ∩ e₂.baseSet`.
-/
noncomputable def prod : Trivialization (F₁ × F₂) (π (F₁ × F₂) (E₁ ×ᵇ E₂)) where
  toFun := Prod.toFun' e₁ e₂
  invFun := Prod.invFun' e₁ e₂
  source := π (F₁ × F₂) (E₁ ×ᵇ E₂) ⁻¹' (e₁.baseSet ∩ e₂.baseSet)
  target := (e₁.baseSet ∩ e₂.baseSet) ×ˢ Set.univ
  map_source' _ h := ⟨h, Set.mem_univ _⟩
  map_target' _ h := h.1
  left_inv' _ := Prod.left_inv
  right_inv' _ := Prod.right_inv
  open_source := by
    convert!
      (e₁.open_source.prod e₂.open_source).preimage
        (FiberBundle.Prod.isInducing_diag F₁ E₁ F₂ E₂).continuous
    ext x
    simp only [Trivialization.source_eq, mfld_simps]
  open_target := (e₁.open_baseSet.inter e₂.open_baseSet).prod isOpen_univ
  continuousOn_toFun := Prod.continuous_to_fun
  continuousOn_invFun := Prod.continuous_inv_fun
  baseSet := e₁.baseSet ∩ e₂.baseSet
  open_baseSet := e₁.open_baseSet.inter e₂.open_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl
/-
**Bundle.Trivialization.prod_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Bundle.Trivia
lization`。
形式化陈述：prod_symm_apply (x : B) (w₁ : F₁) (w₂ : F₂) : (prod e₁ e₂).toPartialEquiv.
symm (x, w₁, w₂) = ⟨x, e₁.symm x w₁, e₂.symm x w₂⟩
参数：x : B；w₁ : F₁；w₂ : F₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_symm_apply (x : B) (w₁ : F₁) (w₂ : F₂) :
    (prod e₁ e₂).toPartialEquiv.symm (x, w₁, w₂) = ⟨x, e₁.symm x w₁, e₂.symm x w₂⟩ := rfl

end Bundle.Trivialization

open Bundle Trivialization

variable [∀ x, Zero (E₁ x)] [∀ x, Zero (E₂ x)] [∀ x : B, TopologicalSpace (E₁ x)]
  [∀ x : B, TopologicalSpace (E₂ x)] [FiberBundle F₁ E₁] [FiberBundle F₂ E₂]

/-- The product of two fiber bundles is a fiber bundle. -/
/-
**FiberBundle.prod** 是 Mathlib 中的一个定义，位于命名空间 `FiberBundle`。
形式化陈述：{B : Type u_1} →   [inst : TopologicalSpace B] →     (F₁ : Type u_2) →    
   [inst_1 : TopologicalSpace F₁] →         (E₁ : B → Type u_3) →           [ins
t_2 : TopologicalSpace (Bundle.TotalSpace F₁ E₁)] →             (F₂ : Type u_4) 
→               [inst_3 : TopologicalSpace F₂] →                 (E₂ : B → Type 
u_5) →                   [inst_4 : TopologicalSpace (Bundle.TotalSpace F₂ E₂)] →
                     [(x : B) → Zero (E₁ x)] →                       [(x : B) → 
Zero (E₂ x)] →                         [inst_7 : (x : B) → TopologicalSpace (E₁ 
x)] →                           [inst_8 : (x : B) → TopologicalSpace (E₂ x)] →  
                           [FiberBundle F₁ E₁] → [FiberBundle F₂ E₂] → FiberBund
le (F₁ × F₂) fun x => E₁ x × E₂ x
参数：F₁ : Type u_2；E₁ : B → Type u_3；Bundle.TotalSpace F₁ E₁；F₂ : Type u_4；E₂ : B 
→ Type u_5；Bundle.TotalSpace F₂ E₂；x : B；E₁ x；x : B；E₂ x；x : B；E₁ x；x : B；E₂ x；F
₁ × F₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of two fiber bundles is a fiber bundle.
-/
@[simps] noncomputable instance FiberBundle.prod : FiberBundle (F₁ × F₂) (E₁ ×ᵇ E₂) where
  totalSpaceMk_isInducing' b := by
    rw [← (Prod.isInducing_diag F₁ E₁ F₂ E₂).of_comp_iff]
    exact (totalSpaceMk_isInducing F₁ E₁ b).prodMap (totalSpaceMk_isInducing F₂ E₂ b)
  trivializationAtlas' := { e |
    ∃ (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
      (_ : MemTrivializationAtlas e₁) (_ : MemTrivializationAtlas e₂),
      e = Trivialization.prod e₁ e₂ }
  trivializationAt' b := (trivializationAt F₁ E₁ b).prod (trivializationAt F₂ E₂ b)
  mem_baseSet_trivializationAt' b :=
    ⟨mem_baseSet_trivializationAt F₁ E₁ b, mem_baseSet_trivializationAt F₂ E₂ b⟩
  trivialization_mem_atlas' b :=
    ⟨trivializationAt F₁ E₁ b, trivializationAt F₂ E₂ b, inferInstance, inferInstance, rfl⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {e₁ : Trivialization F₁ (π F₁ E₁)} {e₂ : Trivialization F₂ (π F₂ E₂)}
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₂] :
    MemTrivializationAtlas (e₁.prod e₂ : Trivialization (F₁ × F₂) (π (F₁ × F₂) (E₁ ×ᵇ E₂))) where
  out := ⟨e₁, e₂, inferInstance, inferInstance, rfl⟩

end Prod

/-! ### Pullbacks of fiber bundles -/

open Bundle

section

universe u v w₁ w₂ U

variable {B : Type u} (F : Type v) (E : B → Type w₁) {B' : Type w₂} (f : B' → B)

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ x : B, TopologicalSpace (E x)] : ∀ x : B', TopologicalSpace ((f *ᵖ E) x) :=
  inferInstanceAs (∀ x, TopologicalSpace (E (f x)))

variable [TopologicalSpace B'] [TopologicalSpace (TotalSpace F E)]

-- adding `@[instance_reducible]` causes downstream breakage
set_option warn.classDefReducibility false in
/-- Definition of `Pullback.TotalSpace.topologicalSpace`, which we make irreducible. -/
irreducible_def pullbackTopology : TopologicalSpace (TotalSpace F (f *ᵖ E)) :=
  induced TotalSpace.proj ‹TopologicalSpace B'› ⊓
    induced (Pullback.lift f) ‹TopologicalSpace (TotalSpace F E)›

/-- The topology on the total space of a pullback bundle is the coarsest topology for which both
the projections to the base and the map to the original bundle are continuous. -/
/-
**Pullback.TotalSpace.topologicalSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pullback.TotalSpace.topologicalSpace : TopologicalSpace (TotalSpace F (f *
ᵖ E))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The topology on the total space of a pullback bundle is the coarsest topology fo
r which both
the projections to the base and the map to the original bundle are continuous.
-/
instance Pullback.TotalSpace.topologicalSpace : TopologicalSpace (TotalSpace F (f *ᵖ E)) :=
  pullbackTopology F E f
/-
**Pullback.continuous_proj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Pullback.continuous_proj (f : B' -> B) : Continuous (π F (f *ᵖ E))
参数：f : B' -> B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuous_iff_le_induced`：continuous_iff_le_induced {t₁ : TopologicalSp
ace α} {t₂ : TopologicalSpace β} : Continuous[t₁, t₂] f ↔ t₁ <= induced f t₂
· 使用定理 `Pullback.TotalSpace.topologicalSpace.eq_1`：∀ {B : Type u} (F : Type v) (
E : B → Type w₁) {B' : Type w₂} (f : B' → B) [inst : TopologicalSpace B']   [ins
t_1 : TopologicalSpace (Bundle.…
· 使用定理 `pullbackTopology_def`：∀ {B : Type u_1} (F : Type u_2) (E : B → Type u_3)
 {B' : Type u_4} (f : B' → B) [inst : TopologicalSpace B']   [inst_1 : Topologic
alSpace (B…
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem Pullback.continuous_proj (f : B' → B) : Continuous (π F (f *ᵖ E)) := by
  rw [continuous_iff_le_induced, Pullback.TotalSpace.topologicalSpace, pullbackTopology_def]
  exact inf_le_left
/-
**Pullback.continuous_lift** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Pullback.continuous_lift (f : B' -> B) : Continuous (@Pullback.lift B F E 
B' f)
参数：f : B' -> B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuous_iff_le_induced`：continuous_iff_le_induced {t₁ : TopologicalSp
ace α} {t₂ : TopologicalSpace β} : Continuous[t₁, t₂] f ↔ t₁ <= induced f t₂
· 使用定理 `Pullback.TotalSpace.topologicalSpace.eq_1`：∀ {B : Type u} (F : Type v) (
E : B → Type w₁) {B' : Type w₂} (f : B' → B) [inst : TopologicalSpace B']   [ins
t_1 : TopologicalSpace (Bundle.…
· 使用定理 `pullbackTopology_def`：∀ {B : Type u_1} (F : Type u_2) (E : B → Type u_3)
 {B' : Type u_4} (f : B' → B) [inst : TopologicalSpace B']   [inst_1 : Topologic
alSpace (B…
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
theorem Pullback.continuous_lift (f : B' → B) : Continuous (@Pullback.lift B F E B' f) := by
  rw [continuous_iff_le_induced, Pullback.TotalSpace.topologicalSpace, pullbackTopology_def]
  exact inf_le_right
/-
**inducing_pullbackTotalSpaceEmbedding** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inducing_pullbackTotalSpaceEmbedding (f : B' -> B) : IsInducing (@pullback
TotalSpaceEmbedding B F E B' f)
参数：f : B' -> B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `induced_inf`：induced_inf : (t₁ ⊓ t₂).induced g = t₁.induced g ⊓ t₂.induc
ed g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `induced_compose`：induced_compose {tγ : TopologicalSpace γ} {f : α -> β} 
{g : β -> γ} : (tγ.induced g).induced f = tγ.induced (g ∘ f)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pullbackTopology_def`：∀ {B : Type u_1} (F : Type u_2) (E : B → Type u_3)
 {B' : Type u_4} (f : B' → B) [inst : TopologicalSpace B']   [inst_1 : Topologic
alSpace (B…
-/
theorem inducing_pullbackTotalSpaceEmbedding (f : B' → B) :
    IsInducing (@pullbackTotalSpaceEmbedding B F E B' f) := by
  constructor
  simp_rw [instTopologicalSpaceProd, induced_inf, induced_compose,
    Pullback.TotalSpace.topologicalSpace, pullbackTopology_def]
  rfl

section FiberBundle

variable [TopologicalSpace F] [TopologicalSpace B]

/-
**Pullback.continuous_totalSpaceMk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Pullback.continuous_totalSpaceMk [forall x, TopologicalSpace (E x)] [Fiber
Bundle F E] {f : B' -> B} {x : B'} : Continuous (@TotalSpace.mk _ F (f *ᵖ E) x)
参数：E x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pullbackTopology_def`：∀ {B : Type u_1} (F : Type u_2) (E : B → Type u_3)
 {B' : Type u_4} (f : B' → B) [inst : TopologicalSpace B']   [inst_1 : Topologic
alSpace (B…
· 使用定理 `induced_inf`：induced_inf : (t₁ ⊓ t₂).induced g = t₁.induced g ⊓ t₂.induc
ed g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `induced_compose`：induced_compose {tγ : TopologicalSpace γ} {f : α -> β} 
{g : β -> γ} : (tγ.induced g).induced f = tγ.induced (g ∘ f)
· 使用定理 `induced_const`：induced_const [t : TopologicalSpace α] {x : α} : (t.induc
ed fun _ : β => x) = ⊤
· 使用定理 `top_inf_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderTo
p α] (a : α), ⊤ ⊓ a = a
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Topology.IsInducing.eq_induced`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsInducing f
 → tX = TopologicalS…
· 使用定理 `FiberBundle.totalSpaceMk_isInducing`：totalSpaceMk_isInducing : IsInducin
g (@TotalSpace.mk B F E b)
-/
theorem Pullback.continuous_totalSpaceMk [∀ x, TopologicalSpace (E x)] [FiberBundle F E]
    {f : B' → B} {x : B'} : Continuous (@TotalSpace.mk _ F (f *ᵖ E) x) := by
  simp only [continuous_iff_le_induced, Pullback.TotalSpace.topologicalSpace, induced_compose,
    induced_inf, Function.comp_def, induced_const, top_inf_eq, pullbackTopology_def]
  exact (FiberBundle.totalSpaceMk_isInducing F E (f x)).eq_induced.le

variable {E F}
variable [∀ _b, Nonempty (E _b)] {K : Type U} [FunLike K B' B] [ContinuousMapClass K B' B]

set_option backward.isDefEq.respectTransparency false in
/-- A fiber bundle trivialization can be pulled back to a trivialization on the pullback bundle. -/
@[simps]
/-
**Bundle.Trivialization.pullback** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Bundle.Trivialization.pullback (e : Trivialization F (π F E)) (f : K) : Tr
ivialization F (π F ((f : B' -> B) *ᵖ E)) where toFun z
参数：e : Trivialization F (π F E)；f : K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A fiber bundle trivialization can be pulled back to a trivialization on the pull
back bundle.
-/
noncomputable def Bundle.Trivialization.pullback (e : Trivialization F (π F E)) (f : K) :
    Trivialization F (π F ((f : B' → B) *ᵖ E)) where
  toFun z := (z.proj, (e (Pullback.lift f z)).2)
  invFun y := TotalSpace.mk' F y.1 (e.symm (f y.1) y.2)
  source := Pullback.lift f ⁻¹' e.source
  baseSet := f ⁻¹' e.baseSet
  target := (f ⁻¹' e.baseSet) ×ˢ univ
  map_source' x h := by
    simp_rw [e.source_eq, mem_preimage, Pullback.lift_proj] at h
    simp_rw [prodMk_mem_set_prod_eq, mem_univ, and_true, mem_preimage, h]
  map_target' y h := by
    rw [mem_prod, mem_preimage] at h
    simp_rw [e.source_eq, mem_preimage, Pullback.lift_proj, h.1]
  left_inv' x h := by
    simp_rw [mem_preimage, e.mem_source, Pullback.lift_proj] at h
    simp_rw [Pullback.lift, e.symm_apply_apply_mk h]
  right_inv' x h := by
    simp_rw [mem_prod, mem_preimage, mem_univ, and_true] at h
    simp_rw [Pullback.lift_mk, e.apply_mk_symm h]
  open_source := by
    simp_rw [e.source_eq, ← preimage_comp]
    exact e.open_baseSet.preimage ((map_continuous f).comp <| Pullback.continuous_proj F E f)
  open_target := ((map_continuous f).isOpen_preimage _ e.open_baseSet).prod isOpen_univ
  open_baseSet := (map_continuous f).isOpen_preimage _ e.open_baseSet
  continuousOn_toFun :=
    (Pullback.continuous_proj F E f).continuousOn.prodMk
      (continuous_snd.comp_continuousOn <|
        e.continuousOn.comp (Pullback.continuous_lift F E f).continuousOn Subset.rfl)
  continuousOn_invFun := by
    simp_rw [(inducing_pullbackTotalSpaceEmbedding F E f).continuousOn_iff, Function.comp_def,
      pullbackTotalSpaceEmbedding]
    exact continuousOn_fst.prodMk
      (e.continuousOn_symm.comp ((map_continuous f).prodMap continuous_id).continuousOn Subset.rfl)
  source_eq := by
    rw [e.source_eq]
    rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

@[simps]
/-
**FiberBundle.pullback** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：FiberBundle.pullback [forall x, TopologicalSpace (E x)] [FiberBundle F E] 
(f : K) : FiberBundle F ((f : B' -> B) *ᵖ E) where totalSpaceMk_isInducing' x
参数：E x；f : K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance FiberBundle.pullback [∀ x, TopologicalSpace (E x)] [FiberBundle F E]
    (f : K) : FiberBundle F ((f : B' → B) *ᵖ E) where
  totalSpaceMk_isInducing' x :=
    (totalSpaceMk_isInducing F E (f x)).of_comp (Pullback.continuous_totalSpaceMk F E)
      (Pullback.continuous_lift F E f)
  trivializationAtlas' :=
    { ef | ∃ (e : Trivialization F (π F E)) (_ : MemTrivializationAtlas e), ef = e.pullback f }
  trivializationAt' x := (trivializationAt F E (f x)).pullback f
  mem_baseSet_trivializationAt' x := mem_baseSet_trivializationAt F E (f x)
  trivialization_mem_atlas' x := ⟨trivializationAt F E (f x), inferInstance, rfl⟩

end FiberBundle

end

