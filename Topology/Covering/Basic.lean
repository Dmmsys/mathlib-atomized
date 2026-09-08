/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Topology.DiscreteSubset
public import Mathlib.Topology.FiberBundle.Basic
public import Mathlib.Topology.IsLocalHomeomorph

/-!
# Covering Maps

This file defines covering maps.

## Main definitions

* `IsEvenlyCovered f x I`: A point `x` is evenly covered by `f : E → X` with fiber `I` if `I` is
  discrete and there is a homeomorphism `f ⁻¹' U ≃ₜ U × I` for some open set `U` containing `x`
  with `f ⁻¹' U` open, such that the induced map `f ⁻¹' U → U` coincides with `f`.
* `IsCoveringMap f`: A function `f : E → X` is a covering map if every point `x` is evenly
  covered by `f` with fiber `f ⁻¹' {x}`. The fibers `f ⁻¹' {x}` must be discrete, but if `X` is
  not connected, then the fibers `f ⁻¹' {x}` are not necessarily isomorphic. Also, `f` is not
  assumed to be surjective, so the fibers are even allowed to be empty.
-/

@[expose] public section

open Bundle Topology

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] (f : E → X) (s : Set X)

/-- A point `x : X` is evenly covered by `f : E → X` if `x` has an evenly covered neighborhood.

**Remark**: `DiscreteTopology I ∧ ∃ Trivialization I f, x ∈ t.baseSet` would be a simpler
definition, but unfortunately it does not work if `E` is nonempty but nonetheless `f` has empty
fibers over `s`. If `OpenPartialHomeomorph` could be refactored to work with an empty space and a
nonempty space while preserving the APIs, we could switch back to the definition. -/
/-
**IsEvenlyCovered** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsEvenlyCovered (x : X) (I : Type*) [TopologicalSpace I]
参数：x : X；I : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A point `x : X` is evenly covered by `f : E → X` if `x` has an evenly covered ne
ighborhood.

**Remark**: `DiscreteTopology I ∧ ∃ Trivialization I f, x ∈ t.baseSet` would be 
a simpler
definition, but unfortunately it does not work if `E` is nonempty but nonetheles
s `f` has empty
fibers over `s`. If `OpenPartialHomeomorph` could be refactored to work with an 
empty space and a
nonempty space while preserving the APIs, we could switch back to the definition
.
-/
def IsEvenlyCovered (x : X) (I : Type*) [TopologicalSpace I] :=
  DiscreteTopology I ∧ ∃ U : Set X, x ∈ U ∧ IsOpen U ∧ IsOpen (f ⁻¹' U) ∧
    ∃ H : f ⁻¹' U ≃ₜ U × I, ∀ x, (H x).1.1 = f x

namespace IsEvenlyCovered

variable {f} {I : Type*} [TopologicalSpace I]

/-- If `x : X` is evenly covered by `f` with fiber `I`, then `I` is homeomorphic to `f ⁻¹' {x}`. -/
/-
**IsEvenlyCovered.fiberHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `IsEvenlyCovered`。
形式化陈述：fiberHomeomorph {x : X} (h : IsEvenlyCovered f x I) : I ≃ₜ f ⁻¹' {x}
参数：h : IsEvenlyCovered f x I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `x : X` is evenly covered by `f` with fiber `I`, then `I` is homeomorphic to 
`f ⁻¹' {x}`.
-/
noncomputable def fiberHomeomorph {x : X} (h : IsEvenlyCovered f x I) : I ≃ₜ f ⁻¹' {x} := by
  choose _ U hxU hU hfU H hH using h
  exact
  { toFun i := ⟨H.symm (⟨x, hxU⟩, i), by simp [← hH]⟩
    invFun e := (H ⟨e, by rwa [Set.mem_preimage, (e.2 : f e = x)]⟩).2
    left_inv _ := by simp
    right_inv e := Set.inclusion_injective (Set.preimage_mono (Set.singleton_subset_iff.mpr hxU)) <|
      H.injective <| Prod.ext (Subtype.ext <| by simpa [hH] using e.2.symm) (by simp)
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
/-
**IsEvenlyCovered.discreteTopology_fiber** 是 Mathlib 中的一个定理，位于命名空间 `IsEvenlyCove
red`。
形式化陈述：discreteTopology_fiber {x : X} (h : IsEvenlyCovered f x I) : DiscreteTopol
ogy (f ⁻¹' {x})
参数：h : IsEvenlyCovered f x I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Homeomorph.discreteTopology`：∀ {X : Type u_1} {Y : Type u_2} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y] [DiscreteTopology X]   (h : X ≃ₜ 
Y), DiscreteTopol…
-/
theorem discreteTopology_fiber {x : X} (h : IsEvenlyCovered f x I) : DiscreteTopology (f ⁻¹' {x}) :=
  have := h.1; h.fiberHomeomorph.discreteTopology

/-- If `x` is evenly covered by `f` with nonempty fiber `I`, then we can construct a
trivialization of `f` at `x` with fiber `I`. -/
/-
**IsEvenlyCovered.toTrivialization'** 是 Mathlib 中的一个定义，位于命名空间 `IsEvenlyCovered`。
形式化陈述：toTrivialization' {x : X} [Nonempty I] (h : IsEvenlyCovered f x I) : Trivi
alization I f
参数：h : IsEvenlyCovered f x I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `x` is evenly covered by `f` with nonempty fiber `I`, then we can construct a
trivialization of `f` at `x` with fiber `I`.
-/
noncomputable def toTrivialization' {x : X} [Nonempty I] (h : IsEvenlyCovered f x I) :
    Trivialization I f := by
  choose _ U hxU hU hfU H hH using h
  classical exact
  { toFun e := if he : f e ∈ U then ⟨(H ⟨e, he⟩).1, (H ⟨e, he⟩).2⟩ else ⟨x, Classical.arbitrary I⟩
    invFun xi := H.symm (if hx : xi.1 ∈ U then ⟨xi.1, hx⟩ else ⟨x, hxU⟩, xi.2)
    source := f ⁻¹' U
    target := U ×ˢ Set.univ
    map_source' e (he : f e ∈ U) := by simp [he]
    map_target' _ _ := Subtype.coe_prop _
    left_inv' e (he : f e ∈ U) := by simp [he]
    right_inv' xi := by rintro ⟨hx, -⟩; simpa [hx] using fun h ↦ (h (H.symm _).2).elim
    open_source := hfU
    open_target := hU.prod isOpen_univ
    continuousOn_toFun := continuousOn_iff_continuous_domRestrict.mpr <|
      ((continuous_subtype_val.prodMap continuous_id).comp H.continuous).congr
      fun ⟨e, (he : f e ∈ U)⟩ ↦ by simp [Prod.map, he]
    continuousOn_invFun := continuousOn_iff_continuous_domRestrict.mpr <|
      ((continuous_subtype_val.comp H.symm.continuous).comp (by fun_prop :
        Continuous fun ui ↦ ⟨⟨_, ui.2.1⟩, ui.1.2⟩)).congr fun ⟨⟨x, i⟩, ⟨hx, _⟩⟩ ↦ by simp [hx]
    baseSet := U
    open_baseSet := hU
    source_eq := rfl
    target_eq := rfl
    proj_toFun e (he : f e ∈ U) := by simp [he, hH] }

/-- If `x` is evenly covered by `f`, then we can construct a trivialization of `f` at `x`. -/
/-
**IsEvenlyCovered.toTrivialization** 是 Mathlib 中的一个定义，位于命名空间 `IsEvenlyCovered`。
形式化陈述：toTrivialization {x : X} [Nonempty I] (h : IsEvenlyCovered f x I) : Trivia
lization (f ⁻¹' {x}) f
参数：h : IsEvenlyCovered f x I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `x` is evenly covered by `f`, then we can construct a trivialization of `f` a
t `x`.
-/
noncomputable def toTrivialization {x : X} [Nonempty I] (h : IsEvenlyCovered f x I) :
    Trivialization (f ⁻¹' {x}) f :=
  h.toTrivialization'.transFiberHomeomorph h.fiberHomeomorph
/-
**IsEvenlyCovered.mem_toTrivialization_baseSet** 是 Mathlib 中的一个定理，位于命名空间 `IsEven
lyCovered`。
形式化陈述：mem_toTrivialization_baseSet {x : X} [Nonempty I] (h : IsEvenlyCovered f x
 I) : x in h.toTrivialization.baseSet
参数：h : IsEvenlyCovered f x I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem mem_toTrivialization_baseSet {x : X} [Nonempty I] (h : IsEvenlyCovered f x I) :
    x ∈ h.toTrivialization.baseSet := h.2.choose_spec.1

set_option backward.isDefEq.respectTransparency.types false in
/-
**IsEvenlyCovered.toTrivialization_apply** 是 Mathlib 中的一个定理，位于命名空间 `IsEvenlyCove
red`。
形式化陈述：toTrivialization_apply {x : E} [Nonempty I] (h : IsEvenlyCovered f (f x) I
) : (h.toTrivialization x).2 = ⟨x, rfl⟩
参数：h : IsEvenlyCovered f (f x) I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.injective`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y),   Function.Injective ⇑h
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Classical.choose.congr_simp`：∀ {α : Sort u} {p p_1 : α → Prop} (e_p : p 
= p_1) (h : ∃ x, p x), Classical.choose h = Classical.choose ⋯
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Equiv.mk.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} (toFun toFun_1 : α 
→ β) (e_toFun : toFun = toFun_1) (invFun invFun_1 : β → α)   (e_invFun : invFun 
= invFun_…
· 使用定理 `Homeomorph.mk.congr_simp`：∀ {X : Type u_5} {Y : Type u_6} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (toEquiv toEquiv_1 : X ≃ Y)   (e_toE
quiv : toEquiv…
· 使用定理 `dite.congr_simp`：∀ {α : Sort u} (c : Prop) {h : Decidable c} [h_1 : Deci
dable c] (t t_1 : c → α),   t = t_1 → ∀ (e e_1 : ¬c → α), e = e_1 → dite c t e =
 dite…
· 使用定理 `PartialEquiv.mk.congr_simp`：∀ {α : Type u_5} {β : Type u_6} (toFun toFun
_1 : α → β) (e_toFun : toFun = toFun_1) (invFun invFun_1 : β → α)   (e_invFun : 
invFun = invFun_…
· 使用定理 `PartialHomeomorph.mk.congr_simp`：∀ {X : Type u_7} {Y : Type u_8} [inst :
 TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (toPartialEquiv toPartialEq
uiv_1 : PartialEquiv …
· 使用定理 `OpenPartialHomeomorph.mk.congr_simp`：∀ {X : Type u_7} {Y : Type u_8} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (toPartialHomeomorph to
PartialHomeomorph_1 : Par…
· 使用定理 `Bundle.Trivialization.mk.congr_simp`：∀ {B : Type u_1} {F : Type u_2} {Z 
: Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 
: TopologicalSpace Z] {pr…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `Homeomorph.apply_symm_apply`：apply_symm_apply (h : X ≃ₜ Y) (y : Y) : h (
h.symm y) = y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toTrivialization_apply {x : E} [Nonempty I] (h : IsEvenlyCovered f (f x) I) :
    (h.toTrivialization x).2 = ⟨x, rfl⟩ :=
  h.fiberHomeomorph.symm.injective <| by
    simp [toTrivialization, toTrivialization', dif_pos h.2.choose_spec.1, fiberHomeomorph]
/-
**IsEvenlyCovered.continuousAt** 是 Mathlib 中的一个定理，位于命名空间 `IsEvenlyCovered`。
形式化陈述：∀ {E : Type u_1} {X : Type u_2} [inst : TopologicalSpace E] [inst_1 : Topo
logicalSpace X] {f : E → X} {I : Type u_3}   [inst_2 : TopologicalSpace I] {x : 
E}, IsEvenlyCovered f (f x) I → ContinuousAt f x
参数：f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Trivialization.continuousAt_proj`：∀ {B : Type u_1} {F : Type u_2}
 {Z : Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj 
: Z → B}   [inst_2 : Topologi…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Bundle.Trivialization.mem_source`：∀ {B : Type u_1} {F : Type u_2} {Z : T
ype u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B
}   [inst_2 : Topologi…
· 使用定理 `IsEvenlyCovered.mem_toTrivialization_baseSet`：mem_toTrivialization_baseS
et {x : X} [Nonempty I] (h : IsEvenlyCovered f x I) : x in h.toTrivialization.ba
seSet
-/
protected theorem continuousAt {x : E} (h : IsEvenlyCovered f (f x) I) : ContinuousAt f x :=
  have ⟨_, _, hxU, _, _, H, _⟩ := h
  have : Nonempty I := ⟨(H ⟨x, hxU⟩).2⟩
  let e := h.toTrivialization
  e.continuousAt_proj (e.mem_source.mpr (mem_toTrivialization_baseSet h))
/-
**IsEvenlyCovered.of_fiber_homeomorph** 是 Mathlib 中的一个定理，位于命名空间 `IsEvenlyCovered
`。
形式化陈述：of_fiber_homeomorph {J} [TopologicalSpace J] (g : I ≃ₜ J) {x : X} (h : IsE
venlyCovered f x I) : IsEvenlyCovered f x J
参数：g : I ≃ₜ J；h : IsEvenlyCovered f x I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.discreteTopology`：∀ {X : Type u_1} {Y : Type u_2} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y] [DiscreteTopology X]   (h : X ≃ₜ 
Y), DiscreteTopol…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Homeomorph.refl_apply`：∀ (X : Type u_7) [inst : TopologicalSpace X], ⇑(H
omeomorph.refl X) = id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem of_fiber_homeomorph {J} [TopologicalSpace J] (g : I ≃ₜ J) {x : X}
    (h : IsEvenlyCovered f x I) : IsEvenlyCovered f x J :=
  have ⟨inst, U, hxU, hU, hfU, H, hH⟩ := h
  ⟨g.discreteTopology, U, hxU, hU, hfU, H.trans (.prodCongr (.refl U) g), fun _ ↦ by simp [hH]⟩
/-
**IsEvenlyCovered.to_isEvenlyCovered_preimage** 是 Mathlib 中的一个定理，位于命名空间 `IsEvenl
yCovered`。
形式化陈述：to_isEvenlyCovered_preimage {x : X} (h : IsEvenlyCovered f x I) : IsEvenly
Covered f x (f ⁻¹' {x})
参数：h : IsEvenlyCovered f x I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsEvenlyCovered.of_fiber_homeomorph`：of_fiber_homeomorph {J} [Topologica
lSpace J] (g : I ≃ₜ J) {x : X} (h : IsEvenlyCovered f x I) : IsEvenlyCovered f x
 J
-/
theorem to_isEvenlyCovered_preimage {x : X} (h : IsEvenlyCovered f x I) :
    IsEvenlyCovered f x (f ⁻¹' {x}) :=
  h.of_fiber_homeomorph h.fiberHomeomorph
/-
**IsEvenlyCovered.of_trivialization** 是 Mathlib 中的一个定理，位于命名空间 `IsEvenlyCovered`。
形式化陈述：of_trivialization [DiscreteTopology I] {x : X} {t : Trivialization I f} (h
x : x in t.baseSet) : IsEvenlyCovered f x I
参数：hx : x in t.baseSet。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.Trivialization.open_baseSet`：∀ {B : Type u_1} {F : Type u_2} {Z :
 Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 :
 TopologicalSpace Z] {pr…
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `Bundle.Trivialization.source_eq`：∀ {B : Type u_1} {F : Type u_2} {Z : Ty
pe u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 : To
pologicalSpace Z] {pr…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Bundle.Trivialization.mem_source`：∀ {B : Type u_1} {F : Type u_2} {Z : T
ype u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B
}   [inst_2 : Topologi…
· 使用定理 `Bundle.Trivialization.map_target`：∀ {B : Type u_1} {F : Type u_2} {Z : T
ype u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B
}   [inst_2 : Topologi…
· 使用定理 `Bundle.Trivialization.target_eq`：∀ {B : Type u_1} {F : Type u_2} {Z : Ty
pe u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 : To
pologicalSpace Z] {pr…
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Bundle.Trivialization.symm_apply_mk_proj`：∀ {B : Type u_1} {F : Type u_2
} {Z : Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj
 : Z → B}   [inst_2 : Topologi…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Bundle.Trivialization.proj_symm_apply'`：∀ {B : Type u_1} {F : Type u_2} 
{Z : Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj :
 Z → B}   [inst_2 : Topologi…
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `Bundle.Trivialization.apply_symm_apply'`：∀ {B : Type u_1} {F : Type u_2}
 {Z : Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj 
: Z → B}   [inst_2 : Topologi…
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Topology.IsInducing.continuous_iff`：continuous_iff (hg : IsInducing g) :
 Continuous f ↔ Continuous (g ∘ f)
· 使用引理 `Topology.IsInducing.prodMap`：Topology.IsInducing.prodMap {f : X -> Y} {g
 : Z -> W} (hf : IsInducing f) (hg : IsInducing g) : IsInducing (Prod.map f g)
· 使用引理 `Topology.IsInducing.subtypeVal`：Topology.IsInducing.subtypeVal {t : Set 
Y} : IsInducing ((↑) : t -> Y)
· 使用定理 `Topology.IsInducing.id`：∀ {X : Type u_1} [inst : TopologicalSpace X], To
pology.IsInducing id
· 使用定理 `Continuous.congr`：Continuous.congr {g : X -> Y} (h : Continuous f) (h' :
 forall x, f x = g x) : Continuous g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuousOn_iff_continuous_domRestrict`：continuousOn_iff_continuous_dom
Restrict : ContinuousOn f s ↔ Continuous (s.domRestrict f)
（共 39 条，此处仅展示前 30 条）
-/
theorem of_trivialization [DiscreteTopology I] {x : X} {t : Trivialization I f}
    (hx : x ∈ t.baseSet) : IsEvenlyCovered f x I :=
  ⟨‹_›, _, hx, t.open_baseSet, t.source_eq ▸ t.open_source,
  { toFun e := ⟨⟨f e, e.2⟩, (t e).2⟩
    invFun xi := ⟨t.invFun (xi.1, xi.2), by
      rw [Set.mem_preimage, ← t.mem_source]; exact t.map_target (t.target_eq ▸ ⟨xi.1.2, ⟨⟩⟩)⟩
    left_inv e := Subtype.ext <| t.symm_apply_mk_proj (t.mem_source.mpr e.2)
    right_inv xi := by simp [t.proj_symm_apply', t.apply_symm_apply']
    continuous_toFun := (IsInducing.subtypeVal.prodMap .id).continuous_iff.mpr <|
      (continuousOn_iff_continuous_domRestrict.mp <| t.continuousOn_toFun.mono t.source_eq.ge).congr
      fun e ↦ by simp [t.mk_proj_snd' e.2]
    continuous_invFun := IsInducing.subtypeVal.continuous_iff.mpr <|
      t.continuousOn_invFun.comp_continuous (continuous_subtype_val.prodMap continuous_id)
      fun ⟨x, _⟩ ↦ t.target_eq ▸ ⟨x.2, ⟨⟩⟩ }, fun _ ↦ by simp⟩

variable (I) in
/-
**IsEvenlyCovered.of_preimage_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `IsEvenlyCovere
d`。
形式化陈述：of_preimage_eq_empty [IsEmpty I] {x : X} {U : Set X} (hUx : U in 𝓝 x) (hfU
 : f ⁻¹' U = ∅) : IsEvenlyCovered f x I
参数：hUx : U in 𝓝 x；hfU : f ⁻¹' U = ∅。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
· 使用定理 `Set.eq_empty_of_subset_empty`：eq_empty_of_subset_empty {s : Set α} : s s
ubseteq ∅ -> s = ∅
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.isEmpty_coe_sort`：isEmpty_coe_sort {s : Set α} : IsEmpty (↥s) ↔ s = 
∅
· 使用定理 `Subsingleton.discreteTopology`：∀ {α : Type u} [t : TopologicalSpace α] [
Subsingleton α], DiscreteTopology α
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `isOpen_empty`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen ∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem of_preimage_eq_empty [IsEmpty I] {x : X} {U : Set X} (hUx : U ∈ 𝓝 x) (hfU : f ⁻¹' U = ∅) :
    IsEvenlyCovered f x I :=
  have ⟨V, hVU, hV, hxV⟩ := mem_nhds_iff.mp hUx
  have hfV : f ⁻¹' V = ∅ := Set.eq_empty_of_subset_empty ((Set.preimage_mono hVU).trans hfU.le)
  have := Set.isEmpty_coe_sort.mpr hfV
  ⟨inferInstance, _, hxV, hV, hfV ▸ isOpen_empty, .empty, isEmptyElim⟩

set_option backward.isDefEq.respectTransparency false in
/-
**IsEvenlyCovered.restrictPreimage** 是 Mathlib 中的一个定理，位于命名空间 `IsEvenlyCovered`。
形式化陈述：restrictPreimage {x : X} (hxs : x in s) (h : IsEvenlyCovered f x I) : IsEv
enlyCovered (s.restrictPreimage f) ⟨x, hxs⟩ I
参数：hxs : x in s；h : IsEvenlyCovered f x I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Homeomorph.apply_symm_apply`：apply_symm_apply (h : X ≃ₜ Y) (y : Y) : h (
h.symm y) = y
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `Homeomorph.symm_apply_apply`：symm_apply_apply (h : X ≃ₜ Y) (x : X) : h.s
ymm (h x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `Continuous.subtype_mk`：Continuous.subtype_mk {f : Y -> X} (h : Continuou
s f) (hp : forall x, p (f x)) : Continuous fun x => (⟨f x, hp x⟩ : Subtype p)
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `Homeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), Continuous ⇑h
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem restrictPreimage {x : X} (hxs : x ∈ s) (h : IsEvenlyCovered f x I) :
    IsEvenlyCovered (s.restrictPreimage f) ⟨x, hxs⟩ I :=
  have ⟨inst, U, hxU, hU, hfU, H, hH⟩ := h
  ⟨inst, Subtype.val ⁻¹' U, hxU, hU.preimage (by fun_prop), hfU.preimage continuous_subtype_val,
    { toFun e := (⟨⟨(H ⟨e, e.2⟩).1, hH _ ▸ e.1.2⟩, by simpa only [hH] using! e.2⟩, (H ⟨e, e.2⟩).2)
      invFun x := ⟨⟨H.symm (⟨x.1, x.1.2⟩, x.2), by simp [← hH]⟩, by simp [← hH]⟩
      left_inv _ := by simp, right_inv _ := by simp }, fun _ ↦ by ext; apply hH⟩
/-
**IsEvenlyCovered.subtypeVal_comp** 是 Mathlib 中的一个定理，位于命名空间 `IsEvenlyCovered`。
形式化陈述：subtypeVal_comp (hs : IsOpen s) {x : s} {f : E -> s} (h : IsEvenlyCovered 
f x I) : IsEvenlyCovered (Subtype.val ∘ f) x I
参数：hs : IsOpen s；h : IsEvenlyCovered f x I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `IsOpen.isOpenMap_subtype_val`：IsOpen.isOpenMap_subtype_val {s : Set X} (
hs : IsOpen s) : IsOpenMap ((↑) : s -> X)
· 使用引理 `Topology.IsEmbedding.subtypeVal`：Topology.IsEmbedding.subtypeVal : IsEmb
edding ((↑) : Subtype p -> X)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem subtypeVal_comp (hs : IsOpen s) {x : s} {f : E → s} (h : IsEvenlyCovered f x I) :
    IsEvenlyCovered (Subtype.val ∘ f) x I :=
  have ⟨inst, U, hxU, hU, hfU, H, hH⟩ := h
  have : Subtype.val ∘ f ⁻¹' Subtype.val '' U = f ⁻¹' U := by ext; simp
  ⟨inst, Subtype.val '' U, ⟨x, hxU, rfl⟩, hs.isOpenMap_subtype_val _ hU, by rwa [this], .trans
    (.setCongr this) (H.trans <| .prodCongr (IsEmbedding.subtypeVal.homeomorphImage U) (.refl I)),
    fun _ ↦ congr_arg Subtype.val (hH _)⟩
/-
**IsEvenlyCovered.comp_subtypeVal** 是 Mathlib 中的一个定理，位于命名空间 `IsEvenlyCovered`。
形式化陈述：comp_subtypeVal (hs : IsOpen s) (hfs : IsOpen (f ⁻¹' s)) {x : X} (hx : x i
n s) (h : IsEvenlyCovered (fun e : f ⁻¹' s => f e) x I) : IsEvenlyCovered f x I
参数：hs : IsOpen s；hfs : IsOpen (f ⁻¹' s)；hx : x in s；h : IsEvenlyCovered (fun e :
 f ⁻¹' s => f e) x I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `IsEvenlyCovered.of_preimage_eq_empty`：of_preimage_eq_empty [IsEmpty I] {
x : X} {U : Set X} (hUx : U in 𝓝 x) (hfU : f ⁻¹' U = ∅) : IsEvenlyCovered f x I
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.not_nonempty_iff_eq_empty`：not_nonempty_iff_eq_empty : ¬s.Nonempty ↔
 s = ∅
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Homeomorph.apply_symm_apply`：apply_symm_apply (h : X ≃ₜ Y) (y : Y) : h (
h.symm y) = y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `IsOpen.isOpenMap_subtype_val`：IsOpen.isOpenMap_subtype_val {s : Set X} (
hs : IsOpen s) : IsOpenMap ((↑) : s -> X)
· 使用引理 `Topology.IsEmbedding.subtypeVal`：Topology.IsEmbedding.subtypeVal : IsEmb
edding ((↑) : Subtype p -> X)
· 使用定理 `Homeomorph.symm_apply_eq`：symm_apply_eq (h : X ≃ₜ Y) {x : X} {y : Y} : h
.symm y = x ↔ y = h x
-/
theorem comp_subtypeVal (hs : IsOpen s) (hfs : IsOpen (f ⁻¹' s)) {x : X} (hx : x ∈ s)
    (h : IsEvenlyCovered (fun e : f ⁻¹' s ↦ f e) x I) : IsEvenlyCovered f x I :=
  have ⟨inst, U, hxU, hU, hfU, H, hH⟩ := h
  (isEmpty_or_nonempty I).elim (fun _ ↦ .of_preimage_eq_empty _ ((hs.inter hU).mem_nhds ⟨hx, hxU⟩)
    <| Set.not_nonempty_iff_eq_empty.mp fun ⟨e, he⟩ ↦ isEmptyElim (H ⟨⟨e, he.1⟩, he.2⟩).2) fun _ ↦
  have hUs : U ⊆ s := fun y hy ↦ by
    convert! Set.mem_preimage.mp (H.symm (⟨y, hy⟩, Classical.arbitrary I)).1.2; simp [← hH]
  have : Subtype.val '' (fun e : f ⁻¹' s ↦ f e) ⁻¹' U = f ⁻¹' U := by ext; simpa using @hUs _
  ⟨inst, U, hxU, hU, this ▸ hfs.isOpenMap_subtype_val _ hfU, .trans (.symm <| .trans
    (IsEmbedding.subtypeVal.homeomorphImage _) <| .setCongr this) H, fun x ↦ by
    dsimp; convert! hH ⟨⟨x, hUs x.2⟩, x.2⟩ using 4; rw [Homeomorph.symm_apply_eq]; rfl⟩
/-
**IsEvenlyCovered.comp_homeomorph** 是 Mathlib 中的一个定理，位于命名空间 `IsEvenlyCovered`。
形式化陈述：comp_homeomorph {x : X} (h : IsEvenlyCovered f x I) {E'} [TopologicalSpace
 E'] (g : E' ≃ₜ E) : IsEvenlyCovered (f ∘ g) x I
参数：h : IsEvenlyCovered f x I；g : E' ≃ₜ E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `Homeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), Continuous ⇑h
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_comp`：preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' g ⁻¹'
 s
· 使用定理 `Homeomorph.image_symm`：image_symm (h : X ≃ₜ Y) : image h.symm = preimage
 h
-/
theorem comp_homeomorph {x : X} (h : IsEvenlyCovered f x I) {E'} [TopologicalSpace E']
    (g : E' ≃ₜ E) : IsEvenlyCovered (f ∘ g) x I :=
  have ⟨inst, U, hxU, hU, hfU, H, hH⟩ := h
  ⟨inst, U, hxU, hU, hfU.preimage g.continuous, .trans (.trans
    (.setCongr <| by rw [Set.preimage_comp, g.image_symm]) (g.symm.image _).symm) H, fun _ ↦ hH _⟩
/-
**IsEvenlyCovered.comp_homeomorph_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsEvenlyCovered
`。
形式化陈述：∀ {E : Type u_1} {X : Type u_2} [inst : TopologicalSpace E] [inst_1 : Topo
logicalSpace X] {f : E → X} {I : Type u_3}   [inst_2 : TopologicalSpace I] {x : 
X} {E' : Type u_4} [inst_3 : TopologicalSpace E'] (g : E' ≃ₜ E),   IsEvenlyCover
ed (f ∘ ⇑g) x I ↔ IsEvenlyCovered f x I
参数：g : E' ≃ₜ E；f ∘ ⇑g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Homeomorph.apply_symm_apply`：apply_symm_apply (h : X ≃ₜ Y) (y : Y) : h (
h.symm y) = y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsEvenlyCovered.comp_homeomorph`：comp_homeomorph {x : X} (h : IsEvenlyCo
vered f x I) {E'} [TopologicalSpace E'] (g : E' ≃ₜ E) : IsEvenlyCovered (f ∘ g) 
x I
-/
@[simp] theorem comp_homeomorph_iff {x : X} {E'} [TopologicalSpace E'] (g : E' ≃ₜ E) :
    IsEvenlyCovered (f ∘ g) x I ↔ IsEvenlyCovered f x I where
  mp h := by convert! h.comp_homeomorph g.symm; ext; simp
  mpr h := h.comp_homeomorph g
/-
**IsEvenlyCovered.homeomorph_comp** 是 Mathlib 中的一个定理，位于命名空间 `IsEvenlyCovered`。
形式化陈述：homeomorph_comp {x : X} (h : IsEvenlyCovered f x I) {Y} [TopologicalSpace 
Y] (g : X ≃ₜ Y) : IsEvenlyCovered (g ∘ f) (g x) I
参数：h : IsEvenlyCovered f x I；g : X ≃ₜ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Homeomorph.isOpen_image`：isOpen_image (h : X ≃ₜ Y) {s : Set X} : IsOpen 
(h '' s) ↔ IsOpen s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Homeomorph.preimage_image`：preimage_image (h : X ≃ₜ Y) (s : Set X) : h ⁻
¹' h '' s = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem homeomorph_comp {x : X} (h : IsEvenlyCovered f x I) {Y} [TopologicalSpace Y] (g : X ≃ₜ Y) :
    IsEvenlyCovered (g ∘ f) (g x) I :=
  have ⟨inst, U, hxU, hU, hfU, H, hH⟩ := h
  ⟨inst, g '' U, ⟨x, hxU, rfl⟩, g.isOpen_image.mpr hU, by simpa [Set.preimage_comp],
    .trans (.setCongr <| by simp [Set.preimage_comp]) (H.trans <| (g.image U).prodCongr (.refl I)),
    fun _ ↦ congr_arg g (hH _)⟩
/-
**IsEvenlyCovered.homeomorph_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsEvenlyCovered
`。
形式化陈述：∀ {E : Type u_1} {X : Type u_2} [inst : TopologicalSpace E] [inst_1 : Topo
logicalSpace X] {f : E → X} {I : Type u_3}   [inst_2 : TopologicalSpace I] {x : 
X} {Y : Type u_4} [inst_3 : TopologicalSpace Y] (g : X ≃ₜ Y),   IsEvenlyCovered 
(⇑g ∘ f) (g x) I ↔ IsEvenlyCovered f x I
参数：g : X ≃ₜ Y；⇑g ∘ f；g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Homeomorph.symm_apply_apply`：symm_apply_apply (h : X ≃ₜ Y) (x : X) : h.s
ymm (h x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsEvenlyCovered.homeomorph_comp`：homeomorph_comp {x : X} (h : IsEvenlyCo
vered f x I) {Y} [TopologicalSpace Y] (g : X ≃ₜ Y) : IsEvenlyCovered (g ∘ f) (g 
x) I
-/
@[simp] theorem homeomorph_comp_iff {x : X} {Y} [TopologicalSpace Y] (g : X ≃ₜ Y) :
    IsEvenlyCovered (g ∘ f) (g x) I ↔ IsEvenlyCovered f x I where
  mp h := by convert! h.homeomorph_comp g.symm <;> ((try ext); simp)
  mpr h := h.homeomorph_comp g

end IsEvenlyCovered

/-- A covering map is a continuous function `f : E → X` with discrete fibers such that each point
  of `X` has an evenly covered neighborhood. -/
/-
**IsCoveringMapOn** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsCoveringMapOn
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A covering map is a continuous function `f : E → X` with discrete fibers such th
at each point
  of `X` has an evenly covered neighborhood.
-/
def IsCoveringMapOn :=
  ∀ x ∈ s, IsEvenlyCovered f x (f ⁻¹' {x})

namespace IsCoveringMapOn

/-
**IsCoveringMapOn.of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `IsCoveringMapOn`。
形式化陈述：of_isEmpty [IsEmpty E] : IsCoveringMapOn f s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsEvenlyCovered.to_isEvenlyCovered_preimage`：to_isEvenlyCovered_preimage
 {x : X} (h : IsEvenlyCovered f x I) : IsEvenlyCovered f x (f ⁻¹' {x})
· 使用定理 `IsEvenlyCovered.of_preimage_eq_empty`：of_preimage_eq_empty [IsEmpty I] {
x : X} {U : Set X} (hUx : U in 𝓝 x) (hfU : f ⁻¹' U = ∅) : IsEvenlyCovered f x I
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用引理 `Set.eq_empty_of_isEmpty`：eq_empty_of_isEmpty (s : Set α) [IsEmpty s] : s
 = ∅
· 使用定理 `instIsEmptySubtype`：∀ {α : Sort u} [IsEmpty α] (p : α → Prop), IsEmpty (
Subtype p)
-/
theorem of_isEmpty [IsEmpty E] : IsCoveringMapOn f s := fun _ _ ↦ .to_isEvenlyCovered_preimage
  (.of_preimage_eq_empty Empty Filter.univ_mem <| Set.eq_empty_of_isEmpty _)

/-- A constructor for `IsCoveringMapOn` when there are both empty and nonempty fibers. -/
/-
**IsCoveringMapOn.mk'** 是 Mathlib 中的一个定理，位于命名空间 `IsCoveringMapOn`。
形式化陈述：mk' (F : s -> Type*) [forall x : s, TopologicalSpace (F x)] [hF : forall x
 : s, DiscreteTopology (F x)] (t : forall x : s, x.1 in Set.range f -> {t : Triv
ialization (F x) f // x.1 in t.baseSet}) (h : forall x : s, x.1 ∉ Set.range f ->
 exists U in 𝓝 x.1, f ⁻¹' U = ∅) : IsCoveringMapOn f s
参数：F : s -> Type*；F x；F x；t : forall x : s, x.1 in Set.range f -> {t : Trivializ
ation (F x) f // x.1 in t.baseSet}；h : forall x : s, x.1 ∉ Set.range f -> exists
 U in 𝓝 x.1, f ⁻¹' U = ∅。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `IsEvenlyCovered.to_isEvenlyCovered_preimage`：to_isEvenlyCovered_preimage
 {x : X} (h : IsEvenlyCovered f x I) : IsEvenlyCovered f x (f ⁻¹' {x})
· 使用定理 `IsEvenlyCovered.of_trivialization`：of_trivialization [DiscreteTopology I
] {x : X} {t : Trivialization I f} (hx : x in t.baseSet) : IsEvenlyCovered f x I
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `IsEvenlyCovered.of_preimage_eq_empty`：of_preimage_eq_empty [IsEmpty I] {
x : X} {U : Set X} (hUx : U in 𝓝 x) (hfU : f ⁻¹' U = ∅) : IsEvenlyCovered f x I

--- 原说明 ---
A constructor for `IsCoveringMapOn` when there are both empty and nonempty fiber
s.
-/
theorem mk' (F : s → Type*) [∀ x : s, TopologicalSpace (F x)] [hF : ∀ x : s, DiscreteTopology (F x)]
    (t : ∀ x : s, x.1 ∈ Set.range f → {t : Trivialization (F x) f // x.1 ∈ t.baseSet})
    (h : ∀ x : s, x.1 ∉ Set.range f → ∃ U ∈ 𝓝 x.1, f ⁻¹' U = ∅) :
    IsCoveringMapOn f s := fun x hx ↦ by
  lift x to s using hx
  by_cases hxf : x.1 ∈ Set.range f
  · exact .to_isEvenlyCovered_preimage (.of_trivialization (t x hxf).2)
  · have ⟨U, hUx, hfU⟩ := h x hxf
    exact .to_isEvenlyCovered_preimage (.of_preimage_eq_empty Empty hUx hfU)
/-
**IsCoveringMapOn.mk** 是 Mathlib 中的一个定理，位于命名空间 `IsCoveringMapOn`。
形式化陈述：mk (F : s -> Type*) [forall x, TopologicalSpace (F x)] [hF : forall x, Dis
creteTopology (F x)] (e : forall x, Trivialization (F x) f) (h : forall x, x.1 i
n (e x).baseSet) : IsCoveringMapOn f s
参数：F : s -> Type*；F x；F x；e : forall x, Trivialization (F x) f；h : forall x, x.1
 in (e x).baseSet。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `IsCoveringMapOn.of_isEmpty`：of_isEmpty [IsEmpty E] : IsCoveringMapOn f s
· 使用定理 `IsCoveringMapOn.mk'`：mk' (F : s -> Type*) [forall x : s, TopologicalSpac
e (F x)] [hF : forall x : s, DiscreteTopology (F x)] (t : forall x : s, x.1 in S
et.range …
· 使用定理 `Bundle.Trivialization.proj_symm_apply'`：∀ {B : Type u_1} {F : Type u_2} 
{Z : Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj :
 Z → B}   [inst_2 : Topologi…
-/
theorem mk (F : s → Type*) [∀ x, TopologicalSpace (F x)] [hF : ∀ x, DiscreteTopology (F x)]
    (e : ∀ x, Trivialization (F x) f) (h : ∀ x, x.1 ∈ (e x).baseSet) :
    IsCoveringMapOn f s := by
  cases isEmpty_or_nonempty E
  · exact .of_isEmpty _ _
  refine .mk' _ _ _ (fun x _ ↦ ⟨e x, h x⟩) fun x hx ↦ (hx ?_).elim
  exact ⟨(e x).invFun (x, (e x <| Classical.arbitrary E).2), (e x).proj_symm_apply' (h x)⟩

variable {f s}
/-
**IsCoveringMapOn.mono** 是 Mathlib 中的一个定理，位于命名空间 `IsCoveringMapOn`。
形式化陈述：mono {t : Set X} (hf : IsCoveringMapOn f s) (ht : t subseteq s) : IsCoveri
ngMapOn f t
参数：hf : IsCoveringMapOn f s；ht : t subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mono {t : Set X} (hf : IsCoveringMapOn f s) (ht : t ⊆ s) : IsCoveringMapOn f t :=
  fun x hx ↦ hf x (ht hx)
/-
**IsCoveringMapOn.continuousAt** 是 Mathlib 中的一个定理，位于命名空间 `IsCoveringMapOn`。
形式化陈述：∀ {E : Type u_1} {X : Type u_2} [inst : TopologicalSpace E] [inst_1 : Topo
logicalSpace X] {f : E → X} {s : Set X},   IsCoveringMapOn f s → ∀ {x : E}, f x 
∈ s → ContinuousAt f x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsEvenlyCovered.continuousAt`：∀ {E : Type u_1} {X : Type u_2} [inst : To
pologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X} {I : Type u_3}   [in
st_2 : Topological…
-/
protected theorem continuousAt (hf : IsCoveringMapOn f s) {x : E} (hx : f x ∈ s) :
    ContinuousAt f x := (hf (f x) hx).continuousAt
/-
**IsCoveringMapOn.continuousOn** 是 Mathlib 中的一个定理，位于命名空间 `IsCoveringMapOn`。
形式化陈述：∀ {E : Type u_1} {X : Type u_2} [inst : TopologicalSpace E] [inst_1 : Topo
logicalSpace X] {f : E → X} {s : Set X},   IsCoveringMapOn f s → ContinuousOn f 
(f ⁻¹' s)
参数：f ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousOn_of_forall_continuousAt`：continuousOn_of_forall_continuousAt
 (hcont : forall x in s, ContinuousAt f x) : ContinuousOn f s
· 使用定理 `IsCoveringMapOn.continuousAt`：∀ {E : Type u_1} {X : Type u_2} [inst : To
pologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X} {s : Set X},   IsCov
eringMapOn f s → ∀…
-/
protected theorem continuousOn (hf : IsCoveringMapOn f s) : ContinuousOn f (f ⁻¹' s) :=
  continuousOn_of_forall_continuousAt fun _ ↦ hf.continuousAt
/-
**IsCoveringMapOn.isLocalHomeomorphOn** 是 Mathlib 中的一个定理，位于命名空间 `IsCoveringMapOn
`。
形式化陈述：∀ {E : Type u_1} {X : Type u_2} [inst : TopologicalSpace E] [inst_1 : Topo
logicalSpace X] {f : E → X} {s : Set X},   IsCoveringMapOn f s → IsLocalHomeomor
phOn f (f ⁻¹' s)
参数：f ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalHomeomorphOn.mk`：mk (h : forall x in s, exists e : OpenPartialHom
eomorph X Y, x in e.source ∧ Set.EqOn f e e.source) : IsLocalHomeomorphOn f s
· 使用定理 `IsEvenlyCovered.mem_toTrivialization_baseSet`：mem_toTrivialization_baseS
et {x : X} [Nonempty I] (h : IsEvenlyCovered f x I) : x in h.toTrivialization.ba
seSet
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Bundle.Trivialization.mem_source`：∀ {B : Type u_1} {F : Type u_2} {Z : T
ype u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B
}   [inst_2 : Topologi…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `continuousOn_fst`：continuousOn_fst {s : Set (α × β)} : ContinuousOn Prod
.fst s
· 使用定理 `ContinuousOn.prodMk`：ContinuousOn.prodMk {f : α -> β} {g : α -> γ} {s : 
Set α} (hf : ContinuousOn f s) (hg : ContinuousOn g s) : ContinuousOn (fun x => 
(f x, g x…
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
· 使用定理 `IsOpen.prod`：IsOpen.prod {s : Set X} {t : Set Y} (hs : IsOpen s) (ht : I
sOpen t) : IsOpen (s ×ˢ t)
· 使用定理 `Bundle.Trivialization.open_baseSet`：∀ {B : Type u_1} {F : Type u_2} {Z :
 Type u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 :
 TopologicalSpace Z] {pr…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `discreteTopology_iff_isOpen_singleton`：discreteTopology_iff_isOpen_singl
eton [TopologicalSpace α] : DiscreteTopology α ↔ (forall a : α, IsOpen ({a} : Se
t α))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.symm_symm`：∀ {X : Type u_1} {Y : Type u_3} [inst :
 TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorph 
X Y), e.symm.symm = e
· 使用定理 `Bundle.Trivialization.proj_toFun`：∀ {B : Type u_1} {F : Type u_2} {Z : T
ype u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 : T
opologicalSpace Z] {pr…
· 使用定理 `IsEvenlyCovered.toTrivialization_apply`：toTrivialization_apply {x : E} [
Nonempty I] (h : IsEvenlyCovered f (f x) I) : (h.toTrivialization x).2 = ⟨x, rfl
⟩
-/
protected theorem isLocalHomeomorphOn (hf : IsCoveringMapOn f s) :
    IsLocalHomeomorphOn f (f ⁻¹' s) := by
  refine IsLocalHomeomorphOn.mk f (f ⁻¹' s) fun x hx ↦ ?_
  have : Nonempty (f ⁻¹' {f x}) := ⟨⟨x, rfl⟩⟩
  let e := (hf (f x) hx).toTrivialization
  have h := (hf (f x) hx).mem_toTrivialization_baseSet
  let he := e.mem_source.2 h
  refine
    ⟨e.toOpenPartialHomeomorph.trans
        { toFun := fun p => p.1
          invFun := fun p => ⟨p, x, rfl⟩
          source := e.baseSet ×ˢ ({⟨x, rfl⟩} : Set (f ⁻¹' {f x}))
          target := e.baseSet
          open_source :=
            e.open_baseSet.prod (discreteTopology_iff_isOpen_singleton.1 (hf (f x) hx).1 ⟨x, rfl⟩)
          open_target := e.open_baseSet
          map_source' := fun p => And.left
          map_target' := fun p hp => ⟨hp, rfl⟩
          left_inv' := fun p hp => Prod.ext rfl hp.2.symm
          right_inv' := fun p _ => rfl
          continuousOn_toFun := continuousOn_fst
          continuousOn_invFun := by fun_prop },
      ⟨he, by rwa [e.toOpenPartialHomeomorph.symm_symm, e.proj_toFun x he],
        (hf (f x) hx).toTrivialization_apply⟩,
      fun p h => (e.proj_toFun p h.1).symm⟩
/-
**IsCoveringMapOn.restrictPreimage** 是 Mathlib 中的一个定理，位于命名空间 `IsCoveringMapOn`。
形式化陈述：restrictPreimage (hf : IsCoveringMapOn f s) (t : Set X) : IsCoveringMapOn 
(t.restrictPreimage f) (Subtype.val ⁻¹' s)
参数：hf : IsCoveringMapOn f s；t : Set X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsEvenlyCovered.to_isEvenlyCovered_preimage`：to_isEvenlyCovered_preimage
 {x : X} (h : IsEvenlyCovered f x I) : IsEvenlyCovered f x (f ⁻¹' {x})
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `IsEvenlyCovered.restrictPreimage`：restrictPreimage {x : X} (hxs : x in s
) (h : IsEvenlyCovered f x I) : IsEvenlyCovered (s.restrictPreimage f) ⟨x, hxs⟩ 
I
-/
theorem restrictPreimage (hf : IsCoveringMapOn f s) (t : Set X) :
    IsCoveringMapOn (t.restrictPreimage f) (Subtype.val ⁻¹' s) :=
  fun x hs ↦ ((hf x hs).restrictPreimage t x.2).to_isEvenlyCovered_preimage
/-
**IsCoveringMapOn.comp_homeomorph** 是 Mathlib 中的一个定理，位于命名空间 `IsCoveringMapOn`。
形式化陈述：comp_homeomorph (hf : IsCoveringMapOn f s) {E'} [TopologicalSpace E'] (g :
 E' ≃ₜ E) : IsCoveringMapOn (f ∘ g) s
参数：hf : IsCoveringMapOn f s；g : E' ≃ₜ E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsEvenlyCovered.to_isEvenlyCovered_preimage`：to_isEvenlyCovered_preimage
 {x : X} (h : IsEvenlyCovered f x I) : IsEvenlyCovered f x (f ⁻¹' {x})
· 使用定理 `IsEvenlyCovered.comp_homeomorph`：comp_homeomorph {x : X} (h : IsEvenlyCo
vered f x I) {E'} [TopologicalSpace E'] (g : E' ≃ₜ E) : IsEvenlyCovered (f ∘ g) 
x I
-/
theorem comp_homeomorph (hf : IsCoveringMapOn f s) {E'} [TopologicalSpace E'] (g : E' ≃ₜ E) :
    IsCoveringMapOn (f ∘ g) s :=
  fun x hx ↦ ((hf x hx).comp_homeomorph _).to_isEvenlyCovered_preimage
/-
**IsCoveringMapOn.comp_homeomorph_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsCoveringMapOn
`。
形式化陈述：∀ {E : Type u_1} {X : Type u_2} [inst : TopologicalSpace E] [inst_1 : Topo
logicalSpace X] {f : E → X} {s : Set X}   {E' : Type u_3} [inst_2 : TopologicalS
pace E'] (g : E' ≃ₜ E), IsCoveringMapOn (f ∘ ⇑g) s ↔ IsCoveringMapOn f s
参数：g : E' ≃ₜ E；f ∘ ⇑g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Homeomorph.apply_symm_apply`：apply_symm_apply (h : X ≃ₜ Y) (y : Y) : h (
h.symm y) = y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsCoveringMapOn.comp_homeomorph`：comp_homeomorph (hf : IsCoveringMapOn f
 s) {E'} [TopologicalSpace E'] (g : E' ≃ₜ E) : IsCoveringMapOn (f ∘ g) s
-/
@[simp] theorem comp_homeomorph_iff {E'} [TopologicalSpace E'] (g : E' ≃ₜ E) :
    IsCoveringMapOn (f ∘ g) s ↔ IsCoveringMapOn f s where
  mp h := by convert! h.comp_homeomorph g.symm; ext; simp
  mpr h := h.comp_homeomorph g
/-
**IsCoveringMapOn.homeomorph_comp** 是 Mathlib 中的一个定理，位于命名空间 `IsCoveringMapOn`。
形式化陈述：homeomorph_comp (hf : IsCoveringMapOn f s) {Y} [TopologicalSpace Y] (g : X
 ≃ₜ Y) : IsCoveringMapOn (g ∘ f) (g.symm ⁻¹' s)
参数：hf : IsCoveringMapOn f s；g : X ≃ₜ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsEvenlyCovered.to_isEvenlyCovered_preimage`：to_isEvenlyCovered_preimage
 {x : X} (h : IsEvenlyCovered f x I) : IsEvenlyCovered f x (f ⁻¹' {x})
· 使用定理 `IsEvenlyCovered.homeomorph_comp`：homeomorph_comp {x : X} (h : IsEvenlyCo
vered f x I) {Y} [TopologicalSpace Y] (g : X ≃ₜ Y) : IsEvenlyCovered (g ∘ f) (g 
x) I
· 使用定理 `Homeomorph.apply_symm_apply`：apply_symm_apply (h : X ≃ₜ Y) (y : Y) : h (
h.symm y) = y
-/
theorem homeomorph_comp (hf : IsCoveringMapOn f s) {Y} [TopologicalSpace Y] (g : X ≃ₜ Y) :
    IsCoveringMapOn (g ∘ f) (g.symm ⁻¹' s) :=
  fun y hy ↦ (g.apply_symm_apply y ▸ (hf _ hy).homeomorph_comp _).to_isEvenlyCovered_preimage
/-
**IsCoveringMapOn.homeomorph_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsCoveringMapOn
`。
形式化陈述：∀ {E : Type u_1} {X : Type u_2} [inst : TopologicalSpace E] [inst_1 : Topo
logicalSpace X] {f : E → X} {s : Set X}   {Y : Type u_3} [inst_2 : TopologicalSp
ace Y] (g : X ≃ₜ Y),   IsCoveringMapOn (⇑g ∘ f) (⇑g.symm ⁻¹' s) ↔ IsCoveringMapO
n f s
参数：g : X ≃ₜ Y；⇑g ∘ f；⇑g.symm ⁻¹' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Homeomorph.symm_apply_apply`：symm_apply_apply (h : X ≃ₜ Y) (x : X) : h.s
ymm (h x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `IsCoveringMapOn.homeomorph_comp`：homeomorph_comp (hf : IsCoveringMapOn f
 s) {Y} [TopologicalSpace Y] (g : X ≃ₜ Y) : IsCoveringMapOn (g ∘ f) (g.symm ⁻¹' 
s)
-/
@[simp] theorem homeomorph_comp_iff {Y} [TopologicalSpace Y] (g : X ≃ₜ Y) :
    IsCoveringMapOn (g ∘ f) (g.symm ⁻¹' s) ↔ IsCoveringMapOn f s where
  mp h := by convert! h.homeomorph_comp g.symm <;> (ext; simp)
  mpr h := h.homeomorph_comp g

end IsCoveringMapOn

/-- A covering map is a continuous function `f : E → X` with discrete fibers such that each point
  of `X` has an evenly covered neighborhood. -/
/-
**IsCoveringMap** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsCoveringMap
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A covering map is a continuous function `f : E → X` with discrete fibers such th
at each point
  of `X` has an evenly covered neighborhood.
-/
def IsCoveringMap :=
  ∀ x, IsEvenlyCovered f x (f ⁻¹' {x})

variable {f}
/-
**isCoveringMap_iff_isCoveringMapOn_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCoveringMap_iff_isCoveringMapOn_univ : IsCoveringMap f ↔ IsCoveringMapOn
 f .univ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isCoveringMap_iff_isCoveringMapOn_univ : IsCoveringMap f ↔ IsCoveringMapOn f .univ := by
  simp only [IsCoveringMap, IsCoveringMapOn, Set.mem_univ, forall_true_left]
/-
**IsCoveringMap.isCoveringMapOn** 是 Mathlib 中的一个定理，位于命名空间 `IsCoveringMap`。
形式化陈述：∀ {E : Type u_1} {X : Type u_2} [inst : TopologicalSpace E] [inst_1 : Topo
logicalSpace X] {f : E → X},   IsCoveringMap f → IsCoveringMapOn f Set.univ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isCoveringMap_iff_isCoveringMapOn_univ`：isCoveringMap_iff_isCoveringMapO
n_univ : IsCoveringMap f ↔ IsCoveringMapOn f .univ
-/
protected theorem IsCoveringMap.isCoveringMapOn (hf : IsCoveringMap f) : IsCoveringMapOn f .univ :=
  isCoveringMap_iff_isCoveringMapOn_univ.mp hf
/-
**IsCoveringMapOn.isCoveringMap_restrictPreimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoveringMapOn.isCoveringMap_restrictPreimage (hf : IsCoveringMapOn f s) 
: IsCoveringMap (s.restrictPreimage f)
参数：hf : IsCoveringMapOn f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isCoveringMap_iff_isCoveringMapOn_univ`：isCoveringMap_iff_isCoveringMapO
n_univ : IsCoveringMap f ↔ IsCoveringMapOn f .univ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.coe_preimage_self`：coe_preimage_self (s : Set α) : ((↑) : s -> α
) ⁻¹' s = univ
· 使用定理 `IsCoveringMapOn.restrictPreimage`：restrictPreimage (hf : IsCoveringMapOn
 f s) (t : Set X) : IsCoveringMapOn (t.restrictPreimage f) (Subtype.val ⁻¹' s)
-/
theorem IsCoveringMapOn.isCoveringMap_restrictPreimage (hf : IsCoveringMapOn f s) :
    IsCoveringMap (s.restrictPreimage f) :=
  isCoveringMap_iff_isCoveringMapOn_univ.mpr <| by simpa using hf.restrictPreimage s
/-
**IsCoveringMapOn.of_isCoveringMap_restrictPreimage** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：IsCoveringMapOn.of_isCoveringMap_restrictPreimage (hs : IsOpen s) (hfs : I
sOpen (f ⁻¹' s)) (hf : IsCoveringMap (s.restrictPreimage f)) : IsCoveringMapOn f
 s
参数：hs : IsOpen s；hfs : IsOpen (f ⁻¹' s)；hf : IsCoveringMap (s.restrictPreimage f
)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsEvenlyCovered.to_isEvenlyCovered_preimage`：to_isEvenlyCovered_preimage
 {x : X} (h : IsEvenlyCovered f x I) : IsEvenlyCovered f x (f ⁻¹' {x})
· 使用定理 `IsEvenlyCovered.comp_subtypeVal`：comp_subtypeVal (hs : IsOpen s) (hfs : 
IsOpen (f ⁻¹' s)) {x : X} (hx : x in s) (h : IsEvenlyCovered (fun e : f ⁻¹' s =>
 f e) x I) : IsEvenly…
· 使用定理 `IsEvenlyCovered.subtypeVal_comp`：subtypeVal_comp (hs : IsOpen s) {x : s}
 {f : E -> s} (h : IsEvenlyCovered f x I) : IsEvenlyCovered (Subtype.val ∘ f) x 
I
-/
theorem IsCoveringMapOn.of_isCoveringMap_restrictPreimage (hs : IsOpen s) (hfs : IsOpen (f ⁻¹' s))
    (hf : IsCoveringMap (s.restrictPreimage f)) : IsCoveringMapOn f s := fun x hx ↦
  (((hf ⟨x, hx⟩).subtypeVal_comp _ hs).comp_subtypeVal _ hs hfs hx).to_isEvenlyCovered_preimage

variable (f)

namespace IsCoveringMap

/-
**IsCoveringMap.of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `IsCoveringMap`。
形式化陈述：of_isEmpty [IsEmpty E] : IsCoveringMap f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isCoveringMap_iff_isCoveringMapOn_univ`：isCoveringMap_iff_isCoveringMapO
n_univ : IsCoveringMap f ↔ IsCoveringMapOn f .univ
· 使用定理 `IsCoveringMapOn.of_isEmpty`：of_isEmpty [IsEmpty E] : IsCoveringMapOn f s
-/
theorem of_isEmpty [IsEmpty E] : IsCoveringMap f :=
  isCoveringMap_iff_isCoveringMapOn_univ.mpr <| .of_isEmpty _ _
/-
**IsCoveringMap.of_discreteTopology** 是 Mathlib 中的一个定理，位于命名空间 `IsCoveringMap`。
形式化陈述：of_discreteTopology [DiscreteTopology E] [DiscreteTopology X] : IsCovering
Map f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instDiscreteTopologySubtype`：∀ {X : Type u} {p : X → Prop} [inst : Topol
ogicalSpace X] [DiscreteTopology X], DiscreteTopology (Subtype p)
· 使用定理 `isOpen_discrete`：isOpen_discrete (s : Set α) : IsOpen s
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem of_discreteTopology [DiscreteTopology E] [DiscreteTopology X] : IsCoveringMap f :=
  fun x ↦ ⟨inferInstance, {x}, rfl, isOpen_discrete _, isOpen_discrete _,
    { toFun e := ⟨⟨x, rfl⟩, e⟩
      invFun xi := xi.2
      left_inv _ := rfl
      right_inv _ := Prod.ext (Subsingleton.elim ..) rfl },
    (·.2.symm)⟩

/-- A constructor for `IsCoveringMap` when there are both empty and nonempty fibers. -/
/-
**IsCoveringMap.mk'** 是 Mathlib 中的一个定理，位于命名空间 `IsCoveringMap`。
形式化陈述：mk' (F : X -> Type*) [forall x, TopologicalSpace (F x)] [forall x, Discret
eTopology (F x)] (t : forall x, x in Set.range f -> {t : Trivialization (F x) f 
// x in t.baseSet}) (h : IsClosed (Set.range f)) : IsCoveringMap f
参数：F : X -> Type*；F x；F x；t : forall x, x in Set.range f -> {t : Trivialization 
(F x) f // x in t.baseSet}；h : IsClosed (Set.range f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isCoveringMap_iff_isCoveringMapOn_univ`：isCoveringMap_iff_isCoveringMapO
n_univ : IsCoveringMap f ↔ IsCoveringMapOn f .univ
· 使用定理 `IsCoveringMapOn.mk'`：mk' (F : s -> Type*) [forall x : s, TopologicalSpac
e (F x)] [hF : forall x : s, DiscreteTopology (F x)] (t : forall x : s, x.1 in S
et.range …
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `Set.eq_empty_of_forall_notMem`：eq_empty_of_forall_notMem (h : forall x, 
x ∉ s) : s = ∅

--- 原说明 ---
A constructor for `IsCoveringMap` when there are both empty and nonempty fibers.
-/
theorem mk' (F : X → Type*) [∀ x, TopologicalSpace (F x)] [∀ x, DiscreteTopology (F x)]
    (t : ∀ x, x ∈ Set.range f → {t : Trivialization (F x) f // x ∈ t.baseSet})
    (h : IsClosed (Set.range f)) : IsCoveringMap f :=
  isCoveringMap_iff_isCoveringMapOn_univ.mpr <| .mk' f _ _ (fun x h ↦ t x h) fun _x hx ↦
    ⟨_, h.isOpen_compl.mem_nhds hx, Set.eq_empty_of_forall_notMem fun x h ↦ h ⟨x, rfl⟩⟩
/-
**IsCoveringMap.mk** 是 Mathlib 中的一个定理，位于命名空间 `IsCoveringMap`。
形式化陈述：mk (F : X -> Type*) [forall x, TopologicalSpace (F x)] [forall x, Discrete
Topology (F x)] (e : forall x, Trivialization (F x) f) (h : forall x, x in (e x)
.baseSet) : IsCoveringMap f
参数：F : X -> Type*；F x；F x；e : forall x, Trivialization (F x) f；h : forall x, x i
n (e x).baseSet。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isCoveringMap_iff_isCoveringMapOn_univ`：isCoveringMap_iff_isCoveringMapO
n_univ : IsCoveringMap f ↔ IsCoveringMapOn f .univ
· 使用定理 `IsCoveringMapOn.mk`：mk (F : s -> Type*) [forall x, TopologicalSpace (F x
)] [hF : forall x, DiscreteTopology (F x)] (e : forall x, Trivialization (F x) f
) (h : f…
-/
theorem mk (F : X → Type*) [∀ x, TopologicalSpace (F x)] [∀ x, DiscreteTopology (F x)]
    (e : ∀ x, Trivialization (F x) f) (h : ∀ x, x ∈ (e x).baseSet) : IsCoveringMap f :=
  isCoveringMap_iff_isCoveringMapOn_univ.mpr <| .mk _ _ _ _ fun x ↦ h x

variable {f}
variable (hf : IsCoveringMap f)
include hf
/-
**IsCoveringMap.continuous** 是 Mathlib 中的一个定理，位于命名空间 `IsCoveringMap`。
形式化陈述：∀ {E : Type u_1} {X : Type u_2} [inst : TopologicalSpace E] [inst_1 : Topo
logicalSpace X] {f : E → X},   IsCoveringMap f → Continuous f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `continuousOn_univ`：continuousOn_univ {f : α -> β} : ContinuousOn f univ 
↔ Continuous f
· 使用定理 `IsCoveringMapOn.continuousOn`：∀ {E : Type u_1} {X : Type u_2} [inst : To
pologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X} {s : Set X},   IsCov
eringMapOn f s → C…
· 使用定理 `IsCoveringMap.isCoveringMapOn`：∀ {E : Type u_1} {X : Type u_2} [inst : T
opologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X},   IsCoveringMap f 
→ IsCoveringMapOn f…
-/
protected theorem continuous : Continuous f :=
  continuousOn_univ.mp hf.isCoveringMapOn.continuousOn
/-
**IsCoveringMap.isLocalHomeomorph** 是 Mathlib 中的一个定理，位于命名空间 `IsCoveringMap`。
形式化陈述：∀ {E : Type u_1} {X : Type u_2} [inst : TopologicalSpace E] [inst_1 : Topo
logicalSpace X] {f : E → X},   IsCoveringMap f → IsLocalHomeomorph f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isLocalHomeomorph_iff_isLocalHomeomorphOn_univ`：isLocalHomeomorph_iff_is
LocalHomeomorphOn_univ : IsLocalHomeomorph f ↔ IsLocalHomeomorphOn f Set.univ
· 使用定理 `IsCoveringMapOn.isLocalHomeomorphOn`：∀ {E : Type u_1} {X : Type u_2} [in
st : TopologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X} {s : Set X}, 
  IsCoveringMapOn f s → I…
· 使用定理 `IsCoveringMap.isCoveringMapOn`：∀ {E : Type u_1} {X : Type u_2} [inst : T
opologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X},   IsCoveringMap f 
→ IsCoveringMapOn f…
-/
protected theorem isLocalHomeomorph : IsLocalHomeomorph f :=
  isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr hf.isCoveringMapOn.isLocalHomeomorphOn
/-
**IsCoveringMap.isOpenMap** 是 Mathlib 中的一个定理，位于命名空间 `IsCoveringMap`。
形式化陈述：∀ {E : Type u_1} {X : Type u_2} [inst : TopologicalSpace E] [inst_1 : Topo
logicalSpace X] {f : E → X},   IsCoveringMap f → IsOpenMap f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalHomeomorph.isOpenMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   IsLocalHomeomorph 
f → IsOpenMap f
· 使用定理 `IsCoveringMap.isLocalHomeomorph`：∀ {E : Type u_1} {X : Type u_2} [inst :
 TopologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X},   IsCoveringMap 
f → IsLocalHomeomorph…
-/
protected theorem isOpenMap : IsOpenMap f :=
  hf.isLocalHomeomorph.isOpenMap
/-
**IsCoveringMap.isQuotientMap** 是 Mathlib 中的一个定理，位于命名空间 `IsCoveringMap`。
形式化陈述：isQuotientMap (hf' : Function.Surjective f) : IsQuotientMap f
参数：hf' : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpenMap.isQuotientMap`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f → Continuo
us f → Functi…
· 使用定理 `IsCoveringMap.isOpenMap`：∀ {E : Type u_1} {X : Type u_2} [inst : Topolog
icalSpace E] [inst_1 : TopologicalSpace X] {f : E → X},   IsCoveringMap f → IsOp
enMap f
· 使用定理 `IsCoveringMap.continuous`：∀ {E : Type u_1} {X : Type u_2} [inst : Topolo
gicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X},   IsCoveringMap f → Con
tinuous f
-/
theorem isQuotientMap (hf' : Function.Surjective f) : IsQuotientMap f :=
  hf.isOpenMap.isQuotientMap hf.continuous hf'
/-
**IsCoveringMap.isSeparatedMap** 是 Mathlib 中的一个定理，位于命名空间 `IsCoveringMap`。
形式化陈述：∀ {E : Type u_1} {X : Type u_2} [inst : TopologicalSpace E] [inst_1 : Topo
logicalSpace X] {f : E → X},   IsCoveringMap f → IsSeparatedMap f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsEvenlyCovered.discreteTopology_fiber`：discreteTopology_fiber {x : X} (
h : IsEvenlyCovered f x I) : DiscreteTopology (f ⁻¹' {x})
· 使用定理 `IsEvenlyCovered.mem_toTrivialization_baseSet`：mem_toTrivialization_baseS
et {x : X} [Nonempty I] (h : IsEvenlyCovered f x I) : x in h.toTrivialization.ba
seSet
· 使用定理 `ContinuousOn.isOpen_inter_preimage`：ContinuousOn.isOpen_inter_preimage {
t : Set β} (hf : ContinuousOn f s) (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s i
nter f ⁻¹' t)
· 使用定理 `PartialHomeomorph.continuousOn_toFun`：∀ {X : Type u_7} {Y : Type u_8} [i
nst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : PartialHomeomo
rph X Y), ContinuousOn (↑s…
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `Continuous.isOpen_preimage`：∀ {X : Type u} {Y : Type v} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Continuous f → ∀ (s : S
et Y), IsOpen s …
· 使用定理 `continuous_snd`：continuous_snd (f : X → Y × Z) (hf : Continuous f) : Con
tinuous (fun x ↦ (f x).snd)
· 使用定理 `isOpen_discrete`：isOpen_discrete (s : Set α) : IsOpen s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Bundle.Trivialization.mem_source`：∀ {B : Type u_1} {F : Type u_2} {Z : T
ype u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {proj : Z → B
}   [inst_2 : Topologi…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `OpenPartialHomeomorph.injOn`：∀ {X : Type u_1} {Y : Type u_3} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorph X Y)
, Set.InjOn (↑e) …
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `Bundle.Trivialization.proj_toFun`：∀ {B : Type u_1} {F : Type u_2} {Z : T
ype u_4} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 : T
opologicalSpace Z] {pr…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
protected theorem isSeparatedMap : IsSeparatedMap f :=
  fun e₁ e₂ he hne ↦ by
    have : Nonempty (f ⁻¹' {f e₁}) := ⟨⟨e₁, rfl⟩⟩
    specialize hf (f e₁)
    let t := hf.toTrivialization
    have := hf.discreteTopology_fiber
    have he₁ := hf.mem_toTrivialization_baseSet
    have he₂ := he₁; simp_rw [he] at he₂; rw [← t.mem_source] at he₁ he₂
    refine ⟨t.source ∩ (Prod.snd ∘ t) ⁻¹' {(t e₁).2}, t.source ∩ (Prod.snd ∘ t) ⁻¹' {(t e₂).2},
      ?_, ?_, ⟨he₁, rfl⟩, ⟨he₂, rfl⟩, Set.disjoint_left.mpr fun x h₁ h₂ ↦ hne (t.injOn he₁ he₂ ?_)⟩
    iterate 2
      exact t.continuousOn_toFun.isOpen_inter_preimage t.open_source
        (continuous_snd.isOpen_preimage _ <| isOpen_discrete _)
    refine Prod.ext ?_ (h₁.2.symm.trans h₂.2)
    rwa [t.proj_toFun e₁ he₁, t.proj_toFun e₂ he₂]

variable {A} [TopologicalSpace A] {s : Set A} {g g₁ g₂ : A → E}

/-- Proposition 1.34 of [hatcher02]. -/
/-
**IsCoveringMap.eq_of_comp_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsCoveringMap`。
形式化陈述：eq_of_comp_eq [PreconnectedSpace A] (h₁ : Continuous g₁) (h₂ : Continuous 
g₂) (he : f ∘ g₁ = f ∘ g₂) (a : A) (ha : g₁ a = g₂ a) : g₁ = g₂
参数：h₁ : Continuous g₁；h₂ : Continuous g₂；he : f ∘ g₁ = f ∘ g₂；a : A；ha : g₁ a = 
g₂ a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSeparatedMap.eq_of_comp_eq`：eq_of_comp_eq [PreconnectedSpace A] (h₁ : 
Continuous g₁) (h₂ : Continuous g₂) (he : p ∘ g₁ = p ∘ g₂) (a : A) (ha : g₁ a = 
g₂ a) : g₁ = g₂
· 使用定理 `IsCoveringMap.isSeparatedMap`：∀ {E : Type u_1} {X : Type u_2} [inst : To
pologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X},   IsCoveringMap f →
 IsSeparatedMap f
· 使用引理 `IsLocalHomeomorph.isLocallyInjective`：isLocallyInjective (hf : IsLocalHo
meomorph f) : IsLocallyInjective f
· 使用定理 `IsCoveringMap.isLocalHomeomorph`：∀ {E : Type u_1} {X : Type u_2} [inst :
 TopologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X},   IsCoveringMap 
f → IsLocalHomeomorph…

--- 原说明 ---
Proposition 1.34 of [hatcher02].
-/
theorem eq_of_comp_eq [PreconnectedSpace A] (h₁ : Continuous g₁) (h₂ : Continuous g₂)
    (he : f ∘ g₁ = f ∘ g₂) (a : A) (ha : g₁ a = g₂ a) : g₁ = g₂ :=
  hf.isSeparatedMap.eq_of_comp_eq hf.isLocalHomeomorph.isLocallyInjective h₁ h₂ he a ha
/-
**IsCoveringMap.const_of_comp** 是 Mathlib 中的一个定理，位于命名空间 `IsCoveringMap`。
形式化陈述：const_of_comp [PreconnectedSpace A] (cont : Continuous g) (he : forall a a
', f (g a) = f (g a')) (a a') : g a = g a'
参数：cont : Continuous g；he : forall a a', f (g a) = f (g a')；a a'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSeparatedMap.const_of_comp`：const_of_comp [PreconnectedSpace A] (cont 
: Continuous g) (he : forall a a', p (g a) = p (g a')) (a a') : g a = g a'
· 使用定理 `IsCoveringMap.isSeparatedMap`：∀ {E : Type u_1} {X : Type u_2} [inst : To
pologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X},   IsCoveringMap f →
 IsSeparatedMap f
· 使用引理 `IsLocalHomeomorph.isLocallyInjective`：isLocallyInjective (hf : IsLocalHo
meomorph f) : IsLocallyInjective f
· 使用定理 `IsCoveringMap.isLocalHomeomorph`：∀ {E : Type u_1} {X : Type u_2} [inst :
 TopologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X},   IsCoveringMap 
f → IsLocalHomeomorph…
-/
theorem const_of_comp [PreconnectedSpace A] (cont : Continuous g)
    (he : ∀ a a', f (g a) = f (g a')) (a a') : g a = g a' :=
  hf.isSeparatedMap.const_of_comp hf.isLocalHomeomorph.isLocallyInjective cont he a a'
/-
**IsCoveringMap.eqOn_of_comp_eqOn** 是 Mathlib 中的一个定理，位于命名空间 `IsCoveringMap`。
形式化陈述：eqOn_of_comp_eqOn (hs : IsPreconnected s) (h₁ : ContinuousOn g₁ s) (h₂ : C
ontinuousOn g₂ s) (he : s.EqOn (f ∘ g₁) (f ∘ g₂)) {a : A} (has : a in s) (ha : g
₁ a = g₂ a) : s.EqOn g₁ g₂
参数：hs : IsPreconnected s；h₁ : ContinuousOn g₁ s；h₂ : ContinuousOn g₂ s；he : s.Eq
On (f ∘ g₁) (f ∘ g₂)；has : a in s；ha : g₁ a = g₂ a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSeparatedMap.eqOn_of_comp_eqOn`：eqOn_of_comp_eqOn (hs : IsPreconnected
 s) (h₁ : ContinuousOn g₁ s) (h₂ : ContinuousOn g₂ s) (he : s.EqOn (p ∘ g₁) (p ∘
 g₂)) {a : A} (has : a…
· 使用定理 `IsCoveringMap.isSeparatedMap`：∀ {E : Type u_1} {X : Type u_2} [inst : To
pologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X},   IsCoveringMap f →
 IsSeparatedMap f
· 使用引理 `IsLocalHomeomorph.isLocallyInjective`：isLocallyInjective (hf : IsLocalHo
meomorph f) : IsLocallyInjective f
· 使用定理 `IsCoveringMap.isLocalHomeomorph`：∀ {E : Type u_1} {X : Type u_2} [inst :
 TopologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X},   IsCoveringMap 
f → IsLocalHomeomorph…
-/
theorem eqOn_of_comp_eqOn (hs : IsPreconnected s) (h₁ : ContinuousOn g₁ s) (h₂ : ContinuousOn g₂ s)
    (he : s.EqOn (f ∘ g₁) (f ∘ g₂)) {a : A} (has : a ∈ s) (ha : g₁ a = g₂ a) : s.EqOn g₁ g₂ :=
  hf.isSeparatedMap.eqOn_of_comp_eqOn hf.isLocalHomeomorph.isLocallyInjective hs h₁ h₂ he has ha
/-
**IsCoveringMap.constOn_of_comp** 是 Mathlib 中的一个定理，位于命名空间 `IsCoveringMap`。
形式化陈述：constOn_of_comp (hs : IsPreconnected s) (cont : ContinuousOn g s) (he : fo
rall a in s, forall a' in s, f (g a) = f (g a')) {a a'} (ha : a in s) (ha' : a' 
in s) : g a = g a'
参数：hs : IsPreconnected s；cont : ContinuousOn g s；he : forall a in s, forall a' i
n s, f (g a) = f (g a')；ha : a in s；ha' : a' in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSeparatedMap.constOn_of_comp`：constOn_of_comp (hs : IsPreconnected s) 
(cont : ContinuousOn g s) (he : forall a in s, forall a' in s, p (g a) = p (g a'
)) {a a'} (ha : a in…
· 使用定理 `IsCoveringMap.isSeparatedMap`：∀ {E : Type u_1} {X : Type u_2} [inst : To
pologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X},   IsCoveringMap f →
 IsSeparatedMap f
· 使用引理 `IsLocalHomeomorph.isLocallyInjective`：isLocallyInjective (hf : IsLocalHo
meomorph f) : IsLocallyInjective f
· 使用定理 `IsCoveringMap.isLocalHomeomorph`：∀ {E : Type u_1} {X : Type u_2} [inst :
 TopologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X},   IsCoveringMap 
f → IsLocalHomeomorph…
-/
theorem constOn_of_comp (hs : IsPreconnected s) (cont : ContinuousOn g s)
    (he : ∀ a ∈ s, ∀ a' ∈ s, f (g a) = f (g a'))
    {a a'} (ha : a ∈ s) (ha' : a' ∈ s) : g a = g a' :=
  hf.isSeparatedMap.constOn_of_comp hf.isLocalHomeomorph.isLocallyInjective hs cont he ha ha'
/-
**IsCoveringMap.restrictPreimage** 是 Mathlib 中的一个定理，位于命名空间 `IsCoveringMap`。
形式化陈述：restrictPreimage (t : Set X) : IsCoveringMap (t.restrictPreimage f)
参数：t : Set X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isCoveringMap_iff_isCoveringMapOn_univ`：isCoveringMap_iff_isCoveringMapO
n_univ : IsCoveringMap f ↔ IsCoveringMapOn f .univ
· 使用定理 `IsCoveringMapOn.restrictPreimage`：restrictPreimage (hf : IsCoveringMapOn
 f s) (t : Set X) : IsCoveringMapOn (t.restrictPreimage f) (Subtype.val ⁻¹' s)
-/
theorem restrictPreimage (t : Set X) : IsCoveringMap (t.restrictPreimage f) := by
  rw [isCoveringMap_iff_isCoveringMapOn_univ] at hf ⊢
  exact hf.restrictPreimage t
/-
**IsCoveringMap.comp_homeomorph** 是 Mathlib 中的一个定理，位于命名空间 `IsCoveringMap`。
形式化陈述：comp_homeomorph {E'} [TopologicalSpace E'] (g : E' ≃ₜ E) : IsCoveringMap (
f ∘ g)
参数：g : E' ≃ₜ E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isCoveringMap_iff_isCoveringMapOn_univ`：isCoveringMap_iff_isCoveringMapO
n_univ : IsCoveringMap f ↔ IsCoveringMapOn f .univ
· 使用定理 `IsCoveringMapOn.comp_homeomorph`：comp_homeomorph (hf : IsCoveringMapOn f
 s) {E'} [TopologicalSpace E'] (g : E' ≃ₜ E) : IsCoveringMapOn (f ∘ g) s
-/
theorem comp_homeomorph {E'} [TopologicalSpace E'] (g : E' ≃ₜ E) : IsCoveringMap (f ∘ g) := by
  rw [isCoveringMap_iff_isCoveringMapOn_univ] at hf ⊢
  exact hf.comp_homeomorph g
/-
**IsCoveringMap.homeomorph_comp** 是 Mathlib 中的一个定理，位于命名空间 `IsCoveringMap`。
形式化陈述：homeomorph_comp {Y} [TopologicalSpace Y] (g : X ≃ₜ Y) : IsCoveringMap (g ∘
 f)
参数：g : X ≃ₜ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isCoveringMap_iff_isCoveringMapOn_univ`：isCoveringMap_iff_isCoveringMapO
n_univ : IsCoveringMap f ↔ IsCoveringMapOn f .univ
· 使用定理 `IsCoveringMapOn.homeomorph_comp`：homeomorph_comp (hf : IsCoveringMapOn f
 s) {Y} [TopologicalSpace Y] (g : X ≃ₜ Y) : IsCoveringMapOn (g ∘ f) (g.symm ⁻¹' 
s)
-/
theorem homeomorph_comp {Y} [TopologicalSpace Y] (g : X ≃ₜ Y) : IsCoveringMap (g ∘ f) := by
  rw [isCoveringMap_iff_isCoveringMapOn_univ] at hf ⊢
  exact hf.homeomorph_comp g

omit hf
/-
**IsCoveringMap.comp_homeomorph_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsCoveringMap`。
形式化陈述：comp_homeomorph_iff {E'} [TopologicalSpace E'] (g : E' ≃ₜ E) : IsCoveringM
ap (f ∘ g) ↔ IsCoveringMap f where mp h
参数：g : E' ≃ₜ E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Homeomorph.apply_symm_apply`：apply_symm_apply (h : X ≃ₜ Y) (y : Y) : h (
h.symm y) = y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsCoveringMap.comp_homeomorph`：comp_homeomorph {E'} [TopologicalSpace E'
] (g : E' ≃ₜ E) : IsCoveringMap (f ∘ g)
-/
theorem comp_homeomorph_iff {E'} [TopologicalSpace E'] (g : E' ≃ₜ E) :
    IsCoveringMap (f ∘ g) ↔ IsCoveringMap f where
  mp h := by convert! h.comp_homeomorph g.symm; ext; simp
  mpr h := h.comp_homeomorph g
/-
**IsCoveringMap.homeomorph_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsCoveringMap`。
形式化陈述：homeomorph_comp_iff {Y} [TopologicalSpace Y] (g : X ≃ₜ Y) : IsCoveringMap 
(g ∘ f) ↔ IsCoveringMap f where mp h
参数：g : X ≃ₜ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Homeomorph.symm_apply_apply`：symm_apply_apply (h : X ≃ₜ Y) (x : X) : h.s
ymm (h x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsCoveringMap.homeomorph_comp`：homeomorph_comp {Y} [TopologicalSpace Y] 
(g : X ≃ₜ Y) : IsCoveringMap (g ∘ f)
-/
theorem homeomorph_comp_iff {Y} [TopologicalSpace Y] (g : X ≃ₜ Y) :
    IsCoveringMap (g ∘ f) ↔ IsCoveringMap f where
  mp h := by convert! h.homeomorph_comp g.symm; ext; simp
  mpr h := h.homeomorph_comp g

end IsCoveringMap

/-
**IsCoveringMapOn.of_isCoveringMap_subtype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoveringMapOn.of_isCoveringMap_subtype {s : Set X} (hs : IsOpen s) {f : 
E -> X} (h : forall x, f x in s) (hf : IsCoveringMap fun x => (⟨f x, h x⟩ : s)) 
: IsCoveringMapOn f s
参数：hs : IsOpen s；h : forall x, f x in s；hf : IsCoveringMap fun x => (⟨f x, h x⟩ 
: s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `IsCoveringMapOn.of_isCoveringMap_restrictPreimage`：IsCoveringMapOn.of_is
CoveringMap_restrictPreimage (hs : IsOpen s) (hfs : IsOpen (f ⁻¹' s)) (hf : IsCo
veringMap (s.restrictPreimage f)) : IsC…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCoveringMap.comp_homeomorph`：comp_homeomorph {E'} [TopologicalSpace E'
] (g : E' ≃ₜ E) : IsCoveringMap (f ∘ g)
-/
theorem IsCoveringMapOn.of_isCoveringMap_subtype {s : Set X} (hs : IsOpen s) {f : E → X}
    (h : ∀ x, f x ∈ s) (hf : IsCoveringMap fun x ↦ (⟨f x, h x⟩ : s)) : IsCoveringMapOn f s :=
  have eq : f ⁻¹' s = .univ := by simpa [Set.range, Set.subset_def] using h
  of_isCoveringMap_restrictPreimage _ hs (by simp [eq]) <|
    hf.comp_homeomorph ((Homeomorph.setCongr eq).trans (Homeomorph.Set.univ E))

variable {f}
/-
**IsFiberBundle.isCoveringMap** 是 Mathlib 中的一个定理，位于命名空间 `IsFiberBundle`。
形式化陈述：∀ {E : Type u_1} {X : Type u_2} [inst : TopologicalSpace E] [inst_1 : Topo
logicalSpace X] {f : E → X} {F : Type u_3}   [inst_2 : TopologicalSpace F] [Disc
reteTopology F], (∀ (x : X), ∃ e, x ∈ e.baseSet) → IsCoveringMap f
参数：∀ (x : X), ∃ e, x ∈ e.baseSet。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCoveringMap.mk`：mk (F : X -> Type*) [forall x, TopologicalSpace (F x)]
 [forall x, DiscreteTopology (F x)] (e : forall x, Trivialization (F x) f) (h : 
forall…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
protected theorem IsFiberBundle.isCoveringMap {F : Type*} [TopologicalSpace F] [DiscreteTopology F]
    (hf : ∀ x : X, ∃ e : Trivialization F f, x ∈ e.baseSet) : IsCoveringMap f :=
  IsCoveringMap.mk f (fun _ => F) (fun x => Classical.choose (hf x)) fun x =>
    Classical.choose_spec (hf x)
/-
**FiberBundle.isCoveringMap** 是 Mathlib 中的一个定理，位于命名空间 `FiberBundle`。
形式化陈述：∀ {X : Type u_2} [inst : TopologicalSpace X] {F : Type u_3} {E : X → Type 
u_4} [inst_1 : TopologicalSpace F]   [DiscreteTopology F] [inst_3 : TopologicalS
pace (Bundle.TotalSpace F E)] [inst_4 : (x : X) → TopologicalSpace (E x)]   [Fib
erBundle F E], IsCoveringMap Bundle.TotalSpace.proj
参数：Bundle.TotalSpace F E；x : X；E x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsFiberBundle.isCoveringMap`：∀ {E : Type u_1} {X : Type u_2} [inst : Top
ologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X} {F : Type u_3}   [ins
t_2 : Topological…
· 使用定理 `FiberBundle.mem_baseSet_trivializationAt`：mem_baseSet_trivializationAt :
 b in (trivializationAt F E b).baseSet
-/
protected theorem FiberBundle.isCoveringMap {F : Type*} {E : X → Type*} [TopologicalSpace F]
    [DiscreteTopology F] [TopologicalSpace (Bundle.TotalSpace F E)] [∀ x, TopologicalSpace (E x)]
    [FiberBundle F E] : IsCoveringMap (π F E) :=
  IsFiberBundle.isCoveringMap fun x => ⟨trivializationAt F E x, mem_baseSet_trivializationAt F E x⟩

open Function in
/-- Let `f : E → X` be a (not necessarily continuous) map between topological spaces, and let
`V` be an open subset of `X`. Suppose that there is a family `U` of disjoint subsets of `E`
that covers `f⁻¹(V)` such that for every `i`,

1. `f` is injective on `Uᵢ`,
2. `V` is contained in the image `f(Uᵢ)`,
3. the open sets in `V` are determined by their preimages in `Uᵢ`.

Then `f` admits a `Bundle.Trivialization` over the base set `V`. -/
/-
**IsOpen.trivializationDiscrete** 是 Mathlib 中的一个定义，位于命名空间 `IsOpen`。
形式化陈述：{E : Type u_1} →   {X : Type u_2} →     [inst : TopologicalSpace E] →     
  [inst_1 : TopologicalSpace X] →         {f : E → X} →           [Nonempty (X →
 E)] →             {ι : Type u_3} →               [Nonempty ι] →                
 [inst_4 : TopologicalSpace ι] →                   [DiscreteTopology ι] →       
              (U : ι → Set E) →                       (V : Set X) →             
            IsOpen V →                           (∀ (i : ι) {W : Set X}, W ⊆ V →
 (IsOpen W ↔ IsOpen (f ⁻¹' W ∩ U i))) →                             (∀ (i : ι), 
Set.InjOn f (U i)) →                               (∀ (i : ι), Set.SurjOn f (U i
) V) →                                 Pairwise (Function.onFun Disjoint U) → f 
⁻¹' V ⊆ ⋃ i, U i → Bundle.Trivialization ι f
参数：X → E；U : ι → Set E；V : Set X；∀ (i : ι) {W : Set X}, W ⊆ V → (IsOpen W ↔ IsOp
en (f ⁻¹' W ∩ U i))；∀ (i : ι), Set.InjOn f (U i)；∀ (i : ι), Set.SurjOn f (U i) V
；Function.onFun Disjoint U。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `f : E → X` be a (not necessarily continuous) map between topological spaces
, and let
`V` be an open subset of `X`. Suppose that there is a family `U` of disjoint sub
sets of `E`
that covers `f⁻¹(V)` such that for every `i`,

1. `f` is injective on `Uᵢ`,
2. `V` is contained in the image `f(Uᵢ)`,
3. the open sets in `V` are determined by their preimages in `Uᵢ`.

Then `f` admits a `Bundle.Trivialization` over the base set `V`.
-/
@[simps source target baseSet] noncomputable def IsOpen.trivializationDiscrete [Nonempty (X → E)]
    {ι} [Nonempty ι] [TopologicalSpace ι] [DiscreteTopology ι] (U : ι → Set E) (V : Set X)
    (open_V : IsOpen V) (open_iff : ∀ i {W}, W ⊆ V → (IsOpen W ↔ IsOpen (f ⁻¹' W ∩ U i)))
    (inj : ∀ i, (U i).InjOn f) (surj : ∀ i, (U i).SurjOn f V)
    (disjoint : Pairwise (Disjoint on U)) (exhaustive : f ⁻¹' V ⊆ ⋃ i, U i) :
    Trivialization ι f := by
  have exhaustive' := exhaustive
  simp_rw [Set.subset_def, Set.mem_iUnion] at exhaustive
  choose idx idx_U using exhaustive
  choose inv inv_U f_inv using surj
  classical
  let F : PartialEquiv E (X × ι) :=
  { toFun e := (f e, if he : f e ∈ V then idx e he else Classical.arbitrary ι),
    invFun x := if hx : x.1 ∈ V then inv x.2 hx else Classical.arbitrary (X → E) x.1,
    source := f ⁻¹' V,
    target := V ×ˢ Set.univ,
    map_source' x hx := ⟨hx, ⟨⟩⟩
    map_target' x hx := by rw [dif_pos hx.1]; apply (f_inv _ hx.1).symm ▸ hx.1,
    left_inv' e he := by
      simp_rw [dif_pos (id he : f e ∈ V)]
      exact inj _ (inv_U _ he) (idx_U e he) (f_inv _ _)
    right_inv' x hx := by
      rw [dif_pos hx.1]
      refine Prod.ext (f_inv _ hx.1) ?_
      rw [dif_pos ((f_inv _ hx.1).symm ▸ hx.1)]
      by_contra h; exact (disjoint h).le_bot ⟨idx_U .., inv_U _ _⟩ }
  have open_preim {W} (hWV : W ⊆ V) (open_W : IsOpen W) : IsOpen (f ⁻¹' W) := by
    convert! isOpen_iUnion (fun i ↦ (open_iff i hWV).mp open_W)
    rw [← Set.inter_iUnion, eq_comm, Set.inter_eq_left]
    exact (Set.preimage_mono hWV).trans exhaustive'
  have open_source : IsOpen F.source := open_preim subset_rfl open_V
  have cont_f : ContinuousOn f F.source := (continuousOn_open_iff open_source).mpr
    fun W open_W ↦ open_preim Set.inter_subset_left (open_V.inter open_W)
  refine
  { toPartialEquiv := F,
    open_source := open_source,
    open_target := open_V.prod isOpen_univ,
    continuousOn_toFun := cont_f.prodMk <| continuousOn_of_forall_continuousAt fun e he ↦
      continuous_const (y := idx e he) |>.continuousAt.congr <| mem_nhds_iff.mpr
        ⟨U (idx e he) ∩ F.source, fun e' he' ↦ ?_, ?_, idx_U e he, he⟩
    continuousOn_invFun := continuousOn_prod_of_discrete_right.mpr fun i ↦ ?_,
    baseSet := V,
    open_baseSet := open_V,
    source_eq := rfl,
    target_eq := rfl,
    proj_toFun _ _ := rfl }
  · by_contra h; apply (disjoint h).le_bot
    · dsimp only; rw [dif_pos (by exact he'.2)]; exact ⟨he'.1, idx_U ..⟩
  · rwa [Set.inter_comm, ← open_iff _ subset_rfl]
  · simp_rw [F, Set.prodMk_mem_set_prod_eq, Set.mem_univ, and_true]
    refine (continuousOn_open_iff open_V).mpr fun W open_W ↦ ?_
    rw [open_iff i Set.inter_subset_left]
    convert! ((open_iff i subset_rfl).mp open_V).inter open_W using 1
    refine Set.ext fun e ↦ and_right_comm.trans (and_congr_right fun ⟨hV, hU⟩ ↦ ?_)
    rw [Set.mem_preimage, dif_pos hV, inj i (inv_U i _) hU (f_inv i _)]

variable {s}

variable (f) in
/-
**IsDiscrete.of_openPartialHomeomorph** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsDiscrete.of_openPartialHomeomorph {t : Set E} {x : X} (htx : t subseteq 
f ⁻¹' {x}) (hf : forall e in t, exists φ : OpenPartialHomeomorph E X, e in φ.sou
rce ∧ φ = f) : IsDiscrete t
参数：htx : t subseteq f ⁻¹' {x}；hf : forall e in t, exists φ : OpenPartialHomeomor
ph E X, e in φ.source ∧ φ = f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isDiscrete_iff_forall_mem_exists_isOpen`：isDiscrete_iff_forall_mem_exist
s_isOpen {s : Set Y} : IsDiscrete s ↔ forall y in s, exists u, IsOpen u ∧ u inte
r s = {y}
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `OpenPartialHomeomorph.injOn`：∀ {X : Type u_1} {Y : Type u_3} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorph X Y)
, Set.InjOn (↑e) …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
-/
theorem IsDiscrete.of_openPartialHomeomorph {t : Set E} {x : X}
    (htx : t ⊆ f ⁻¹' {x}) (hf : ∀ e ∈ t, ∃ φ : OpenPartialHomeomorph E X, e ∈ φ.source ∧ φ = f) :
    IsDiscrete t :=
  isDiscrete_iff_forall_mem_exists_isOpen.mpr fun e he ↦ by
    obtain ⟨φ, hφ, rfl⟩ := hf e he
    exact ⟨_, φ.open_source, subset_antisymm (fun e' he' ↦ φ.injOn he'.1 hφ <|
      (htx he'.2).trans (htx he).symm) <| Set.singleton_subset_iff.mpr ⟨hφ, he⟩⟩

open Set in
/-- If `f : E → X` is a closed map between topological spaces with `E` Hausdorff, such that the
fiber over a point `x : X` is finite and `f` restricts to a homeomorphism on a neighborhood of
every point of the fiber, then `x` admits an evenly covered neighborhood. -/
/-
**IsClosedMap.isEvenlyCovered_of_openPartialHomeomorph** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：IsClosedMap.isEvenlyCovered_of_openPartialHomeomorph [T2Space E] {x : X} (
hf : IsClosedMap f) (fin : (f ⁻¹' {x}).Finite) (h : forall e in f ⁻¹' {x}, exist
s φ : OpenPartialHomeomorph E X, e in φ.source ∧ φ = f) : IsEvenlyCovered f x (f
 ⁻¹' {x})
参数：hf : IsClosedMap f；fin : (f ⁻¹' {x}).Finite；h : forall e in f ⁻¹' {x}, exists
 φ : OpenPartialHomeomorph E X, e in φ.source ∧ φ = f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDiscrete.to_subtype`：∀ {X : Type u_5} [inst : TopologicalSpace X] {s :
 Set X}, IsDiscrete s → DiscreteTopology ↑s
· 使用定理 `IsDiscrete.of_openPartialHomeomorph`：IsDiscrete.of_openPartialHomeomorph
 {t : Set E} {x : X} (htx : t subseteq f ⁻¹' {x}) (hf : forall e in t, exists φ 
: OpenPartialHomeomorph E…
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
· 使用定理 `Set.Finite.t2_separation`：Set.Finite.t2_separation [T2Space X] {s : Set 
X} (hs : s.Finite) : exists U : X -> Set X, (forall x, x in U x ∧ IsOpen (U x)) 
∧ s.PairwiseDi…
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsOpen.mem_nhdsSet`：IsOpen.mem_nhdsSet (hU : IsOpen s) : s in 𝓝ˢ t ↔ t s
ubseteq s
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `Set.mem_iUnion_of_mem`：mem_iUnion_of_mem {s : ι -> Set α} {a : α} (i : ι
) (ha : a in s i) : a in ⋃ i, s i
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isClosedMap_iff_comap_nhds_le`：∀ {X : Type u_1} {Y : Type u_2} {f : X → 
Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsClosedMap f ↔ 
∀ {y : Y}, Filter.c…
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `IsEvenlyCovered.of_preimage_eq_empty`：of_preimage_eq_empty [IsEmpty I] {
x : X} {U : Set X} (hUx : U in 𝓝 x) (hfU : f ⁻¹' U = ∅) : IsEvenlyCovered f x I
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iUnion_of_empty`：iUnion_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋃ i,
 s i = ∅
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
· 使用定理 `isOpen_iInter_of_finite`：isOpen_iInter_of_finite [Finite ι] {s : ι -> Se
t X} (h : forall i, IsOpen (s i)) : IsOpen (⋂ i, s i)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用引理 `OpenPartialHomeomorph.isOpen_image_of_subset_source`：isOpen_image_of_sub
set_source {s : Set X} (hs : IsOpen s) (hse : s subseteq e.source) : IsOpen (e '
' s)
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.iInter_subset`：iInter_subset : forall (s : ι -> Set β) (i : ι), ⋂ i,
 s i subseteq s i
· 使用定理 `IsEvenlyCovered.of_trivialization`：of_trivialization [DiscreteTopology I
] {x : X} {t : Trivialization I f} (hx : x in t.baseSet) : IsEvenlyCovered f x I
· 使用定理 `Pi.instNonempty`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Nonempty (β
 a)], Nonempty ((a : α) → β a)
（共 51 条，此处仅展示前 30 条）

--- 原说明 ---
If `f : E → X` is a closed map between topological spaces with `E` Hausdorff, su
ch that the
fiber over a point `x : X` is finite and `f` restricts to a homeomorphism on a n
eighborhood of
every point of the fiber, then `x` admits an evenly covered neighborhood.
-/
theorem IsClosedMap.isEvenlyCovered_of_openPartialHomeomorph [T2Space E] {x : X}
    (hf : IsClosedMap f) (fin : (f ⁻¹' {x}).Finite)
    (h : ∀ e ∈ f ⁻¹' {x}, ∃ φ : OpenPartialHomeomorph E X, e ∈ φ.source ∧ φ = f) :
    IsEvenlyCovered f x (f ⁻¹' {x}) := by
  have : DiscreteTopology (f ⁻¹' {x}) :=
    (IsDiscrete.of_openPartialHomeomorph f subset_rfl h).1
  /- for each preimage e of x, choose a homeomorphism φₑ
    from a neighborhood of e to its image -/
  choose φ hφ using fun e : f ⁻¹' {x} ↦ h e e.2
  -- separately, choose pairwise disjoint neighborhoods Vₑ by Hausdorff-ness
  have ⟨V, hV, disj⟩ := fin.t2_separation
  -- let Vₑ' be the intersection Vₑ ∩ dom(φₑ)
  let V' (e : f ⁻¹' {x}) := V e ∩ (φ e).source
  have hV' e : IsOpen (V' e) := (hV e).2.inter (φ e).open_source
  have : ⋃ e, V' e ∈ nhdsSet (f ⁻¹' {x}) :=
    (isOpen_iUnion hV').mem_nhdsSet.2 fun e he ↦ mem_iUnion_of_mem ⟨e, he⟩ ⟨(hV e).1, (hφ _).1⟩
  -- since f is a closed map, the union of the Vₑ' contains the preimage of a neighborhood U of x
  have ⟨W, hWx, hWV⟩ := isClosedMap_iff_comap_nhds_le.mp hf this
  cases isEmpty_or_nonempty (f ⁻¹' {x})
  · exact .of_preimage_eq_empty _ hWx (by simpa using hWV)
  have ⟨U, hUW, hU, hxU⟩ := mem_nhds_iff.mp hWx
  -- show that the intersection of U with the images of Vₑ' is evenly covered
  let U' := U ∩ ⋂ e : f ⁻¹' {x}, f '' (V' e)
  have : Finite (f ⁻¹' {x}) := fin
  have hU' : IsOpen U' := hU.inter <| isOpen_iInter_of_finite fun e ↦ by
    convert! ← (φ e).isOpen_image_of_subset_source (hV' _) inter_subset_right; exact (hφ e).2
  have hUV e : U' ⊆ f '' V' e := inter_subset_right.trans (iInter_subset ..)
  have : Nonempty E := ⟨Classical.arbitrary (f ⁻¹' {x})⟩
  refine .of_trivialization (t := hU'.trivializationDiscrete _ _
    (fun e s hs ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩) (fun e ↦ ?_)
    (fun e ↦ .mono subset_rfl (hUV e) (surjOn_image f _))
    (pairwise_disjoint_mono disj.subtype fun e ↦ inter_subset_left)
    ((preimage_mono (inter_subset_left.trans hUW)).trans hWV))
    ⟨hxU, Set.mem_iInter.mpr fun e ↦ ⟨e, ⟨(hV e).1, (hφ e).1⟩, e.2⟩⟩
  · convert! ((φ e).isOpen_inter_preimage h).inter (hV e).2 using 1
    simp_rw [(hφ e).2, V']; ac_rfl
  · have : s ⊆ (φ e).target := hs.trans <| (hUV e).trans <| by
      rw [← (φ e).image_source_eq_target, (hφ e).2]; exact image_mono inter_subset_right
    rw [← (φ e).isOpen_symm_image_iff_of_subset_target this,
      (φ e).symm_image_eq_source_inter_preimage this, (hφ e).2, inter_comm]
    convert! h using 1
    refine inter_eq_inter_iff_left.mpr ⟨fun e' h ↦ h.2.2, fun e' h ↦ ⟨?_ , h.2⟩⟩
    have ⟨e'', ⟨_, mem⟩, eq⟩ := mem_iInter.mp (hs h.1).2 e
    rwa [← (φ e).injOn mem h.2 (by rwa [(hφ e).2])]
  · convert! ← (φ e).injOn.mono inter_subset_right; exact (hφ e).2

/-- If `f : E → X` is a closed map between topological spaces with `E` Hausdorff, and `s` is
a subset of `X` on which `f` has finite fibers, such that `f` restricts to a homeomorphism on
a neighborhood of every point of `f ⁻¹' s`, then `f` is a covering map on `s`. -/
/-
**IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn [T2Space E] (hf : IsClo
sedMap f) (hs : forall x in s, (f ⁻¹' {x}).Finite) (h : IsLocalHomeomorphOn f (f
 ⁻¹' s)) : IsCoveringMapOn f s
参数：hf : IsClosedMap f；hs : forall x in s, (f ⁻¹' {x}).Finite；h : IsLocalHomeomor
phOn f (f ⁻¹' s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosedMap.isEvenlyCovered_of_openPartialHomeomorph`：IsClosedMap.isEven
lyCovered_of_openPartialHomeomorph [T2Space E] {x : X} (hf : IsClosedMap f) (fin
 : (f ⁻¹' {x}).Finite) (h : forall e in f …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `f : E → X` is a closed map between topological spaces with `E` Hausdorff, an
d `s` is
a subset of `X` on which `f` has finite fibers, such that `f` restricts to a hom
eomorphism on
a neighborhood of every point of `f ⁻¹' s`, then `f` is a covering map on `s`.
-/
theorem IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn [T2Space E]
    (hf : IsClosedMap f) (hs : ∀ x ∈ s, (f ⁻¹' {x}).Finite)
    (h : IsLocalHomeomorphOn f (f ⁻¹' s)) :
    IsCoveringMapOn f s := by
  intro x hx
  refine hf.isEvenlyCovered_of_openPartialHomeomorph (hs x hx) fun e he ↦ ?_
  obtain ⟨φ, hφ, rfl⟩ := h e (by aesop)
  aesop

@[deprecated (since := "2026-06-25")]
alias IsClosedMap.isCoveringMapOn_of_openPartialHomeomorph :=
  IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn

/-- If `f : E → X` is a continuous map between Hausdorff spaces with `E` compact,
and `f` restricts to a homeomorphism on a neighborhood of every point of a fiber `f ⁻¹' {x}`,
then `x` admits an evenly covered neighborhood. -/
/-
**IsEvenlyCovered.of_openPartialHomeomorph** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsEvenlyCovered.of_openPartialHomeomorph [T2Space E] [T2Space X] [CompactS
pace E] {x : X} (hf : Continuous f) (h : forall e in f ⁻¹' {x}, exists φ : OpenP
artialHomeomorph E X, e in φ.source ∧ φ = f) : IsEvenlyCovered f x (f ⁻¹' {x})
参数：hf : Continuous f；h : forall e in f ⁻¹' {x}, exists φ : OpenPartialHomeomorph
 E X, e in φ.source ∧ φ = f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosedMap.isEvenlyCovered_of_openPartialHomeomorph`：IsClosedMap.isEven
lyCovered_of_openPartialHomeomorph [T2Space E] {x : X} (hf : IsClosedMap f) (fin
 : (f ⁻¹' {x}).Finite) (h : forall e in f …
· 使用定理 `Continuous.isClosedMap`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] [CompactSpace X] [T2Space Y]   {f : X 
→ Y}, Contin…
· 使用定理 `IsCompact.finite`：IsCompact.finite (hs : IsCompact s) (hs' : IsDiscrete 
s) : s.Finite
· 使用定理 `IsClosed.isCompact`：IsClosed.isCompact [CompactSpace X] (h : IsClosed s)
 : IsCompact s
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `IsDiscrete.of_openPartialHomeomorph`：IsDiscrete.of_openPartialHomeomorph
 {t : Set E} {x : X} (htx : t subseteq f ⁻¹' {x}) (hf : forall e in t, exists φ 
: OpenPartialHomeomorph E…
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a

--- 原说明 ---
If `f : E → X` is a continuous map between Hausdorff spaces with `E` compact,
and `f` restricts to a homeomorphism on a neighborhood of every point of a fiber
 `f ⁻¹' {x}`,
then `x` admits an evenly covered neighborhood.
-/
theorem IsEvenlyCovered.of_openPartialHomeomorph
    [T2Space E] [T2Space X] [CompactSpace E] {x : X} (hf : Continuous f)
    (h : ∀ e ∈ f ⁻¹' {x}, ∃ φ : OpenPartialHomeomorph E X, e ∈ φ.source ∧ φ = f) :
    IsEvenlyCovered f x (f ⁻¹' {x}) :=
  hf.isClosedMap.isEvenlyCovered_of_openPartialHomeomorph
    ((isClosed_singleton.preimage hf).isCompact.finite (.of_openPartialHomeomorph f subset_rfl h)) h

/-- If `f : E → X` is a continuous map between Hausdorff spaces with `E` compact, `s` is a subset
of `X` such that `f` restricts to a homeomorphism on a neighborhood of every point of `f ⁻¹' s`,
then `f` is a covering map on `s`.

For example, `s` can be taken to be the set of regular values of a C¹ map `f : E → X`
where `E` and `X` are manifolds of the same dimension with `E` compact, according to
the inverse function theorem (see `ContDiffAt.toOpenPartialHomeomorph`). -/
/-
**IsCoveringMapOn.of_isLocalHomeomorphOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoveringMapOn.of_isLocalHomeomorphOn [T2Space E] [T2Space X] [CompactSpa
ce E] (hf : Continuous f) (h : IsLocalHomeomorphOn f (f ⁻¹' s)) : IsCoveringMapO
n f s
参数：hf : Continuous f；h : IsLocalHomeomorphOn f (f ⁻¹' s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsEvenlyCovered.of_openPartialHomeomorph`：IsEvenlyCovered.of_openPartial
Homeomorph [T2Space E] [T2Space X] [CompactSpace E] {x : X} (hf : Continuous f) 
(h : forall e in f ⁻¹' {x}, ex…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `f : E → X` is a continuous map between Hausdorff spaces with `E` compact, `s
` is a subset
of `X` such that `f` restricts to a homeomorphism on a neighborhood of every poi
nt of `f ⁻¹' s`,
then `f` is a covering map on `s`.

For example, `s` can be taken to be the set of regular values of a C¹ map `f : E
 → X`
where `E` and `X` are manifolds of the same dimension with `E` compact, accordin
g to
the inverse function theorem (see `ContDiffAt.toOpenPartialHomeomorph`).
-/
theorem IsCoveringMapOn.of_isLocalHomeomorphOn
    [T2Space E] [T2Space X] [CompactSpace E] (hf : Continuous f)
    (h : IsLocalHomeomorphOn f (f ⁻¹' s)) :
    IsCoveringMapOn f s := by
  intro x hx
  refine .of_openPartialHomeomorph hf fun e he ↦ ?_
  obtain ⟨φ, hφ, rfl⟩ := h e (by aesop)
  aesop

@[deprecated (since := "2026-06-25")]
alias IsCoveringMapOn.of_openPartialHomeomorph := IsCoveringMapOn.of_isLocalHomeomorphOn

@[simp]
/-
**isLocalHomeomorph_iff_isCoveringMap** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isLocalHomeomorph_iff_isCoveringMap [T2Space E] [T2Space X] [CompactSpace 
E] : IsLocalHomeomorph f ↔ IsCoveringMap f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `OpenPartialHomeomorph.continuousAt`：∀ {X : Type u_1} {Y : Type u_3} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomor
ph X Y) {x : X}, x ∈ e.s…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isCoveringMap_iff_isCoveringMapOn_univ`：isCoveringMap_iff_isCoveringMapO
n_univ : IsCoveringMap f ↔ IsCoveringMapOn f .univ
· 使用定理 `IsCoveringMapOn.of_isLocalHomeomorphOn`：IsCoveringMapOn.of_isLocalHomeom
orphOn [T2Space E] [T2Space X] [CompactSpace E] (hf : Continuous f) (h : IsLocal
HomeomorphOn f (f ⁻¹' s)) : …
· 使用定理 `IsCoveringMap.isLocalHomeomorph`：∀ {E : Type u_1} {X : Type u_2} [inst :
 TopologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X},   IsCoveringMap 
f → IsLocalHomeomorph…
-/
lemma isLocalHomeomorph_iff_isCoveringMap [T2Space E] [T2Space X] [CompactSpace E] :
    IsLocalHomeomorph f ↔ IsCoveringMap f := by
  refine ⟨fun h ↦ ?_, IsCoveringMap.isLocalHomeomorph⟩
  have hf : Continuous f := by
    rw [continuous_iff_continuousAt]
    intro e
    obtain ⟨φ, hφ, rfl⟩ := h e
    exact φ.continuousAt hφ
  rw [isCoveringMap_iff_isCoveringMapOn_univ]
  apply IsCoveringMapOn.of_isLocalHomeomorphOn hf
  simpa [← isLocalHomeomorph_iff_isLocalHomeomorphOn_univ]
