/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Covering.Basic

/-!
# Covering maps to quotients by free and properly discontinuous group actions
-/

@[expose] public section

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] (f : E → X)
variable (G : Type*) [Group G] [MulAction G E]

open Topology

/-- A function from a topological space `E` with an action by a discrete group to another
topological space `X` is a quotient covering map if it is a quotient map, the action is
continuous and transitive on fibers, and every point of `E` has a neighborhood whose translates
by the group elements are pairwise disjoint. -/
/-
**IsAddQuotientCoveringMap** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{E : Type u_1} →   {X : Type u_2} →     [TopologicalSpace E] →       [Topo
logicalSpace X] → (E → X) → (G : Type u_4) → [inst : AddGroup G] → [AddAction G 
E] → Prop
参数：E → X；G : Type u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function from a topological space `E` with an action by a discrete group to an
other
topological space `X` is a quotient covering map if it is a quotient map, the ac
tion is
continuous and transitive on fibers, and every point of `E` has a neighborhood w
hose translates
by the group elements are pairwise disjoint.
-/
structure IsAddQuotientCoveringMap (G) [AddGroup G] [AddAction G E] : Prop
    extends IsQuotientMap f, ContinuousConstVAdd G E where
  apply_eq_iff_mem_orbit {e₁ e₂} : f e₁ = f e₂ ↔ e₁ ∈ AddAction.orbit G e₂
  disjoint (e : E) : ∃ U ∈ 𝓝 e, ∀ g : G, ((g +ᵥ ·) '' U ∩ U).Nonempty → g = 0

/-- A function from a topological space `E` with an action by a discrete group to another
topological space `X` is a quotient covering map if it is a quotient map, the action is
continuous and transitive on fibers, and every point of `E` has a neighborhood whose translates
by the group elements are pairwise disjoint. -/
@[mk_iff, to_additive]
/-
**IsQuotientCoveringMap** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{E : Type u_1} →   {X : Type u_2} →     [TopologicalSpace E] → [Topologica
lSpace X] → (E → X) → (G : Type u_3) → [inst : Group G] → [MulAction G E] → Prop
参数：E → X；G : Type u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function from a topological space `E` with an action by a discrete group to an
other
topological space `X` is a quotient covering map if it is a quotient map, the ac
tion is
continuous and transitive on fibers, and every point of `E` has a neighborhood w
hose translates
by the group elements are pairwise disjoint.
-/
structure IsQuotientCoveringMap : Prop extends IsQuotientMap f, ContinuousConstSMul G E where
  apply_eq_iff_mem_orbit {e₁ e₂} : f e₁ = f e₂ ↔ e₁ ∈ MulAction.orbit G e₂
  disjoint (e : E) : ∃ U ∈ 𝓝 e, ∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g = 1

attribute [to_additive] isQuotientCoveringMap_iff
/-
**IsAddQuotientCoveringMap.toMultiplicative** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsAddQuotientCoveringMap.toMultiplicative (G) [AddGroup G] [AddAction G E]
 (hf : IsAddQuotientCoveringMap f G) : IsQuotientCoveringMap f (Multiplicative G
) where __
参数：G；hf : IsAddQuotientCoveringMap f G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAddQuotientCoveringMap.toIsQuotientMap`：∀ {E : Type u_1} {X : Type u_2
} [inst : TopologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X} {G : Typ
e u_4}   [inst_2 : AddGroup G]…
· 使用定理 `ContinuousConstVAdd.continuous_const_vadd`：∀ {Γ : Type u_1} {T : Type u_
2} {inst : TopologicalSpace T} {inst_1 : VAdd Γ T} [self : ContinuousConstVAdd Γ
 T]   (γ : Γ), Continuous fun x…
· 使用定理 `IsAddQuotientCoveringMap.toContinuousConstVAdd`：∀ {E : Type u_1} {X : Ty
pe u_2} [inst : TopologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X} {G
 : Type u_4}   [inst_2 : AddGroup G]…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsAddQuotientCoveringMap.apply_eq_iff_mem_orbit`：∀ {E : Type u_1} {X : T
ype u_2} [inst : TopologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X} {
G : Type u_4}   [inst_2 : AddGroup G]…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `IsAddQuotientCoveringMap.disjoint`：∀ {E : Type u_1} {X : Type u_2} [inst
 : TopologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X} {G : Type u_4} 
  [inst_2 : AddGroup G]…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
-/
lemma IsAddQuotientCoveringMap.toMultiplicative (G) [AddGroup G] [AddAction G E]
    (hf : IsAddQuotientCoveringMap f G) :
    IsQuotientCoveringMap f (Multiplicative G) where
  __ := hf.toIsQuotientMap
  continuous_const_smul g := by simpa using hf.continuous_const_vadd (Multiplicative.ofAdd.symm g)
  apply_eq_iff_mem_orbit {e₁ e₂} := by simp [hf.apply_eq_iff_mem_orbit]
  disjoint e := by
    obtain ⟨U, hU, hU'⟩ := hf.disjoint e
    exact ⟨U, hU, fun g ↦ by simpa using hU' (Multiplicative.ofAdd.symm g)⟩
/-
**IsQuotientCoveringMap.toAdditive** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsQuotientCoveringMap.toAdditive (G) [Group G] [MulAction G E] (hf : IsQuo
tientCoveringMap f G) : IsAddQuotientCoveringMap f (Additive G) where __
参数：G；hf : IsQuotientCoveringMap f G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsQuotientCoveringMap.toIsQuotientMap`：∀ {E : Type u_1} {X : Type u_2} [
inst : TopologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X} {G : Type u
_3}   [inst_2 : Group G] [i…
· 使用定理 `ContinuousConstSMul.continuous_const_smul`：∀ {Γ : Type u_1} {T : Type u_
2} {inst : TopologicalSpace T} {inst_1 : SMul Γ T} [self : ContinuousConstSMul Γ
 T]   (γ : Γ), Continuous fun x…
· 使用定理 `IsQuotientCoveringMap.toContinuousConstSMul`：∀ {E : Type u_1} {X : Type 
u_2} [inst : TopologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X} {G : 
Type u_3}   [inst_2 : Group G] [i…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsQuotientCoveringMap.apply_eq_iff_mem_orbit`：∀ {E : Type u_1} {X : Type
 u_2} [inst : TopologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X} {G :
 Type u_3}   [inst_2 : Group G] [i…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `IsQuotientCoveringMap.disjoint`：∀ {E : Type u_1} {X : Type u_2} [inst : 
TopologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X} {G : Type u_3}   [
inst_2 : Group G] [i…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
-/
lemma IsQuotientCoveringMap.toAdditive (G) [Group G] [MulAction G E]
    (hf : IsQuotientCoveringMap f G) :
    IsAddQuotientCoveringMap f (Additive G) where
  __ := hf.toIsQuotientMap
  continuous_const_vadd g := by simpa using hf.continuous_const_smul (Additive.ofMul.symm g)
  apply_eq_iff_mem_orbit {e₁ e₂} := by simp [hf.apply_eq_iff_mem_orbit]
  disjoint e := by
    obtain ⟨U, hU, hU'⟩ := hf.disjoint e
    exact ⟨U, hU, fun g ↦ by simpa using hU' (Additive.ofMul.symm g)⟩

namespace IsQuotientCoveringMap

/-
**IsQuotientCoveringMap.subgroup_congr** 是 Mathlib 中的一个定理，位于命名空间 `IsQuotientCove
ringMap`。
形式化陈述：∀ {E : Type u_1} {X : Type u_2} [inst : TopologicalSpace E] [inst_1 : Topo
logicalSpace X] (f : E → X) (G : Type u_3)   [inst_2 : Group G] [inst_3 : MulAct
ion G E] (S S' : Subgroup G),   S = S' → (IsQuotientCoveringMap f ↥S ↔ IsQuotien
tCoveringMap f ↥S')
参数：f : E → X；G : Type u_3；S S' : Subgroup G；IsQuotientCoveringMap f ↥S ↔ IsQuoti
entCoveringMap f ↥S'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[to_additive] theorem subgroup_congr (S S' : Subgroup G) (eq : S = S') :
    IsQuotientCoveringMap f S ↔ IsQuotientCoveringMap f S' := by rw [eq]

variable {f G} (hf : IsQuotientCoveringMap f G)
include hf
/-
**IsQuotientCoveringMap.map_smul** 是 Mathlib 中的一个定理，位于命名空间 `IsQuotientCoveringMa
p`。
形式化陈述：∀ {E : Type u_1} {X : Type u_2} [inst : TopologicalSpace E] [inst_1 : Topo
logicalSpace X] {f : E → X} {G : Type u_3}   [inst_2 : Group G] [inst_3 : MulAct
ion G E], IsQuotientCoveringMap f G → ∀ (g : G) {e : E}, f (g • e) = f e
参数：g : G；g • e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsQuotientCoveringMap.apply_eq_iff_mem_orbit`：∀ {E : Type u_1} {X : Type
 u_2} [inst : TopologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X} {G :
 Type u_3}   [inst_2 : Group G] [i…
-/
@[to_additive] protected theorem map_smul (g : G) {e : E} : f (g • e) = f e :=
  hf.apply_eq_iff_mem_orbit.mpr ⟨g, rfl⟩

/-- The group action on the domain of a quotient covering map is free. -/
/-
**IsQuotientCoveringMap.isCancelSMul** 是 Mathlib 中的一个定理，位于命名空间 `IsQuotientCoveri
ngMap`。
形式化陈述：∀ {E : Type u_1} {X : Type u_2} [inst : TopologicalSpace E] [inst_1 : Topo
logicalSpace X] {f : E → X} {G : Type u_3}   [inst_2 : Group G] [inst_3 : MulAct
ion G E], IsQuotientCoveringMap f G → IsCancelSMul G E
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsLeftCancelSMul`：∀ (G : Type u_9) (P : Type u_10) [inst : Group G] 
[inst_1 : MulAction G P], IsLeftCancelSMul G P
· 使用定理 `IsQuotientCoveringMap.disjoint`：∀ {E : Type u_1} {X : Type u_2} [inst : 
TopologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X} {G : Type u_3}   [
inst_2 : Group G] [i…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b

--- 原说明 ---
The group action on the domain of a quotient covering map is free.
-/
@[to_additive] theorem isCancelSMul : IsCancelSMul G E where
  right_cancel' g g' e eq := by
    have ⟨U, heU, hU⟩ := hf.disjoint e
    simpa [inv_mul_eq_one, eq_comm] using hU (g'⁻¹ * g)
      ⟨e, ⟨e, mem_of_mem_nhds heU, by simpa [mul_smul, inv_smul_eq_iff]⟩, mem_of_mem_nhds heU⟩
/-
**IsQuotientCoveringMap.homeomorph_comp** 是 Mathlib 中的一个定理，位于命名空间 `IsQuotientCov
eringMap`。
形式化陈述：∀ {E : Type u_1} {X : Type u_2} [inst : TopologicalSpace E] [inst_1 : Topo
logicalSpace X] {f : E → X} {G : Type u_3}   [inst_2 : Group G] [inst_3 : MulAct
ion G E],   IsQuotientCoveringMap f G →     ∀ {Y : Type u_4} [inst_4 : Topologic
alSpace Y] (φ : X ≃ₜ Y), IsQuotientCoveringMap (⇑φ ∘ f) G
参数：φ : X ≃ₜ Y；⇑φ ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsQuotientMap.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u
_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalS
pace Y] [inst_2 :…
· 使用定理 `Homeomorph.isQuotientMap`：isQuotientMap (h : X ≃ₜ Y) : IsQuotientMap h
· 使用定理 `IsQuotientCoveringMap.toIsQuotientMap`：∀ {E : Type u_1} {X : Type u_2} [
inst : TopologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X} {G : Type u
_3}   [inst_2 : Group G] [i…
· 使用定理 `IsQuotientCoveringMap.toContinuousConstSMul`：∀ {E : Type u_1} {X : Type 
u_2} [inst : TopologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X} {G : 
Type u_3}   [inst_2 : Group G] [i…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `IsQuotientCoveringMap.apply_eq_iff_mem_orbit`：∀ {E : Type u_1} {X : Type
 u_2} [inst : TopologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X} {G :
 Type u_3}   [inst_2 : Group G] [i…
· 使用定理 `IsQuotientCoveringMap.disjoint`：∀ {E : Type u_1} {X : Type u_2} [inst : 
TopologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X} {G : Type u_3}   [
inst_2 : Group G] [i…
-/
@[to_additive] theorem homeomorph_comp {Y} [TopologicalSpace Y]
    (φ : X ≃ₜ Y) : IsQuotientCoveringMap (φ ∘ f) G where
  __ := φ.isQuotientMap.comp hf.toIsQuotientMap
  continuous_const_smul := hf.continuous_const_smul
  apply_eq_iff_mem_orbit := by simpa using @hf.apply_eq_iff_mem_orbit
  disjoint := hf.disjoint

omit hf in
/-
**IsQuotientCoveringMap.homeomorph_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsQuotien
tCoveringMap`。
形式化陈述：∀ {E : Type u_1} {X : Type u_2} [inst : TopologicalSpace E] [inst_1 : Topo
logicalSpace X] {f : E → X} {G : Type u_3}   [inst_2 : Group G] [inst_3 : MulAct
ion G E] {Y : Type u_4} [inst_4 : TopologicalSpace Y] (φ : X ≃ₜ Y),   IsQuotient
CoveringMap (⇑φ ∘ f) G ↔ IsQuotientCoveringMap f G
参数：φ : X ≃ₜ Y；⇑φ ∘ f。
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
· 使用定理 `IsQuotientCoveringMap.homeomorph_comp`：∀ {E : Type u_1} {X : Type u_2} [
inst : TopologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X} {G : Type u
_3}   [inst_2 : Group G] [i…
-/
@[to_additive (attr := simp)] theorem homeomorph_comp_iff {Y} [TopologicalSpace Y]
    (φ : X ≃ₜ Y) : IsQuotientCoveringMap (φ ∘ f) G ↔ IsQuotientCoveringMap f G where
  mp h := by convert! h.homeomorph_comp φ.symm; ext; simp
  mpr h := h.homeomorph_comp φ

/-- Fibers of a quotient covering map by a group G is a G-torsor. -/
@[to_additive /-- Fibers of a quotient covering map by an additive group G is a G-torsor. -/]
/-
**IsQuotientCoveringMap.fiberEquivGroup** 是 Mathlib 中的一个定义，位于命名空间 `IsQuotientCov
eringMap`。
形式化陈述：fiberEquivGroup {x : X} (e : f ⁻¹' {x}) : f ⁻¹' {x} ≃ G
参数：e : f ⁻¹' {x}。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsQuotientCoveringMap.isCancelSMul`：∀ {E : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X} {G : Type u_3}
   [inst_2 : Group G] [i…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Fibers of a quotient covering map by a group G is a G-torsor.
-/
noncomputable def fiberEquivGroup {x : X} (e : f ⁻¹' {x}) : f ⁻¹' {x} ≃ G :=
  have := hf.isCancelSMul
  .symm <| .ofBijective (fun g ↦ ⟨g • e, (hf.map_smul g).trans e.2⟩)
    ⟨fun _ _ eq ↦ IsCancelSMul.right_cancel _ _ e.1 congr($eq), fun e' ↦
      have ⟨g, eq⟩ := hf.apply_eq_iff_mem_orbit.mp (e'.2.trans e.2.symm); ⟨g, Subtype.ext eq⟩⟩
/-
**IsQuotientCoveringMap.fiberEquivGroup_self** 是 Mathlib 中的一个定理，位于命名空间 `IsQuotie
ntCoveringMap`。
形式化陈述：∀ {E : Type u_1} {X : Type u_2} [inst : TopologicalSpace E] [inst_1 : Topo
logicalSpace X] {f : E → X} {G : Type u_3}   [inst_2 : Group G] [inst_3 : MulAct
ion G E] (hf : IsQuotientCoveringMap f G) {x : X} (e : ↑(f ⁻¹' {x})),   (hf.fibe
rEquivGroup e) e = 1
参数：hf : IsQuotientCoveringMap f G；e : ↑(f ⁻¹' {x})；hf.fiberEquivGroup e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
@[simp] theorem fiberEquivGroup_self {x : X} (e : f ⁻¹' {x}) : hf.fiberEquivGroup e e = 1 :=
  (Equiv.eq_symm_apply _).mp <| Subtype.ext (one_smul ..).symm

set_option backward.isDefEq.respectTransparency.types false in
/-
**IsQuotientCoveringMap.fiberEquivGroup_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsQuot
ientCoveringMap`。
形式化陈述：∀ {E : Type u_1} {X : Type u_2} [inst : TopologicalSpace E] [inst_1 : Topo
logicalSpace X] {f : E → X} {G : Type u_3}   [inst_2 : Group G] [inst_3 : MulAct
ion G E] (hf : IsQuotientCoveringMap f G) {x : X} (e e' : ↑(f ⁻¹' {x})) (g : G),
   (hf.fiberEquivGroup e) e' = g ↔ ↑e' = g • ↑e
参数：hf : IsQuotientCoveringMap f G；e e' : ↑(f ⁻¹' {x})；g : G；hf.fiberEquivGroup e
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `IsQuotientCoveringMap.isCancelSMul`：∀ {E : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X} {G : Type u_3}
   [inst_2 : Group G] [i…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsQuotientCoveringMap.fiberEquivGroup.eq_1`：∀ {E : Type u_1} {X : Type u
_2} [inst : TopologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X} {G : T
ype u_3}   [inst_2 : Group G] [i…
· 使用定理 `Equiv.symm_apply_eq`：symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = 
y ↔ x = e y
· 使用定理 `Equiv.ofBijective_apply`：∀ {α : Sort u} {β : Sort v} (f : α → β) (hf : F
unction.Bijective f) (a : α), (Equiv.ofBijective f hf) a = f a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem fiberEquivGroup_eq_iff {x : X} (e e' : f ⁻¹' {x}) (g : G) :
    hf.fiberEquivGroup e e' = g ↔ e' = g • (e : E) := by
  rw [fiberEquivGroup, Equiv.symm_apply_eq, Equiv.ofBijective_apply, Subtype.mk.injEq]
/-
**IsQuotientCoveringMap.fiberEquivGroup_smul_self** 是 Mathlib 中的一个定理，位于命名空间 `IsQ
uotientCoveringMap`。
形式化陈述：∀ {E : Type u_1} {X : Type u_2} [inst : TopologicalSpace E] [inst_1 : Topo
logicalSpace X] {f : E → X} {G : Type u_3}   [inst_2 : Group G] [inst_3 : MulAct
ion G E] (hf : IsQuotientCoveringMap f G) {x : X} (e : ↑(f ⁻¹' {x}))   {e' : ↑(f
 ⁻¹' {x})}, (hf.fiberEquivGroup e) e' • ↑e = ↑e'
参数：hf : IsQuotientCoveringMap f G；e : ↑(f ⁻¹' {x})；f ⁻¹' {x}；hf.fiberEquivGroup 
e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
@[simp] theorem fiberEquivGroup_smul_self {x : X} (e : f ⁻¹' {x}) {e' : f ⁻¹' {x}} :
    hf.fiberEquivGroup e e' • (e : E) = (e' : E) :=
  congr($((hf.fiberEquivGroup e).symm_apply_apply e'))

/-- The action of `G` restricted to the fiber. -/
/-
**IsQuotientCoveringMap.mulActionFiber** 是 Mathlib 中的一个定义，位于命名空间 `IsQuotientCove
ringMap`。
形式化陈述：{E : Type u_1} →   {X : Type u_2} →     [inst : TopologicalSpace E] →     
  [inst_1 : TopologicalSpace X] →         {f : E → X} →           {G : Type u_3}
 →             [inst_2 : Group G] →               [inst_3 : MulAction G E] → IsQ
uotientCoveringMap f G → (x : X) → MulAction G ↑(f ⁻¹' {x})
参数：x : X；f ⁻¹' {x}。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action of `G` restricted to the fiber.
-/
@[implicit_reducible] def mulActionFiber (x : X) : MulAction G (f ⁻¹' {x}) :=
  SubMulAction.mulAction ⟨f ⁻¹' {x}, fun g _ h ↦ (hf.map_smul g).trans h⟩
/-
**IsQuotientCoveringMap.coe_mulActionFiber_smul** 是 Mathlib 中的一个定理，位于命名空间 `IsQuo
tientCoveringMap`。
形式化陈述：∀ {E : Type u_1} {X : Type u_2} [inst : TopologicalSpace E] [inst_1 : Topo
logicalSpace X] {f : E → X} {G : Type u_3}   [inst_2 : Group G] [inst_3 : MulAct
ion G E] (hf : IsQuotientCoveringMap f G) (x : X) (g : G) (e : ↑(f ⁻¹' {x})),   
↑(g • e) = g • ↑e
参数：hf : IsQuotientCoveringMap f G；x : X；g : G；e : ↑(f ⁻¹' {x})；g • e。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_mulActionFiber_smul (x : X) (g : G) (e : f ⁻¹' {x}) :
    letI := hf.mulActionFiber x
    (↑(g • e) : E) = g • (e : E) :=
  rfl
/-
**IsQuotientCoveringMap.mulActionFiber_isPretransitive** 是 Mathlib 中的一个引理，位于命名空间
 `IsQuotientCoveringMap`。
形式化陈述：mulActionFiber_isPretransitive (x : X) : letI
参数：x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsQuotientCoveringMap.apply_eq_iff_mem_orbit`：∀ {E : Type u_1} {X : Type
 u_2} [inst : TopologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X} {G :
 Type u_3}   [inst_2 : Group G] [i…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
lemma mulActionFiber_isPretransitive (x : X) :
    letI := hf.mulActionFiber x
    MulAction.IsPretransitive G (f ⁻¹' {x}) := by
  let := hf.mulActionFiber x
  constructor
  intro e e'
  obtain ⟨g, hg⟩ := hf.apply_eq_iff_mem_orbit.mp (e'.2.trans e.2.symm)
  exact ⟨g, Subtype.ext hg⟩

/-- A quotient covering map `f` induces a permutation action on each fiber. -/
/-
**IsQuotientCoveringMap.toPermFiber** 是 Mathlib 中的一个定义，位于命名空间 `IsQuotientCoverin
gMap`。
形式化陈述：{E : Type u_1} →   {X : Type u_2} →     [inst : TopologicalSpace E] →     
  [inst_1 : TopologicalSpace X] →         {f : E → X} →           {G : Type u_3}
 →             [inst_2 : Group G] →               [inst_3 : MulAction G E] → IsQ
uotientCoveringMap f G → (x : X) → G →* Equiv.Perm ↑(f ⁻¹' {x})
参数：x : X；f ⁻¹' {x}。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A quotient covering map `f` induces a permutation action on each fiber.
-/
@[simps!] def toPermFiber (x : X) : G →* Equiv.Perm (f ⁻¹' {x}) :=
  (hf.mulActionFiber x).toPermHom
/-
**IsQuotientCoveringMap.toPermFiber_ext** 是 Mathlib 中的一个定理，位于命名空间 `IsQuotientCov
eringMap`。
形式化陈述：toPermFiber_ext (x : X) (e : f ⁻¹' {x}) {g g' : G} (eq : hf.toPermFiber x 
g e = hf.toPermFiber x g' e) : g = g'
参数：x : X；e : f ⁻¹' {x}；eq : hf.toPermFiber x g e = hf.toPermFiber x g' e。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsQuotientCoveringMap.isCancelSMul`：∀ {E : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X} {G : Type u_3}
   [inst_2 : Group G] [i…
· 使用引理 `IsCancelSMul.right_cancel`：IsCancelSMul.right_cancel {G P} [SMul G P] [I
sCancelSMul G P] (a b : G) (c : P) : a • c = b • c -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem toPermFiber_ext (x : X) (e : f ⁻¹' {x}) {g g' : G}
    (eq : hf.toPermFiber x g e = hf.toPermFiber x g' e) : g = g' :=
  have := hf.isCancelSMul
  IsCancelSMul.right_cancel _ _ e.1 congr($eq)
/-
**IsQuotientCoveringMap.toPermFiber_injective** 是 Mathlib 中的一个定理，位于命名空间 `IsQuoti
entCoveringMap`。
形式化陈述：toPermFiber_injective (x : X) : Function.Injective (hf.toPermFiber x)
参数：x : X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsQuotientMap.surjective`：∀ {X : Type u_3} {Y : Type u_4} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topology.IsQ
uotientMap f → Function…
· 使用定理 `IsQuotientCoveringMap.toIsQuotientMap`：∀ {E : Type u_1} {X : Type u_2} [
inst : TopologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X} {G : Type u
_3}   [inst_2 : Group G] [i…
· 使用定理 `IsQuotientCoveringMap.toPermFiber_ext`：toPermFiber_ext (x : X) (e : f ⁻¹
' {x}) {g g' : G} (eq : hf.toPermFiber x g e = hf.toPermFiber x g' e) : g = g'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem toPermFiber_injective (x : X) : Function.Injective (hf.toPermFiber x) :=
  have ⟨e, he⟩ := hf.surjective x
  fun _ _ eq ↦ hf.toPermFiber_ext x ⟨e, he⟩ congr($eq _)
/-
**IsQuotientCoveringMap.exists_toPermFiber_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsQuoti
entCoveringMap`。
形式化陈述：exists_toPermFiber_eq {x : X} (e e' : f ⁻¹' {x}) : exists g, hf.toPermFibe
r x g e = e'
参数：e e' : f ⁻¹' {x}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsQuotientCoveringMap.mulActionFiber_isPretransitive`：mulActionFiber_isP
retransitive (x : X) : letI
· 使用定理 `MulAction.IsPretransitive.exists_smul_eq`：∀ {M : Type u_5} {α : Type u_6
} {inst : SMul M α} [self : MulAction.IsPretransitive M α] (x y : α), ∃ g, g • x
 = y
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsQuotientCoveringMap.toPermFiber_apply_apply_coe`：∀ {E : Type u_1} {X :
 Type u_2} [inst : TopologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X}
 {G : Type u_3}   [inst_2 : Group G] [i…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem exists_toPermFiber_eq {x : X} (e e' : f ⁻¹' {x}) : ∃ g, hf.toPermFiber x g e = e' := by
  let := hf.mulActionFiber x
  have := hf.mulActionFiber_isPretransitive x
  obtain ⟨g, rfl⟩ := MulAction.IsPretransitive.exists_smul_eq e e' (M := G)
  use g
  ext
  simp

end IsQuotientCoveringMap

namespace Topology.IsQuotientMap

variable {f G} (hf : IsQuotientMap f)
include hf

section MulAction

open Bundle

variable [ContinuousConstSMul G E]
variable (hfG : ∀ {e₁ e₂}, f e₁ = f e₂ ↔ e₁ ∈ MulAction.orbit G e₂)
include hfG

/-- If a group `G` acts on a space `E` and `U` is an open subset disjoint from all other
`G`-translates of itself, and `p` is a quotient map by this action, then `p` admits a
`Bundle.Trivialization` over the base set `p(U)`. -/
@[to_additive (attr := simps! source target baseSet)
/-- If a group `G` acts on a space `E` and `U` is an open subset disjoint from all
other `G`-translates of itself, and `p` is a quotient map by this action, then `p` admits a
`Bundle.Trivialization` over the base set `p(U)`. -/]
/-
**Topology.IsQuotientMap.trivializationOfSMulDisjoint** 是 Mathlib 中的一个定义，位于命名空间 
`Topology.IsQuotientMap`。
形式化陈述：trivializationOfSMulDisjoint [TopologicalSpace G] [DiscreteTopology G] (U 
: Set E) (open_U : IsOpen U) (disjoint : forall g : G, ((g • ·) '' U inter U).No
nempty -> g = 1) : Trivialization G f
参数：U : Set E；open_U : IsOpen U；disjoint : forall g : G, ((g • ·) '' U inter U).N
onempty -> g = 1。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def trivializationOfSMulDisjoint [TopologicalSpace G] [DiscreteTopology G]
    (U : Set E) (open_U : IsOpen U) (disjoint : ∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g = 1) :
    Trivialization G f := by
  have pGE (g : G) e : f (g • e) = f e := hfG.mpr ⟨g, rfl⟩
  have preim_im : f ⁻¹' f '' U = ⋃ g : G, (g • ·) ⁻¹' U := by
    ext e; refine ⟨fun ⟨e', heU, he⟩ ↦ ?_, ?_⟩
    · obtain ⟨g, rfl⟩ := hfG.mp he; exact ⟨_, ⟨g, rfl⟩, heU⟩
    · intro ⟨_, ⟨g, rfl⟩, hg⟩; exact ⟨_, hg, pGE g e⟩
  have : Nonempty (X → E) := ⟨Function.surjInv hf.surjective⟩
  refine IsOpen.trivializationDiscrete (fun g ↦ (g • ·) ⁻¹' U) (f '' U)
    ?_ (fun g W hWU ↦ ⟨fun hoW ↦ (hoW.preimage hf.continuous).inter (open_U.preimage <|
      continuous_const_smul g), fun isOpen ↦ hf.isOpen_preimage.mp ?_⟩) (fun g e₁ h₁ e₂ h₂ he ↦ ?_)
    ?_ (fun {g₁ g₂} hne ↦ disjoint_iff_inf_le.mpr fun e ⟨h₁, h₂⟩ ↦ hne <|
      mul_inv_eq_one.mp (disjoint _ ⟨_, ⟨_, h₂, ?_⟩, h₁⟩)) preim_im.subset
  · rw [← hf.isOpen_preimage, preim_im]
    exact isOpen_iUnion fun g ↦ open_U.preimage (continuous_const_smul g)
  · convert! isOpen_iUnion fun g : G ↦ isOpen.preimage (continuous_const_smul g)
    ext e; refine ⟨fun hW ↦ ?_, ?_⟩
    · have ⟨e', he', hfe⟩ := hWU hW
      obtain ⟨g', rfl⟩ := hfG.mp hfe
      refine ⟨_, ⟨g⁻¹ * g', rfl⟩, ?_, ?_⟩
      · apply Set.mem_of_eq_of_mem (pGE _ e) hW
      · apply Set.mem_of_eq_of_mem _ he'; simp_rw [mul_smul, smul_inv_smul]
    · rintro ⟨_, ⟨g, rfl⟩, hW, -⟩; apply Set.mem_of_eq_of_mem (pGE _ e).symm hW
  · rw [← pGE g, ← pGE g e₂] at he
    have ⟨g', he⟩ := hfG.mp he
    rw [← smul_left_cancel_iff g, ← he, disjoint g' ⟨_, ⟨_, h₂, he⟩, h₁⟩]
    apply one_smul
  · rintro g x ⟨e, hU, rfl⟩; exact ⟨g⁻¹ • e, by apply (smul_inv_smul g e).symm ▸ hU, pGE _ e⟩
  · simp_rw [mul_smul, inv_smul_smul]
/-
**Topology.IsQuotientMap.isCoveringMapOn_of_smul_disjoint** 是 Mathlib 中的一个定理，位于命
名空间 `Topology.IsQuotientMap`。
形式化陈述：∀ {E : Type u_1} {X : Type u_2} [inst : TopologicalSpace E] [inst_1 : Topo
logicalSpace X] {f : E → X} {G : Type u_3}   [inst_2 : Group G] [inst_3 : MulAct
ion G E],   Topology.IsQuotientMap f →     ∀ [ContinuousConstSMul G E],       (∀
 {e₁ e₂ : E}, f e₁ = f e₂ ↔ e₁ ∈ MulAction.orbit G e₂) →         (∀ (e : E), ∃ U
 ∈ nhds e, ∀ (g : G), ((fun x => g • x) '' U ∩ U).Nonempty → g • e = e) →       
    IsCoveringMapOn f (f '' {e | MulAction.stabilizer G e = ⊥})
参数：∀ {e₁ e₂ : E}, f e₁ = f e₂ ↔ e₁ ∈ MulAction.orbit G e₂；∀ (e : E), ∃ U ∈ nhds 
e, ∀ (g : G), ((fun x => g • x) '' U ∩ U).Nonempty → g • e = e；f '' {e | MulActi
on.stabilizer G e = ⊥}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.mem_bot`：mem_bot {x : G} : x in (⊥ : Subgroup G) ↔ x = 1
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Set.inter_subset_inter`：inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq t₁) (h₂ : s₂ subseteq t₂) : s₁ inter s₂ subseteq t₁ inter t₂
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用定理 `IsCoveringMapOn.mk`：mk (F : s -> Type*) [forall x, TopologicalSpace (F x
)] [hF : forall x, DiscreteTopology (F x)] (e : forall x, Trivialization (F x) f
) (h : f…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
@[to_additive] lemma isCoveringMapOn_of_smul_disjoint
    (disjoint : ∀ e : E, ∃ U ∈ 𝓝 e, ∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g • e = e) :
    IsCoveringMapOn f (f '' {e | MulAction.stabilizer G e = ⊥}) := by
  let : TopologicalSpace G := ⊥; have : DiscreteTopology G := ⟨rfl⟩
  suffices ∀ x ∈ f '' {e | MulAction.stabilizer G e = ⊥}, ∃ t : Trivialization G f, x ∈ t.baseSet by
    choose t ht using this; exact IsCoveringMapOn.mk _ _ _ _ fun x ↦ ht x x.2
  rintro x ⟨e, he, rfl⟩
  have ⟨U, heU, hU⟩ := disjoint e
  refine ⟨hf.trivializationOfSMulDisjoint hfG (interior U) isOpen_interior
    fun g hg ↦ ?_, e, mem_interior_iff_mem_nhds.mpr heU, rfl⟩
  rw [← Subgroup.mem_bot, ← he]
  exact hU _ (hg.mono (by grw [interior_subset]))

section ProperlyDiscontinuousSMul

variable [ProperlyDiscontinuousSMul G E] [LocallyCompactSpace E] [T2Space E]

/-
**Topology.IsQuotientMap.isCoveringMapOn_of_properlyDiscontinuousSMul** 是 Mathli
b 中的一个定理，位于命名空间 `Topology.IsQuotientMap`。
形式化陈述：∀ {E : Type u_1} {X : Type u_2} [inst : TopologicalSpace E] [inst_1 : Topo
logicalSpace X] {f : E → X} {G : Type u_3}   [inst_2 : Group G] [inst_3 : MulAct
ion G E],   Topology.IsQuotientMap f →     ∀ [ContinuousConstSMul G E],       (∀
 {e₁ e₂ : E}, f e₁ = f e₂ ↔ e₁ ∈ MulAction.orbit G e₂) →         ∀ [ProperlyDisc
ontinuousSMul G E] [LocallyCompactSpace E] [T2Space E],           IsCoveringMapO
n f (f '' {e | MulAction.stabilizer G e = ⊥})
参数：∀ {e₁ e₂ : E}, f e₁ = f e₂ ↔ e₁ ∈ MulAction.orbit G e₂；f '' {e | MulAction.st
abilizer G e = ⊥}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsQuotientMap.isCoveringMapOn_of_smul_disjoint`：∀ {E : Type u_1
} {X : Type u_2} [inst : TopologicalSpace E] [inst_1 : TopologicalSpace X] {f : 
E → X} {G : Type u_3}   [inst_2 : Group G] [i…
· 使用定理 `ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self`：∀ (Γ : Type u_
4) {T : Type u_5} [inst : TopologicalSpace T] [inst_1 : SMul Γ T] [ProperlyDisco
ntinuousSMul Γ T]   [T2Space T] [LocallyCompac…
-/
@[to_additive] lemma isCoveringMapOn_of_properlyDiscontinuousSMul :
    IsCoveringMapOn f (f '' {e | MulAction.stabilizer G e = ⊥}) :=
  hf.isCoveringMapOn_of_smul_disjoint hfG
    (ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self G)
/-
**Topology.IsQuotientMap.isQuotientCoveringMap_of_properlyDiscontinuousSMul** 是 
Mathlib 中的一个定理，位于命名空间 `Topology.IsQuotientMap`。
形式化陈述：∀ {E : Type u_1} {X : Type u_2} [inst : TopologicalSpace E] [inst_1 : Topo
logicalSpace X] {f : E → X} {G : Type u_3}   [inst_2 : Group G] [inst_3 : MulAct
ion G E],   Topology.IsQuotientMap f →     ∀ [ContinuousConstSMul G E],       (∀
 {e₁ e₂ : E}, f e₁ = f e₂ ↔ e₁ ∈ MulAction.orbit G e₂) →         ∀ [ProperlyDisc
ontinuousSMul G E] [LocallyCompactSpace E] [T2Space E] [IsCancelSMul G E],      
     IsQuotientCoveringMap f G
参数：∀ {e₁ e₂ : E}, f e₁ = f e₂ ↔ e₁ ∈ MulAction.orbit G e₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self`：∀ (Γ : Type u_
4) {T : Type u_5} [inst : TopologicalSpace T] [inst_1 : SMul Γ T] [ProperlyDisco
ntinuousSMul Γ T]   [T2Space T] [LocallyCompac…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `isCancelSMul_iff_eq_one_of_smul_eq`：isCancelSMul_iff_eq_one_of_smul_eq :
 IsCancelSMul α β ↔ (forall (g : α) (x : β), g • x = x -> g = 1)
-/
@[to_additive] lemma isQuotientCoveringMap_of_properlyDiscontinuousSMul [IsCancelSMul G E] :
    IsQuotientCoveringMap f G where
  __ := hf
  apply_eq_iff_mem_orbit := hfG
  disjoint e :=
    have ⟨U, heU, hU⟩ := ProperlyDiscontinuousSMul.exists_nhds_image_smul_eq_self G e
    ⟨U, heU, fun g hg ↦ isCancelSMul_iff_eq_one_of_smul_eq.mp ‹_› _ _ (hU g hg)⟩

omit hf hfG
/-
**Topology.IsQuotientMap._root_.isCoveringMapOn_quotientMk_of_properlyDiscontinu
ousSMul** 是 Mathlib 中的一个引理，位于命名空间 `Topology.IsQuotientMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] lemma _root_.isCoveringMapOn_quotientMk_of_properlyDiscontinuousSMul :
    IsCoveringMapOn (Quotient.mk _) <|
      (Quotient.mk <| MulAction.orbitRel G E) '' {e | MulAction.stabilizer G e = ⊥} :=
  isQuotientMap_quotient_mk'.isCoveringMapOn_of_properlyDiscontinuousSMul Quotient.eq''
/-
**Topology.IsQuotientMap._root_.isQuotientCoveringMap_quotientMk_of_properlyDisc
ontinuousSMul** 是 Mathlib 中的一个引理，位于命名空间 `Topology.IsQuotientMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] lemma _root_.isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
    [IsCancelSMul G E] : IsQuotientCoveringMap (Quotient.mk <| MulAction.orbitRel G E) G :=
  isQuotientMap_quotient_mk'.isQuotientCoveringMap_of_properlyDiscontinuousSMul Quotient.eq''

end ProperlyDiscontinuousSMul

end MulAction

/-
**Topology.IsQuotientMap.isQuotientCoveringMap_of_subgroup** 是 Mathlib 中的一个定理，位于
命名空间 `Topology.IsQuotientMap`。
形式化陈述：∀ {E : Type u_1} {X : Type u_2} [inst : TopologicalSpace E] [inst_1 : Topo
logicalSpace X] {f : E → X},   Topology.IsQuotientMap f →     ∀ [inst_2 : Group 
E] [IsTopologicalGroup E] (G : Subgroup E),       IsDiscrete ↑G → (∀ {e₁ e₂ : E}
, f e₁ = f e₂ ↔ e₂ * e₁⁻¹ ∈ G) → IsQuotientCoveringMap f ↥G
参数：G : Subgroup E；∀ {e₁ e₂ : E}, f e₁ = f e₂ ↔ e₂ * e₁⁻¹ ∈ G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [IsScalarTower R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Subgroup.instIsScalarTowerSubtypeMem`：∀ {G : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : Group G] [inst_1 : SMul α β] [inst_2 : MulAction G α]   [in
st_3 : MulAction G β] [IsS…
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `QuotientGroup.rightRel_apply`：rightRel_apply {x y : α} : rightRel s x y 
↔ y * x⁻¹ in s
· 使用定理 `IsDiscrete.exists_nhds_eq_one_of_image_mulLeft_inter_nonempty`：∀ {G : Ty
pe w} [inst : TopologicalSpace G] [inst_1 : Group G] [IsTopologicalGroup G] (S :
 Subgroup G),   IsDiscrete ↑S → ∃ U ∈ nhds 1, U⁻¹ =…
· 使用定理 `mul_singleton_mem_nhds_of_nhds_one`：mul_singleton_mem_nhds_of_nhds_one (
a : α) (h : s in 𝓝 (1 : α)) : s * {a} in 𝓝 a
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `mul_right_cancel`：mul_right_cancel : a * b = c * b -> a = c
· 使用定理 `RightCancelSemigroup.toIsRightCancelMul`：∀ {G : Type u} [self : RightCan
celSemigroup G], IsRightCancelMul G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[to_additive] lemma isQuotientCoveringMap_of_subgroup [Group E] [IsTopologicalGroup E]
    (G : Subgroup E) (hG : IsDiscrete (G : Set E)) (hfG : ∀ {e₁ e₂}, f e₁ = f e₂ ↔ e₂ * e₁⁻¹ ∈ G) :
    IsQuotientCoveringMap f G where
  __ := hf
  apply_eq_iff_mem_orbit := hfG.trans QuotientGroup.rightRel_apply.symm
  disjoint e := have ⟨U, hU, _, disj⟩ := hG.exists_nhds_eq_one_of_image_mulLeft_inter_nonempty
    ⟨_, mul_singleton_mem_nhds_of_nhds_one e hU, fun s hs ↦ Subtype.ext <| disj _ s.2 <| by
      obtain ⟨_, ⟨_, ⟨x, hx, _, rfl, rfl⟩, rfl⟩, y, hy, g, rfl, he⟩ := hs
      exact ⟨y, ⟨x, hx, mul_right_cancel ((mul_assoc ..).trans he.symm)⟩, hy⟩⟩
/-
**Topology.IsQuotientMap.isQuotientCoveringMap_of_subgroupOp** 是 Mathlib 中的一个定理，
位于命名空间 `Topology.IsQuotientMap`。
形式化陈述：∀ {E : Type u_1} {X : Type u_2} [inst : TopologicalSpace E] [inst_1 : Topo
logicalSpace X] {f : E → X},   Topology.IsQuotientMap f →     ∀ [inst_2 : Group 
E] [IsTopologicalGroup E] (G : Subgroup E),       IsDiscrete ↑G → (∀ {e₁ e₂ : E}
, f e₁ = f e₂ ↔ e₁⁻¹ * e₂ ∈ G) → IsQuotientCoveringMap f ↥G.op
参数：G : Subgroup E；∀ {e₁ e₂ : E}, f e₁ = f e₂ ↔ e₁⁻¹ * e₂ ∈ G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `QuotientGroup.leftRel_apply`：leftRel_apply {x y : α} : leftRel s x y ↔ x
⁻¹ * y in s
· 使用定理 `IsDiscrete.exists_nhds_eq_one_of_image_mulRight_inter_nonempty`：∀ {G : T
ype w} [inst : TopologicalSpace G] [inst_1 : Group G] [IsTopologicalGroup G] (S 
: Subgroup G),   IsDiscrete ↑S → ∃ U ∈ nhds 1, U⁻¹ =…
· 使用定理 `singleton_mul_mem_nhds_of_nhds_one`：singleton_mul_mem_nhds_of_nhds_one (
a : α) (h : s in 𝓝 (1 : α)) : {a} * s in 𝓝 a
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `MulOpposite.unop_injective`：unop_injective : Injective (unop : αᵐᵒᵖ -> α
)
· 使用定理 `mul_left_cancel`：mul_left_cancel : a * b = a * c -> b = c
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
@[to_additive] lemma isQuotientCoveringMap_of_subgroupOp [Group E] [IsTopologicalGroup E]
    (G : Subgroup E) (hG : IsDiscrete (G : Set E)) (hfG : ∀ {e₁ e₂}, f e₁ = f e₂ ↔ e₁⁻¹ * e₂ ∈ G) :
    IsQuotientCoveringMap f G.op where
  __ := hf
  apply_eq_iff_mem_orbit := hfG.trans QuotientGroup.leftRel_apply.symm
  disjoint e := have ⟨U, hU, _, disj⟩ := hG.exists_nhds_eq_one_of_image_mulRight_inter_nonempty
    ⟨_, singleton_mul_mem_nhds_of_nhds_one e hU, fun ⟨⟨s⟩, hS⟩ hs ↦ Subtype.ext <|
        MulOpposite.unop_injective <| disj _ hS <| by
      obtain ⟨_, ⟨_, ⟨_, rfl, x, hx, rfl⟩, rfl⟩, g, rfl, y, hy, he⟩ := hs
      exact ⟨y, ⟨x, hx, mul_left_cancel (he.trans <| mul_assoc ..).symm⟩, hy⟩⟩

omit hf in
/-
**Topology.IsQuotientMap.isQuotientCoveringMap_of_isDiscrete_ker_monoidHom** 是 M
athlib 中的一个定理，位于命名空间 `Topology.IsQuotientMap`。
形式化陈述：∀ {E : Type u_1} {X : Type u_2} [inst : TopologicalSpace E] [inst_1 : Topo
logicalSpace X] [inst_2 : Group E]   [IsTopologicalGroup E] [inst_4 : Group X] {
f : E →* X},   Topology.IsQuotientMap ⇑f → IsDiscrete ↑f.ker → IsQuotientCoverin
gMap ⇑f ↥f.ker
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsQuotientMap.isQuotientCoveringMap_of_subgroup`：∀ {E : Type u_
1} {X : Type u_2} [inst : TopologicalSpace E] [inst_1 : TopologicalSpace X] {f :
 E → X},   Topology.IsQuotientMap f →     ∀ [i…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_inv_eq_one`：mul_inv_eq_one : a * b⁻¹ = 1 ↔ a = b
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[to_additive] lemma isQuotientCoveringMap_of_isDiscrete_ker_monoidHom [Group E]
    [IsTopologicalGroup E] [Group X] {f : E →* X} (hf : IsQuotientMap f)
    (disc : IsDiscrete (f.ker : Set E)) :
    IsQuotientCoveringMap f f.ker :=
  hf.isQuotientCoveringMap_of_subgroup f.ker disc fun {_ _} ↦ by
    rw [eq_comm, ← mul_inv_eq_one, ← map_inv, ← map_mul]; rfl

end Topology.IsQuotientMap

/-
**Subgroup.isQuotientCoveringMap** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：∀ {G : Type u_4} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopolog
icalGroup G] (S : Subgroup G),   IsDiscrete ↑S → IsQuotientCoveringMap QuotientG
roup.mk ↥S.op
参数：S : Subgroup G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsQuotientMap.isQuotientCoveringMap_of_subgroupOp`：∀ {E : Type 
u_1} {X : Type u_2} [inst : TopologicalSpace E] [inst_1 : TopologicalSpace X] {f
 : E → X},   Topology.IsQuotientMap f →     ∀ [i…
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `isQuotientMap_quotient_mk'`：isQuotientMap_quotient_mk' : IsQuotientMap (
@Quotient.mk' X s)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Quotient.eq''`：∀ {α : Sort u_1} {s₁ : Setoid α} {a b : α}, Quotient.mk''
 a = Quotient.mk'' b ↔ s₁ a b
· 使用定理 `QuotientGroup.leftRel_apply`：leftRel_apply {x y : α} : leftRel s x y ↔ x
⁻¹ * y in s
-/
@[to_additive] lemma Subgroup.isQuotientCoveringMap {G} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (S : Subgroup G) (hS : IsDiscrete (S : Set G)) :
    IsQuotientCoveringMap (QuotientGroup.mk (s := S)) S.op :=
  isQuotientMap_quotient_mk'.isQuotientCoveringMap_of_subgroupOp S hS <|
    Quotient.eq''.trans QuotientGroup.leftRel_apply
/-
**Subgroup.isQuotientCoveringMap_of_comm** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：∀ {G : Type u_4} [inst : CommGroup G] [inst_1 : TopologicalSpace G] [IsTop
ologicalGroup G] (S : Subgroup G),   IsDiscrete ↑S → IsQuotientCoveringMap Quoti
entGroup.mk ↥S
参数：S : Subgroup G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsQuotientMap.isQuotientCoveringMap_of_subgroup`：∀ {E : Type u_
1} {X : Type u_2} [inst : TopologicalSpace E] [inst_1 : TopologicalSpace X] {f :
 E → X},   Topology.IsQuotientMap f →     ∀ [i…
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `isQuotientMap_quotient_mk'`：isQuotientMap_quotient_mk' : IsQuotientMap (
@Quotient.mk' X s)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Quotient.eq''`：∀ {α : Sort u_1} {s₁ : Setoid α} {a b : α}, Quotient.mk''
 a = Quotient.mk'' b ↔ s₁ a b
· 使用定理 `QuotientGroup.leftRel_apply`：leftRel_apply {x y : α} : leftRel s x y ↔ x
⁻¹ * y in s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[to_additive] lemma Subgroup.isQuotientCoveringMap_of_comm {G} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] (S : Subgroup G) (hS : IsDiscrete (S : Set G)) :
    IsQuotientCoveringMap (QuotientGroup.mk (s := S)) S :=
  isQuotientMap_quotient_mk'.isQuotientCoveringMap_of_subgroup S hS <| Quotient.eq''.trans <|
    QuotientGroup.leftRel_apply.trans <| by rw [mul_comm]

namespace IsQuotientCoveringMap

/-
**IsQuotientCoveringMap.isCoveringMap** 是 Mathlib 中的一个定理，位于命名空间 `IsQuotientCover
ingMap`。
形式化陈述：∀ {E : Type u_1} {X : Type u_2} [inst : TopologicalSpace E] [inst_1 : Topo
logicalSpace X] (f : E → X) (G : Type u_3)   [inst_2 : Group G] [inst_3 : MulAct
ion G E], IsQuotientCoveringMap f G → IsCoveringMap f
参数：f : E → X；G : Type u_3。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isCoveringMap_iff_isCoveringMapOn_univ`：isCoveringMap_iff_isCoveringMapO
n_univ : IsCoveringMap f ↔ IsCoveringMapOn f .univ
· 使用定理 `IsQuotientCoveringMap.toContinuousConstSMul`：∀ {E : Type u_1} {X : Type 
u_2} [inst : TopologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X} {G : 
Type u_3}   [inst_2 : Group G] [i…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ
· 使用定理 `Topology.IsQuotientMap.surjective`：∀ {X : Type u_3} {Y : Type u_4} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topology.IsQ
uotientMap f → Function…
· 使用定理 `IsQuotientCoveringMap.toIsQuotientMap`：∀ {E : Type u_1} {X : Type u_2} [
inst : TopologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X} {G : Type u
_3}   [inst_2 : Group G] [i…
· 使用定理 `IsQuotientCoveringMap.disjoint`：∀ {E : Type u_1} {X : Type u_2} [inst : 
TopologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X} {G : Type u_3}   [
inst_2 : Group G] [i…
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `Subgroup.eq_bot_iff_forall`：eq_bot_iff_forall : H = ⊥ ↔ forall x in H, x
 = (1 : G)
· 使用定理 `Topology.IsQuotientMap.isCoveringMapOn_of_smul_disjoint`：∀ {E : Type u_1
} {X : Type u_2} [inst : TopologicalSpace E] [inst_1 : TopologicalSpace X] {f : 
E → X} {G : Type u_3}   [inst_2 : Group G] [i…
· 使用定理 `IsQuotientCoveringMap.apply_eq_iff_mem_orbit`：∀ {E : Type u_1} {X : Type
 u_2} [inst : TopologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X} {G :
 Type u_3}   [inst_2 : Group G] [i…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
@[to_additive] lemma isCoveringMap (h : IsQuotientCoveringMap f G) :
    IsCoveringMap f :=
  isCoveringMap_iff_isCoveringMapOn_univ.mpr <| by
    have := h.toContinuousConstSMul
    convert! ← h.isCoveringMapOn_of_smul_disjoint h.apply_eq_iff_mem_orbit fun e ↦ ?_
    · refine Set.eq_univ_of_forall fun x ↦ ?_
      obtain ⟨e, rfl⟩ := h.surjective x
      have ⟨U, hU, hGU⟩ := h.disjoint e
      replace hU := mem_of_mem_nhds hU
      exact ⟨e, (Subgroup.eq_bot_iff_forall _).mpr fun g hg ↦ hGU g (⟨e, ⟨e, hU, hg⟩, hU⟩), rfl⟩
    · have ⟨U, hU, hGU⟩ := h.disjoint e
      exact ⟨U, hU, fun g hg ↦ by rw [hGU g hg, one_smul]⟩
/-
**IsQuotientCoveringMap.isOpenQuotientMap** 是 Mathlib 中的一个定理，位于命名空间 `IsQuotientC
overingMap`。
形式化陈述：∀ {E : Type u_1} {X : Type u_2} [inst : TopologicalSpace E] [inst_1 : Topo
logicalSpace X] (f : E → X) (G : Type u_3)   [inst_2 : Group G] [inst_3 : MulAct
ion G E], IsQuotientCoveringMap f G → IsOpenQuotientMap f
参数：f : E → X；G : Type u_3。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsQuotientMap.surjective`：∀ {X : Type u_3} {Y : Type u_4} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topology.IsQ
uotientMap f → Function…
· 使用定理 `IsQuotientCoveringMap.toIsQuotientMap`：∀ {E : Type u_1} {X : Type u_2} [
inst : TopologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X} {G : Type u
_3}   [inst_2 : Group G] [i…
· 使用定理 `IsCoveringMap.continuous`：∀ {E : Type u_1} {X : Type u_2} [inst : Topolo
gicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X},   IsCoveringMap f → Con
tinuous f
· 使用定理 `IsQuotientCoveringMap.isCoveringMap`：∀ {E : Type u_1} {X : Type u_2} [in
st : TopologicalSpace E] [inst_1 : TopologicalSpace X] (f : E → X) (G : Type u_3
)   [inst_2 : Group G] [i…
· 使用定理 `IsCoveringMap.isOpenMap`：∀ {E : Type u_1} {X : Type u_2} [inst : Topolog
icalSpace E] [inst_1 : TopologicalSpace X] {f : E → X},   IsCoveringMap f → IsOp
enMap f
-/
@[to_additive] theorem isOpenQuotientMap (h : IsQuotientCoveringMap f G) :
    IsOpenQuotientMap f where
  surjective := h.surjective
  continuous := h.isCoveringMap.continuous
  isOpenMap := h.isCoveringMap.isOpenMap

end IsQuotientCoveringMap

/-
**isQuotientCoveringMap_iff_isCoveringMap_and** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {E : Type u_1} {X : Type u_2} [inst : TopologicalSpace E] [inst_1 : Topo
logicalSpace X] (f : E → X) (G : Type u_3)   [inst_2 : Group G] [inst_3 : MulAct
ion G E],   IsQuotientCoveringMap f G ↔     IsCoveringMap f ∧       Function.Sur
jective f ∧         ContinuousConstSMul G E ∧ IsCancelSMul G E ∧ ∀ {e₁ e₂ : E}, 
f e₁ = f e₂ ↔ e₁ ∈ MulAction.orbit G e₂
参数：f : E → X；G : Type u_3。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsQuotientCoveringMap.toContinuousConstSMul`：∀ {E : Type u_1} {X : Type 
u_2} [inst : TopologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X} {G : 
Type u_3}   [inst_2 : Group G] [i…
· 使用定理 `IsQuotientCoveringMap.isCoveringMap`：∀ {E : Type u_1} {X : Type u_2} [in
st : TopologicalSpace E] [inst_1 : TopologicalSpace X] (f : E → X) (G : Type u_3
)   [inst_2 : Group G] [i…
· 使用定理 `Topology.IsQuotientMap.surjective`：∀ {X : Type u_3} {Y : Type u_4} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topology.IsQ
uotientMap f → Function…
· 使用定理 `IsQuotientCoveringMap.toIsQuotientMap`：∀ {E : Type u_1} {X : Type u_2} [
inst : TopologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X} {G : Type u
_3}   [inst_2 : Group G] [i…
· 使用定理 `IsQuotientCoveringMap.isCancelSMul`：∀ {E : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X} {G : Type u_3}
   [inst_2 : Group G] [i…
· 使用定理 `IsQuotientCoveringMap.apply_eq_iff_mem_orbit`：∀ {E : Type u_1} {X : Type
 u_2} [inst : TopologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X} {G :
 Type u_3}   [inst_2 : Group G] [i…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isQuotientCoveringMap_iff`：∀ {E : Type u_1} {X : Type u_2} [inst : Topol
ogicalSpace E] [inst_1 : TopologicalSpace X] (f : E → X) (G : Type u_3)   [inst_
2 : Group G] [i…
· 使用定理 `IsCoveringMap.isQuotientMap`：isQuotientMap (hf' : Function.Surjective f)
 : IsQuotientMap f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `IsOpen.isOpenMap_subtype_val`：IsOpen.isOpenMap_subtype_val {s : Set X} (
hs : IsOpen s) : IsOpenMap ((↑) : s -> X)
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
· 使用定理 `Homeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), Continuous ⇑h
· 使用定理 `isOpen_discrete`：isOpen_discrete (s : Set α) : IsOpen s
· 使用引理 `IsCancelSMul.right_cancel`：IsCancelSMul.right_cancel {G P} [SMul G P] [I
sCancelSMul G P] (a b : G) (c : P) : a • c = b • c -> a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Homeomorph.injective`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y),   Function.Injective ⇑h
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
@[to_additive] theorem isQuotientCoveringMap_iff_isCoveringMap_and :
    IsQuotientCoveringMap f G ↔ IsCoveringMap f ∧ f.Surjective ∧ ContinuousConstSMul G E ∧
      IsCancelSMul G E ∧ ∀ {e₁ e₂}, f e₁ = f e₂ ↔ e₁ ∈ MulAction.orbit G e₂ where
  mp h := have := h.toContinuousConstSMul
    ⟨h.isCoveringMap, h.surjective, this, h.isCancelSMul, h.apply_eq_iff_mem_orbit⟩
  mpr h := (isQuotientCoveringMap_iff ..).mpr ⟨h.1.isQuotientMap h.2.1, h.2.2.1, h.2.2.2.2, fun e ↦
    have ⟨_, U, heU, hU, hfU, H, hH⟩ := h.1 (f e)
    ⟨Subtype.val '' Prod.snd ∘ H ⁻¹' {(H ⟨e, heU⟩).2}, (hfU.isOpenMap_subtype_val _ <|
        (isOpen_discrete _).preimage <| by fun_prop).mem_nhds ⟨⟨e, heU⟩, rfl, rfl⟩, fun g ↦ by
      rintro ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, y, hy, eq⟩
      have := h.2.2.2.1
      apply IsCancelSMul.right_cancel _ _ x.1
      simp_rw [← eq, one_smul]
      refine congr($(H.injective <| Prod.ext (Subtype.ext ?_) <| hy.trans hx.symm))
      simp_rw [hH]
      exact h.2.2.2.2.mpr ⟨_, eq.symm⟩⟩⟩
