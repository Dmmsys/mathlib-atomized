/-
Copyright (c) 2022 Paul Reichert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

/-!
# Affine map restrictions

This file defines restrictions of affine maps.

## Main definitions

* The domain and codomain of an affine map can be restricted using
  `AffineMap.restrict`.

## Main theorems

* The associated linear map of the restriction is the restriction of the
  linear map associated to the original affine map.
* The restriction is injective if the original map is injective.
* The restriction in surjective if the codomain is the image of the domain.
-/

@[expose] public section


variable {k V₁ P₁ V₂ P₂ : Type*} [Ring k] [AddCommGroup V₁] [AddCommGroup V₂] [Module k V₁]
  [Module k V₂] [AddTorsor V₁ P₁] [AddTorsor V₂ P₂]

/-
**AffineSubspace.nonempty_map** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：AffineSubspace.nonempty_map {E : AffineSubspace k P₁} [Ene : Nonempty E] {
φ : P₁ ->ᵃ[k] P₂} : Nonempty (E.map φ)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AffineSubspace.mem_map`：mem_map {f : P₁ ->ᵃ[k] P₂} {x : P₂} {s : AffineS
ubspace k P₁} : x in s.map f ↔ exists y in s, f y = x
-/
instance AffineSubspace.nonempty_map {E : AffineSubspace k P₁} [Ene : Nonempty E]
    {φ : P₁ →ᵃ[k] P₂} : Nonempty (E.map φ) := by
  obtain ⟨x, hx⟩ := id Ene
  exact ⟨⟨φ x, AffineSubspace.mem_map.mpr ⟨x, hx, rfl⟩⟩⟩

/-- Restrict domain and codomain of an affine map to the given subspaces. -/
/-
**AffineMap.restrict** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AffineMap.restrict (φ : P₁ ->ᵃ[k] P₂) {E : AffineSubspace k P₁} {F : Affin
eSubspace k P₂} [Nonempty E] [Nonempty F] (hEF : E.map φ <= F) : E ->ᵃ[k] F
参数：φ : P₁ ->ᵃ[k] P₂；hEF : E.map φ <= F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict domain and codomain of an affine map to the given subspaces.
-/
def AffineMap.restrict (φ : P₁ →ᵃ[k] P₂) {E : AffineSubspace k P₁} {F : AffineSubspace k P₂}
    [Nonempty E] [Nonempty F] (hEF : E.map φ ≤ F) : E →ᵃ[k] F := by
  refine ⟨?_, ?_, ?_⟩
  · exact fun x => ⟨φ x, hEF <| AffineSubspace.mem_map.mpr ⟨x, x.property, rfl⟩⟩
  · refine φ.linear.restrict (?_ : E.direction ≤ F.direction.comap φ.linear)
    rw [← Submodule.map_le_iff_le_comap, ← AffineSubspace.map_direction]
    exact AffineSubspace.direction_le hEF
  · intro p v
    simp only [Subtype.ext_iff, AffineSubspace.coe_vadd]
    apply AffineMap.map_vadd
/-
**AffineMap.restrict.coe_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AffineMap.restrict.coe_apply (φ : P₁ ->ᵃ[k] P₂) {E : AffineSubspace k P₁} 
{F : AffineSubspace k P₂} [Nonempty E] [Nonempty F] (hEF : E.map φ <= F) (x : E)
 : ↑(φ.restrict hEF x) = φ x
参数：φ : P₁ ->ᵃ[k] P₂；hEF : E.map φ <= F；x : E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AffineMap.restrict.coe_apply (φ : P₁ →ᵃ[k] P₂) {E : AffineSubspace k P₁}
    {F : AffineSubspace k P₂} [Nonempty E] [Nonempty F] (hEF : E.map φ ≤ F) (x : E) :
    ↑(φ.restrict hEF x) = φ x :=
  rfl
/-
**AffineMap.restrict.linear_aux** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AffineMap.restrict.linear_aux {φ : P₁ ->ᵃ[k] P₂} {E : AffineSubspace k P₁}
 {F : AffineSubspace k P₂} (hEF : E.map φ <= F) : E.direction <= F.direction.com
ap φ.linear
参数：hEF : E.map φ <= F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.map_le_iff_le_comap`：map_le_iff_le_comap {f : M ->ₛₗ[σ₁₂] M₂} 
{p : Submodule R M} {q : Submodule R₂ M₂} : map f p <= q ↔ p <= comap f q
· 使用定理 `AffineSubspace.map_direction`：map_direction (s : AffineSubspace k P₁) : 
(s.map f).direction = s.direction.map f.linear
· 使用定理 `AffineSubspace.direction_le`：direction_le {s₁ s₂ : AffineSubspace k P} (
h : s₁ <= s₂) : s₁.direction <= s₂.direction
-/
theorem AffineMap.restrict.linear_aux {φ : P₁ →ᵃ[k] P₂} {E : AffineSubspace k P₁}
    {F : AffineSubspace k P₂} (hEF : E.map φ ≤ F) : E.direction ≤ F.direction.comap φ.linear := by
  rw [← Submodule.map_le_iff_le_comap, ← AffineSubspace.map_direction]
  exact AffineSubspace.direction_le hEF
/-
**AffineMap.restrict.linear** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AffineMap.restrict.linear (φ : P₁ ->ᵃ[k] P₂) {E : AffineSubspace k P₁} {F 
: AffineSubspace k P₂} [Nonempty E] [Nonempty F] (hEF : E.map φ <= F) : (φ.restr
ict hEF).linear = φ.linear.restrict (AffineMap.restrict.linear_aux hEF)
参数：φ : P₁ ->ᵃ[k] P₂；hEF : E.map φ <= F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AffineMap.restrict.linear (φ : P₁ →ᵃ[k] P₂) {E : AffineSubspace k P₁}
    {F : AffineSubspace k P₂} [Nonempty E] [Nonempty F] (hEF : E.map φ ≤ F) :
    (φ.restrict hEF).linear = φ.linear.restrict (AffineMap.restrict.linear_aux hEF) :=
  rfl
/-
**AffineMap.restrict.injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AffineMap.restrict.injective {φ : P₁ ->ᵃ[k] P₂} (hφ : Function.Injective φ
) {E : AffineSubspace k P₁} {F : AffineSubspace k P₂} [Nonempty E] [Nonempty F] 
(hEF : E.map φ <= F) : Function.Injective (AffineMap.restrict φ hEF)
参数：hφ : Function.Injective φ；hEF : E.map φ <= F。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem AffineMap.restrict.injective {φ : P₁ →ᵃ[k] P₂} (hφ : Function.Injective φ)
    {E : AffineSubspace k P₁} {F : AffineSubspace k P₂} [Nonempty E] [Nonempty F]
    (hEF : E.map φ ≤ F) : Function.Injective (AffineMap.restrict φ hEF) := by
  intro x y h
  simp only [Subtype.ext_iff, AffineMap.restrict.coe_apply] at h ⊢
  exact hφ h
/-
**AffineMap.restrict.surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AffineMap.restrict.surjective (φ : P₁ ->ᵃ[k] P₂) {E : AffineSubspace k P₁}
 {F : AffineSubspace k P₂} [Nonempty E] [Nonempty F] (h : E.map φ = F) : Functio
n.Surjective (AffineMap.restrict φ (le_of_eq h))
参数：φ : P₁ ->ᵃ[k] P₂；h : E.map φ = F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineSubspace.mem_map`：mem_map {f : P₁ ->ᵃ[k] P₂} {x : P₂} {s : AffineS
ubspace k P₁} : x in s.map f ↔ exists y in s, f y = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem AffineMap.restrict.surjective (φ : P₁ →ᵃ[k] P₂) {E : AffineSubspace k P₁}
    {F : AffineSubspace k P₂} [Nonempty E] [Nonempty F] (h : E.map φ = F) :
    Function.Surjective (AffineMap.restrict φ (le_of_eq h)) := by
  rintro ⟨x, hx : x ∈ F⟩
  rw [← h, AffineSubspace.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨⟨y, hy⟩, rfl⟩
/-
**AffineMap.restrict.bijective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AffineMap.restrict.bijective {E : AffineSubspace k P₁} [Nonempty E] {φ : P
₁ ->ᵃ[k] P₂} (hφ : Function.Injective φ) : Function.Bijective (φ.restrict (le_re
fl (E.map φ)))
参数：hφ : Function.Injective φ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `AffineMap.restrict.injective`：AffineMap.restrict.injective {φ : P₁ ->ᵃ[k
] P₂} (hφ : Function.Injective φ) {E : AffineSubspace k P₁} {F : AffineSubspace 
k P₂} [Nonempty E]…
· 使用定理 `AffineMap.restrict.surjective`：AffineMap.restrict.surjective (φ : P₁ ->ᵃ
[k] P₂) {E : AffineSubspace k P₁} {F : AffineSubspace k P₂} [Nonempty E] [Nonemp
ty F] (h : E.map φ …
-/
theorem AffineMap.restrict.bijective {E : AffineSubspace k P₁} [Nonempty E] {φ : P₁ →ᵃ[k] P₂}
    (hφ : Function.Injective φ) : Function.Bijective (φ.restrict (le_refl (E.map φ))) :=
  ⟨AffineMap.restrict.injective hφ _, AffineMap.restrict.surjective _ rfl⟩

namespace AffineEquiv

/-- An affine equivalence restricts to an affine equivalence between an affine subspace and its
image. -/
/-
**AffineEquiv.affineSubspaceMap** 是 Mathlib 中的一个定义，位于命名空间 `AffineEquiv`。
形式化陈述：affineSubspaceMap (e : P₁ ≃ᵃ[k] P₂) (s : AffineSubspace k P₁) [Nonempty s]
 : s ≃ᵃ[k] s.map e.toAffineMap
参数：e : P₁ ≃ᵃ[k] P₂；s : AffineSubspace k P₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An affine equivalence restricts to an affine equivalence between an affine subsp
ace and its
image.
-/
noncomputable def affineSubspaceMap (e : P₁ ≃ᵃ[k] P₂) (s : AffineSubspace k P₁)
    [Nonempty s] : s ≃ᵃ[k] s.map e.toAffineMap :=
  .ofBijective (AffineMap.restrict.bijective e.injective)

@[simp]
/-
**AffineEquiv.affineSubspaceMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `AffineEquiv`。
形式化陈述：affineSubspaceMap_apply (e : P₁ ≃ᵃ[k] P₂) (s : AffineSubspace k P₁) [Nonem
pty s] (x : s) : e.affineSubspaceMap s x = e x
参数：e : P₁ ≃ᵃ[k] P₂；s : AffineSubspace k P₁；x : s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem affineSubspaceMap_apply (e : P₁ ≃ᵃ[k] P₂) (s : AffineSubspace k P₁)
    [Nonempty s] (x : s) : e.affineSubspaceMap s x = e x :=
  rfl

@[simp]
/-
**AffineEquiv.affineSubspaceMap_apply_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Affi
neEquiv`。
形式化陈述：affineSubspaceMap_apply_symm_apply (e : P₁ ≃ᵃ[k] P₂) (s : AffineSubspace k
 P₁) [Nonempty s] (x : s.map e.toAffineMap) : e ((e.affineSubspaceMap s).symm x)
 = x
参数：e : P₁ ≃ᵃ[k] P₂；s : AffineSubspace k P₁；x : s.map e.toAffineMap。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineEquiv.apply_symm_apply`：apply_symm_apply (e : P₁ ≃ᵃ[k] P₂) (p : P₂
) : e (e.symm p) = p
-/
theorem affineSubspaceMap_apply_symm_apply (e : P₁ ≃ᵃ[k] P₂) (s : AffineSubspace k P₁)
    [Nonempty s] (x : s.map e.toAffineMap) : e ((e.affineSubspaceMap s).symm x) = x :=
  congrArg Subtype.val <| (e.affineSubspaceMap s).apply_symm_apply x

end AffineEquiv

