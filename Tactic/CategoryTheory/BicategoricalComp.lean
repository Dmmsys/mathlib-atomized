/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import Mathlib.CategoryTheory.Bicategory.Basic

/-!
# Bicategorical composition `⊗≫` (composition up to associators)

We provide `f ⊗≫ g`, the `bicategoricalComp` operation,
which automatically inserts associators and unitors as needed
to make the target of `f` match the source of `g`.
-/

@[expose] public section

universe w v u

open CategoryTheory Bicategory

namespace CategoryTheory

variable {B : Type u} [Bicategory.{w, v} B] {a b c d : B}

/--
Definition of `BicategoricalCoherence` / `BicategoricalCoherence` 的定义

English:
class BicategoricalCoherence
  parameters: (f g : a ⟶ b)
  axioms and operations (1):
    - iso : f ≅ g

中文:
类 BicategoricalCoherence
  参数: (f g : a ⟶ b)
  公理与运算 (1 个):
    - iso : f ≅ g
-/
class BicategoricalCoherence (f g : a ⟶ b) where
  /-- The chosen structural isomorphism between to 1-morphisms. -/
  iso : f ≅ g

/-- Notation for identities up to unitors and associators. -/
scoped[CategoryTheory.Bicategory] notation " otimes𝟙 " =>
  BicategoricalCoherence.iso -- type as \ot 𝟙

/--
Definition of `bicategoricalIso` / `bicategoricalIso` 的定义

English:
abbreviation bicategoricalIso
  signature: (f g : a ⟶ b) [BicategoricalCoherence f g]
  body: otimes𝟙

中文:
缩写 bicategoricalIso
  签名: (f g : a ⟶ b) [BicategoricalCoherence f g]
  定义体: otimes𝟙
-/
abbrev bicategoricalIso (f g : a ⟶ b) [BicategoricalCoherence f g] : f ≅ g :=
  otimes𝟙

/--
Definition of `bicategoricalComp` / `bicategoricalComp` 的定义

English:
definition bicategoricalComp
  signature: {f g h i : a ⟶ b} [BicategoricalCoherence g h]
  body: η ≫ otimes𝟙.hom ≫ θ

中文:
定义 bicategoricalComp
  签名: {f g h i : a ⟶ b} [BicategoricalCoherence g h]
  定义体: η ≫ otimes𝟙.hom ≫ θ
-/
def bicategoricalComp {f g h i : a ⟶ b} [BicategoricalCoherence g h]
    (η : f ⟶ g) (θ : h ⟶ i) : f ⟶ i :=
  η ≫ otimes𝟙.hom ≫ θ

-- type as \ot \gg
@[inherit_doc bicategoricalComp]
scoped[CategoryTheory.Bicategory] infixr:80 " otimes≫ " => bicategoricalComp

/--
Definition of `bicategoricalIsoComp` / `bicategoricalIsoComp` 的定义

English:
definition bicategoricalIsoComp
  signature: {f g h i : a ⟶ b} [BicategoricalCoherence g h]
  body: η ≪≫ otimes𝟙 ≪≫ θ

@[inherit_doc bicategoricalIsoComp]
scoped[CategoryTheory.Bicategory] infixr:80 " ≪otimes≫ " =>
  bicategoricalIsoComp -- type as \ll \ot \gg

中文:
定义 bicategoricalIsoComp
  签名: {f g h i : a ⟶ b} [BicategoricalCoherence g h]
  定义体: η ≪≫ otimes𝟙 ≪≫ θ

@[inherit_doc bicategoricalIsoComp]
scoped[CategoryTheory.Bicategory] infixr:80 " ≪otimes≫ " =>
  bicategoricalIsoComp -- type as \ll \ot \gg
-/
def bicategoricalIsoComp {f g h i : a ⟶ b} [BicategoricalCoherence g h]
    (η : f ≅ g) (θ : h ≅ i) : f ≅ i :=
  η ≪≫ otimes𝟙 ≪≫ θ

@[inherit_doc bicategoricalIsoComp]
scoped[CategoryTheory.Bicategory] infixr:80 " ≪otimes≫ " =>
  bicategoricalIsoComp -- type as \ll \ot \gg

namespace BicategoricalCoherence

@[simps]
/--
Instance `refl` / 实例 `refl`

English:
instance refl
  signature: (f : a ⟶ b)
  body: ⟨Iso.refl _⟩

@[simps]

中文:
实例 refl
  签名: (f : a ⟶ b)
  定义体: ⟨Iso.refl _⟩

@[simps]

Depends on / 依赖: Iso.refl
-/
instance refl (f : a ⟶ b) : BicategoricalCoherence f f :=
  ⟨Iso.refl _⟩

@[simps]
/--
Instance `whiskerLeft` / 实例 `whiskerLeft`

English:
instance whiskerLeft
  signature: (f : a ⟶ b) (g h : b ⟶ c)
  body: ⟨whiskerLeftIso f otimes𝟙⟩

@[simps]

中文:
实例 whiskerLeft
  签名: (f : a ⟶ b) (g h : b ⟶ c)
  定义体: ⟨whiskerLeftIso f otimes𝟙⟩

@[simps]

Depends on / 依赖: whiskerLeftIso
-/
instance whiskerLeft (f : a ⟶ b) (g h : b ⟶ c)
    [BicategoricalCoherence g h] : BicategoricalCoherence (f ≫ g) (f ≫ h) :=
  ⟨whiskerLeftIso f otimes𝟙⟩

@[simps]
/--
Instance `whiskerRight` / 实例 `whiskerRight`

English:
instance whiskerRight
  signature: (f g : a ⟶ b) (h : b ⟶ c)
  body: ⟨whiskerRightIso otimes𝟙 h⟩

@[simps]

中文:
实例 whiskerRight
  签名: (f g : a ⟶ b) (h : b ⟶ c)
  定义体: ⟨whiskerRightIso otimes𝟙 h⟩

@[simps]

Depends on / 依赖: whiskerRightIso
-/
instance whiskerRight (f g : a ⟶ b) (h : b ⟶ c)
    [BicategoricalCoherence f g] : BicategoricalCoherence (f ≫ h) (g ≫ h) :=
  ⟨whiskerRightIso otimes𝟙 h⟩

@[simps]
/--
Instance `tensorRight` / 实例 `tensorRight`

English:
instance tensorRight
  signature: (f : a ⟶ b) (g : b ⟶ b)
  body: ⟨(ρ_ f).symm ≪≫ (whiskerLeftIso f otimes𝟙)⟩

@[simps]

中文:
实例 tensorRight
  签名: (f : a ⟶ b) (g : b ⟶ b)
  定义体: ⟨(ρ_ f).symm ≪≫ (whiskerLeftIso f otimes𝟙)⟩

@[simps]

Depends on / 依赖: whiskerLeftIso
-/
instance tensorRight (f : a ⟶ b) (g : b ⟶ b)
    [BicategoricalCoherence (𝟙 b) g] : BicategoricalCoherence f (f ≫ g) :=
  ⟨(ρ_ f).symm ≪≫ (whiskerLeftIso f otimes𝟙)⟩

@[simps]
/--
Instance `tensorRight'` / 实例 `tensorRight'`

English:
instance tensorRight'
  signature: (f : a ⟶ b) (g : b ⟶ b)
  body: ⟨whiskerLeftIso f otimes𝟙 ≪≫ (ρ_ f)⟩

@[simps]

中文:
实例 tensorRight'
  签名: (f : a ⟶ b) (g : b ⟶ b)
  定义体: ⟨whiskerLeftIso f otimes𝟙 ≪≫ (ρ_ f)⟩

@[simps]

Depends on / 依赖: whiskerLeftIso
-/
instance tensorRight' (f : a ⟶ b) (g : b ⟶ b)
    [BicategoricalCoherence g (𝟙 b)] : BicategoricalCoherence (f ≫ g) f :=
  ⟨whiskerLeftIso f otimes𝟙 ≪≫ (ρ_ f)⟩

@[simps]
/--
Instance `left` / 实例 `left`

English:
instance left
  signature: (f g : a ⟶ b) [BicategoricalCoherence f g]
  body: ⟨fun_ f ≪≫ otimes𝟙⟩

@[simps]

中文:
实例 left
  签名: (f g : a ⟶ b) [BicategoricalCoherence f g]
  定义体: ⟨fun_ f ≪≫ otimes𝟙⟩

@[simps]

Depends on / 依赖: fun_
-/
instance left (f g : a ⟶ b) [BicategoricalCoherence f g] :
    BicategoricalCoherence (𝟙 a ≫ f) g :=
  ⟨fun_ f ≪≫ otimes𝟙⟩

@[simps]
/--
Instance `left'` / 实例 `left'`

English:
instance left'
  signature: (f g : a ⟶ b) [BicategoricalCoherence f g]
  body: ⟨otimes𝟙 ≪≫ (fun_ g).symm⟩

@[simps]

中文:
实例 left'
  签名: (f g : a ⟶ b) [BicategoricalCoherence f g]
  定义体: ⟨otimes𝟙 ≪≫ (fun_ g).symm⟩

@[simps]

Depends on / 依赖: fun_
-/
instance left' (f g : a ⟶ b) [BicategoricalCoherence f g] :
    BicategoricalCoherence f (𝟙 a ≫ g) :=
  ⟨otimes𝟙 ≪≫ (fun_ g).symm⟩

@[simps]
/--
Instance `right` / 实例 `right`

English:
instance right
  signature: (f g : a ⟶ b) [BicategoricalCoherence f g]
  body: ⟨ρ_ f ≪≫ otimes𝟙⟩

@[simps]

中文:
实例 right
  签名: (f g : a ⟶ b) [BicategoricalCoherence f g]
  定义体: ⟨ρ_ f ≪≫ otimes𝟙⟩

@[simps]
-/
instance right (f g : a ⟶ b) [BicategoricalCoherence f g] :
    BicategoricalCoherence (f ≫ 𝟙 b) g :=
  ⟨ρ_ f ≪≫ otimes𝟙⟩

@[simps]
/--
Instance `right'` / 实例 `right'`

English:
instance right'
  signature: (f g : a ⟶ b) [BicategoricalCoherence f g]
  body: ⟨otimes𝟙 ≪≫ (ρ_ g).symm⟩

@[simps]

中文:
实例 right'
  签名: (f g : a ⟶ b) [BicategoricalCoherence f g]
  定义体: ⟨otimes𝟙 ≪≫ (ρ_ g).symm⟩

@[simps]
-/
instance right' (f g : a ⟶ b) [BicategoricalCoherence f g] :
    BicategoricalCoherence f (g ≫ 𝟙 b) :=
  ⟨otimes𝟙 ≪≫ (ρ_ g).symm⟩

@[simps]
/--
Instance `assoc` / 实例 `assoc`

English:
instance assoc
  signature: (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : a ⟶ d)
  body: ⟨α_ f g h ≪≫ otimes𝟙⟩

@[simps]

中文:
实例 assoc
  签名: (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : a ⟶ d)
  定义体: ⟨α_ f g h ≪≫ otimes𝟙⟩

@[simps]
-/
instance assoc (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : a ⟶ d)
    [BicategoricalCoherence (f ≫ g ≫ h) i] :
    BicategoricalCoherence ((f ≫ g) ≫ h) i :=
  ⟨α_ f g h ≪≫ otimes𝟙⟩

@[simps]
/--
Instance `assoc'` / 实例 `assoc'`

English:
instance assoc'
  signature: (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : a ⟶ d)
  body: ⟨otimes𝟙 ≪≫ (α_ f g h).symm⟩

中文:
实例 assoc'
  签名: (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : a ⟶ d)
  定义体: ⟨otimes𝟙 ≪≫ (α_ f g h).symm⟩
-/
instance assoc' (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : a ⟶ d)
    [BicategoricalCoherence i (f ≫ g ≫ h)] :
    BicategoricalCoherence i ((f ≫ g) ≫ h) :=
  ⟨otimes𝟙 ≪≫ (α_ f g h).symm⟩

end BicategoricalCoherence

@[simp]
/--
theorem `bicategoricalComp_refl` / 定理 `bicategoricalComp_refl`

English:
theorem bicategoricalComp_refl
  given: {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h)
  statement: η otimes≫ θ = η ≫ θ
  proof: by
  dsimp [bicategoricalComp]; simp

中文:
定理 bicategoricalComp_refl
  条件: {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h)
  结论: η otimes≫ θ = η ≫ θ
  证明: by
  dsimp [bicategoricalComp]; simp

Depends on / 依赖: bicategoricalComp
-/
theorem bicategoricalComp_refl {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) : η otimes≫ θ = η ≫ θ := by
  dsimp [bicategoricalComp]; simp

end CategoryTheory
