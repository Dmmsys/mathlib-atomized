/-
Copyright (c) 2026 Benoît Guillemet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benoît Guillemet, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!

# Equivalence relations

We define internal equivalence relations (sometimes called congruences) in any category `C`, as a
structure on pairs of parallel morphisms `p₁, p₂ : R ⟶ X` .
We also define effective and universally effective equivalence relations.

We prove that equivalence relations on types provide internal equivalence relation structures in the
category of types.
In general, kernel pairs in any category are internal equivalence relations.

## References

* <https://ncatlab.org/nlab/show/congruence>

-/

@[expose] public section

universe w

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C] {D : Type*} [Category* D]
variable {R X : C} {p₁ p₂ : R ⟶ X}

/-- A typeclass for pairs of morphisms that are jointly monic. -/
/-
**CategoryTheory.JointlyMono** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A typeclass for pairs of morphisms that are jointly monic.
-/
class JointlyMono₂ {R X₁ X₂ : C} (p₁ : R ⟶ X₁) (p₂ : R ⟶ X₂) : Prop where
  right_cancellation : ∀ ⦃Y : C⦄ (f g : Y ⟶ R), f ≫ p₁ = g ≫ p₁ → f ≫ p₂ = g ≫ p₂ → f = g

/-- A reflexive relation is a jointly monic pair of parallel morphisms `p₁, p₂ : R ⟶ X`, together
with a section `r : X ⟶ R` of both `p₁` and `p₂`. -/
/-
**CategoryTheory.ReflexiveRelation** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory`。
形式化陈述：ReflexiveRelation {R X : C} (p₁ p₂ : R ⟶ X) extends JointlyMono₂ p₁ p₂ whe
re /-- `r` is the morphism witnessing reflexivity -/ r : X ⟶ R reflexivity₁ : r 
≫ p₁ = 𝟙 _
参数：p₁ p₂ : R ⟶ X。
继承自：JointlyMono₂ p₁ p₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A reflexive relation is a jointly monic pair of parallel morphisms `p₁, p₂ : R ⟶
 X`, together
with a section `r : X ⟶ R` of both `p₁` and `p₂`.
-/
structure ReflexiveRelation {R X : C} (p₁ p₂ : R ⟶ X) extends JointlyMono₂ p₁ p₂ where
  /-- `r` is the morphism witnessing reflexivity -/
  r : X ⟶ R
  reflexivity₁ : r ≫ p₁ = 𝟙 _ := by cat_disch
  reflexivity₂ : r ≫ p₂ = 𝟙 _ := by cat_disch

attribute [reassoc (attr := simp), elementwise (attr := simp)]
  ReflexiveRelation.reflexivity₁ ReflexiveRelation.reflexivity₂

/-- A symmetric relation is a jointly monic pair of parallel morphisms `p₁, p₂ : R ⟶ X` together
with a morphism `s : R ⟶ R` which interchanges `p₁` and `p₂`. -/
/-
**CategoryTheory.SymmetricRelation** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory`。
形式化陈述：SymmetricRelation {R X : C} (p₁ p₂ : R ⟶ X) extends JointlyMono₂ p₁ p₂ whe
re /-- `s` is the morphism witnessing symmetry -/ s : R ⟶ R symmetry₁ : s ≫ p₁ =
 p₂
参数：p₁ p₂ : R ⟶ X。
继承自：JointlyMono₂ p₁ p₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A symmetric relation is a jointly monic pair of parallel morphisms `p₁, p₂ : R ⟶
 X` together
with a morphism `s : R ⟶ R` which interchanges `p₁` and `p₂`.
-/
structure SymmetricRelation {R X : C} (p₁ p₂ : R ⟶ X) extends JointlyMono₂ p₁ p₂ where
  /-- `s` is the morphism witnessing symmetry -/
  s : R ⟶ R
  symmetry₁ : s ≫ p₁ = p₂ := by cat_disch
  symmetry₂ : s ≫ p₂ = p₁ := by cat_disch

attribute [reassoc (attr := simp), elementwise (attr := simp)]
  SymmetricRelation.symmetry₁ SymmetricRelation.symmetry₂

/-- A transitive relation is a jointly monic pair of parallel morphisms `p₁, p₂ : R ⟶ X`, together
with a limiting pullback cone `c` for `p₁` and `p₂` and a map `c.pt ⟶ R` which factors the two
projections `c.pt ⟶ X` through `R`. -/
/-
**CategoryTheory.TransitiveRelation** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory`。
形式化陈述：TransitiveRelation {R X : C} (p₁ p₂ : R ⟶ X) extends JointlyMono₂ p₁ p₂ wh
ere /-- `c` is a pullback cone for `p₁` and `p₂` -/ c : PullbackCone p₂ p₁ /-- `
c` is limiting -/ isLimit : IsLimit c /-- `t` is the morphism witnessing transit
ivity -/ t : c.pt ⟶ R transitivity₁ : t ≫ p₁ = c.fst ≫ p₁
参数：p₁ p₂ : R ⟶ X。
继承自：JointlyMono₂ p₁ p₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A transitive relation is a jointly monic pair of parallel morphisms `p₁, p₂ : R 
⟶ X`, together
with a limiting pullback cone `c` for `p₁` and `p₂` and a map `c.pt ⟶ R` which f
actors the two
projections `c.pt ⟶ X` through `R`.
-/
structure TransitiveRelation {R X : C} (p₁ p₂ : R ⟶ X) extends JointlyMono₂ p₁ p₂ where
  /-- `c` is a pullback cone for `p₁` and `p₂` -/
  c : PullbackCone p₂ p₁
  /-- `c` is limiting -/
  isLimit : IsLimit c
  /-- `t` is the morphism witnessing transitivity -/
  t : c.pt ⟶ R
  transitivity₁ : t ≫ p₁ = c.fst ≫ p₁ := by cat_disch
  transitivity₂ : t ≫ p₂ = c.snd ≫ p₂ := by cat_disch

initialize_simps_projections TransitiveRelation (-isLimit)

attribute [reassoc (attr := simp), elementwise (attr := simp)]
  TransitiveRelation.transitivity₁ TransitiveRelation.transitivity₂

/-- An equivalence relation is a reflexive, symmetric and transitive relation. -/
/-
**CategoryTheory.EquivalenceRelation** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory
`。
形式化陈述：{C : Type u_1} → [inst : CategoryTheory.Category.{v_1, u_1} C] → {R X : C}
 → (R ⟶ X) → (R ⟶ X) → Type (max u_1 v_1)
参数：R ⟶ X；R ⟶ X；max u_1 v_1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence relation is a reflexive, symmetric and transitive relation.
-/
structure EquivalenceRelation {R X : C} (p₁ p₂ : R ⟶ X) extends ReflexiveRelation p₁ p₂,
  SymmetricRelation p₁ p₂, TransitiveRelation p₁ p₂

/-- Reinterpret an equivalence relation as a reflexive relation. -/
add_decl_doc EquivalenceRelation.toReflexiveRelation

/-- Reinterpret an equivalence relation as a symmetric relation. -/
add_decl_doc EquivalenceRelation.toSymmetricRelation

/-- Reinterpret an equivalence relation as a transitive relation. -/
add_decl_doc EquivalenceRelation.toTransitiveRelation

/-- The typeclass associated with the structure `EquivalenceRelation`. -/
/-
**CategoryTheory.IsEquivalenceRelation** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheo
ry`。
形式化陈述：{C : Type u_1} → [inst : CategoryTheory.Category.{v_1, u_1} C] → {R X : C}
 → (R ⟶ X) → (R ⟶ X) → Prop
参数：R ⟶ X；R ⟶ X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The typeclass associated with the structure `EquivalenceRelation`.
-/
class IsEquivalenceRelation {R X : C} (p₁ p₂ : R ⟶ X) : Prop where
  nonempty_equivalenceRelation : Nonempty (EquivalenceRelation p₁ p₂)
/-
**CategoryTheory.EquivalenceRelation.isEquivalenceRelation** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.EquivalenceRelation`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {R X : C} {
p₁ p₂ : R ⟶ X}   (h : CategoryTheory.EquivalenceRelation p₁ p₂), CategoryTheory.
IsEquivalenceRelation p₁ p₂
参数：h : CategoryTheory.EquivalenceRelation p₁ p₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma EquivalenceRelation.isEquivalenceRelation (h : EquivalenceRelation p₁ p₂) :
    IsEquivalenceRelation p₁ p₂ where
  nonempty_equivalenceRelation := ⟨h⟩

/-- A kernel pair gives rise to an equivalence relation. -/
/-
**CategoryTheory.IsKernelPair.equivalenceRelation** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.IsKernelPair`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {X 
Y : C} →       (f : X ⟶ Y) →         {R : C} →           (p₁ p₂ : R ⟶ X) →      
       {t : CategoryTheory.Limits.PullbackCone p₂ p₁} →               CategoryTh
eory.Limits.IsLimit t →                 CategoryTheory.IsKernelPair f p₁ p₂ → Ca
tegoryTheory.EquivalenceRelation p₁ p₂
参数：f : X ⟶ Y；p₁ p₂ : R ⟶ X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A kernel pair gives rise to an equivalence relation.
-/
noncomputable def IsKernelPair.equivalenceRelation {X Y : C} (f : X ⟶ Y) {R : C} (p₁ p₂ : R ⟶ X)
    {t : PullbackCone p₂ p₁} (ht : IsLimit t) (h : IsKernelPair f p₁ p₂) :
    EquivalenceRelation p₁ p₂ where
  right_cancellation A a b h₁ h₂ := h.hom_ext h₁ h₂
  r := h.lift (𝟙 _) (𝟙 _) (by simp)
  s := h.lift p₂ p₁ h.w.symm
  c := t
  isLimit := ht
  t := h.lift (t.fst ≫ p₁) (t.snd ≫ p₂) (by simp [reassoc_of% t.condition, h.w])

/-- Given a functor `F : C ⥤ D`, if `F.map p₁` and `F.map p₂` form a jointly monic pair of
morphisms, then `F` preserves reflexive relations. -/
/-
**CategoryTheory.ReflexiveRelation.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.ReflexiveRelation`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {D 
: Type u_2} →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         {R
 X : C} →           {p₁ p₂ : R ⟶ X} →             CategoryTheory.ReflexiveRelati
on p₁ p₂ →               (F : CategoryTheory.Functor C D) →                 [Cat
egoryTheory.JointlyMono₂ (F.map p₁) (F.map p₂)] →                   CategoryTheo
ry.ReflexiveRelation (F.map p₁) (F.map p₂)
参数：F : CategoryTheory.Functor C D；F.map p₁；F.map p₂；F.map p₁；F.map p₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor `F : C ⥤ D`, if `F.map p₁` and `F.map p₂` form a jointly monic p
air of
morphisms, then `F` preserves reflexive relations.
-/
def ReflexiveRelation.map (e : ReflexiveRelation p₁ p₂) (F : C ⥤ D)
    [JointlyMono₂ (F.map p₁) (F.map p₂)] :
    ReflexiveRelation (F.map p₁) (F.map p₂) where
  r := F.map e.r
  reflexivity₁ := by simp [← F.map_comp]
  reflexivity₂ := by simp [← F.map_comp]

/-- Given a functor `F : C ⥤ D`, if `F.map p₁` and `F.map p₂` form a jointly monic pair of
morphisms, then `F` preserves symmetric relations. -/
/-
**CategoryTheory.SymmetricRelation.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.SymmetricRelation`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {D 
: Type u_2} →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         {R
 X : C} →           {p₁ p₂ : R ⟶ X} →             CategoryTheory.SymmetricRelati
on p₁ p₂ →               (F : CategoryTheory.Functor C D) →                 [Cat
egoryTheory.JointlyMono₂ (F.map p₁) (F.map p₂)] →                   CategoryTheo
ry.SymmetricRelation (F.map p₁) (F.map p₂)
参数：F : CategoryTheory.Functor C D；F.map p₁；F.map p₂；F.map p₁；F.map p₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor `F : C ⥤ D`, if `F.map p₁` and `F.map p₂` form a jointly monic p
air of
morphisms, then `F` preserves symmetric relations.
-/
def SymmetricRelation.map (e : SymmetricRelation p₁ p₂) (F : C ⥤ D)
    [JointlyMono₂ (F.map p₁) (F.map p₂)] :
    SymmetricRelation (F.map p₁) (F.map p₂) where
  s := F.map e.s
  symmetry₁ := by simp [← F.map_comp]
  symmetry₂ := by simp [← F.map_comp]

/-- Given a functor `F : C ⥤ D`, if `F.map p₁` and `F.map p₂` form a jointly monic pair of
morphisms, and if `F` preserves pullbacks, then `F` preserves reflexive relations. -/
/-
**CategoryTheory.TransitiveRelation.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.TransitiveRelation`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {D 
: Type u_2} →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         {R
 X : C} →           {p₁ p₂ : R ⟶ X} →             CategoryTheory.TransitiveRelat
ion p₁ p₂ →               (F : CategoryTheory.Functor C D) →                 [Ca
tegoryTheory.JointlyMono₂ (F.map p₁) (F.map p₂)] →                   [CategoryTh
eory.Limits.PreservesLimitsOfShape CategoryTheory.Limits.WalkingCospan F] →     
                CategoryTheory.TransitiveRelation (F.map p₁) (F.map p₂)
参数：F : CategoryTheory.Functor C D；F.map p₁；F.map p₂；F.map p₁；F.map p₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a functor `F : C ⥤ D`, if `F.map p₁` and `F.map p₂` form a jointly monic p
air of
morphisms, and if `F` preserves pullbacks, then `F` preserves reflexive relation
s.
-/
noncomputable def TransitiveRelation.map (e : TransitiveRelation p₁ p₂) (F : C ⥤ D)
    [JointlyMono₂ (F.map p₁) (F.map p₂)] [PreservesLimitsOfShape WalkingCospan F] :
    TransitiveRelation (F.map p₁) (F.map p₂) where
  t := F.map e.t
  c := e.c.map F
  isLimit := isLimitPullbackConeMapOfIsLimit F e.c.condition (.ofIsoLimit e.isLimit e.c.eta)
  transitivity₁ :=
    (F.map_comp _ _).symm.trans ((congr(F.map $e.transitivity₁)).trans (F.map_comp _ _))
  transitivity₂ :=
    (F.map_comp _ _).symm.trans ((congr(F.map $e.transitivity₂)).trans (F.map_comp _ _))

end CategoryTheory

namespace TypeCat

open CategoryTheory Limits

variable {X : Type w} (φ : X → X → Prop)

/-- The subtype of `X × X` corresponding to a relation `φ : X → X → Prop`. -/
/-
**TypeCat.ROfRel** 是 Mathlib 中的一个缩写定义，位于命名空间 `TypeCat`。
形式化陈述：ROfRel
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subtype of `X × X` corresponding to a relation `φ : X → X → Prop`.
-/
abbrev ROfRel := Subtype φ.uncurry

/-- The first projection `ROfRel ⟶ X`. -/
/-
**TypeCat.p** 是 Mathlib 中的一个缩写定义，位于命名空间 `TypeCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first projection `ROfRel ⟶ X`.
-/
abbrev p₁OfRel : ROfRel φ ⟶ X := ↾(Prod.fst ∘ Subtype.val)

/-- The second projection `ROfRel ⟶ X`. -/
/-
**TypeCat.p** 是 Mathlib 中的一个缩写定义，位于命名空间 `TypeCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second projection `ROfRel ⟶ X`.
-/
abbrev p₂OfRel : ROfRel φ ⟶ X := ↾(Prod.snd ∘ Subtype.val)
/-
**TypeCat.jointlyMono** 是 Mathlib 中的一个引理，位于命名空间 `TypeCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma jointlyMono₂ :
    JointlyMono₂ (p₁OfRel φ) (p₂OfRel φ) where
  right_cancellation Y f g h₁ h₂ := by
    ext y
    · exact congr($h₁ y)
    · exact congr($h₂ y)

/-- Standard reflexive relations on types are internal reflexive relations in the category of
types. -/
/-
**TypeCat.ReflexiveRelation.ofRefl** 是 Mathlib 中的一个定义，位于命名空间 `TypeCat.ReflexiveR
elation`。
形式化陈述：{X : Type w} →   {φ : X → X → Prop} → Std.Refl φ → CategoryTheory.Reflexiv
eRelation (TypeCat.p₁OfRel φ) (TypeCat.p₂OfRel φ)
参数：TypeCat.p₁OfRel φ；TypeCat.p₂OfRel φ。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `TypeCat.jointlyMono₂`：jointlyMono₂ : JointlyMono₂ (p₁OfRel φ) (p₂OfRel φ
) where right_cancellation Y f g h₁ h₂
· 使用定理 `Std.Refl.refl`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Refl r] (a 
: α), r a a

--- 原说明 ---
Standard reflexive relations on types are internal reflexive relations in the ca
tegory of
types.
-/
def ReflexiveRelation.ofRefl {X : Type w} {φ : X → X → Prop} (hφ : Std.Refl φ) :
    ReflexiveRelation (p₁OfRel φ) (p₂OfRel φ) where
  __ := jointlyMono₂ φ
  r := (↾(fun x => ⟨⟨x, x⟩, hφ.refl x⟩))

/-- Standard symmetric relations on types are internal symmetric relations in the category of
types. -/
/-
**TypeCat.SymmetricRelation.ofSymmetric** 是 Mathlib 中的一个定义，位于命名空间 `TypeCat.Symme
tricRelation`。
形式化陈述：{X : Type w} →   {φ : X → X → Prop} → [Std.Symm φ] → CategoryTheory.Symmet
ricRelation (TypeCat.p₁OfRel φ) (TypeCat.p₂OfRel φ)
参数：TypeCat.p₁OfRel φ；TypeCat.p₂OfRel φ。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `TypeCat.jointlyMono₂`：jointlyMono₂ : JointlyMono₂ (p₁OfRel φ) (p₂OfRel φ
) where right_cancellation Y f g h₁ h₂

--- 原说明 ---
Standard symmetric relations on types are internal symmetric relations in the ca
tegory of
types.
-/
def SymmetricRelation.ofSymmetric {X : Type w} {φ : X → X → Prop} [Std.Symm φ] :
    SymmetricRelation (p₁OfRel φ) (p₂OfRel φ) where
  __ := jointlyMono₂ φ
  s := ↾(fun ⟨⟨x₁, x₂⟩, h⟩ => ⟨⟨x₂, x₁⟩, symm h⟩)

/-- Standard transitive relations on types are internal transitive relations in the category of
types. -/
/-
**TypeCat.TransitiveRelation.ofIsTrans** 是 Mathlib 中的一个定义，位于命名空间 `TypeCat.Transi
tiveRelation`。
形式化陈述：{X : Type w} →   {φ : X → X → Prop} → IsTrans X φ → CategoryTheory.Transit
iveRelation (TypeCat.p₁OfRel φ) (TypeCat.p₂OfRel φ)
参数：TypeCat.p₁OfRel φ；TypeCat.p₂OfRel φ。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `TypeCat.jointlyMono₂`：jointlyMono₂ : JointlyMono₂ (p₁OfRel φ) (p₂OfRel φ
) where right_cancellation Y f g h₁ h₂

--- 原说明 ---
Standard transitive relations on types are internal transitive relations in the 
category of
types.
-/
def TransitiveRelation.ofIsTrans {X : Type w} {φ : X → X → Prop} (hφ : IsTrans _ φ) :
    TransitiveRelation (p₁OfRel φ) (p₂OfRel φ) where
  __ := jointlyMono₂ φ
  c := Types.pullbackCone _ _
  isLimit := (Types.pullbackLimitCone _ _).isLimit
  t := ↾(fun ⟨⟨⟨⟨x₁, _⟩, h⟩, ⟨⟨_, x₂'⟩, h'⟩⟩, h₁₂⟩ => by
    dsimp at h₁₂
    rw [← h₁₂] at h'
    refine ⟨⟨x₁, x₂'⟩, hφ.trans _ _ _ h h'⟩)

/-- Standard equivalence relations on types are internal equivalence relations in the category of
types. -/
/-
**TypeCat.EquivalenceRelation.ofEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `TypeCat.E
quivalenceRelation`。
形式化陈述：{X : Type w} →   {φ : X → X → Prop} → Equivalence φ → CategoryTheory.Equiv
alenceRelation (TypeCat.p₁OfRel φ) (TypeCat.p₂OfRel φ)
参数：TypeCat.p₁OfRel φ；TypeCat.p₂OfRel φ。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equivalence.stdRefl`：Equivalence.stdRefl (h : Equivalence r) : Std.Refl 
r where refl
· 使用定理 `Equivalence.stdSymm`：Equivalence.stdSymm (h : Equivalence r) : Std.Symm 
r where symm _ _
· 使用定理 `Equivalence.isTrans`：Equivalence.isTrans (h : Equivalence r) : IsTrans α
 r

--- 原说明 ---
Standard equivalence relations on types are internal equivalence relations in th
e category of
types.
-/
def EquivalenceRelation.ofEquivalence {X : Type w} {φ : X → X → Prop} (hφ : Equivalence φ) :
    EquivalenceRelation (p₁OfRel φ) (p₂OfRel φ) where
  __ := ReflexiveRelation.ofRefl hφ.stdRefl
  __ := let := hφ.stdSymm; SymmetricRelation.ofSymmetric
  __ := TransitiveRelation.ofIsTrans hφ.isTrans

variable {R : Type w} (p₁ p₂ : R ⟶ X)

/-- The relation on a type `X` coming from a pair of maps `R ⟶ X`. -/
/-
**TypeCat.Rel.ofPair** 是 Mathlib 中的一个定义，位于命名空间 `TypeCat.Rel`。
形式化陈述：{X R : Type w} → (R ⟶ X) → (R ⟶ X) → X → X → Prop
参数：R ⟶ X；R ⟶ X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The relation on a type `X` coming from a pair of maps `R ⟶ X`.
-/
abbrev Rel.ofPair := fun x₁ x₂ => ∃ r : R, p₁ r = x₁ ∧ p₂ r = x₂

variable {p₁ p₂}

/-- An internal reflexive relation in the category of types gives rise to a standard reflexive
relation. -/
/-
**TypeCat.refl_of_reflexiveRelation** 是 Mathlib 中的一个引理，位于命名空间 `TypeCat`。
形式化陈述：refl_of_reflexiveRelation (e : ReflexiveRelation p₁ p₂) : Std.Refl (Rel.of
Pair p₁ p₂) where refl x
参数：e : ReflexiveRelation p₁ p₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ReflexiveRelation.reflexivity₁`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] {R X : C} {p₁ p₂ : R ⟶ X}   (self : Catego
ryTheory.ReflexiveRelation p₁ p₂), …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.ReflexiveRelation.reflexivity₂_apply`：∀ {C : Type u_1} [i
nst : CategoryTheory.Category.{v_1, u_1} C] {R X : C} {p₁ p₂ : R ⟶ X}   (self : 
CategoryTheory.ReflexiveRelation p₁ p₂) {…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
An internal reflexive relation in the category of types gives rise to a standard
 reflexive
relation.
-/
lemma refl_of_reflexiveRelation (e : ReflexiveRelation p₁ p₂) :
    Std.Refl (Rel.ofPair p₁ p₂) where
  refl x := ⟨e.r x, congr($e.reflexivity₁ x), by simp⟩

/-- An internal symmetric relation in the category of types gives rise to a standard symmetric
relation. -/
/-
**TypeCat.symm_of_symmetricRelation** 是 Mathlib 中的一个引理，位于命名空间 `TypeCat`。
形式化陈述：symm_of_symmetricRelation (e : SymmetricRelation p₁ p₂) : Std.Symm (Rel.of
Pair p₁ p₂) where symm x₁ x₂
参数：e : SymmetricRelation p₁ p₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.SymmetricRelation.symmetry₁_apply`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] {R X : C} {p₁ p₂ : R ⟶ X}   (self : Cat
egoryTheory.SymmetricRelation p₁ p₂) {…
· 使用定理 `CategoryTheory.SymmetricRelation.symmetry₂_apply`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] {R X : C} {p₁ p₂ : R ⟶ X}   (self : Cat
egoryTheory.SymmetricRelation p₁ p₂) {…

--- 原说明 ---
An internal symmetric relation in the category of types gives rise to a standard
 symmetric
relation.
-/
lemma symm_of_symmetricRelation (e : SymmetricRelation p₁ p₂) : Std.Symm (Rel.ofPair p₁ p₂) where
  symm x₁ x₂ := fun ⟨r, hr₁, hr₂⟩ ↦ ⟨e.s r, by simpa, by simpa⟩

@[deprecated (since := "2026-06-10")]
alias symmetric_of_symmetricRelation := symm_of_symmetricRelation

/-- An internal transitive relation in the category of types gives rise to a standard transitive
relation. -/
/-
**TypeCat.isTrans_of_transitiveRelation** 是 Mathlib 中的一个引理，位于命名空间 `TypeCat`。
形式化陈述：isTrans_of_transitiveRelation (e : TransitiveRelation p₁ p₂) : IsTrans _ (
Rel.ofPair p₁ p₂) where trans x₁ x₂ x₃
参数：e : TransitiveRelation p₁ p₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.TransitiveRelation.transitivity₁_apply`：∀ {C : Type u_1} 
[inst : CategoryTheory.Category.{v_1, u_1} C] {R X : C} {p₁ p₂ : R ⟶ X}   (self 
: CategoryTheory.TransitiveRelation p₁ p₂) …
· 使用定理 `CategoryTheory.Limits.PullbackCone.IsLimit.equivPullbackObj_symm_apply_f
st`：∀ {X Y S : Type v} {f : X ⟶ S} {g : Y ⟶ S} {c : CategoryTheory.Limits.Pullba
ckCone f g}   (hc : CategoryTheory.Limits.IsLimit c) (x : Catego…
· 使用定理 `CategoryTheory.TransitiveRelation.transitivity₂_apply`：∀ {C : Type u_1} 
[inst : CategoryTheory.Category.{v_1, u_1} C] {R X : C} {p₁ p₂ : R ⟶ X}   (self 
: CategoryTheory.TransitiveRelation p₁ p₂) …
· 使用定理 `CategoryTheory.Limits.PullbackCone.IsLimit.equivPullbackObj_symm_apply_s
nd`：∀ {X Y S : Type v} {f : X ⟶ S} {g : Y ⟶ S} {c : CategoryTheory.Limits.Pullba
ckCone f g}   (hc : CategoryTheory.Limits.IsLimit c) (x : Catego…

--- 原说明 ---
An internal transitive relation in the category of types gives rise to a standar
d transitive
relation.
-/
lemma isTrans_of_transitiveRelation (e : TransitiveRelation p₁ p₂) :
    IsTrans _ (Rel.ofPair p₁ p₂) where
  trans x₁ x₂ x₃ := by
    refine fun ⟨r, ⟨hr₁, hr₂⟩⟩ ⟨r', ⟨hr₁', hr₂'⟩⟩ =>
      ⟨e.t ((PullbackCone.IsLimit.equivPullbackObj e.isLimit).symm ⟨(r, r'), hr₂.trans hr₁'.symm⟩),
        ⟨?_, ?_⟩⟩
    all_goals simpa

/-- An internal equivalence relation in the category of types gives rise to a standard equivalence
relation. -/
/-
**TypeCat.equivalence_of_equivalenceRelation** 是 Mathlib 中的一个引理，位于命名空间 `TypeCat`
。
形式化陈述：equivalence_of_equivalenceRelation (e : EquivalenceRelation p₁ p₂) : Equiv
alence (Rel.ofPair p₁ p₂) where refl
参数：e : EquivalenceRelation p₁ p₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.Refl.refl`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Refl r] (a 
: α), r a a
· 使用引理 `TypeCat.refl_of_reflexiveRelation`：refl_of_reflexiveRelation (e : Reflex
iveRelation p₁ p₂) : Std.Refl (Rel.ofPair p₁ p₂) where refl x
· 使用定理 `Std.Symm.symm`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Symm r] (a 
b : α), r a b → r b a
· 使用引理 `TypeCat.symm_of_symmetricRelation`：symm_of_symmetricRelation (e : Symmet
ricRelation p₁ p₂) : Std.Symm (Rel.ofPair p₁ p₂) where symm x₁ x₂
· 使用定理 `IsTrans.trans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsTrans α r] 
(a b c : α), r a b → r b c → r a c
· 使用引理 `TypeCat.isTrans_of_transitiveRelation`：isTrans_of_transitiveRelation (e 
: TransitiveRelation p₁ p₂) : IsTrans _ (Rel.ofPair p₁ p₂) where trans x₁ x₂ x₃

--- 原说明 ---
An internal equivalence relation in the category of types gives rise to a standa
rd equivalence
relation.
-/
lemma equivalence_of_equivalenceRelation (e : EquivalenceRelation p₁ p₂) :
    Equivalence (Rel.ofPair p₁ p₂) where
  refl := (refl_of_reflexiveRelation e.toReflexiveRelation).refl
  symm := symm_of_symmetricRelation e.toSymmetricRelation |>.symm _ _
  trans := (isTrans_of_transitiveRelation e.toTransitiveRelation).trans _ _ _

end TypeCat

namespace CategoryTheory

open Limits

variable {C : Type*} [Category* C]
variable {R A : C} (p₁ p₂ : R ⟶ A)

section Effective

/-- An effective equivalence relation is an equivalence relation `p₁, p₂ : R ⟶ A` together with a
morphism `π : A ⟶ B` such that the resulting square is both a pullback square and a pushout
square. -/
/-
**CategoryTheory.EffectiveEquivalenceRelation** 是 Mathlib 中的一个归纳类型，位于命名空间 `Categ
oryTheory`。
形式化陈述：{C : Type u_1} → [inst : CategoryTheory.Category.{v_1, u_1} C] → {R A : C}
 → (R ⟶ A) → (R ⟶ A) → Type (max u_1 v_1)
参数：R ⟶ A；R ⟶ A；max u_1 v_1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An effective equivalence relation is an equivalence relation `p₁, p₂ : R ⟶ A` to
gether with a
morphism `π : A ⟶ B` such that the resulting square is both a pullback square an
d a pushout
square.
-/
structure EffectiveEquivalenceRelation {R A : C} (p₁ p₂ : R ⟶ A) extends EquivalenceRelation p₁ p₂
    where
  /-- `B` is the "quotient" of the relation -/
  B : C
  /-- `π` is the "quotient map" of the relation -/
  π : A ⟶ B
  isKernelPair : IsKernelPair π p₁ p₂
  isPushout : IsPushout p₁ p₂ π π

/-- The typeclass associated with the structure `EffectiveEquivalenceRelation`. -/
/-
**CategoryTheory.IsEffectiveEquivalenceRelation** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cat
egoryTheory`。
形式化陈述：{C : Type u_1} → [inst : CategoryTheory.Category.{v_1, u_1} C] → {R A : C}
 → (R ⟶ A) → (R ⟶ A) → Prop
参数：R ⟶ A；R ⟶ A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The typeclass associated with the structure `EffectiveEquivalenceRelation`.
-/
class IsEffectiveEquivalenceRelation {R A : C} (p₁ p₂ : R ⟶ A) : Prop where
  nonempty_effectiveEquivalenceRelation : Nonempty (EffectiveEquivalenceRelation p₁ p₂)

/-- Given an effective equivalence relation structure `e` on `p₁, p₂ : R ⟶ A`, the morphism
`e.π : A ⟶ e.B` makes `e.B` a coequalizer of `p₁` and `p₂`. -/
/-
**CategoryTheory.EffectiveEquivalenceRelation.isCoequalizer** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.EffectiveEquivalenceRelation`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {R 
A : C} →       (p₁ p₂ : R ⟶ A) →         (e : CategoryTheory.EffectiveEquivalenc
eRelation p₁ p₂) →           CategoryTheory.Limits.IsColimit (CategoryTheory.Lim
its.Cofork.ofπ e.π ⋯)
参数：p₁ p₂ : R ⟶ A；e : CategoryTheory.EffectiveEquivalenceRelation p₁ p₂；CategoryT
heory.Limits.Cofork.ofπ e.π ⋯。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.EffectiveEquivalenceRelation.isPushout`：∀ {C : Type u_1} 
[inst : CategoryTheory.Category.{v_1, u_1} C] {R A : C} {p₁ p₂ : R ⟶ A}   (self 
: CategoryTheory.EffectiveEquivalenceRelati…

--- 原说明 ---
Given an effective equivalence relation structure `e` on `p₁, p₂ : R ⟶ A`, the m
orphism
`e.π : A ⟶ e.B` makes `e.B` a coequalizer of `p₁` and `p₂`.
-/
noncomputable def EffectiveEquivalenceRelation.isCoequalizer {R A : C} (p₁ p₂ : R ⟶ A)
    (e : EffectiveEquivalenceRelation p₁ p₂) :
    IsColimit (Cofork.ofπ e.π e.isPushout.w) :=
  e.isPushout.isLimitFork
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (e : EffectiveEquivalenceRelation p₁ p₂) :
    IsRegularEpi e.π where
  regularEpi := ⟨Cofork.IsColimit.regularEpi e.isCoequalizer⟩

/-- A universally effective equivalence relation is an effective equivalence relation
`p₁, p₂ : R ⟶ A` such that the corresponding morphism `π : A ⟶ B` is a universal effective
epimorphism. -/
/-
**CategoryTheory.UniversallyEffectiveEquivalenceRelation** 是 Mathlib 中的一个归纳类型，位于
命名空间 `CategoryTheory`。
形式化陈述：{C : Type u_1} → [inst : CategoryTheory.Category.{v_1, u_1} C] → {R A : C}
 → (R ⟶ A) → (R ⟶ A) → Type (max u_1 v_1)
参数：R ⟶ A；R ⟶ A；max u_1 v_1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A universally effective equivalence relation is an effective equivalence relatio
n
`p₁, p₂ : R ⟶ A` such that the corresponding morphism `π : A ⟶ B` is a universal
 effective
epimorphism.
-/
structure UniversallyEffectiveEquivalenceRelation {R A : C} (p₁ p₂ : R ⟶ A)
    extends EffectiveEquivalenceRelation p₁ p₂ where
  universally_effectiveEpi_π : MorphismProperty.universally (fun _ _ f => EffectiveEpi f)
    toEffectiveEquivalenceRelation.π

/-- The typeclass associated with the structure `UniversallyEffectiveEquivalenceRelation`. -/
/-
**CategoryTheory.IsUniversallyEffectiveEquivalenceRelation** 是 Mathlib 中的一个归纳类型，
位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u_1} → [inst : CategoryTheory.Category.{v_1, u_1} C] → {R A : C}
 → (R ⟶ A) → (R ⟶ A) → Prop
参数：R ⟶ A；R ⟶ A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The typeclass associated with the structure `UniversallyEffectiveEquivalenceRela
tion`.
-/
class IsUniversallyEffectiveEquivalenceRelation {R A : C} (p₁ p₂ : R ⟶ A) : Prop where
  nonempty_universallyEffectiveEquivalenceRelation :
    Nonempty (UniversallyEffectiveEquivalenceRelation p₁ p₂)

variable (C) in
/-- A category `C` is a universally exact category if all equivalence relations in `C` are
universally effective equivalence relations. -/
/-
**CategoryTheory.IsUniversallyEffectiveEquivalenceRelationCategory** 是 Mathlib 中
的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：(C : Type u_1) → [CategoryTheory.Category.{v_1, u_1} C] → {R A : C} → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category `C` is a universally exact category if all equivalence relations in `
C` are
universally effective equivalence relations.
-/
class IsUniversallyEffectiveEquivalenceRelationCategory where
  isUniversallyEffectiveEquivalenceRelation (p₁ p₂ : R ⟶ A) [IsEquivalenceRelation p₁ p₂] :
    IsUniversallyEffectiveEquivalenceRelation p₁ p₂

end Effective

end CategoryTheory

