/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts

/-!
# Preservation of finite (co)limits.

These functors are also known as left exact (flat) or right exact functors when the categories
involved are abelian, or more generally, finitely (co)complete.

## Related results
* `CategoryTheory.Limits.preservesFiniteLimitsOfPreservesEqualizersAndFiniteProducts` :
  see `Mathlib/CategoryTheory/Limits/Constructions/LimitsOfProductsAndEqualizers.lean`.
  Also provides the dual version.
* `CategoryTheory.Limits.preservesFiniteLimitsIffFlat` :
  see `Mathlib/CategoryTheory/Functor/Flat.lean`.

-/

public section


open CategoryTheory

namespace CategoryTheory.Limits

-- declare the `v`'s first; see `CategoryTheory.Category` for an explanation
universe u w w₂ v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]
variable {J : Type w} [SmallCategory J] {K : J ⥤ C}

/-- A functor is said to preserve finite limits, if it preserves all limits of shape `J`,
where `J : Type` is a finite category.
-/
/-
**CategoryTheory.Limits.PreservesFiniteLimits** 是 Mathlib 中的一个类，位于命名空间 `Category
Theory.Limits`。
形式化陈述：PreservesFiniteLimits (F : C ⥤ D) : Prop where preservesFiniteLimits : for
all (J : Type) [SmallCategory J] [FinCategory J], PreservesLimitsOfShape J F
参数：F : C ⥤ D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor is said to preserve finite limits, if it preserves all limits of shape
 `J`,
where `J : Type` is a finite category.
-/
class PreservesFiniteLimits (F : C ⥤ D) : Prop where
  preservesFiniteLimits :
    ∀ (J : Type) [SmallCategory J] [FinCategory J], PreservesLimitsOfShape J F := by infer_instance

attribute [instance] PreservesFiniteLimits.preservesFiniteLimits

/-- Preserving finite limits also implies preserving limits over finite shapes in higher universes,
though through a noncomputable instance. -/
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Preserving finite limits also implies preserving limits over finite shapes in hi
gher universes,
though through a noncomputable instance.
-/
instance (priority := 100) preservesLimitsOfShapeOfPreservesFiniteLimits (F : C ⥤ D)
    [PreservesFiniteLimits F] (J : Type w) [SmallCategory J] [FinCategory J] :
    PreservesLimitsOfShape J F := by
  apply preservesLimitsOfShape_of_equiv (FinCategory.equivAsType J)

-- This is a dangerous instance as it has unbound universe variables.
/-- If we preserve limits of some arbitrary size, then we preserve all finite limits. -/
/-
**CategoryTheory.Limits.PreservesLimitsOfSize.preservesFiniteLimits** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.Limits.PreservesLimitsOfSize`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor C D)
 [CategoryTheory.Limits.PreservesLimitsOfSize.{w, w₂, v₁, v₂, u₁, u₂} F],   Cate
goryTheory.Limits.PreservesFiniteLimits F
参数：F : CategoryTheory.Functor C D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesSmallestLimits_of_preservesLimits`：preser
vesSmallestLimits_of_preservesLimits (F : C ⥤ D) [PreservesLimitsOfSize.{v₃, u₃}
 F] : PreservesLimitsOfSize.{0, 0} F
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_of_equiv`：preservesLimitsOf
Shape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D) [Pres
ervesLimitsOfShape J F] : PreservesLimitsOf…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If we preserve limits of some arbitrary size, then we preserve all finite limits
.
-/
lemma PreservesLimitsOfSize.preservesFiniteLimits (F : C ⥤ D)
    [PreservesLimitsOfSize.{w, w₂} F] : PreservesFiniteLimits F where
  preservesFiniteLimits J (sJ : SmallCategory J) fJ := by
    have := preservesSmallestLimits_of_preservesLimits F
    exact preservesLimitsOfShape_of_equiv (FinCategory.equivAsType J) F

-- Added as a specialization of the dangerous instance above, for limits indexed in Type 0.
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 120) PreservesLimitsOfSize0.preservesFiniteLimits
    (F : C ⥤ D) [PreservesLimitsOfSize.{0, 0} F] : PreservesFiniteLimits F :=
  PreservesLimitsOfSize.preservesFiniteLimits F

-- An alternative specialization of the dangerous instance for small limits.
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 120) PreservesLimits.preservesFiniteLimits (F : C ⥤ D)
    [PreservesLimits F] : PreservesFiniteLimits F :=
  PreservesLimitsOfSize.preservesFiniteLimits F

attribute [local instance] uliftCategory in
/-- We can always derive `PreservesFiniteLimits C` by showing that we are preserving limits at an
arbitrary universe. -/
/-
**CategoryTheory.Limits.preservesFiniteLimits_of_preservesFiniteLimitsOfSize** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesFiniteLimits_of_preservesFiniteLimitsOfSize (F : C ⥤ D) (h : fora
ll (J : Type w) {𝒥 : SmallCategory J} (_ : @FinCategory J 𝒥), PreservesLimitsOfS
hape J F) : PreservesFiniteLimits F where preservesFiniteLimits J (_ : SmallCate
gory J) _
参数：F : C ⥤ D；h : forall (J : Type w) {𝒥 : SmallCategory J} (_ : @FinCategory J 𝒥
), PreservesLimitsOfShape J F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_of_equiv`：preservesLimitsOf
Shape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D) [Pres
ervesLimitsOfShape J F] : PreservesLimitsOf…

--- 原说明 ---
We can always derive `PreservesFiniteLimits C` by showing that we are preserving
 limits at an
arbitrary universe.
-/
lemma preservesFiniteLimits_of_preservesFiniteLimitsOfSize (F : C ⥤ D)
    (h :
      ∀ (J : Type w) {𝒥 : SmallCategory J} (_ : @FinCategory J 𝒥), PreservesLimitsOfShape J F) :
    PreservesFiniteLimits F where
      preservesFiniteLimits J (_ : SmallCategory J) _ := by
        have := h (ULiftHom (ULift J)) CategoryTheory.finCategoryUlift
        exact preservesLimitsOfShape_of_equiv (ULiftHomULiftCategory.equiv J).symm F

/-- The composition of two left exact functors is left exact. -/
/-
**CategoryTheory.Limits.comp_preservesFiniteLimits** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：comp_preservesFiniteLimits (F : C ⥤ D) (G : D ⥤ E) [PreservesFiniteLimits 
F] [PreservesFiniteLimits G] : PreservesFiniteLimits (F ⋙ G)
参数：F : C ⥤ D；G : D ⥤ E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.comp_preservesLimitsOfShape`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
The composition of two left exact functors is left exact.
-/
lemma comp_preservesFiniteLimits (F : C ⥤ D) (G : D ⥤ E) [PreservesFiniteLimits F]
    [PreservesFiniteLimits G] : PreservesFiniteLimits (F ⋙ G) :=
  ⟨fun _ _ _ => inferInstance⟩

/-- Transfer preservation of finite limits along a natural isomorphism in the functor. -/
/-
**CategoryTheory.Limits.preservesFiniteLimits_of_natIso** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：preservesFiniteLimits_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesFinite
Limits F] : PreservesFiniteLimits G where preservesFiniteLimits _ _ _
参数：h : F ≅ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_of_natIso`：preservesLimitsO
fShape_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesLimitsOfShape J F] : Preser
vesLimitsOfShape J G where preservesLimit {K…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
Transfer preservation of finite limits along a natural isomorphism in the functo
r.
-/
lemma preservesFiniteLimits_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesFiniteLimits F] :
    PreservesFiniteLimits G where
  preservesFiniteLimits _ _ _ := preservesLimitsOfShape_of_natIso h

/-- A functor `F` preserves finite products if it preserves all from `Discrete J` for `Finite J`.
We require this for `J = Fin n` in the definition,
then generalize to `J : Type u` in the instance. -/
/-
**CategoryTheory.Limits.PreservesFiniteProducts** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} → [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → CategoryTheory.Functor
 C D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `F` preserves finite products if it preserves all from `Discrete J` fo
r `Finite J`.
We require this for `J = Fin n` in the definition,
then generalize to `J : Type u` in the instance.
-/
class PreservesFiniteProducts (F : C ⥤ D) : Prop where
  preserves : ∀ n, PreservesLimitsOfShape (Discrete (Fin n)) F
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) (F : C ⥤ D) (J : Type u) [Finite J]
    [PreservesFiniteProducts F] : PreservesLimitsOfShape (Discrete J) F := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  have := PreservesFiniteProducts.preserves (F := F) n
  exact preservesLimitsOfShape_of_equiv (Discrete.equivalence e.symm) F
/-
**CategoryTheory.Limits.comp_preservesFiniteProducts** 是 Mathlib 中的一个实例，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：comp_preservesFiniteProducts (F : C ⥤ D) (G : D ⥤ E) [PreservesFiniteProdu
cts F] [PreservesFiniteProducts G] : PreservesFiniteProducts (F ⋙ G) where prese
rves _
参数：F : C ⥤ D；G : D ⥤ E。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.comp_preservesLimitsOfShape`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.instPreservesLimitsOfShapeDiscreteOfFiniteOfPreser
vesFiniteProducts`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {
D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
instance comp_preservesFiniteProducts (F : C ⥤ D) (G : D ⥤ E)
    [PreservesFiniteProducts F] [PreservesFiniteProducts G] :
    PreservesFiniteProducts (F ⋙ G) where
  preserves _ := inferInstance
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ D) [PreservesFiniteLimits F] : PreservesFiniteProducts F where
  preserves _ := inferInstance

/--
A functor is said to reflect finite limits, if it reflects all limits of shape `J`,
where `J : Type` is a finite category.
-/
/-
**CategoryTheory.Limits.ReflectsFiniteLimits** 是 Mathlib 中的一个类，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：ReflectsFiniteLimits (F : C ⥤ D) : Prop where reflects : forall (J : Type)
 [SmallCategory J] [FinCategory J], ReflectsLimitsOfShape J F
参数：F : C ⥤ D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor is said to reflect finite limits, if it reflects all limits of shape `
J`,
where `J : Type` is a finite category.
-/
class ReflectsFiniteLimits (F : C ⥤ D) : Prop where
  reflects : ∀ (J : Type) [SmallCategory J] [FinCategory J], ReflectsLimitsOfShape J F := by
    infer_instance

attribute [instance] ReflectsFiniteLimits.reflects

/- Similarly to preserving finite products, quantified classes don't behave well. -/
/--
A functor `F` preserves finite products if it reflects limits of shape `Discrete J` for finite `J`.
We require this for `J = Fin n` in the definition,
then generalize to `J : Type u` in the instance.
-/
/-
**CategoryTheory.Limits.ReflectsFiniteProducts** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} → [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → CategoryTheory.Functor
 C D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `F` preserves finite products if it reflects limits of shape `Discrete
 J` for finite `J`.
We require this for `J = Fin n` in the definition,
then generalize to `J : Type u` in the instance.
-/
class ReflectsFiniteProducts (F : C ⥤ D) : Prop where
  reflects : ∀ n, ReflectsLimitsOfShape (Discrete (Fin n)) F
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) (F : C ⥤ D) [ReflectsFiniteProducts F] (J : Type u) [Finite J] :
    ReflectsLimitsOfShape (Discrete J) F :=
  let ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  have := ReflectsFiniteProducts.reflects (F := F) n
  reflectsLimitsOfShape_of_equiv (Discrete.equivalence e.symm) _

-- This is a dangerous instance as it has unbound universe variables.
/-- If we reflect limits of some arbitrary size, then we reflect all finite limits. -/
/-
**CategoryTheory.Limits.ReflectsLimitsOfSize.reflectsFiniteLimits** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.Limits.ReflectsLimitsOfSize`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor C D)
 [CategoryTheory.Limits.ReflectsLimitsOfSize.{w, w₂, v₁, v₂, u₁, u₂} F],   Categ
oryTheory.Limits.ReflectsFiniteLimits F
参数：F : CategoryTheory.Functor C D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsSmallestLimits_of_reflectsLimits`：reflects
SmallestLimits_of_reflectsLimits (F : C ⥤ D) [ReflectsLimitsOfSize.{v₃, u₃} F] :
 ReflectsLimitsOfSize.{0, 0} F
· 使用引理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_equiv`：reflectsLimitsOfSh
ape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D) [Reflec
tsLimitsOfShape J F] : ReflectsLimitsOfSha…
· 使用定理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_reflectsLimits`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…

--- 原说明 ---
If we reflect limits of some arbitrary size, then we reflect all finite limits.
-/
lemma ReflectsLimitsOfSize.reflectsFiniteLimits
    (F : C ⥤ D) [ReflectsLimitsOfSize.{w, w₂} F] : ReflectsFiniteLimits F where
  reflects J (sJ : SmallCategory J) fJ := by
    have := reflectsSmallestLimits_of_reflectsLimits F
    exact reflectsLimitsOfShape_of_equiv (FinCategory.equivAsType J) F

-- Added as a specialization of the dangerous instance above, for colimits indexed in Type 0.
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 120) (F : C ⥤ D) [ReflectsLimitsOfSize.{0, 0} F] :
    ReflectsFiniteLimits F :=
  ReflectsLimitsOfSize.reflectsFiniteLimits F

-- An alternative specialization of the dangerous instance for small colimits.
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 120) (F : C ⥤ D)
    [ReflectsLimits F] : ReflectsFiniteLimits F :=
  ReflectsLimitsOfSize.reflectsFiniteLimits F

/--
If `F ⋙ G` preserves finite limits and `G` reflects finite limits, then `F` preserves
finite limits.
-/
/-
**CategoryTheory.Limits.preservesFiniteLimits_of_reflects_of_preserves** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesFiniteLimits_of_reflects_of_preserves (F : C ⥤ D) (G : D ⥤ E) [Pr
eservesFiniteLimits (F ⋙ G)] [ReflectsFiniteLimits G] : PreservesFiniteLimits F 
where preservesFiniteLimits _ _ _
参数：F : C ⥤ D；G : D ⥤ E；F ⋙ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_of_reflects_of_preserves`：p
reservesLimitsOfShape_of_reflects_of_preserves [PreservesLimitsOfShape J (F ⋙ G)
] [ReflectsLimitsOfShape J G] : PreservesLimitsOfShape J F …
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.ReflectsFiniteLimits.reflects`：∀ {C : Type u₁} {in
st : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.
Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F ⋙ G` preserves finite limits and `G` reflects finite limits, then `F` pres
erves
finite limits.
-/
lemma preservesFiniteLimits_of_reflects_of_preserves (F : C ⥤ D) (G : D ⥤ E)
    [PreservesFiniteLimits (F ⋙ G)] [ReflectsFiniteLimits G] : PreservesFiniteLimits F where
  preservesFiniteLimits _ _ _ := preservesLimitsOfShape_of_reflects_of_preserves F G

/--
If `F ⋙ G` preserves finite products and `G` reflects finite products, then `F` preserves
finite products.
-/
/-
**CategoryTheory.Limits.preservesFiniteProducts_of_reflects_of_preserves** 是 Mat
hlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesFiniteProducts_of_reflects_of_preserves (F : C ⥤ D) (G : D ⥤ E) [
PreservesFiniteProducts (F ⋙ G)] [ReflectsFiniteProducts G] : PreservesFinitePro
ducts F where preserves _
参数：F : C ⥤ D；G : D ⥤ E；F ⋙ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesLimitsOfShape_of_reflects_of_preserves`：p
reservesLimitsOfShape_of_reflects_of_preserves [PreservesLimitsOfShape J (F ⋙ G)
] [ReflectsLimitsOfShape J G] : PreservesLimitsOfShape J F …
· 使用定理 `CategoryTheory.Limits.instPreservesLimitsOfShapeDiscreteOfFiniteOfPreser
vesFiniteProducts`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {
D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.instReflectsLimitsOfShapeDiscreteOfReflectsFiniteP
roductsOfFinite`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D 
: Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…

--- 原说明 ---
If `F ⋙ G` preserves finite products and `G` reflects finite products, then `F` 
preserves
finite products.
-/
lemma preservesFiniteProducts_of_reflects_of_preserves (F : C ⥤ D) (G : D ⥤ E)
    [PreservesFiniteProducts (F ⋙ G)] [ReflectsFiniteProducts G] : PreservesFiniteProducts F where
  preserves _ := preservesLimitsOfShape_of_reflects_of_preserves F G
/-
**CategoryTheory.Limits.reflectsFiniteLimits_of_reflectsIsomorphisms** 是 Mathlib
 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：reflectsFiniteLimits_of_reflectsIsomorphisms (F : C ⥤ D) [F.ReflectsIsomor
phisms] [HasFiniteLimits C] [PreservesFiniteLimits F] : ReflectsFiniteLimits F w
here reflects _ _ _
参数：F : C ⥤ D。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_reflectsIsomorphisms`：ref
lectsLimitsOfShape_of_reflectsIsomorphisms {G : C ⥤ D} [G.ReflectsIsomorphisms] 
[HasLimitsOfShape J C] [PreservesLimitsOfShape J G] : Ref…
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_hasFiniteLimits`：∀ (C : Type u
) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLimi
ts C] (J : Type w)   [inst_2 : CategoryTheory.S…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
-/
instance reflectsFiniteLimits_of_reflectsIsomorphisms (F : C ⥤ D)
    [F.ReflectsIsomorphisms] [HasFiniteLimits C] [PreservesFiniteLimits F] :
      ReflectsFiniteLimits F where
  reflects _ _ _ := reflectsLimitsOfShape_of_reflectsIsomorphisms
/-
**CategoryTheory.Limits.reflectsFiniteProducts_of_reflectsIsomorphisms** 是 Mathl
ib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：reflectsFiniteProducts_of_reflectsIsomorphisms (F : C ⥤ D) [F.ReflectsIsom
orphisms] [HasFiniteProducts C] [PreservesFiniteProducts F] : ReflectsFiniteProd
ucts F where reflects _
参数：F : C ⥤ D。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsLimitsOfShape_of_reflectsIsomorphisms`：ref
lectsLimitsOfShape_of_reflectsIsomorphisms {G : C ⥤ D} [G.ReflectsIsomorphisms] 
[HasLimitsOfShape J C] [PreservesLimitsOfShape J G] : Ref…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.instPreservesLimitsOfShapeDiscreteOfFiniteOfPreser
vesFiniteProducts`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {
D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
-/
instance reflectsFiniteProducts_of_reflectsIsomorphisms (F : C ⥤ D)
    [F.ReflectsIsomorphisms] [HasFiniteProducts C] [PreservesFiniteProducts F] :
      ReflectsFiniteProducts F where
  reflects _ := reflectsLimitsOfShape_of_reflectsIsomorphisms
/-
**CategoryTheory.Limits.comp_reflectsFiniteProducts** 是 Mathlib 中的一个实例，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：comp_reflectsFiniteProducts (F : C ⥤ D) (G : D ⥤ E) [ReflectsFiniteProduct
s F] [ReflectsFiniteProducts G] : ReflectsFiniteProducts (F ⋙ G) where reflects 
_
参数：F : C ⥤ D；G : D ⥤ E。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.comp_reflectsLimitsOfShape`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.instReflectsLimitsOfShapeDiscreteOfReflectsFiniteP
roductsOfFinite`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D 
: Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
instance comp_reflectsFiniteProducts (F : C ⥤ D) (G : D ⥤ E)
    [ReflectsFiniteProducts F] [ReflectsFiniteProducts G] :
    ReflectsFiniteProducts (F ⋙ G) where
  reflects _ := inferInstance
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ D) [ReflectsFiniteLimits F] : ReflectsFiniteProducts F where
  reflects _ := inferInstance

/-- A functor is said to preserve finite colimits, if it preserves all colimits of
shape `J`, where `J : Type` is a finite category.
-/
/-
**CategoryTheory.Limits.PreservesFiniteColimits** 是 Mathlib 中的一个类，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：PreservesFiniteColimits (F : C ⥤ D) : Prop where preservesFiniteColimits :
 forall (J : Type) [SmallCategory J] [FinCategory J], PreservesColimitsOfShape J
 F
参数：F : C ⥤ D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor is said to preserve finite colimits, if it preserves all colimits of
shape `J`, where `J : Type` is a finite category.
-/
class PreservesFiniteColimits (F : C ⥤ D) : Prop where
  preservesFiniteColimits :
    ∀ (J : Type) [SmallCategory J] [FinCategory J], PreservesColimitsOfShape J F := by
      infer_instance

attribute [instance] PreservesFiniteColimits.preservesFiniteColimits

/--
Preserving finite colimits also implies preserving colimits over finite shapes in higher
universes.
-/
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Preserving finite colimits also implies preserving colimits over finite shapes i
n higher
universes.
-/
instance (priority := 100) preservesColimitsOfShapeOfPreservesFiniteColimits
    (F : C ⥤ D) [PreservesFiniteColimits F] (J : Type w) [SmallCategory J] [FinCategory J] :
    PreservesColimitsOfShape J F := by
  apply preservesColimitsOfShape_of_equiv (FinCategory.equivAsType J)

-- This is a dangerous instance as it has unbound universe variables.
/-- If we preserve colimits of some arbitrary size, then we preserve all finite colimits. -/
/-
**CategoryTheory.Limits.PreservesColimitsOfSize.preservesFiniteColimits** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory.Limits.PreservesColimitsOfSize`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor C D)
 [CategoryTheory.Limits.PreservesColimitsOfSize.{w, w₂, v₁, v₂, u₁, u₂} F],   Ca
tegoryTheory.Limits.PreservesFiniteColimits F
参数：F : CategoryTheory.Functor C D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesSmallestColimits_of_preservesColimits`：pr
eservesSmallestColimits_of_preservesColimits (F : C ⥤ D) [PreservesColimitsOfSiz
e.{v₃, u₃} F] : PreservesColimitsOfSize.{0, 0} F
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_of_equiv`：preservesColimi
tsOfShape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D) [
PreservesColimitsOfShape J F] : PreservesColi…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfSize.preservesColimitsOfShape`：
∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_
1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If we preserve colimits of some arbitrary size, then we preserve all finite coli
mits.
-/
lemma PreservesColimitsOfSize.preservesFiniteColimits (F : C ⥤ D)
    [PreservesColimitsOfSize.{w, w₂} F] : PreservesFiniteColimits F where
  preservesFiniteColimits J (sJ : SmallCategory J) fJ := by
    have := preservesSmallestColimits_of_preservesColimits F
    exact preservesColimitsOfShape_of_equiv (FinCategory.equivAsType J) F

-- Added as a specialization of the dangerous instance above, for colimits indexed in Type 0.
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 120) PreservesColimitsOfSize0.preservesFiniteColimits
    (F : C ⥤ D) [PreservesColimitsOfSize.{0, 0} F] : PreservesFiniteColimits F :=
  PreservesColimitsOfSize.preservesFiniteColimits F

-- An alternative specialization of the dangerous instance for small colimits.
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 120) PreservesColimits.preservesFiniteColimits (F : C ⥤ D)
    [PreservesColimits F] : PreservesFiniteColimits F :=
  PreservesColimitsOfSize.preservesFiniteColimits F

attribute [local instance] uliftCategory in
/-- We can always derive `PreservesFiniteColimits C`
by showing that we are preserving colimits at an arbitrary universe. -/
/-
**CategoryTheory.Limits.preservesFiniteColimits_of_preservesFiniteColimitsOfSize
** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesFiniteColimits_of_preservesFiniteColimitsOfSize (F : C ⥤ D) (h : 
forall (J : Type w) {𝒥 : SmallCategory J} (_ : @FinCategory J 𝒥), PreservesColim
itsOfShape J F) : PreservesFiniteColimits F where preservesFiniteColimits J (_ :
 SmallCategory J) _
参数：F : C ⥤ D；h : forall (J : Type w) {𝒥 : SmallCategory J} (_ : @FinCategory J 𝒥
), PreservesColimitsOfShape J F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_of_equiv`：preservesColimi
tsOfShape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D) [
PreservesColimitsOfShape J F] : PreservesColi…

--- 原说明 ---
We can always derive `PreservesFiniteColimits C`
by showing that we are preserving colimits at an arbitrary universe.
-/
lemma preservesFiniteColimits_of_preservesFiniteColimitsOfSize (F : C ⥤ D)
    (h :
      ∀ (J : Type w) {𝒥 : SmallCategory J} (_ : @FinCategory J 𝒥), PreservesColimitsOfShape J F) :
    PreservesFiniteColimits F where
      preservesFiniteColimits J (_ : SmallCategory J) _ := by
        let : Category (ULiftHom (ULift J)) := ULiftHom.category
        have := h (ULiftHom (ULift J)) CategoryTheory.finCategoryUlift
        exact preservesColimitsOfShape_of_equiv (ULiftHomULiftCategory.equiv J).symm F

/-- The composition of two right exact functors is right exact. -/
/-
**CategoryTheory.Limits.comp_preservesFiniteColimits** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：comp_preservesFiniteColimits (F : C ⥤ D) (G : D ⥤ E) [PreservesFiniteColim
its F] [PreservesFiniteColimits G] : PreservesFiniteColimits (F ⋙ G)
参数：F : C ⥤ D；G : D ⥤ E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.comp_preservesColimitsOfShape`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteColimits.preservesFiniteColimits`：∀
 {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1
 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
The composition of two right exact functors is right exact.
-/
lemma comp_preservesFiniteColimits (F : C ⥤ D) (G : D ⥤ E) [PreservesFiniteColimits F]
    [PreservesFiniteColimits G] : PreservesFiniteColimits (F ⋙ G) :=
  ⟨fun _ _ _ => inferInstance⟩

/-- Transfer preservation of finite colimits along a natural isomorphism in the functor. -/
/-
**CategoryTheory.Limits.preservesFiniteColimits_of_natIso** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Limits`。
形式化陈述：preservesFiniteColimits_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesFini
teColimits F] : PreservesFiniteColimits G where preservesFiniteColimits _ _ _
参数：h : F ≅ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_of_natIso`：preservesColim
itsOfShape_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesColimitsOfShape J F] : 
PreservesColimitsOfShape J G where preservesCo…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteColimits.preservesFiniteColimits`：∀
 {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1
 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
Transfer preservation of finite colimits along a natural isomorphism in the func
tor.
-/
lemma preservesFiniteColimits_of_natIso {F G : C ⥤ D} (h : F ≅ G) [PreservesFiniteColimits F] :
    PreservesFiniteColimits G where
  preservesFiniteColimits _ _ _ := preservesColimitsOfShape_of_natIso h

/-- A functor `F` preserves finite products if it preserves all from `Discrete J` for `Fintype J`.
We require this for `J = Fin n` in the definition,
then generalize to `J : Type u` in the instance. -/
/-
**CategoryTheory.Limits.PreservesFiniteCoproducts** 是 Mathlib 中的一个归纳类型，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} → [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → CategoryTheory.Functor
 C D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `F` preserves finite products if it preserves all from `Discrete J` fo
r `Fintype J`.
We require this for `J = Fin n` in the definition,
then generalize to `J : Type u` in the instance.
-/
class PreservesFiniteCoproducts (F : C ⥤ D) : Prop where
  /-- preservation of colimits indexed by `Discrete (Fin n)`. -/
  preserves : ∀ n, PreservesColimitsOfShape (Discrete (Fin n)) F
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) (F : C ⥤ D) (J : Type u) [Finite J]
    [PreservesFiniteCoproducts F] : PreservesColimitsOfShape (Discrete J) F :=
  let ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  have := PreservesFiniteCoproducts.preserves (F := F) n
  preservesColimitsOfShape_of_equiv (Discrete.equivalence e.symm) F
/-
**CategoryTheory.Limits.comp_preservesFiniteCoproducts** 是 Mathlib 中的一个实例，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：comp_preservesFiniteCoproducts (F : C ⥤ D) (G : D ⥤ E) [PreservesFiniteCop
roducts F] [PreservesFiniteCoproducts G] : PreservesFiniteCoproducts (F ⋙ G) whe
re preserves _
参数：F : C ⥤ D；G : D ⥤ E。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.comp_preservesColimitsOfShape`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.instPreservesColimitsOfShapeDiscreteOfFiniteOfPres
ervesFiniteCoproducts`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} 
C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTh
eor…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
instance comp_preservesFiniteCoproducts (F : C ⥤ D) (G : D ⥤ E)
    [PreservesFiniteCoproducts F] [PreservesFiniteCoproducts G] :
    PreservesFiniteCoproducts (F ⋙ G) where
  preserves _ := inferInstance
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ D) [PreservesFiniteColimits F] : PreservesFiniteCoproducts F where
  preserves _ := inferInstance

/--
A functor is said to reflect finite colimits, if it reflects all colimits of shape `J`,
where `J : Type` is a finite category.
-/
/-
**CategoryTheory.Limits.ReflectsFiniteColimits** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} → [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → CategoryTheory.Functor
 C D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor is said to reflect finite colimits, if it reflects all colimits of sha
pe `J`,
where `J : Type` is a finite category.
-/
class ReflectsFiniteColimits (F : C ⥤ D) : Prop where
  [reflects : ∀ (J : Type) [SmallCategory J] [FinCategory J], ReflectsColimitsOfShape J F]

attribute [instance] ReflectsFiniteColimits.reflects

-- This is a dangerous instance as it has unbound universe variables.
/-- If we reflect colimits of some arbitrary size, then we reflect all finite colimits. -/
/-
**CategoryTheory.Limits.ReflectsColimitsOfSize.reflectsFiniteColimits** 是 Mathli
b 中的一个定理，位于命名空间 `CategoryTheory.Limits.ReflectsColimitsOfSize`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheory.Functor C D)
 [CategoryTheory.Limits.ReflectsColimitsOfSize.{w, w₂, v₁, v₂, u₁, u₂} F],   Cat
egoryTheory.Limits.ReflectsFiniteColimits F
参数：F : CategoryTheory.Functor C D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsSmallestColimits_of_reflectsColimits`：refl
ectsSmallestColimits_of_reflectsColimits (F : C ⥤ D) [ReflectsColimitsOfSize.{v₃
, u₃} F] : ReflectsColimitsOfSize.{0, 0} F
· 使用引理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_equiv`：reflectsColimits
OfShape_of_equiv {J' : Type w₂} [Category.{w₂'} J'] (e : J ≌ J') (F : C ⥤ D) [Re
flectsColimitsOfShape J F] : ReflectsColimit…
· 使用定理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_reflectsColimits`：∀ {C 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : C
ategoryTheory.Category.{v₂, u₂} D]   (J : Type w) [inst…

--- 原说明 ---
If we reflect colimits of some arbitrary size, then we reflect all finite colimi
ts.
-/
lemma ReflectsColimitsOfSize.reflectsFiniteColimits
    (F : C ⥤ D) [ReflectsColimitsOfSize.{w, w₂} F] : ReflectsFiniteColimits F where
  reflects J (sJ : SmallCategory J) fJ := by
    have := reflectsSmallestColimits_of_reflectsColimits F
    exact reflectsColimitsOfShape_of_equiv (FinCategory.equivAsType J) F

-- Added as a specialization of the dangerous instance above, for colimits indexed in Type 0.
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 120) (F : C ⥤ D) [ReflectsColimitsOfSize.{0, 0} F] :
    ReflectsFiniteColimits F :=
  ReflectsColimitsOfSize.reflectsFiniteColimits F

-- An alternative specialization of the dangerous instance for small colimits.
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 120) (F : C ⥤ D)
    [ReflectsColimits F] : ReflectsFiniteColimits F :=
  ReflectsColimitsOfSize.reflectsFiniteColimits F

/- Similarly to preserving finite coproducts, quantified classes don't behave well. -/
/--
A functor `F` preserves finite coproducts if it reflects colimits of shape `Discrete J`
for finite `J`.

We require this for `J = Fin n` in the definition,
then generalize to `J : Type u` in the instance.
-/
/-
**CategoryTheory.Limits.ReflectsFiniteCoproducts** 是 Mathlib 中的一个归纳类型，位于命名空间 `Ca
tegoryTheory.Limits`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {D : T
ype u₂} → [inst_1 : CategoryTheory.Category.{v₂, u₂} D] → CategoryTheory.Functor
 C D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `F` preserves finite coproducts if it reflects colimits of shape `Disc
rete J`
for finite `J`.

We require this for `J = Fin n` in the definition,
then generalize to `J : Type u` in the instance.
-/
class ReflectsFiniteCoproducts (F : C ⥤ D) : Prop where
  reflects : ∀ n, ReflectsColimitsOfShape (Discrete (Fin n)) F
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) (F : C ⥤ D) [ReflectsFiniteCoproducts F] (J : Type u) [Finite J] :
    ReflectsColimitsOfShape (Discrete J) F :=
  let ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  have := ReflectsFiniteCoproducts.reflects (F := F) n
  reflectsColimitsOfShape_of_equiv (Discrete.equivalence e.symm) _

/--
If `F ⋙ G` preserves finite colimits and `G` reflects finite colimits, then `F` preserves finite
colimits.
-/
/-
**CategoryTheory.Limits.preservesFiniteColimits_of_reflects_of_preserves** 是 Mat
hlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesFiniteColimits_of_reflects_of_preserves (F : C ⥤ D) (G : D ⥤ E) [
PreservesFiniteColimits (F ⋙ G)] [ReflectsFiniteColimits G] : PreservesFiniteCol
imits F where preservesFiniteColimits _ _ _
参数：F : C ⥤ D；G : D ⥤ E；F ⋙ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_of_reflects_of_preserves`
：preservesColimitsOfShape_of_reflects_of_preserves [PreservesColimitsOfShape J (
F ⋙ G)] [ReflectsColimitsOfShape J G] : PreservesColimitsOfSh…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteColimits.preservesFiniteColimits`：∀
 {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1
 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.ReflectsFiniteColimits.reflects`：∀ {C : Type u₁} {
inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheor
y.Category.{v₂, u₂} D}   {F : CategoryTheor…

--- 原说明 ---
If `F ⋙ G` preserves finite colimits and `G` reflects finite colimits, then `F` 
preserves finite
colimits.
-/
lemma preservesFiniteColimits_of_reflects_of_preserves (F : C ⥤ D) (G : D ⥤ E)
    [PreservesFiniteColimits (F ⋙ G)] [ReflectsFiniteColimits G] : PreservesFiniteColimits F where
  preservesFiniteColimits _ _ _ := preservesColimitsOfShape_of_reflects_of_preserves F G

/--
If `F ⋙ G` preserves finite coproducts and `G` reflects finite coproducts, then `F` preserves
finite coproducts.
-/
/-
**CategoryTheory.Limits.preservesFiniteCoproducts_of_reflects_of_preserves** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：preservesFiniteCoproducts_of_reflects_of_preserves (F : C ⥤ D) (G : D ⥤ E)
 [PreservesFiniteCoproducts (F ⋙ G)] [ReflectsFiniteCoproducts G] : PreservesFin
iteCoproducts F where preserves _
参数：F : C ⥤ D；G : D ⥤ E；F ⋙ G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.preservesColimitsOfShape_of_reflects_of_preserves`
：preservesColimitsOfShape_of_reflects_of_preserves [PreservesColimitsOfShape J (
F ⋙ G)] [ReflectsColimitsOfShape J G] : PreservesColimitsOfSh…
· 使用定理 `CategoryTheory.Limits.instPreservesColimitsOfShapeDiscreteOfFiniteOfPres
ervesFiniteCoproducts`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} 
C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTh
eor…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.instReflectsColimitsOfShapeDiscreteOfReflectsFinit
eCoproductsOfFinite`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C]
 {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheo
r…

--- 原说明 ---
If `F ⋙ G` preserves finite coproducts and `G` reflects finite coproducts, then 
`F` preserves
finite coproducts.
-/
lemma preservesFiniteCoproducts_of_reflects_of_preserves (F : C ⥤ D) (G : D ⥤ E)
    [PreservesFiniteCoproducts (F ⋙ G)] [ReflectsFiniteCoproducts G] :
    PreservesFiniteCoproducts F where
  preserves _ := preservesColimitsOfShape_of_reflects_of_preserves F G
/-
**CategoryTheory.Limits.reflectsFiniteColimitsOfReflectsIsomorphisms** 是 Mathlib
 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：reflectsFiniteColimitsOfReflectsIsomorphisms (F : C ⥤ D) [F.ReflectsIsomor
phisms] [HasFiniteColimits C] [PreservesFiniteColimits F] : ReflectsFiniteColimi
ts F where reflects _ _ _
参数：F : C ⥤ D。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_reflectsIsomorphisms`：r
eflectsColimitsOfShape_of_reflectsIsomorphisms {G : C ⥤ D} [G.ReflectsIsomorphis
ms] [HasColimitsOfShape J C] [PreservesColimitsOfShape J G]…
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_hasFiniteColimits`：∀ (C : Ty
pe u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFinite
Colimits C] (J : Type w)   [inst_2 : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteColimits.preservesFiniteColimits`：∀
 {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1
 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
-/
instance reflectsFiniteColimitsOfReflectsIsomorphisms (F : C ⥤ D)
    [F.ReflectsIsomorphisms] [HasFiniteColimits C] [PreservesFiniteColimits F] :
      ReflectsFiniteColimits F where
  reflects _ _ _ := reflectsColimitsOfShape_of_reflectsIsomorphisms
/-
**CategoryTheory.Limits.reflectsFiniteCoproductsOfReflectsIsomorphisms** 是 Mathl
ib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：reflectsFiniteCoproductsOfReflectsIsomorphisms (F : C ⥤ D) [F.ReflectsIsom
orphisms] [HasFiniteCoproducts C] [PreservesFiniteCoproducts F] : ReflectsFinite
Coproducts F where reflects _
参数：F : C ⥤ D。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.reflectsColimitsOfShape_of_reflectsIsomorphisms`：r
eflectsColimitsOfShape_of_reflectsIsomorphisms {G : C ⥤ D} [G.ReflectsIsomorphis
ms] [HasColimitsOfShape J C] [PreservesColimitsOfShape J G]…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.instPreservesColimitsOfShapeDiscreteOfFiniteOfPres
ervesFiniteCoproducts`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} 
C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTh
eor…
-/
instance reflectsFiniteCoproductsOfReflectsIsomorphisms (F : C ⥤ D)
    [F.ReflectsIsomorphisms] [HasFiniteCoproducts C] [PreservesFiniteCoproducts F] :
      ReflectsFiniteCoproducts F where
  reflects _ := reflectsColimitsOfShape_of_reflectsIsomorphisms
/-
**CategoryTheory.Limits.comp_reflectsFiniteCoproducts** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory.Limits`。
形式化陈述：comp_reflectsFiniteCoproducts (F : C ⥤ D) (G : D ⥤ E) [ReflectsFiniteCopro
ducts F] [ReflectsFiniteCoproducts G] : ReflectsFiniteCoproducts (F ⋙ G) where r
eflects _
参数：F : C ⥤ D；G : D ⥤ E。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.comp_reflectsColimitsOfShape`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.C
ategory.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.instReflectsColimitsOfShapeDiscreteOfReflectsFinit
eCoproductsOfFinite`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C]
 {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheo
r…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
instance comp_reflectsFiniteCoproducts (F : C ⥤ D) (G : D ⥤ E)
    [ReflectsFiniteCoproducts F] [ReflectsFiniteCoproducts G] :
    ReflectsFiniteCoproducts (F ⋙ G) where
  reflects _ := inferInstance
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (F : C ⥤ D) [ReflectsFiniteColimits F] : ReflectsFiniteCoproducts F where
  reflects _ := inferInstance

end CategoryTheory.Limits

