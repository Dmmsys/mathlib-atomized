/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.Functor.RegularEpi
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Images
public import Mathlib.CategoryTheory.Sites.LeftExact

/-!

# The category of type-valued sheaves is a regular epi category

## Main results

`isRegularEpiCategory_sheaf`: Let `J` be a Grothendieck topology on `C`, and suppose that
`D` is a regular epi category which has pushouts and pullbacks, and that sheafification of
`D`-valued `J`-sheaves exists. Suppose further that the category `Sheaf J D` is balanced, and
that the underlying morphism of presheaves of every epimorphism in `Sheaf J D` can be factored
as an epimorphism followed by a monomorphism. Then `Sheaf J D` is a regular epi category.

Note: This is not an instance because of the factorisation requirement, but it can in principle be
turned into an instance whenever `D` has equalizers and `Cᵒᵖ ⥤ D` has images. This holds in
particular when `D` is `Type*` or any abelian category. We add it as an instance for `D := Type*`,
but the fact that `Sheaf J D` is a regular epi category when `D` is an abelian category
already follows from the sheaf category being abelian.

## References

We follow the proof of Proposition 3.4.13 in [borceux-vol3]
*Handbook of Categorical Algebra: Volume 3, Sheaf Theory*, by Borceux, 1994.
The first part of that proof, the result for presheaf categories, is proved in the file
`Mathlib.CategoryTheory.Functor.RegularEpi`.
-/

public section

universe v u

namespace CategoryTheory

open Limits

variable {C D : Type*} [Category C] [Category D]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.isRegularEpiCategory_sheaf** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory`。
形式化陈述：isRegularEpiCategory_sheaf (J : GrothendieckTopology C) [HasPullbacks D] [
HasPushouts D] [IsRegularEpiCategory D] (h : forall {F G : Sheaf J D} (f : F ⟶ G
) [Epi f], exists (I : Cᵒᵖ ⥤ D) (p : F.obj ⟶ I) (i : I ⟶ G.obj), Epi p ∧ Mono i 
∧ p ≫ i = f.hom) [HasSheafify J D] [Balanced (Sheaf J D)] : IsRegularEpiCategory
 (Sheaf J D) where regularEpiOfEpi {F G} f _
参数：J : GrothendieckTopology C；h : forall {F G : Sheaf J D} (f : F ⟶ G) [Epi f], 
exists (I : Cᵒᵖ ⥤ D) (p : F.obj ⟶ I) (i : I ⟶ G.obj), Epi p ∧ Mono i ∧ p ≫ i = f
.hom；Sheaf J D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instHasWeakSheafifyOfHasSheafify`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C)
 (A : Type u₂)   [inst_1 : CategoryTh…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Adjunction.counit_naturality`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category
.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.IsIso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : Y ⟶ Z), CategoryT…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Sheaf.Hom.epi_of_presheaf_epi`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C) (A
 : Type u₂)   [inst_1 : CategoryTh…
· 使用定理 `CategoryTheory.IsSplitEpi.EffectiveEpi`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {B X : C} (f : X ⟶ B) [CategoryTheory.IsSplitEpi 
f],   CategoryTheory.Effecti…
· 使用定理 `CategoryTheory.IsSplitEpi.of_iso`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],   Category
Theory.IsSplitEpi f
· 使用定理 `CategoryTheory.instIsIsoFunctorOppositeHomFullSubcategoryIsSheafAppSheaf
CounitSheafificationAdjunction`：∀ {C : Type u₁} [inst : CategoryTheory.Category.
{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C} {D : Type u_1}   [inst_1
 : CategoryT…
· 使用定理 `CategoryTheory.ObjectProperty.instIsIsoHomFullSubcategory`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C
} {X Y : P.FullSubcategory}   (f : X ⟶ Y) [Cate…
· 使用定理 `CategoryTheory.epi_of_epi`：epi_of_epi (f : X ⟶ Y) (g : Y ⟶ Z) [Epi (f ≫ 
g)] : Epi g
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Balanced.isIso_of_mono_of_epi`：∀ {C : Type u} {inst : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.Balanced C] {X Y : C} (f :
 X ⟶ Y)   [CategoryTheory.Mono f] …
· 使用定理 `CategoryTheory.Functor.map_mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (F : CategoryTheor…
· 使用定理 `CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape`：∀ {C : 
Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.instPreservesFiniteLimitsFunctorOppositeSheafPresheafToSh
eaf`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTh
eory.GrothendieckTopology C) (A : Type u₂)   [inst_1 : CategoryTh…
· 使用引理 `CategoryTheory.isRegularEpi_iff_effectiveEpi`：isRegularEpi_iff_effective
Epi {B X : C} (f : X ⟶ B) [HasPullback f f] : IsRegularEpi f ↔ EffectiveEpi f
· 使用定理 `CategoryTheory.Limits.instHasPullbackCompOfIsIso`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) {X' : 
C} (i : X' ⟶ X)   [CategoryTheory.IsIs…
· 使用定理 `CategoryTheory.instMonoAppOfFunctor`：∀ {K : Type u} [inst : CategoryTheo
ry.Category.{v, u} K] {C : Type u'} [inst_1 : CategoryTheory.Category.{v', u'} C
]   {F G : CategoryTheory…
· 使用定理 `CategoryTheory.Sheaf.instHasLimitsOfShape`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopology C} {D : Typ
e w}   [inst_1 : CategoryTheory…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
（共 54 条，此处仅展示前 30 条）
-/
lemma isRegularEpiCategory_sheaf (J : GrothendieckTopology C)
    [HasPullbacks D] [HasPushouts D] [IsRegularEpiCategory D]
    (h : ∀ {F G : Sheaf J D} (f : F ⟶ G) [Epi f], ∃ (I : Cᵒᵖ ⥤ D) (p : F.obj ⟶ I) (i : I ⟶ G.obj),
      Epi p ∧ Mono i ∧ p ≫ i = f.hom)
    [HasSheafify J D] [Balanced (Sheaf J D)] : IsRegularEpiCategory (Sheaf J D) where
  regularEpiOfEpi {F G} f _ := by
    -- Factor `f` on the level of presheaves as an epimorphism `p` followed by a monomorphism `i`.
    obtain ⟨I, p, i, hp, hi, hpi⟩ := h f
    -- The sheafification of `f.hom` is `f` pre- and postcomposed with isomorphisms.
    have h₁ : (presheafToSheaf J D).map f.hom =
          (sheafificationAdjunction J D).counit.app F ≫ f ≫
          inv ((sheafificationAdjunction J D).counit.app G) := by
        simpa [← Category.assoc] using (sheafificationAdjunction J D).counit_naturality f
    have h₂ : f = inv ((sheafificationAdjunction J D).counit.app F) ≫
        (presheafToSheaf J D).map f.hom ≫ (sheafificationAdjunction J D).counit.app G := by
      simp [h₁]
    -- The sheafification of `f.val` is still an epimorphism
    have : Epi ((presheafToSheaf J D).map f.hom) := by
      rw [h₁]
      infer_instance
    -- The sheafification of `i` is an epimorphism, because the sheafification of `p ≫ i = f.val`
    -- is an epimorphism.
    have : Epi ((presheafToSheaf J D).map i) := by
      rw [← hpi, Functor.map_comp] at this
      exact epi_of_epi ((presheafToSheaf J D).map p) _
    -- Since the sheafification of `i` is both a monomorphism and an epimorphism, it is an
    -- isomorphism.
    have : IsIso ((presheafToSheaf J D).map i) :=
      Balanced.isIso_of_mono_of_epi _
    -- The next five lines show that it suffices to show that the sheafification of `p` is a
    -- regular epimorphism.
    rw [h₂, isRegularEpi_iff_effectiveEpi]
    suffices EffectiveEpi ((presheafToSheaf J D).map f.hom) by infer_instance
    rw [← hpi, Functor.map_comp]
    suffices EffectiveEpi ((presheafToSheaf J D).map p) by infer_instance
    rw [← isRegularEpi_iff_effectiveEpi]
    -- The underlying presheaf of the kernel pair of `f` is a kernel pair for `p`, and since
    -- sheafification preserves colimits, `p` exhibits its target `I` as a coequalizer of this
    -- kernel pair. The result follows.
    exact ⟨⟨{
      W := (presheafToSheaf J D).obj (pullback f f).obj
      left := (presheafToSheaf J D).map (pullback.fst f f).hom
      right := (presheafToSheaf J D).map (pullback.snd f f).hom
      w := by
        rw [← Functor.map_comp, ← Functor.map_comp]
        congr 1
        rw [← cancel_mono i]
        simp [hpi, ← ObjectProperty.FullSubcategory.comp_hom, pullback.condition]
      isColimit := by
        have := IsRegularEpiCategory.regularEpiOfEpi p
        exact isColimitCoforkMapOfIsColimit (presheafToSheaf J D) _
          (isColimitCoforkOfEffectiveEpi p _
            (PullbackCone.isLimitOfFactors f.hom f.hom i _ _ hpi hpi _
              ((isLimitPullbackConeMapOfIsLimit (sheafToPresheaf _ _) _
                (pullbackIsPullback f f))))) }⟩⟩
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (J : GrothendieckTopology C) [HasSheafify J (Type u)] :
    IsRegularEpiCategory (Sheaf J (Type u)) := isRegularEpiCategory_sheaf J fun f hf ↦
  ⟨image f.hom, factorThruImage f.hom, image.ι f.hom, inferInstance, inferInstance, by simp⟩
/-
**CategoryTheory.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) :
    IsRegularEpiCategory (Sheaf J (Type (max u v))) :=
  inferInstance

end CategoryTheory

