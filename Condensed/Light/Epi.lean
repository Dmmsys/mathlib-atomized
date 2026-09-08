/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.SequentialProduct
public import Mathlib.CategoryTheory.Sites.Coherent.SequentialLimit
public import Mathlib.Condensed.Light.Functors
public import Mathlib.Condensed.Light.Limits
/-!

# Epimorphisms of light condensed objects

This file characterises epimorphisms in light condensed sets and modules as the locally surjective
morphisms. Here, the condition of locally surjective is phrased in terms of continuous surjections
of light profinite sets.

Further, we prove that the functor `lim : Discrete ℕ ⥤ LightCondMod R` preserves epimorphisms.
-/

public section

universe v u w u' v'

open CategoryTheory Sheaf Limits GrothendieckTopology

namespace LightCondensed

variable (A : Type u') [Category.{v'} A] {FA : A → A → Type*} {CA : A → Type w}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w} A FA]
  [PreservesFiniteProducts (CategoryTheory.forget A)]

variable {X Y : LightCondensed.{u} A} (f : X ⟶ Y)

/-
**LightCondensed.isLocallySurjective_iff_locallySurjective_on_lightProfinite** 是
 Mathlib 中的一个引理，位于命名空间 `LightCondensed`。
形式化陈述：isLocallySurjective_iff_locallySurjective_on_lightProfinite : IsLocallySur
jective f ↔ forall (S : LightProfinite) (y : ToType (Y.obj.obj ⟨S⟩)), (exists (S
' : LightProfinite) (φ : S' ⟶ S) (_ : Function.Surjective φ) (x : ToType (X.obj.
obj ⟨S'⟩)), f.hom.app ⟨S'⟩ x = Y.obj.map ⟨φ⟩ y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LightProfinite.instPreregular`：CategoryTheory.Preregular LightProfinite
· 使用定理 `CategoryTheory.instPrecoherentOfFinitaryPreExtensiveOfPreregular`：∀ (C :
 Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Finitar
yPreExtensive C]   [CategoryTheory.Preregular C], Cate…
· 使用定理 `CategoryTheory.FinitaryExtensive.toFinitaryPreExtensive`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.FinitaryExtensive C], 
  CategoryTheory.FinitaryPreExtensive C
· 使用定理 `CompHausLike.instFinitaryExtensiveOfHasExplicitPullbacksOfInclusions`：∀ 
{P : TopCat → Prop} [inst : CompHausLike.HasExplicitFiniteCoproducts P]   [CompH
ausLike.HasExplicitPullbacksOfInclusions P], CategoryTheor…
· 使用定理 `LightProfinite.instHasExplicitFiniteCoproductsAndTotallyDisconnectedSpac
eCarrierSecondCountableTopology`：CompHausLike.HasExplicitFiniteCoproducts fun Y 
=> TotallyDisconnectedSpace ↑Y ∧ SecondCountableTopology ↑Y
· 使用定理 `CompHausLike.instHasExplicitPullbacksOfInclusionsOfHasExplicitPullbacks`
：∀ {P : TopCat → Prop} [CompHausLike.HasExplicitPullbacks P] [inst : CompHausLik
e.HasExplicitFiniteCoproducts P],   CompHausLike.HasExplicitP…
· 使用定理 `LightProfinite.instHasExplicitPullbacksAndTotallyDisconnectedSpaceCarrie
rSecondCountableTopology`：CompHausLike.HasExplicitPullbacks fun Y => TotallyDisc
onnectedSpace ↑Y ∧ SecondCountableTopology ↑Y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.coherentTopology.isLocallySurjective_iff`：∀ {C : Type u_1
} (D : Type u_2) [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Categ
oryTheory.Category.{v_2, u_2} D] {FD : D → D …
· 使用定理 `CategoryTheory.regularTopology.isLocallySurjective_iff`：∀ {C : Type u_1}
 (D : Type u_2) [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Catego
ryTheory.Category.{v_2, u_2} D] {FD : D → D …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isLocallySurjective_iff_locallySurjective_on_lightProfinite : IsLocallySurjective f ↔
    ∀ (S : LightProfinite) (y : ToType (Y.obj.obj ⟨S⟩)),
      (∃ (S' : LightProfinite) (φ : S' ⟶ S) (_ : Function.Surjective φ)
        (x : ToType (X.obj.obj ⟨S'⟩)),
        f.hom.app ⟨S'⟩ x = Y.obj.map ⟨φ⟩ y) := by
  rw [coherentTopology.isLocallySurjective_iff,
    regularTopology.isLocallySurjective_iff]
  simp_rw [LightProfinite.effectiveEpi_iff_surjective]

end LightCondensed

namespace LightCondSet

variable {X Y : LightCondSet.{u}} (f : X ⟶ Y)

/-
**LightCondSet.epi_iff_locallySurjective_on_lightProfinite** 是 Mathlib 中的一个引理，位于
命名空间 `LightCondSet`。
形式化陈述：epi_iff_locallySurjective_on_lightProfinite : Epi f ↔ forall (S : LightPro
finite) (y : Y.obj.obj ⟨S⟩), (exists (S' : LightProfinite) (φ : S' ⟶ S) (_ : Fun
ction.Surjective φ) (x : X.obj.obj ⟨S'⟩), f.hom.app ⟨S'⟩ x = Y.obj.map ⟨φ⟩ y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Sheaf.isLocallySurjective_iff_epi'`：isLocallySurjective_i
ff_epi' : IsLocallySurjective φ ↔ Epi φ
· 使用定理 `CategoryTheory.instHasFunctorialSurjectiveInjectiveFactorizationTypeFun`
：CategoryTheory.ConcreteCategory.HasFunctorialSurjectiveInjectiveFactorization (
Type u)
· 使用定理 `LightProfinite.instWEqualsLocallyBijectiveCoherentTopology`：∀ (A : Type 
u') [inst : CategoryTheory.Category.{u, u'} A] [CategoryTheory.Limits.HasLimits 
A]   [CategoryTheory.Limits.HasColimits A] {FA :…
· 使用定理 `CategoryTheory.Limits.Types.hasLimitsOfSize`：∀ [UnivLE.{v, u}], Category
Theory.Limits.HasLimitsOfSize.{w, v, u, u + 1} (Type u)
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfSize`：∀ [UnivLE.{v, u}], Catego
ryTheory.Limits.HasColimitsOfSize.{w, v, u, u + 1} (Type u)
· 使用定理 `CategoryTheory.Limits.PreservesColimits.preservesFilteredColimits`：∀ {C 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : C
ategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Types.instPreservesColimitsOfSizeForgetTypeFun`：CategoryT
heory.Limits.PreservesColimitsOfSize.{u_1, u_2, u, u, u + 1, u + 1} (CategoryThe
ory.forget (Type u))
· 使用定理 `CategoryTheory.Types.instPreservesLimitsOfSizeForgetTypeFun`：CategoryThe
ory.Limits.PreservesLimitsOfSize.{u_1, u_2, u, u, u + 1, u + 1} (CategoryTheory.
forget (Type u))
· 使用定理 `CategoryTheory.instReflectsIsomorphismsForgetTypeFun`：(CategoryTheory.fo
rget (Type u_1)).ReflectsIsomorphisms
· 使用定理 `CategoryTheory.hasSheafCompose_of_preservesMulticospan`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {A : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} A]   {B : Type u₃} [ins…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfShapeOfIsRightAdjoint`：∀ {J 
: Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1, 
u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Types.instIsEquivalenceForgetTypeFun`：(CategoryTheory.for
get (Type u)).IsEquivalence
· 使用定理 `CategoryTheory.SheafOfTypes.balanced`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopology C}   [CategoryTh
eory.HasSheafify J (Type w…
· 使用引理 `LightCondensed.isLocallySurjective_iff_locallySurjective_on_lightProfini
te`：isLocallySurjective_iff_locallySurjective_on_lightProfinite : IsLocallySurje
ctive f ↔ forall (S : LightProfinite) (y : ToType (Y.obj.obj ⟨S⟩…
· 使用定理 `CategoryTheory.Limits.instPreservesFiniteProductsOfPreservesFiniteLimits
`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [ins
t_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
-/
lemma epi_iff_locallySurjective_on_lightProfinite : Epi f ↔
    ∀ (S : LightProfinite) (y : Y.obj.obj ⟨S⟩),
      (∃ (S' : LightProfinite) (φ : S' ⟶ S) (_ : Function.Surjective φ) (x : X.obj.obj ⟨S'⟩),
        f.hom.app ⟨S'⟩ x = Y.obj.map ⟨φ⟩ y) := by
  rw [← isLocallySurjective_iff_epi']
  exact LightCondensed.isLocallySurjective_iff_locallySurjective_on_lightProfinite _ f

end LightCondSet

namespace LightCondMod

variable (R : Type u) [Ring R] {X Y : LightCondMod.{u} R} (f : X ⟶ Y)

/-
**LightCondMod.epi_iff_locallySurjective_on_lightProfinite** 是 Mathlib 中的一个引理，位于
命名空间 `LightCondMod`。
形式化陈述：epi_iff_locallySurjective_on_lightProfinite : Epi f ↔ forall (S : LightPro
finite) (y : Y.obj.obj ⟨S⟩), (exists (S' : LightProfinite) (φ : S' ⟶ S) (_ : Fun
ction.Surjective φ) (x : X.obj.obj ⟨S'⟩), f.hom.app ⟨S'⟩ x = Y.obj.map ⟨φ⟩ y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Sheaf.isLocallySurjective_iff_epi'`：isLocallySurjective_i
ff_epi' : IsLocallySurjective φ ↔ Epi φ
· 使用定理 `CategoryTheory.ConcreteCategory.instHasFunctorialSurjectiveInjectiveFact
orization`：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] {FC : C → C 
→ Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunLike (FC X Y) …
· 使用定理 `CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Abelian C],   Catego
ryTheory.Limits.HasStrongEpiMonoFactorisations …
· 使用定理 `LightProfinite.instWEqualsLocallyBijectiveCoherentTopology`：∀ (A : Type 
u') [inst : CategoryTheory.Category.{u, u'} A] [CategoryTheory.Limits.HasLimits 
A]   [CategoryTheory.Limits.HasColimits A] {FA :…
· 使用定理 `ModuleCat.hasLimits'`：∀ {R : Type u} [inst : Ring R], CategoryTheory.Lim
its.HasLimits (ModuleCat R)
· 使用定理 `ModuleCat.hasColimitsOfSize`：∀ (R : Type w) [inst : Ring R] [CategoryThe
ory.Limits.HasColimitsOfSize.{v, u, w', w' + 1} AddCommGrpCat],   CategoryTheory
.Limits.HasColimi…
· 使用定理 `AddCommGrpCat.hasColimitsOfSize`：∀ [UnivLE.{u, w}], CategoryTheory.Limit
s.HasColimitsOfSize.{v, u, w, w + 1} AddCommGrpCat
· 使用定理 `ModuleCat.instReflectsIsomorphismsForgetLinearMapIdCarrier`：∀ {R : Type 
u} [inst : Ring R], (CategoryTheory.forget (ModuleCat R)).ReflectsIsomorphisms
· 使用定理 `CategoryTheory.hasSheafCompose_of_preservesMulticospan`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {A : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} A]   {B : Type u₃} [ins…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfShapeOfIsRightAdjoint`：∀ {J 
: Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1, 
u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `ModuleCat.instIsRightAdjointForgetLinearMapIdCarrier`：∀ (R : Type u) [in
st : Ring R], (CategoryTheory.forget (ModuleCat R)).IsRightAdjoint
· 使用定理 `CategoryTheory.balanced_of_strongMonoCategory`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [CategoryTheory.StrongMonoCategory C],   Categor
yTheory.Balanced C
· 使用定理 `CategoryTheory.strongMonoCategory_of_regularMonoCategory`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheory.IsRegularMonoCateg
ory C],   CategoryTheory.StrongMonoCategory C
· 使用定理 `CategoryTheory.regularMonoCategoryOfNormalMonoCategory`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasZ
eroMorphisms C]   [CategoryTheory.IsNormalMo…
· 使用定理 `CategoryTheory.Abelian.toIsNormalMonoCategory`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} [self : CategoryTheory.Abelian C],   CategoryThe
ory.IsNormalMonoCategory C
· 使用引理 `LightCondensed.isLocallySurjective_iff_locallySurjective_on_lightProfini
te`：isLocallySurjective_iff_locallySurjective_on_lightProfinite : IsLocallySurje
ctive f ↔ forall (S : LightProfinite) (y : ToType (Y.obj.obj ⟨S⟩…
· 使用定理 `CategoryTheory.Limits.instPreservesFiniteProductsOfPreservesFiniteLimits
`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [ins
t_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
-/
lemma epi_iff_locallySurjective_on_lightProfinite : Epi f ↔
    ∀ (S : LightProfinite) (y : Y.obj.obj ⟨S⟩),
      (∃ (S' : LightProfinite) (φ : S' ⟶ S) (_ : Function.Surjective φ) (x : X.obj.obj ⟨S'⟩),
        f.hom.app ⟨S'⟩ x = Y.obj.map ⟨φ⟩ y) := by
  rw [← isLocallySurjective_iff_epi']
  exact LightCondensed.isLocallySurjective_iff_locallySurjective_on_lightProfinite _ f
/-
**LightCondMod.** 是 Mathlib 中的一个实例，位于命名空间 `LightCondMod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (LightCondensed.forget R).ReflectsEpimorphisms where
  reflects f hf := by
    rw [← Sheaf.isLocallySurjective_iff_epi'] at hf ⊢
    exact (Presheaf.isLocallySurjective_iff_whisker_forget _ f.hom).mpr hf
/-
**LightCondMod.** 是 Mathlib 中的一个实例，位于命名空间 `LightCondMod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (LightCondensed.forget R).PreservesEpimorphisms where
  preserves f hf := by
    rw [← Sheaf.isLocallySurjective_iff_epi'] at hf ⊢
    exact (Presheaf.isLocallySurjective_iff_whisker_forget _ f.hom).mp hf

set_option backward.isDefEq.respectTransparency false in
/-
**LightCondMod.factorsThru_lightProfinite_epi_of_epi** 是 Mathlib 中的一个引理，位于命名空间 `
LightCondMod`。
形式化陈述：factorsThru_lightProfinite_epi_of_epi [Epi f] {S : LightProfinite} (p : (L
ightCondensed.free R).obj S.toCondensed ⟶ Y) : exists (T : LightProfinite) (π : 
T ⟶ S) (g : ((LightCondensed.free R).obj T.toCondensed) ⟶ X), Epi π ∧ (lightProf
initeToLightCondSet ⋙ (LightCondensed.free R)).map π ≫ p = g ≫ f
参数：p : (LightCondensed.free R).obj S.toCondensed ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LightCondMod.instPreservesEpimorphismsLightCondSetForget`：∀ (R : Type u)
 [inst : Ring R], (LightCondensed.forget R).PreservesEpimorphisms
· 使用定理 `CategoryTheory.instPrecoherentOfFinitaryPreExtensiveOfPreregular`：∀ (C :
 Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Finitar
yPreExtensive C]   [CategoryTheory.Preregular C], Cate…
· 使用定理 `CategoryTheory.FinitaryExtensive.toFinitaryPreExtensive`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.FinitaryExtensive C], 
  CategoryTheory.FinitaryPreExtensive C
· 使用定理 `CompHausLike.instFinitaryExtensiveOfHasExplicitPullbacksOfInclusions`：∀ 
{P : TopCat → Prop} [inst : CompHausLike.HasExplicitFiniteCoproducts P]   [CompH
ausLike.HasExplicitPullbacksOfInclusions P], CategoryTheor…
· 使用定理 `LightProfinite.instHasExplicitFiniteCoproductsAndTotallyDisconnectedSpac
eCarrierSecondCountableTopology`：CompHausLike.HasExplicitFiniteCoproducts fun Y 
=> TotallyDisconnectedSpace ↑Y ∧ SecondCountableTopology ↑Y
· 使用定理 `CompHausLike.instHasExplicitPullbacksOfInclusionsOfHasExplicitPullbacks`
：∀ {P : TopCat → Prop} [CompHausLike.HasExplicitPullbacks P] [inst : CompHausLik
e.HasExplicitFiniteCoproducts P],   CompHausLike.HasExplicitP…
· 使用定理 `LightProfinite.instHasExplicitPullbacksAndTotallyDisconnectedSpaceCarrie
rSecondCountableTopology`：CompHausLike.HasExplicitPullbacks fun Y => TotallyDisc
onnectedSpace ↑Y ∧ SecondCountableTopology ↑Y
· 使用定理 `LightProfinite.instPreregular`：CategoryTheory.Preregular LightProfinite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LightCondSet.epi_iff_locallySurjective_on_lightProfinite`：epi_iff_locall
ySurjective_on_lightProfinite : Epi f ↔ forall (S : LightProfinite) (y : Y.obj.o
bj ⟨S⟩), (exists (S' : LightProfinite) (φ : S'…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LightProfinite.epi_iff_surjective`：epi_iff_surjective {X Y : LightProfin
ite.{u}} (f : X ⟶ Y) : Epi f ↔ Function.Surjective f
· 使用定理 `CategoryTheory.Functor.comp_map`：comp_map (F : C ⥤ D) (G : D ⥤ E) {X Y :
 C} (f : X ⟶ Y) : (F ⋙ G).map f = G.map (F.map f)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Adjunction.homEquiv_naturality_left_square_iff`：homEquiv_
naturality_left_square_iff (f : X' ⟶ X) (g : F.obj X ⟶ Y') (h : F.obj X' ⟶ Y) (k
 : Y ⟶ Y') : (f ≫ (adj.homEquiv X Y') g = (adj.homE…
· 使用定理 `CategoryTheory.Sheaf.hom_ext_iff`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C} {A : Type u₂} 
  [inst_1 : CategoryTh…
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用引理 `CategoryTheory.GrothendieckTopology.yonedaEquiv_symm_naturality_right`：y
onedaEquiv_symm_naturality_right (X : C) {F F' : Sheaf J (Type v)} (f : F ⟶ F') 
(x : F.obj.obj ⟨X⟩) : J.yonedaEquiv.symm x ≫ f = J.yonedaEq…
· 使用引理 `CategoryTheory.GrothendieckTopology.map_yonedaEquiv'`：map_yonedaEquiv' {
X Y : Cᵒᵖ} {F : Sheaf J (Type v)} (f : J.yoneda.obj (unop X) ⟶ F) (g : X ⟶ Y) : 
F.obj.map g (J.yonedaEquiv f) = f.hom.app …
-/
lemma factorsThru_lightProfinite_epi_of_epi [Epi f]
    {S : LightProfinite} (p : (LightCondensed.free R).obj S.toCondensed ⟶ Y) :
      ∃ (T : LightProfinite) (π : T ⟶ S) (g : ((LightCondensed.free R).obj T.toCondensed) ⟶ X),
        Epi π ∧ (lightProfiniteToLightCondSet ⋙ (LightCondensed.free R)).map π ≫ p = g ≫ f := by
  have : Epi ((LightCondensed.forget _).map f) := inferInstance
  rw [LightCondSet.epi_iff_locallySurjective_on_lightProfinite] at this
  obtain ⟨T, π, hπ, x, hx⟩ := this S <| (coherentTopology LightProfinite).yonedaEquiv <|
    (LightCondensed.freeForgetAdjunction R).homEquiv S.toCondensed Y p
  refine ⟨T, π, ((LightCondensed.freeForgetAdjunction R).homEquiv T.toCondensed X).symm
    ((coherentTopology LightProfinite).yonedaEquiv.symm x),
    (LightProfinite.epi_iff_surjective π).mpr hπ, ?_⟩
  rw [Functor.comp_map, ← Adjunction.homEquiv_naturality_left_square_iff
    (LightCondensed.freeForgetAdjunction R), Sheaf.hom_ext_iff, Equiv.apply_symm_apply,
    GrothendieckTopology.yonedaEquiv_symm_naturality_right, hx,
    GrothendieckTopology.map_yonedaEquiv', ← GrothendieckTopology.yonedaEquiv_symm_naturality_right]
  rfl

end LightCondMod

namespace LightCondensed

variable (R : Type*) [Ring R]
variable {F : ℕᵒᵖ ⥤ LightCondMod R} {c : Cone F} (hc : IsLimit c)
  (hF : ∀ n, Epi (F.map (homOfLE (Nat.le_succ n)).op))

include hc hF in
/-
**LightCondensed.epi_** 是 Mathlib 中的一个引理，位于命名空间 `LightCondensed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma epi_π_app_zero_of_epi : Epi (c.π.app ⟨0⟩) := by
  apply Functor.epi_of_epi_map (forget R)
  change Epi (((forget R).mapCone c).π.app ⟨0⟩)
  apply coherentTopology.epi_π_app_zero_of_epi
  · simp only [LightProfinite.effectiveEpi_iff_surjective]
    exact fun x h ↦ Concrete.surjective_π_app_zero_of_surjective_map (limit.isLimit x) h
  · have := (freeForgetAdjunction R).isRightAdjoint
    exact isLimitOfPreserves _ hc
  · exact fun _ ↦ (forget R).map_epi _

end LightCondensed

open CategoryTheory.Limits.SequentialProduct

namespace LightCondensed

variable (n : ℕ)

attribute [local instance] functorMap_epi Abelian.hasFiniteBiproducts

variable {R : Type u} [Ring R] {M N : ℕ → LightCondMod.{u} R} (f : ∀ n, M n ⟶ N n) [∀ n, Epi (f n)]

set_option backward.defeqAttrib.useBackward true in
/-
**LightCondensed.** 是 Mathlib 中的一个实例，位于命名空间 `LightCondensed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Epi (Limits.Pi.map f) :=
  epi_π_app_zero_of_epi R (isLimit f) (fun n ↦ by
    simp only [Nat.succ_eq_add_one, Functor.ofOpSequence_obj, homOfLE_leOfHom,
      Functor.ofOpSequence_map_homOfLE_succ]
    infer_instance)

set_option backward.defeqAttrib.useBackward true in
/-
**LightCondensed.** 是 Mathlib 中的一个实例，位于命名空间 `LightCondensed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (lim (J := Discrete ℕ) (C := LightCondMod R)).PreservesEpimorphisms where
  preserves f _ := by
    have : lim.map f = (Pi.isoLimit _).inv ≫ Limits.Pi.map (f.app ⟨·⟩) ≫ (Pi.isoLimit _).hom := by
      apply limit.hom_ext
      intro ⟨n⟩
      simp
    rw [this]
    dsimp
    infer_instance

end LightCondensed

