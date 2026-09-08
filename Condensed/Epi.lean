/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Sites.Coherent.LocallySurjective
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.Condensed.Equivalence
public import Mathlib.Condensed.Module
/-!

# Epimorphisms of condensed objects

This file characterises epimorphisms of condensed sets and condensed `R`-modules for any ring `R`,
as those morphisms which are objectwise surjective on `Stonean` (see
`CondensedSet.epi_iff_surjective_on_stonean` and `CondensedMod.epi_iff_surjective_on_stonean`).
-/

public section

universe v u w u' v'

open CategoryTheory Sheaf Opposite Limits Condensed ConcreteCategory

namespace Condensed

variable (A : Type u') [Category.{v'} A] {FA : A → A → Type*} {CA : A → Type v'}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{v'} A FA]
  [HasFunctorialSurjectiveInjectiveFactorization A]

variable {X Y : Condensed.{u} A} (f : X ⟶ Y)

set_option Elab.async false in  -- TODO: universe levels from type are unified in proof
variable
  [(coherentTopology CompHaus).WEqualsLocallyBijective A]
  [HasSheafify (coherentTopology CompHaus) A]
  [(coherentTopology CompHaus.{u}).HasSheafCompose (CategoryTheory.forget A)]
  [Balanced (Sheaf (coherentTopology CompHaus) A)]
  [PreservesFiniteProducts (CategoryTheory.forget A)] in
/-
**Condensed.epi_iff_locallySurjective_on_compHaus** 是 Mathlib 中的一个引理，位于命名空间 `Con
densed`。
形式化陈述：epi_iff_locallySurjective_on_compHaus : Epi f ↔ forall (S : CompHaus) (y :
 ToType (Y.obj.obj ⟨S⟩)), (exists (S' : CompHaus) (φ : S' ⟶ S) (_ : Function.Sur
jective φ) (x : ToType (X.obj.obj ⟨S'⟩)), f.hom.app ⟨S'⟩ x = Y.obj.map ⟨φ⟩ y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instPrecoherentOfFinitaryPreExtensiveOfPreregular`：∀ (C :
 Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Finitar
yPreExtensive C]   [CategoryTheory.Preregular C], Cate…
· 使用定理 `CategoryTheory.FinitaryExtensive.toFinitaryPreExtensive`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.FinitaryExtensive C], 
  CategoryTheory.FinitaryPreExtensive C
· 使用定理 `CompHausLike.instFinitaryExtensiveOfHasExplicitPullbacksOfInclusions`：∀ 
{P : TopCat → Prop} [inst : CompHausLike.HasExplicitFiniteCoproducts P]   [CompH
ausLike.HasExplicitPullbacksOfInclusions P], CategoryTheor…
· 使用定理 `CompHaus.instHasExplicitFiniteCoproductsTrue`：CompHausLike.HasExplicitFi
niteCoproducts fun x => True
· 使用定理 `CompHausLike.instHasExplicitPullbacksOfInclusionsOfHasExplicitPullbacks`
：∀ {P : TopCat → Prop} [CompHausLike.HasExplicitPullbacks P] [inst : CompHausLik
e.HasExplicitFiniteCoproducts P],   CompHausLike.HasExplicitP…
· 使用定理 `CompHaus.instHasExplicitPullbacksTrue`：CompHausLike.HasExplicitPullbacks
 fun x => True
· 使用定理 `CompHaus.instPreregular`：CategoryTheory.Preregular CompHaus
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Sheaf.isLocallySurjective_iff_epi'`：isLocallySurjective_i
ff_epi' : IsLocallySurjective φ ↔ Epi φ
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
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `CompHaus.effectiveEpi_tfae`：effectiveEpi_tfae {B X : CompHaus.{u}} (π : 
X ⟶ B) : TFAE [ EffectiveEpi π , Epi π , Function.Surjective π ]
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma epi_iff_locallySurjective_on_compHaus : Epi f ↔
    ∀ (S : CompHaus) (y : ToType (Y.obj.obj ⟨S⟩)),
      (∃ (S' : CompHaus) (φ : S' ⟶ S) (_ : Function.Surjective φ) (x : ToType (X.obj.obj ⟨S'⟩)),
        f.hom.app ⟨S'⟩ x = Y.obj.map ⟨φ⟩ y) := by
  rw [← isLocallySurjective_iff_epi', coherentTopology.isLocallySurjective_iff,
    regularTopology.isLocallySurjective_iff]
  simp_rw [((CompHaus.effectiveEpi_tfae _).out 0 2 :)]

set_option Elab.async false in  -- TODO: universe levels from type are unified in proof
variable
  [PreservesFiniteProducts (CategoryTheory.forget A)]
  [∀ (X : CompHausᵒᵖ), HasLimitsOfShape (StructuredArrow X Stonean.toCompHaus.op) A]
  [(extensiveTopology Stonean).WEqualsLocallyBijective A]
  [HasSheafify (extensiveTopology Stonean) A]
  [(extensiveTopology Stonean.{u}).HasSheafCompose (CategoryTheory.forget A)]
  [Balanced (Sheaf (extensiveTopology Stonean) A)] in
/-
**Condensed.epi_iff_surjective_on_stonean** 是 Mathlib 中的一个引理，位于命名空间 `Condensed`。
形式化陈述：epi_iff_surjective_on_stonean : Epi f ↔ forall (S : Stonean), Function.Sur
jective (f.hom.app (op S.compHaus))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.FinitaryExtensive.toFinitaryPreExtensive`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.FinitaryExtensive C], 
  CategoryTheory.FinitaryPreExtensive C
· 使用定理 `CompHausLike.instFinitaryExtensiveOfHasExplicitPullbacksOfInclusions`：∀ 
{P : TopCat → Prop} [inst : CompHausLike.HasExplicitFiniteCoproducts P]   [CompH
ausLike.HasExplicitPullbacksOfInclusions P], CategoryTheor…
· 使用定理 `Stonean.instHasExplicitFiniteCoproductsExtremallyDisconnectedCarrier`：Co
mpHausLike.HasExplicitFiniteCoproducts fun Y => ExtremallyDisconnected ↑Y
· 使用定理 `Stonean.instHasExplicitPullbacksOfInclusionsExtremallyDisconnectedCarrie
r`：CompHausLike.HasExplicitPullbacksOfInclusions fun Y => ExtremallyDisconnected
 ↑Y
· 使用定理 `CategoryTheory.instPrecoherentOfFinitaryPreExtensiveOfPreregular`：∀ (C :
 Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Finitar
yPreExtensive C]   [CategoryTheory.Preregular C], Cate…
· 使用定理 `Stonean.instPreregular`：CategoryTheory.Preregular Stonean
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.epi_map_iff_epi`：epi_map_iff_epi [hF₁ : Preserves
Epimorphisms F] [hF₂ : ReflectsEpimorphisms F] : Epi (F.map f) ↔ Epi f
· 使用定理 `CategoryTheory.preservesEpimorphisms_of_preservesColimitsOfShape`：∀ {C :
 Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesFiniteColimits.preservesFiniteColimits`：∀
 {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1
 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesColimits.preservesFiniteColimits`：∀ {C : 
Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfSizeOfIsLeftAdjoint`：∀ {C 
: Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_2, u_2} C]   [inst
_1 : CategoryTheory.Category.{v_3, u_3} D] (F : Categor…
· 使用定理 `CategoryTheory.Functor.isLeftAdjoint_of_isEquivalence`：∀ {C : Type u₁} [
inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheor
y.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_inverse`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.inv…
· 使用定理 `CategoryTheory.reflectsEpimorphisms_of_reflectsColimitsOfShape`：∀ {C : T
ype u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Cate
goryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.ReflectsFiniteColimits.reflects`：∀ {C : Type u₁} {
inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheor
y.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.instReflectsFiniteColimitsOfReflectsColimits`：∀ {C
 : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : 
CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `Stonean.instProjective`：∀ (X : Stonean), CategoryTheory.Projective X
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
· 使用引理 `CategoryTheory.Sheaf.isLocallySurjective_iff_epi'`：isLocallySurjective_i
ff_epi' : IsLocallySurjective φ ↔ Epi φ
· 使用定理 `CategoryTheory.extensiveTopology.isLocallySurjective_iff`：∀ {C : Type u_
1} (D : Type u_2) [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} D] {FD : D → D …
-/
lemma epi_iff_surjective_on_stonean : Epi f ↔
    ∀ (S : Stonean), Function.Surjective (f.hom.app (op S.compHaus)) := by
  rw [← (StoneanCompHaus.equivalence A).inverse.epi_map_iff_epi,
    ← Presheaf.coherentExtensiveEquivalence.functor.epi_map_iff_epi,
    ← isLocallySurjective_iff_epi']
  exact extensiveTopology.isLocallySurjective_iff (D := A) _

end Condensed

namespace CondensedSet

variable {X Y : CondensedSet.{u}} (f : X ⟶ Y)

/-
**CondensedSet.epi_iff_locallySurjective_on_compHaus** 是 Mathlib 中的一个引理，位于命名空间 `
CondensedSet`。
形式化陈述：epi_iff_locallySurjective_on_compHaus : Epi f ↔ forall (S : CompHaus) (y :
 Y.obj.obj ⟨S⟩), (exists (S' : CompHaus) (φ : S' ⟶ S) (_ : Function.Surjective φ
) (x : X.obj.obj ⟨S'⟩), f.hom.app ⟨S'⟩ x = Y.obj.map ⟨φ⟩ y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Condensed.epi_iff_locallySurjective_on_compHaus`：epi_iff_locallySurjecti
ve_on_compHaus : Epi f ↔ forall (S : CompHaus) (y : ToType (Y.obj.obj ⟨S⟩)), (ex
ists (S' : CompHaus) (φ : S' ⟶ S) (_ …
· 使用定理 `CategoryTheory.instHasFunctorialSurjectiveInjectiveFactorizationTypeFun`
：CategoryTheory.ConcreteCategory.HasFunctorialSurjectiveInjectiveFactorization (
Type u)
· 使用定理 `CategoryTheory.GrothendieckTopology.instWEqualsLocallyBijectiveTypeFun`：
∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.Gro
thendieckTopology C),   J.WEqualsLocallyBijective (Type (max…
· 使用定理 `CategoryTheory.instPrecoherentOfFinitaryPreExtensiveOfPreregular`：∀ (C :
 Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Finitar
yPreExtensive C]   [CategoryTheory.Preregular C], Cate…
· 使用定理 `CategoryTheory.FinitaryExtensive.toFinitaryPreExtensive`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.FinitaryExtensive C], 
  CategoryTheory.FinitaryPreExtensive C
· 使用定理 `CompHausLike.instFinitaryExtensiveOfHasExplicitPullbacksOfInclusions`：∀ 
{P : TopCat → Prop} [inst : CompHausLike.HasExplicitFiniteCoproducts P]   [CompH
ausLike.HasExplicitPullbacksOfInclusions P], CategoryTheor…
· 使用定理 `CompHaus.instHasExplicitFiniteCoproductsTrue`：CompHausLike.HasExplicitFi
niteCoproducts fun x => True
· 使用定理 `CompHausLike.instHasExplicitPullbacksOfInclusionsOfHasExplicitPullbacks`
：∀ {P : TopCat → Prop} [CompHausLike.HasExplicitPullbacks P] [inst : CompHausLik
e.HasExplicitFiniteCoproducts P],   CompHausLike.HasExplicitP…
· 使用定理 `CompHaus.instHasExplicitPullbacksTrue`：CompHausLike.HasExplicitPullbacks
 fun x => True
· 使用定理 `CompHaus.instPreregular`：CategoryTheory.Preregular CompHaus
· 使用定理 `CategoryTheory.instHasSheafifyType`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] (J : CategoryTheory.GrothendieckTopology C),   CategoryTheo
ry.HasSheafify J (Type (…
· 使用定理 `CategoryTheory.hasSheafCompose_of_preservesMulticospan`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {A : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} A]   {B : Type u₃} [ins…
· 使用定理 `CategoryTheory.preservesLimit_of_createsLimit_and_hasLimit`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Types.instIsEquivalenceForgetTypeFun`：(CategoryTheory.for
get (Type u)).IsEquivalence
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.SheafOfTypes.balanced`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopology C}   [CategoryTh
eory.HasSheafify J (Type w…
· 使用定理 `CategoryTheory.Limits.instPreservesFiniteProductsOfPreservesFiniteLimits
`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [ins
t_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Types.instPreservesLimitsOfSizeForgetTypeFun`：CategoryThe
ory.Limits.PreservesLimitsOfSize.{u_1, u_2, u, u, u + 1, u + 1} (CategoryTheory.
forget (Type u))
-/
lemma epi_iff_locallySurjective_on_compHaus : Epi f ↔
    ∀ (S : CompHaus) (y : Y.obj.obj ⟨S⟩),
      (∃ (S' : CompHaus) (φ : S' ⟶ S) (_ : Function.Surjective φ) (x : X.obj.obj ⟨S'⟩),
        f.hom.app ⟨S'⟩ x = Y.obj.map ⟨φ⟩ y) :=
  Condensed.epi_iff_locallySurjective_on_compHaus _ f
/-
**CondensedSet.epi_iff_surjective_on_stonean** 是 Mathlib 中的一个引理，位于命名空间 `Condense
dSet`。
形式化陈述：epi_iff_surjective_on_stonean : Epi f ↔ forall (S : Stonean), Function.Sur
jective (f.hom.app (op S.compHaus))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Condensed.epi_iff_surjective_on_stonean`：epi_iff_surjective_on_stonean :
 Epi f ↔ forall (S : Stonean), Function.Surjective (f.hom.app (op S.compHaus))
· 使用定理 `CategoryTheory.instHasFunctorialSurjectiveInjectiveFactorizationTypeFun`
：CategoryTheory.ConcreteCategory.HasFunctorialSurjectiveInjectiveFactorization (
Type u)
· 使用定理 `CategoryTheory.Limits.instPreservesFiniteProductsOfPreservesFiniteLimits
`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [ins
t_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Types.instPreservesLimitsOfSizeForgetTypeFun`：CategoryThe
ory.Limits.PreservesLimitsOfSize.{u_1, u_2, u, u, u + 1, u + 1} (CategoryTheory.
forget (Type u))
· 使用定理 `CategoryTheory.Limits.Types.hasLimitsOfShape`：∀ {J : Type v} [inst : Cat
egoryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasLimi
tsOfShape J (Type u)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.GrothendieckTopology.instWEqualsLocallyBijectiveTypeFun`：
∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.Gro
thendieckTopology C),   J.WEqualsLocallyBijective (Type (max…
· 使用定理 `CategoryTheory.FinitaryExtensive.toFinitaryPreExtensive`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.FinitaryExtensive C], 
  CategoryTheory.FinitaryPreExtensive C
· 使用定理 `CompHausLike.instFinitaryExtensiveOfHasExplicitPullbacksOfInclusions`：∀ 
{P : TopCat → Prop} [inst : CompHausLike.HasExplicitFiniteCoproducts P]   [CompH
ausLike.HasExplicitPullbacksOfInclusions P], CategoryTheor…
· 使用定理 `Stonean.instHasExplicitFiniteCoproductsExtremallyDisconnectedCarrier`：Co
mpHausLike.HasExplicitFiniteCoproducts fun Y => ExtremallyDisconnected ↑Y
· 使用定理 `Stonean.instHasExplicitPullbacksOfInclusionsExtremallyDisconnectedCarrie
r`：CompHausLike.HasExplicitPullbacksOfInclusions fun Y => ExtremallyDisconnected
 ↑Y
· 使用定理 `CategoryTheory.instHasSheafifyType`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] (J : CategoryTheory.GrothendieckTopology C),   CategoryTheo
ry.HasSheafify J (Type (…
· 使用定理 `CategoryTheory.hasSheafCompose_of_preservesMulticospan`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {A : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} A]   {B : Type u₃} [ins…
· 使用定理 `CategoryTheory.preservesLimit_of_createsLimit_and_hasLimit`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Types.instIsEquivalenceForgetTypeFun`：(CategoryTheory.for
get (Type u)).IsEquivalence
· 使用定理 `CategoryTheory.SheafOfTypes.balanced`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopology C}   [CategoryTh
eory.HasSheafify J (Type w…
-/
lemma epi_iff_surjective_on_stonean : Epi f ↔
    ∀ (S : Stonean), Function.Surjective (f.hom.app (op S.compHaus)) :=
  Condensed.epi_iff_surjective_on_stonean _ f

end CondensedSet

namespace CondensedMod

variable (R : Type (u + 1)) [Ring R] {X Y : CondensedMod.{u} R} (f : X ⟶ Y)

/-
**CondensedMod.epi_iff_locallySurjective_on_compHaus** 是 Mathlib 中的一个引理，位于命名空间 `
CondensedMod`。
形式化陈述：epi_iff_locallySurjective_on_compHaus : Epi f ↔ forall (S : CompHaus) (y :
 Y.obj.obj ⟨S⟩), (exists (S' : CompHaus) (φ : S' ⟶ S) (_ : Function.Surjective φ
) (x : X.obj.obj ⟨S'⟩), f.hom.app ⟨S'⟩ x = Y.obj.map ⟨φ⟩ y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Condensed.epi_iff_locallySurjective_on_compHaus`：epi_iff_locallySurjecti
ve_on_compHaus : Epi f ↔ forall (S : CompHaus) (y : ToType (Y.obj.obj ⟨S⟩)), (ex
ists (S' : CompHaus) (φ : S' ⟶ S) (_ …
· 使用定理 `CategoryTheory.ConcreteCategory.instHasFunctorialSurjectiveInjectiveFact
orization`：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] {FC : C → C 
→ Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunLike (FC X Y) …
· 使用定理 `CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Abelian C],   Catego
ryTheory.Limits.HasStrongEpiMonoFactorisations …
· 使用定理 `CategoryTheory.GrothendieckTopology.instWEqualsLocallyBijectiveOfHasWeak
SheafifyOfHasSheafComposeOfPreservesSheafificationOfReflectsIsomorphismsForget`：
∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.Gro
thendieckTopology C) {D : Type w}   [inst_1 : CategoryTheory…
· 使用定理 `CategoryTheory.instPrecoherentOfFinitaryPreExtensiveOfPreregular`：∀ (C :
 Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Finitar
yPreExtensive C]   [CategoryTheory.Preregular C], Cate…
· 使用定理 `CategoryTheory.FinitaryExtensive.toFinitaryPreExtensive`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.FinitaryExtensive C], 
  CategoryTheory.FinitaryPreExtensive C
· 使用定理 `CompHausLike.instFinitaryExtensiveOfHasExplicitPullbacksOfInclusions`：∀ 
{P : TopCat → Prop} [inst : CompHausLike.HasExplicitFiniteCoproducts P]   [CompH
ausLike.HasExplicitPullbacksOfInclusions P], CategoryTheor…
· 使用定理 `CompHaus.instHasExplicitFiniteCoproductsTrue`：CompHausLike.HasExplicitFi
niteCoproducts fun x => True
· 使用定理 `CompHausLike.instHasExplicitPullbacksOfInclusionsOfHasExplicitPullbacks`
：∀ {P : TopCat → Prop} [CompHausLike.HasExplicitPullbacks P] [inst : CompHausLik
e.HasExplicitFiniteCoproducts P],   CompHausLike.HasExplicitP…
· 使用定理 `CompHaus.instHasExplicitPullbacksTrue`：CompHausLike.HasExplicitPullbacks
 fun x => True
· 使用定理 `CompHaus.instPreregular`：CategoryTheory.Preregular CompHaus
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfShapeOfIsRightAdjoint`：∀ {J 
: Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1, 
u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `ModuleCat.instIsRightAdjointForgetLinearMapIdCarrier`：∀ (R : Type u) [in
st : Ring R], (CategoryTheory.forget (ModuleCat R)).IsRightAdjoint
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `ModuleCat.hasColimitsOfShape`：∀ (R : Type w) [inst : Ring R] (J : Type u
) [inst_1 : CategoryTheory.Category.{v, u} J]   [CategoryTheory.Limits.HasColimi
tsOfShape J AddCom…
· 使用定理 `AddCommGrpCat.hasColimitsOfShape`：∀ {J : Type u} [inst : CategoryTheory.
Category.{v, u} J] [Small.{w, u} J],   CategoryTheory.Limits.HasColimitsOfShape 
J AddCommGrpCat
· 使用定理 `CategoryTheory.Limits.PreservesFilteredColimitsOfSize.preserves_filtered
_colimits`：∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type
 u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.isCofiltered_of_directed_ge_nonempty`：∀ (α : Type u) [ins
t : Preorder α] [IsCodirectedOrder α] [Nonempty α], CategoryTheory.IsCofiltered 
α
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `ModuleCat.instReflectsIsomorphismsForgetLinearMapIdCarrier`：∀ {R : Type 
u} [inst : Ring R], (CategoryTheory.forget (ModuleCat R)).ReflectsIsomorphisms
· 使用定理 `CategoryTheory.hasSheafCompose_of_preservesMulticospan`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {A : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} A]   {B : Type u₃} [ins…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.GrothendieckTopology.instPreservesSheafificationForgetOfP
reservesLimitsOfHasColimitsOfShapeOfPreservesColimitsOfShapeOppositeCoverOfHasLi
mitsOfShapeWalkingMulticospanOfReflectsIsomorphisms`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] (J : CategoryTheory.GrothendieckTopology C) {D : T
ype u_3}   [inst_1 : CategoryTheo…
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTh
eory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `ModuleCat.hasLimits'`：∀ {R : Type u} [inst : Ring R], CategoryTheory.Lim
its.HasLimits (ModuleCat R)
· 使用定理 `CategoryTheory.instHasSheafifyOfPreservesLimitsForgetOfHasFiniteLimitsOf
SmallOppositeCover`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (J 
: CategoryTheory.GrothendieckTopology C) (D : Type w)   [inst_1 : CategoryTheory
…
· 使用定理 `CategoryTheory.Abelian.hasFiniteLimits`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.Has
FiniteLimits C
· 使用定理 `CategoryTheory.balanced_of_strongMonoCategory`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [CategoryTheory.StrongMonoCategory C],   Categor
yTheory.Balanced C
· 使用定理 `CategoryTheory.strongMonoCategory_of_regularMonoCategory`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheory.IsRegularMonoCateg
ory C],   CategoryTheory.StrongMonoCategory C
（共 34 条，此处仅展示前 30 条）
-/
lemma epi_iff_locallySurjective_on_compHaus : Epi f ↔
    ∀ (S : CompHaus) (y : Y.obj.obj ⟨S⟩),
      (∃ (S' : CompHaus) (φ : S' ⟶ S) (_ : Function.Surjective φ) (x : X.obj.obj ⟨S'⟩),
        f.hom.app ⟨S'⟩ x = Y.obj.map ⟨φ⟩ y) :=
  Condensed.epi_iff_locallySurjective_on_compHaus _ f
/-
**CondensedMod.epi_iff_surjective_on_stonean** 是 Mathlib 中的一个引理，位于命名空间 `Condense
dMod`。
形式化陈述：epi_iff_surjective_on_stonean : Epi f ↔ forall (S : Stonean), Function.Sur
jective (f.hom.app (op S.compHaus))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimitsOfSizeShrink`：hasLimitsOfSizeShrink [HasL
imitsOfSize.{max v₁ v₂, max u₁ u₂} C] : HasLimitsOfSize.{v₁, u₁} C
· 使用定理 `ModuleCat.hasLimits'`：∀ {R : Type u} [inst : Ring R], CategoryTheory.Lim
its.HasLimits (ModuleCat R)
· 使用引理 `Condensed.epi_iff_surjective_on_stonean`：epi_iff_surjective_on_stonean :
 Epi f ↔ forall (S : Stonean), Function.Surjective (f.hom.app (op S.compHaus))
· 使用定理 `CategoryTheory.ConcreteCategory.instHasFunctorialSurjectiveInjectiveFact
orization`：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] {FC : C → C 
→ Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunLike (FC X Y) …
· 使用定理 `CategoryTheory.Abelian.instHasStrongEpiMonoFactorisations`：∀ {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Abelian C],   Catego
ryTheory.Limits.HasStrongEpiMonoFactorisations …
· 使用定理 `CategoryTheory.Limits.instPreservesFiniteProductsOfPreservesFiniteLimits
`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [ins
t_1 : CategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.instHasLimitsOfShapeOfHasLimitsOfSize`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTh
eory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.GrothendieckTopology.instWEqualsLocallyBijectiveOfHasWeak
SheafifyOfHasSheafComposeOfPreservesSheafificationOfReflectsIsomorphismsForget`：
∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.Gro
thendieckTopology C) {D : Type w}   [inst_1 : CategoryTheory…
· 使用定理 `CategoryTheory.FinitaryExtensive.toFinitaryPreExtensive`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.FinitaryExtensive C], 
  CategoryTheory.FinitaryPreExtensive C
· 使用定理 `CompHausLike.instFinitaryExtensiveOfHasExplicitPullbacksOfInclusions`：∀ 
{P : TopCat → Prop} [inst : CompHausLike.HasExplicitFiniteCoproducts P]   [CompH
ausLike.HasExplicitPullbacksOfInclusions P], CategoryTheor…
· 使用定理 `Stonean.instHasExplicitFiniteCoproductsExtremallyDisconnectedCarrier`：Co
mpHausLike.HasExplicitFiniteCoproducts fun Y => ExtremallyDisconnected ↑Y
· 使用定理 `Stonean.instHasExplicitPullbacksOfInclusionsExtremallyDisconnectedCarrie
r`：CompHausLike.HasExplicitPullbacksOfInclusions fun Y => ExtremallyDisconnected
 ↑Y
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfShapeOfIsRightAdjoint`：∀ {J 
: Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1, 
u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `ModuleCat.instIsRightAdjointForgetLinearMapIdCarrier`：∀ (R : Type u) [in
st : Ring R], (CategoryTheory.forget (ModuleCat R)).IsRightAdjoint
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `ModuleCat.hasColimitsOfShape`：∀ (R : Type w) [inst : Ring R] (J : Type u
) [inst_1 : CategoryTheory.Category.{v, u} J]   [CategoryTheory.Limits.HasColimi
tsOfShape J AddCom…
· 使用定理 `AddCommGrpCat.hasColimitsOfShape`：∀ {J : Type u} [inst : CategoryTheory.
Category.{v, u} J] [Small.{w, u} J],   CategoryTheory.Limits.HasColimitsOfShape 
J AddCommGrpCat
· 使用定理 `CategoryTheory.Limits.PreservesFilteredColimitsOfSize.preserves_filtered
_colimits`：∀ {C : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type
 u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.isCofiltered_of_directed_ge_nonempty`：∀ (α : Type u) [ins
t : Preorder α] [IsCodirectedOrder α] [Nonempty α], CategoryTheory.IsCofiltered 
α
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `ModuleCat.instReflectsIsomorphismsForgetLinearMapIdCarrier`：∀ {R : Type 
u} [inst : Ring R], (CategoryTheory.forget (ModuleCat R)).ReflectsIsomorphisms
· 使用定理 `CategoryTheory.hasSheafCompose_of_preservesMulticospan`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {A : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} A]   {B : Type u₃} [ins…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.GrothendieckTopology.instPreservesSheafificationForgetOfP
reservesLimitsOfHasColimitsOfShapeOfPreservesColimitsOfShapeOppositeCoverOfHasLi
mitsOfShapeWalkingMulticospanOfReflectsIsomorphisms`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] (J : CategoryTheory.GrothendieckTopology C) {D : T
ype u_3}   [inst_1 : CategoryTheo…
· 使用定理 `CategoryTheory.instHasSheafifyOfPreservesLimitsForgetOfHasFiniteLimitsOf
SmallOppositeCover`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (J 
: CategoryTheory.GrothendieckTopology C) (D : Type w)   [inst_1 : CategoryTheory
…
· 使用定理 `CategoryTheory.Abelian.hasFiniteLimits`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.Has
FiniteLimits C
· 使用定理 `CategoryTheory.balanced_of_strongMonoCategory`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [CategoryTheory.StrongMonoCategory C],   Categor
yTheory.Balanced C
· 使用定理 `CategoryTheory.strongMonoCategory_of_regularMonoCategory`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] [CategoryTheory.IsRegularMonoCateg
ory C],   CategoryTheory.StrongMonoCategory C
（共 32 条，此处仅展示前 30 条）
-/
lemma epi_iff_surjective_on_stonean : Epi f ↔
    ∀ (S : Stonean), Function.Surjective (f.hom.app (op S.compHaus)) :=
  have : HasLimitsOfSize.{u, u + 1} (ModuleCat R) :=
    hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} _
  Condensed.epi_iff_surjective_on_stonean _ f

end CondensedMod

