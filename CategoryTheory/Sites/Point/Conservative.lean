/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Category
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
public import Mathlib.CategoryTheory.Types.Epimorphisms

/-!
# Conservative families of points

Let `J` be a Grothendieck topology on a category `C`.
Let `P : ObjectProperty J.Point` be a family of points. We say that
`P` is a conservative family of points if the corresponding
fiber functors `Sheaf J (Type w) ⥤ Type w` jointly reflect
isomorphisms. Under suitable assumptions on the coefficient
category `A`, this implies that the fiber functors
`Sheaf J A ⥤ A` corresponding to the points in `P`
jointly reflect isomorphisms, epimorphisms and monomorphisms,
and they are also jointly faithful.

We provide a constructor `ObjectProperty.IsConservativeFamilyOfPoints.mk'`
which allows to verify that a family of points is conservative
using a condition involving covering sieves (SGA 4 IV 6.5 (a)).

-/

public section

universe w w' v v' u u'

namespace CategoryTheory

open Limits Opposite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (P : ObjectProperty (GrothendieckTopology.Point.{w} J))

namespace ObjectProperty

/-- Let `P : ObjectProperty J.Point` a family of points of a
site `(C, J)`). We say that it is a conservative family of points
if the corresponding fiber functors `Sheaf J (Type w) ⥤ Type w`
jointly reflect isomorphisms. -/
@[stacks 00YK "(1)"]
/-
**CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints** 是 Mathlib 中的一个结构，
位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：IsConservativeFamilyOfPoints : Prop where jointlyReflectIsomorphisms_type 
: JointlyReflectIsomorphisms (fun (Φ : P.FullSubcategory) => Φ.obj.sheafFiber (A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `P : ObjectProperty J.Point` a family of points of a
site `(C, J)`). We say that it is a conservative family of points
if the corresponding fiber functors `Sheaf J (Type w) ⥤ Type w`
jointly reflect isomorphisms.
-/
structure IsConservativeFamilyOfPoints : Prop where
  jointlyReflectIsomorphisms_type :
    JointlyReflectIsomorphisms
      (fun (Φ : P.FullSubcategory) ↦ Φ.obj.sheafFiber (A := Type w))

namespace IsConservativeFamilyOfPoints

variable {P} (hP : P.IsConservativeFamilyOfPoints)
  (A : Type u') [Category.{v'} A] [LocallySmall.{w} C]

section

variable
  [HasColimitsOfSize.{w, w} A]
  {FC : A → A → Type*} {CC : A → Type w}
  [∀ (X Y : A), FunLike (FC X Y) (CC X) (CC Y)]
  [ConcreteCategory.{w} A FC]
  [(forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{w, w} (forget A)]
  [hJ : J.HasSheafCompose (forget A)]

include hP hJ in
@[stacks 00YK "(1)"]
/-
**CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.jointlyReflectIsomo
rphisms** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.IsConservativeF
amilyOfPoints`。
形式化陈述：jointlyReflectIsomorphisms : JointlyReflectIsomorphisms (fun (Φ : P.FullSu
bcategory) => Φ.obj.sheafFiber (A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.isIso_iff_of_reflects_iso`：isIso_iff_of_reflects_iso {A B
 : C} (f : A ⟶ B) (F : C ⥤ D) [F.ReflectsIsomorphisms] : IsIso (F.map f) ↔ IsIso
 f
· 使用定理 `CategoryTheory.instReflectsIsomorphismsSheafSheafCompose`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {A : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} A]   {B : Type u₃} [ins…
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfSize`：∀ [UnivLE.{v, u}], Catego
ryTheory.Limits.HasColimitsOfSize.{w, v, u, u + 1} (Type u)
· 使用引理 `CategoryTheory.JointlyReflectIsomorphisms.isIso_iff`：isIso_iff {X Y : C}
 (f : X ⟶ Y) : IsIso f ↔ forall i, IsIso ((F i).map f)
· 使用定理 `CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.jointlyReflec
tIsomorphisms_type`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J 
: CategoryTheory.GrothendieckTopology C}   {P : CategoryTheory.ObjectProperty J.
…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.isomorphisms`：∀ (C : Type u)
 [inst : CategoryTheory.Category.{v, u} C], (CategoryTheory.MorphismProperty.iso
morphisms C).RespectsIso
-/
lemma jointlyReflectIsomorphisms :
    JointlyReflectIsomorphisms
      (fun (Φ : P.FullSubcategory) ↦ Φ.obj.sheafFiber (A := A)) where
  isIso {K L} f _ := by
    rw [← isIso_iff_of_reflects_iso _ (sheafCompose J (forget A)),
      hP.jointlyReflectIsomorphisms_type.isIso_iff]
    exact fun Φ ↦ ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
      (((Functor.mapArrowFunctor _ _).mapIso
        (Φ.obj.sheafFiberCompIso (forget A))).app (Arrow.mk f))).2
          (inferInstanceAs (IsIso ((forget A).map (Φ.obj.sheafFiber.map f))))

include hP hJ in
@[stacks 00YL "(1)"]
/-
**CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.jointlyReflectMonom
orphisms** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.IsConservative
FamilyOfPoints`。
形式化陈述：jointlyReflectMonomorphisms [AB5OfSize.{w, w} A] [HasFiniteLimits A] : Joi
ntlyReflectMonomorphisms (fun (Φ : P.FullSubcategory) => Φ.obj.sheafFiber (A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFilteredColimitsOfSize_of_hasColimitsOfSize`：∀ 
{C : Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.Ha
sColimitsOfSize.{w', w, v, u} C],   CategoryTheory.Limits.…
· 使用引理 `CategoryTheory.JointlyReflectIsomorphisms.jointlyReflectMonomorphisms`：j
ointlyReflectMonomorphisms [forall i, PreservesLimitsOfShape WalkingCospan (F i)
] [HasPullbacks C] : JointlyReflectMonomorphisms F where mo…
· 使用引理 `CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.jointlyReflec
tIsomorphisms`：jointlyReflectIsomorphisms : JointlyReflectIsomorphisms (fun (Φ :
 P.FullSubcategory) => Φ.obj.sheafFiber (A
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.instPreservesFiniteLimitsSheaf
SheafFiberOfLocallySmallOfHasFiniteLimitsOfAB5OfSize`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopology C} (Φ : 
J.Point)   {A : Type u'} [inst_1 :…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasFiniteLimits`：∀ (C : 
Type u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFini
teLimits C],   CategoryTheory.Limits.HasFiniteWidePul…
· 使用定理 `CategoryTheory.Sheaf.instHasFiniteLimits`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopology C} {D : Type
 w}   [inst_1 : CategoryTheory…
-/
lemma jointlyReflectMonomorphisms [AB5OfSize.{w, w} A] [HasFiniteLimits A] :
    JointlyReflectMonomorphisms
      (fun (Φ : P.FullSubcategory) ↦ Φ.obj.sheafFiber (A := A)) :=
  (hP.jointlyReflectIsomorphisms A).jointlyReflectMonomorphisms

include hP hJ in
@[stacks 00YL "(2)"]
/-
**CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.jointlyReflectEpimo
rphisms** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.IsConservativeF
amilyOfPoints`。
形式化陈述：jointlyReflectEpimorphisms [HasWeakSheafify J A] [HasProducts.{w} A] : Joi
ntlyReflectEpimorphisms (fun (Φ : P.FullSubcategory) => Φ.obj.sheafFiber (A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.JointlyReflectIsomorphisms.jointlyReflectEpimorphisms`：jo
intlyReflectEpimorphisms [forall i, PreservesColimitsOfShape WalkingSpan (F i)] 
[HasPushouts C] : JointlyReflectEpimorphisms F where epi f…
· 使用引理 `CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.jointlyReflec
tIsomorphisms`：jointlyReflectIsomorphisms : JointlyReflectIsomorphisms (fun (Φ :
 P.FullSubcategory) => Φ.obj.sheafFiber (A
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint`：∀ {J
 : Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1,
 u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.instIsLeftAdjointSheafSheafFib
er`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory
.GrothendieckTopology C} (Φ : J.Point)   {A : Type u'} [inst_1 :…
· 使用定理 `CategoryTheory.Sheaf.instHasColimitsOfShape`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopology C} {D : T
ype w}   [inst_1 : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.hasPushouts_of_hasWidePushouts`：∀ (D : Type u) [in
st : CategoryTheory.Category.{v, u} D] [CategoryTheory.Limits.HasWidePushouts D]
,   CategoryTheory.Limits.HasPushouts D
· 使用定理 `CategoryTheory.Limits.instHasColimitsOfShapeOfHasColimitsOfSize`：∀ {C : 
Type u} [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : Catego
ryTheory.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
lemma jointlyReflectEpimorphisms
    [HasWeakSheafify J A] [HasProducts.{w} A] :
    JointlyReflectEpimorphisms
      (fun (Φ : P.FullSubcategory) ↦ Φ.obj.sheafFiber (A := A)) :=
  (hP.jointlyReflectIsomorphisms A).jointlyReflectEpimorphisms

include hP hJ in
@[stacks 00YL "(3)"]
/-
**CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.jointlyFaithful** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoin
ts`。
形式化陈述：jointlyFaithful [AB5OfSize.{w, w} A] [HasFiniteLimits A] : JointlyFaithful
 (fun (Φ : P.FullSubcategory) => Φ.obj.sheafFiber (A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFilteredColimitsOfSize_of_hasColimitsOfSize`：∀ 
{C : Type u} [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.Ha
sColimitsOfSize.{w', w, v, u} C],   CategoryTheory.Limits.…
· 使用引理 `CategoryTheory.JointlyReflectIsomorphisms.jointlyFaithful`：jointlyFaithf
ul [forall i, PreservesLimitsOfShape WalkingParallelPair (F i)] [HasEqualizers C
] : JointlyFaithful F
· 使用引理 `CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.jointlyReflec
tIsomorphisms`：jointlyReflectIsomorphisms : JointlyReflectIsomorphisms (fun (Φ :
 P.FullSubcategory) => Φ.obj.sheafFiber (A
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.instPreservesFiniteLimitsSheaf
SheafFiberOfLocallySmallOfHasFiniteLimitsOfAB5OfSize`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopology C} (Φ : 
J.Point)   {A : Type u'} [inst_1 :…
· 使用定理 `CategoryTheory.Sheaf.instHasLimitsOfShape`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopology C} {D : Typ
e w}   [inst_1 : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.hasLimitsOfShape_of_hasFiniteLimits`：∀ (C : Type u
) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLimi
ts C] (J : Type w)   [inst_2 : CategoryTheory.S…
-/
lemma jointlyFaithful [AB5OfSize.{w, w} A] [HasFiniteLimits A] :
    JointlyFaithful
      (fun (Φ : P.FullSubcategory) ↦ Φ.obj.sheafFiber (A := A)) :=
  (hP.jointlyReflectIsomorphisms A).jointlyFaithful

variable {A} in
include hP hJ in
/-
**CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.W_iff** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints`。
形式化陈述：W_iff {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) [HasWeakSheafify J A] [HasProducts.{w} A
] : J.W f ↔ forall (Φ : P.FullSubcategory), IsIso (Φ.obj.presheafFiber.map f)
参数：f : F ⟶ G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.GrothendieckTopology.W_iff`：W_iff {P₁ P₂ : Cᵒᵖ ⥤ A} (f : 
P₁ ⟶ P₂) : J.W f ↔ IsIso ((presheafToSheaf J A).map f)
· 使用引理 `CategoryTheory.JointlyReflectIsomorphisms.isIso_iff`：isIso_iff {X Y : C}
 (f : X ⟶ Y) : IsIso f ↔ forall i, IsIso ((F i).map f)
· 使用引理 `CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.jointlyReflec
tIsomorphisms`：jointlyReflectIsomorphisms : JointlyReflectIsomorphisms (fun (Φ :
 P.FullSubcategory) => Φ.obj.sheafFiber (A
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.isomorphisms`：∀ (C : Type u)
 [inst : CategoryTheory.Category.{v, u} C], (CategoryTheory.MorphismProperty.iso
morphisms C).RespectsIso
-/
lemma W_iff {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) [HasWeakSheafify J A]
    [HasProducts.{w} A] :
    J.W f ↔ ∀ (Φ : P.FullSubcategory), IsIso (Φ.obj.presheafFiber.map f) := by
  rw [GrothendieckTopology.W_iff, (hP.jointlyReflectIsomorphisms A).isIso_iff]
  exact forall_congr'
    (fun Φ ↦ (MorphismProperty.isomorphisms A).arrow_mk_iso_iff
      (((Functor.mapArrowFunctor _ _).mapIso
        (Φ.obj.presheafToSheafCompSheafFiberIso A)).app (Arrow.mk f)))

omit [(forget A).ReflectsIsomorphisms] hJ in
include hP in
variable {A} in
/-
**CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.jointly_reflect_isL
ocallySurjective** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.IsCons
ervativeFamilyOfPoints`。
形式化陈述：jointly_reflect_isLocallySurjective [J.WEqualsLocallyBijective (Type w)] [
HasSheafify J (Type w)] {X Y : Cᵒᵖ ⥤ A} (f : X ⟶ Y) (hf : forall (Φ : P.FullSubc
ategory), Function.Surjective (Φ.obj.presheafFiber.map f)) : Presheaf.IsLocallyS
urjective J f
参数：Type w；Type w；f : X ⟶ Y；hf : forall (Φ : P.FullSubcategory), Function.Surject
ive (Φ.obj.presheafFiber.map f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presheaf.isLocallySurjective_iff_whisker_forget`：isLocall
ySurjective_iff_whisker_forget {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) : IsLocallySurjective
 J f ↔ IsLocallySurjective J (whiskerRight f (forget…
· 使用定理 `CategoryTheory.instHasWeakSheafifyOfHasSheafify`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C)
 (A : Type u₂)   [inst_1 : CategoryTh…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Presheaf.isLocallySurjective_presheafToSheaf_map_iff`：isL
ocallySurjective_presheafToSheaf_map_iff : Sheaf.IsLocallySurjective ((presheafT
oSheaf J A).map φ) ↔ IsLocallySurjective J φ
· 使用引理 `CategoryTheory.Sheaf.isLocallySurjective_iff_epi`：isLocallySurjective_if
f_epi {F G : Sheaf J (Type w)} (φ : F ⟶ G) [HasSheafify J (Type w)] : IsLocallyS
urjective φ ↔ Epi φ
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfSize`：∀ [UnivLE.{v, u}], Catego
ryTheory.Limits.HasColimitsOfSize.{w, v, u, u + 1} (Type u)
· 使用定理 `CategoryTheory.JointlyReflectEpimorphisms.epi_iff`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{u_4, u_1} C] {I : Type u_2} {D : I → Type u_3}   [i
nst_1 : (i : I) → CategoryTheory.Catego…
· 使用引理 `CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.jointlyReflec
tEpimorphisms`：jointlyReflectEpimorphisms [HasWeakSheafify J A] [HasProducts.{w}
 A] : JointlyReflectEpimorphisms (fun (Φ : P.FullSubcategory) => Φ.obj.shea…
· 使用定理 `CategoryTheory.reflectsIsomorphisms_of_full_and_faithful`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} D] (F : Categor…
· 使用定理 `CategoryTheory.Types.instFullForgetTypeFun`：(CategoryTheory.forget (Type
 u)).Full
· 使用定理 `CategoryTheory.instFaithfulForget`：∀ (C : Type u_1) [inst : CategoryTheo
ry.Category.{v_1, u_1} C] {FC : outParam (C → C → Type u_2)}   {CC : outParam (C
 → Type w)} [inst_1 : o…
· 使用定理 `CategoryTheory.Limits.PreservesColimits.preservesFilteredColimits`：∀ {C 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : C
ategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Types.instPreservesColimitsOfSizeForgetTypeFun`：CategoryT
heory.Limits.PreservesColimitsOfSize.{u_1, u_2, u, u, u + 1, u + 1} (CategoryThe
ory.forget (Type u))
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
· 使用定理 `CategoryTheory.Limits.Types.instHasProductsType`：CategoryTheory.Limits.H
asProducts (Type v)
· 使用定理 `CategoryTheory.preservesEpimorphisms_of_preservesColimitsOfShape`：∀ {C :
 Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint`：∀ {J
 : Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1,
 u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.instIsLeftAdjointSheafSheafFib
er`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory
.GrothendieckTopology C} (Φ : J.Point)   {A : Type u'} [inst_1 :…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.epimorphisms`：∀ (C : Type u)
 [inst : CategoryTheory.Category.{v, u} C], (CategoryTheory.MorphismProperty.epi
morphisms C).RespectsIso
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
lemma jointly_reflect_isLocallySurjective
    [J.WEqualsLocallyBijective (Type w)] [HasSheafify J (Type w)]
    {X Y : Cᵒᵖ ⥤ A} (f : X ⟶ Y)
    (hf : ∀ (Φ : P.FullSubcategory),
      Function.Surjective (Φ.obj.presheafFiber.map f)) :
    Presheaf.IsLocallySurjective J f := by
  simp only [← ofHom_epi_iff_surjective] at hf
  rw [Presheaf.isLocallySurjective_iff_whisker_forget,
    ← Presheaf.isLocallySurjective_presheafToSheaf_map_iff,
    Sheaf.isLocallySurjective_iff_epi,
    (hP.jointlyReflectEpimorphisms (Type w)).epi_iff]
  exact fun Φ ↦ ((MorphismProperty.epimorphisms (Type w)).arrow_mk_iso_iff
    (((Functor.mapArrowFunctor _ _).mapIso
      ((Φ.obj.presheafFiberCompIso (forget A)).symm ≪≫
        Functor.isoWhiskerLeft _ (Φ.obj.presheafToSheafCompSheafFiberIso (Type w)).symm)).app
          (Arrow.mk f))).1 (hf Φ)

end

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.jointly_reflect_ofA
rrows_mem** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.IsConservativ
eFamilyOfPoints`。
形式化陈述：jointly_reflect_ofArrows_mem [HasSheafify J (Type w)] [J.WEqualsLocallyBij
ective (Type w)] (hP : P.IsConservativeFamilyOfPoints) {X : C} {ι : Type*} [Smal
l.{w} ι] {U : ι -> C} (f : forall i, U i ⟶ X) : Sieve.ofArrows _ f in J X ↔ fora
ll (Φ : P.FullSubcategory) (x : Φ.obj.fiber.obj X), exists (i : ι) (y : Φ.obj.fi
ber.obj (U i)), Φ.obj.fiber.map (f i) y = x
参数：Type w；Type w；hP : P.IsConservativeFamilyOfPoints；f : forall i, U i ⟶ X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.jointly_surjective`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckT
opology C} (self : J.Point)   {X : C},   ∀ R ∈ J X…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用引理 `CategoryTheory.GrothendieckTopology.ofArrows_mem_iff_isLocallySurjective
_sigmaDesc_shrinkYoneda_map`：ofArrows_mem_iff_isLocallySurjective_sigmaDesc_shri
nkYoneda_map [LocallySmall.{w} C] {S : C} {ι : Type*} [Small.{w} ι] {X : ι -> C}
 (f : for…
· 使用引理 `CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.jointly_refle
ct_isLocallySurjective`：jointly_reflect_isLocallySurjective [J.WEqualsLocallyBij
ective (Type w)] [HasSheafify J (Type w)] {X Y : Cᵒᵖ ⥤ A} (f : X ⟶ Y) (hf : fora
ll (…
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfSize`：∀ [UnivLE.{v, u}], Catego
ryTheory.Limits.HasColimitsOfSize.{w, v, u, u + 1} (Type u)
· 使用定理 `CategoryTheory.Limits.PreservesColimits.preservesFilteredColimits`：∀ {C 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : C
ategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Types.instPreservesColimitsOfSizeForgetTypeFun`：CategoryT
heory.Limits.PreservesColimitsOfSize.{u_1, u_2, u, u, u + 1, u + 1} (CategoryThe
ory.forget (Type u))
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Limits.Sigma.ι_desc`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {β : Type w} {f : β → C}   [inst_1 : CategoryTheory.Limits.
HasCoproduct f] {P : C} …
-/
lemma jointly_reflect_ofArrows_mem
    [HasSheafify J (Type w)] [J.WEqualsLocallyBijective (Type w)]
    (hP : P.IsConservativeFamilyOfPoints)
    {X : C} {ι : Type*} [Small.{w} ι] {U : ι → C} (f : ∀ i, U i ⟶ X) :
    Sieve.ofArrows _ f ∈ J X ↔
      ∀ (Φ : P.FullSubcategory) (x : Φ.obj.fiber.obj X),
        ∃ (i : ι) (y : Φ.obj.fiber.obj (U i)), Φ.obj.fiber.map (f i) y = x := by
  refine ⟨fun hf Φ x ↦ ?_, fun hf ↦ ?_⟩
  · obtain ⟨Z, _, ⟨_, p, _, ⟨i⟩, rfl⟩, z, rfl⟩ := Φ.obj.jointly_surjective _ hf x
    exact ⟨i, Φ.obj.fiber.map p z, by simp⟩
  · rw [J.ofArrows_mem_iff_isLocallySurjective_sigmaDesc_shrinkYoneda_map]
    refine hP.jointly_reflect_isLocallySurjective _ (fun Φ x ↦ ?_)
    obtain ⟨x, rfl⟩ := (Φ.obj.shrinkYonedaCompPresheafFiberIso.app X).toEquiv.symm.surjective x
    obtain ⟨i, y, rfl⟩ := hf Φ x
    refine ⟨Φ.obj.presheafFiber.map (Sigma.ι (fun i ↦ shrinkYoneda.{w}.obj (U i)) i)
      (Φ.obj.shrinkYonedaCompPresheafFiberIso.inv.app _ y), ?_⟩
    have := ConcreteCategory.congr_hom
      (Φ.obj.shrinkYonedaCompPresheafFiberIso.inv.naturality (f i)) y
    dsimp at this ⊢
    rw [this, ← Sigma.ι_desc (fun i ↦ shrinkYoneda.{w}.map (f i)) i, Functor.map_comp]
    rfl
/-
**CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.jointly_reflect_ofA
rrows_mem_of_small** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.IsCo
nservativeFamilyOfPoints`。
形式化陈述：jointly_reflect_ofArrows_mem_of_small [HasSheafify J (Type w)] [J.WEqualsL
ocallyBijective (Type w)] (hP : P.IsConservativeFamilyOfPoints) [ObjectProperty.
Small.{w} P] {X : C} {ι : Type*} {U : ι -> C} (f : forall i, U i ⟶ X) : Sieve.of
Arrows _ f in J X ↔ forall (Φ : P.FullSubcategory) (x : Φ.obj.fiber.obj X), exis
ts (i : ι) (y : Φ.obj.fiber.obj (U i)), Φ.obj.fiber.map (f i) y = x
参数：Type w；Type w；hP : P.IsConservativeFamilyOfPoints；f : forall i, U i ⟶ X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.jointly_surjective`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckT
opology C} (self : J.Point)   {X : C},   ∀ R ∈ J X…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `CategoryTheory.GrothendieckTopology.superset_covering`：superset_covering
 (Hss : S <= R) (sjx : S in J X) : R in J X
· 使用定理 `CategoryTheory.Sieve.generate_le_iff`：generate_le_iff (R : Presieve X) (
S : Sieve X) : generate R <= S ↔ R <= S
· 使用引理 `CategoryTheory.Presieve.ofArrows_le_iff`：ofArrows_le_iff {X : C} {ι : Ty
pe*} {Y : ι -> C} {f : forall i, Y i ⟶ X} {R : Presieve X} : Presieve.ofArrows Y
 f <= R ↔ forall i, R (f i)
· 使用引理 `CategoryTheory.Sieve.ofArrows_mk`：ofArrows_mk (i : I) : ofArrows Y f (f 
i)
· 使用引理 `CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.jointly_refle
ct_ofArrows_mem`：jointly_reflect_ofArrows_mem [HasSheafify J (Type w)] [J.WEqual
sLocallyBijective (Type w)] (hP : P.IsConservativeFamilyOfPoints) {X : C} {ι …
· 使用定理 `CategoryTheory.ObjectProperty.instSmallFullSubcategoryOfSmall`：∀ {C : Ty
pe u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.ObjectProper
ty C)   [CategoryTheory.ObjectProperty.Small.{w, v,…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma jointly_reflect_ofArrows_mem_of_small
    [HasSheafify J (Type w)] [J.WEqualsLocallyBijective (Type w)]
    (hP : P.IsConservativeFamilyOfPoints) [ObjectProperty.Small.{w} P]
    {X : C} {ι : Type*} {U : ι → C} (f : ∀ i, U i ⟶ X) :
    Sieve.ofArrows _ f ∈ J X ↔
      ∀ (Φ : P.FullSubcategory) (x : Φ.obj.fiber.obj X),
        ∃ (i : ι) (y : Φ.obj.fiber.obj (U i)), Φ.obj.fiber.map (f i) y = x := by
  refine ⟨fun hf Φ x ↦ ?_, fun hf ↦ ?_⟩
  · obtain ⟨Z, _, ⟨_, p, _, ⟨i⟩, rfl⟩, z, rfl⟩ := Φ.obj.jointly_surjective _ hf x
    exact ⟨i, Φ.obj.fiber.map p z, by simp⟩
  · let ι' : Type _ := Σ (Φ : P.FullSubcategory), Φ.obj.fiber.obj X
    choose i y hy using fun (j : ι') ↦ hf j.1 j.2
    refine J.superset_covering (S := Sieve.ofArrows _ (fun i' ↦ f (i i'))) ?_ ?_
    · rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
      exact fun _ ↦ Sieve.ofArrows_mk _ _ _
    · rw [hP.jointly_reflect_ofArrows_mem]
      exact fun Φ x ↦ ⟨_, _, hy ⟨Φ, x⟩⟩

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.mk'.isLocallySurjec
tive** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty.IsConservativeFami
lyOfPoints`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma mk'.isLocallySurjective
    (hP : ∀ ⦃X : C⦄ (S : Sieve X) (_ : ∀ (Φ : P.FullSubcategory) (x : Φ.obj.fiber.obj X),
      ∃ (Y : C) (g : Y ⟶ X) (_ : S g) (y : Φ.obj.fiber.obj Y), Φ.obj.fiber.map g y = x),
        S ∈ J X)
    {F₁ F₂ : Cᵒᵖ ⥤ Type w} (f : F₁ ⟶ F₂) [Mono f]
    (hf : ∀ (Φ : P.FullSubcategory), Function.Surjective (Φ.obj.presheafFiber.map f)) :
    Presheaf.IsLocallySurjective J f := by
  wlog hF₂ : ∃ (U : C), F₂ = shrinkYoneda.obj U generalizing F₁ F₂
  · refine ⟨fun {U} s ↦ ?_⟩
    let f' := pullback.snd f (shrinkYonedaEquiv.{w}.symm s)
    have hf' (Φ : P.FullSubcategory) :
        Function.Surjective (Φ.obj.presheafFiber.map f') := by
      replace hf := hf Φ
      rw [← CategoryTheory.epi_iff_surjective] at hf ⊢
      exact (MorphismProperty.epimorphisms _).of_isPullback
        ((IsPullback.of_hasPullback f (shrinkYonedaEquiv.{w}.symm s)).map
          Φ.obj.presheafFiber) (.infer_property _)
    have := this f' hf' ⟨_, rfl⟩
    refine J.superset_covering ?_
      (Presheaf.imageSieve_mem J f' (shrinkYonedaObjObjEquiv.symm (𝟙 U)))
    rintro V g ⟨v, hv⟩
    refine ⟨(pullback.fst f (shrinkYonedaEquiv.{w}.symm s)).app _ v, ?_⟩
    refine (ConcreteCategory.congr_hom (NatTrans.congr_app
      (pullback.condition (f := f)) (op V)) _).trans ?_
    dsimp at hv ⊢
    refine (congr_arg _ hv).trans ?_
    refine (congr_arg _ (shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm g.op (𝟙 _))).trans ?_
    simpa using shrinkYonedaEquiv_symm_app_shrinkYonedaObjObjEquiv_symm s g
  obtain ⟨U, rfl⟩ := hF₂
  suffices Presheaf.imageSieve f (shrinkYonedaObjObjEquiv.symm (𝟙 U)) ∈ J U from ⟨by
    intro V g
    obtain ⟨g, rfl⟩ := shrinkYonedaObjObjEquiv.symm.surjective g
    replace this := J.pullback_stable g this
    rw [Presheaf.pullback_imageSieve] at this
    have hg := shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm g.op (𝟙 _)
    simp only [Quiver.Hom.unop_op, Category.comp_id] at hg
    simpa [← hg]⟩
  refine hP _ (fun Φ u ↦ ?_)
  obtain ⟨x₁, hx₁⟩ := hf Φ (Φ.obj.shrinkYonedaCompPresheafFiberIso.inv.app _ u)
  obtain ⟨V, v, y, rfl⟩ := Φ.obj.toPresheafFiber_jointly_surjective (A := Type w) x₁
  obtain ⟨t, ht⟩ := shrinkYonedaObjObjEquiv.symm.surjective (f.app _ y)
  refine ⟨V, t, ⟨y, ht.symm.trans ?_⟩, v, ?_⟩
  · simpa using (shrinkYoneda_obj_map_shrinkYonedaObjObjEquiv_symm t.op (𝟙 _)).symm
  · refine (Φ.obj.shrinkYonedaCompPresheafFiberIso.symm.app U).toEquiv.injective ?_
    dsimp [-Functor.comp_obj]
    trans (Φ.obj.toPresheafFiber V v (shrinkYoneda.{w}.obj U)) (shrinkYonedaObjObjEquiv.symm t)
    · rw [← Φ.obj.presheafFiber_map_shrinkYoneda_map_shrinkYonedaCompPresheafFiberIso_inv_app]
      exact Φ.obj.shrinkYonedaCompPresheafFiberIso.inv.naturality_apply t v
    · rw [← hx₁]
      refine Eq.trans (congr_arg _ ht)
        (Φ.obj.toPresheafFiber_naturality_apply f _ v y).symm

/- Let `P` be family of points of a site `(C, J)`, we show that `P` is a conservative
family of points if the following condition is satisfied (SGA 4 IV 6.5 (a)):
for any sieve `S : Sieve X`, if the family of maps `Φ.map.fiber.map f`
for all morphisms `f` in the sieve `S` is jointly surjective for any `Φ` in `P`,
then `S` is a covering sieve for `J`. -/
/-
**CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints.mk'** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints`。
形式化陈述：mk' [HasSheafify J (Type w)] (hP : forall ⦃X : C⦄ (S : Sieve X) (_ : foral
l (Φ : P.FullSubcategory) (x : Φ.obj.fiber.obj X), exists (Y : C) (g : Y ⟶ X) (_
 : S g) (y : Φ.obj.fiber.obj Y), Φ.obj.fiber.map g y = x), S in J X) : P.IsConse
rvativeFamilyOfPoints where jointlyReflectIsomorphisms_type
参数：Type w；hP : forall ⦃X : C⦄ (S : Sieve X) (_ : forall (Φ : P.FullSubcategory) 
(x : Φ.obj.fiber.obj X), exists (Y : C) (g : Y ⟶ X) (_ : S g) (y : Φ.obj.fiber.o
bj Y), Φ.obj.fiber.map g y = x), S in J X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.JointlyFaithful.jointlyReflectsIsomorphisms`：jointlyRefle
ctsIsomorphisms [Balanced C] (h : JointlyFaithful F) : JointlyReflectIsomorphism
s F where isIso f _
· 使用定理 `CategoryTheory.Limits.Types.hasColimitsOfSize`：∀ [UnivLE.{v, u}], Catego
ryTheory.Limits.HasColimitsOfSize.{w, v, u, u + 1} (Type u)
· 使用定理 `CategoryTheory.SheafOfTypes.balanced`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopology C}   [CategoryTh
eory.HasSheafify J (Type w…
· 使用定理 `CategoryTheory.JointlyFaithful.of_jointly_reflects_isIso_of_mono`：∀ {C :
 Type u_1} [inst : CategoryTheory.Category.{u_4, u_1} C] {I : Type u_2} {D : I →
 Type u_3}   [inst_1 : (i : I) → CategoryTheory.Catego…
· 使用定理 `CategoryTheory.Sheaf.instHasLimitsOfShape`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopology C} {D : Typ
e w}   [inst_1 : CategoryTheory…
· 使用定理 `CategoryTheory.Limits.Types.hasLimitsOfShape`：∀ {J : Type v} [inst : Cat
egoryTheory.Category.{w, v} J] [Small.{u, v} J],   CategoryTheory.Limits.HasLimi
tsOfShape J (Type u)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `CategoryTheory.Limits.PreservesFiniteLimits.preservesFiniteLimits`：∀ {C 
: Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : C
ategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.GrothendieckTopology.Point.instPreservesFiniteLimitsSheaf
SheafFiberOfLocallySmallOfHasFiniteLimitsOfAB5OfSize`：∀ {C : Type u} [inst : Cat
egoryTheory.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopology C} (Φ : 
J.Point)   {A : Type u'} [inst_1 :…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasCountableLimits`：∀ (C : Type
 u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Limits.HasCo
untableLimits C],   CategoryTheory.Limits.HasFini…
· 使用定理 `CategoryTheory.Limits.hasCountableLimits_of_hasLimits`：∀ (C : Type u_1) 
[inst : CategoryTheory.Category.{v_1, u_1} C] [CategoryTheory.Limits.HasLimits C
],   CategoryTheory.Limits.HasCountableLimi…
· 使用定理 `CategoryTheory.Limits.Types.hasLimitsOfSize`：∀ [UnivLE.{v, u}], Category
Theory.Limits.HasLimitsOfSize.{w, v, u, u + 1} (Type u)
· 使用定理 `CategoryTheory.Limits.instAB5Type`：CategoryTheory.AB5 (Type v)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Sheaf.isLocallySurjective_iff_epi`：isLocallySurjective_if
f_epi {F G : Sheaf J (Type w)} (φ : F ⟶ G) [HasSheafify J (Type w)] : IsLocallyS
urjective φ ↔ Epi φ
· 使用定理 `_private.Mathlib.CategoryTheory.Sites.Point.Conservative.0.CategoryTheor
y.ObjectProperty.IsConservativeFamilyOfPoints.mk'.isLocallySurjective`：∀ {C : Ty
pe u} [inst : CategoryTheory.Category.{v, u} C] {J : CategoryTheory.Grothendieck
Topology C}   {P : CategoryTheory.ObjectProperty J.…
· 使用定理 `CategoryTheory.instMonoFunctorOppositeHomFullSubcategoryIsSheafOfHasWeak
SheafifyOfSheaf`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (J 
: CategoryTheory.GrothendieckTopology C) (A : Type u₂)   [inst_1 : CategoryTh…
· 使用定理 `CategoryTheory.instHasWeakSheafifyOfHasSheafify`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C)
 (A : Type u₂)   [inst_1 : CategoryTh…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.isIso_iff_bijective`：isIso_iff_bijective {X Y : Type u} (
f : X ⟶ Y) : IsIso f ↔ Function.Bijective f
· 使用定理 `CategoryTheory.Balanced.isIso_of_mono_of_epi`：∀ {C : Type u} {inst : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.Balanced C] {X Y : C} (f :
 X ⟶ Y)   [CategoryTheory.Mono f] …

--- 原说明 ---
Let `P` be family of points of a site `(C, J)`, we show that `P` is a conservati
ve
family of points if the following condition is satisfied (SGA 4 IV 6.5 (a)):
for any sieve `S : Sieve X`, if the family of maps `Φ.map.fiber.map f`
for all morphisms `f` in the sieve `S` is jointly surjective for any `Φ` in `P`,
then `S` is a covering sieve for `J`.
-/
lemma mk' [HasSheafify J (Type w)]
    (hP : ∀ ⦃X : C⦄ (S : Sieve X) (_ : ∀ (Φ : P.FullSubcategory) (x : Φ.obj.fiber.obj X),
      ∃ (Y : C) (g : Y ⟶ X) (_ : S g) (y : Φ.obj.fiber.obj Y), Φ.obj.fiber.map g y = x),
        S ∈ J X) :
    P.IsConservativeFamilyOfPoints where
  jointlyReflectIsomorphisms_type :=
    JointlyFaithful.jointlyReflectsIsomorphisms
      (JointlyFaithful.of_jointly_reflects_isIso_of_mono (fun _ _ f _ hf ↦ by
        have : Epi f := by
          rw [← Sheaf.isLocallySurjective_iff_epi]
          exact mk'.isLocallySurjective hP _
            (fun Φ ↦ ((isIso_iff_bijective _).1 (hf Φ)).2)
        exact Balanced.isIso_of_mono_of_epi f))

end IsConservativeFamilyOfPoints

end ObjectProperty

namespace GrothendieckTopology

/-- A site has enough points (relatively to a universe `w`)
if it has a `w`-small conservative family of points. -/
/-
**CategoryTheory.GrothendieckTopology.HasEnoughPoints** 是 Mathlib 中的一个归纳类型，位于命名空
间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → CategoryTheory.
GrothendieckTopology C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A site has enough points (relatively to a universe `w`)
if it has a `w`-small conservative family of points.
-/
class HasEnoughPoints (J : GrothendieckTopology C) : Prop where
  exists_objectProperty (J) :
    ∃ (P : ObjectProperty (Point.{w} J)),
      ObjectProperty.Small.{w} P ∧ P.IsConservativeFamilyOfPoints

end GrothendieckTopology

end CategoryTheory

