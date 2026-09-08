/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!
# (Co)limits in subcategories of comma categories defined by morphism properties

-/

@[expose] public section

namespace CategoryTheory

open Limits MorphismProperty.Comma

variable {T : Type*} [Category* T] (P : MorphismProperty T)

namespace MorphismProperty.Comma

variable {A B J : Type*} [Category* A] [Category* B] [Category* J] {L : A ⥤ T} {R : B ⥤ T}
variable (D : J ⥤ P.Comma L R ⊤ ⊤)

/-- If `P` is closed under limits of shape `J` in `Comma L R`, then when `D` has
a limit in `Comma L R`, the forgetful functor creates this limit. -/
@[instance_reducible]
/-
**CategoryTheory.MorphismProperty.Comma.forgetCreatesLimitOfClosed** 是 Mathlib 中
的一个定义，位于命名空间 `CategoryTheory.MorphismProperty.Comma`。
形式化陈述：forgetCreatesLimitOfClosed [(P.commaObj L R).IsClosedUnderLimitsOfShape J]
 [HasLimit (D ⋙ forget L R P ⊤ ⊤)] : CreatesLimit D (forget L R P ⊤ ⊤)
参数：P.commaObj L R；D ⋙ forget L R P ⊤ ⊤。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `CategoryTheory.MorphismProperty.Comma.instFullTopCommaForget`：∀ {A : Typ
e u_1} [inst : CategoryTheory.Category.{v_1, u_1} A] {B : Type u_2}   [inst_1 : 
CategoryTheory.Category.{v_2, u_2} B] {T : Type u_…

--- 原说明 ---
If `P` is closed under limits of shape `J` in `Comma L R`, then when `D` has
a limit in `Comma L R`, the forgetful functor creates this limit.
-/
noncomputable def forgetCreatesLimitOfClosed
    [(P.commaObj L R).IsClosedUnderLimitsOfShape J]
    [HasLimit (D ⋙ forget L R P ⊤ ⊤)] :
    CreatesLimit D (forget L R P ⊤ ⊤) :=
  createsLimitOfFullyFaithfulOfIso
    (⟨limit (D ⋙ forget L R P ⊤ ⊤),
      ObjectProperty.prop_limit (P.commaObj L R) _
        fun j ↦ (D.obj j).prop⟩) (Iso.refl _)

/-- If `Comma L R` has limits of shape `J` and `Comma L R` is closed under limits of shape
`J`, then `forget L R P ⊤ ⊤` creates limits of shape `J`. -/
@[instance_reducible]
/-
**CategoryTheory.MorphismProperty.Comma.forgetCreatesLimitsOfShapeOfClosed** 是 M
athlib 中的一个定义，位于命名空间 `CategoryTheory.MorphismProperty.Comma`。
形式化陈述：forgetCreatesLimitsOfShapeOfClosed [HasLimitsOfShape J (Comma L R)] [Objec
tProperty.IsClosedUnderLimitsOfShape (P.commaObj L R) J] : CreatesLimitsOfShape 
J (forget L R P ⊤ ⊤) where CreatesLimit
参数：Comma L R；P.commaObj L R。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative

--- 原说明 ---
If `Comma L R` has limits of shape `J` and `Comma L R` is closed under limits of
 shape
`J`, then `forget L R P ⊤ ⊤` creates limits of shape `J`.
-/
noncomputable def forgetCreatesLimitsOfShapeOfClosed [HasLimitsOfShape J (Comma L R)]
    [ObjectProperty.IsClosedUnderLimitsOfShape (P.commaObj L R) J] :
    CreatesLimitsOfShape J (forget L R P ⊤ ⊤) where
  CreatesLimit := forgetCreatesLimitOfClosed _ _
/-
**CategoryTheory.MorphismProperty.Comma.hasLimit_of_closedUnderLimitsOfShape** 是
 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty.Comma`。
形式化陈述：hasLimit_of_closedUnderLimitsOfShape [(P.commaObj L R).IsClosedUnderLimits
OfShape J] [HasLimit (D ⋙ forget L R P ⊤ ⊤)] : HasLimit D
参数：P.commaObj L R；D ⋙ forget L R P ⊤ ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `CategoryTheory.hasLimit_of_created`：hasLimit_of_created (K : J ⥤ C) (F :
 C ⥤ D) [HasLimit (K ⋙ F)] [CreatesLimit K F] : HasLimit K
-/
lemma hasLimit_of_closedUnderLimitsOfShape
    [(P.commaObj L R).IsClosedUnderLimitsOfShape J]
    [HasLimit (D ⋙ forget L R P ⊤ ⊤)] :
    HasLimit D :=
  haveI : CreatesLimit D (forget L R P ⊤ ⊤) := forgetCreatesLimitOfClosed _ D
  hasLimit_of_created D (forget L R P ⊤ ⊤)
/-
**CategoryTheory.MorphismProperty.Comma.hasLimitsOfShape_of_closedUnderLimitsOfS
hape** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.MorphismProperty.Comma`。
形式化陈述：hasLimitsOfShape_of_closedUnderLimitsOfShape [HasLimitsOfShape J (Comma L 
R)] [(P.commaObj L R).IsClosedUnderLimitsOfShape J] : HasLimitsOfShape J (P.Comm
a L R ⊤ ⊤) where has_limit _
参数：Comma L R；P.commaObj L R。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用引理 `CategoryTheory.MorphismProperty.Comma.hasLimit_of_closedUnderLimitsOfSha
pe`：hasLimit_of_closedUnderLimitsOfShape [(P.commaObj L R).IsClosedUnderLimitsOf
Shape J] [HasLimit (D ⋙ forget L R P ⊤ ⊤)] : HasLimit D
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
instance hasLimitsOfShape_of_closedUnderLimitsOfShape [HasLimitsOfShape J (Comma L R)]
    [(P.commaObj L R).IsClosedUnderLimitsOfShape J] :
    HasLimitsOfShape J (P.Comma L R ⊤ ⊤) where
  has_limit _ := hasLimit_of_closedUnderLimitsOfShape _ _

/-- If `P` is closed under colimits of shape `J` in `Comma L R`, then when `D` has
a colimit in `Comma L R`, the forgetful functor creates this colimit. -/
@[instance_reducible]
/-
**CategoryTheory.MorphismProperty.Comma.forgetCreatesColimitOfClosed** 是 Mathlib
 中的一个定义，位于命名空间 `CategoryTheory.MorphismProperty.Comma`。
形式化陈述：forgetCreatesColimitOfClosed [(P.commaObj L R).IsClosedUnderColimitsOfShap
e J] [HasColimit (D ⋙ forget L R P ⊤ ⊤)] : CreatesColimit D (forget L R P ⊤ ⊤)
参数：P.commaObj L R；D ⋙ forget L R P ⊤ ⊤。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `CategoryTheory.MorphismProperty.Comma.instFullTopCommaForget`：∀ {A : Typ
e u_1} [inst : CategoryTheory.Category.{v_1, u_1} A] {B : Type u_2}   [inst_1 : 
CategoryTheory.Category.{v_2, u_2} B] {T : Type u_…

--- 原说明 ---
If `P` is closed under colimits of shape `J` in `Comma L R`, then when `D` has
a colimit in `Comma L R`, the forgetful functor creates this colimit.
-/
noncomputable def forgetCreatesColimitOfClosed
    [(P.commaObj L R).IsClosedUnderColimitsOfShape J]
    [HasColimit (D ⋙ forget L R P ⊤ ⊤)] :
    CreatesColimit D (forget L R P ⊤ ⊤) :=
  createsColimitOfFullyFaithfulOfIso
    (⟨colimit (D ⋙ forget L R P ⊤ ⊤),
      (P.commaObj L R).prop_colimit _ (fun j ↦ (D.obj j).prop)⟩) (Iso.refl _)

variable (J) in
/-- If `Comma L R` has colimits of shape `J` and `Comma L R` is closed under colimits of shape
`J`, then `forget L R P ⊤ ⊤` creates colimits of shape `J`. -/
@[instance_reducible]
/-
**CategoryTheory.MorphismProperty.Comma.forgetCreatesColimitsOfShapeOfClosed** 是
 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.MorphismProperty.Comma`。
形式化陈述：forgetCreatesColimitsOfShapeOfClosed [HasColimitsOfShape J (Comma L R)] [(
P.commaObj L R).IsClosedUnderColimitsOfShape J] : CreatesColimitsOfShape J (forg
et L R P ⊤ ⊤) where CreatesColimit
参数：Comma L R；P.commaObj L R。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative

--- 原说明 ---
If `Comma L R` has colimits of shape `J` and `Comma L R` is closed under colimit
s of shape
`J`, then `forget L R P ⊤ ⊤` creates colimits of shape `J`.
-/
noncomputable def forgetCreatesColimitsOfShapeOfClosed [HasColimitsOfShape J (Comma L R)]
    [(P.commaObj L R).IsClosedUnderColimitsOfShape J] :
    CreatesColimitsOfShape J (forget L R P ⊤ ⊤) where
  CreatesColimit := forgetCreatesColimitOfClosed _ _
/-
**CategoryTheory.MorphismProperty.Comma.hasColimit_of_closedUnderColimitsOfShape
** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.MorphismProperty.Comma`。
形式化陈述：hasColimit_of_closedUnderColimitsOfShape [(P.commaObj L R).IsClosedUnderCo
limitsOfShape J] [HasColimit (D ⋙ forget L R P ⊤ ⊤)] : HasColimit D
参数：P.commaObj L R；D ⋙ forget L R P ⊤ ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `CategoryTheory.hasColimit_of_created`：hasColimit_of_created (K : J ⥤ C) 
(F : C ⥤ D) [HasColimit (K ⋙ F)] [CreatesColimit K F] : HasColimit K
-/
lemma hasColimit_of_closedUnderColimitsOfShape
    [(P.commaObj L R).IsClosedUnderColimitsOfShape J]
    [HasColimit (D ⋙ forget L R P ⊤ ⊤)] :
    HasColimit D :=
  haveI : CreatesColimit D (forget L R P ⊤ ⊤) := forgetCreatesColimitOfClosed _ D
  hasColimit_of_created D (forget L R P ⊤ ⊤)
/-
**CategoryTheory.MorphismProperty.Comma.hasColimitsOfShape_of_closedUnderColimit
sOfShape** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.MorphismProperty.Comma`。
形式化陈述：hasColimitsOfShape_of_closedUnderColimitsOfShape [HasColimitsOfShape J (Co
mma L R)] [(P.commaObj L R).IsClosedUnderColimitsOfShape J] : HasColimitsOfShape
 J (P.Comma L R ⊤ ⊤) where has_colimit _
参数：Comma L R；P.commaObj L R。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用引理 `CategoryTheory.MorphismProperty.Comma.hasColimit_of_closedUnderColimitsO
fShape`：hasColimit_of_closedUnderColimitsOfShape [(P.commaObj L R).IsClosedUnder
ColimitsOfShape J] [HasColimit (D ⋙ forget L R P ⊤ ⊤)] : HasColimit …
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
-/
instance hasColimitsOfShape_of_closedUnderColimitsOfShape [HasColimitsOfShape J (Comma L R)]
    [(P.commaObj L R).IsClosedUnderColimitsOfShape J] :
    HasColimitsOfShape J (P.Comma L R ⊤ ⊤) where
  has_colimit _ := hasColimit_of_closedUnderColimitsOfShape _ _

end MorphismProperty.Comma

section CostructuredArrow

variable {A : Type*} [Category* A] {L : A ⥤ T}

/-
**CategoryTheory.CostructuredArrow.closedUnderLimitsOfShape_discrete_empty** 是 M
athlib 中的一个定理，位于命名空间 `CategoryTheory.CostructuredArrow`。
形式化陈述：∀ {T : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] (P : Catego
ryTheory.MorphismProperty T) {A : Type u_2}   [inst_1 : CategoryTheory.Category.
{v_2, u_2} A] {L : CategoryTheory.Functor A T} [L.Faithful] [L.Full] {Y : A}   [
P.ContainsIdentities] [P.RespectsIso],   (CategoryTheory.MorphismProperty.costru
cturedArrowObj L P).IsClosedUnderLimitsOfShape     (CategoryTheory.Discrete PEmp
ty.{1})
参数：P : CategoryTheory.MorphismProperty T；CategoryTheory.MorphismProperty.costruc
turedArrowObj L P；CategoryTheory.Discrete PEmpty.{1}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `CategoryTheory.ObjectProperty.limitsOfShape_isEmpty_iff`：limitsOfShape_i
sEmpty_iff [IsEmpty J] (X : C) : P.limitsOfShape J X ↔ Nonempty (IsTerminal X)
· 使用定理 `CategoryTheory.instIsEmptyDiscrete`：∀ (α : Type u_1) [IsEmpty α], IsEmpt
y (CategoryTheory.Discrete α)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.MorphismProperty.costructuredArrow_iso_iff`：costructuredA
rrow_iso_iff (P : MorphismProperty T) [P.RespectsIso] {L : A ⥤ T} {X : T} {f g :
 CostructuredArrow L X} (e : f ≅ g) : P f.hom ↔…
· 使用引理 `CategoryTheory.MorphismProperty.id_mem`：id_mem (W : MorphismProperty C) 
[W.ContainsIdentities] (X : C) : W (𝟙 X)
-/
instance CostructuredArrow.closedUnderLimitsOfShape_discrete_empty [L.Faithful] [L.Full] {Y : A}
    [P.ContainsIdentities] [P.RespectsIso] :
    (P.costructuredArrowObj L (X := L.obj Y)).IsClosedUnderLimitsOfShape (Discrete PEmpty.{1}) where
  limitsOfShape_le := by
    rintro X p
    let t : IsTerminal X := (ObjectProperty.limitsOfShape_isEmpty_iff _ _ _ |>.mp p).some
    let e : X ≅ CostructuredArrow.mk (𝟙 (L.obj Y)) := t.uniqueUpToIso CostructuredArrow.mkIdTerminal
    simpa [MorphismProperty.costructuredArrowObj_iff,
      P.costructuredArrow_iso_iff e] using P.id_mem (L.obj Y)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.CostructuredArrow.isClosedUnderColimitsOfShape** 是 Mathlib 中的一个
定理，位于命名空间 `CategoryTheory.CostructuredArrow`。
形式化陈述：∀ {T : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] {A : Type u
_2}   [inst_1 : CategoryTheory.Category.{v_2, u_2} A] {L : CategoryTheory.Functo
r A T} {J : Type u_3}   [inst_2 : CategoryTheory.Category.{v_3, u_3} J] {P : Cat
egoryTheory.MorphismProperty T} [P.RespectsIso]   [CategoryTheory.Limits.Preserv
esColimitsOfShape J L] [CategoryTheory.Limits.HasColimitsOfShape J A]   (c : (D 
: CategoryTheory.Functor J T) → [CategoryTheory.Limits.HasColimit D] → CategoryT
heory.Limits.Cocone D)   (hc :     (D : CategoryTheory.Functor J T) →       [ins
t_6 : CategoryTheory.Limits.HasColimit D] → CategoryTheory.Limits.IsColimit (c D
)),   (∀ (D : CategoryTheory.Functor J T) [inst_6 : CategoryTheory.Limits.HasCol
imit D] {X : T}       (s : D ⟶ (CategoryTheory.Functor.const J).obj X),       (∀
 (j : J), P (s.app j)) → P ((hc D).desc { pt := X, ι := s })) →     ∀ (X : T), (
CategoryTheory.MorphismProperty.costructuredArrowObj L P).IsClosedUnderColimitsO
fShape J
参数：c : (D : CategoryTheory.Functor J T) → [CategoryTheory.Limits.HasColimit D] →
 CategoryTheory.Limits.Cocone D；hc :     (D : CategoryTheory.Functor J T) →     
  [inst_6 : CategoryTheory.Limits.HasColimit D] → CategoryTheory.Limits.IsColimi
t (c D)；∀ (D : CategoryTheory.Functor J T) [inst_6 : CategoryTheory.Limits.HasCo
limit D] {X : T}       (s : D ⟶ (CategoryTheory.Functor.const J).obj X),       (
∀ (j : J), P (s.app j)) → P ((hc D).desc { pt := X, ι := s })；X : T；CategoryTheo
ry.MorphismProperty.costructuredArrowObj L P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.preservesColimit_of_createsColimit_and_hasColimit`：∀ {C :
 Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.CommaMorphism.w`：∀ {A : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} A] {B : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} B] 
  {T : Type u₃} [ins…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.IsColimit.hom_ext`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.IsColimit.fac`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} C]   {F : CategoryTheor…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MorphismProperty.costructuredArrowObj_iff`：∀ {A : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} A] {T : Type u_3}   [inst_1 : Cate
goryTheory.Category.{v_3, u_3} T] (L : Categor…
· 使用定理 `CategoryTheory.Limits.instHasColimitCompOfPreservesColimit`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.comp_preservesColimitsOfShape`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.preservesColimitOfShape_of_createsColimitsOfShape_and_has
ColimitsOfShape`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D 
: Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.IsColimit.coconePointUniqueUpToIso_hom_desc`：∀ {J 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : C
ategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.MorphismProperty.cancel_left_of_respectsIso`：cancel_left_
of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C} (f : X 
⟶ Y) (g : Y ⟶ Z) [IsIso f] : P (f ≫ g) ↔ P g
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.ObjectProperty.ColimitOfShape.prop_diag_obj`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P : CategoryTheory.ObjectPro
perty C} {J : Type u'}   [inst_1 : CategoryTheor…
-/
lemma CostructuredArrow.isClosedUnderColimitsOfShape {J : Type*} [Category* J]
    {P : MorphismProperty T} [P.RespectsIso] [PreservesColimitsOfShape J L] [HasColimitsOfShape J A]
    (c : ∀ (D : J ⥤ T) [HasColimit D], Cocone D)
    (hc : ∀ (D : J ⥤ T) [HasColimit D], IsColimit (c D))
    (H : ∀ (D : J ⥤ T) [HasColimit D] {X : T} (s : D ⟶ (Functor.const J).obj X),
      (∀ j, P (s.app j)) → P ((hc D).desc (Cocone.mk X s))) (X : T) :
    (P.costructuredArrowObj L (X := X)).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le Y := by
    intro ⟨d⟩
    let hd : IsColimit ((CategoryTheory.CostructuredArrow.proj L X ⋙ L).mapCocone d.cocone) :=
      isColimitOfPreserves _ d.isColimit
    have heq : Y.hom = hd.desc { pt := X, ι := { app j := (d.diag.obj j).hom } } := by
      refine hd.hom_ext fun j ↦ ?_
      simp only [IsColimit.fac]
      simp
    rw [P.costructuredArrowObj_iff, heq, ← hd.coconePointUniqueUpToIso_hom_desc (hc _),
      P.cancel_left_of_respectsIso]
    exact H _ _ d.prop_diag_obj

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.CostructuredArrow.closedUnderLimitsOfShape_walkingCospan** 是 Ma
thlib 中的一个定理，位于命名空间 `CategoryTheory.CostructuredArrow`。
形式化陈述：∀ {T : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] (P : Catego
ryTheory.MorphismProperty T) {A : Type u_2}   [inst_1 : CategoryTheory.Category.
{v_2, u_2} A] {L : CategoryTheory.Functor A T}   [CategoryTheory.Limits.HasPullb
acks A] [CategoryTheory.Limits.HasPullbacks T]   [CategoryTheory.Limits.Preserve
sLimitsOfShape CategoryTheory.Limits.WalkingCospan L] (X : T)   [P.IsStableUnder
Composition] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P],   (Categor
yTheory.MorphismProperty.costructuredArrowObj L P).IsClosedUnderLimitsOfShape   
  CategoryTheory.Limits.WalkingCospan
参数：P : CategoryTheory.MorphismProperty T；X : T；CategoryTheory.MorphismProperty.c
ostructuredArrowObj L P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsPullback.of_isLimit_cone`：of_isLimit_cone {D : WalkingC
ospan ⥤ C} {c : Cone D} (hc : IsLimit c) : IsPullback (c.π.app .left) (c.π.app .
right) (D.map WalkingCospan.Hom…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.instPreservesLimitsOfShapeCostructuredArrowOverToOverOfIs
ConnectedOfHasLimitsOfShape`：∀ {J : Type u'} [inst : CategoryTheory.Category.{v'
, u'} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]   {D : Type u_
1} [inst_…
· 使用定理 `CategoryTheory.preservesLimit_of_createsLimit_and_hasLimit`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MorphismProperty.costructuredArrowObj_iff`：∀ {A : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} A] {T : Type u_3}   [inst_1 : Cate
goryTheory.Category.{v_3, u_3} T] (L : Categor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.CommaMorphism.w`：∀ {A : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} A] {B : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} B] 
  {T : Type u₃} [ins…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
· 使用定理 `CategoryTheory.MorphismProperty.of_isPullback`：∀ {C : Type u} {inst : Ca
tegoryTheory.Category.{v, u} C} {P : CategoryTheory.MorphismProperty C}   [self 
: P.IsStableUnderBaseChange] {X Y Y…
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
· 使用引理 `CategoryTheory.MorphismProperty.of_postcomp`：of_postcomp [W.HasOfPostcom
pProperty W'] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hg : W' g) (hfg : W (f ≫ g)) 
: W f
-/
lemma CostructuredArrow.closedUnderLimitsOfShape_walkingCospan [HasPullbacks A] [HasPullbacks T]
    [PreservesLimitsOfShape WalkingCospan L] (X : T)
    [P.IsStableUnderComposition] [P.IsStableUnderBaseChange]
    [P.HasOfPostcompProperty P] :
    (P.costructuredArrowObj L (X := X)).IsClosedUnderLimitsOfShape WalkingCospan where
  limitsOfShape_le := by
    rintro Y ⟨pres, hpres⟩
    have h : IsPullback (L.map (pres.π.app .left).left) (L.map (pres.π.app .right).left)
        (L.map (pres.diag.map WalkingCospan.Hom.inl).left)
          (L.map (pres.diag.map WalkingCospan.Hom.inr).left) :=
      IsPullback.of_isLimit_cone <| isLimitOfPreserves
        (CategoryTheory.CostructuredArrow.toOver L X ⋙ CategoryTheory.Over.forget X) pres.isLimit
    rw [MorphismProperty.costructuredArrowObj_iff]
    rw [show Y.hom = L.map (pres.π.app .left).left ≫ (pres.diag.obj .left).hom by simp]
    apply P.comp_mem _ _ (P.of_isPullback h.flip ?_) (hpres _)
    exact P.of_postcomp _ (pres.diag.obj WalkingCospan.one).hom (hpres .one)
      (by simpa using hpres .right)

namespace MorphismProperty.CostructuredArrow

variable (X : T) [P.IsStableUnderComposition] [P.IsStableUnderBaseChange]
  [P.HasOfPostcompProperty P] [HasPullbacks A] [HasPullbacks T]
  [PreservesLimitsOfShape WalkingCospan L]

/-
**CategoryTheory.MorphismProperty.CostructuredArrow.createsLimitsOfShape_walking
Cospan** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.MorphismProperty.CostructuredAr
row`。
形式化陈述：createsLimitsOfShape_walkingCospan : CreatesLimitsOfShape WalkingCospan (C
ostructuredArrow.forget P ⊤ L X)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CostructuredArrow.closedUnderLimitsOfShape_walkingCospan`
：∀ {T : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] (P : CategoryThe
ory.MorphismProperty T) {A : Type u_2}   [inst_1 : CategoryTh…
-/
noncomputable instance createsLimitsOfShape_walkingCospan :
    CreatesLimitsOfShape WalkingCospan (CostructuredArrow.forget P ⊤ L X) := by
  apply +allowSynthFailures forgetCreatesLimitsOfShapeOfClosed
  · exact inferInstanceAs (HasLimitsOfShape WalkingCospan (CostructuredArrow L X))
  · exact CostructuredArrow.closedUnderLimitsOfShape_walkingCospan _ _
/-
**CategoryTheory.MorphismProperty.CostructuredArrow.hasPullbacks** 是 Mathlib 中的一
个实例，位于命名空间 `CategoryTheory.MorphismProperty.CostructuredArrow`。
形式化陈述：hasPullbacks : HasPullbacks (P.CostructuredArrow ⊤ L X)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CostructuredArrow.closedUnderLimitsOfShape_walkingCospan`
：∀ {T : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] (P : CategoryThe
ory.MorphismProperty T) {A : Type u_2}   [inst_1 : CategoryTh…
-/
instance hasPullbacks : HasPullbacks (P.CostructuredArrow ⊤ L X) := by
  apply +allowSynthFailures hasLimitsOfShape_of_closedUnderLimitsOfShape
  · exact inferInstanceAs (HasLimitsOfShape WalkingCospan (CostructuredArrow L X))
  · exact CostructuredArrow.closedUnderLimitsOfShape_walkingCospan _ _
/-
**CategoryTheory.MorphismProperty.CostructuredArrow.** 是 Mathlib 中的一个实例，位于命名空间 `
CategoryTheory.MorphismProperty.CostructuredArrow`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PreservesLimitsOfShape WalkingCospan (CostructuredArrow.toOver P L X) :=
  have : PreservesLimitsOfShape WalkingCospan
      (CostructuredArrow.toOver P L X ⋙ Over.forget P ⊤ X) :=
    inferInstanceAs <| PreservesLimitsOfShape WalkingCospan <|
      CostructuredArrow.forget P ⊤ L X ⋙ CategoryTheory.CostructuredArrow.toOver L X
  preservesLimitsOfShape_of_reflects_of_preserves _ (Over.forget _ _ X)

end MorphismProperty.CostructuredArrow

end CostructuredArrow

section

variable {A : Type*} [Category* A] {L : A ⥤ T}

/-
**CategoryTheory.StructuredArrow.closedUnderColimitsOfShape_discrete_empty** 是 M
athlib 中的一个定理，位于命名空间 `CategoryTheory.StructuredArrow`。
形式化陈述：∀ {T : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] (P : Catego
ryTheory.MorphismProperty T) {A : Type u_2}   [inst_1 : CategoryTheory.Category.
{v_2, u_2} A] {L : CategoryTheory.Functor A T} [L.Faithful] [L.Full] {Y : A}   [
P.ContainsIdentities] [P.RespectsIso],   (CategoryTheory.MorphismProperty.struct
uredArrowObj L P).IsClosedUnderColimitsOfShape     (CategoryTheory.Discrete PEmp
ty.{1})
参数：P : CategoryTheory.MorphismProperty T；CategoryTheory.MorphismProperty.structu
redArrowObj L P；CategoryTheory.Discrete PEmpty.{1}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `CategoryTheory.ObjectProperty.colimitsOfShape_isEmpty_iff`：colimitsOfSha
pe_isEmpty_iff [IsEmpty J] (X : C) : P.colimitsOfShape J X ↔ Nonempty (IsInitial
 X)
· 使用定理 `CategoryTheory.instIsEmptyDiscrete`：∀ (α : Type u_1) [IsEmpty α], IsEmpt
y (CategoryTheory.Discrete α)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.MorphismProperty.structuredArrow_iso_iff`：structuredArrow
_iso_iff (P : MorphismProperty T) [P.RespectsIso] {L : A ⥤ T} {X : T} {f g : Str
ucturedArrow X L} (e : f ≅ g) : P f.hom ↔ P g…
· 使用引理 `CategoryTheory.MorphismProperty.id_mem`：id_mem (W : MorphismProperty C) 
[W.ContainsIdentities] (X : C) : W (𝟙 X)
-/
instance StructuredArrow.closedUnderColimitsOfShape_discrete_empty [L.Faithful] [L.Full] {Y : A}
    [P.ContainsIdentities] [P.RespectsIso] :
    (P.structuredArrowObj L (X := L.obj Y)).IsClosedUnderColimitsOfShape (Discrete PEmpty.{1}) where
  colimitsOfShape_le := by
    rintro X p
    let t : IsInitial X := (ObjectProperty.colimitsOfShape_isEmpty_iff _ _ _ |>.mp p).some
    let e : X ≅ StructuredArrow.mk (𝟙 (L.obj Y)) := t.uniqueUpToIso StructuredArrow.mkIdInitial
    simpa [MorphismProperty.structuredArrowObj_iff,
      P.structuredArrow_iso_iff e] using P.id_mem (L.obj Y)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.StructuredArrow.isClosedUnderLimitsOfShape** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.StructuredArrow`。
形式化陈述：∀ {T : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] {A : Type u
_2}   [inst_1 : CategoryTheory.Category.{v_2, u_2} A] {L : CategoryTheory.Functo
r A T} {J : Type u_3}   [inst_2 : CategoryTheory.Category.{v_3, u_3} J] {P : Cat
egoryTheory.MorphismProperty T} [P.RespectsIso]   [CategoryTheory.Limits.Preserv
esLimitsOfShape J L] [CategoryTheory.Limits.HasLimitsOfShape J A]   (c : (D : Ca
tegoryTheory.Functor J T) → [CategoryTheory.Limits.HasLimit D] → CategoryTheory.
Limits.Cone D)   (hc :     (D : CategoryTheory.Functor J T) →       [inst_6 : Ca
tegoryTheory.Limits.HasLimit D] → CategoryTheory.Limits.IsLimit (c D)),   (∀ (D 
: CategoryTheory.Functor J T) [inst_6 : CategoryTheory.Limits.HasLimit D] {X : T
}       (s : (CategoryTheory.Functor.const J).obj X ⟶ D),       (∀ (j : J), P (s
.app j)) → P ((hc D).lift { pt := X, π := s })) →     ∀ (X : T), (CategoryTheory
.MorphismProperty.structuredArrowObj L P).IsClosedUnderLimitsOfShape J
参数：c : (D : CategoryTheory.Functor J T) → [CategoryTheory.Limits.HasLimit D] → C
ategoryTheory.Limits.Cone D；hc :     (D : CategoryTheory.Functor J T) →       [i
nst_6 : CategoryTheory.Limits.HasLimit D] → CategoryTheory.Limits.IsLimit (c D)；
∀ (D : CategoryTheory.Functor J T) [inst_6 : CategoryTheory.Limits.HasLimit D] {
X : T}       (s : (CategoryTheory.Functor.const J).obj X ⟶ D),       (∀ (j : J),
 P (s.app j)) → P ((hc D).lift { pt := X, π := s })；X : T；CategoryTheory.Morphis
mProperty.structuredArrowObj L P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.preservesLimit_of_createsLimit_and_hasLimit`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.StructuredArrow.w`：w : X.hom ≫ T.map f.right = Y.hom
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.IsLimit.hom_ext`：hom_ext (h : IsLimit t) {W : C} {
f f' : W ⟶ t.pt} (w : forall j, f ≫ t.π.app j = f' ≫ t.π.app j) : f = f'
· 使用定理 `CategoryTheory.Limits.IsLimit.fac`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} 
C]   {F : CategoryTheor…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MorphismProperty.structuredArrowObj_iff`：∀ {B : Type u_2}
 [inst : CategoryTheory.Category.{v_2, u_2} B] {T : Type u_3}   [inst_1 : Catego
ryTheory.Category.{v_3, u_3} T] (R : Categor…
· 使用定理 `CategoryTheory.Limits.instHasLimitCompOfPreservesLimit`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.comp_preservesLimitsOfShape`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.preservesLimitOfShape_of_createsLimitsOfShape_and_hasLimi
tsOfShape`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type
 u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.IsLimit.lift_comp_conePointUniqueUpToIso_hom`：lift
_comp_conePointUniqueUpToIso_hom {r s t : Cone F} (P : IsLimit s) (Q : IsLimit t
) : P.lift r ≫ (conePointUniqueUpToIso P Q).hom = Q.lift…
· 使用定理 `CategoryTheory.MorphismProperty.cancel_right_of_respectsIso`：cancel_righ
t_of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C} (f : 
X ⟶ Y) (g : Y ⟶ Z) [IsIso g] : P (f ≫ g) ↔ P f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.ObjectProperty.LimitOfShape.prop_diag_obj`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {P : CategoryTheory.ObjectPrope
rty C} {J : Type u'}   [inst_1 : CategoryTheor…
-/
lemma StructuredArrow.isClosedUnderLimitsOfShape {J : Type*} [Category* J]
    {P : MorphismProperty T} [P.RespectsIso] [PreservesLimitsOfShape J L] [HasLimitsOfShape J A]
    (c : ∀ (D : J ⥤ T) [HasLimit D], Cone D)
    (hc : ∀ (D : J ⥤ T) [HasLimit D], IsLimit (c D))
    (H : ∀ (D : J ⥤ T) [HasLimit D] {X : T} (s : (Functor.const J).obj X ⟶ D),
      (∀ j, P (s.app j)) → P ((hc D).lift (Cone.mk X s))) (X : T) :
    (P.structuredArrowObj L (X := X)).IsClosedUnderLimitsOfShape J where
  limitsOfShape_le Y := by
    intro ⟨d⟩
    let hd : IsLimit ((CategoryTheory.StructuredArrow.proj X L ⋙ L).mapCone d.cone) :=
      isLimitOfPreserves _ d.isLimit
    have heq : Y.hom = hd.lift { pt := X, π := { app j := (d.diag.obj j).hom } } := by
      refine hd.hom_ext fun j ↦ ?_
      simp only [IsLimit.fac]
      simp
    rw [P.structuredArrowObj_iff, heq, ← (hc _).lift_comp_conePointUniqueUpToIso_hom hd,
      P.cancel_right_of_respectsIso]
    exact H _ _ d.prop_diag_obj

end

section

variable {X : T}

/-
**CategoryTheory.Over.closedUnderLimitsOfShape_discrete_empty** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Over`。
形式化陈述：∀ {T : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] (P : Catego
ryTheory.MorphismProperty T) {X : T}   [P.ContainsIdentities] [P.RespectsIso], P
.overObj.IsClosedUnderLimitsOfShape (CategoryTheory.Discrete PEmpty.{1})
参数：P : CategoryTheory.MorphismProperty T；CategoryTheory.Discrete PEmpty.{1}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CostructuredArrow.closedUnderLimitsOfShape_discrete_empty
`：∀ {T : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] (P : CategoryTh
eory.MorphismProperty T) {A : Type u_2}   [inst_1 : CategoryTh…
· 使用定理 `CategoryTheory.Functor.Faithful.id`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C], (CategoryTheory.Functor.id C).Faithful
· 使用定理 `CategoryTheory.Functor.Full.id`：∀ {C : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} C], (CategoryTheory.Functor.id C).Full
-/
instance Over.closedUnderLimitsOfShape_discrete_empty [P.ContainsIdentities] [P.RespectsIso] :
    (P.overObj (X := X)).IsClosedUnderLimitsOfShape (Discrete PEmpty.{1}) :=
  CostructuredArrow.closedUnderLimitsOfShape_discrete_empty P

set_option backward.defeqAttrib.useBackward true in
/-- Let `P` be stable under composition and base change. If `P` satisfies cancellation on the right,
the subcategory of `Over X` defined by `P` is closed under pullbacks.

Without the cancellation property, this does not in general. Consider for example
`P = Function.Surjective` on `Type`. -/
/-
**CategoryTheory.Over.closedUnderLimitsOfShape_pullback** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Over`。
形式化陈述：∀ {T : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] (P : Catego
ryTheory.MorphismProperty T) {X : T}   [CategoryTheory.Limits.HasPullbacks T] [P
.IsStableUnderComposition] [P.IsStableUnderBaseChange]   [P.HasOfPostcompPropert
y P], P.overObj.IsClosedUnderLimitsOfShape CategoryTheory.Limits.WalkingCospan
参数：P : CategoryTheory.MorphismProperty T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CostructuredArrow.closedUnderLimitsOfShape_walkingCospan`
：∀ {T : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] (P : CategoryThe
ory.MorphismProperty T) {A : Type u_2}   [inst_1 : CategoryTh…
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfShapeOfIsRightAdjoint`：∀ {J 
: Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1, 
u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…

--- 原说明 ---
Let `P` be stable under composition and base change. If `P` satisfies cancellati
on on the right,
the subcategory of `Over X` defined by `P` is closed under pullbacks.

Without the cancellation property, this does not in general. Consider for exampl
e
`P = Function.Surjective` on `Type`.
-/
instance Over.closedUnderLimitsOfShape_pullback [HasPullbacks T]
    [P.IsStableUnderComposition] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P] :
    (P.overObj (X := X)).IsClosedUnderLimitsOfShape WalkingCospan :=
  CostructuredArrow.closedUnderLimitsOfShape_walkingCospan _ _

end

section

variable {X : T}

/-
**CategoryTheory.Under.closedUnderColimitsOfShape_discrete_empty** 是 Mathlib 中的一
个定理，位于命名空间 `CategoryTheory.Under`。
形式化陈述：∀ {T : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] (P : Catego
ryTheory.MorphismProperty T) {X : T}   [P.ContainsIdentities] [P.RespectsIso], P
.underObj.IsClosedUnderColimitsOfShape (CategoryTheory.Discrete PEmpty.{1})
参数：P : CategoryTheory.MorphismProperty T；CategoryTheory.Discrete PEmpty.{1}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.StructuredArrow.closedUnderColimitsOfShape_discrete_empty
`：∀ {T : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] (P : CategoryTh
eory.MorphismProperty T) {A : Type u_2}   [inst_1 : CategoryTh…
· 使用定理 `CategoryTheory.Functor.Faithful.id`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C], (CategoryTheory.Functor.id C).Faithful
· 使用定理 `CategoryTheory.Functor.Full.id`：∀ {C : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} C], (CategoryTheory.Functor.id C).Full
-/
instance Under.closedUnderColimitsOfShape_discrete_empty [P.ContainsIdentities] [P.RespectsIso] :
    (P.underObj (X := X)).IsClosedUnderColimitsOfShape (Discrete PEmpty.{1}) :=
  StructuredArrow.closedUnderColimitsOfShape_discrete_empty (L := 𝟭 _) P

/-- Let `P` be stable under composition and cobase change. If `P` satisfies cancellation on the
left, the subcategory of `Under X` defined by `P` is closed under pushouts. -/
/-
**CategoryTheory.Under.closedUnderColimitsOfShape_pushout** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Under`。
形式化陈述：∀ {T : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] (P : Catego
ryTheory.MorphismProperty T) {X : T}   [CategoryTheory.Limits.HasPushouts T] [P.
IsStableUnderComposition] [P.IsStableUnderCobaseChange]   [P.HasOfPrecompPropert
y P], P.underObj.IsClosedUnderColimitsOfShape CategoryTheory.Limits.WalkingSpan
参数：P : CategoryTheory.MorphismProperty T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.isClosedUnderColimitsOfShape_iff_op`：isClo
sedUnderColimitsOfShape_iff_op : P.IsClosedUnderColimitsOfShape J ↔ P.op.IsClose
dUnderLimitsOfShape Jᵒᵖ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ObjectProperty.isClosedUnderLimitsOfShape_inverseImage_if
f`：isClosedUnderLimitsOfShape_inverseImage_iff (P : ObjectProperty D) [P.IsClose
dUnderIsomorphisms] (e : C ≌ D) : (P.inverseImage e.functor).Is…
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderIsomorphismsOppositeOp`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.Obje
ctProperty C)   [P.IsClosedUnderIsomorphisms], P.op.IsClose…
· 使用定理 `CategoryTheory.MorphismProperty.instIsClosedUnderIsomorphismsUnderUnderO
bjOfRespectsIso`：∀ {T : Type u_3} [inst : CategoryTheory.Category.{v_3, u_3} T] 
{W : CategoryTheory.MorphismProperty T} {X : T}   [W.RespectsIso], W.underObj…
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderCobaseChange.respectsIso`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.Morp
hismProperty C}   [P.IsStableUnderCobaseChange], P.Respects…
· 使用引理 `CategoryTheory.MorphismProperty.inverseImage_op_underObj`：inverseImage_o
p_underObj (W : MorphismProperty T) {X : T} : W.underObj.op.inverseImage (Over.o
pEquivOpUnder X).functor = W.op.overObj
· 使用引理 `CategoryTheory.ObjectProperty.isClosedUnderLimitsOfShape_iff_of_equivale
nce`：isClosedUnderLimitsOfShape_iff_of_equivalence (e : J ≌ J') : P.IsClosedUnde
rLimitsOfShape J ↔ P.IsClosedUnderLimitsOfShape J'
· 使用定理 `CategoryTheory.Over.closedUnderLimitsOfShape_pullback`：∀ {T : Type u_1} 
[inst : CategoryTheory.Category.{v_1, u_1} T] (P : CategoryTheory.MorphismProper
ty T) {X : T}   [CategoryTheory.Limits.HasP…
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderComposition.op`：∀ {C : Type
 u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.MorphismProper
ty C}   [P.IsStableUnderComposition], P.op.IsStab…
· 使用定理 `CategoryTheory.MorphismProperty.IsStableUnderCobaseChange.op`：∀ {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.MorphismPrope
rty C}   [P.IsStableUnderCobaseChange], P.op.IsSta…
· 使用定理 `CategoryTheory.MorphismProperty.instHasOfPostcompPropertyOppositeOpOfHas
OfPrecompProperty`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (W :
 CategoryTheory.MorphismProperty C)   {W' : CategoryTheory.MorphismProperty C} …

--- 原说明 ---
Let `P` be stable under composition and cobase change. If `P` satisfies cancella
tion on the
left, the subcategory of `Under X` defined by `P` is closed under pushouts.
-/
instance Under.closedUnderColimitsOfShape_pushout [HasPushouts T]
    [P.IsStableUnderComposition] [P.IsStableUnderCobaseChange] [P.HasOfPrecompProperty P] :
    (P.underObj (X := X)).IsClosedUnderColimitsOfShape WalkingSpan := by
  rw [ObjectProperty.isClosedUnderColimitsOfShape_iff_op, ←
    ObjectProperty.isClosedUnderLimitsOfShape_inverseImage_iff _ _ (Over.opEquivOpUnder _),
    MorphismProperty.inverseImage_op_underObj,
    ObjectProperty.isClosedUnderLimitsOfShape_iff_of_equivalence _ walkingSpanOpEquiv]
  infer_instance

end

namespace MorphismProperty.Over

variable (X : T)

/-
**CategoryTheory.MorphismProperty.Over.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.MorphismProperty.Over`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [P.ContainsIdentities] [P.RespectsIso] :
    CreatesLimitsOfShape (Discrete PEmpty.{1}) (Over.forget P ⊤ X) := by
  apply +allowSynthFailures forgetCreatesLimitsOfShapeOfClosed
  · exact inferInstanceAs (HasLimitsOfShape _ (Over X))
  · apply Over.closedUnderLimitsOfShape_discrete_empty _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable {X} in
/-
**CategoryTheory.MorphismProperty.Over.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.MorphismProperty.Over`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.ContainsIdentities] (Y : P.Over ⊤ X) :
    Unique (Y ⟶ Over.mk ⊤ (𝟙 X) (P.id_mem X)) where
  default := Over.homMk Y.hom
  uniq a := by
    ext
    · simp only [mk_left, homMk_hom, Over.homMk_left]
      rw [← Over.w a]
      simp only [mk_left, Functor.const_obj_obj, mk_hom, Category.comp_id]

/-- `X ⟶ X` is the terminal object of `P.Over ⊤ X`. -/
/-
**CategoryTheory.MorphismProperty.Over.mkIdTerminal** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.MorphismProperty.Over`。
形式化陈述：mkIdTerminal [P.ContainsIdentities] : IsTerminal (Over.mk ⊤ (𝟙 X) (P.id_me
m X))
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用引理 `CategoryTheory.MorphismProperty.id_mem`：id_mem (W : MorphismProperty C) 
[W.ContainsIdentities] (X : C) : W (𝟙 X)

--- 原说明 ---
`X ⟶ X` is the terminal object of `P.Over ⊤ X`.
-/
def mkIdTerminal [P.ContainsIdentities] :
    IsTerminal (Over.mk ⊤ (𝟙 X) (P.id_mem X)) :=
  IsTerminal.ofUnique _
/-
**CategoryTheory.MorphismProperty.Over.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.MorphismProperty.Over`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.ContainsIdentities] : HasTerminal (P.Over ⊤ X) :=
  let h : IsTerminal (Over.mk ⊤ (𝟙 X) (P.id_mem X)) := Over.mkIdTerminal P X
  h.hasTerminal

/-- If `P` is stable under composition, base change and satisfies post-cancellation,
`Over.forget P ⊤ X` creates pullbacks. -/
/-
**CategoryTheory.MorphismProperty.Over.createsLimitsOfShape_walkingCospan** 是 Ma
thlib 中的一个实例，位于命名空间 `CategoryTheory.MorphismProperty.Over`。
形式化陈述：createsLimitsOfShape_walkingCospan [HasPullbacks T] [P.IsStableUnderCompos
ition] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P] : CreatesLimitsOf
Shape WalkingCospan (Over.forget P ⊤ X)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `P` is stable under composition, base change and satisfies post-cancellation,
`Over.forget P ⊤ X` creates pullbacks.
-/
noncomputable instance createsLimitsOfShape_walkingCospan [HasPullbacks T]
    [P.IsStableUnderComposition] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P] :
    CreatesLimitsOfShape WalkingCospan (Over.forget P ⊤ X) :=
  CostructuredArrow.createsLimitsOfShape_walkingCospan _ _

/-- If `P` is stable under composition, base change and satisfies post-cancellation,
`P.Over ⊤ X` has pullbacks -/
/-
**CategoryTheory.MorphismProperty.Over.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.MorphismProperty.Over`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `P` is stable under composition, base change and satisfies post-cancellation,
`P.Over ⊤ X` has pullbacks
-/
instance (priority := 900) hasPullbacks [HasPullbacks T] [P.IsStableUnderComposition]
    [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P] : HasPullbacks (P.Over ⊤ X) :=
  CostructuredArrow.hasPullbacks _ _

variable [HasPullbacks T] [P.IsMultiplicative]
  [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
/-
**CategoryTheory.MorphismProperty.Over.hasFiniteLimits** 是 Mathlib 中的一个实例，位于命名空间
 `CategoryTheory.MorphismProperty.Over`。
形式化陈述：hasFiniteLimits : HasFiniteLimits (P.Over ⊤ X)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasTerminal_and_pullbacks`：hasF
initeLimits_of_hasTerminal_and_pullbacks [HasTerminal C] [HasPullbacks C] : HasF
initeLimits C
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `CategoryTheory.MorphismProperty.Over.instHasTerminalTopOfContainsIdentit
ies`：∀ {T : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} T] (P : Categor
yTheory.MorphismProperty T) (X : T)   [P.ContainsIdentities], Cat…
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toContainsIdentities`：∀
 {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheory.Morp
hismProperty C}   [self : W.IsMultiplicative], W.ContainsId…
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.toIsStableUnderComposit
ion`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryTheor
y.MorphismProperty C}   [self : W.IsMultiplicative], W.IsStableUn…
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfShapeOfIsRightAdjoint`：∀ {J 
: Type u_1} {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_1, 
u_1} J]   [inst_1 : CategoryTheory.Category.{v_2, u_2} …
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
-/
instance hasFiniteLimits : HasFiniteLimits (P.Over ⊤ X) :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks
/-
**CategoryTheory.MorphismProperty.Over.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.MorphismProperty.Over`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : CreatesFiniteLimits (Over.forget P ⊤ X) :=
  createsFiniteLimitsOfCreatesTerminalAndPullbacks _
/-
**CategoryTheory.MorphismProperty.Over.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.MorphismProperty.Over`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasFiniteWidePullbacks T] : HasFiniteLimits (P.Over ⊤ X) :=
  hasFiniteLimits_of_hasLimitsLimits_of_createsFiniteLimits (Over.forget P ⊤ X)
/-
**CategoryTheory.MorphismProperty.Over.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.MorphismProperty.Over`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PreservesFiniteLimits (Over.forget P ⊤ X) :=
  preservesFiniteLimits_of_preservesTerminal_and_pullbacks (Over.forget P ⊤ X)
/-
**CategoryTheory.MorphismProperty.Over.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheor
y.MorphismProperty.Over`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : T} (f : X ⟶ Y) : PreservesFiniteLimits (pullback P ⊤ f) where
  preservesFiniteLimits J _ _ := by
    have : PreservesLimitsOfShape J
        (MorphismProperty.Over.pullback P ⊤ f ⋙ MorphismProperty.Over.forget _ _ _) :=
      inferInstanceAs <| PreservesLimitsOfShape J <|
        Over.forget _ _ _ ⋙ CategoryTheory.Over.pullback f
    exact preservesLimitsOfShape_of_reflects_of_preserves
      (MorphismProperty.Over.pullback P ⊤ f) (MorphismProperty.Over.forget _ _ _)

end MorphismProperty.Over

namespace MorphismProperty.Under

variable (X : T)

/-
**CategoryTheory.MorphismProperty.Under.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.MorphismProperty.Under`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [P.ContainsIdentities] [P.RespectsIso] :
    CreatesColimitsOfShape (Discrete PEmpty.{1}) (Under.forget P ⊤ X) := by
  apply +allowSynthFailures forgetCreatesColimitsOfShapeOfClosed
  · exact inferInstanceAs (HasColimitsOfShape _ (Under X))
  · apply Under.closedUnderColimitsOfShape_discrete_empty _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {X} in
/-
**CategoryTheory.MorphismProperty.Under.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.MorphismProperty.Under`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.ContainsIdentities] (Y : P.Under ⊤ X) :
    Unique (Under.mk ⊤ (𝟙 X) (P.id_mem X) ⟶ Y) where
  default := Under.homMk Y.hom (by simp)
  uniq a := by ext; simp [← Under.w a]

/-- `X ⟶ X` is the initial object of `P.Under ⊤ X`. -/
/-
**CategoryTheory.MorphismProperty.Under.mkIdInitial** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.MorphismProperty.Under`。
形式化陈述：mkIdInitial [P.ContainsIdentities] : IsInitial (Under.mk ⊤ (𝟙 X) (P.id_mem
 X))
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用引理 `CategoryTheory.MorphismProperty.id_mem`：id_mem (W : MorphismProperty C) 
[W.ContainsIdentities] (X : C) : W (𝟙 X)

--- 原说明 ---
`X ⟶ X` is the initial object of `P.Under ⊤ X`.
-/
def mkIdInitial [P.ContainsIdentities] :
    IsInitial (Under.mk ⊤ (𝟙 X) (P.id_mem X)) :=
  .ofUnique _
/-
**CategoryTheory.MorphismProperty.Under.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.MorphismProperty.Under`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.ContainsIdentities] : HasInitial (P.Under ⊤ X) :=
  (Under.mkIdInitial P X).hasInitial

/-- If `P` is stable under composition, cobase change and satisfies pre-cancellation,
`Under.forget P ⊤ X` creates pushouts. -/
/-
**CategoryTheory.MorphismProperty.Under.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.MorphismProperty.Under`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `P` is stable under composition, cobase change and satisfies pre-cancellation
,
`Under.forget P ⊤ X` creates pushouts.
-/
noncomputable instance [HasPushouts T]
    [P.IsStableUnderComposition] [P.IsStableUnderCobaseChange] [P.HasOfPrecompProperty P] :
    CreatesColimitsOfShape WalkingSpan (Under.forget P ⊤ X) := by
  apply +allowSynthFailures forgetCreatesColimitsOfShapeOfClosed
  · exact inferInstanceAs (HasColimitsOfShape WalkingSpan (Under X))
  · apply Under.closedUnderColimitsOfShape_pushout

/-- If `P` is stable under composition, cobase change and satisfies pre-cancellation,
`P.Under ⊤ X` has pushouts. -/
/-
**CategoryTheory.MorphismProperty.Under.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.MorphismProperty.Under`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `P` is stable under composition, cobase change and satisfies pre-cancellation
,
`P.Under ⊤ X` has pushouts.
-/
instance (priority := 900) [HasPushouts T] [P.IsStableUnderComposition]
    [P.IsStableUnderCobaseChange] [P.HasOfPrecompProperty P] : HasPushouts (P.Under ⊤ X) := by
  apply +allowSynthFailures hasColimitsOfShape_of_closedUnderColimitsOfShape
  · exact inferInstanceAs (HasColimitsOfShape WalkingSpan (Under X))
  · apply Under.closedUnderColimitsOfShape_pushout

variable [HasPushouts T] [P.IsStableUnderComposition] [P.ContainsIdentities]
  [P.IsStableUnderCobaseChange] [P.HasOfPrecompProperty P]
/-
**CategoryTheory.MorphismProperty.Under.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.MorphismProperty.Under`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : CreatesFiniteColimits (Under.forget P ⊤ X) :=
  createsFiniteColimitsOfCreatesInitialAndPushouts _
/-
**CategoryTheory.MorphismProperty.Under.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.MorphismProperty.Under`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasFiniteWidePushouts T] : HasFiniteColimits (P.Under ⊤ X) :=
  hasFiniteColimits_of_hasColimits_of_createsFiniteColimits (Under.forget P ⊤ X)
/-
**CategoryTheory.MorphismProperty.Under.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.MorphismProperty.Under`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PreservesFiniteColimits (Under.forget P ⊤ X) :=
  preservesFiniteColimits_of_preservesInitial_and_pushouts (Under.forget P ⊤ X)

end MorphismProperty.Under

end CategoryTheory

