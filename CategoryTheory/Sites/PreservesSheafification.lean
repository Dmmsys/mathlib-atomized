/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.CompatibleSheafification
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Sheafification

/-! # Functors which preserve sheafification

In this file, given a Grothendieck topology `J` on `C` and `F : A ⥤ B`,
we define a type class `J.PreservesSheafification F`. We say that `F` preserves
the sheafification if whenever a morphism of presheaves `P₁ ⟶ P₂` induces
an isomorphism on the associated sheaves, then the induced map `P₁ ⋙ F ⟶ P₂ ⋙ F`
also induces an isomorphism on the associated sheaves. (Note: it suffices to check
this property for the map from any presheaf `P` to its associated sheaf, see
`GrothendieckTopology.preservesSheafification_iff_of_adjunctions`).

In general, we define `Sheaf.composeAndSheafify J F : Sheaf J A ⥤ Sheaf J B` as the functor
which sends a sheaf `G` to the sheafification of the composition `G.val ⋙ F`.
If `J.PreservesSheafification F`, we show that this functor can also be thought of
as the localization of the functor `_ ⋙ F` on presheaves: we construct an isomorphism
`presheafToSheafCompComposeAndSheafifyIso` between
`presheafToSheaf J A ⋙ Sheaf.composeAndSheafify J F` and
`(whiskeringRight Cᵒᵖ A B).obj F ⋙ presheafToSheaf J B`.

Moreover, if we assume `J.HasSheafCompose F`, we obtain an isomorphism
`sheafifyComposeIso J F P : sheafify J (P ⋙ F) ≅ sheafify J P ⋙ F`.

We show that under suitable assumptions, the forgetful functor from a concrete
category preserves sheafification; this holds more generally for
functors between such concrete categories which commute both with
suitable limits and colimits.

## TODO
* construct an isomorphism `Sheaf.composeAndSheafify J F ≅ sheafCompose J F`

-/

@[expose] public section

universe v u

namespace CategoryTheory

open Category Limits CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A B : Type*} [Category* A] [Category* B] (F : A ⥤ B)

namespace GrothendieckTopology

/-- A functor `F : A ⥤ B` preserves the sheafification for the Grothendieck
topology `J` on a category `C` if whenever a morphism of presheaves `f : P₁ ⟶ P₂`
in `Cᵒᵖ ⥤ A` is such that becomes an iso after sheafification, then it is
also the case of `whiskerRight f F : P₁ ⋙ F ⟶ P₂ ⋙ F`. -/
/-
**CategoryTheory.GrothendieckTopology.PreservesSheafification** 是 Mathlib 中的一个归纳
类型，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     CategoryT
heory.GrothendieckTopology C →       {A : Type u_1} →         {B : Type u_2} →  
         [inst : CategoryTheory.Category.{v_1, u_1} A] →             [inst_1 : C
ategoryTheory.Category.{v_2, u_2} B] → CategoryTheory.Functor A B → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `F : A ⥤ B` preserves the sheafification for the Grothendieck
topology `J` on a category `C` if whenever a morphism of presheaves `f : P₁ ⟶ P₂
`
in `Cᵒᵖ ⥤ A` is such that becomes an iso after sheafification, then it is
also the case of `whiskerRight f F : P₁ ⋙ F ⟶ P₂ ⋙ F`.
-/
class PreservesSheafification : Prop where
  le : J.W ≤ J.W.inverseImage ((whiskeringRight Cᵒᵖ A B).obj F)

variable [PreservesSheafification J F]
/-
**CategoryTheory.GrothendieckTopology.W_of_preservesSheafification** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：W_of_preservesSheafification {P₁ P₂ : Cᵒᵖ ⥤ A} (f : P₁ ⟶ P₂) (hf : J.W f) 
: J.W (whiskerRight f F)
参数：f : P₁ ⟶ P₂；hf : J.W f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.PreservesSheafification.le`：∀ {C : T
ype u} {inst : CategoryTheory.Category.{v, u} C} {J : CategoryTheory.Grothendiec
kTopology C} {A : Type u_1}   {B : Type u_2} {inst_1…
-/
lemma W_of_preservesSheafification
    {P₁ P₂ : Cᵒᵖ ⥤ A} (f : P₁ ⟶ P₂) (hf : J.W f) :
    J.W (whiskerRight f F) :=
  PreservesSheafification.le _ hf

variable [HasWeakSheafify J B]

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.GrothendieckTopology.W_isInvertedBy_whiskeringRight_presheafToS
heaf** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：W_isInvertedBy_whiskeringRight_presheafToSheaf : J.W.IsInvertedBy (((whisk
eringRight Cᵒᵖ A B).obj F) ⋙ presheafToSheaf J B)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.GrothendieckTopology.W_iff`：W_iff {P₁ P₂ : Cᵒᵖ ⥤ A} (f : 
P₁ ⟶ P₂) : J.W f ↔ IsIso ((presheafToSheaf J A).map f)
· 使用引理 `CategoryTheory.GrothendieckTopology.W_of_preservesSheafification`：W_of_p
reservesSheafification {P₁ P₂ : Cᵒᵖ ⥤ A} (f : P₁ ⟶ P₂) (hf : J.W f) : J.W (whisk
erRight f F)
-/
lemma W_isInvertedBy_whiskeringRight_presheafToSheaf :
    J.W.IsInvertedBy (((whiskeringRight Cᵒᵖ A B).obj F) ⋙ presheafToSheaf J B) := by
  intro P₁ P₂ f hf
  dsimp
  rw [← W_iff]
  exact J.W_of_preservesSheafification F _ hf

end GrothendieckTopology

section

variable [HasWeakSheafify J B]

/-- This is the functor sending a sheaf `X : Sheaf J A` to the sheafification
of `X.val ⋙ F`. -/
/-
**CategoryTheory.Sheaf.composeAndSheafify** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.Sheaf`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     (J : Cate
goryTheory.GrothendieckTopology C) →       {A : Type u_1} →         {B : Type u_
2} →           [inst_1 : CategoryTheory.Category.{v_1, u_1} A] →             [in
st_2 : CategoryTheory.Category.{v_2, u_2} B] →               CategoryTheory.Func
tor A B →                 [CategoryTheory.HasWeakSheafify J B] →                
   CategoryTheory.Functor (CategoryTheory.Sheaf J A) (CategoryTheory.Sheaf J B)
参数：J : CategoryTheory.GrothendieckTopology C；CategoryTheory.Sheaf J A；CategoryTh
eory.Sheaf J B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the functor sending a sheaf `X : Sheaf J A` to the sheafification
of `X.val ⋙ F`.
-/
noncomputable abbrev Sheaf.composeAndSheafify : Sheaf J A ⥤ Sheaf J B :=
  sheafToPresheaf J A ⋙ (whiskeringRight _ _ _).obj F ⋙ presheafToSheaf J B

variable [HasWeakSheafify J A]

/-- The canonical natural transformation from
`(whiskeringRight Cᵒᵖ A B).obj F ⋙ presheafToSheaf J B` to
`presheafToSheaf J A ⋙ Sheaf.composeAndSheafify J F`. -/
@[simps!]
/-
**CategoryTheory.toPresheafToSheafCompComposeAndSheafify** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory`。
形式化陈述：toPresheafToSheafCompComposeAndSheafify : (whiskeringRight Cᵒᵖ A B).obj F 
⋙ presheafToSheaf J B ⟶ presheafToSheaf J A ⋙ Sheaf.composeAndSheafify J F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical natural transformation from
`(whiskeringRight Cᵒᵖ A B).obj F ⋙ presheafToSheaf J B` to
`presheafToSheaf J A ⋙ Sheaf.composeAndSheafify J F`.
-/
noncomputable def toPresheafToSheafCompComposeAndSheafify :
    (whiskeringRight Cᵒᵖ A B).obj F ⋙ presheafToSheaf J B ⟶
      presheafToSheaf J A ⋙ Sheaf.composeAndSheafify J F :=
  whiskerRight (sheafificationAdjunction J A).unit
    ((whiskeringRight _ _ _).obj F ⋙ presheafToSheaf J B)

variable [J.PreservesSheafification F]

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso (toPresheafToSheafCompComposeAndSheafify J F) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  dsimp
  simpa only [← J.W_iff] using J.W_of_preservesSheafification F _ (J.W_toSheafify X)

/-- The canonical isomorphism between `presheafToSheaf J A ⋙ Sheaf.composeAndSheafify J F`
and `(whiskeringRight Cᵒᵖ A B).obj F ⋙ presheafToSheaf J B` when `F : A ⥤ B`
preserves sheafification. -/
@[simps! inv_app]
/-
**CategoryTheory.presheafToSheafCompComposeAndSheafifyIso** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory`。
形式化陈述：presheafToSheafCompComposeAndSheafifyIso : presheafToSheaf J A ⋙ Sheaf.com
poseAndSheafify J F ≅ (whiskeringRight Cᵒᵖ A B).obj F ⋙ presheafToSheaf J B
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instIsIsoFunctorOppositeSheafToPresheafToSheafCompCompose
AndSheafify`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (J : Categ
oryTheory.GrothendieckTopology C) {A : Type u_1}   {B : Type u_2} [inst_1…

--- 原说明 ---
The canonical isomorphism between `presheafToSheaf J A ⋙ Sheaf.composeAndSheafif
y J F`
and `(whiskeringRight Cᵒᵖ A B).obj F ⋙ presheafToSheaf J B` when `F : A ⥤ B`
preserves sheafification.
-/
noncomputable def presheafToSheafCompComposeAndSheafifyIso :
    presheafToSheaf J A ⋙ Sheaf.composeAndSheafify J F ≅
      (whiskeringRight Cᵒᵖ A B).obj F ⋙ presheafToSheaf J B :=
  (asIso (toPresheafToSheafCompComposeAndSheafify J F)).symm
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Localization.Lifting (presheafToSheaf J A) J.W
    ((whiskeringRight Cᵒᵖ A B).obj F ⋙ presheafToSheaf J B) (Sheaf.composeAndSheafify J F) :=
  ⟨presheafToSheafCompComposeAndSheafifyIso J F⟩

end

section

variable {G₁ : (Cᵒᵖ ⥤ A) ⥤ Sheaf J A} (adj₁ : G₁ ⊣ sheafToPresheaf J A)
  {G₂ : (Cᵒᵖ ⥤ B) ⥤ Sheaf J B}

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.GrothendieckTopology.preservesSheafification_iff_of_adjunctions
** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheo
ry.GrothendieckTopology C) {A : Type u_1}   {B : Type u_2} [inst_1 : CategoryThe
ory.Category.{v_1, u_1} A] [inst_2 : CategoryTheory.Category.{v_2, u_2} B]   (F 
: CategoryTheory.Functor A B)   {G₁ : CategoryTheory.Functor (CategoryTheory.Fun
ctor Cᵒᵖ A) (CategoryTheory.Sheaf J A)}   (adj₁ : G₁ ⊣ CategoryTheory.sheafToPre
sheaf J A)   {G₂ : CategoryTheory.Functor (CategoryTheory.Functor Cᵒᵖ B) (Catego
ryTheory.Sheaf J B)}   (adj₂ : G₂ ⊣ CategoryTheory.sheafToPresheaf J B),   J.Pre
servesSheafification F ↔     ∀ (P : CategoryTheory.Functor Cᵒᵖ A),       Categor
yTheory.IsIso (G₂.map (CategoryTheory.Functor.whiskerRight (adj₁.unit.app P) F))
参数：J : CategoryTheory.GrothendieckTopology C；F : CategoryTheory.Functor A B；Cate
goryTheory.Functor Cᵒᵖ A；CategoryTheory.Sheaf J A；adj₁ : G₁ ⊣ CategoryTheory.she
afToPresheaf J A；CategoryTheory.Functor Cᵒᵖ B；CategoryTheory.Sheaf J B；adj₂ : G₂
 ⊣ CategoryTheory.sheafToPresheaf J B；P : CategoryTheory.Functor Cᵒᵖ A；G₂.map (C
ategoryTheory.Functor.whiskerRight (adj₁.unit.app P) F)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.GrothendieckTopology.W_iff_isIso_map_of_adjunction`：W_iff
_isIso_map_of_adjunction (adj : G ⊣ sheafToPresheaf J A) {P₁ P₂ : Cᵒᵖ ⥤ A} (f : 
P₁ ⟶ P₂) : J.W f ↔ IsIso (G.map f)
· 使用引理 `CategoryTheory.GrothendieckTopology.W_of_preservesSheafification`：W_of_p
reservesSheafification {P₁ P₂ : Cᵒᵖ ⥤ A} (f : P₁ ⟶ P₂) (hf : J.W f) : J.W (whisk
erRight f F)
· 使用定理 `CategoryTheory.Adjunction.instIsIsoMapAppUnitOfFaithfulOfFull`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categ
oryTheory.Category.{v₂, u₂} D]   {L : CategoryTheor…
· 使用引理 `CategoryTheory.MorphismProperty.postcomp_iff`：postcomp_iff [W.RespectsRi
ght W'] [W.HasOfPostcompProperty W'] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hg : W
' g) : W (f ≫ g) ↔ W f
· 使用定理 `CategoryTheory.MorphismProperty.Respects.toRespectsRight`：∀ {C : Type u}
 {inst : CategoryTheory.CategoryStruct.{v, u} C} {P Q : CategoryTheory.MorphismP
roperty C}   [self : P.Respects Q], P.Respects…
· 使用定理 `CategoryTheory.MorphismProperty.instRespectsOfIsStableUnderComposition`：
∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (W : CategoryTheory.Mor
phismProperty C)   [W.IsStableUnderComposition], W.Respects …
· 使用定理 `CategoryTheory.MorphismProperty.HasTwoOutOfThreeProperty.toIsStableUnder
Composition`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : Categ
oryTheory.MorphismProperty C}   [self : W.HasTwoOutOfThreeProperty], W.Is…
· 使用定理 `CategoryTheory.ObjectProperty.instHasTwoOutOfThreePropertyIsLocal`：∀ {C 
: Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (P : CategoryTheory.Ob
jectProperty C),   P.isLocal.HasTwoOutOfThreeProperty
· 使用定理 `CategoryTheory.MorphismProperty.HasTwoOutOfThreeProperty.toHasOfPostcomp
Property`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : Category
Theory.MorphismProperty C}   [self : W.HasTwoOutOfThreeProperty], W.Ha…
· 使用定理 `CategoryTheory.Functor.whiskerRight_comp`：whiskerRight_comp {G H K : C ⥤
 D} (α : G ⟶ H) (β : H ⟶ K) (F : D ⥤ E) : whiskerRight (α ≫ β) F = whiskerRight 
α F ≫ whiskerRight β F
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用引理 `CategoryTheory.MorphismProperty.precomp_iff`：precomp_iff [W.RespectsLeft
 W'] [W.HasOfPrecompProperty W'] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W' f)
 : W (f ≫ g) ↔ W g
· 使用定理 `CategoryTheory.MorphismProperty.Respects.toRespectsLeft`：∀ {C : Type u} 
{inst : CategoryTheory.CategoryStruct.{v, u} C} {P Q : CategoryTheory.MorphismPr
operty C}   [self : P.Respects Q], P.Respects…
· 使用定理 `CategoryTheory.MorphismProperty.HasTwoOutOfThreeProperty.toHasOfPrecompP
roperty`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryT
heory.MorphismProperty C}   [self : W.HasTwoOutOfThreeProperty], W.Ha…
· 使用引理 `CategoryTheory.ObjectProperty.isLocal_of_isIso`：isLocal_of_isIso {X Y : 
C} (f : X ⟶ Y) [IsIso f] : P.isLocal f
-/
lemma GrothendieckTopology.preservesSheafification_iff_of_adjunctions
    (adj₂ : G₂ ⊣ sheafToPresheaf J B) :
    J.PreservesSheafification F ↔ ∀ (P : Cᵒᵖ ⥤ A),
      IsIso (G₂.map (whiskerRight (adj₁.unit.app P) F)) := by
  simp only [← J.W_iff_isIso_map_of_adjunction adj₂]
  constructor
  · intro _ P
    apply W_of_preservesSheafification
    rw [J.W_iff_isIso_map_of_adjunction adj₁]
    infer_instance
  · intro h
    constructor
    intro P₁ P₂ f hf
    rw [J.W_iff_isIso_map_of_adjunction adj₁] at hf
    dsimp [MorphismProperty.inverseImage]
    rw [← (W _).postcomp_iff _ _ (h P₂), ← whiskerRight_comp]
    erw [adj₁.unit.naturality f]
    dsimp only [Functor.comp_map]
    rw [whiskerRight_comp, (W _).precomp_iff _ _ (h P₁)]
    apply ObjectProperty.isLocal_of_isIso

section HasSheafCompose

variable (adj₂ : G₂ ⊣ sheafToPresheaf J B) [J.HasSheafCompose F]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonical natural transformation
`(whiskeringRight Cᵒᵖ A B).obj F ⋙ G₂ ⟶ G₁ ⋙ sheafCompose J F`
when `F : A ⥤ B` is such that `J.HasSheafCompose F`, and that `G₁` and `G₂` are
left adjoints to the forget functors `sheafToPresheaf`. -/
/-
**CategoryTheory.sheafComposeNatTrans** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`
。
形式化陈述：sheafComposeNatTrans : (whiskeringRight Cᵒᵖ A B).obj F ⋙ G₂ ⟶ G₁ ⋙ sheafCo
mpose J F where app P
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The canonical natural transformation
`(whiskeringRight Cᵒᵖ A B).obj F ⋙ G₂ ⟶ G₁ ⋙ sheafCompose J F`
when `F : A ⥤ B` is such that `J.HasSheafCompose F`, and that `G₁` and `G₂` are
left adjoints to the forget functors `sheafToPresheaf`.
-/
def sheafComposeNatTrans :
    (whiskeringRight Cᵒᵖ A B).obj F ⋙ G₂ ⟶ G₁ ⋙ sheafCompose J F where
  app P := (adj₂.homEquiv _ _).symm (whiskerRight (adj₁.unit.app P) F)
  naturality {P Q} f := by
    dsimp
    erw [← adj₂.homEquiv_naturality_left_symm,
      ← adj₂.homEquiv_naturality_right_symm]
    congr 1
    ext X
    have := NatTrans.congr_app (adj₁.unit.naturality f) X
    dsimp at this ⊢
    grind

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.sheafComposeNatTrans_fac** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory`。
形式化陈述：sheafComposeNatTrans_fac (P : Cᵒᵖ ⥤ A) : adj₂.unit.app (P ⋙ F) ≫ (sheafToP
resheaf J B).map ((sheafComposeNatTrans J F adj₁ adj₂).app P) = whiskerRight (ad
j₁.unit.app P) F
参数：P : Cᵒᵖ ⥤ A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Adjunction.homEquiv_counit`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{
v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.NatTrans.mk.congr_simp`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, 
u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Adjunction.unit_naturality_assoc`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.right_triangle_components`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sheafComposeNatTrans_fac (P : Cᵒᵖ ⥤ A) :
    adj₂.unit.app (P ⋙ F) ≫
      (sheafToPresheaf J B).map ((sheafComposeNatTrans J F adj₁ adj₂).app P) =
        whiskerRight (adj₁.unit.app P) F := by
  simp [sheafComposeNatTrans, -ObjectProperty.ι_obj, -ObjectProperty.ι_map,
    Adjunction.homEquiv_counit]
/-
**CategoryTheory.sheafComposeNatTrans_app_uniq** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory`。
形式化陈述：sheafComposeNatTrans_app_uniq (P : Cᵒᵖ ⥤ A) (α : G₂.obj (P ⋙ F) ⟶ (sheafCo
mpose J F).obj (G₁.obj P)) (hα : adj₂.unit.app (P ⋙ F) ≫ (sheafToPresheaf J B).m
ap α = whiskerRight (adj₁.unit.app P) F) : α = (sheafComposeNatTrans J F adj₁ ad
j₂).app P
参数：P : Cᵒᵖ ⥤ A；α : G₂.obj (P ⋙ F) ⟶ (sheafCompose J F).obj (G₁.obj P)；hα : adj₂.
unit.app (P ⋙ F) ≫ (sheafToPresheaf J B).map α = whiskerRight (adj₁.unit.app P) 
F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Adjunction.homEquiv_unit`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂
, u₂} D]   {F : CategoryTheor…
-/
lemma sheafComposeNatTrans_app_uniq (P : Cᵒᵖ ⥤ A)
    (α : G₂.obj (P ⋙ F) ⟶ (sheafCompose J F).obj (G₁.obj P))
    (hα : adj₂.unit.app (P ⋙ F) ≫ (sheafToPresheaf J B).map α =
        whiskerRight (adj₁.unit.app P) F) :
    α = (sheafComposeNatTrans J F adj₁ adj₂).app P := by
  apply (adj₂.homEquiv _ _).injective
  dsimp [ObjectProperty.ι_obj, sheafComposeNatTrans, id_obj]
  erw [Equiv.apply_symm_apply]
  rw [← hα]
  apply adj₂.homEquiv_unit

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.GrothendieckTopology.preservesSheafification_iff_of_adjunctions
_of_hasSheafCompose** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.GrothendieckTopolo
gy`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheo
ry.GrothendieckTopology C) {A : Type u_1}   {B : Type u_2} [inst_1 : CategoryThe
ory.Category.{v_1, u_1} A] [inst_2 : CategoryTheory.Category.{v_2, u_2} B]   (F 
: CategoryTheory.Functor A B)   {G₁ : CategoryTheory.Functor (CategoryTheory.Fun
ctor Cᵒᵖ A) (CategoryTheory.Sheaf J A)}   (adj₁ : G₁ ⊣ CategoryTheory.sheafToPre
sheaf J A)   {G₂ : CategoryTheory.Functor (CategoryTheory.Functor Cᵒᵖ B) (Catego
ryTheory.Sheaf J B)}   (adj₂ : G₂ ⊣ CategoryTheory.sheafToPresheaf J B) [inst_3 
: J.HasSheafCompose F],   J.PreservesSheafification F ↔ CategoryTheory.IsIso (Ca
tegoryTheory.sheafComposeNatTrans J F adj₁ adj₂)
参数：J : CategoryTheory.GrothendieckTopology C；F : CategoryTheory.Functor A B；Cate
goryTheory.Functor Cᵒᵖ A；CategoryTheory.Sheaf J A；adj₁ : G₁ ⊣ CategoryTheory.she
afToPresheaf J A；CategoryTheory.Functor Cᵒᵖ B；CategoryTheory.Sheaf J B；adj₂ : G₂
 ⊣ CategoryTheory.sheafToPresheaf J B；CategoryTheory.sheafComposeNatTrans J F ad
j₁ adj₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.GrothendieckTopology.preservesSheafification_iff_of_adjun
ctions`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTh
eory.GrothendieckTopology C) {A : Type u_1}   {B : Type u_2} [inst_1…
· 使用定理 `CategoryTheory.NatTrans.isIso_iff_isIso_app`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category
.{v₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.GrothendieckTopology.W_iff_isIso_map_of_adjunction`：W_iff
_isIso_map_of_adjunction (adj : G ⊣ sheafToPresheaf J A) {P₁ P₂ : Cᵒᵖ ⥤ A} (f : 
P₁ ⟶ P₂) : J.W f ↔ IsIso (G.map f)
· 使用引理 `CategoryTheory.GrothendieckTopology.W_sheafToPresheaf_map_iff_isIso`：W_s
heafToPresheaf_map_iff_isIso {F₁ F₂ : Sheaf J A} (φ : F₁ ⟶ F₂) : J.W ((sheafToPr
esheaf J A).map φ) ↔ IsIso φ
· 使用引理 `CategoryTheory.sheafComposeNatTrans_fac`：sheafComposeNatTrans_fac (P : C
ᵒᵖ ⥤ A) : adj₂.unit.app (P ⋙ F) ≫ (sheafToPresheaf J B).map ((sheafComposeNatTra
ns J F adj₁ adj₂).app P) = wh…
· 使用引理 `CategoryTheory.MorphismProperty.precomp_iff`：precomp_iff [W.RespectsLeft
 W'] [W.HasOfPrecompProperty W'] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W' f)
 : W (f ≫ g) ↔ W g
· 使用定理 `CategoryTheory.MorphismProperty.Respects.toRespectsLeft`：∀ {C : Type u} 
{inst : CategoryTheory.CategoryStruct.{v, u} C} {P Q : CategoryTheory.MorphismPr
operty C}   [self : P.Respects Q], P.Respects…
· 使用定理 `CategoryTheory.MorphismProperty.instRespectsOfIsStableUnderComposition`：
∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (W : CategoryTheory.Mor
phismProperty C)   [W.IsStableUnderComposition], W.Respects …
· 使用定理 `CategoryTheory.MorphismProperty.HasTwoOutOfThreeProperty.toIsStableUnder
Composition`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : Categ
oryTheory.MorphismProperty C}   [self : W.HasTwoOutOfThreeProperty], W.Is…
· 使用定理 `CategoryTheory.ObjectProperty.instHasTwoOutOfThreePropertyIsLocal`：∀ {C 
: Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (P : CategoryTheory.Ob
jectProperty C),   P.isLocal.HasTwoOutOfThreeProperty
· 使用定理 `CategoryTheory.MorphismProperty.HasTwoOutOfThreeProperty.toHasOfPrecompP
roperty`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryT
heory.MorphismProperty C}   [self : W.HasTwoOutOfThreeProperty], W.Ha…
· 使用引理 `CategoryTheory.GrothendieckTopology.W_adj_unit_app`：W_adj_unit_app (adj 
: G ⊣ sheafToPresheaf J A) (P : Cᵒᵖ ⥤ A) : J.W (adj.unit.app P)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma GrothendieckTopology.preservesSheafification_iff_of_adjunctions_of_hasSheafCompose :
    J.PreservesSheafification F ↔ IsIso (sheafComposeNatTrans J F adj₁ adj₂) := by
  rw [J.preservesSheafification_iff_of_adjunctions F adj₁ adj₂,
    NatTrans.isIso_iff_isIso_app]
  apply forall_congr'
  intro P
  rw [← J.W_iff_isIso_map_of_adjunction adj₂, ← J.W_sheafToPresheaf_map_iff_isIso,
    ← sheafComposeNatTrans_fac J F adj₁ adj₂,
    (W _).precomp_iff _ _ (J.W_adj_unit_app adj₂ (P ⋙ F))]

variable [J.PreservesSheafification F]
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso (sheafComposeNatTrans J F adj₁ adj₂) := by
  rw [← J.preservesSheafification_iff_of_adjunctions_of_hasSheafCompose]
  infer_instance

/-- The canonical natural isomorphism
`(whiskeringRight Cᵒᵖ A B).obj F ⋙ G₂ ≅ G₁ ⋙ sheafCompose J F`
when `F : A ⥤ B` preserves sheafification, and that `G₁` and `G₂` are
left adjoints to the forget functors `sheafToPresheaf`. -/
/-
**CategoryTheory.sheafComposeNatIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：sheafComposeNatIso : (whiskeringRight Cᵒᵖ A B).obj F ⋙ G₂ ≅ G₁ ⋙ sheafComp
ose J F
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.instIsIsoFunctorOppositeSheafSheafComposeNatTrans`：∀ {C :
 Type u} [inst : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.Grothendi
eckTopology C) {A : Type u_1}   {B : Type u_2} [inst_1…

--- 原说明 ---
The canonical natural isomorphism
`(whiskeringRight Cᵒᵖ A B).obj F ⋙ G₂ ≅ G₁ ⋙ sheafCompose J F`
when `F : A ⥤ B` preserves sheafification, and that `G₁` and `G₂` are
left adjoints to the forget functors `sheafToPresheaf`.
-/
noncomputable def sheafComposeNatIso :
    (whiskeringRight Cᵒᵖ A B).obj F ⋙ G₂ ≅ G₁ ⋙ sheafCompose J F :=
  asIso (sheafComposeNatTrans J F adj₁ adj₂)

end HasSheafCompose

end

section HasSheafCompose

variable [HasWeakSheafify J A] [HasWeakSheafify J B] [J.HasSheafCompose F]
  [J.PreservesSheafification F] (P : Cᵒᵖ ⥤ A)

/-- The canonical isomorphism `sheafify J (P ⋙ F) ≅ sheafify J P ⋙ F` when
`F` preserves the sheafification. -/
/-
**CategoryTheory.sheafifyComposeIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：sheafifyComposeIso : sheafify J (P ⋙ F) ≅ sheafify J P ⋙ F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism `sheafify J (P ⋙ F) ≅ sheafify J P ⋙ F` when
`F` preserves the sheafification.
-/
noncomputable def sheafifyComposeIso :
    sheafify J (P ⋙ F) ≅ sheafify J P ⋙ F :=
  (sheafToPresheaf J B).mapIso
    ((sheafComposeNatIso J F (sheafificationAdjunction J A) (sheafificationAdjunction J B)).app P)

@[reassoc (attr := simp)]
/-
**CategoryTheory.sheafComposeIso_hom_fac** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry`。
形式化陈述：sheafComposeIso_hom_fac : toSheafify J (P ⋙ F) ≫ (sheafifyComposeIso J F P
).hom = whiskerRight (toSheafify J P) F
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.sheafComposeNatTrans_fac`：sheafComposeNatTrans_fac (P : C
ᵒᵖ ⥤ A) : adj₂.unit.app (P ⋙ F) ≫ (sheafToPresheaf J B).map ((sheafComposeNatTra
ns J F adj₁ adj₂).app P) = wh…
-/
lemma sheafComposeIso_hom_fac :
    toSheafify J (P ⋙ F) ≫ (sheafifyComposeIso J F P).hom =
      whiskerRight (toSheafify J P) F :=
  sheafComposeNatTrans_fac J F (sheafificationAdjunction J A) (sheafificationAdjunction J B) P

@[reassoc (attr := simp)]
/-
**CategoryTheory.sheafComposeIso_inv_fac** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheo
ry`。
形式化陈述：sheafComposeIso_inv_fac : whiskerRight (toSheafify J P) F ≫ (sheafifyCompo
seIso J F P).inv = toSheafify J (P ⋙ F)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.sheafComposeIso_hom_fac`：sheafComposeIso_hom_fac : toShea
fify J (P ⋙ F) ≫ (sheafifyComposeIso J F P).hom = whiskerRight (toSheafify J P) 
F
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma sheafComposeIso_inv_fac :
    whiskerRight (toSheafify J P) F ≫ (sheafifyComposeIso J F P).inv =
      toSheafify J (P ⋙ F) := by
  rw [← sheafComposeIso_hom_fac, assoc, Iso.hom_inv_id, comp_id]

end HasSheafCompose

namespace GrothendieckTopology

section

variable {D E : Type*} [Category* D] [Category* E] (F : D ⥤ E)
  [∀ (J : MulticospanShape.{max v u, max v u}), HasLimitsOfShape (WalkingMulticospan J) D]
  [∀ (J : MulticospanShape.{max v u, max v u}), HasLimitsOfShape (WalkingMulticospan J) E]
  [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]
  [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ E]
  [∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ F]
  [∀ (X : C) (W : J.Cover X) (P : Cᵒᵖ ⥤ D), PreservesLimit (W.index P).multicospan F]
  {FD : D → D → Type*} {CD : D → Type*} {FE : E → E → Type*} {CE : E → Type*}
  [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [∀ X Y, FunLike (FE X Y) (CE X) (CE Y)]
  [instCCD : ConcreteCategory D FD] [instCCE : ConcreteCategory E FE]
  [∀ X, PreservesColimitsOfShape (Cover J X)ᵒᵖ (forget D)]
  [∀ X, PreservesColimitsOfShape (Cover J X)ᵒᵖ (forget E)]
  [PreservesLimitsOfSize.{max v u, max v u} (forget D)]
  [PreservesLimitsOfSize.{max v u, max v u} (forget E)]
  [(forget D).ReflectsIsomorphisms] [(forget E).ReflectsIsomorphisms]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include instCCD instCCE in
/-
**CategoryTheory.GrothendieckTopology.sheafToPresheaf_map_sheafComposeNatTrans_e
q_sheafifyCompIso_inv** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.GrothendieckTopo
logy`。
形式化陈述：sheafToPresheaf_map_sheafComposeNatTrans_eq_sheafifyCompIso_inv (P : Cᵒᵖ ⥤
 D) : (sheafToPresheaf J E).map ((sheafComposeNatTrans J F (plusPlusAdjunction J
 D) (plusPlusAdjunction J E)).app P) = (sheafifyCompIso J F P).inv
参数：P : Cᵒᵖ ⥤ D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfSize.preservesLimitsOfShape`：∀ {C
 : Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : 
CategoryTheory.Category.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.instHasLimitOfHasLimitsOfShape`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheory.Ca
tegory.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.hasSheafCompose_of_preservesMulticospan`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {A : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} A]   {B : Type u₃} [ins…
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.GrothendieckTopology.HasSheafCompose.isSheaf`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {A : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} A}   {B : Type u₃} {ins…
· 使用定理 `CategoryTheory.GrothendieckTopology.sheafify_isSheaf`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] (J : CategoryTheory.GrothendieckTopology 
C) {D : Type w}   [inst_1 : CategoryTheory…
· 使用引理 `CategoryTheory.Adjunction.mkOfHomEquiv_homEquiv`：mkOfHomEquiv_homEquiv (
adj : CoreHomEquiv F G) : (mkOfHomEquiv adj).homEquiv = adj.homEquiv
· 使用定理 `CategoryTheory.GrothendieckTopology.sheafifyCompIso_inv_eq_sheafifyLift`
：sheafifyCompIso_inv_eq_sheafifyLift : (J.sheafifyCompIso F P).inv = J.sheafifyL
ift (whiskerRight (J.toSheafify P) F) (HasSheafCompose.isShea…
· 使用定理 `CategoryTheory.GrothendieckTopology.toSheafify_sheafifyLift`：toSheafify_
sheafifyLift {P Q : Cᵒᵖ ⥤ D} (η : P ⟶ Q) (hQ : Presheaf.IsSheaf J Q) : J.toSheaf
ify P ≫ sheafifyLift J η hQ = η
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.sheafComposeNatTrans_fac`：sheafComposeNatTrans_fac (P : C
ᵒᵖ ⥤ A) : adj₂.unit.app (P ⋙ F) ≫ (sheafToPresheaf J B).map ((sheafComposeNatTra
ns J F adj₁ adj₂).app P) = wh…
-/
lemma sheafToPresheaf_map_sheafComposeNatTrans_eq_sheafifyCompIso_inv (P : Cᵒᵖ ⥤ D) :
    (sheafToPresheaf J E).map
      ((sheafComposeNatTrans J F (plusPlusAdjunction J D) (plusPlusAdjunction J E)).app P) =
      (sheafifyCompIso J F P).inv := by
  suffices (sheafComposeNatTrans J F (plusPlusAdjunction J D) (plusPlusAdjunction J E)).app P =
    ⟨(sheafifyCompIso J F P).inv⟩ by
    rw [this]
    rfl
  apply ((plusPlusAdjunction J E).homEquiv _ _).injective
  convert! sheafComposeNatTrans_fac J F (plusPlusAdjunction J D) (plusPlusAdjunction J E) P
  dsimp [plusPlusAdjunction]
  simp

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.GrothendieckTopology.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.GrothendieckTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P : Cᵒᵖ ⥤ D) :
    IsIso ((sheafComposeNatTrans J F (plusPlusAdjunction J D) (plusPlusAdjunction J E)).app P) := by
  rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf J E),
    sheafToPresheaf_map_sheafComposeNatTrans_eq_sheafifyCompIso_inv]
  infer_instance
/-
**CategoryTheory.GrothendieckTopology.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.GrothendieckTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso (sheafComposeNatTrans J F (plusPlusAdjunction J D) (plusPlusAdjunction J E)) :=
  NatIso.isIso_of_isIso_app _
/-
**CategoryTheory.GrothendieckTopology.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.GrothendieckTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PreservesSheafification J F := by
  rw [preservesSheafification_iff_of_adjunctions_of_hasSheafCompose _ _
    (plusPlusAdjunction J D) (plusPlusAdjunction J E)]
  infer_instance

end

/-
**CategoryTheory.GrothendieckTopology.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.GrothendieckTopology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {D : Type*} [Category.{max v u} D] {FD : D → D → Type*} {CD : D → Type (max v u)}
    [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory.{max v u} D FD]
    [PreservesLimits (forget D)]
    [∀ X : C, HasColimitsOfShape (J.Cover X)ᵒᵖ D]
    [∀ X : C, PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget D)]
    [∀ (J : MulticospanShape.{max v u, max v u}),
      Limits.HasLimitsOfShape (Limits.WalkingMulticospan J) D]
    [(forget D).ReflectsIsomorphisms] : PreservesSheafification J (forget D) :=
  inferInstance

end GrothendieckTopology

end CategoryTheory

