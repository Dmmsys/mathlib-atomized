/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Cartesian closed functors

Define the exponential comparison morphisms for a functor which preserves binary products, and use
them to define a Cartesian closed functor: one which (naturally) preserves exponentials.

Define the Frobenius morphism, and show it is an isomorphism iff the exponential comparison is an
isomorphism.

## TODO
Some of the results here are true more generally for closed objects and for closed monoidal
categories, and these could be generalised.

## References
https://ncatlab.org/nlab/show/cartesian+closed+functor
https://ncatlab.org/nlab/show/Frobenius+reciprocity

## Tags
Frobenius reciprocity, Cartesian closed functor

-/

@[expose] public section


noncomputable section

namespace CategoryTheory

open Category MonoidalClosed MonoidalCategory CartesianMonoidalCategory TwoSquare

universe v u u'

variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v} D]
variable [CartesianMonoidalCategory C] [CartesianMonoidalCategory D]
variable (F : C ⥤ D) {L : D ⥤ C}

/-- The Frobenius morphism for an adjunction `L ⊣ F` at `A` is given by the morphism

    L(FA ⨯ B) ⟶ LFA ⨯ LB ⟶ A ⨯ LB

natural in `B`, where the first morphism is the product comparison and the latter uses the counit
of the adjunction.

We will show that if `C` and `D` are Cartesian closed, then this morphism is an isomorphism for all
`A` iff `F` is a Cartesian closed functor, i.e. it preserves exponentials.
-/
/-
**CategoryTheory.frobeniusMorphism** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：frobeniusMorphism (h : L ⊣ F) (A : C) : TwoSquare (tensorLeft (F.obj A)) L
 L (tensorLeft A)
参数：h : L ⊣ F；A : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Frobenius morphism for an adjunction `L ⊣ F` at `A` is given by the morphism

    L(FA ⨯ B) ⟶ LFA ⨯ LB ⟶ A ⨯ LB

natural in `B`, where the first morphism is the product comparison and the latte
r uses the counit
of the adjunction.

We will show that if `C` and `D` are Cartesian closed, then this morphism is an 
isomorphism for all
`A` iff `F` is a Cartesian closed functor, i.e. it preserves exponentials.
-/
def frobeniusMorphism (h : L ⊣ F) (A : C) : TwoSquare (tensorLeft (F.obj A)) L L (tensorLeft A) :=
  prodComparisonNatTrans L (F.obj A) ≫
    Functor.whiskerLeft _ ((curriedTensor C).map (h.counit.app _))

/-- If `F` is full and faithful and has a left adjoint `L` which preserves binary products, then the
Frobenius morphism is an isomorphism.
-/
/-
**CategoryTheory.frobeniusMorphism_iso_of_preserves_binary_products** 是 Mathlib 
中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：frobeniusMorphism_iso_of_preserves_binary_products (h : L ⊣ F) (A : C) [Li
mits.PreservesLimitsOfShape (Discrete Limits.WalkingPair) L] [F.Full] [F.Faithfu
l] : IsIso (frobeniusMorphism F h A).natTrans
参数：h : L ⊣ F；A : C；Discrete Limits.WalkingPair。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatIso.isIso_app_of_isIso`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.instIsIsoFunctorProdComparisonN
atTransOfProdComparison`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C
] [inst_1 : CategoryTheory.CartesianMonoidalCategory C]   {D : Type u₁} [inst_2 
: Cat…
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.Adjunction.instIsIsoAppCounitOfFullOfFaithful`：∀ {C : Typ
e u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Catego
ryTheory.Category.{v₂, u₂} D]   {L : CategoryTheor…
· 使用定理 `CategoryTheory.NatIso.isIso_of_isIso_app`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…

--- 原说明 ---
If `F` is full and faithful and has a left adjoint `L` which preserves binary pr
oducts, then the
Frobenius morphism is an isomorphism.
-/
instance frobeniusMorphism_iso_of_preserves_binary_products (h : L ⊣ F) (A : C)
    [Limits.PreservesLimitsOfShape (Discrete Limits.WalkingPair) L] [F.Full] [F.Faithful] :
    IsIso (frobeniusMorphism F h A).natTrans :=
  suffices ∀ (X : D), IsIso ((frobeniusMorphism F h A).natTrans.app X) from
    NatIso.isIso_of_isIso_app _
  fun B ↦ by dsimp [frobeniusMorphism]; infer_instance

variable [MonoidalClosed C] [MonoidalClosed D]
variable [Limits.PreservesLimitsOfShape (Discrete Limits.WalkingPair) F]

/-- The exponential comparison map.
`F` is a Cartesian closed functor if this is an iso for all `A`.
-/
/-
**CategoryTheory.expComparison** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：expComparison (A : C) : TwoSquare (ihom A) F F (ihom (F.obj A))
参数：A : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The exponential comparison map.
`F` is a Cartesian closed functor if this is an iso for all `A`.
-/
def expComparison (A : C) : TwoSquare (ihom A) F F (ihom (F.obj A)) :=
  mateEquiv (ihom.adjunction A) (ihom.adjunction (F.obj A)) (prodComparisonNatIso F A).inv

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.expComparison_ev** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：expComparison_ev (A B : C) : F.obj A ◁ ((expComparison F A).natTrans.app B
) ≫ (ihom.ev (F.obj A)).app (F.obj B) = inv (prodComparison F _ _) ≫ F.map ((iho
m.ev _).app _)
参数：A B : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `CategoryTheory.IsIso.inv_eq_of_hom_inv_id`：inv_eq_of_hom_inv_id {f : X ⟶
 Y} [IsIso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g = 𝟙 X) : inv f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatIso.isIso_app_of_isIso`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.prodComparisonNatTrans_app`：∀ {
C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.C
artesianMonoidalCategory C]   {D : Type u₁} [inst_2 : Cat…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.prodComparisonNatIso_inv`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Car
tesianMonoidalCategory C]   {D : Type u₁} [inst_2 : Cat…
· 使用定理 `CategoryTheory.NatIso.isIso_inv_app`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.inv.congr_simp`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (f f_1 : X ⟶ Y) (e_f : f = f_1)   [I : CategoryTheory.
IsIso f], CategoryT…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.mateEquiv_counit`：mateEquiv_counit (α : TwoSquare G L₁ L₂
 H) (d : D) : L₂.map ((mateEquiv adj₁ adj₂ α).app _) ≫ adj₂.counit.app _ = α.app
 _ ≫ H.map (adj₁.coun…
-/
theorem expComparison_ev (A B : C) :
    F.obj A ◁ ((expComparison F A).natTrans.app B) ≫ (ihom.ev (F.obj A)).app (F.obj B) =
      inv (prodComparison F _ _) ≫ F.map ((ihom.ev _).app _) := by
  convert! mateEquiv_counit _ _ (prodComparisonNatIso F A).inv B using 2
  apply IsIso.inv_eq_of_hom_inv_id -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): was `ext`
  simp only [prodComparisonNatTrans_app, prodComparisonNatIso_inv, NatIso.isIso_inv_app,
    IsIso.hom_inv_id]

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.coev_expComparison** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：coev_expComparison (A B : C) : F.map ((ihom.coev A).app B) ≫ (expCompariso
n F A).natTrans.app (A otimes B) = (ihom.coev _).app (F.obj B) ≫ (ihom (F.obj A)
).map (inv (prodComparison F A B))
参数：A B : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `CategoryTheory.IsIso.inv_eq_of_hom_inv_id`：inv_eq_of_hom_inv_id {f : X ⟶
 Y} [IsIso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g = 𝟙 X) : inv f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatIso.isIso_app_of_isIso`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.prodComparisonNatTrans_app`：∀ {
C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.C
artesianMonoidalCategory C]   {D : Type u₁} [inst_2 : Cat…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.prodComparisonNatIso_inv`：∀ {C 
: Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Car
tesianMonoidalCategory C]   {D : Type u₁} [inst_2 : Cat…
· 使用定理 `CategoryTheory.NatIso.isIso_inv_app`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.inv.congr_simp`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (f f_1 : X ⟶ Y) (e_f : f = f_1)   [I : CategoryTheory.
IsIso f], CategoryT…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.unit_mateEquiv`：unit_mateEquiv (α : TwoSquare G L₁ L₂ H) 
(c : C) : G.map (adj₁.unit.app c) ≫ (mateEquiv adj₁ adj₂ α).app _ = adj₂.unit.ap
p _ ≫ R₂.map (α.app…
-/
theorem coev_expComparison (A B : C) :
    F.map ((ihom.coev A).app B) ≫ (expComparison F A).natTrans.app (A ⊗ B) =
      (ihom.coev _).app (F.obj B) ≫ (ihom (F.obj A)).map (inv (prodComparison F A B)) := by
  convert! unit_mateEquiv _ _ (prodComparisonNatIso F A).inv B using 3
  apply IsIso.inv_eq_of_hom_inv_id -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): was `ext`
  simp
/-
**CategoryTheory.uncurry_expComparison** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
`。
形式化陈述：uncurry_expComparison (A B : C) : MonoidalClosed.uncurry ((expComparison F
 A).natTrans.app B) = inv (prodComparison F _ _) ≫ F.map ((ihom.ev _).app _)
参数：A B : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalClosed.uncurry_eq`：uncurry_eq (g : Y ⟶ A ⟶[C] X) 
: uncurry g = (A ◁ g) ≫ (ihom.ev A).app X
· 使用定理 `CategoryTheory.expComparison_ev`：expComparison_ev (A B : C) : F.obj A ◁ 
((expComparison F A).natTrans.app B) ≫ (ihom.ev (F.obj A)).app (F.obj B) = inv (
prodComparison F _ _)…
-/
theorem uncurry_expComparison (A B : C) :
    MonoidalClosed.uncurry ((expComparison F A).natTrans.app B) =
      inv (prodComparison F _ _) ≫ F.map ((ihom.ev _).app _) := by
  rw [uncurry_eq, expComparison_ev]

set_option backward.defeqAttrib.useBackward true in
/-- The exponential comparison map is natural in `A`. -/
/-
**CategoryTheory.expComparison_whiskerLeft** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory`。
形式化陈述：expComparison_whiskerLeft {A A' : C} (f : A' ⟶ A) : (expComparison F A).wh
iskerBottom (MonoidalClosed.pre (F.map f)) = (expComparison F A').whiskerTop (Mo
noidalClosed.pre f)
参数：f : A' ⟶ A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `CategoryTheory.mateEquiv_conjugateEquiv_vcomp`：mateEquiv_conjugateEquiv_
vcomp {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C} {L₃ : C ⥤ D} {R₃ : D ⥤
 C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R…
· 使用定理 `CategoryTheory.conjugateEquiv_mateEquiv_vcomp`：conjugateEquiv_mateEquiv_
vcomp {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : A ⥤ B} {R₂ : B ⥤ A} {L₃ : C ⥤ D} {R₃ : D ⥤
 C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.NatIso.isIso_app_of_isIso`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.NatIso.isIso_inv_app`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.prodComparison_inv_natural_whis
kerRight`：prodComparison_inv_natural_whiskerRight (f : A ⟶ A') [IsIso (prodCompa
rison F A' B)] : inv (prodComparison F A B) ≫ F.map (f ▷ B) = (F.map f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.IsIso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : X ⟶ Z), CategoryT…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The exponential comparison map is natural in `A`.
-/
theorem expComparison_whiskerLeft {A A' : C} (f : A' ⟶ A) :
    (expComparison F A).whiskerBottom (MonoidalClosed.pre (F.map f)) =
      (expComparison F A').whiskerTop (MonoidalClosed.pre f) := by
  unfold expComparison MonoidalClosed.pre
  have vcomp1 := mateEquiv_conjugateEquiv_vcomp
    (ihom.adjunction A) (ihom.adjunction (F.obj A)) (ihom.adjunction (F.obj A'))
    ((prodComparisonNatIso F A).inv) (((curriedTensor D).map (F.map f)))
  have vcomp2 := conjugateEquiv_mateEquiv_vcomp
    (ihom.adjunction A) (ihom.adjunction A') (ihom.adjunction (F.obj A'))
    (((curriedTensor C).map f)) ((prodComparisonNatIso F A').inv)
  rw [← vcomp1, ← vcomp2]
  unfold TwoSquare.whiskerLeft TwoSquare.whiskerRight
  congr 1
  apply congr_arg
  ext B
  simp only [Functor.comp_obj, curriedTensor_obj_obj, prodComparisonNatIso_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app, curriedTensor_map_app, NatIso.isIso_inv_app,
    Functor.whiskerRight_app, IsIso.eq_inv_comp, prodComparisonNatTrans_app]
  rw [← prodComparison_inv_natural_whiskerRight F f]
  simp

/-- The functor `F` is Cartesian closed (i.e. preserves exponentials) if each natural transformation
`expComparison F A` is an isomorphism
-/
/-
**CategoryTheory.MonoidalClosedFunctor** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheo
ry`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {D : Type
 u'} →       [inst_1 : CategoryTheory.Category.{v, u'} D] →         [inst_2 : Ca
tegoryTheory.CartesianMonoidalCategory C] →           [inst_3 : CategoryTheory.C
artesianMonoidalCategory D] →             (F : CategoryTheory.Functor C D) →    
           [CategoryTheory.MonoidalClosed C] →                 [CategoryTheory.M
onoidalClosed D] →                   [CategoryTheory.Limits.PreservesLimitsOfSha
pe                         (CategoryTheory.Discrete CategoryTheory.Limits.Walkin
gPair) F] →                     Prop
参数：F : CategoryTheory.Functor C D；CategoryTheory.Discrete CategoryTheory.Limits.
WalkingPair。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `F` is Cartesian closed (i.e. preserves exponentials) if each natura
l transformation
`expComparison F A` is an isomorphism
-/
class MonoidalClosedFunctor : Prop where
  comparison_iso : ∀ A, IsIso (expComparison F A).natTrans

attribute [instance] MonoidalClosedFunctor.comparison_iso

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.frobeniusMorphism_mate** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y`。
形式化陈述：frobeniusMorphism_mate (h : L ⊣ F) (A : C) : conjugateEquiv (h.comp (ihom.
adjunction A)) ((ihom.adjunction (F.obj A)).comp h) (frobeniusMorphism F h A).na
tTrans = (expComparison F A).natTrans
参数：h : L ⊣ F；A : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.iterated_mateEquiv_conjugateEquiv`：iterated_mateEquiv_con
jugateEquiv (α : TwoSquare F₁ L₁ L₂ F₂) : (mateEquiv adj₄ adj₃ (mateEquiv adj₁ a
dj₂ α)).natTrans = conjugateEquiv (adj…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `CategoryTheory.TwoSquare.ext`：ext (w w' : TwoSquare T L R B) (h : forall
 (X : C₁), w.natTrans.app X = w'.natTrans.app X) : w = w'
· 使用定理 `CategoryTheory.NatIso.isIso_app_of_isIso`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.whiskerRight_comp`：whiskerRight_comp {G H K : C ⥤
 D} (α : G ⟶ H) (β : H ⟶ K) (F : D ⥤ E) : whiskerRight (α ≫ β) F = whiskerRight 
α F ≫ whiskerRight β F
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.NatIso.isIso_inv_app`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.IsIso.eq_inv_of_inv_hom_id`：∀ {C : Type u} [inst : Catego
ryTheory.Category.{v, u} C] {X Y : C} {f : Y ⟶ X} [inst_1 : CategoryTheory.IsIso
 f]   {g : X ⟶ Y}, CategoryTheo…
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.prodComparison_natural_whiskerL
eft`：prodComparison_natural_whiskerLeft (g : B ⟶ B') : F.map (A ◁ g) ≫ prodCompa
rison F A B' = prodComparison F A B ≫ (F.obj A ◁ F.map g)
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.prodComparison_natural_whiskerR
ight_assoc`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : C
ategoryTheory.CartesianMonoidalCategory C]   {D : Type u₁} [inst_2 : Cat…
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.prodComparison_comp`：prodCompar
ison_comp : prodComparison (F ⋙ G) A B = G.map (prodComparison F A B) ≫ prodComp
arison G (F.obj A) (F.obj B)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.CartesianMonoidalCategory.lift_whiskerRight_assoc`：∀ {C :
 Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Cart
esianMonoidalCategory C]   {X Y Z W : C} (f : X ⟶ Y) (…
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_whiskerLeft`：lift_whiskerL
eft {X Y Z W : C} (f : X ⟶ Y) (g : X ⟶ Z) (h : Z ⟶ W) : lift f g ≫ (Y ◁ h) = lif
t f (g ≫ h)
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.comp_lift`：comp_lift {V W X Y :
 C} (f : V ⟶ W) (g : W ⟶ X) (h : W ⟶ Y) : f ≫ lift g h = lift (f ≫ g) (f ≫ h)
· 使用定理 `CategoryTheory.Adjunction.unit_naturality_assoc`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.right_triangle_components`：∀ {C : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.
Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用引理 `CategoryTheory.CartesianMonoidalCategory.lift_fst_snd`：lift_fst_snd {X Y
 : C} : lift (fst X Y) (snd X Y) = 𝟙 (X otimes Y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem frobeniusMorphism_mate (h : L ⊣ F) (A : C) :
    conjugateEquiv (h.comp (ihom.adjunction A)) ((ihom.adjunction (F.obj A)).comp h)
        (frobeniusMorphism F h A).natTrans = (expComparison F A).natTrans := by
  unfold expComparison frobeniusMorphism
  have conjeq := iterated_mateEquiv_conjugateEquiv h h
    (ihom.adjunction (F.obj A)) (ihom.adjunction A)
    (prodComparisonNatTrans L (F.obj A) ≫
      Functor.whiskerLeft L ((curriedTensor C).map (h.counit.app A)))
  rw [← conjeq]
  congr 1
  apply congr_arg
  ext B
  unfold mateEquiv
  simp only [Functor.comp_obj, curriedTensor_obj_obj, Equiv.coe_fn_mk, Functor.whiskerRight_comp,
    Functor.whiskerLeft_comp, Category.assoc, NatTrans.comp_app, Functor.id_obj,
    Functor.rightUnitor_inv_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, prodComparisonNatTrans_app,
    curriedTensor_map_app, Functor.comp_map, curriedTensor_obj_map, Functor.leftUnitor_hom_app,
    Category.comp_id, Category.id_comp, prodComparisonNatIso_inv, NatIso.isIso_inv_app]
  rw [← F.map_comp, ← F.map_comp]
  simp only [Functor.map_comp]
  apply IsIso.eq_inv_of_inv_hom_id
  simp only [Category.assoc]
  rw [prodComparison_natural_whiskerLeft, prodComparison_natural_whiskerRight_assoc]
  slice_lhs 2 3 => rw [← prodComparison_comp]
  simp only [Category.assoc]
  unfold prodComparison
  simp

/--
If the exponential comparison transformation (at `A`) is an isomorphism, then the Frobenius morphism
at `A` is an isomorphism.
-/
/-
**CategoryTheory.frobeniusMorphism_iso_of_expComparison_iso** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory`。
形式化陈述：frobeniusMorphism_iso_of_expComparison_iso (h : L ⊣ F) (A : C) [i : IsIso 
(expComparison F A).natTrans] : IsIso (frobeniusMorphism F h A).natTrans
参数：h : L ⊣ F；A : C；expComparison F A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.conjugateEquiv_of_iso`：conjugateEquiv_of_iso (α : L₂ ⟶ L₁
) [IsIso (conjugateEquiv adj₁ adj₂ α)] : IsIso α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.frobeniusMorphism_mate`：frobeniusMorphism_mate (h : L ⊣ F
) (A : C) : conjugateEquiv (h.comp (ihom.adjunction A)) ((ihom.adjunction (F.obj
 A)).comp h) (frobeniusMorp…

--- 原说明 ---
If the exponential comparison transformation (at `A`) is an isomorphism, then th
e Frobenius morphism
at `A` is an isomorphism.
-/
theorem frobeniusMorphism_iso_of_expComparison_iso (h : L ⊣ F) (A : C)
    [i : IsIso (expComparison F A).natTrans] : IsIso (frobeniusMorphism F h A).natTrans := by
  rw [← frobeniusMorphism_mate F h] at i
  exact @conjugateEquiv_of_iso _ _ _ _ _ _ _ _ _ _ _ i

/--
If the Frobenius morphism at `A` is an isomorphism, then the exponential comparison transformation
(at `A`) is an isomorphism.
-/
/-
**CategoryTheory.expComparison_iso_of_frobeniusMorphism_iso** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory`。
形式化陈述：expComparison_iso_of_frobeniusMorphism_iso (h : L ⊣ F) (A : C) [i : IsIso 
(frobeniusMorphism F h A)] : IsIso (expComparison F A).natTrans
参数：h : L ⊣ F；A : C；frobeniusMorphism F h A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.frobeniusMorphism_mate`：frobeniusMorphism_mate (h : L ⊣ F
) (A : C) : conjugateEquiv (h.comp (ihom.adjunction A)) ((ihom.adjunction (F.obj
 A)).comp h) (frobeniusMorp…

--- 原说明 ---
If the Frobenius morphism at `A` is an isomorphism, then the exponential compari
son transformation
(at `A`) is an isomorphism.
-/
theorem expComparison_iso_of_frobeniusMorphism_iso (h : L ⊣ F) (A : C)
    [i : IsIso (frobeniusMorphism F h A)] : IsIso (expComparison F A).natTrans := by
  rw [← frobeniusMorphism_mate F h]; infer_instance

open Limits in
/-- If `F` is full and faithful, and has a left adjoint which preserves binary products, then it is
Cartesian closed.

TODO: Show the converse, that if `F` is Cartesian closed and its left adjoint preserves binary
products, then it is full and faithful.
-/
/-
**CategoryTheory.cartesianClosedFunctorOfLeftAdjointPreservesBinaryProducts** 是 
Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：cartesianClosedFunctorOfLeftAdjointPreservesBinaryProducts (h : L ⊣ F) [F.
Full] [F.Faithful] [PreservesLimitsOfShape (Discrete WalkingPair) L] : MonoidalC
losedFunctor F where comparison_iso _
参数：h : L ⊣ F；Discrete WalkingPair。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.expComparison_iso_of_frobeniusMorphism_iso`：expComparison
_iso_of_frobeniusMorphism_iso (h : L ⊣ F) (A : C) [i : IsIso (frobeniusMorphism 
F h A)] : IsIso (expComparison F A).natTrans

--- 原说明 ---
If `F` is full and faithful, and has a left adjoint which preserves binary produ
cts, then it is
Cartesian closed.

TODO: Show the converse, that if `F` is Cartesian closed and its left adjoint pr
eserves binary
products, then it is full and faithful.
-/
theorem cartesianClosedFunctorOfLeftAdjointPreservesBinaryProducts (h : L ⊣ F) [F.Full] [F.Faithful]
    [PreservesLimitsOfShape (Discrete WalkingPair) L] : MonoidalClosedFunctor F where
  comparison_iso _ := expComparison_iso_of_frobeniusMorphism_iso F h _

end CategoryTheory

