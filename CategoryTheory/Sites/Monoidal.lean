/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Localization.Monoidal.Braided
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.SheafHom

/-!
# Monoidal category structure on categories of sheaves

If `A` is a closed braided category with suitable limits,
and `J` is a Grothendieck topology with `HasWeakSheafify J A`,
then `Sheaf J A` can be equipped with a monoidal category
structure. This is not made an instance as in some cases
it may conflict with monoidal structure deduced from
chosen finite products.

## TODO

* show that the monoidal category structure on sheaves is closed,
  and that the internal hom can be defined in such a way that the
  underlying presheaf is the internal hom in the category of presheaves.
  Note that a `MonoidalClosed` instance on sheaves can already be obtained
  abstractly using the material in `CategoryTheory.Monoidal.Braided.Reflection`.

-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {A : Type u₃} [Category.{v₃} A] [MonoidalCategory A]

open Opposite Limits MonoidalCategory MonoidalClosed Enriched.FunctorCategory

namespace Presheaf

variable [MonoidalClosed A]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Relation between `functorEnrichedHom` and `presheafHom`. -/
/-
**CategoryTheory.Presheaf.functorEnrichedHomCoyonedaObjEquiv** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.Presheaf`。
形式化陈述：functorEnrichedHomCoyonedaObjEquiv (M : A) (F G : Cᵒᵖ ⥤ A) [HasFunctorEnri
chedHom A F G] (X : C) : (functorEnrichedHom A F G ⋙ coyoneda.obj (op M)).obj (o
p X) ≃ (presheafHom (F otimes (Functor.const _).obj M) G).obj (op X) where toFun
 f
参数：M : A；F G : Cᵒᵖ ⥤ A；X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Relation between `functorEnrichedHom` and `presheafHom`.
-/
noncomputable def functorEnrichedHomCoyonedaObjEquiv (M : A) (F G : Cᵒᵖ ⥤ A)
    [HasFunctorEnrichedHom A F G] (X : C) :
    (functorEnrichedHom A F G ⋙ coyoneda.obj (op M)).obj (op X) ≃
    (presheafHom (F ⊗ (Functor.const _).obj M) G).obj (op X) where
  toFun f :=
    { app j := MonoidalClosed.uncurry (f ≫ enrichedHomπ A _ _ (Under.mk j.unop.hom.op))
      naturality j j' φ := by
        dsimp
        rw [tensorHom_id, ← uncurry_natural_right, ← uncurry_pre_app, Category.assoc,
          Category.assoc, ← enrichedOrdinaryCategorySelf_eHomWhiskerRight,
          ← enrichedOrdinaryCategorySelf_eHomWhiskerLeft]
        congr 2
        exact (enrichedHom_condition A (Under.forget (op X) ⋙ F) (Under.forget (op X) ⋙ G)
          (i := Under.mk j.unop.hom.op) (j := Under.mk j'.unop.hom.op)
            (Under.homMk φ.unop.left.op (Quiver.Hom.unop_inj (by simp)))).symm }
  invFun g :=
    end_.lift (fun j ↦ MonoidalClosed.curry (g.app (op (Over.mk j.hom.unop)))) (fun j j' φ ↦ by
      dsimp
      rw [enrichedOrdinaryCategorySelf_eHomWhiskerRight,
        enrichedOrdinaryCategorySelf_eHomWhiskerLeft,
        curry_pre_app, ← curry_natural_right]
      congr 1
      let α : Over.mk j'.hom.unop ⟶ Over.mk j.hom.unop := Over.homMk φ.right.unop
        (Quiver.Hom.op_inj (by simp))
      simpa using! (g.naturality α.op).symm)
  left_inv f := by
    dsimp
    ext j
    dsimp
    simp only [curry_uncurry, end_.lift_π]
    rfl
  right_inv g := by
    dsimp
    ext j
    dsimp
    simp only [uncurry_curry, end_.lift_π]
    rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Presheaf.functorEnrichedHomCoyonedaObjEquiv_naturality** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.Presheaf`。
形式化陈述：functorEnrichedHomCoyonedaObjEquiv_naturality {M : A} {F G : Cᵒᵖ ⥤ A} {X Y
 : C} (f : X ⟶ Y) [HasFunctorEnrichedHom A F G] (y : (functorEnrichedHom A F G ⋙
 coyoneda.obj (op M)).obj (op Y)) : functorEnrichedHomCoyonedaObjEquiv M F G X (
y ≫ precompEnrichedHom' _ (Under.map f.op) (Iso.refl _) (Iso.refl _)) = (preshea
fHom (F otimes (Functor.const Cᵒᵖ).obj M) G).map f.op (functorEnrichedHomCoyoned
aObjEquiv M F G Y y)
参数：f : X ⟶ Y；y : (functorEnrichedHom A F G ⋙ coyoneda.obj (op M)).obj (op Y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.end_.lift_π`：∀ {J : Type u} [inst : CategoryTheory
.Category.{v, u} J] {C : Type u'} [inst_1 : CategoryTheory.Category.{v', u'} C] 
  {F : CategoryTheory.F…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CategoryTheory.eHomWhiskerRight_id`：eHomWhiskerRight_id (X Y : C) : eHom
WhiskerRight V (𝟙 X) Y = 𝟙 _
· 使用引理 `CategoryTheory.eHomWhiskerLeft_id`：eHomWhiskerLeft_id (X Y : C) : eHomWh
iskerLeft V X (𝟙 Y) = 𝟙 _
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.NatTrans.mk.congr_simp`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, 
u₂} D]   {F G : CategoryThe…
-/
lemma functorEnrichedHomCoyonedaObjEquiv_naturality
    {M : A} {F G : Cᵒᵖ ⥤ A} {X Y : C} (f : X ⟶ Y)
    [HasFunctorEnrichedHom A F G]
    (y : (functorEnrichedHom A F G ⋙ coyoneda.obj (op M)).obj (op Y)) :
    functorEnrichedHomCoyonedaObjEquiv M F G X
      (y ≫ precompEnrichedHom' _ (Under.map f.op) (Iso.refl _) (Iso.refl _)) =
    (presheafHom (F ⊗ (Functor.const Cᵒᵖ).obj M) G).map f.op
      (functorEnrichedHomCoyonedaObjEquiv M F G Y y) := by
  dsimp
  ext ⟨j⟩
  simp [functorEnrichedHomCoyonedaObjEquiv, presheafHom]
  rfl
/-
**CategoryTheory.Presheaf.isSheaf_functorEnrichedHom** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Presheaf`。
形式化陈述：isSheaf_functorEnrichedHom (F G : Cᵒᵖ ⥤ A) (hG : Presheaf.IsSheaf J G) [Ha
sFunctorEnrichedHom A F G] : Presheaf.IsSheaf J (functorEnrichedHom A F G)
参数：F G : Cᵒᵖ ⥤ A；hG : Presheaf.IsSheaf J G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Presieve.isSheaf_iff_of_nat_equiv`：isSheaf_iff_of_nat_equ
iv : Presieve.IsSheaf J P₁ ↔ Presieve.IsSheaf J P₂
· 使用引理 `CategoryTheory.Presheaf.functorEnrichedHomCoyonedaObjEquiv_naturality`：f
unctorEnrichedHomCoyonedaObjEquiv_naturality {M : A} {F G : Cᵒᵖ ⥤ A} {X Y : C} (
f : X ⟶ Y) [HasFunctorEnrichedHom A F G] (y : (functorEnric…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.isSheaf_iff_isSheaf_of_type`：isSheaf_iff_isSheaf_of_type 
(P : Cᵒᵖ ⥤ Type w) : Presheaf.IsSheaf J P ↔ Presieve.IsSheaf J P
· 使用定理 `CategoryTheory.Presheaf.IsSheaf.hom`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {J : CategoryTheory.GrothendieckTopology C} {A : Type u'} 
  [inst_1 : CategoryTheor…
-/
lemma isSheaf_functorEnrichedHom (F G : Cᵒᵖ ⥤ A) (hG : Presheaf.IsSheaf J G)
    [HasFunctorEnrichedHom A F G] :
    Presheaf.IsSheaf J (functorEnrichedHom A F G) := fun M ↦ by
  rw [Presieve.isSheaf_iff_of_nat_equiv
    (functorEnrichedHomCoyonedaObjEquiv M F G)
    (fun _ _ _ _ ↦ functorEnrichedHomCoyonedaObjEquiv_naturality _ _)]
  rw [← isSheaf_iff_isSheaf_of_type]
  exact Presheaf.IsSheaf.hom (F ⊗ (Functor.const _).obj M) G hG

end Presheaf

namespace GrothendieckTopology

namespace W

variable (J A) in
/-
**CategoryTheory.GrothendieckTopology.W.transport_isMonoidal** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.GrothendieckTopology.W`。
形式化陈述：transport_isMonoidal {D : Type u₂} [Category.{v₂} D] (K : GrothendieckTopo
logy D) (G : D ⥤ C) [G.IsCoverDense J] [G.Full] [G.IsContinuous K J] [(G.sheafPu
shforwardContinuous A K J).EssSurj] [(K.W (A
参数：K : GrothendieckTopology D；G : D ⥤ C；G.sheafPushforwardContinuous A K J。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.GrothendieckTopology.W_inverseImage_whiskeringLeft`：W_inv
erseImage_whiskeringLeft : K.W.inverseImage ((whiskeringLeft Dᵒᵖ Cᵒᵖ A).obj G.op
) = J.W
· 使用定理 `CategoryTheory.MorphismProperty.instIsMonoidalInverseImageOfMonoidalOfRe
spectsIso`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (W : C
ategoryTheory.MorphismProperty C)   [inst_1 : CategoryTheory.MonoidalCa…
· 使用定理 `CategoryTheory.ObjectProperty.instRespectsIsoIsLocal`：∀ {C : Type u_1} [
inst : CategoryTheory.Category.{v_1, u_1} C] (P : CategoryTheory.ObjectProperty 
C),   P.isLocal.RespectsIso
-/
lemma transport_isMonoidal {D : Type u₂} [Category.{v₂} D] (K : GrothendieckTopology D)
    (G : D ⥤ C) [G.IsCoverDense J] [G.Full] [G.IsContinuous K J]
    [(G.sheafPushforwardContinuous A K J).EssSurj] [(K.W (A := A)).IsMonoidal] :
    (J.W (A := A)).IsMonoidal := by
  rw [← J.W_inverseImage_whiskeringLeft K G]
  infer_instance

variable [MonoidalClosed A]
  [∀ (F₁ F₂ : Cᵒᵖ ⥤ A), HasFunctorEnrichedHom A F₁ F₂]
  [∀ (F₁ F₂ : Cᵒᵖ ⥤ A), HasEnrichedHom A F₁ F₂]

open MonoidalClosed.FunctorCategory

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.GrothendieckTopology.W.whiskerLeft** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.GrothendieckTopology.W`。
形式化陈述：whiskerLeft {G₁ G₂ : Cᵒᵖ ⥤ A} {g : G₁ ⟶ G₂} (hg : J.W g) (F : Cᵒᵖ ⥤ A) : J
.W (F ◁ g)
参数：hg : J.W g；F : Cᵒᵖ ⥤ A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Presheaf.isSheaf_functorEnrichedHom`：isSheaf_functorEnric
hedHom (F G : Cᵒᵖ ⥤ A) (hG : Presheaf.IsSheaf J G) [HasFunctorEnrichedHom A F G]
 : Presheaf.IsSheaf J (functorEnrichedHo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Bijective.of_comp_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Bijective f → ∀ (g : γ → α), Function.Bijective 
(f ∘ g) ↔ Function.Bi…
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.MonoidalClosed.curry_natural_left`：curry_natural_left (f 
: X ⟶ X') (g : A otimes X' ⟶ Y) : curry (_ ◁ f ≫ g) = f ≫ curry g
· 使用定理 `Function.Bijective.of_comp_iff`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sor
t u_3} (f : α → β) {g : γ → α},   Function.Bijective g → (Function.Bijective (f 
∘ g) ↔ Function.Bije…
-/
lemma whiskerLeft {G₁ G₂ : Cᵒᵖ ⥤ A} {g : G₁ ⟶ G₂} (hg : J.W g) (F : Cᵒᵖ ⥤ A) :
    J.W (F ◁ g) := fun H h ↦ by
  have := hg _ (Presheaf.isSheaf_functorEnrichedHom F H h)
  rw [← Function.Bijective.of_comp_iff' (f := MonoidalClosed.curry)
    ((ihom.adjunction _).homEquiv _ _).bijective]
  rw [← Function.Bijective.of_comp_iff (g := MonoidalClosed.curry) _
    ((ihom.adjunction _).homEquiv _ _).bijective] at this
  convert! this using 1
  ext α : 1
  dsimp
  rw [curry_natural_left]

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.GrothendieckTopology.W.whiskerRight** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.GrothendieckTopology.W`。
形式化陈述：whiskerRight [BraidedCategory A] {F₁ F₂ : Cᵒᵖ ⥤ A} {f : F₁ ⟶ F₂} (hf : J.W
 f) (G : Cᵒᵖ ⥤ A) : J.W (f ▷ G)
参数：hf : J.W f；G : Cᵒᵖ ⥤ A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `CategoryTheory.ObjectProperty.instRespectsIsoIsLocal`：∀ {C : Type u_1} [
inst : CategoryTheory.Category.{v_1, u_1} C] (P : CategoryTheory.ObjectProperty 
C),   P.isLocal.RespectsIso
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.BraidedCategory.braiding_naturality_left`：∀ {C : Type u} 
{inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.MonoidalCateg
ory C}   [self : CategoryTheory.BraidedCatego…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.GrothendieckTopology.W.whiskerLeft`：whiskerLeft {G₁ G₂ : 
Cᵒᵖ ⥤ A} {g : G₁ ⟶ G₂} (hg : J.W g) (F : Cᵒᵖ ⥤ A) : J.W (F ◁ g)
-/
lemma whiskerRight [BraidedCategory A]
    {F₁ F₂ : Cᵒᵖ ⥤ A} {f : F₁ ⟶ F₂} (hf : J.W f) (G : Cᵒᵖ ⥤ A) :
    J.W (f ▷ G) :=
  (J.W.arrow_mk_iso_iff (Arrow.isoMk (β_ F₁ G) (β_ F₂ G))).2 (hf.whiskerLeft G)
/-
**CategoryTheory.GrothendieckTopology.W.monoidal** 是 Mathlib 中的一个实例，位于命名空间 `Cate
goryTheory.GrothendieckTopology.W`。
形式化陈述：monoidal [BraidedCategory A] : (J.W (A
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.instIsMultiplicativeIsLocal`：∀ {C : Type u
_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (P : CategoryTheory.ObjectProp
erty C),   P.isLocal.IsMultiplicative
· 使用引理 `CategoryTheory.GrothendieckTopology.W.whiskerLeft`：whiskerLeft {G₁ G₂ : 
Cᵒᵖ ⥤ A} {g : G₁ ⟶ G₂} (hg : J.W g) (F : Cᵒᵖ ⥤ A) : J.W (F ◁ g)
· 使用引理 `CategoryTheory.GrothendieckTopology.W.whiskerRight`：whiskerRight [Braide
dCategory A] {F₁ F₂ : Cᵒᵖ ⥤ A} {f : F₁ ⟶ F₂} (hf : J.W f) (G : Cᵒᵖ ⥤ A) : J.W (f
 ▷ G)
-/
instance monoidal [BraidedCategory A] : (J.W (A := A)).IsMonoidal where
  whiskerLeft F _ _ _ hg := hg.whiskerLeft F
  whiskerRight _ hf G := hf.whiskerRight G

end W

end GrothendieckTopology

namespace Sheaf

variable (J A)

/-- The monoidal category structure on `Sheaf J A` that is obtained
by localization of the monoidal category structure on the category
of presheaves. -/
@[instance_reducible]
/-
**CategoryTheory.Sheaf.monoidalCategory** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Sheaf`。
形式化陈述：monoidalCategory [(J.W (A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The monoidal category structure on `Sheaf J A` that is obtained
by localization of the monoidal category structure on the category
of presheaves.
-/
noncomputable def monoidalCategory [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A] :
    MonoidalCategory (Sheaf J A) :=
  inferInstanceAs (MonoidalCategory
    (LocalizedMonoidal (L := presheafToSheaf J A) (W := J.W) (Iso.refl _)))

attribute [local instance] monoidalCategory

/-- The monoidal category structure on `Sheaf J A` obtained in `Sheaf.monoidalCategory` is
braided when `A` is braided. -/
@[instance_reducible]
/-
**CategoryTheory.Sheaf.braidedCategory** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Sheaf`。
形式化陈述：braidedCategory [(J.W (A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The monoidal category structure on `Sheaf J A` obtained in `Sheaf.monoidalCatego
ry` is
braided when `A` is braided.
-/
noncomputable def braidedCategory [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]
    [BraidedCategory A] : BraidedCategory (Sheaf J A) :=
  inferInstanceAs (BraidedCategory
    (LocalizedMonoidal (L := presheafToSheaf J A) (W := J.W) (Iso.refl _)))

/-- The monoidal category structure on `Sheaf J A` obtained in `Sheaf.monoidalCategory` is
symmetric when `A` is symmetric. -/
@[instance_reducible]
/-
**CategoryTheory.Sheaf.symmetricCategory** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Sheaf`。
形式化陈述：symmetricCategory [(J.W (A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The monoidal category structure on `Sheaf J A` obtained in `Sheaf.monoidalCatego
ry` is
symmetric when `A` is symmetric.
-/
noncomputable def symmetricCategory [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]
    [SymmetricCategory A] :
    SymmetricCategory (Sheaf J A) :=
  inferInstanceAs (SymmetricCategory
    (LocalizedMonoidal (L := presheafToSheaf J A) (W := J.W) (Iso.refl _)))
/-
**CategoryTheory.Sheaf.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A] :
    (presheafToSheaf J A).Monoidal :=
  inferInstanceAs (Localization.Monoidal.toMonoidalCategory
    (L := presheafToSheaf J A) (W := J.W) (Iso.refl _)).Monoidal
/-
**CategoryTheory.Sheaf.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Sheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A] [BraidedCategory A] :
    letI := braidedCategory J A
    (presheafToSheaf J A).Braided :=
  inferInstanceAs (Localization.Monoidal.toMonoidalCategory
    (L := presheafToSheaf J A) (W := J.W) (Iso.refl _)).Braided
/-
**CategoryTheory.Sheaf.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Sheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable example
    [HasWeakSheafify J A] [MonoidalClosed A] [BraidedCategory A]
    [∀ (F₁ F₂ : Cᵒᵖ ⥤ A), HasFunctorEnrichedHom A F₁ F₂]
    [∀ (F₁ F₂ : Cᵒᵖ ⥤ A), HasEnrichedHom A F₁ F₂] :
    MonoidalCategory (Sheaf J A) :=
  monoidalCategory J A
/-
**CategoryTheory.Sheaf.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Sheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable example
    [HasWeakSheafify J A] [MonoidalClosed A] [BraidedCategory A]
    [∀ (F₁ F₂ : Cᵒᵖ ⥤ A), HasFunctorEnrichedHom A F₁ F₂]
    [∀ (F₁ F₂ : Cᵒᵖ ⥤ A), HasEnrichedHom A F₁ F₂] :
    BraidedCategory (Sheaf J A) :=
  braidedCategory J A
/-
**CategoryTheory.Sheaf.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Sheaf`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable example
    [HasWeakSheafify J A] [MonoidalClosed A] [SymmetricCategory A]
    [∀ (F₁ F₂ : Cᵒᵖ ⥤ A), HasFunctorEnrichedHom A F₁ F₂]
    [∀ (F₁ F₂ : Cᵒᵖ ⥤ A), HasEnrichedHom A F₁ F₂] :
    SymmetricCategory (Sheaf J A) :=
  symmetricCategory J A

end Sheaf

end CategoryTheory

