/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Localization.Predicate
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# Localization of product categories

In this file, it is shown that if functors `L₁ : C₁ ⥤ D₁` and `L₂ : C₂ ⥤ D₂`
are localization functors for morphisms properties `W₁` and `W₂`, then
the product functor `C₁ × C₂ ⥤ D₁ × D₂` is a localization functor for
`W₁.prod W₂ : MorphismProperty (C₁ × C₂)`, at least if both `W₁` and `W₂`
contain identities. This main result is the instance `Functor.IsLocalization.prod`.

The proof proceeds by showing first `Localization.Construction.prodIsLocalization`,
which asserts that this holds for the localization functors `W₁.Q` and `W₂.Q` to
the constructed localized categories: this is done by showing that the product
functor `W₁.Q.prod W₂.Q : C₁ × C₂ ⥤ W₁.Localization × W₂.Localization` satisfies
the strict universal property of the localization for `W₁.prod W₂`. The general
case follows by transporting this result through equivalences of categories.

-/

@[expose] public section

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

namespace CategoryTheory

open CategoryTheory.Functor

variable {C₁ : Type u₁} {C₂ : Type u₂} {D₁ : Type u₃} {D₂ : Type u₄}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} D₁] [Category.{v₄} D₂]
  (L₁ : C₁ ⥤ D₁) {W₁ : MorphismProperty C₁}
  (L₂ : C₂ ⥤ D₂) {W₂ : MorphismProperty C₂}

namespace Localization

namespace StrictUniversalPropertyFixedTarget

variable {E : Type u₅} [Category.{v₅} E] (F : C₁ × C₂ ⥤ E)

/-
**CategoryTheory.Localization.StrictUniversalPropertyFixedTarget.prod_uniq** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.Localization.StrictUniversalPropertyFixedTa
rget`。
形式化陈述：prod_uniq (F₁ F₂ : (W₁.Localization × W₂.Localization ⥤ E)) (h : (W₁.Q.pro
d W₂.Q) ⋙ F₁ = (W₁.Q.prod W₂.Q) ⋙ F₂) : F₁ = F₂
参数：F₁ F₂ : (W₁.Localization × W₂.Localization ⥤ E)；h : (W₁.Q.prod W₂.Q) ⋙ F₁ = (
W₁.Q.prod W₂.Q) ⋙ F₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.curry_obj_injective`：curry_obj_injective {F₁ F₂ :
 C × D ⥤ E} (h : curry.obj F₁ = curry.obj F₂) : F₁ = F₂
· 使用定理 `CategoryTheory.Localization.Construction.uniq`：uniq (G₁ G₂ : W.Localizat
ion ⥤ D) (h : W.Q ⋙ G₁ = W.Q ⋙ G₂) : G₁ = G₂
· 使用引理 `CategoryTheory.Functor.flip_injective`：flip_injective {F₁ F₂ : B ⥤ C ⥤ D
} (h : F₁.flip = F₂.flip) : F₁ = F₂
· 使用引理 `CategoryTheory.Functor.uncurry_obj_injective`：uncurry_obj_injective {F₁ 
F₂ : B ⥤ C ⥤ D} (h : uncurry.obj F₁ = uncurry.obj F₂) : F₁ = F₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.uncurry_obj_curry_obj_flip_flip`：uncurry_obj_curr
y_obj_flip_flip (F₁ : B ⥤ C) (F₂ : D ⥤ E) (G : C × E ⥤ H) : uncurry.obj (F₂ ⋙ (F
₁ ⋙ curry.obj G).flip).flip = (F₁.prod F₂) ⋙…
-/
lemma prod_uniq (F₁ F₂ : (W₁.Localization × W₂.Localization ⥤ E))
    (h : (W₁.Q.prod W₂.Q) ⋙ F₁ = (W₁.Q.prod W₂.Q) ⋙ F₂) :
      F₁ = F₂ := by
  apply Functor.curry_obj_injective
  apply Construction.uniq
  apply Functor.flip_injective
  apply Construction.uniq
  apply Functor.flip_injective
  apply Functor.uncurry_obj_injective
  simpa only [Functor.uncurry_obj_curry_obj_flip_flip] using h

/-- Auxiliary definition for `prodLift`. -/
/-
**CategoryTheory.Localization.StrictUniversalPropertyFixedTarget.prodLift** 是 Ma
thlib 中的一个定义，位于命名空间 `CategoryTheory.Localization.StrictUniversalPropertyFixedTar
get`。
形式化陈述：prodLift : W₁.Localization × W₂.Localization ⥤ E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `prodLift`.
-/
noncomputable def prodLift₁ [W₂.ContainsIdentities]
    (hF : (W₁.prod W₂).IsInvertedBy F) :
    W₁.Localization ⥤ C₂ ⥤ E :=
  Construction.lift (curry.obj F) (fun _ _ f₁ hf₁ => by
    have : ∀ (X₂ : C₂), IsIso (((curry.obj F).map f₁).app X₂) :=
      fun X₂ => hF _ ⟨hf₁, MorphismProperty.id_mem _ _⟩
    apply NatIso.isIso_of_isIso_app)

variable (hF : (W₁.prod W₂).IsInvertedBy F)
/-
**CategoryTheory.Localization.StrictUniversalPropertyFixedTarget.prod_fac** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.Localization.StrictUniversalPropertyFixedTar
get`。
形式化陈述：prod_fac : (W₁.Q.prod W₂.Q) ⋙ prodLift F hF = F
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Functor.uncurry_obj_curry_obj_flip_flip'`：uncurry_obj_cur
ry_obj_flip_flip' (F₁ : B ⥤ C) (F₂ : D ⥤ E) (G : C × E ⥤ H) : uncurry.obj (F₁ ⋙ 
(F₂ ⋙ (curry.obj G).flip).flip) = (F₁.prod F₂…
· 使用引理 `CategoryTheory.Localization.StrictUniversalPropertyFixedTarget.prod_fac₂
`：prod_fac₂ : W₂.Q ⋙ (curry.obj (prodLift F hF)).flip = (prodLift₁ F hF).flip
· 使用引理 `CategoryTheory.Functor.flip_flip`：flip_flip (F : B ⥤ C ⥤ D) : F.flip.fli
p = F
· 使用引理 `CategoryTheory.Localization.StrictUniversalPropertyFixedTarget.prod_fac₁
`：prod_fac₁ [W₂.ContainsIdentities] : W₁.Q ⋙ prodLift₁ F hF = curry.obj F
· 使用引理 `CategoryTheory.Functor.uncurry_obj_curry_obj`：uncurry_obj_curry_obj (F :
 B × C ⥤ D) : uncurry.obj (curry.obj F) = F
-/
lemma prod_fac₁ [W₂.ContainsIdentities] :
    W₁.Q ⋙ prodLift₁ F hF = curry.obj F :=
  Construction.fac _ _

variable [W₁.ContainsIdentities] [W₂.ContainsIdentities]

/-- The lifting of a functor `F : C₁ × C₂ ⥤ E` inverting `W₁.prod W₂` to a functor
`W₁.Localization × W₂.Localization ⥤ E` -/
/-
**CategoryTheory.Localization.StrictUniversalPropertyFixedTarget.prodLift** 是 Ma
thlib 中的一个定义，位于命名空间 `CategoryTheory.Localization.StrictUniversalPropertyFixedTar
get`。
形式化陈述：prodLift : W₁.Localization × W₂.Localization ⥤ E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lifting of a functor `F : C₁ × C₂ ⥤ E` inverting `W₁.prod W₂` to a functor
`W₁.Localization × W₂.Localization ⥤ E`
-/
noncomputable def prodLift :
    W₁.Localization × W₂.Localization ⥤ E := by
  refine uncurry.obj (Construction.lift (prodLift₁ F hF).flip ?_).flip
  intro _ _ f₂ hf₂
  have : ∀ (X₁ : W₁.Localization),
      IsIso (((Functor.flip (prodLift₁ F hF)).map f₂).app X₁) := fun X₁ => by
    obtain ⟨X₁, rfl⟩ := (Construction.objEquiv W₁).surjective X₁
    exact ((MorphismProperty.isomorphisms E).arrow_mk_iso_iff
      (((Functor.mapArrowFunctor _ _).mapIso
        (eqToIso (Functor.congr_obj (prod_fac₁ F hF) X₁))).app (Arrow.mk f₂))).2
          (hF _ ⟨MorphismProperty.id_mem _ _, hf₂⟩)
  apply NatIso.isIso_of_isIso_app
/-
**CategoryTheory.Localization.StrictUniversalPropertyFixedTarget.prod_fac** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.Localization.StrictUniversalPropertyFixedTar
get`。
形式化陈述：prod_fac : (W₁.Q.prod W₂.Q) ⋙ prodLift F hF = F
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Functor.uncurry_obj_curry_obj_flip_flip'`：uncurry_obj_cur
ry_obj_flip_flip' (F₁ : B ⥤ C) (F₂ : D ⥤ E) (G : C × E ⥤ H) : uncurry.obj (F₁ ⋙ 
(F₂ ⋙ (curry.obj G).flip).flip) = (F₁.prod F₂…
· 使用引理 `CategoryTheory.Localization.StrictUniversalPropertyFixedTarget.prod_fac₂
`：prod_fac₂ : W₂.Q ⋙ (curry.obj (prodLift F hF)).flip = (prodLift₁ F hF).flip
· 使用引理 `CategoryTheory.Functor.flip_flip`：flip_flip (F : B ⥤ C ⥤ D) : F.flip.fli
p = F
· 使用引理 `CategoryTheory.Localization.StrictUniversalPropertyFixedTarget.prod_fac₁
`：prod_fac₁ [W₂.ContainsIdentities] : W₁.Q ⋙ prodLift₁ F hF = curry.obj F
· 使用引理 `CategoryTheory.Functor.uncurry_obj_curry_obj`：uncurry_obj_curry_obj (F :
 B × C ⥤ D) : uncurry.obj (curry.obj F) = F
-/
lemma prod_fac₂ :
    W₂.Q ⋙ (curry.obj (prodLift F hF)).flip = (prodLift₁ F hF).flip := by
  simp only [prodLift, Functor.curry_obj_uncurry_obj, Functor.flip_flip]
  apply Construction.fac
/-
**CategoryTheory.Localization.StrictUniversalPropertyFixedTarget.prod_fac** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.Localization.StrictUniversalPropertyFixedTar
get`。
形式化陈述：prod_fac : (W₁.Q.prod W₂.Q) ⋙ prodLift F hF = F
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Functor.uncurry_obj_curry_obj_flip_flip'`：uncurry_obj_cur
ry_obj_flip_flip' (F₁ : B ⥤ C) (F₂ : D ⥤ E) (G : C × E ⥤ H) : uncurry.obj (F₁ ⋙ 
(F₂ ⋙ (curry.obj G).flip).flip) = (F₁.prod F₂…
· 使用引理 `CategoryTheory.Localization.StrictUniversalPropertyFixedTarget.prod_fac₂
`：prod_fac₂ : W₂.Q ⋙ (curry.obj (prodLift F hF)).flip = (prodLift₁ F hF).flip
· 使用引理 `CategoryTheory.Functor.flip_flip`：flip_flip (F : B ⥤ C ⥤ D) : F.flip.fli
p = F
· 使用引理 `CategoryTheory.Localization.StrictUniversalPropertyFixedTarget.prod_fac₁
`：prod_fac₁ [W₂.ContainsIdentities] : W₁.Q ⋙ prodLift₁ F hF = curry.obj F
· 使用引理 `CategoryTheory.Functor.uncurry_obj_curry_obj`：uncurry_obj_curry_obj (F :
 B × C ⥤ D) : uncurry.obj (curry.obj F) = F
-/
lemma prod_fac :
    (W₁.Q.prod W₂.Q) ⋙ prodLift F hF = F := by
  rw [← Functor.uncurry_obj_curry_obj_flip_flip', prod_fac₂, Functor.flip_flip, prod_fac₁,
    Functor.uncurry_obj_curry_obj]

variable (W₁ W₂)

/-- The product of two (constructed) localized categories satisfies the universal
property of the localized category of the product. -/
/-
**CategoryTheory.Localization.StrictUniversalPropertyFixedTarget.prod** 是 Mathli
b 中的一个定义，位于命名空间 `CategoryTheory.Localization.StrictUniversalPropertyFixedTarget`
。
形式化陈述：prod : StrictUniversalPropertyFixedTarget (W₁.Q.prod W₂.Q) (W₁.prod W₂) E 
where inverts
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Localization.StrictUniversalPropertyFixedTarget.prod_fac`
：prod_fac : (W₁.Q.prod W₂.Q) ⋙ prodLift F hF = F
· 使用引理 `CategoryTheory.Localization.StrictUniversalPropertyFixedTarget.prod_uniq
`：prod_uniq (F₁ F₂ : (W₁.Localization × W₂.Localization ⥤ E)) (h : (W₁.Q.prod W₂
.Q) ⋙ F₁ = (W₁.Q.prod W₂.Q) ⋙ F₂) : F₁ = F₂

--- 原说明 ---
The product of two (constructed) localized categories satisfies the universal
property of the localized category of the product.
-/
noncomputable def prod :
    StrictUniversalPropertyFixedTarget (W₁.Q.prod W₂.Q) (W₁.prod W₂) E where
  inverts := (Localization.inverts W₁.Q W₁).prod (Localization.inverts W₂.Q W₂)
  lift := fun F hF => prodLift F hF
  fac := fun F hF => prod_fac F hF
  uniq := prod_uniq

end StrictUniversalPropertyFixedTarget

variable (W₁ W₂)
variable [W₁.ContainsIdentities] [W₂.ContainsIdentities]

/-
**CategoryTheory.Localization.Construction.prodIsLocalization** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Localization.Construction`。
形式化陈述：∀ {C₁ : Type u₁} {C₂ : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C
₁]   [inst_1 : CategoryTheory.Category.{v₂, u₂} C₂] (W₁ : CategoryTheory.Morphis
mProperty C₁)   (W₂ : CategoryTheory.MorphismProperty C₂) [W₁.ContainsIdentities
] [W₂.ContainsIdentities],   (W₁.Q.prod W₂.Q).IsLocalization (W₁.prod W₂)
参数：W₁ : CategoryTheory.MorphismProperty C₁；W₂ : CategoryTheory.MorphismProperty 
C₂；W₁.Q.prod W₂.Q；W₁.prod W₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsLocalization.mk'`：∀ {C : Type u_1} {D : Type u_
2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryTheory.Cate
gory.{v_2, u_2} D] (L : Categor…
-/
lemma Construction.prodIsLocalization :
    (W₁.Q.prod W₂.Q).IsLocalization (W₁.prod W₂) :=
  Functor.IsLocalization.mk' _ _
    (StrictUniversalPropertyFixedTarget.prod W₁ W₂)
    (StrictUniversalPropertyFixedTarget.prod W₁ W₂)

end Localization

open Localization

namespace Functor

namespace IsLocalization

variable (W₁ W₂)
variable [W₁.ContainsIdentities] [W₂.ContainsIdentities]

/-- If `L₁ : C₁ ⥤ D₁` and `L₂ : C₂ ⥤ D₂` are localization functors
for `W₁ : MorphismProperty C₁` and `W₂ : MorphismProperty C₂` respectively,
and if both `W₁` and `W₂` contain identities, then the product
functor `L₁.prod L₂ : C₁ × C₂ ⥤ D₁ × D₂` is a localization functor for `W₁.prod W₂`. -/
/-
**CategoryTheory.Functor.IsLocalization.prod** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.Functor.IsLocalization`。
形式化陈述：prod [L₁.IsLocalization W₁] [L₂.IsLocalization W₂] : (L₁.prod L₂).IsLocali
zation (W₁.prod W₂)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Localization.Construction.prodIsLocalization`：∀ {C₁ : Typ
e u₁} {C₂ : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C₁]   [inst_1 : Ca
tegoryTheory.Category.{v₂, u₂} C₂] (W₁ : Category…
· 使用定理 `CategoryTheory.Functor.IsLocalization.of_equivalence_target`：of_equivale
nce_target {E : Type*} [Category* E] (L' : C ⥤ E) (eq : D ≌ E) [L.IsLocalization
 W] (e : L ⋙ eq.functor ≅ L') : L'.IsLocalization…

--- 原说明 ---
If `L₁ : C₁ ⥤ D₁` and `L₂ : C₂ ⥤ D₂` are localization functors
for `W₁ : MorphismProperty C₁` and `W₂ : MorphismProperty C₂` respectively,
and if both `W₁` and `W₂` contain identities, then the product
functor `L₁.prod L₂ : C₁ × C₂ ⥤ D₁ × D₂` is a localization functor for `W₁.prod 
W₂`.
-/
instance prod [L₁.IsLocalization W₁] [L₂.IsLocalization W₂] :
    (L₁.prod L₂).IsLocalization (W₁.prod W₂) := by
  have := Construction.prodIsLocalization W₁ W₂
  exact of_equivalence_target (W₁.Q.prod W₂.Q) (W₁.prod W₂) (L₁.prod L₂)
    ((uniq W₁.Q L₁ W₁).prod (uniq W₂.Q L₂ W₂))
    (NatIso.prod (compUniqFunctor W₁.Q L₁ W₁) (compUniqFunctor W₂.Q L₂ W₂))

end IsLocalization

end Functor

end CategoryTheory

