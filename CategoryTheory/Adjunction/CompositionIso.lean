/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Compatibilities for left adjoints from compatibilities satisfied by right adjoints

In this file, given isomorphisms between compositions of right adjoint functors,
we obtain isomorphisms between the corresponding compositions of the left adjoint functors,
and show that the left adjoint functors satisfy properties similar to the left/right
unitality and the associativity of pseudofunctors if the right adjoint functors
satisfy the corresponding properties.

This is used in `Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback` to study
the behaviour with respect to composition of the pullback functors on presheaves
of modules, by reducing these definitions and properties to the (obvious) case of the
pushforward functors. Similar results are obtained for sheaves of modules
in `Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous`.

-/

@[expose] public section

namespace CategoryTheory

variable {C₀ C₁ C₂ C₃ : Type*} [Category* C₀] [Category* C₁] [Category* C₂] [Category* C₃]

open CategoryTheory.Functor

namespace Adjunction

section

variable {F : C₀ ⥤ C₀} {G : C₀ ⥤ C₀} (adj : F ⊣ G) (e : G ≅ 𝟭 C₀)

/-- If a right adjoint functor is isomorphic to the identity functor,
so is the left adjoint. -/
@[simps! -isSimp]
/-
**CategoryTheory.Adjunction.leftAdjointIdIso** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Adjunction`。
形式化陈述：leftAdjointIdIso {F : C₀ ⥤ C₀} {G : C₀ ⥤ C₀} (adj : F ⊣ G) (e : G ≅ 𝟭 C₀) 
: F ≅ 𝟭 C₀
参数：adj : F ⊣ G；e : G ≅ 𝟭 C₀。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If a right adjoint functor is isomorphic to the identity functor,
so is the left adjoint.
-/
def leftAdjointIdIso {F : C₀ ⥤ C₀} {G : C₀ ⥤ C₀} (adj : F ⊣ G) (e : G ≅ 𝟭 C₀) :
    F ≅ 𝟭 C₀ := (conjugateIsoEquiv .id adj).symm e.symm

@[simp]
/-
**CategoryTheory.Adjunction.conjugateEquiv_leftAdjointIdIso_hom** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.Adjunction`。
形式化陈述：conjugateEquiv_leftAdjointIdIso_hom : conjugateEquiv .id adj (leftAdjointI
dIso adj e).hom = e.inv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.conjugateIsoEquiv_symm_apply_hom`：∀ {C : Type u₁} {D : Ty
pe u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} D]   {L₁ L₂ : CategoryT…
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma conjugateEquiv_leftAdjointIdIso_hom :
    conjugateEquiv .id adj (leftAdjointIdIso adj e).hom = e.inv := by
  simp [leftAdjointIdIso]

end

section

variable {F₀₁ : C₀ ⥤ C₁} {F₁₂ : C₁ ⥤ C₂} {F₀₂ : C₀ ⥤ C₂}
  {G₁₀ : C₁ ⥤ C₀} {G₂₁ : C₂ ⥤ C₁} {G₂₀ : C₂ ⥤ C₀}
  (adj₀₁ : F₀₁ ⊣ G₁₀) (adj₁₂ : F₁₂ ⊣ G₂₁) (adj₀₂ : F₀₂ ⊣ G₂₀)

/-- A natural transformation `G₂₀ ⟶ G₂₁ ⋙ G₁₀` involving right adjoint functors
induces a natural transformation `F₀₁ ⋙ F₁₂ ⟶ F₀₂` between the corresponding
left adjoint functors. -/
@[simps! -isSimp]
/-
**CategoryTheory.Adjunction.leftAdjointCompNatTrans** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Adjunction`。
形式化陈述：leftAdjointCompNatTrans (τ₀₁₂ : G₂₀ ⟶ G₂₁ ⋙ G₁₀) : F₀₁ ⋙ F₁₂ ⟶ F₀₂
参数：τ₀₁₂ : G₂₀ ⟶ G₂₁ ⋙ G₁₀。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A natural transformation `G₂₀ ⟶ G₂₁ ⋙ G₁₀` involving right adjoint functors
induces a natural transformation `F₀₁ ⋙ F₁₂ ⟶ F₀₂` between the corresponding
left adjoint functors.
-/
def leftAdjointCompNatTrans (τ₀₁₂ : G₂₀ ⟶ G₂₁ ⋙ G₁₀) :
    F₀₁ ⋙ F₁₂ ⟶ F₀₂ :=
  (conjugateEquiv adj₀₂ (adj₀₁.comp adj₁₂)).symm τ₀₁₂

/-- A natural isomorphism `G₂₁ ⋙ G₁₀ ≅ G₂₀` involving right adjoint functors
induces a natural isomorphism `F₀₁ ⋙ F₁₂ ≅ F₀₂` between the corresponding
left adjoint functors. -/
@[simps! -isSimp]
/-
**CategoryTheory.Adjunction.leftAdjointCompIso** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Adjunction`。
形式化陈述：leftAdjointCompIso (e₀₁₂ : G₂₁ ⋙ G₁₀ ≅ G₂₀) : F₀₁ ⋙ F₁₂ ≅ F₀₂
参数：e₀₁₂ : G₂₁ ⋙ G₁₀ ≅ G₂₀。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A natural isomorphism `G₂₁ ⋙ G₁₀ ≅ G₂₀` involving right adjoint functors
induces a natural isomorphism `F₀₁ ⋙ F₁₂ ≅ F₀₂` between the corresponding
left adjoint functors.
-/
def leftAdjointCompIso (e₀₁₂ : G₂₁ ⋙ G₁₀ ≅ G₂₀) :
    F₀₁ ⋙ F₁₂ ≅ F₀₂ :=
  (conjugateIsoEquiv adj₀₂ (adj₀₁.comp adj₁₂)).symm e₀₁₂.symm
/-
**CategoryTheory.Adjunction.leftAdjointCompIso_hom** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Adjunction`。
形式化陈述：leftAdjointCompIso_hom (e₀₁₂ : G₂₁ ⋙ G₁₀ ≅ G₂₀) : (leftAdjointCompIso adj₀
₁ adj₁₂ adj₀₂ e₀₁₂).hom = leftAdjointCompNatTrans adj₀₁ adj₁₂ adj₀₂ e₀₁₂.inv
参数：e₀₁₂ : G₂₁ ⋙ G₁₀ ≅ G₂₀。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma leftAdjointCompIso_hom (e₀₁₂ : G₂₁ ⋙ G₁₀ ≅ G₂₀) :
    (leftAdjointCompIso adj₀₁ adj₁₂ adj₀₂ e₀₁₂).hom =
      leftAdjointCompNatTrans adj₀₁ adj₁₂ adj₀₂ e₀₁₂.inv :=
  rfl

@[simp]
/-
**CategoryTheory.Adjunction.conjugateEquiv_leftAdjointCompIso_inv** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.Adjunction`。
形式化陈述：conjugateEquiv_leftAdjointCompIso_inv (e₀₁₂ : G₂₁ ⋙ G₁₀ ≅ G₂₀) : conjugate
Equiv (adj₀₁.comp adj₁₂) adj₀₂ (leftAdjointCompIso adj₀₁ adj₁₂ adj₀₂ e₀₁₂).inv =
 e₀₁₂.hom
参数：e₀₁₂ : G₂₁ ⋙ G₁₀ ≅ G₂₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.conjugateIsoEquiv_symm_apply_inv`：∀ {C : Type u₁} {D : Ty
pe u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Cate
gory.{v₂, u₂} D]   {L₁ L₂ : CategoryT…
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma conjugateEquiv_leftAdjointCompIso_inv (e₀₁₂ : G₂₁ ⋙ G₁₀ ≅ G₂₀) :
    conjugateEquiv (adj₀₁.comp adj₁₂) adj₀₂
      (leftAdjointCompIso adj₀₁ adj₁₂ adj₀₂ e₀₁₂).inv = e₀₁₂.hom := by
  dsimp only [leftAdjointCompIso]
  simp

end

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Adjunction.leftAdjointCompIso_comp_id** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Adjunction`。
形式化陈述：leftAdjointCompIso_comp_id {F₀₁ : C₀ ⥤ C₁} {F₁₁' : C₁ ⥤ C₁} {G₁₀ : C₁ ⥤ C₀
} {G₁'₁ : C₁ ⥤ C₁} (adj₀₁ : F₀₁ ⊣ G₁₀) (adj₁₁' : F₁₁' ⊣ G₁'₁) (e₀₁₁' : G₁'₁ ⋙ G₁
₀ ≅ G₁₀) (e₁'₁ : G₁'₁ ≅ 𝟭 _) (h : e₀₁₁' = isoWhiskerRight e₁'₁ G₁₀ ≪≫ leftUnitor
 G₁₀) : leftAdjointCompIso adj₀₁ adj₁₁' adj₀₁ e₀₁₁' = isoWhiskerLeft _ (leftAdjo
intIdIso adj₁₁' e₁'₁) ≪≫ rightUnitor F₀₁
参数：adj₀₁ : F₀₁ ⊣ G₁₀；adj₁₁' : F₁₁' ⊣ G₁'₁；e₀₁₁' : G₁'₁ ⋙ G₁₀ ≅ G₁₀；e₁'₁ : G₁'₁ ≅
 𝟭 _；h : e₀₁₁' = isoWhiskerRight e₁'₁ G₁₀ ≪≫ leftUnitor G₁₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Adjunction.leftAdjointCompIso_hom_app`：∀ {C₀ : Type u_1} 
{C₁ : Type u_2} {C₂ : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1} C₀]  
 [inst_1 : CategoryTheory.Category.{v_2, u…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Adjunction.counit_naturality`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category
.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.left_triangle_components_assoc`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Adjunction.leftAdjointIdIso_hom_app`：∀ {C₀ : Type u_1} [i
nst : CategoryTheory.Category.{v_1, u_1} C₀] {F G : CategoryTheory.Functor C₀ C₀
} (adj : F ⊣ G)   (e : G ≅ CategoryTheor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma leftAdjointCompIso_comp_id
    {F₀₁ : C₀ ⥤ C₁} {F₁₁' : C₁ ⥤ C₁} {G₁₀ : C₁ ⥤ C₀} {G₁'₁ : C₁ ⥤ C₁}
    (adj₀₁ : F₀₁ ⊣ G₁₀) (adj₁₁' : F₁₁' ⊣ G₁'₁)
    (e₀₁₁' : G₁'₁ ⋙ G₁₀ ≅ G₁₀) (e₁'₁ : G₁'₁ ≅ 𝟭 _)
    (h : e₀₁₁' = isoWhiskerRight e₁'₁ G₁₀ ≪≫ leftUnitor G₁₀) :
    leftAdjointCompIso adj₀₁ adj₁₁' adj₀₁ e₀₁₁' =
      isoWhiskerLeft _ (leftAdjointIdIso adj₁₁' e₁'₁) ≪≫ rightUnitor F₀₁ := by
  subst h
  ext X₀
  simp [leftAdjointCompIso_hom_app, leftAdjointIdIso_hom_app,
    ← Functor.map_comp_assoc, -Functor.map_comp]

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Adjunction.leftAdjointCompIso_id_comp** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Adjunction`。
形式化陈述：leftAdjointCompIso_id_comp {F₀₀' : C₀ ⥤ C₀} {F₀'₁ : C₀ ⥤ C₁} {G₀'₀ : C₀ ⥤ 
C₀} {G₁₀' : C₁ ⥤ C₀} (adj₀₀' : F₀₀' ⊣ G₀'₀) (adj₀'₁ : F₀'₁ ⊣ G₁₀') (e₀₀'₁ : G₁₀'
 ⋙ G₀'₀ ≅ G₁₀') (e₀'₀ : G₀'₀ ≅ 𝟭 _) (h : e₀₀'₁ = isoWhiskerLeft G₁₀' e₀'₀ ≪≫ rig
htUnitor G₁₀') : leftAdjointCompIso adj₀₀' adj₀'₁ adj₀'₁ e₀₀'₁ = isoWhiskerRight
 (leftAdjointIdIso adj₀₀' e₀'₀) F₀'₁ ≪≫ leftUnitor F₀'₁
参数：adj₀₀' : F₀₀' ⊣ G₀'₀；adj₀'₁ : F₀'₁ ⊣ G₁₀'；e₀₀'₁ : G₁₀' ⋙ G₀'₀ ≅ G₁₀'；e₀'₀ : G
₀'₀ ≅ 𝟭 _；h : e₀₀'₁ = isoWhiskerLeft G₁₀' e₀'₀ ≪≫ rightUnitor G₁₀'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Functor.congr_map`：congr_map (F : C ⥤ D) {X Y : C} {f g :
 X ⟶ Y} (h : f = g) : F.map f = F.map g
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Adjunction.leftAdjointCompIso_hom_app`：∀ {C₀ : Type u_1} 
{C₁ : Type u_2} {C₂ : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1} C₀]  
 [inst_1 : CategoryTheory.Category.{v_2, u…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Adjunction.left_triangle_components`：∀ {C : Type u₁} [ins
t : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.C
ategory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Adjunction.leftAdjointIdIso_hom_app`：∀ {C₀ : Type u_1} [i
nst : CategoryTheory.Category.{v_1, u_1} C₀] {F G : CategoryTheory.Functor C₀ C₀
} (adj : F ⊣ G)   (e : G ≅ CategoryTheor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma leftAdjointCompIso_id_comp
    {F₀₀' : C₀ ⥤ C₀} {F₀'₁ : C₀ ⥤ C₁} {G₀'₀ : C₀ ⥤ C₀} {G₁₀' : C₁ ⥤ C₀}
    (adj₀₀' : F₀₀' ⊣ G₀'₀) (adj₀'₁ : F₀'₁ ⊣ G₁₀')
    (e₀₀'₁ : G₁₀' ⋙ G₀'₀ ≅ G₁₀') (e₀'₀ : G₀'₀ ≅ 𝟭 _)
    (h : e₀₀'₁ = isoWhiskerLeft G₁₀' e₀'₀ ≪≫ rightUnitor G₁₀') :
    leftAdjointCompIso adj₀₀' adj₀'₁ adj₀'₁ e₀₀'₁ =
      isoWhiskerRight (leftAdjointIdIso adj₀₀' e₀'₀) F₀'₁ ≪≫ leftUnitor F₀'₁ := by
  subst h
  ext X₀
  have h₁ := congr_map F₀'₁ (adj₀₀'.counit.naturality (adj₀'₁.unit.app X₀))
  have h₂ := congr_map (F₀₀' ⋙ F₀'₁) (e₀'₀.inv.naturality (adj₀'₁.unit.app X₀))
  simp only [id_obj, comp_obj, Functor.id_map, Functor.comp_map, Functor.map_comp] at h₁ h₂
  simp [leftAdjointCompIso_hom_app, leftAdjointIdIso_hom_app,
    reassoc_of% h₂, reassoc_of% h₁]

section

variable
  {F₀₁ : C₀ ⥤ C₁} {F₁₂ : C₁ ⥤ C₂} {F₂₃ : C₂ ⥤ C₃} {F₀₂ : C₀ ⥤ C₂} {F₁₃ : C₁ ⥤ C₃} {F₀₃ : C₀ ⥤ C₃}
  {G₁₀ : C₁ ⥤ C₀} {G₂₁ : C₂ ⥤ C₁} {G₃₂ : C₃ ⥤ C₂} {G₂₀ : C₂ ⥤ C₀} {G₃₁ : C₃ ⥤ C₁} {G₃₀ : C₃ ⥤ C₀}
  (adj₀₁ : F₀₁ ⊣ G₁₀) (adj₁₂ : F₁₂ ⊣ G₂₁) (adj₂₃ : F₂₃ ⊣ G₃₂) (adj₀₂ : F₀₂ ⊣ G₂₀)
  (adj₁₃ : F₁₃ ⊣ G₃₁) (adj₀₃ : F₀₃ ⊣ G₃₀)

section

variable (τ₀₁₂ : G₂₀ ⟶ G₂₁ ⋙ G₁₀) (τ₁₂₃ : G₃₁ ⟶ G₃₂ ⋙ G₂₁)
  (τ₀₁₃ : G₃₀ ⟶ G₃₁ ⋙ G₁₀) (τ₀₂₃ : G₃₀ ⟶ G₃₂ ⋙ G₂₀)

/-
**CategoryTheory.Adjunction.leftAdjointCompNatTrans** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Adjunction`。
形式化陈述：leftAdjointCompNatTrans (τ₀₁₂ : G₂₀ ⟶ G₂₁ ⋙ G₁₀) : F₀₁ ⋙ F₁₂ ⟶ F₀₂
参数：τ₀₁₂ : G₂₀ ⟶ G₂₁ ⋙ G₁₀。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma leftAdjointCompNatTrans₀₁₃_eq_conjugateEquiv_symm :
    whiskerLeft _ (leftAdjointCompNatTrans adj₁₂ adj₂₃ adj₁₃ τ₁₂₃) ≫
      leftAdjointCompNatTrans adj₀₁ adj₁₃ adj₀₃ τ₀₁₃ =
    (conjugateEquiv adj₀₃ (adj₀₁.comp (adj₁₂.comp adj₂₃))).symm
      (τ₀₁₃ ≫ whiskerRight τ₁₂₃ G₁₀) := by
  obtain ⟨τ₁₂₃, rfl⟩ := (conjugateEquiv adj₁₃ (adj₁₂.comp adj₂₃)).surjective τ₁₂₃
  obtain ⟨τ₀₁₃, rfl⟩ := (conjugateEquiv adj₀₃ (adj₀₁.comp adj₁₃)).surjective τ₀₁₃
  apply (conjugateEquiv adj₀₃ (adj₀₁.comp (adj₁₂.comp adj₂₃))).injective
  simp [leftAdjointCompNatTrans, ← conjugateEquiv_whiskerLeft _ _ adj₀₁]
/-
**CategoryTheory.Adjunction.leftAdjointCompNatTrans** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Adjunction`。
形式化陈述：leftAdjointCompNatTrans (τ₀₁₂ : G₂₀ ⟶ G₂₁ ⋙ G₁₀) : F₀₁ ⋙ F₁₂ ⟶ F₀₂
参数：τ₀₁₂ : G₂₀ ⟶ G₂₁ ⋙ G₁₀。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma leftAdjointCompNatTrans₀₂₃_eq_conjugateEquiv_symm :
    (associator _ _ _).inv ≫
      whiskerRight (leftAdjointCompNatTrans adj₀₁ adj₁₂ adj₀₂ τ₀₁₂) F₂₃ ≫
          leftAdjointCompNatTrans adj₀₂ adj₂₃ adj₀₃ τ₀₂₃ =
    (conjugateEquiv adj₀₃ (adj₀₁.comp (adj₁₂.comp adj₂₃))).symm
      (τ₀₂₃ ≫ whiskerLeft G₃₂ τ₀₁₂ ≫ (associator _ _ _).inv) := by
  obtain ⟨τ₀₁₂, rfl⟩ := (conjugateEquiv adj₀₂ (adj₀₁.comp adj₁₂)).surjective τ₀₁₂
  obtain ⟨τ₀₂₃, rfl⟩ := (conjugateEquiv adj₀₃ (adj₀₂.comp adj₂₃)).surjective τ₀₂₃
  apply (conjugateEquiv adj₀₃ (adj₀₁.comp (adj₁₂.comp adj₂₃))).injective
  simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply, leftAdjointCompNatTrans]
  rw [← cancel_mono (associator G₃₂ G₂₁ G₁₀).hom, Category.assoc, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, ← conjugateEquiv_associator_hom adj₀₁ adj₁₂ adj₂₃,
    ← conjugateEquiv_whiskerRight _ _ adj₂₃, conjugateEquiv_comp, Iso.hom_inv_id_assoc,
    conjugateEquiv_comp]
/-
**CategoryTheory.Adjunction.leftAdjointCompNatTrans_assoc** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Adjunction`。
形式化陈述：leftAdjointCompNatTrans_assoc (h : τ₀₂₃ ≫ whiskerLeft G₃₂ τ₀₁₂ = τ₀₁₃ ≫ wh
iskerRight τ₁₂₃ G₁₀ ≫ (associator _ _ _).hom) : whiskerLeft _ (leftAdjointCompNa
tTrans adj₁₂ adj₂₃ adj₁₃ τ₁₂₃) ≫ leftAdjointCompNatTrans adj₀₁ adj₁₃ adj₀₃ τ₀₁₃ 
= (associator _ _ _).inv ≫ whiskerRight (leftAdjointCompNatTrans adj₀₁ adj₁₂ adj
₀₂ τ₀₁₂) F₂₃ ≫ leftAdjointCompNatTrans adj₀₂ adj₂₃ adj₀₃ τ₀₂₃
参数：h : τ₀₂₃ ≫ whiskerLeft G₃₂ τ₀₁₂ = τ₀₁₃ ≫ whiskerRight τ₁₂₃ G₁₀ ≫ (associator 
_ _ _).hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Adjunction.leftAdjointCompNatTrans₀₁₃_eq_conjugateEquiv_s
ymm`：leftAdjointCompNatTrans₀₁₃_eq_conjugateEquiv_symm : whiskerLeft _ (leftAdjo
intCompNatTrans adj₁₂ adj₂₃ adj₁₃ τ₁₂₃) ≫ leftAdjointCompNatTrans…
· 使用引理 `CategoryTheory.Adjunction.leftAdjointCompNatTrans₀₂₃_eq_conjugateEquiv_s
ymm`：leftAdjointCompNatTrans₀₂₃_eq_conjugateEquiv_symm : (associator _ _ _).inv 
≫ whiskerRight (leftAdjointCompNatTrans adj₀₁ adj₁₂ adj₀₂ τ₀₁₂) F…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma leftAdjointCompNatTrans_assoc
    (h : τ₀₂₃ ≫ whiskerLeft G₃₂ τ₀₁₂ =
      τ₀₁₃ ≫ whiskerRight τ₁₂₃ G₁₀ ≫ (associator _ _ _).hom) :
    whiskerLeft _ (leftAdjointCompNatTrans adj₁₂ adj₂₃ adj₁₃ τ₁₂₃) ≫
        leftAdjointCompNatTrans adj₀₁ adj₁₃ adj₀₃ τ₀₁₃ =
      (associator _ _ _).inv ≫
        whiskerRight (leftAdjointCompNatTrans adj₀₁ adj₁₂ adj₀₂ τ₀₁₂) F₂₃ ≫
          leftAdjointCompNatTrans adj₀₂ adj₂₃ adj₀₃ τ₀₂₃ := by
  simp [leftAdjointCompNatTrans₀₁₃_eq_conjugateEquiv_symm,
    leftAdjointCompNatTrans₀₂₃_eq_conjugateEquiv_symm, reassoc_of% h]

end

/-
**CategoryTheory.Adjunction.leftAdjointCompIso_assoc** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Adjunction`。
形式化陈述：leftAdjointCompIso_assoc (e₀₁₂ : G₂₁ ⋙ G₁₀ ≅ G₂₀) (e₁₂₃ : G₃₂ ⋙ G₂₁ ≅ G₃₁)
 (e₀₁₃ : G₃₁ ⋙ G₁₀ ≅ G₃₀) (e₀₂₃ : G₃₂ ⋙ G₂₀ ≅ G₃₀) (h : isoWhiskerLeft G₃₂ e₀₁₂ 
≪≫ e₀₂₃ = (associator _ _ _).symm ≪≫ isoWhiskerRight e₁₂₃ _ ≪≫ e₀₁₃) : isoWhiske
rLeft _ (leftAdjointCompIso adj₁₂ adj₂₃ adj₁₃ e₁₂₃) ≪≫ leftAdjointCompIso adj₀₁ 
adj₁₃ adj₀₃ e₀₁₃ = (associator _ _ _).symm ≪≫ isoWhiskerRight (leftAdjointCompIs
o adj₀₁ adj₁₂ adj₀₂ e₀₁₂) F₂₃ ≪≫ leftAdjointCompIso adj₀₂ adj₂₃ adj₀₃ e₀₂₃
参数：e₀₁₂ : G₂₁ ⋙ G₁₀ ≅ G₂₀；e₁₂₃ : G₃₂ ⋙ G₂₁ ≅ G₃₁；e₀₁₃ : G₃₁ ⋙ G₁₀ ≅ G₃₀；e₀₂₃ : G
₃₂ ⋙ G₂₀ ≅ G₃₀；h : isoWhiskerLeft G₃₂ e₀₁₂ ≪≫ e₀₂₃ = (associator _ _ _).symm ≪≫ 
isoWhiskerRight e₁₂₃ _ ≪≫ e₀₁₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用引理 `CategoryTheory.Adjunction.leftAdjointCompNatTrans_assoc`：leftAdjointComp
NatTrans_assoc (h : τ₀₂₃ ≫ whiskerLeft G₃₂ τ₀₁₂ = τ₀₁₃ ≫ whiskerRight τ₁₂₃ G₁₀ ≫
 (associator _ _ _).hom) : whiskerLeft _ (lef…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
lemma leftAdjointCompIso_assoc
    (e₀₁₂ : G₂₁ ⋙ G₁₀ ≅ G₂₀) (e₁₂₃ : G₃₂ ⋙ G₂₁ ≅ G₃₁)
    (e₀₁₃ : G₃₁ ⋙ G₁₀ ≅ G₃₀) (e₀₂₃ : G₃₂ ⋙ G₂₀ ≅ G₃₀)
    (h : isoWhiskerLeft G₃₂ e₀₁₂ ≪≫ e₀₂₃ =
      (associator _ _ _).symm ≪≫ isoWhiskerRight e₁₂₃ _ ≪≫ e₀₁₃) :
    isoWhiskerLeft _ (leftAdjointCompIso adj₁₂ adj₂₃ adj₁₃ e₁₂₃) ≪≫
        leftAdjointCompIso adj₀₁ adj₁₃ adj₀₃ e₀₁₃ =
      (associator _ _ _).symm ≪≫
        isoWhiskerRight (leftAdjointCompIso adj₀₁ adj₁₂ adj₀₂ e₀₁₂) F₂₃ ≪≫
          leftAdjointCompIso adj₀₂ adj₂₃ adj₀₃ e₀₂₃ := by
  ext : 1
  exact leftAdjointCompNatTrans_assoc _ _ _ _ _ _ _ _ _ _
    (by simpa using congr_arg Iso.inv h)

end

end Adjunction

end CategoryTheory

