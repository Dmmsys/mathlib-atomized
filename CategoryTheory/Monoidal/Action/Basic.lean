/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Monoidal.Category

/-!

# Actions from a monoidal category on a category

Given a monoidal category `C`, and a category `D`, we define a left action of
`C` on `D` as the data of an object `c ⊙ₗ d` of `D` for every
`c : C` and `d : D`, as well as the data required to turn `- ⊙ₗ -` into
a bifunctor, along with structure natural isomorphisms
`(- ⊗ -) ⊙ₗ - ≅ - ⊙ₗ - ⊙ₗ -` and `𝟙_ C ⊙ₗ - ≅ -`, subject to coherence conditions.

We also define right actions, for these, the notation for the action of `c`
on `d` is `d ⊙ᵣ c`, and the structure isomorphisms are of the form
`- ⊙ᵣ (- ⊗ -) ≅ (- ⊙ᵣ -) ⊙ᵣ -` and `- ⊙ₗ 𝟙_ C ≅ -`.


## References
* [Janelidze, G, and Kelly, G.M., *A note on actions of a monoidal category*][JanelidzeKelly2001]

## TODOs/Projects
* Equivalence between actions of `C` on `D` and pseudofunctors from the
  classifying bicategory of `C` to `Cat`.
* Left/Right Modules in `D` over a monoid object in `C`.
  Equivalence with `Mod_` when `D` is `C`. Bimodules objects.
* Given a monad `M` on `C`, equivalence between `Algebra M`, and modules in `C`
  on `M.toMon : Mon (C ⥤ C)`.
* Canonical left action of `Type u` on `u`-small cocomplete categories via the
  copower.

-/

@[expose] public section

namespace CategoryTheory.MonoidalCategory

variable (C D : Type*)

variable [Category* C] [Category* D]
/-- A class that carries the non-Prop data required to define a left action of a
monoidal category `C` on a category `D`, to set up notations. -/
/-
**CategoryTheory.MonoidalCategory.MonoidalLeftActionStruct** 是 Mathlib 中的一个类，位于命
名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：MonoidalLeftActionStruct [MonoidalCategoryStruct C] where /-- The left act
ion on objects. This is denoted `c ⊙ₗ d`. -/ actionObj : C -> D -> D /-- The lef
t action of a map `f : c ⟶ c'` in `C` on an object `d` in `D`. If we are to cons
ider the action as a functor `Α : C ⥤ D ⥤ D`, this is `(Α.map f).app d`. This is
 denoted `f ⊵ₗ d`. -/ actionHomLeft {c c' : C} (f : c ⟶ c') (d : D) : actionObj 
c d ⟶ actionObj c' d /-- The action of an object `c : C` on a map `f : d ⟶ d'` i
n `D`. If we are to consid
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A class that carries the non-Prop data required to define a left action of a
monoidal category `C` on a category `D`, to set up notations. -/
-/
class MonoidalLeftActionStruct [MonoidalCategoryStruct C] where
  /-- The left action on objects. This is denoted `c ⊙ₗ d`. -/
  actionObj : C → D → D
  /-- The left action of a map `f : c ⟶ c'` in `C` on an object `d` in `D`.
  If we are to consider the action as a functor `Α : C ⥤ D ⥤ D`,
  this is `(Α.map f).app d`. This is denoted `f ⊵ₗ d`. -/
  actionHomLeft {c c' : C} (f : c ⟶ c') (d : D) :
    actionObj c d ⟶ actionObj c' d
  /-- The action of an object `c : C` on a map `f : d ⟶ d'` in `D`.
  If we are to consider the action as a functor `Α : C ⥤ D ⥤ D`,
  this is `(Α.obj c).map f`. This is denoted `c ⊴ₗ f`. -/
  actionHomRight (c : C) {d d' : D} (f : d ⟶ d') :
    actionObj c d ⟶ actionObj c d'
  /-- The action of a pair of maps `f : c ⟶ c'` and `d ⟶ d'`. By default,
  this is defined in terms of `actionHomLeft` and `actionHomRight`. -/
  actionHom {c c' : C} {d d' : D} (f : c ⟶ c') (g : d ⟶ d') :
    actionObj c d ⟶ actionObj c' d' := actionHomLeft f d ≫ actionHomRight c' g
  /-- The structural isomorphism `(c ⊗ c') ⊙ₗ d ≅ c ⊙ₗ (c' ⊙ₗ d)`. -/
  actionAssocIso (c c' : C) (d : D) :
    actionObj (c ⊗ c') d ≅ actionObj c (actionObj c' d)
  /-- The structural isomorphism between `𝟙_ C ⊙ₗ d` and `d`. -/
  actionUnitIso (d : D) : actionObj (𝟙_ C) d ≅ d

namespace MonoidalLeftAction

export MonoidalLeftActionStruct
  (actionObj actionHomLeft actionHomRight actionHom actionAssocIso
    actionUnitIso)

-- infix priorities are aligned with the ones from `MonoidalCategoryStruct`.

/-- Notation for `actionObj`, the action of `C` on `D`. -/
scoped infixr:70 " ⊙ₗ " => MonoidalLeftActionStruct.actionObj

/-- Notation for `actionHomLeft`, the action of `C` on morphisms in `D`. -/
scoped infixr:81 " ⊵ₗ " => MonoidalLeftActionStruct.actionHomLeft

/-- Notation for `actionHomRight`, the action of morphism in `C` on `D`. -/
scoped infixr:81 " ⊴ₗ " => MonoidalLeftActionStruct.actionHomRight

/-- Notation for `actionHom`, the bifunctorial action of morphisms in `C` and
`D` on `- ⊙ₗ -`. -/
scoped infixr:70 " ⊙ₗₘ " => MonoidalLeftActionStruct.actionHom

/-- Notation for `actionAssocIso`, the structural isomorphism
`- ⊗ - ⊙ₗ - ≅ - ⊙ₗ - ⊙ₗ -`. -/
scoped notation "αₗ " => MonoidalLeftActionStruct.actionAssocIso

/-- Notation for `actionUnitIso`, the structural isomorphism `𝟙_ C ⊙ₗ - ≅ -`. -/
scoped notation "λₗ " => MonoidalLeftActionStruct.actionUnitIso
/-- Notation for `actionUnitIso`, the structural isomorphism `𝟙_ C ⊙ₗ - ≅ -`,
allowing one to specify the acting category. -/
scoped notation "λₗ["J"]" => MonoidalLeftActionStruct.actionUnitIso (C := J)

end MonoidalLeftAction

open scoped MonoidalLeftAction in
/-- A `MonoidalLeftAction C D` is the data of:
- For every object `c : C` and `d : D`, an object `c ⊙ₗ d` of `D`.
- For every morphism `f : (c : C) ⟶ c'` and every `d : D`, a morphism
  `f ⊵ₗ d : c ⊙ₗ d ⟶ c' ⊙ₗ d`.
- For every morphism `f : (d : D) ⟶ d'` and every `c : C`, a morphism
  `c ⊴ₗ f : c ⊙ₗ d ⟶ c ⊙ₗ d'`.
- For every pair of morphisms `f : (c : C) ⟶ c'` and
  `f : (d : D) ⟶ d'`, a morphism `f ⊙ₗ f' : c ⊙ₗ d ⟶ c' ⊙ₗ d'`.
- A structure isomorphism `αₗ c c' d : c ⊗ c' ⊙ₗ d ≅ c ⊙ₗ c' ⊙ₗ d`.
- A structure isomorphism `λₗ d : (𝟙_ C) ⊙ₗ d ≅ d`.

Furthermore, we require identities that turn `- ⊙ₗ -` into a bifunctor,
ensure naturality of `αₗ` and `λₗ`, and ensure compatibilities with
the associator and unitor isomorphisms in `C`. -/
/-
**CategoryTheory.MonoidalCategory.MonoidalLeftAction** 是 Mathlib 中的一个类，位于命名空间 `C
ategoryTheory.MonoidalCategory`。
形式化陈述：MonoidalLeftAction [MonoidalCategory C] extends MonoidalLeftActionStruct C
 D where actionHom_def {c c' : C} {d d' : D} (f : c ⟶ c') (g : d ⟶ d') : f ⊙ₗₘ g
 = f ⊵ₗ d ≫ c' ⊴ₗ g
参数：f : c ⟶ c'；g : d ⟶ d'。
继承自：MonoidalLeftActionStruct C D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `MonoidalLeftAction C D` is the data of:
- For every object `c : C` and `d : D`, an object `c ⊙ₗ d` of `D`.
- For every morphism `f : (c : C) ⟶ c'` and every `d : D`, a morphism
  `f ⊵ₗ d : c ⊙ₗ d ⟶ c' ⊙ₗ d`.
- For every morphism `f : (d : D) ⟶ d'` and every `c : C`, a morphism
  `c ⊴ₗ f : c ⊙ₗ d ⟶ c ⊙ₗ d'`.
- For every pair of morphisms `f : (c : C) ⟶ c'` and
  `f : (d : D) ⟶ d'`, a morphism `f ⊙ₗ f' : c ⊙ₗ d ⟶ c' ⊙ₗ d'`.
- A structure isomorphism `αₗ c c' d : c ⊗ c' ⊙ₗ d ≅ c ⊙ₗ c' ⊙ₗ d`.
- A structure isomorphism `λₗ d : (𝟙_ C) ⊙ₗ d ≅ d`.

Furthermore, we require identities that turn `- ⊙ₗ -` into a bifunctor,
ensure naturality of `αₗ` and `λₗ`, and ensure compatibilities with
the associator and unitor isomorphisms in `C`.
-/
class MonoidalLeftAction [MonoidalCategory C] extends
    MonoidalLeftActionStruct C D where
  actionHom_def {c c' : C} {d d' : D} (f : c ⟶ c') (g : d ⟶ d') :
      f ⊙ₗₘ g = f ⊵ₗ d ≫ c' ⊴ₗ g := by
    cat_disch
  actionHomRight_id (c : C) (d : D) : c ⊴ₗ 𝟙 d = 𝟙 (c ⊙ₗ d) := by cat_disch
  id_actionHomLeft (c : C) (d : D) : 𝟙 c ⊵ₗ d = 𝟙 (c ⊙ₗ d) := by cat_disch
  actionHom_comp
      {c c' c'' : C} {d d' d'' : D} (f₁ : c ⟶ c') (f₂ : c' ⟶ c'')
      (g₁ : d ⟶ d') (g₂ : d' ⟶ d'') :
      (f₁ ≫ f₂) ⊙ₗₘ (g₁ ≫ g₂) = (f₁ ⊙ₗₘ g₁) ≫ (f₂ ⊙ₗₘ g₂) := by
    cat_disch
  actionAssocIso_hom_naturality
      {c₁ c₂ c₃ c₄ : C} {d₁ d₂ : D} (f : c₁ ⟶ c₂) (g : c₃ ⟶ c₄) (h : d₁ ⟶ d₂) :
      ((f ⊗ₘ g) ⊙ₗₘ h) ≫ (αₗ c₂ c₄ d₂).hom =
        (αₗ c₁ c₃ d₁).hom ≫ (f ⊙ₗₘ g ⊙ₗₘ h) := by
    cat_disch
  actionUnitIso_hom_naturality {d d' : D} (f : d ⟶ d') :
      (λₗ d).hom ≫ f = (𝟙_ C) ⊴ₗ f ≫ (λₗ d').hom := by
    cat_disch
  whiskerLeft_actionHomLeft (c : C) {c' c'' : C} (f : c' ⟶ c'') (d : D) :
      (c ◁ f) ⊵ₗ d = (αₗ _ _ _).hom ≫ c ⊴ₗ f ⊵ₗ d ≫ (αₗ _ _ _).inv := by
    cat_disch
  whiskerRight_actionHomLeft {c c' : C} (c'' : C) (f : c ⟶ c') (d : D) :
      (f ▷ c'') ⊵ₗ d = (αₗ c c'' d).hom ≫
        f ⊵ₗ (c'' ⊙ₗ d : D) ≫ (αₗ c' c'' d).inv := by
    cat_disch
  associator_actionHom (c₁ c₂ c₃ : C) (d : D) :
      (α_ c₁ c₂ c₃).hom ⊵ₗ d ≫ (αₗ c₁ (c₂ ⊗ c₃) d).hom ≫
        c₁ ⊴ₗ (αₗ c₂ c₃ d).hom =
      (αₗ (c₁ ⊗ c₂ : C) c₃ d).hom ≫ (αₗ c₁ c₂ (c₃ ⊙ₗ d)).hom := by
    cat_disch
  leftUnitor_actionHom (c : C) (d : D) :
      (λ_ c).hom ⊵ₗ d = (αₗ _ _ _).hom ≫ (λₗ _).hom := by
    cat_disch
  rightUnitor_actionHom (c : C) (d : D) :
      (ρ_ c).hom ⊵ₗ d = (αₗ _ _ _).hom ≫ c ⊴ₗ (λₗ _).hom := by
    cat_disch

attribute [reassoc] MonoidalLeftAction.actionHom_def
attribute [reassoc, simp] MonoidalLeftAction.id_actionHomLeft
attribute [reassoc, simp] MonoidalLeftAction.actionHomRight_id
attribute [reassoc, simp] MonoidalLeftAction.whiskerLeft_actionHomLeft
attribute [simp, reassoc] MonoidalLeftAction.actionHom_comp
attribute [reassoc] MonoidalLeftAction.actionAssocIso_hom_naturality
attribute [reassoc] MonoidalLeftAction.actionUnitIso_hom_naturality
attribute [reassoc (attr := simp)] MonoidalLeftAction.associator_actionHom
attribute [simp, reassoc] MonoidalLeftAction.leftUnitor_actionHom
attribute [simp, reassoc] MonoidalLeftAction.rightUnitor_actionHom

/--
A monoidal category acts on itself on the left through the tensor product.
-/
@[simps!]
/-
**CategoryTheory.MonoidalCategory.selfLeftAction** 是 Mathlib 中的一个实例，位于命名空间 `Cate
goryTheory.MonoidalCategory`。
形式化陈述：selfLeftAction [MonoidalCategory C] : MonoidalLeftAction C C where actionO
bj x y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A monoidal category acts on itself on the left through the tensor product.
-/
instance selfLeftAction [MonoidalCategory C] : MonoidalLeftAction C C where
  actionObj x y := x ⊗ y
  actionHom f g := f ⊗ₘ g
  actionUnitIso x := λ_ x
  actionAssocIso x y z := α_ x y z
  actionHomLeft f x := f ▷ x
  actionHomRight x _ _ f := x ◁ f
  actionHom_def := by simp [tensorHom_def]

namespace MonoidalLeftAction

open Category

variable {C D} [MonoidalCategory C] [MonoidalLeftAction C D]

-- Simp normal forms are aligned with the ones in `MonoidalCategory`.

@[simp]
/-
**CategoryTheory.MonoidalCategory.MonoidalLeftAction.id_actionHom** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalLeftAction`。
形式化陈述：id_actionHom (c : C) {d d' : D} (f : d ⟶ d') : (𝟙 c) ⊙ₗₘ f = c ⊴ₗ f
参数：c : C；f : d ⟶ d'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalLeftAction.actionHom_def`：∀ {C :
 Type u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {inst_
1 : CategoryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalLeftAction.id_actionHomLeft`：∀ {
C : Type u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {in
st_1 : CategoryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma id_actionHom (c : C) {d d' : D} (f : d ⟶ d') :
    (𝟙 c) ⊙ₗₘ f = c ⊴ₗ f := by
  simp [actionHom_def]

@[simp]
/-
**CategoryTheory.MonoidalCategory.MonoidalLeftAction.actionHom_id** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalLeftAction`。
形式化陈述：actionHom_id {c c' : C} (f : c ⟶ c') (d : D) : f ⊙ₗₘ (𝟙 d) = f ⊵ₗ d
参数：f : c ⟶ c'；d : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalLeftAction.actionHom_def`：∀ {C :
 Type u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {inst_
1 : CategoryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalLeftAction.actionHomRight_id`：∀ 
{C : Type u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {i
nst_1 : CategoryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma actionHom_id {c c' : C} (f : c ⟶ c') (d : D) :
    f ⊙ₗₘ (𝟙 d) = f ⊵ₗ d := by
  simp [actionHom_def]

@[reassoc, simp]
/-
**CategoryTheory.MonoidalCategory.MonoidalLeftAction.actionHomRight_comp** 是 Mat
hlib 中的一个定理，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalLeftAction`。
形式化陈述：actionHomRight_comp (w : C) {x y z : D} (f : x ⟶ y) (g : y ⟶ z) : w ⊴ₗ (f 
≫ g) = w ⊴ₗ f ≫ w ⊴ₗ g
参数：w : C；f : x ⟶ y；g : y ⟶ z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem actionHomRight_comp (w : C) {x y z : D} (f : x ⟶ y) (g : y ⟶ z) :
    w ⊴ₗ (f ≫ g) = w ⊴ₗ f ≫ w ⊴ₗ g := by
  simp [← id_actionHom, ← actionHom_comp]

@[reassoc, simp]
/-
**CategoryTheory.MonoidalCategory.MonoidalLeftAction.unit_actionHomRight** 是 Mat
hlib 中的一个定理，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalLeftAction`。
形式化陈述：unit_actionHomRight {x y : D} (f : x ⟶ y) : (𝟙_ C) ⊴ₗ f = (funₗ x).hom ≫ f
 ≫ (funₗ y).inv
参数：f : x ⟶ y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalLeftAction.actionUnitIso_hom_nat
urality`：∀ {C : Type u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, u
_1} C}   {inst_1 : CategoryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem unit_actionHomRight {x y : D} (f : x ⟶ y) :
    (𝟙_ C) ⊴ₗ f = (λₗ x).hom ≫ f ≫ (λₗ y).inv := by
  rw [← Category.assoc, actionUnitIso_hom_naturality]
  simp

@[reassoc, simp]
/-
**CategoryTheory.MonoidalCategory.MonoidalLeftAction.tensor_actionHomRight** 是 M
athlib 中的一个定理，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalLeftAction`。
形式化陈述：tensor_actionHomRight (x y : C) {z z' : D} (f : z ⟶ z') : (x otimes y) ⊴ₗ 
f = (αₗ x y z).hom ≫ x ⊴ₗ y ⊴ₗ f ≫ (αₗ x y z').inv
参数：x y : C；f : z ⟶ z'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalLeftAction.actionAssocIso_hom_na
turality`：∀ {C : Type u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, 
u_1} C}   {inst_1 : CategoryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `CategoryTheory.MonoidalCategory.MonoidalLeftAction.id_actionHom`：id_acti
onHom (c : C) {d d' : D} (f : d ⟶ d') : (𝟙 c) ⊙ₗₘ f = c ⊴ₗ f
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerRight`：∀ {C : Type u} {𝒞 : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y :
 C),   CategoryTheory.MonoidalCategor…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tensor_actionHomRight (x y : C) {z z' : D} (f : z ⟶ z') :
    (x ⊗ y) ⊴ₗ f = (αₗ x y z).hom ≫ x ⊴ₗ y ⊴ₗ f ≫ (αₗ x y z').inv := by
  simp only [← id_actionHom]
  rw [← Category.assoc, ← actionAssocIso_hom_naturality]
  simp

@[reassoc, simp]
/-
**CategoryTheory.MonoidalCategory.MonoidalLeftAction.comp_actionHomLeft** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalLeftAction`。
形式化陈述：comp_actionHomLeft {w x y : C} (f : w ⟶ x) (g : x ⟶ y) (z : D) : (f ≫ g) ⊵
ₗ z = f ⊵ₗ z ≫ g ⊵ₗ z
参数：f : w ⟶ x；g : x ⟶ y；z : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp_actionHomLeft {w x y : C} (f : w ⟶ x) (g : x ⟶ y) (z : D) :
    (f ≫ g) ⊵ₗ z = f ⊵ₗ z ≫ g ⊵ₗ z := by
  simp only [← actionHom_id, ← actionHom_comp, Category.id_comp]

@[reassoc, simp]
/-
**CategoryTheory.MonoidalCategory.MonoidalLeftAction.actionHomLeft_action** 是 Ma
thlib 中的一个定理，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalLeftAction`。
形式化陈述：actionHomLeft_action {x x' : C} (f : x ⟶ x') (y : C) (z : D) : f ⊵ₗ (y ⊙ₗ 
z) = (αₗ x y z).inv ≫ (f ▷ y) ⊵ₗ z ≫ (αₗ x' y z).hom
参数：f : x ⟶ x'；y : C；z : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalLeftAction.whiskerRight_actionHo
mLeft`：∀ {C : Type u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1
} C}   {inst_1 : CategoryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem actionHomLeft_action {x x' : C} (f : x ⟶ x') (y : C) (z : D) :
    f ⊵ₗ (y ⊙ₗ z) = (αₗ x y z).inv ≫ (f ▷ y) ⊵ₗ z ≫ (αₗ x' y z).hom := by
  simp [whiskerRight_actionHomLeft]

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.MonoidalLeftAction.action_exchange** 是 Mathlib
 中的一个定理，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalLeftAction`。
形式化陈述：action_exchange {w x : C} {y z : D} (f : w ⟶ x) (g : y ⟶ z) : w ⊴ₗ g ≫ f ⊵
ₗ z = f ⊵ₗ y ≫ x ⊴ₗ g
参数：f : w ⟶ x；g : y ⟶ z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem action_exchange {w x : C} {y z : D} (f : w ⟶ x) (g : y ⟶ z) :
    w ⊴ₗ g ≫ f ⊵ₗ z = f ⊵ₗ y ≫ x ⊴ₗ g := by
  simp only [← id_actionHom, ← actionHom_id, ← actionHom_comp, id_comp, comp_id]

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.MonoidalLeftAction.actionHom_def'** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalLeftAction`。
形式化陈述：actionHom_def' {x₁ y₁ : C} {x₂ y₂ : D} (f : x₁ ⟶ y₁) (g : x₂ ⟶ y₂) : f ⊙ₗₘ
 g = x₁ ⊴ₗ g ≫ f ⊵ₗ y₂
参数：f : x₁ ⟶ y₁；g : x₂ ⟶ y₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalLeftAction.actionHom_def`：∀ {C :
 Type u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {inst_
1 : CategoryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalLeftAction.action_exchange`：acti
on_exchange {w x : C} {y z : D} (f : w ⟶ x) (g : y ⟶ z) : w ⊴ₗ g ≫ f ⊵ₗ z = f ⊵ₗ
 y ≫ x ⊴ₗ g
-/
theorem actionHom_def' {x₁ y₁ : C} {x₂ y₂ : D} (f : x₁ ⟶ y₁) (g : x₂ ⟶ y₂) :
    f ⊙ₗₘ g = x₁ ⊴ₗ g ≫ f ⊵ₗ y₂ :=
  action_exchange f g ▸ actionHom_def f g

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.MonoidalLeftAction.actionAssocIso_inv_naturali
ty** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalLeftAction
`。
形式化陈述：actionAssocIso_inv_naturality {c₁ c₂ c₃ c₄ : C} {d₁ d₂ : D} (f : c₁ ⟶ c₂) 
(g : c₃ ⟶ c₄) (h : d₁ ⟶ d₂) : (f ⊙ₗₘ g ⊙ₗₘ h) ≫ (αₗ c₂ c₄ d₂).inv = (αₗ c₁ c₃ d₁
).inv ≫ ((f otimesₘ g) ⊙ₗₘ h)
参数：f : c₁ ⟶ c₂；g : c₃ ⟶ c₄；h : d₁ ⟶ d₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.comp_inv_eq`：comp_inv_eq (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : f ≫ α.inv = g ↔ f = g ≫ α.hom
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `CategoryTheory.Iso.inv_comp_eq`：inv_comp_eq (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : α.inv ≫ f = g ↔ f = α.hom ≫ g
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalLeftAction.actionAssocIso_hom_na
turality`：∀ {C : Type u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, 
u_1} C}   {inst_1 : CategoryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…
-/
theorem actionAssocIso_inv_naturality
    {c₁ c₂ c₃ c₄ : C} {d₁ d₂ : D} (f : c₁ ⟶ c₂) (g : c₃ ⟶ c₄) (h : d₁ ⟶ d₂) :
    (f ⊙ₗₘ g ⊙ₗₘ h) ≫ (αₗ c₂ c₄ d₂).inv =
    (αₗ c₁ c₃ d₁).inv ≫ ((f ⊗ₘ g) ⊙ₗₘ h) := by
  rw [Iso.comp_inv_eq, Category.assoc, Eq.comm, Iso.inv_comp_eq, actionAssocIso_hom_naturality]

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.MonoidalLeftAction.actionUnitIso_inv_naturalit
y** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalLeftAction`
。
形式化陈述：actionUnitIso_inv_naturality {d d' : D} (f : d ⟶ d') : (funₗ d).inv ≫ (𝟙_ 
C) ⊴ₗ f = f ≫ (funₗ d').inv
参数：f : d ⟶ d'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.inv_comp_eq`：inv_comp_eq (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : α.inv ≫ f = g ↔ f = α.hom ≫ g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `CategoryTheory.Iso.comp_inv_eq`：comp_inv_eq (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : f ≫ α.inv = g ↔ f = g ≫ α.hom
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalLeftAction.actionUnitIso_hom_nat
urality`：∀ {C : Type u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, u
_1} C}   {inst_1 : CategoryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…
-/
theorem actionUnitIso_inv_naturality {d d' : D} (f : d ⟶ d') :
      (λₗ d).inv ≫ (𝟙_ C) ⊴ₗ f = f ≫ (λₗ d').inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Eq.comm, Iso.comp_inv_eq, actionUnitIso_hom_naturality]

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.MonoidalLeftAction.actionHomRight_hom_inv** 是 
Mathlib 中的一个定理，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalLeftAction`。
形式化陈述：actionHomRight_hom_inv (x : C) {y z : D} (f : y ≅ z) : x ⊴ₗ f.hom ≫ x ⊴ₗ f
.inv = 𝟙 (x ⊙ₗ y : D)
参数：x : C；f : y ≅ z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalLeftAction.actionHomRight_comp`：
actionHomRight_comp (w : C) {x y z : D} (f : x ⟶ y) (g : y ⟶ z) : w ⊴ₗ (f ≫ g) =
 w ⊴ₗ f ≫ w ⊴ₗ g
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalLeftAction.actionHomRight_id`：∀ 
{C : Type u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {i
nst_1 : CategoryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…
-/
theorem actionHomRight_hom_inv (x : C) {y z : D} (f : y ≅ z) :
    x ⊴ₗ f.hom ≫ x ⊴ₗ f.inv = 𝟙 (x ⊙ₗ y : D) := by
  rw [← actionHomRight_comp, Iso.hom_inv_id, actionHomRight_id]

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.MonoidalLeftAction.hom_inv_actionHomLeft** 是 M
athlib 中的一个定理，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalLeftAction`。
形式化陈述：hom_inv_actionHomLeft {x y : C} (f : x ≅ y) (z : D) : f.hom ⊵ₗ z ≫ f.inv ⊵
ₗ z = 𝟙 (x ⊙ₗ z)
参数：f : x ≅ y；z : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalLeftAction.comp_actionHomLeft`：c
omp_actionHomLeft {w x y : C} (f : w ⟶ x) (g : x ⟶ y) (z : D) : (f ≫ g) ⊵ₗ z = f
 ⊵ₗ z ≫ g ⊵ₗ z
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalLeftAction.id_actionHomLeft`：∀ {
C : Type u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {in
st_1 : CategoryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…
-/
theorem hom_inv_actionHomLeft {x y : C} (f : x ≅ y) (z : D) :
    f.hom ⊵ₗ z ≫ f.inv ⊵ₗ z = 𝟙 (x ⊙ₗ z) := by
  rw [← comp_actionHomLeft, Iso.hom_inv_id, id_actionHomLeft]

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.MonoidalLeftAction.actionHomRight_inv_hom** 是 
Mathlib 中的一个定理，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalLeftAction`。
形式化陈述：actionHomRight_inv_hom (x : C) {y z : D} (f : y ≅ z) : x ⊴ₗ f.inv ≫ x ⊴ₗ f
.hom = 𝟙 (x ⊙ₗ z)
参数：x : C；f : y ≅ z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalLeftAction.actionHomRight_comp`：
actionHomRight_comp (w : C) {x y z : D} (f : x ⟶ y) (g : y ⟶ z) : w ⊴ₗ (f ≫ g) =
 w ⊴ₗ f ≫ w ⊴ₗ g
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalLeftAction.actionHomRight_id`：∀ 
{C : Type u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {i
nst_1 : CategoryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…
-/
theorem actionHomRight_inv_hom (x : C) {y z : D} (f : y ≅ z) :
    x ⊴ₗ f.inv ≫ x ⊴ₗ f.hom = 𝟙 (x ⊙ₗ z) := by
  rw [← actionHomRight_comp, Iso.inv_hom_id, actionHomRight_id]

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.MonoidalLeftAction.inv_hom_actionHomLeft** 是 M
athlib 中的一个定理，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalLeftAction`。
形式化陈述：inv_hom_actionHomLeft {x y : C} (f : x ≅ y) (z : D) : f.inv ⊵ₗ z ≫ f.hom ⊵
ₗ z = 𝟙 (y ⊙ₗ z)
参数：f : x ≅ y；z : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalLeftAction.comp_actionHomLeft`：c
omp_actionHomLeft {w x y : C} (f : w ⟶ x) (g : x ⟶ y) (z : D) : (f ≫ g) ⊵ₗ z = f
 ⊵ₗ z ≫ g ⊵ₗ z
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalLeftAction.id_actionHomLeft`：∀ {
C : Type u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {in
st_1 : CategoryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…
-/
theorem inv_hom_actionHomLeft {x y : C} (f : x ≅ y) (z : D) :
    f.inv ⊵ₗ z ≫ f.hom ⊵ₗ z = 𝟙 (y ⊙ₗ z) := by
  rw [← comp_actionHomLeft, Iso.inv_hom_id, id_actionHomLeft]

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.MonoidalLeftAction.actionHomRight_hom_inv'** 是
 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalLeftAction`。
形式化陈述：actionHomRight_hom_inv' (x : C) {y z : D} (f : y ⟶ z) [IsIso f] : x ⊴ₗ f ≫
 x ⊴ₗ inv f = 𝟙 (x ⊙ₗ y)
参数：x : C；f : y ⟶ z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalLeftAction.actionHomRight_comp`：
actionHomRight_comp (w : C) {x y z : D} (f : x ⟶ y) (g : y ⟶ z) : w ⊴ₗ (f ≫ g) =
 w ⊴ₗ f ≫ w ⊴ₗ g
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalLeftAction.actionHomRight_id`：∀ 
{C : Type u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {i
nst_1 : CategoryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…
-/
theorem actionHomRight_hom_inv' (x : C) {y z : D} (f : y ⟶ z) [IsIso f] :
    x ⊴ₗ f ≫ x ⊴ₗ inv f = 𝟙 (x ⊙ₗ y) := by
  rw [← actionHomRight_comp, IsIso.hom_inv_id, actionHomRight_id]

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.MonoidalLeftAction.hom_inv_actionHomLeft'** 是 
Mathlib 中的一个定理，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalLeftAction`。
形式化陈述：hom_inv_actionHomLeft' {x y : C} (f : x ⟶ y) [IsIso f] (z : D) : f ⊵ₗ z ≫ 
inv f ⊵ₗ z = 𝟙 (x ⊙ₗ z)
参数：f : x ⟶ y；z : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalLeftAction.comp_actionHomLeft`：c
omp_actionHomLeft {w x y : C} (f : w ⟶ x) (g : x ⟶ y) (z : D) : (f ≫ g) ⊵ₗ z = f
 ⊵ₗ z ≫ g ⊵ₗ z
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalLeftAction.id_actionHomLeft`：∀ {
C : Type u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {in
st_1 : CategoryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…
-/
theorem hom_inv_actionHomLeft' {x y : C} (f : x ⟶ y) [IsIso f] (z : D) :
    f ⊵ₗ z ≫ inv f ⊵ₗ z = 𝟙 (x ⊙ₗ z) := by
  rw [← comp_actionHomLeft, IsIso.hom_inv_id, id_actionHomLeft]

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.MonoidalLeftAction.actionHomRight_inv_hom'** 是
 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalLeftAction`。
形式化陈述：actionHomRight_inv_hom' (x : C) {y z : D} (f : y ⟶ z) [IsIso f] : x ⊴ₗ inv
 f ≫ x ⊴ₗ f = 𝟙 (x ⊙ₗ z)
参数：x : C；f : y ⟶ z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalLeftAction.actionHomRight_comp`：
actionHomRight_comp (w : C) {x y z : D} (f : x ⟶ y) (g : y ⟶ z) : w ⊴ₗ (f ≫ g) =
 w ⊴ₗ f ≫ w ⊴ₗ g
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalLeftAction.actionHomRight_id`：∀ 
{C : Type u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {i
nst_1 : CategoryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…
-/
theorem actionHomRight_inv_hom' (x : C) {y z : D} (f : y ⟶ z) [IsIso f] :
    x ⊴ₗ inv f ≫ x ⊴ₗ f = 𝟙 (x ⊙ₗ z) := by
  rw [← actionHomRight_comp, IsIso.inv_hom_id, actionHomRight_id]

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.MonoidalLeftAction.inv_hom_actionHomLeft'** 是 
Mathlib 中的一个定理，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalLeftAction`。
形式化陈述：inv_hom_actionHomLeft' {x y : C} (f : x ⟶ y) [IsIso f] (z : D) : inv f ⊵ₗ 
z ≫ f ⊵ₗ z = 𝟙 (y ⊙ₗ z)
参数：f : x ⟶ y；z : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalLeftAction.comp_actionHomLeft`：c
omp_actionHomLeft {w x y : C} (f : w ⟶ x) (g : x ⟶ y) (z : D) : (f ≫ g) ⊵ₗ z = f
 ⊵ₗ z ≫ g ⊵ₗ z
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalLeftAction.id_actionHomLeft`：∀ {
C : Type u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {in
st_1 : CategoryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…
-/
theorem inv_hom_actionHomLeft' {x y : C} (f : x ⟶ y) [IsIso f] (z : D) :
    inv f ⊵ₗ z ≫ f ⊵ₗ z = 𝟙 (y ⊙ₗ z) := by
  rw [← comp_actionHomLeft, IsIso.inv_hom_id, id_actionHomLeft]
/-
**CategoryTheory.MonoidalCategory.MonoidalLeftAction.isIso_actionHomRight** 是 Ma
thlib 中的一个实例，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalLeftAction`。
形式化陈述：isIso_actionHomRight (x : C) {y z : D} (f : y ⟶ z) [IsIso f] : IsIso (x ⊴ₗ
 f)
参数：x : C；f : y ⟶ z。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalLeftAction.actionHomRight_hom_in
v'`：actionHomRight_hom_inv' (x : C) {y z : D} (f : y ⟶ z) [IsIso f] : x ⊴ₗ f ≫ x
 ⊴ₗ inv f = 𝟙 (x ⊙ₗ y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalLeftAction.actionHomRight_inv_ho
m'`：actionHomRight_inv_hom' (x : C) {y z : D} (f : y ⟶ z) [IsIso f] : x ⊴ₗ inv f
 ≫ x ⊴ₗ f = 𝟙 (x ⊙ₗ z)
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
instance isIso_actionHomRight (x : C) {y z : D} (f : y ⟶ z) [IsIso f] :
    IsIso (x ⊴ₗ f) :=
  ⟨x ⊴ₗ inv f, by simp⟩
/-
**CategoryTheory.MonoidalCategory.MonoidalLeftAction.isIso_actionHomLeft** 是 Mat
hlib 中的一个实例，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalLeftAction`。
形式化陈述：isIso_actionHomLeft {x y : C} (f : x ⟶ y) [IsIso f] (z : D) : IsIso (f ⊵ₗ 
z)
参数：f : x ⟶ y；z : D。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalLeftAction.hom_inv_actionHomLeft
'`：hom_inv_actionHomLeft' {x y : C} (f : x ⟶ y) [IsIso f] (z : D) : f ⊵ₗ z ≫ inv
 f ⊵ₗ z = 𝟙 (x ⊙ₗ z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalLeftAction.inv_hom_actionHomLeft
'`：inv_hom_actionHomLeft' {x y : C} (f : x ⟶ y) [IsIso f] (z : D) : inv f ⊵ₗ z ≫
 f ⊵ₗ z = 𝟙 (y ⊙ₗ z)
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
instance isIso_actionHomLeft {x y : C} (f : x ⟶ y) [IsIso f] (z : D) :
    IsIso (f ⊵ₗ z) :=
  ⟨inv f ⊵ₗ z, by simp⟩
/-
**CategoryTheory.MonoidalCategory.MonoidalLeftAction.isIso_actionHom** 是 Mathlib
 中的一个实例，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalLeftAction`。
形式化陈述：isIso_actionHom {x y : C} {x' y' : D} (f : x ⟶ y) (g : x' ⟶ y') [IsIso f] 
[IsIso g] : IsIso (f ⊙ₗₘ g)
参数：f : x ⟶ y；g : x' ⟶ y'。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用引理 `CategoryTheory.MonoidalCategory.MonoidalLeftAction.actionHom_id`：actionH
om_id {c c' : C} (f : c ⟶ c') (d : D) : f ⊙ₗₘ (𝟙 d) = f ⊵ₗ d
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalLeftAction.id_actionHomLeft`：∀ {
C : Type u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {in
st_1 : CategoryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
instance isIso_actionHom {x y : C} {x' y' : D}
    (f : x ⟶ y) (g : x' ⟶ y') [IsIso f] [IsIso g] :
    IsIso (f ⊙ₗₘ g) :=
  ⟨(inv f) ⊙ₗₘ (inv g), by simp [← actionHom_comp]⟩

@[simp]
/-
**CategoryTheory.MonoidalCategory.MonoidalLeftAction.inv_actionHomLeft** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalLeftAction`。
形式化陈述：inv_actionHomLeft {x y : C} (f : x ⟶ y) [IsIso f] (z : D) : inv (f ⊵ₗ z) =
 inv f ⊵ₗ z
参数：f : x ⟶ y；z : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsIso.inv_eq_of_hom_inv_id`：inv_eq_of_hom_inv_id {f : X ⟶
 Y} [IsIso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g = 𝟙 X) : inv f = g
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalLeftAction.hom_inv_actionHomLeft
'`：hom_inv_actionHomLeft' {x y : C} (f : x ⟶ y) [IsIso f] (z : D) : f ⊵ₗ z ≫ inv
 f ⊵ₗ z = 𝟙 (x ⊙ₗ z)
-/
lemma inv_actionHomLeft {x y : C} (f : x ⟶ y) [IsIso f] (z : D) :
    inv (f ⊵ₗ z) = inv f ⊵ₗ z :=
  IsIso.inv_eq_of_hom_inv_id <| hom_inv_actionHomLeft' f z

@[simp]
/-
**CategoryTheory.MonoidalCategory.MonoidalLeftAction.inv_actionHomRight** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalLeftAction`。
形式化陈述：inv_actionHomRight (x : C) {y z : D} (f : y ⟶ z) [IsIso f] : inv (x ⊴ₗ f) 
= x ⊴ₗ inv f
参数：x : C；f : y ⟶ z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsIso.inv_eq_of_hom_inv_id`：inv_eq_of_hom_inv_id {f : X ⟶
 Y} [IsIso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g = 𝟙 X) : inv f = g
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalLeftAction.actionHomRight_hom_in
v'`：actionHomRight_hom_inv' (x : C) {y z : D} (f : y ⟶ z) [IsIso f] : x ⊴ₗ f ≫ x
 ⊴ₗ inv f = 𝟙 (x ⊙ₗ y)
-/
lemma inv_actionHomRight (x : C) {y z : D} (f : y ⟶ z) [IsIso f] :
    inv (x ⊴ₗ f) = x ⊴ₗ inv f :=
  IsIso.inv_eq_of_hom_inv_id <| actionHomRight_hom_inv' x f

@[simp]
/-
**CategoryTheory.MonoidalCategory.MonoidalLeftAction.inv_actionHom** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalLeftAction`。
形式化陈述：inv_actionHom {x y : C} {x' y' : D} (f : x ⟶ y) (g : x' ⟶ y') [IsIso f] [I
sIso g] : inv (f ⊙ₗₘ g) = (inv f) ⊙ₗₘ (inv g)
参数：f : x ⟶ y；g : x' ⟶ y'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsIso.inv_eq_of_hom_inv_id`：inv_eq_of_hom_inv_id {f : X ⟶
 Y} [IsIso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g = 𝟙 X) : inv f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用引理 `CategoryTheory.MonoidalCategory.MonoidalLeftAction.actionHom_id`：actionH
om_id {c c' : C} (f : c ⟶ c') (d : D) : f ⊙ₗₘ (𝟙 d) = f ⊵ₗ d
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalLeftAction.id_actionHomLeft`：∀ {
C : Type u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {in
st_1 : CategoryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inv_actionHom {x y : C} {x' y' : D}
    (f : x ⟶ y) (g : x' ⟶ y') [IsIso f] [IsIso g] :
    inv (f ⊙ₗₘ g) = (inv f) ⊙ₗₘ (inv g) :=
  IsIso.inv_eq_of_hom_inv_id <| by simp [← actionHom_comp]

section

variable (C D)
/-- Bundle the action of `C` on `D` as a functor `C ⥤ D ⥤ D`. -/
@[simps!]
/-
**CategoryTheory.MonoidalCategory.MonoidalLeftAction.curriedAction** 是 Mathlib 中
的一个定义，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalLeftAction`。
形式化陈述：curriedAction : C ⥤ D ⥤ D where obj x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bundle the action of `C` on `D` as a functor `C ⥤ D ⥤ D`.
-/
def curriedAction : C ⥤ D ⥤ D where
  obj x :=
    { obj y := x ⊙ₗ y
      map f := x ⊴ₗ f }
  map f :=
    { app y := f ⊵ₗ y
      naturality _ _ _ := by simp [action_exchange] }

variable {C} in
/-- Bundle `d ↦ c ⊙ₗ d` as a functor. -/
/-
**CategoryTheory.MonoidalCategory.MonoidalLeftAction.actionLeft** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalLeftAction`。
形式化陈述：{C : Type u_1} →   (D : Type u_2) →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         [i
nst_2 : CategoryTheory.MonoidalCategory C] →           [CategoryTheory.MonoidalC
ategory.MonoidalLeftAction C D] → C → CategoryTheory.Functor D D
参数：D : Type u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bundle `d ↦ c ⊙ₗ d` as a functor.
-/
abbrev actionLeft (c : C) : D ⥤ D := curriedAction C D |>.obj c

variable {D} in
/-- Bundle `c ↦ c ⊙ₗ d` as a functor. -/
/-
**CategoryTheory.MonoidalCategory.MonoidalLeftAction.actionRight** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalLeftAction`。
形式化陈述：(C : Type u_1) →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         [i
nst_2 : CategoryTheory.MonoidalCategory C] →           [CategoryTheory.MonoidalC
ategory.MonoidalLeftAction C D] → D → CategoryTheory.Functor C D
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bundle `c ↦ c ⊙ₗ d` as a functor.
-/
abbrev actionRight (d : D) : C ⥤ D := curriedAction C D |>.flip.obj d

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Bundle `αₗ _ _ _` as an isomorphism of trifunctors. -/
@[simps!]
/-
**CategoryTheory.MonoidalCategory.MonoidalLeftAction.actionAssocNatIso** 是 Mathl
ib 中的一个定义，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalLeftAction`。
形式化陈述：actionAssocNatIso : bifunctorComp₁₂ (curriedTensor C) (curriedAction C D) 
≅ bifunctorComp₂₃ (curriedAction C D) (curriedAction C D)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bundle `αₗ _ _ _` as an isomorphism of trifunctors.
-/
def actionAssocNatIso :
    bifunctorComp₁₂ (curriedTensor C) (curriedAction C D) ≅
    bifunctorComp₂₃ (curriedAction C D) (curriedAction C D) :=
  NatIso.ofComponents fun _ ↦
    NatIso.ofComponents fun _ ↦
     NatIso.ofComponents fun _ ↦ αₗ _ _ _

set_option backward.defeqAttrib.useBackward true in
/-- Bundle `λₗ _` as an isomorphism of functors. -/
@[simps!]
/-
**CategoryTheory.MonoidalCategory.MonoidalLeftAction.actionUnitNatIso** 是 Mathli
b 中的一个定义，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalLeftAction`。
形式化陈述：actionUnitNatIso : actionLeft D (𝟙_ C) ≅ 𝟭 D
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bundle `λₗ _` as an isomorphism of functors.
-/
def actionUnitNatIso : actionLeft D (𝟙_ C) ≅ 𝟭 D := NatIso.ofComponents (λₗ ·)

end

end MonoidalLeftAction

/-- A class that carries the non-Prop data required to define a right action of
a monoidal category `C` on a category `D`, to set up notations. -/
/-
**CategoryTheory.MonoidalCategory.MonoidalRightActionStruct** 是 Mathlib 中的一个类，位于
命名空间 `CategoryTheory.MonoidalCategory`。
形式化陈述：MonoidalRightActionStruct [MonoidalCategoryStruct C] where /-- The right a
ction on objects. This is denoted `d ⊙ᵣ c`. -/ actionObj : D -> C -> D /-- The r
ight action of a map `f : c ⟶ c'` in `C` on an object `d` in `D`. If we are to c
onsider the action as a functor `Α : C ⥤ D ⥤ D`, this is `(Α.map f).app d`. This
 is denoted `d ⊴ᵣ f`. -/ actionHomRight (d : D) {c c' : C} (f : c ⟶ c') : action
Obj d c ⟶ actionObj d c' /-- The action of an object `c : C` on a map `f : d ⟶ d
'` in `D`. If we are to co
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A class that carries the non-Prop data required to define a right action of
a monoidal category `C` on a category `D`, to set up notations. -/
-/
class MonoidalRightActionStruct [MonoidalCategoryStruct C] where
  /-- The right action on objects. This is denoted `d ⊙ᵣ c`. -/
  actionObj : D → C → D
  /-- The right action of a map `f : c ⟶ c'` in `C` on an object `d` in `D`.
  If we are to consider the action as a functor `Α : C ⥤ D ⥤ D`,
  this is `(Α.map f).app d`. This is denoted `d ⊴ᵣ f`. -/
  actionHomRight (d : D) {c c' : C} (f : c ⟶ c') :
    actionObj d c ⟶ actionObj d c'
  /-- The action of an object `c : C` on a map `f : d ⟶ d'` in `D`.
  If we are to consider the action as a functor `Α : C ⥤ D ⥤ D`,
  this is `(Α.obj c).map f`. This is denoted `f ⊵ᵣ c`. -/
  actionHomLeft {d d' : D} (f : d ⟶ d') (c : C) :
    actionObj d c ⟶ actionObj d' c
  /-- The action of a pair of maps `f : c ⟶ c'` and `d ⟶ d'`. By default,
  this is defined in terms of `actionHomLeft` and `actionHomRight`. -/
  actionHom {c c' : C} {d d' : D} (f : d ⟶ d') (g : c ⟶ c') :
    actionObj d c ⟶ actionObj d' c' := actionHomLeft f c ≫ actionHomRight d' g
  /-- The structural isomorphism `d ⊙ᵣ (c ⊗ c') ≅ (d ⊙ᵣ c) ⊙ᵣ c'`. -/
  actionAssocIso (d : D) (c c' : C) :
    actionObj d (c ⊗ c') ≅ actionObj (actionObj d c) c'
  /-- The structural isomorphism between `d ⊙ᵣ 𝟙_ C` and `d`. -/
  actionUnitIso (d : D) : actionObj d (𝟙_ C) ≅ d

namespace MonoidalRightAction

export MonoidalRightActionStruct
  (actionObj actionHomLeft actionHomRight actionHom actionAssocIso
    actionUnitIso)

-- infix priorities are aligned with the ones from `MonoidalCategoryStruct`.

/-- Notation for `actionObj`, the action of `C` on `D`. -/
scoped infixr:70 " ⊙ᵣ " => MonoidalRightActionStruct.actionObj

/-- Notation for `actionHomLeft`, the action of `D` on morphisms in `C`. -/
scoped infixr:81 " ⊵ᵣ " => MonoidalRightActionStruct.actionHomLeft

/-- Notation for `actionHomRight`, the action of morphism in `D` on `C`. -/
scoped infixr:81 " ⊴ᵣ " => MonoidalRightActionStruct.actionHomRight

/-- Notation for `actionHom`, the bifunctorial action of morphisms in `C` and
`D` on `- ⊙ -`. -/
scoped infixr:70 " ⊙ᵣₘ " => MonoidalRightActionStruct.actionHom

/-- Notation for `actionAssocIso`, the structural isomorphism
`- ⊙ᵣ (- ⊗ -) ≅ (- ⊙ᵣ -) ⊙ᵣ -`. -/
scoped notation "αᵣ " => MonoidalRightActionStruct.actionAssocIso

/-- Notation for `actionUnitIso`, the structural isomorphism `- ⊙ᵣ 𝟙_ C  ≅ -`. -/
scoped notation "ρᵣ " => MonoidalRightActionStruct.actionUnitIso
/-- Notation for `actionUnitIso`, the structural isomorphism `- ⊙ᵣ 𝟙_ C  ≅ -`,
allowing one to specify the acting category. -/
scoped notation "ρᵣ[" J "]" => MonoidalRightActionStruct.actionUnitIso (C := J)

end MonoidalRightAction

open scoped MonoidalRightAction in
/-- A `MonoidalRightAction C D` is the data of:
- For every object `c : C` and `d : D`, an object `c ⊙ᵣ d` of `D`.
- For every morphism `f : (c : C) ⟶ c'` and every `d : D`, a morphism
  `f ⊵ᵣ d : c ⊙ᵣ d ⟶ c' ⊙ᵣ d`.
- For every morphism `f : (d : D) ⟶ d'` and every `c : C`, a morphism
  `c ⊴ᵣ f : c ⊙ᵣ d ⟶ c ⊙ᵣ d'`.
- For every pair of morphisms `f : (c : C) ⟶ c'` and
  `f : (d : D) ⟶ d'`, a morphism `f ⊙ᵣₘ f' : c ⊙ᵣ d ⟶ c' ⊙ᵣ d'`.
- A structure isomorphism `αᵣ c c' d : c ⊗ c' ⊙ᵣ d ≅ c ⊙ᵣ c' ⊙ᵣ d`.
- A structure isomorphism `ρᵣ d : (𝟙_ C) ⊙ᵣ d ≅ d`.

Furthermore, we require identities that turn `- ⊙ᵣ -` into a bifunctor,
ensure naturality of `αᵣ` and `ρᵣ`, and ensure compatibilities with
the associator and unitor isomorphisms in `C`. -/
/-
**CategoryTheory.MonoidalCategory.MonoidalRightAction** 是 Mathlib 中的一个类，位于命名空间 `
CategoryTheory.MonoidalCategory`。
形式化陈述：MonoidalRightAction [MonoidalCategory C] extends MonoidalRightActionStruct
 C D where actionHom_def {c c' : C} {d d' : D} (f : d ⟶ d') (g : c ⟶ c') : f ⊙ᵣₘ
 g = f ⊵ᵣ c ≫ d' ⊴ᵣ g
参数：f : d ⟶ d'；g : c ⟶ c'。
继承自：MonoidalRightActionStruct C D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `MonoidalRightAction C D` is the data of:
- For every object `c : C` and `d : D`, an object `c ⊙ᵣ d` of `D`.
- For every morphism `f : (c : C) ⟶ c'` and every `d : D`, a morphism
  `f ⊵ᵣ d : c ⊙ᵣ d ⟶ c' ⊙ᵣ d`.
- For every morphism `f : (d : D) ⟶ d'` and every `c : C`, a morphism
  `c ⊴ᵣ f : c ⊙ᵣ d ⟶ c ⊙ᵣ d'`.
- For every pair of morphisms `f : (c : C) ⟶ c'` and
  `f : (d : D) ⟶ d'`, a morphism `f ⊙ᵣₘ f' : c ⊙ᵣ d ⟶ c' ⊙ᵣ d'`.
- A structure isomorphism `αᵣ c c' d : c ⊗ c' ⊙ᵣ d ≅ c ⊙ᵣ c' ⊙ᵣ d`.
- A structure isomorphism `ρᵣ d : (𝟙_ C) ⊙ᵣ d ≅ d`.

Furthermore, we require identities that turn `- ⊙ᵣ -` into a bifunctor,
ensure naturality of `αᵣ` and `ρᵣ`, and ensure compatibilities with
the associator and unitor isomorphisms in `C`.
-/
class MonoidalRightAction [MonoidalCategory C] extends
    MonoidalRightActionStruct C D where
  actionHom_def {c c' : C} {d d' : D} (f : d ⟶ d') (g : c ⟶ c') :
      f ⊙ᵣₘ g = f ⊵ᵣ c ≫ d' ⊴ᵣ g := by
    cat_disch
  actionHomRight_id (c : C) (d : D) : d ⊴ᵣ 𝟙 c = 𝟙 (d ⊙ᵣ c) := by cat_disch
  id_actionHomLeft (c : C) (d : D) : 𝟙 d ⊵ᵣ c = 𝟙 (d ⊙ᵣ c) := by cat_disch
  actionHom_comp
      {c c' c'' : C} {d d' d'' : D} (f₁ : d ⟶ d') (f₂ : d' ⟶ d'')
      (g₁ : c ⟶ c') (g₂ : c' ⟶ c'') :
      (f₁ ≫ f₂) ⊙ᵣₘ (g₁ ≫ g₂) = (f₁ ⊙ᵣₘ g₁) ≫ (f₂ ⊙ᵣₘ g₂) := by
    cat_disch
  actionAssocIso_hom_naturality
      {d₁ d₂ : D} {c₁ c₂ c₃ c₄ : C} (f : d₁ ⟶ d₂) (g : c₁ ⟶ c₂) (h : c₃ ⟶ c₄) :
      (f ⊙ᵣₘ g ⊗ₘ h) ≫ (αᵣ d₂ c₂ c₄).hom =
        (αᵣ d₁ c₁ c₃).hom ≫ ((f ⊙ᵣₘ g) ⊙ᵣₘ h) := by
    cat_disch
  actionUnitIso_hom_naturality {d d' : D} (f : d ⟶ d') :
      (ρᵣ d).hom ≫ f = f ⊵ᵣ (𝟙_ C) ≫ (ρᵣ d').hom := by
    cat_disch
  actionHomRight_whiskerRight {c' c'' : C} (f : c' ⟶ c'') (c : C) (d : D) :
     d ⊴ᵣ (f ▷ c) = (αᵣ _ _ _).hom ≫ ((d ⊴ᵣ f) ⊵ᵣ c) ≫ (αᵣ _ _ _).inv := by
    cat_disch
  whiskerRight_actionHomLeft (c : C) {c' c'' : C} (f : c' ⟶ c'') (d : D) :
     d ⊴ᵣ (c ◁ f) = (αᵣ d c c').hom ≫ (d ⊙ᵣ c) ⊴ᵣ f ≫ (αᵣ d c c'').inv := by
    cat_disch
  actionHom_associator (c₁ c₂ c₃ : C) (d : D) :
      d ⊴ᵣ (α_ c₁ c₂ c₃).hom ≫ (αᵣ d c₁ (c₂ ⊗ c₃)).hom ≫
        (αᵣ (d ⊙ᵣ c₁ : D) c₂ c₃).hom =
      (αᵣ d (c₁ ⊗ c₂ : C) c₃).hom ≫ (αᵣ d c₁ c₂).hom ⊵ᵣ c₃ := by
    cat_disch
  actionHom_leftUnitor (c : C) (d : D) :
      d ⊴ᵣ (λ_ c).hom = (αᵣ _ _ _).hom ≫ (ρᵣ _).hom ⊵ᵣ c := by
    cat_disch
  actionHom_rightUnitor (c : C) (d : D) :
      d ⊴ᵣ (ρ_ c).hom = (αᵣ _ _ _).hom ≫ (ρᵣ _).hom := by
    cat_disch

attribute [reassoc] MonoidalRightAction.actionHom_def
attribute [reassoc, simp] MonoidalRightAction.id_actionHomLeft
attribute [reassoc, simp] MonoidalRightAction.actionHomRight_id
attribute [reassoc, simp] MonoidalRightAction.actionHomRight_whiskerRight
attribute [simp, reassoc] MonoidalRightAction.actionHom_comp
attribute [reassoc] MonoidalRightAction.actionAssocIso_hom_naturality
attribute [reassoc] MonoidalRightAction.actionUnitIso_hom_naturality
attribute [reassoc (attr := simp)] MonoidalRightAction.actionHom_associator
attribute [simp, reassoc] MonoidalRightAction.actionHom_leftUnitor
attribute [simp, reassoc] MonoidalRightAction.actionHom_rightUnitor

/-- A monoidal category acts on itself through the tensor product. -/
@[simps!]
/-
**CategoryTheory.MonoidalCategory.selRightfAction** 是 Mathlib 中的一个实例，位于命名空间 `Cat
egoryTheory.MonoidalCategory`。
形式化陈述：selRightfAction [MonoidalCategory C] : MonoidalRightAction C C where actio
nObj x y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A monoidal category acts on itself through the tensor product.
-/
instance selRightfAction [MonoidalCategory C] : MonoidalRightAction C C where
  actionObj x y := x ⊗ y
  actionHom f g := f ⊗ₘ g
  actionUnitIso x := ρ_ x
  actionAssocIso x y z := α_ x y z |>.symm
  actionHomLeft f x := f ▷ x
  actionHomRight x _ _ f := x ◁ f
  actionHom_def := by simp [tensorHom_def]

namespace MonoidalRightAction

open Category

variable {C D} [MonoidalCategory C] [MonoidalRightAction C D]

-- Simp normal forms are aligned with the ones in `MonoidalCategory`.

@[simp]
/-
**CategoryTheory.MonoidalCategory.MonoidalRightAction.actionHom_id** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalRightAction`。
形式化陈述：actionHom_id {d d' : D} (f : d ⟶ d') (c : C) : f ⊙ᵣₘ (𝟙 c) = f ⊵ᵣ c
参数：f : d ⟶ d'；c : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalRightAction.actionHom_def`：∀ {C 
: Type u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {inst
_1 : CategoryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalRightAction.actionHomRight_id`：∀
 {C : Type u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {
inst_1 : CategoryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma actionHom_id {d d' : D} (f : d ⟶ d') (c : C) :
    f ⊙ᵣₘ (𝟙 c) = f ⊵ᵣ c := by
  simp [actionHom_def]

@[simp]
/-
**CategoryTheory.MonoidalCategory.MonoidalRightAction.id_actionHom** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalRightAction`。
形式化陈述：id_actionHom (d : D) {c c' : C} (f : c ⟶ c') : (𝟙 d) ⊙ᵣₘ f = d ⊴ᵣ f
参数：d : D；f : c ⟶ c'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalRightAction.actionHom_def`：∀ {C 
: Type u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {inst
_1 : CategoryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalRightAction.id_actionHomLeft`：∀ 
{C : Type u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {i
nst_1 : CategoryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma id_actionHom (d : D) {c c' : C} (f : c ⟶ c') :
    (𝟙 d) ⊙ᵣₘ f = d ⊴ᵣ f := by
  simp [actionHom_def]

@[reassoc, simp]
/-
**CategoryTheory.MonoidalCategory.MonoidalRightAction.actionHomRight_comp** 是 Ma
thlib 中的一个定理，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalRightAction`。
形式化陈述：actionHomRight_comp (w : D) {x y z : C} (f : x ⟶ y) (g : y ⟶ z) : w ⊴ᵣ (f 
≫ g) = w ⊴ᵣ f ≫ w ⊴ᵣ g
参数：w : D；f : x ⟶ y；g : y ⟶ z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem actionHomRight_comp (w : D) {x y z : C} (f : x ⟶ y) (g : y ⟶ z) :
    w ⊴ᵣ (f ≫ g) = w ⊴ᵣ f ≫ w ⊴ᵣ g := by
  simp [← id_actionHom, ← actionHom_comp]

@[reassoc, simp]
/-
**CategoryTheory.MonoidalCategory.MonoidalRightAction.unit_actionHomRight** 是 Ma
thlib 中的一个定理，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalRightAction`。
形式化陈述：unit_actionHomRight {x y : D} (f : x ⟶ y) : f ⊵ᵣ (𝟙_ C) = (ρᵣ x).hom ≫ f ≫
 (ρᵣ y).inv
参数：f : x ⟶ y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalRightAction.actionUnitIso_hom_na
turality`：∀ {C : Type u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, 
u_1} C}   {inst_1 : CategoryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem unit_actionHomRight {x y : D} (f : x ⟶ y) :
    f ⊵ᵣ (𝟙_ C) = (ρᵣ x).hom ≫ f ≫ (ρᵣ y).inv := by
  rw [← Category.assoc, actionUnitIso_hom_naturality]
  simp

@[reassoc, simp]
/-
**CategoryTheory.MonoidalCategory.MonoidalRightAction.actionHomLeft_tensor** 是 M
athlib 中的一个定理，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalRightAction`。
形式化陈述：actionHomLeft_tensor {z z' : D} (f : z ⟶ z') (x y : C) : (f ⊵ᵣ (x otimes y
)) = (αᵣ z x y).hom ≫ (f ⊵ᵣ x) ⊵ᵣ y ≫ (αᵣ z' x y).inv
参数：f : z ⟶ z'；x y : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalRightAction.actionAssocIso_hom_n
aturality`：∀ {C : Type u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1,
 u_1} C}   {inst_1 : CategoryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `CategoryTheory.MonoidalCategory.MonoidalRightAction.actionHom_id`：action
Hom_id {d d' : D} (f : d ⟶ d') (c : C) : f ⊙ᵣₘ (𝟙 c) = f ⊵ᵣ c
· 使用定理 `CategoryTheory.MonoidalCategory.tensorHom_id`：tensorHom_id {X₁ X₂ : C} (
f : X₁ ⟶ X₂) (Y : C) : f otimesₘ 𝟙 Y = f ▷ Y
· 使用定理 `CategoryTheory.MonoidalCategory.id_whiskerRight`：∀ {C : Type u} {𝒞 : Cat
egoryTheory.Category.{v, u} C} [self : CategoryTheory.MonoidalCategory C] (X Y :
 C),   CategoryTheory.MonoidalCategor…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem actionHomLeft_tensor {z z' : D} (f : z ⟶ z') (x y : C) :
    (f ⊵ᵣ (x ⊗ y)) = (αᵣ z x y).hom ≫ (f ⊵ᵣ x) ⊵ᵣ y ≫ (αᵣ z' x y).inv := by
  simp only [← actionHom_id]
  rw [← Category.assoc, ← actionAssocIso_hom_naturality]
  simp

@[reassoc, simp]
/-
**CategoryTheory.MonoidalCategory.MonoidalRightAction.comp_actionHomLeft** 是 Mat
hlib 中的一个定理，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalRightAction`。
形式化陈述：comp_actionHomLeft {w x y : D} (f : w ⟶ x) (g : x ⟶ y) (z : C) : (f ≫ g) ⊵
ᵣ z = f ⊵ᵣ z ≫ g ⊵ᵣ z
参数：f : w ⟶ x；g : x ⟶ y；z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp_actionHomLeft {w x y : D} (f : w ⟶ x) (g : x ⟶ y) (z : C) :
    (f ≫ g) ⊵ᵣ z = f ⊵ᵣ z ≫ g ⊵ᵣ z := by
  simp only [← actionHom_id, ← actionHom_comp, Category.id_comp]

@[reassoc, simp]
/-
**CategoryTheory.MonoidalCategory.MonoidalRightAction.action_actionHomRight** 是 
Mathlib 中的一个定理，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalRightAction`。
形式化陈述：action_actionHomRight (y : D) (z : C) {x x' : C} (f : x ⟶ x') : (y ⊙ᵣ z) ⊴
ᵣ f = (αᵣ y z x).inv ≫ y ⊴ᵣ (z ◁ f) ≫ (αᵣ y z x').hom
参数：y : D；z : C；f : x ⟶ x'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalRightAction.whiskerRight_actionH
omLeft`：∀ {C : Type u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_
1} C}   {inst_1 : CategoryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem action_actionHomRight (y : D) (z : C) {x x' : C} (f : x ⟶ x') :
    (y ⊙ᵣ z) ⊴ᵣ f = (αᵣ y z x).inv ≫ y ⊴ᵣ (z ◁ f) ≫ (αᵣ y z x').hom := by
  simp [whiskerRight_actionHomLeft]

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.MonoidalRightAction.action_exchange** 是 Mathli
b 中的一个定理，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalRightAction`。
形式化陈述：action_exchange {w x : D} {y z : C} (f : w ⟶ x) (g : y ⟶ z) : w ⊴ᵣ g ≫ f ⊵
ᵣ z = f ⊵ᵣ y ≫ x ⊴ᵣ g
参数：f : w ⟶ x；g : y ⟶ z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem action_exchange {w x : D} {y z : C} (f : w ⟶ x) (g : y ⟶ z) :
    w ⊴ᵣ g ≫ f ⊵ᵣ z = f ⊵ᵣ y ≫ x ⊴ᵣ g := by
  simp only [← id_actionHom, ← actionHom_id, ← actionHom_comp, id_comp, comp_id]

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.MonoidalRightAction.actionHom_def'** 是 Mathlib
 中的一个定理，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalRightAction`。
形式化陈述：actionHom_def' {x₁ y₁ : D} {x₂ y₂ : C} (f : x₁ ⟶ y₁) (g : x₂ ⟶ y₂) : f ⊙ᵣₘ
 g = x₁ ⊴ᵣ g ≫ f ⊵ᵣ y₂
参数：f : x₁ ⟶ y₁；g : x₂ ⟶ y₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalRightAction.actionHom_def`：∀ {C 
: Type u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {inst
_1 : CategoryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalRightAction.action_exchange`：act
ion_exchange {w x : D} {y z : C} (f : w ⟶ x) (g : y ⟶ z) : w ⊴ᵣ g ≫ f ⊵ᵣ z = f ⊵
ᵣ y ≫ x ⊴ᵣ g
-/
theorem actionHom_def' {x₁ y₁ : D} {x₂ y₂ : C} (f : x₁ ⟶ y₁) (g : x₂ ⟶ y₂) :
    f ⊙ᵣₘ g = x₁ ⊴ᵣ g ≫ f ⊵ᵣ y₂ :=
  action_exchange f g ▸ actionHom_def f g

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.MonoidalRightAction.actionAssocIso_inv_natural
ity** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalRightActi
on`。
形式化陈述：actionAssocIso_inv_naturality {d₁ d₂ : D} {c₁ c₂ c₃ c₄ : C} (f : d₁ ⟶ d₂) 
(g : c₁ ⟶ c₂) (h : c₃ ⟶ c₄) : ((f ⊙ᵣₘ g) ⊙ᵣₘ h) ≫ (αᵣ d₂ c₂ c₄).inv = (αᵣ d₁ c₁ 
c₃).inv ≫ (f ⊙ᵣₘ g otimesₘ h)
参数：f : d₁ ⟶ d₂；g : c₁ ⟶ c₂；h : c₃ ⟶ c₄。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.comp_inv_eq`：comp_inv_eq (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : f ≫ α.inv = g ↔ f = g ≫ α.hom
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `CategoryTheory.Iso.inv_comp_eq`：inv_comp_eq (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : α.inv ≫ f = g ↔ f = α.hom ≫ g
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalRightAction.actionAssocIso_hom_n
aturality`：∀ {C : Type u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1,
 u_1} C}   {inst_1 : CategoryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…
-/
theorem actionAssocIso_inv_naturality
    {d₁ d₂ : D} {c₁ c₂ c₃ c₄ : C} (f : d₁ ⟶ d₂) (g : c₁ ⟶ c₂) (h : c₃ ⟶ c₄) :
    ((f ⊙ᵣₘ g) ⊙ᵣₘ h) ≫ (αᵣ d₂ c₂ c₄).inv =
    (αᵣ d₁ c₁ c₃).inv ≫ (f ⊙ᵣₘ g ⊗ₘ h) := by
  rw [Iso.comp_inv_eq, Category.assoc, Eq.comm, Iso.inv_comp_eq, actionAssocIso_hom_naturality]

@[reassoc]
/-
**CategoryTheory.MonoidalCategory.MonoidalRightAction.actionUnitIso_inv_naturali
ty** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalRightActio
n`。
形式化陈述：actionUnitIso_inv_naturality {d d' : D} (f : d ⟶ d') : (ρᵣ d).inv ≫ f ⊵ᵣ (
𝟙_ C) = f ≫ (ρᵣ d').inv
参数：f : d ⟶ d'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.inv_comp_eq`：inv_comp_eq (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : α.inv ≫ f = g ↔ f = α.hom ≫ g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `CategoryTheory.Iso.comp_inv_eq`：comp_inv_eq (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : f ≫ α.inv = g ↔ f = g ≫ α.hom
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalRightAction.actionUnitIso_hom_na
turality`：∀ {C : Type u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, 
u_1} C}   {inst_1 : CategoryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…
-/
theorem actionUnitIso_inv_naturality {d d' : D} (f : d ⟶ d') :
      (ρᵣ d).inv ≫ f ⊵ᵣ (𝟙_ C) = f ≫ (ρᵣ d').inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Eq.comm, Iso.comp_inv_eq, actionUnitIso_hom_naturality]

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.MonoidalRightAction.actionHomRight_hom_inv** 是
 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalRightAction`。
形式化陈述：actionHomRight_hom_inv (x : D) {y z : C} (f : y ≅ z) : x ⊴ᵣ f.hom ≫ x ⊴ᵣ f
.inv = 𝟙 (x ⊙ᵣ y : D)
参数：x : D；f : y ≅ z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalRightAction.actionHomRight_comp`
：actionHomRight_comp (w : D) {x y z : C} (f : x ⟶ y) (g : y ⟶ z) : w ⊴ᵣ (f ≫ g) 
= w ⊴ᵣ f ≫ w ⊴ᵣ g
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalRightAction.actionHomRight_id`：∀
 {C : Type u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {
inst_1 : CategoryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…
-/
theorem actionHomRight_hom_inv (x : D) {y z : C} (f : y ≅ z) :
    x ⊴ᵣ f.hom ≫ x ⊴ᵣ f.inv = 𝟙 (x ⊙ᵣ y : D) := by
  rw [← actionHomRight_comp, Iso.hom_inv_id, actionHomRight_id]

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.MonoidalRightAction.hom_inv_actionHomLeft** 是 
Mathlib 中的一个定理，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalRightAction`。
形式化陈述：hom_inv_actionHomLeft {x y : D} (f : x ≅ y) (z : C) : f.hom ⊵ᵣ z ≫ f.inv ⊵
ᵣ z = 𝟙 (x ⊙ᵣ z)
参数：f : x ≅ y；z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalRightAction.comp_actionHomLeft`：
comp_actionHomLeft {w x y : D} (f : w ⟶ x) (g : x ⟶ y) (z : C) : (f ≫ g) ⊵ᵣ z = 
f ⊵ᵣ z ≫ g ⊵ᵣ z
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalRightAction.id_actionHomLeft`：∀ 
{C : Type u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {i
nst_1 : CategoryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…
-/
theorem hom_inv_actionHomLeft {x y : D} (f : x ≅ y) (z : C) :
    f.hom ⊵ᵣ z ≫ f.inv ⊵ᵣ z = 𝟙 (x ⊙ᵣ z) := by
  rw [← comp_actionHomLeft, Iso.hom_inv_id, id_actionHomLeft]

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.MonoidalRightAction.actionHomRight_inv_hom** 是
 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalRightAction`。
形式化陈述：actionHomRight_inv_hom (x : D) {y z : C} (f : y ≅ z) : x ⊴ᵣ f.inv ≫ x ⊴ᵣ f
.hom = 𝟙 (x ⊙ᵣ z)
参数：x : D；f : y ≅ z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalRightAction.actionHomRight_comp`
：actionHomRight_comp (w : D) {x y z : C} (f : x ⟶ y) (g : y ⟶ z) : w ⊴ᵣ (f ≫ g) 
= w ⊴ᵣ f ≫ w ⊴ᵣ g
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalRightAction.actionHomRight_id`：∀
 {C : Type u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {
inst_1 : CategoryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…
-/
theorem actionHomRight_inv_hom (x : D) {y z : C} (f : y ≅ z) :
    x ⊴ᵣ f.inv ≫ x ⊴ᵣ f.hom = 𝟙 (x ⊙ᵣ z) := by
  rw [← actionHomRight_comp, Iso.inv_hom_id, actionHomRight_id]

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.MonoidalRightAction.inv_hom_actionHomLeft** 是 
Mathlib 中的一个定理，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalRightAction`。
形式化陈述：inv_hom_actionHomLeft {x y : D} (f : x ≅ y) (z : C) : f.inv ⊵ᵣ z ≫ f.hom ⊵
ᵣ z = 𝟙 (y ⊙ᵣ z)
参数：f : x ≅ y；z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalRightAction.comp_actionHomLeft`：
comp_actionHomLeft {w x y : D} (f : w ⟶ x) (g : x ⟶ y) (z : C) : (f ≫ g) ⊵ᵣ z = 
f ⊵ᵣ z ≫ g ⊵ᵣ z
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalRightAction.id_actionHomLeft`：∀ 
{C : Type u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {i
nst_1 : CategoryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…
-/
theorem inv_hom_actionHomLeft {x y : D} (f : x ≅ y) (z : C) :
    f.inv ⊵ᵣ z ≫ f.hom ⊵ᵣ z = 𝟙 (y ⊙ᵣ z) := by
  rw [← comp_actionHomLeft, Iso.inv_hom_id, id_actionHomLeft]

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.MonoidalRightAction.actionHomRight_hom_inv'** 
是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalRightAction`。
形式化陈述：actionHomRight_hom_inv' (x : D) {y z : C} (f : y ⟶ z) [IsIso f] : x ⊴ᵣ f ≫
 x ⊴ᵣ inv f = 𝟙 (x ⊙ᵣ y)
参数：x : D；f : y ⟶ z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalRightAction.actionHomRight_comp`
：actionHomRight_comp (w : D) {x y z : C} (f : x ⟶ y) (g : y ⟶ z) : w ⊴ᵣ (f ≫ g) 
= w ⊴ᵣ f ≫ w ⊴ᵣ g
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalRightAction.actionHomRight_id`：∀
 {C : Type u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {
inst_1 : CategoryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…
-/
theorem actionHomRight_hom_inv' (x : D) {y z : C} (f : y ⟶ z) [IsIso f] :
    x ⊴ᵣ f ≫ x ⊴ᵣ inv f = 𝟙 (x ⊙ᵣ y) := by
  rw [← actionHomRight_comp, IsIso.hom_inv_id, actionHomRight_id]

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.MonoidalRightAction.hom_inv_actionHomLeft'** 是
 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalRightAction`。
形式化陈述：hom_inv_actionHomLeft' {x y : D} (f : x ⟶ y) [IsIso f] (z : C) : f ⊵ᵣ z ≫ 
inv f ⊵ᵣ z = 𝟙 (x ⊙ᵣ z)
参数：f : x ⟶ y；z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalRightAction.comp_actionHomLeft`：
comp_actionHomLeft {w x y : D} (f : w ⟶ x) (g : x ⟶ y) (z : C) : (f ≫ g) ⊵ᵣ z = 
f ⊵ᵣ z ≫ g ⊵ᵣ z
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalRightAction.id_actionHomLeft`：∀ 
{C : Type u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {i
nst_1 : CategoryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…
-/
theorem hom_inv_actionHomLeft' {x y : D} (f : x ⟶ y) [IsIso f] (z : C) :
    f ⊵ᵣ z ≫ inv f ⊵ᵣ z = 𝟙 (x ⊙ᵣ z) := by
  rw [← comp_actionHomLeft, IsIso.hom_inv_id, id_actionHomLeft]

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.MonoidalRightAction.actionHomRight_inv_hom'** 
是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalRightAction`。
形式化陈述：actionHomRight_inv_hom' (x : D) {y z : C} (f : y ⟶ z) [IsIso f] : x ⊴ᵣ inv
 f ≫ x ⊴ᵣ f = 𝟙 (x ⊙ᵣ z)
参数：x : D；f : y ⟶ z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalRightAction.actionHomRight_comp`
：actionHomRight_comp (w : D) {x y z : C} (f : x ⟶ y) (g : y ⟶ z) : w ⊴ᵣ (f ≫ g) 
= w ⊴ᵣ f ≫ w ⊴ᵣ g
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalRightAction.actionHomRight_id`：∀
 {C : Type u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {
inst_1 : CategoryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…
-/
theorem actionHomRight_inv_hom' (x : D) {y z : C} (f : y ⟶ z) [IsIso f] :
    x ⊴ᵣ inv f ≫ x ⊴ᵣ f = 𝟙 (x ⊙ᵣ z) := by
  rw [← actionHomRight_comp, IsIso.inv_hom_id, actionHomRight_id]

@[reassoc (attr := simp)]
/-
**CategoryTheory.MonoidalCategory.MonoidalRightAction.inv_hom_actionHomLeft'** 是
 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalRightAction`。
形式化陈述：inv_hom_actionHomLeft' {x y : D} (f : x ⟶ y) [IsIso f] (z : C) : inv f ⊵ᵣ 
z ≫ f ⊵ᵣ z = 𝟙 (y ⊙ᵣ z)
参数：f : x ⟶ y；z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalRightAction.comp_actionHomLeft`：
comp_actionHomLeft {w x y : D} (f : w ⟶ x) (g : x ⟶ y) (z : C) : (f ≫ g) ⊵ᵣ z = 
f ⊵ᵣ z ≫ g ⊵ᵣ z
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalRightAction.id_actionHomLeft`：∀ 
{C : Type u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {i
nst_1 : CategoryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…
-/
theorem inv_hom_actionHomLeft' {x y : D} (f : x ⟶ y) [IsIso f] (z : C) :
    inv f ⊵ᵣ z ≫ f ⊵ᵣ z = 𝟙 (y ⊙ᵣ z) := by
  rw [← comp_actionHomLeft, IsIso.inv_hom_id, id_actionHomLeft]
/-
**CategoryTheory.MonoidalCategory.MonoidalRightAction.isIso_actionHomLeft** 是 Ma
thlib 中的一个实例，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalRightAction`。
形式化陈述：isIso_actionHomLeft {x y : D} (f : x ⟶ y) [IsIso f] (z : C) : IsIso (f ⊵ᵣ 
z)
参数：f : x ⟶ y；z : C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalRightAction.hom_inv_actionHomLef
t'`：hom_inv_actionHomLeft' {x y : D} (f : x ⟶ y) [IsIso f] (z : C) : f ⊵ᵣ z ≫ in
v f ⊵ᵣ z = 𝟙 (x ⊙ᵣ z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalRightAction.inv_hom_actionHomLef
t'`：inv_hom_actionHomLeft' {x y : D} (f : x ⟶ y) [IsIso f] (z : C) : inv f ⊵ᵣ z 
≫ f ⊵ᵣ z = 𝟙 (y ⊙ᵣ z)
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
instance isIso_actionHomLeft {x y : D} (f : x ⟶ y) [IsIso f] (z : C) :
    IsIso (f ⊵ᵣ z) :=
  ⟨inv f ⊵ᵣ z, by simp⟩
/-
**CategoryTheory.MonoidalCategory.MonoidalRightAction.isIso_actionHomRight** 是 M
athlib 中的一个实例，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalRightAction`。
形式化陈述：isIso_actionHomRight (x : D) {y z : C} (f : y ⟶ z) [IsIso f] : IsIso (x ⊴ᵣ
 f)
参数：x : D；f : y ⟶ z。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalRightAction.actionHomRight_hom_i
nv'`：actionHomRight_hom_inv' (x : D) {y z : C} (f : y ⟶ z) [IsIso f] : x ⊴ᵣ f ≫ 
x ⊴ᵣ inv f = 𝟙 (x ⊙ᵣ y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalRightAction.actionHomRight_inv_h
om'`：actionHomRight_inv_hom' (x : D) {y z : C} (f : y ⟶ z) [IsIso f] : x ⊴ᵣ inv 
f ≫ x ⊴ᵣ f = 𝟙 (x ⊙ᵣ z)
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
instance isIso_actionHomRight (x : D) {y z : C} (f : y ⟶ z) [IsIso f] :
    IsIso (x ⊴ᵣ f) :=
  ⟨x ⊴ᵣ inv f, by simp⟩
/-
**CategoryTheory.MonoidalCategory.MonoidalRightAction.isIso_actionHom** 是 Mathli
b 中的一个实例，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalRightAction`。
形式化陈述：isIso_actionHom {x y : D} {x' y' : C} (f : x ⟶ y) (g : x' ⟶ y') [IsIso f] 
[IsIso g] : IsIso (f ⊙ᵣₘ g)
参数：f : x ⟶ y；g : x' ⟶ y'。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用引理 `CategoryTheory.MonoidalCategory.MonoidalRightAction.actionHom_id`：action
Hom_id {d d' : D} (f : d ⟶ d') (c : C) : f ⊙ᵣₘ (𝟙 c) = f ⊵ᵣ c
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalRightAction.id_actionHomLeft`：∀ 
{C : Type u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {i
nst_1 : CategoryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
instance isIso_actionHom {x y : D} {x' y' : C}
    (f : x ⟶ y) (g : x' ⟶ y') [IsIso f] [IsIso g] :
    IsIso (f ⊙ᵣₘ g) :=
  ⟨(inv f) ⊙ᵣₘ (inv g), by simp [← actionHom_comp]⟩

@[simp]
/-
**CategoryTheory.MonoidalCategory.MonoidalRightAction.inv_actionHomLeft** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalRightAction`。
形式化陈述：inv_actionHomLeft {x y : D} (f : x ⟶ y) [IsIso f] (z : C) : inv (f ⊵ᵣ z) =
 inv f ⊵ᵣ z
参数：f : x ⟶ y；z : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsIso.inv_eq_of_hom_inv_id`：inv_eq_of_hom_inv_id {f : X ⟶
 Y} [IsIso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g = 𝟙 X) : inv f = g
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalRightAction.hom_inv_actionHomLef
t'`：hom_inv_actionHomLeft' {x y : D} (f : x ⟶ y) [IsIso f] (z : C) : f ⊵ᵣ z ≫ in
v f ⊵ᵣ z = 𝟙 (x ⊙ᵣ z)
-/
lemma inv_actionHomLeft {x y : D} (f : x ⟶ y) [IsIso f] (z : C) :
    inv (f ⊵ᵣ z) = inv f ⊵ᵣ z :=
  IsIso.inv_eq_of_hom_inv_id <| hom_inv_actionHomLeft' f z

@[simp]
/-
**CategoryTheory.MonoidalCategory.MonoidalRightAction.inv_actionHomRight** 是 Mat
hlib 中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalRightAction`。
形式化陈述：inv_actionHomRight (x : D) {y z : C} (f : y ⟶ z) [IsIso f] : inv (x ⊴ᵣ f) 
= x ⊴ᵣ inv f
参数：x : D；f : y ⟶ z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsIso.inv_eq_of_hom_inv_id`：inv_eq_of_hom_inv_id {f : X ⟶
 Y} [IsIso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g = 𝟙 X) : inv f = g
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalRightAction.actionHomRight_hom_i
nv'`：actionHomRight_hom_inv' (x : D) {y z : C} (f : y ⟶ z) [IsIso f] : x ⊴ᵣ f ≫ 
x ⊴ᵣ inv f = 𝟙 (x ⊙ᵣ y)
-/
lemma inv_actionHomRight (x : D) {y z : C} (f : y ⟶ z) [IsIso f] :
    inv (x ⊴ᵣ f) = x ⊴ᵣ inv f :=
  IsIso.inv_eq_of_hom_inv_id <| actionHomRight_hom_inv' x f

@[simp]
/-
**CategoryTheory.MonoidalCategory.MonoidalRightAction.inv_actionHom** 是 Mathlib 
中的一个引理，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalRightAction`。
形式化陈述：inv_actionHom {x y : D} {x' y' : C} (f : x ⟶ y) (g : x' ⟶ y') [IsIso f] [I
sIso g] : inv (f ⊙ᵣₘ g) = (inv f) ⊙ᵣₘ (inv g)
参数：f : x ⟶ y；g : x' ⟶ y'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsIso.inv_eq_of_hom_inv_id`：inv_eq_of_hom_inv_id {f : X ⟶
 Y} [IsIso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g = 𝟙 X) : inv f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用引理 `CategoryTheory.MonoidalCategory.MonoidalRightAction.actionHom_id`：action
Hom_id {d d' : D} (f : d ⟶ d') (c : C) : f ⊙ᵣₘ (𝟙 c) = f ⊵ᵣ c
· 使用定理 `CategoryTheory.MonoidalCategory.MonoidalRightAction.id_actionHomLeft`：∀ 
{C : Type u_1} {D : Type u_2} {inst : CategoryTheory.Category.{v_1, u_1} C}   {i
nst_1 : CategoryTheory.Category.{v_2, u_2} D} {inst_2 : Ca…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inv_actionHom
    {x y : D} {x' y' : C}
    (f : x ⟶ y) (g : x' ⟶ y') [IsIso f] [IsIso g] :
    inv (f ⊙ᵣₘ g) = (inv f) ⊙ᵣₘ (inv g) :=
  IsIso.inv_eq_of_hom_inv_id <| by simp [← actionHom_comp]

section

variable (C D)
/-- Bundle the action of `C` on `D` as a functor `C ⥤ D ⥤ D`. -/
@[simps!]
/-
**CategoryTheory.MonoidalCategory.MonoidalRightAction.curriedAction** 是 Mathlib 
中的一个定义，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalRightAction`。
形式化陈述：curriedAction : C ⥤ D ⥤ D where obj x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bundle the action of `C` on `D` as a functor `C ⥤ D ⥤ D`.
-/
def curriedAction : C ⥤ D ⥤ D where
  obj x :=
    { obj y := y ⊙ᵣ x
      map f := f ⊵ᵣ x }
  map f :=
    { app y := y ⊴ᵣ f
      naturality _ _ _ := by simp [action_exchange] }

variable {C} in
/-- Bundle `d ↦ d ⊙ᵣ c` as a functor. -/
/-
**CategoryTheory.MonoidalCategory.MonoidalRightAction.actionRight** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalRightAction`。
形式化陈述：{C : Type u_1} →   (D : Type u_2) →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         [i
nst_2 : CategoryTheory.MonoidalCategory C] →           [CategoryTheory.MonoidalC
ategory.MonoidalRightAction C D] → C → CategoryTheory.Functor D D
参数：D : Type u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bundle `d ↦ d ⊙ᵣ c` as a functor.
-/
abbrev actionRight (c : C) : D ⥤ D := curriedAction C D |>.obj c

variable {D} in
/-- Bundle `c ↦ d ⊙ᵣ c` as a functor. -/
/-
**CategoryTheory.MonoidalCategory.MonoidalRightAction.actionLeft** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalRightAction`。
形式化陈述：(C : Type u_1) →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         [i
nst_2 : CategoryTheory.MonoidalCategory C] →           [CategoryTheory.MonoidalC
ategory.MonoidalRightAction C D] → D → CategoryTheory.Functor C D
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bundle `c ↦ d ⊙ᵣ c` as a functor.
-/
abbrev actionLeft (d : D) : C ⥤ D := curriedAction C D |>.flip.obj d

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Bundle `αᵣ _ _ _` as an isomorphism of trifunctors. -/
@[simps!]
/-
**CategoryTheory.MonoidalCategory.MonoidalRightAction.actionAssocNatIso** 是 Math
lib 中的一个定义，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalRightAction`。
形式化陈述：actionAssocNatIso : bifunctorComp₁₂ (curriedTensor C) (curriedAction C D) 
≅ (bifunctorComp₂₃ (curriedAction C D) (curriedAction C D)).flip
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bundle `αᵣ _ _ _` as an isomorphism of trifunctors.
-/
def actionAssocNatIso :
    bifunctorComp₁₂ (curriedTensor C) (curriedAction C D) ≅
    (bifunctorComp₂₃ (curriedAction C D) (curriedAction C D)).flip :=
  NatIso.ofComponents fun _ ↦
    NatIso.ofComponents fun _ ↦
     NatIso.ofComponents fun _ ↦ αᵣ _ _ _

set_option backward.defeqAttrib.useBackward true in
/-- Bundle `ρᵣ _` as an isomorphism of functors. -/
@[simps!]
/-
**CategoryTheory.MonoidalCategory.MonoidalRightAction.actionUnitNatIso** 是 Mathl
ib 中的一个定义，位于命名空间 `CategoryTheory.MonoidalCategory.MonoidalRightAction`。
形式化陈述：actionUnitNatIso : actionRight D (𝟙_ C) ≅ 𝟭 D
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bundle `ρᵣ _` as an isomorphism of functors.
-/
def actionUnitNatIso : actionRight D (𝟙_ C) ≅ 𝟭 D := NatIso.ofComponents (ρᵣ ·)

end

end MonoidalRightAction

end CategoryTheory.MonoidalCategory

