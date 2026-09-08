/-
Copyright (c) 2025 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Emily Riehl
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Cat
public import Mathlib.CategoryTheory.Enriched.Basic
public import Mathlib.CategoryTheory.Enriched.Ordinary.Basic

/-!
# The strict bicategory associated to a Cat-enriched category

If `C` is a type with an `EnrichedCategory Cat C` structure, then it has hom-categories, whose
objects define 1-dimensional arrows on `C` and whose morphisms define 2-dimensional arrows between
these. The enriched category axioms equip this data with the structure of a strict bicategory.

We define a type alias `CatEnriched C` for a type `C` with an `EnrichedCategory Cat C` structure. We
provide this with an instance of a strict bicategory structure constructing
`Bicategory.Strict (CatEnriched C)`.

If `C` is a type with an `EnrichedOrdinaryCategory Cat C` structure, then it has an
`EnrichedCategory Cat C` structure, so the previous construction would again produce a strict
bicategory. However, in this setting `C` is also given a `Category C` structure, together with an
equivalence between this category and the underlying category of the `EnrichedCategory Cat C`, and
in examples the given category structure is the preferred one.

Thus, we define a type alias `CatEnrichedOrdinary C` for a type `C` with an
`EnrichedOrdinaryCategory Cat C` structure. We provide this with an instance of a strict bicategory
structure extending the category structure provided by the given instance `Category C` constructing
`Bicategory.Strict (CatEnrichedOrdinary C)`.

-/

@[expose] public section

universe u v u' v'
namespace CategoryTheory
open Category

section
variable {C : Type*} [EnrichedCategory Cat C]

/-- A type synonym for `C`, which should come equipped with a `Cat`-enriched category structure.
This converts it to a strict bicategory where `Category (X ⟶ Y)` is `(X ⟶[Cat] Y)`. -/
/-
**CategoryTheory.CatEnriched** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：CatEnriched (C : Type*)
参数：C : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type synonym for `C`, which should come equipped with a `Cat`-enriched categor
y structure.
This converts it to a strict bicategory where `Category (X ⟶ Y)` is `(X ⟶[Cat] Y
)`.
-/
def CatEnriched (C : Type*) := C

namespace CatEnriched

/-
**CategoryTheory.CatEnriched.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.CatEnric
hed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : EnrichedCategory Cat (CatEnriched C) := inferInstanceAs (EnrichedCategory Cat C)

/-- Any enriched category has an underlying category structure defined by `ForgetEnrichment`.
This is equivalent but not definitionally equal to the category structure constructed here, which is
more canonically associated to the data of an `EnrichedCategory Cat` structure. -/
/-
**CategoryTheory.CatEnriched.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.CatEnric
hed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any enriched category has an underlying category structure defined by `ForgetEnr
ichment`.
This is equivalent but not definitionally equal to the category structure constr
ucted here, which is
more canonically associated to the data of an `EnrichedCategory Cat` structure.
-/
instance : CategoryStruct (CatEnriched C) where
  Hom X Y := X ⟶[Cat] Y
  id X := (eId Cat X).toFunctor.obj ⟨⟨()⟩⟩
  comp {X Y Z} f g := (eComp Cat X Y Z).toFunctor.obj (f, g)
/-
**CategoryTheory.CatEnriched.id_eq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Cat
Enriched`。
形式化陈述：id_eq (X : CatEnriched C) : 𝟙 X = (eId Cat X).toFunctor.obj ⟨⟨()⟩⟩
参数：X : CatEnriched C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_eq (X : CatEnriched C) : 𝟙 X = (eId Cat X).toFunctor.obj ⟨⟨()⟩⟩ := rfl
/-
**CategoryTheory.CatEnriched.comp_eq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.C
atEnriched`。
形式化陈述：comp_eq {X Y Z : CatEnriched C} (f : X ⟶ Y) (g : Y ⟶ Z) : f ≫ g = (eComp C
at X Y Z).toFunctor.obj (f, g)
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_eq {X Y Z : CatEnriched C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ≫ g = (eComp Cat X Y Z).toFunctor.obj (f, g) := rfl
/-
**CategoryTheory.CatEnriched.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.CatEnric
hed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : CatEnriched C} : Category (X ⟶ Y) := inferInstanceAs (Category (X ⟶[Cat] Y).α)

/-- The horizontal composition on 2-morphisms is defined using the action on arrows of the
composition bifunctor from the enriched category structure. -/
/-
**CategoryTheory.CatEnriched.hComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Cat
Enriched`。
形式化陈述：hComp {a b c : CatEnriched C} {f f' : a ⟶ b} {g g' : b ⟶ c} (η : f ⟶ f') (
θ : g ⟶ g') : f ≫ g ⟶ f' ≫ g'
参数：η : f ⟶ f'；θ : g ⟶ g'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The horizontal composition on 2-morphisms is defined using the action on arrows 
of the
composition bifunctor from the enriched category structure.
-/
def hComp {a b c : CatEnriched C} {f f' : a ⟶ b} {g g' : b ⟶ c}
    (η : f ⟶ f') (θ : g ⟶ g') : f ≫ g ⟶ f' ≫ g' := (eComp Cat a b c).toFunctor.map (η, θ)

@[simp]
/-
**CategoryTheory.CatEnriched.id_hComp_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.CatEnriched`。
形式化陈述：id_hComp_id {a b c : CatEnriched C} (f : a ⟶ b) (g : b ⟶ c) : hComp (𝟙 f) 
(𝟙 g) = 𝟙 (f ≫ g)
参数：f : a ⟶ b；g : b ⟶ c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
-/
theorem id_hComp_id {a b c : CatEnriched C} (f : a ⟶ b) (g : b ⟶ c) :
    hComp (𝟙 f) (𝟙 g) = 𝟙 (f ≫ g) := Functor.map_id ..

@[simp]
/-
**CategoryTheory.CatEnriched.eqToHom_hComp_eqToHom** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.CatEnriched`。
形式化陈述：eqToHom_hComp_eqToHom {a b c : CatEnriched C} {f f' : a ⟶ b} (α : f = f') 
{g g' : b ⟶ c} (β : g = g') : hComp (eqToHom α) (eqToHom β) = eqToHom (α ▸ β ▸ r
fl)
参数：α : f = f'；β : g = g'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.CatEnriched.id_hComp_id`：id_hComp_id {a b c : CatEnriched
 C} (f : a ⟶ b) (g : b ⟶ c) : hComp (𝟙 f) (𝟙 g) = 𝟙 (f ≫ g)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem eqToHom_hComp_eqToHom {a b c : CatEnriched C}
    {f f' : a ⟶ b} (α : f = f') {g g' : b ⟶ c} (β : g = g') :
    hComp (eqToHom α) (eqToHom β) = eqToHom (α ▸ β ▸ rfl) := by cases α; cases β; simp

/-- The interchange law for horizontal and vertical composition of 2-cells in a bicategory. -/
@[simp]
/-
**CategoryTheory.CatEnriched.hComp_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.CatEnriched`。
形式化陈述：hComp_comp {a b c : CatEnriched C} {f₁ f₂ f₃ : a ⟶ b} {g₁ g₂ g₃ : b ⟶ c} (
η : f₁ ⟶ f₂) (η' : f₂ ⟶ f₃) (θ : g₁ ⟶ g₂) (θ' : g₂ ⟶ g₃) : hComp η θ ≫ hComp η' 
θ' = hComp (η ≫ η') (θ ≫ θ')
参数：η : f₁ ⟶ f₂；η' : f₂ ⟶ f₃；θ : g₁ ⟶ g₂；θ' : g₂ ⟶ g₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…

--- 原说明 ---
The interchange law for horizontal and vertical composition of 2-cells in a bica
tegory.
-/
theorem hComp_comp {a b c : CatEnriched C} {f₁ f₂ f₃ : a ⟶ b} {g₁ g₂ g₃ : b ⟶ c}
    (η : f₁ ⟶ f₂) (η' : f₂ ⟶ f₃) (θ : g₁ ⟶ g₂) (θ' : g₂ ⟶ g₃) :
    hComp η θ ≫ hComp η' θ' = hComp (η ≫ η') (θ ≫ θ') :=
  ((eComp Cat a b c).toFunctor.map_comp (Y := (_, _)) (_, _) (_, _)).symm

/-- The action on objects of the `EnrichedCategory Cat` coherences proves the category axioms. -/
/-
**CategoryTheory.CatEnriched.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.CatEnric
hed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action on objects of the `EnrichedCategory Cat` coherences proves the catego
ry axioms.
-/
instance : Category (CatEnriched C) where
  id_comp {X Y} f := congrArg (·.toFunctor.obj f) (e_id_comp (V := Cat) X Y)
  comp_id {X Y} f := congrArg (·.toFunctor.obj f) (e_comp_id (V := Cat) X Y)
  assoc {X Y Z W} f g h := congrArg (·.toFunctor.obj (f, g, h)) (e_assoc (V := Cat) X Y Z W)

/-- The category instance on `CatEnriched C` promotes it to a `Cat` enriched ordinary
category. -/
/-
**CategoryTheory.CatEnriched.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.CatEnric
hed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category instance on `CatEnriched C` promotes it to a `Cat` enriched ordinar
y
category.
-/
instance : EnrichedOrdinaryCategory Cat (CatEnriched C) where
  homEquiv := ((Cat.Hom.equivFunctor _ _).trans Cat.fromChosenTerminalEquiv).symm
  homEquiv_comp _ _ :=
    ((Cat.Hom.equivFunctor _ _).trans Cat.fromChosenTerminalEquiv).symm_apply_eq.mpr rfl
  homEquiv_id _ :=
    ((Cat.Hom.equivFunctor _ _).trans Cat.fromChosenTerminalEquiv).symm_apply_eq.mpr rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.CatEnriched.id_hComp_heq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.CatEnriched`。
形式化陈述：id_hComp_heq {a b : CatEnriched C} {f f' : a ⟶ b} (η : f ⟶ f') : HEq (hCom
p (𝟙 (𝟙 a)) η) η
参数：η : f ⟶ f'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.CatEnriched.id_eq`：id_eq (X : CatEnriched C) : 𝟙 X = (eId
 Cat X).toFunctor.obj ⟨⟨()⟩⟩
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `congr_arg_heq`：∀ {α : Sort u_1} {β : α → Sort u_2} (f : (a : α) → β a) {
a₁ a₂ : α}, a₁ = a₂ → f a₁ ≍ f a₂
· 使用定理 `CategoryTheory.e_id_comp`：e_id_comp (X Y : C) : (fun_ (X ⟶[V] Y)).inv ≫ 
eId V X ▷ _ ≫ eComp V X X Y = 𝟙 (X ⟶[V] Y)
-/
theorem id_hComp_heq {a b : CatEnriched C} {f f' : a ⟶ b} (η : f ⟶ f') :
    HEq (hComp (𝟙 (𝟙 a)) η) η := by
  rw [id_eq, ← Functor.map_id]
  exact congr_arg_heq (·.toFunctor.map η) (e_id_comp (V := Cat) a b)
/-
**CategoryTheory.CatEnriched.id_hComp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
CatEnriched`。
形式化陈述：id_hComp {a b : CatEnriched C} {f f' : a ⟶ b} (η : f ⟶ f') : hComp (𝟙 (𝟙 a
)) η = eqToHom (id_comp f) ≫ η ≫ eqToHom (id_comp f').symm
参数：η : f ⟶ f'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem id_hComp {a b : CatEnriched C} {f f' : a ⟶ b} (η : f ⟶ f') :
    hComp (𝟙 (𝟙 a)) η = eqToHom (id_comp f) ≫ η ≫ eqToHom (id_comp f').symm := by
  simp [← heq_eq_eq, id_hComp_heq]

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.CatEnriched.hComp_id_heq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.CatEnriched`。
形式化陈述：hComp_id_heq {a b : CatEnriched C} {f f' : a ⟶ b} (η : f ⟶ f') : HEq (hCom
p η (𝟙 (𝟙 b))) η
参数：η : f ⟶ f'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.CatEnriched.id_eq`：id_eq (X : CatEnriched C) : 𝟙 X = (eId
 Cat X).toFunctor.obj ⟨⟨()⟩⟩
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `congr_arg_heq`：∀ {α : Sort u_1} {β : α → Sort u_2} (f : (a : α) → β a) {
a₁ a₂ : α}, a₁ = a₂ → f a₁ ≍ f a₂
· 使用定理 `CategoryTheory.e_comp_id`：e_comp_id (X Y : C) : (ρ_ (X ⟶[V] Y)).inv ≫ _ 
◁ eId V Y ≫ eComp V X Y Y = 𝟙 (X ⟶[V] Y)
-/
theorem hComp_id_heq {a b : CatEnriched C} {f f' : a ⟶ b} (η : f ⟶ f') :
    HEq (hComp η (𝟙 (𝟙 b))) η := by
  rw [id_eq, ← Functor.map_id]
  exact congr_arg_heq (·.toFunctor.map η) (e_comp_id (V := Cat) a b)
/-
**CategoryTheory.CatEnriched.hComp_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
CatEnriched`。
形式化陈述：hComp_id {a b : CatEnriched C} {f f' : a ⟶ b} (η : f ⟶ f') : hComp η (𝟙 (𝟙
 b)) = eqToHom (comp_id f) ≫ η ≫ eqToHom (comp_id f').symm
参数：η : f ⟶ f'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem hComp_id {a b : CatEnriched C} {f f' : a ⟶ b} (η : f ⟶ f') :
    hComp η (𝟙 (𝟙 b)) = eqToHom (comp_id f) ≫ η ≫ eqToHom (comp_id f').symm := by
  simp [← heq_eq_eq, hComp_id_heq]
/-
**CategoryTheory.CatEnriched.hComp_assoc_heq** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.CatEnriched`。
形式化陈述：hComp_assoc_heq {a b c d : CatEnriched C} {f f' : a ⟶ b} {g g' : b ⟶ c} {h
 h' : c ⟶ d} (η : f ⟶ f') (θ : g ⟶ g') (κ : h ⟶ h') : HEq (hComp (hComp η θ) κ) 
(hComp η (hComp θ κ))
参数：η : f ⟶ f'；θ : g ⟶ g'；κ : h ⟶ h'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg_heq`：∀ {α : Sort u_1} {β : α → Sort u_2} (f : (a : α) → β a) {
a₁ a₂ : α}, a₁ = a₂ → f a₁ ≍ f a₂
· 使用定理 `CategoryTheory.e_assoc`：e_assoc (W X Y Z : C) : (α_ _ _ _).inv ≫ eComp V
 W X Y ▷ _ ≫ eComp V W Y Z = _ ◁ eComp V X Y Z ≫ eComp V W X Z
-/
theorem hComp_assoc_heq {a b c d : CatEnriched C} {f f' : a ⟶ b} {g g' : b ⟶ c} {h h' : c ⟶ d}
    (η : f ⟶ f') (θ : g ⟶ g') (κ : h ⟶ h') :
    HEq (hComp (hComp η θ) κ) (hComp η (hComp θ κ)) :=
  congr_arg_heq (·.toFunctor.map (X := (_, _, _)) (Y := (_, _, _)) (η, θ, κ))
    (e_assoc (V := Cat) a b c d)
/-
**CategoryTheory.CatEnriched.hComp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.CatEnriched`。
形式化陈述：hComp_assoc {a b c d : CatEnriched C} {f f' : a ⟶ b} {g g' : b ⟶ c} {h h' 
: c ⟶ d} (η : f ⟶ f') (θ : g ⟶ g') (κ : h ⟶ h') : hComp (hComp η θ) κ = eqToHom 
(assoc f g h) ≫ hComp η (hComp θ κ) ≫ eqToHom (assoc f' g' h').symm
参数：η : f ⟶ f'；θ : g ⟶ g'；κ : h ⟶ h'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem hComp_assoc {a b c d : CatEnriched C} {f f' : a ⟶ b} {g g' : b ⟶ c} {h h' : c ⟶ d}
    (η : f ⟶ f') (θ : g ⟶ g') (κ : h ⟶ h') :
    hComp (hComp η θ) κ =
      eqToHom (assoc f g h) ≫ hComp η (hComp θ κ) ≫ eqToHom (assoc f' g' h').symm := by
  simp [← heq_eq_eq, hComp_assoc_heq]
/-
**CategoryTheory.CatEnriched.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.CatEnric
hed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Bicategory (CatEnriched C) where
  homCategory := inferInstance
  whiskerLeft {_ _ _} f {_ _} η := hComp (𝟙 f) η
  whiskerRight η h := hComp η (𝟙 h)
  associator f g h := eqToIso (assoc f g h)
  leftUnitor f := eqToIso (id_comp f)
  rightUnitor f := eqToIso (comp_id f)
  id_whiskerLeft := id_hComp
  comp_whiskerLeft := by simp [← id_hComp_id, hComp_assoc]
  whiskerRight_id := hComp_id
  whiskerRight_comp := by simp [hComp_assoc]
  whisker_assoc := by simp [hComp_assoc]
  pentagon f g h i := by
    generalize_proofs h1 h2 h3 h4; revert h1 h2 h3 h4
    generalize (f ≫ g) ≫ h = x, (g ≫ h) ≫ i = w
    rintro rfl _ rfl _; simp
  triangle f g := by
    generalize_proofs h1 h2 h3; revert h1 h2 h3
    generalize 𝟙 _ ≫ g = g, f ≫ 𝟙 _ = f
    rintro _ rfl rfl; simp

/-- As the associator and left and right unitors are defined as eqToIso of category axioms, the
bicategory structure on `CatEnriched C` is strict. -/
/-
**CategoryTheory.CatEnriched.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.CatEnric
hed`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
As the associator and left and right unitors are defined as eqToIso of category 
axioms, the
bicategory structure on `CatEnriched C` is strict.
-/
instance : Bicategory.Strict (CatEnriched C) where

end CatEnriched

end

section
variable {C : Type u} [Category.{v} C] [EnrichedOrdinaryCategory Cat.{v', u'} C]

/-- A type synonym for `C`, which should come equipped with a `Cat`-enriched category structure.
This converts it to a strict bicategory where `Category (X ⟶ Y)` is `(X ⟶[Cat] Y)`. -/
/-
**CategoryTheory.CatEnrichedOrdinary** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：CatEnrichedOrdinary (C : Type*)
参数：C : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type synonym for `C`, which should come equipped with a `Cat`-enriched categor
y structure.
This converts it to a strict bicategory where `Category (X ⟶ Y)` is `(X ⟶[Cat] Y
)`.
-/
def CatEnrichedOrdinary (C : Type*) := C

namespace CatEnrichedOrdinary

/-
**CategoryTheory.CatEnrichedOrdinary.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
CatEnrichedOrdinary`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (CatEnrichedOrdinary C) := inferInstanceAs (Category C)
/-
**CategoryTheory.CatEnrichedOrdinary.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
CatEnrichedOrdinary`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : EnrichedCategory Cat (CatEnrichedOrdinary C) := inferInstanceAs (EnrichedCategory Cat C)
/-
**CategoryTheory.CatEnrichedOrdinary.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
CatEnrichedOrdinary`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : EnrichedOrdinaryCategory Cat (CatEnrichedOrdinary C) :=
  inferInstanceAs (EnrichedOrdinaryCategory Cat C)

/-- The forgetful map from the type alias associated to `EnrichedOrdinaryCategory Cat C` and the
type alias associated to `EnrichedCategory Cat C` is the identity on underlying types. -/
/-
**CategoryTheory.CatEnrichedOrdinary.toBase** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.CatEnrichedOrdinary`。
形式化陈述：toBase (a : CatEnrichedOrdinary C) : CatEnriched C
参数：a : CatEnrichedOrdinary C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful map from the type alias associated to `EnrichedOrdinaryCategory Ca
t C` and the
type alias associated to `EnrichedCategory Cat C` is the identity on underlying 
types.
-/
def toBase (a : CatEnrichedOrdinary C) : CatEnriched C := a

/-- The hom-types in a `Cat`-enriched ordinary category are equivalent to the types underlying the
hom-categories. -/
/-
**CategoryTheory.CatEnrichedOrdinary.homEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.CatEnrichedOrdinary`。
形式化陈述：homEquiv {a b : CatEnrichedOrdinary C} : (a ⟶ b) ≃ (a.toBase ⟶ b.toBase)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
The hom-types in a `Cat`-enriched ordinary category are equivalent to the types 
underlying the
hom-categories.
-/
def homEquiv {a b : CatEnrichedOrdinary C} : (a ⟶ b) ≃ (a.toBase ⟶ b.toBase) :=
  (eHomEquiv (V := Cat)).trans (Equiv.trans (Cat.Hom.equivFunctor _ _) Cat.fromChosenTerminalEquiv)
/-
**CategoryTheory.CatEnrichedOrdinary.homEquiv_id** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.CatEnrichedOrdinary`。
形式化陈述：homEquiv_id {a : CatEnrichedOrdinary C} : homEquiv (𝟙 a) = 𝟙 a.toBase
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.eHomEquiv_id`：eHomEquiv_id (X : C) : eHomEquiv V (𝟙 X) = 
eId V X
-/
theorem homEquiv_id {a : CatEnrichedOrdinary C} : homEquiv (𝟙 a) = 𝟙 a.toBase := by
  unfold homEquiv
  simp only [Equiv.trans_apply]
  rw [eHomEquiv_id]
  rfl
/-
**CategoryTheory.CatEnrichedOrdinary.homEquiv_comp** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.CatEnrichedOrdinary`。
形式化陈述：homEquiv_comp {a b c : CatEnrichedOrdinary C} (f : a ⟶ b) (g : b ⟶ c) : ho
mEquiv (f ≫ g) = homEquiv f ≫ homEquiv g
参数：f : a ⟶ b；g : b ⟶ c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.eHomEquiv_comp`：eHomEquiv_comp {X Y Z : C} (f : X ⟶ Y) (g
 : Y ⟶ Z) : eHomEquiv V (f ≫ g) = (fun_ _).inv ≫ (eHomEquiv V f otimesₘ eHomEqui
v V g) ≫ eComp V X …
-/
theorem homEquiv_comp {a b c : CatEnrichedOrdinary C} (f : a ⟶ b) (g : b ⟶ c) :
    homEquiv (f ≫ g) = homEquiv f ≫ homEquiv g := by
  unfold homEquiv
  simp only [Equiv.trans_apply]
  rw [eHomEquiv_comp]
  rfl

/-- The 2-cells between a parallel pair of 1-cells `f g` in `CatEnrichedOrdinary C` are defined to
be the morphisms in the hom-categories provided by the `EnrichedCategory Cat C` structure between
the corresponding objects. -/
/-
**CategoryTheory.CatEnrichedOrdinary.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTh
eory.CatEnrichedOrdinary`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [Category
Theory.EnrichedOrdinaryCategory CategoryTheory.Cat C] →       {X Y : CategoryThe
ory.CatEnrichedOrdinary C} → (X ⟶ Y) → (X ⟶ Y) → Type v'
参数：X ⟶ Y；X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The 2-cells between a parallel pair of 1-cells `f g` in `CatEnrichedOrdinary C` 
are defined to
be the morphisms in the hom-categories provided by the `EnrichedCategory Cat C` 
structure between
the corresponding objects.
-/
structure Hom {X Y : CatEnrichedOrdinary C} (f g : X ⟶ Y) where mk' ::
  /-- A 2-cell from `f` to `g` is a 2-cell from `homEquiv f` to `homEquiv g`. -/
  base' : homEquiv f ⟶ homEquiv g
/-
**CategoryTheory.CatEnrichedOrdinary.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
CatEnrichedOrdinary`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : CatEnrichedOrdinary C} : Quiver (X ⟶ Y) where
  Hom f g := Hom f g

/-- A 2-cell in `CatEnrichedOrdinary C` has a corresponding "base" 2-cell in `CatEnriched C`. -/
/-
**CategoryTheory.CatEnrichedOrdinary.Hom.base** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.CatEnrichedOrdinary.Hom`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.EnrichedOrdinaryCategory CategoryTheory.Cat C] →       {X Y : Ca
tegoryTheory.CatEnrichedOrdinary C} →         {f g : X ⟶ Y} →           (f ⟶ g) 
→ (CategoryTheory.CatEnrichedOrdinary.homEquiv f ⟶ CategoryTheory.CatEnrichedOrd
inary.homEquiv g)
参数：f ⟶ g；CategoryTheory.CatEnrichedOrdinary.homEquiv f ⟶ CategoryTheory.CatEnric
hedOrdinary.homEquiv g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A 2-cell in `CatEnrichedOrdinary C` has a corresponding "base" 2-cell in `CatEnr
iched C`.
-/
def Hom.base {X Y : CatEnrichedOrdinary C} {f g : X ⟶ Y} (α : f ⟶ g) :
    homEquiv f ⟶ homEquiv g := α.base'

/-- A 2-cell in `CatEnriched C` can be "made" into a 2-cell in `CatEnrichedOrdinary C`. -/
/-
**CategoryTheory.CatEnrichedOrdinary.Hom.mk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.CatEnrichedOrdinary.Hom`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.EnrichedOrdinaryCategory CategoryTheory.Cat C] →       {X Y : Ca
tegoryTheory.CatEnrichedOrdinary C} →         {f g : X ⟶ Y} →           (Categor
yTheory.CatEnrichedOrdinary.homEquiv f ⟶ CategoryTheory.CatEnrichedOrdinary.homE
quiv g) → (f ⟶ g)
参数：CategoryTheory.CatEnrichedOrdinary.homEquiv f ⟶ CategoryTheory.CatEnrichedOrd
inary.homEquiv g；f ⟶ g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A 2-cell in `CatEnriched C` can be "made" into a 2-cell in `CatEnrichedOrdinary 
C`.
-/
def Hom.mk {X Y : CatEnrichedOrdinary C} {f g : X ⟶ Y} (α : homEquiv f ⟶ homEquiv g) :
    f ⟶ g := .mk' α
/-
**CategoryTheory.CatEnrichedOrdinary.mk_base** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.CatEnrichedOrdinary`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C]   [inst_1 : Categ
oryTheory.EnrichedOrdinaryCategory CategoryTheory.Cat C] {X Y : CategoryTheory.C
atEnrichedOrdinary C}   {f g : X ⟶ Y} (α : f ⟶ g),   CategoryTheory.CatEnrichedO
rdinary.Hom.mk (CategoryTheory.CatEnrichedOrdinary.Hom.base α) = α
参数：α : f ⟶ g；CategoryTheory.CatEnrichedOrdinary.Hom.base α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem mk_base {X Y : CatEnrichedOrdinary C} {f g : X ⟶ Y} (α : f ⟶ g) :
    Hom.mk (Hom.base α) = α := rfl
/-
**CategoryTheory.CatEnrichedOrdinary.base_mk** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.CatEnrichedOrdinary`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C]   [inst_1 : Categ
oryTheory.EnrichedOrdinaryCategory CategoryTheory.Cat C] {X Y : CategoryTheory.C
atEnrichedOrdinary C}   {f g : X ⟶ Y} (α : CategoryTheory.CatEnrichedOrdinary.ho
mEquiv f ⟶ CategoryTheory.CatEnrichedOrdinary.homEquiv g),   CategoryTheory.CatE
nrichedOrdinary.Hom.base (CategoryTheory.CatEnrichedOrdinary.Hom.mk α) = α
参数：α : CategoryTheory.CatEnrichedOrdinary.homEquiv f ⟶ CategoryTheory.CatEnriche
dOrdinary.homEquiv g；CategoryTheory.CatEnrichedOrdinary.Hom.mk α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem base_mk {X Y : CatEnrichedOrdinary C} {f g : X ⟶ Y} (α : homEquiv f ⟶ homEquiv g) :
    Hom.base (Hom.mk α) = α := rfl
/-
**CategoryTheory.CatEnrichedOrdinary.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
CatEnrichedOrdinary`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : CatEnrichedOrdinary C} : CategoryStruct (X ⟶ Y) where
  id f := Hom.mk (𝟙 (homEquiv f))
  comp α β := Hom.mk (Hom.base α ≫ Hom.base β)
/-
**CategoryTheory.CatEnrichedOrdinary.Hom.id_eq** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.CatEnrichedOrdinary.Hom`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C]   [inst_1 : Categ
oryTheory.EnrichedOrdinaryCategory CategoryTheory.Cat C] {X Y : CategoryTheory.C
atEnrichedOrdinary C}   (f : X ⟶ Y),   CategoryTheory.CategoryStruct.id f =     
CategoryTheory.CatEnrichedOrdinary.Hom.mk       (CategoryTheory.CategoryStruct.i
d (CategoryTheory.CatEnrichedOrdinary.homEquiv f))
参数：f : X ⟶ Y；CategoryTheory.CategoryStruct.id (CategoryTheory.CatEnrichedOrdinar
y.homEquiv f)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Hom.id_eq {X Y : CatEnrichedOrdinary C} (f : X ⟶ Y) :
    𝟙 f = Hom.mk (𝟙 (homEquiv f)) := rfl
/-
**CategoryTheory.CatEnrichedOrdinary.Hom.base_id** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.CatEnrichedOrdinary.Hom`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C]   [inst_1 : Categ
oryTheory.EnrichedOrdinaryCategory CategoryTheory.Cat C] {X Y : CategoryTheory.C
atEnrichedOrdinary C}   (f : X ⟶ Y),   CategoryTheory.CatEnrichedOrdinary.Hom.ba
se (CategoryTheory.CategoryStruct.id f) =     CategoryTheory.CategoryStruct.id (
CategoryTheory.CatEnrichedOrdinary.homEquiv f)
参数：f : X ⟶ Y；CategoryTheory.CategoryStruct.id f；CategoryTheory.CatEnrichedOrdina
ry.homEquiv f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem Hom.base_id {X Y : CatEnrichedOrdinary C} (f : X ⟶ Y) :
    Hom.base (𝟙 f) = 𝟙 (homEquiv f) := rfl
/-
**CategoryTheory.CatEnrichedOrdinary.Hom.comp_eq** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.CatEnrichedOrdinary.Hom`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C]   [inst_1 : Categ
oryTheory.EnrichedOrdinaryCategory CategoryTheory.Cat C] {X Y : CategoryTheory.C
atEnrichedOrdinary C}   {f g h : X ⟶ Y} (α : f ⟶ g) (β : g ⟶ h),   CategoryTheor
y.CategoryStruct.comp α β =     CategoryTheory.CatEnrichedOrdinary.Hom.mk       
(CategoryTheory.CategoryStruct.comp (CategoryTheory.CatEnrichedOrdinary.Hom.base
 α)         (CategoryTheory.CatEnrichedOrdinary.Hom.base β))
参数：α : f ⟶ g；β : g ⟶ h；CategoryTheory.CategoryStruct.comp (CategoryTheory.CatEnr
ichedOrdinary.Hom.base α)         (CategoryTheory.CatEnrichedOrdinary.Hom.base β
)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Hom.comp_eq {X Y : CatEnrichedOrdinary C} {f g h : X ⟶ Y}
    (α : f ⟶ g) (β : g ⟶ h) : (α ≫ β) = Hom.mk (Hom.base α ≫ Hom.base β) := rfl
/-
**CategoryTheory.CatEnrichedOrdinary.Hom.base_comp** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.CatEnrichedOrdinary.Hom`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C]   [inst_1 : Categ
oryTheory.EnrichedOrdinaryCategory CategoryTheory.Cat C] {X Y : CategoryTheory.C
atEnrichedOrdinary C}   {f g h : X ⟶ Y} (α : f ⟶ g) (β : g ⟶ h),   CategoryTheor
y.CatEnrichedOrdinary.Hom.base (CategoryTheory.CategoryStruct.comp α β) =     Ca
tegoryTheory.CategoryStruct.comp (CategoryTheory.CatEnrichedOrdinary.Hom.base α)
       (CategoryTheory.CatEnrichedOrdinary.Hom.base β)
参数：α : f ⟶ g；β : g ⟶ h；CategoryTheory.CategoryStruct.comp α β；CategoryTheory.Cat
EnrichedOrdinary.Hom.base α；CategoryTheory.CatEnrichedOrdinary.Hom.base β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem Hom.base_comp {X Y : CatEnrichedOrdinary C} {f g h : X ⟶ Y}
    (α : f ⟶ g) (β : g ⟶ h) : Hom.base (α ≫ β) = Hom.base α ≫ Hom.base β := rfl
/-
**CategoryTheory.CatEnrichedOrdinary.Hom.mk_comp** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.CatEnrichedOrdinary.Hom`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C]   [inst_1 : Categ
oryTheory.EnrichedOrdinaryCategory CategoryTheory.Cat C] {X Y : CategoryTheory.C
atEnrichedOrdinary C}   {f g h : X ⟶ Y} (α : CategoryTheory.CatEnrichedOrdinary.
homEquiv f ⟶ CategoryTheory.CatEnrichedOrdinary.homEquiv g)   (β : CategoryTheor
y.CatEnrichedOrdinary.homEquiv g ⟶ CategoryTheory.CatEnrichedOrdinary.homEquiv h
),   CategoryTheory.CatEnrichedOrdinary.Hom.mk (CategoryTheory.CategoryStruct.co
mp α β) =     CategoryTheory.CategoryStruct.comp (CategoryTheory.CatEnrichedOrdi
nary.Hom.mk α)       (CategoryTheory.CatEnrichedOrdinary.Hom.mk β)
参数：α : CategoryTheory.CatEnrichedOrdinary.homEquiv f ⟶ CategoryTheory.CatEnriche
dOrdinary.homEquiv g；β : CategoryTheory.CatEnrichedOrdinary.homEquiv g ⟶ Categor
yTheory.CatEnrichedOrdinary.homEquiv h；CategoryTheory.CategoryStruct.comp α β；Ca
tegoryTheory.CatEnrichedOrdinary.Hom.mk α；CategoryTheory.CatEnrichedOrdinary.Hom
.mk β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Hom.mk_comp {X Y : CatEnrichedOrdinary C} {f g h : X ⟶ Y}
    (α : homEquiv f ⟶ homEquiv g) (β : homEquiv g ⟶ homEquiv h) :
    Hom.mk (α ≫ β) = Hom.mk α ≫ Hom.mk β := rfl
/-
**CategoryTheory.CatEnrichedOrdinary.Hom.ext** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.CatEnrichedOrdinary.Hom`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C]   [inst_1 : Categ
oryTheory.EnrichedOrdinaryCategory CategoryTheory.Cat C] {X Y : CategoryTheory.C
atEnrichedOrdinary C}   {f g : X ⟶ Y} (α β : f ⟶ g),   CategoryTheory.CatEnriche
dOrdinary.Hom.base α = CategoryTheory.CatEnrichedOrdinary.Hom.base β → α = β
参数：α β : f ⟶ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[ext] theorem Hom.ext {X Y : CatEnrichedOrdinary C} {f g : X ⟶ Y} (α β : f ⟶ g)
    (H : Hom.base α = Hom.base β) : α = β := by cases α; cases β; cases H; rfl

/-- A `Cat`-enriched ordinary category comes with hom-categories `X ⟶[Cat] Y` whose underlying type
of objects is equivalent to the type `X ⟶ Y` defined by the category structure on `C`. The following
definition transfers the category structure to the latter type of objects. -/
/-
**CategoryTheory.CatEnrichedOrdinary.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
CatEnrichedOrdinary`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Cat`-enriched ordinary category comes with hom-categories `X ⟶[Cat] Y` whose 
underlying type
of objects is equivalent to the type `X ⟶ Y` defined by the category structure o
n `C`. The following
definition transfers the category structure to the latter type of objects.
-/
instance {X Y : CatEnrichedOrdinary C} : Category (X ⟶ Y) where
/-
**CategoryTheory.CatEnrichedOrdinary.Hom.base_eqToHom** 是 Mathlib 中的一个定理，位于命名空间 
`CategoryTheory.CatEnrichedOrdinary.Hom`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C]   [inst_1 : Categ
oryTheory.EnrichedOrdinaryCategory CategoryTheory.Cat C] {X Y : CategoryTheory.C
atEnrichedOrdinary C}   {f g : X ⟶ Y} (α : f = g),   CategoryTheory.CatEnrichedO
rdinary.Hom.base (CategoryTheory.eqToHom α) = CategoryTheory.eqToHom ⋯
参数：α : f = g；CategoryTheory.eqToHom α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
@[simp] theorem Hom.base_eqToHom {X Y : CatEnrichedOrdinary C} {f g : X ⟶ Y} (α : f = g) :
    Hom.base (eqToHom α) = eqToHom (congrArg _ α) := by cases α; rfl

/-- The horizontal composition on 2-morphisms is defined using the action on arrows of the
composition bifunctor from the enriched category structure. -/
/-
**CategoryTheory.CatEnrichedOrdinary.hComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.CatEnrichedOrdinary`。
形式化陈述：hComp {a b c : CatEnrichedOrdinary C} {f f' : a ⟶ b} {g g' : b ⟶ c} (η : f
 ⟶ f') (θ : g ⟶ g') : f ≫ g ⟶ f' ≫ g'
参数：η : f ⟶ f'；θ : g ⟶ g'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CatEnrichedOrdinary.homEquiv_comp`：homEquiv_comp {a b c :
 CatEnrichedOrdinary C} (f : a ⟶ b) (g : b ⟶ c) : homEquiv (f ≫ g) = homEquiv f 
≫ homEquiv g

--- 原说明 ---
The horizontal composition on 2-morphisms is defined using the action on arrows 
of the
composition bifunctor from the enriched category structure.
-/
def hComp {a b c : CatEnrichedOrdinary C} {f f' : a ⟶ b} {g g' : b ⟶ c}
    (η : f ⟶ f') (θ : g ⟶ g') : f ≫ g ⟶ f' ≫ g' :=
  .mk <|
    eqToHom (homEquiv_comp f g) ≫ CatEnriched.hComp (Hom.base η) (Hom.base θ) ≫
    eqToHom (homEquiv_comp f' g').symm

@[simp]
/-
**CategoryTheory.CatEnrichedOrdinary.id_hComp_id** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.CatEnrichedOrdinary`。
形式化陈述：id_hComp_id {a b c : CatEnrichedOrdinary C} (f : a ⟶ b) (g : b ⟶ c) : hCom
p (𝟙 f) (𝟙 g) = 𝟙 (f ≫ g)
参数：f : a ⟶ b；g : b ⟶ c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.CatEnrichedOrdinary.homEquiv_comp`：homEquiv_comp {a b c :
 CatEnrichedOrdinary C} (f : a ⟶ b) (g : b ⟶ c) : homEquiv (f ≫ g) = homEquiv f 
≫ homEquiv g
· 使用定理 `CategoryTheory.CatEnriched.id_hComp_id`：id_hComp_id {a b c : CatEnriched
 C} (f : a ⟶ b) (g : b ⟶ c) : hComp (𝟙 f) (𝟙 g) = 𝟙 (f ≫ g)
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.eqToHom_trans`：eqToHom_trans {X Y Z : C} (p : X = Y) (q :
 Y = Z) : eqToHom p ≫ eqToHom q = eqToHom (p.trans q)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem id_hComp_id {a b c : CatEnrichedOrdinary C} (f : a ⟶ b) (g : b ⟶ c) :
    hComp (𝟙 f) (𝟙 g) = 𝟙 (f ≫ g) := by simp [hComp, Hom.id_eq]

@[simp]
/-
**CategoryTheory.CatEnrichedOrdinary.eqToHom_hComp_eqToHom** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.CatEnrichedOrdinary`。
形式化陈述：eqToHom_hComp_eqToHom {a b c : CatEnrichedOrdinary C} {f f' : a ⟶ b} (α : 
f = f') {g g' : b ⟶ c} (β : g = g') : hComp (eqToHom α) (eqToHom β) = eqToHom (α
 ▸ β ▸ rfl)
参数：α : f = f'；β : g = g'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.CatEnrichedOrdinary.id_hComp_id`：id_hComp_id {a b c : Cat
EnrichedOrdinary C} (f : a ⟶ b) (g : b ⟶ c) : hComp (𝟙 f) (𝟙 g) = 𝟙 (f ≫ g)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem eqToHom_hComp_eqToHom {a b c : CatEnrichedOrdinary C}
    {f f' : a ⟶ b} (α : f = f') {g g' : b ⟶ c} (β : g = g') :
    hComp (eqToHom α) (eqToHom β) = eqToHom (α ▸ β ▸ rfl) := by cases α; cases β; simp

/-- The interchange law for horizontal and vertical composition of 2-cells in a bicategory. -/
@[simp]
/-
**CategoryTheory.CatEnrichedOrdinary.hComp_comp** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.CatEnrichedOrdinary`。
形式化陈述：hComp_comp {a b c : CatEnrichedOrdinary C} {f₁ f₂ f₃ : a ⟶ b} {g₁ g₂ g₃ : 
b ⟶ c} (η : f₁ ⟶ f₂) (η' : f₂ ⟶ f₃) (θ : g₁ ⟶ g₂) (θ' : g₂ ⟶ g₃) : hComp η θ ≫ h
Comp η' θ' = hComp (η ≫ η') (θ ≫ θ')
参数：η : f₁ ⟶ f₂；η' : f₂ ⟶ f₃；θ : g₁ ⟶ g₂；θ' : g₂ ⟶ g₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.CatEnrichedOrdinary.homEquiv_comp`：homEquiv_comp {a b c :
 CatEnrichedOrdinary C} (f : a ⟶ b) (g : b ⟶ c) : homEquiv (f ≫ g) = homEquiv f 
≫ homEquiv g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.eqToHom_trans_assoc`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {X Y Z : C} (p : X = Y) (q : Y = Z) {Z_1 : C} (h : Z ⟶ Z
_1),   CategoryTheory.Ca…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The interchange law for horizontal and vertical composition of 2-cells in a bica
tegory.
-/
theorem hComp_comp {a b c : CatEnrichedOrdinary C} {f₁ f₂ f₃ : a ⟶ b} {g₁ g₂ g₃ : b ⟶ c}
    (η : f₁ ⟶ f₂) (η' : f₂ ⟶ f₃) (θ : g₁ ⟶ g₂) (θ' : g₂ ⟶ g₃) :
    hComp η θ ≫ hComp η' θ' = hComp (η ≫ η') (θ ≫ θ') := by
  simp [hComp, ← CatEnriched.hComp_comp, Hom.comp_eq]
/-
**CategoryTheory.CatEnrichedOrdinary.id_hComp** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.CatEnrichedOrdinary`。
形式化陈述：id_hComp {a b : CatEnrichedOrdinary C} {f f' : a ⟶ b} (η : f ⟶ f') : hComp
 (𝟙 (𝟙 a)) η = eqToHom (id_comp f) ≫ η ≫ eqToHom (id_comp f').symm
参数：η : f ⟶ f'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CatEnrichedOrdinary.Hom.ext`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.EnrichedOrdinaryCategory
 CategoryTheory.Cat C] {X Y : Ca…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.CatEnrichedOrdinary.homEquiv_comp`：homEquiv_comp {a b c :
 CatEnrichedOrdinary C} (f : a ⟶ b) (g : b ⟶ c) : homEquiv (f ≫ g) = homEquiv f 
≫ homEquiv g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.CatEnrichedOrdinary.homEquiv_id`：homEquiv_id {a : CatEnri
chedOrdinary C} : homEquiv (𝟙 a) = 𝟙 a.toBase
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.CatEnrichedOrdinary.Hom.base_eqToHom`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.EnrichedOrdinar
yCategory CategoryTheory.Cat C] {X Y : Ca…
-/
theorem id_hComp {a b : CatEnrichedOrdinary C} {f f' : a ⟶ b} (η : f ⟶ f') :
    hComp (𝟙 (𝟙 a)) η = eqToHom (id_comp f) ≫ η ≫ eqToHom (id_comp f').symm := by
  ext
  simp only [hComp, Hom.base_id, base_mk, ← heq_eq_eq, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rw [homEquiv_id]; simp [CatEnriched.id_hComp_heq]
/-
**CategoryTheory.CatEnrichedOrdinary.id_hComp_heq** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.CatEnrichedOrdinary`。
形式化陈述：id_hComp_heq {a b : CatEnrichedOrdinary C} {f f' : a ⟶ b} (η : f ⟶ f') : H
Eq (hComp (𝟙 (𝟙 a)) η) η
参数：η : f ⟶ f'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.CatEnrichedOrdinary.id_hComp`：id_hComp {a b : CatEnriched
Ordinary C} {f f' : a ⟶ b} (η : f ⟶ f') : hComp (𝟙 (𝟙 a)) η = eqToHom (id_comp f
) ≫ η ≫ eqToHom (id_comp f').symm
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem id_hComp_heq {a b : CatEnrichedOrdinary C} {f f' : a ⟶ b} (η : f ⟶ f') :
    HEq (hComp (𝟙 (𝟙 a)) η) η := by simp [id_hComp]
/-
**CategoryTheory.CatEnrichedOrdinary.hComp_id** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.CatEnrichedOrdinary`。
形式化陈述：hComp_id {a b : CatEnrichedOrdinary C} {f f' : a ⟶ b} (η : f ⟶ f') : hComp
 η (𝟙 (𝟙 b)) = eqToHom (comp_id f) ≫ η ≫ eqToHom (comp_id f').symm
参数：η : f ⟶ f'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CatEnrichedOrdinary.Hom.ext`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.EnrichedOrdinaryCategory
 CategoryTheory.Cat C] {X Y : Ca…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.CatEnrichedOrdinary.homEquiv_comp`：homEquiv_comp {a b c :
 CatEnrichedOrdinary C} (f : a ⟶ b) (g : b ⟶ c) : homEquiv (f ≫ g) = homEquiv f 
≫ homEquiv g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.CatEnrichedOrdinary.homEquiv_id`：homEquiv_id {a : CatEnri
chedOrdinary C} : homEquiv (𝟙 a) = 𝟙 a.toBase
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.CatEnrichedOrdinary.Hom.base_eqToHom`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.EnrichedOrdinar
yCategory CategoryTheory.Cat C] {X Y : Ca…
-/
theorem hComp_id {a b : CatEnrichedOrdinary C} {f f' : a ⟶ b} (η : f ⟶ f') :
    hComp η (𝟙 (𝟙 b)) = eqToHom (comp_id f) ≫ η ≫ eqToHom (comp_id f').symm := by
  ext
  simp only [hComp, Hom.base_id, base_mk, ← heq_eq_eq, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rw [homEquiv_id]
  simp [CatEnriched.hComp_id_heq]
/-
**CategoryTheory.CatEnrichedOrdinary.hComp_id_heq** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.CatEnrichedOrdinary`。
形式化陈述：hComp_id_heq {a b : CatEnrichedOrdinary C} {f f' : a ⟶ b} (η : f ⟶ f') : H
Eq (hComp η (𝟙 (𝟙 b))) η
参数：η : f ⟶ f'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.CatEnrichedOrdinary.hComp_id`：hComp_id {a b : CatEnriched
Ordinary C} {f f' : a ⟶ b} (η : f ⟶ f') : hComp η (𝟙 (𝟙 b)) = eqToHom (comp_id f
) ≫ η ≫ eqToHom (comp_id f').symm
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem hComp_id_heq {a b : CatEnrichedOrdinary C} {f f' : a ⟶ b} (η : f ⟶ f') :
    HEq (hComp η (𝟙 (𝟙 b))) η := by simp [hComp_id]
/-
**CategoryTheory.CatEnrichedOrdinary.id_eq_eqToHom** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.CatEnrichedOrdinary`。
形式化陈述：id_eq_eqToHom {C} [Category* C] (X : C) : 𝟙 X = eqToHom rfl
参数：X : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_eq_eqToHom {C} [Category* C] (X : C) : 𝟙 X = eqToHom rfl := rfl
/-
**CategoryTheory.CatEnrichedOrdinary.hComp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.CatEnrichedOrdinary`。
形式化陈述：hComp_assoc {a b c d : CatEnrichedOrdinary C} {f f' : a ⟶ b} {g g' : b ⟶ c
} {h h' : c ⟶ d} (η : f ⟶ f') (θ : g ⟶ g') (κ : h ⟶ h') : hComp (hComp η θ) κ = 
eqToHom (assoc f g h) ≫ hComp η (hComp θ κ) ≫ eqToHom (assoc f' g' h').symm
参数：η : f ⟶ f'；θ : g ⟶ g'；κ : h ⟶ h'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CatEnrichedOrdinary.Hom.ext`：∀ {C : Type u} [inst : Categ
oryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.EnrichedOrdinaryCategory
 CategoryTheory.Cat C] {X Y : Ca…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.CatEnrichedOrdinary.homEquiv_comp`：homEquiv_comp {a b c :
 CatEnrichedOrdinary C} (f : a ⟶ b) (g : b ⟶ c) : homEquiv (f ≫ g) = homEquiv f 
≫ homEquiv g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.CatEnrichedOrdinary.Hom.base_eqToHom`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C]   [inst_1 : CategoryTheory.EnrichedOrdinar
yCategory CategoryTheory.Cat C] {X Y : Ca…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.CatEnriched.hComp_comp`：hComp_comp {a b c : CatEnriched C
} {f₁ f₂ f₃ : a ⟶ b} {g₁ g₂ g₃ : b ⟶ c} (η : f₁ ⟶ f₂) (η' : f₂ ⟶ f₃) (θ : g₁ ⟶ g
₂) (θ' : g₂ ⟶ g₃) : hComp η…
· 使用定理 `CategoryTheory.CatEnrichedOrdinary.id_eq_eqToHom`：id_eq_eqToHom {C} [Cat
egory* C] (X : C) : 𝟙 X = eqToHom rfl
· 使用定理 `CategoryTheory.CatEnriched.eqToHom_hComp_eqToHom`：eqToHom_hComp_eqToHom 
{a b c : CatEnriched C} {f f' : a ⟶ b} (α : f = f') {g g' : b ⟶ c} (β : g = g') 
: hComp (eqToHom α) (eqToHom β) = eqTo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem hComp_assoc {a b c d : CatEnrichedOrdinary C} {f f' : a ⟶ b} {g g' : b ⟶ c} {h h' : c ⟶ d}
    (η : f ⟶ f') (θ : g ⟶ g') (κ : h ⟶ h') :
    hComp (hComp η θ) κ =
      eqToHom (assoc f g h) ≫ hComp η (hComp θ κ) ≫ eqToHom (assoc f' g' h').symm := by
  ext
  simp only [hComp, base_mk, Hom.base_comp, Hom.base_eqToHom,
    ← heq_eq_eq, heq_eqToHom_comp_iff, heq_comp_eqToHom_iff,
    eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  conv => enter [1, 2]; exact ((id_comp _).trans (comp_id _)).symm
  conv => enter [2, 1]; exact ((id_comp _).trans (comp_id _)).symm
  iterate 4 rw [← CatEnriched.hComp_comp, id_eq_eqToHom, CatEnriched.eqToHom_hComp_eqToHom]
  simp [CatEnriched.hComp_assoc_heq]
/-
**CategoryTheory.CatEnrichedOrdinary.hComp_assoc_heq** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.CatEnrichedOrdinary`。
形式化陈述：hComp_assoc_heq {a b c d : CatEnrichedOrdinary C} {f f' : a ⟶ b} {g g' : b
 ⟶ c} {h h' : c ⟶ d} (η : f ⟶ f') (θ : g ⟶ g') (κ : h ⟶ h') : HEq (hComp (hComp 
η θ) κ) (hComp η (hComp θ κ))
参数：η : f ⟶ f'；θ : g ⟶ g'；κ : h ⟶ h'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.CatEnrichedOrdinary.hComp_assoc`：hComp_assoc {a b c d : C
atEnrichedOrdinary C} {f f' : a ⟶ b} {g g' : b ⟶ c} {h h' : c ⟶ d} (η : f ⟶ f') 
(θ : g ⟶ g') (κ : h ⟶ h') : hComp (h…
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem hComp_assoc_heq {a b c d : CatEnrichedOrdinary C}
    {f f' : a ⟶ b} {g g' : b ⟶ c} {h h' : c ⟶ d} (η : f ⟶ f') (θ : g ⟶ g') (κ : h ⟶ h') :
    HEq (hComp (hComp η θ) κ) (hComp η (hComp θ κ)) := by simp [hComp_assoc]

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.CatEnrichedOrdinary.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
CatEnrichedOrdinary`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Bicategory (CatEnrichedOrdinary C) where
  homCategory := inferInstance
  whiskerLeft {_ _ _} f {_ _} η := hComp (𝟙 f) η
  whiskerRight η h := hComp η (𝟙 h)
  associator f g h := eqToIso (assoc f g h)
  leftUnitor f := eqToIso (id_comp f)
  rightUnitor f := eqToIso (comp_id f)
  id_whiskerLeft := by simp [id_hComp]
  comp_whiskerLeft := by simp [← hComp_assoc]
  whiskerRight_id := by simp [hComp_id]
  whiskerRight_comp := by simp [hComp_assoc]
  whisker_assoc := by simp [hComp_assoc]
  pentagon := by simp [id_eq_eqToHom, -eqToHom_refl]
  triangle := by simp [id_eq_eqToHom, -eqToHom_refl]

/-- As the associator and left and right unitors are defined as eqToIso of category axioms, the
bicategory structure on `CatEnrichedOrdinary C` is strict. -/
/-
**CategoryTheory.CatEnrichedOrdinary.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
CatEnrichedOrdinary`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
As the associator and left and right unitors are defined as eqToIso of category 
axioms, the
bicategory structure on `CatEnrichedOrdinary C` is strict.
-/
instance : Bicategory.Strict (CatEnrichedOrdinary C) where

end CatEnrichedOrdinary

end

end CategoryTheory

