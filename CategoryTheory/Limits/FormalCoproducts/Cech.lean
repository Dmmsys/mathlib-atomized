/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic

/-!
# The Cech object for formal coproducts

Let `C` be a category that has finite products. In this file, we define a
functor `cechFunctor : FormalCoproduct C ⥤ SimplicialObject (FormalCoproduct C)`
which sends a formal coproduct of objects `U j` (for `j : ι`) to the simplicial object
which sends `⦋n⦌` to the formal coproduct, indexed by `i : Fin (n + 1) → ι`,
of the products of the objects `U (i a)` for all `a : Fin (n + 1)`.

-/

@[expose] public section

universe w t v u

namespace CategoryTheory.Limits.FormalCoproduct

variable {C : Type u} [Category.{v} C]

/-- Given `U : FormalCoproduct C` and a type `α`, this is the formal coproduct
indexed by all `i : α → U.I` of the products of the objects `U.obj (i a)`
for all `a : α`. -/
@[simps]
/-
**CategoryTheory.Limits.FormalCoproduct.power** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits.FormalCoproduct`。
形式化陈述：power (U : FormalCoproduct.{w} C) (α : Type t) [HasProductsOfShape α C] : 
FormalCoproduct.{max w t} C where I
参数：U : FormalCoproduct.{w} C；α : Type t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `U : FormalCoproduct C` and a type `α`, this is the formal coproduct
indexed by all `i : α → U.I` of the products of the objects `U.obj (i a)`
for all `a : α`.
-/
noncomputable def power (U : FormalCoproduct.{w} C) (α : Type t)
    [HasProductsOfShape α C] : FormalCoproduct.{max w t} C where
  I := α → U.I
  obj i := ∏ᶜ (U.obj ∘ i)

section

variable (U : FormalCoproduct.{w} C) (α : Type) [HasProductsOfShape α C]

variable {α} in
/-- The projection `U.power α ⟶ U` for each `a : α`. -/
@[simps]
/-
**CategoryTheory.Limits.FormalCoproduct.power** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits.FormalCoproduct`。
形式化陈述：power (U : FormalCoproduct.{w} C) (α : Type t) [HasProductsOfShape α C] : 
FormalCoproduct.{max w t} C where I
参数：U : FormalCoproduct.{w} C；α : Type t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection `U.power α ⟶ U` for each `a : α`.
-/
noncomputable def powerπ (a : α) : U.power α ⟶ U where
  f i := i a
  φ _ := Pi.π _ a

/-- The (limit) fan expressing that `U.power α` is a product of copies of
`U` indexed by `α`. -/
/-
**CategoryTheory.Limits.FormalCoproduct.powerFan** 是 Mathlib 中的一个缩写定义，位于命名空间 `Ca
tegoryTheory.Limits.FormalCoproduct`。
形式化陈述：powerFan : Fan (fun (_ : α) => U)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (limit) fan expressing that `U.power α` is a product of copies of
`U` indexed by `α`.
-/
noncomputable abbrev powerFan :
    Fan (fun (_ : α) ↦ U) :=
  Fan.mk (U.power α) U.powerπ

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- `U.power α` identifies to the product of copies of `U` indexed by `α`. -/
/-
**CategoryTheory.Limits.FormalCoproduct.isLimitPowerFan** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Limits.FormalCoproduct`。
形式化陈述：isLimitPowerFan : IsLimit (U.powerFan α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`U.power α` identifies to the product of copies of `U` indexed by `α`.
-/
noncomputable def isLimitPowerFan : IsLimit (U.powerFan α) :=
  Fan.IsLimit.mk _
    (fun s ↦
      { f i a := (s.proj a).f i
        φ i := Pi.lift (fun a ↦ (s.proj a).φ i) })
    (fun _ _ ↦ by ext <;> simp)
    (fun s m hm ↦ by
      obtain ⟨f, φ⟩ := m
      obtain rfl : f = fun i a ↦ (s.proj a).f i := by
        ext i
        dsimp
        ext a
        exact congr_fun (congr_arg FormalCoproduct.Hom.f (hm a)) i
      ext i
      · rfl
      · dsimp
        ext a
        specialize hm a
        rw [hom_ext_iff] at hm
        obtain ⟨_, hm⟩ := hm
        simpa using hm i)

end

/-- For any morphism `f : U ⟶ V` in `FormalCoproduct C` and a type `α`,
this is the induced map `U.power α ⟶ V.power α`. -/
@[simps -fullyApplied]
/-
**CategoryTheory.Limits.FormalCoproduct.powerMap** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits.FormalCoproduct`。
形式化陈述：powerMap {U V : FormalCoproduct.{w} C} (f : U ⟶ V) (α : Type t) [HasProduc
tsOfShape α C] : U.power α ⟶ V.power α where f i
参数：f : U ⟶ V；α : Type t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For any morphism `f : U ⟶ V` in `FormalCoproduct C` and a type `α`,
this is the induced map `U.power α ⟶ V.power α`.
-/
noncomputable def powerMap {U V : FormalCoproduct.{w} C} (f : U ⟶ V) (α : Type t)
    [HasProductsOfShape α C] :
    U.power α ⟶ V.power α where
  f i := f.f ∘ i
  φ i := Pi.map (fun a ↦ f.φ (i a))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Limits.FormalCoproduct.powerMap_id** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Limits.FormalCoproduct`。
形式化陈述：powerMap_id (U : FormalCoproduct.{w} C) (α : Type t) [HasProductsOfShape α
 C] : powerMap (𝟙 U) α = 𝟙 _
参数：U : FormalCoproduct.{w} C；α : Type t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.FormalCoproduct.hom_ext`：hom_ext {X Y : FormalCopr
oduct.{w} C} {f g : X ⟶ Y} (h₁ : f.f = g.f) (h₂ : forall (i : X.I), f.φ i ≫ eqTo
Hom (by rw [h₁]) = g.φ i) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.Pi.hom_ext`：∀ {β : Type w} {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limits.Ha
sProduct f] {X : C} (g…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.Pi.map_π`：∀ {β : Type w} {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {f g : β → C}   [inst_1 : CategoryTheory.Limits.Ha
sProduct f] [inst_2 …
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma powerMap_id (U : FormalCoproduct.{w} C) (α : Type t) [HasProductsOfShape α C] :
    powerMap (𝟙 U) α = 𝟙 _ := by
  cat_disch

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.Limits.FormalCoproduct.powerMap_comp** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Limits.FormalCoproduct`。
形式化陈述：powerMap_comp {U V W : FormalCoproduct.{w} C} (f : U ⟶ V) (g : V ⟶ W) (α :
 Type t) [HasProductsOfShape α C] : powerMap (f ≫ g) α = powerMap f α ≫ powerMap
 g α
参数：f : U ⟶ V；g : V ⟶ W；α : Type t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.FormalCoproduct.hom_ext`：hom_ext {X Y : FormalCopr
oduct.{w} C} {f g : X ⟶ Y} (h₁ : f.f = g.f) (h₂ : forall (i : X.I), f.φ i ≫ eqTo
Hom (by rw [h₁]) = g.φ i) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Limits.Pi.hom_ext`：∀ {β : Type w} {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limits.Ha
sProduct f] {X : C} (g…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.Pi.map_π`：∀ {β : Type w} {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {f g : β → C}   [inst_1 : CategoryTheory.Limits.Ha
sProduct f] [inst_2 …
· 使用定理 `CategoryTheory.Limits.Pi.map_π_assoc`：∀ {β : Type w} {C : Type u} [inst 
: CategoryTheory.Category.{v, u} C] {f g : β → C}   [inst_1 : CategoryTheory.Lim
its.HasProduct f] [inst_2 …
-/
lemma powerMap_comp {U V W : FormalCoproduct.{w} C} (f : U ⟶ V) (g : V ⟶ W) (α : Type t)
    [HasProductsOfShape α C] :
    powerMap (f ≫ g) α = powerMap f α ≫ powerMap g α := by
  ext
  · cat_disch
  · dsimp
    ext
    simp only [Category.comp_id, Category.assoc, Pi.map_π, Function.comp_apply,
      Pi.map_π_assoc]
    apply Pi.map_π

attribute [local simp] powerMap_comp

/-- Given a type `α`, this is the functor `FormalCoproduct C ⥤ FormalCoproduct C`
which sends `U` to `U.power α`. -/
@[simps]
/-
**CategoryTheory.Limits.FormalCoproduct.powerFunctor** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits.FormalCoproduct`。
形式化陈述：powerFunctor (α : Type t) [HasProductsOfShape α C] : FormalCoproduct.{w} C
 ⥤ FormalCoproduct.{max w t} C where obj U
参数：α : Type t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a type `α`, this is the functor `FormalCoproduct C ⥤ FormalCoproduct C`
which sends `U` to `U.power α`.
-/
noncomputable def powerFunctor (α : Type t) [HasProductsOfShape α C] :
    FormalCoproduct.{w} C ⥤ FormalCoproduct.{max w t} C where
  obj U := U.power α
  map f := powerMap f α

/-- The functoriality of `FormalCoproduct.power` with respect to the index type. -/
@[simps -fullyApplied]
/-
**CategoryTheory.Limits.FormalCoproduct.mapPower** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits.FormalCoproduct`。
形式化陈述：mapPower (U : FormalCoproduct.{w} C) {α β : Type t} [HasProductsOfShape α 
C] [HasProductsOfShape β C] (f : α -> β) : U.power β ⟶ U.power α where f i
参数：U : FormalCoproduct.{w} C；f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functoriality of `FormalCoproduct.power` with respect to the index type.
-/
noncomputable def mapPower (U : FormalCoproduct.{w} C) {α β : Type t}
    [HasProductsOfShape α C] [HasProductsOfShape β C] (f : α → β) :
    U.power β ⟶ U.power α where
  f i := i ∘ f
  φ _ := Pi.lift (fun _ ↦ Pi.π _ _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Limits.FormalCoproduct.mapPower_id** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Limits.FormalCoproduct`。
形式化陈述：mapPower_id (U : FormalCoproduct.{w} C) (α : Type t) [HasProductsOfShape α
 C] : U.mapPower (id : α -> α) = 𝟙 _
参数：U : FormalCoproduct.{w} C；α : Type t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.FormalCoproduct.hom_ext`：hom_ext {X Y : FormalCopr
oduct.{w} C} {f g : X ⟶ Y} (h₁ : f.f = g.f) (h₂ : forall (i : X.I), f.φ i ≫ eqTo
Hom (by rw [h₁]) = g.φ i) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.Pi.hom_ext`：∀ {β : Type w} {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limits.Ha
sProduct f] {X : C} (g…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma mapPower_id (U : FormalCoproduct.{w} C) (α : Type t)
    [HasProductsOfShape α C] :
    U.mapPower (id : α → α) = 𝟙 _ := by
  cat_disch

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.Limits.FormalCoproduct.mapPower_comp** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Limits.FormalCoproduct`。
形式化陈述：mapPower_comp (U : FormalCoproduct.{w} C) {α β γ : Type t} [HasProductsOfS
hape α C] [HasProductsOfShape β C] [HasProductsOfShape γ C] (f : α -> β) (g : β 
-> γ) : U.mapPower (g ∘ f) = U.mapPower g ≫ U.mapPower f
参数：U : FormalCoproduct.{w} C；f : α -> β；g : β -> γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.FormalCoproduct.hom_ext`：hom_ext {X Y : FormalCopr
oduct.{w} C} {f g : X ⟶ Y} (h₁ : f.f = g.f) (h₂ : forall (i : X.I), f.φ i ≫ eqTo
Hom (by rw [h₁]) = g.φ i) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Limits.Pi.hom_ext`：∀ {β : Type w} {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limits.Ha
sProduct f] {X : C} (g…
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
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapPower_comp (U : FormalCoproduct.{w} C) {α β γ : Type t}
    [HasProductsOfShape α C] [HasProductsOfShape β C] [HasProductsOfShape γ C]
    (f : α → β) (g : β → γ) :
    U.mapPower (g ∘ f) = U.mapPower g ≫ U.mapPower f := by
  ext
  · cat_disch
  · dsimp
    ext
    simp [Function.comp_def]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.Limits.FormalCoproduct.mapPower_powerMap** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Limits.FormalCoproduct`。
形式化陈述：mapPower_powerMap {U V : FormalCoproduct.{w} C} (f : U ⟶ V) {α β : Type t}
 [HasProductsOfShape α C] [HasProductsOfShape β C] (g : α -> β) : U.mapPower g ≫
 powerMap f α = powerMap f β ≫ V.mapPower g
参数：f : U ⟶ V；g : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Limits.FormalCoproduct.hom_ext`：hom_ext {X Y : FormalCopr
oduct.{w} C} {f g : X ⟶ Y} (h₁ : f.f = g.f) (h₂ : forall (i : X.I), f.φ i ≫ eqTo
Hom (by rw [h₁]) = g.φ i) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Limits.Pi.hom_ext`：∀ {β : Type w} {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limits.Ha
sProduct f] {X : C} (g…
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
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.Pi.map_π`：∀ {β : Type w} {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {f g : β → C}   [inst_1 : CategoryTheory.Limits.Ha
sProduct f] [inst_2 …
· 使用定理 `CategoryTheory.Limits.limit.lift_π_assoc`：∀ {J : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v,
 u} C]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapPower_powerMap {U V : FormalCoproduct.{w} C} (f : U ⟶ V)
    {α β : Type t} [HasProductsOfShape α C] [HasProductsOfShape β C] (g : α → β) :
    U.mapPower g ≫ powerMap f α = powerMap f β ≫ V.mapPower g := by
  ext
  · cat_disch
  · dsimp
    ext
    simp [Function.comp_def]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.FormalCoproduct.mapPower_** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Limits.FormalCoproduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapPower_π (U : FormalCoproduct.{w} C) {α β : Type}
    [HasProductsOfShape α C] [HasProductsOfShape β C] (f : α → β) (a : α) :
    mapPower U f ≫ U.powerπ a = U.powerπ (f a) := by
  ext <;> simp

attribute [local simp] mapPower_comp mapPower_powerMap

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The functor `(Type t)ᵒᵖ ⥤ FormalCoproduct.{w} C ⥤ FormalCoproduct.{max w t} C`
which sends a type `α` and `U : FormalCoproduct C` to `U.power α`. -/
@[simps]
/-
**CategoryTheory.Limits.FormalCoproduct.powerBifunctor** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Limits.FormalCoproduct`。
形式化陈述：powerBifunctor [HasProducts.{t} C] : Type tᵒᵖ ⥤ FormalCoproduct.{w} C ⥤ Fo
rmalCoproduct.{max w t} C where obj α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `(Type t)ᵒᵖ ⥤ FormalCoproduct.{w} C ⥤ FormalCoproduct.{max w t} C`
which sends a type `α` and `U : FormalCoproduct C` to `U.power α`.
-/
noncomputable def powerBifunctor [HasProducts.{t} C] :
    Type tᵒᵖ ⥤ FormalCoproduct.{w} C ⥤ FormalCoproduct.{max w t} C where
  obj α := powerFunctor α.unop
  map f := { app _ := mapPower _ f.unop }
  map_comp _ _ := by ext : 2; simp [types_comp]

variable [HasFiniteProducts C]

/-- Given `U : FormalCoproduct C`, this is the simplicial object
in `FormalCoproduct C` which sends `⦋n⦌` to `U.power (Fin (n + 1))`. -/
@[simps]
/-
**CategoryTheory.Limits.FormalCoproduct.cech** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits.FormalCoproduct`。
形式化陈述：cech (U : FormalCoproduct.{w} C) : SimplicialObject (FormalCoproduct.{w} C
) where obj n
参数：U : FormalCoproduct.{w} C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `U : FormalCoproduct C`, this is the simplicial object
in `FormalCoproduct C` which sends `⦋n⦌` to `U.power (Fin (n + 1))`.
-/
noncomputable def cech (U : FormalCoproduct.{w} C) :
    SimplicialObject (FormalCoproduct.{w} C) where
  obj n := U.power (ToType n.unop)
  map f := U.mapPower f.unop.toOrderHom.toFun

set_option backward.defeqAttrib.useBackward true in
/-- The functor `FormalCoproduct C ⥤ SimplicialObject (FormalCoproduct C)`
which sends a formal coproduct to its Cech object. -/
@[simps]
/-
**CategoryTheory.Limits.FormalCoproduct.cechFunctor** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits.FormalCoproduct`。
形式化陈述：cechFunctor : FormalCoproduct.{w} C ⥤ SimplicialObject (FormalCoproduct.{w
} C) where obj U
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `FormalCoproduct C ⥤ SimplicialObject (FormalCoproduct C)`
which sends a formal coproduct to its Cech object.
-/
noncomputable def cechFunctor :
    FormalCoproduct.{w} C ⥤ SimplicialObject (FormalCoproduct.{w} C) where
  obj U := U.cech
  map f := { app _ := powerMap f _ }
  map_comp _ _ := by ext : 1; simp

end CategoryTheory.Limits.FormalCoproduct

