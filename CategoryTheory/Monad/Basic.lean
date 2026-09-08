/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Bhavik Mehta, Adam Topaz
-/
module

public import Mathlib.CategoryTheory.EpiMono

/-!
# Monads

We construct the categories of monads and comonads, and their forgetful functors to endofunctors.

(Note that these are the category theorist's monads, not the programmers monads.
For the translation, see the file `Mathlib/CategoryTheory/Monad/Types.lean`.)

For the fact that monads are "just" monoids in the category of endofunctors, see the file
`CategoryTheory.Monad.EquivMon`.
-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section


namespace CategoryTheory

open Category

universe v₁ u₁

-- morphism levels before object levels. See note [category theory universes].
variable (C : Type u₁) [Category.{v₁} C]

/-- The data of a monad on C consists of an endofunctor T together with natural transformations
`η : 𝟭 C ⟶ T` and `μ : T ⋙ T ⟶ T` satisfying three equations:
- `T μ_X ≫ μ_X = μ_(TX) ≫ μ_X` (associativity)
- `η_(TX) ≫ μ_X = 1_X` (left unit)
- `Tη_X ≫ μ_X = 1_X` (right unit)
-/
/-
**CategoryTheory.Monad** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory`。
形式化陈述：Monad extends C ⥤ C where /-- The unit for the monad. -/ η : 𝟭 _ ⟶ toFunct
or /-- The multiplication for the monad. -/ μ : toFunctor ⋙ toFunctor ⟶ toFuncto
r assoc : forall X, toFunctor.map (NatTrans.app μ X) ≫ μ.app _ = μ.app _ ≫ μ.app
 _
继承自：C ⥤ C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The data of a monad on C consists of an endofunctor T together with natural tran
sformations
`η : 𝟭 C ⟶ T` and `μ : T ⋙ T ⟶ T` satisfying three equations:
- `T μ_X ≫ μ_X = μ_(TX) ≫ μ_X` (associativity)
- `η_(TX) ≫ μ_X = 1_X` (left unit)
- `Tη_X ≫ μ_X = 1_X` (right unit)
-/
structure Monad extends C ⥤ C where
  /-- The unit for the monad. -/
  η : 𝟭 _ ⟶ toFunctor
  /-- The multiplication for the monad. -/
  μ : toFunctor ⋙ toFunctor ⟶ toFunctor
  assoc : ∀ X, toFunctor.map (NatTrans.app μ X) ≫ μ.app _ = μ.app _ ≫ μ.app _ := by cat_disch
  left_unit : ∀ X : C, η.app (toFunctor.obj X) ≫ μ.app _ = 𝟙 _ := by cat_disch
  right_unit : ∀ X : C, toFunctor.map (η.app X) ≫ μ.app _ = 𝟙 _ := by cat_disch

@[reassoc]
/-
**CategoryTheory.Monad.unit_naturality** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.Monad`。
形式化陈述：∀ (C : Type u₁) [inst : CategoryTheory.Category.{v₁, u₁} C] (T : CategoryT
heory.Monad C) ⦃X Y : C⦄ (f : X ⟶ Y),   CategoryTheory.CategoryStruct.comp f (T.
η.app Y) = CategoryTheory.CategoryStruct.comp (T.η.app X) (T.map f)
参数：C : Type u₁；T : CategoryTheory.Monad C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
lemma Monad.unit_naturality (T : Monad C) ⦃X Y : C⦄ (f : X ⟶ Y) :
    f ≫ T.η.app Y = T.η.app X ≫ T.map f :=
  T.η.naturality _

@[reassoc]
/-
**CategoryTheory.Monad.mu_naturality** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.M
onad`。
形式化陈述：∀ (C : Type u₁) [inst : CategoryTheory.Category.{v₁, u₁} C] (T : CategoryT
heory.Monad C) ⦃X Y : C⦄ (f : X ⟶ Y),   CategoryTheory.CategoryStruct.comp (T.ma
p (T.map f)) (T.μ.app Y) =     CategoryTheory.CategoryStruct.comp (T.μ.app X) (T
.map f)
参数：C : Type u₁；T : CategoryTheory.Monad C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
lemma Monad.mu_naturality (T : Monad C) ⦃X Y : C⦄ (f : X ⟶ Y) :
    T.map (T.map f) ≫ T.μ.app Y = T.μ.app X ≫ T.map f :=
  T.μ.naturality _

/-- The data of a comonad on C consists of an endofunctor G together with natural transformations
`ε : G ⟶ 𝟭 C` and `δ : G ⟶ G ⋙ G` satisfying three equations:
- `δ_X ≫ G δ_X = δ_X ≫ δ_(GX)` (coassociativity)
- `δ_X ≫ ε_(GX) = 1_X` (left counit)
- `δ_X ≫ G ε_X = 1_X` (right counit)
-/
/-
**CategoryTheory.Comonad** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory`。
形式化陈述：Comonad extends C ⥤ C where /-- The counit for the comonad. -/ ε : toFunct
or ⟶ 𝟭 _ /-- The comultiplication for the comonad. -/ δ : toFunctor ⟶ toFunctor 
⋙ toFunctor coassoc : forall X, NatTrans.app δ _ ≫ toFunctor.map (δ.app X) = δ.a
pp _ ≫ δ.app _
继承自：C ⥤ C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The data of a comonad on C consists of an endofunctor G together with natural tr
ansformations
`ε : G ⟶ 𝟭 C` and `δ : G ⟶ G ⋙ G` satisfying three equations:
- `δ_X ≫ G δ_X = δ_X ≫ δ_(GX)` (coassociativity)
- `δ_X ≫ ε_(GX) = 1_X` (left counit)
- `δ_X ≫ G ε_X = 1_X` (right counit)
-/
structure Comonad extends C ⥤ C where
  /-- The counit for the comonad. -/
  ε : toFunctor ⟶ 𝟭 _
  /-- The comultiplication for the comonad. -/
  δ : toFunctor ⟶ toFunctor ⋙ toFunctor
  coassoc : ∀ X, NatTrans.app δ _ ≫ toFunctor.map (δ.app X) = δ.app _ ≫ δ.app _ := by
    cat_disch
  left_counit : ∀ X : C, δ.app X ≫ ε.app (toFunctor.obj X) = 𝟙 _ := by cat_disch
  right_counit : ∀ X : C, δ.app X ≫ toFunctor.map (ε.app X) = 𝟙 _ := by cat_disch

@[reassoc]
/-
**CategoryTheory.Comonad.counit_naturality** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Comonad`。
形式化陈述：∀ (C : Type u₁) [inst : CategoryTheory.Category.{v₁, u₁} C] (T : CategoryT
heory.Comonad C) ⦃X Y : C⦄ (f : X ⟶ Y),   CategoryTheory.CategoryStruct.comp (T.
map f) (T.ε.app Y) = CategoryTheory.CategoryStruct.comp (T.ε.app X) f
参数：C : Type u₁；T : CategoryTheory.Comonad C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
lemma Comonad.counit_naturality (T : Comonad C) ⦃X Y : C⦄ (f : X ⟶ Y) :
    T.map f ≫ T.ε.app Y = T.ε.app X ≫ f :=
  T.ε.naturality _

@[reassoc]
/-
**CategoryTheory.Comonad.delta_naturality** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Comonad`。
形式化陈述：∀ (C : Type u₁) [inst : CategoryTheory.Category.{v₁, u₁} C] (T : CategoryT
heory.Comonad C) ⦃X Y : C⦄ (f : X ⟶ Y),   CategoryTheory.CategoryStruct.comp (T.
map f) (T.δ.app Y) =     CategoryTheory.CategoryStruct.comp (T.δ.app X) (T.map (
T.map f))
参数：C : Type u₁；T : CategoryTheory.Comonad C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
lemma Comonad.delta_naturality (T : Comonad C) ⦃X Y : C⦄ (f : X ⟶ Y) :
    T.map f ≫ T.δ.app Y = T.δ.app X ≫ T.map (T.map f) :=
  T.δ.naturality _

variable {C}
variable (T : Monad C) (G : Comonad C)
/-
**CategoryTheory.coeMonad** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：coeMonad : Coe (Monad C) (C ⥤ C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance coeMonad : Coe (Monad C) (C ⥤ C) :=
  ⟨fun T => T.toFunctor⟩
/-
**CategoryTheory.coeComonad** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
形式化陈述：coeComonad : Coe (Comonad C) (C ⥤ C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance coeComonad : Coe (Comonad C) (C ⥤ C) :=
  ⟨fun G => G.toFunctor⟩

initialize_simps_projections CategoryTheory.Monad (toFunctor → coe)

initialize_simps_projections CategoryTheory.Comonad (toFunctor → coe)

-- TODO: investigate whether `Monad.assoc` can be a `simp` lemma?
attribute [reassoc (attr := simp)] Monad.left_unit Monad.right_unit
attribute [reassoc (attr := simp)] Comonad.coassoc Comonad.left_counit Comonad.right_counit

/-- A morphism of monads is a natural transformation compatible with η and μ. -/
@[ext]
/-
**CategoryTheory.MonadHom** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory`。
形式化陈述：MonadHom (T₁ T₂ : Monad C) extends NatTrans (T₁ : C ⥤ C) T₂ where app_η : 
forall X, T₁.η.app X ≫ app X = T₂.η.app X
参数：T₁ T₂ : Monad C；T₁ : C ⥤ C。
继承自：NatTrans (T₁ : C ⥤ C) T₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of monads is a natural transformation compatible with η and μ.
-/
structure MonadHom (T₁ T₂ : Monad C) extends NatTrans (T₁ : C ⥤ C) T₂ where
  app_η : ∀ X, T₁.η.app X ≫ app X = T₂.η.app X := by cat_disch
  app_μ : ∀ X, T₁.μ.app X ≫ app X = (T₁.map (app X) ≫ app _) ≫ T₂.μ.app X := by
    cat_disch

initialize_simps_projections MonadHom (+toNatTrans, -app)

/-- A morphism of comonads is a natural transformation compatible with ε and δ. -/
@[ext]
/-
**CategoryTheory.ComonadHom** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheory`。
形式化陈述：ComonadHom (M N : Comonad C) extends NatTrans (M : C ⥤ C) N where app_ε : 
forall X, app X ≫ N.ε.app X = M.ε.app X
参数：M N : Comonad C；M : C ⥤ C。
继承自：NatTrans (M : C ⥤ C) N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of comonads is a natural transformation compatible with ε and δ.
-/
structure ComonadHom (M N : Comonad C) extends NatTrans (M : C ⥤ C) N where
  app_ε : ∀ X, app X ≫ N.ε.app X = M.ε.app X := by cat_disch
  app_δ : ∀ X, app X ≫ N.δ.app X = M.δ.app X ≫ app _ ≫ N.map (app X) := by cat_disch

initialize_simps_projections ComonadHom (+toNatTrans, -app)

attribute [reassoc (attr := simp)] MonadHom.app_η MonadHom.app_μ
attribute [reassoc (attr := simp)] ComonadHom.app_ε ComonadHom.app_δ
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Quiver (Monad C) where
  Hom := MonadHom
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Quiver (Comonad C) where
  Hom := ComonadHom

@[ext]
/-
**CategoryTheory.MonadHom.ext'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.MonadHo
m`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {T₁ T₂ : Categ
oryTheory.Monad C} (f g : T₁ ⟶ T₂),   f.app = g.app → f = g
参数：f g : T₁ ⟶ T₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MonadHom.ext`：∀ {C : Type u₁} {inst : CategoryTheory.Cate
gory.{v₁, u₁} C} {T₁ T₂ : CategoryTheory.Monad C}   {x y : CategoryTheory.MonadH
om T₁ T₂}, x.app …
-/
lemma MonadHom.ext' {T₁ T₂ : Monad C} (f g : T₁ ⟶ T₂) (h : f.app = g.app) : f = g :=
  MonadHom.ext h

@[ext]
/-
**CategoryTheory.ComonadHom.ext'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Comon
adHom`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {T₁ T₂ : Categ
oryTheory.Comonad C} (f g : T₁ ⟶ T₂),   f.app = g.app → f = g
参数：f g : T₁ ⟶ T₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ComonadHom.ext`：∀ {C : Type u₁} {inst : CategoryTheory.Ca
tegory.{v₁, u₁} C} {M N : CategoryTheory.Comonad C}   {x y : CategoryTheory.Como
nadHom M N}, x.app …
-/
lemma ComonadHom.ext' {T₁ T₂ : Comonad C} (f g : T₁ ⟶ T₂) (h : f.app = g.app) : f = g :=
  ComonadHom.ext h
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (Monad C) where
  id M := { toNatTrans := 𝟙 (M : C ⥤ C) }
  comp f g :=
    { toNatTrans :=
        { app := fun X => f.app X ≫ g.app X
          naturality := fun X Y h => by rw [assoc, f.1.naturality_assoc, g.1.naturality] } }

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (Comonad C) where
  id M := { toNatTrans := 𝟙 (M : C ⥤ C) }
  comp f g :=
    { toNatTrans :=
        { app := fun X => f.app X ≫ g.app X
          naturality := fun X Y h => by rw [assoc, f.1.naturality_assoc, g.1.naturality] } }
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {T : Monad C} : Inhabited (MonadHom T T) :=
  ⟨𝟙 T⟩

@[simp]
/-
**CategoryTheory.MonadHom.id_toNatTrans** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.MonadHom`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (T : CategoryT
heory.Monad C),   (CategoryTheory.CategoryStruct.id T).toNatTrans = CategoryTheo
ry.CategoryStruct.id T.toFunctor
参数：T : CategoryTheory.Monad C；CategoryTheory.CategoryStruct.id T。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MonadHom.id_toNatTrans (T : Monad C) : (𝟙 T : T ⟶ T).toNatTrans = 𝟙 (T : C ⥤ C) :=
  rfl

@[simp]
/-
**CategoryTheory.MonadHom.comp_toNatTrans** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.MonadHom`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {T₁ T₂ T₃ : Ca
tegoryTheory.Monad C} (f : T₁ ⟶ T₂)   (g : T₂ ⟶ T₃),   (CategoryTheory.CategoryS
truct.comp f g).toNatTrans = CategoryTheory.CategoryStruct.comp f.toNatTrans g.t
oNatTrans
参数：f : T₁ ⟶ T₂；g : T₂ ⟶ T₃；CategoryTheory.CategoryStruct.comp f g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MonadHom.comp_toNatTrans {T₁ T₂ T₃ : Monad C} (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃) :
    (f ≫ g).toNatTrans = ((f.toNatTrans : _ ⟶ (T₂ : C ⥤ C)) ≫ g.toNatTrans : (T₁ : C ⥤ C) ⟶ T₃) :=
  rfl
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {G : Comonad C} : Inhabited (ComonadHom G G) :=
  ⟨𝟙 G⟩

@[simp]
/-
**CategoryTheory.ComonadHom.id_toNatTrans** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.ComonadHom`。
形式化陈述：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (T : CategoryT
heory.Comonad C),   (CategoryTheory.CategoryStruct.id T).toNatTrans = CategoryTh
eory.CategoryStruct.id T.toFunctor
参数：T : CategoryTheory.Comonad C；CategoryTheory.CategoryStruct.id T。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ComonadHom.id_toNatTrans (T : Comonad C) : (𝟙 T : T ⟶ T).toNatTrans = 𝟙 (T : C ⥤ C) :=
  rfl

@[simp]
/-
**CategoryTheory.comp_toNatTrans** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：comp_toNatTrans {T₁ T₂ T₃ : Comonad C} (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃) : (f ≫ 
g).toNatTrans = ((f.toNatTrans : _ ⟶ (T₂ : C ⥤ C)) ≫ g.toNatTrans : (T₁ : C ⥤ C)
 ⟶ T₃)
参数：f : T₁ ⟶ T₂；g : T₂ ⟶ T₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_toNatTrans {T₁ T₂ T₃ : Comonad C} (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃) :
    (f ≫ g).toNatTrans = ((f.toNatTrans : _ ⟶ (T₂ : C ⥤ C)) ≫ g.toNatTrans : (T₁ : C ⥤ C) ⟶ T₃) :=
  rfl

/-- Construct a monad isomorphism from a natural isomorphism of functors where the forward
direction is a monad morphism. -/
@[simps]
/-
**CategoryTheory.MonadIso.mk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.MonadIso`
。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {M N :
 CategoryTheory.Monad C} →       (f : M.toFunctor ≅ N.toFunctor) →         autoP
aram (∀ (X : C), CategoryTheory.CategoryStruct.comp (M.η.app X) (f.hom.app X) = 
N.η.app X)             CategoryTheory.MonadIso.mk._auto_1 →           autoParam 
              (∀ (X : C),                 CategoryTheory.CategoryStruct.comp (M.
μ.app X) (f.hom.app X) =                   CategoryTheory.CategoryStruct.comp   
                  (CategoryTheory.CategoryStruct.comp (M.map (f.hom.app X)) (f.h
om.app (N.obj X))) (N.μ.app X))               CategoryTheory.MonadIso.mk._auto_3
 →             (M ≅ N)
参数：f : M.toFunctor ≅ N.toFunctor；∀ (X : C), CategoryTheory.CategoryStruct.comp (
M.η.app X) (f.hom.app X) = N.η.app X；∀ (X : C),                 CategoryTheory.C
ategoryStruct.comp (M.μ.app X) (f.hom.app X) =                   CategoryTheory.
CategoryStruct.comp                     (CategoryTheory.CategoryStruct.comp (M.m
ap (f.hom.app X)) (f.hom.app (N.obj X))) (N.μ.app X)；M ≅ N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a monad isomorphism from a natural isomorphism of functors where the f
orward
direction is a monad morphism.
-/
def MonadIso.mk {M N : Monad C} (f : (M : C ⥤ C) ≅ N)
    (f_η : ∀ (X : C), M.η.app X ≫ f.hom.app X = N.η.app X := by cat_disch)
    (f_μ : ∀ (X : C), M.μ.app X ≫ f.hom.app X =
    (M.map (f.hom.app X) ≫ f.hom.app (N.obj X)) ≫ N.μ.app X := by cat_disch) : M ≅ N where
  hom :=
    { toNatTrans := f.hom
      app_η := f_η
      app_μ := f_μ }
  inv :=
    { toNatTrans := f.inv
      app_η := fun X => by simp [← f_η]
      app_μ := fun X => by
        rw [← NatIso.cancel_natIso_hom_right f]
        simp only [NatTrans.naturality, Iso.inv_hom_id_app, assoc, comp_id, f_μ,
          NatTrans.naturality_assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc]
        simp }

/-- Construct a comonad isomorphism from a natural isomorphism of functors where the forward
direction is a comonad morphism. -/
@[simps]
/-
**CategoryTheory.ComonadIso.mk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Comonad
Iso`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] →     {M N :
 CategoryTheory.Comonad C} →       (f : M.toFunctor ≅ N.toFunctor) →         aut
oParam (∀ (X : C), CategoryTheory.CategoryStruct.comp (f.hom.app X) (N.ε.app X) 
= M.ε.app X)             CategoryTheory.ComonadIso.mk._auto_1 →           autoPa
ram               (∀ (X : C),                 CategoryTheory.CategoryStruct.comp
 (f.hom.app X) (N.δ.app X) =                   CategoryTheory.CategoryStruct.com
p (M.δ.app X)                     (CategoryTheory.CategoryStruct.comp (f.hom.app
 (M.obj X)) (N.map (f.hom.app X))))               CategoryTheory.ComonadIso.mk._
auto_3 →             (M ≅ N)
参数：f : M.toFunctor ≅ N.toFunctor；∀ (X : C), CategoryTheory.CategoryStruct.comp (
f.hom.app X) (N.ε.app X) = M.ε.app X；∀ (X : C),                 CategoryTheory.C
ategoryStruct.comp (f.hom.app X) (N.δ.app X) =                   CategoryTheory.
CategoryStruct.comp (M.δ.app X)                     (CategoryTheory.CategoryStru
ct.comp (f.hom.app (M.obj X)) (N.map (f.hom.app X)))；M ≅ N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a comonad isomorphism from a natural isomorphism of functors where the
 forward
direction is a comonad morphism.
-/
def ComonadIso.mk {M N : Comonad C} (f : (M : C ⥤ C) ≅ N)
    (f_ε : ∀ (X : C), f.hom.app X ≫ N.ε.app X = M.ε.app X := by cat_disch)
    (f_δ : ∀ (X : C), f.hom.app X ≫ N.δ.app X =
    M.δ.app X ≫ f.hom.app (M.obj X) ≫ N.map (f.hom.app X) := by cat_disch) : M ≅ N where
  hom :=
    { toNatTrans := f.hom
      app_ε := f_ε
      app_δ := f_δ }
  inv :=
    { toNatTrans := f.inv
      app_ε := fun X => by simp [← f_ε]
      app_δ := fun X => by
        rw [← NatIso.cancel_natIso_hom_left f]
        simp only [reassoc_of% (f_δ X), Iso.hom_inv_id_app_assoc, NatTrans.naturality_assoc]
        rw [← Functor.map_comp, Iso.hom_inv_id_app, Functor.map_id]
        apply (comp_id _).symm }

variable (C)

/-- The forgetful functor from the category of monads to the category of endofunctors.
-/
@[simps!]
/-
**CategoryTheory.monadToFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：monadToFunctor : Monad C ⥤ C ⥤ C where obj T
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from the category of monads to the category of endofunctor
s.
-/
def monadToFunctor : Monad C ⥤ C ⥤ C where
  obj T := T
  map f := f.toNatTrans
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (monadToFunctor C).Faithful where
/-
**CategoryTheory.monadToFunctor_mapIso_monad_iso_mk** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory`。
形式化陈述：monadToFunctor_mapIso_monad_iso_mk {M N : Monad C} (f : (M : C ⥤ C) ≅ N) (
f_η f_μ) : (monadToFunctor _).mapIso (MonadIso.mk f f_η f_μ) = f
参数：f : (M : C ⥤ C) ≅ N；f_η f_μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem monadToFunctor_mapIso_monad_iso_mk {M N : Monad C} (f : (M : C ⥤ C) ≅ N) (f_η f_μ) :
    (monadToFunctor _).mapIso (MonadIso.mk f f_η f_μ) = f := by
  ext
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (monadToFunctor C).ReflectsIsomorphisms where
  reflects f _ := (MonadIso.mk (asIso ((monadToFunctor C).map f)) f.app_η f.app_μ).isIso_hom

/-- The forgetful functor from the category of comonads to the category of endofunctors.
-/
@[simps!]
/-
**CategoryTheory.comonadToFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：comonadToFunctor : Comonad C ⥤ C ⥤ C where obj G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from the category of comonads to the category of endofunct
ors.
-/
def comonadToFunctor : Comonad C ⥤ C ⥤ C where
  obj G := G
  map f := f.toNatTrans
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (comonadToFunctor C).Faithful where
/-
**CategoryTheory.comonadToFunctor_mapIso_comonad_iso_mk** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory`。
形式化陈述：comonadToFunctor_mapIso_comonad_iso_mk {M N : Comonad C} (f : (M : C ⥤ C) 
≅ N) (f_ε f_δ) : (comonadToFunctor _).mapIso (ComonadIso.mk f f_ε f_δ) = f
参数：f : (M : C ⥤ C) ≅ N；f_ε f_δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem comonadToFunctor_mapIso_comonad_iso_mk {M N : Comonad C} (f : (M : C ⥤ C) ≅ N) (f_ε f_δ) :
    (comonadToFunctor _).mapIso (ComonadIso.mk f f_ε f_δ) = f := by
  ext
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (comonadToFunctor C).ReflectsIsomorphisms where
  reflects f _ := (ComonadIso.mk (asIso ((comonadToFunctor C).map f)) f.app_ε f.app_δ).isIso_hom

variable {C}

/-- An isomorphism of monads gives a natural isomorphism of the underlying functors.
-/
@[simps (rhsMd := .default)]
/-
**CategoryTheory.MonadIso.toNatIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Mon
adIso`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] → {M N : Cat
egoryTheory.Monad C} → (M ≅ N) → (M.toFunctor ≅ N.toFunctor)
参数：M ≅ N；M.toFunctor ≅ N.toFunctor。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isomorphism of monads gives a natural isomorphism of the underlying functors.
-/
def MonadIso.toNatIso {M N : Monad C} (h : M ≅ N) : (M : C ⥤ C) ≅ N :=
  (monadToFunctor C).mapIso h

/-- An isomorphism of comonads gives a natural isomorphism of the underlying functors.
-/
@[simps (rhsMd := .default)]
/-
**CategoryTheory.ComonadIso.toNatIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.C
omonadIso`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] → {M N : Cat
egoryTheory.Comonad C} → (M ≅ N) → (M.toFunctor ≅ N.toFunctor)
参数：M ≅ N；M.toFunctor ≅ N.toFunctor。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isomorphism of comonads gives a natural isomorphism of the underlying functor
s.
-/
def ComonadIso.toNatIso {M N : Comonad C} (h : M ≅ N) : (M : C ⥤ C) ≅ N :=
  (comonadToFunctor C).mapIso h

variable (C)

namespace Monad

/-- The identity monad. -/
@[simps!]
/-
**CategoryTheory.Monad.id** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Monad`。
形式化陈述：id : Monad C where toFunctor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity monad.
-/
def id : Monad C where
  toFunctor := 𝟭 C
  η := 𝟙 (𝟭 C)
  μ := 𝟙 (𝟭 C)
/-
**CategoryTheory.Monad.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Monad`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Monad C) :=
  ⟨Monad.id C⟩

end Monad

namespace Comonad

set_option backward.defeqAttrib.useBackward true in
/-- The identity comonad. -/
@[simps!]
/-
**CategoryTheory.Comonad.id** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Comonad`。
形式化陈述：id : Comonad C where toFunctor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity comonad.
-/
def id : Comonad C where
  toFunctor := 𝟭 _
  ε := 𝟙 (𝟭 C)
  δ := 𝟙 (𝟭 C)
/-
**CategoryTheory.Comonad.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Comonad`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Comonad C) :=
  ⟨Comonad.id C⟩

end Comonad

open Iso CategoryTheory.Functor

variable {C}

namespace Monad

set_option backward.defeqAttrib.useBackward true in
/-- Transport a monad structure on a functor along an isomorphism of functors. -/
/-
**CategoryTheory.Monad.transport** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Monad
`。
形式化陈述：transport {F : C ⥤ C} (T : Monad C) (i : (T : C ⥤ C) ≅ F) : Monad C where 
toFunctor
参数：T : Monad C；i : (T : C ⥤ C) ≅ F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transport a monad structure on a functor along an isomorphism of functors.
-/
def transport {F : C ⥤ C} (T : Monad C) (i : (T : C ⥤ C) ≅ F) : Monad C where
  toFunctor := F
  η := T.η ≫ i.hom
  μ := (i.inv ◫ i.inv) ≫ T.μ ≫ i.hom
  left_unit X := by
    simp only [Functor.id_obj, NatTrans.comp_app, comp_obj, NatTrans.hcomp_app, Category.assoc,
      hom_inv_id_app_assoc]
    slice_lhs 1 2 => rw [← T.η.naturality (i.inv.app X), ]
    simp
  right_unit X := by
    simp only [NatTrans.comp_app, Functor.map_comp, comp_obj, NatTrans.hcomp_app,
      Category.assoc, NatTrans.naturality_assoc]
    slice_lhs 2 4 =>
      simp only [← T.map_comp]
    simp
  assoc X := by
    simp only [comp_obj, NatTrans.comp_app, NatTrans.hcomp_app, Category.assoc, Functor.map_comp,
      NatTrans.naturality_assoc, hom_inv_id_app_assoc, NatIso.cancel_natIso_inv_left]
    slice_lhs 4 5 => rw [← T.map_comp]
    simp only [hom_inv_id_app, Functor.map_id, id_comp]
    slice_lhs 1 2 => rw [← T.map_comp]
    simp only [Functor.map_comp, Category.assoc]
    congr 1
    simp only [← Category.assoc, NatIso.cancel_natIso_hom_right]
    rw [← T.μ.naturality]
    simp [T.assoc X]

end Monad

namespace Comonad

/-- Transport a comonad structure on a functor along an isomorphism of functors. -/
/-
**CategoryTheory.Comonad.transport** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Com
onad`。
形式化陈述：transport {F : C ⥤ C} (T : Comonad C) (i : (T : C ⥤ C) ≅ F) : Comonad C wh
ere toFunctor
参数：T : Comonad C；i : (T : C ⥤ C) ≅ F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transport a comonad structure on a functor along an isomorphism of functors.
-/
def transport {F : C ⥤ C} (T : Comonad C) (i : (T : C ⥤ C) ≅ F) : Comonad C where
  toFunctor := F
  ε := i.inv ≫ T.ε
  δ := i.inv ≫ T.δ ≫ (i.hom ◫ i.hom)
  right_counit X := by
    simp only [comp_obj, NatTrans.comp_app, NatTrans.hcomp_app, Functor.map_comp, assoc]
    slice_lhs 4 5 => rw [← F.map_comp]
    simp only [hom_inv_id_app, Functor.map_id, id_comp, ← i.hom.naturality]
    slice_lhs 2 3 => rw [T.right_counit]
    simp
  coassoc X := by
    simp only [comp_obj, NatTrans.comp_app, NatTrans.hcomp_app, Functor.map_comp, assoc,
      NatTrans.naturality_assoc, Functor.comp_map, hom_inv_id_app_assoc,
      NatIso.cancel_natIso_inv_left]
    slice_lhs 3 4 => rw [← F.map_comp]
    simp only [hom_inv_id_app, Functor.map_id, id_comp, assoc]
    rw [← i.hom.naturality_assoc, ← T.coassoc_assoc]
    simp only [NatTrans.naturality_assoc]
    congr 3
    simp only [← Functor.map_comp, i.hom.naturality]

end Comonad

namespace Monad

/-
**CategoryTheory.Monad.map_unit_app** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Mo
nad`。
形式化陈述：map_unit_app (T : Monad C) (X : C) [IsIso T.μ] : T.map (T.η.app X) = T.η.a
pp (T.obj X)
参数：T : Monad C；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.IsSplitMono.mono`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [hf : CategoryTheory.IsSplitMono f], 
  CategoryTheory.Mono…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.NatIso.isIso_app_of_isIso`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Monad.right_unit`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] (self : CategoryTheory.Monad C) (X : C),   CategoryTheory.C
ategoryStruct.comp (s…
· 使用定理 `CategoryTheory.Monad.left_unit`：∀ {C : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} C] (self : CategoryTheory.Monad C) (X : C),   CategoryTheory.Ca
tegoryStruct.comp (s…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_unit_app (T : Monad C) (X : C) [IsIso T.μ] :
    T.map (T.η.app X) = T.η.app (T.obj X) := by
  simp [← cancel_mono (T.μ.app _)]
/-
**CategoryTheory.Monad.isSplitMono_iff_isIso_unit** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Monad`。
形式化陈述：isSplitMono_iff_isIso_unit (T : Monad C) (X : C) [IsIso T.μ] : IsSplitMono
 (T.η.app X) ↔ IsIso (T.η.app X)
参数：T : Monad C；X : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsSplitMono.id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [hf : CategoryTheory.IsSplitMono f],   
CategoryTheory.Cate…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用引理 `CategoryTheory.Monad.map_unit_app`：map_unit_app (T : Monad C) (X : C) [I
sIso T.μ] : T.map (T.η.app X) = T.η.app (T.obj X)
· 使用定理 `CategoryTheory.Monad.unit_naturality`：∀ (C : Type u₁) [inst : CategoryTh
eory.Category.{v₁, u₁} C] (T : CategoryTheory.Monad C) ⦃X Y : C⦄ (f : X ⟶ Y),   
CategoryTheory.CategoryStr…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
-/
lemma isSplitMono_iff_isIso_unit (T : Monad C) (X : C) [IsIso T.μ] :
    IsSplitMono (T.η.app X) ↔ IsIso (T.η.app X) := by
  refine ⟨fun _ ↦ ⟨retraction (T.η.app X), by simp, ?_⟩, fun _ ↦ inferInstance⟩
  rw [← map_id, ← show T.η.app X ≫ retraction (T.η.app X) = 𝟙 X from IsSplitMono.id _,
    map_comp, T.map_unit_app X, ← T.unit_naturality]

end Monad

namespace Comonad

/-
**CategoryTheory.Comonad.map_counit_app** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Comonad`。
形式化陈述：map_counit_app (T : Comonad C) (X : C) [IsIso T.δ] : T.map (T.ε.app X) = T
.ε.app (T.obj X)
参数：T : Comonad C；X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.IsSplitEpi.epi`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [hf : CategoryTheory.IsSplitEpi f],   C
ategoryTheory.Epi f
· 使用定理 `CategoryTheory.IsSplitEpi.of_iso`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],   Category
Theory.IsSplitEpi f
· 使用定理 `CategoryTheory.NatIso.isIso_app_of_isIso`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Comonad.right_counit`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] (self : CategoryTheory.Comonad C) (X : C),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Comonad.left_counit`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] (self : CategoryTheory.Comonad C) (X : C),   CategoryThe
ory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_counit_app (T : Comonad C) (X : C) [IsIso T.δ] :
    T.map (T.ε.app X) = T.ε.app (T.obj X) := by
  simp [← cancel_epi (T.δ.app _)]
/-
**CategoryTheory.Comonad.isSplitEpi_iff_isIso_counit** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Comonad`。
形式化陈述：isSplitEpi_iff_isIso_counit (T : Comonad C) (X : C) [IsIso T.δ] : IsSplitE
pi (T.ε.app X) ↔ IsIso (T.ε.app X)
参数：T : Comonad C；X : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.IsSplitEpi.id`：∀ {C : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [hf : CategoryTheory.IsSplitEpi f],   Ca
tegoryTheory.Categ…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用引理 `CategoryTheory.Comonad.map_counit_app`：map_counit_app (T : Comonad C) (X
 : C) [IsIso T.δ] : T.map (T.ε.app X) = T.ε.app (T.obj X)
· 使用定理 `CategoryTheory.Comonad.counit_naturality`：∀ (C : Type u₁) [inst : Catego
ryTheory.Category.{v₁, u₁} C] (T : CategoryTheory.Comonad C) ⦃X Y : C⦄ (f : X ⟶ 
Y),   CategoryTheory.CategoryS…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.IsSplitEpi.of_iso`：∀ {C : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],   Category
Theory.IsSplitEpi f
-/
lemma isSplitEpi_iff_isIso_counit (T : Comonad C) (X : C) [IsIso T.δ] :
    IsSplitEpi (T.ε.app X) ↔ IsIso (T.ε.app X) := by
  refine ⟨fun _ ↦ ⟨section_ (T.ε.app X), ?_, by simp⟩, fun _ ↦ inferInstance⟩
  rw [← map_id, ← show section_ (T.ε.app X) ≫ T.ε.app X = 𝟙 X from IsSplitEpi.id (T.ε.app X),
    map_comp, T.map_counit_app X, T.counit_naturality]

end Comonad

end CategoryTheory

