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

/--
Definition of `Monad` / `Monad` 的定义

English:
structure Monad
  parameters: extends C ⥤ C
  extends: C ⥤ C
  axioms and operations (5):
    - η : 𝟭 _ ⟶ toFunctor
    - μ : toFunctor ⋙ toFunctor ⟶ toFunctor
    - assoc : forall X, toFunctor.map (NatTrans.app μ X) ≫ μ.app _ = μ.app _ ≫ μ.app _  [default: by cat_disch]
    - left_unit : forall X : C, η.app (toFunctor.obj X) ≫ μ.app _ = 𝟙 _  [default: by cat_disch]
    - right_unit : forall X : C, toFunctor.map (η.app X) ≫ μ.app _ = 𝟙 _  [default: by cat_disch]

中文:
结构 单子
  参数: extends C ⥤ C
  继承: C ⥤ C
  公理与运算 (5 个):
    - η : 𝟭 _ ⟶ toFunctor
    - μ : toFunctor ⋙ toFunctor ⟶ toFunctor
    - assoc : 对任意 X, toFunctor.map (自然变换.app μ X) ≫ μ.app _ = μ.app _ ≫ μ.app _  [默认: by cat_disch]
    - left_unit : 对任意 X : C, η.app (toFunctor.obj X) ≫ μ.app _ = 𝟙 _  [默认: by cat_disch]
    - right_unit : 对任意 X : C, toFunctor.map (η.app X) ≫ μ.app _ = 𝟙 _  [默认: by cat_disch]

Depends on / 依赖: cat_disch, left_unit, right_unit, toFunctor, toFunctor.map, toFunctor.obj
-/
structure Monad extends C ⥤ C where
  /-- The unit for the monad. -/
  η : 𝟭 _ ⟶ toFunctor
  /-- The multiplication for the monad. -/
  μ : toFunctor ⋙ toFunctor ⟶ toFunctor
  assoc : forall X, toFunctor.map (NatTrans.app μ X) ≫ μ.app _ = μ.app _ ≫ μ.app _ := by cat_disch
  left_unit : forall X : C, η.app (toFunctor.obj X) ≫ μ.app _ = 𝟙 _ := by cat_disch
  right_unit : forall X : C, toFunctor.map (η.app X) ≫ μ.app _ = 𝟙 _ := by cat_disch

@[reassoc]
/--
lemma `Monad.unit_naturality` / 引理 `Monad.unit_naturality`

English:
lemma Monad.unit_naturality
  given: (T : Monad C) ⦃X Y
  statement: C⦄ (f : X ⟶ Y) :
  proof: T.η.naturality _

@[reassoc]

中文:
引理 单子.unit_naturality
  条件: (T : 单子 C) ⦃X Y
  结论: C⦄ (f : X ⟶ Y) :
  证明: T.η.naturality _

@[reassoc]

Depends on / 依赖: naturality
-/
lemma Monad.unit_naturality (T : Monad C) ⦃X Y : C⦄ (f : X ⟶ Y) :
    f ≫ T.η.app Y = T.η.app X ≫ T.map f :=
  T.η.naturality _

@[reassoc]
/--
lemma `Monad.mu_naturality` / 引理 `Monad.mu_naturality`

English:
lemma Monad.mu_naturality
  given: (T : Monad C) ⦃X Y
  statement: C⦄ (f : X ⟶ Y) :
  proof: T.μ.naturality _

中文:
引理 单子.mu_naturality
  条件: (T : 单子 C) ⦃X Y
  结论: C⦄ (f : X ⟶ Y) :
  证明: T.μ.naturality _

Depends on / 依赖: naturality
-/
lemma Monad.mu_naturality (T : Monad C) ⦃X Y : C⦄ (f : X ⟶ Y) :
    T.map (T.map f) ≫ T.μ.app Y = T.μ.app X ≫ T.map f :=
  T.μ.naturality _

/--
Definition of `Comonad` / `Comonad` 的定义

English:
structure Comonad
  parameters: extends C ⥤ C
  extends: C ⥤ C
  axioms and operations (5):
    - ε : toFunctor ⟶ 𝟭 _
    - δ : toFunctor ⟶ toFunctor ⋙ toFunctor
    - coassoc : forall X, NatTrans.app δ _ ≫ toFunctor.map (δ.app X) = δ.app _ ≫ δ.app _  [default: by cat_disch]
    - left_counit : forall X : C, δ.app X ≫ ε.app (toFunctor.obj X) = 𝟙 _  [default: by cat_disch]
    - right_counit : forall X : C, δ.app X ≫ toFunctor.map (ε.app X) = 𝟙 _  [default: by cat_disch]

中文:
结构 余单子
  参数: extends C ⥤ C
  继承: C ⥤ C
  公理与运算 (5 个):
    - ε : toFunctor ⟶ 𝟭 _
    - δ : toFunctor ⟶ toFunctor ⋙ toFunctor
    - coassoc : 对任意 X, 自然变换.app δ _ ≫ toFunctor.map (δ.app X) = δ.app _ ≫ δ.app _  [默认: by cat_disch]
    - left_counit : 对任意 X : C, δ.app X ≫ ε.app (toFunctor.obj X) = 𝟙 _  [默认: by cat_disch]
    - right_counit : 对任意 X : C, δ.app X ≫ toFunctor.map (ε.app X) = 𝟙 _  [默认: by cat_disch]

Depends on / 依赖: cat_disch, left_counit, right_counit, toFunctor, toFunctor.map, toFunctor.obj
-/
structure Comonad extends C ⥤ C where
  /-- The counit for the comonad. -/
  ε : toFunctor ⟶ 𝟭 _
  /-- The comultiplication for the comonad. -/
  δ : toFunctor ⟶ toFunctor ⋙ toFunctor
  coassoc : forall X, NatTrans.app δ _ ≫ toFunctor.map (δ.app X) = δ.app _ ≫ δ.app _ := by
    cat_disch
  left_counit : forall X : C, δ.app X ≫ ε.app (toFunctor.obj X) = 𝟙 _ := by cat_disch
  right_counit : forall X : C, δ.app X ≫ toFunctor.map (ε.app X) = 𝟙 _ := by cat_disch

@[reassoc]
/--
lemma `Comonad.counit_naturality` / 引理 `Comonad.counit_naturality`

English:
lemma Comonad.counit_naturality
  given: (T : Comonad C) ⦃X Y
  statement: C⦄ (f : X ⟶ Y) :
  proof: T.ε.naturality _

@[reassoc]

中文:
引理 余单子.counit_naturality
  条件: (T : 余单子 C) ⦃X Y
  结论: C⦄ (f : X ⟶ Y) :
  证明: T.ε.naturality _

@[reassoc]

Depends on / 依赖: naturality
-/
lemma Comonad.counit_naturality (T : Comonad C) ⦃X Y : C⦄ (f : X ⟶ Y) :
    T.map f ≫ T.ε.app Y = T.ε.app X ≫ f :=
  T.ε.naturality _

@[reassoc]
/--
lemma `Comonad.delta_naturality` / 引理 `Comonad.delta_naturality`

English:
lemma Comonad.delta_naturality
  given: (T : Comonad C) ⦃X Y
  statement: C⦄ (f : X ⟶ Y) :
  proof: T.δ.naturality _

中文:
引理 余单子.delta_naturality
  条件: (T : 余单子 C) ⦃X Y
  结论: C⦄ (f : X ⟶ Y) :
  证明: T.δ.naturality _

Depends on / 依赖: naturality
-/
lemma Comonad.delta_naturality (T : Comonad C) ⦃X Y : C⦄ (f : X ⟶ Y) :
    T.map f ≫ T.δ.app Y = T.δ.app X ≫ T.map (T.map f) :=
  T.δ.naturality _

variable {C}
variable (T : Monad C) (G : Comonad C)

/--
Instance `coeMonad` / 实例 `coeMonad`

English:
instance coeMonad
  signature: : Coe (Monad C) (C ⥤ C)
  body: ⟨fun T => T.toFunctor⟩

中文:
实例 coeMonad
  签名: : Coe (单子 C) (C ⥤ C)
  定义体: ⟨fun T => T.toFunctor⟩

Depends on / 依赖: T.toFunctor, toFunctor
-/
instance coeMonad : Coe (Monad C) (C ⥤ C) :=
  ⟨fun T => T.toFunctor⟩

/--
Instance `coeComonad` / 实例 `coeComonad`

English:
instance coeComonad
  signature: : Coe (Comonad C) (C ⥤ C)
  body: ⟨fun G => G.toFunctor⟩

initialize_simps_projections CategoryTheory.Monad (toFunctor -> coe)

initialize_simps_projections CategoryTheory.Comonad (toFunctor -> coe)

中文:
实例 coeComonad
  签名: : Coe (余单子 C) (C ⥤ C)
  定义体: ⟨fun G => G.toFunctor⟩

initialize_simps_projections CategoryTheory.Monad (toFunctor -> coe)

initialize_simps_projections CategoryTheory.Comonad (toFunctor -> coe)

Depends on / 依赖: G.toFunctor, toFunctor
-/
instance coeComonad : Coe (Comonad C) (C ⥤ C) :=
  ⟨fun G => G.toFunctor⟩

initialize_simps_projections CategoryTheory.Monad (toFunctor -> coe)

initialize_simps_projections CategoryTheory.Comonad (toFunctor -> coe)

-- TODO: investigate whether `Monad.assoc` can be a `simp` lemma?
attribute [reassoc (attr := simp)] Monad.left_unit Monad.right_unit
attribute [reassoc (attr := simp)] Comonad.coassoc Comonad.left_counit Comonad.right_counit

/-- A morphism of monads is a natural transformation compatible with η and μ. -/
@[ext]
/--
Definition of `MonadHom` / `MonadHom` 的定义

English:
structure MonadHom
  parameters: (T₁ T₂ : Monad C)
  extends: NatTrans (T₁ : C ⥤ C) T₂
  axioms and operations (2):
    - app_η : forall X, T₁.η.app X ≫ app X = T₂.η.app X  [default: by cat_disch]
    - app_μ : forall X, T₁.μ.app X ≫ app X = (T₁.map (app X) ≫ app _) ≫ T₂.μ.app X  [default: by cat_disch]

中文:
结构 单子态射
  参数: (T₁ T₂ : 单子 C)
  继承: 自然变换 (T₁ : C ⥤ C) T₂
  公理与运算 (2 个):
    - app_η : 对任意 X, T₁.η.app X ≫ app X = T₂.η.app X  [默认: by cat_disch]
    - app_μ : 对任意 X, T₁.μ.app X ≫ app X = (T₁.map (app X) ≫ app _) ≫ T₂.μ.app X  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure MonadHom (T₁ T₂ : Monad C) extends NatTrans (T₁ : C ⥤ C) T₂ where
  app_η : forall X, T₁.η.app X ≫ app X = T₂.η.app X := by cat_disch
  app_μ : forall X, T₁.μ.app X ≫ app X = (T₁.map (app X) ≫ app _) ≫ T₂.μ.app X := by
    cat_disch

initialize_simps_projections MonadHom (+toNatTrans, -app)

/-- A morphism of comonads is a natural transformation compatible with ε and δ. -/
@[ext]
/--
Definition of `ComonadHom` / `ComonadHom` 的定义

English:
structure ComonadHom
  parameters: (M N : Comonad C)
  extends: NatTrans (M : C ⥤ C) N
  axioms and operations (2):
    - app_ε : forall X, app X ≫ N.ε.app X = M.ε.app X  [default: by cat_disch]
    - app_δ : forall X, app X ≫ N.δ.app X = M.δ.app X ≫ app _ ≫ N.map (app X)  [default: by cat_disch]

中文:
结构 余单子态射
  参数: (M N : 余单子 C)
  继承: 自然变换 (M : C ⥤ C) N
  公理与运算 (2 个):
    - app_ε : 对任意 X, app X ≫ N.ε.app X = M.ε.app X  [默认: by cat_disch]
    - app_δ : 对任意 X, app X ≫ N.δ.app X = M.δ.app X ≫ app _ ≫ N.map (app X)  [默认: by cat_disch]

Depends on / 依赖: N.map, cat_disch
-/
structure ComonadHom (M N : Comonad C) extends NatTrans (M : C ⥤ C) N where
  app_ε : forall X, app X ≫ N.ε.app X = M.ε.app X := by cat_disch
  app_δ : forall X, app X ≫ N.δ.app X = M.δ.app X ≫ app _ ≫ N.map (app X) := by cat_disch

initialize_simps_projections ComonadHom (+toNatTrans, -app)

attribute [reassoc (attr := simp)] MonadHom.app_η MonadHom.app_μ
attribute [reassoc (attr := simp)] ComonadHom.app_ε ComonadHom.app_δ

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Quiver (Monad C)
  body: MonadHom

中文:
实例 :
  签名: 箭图 (单子 C)
  定义体: MonadHom

Depends on / 依赖: MonadHom
-/
instance : Quiver (Monad C) where
  Hom := MonadHom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Quiver (Comonad C)
  body: ComonadHom

@[ext]

中文:
实例 :
  签名: 箭图 (余单子 C)
  定义体: ComonadHom

@[ext]

Depends on / 依赖: ComonadHom
-/
instance : Quiver (Comonad C) where
  Hom := ComonadHom

@[ext]
/--
lemma `MonadHom.ext'` / 引理 `MonadHom.ext'`

English:
lemma MonadHom.ext'
  given: {T₁ T₂ : Monad C} (f g : T₁ ⟶ T₂) (h : f.app = g.app)
  statement: f = g
  proof: MonadHom.ext h

@[ext]

中文:
引理 单子态射.ext'
  条件: {T₁ T₂ : 单子 C} (f g : T₁ ⟶ T₂) (h : f.app = g.app)
  结论: f = g
  证明: MonadHom.ext h

@[ext]

Depends on / 依赖: MonadHom, MonadHom.ext
-/
lemma MonadHom.ext' {T₁ T₂ : Monad C} (f g : T₁ ⟶ T₂) (h : f.app = g.app) : f = g :=
  MonadHom.ext h

@[ext]
/--
lemma `ComonadHom.ext'` / 引理 `ComonadHom.ext'`

English:
lemma ComonadHom.ext'
  given: {T₁ T₂ : Comonad C} (f g : T₁ ⟶ T₂) (h : f.app = g.app)
  statement: f = g
  proof: ComonadHom.ext h

中文:
引理 余单子态射.ext'
  条件: {T₁ T₂ : 余单子 C} (f g : T₁ ⟶ T₂) (h : f.app = g.app)
  结论: f = g
  证明: ComonadHom.ext h

Depends on / 依赖: ComonadHom, ComonadHom.ext
-/
lemma ComonadHom.ext' {T₁ T₂ : Comonad C} (f g : T₁ ⟶ T₂) (h : f.app = g.app) : f = g :=
  ComonadHom.ext h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (Monad C)
  body: { toNatTrans := 𝟙 (M : C ⥤ C) }
  comp f g :=
    { toNatTrans :=
        { app := fun X => f.app X ≫ g.app X
          naturality := fun X Y h => by rw [assoc, f.1.naturality_assoc, g.1.naturality] } }

中文:
实例 :
  签名: 范畴 (单子 C)
  定义体: { toNatTrans := 𝟙 (M : C ⥤ C) }
  comp f g :=
    { toNatTrans :=
        { app := fun X => f.app X ≫ g.app X
          naturality := fun X Y h => by rw [assoc, f.1.naturality_assoc, g.1.naturality] } }

Depends on / 依赖: toNatTrans
-/
instance : Category (Monad C) where
  id M := { toNatTrans := 𝟙 (M : C ⥤ C) }
  comp f g :=
    { toNatTrans :=
        { app := fun X => f.app X ≫ g.app X
          naturality := fun X Y h => by rw [assoc, f.1.naturality_assoc, g.1.naturality] } }

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (Comonad C)
  body: { toNatTrans := 𝟙 (M : C ⥤ C) }
  comp f g :=
    { toNatTrans :=
        { app := fun X => f.app X ≫ g.app X
          naturality := fun X Y h => by rw [assoc, f.1.naturality_assoc, g.1.naturality] } }

中文:
实例 :
  签名: 范畴 (余单子 C)
  定义体: { toNatTrans := 𝟙 (M : C ⥤ C) }
  comp f g :=
    { toNatTrans :=
        { app := fun X => f.app X ≫ g.app X
          naturality := fun X Y h => by rw [assoc, f.1.naturality_assoc, g.1.naturality] } }

Depends on / 依赖: toNatTrans
-/
instance : Category (Comonad C) where
  id M := { toNatTrans := 𝟙 (M : C ⥤ C) }
  comp f g :=
    { toNatTrans :=
        { app := fun X => f.app X ≫ g.app X
          naturality := fun X Y h => by rw [assoc, f.1.naturality_assoc, g.1.naturality] } }

instance {T : Monad C} : Inhabited (MonadHom T T) :=
  ⟨𝟙 T⟩

@[simp]
/--
theorem `MonadHom.id_toNatTrans` / 定理 `MonadHom.id_toNatTrans`

English:
theorem MonadHom.id_toNatTrans
  given: (T : Monad C)
  statement: (𝟙 T : T ⟶ T).toNatTrans = 𝟙 (T : C ⥤ C)
  proof: rfl

@[simp]

中文:
定理 单子态射.id_to自然数Trans
  条件: (T : 单子 C)
  结论: (𝟙 T : T ⟶ T).to自然数Trans = 𝟙 (T : C ⥤ C)
  证明: rfl

@[simp]
-/
theorem MonadHom.id_toNatTrans (T : Monad C) : (𝟙 T : T ⟶ T).toNatTrans = 𝟙 (T : C ⥤ C) :=
  rfl

@[simp]
/--
theorem `MonadHom.comp_toNatTrans` / 定理 `MonadHom.comp_toNatTrans`

English:
theorem MonadHom.comp_toNatTrans
  given: {T₁ T₂ T₃ : Monad C} (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃)
  proof: rfl

中文:
定理 单子态射.comp_to自然数Trans
  条件: {T₁ T₂ T₃ : 单子 C} (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃)
  证明: rfl
-/
theorem MonadHom.comp_toNatTrans {T₁ T₂ T₃ : Monad C} (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃) :
    (f ≫ g).toNatTrans = ((f.toNatTrans : _ ⟶ (T₂ : C ⥤ C)) ≫ g.toNatTrans : (T₁ : C ⥤ C) ⟶ T₃) :=
  rfl

instance {G : Comonad C} : Inhabited (ComonadHom G G) :=
  ⟨𝟙 G⟩

@[simp]
/--
theorem `ComonadHom.id_toNatTrans` / 定理 `ComonadHom.id_toNatTrans`

English:
theorem ComonadHom.id_toNatTrans
  given: (T : Comonad C)
  statement: (𝟙 T : T ⟶ T).toNatTrans = 𝟙 (T : C ⥤ C)
  proof: rfl

@[simp]

中文:
定理 余单子态射.id_to自然数Trans
  条件: (T : 余单子 C)
  结论: (𝟙 T : T ⟶ T).to自然数Trans = 𝟙 (T : C ⥤ C)
  证明: rfl

@[simp]
-/
theorem ComonadHom.id_toNatTrans (T : Comonad C) : (𝟙 T : T ⟶ T).toNatTrans = 𝟙 (T : C ⥤ C) :=
  rfl

@[simp]
/--
theorem `comp_toNatTrans` / 定理 `comp_toNatTrans`

English:
theorem comp_toNatTrans
  given: {T₁ T₂ T₃ : Comonad C} (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃)
  proof: rfl

中文:
定理 comp_to自然数Trans
  条件: {T₁ T₂ T₃ : 余单子 C} (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃)
  证明: rfl
-/
theorem comp_toNatTrans {T₁ T₂ T₃ : Comonad C} (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃) :
    (f ≫ g).toNatTrans = ((f.toNatTrans : _ ⟶ (T₂ : C ⥤ C)) ≫ g.toNatTrans : (T₁ : C ⥤ C) ⟶ T₃) :=
  rfl

/-- Construct a monad isomorphism from a natural isomorphism of functors where the forward
direction is a monad morphism. -/
@[simps]
/--
Definition of `MonadIso.mk` / `MonadIso.mk` 的定义

English:
definition MonadIso.mk
  signature: {M N : Monad C} (f : (M : C ⥤ C) ≅ N)
  body: { toNatTrans := f.hom
      app_η := f_η
      app_μ := f_μ }
  inv :=
    { toNatTrans := f.inv
      app_η := fun X => by simp [← f_η]
      app_μ := fun X => by
        rw [← NatIso.cancel_natIso_hom_right f]
        simp only [NatTrans.naturality, Iso.inv_hom_id_app, assoc, comp_id, f_μ,
       

中文:
定义 MonadIso.mk
  签名: {M N : 单子 C} (f : (M : C ⥤ C) ≅ N)
  定义体: { toNatTrans := f.hom
      app_η := f_η
      app_μ := f_μ }
  inv :=
    { toNatTrans := f.inv
      app_η := fun X => by simp [← f_η]
      app_μ := fun X => by
        rw [← NatIso.cancel_natIso_hom_right f]
        simp only [NatTrans.naturality, Iso.inv_hom_id_app, assoc, comp_id, f_μ,
       

Depends on / 依赖: Functor, Functor.map_comp_assoc, Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc, M.map, N.obj, NatIso, NatIso.cancel_natIso_hom_right, NatTrans, NatTrans.naturality, NatTrans.naturality_assoc, cancel_natIso_hom_right, cat_disch, comp_id, f.hom, f.hom.app, f.inv, inv_hom_id_app, inv_hom_id_app_assoc, map_comp_assoc
-/
def MonadIso.mk {M N : Monad C} (f : (M : C ⥤ C) ≅ N)
    (f_η : forall (X : C), M.η.app X ≫ f.hom.app X = N.η.app X := by cat_disch)
    (f_μ : forall (X : C), M.μ.app X ≫ f.hom.app X =
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
/--
Definition of `ComonadIso.mk` / `ComonadIso.mk` 的定义

English:
definition ComonadIso.mk
  signature: {M N : Comonad C} (f : (M : C ⥤ C) ≅ N)
  body: { toNatTrans := f.hom
      app_ε := f_ε
      app_δ := f_δ }
  inv :=
    { toNatTrans := f.inv
      app_ε := fun X => by simp [← f_ε]
      app_δ := fun X => by
        rw [← NatIso.cancel_natIso_hom_left f]
        simp only [reassoc_of% (f_δ X), Iso.hom_inv_id_app_assoc, NatTrans.naturality_ass

中文:
定义 ComonadIso.mk
  签名: {M N : 余单子 C} (f : (M : C ⥤ C) ≅ N)
  定义体: { toNatTrans := f.hom
      app_ε := f_ε
      app_δ := f_δ }
  inv :=
    { toNatTrans := f.inv
      app_ε := fun X => by simp [← f_ε]
      app_δ := fun X => by
        rw [← NatIso.cancel_natIso_hom_left f]
        simp only [reassoc_of% (f_δ X), Iso.hom_inv_id_app_assoc, NatTrans.naturality_ass

Depends on / 依赖: Functor, Functor.map_comp, Functor.map_id, Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc, M.obj, N.map, NatIso, NatIso.cancel_natIso_hom_left, NatTrans, NatTrans.naturality_assoc, cancel_natIso_hom_left, cat_disch, comp_id, f.hom, f.hom.app, f.inv, hom_inv_id_app, hom_inv_id_app_assoc, map_comp
-/
def ComonadIso.mk {M N : Comonad C} (f : (M : C ⥤ C) ≅ N)
    (f_ε : forall (X : C), f.hom.app X ≫ N.ε.app X = M.ε.app X := by cat_disch)
    (f_δ : forall (X : C), f.hom.app X ≫ N.δ.app X =
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
        rw [← Functor.map_comp]; rw [Iso.hom_inv_id_app]; rw [Functor.map_id]
        apply (comp_id _).symm }

variable (C)

/-- The forgetful functor from the category of monads to the category of endofunctors.
-/
@[simps!]
/--
Definition of `monadToFunctor` / `monadToFunctor` 的定义

English:
definition monadToFunctor
  signature: : Monad C ⥤ C ⥤ C where
  body: T
  map f := f.toNatTrans

中文:
定义 monadToFunctor
  签名: : 单子 C ⥤ C ⥤ C where
  定义体: T
  map f := f.toNatTrans
-/
def monadToFunctor : Monad C ⥤ C ⥤ C where
  obj T := T
  map f := f.toNatTrans

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (monadToFunctor C).Faithful

中文:
实例 :
  签名: (monadToFunctor C).忠实
-/
instance : (monadToFunctor C).Faithful where

/--
theorem `monadToFunctor_mapIso_monad_iso_mk` / 定理 `monadToFunctor_mapIso_monad_iso_mk`

English:
theorem monadToFunctor_mapIso_monad_iso_mk
  given: {M N : Monad C} (f : (M : C ⥤ C) ≅ N) (f_η f_μ)
  proof: by
  ext
  rfl

中文:
定理 monadToFunctor_mapIso_monad_iso_mk
  条件: {M N : 单子 C} (f : (M : C ⥤ C) ≅ N) (f_η f_μ)
  证明: by
  ext
  rfl
-/
theorem monadToFunctor_mapIso_monad_iso_mk {M N : Monad C} (f : (M : C ⥤ C) ≅ N) (f_η f_μ) :
    (monadToFunctor _).mapIso (MonadIso.mk f f_η f_μ) = f := by
  ext
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (monadToFunctor C).ReflectsIsomorphisms
  body: (MonadIso.mk (asIso ((monadToFunctor C).map f)) f.app_η f.app_μ).isIso_hom

中文:
实例 :
  签名: (monadToFunctor C).反映同构
  定义体: (MonadIso.mk (asIso ((monadToFunctor C).map f)) f.app_η f.app_μ).isIso_hom

Depends on / 依赖: MonadIso, MonadIso.mk, f.app_, isIso_hom, monadToFunctor
-/
instance : (monadToFunctor C).ReflectsIsomorphisms where
  reflects f _ := (MonadIso.mk (asIso ((monadToFunctor C).map f)) f.app_η f.app_μ).isIso_hom

/-- The forgetful functor from the category of comonads to the category of endofunctors.
-/
@[simps!]
/--
Definition of `comonadToFunctor` / `comonadToFunctor` 的定义

English:
definition comonadToFunctor
  signature: : Comonad C ⥤ C ⥤ C where
  body: G
  map f := f.toNatTrans

中文:
定义 comonadToFunctor
  签名: : 余单子 C ⥤ C ⥤ C where
  定义体: G
  map f := f.toNatTrans
-/
def comonadToFunctor : Comonad C ⥤ C ⥤ C where
  obj G := G
  map f := f.toNatTrans

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (comonadToFunctor C).Faithful

中文:
实例 :
  签名: (comonadToFunctor C).忠实
-/
instance : (comonadToFunctor C).Faithful where

/--
theorem `comonadToFunctor_mapIso_comonad_iso_mk` / 定理 `comonadToFunctor_mapIso_comonad_iso_mk`

English:
theorem comonadToFunctor_mapIso_comonad_iso_mk
  given: {M N : Comonad C} (f : (M : C ⥤ C) ≅ N) (f_ε f_δ)
  proof: by
  ext
  rfl

中文:
定理 comonadToFunctor_mapIso_comonad_iso_mk
  条件: {M N : 余单子 C} (f : (M : C ⥤ C) ≅ N) (f_ε f_δ)
  证明: by
  ext
  rfl
-/
theorem comonadToFunctor_mapIso_comonad_iso_mk {M N : Comonad C} (f : (M : C ⥤ C) ≅ N) (f_ε f_δ) :
    (comonadToFunctor _).mapIso (ComonadIso.mk f f_ε f_δ) = f := by
  ext
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (comonadToFunctor C).ReflectsIsomorphisms
  body: (ComonadIso.mk (asIso ((comonadToFunctor C).map f)) f.app_ε f.app_δ).isIso_hom

中文:
实例 :
  签名: (comonadToFunctor C).反映同构
  定义体: (ComonadIso.mk (asIso ((comonadToFunctor C).map f)) f.app_ε f.app_δ).isIso_hom

Depends on / 依赖: ComonadIso, ComonadIso.mk, comonadToFunctor, f.app_, isIso_hom
-/
instance : (comonadToFunctor C).ReflectsIsomorphisms where
  reflects f _ := (ComonadIso.mk (asIso ((comonadToFunctor C).map f)) f.app_ε f.app_δ).isIso_hom

variable {C}

/-- An isomorphism of monads gives a natural isomorphism of the underlying functors.
-/
@[simps (rhsMd := .default)]
/--
Definition of `MonadIso.toNatIso` / `MonadIso.toNatIso` 的定义

English:
definition MonadIso.toNatIso
  signature: {M N : Monad C} (h : M ≅ N)
  body: (monadToFunctor C).mapIso h

中文:
定义 MonadIso.to自然数Iso
  签名: {M N : 单子 C} (h : M ≅ N)
  定义体: (monadToFunctor C).mapIso h

Depends on / 依赖: mapIso, monadToFunctor
-/
def MonadIso.toNatIso {M N : Monad C} (h : M ≅ N) : (M : C ⥤ C) ≅ N :=
  (monadToFunctor C).mapIso h

/-- An isomorphism of comonads gives a natural isomorphism of the underlying functors.
-/
@[simps (rhsMd := .default)]
/--
Definition of `ComonadIso.toNatIso` / `ComonadIso.toNatIso` 的定义

English:
definition ComonadIso.toNatIso
  signature: {M N : Comonad C} (h : M ≅ N)
  body: (comonadToFunctor C).mapIso h

中文:
定义 ComonadIso.to自然数Iso
  签名: {M N : 余单子 C} (h : M ≅ N)
  定义体: (comonadToFunctor C).mapIso h

Depends on / 依赖: comonadToFunctor, mapIso
-/
def ComonadIso.toNatIso {M N : Comonad C} (h : M ≅ N) : (M : C ⥤ C) ≅ N :=
  (comonadToFunctor C).mapIso h

variable (C)

namespace Monad

/-- The identity monad. -/
@[simps!]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : Monad C where
  body: 𝟭 C
  η := 𝟙 (𝟭 C)
  μ := 𝟙 (𝟭 C)

中文:
定义 id
  签名: : 单子 C where
  定义体: 𝟭 C
  η := 𝟙 (𝟭 C)
  μ := 𝟙 (𝟭 C)
-/
def id : Monad C where
  toFunctor := 𝟭 C
  η := 𝟙 (𝟭 C)
  μ := 𝟙 (𝟭 C)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Monad C)
  body: ⟨Monad.id C⟩

中文:
实例 :
  签名: 可居 (单子 C)
  定义体: ⟨Monad.id C⟩

Depends on / 依赖: Monad.id
-/
instance : Inhabited (Monad C) :=
  ⟨Monad.id C⟩

end Monad

namespace Comonad

set_option backward.defeqAttrib.useBackward true in
/-- The identity comonad. -/
@[simps!]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : Comonad C where
  body: 𝟭 _
  ε := 𝟙 (𝟭 C)
  δ := 𝟙 (𝟭 C)

中文:
定义 id
  签名: : 余单子 C where
  定义体: 𝟭 _
  ε := 𝟙 (𝟭 C)
  δ := 𝟙 (𝟭 C)
-/
def id : Comonad C where
  toFunctor := 𝟭 _
  ε := 𝟙 (𝟭 C)
  δ := 𝟙 (𝟭 C)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Comonad C)
  body: ⟨Comonad.id C⟩

中文:
实例 :
  签名: 可居 (余单子 C)
  定义体: ⟨Comonad.id C⟩

Depends on / 依赖: Comonad, Comonad.id
-/
instance : Inhabited (Comonad C) :=
  ⟨Comonad.id C⟩

end Comonad

open Iso CategoryTheory.Functor

variable {C}

namespace Monad

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `transport` / `transport` 的定义

English:
definition transport
  signature: {F : C ⥤ C} (T : Monad C) (i : (T : C ⥤ C) ≅ F)
  body: F
  η := T.η ≫ i.hom
  μ := (i.inv ◫ i.inv) ≫ T.μ ≫ i.hom
  left_unit X := by
    simp only [Functor.id_obj, NatTrans.comp_app, comp_obj, NatTrans.hcomp_app, Category.assoc,
      hom_inv_id_app_assoc]
    slice_lhs 1 2 => rw [← T.η.naturality (i.inv.app X), ]
    simp
  right_unit X := by
    simp 

中文:
定义 transport
  签名: {F : C ⥤ C} (T : 单子 C) (i : (T : C ⥤ C) ≅ F)
  定义体: F
  η := T.η ≫ i.hom
  μ := (i.inv ◫ i.inv) ≫ T.μ ≫ i.hom
  left_unit X := by
    simp only [Functor.id_obj, NatTrans.comp_app, comp_obj, NatTrans.hcomp_app, Category.assoc,
      hom_inv_id_app_assoc]
    slice_lhs 1 2 => rw [← T.η.naturality (i.inv.app X), ]
    simp
  right_unit X := by
    simp 
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

/--
Definition of `transport` / `transport` 的定义

English:
definition transport
  signature: {F : C ⥤ C} (T : Comonad C) (i : (T : C ⥤ C) ≅ F)
  body: F
  ε := i.inv ≫ T.ε
  δ := i.inv ≫ T.δ ≫ (i.hom ◫ i.hom)
  right_counit X := by
    simp only [comp_obj, NatTrans.comp_app, NatTrans.hcomp_app, Functor.map_comp, assoc]
    slice_lhs 4 5 => rw [← F.map_comp]
    simp only [hom_inv_id_app, Functor.map_id, id_comp, ← i.hom.naturality]
    slice_lhs 2

中文:
定义 transport
  签名: {F : C ⥤ C} (T : 余单子 C) (i : (T : C ⥤ C) ≅ F)
  定义体: F
  ε := i.inv ≫ T.ε
  δ := i.inv ≫ T.δ ≫ (i.hom ◫ i.hom)
  right_counit X := by
    simp only [comp_obj, NatTrans.comp_app, NatTrans.hcomp_app, Functor.map_comp, assoc]
    slice_lhs 4 5 => rw [← F.map_comp]
    simp only [hom_inv_id_app, Functor.map_id, id_comp, ← i.hom.naturality]
    slice_lhs 2
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
    rw [← i.hom.naturality_assoc]; rw [← T.coassoc_assoc]
    simp only [NatTrans.naturality_assoc]
    congr 3
    simp only [← Functor.map_comp, i.hom.naturality]

end Comonad

namespace Monad

/--
lemma `map_unit_app` / 引理 `map_unit_app`

English:
lemma map_unit_app
  given: (T : Monad C) (X : C) [IsIso T.μ]
  proof: by
  simp [← cancel_mono (T.μ.app _)]

中文:
引理 map_unit_app
  条件: (T : 单子 C) (X : C) [是同构 T.μ]
  证明: by
  simp [← cancel_mono (T.μ.app _)]

Depends on / 依赖: cancel_mono
-/
lemma map_unit_app (T : Monad C) (X : C) [IsIso T.μ] :
    T.map (T.η.app X) = T.η.app (T.obj X) := by
  simp [← cancel_mono (T.μ.app _)]

/--
lemma `isSplitMono_iff_isIso_unit` / 引理 `isSplitMono_iff_isIso_unit`

English:
lemma isSplitMono_iff_isIso_unit
  given: (T : Monad C) (X : C) [IsIso T.μ]
  proof: by
  refine ⟨fun _ => ⟨retraction (T.η.app X), by simp, ?_⟩, fun _ => inferInstance⟩
  rw [← map_id]; rw [← show T.η.app X ≫ retraction (T.η.app X) = 𝟙 X from IsSplitMono.id _]; rw [map_comp]; rw [T.map_unit_app X]; rw [← T.unit_naturality]

中文:
引理 isSplitMono_iff_isIso_unit
  条件: (T : 单子 C) (X : C) [是同构 T.μ]
  证明: by
  refine ⟨fun _ => ⟨retraction (T.η.app X), by simp, ?_⟩, fun _ => inferInstance⟩
  rw [← map_id]; rw [← show T.η.app X ≫ retraction (T.η.app X) = 𝟙 X from IsSplitMono.id _]; rw [map_comp]; rw [T.map_unit_app X]; rw [← T.unit_naturality]

Depends on / 依赖: IsSplitMono, IsSplitMono.id, T.map_unit_app, T.unit_naturality, map_comp, map_id, map_unit_app, retraction, unit_naturality
-/
lemma isSplitMono_iff_isIso_unit (T : Monad C) (X : C) [IsIso T.μ] :
    IsSplitMono (T.η.app X) ↔ IsIso (T.η.app X) := by
  refine ⟨fun _ => ⟨retraction (T.η.app X), by simp, ?_⟩, fun _ => inferInstance⟩
  rw [← map_id]; rw [← show T.η.app X ≫ retraction (T.η.app X) = 𝟙 X from IsSplitMono.id _]; rw [map_comp]; rw [T.map_unit_app X]; rw [← T.unit_naturality]

end Monad

namespace Comonad

/--
lemma `map_counit_app` / 引理 `map_counit_app`

English:
lemma map_counit_app
  given: (T : Comonad C) (X : C) [IsIso T.δ]
  proof: by
  simp [← cancel_epi (T.δ.app _)]

中文:
引理 map_counit_app
  条件: (T : 余单子 C) (X : C) [是同构 T.δ]
  证明: by
  simp [← cancel_epi (T.δ.app _)]

Depends on / 依赖: cancel_epi
-/
lemma map_counit_app (T : Comonad C) (X : C) [IsIso T.δ] :
    T.map (T.ε.app X) = T.ε.app (T.obj X) := by
  simp [← cancel_epi (T.δ.app _)]

/--
lemma `isSplitEpi_iff_isIso_counit` / 引理 `isSplitEpi_iff_isIso_counit`

English:
lemma isSplitEpi_iff_isIso_counit
  given: (T : Comonad C) (X : C) [IsIso T.δ]
  proof: by
  refine ⟨fun _ => ⟨section_ (T.ε.app X), ?_, by simp⟩, fun _ => inferInstance⟩
  rw [← map_id]; rw [← show section_ (T.ε.app X) ≫ T.ε.app X = 𝟙 X from IsSplitEpi.id (T.ε.app X)]; rw [map_comp]; rw [T.map_counit_app X]; rw [T.counit_naturality]

中文:
引理 isSplitEpi_iff_isIso_counit
  条件: (T : 余单子 C) (X : C) [是同构 T.δ]
  证明: by
  refine ⟨fun _ => ⟨section_ (T.ε.app X), ?_, by simp⟩, fun _ => inferInstance⟩
  rw [← map_id]; rw [← show section_ (T.ε.app X) ≫ T.ε.app X = 𝟙 X from IsSplitEpi.id (T.ε.app X)]; rw [map_comp]; rw [T.map_counit_app X]; rw [T.counit_naturality]

Depends on / 依赖: IsSplitEpi, IsSplitEpi.id, T.counit_naturality, T.map_counit_app, counit_naturality, map_comp, map_counit_app, map_id, section_
-/
lemma isSplitEpi_iff_isIso_counit (T : Comonad C) (X : C) [IsIso T.δ] :
    IsSplitEpi (T.ε.app X) ↔ IsIso (T.ε.app X) := by
  refine ⟨fun _ => ⟨section_ (T.ε.app X), ?_, by simp⟩, fun _ => inferInstance⟩
  rw [← map_id]; rw [← show section_ (T.ε.app X) ≫ T.ε.app X = 𝟙 X from IsSplitEpi.id (T.ε.app X)]; rw [map_comp]; rw [T.map_counit_app X]; rw [T.counit_naturality]

end Comonad

end CategoryTheory
