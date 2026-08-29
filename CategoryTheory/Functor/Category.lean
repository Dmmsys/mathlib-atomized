/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baumann, Stephen Morgan, Kim Morrison, Floris van Doorn
-/
module

public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.Iso

/-!
# The category of functors and natural transformations between two fixed categories.

We provide the category instance on `C ⥤ D`, with morphisms the natural transformations.

At the end of the file, we provide the left and right unitors, and the associator,
for functor composition.
(In fact functor composition is definitionally associative, but very often relying on this causes
extremely slow elaboration, so it is better to insert it explicitly.)

## Universes

If `C` and `D` are both small categories at the same universe level,
this is another small category at that level.
However if `C` and `D` are both large categories at the same universe level,
this is a small category at the next higher level.
-/

@[expose] public section

set_option mathlib.tactic.category.grind true

namespace CategoryTheory

-- declare the `v`'s first; see note [category theory universes].
universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

open NatTrans Category CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E] {E' : Type u₄} [Category.{v₄} E']
variable {F G H I : C ⥤ D}

attribute [local grind =] NatTrans.id_app' in
/--
Instance `Functor.category` / 实例 `Functor.category`

English:
instance Functor.category
  signature: : Category.{max u₁ v₂} (C ⥤ D) where
  body: NatTrans F G
  id F := NatTrans.id F
  comp α β := vcomp α β

中文:
实例 函子.category
  签名: : 范畴.{最大值 u₁ v₂} (C ⥤ D) where
  定义体: NatTrans F G
  id F := NatTrans.id F
  comp α β := vcomp α β

Depends on / 依赖: NatTrans
-/
instance Functor.category : Category.{max u₁ v₂} (C ⥤ D) where
  Hom F G := NatTrans F G
  id F := NatTrans.id F
  comp α β := vcomp α β

namespace NatTrans

@[ext, grind ext, to_dual self]
/--
theorem `ext'` / 定理 `ext'`

English:
theorem ext'
  given: {α β : F ⟶ G} (w : α.app = β.app)
  statement: α = β
  proof: NatTrans.ext w

@[simp, to_dual self]

中文:
定理 ext'
  条件: {α β : F ⟶ G} (w : α.app = β.app)
  结论: α = β
  证明: NatTrans.ext w

@[simp, to_dual self]

Depends on / 依赖: NatTrans, NatTrans.ext
-/
theorem ext' {α β : F ⟶ G} (w : α.app = β.app) : α = β := NatTrans.ext w

@[simp, to_dual self]
/--
theorem `vcomp_eq_comp` / 定理 `vcomp_eq_comp`

English:
theorem vcomp_eq_comp
  given: (α : F ⟶ G) (β : G ⟶ H)
  statement: vcomp α β = α ≫ β
  proof: rfl

@[to_dual self]

中文:
定理 vcomp_eq_comp
  条件: (α : F ⟶ G) (β : G ⟶ H)
  结论: vcomp α β = α ≫ β
  证明: rfl

@[to_dual self]
-/
theorem vcomp_eq_comp (α : F ⟶ G) (β : G ⟶ H) : vcomp α β = α ≫ β := rfl

@[to_dual self]
/--
theorem `vcomp_app'` / 定理 `vcomp_app'`

English:
theorem vcomp_app'
  given: (α : F ⟶ G) (β : G ⟶ H) (X : C)
  statement: (α ≫ β).app X = α.app X ≫ β.app X
  proof: rfl

@[to_dual self]

中文:
定理 vcomp_app'
  条件: (α : F ⟶ G) (β : G ⟶ H) (X : C)
  结论: (α ≫ β).app X = α.app X ≫ β.app X
  证明: rfl

@[to_dual self]
-/
theorem vcomp_app' (α : F ⟶ G) (β : G ⟶ H) (X : C) : (α ≫ β).app X = α.app X ≫ β.app X := rfl

@[to_dual self]
/--
theorem `congr_app` / 定理 `congr_app`

English:
theorem congr_app
  given: {α β : F ⟶ G} (h : α = β) (X : C)
  statement: α.app X = β.app X
  proof: by rw [h]

@[simp, grind =]

中文:
定理 congr_app
  条件: {α β : F ⟶ G} (h : α = β) (X : C)
  结论: α.app X = β.app X
  证明: by rw [h]

@[simp, grind =]
-/
theorem congr_app {α β : F ⟶ G} (h : α = β) (X : C) : α.app X = β.app X := by rw [h]

@[simp, grind =]
/--
theorem `id_app` / 定理 `id_app`

English:
theorem id_app
  given: (F : C ⥤ D) (X : C)
  statement: (𝟙 F : F ⟶ F).app X = 𝟙 (F.obj X)
  proof: rfl

@[simp, grind _=_, to_dual self, reassoc]

中文:
定理 id_app
  条件: (F : C ⥤ D) (X : C)
  结论: (𝟙 F : F ⟶ F).app X = 𝟙 (F.obj X)
  证明: rfl

@[simp, grind _=_, to_dual self, reassoc]
-/
theorem id_app (F : C ⥤ D) (X : C) : (𝟙 F : F ⟶ F).app X = 𝟙 (F.obj X) := rfl

@[simp, grind _=_, to_dual self, reassoc]
/--
theorem `comp_app` / 定理 `comp_app`

English:
theorem comp_app
  given: {F G H : C ⥤ D} (α : F ⟶ G) (β : G ⟶ H) (X : C)
  proof: rfl

@[to_dual none, reassoc]

中文:
定理 comp_app
  条件: {F G H : C ⥤ D} (α : F ⟶ G) (β : G ⟶ H) (X : C)
  证明: rfl

@[to_dual none, reassoc]
-/
theorem comp_app {F G H : C ⥤ D} (α : F ⟶ G) (β : G ⟶ H) (X : C) :
    (α ≫ β).app X = α.app X ≫ β.app X := rfl

@[to_dual none, reassoc]
/--
theorem `app_naturality` / 定理 `app_naturality`

English:
theorem app_naturality
  given: {F G : C ⥤ D ⥤ E} (T : F ⟶ G) (X : C) {Y Z : D} (f : Y ⟶ Z)
  proof: (T.app X).naturality f

@[to_dual none, reassoc (attr := simp)]

中文:
定理 app_naturality
  条件: {F G : C ⥤ D ⥤ E} (T : F ⟶ G) (X : C) {Y Z : D} (f : Y ⟶ Z)
  证明: (T.app X).naturality f

@[to_dual none, reassoc (attr := simp)]

Depends on / 依赖: T.app, naturality
-/
theorem app_naturality {F G : C ⥤ D ⥤ E} (T : F ⟶ G) (X : C) {Y Z : D} (f : Y ⟶ Z) :
    (F.obj X).map f ≫ (T.app X).app Z = (T.app X).app Y ≫ (G.obj X).map f :=
  (T.app X).naturality f

@[to_dual none, reassoc (attr := simp)]
/--
theorem `naturality_app` / 定理 `naturality_app`

English:
theorem naturality_app
  given: {F G : C ⥤ D ⥤ E} (T : F ⟶ G) (Z : D) {X Y : C} (f : X ⟶ Y)
  proof: congr_fun (congr_arg app (T.naturality f)) Z

@[to_dual none, reassoc]

中文:
定理 naturality_app
  条件: {F G : C ⥤ D ⥤ E} (T : F ⟶ G) (Z : D) {X Y : C} (f : X ⟶ Y)
  证明: congr_fun (congr_arg app (T.naturality f)) Z

@[to_dual none, reassoc]

Depends on / 依赖: T.naturality, congr_arg, congr_fun, naturality
-/
theorem naturality_app {F G : C ⥤ D ⥤ E} (T : F ⟶ G) (Z : D) {X Y : C} (f : X ⟶ Y) :
    (F.map f).app Z ≫ (T.app Y).app Z = (T.app X).app Z ≫ (G.map f).app Z :=
  congr_fun (congr_arg app (T.naturality f)) Z

@[to_dual none, reassoc]
/--
theorem `naturality_app_app` / 定理 `naturality_app_app`

English:
theorem naturality_app_app
  statement: {F G : C ⥤ D ⥤ E ⥤ E'}
  proof: congr_app (NatTrans.naturality_app α X₂ f) X₃

@[reassoc]

中文:
定理 naturality_app_app
  结论: {F G : C ⥤ D ⥤ E ⥤ E'}
  证明: congr_app (NatTrans.naturality_app α X₂ f) X₃

@[reassoc]

Depends on / 依赖: NatTrans, NatTrans.naturality_app, congr_app, naturality_app
-/
theorem naturality_app_app {F G : C ⥤ D ⥤ E ⥤ E'}
    (α : F ⟶ G) {X₁ Y₁ : C} (f : X₁ ⟶ Y₁) (X₂ : D) (X₃ : E) :
    ((F.map f).app X₂).app X₃ ≫ ((α.app Y₁).app X₂).app X₃ =
      ((α.app X₁).app X₂).app X₃ ≫ ((G.map f).app X₂).app X₃ :=
  congr_app (NatTrans.naturality_app α X₂ f) X₃

@[reassoc]
/--
lemma `naturality_inv` / 引理 `naturality_inv`

English:
lemma naturality_inv
  statement: {F G : C ⥤ D} (α : F ⟶ G) {X Y : C} (f : X ⟶ Y) [IsIso (α.app X)]
  proof: by
  rw [IsIso.inv_comp_eq]; rw [← Category.assoc]; rw [IsIso.eq_comp_inv]
  exact α.naturality f

中文:
引理 naturality_inv
  结论: {F G : C ⥤ D} (α : F ⟶ G) {X Y : C} (f : X ⟶ Y) [是同构 (α.app X)]
  证明: by
  rw [IsIso.inv_comp_eq]; rw [← Category.assoc]; rw [IsIso.eq_comp_inv]
  exact α.naturality f

Depends on / 依赖: Category, Category.assoc, IsIso.eq_comp_inv, IsIso.inv_comp_eq, eq_comp_inv, inv_comp_eq, naturality
-/
lemma naturality_inv {F G : C ⥤ D} (α : F ⟶ G) {X Y : C} (f : X ⟶ Y) [IsIso (α.app X)]
    [IsIso (α.app Y)] :
    inv (α.app X) ≫ F.map f = G.map f ≫ inv (α.app Y) := by
  rw [IsIso.inv_comp_eq]; rw [← Category.assoc]; rw [IsIso.eq_comp_inv]
  exact α.naturality f

/-- A natural transformation is an epimorphism if each component is. -/
@[to_dual /-- A natural transformation is a monomorphism if each component is. -/]
/--
theorem `epi_of_epi_app` / 定理 `epi_of_epi_app`

English:
theorem epi_of_epi_app
  given: (α : F ⟶ G) [forall X : C, Epi (α.app X)]
  statement: Epi α
  proof: ⟨fun g h eq => by
    ext X
    rw [← cancel_epi (α.app X)]; rw [← comp_app]; rw [eq]; rw [comp_app]⟩

中文:
定理 epi_of_epi_app
  条件: (α : F ⟶ G) [对任意 X : C, 满态射 (α.app X)]
  结论: 满态射 α
  证明: ⟨fun g h eq => by
    ext X
    rw [← cancel_epi (α.app X)]; rw [← comp_app]; rw [eq]; rw [comp_app]⟩

Depends on / 依赖: cancel_epi, comp_app
-/
theorem epi_of_epi_app (α : F ⟶ G) [forall X : C, Epi (α.app X)] : Epi α :=
  ⟨fun g h eq => by
    ext X
    rw [← cancel_epi (α.app X)]; rw [← comp_app]; rw [eq]; rw [comp_app]⟩

/-- The monoid of natural transformations of the identity is commutative. -/
@[to_dual self]
/--
lemma `id_comm` / 引理 `id_comm`

English:
lemma id_comm
  given: (α β : (𝟭 C) ⟶ (𝟭 C))
  statement: α ≫ β = β ≫ α
  proof: by
  ext X
  exact (α.naturality (β.app X)).symm

中文:
引理 id_comm
  条件: (α β : (𝟭 C) ⟶ (𝟭 C))
  结论: α ≫ β = β ≫ α
  证明: by
  ext X
  exact (α.naturality (β.app X)).symm

Depends on / 依赖: naturality
-/
lemma id_comm (α β : (𝟭 C) ⟶ (𝟭 C)) : α ≫ β = β ≫ α := by
  ext X
  exact (α.naturality (β.app X)).symm

/-- `hcomp α β` is the horizontal composition of natural transformations. -/
@[simps (attr := grind =), to_dual self]
/--
Definition of `hcomp` / `hcomp` 的定义

English:
definition hcomp
  signature: {H I : D ⥤ E} (α : F ⟶ G) (β : H ⟶ I)
  body: fun X : C => β.app (F.obj X) ≫ I.map (α.app X)

中文:
定义 hcomp
  签名: {H I : D ⥤ E} (α : F ⟶ G) (β : H ⟶ I)
  定义体: fun X : C => β.app (F.obj X) ≫ I.map (α.app X)

Depends on / 依赖: F.obj, I.map
-/
def hcomp {H I : D ⥤ E} (α : F ⟶ G) (β : H ⟶ I) : F ⋙ H ⟶ G ⋙ I where
  app := fun X : C => β.app (F.obj X) ≫ I.map (α.app X)

-- Horizontal composition has two possible definitions that are dual to each other,
-- and we need to prove to `to_dual` that these are equivalent.
set_option linter.auxLemma false in
attribute [to_dual none] hcomp._proof_2 hcomp._proof_3
to_dual_insert_cast hcomp := by ext x; exact β.naturality' (α.app x)

/-- Notation for horizontal composition of natural transformations. -/
infixl:80 " ◫ " => hcomp

@[to_dual self]
/--
theorem `hcomp_id_app` / 定理 `hcomp_id_app`

English:
theorem hcomp_id_app
  given: {H : D ⥤ E} (α : F ⟶ G) (X : C)
  statement: (α ◫ 𝟙 H).app X = H.map (α.app X)
  proof: by
  simp

@[to_dual self]

中文:
定理 hcomp_id_app
  条件: {H : D ⥤ E} (α : F ⟶ G) (X : C)
  结论: (α ◫ 𝟙 H).app X = H.map (α.app X)
  证明: by
  simp

@[to_dual self]
-/
theorem hcomp_id_app {H : D ⥤ E} (α : F ⟶ G) (X : C) : (α ◫ 𝟙 H).app X = H.map (α.app X) := by
  simp

@[to_dual self]
/--
theorem `id_hcomp_app` / 定理 `id_hcomp_app`

English:
theorem id_hcomp_app
  given: {H : E ⥤ C} (α : F ⟶ G) (X : E)
  statement: (𝟙 H ◫ α).app X = α.app _
  proof: by simp

中文:
定理 id_hcomp_app
  条件: {H : E ⥤ C} (α : F ⟶ G) (X : E)
  结论: (𝟙 H ◫ α).app X = α.app _
  证明: by simp
-/
theorem id_hcomp_app {H : E ⥤ C} (α : F ⟶ G) (X : E) : (𝟙 H ◫ α).app X = α.app _ := by simp

-- Note that we don't yet prove a `hcomp_assoc` lemma here: even stating it is painful, because we
-- need to use associativity of functor composition. (It's true without the explicit associator,
-- because functor composition is definitionally associative,
-- but relying on the definitional equality causes bad problems with elaboration later.)
@[to_dual self]
/--
theorem `exchange` / 定理 `exchange`

English:
theorem exchange
  given: {I J K : D ⥤ E} (α : F ⟶ G) (β : G ⟶ H) (γ : I ⟶ J) (δ : J ⟶ K)
  proof: by
  cat_disch

中文:
定理 exchange
  条件: {I J K : D ⥤ E} (α : F ⟶ G) (β : G ⟶ H) (γ : I ⟶ J) (δ : J ⟶ K)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
theorem exchange {I J K : D ⥤ E} (α : F ⟶ G) (β : G ⟶ H) (γ : I ⟶ J) (δ : J ⟶ K) :
    (α ≫ β) ◫ (γ ≫ δ) = (α ◫ γ) ≫ β ◫ δ := by
  cat_disch

end NatTrans

namespace Functor

/-- Flip the arguments of a bifunctor. See also `Currying.lean`. -/
@[implicit_reducible, simps (attr := grind =) obj_obj obj_map]
/--
Definition of `flip` / `flip` 的定义

English:
definition flip
  signature: (F : C ⥤ D ⥤ E)
  body: { obj := fun j => (F.obj j).obj k,
      map := fun f => (F.map f).app k, }
  map f := { app := fun j => (F.obj j).map f }

中文:
定义 flip
  签名: (F : C ⥤ D ⥤ E)
  定义体: { obj := fun j => (F.obj j).obj k,
      map := fun f => (F.map f).app k, }
  map f := { app := fun j => (F.obj j).map f }
-/
protected def flip (F : C ⥤ D ⥤ E) : D ⥤ C ⥤ E where
  obj k :=
    { obj := fun j => (F.obj j).obj k,
      map := fun f => (F.map f).app k, }
  map f := { app := fun j => (F.obj j).map f }

-- `@[simps]` doesn't produce a nicely stated lemma here:
-- the implicit arguments for `app` use the definition of `flip`, rather than `flip` itself.
/--
theorem `flip_map_app` / 定理 `flip_map_app`

English:
theorem flip_map_app
  given: (F : C ⥤ D ⥤ E) {d d' : D} (f : d ⟶ d') (c : C)
  proof: rfl

中文:
定理 flip_map_app
  条件: (F : C ⥤ D ⥤ E) {d d' : D} (f : d ⟶ d') (c : C)
  证明: rfl
-/
@[simp, grind =] theorem flip_map_app (F : C ⥤ D ⥤ E) {d d' : D} (f : d ⟶ d') (c : C) :
    (F.flip.map f).app c = (F.obj c).map f := rfl

/-- The left unitor, a natural isomorphism `((𝟭 _) ⋙ F) ≅ F`.
-/
@[implicit_reducible, simps]
/--
Definition of `leftUnitor` / `leftUnitor` 的定义

English:
definition leftUnitor
  signature: (F : C ⥤ D)
  body: { app := fun X => 𝟙 (F.obj X) }
  inv := { app := fun X => 𝟙 (F.obj X) }

中文:
定义 leftUnitor
  签名: (F : C ⥤ D)
  定义体: { app := fun X => 𝟙 (F.obj X) }
  inv := { app := fun X => 𝟙 (F.obj X) }

Depends on / 依赖: F.obj
-/
def leftUnitor (F : C ⥤ D) :
    𝟭 C ⋙ F ≅ F where
  hom := { app := fun X => 𝟙 (F.obj X) }
  inv := { app := fun X => 𝟙 (F.obj X) }

/-- The right unitor, a natural isomorphism `(F ⋙ (𝟭 B)) ≅ F`.
-/
@[implicit_reducible, simps]
/--
Definition of `rightUnitor` / `rightUnitor` 的定义

English:
definition rightUnitor
  signature: (F : C ⥤ D)
  body: { app := fun X => 𝟙 (F.obj X) }
  inv := { app := fun X => 𝟙 (F.obj X) }

中文:
定义 rightUnitor
  签名: (F : C ⥤ D)
  定义体: { app := fun X => 𝟙 (F.obj X) }
  inv := { app := fun X => 𝟙 (F.obj X) }

Depends on / 依赖: F.obj
-/
def rightUnitor (F : C ⥤ D) :
    F ⋙ 𝟭 D ≅ F where
  hom := { app := fun X => 𝟙 (F.obj X) }
  inv := { app := fun X => 𝟙 (F.obj X) }

/-- The associator for functors, a natural isomorphism `((F ⋙ G) ⋙ H) ≅ (F ⋙ (G ⋙ H))`.

(In fact, `iso.refl _` will work here, but it tends to make Lean slow later,
and it's usually best to insert explicit associators.)
-/
@[implicit_reducible, simps]
/--
Definition of `associator` / `associator` 的定义

English:
definition associator
  signature: (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ E')
  body: { app := fun _ => 𝟙 _ }
  inv := { app := fun _ => 𝟙 _ }

中文:
定义 associator
  签名: (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ E')
  定义体: { app := fun _ => 𝟙 _ }
  inv := { app := fun _ => 𝟙 _ }
-/
def associator (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ E') :
    (F ⋙ G) ⋙ H ≅ F ⋙ G ⋙ H where
  hom := { app := fun _ => 𝟙 _ }
  inv := { app := fun _ => 𝟙 _ }

/--
theorem `assoc` / 定理 `assoc`

English:
theorem assoc
  given: (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ E')
  statement: (F ⋙ G) ⋙ H = F ⋙ G ⋙ H
  proof: rfl

中文:
定理 assoc
  条件: (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ E')
  结论: (F ⋙ G) ⋙ H = F ⋙ G ⋙ H
  证明: rfl
-/
protected theorem assoc (F : C ⥤ D) (G : D ⥤ E) (H : E ⥤ E') : (F ⋙ G) ⋙ H = F ⋙ G ⋙ H :=
  rfl

end Functor

variable (C D E) in
/-- The functor `(C ⥤ D ⥤ E) ⥤ D ⥤ C ⥤ E` which flips the variables. -/
@[implicit_reducible, simps]
/--
Definition of `flipFunctor` / `flipFunctor` 的定义

English:
definition flipFunctor
  signature: : (C ⥤ D ⥤ E) ⥤ D ⥤ C ⥤ E where
  body: F.flip
  map {F₁ F₂} φ :=
    { app := fun Y =>
      { app := fun X => (φ.app X).app Y } }

中文:
定义 flipFunctor
  签名: : (C ⥤ D ⥤ E) ⥤ D ⥤ C ⥤ E where
  定义体: F.flip
  map {F₁ F₂} φ :=
    { app := fun Y =>
      { app := fun X => (φ.app X).app Y } }

Depends on / 依赖: F.flip
-/
def flipFunctor : (C ⥤ D ⥤ E) ⥤ D ⥤ C ⥤ E where
  obj F := F.flip
  map {F₁ F₂} φ :=
    { app := fun Y =>
      { app := fun X => (φ.app X).app Y } }

namespace Iso

@[reassoc (attr := simp)]
/--
theorem `map_hom_inv_id_app` / 定理 `map_hom_inv_id_app`

English:
theorem map_hom_inv_id_app
  given: {X Y : C} (e : X ≅ Y) (F : C ⥤ D ⥤ E) (Z : D)
  proof: by
  cat_disch

@[reassoc (attr := simp)]

中文:
定理 map_hom_inv_id_app
  条件: {X Y : C} (e : X ≅ Y) (F : C ⥤ D ⥤ E) (Z : D)
  证明: by
  cat_disch

@[reassoc (attr := simp)]

Depends on / 依赖: cat_disch
-/
theorem map_hom_inv_id_app {X Y : C} (e : X ≅ Y) (F : C ⥤ D ⥤ E) (Z : D) :
    (F.map e.hom).app Z ≫ (F.map e.inv).app Z = 𝟙 _ := by
  cat_disch

@[reassoc (attr := simp)]
/--
theorem `map_inv_hom_id_app` / 定理 `map_inv_hom_id_app`

English:
theorem map_inv_hom_id_app
  given: {X Y : C} (e : X ≅ Y) (F : C ⥤ D ⥤ E) (Z : D)
  proof: by
  cat_disch

中文:
定理 map_inv_hom_id_app
  条件: {X Y : C} (e : X ≅ Y) (F : C ⥤ D ⥤ E) (Z : D)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
theorem map_inv_hom_id_app {X Y : C} (e : X ≅ Y) (F : C ⥤ D ⥤ E) (Z : D) :
    (F.map e.inv).app Z ≫ (F.map e.hom).app Z = 𝟙 _ := by
  cat_disch

end Iso

/--
Definition of `NatTrans.flipApp` / `NatTrans.flipApp` 的定义

English:
abbreviation NatTrans.flipApp
  signature: {G G' : C ⥤ D ⥤ E} (τ : G ⟶ G') (Y : D)
  body: ((flipFunctor _ _ _).map τ).app Y

中文:
缩写 自然变换.flipApp
  签名: {G G' : C ⥤ D ⥤ E} (τ : G ⟶ G') (Y : D)
  定义体: ((flipFunctor _ _ _).map τ).app Y

Depends on / 依赖: flipFunctor
-/
abbrev NatTrans.flipApp {G G' : C ⥤ D ⥤ E} (τ : G ⟶ G') (Y : D) :
    G.flip.obj Y ⟶ G'.flip.obj Y :=
  ((flipFunctor _ _ _).map τ).app Y

end CategoryTheory
