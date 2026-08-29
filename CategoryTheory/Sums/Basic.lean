/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Equivalence

/-!
# Binary disjoint unions of categories

We define the category instance on `C ⊕ D` when `C` and `D` are categories.

We define:
* `inl_` : the functor `C ⥤ C ⊕ D`
* `inr_` : the functor `D ⥤ C ⊕ D`
* `swap` : the functor `C ⊕ D ⥤ D ⊕ C`
    (and the fact this is an equivalence)

We provide an induction principle `Sum.homInduction` to reason and work with morphisms in this
category.

The sum of two functors `F : A ⥤ C` and `G : B ⥤ C` is a functor `A ⊕ B ⥤ C`, written `F.sum' G`.
This construction should be preferred when defining functors out of a sum.

We provide natural isomorphisms `inlCompSum' : inl_ ⋙ F.sum' G ≅ F` and
`inrCompSum' : inr_ ⋙ F.sum' G ≅ G`.

Furthermore, we provide `Functor.sumIsoExt`, which
constructs a natural isomorphism of functors out of a sum out of natural isomorphism with
their precomposition with the inclusion. This construction should be preferred when trying
to construct isomorphisms between functors out of a sum.

We further define sums of functors and natural transformations, written `F.sum G` and `α.sum β`.
-/

@[expose] public section


namespace CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

-- morphism levels before object levels. See note [category_theory universes].
open Sum CategoryTheory.Functor

section

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]

/--
Instance `sum` / 实例 `sum`

English:
instance sum
  signature: : Category.{max v₁ v₂} (C oplus D) where
  body: match X, Y with
    | inl X, inl Y => ULift.{max v₁ v₂} (X ⟶ Y)
    | inl _, inr _ => PEmpty
    | inr _, inl _ => PEmpty
    | inr X, inr Y => ULift.{max v₁ v₂} (X ⟶ Y)
  id X :=
    match X with
    | inl X => ULift.up (𝟙 X)
    | inr X => ULift.up (𝟙 X)
  comp {X Y Z} f g :=
    match X, Y, Z, f,

中文:
实例 求和
  签名: : 范畴.{最大值 v₁ v₂} (C oplus D) where
  定义体: match X, Y with
    | inl X, inl Y => ULift.{max v₁ v₂} (X ⟶ Y)
    | inl _, inr _ => PEmpty
    | inr _, inl _ => PEmpty
    | inr X, inr Y => ULift.{max v₁ v₂} (X ⟶ Y)
  id X :=
    match X with
    | inl X => ULift.up (𝟙 X)
    | inr X => ULift.up (𝟙 X)
  comp {X Y Z} f g :=
    match X, Y, Z, f,

Depends on / 依赖: PEmpty, ULift.up, f.down, g.down
-/
instance sum : Category.{max v₁ v₂} (C oplus D) where
  Hom X Y :=
    match X, Y with
    | inl X, inl Y => ULift.{max v₁ v₂} (X ⟶ Y)
    | inl _, inr _ => PEmpty
    | inr _, inl _ => PEmpty
    | inr X, inr Y => ULift.{max v₁ v₂} (X ⟶ Y)
  id X :=
    match X with
    | inl X => ULift.up (𝟙 X)
    | inr X => ULift.up (𝟙 X)
  comp {X Y Z} f g :=
    match X, Y, Z, f, g with
| inl _, inl _, inl _, f, g => ULift.up f.down ≫ g.down
| inr _, inr _, inr _, f, g => ULift.up f.down ≫ g.down

@[aesop norm -10 destruct (rule_sets := [CategoryTheory])]
/--
theorem `hom_inl_inr_false` / 定理 `hom_inl_inr_false`

English:
theorem hom_inl_inr_false
  given: {X : C} {Y : D} (f : Sum.inl X ⟶ Sum.inr Y)
  statement: False
  proof: by
  cases f

@[aesop norm -10 destruct (rule_sets := [CategoryTheory])]

中文:
定理 hom_inl_inr_false
  条件: {X : C} {Y : D} (f : 和.inl X ⟶ 和.inr Y)
  结论: 假
  证明: by
  cases f

@[aesop norm -10 destruct (rule_sets := [CategoryTheory])]
-/
theorem hom_inl_inr_false {X : C} {Y : D} (f : Sum.inl X ⟶ Sum.inr Y) : False := by
  cases f

@[aesop norm -10 destruct (rule_sets := [CategoryTheory])]
/--
theorem `hom_inr_inl_false` / 定理 `hom_inr_inl_false`

English:
theorem hom_inr_inl_false
  given: {X : C} {Y : D} (f : Sum.inr X ⟶ Sum.inl Y)
  statement: False
  proof: by
  cases f

中文:
定理 hom_inr_inl_false
  条件: {X : C} {Y : D} (f : 和.inr X ⟶ 和.inl Y)
  结论: 假
  证明: by
  cases f
-/
theorem hom_inr_inl_false {X : C} {Y : D} (f : Sum.inr X ⟶ Sum.inl Y) : False := by
  cases f

end

namespace Sum

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]

-- Unfortunate naming here, suggestions welcome.
/-- `inl_` is the functor `X ↦ inl X`. -/
@[simps! obj]
/--
Definition of `inl_` / `inl_` 的定义

English:
definition inl_
  signature: : C ⥤ C oplus D where
  body: inl X
  map f := ULift.up f

中文:
定义 inl_
  签名: : C ⥤ C oplus D where
  定义体: inl X
  map f := ULift.up f
-/
def inl_ : C ⥤ C oplus D where
  obj X := inl X
  map f := ULift.up f

/-- `inr_` is the functor `X ↦ inr X`. -/
@[simps! obj]
/--
Definition of `inr_` / `inr_` 的定义

English:
definition inr_
  signature: : D ⥤ C oplus D where
  body: inr X
  map f := ULift.up f

中文:
定义 inr_
  签名: : D ⥤ C oplus D where
  定义体: inr X
  map f := ULift.up f
-/
def inr_ : D ⥤ C oplus D where
  obj X := inr X
  map f := ULift.up f

variable {C D}

/-- An induction principle for morphisms in a sum of categories: a morphism is either of the form
`(inl_ _ _).map _` or of the form `(inr_ _ _).map _`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
/--
Definition of `homInduction` / `homInduction` 的定义

English:
definition homInduction
  signature: {P : {x y : C oplus D} -> (x ⟶ y) -> Sort*}
  body: match x, y, f with
  | .inl x, .inl y, f => inl x y f.down
  | .inr x, .inr y, f => inr x y f.down

@[simp]

中文:
定义 homInduction
  签名: {P : {x y : C oplus D} -> (x ⟶ y) -> 类型层*}
  定义体: match x, y, f with
  | .inl x, .inl y, f => inl x y f.down
  | .inr x, .inr y, f => inr x y f.down

@[simp]

Depends on / 依赖: f.down
-/
def homInduction {P : {x y : C oplus D} -> (x ⟶ y) -> Sort*}
    (inl : forall x y : C, (f : x ⟶ y) -> P ((inl_ C D).map f))
    (inr : forall x y : D, (f : x ⟶ y) -> P ((inr_ C D).map f))
    {x y : C oplus D} (f : x ⟶ y) : P f :=
  match x, y, f with
  | .inl x, .inl y, f => inl x y f.down
  | .inr x, .inr y, f => inr x y f.down

@[simp]
/--
lemma `homInduction_left` / 引理 `homInduction_left`

English:
lemma homInduction_left
  statement: {P : {x y : C oplus D} -> (x ⟶ y) -> Sort*}
  proof: rfl

@[simp]

中文:
引理 homInduction_left
  结论: {P : {x y : C oplus D} -> (x ⟶ y) -> 类型层*}
  证明: rfl

@[simp]
-/
lemma homInduction_left {P : {x y : C oplus D} -> (x ⟶ y) -> Sort*}
    (inl : forall x y : C, (f : x ⟶ y) -> P ((inl_ C D).map f))
    (inr : forall x y : D, (f : x ⟶ y) -> P ((inr_ C D).map f))
    {x y : C} (f : x ⟶ y) : homInduction inl inr ((inl_ C D).map f) = inl x y f :=
  rfl

@[simp]
/--
lemma `homInduction_right` / 引理 `homInduction_right`

English:
lemma homInduction_right
  statement: {P : {x y : C oplus D} -> (x ⟶ y) -> Sort*}
  proof: rfl

中文:
引理 homInduction_right
  结论: {P : {x y : C oplus D} -> (x ⟶ y) -> 类型层*}
  证明: rfl
-/
lemma homInduction_right {P : {x y : C oplus D} -> (x ⟶ y) -> Sort*}
    (inl : forall x y : C, (f : x ⟶ y) -> P ((inl_ C D).map f))
    (inr : forall x y : D, (f : x ⟶ y) -> P ((inr_ C D).map f))
    {x y : D} (f : x ⟶ y) : homInduction inl inr ((inr_ C D).map f) = inr x y f :=
  rfl

end Sum

namespace Functor

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B] {C : Type u₃}
  [Category.{v₃} C] {D : Type u₄} [Category.{v₄} D]

section Sum'

variable (F : A ⥤ C) (G : B ⥤ C)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `sum'` / `sum'` 的定义

English:
definition sum'
  signature: : A oplus B ⥤ C where
  body: Sum.homInduction (inl := fun _ _ f => F.map f) (inr := fun _ _ g => G.map g) f
  map_comp {x y z} f g := by
    cases f <;> cases g <;> simp [← Functor.map_comp]
  map_id x := by
    cases x <;> (simp only [← map_id]; rfl)

中文:
定义 求和'
  签名: : A oplus B ⥤ C where
  定义体: Sum.homInduction (inl := fun _ _ f => F.map f) (inr := fun _ _ g => G.map g) f
  map_comp {x y z} f g := by
    cases f <;> cases g <;> simp [← Functor.map_comp]
  map_id x := by
    cases x <;> (simp only [← map_id]; rfl)

Depends on / 依赖: F.map, G.map, Sum.homInduction, homInduction
-/
def sum' : A oplus B ⥤ C where
  obj
  | inl X => F.obj X
  | inr X => G.obj X
  map {X Y} f := Sum.homInduction (inl := fun _ _ f => F.map f) (inr := fun _ _ g => G.map g) f
  map_comp {x y z} f g := by
    cases f <;> cases g <;> simp [← Functor.map_comp]
  map_id x := by
    cases x <;> (simp only [← map_id]; rfl)

set_option backward.isDefEq.respectTransparency false in
/-- The sum `F.sum' G` precomposed with the left inclusion functor is isomorphic to `F` -/
@[simps!]
/--
Definition of `inlCompSum'` / `inlCompSum'` 的定义

English:
definition inlCompSum'
  signature: : Sum.inl_ A B ⋙ F.sum' G ≅ F
  body: NatIso.ofComponents fun _ => Iso.refl _

中文:
定义 inlCompSum'
  签名: : 和.inl_ A B ⋙ F.求和' G ≅ F
  定义体: NatIso.ofComponents fun _ => Iso.refl _

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def inlCompSum' : Sum.inl_ A B ⋙ F.sum' G ≅ F :=
  NatIso.ofComponents fun _ => Iso.refl _

set_option backward.isDefEq.respectTransparency false in
/-- The sum `F.sum' G` precomposed with the right inclusion functor is isomorphic to `G` -/
@[simps!]
/--
Definition of `inrCompSum'` / `inrCompSum'` 的定义

English:
definition inrCompSum'
  signature: : Sum.inr_ A B ⋙ F.sum' G ≅ G
  body: NatIso.ofComponents fun _ => Iso.refl _

@[simp]

中文:
定义 inrCompSum'
  签名: : 和.inr_ A B ⋙ F.求和' G ≅ G
  定义体: NatIso.ofComponents fun _ => Iso.refl _

@[simp]

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def inrCompSum' : Sum.inr_ A B ⋙ F.sum' G ≅ G :=
  NatIso.ofComponents fun _ => Iso.refl _

@[simp]
/--
theorem `sum'_obj_inl` / 定理 `sum'_obj_inl`

English:
theorem sum'_obj_inl
  given: (a : A)
  statement: (F.sum' G).obj (inl a) = (F.obj a)
  proof: rfl

@[simp]

中文:
定理 求和'_obj_inl
  条件: (a : A)
  结论: (F.求和' G).obj (inl a) = (F.obj a)
  证明: rfl

@[simp]
-/
theorem sum'_obj_inl (a : A) : (F.sum' G).obj (inl a) = (F.obj a) :=
  rfl

@[simp]
/--
theorem `sum'_obj_inr` / 定理 `sum'_obj_inr`

English:
theorem sum'_obj_inr
  given: (b : B)
  statement: (F.sum' G).obj (inr b) = (G.obj b)
  proof: rfl

@[simp]

中文:
定理 求和'_obj_inr
  条件: (b : B)
  结论: (F.求和' G).obj (inr b) = (G.obj b)
  证明: rfl

@[simp]
-/
theorem sum'_obj_inr (b : B) : (F.sum' G).obj (inr b) = (G.obj b) :=
  rfl

@[simp]
/--
theorem `sum'_map_inl` / 定理 `sum'_map_inl`

English:
theorem sum'_map_inl
  given: {a a' : A} (f : a ⟶ a')
  proof: rfl

@[simp]

中文:
定理 求和'_map_inl
  条件: {a a' : A} (f : a ⟶ a')
  证明: rfl

@[simp]

Depends on / 依赖: Nat.cast_le, P.nonUniforms_mono, card_le_card, cast_le, nonUniforms_mono
-/
theorem sum'_map_inl {a a' : A} (f : a ⟶ a') :
    (F.sum' G).map ((Sum.inl_ _ _).map f) = F.map f :=
  rfl

@[simp]
/--
theorem `sum'_map_inr` / 定理 `sum'_map_inr`

English:
theorem sum'_map_inr
  given: {b b' : B} (f : b ⟶ b')
  proof: rfl

中文:
定理 求和'_map_inr
  条件: {b b' : B} (f : b ⟶ b')
  证明: rfl
-/
theorem sum'_map_inr {b b' : B} (f : b ⟶ b') :
    (F.sum' G).map ((Sum.inr_ _ _).map f) = G.map f :=
  rfl

end Sum'

/--
Definition of `sum` / `sum` 的定义

English:
definition sum
  signature: (F : A ⥤ B) (G : C ⥤ D)
  body: (F ⋙ Sum.inl_ _ _).sum' (G ⋙ Sum.inr_ _ _)

@[simp]

中文:
定义 求和
  签名: (F : A ⥤ B) (G : C ⥤ D)
  定义体: (F ⋙ Sum.inl_ _ _).sum' (G ⋙ Sum.inr_ _ _)

@[simp]

Depends on / 依赖: Sum.inl_, Sum.inr_, inl_, inr_
-/
def sum (F : A ⥤ B) (G : C ⥤ D) : A oplus C ⥤ B oplus D := (F ⋙ Sum.inl_ _ _).sum' (G ⋙ Sum.inr_ _ _)

@[simp]
/--
theorem `sum_obj_inl` / 定理 `sum_obj_inl`

English:
theorem sum_obj_inl
  given: (F : A ⥤ B) (G : C ⥤ D) (a : A)
  statement: (F.sum G).obj (inl a) = inl (F.obj a)
  proof: rfl

@[simp]

中文:
定理 sum_obj_inl
  条件: (F : A ⥤ B) (G : C ⥤ D) (a : A)
  结论: (F.求和 G).obj (inl a) = inl (F.obj a)
  证明: rfl

@[simp]
-/
theorem sum_obj_inl (F : A ⥤ B) (G : C ⥤ D) (a : A) : (F.sum G).obj (inl a) = inl (F.obj a) :=
  rfl

@[simp]
/--
theorem `sum_obj_inr` / 定理 `sum_obj_inr`

English:
theorem sum_obj_inr
  given: (F : A ⥤ B) (G : C ⥤ D) (c : C)
  statement: (F.sum G).obj (inr c) = inr (G.obj c)
  proof: rfl

中文:
定理 sum_obj_inr
  条件: (F : A ⥤ B) (G : C ⥤ D) (c : C)
  结论: (F.求和 G).obj (inr c) = inr (G.obj c)
  证明: rfl
-/
theorem sum_obj_inr (F : A ⥤ B) (G : C ⥤ D) (c : C) : (F.sum G).obj (inr c) = inr (G.obj c) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `sum_map_inl` / 定理 `sum_map_inl`

English:
theorem sum_map_inl
  given: (F : A ⥤ B) (G : C ⥤ D) {a a' : A} (f : a ⟶ a')
  proof: by
  simp [sum]

中文:
定理 sum_map_inl
  条件: (F : A ⥤ B) (G : C ⥤ D) {a a' : A} (f : a ⟶ a')
  证明: by
  simp [sum]
-/
theorem sum_map_inl (F : A ⥤ B) (G : C ⥤ D) {a a' : A} (f : a ⟶ a') :
    (F.sum G).map ((Sum.inl_ _ _).map f) = (Sum.inl_ _ _).map (F.map f) := by
  simp [sum]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `sum_map_inr` / 定理 `sum_map_inr`

English:
theorem sum_map_inr
  given: (F : A ⥤ B) (G : C ⥤ D) {c c' : C} (f : c ⟶ c')
  proof: by
  simp [sum]

中文:
定理 sum_map_inr
  条件: (F : A ⥤ B) (G : C ⥤ D) {c c' : C} (f : c ⟶ c')
  证明: by
  simp [sum]
-/
theorem sum_map_inr (F : A ⥤ B) (G : C ⥤ D) {c c' : C} (f : c ⟶ c') :
    (F.sum G).map ((Sum.inr_ _ _).map f) = (Sum.inr_ _ _).map (G.map f) := by
  simp [sum]

section

variable {F G : A oplus B ⥤ C}
  (e₁ : Sum.inl_ A B ⋙ F ≅ Sum.inl_ A B ⋙ G)
  (e₂ : Sum.inr_ A B ⋙ F ≅ Sum.inr_ A B ⋙ G)

/--
Definition of `sumIsoExt` / `sumIsoExt` 的定义

English:
definition sumIsoExt
  signature: : F ≅ G
  body: NatIso.ofComponents (fun x =>
    match x with
    | inl x => e₁.app x
    | inr x => e₂.app x)
    (fun {x y} f => by
      cases f
      · simpa using! e₁.hom.naturality _
      · simpa using! e₂.hom.naturality _)

@[simp]

中文:
定义 sumIsoExt
  签名: : F ≅ G
  定义体: NatIso.ofComponents (fun x =>
    match x with
    | inl x => e₁.app x
    | inr x => e₂.app x)
    (fun {x y} f => by
      cases f
      · simpa using! e₁.hom.naturality _
      · simpa using! e₂.hom.naturality _)

@[simp]

Depends on / 依赖: NatIso, NatIso.ofComponents, hom.naturality, naturality, ofComponents
-/
def sumIsoExt : F ≅ G :=
  NatIso.ofComponents (fun x =>
    match x with
    | inl x => e₁.app x
    | inr x => e₂.app x)
    (fun {x y} f => by
      cases f
      · simpa using! e₁.hom.naturality _
      · simpa using! e₂.hom.naturality _)

@[simp]
/--
lemma `sumIsoExt_hom_app_inl` / 引理 `sumIsoExt_hom_app_inl`

English:
lemma sumIsoExt_hom_app_inl
  given: (a : A)
  statement: (sumIsoExt e₁ e₂).hom.app (inl a) = e₁.hom.app a
  proof: rfl

@[simp]

中文:
引理 sumIsoExt_hom_app_inl
  条件: (a : A)
  结论: (sumIsoExt e₁ e₂).hom.app (inl a) = e₁.hom.app a
  证明: rfl

@[simp]
-/
lemma sumIsoExt_hom_app_inl (a : A) : (sumIsoExt e₁ e₂).hom.app (inl a) = e₁.hom.app a := rfl

@[simp]
/--
lemma `sumIsoExt_hom_app_inr` / 引理 `sumIsoExt_hom_app_inr`

English:
lemma sumIsoExt_hom_app_inr
  given: (b : B)
  statement: (sumIsoExt e₁ e₂).hom.app (inr b) = e₂.hom.app b
  proof: rfl

@[simp]

中文:
引理 sumIsoExt_hom_app_inr
  条件: (b : B)
  结论: (sumIsoExt e₁ e₂).hom.app (inr b) = e₂.hom.app b
  证明: rfl

@[simp]
-/
lemma sumIsoExt_hom_app_inr (b : B) : (sumIsoExt e₁ e₂).hom.app (inr b) = e₂.hom.app b := rfl

@[simp]
/--
lemma `sumIsoExt_inv_app_inl` / 引理 `sumIsoExt_inv_app_inl`

English:
lemma sumIsoExt_inv_app_inl
  given: (a : A)
  statement: (sumIsoExt e₁ e₂).inv.app (inl a) = e₁.inv.app a
  proof: rfl

@[simp]

中文:
引理 sumIsoExt_inv_app_inl
  条件: (a : A)
  结论: (sumIsoExt e₁ e₂).inv.app (inl a) = e₁.inv.app a
  证明: rfl

@[simp]
-/
lemma sumIsoExt_inv_app_inl (a : A) : (sumIsoExt e₁ e₂).inv.app (inl a) = e₁.inv.app a := rfl

@[simp]
/--
lemma `sumIsoExt_inv_app_inr` / 引理 `sumIsoExt_inv_app_inr`

English:
lemma sumIsoExt_inv_app_inr
  given: (b : B)
  statement: (sumIsoExt e₁ e₂).inv.app (inr b) = e₂.inv.app b
  proof: rfl

中文:
引理 sumIsoExt_inv_app_inr
  条件: (b : B)
  结论: (sumIsoExt e₁ e₂).inv.app (inr b) = e₂.inv.app b
  证明: rfl
-/
lemma sumIsoExt_inv_app_inr (b : B) : (sumIsoExt e₁ e₂).inv.app (inr b) = e₂.inv.app b := rfl

end

section

variable (F : A oplus B ⥤ C)

/--
Definition of `isoSum` / `isoSum` 的定义

English:
definition isoSum
  signature: : F ≅ (Sum.inl_ A B ⋙ F).sum' (Sum.inr_ A B ⋙ F)
  body: sumIsoExt (inlCompSum' _ _).symm (inrCompSum' _ _).symm

中文:
定义 isoSum
  签名: : F ≅ (和.inl_ A B ⋙ F).求和' (和.inr_ A B ⋙ F)
  定义体: sumIsoExt (inlCompSum' _ _).symm (inrCompSum' _ _).symm

Depends on / 依赖: inlCompSum, inrCompSum, sumIsoExt
-/
def isoSum : F ≅ (Sum.inl_ A B ⋙ F).sum' (Sum.inr_ A B ⋙ F) :=
  sumIsoExt (inlCompSum' _ _).symm (inrCompSum' _ _).symm

variable (a : A) (b : B)

@[simp]
/--
lemma `isoSum_hom_app_inl` / 引理 `isoSum_hom_app_inl`

English:
lemma isoSum_hom_app_inl
  statement: (isoSum F).hom.app (inl a) = 𝟙 (F.obj (inl a))
  proof: rfl

@[simp]

中文:
引理 isoSum_hom_app_inl
  结论: (isoSum F).hom.app (inl a) = 𝟙 (F.obj (inl a))
  证明: rfl

@[simp]
-/
lemma isoSum_hom_app_inl : (isoSum F).hom.app (inl a) = 𝟙 (F.obj (inl a)) := rfl

@[simp]
/--
lemma `isoSum_hom_app_inr` / 引理 `isoSum_hom_app_inr`

English:
lemma isoSum_hom_app_inr
  statement: (isoSum F).hom.app (inr b) = 𝟙 (F.obj (inr b))
  proof: rfl

@[simp]

中文:
引理 isoSum_hom_app_inr
  结论: (isoSum F).hom.app (inr b) = 𝟙 (F.obj (inr b))
  证明: rfl

@[simp]
-/
lemma isoSum_hom_app_inr : (isoSum F).hom.app (inr b) = 𝟙 (F.obj (inr b)) := rfl

@[simp]
/--
lemma `isoSum_inv_app_inl` / 引理 `isoSum_inv_app_inl`

English:
lemma isoSum_inv_app_inl
  statement: (isoSum F).inv.app (inl a) = 𝟙 (F.obj (inl a))
  proof: rfl

@[simp]

中文:
引理 isoSum_inv_app_inl
  结论: (isoSum F).inv.app (inl a) = 𝟙 (F.obj (inl a))
  证明: rfl

@[simp]
-/
lemma isoSum_inv_app_inl : (isoSum F).inv.app (inl a) = 𝟙 (F.obj (inl a)) := rfl

@[simp]
/--
lemma `isoSum_inv_app_inr` / 引理 `isoSum_inv_app_inr`

English:
lemma isoSum_inv_app_inr
  statement: (isoSum F).inv.app (inr b) = 𝟙 (F.obj (inr b))
  proof: rfl

中文:
引理 isoSum_inv_app_inr
  结论: (isoSum F).inv.app (inr b) = 𝟙 (F.obj (inr b))
  证明: rfl
-/
lemma isoSum_inv_app_inr : (isoSum F).inv.app (inr b) = 𝟙 (F.obj (inr b)) := rfl

end

end Functor

namespace NatTrans

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B] {C : Type u₃}
  [Category.{v₃} C] {D : Type u₄} [Category.{v₄} D]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `sum'` / `sum'` 的定义

English:
definition sum'
  signature: {F G : A ⥤ C} {H I : B ⥤ C} (α : F ⟶ G) (β : H ⟶ I)
  body: match X with
    | inl X => α.app X
    | inr X => β.app X
  naturality X Y f := by
    cases f <;> simp

@[simp]

中文:
定义 求和'
  签名: {F G : A ⥤ C} {H I : B ⥤ C} (α : F ⟶ G) (β : H ⟶ I)
  定义体: match X with
    | inl X => α.app X
    | inr X => β.app X
  naturality X Y f := by
    cases f <;> simp

@[simp]

Depends on / 依赖: naturality
-/
def sum' {F G : A ⥤ C} {H I : B ⥤ C} (α : F ⟶ G) (β : H ⟶ I) : F.sum' H ⟶ G.sum' I where
  app X :=
    match X with
    | inl X => α.app X
    | inr X => β.app X
  naturality X Y f := by
    cases f <;> simp

@[simp]
/--
theorem `sum'_app_inl` / 定理 `sum'_app_inl`

English:
theorem sum'_app_inl
  given: {F G : A ⥤ C} {H I : B ⥤ C} (α : F ⟶ G) (β : H ⟶ I) (a : A)
  proof: rfl

@[simp]

中文:
定理 求和'_app_inl
  条件: {F G : A ⥤ C} {H I : B ⥤ C} (α : F ⟶ G) (β : H ⟶ I) (a : A)
  证明: rfl

@[simp]
-/
theorem sum'_app_inl {F G : A ⥤ C} {H I : B ⥤ C} (α : F ⟶ G) (β : H ⟶ I) (a : A) :
    (sum' α β).app (inl a) = α.app a :=
  rfl

@[simp]
/--
theorem `sum'_app_inr` / 定理 `sum'_app_inr`

English:
theorem sum'_app_inr
  given: {F G : A ⥤ C} {H I : B ⥤ C} (α : F ⟶ G) (β : H ⟶ I) (b : B)
  proof: rfl

中文:
定理 求和'_app_inr
  条件: {F G : A ⥤ C} {H I : B ⥤ C} (α : F ⟶ G) (β : H ⟶ I) (b : B)
  证明: rfl
-/
theorem sum'_app_inr {F G : A ⥤ C} {H I : B ⥤ C} (α : F ⟶ G) (β : H ⟶ I) (b : B) :
    (sum' α β).app (inr b) = β.app b :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `sum` / `sum` 的定义

English:
definition sum
  signature: {F G : A ⥤ B} {H I : C ⥤ D} (α : F ⟶ G) (β : H ⟶ I)
  body: match X with
    | inl X => (Sum.inl_ B D).map (α.app X)
    | inr X => (Sum.inr_ B D).map (β.app X)
  naturality X Y f := by
    cases f <;> simp [← Functor.map_comp]

@[simp]

中文:
定义 求和
  签名: {F G : A ⥤ B} {H I : C ⥤ D} (α : F ⟶ G) (β : H ⟶ I)
  定义体: match X with
    | inl X => (Sum.inl_ B D).map (α.app X)
    | inr X => (Sum.inr_ B D).map (β.app X)
  naturality X Y f := by
    cases f <;> simp [← Functor.map_comp]

@[simp]

Depends on / 依赖: Functor, Functor.map_comp, Sum.inl_, Sum.inr_, inl_, inr_, map_comp, naturality
-/
def sum {F G : A ⥤ B} {H I : C ⥤ D} (α : F ⟶ G) (β : H ⟶ I) : F.sum H ⟶ G.sum I where
  app X :=
    match X with
    | inl X => (Sum.inl_ B D).map (α.app X)
    | inr X => (Sum.inr_ B D).map (β.app X)
  naturality X Y f := by
    cases f <;> simp [← Functor.map_comp]

@[simp]
/--
theorem `sum_app_inl` / 定理 `sum_app_inl`

English:
theorem sum_app_inl
  given: {F G : A ⥤ B} {H I : C ⥤ D} (α : F ⟶ G) (β : H ⟶ I) (a : A)
  proof: rfl

@[simp]

中文:
定理 sum_app_inl
  条件: {F G : A ⥤ B} {H I : C ⥤ D} (α : F ⟶ G) (β : H ⟶ I) (a : A)
  证明: rfl

@[simp]
-/
theorem sum_app_inl {F G : A ⥤ B} {H I : C ⥤ D} (α : F ⟶ G) (β : H ⟶ I) (a : A) :
    (sum α β).app (inl a) = (Sum.inl_ _ _).map (α.app a) :=
  rfl

@[simp]
/--
theorem `sum_app_inr` / 定理 `sum_app_inr`

English:
theorem sum_app_inr
  given: {F G : A ⥤ B} {H I : C ⥤ D} (α : F ⟶ G) (β : H ⟶ I) (c : C)
  proof: rfl

中文:
定理 sum_app_inr
  条件: {F G : A ⥤ B} {H I : C ⥤ D} (α : F ⟶ G) (β : H ⟶ I) (c : C)
  证明: rfl
-/
theorem sum_app_inr {F G : A ⥤ B} {H I : C ⥤ D} (α : F ⟶ G) (β : H ⟶ I) (c : C) :
    (sum α β).app (inr c) = (Sum.inr_ _ _).map (β.app c) :=
  rfl

end NatTrans

namespace Sum

variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]

/--
Definition of `swap` / `swap` 的定义

English:
definition swap
  signature: : C oplus D ⥤ D oplus C
  body: (inr_ D C).sum' (inl_ D C)

@[simp]

中文:
定义 swap
  签名: : C oplus D ⥤ D oplus C
  定义体: (inr_ D C).sum' (inl_ D C)

@[simp]

Depends on / 依赖: inl_, inr_
-/
def swap : C oplus D ⥤ D oplus C := (inr_ D C).sum' (inl_ D C)

@[simp]
/--
theorem `swap_obj_inl` / 定理 `swap_obj_inl`

English:
theorem swap_obj_inl
  given: (X : C)
  statement: (swap C D).obj (inl X) = inr X
  proof: rfl

@[simp]

中文:
定理 swap_obj_inl
  条件: (X : C)
  结论: (swap C D).obj (inl X) = inr X
  证明: rfl

@[simp]
-/
theorem swap_obj_inl (X : C) : (swap C D).obj (inl X) = inr X :=
  rfl

@[simp]
/--
theorem `swap_obj_inr` / 定理 `swap_obj_inr`

English:
theorem swap_obj_inr
  given: (X : D)
  statement: (swap C D).obj (inr X) = inl X
  proof: rfl

@[simp]

中文:
定理 swap_obj_inr
  条件: (X : D)
  结论: (swap C D).obj (inr X) = inl X
  证明: rfl

@[simp]
-/
theorem swap_obj_inr (X : D) : (swap C D).obj (inr X) = inl X :=
  rfl

@[simp]
/--
theorem `swap_map_inl` / 定理 `swap_map_inl`

English:
theorem swap_map_inl
  given: {X Y : C} {f : inl X ⟶ inl Y}
  statement: (swap C D).map f = f
  proof: rfl

@[simp]

中文:
定理 swap_map_inl
  条件: {X Y : C} {f : inl X ⟶ inl Y}
  结论: (swap C D).map f = f
  证明: rfl

@[simp]
-/
theorem swap_map_inl {X Y : C} {f : inl X ⟶ inl Y} : (swap C D).map f = f :=
  rfl

@[simp]
/--
theorem `swap_map_inr` / 定理 `swap_map_inr`

English:
theorem swap_map_inr
  given: {X Y : D} {f : inr X ⟶ inr Y}
  statement: (swap C D).map f = f
  proof: rfl

中文:
定理 swap_map_inr
  条件: {X Y : D} {f : inr X ⟶ inr Y}
  结论: (swap C D).map f = f
  证明: rfl
-/
theorem swap_map_inr {X Y : D} {f : inr X ⟶ inr Y} : (swap C D).map f = f :=
  rfl

/-- Precomposing `swap` with the left inclusion gives the right inclusion. -/
@[simps! hom_app inv_app]
/--
Definition of `swapCompInl` / `swapCompInl` 的定义

English:
definition swapCompInl
  signature: : inl_ C D ⋙ swap C D ≅ inr_ D C
  body: Functor.inlCompSum' (inr_ _ _) (inl_ _ _)

中文:
定义 swapCompInl
  签名: : inl_ C D ⋙ swap C D ≅ inr_ D C
  定义体: Functor.inlCompSum' (inr_ _ _) (inl_ _ _)

Depends on / 依赖: Functor, Functor.inlCompSum, inlCompSum, inl_, inr_
-/
def swapCompInl : inl_ C D ⋙ swap C D ≅ inr_ D C :=
  Functor.inlCompSum' (inr_ _ _) (inl_ _ _)

/-- Precomposing `swap` with the right inclusion gives the left inclusion. -/
@[simps! hom_app inv_app]
/--
Definition of `swapCompInr` / `swapCompInr` 的定义

English:
definition swapCompInr
  signature: : inr_ C D ⋙ swap C D ≅ inl_ D C
  body: Functor.inrCompSum' (inr_ _ _) (inl_ _ _)

中文:
定义 swapCompInr
  签名: : inr_ C D ⋙ swap C D ≅ inl_ D C
  定义体: Functor.inrCompSum' (inr_ _ _) (inl_ _ _)

Depends on / 依赖: Functor, Functor.inrCompSum, inl_, inrCompSum, inr_
-/
def swapCompInr : inr_ C D ⋙ swap C D ≅ inl_ D C :=
  Functor.inrCompSum' (inr_ _ _) (inl_ _ _)

namespace Swap

set_option backward.defeqAttrib.useBackward true in
/-- `swap` gives an equivalence between `C ⊕ D` and `D ⊕ C`. -/
@[simps functor inverse]
/--
Definition of `equivalence` / `equivalence` 的定义

English:
definition equivalence
  signature: : C oplus D ≌ D oplus C where
  body: swap C D
  inverse := swap D C
  unitIso := Functor.sumIsoExt
    (calc inl_ C D ⋙ 𝟭 (C oplus D)
        ≅ inl_ C D := rightUnitor _
      _ ≅ inr_ D C ⋙ swap D C := (swapCompInr D C).symm
      _ ≅ (inl_ C D ⋙ swap C D) ⋙ swap D C := isoWhiskerRight (swapCompInl C D).symm _
      _ ≅ inl_ C D ⋙ swa

中文:
定义 equivalence
  签名: : C oplus D ≌ D oplus C where
  定义体: swap C D
  inverse := swap D C
  unitIso := Functor.sumIsoExt
    (calc inl_ C D ⋙ 𝟭 (C oplus D)
        ≅ inl_ C D := rightUnitor _
      _ ≅ inr_ D C ⋙ swap D C := (swapCompInr D C).symm
      _ ≅ (inl_ C D ⋙ swap C D) ⋙ swap D C := isoWhiskerRight (swapCompInl C D).symm _
      _ ≅ inl_ C D ⋙ swa
-/
def equivalence : C oplus D ≌ D oplus C where
  functor := swap C D
  inverse := swap D C
  unitIso := Functor.sumIsoExt
    (calc inl_ C D ⋙ 𝟭 (C oplus D)
        ≅ inl_ C D := rightUnitor _
      _ ≅ inr_ D C ⋙ swap D C := (swapCompInr D C).symm
      _ ≅ (inl_ C D ⋙ swap C D) ⋙ swap D C := isoWhiskerRight (swapCompInl C D).symm _
      _ ≅ inl_ C D ⋙ swap C D ⋙ swap D C := associator _ _ _)
    (calc inr_ C D ⋙ 𝟭 (C oplus D)
        ≅ inr_ C D := rightUnitor _
      _ ≅ inl_ D C ⋙ swap D C := (swapCompInl D C).symm
      _ ≅ (inr_ C D ⋙ swap C D) ⋙ swap D C := isoWhiskerRight (swapCompInr C D).symm _
      _ ≅ inr_ C D ⋙ swap C D ⋙ swap D C := associator _ _ _)
  counitIso := Functor.sumIsoExt
    (calc inl_ D C ⋙ swap D C ⋙ swap C D
        ≅ (inl_ D C ⋙ swap D C) ⋙ swap C D := (associator _ _ _).symm
      _ ≅ inr_ C D ⋙ swap C D := isoWhiskerRight (swapCompInl D C) _
      _ ≅ inl_ D C := swapCompInr C D
      _ ≅ inl_ D C ⋙ 𝟭 (D oplus C) := (rightUnitor _).symm)
    (calc inr_ D C ⋙ swap D C ⋙ swap C D
        ≅ (inr_ D C ⋙ swap D C) ⋙ swap C D := (associator _ _ _).symm
      _ ≅ inl_ C D ⋙ swap C D := isoWhiskerRight (swapCompInr D C) _
      _ ≅ inr_ D C := swapCompInl C D
      _ ≅ inr_ D C ⋙ 𝟭 (D oplus C) := (rightUnitor _).symm)

/--
Instance `isEquivalence` / 实例 `isEquivalence`

English:
instance isEquivalence
  signature: : (swap C D).IsEquivalence
  body: (by infer_instance : (equivalence C D).functor.IsEquivalence)

中文:
实例 isEquivalence
  签名: : (swap C D).是等价
  定义体: (by infer_instance : (equivalence C D).functor.IsEquivalence)

Depends on / 依赖: IsEquivalence, equivalence, functor, functor.IsEquivalence, infer_instance
-/
instance isEquivalence : (swap C D).IsEquivalence :=
  (by infer_instance : (equivalence C D).functor.IsEquivalence)

/--
Definition of `symmetry` / `symmetry` 的定义

English:
definition symmetry
  signature: : swap C D ⋙ swap D C ≅ 𝟭 (C oplus D)
  body: (equivalence C D).unitIso.symm

中文:
定义 symmetry
  签名: : swap C D ⋙ swap D C ≅ 𝟭 (C oplus D)
  定义体: (equivalence C D).unitIso.symm

Depends on / 依赖: equivalence, unitIso, unitIso.symm
-/
def symmetry : swap C D ⋙ swap D C ≅ 𝟭 (C oplus D) :=
  (equivalence C D).unitIso.symm

end Swap

end Sum

end CategoryTheory
