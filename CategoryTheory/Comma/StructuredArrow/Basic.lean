/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.PUnit
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Functor.EpiMono

/-!
# The category of "structured arrows"

For `T : C ⥤ D`, a `T`-structured arrow with source `S : D`
is just a morphism `S ⟶ T.obj Y`, for some `Y : C`.

These form a category with morphisms `g : Y ⟶ Y'` making the obvious diagram commute.

We prove that `𝟙 (T.obj Y)` is the initial object in `T`-structured objects with source `T.obj Y`.
-/

@[expose] public section


namespace CategoryTheory

-- morphism levels before object levels. See note [category theory universes].
universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- The category of `T`-structured arrows with domain `S : D` (here `T : C ⥤ D`),
has as its objects `D`-morphisms of the form `S ⟶ T Y`, for some `Y : C`,
and morphisms `C`-morphisms `Y ⟶ Y'` making the obvious triangle commute.
-/
-- We explicitly come from `PUnit.{1}` here to obtain the correct universe for morphisms of
-- structured arrows.
@[implicit_reducible]
/--
Definition of `StructuredArrow` / `StructuredArrow` 的定义

English:
definition StructuredArrow
  signature: (S : D) (T : C ⥤ D)
  body: Comma (Functor.fromPUnit.{0} S) T

中文:
定义 结构化箭头
  签名: (S : D) (T : C ⥤ D)
  定义体: Comma (Functor.fromPUnit.{0} S) T

Depends on / 依赖: Functor, Functor.fromPUnit, fromPUnit
-/
def StructuredArrow (S : D) (T : C ⥤ D) :=
  Comma (Functor.fromPUnit.{0} S) T

/-- The type of morphisms in the category `StructuredArrow`. -/
@[implicit_reducible]
/--
Definition of `StructuredArrow.Hom` / `StructuredArrow.Hom` 的定义

English:
definition StructuredArrow.Hom
  signature: {S : D} {T : C ⥤ D}
  body: CommaMorphism f g

中文:
定义 结构化箭头.态射
  签名: {S : D} {T : C ⥤ D}
  定义体: CommaMorphism f g
-/
protected def StructuredArrow.Hom {S : D} {T : C ⥤ D}
    (f g : StructuredArrow S T) : Type v₁ :=
  CommaMorphism f g

instance {S : D} {T : C ⥤ D} : Category (StructuredArrow S T) where
  Hom := StructuredArrow.Hom
  __ := (inferInstance : Category (Comma _ _))

namespace StructuredArrow

section

variable {S : D} {T : C ⥤ D}

/--
Definition of `right` / `right` 的定义

English:
abbreviation right
  signature: (X : StructuredArrow S T)
  body: Comma.right X

中文:
缩写 right
  签名: (X : 结构化箭头 S T)
  定义体: Comma.right X

Depends on / 依赖: Comma.right
-/
abbrev right (X : StructuredArrow S T) : C := Comma.right X

/--
Definition of `hom` / `hom` 的定义

English:
abbreviation hom
  signature: (X : StructuredArrow S T)
  body: Comma.hom X

中文:
缩写 hom
  签名: (X : 结构化箭头 S T)
  定义体: Comma.hom X

Depends on / 依赖: Comma.hom
-/
abbrev hom (X : StructuredArrow S T) : S ⟶ T.obj X.right := Comma.hom X

variable {X Y : StructuredArrow S T} (f : X ⟶ Y)

/--
Definition of `Hom.right` / `Hom.right` 的定义

English:
abbreviation Hom.right
  signature: : X.right ⟶ Y.right
  body: CommaMorphism.right f

中文:
缩写 态射.right
  签名: : X.right ⟶ Y.right
  定义体: CommaMorphism.right f
-/
abbrev Hom.right : X.right ⟶ Y.right := CommaMorphism.right f

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
theorem `w` / 定理 `w`

English:
theorem w
  statement: X.hom ≫ T.map f.right = Y.hom
  proof: by
  simpa using (CommaMorphism.w f).symm

@[reassoc]

中文:
定理 w
  结论: X.hom ≫ T.map f.right = Y.hom
  证明: by
  simpa using (CommaMorphism.w f).symm

@[reassoc]

Depends on / 依赖: CommaMorphism, CommaMorphism.w
-/
theorem w : X.hom ≫ T.map f.right = Y.hom := by
  simpa using (CommaMorphism.w f).symm

@[reassoc]
/--
lemma `Hom.w` / 引理 `Hom.w`

English:
lemma Hom.w
  statement: X.hom ≫ T.map f.right = Y.hom
  proof: StructuredArrow.w f

中文:
引理 态射.w
  结论: X.hom ≫ T.map f.right = Y.hom
  证明: StructuredArrow.w f
-/
lemma Hom.w : X.hom ≫ T.map f.right = Y.hom := StructuredArrow.w f

end

/-- The obvious projection functor from structured arrows. -/
@[simps!]
/--
Definition of `proj` / `proj` 的定义

English:
definition proj
  signature: (S : D) (T : C ⥤ D)
  body: Comma.snd _ _

中文:
定义 proj
  签名: (S : D) (T : C ⥤ D)
  定义体: Comma.snd _ _

Depends on / 依赖: Comma.snd
-/
def proj (S : D) (T : C ⥤ D) : StructuredArrow S T ⥤ C :=
  Comma.snd _ _

variable {S S' S'' : D} {Y Y' Y'' : C} {T T' : C ⥤ D}

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {X Y : StructuredArrow S T} (f g : X ⟶ Y) (h : f.right = g.right)
  statement: f = g
  proof: CommaMorphism.ext (Subsingleton.elim _ _) h

@[simp]

中文:
引理 hom_ext
  条件: {X Y : 结构化箭头 S T} (f g : X ⟶ Y) (h : f.right = g.right)
  结论: f = g
  证明: CommaMorphism.ext (Subsingleton.elim _ _) h

@[simp]

Depends on / 依赖: CommaMorphism, CommaMorphism.ext, Subsingleton, Subsingleton.elim
-/
lemma hom_ext {X Y : StructuredArrow S T} (f g : X ⟶ Y) (h : f.right = g.right) : f = g :=
  CommaMorphism.ext (Subsingleton.elim _ _) h

@[simp]
/--
theorem `hom_eq_iff` / 定理 `hom_eq_iff`

English:
theorem hom_eq_iff
  given: {X Y : StructuredArrow S T} (f g : X ⟶ Y)
  statement: f = g ↔ f.right = g.right
  proof: ⟨fun h => by rw [h], hom_ext _ _⟩

中文:
定理 hom_eq_iff
  条件: {X Y : 结构化箭头 S T} (f g : X ⟶ Y)
  结论: f = g ↔ f.right = g.right
  证明: ⟨fun h => by rw [h], hom_ext _ _⟩

Depends on / 依赖: hom_ext
-/
theorem hom_eq_iff {X Y : StructuredArrow S T} (f g : X ⟶ Y) : f = g ↔ f.right = g.right :=
  ⟨fun h => by rw [h], hom_ext _ _⟩

/-- Construct a structured arrow from a morphism. -/
@[implicit_reducible]
/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: (f : S ⟶ T.obj Y)
  body: ⟨⟨⟨⟩⟩, Y, f⟩

@[simp]

中文:
定义 mk
  签名: (f : S ⟶ T.obj Y)
  定义体: ⟨⟨⟨⟩⟩, Y, f⟩

@[simp]
-/
def mk (f : S ⟶ T.obj Y) : StructuredArrow S T :=
  ⟨⟨⟨⟩⟩, Y, f⟩

@[simp]
/--
theorem `mk_left` / 定理 `mk_left`

English:
theorem mk_left
  given: (f : S ⟶ T.obj Y)
  statement: (mk f).left = ⟨⟨⟩⟩
  proof: rfl

@[simp]

中文:
定理 mk_left
  条件: (f : S ⟶ T.obj Y)
  结论: (mk f).left = ⟨⟨⟩⟩
  证明: rfl

@[simp]
-/
theorem mk_left (f : S ⟶ T.obj Y) : (mk f).left = ⟨⟨⟩⟩ :=
  rfl

@[simp]
/--
theorem `mk_right` / 定理 `mk_right`

English:
theorem mk_right
  given: (f : S ⟶ T.obj Y)
  statement: (mk f).right = Y
  proof: rfl

@[simp]

中文:
定理 mk_right
  条件: (f : S ⟶ T.obj Y)
  结论: (mk f).right = Y
  证明: rfl

@[simp]
-/
theorem mk_right (f : S ⟶ T.obj Y) : (mk f).right = Y :=
  rfl

@[simp]
/--
theorem `mk_hom_eq_self` / 定理 `mk_hom_eq_self`

English:
theorem mk_hom_eq_self
  given: (f : S ⟶ T.obj Y)
  statement: (mk f).hom = f
  proof: rfl

@[simp, reassoc]

中文:
定理 mk_hom_eq_self
  条件: (f : S ⟶ T.obj Y)
  结论: (mk f).hom = f
  证明: rfl

@[simp, reassoc]
-/
theorem mk_hom_eq_self (f : S ⟶ T.obj Y) : (mk f).hom = f :=
  rfl

@[simp, reassoc]
/--
theorem `comp_right` / 定理 `comp_right`

English:
theorem comp_right
  given: {X Y Z : StructuredArrow S T} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

@[simp]

中文:
定理 comp_right
  条件: {X Y Z : 结构化箭头 S T} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl

@[simp]
-/
theorem comp_right {X Y Z : StructuredArrow S T} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).right = f.right ≫ g.right := rfl

@[simp]
/--
theorem `id_right` / 定理 `id_right`

English:
theorem id_right
  given: (X : StructuredArrow S T)
  statement: (𝟙 X : X ⟶ X).right = 𝟙 X.right
  proof: rfl

@[simp]

中文:
定理 id_right
  条件: (X : 结构化箭头 S T)
  结论: (𝟙 X : X ⟶ X).right = 𝟙 X.right
  证明: rfl

@[simp]
-/
theorem id_right (X : StructuredArrow S T) : (𝟙 X : X ⟶ X).right = 𝟙 X.right := rfl

@[simp]
/--
theorem `eqToHom_right` / 定理 `eqToHom_right`

English:
theorem eqToHom_right
  given: {X Y : StructuredArrow S T} (h : X = Y)
  proof: by
  subst h
  simp only [eqToHom_refl, id_right]

@[simp]

中文:
定理 eqToHom_right
  条件: {X Y : 结构化箭头 S T} (h : X = Y)
  证明: by
  subst h
  simp only [eqToHom_refl, id_right]

@[simp]

Depends on / 依赖: eqToHom_refl, id_right
-/
theorem eqToHom_right {X Y : StructuredArrow S T} (h : X = Y) :
    (eqToHom h).right = eqToHom (by rw [h]) := by
  subst h
  simp only [eqToHom_refl, id_right]

@[simp]
/--
theorem `left_eq_id` / 定理 `left_eq_id`

English:
theorem left_eq_id
  given: {X Y : StructuredArrow S T} (f : X ⟶ Y)
  statement: f.left = 𝟙 X.left
  proof: rfl

中文:
定理 left_eq_id
  条件: {X Y : 结构化箭头 S T} (f : X ⟶ Y)
  结论: f.left = 𝟙 X.left
  证明: rfl
-/
theorem left_eq_id {X Y : StructuredArrow S T} (f : X ⟶ Y) : f.left = 𝟙 X.left := rfl

set_option backward.defeqAttrib.useBackward true in
/-- To construct a morphism of structured arrows,
we need a morphism of the objects underlying the target,
and to check that the triangle commutes.
-/
@[simps right, implicit_reducible]
/--
Definition of `homMk` / `homMk` 的定义

English:
definition homMk
  signature: {f f' : StructuredArrow S T} (g : f.right ⟶ f'.right)
  body: 𝟙 f.left
  right := g

中文:
定义 homMk
  签名: {f f' : 结构化箭头 S T} (g : f.right ⟶ f'.right)
  定义体: 𝟙 f.left
  right := g

Depends on / 依赖: cat_disch, f.left
-/
def homMk {f f' : StructuredArrow S T} (g : f.right ⟶ f'.right)
    (w : f.hom ≫ T.map g = f'.hom := by cat_disch) : f ⟶ f' where
  left := 𝟙 f.left
  right := g

/--
theorem `homMk_surjective` / 定理 `homMk_surjective`

English:
theorem homMk_surjective
  given: {f f' : StructuredArrow S T} (φ : f ⟶ f')
  proof: ⟨φ.right, StructuredArrow.w φ, rfl⟩

中文:
定理 homMk_surjective
  条件: {f f' : 结构化箭头 S T} (φ : f ⟶ f')
  证明: ⟨φ.right, StructuredArrow.w φ, rfl⟩

Depends on / 依赖: StructuredArrow, StructuredArrow.w
-/
theorem homMk_surjective {f f' : StructuredArrow S T} (φ : f ⟶ f') :
    exists (ψ : f.right ⟶ f'.right) (hψ : f.hom ≫ T.map ψ = f'.hom),
      φ = StructuredArrow.homMk ψ hψ :=
  ⟨φ.right, StructuredArrow.w φ, rfl⟩

/-- Given a structured arrow `X ⟶ T(Y)`, and an arrow `Y ⟶ Y'`, we can construct a morphism of
structured arrows given by `(X ⟶ T(Y)) ⟶ (X ⟶ T(Y) ⟶ T(Y'))`. -/
@[simps]
/--
Definition of `homMk'` / `homMk'` 的定义

English:
definition homMk'
  signature: (f : StructuredArrow S T) (g : f.right ⟶ Y')
  body: 𝟙 _
  right := g

中文:
定义 homMk'
  签名: (f : 结构化箭头 S T) (g : f.right ⟶ Y')
  定义体: 𝟙 _
  right := g
-/
def homMk' (f : StructuredArrow S T) (g : f.right ⟶ Y') : f ⟶ mk (f.hom ≫ T.map g) where
  left := 𝟙 _
  right := g

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `homMk'_id` / 引理 `homMk'_id`

English:
lemma homMk'_id
  given: (f : StructuredArrow S T)
  statement: homMk' f (𝟙 f.right) = eqToHom (by cat_disch)
  proof: by
  simp [eqToHom_right]

中文:
引理 homMk'_id
  条件: (f : 结构化箭头 S T)
  结论: homMk' f (𝟙 f.right) = eqToHom (by cat_disch)
  证明: by
  simp [eqToHom_right]
-/
lemma homMk'_id (f : StructuredArrow S T) : homMk' f (𝟙 f.right) = eqToHom (by cat_disch) := by
  simp [eqToHom_right]

/--
lemma `homMk'_mk_id` / 引理 `homMk'_mk_id`

English:
lemma homMk'_mk_id
  given: (f : S ⟶ T.obj Y)
  statement: homMk' (mk f) (𝟙 Y) = eqToHom (by simp)
  proof: homMk'_id _

中文:
引理 homMk'_mk_id
  条件: (f : S ⟶ T.obj Y)
  结论: homMk' (mk f) (𝟙 Y) = eqToHom (by simp)
  证明: homMk'_id _
-/
lemma homMk'_mk_id (f : S ⟶ T.obj Y) : homMk' (mk f) (𝟙 Y) = eqToHom (by simp) :=
  homMk'_id _

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `homMk'_comp` / 引理 `homMk'_comp`

English:
lemma homMk'_comp
  given: (f : StructuredArrow S T) (g : f.right ⟶ Y') (g' : Y' ⟶ Y'')
  proof: by
  simp [eqToHom_right]

中文:
引理 homMk'_comp
  条件: (f : 结构化箭头 S T) (g : f.right ⟶ Y') (g' : Y' ⟶ Y'')
  证明: by
  simp [eqToHom_right]
-/
lemma homMk'_comp (f : StructuredArrow S T) (g : f.right ⟶ Y') (g' : Y' ⟶ Y'') :
    homMk' f (g ≫ g') = homMk' f g ≫ homMk' (mk (f.hom ≫ T.map g)) g' ≫ eqToHom (by simp) := by
  simp [eqToHom_right]

/--
lemma `homMk'_mk_comp` / 引理 `homMk'_mk_comp`

English:
lemma homMk'_mk_comp
  given: (f : S ⟶ T.obj Y) (g : Y ⟶ Y') (g' : Y' ⟶ Y'')
  proof: homMk'_comp _ _ _

中文:
引理 homMk'_mk_comp
  条件: (f : S ⟶ T.obj Y) (g : Y ⟶ Y') (g' : Y' ⟶ Y'')
  证明: homMk'_comp _ _ _
-/
lemma homMk'_mk_comp (f : S ⟶ T.obj Y) (g : Y ⟶ Y') (g' : Y' ⟶ Y'') :
    homMk' (mk f) (g ≫ g') = homMk' (mk f) g ≫ homMk' (mk (f ≫ T.map g)) g' ≫ eqToHom (by simp) :=
  homMk'_comp _ _ _

/-- Variant of `homMk'` where both objects are applications of `mk`. -/
@[simps]
/--
Definition of `mkPostcomp` / `mkPostcomp` 的定义

English:
definition mkPostcomp
  signature: (f : S ⟶ T.obj Y) (g : Y ⟶ Y')
  body: 𝟙 _
  right := g

中文:
定义 mkPostcomp
  签名: (f : S ⟶ T.obj Y) (g : Y ⟶ Y')
  定义体: 𝟙 _
  right := g
-/
def mkPostcomp (f : S ⟶ T.obj Y) (g : Y ⟶ Y') : mk f ⟶ mk (f ≫ T.map g) where
  left := 𝟙 _
  right := g

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `mkPostcomp_id` / 引理 `mkPostcomp_id`

English:
lemma mkPostcomp_id
  given: (f : S ⟶ T.obj Y)
  statement: mkPostcomp f (𝟙 Y) = eqToHom (by simp)
  proof: by simp

中文:
引理 mkPostcomp_id
  条件: (f : S ⟶ T.obj Y)
  结论: mkPostcomp f (𝟙 Y) = eqToHom (by simp)
  证明: by simp

Depends on / 依赖: backward, backward.isDefEq.respectTransparency.types, isDefEq, respectTransparency, set_option
-/
lemma mkPostcomp_id (f : S ⟶ T.obj Y) : mkPostcomp f (𝟙 Y) = eqToHom (by simp) := by simp
set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `mkPostcomp_comp` / 引理 `mkPostcomp_comp`

English:
lemma mkPostcomp_comp
  given: (f : S ⟶ T.obj Y) (g : Y ⟶ Y') (g' : Y' ⟶ Y'')
  proof: by
  simp

中文:
引理 mkPostcomp_comp
  条件: (f : S ⟶ T.obj Y) (g : Y ⟶ Y') (g' : Y' ⟶ Y'')
  证明: by
  simp
-/
lemma mkPostcomp_comp (f : S ⟶ T.obj Y) (g : Y ⟶ Y') (g' : Y' ⟶ Y'') :
    mkPostcomp f (g ≫ g') = mkPostcomp f g ≫ mkPostcomp (f ≫ T.map g) g' ≫ eqToHom (by simp) := by
  simp

set_option backward.defeqAttrib.useBackward true in
/-- To construct an isomorphism of structured arrows,
we need an isomorphism of the objects underlying the target,
and to check that the triangle commutes.
-/
@[simps! hom_right inv_right]
/--
Definition of `isoMk` / `isoMk` 的定义

English:
definition isoMk
  signature: {f f' : StructuredArrow S T} (g : f.right ≅ f'.right)
  body: Comma.isoMk (eqToIso (by ext)) g (by simpa using w.symm)

中文:
定义 isoMk
  签名: {f f' : 结构化箭头 S T} (g : f.right ≅ f'.right)
  定义体: Comma.isoMk (eqToIso (by ext)) g (by simpa using w.symm)

Depends on / 依赖: Comma.isoMk, cat_disch, eqToIso, w.symm
-/
def isoMk {f f' : StructuredArrow S T} (g : f.right ≅ f'.right)
    (w : f.hom ≫ T.map g.hom = f'.hom := by cat_disch) :
    f ≅ f' :=
  Comma.isoMk (eqToIso (by ext)) g (by simpa using w.symm)

/--
theorem `obj_ext` / 定理 `obj_ext`

English:
theorem obj_ext
  statement: (x y : StructuredArrow S T) (hr : x.right = y.right)
  proof: by
  cases x
  cases y
  cases hr
  cat_disch

中文:
定理 obj_ext
  结论: (x y : 结构化箭头 S T) (hr : x.right = y.right)
  证明: by
  cases x
  cases y
  cases hr
  cat_disch

Depends on / 依赖: cat_disch
-/
theorem obj_ext (x y : StructuredArrow S T) (hr : x.right = y.right)
    (hh : x.hom ≫ T.map (eqToHom hr) = y.hom) : x = y := by
  cases x
  cases y
  cases hr
  cat_disch

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {A B : StructuredArrow S T} (f g : A ⟶ B)
  statement: f.right = g.right -> f = g
  proof: CommaMorphism.ext (Subsingleton.elim _ _)

中文:
定理 ext
  条件: {A B : 结构化箭头 S T} (f g : A ⟶ B)
  结论: f.right = g.right -> f = g
  证明: CommaMorphism.ext (Subsingleton.elim _ _)

Depends on / 依赖: CommaMorphism, CommaMorphism.ext, Subsingleton, Subsingleton.elim
-/
theorem ext {A B : StructuredArrow S T} (f g : A ⟶ B) : f.right = g.right -> f = g :=
  CommaMorphism.ext (Subsingleton.elim _ _)

/--
theorem `ext_iff` / 定理 `ext_iff`

English:
theorem ext_iff
  given: {A B : StructuredArrow S T} (f g : A ⟶ B)
  statement: f = g ↔ f.right = g.right
  proof: ⟨fun h => h ▸ rfl, ext f g⟩

中文:
定理 ext_iff
  条件: {A B : 结构化箭头 S T} (f g : A ⟶ B)
  结论: f = g ↔ f.right = g.right
  证明: ⟨fun h => h ▸ rfl, ext f g⟩
-/
theorem ext_iff {A B : StructuredArrow S T} (f g : A ⟶ B) : f = g ↔ f.right = g.right :=
  ⟨fun h => h ▸ rfl, ext f g⟩

/--
Instance `proj_faithful` / 实例 `proj_faithful`

English:
instance proj_faithful
  signature: : (proj S T).Faithful where
  body: ext

中文:
实例 proj_faithful
  签名: : (proj S T).忠实 where
  定义体: ext
-/
instance proj_faithful : (proj S T).Faithful where
  map_injective {_ _} := ext

/--
theorem `mono_of_mono_right` / 定理 `mono_of_mono_right`

English:
theorem mono_of_mono_right
  given: {A B : StructuredArrow S T} (f : A ⟶ B) [h : Mono f.right]
  statement: Mono f
  proof: (proj S T).mono_of_mono_map h

中文:
定理 mono_of_mono_right
  条件: {A B : 结构化箭头 S T} (f : A ⟶ B) [h : 单态射 f.right]
  结论: 单态射 f
  证明: (proj S T).mono_of_mono_map h

Depends on / 依赖: mono_of_mono_map
-/
theorem mono_of_mono_right {A B : StructuredArrow S T} (f : A ⟶ B) [h : Mono f.right] : Mono f :=
  (proj S T).mono_of_mono_map h

/--
theorem `epi_of_epi_right` / 定理 `epi_of_epi_right`

English:
theorem epi_of_epi_right
  given: {A B : StructuredArrow S T} (f : A ⟶ B) [h : Epi f.right]
  statement: Epi f
  proof: (proj S T).epi_of_epi_map h

中文:
定理 epi_of_epi_right
  条件: {A B : 结构化箭头 S T} (f : A ⟶ B) [h : 满态射 f.right]
  结论: 满态射 f
  证明: (proj S T).epi_of_epi_map h

Depends on / 依赖: epi_of_epi_map
-/
theorem epi_of_epi_right {A B : StructuredArrow S T} (f : A ⟶ B) [h : Epi f.right] : Epi f :=
  (proj S T).epi_of_epi_map h

/--
Instance `mono_homMk` / 实例 `mono_homMk`

English:
instance mono_homMk
  signature: {A B : StructuredArrow S T} (f : A.right ⟶ B.right) (w) [h : Mono f]
  body: (proj S T).mono_of_mono_map h

中文:
实例 mono_homMk
  签名: {A B : 结构化箭头 S T} (f : A.right ⟶ B.right) (w) [h : 单态射 f]
  定义体: (proj S T).mono_of_mono_map h

Depends on / 依赖: mono_of_mono_map
-/
instance mono_homMk {A B : StructuredArrow S T} (f : A.right ⟶ B.right) (w) [h : Mono f] :
    Mono (homMk f w) :=
  (proj S T).mono_of_mono_map h

/--
Instance `epi_homMk` / 实例 `epi_homMk`

English:
instance epi_homMk
  signature: {A B : StructuredArrow S T} (f : A.right ⟶ B.right) (w) [h : Epi f]
  body: (proj S T).epi_of_epi_map h

中文:
实例 epi_homMk
  签名: {A B : 结构化箭头 S T} (f : A.right ⟶ B.right) (w) [h : 满态射 f]
  定义体: (proj S T).epi_of_epi_map h

Depends on / 依赖: epi_of_epi_map
-/
instance epi_homMk {A B : StructuredArrow S T} (f : A.right ⟶ B.right) (w) [h : Epi f] :
    Epi (homMk f w) :=
  (proj S T).epi_of_epi_map h

/--
theorem `eq_mk` / 定理 `eq_mk`

English:
theorem eq_mk
  given: (f : StructuredArrow S T)
  statement: f = mk f.hom
  proof: rfl

中文:
定理 eq_mk
  条件: (f : 结构化箭头 S T)
  结论: f = mk f.hom
  证明: rfl
-/
theorem eq_mk (f : StructuredArrow S T) : f = mk f.hom :=
  rfl

/-- Eta rule for structured arrows. -/
@[simps! hom_right inv_right]
/--
Definition of `eta` / `eta` 的定义

English:
definition eta
  signature: (f : StructuredArrow S T)
  body: isoMk (Iso.refl _)

中文:
定义 eta
  签名: (f : 结构化箭头 S T)
  定义体: isoMk (Iso.refl _)

Depends on / 依赖: Iso.refl
-/
def eta (f : StructuredArrow S T) : f ≅ mk f.hom :=
  isoMk (Iso.refl _)

/--
lemma `mk_surjective` / 引理 `mk_surjective`

English:
lemma mk_surjective
  given: (f : StructuredArrow S T)
  proof: ⟨_, _, eq_mk f⟩

中文:
引理 mk_surjective
  条件: (f : 结构化箭头 S T)
  证明: ⟨_, _, eq_mk f⟩

Depends on / 依赖: eq_mk
-/
lemma mk_surjective (f : StructuredArrow S T) :
    exists (Y : C) (g : S ⟶ T.obj Y), f = mk g :=
  ⟨_, _, eq_mk f⟩

/-- A morphism between source objects `S ⟶ S'`
contravariantly induces a functor between structured arrows,
`StructuredArrow S' T ⥤ StructuredArrow S T`.

Ideally this would be described as a 2-functor from `D`
(promoted to a 2-category with equations as 2-morphisms)
to `Cat`.
-/
@[simps!, implicit_reducible]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : S ⟶ S')
  body: Comma.mapLeft _ ((Functor.const _).map f)

@[simp]

中文:
定义 map
  签名: (f : S ⟶ S')
  定义体: Comma.mapLeft _ ((Functor.const _).map f)

@[simp]

Depends on / 依赖: Comma.mapLeft, Functor, Functor.const, mapLeft
-/
def map (f : S ⟶ S') : StructuredArrow S' T ⥤ StructuredArrow S T :=
  Comma.mapLeft _ ((Functor.const _).map f)

@[simp]
/--
theorem `map_mk` / 定理 `map_mk`

English:
theorem map_mk
  given: {f : S' ⟶ T.obj Y} (g : S ⟶ S')
  statement: (map g).obj (mk f) = mk (g ≫ f)
  proof: rfl

@[simp]

中文:
定理 map_mk
  条件: {f : S' ⟶ T.obj Y} (g : S ⟶ S')
  结论: (map g).obj (mk f) = mk (g ≫ f)
  证明: rfl

@[simp]
-/
theorem map_mk {f : S' ⟶ T.obj Y} (g : S ⟶ S') : (map g).obj (mk f) = mk (g ≫ f) :=
  rfl

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  given: {f : StructuredArrow S T}
  statement: (map (𝟙 S)).obj f = f
  proof: by
  rw [eq_mk f]
  simp

@[simp]

中文:
定理 map_id
  条件: {f : 结构化箭头 S T}
  结论: (map (𝟙 S)).obj f = f
  证明: by
  rw [eq_mk f]
  simp

@[simp]

Depends on / 依赖: eq_mk
-/
theorem map_id {f : StructuredArrow S T} : (map (𝟙 S)).obj f = f := by
  rw [eq_mk f]
  simp

@[simp]
/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  given: {f : S ⟶ S'} {f' : S' ⟶ S''} {h : StructuredArrow S'' T}
  proof: by
  rw [eq_mk h]
  simp

#adaptation_note

中文:
定理 map_comp
  条件: {f : S ⟶ S'} {f' : S' ⟶ S''} {h : 结构化箭头 S'' T}
  证明: by
  rw [eq_mk h]
  simp

#adaptation_note

Depends on / 依赖: eq_mk
-/
theorem map_comp {f : S ⟶ S'} {f' : S' ⟶ S''} {h : StructuredArrow S'' T} :
    (map (f ≫ f')).obj h = (map f).obj ((map f').obj h) := by
  rw [eq_mk h]
  simp

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- An isomorphism `S ≅ S'` induces an equivalence `StructuredArrow S T ≌ StructuredArrow S' T`. -/
@[simps!, implicit_reducible]
/--
Definition of `mapIso` / `mapIso` 的定义

English:
definition mapIso
  signature: (i : S ≅ S')
  body: Comma.mapLeftIso _ ((Functor.const _).mapIso i)

中文:
定义 mapIso
  签名: (i : S ≅ S')
  定义体: Comma.mapLeftIso _ ((Functor.const _).mapIso i)

Depends on / 依赖: Comma.mapLeftIso, Functor, Functor.const, mapIso, mapLeftIso
-/
def mapIso (i : S ≅ S') : StructuredArrow S T ≌ StructuredArrow S' T :=
  Comma.mapLeftIso _ ((Functor.const _).mapIso i)

/-- A natural isomorphism `T ≅ T'` induces an equivalence
`StructuredArrow S T ≌ StructuredArrow S T'`. -/
@[simps!, implicit_reducible]
/--
Definition of `mapNatIso` / `mapNatIso` 的定义

English:
definition mapNatIso
  signature: (i : T ≅ T')
  body: Comma.mapRightIso _ i

中文:
定义 map自然数Iso
  签名: (i : T ≅ T')
  定义体: Comma.mapRightIso _ i

Depends on / 依赖: Comma.mapRightIso, mapRightIso
-/
def mapNatIso (i : T ≅ T') : StructuredArrow S T ≌ StructuredArrow S T' :=
  Comma.mapRightIso _ i

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `proj_reflectsIsomorphisms` / 实例 `proj_reflectsIsomorphisms`

English:
instance proj_reflectsIsomorphisms
  signature: : (proj S T).ReflectsIsomorphisms where
  body: ⟨StructuredArrow.homMk (inv ((proj S T).map f) :), by simp⟩

中文:
实例 proj_reflectsIsomorphisms
  签名: : (proj S T).反映同构 where
  定义体: ⟨StructuredArrow.homMk (inv ((proj S T).map f) :), by simp⟩

Depends on / 依赖: HasProduct, StructuredArrow, StructuredArrow.homMk, U.isLimitPowerFan, hasWidePullback_of_isTerminal, isLimitPowerFan, isTerminalIncl
-/
instance proj_reflectsIsomorphisms : (proj S T).ReflectsIsomorphisms where
  reflects f t := ⟨StructuredArrow.homMk (inv ((proj S T).map f) :), by simp⟩

open CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `mkIdInitial` / `mkIdInitial` 的定义

English:
definition mkIdInitial
  signature: [T.Full] [T.Faithful]
  body: homMk (T.preimage c.pt.hom)
  uniq c m _ := by
    apply CommaMorphism.ext
    · simp
    · apply T.map_injective
      simpa only [homMk_right, T.map_preimage, ← w m] using! (Category.id_comp _).symm

中文:
定义 mkIdInitial
  签名: [T.满] [T.忠实]
  定义体: homMk (T.preimage c.pt.hom)
  uniq c m _ := by
    apply CommaMorphism.ext
    · simp
    · apply T.map_injective
      simpa only [homMk_right, T.map_preimage, ← w m] using! (Category.id_comp _).symm

Depends on / 依赖: T.preimage, U.isLimitPowerFan, WidePullbackCone, WidePullbackCone.isLimitOfFan, c.pt.hom, isLimitOfFan, isLimitPowerFan, isTerminalIncl, preimage
-/
noncomputable def mkIdInitial [T.Full] [T.Faithful] : IsInitial (mk (𝟙 (T.obj Y))) where
  desc c := homMk (T.preimage c.pt.hom)
  uniq c m _ := by
    apply CommaMorphism.ext
    · simp
    · apply T.map_injective
      simpa only [homMk_right, T.map_preimage, ← w m] using! (Category.id_comp _).symm

variable {A : Type u₃} [Category.{v₃} A] {B : Type u₄} [Category.{v₄} B]

/-- The functor `(S, F ⋙ G) ⥤ (S, G)`. -/
@[simps!, implicit_reducible]
/--
Definition of `pre` / `pre` 的定义

English:
definition pre
  signature: (S : D) (F : B ⥤ C) (G : C ⥤ D)
  body: Comma.preRight _ F G

中文:
定义 pre
  签名: (S : D) (F : B ⥤ C) (G : C ⥤ D)
  定义体: Comma.preRight _ F G

Depends on / 依赖: Comma.preRight, preRight
-/
def pre (S : D) (F : B ⥤ C) (G : C ⥤ D) : StructuredArrow S (F ⋙ G) ⥤ StructuredArrow S G :=
  Comma.preRight _ F G

instance (S : D) (F : B ⥤ C) (G : C ⥤ D) [F.Faithful] : (pre S F G).Faithful :=
  show (Comma.preRight _ _ _).Faithful from inferInstance

instance (S : D) (F : B ⥤ C) (G : C ⥤ D) [F.Full] : (pre S F G).Full :=
  show (Comma.preRight _ _ _).Full from inferInstance

instance (S : D) (F : B ⥤ C) (G : C ⥤ D) [F.EssSurj] : (pre S F G).EssSurj :=
  show (Comma.preRight _ _ _).EssSurj from inferInstance

/--
Instance `isEquivalence_pre` / 实例 `isEquivalence_pre`

English:
instance isEquivalence_pre
  signature: (S : D) (F : B ⥤ C) (G : C ⥤ D) [F.IsEquivalence]
  body: Comma.isEquivalence_preRight _ _ _

中文:
实例 isEquivalence_pre
  签名: (S : D) (F : B ⥤ C) (G : C ⥤ D) [F.是等价]
  定义体: Comma.isEquivalence_preRight _ _ _

Depends on / 依赖: Comma.isEquivalence_preRight, isEquivalence_preRight
-/
instance isEquivalence_pre (S : D) (F : B ⥤ C) (G : C ⥤ D) [F.IsEquivalence] :
    (pre S F G).IsEquivalence :=
  Comma.isEquivalence_preRight _ _ _

set_option backward.defeqAttrib.useBackward true in
/-- The functor `(S, F) ⥤ (G(S), F ⋙ G)`. -/
@[simps]
/--
Definition of `post` / `post` 的定义

English:
definition post
  signature: (S : C) (F : B ⥤ C) (G : C ⥤ D)
  body: StructuredArrow.mk (G.map X.hom)
  map f := StructuredArrow.homMk f.right (by simp [← Functor.map_comp])

中文:
定义 post
  签名: (S : C) (F : B ⥤ C) (G : C ⥤ D)
  定义体: StructuredArrow.mk (G.map X.hom)
  map f := StructuredArrow.homMk f.right (by simp [← Functor.map_comp])

Depends on / 依赖: G.map, StructuredArrow, StructuredArrow.mk, X.hom
-/
def post (S : C) (F : B ⥤ C) (G : C ⥤ D) :
    StructuredArrow S F ⥤ StructuredArrow (G.obj S) (F ⋙ G) where
  obj X := StructuredArrow.mk (G.map X.hom)
  map f := StructuredArrow.homMk f.right (by simp [← Functor.map_comp])

set_option backward.defeqAttrib.useBackward true in
instance (S : C) (F : B ⥤ C) (G : C ⥤ D) : (post S F G).Faithful where
  map_injective {_ _} _ _ h := by simpa [ext_iff] using h

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
instance (S : C) (F : B ⥤ C) (G : C ⥤ D) [G.Faithful] : (post S F G).Full where
  map_surjective f := ⟨homMk f.right (G.map_injective (by simpa using f.w)), by simp⟩

set_option backward.defeqAttrib.useBackward true in
instance (S : C) (F : B ⥤ C) (G : C ⥤ D) [G.Full] : (post S F G).EssSurj where
  mem_essImage h := ⟨mk (G.preimage h.hom), ⟨isoMk (Iso.refl _) (by simp)⟩⟩

/--
Instance `isEquivalence_post` / 实例 `isEquivalence_post`

English:
instance isEquivalence_post
  signature: (S : C) (F : B ⥤ C) (G : C ⥤ D) [G.Full] [G.Faithful]

中文:
实例 isEquivalence_post
  签名: (S : C) (F : B ⥤ C) (G : C ⥤ D) [G.满] [G.忠实]
-/
instance isEquivalence_post (S : C) (F : B ⥤ C) (G : C ⥤ D) [G.Full] [G.Faithful] :
    (post S F G).IsEquivalence where

section

variable {L : D} {R : C ⥤ D} {L' : B} {R' : A ⥤ B} {F : C ⥤ A} {G : D ⥤ B}
  (α : L' ⟶ G.obj L) (β : R ⋙ G ⟶ F ⋙ R')

/-- The functor `StructuredArrow L R ⥤ StructuredArrow L' R'` that is deduced from
a natural transformation `R ⋙ G ⟶ F ⋙ R'` and a morphism `L' ⟶ G.obj L.` -/
@[simps!, implicit_reducible]
/--
Definition of `map₂` / `map₂` 的定义

English:
definition map₂
  signature: : StructuredArrow L R ⥤ StructuredArrow L' R'
  body: Comma.map (F₁ := 𝟭 (Discrete PUnit)) (Discrete.natTrans (fun _ => α)) β

中文:
定义 map₂
  签名: : 结构化箭头 L R ⥤ 结构化箭头 L' R'
  定义体: Comma.map (F₁ := 𝟭 (Discrete PUnit)) (Discrete.natTrans (fun _ => α)) β

Depends on / 依赖: Comma.map, Discrete, Discrete.natTrans, natTrans
-/
def map₂ : StructuredArrow L R ⥤ StructuredArrow L' R' :=
  Comma.map (F₁ := 𝟭 (Discrete PUnit)) (Discrete.natTrans (fun _ => α)) β

/--
Instance `faithful_map₂` / 实例 `faithful_map₂`

English:
instance faithful_map₂
  signature: [F.Faithful]
  body: by
  apply Comma.faithful_map

中文:
实例 faithful_map₂
  签名: [F.忠实]
  定义体: by
  apply Comma.faithful_map

Depends on / 依赖: Comma.faithful_map, faithful_map
-/
instance faithful_map₂ [F.Faithful] : (map₂ α β).Faithful := by
  apply Comma.faithful_map

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `full_map₂` / 实例 `full_map₂`

English:
instance full_map₂
  signature: [G.Faithful] [F.Full] [IsIso α] [IsIso β]
  body: by
  apply Comma.full_map

中文:
实例 full_map₂
  签名: [G.忠实] [F.满] [是同构 α] [是同构 β]
  定义体: by
  apply Comma.full_map

Depends on / 依赖: Comma.full_map, full_map
-/
instance full_map₂ [G.Faithful] [F.Full] [IsIso α] [IsIso β] : (map₂ α β).Full := by
  apply Comma.full_map

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `essSurj_map₂` / 实例 `essSurj_map₂`

English:
instance essSurj_map₂
  signature: [F.EssSurj] [G.Full] [IsIso α] [IsIso β]
  body: by
  apply Comma.essSurj_map

中文:
实例 essSurj_map₂
  签名: [F.本质满射] [G.满] [是同构 α] [是同构 β]
  定义体: by
  apply Comma.essSurj_map

Depends on / 依赖: Comma.essSurj_map, essSurj_map
-/
instance essSurj_map₂ [F.EssSurj] [G.Full] [IsIso α] [IsIso β] : (map₂ α β).EssSurj := by
  apply Comma.essSurj_map

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `isEquivalenceMap₂` / 实例 `isEquivalenceMap₂`

English:
instance isEquivalenceMap₂
  body: by
  apply Comma.isEquivalenceMap

中文:
实例 isEquivalenceMap₂
  定义体: by
  apply Comma.isEquivalenceMap

Depends on / 依赖: Comma.isEquivalenceMap, isEquivalenceMap
-/
noncomputable instance isEquivalenceMap₂
    [F.IsEquivalence] [G.Faithful] [G.Full] [IsIso α] [IsIso β] :
    (map₂ α β).IsEquivalence := by
  apply Comma.isEquivalenceMap

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The composition of two applications of `map₂` is naturally isomorphic to a single such one. -/
@[simps!]
/--
Definition of `map₂CompMap₂Iso` / `map₂CompMap₂Iso` 的定义

English:
definition map₂CompMap₂Iso
  signature: {C' : Type u₆} [Category.{v₆} C'] {D' : Type u₅} [Category.{v₅} D']
  body: NatIso.ofComponents (fun X => isoMk (Iso.refl _))

中文:
定义 map₂CompMap₂Iso
  签名: {C' : 类型u₆} [范畴.{v₆} C'] {D' : 类型u₅} [范畴.{v₅} D']
  定义体: NatIso.ofComponents (fun X => isoMk (Iso.refl _))

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def map₂CompMap₂Iso {C' : Type u₆} [Category.{v₆} C'] {D' : Type u₅} [Category.{v₅} D']
    {L'' : D'} {R'' : C' ⥤ D'} {F' : C' ⥤ C} {G' : D' ⥤ D} (α' : L ⟶ G'.obj L'')
    (β' : R'' ⋙ G' ⟶ F' ⋙ R) :
    map₂ α' β' ⋙ map₂ α β ≅
    map₂ (α ≫ G.map α')
      ((Functor.associator ..).inv ≫ Functor.whiskerRight β' _ ≫ (Functor.associator ..).hom ≫
        Functor.whiskerLeft _ β ≫ (Functor.associator ..).inv) :=
  NatIso.ofComponents (fun X => isoMk (Iso.refl _))

set_option backward.defeqAttrib.useBackward true in
/-- `map₂` is invariant under isomorphisms. -/
@[simps!]
/--
Definition of `map₂Congr` / `map₂Congr` 的定义

English:
definition map₂Congr
  signature: {F' : C ⥤ A} {G' : D ⥤ B} (e₁ : F ≅ F') (e₂ : G ≅ G')
  body: NatIso.ofComponents (fun X => isoMk (e₁.app X.right) ?_) ?_

中文:
定义 map₂Congr
  签名: {F' : C ⥤ A} {G' : D ⥤ B} (e₁ : F ≅ F') (e₂ : G ≅ G')
  定义体: NatIso.ofComponents (fun X => isoMk (e₁.app X.right) ?_) ?_

Depends on / 依赖: Functor, Functor.whiskerLeft, Functor.whiskerRight, NatIso, NatIso.ofComponents, X.right, cat_disch, ofComponents, whiskerLeft, whiskerRight
-/
def map₂Congr {F' : C ⥤ A} {G' : D ⥤ B} (e₁ : F ≅ F') (e₂ : G ≅ G')
    (α' : L' ⟶ G'.obj L) (β' : R ⋙ G' ⟶ F' ⋙ R')
    (hα : α = α' ≫ e₂.inv.app _ := by cat_disch)
    (hβ : β ≫ Functor.whiskerRight e₁.hom _ = Functor.whiskerLeft _ e₂.hom ≫ β' := by cat_disch) :
    map₂ α β ≅ map₂ α' β' :=
  NatIso.ofComponents (fun X => isoMk (e₁.app X.right) ?_) ?_
where finally
  · subst hα
    simp [dsimp% congr($(hβ).app X.right)]
  · simp

set_option backward.defeqAttrib.useBackward true in
/-- `map₂` of the identity is the identity. -/
@[simps!]
/--
Definition of `map₂IdIso` / `map₂IdIso` 的定义

English:
definition map₂IdIso
  signature: (T : D) (α : T ⟶ (𝟭 _).obj T) (β : R ⋙ 𝟭 _ ⟶ 𝟭 _ ⋙ R)
  body: NatIso.ofComponents (fun X => isoMk (.refl _))

中文:
定义 map₂IdIso
  签名: (T : D) (α : T ⟶ (𝟭 _).obj T) (β : R ⋙ 𝟭 _ ⟶ 𝟭 _ ⋙ R)
  定义体: NatIso.ofComponents (fun X => isoMk (.refl _))

Depends on / 依赖: Functor, Functor.leftUnitor, Functor.rightUnitor, NatIso, NatIso.ofComponents, cat_disch, leftUnitor, ofComponents, rightUnitor
-/
def map₂IdIso (T : D) (α : T ⟶ (𝟭 _).obj T) (β : R ⋙ 𝟭 _ ⟶ 𝟭 _ ⋙ R)
    (hα : α = 𝟙 _ := by cat_disch)
    (hβ : β = (Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv := by cat_disch) :
    map₂ α β ≅ 𝟭 _ :=
  NatIso.ofComponents (fun X => isoMk (.refl _))

set_option backward.defeqAttrib.useBackward true in
/-- `map₂` along equivalences of categories is an equivalence of categories. -/
@[simps]
/--
Definition of `map₂Iso` / `map₂Iso` 的定义

English:
definition map₂Iso
  signature: {F : C ≌ A} {G : D ≌ B}
  body: map₂ α β
  inverse := map₂ α' β'
  unitIso := (map₂IdIso _ _ _ rfl rfl).symm ≪≫ map₂Congr _ _ F.unitIso G.unitIso _ _ ?_ ?_ ≪≫
    (map₂CompMap₂Iso ..).symm
  counitIso := map₂CompMap₂Iso .. ≪≫
    map₂Congr _ _ F.counitIso G.counitIso _ _ ?_ ?_ ≪≫ map₂IdIso _ _ _ rfl rfl
  functor_unitIso_comp := ?_

中文:
定义 map₂Iso
  签名: {F : C ≌ A} {G : D ≌ B}
  定义体: map₂ α β
  inverse := map₂ α' β'
  unitIso := (map₂IdIso _ _ _ rfl rfl).symm ≪≫ map₂Congr _ _ F.unitIso G.unitIso _ _ ?_ ?_ ≪≫
    (map₂CompMap₂Iso ..).symm
  counitIso := map₂CompMap₂Iso .. ≪≫
    map₂Congr _ _ F.counitIso G.counitIso _ _ ?_ ?_ ≪≫ map₂IdIso _ _ _ rfl rfl
  functor_unitIso_comp := ?_
-/
def map₂Iso {F : C ≌ A} {G : D ≌ B}
    (α : L' ⟶ G.functor.obj L) (α' : L ⟶ G.inverse.obj L')
    (β : R ⋙ G.functor ⟶ F.functor ⋙ R') (β' : R' ⋙ G.inverse ⟶ F.inverse ⋙ R)
    (hαα' : α ≫ G.functor.map α' = G.counitIso.inv.app _)
    (hα'α : α' ≫ G.inverse.map α = G.unitIso.hom.app _)
    (hββ' :
      (Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv ≫
        Functor.whiskerRight F.unitIso.hom _ ≫ (Functor.associator ..).hom =
        Functor.whiskerLeft R G.unitIso.hom ≫ (Functor.associator ..).inv ≫
        Functor.whiskerRight β _ ≫
        (Functor.associator ..).hom ≫ Functor.whiskerLeft _ β')
    (hβ'β :
      Functor.whiskerRight β' G.functor ≫ (Functor.associator ..).hom ≫
        Functor.whiskerLeft _ β ≫ (Functor.associator ..).inv ≫
        Functor.whiskerRight F.counitIso.hom _ =
        (Functor.associator ..).hom ≫ Functor.whiskerLeft _ G.counitIso.hom ≫
        (Functor.rightUnitor _).hom ≫ (Functor.leftUnitor _).inv) :
    StructuredArrow L R ≌ StructuredArrow L' R' where
  functor := map₂ α β
  inverse := map₂ α' β'
  unitIso := (map₂IdIso _ _ _ rfl rfl).symm ≪≫ map₂Congr _ _ F.unitIso G.unitIso _ _ ?_ ?_ ≪≫
    (map₂CompMap₂Iso ..).symm
  counitIso := map₂CompMap₂Iso .. ≪≫
    map₂Congr _ _ F.counitIso G.counitIso _ _ ?_ ?_ ≪≫ map₂IdIso _ _ _ rfl rfl
  functor_unitIso_comp := ?_
where finally
  · simp [reassoc_of% hα'α]
  · ext X
    simpa using congr($(hββ').app X)
  · simp [hαα']
  · ext X
    simpa using congr($(hβ'β).app X)
  · simp [map₂Congr]

end

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `postIsoMap₂` / `postIsoMap₂` 的定义

English:
definition postIsoMap₂
  signature: (S : C) (F : B ⥤ C) (G : C ⥤ D)
  body: NatIso.ofComponents fun _ => isoMk Iso.refl _

中文:
定义 postIsoMap₂
  签名: (S : C) (F : B ⥤ C) (G : C ⥤ D)
  定义体: NatIso.ofComponents fun _ => isoMk Iso.refl _
-/
def postIsoMap₂ (S : C) (F : B ⥤ C) (G : C ⥤ D) :
    post S F G ≅ map₂ (F := 𝟭 _) (𝟙 _) (𝟙 (F ⋙ G)) :=
NatIso.ofComponents fun _ => isoMk Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `mapIsoMap₂` / `mapIsoMap₂` 的定义

English:
definition mapIsoMap₂
  signature: {S S' : D} (f : S ⟶ S')
  body: NatIso.ofComponents fun _ => isoMk Iso.refl _

中文:
定义 mapIsoMap₂
  签名: {S S' : D} (f : S ⟶ S')
  定义体: NatIso.ofComponents fun _ => isoMk Iso.refl _
-/
def mapIsoMap₂ {S S' : D} (f : S ⟶ S') : map (T := T) f ≅ map₂ (F := 𝟭 _) (G := 𝟭 _) f (𝟙 T) :=
NatIso.ofComponents fun _ => isoMk Iso.refl _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `preIsoMap₂` / `preIsoMap₂` 的定义

English:
definition preIsoMap₂
  signature: (S : D) (F : B ⥤ C) (G : C ⥤ D)
  body: NatIso.ofComponents fun _ => isoMk Iso.refl _

中文:
定义 preIsoMap₂
  签名: (S : D) (F : B ⥤ C) (G : C ⥤ D)
  定义体: NatIso.ofComponents fun _ => isoMk Iso.refl _
-/
def preIsoMap₂ (S : D) (F : B ⥤ C) (G : C ⥤ D) :
    pre S F G ≅ map₂ (G := 𝟭 _) (𝟙 _) (𝟙 (F ⋙ G)) :=
NatIso.ofComponents fun _ => isoMk Iso.refl _

/--
Definition of `IsUniversal` / `IsUniversal` 的定义

English:
abbreviation IsUniversal
  signature: (f : StructuredArrow S T)
  body: IsInitial f

中文:
缩写 是泛
  签名: (f : 结构化箭头 S T)
  定义体: IsInitial f

Depends on / 依赖: IsInitial
-/
abbrev IsUniversal (f : StructuredArrow S T) := IsInitial f

namespace IsUniversal

variable {f g : StructuredArrow S T}

/--
theorem `uniq` / 定理 `uniq`

English:
theorem uniq
  given: (h : IsUniversal f) (η : f ⟶ g)
  statement: η = h.to g
  proof: h.hom_ext η (h.to g)

中文:
定理 uniq
  条件: (h : 是泛 f) (η : f ⟶ g)
  结论: η = h.to g
  证明: h.hom_ext η (h.to g)

Depends on / 依赖: h.hom_ext, h.to, hom_ext
-/
theorem uniq (h : IsUniversal f) (η : f ⟶ g) : η = h.to g :=
  h.hom_ext η (h.to g)

/--
Definition of `desc` / `desc` 的定义

English:
definition desc
  signature: (h : IsUniversal f) (g : StructuredArrow S T)
  body: (h.to g).right

中文:
定义 desc
  签名: (h : 是泛 f) (g : 结构化箭头 S T)
  定义体: (h.to g).right

Depends on / 依赖: h.to
-/
def desc (h : IsUniversal f) (g : StructuredArrow S T) : f.right ⟶ g.right :=
  (h.to g).right

/-- Any structured arrow factors through a universal arrow. -/
@[reassoc (attr := simp)]
/--
theorem `fac` / 定理 `fac`

English:
theorem fac
  given: (h : IsUniversal f) (g : StructuredArrow S T)
  proof: (h.to g).w

中文:
定理 fac
  条件: (h : 是泛 f) (g : 结构化箭头 S T)
  证明: (h.to g).w

Depends on / 依赖: h.to
-/
theorem fac (h : IsUniversal f) (g : StructuredArrow S T) :
    f.hom ≫ T.map (h.desc g) = g.hom :=
  (h.to g).w

/--
theorem `hom_desc` / 定理 `hom_desc`

English:
theorem hom_desc
  given: (h : IsUniversal f) {c : C} (η : f.right ⟶ c)
  proof: let g := mk f.hom ≫ T.map η
  congrArg CommaMorphism.right (h.hom_ext (homMk η rfl : f ⟶ g) (h.to g))

中文:
定理 hom_desc
  条件: (h : 是泛 f) {c : C} (η : f.right ⟶ c)
  证明: let g := mk f.hom ≫ T.map η
  congrArg CommaMorphism.right (h.hom_ext (homMk η rfl : f ⟶ g) (h.to g))

Depends on / 依赖: CommaMorphism, CommaMorphism.right, T.map, f.hom, h.hom_ext, h.to, hom_ext
-/
theorem hom_desc (h : IsUniversal f) {c : C} (η : f.right ⟶ c) :
    η = h.desc (mk <| f.hom ≫ T.map η) :=
let g := mk f.hom ≫ T.map η
  congrArg CommaMorphism.right (h.hom_ext (homMk η rfl : f ⟶ g) (h.to g))

/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  statement: (h : IsUniversal f) {c : C} {η η' : f.right ⟶ c}
  proof: by
  rw [h.hom_desc η]; rw [h.hom_desc η']; rw [w]

中文:
定理 hom_ext
  结论: (h : 是泛 f) {c : C} {η η' : f.right ⟶ c}
  证明: by
  rw [h.hom_desc η]; rw [h.hom_desc η']; rw [w]

Depends on / 依赖: h.hom_desc, hom_desc
-/
theorem hom_ext (h : IsUniversal f) {c : C} {η η' : f.right ⟶ c}
    (w : f.hom ≫ T.map η = f.hom ≫ T.map η') : η = η' := by
  rw [h.hom_desc η]; rw [h.hom_desc η']; rw [w]

/--
theorem `existsUnique` / 定理 `existsUnique`

English:
theorem existsUnique
  given: (h : IsUniversal f) (g : StructuredArrow S T)
  proof: ⟨h.desc g, h.fac g, fun f w => h.hom_ext by simp [w]⟩

中文:
定理 存在Unique
  条件: (h : 是泛 f) (g : 结构化箭头 S T)
  证明: ⟨h.desc g, h.fac g, fun f w => h.hom_ext by simp [w]⟩

Depends on / 依赖: h.desc, h.fac, h.hom_ext, hom_ext
-/
theorem existsUnique (h : IsUniversal f) (g : StructuredArrow S T) :
    exists! η : f.right ⟶ g.right, f.hom ≫ T.map η = g.hom :=
⟨h.desc g, h.fac g, fun f w => h.hom_ext by simp [w]⟩

end IsUniversal

end StructuredArrow

/-- The category of `S`-costructured arrows with target `T : D` (here `S : C ⥤ D`),
has as its objects `D`-morphisms of the form `S Y ⟶ T`, for some `Y : C`,
and morphisms `C`-morphisms `Y ⟶ Y'` making the obvious triangle commute.
-/
-- We explicitly come from `PUnit.{1}` here to obtain the correct universe for morphisms of
-- costructured arrows.
@[implicit_reducible]
/--
Definition of `CostructuredArrow` / `CostructuredArrow` 的定义

English:
definition CostructuredArrow
  signature: (S : C ⥤ D) (T : D)
  body: Comma S (Functor.fromPUnit.{0} T)

中文:
定义 CostructuredArrow
  签名: (S : C ⥤ D) (T : D)
  定义体: Comma S (Functor.fromPUnit.{0} T)

Depends on / 依赖: Functor, Functor.fromPUnit, fromPUnit
-/
def CostructuredArrow (S : C ⥤ D) (T : D) :=
  Comma S (Functor.fromPUnit.{0} T)

/--
Definition of `CostructuredArrow.Hom` / `CostructuredArrow.Hom` 的定义

English:
definition CostructuredArrow.Hom
  signature: {S : C ⥤ D} {T : D}
  body: CommaMorphism f g

中文:
定义 CostructuredArrow.态射
  签名: {S : C ⥤ D} {T : D}
  定义体: CommaMorphism f g

Depends on / 依赖: hasLimitCompEvaluation
-/
protected def CostructuredArrow.Hom {S : C ⥤ D} {T : D}
    (f g : CostructuredArrow S T) := CommaMorphism f g

instance {S : C ⥤ D} {T : D} : Category (CostructuredArrow S T) where
  Hom := CostructuredArrow.Hom
  __ := (inferInstance : Category (Comma _ _))

instance (S : C ⥤ D) (T : D) : Category (CostructuredArrow S T) := commaCategory

namespace CostructuredArrow

section

variable {S : C ⥤ D} {T : D}

/--
Definition of `left` / `left` 的定义

English:
abbreviation left
  signature: (X : CostructuredArrow S T)
  body: Comma.left X

中文:
缩写 left
  签名: (X : CostructuredArrow S T)
  定义体: Comma.left X

Depends on / 依赖: Comma.left
-/
abbrev left (X : CostructuredArrow S T) : C := Comma.left X

/--
Definition of `hom` / `hom` 的定义

English:
abbreviation hom
  signature: (X : CostructuredArrow S T)
  body: Comma.hom X

中文:
缩写 hom
  签名: (X : CostructuredArrow S T)
  定义体: Comma.hom X

Depends on / 依赖: Comma.hom
-/
abbrev hom (X : CostructuredArrow S T) : S.obj X.left ⟶ T := Comma.hom X

variable {X Y : CostructuredArrow S T} (f : X ⟶ Y)

/--
Definition of `Hom.left` / `Hom.left` 的定义

English:
abbreviation Hom.left
  signature: : X.left ⟶ Y.left
  body: CommaMorphism.left f

#adaptation_note

中文:
缩写 态射.left
  签名: : X.left ⟶ Y.left
  定义体: CommaMorphism.left f

#adaptation_note
-/
abbrev Hom.left : X.left ⟶ Y.left := CommaMorphism.left f

#adaptation_note
/--
The combination of `implicitBump` and making `Functor.const` implicit-reducible makes this former
`simp` lemma redundant, so no `simp` annotation.
-/
@[reassoc]
/--
theorem `w` / 定理 `w`

English:
theorem w
  given: (f : X ⟶ Y)
  statement: S.map f.left ≫ Y.hom = X.hom
  proof: by
  simp

@[reassoc]

中文:
定理 w
  条件: (f : X ⟶ Y)
  结论: S.map f.left ≫ Y.hom = X.hom
  证明: by
  simp

@[reassoc]
-/
theorem w (f : X ⟶ Y) : S.map f.left ≫ Y.hom = X.hom := by
  simp

@[reassoc]
/--
theorem `Hom.w` / 定理 `Hom.w`

English:
theorem Hom.w
  given: (f : X ⟶ Y)
  statement: S.map f.left ≫ Y.hom = X.hom
  proof: CostructuredArrow.w f

中文:
定理 态射.w
  条件: (f : X ⟶ Y)
  结论: S.map f.left ≫ Y.hom = X.hom
  证明: CostructuredArrow.w f
-/
theorem Hom.w (f : X ⟶ Y) : S.map f.left ≫ Y.hom = X.hom := CostructuredArrow.w f

end


/-- The obvious projection functor from costructured arrows. -/
@[simps!]
/--
Definition of `proj` / `proj` 的定义

English:
definition proj
  signature: (S : C ⥤ D) (T : D)
  body: Comma.fst _ _

中文:
定义 proj
  签名: (S : C ⥤ D) (T : D)
  定义体: Comma.fst _ _

Depends on / 依赖: Comma.fst
-/
def proj (S : C ⥤ D) (T : D) : CostructuredArrow S T ⥤ C :=
  Comma.fst _ _

variable {T T' T'' : D} {Y Y' Y'' : C} {S S' : C ⥤ D}

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {X Y : CostructuredArrow S T} (f g : X ⟶ Y) (h : f.left = g.left)
  statement: f = g
  proof: CommaMorphism.ext h (Subsingleton.elim _ _)

@[simp]

中文:
引理 hom_ext
  条件: {X Y : CostructuredArrow S T} (f g : X ⟶ Y) (h : f.left = g.left)
  结论: f = g
  证明: CommaMorphism.ext h (Subsingleton.elim _ _)

@[simp]

Depends on / 依赖: CommaMorphism, CommaMorphism.ext, Subsingleton, Subsingleton.elim
-/
lemma hom_ext {X Y : CostructuredArrow S T} (f g : X ⟶ Y) (h : f.left = g.left) : f = g :=
  CommaMorphism.ext h (Subsingleton.elim _ _)

@[simp]
/--
theorem `hom_eq_iff` / 定理 `hom_eq_iff`

English:
theorem hom_eq_iff
  given: {X Y : CostructuredArrow S T} (f g : X ⟶ Y)
  statement: f = g ↔ f.left = g.left
  proof: ⟨fun h => by rw [h], hom_ext _ _⟩

中文:
定理 hom_eq_iff
  条件: {X Y : CostructuredArrow S T} (f g : X ⟶ Y)
  结论: f = g ↔ f.left = g.left
  证明: ⟨fun h => by rw [h], hom_ext _ _⟩

Depends on / 依赖: hom_ext
-/
theorem hom_eq_iff {X Y : CostructuredArrow S T} (f g : X ⟶ Y) : f = g ↔ f.left = g.left :=
  ⟨fun h => by rw [h], hom_ext _ _⟩

/-- Construct a costructured arrow from a morphism. -/
@[implicit_reducible]
/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: (f : S.obj Y ⟶ T)
  body: ⟨Y, ⟨⟨⟩⟩, f⟩

@[simp]

中文:
定义 mk
  签名: (f : S.obj Y ⟶ T)
  定义体: ⟨Y, ⟨⟨⟩⟩, f⟩

@[simp]
-/
def mk (f : S.obj Y ⟶ T) : CostructuredArrow S T :=
  ⟨Y, ⟨⟨⟩⟩, f⟩

@[simp]
/--
theorem `mk_left` / 定理 `mk_left`

English:
theorem mk_left
  given: (f : S.obj Y ⟶ T)
  statement: (mk f).left = Y
  proof: rfl

@[simp]

中文:
定理 mk_left
  条件: (f : S.obj Y ⟶ T)
  结论: (mk f).left = Y
  证明: rfl

@[simp]
-/
theorem mk_left (f : S.obj Y ⟶ T) : (mk f).left = Y :=
  rfl

@[simp]
/--
theorem `mk_right` / 定理 `mk_right`

English:
theorem mk_right
  given: (f : S.obj Y ⟶ T)
  statement: (mk f).right = ⟨⟨⟩⟩
  proof: rfl

@[simp]

中文:
定理 mk_right
  条件: (f : S.obj Y ⟶ T)
  结论: (mk f).right = ⟨⟨⟩⟩
  证明: rfl

@[simp]
-/
theorem mk_right (f : S.obj Y ⟶ T) : (mk f).right = ⟨⟨⟩⟩ :=
  rfl

@[simp]
/--
theorem `mk_hom_eq_self` / 定理 `mk_hom_eq_self`

English:
theorem mk_hom_eq_self
  given: (f : S.obj Y ⟶ T)
  statement: (mk f).hom = f
  proof: rfl

@[simp, reassoc]

中文:
定理 mk_hom_eq_self
  条件: (f : S.obj Y ⟶ T)
  结论: (mk f).hom = f
  证明: rfl

@[simp, reassoc]
-/
theorem mk_hom_eq_self (f : S.obj Y ⟶ T) : (mk f).hom = f :=
  rfl

@[simp, reassoc]
/--
theorem `comp_left` / 定理 `comp_left`

English:
theorem comp_left
  given: {X Y Z : CostructuredArrow S T} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

@[simp]

中文:
定理 comp_left
  条件: {X Y Z : CostructuredArrow S T} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl

@[simp]
-/
theorem comp_left {X Y Z : CostructuredArrow S T} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).left = f.left ≫ g.left := rfl

@[simp]
/--
theorem `id_left` / 定理 `id_left`

English:
theorem id_left
  given: (X : CostructuredArrow S T)
  statement: (𝟙 X : X ⟶ X).left = 𝟙 X.left
  proof: rfl

@[simp]

中文:
定理 id_left
  条件: (X : CostructuredArrow S T)
  结论: (𝟙 X : X ⟶ X).left = 𝟙 X.left
  证明: rfl

@[simp]
-/
theorem id_left (X : CostructuredArrow S T) : (𝟙 X : X ⟶ X).left = 𝟙 X.left := rfl

@[simp]
/--
theorem `eqToHom_left` / 定理 `eqToHom_left`

English:
theorem eqToHom_left
  given: {X Y : CostructuredArrow S T} (h : X = Y)
  proof: by
  subst h
  simp only [eqToHom_refl, id_left]

@[simp]

中文:
定理 eqToHom_left
  条件: {X Y : CostructuredArrow S T} (h : X = Y)
  证明: by
  subst h
  simp only [eqToHom_refl, id_left]

@[simp]

Depends on / 依赖: eqToHom_refl, id_left
-/
theorem eqToHom_left {X Y : CostructuredArrow S T} (h : X = Y) :
    (eqToHom h).left = eqToHom (by rw [h]) := by
  subst h
  simp only [eqToHom_refl, id_left]

@[simp]
/--
theorem `right_eq_id` / 定理 `right_eq_id`

English:
theorem right_eq_id
  given: {X Y : CostructuredArrow S T} (f : X ⟶ Y)
  statement: f.right = 𝟙 X.right
  proof: rfl

中文:
定理 right_eq_id
  条件: {X Y : CostructuredArrow S T} (f : X ⟶ Y)
  结论: f.right = 𝟙 X.right
  证明: rfl
-/
theorem right_eq_id {X Y : CostructuredArrow S T} (f : X ⟶ Y) : f.right = 𝟙 X.right := rfl

set_option backward.defeqAttrib.useBackward true in
/-- To construct a morphism of costructured arrows,
we need a morphism of the objects underlying the source,
and to check that the triangle commutes.
-/
@[simps! left]
/--
Definition of `homMk` / `homMk` 的定义

English:
definition homMk
  signature: {f f' : CostructuredArrow S T} (g : f.left ⟶ f'.left)
  body: g
  right := 𝟙 f.right

中文:
定义 homMk
  签名: {f f' : CostructuredArrow S T} (g : f.left ⟶ f'.left)
  定义体: g
  right := 𝟙 f.right

Depends on / 依赖: cat_disch, f.right
-/
def homMk {f f' : CostructuredArrow S T} (g : f.left ⟶ f'.left)
    (w : S.map g ≫ f'.hom = f.hom := by cat_disch) : f ⟶ f' where
  left := g
  right := 𝟙 f.right

/--
theorem `homMk_surjective` / 定理 `homMk_surjective`

English:
theorem homMk_surjective
  given: {f f' : CostructuredArrow S T} (φ : f ⟶ f')
  proof: ⟨φ.left, CostructuredArrow.w φ, rfl⟩

中文:
定理 homMk_surjective
  条件: {f f' : CostructuredArrow S T} (φ : f ⟶ f')
  证明: ⟨φ.left, CostructuredArrow.w φ, rfl⟩

Depends on / 依赖: CostructuredArrow, CostructuredArrow.w
-/
theorem homMk_surjective {f f' : CostructuredArrow S T} (φ : f ⟶ f') :
    exists (ψ : f.left ⟶ f'.left) (hψ : S.map ψ ≫ f'.hom = f.hom),
      φ = CostructuredArrow.homMk ψ hψ :=
  ⟨φ.left, CostructuredArrow.w φ, rfl⟩

/-- Given a costructured arrow `S(Y) ⟶ X`, and an arrow `Y' ⟶ Y'`, we can construct a morphism of
costructured arrows given by `(S(Y) ⟶ X) ⟶ (S(Y') ⟶ S(Y) ⟶ X)`. -/
@[simps]
/--
Definition of `homMk'` / `homMk'` 的定义

English:
definition homMk'
  signature: (f : CostructuredArrow S T) (g : Y' ⟶ f.left)
  body: g
  right := 𝟙 _

中文:
定义 homMk'
  签名: (f : CostructuredArrow S T) (g : Y' ⟶ f.left)
  定义体: g
  right := 𝟙 _
-/
def homMk' (f : CostructuredArrow S T) (g : Y' ⟶ f.left) : mk (S.map g ≫ f.hom) ⟶ f where
  left := g
  right := 𝟙 _

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `homMk'_id` / 引理 `homMk'_id`

English:
lemma homMk'_id
  given: (f : CostructuredArrow S T)
  statement: homMk' f (𝟙 f.left) = eqToHom (by cat_disch)
  proof: by
  simp [eqToHom_left]

中文:
引理 homMk'_id
  条件: (f : CostructuredArrow S T)
  结论: homMk' f (𝟙 f.left) = eqToHom (by cat_disch)
  证明: by
  simp [eqToHom_left]
-/
lemma homMk'_id (f : CostructuredArrow S T) : homMk' f (𝟙 f.left) = eqToHom (by cat_disch) := by
  simp [eqToHom_left]

/--
lemma `homMk'_mk_id` / 引理 `homMk'_mk_id`

English:
lemma homMk'_mk_id
  given: (f : S.obj Y ⟶ T)
  statement: homMk' (mk f) (𝟙 Y) = eqToHom (by simp)
  proof: homMk'_id _

中文:
引理 homMk'_mk_id
  条件: (f : S.obj Y ⟶ T)
  结论: homMk' (mk f) (𝟙 Y) = eqToHom (by simp)
  证明: homMk'_id _
-/
lemma homMk'_mk_id (f : S.obj Y ⟶ T) : homMk' (mk f) (𝟙 Y) = eqToHom (by simp) :=
  homMk'_id _

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `homMk'_comp` / 引理 `homMk'_comp`

English:
lemma homMk'_comp
  given: (f : CostructuredArrow S T) (g : Y' ⟶ f.left) (g' : Y'' ⟶ Y')
  proof: by
  simp [eqToHom_left]

中文:
引理 homMk'_comp
  条件: (f : CostructuredArrow S T) (g : Y' ⟶ f.left) (g' : Y'' ⟶ Y')
  证明: by
  simp [eqToHom_left]
-/
lemma homMk'_comp (f : CostructuredArrow S T) (g : Y' ⟶ f.left) (g' : Y'' ⟶ Y') :
    homMk' f (g' ≫ g) = eqToHom (by simp) ≫ homMk' (mk (S.map g ≫ f.hom)) g' ≫ homMk' f g := by
  simp [eqToHom_left]

/--
lemma `homMk'_mk_comp` / 引理 `homMk'_mk_comp`

English:
lemma homMk'_mk_comp
  given: (f : S.obj Y ⟶ T) (g : Y' ⟶ Y) (g' : Y'' ⟶ Y')
  proof: homMk'_comp _ _ _

中文:
引理 homMk'_mk_comp
  条件: (f : S.obj Y ⟶ T) (g : Y' ⟶ Y) (g' : Y'' ⟶ Y')
  证明: homMk'_comp _ _ _
-/
lemma homMk'_mk_comp (f : S.obj Y ⟶ T) (g : Y' ⟶ Y) (g' : Y'' ⟶ Y') :
    homMk' (mk f) (g' ≫ g) = eqToHom (by simp) ≫ homMk' (mk (S.map g ≫ f)) g' ≫ homMk' (mk f) g :=
  homMk'_comp _ _ _

/-- Variant of `homMk'` where both objects are applications of `mk`. -/
@[simps]
/--
Definition of `mkPrecomp` / `mkPrecomp` 的定义

English:
definition mkPrecomp
  signature: (f : S.obj Y ⟶ T) (g : Y' ⟶ Y)
  body: g
  right := 𝟙 _

中文:
定义 mkPrecomp
  签名: (f : S.obj Y ⟶ T) (g : Y' ⟶ Y)
  定义体: g
  right := 𝟙 _
-/
def mkPrecomp (f : S.obj Y ⟶ T) (g : Y' ⟶ Y) : mk (S.map g ≫ f) ⟶ mk f where
  left := g
  right := 𝟙 _

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `mkPrecomp_id` / 引理 `mkPrecomp_id`

English:
lemma mkPrecomp_id
  given: (f : S.obj Y ⟶ T)
  statement: mkPrecomp f (𝟙 Y) = eqToHom (by simp)
  proof: by simp

中文:
引理 mkPrecomp_id
  条件: (f : S.obj Y ⟶ T)
  结论: mkPrecomp f (𝟙 Y) = eqToHom (by simp)
  证明: by simp

Depends on / 依赖: backward, backward.isDefEq.respectTransparency.types, isDefEq, respectTransparency, set_option
-/
lemma mkPrecomp_id (f : S.obj Y ⟶ T) : mkPrecomp f (𝟙 Y) = eqToHom (by simp) := by simp
set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `mkPrecomp_comp` / 引理 `mkPrecomp_comp`

English:
lemma mkPrecomp_comp
  given: (f : S.obj Y ⟶ T) (g : Y' ⟶ Y) (g' : Y'' ⟶ Y')
  proof: by
  simp

中文:
引理 mkPrecomp_comp
  条件: (f : S.obj Y ⟶ T) (g : Y' ⟶ Y) (g' : Y'' ⟶ Y')
  证明: by
  simp
-/
lemma mkPrecomp_comp (f : S.obj Y ⟶ T) (g : Y' ⟶ Y) (g' : Y'' ⟶ Y') :
    mkPrecomp f (g' ≫ g) = eqToHom (by simp) ≫ mkPrecomp (S.map g ≫ f) g' ≫ mkPrecomp f g := by
  simp

set_option backward.defeqAttrib.useBackward true in
/-- To construct an isomorphism of costructured arrows,
we need an isomorphism of the objects underlying the source,
and to check that the triangle commutes.
-/
@[simps! hom_left inv_left]
/--
Definition of `isoMk` / `isoMk` 的定义

English:
definition isoMk
  signature: {f f' : CostructuredArrow S T} (g : f.left ≅ f'.left)
  body: Comma.isoMk g (eqToIso (by ext)) (by simpa using w)

中文:
定义 isoMk
  签名: {f f' : CostructuredArrow S T} (g : f.left ≅ f'.left)
  定义体: Comma.isoMk g (eqToIso (by ext)) (by simpa using w)

Depends on / 依赖: Comma.isoMk, cat_disch, eqToIso
-/
def isoMk {f f' : CostructuredArrow S T} (g : f.left ≅ f'.left)
    (w : S.map g.hom ≫ f'.hom = f.hom := by cat_disch) : f ≅ f' :=
  Comma.isoMk g (eqToIso (by ext)) (by simpa using w)

/--
theorem `obj_ext` / 定理 `obj_ext`

English:
theorem obj_ext
  statement: (x y : CostructuredArrow S T) (hl : x.left = y.left)
  proof: by
  cases x
  cases y
  cases hl
  cat_disch

中文:
定理 obj_ext
  结论: (x y : CostructuredArrow S T) (hl : x.left = y.left)
  证明: by
  cases x
  cases y
  cases hl
  cat_disch

Depends on / 依赖: cat_disch
-/
theorem obj_ext (x y : CostructuredArrow S T) (hl : x.left = y.left)
    (hh : S.map (eqToHom hl) ≫ y.hom = x.hom) : x = y := by
  cases x
  cases y
  cases hl
  cat_disch

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {A B : CostructuredArrow S T} (f g : A ⟶ B) (h : f.left = g.left)
  statement: f = g
  proof: CommaMorphism.ext h (Subsingleton.elim _ _)

中文:
定理 ext
  条件: {A B : CostructuredArrow S T} (f g : A ⟶ B) (h : f.left = g.left)
  结论: f = g
  证明: CommaMorphism.ext h (Subsingleton.elim _ _)

Depends on / 依赖: CommaMorphism, CommaMorphism.ext, Subsingleton, Subsingleton.elim
-/
theorem ext {A B : CostructuredArrow S T} (f g : A ⟶ B) (h : f.left = g.left) : f = g :=
  CommaMorphism.ext h (Subsingleton.elim _ _)

/--
theorem `ext_iff` / 定理 `ext_iff`

English:
theorem ext_iff
  given: {A B : CostructuredArrow S T} (f g : A ⟶ B)
  statement: f = g ↔ f.left = g.left
  proof: ⟨fun h => h ▸ rfl, ext f g⟩

中文:
定理 ext_iff
  条件: {A B : CostructuredArrow S T} (f g : A ⟶ B)
  结论: f = g ↔ f.left = g.left
  证明: ⟨fun h => h ▸ rfl, ext f g⟩
-/
theorem ext_iff {A B : CostructuredArrow S T} (f g : A ⟶ B) : f = g ↔ f.left = g.left :=
  ⟨fun h => h ▸ rfl, ext f g⟩

/--
Instance `proj_faithful` / 实例 `proj_faithful`

English:
instance proj_faithful
  signature: : (proj S T).Faithful where map_injective {_ _}
  body: ext

中文:
实例 proj_faithful
  签名: : (proj S T).忠实 where map_injective {_ _}
  定义体: ext
-/
instance proj_faithful : (proj S T).Faithful where map_injective {_ _} := ext

/--
theorem `mono_of_mono_left` / 定理 `mono_of_mono_left`

English:
theorem mono_of_mono_left
  given: {A B : CostructuredArrow S T} (f : A ⟶ B) [h : Mono f.left]
  statement: Mono f
  proof: (proj S T).mono_of_mono_map h

中文:
定理 mono_of_mono_left
  条件: {A B : CostructuredArrow S T} (f : A ⟶ B) [h : 单态射 f.left]
  结论: 单态射 f
  证明: (proj S T).mono_of_mono_map h

Depends on / 依赖: mono_of_mono_map
-/
theorem mono_of_mono_left {A B : CostructuredArrow S T} (f : A ⟶ B) [h : Mono f.left] : Mono f :=
  (proj S T).mono_of_mono_map h

/--
theorem `epi_of_epi_left` / 定理 `epi_of_epi_left`

English:
theorem epi_of_epi_left
  given: {A B : CostructuredArrow S T} (f : A ⟶ B) [h : Epi f.left]
  statement: Epi f
  proof: (proj S T).epi_of_epi_map h

中文:
定理 epi_of_epi_left
  条件: {A B : CostructuredArrow S T} (f : A ⟶ B) [h : 满态射 f.left]
  结论: 满态射 f
  证明: (proj S T).epi_of_epi_map h

Depends on / 依赖: epi_of_epi_map
-/
theorem epi_of_epi_left {A B : CostructuredArrow S T} (f : A ⟶ B) [h : Epi f.left] : Epi f :=
  (proj S T).epi_of_epi_map h

/--
Instance `mono_homMk` / 实例 `mono_homMk`

English:
instance mono_homMk
  signature: {A B : CostructuredArrow S T} (f : A.left ⟶ B.left) (w) [h : Mono f]
  body: (proj S T).mono_of_mono_map h

中文:
实例 mono_homMk
  签名: {A B : CostructuredArrow S T} (f : A.left ⟶ B.left) (w) [h : 单态射 f]
  定义体: (proj S T).mono_of_mono_map h

Depends on / 依赖: mono_of_mono_map
-/
instance mono_homMk {A B : CostructuredArrow S T} (f : A.left ⟶ B.left) (w) [h : Mono f] :
    Mono (homMk f w) :=
  (proj S T).mono_of_mono_map h

/--
Instance `epi_homMk` / 实例 `epi_homMk`

English:
instance epi_homMk
  signature: {A B : CostructuredArrow S T} (f : A.left ⟶ B.left) (w) [h : Epi f]
  body: (proj S T).epi_of_epi_map h

中文:
实例 epi_homMk
  签名: {A B : CostructuredArrow S T} (f : A.left ⟶ B.left) (w) [h : 满态射 f]
  定义体: (proj S T).epi_of_epi_map h

Depends on / 依赖: epi_of_epi_map
-/
instance epi_homMk {A B : CostructuredArrow S T} (f : A.left ⟶ B.left) (w) [h : Epi f] :
    Epi (homMk f w) :=
  (proj S T).epi_of_epi_map h

/--
theorem `eq_mk` / 定理 `eq_mk`

English:
theorem eq_mk
  given: (f : CostructuredArrow S T)
  statement: f = mk f.hom
  proof: rfl

中文:
定理 eq_mk
  条件: (f : CostructuredArrow S T)
  结论: f = mk f.hom
  证明: rfl
-/
theorem eq_mk (f : CostructuredArrow S T) : f = mk f.hom :=
  rfl

/-- Eta rule for costructured arrows. -/
@[simps! hom_left inv_left]
/--
Definition of `eta` / `eta` 的定义

English:
definition eta
  signature: (f : CostructuredArrow S T)
  body: isoMk (Iso.refl _)

中文:
定义 eta
  签名: (f : CostructuredArrow S T)
  定义体: isoMk (Iso.refl _)

Depends on / 依赖: Iso.refl
-/
def eta (f : CostructuredArrow S T) : f ≅ mk f.hom :=
  isoMk (Iso.refl _)

/--
lemma `mk_surjective` / 引理 `mk_surjective`

English:
lemma mk_surjective
  given: (f : CostructuredArrow S T)
  proof: ⟨_, _, eq_mk f⟩

中文:
引理 mk_surjective
  条件: (f : CostructuredArrow S T)
  证明: ⟨_, _, eq_mk f⟩

Depends on / 依赖: eq_mk
-/
lemma mk_surjective (f : CostructuredArrow S T) :
    exists (Y : C) (g : S.obj Y ⟶ T), f = mk g :=
  ⟨_, _, eq_mk f⟩

/-- A morphism between target objects `T ⟶ T'`
covariantly induces a functor between costructured arrows,
`CostructuredArrow S T ⥤ CostructuredArrow S T'`.

Ideally this would be described as a 2-functor from `D`
(promoted to a 2-category with equations as 2-morphisms)
to `Cat`.
-/
@[simps!, implicit_reducible]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : T ⟶ T')
  body: Comma.mapRight _ ((Functor.const _).map f)

@[simp]

中文:
定义 map
  签名: (f : T ⟶ T')
  定义体: Comma.mapRight _ ((Functor.const _).map f)

@[simp]

Depends on / 依赖: Comma.mapRight, Functor, Functor.const, mapRight
-/
def map (f : T ⟶ T') : CostructuredArrow S T ⥤ CostructuredArrow S T' :=
  Comma.mapRight _ ((Functor.const _).map f)

@[simp]
/--
theorem `map_mk` / 定理 `map_mk`

English:
theorem map_mk
  given: {f : S.obj Y ⟶ T} (g : T ⟶ T')
  statement: (map g).obj (mk f) = mk (f ≫ g)
  proof: rfl

@[simp]

中文:
定理 map_mk
  条件: {f : S.obj Y ⟶ T} (g : T ⟶ T')
  结论: (map g).obj (mk f) = mk (f ≫ g)
  证明: rfl

@[simp]
-/
theorem map_mk {f : S.obj Y ⟶ T} (g : T ⟶ T') : (map g).obj (mk f) = mk (f ≫ g) :=
  rfl

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  given: {f : CostructuredArrow S T}
  statement: (map (𝟙 T)).obj f = f
  proof: by
  rw [eq_mk f]
  simp

@[simp]

中文:
定理 map_id
  条件: {f : CostructuredArrow S T}
  结论: (map (𝟙 T)).obj f = f
  证明: by
  rw [eq_mk f]
  simp

@[simp]

Depends on / 依赖: eq_mk
-/
theorem map_id {f : CostructuredArrow S T} : (map (𝟙 T)).obj f = f := by
  rw [eq_mk f]
  simp

@[simp]
/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  given: {f : T ⟶ T'} {f' : T' ⟶ T''} {h : CostructuredArrow S T}
  proof: by
  rw [eq_mk h]
  simp

#adaptation_note

中文:
定理 map_comp
  条件: {f : T ⟶ T'} {f' : T' ⟶ T''} {h : CostructuredArrow S T}
  证明: by
  rw [eq_mk h]
  simp

#adaptation_note

Depends on / 依赖: eq_mk
-/
theorem map_comp {f : T ⟶ T'} {f' : T' ⟶ T''} {h : CostructuredArrow S T} :
    (map (f ≫ f')).obj h = (map f').obj ((map f).obj h) := by
  rw [eq_mk h]
  simp

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- An isomorphism `T ≅ T'` induces an equivalence
`CostructuredArrow S T ≌ CostructuredArrow S T'`. -/
@[simps!, implicit_reducible]
/--
Definition of `mapIso` / `mapIso` 的定义

English:
definition mapIso
  signature: (i : T ≅ T')
  body: Comma.mapRightIso _ ((Functor.const _).mapIso i)

中文:
定义 mapIso
  签名: (i : T ≅ T')
  定义体: Comma.mapRightIso _ ((Functor.const _).mapIso i)

Depends on / 依赖: Comma.mapRightIso, Functor, Functor.const, mapIso, mapRightIso
-/
def mapIso (i : T ≅ T') : CostructuredArrow S T ≌ CostructuredArrow S T' :=
  Comma.mapRightIso _ ((Functor.const _).mapIso i)

/-- A natural isomorphism `S ≅ S'` induces an equivalence
`CostrucutredArrow S T ≌ CostructuredArrow S' T`. -/
@[simps!, implicit_reducible]
/--
Definition of `mapNatIso` / `mapNatIso` 的定义

English:
definition mapNatIso
  signature: (i : S ≅ S')
  body: Comma.mapLeftIso _ i

中文:
定义 map自然数Iso
  签名: (i : S ≅ S')
  定义体: Comma.mapLeftIso _ i

Depends on / 依赖: Comma.mapLeftIso, mapLeftIso
-/
def mapNatIso (i : S ≅ S') : CostructuredArrow S T ≌ CostructuredArrow S' T :=
  Comma.mapLeftIso _ i

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `proj_reflectsIsomorphisms` / 实例 `proj_reflectsIsomorphisms`

English:
instance proj_reflectsIsomorphisms
  signature: : (proj S T).ReflectsIsomorphisms where
  body: ⟨CostructuredArrow.homMk (inv ((proj S T).map f) :), by simp⟩

中文:
实例 proj_reflectsIsomorphisms
  签名: : (proj S T).反映同构 where
  定义体: ⟨CostructuredArrow.homMk (inv ((proj S T).map f) :), by simp⟩

Depends on / 依赖: CostructuredArrow, CostructuredArrow.homMk
-/
instance proj_reflectsIsomorphisms : (proj S T).ReflectsIsomorphisms where
  reflects f t := ⟨CostructuredArrow.homMk (inv ((proj S T).map f) :), by simp⟩

open CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `mkIdTerminal` / `mkIdTerminal` 的定义

English:
definition mkIdTerminal
  signature: [S.Full] [S.Faithful]
  body: homMk (S.preimage c.pt.hom)
  uniq := by
    rintro c m -
    ext
    apply S.map_injective
    simpa only [homMk_left, S.map_preimage, ← w m] using! (Category.comp_id _).symm

中文:
定义 mkIdTerminal
  签名: [S.满] [S.忠实]
  定义体: homMk (S.preimage c.pt.hom)
  uniq := by
    rintro c m -
    ext
    apply S.map_injective
    simpa only [homMk_left, S.map_preimage, ← w m] using! (Category.comp_id _).symm

Depends on / 依赖: S.preimage, c.pt.hom, preimage
-/
noncomputable def mkIdTerminal [S.Full] [S.Faithful] : IsTerminal (mk (𝟙 (S.obj Y))) where
  lift c := homMk (S.preimage c.pt.hom)
  uniq := by
    rintro c m -
    ext
    apply S.map_injective
    simpa only [homMk_left, S.map_preimage, ← w m] using! (Category.comp_id _).symm

variable {A : Type u₃} [Category.{v₃} A] {B : Type u₄} [Category.{v₄} B]

/-- The functor `(F ⋙ G, S) ⥤ (G, S)`. -/
@[simps!, implicit_reducible]
/--
Definition of `pre` / `pre` 的定义

English:
definition pre
  signature: (F : B ⥤ C) (G : C ⥤ D) (S : D)
  body: Comma.preLeft F G _

中文:
定义 pre
  签名: (F : B ⥤ C) (G : C ⥤ D) (S : D)
  定义体: Comma.preLeft F G _

Depends on / 依赖: Comma.preLeft, preLeft
-/
def pre (F : B ⥤ C) (G : C ⥤ D) (S : D) : CostructuredArrow (F ⋙ G) S ⥤ CostructuredArrow G S :=
  Comma.preLeft F G _

instance (F : B ⥤ C) (G : C ⥤ D) (S : D) [F.Faithful] : (pre F G S).Faithful :=
  show (Comma.preLeft _ _ _).Faithful from inferInstance

instance (F : B ⥤ C) (G : C ⥤ D) (S : D) [F.Full] : (pre F G S).Full :=
  show (Comma.preLeft _ _ _).Full from inferInstance

instance (F : B ⥤ C) (G : C ⥤ D) (S : D) [F.EssSurj] : (pre F G S).EssSurj :=
  show (Comma.preLeft _ _ _).EssSurj from inferInstance

/--
Instance `isEquivalence_pre` / 实例 `isEquivalence_pre`

English:
instance isEquivalence_pre
  signature: (F : B ⥤ C) (G : C ⥤ D) (S : D) [F.IsEquivalence]
  body: Comma.isEquivalence_preLeft _ _ _

中文:
实例 isEquivalence_pre
  签名: (F : B ⥤ C) (G : C ⥤ D) (S : D) [F.是等价]
  定义体: Comma.isEquivalence_preLeft _ _ _

Depends on / 依赖: Comma.isEquivalence_preLeft, isEquivalence_preLeft
-/
instance isEquivalence_pre (F : B ⥤ C) (G : C ⥤ D) (S : D) [F.IsEquivalence] :
    (pre F G S).IsEquivalence :=
  Comma.isEquivalence_preLeft _ _ _

set_option backward.defeqAttrib.useBackward true in
/-- The functor `(F, S) ⥤ (F ⋙ G, G(S))`. -/
@[simps]
/--
Definition of `post` / `post` 的定义

English:
definition post
  signature: (F : B ⥤ C) (G : C ⥤ D) (S : C)
  body: CostructuredArrow.mk (G.map X.hom)
  map f := CostructuredArrow.homMk f.left (by simp [← G.map_comp])

中文:
定义 post
  签名: (F : B ⥤ C) (G : C ⥤ D) (S : C)
  定义体: CostructuredArrow.mk (G.map X.hom)
  map f := CostructuredArrow.homMk f.left (by simp [← G.map_comp])

Depends on / 依赖: CostructuredArrow, CostructuredArrow.mk, G.map, X.hom
-/
def post (F : B ⥤ C) (G : C ⥤ D) (S : C) :
    CostructuredArrow F S ⥤ CostructuredArrow (F ⋙ G) (G.obj S) where
  obj X := CostructuredArrow.mk (G.map X.hom)
  map f := CostructuredArrow.homMk f.left (by simp [← G.map_comp])

set_option backward.defeqAttrib.useBackward true in
instance (F : B ⥤ C) (G : C ⥤ D) (S : C) : (post F G S).Faithful where
  map_injective {_ _} _ _ h := by simpa [ext_iff] using h

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
instance (F : B ⥤ C) (G : C ⥤ D) (S : C) [G.Faithful] : (post F G S).Full where
  map_surjective f := ⟨homMk f.left (G.map_injective (by simpa using f.w)), by simp⟩

set_option backward.defeqAttrib.useBackward true in
instance (F : B ⥤ C) (G : C ⥤ D) (S : C) [G.Full] : (post F G S).EssSurj where
  mem_essImage h := ⟨mk (G.preimage h.hom), ⟨isoMk (Iso.refl _) (by simp)⟩⟩

/--
Instance `isEquivalence_post` / 实例 `isEquivalence_post`

English:
instance isEquivalence_post
  signature: (S : C) (F : B ⥤ C) (G : C ⥤ D) [G.Full] [G.Faithful]

中文:
实例 isEquivalence_post
  签名: (S : C) (F : B ⥤ C) (G : C ⥤ D) [G.满] [G.忠实]
-/
instance isEquivalence_post (S : C) (F : B ⥤ C) (G : C ⥤ D) [G.Full] [G.Faithful] :
    (post F G S).IsEquivalence where

section

variable {U : A ⥤ B} {V : B} {F : C ⥤ A} {G : D ⥤ B}
  (α : F ⋙ U ⟶ S ⋙ G) (β : G.obj T ⟶ V)

/-- The functor `CostructuredArrow S T ⥤ CostructuredArrow U V` that is deduced from
a natural transformation `F ⋙ U ⟶ S ⋙ G` and a morphism `G.obj T ⟶ V` -/
@[simps!, implicit_reducible]
/--
Definition of `map₂` / `map₂` 的定义

English:
definition map₂
  signature: : CostructuredArrow S T ⥤ CostructuredArrow U V
  body: Comma.map (F₂ := 𝟭 (Discrete PUnit)) α (Discrete.natTrans (fun _ => β))

中文:
定义 map₂
  签名: : CostructuredArrow S T ⥤ CostructuredArrow U V
  定义体: Comma.map (F₂ := 𝟭 (Discrete PUnit)) α (Discrete.natTrans (fun _ => β))

Depends on / 依赖: Comma.map, Discrete, Discrete.natTrans, infer_instance, natTrans
-/
def map₂ : CostructuredArrow S T ⥤ CostructuredArrow U V :=
  Comma.map (F₂ := 𝟭 (Discrete PUnit)) α (Discrete.natTrans (fun _ => β))

/--
Instance `faithful_map₂` / 实例 `faithful_map₂`

English:
instance faithful_map₂
  signature: [F.Faithful]
  body: by
  apply Comma.faithful_map

中文:
实例 faithful_map₂
  签名: [F.忠实]
  定义体: by
  apply Comma.faithful_map

Depends on / 依赖: Comma.faithful_map, faithful_map
-/
instance faithful_map₂ [F.Faithful] : (map₂ α β).Faithful := by
  apply Comma.faithful_map

/--
Instance `full_map₂` / 实例 `full_map₂`

English:
instance full_map₂
  signature: [G.Faithful] [F.Full] [IsIso α] [IsIso β]
  body: by
  apply Comma.full_map

中文:
实例 full_map₂
  签名: [G.忠实] [F.满] [是同构 α] [是同构 β]
  定义体: by
  apply Comma.full_map

Depends on / 依赖: Comma.full_map, full_map
-/
instance full_map₂ [G.Faithful] [F.Full] [IsIso α] [IsIso β] : (map₂ α β).Full := by
  apply Comma.full_map

/--
Instance `essSurj_map₂` / 实例 `essSurj_map₂`

English:
instance essSurj_map₂
  signature: [F.EssSurj] [G.Full] [IsIso α] [IsIso β]
  body: by
  apply Comma.essSurj_map

中文:
实例 essSurj_map₂
  签名: [F.本质满射] [G.满] [是同构 α] [是同构 β]
  定义体: by
  apply Comma.essSurj_map

Depends on / 依赖: Comma.essSurj_map, essSurj_map
-/
instance essSurj_map₂ [F.EssSurj] [G.Full] [IsIso α] [IsIso β] : (map₂ α β).EssSurj := by
  apply Comma.essSurj_map

/--
Instance `isEquivalenceMap₂` / 实例 `isEquivalenceMap₂`

English:
instance isEquivalenceMap₂
  body: by
  apply Comma.isEquivalenceMap

中文:
实例 isEquivalenceMap₂
  定义体: by
  apply Comma.isEquivalenceMap

Depends on / 依赖: Comma.isEquivalenceMap, isEquivalenceMap
-/
noncomputable instance isEquivalenceMap₂
    [F.IsEquivalence] [G.Faithful] [G.Full] [IsIso α] [IsIso β] :
    (map₂ α β).IsEquivalence := by
  apply Comma.isEquivalenceMap

set_option backward.defeqAttrib.useBackward true in
/-- The composition of two applications of `map₂` is naturally isomorphic to a single such one. -/
@[simps!]
/--
Definition of `map₂CompMap₂Iso` / `map₂CompMap₂Iso` 的定义

English:
definition map₂CompMap₂Iso
  signature: {C' : Type u₆} [Category.{v₆} C'] {D' : Type u₅} [Category.{v₅} D']
  body: NatIso.ofComponents fun X => isoMk (.refl _)

中文:
定义 map₂CompMap₂Iso
  签名: {C' : 类型u₆} [范畴.{v₆} C'] {D' : 类型u₅} [范畴.{v₅} D']
  定义体: NatIso.ofComponents fun X => isoMk (.refl _)
-/
def map₂CompMap₂Iso {C' : Type u₆} [Category.{v₆} C'] {D' : Type u₅} [Category.{v₅} D']
    {R : C' ⥤ D'} {F' : C' ⥤ C} {G' : D' ⥤ D} {X : D'} (α' : F' ⋙ S ⟶ R ⋙ G') (β' : G'.obj X ⟶ T) :
    map₂ α' β' ⋙ map₂ α β ≅
    map₂ (F := F' ⋙ F) (G := G' ⋙ G)
      ((Functor.associator ..).hom ≫ Functor.whiskerLeft _ α ≫
        (Functor.associator ..).inv ≫ Functor.whiskerRight α' _ ≫ (Functor.associator ..).hom)
      (G.map β' ≫ β) :=
  NatIso.ofComponents fun X => isoMk (.refl _)

set_option backward.defeqAttrib.useBackward true in
/-- `map₂` is invariant under isomorphisms. -/
@[simps!]
/--
Definition of `map₂Congr` / `map₂Congr` 的定义

English:
definition map₂Congr
  signature: {F' : C ⥤ A} {G' : D ⥤ B} (e₁ : F ≅ F') (e₂ : G ≅ G')
  body: NatIso.ofComponents (fun X => isoMk (e₁.app X.left) ?_) ?_

中文:
定义 map₂Congr
  签名: {F' : C ⥤ A} {G' : D ⥤ B} (e₁ : F ≅ F') (e₂ : G ≅ G')
  定义体: NatIso.ofComponents (fun X => isoMk (e₁.app X.left) ?_) ?_

Depends on / 依赖: NatIso, NatIso.ofComponents, X.left, ofComponents
-/
def map₂Congr {F' : C ⥤ A} {G' : D ⥤ B} (e₁ : F ≅ F') (e₂ : G ≅ G')
    (α' : F' ⋙ U ⟶ S ⋙ G') (β' : G'.obj T ⟶ V)
    (hα : α ≫ Functor.whiskerLeft _ e₂.hom = Functor.whiskerRight e₁.hom _ ≫ α')
    (hβ : β = e₂.hom.app _ ≫ β') :
    map₂ α β ≅ map₂ α' β' :=
  NatIso.ofComponents (fun X => isoMk (e₁.app X.left) ?_) ?_
where finally
  · subst hβ
    simp [← reassoc_of% dsimp% congr($(hα).app X.left)]
  · simp

set_option backward.defeqAttrib.useBackward true in
/-- `map₂` of the identity is the identity. -/
@[simps!]
/--
Definition of `map₂IdIso` / `map₂IdIso` 的定义

English:
definition map₂IdIso
  signature: (α : 𝟭 _ ⋙ S ⟶ S ⋙ 𝟭 _) (T : D) (β : (𝟭 _).obj T ⟶ T)
  body: NatIso.ofComponents (fun X => isoMk (.refl _))

中文:
定义 map₂IdIso
  签名: (α : 𝟭 _ ⋙ S ⟶ S ⋙ 𝟭 _) (T : D) (β : (𝟭 _).obj T ⟶ T)
  定义体: NatIso.ofComponents (fun X => isoMk (.refl _))

Depends on / 依赖: NatIso, NatIso.ofComponents, cat_disch, ofComponents
-/
def map₂IdIso (α : 𝟭 _ ⋙ S ⟶ S ⋙ 𝟭 _) (T : D) (β : (𝟭 _).obj T ⟶ T)
    (hα : α = (Functor.leftUnitor _).hom ≫ (Functor.rightUnitor _).inv := by cat_disch)
    (hβ : β = 𝟙 _ := by cat_disch) :
    map₂ α β ≅ 𝟭 _ :=
  NatIso.ofComponents (fun X => isoMk (.refl _))

set_option backward.defeqAttrib.useBackward true in
/-- `map₂` along equivalences of categories is an equivalence of categories. -/
@[simps]
/--
Definition of `map₂Iso` / `map₂Iso` 的定义

English:
definition map₂Iso
  signature: {F : C ≌ A} {G : D ≌ B} (α : F.functor ⋙ U ⟶ S ⋙ G.functor)
  body: CostructuredArrow.map₂ α β
  inverse := CostructuredArrow.map₂ α' β'
  unitIso := (map₂IdIso _ _ _ rfl rfl).symm ≪≫ map₂Congr _ _ F.unitIso G.unitIso _ _ ?_ ?_ ≪≫
    (map₂CompMap₂Iso ..).symm
  counitIso := map₂CompMap₂Iso .. ≪≫
    map₂Congr _ _ F.counitIso G.counitIso _ _ ?_ ?_ ≪≫ map₂IdIso _ _ _ rfl rfl
  functor_unitIso_comp := ?_

中文:
定义 map₂Iso
  签名: {F : C ≌ A} {G : D ≌ B} (α : F.functor ⋙ U ⟶ S ⋙ G.functor)
  定义体: CostructuredArrow.map₂ α β
  inverse := CostructuredArrow.map₂ α' β'
  unitIso := (map₂IdIso _ _ _ rfl rfl).symm ≪≫ map₂Congr _ _ F.unitIso G.unitIso _ _ ?_ ?_ ≪≫
    (map₂CompMap₂Iso ..).symm
  counitIso := map₂CompMap₂Iso .. ≪≫
    map₂Congr _ _ F.counitIso G.counitIso _ _ ?_ ?_ ≪≫ map₂IdIso _ _ _ rfl rfl
  functor_unitIso_comp := ?_

Depends on / 依赖: CostructuredArrow, CostructuredArrow.map
-/
def map₂Iso {F : C ≌ A} {G : D ≌ B} (α : F.functor ⋙ U ⟶ S ⋙ G.functor)
    (α' : F.inverse ⋙ S ⟶ U ⋙ G.inverse)
    (hα'α : (Functor.leftUnitor _).hom ≫ (Functor.rightUnitor _).inv ≫
      Functor.whiskerLeft _ G.unitIso.hom ≫ (Functor.associator ..).inv =
      Functor.whiskerRight F.unitIso.hom _ ≫ (Functor.associator ..).hom ≫
      Functor.whiskerLeft F.functor α' ≫
      (Functor.associator ..).inv ≫ Functor.whiskerRight α _)
    (hαα' : Functor.whiskerLeft F.inverse α ≫ (Functor.associator ..).inv ≫
      Functor.whiskerRight α' _ ≫
      (Functor.associator ..).hom ≫ Functor.whiskerLeft _ G.counitIso.hom =
      (Functor.associator ..).inv ≫ Functor.whiskerRight F.counitIso.hom _ ≫
      (Functor.leftUnitor _).hom ≫ (Functor.rightUnitor _).inv)
    (β : G.functor.obj T ⟶ V) (β' : G.inverse.obj V ⟶ T)
    (hββ' : G.inverse.map β ≫ β' = G.unitIso.inv.app _)
    (hβ'β : G.functor.map β' ≫ β = G.counitIso.hom.app _) :
    CostructuredArrow S T ≌ CostructuredArrow U V where
  functor := CostructuredArrow.map₂ α β
  inverse := CostructuredArrow.map₂ α' β'
  unitIso := (map₂IdIso _ _ _ rfl rfl).symm ≪≫ map₂Congr _ _ F.unitIso G.unitIso _ _ ?_ ?_ ≪≫
    (map₂CompMap₂Iso ..).symm
  counitIso := map₂CompMap₂Iso .. ≪≫
    map₂Congr _ _ F.counitIso G.counitIso _ _ ?_ ?_ ≪≫ map₂IdIso _ _ _ rfl rfl
  functor_unitIso_comp := ?_
where finally
  · ext X
    simpa using congr($(hα'α).app X)
  · simp [hββ']
  · ext X
    simpa using congr($(hαα').app X)
  · simp [hβ'β]
  · simp [map₂Congr]

end

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `postIsoMap₂` / `postIsoMap₂` 的定义

English:
definition postIsoMap₂
  signature: (S : C) (F : B ⥤ C) (G : C ⥤ D)
  body: NatIso.ofComponents fun _ => isoMk Iso.refl _

中文:
定义 postIsoMap₂
  签名: (S : C) (F : B ⥤ C) (G : C ⥤ D)
  定义体: NatIso.ofComponents fun _ => isoMk Iso.refl _
-/
def postIsoMap₂ (S : C) (F : B ⥤ C) (G : C ⥤ D) :
    post F G S ≅ map₂ (F := 𝟭 _) (𝟙 (F ⋙ G)) (𝟙 _) :=
NatIso.ofComponents fun _ => isoMk Iso.refl _

/--
Definition of `IsUniversal` / `IsUniversal` 的定义

English:
abbreviation IsUniversal
  signature: (f : CostructuredArrow S T)
  body: IsTerminal f

中文:
缩写 是泛
  签名: (f : CostructuredArrow S T)
  定义体: IsTerminal f

Depends on / 依赖: IsTerminal
-/
abbrev IsUniversal (f : CostructuredArrow S T) := IsTerminal f

namespace IsUniversal

variable {f g : CostructuredArrow S T}

/--
theorem `uniq` / 定理 `uniq`

English:
theorem uniq
  given: (h : IsUniversal f) (η : g ⟶ f)
  statement: η = h.from g
  proof: h.hom_ext η (h.from g)

中文:
定理 uniq
  条件: (h : 是泛 f) (η : g ⟶ f)
  结论: η = h.from g
  证明: h.hom_ext η (h.from g)

Depends on / 依赖: h.from, h.hom_ext, hom_ext
-/
theorem uniq (h : IsUniversal f) (η : g ⟶ f) : η = h.from g :=
  h.hom_ext η (h.from g)

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (h : IsUniversal f) (g : CostructuredArrow S T)
  body: (h.from g).left

中文:
定义 lift
  签名: (h : 是泛 f) (g : CostructuredArrow S T)
  定义体: (h.from g).left

Depends on / 依赖: h.from
-/
def lift (h : IsUniversal f) (g : CostructuredArrow S T) : g.left ⟶ f.left :=
  (h.from g).left

/-- Any costructured arrow factors through a universal arrow. -/
@[reassoc (attr := simp)]
/--
theorem `fac` / 定理 `fac`

English:
theorem fac
  given: (h : IsUniversal f) (g : CostructuredArrow S T)
  proof: Category.comp_id g.hom ▸ (h.from g).w

中文:
定理 fac
  条件: (h : 是泛 f) (g : CostructuredArrow S T)
  证明: Category.comp_id g.hom ▸ (h.from g).w

Depends on / 依赖: Category, Category.comp_id, comp_id, g.hom, h.from
-/
theorem fac (h : IsUniversal f) (g : CostructuredArrow S T) :
    S.map (h.lift g) ≫ f.hom = g.hom :=
  Category.comp_id g.hom ▸ (h.from g).w

/--
theorem `hom_desc` / 定理 `hom_desc`

English:
theorem hom_desc
  given: (h : IsUniversal f) {c : C} (η : c ⟶ f.left)
  proof: let g := mk S.map η ≫ f.hom
  congrArg CommaMorphism.left (h.hom_ext (homMk η rfl : g ⟶ f) (h.from g))

中文:
定理 hom_desc
  条件: (h : 是泛 f) {c : C} (η : c ⟶ f.left)
  证明: let g := mk S.map η ≫ f.hom
  congrArg CommaMorphism.left (h.hom_ext (homMk η rfl : g ⟶ f) (h.from g))

Depends on / 依赖: CommaMorphism, CommaMorphism.left, S.map, f.hom, h.from, h.hom_ext, hom_ext
-/
theorem hom_desc (h : IsUniversal f) {c : C} (η : c ⟶ f.left) :
    η = h.lift (mk <| S.map η ≫ f.hom) :=
let g := mk S.map η ≫ f.hom
  congrArg CommaMorphism.left (h.hom_ext (homMk η rfl : g ⟶ f) (h.from g))

/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  statement: (h : IsUniversal f) {c : C} {η η' : c ⟶ f.left}
  proof: by
  rw [h.hom_desc η]; rw [h.hom_desc η']; rw [w]

中文:
定理 hom_ext
  结论: (h : 是泛 f) {c : C} {η η' : c ⟶ f.left}
  证明: by
  rw [h.hom_desc η]; rw [h.hom_desc η']; rw [w]

Depends on / 依赖: h.hom_desc, hom_desc
-/
theorem hom_ext (h : IsUniversal f) {c : C} {η η' : c ⟶ f.left}
    (w : S.map η ≫ f.hom = S.map η' ≫ f.hom) : η = η' := by
  rw [h.hom_desc η]; rw [h.hom_desc η']; rw [w]

/--
theorem `existsUnique` / 定理 `existsUnique`

English:
theorem existsUnique
  given: (h : IsUniversal f) (g : CostructuredArrow S T)
  proof: ⟨h.lift g, h.fac g, fun f w => h.hom_ext by simp [w]⟩

中文:
定理 存在Unique
  条件: (h : 是泛 f) (g : CostructuredArrow S T)
  证明: ⟨h.lift g, h.fac g, fun f w => h.hom_ext by simp [w]⟩

Depends on / 依赖: h.fac, h.hom_ext, h.lift, hom_ext
-/
theorem existsUnique (h : IsUniversal f) (g : CostructuredArrow S T) :
    exists! η : g.left ⟶ f.left, S.map η ≫ f.hom = g.hom :=
⟨h.lift g, h.fac g, fun f w => h.hom_ext by simp [w]⟩

end IsUniversal

end CostructuredArrow

namespace Functor

variable {E : Type u₃} [Category.{v₃} E]

/-- Given `X : D` and `F : C ⥤ D`, to upgrade a functor `G : E ⥤ C` to a functor
`E ⥤ StructuredArrow X F`, it suffices to provide maps `X ⟶ F.obj (G.obj Y)` for all `Y` making
the obvious triangles involving all `F.map (G.map g)` commute.

This is of course the same as providing a cone over `F ⋙ G` with cone point `X`, see
`Functor.toStructuredArrowIsoToStructuredArrow`. -/
@[simps]
/--
Definition of `toStructuredArrow` / `toStructuredArrow` 的定义

English:
definition toStructuredArrow
  signature: (G : E ⥤ C) (X : D) (F : C ⥤ D) (f : (Y : E) -> X ⟶ F.obj (G.obj Y))
  body: StructuredArrow.mk (f Y)
  map g := StructuredArrow.homMk (G.map g) (h g)

中文:
定义 toStructuredArrow
  签名: (G : E ⥤ C) (X : D) (F : C ⥤ D) (f : (Y : E) -> X ⟶ F.obj (G.obj Y))
  定义体: StructuredArrow.mk (f Y)
  map g := StructuredArrow.homMk (G.map g) (h g)

Depends on / 依赖: StructuredArrow, StructuredArrow.mk
-/
def toStructuredArrow (G : E ⥤ C) (X : D) (F : C ⥤ D) (f : (Y : E) -> X ⟶ F.obj (G.obj Y))
    (h : forall {Y Z : E} (g : Y ⟶ Z), f Y ≫ F.map (G.map g) = f Z) : E ⥤ StructuredArrow X F where
  obj Y := StructuredArrow.mk (f Y)
  map g := StructuredArrow.homMk (G.map g) (h g)

/--
Definition of `toStructuredArrowCompProj` / `toStructuredArrowCompProj` 的定义

English:
definition toStructuredArrowCompProj
  signature: (G : E ⥤ C) (X : D) (F : C ⥤ D) (f : (Y : E) -> X ⟶ F.obj (G.obj Y))
  body: Iso.refl _

@[simp]

中文:
定义 toStructuredArrowCompProj
  签名: (G : E ⥤ C) (X : D) (F : C ⥤ D) (f : (Y : E) -> X ⟶ F.obj (G.obj Y))
  定义体: Iso.refl _

@[simp]

Depends on / 依赖: Iso.refl
-/
def toStructuredArrowCompProj (G : E ⥤ C) (X : D) (F : C ⥤ D) (f : (Y : E) -> X ⟶ F.obj (G.obj Y))
    (h : forall {Y Z : E} (g : Y ⟶ Z), f Y ≫ F.map (G.map g) = f Z) :
    G.toStructuredArrow X F f h ⋙ StructuredArrow.proj _ _ ≅ G :=
  Iso.refl _

@[simp]
/--
lemma `toStructuredArrow_comp_proj` / 引理 `toStructuredArrow_comp_proj`

English:
lemma toStructuredArrow_comp_proj
  statement: (G : E ⥤ C) (X : D) (F : C ⥤ D)
  proof: rfl

中文:
引理 toStructuredArrow_comp_proj
  结论: (G : E ⥤ C) (X : D) (F : C ⥤ D)
  证明: rfl
-/
lemma toStructuredArrow_comp_proj (G : E ⥤ C) (X : D) (F : C ⥤ D)
    (f : (Y : E) -> X ⟶ F.obj (G.obj Y)) (h : forall {Y Z : E} (g : Y ⟶ Z), f Y ≫ F.map (G.map g) = f Z) :
    G.toStructuredArrow X F f h ⋙ StructuredArrow.proj _ _ = G :=
  rfl

/-- Given `F : C ⥤ D` and `X : D`, to upgrade a functor `G : E ⥤ C` to a functor
`E ⥤ CostructuredArrow F X`, it suffices to provide maps `F.obj (G.obj Y) ⟶ X` for all `Y`
making the obvious triangles involving all `F.map (G.map g)` commute.

This is of course the same as providing a cocone over `F ⋙ G` with cocone point `X`, see
`Functor.toCostructuredArrowIsoToCostructuredArrow`. -/
@[simps]
/--
Definition of `toCostructuredArrow` / `toCostructuredArrow` 的定义

English:
definition toCostructuredArrow
  signature: (G : E ⥤ C) (F : C ⥤ D) (X : D) (f : (Y : E) -> F.obj (G.obj Y) ⟶ X)
  body: CostructuredArrow.mk (f Y)
  map g := CostructuredArrow.homMk (G.map g) (h g)

中文:
定义 toCostructuredArrow
  签名: (G : E ⥤ C) (F : C ⥤ D) (X : D) (f : (Y : E) -> F.obj (G.obj Y) ⟶ X)
  定义体: CostructuredArrow.mk (f Y)
  map g := CostructuredArrow.homMk (G.map g) (h g)

Depends on / 依赖: CostructuredArrow, CostructuredArrow.mk
-/
def toCostructuredArrow (G : E ⥤ C) (F : C ⥤ D) (X : D) (f : (Y : E) -> F.obj (G.obj Y) ⟶ X)
    (h : forall {Y Z : E} (g : Y ⟶ Z), F.map (G.map g) ≫ f Z = f Y) : E ⥤ CostructuredArrow F X where
  obj Y := CostructuredArrow.mk (f Y)
  map g := CostructuredArrow.homMk (G.map g) (h g)

/--
Definition of `toCostructuredArrowCompProj` / `toCostructuredArrowCompProj` 的定义

English:
definition toCostructuredArrowCompProj
  signature: (G : E ⥤ C) (F : C ⥤ D) (X : D)
  body: Iso.refl _

@[simp]

中文:
定义 toCostructuredArrowCompProj
  签名: (G : E ⥤ C) (F : C ⥤ D) (X : D)
  定义体: Iso.refl _

@[simp]

Depends on / 依赖: Iso.refl
-/
def toCostructuredArrowCompProj (G : E ⥤ C) (F : C ⥤ D) (X : D)
    (f : (Y : E) -> F.obj (G.obj Y) ⟶ X) (h : forall {Y Z : E} (g : Y ⟶ Z), F.map (G.map g) ≫ f Z = f Y) :
    G.toCostructuredArrow F X f h ⋙ CostructuredArrow.proj _ _ ≅ G :=
  Iso.refl _

@[simp]
/--
lemma `toCostructuredArrow_comp_proj` / 引理 `toCostructuredArrow_comp_proj`

English:
lemma toCostructuredArrow_comp_proj
  statement: (G : E ⥤ C) (F : C ⥤ D) (X : D)
  proof: rfl

中文:
引理 toCostructuredArrow_comp_proj
  结论: (G : E ⥤ C) (F : C ⥤ D) (X : D)
  证明: rfl
-/
lemma toCostructuredArrow_comp_proj (G : E ⥤ C) (F : C ⥤ D) (X : D)
    (f : (Y : E) -> F.obj (G.obj Y) ⟶ X) (h : forall {Y Z : E} (g : Y ⟶ Z), F.map (G.map g) ≫ f Z = f Y) :
    G.toCostructuredArrow F X f h ⋙ CostructuredArrow.proj _ _ = G :=
rfl

end Functor

open Opposite

namespace StructuredArrow

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- For a functor `F : C ⥤ D` and an object `d : D`, we obtain a contravariant functor from the
category of structured arrows `d ⟶ F.obj c` to the category of costructured arrows
`F.op.obj c ⟶ (op d)`.
-/
@[simps]
/--
Definition of `toCostructuredArrow` / `toCostructuredArrow` 的定义

English:
definition toCostructuredArrow
  signature: (F : C ⥤ D) (d : D)
  body: CostructuredArrow.mk (Y := op X.unop.right) X.unop.hom.op
  map f := CostructuredArrow.homMk f.unop.right.op (by simp [← op_comp])

中文:
定义 toCostructuredArrow
  签名: (F : C ⥤ D) (d : D)
  定义体: CostructuredArrow.mk (Y := op X.unop.right) X.unop.hom.op
  map f := CostructuredArrow.homMk f.unop.right.op (by simp [← op_comp])

Depends on / 依赖: CostructuredArrow, CostructuredArrow.mk, X.unop.hom.op, X.unop.right
-/
def toCostructuredArrow (F : C ⥤ D) (d : D) :
    (StructuredArrow d F)ᵒᵖ ⥤ CostructuredArrow F.op (op d) where
  obj X := CostructuredArrow.mk (Y := op X.unop.right) X.unop.hom.op
  map f := CostructuredArrow.homMk f.unop.right.op (by simp [← op_comp])

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- For a functor `F : C ⥤ D` and an object `d : D`, we obtain a contravariant functor from the
category of structured arrows `op d ⟶ F.op.obj c` to the category of costructured arrows
`F.obj c ⟶ d`.
-/
@[simps]
/--
Definition of `toCostructuredArrow'` / `toCostructuredArrow'` 的定义

English:
definition toCostructuredArrow'
  signature: (F : C ⥤ D) (d : D)
  body: CostructuredArrow.mk (Y := unop X.unop.right) X.unop.hom.unop
  map f :=
    CostructuredArrow.homMk f.unop.right.unop
      (Quiver.Hom.op_inj (by simp [dsimp% f.unop.w]))

中文:
定义 toCostructuredArrow'
  签名: (F : C ⥤ D) (d : D)
  定义体: CostructuredArrow.mk (Y := unop X.unop.right) X.unop.hom.unop
  map f :=
    CostructuredArrow.homMk f.unop.right.unop
      (Quiver.Hom.op_inj (by simp [dsimp% f.unop.w]))

Depends on / 依赖: CostructuredArrow, CostructuredArrow.mk, X.unop.hom.unop, X.unop.right
-/
def toCostructuredArrow' (F : C ⥤ D) (d : D) :
    (StructuredArrow (op d) F.op)ᵒᵖ ⥤ CostructuredArrow F d where
  obj X := CostructuredArrow.mk (Y := unop X.unop.right) X.unop.hom.unop
  map f :=
    CostructuredArrow.homMk f.unop.right.unop
      (Quiver.Hom.op_inj (by simp [dsimp% f.unop.w]))

end StructuredArrow

namespace CostructuredArrow

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- For a functor `F : C ⥤ D` and an object `d : D`, we obtain a contravariant functor from the
category of costructured arrows `F.obj c ⟶ d` to the category of structured arrows
`op d ⟶ F.op.obj c`.
-/
@[simps]
/--
Definition of `toStructuredArrow` / `toStructuredArrow` 的定义

English:
definition toStructuredArrow
  signature: (F : C ⥤ D) (d : D)
  body: StructuredArrow.mk (Y := op X.unop.left) X.unop.hom.op
  map f := StructuredArrow.homMk f.unop.left.op (by simp [← op_comp])

中文:
定义 toStructuredArrow
  签名: (F : C ⥤ D) (d : D)
  定义体: StructuredArrow.mk (Y := op X.unop.left) X.unop.hom.op
  map f := StructuredArrow.homMk f.unop.left.op (by simp [← op_comp])

Depends on / 依赖: StructuredArrow, StructuredArrow.mk, X.unop.hom.op, X.unop.left
-/
def toStructuredArrow (F : C ⥤ D) (d : D) :
    (CostructuredArrow F d)ᵒᵖ ⥤ StructuredArrow (op d) F.op where
  obj X := StructuredArrow.mk (Y := op X.unop.left) X.unop.hom.op
  map f := StructuredArrow.homMk f.unop.left.op (by simp [← op_comp])

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- For a functor `F : C ⥤ D` and an object `d : D`, we obtain a contravariant functor from the
category of costructured arrows `F.op.obj c ⟶ op d` to the category of structured arrows
`d ⟶ F.obj c`.
-/
@[simps]
/--
Definition of `toStructuredArrow'` / `toStructuredArrow'` 的定义

English:
definition toStructuredArrow'
  signature: (F : C ⥤ D) (d : D)
  body: StructuredArrow.mk (Y := unop X.unop.left) X.unop.hom.unop
  map f :=
    StructuredArrow.homMk f.unop.left.unop
      (Quiver.Hom.op_inj (by simp [dsimp% f.unop.w]))

中文:
定义 toStructuredArrow'
  签名: (F : C ⥤ D) (d : D)
  定义体: StructuredArrow.mk (Y := unop X.unop.left) X.unop.hom.unop
  map f :=
    StructuredArrow.homMk f.unop.left.unop
      (Quiver.Hom.op_inj (by simp [dsimp% f.unop.w]))

Depends on / 依赖: StructuredArrow, StructuredArrow.mk, X.unop.hom.unop, X.unop.left
-/
def toStructuredArrow' (F : C ⥤ D) (d : D) :
    (CostructuredArrow F.op (op d))ᵒᵖ ⥤ StructuredArrow d F where
  obj X := StructuredArrow.mk (Y := unop X.unop.left) X.unop.hom.unop
  map f :=
    StructuredArrow.homMk f.unop.left.unop
      (Quiver.Hom.op_inj (by simp [dsimp% f.unop.w]))

end CostructuredArrow

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `structuredArrowOpEquivalence` / `structuredArrowOpEquivalence` 的定义

English:
definition structuredArrowOpEquivalence
  signature: (F : C ⥤ D) (d : D)
  body: StructuredArrow.toCostructuredArrow F d
  inverse := (CostructuredArrow.toStructuredArrow' F d).rightOp
  unitIso := NatIso.ofComponents
    (fun X => (StructuredArrow.isoMk (Iso.refl _)).op) (by
      rintro ⟨X⟩ ⟨Y⟩ f
      obtain ⟨X, x, rfl⟩ := X.mk_surjective
      obtain ⟨Y, y, rfl⟩ := Y.mk_surjective
      exact Quiver.Hom.unop_inj (by ext; apply Quiver.Hom.op_inj (by simp)))
  counitIso := NatIso.ofComponents
    (fun X => CostructuredArrow.isoMk (Iso.refl _))

中文:
定义 structuredArrowOpEquivalence
  签名: (F : C ⥤ D) (d : D)
  定义体: StructuredArrow.toCostructuredArrow F d
  inverse := (CostructuredArrow.toStructuredArrow' F d).rightOp
  unitIso := NatIso.ofComponents
    (fun X => (StructuredArrow.isoMk (Iso.refl _)).op) (by
      rintro ⟨X⟩ ⟨Y⟩ f
      obtain ⟨X, x, rfl⟩ := X.mk_surjective
      obtain ⟨Y, y, rfl⟩ := Y.mk_surjective
      exact Quiver.Hom.unop_inj (by ext; apply Quiver.Hom.op_inj (by simp)))
  counitIso := NatIso.ofComponents
    (fun X => CostructuredArrow.isoMk (Iso.refl _))

Depends on / 依赖: StructuredArrow, StructuredArrow.toCostructuredArrow, toCostructuredArrow
-/
def structuredArrowOpEquivalence (F : C ⥤ D) (d : D) :
    (StructuredArrow d F)ᵒᵖ ≌ CostructuredArrow F.op (op d) where
  functor := StructuredArrow.toCostructuredArrow F d
  inverse := (CostructuredArrow.toStructuredArrow' F d).rightOp
  unitIso := NatIso.ofComponents
    (fun X => (StructuredArrow.isoMk (Iso.refl _)).op) (by
      rintro ⟨X⟩ ⟨Y⟩ f
      obtain ⟨X, x, rfl⟩ := X.mk_surjective
      obtain ⟨Y, y, rfl⟩ := Y.mk_surjective
      exact Quiver.Hom.unop_inj (by ext; apply Quiver.Hom.op_inj (by simp)))
  counitIso := NatIso.ofComponents
    (fun X => CostructuredArrow.isoMk (Iso.refl _))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `costructuredArrowOpEquivalence` / `costructuredArrowOpEquivalence` 的定义

English:
definition costructuredArrowOpEquivalence
  signature: (F : C ⥤ D) (d : D)
  body: CostructuredArrow.toStructuredArrow F d
  inverse := (StructuredArrow.toCostructuredArrow' F d).rightOp
  unitIso := NatIso.ofComponents
    (fun X => (CostructuredArrow.isoMk (Iso.refl _)).op) (by
      rintro ⟨X⟩ ⟨Y⟩ f
      obtain ⟨X, x, rfl⟩ := X.mk_surjective
      obtain ⟨Y, y, rfl⟩ := Y.mk_surjective
      exact Quiver.Hom.unop_inj (by ext; apply Quiver.Hom.op_inj (by simp)))
  counitIso := NatIso.ofComponents
      (fun X => StructuredArrow.isoMk (Iso.refl _))

中文:
定义 costructuredArrowOpEquivalence
  签名: (F : C ⥤ D) (d : D)
  定义体: CostructuredArrow.toStructuredArrow F d
  inverse := (StructuredArrow.toCostructuredArrow' F d).rightOp
  unitIso := NatIso.ofComponents
    (fun X => (CostructuredArrow.isoMk (Iso.refl _)).op) (by
      rintro ⟨X⟩ ⟨Y⟩ f
      obtain ⟨X, x, rfl⟩ := X.mk_surjective
      obtain ⟨Y, y, rfl⟩ := Y.mk_surjective
      exact Quiver.Hom.unop_inj (by ext; apply Quiver.Hom.op_inj (by simp)))
  counitIso := NatIso.ofComponents
      (fun X => StructuredArrow.isoMk (Iso.refl _))

Depends on / 依赖: CostructuredArrow, CostructuredArrow.toStructuredArrow, toStructuredArrow
-/
def costructuredArrowOpEquivalence (F : C ⥤ D) (d : D) :
    (CostructuredArrow F d)ᵒᵖ ≌ StructuredArrow (op d) F.op where
  functor := CostructuredArrow.toStructuredArrow F d
  inverse := (StructuredArrow.toCostructuredArrow' F d).rightOp
  unitIso := NatIso.ofComponents
    (fun X => (CostructuredArrow.isoMk (Iso.refl _)).op) (by
      rintro ⟨X⟩ ⟨Y⟩ f
      obtain ⟨X, x, rfl⟩ := X.mk_surjective
      obtain ⟨Y, y, rfl⟩ := Y.mk_surjective
      exact Quiver.Hom.unop_inj (by ext; apply Quiver.Hom.op_inj (by simp)))
  counitIso := NatIso.ofComponents
      (fun X => StructuredArrow.isoMk (Iso.refl _))

section Pre

variable {E : Type u₃} [Category.{v₃} E] (F : C ⥤ D) {G : D ⥤ E} {e : E}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The functor establishing the equivalence `StructuredArrow.preEquivalence`. -/
@[simps!]
/--
Definition of `StructuredArrow.preEquivalenceFunctor` / `StructuredArrow.preEquivalenceFunctor` 的定义

English:
definition StructuredArrow.preEquivalenceFunctor
  signature: (f : StructuredArrow e G)
  body: mk g.hom.right
map φ := homMk φ.right.right by
    rw [← w φ]; rw [comp_right]
    simp

中文:
定义 结构化箭头.preEquivalenceFunctor
  签名: (f : 结构化箭头 e G)
  定义体: mk g.hom.right
map φ := homMk φ.right.right by
    rw [← w φ]; rw [comp_right]
    simp

Depends on / 依赖: g.hom.right
-/
def StructuredArrow.preEquivalenceFunctor (f : StructuredArrow e G) :
    StructuredArrow f (pre e F G) ⥤ StructuredArrow f.right F where
  obj g := mk g.hom.right
map φ := homMk φ.right.right by
    rw [← w φ]; rw [comp_right]
    simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The inverse functor establishing the equivalence `StructuredArrow.preEquivalence`. -/
@[simps!]
/--
Definition of `StructuredArrow.preEquivalenceInverse` / `StructuredArrow.preEquivalenceInverse` 的定义

English:
definition StructuredArrow.preEquivalenceInverse
  signature: (f : StructuredArrow e G)
  body: mk
            (Y := mk (Y := g.right)
              (f.hom ≫ (G.map g.hom : G.obj f.right ⟶ (F ⋙ G).obj g.right)))
            (homMk g.hom)
map φ := homMk homMk φ.right by
    simp only [Functor.comp_obj, mk_right, mk_hom_eq_self,
      Functor.comp_map, Category.assoc, ← w φ, Functor.map_comp]

中文:
定义 结构化箭头.preEquivalenceInverse
  签名: (f : 结构化箭头 e G)
  定义体: mk
            (Y := mk (Y := g.right)
              (f.hom ≫ (G.map g.hom : G.obj f.right ⟶ (F ⋙ G).obj g.right)))
            (homMk g.hom)
map φ := homMk homMk φ.right by
    simp only [Functor.comp_obj, mk_right, mk_hom_eq_self,
      Functor.comp_map, Category.assoc, ← w φ, Functor.map_comp]
-/
def StructuredArrow.preEquivalenceInverse (f : StructuredArrow e G) :
    StructuredArrow f.right F ⥤ StructuredArrow f (pre e F G) where
  obj g := mk
            (Y := mk (Y := g.right)
              (f.hom ≫ (G.map g.hom : G.obj f.right ⟶ (F ⋙ G).obj g.right)))
            (homMk g.hom)
map φ := homMk homMk φ.right by
    simp only [Functor.comp_obj, mk_right, mk_hom_eq_self,
      Functor.comp_map, Category.assoc, ← w φ, Functor.map_comp]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A structured arrow category on a `StructuredArrow.pre e F G` functor is equivalent to the
structured arrow category on F -/
@[simps]
/--
Definition of `StructuredArrow.preEquivalence` / `StructuredArrow.preEquivalence` 的定义

English:
definition StructuredArrow.preEquivalence
  signature: (f : StructuredArrow e G)
  body: preEquivalenceFunctor F f
  inverse := preEquivalenceInverse F f
  unitIso := NatIso.ofComponents (fun X => isoMk (isoMk (Iso.refl _) (by simp)))
  counitIso := NatIso.ofComponents (fun _ => isoMk (Iso.refl _))

中文:
定义 结构化箭头.preEquivalence
  签名: (f : 结构化箭头 e G)
  定义体: preEquivalenceFunctor F f
  inverse := preEquivalenceInverse F f
  unitIso := NatIso.ofComponents (fun X => isoMk (isoMk (Iso.refl _) (by simp)))
  counitIso := NatIso.ofComponents (fun _ => isoMk (Iso.refl _))

Depends on / 依赖: preEquivalenceFunctor
-/
def StructuredArrow.preEquivalence (f : StructuredArrow e G) :
    StructuredArrow f (pre e F G) ≌ StructuredArrow f.right F where
  functor := preEquivalenceFunctor F f
  inverse := preEquivalenceInverse F f
  unitIso := NatIso.ofComponents (fun X => isoMk (isoMk (Iso.refl _) (by simp)))
  counitIso := NatIso.ofComponents (fun _ => isoMk (Iso.refl _))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `StructuredArrow.map₂IsoPreEquivalenceInverseCompProj` / `StructuredArrow.map₂IsoPreEquivalenceInverseCompProj` 的定义

English:
definition StructuredArrow.map₂IsoPreEquivalenceInverseCompProj
  signature: {T : C ⥤ D} {S : D ⥤ E} {T' : C ⥤ E}
  body: NatIso.ofComponents fun _ => isoMk (Iso.refl _)

中文:
定义 结构化箭头.map₂IsoPreEquivalenceInverseCompProj
  签名: {T : C ⥤ D} {S : D ⥤ E} {T' : C ⥤ E}
  定义体: NatIso.ofComponents fun _ => isoMk (Iso.refl _)

Depends on / 依赖: inverse, preEquivalence
-/
def StructuredArrow.map₂IsoPreEquivalenceInverseCompProj {T : C ⥤ D} {S : D ⥤ E} {T' : C ⥤ E}
    (d : D) (e : E) (u : e ⟶ S.obj d) (α : T ⋙ S ⟶ T') :
    map₂ (F := 𝟭 _) u α ≅ (preEquivalence T (mk u)).inverse ⋙ proj (mk u) (pre _ T S) ⋙
      map₂ (F := 𝟭 _) (G := 𝟭 _) (𝟙 _) α :=
  NatIso.ofComponents fun _ => isoMk (Iso.refl _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The functor establishing the equivalence `CostructuredArrow.preEquivalence`. -/
@[simps!]
/--
Definition of `CostructuredArrow.preEquivalence.functor` / `CostructuredArrow.preEquivalence.functor` 的定义

English:
definition CostructuredArrow.preEquivalence.functor
  signature: (f : CostructuredArrow G e)
  body: mk g.hom.left
map φ := homMk φ.left.left by
    rw [← w φ]; rw [comp_left]
    simp

中文:
定义 CostructuredArrow.preEquivalence.functor
  签名: (f : CostructuredArrow G e)
  定义体: mk g.hom.left
map φ := homMk φ.left.left by
    rw [← w φ]; rw [comp_left]
    simp

Depends on / 依赖: g.hom.left
-/
def CostructuredArrow.preEquivalence.functor (f : CostructuredArrow G e) :
    CostructuredArrow (pre F G e) f ⥤ CostructuredArrow F f.left where
  obj g := mk g.hom.left
map φ := homMk φ.left.left by
    rw [← w φ]; rw [comp_left]
    simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The inverse functor establishing the equivalence `CostructuredArrow.preEquivalence`. -/
@[simps!]
/--
Definition of `CostructuredArrow.preEquivalence.inverse` / `CostructuredArrow.preEquivalence.inverse` 的定义

English:
definition CostructuredArrow.preEquivalence.inverse
  signature: (f : CostructuredArrow G e)
  body: mk (Y := mk (Y := g.left) (G.map g.hom ≫ f.hom)) (homMk g.hom)
map φ := homMk homMk φ.left by
    simp only [Functor.comp_obj, mk_left, Functor.comp_map, mk_hom_eq_self,
      ← w φ, Functor.map_comp, Category.assoc]

中文:
定义 CostructuredArrow.preEquivalence.inverse
  签名: (f : CostructuredArrow G e)
  定义体: mk (Y := mk (Y := g.left) (G.map g.hom ≫ f.hom)) (homMk g.hom)
map φ := homMk homMk φ.left by
    simp only [Functor.comp_obj, mk_left, Functor.comp_map, mk_hom_eq_self,
      ← w φ, Functor.map_comp, Category.assoc]

Depends on / 依赖: G.map, f.hom, g.hom, g.left
-/
def CostructuredArrow.preEquivalence.inverse (f : CostructuredArrow G e) :
    CostructuredArrow F f.left ⥤ CostructuredArrow (pre F G e) f where
  obj g := mk (Y := mk (Y := g.left) (G.map g.hom ≫ f.hom)) (homMk g.hom)
map φ := homMk homMk φ.left by
    simp only [Functor.comp_obj, mk_left, Functor.comp_map, mk_hom_eq_self,
      ← w φ, Functor.map_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A costructured arrow category on a `CostructuredArrow.pre F G e` functor is equivalent to the
costructured arrow category on F -/
@[simps]
/--
Definition of `CostructuredArrow.preEquivalence` / `CostructuredArrow.preEquivalence` 的定义

English:
definition CostructuredArrow.preEquivalence
  signature: (f : CostructuredArrow G e)
  body: preEquivalence.functor F f
  inverse := preEquivalence.inverse F f
  unitIso := NatIso.ofComponents (fun X => isoMk (isoMk (Iso.refl _)
    (by simp)))
  counitIso := NatIso.ofComponents (fun _ => isoMk (Iso.refl _))

中文:
定义 CostructuredArrow.preEquivalence
  签名: (f : CostructuredArrow G e)
  定义体: preEquivalence.functor F f
  inverse := preEquivalence.inverse F f
  unitIso := NatIso.ofComponents (fun X => isoMk (isoMk (Iso.refl _)
    (by simp)))
  counitIso := NatIso.ofComponents (fun _ => isoMk (Iso.refl _))

Depends on / 依赖: functor, preEquivalence, preEquivalence.functor
-/
def CostructuredArrow.preEquivalence (f : CostructuredArrow G e) :
    CostructuredArrow (pre F G e) f ≌ CostructuredArrow F f.left where
  functor := preEquivalence.functor F f
  inverse := preEquivalence.inverse F f
  unitIso := NatIso.ofComponents (fun X => isoMk (isoMk (Iso.refl _)
    (by simp)))
  counitIso := NatIso.ofComponents (fun _ => isoMk (Iso.refl _))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `CostructuredArrow.map₂IsoPreEquivalenceInverseCompProj` / `CostructuredArrow.map₂IsoPreEquivalenceInverseCompProj` 的定义

English:
definition CostructuredArrow.map₂IsoPreEquivalenceInverseCompProj
  signature: (T : C ⥤ D) (S : D ⥤ E) (d : D) (e : E)
  body: NatIso.ofComponents fun _ => isoMk (Iso.refl _)

中文:
定义 CostructuredArrow.map₂IsoPreEquivalenceInverseCompProj
  签名: (T : C ⥤ D) (S : D ⥤ E) (d : D) (e : E)
  定义体: NatIso.ofComponents fun _ => isoMk (Iso.refl _)
-/
def CostructuredArrow.map₂IsoPreEquivalenceInverseCompProj (T : C ⥤ D) (S : D ⥤ E) (d : D) (e : E)
    (u : S.obj d ⟶ e) :
    map₂ (F := 𝟭 _) (U := T ⋙ S) (𝟙 (T ⋙ S)) u ≅
      (preEquivalence T (mk u)).inverse ⋙ proj (pre T S _) (mk u) :=
  NatIso.ofComponents fun _ => isoMk (Iso.refl _)

end Pre

section Prod

section

variable {C' : Type u₃} [Category.{v₃} C'] {D' : Type u₄} [Category.{v₄} D']
  (S : D) (S' : D') (T : C ⥤ D) (T' : C' ⥤ D')

@[reassoc (attr := simp)]
/--
theorem `StructuredArrow.w_prod_fst` / 定理 `StructuredArrow.w_prod_fst`

English:
theorem StructuredArrow.w_prod_fst
  statement: {X Y : StructuredArrow (S, S') (T.prod T')}
  proof: congr_arg _root_.Prod.fst (StructuredArrow.w f)

@[reassoc (attr := simp)]

中文:
定理 结构化箭头.w_prod_fst
  结论: {X Y : 结构化箭头 (S, S') (T.乘积 T')}
  证明: congr_arg _root_.Prod.fst (StructuredArrow.w f)

@[reassoc (attr := simp)]

Depends on / 依赖: StructuredArrow, StructuredArrow.w, _root_, _root_.Prod.fst, congr_arg
-/
theorem StructuredArrow.w_prod_fst {X Y : StructuredArrow (S, S') (T.prod T')}
    (f : X ⟶ Y) : X.hom.1 ≫ T.map f.right.1 = Y.hom.1 :=
  congr_arg _root_.Prod.fst (StructuredArrow.w f)

@[reassoc (attr := simp)]
/--
theorem `StructuredArrow.w_prod_snd` / 定理 `StructuredArrow.w_prod_snd`

English:
theorem StructuredArrow.w_prod_snd
  statement: {X Y : StructuredArrow (S, S') (T.prod T')}
  proof: congr_arg _root_.Prod.snd (StructuredArrow.w f)

中文:
定理 结构化箭头.w_prod_snd
  结论: {X Y : 结构化箭头 (S, S') (T.乘积 T')}
  证明: congr_arg _root_.Prod.snd (StructuredArrow.w f)

Depends on / 依赖: StructuredArrow, StructuredArrow.w, _root_, _root_.Prod.snd, congr_arg
-/
theorem StructuredArrow.w_prod_snd {X Y : StructuredArrow (S, S') (T.prod T')}
    (f : X ⟶ Y) : X.hom.2 ≫ T'.map f.right.2 = Y.hom.2 :=
  congr_arg _root_.Prod.snd (StructuredArrow.w f)

/-- Implementation; see `StructuredArrow.prodEquivalence`. -/
@[simps]
/--
Definition of `StructuredArrow.prodFunctor` / `StructuredArrow.prodFunctor` 的定义

English:
definition StructuredArrow.prodFunctor
  signature: :
  body: ⟨.mk f.hom.1, .mk f.hom.2⟩
  map η := ⟨StructuredArrow.homMk η.right.1 (by simp),
            StructuredArrow.homMk η.right.2 (by simp)⟩

中文:
定义 结构化箭头.prodFunctor
  签名: :
  定义体: ⟨.mk f.hom.1, .mk f.hom.2⟩
  map η := ⟨StructuredArrow.homMk η.right.1 (by simp),
            StructuredArrow.homMk η.right.2 (by simp)⟩

Depends on / 依赖: f.hom
-/
def StructuredArrow.prodFunctor :
    StructuredArrow (S, S') (T.prod T') ⥤ StructuredArrow S T × StructuredArrow S' T' where
  obj f := ⟨.mk f.hom.1, .mk f.hom.2⟩
  map η := ⟨StructuredArrow.homMk η.right.1 (by simp),
            StructuredArrow.homMk η.right.2 (by simp)⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Implementation; see `StructuredArrow.prodEquivalence`. -/
@[simps]
/--
Definition of `StructuredArrow.prodInverse` / `StructuredArrow.prodInverse` 的定义

English:
definition StructuredArrow.prodInverse
  signature: :
  body: .mk (Y := (f.1.right, f.2.right)) ⟨f.1.hom, f.2.hom⟩
  map η := StructuredArrow.homMk ⟨η.1.right, η.2.right⟩ (by simp)

中文:
定义 结构化箭头.prodInverse
  签名: :
  定义体: .mk (Y := (f.1.right, f.2.right)) ⟨f.1.hom, f.2.hom⟩
  map η := StructuredArrow.homMk ⟨η.1.right, η.2.right⟩ (by simp)
-/
def StructuredArrow.prodInverse :
    StructuredArrow S T × StructuredArrow S' T' ⥤ StructuredArrow (S, S') (T.prod T') where
  obj f := .mk (Y := (f.1.right, f.2.right)) ⟨f.1.hom, f.2.hom⟩
  map η := StructuredArrow.homMk ⟨η.1.right, η.2.right⟩ (by simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The natural equivalence
`StructuredArrow (S, S') (T.prod T') ≌ StructuredArrow S T × StructuredArrow S' T'`. -/
@[simps]
/--
Definition of `StructuredArrow.prodEquivalence` / `StructuredArrow.prodEquivalence` 的定义

English:
definition StructuredArrow.prodEquivalence
  signature: :
  body: StructuredArrow.prodFunctor S S' T T'
  inverse := StructuredArrow.prodInverse S S' T T'
  unitIso := NatIso.ofComponents (fun f => Iso.refl _) (by simp)
  counitIso := NatIso.ofComponents (fun f => Iso.refl _) (by intros; ext; all_goals simp)

中文:
定义 结构化箭头.prodEquivalence
  签名: :
  定义体: StructuredArrow.prodFunctor S S' T T'
  inverse := StructuredArrow.prodInverse S S' T T'
  unitIso := NatIso.ofComponents (fun f => Iso.refl _) (by simp)
  counitIso := NatIso.ofComponents (fun f => Iso.refl _) (by intros; ext; all_goals simp)

Depends on / 依赖: StructuredArrow, StructuredArrow.prodFunctor, prodFunctor
-/
def StructuredArrow.prodEquivalence :
    StructuredArrow (S, S') (T.prod T') ≌ StructuredArrow S T × StructuredArrow S' T' where
  functor := StructuredArrow.prodFunctor S S' T T'
  inverse := StructuredArrow.prodInverse S S' T T'
  unitIso := NatIso.ofComponents (fun f => Iso.refl _) (by simp)
  counitIso := NatIso.ofComponents (fun f => Iso.refl _) (by intros; ext; all_goals simp)

end

section

variable {C' : Type u₃} [Category.{v₃} C'] {D' : Type u₄} [Category.{v₄} D']
  (S : C ⥤ D) (S' : C' ⥤ D') (T : D) (T' : D')

@[reassoc (attr := simp)]
/--
theorem `CostructuredArrow.w_prod_fst` / 定理 `CostructuredArrow.w_prod_fst`

English:
theorem CostructuredArrow.w_prod_fst
  given: {A B : CostructuredArrow (S.prod S') (T, T')} (f : A ⟶ B)
  proof: congr_arg _root_.Prod.fst (CostructuredArrow.w f)

@[reassoc (attr := simp)]

中文:
定理 CostructuredArrow.w_prod_fst
  条件: {A B : CostructuredArrow (S.乘积 S') (T, T')} (f : A ⟶ B)
  证明: congr_arg _root_.Prod.fst (CostructuredArrow.w f)

@[reassoc (attr := simp)]

Depends on / 依赖: CostructuredArrow, CostructuredArrow.w, _root_, _root_.Prod.fst, congr_arg
-/
theorem CostructuredArrow.w_prod_fst {A B : CostructuredArrow (S.prod S') (T, T')} (f : A ⟶ B) :
    S.map f.left.1 ≫ B.hom.1 = A.hom.1 :=
  congr_arg _root_.Prod.fst (CostructuredArrow.w f)

@[reassoc (attr := simp)]
/--
theorem `CostructuredArrow.w_prod_snd` / 定理 `CostructuredArrow.w_prod_snd`

English:
theorem CostructuredArrow.w_prod_snd
  given: {A B : CostructuredArrow (S.prod S') (T, T')} (f : A ⟶ B)
  proof: congr_arg _root_.Prod.snd (CostructuredArrow.w f)

中文:
定理 CostructuredArrow.w_prod_snd
  条件: {A B : CostructuredArrow (S.乘积 S') (T, T')} (f : A ⟶ B)
  证明: congr_arg _root_.Prod.snd (CostructuredArrow.w f)

Depends on / 依赖: CostructuredArrow, CostructuredArrow.w, _root_, _root_.Prod.snd, congr_arg
-/
theorem CostructuredArrow.w_prod_snd {A B : CostructuredArrow (S.prod S') (T, T')} (f : A ⟶ B) :
    S'.map f.left.2 ≫ B.hom.2 = A.hom.2 :=
  congr_arg _root_.Prod.snd (CostructuredArrow.w f)

set_option backward.isDefEq.respectTransparency.types false in
/-- Implementation; see `CostructuredArrow.prodEquivalence`. -/
@[simps]
/--
Definition of `CostructuredArrow.prodFunctor` / `CostructuredArrow.prodFunctor` 的定义

English:
definition CostructuredArrow.prodFunctor
  signature: :
  body: ⟨.mk f.hom.1, .mk f.hom.2⟩
  map η := ⟨CostructuredArrow.homMk η.left.1 (by simp),
            CostructuredArrow.homMk η.left.2 (by simp)⟩

中文:
定义 CostructuredArrow.prodFunctor
  签名: :
  定义体: ⟨.mk f.hom.1, .mk f.hom.2⟩
  map η := ⟨CostructuredArrow.homMk η.left.1 (by simp),
            CostructuredArrow.homMk η.left.2 (by simp)⟩

Depends on / 依赖: f.hom
-/
def CostructuredArrow.prodFunctor :
    CostructuredArrow (S.prod S') (T, T') ⥤ CostructuredArrow S T × CostructuredArrow S' T' where
  obj f := ⟨.mk f.hom.1, .mk f.hom.2⟩
  map η := ⟨CostructuredArrow.homMk η.left.1 (by simp),
            CostructuredArrow.homMk η.left.2 (by simp)⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Implementation; see `CostructuredArrow.prodEquivalence`. -/
@[simps]
/--
Definition of `CostructuredArrow.prodInverse` / `CostructuredArrow.prodInverse` 的定义

English:
definition CostructuredArrow.prodInverse
  signature: :
  body: .mk (Y := (f.1.left, f.2.left)) ⟨f.1.hom, f.2.hom⟩
  map η := CostructuredArrow.homMk ⟨η.1.left, η.2.left⟩ (by simp)

中文:
定义 CostructuredArrow.prodInverse
  签名: :
  定义体: .mk (Y := (f.1.left, f.2.left)) ⟨f.1.hom, f.2.hom⟩
  map η := CostructuredArrow.homMk ⟨η.1.left, η.2.left⟩ (by simp)
-/
def CostructuredArrow.prodInverse :
    CostructuredArrow S T × CostructuredArrow S' T' ⥤ CostructuredArrow (S.prod S') (T, T') where
  obj f := .mk (Y := (f.1.left, f.2.left)) ⟨f.1.hom, f.2.hom⟩
  map η := CostructuredArrow.homMk ⟨η.1.left, η.2.left⟩ (by simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The natural equivalence
`CostructuredArrow (S.prod S') (T, T') ≌ CostructuredArrow S T × CostructuredArrow S' T'`. -/
@[simps]
/--
Definition of `CostructuredArrow.prodEquivalence` / `CostructuredArrow.prodEquivalence` 的定义

English:
definition CostructuredArrow.prodEquivalence
  signature: :
  body: CostructuredArrow.prodFunctor S S' T T'
  inverse := CostructuredArrow.prodInverse S S' T T'
  unitIso := NatIso.ofComponents (fun f => Iso.refl _) (by simp)
  counitIso := NatIso.ofComponents (fun f => Iso.refl _) (by intros; ext; all_goals simp)

中文:
定义 CostructuredArrow.prodEquivalence
  签名: :
  定义体: CostructuredArrow.prodFunctor S S' T T'
  inverse := CostructuredArrow.prodInverse S S' T T'
  unitIso := NatIso.ofComponents (fun f => Iso.refl _) (by simp)
  counitIso := NatIso.ofComponents (fun f => Iso.refl _) (by intros; ext; all_goals simp)

Depends on / 依赖: CostructuredArrow, CostructuredArrow.prodFunctor, prodFunctor
-/
def CostructuredArrow.prodEquivalence :
    CostructuredArrow (S.prod S') (T, T') ≌ CostructuredArrow S T × CostructuredArrow S' T' where
  functor := CostructuredArrow.prodFunctor S S' T T'
  inverse := CostructuredArrow.prodInverse S S' T T'
  unitIso := NatIso.ofComponents (fun f => Iso.refl _) (by simp)
  counitIso := NatIso.ofComponents (fun f => Iso.refl _) (by intros; ext; all_goals simp)

end

end Prod

namespace Comma

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  {T : Type u₃} [Category.{v₃} T] (L : A ⥤ T) (R : B ⥤ T)

set_option backward.defeqAttrib.useBackward true in
/-- The functor from the costructured arrow category on `snd L R` over `b : B` to the
costructured arrow category on `L` over `R.obj b`. It is left adjoint to
`costructuredArrowSndInclusion`, see `costructuredArrowSndAdjunction`. -/
@[simps]
/--
Definition of `costructuredArrowSndProj` / `costructuredArrowSndProj` 的定义

English:
definition costructuredArrowSndProj
  signature: (b : B)
  body: CostructuredArrow.mk (X.left.hom ≫ R.map X.hom)
map f := CostructuredArrow.homMk f.left.left by
    dsimp
    rw [reassoc_of% f.left.w]; rw [← R.map_comp]; rw [dsimp% CostructuredArrow.w f]

中文:
定义 costructuredArrowSndProj
  签名: (b : B)
  定义体: CostructuredArrow.mk (X.left.hom ≫ R.map X.hom)
map f := CostructuredArrow.homMk f.left.left by
    dsimp
    rw [reassoc_of% f.left.w]; rw [← R.map_comp]; rw [dsimp% CostructuredArrow.w f]

Depends on / 依赖: CostructuredArrow, CostructuredArrow.mk, CreatesColimitsOfShape, Ind.equivalence, ObjectProperty, R.map, X.hom, X.left.hom, equivalence, functor
-/
def costructuredArrowSndProj (b : B) :
    CostructuredArrow (snd L R) b ⥤ CostructuredArrow L (R.obj b) where
  obj X := CostructuredArrow.mk (X.left.hom ≫ R.map X.hom)
map f := CostructuredArrow.homMk f.left.left by
    dsimp
    rw [reassoc_of% f.left.w]; rw [← R.map_comp]; rw [dsimp% CostructuredArrow.w f]

set_option backward.defeqAttrib.useBackward true in
/-- The functor from the costructured arrow category on `L` over `R.obj b` to the costructured
arrow category on `snd L R` over `b : B`. -/
@[simps]
/--
Definition of `costructuredArrowSndInclusion` / `costructuredArrowSndInclusion` 的定义

English:
definition costructuredArrowSndInclusion
  signature: (b : B)
  body: ⟨⟨X.left, b, X.hom⟩, ⟨⟨⟩⟩, 𝟙 b⟩
  map f := CostructuredArrow.homMk ⟨f.left, 𝟙 b, by simp⟩ (by simp)

中文:
定义 costructuredArrowSndInclusion
  签名: (b : B)
  定义体: ⟨⟨X.left, b, X.hom⟩, ⟨⟨⟩⟩, 𝟙 b⟩
  map f := CostructuredArrow.homMk ⟨f.left, 𝟙 b, by simp⟩ (by simp)

Depends on / 依赖: X.hom, X.left
-/
def costructuredArrowSndInclusion (b : B) :
    CostructuredArrow L (R.obj b) ⥤ CostructuredArrow (snd L R) b where
  obj X := ⟨⟨X.left, b, X.hom⟩, ⟨⟨⟩⟩, 𝟙 b⟩
  map f := CostructuredArrow.homMk ⟨f.left, 𝟙 b, by simp⟩ (by simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The functor `costructuredArrowSndProj` is left adjoint to `costructuredArrowSndInclusion`. -/
@[simps]
/--
Definition of `costructuredArrowSndAdjunction` / `costructuredArrowSndAdjunction` 的定义

English:
definition costructuredArrowSndAdjunction
  signature: (b : B)
  body: CostructuredArrow.homMk ⟨𝟙 X.left.left, X.hom, by simp⟩ (by simp)
  unit.naturality _ _ f := by
    have := CostructuredArrow.w f
    cat_disch
  counit.app X := CostructuredArrow.homMk (𝟙 X.left) (by simp)

中文:
定义 costructuredArrowSndAdjunction
  签名: (b : B)
  定义体: CostructuredArrow.homMk ⟨𝟙 X.left.left, X.hom, by simp⟩ (by simp)
  unit.naturality _ _ f := by
    have := CostructuredArrow.w f
    cat_disch
  counit.app X := CostructuredArrow.homMk (𝟙 X.left) (by simp)

Depends on / 依赖: CostructuredArrow, CostructuredArrow.homMk, Discrete, X.hom, X.left.left
-/
def costructuredArrowSndAdjunction (b : B) :
    costructuredArrowSndProj L R b ⊣ costructuredArrowSndInclusion L R b where
  unit.app X := CostructuredArrow.homMk ⟨𝟙 X.left.left, X.hom, by simp⟩ (by simp)
  unit.naturality _ _ f := by
    have := CostructuredArrow.w f
    cat_disch
  counit.app X := CostructuredArrow.homMk (𝟙 X.left) (by simp)

end Comma

end CategoryTheory
