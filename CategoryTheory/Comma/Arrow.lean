/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Comma.Basic

/-!
# The category of arrows

The category of arrows, with morphisms commutative squares.
We set this up as a specialization of the comma category `Comma L R`,
where `L` and `R` are both the identity functor.

## Tags

comma, arrow
-/

@[expose] public section

namespace CategoryTheory

universe v u

-- morphism levels before object levels. See note [category theory universes].
variable {T : Type u} [Category.{v} T]

variable (T) in
/--
Definition of `Arrow` / `Arrow` 的定义

English:
definition Arrow
  body: Comma (𝟭 T) (𝟭 T)

to_dual_name_hint Left Right

中文:
定义 箭头
  定义体: Comma (𝟭 T) (𝟭 T)

to_dual_name_hint Left Right
-/
def Arrow := Comma (𝟭 T) (𝟭 T)

to_dual_name_hint Left Right

/-- The type of morphisms in the category `Arrow T`. -/
@[to_dual self (reorder := f g)]
/--
Definition of `Arrow.Hom` / `Arrow.Hom` 的定义

English:
definition Arrow.Hom
  signature: (f g : Arrow T)
  body: CommaMorphism f g

中文:
定义 箭头.态射
  签名: (f g : 箭头 T)
  定义体: CommaMorphism f g
-/
protected def Arrow.Hom (f g : Arrow T) := CommaMorphism f g

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Quiver (Arrow T)
  body: Arrow.Hom

中文:
实例 :
  签名: 箭图 (箭头 T)
  定义体: Arrow.Hom

Depends on / 依赖: Arrow.Hom
-/
instance : Quiver (Arrow T) where
  Hom := Arrow.Hom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (Arrow T)
  body: inferInstanceAs Category (Comma (𝟭 T) (𝟭 T))

中文:
实例 :
  签名: 范畴 (箭头 T)
  定义体: inferInstanceAs Category (Comma (𝟭 T) (𝟭 T))

Depends on / 依赖: Category
-/
instance : Category (Arrow T) :=
inferInstanceAs Category (Comma (𝟭 T) (𝟭 T))

namespace Arrow

/-- The left object of an arrow. -/
@[to_dual /-- The right object of an arrow. -/]
/--
Definition of `left` / `left` 的定义

English:
abbreviation left
  signature: (X : Arrow T)
  body: Comma.left X

中文:
缩写 left
  签名: (X : 箭头 T)
  定义体: Comma.left X

Depends on / 依赖: Comma.left
-/
abbrev left (X : Arrow T) : T := Comma.left X

/--
Definition of `hom` / `hom` 的定义

English:
abbreviation hom
  signature: (X : Arrow T)
  body: Comma.hom X

中文:
缩写 hom
  签名: (X : 箭头 T)
  定义体: Comma.hom X

Depends on / 依赖: Comma.hom
-/
abbrev hom (X : Arrow T) : X.left ⟶ X.right := Comma.hom X

/-- The left part of a morphism in the category of arrows. -/
@[to_dual /-- The right part of a morphism in the category of arrows. -/]
/--
Definition of `Hom.left` / `Hom.left` 的定义

English:
abbreviation Hom.left
  signature: {X Y : Arrow T} (f : X ⟶ Y)
  body: CommaMorphism.left f

@[ext, to_dual self (reorder := X Y, h₁ h₂)]

中文:
缩写 态射.left
  签名: {X Y : 箭头 T} (f : X ⟶ Y)
  定义体: CommaMorphism.left f

@[ext, to_dual self (reorder := X Y, h₁ h₂)]

Depends on / 依赖: CommaMorphism, CommaMorphism.left
-/
abbrev Hom.left {X Y : Arrow T} (f : X ⟶ Y) : X.left ⟶ Y.left := CommaMorphism.left f

@[ext, to_dual self (reorder := X Y, h₁ h₂)]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {X Y : Arrow T} (f g : X ⟶ Y) (h₁ : f.left = g.left) (h₂ : f.right = g.right)
  proof: CommaMorphism.ext h₁ h₂

@[to_dual (attr := simp)]

中文:
引理 hom_ext
  条件: {X Y : 箭头 T} (f g : X ⟶ Y) (h₁ : f.left = g.left) (h₂ : f.right = g.right)
  证明: CommaMorphism.ext h₁ h₂

@[to_dual (attr := simp)]

Depends on / 依赖: CommaMorphism, CommaMorphism.ext
-/
lemma hom_ext {X Y : Arrow T} (f g : X ⟶ Y) (h₁ : f.left = g.left) (h₂ : f.right = g.right) :
    f = g :=
  CommaMorphism.ext h₁ h₂

@[to_dual (attr := simp)]
/--
theorem `id_left` / 定理 `id_left`

English:
theorem id_left
  given: (f : Arrow T)
  statement: Arrow.Hom.left (𝟙 f) = 𝟙 f.left
  proof: rfl

@[to_dual (reorder := f g) (attr := simp, reassoc)]

中文:
定理 id_left
  条件: (f : 箭头 T)
  结论: 箭头.态射.left (𝟙 f) = 𝟙 f.left
  证明: rfl

@[to_dual (reorder := f g) (attr := simp, reassoc)]
-/
theorem id_left (f : Arrow T) : Arrow.Hom.left (𝟙 f) = 𝟙 f.left :=
  rfl

@[to_dual (reorder := f g) (attr := simp, reassoc)]
/--
theorem `comp_left` / 定理 `comp_left`

English:
theorem comp_left
  given: {X Y Z : Arrow T} (f : X ⟶ Y) (g : Y ⟶ Z)
  proof: rfl

中文:
定理 comp_left
  条件: {X Y Z : 箭头 T} (f : X ⟶ Y) (g : Y ⟶ Z)
  证明: rfl
-/
theorem comp_left {X Y Z : Arrow T} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).left = f.left ≫ g.left := rfl

/-- An object in the arrow category is simply a morphism in `T`. -/
@[simps, to_dual self, implicit_reducible]
/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: {X Y : T} (f : X ⟶ Y)
  body: X
  right := Y
  hom := f

中文:
定义 mk
  签名: {X Y : T} (f : X ⟶ Y)
  定义体: X
  right := Y
  hom := f
-/
def mk {X Y : T} (f : X ⟶ Y) : Arrow T where
  left := X
  right := Y
  hom := f

attribute [to_dual existing] mk_left
attribute [to_dual self] mk_hom

@[simp]
/--
theorem `mk_eq` / 定理 `mk_eq`

English:
theorem mk_eq
  given: (f : Arrow T)
  statement: Arrow.mk f.hom = f
  proof: by
  cases f
  rfl

@[to_dual none]

中文:
定理 mk_eq
  条件: (f : 箭头 T)
  结论: 箭头.mk f.hom = f
  证明: by
  cases f
  rfl

@[to_dual none]
-/
theorem mk_eq (f : Arrow T) : Arrow.mk f.hom = f := by
  cases f
  rfl

@[to_dual none]
/--
lemma `mk_surjective` / 引理 `mk_surjective`

English:
lemma mk_surjective
  given: (f : Arrow T)
  proof: ⟨_, _, f.hom, rfl⟩

@[to_dual self]

中文:
引理 mk_surjective
  条件: (f : 箭头 T)
  证明: ⟨_, _, f.hom, rfl⟩

@[to_dual self]

Depends on / 依赖: f.hom
-/
lemma mk_surjective (f : Arrow T) :
    exists (X Y : T) (g : X ⟶ Y), f = Arrow.mk g :=
  ⟨_, _, f.hom, rfl⟩

@[to_dual self]
/--
theorem `mk_injective` / 定理 `mk_injective`

English:
theorem mk_injective
  given: (A B : T)
  proof: fun f g h => by
  cases h
  rfl

@[to_dual self]

中文:
定理 mk_injective
  条件: (A B : T)
  证明: fun f g h => by
  cases h
  rfl

@[to_dual self]
-/
theorem mk_injective (A B : T) :
    Function.Injective (Arrow.mk : (A ⟶ B) -> Arrow T) := fun f g h => by
  cases h
  rfl

@[to_dual self]
/--
theorem `mk_inj` / 定理 `mk_inj`

English:
theorem mk_inj
  given: (A B : T) {f g : A ⟶ B}
  statement: Arrow.mk f = Arrow.mk g ↔ f = g
  proof: (mk_injective A B).eq_iff

@[to_dual self]

中文:
定理 mk_inj
  条件: (A B : T) {f g : A ⟶ B}
  结论: 箭头.mk f = 箭头.mk g ↔ f = g
  证明: (mk_injective A B).eq_iff

@[to_dual self]

Depends on / 依赖: eq_iff, mk_injective
-/
theorem mk_inj (A B : T) {f g : A ⟶ B} : Arrow.mk f = Arrow.mk g ↔ f = g :=
  (mk_injective A B).eq_iff

@[to_dual self]
instance {X Y : T} : CoeOut (X ⟶ Y) (Arrow T) where
  coe := mk

@[to_dual none, reassoc (attr := simp high)]
/--
theorem `w` / 定理 `w`

English:
theorem w
  given: {f g : Arrow T} (sq : f ⟶ g)
  statement: sq.left ≫ g.hom = f.hom ≫ sq.right
  proof: CommaMorphism.w sq

@[to_dual none, reassoc]
alias Hom.w := w

@[to_dual]

中文:
定理 w
  条件: {f g : 箭头 T} (sq : f ⟶ g)
  结论: sq.left ≫ g.hom = f.hom ≫ sq.right
  证明: CommaMorphism.w sq

@[to_dual none, reassoc]
alias Hom.w := w

@[to_dual]

Depends on / 依赖: CommaMorphism, CommaMorphism.w
-/
theorem w {f g : Arrow T} (sq : f ⟶ g) : sq.left ≫ g.hom = f.hom ≫ sq.right :=
  CommaMorphism.w sq

@[to_dual none, reassoc]
alias Hom.w := w

@[to_dual]
/--
theorem `hom.congr_left` / 定理 `hom.congr_left`

English:
theorem hom.congr_left
  given: {f g : Arrow T} {φ₁ φ₂ : f ⟶ g} (h : φ₁ = φ₂)
  statement: φ₁.left = φ₂.left
  proof: by
  rw [h]

@[to_dual none]

中文:
定理 hom.congr_left
  条件: {f g : 箭头 T} {φ₁ φ₂ : f ⟶ g} (h : φ₁ = φ₂)
  结论: φ₁.left = φ₂.left
  证明: by
  rw [h]

@[to_dual none]
-/
theorem hom.congr_left {f g : Arrow T} {φ₁ φ₂ : f ⟶ g} (h : φ₁ = φ₂) : φ₁.left = φ₂.left := by
  rw [h]

@[to_dual none]
/--
theorem `iso_w` / 定理 `iso_w`

English:
theorem iso_w
  given: {f g : Arrow T} (e : f ≅ g)
  statement: g.hom = e.inv.left ≫ f.hom ≫ e.hom.right
  proof: by
  simp [← Arrow.comp_right]

@[to_dual none]

中文:
定理 iso_w
  条件: {f g : 箭头 T} (e : f ≅ g)
  结论: g.hom = e.inv.left ≫ f.hom ≫ e.hom.right
  证明: by
  simp [← Arrow.comp_right]

@[to_dual none]

Depends on / 依赖: Arrow.comp_right, comp_right
-/
theorem iso_w {f g : Arrow T} (e : f ≅ g) : g.hom = e.inv.left ≫ f.hom ≫ e.hom.right := by
  simp [← Arrow.comp_right]

@[to_dual none]
/--
theorem `iso_w'` / 定理 `iso_w'`

English:
theorem iso_w'
  given: {W X Y Z : T} {f : W ⟶ X} {g : Y ⟶ Z} (e : Arrow.mk f ≅ Arrow.mk g)
  proof: iso_w e

中文:
定理 iso_w'
  条件: {W X Y Z : T} {f : W ⟶ X} {g : Y ⟶ Z} (e : 箭头.mk f ≅ 箭头.mk g)
  证明: iso_w e

Depends on / 依赖: iso_w
-/
theorem iso_w' {W X Y Z : T} {f : W ⟶ X} {g : Y ⟶ Z} (e : Arrow.mk f ≅ Arrow.mk g) :
    g = e.inv.left ≫ f ≫ e.hom.right :=
  iso_w e

/--
lemma `eqToHom_left` / 引理 `eqToHom_left`

English:
lemma eqToHom_left
  given: {X Y : Arrow T} (h : X = Y)
  proof: by subst h; rfl

中文:
引理 eqToHom_left
  条件: {X Y : 箭头 T} (h : X = Y)
  证明: by subst h; rfl
-/
lemma eqToHom_left {X Y : Arrow T} (h : X = Y) :
    (eqToHom h).left = eqToHom (by rw [h]) := by subst h; rfl

/--
lemma `eqToHom_right` / 引理 `eqToHom_right`

English:
lemma eqToHom_right
  given: {X Y : Arrow T} (h : X = Y)
  proof: by subst h; rfl

中文:
引理 eqToHom_right
  条件: {X Y : 箭头 T} (h : X = Y)
  证明: by subst h; rfl
-/
lemma eqToHom_right {X Y : Arrow T} (h : X = Y) :
    (eqToHom h).right = eqToHom (by rw [h]) := by subst h; rfl

/--
lemma `mk_eq_mk_iff` / 引理 `mk_eq_mk_iff`

English:
lemma mk_eq_mk_iff
  given: {X Y X' Y' : T} (f : X ⟶ Y) (f' : X' ⟶ Y')
  proof: by
  constructor
  · intro h
    refine ⟨congr_arg Arrow.left h, congr_arg Arrow.right h, ?_⟩
    simpa [eqToHom_left, eqToHom_right] using! iso_w (eqToIso h.symm)
  · rintro ⟨rfl, rfl, h⟩
    simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at h
    rw [h]

中文:
引理 mk_eq_mk_iff
  条件: {X Y X' Y' : T} (f : X ⟶ Y) (f' : X' ⟶ Y')
  证明: by
  constructor
  · intro h
    refine ⟨congr_arg Arrow.left h, congr_arg Arrow.right h, ?_⟩
    simpa [eqToHom_left, eqToHom_right] using! iso_w (eqToIso h.symm)
  · rintro ⟨rfl, rfl, h⟩
    simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at h
    rw [h]

Depends on / 依赖: Arrow.left, Arrow.right, Category, Category.comp_id, Category.id_comp, comp_id, congr_arg, eqToHom_left, eqToHom_refl, eqToHom_right, eqToIso, h.symm, id_comp, iso_w
-/
lemma mk_eq_mk_iff {X Y X' Y' : T} (f : X ⟶ Y) (f' : X' ⟶ Y') :
    Arrow.mk f = Arrow.mk f' ↔
      exists (hX : X = X') (hY : Y = Y'), f = eqToHom hX ≫ f' ≫ eqToHom hY.symm := by
  constructor
  · intro h
    refine ⟨congr_arg Arrow.left h, congr_arg Arrow.right h, ?_⟩
    simpa [eqToHom_left, eqToHom_right] using! iso_w (eqToIso h.symm)
  · rintro ⟨rfl, rfl, h⟩
    simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at h
    rw [h]

/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  statement: {f g : Arrow T}
  proof: (mk_eq_mk_iff _ _).2 (by simp_all)

中文:
引理 ext
  结论: {f g : 箭头 T}
  证明: (mk_eq_mk_iff _ _).2 (by simp_all)

Depends on / 依赖: mk_eq_mk_iff
-/
lemma ext {f g : Arrow T}
    (h₁ : f.left = g.left) (h₂ : f.right = g.right)
    (h₃ : f.hom = eqToHom h₁ ≫ g.hom ≫ eqToHom h₂.symm) : f = g :=
  (mk_eq_mk_iff _ _).2 (by simp_all)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `arrow_mk_comp_eqToHom` / 引理 `arrow_mk_comp_eqToHom`

English:
lemma arrow_mk_comp_eqToHom
  given: {X Y Y' : T} (f : X ⟶ Y) (h : Y = Y')
  proof: ext rfl h.symm (by simp)

中文:
引理 arrow_mk_comp_eqToHom
  条件: {X Y Y' : T} (f : X ⟶ Y) (h : Y = Y')
  证明: ext rfl h.symm (by simp)

Depends on / 依赖: h.symm
-/
lemma arrow_mk_comp_eqToHom {X Y Y' : T} (f : X ⟶ Y) (h : Y = Y') :
    Arrow.mk (f ≫ eqToHom h) = Arrow.mk f :=
  ext rfl h.symm (by simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `arrow_mk_eqToHom_comp` / 引理 `arrow_mk_eqToHom_comp`

English:
lemma arrow_mk_eqToHom_comp
  given: {X' X Y : T} (f : X ⟶ Y) (h : X' = X)
  proof: ext h rfl (by simp)

中文:
引理 arrow_mk_eqToHom_comp
  条件: {X' X Y : T} (f : X ⟶ Y) (h : X' = X)
  证明: ext h rfl (by simp)
-/
lemma arrow_mk_eqToHom_comp {X' X Y : T} (f : X ⟶ Y) (h : X' = X) :
    Arrow.mk (eqToHom h ≫ f) = Arrow.mk f :=
  ext h rfl (by simp)

/-- A morphism in the arrow category is a commutative square connecting two objects of the arrow
    category. -/
@[simps]
/--
Definition of `homMk` / `homMk` 的定义

English:
definition homMk
  signature: {f g : Arrow T} (u : f.left ⟶ g.left) (v : f.right ⟶ g.right)
  body: u
  right := v
  w := w

中文:
定义 homMk
  签名: {f g : 箭头 T} (u : f.left ⟶ g.left) (v : f.right ⟶ g.right)
  定义体: u
  right := v
  w := w

Depends on / 依赖: cat_disch
-/
def homMk {f g : Arrow T} (u : f.left ⟶ g.left) (v : f.right ⟶ g.right)
    (w : u ≫ g.hom = f.hom ≫ v := by cat_disch) : f ⟶ g where
  left := u
  right := v
  w := w

/-- `homMk''` is the dual of `homMk`, which we need for `to_dual`.
Please avoid using this directly. -/
@[to_dual existing homMk]
/--
Definition of `homMk''` / `homMk''` 的定义

English:
abbreviation homMk''
  signature: {f g : Arrow T} (u : g.right ⟶ f.right) (v : g.left ⟶ f.left)
  body: homMk v u

中文:
缩写 homMk''
  签名: {f g : 箭头 T} (u : g.right ⟶ f.right) (v : g.left ⟶ f.left)
  定义体: homMk v u

Depends on / 依赖: attribute, cat_disch, homMk_left, homMk_right, to_dual
-/
abbrev homMk'' {f g : Arrow T} (u : g.right ⟶ f.right) (v : g.left ⟶ f.left)
    (w : g.hom ≫ u = v ≫ f.hom := by cat_disch) : g ⟶ f :=
  homMk v u
attribute [to_dual none] homMk_left homMk_right

/-- We can also build a morphism in the arrow category out of any commutative square in `T`. -/
@[simps]
/--
Definition of `homMk'` / `homMk'` 的定义

English:
definition homMk'
  signature: {X Y : T} {f : X ⟶ Y} {P Q : T} {g : P ⟶ Q} (u : X ⟶ P) (v : Y ⟶ Q)
  body: u
  right := v
  w := w

中文:
定义 homMk'
  签名: {X Y : T} {f : X ⟶ Y} {P Q : T} {g : P ⟶ Q} (u : X ⟶ P) (v : Y ⟶ Q)
  定义体: u
  right := v
  w := w

Depends on / 依赖: Arrow.mk, cat_disch
-/
def homMk' {X Y : T} {f : X ⟶ Y} {P Q : T} {g : P ⟶ Q} (u : X ⟶ P) (v : Y ⟶ Q)
    (w : u ≫ g = f ≫ v := by cat_disch) :
    Arrow.mk f ⟶ Arrow.mk g where
  left := u
  right := v
  w := w

/-- `homMk'''` is the dual of `homMk'`, which we need for `to_dual`.
Please avoid using this directly. -/
@[to_dual existing homMk']
/--
Definition of `homMk'''` / `homMk'''` 的定义

English:
abbreviation homMk'''
  signature: {X Y : T} {f : Y ⟶ X} {P Q : T} {g : Q ⟶ P} (u : P ⟶ X) (v : Q ⟶ Y)
  body: homMk' v u

中文:
缩写 homMk'''
  签名: {X Y : T} {f : Y ⟶ X} {P Q : T} {g : Q ⟶ P} (u : P ⟶ X) (v : Q ⟶ Y)
  定义体: homMk' v u

Depends on / 依赖: _left, attribute, cat_disch, to_dual
-/
abbrev homMk''' {X Y : T} {f : Y ⟶ X} {P Q : T} {g : Q ⟶ P} (u : P ⟶ X) (v : Q ⟶ Y)
    (w : g ≫ u = v ≫ f := by cat_disch) : mk g ⟶ mk f :=
  homMk' v u
attribute [to_dual none] homMk'_left

set_option backward.defeqAttrib.useBackward true in
@[to_dual none, reassoc]
/--
theorem `w_mk_left` / 定理 `w_mk_left`

English:
theorem w_mk_left
  given: {X Y : T} {f : X ⟶ Y} {g : Arrow T} (sq : mk f ⟶ g)
  proof: sq.w

中文:
定理 w_mk_left
  条件: {X Y : T} {f : X ⟶ Y} {g : 箭头 T} (sq : mk f ⟶ g)
  证明: sq.w

Depends on / 依赖: sq.w
-/
theorem w_mk_left {X Y : T} {f : X ⟶ Y} {g : Arrow T} (sq : mk f ⟶ g) :
    dsimp% sq.left ≫ g.hom = f ≫ sq.right :=
  sq.w

set_option backward.defeqAttrib.useBackward true in
@[to_dual none, reassoc (attr := simp)]
/--
theorem `w_mk_right` / 定理 `w_mk_right`

English:
theorem w_mk_right
  given: {f : Arrow T} {X Y : T} {g : X ⟶ Y} (sq : f ⟶ mk g)
  proof: sq.w

中文:
定理 w_mk_right
  条件: {f : 箭头 T} {X Y : T} {g : X ⟶ Y} (sq : f ⟶ mk g)
  证明: sq.w

Depends on / 依赖: sq.w
-/
theorem w_mk_right {f : Arrow T} {X Y : T} {g : X ⟶ Y} (sq : f ⟶ mk g) :
    dsimp% sq.left ≫ g = f.hom ≫ sq.right :=
  sq.w

set_option backward.defeqAttrib.useBackward true in
@[to_dual none, reassoc]
/--
theorem `w_mk` / 定理 `w_mk`

English:
theorem w_mk
  given: {X Y X' Y' : T} {f : X ⟶ Y} {g : X' ⟶ Y'} (sq : mk f ⟶ mk g)
  proof: sq.w

@[to_dual self (reorder := f g, 6 7)]

中文:
定理 w_mk
  条件: {X Y X' Y' : T} {f : X ⟶ Y} {g : X' ⟶ Y'} (sq : mk f ⟶ mk g)
  证明: sq.w

@[to_dual self (reorder := f g, 6 7)]

Depends on / 依赖: sq.w
-/
theorem w_mk {X Y X' Y' : T} {f : X ⟶ Y} {g : X' ⟶ Y'} (sq : mk f ⟶ mk g) :
    dsimp% sq.left ≫ g = f ≫ sq.right :=
  sq.w

@[to_dual self (reorder := f g, 6 7)]
/--
theorem `isIso_of_isIso_left_of_isIso_right` / 定理 `isIso_of_isIso_left_of_isIso_right`

English:
theorem isIso_of_isIso_left_of_isIso_right
  statement: {f g : Arrow T} (ff : f ⟶ g) [IsIso ff.left]
  proof: ⟨homMk (inv ff.left) (inv ff.right), by cat_disch⟩

中文:
定理 isIso_of_isIso_left_of_isIso_right
  结论: {f g : 箭头 T} (ff : f ⟶ g) [是同构 ff.left]
  证明: ⟨homMk (inv ff.left) (inv ff.right), by cat_disch⟩

Depends on / 依赖: cat_disch, ff.left, ff.right
-/
theorem isIso_of_isIso_left_of_isIso_right {f g : Arrow T} (ff : f ⟶ g) [IsIso ff.left]
    [IsIso ff.right] : IsIso ff where
  out := ⟨homMk (inv ff.left) (inv ff.right), by cat_disch⟩

/-- Create an isomorphism between arrows,
by providing isomorphisms between the domains and codomains,
and a proof that the square commutes. -/
@[simps!]
/--
Definition of `isoMk` / `isoMk` 的定义

English:
definition isoMk
  signature: {f g : Arrow T} (l : f.left ≅ g.left) (r : f.right ≅ g.right)
  body: Comma.isoMk l r h

中文:
定义 isoMk
  签名: {f g : 箭头 T} (l : f.left ≅ g.left) (r : f.right ≅ g.right)
  定义体: Comma.isoMk l r h

Depends on / 依赖: Comma.isoMk, cat_disch
-/
def isoMk {f g : Arrow T} (l : f.left ≅ g.left) (r : f.right ≅ g.right)
    (h : l.hom ≫ g.hom = f.hom ≫ r.hom := by cat_disch) : f ≅ g :=
  Comma.isoMk l r h

/-- `isoMk''` is the dual of `isoMk`, which we need for `to_dual`.
Please avoid using this directly. -/
@[to_dual existing isoMk]
/--
Definition of `isoMk''` / `isoMk''` 的定义

English:
abbreviation isoMk''
  signature: {f g : Arrow T} (l : f.right ≅ g.right) (r : f.left ≅ g.left)
  body: isoMk r l (by rwa [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp] at h)

中文:
缩写 isoMk''
  签名: {f g : 箭头 T} (l : f.right ≅ g.right) (r : f.left ≅ g.left)
  定义体: isoMk r l (by rwa [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp] at h)

Depends on / 依赖: Category, Category.assoc, Iso.comp_inv_eq, Iso.eq_inv_comp, attribute, cat_disch, comp_inv_eq, eq_inv_comp, isoMk_hom_left, isoMk_hom_right, isoMk_inv_left, isoMk_inv_right, to_dual
-/
abbrev isoMk'' {f g : Arrow T} (l : f.right ≅ g.right) (r : f.left ≅ g.left)
    (h : g.hom ≫ l.inv = r.inv ≫ f.hom := by cat_disch) : f ≅ g :=
  isoMk r l (by rwa [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp] at h)
attribute [to_dual none] isoMk_hom_left isoMk_hom_right isoMk_inv_left isoMk_inv_right

/--
Definition of `isoMk'` / `isoMk'` 的定义

English:
abbreviation isoMk'
  signature: {W X Y Z : T} (f : W ⟶ X) (g : Y ⟶ Z) (e₁ : W ≅ Y) (e₂ : X ≅ Z)
  body: Arrow.isoMk e₁ e₂ h

中文:
缩写 isoMk'
  签名: {W X Y Z : T} (f : W ⟶ X) (g : Y ⟶ Z) (e₁ : W ≅ Y) (e₂ : X ≅ Z)
  定义体: Arrow.isoMk e₁ e₂ h

Depends on / 依赖: Arrow.isoMk, Arrow.mk, cat_disch
-/
abbrev isoMk' {W X Y Z : T} (f : W ⟶ X) (g : Y ⟶ Z) (e₁ : W ≅ Y) (e₂ : X ≅ Z)
    (h : e₁.hom ≫ g = f ≫ e₂.hom := by cat_disch) : Arrow.mk f ≅ Arrow.mk g :=
  Arrow.isoMk e₁ e₂ h

/-- `isoMk'''` is the dual of `isoMk'`, which we need for `to_dual`.
Please avoid using this directly. -/
@[to_dual existing isoMk']
/--
Definition of `isoMk'''` / `isoMk'''` 的定义

English:
abbreviation isoMk'''
  signature: {W X Y Z : T} (f : X ⟶ W) (g : Z ⟶ Y) (e₁ : W ≅ Y)
  body: isoMk' f g e₂ e₁ (by rwa [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp] at h)

中文:
缩写 isoMk'''
  签名: {W X Y Z : T} (f : X ⟶ W) (g : Z ⟶ Y) (e₁ : W ≅ Y)
  定义体: isoMk' f g e₂ e₁ (by rwa [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp] at h)

Depends on / 依赖: Category, Category.assoc, Iso.comp_inv_eq, Iso.eq_inv_comp, cat_disch, comp_inv_eq, eq_inv_comp
-/
abbrev isoMk''' {W X Y Z : T} (f : X ⟶ W) (g : Z ⟶ Y) (e₁ : W ≅ Y)
  (e₂ : X ≅ Z) (h : g ≫ e₁.inv = e₂.inv ≫ f := by cat_disch) : mk f ≅ mk g :=
  isoMk' f g e₂ e₁ (by rwa [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp] at h)

section

variable {f g : Arrow T} (sq : f ⟶ g)

@[to_dual]
/--
Instance `isIso_left` / 实例 `isIso_left`

English:
instance isIso_left
  signature: [IsIso sq]
  body: ⟨(inv sq).left, by simp [← comp_left]⟩

@[to_dual none]

中文:
实例 isIso_left
  签名: [是同构 sq]
  定义体: ⟨(inv sq).left, by simp [← comp_left]⟩

@[to_dual none]

Depends on / 依赖: comp_left
-/
instance isIso_left [IsIso sq] : IsIso sq.left :=
  ⟨(inv sq).left, by simp [← comp_left]⟩

@[to_dual none]
/--
lemma `isIso_of_isIso'` / 引理 `isIso_of_isIso'`

English:
lemma isIso_of_isIso'
  given: {f g : Arrow T} (sq : f ⟶ g) [IsIso sq] [IsIso f.hom]
  proof: by
  rw [iso_w (asIso sq)]
  infer_instance

@[to_dual none]

中文:
引理 isIso_of_isIso'
  条件: {f g : 箭头 T} (sq : f ⟶ g) [是同构 sq] [是同构 f.hom]
  证明: by
  rw [iso_w (asIso sq)]
  infer_instance

@[to_dual none]
-/
private lemma isIso_of_isIso' {f g : Arrow T} (sq : f ⟶ g) [IsIso sq] [IsIso f.hom] :
    IsIso g.hom := by
  rw [iso_w (asIso sq)]
  infer_instance

@[to_dual none]
/--
lemma `isIso_hom_iff_isIso_hom_of_isIso` / 引理 `isIso_hom_iff_isIso_hom_of_isIso`

English:
lemma isIso_hom_iff_isIso_hom_of_isIso
  given: {f g : Arrow T} (sq : f ⟶ g) [IsIso sq]
  proof: ⟨fun _ => isIso_of_isIso' sq, fun _ => isIso_of_isIso' (inv sq)⟩

@[to_dual none]

中文:
引理 isIso_hom_iff_isIso_hom_of_isIso
  条件: {f g : 箭头 T} (sq : f ⟶ g) [是同构 sq]
  证明: ⟨fun _ => isIso_of_isIso' sq, fun _ => isIso_of_isIso' (inv sq)⟩

@[to_dual none]

Depends on / 依赖: isIso_of_isIso
-/
lemma isIso_hom_iff_isIso_hom_of_isIso {f g : Arrow T} (sq : f ⟶ g) [IsIso sq] :
    IsIso f.hom ↔ IsIso g.hom :=
  ⟨fun _ => isIso_of_isIso' sq, fun _ => isIso_of_isIso' (inv sq)⟩

@[to_dual none]
/--
lemma `isIso_iff_isIso_of_isIso` / 引理 `isIso_iff_isIso_of_isIso`

English:
lemma isIso_iff_isIso_of_isIso
  given: {W X Y Z : T} {f : W ⟶ X} {g : Y ⟶ Z} (sq : mk f ⟶ mk g) [IsIso sq]
  proof: isIso_hom_iff_isIso_hom_of_isIso sq

@[to_dual none]

中文:
引理 isIso_iff_isIso_of_isIso
  条件: {W X Y Z : T} {f : W ⟶ X} {g : Y ⟶ Z} (sq : mk f ⟶ mk g) [是同构 sq]
  证明: isIso_hom_iff_isIso_hom_of_isIso sq

@[to_dual none]

Depends on / 依赖: isIso_hom_iff_isIso_hom_of_isIso
-/
lemma isIso_iff_isIso_of_isIso {W X Y Z : T} {f : W ⟶ X} {g : Y ⟶ Z} (sq : mk f ⟶ mk g) [IsIso sq] :
    IsIso f ↔ IsIso g :=
  isIso_hom_iff_isIso_hom_of_isIso sq

@[to_dual none]
/--
lemma `isIso_hom_iff_isIso_of_isIso` / 引理 `isIso_hom_iff_isIso_of_isIso`

English:
lemma isIso_hom_iff_isIso_of_isIso
  given: {Y Z : T} {f : Arrow T} {g : Y ⟶ Z} (sq : f ⟶ mk g) [IsIso sq]
  proof: isIso_hom_iff_isIso_hom_of_isIso sq

@[to_dual (attr := simp, push ←)]

中文:
引理 isIso_hom_iff_isIso_of_isIso
  条件: {Y Z : T} {f : 箭头 T} {g : Y ⟶ Z} (sq : f ⟶ mk g) [是同构 sq]
  证明: isIso_hom_iff_isIso_hom_of_isIso sq

@[to_dual (attr := simp, push ←)]

Depends on / 依赖: isIso_hom_iff_isIso_hom_of_isIso
-/
lemma isIso_hom_iff_isIso_of_isIso {Y Z : T} {f : Arrow T} {g : Y ⟶ Z} (sq : f ⟶ mk g) [IsIso sq] :
    IsIso f.hom ↔ IsIso g :=
  isIso_hom_iff_isIso_hom_of_isIso sq

@[to_dual (attr := simp, push ←)]
/--
theorem `inv_left` / 定理 `inv_left`

English:
theorem inv_left
  given: [IsIso sq]
  statement: (inv sq).left = inv sq.left
  proof: IsIso.eq_inv_of_hom_inv_id (by simp [← comp_left])

@[to_dual none]

中文:
定理 inv_left
  条件: [是同构 sq]
  结论: (inv sq).left = inv sq.left
  证明: IsIso.eq_inv_of_hom_inv_id (by simp [← comp_left])

@[to_dual none]

Depends on / 依赖: IsIso.eq_inv_of_hom_inv_id, Iso.refl, comp_left, eq_inv_of_hom_inv_id, isLeftKanExtension_of_preservesColimits
-/
theorem inv_left [IsIso sq] : (inv sq).left = inv sq.left :=
  IsIso.eq_inv_of_hom_inv_id (by simp [← comp_left])

@[to_dual none]
/--
theorem `left_hom_inv_right` / 定理 `left_hom_inv_right`

English:
theorem left_hom_inv_right
  given: [IsIso sq]
  statement: sq.left ≫ g.hom ≫ inv sq.right = f.hom
  proof: by
  simp only [← Category.assoc, IsIso.comp_inv_eq, w]

@[to_dual none]

中文:
定理 left_hom_inv_right
  条件: [是同构 sq]
  结论: sq.left ≫ g.hom ≫ inv sq.right = f.hom
  证明: by
  simp only [← Category.assoc, IsIso.comp_inv_eq, w]

@[to_dual none]

Depends on / 依赖: Category, Category.assoc, IsIso.comp_inv_eq, comp_inv_eq
-/
theorem left_hom_inv_right [IsIso sq] : sq.left ≫ g.hom ≫ inv sq.right = f.hom := by
  simp only [← Category.assoc, IsIso.comp_inv_eq, w]

@[to_dual none]
/--
theorem `inv_left_hom_right` / 定理 `inv_left_hom_right`

English:
theorem inv_left_hom_right
  given: [IsIso sq]
  statement: inv sq.left ≫ f.hom ≫ sq.right = g.hom
  proof: by
  simp only [w, IsIso.inv_comp_eq]

中文:
定理 inv_left_hom_right
  条件: [是同构 sq]
  结论: inv sq.left ≫ f.hom ≫ sq.right = g.hom
  证明: by
  simp only [w, IsIso.inv_comp_eq]

Depends on / 依赖: IsIso.inv_comp_eq, StructuredArrow, StructuredArrow.homMk, inv_comp_eq
-/
theorem inv_left_hom_right [IsIso sq] : inv sq.left ≫ f.hom ≫ sq.right = g.hom := by
  simp only [w, IsIso.inv_comp_eq]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[to_dual epi_right]
/--
Instance `mono_left` / 实例 `mono_left`

English:
instance mono_left
  signature: [Mono sq]
  body: by
    let aux : (Z ⟶ f.left) -> (Arrow.mk (𝟙 Z) ⟶ f) := fun φ =>
      { left := φ
        right := φ ≫ f.hom }
    have : forall g, (aux g).right = g ≫ f.hom := fun g => rfl
    change (aux φ).left = (aux ψ).left
    congr 1
    rw [← cancel_mono sq]
    ext
    · exact h
    · simp [this, ← Arrow.w_mk_right, reassoc_of% h]

@[to_dual (attr := reassoc (attr := simp))]

中文:
实例 mono_left
  签名: [单态射 sq]
  定义体: by
    let aux : (Z ⟶ f.left) -> (Arrow.mk (𝟙 Z) ⟶ f) := fun φ =>
      { left := φ
        right := φ ≫ f.hom }
    have : forall g, (aux g).right = g ≫ f.hom := fun g => rfl
    change (aux φ).left = (aux ψ).left
    congr 1
    rw [← cancel_mono sq]
    ext
    · exact h
    · simp [this, ← Arrow.w_mk_right, reassoc_of% h]

@[to_dual (attr := reassoc (attr := simp))]

Depends on / 依赖: Arrow.mk, Arrow.w_mk_right, IsInitial, Limits, Limits.IsInitial.ofUnique, cancel_mono, f.hom, f.left, ofUnique, reassoc_of, w_mk_right
-/
instance mono_left [Mono sq] : Mono sq.left where
  right_cancellation {Z} φ ψ h := by
    let aux : (Z ⟶ f.left) -> (Arrow.mk (𝟙 Z) ⟶ f) := fun φ =>
      { left := φ
        right := φ ≫ f.hom }
    have : forall g, (aux g).right = g ≫ f.hom := fun g => rfl
    change (aux φ).left = (aux ψ).left
    congr 1
    rw [← cancel_mono sq]
    ext
    · exact h
    · simp [this, ← Arrow.w_mk_right, reassoc_of% h]

@[to_dual (attr := reassoc (attr := simp))]
/--
lemma `hom_inv_id_left` / 引理 `hom_inv_id_left`

English:
lemma hom_inv_id_left
  given: (e : f ≅ g)
  statement: e.hom.left ≫ e.inv.left = 𝟙 _
  proof: by
  rw [← comp_left]; rw [e.hom_inv_id]; rw [id_left]

@[to_dual (attr := reassoc (attr := simp))]

中文:
引理 hom_inv_id_left
  条件: (e : f ≅ g)
  结论: e.hom.left ≫ e.inv.left = 𝟙 _
  证明: by
  rw [← comp_left]; rw [e.hom_inv_id]; rw [id_left]

@[to_dual (attr := reassoc (attr := simp))]

Depends on / 依赖: StructuredArrow, StructuredArrow.homMk, comp_left, e.hom_inv_id, hom_inv_id, id_left
-/
lemma hom_inv_id_left (e : f ≅ g) : e.hom.left ≫ e.inv.left = 𝟙 _ := by
  rw [← comp_left]; rw [e.hom_inv_id]; rw [id_left]

@[to_dual (attr := reassoc (attr := simp))]
/--
lemma `inv_hom_id_left` / 引理 `inv_hom_id_left`

English:
lemma inv_hom_id_left
  given: (e : f ≅ g)
  statement: e.inv.left ≫ e.hom.left = 𝟙 _
  proof: by
  rw [← comp_left]; rw [e.inv_hom_id]; rw [id_left]

中文:
引理 inv_hom_id_left
  条件: (e : f ≅ g)
  结论: e.inv.left ≫ e.hom.left = 𝟙 _
  证明: by
  rw [← comp_left]; rw [e.inv_hom_id]; rw [id_left]

Depends on / 依赖: IsInitial, Limits, Limits.IsInitial.ofUnique, comp_left, e.inv_hom_id, id_left, inv_hom_id, ofUnique
-/
lemma inv_hom_id_left (e : f ≅ g) : e.inv.left ≫ e.hom.left = 𝟙 _ := by
  rw [← comp_left]; rw [e.inv_hom_id]; rw [id_left]

end

set_option backward.isDefEq.respectTransparency.types false in
/-- Given a square from an arrow `i` to an isomorphism `p`, express the source part of `sq`
in terms of the inverse of `p`. -/
@[simp]
/--
theorem `square_to_iso_invert` / 定理 `square_to_iso_invert`

English:
theorem square_to_iso_invert
  given: (i : Arrow T) {X Y : T} (p : X ≅ Y) (sq : i ⟶ Arrow.mk p.hom)
  proof: by
  simpa only [mk_right, Category.assoc] using! (Iso.comp_inv_eq p).mpr (Arrow.w_mk_right sq).symm

中文:
定理 square_to_iso_invert
  条件: (i : 箭头 T) {X Y : T} (p : X ≅ Y) (sq : i ⟶ 箭头.mk p.hom)
  证明: by
  simpa only [mk_right, Category.assoc] using! (Iso.comp_inv_eq p).mpr (Arrow.w_mk_right sq).symm

Depends on / 依赖: Arrow.w_mk_right, Category, Category.assoc, Iso.comp_inv_eq, comp_inv_eq, mk_right, w_mk_right
-/
theorem square_to_iso_invert (i : Arrow T) {X Y : T} (p : X ≅ Y) (sq : i ⟶ Arrow.mk p.hom) :
    i.hom ≫ sq.right ≫ p.inv = sq.left := by
  simpa only [mk_right, Category.assoc] using! (Iso.comp_inv_eq p).mpr (Arrow.w_mk_right sq).symm

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `square_from_iso_invert` / 定理 `square_from_iso_invert`

English:
theorem square_from_iso_invert
  given: {X Y : T} (i : X ≅ Y) (p : Arrow T) (sq : Arrow.mk i.hom ⟶ p)
  proof: by
  simp

中文:
定理 square_from_iso_invert
  条件: {X Y : T} (i : X ≅ Y) (p : 箭头 T) (sq : 箭头.mk i.hom ⟶ p)
  证明: by
  simp
-/
theorem square_from_iso_invert {X Y : T} (i : X ≅ Y) (p : Arrow T) (sq : Arrow.mk i.hom ⟶ p) :
    i.inv ≫ sq.left ≫ p.hom = sq.right := by
  simp

variable {C : Type u} [Category.{v} C]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A helper construction: given a square between `i` and `f ≫ g`, produce a square between
`i` and `g`, whose top leg uses `f`:
```
A → X
     ↓f
↓i Y --> A → Y
     ↓g ↓i ↓g
B → Z B → Z
```
-/
@[simps!]
/--
Definition of `squareToSnd` / `squareToSnd` 的定义

English:
definition squareToSnd
  signature: {X Y Z : C} {i : Arrow C} {f : X ⟶ Y} {g : Y ⟶ Z} (sq : i ⟶ Arrow.mk (f ≫ g))
  body: Arrow.homMk (sq.left ≫ f) (sq.right) (by simp [w_mk sq])

中文:
定义 squareToSnd
  签名: {X Y Z : C} {i : 箭头 C} {f : X ⟶ Y} {g : Y ⟶ Z} (sq : i ⟶ 箭头.mk (f ≫ g))
  定义体: Arrow.homMk (sq.left ≫ f) (sq.right) (by simp [w_mk sq])

Depends on / 依赖: Arrow.homMk, sq.left, sq.right, w_mk
-/
def squareToSnd {X Y Z : C} {i : Arrow C} {f : X ⟶ Y} {g : Y ⟶ Z} (sq : i ⟶ Arrow.mk (f ≫ g)) :
    i ⟶ Arrow.mk g :=
  Arrow.homMk (sq.left ≫ f) (sq.right) (by simp [w_mk sq])

/-- The functor sending an arrow to its source. -/
@[to_dual (attr := simps!) /-- The functor sending an arrow to its target. -/]
/--
Definition of `leftFunc` / `leftFunc` 的定义

English:
definition leftFunc
  signature: : Arrow C ⥤ C
  body: Comma.fst _ _

中文:
定义 leftFunc
  签名: : 箭头 C ⥤ C
  定义体: Comma.fst _ _

Depends on / 依赖: Comma.fst
-/
def leftFunc : Arrow C ⥤ C :=
  Comma.fst _ _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The natural transformation from `leftFunc` to `rightFunc`, given by the arrow itself. -/
@[simps]
/--
Definition of `leftToRight` / `leftToRight` 的定义

English:
definition leftToRight
  signature: : (leftFunc : Arrow C ⥤ C) ⟶ rightFunc where app f
  body: f.hom

中文:
定义 leftToRight
  签名: : (leftFunc : 箭头 C ⥤ C) ⟶ rightFunc where app f
  定义体: f.hom

Depends on / 依赖: f.hom
-/
def leftToRight : (leftFunc : Arrow C ⥤ C) ⟶ rightFunc where app f := f.hom

end Arrow

namespace Functor

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

set_option backward.defeqAttrib.useBackward true in
/-- A functor `C ⥤ D` induces a functor between the corresponding arrow categories. -/
@[simps]
/--
Definition of `mapArrow` / `mapArrow` 的定义

English:
definition mapArrow
  signature: (F : C ⥤ D)
  body: Arrow.mk (F.map a.hom)
  map {X Y} f := Arrow.homMk (F.map f.left) (F.map f.right) (by simp [← Functor.map_comp])

中文:
定义 mapArrow
  签名: (F : C ⥤ D)
  定义体: Arrow.mk (F.map a.hom)
  map {X Y} f := Arrow.homMk (F.map f.left) (F.map f.right) (by simp [← Functor.map_comp])

Depends on / 依赖: Arrow.mk, F.map, a.hom
-/
def mapArrow (F : C ⥤ D) : Arrow C ⥤ Arrow D where
  obj a := Arrow.mk (F.map a.hom)
  map {X Y} f := Arrow.homMk (F.map f.left) (F.map f.right) (by simp [← Functor.map_comp])

attribute [to_dual self (reorder := X Y)] mapArrow_map

variable (C D)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The functor `(C ⥤ D) ⥤ (Arrow C ⥤ Arrow D)` which sends
a functor `F : C ⥤ D` to `F.mapArrow`. -/
@[simps]
/--
Definition of `mapArrowFunctor` / `mapArrowFunctor` 的定义

English:
definition mapArrowFunctor
  signature: : (C ⥤ D) ⥤ (Arrow C ⥤ Arrow D) where
  body: F.mapArrow
  map {X Y} τ := { app f := Arrow.homMk (τ.app _) (τ.app _) }

中文:
定义 mapArrowFunctor
  签名: : (C ⥤ D) ⥤ (箭头 C ⥤ 箭头 D) where
  定义体: F.mapArrow
  map {X Y} τ := { app f := Arrow.homMk (τ.app _) (τ.app _) }

Depends on / 依赖: F.mapArrow, mapArrow
-/
def mapArrowFunctor : (C ⥤ D) ⥤ (Arrow C ⥤ Arrow D) where
  obj F := F.mapArrow
  map {X Y} τ := { app f := Arrow.homMk (τ.app _) (τ.app _) }

attribute [to_dual self (reorder := X Y)] mapArrowFunctor_map_app

variable {C D}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The equivalence of categories `Arrow C ≌ Arrow D` induced by an equivalence `C ≌ D`. -/
@[simps]
/--
Definition of `mapArrowEquivalence` / `mapArrowEquivalence` 的定义

English:
definition mapArrowEquivalence
  signature: (e : C ≌ D)
  body: e.functor.mapArrow
  inverse := e.inverse.mapArrow
  unitIso := Functor.mapIso (mapArrowFunctor C C) e.unitIso
  counitIso := Functor.mapIso (mapArrowFunctor D D) e.counitIso

中文:
定义 mapArrowEquivalence
  签名: (e : C ≌ D)
  定义体: e.functor.mapArrow
  inverse := e.inverse.mapArrow
  unitIso := Functor.mapIso (mapArrowFunctor C C) e.unitIso
  counitIso := Functor.mapIso (mapArrowFunctor D D) e.counitIso

Depends on / 依赖: e.functor.mapArrow, functor, mapArrow
-/
def mapArrowEquivalence (e : C ≌ D) : Arrow C ≌ Arrow D where
  functor := e.functor.mapArrow
  inverse := e.inverse.mapArrow
  unitIso := Functor.mapIso (mapArrowFunctor C C) e.unitIso
  counitIso := Functor.mapIso (mapArrowFunctor D D) e.counitIso

set_option backward.defeqAttrib.useBackward true in
/--
Instance `essSurj_mapArrow` / 实例 `essSurj_mapArrow`

English:
instance essSurj_mapArrow
  signature: (F : C ⥤ D) [F.Full] [F.EssSurj]
  body: ⟨Arrow.mk (F.preimage ((F.objObjPreimageIso _).hom ≫ f.hom ≫
      (F.objObjPreimageIso _).inv)),
        ⟨Arrow.isoMk (F.objObjPreimageIso _) (F.objObjPreimageIso _)⟩⟩

中文:
实例 essSurj_mapArrow
  签名: (F : C ⥤ D) [F.满] [F.本质满射]
  定义体: ⟨Arrow.mk (F.preimage ((F.objObjPreimageIso _).hom ≫ f.hom ≫
      (F.objObjPreimageIso _).inv)),
        ⟨Arrow.isoMk (F.objObjPreimageIso _) (F.objObjPreimageIso _)⟩⟩

Depends on / 依赖: Arrow.isoMk, Arrow.mk, F.objObjPreimageIso, F.preimage, f.hom, objObjPreimageIso, preimage
-/
instance essSurj_mapArrow (F : C ⥤ D) [F.Full] [F.EssSurj] :
    F.mapArrow.EssSurj where
  mem_essImage f :=
    ⟨Arrow.mk (F.preimage ((F.objObjPreimageIso _).hom ≫ f.hom ≫
      (F.objObjPreimageIso _).inv)),
        ⟨Arrow.isoMk (F.objObjPreimageIso _) (F.objObjPreimageIso _)⟩⟩

/--
Instance `isEquivalence_mapArrow` / 实例 `isEquivalence_mapArrow`

English:
instance isEquivalence_mapArrow
  signature: (F : C ⥤ D) [IsEquivalence F]
  body: (mapArrowEquivalence (asEquivalence F)).isEquivalence_functor

中文:
实例 isEquivalence_mapArrow
  签名: (F : C ⥤ D) [是等价 F]
  定义体: (mapArrowEquivalence (asEquivalence F)).isEquivalence_functor

Depends on / 依赖: asEquivalence, isEquivalence_functor, mapArrowEquivalence
-/
instance isEquivalence_mapArrow (F : C ⥤ D) [IsEquivalence F] :
    IsEquivalence F.mapArrow :=
  (mapArrowEquivalence (asEquivalence F)).isEquivalence_functor

end Functor

variable {C D : Type*} [Category* C] [Category* D]

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `Arrow.isoOfNatIso` / `Arrow.isoOfNatIso` 的定义

English:
definition Arrow.isoOfNatIso
  signature: {F G : C ⥤ D} (e : F ≅ G)
  body: Arrow.isoMk (e.app f.left) (e.app f.right)

中文:
定义 箭头.isoOf自然数Iso
  签名: {F G : C ⥤ D} (e : F ≅ G)
  定义体: Arrow.isoMk (e.app f.left) (e.app f.right)

Depends on / 依赖: Arrow.isoMk, e.app, f.left, f.right
-/
def Arrow.isoOfNatIso {F G : C ⥤ D} (e : F ≅ G)
    (f : Arrow C) : F.mapArrow.obj f ≅ G.mapArrow.obj f :=
  Arrow.isoMk (e.app f.left) (e.app f.right)

variable (T)

/-- `Arrow T` is equivalent to a sigma type. -/
@[simps!]
/--
Definition of `Arrow.equivSigma` / `Arrow.equivSigma` 的定义

English:
definition Arrow.equivSigma
  signature: :
  body: ⟨_, _, f.hom⟩
  invFun x := Arrow.mk x.2.2

中文:
定义 箭头.equivSigma
  签名: :
  定义体: ⟨_, _, f.hom⟩
  invFun x := Arrow.mk x.2.2

Depends on / 依赖: f.hom
-/
def Arrow.equivSigma :
    Arrow T ≃ Σ (X Y : T), X ⟶ Y where
  toFun f := ⟨_, _, f.hom⟩
  invFun x := Arrow.mk x.2.2

/--
Definition of `Arrow.discreteEquiv` / `Arrow.discreteEquiv` 的定义

English:
definition Arrow.discreteEquiv
  signature: (S : Type u)
  body: f.left.as
  invFun s := Arrow.mk (𝟙 (Discrete.mk s))
  left_inv := by
    rintro ⟨⟨_⟩, ⟨_⟩, f⟩
    obtain rfl := Discrete.eq_of_hom f
    rfl

中文:
定义 箭头.discreteEquiv
  签名: (S : 类型u)
  定义体: f.left.as
  invFun s := Arrow.mk (𝟙 (Discrete.mk s))
  left_inv := by
    rintro ⟨⟨_⟩, ⟨_⟩, f⟩
    obtain rfl := Discrete.eq_of_hom f
    rfl

Depends on / 依赖: compULiftYonedaIsoULiftYonedaCompLan, compULiftYonedaIsoULiftYonedaCompLan.extensionHom, extensionHom, f.left.as
-/
def Arrow.discreteEquiv (S : Type u) : Arrow (Discrete S) ≃ S where
  toFun f := f.left.as
  invFun s := Arrow.mk (𝟙 (Discrete.mk s))
  left_inv := by
    rintro ⟨⟨_⟩, ⟨_⟩, f⟩
    obtain rfl := Discrete.eq_of_hom f
    rfl

/-- Extensionality lemma for functors `C ⥤ D` which uses as an assumption
that the induced maps `Arrow C → Arrow D` coincide. -/
@[to_dual self]
/--
lemma `Arrow.functor_ext` / 引理 `Arrow.functor_ext`

English:
lemma Arrow.functor_ext
  statement: {F G : C ⥤ D} (h : forall ⦃X Y : C⦄ (f : X ⟶ Y),
  proof: Functor.ext (fun X => congr_arg Comma.left (h (𝟙 X))) (fun X Y f => by
    have := h f
    simp only [Functor.mapArrow_obj, mk_eq_mk_iff] at this
    tauto)

中文:
引理 箭头.functor_ext
  结论: {F G : C ⥤ D} (h : 对任意 ⦃X Y : C⦄ (f : X ⟶ Y),
  证明: Functor.ext (fun X => congr_arg Comma.left (h (𝟙 X))) (fun X Y f => by
    have := h f
    simp only [Functor.mapArrow_obj, mk_eq_mk_iff] at this
    tauto)

Depends on / 依赖: Comma.left, Functor, Functor.ext, Functor.mapArrow_obj, congr_arg, mapArrow_obj, mk_eq_mk_iff
-/
lemma Arrow.functor_ext {F G : C ⥤ D} (h : forall ⦃X Y : C⦄ (f : X ⟶ Y),
    F.mapArrow.obj (Arrow.mk f) = G.mapArrow.obj (Arrow.mk f)) :
    F = G :=
  Functor.ext (fun X => congr_arg Comma.left (h (𝟙 X))) (fun X Y f => by
    have := h f
    simp only [Functor.mapArrow_obj, mk_eq_mk_iff] at this
    tauto)

end CategoryTheory
