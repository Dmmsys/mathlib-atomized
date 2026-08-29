/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Comma.Arrow

/-!
# Commutative squares

This file provides an API for commutative squares in categories.
If `top`, `left`, `right` and `bottom` are four morphisms which are the edges
of a square, `CommSq top left right bottom` is the predicate that this
square is commutative.

The structure `CommSq` is extended in
`Mathlib/CategoryTheory/Limits/Shapes/Pullback/IsPullback/Defs.lean`
as `IsPullback` and `IsPushout` in order to define pullback and pushout squares.

## Future work

Refactor `LiftStruct` from `Arrow.lean` and lifting properties using `CommSq.lean`.

-/

@[expose] public section


namespace CategoryTheory

variable {C : Type*} [Category* C]

set_option linter.translate.warnInvalid false in
/-- The proposition that a square
```
  W ---f---> X
  | |
  g h
  | |
  v v
  Y ---i---> Z

```
is a commuting square.
-/
@[to_dual self (reorder := W Z, X Y, f i, g h)]
/--
Definition of `CommSq` / `CommSq` 的定义

English:
structure CommSq
  parameters: {W X Y Z : C} (f : W ⟶ X) (g : W ⟶ Y) (h : X ⟶ Z) (i : Y ⟶ Z)
  axioms and operations (1):
    - w : f ≫ h = g ≫ i  [default: by cat_disch]

中文:
结构 CommSq
  参数: {W X Y Z : C} (f : W ⟶ X) (g : W ⟶ Y) (h : X ⟶ Z) (i : Y ⟶ Z)
  公理与运算 (1 个):
    - w : f ≫ h = g ≫ i  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure CommSq {W X Y Z : C} (f : W ⟶ X) (g : W ⟶ Y) (h : X ⟶ Z) (i : Y ⟶ Z) : Prop where
  /-- The square commutes. -/
  w : f ≫ h = g ≫ i := by cat_disch

attribute [simp] CommSq.mk

namespace CommSq

variable {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}

@[to_dual existing w]
/--
lemma `w'` / 引理 `w'`

English:
lemma w'
  given: (self : CommSq f g h i)
  statement: g ≫ i = f ≫ h
  proof: self.w.symm

中文:
引理 w'
  条件: (self : CommSq f g h i)
  结论: g ≫ i = f ≫ h
  证明: self.w.symm

Depends on / 依赖: self.w.symm
-/
lemma w' (self : CommSq f g h i) : g ≫ i = f ≫ h := self.w.symm

/-- `CommSq.mk'` is the dual of `CommSq.mk`, which we need for `to_dual`.
Please avoid using this directly. -/
@[to_dual existing mk]
/--
lemma `mk'` / 引理 `mk'`

English:
lemma mk'
  given: (w : g ≫ i = f ≫ h := by cat_disch)
  statement: CommSq f g h i
  proof: ⟨w.symm⟩

中文:
引理 mk'
  条件: (w : g ≫ i = f ≫ h := by cat_disch)
  结论: CommSq f g h i
  证明: ⟨w.symm⟩

Depends on / 依赖: CommSq, cat_disch, w.symm
-/
lemma mk' (w : g ≫ i = f ≫ h := by cat_disch) : CommSq f g h i :=
  ⟨w.symm⟩

attribute [reassoc] CommSq.w

@[to_dual self]
/--
theorem `flip` / 定理 `flip`

English:
theorem flip
  given: (p : CommSq f g h i)
  statement: CommSq g f i h
  proof: ⟨p.w.symm⟩

中文:
定理 flip
  条件: (p : CommSq f g h i)
  结论: CommSq g f i h
  证明: ⟨p.w.symm⟩

Depends on / 依赖: p.w.symm
-/
theorem flip (p : CommSq f g h i) : CommSq g f i h :=
  ⟨p.w.symm⟩

/--
theorem `of_arrow` / 定理 `of_arrow`

English:
theorem of_arrow
  given: {f g : Arrow C} (h : f ⟶ g)
  statement: CommSq f.hom h.left h.right g.hom
  proof: ⟨h.w.symm⟩

中文:
定理 of_arrow
  条件: {f g : Arrow C} (h : f ⟶ g)
  结论: CommSq f.hom h.left h.right g.hom
  证明: ⟨h.w.symm⟩

Depends on / 依赖: h.w.symm
-/
theorem of_arrow {f g : Arrow C} (h : f ⟶ g) : CommSq f.hom h.left h.right g.hom :=
  ⟨h.w.symm⟩

/-- The commutative square in the opposite category associated to a commutative square. -/
@[to_dual self]
/--
theorem `op` / 定理 `op`

English:
theorem op
  given: (p : CommSq f g h i)
  statement: CommSq i.op h.op g.op f.op
  proof: ⟨by simp only [← op_comp, p.w]⟩

中文:
定理 op
  条件: (p : CommSq f g h i)
  结论: CommSq i.op h.op g.op f.op
  证明: ⟨by simp only [← op_comp, p.w]⟩

Depends on / 依赖: op_comp
-/
theorem op (p : CommSq f g h i) : CommSq i.op h.op g.op f.op :=
  ⟨by simp only [← op_comp, p.w]⟩

/-- The commutative square associated to a commutative square in the opposite category. -/
@[to_dual self]
/--
theorem `unop` / 定理 `unop`

English:
theorem unop
  given: {W X Y Z : Cᵒᵖ} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z} (p : CommSq f g h i)
  proof: ⟨by simp only [← unop_comp, p.w]⟩

@[to_dual none]

中文:
定理 unop
  条件: {W X Y Z : Cᵒᵖ} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z} (p : CommSq f g h i)
  证明: ⟨by simp only [← unop_comp, p.w]⟩

@[to_dual none]

Depends on / 依赖: unop_comp
-/
theorem unop {W X Y Z : Cᵒᵖ} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z} (p : CommSq f g h i) :
    CommSq i.unop h.unop g.unop f.unop :=
  ⟨by simp only [← unop_comp, p.w]⟩

@[to_dual none]
/--
theorem `vert_inv` / 定理 `vert_inv`

English:
theorem vert_inv
  given: {g : W ≅ Y} {h : X ≅ Z} (p : CommSq f g.hom h.hom i)
  proof: ⟨by rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, p.w]⟩

@[to_dual none]

中文:
定理 vert_inv
  条件: {g : W ≅ Y} {h : X ≅ Z} (p : CommSq f g.hom h.hom i)
  证明: ⟨by rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, p.w]⟩

@[to_dual none]

Depends on / 依赖: Category, Category.assoc, Iso.comp_inv_eq, Iso.eq_inv_comp, comp_inv_eq, eq_inv_comp
-/
theorem vert_inv {g : W ≅ Y} {h : X ≅ Z} (p : CommSq f g.hom h.hom i) :
    CommSq i g.inv h.inv f :=
  ⟨by rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, p.w]⟩

@[to_dual none]
/--
theorem `horiz_inv` / 定理 `horiz_inv`

English:
theorem horiz_inv
  given: {f : W ≅ X} {i : Y ≅ Z} (p : CommSq f.hom g h i.hom)
  proof: flip (vert_inv (flip p))

中文:
定理 horiz_inv
  条件: {f : W ≅ X} {i : Y ≅ Z} (p : CommSq f.hom g h i.hom)
  证明: flip (vert_inv (flip p))

Depends on / 依赖: vert_inv
-/
theorem horiz_inv {f : W ≅ X} {i : Y ≅ Z} (p : CommSq f.hom g h i.hom) :
    CommSq f.inv h g i.inv :=
  flip (vert_inv (flip p))

/-- The horizontal composition of two commutative squares as below is a commutative square.
```
  W ---f---> X ---f'--> X'
  | | |
  g h h'
  | | |
  v v v
  Y ---i---> Z ---i'--> Z'

```
-/
@[to_dual self (reorder := W Z', X Z, X' Y, f i', f' i, g h', hsq₁ hsq₂)]
/--
lemma `horiz_comp` / 引理 `horiz_comp`

English:
lemma horiz_comp
  statement: {W X X' Y Z Z' : C} {f : W ⟶ X} {f' : X ⟶ X'} {g : W ⟶ Y} {h : X ⟶ Z}
  proof: ⟨by rw [← Category.assoc, Category.assoc, ← hsq₁.w, hsq₂.w, Category.assoc]⟩

中文:
引理 horiz_comp
  结论: {W X X' Y Z Z' : C} {f : W ⟶ X} {f' : X ⟶ X'} {g : W ⟶ Y} {h : X ⟶ Z}
  证明: ⟨by rw [← Category.assoc, Category.assoc, ← hsq₁.w, hsq₂.w, Category.assoc]⟩

Depends on / 依赖: Category, Category.assoc
-/
lemma horiz_comp {W X X' Y Z Z' : C} {f : W ⟶ X} {f' : X ⟶ X'} {g : W ⟶ Y} {h : X ⟶ Z}
    {h' : X' ⟶ Z'} {i : Y ⟶ Z} {i' : Z ⟶ Z'} (hsq₁ : CommSq f g h i) (hsq₂ : CommSq f' h h' i') :
    CommSq (f ≫ f') g h' (i ≫ i') :=
  ⟨by rw [← Category.assoc, Category.assoc, ← hsq₁.w, hsq₂.w, Category.assoc]⟩

/-- The vertical composition of two commutative squares as below is a commutative square.
```
  W ---f---> X
  | |
  g h
  | |
  v v
  Y ---i---> Z
  | |
  g' h'
  | |
  v v
  Y'---i'--> Z'

```
-/
@[to_dual self (reorder := W Z', Y Z, Y' X, g h', g' h, f i', hsq₁ hsq₂)]
/--
lemma `vert_comp` / 引理 `vert_comp`

English:
lemma vert_comp
  statement: {W X Y Y' Z Z' : C} {f : W ⟶ X} {g : W ⟶ Y} {g' : Y ⟶ Y'} {h : X ⟶ Z}
  proof: flip (horiz_comp (flip hsq₁) (flip hsq₂))

中文:
引理 vert_comp
  结论: {W X Y Y' Z Z' : C} {f : W ⟶ X} {g : W ⟶ Y} {g' : Y ⟶ Y'} {h : X ⟶ Z}
  证明: flip (horiz_comp (flip hsq₁) (flip hsq₂))

Depends on / 依赖: horiz_comp
-/
lemma vert_comp {W X Y Y' Z Z' : C} {f : W ⟶ X} {g : W ⟶ Y} {g' : Y ⟶ Y'} {h : X ⟶ Z}
    {h' : Z ⟶ Z'} {i : Y ⟶ Z} {i' : Y' ⟶ Z'} (hsq₁ : CommSq f g h i) (hsq₂ : CommSq i g' h' i') :
    CommSq f (g ≫ g') (h ≫ h') i' :=
  flip (horiz_comp (flip hsq₁) (flip hsq₂))


section

variable {W X Y : C}

@[to_dual none]
/--
theorem `eq_of_mono` / 定理 `eq_of_mono`

English:
theorem eq_of_mono
  given: {f : W ⟶ X} {g : W ⟶ X} {i : X ⟶ Y} [Mono i] (sq : CommSq f g i i)
  statement: f = g
  proof: (cancel_mono i).1 sq.w

@[to_dual none]

中文:
定理 eq_of_mono
  条件: {f : W ⟶ X} {g : W ⟶ X} {i : X ⟶ Y} [Mono i] (sq : CommSq f g i i)
  结论: f = g
  证明: (cancel_mono i).1 sq.w

@[to_dual none]

Depends on / 依赖: cancel_mono, sq.w
-/
theorem eq_of_mono {f : W ⟶ X} {g : W ⟶ X} {i : X ⟶ Y} [Mono i] (sq : CommSq f g i i) : f = g :=
  (cancel_mono i).1 sq.w

@[to_dual none]
/--
theorem `eq_of_epi` / 定理 `eq_of_epi`

English:
theorem eq_of_epi
  given: {f : W ⟶ X} {h : X ⟶ Y} {i : X ⟶ Y} [Epi f] (sq : CommSq f f h i)
  statement: h = i
  proof: (cancel_epi f).1 sq.w

中文:
定理 eq_of_epi
  条件: {f : W ⟶ X} {h : X ⟶ Y} {i : X ⟶ Y} [Epi f] (sq : CommSq f f h i)
  结论: h = i
  证明: (cancel_epi f).1 sq.w

Depends on / 依赖: cancel_epi, sq.w
-/
theorem eq_of_epi {f : W ⟶ X} {h : X ⟶ Y} {i : X ⟶ Y} [Epi f] (sq : CommSq f f h i) : h = i :=
  (cancel_epi f).1 sq.w

end

end CommSq

namespace Functor

variable {D : Type*} [Category* D]
variable (F : C ⥤ D) {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}

@[to_dual self]
/--
theorem `map_commSq` / 定理 `map_commSq`

English:
theorem map_commSq
  given: (s : CommSq f g h i)
  statement: CommSq (F.map f) (F.map g) (F.map h) (F.map i)
  proof: ⟨by simpa using congr_arg (fun k : W ⟶ Z => F.map k) s.w⟩

中文:
定理 map_commSq
  条件: (s : CommSq f g h i)
  结论: CommSq (F.map f) (F.map g) (F.map h) (F.map i)
  证明: ⟨by simpa using congr_arg (fun k : W ⟶ Z => F.map k) s.w⟩

Depends on / 依赖: F.map, congr_arg
-/
theorem map_commSq (s : CommSq f g h i) : CommSq (F.map f) (F.map g) (F.map h) (F.map i) :=
  ⟨by simpa using congr_arg (fun k : W ⟶ Z => F.map k) s.w⟩

end Functor

@[to_dual self]
alias CommSq.map := Functor.map_commSq

namespace CommSq


variable {A B X Y : C} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y}

set_option linter.translate.warnInvalid false in
/-- Now we consider a square:
```
  A ---f---> X
  | |
  i p
  | |
  v v
  B ---g---> Y
```

The datum of a lift in a commutative square, i.e. an up-right-diagonal
morphism which makes both triangles commute. -/
@[ext, to_dual self]
/--
Definition of `LiftStruct` / `LiftStruct` 的定义

English:
structure LiftStruct
  parameters: (sq : CommSq f i p g)
  axioms and operations (3):
    - l : B ⟶ X
    - fac_left : i ≫ l = f  [default: by cat_disch]
    - fac_right : l ≫ p = g  [default: by cat_disch]

中文:
结构 LiftStruct
  参数: (sq : CommSq f i p g)
  公理与运算 (3 个):
    - l : B ⟶ X
    - fac_left : i ≫ l = f  [默认: by cat_disch]
    - fac_right : l ≫ p = g  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure LiftStruct (sq : CommSq f i p g) where
  /-- The lift. -/
  l : B ⟶ X
  /-- The upper left triangle commutes. -/
  fac_left : i ≫ l = f := by cat_disch
  /-- The lower right triangle commutes. -/
  fac_right : l ≫ p = g := by cat_disch

attribute [to_dual self] LiftStruct.ext
attribute [to_dual existing fac_left] LiftStruct.fac_right
attribute [to_dual self (reorder := A Y, B X, f g, i p, fac_left fac_right)] LiftStruct.mk

namespace LiftStruct

/-- A `LiftStruct` for a commutative square gives a `LiftStruct` for the
corresponding square in the opposite category. -/
@[simps, to_dual self]
/--
Definition of `op` / `op` 的定义

English:
definition op
  signature: {sq : CommSq f i p g} (l : LiftStruct sq)
  body: l.l.op
  fac_left := by rw [← op_comp, l.fac_right]
  fac_right := by rw [← op_comp, l.fac_left]

中文:
定义 op
  签名: {sq : CommSq f i p g} (l : LiftStruct sq)
  定义体: l.l.op
  fac_left := by rw [← op_comp, l.fac_right]
  fac_right := by rw [← op_comp, l.fac_left]

Depends on / 依赖: l.l.op
-/
def op {sq : CommSq f i p g} (l : LiftStruct sq) : LiftStruct sq.op where
  l := l.l.op
  fac_left := by rw [← op_comp, l.fac_right]
  fac_right := by rw [← op_comp, l.fac_left]

/-- A `LiftStruct` for a commutative square in the opposite category
gives a `LiftStruct` for the corresponding square in the original category. -/
@[simps, to_dual self]
/--
Definition of `unop` / `unop` 的定义

English:
definition unop
  signature: {A B X Y : Cᵒᵖ} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y} {sq : CommSq f i p g}
  body: l.l.unop
  fac_left := by rw [← unop_comp, l.fac_right]
  fac_right := by rw [← unop_comp, l.fac_left]

中文:
定义 unop
  签名: {A B X Y : Cᵒᵖ} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y} {sq : CommSq f i p g}
  定义体: l.l.unop
  fac_left := by rw [← unop_comp, l.fac_right]
  fac_right := by rw [← unop_comp, l.fac_left]

Depends on / 依赖: l.l.unop
-/
def unop {A B X Y : Cᵒᵖ} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y} {sq : CommSq f i p g}
    (l : LiftStruct sq) : LiftStruct sq.unop where
  l := l.l.unop
  fac_left := by rw [← unop_comp, l.fac_right]
  fac_right := by rw [← unop_comp, l.fac_left]

/-- Equivalences of `LiftStruct` for a square and the corresponding square
in the opposite category. -/
@[simps, to_dual self]
/--
Definition of `opEquiv` / `opEquiv` 的定义

English:
definition opEquiv
  signature: (sq : CommSq f i p g)
  body: op
  invFun := unop
  left_inv := by cat_disch
  right_inv := by cat_disch

中文:
定义 opEquiv
  签名: (sq : CommSq f i p g)
  定义体: op
  invFun := unop
  left_inv := by cat_disch
  right_inv := by cat_disch
-/
def opEquiv (sq : CommSq f i p g) : LiftStruct sq ≃ LiftStruct sq.op where
  toFun := op
  invFun := unop
  left_inv := by cat_disch
  right_inv := by cat_disch

/-- Equivalences of `LiftStruct` for a square in the opposite category and
the corresponding square in the original category. -/
@[simps, to_dual self]
/--
Definition of `unopEquiv` / `unopEquiv` 的定义

English:
definition unopEquiv
  signature: {A B X Y : Cᵒᵖ} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y}
  body: unop
  invFun := op
  left_inv := by cat_disch
  right_inv := by cat_disch

中文:
定义 unopEquiv
  签名: {A B X Y : Cᵒᵖ} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y}
  定义体: unop
  invFun := op
  left_inv := by cat_disch
  right_inv := by cat_disch
-/
def unopEquiv {A B X Y : Cᵒᵖ} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y}
    (sq : CommSq f i p g) : LiftStruct sq ≃ LiftStruct sq.unop where
  toFun := unop
  invFun := op
  left_inv := by cat_disch
  right_inv := by cat_disch

end LiftStruct

@[to_dual]
/--
Instance `subsingleton_liftStruct_of_epi` / 实例 `subsingleton_liftStruct_of_epi`

English:
instance subsingleton_liftStruct_of_epi
  signature: (sq : CommSq f i p g) [Epi i]
  body: ⟨fun l₁ l₂ => by
    ext
    rw [← cancel_epi i]
    simp only [LiftStruct.fac_left]⟩

中文:
实例 subsingleton_liftStruct_of_epi
  签名: (sq : CommSq f i p g) [Epi i]
  定义体: ⟨fun l₁ l₂ => by
    ext
    rw [← cancel_epi i]
    simp only [LiftStruct.fac_left]⟩

Depends on / 依赖: LiftStruct, LiftStruct.fac_left, cancel_epi, fac_left
-/
instance subsingleton_liftStruct_of_epi (sq : CommSq f i p g) [Epi i] :
    Subsingleton (LiftStruct sq) :=
  ⟨fun l₁ l₂ => by
    ext
    rw [← cancel_epi i]
    simp only [LiftStruct.fac_left]⟩

variable (sq : CommSq f i p g)

/-- The assertion that a square has a `LiftStruct`. -/
@[to_dual self]
/--
Definition of `HasLift` / `HasLift` 的定义

English:
class HasLift
  parameters: : Prop where
  axioms and operations (1):
    - exists_lift : Nonempty sq.LiftStruct

中文:
类 HasLift
  参数: : 命题 where
  公理与运算 (1 个):
    - exists_lift : Nonempty sq.LiftStruct
-/
class HasLift : Prop where
  /-- Square has a `LiftStruct`. -/
  exists_lift : Nonempty sq.LiftStruct

namespace HasLift

variable {sq} in
@[to_dual self]
/--
theorem `mk'` / 定理 `mk'`

English:
theorem mk'
  given: (l : sq.LiftStruct)
  statement: HasLift sq
  proof: ⟨Nonempty.intro l⟩

@[to_dual self]

中文:
定理 mk'
  条件: (l : sq.LiftStruct)
  结论: HasLift sq
  证明: ⟨Nonempty.intro l⟩

@[to_dual self]

Depends on / 依赖: Nonempty, Nonempty.intro
-/
theorem mk' (l : sq.LiftStruct) : HasLift sq :=
  ⟨Nonempty.intro l⟩

@[to_dual self]
/--
theorem `iff` / 定理 `iff`

English:
theorem iff
  statement: HasLift sq ↔ Nonempty sq.LiftStruct
  proof: by
  constructor
  exacts [fun h => h.exists_lift, fun h => mk h]

@[to_dual self]

中文:
定理 iff
  结论: HasLift sq ↔ Nonempty sq.LiftStruct
  证明: by
  constructor
  exacts [fun h => h.exists_lift, fun h => mk h]

@[to_dual self]

Depends on / 依赖: exacts, exists_lift, h.exists_lift
-/
theorem iff : HasLift sq ↔ Nonempty sq.LiftStruct := by
  constructor
  exacts [fun h => h.exists_lift, fun h => mk h]

@[to_dual self]
/--
theorem `iff_op` / 定理 `iff_op`

English:
theorem iff_op
  statement: HasLift sq ↔ HasLift sq.op
  proof: by
  rw [iff]; rw [iff]
  exact Nonempty.congr (LiftStruct.opEquiv sq).toFun (LiftStruct.opEquiv sq).invFun

@[to_dual self]

中文:
定理 iff_op
  结论: HasLift sq ↔ HasLift sq.op
  证明: by
  rw [iff]; rw [iff]
  exact Nonempty.congr (LiftStruct.opEquiv sq).toFun (LiftStruct.opEquiv sq).invFun

@[to_dual self]

Depends on / 依赖: LiftStruct, LiftStruct.opEquiv, Nonempty, Nonempty.congr, invFun, opEquiv
-/
theorem iff_op : HasLift sq ↔ HasLift sq.op := by
  rw [iff]; rw [iff]
  exact Nonempty.congr (LiftStruct.opEquiv sq).toFun (LiftStruct.opEquiv sq).invFun

@[to_dual self]
/--
theorem `iff_unop` / 定理 `iff_unop`

English:
theorem iff_unop
  statement: {A B X Y : Cᵒᵖ} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y}
  proof: by
  rw [iff]; rw [iff]
  exact Nonempty.congr (LiftStruct.unopEquiv sq).toFun (LiftStruct.unopEquiv sq).invFun

中文:
定理 iff_unop
  结论: {A B X Y : Cᵒᵖ} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y}
  证明: by
  rw [iff]; rw [iff]
  exact Nonempty.congr (LiftStruct.unopEquiv sq).toFun (LiftStruct.unopEquiv sq).invFun

Depends on / 依赖: LiftStruct, LiftStruct.unopEquiv, Nonempty, Nonempty.congr, invFun, unopEquiv
-/
theorem iff_unop {A B X Y : Cᵒᵖ} {f : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {g : B ⟶ Y}
    (sq : CommSq f i p g) : HasLift sq ↔ HasLift sq.unop := by
  rw [iff]; rw [iff]
  exact Nonempty.congr (LiftStruct.unopEquiv sq).toFun (LiftStruct.unopEquiv sq).invFun

end HasLift

/-- A choice of a diagonal morphism that is part of a `LiftStruct` when
the square has a lift. -/
@[to_dual self]
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: [hsq : HasLift sq]
  body: hsq.exists_lift.some.l

@[to_dual (attr := reassoc (attr := simp)) fac_right]

中文:
定义 lift
  签名: [hsq : HasLift sq]
  定义体: hsq.exists_lift.some.l

@[to_dual (attr := reassoc (attr := simp)) fac_right]

Depends on / 依赖: exists_lift, hsq.exists_lift.some.l
-/
noncomputable def lift [hsq : HasLift sq] : B ⟶ X :=
  hsq.exists_lift.some.l

@[to_dual (attr := reassoc (attr := simp)) fac_right]
/--
theorem `fac_left` / 定理 `fac_left`

English:
theorem fac_left
  given: [hsq : HasLift sq]
  statement: i ≫ sq.lift = f
  proof: hsq.exists_lift.some.fac_left

中文:
定理 fac_left
  条件: [hsq : HasLift sq]
  结论: i ≫ sq.lift = f
  证明: hsq.exists_lift.some.fac_left

Depends on / 依赖: exists_lift, fac_left, hsq.exists_lift.some.fac_left
-/
theorem fac_left [hsq : HasLift sq] : i ≫ sq.lift = f :=
  hsq.exists_lift.some.fac_left

end CommSq

end CategoryTheory
