/-
Copyright (c) 2025 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Jakob von Raumer
-/
module

public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.Tactic.CategoryTheory.Slice

/-!
# 2-squares of functors

Given four functors `T`, `L`, `R` and `B`, a 2-square `TwoSquare T L R B` consists of
a natural transformation `w : T ⋙ R ⟶ L ⋙ B`:
```
     T
  C₁ ⥤ C₂
L | | R
  v v
  C₃ ⥤ C₄
     B
```

We define operations to paste such squares horizontally and vertically and prove the interchange
law of those two operations.

## TODO

Generalize all of this to double categories.

-/

@[expose] public section

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉

namespace CategoryTheory

open Category CategoryTheory.Functor

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} C₄]
  (T : C₁ ⥤ C₂) (L : C₁ ⥤ C₃) (R : C₂ ⥤ C₄) (B : C₃ ⥤ C₄)

/--
Definition of `TwoSquare` / `TwoSquare` 的定义

English:
definition TwoSquare
  body: T ⋙ R ⟶ L ⋙ B

中文:
定义 TwoSquare
  定义体: T ⋙ R ⟶ L ⋙ B
-/
def TwoSquare := T ⋙ R ⟶ L ⋙ B

namespace TwoSquare

/--
Definition of `mk` / `mk` 的定义

English:
abbreviation mk
  signature: (α : T ⋙ R ⟶ L ⋙ B)
  body: α

中文:
缩写 mk
  签名: (α : T ⋙ R ⟶ L ⋙ B)
  定义体: α
-/
abbrev mk (α : T ⋙ R ⟶ L ⋙ B) : TwoSquare T L R B := α

variable {T} {L} {R} {B} in
/--
Definition of `natTrans` / `natTrans` 的定义

English:
abbreviation natTrans
  signature: (w : TwoSquare T L R B)
  body: w

中文:
缩写 natTrans
  签名: (w : TwoSquare T L R B)
  定义体: w
-/
abbrev natTrans (w : TwoSquare T L R B) : T ⋙ R ⟶ L ⋙ B := w

/-- The type of 2-squares on functors `T`, `L`, `R`, and `B` is trivially equivalent to
the type of natural transformations `T ⋙ R ⟶ L ⋙ B`. -/
@[simps]
/--
Definition of `equivNatTrans` / `equivNatTrans` 的定义

English:
definition equivNatTrans
  signature: : TwoSquare T L R B ≃ (T ⋙ R ⟶ L ⋙ B) where
  body: natTrans
  invFun := mk T L R B

中文:
定义 equivNatTrans
  签名: : TwoSquare T L R B ≃ (T ⋙ R ⟶ L ⋙ B) where
  定义体: natTrans
  invFun := mk T L R B

Depends on / 依赖: natTrans
-/
def equivNatTrans : TwoSquare T L R B ≃ (T ⋙ R ⟶ L ⋙ B) where
  toFun := natTrans
  invFun := mk T L R B

variable {T L R B}

/--
Definition of `op` / `op` 的定义

English:
definition op
  signature: (α : TwoSquare T L R B)
  body: NatTrans.op α

@[simp]

中文:
定义 op
  签名: (α : TwoSquare T L R B)
  定义体: NatTrans.op α

@[simp]

Depends on / 依赖: NatTrans, NatTrans.op
-/
def op (α : TwoSquare T L R B) : TwoSquare L.op T.op B.op R.op := NatTrans.op α

@[simp]
/--
lemma `natTrans_op` / 引理 `natTrans_op`

English:
lemma natTrans_op
  given: (α : TwoSquare T L R B)
  proof: rfl

中文:
引理 natTrans_op
  条件: (α : TwoSquare T L R B)
  证明: rfl
-/
lemma natTrans_op (α : TwoSquare T L R B) :
    α.op.natTrans = NatTrans.op α.natTrans := rfl

instance (α : TwoSquare T L R B) [IsIso α.natTrans] : IsIso α.op.natTrans :=
  inferInstanceAs (IsIso (NatTrans.op α.natTrans))

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: (w w' : TwoSquare T L R B) (h : forall (X : C₁), w.natTrans.app X = w'.natTrans.app X)
  proof: NatTrans.ext (funext h)

中文:
引理 ext
  条件: (w w' : TwoSquare T L R B) (h : 对任意 (X : C₁), w.natTrans.app X = w'.natTrans.app X)
  证明: NatTrans.ext (funext h)

Depends on / 依赖: NatTrans, NatTrans.ext
-/
lemma ext (w w' : TwoSquare T L R B) (h : forall (X : C₁), w.natTrans.app X = w'.natTrans.app X) :
    w = w' :=
  NatTrans.ext (funext h)

/-- The horizontal identity 2-square. -/
@[simps!]
/--
Definition of `hId` / `hId` 的定义

English:
definition hId
  signature: (L : C₁ ⥤ C₃)
  body: (Functor.leftUnitor L).hom ≫ (Functor.rightUnitor L).inv

中文:
定义 hId
  签名: (L : C₁ ⥤ C₃)
  定义体: (Functor.leftUnitor L).hom ≫ (Functor.rightUnitor L).inv

Depends on / 依赖: Functor, Functor.leftUnitor, Functor.rightUnitor, leftUnitor, rightUnitor
-/
def hId (L : C₁ ⥤ C₃) : TwoSquare (𝟭 _) L L (𝟭 _) :=
  (Functor.leftUnitor L).hom ≫ (Functor.rightUnitor L).inv

/-- Notation for the horizontal identity 2-square. -/
scoped notation "𝟙ₕ" => hId -- type as \b1\_h

/-- The vertical identity 2-square. -/
@[simps!]
/--
Definition of `vId` / `vId` 的定义

English:
definition vId
  signature: (T : C₁ ⥤ C₂)
  body: (Functor.rightUnitor T).hom ≫ (Functor.leftUnitor T).inv

中文:
定义 vId
  签名: (T : C₁ ⥤ C₂)
  定义体: (Functor.rightUnitor T).hom ≫ (Functor.leftUnitor T).inv

Depends on / 依赖: Functor, Functor.leftUnitor, Functor.rightUnitor, leftUnitor, rightUnitor
-/
def vId (T : C₁ ⥤ C₂) : TwoSquare T (𝟭 _) (𝟭 _) T :=
  (Functor.rightUnitor T).hom ≫ (Functor.leftUnitor T).inv

/-- Notation for the vertical identity 2-square. -/
scoped notation "𝟙ᵥ" => vId -- type as \b1\_v

/-- Whiskering a 2-square with a natural transformation at the top. -/
@[simps!]
/--
Definition of `whiskerTop` / `whiskerTop` 的定义

English:
definition whiskerTop
  signature: {T' : C₁ ⥤ C₂} (w : TwoSquare T' L R B) (α : T ⟶ T')
  body: .mk _ _ _ _ whiskerRight α R ≫ w.natTrans

中文:
定义 whiskerTop
  签名: {T' : C₁ ⥤ C₂} (w : TwoSquare T' L R B) (α : T ⟶ T')
  定义体: .mk _ _ _ _ whiskerRight α R ≫ w.natTrans
-/
protected def whiskerTop {T' : C₁ ⥤ C₂} (w : TwoSquare T' L R B) (α : T ⟶ T') : TwoSquare T L R B :=
.mk _ _ _ _ whiskerRight α R ≫ w.natTrans

/-- Whiskering a 2-square with a natural transformation at the left side. -/
@[simps!]
/--
Definition of `whiskerLeft` / `whiskerLeft` 的定义

English:
definition whiskerLeft
  signature: {L' : C₁ ⥤ C₃} (w : TwoSquare T L R B) (α : L ⟶ L')
  body: .mk _ _ _ _ w.natTrans ≫ whiskerRight α B

中文:
定义 whiskerLeft
  签名: {L' : C₁ ⥤ C₃} (w : TwoSquare T L R B) (α : L ⟶ L')
  定义体: .mk _ _ _ _ w.natTrans ≫ whiskerRight α B
-/
protected def whiskerLeft {L' : C₁ ⥤ C₃} (w : TwoSquare T L R B) (α : L ⟶ L') :
    TwoSquare T L' R B :=
.mk _ _ _ _ w.natTrans ≫ whiskerRight α B

/-- Whiskering a 2-square with a natural transformation at the right side. -/
@[simps!]
/--
Definition of `whiskerRight` / `whiskerRight` 的定义

English:
definition whiskerRight
  signature: {R' : C₂ ⥤ C₄} (w : TwoSquare T L R' B) (α : R ⟶ R')
  body: .mk _ _ _ _ whiskerLeft T α ≫ w.natTrans

中文:
定义 whiskerRight
  签名: {R' : C₂ ⥤ C₄} (w : TwoSquare T L R' B) (α : R ⟶ R')
  定义体: .mk _ _ _ _ whiskerLeft T α ≫ w.natTrans
-/
protected def whiskerRight {R' : C₂ ⥤ C₄} (w : TwoSquare T L R' B) (α : R ⟶ R') :
    TwoSquare T L R B :=
.mk _ _ _ _ whiskerLeft T α ≫ w.natTrans

/-- Whiskering a 2-square with a natural transformation at the bottom. -/
@[simps!]
/--
Definition of `whiskerBottom` / `whiskerBottom` 的定义

English:
definition whiskerBottom
  signature: {B' : C₃ ⥤ C₄} (w : TwoSquare T L R B) (α : B ⟶ B')
  body: .mk _ _ _ _ w.natTrans ≫ whiskerLeft L α

中文:
定义 whiskerBottom
  签名: {B' : C₃ ⥤ C₄} (w : TwoSquare T L R B) (α : B ⟶ B')
  定义体: .mk _ _ _ _ w.natTrans ≫ whiskerLeft L α
-/
protected def whiskerBottom {B' : C₃ ⥤ C₄} (w : TwoSquare T L R B) (α : B ⟶ B') :
    TwoSquare T L R B' :=
.mk _ _ _ _ w.natTrans ≫ whiskerLeft L α

variable {C₅ : Type u₅} {C₆ : Type u₆} {C₇ : Type u₇} {C₈ : Type u₈}
  [Category.{v₅} C₅] [Category.{v₆} C₆] [Category.{v₇} C₇] [Category.{v₈} C₈]
  {T' : C₂ ⥤ C₅} {R' : C₅ ⥤ C₆} {B' : C₄ ⥤ C₆} {L' : C₃ ⥤ C₇} {R'' : C₄ ⥤ C₈} {B'' : C₇ ⥤ C₈}

/-- The horizontal composition of 2-squares. -/
@[simps!]
/--
Definition of `hComp` / `hComp` 的定义

English:
definition hComp
  signature: (w : TwoSquare T L R B) (w' : TwoSquare T' R R' B')
  body: .mk _ _ _ _ (associator _ _ _).hom ≫ (whiskerLeft T w'.natTrans) ≫
    (associator _ _ _).inv ≫ (whiskerRight w.natTrans B') ≫ (associator _ _ _).hom

中文:
定义 hComp
  签名: (w : TwoSquare T L R B) (w' : TwoSquare T' R R' B')
  定义体: .mk _ _ _ _ (associator _ _ _).hom ≫ (whiskerLeft T w'.natTrans) ≫
    (associator _ _ _).inv ≫ (whiskerRight w.natTrans B') ≫ (associator _ _ _).hom

Depends on / 依赖: associator, natTrans, w.natTrans, whiskerLeft, whiskerRight
-/
def hComp (w : TwoSquare T L R B) (w' : TwoSquare T' R R' B') :
    TwoSquare (T ⋙ T') L R' (B ⋙ B') :=
.mk _ _ _ _ (associator _ _ _).hom ≫ (whiskerLeft T w'.natTrans) ≫
    (associator _ _ _).inv ≫ (whiskerRight w.natTrans B') ≫ (associator _ _ _).hom

/-- Notation for the horizontal composition of 2-squares. -/
scoped infixr:80 " ≫ₕ " => hComp -- type as \gg\_h

/-- The vertical composition of 2-squares. -/
@[simps!]
/--
Definition of `vComp` / `vComp` 的定义

English:
definition vComp
  signature: (w : TwoSquare T L R B) (w' : TwoSquare B L' R'' B'')
  body: .mk _ _ _ _ (associator _ _ _).inv ≫ whiskerRight w.natTrans R'' ≫
    (associator _ _ _).hom ≫ whiskerLeft L w'.natTrans ≫ (associator _ _ _).inv

中文:
定义 vComp
  签名: (w : TwoSquare T L R B) (w' : TwoSquare B L' R'' B'')
  定义体: .mk _ _ _ _ (associator _ _ _).inv ≫ whiskerRight w.natTrans R'' ≫
    (associator _ _ _).hom ≫ whiskerLeft L w'.natTrans ≫ (associator _ _ _).inv

Depends on / 依赖: associator, natTrans, w.natTrans, whiskerLeft, whiskerRight
-/
def vComp (w : TwoSquare T L R B) (w' : TwoSquare B L' R'' B'') :
    TwoSquare T (L ⋙ L') (R ⋙ R'') B'' :=
.mk _ _ _ _ (associator _ _ _).inv ≫ whiskerRight w.natTrans R'' ≫
    (associator _ _ _).hom ≫ whiskerLeft L w'.natTrans ≫ (associator _ _ _).inv

/-- Notation for the vertical composition of 2-squares. -/
scoped infixr:80 " ≫ᵥ " => vComp -- type as \gg\_v

section Interchange

variable {C₉ : Type u₉} [Category.{v₉} C₉] {R₃ : C₆ ⥤ C₉} {B₃ : C₈ ⥤ C₉}

set_option backward.defeqAttrib.useBackward true in
/--
lemma `hCompVCompHComp` / 引理 `hCompVCompHComp`

English:
lemma hCompVCompHComp
  statement: (w₁ : TwoSquare T L R B) (w₂ : TwoSquare T' R R' B')
  proof: by
  unfold hComp vComp whiskerLeft whiskerRight
  ext c
  simp only [comp_obj, NatTrans.comp_app, associator_hom_app, associator_inv_app, comp_id, id_comp,
    map_comp, assoc]
  slice_rhs 2 3 =>
    rw [← Functor.comp_map _ B₃]; rw [← w₄.naturality]
  simp

中文:
引理 hCompVCompHComp
  结论: (w₁ : TwoSquare T L R B) (w₂ : TwoSquare T' R R' B')
  证明: by
  unfold hComp vComp whiskerLeft whiskerRight
  ext c
  simp only [comp_obj, NatTrans.comp_app, associator_hom_app, associator_inv_app, comp_id, id_comp,
    map_comp, assoc]
  slice_rhs 2 3 =>
    rw [← Functor.comp_map _ B₃]; rw [← w₄.naturality]
  simp

Depends on / 依赖: Functor, Functor.comp_map, NatTrans, NatTrans.comp_app, associator_hom_app, associator_inv_app, comp_app, comp_id, comp_map, comp_obj, id_comp, map_comp, naturality, slice_rhs, whiskerLeft, whiskerRight
-/
lemma hCompVCompHComp (w₁ : TwoSquare T L R B) (w₂ : TwoSquare T' R R' B')
    (w₃ : TwoSquare B L' R'' B'') (w₄ : TwoSquare B' R'' R₃ B₃) :
    (w₁ ≫ₕ w₂) ≫ᵥ (w₃ ≫ₕ w₄) = (w₁ ≫ᵥ w₃) ≫ₕ (w₂ ≫ᵥ w₄) := by
  unfold hComp vComp whiskerLeft whiskerRight
  ext c
  simp only [comp_obj, NatTrans.comp_app, associator_hom_app, associator_inv_app, comp_id, id_comp,
    map_comp, assoc]
  slice_rhs 2 3 =>
    rw [← Functor.comp_map _ B₃]; rw [← w₄.naturality]
  simp

end Interchange

end TwoSquare

end CategoryTheory
