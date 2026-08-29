/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Comma.CatCommSq
public import Mathlib.CategoryTheory.Localization.LocalizerMorphism

/-!
# Resolutions for a morphism of localizers

Given a morphism of localizers `Φ : LocalizerMorphism W₁ W₂` (i.e. `W₁` and `W₂` are
morphism properties on categories `C₁` and `C₂`, and we have a functor
`Φ.functor : C₁ ⥤ C₂` which sends morphisms in `W₁` to morphisms in `W₂`), we introduce
the notion of right resolutions of objects in `C₂`, for `X₂ : C₂`.
A right resolution consists of an object `X₁ : C₁` and a morphism
`w : X₂ ⟶ Φ.functor.obj X₁` that is in `W₂`. Then, the typeclass
`Φ.HasRightResolutions` holds when any `X₂ : C₂` has a right resolution.

The type of right resolutions `Φ.RightResolution X₂` is endowed with a category
structure.

Similar definitions are done for left resolutions.

## Future work

* show that if `C` is an abelian category with enough injectives, there is a derivability
  structure associated to the inclusion of the full subcategory of complexes of injective
  objects into the bounded below homotopy category of `C` (TODO @joelriou)
* formalize dual results

## References
* [Bruno Kahn and Georges Maltsiniotis, *Structures de dérivabilité*][KahnMaltsiniotis2008]

-/

@[expose] public section

universe v₁ v₂ v₂' u₁ u₂ u₂'

namespace CategoryTheory

open Category Localization

variable {C₁ C₂ D₁ D₂ H : Type*}
  [Category* C₁] [Category* C₂] [Category* D₁] [Category* D₂] [Category* H]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
  {W₁' : MorphismProperty D₁} {W₂' : MorphismProperty D₂}

namespace LocalizerMorphism

variable (Φ : LocalizerMorphism W₁ W₂)

/--
Definition of `RightResolution` / `RightResolution` 的定义

English:
structure RightResolution
  parameters: (X₂ : C₂)
  axioms and operations (3):
    - {X₁ : C₁}
    - w : X₂ ⟶ Φ.functor.obj X₁
    - hw : W₂ w

中文:
结构 RightResolution
  参数: (X₂ : C₂)
  公理与运算 (3 个):
    - {X₁ : C₁}
    - w : X₂ ⟶ Φ.functor.obj X₁
    - hw : W₂ w
-/
structure RightResolution (X₂ : C₂) where
  /-- an object in the source category -/
  {X₁ : C₁}
  /-- a morphism to an object of the form `Φ.functor.obj X₁` -/
  w : X₂ ⟶ Φ.functor.obj X₁
  hw : W₂ w

/--
Definition of `LeftResolution` / `LeftResolution` 的定义

English:
structure LeftResolution
  parameters: (X₂ : C₂)
  axioms and operations (3):
    - {X₁ : C₁}
    - w : Φ.functor.obj X₁ ⟶ X₂
    - hw : W₂ w

中文:
结构 LeftResolution
  参数: (X₂ : C₂)
  公理与运算 (3 个):
    - {X₁ : C₁}
    - w : Φ.functor.obj X₁ ⟶ X₂
    - hw : W₂ w
-/
structure LeftResolution (X₂ : C₂) where
  /-- an object in the source category -/
  {X₁ : C₁}
  /-- a morphism from an object of the form `Φ.functor.obj X₁` -/
  w : Φ.functor.obj X₁ ⟶ X₂
  hw : W₂ w

variable {Φ X₂} in
/--
lemma `RightResolution.mk_surjective` / 引理 `RightResolution.mk_surjective`

English:
lemma RightResolution.mk_surjective
  given: (R : Φ.RightResolution X₂)
  proof: ⟨_, R.w, R.hw, rfl⟩

中文:
引理 RightResolution.mk_surjective
  条件: (R : Φ.RightResolution X₂)
  证明: ⟨_, R.w, R.hw, rfl⟩

Depends on / 依赖: R.hw
-/
lemma RightResolution.mk_surjective (R : Φ.RightResolution X₂) :
    exists (X₁ : C₁) (w : X₂ ⟶ Φ.functor.obj X₁) (hw : W₂ w), R = RightResolution.mk w hw :=
  ⟨_, R.w, R.hw, rfl⟩

variable {Φ X₂} in
/--
lemma `LeftResolution.mk_surjective` / 引理 `LeftResolution.mk_surjective`

English:
lemma LeftResolution.mk_surjective
  given: (L : Φ.LeftResolution X₂)
  proof: ⟨_, L.w, L.hw, rfl⟩

中文:
引理 LeftResolution.mk_surjective
  条件: (L : Φ.LeftResolution X₂)
  证明: ⟨_, L.w, L.hw, rfl⟩

Depends on / 依赖: L.hw
-/
lemma LeftResolution.mk_surjective (L : Φ.LeftResolution X₂) :
    exists (X₁ : C₁) (w : Φ.functor.obj X₁ ⟶ X₂) (hw : W₂ w), L = LeftResolution.mk w hw :=
  ⟨_, L.w, L.hw, rfl⟩

/--
Definition of `HasRightResolutions` / `HasRightResolutions` 的定义

English:
abbreviation HasRightResolutions
  body: forall (X₂ : C₂), Nonempty (Φ.RightResolution X₂)

中文:
缩写 HasRightResolutions
  定义体: forall (X₂ : C₂), Nonempty (Φ.RightResolution X₂)

Depends on / 依赖: Nonempty, RightResolution
-/
abbrev HasRightResolutions := forall (X₂ : C₂), Nonempty (Φ.RightResolution X₂)

/--
Definition of `HasLeftResolutions` / `HasLeftResolutions` 的定义

English:
abbreviation HasLeftResolutions
  body: forall (X₂ : C₂), Nonempty (Φ.LeftResolution X₂)

中文:
缩写 HasLeftResolutions
  定义体: forall (X₂ : C₂), Nonempty (Φ.LeftResolution X₂)

Depends on / 依赖: LeftResolution, Nonempty
-/
abbrev HasLeftResolutions := forall (X₂ : C₂), Nonempty (Φ.LeftResolution X₂)

namespace RightResolution

variable {Φ} {X₂ : C₂}

/-- The type of morphisms in the category `Φ.RightResolution X₂`. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (R R' : Φ.RightResolution X₂)
  axioms and operations (2):
    - f : R.X₁ ⟶ R'.X₁
    - comm : R.w ≫ Φ.functor.map f = R'.w  [default: by cat_disch]

中文:
结构 Hom
  参数: (R R' : Φ.RightResolution X₂)
  公理与运算 (2 个):
    - f : R.X₁ ⟶ R'.X₁
    - comm : R.w ≫ Φ.functor.map f = R'.w  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure Hom (R R' : Φ.RightResolution X₂) where
  /-- a morphism in the source category -/
  f : R.X₁ ⟶ R'.X₁
  comm : R.w ≫ Φ.functor.map f = R'.w := by cat_disch

attribute [reassoc (attr := simp)] Hom.comm

/-- The identity of an object in `Φ.RightResolution X₂`. -/
@[simps]
/--
Definition of `Hom.id` / `Hom.id` 的定义

English:
definition Hom.id
  signature: (R : Φ.RightResolution X₂)
  body: 𝟙 _

中文:
定义 Hom.id
  签名: (R : Φ.RightResolution X₂)
  定义体: 𝟙 _
-/
def Hom.id (R : Φ.RightResolution X₂) : Hom R R where
  f := 𝟙 _

/-- The composition of morphisms in `Φ.RightResolution X₂`. -/
@[simps]
/--
Definition of `Hom.comp` / `Hom.comp` 的定义

English:
definition Hom.comp
  signature: {R R' R'' : Φ.RightResolution X₂}
  body: φ.f ≫ ψ.f

中文:
定义 Hom.comp
  签名: {R R' R'' : Φ.RightResolution X₂}
  定义体: φ.f ≫ ψ.f
-/
def Hom.comp {R R' R'' : Φ.RightResolution X₂}
    (φ : Hom R R') (ψ : Hom R' R'') :
    Hom R R'' where
  f := φ.f ≫ ψ.f

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (Φ.RightResolution X₂)
  body: Hom
  id := Hom.id
  comp := Hom.comp

@[simp]

中文:
实例 :
  签名: Category (Φ.RightResolution X₂)
  定义体: Hom
  id := Hom.id
  comp := Hom.comp

@[simp]
-/
instance : Category (Φ.RightResolution X₂) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

@[simp]
/--
lemma `id_f` / 引理 `id_f`

English:
lemma id_f
  given: (R : Φ.RightResolution X₂)
  statement: Hom.f (𝟙 R) = 𝟙 R.X₁
  proof: rfl

@[simp, reassoc]

中文:
引理 id_f
  条件: (R : Φ.RightResolution X₂)
  结论: Hom.f (𝟙 R) = 𝟙 R.X₁
  证明: rfl

@[simp, reassoc]
-/
lemma id_f (R : Φ.RightResolution X₂) : Hom.f (𝟙 R) = 𝟙 R.X₁ := rfl

@[simp, reassoc]
/--
lemma `comp_f` / 引理 `comp_f`

English:
lemma comp_f
  given: {R R' R'' : Φ.RightResolution X₂} (φ : R ⟶ R') (ψ : R' ⟶ R'')
  proof: rfl

@[ext]

中文:
引理 comp_f
  条件: {R R' R'' : Φ.RightResolution X₂} (φ : R ⟶ R') (ψ : R' ⟶ R'')
  证明: rfl

@[ext]
-/
lemma comp_f {R R' R'' : Φ.RightResolution X₂} (φ : R ⟶ R') (ψ : R' ⟶ R'') :
    (φ ≫ ψ).f = φ.f ≫ ψ.f := rfl

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {R R' : Φ.RightResolution X₂} {φ₁ φ₂ : R ⟶ R'} (h : φ₁.f = φ₂.f)
  proof: Hom.ext h

中文:
引理 hom_ext
  条件: {R R' : Φ.RightResolution X₂} {φ₁ φ₂ : R ⟶ R'} (h : φ₁.f = φ₂.f)
  证明: Hom.ext h

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {R R' : Φ.RightResolution X₂} {φ₁ φ₂ : R ⟶ R'} (h : φ₁.f = φ₂.f) :
    φ₁ = φ₂ :=
  Hom.ext h

end RightResolution

namespace LeftResolution

variable {Φ} {X₂ : C₂}

/-- The type of morphisms in the category `Φ.LeftResolution X₂`. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (L L' : Φ.LeftResolution X₂)
  axioms and operations (2):
    - f : L.X₁ ⟶ L'.X₁
    - comm : Φ.functor.map f ≫ L'.w = L.w  [default: by cat_disch]

中文:
结构 Hom
  参数: (L L' : Φ.LeftResolution X₂)
  公理与运算 (2 个):
    - f : L.X₁ ⟶ L'.X₁
    - comm : Φ.functor.map f ≫ L'.w = L.w  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure Hom (L L' : Φ.LeftResolution X₂) where
  /-- a morphism in the source category -/
  f : L.X₁ ⟶ L'.X₁
  comm : Φ.functor.map f ≫ L'.w = L.w := by cat_disch

attribute [reassoc (attr := simp)] Hom.comm

/-- The identity of an object in `Φ.LeftResolution X₂`. -/
@[simps]
/--
Definition of `Hom.id` / `Hom.id` 的定义

English:
definition Hom.id
  signature: (L : Φ.LeftResolution X₂)
  body: 𝟙 _

中文:
定义 Hom.id
  签名: (L : Φ.LeftResolution X₂)
  定义体: 𝟙 _
-/
def Hom.id (L : Φ.LeftResolution X₂) : Hom L L where
  f := 𝟙 _

/-- The composition of morphisms in `Φ.LeftResolution X₂`. -/
@[simps]
/--
Definition of `Hom.comp` / `Hom.comp` 的定义

English:
definition Hom.comp
  signature: {L L' L'' : Φ.LeftResolution X₂}
  body: φ.f ≫ ψ.f

中文:
定义 Hom.comp
  签名: {L L' L'' : Φ.LeftResolution X₂}
  定义体: φ.f ≫ ψ.f
-/
def Hom.comp {L L' L'' : Φ.LeftResolution X₂}
    (φ : Hom L L') (ψ : Hom L' L'') :
    Hom L L'' where
  f := φ.f ≫ ψ.f

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (Φ.LeftResolution X₂)
  body: Hom
  id := Hom.id
  comp := Hom.comp

@[simp]

中文:
实例 :
  签名: Category (Φ.LeftResolution X₂)
  定义体: Hom
  id := Hom.id
  comp := Hom.comp

@[simp]
-/
instance : Category (Φ.LeftResolution X₂) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

@[simp]
/--
lemma `id_f` / 引理 `id_f`

English:
lemma id_f
  given: (L : Φ.LeftResolution X₂)
  statement: Hom.f (𝟙 L) = 𝟙 L.X₁
  proof: rfl

@[simp, reassoc]

中文:
引理 id_f
  条件: (L : Φ.LeftResolution X₂)
  结论: Hom.f (𝟙 L) = 𝟙 L.X₁
  证明: rfl

@[simp, reassoc]
-/
lemma id_f (L : Φ.LeftResolution X₂) : Hom.f (𝟙 L) = 𝟙 L.X₁ := rfl

@[simp, reassoc]
/--
lemma `comp_f` / 引理 `comp_f`

English:
lemma comp_f
  given: {L L' L'' : Φ.LeftResolution X₂} (φ : L ⟶ L') (ψ : L' ⟶ L'')
  proof: rfl

@[ext]

中文:
引理 comp_f
  条件: {L L' L'' : Φ.LeftResolution X₂} (φ : L ⟶ L') (ψ : L' ⟶ L'')
  证明: rfl

@[ext]
-/
lemma comp_f {L L' L'' : Φ.LeftResolution X₂} (φ : L ⟶ L') (ψ : L' ⟶ L'') :
    (φ ≫ ψ).f = φ.f ≫ ψ.f := rfl

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {L L' : Φ.LeftResolution X₂} {φ₁ φ₂ : L ⟶ L'} (h : φ₁.f = φ₂.f)
  proof: Hom.ext h

中文:
引理 hom_ext
  条件: {L L' : Φ.LeftResolution X₂} {φ₁ φ₂ : L ⟶ L'} (h : φ₁.f = φ₂.f)
  证明: Hom.ext h

Depends on / 依赖: Hom.ext
-/
lemma hom_ext {L L' : Φ.LeftResolution X₂} {φ₁ φ₂ : L ⟶ L'} (h : φ₁.f = φ₂.f) :
    φ₁ = φ₂ :=
  Hom.ext h

end LeftResolution

variable {Φ}

/-- The canonical map `Φ.LeftResolution X₂ → Φ.op.RightResolution (Opposite.op X₂)`. -/
@[simps]
/--
Definition of `LeftResolution.op` / `LeftResolution.op` 的定义

English:
definition LeftResolution.op
  signature: {X₂ : C₂} (L : Φ.LeftResolution X₂)
  body: Opposite.op L.X₁
  w := L.w.op
  hw := L.hw

中文:
定义 LeftResolution.op
  签名: {X₂ : C₂} (L : Φ.LeftResolution X₂)
  定义体: Opposite.op L.X₁
  w := L.w.op
  hw := L.hw

Depends on / 依赖: Opposite, Opposite.op
-/
def LeftResolution.op {X₂ : C₂} (L : Φ.LeftResolution X₂) :
    Φ.op.RightResolution (Opposite.op X₂) where
  X₁ := Opposite.op L.X₁
  w := L.w.op
  hw := L.hw

/-- The canonical map `Φ.op.LeftResolution X₂ → Φ.RightResolution X₂`. -/
@[simps]
/--
Definition of `LeftResolution.unop` / `LeftResolution.unop` 的定义

English:
definition LeftResolution.unop
  signature: {X₂ : C₂ᵒᵖ} (L : Φ.op.LeftResolution X₂)
  body: Opposite.unop L.X₁
  w := L.w.unop
  hw := L.hw

中文:
定义 LeftResolution.unop
  签名: {X₂ : C₂ᵒᵖ} (L : Φ.op.LeftResolution X₂)
  定义体: Opposite.unop L.X₁
  w := L.w.unop
  hw := L.hw

Depends on / 依赖: Opposite, Opposite.unop
-/
def LeftResolution.unop {X₂ : C₂ᵒᵖ} (L : Φ.op.LeftResolution X₂) :
    Φ.RightResolution X₂.unop where
  X₁ := Opposite.unop L.X₁
  w := L.w.unop
  hw := L.hw

/-- The canonical map `Φ.RightResolution X₂ → Φ.op.LeftResolution (Opposite.op X₂)`. -/
@[simps]
/--
Definition of `RightResolution.op` / `RightResolution.op` 的定义

English:
definition RightResolution.op
  signature: {X₂ : C₂} (L : Φ.RightResolution X₂)
  body: Opposite.op L.X₁
  w := L.w.op
  hw := L.hw

中文:
定义 RightResolution.op
  签名: {X₂ : C₂} (L : Φ.RightResolution X₂)
  定义体: Opposite.op L.X₁
  w := L.w.op
  hw := L.hw

Depends on / 依赖: Opposite, Opposite.op
-/
def RightResolution.op {X₂ : C₂} (L : Φ.RightResolution X₂) :
    Φ.op.LeftResolution (Opposite.op X₂) where
  X₁ := Opposite.op L.X₁
  w := L.w.op
  hw := L.hw

/-- The canonical map `Φ.op.RightResolution X₂ → Φ.LeftResolution X₂`. -/
@[simps]
/--
Definition of `RightResolution.unop` / `RightResolution.unop` 的定义

English:
definition RightResolution.unop
  signature: {X₂ : C₂ᵒᵖ} (L : Φ.op.RightResolution X₂)
  body: Opposite.unop L.X₁
  w := L.w.unop
  hw := L.hw

中文:
定义 RightResolution.unop
  签名: {X₂ : C₂ᵒᵖ} (L : Φ.op.RightResolution X₂)
  定义体: Opposite.unop L.X₁
  w := L.w.unop
  hw := L.hw

Depends on / 依赖: Opposite, Opposite.unop
-/
def RightResolution.unop {X₂ : C₂ᵒᵖ} (L : Φ.op.RightResolution X₂) :
    Φ.LeftResolution X₂.unop where
  X₁ := Opposite.unop L.X₁
  w := L.w.unop
  hw := L.hw

variable (Φ)

/--
lemma `nonempty_leftResolution_iff_op` / 引理 `nonempty_leftResolution_iff_op`

English:
lemma nonempty_leftResolution_iff_op
  given: (X₂ : C₂)
  proof: Equiv.nonempty_congr
    { toFun := fun L => L.op
      invFun := fun R => R.unop }

中文:
引理 nonempty_leftResolution_iff_op
  条件: (X₂ : C₂)
  证明: Equiv.nonempty_congr
    { toFun := fun L => L.op
      invFun := fun R => R.unop }

Depends on / 依赖: Equiv.nonempty_congr, L.op, R.unop, invFun, nonempty_congr
-/
lemma nonempty_leftResolution_iff_op (X₂ : C₂) :
    Nonempty (Φ.LeftResolution X₂) ↔ Nonempty (Φ.op.RightResolution (Opposite.op X₂)) :=
  Equiv.nonempty_congr
    { toFun := fun L => L.op
      invFun := fun R => R.unop }

/--
lemma `nonempty_rightResolution_iff_op` / 引理 `nonempty_rightResolution_iff_op`

English:
lemma nonempty_rightResolution_iff_op
  given: (X₂ : C₂)
  proof: Equiv.nonempty_congr
    { toFun := fun R => R.op
      invFun := fun L => L.unop }

中文:
引理 nonempty_rightResolution_iff_op
  条件: (X₂ : C₂)
  证明: Equiv.nonempty_congr
    { toFun := fun R => R.op
      invFun := fun L => L.unop }

Depends on / 依赖: Equiv.nonempty_congr, L.unop, R.op, invFun, nonempty_congr
-/
lemma nonempty_rightResolution_iff_op (X₂ : C₂) :
    Nonempty (Φ.RightResolution X₂) ↔ Nonempty (Φ.op.LeftResolution (Opposite.op X₂)) :=
  Equiv.nonempty_congr
    { toFun := fun R => R.op
      invFun := fun L => L.unop }

/--
lemma `hasLeftResolutions_iff_op` / 引理 `hasLeftResolutions_iff_op`

English:
lemma hasLeftResolutions_iff_op
  statement: Φ.HasLeftResolutions ↔ Φ.op.HasRightResolutions
  proof: ⟨fun _ X₂ => ⟨(Classical.arbitrary (Φ.LeftResolution X₂.unop)).op⟩,
    fun _ X₂ => ⟨(Classical.arbitrary (Φ.op.RightResolution (Opposite.op X₂))).unop⟩⟩

中文:
引理 hasLeftResolutions_iff_op
  结论: Φ.HasLeftResolutions ↔ Φ.op.HasRightResolutions
  证明: ⟨fun _ X₂ => ⟨(Classical.arbitrary (Φ.LeftResolution X₂.unop)).op⟩,
    fun _ X₂ => ⟨(Classical.arbitrary (Φ.op.RightResolution (Opposite.op X₂))).unop⟩⟩

Depends on / 依赖: Classical, Classical.arbitrary, LeftResolution, Opposite, Opposite.op, RightResolution, arbitrary, op.RightResolution
-/
lemma hasLeftResolutions_iff_op : Φ.HasLeftResolutions ↔ Φ.op.HasRightResolutions :=
  ⟨fun _ X₂ => ⟨(Classical.arbitrary (Φ.LeftResolution X₂.unop)).op⟩,
    fun _ X₂ => ⟨(Classical.arbitrary (Φ.op.RightResolution (Opposite.op X₂))).unop⟩⟩

/--
lemma `hasRightResolutions_iff_op` / 引理 `hasRightResolutions_iff_op`

English:
lemma hasRightResolutions_iff_op
  statement: Φ.HasRightResolutions ↔ Φ.op.HasLeftResolutions
  proof: ⟨fun _ X₂ => ⟨(Classical.arbitrary (Φ.RightResolution X₂.unop)).op⟩,
    fun _ X₂ => ⟨(Classical.arbitrary (Φ.op.LeftResolution (Opposite.op X₂))).unop⟩⟩

中文:
引理 hasRightResolutions_iff_op
  结论: Φ.HasRightResolutions ↔ Φ.op.HasLeftResolutions
  证明: ⟨fun _ X₂ => ⟨(Classical.arbitrary (Φ.RightResolution X₂.unop)).op⟩,
    fun _ X₂ => ⟨(Classical.arbitrary (Φ.op.LeftResolution (Opposite.op X₂))).unop⟩⟩

Depends on / 依赖: Classical, Classical.arbitrary, LeftResolution, Opposite, Opposite.op, RightResolution, arbitrary, op.LeftResolution
-/
lemma hasRightResolutions_iff_op : Φ.HasRightResolutions ↔ Φ.op.HasLeftResolutions :=
  ⟨fun _ X₂ => ⟨(Classical.arbitrary (Φ.RightResolution X₂.unop)).op⟩,
    fun _ X₂ => ⟨(Classical.arbitrary (Φ.op.LeftResolution (Opposite.op X₂))).unop⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Φ.HasRightResolutions]
  signature: : Φ.op.HasLeftResolutions
  body: by
  rwa [← hasRightResolutions_iff_op]

中文:
实例 [Φ.HasRightResolutions]
  签名: : Φ.op.HasLeftResolutions
  定义体: by
  rwa [← hasRightResolutions_iff_op]

Depends on / 依赖: hasRightResolutions_iff_op
-/
instance [Φ.HasRightResolutions] : Φ.op.HasLeftResolutions := by
  rwa [← hasRightResolutions_iff_op]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Φ.HasLeftResolutions]
  signature: : Φ.op.HasRightResolutions
  body: by
  rwa [← hasLeftResolutions_iff_op]

中文:
实例 [Φ.HasLeftResolutions]
  签名: : Φ.op.HasRightResolutions
  定义体: by
  rwa [← hasLeftResolutions_iff_op]

Depends on / 依赖: hasLeftResolutions_iff_op
-/
instance [Φ.HasLeftResolutions] : Φ.op.HasRightResolutions := by
  rwa [← hasLeftResolutions_iff_op]

/-- The functor `(Φ.LeftResolution X₂)ᵒᵖ ⥤ Φ.op.RightResolution (Opposite.op X₂)`. -/
@[simps]
/--
Definition of `LeftResolution.opFunctor` / `LeftResolution.opFunctor` 的定义

English:
definition LeftResolution.opFunctor
  signature: (X₂ : C₂)
  body: L.unop.op
  map φ :=
    { f := φ.unop.f.op
      comm := Quiver.Hom.unop_inj φ.unop.comm }

中文:
定义 LeftResolution.opFunctor
  签名: (X₂ : C₂)
  定义体: L.unop.op
  map φ :=
    { f := φ.unop.f.op
      comm := Quiver.Hom.unop_inj φ.unop.comm }

Depends on / 依赖: L.unop.op
-/
def LeftResolution.opFunctor (X₂ : C₂) :
    (Φ.LeftResolution X₂)ᵒᵖ ⥤ Φ.op.RightResolution (Opposite.op X₂) where
  obj L := L.unop.op
  map φ :=
    { f := φ.unop.f.op
      comm := Quiver.Hom.unop_inj φ.unop.comm }

/-- The functor `(Φ.op.RightResolution X₂)ᵒᵖ ⥤ Φ.LeftResolution X₂.unop`. -/
@[simps]
/--
Definition of `RightResolution.unopFunctor` / `RightResolution.unopFunctor` 的定义

English:
definition RightResolution.unopFunctor
  signature: (X₂ : C₂ᵒᵖ)
  body: R.unop.unop
  map φ :=
    { f := φ.unop.f.unop
      comm := Quiver.Hom.op_inj φ.unop.comm }

中文:
定义 RightResolution.unopFunctor
  签名: (X₂ : C₂ᵒᵖ)
  定义体: R.unop.unop
  map φ :=
    { f := φ.unop.f.unop
      comm := Quiver.Hom.op_inj φ.unop.comm }

Depends on / 依赖: R.unop.unop
-/
def RightResolution.unopFunctor (X₂ : C₂ᵒᵖ) :
    (Φ.op.RightResolution X₂)ᵒᵖ ⥤ Φ.LeftResolution X₂.unop where
  obj R := R.unop.unop
  map φ :=
    { f := φ.unop.f.unop
      comm := Quiver.Hom.op_inj φ.unop.comm }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The equivalence of categories
`(Φ.LeftResolution X₂)ᵒᵖ ≌ Φ.op.RightResolution (Opposite.op X₂)`. -/
@[simps]
/--
Definition of `LeftResolution.opEquivalence` / `LeftResolution.opEquivalence` 的定义

English:
definition LeftResolution.opEquivalence
  signature: (X₂ : C₂)
  body: LeftResolution.opFunctor Φ X₂
  inverse := (RightResolution.unopFunctor Φ (Opposite.op X₂)).rightOp
  unitIso := Iso.refl _
  counitIso := Iso.refl _

中文:
定义 LeftResolution.opEquivalence
  签名: (X₂ : C₂)
  定义体: LeftResolution.opFunctor Φ X₂
  inverse := (RightResolution.unopFunctor Φ (Opposite.op X₂)).rightOp
  unitIso := Iso.refl _
  counitIso := Iso.refl _

Depends on / 依赖: LeftResolution, LeftResolution.opFunctor, opFunctor
-/
def LeftResolution.opEquivalence (X₂ : C₂) :
    (Φ.LeftResolution X₂)ᵒᵖ ≌ Φ.op.RightResolution (Opposite.op X₂) where
  functor := LeftResolution.opFunctor Φ X₂
  inverse := (RightResolution.unopFunctor Φ (Opposite.op X₂)).rightOp
  unitIso := Iso.refl _
  counitIso := Iso.refl _

section

variable (L₂ : C₂ ⥤ D₂) [L₂.IsLocalization W₂]

/--
lemma `essSurj_of_hasRightResolutions` / 引理 `essSurj_of_hasRightResolutions`

English:
lemma essSurj_of_hasRightResolutions
  given: [Φ.HasRightResolutions]
  statement: (Φ.functor ⋙ L₂).EssSurj where
  proof: by
    have := Localization.essSurj L₂ W₂
    have R : Φ.RightResolution (L₂.objPreimage X₂) := Classical.arbitrary _
    exact ⟨R.X₁, ⟨(Localization.isoOfHom L₂ W₂ _ R.hw).symm ≪≫ L₂.objObjPreimageIso X₂⟩⟩

中文:
引理 essSurj_of_hasRightResolutions
  条件: [Φ.HasRightResolutions]
  结论: (Φ.functor ⋙ L₂).EssSurj where
  证明: by
    have := Localization.essSurj L₂ W₂
    have R : Φ.RightResolution (L₂.objPreimage X₂) := Classical.arbitrary _
    exact ⟨R.X₁, ⟨(Localization.isoOfHom L₂ W₂ _ R.hw).symm ≪≫ L₂.objObjPreimageIso X₂⟩⟩

Depends on / 依赖: Classical, Classical.arbitrary, Localization, Localization.essSurj, Localization.isoOfHom, R.hw, RightResolution, arbitrary, essSurj, isoOfHom, objObjPreimageIso, objPreimage
-/
lemma essSurj_of_hasRightResolutions [Φ.HasRightResolutions] : (Φ.functor ⋙ L₂).EssSurj where
  mem_essImage X₂ := by
    have := Localization.essSurj L₂ W₂
    have R : Φ.RightResolution (L₂.objPreimage X₂) := Classical.arbitrary _
    exact ⟨R.X₁, ⟨(Localization.isoOfHom L₂ W₂ _ R.hw).symm ≪≫ L₂.objObjPreimageIso X₂⟩⟩

/--
lemma `isIso_iff_of_hasRightResolutions` / 引理 `isIso_iff_of_hasRightResolutions`

English:
lemma isIso_iff_of_hasRightResolutions
  given: [Φ.HasRightResolutions] {F G : D₂ ⥤ H} (α : F ⟶ G)
  proof: by
  constructor
  · intros
    infer_instance
  · intro hα
    have : forall (X₂ : D₂), IsIso (α.app X₂) := fun X₂ => by
      have := Φ.essSurj_of_hasRightResolutions L₂
      rw [← NatTrans.isIso_app_iff_of_iso α ((Φ.functor ⋙ L₂).objObjPreimageIso X₂)]
      apply hα
    exact NatIso.isIso_of_is

中文:
引理 isIso_iff_of_hasRightResolutions
  条件: [Φ.HasRightResolutions] {F G : D₂ ⥤ H} (α : F ⟶ G)
  证明: by
  constructor
  · intros
    infer_instance
  · intro hα
    have : forall (X₂ : D₂), IsIso (α.app X₂) := fun X₂ => by
      have := Φ.essSurj_of_hasRightResolutions L₂
      rw [← NatTrans.isIso_app_iff_of_iso α ((Φ.functor ⋙ L₂).objObjPreimageIso X₂)]
      apply hα
    exact NatIso.isIso_of_is

Depends on / 依赖: NatIso, NatIso.isIso_of_isIso_app, NatTrans, NatTrans.isIso_app_iff_of_iso, essSurj_of_hasRightResolutions, functor, infer_instance, intros, isIso_app_iff_of_iso, isIso_of_isIso_app, objObjPreimageIso
-/
lemma isIso_iff_of_hasRightResolutions [Φ.HasRightResolutions] {F G : D₂ ⥤ H} (α : F ⟶ G) :
    IsIso α ↔ forall (X₁ : C₁), IsIso (α.app (L₂.obj (Φ.functor.obj X₁))) := by
  constructor
  · intros
    infer_instance
  · intro hα
    have : forall (X₂ : D₂), IsIso (α.app X₂) := fun X₂ => by
      have := Φ.essSurj_of_hasRightResolutions L₂
      rw [← NatTrans.isIso_app_iff_of_iso α ((Φ.functor ⋙ L₂).objObjPreimageIso X₂)]
      apply hα
    exact NatIso.isIso_of_isIso_app α

/--
lemma `essSurj_of_hasLeftResolutions` / 引理 `essSurj_of_hasLeftResolutions`

English:
lemma essSurj_of_hasLeftResolutions
  given: [Φ.HasLeftResolutions]
  statement: (Φ.functor ⋙ L₂).EssSurj where
  proof: by
    have := Localization.essSurj L₂ W₂
    have L : Φ.LeftResolution (L₂.objPreimage X₂) := Classical.arbitrary _
    exact ⟨L.X₁, ⟨Localization.isoOfHom L₂ W₂ _ L.hw ≪≫ L₂.objObjPreimageIso X₂⟩⟩

中文:
引理 essSurj_of_hasLeftResolutions
  条件: [Φ.HasLeftResolutions]
  结论: (Φ.functor ⋙ L₂).EssSurj where
  证明: by
    have := Localization.essSurj L₂ W₂
    have L : Φ.LeftResolution (L₂.objPreimage X₂) := Classical.arbitrary _
    exact ⟨L.X₁, ⟨Localization.isoOfHom L₂ W₂ _ L.hw ≪≫ L₂.objObjPreimageIso X₂⟩⟩

Depends on / 依赖: Classical, Classical.arbitrary, L.hw, LeftResolution, Localization, Localization.essSurj, Localization.isoOfHom, arbitrary, essSurj, isoOfHom, objObjPreimageIso, objPreimage
-/
lemma essSurj_of_hasLeftResolutions [Φ.HasLeftResolutions] : (Φ.functor ⋙ L₂).EssSurj where
  mem_essImage X₂ := by
    have := Localization.essSurj L₂ W₂
    have L : Φ.LeftResolution (L₂.objPreimage X₂) := Classical.arbitrary _
    exact ⟨L.X₁, ⟨Localization.isoOfHom L₂ W₂ _ L.hw ≪≫ L₂.objObjPreimageIso X₂⟩⟩

/--
lemma `isIso_iff_of_hasLeftResolutions` / 引理 `isIso_iff_of_hasLeftResolutions`

English:
lemma isIso_iff_of_hasLeftResolutions
  given: [Φ.HasLeftResolutions] {F G : D₂ ⥤ H} (α : F ⟶ G)
  proof: by
  constructor
  · intros
    infer_instance
  · intro hα
    have : forall (X₂ : D₂), IsIso (α.app X₂) := fun X₂ => by
      have := Φ.essSurj_of_hasLeftResolutions L₂
      rw [← NatTrans.isIso_app_iff_of_iso α ((Φ.functor ⋙ L₂).objObjPreimageIso X₂)]
      apply hα
    exact NatIso.isIso_of_isI

中文:
引理 isIso_iff_of_hasLeftResolutions
  条件: [Φ.HasLeftResolutions] {F G : D₂ ⥤ H} (α : F ⟶ G)
  证明: by
  constructor
  · intros
    infer_instance
  · intro hα
    have : forall (X₂ : D₂), IsIso (α.app X₂) := fun X₂ => by
      have := Φ.essSurj_of_hasLeftResolutions L₂
      rw [← NatTrans.isIso_app_iff_of_iso α ((Φ.functor ⋙ L₂).objObjPreimageIso X₂)]
      apply hα
    exact NatIso.isIso_of_isI

Depends on / 依赖: NatIso, NatIso.isIso_of_isIso_app, NatTrans, NatTrans.isIso_app_iff_of_iso, essSurj_of_hasLeftResolutions, functor, infer_instance, intros, isIso_app_iff_of_iso, isIso_of_isIso_app, objObjPreimageIso
-/
lemma isIso_iff_of_hasLeftResolutions [Φ.HasLeftResolutions] {F G : D₂ ⥤ H} (α : F ⟶ G) :
    IsIso α ↔ forall (X₁ : C₁), IsIso (α.app (L₂.obj (Φ.functor.obj X₁))) := by
  constructor
  · intros
    infer_instance
  · intro hα
    have : forall (X₂ : D₂), IsIso (α.app X₂) := fun X₂ => by
      have := Φ.essSurj_of_hasLeftResolutions L₂
      rw [← NatTrans.isIso_app_iff_of_iso α ((Φ.functor ⋙ L₂).objObjPreimageIso X₂)]
      apply hα
    exact NatIso.isIso_of_isIso_app α

end

section

variable {T : LocalizerMorphism W₁ W₂} {L : LocalizerMorphism W₁ W₁'}
  {R : LocalizerMorphism W₂ W₂'} {B : LocalizerMorphism W₁' W₂'}

set_option backward.defeqAttrib.useBackward true in
/--
lemma `hasRightResolutions_of_iso_of_essSurj` / 引理 `hasRightResolutions_of_iso_of_essSurj`

English:
lemma hasRightResolutions_of_iso_of_essSurj
  proof: by
  intro Y₂
  obtain ⟨X₂, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := R.functor) Y₂
  let ρ : T.RightResolution X₂ := Classical.arbitrary _
  exact ⟨{
    X₁ := L.functor.obj ρ.X₁
    w := e.inv ≫ R.functor.map ρ.w ≫ iso.hom.app _
    hw := (W₂'.arrow_mk_iso_iff (Arrow.isoMk e (iso.app _))).1 (R.ma

中文:
引理 hasRightResolutions_of_iso_of_essSurj
  证明: by
  intro Y₂
  obtain ⟨X₂, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := R.functor) Y₂
  let ρ : T.RightResolution X₂ := Classical.arbitrary _
  exact ⟨{
    X₁ := L.functor.obj ρ.X₁
    w := e.inv ≫ R.functor.map ρ.w ≫ iso.hom.app _
    hw := (W₂'.arrow_mk_iso_iff (Arrow.isoMk e (iso.app _))).1 (R.ma

Depends on / 依赖: Arrow.isoMk, Classical, Classical.arbitrary, EssSurj, Functor, Functor.EssSurj.mem_essImage, L.functor.obj, R.functor, R.functor.map, R.map, RightResolution, T.RightResolution, arbitrary, arrow_mk_iso_iff, e.inv, functor, iso.app, iso.hom.app, mem_essImage
-/
lemma hasRightResolutions_of_iso_of_essSurj
    [R.functor.EssSurj] [W₂'.RespectsIso]
    (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor) [T.HasRightResolutions] :
    B.HasRightResolutions := by
  intro Y₂
  obtain ⟨X₂, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := R.functor) Y₂
  let ρ : T.RightResolution X₂ := Classical.arbitrary _
  exact ⟨{
    X₁ := L.functor.obj ρ.X₁
    w := e.inv ≫ R.functor.map ρ.w ≫ iso.hom.app _
    hw := (W₂'.arrow_mk_iso_iff (Arrow.isoMk e (iso.app _))).1 (R.map _ ρ.hw) }⟩

set_option backward.isDefEq.respectTransparency false in
/--
lemma `hasLeftResolutions_of_iso_of_essSurj` / 引理 `hasLeftResolutions_of_iso_of_essSurj`

English:
lemma hasLeftResolutions_of_iso_of_essSurj
  proof: by
  intro Y₂
  obtain ⟨X₂, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := R.functor) Y₂
  let ρ : T.LeftResolution X₂ := Classical.arbitrary _
  exact ⟨{
    X₁ := L.functor.obj ρ.X₁
    w := iso.inv.app _ ≫ R.functor.map ρ.w ≫ e.hom
    hw := (W₂'.arrow_mk_iso_iff (Arrow.isoMk (iso.app _) e)).1 (R.map

中文:
引理 hasLeftResolutions_of_iso_of_essSurj
  证明: by
  intro Y₂
  obtain ⟨X₂, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := R.functor) Y₂
  let ρ : T.LeftResolution X₂ := Classical.arbitrary _
  exact ⟨{
    X₁ := L.functor.obj ρ.X₁
    w := iso.inv.app _ ≫ R.functor.map ρ.w ≫ e.hom
    hw := (W₂'.arrow_mk_iso_iff (Arrow.isoMk (iso.app _) e)).1 (R.map

Depends on / 依赖: Arrow.isoMk, Classical, Classical.arbitrary, EssSurj, Functor, Functor.EssSurj.mem_essImage, L.functor.obj, LeftResolution, R.functor, R.functor.map, R.map, T.LeftResolution, arbitrary, arrow_mk_iso_iff, e.hom, functor, iso.app, iso.inv.app, mem_essImage
-/
lemma hasLeftResolutions_of_iso_of_essSurj
    [R.functor.EssSurj] [W₂'.RespectsIso]
    (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor) [T.HasLeftResolutions] :
    B.HasLeftResolutions := by
  intro Y₂
  obtain ⟨X₂, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := R.functor) Y₂
  let ρ : T.LeftResolution X₂ := Classical.arbitrary _
  exact ⟨{
    X₁ := L.functor.obj ρ.X₁
    w := iso.inv.app _ ≫ R.functor.map ρ.w ≫ e.hom
    hw := (W₂'.arrow_mk_iso_iff (Arrow.isoMk (iso.app _) e)).1 (R.map _ ρ.hw) }⟩

set_option backward.isDefEq.respectTransparency false in
/--
lemma `hasRightResolutions_of_iso_of_essSurj_of_full` / 引理 `hasRightResolutions_of_iso_of_essSurj_of_full`

English:
lemma hasRightResolutions_of_iso_of_essSurj_of_full
  proof: by
  intro X₂
  let ρ : B.RightResolution (R.functor.obj X₂) := Classical.arbitrary _
  obtain ⟨X₁, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage L.functor ρ.X₁
  exact ⟨{
    X₁ := X₁
    w := R.functor.preimage (ρ.w ≫ B.functor.map e.inv ≫ iso.inv.app X₁)
    hw := by
      simp only [← R.inverseImage_eq, 

中文:
引理 hasRightResolutions_of_iso_of_essSurj_of_full
  证明: by
  intro X₂
  let ρ : B.RightResolution (R.functor.obj X₂) := Classical.arbitrary _
  obtain ⟨X₁, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage L.functor ρ.X₁
  exact ⟨{
    X₁ := X₁
    w := R.functor.preimage (ρ.w ≫ B.functor.map e.inv ≫ iso.inv.app X₁)
    hw := by
      simp only [← R.inverseImage_eq, 

Depends on / 依赖: Arrow.isoMk, B.RightResolution, B.functor.map, B.functor.mapIso, Classical, Classical.arbitrary, EssSurj, Functor, Functor.EssSurj.mem_essImage, Functor.map_preimage, Iso.refl, L.functor, MorphismProperty, MorphismProperty.inverseImage_iff, R.functor.obj, R.functor.preimage, R.inverseImage_eq, RightResolution, arbitrary, arrow_mk_iso_iff
-/
lemma hasRightResolutions_of_iso_of_essSurj_of_full
    [L.functor.EssSurj] [R.functor.Full] [R.IsInduced] [W₂'.RespectsIso]
    (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor) [B.HasRightResolutions] :
    T.HasRightResolutions := by
  intro X₂
  let ρ : B.RightResolution (R.functor.obj X₂) := Classical.arbitrary _
  obtain ⟨X₁, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage L.functor ρ.X₁
  exact ⟨{
    X₁ := X₁
    w := R.functor.preimage (ρ.w ≫ B.functor.map e.inv ≫ iso.inv.app X₁)
    hw := by
      simp only [← R.inverseImage_eq, MorphismProperty.inverseImage_iff, Functor.map_preimage]
      refine (W₂'.arrow_mk_iso_iff ?_).2 ρ.hw
      exact Arrow.isoMk (Iso.refl _) (iso.app _ ≪≫ B.functor.mapIso e)}⟩

set_option backward.defeqAttrib.useBackward true in
/--
lemma `hasLeftResolutions_of_iso_of_essSurj_of_full` / 引理 `hasLeftResolutions_of_iso_of_essSurj_of_full`

English:
lemma hasLeftResolutions_of_iso_of_essSurj_of_full
  proof: by
  intro X₂
  let ρ : B.LeftResolution (R.functor.obj X₂) := Classical.arbitrary _
  obtain ⟨X₁, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage L.functor ρ.X₁
  exact ⟨{
    X₁ := X₁
    w := R.functor.preimage (iso.hom.app X₁ ≫ B.functor.map e.hom ≫ ρ.w)
    hw := by
      simp only [← R.inverseImage_eq, M

中文:
引理 hasLeftResolutions_of_iso_of_essSurj_of_full
  证明: by
  intro X₂
  let ρ : B.LeftResolution (R.functor.obj X₂) := Classical.arbitrary _
  obtain ⟨X₁, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage L.functor ρ.X₁
  exact ⟨{
    X₁ := X₁
    w := R.functor.preimage (iso.hom.app X₁ ≫ B.functor.map e.hom ≫ ρ.w)
    hw := by
      simp only [← R.inverseImage_eq, M

Depends on / 依赖: Arrow.isoMk, B.LeftResolution, B.functor.map, B.functor.mapIso, Classical, Classical.arbitrary, EssSurj, Functor, Functor.EssSurj.mem_essImage, Functor.map_comp, Functor.map_preimage, Iso.refl, L.functor, LeftResolution, MorphismProperty, MorphismProperty.inverseImage_iff, Opposite, Opposite.op, Quiver, Quiver.Hom.op_inj
-/
lemma hasLeftResolutions_of_iso_of_essSurj_of_full
    [L.functor.EssSurj] [R.functor.Full] [R.IsInduced] [W₂'.RespectsIso]
    (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor) [B.HasLeftResolutions] :
    T.HasLeftResolutions := by
  intro X₂
  let ρ : B.LeftResolution (R.functor.obj X₂) := Classical.arbitrary _
  obtain ⟨X₁, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage L.functor ρ.X₁
  exact ⟨{
    X₁ := X₁
    w := R.functor.preimage (iso.hom.app X₁ ≫ B.functor.map e.hom ≫ ρ.w)
    hw := by
      simp only [← R.inverseImage_eq, MorphismProperty.inverseImage_iff, Functor.map_preimage]
      refine (W₂'.arrow_mk_iso_iff ?_).2 ρ.hw
      exact Arrow.isoMk (iso.app _ ≪≫ B.functor.mapIso e) (Iso.refl _) }⟩

/--
lemma `hasRightResolutions_iff_iso_of_essSurj_of_full` / 引理 `hasRightResolutions_iff_iso_of_essSurj_of_full`

English:
lemma hasRightResolutions_iff_iso_of_essSurj_of_full
  proof: ⟨fun _ => hasRightResolutions_of_iso_of_essSurj iso,
    fun _ => hasRightResolutions_of_iso_of_essSurj_of_full iso⟩

中文:
引理 hasRightResolutions_iff_iso_of_essSurj_of_full
  证明: ⟨fun _ => hasRightResolutions_of_iso_of_essSurj iso,
    fun _ => hasRightResolutions_of_iso_of_essSurj_of_full iso⟩

Depends on / 依赖: Quiver, Quiver.Hom.op_inj, _symm_apply, hasRightResolutions_of_iso_of_essSurj, hasRightResolutions_of_iso_of_essSurj_of_full, opEquiv, opEquiv_symm_apply, op_inj
-/
lemma hasRightResolutions_iff_iso_of_essSurj_of_full
    [R.functor.EssSurj] [R.functor.Full] [R.IsInduced] [L.functor.EssSurj] [W₂'.RespectsIso]
    (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor) :
    T.HasRightResolutions ↔ B.HasRightResolutions :=
  ⟨fun _ => hasRightResolutions_of_iso_of_essSurj iso,
    fun _ => hasRightResolutions_of_iso_of_essSurj_of_full iso⟩

/--
lemma `hasLeftResolutions_iff_iso_of_essSurj_of_full` / 引理 `hasLeftResolutions_iff_iso_of_essSurj_of_full`

English:
lemma hasLeftResolutions_iff_iso_of_essSurj_of_full
  proof: ⟨fun _ => hasLeftResolutions_of_iso_of_essSurj iso,
    fun _ => hasLeftResolutions_of_iso_of_essSurj_of_full iso⟩

中文:
引理 hasLeftResolutions_iff_iso_of_essSurj_of_full
  证明: ⟨fun _ => hasLeftResolutions_of_iso_of_essSurj iso,
    fun _ => hasLeftResolutions_of_iso_of_essSurj_of_full iso⟩

Depends on / 依赖: _add_zero, _symm_apply, hasLeftResolutions_of_iso_of_essSurj, hasLeftResolutions_of_iso_of_essSurj_of_full, opEquiv, opEquiv_symm_apply, opShiftFunctorEquivalence_zero_unitIso_inv_app, shiftFunctorAdd
-/
lemma hasLeftResolutions_iff_iso_of_essSurj_of_full
    [R.functor.EssSurj] [R.functor.Full] [R.IsInduced] [L.functor.EssSurj] [W₂'.RespectsIso]
    (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor) :
    T.HasLeftResolutions ↔ B.HasLeftResolutions :=
  ⟨fun _ => hasLeftResolutions_of_iso_of_essSurj iso,
    fun _ => hasLeftResolutions_of_iso_of_essSurj_of_full iso⟩

/--
lemma `hasRightResolutions_arrow_of_essSurj_of_full` / 引理 `hasRightResolutions_arrow_of_essSurj_of_full`

English:
lemma hasRightResolutions_arrow_of_essSurj_of_full
  proof: by
  let : CatCommSq T.functor L.functor R.functor B.functor := ⟨iso⟩
  exact hasRightResolutions_of_iso_of_essSurj
    (CatCommSq.iso T.arrow.functor L.arrow.functor R.arrow.functor B.arrow.functor)

中文:
引理 hasRightResolutions_arrow_of_essSurj_of_full
  证明: by
  let : CatCommSq T.functor L.functor R.functor B.functor := ⟨iso⟩
  exact hasRightResolutions_of_iso_of_essSurj
    (CatCommSq.iso T.arrow.functor L.arrow.functor R.arrow.functor B.arrow.functor)

Depends on / 依赖: B.arrow.functor, B.functor, CatCommSq, CatCommSq.iso, Functor, Functor.map_comp, L.arrow.functor, L.functor, NatTrans, NatTrans.naturality_assoc, R.arrow.functor, R.functor, T.arrow.functor, T.functor, _assoc_inv_app, _eq_shiftFunctorAdd, _symm_apply, add_comm, functor, hasRightResolutions_of_iso_of_essSurj
-/
lemma hasRightResolutions_arrow_of_essSurj_of_full
    [R.functor.EssSurj] [R.functor.Full] [W₂'.RespectsIso]
    (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor) [T.arrow.HasRightResolutions] :
    B.arrow.HasRightResolutions := by
  let : CatCommSq T.functor L.functor R.functor B.functor := ⟨iso⟩
  exact hasRightResolutions_of_iso_of_essSurj
    (CatCommSq.iso T.arrow.functor L.arrow.functor R.arrow.functor B.arrow.functor)

/--
lemma `hasLeftResolutions_arrow_of_essSurj_of_full` / 引理 `hasLeftResolutions_arrow_of_essSurj_of_full`

English:
lemma hasLeftResolutions_arrow_of_essSurj_of_full
  proof: by
  let : CatCommSq T.functor L.functor R.functor B.functor := ⟨iso⟩
  exact hasLeftResolutions_of_iso_of_essSurj
    (CatCommSq.iso T.arrow.functor L.arrow.functor R.arrow.functor B.arrow.functor)

中文:
引理 hasLeftResolutions_arrow_of_essSurj_of_full
  证明: by
  let : CatCommSq T.functor L.functor R.functor B.functor := ⟨iso⟩
  exact hasLeftResolutions_of_iso_of_essSurj
    (CatCommSq.iso T.arrow.functor L.arrow.functor R.arrow.functor B.arrow.functor)

Depends on / 依赖: B.arrow.functor, B.functor, CatCommSq, CatCommSq.iso, L.arrow.functor, L.functor, R.arrow.functor, R.functor, T.arrow.functor, T.functor, functor, hasLeftResolutions_of_iso_of_essSurj
-/
lemma hasLeftResolutions_arrow_of_essSurj_of_full
    [R.functor.EssSurj] [R.functor.Full] [W₂'.RespectsIso]
    (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor) [T.arrow.HasLeftResolutions] :
    B.arrow.HasLeftResolutions := by
  let : CatCommSq T.functor L.functor R.functor B.functor := ⟨iso⟩
  exact hasLeftResolutions_of_iso_of_essSurj
    (CatCommSq.iso T.arrow.functor L.arrow.functor R.arrow.functor B.arrow.functor)

/--
lemma `hasRightResolutions_arrow_iff_of_equivalences` / 引理 `hasRightResolutions_arrow_iff_of_equivalences`

English:
lemma hasRightResolutions_arrow_iff_of_equivalences
  proof: by
  let : CatCommSq T.functor L.functor R.functor B.functor := ⟨iso⟩
  exact hasRightResolutions_iff_iso_of_essSurj_of_full
    (CatCommSq.iso T.arrow.functor L.arrow.functor R.arrow.functor B.arrow.functor)

中文:
引理 hasRightResolutions_arrow_iff_of_equivalences
  证明: by
  let : CatCommSq T.functor L.functor R.functor B.functor := ⟨iso⟩
  exact hasRightResolutions_iff_iso_of_essSurj_of_full
    (CatCommSq.iso T.arrow.functor L.arrow.functor R.arrow.functor B.arrow.functor)

Depends on / 依赖: B.arrow.functor, B.functor, CatCommSq, CatCommSq.iso, L.arrow.functor, L.functor, Preadditive, Preadditive.add_comp, R.arrow.functor, R.functor, T.arrow.functor, T.functor, add_comp, functor, hasRightResolutions_iff_iso_of_essSurj_of_full, opEquiv, opEquiv_symm_add
-/
lemma hasRightResolutions_arrow_iff_of_equivalences
    [R.functor.IsEquivalence] [R.IsInduced] [L.functor.IsEquivalence] [W₂'.RespectsIso]
    (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor) :
    T.arrow.HasRightResolutions ↔ B.arrow.HasRightResolutions := by
  let : CatCommSq T.functor L.functor R.functor B.functor := ⟨iso⟩
  exact hasRightResolutions_iff_iso_of_essSurj_of_full
    (CatCommSq.iso T.arrow.functor L.arrow.functor R.arrow.functor B.arrow.functor)

/--
lemma `hasLeftResolutions_arrow_iff_of_equivalences` / 引理 `hasLeftResolutions_arrow_iff_of_equivalences`

English:
lemma hasLeftResolutions_arrow_iff_of_equivalences
  proof: by
  let : CatCommSq T.functor L.functor R.functor B.functor := ⟨iso⟩
  exact hasLeftResolutions_iff_iso_of_essSurj_of_full
    (CatCommSq.iso T.arrow.functor L.arrow.functor R.arrow.functor B.arrow.functor)

中文:
引理 hasLeftResolutions_arrow_iff_of_equivalences
  证明: by
  let : CatCommSq T.functor L.functor R.functor B.functor := ⟨iso⟩
  exact hasLeftResolutions_iff_iso_of_essSurj_of_full
    (CatCommSq.iso T.arrow.functor L.arrow.functor R.arrow.functor B.arrow.functor)

Depends on / 依赖: B.arrow.functor, B.functor, CatCommSq, CatCommSq.iso, L.arrow.functor, L.functor, R.arrow.functor, R.functor, T.arrow.functor, T.functor, functor, hasLeftResolutions_iff_iso_of_essSurj_of_full
-/
lemma hasLeftResolutions_arrow_iff_of_equivalences
    [R.functor.IsEquivalence] [R.IsInduced] [L.functor.IsEquivalence] [W₂'.RespectsIso]
    (iso : T.functor ⋙ R.functor ≅ L.functor ⋙ B.functor) :
    T.arrow.HasLeftResolutions ↔ B.arrow.HasLeftResolutions := by
  let : CatCommSq T.functor L.functor R.functor B.functor := ⟨iso⟩
  exact hasLeftResolutions_iff_iso_of_essSurj_of_full
    (CatCommSq.iso T.arrow.functor L.arrow.functor R.arrow.functor B.arrow.functor)

end

end LocalizerMorphism

end CategoryTheory
