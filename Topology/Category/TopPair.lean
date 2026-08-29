/-
Copyright (c) 2026 Jakob Scharmberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Scharmberg
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.Topology.Homotopy.TopCat.Basic

/-!
# Topological Pairs

In this file we introduce `TopPair`, the category of topological pairs. It is defined as the
category of arrows in `TopCat` which are topological embeddings.

We provide the inclusion and diagonal functors `TopCat ⥤ TopPair` and show that they are left and
right adjoint to the first projection functor, respectively.

We also define for two morphisms of topological pairs `f, g : X ⟶ Y` the structure `Homotopy f g` of
homotopies between them.
-/

@[expose] public section

universe u

open TopologicalSpace TopCat CategoryTheory MonoidalCategory

/--
Definition of `TopPair` / `TopPair` 的定义

English:
abbreviation TopPair
  body: MorphismProperty.Arrow TopCat.isEmbedding ⊤ ⊤

中文:
缩写 TopPair
  定义体: MorphismProperty.Arrow TopCat.isEmbedding ⊤ ⊤

Depends on / 依赖: MorphismProperty, MorphismProperty.Arrow, TopCat, TopCat.isEmbedding, isEmbedding
-/
abbrev TopPair :=
  MorphismProperty.Arrow TopCat.isEmbedding ⊤ ⊤

namespace TopPair

variable {X Y : TopPair.{u}}

/--
Definition of `fst` / `fst` 的定义

English:
abbreviation fst
  signature: : TopCat.{u}
  body: X.right

中文:
缩写 fst
  签名: : 顶元素范畴.{u}
  定义体: X.right

Depends on / 依赖: X.right
-/
abbrev fst : TopCat.{u} := X.right

/--
Definition of `snd` / `snd` 的定义

English:
abbreviation snd
  signature: : TopCat.{u}
  body: X.left

中文:
缩写 snd
  签名: : 顶元素范畴.{u}
  定义体: X.left

Depends on / 依赖: X.left
-/
abbrev snd : TopCat.{u} := X.left

/--
Definition of `map` / `map` 的定义

English:
abbreviation map
  signature: : X.snd ⟶ X.fst
  body: X.hom

中文:
缩写 map
  签名: : X.snd ⟶ X.fst
  定义体: X.hom

Depends on / 依赖: X.hom
-/
abbrev map : X.snd ⟶ X.fst := X.hom

/--
lemma `isEmbedding_map` / 引理 `isEmbedding_map`

English:
lemma isEmbedding_map
  given: (X : TopPair.{u})
  statement: Topology.IsEmbedding X.map
  proof: X.prop

中文:
引理 isEmbedding_map
  条件: (X : TopPair.{u})
  结论: 拓扑.是嵌入 X.map
  证明: X.prop

Depends on / 依赖: X.prop
-/
lemma isEmbedding_map (X : TopPair.{u}) : Topology.IsEmbedding X.map := X.prop

/--
Definition of `of` / `of` 的定义

English:
abbreviation of
  signature: {A X : TopCat.{u}} (f : A ⟶ X) (h : Topology.IsEmbedding f)
  body: MorphismProperty.Arrow.mk (P := TopCat.isEmbedding) f h

中文:
缩写 of
  签名: {A X : 顶元素范畴.{u}} (f : A ⟶ X) (h : 拓扑.是嵌入 f)
  定义体: MorphismProperty.Arrow.mk (P := TopCat.isEmbedding) f h

Depends on / 依赖: MorphismProperty, MorphismProperty.Arrow.mk, TopCat, TopCat.isEmbedding, isEmbedding
-/
abbrev of {A X : TopCat.{u}} (f : A ⟶ X) (h : Topology.IsEmbedding f) : TopPair.{u} :=
  MorphismProperty.Arrow.mk (P := TopCat.isEmbedding) f h

/--
Definition of `ofSubset` / `ofSubset` 的定义

English:
abbreviation ofSubset
  signature: {X : TopCat.{u}} (A : Set X)
  body: TopPair.of (A := (TopCat.of A))
  (X := X) (TopCat.ofHom { toFun := Subtype.val }) Topology.IsEmbedding.subtypeVal

中文:
缩写 ofSubset
  签名: {X : 顶元素范畴.{u}} (A : 集合 X)
  定义体: TopPair.of (A := (TopCat.of A))
  (X := X) (TopCat.ofHom { toFun := Subtype.val }) Topology.IsEmbedding.subtypeVal

Depends on / 依赖: TopCat, TopCat.of, TopPair, TopPair.of
-/
abbrev ofSubset {X : TopCat.{u}} (A : Set X) : TopPair.{u} := TopPair.of (A := (TopCat.of A))
  (X := X) (TopCat.ofHom { toFun := Subtype.val }) Topology.IsEmbedding.subtypeVal

/--
Definition of `ofTopCat` / `ofTopCat` 的定义

English:
abbreviation ofTopCat
  signature: (X : TopCat.{u})
  body: TopPair.of (TopCat.isInitialPEmpty.to X) (Topology.IsOpenEmbedding.of_isEmpty _).1

中文:
缩写 ofTopCat
  签名: (X : 顶元素范畴.{u})
  定义体: TopPair.of (TopCat.isInitialPEmpty.to X) (Topology.IsOpenEmbedding.of_isEmpty _).1

Depends on / 依赖: IsOpenEmbedding, TopCat, TopCat.isInitialPEmpty.to, TopPair, TopPair.of, Topology, Topology.IsOpenEmbedding.of_isEmpty, isInitialPEmpty, of_isEmpty
-/
abbrev ofTopCat (X : TopCat.{u}) : TopPair.{u} :=
  TopPair.of (TopCat.isInitialPEmpty.to X) (Topology.IsOpenEmbedding.of_isEmpty _).1

/--
Definition of `ofHom` / `ofHom` 的定义

English:
abbreviation ofHom
  signature: (f : X.fst ⟶ Y.fst) (g : X.snd ⟶ Y.snd) (w : g ≫ Y.map = X.map ≫ f := by cat_disch)
  body: MorphismProperty.Arrow.homMk g f w

中文:
缩写 ofHom
  签名: (f : X.fst ⟶ Y.fst) (g : X.snd ⟶ Y.snd) (w : g ≫ Y.map = X.map ≫ f := by cat_disch)
  定义体: MorphismProperty.Arrow.homMk g f w

Depends on / 依赖: MorphismProperty, MorphismProperty.Arrow.homMk, cat_disch
-/
abbrev ofHom (f : X.fst ⟶ Y.fst) (g : X.snd ⟶ Y.snd) (w : g ≫ Y.map = X.map ≫ f := by cat_disch) :=
  MorphismProperty.Arrow.homMk g f w

variable {X Y Z : TopPair.{u}}

/--
Definition of `Hom.fst` / `Hom.fst` 的定义

English:
abbreviation Hom.fst
  signature: (f : X ⟶ Y)
  body: f.hom.right

中文:
缩写 态射.fst
  签名: (f : X ⟶ Y)
  定义体: f.hom.right
-/
abbrev Hom.fst (f : X ⟶ Y) : X.fst ⟶ Y.fst := f.hom.right

/--
Definition of `Hom.snd` / `Hom.snd` 的定义

English:
abbreviation Hom.snd
  signature: (f : X ⟶ Y)
  body: f.hom.left

@[reassoc, elementwise]

中文:
缩写 态射.snd
  签名: (f : X ⟶ Y)
  定义体: f.hom.left

@[reassoc, elementwise]
-/
abbrev Hom.snd (f : X ⟶ Y) : X.snd ⟶ Y.snd := f.hom.left

@[reassoc, elementwise]
/--
lemma `Hom.w` / 引理 `Hom.w`

English:
lemma Hom.w
  given: {X Y : TopPair.{u}} (f : X ⟶ Y)
  proof: f.hom.w

中文:
引理 态射.w
  条件: {X Y : TopPair.{u}} (f : X ⟶ Y)
  证明: f.hom.w
-/
lemma Hom.w {X Y : TopPair.{u}} (f : X ⟶ Y) :
    Hom.snd f ≫ Y.map = X.map ≫ Hom.fst f :=
  f.hom.w

attribute [local simp] Hom.w_apply

/--
Definition of `proj₁` / `proj₁` 的定义

English:
abbreviation proj₁
  signature: : TopPair.{u} ⥤ TopCat.{u}
  body: MorphismProperty.Arrow.forget _ _ _ ⋙ CategoryTheory.Arrow.rightFunc

中文:
缩写 proj₁
  签名: : TopPair.{u} ⥤ 顶元素范畴.{u}
  定义体: MorphismProperty.Arrow.forget _ _ _ ⋙ CategoryTheory.Arrow.rightFunc

Depends on / 依赖: CategoryTheory, CategoryTheory.Arrow.rightFunc, MorphismProperty, MorphismProperty.Arrow.forget, forget, rightFunc
-/
abbrev proj₁ : TopPair.{u} ⥤ TopCat.{u} :=
  MorphismProperty.Arrow.forget _ _ _ ⋙ CategoryTheory.Arrow.rightFunc

/--
Definition of `proj₂` / `proj₂` 的定义

English:
abbreviation proj₂
  signature: : TopPair.{u} ⥤ TopCat.{u}
  body: MorphismProperty.Arrow.forget _ _ _ ⋙ CategoryTheory.Arrow.leftFunc

中文:
缩写 proj₂
  签名: : TopPair.{u} ⥤ 顶元素范畴.{u}
  定义体: MorphismProperty.Arrow.forget _ _ _ ⋙ CategoryTheory.Arrow.leftFunc

Depends on / 依赖: CategoryTheory, CategoryTheory.Arrow.leftFunc, MorphismProperty, MorphismProperty.Arrow.forget, forget, leftFunc
-/
abbrev proj₂ : TopPair.{u} ⥤ TopCat.{u} :=
  MorphismProperty.Arrow.forget _ _ _ ⋙ CategoryTheory.Arrow.leftFunc

/-- The inclusion functor from topological spaces to topological pairs that sends a space X to
(X, ∅). -/
@[simps]
/--
Definition of `incl` / `incl` 的定义

English:
definition incl
  signature: : TopCat.{u} ⥤ TopPair.{u} where
  body: ofTopCat X
map f := TopPair.ofHom f (𝟙 _) by ext x; induction x

中文:
定义 incl
  签名: : 顶元素范畴.{u} ⥤ TopPair.{u} where
  定义体: ofTopCat X
map f := TopPair.ofHom f (𝟙 _) by ext x; induction x

Depends on / 依赖: ofTopCat
-/
def incl : TopCat.{u} ⥤ TopPair.{u} where
  obj X := ofTopCat X
map f := TopPair.ofHom f (𝟙 _) by ext x; induction x

/--
Definition of `diag` / `diag` 的定义

English:
abbreviation diag
  signature: : TopCat.{u} ⥤ TopPair.{u} where
  body: TopPair.of (𝟙 X) Topology.IsEmbedding.id
  map f := TopPair.ofHom f f

中文:
缩写 diag
  签名: : 顶元素范畴.{u} ⥤ TopPair.{u} where
  定义体: TopPair.of (𝟙 X) Topology.IsEmbedding.id
  map f := TopPair.ofHom f f

Depends on / 依赖: IsEmbedding, TopPair, TopPair.of, Topology, Topology.IsEmbedding.id
-/
abbrev diag : TopCat.{u} ⥤ TopPair.{u} where
  obj X := TopPair.of (𝟙 X) Topology.IsEmbedding.id
  map f := TopPair.ofHom f f

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The inclusion functor is left adjoint to the projection to the first component. -/
@[simps]
/--
Definition of `inclAdjProj₁` / `inclAdjProj₁` 的定义

English:
definition inclAdjProj₁
  signature: : incl ⊣ proj₁ where
  body: 𝟙 X
  counit.app X := TopPair.ofHom (𝟙 X.fst) (TopCat.isInitialPEmpty.to X.snd)

中文:
定义 inclAdjProj₁
  签名: : incl ⊣ proj₁ where
  定义体: 𝟙 X
  counit.app X := TopPair.ofHom (𝟙 X.fst) (TopCat.isInitialPEmpty.to X.snd)
-/
def inclAdjProj₁ : incl ⊣ proj₁ where
  unit.app X := 𝟙 X
  counit.app X := TopPair.ofHom (𝟙 X.fst) (TopCat.isInitialPEmpty.to X.snd)

/-- The projection functor to the first component is left adjoint to the diagonal functor. -/
@[simps]
/--
Definition of `proj₁AdjDiag` / `proj₁AdjDiag` 的定义

English:
definition proj₁AdjDiag
  signature: : proj₁ ⊣ diag where
  body: TopPair.ofHom (𝟙 X.fst) X.map
  unit.naturality X Y f := MorphismProperty.Arrow.Hom.ext f.w (by cat_disch)
  counit.app X := 𝟙 X

中文:
定义 proj₁AdjDiag
  签名: : proj₁ ⊣ diag where
  定义体: TopPair.ofHom (𝟙 X.fst) X.map
  unit.naturality X Y f := MorphismProperty.Arrow.Hom.ext f.w (by cat_disch)
  counit.app X := 𝟙 X

Depends on / 依赖: TopPair, TopPair.ofHom, X.fst, X.map
-/
def proj₁AdjDiag : proj₁ ⊣ diag where
  unit.app X := TopPair.ofHom (𝟙 X.fst) X.map
  unit.naturality X Y f := MorphismProperty.Arrow.Hom.ext f.w (by cat_disch)
  counit.app X := 𝟙 X

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `j` / `j` 的定义

English:
abbreviation j
  signature: (X : TopPair.{u})
  body: TopPair.ofHom (𝟙 _) (TopCat.isInitialPEmpty.to _)

中文:
缩写 j
  签名: (X : TopPair.{u})
  定义体: TopPair.ofHom (𝟙 _) (TopCat.isInitialPEmpty.to _)

Depends on / 依赖: TopCat, TopCat.isInitialPEmpty.to, TopPair, TopPair.ofHom, isInitialPEmpty
-/
abbrev j (X : TopPair.{u}) : TopPair.incl.obj X.fst ⟶ X :=
  TopPair.ofHom (𝟙 _) (TopCat.isInitialPEmpty.to _)

/-- A homotopy of maps between topological pairs is a homotopy on the first space and a homotopy on
the second space that fit in a commutative square with the maps of the pairs. -/
@[ext]
/--
Definition of `Homotopy` / `Homotopy` 的定义

English:
structure Homotopy
  parameters: (f g : X ⟶ Y)
  axioms and operations (3):
    - fst : TopCat.Homotopy (Hom.fst f) (Hom.fst g)
    - snd : TopCat.Homotopy (Hom.snd f) (Hom.snd g)
    - w : X.map ▷ _ ≫ fst.h = snd.h ≫ Y.map  [default: by cat_disch]

中文:
结构 同伦
  参数: (f g : X ⟶ Y)
  公理与运算 (3 个):
    - fst : 顶元素范畴.同伦 (态射.fst f) (态射.fst g)
    - snd : 顶元素范畴.同伦 (态射.snd f) (态射.snd g)
    - w : X.map ▷ _ ≫ fst.h = snd.h ≫ Y.map  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure Homotopy (f g : X ⟶ Y) where
  /-- The homotopy on the first space. -/
  fst : TopCat.Homotopy (Hom.fst f) (Hom.fst g)
  /-- The homotopy on the second space. -/
  snd : TopCat.Homotopy (Hom.snd f) (Hom.snd g)
  /-- The proof that the homotopies fit into a commutative square with the maps of the pairs. -/
  w : X.map ▷ _ ≫ fst.h = snd.h ≫ Y.map := by cat_disch

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
attribute [reassoc, elementwise] Homotopy.w
attribute [local simp] Homotopy.w Homotopy.w_apply

namespace Homotopy

@[local simp]
/--
lemma `w_apply'` / 引理 `w_apply'`

English:
lemma w_apply'
  given: {f g : X ⟶ Y} (H : Homotopy f g) (x : TopPair.snd) (t : unitInterval)
  proof: by
  have := w_apply H (x, I.homeomorph.symm t)
  cat_disch

中文:
引理 w_apply'
  条件: {f g : X ⟶ Y} (H : 同伦 f g) (x : TopPair.snd) (t : unit整数erval)
  证明: by
  have := w_apply H (x, I.homeomorph.symm t)
  cat_disch

Depends on / 依赖: I.homeomorph.symm, cat_disch, homeomorph, w_apply
-/
lemma w_apply' {f g : X ⟶ Y} (H : Homotopy f g) (x : TopPair.snd) (t : unitInterval) :
    H.fst (t, X.map x) = Y.map (H.snd (t, x)) := by
  have := w_apply H (x, I.homeomorph.symm t)
  cat_disch

/-- Given a morphism `f` of topological pairs, we can define a `Homotopy f f` by
`TopCat.Homotopy.refl` on the first and second components.
-/
@[simps]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: (f : X ⟶ Y)
  body: TopCat.Homotopy.refl (Hom.fst f)
  snd := TopCat.Homotopy.refl (Hom.snd f)

中文:
定义 refl
  签名: (f : X ⟶ Y)
  定义体: TopCat.Homotopy.refl (Hom.fst f)
  snd := TopCat.Homotopy.refl (Hom.snd f)

Depends on / 依赖: Hom.fst, Homotopy, TopCat, TopCat.Homotopy.refl
-/
def refl (f : X ⟶ Y) : Homotopy f f where
  fst := TopCat.Homotopy.refl (Hom.fst f)
  snd := TopCat.Homotopy.refl (Hom.snd f)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Homotopy (𝟙 X) (𝟙 X))
  body: ⟨Homotopy.refl _⟩

中文:
实例 :
  签名: 可居 (同伦 (𝟙 X) (𝟙 X))
  定义体: ⟨Homotopy.refl _⟩

Depends on / 依赖: Homotopy, Homotopy.refl
-/
instance : Inhabited (Homotopy (𝟙 X) (𝟙 X)) :=
  ⟨Homotopy.refl _⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- Given a `Homotopy f₀ f₁`, we can define a `Homotopy f₁ f₀` by `TopCat.Homotopy.symm` on
the first and second components.
-/
@[simps]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: {f₀ f₁ : X ⟶ Y} (F : Homotopy f₀ f₁)
  body: F.fst.symm
  snd := F.snd.symm

@[simp]

中文:
定义 symm
  签名: {f₀ f₁ : X ⟶ Y} (F : 同伦 f₀ f₁)
  定义体: F.fst.symm
  snd := F.snd.symm

@[simp]

Depends on / 依赖: F.fst.symm
-/
def symm {f₀ f₁ : X ⟶ Y} (F : Homotopy f₀ f₁) : Homotopy f₁ f₀ where
  fst := F.fst.symm
  snd := F.snd.symm

@[simp]
/--
theorem `symm_symm` / 定理 `symm_symm`

English:
theorem symm_symm
  given: {f₀ f₁ : X ⟶ Y} (F : Homotopy f₀ f₁)
  statement: F.symm.symm = F
  proof: by
  cat_disch

中文:
定理 symm_symm
  条件: {f₀ f₁ : X ⟶ Y} (F : 同伦 f₀ f₁)
  结论: F.symm.symm = F
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
theorem symm_symm {f₀ f₁ : X ⟶ Y} (F : Homotopy f₀ f₁) : F.symm.symm = F := by
  cat_disch

/--
theorem `symm_bijective` / 定理 `symm_bijective`

English:
theorem symm_bijective
  given: {f₀ f₁ : X ⟶ Y}
  proof: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

中文:
定理 symm_bijective
  条件: {f₀ f₁ : X ⟶ Y}
  证明: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

Depends on / 依赖: Function, Function.bijective_iff_has_inverse.mpr, bijective_iff_has_inverse, symm_symm
-/
theorem symm_bijective {f₀ f₁ : X ⟶ Y} :
    Function.Bijective (Homotopy.symm : Homotopy f₀ f₁ -> Homotopy f₁ f₀) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
Given `Homotopy f₀ f₁` and `Homotopy f₁ f₂`, we can define a `Homotopy f₀ f₂` by
`TopCat.Homotopy.trans` on the first and second components.
-/
@[simps]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: {f₀ f₁ f₂ : X ⟶ Y} (F : Homotopy f₀ f₁) (G : Homotopy f₁ f₂)
  body: F.fst.trans G.fst
  snd := F.snd.trans G.snd
  w := by
    ext ⟨_, _⟩
    simp only [TopCat.comp_app, Homotopy.h_hom_apply, ContinuousMap.Homotopy.trans_apply]
    cat_disch

中文:
定义 trans
  签名: {f₀ f₁ f₂ : X ⟶ Y} (F : 同伦 f₀ f₁) (G : 同伦 f₁ f₂)
  定义体: F.fst.trans G.fst
  snd := F.snd.trans G.snd
  w := by
    ext ⟨_, _⟩
    simp only [TopCat.comp_app, Homotopy.h_hom_apply, ContinuousMap.Homotopy.trans_apply]
    cat_disch

Depends on / 依赖: F.fst.trans, G.fst
-/
noncomputable def trans {f₀ f₁ f₂ : X ⟶ Y} (F : Homotopy f₀ f₁) (G : Homotopy f₁ f₂) :
    Homotopy f₀ f₂ where
  fst := F.fst.trans G.fst
  snd := F.snd.trans G.snd
  w := by
    ext ⟨_, _⟩
    simp only [TopCat.comp_app, Homotopy.h_hom_apply, ContinuousMap.Homotopy.trans_apply]
    cat_disch

/--
theorem `symm_trans` / 定理 `symm_trans`

English:
theorem symm_trans
  given: {f₀ f₁ f₂ : X ⟶ Y} (F : Homotopy f₀ f₁) (G : Homotopy f₁ f₂)
  proof: by
      ext : 1 <;> exact ContinuousMap.Homotopy.symm_trans _ _

中文:
定理 symm_trans
  条件: {f₀ f₁ f₂ : X ⟶ Y} (F : 同伦 f₀ f₁) (G : 同伦 f₁ f₂)
  证明: by
      ext : 1 <;> exact ContinuousMap.Homotopy.symm_trans _ _

Depends on / 依赖: ContinuousMap, ContinuousMap.Homotopy.symm_trans, Homotopy, symm_trans
-/
theorem symm_trans {f₀ f₁ f₂ : X ⟶ Y} (F : Homotopy f₀ f₁) (G : Homotopy f₁ f₂) :
    (F.trans G).symm = G.symm.trans F.symm := by
      ext : 1 <;> exact ContinuousMap.Homotopy.symm_trans _ _

set_option backward.isDefEq.respectTransparency false in
/-- If we have a `Homotopy g₀ g₁` and a `Homotopy f₀ f₁`, we can define a
`Homotopy (f₀ ≫ g₀) (f₁ ≫ g₁)` by `TopCat.Homotopy.comp` on the first and second components.
-/
@[simps]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: {f₀ f₁ : X ⟶ Y} {g₀ g₁ : Y ⟶ Z} (G : Homotopy g₀ g₁) (F : Homotopy f₀ f₁)
  body: G.fst.comp F.fst
  snd := G.snd.comp F.snd

中文:
定义 comp
  签名: {f₀ f₁ : X ⟶ Y} {g₀ g₁ : Y ⟶ Z} (G : 同伦 g₀ g₁) (F : 同伦 f₀ f₁)
  定义体: G.fst.comp F.fst
  snd := G.snd.comp F.snd

Depends on / 依赖: F.fst, G.fst.comp
-/
def comp {f₀ f₁ : X ⟶ Y} {g₀ g₁ : Y ⟶ Z} (G : Homotopy g₀ g₁) (F : Homotopy f₀ f₁) :
    Homotopy (f₀ ≫ g₀) (f₁ ≫ g₁) where
  fst := G.fst.comp F.fst
  snd := G.snd.comp F.snd

end Homotopy

/--
Definition of `Homotopic` / `Homotopic` 的定义

English:
definition Homotopic
  signature: (f g : X ⟶ Y)
  body: Nonempty (Homotopy f g)

中文:
定义 同伦
  签名: (f g : X ⟶ Y)
  定义体: Nonempty (Homotopy f g)

Depends on / 依赖: Homotopy, Nonempty
-/
def Homotopic (f g : X ⟶ Y) := Nonempty (Homotopy f g)

namespace Homotopic

/--
theorem `equivalence` / 定理 `equivalence`

English:
theorem equivalence
  statement: Equivalence (Homotopic (X := X) (Y := Y))
  proof: ⟨fun f => ⟨Homotopy.refl f⟩, fun h => h.map Homotopy.symm, fun h₀ h₁ => h₀.map2 Homotopy.trans h₁⟩

中文:
定理 equivalence
  结论: 等价 (同伦 (X := X) (Y := Y))
  证明: ⟨fun f => ⟨Homotopy.refl f⟩, fun h => h.map Homotopy.symm, fun h₀ h₁ => h₀.map2 Homotopy.trans h₁⟩
-/
theorem equivalence : Equivalence (Homotopic (X := X) (Y := Y)) :=
  ⟨fun f => ⟨Homotopy.refl f⟩, fun h => h.map Homotopy.symm, fun h₀ h₁ => h₀.map2 Homotopy.trans h₁⟩

end Homotopic

end TopPair
