/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Shift.CommShift

/-!
# Functors from a category to a category with a shift

Given a category `C`, and a category `D` equipped with a shift by a monoid `A`,
we define a structure `SingleFunctors C D A` which contains the data of
functors `functor a : C ⥤ D` for all `a : A` and isomorphisms
`shiftIso n a a' h : functor a' ⋙ shiftFunctor D n ≅ functor a`
whenever `n + a = a'`. These isomorphisms should satisfy certain compatibilities
with respect to the shift on `D`.

This notion is similar to `Functor.ShiftSequence` which can be used in order to
attach shifted versions of a homological functor `D ⥤ C` with `D` a
triangulated category and `C` an abelian category. However, the definition
`SingleFunctors` is for functors in the other direction: it is meant to
ease the formalization of the compatibilities with shifts of the
functors `C ⥤ CochainComplex C ℤ` (or `C ⥤ DerivedCategory C` (TODO))
which sends an object `X : C` to a complex where `X` sits in a single degree.

-/

@[expose] public section

open CategoryTheory Category ZeroObject Limits Functor

variable (C D E E' : Type*) [Category* C] [Category* D] [Category* E] [Category* E']
  (A : Type*) [AddMonoid A] [HasShift D A] [HasShift E A] [HasShift E' A]

namespace CategoryTheory

/--
Definition of `SingleFunctors` / `SingleFunctors` 的定义

English:
structure SingleFunctors
  parameters: where
  axioms and operations (4):
    - functor((a : A)) : C ⥤ D
    - shiftIso((n a a' : A) (ha' : n + a = a')) : functor a' ⋙ shiftFunctor D n ≅ functor a
    - shiftIso_zero((a : A)) : shiftIso 0 a a (zero_add a) = isoWhiskerLeft _ (shiftFunctorZero D A)
    - shiftIso_add((n m a a' a'' : A) (ha' : n + a = a') (ha'' : m + a' = a'')) : shiftIso (m + n) a a'' (by rw [add_assoc, ha', ha'']) = isoWhiskerLeft _ (shiftFunctorAdd D m n) ≪≫ (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (shiftIso m a' a'' ha'') _ ≪≫ shiftIso n a a' ha'

中文:
结构 SingleFunctors
  参数: where
  公理与运算 (4 个):
    - functor((a : A)) : C ⥤ D
    - shiftIso((n a a' : A) (ha' : n + a = a')) : functor a' ⋙ shiftFunctor D n ≅ functor a
    - shiftIso_zero((a : A)) : shiftIso 0 a a (zero_add a) = isoWhiskerLeft _ (shiftFunctorZero D A)
    - shiftIso_add((n m a a' a'' : A) (ha' : n + a = a') (ha'' : m + a' = a'')) : shiftIso (m + n) a a'' (by rw [add_assoc, ha', ha'']) = isoWhiskerLeft _ (shiftFunctorAdd D m n) ≪≫ (函子.associator _ _ _).symm ≪≫ isoWhiskerRight (shiftIso m a' a'' ha'') _ ≪≫ shiftIso n a a' ha'
-/
structure SingleFunctors where
  /-- a family of functors `C ⥤ D` indexed by the elements of the additive monoid `A` -/
  functor (a : A) : C ⥤ D
  /-- the isomorphism `functor a' ⋙ shiftFunctor D n ≅ functor a` when `n + a = a'` -/
  shiftIso (n a a' : A) (ha' : n + a = a') : functor a' ⋙ shiftFunctor D n ≅ functor a
  /-- `shiftIso 0` is the obvious isomorphism. -/
  shiftIso_zero (a : A) :
    shiftIso 0 a a (zero_add a) = isoWhiskerLeft _ (shiftFunctorZero D A)
  /-- `shiftIso (m + n)` is determined by `shiftIso m` and `shiftIso n`. -/
  shiftIso_add (n m a a' a'' : A) (ha' : n + a = a') (ha'' : m + a' = a'') :
    shiftIso (m + n) a a'' (by rw [add_assoc, ha', ha'']) =
      isoWhiskerLeft _ (shiftFunctorAdd D m n) ≪≫ (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (shiftIso m a' a'' ha'') _ ≪≫ shiftIso n a a' ha'

variable {C D E A}
variable (F G H : SingleFunctors C D A)

namespace SingleFunctors

set_option backward.defeqAttrib.useBackward true in
/--
lemma `shiftIso_add_hom_app` / 引理 `shiftIso_add_hom_app`

English:
lemma shiftIso_add_hom_app
  given: (n m a a' a'' : A) (ha' : n + a = a') (ha'' : m + a' = a'') (X : C)
  proof: by
  simp [F.shiftIso_add n m a a' a'' ha' ha'']

中文:
引理 shiftIso_add_hom_app
  条件: (n m a a' a'' : A) (ha' : n + a = a') (ha'' : m + a' = a'') (X : C)
  证明: by
  simp [F.shiftIso_add n m a a' a'' ha' ha'']

Depends on / 依赖: F.shiftIso_add, shiftIso_add
-/
lemma shiftIso_add_hom_app (n m a a' a'' : A) (ha' : n + a = a') (ha'' : m + a' = a'') (X : C) :
    (F.shiftIso (m + n) a a'' (by rw [add_assoc, ha', ha''])).hom.app X =
      (shiftFunctorAdd D m n).hom.app ((F.functor a'').obj X) ≫
        ((F.shiftIso m a' a'' ha'').hom.app X)⟦n⟧' ≫
        (F.shiftIso n a a' ha').hom.app X := by
  simp [F.shiftIso_add n m a a' a'' ha' ha'']

set_option backward.defeqAttrib.useBackward true in
/--
lemma `shiftIso_add_inv_app` / 引理 `shiftIso_add_inv_app`

English:
lemma shiftIso_add_inv_app
  given: (n m a a' a'' : A) (ha' : n + a = a') (ha'' : m + a' = a'') (X : C)
  proof: by
  simp [F.shiftIso_add n m a a' a'' ha' ha'']

中文:
引理 shiftIso_add_inv_app
  条件: (n m a a' a'' : A) (ha' : n + a = a') (ha'' : m + a' = a'') (X : C)
  证明: by
  simp [F.shiftIso_add n m a a' a'' ha' ha'']

Depends on / 依赖: F.shiftIso_add, shiftIso_add
-/
lemma shiftIso_add_inv_app (n m a a' a'' : A) (ha' : n + a = a') (ha'' : m + a' = a'') (X : C) :
    (F.shiftIso (m + n) a a'' (by rw [add_assoc, ha', ha''])).inv.app X =
      (F.shiftIso n a a' ha').inv.app X ≫
      ((F.shiftIso m a' a'' ha'').inv.app X)⟦n⟧' ≫
      (shiftFunctorAdd D m n).inv.app ((F.functor a'').obj X) := by
  simp [F.shiftIso_add n m a a' a'' ha' ha'']

/--
lemma `shiftIso_add'` / 引理 `shiftIso_add'`

English:
lemma shiftIso_add'
  statement: (n m mn : A) (hnm : m + n = mn) (a a' a'' : A)
  proof: by
  subst hnm
  rw [shiftFunctorAdd'_eq_shiftFunctorAdd]; rw [shiftIso_add]

中文:
引理 shiftIso_add'
  结论: (n m mn : A) (hnm : m + n = mn) (a a' a'' : A)
  证明: by
  subst hnm
  rw [shiftFunctorAdd'_eq_shiftFunctorAdd]; rw [shiftIso_add]

Depends on / 依赖: _eq_shiftFunctorAdd, shiftFunctorAdd, shiftIso_add
-/
lemma shiftIso_add' (n m mn : A) (hnm : m + n = mn) (a a' a'' : A)
    (ha' : n + a = a') (ha'' : m + a' = a'') :
    F.shiftIso mn a a'' (by rw [← hnm, ← ha'', ← ha', add_assoc]) =
      isoWhiskerLeft _ (shiftFunctorAdd' D m n mn hnm) ≪≫ (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (F.shiftIso m a' a'' ha'') _ ≪≫ F.shiftIso n a a' ha' := by
  subst hnm
  rw [shiftFunctorAdd'_eq_shiftFunctorAdd]; rw [shiftIso_add]

set_option backward.defeqAttrib.useBackward true in
/--
lemma `shiftIso_add'_hom_app` / 引理 `shiftIso_add'_hom_app`

English:
lemma shiftIso_add'_hom_app
  statement: (n m mn : A) (hnm : m + n = mn) (a a' a'' : A)
  proof: by
  simp [F.shiftIso_add' n m mn hnm a a' a'' ha' ha'']

中文:
引理 shiftIso_add'_hom_app
  结论: (n m mn : A) (hnm : m + n = mn) (a a' a'' : A)
  证明: by
  simp [F.shiftIso_add' n m mn hnm a a' a'' ha' ha'']
-/
lemma shiftIso_add'_hom_app (n m mn : A) (hnm : m + n = mn) (a a' a'' : A)
    (ha' : n + a = a') (ha'' : m + a' = a'') (X : C) :
    (F.shiftIso mn a a'' (by rw [← hnm, ← ha'', ← ha', add_assoc])).hom.app X =
      (shiftFunctorAdd' D m n mn hnm).hom.app ((F.functor a'').obj X) ≫
        ((F.shiftIso m a' a'' ha'').hom.app X)⟦n⟧' ≫ (F.shiftIso n a a' ha').hom.app X := by
  simp [F.shiftIso_add' n m mn hnm a a' a'' ha' ha'']

set_option backward.defeqAttrib.useBackward true in
/--
lemma `shiftIso_add'_inv_app` / 引理 `shiftIso_add'_inv_app`

English:
lemma shiftIso_add'_inv_app
  statement: (n m mn : A) (hnm : m + n = mn) (a a' a'' : A)
  proof: by
  simp [F.shiftIso_add' n m mn hnm a a' a'' ha' ha'']

@[simp]

中文:
引理 shiftIso_add'_inv_app
  结论: (n m mn : A) (hnm : m + n = mn) (a a' a'' : A)
  证明: by
  simp [F.shiftIso_add' n m mn hnm a a' a'' ha' ha'']

@[simp]
-/
lemma shiftIso_add'_inv_app (n m mn : A) (hnm : m + n = mn) (a a' a'' : A)
    (ha' : n + a = a') (ha'' : m + a' = a'') (X : C) :
    (F.shiftIso mn a a'' (by rw [← hnm, ← ha'', ← ha', add_assoc])).inv.app X =
      (F.shiftIso n a a' ha').inv.app X ≫
      ((F.shiftIso m a' a'' ha'').inv.app X)⟦n⟧' ≫
      (shiftFunctorAdd' D m n mn hnm).inv.app ((F.functor a'').obj X) := by
  simp [F.shiftIso_add' n m mn hnm a a' a'' ha' ha'']

@[simp]
/--
lemma `shiftIso_zero_hom_app` / 引理 `shiftIso_zero_hom_app`

English:
lemma shiftIso_zero_hom_app
  given: (a : A) (X : C)
  proof: by
  rw [shiftIso_zero]
  rfl

@[simp]

中文:
引理 shiftIso_zero_hom_app
  条件: (a : A) (X : C)
  证明: by
  rw [shiftIso_zero]
  rfl

@[simp]

Depends on / 依赖: shiftIso_zero
-/
lemma shiftIso_zero_hom_app (a : A) (X : C) :
    (F.shiftIso 0 a a (zero_add a)).hom.app X = (shiftFunctorZero D A).hom.app _ := by
  rw [shiftIso_zero]
  rfl

@[simp]
/--
lemma `shiftIso_zero_inv_app` / 引理 `shiftIso_zero_inv_app`

English:
lemma shiftIso_zero_inv_app
  given: (a : A) (X : C)
  proof: by
  rw [shiftIso_zero]
  rfl

中文:
引理 shiftIso_zero_inv_app
  条件: (a : A) (X : C)
  证明: by
  rw [shiftIso_zero]
  rfl

Depends on / 依赖: shiftIso_zero
-/
lemma shiftIso_zero_inv_app (a : A) (X : C) :
    (F.shiftIso 0 a a (zero_add a)).inv.app X = (shiftFunctorZero D A).inv.app _ := by
  rw [shiftIso_zero]
  rfl

/-- The morphisms in the category `SingleFunctors C D A` -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: where
  axioms and operations (2):
    - hom((a : A)) : F.functor a ⟶ G.functor a
    - comm((n a a' : A) (ha' : n + a = a')) : (F.shiftIso n a a' ha').hom ≫ hom a = whiskerRight (hom a') (shiftFunctor D n) ≫ (G.shiftIso n a a' ha').hom  [default: by cat_disch]

中文:
结构 态射
  参数: where
  公理与运算 (2 个):
    - hom((a : A)) : F.functor a ⟶ G.functor a
    - comm((n a a' : A) (ha' : n + a = a')) : (F.shiftIso n a a' ha').hom ≫ hom a = whiskerRight (hom a') (shiftFunctor D n) ≫ (G.shiftIso n a a' ha').hom  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure Hom where
  /-- a family of natural transformations `F.functor a ⟶ G.functor a` -/
  hom (a : A) : F.functor a ⟶ G.functor a
  comm (n a a' : A) (ha' : n + a = a') : (F.shiftIso n a a' ha').hom ≫ hom a =
    whiskerRight (hom a') (shiftFunctor D n) ≫ (G.shiftIso n a a' ha').hom := by cat_disch

namespace Hom

attribute [reassoc] comm
attribute [local simp] comm comm_assoc

/-- The identity morphism in `SingleFunctors C D A`. -/
@[simps]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : Hom F F where
  body: 𝟙 _

中文:
定义 id
  签名: : 态射 F F where
  定义体: 𝟙 _
-/
def id : Hom F F where
  hom _ := 𝟙 _

variable {F G H}

/-- The composition of morphisms in `SingleFunctors C D A`. -/
@[simps]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (α : Hom F G) (β : Hom G H)
  body: α.hom a ≫ β.hom a

中文:
定义 comp
  签名: (α : 态射 F G) (β : 态射 G H)
  定义体: α.hom a ≫ β.hom a
-/
def comp (α : Hom F G) (β : Hom G H) : Hom F H where
  hom a := α.hom a ≫ β.hom a

end Hom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (SingleFunctors C D A)
  body: Hom
  id := Hom.id
  comp := Hom.comp

@[simp]

中文:
实例 :
  签名: 范畴 (SingleFunctors C D A)
  定义体: Hom
  id := Hom.id
  comp := Hom.comp

@[simp]
-/
instance : Category (SingleFunctors C D A) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

@[simp]
/--
lemma `id_hom` / 引理 `id_hom`

English:
lemma id_hom
  given: (a : A)
  statement: Hom.hom (𝟙 F) a = 𝟙 _
  proof: rfl

中文:
引理 id_hom
  条件: (a : A)
  结论: 态射.hom (𝟙 F) a = 𝟙 _
  证明: rfl
-/
lemma id_hom (a : A) : Hom.hom (𝟙 F) a = 𝟙 _ := rfl

variable {F G H}

@[simp, reassoc]
/--
lemma `comp_hom` / 引理 `comp_hom`

English:
lemma comp_hom
  given: (f : F ⟶ G) (g : G ⟶ H) (a : A)
  statement: (f ≫ g).hom a = f.hom a ≫ g.hom a
  proof: rfl

@[ext]

中文:
引理 comp_hom
  条件: (f : F ⟶ G) (g : G ⟶ H) (a : A)
  结论: (f ≫ g).hom a = f.hom a ≫ g.hom a
  证明: rfl

@[ext]
-/
lemma comp_hom (f : F ⟶ G) (g : G ⟶ H) (a : A) : (f ≫ g).hom a = f.hom a ≫ g.hom a := rfl

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: (f g : F ⟶ G) (h : f.hom = g.hom)
  statement: f = g
  proof: Hom.ext h

中文:
引理 hom_ext
  条件: (f g : F ⟶ G) (h : f.hom = g.hom)
  结论: f = g
  证明: Hom.ext h

Depends on / 依赖: Hom.ext, IsColoop, M.IsColoop, closure_eq_right, hIX.isBasis_closure_right.closure_eq_right, heI.mem_closure_iff_mem, isBasis_closure_right, mem_closure_iff_mem
-/
lemma hom_ext (f g : F ⟶ G) (h : f.hom = g.hom) : f = g := Hom.ext h

/-- Construct an isomorphism in `SingleFunctors C D A` by giving
level-wise isomorphisms and checking compatibility only in the forward direction. -/
@[simps]
/--
Definition of `isoMk` / `isoMk` 的定义

English:
definition isoMk
  signature: (iso : forall a, (F.functor a ≅ G.functor a))
  body: { hom := fun a => (iso a).hom
      comm := comm }
  inv :=
    { hom := fun a => (iso a).inv
      comm := fun n a a' ha' => by
        rw [← cancel_mono (iso a).hom]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]; rw [comm]; rw [← whiskerRight_comp_assoc]; rw [Iso.inv_hom_id]; rw [whis

中文:
定义 isoMk
  签名: (iso : 对任意 a, (F.functor a ≅ G.functor a))
  定义体: { hom := fun a => (iso a).hom
      comm := comm }
  inv :=
    { hom := fun a => (iso a).inv
      comm := fun n a a' ha' => by
        rw [← cancel_mono (iso a).hom]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]; rw [comm]; rw [← whiskerRight_comp_assoc]; rw [Iso.inv_hom_id]; rw [whis

Depends on / 依赖: Iso.inv_hom_id, cancel_mono, comp_id, id_comp, inv_hom_id, whiskerRight_comp_assoc, whiskerRight_id
-/
def isoMk (iso : forall a, (F.functor a ≅ G.functor a))
    (comm : forall (n a a' : A) (ha' : n + a = a'), (F.shiftIso n a a' ha').hom ≫ (iso a).hom =
      whiskerRight (iso a').hom (shiftFunctor D n) ≫ (G.shiftIso n a a' ha').hom) :
    F ≅ G where
  hom :=
    { hom := fun a => (iso a).hom
      comm := comm }
  inv :=
    { hom := fun a => (iso a).inv
      comm := fun n a a' ha' => by
        rw [← cancel_mono (iso a).hom]; rw [assoc]; rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]; rw [comm]; rw [← whiskerRight_comp_assoc]; rw [Iso.inv_hom_id]; rw [whiskerRight_id']; rw [id_comp] }

variable (C D)

/-- The evaluation `SingleFunctors C D A ⥤ C ⥤ D` for some `a : A`. -/
@[simps]
/--
Definition of `evaluation` / `evaluation` 的定义

English:
definition evaluation
  signature: (a : A)
  body: F.functor a
  map {_ _} φ := φ.hom a

中文:
定义 evaluation
  签名: (a : A)
  定义体: F.functor a
  map {_ _} φ := φ.hom a

Depends on / 依赖: F.functor, functor
-/
def evaluation (a : A) : SingleFunctors C D A ⥤ C ⥤ D where
  obj F := F.functor a
  map {_ _} φ := φ.hom a

variable {C D}

@[reassoc (attr := simp)]
/--
lemma `hom_inv_id_hom` / 引理 `hom_inv_id_hom`

English:
lemma hom_inv_id_hom
  given: (e : F ≅ G) (n : A)
  statement: e.hom.hom n ≫ e.inv.hom n = 𝟙 _
  proof: by
  rw [← comp_hom]; rw [e.hom_inv_id]; rw [id_hom]

@[reassoc (attr := simp)]

中文:
引理 hom_inv_id_hom
  条件: (e : F ≅ G) (n : A)
  结论: e.hom.hom n ≫ e.inv.hom n = 𝟙 _
  证明: by
  rw [← comp_hom]; rw [e.hom_inv_id]; rw [id_hom]

@[reassoc (attr := simp)]

Depends on / 依赖: comp_hom, e.hom_inv_id, hom_inv_id, id_hom
-/
lemma hom_inv_id_hom (e : F ≅ G) (n : A) : e.hom.hom n ≫ e.inv.hom n = 𝟙 _ := by
  rw [← comp_hom]; rw [e.hom_inv_id]; rw [id_hom]

@[reassoc (attr := simp)]
/--
lemma `inv_hom_id_hom` / 引理 `inv_hom_id_hom`

English:
lemma inv_hom_id_hom
  given: (e : F ≅ G) (n : A)
  statement: e.inv.hom n ≫ e.hom.hom n = 𝟙 _
  proof: by
  rw [← comp_hom]; rw [e.inv_hom_id]; rw [id_hom]

@[reassoc (attr := simp)]

中文:
引理 inv_hom_id_hom
  条件: (e : F ≅ G) (n : A)
  结论: e.inv.hom n ≫ e.hom.hom n = 𝟙 _
  证明: by
  rw [← comp_hom]; rw [e.inv_hom_id]; rw [id_hom]

@[reassoc (attr := simp)]

Depends on / 依赖: comp_hom, e.inv_hom_id, id_hom, inv_hom_id
-/
lemma inv_hom_id_hom (e : F ≅ G) (n : A) : e.inv.hom n ≫ e.hom.hom n = 𝟙 _ := by
  rw [← comp_hom]; rw [e.inv_hom_id]; rw [id_hom]

@[reassoc (attr := simp)]
/--
lemma `hom_inv_id_hom_app` / 引理 `hom_inv_id_hom_app`

English:
lemma hom_inv_id_hom_app
  given: (e : F ≅ G) (n : A) (X : C)
  proof: by
  rw [← NatTrans.comp_app]; rw [hom_inv_id_hom]; rw [NatTrans.id_app]

@[reassoc (attr := simp)]

中文:
引理 hom_inv_id_hom_app
  条件: (e : F ≅ G) (n : A) (X : C)
  证明: by
  rw [← NatTrans.comp_app]; rw [hom_inv_id_hom]; rw [NatTrans.id_app]

@[reassoc (attr := simp)]

Depends on / 依赖: NatTrans, NatTrans.comp_app, NatTrans.id_app, comp_app, hom_inv_id_hom, id_app
-/
lemma hom_inv_id_hom_app (e : F ≅ G) (n : A) (X : C) :
    (e.hom.hom n).app X ≫ (e.inv.hom n).app X = 𝟙 _ := by
  rw [← NatTrans.comp_app]; rw [hom_inv_id_hom]; rw [NatTrans.id_app]

@[reassoc (attr := simp)]
/--
lemma `inv_hom_id_hom_app` / 引理 `inv_hom_id_hom_app`

English:
lemma inv_hom_id_hom_app
  given: (e : F ≅ G) (n : A) (X : C)
  proof: by
  rw [← NatTrans.comp_app]; rw [inv_hom_id_hom]; rw [NatTrans.id_app]

中文:
引理 inv_hom_id_hom_app
  条件: (e : F ≅ G) (n : A) (X : C)
  证明: by
  rw [← NatTrans.comp_app]; rw [inv_hom_id_hom]; rw [NatTrans.id_app]

Depends on / 依赖: NatTrans, NatTrans.comp_app, NatTrans.id_app, comp_app, id_app, inv_hom_id_hom
-/
lemma inv_hom_id_hom_app (e : F ≅ G) (n : A) (X : C) :
    (e.inv.hom n).app X ≫ (e.hom.hom n).app X = 𝟙 _ := by
  rw [← NatTrans.comp_app]; rw [inv_hom_id_hom]; rw [NatTrans.id_app]

instance (f : F ⟶ G) [IsIso f] (n : A) : IsIso (f.hom n) :=
inferInstanceAs IsIso ((evaluation C D n).map f)

variable (F)

set_option backward.defeqAttrib.useBackward true in
/-- Given `F : SingleFunctors C D A`, and a functor `G : D ⥤ E` which commutes
with the shift by `A`, this is the "composition" of `F` and `G` in `SingleFunctors C E A`. -/
@[simps! functor shiftIso_hom_app shiftIso_inv_app]
/--
Definition of `postcomp` / `postcomp` 的定义

English:
definition postcomp
  signature: (G : D ⥤ E) [G.CommShift A]
  body: F.functor a ⋙ G
  shiftIso n a a' ha' :=
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (G.commShiftIso n).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (F.shiftIso n a a' ha') G
  shiftIso_zero a := by
    ext X
    dsimp
    simp only [Functor.commShiftIso_zero, Functor.CommSh

中文:
定义 postcomp
  签名: (G : D ⥤ E) [G.交换Shift A]
  定义体: F.functor a ⋙ G
  shiftIso n a a' ha' :=
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (G.commShiftIso n).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (F.shiftIso n a a' ha') G
  shiftIso_zero a := by
    ext X
    dsimp
    simp only [Functor.commShiftIso_zero, Functor.CommSh

Depends on / 依赖: F.functor, functor
-/
def postcomp (G : D ⥤ E) [G.CommShift A] :
    SingleFunctors C E A where
  functor a := F.functor a ⋙ G
  shiftIso n a a' ha' :=
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (G.commShiftIso n).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (F.shiftIso n a a' ha') G
  shiftIso_zero a := by
    ext X
    dsimp
    simp only [Functor.commShiftIso_zero, Functor.CommShift.isoZero_inv_app,
      SingleFunctors.shiftIso_zero_hom_app, id_comp, assoc, ← G.map_comp, Iso.inv_hom_id_app,
      Functor.map_id, Functor.id_obj, comp_id]
  shiftIso_add n m a a' a'' ha' ha'' := by
    ext X
    dsimp
    simp only [F.shiftIso_add_hom_app n m a a' a'' ha' ha'', Functor.commShiftIso_add,
      Functor.CommShift.isoAdd_inv_app, Functor.map_comp, id_comp, assoc,
      Functor.commShiftIso_inv_naturality_assoc]
    simp only [← G.map_comp, Iso.inv_hom_id_app_assoc]

variable (C A)

set_option backward.defeqAttrib.useBackward true in
/-- The functor `SingleFunctors C D A ⥤ SingleFunctors C E A` given by the postcomposition
by a functor `G : D ⥤ E` which commutes with the shift. -/
@[simps]
/--
Definition of `postcompFunctor` / `postcompFunctor` 的定义

English:
definition postcompFunctor
  signature: (G : D ⥤ E) [G.CommShift A]
  body: F.postcomp G
  map {F₁ F₂} φ :=
    { hom := fun a => whiskerRight (φ.hom a) G
      comm := fun n a a' ha' => by
        ext X
        simpa using G.congr_map (congr_app (φ.comm n a a' ha') X) }

中文:
定义 postcompFunctor
  签名: (G : D ⥤ E) [G.交换Shift A]
  定义体: F.postcomp G
  map {F₁ F₂} φ :=
    { hom := fun a => whiskerRight (φ.hom a) G
      comm := fun n a a' ha' => by
        ext X
        simpa using G.congr_map (congr_app (φ.comm n a a' ha') X) }

Depends on / 依赖: F.postcomp, postcomp
-/
def postcompFunctor (G : D ⥤ E) [G.CommShift A] :
    SingleFunctors C D A ⥤ SingleFunctors C E A where
  obj F := F.postcomp G
  map {F₁ F₂} φ :=
    { hom := fun a => whiskerRight (φ.hom a) G
      comm := fun n a a' ha' => by
        ext X
        simpa using G.congr_map (congr_app (φ.comm n a a' ha') X) }

variable {C E' A}

set_option backward.defeqAttrib.useBackward true in
/-- The canonical isomorphism `(F.postcomp G).postcomp G' ≅ F.postcomp (G ⋙ G')`. -/
@[simps!]
/--
Definition of `postcompPostcompIso` / `postcompPostcompIso` 的定义

English:
definition postcompPostcompIso
  signature: (G : D ⥤ E) (G' : E ⥤ E') [G.CommShift A] [G'.CommShift A]
  body: isoMk (fun _ => Functor.associator _ _ _) (fun n a a' ha' => by
    ext X
    simp [Functor.commShiftIso_comp_inv_app])

中文:
定义 postcompPostcompIso
  签名: (G : D ⥤ E) (G' : E ⥤ E') [G.交换Shift A] [G'.交换Shift A]
  定义体: isoMk (fun _ => Functor.associator _ _ _) (fun n a a' ha' => by
    ext X
    simp [Functor.commShiftIso_comp_inv_app])

Depends on / 依赖: Functor, Functor.associator, Functor.commShiftIso_comp_inv_app, associator, commShiftIso_comp_inv_app
-/
def postcompPostcompIso (G : D ⥤ E) (G' : E ⥤ E') [G.CommShift A] [G'.CommShift A] :
    (F.postcomp G).postcomp G' ≅ F.postcomp (G ⋙ G') :=
  isoMk (fun _ => Functor.associator _ _ _) (fun n a a' ha' => by
    ext X
    simp [Functor.commShiftIso_comp_inv_app])

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism `F.postcomp G ≅ F.postcomp G'` induced by an isomorphism `e : G ≅ G'`
which commutes with the shift. -/
@[simps!]
/--
Definition of `postcompIsoOfIso` / `postcompIsoOfIso` 的定义

English:
definition postcompIsoOfIso
  signature: {G G' : D ⥤ E} (e : G ≅ G') [G.CommShift A] [G'.CommShift A]
  body: isoMk (fun a => isoWhiskerLeft (F.functor a) e) (fun n a a' ha' => by
    ext X
    simp [NatTrans.shift_app e.hom n])

中文:
定义 postcompIsoOfIso
  签名: {G G' : D ⥤ E} (e : G ≅ G') [G.交换Shift A] [G'.交换Shift A]
  定义体: isoMk (fun a => isoWhiskerLeft (F.functor a) e) (fun n a a' ha' => by
    ext X
    simp [NatTrans.shift_app e.hom n])

Depends on / 依赖: F.functor, NatTrans, NatTrans.shift_app, e.hom, functor, isoWhiskerLeft, shift_app
-/
def postcompIsoOfIso {G G' : D ⥤ E} (e : G ≅ G') [G.CommShift A] [G'.CommShift A]
    [NatTrans.CommShift e.hom A] :
    F.postcomp G ≅ F.postcomp G' :=
  isoMk (fun a => isoWhiskerLeft (F.functor a) e) (fun n a a' ha' => by
    ext X
    simp [NatTrans.shift_app e.hom n])

end SingleFunctors

end CategoryTheory
