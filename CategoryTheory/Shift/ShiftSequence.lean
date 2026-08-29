/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Sequences of functors from a category equipped with a shift

Let `F : C ⥤ A` be a functor from a category `C` that is equipped with a
shift by an additive monoid `M`. In this file, we define a typeclass
`F.ShiftSequence M` which includes the data of a sequence of functors
`F.shift a : C ⥤ A` for all `a : A`. For each `a : A`, we have
an isomorphism `F.isoShift a : shiftFunctor C a ⋙ F ≅ F.shift a` which
satisfies some coherence relations. This allows to state results
(e.g. the long exact sequence of a homology functor (TODO)) using
functors `F.shift a` rather than `shiftFunctor C a ⋙ F`. The reason
for this design is that we can often choose functors `F.shift a` that
have better definitional properties than `shiftFunctor C a ⋙ F`.
For example, if `C` is the derived category (TODO) of an abelian
category `A` and `F` is the homology functor in degree `0`, then
for any `n : ℤ`, we may choose `F.shift n` to be the homology functor
in degree `n`.

-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

open CategoryTheory Category ZeroObject Limits

variable {C D A : Type*} [Category* C] [Category* D] [Category* A] (F : C ⥤ A)
  {π : C ⥤ D} {H : D ⥤ A} (e : π ⋙ H ≅ F)
  (M : Type*) [AddMonoid M] [HasShift C M] [HasShift D M]
  {G : Type*} [AddGroup G] [HasShift C G]

namespace CategoryTheory

namespace Functor

/--
Definition of `ShiftSequence` / `ShiftSequence` 的定义

English:
class ShiftSequence
  parameters: where
  axioms and operations (5):
    - sequence : M -> C ⥤ A
    - isoZero : sequence 0 ≅ F
    - shiftIso((n a a' : M) (ha' : n + a = a')) : shiftFunctor C n ⋙ sequence a ≅ sequence a'
    - shiftIso_zero((a : M)) : shiftIso 0 a a (zero_add a) = isoWhiskerRight (shiftFunctorZero C M) _ ≪≫ leftUnitor _
    - shiftIso_add : forall (n m a a' a'' : M) (ha' : n + a = a') (ha'' : m + a' = a''), shiftIso (m + n) a a'' (by rw [add_assoc, ha', ha'']) = isoWhiskerRight (shiftFunctorAdd C m n) _ ≪≫ Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ (shiftIso n a a' ha') ≪≫ shiftIso m a' a'' ha''

中文:
类 ShiftSequence
  参数: where
  公理与运算 (5 个):
    - sequence : M -> C ⥤ A
    - isoZero : sequence 0 ≅ F
    - shiftIso((n a a' : M) (ha' : n + a = a')) : shiftFunctor C n ⋙ sequence a ≅ sequence a'
    - shiftIso_zero((a : M)) : shiftIso 0 a a (zero_add a) = isoWhiskerRight (shiftFunctorZero C M) _ ≪≫ leftUnitor _
    - shiftIso_add : 对任意 (n m a a' a'' : M) (ha' : n + a = a') (ha'' : m + a' = a''), shiftIso (m + n) a a'' (by rw [add_assoc, ha', ha'']) = isoWhiskerRight (shiftFunctorAdd C m n) _ ≪≫ 函子.associator _ _ _ ≪≫ isoWhiskerLeft _ (shiftIso n a a' ha') ≪≫ shiftIso m a' a'' ha''
-/
class ShiftSequence where
  /-- a sequence of functors -/
  sequence : M -> C ⥤ A
  /-- `sequence 0` identifies to the given functor -/
  isoZero : sequence 0 ≅ F
  /-- compatibility isomorphism with the shift -/
  shiftIso (n a a' : M) (ha' : n + a = a') : shiftFunctor C n ⋙ sequence a ≅ sequence a'
  shiftIso_zero (a : M) : shiftIso 0 a a (zero_add a) =
    isoWhiskerRight (shiftFunctorZero C M) _ ≪≫ leftUnitor _
  shiftIso_add : forall (n m a a' a'' : M) (ha' : n + a = a') (ha'' : m + a' = a''),
    shiftIso (m + n) a a'' (by rw [add_assoc, ha', ha'']) =
      isoWhiskerRight (shiftFunctorAdd C m n) _ ≪≫ Functor.associator _ _ _ ≪≫
        isoWhiskerLeft _ (shiftIso n a a' ha') ≪≫ shiftIso m a' a'' ha''

set_option backward.defeqAttrib.useBackward true in
/-- The tautological shift sequence on a functor. -/
@[instance_reducible]
/--
Definition of `ShiftSequence.tautological` / `ShiftSequence.tautological` 的定义

English:
definition ShiftSequence.tautological
  signature: : ShiftSequence F M where
  body: shiftFunctor C n ⋙ F
  isoZero := isoWhiskerRight (shiftFunctorZero C M) F ≪≫ F.leftUnitor
  shiftIso n a a' ha' := (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (shiftFunctorAdd' C n a a' ha').symm _
  shiftIso_zero a := by
    rw [shiftFunctorAdd'_zero_add]
    cat_disch
  shiftIso_add n 

中文:
定义 ShiftSequence.tautological
  签名: : ShiftSequence F M where
  定义体: shiftFunctor C n ⋙ F
  isoZero := isoWhiskerRight (shiftFunctorZero C M) F ≪≫ F.leftUnitor
  shiftIso n a a' ha' := (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (shiftFunctorAdd' C n a a' ha').symm _
  shiftIso_zero a := by
    rw [shiftFunctorAdd'_zero_add]
    cat_disch
  shiftIso_add n 

Depends on / 依赖: shiftFunctor
-/
noncomputable def ShiftSequence.tautological : ShiftSequence F M where
  sequence n := shiftFunctor C n ⋙ F
  isoZero := isoWhiskerRight (shiftFunctorZero C M) F ≪≫ F.leftUnitor
  shiftIso n a a' ha' := (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (shiftFunctorAdd' C n a a' ha').symm _
  shiftIso_zero a := by
    rw [shiftFunctorAdd'_zero_add]
    cat_disch
  shiftIso_add n m a a' a'' ha' ha'' := by
    ext X
    dsimp
    simp only [id_comp, ← Functor.map_comp]
    congr
    simpa only [← cancel_epi ((shiftFunctor C a).map ((shiftFunctorAdd C m n).hom.app X)),
      shiftFunctorAdd'_eq_shiftFunctorAdd, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
      Functor.map_id, id_comp] using! shiftFunctorAdd'_assoc_inv_app m n a (m + n) a' a'' rfl ha'
        (by rw [← ha'', ← ha', add_assoc]) X

section

variable {M}
variable [F.ShiftSequence M]

/--
Definition of `shift` / `shift` 的定义

English:
definition shift
  signature: (n : M)
  body: ShiftSequence.sequence F n

中文:
定义 shift
  签名: (n : M)
  定义体: ShiftSequence.sequence F n

Depends on / 依赖: ShiftSequence, ShiftSequence.sequence, sequence
-/
def shift (n : M) : C ⥤ A := ShiftSequence.sequence F n

/--
Definition of `shiftIso` / `shiftIso` 的定义

English:
definition shiftIso
  signature: (n a a' : M) (ha' : n + a = a')
  body: ShiftSequence.shiftIso n a a' ha'

@[reassoc (attr := simp)]

中文:
定义 shiftIso
  签名: (n a a' : M) (ha' : n + a = a')
  定义体: ShiftSequence.shiftIso n a a' ha'

@[reassoc (attr := simp)]

Depends on / 依赖: ShiftSequence, ShiftSequence.shiftIso, shiftIso
-/
def shiftIso (n a a' : M) (ha' : n + a = a') :
    shiftFunctor C n ⋙ F.shift a ≅ F.shift a' :=
  ShiftSequence.shiftIso n a a' ha'

@[reassoc (attr := simp)]
/--
lemma `shiftIso_hom_naturality` / 引理 `shiftIso_hom_naturality`

English:
lemma shiftIso_hom_naturality
  given: {X Y : C} (n a a' : M) (ha' : n + a = a') (f : X ⟶ Y)
  proof: (F.shiftIso n a a' ha').hom.naturality f

@[reassoc]

中文:
引理 shiftIso_hom_naturality
  条件: {X Y : C} (n a a' : M) (ha' : n + a = a') (f : X ⟶ Y)
  证明: (F.shiftIso n a a' ha').hom.naturality f

@[reassoc]

Depends on / 依赖: F.shiftIso, hom.naturality, naturality, shiftIso
-/
lemma shiftIso_hom_naturality {X Y : C} (n a a' : M) (ha' : n + a = a') (f : X ⟶ Y) :
    (shift F a).map (f⟦n⟧') ≫ (shiftIso F n a a' ha').hom.app Y =
      (shiftIso F n a a' ha').hom.app X ≫ (shift F a').map f :=
  (F.shiftIso n a a' ha').hom.naturality f

@[reassoc]
/--
lemma `shiftIso_inv_naturality` / 引理 `shiftIso_inv_naturality`

English:
lemma shiftIso_inv_naturality
  given: {X Y : C} (n a a' : M) (ha' : n + a = a') (f : X ⟶ Y)
  proof: by
  simp

中文:
引理 shiftIso_inv_naturality
  条件: {X Y : C} (n a a' : M) (ha' : n + a = a') (f : X ⟶ Y)
  证明: by
  simp
-/
lemma shiftIso_inv_naturality {X Y : C} (n a a' : M) (ha' : n + a = a') (f : X ⟶ Y) :
    (shift F a').map f ≫ (shiftIso F n a a' ha').inv.app Y =
      (shiftIso F n a a' ha').inv.app X ≫ (shift F a).map (f⟦n⟧') := by
  simp

variable (M) in
/--
Definition of `isoShiftZero` / `isoShiftZero` 的定义

English:
definition isoShiftZero
  signature: : F.shift (0 : M) ≅ F
  body: ShiftSequence.isoZero

中文:
定义 isoShiftZero
  签名: : F.shift (0 : M) ≅ F
  定义体: ShiftSequence.isoZero

Depends on / 依赖: ShiftSequence, ShiftSequence.isoZero, isoZero
-/
def isoShiftZero : F.shift (0 : M) ≅ F := ShiftSequence.isoZero

/--
Definition of `isoShift` / `isoShift` 的定义

English:
definition isoShift
  signature: (n : M)
  body: isoWhiskerLeft _ (F.isoShiftZero M).symm ≪≫ F.shiftIso _ _ _ (add_zero n)

@[reassoc]

中文:
定义 isoShift
  签名: (n : M)
  定义体: isoWhiskerLeft _ (F.isoShiftZero M).symm ≪≫ F.shiftIso _ _ _ (add_zero n)

@[reassoc]

Depends on / 依赖: F.isoShiftZero, F.shiftIso, add_zero, isoShiftZero, isoWhiskerLeft, shiftIso
-/
def isoShift (n : M) : shiftFunctor C n ⋙ F ≅ F.shift n :=
  isoWhiskerLeft _ (F.isoShiftZero M).symm ≪≫ F.shiftIso _ _ _ (add_zero n)

@[reassoc]
/--
lemma `isoShift_hom_naturality` / 引理 `isoShift_hom_naturality`

English:
lemma isoShift_hom_naturality
  given: (n : M) {X Y : C} (f : X ⟶ Y)
  proof: (F.isoShift n).hom.naturality f

中文:
引理 isoShift_hom_naturality
  条件: (n : M) {X Y : C} (f : X ⟶ Y)
  证明: (F.isoShift n).hom.naturality f

Depends on / 依赖: F.isoShift, hom.naturality, isoShift, naturality
-/
lemma isoShift_hom_naturality (n : M) {X Y : C} (f : X ⟶ Y) :
    F.map (f⟦n⟧') ≫ (F.isoShift n).hom.app Y =
      (F.isoShift n).hom.app X ≫ (F.shift n).map f :=
  (F.isoShift n).hom.naturality f

attribute [simp] isoShift_hom_naturality

@[reassoc]
/--
lemma `isoShift_inv_naturality` / 引理 `isoShift_inv_naturality`

English:
lemma isoShift_inv_naturality
  given: (n : M) {X Y : C} (f : X ⟶ Y)
  proof: (F.isoShift n).inv.naturality f

中文:
引理 isoShift_inv_naturality
  条件: (n : M) {X Y : C} (f : X ⟶ Y)
  证明: (F.isoShift n).inv.naturality f

Depends on / 依赖: F.isoShift, inv.naturality, isoShift, naturality
-/
lemma isoShift_inv_naturality (n : M) {X Y : C} (f : X ⟶ Y) :
    (F.shift n).map f ≫ (F.isoShift n).inv.app Y =
      (F.isoShift n).inv.app X ≫ F.map (f⟦n⟧') :=
  (F.isoShift n).inv.naturality f

/--
lemma `shiftIso_zero` / 引理 `shiftIso_zero`

English:
lemma shiftIso_zero
  given: (a : M)
  proof: ShiftSequence.shiftIso_zero a

中文:
引理 shiftIso_zero
  条件: (a : M)
  证明: ShiftSequence.shiftIso_zero a

Depends on / 依赖: ShiftSequence, ShiftSequence.shiftIso_zero, shiftIso_zero
-/
lemma shiftIso_zero (a : M) :
    F.shiftIso 0 a a (zero_add a) =
      isoWhiskerRight (shiftFunctorZero C M) _ ≪≫ leftUnitor _ :=
  ShiftSequence.shiftIso_zero a

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `shiftIso_zero_hom_app` / 引理 `shiftIso_zero_hom_app`

English:
lemma shiftIso_zero_hom_app
  given: (a : M) (X : C)
  proof: by
  simp [F.shiftIso_zero a]

中文:
引理 shiftIso_zero_hom_app
  条件: (a : M) (X : C)
  证明: by
  simp [F.shiftIso_zero a]

Depends on / 依赖: F.shiftIso_zero, shiftIso_zero
-/
lemma shiftIso_zero_hom_app (a : M) (X : C) :
    (F.shiftIso 0 a a (zero_add a)).hom.app X =
      (shift F a).map ((shiftFunctorZero C M).hom.app X) := by
  simp [F.shiftIso_zero a]

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
lemma `shiftIso_zero_inv_app` / 引理 `shiftIso_zero_inv_app`

English:
lemma shiftIso_zero_inv_app
  given: (a : M) (X : C)
  proof: by
  simp [F.shiftIso_zero a]

中文:
引理 shiftIso_zero_inv_app
  条件: (a : M) (X : C)
  证明: by
  simp [F.shiftIso_zero a]

Depends on / 依赖: F.shiftIso_zero, shiftIso_zero
-/
lemma shiftIso_zero_inv_app (a : M) (X : C) :
    (F.shiftIso 0 a a (zero_add a)).inv.app X =
      (shift F a).map ((shiftFunctorZero C M).inv.app X) := by
  simp [F.shiftIso_zero a]

/--
lemma `shiftIso_add` / 引理 `shiftIso_add`

English:
lemma shiftIso_add
  given: (n m a a' a'' : M) (ha' : n + a = a') (ha'' : m + a' = a'')
  proof: ShiftSequence.shiftIso_add _ _ _ _ _ _ _

中文:
引理 shiftIso_add
  条件: (n m a a' a'' : M) (ha' : n + a = a') (ha'' : m + a' = a'')
  证明: ShiftSequence.shiftIso_add _ _ _ _ _ _ _

Depends on / 依赖: ShiftSequence, ShiftSequence.shiftIso_add, shiftIso_add
-/
lemma shiftIso_add (n m a a' a'' : M) (ha' : n + a = a') (ha'' : m + a' = a'') :
    F.shiftIso (m + n) a a'' (by rw [add_assoc, ha', ha'']) =
      isoWhiskerRight (shiftFunctorAdd C m n) _ ≪≫ Functor.associator _ _ _ ≪≫
        isoWhiskerLeft _ (F.shiftIso n a a' ha') ≪≫ F.shiftIso m a' a'' ha'' :=
  ShiftSequence.shiftIso_add _ _ _ _ _ _ _

set_option backward.defeqAttrib.useBackward true in
/--
lemma `shiftIso_add_hom_app` / 引理 `shiftIso_add_hom_app`

English:
lemma shiftIso_add_hom_app
  given: (n m a a' a'' : M) (ha' : n + a = a') (ha'' : m + a' = a'') (X : C)
  proof: by
  simp [F.shiftIso_add n m a a' a'' ha' ha'']

中文:
引理 shiftIso_add_hom_app
  条件: (n m a a' a'' : M) (ha' : n + a = a') (ha'' : m + a' = a'') (X : C)
  证明: by
  simp [F.shiftIso_add n m a a' a'' ha' ha'']

Depends on / 依赖: F.shiftIso_add, shiftIso_add
-/
lemma shiftIso_add_hom_app (n m a a' a'' : M) (ha' : n + a = a') (ha'' : m + a' = a'') (X : C) :
    (F.shiftIso (m + n) a a'' (by rw [add_assoc, ha', ha''])).hom.app X =
      (shift F a).map ((shiftFunctorAdd C m n).hom.app X) ≫
        (shiftIso F n a a' ha').hom.app ((shiftFunctor C m).obj X) ≫
          (shiftIso F m a' a'' ha'').hom.app X := by
  simp [F.shiftIso_add n m a a' a'' ha' ha'']

set_option backward.defeqAttrib.useBackward true in
/--
lemma `shiftIso_add_inv_app` / 引理 `shiftIso_add_inv_app`

English:
lemma shiftIso_add_inv_app
  given: (n m a a' a'' : M) (ha' : n + a = a') (ha'' : m + a' = a'') (X : C)
  proof: by
  simp [F.shiftIso_add n m a a' a'' ha' ha'']

中文:
引理 shiftIso_add_inv_app
  条件: (n m a a' a'' : M) (ha' : n + a = a') (ha'' : m + a' = a'') (X : C)
  证明: by
  simp [F.shiftIso_add n m a a' a'' ha' ha'']

Depends on / 依赖: F.shiftIso_add, shiftIso_add
-/
lemma shiftIso_add_inv_app (n m a a' a'' : M) (ha' : n + a = a') (ha'' : m + a' = a'') (X : C) :
    (F.shiftIso (m + n) a a'' (by rw [add_assoc, ha', ha''])).inv.app X =
      (shiftIso F m a' a'' ha'').inv.app X ≫
        (shiftIso F n a a' ha').inv.app ((shiftFunctor C m).obj X) ≫
          (shift F a).map ((shiftFunctorAdd C m n).inv.app X) := by
  simp [F.shiftIso_add n m a a' a'' ha' ha'']

/--
lemma `shiftIso_add'` / 引理 `shiftIso_add'`

English:
lemma shiftIso_add'
  statement: (n m mn : M) (hnm : m + n = mn) (a a' a'' : M)
  proof: by
  subst hnm
  rw [shiftFunctorAdd'_eq_shiftFunctorAdd]; rw [shiftIso_add]

中文:
引理 shiftIso_add'
  结论: (n m mn : M) (hnm : m + n = mn) (a a' a'' : M)
  证明: by
  subst hnm
  rw [shiftFunctorAdd'_eq_shiftFunctorAdd]; rw [shiftIso_add]

Depends on / 依赖: _eq_shiftFunctorAdd, shiftFunctorAdd, shiftIso_add
-/
lemma shiftIso_add' (n m mn : M) (hnm : m + n = mn) (a a' a'' : M)
    (ha' : n + a = a') (ha'' : m + a' = a'') :
    F.shiftIso mn a a'' (by rw [← hnm, ← ha'', ← ha', add_assoc]) =
      isoWhiskerRight (shiftFunctorAdd' C m n _ hnm) _ ≪≫ Functor.associator _ _ _ ≪≫
        isoWhiskerLeft _ (F.shiftIso n a a' ha') ≪≫ F.shiftIso m a' a'' ha'' := by
  subst hnm
  rw [shiftFunctorAdd'_eq_shiftFunctorAdd]; rw [shiftIso_add]

set_option backward.defeqAttrib.useBackward true in
/--
lemma `shiftIso_add'_hom_app` / 引理 `shiftIso_add'_hom_app`

English:
lemma shiftIso_add'_hom_app
  statement: (n m mn : M) (hnm : m + n = mn) (a a' a'' : M)
  proof: by
  simp [F.shiftIso_add' n m mn hnm a a' a'' ha' ha'']

中文:
引理 shiftIso_add'_hom_app
  结论: (n m mn : M) (hnm : m + n = mn) (a a' a'' : M)
  证明: by
  simp [F.shiftIso_add' n m mn hnm a a' a'' ha' ha'']
-/
lemma shiftIso_add'_hom_app (n m mn : M) (hnm : m + n = mn) (a a' a'' : M)
    (ha' : n + a = a') (ha'' : m + a' = a'') (X : C) :
    (F.shiftIso mn a a'' (by rw [← hnm, ← ha'', ← ha', add_assoc])).hom.app X =
      (shift F a).map ((shiftFunctorAdd' C m n mn hnm).hom.app X) ≫
        (shiftIso F n a a' ha').hom.app ((shiftFunctor C m).obj X) ≫
          (shiftIso F m a' a'' ha'').hom.app X := by
  simp [F.shiftIso_add' n m mn hnm a a' a'' ha' ha'']

set_option backward.defeqAttrib.useBackward true in
/--
lemma `shiftIso_add'_inv_app` / 引理 `shiftIso_add'_inv_app`

English:
lemma shiftIso_add'_inv_app
  statement: (n m mn : M) (hnm : m + n = mn) (a a' a'' : M)
  proof: by
  simp [F.shiftIso_add' n m mn hnm a a' a'' ha' ha'']

@[reassoc]

中文:
引理 shiftIso_add'_inv_app
  结论: (n m mn : M) (hnm : m + n = mn) (a a' a'' : M)
  证明: by
  simp [F.shiftIso_add' n m mn hnm a a' a'' ha' ha'']

@[reassoc]
-/
lemma shiftIso_add'_inv_app (n m mn : M) (hnm : m + n = mn) (a a' a'' : M)
    (ha' : n + a = a') (ha'' : m + a' = a'') (X : C) :
    (F.shiftIso mn a a'' (by rw [← hnm, ← ha'', ← ha', add_assoc])).inv.app X =
      (shiftIso F m a' a'' ha'').inv.app X ≫
        (shiftIso F n a a' ha').inv.app ((shiftFunctor C m).obj X) ≫
        (shift F a).map ((shiftFunctorAdd' C m n mn hnm).inv.app X) := by
  simp [F.shiftIso_add' n m mn hnm a a' a'' ha' ha'']

@[reassoc]
/--
lemma `shiftIso_hom_app_comp` / 引理 `shiftIso_hom_app_comp`

English:
lemma shiftIso_hom_app_comp
  statement: (n m mn : M) (hnm : m + n = mn)
  proof: by
  rw [F.shiftIso_add'_hom_app n m mn hnm a a' a'' ha' ha'']; rw [← Functor.map_comp_assoc]; rw [Iso.inv_hom_id_app]; rw [Functor.map_id]; rw [id_comp]

中文:
引理 shiftIso_hom_app_comp
  结论: (n m mn : M) (hnm : m + n = mn)
  证明: by
  rw [F.shiftIso_add'_hom_app n m mn hnm a a' a'' ha' ha'']; rw [← Functor.map_comp_assoc]; rw [Iso.inv_hom_id_app]; rw [Functor.map_id]; rw [id_comp]

Depends on / 依赖: F.shiftIso_add, Functor, Functor.map_comp_assoc, Functor.map_id, Iso.inv_hom_id_app, _hom_app, id_comp, inv_hom_id_app, map_comp_assoc, map_id, shiftIso_add
-/
lemma shiftIso_hom_app_comp (n m mn : M) (hnm : m + n = mn)
    (a a' a'' : M) (ha' : n + a = a') (ha'' : m + a' = a'') (X : C) :
    (shiftIso F n a a' ha').hom.app ((shiftFunctor C m).obj X) ≫
      (shiftIso F m a' a'' ha'').hom.app X =
        (shift F a).map ((shiftFunctorAdd' C m n mn hnm).inv.app X) ≫
          (F.shiftIso mn a a'' (by rw [← hnm, ← ha'', ← ha', add_assoc])).hom.app X := by
  rw [F.shiftIso_add'_hom_app n m mn hnm a a' a'' ha' ha'']; rw [← Functor.map_comp_assoc]; rw [Iso.inv_hom_id_app]; rw [Functor.map_id]; rw [id_comp]

/--
Definition of `shiftMap` / `shiftMap` 的定义

English:
definition shiftMap
  signature: {X Y : C} {n : M} (f : X ⟶ Y⟦n⟧) (a a' : M) (ha' : n + a = a')
  body: (F.shift a).map f ≫ (F.shiftIso _ _ _ ha').hom.app Y

中文:
定义 shiftMap
  签名: {X Y : C} {n : M} (f : X ⟶ Y⟦n⟧) (a a' : M) (ha' : n + a = a')
  定义体: (F.shift a).map f ≫ (F.shiftIso _ _ _ ha').hom.app Y

Depends on / 依赖: F.shift, F.shiftIso, hom.app, shiftIso
-/
def shiftMap {X Y : C} {n : M} (f : X ⟶ Y⟦n⟧) (a a' : M) (ha' : n + a = a') :
    (F.shift a).obj X ⟶ (F.shift a').obj Y :=
  (F.shift a).map f ≫ (F.shiftIso _ _ _ ha').hom.app Y

set_option backward.defeqAttrib.useBackward true in
@[reassoc]
/--
lemma `shiftMap_comp` / 引理 `shiftMap_comp`

English:
lemma shiftMap_comp
  given: {X Y Z : C} {n : M} (f : X ⟶ Y⟦n⟧) (g : Y ⟶ Z) (a a' : M) (ha' : n + a = a')
  proof: by
  simp [shiftMap]

@[reassoc]

中文:
引理 shiftMap_comp
  条件: {X Y Z : C} {n : M} (f : X ⟶ Y⟦n⟧) (g : Y ⟶ Z) (a a' : M) (ha' : n + a = a')
  证明: by
  simp [shiftMap]

@[reassoc]

Depends on / 依赖: shiftMap
-/
lemma shiftMap_comp {X Y Z : C} {n : M} (f : X ⟶ Y⟦n⟧) (g : Y ⟶ Z) (a a' : M) (ha' : n + a = a') :
    F.shiftMap (f ≫ g⟦n⟧') a a' ha' = F.shiftMap f a a' ha' ≫ (F.shift a').map g := by
  simp [shiftMap]

@[reassoc]
/--
lemma `shiftMap_comp'` / 引理 `shiftMap_comp'`

English:
lemma shiftMap_comp'
  given: {X Y Z : C} {n : M} (f : X ⟶ Y) (g : Y ⟶ Z⟦n⟧) (a a' : M) (ha' : n + a = a')
  proof: by
  simp [shiftMap]

中文:
引理 shiftMap_comp'
  条件: {X Y Z : C} {n : M} (f : X ⟶ Y) (g : Y ⟶ Z⟦n⟧) (a a' : M) (ha' : n + a = a')
  证明: by
  simp [shiftMap]

Depends on / 依赖: shiftMap
-/
lemma shiftMap_comp' {X Y Z : C} {n : M} (f : X ⟶ Y) (g : Y ⟶ Z⟦n⟧) (a a' : M) (ha' : n + a = a') :
    F.shiftMap (f ≫ g) a a' ha' = (F.shift a).map f ≫ F.shiftMap g a a' ha' := by
  simp [shiftMap]

/--
lemma `shiftIso_hom_app_comp_shiftMap` / 引理 `shiftIso_hom_app_comp_shiftMap`

English:
lemma shiftIso_hom_app_comp_shiftMap
  statement: {X Y : C} {m : M} (f : X ⟶ Y⟦m⟧) (n mn : M) (hnm : m + n = mn)
  proof: by
  simp only [F.shiftIso_add'_hom_app n m mn hnm a a' a'' ha' ha'' Y,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id,
    id_comp, comp_obj, shiftIso_hom_naturality_assoc, shiftMap]

中文:
引理 shiftIso_hom_app_comp_shiftMap
  结论: {X Y : C} {m : M} (f : X ⟶ Y⟦m⟧) (n mn : M) (hnm : m + n = mn)
  证明: by
  simp only [F.shiftIso_add'_hom_app n m mn hnm a a' a'' ha' ha'' Y,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id,
    id_comp, comp_obj, shiftIso_hom_naturality_assoc, shiftMap]

Depends on / 依赖: F.shiftIso_add, Functor, Functor.map_comp_assoc, Functor.map_id, Iso.inv_hom_id_app, _hom_app, comp_obj, id_comp, inv_hom_id_app, map_comp_assoc, map_id, shiftIso_add, shiftIso_hom_naturality_assoc, shiftMap
-/
lemma shiftIso_hom_app_comp_shiftMap {X Y : C} {m : M} (f : X ⟶ Y⟦m⟧) (n mn : M) (hnm : m + n = mn)
    (a a' a'' : M) (ha' : n + a = a') (ha'' : m + a' = a'') :
    (F.shiftIso n a a' ha').hom.app X ≫ F.shiftMap f a' a'' ha'' =
      (F.shift a).map (f⟦n⟧') ≫ (F.shift a).map ((shiftFunctorAdd' C m n mn hnm).inv.app Y) ≫
        (F.shiftIso mn a a'' (by rw [← ha'', ← ha', ← hnm, add_assoc])).hom.app Y := by
  simp only [F.shiftIso_add'_hom_app n m mn hnm a a' a'' ha' ha'' Y,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id,
    id_comp, comp_obj, shiftIso_hom_naturality_assoc, shiftMap]

/--
lemma `shiftIso_hom_app_comp_shiftMap_of_add_eq_zero` / 引理 `shiftIso_hom_app_comp_shiftMap_of_add_eq_zero`

English:
lemma shiftIso_hom_app_comp_shiftMap_of_add_eq_zero
  statement: [F.ShiftSequence G]
  proof: by
  have hnm' : m + n = 0 := by
    rw [← add_left_inj m]; rw [add_assoc]; rw [hnm]; rw [zero_add]; rw [add_zero]
  simp [F.shiftIso_hom_app_comp_shiftMap f n 0 hnm' a' a, shiftIso_zero_hom_app,
    shiftFunctorCompIsoId]

中文:
引理 shiftIso_hom_app_comp_shiftMap_of_add_eq_zero
  结论: [F.ShiftSequence G]
  证明: by
  have hnm' : m + n = 0 := by
    rw [← add_left_inj m]; rw [add_assoc]; rw [hnm]; rw [zero_add]; rw [add_zero]
  simp [F.shiftIso_hom_app_comp_shiftMap f n 0 hnm' a' a, shiftIso_zero_hom_app,
    shiftFunctorCompIsoId]

Depends on / 依赖: F.shiftIso_hom_app_comp_shiftMap, add_assoc, add_left_inj, add_zero, shiftFunctorCompIsoId, shiftIso_hom_app_comp_shiftMap, shiftIso_zero_hom_app, zero_add
-/
lemma shiftIso_hom_app_comp_shiftMap_of_add_eq_zero [F.ShiftSequence G]
    {X Y : C} {m : G} (f : X ⟶ Y⟦m⟧)
    (n : G) (hnm : n + m = 0) (a a' : G) (ha' : m + a = a') :
    (F.shiftIso n a' a (by rw [← ha', ← add_assoc, hnm, zero_add])).hom.app X ≫
      F.shiftMap f a a' ha' =
    (F.shift a').map (f⟦n⟧' ≫ (shiftFunctorCompIsoId C m n
      (by rw [← add_left_inj m, add_assoc, hnm, zero_add, add_zero])).hom.app Y) := by
  have hnm' : m + n = 0 := by
    rw [← add_left_inj m]; rw [add_assoc]; rw [hnm]; rw [zero_add]; rw [add_zero]
  simp [F.shiftIso_hom_app_comp_shiftMap f n 0 hnm' a' a, shiftIso_zero_hom_app,
    shiftFunctorCompIsoId]

section

variable [HasZeroMorphisms C] [HasZeroMorphisms A] [F.PreservesZeroMorphisms]
  [forall (n : M), (shiftFunctor C n).PreservesZeroMorphisms]

instance (n : M) : (F.shift n).PreservesZeroMorphisms :=
  preservesZeroMorphisms_of_iso (F.isoShift n)

@[simp]
/--
lemma `shiftMap_zero` / 引理 `shiftMap_zero`

English:
lemma shiftMap_zero
  given: (X Y : C) (n a a' : M) (ha' : n + a = a')
  proof: by
  simp [shiftMap]

中文:
引理 shiftMap_zero
  条件: (X Y : C) (n a a' : M) (ha' : n + a = a')
  证明: by
  simp [shiftMap]

Depends on / 依赖: shiftMap
-/
lemma shiftMap_zero (X Y : C) (n a a' : M) (ha' : n + a = a') :
    F.shiftMap (0 : X ⟶ Y⟦n⟧) a a' ha' = 0 := by
  simp [shiftMap]

end

section

variable [Preadditive C] [Preadditive A] [F.Additive]
  [forall (n : M), (shiftFunctor C n).Additive]

instance (n : M) : (F.shift n).Additive := additive_of_iso (F.isoShift n)

end

end

namespace ShiftSequence

variable {F} in
set_option backward.isDefEq.respectTransparency false in
/-- Given an isomorphism `π ⋙ H ≅ F`, where `π` is a functor which commutes
with the shift by `M` and `H` is equipped with a shift sequence,
then this is the shift sequence for `F` induced by composition. -/
@[implicit_reducible, simps]
/--
Definition of `leftComp` / `leftComp` 的定义

English:
definition leftComp
  signature: [π.CommShift M] [H.ShiftSequence M]
  body: π ⋙ H.shift n
  isoZero := isoWhiskerLeft π (H.isoShiftZero M) ≪≫ e
  shiftIso n a a' ha' :=
    (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (π.commShiftIso n) _ ≪≫ Functor.associator _ _ _ ≪≫
      isoWhiskerLeft π (H.shiftIso n a a' ha')
  shiftIso_zero a := by
    ext K
    simp [← F

中文:
定义 leftComp
  签名: [π.交换Shift M] [H.ShiftSequence M]
  定义体: π ⋙ H.shift n
  isoZero := isoWhiskerLeft π (H.isoShiftZero M) ≪≫ e
  shiftIso n a a' ha' :=
    (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (π.commShiftIso n) _ ≪≫ Functor.associator _ _ _ ≪≫
      isoWhiskerLeft π (H.shiftIso n a a' ha')
  shiftIso_zero a := by
    ext K
    simp [← F

Depends on / 依赖: H.shift
-/
def leftComp [π.CommShift M] [H.ShiftSequence M] : F.ShiftSequence M where
  sequence n := π ⋙ H.shift n
  isoZero := isoWhiskerLeft π (H.isoShiftZero M) ≪≫ e
  shiftIso n a a' ha' :=
    (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (π.commShiftIso n) _ ≪≫ Functor.associator _ _ _ ≪≫
      isoWhiskerLeft π (H.shiftIso n a a' ha')
  shiftIso_zero a := by
    ext K
    simp [← Functor.map_comp, commShiftIso_zero]
  shiftIso_add n m a a' a'' ha' ha'':= by
    ext K
    dsimp
    simp only [H.shiftIso_add_hom_app n m a a' a'' ha' ha'', assoc,
      commShiftIso_add, CommShift.isoAdd_hom_app, ← Functor.map_comp_assoc,
      id_comp, Iso.inv_hom_id_app, comp_obj, comp_id]
    simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [π.CommShift
  signature: M] [H.ShiftSequence M] : (π ⋙ H).ShiftSequence M
  body: leftComp (Iso.refl _) _

中文:
实例 [π.交换Shift
  签名: M] [H.ShiftSequence M] : (π ⋙ H).ShiftSequence M
  定义体: leftComp (Iso.refl _) _

Depends on / 依赖: Iso.refl, leftComp
-/
instance [π.CommShift M] [H.ShiftSequence M] : (π ⋙ H).ShiftSequence M :=
  leftComp (Iso.refl _) _

end ShiftSequence

end Functor

end CategoryTheory
