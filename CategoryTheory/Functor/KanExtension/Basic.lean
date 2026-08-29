/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Equivalence
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Kan extensions

The basic definitions for Kan extensions of functors are introduced in this file. Part of API
is parallel to the definitions for bicategories (see `CategoryTheory.Bicategory.Kan.IsKan`).
(The bicategory API cannot be used directly here because it would not allow the universe
polymorphism which is necessary for some applications.)

Given a natural transformation `α : L ⋙ F' ⟶ F`, we define the property
`F'.IsRightKanExtension α` which expresses that `(F', α)` is a right Kan
extension of `F` along `L`, i.e. that it is a terminal object in a
category `RightExtension L F` of costructured arrows. The condition
`F'.IsLeftKanExtension α` for `α : F ⟶ L ⋙ F'` is defined similarly.

We also introduce typeclasses `HasRightKanExtension L F` and `HasLeftKanExtension L F`
which assert the existence of a right or left Kan extension, and chosen Kan extensions
are obtained as `leftKanExtension L F` and `rightKanExtension L F`.

## References
* https://ncatlab.org/nlab/show/Kan+extension

-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

namespace CategoryTheory

open Category Limits

namespace Functor

variable {C C' H D D' : Type*}
  [Category* C] [Category* C'] [Category* H] [Category* D] [Category* D']

/--
Definition of `RightExtension` / `RightExtension` 的定义

English:
abbreviation RightExtension
  signature: (L : C ⥤ D) (F : C ⥤ H)
  body: CostructuredArrow ((whiskeringLeft C D H).obj L) F

中文:
缩写 RightExtension
  签名: (L : C ⥤ D) (F : C ⥤ H)
  定义体: CostructuredArrow ((whiskeringLeft C D H).obj L) F

Depends on / 依赖: CostructuredArrow, whiskeringLeft
-/
abbrev RightExtension (L : C ⥤ D) (F : C ⥤ H) :=
  CostructuredArrow ((whiskeringLeft C D H).obj L) F

/--
Definition of `LeftExtension` / `LeftExtension` 的定义

English:
abbreviation LeftExtension
  signature: (L : C ⥤ D) (F : C ⥤ H)
  body: StructuredArrow F ((whiskeringLeft C D H).obj L)

中文:
缩写 LeftExtension
  签名: (L : C ⥤ D) (F : C ⥤ H)
  定义体: StructuredArrow F ((whiskeringLeft C D H).obj L)

Depends on / 依赖: StructuredArrow, whiskeringLeft
-/
abbrev LeftExtension (L : C ⥤ D) (F : C ⥤ H) :=
  StructuredArrow F ((whiskeringLeft C D H).obj L)

/-- Constructor for objects of the category `Functor.RightExtension L F`. -/
@[simps!]
/--
Definition of `RightExtension.mk` / `RightExtension.mk` 的定义

English:
definition RightExtension.mk
  signature: (F' : D ⥤ H) {L : C ⥤ D} {F : C ⥤ H} (α : L ⋙ F' ⟶ F)
  body: CostructuredArrow.mk α

中文:
定义 RightExtension.mk
  签名: (F' : D ⥤ H) {L : C ⥤ D} {F : C ⥤ H} (α : L ⋙ F' ⟶ F)
  定义体: CostructuredArrow.mk α

Depends on / 依赖: CostructuredArrow, CostructuredArrow.mk
-/
def RightExtension.mk (F' : D ⥤ H) {L : C ⥤ D} {F : C ⥤ H} (α : L ⋙ F' ⟶ F) :
    RightExtension L F :=
  CostructuredArrow.mk α

/-- Constructor for objects of the category `Functor.LeftExtension L F`. -/
@[simps!]
/--
Definition of `LeftExtension.mk` / `LeftExtension.mk` 的定义

English:
definition LeftExtension.mk
  signature: (F' : D ⥤ H) {L : C ⥤ D} {F : C ⥤ H} (α : F ⟶ L ⋙ F')
  body: StructuredArrow.mk α

中文:
定义 LeftExtension.mk
  签名: (F' : D ⥤ H) {L : C ⥤ D} {F : C ⥤ H} (α : F ⟶ L ⋙ F')
  定义体: StructuredArrow.mk α

Depends on / 依赖: StructuredArrow, StructuredArrow.mk
-/
def LeftExtension.mk (F' : D ⥤ H) {L : C ⥤ D} {F : C ⥤ H} (α : F ⟶ L ⋙ F') :
    LeftExtension L F :=
  StructuredArrow.mk α

section

variable (F' : D ⥤ H) {L : C ⥤ D} {F : C ⥤ H} (α : L ⋙ F' ⟶ F)

/--
Definition of `IsRightKanExtension` / `IsRightKanExtension` 的定义

English:
class IsRightKanExtension
  parameters: : Prop where
  axioms and operations (1):
    - nonempty_isUniversal : Nonempty (RightExtension.mk F' α).IsUniversal

中文:
类 是RightKanExtension
  参数: : 命题 where
  公理与运算 (1 个):
    - nonempty_isUniversal : 非空 (RightExtension.mk F' α).是泛
-/
class IsRightKanExtension : Prop where
  nonempty_isUniversal : Nonempty (RightExtension.mk F' α).IsUniversal

variable [F'.IsRightKanExtension α]

/--
Definition of `isUniversalOfIsRightKanExtension` / `isUniversalOfIsRightKanExtension` 的定义

English:
definition isUniversalOfIsRightKanExtension
  signature: : (RightExtension.mk F' α).IsUniversal
  body: IsRightKanExtension.nonempty_isUniversal.some

中文:
定义 isUniversalOfIsRightKanExtension
  签名: : (RightExtension.mk F' α).是泛
  定义体: IsRightKanExtension.nonempty_isUniversal.some

Depends on / 依赖: IsRightKanExtension, IsRightKanExtension.nonempty_isUniversal.some, nonempty_isUniversal
-/
noncomputable def isUniversalOfIsRightKanExtension : (RightExtension.mk F' α).IsUniversal :=
  IsRightKanExtension.nonempty_isUniversal.some

/--
Definition of `liftOfIsRightKanExtension` / `liftOfIsRightKanExtension` 的定义

English:
definition liftOfIsRightKanExtension
  signature: (G : D ⥤ H) (β : L ⋙ G ⟶ F)
  body: (F'.isUniversalOfIsRightKanExtension α).lift (RightExtension.mk G β)

@[reassoc (attr := simp)]

中文:
定义 liftOfIsRightKanExtension
  签名: (G : D ⥤ H) (β : L ⋙ G ⟶ F)
  定义体: (F'.isUniversalOfIsRightKanExtension α).lift (RightExtension.mk G β)

@[reassoc (attr := simp)]

Depends on / 依赖: RightExtension, RightExtension.mk, isUniversalOfIsRightKanExtension
-/
noncomputable def liftOfIsRightKanExtension (G : D ⥤ H) (β : L ⋙ G ⟶ F) : G ⟶ F' :=
  (F'.isUniversalOfIsRightKanExtension α).lift (RightExtension.mk G β)

@[reassoc (attr := simp)]
/--
lemma `liftOfIsRightKanExtension_fac` / 引理 `liftOfIsRightKanExtension_fac`

English:
lemma liftOfIsRightKanExtension_fac
  given: (G : D ⥤ H) (β : L ⋙ G ⟶ F)
  proof: (F'.isUniversalOfIsRightKanExtension α).fac (RightExtension.mk G β)

@[reassoc (attr := simp)]

中文:
引理 liftOfIsRightKanExtension_fac
  条件: (G : D ⥤ H) (β : L ⋙ G ⟶ F)
  证明: (F'.isUniversalOfIsRightKanExtension α).fac (RightExtension.mk G β)

@[reassoc (attr := simp)]

Depends on / 依赖: RightExtension, RightExtension.mk, isUniversalOfIsRightKanExtension
-/
lemma liftOfIsRightKanExtension_fac (G : D ⥤ H) (β : L ⋙ G ⟶ F) :
    whiskerLeft L (F'.liftOfIsRightKanExtension α G β) ≫ α = β :=
  (F'.isUniversalOfIsRightKanExtension α).fac (RightExtension.mk G β)

@[reassoc (attr := simp)]
/--
lemma `liftOfIsRightKanExtension_fac_app` / 引理 `liftOfIsRightKanExtension_fac_app`

English:
lemma liftOfIsRightKanExtension_fac_app
  given: (G : D ⥤ H) (β : L ⋙ G ⟶ F) (X : C)
  proof: NatTrans.congr_app (F'.liftOfIsRightKanExtension_fac α G β) X

中文:
引理 liftOfIsRightKanExtension_fac_app
  条件: (G : D ⥤ H) (β : L ⋙ G ⟶ F) (X : C)
  证明: NatTrans.congr_app (F'.liftOfIsRightKanExtension_fac α G β) X

Depends on / 依赖: NatTrans, NatTrans.congr_app, congr_app, liftOfIsRightKanExtension_fac
-/
lemma liftOfIsRightKanExtension_fac_app (G : D ⥤ H) (β : L ⋙ G ⟶ F) (X : C) :
    (F'.liftOfIsRightKanExtension α G β).app (L.obj X) ≫ α.app X = β.app X :=
  NatTrans.congr_app (F'.liftOfIsRightKanExtension_fac α G β) X

/--
lemma `hom_ext_of_isRightKanExtension` / 引理 `hom_ext_of_isRightKanExtension`

English:
lemma hom_ext_of_isRightKanExtension
  statement: {G : D ⥤ H} (γ₁ γ₂ : G ⟶ F')
  proof: (F'.isUniversalOfIsRightKanExtension α).hom_ext hγ

中文:
引理 hom_ext_of_isRightKanExtension
  结论: {G : D ⥤ H} (γ₁ γ₂ : G ⟶ F')
  证明: (F'.isUniversalOfIsRightKanExtension α).hom_ext hγ

Depends on / 依赖: hom_ext, isUniversalOfIsRightKanExtension
-/
lemma hom_ext_of_isRightKanExtension {G : D ⥤ H} (γ₁ γ₂ : G ⟶ F')
    (hγ : whiskerLeft L γ₁ ≫ α = whiskerLeft L γ₂ ≫ α) : γ₁ = γ₂ :=
  (F'.isUniversalOfIsRightKanExtension α).hom_ext hγ

/-- If `(F', α)` is a right Kan extension of `F` along `L`, then this
is the induced bijection `(G ⟶ F') ≃ (L ⋙ G ⟶ F)` for all `G`. -/
@[simps!]
/--
Definition of `homEquivOfIsRightKanExtension` / `homEquivOfIsRightKanExtension` 的定义

English:
definition homEquivOfIsRightKanExtension
  signature: (G : D ⥤ H)
  body: whiskerLeft _ β ≫ α
  invFun β := liftOfIsRightKanExtension _ α _ β
  left_inv β := Functor.hom_ext_of_isRightKanExtension _ α _ _ (by simp)
  right_inv := by cat_disch

中文:
定义 homEquivOfIsRightKanExtension
  签名: (G : D ⥤ H)
  定义体: whiskerLeft _ β ≫ α
  invFun β := liftOfIsRightKanExtension _ α _ β
  left_inv β := Functor.hom_ext_of_isRightKanExtension _ α _ _ (by simp)
  right_inv := by cat_disch

Depends on / 依赖: whiskerLeft
-/
noncomputable def homEquivOfIsRightKanExtension (G : D ⥤ H) :
    (G ⟶ F') ≃ (L ⋙ G ⟶ F) where
  toFun β := whiskerLeft _ β ≫ α
  invFun β := liftOfIsRightKanExtension _ α _ β
  left_inv β := Functor.hom_ext_of_isRightKanExtension _ α _ _ (by simp)
  right_inv := by cat_disch

/--
lemma `isRightKanExtension_of_iso` / 引理 `isRightKanExtension_of_iso`

English:
lemma isRightKanExtension_of_iso
  statement: {F' F'' : D ⥤ H} (e : F' ≅ F'') {L : C ⥤ D} {F : C ⥤ H}
  proof: ⟨IsTerminal.ofIso (F'.isUniversalOfIsRightKanExtension α)
    (CostructuredArrow.isoMk e comm)⟩

中文:
引理 isRightKanExtension_of_iso
  结论: {F' F'' : D ⥤ H} (e : F' ≅ F'') {L : C ⥤ D} {F : C ⥤ H}
  证明: ⟨IsTerminal.ofIso (F'.isUniversalOfIsRightKanExtension α)
    (CostructuredArrow.isoMk e comm)⟩

Depends on / 依赖: IsTerminal, IsTerminal.ofIso, isUniversalOfIsRightKanExtension
-/
lemma isRightKanExtension_of_iso {F' F'' : D ⥤ H} (e : F' ≅ F'') {L : C ⥤ D} {F : C ⥤ H}
    (α : L ⋙ F' ⟶ F) (α' : L ⋙ F'' ⟶ F) (comm : whiskerLeft L e.hom ≫ α' = α)
    [F'.IsRightKanExtension α] : F''.IsRightKanExtension α' where
  nonempty_isUniversal := ⟨IsTerminal.ofIso (F'.isUniversalOfIsRightKanExtension α)
    (CostructuredArrow.isoMk e comm)⟩

/--
lemma `isRightKanExtension_iff_of_iso` / 引理 `isRightKanExtension_iff_of_iso`

English:
lemma isRightKanExtension_iff_of_iso
  statement: {F' F'' : D ⥤ H} (e : F' ≅ F'') {L : C ⥤ D} {F : C ⥤ H}
  proof: by
  constructor
  · intro
    exact isRightKanExtension_of_iso e α α' comm
  · intro
    refine isRightKanExtension_of_iso e.symm α' α ?_
    rw [← comm]; rw [← whiskerLeft_comp_assoc]; rw [Iso.symm_hom]; rw [e.inv_hom_id]; rw [whiskerLeft_id']; rw [id_comp]

中文:
引理 isRightKanExtension_iff_of_iso
  结论: {F' F'' : D ⥤ H} (e : F' ≅ F'') {L : C ⥤ D} {F : C ⥤ H}
  证明: by
  constructor
  · intro
    exact isRightKanExtension_of_iso e α α' comm
  · intro
    refine isRightKanExtension_of_iso e.symm α' α ?_
    rw [← comm]; rw [← whiskerLeft_comp_assoc]; rw [Iso.symm_hom]; rw [e.inv_hom_id]; rw [whiskerLeft_id']; rw [id_comp]

Depends on / 依赖: Iso.symm_hom, e.inv_hom_id, e.symm, id_comp, inv_hom_id, isRightKanExtension_of_iso, symm_hom, whiskerLeft_comp_assoc, whiskerLeft_id
-/
lemma isRightKanExtension_iff_of_iso {F' F'' : D ⥤ H} (e : F' ≅ F'') {L : C ⥤ D} {F : C ⥤ H}
    (α : L ⋙ F' ⟶ F) (α' : L ⋙ F'' ⟶ F) (comm : whiskerLeft L e.hom ≫ α' = α) :
    F'.IsRightKanExtension α ↔ F''.IsRightKanExtension α' := by
  constructor
  · intro
    exact isRightKanExtension_of_iso e α α' comm
  · intro
    refine isRightKanExtension_of_iso e.symm α' α ?_
    rw [← comm]; rw [← whiskerLeft_comp_assoc]; rw [Iso.symm_hom]; rw [e.inv_hom_id]; rw [whiskerLeft_id']; rw [id_comp]

/-- Right Kan extensions of isomorphic functors are isomorphic. -/
@[simps]
/--
Definition of `rightKanExtensionUniqueOfIso` / `rightKanExtensionUniqueOfIso` 的定义

English:
definition rightKanExtensionUniqueOfIso
  signature: {G : C ⥤ H} (i : F ≅ G) (G' : D ⥤ H)
  body: liftOfIsRightKanExtension _ β F' (α ≫ i.hom)
  inv := liftOfIsRightKanExtension _ α G' (β ≫ i.inv)
  hom_inv_id := F'.hom_ext_of_isRightKanExtension α _ _ (by simp)
  inv_hom_id := G'.hom_ext_of_isRightKanExtension β _ _ (by simp)

中文:
定义 rightKanExtensionUniqueOfIso
  签名: {G : C ⥤ H} (i : F ≅ G) (G' : D ⥤ H)
  定义体: liftOfIsRightKanExtension _ β F' (α ≫ i.hom)
  inv := liftOfIsRightKanExtension _ α G' (β ≫ i.inv)
  hom_inv_id := F'.hom_ext_of_isRightKanExtension α _ _ (by simp)
  inv_hom_id := G'.hom_ext_of_isRightKanExtension β _ _ (by simp)

Depends on / 依赖: i.hom, liftOfIsRightKanExtension
-/
noncomputable def rightKanExtensionUniqueOfIso {G : C ⥤ H} (i : F ≅ G) (G' : D ⥤ H)
    (β : L ⋙ G' ⟶ G) [G'.IsRightKanExtension β] : F' ≅ G' where
  hom := liftOfIsRightKanExtension _ β F' (α ≫ i.hom)
  inv := liftOfIsRightKanExtension _ α G' (β ≫ i.inv)
  hom_inv_id := F'.hom_ext_of_isRightKanExtension α _ _ (by simp)
  inv_hom_id := G'.hom_ext_of_isRightKanExtension β _ _ (by simp)

/-- Two right Kan extensions are (canonically) isomorphic. -/
@[simps!]
/--
Definition of `rightKanExtensionUnique` / `rightKanExtensionUnique` 的定义

English:
definition rightKanExtensionUnique
  body: rightKanExtensionUniqueOfIso F' α (Iso.refl _) F'' α'

中文:
定义 rightKanExtensionUnique
  定义体: rightKanExtensionUniqueOfIso F' α (Iso.refl _) F'' α'

Depends on / 依赖: Iso.refl, rightKanExtensionUniqueOfIso
-/
noncomputable def rightKanExtensionUnique
    (F'' : D ⥤ H) (α' : L ⋙ F'' ⟶ F) [F''.IsRightKanExtension α'] : F' ≅ F'' :=
  rightKanExtensionUniqueOfIso F' α (Iso.refl _) F'' α'


/--
lemma `isRightKanExtension_iff_isIso` / 引理 `isRightKanExtension_iff_isIso`

English:
lemma isRightKanExtension_iff_isIso
  statement: {F' : D ⥤ H} {F'' : D ⥤ H} (φ : F'' ⟶ F')
  proof: by
  constructor
  · intro
    rw [F'.hom_ext_of_isRightKanExtension α φ (rightKanExtensionUnique _ α' _ α).hom
      (by simp [comm])]
    infer_instance
  · intro
    rw [isRightKanExtension_iff_of_iso (asIso φ) α' α comm]
    infer_instance

中文:
引理 isRightKanExtension_iff_isIso
  结论: {F' : D ⥤ H} {F'' : D ⥤ H} (φ : F'' ⟶ F')
  证明: by
  constructor
  · intro
    rw [F'.hom_ext_of_isRightKanExtension α φ (rightKanExtensionUnique _ α' _ α).hom
      (by simp [comm])]
    infer_instance
  · intro
    rw [isRightKanExtension_iff_of_iso (asIso φ) α' α comm]
    infer_instance

Depends on / 依赖: hom_ext_of_isRightKanExtension, infer_instance, isRightKanExtension_iff_of_iso, rightKanExtensionUnique
-/
lemma isRightKanExtension_iff_isIso {F' : D ⥤ H} {F'' : D ⥤ H} (φ : F'' ⟶ F')
    {L : C ⥤ D} {F : C ⥤ H} (α : L ⋙ F' ⟶ F) (α' : L ⋙ F'' ⟶ F)
    (comm : whiskerLeft L φ ≫ α = α') [F'.IsRightKanExtension α] :
    F''.IsRightKanExtension α' ↔ IsIso φ := by
  constructor
  · intro
    rw [F'.hom_ext_of_isRightKanExtension α φ (rightKanExtensionUnique _ α' _ α).hom
      (by simp [comm])]
    infer_instance
  · intro
    rw [isRightKanExtension_iff_of_iso (asIso φ) α' α comm]
    infer_instance
end

section

variable (F' : D ⥤ H) {L : C ⥤ D} {F : C ⥤ H} (α : F ⟶ L ⋙ F')

/--
Definition of `IsLeftKanExtension` / `IsLeftKanExtension` 的定义

English:
class IsLeftKanExtension
  parameters: : Prop where
  axioms and operations (1):
    - nonempty_isUniversal : Nonempty (LeftExtension.mk F' α).IsUniversal

中文:
类 是LeftKanExtension
  参数: : 命题 where
  公理与运算 (1 个):
    - nonempty_isUniversal : 非空 (LeftExtension.mk F' α).是泛
-/
class IsLeftKanExtension : Prop where
  nonempty_isUniversal : Nonempty (LeftExtension.mk F' α).IsUniversal

variable [F'.IsLeftKanExtension α]

/--
Definition of `isUniversalOfIsLeftKanExtension` / `isUniversalOfIsLeftKanExtension` 的定义

English:
definition isUniversalOfIsLeftKanExtension
  signature: : (LeftExtension.mk F' α).IsUniversal
  body: IsLeftKanExtension.nonempty_isUniversal.some

中文:
定义 isUniversalOfIsLeftKanExtension
  签名: : (LeftExtension.mk F' α).是泛
  定义体: IsLeftKanExtension.nonempty_isUniversal.some

Depends on / 依赖: IsLeftKanExtension, IsLeftKanExtension.nonempty_isUniversal.some, nonempty_isUniversal
-/
noncomputable def isUniversalOfIsLeftKanExtension : (LeftExtension.mk F' α).IsUniversal :=
  IsLeftKanExtension.nonempty_isUniversal.some

/--
Definition of `descOfIsLeftKanExtension` / `descOfIsLeftKanExtension` 的定义

English:
definition descOfIsLeftKanExtension
  signature: (G : D ⥤ H) (β : F ⟶ L ⋙ G)
  body: (F'.isUniversalOfIsLeftKanExtension α).desc (LeftExtension.mk G β)

@[reassoc (attr := simp)]

中文:
定义 descOfIsLeftKanExtension
  签名: (G : D ⥤ H) (β : F ⟶ L ⋙ G)
  定义体: (F'.isUniversalOfIsLeftKanExtension α).desc (LeftExtension.mk G β)

@[reassoc (attr := simp)]

Depends on / 依赖: LeftExtension, LeftExtension.mk, isUniversalOfIsLeftKanExtension
-/
noncomputable def descOfIsLeftKanExtension (G : D ⥤ H) (β : F ⟶ L ⋙ G) : F' ⟶ G :=
  (F'.isUniversalOfIsLeftKanExtension α).desc (LeftExtension.mk G β)

@[reassoc (attr := simp)]
/--
lemma `descOfIsLeftKanExtension_fac` / 引理 `descOfIsLeftKanExtension_fac`

English:
lemma descOfIsLeftKanExtension_fac
  given: (G : D ⥤ H) (β : F ⟶ L ⋙ G)
  proof: (F'.isUniversalOfIsLeftKanExtension α).fac (LeftExtension.mk G β)

@[reassoc (attr := simp)]

中文:
引理 descOfIsLeftKanExtension_fac
  条件: (G : D ⥤ H) (β : F ⟶ L ⋙ G)
  证明: (F'.isUniversalOfIsLeftKanExtension α).fac (LeftExtension.mk G β)

@[reassoc (attr := simp)]

Depends on / 依赖: LeftExtension, LeftExtension.mk, isUniversalOfIsLeftKanExtension
-/
lemma descOfIsLeftKanExtension_fac (G : D ⥤ H) (β : F ⟶ L ⋙ G) :
    α ≫ whiskerLeft L (F'.descOfIsLeftKanExtension α G β) = β :=
  (F'.isUniversalOfIsLeftKanExtension α).fac (LeftExtension.mk G β)

@[reassoc (attr := simp)]
/--
lemma `descOfIsLeftKanExtension_fac_app` / 引理 `descOfIsLeftKanExtension_fac_app`

English:
lemma descOfIsLeftKanExtension_fac_app
  given: (G : D ⥤ H) (β : F ⟶ L ⋙ G) (X : C)
  proof: NatTrans.congr_app (F'.descOfIsLeftKanExtension_fac α G β) X

中文:
引理 descOfIsLeftKanExtension_fac_app
  条件: (G : D ⥤ H) (β : F ⟶ L ⋙ G) (X : C)
  证明: NatTrans.congr_app (F'.descOfIsLeftKanExtension_fac α G β) X

Depends on / 依赖: NatTrans, NatTrans.congr_app, congr_app, descOfIsLeftKanExtension_fac
-/
lemma descOfIsLeftKanExtension_fac_app (G : D ⥤ H) (β : F ⟶ L ⋙ G) (X : C) :
    α.app X ≫ (F'.descOfIsLeftKanExtension α G β).app (L.obj X) = β.app X :=
  NatTrans.congr_app (F'.descOfIsLeftKanExtension_fac α G β) X

/--
lemma `hom_ext_of_isLeftKanExtension` / 引理 `hom_ext_of_isLeftKanExtension`

English:
lemma hom_ext_of_isLeftKanExtension
  statement: {G : D ⥤ H} (γ₁ γ₂ : F' ⟶ G)
  proof: (F'.isUniversalOfIsLeftKanExtension α).hom_ext hγ

中文:
引理 hom_ext_of_isLeftKanExtension
  结论: {G : D ⥤ H} (γ₁ γ₂ : F' ⟶ G)
  证明: (F'.isUniversalOfIsLeftKanExtension α).hom_ext hγ

Depends on / 依赖: hom_ext, isUniversalOfIsLeftKanExtension
-/
lemma hom_ext_of_isLeftKanExtension {G : D ⥤ H} (γ₁ γ₂ : F' ⟶ G)
    (hγ : α ≫ whiskerLeft L γ₁ = α ≫ whiskerLeft L γ₂) : γ₁ = γ₂ :=
  (F'.isUniversalOfIsLeftKanExtension α).hom_ext hγ

/-- If `(F', α)` is a left Kan extension of `F` along `L`, then this
is the induced bijection `(F' ⟶ G) ≃ (F ⟶ L ⋙ G)` for all `G`. -/
@[simps!]
/--
Definition of `homEquivOfIsLeftKanExtension` / `homEquivOfIsLeftKanExtension` 的定义

English:
definition homEquivOfIsLeftKanExtension
  signature: (G : D ⥤ H)
  body: α ≫ whiskerLeft _ β
  invFun β := descOfIsLeftKanExtension _ α _ β
  left_inv β := Functor.hom_ext_of_isLeftKanExtension _ α _ _ (by simp)
  right_inv := by cat_disch

中文:
定义 homEquivOfIsLeftKanExtension
  签名: (G : D ⥤ H)
  定义体: α ≫ whiskerLeft _ β
  invFun β := descOfIsLeftKanExtension _ α _ β
  left_inv β := Functor.hom_ext_of_isLeftKanExtension _ α _ _ (by simp)
  right_inv := by cat_disch

Depends on / 依赖: whiskerLeft
-/
noncomputable def homEquivOfIsLeftKanExtension (G : D ⥤ H) :
    (F' ⟶ G) ≃ (F ⟶ L ⋙ G) where
  toFun β := α ≫ whiskerLeft _ β
  invFun β := descOfIsLeftKanExtension _ α _ β
  left_inv β := Functor.hom_ext_of_isLeftKanExtension _ α _ _ (by simp)
  right_inv := by cat_disch

/--
lemma `isLeftKanExtension_of_iso` / 引理 `isLeftKanExtension_of_iso`

English:
lemma isLeftKanExtension_of_iso
  statement: {F' : D ⥤ H} {F'' : D ⥤ H} (e : F' ≅ F'')
  proof: ⟨IsInitial.ofIso (F'.isUniversalOfIsLeftKanExtension α)
    (StructuredArrow.isoMk e comm)⟩

中文:
引理 isLeftKanExtension_of_iso
  结论: {F' : D ⥤ H} {F'' : D ⥤ H} (e : F' ≅ F'')
  证明: ⟨IsInitial.ofIso (F'.isUniversalOfIsLeftKanExtension α)
    (StructuredArrow.isoMk e comm)⟩

Depends on / 依赖: IsInitial, IsInitial.ofIso, isUniversalOfIsLeftKanExtension
-/
lemma isLeftKanExtension_of_iso {F' : D ⥤ H} {F'' : D ⥤ H} (e : F' ≅ F'')
    {L : C ⥤ D} {F : C ⥤ H} (α : F ⟶ L ⋙ F') (α' : F ⟶ L ⋙ F'')
    (comm : α ≫ whiskerLeft L e.hom = α') [F'.IsLeftKanExtension α] :
    F''.IsLeftKanExtension α' where
  nonempty_isUniversal := ⟨IsInitial.ofIso (F'.isUniversalOfIsLeftKanExtension α)
    (StructuredArrow.isoMk e comm)⟩

/--
lemma `isLeftKanExtension_iff_of_iso` / 引理 `isLeftKanExtension_iff_of_iso`

English:
lemma isLeftKanExtension_iff_of_iso
  statement: {F' F'' : D ⥤ H} (e : F' ≅ F'')
  proof: by
  constructor
  · intro
    exact isLeftKanExtension_of_iso e α α' comm
  · intro
    refine isLeftKanExtension_of_iso e.symm α' α ?_
    rw [← comm]; rw [assoc]; rw [← whiskerLeft_comp]; rw [Iso.symm_hom]; rw [e.hom_inv_id]; rw [whiskerLeft_id']; rw [comp_id]

中文:
引理 isLeftKanExtension_iff_of_iso
  结论: {F' F'' : D ⥤ H} (e : F' ≅ F'')
  证明: by
  constructor
  · intro
    exact isLeftKanExtension_of_iso e α α' comm
  · intro
    refine isLeftKanExtension_of_iso e.symm α' α ?_
    rw [← comm]; rw [assoc]; rw [← whiskerLeft_comp]; rw [Iso.symm_hom]; rw [e.hom_inv_id]; rw [whiskerLeft_id']; rw [comp_id]

Depends on / 依赖: Iso.symm_hom, comp_id, e.hom_inv_id, e.symm, hom_inv_id, isLeftKanExtension_of_iso, symm_hom, whiskerLeft_comp, whiskerLeft_id
-/
lemma isLeftKanExtension_iff_of_iso {F' F'' : D ⥤ H} (e : F' ≅ F'')
    {L : C ⥤ D} {F : C ⥤ H} (α : F ⟶ L ⋙ F') (α' : F ⟶ L ⋙ F'')
    (comm : α ≫ whiskerLeft L e.hom = α') :
    F'.IsLeftKanExtension α ↔ F''.IsLeftKanExtension α' := by
  constructor
  · intro
    exact isLeftKanExtension_of_iso e α α' comm
  · intro
    refine isLeftKanExtension_of_iso e.symm α' α ?_
    rw [← comm]; rw [assoc]; rw [← whiskerLeft_comp]; rw [Iso.symm_hom]; rw [e.hom_inv_id]; rw [whiskerLeft_id']; rw [comp_id]

/-- Left Kan extensions of isomorphic functors are isomorphic. -/
@[simps]
/--
Definition of `leftKanExtensionUniqueOfIso` / `leftKanExtensionUniqueOfIso` 的定义

English:
definition leftKanExtensionUniqueOfIso
  signature: {G : C ⥤ H} (i : F ≅ G) (G' : D ⥤ H)
  body: descOfIsLeftKanExtension _ α G' (i.hom ≫ β)
  inv := descOfIsLeftKanExtension _ β F' (i.inv ≫ α)
  hom_inv_id := F'.hom_ext_of_isLeftKanExtension α _ _ (by simp)
  inv_hom_id := G'.hom_ext_of_isLeftKanExtension β _ _ (by simp)

中文:
定义 leftKanExtensionUniqueOfIso
  签名: {G : C ⥤ H} (i : F ≅ G) (G' : D ⥤ H)
  定义体: descOfIsLeftKanExtension _ α G' (i.hom ≫ β)
  inv := descOfIsLeftKanExtension _ β F' (i.inv ≫ α)
  hom_inv_id := F'.hom_ext_of_isLeftKanExtension α _ _ (by simp)
  inv_hom_id := G'.hom_ext_of_isLeftKanExtension β _ _ (by simp)

Depends on / 依赖: descOfIsLeftKanExtension, i.hom
-/
noncomputable def leftKanExtensionUniqueOfIso {G : C ⥤ H} (i : F ≅ G) (G' : D ⥤ H)
    (β : G ⟶ L ⋙ G') [G'.IsLeftKanExtension β] : F' ≅ G' where
  hom := descOfIsLeftKanExtension _ α G' (i.hom ≫ β)
  inv := descOfIsLeftKanExtension _ β F' (i.inv ≫ α)
  hom_inv_id := F'.hom_ext_of_isLeftKanExtension α _ _ (by simp)
  inv_hom_id := G'.hom_ext_of_isLeftKanExtension β _ _ (by simp)

/-- Two left Kan extensions are (canonically) isomorphic. -/
@[simps!]
/--
Definition of `leftKanExtensionUnique` / `leftKanExtensionUnique` 的定义

English:
definition leftKanExtensionUnique
  body: leftKanExtensionUniqueOfIso F' α (Iso.refl _) F'' α'

中文:
定义 leftKanExtensionUnique
  定义体: leftKanExtensionUniqueOfIso F' α (Iso.refl _) F'' α'

Depends on / 依赖: Iso.refl, leftKanExtensionUniqueOfIso
-/
noncomputable def leftKanExtensionUnique
    (F'' : D ⥤ H) (α' : F ⟶ L ⋙ F'') [F''.IsLeftKanExtension α'] : F' ≅ F'' :=
  leftKanExtensionUniqueOfIso F' α (Iso.refl _) F'' α'

/--
lemma `isLeftKanExtension_iff_isIso` / 引理 `isLeftKanExtension_iff_isIso`

English:
lemma isLeftKanExtension_iff_isIso
  statement: {F' : D ⥤ H} {F'' : D ⥤ H} (φ : F' ⟶ F'')
  proof: by
  constructor
  · intro
    rw [F'.hom_ext_of_isLeftKanExtension α φ (leftKanExtensionUnique _ α _ α').hom
      (by simp [comm])]
    infer_instance
  · intro
    exact isLeftKanExtension_of_iso (asIso φ) α α' comm

中文:
引理 isLeftKanExtension_iff_isIso
  结论: {F' : D ⥤ H} {F'' : D ⥤ H} (φ : F' ⟶ F'')
  证明: by
  constructor
  · intro
    rw [F'.hom_ext_of_isLeftKanExtension α φ (leftKanExtensionUnique _ α _ α').hom
      (by simp [comm])]
    infer_instance
  · intro
    exact isLeftKanExtension_of_iso (asIso φ) α α' comm

Depends on / 依赖: hom_ext_of_isLeftKanExtension, infer_instance, isLeftKanExtension_of_iso, leftKanExtensionUnique
-/
lemma isLeftKanExtension_iff_isIso {F' : D ⥤ H} {F'' : D ⥤ H} (φ : F' ⟶ F'')
    {L : C ⥤ D} {F : C ⥤ H} (α : F ⟶ L ⋙ F') (α' : F ⟶ L ⋙ F'')
    (comm : α ≫ whiskerLeft L φ = α') [F'.IsLeftKanExtension α] :
    F''.IsLeftKanExtension α' ↔ IsIso φ := by
  constructor
  · intro
    rw [F'.hom_ext_of_isLeftKanExtension α φ (leftKanExtensionUnique _ α _ α').hom
      (by simp [comm])]
    infer_instance
  · intro
    exact isLeftKanExtension_of_iso (asIso φ) α α' comm

end

/--
Definition of `HasRightKanExtension` / `HasRightKanExtension` 的定义

English:
abbreviation HasRightKanExtension
  signature: (L : C ⥤ D) (F : C ⥤ H)
  body: HasTerminal (RightExtension L F)

中文:
缩写 HasRightKanExtension
  签名: (L : C ⥤ D) (F : C ⥤ H)
  定义体: HasTerminal (RightExtension L F)

Depends on / 依赖: HasTerminal, RightExtension
-/
abbrev HasRightKanExtension (L : C ⥤ D) (F : C ⥤ H) := HasTerminal (RightExtension L F)

/--
lemma `HasRightKanExtension.mk` / 引理 `HasRightKanExtension.mk`

English:
lemma HasRightKanExtension.mk
  statement: (F' : D ⥤ H) {L : C ⥤ D} {F : C ⥤ H} (α : L ⋙ F' ⟶ F)
  proof: (F'.isUniversalOfIsRightKanExtension α).hasTerminal

中文:
引理 HasRightKanExtension.mk
  结论: (F' : D ⥤ H) {L : C ⥤ D} {F : C ⥤ H} (α : L ⋙ F' ⟶ F)
  证明: (F'.isUniversalOfIsRightKanExtension α).hasTerminal

Depends on / 依赖: hasTerminal, isUniversalOfIsRightKanExtension
-/
lemma HasRightKanExtension.mk (F' : D ⥤ H) {L : C ⥤ D} {F : C ⥤ H} (α : L ⋙ F' ⟶ F)
    [F'.IsRightKanExtension α] : HasRightKanExtension L F :=
  (F'.isUniversalOfIsRightKanExtension α).hasTerminal

/--
Definition of `HasLeftKanExtension` / `HasLeftKanExtension` 的定义

English:
abbreviation HasLeftKanExtension
  signature: (L : C ⥤ D) (F : C ⥤ H)
  body: HasInitial (LeftExtension L F)

中文:
缩写 有LeftKanExtension
  签名: (L : C ⥤ D) (F : C ⥤ H)
  定义体: HasInitial (LeftExtension L F)

Depends on / 依赖: HasInitial, LeftExtension
-/
abbrev HasLeftKanExtension (L : C ⥤ D) (F : C ⥤ H) := HasInitial (LeftExtension L F)

/--
lemma `HasLeftKanExtension.mk` / 引理 `HasLeftKanExtension.mk`

English:
lemma HasLeftKanExtension.mk
  statement: (F' : D ⥤ H) {L : C ⥤ D} {F : C ⥤ H} (α : F ⟶ L ⋙ F')
  proof: (F'.isUniversalOfIsLeftKanExtension α).hasInitial

中文:
引理 有LeftKanExtension.mk
  结论: (F' : D ⥤ H) {L : C ⥤ D} {F : C ⥤ H} (α : F ⟶ L ⋙ F')
  证明: (F'.isUniversalOfIsLeftKanExtension α).hasInitial

Depends on / 依赖: hasInitial, isUniversalOfIsLeftKanExtension
-/
lemma HasLeftKanExtension.mk (F' : D ⥤ H) {L : C ⥤ D} {F : C ⥤ H} (α : F ⟶ L ⋙ F')
    [F'.IsLeftKanExtension α] : HasLeftKanExtension L F :=
  (F'.isUniversalOfIsLeftKanExtension α).hasInitial

section

variable (L : C ⥤ D) (F : C ⥤ H) [HasRightKanExtension L F]

/--
Definition of `rightKanExtension` / `rightKanExtension` 的定义

English:
definition rightKanExtension
  signature: : D ⥤ H
  body: (⊤_ _ : RightExtension L F).left

中文:
定义 rightKanExtension
  签名: : D ⥤ H
  定义体: (⊤_ _ : RightExtension L F).left

Depends on / 依赖: RightExtension
-/
noncomputable def rightKanExtension : D ⥤ H := (⊤_ _ : RightExtension L F).left

/--
Definition of `rightKanExtensionCounit` / `rightKanExtensionCounit` 的定义

English:
definition rightKanExtensionCounit
  signature: : L ⋙ rightKanExtension L F ⟶ F
  body: (⊤_ _ : RightExtension L F).hom

中文:
定义 rightKanExtensionCounit
  签名: : L ⋙ rightKanExtension L F ⟶ F
  定义体: (⊤_ _ : RightExtension L F).hom

Depends on / 依赖: RightExtension
-/
noncomputable def rightKanExtensionCounit : L ⋙ rightKanExtension L F ⟶ F :=
  (⊤_ _ : RightExtension L F).hom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (L.rightKanExtension F).IsRightKanExtension (L.rightKanExtensionCounit F)
  body: ⟨terminalIsTerminal⟩

@[ext]

中文:
实例 :
  签名: (L.rightKanExtension F).是RightKanExtension (L.rightKanExtensionCounit F)
  定义体: ⟨terminalIsTerminal⟩

@[ext]

Depends on / 依赖: terminalIsTerminal
-/
instance : (L.rightKanExtension F).IsRightKanExtension (L.rightKanExtensionCounit F) where
  nonempty_isUniversal := ⟨terminalIsTerminal⟩

@[ext]
/--
lemma `rightKanExtension_hom_ext` / 引理 `rightKanExtension_hom_ext`

English:
lemma rightKanExtension_hom_ext
  statement: {G : D ⥤ H} (γ₁ γ₂ : G ⟶ rightKanExtension L F)
  proof: hom_ext_of_isRightKanExtension _ _ _ _ hγ

中文:
引理 rightKanExtension_hom_ext
  结论: {G : D ⥤ H} (γ₁ γ₂ : G ⟶ rightKanExtension L F)
  证明: hom_ext_of_isRightKanExtension _ _ _ _ hγ

Depends on / 依赖: hom_ext_of_isRightKanExtension
-/
lemma rightKanExtension_hom_ext {G : D ⥤ H} (γ₁ γ₂ : G ⟶ rightKanExtension L F)
    (hγ : whiskerLeft L γ₁ ≫ rightKanExtensionCounit L F =
      whiskerLeft L γ₂ ≫ rightKanExtensionCounit L F) :
    γ₁ = γ₂ :=
  hom_ext_of_isRightKanExtension _ _ _ _ hγ

end

section

variable (L : C ⥤ D) (F : C ⥤ H) [HasLeftKanExtension L F]

/--
Definition of `leftKanExtension` / `leftKanExtension` 的定义

English:
definition leftKanExtension
  signature: : D ⥤ H
  body: (⊥_ _ : LeftExtension L F).right

中文:
定义 leftKanExtension
  签名: : D ⥤ H
  定义体: (⊥_ _ : LeftExtension L F).right

Depends on / 依赖: LeftExtension
-/
noncomputable def leftKanExtension : D ⥤ H := (⊥_ _ : LeftExtension L F).right

/--
Definition of `leftKanExtensionUnit` / `leftKanExtensionUnit` 的定义

English:
definition leftKanExtensionUnit
  signature: : F ⟶ L ⋙ leftKanExtension L F
  body: (⊥_ _ : LeftExtension L F).hom

中文:
定义 leftKanExtensionUnit
  签名: : F ⟶ L ⋙ leftKanExtension L F
  定义体: (⊥_ _ : LeftExtension L F).hom

Depends on / 依赖: LeftExtension
-/
noncomputable def leftKanExtensionUnit : F ⟶ L ⋙ leftKanExtension L F :=
  (⊥_ _ : LeftExtension L F).hom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (L.leftKanExtension F).IsLeftKanExtension (L.leftKanExtensionUnit F)
  body: ⟨initialIsInitial⟩

@[ext]

中文:
实例 :
  签名: (L.leftKanExtension F).是LeftKanExtension (L.leftKanExtensionUnit F)
  定义体: ⟨initialIsInitial⟩

@[ext]

Depends on / 依赖: initialIsInitial
-/
instance : (L.leftKanExtension F).IsLeftKanExtension (L.leftKanExtensionUnit F) where
  nonempty_isUniversal := ⟨initialIsInitial⟩

@[ext]
/--
lemma `leftKanExtension_hom_ext` / 引理 `leftKanExtension_hom_ext`

English:
lemma leftKanExtension_hom_ext
  statement: {G : D ⥤ H} (γ₁ γ₂ : leftKanExtension L F ⟶ G)
  proof: hom_ext_of_isLeftKanExtension _ _ _ _ hγ

中文:
引理 leftKanExtension_hom_ext
  结论: {G : D ⥤ H} (γ₁ γ₂ : leftKanExtension L F ⟶ G)
  证明: hom_ext_of_isLeftKanExtension _ _ _ _ hγ

Depends on / 依赖: hom_ext_of_isLeftKanExtension
-/
lemma leftKanExtension_hom_ext {G : D ⥤ H} (γ₁ γ₂ : leftKanExtension L F ⟶ G)
    (hγ : leftKanExtensionUnit L F ≫ whiskerLeft L γ₁ =
      leftKanExtensionUnit L F ≫ whiskerLeft L γ₂) : γ₁ = γ₂ :=
  hom_ext_of_isLeftKanExtension _ _ _ _ hγ

end

section

variable {L : C ⥤ D} {L' : C ⥤ D'} (G : D ⥤ D')

/-- The functor `LeftExtension L' F ⥤ LeftExtension L F`
induced by a natural transformation `L' ⟶ L ⋙ G'`. -/
@[simps!, implicit_reducible]
/--
Definition of `LeftExtension.postcomp₁` / `LeftExtension.postcomp₁` 的定义

English:
definition LeftExtension.postcomp₁
  signature: (f : L' ⟶ L ⋙ G) (F : C ⥤ H)
  body: StructuredArrow.map₂ (F := (whiskeringLeft D D' H).obj G) (G := 𝟭 _) (𝟙 _)
    ((whiskeringLeft C D' H).map f)

中文:
定义 LeftExtension.postcomp₁
  签名: (f : L' ⟶ L ⋙ G) (F : C ⥤ H)
  定义体: StructuredArrow.map₂ (F := (whiskeringLeft D D' H).obj G) (G := 𝟭 _) (𝟙 _)
    ((whiskeringLeft C D' H).map f)

Depends on / 依赖: StructuredArrow, StructuredArrow.map, whiskeringLeft
-/
def LeftExtension.postcomp₁ (f : L' ⟶ L ⋙ G) (F : C ⥤ H) :
    LeftExtension L' F ⥤ LeftExtension L F :=
  StructuredArrow.map₂ (F := (whiskeringLeft D D' H).obj G) (G := 𝟭 _) (𝟙 _)
    ((whiskeringLeft C D' H).map f)

/-- The functor `RightExtension L' F ⥤ RightExtension L F`
induced by a natural transformation `L ⋙ G ⟶ L'`. -/
@[simps!, implicit_reducible]
/--
Definition of `RightExtension.postcomp₁` / `RightExtension.postcomp₁` 的定义

English:
definition RightExtension.postcomp₁
  signature: (f : L ⋙ G ⟶ L') (F : C ⥤ H)
  body: CostructuredArrow.map₂ (F := (whiskeringLeft D D' H).obj G) (G := 𝟭 _)
    ((whiskeringLeft C D' H).map f) (𝟙 _)

中文:
定义 RightExtension.postcomp₁
  签名: (f : L ⋙ G ⟶ L') (F : C ⥤ H)
  定义体: CostructuredArrow.map₂ (F := (whiskeringLeft D D' H).obj G) (G := 𝟭 _)
    ((whiskeringLeft C D' H).map f) (𝟙 _)

Depends on / 依赖: CostructuredArrow, CostructuredArrow.map, whiskeringLeft
-/
def RightExtension.postcomp₁ (f : L ⋙ G ⟶ L') (F : C ⥤ H) :
    RightExtension L' F ⥤ RightExtension L F :=
  CostructuredArrow.map₂ (F := (whiskeringLeft D D' H).obj G) (G := 𝟭 _)
    ((whiskeringLeft C D' H).map f) (𝟙 _)

variable [IsEquivalence G]

set_option backward.isDefEq.respectTransparency false in
noncomputable instance (f : L' ⟶ L ⋙ G) [IsIso f] (F : C ⥤ H) :
    IsEquivalence (LeftExtension.postcomp₁ G f F) := by
  apply StructuredArrow.isEquivalenceMap₂

set_option backward.isDefEq.respectTransparency false in
noncomputable instance (f : L ⋙ G ⟶ L') [IsIso f] (F : C ⥤ H) :
    IsEquivalence (RightExtension.postcomp₁ G f F) := by
  apply CostructuredArrow.isEquivalenceMap₂

variable {G} in
/--
lemma `hasLeftExtension_iff_postcomp₁` / 引理 `hasLeftExtension_iff_postcomp₁`

English:
lemma hasLeftExtension_iff_postcomp₁
  given: (e : L ⋙ G ≅ L') (F : C ⥤ H)
  proof: (LeftExtension.postcomp₁ G e.inv F).asEquivalence.hasInitial_iff

中文:
引理 hasLeftExtension_iff_postcomp₁
  条件: (e : L ⋙ G ≅ L') (F : C ⥤ H)
  证明: (LeftExtension.postcomp₁ G e.inv F).asEquivalence.hasInitial_iff

Depends on / 依赖: LeftExtension, LeftExtension.postcomp, asEquivalence, asEquivalence.hasInitial_iff, e.inv, hasInitial_iff
-/
lemma hasLeftExtension_iff_postcomp₁ (e : L ⋙ G ≅ L') (F : C ⥤ H) :
    HasLeftKanExtension L' F ↔ HasLeftKanExtension L F :=
  (LeftExtension.postcomp₁ G e.inv F).asEquivalence.hasInitial_iff

variable {G} in
/--
lemma `hasRightExtension_iff_postcomp₁` / 引理 `hasRightExtension_iff_postcomp₁`

English:
lemma hasRightExtension_iff_postcomp₁
  given: (e : L ⋙ G ≅ L') (F : C ⥤ H)
  proof: (RightExtension.postcomp₁ G e.hom F).asEquivalence.hasTerminal_iff

中文:
引理 hasRightExtension_iff_postcomp₁
  条件: (e : L ⋙ G ≅ L') (F : C ⥤ H)
  证明: (RightExtension.postcomp₁ G e.hom F).asEquivalence.hasTerminal_iff

Depends on / 依赖: RightExtension, RightExtension.postcomp, asEquivalence, asEquivalence.hasTerminal_iff, e.hom, hasTerminal_iff
-/
lemma hasRightExtension_iff_postcomp₁ (e : L ⋙ G ≅ L') (F : C ⥤ H) :
    HasRightKanExtension L' F ↔ HasRightKanExtension L F :=
  (RightExtension.postcomp₁ G e.hom F).asEquivalence.hasTerminal_iff

variable (e : L ⋙ G ≅ L') (F : C ⥤ H)

/--
Definition of `LeftExtension.isUniversalPostcomp₁Equiv` / `LeftExtension.isUniversalPostcomp₁Equiv` 的定义

English:
definition LeftExtension.isUniversalPostcomp₁Equiv
  signature: (ex : LeftExtension L' F)
  body: by
  apply IsInitial.isInitialIffObj (LeftExtension.postcomp₁ G e.inv F)

中文:
定义 LeftExtension.isUniversalPostcomp₁Equiv
  签名: (ex : LeftExtension L' F)
  定义体: by
  apply IsInitial.isInitialIffObj (LeftExtension.postcomp₁ G e.inv F)

Depends on / 依赖: IsInitial, IsInitial.isInitialIffObj, LeftExtension, LeftExtension.postcomp, e.inv, isInitialIffObj
-/
noncomputable def LeftExtension.isUniversalPostcomp₁Equiv (ex : LeftExtension L' F) :
    ex.IsUniversal ≃ ((LeftExtension.postcomp₁ G e.inv F).obj ex).IsUniversal := by
  apply IsInitial.isInitialIffObj (LeftExtension.postcomp₁ G e.inv F)

/--
Definition of `RightExtension.isUniversalPostcomp₁Equiv` / `RightExtension.isUniversalPostcomp₁Equiv` 的定义

English:
definition RightExtension.isUniversalPostcomp₁Equiv
  signature: (ex : RightExtension L' F)
  body: by
  apply IsTerminal.isTerminalIffObj (RightExtension.postcomp₁ G e.hom F)

中文:
定义 RightExtension.isUniversalPostcomp₁Equiv
  签名: (ex : RightExtension L' F)
  定义体: by
  apply IsTerminal.isTerminalIffObj (RightExtension.postcomp₁ G e.hom F)

Depends on / 依赖: IsTerminal, IsTerminal.isTerminalIffObj, RightExtension, RightExtension.postcomp, e.hom, isTerminalIffObj
-/
noncomputable def RightExtension.isUniversalPostcomp₁Equiv (ex : RightExtension L' F) :
    ex.IsUniversal ≃ ((RightExtension.postcomp₁ G e.hom F).obj ex).IsUniversal := by
  apply IsTerminal.isTerminalIffObj (RightExtension.postcomp₁ G e.hom F)

variable {F F'}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `isLeftKanExtension_iff_postcomp₁` / 引理 `isLeftKanExtension_iff_postcomp₁`

English:
lemma isLeftKanExtension_iff_postcomp₁
  given: (α : F ⟶ L' ⋙ F')
  proof: by
  let eq : (LeftExtension.mk _ α).IsUniversal ≃
      (LeftExtension.mk _
        (α ≫ whiskerRight e.inv _ ≫ (associator _ _ _).hom)).IsUniversal :=
    (LeftExtension.isUniversalPostcomp₁Equiv G e F _).trans
    (IsInitial.equivOfIso (StructuredArrow.isoMk (Iso.refl _)))
  constructor
  · exact

中文:
引理 isLeftKanExtension_iff_postcomp₁
  条件: (α : F ⟶ L' ⋙ F')
  证明: by
  let eq : (LeftExtension.mk _ α).IsUniversal ≃
      (LeftExtension.mk _
        (α ≫ whiskerRight e.inv _ ≫ (associator _ _ _).hom)).IsUniversal :=
    (LeftExtension.isUniversalPostcomp₁Equiv G e F _).trans
    (IsInitial.equivOfIso (StructuredArrow.isoMk (Iso.refl _)))
  constructor
  · exact

Depends on / 依赖: IsInitial, IsInitial.equivOfIso, IsUniversal, Iso.refl, LeftExtension, LeftExtension.isUniversalPostcomp, LeftExtension.mk, StructuredArrow, StructuredArrow.isoMk, associator, e.inv, eq.symm, equivOfIso, isUniversalOfIsLeftKanExtension, whiskerRight
-/
lemma isLeftKanExtension_iff_postcomp₁ (α : F ⟶ L' ⋙ F') :
    F'.IsLeftKanExtension α ↔ (G ⋙ F').IsLeftKanExtension
      (α ≫ whiskerRight e.inv _ ≫ (associator _ _ _).hom) := by
  let eq : (LeftExtension.mk _ α).IsUniversal ≃
      (LeftExtension.mk _
        (α ≫ whiskerRight e.inv _ ≫ (associator _ _ _).hom)).IsUniversal :=
    (LeftExtension.isUniversalPostcomp₁Equiv G e F _).trans
    (IsInitial.equivOfIso (StructuredArrow.isoMk (Iso.refl _)))
  constructor
  · exact fun _ => ⟨⟨eq (isUniversalOfIsLeftKanExtension _ _)⟩⟩
  · exact fun _ => ⟨⟨eq.symm (isUniversalOfIsLeftKanExtension _ _)⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `isRightKanExtension_iff_postcomp₁` / 引理 `isRightKanExtension_iff_postcomp₁`

English:
lemma isRightKanExtension_iff_postcomp₁
  given: (α : L' ⋙ F' ⟶ F)
  proof: by
  let eq : (RightExtension.mk _ α).IsUniversal ≃
    (RightExtension.mk _
      ((associator _ _ _).inv ≫ whiskerRight e.hom F' ≫ α)).IsUniversal :=
  (RightExtension.isUniversalPostcomp₁Equiv G e F _).trans
    (IsTerminal.equivOfIso (CostructuredArrow.isoMk (Iso.refl _)))
  constructor
  · exac

中文:
引理 isRightKanExtension_iff_postcomp₁
  条件: (α : L' ⋙ F' ⟶ F)
  证明: by
  let eq : (RightExtension.mk _ α).IsUniversal ≃
    (RightExtension.mk _
      ((associator _ _ _).inv ≫ whiskerRight e.hom F' ≫ α)).IsUniversal :=
  (RightExtension.isUniversalPostcomp₁Equiv G e F _).trans
    (IsTerminal.equivOfIso (CostructuredArrow.isoMk (Iso.refl _)))
  constructor
  · exac

Depends on / 依赖: CostructuredArrow, CostructuredArrow.isoMk, IsTerminal, IsTerminal.equivOfIso, IsUniversal, Iso.refl, RightExtension, RightExtension.isUniversalPostcomp, RightExtension.mk, associator, e.hom, eq.symm, equivOfIso, isUniversalOfIsRightKanExtension, whiskerRight
-/
lemma isRightKanExtension_iff_postcomp₁ (α : L' ⋙ F' ⟶ F) :
    F'.IsRightKanExtension α ↔ (G ⋙ F').IsRightKanExtension
      ((associator _ _ _).inv ≫ whiskerRight e.hom F' ≫ α) := by
  let eq : (RightExtension.mk _ α).IsUniversal ≃
    (RightExtension.mk _
      ((associator _ _ _).inv ≫ whiskerRight e.hom F' ≫ α)).IsUniversal :=
  (RightExtension.isUniversalPostcomp₁Equiv G e F _).trans
    (IsTerminal.equivOfIso (CostructuredArrow.isoMk (Iso.refl _)))
  constructor
  · exact fun _ => ⟨⟨eq (isUniversalOfIsRightKanExtension _ _)⟩⟩
  · exact fun _ => ⟨⟨eq.symm (isUniversalOfIsRightKanExtension _ _)⟩⟩

end

section

variable (L : C ⥤ D) (F : C ⥤ H) (G : H ⥤ D')

set_option backward.defeqAttrib.useBackward true in
/-- Given a left extension `E` of `F : C ⥤ H` along `L : C ⥤ D` and a functor `G : H ⥤ D'`,
`E.postcompose₂ G` is the extension of `F ⋙ G` along `L` obtained by whiskering by `G`
on the right. -/
@[simps!, implicit_reducible]
/--
Definition of `LeftExtension.postcompose₂` / `LeftExtension.postcompose₂` 的定义

English:
definition LeftExtension.postcompose₂
  signature: : LeftExtension L F ⥤ LeftExtension L (F ⋙ G)
  body: StructuredArrow.map₂
    (F := (whiskeringRight _ _ _).obj G)
    (G := (whiskeringRight _ _ _).obj G)
    (𝟙 _) ({ app _ := (associator _ _ _).hom })

中文:
定义 LeftExtension.postcompose₂
  签名: : LeftExtension L F ⥤ LeftExtension L (F ⋙ G)
  定义体: StructuredArrow.map₂
    (F := (whiskeringRight _ _ _).obj G)
    (G := (whiskeringRight _ _ _).obj G)
    (𝟙 _) ({ app _ := (associator _ _ _).hom })

Depends on / 依赖: StructuredArrow, StructuredArrow.map, associator, whiskeringRight
-/
def LeftExtension.postcompose₂ : LeftExtension L F ⥤ LeftExtension L (F ⋙ G) :=
  StructuredArrow.map₂
    (F := (whiskeringRight _ _ _).obj G)
    (G := (whiskeringRight _ _ _).obj G)
    (𝟙 _) ({ app _ := (associator _ _ _).hom })

set_option backward.defeqAttrib.useBackward true in
/-- Given a right extension `E` of `F : C ⥤ H` along `L : C ⥤ D` and a functor `G : H ⥤ D'`,
`E.postcompose₂ G` is the extension of `F ⋙ G` along `L` obtained by whiskering by `G`
on the right. -/
@[simps!, implicit_reducible]
/--
Definition of `RightExtension.postcompose₂` / `RightExtension.postcompose₂` 的定义

English:
definition RightExtension.postcompose₂
  signature: : RightExtension L F ⥤ RightExtension L (F ⋙ G)
  body: CostructuredArrow.map₂
    (F := (whiskeringRight _ _ _).obj G)
    (G := (whiskeringRight _ _ _).obj G)
    ({ app _ := associator _ _ _ |>.inv }) (𝟙 _)

中文:
定义 RightExtension.postcompose₂
  签名: : RightExtension L F ⥤ RightExtension L (F ⋙ G)
  定义体: CostructuredArrow.map₂
    (F := (whiskeringRight _ _ _).obj G)
    (G := (whiskeringRight _ _ _).obj G)
    ({ app _ := associator _ _ _ |>.inv }) (𝟙 _)

Depends on / 依赖: CostructuredArrow, CostructuredArrow.map, associator, whiskeringRight
-/
def RightExtension.postcompose₂ : RightExtension L F ⥤ RightExtension L (F ⋙ G) :=
  CostructuredArrow.map₂
    (F := (whiskeringRight _ _ _).obj G)
    (G := (whiskeringRight _ _ _).obj G)
    ({ app _ := associator _ _ _ |>.inv }) (𝟙 _)

variable {L F} {F' : D ⥤ H}
set_option backward.isDefEq.respectTransparency.types false in
/-- An isomorphism to describe the action of `LeftExtension.postcompose₂` on terms of the form
`LeftExtension.mk _ α`. -/
@[simps!]
/--
Definition of `LeftExtension.postcompose₂ObjMkIso` / `LeftExtension.postcompose₂ObjMkIso` 的定义

English:
definition LeftExtension.postcompose₂ObjMkIso
  signature: (α : F ⟶ L ⋙ F')
  body: StructuredArrow.isoMk (.refl _)

中文:
定义 LeftExtension.postcompose₂ObjMkIso
  签名: (α : F ⟶ L ⋙ F')
  定义体: StructuredArrow.isoMk (.refl _)

Depends on / 依赖: StructuredArrow, StructuredArrow.isoMk
-/
def LeftExtension.postcompose₂ObjMkIso (α : F ⟶ L ⋙ F') :
    (LeftExtension.postcompose₂ L F G).obj (.mk F' α) ≅
.mk (F' ⋙ G) whiskerRight α G ≫ (associator _ _ _).hom :=
  StructuredArrow.isoMk (.refl _)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- An isomorphism to describe the action of `RightExtension.postcompose₂` on terms of the form
`RightExtension.mk _ α`. -/
@[simps!]
/--
Definition of `RightExtension.postcompose₂ObjMkIso` / `RightExtension.postcompose₂ObjMkIso` 的定义

English:
definition RightExtension.postcompose₂ObjMkIso
  signature: (α : L ⋙ F' ⟶ F)
  body: CostructuredArrow.isoMk (.refl _)

中文:
定义 RightExtension.postcompose₂ObjMkIso
  签名: (α : L ⋙ F' ⟶ F)
  定义体: CostructuredArrow.isoMk (.refl _)

Depends on / 依赖: CostructuredArrow, CostructuredArrow.isoMk
-/
def RightExtension.postcompose₂ObjMkIso (α : L ⋙ F' ⟶ F) :
    (RightExtension.postcompose₂ L F G).obj (.mk F' α) ≅
.mk (F' ⋙ G) (associator _ _ _).inv ≫ whiskerRight α G :=
  CostructuredArrow.isoMk (.refl _)

end

section

variable (L : C ⥤ D) (F : C ⥤ H) (F' : D ⥤ H) (G : C' ⥤ C)

/-- The functor `LeftExtension L F ⥤ LeftExtension (G ⋙ L) (G ⋙ F)`
obtained by precomposition. -/
@[simps!, implicit_reducible]
/--
Definition of `LeftExtension.precomp` / `LeftExtension.precomp` 的定义

English:
definition LeftExtension.precomp
  signature: : LeftExtension L F ⥤ LeftExtension (G ⋙ L) (G ⋙ F)
  body: StructuredArrow.map₂ (F := 𝟭 _) (G := (whiskeringLeft C' C H).obj G) (𝟙 _) (𝟙 _)

中文:
定义 LeftExtension.precomp
  签名: : LeftExtension L F ⥤ LeftExtension (G ⋙ L) (G ⋙ F)
  定义体: StructuredArrow.map₂ (F := 𝟭 _) (G := (whiskeringLeft C' C H).obj G) (𝟙 _) (𝟙 _)

Depends on / 依赖: StructuredArrow, StructuredArrow.map, whiskeringLeft
-/
def LeftExtension.precomp : LeftExtension L F ⥤ LeftExtension (G ⋙ L) (G ⋙ F) :=
  StructuredArrow.map₂ (F := 𝟭 _) (G := (whiskeringLeft C' C H).obj G) (𝟙 _) (𝟙 _)

/-- The functor `RightExtension L F ⥤ RightExtension (G ⋙ L) (G ⋙ F)`
obtained by precomposition. -/
@[simps!, implicit_reducible]
/--
Definition of `RightExtension.precomp` / `RightExtension.precomp` 的定义

English:
definition RightExtension.precomp
  signature: : RightExtension L F ⥤ RightExtension (G ⋙ L) (G ⋙ F)
  body: CostructuredArrow.map₂ (F := 𝟭 _) (G := (whiskeringLeft C' C H).obj G) (𝟙 _) (𝟙 _)

中文:
定义 RightExtension.precomp
  签名: : RightExtension L F ⥤ RightExtension (G ⋙ L) (G ⋙ F)
  定义体: CostructuredArrow.map₂ (F := 𝟭 _) (G := (whiskeringLeft C' C H).obj G) (𝟙 _) (𝟙 _)

Depends on / 依赖: CostructuredArrow, CostructuredArrow.map, whiskeringLeft
-/
def RightExtension.precomp : RightExtension L F ⥤ RightExtension (G ⋙ L) (G ⋙ F) :=
  CostructuredArrow.map₂ (F := 𝟭 _) (G := (whiskeringLeft C' C H).obj G) (𝟙 _) (𝟙 _)

variable [IsEquivalence G]

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsEquivalence (LeftExtension.precomp L F G)
  body: by
  apply StructuredArrow.isEquivalenceMap₂

中文:
实例 :
  签名: 是等价 (LeftExtension.precomp L F G)
  定义体: by
  apply StructuredArrow.isEquivalenceMap₂

Depends on / 依赖: StructuredArrow, StructuredArrow.isEquivalenceMap
-/
noncomputable instance : IsEquivalence (LeftExtension.precomp L F G) := by
  apply StructuredArrow.isEquivalenceMap₂

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsEquivalence (RightExtension.precomp L F G)
  body: by
  apply CostructuredArrow.isEquivalenceMap₂

中文:
实例 :
  签名: 是等价 (RightExtension.precomp L F G)
  定义体: by
  apply CostructuredArrow.isEquivalenceMap₂

Depends on / 依赖: CostructuredArrow, CostructuredArrow.isEquivalenceMap
-/
noncomputable instance : IsEquivalence (RightExtension.precomp L F G) := by
  apply CostructuredArrow.isEquivalenceMap₂

/--
Definition of `LeftExtension.isUniversalPrecompEquiv` / `LeftExtension.isUniversalPrecompEquiv` 的定义

English:
definition LeftExtension.isUniversalPrecompEquiv
  signature: (e : LeftExtension L F)
  body: by
  apply IsInitial.isInitialIffObj (LeftExtension.precomp L F G)

中文:
定义 LeftExtension.isUniversalPrecompEquiv
  签名: (e : LeftExtension L F)
  定义体: by
  apply IsInitial.isInitialIffObj (LeftExtension.precomp L F G)

Depends on / 依赖: IsInitial, IsInitial.isInitialIffObj, LeftExtension, LeftExtension.precomp, isInitialIffObj, precomp
-/
noncomputable def LeftExtension.isUniversalPrecompEquiv (e : LeftExtension L F) :
    e.IsUniversal ≃ ((LeftExtension.precomp L F G).obj e).IsUniversal := by
  apply IsInitial.isInitialIffObj (LeftExtension.precomp L F G)

/--
Definition of `RightExtension.isUniversalPrecompEquiv` / `RightExtension.isUniversalPrecompEquiv` 的定义

English:
definition RightExtension.isUniversalPrecompEquiv
  signature: (e : RightExtension L F)
  body: by
  apply IsTerminal.isTerminalIffObj (RightExtension.precomp L F G)

中文:
定义 RightExtension.isUniversalPrecompEquiv
  签名: (e : RightExtension L F)
  定义体: by
  apply IsTerminal.isTerminalIffObj (RightExtension.precomp L F G)

Depends on / 依赖: IsTerminal, IsTerminal.isTerminalIffObj, RightExtension, RightExtension.precomp, isTerminalIffObj, precomp
-/
noncomputable def RightExtension.isUniversalPrecompEquiv (e : RightExtension L F) :
    e.IsUniversal ≃ ((RightExtension.precomp L F G).obj e).IsUniversal := by
  apply IsTerminal.isTerminalIffObj (RightExtension.precomp L F G)

variable {F L}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `isLeftKanExtension_iff_precomp` / 引理 `isLeftKanExtension_iff_precomp`

English:
lemma isLeftKanExtension_iff_precomp
  given: (α : F ⟶ L ⋙ F')
  proof: by
  let eq : (LeftExtension.mk _ α).IsUniversal ≃ (LeftExtension.mk _
      (whiskerLeft G α ≫ (associator _ _ _).inv)).IsUniversal :=
    (LeftExtension.isUniversalPrecompEquiv L F G _).trans
    (IsInitial.equivOfIso (StructuredArrow.isoMk (Iso.refl _)))
  constructor
  · exact fun _ => ⟨⟨eq (isU

中文:
引理 isLeftKanExtension_iff_precomp
  条件: (α : F ⟶ L ⋙ F')
  证明: by
  let eq : (LeftExtension.mk _ α).IsUniversal ≃ (LeftExtension.mk _
      (whiskerLeft G α ≫ (associator _ _ _).inv)).IsUniversal :=
    (LeftExtension.isUniversalPrecompEquiv L F G _).trans
    (IsInitial.equivOfIso (StructuredArrow.isoMk (Iso.refl _)))
  constructor
  · exact fun _ => ⟨⟨eq (isU

Depends on / 依赖: IsInitial, IsInitial.equivOfIso, IsUniversal, Iso.refl, LeftExtension, LeftExtension.isUniversalPrecompEquiv, LeftExtension.mk, StructuredArrow, StructuredArrow.isoMk, associator, eq.symm, equivOfIso, isUniversalOfIsLeftKanExtension, isUniversalPrecompEquiv, whiskerLeft
-/
lemma isLeftKanExtension_iff_precomp (α : F ⟶ L ⋙ F') :
    F'.IsLeftKanExtension α ↔ F'.IsLeftKanExtension
      (whiskerLeft G α ≫ (associator _ _ _).inv) := by
  let eq : (LeftExtension.mk _ α).IsUniversal ≃ (LeftExtension.mk _
      (whiskerLeft G α ≫ (associator _ _ _).inv)).IsUniversal :=
    (LeftExtension.isUniversalPrecompEquiv L F G _).trans
    (IsInitial.equivOfIso (StructuredArrow.isoMk (Iso.refl _)))
  constructor
  · exact fun _ => ⟨⟨eq (isUniversalOfIsLeftKanExtension _ _)⟩⟩
  · exact fun _ => ⟨⟨eq.symm (isUniversalOfIsLeftKanExtension _ _)⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `isRightKanExtension_iff_precomp` / 引理 `isRightKanExtension_iff_precomp`

English:
lemma isRightKanExtension_iff_precomp
  given: (α : L ⋙ F' ⟶ F)
  proof: by
  let eq : (RightExtension.mk _ α).IsUniversal ≃ (RightExtension.mk _
      ((associator _ _ _).hom ≫ whiskerLeft G α)).IsUniversal :=
    (RightExtension.isUniversalPrecompEquiv L F G _).trans
    (IsTerminal.equivOfIso (CostructuredArrow.isoMk (Iso.refl _)))
  constructor
  · exact fun _ => ⟨⟨e

中文:
引理 isRightKanExtension_iff_precomp
  条件: (α : L ⋙ F' ⟶ F)
  证明: by
  let eq : (RightExtension.mk _ α).IsUniversal ≃ (RightExtension.mk _
      ((associator _ _ _).hom ≫ whiskerLeft G α)).IsUniversal :=
    (RightExtension.isUniversalPrecompEquiv L F G _).trans
    (IsTerminal.equivOfIso (CostructuredArrow.isoMk (Iso.refl _)))
  constructor
  · exact fun _ => ⟨⟨e

Depends on / 依赖: CostructuredArrow, CostructuredArrow.isoMk, IsTerminal, IsTerminal.equivOfIso, IsUniversal, Iso.refl, RightExtension, RightExtension.isUniversalPrecompEquiv, RightExtension.mk, associator, eq.symm, equivOfIso, isUniversalOfIsRightKanExtension, isUniversalPrecompEquiv, whiskerLeft
-/
lemma isRightKanExtension_iff_precomp (α : L ⋙ F' ⟶ F) :
    F'.IsRightKanExtension α ↔
      F'.IsRightKanExtension ((associator _ _ _).hom ≫ whiskerLeft G α) := by
  let eq : (RightExtension.mk _ α).IsUniversal ≃ (RightExtension.mk _
      ((associator _ _ _).hom ≫ whiskerLeft G α)).IsUniversal :=
    (RightExtension.isUniversalPrecompEquiv L F G _).trans
    (IsTerminal.equivOfIso (CostructuredArrow.isoMk (Iso.refl _)))
  constructor
  · exact fun _ => ⟨⟨eq (isUniversalOfIsRightKanExtension _ _)⟩⟩
  · exact fun _ => ⟨⟨eq.symm (isUniversalOfIsRightKanExtension _ _)⟩⟩

end

section

variable {L L' : C ⥤ D} (iso₁ : L ≅ L') (F : C ⥤ H)

-- TODO: Should this be `@[simps!]` too?
/--
Definition of `rightExtensionEquivalenceOfIso₁` / `rightExtensionEquivalenceOfIso₁` 的定义

English:
definition rightExtensionEquivalenceOfIso₁
  signature: : RightExtension L F ≌ RightExtension L' F
  body: CostructuredArrow.mapNatIso ((whiskeringLeft C D H).mapIso iso₁)

include iso₁ in

中文:
定义 rightExtensionEquivalenceOfIso₁
  签名: : RightExtension L F ≌ RightExtension L' F
  定义体: CostructuredArrow.mapNatIso ((whiskeringLeft C D H).mapIso iso₁)

include iso₁ in

Depends on / 依赖: CostructuredArrow, CostructuredArrow.mapNatIso, mapIso, mapNatIso, whiskeringLeft
-/
def rightExtensionEquivalenceOfIso₁ : RightExtension L F ≌ RightExtension L' F :=
  CostructuredArrow.mapNatIso ((whiskeringLeft C D H).mapIso iso₁)

include iso₁ in
/--
lemma `hasRightExtension_iff_of_iso₁` / 引理 `hasRightExtension_iff_of_iso₁`

English:
lemma hasRightExtension_iff_of_iso₁
  statement: HasRightKanExtension L F ↔ HasRightKanExtension L' F
  proof: (rightExtensionEquivalenceOfIso₁ iso₁ F).hasTerminal_iff

#adaptation_note

中文:
引理 hasRightExtension_iff_of_iso₁
  结论: HasRightKanExtension L F ↔ HasRightKanExtension L' F
  证明: (rightExtensionEquivalenceOfIso₁ iso₁ F).hasTerminal_iff

#adaptation_note

Depends on / 依赖: hasTerminal_iff
-/
lemma hasRightExtension_iff_of_iso₁ : HasRightKanExtension L F ↔ HasRightKanExtension L' F :=
  (rightExtensionEquivalenceOfIso₁ iso₁ F).hasTerminal_iff

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The equivalence `LeftExtension L F ≌ LeftExtension L' F` induced by
a natural isomorphism `L ≅ L'`. -/
@[simps!, implicit_reducible]
/--
Definition of `leftExtensionEquivalenceOfIso₁` / `leftExtensionEquivalenceOfIso₁` 的定义

English:
definition leftExtensionEquivalenceOfIso₁
  signature: : LeftExtension L F ≌ LeftExtension L' F
  body: StructuredArrow.mapNatIso ((whiskeringLeft C D H).mapIso iso₁)

include iso₁ in

中文:
定义 leftExtensionEquivalenceOfIso₁
  签名: : LeftExtension L F ≌ LeftExtension L' F
  定义体: StructuredArrow.mapNatIso ((whiskeringLeft C D H).mapIso iso₁)

include iso₁ in

Depends on / 依赖: StructuredArrow, StructuredArrow.mapNatIso, mapIso, mapNatIso, whiskeringLeft
-/
def leftExtensionEquivalenceOfIso₁ : LeftExtension L F ≌ LeftExtension L' F :=
  StructuredArrow.mapNatIso ((whiskeringLeft C D H).mapIso iso₁)

include iso₁ in
/--
lemma `hasLeftExtension_iff_of_iso₁` / 引理 `hasLeftExtension_iff_of_iso₁`

English:
lemma hasLeftExtension_iff_of_iso₁
  statement: HasLeftKanExtension L F ↔ HasLeftKanExtension L' F
  proof: (leftExtensionEquivalenceOfIso₁ iso₁ F).hasInitial_iff

中文:
引理 hasLeftExtension_iff_of_iso₁
  结论: 有LeftKanExtension L F ↔ 有LeftKanExtension L' F
  证明: (leftExtensionEquivalenceOfIso₁ iso₁ F).hasInitial_iff

Depends on / 依赖: hasInitial_iff
-/
lemma hasLeftExtension_iff_of_iso₁ : HasLeftKanExtension L F ↔ HasLeftKanExtension L' F :=
  (leftExtensionEquivalenceOfIso₁ iso₁ F).hasInitial_iff

end

section

variable (L : C ⥤ D) {F F' : C ⥤ H} (iso₂ : F ≅ F')

/--
Definition of `rightExtensionEquivalenceOfIso₂` / `rightExtensionEquivalenceOfIso₂` 的定义

English:
definition rightExtensionEquivalenceOfIso₂
  signature: : RightExtension L F ≌ RightExtension L F'
  body: CostructuredArrow.mapIso iso₂

include iso₂ in

中文:
定义 rightExtensionEquivalenceOfIso₂
  签名: : RightExtension L F ≌ RightExtension L F'
  定义体: CostructuredArrow.mapIso iso₂

include iso₂ in

Depends on / 依赖: CostructuredArrow, CostructuredArrow.mapIso, mapIso
-/
def rightExtensionEquivalenceOfIso₂ : RightExtension L F ≌ RightExtension L F' :=
  CostructuredArrow.mapIso iso₂

include iso₂ in
/--
lemma `hasRightExtension_iff_of_iso₂` / 引理 `hasRightExtension_iff_of_iso₂`

English:
lemma hasRightExtension_iff_of_iso₂
  statement: HasRightKanExtension L F ↔ HasRightKanExtension L F'
  proof: (rightExtensionEquivalenceOfIso₂ L iso₂).hasTerminal_iff

中文:
引理 hasRightExtension_iff_of_iso₂
  结论: HasRightKanExtension L F ↔ HasRightKanExtension L F'
  证明: (rightExtensionEquivalenceOfIso₂ L iso₂).hasTerminal_iff

Depends on / 依赖: hasTerminal_iff
-/
lemma hasRightExtension_iff_of_iso₂ : HasRightKanExtension L F ↔ HasRightKanExtension L F' :=
  (rightExtensionEquivalenceOfIso₂ L iso₂).hasTerminal_iff

/--
Definition of `leftExtensionEquivalenceOfIso₂` / `leftExtensionEquivalenceOfIso₂` 的定义

English:
definition leftExtensionEquivalenceOfIso₂
  signature: : LeftExtension L F ≌ LeftExtension L F'
  body: StructuredArrow.mapIso iso₂

include iso₂ in

中文:
定义 leftExtensionEquivalenceOfIso₂
  签名: : LeftExtension L F ≌ LeftExtension L F'
  定义体: StructuredArrow.mapIso iso₂

include iso₂ in

Depends on / 依赖: StructuredArrow, StructuredArrow.mapIso, mapIso
-/
def leftExtensionEquivalenceOfIso₂ : LeftExtension L F ≌ LeftExtension L F' :=
  StructuredArrow.mapIso iso₂

include iso₂ in
/--
lemma `hasLeftExtension_iff_of_iso₂` / 引理 `hasLeftExtension_iff_of_iso₂`

English:
lemma hasLeftExtension_iff_of_iso₂
  statement: HasLeftKanExtension L F ↔ HasLeftKanExtension L F'
  proof: (leftExtensionEquivalenceOfIso₂ L iso₂).hasInitial_iff

中文:
引理 hasLeftExtension_iff_of_iso₂
  结论: 有LeftKanExtension L F ↔ 有LeftKanExtension L F'
  证明: (leftExtensionEquivalenceOfIso₂ L iso₂).hasInitial_iff

Depends on / 依赖: hasInitial_iff
-/
lemma hasLeftExtension_iff_of_iso₂ : HasLeftKanExtension L F ↔ HasLeftKanExtension L F' :=
  (leftExtensionEquivalenceOfIso₂ L iso₂).hasInitial_iff

end

section

variable {L : C ⥤ D} {F₁ F₂ : C ⥤ H}

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `LeftExtension.isUniversalEquivOfIso₂` / `LeftExtension.isUniversalEquivOfIso₂` 的定义

English:
definition LeftExtension.isUniversalEquivOfIso₂
  body: (IsInitial.isInitialIffObj (leftExtensionEquivalenceOfIso₂ L e).functor α₁).trans
    (IsInitial.equivOfIso (StructuredArrow.isoMk e'
      (by simp [leftExtensionEquivalenceOfIso₂, h])))

中文:
定义 LeftExtension.isUniversalEquivOfIso₂
  定义体: (IsInitial.isInitialIffObj (leftExtensionEquivalenceOfIso₂ L e).functor α₁).trans
    (IsInitial.equivOfIso (StructuredArrow.isoMk e'
      (by simp [leftExtensionEquivalenceOfIso₂, h])))

Depends on / 依赖: IsInitial, IsInitial.equivOfIso, IsInitial.isInitialIffObj, StructuredArrow, StructuredArrow.isoMk, equivOfIso, functor, isInitialIffObj
-/
noncomputable def LeftExtension.isUniversalEquivOfIso₂
    (α₁ : LeftExtension L F₁) (α₂ : LeftExtension L F₂) (e : F₁ ≅ F₂)
    (e' : α₁.right ≅ α₂.right)
    (h : α₁.hom ≫ whiskerLeft L e'.hom = e.hom ≫ α₂.hom) :
    α₁.IsUniversal ≃ α₂.IsUniversal :=
  (IsInitial.isInitialIffObj (leftExtensionEquivalenceOfIso₂ L e).functor α₁).trans
    (IsInitial.equivOfIso (StructuredArrow.isoMk e'
      (by simp [leftExtensionEquivalenceOfIso₂, h])))

/--
lemma `isLeftKanExtension_iff_of_iso₂` / 引理 `isLeftKanExtension_iff_of_iso₂`

English:
lemma isLeftKanExtension_iff_of_iso₂
  statement: {F₁' F₂' : D ⥤ H} (α₁ : F₁ ⟶ L ⋙ F₁') (α₂ : F₂ ⟶ L ⋙ F₂')
  proof: by
  let eq := LeftExtension.isUniversalEquivOfIso₂ (LeftExtension.mk _ α₁)
    (LeftExtension.mk _ α₂) e e' h
  constructor
  · exact fun _ => ⟨⟨eq.1 (isUniversalOfIsLeftKanExtension F₁' α₁)⟩⟩
  · exact fun _ => ⟨⟨eq.2 (isUniversalOfIsLeftKanExtension F₂' α₂)⟩⟩

中文:
引理 isLeftKanExtension_iff_of_iso₂
  结论: {F₁' F₂' : D ⥤ H} (α₁ : F₁ ⟶ L ⋙ F₁') (α₂ : F₂ ⟶ L ⋙ F₂')
  证明: by
  let eq := LeftExtension.isUniversalEquivOfIso₂ (LeftExtension.mk _ α₁)
    (LeftExtension.mk _ α₂) e e' h
  constructor
  · exact fun _ => ⟨⟨eq.1 (isUniversalOfIsLeftKanExtension F₁' α₁)⟩⟩
  · exact fun _ => ⟨⟨eq.2 (isUniversalOfIsLeftKanExtension F₂' α₂)⟩⟩

Depends on / 依赖: LeftExtension, LeftExtension.isUniversalEquivOfIso, LeftExtension.mk, isUniversalOfIsLeftKanExtension
-/
lemma isLeftKanExtension_iff_of_iso₂ {F₁' F₂' : D ⥤ H} (α₁ : F₁ ⟶ L ⋙ F₁') (α₂ : F₂ ⟶ L ⋙ F₂')
    (e : F₁ ≅ F₂) (e' : F₁' ≅ F₂') (h : α₁ ≫ whiskerLeft L e'.hom = e.hom ≫ α₂) :
    F₁'.IsLeftKanExtension α₁ ↔ F₂'.IsLeftKanExtension α₂ := by
  let eq := LeftExtension.isUniversalEquivOfIso₂ (LeftExtension.mk _ α₁)
    (LeftExtension.mk _ α₂) e e' h
  constructor
  · exact fun _ => ⟨⟨eq.1 (isUniversalOfIsLeftKanExtension F₁' α₁)⟩⟩
  · exact fun _ => ⟨⟨eq.2 (isUniversalOfIsLeftKanExtension F₂' α₂)⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `RightExtension.isUniversalEquivOfIso₂` / `RightExtension.isUniversalEquivOfIso₂` 的定义

English:
definition RightExtension.isUniversalEquivOfIso₂
  body: (IsTerminal.isTerminalIffObj (rightExtensionEquivalenceOfIso₂ L e).functor α₁).trans
    (IsTerminal.equivOfIso (CostructuredArrow.isoMk e'
      (by simp [rightExtensionEquivalenceOfIso₂, h])))

中文:
定义 RightExtension.isUniversalEquivOfIso₂
  定义体: (IsTerminal.isTerminalIffObj (rightExtensionEquivalenceOfIso₂ L e).functor α₁).trans
    (IsTerminal.equivOfIso (CostructuredArrow.isoMk e'
      (by simp [rightExtensionEquivalenceOfIso₂, h])))

Depends on / 依赖: CostructuredArrow, CostructuredArrow.isoMk, IsTerminal, IsTerminal.equivOfIso, IsTerminal.isTerminalIffObj, equivOfIso, functor, isTerminalIffObj
-/
noncomputable def RightExtension.isUniversalEquivOfIso₂
    (α₁ : RightExtension L F₁) (α₂ : RightExtension L F₂) (e : F₁ ≅ F₂)
    (e' : α₁.left ≅ α₂.left)
    (h : whiskerLeft L e'.hom ≫ α₂.hom = α₁.hom ≫ e.hom) :
    α₁.IsUniversal ≃ α₂.IsUniversal :=
  (IsTerminal.isTerminalIffObj (rightExtensionEquivalenceOfIso₂ L e).functor α₁).trans
    (IsTerminal.equivOfIso (CostructuredArrow.isoMk e'
      (by simp [rightExtensionEquivalenceOfIso₂, h])))

/--
lemma `isRightKanExtension_iff_of_iso₂` / 引理 `isRightKanExtension_iff_of_iso₂`

English:
lemma isRightKanExtension_iff_of_iso₂
  statement: {F₁' F₂' : D ⥤ H} (α₁ : L ⋙ F₁' ⟶ F₁) (α₂ : L ⋙ F₂' ⟶ F₂)
  proof: by
  let eq := RightExtension.isUniversalEquivOfIso₂ (RightExtension.mk _ α₁)
    (RightExtension.mk _ α₂) e e' h
  constructor
  · exact fun _ => ⟨⟨eq.1 (isUniversalOfIsRightKanExtension F₁' α₁)⟩⟩
  · exact fun _ => ⟨⟨eq.2 (isUniversalOfIsRightKanExtension F₂' α₂)⟩⟩

中文:
引理 isRightKanExtension_iff_of_iso₂
  结论: {F₁' F₂' : D ⥤ H} (α₁ : L ⋙ F₁' ⟶ F₁) (α₂ : L ⋙ F₂' ⟶ F₂)
  证明: by
  let eq := RightExtension.isUniversalEquivOfIso₂ (RightExtension.mk _ α₁)
    (RightExtension.mk _ α₂) e e' h
  constructor
  · exact fun _ => ⟨⟨eq.1 (isUniversalOfIsRightKanExtension F₁' α₁)⟩⟩
  · exact fun _ => ⟨⟨eq.2 (isUniversalOfIsRightKanExtension F₂' α₂)⟩⟩

Depends on / 依赖: RightExtension, RightExtension.isUniversalEquivOfIso, RightExtension.mk, isUniversalOfIsRightKanExtension
-/
lemma isRightKanExtension_iff_of_iso₂ {F₁' F₂' : D ⥤ H} (α₁ : L ⋙ F₁' ⟶ F₁) (α₂ : L ⋙ F₂' ⟶ F₂)
    (e : F₁ ≅ F₂) (e' : F₁' ≅ F₂') (h : whiskerLeft L e'.hom ≫ α₂ = α₁ ≫ e.hom) :
    F₁'.IsRightKanExtension α₁ ↔ F₂'.IsRightKanExtension α₂ := by
  let eq := RightExtension.isUniversalEquivOfIso₂ (RightExtension.mk _ α₁)
    (RightExtension.mk _ α₂) e e' h
  constructor
  · exact fun _ => ⟨⟨eq.1 (isUniversalOfIsRightKanExtension F₁' α₁)⟩⟩
  · exact fun _ => ⟨⟨eq.2 (isUniversalOfIsRightKanExtension F₂' α₂)⟩⟩

end

section transitivity

/-- A variant of `LeftExtension.precomp` where we precompose, and then
"whisker" the diagram by a given natural transformation `(α : F₀ ⟶ L ⋙ F₁)` -/
@[simps!]
/--
Definition of `LeftExtension.precomp₂` / `LeftExtension.precomp₂` 的定义

English:
definition LeftExtension.precomp₂
  body: LeftExtension.precomp L' F₁ L ⋙ StructuredArrow.map α

#adaptation_note /-- As of nightly-2026-04-29, the simpNF linter is failing here.
Assistance investigating this would be appreciated. -/

中文:
定义 LeftExtension.precomp₂
  定义体: LeftExtension.precomp L' F₁ L ⋙ StructuredArrow.map α

#adaptation_note /-- As of nightly-2026-04-29, the simpNF linter is failing here.
Assistance investigating this would be appreciated. -/

Depends on / 依赖: LeftExtension, LeftExtension.precomp, StructuredArrow, StructuredArrow.map, precomp
-/
def LeftExtension.precomp₂
    {F₀ : C ⥤ H} {L : C ⥤ D} {F₁ : D ⥤ H} (L' : D ⥤ D') (α : F₀ ⟶ L ⋙ F₁) :
    L'.LeftExtension F₁ ⥤ (L ⋙ L').LeftExtension F₀ :=
  LeftExtension.precomp L' F₁ L ⋙ StructuredArrow.map α

#adaptation_note /-- As of nightly-2026-04-29, the simpNF linter is failing here.
Assistance investigating this would be appreciated. -/
attribute [nolint simpNF] _root_.CategoryTheory.Functor.LeftExtension.precomp₂_map_left

variable
    {L : C ⥤ D} {L' : D ⥤ D'}
    {F₀ : C ⥤ H} {F₁ : D ⥤ H} {F₂ : D' ⥤ H}
    (α : F₀ ⟶ L ⋙ F₁)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `LeftExtension.isUniversalPrecomp₂` / `LeftExtension.isUniversalPrecomp₂` 的定义

English:
definition LeftExtension.isUniversalPrecomp₂
  body: by
  letI (y : (L ⋙ L').LeftExtension F₀) :
      Unique ((precomp₂ L' α).obj b ⟶ y) := by
    let u : L'.LeftExtension F₁ :=
mk y.right
hα.desc LeftExtension.mk _
          y.hom ≫ (L.associator L' y.right).hom
    refine
⟨⟨StructuredArrow.homMk (hb.desc u) by
          ext x
          have hb_fac_

中文:
定义 LeftExtension.isUniversalPrecomp₂
  定义体: by
  letI (y : (L ⋙ L').LeftExtension F₀) :
      Unique ((precomp₂ L' α).obj b ⟶ y) := by
    let u : L'.LeftExtension F₁ :=
mk y.right
hα.desc LeftExtension.mk _
          y.hom ≫ (L.associator L' y.right).hom
    refine
⟨⟨StructuredArrow.homMk (hb.desc u) by
          ext x
          have hb_fac_

Depends on / 依赖: L.associator, L.obj, LeftExtension, LeftExtension.mk, StructuredArrow, StructuredArrow.homMk, Unique, associator, congr_app, hb.desc, hb.fac, hb.hom_ex, hb_fac_app, hom_ex, y.hom, y.right
-/
def LeftExtension.isUniversalPrecomp₂
    (hα : (LeftExtension.mk F₁ α).IsUniversal)
    {b : L'.LeftExtension F₁} (hb : b.IsUniversal) :
    ((LeftExtension.precomp₂ L' α).obj b).IsUniversal := by
  letI (y : (L ⋙ L').LeftExtension F₀) :
      Unique ((precomp₂ L' α).obj b ⟶ y) := by
    let u : L'.LeftExtension F₁ :=
mk y.right
hα.desc LeftExtension.mk _
          y.hom ≫ (L.associator L' y.right).hom
    refine
⟨⟨StructuredArrow.homMk (hb.desc u) by
          ext x
          have hb_fac_app := congr_app (hb.fac u) (L.obj x)
          have hα_fac_app :=
            congr_app (hα.fac <| LeftExtension.mk _ <|
              y.hom ≫ (L.associator L' y.right).hom) x
          dsimp at hα_fac_app hb_fac_app
          simp [hb_fac_app, u, hα_fac_app]⟩, fun a => ?_⟩
    dsimp
    ext1
    apply hb.hom_ext
    apply hα.hom_ext
    ext t
    dsimp
    have a_w_t := congr_app a.w t
    have hb_fac_app := congr_app (hb.fac u) (L.obj t)
    have hα_fac_app :=
      congr_app
        (hα.fac <| LeftExtension.mk _ <|
          y.hom ≫ (L.associator L' y.right).hom) t
    dsimp at hb_fac_app hα_fac_app
    simp only [whiskeringLeft_obj_obj, comp_obj,
      precomp₂_obj_right, whiskeringLeft_obj_map, NatTrans.comp_app,
      precomp₂_obj_hom_app, whiskerLeft_app, assoc] at a_w_t
    simp [← a_w_t, hb_fac_app, u, hα_fac_app]
  apply IsInitial.ofUnique

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `LeftExtension.isUniversalOfPrecomp₂` / `LeftExtension.isUniversalOfPrecomp₂` 的定义

English:
definition LeftExtension.isUniversalOfPrecomp₂
  body: by
  letI (y : L'.LeftExtension F₁) : Unique (b ⟶ y) := by
    let u : (LeftExtension.precomp₂ L' α).obj b ⟶
      (LeftExtension.precomp₂ L' α).obj y := hb.to _
    refine
⟨⟨StructuredArrow.homMk u.right by
          apply hα.hom_ext
          ext t
          have := congr_app u.w t
          dsimp

中文:
定义 LeftExtension.isUniversalOfPrecomp₂
  定义体: by
  letI (y : L'.LeftExtension F₁) : Unique (b ⟶ y) := by
    let u : (LeftExtension.precomp₂ L' α).obj b ⟶
      (LeftExtension.precomp₂ L' α).obj y := hb.to _
    refine
⟨⟨StructuredArrow.homMk u.right by
          apply hα.hom_ext
          ext t
          have := congr_app u.w t
          dsimp

Depends on / 依赖: IsInitial, IsInitial.ofUnique, LeftExtension, LeftExtension.precomp, StructuredArrow, StructuredArrow.homMk, Unique, congr_app, hb.hom_ext, hb.to, hom_ext, ofUnique, u.right
-/
def LeftExtension.isUniversalOfPrecomp₂
    (hα : (LeftExtension.mk F₁ α).IsUniversal)
    {b : L'.LeftExtension F₁}
    (hb : ((LeftExtension.precomp₂ L' α).obj b).IsUniversal) :
    b.IsUniversal := by
  letI (y : L'.LeftExtension F₁) : Unique (b ⟶ y) := by
    let u : (LeftExtension.precomp₂ L' α).obj b ⟶
      (LeftExtension.precomp₂ L' α).obj y := hb.to _
    refine
⟨⟨StructuredArrow.homMk u.right by
          apply hα.hom_ext
          ext t
          have := congr_app u.w t
          dsimp at this
          simp only [precomp₂_obj_hom_app, assoc] at this
          simp [this]⟩, fun a => ?_⟩
    ext1
    apply hb.hom_ext
    ext t
    have := congr_app u.w t
    dsimp at this
    simp only [precomp₂_obj_hom_app, assoc] at this
    simp [this, ← a.w]
  apply IsInitial.ofUnique

/--
Definition of `LeftExtension.isUniversalPrecomp₂Equiv` / `LeftExtension.isUniversalPrecomp₂Equiv` 的定义

English:
definition LeftExtension.isUniversalPrecomp₂Equiv
  body: LeftExtension.isUniversalPrecomp₂ α hα h
  invFun h := LeftExtension.isUniversalOfPrecomp₂ α hα h
  left_inv x := by subsingleton
  right_inv x := by subsingleton

中文:
定义 LeftExtension.isUniversalPrecomp₂Equiv
  定义体: LeftExtension.isUniversalPrecomp₂ α hα h
  invFun h := LeftExtension.isUniversalOfPrecomp₂ α hα h
  left_inv x := by subsingleton
  right_inv x := by subsingleton

Depends on / 依赖: LeftExtension, LeftExtension.isUniversalPrecomp
-/
def LeftExtension.isUniversalPrecomp₂Equiv
    (hα : (LeftExtension.mk F₁ α).IsUniversal)
    (b : L'.LeftExtension F₁) :
    b.IsUniversal ≃ ((LeftExtension.precomp₂ L' α).obj b).IsUniversal where
  toFun h := LeftExtension.isUniversalPrecomp₂ α hα h
  invFun h := LeftExtension.isUniversalOfPrecomp₂ α hα h
  left_inv x := by subsingleton
  right_inv x := by subsingleton


set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `isLeftKanExtension_iff_postcompose` / 定理 `isLeftKanExtension_iff_postcompose`

English:
theorem isLeftKanExtension_iff_postcompose
  statement: [F₁.IsLeftKanExtension α]
  proof: by
  let Ψ := leftExtensionEquivalenceOfIso₁ e F₀
  obtain ⟨⟨hα⟩⟩ := (inferInstance : F₁.IsLeftKanExtension α)
  refine ⟨fun ⟨⟨h⟩⟩ => ⟨⟨?_⟩⟩, fun ⟨⟨h⟩⟩ => ⟨⟨?_⟩⟩⟩
.invFun · apply IsInitial.isInitialIffObj Ψ.inverse _
    haveI := LeftExtension.isUniversalPrecomp₂ α hα h
    let i :
        (LeftExte

中文:
定理 isLeftKanExtension_iff_postcompose
  结论: [F₁.是LeftKanExtension α]
  证明: by
  let Ψ := leftExtensionEquivalenceOfIso₁ e F₀
  obtain ⟨⟨hα⟩⟩ := (inferInstance : F₁.IsLeftKanExtension α)
  refine ⟨fun ⟨⟨h⟩⟩ => ⟨⟨?_⟩⟩, fun ⟨⟨h⟩⟩ => ⟨⟨?_⟩⟩⟩
.invFun · apply IsInitial.isInitialIffObj Ψ.inverse _
    haveI := LeftExtension.isUniversalPrecomp₂ α hα h
    let i :
        (LeftExte

Depends on / 依赖: IsInitial, IsInitial.isInitialIffObj, IsLeftKanExtension, LeftExtension, LeftExtension.isUniversalPrecomp, LeftExtension.mk, LeftExtension.precomp, NatIso, NatIso.ofComponents, StructuredArrow, StructuredArrow.isoMk, aesop_cat, invFun, inverse, inverse.obj, isInitialIffObj, ofComponents
-/
theorem isLeftKanExtension_iff_postcompose [F₁.IsLeftKanExtension α]
    {F₂ : D' ⥤ H} (L'' : C ⥤ D') (e : L ⋙ L' ≅ L'') (β : F₁ ⟶ L' ⋙ F₂)
    (γ : F₀ ⟶ L'' ⋙ F₂)
    (hγ :
      α ≫ whiskerLeft _ β ≫
        (Functor.associator _ _ _).inv ≫ whiskerRight e.hom F₂ =
      γ := by aesop_cat) :
    F₂.IsLeftKanExtension β ↔ F₂.IsLeftKanExtension γ := by
  let Ψ := leftExtensionEquivalenceOfIso₁ e F₀
  obtain ⟨⟨hα⟩⟩ := (inferInstance : F₁.IsLeftKanExtension α)
  refine ⟨fun ⟨⟨h⟩⟩ => ⟨⟨?_⟩⟩, fun ⟨⟨h⟩⟩ => ⟨⟨?_⟩⟩⟩
.invFun · apply IsInitial.isInitialIffObj Ψ.inverse _
    haveI := LeftExtension.isUniversalPrecomp₂ α hα h
    let i :
        (LeftExtension.precomp₂ L' α).obj (LeftExtension.mk F₂ β) ≅
        Ψ.inverse.obj (LeftExtension.mk F₂ γ) :=
StructuredArrow.isoMk (NatIso.ofComponents fun _ => .refl _) by
        ext x
        simp [Ψ, ← congr_app hγ x, ← Functor.map_comp]
    exact IsInitial.ofIso this i
  · apply LeftExtension.isUniversalOfPrecomp₂ α hα
.invFun apply IsInitial.isInitialIffObj Ψ.functor _
    let i :
        (LeftExtension.mk F₂ γ) ≅
Ψ.functor.obj (LeftExtension.precomp₂ L' α).obj
          LeftExtension.mk F₂ β :=
      StructuredArrow.isoMk (NatIso.ofComponents fun _ => .refl _)
    exact IsInitial.ofIso h i

end transitivity

section Colimit

variable (F' : D ⥤ H) {L : C ⥤ D} {F : C ⥤ H} (α : F ⟶ L ⋙ F') [F'.IsLeftKanExtension α]

/-- Construct a cocone for a left Kan extension `F' : D ⥤ H` of `F : C ⥤ H` along a functor
`L : C ⥤ D` given a cocone for `F`. -/
@[simps]
/--
Definition of `coconeOfIsLeftKanExtension` / `coconeOfIsLeftKanExtension` 的定义

English:
definition coconeOfIsLeftKanExtension
  signature: (c : Cocone F)
  body: c.pt
  ι := F'.descOfIsLeftKanExtension α _ c.ι

中文:
定义 coconeOfIsLeftKanExtension
  签名: (c : 余锥 F)
  定义体: c.pt
  ι := F'.descOfIsLeftKanExtension α _ c.ι

Depends on / 依赖: c.pt
-/
noncomputable def coconeOfIsLeftKanExtension (c : Cocone F) : Cocone F' where
  pt := c.pt
  ι := F'.descOfIsLeftKanExtension α _ c.ι

set_option backward.isDefEq.respectTransparency false in
/-- If `c` is a colimit cocone for a functor `F : C ⥤ H` and `α : F ⟶ L ⋙ F'` is the unit of any
left Kan extension `F' : D ⥤ H` of `F` along `L : C ⥤ D`, then `coconeOfIsLeftKanExtension α c` is
a colimit cocone, too. -/
@[simps]
/--
Definition of `isColimitCoconeOfIsLeftKanExtension` / `isColimitCoconeOfIsLeftKanExtension` 的定义

English:
definition isColimitCoconeOfIsLeftKanExtension
  signature: {c : Cocone F} (hc : IsColimit c)
  body: hc.desc (Cocone.mk _ (α ≫ whiskerLeft L s.ι))
  fac s := by
    have : F'.descOfIsLeftKanExtension α ((const D).obj c.pt) c.ι ≫
        (Functor.const _).map (hc.desc (Cocone.mk _ (α ≫ whiskerLeft L s.ι))) = s.ι :=
      F'.hom_ext_of_isLeftKanExtension α _ _ (by cat_disch)
    exact congr_app this


中文:
定义 isColimitCoconeOfIsLeftKanExtension
  签名: {c : 余锥 F} (hc : 是余极限 c)
  定义体: hc.desc (Cocone.mk _ (α ≫ whiskerLeft L s.ι))
  fac s := by
    have : F'.descOfIsLeftKanExtension α ((const D).obj c.pt) c.ι ≫
        (Functor.const _).map (hc.desc (Cocone.mk _ (α ≫ whiskerLeft L s.ι))) = s.ι :=
      F'.hom_ext_of_isLeftKanExtension α _ _ (by cat_disch)
    exact congr_app this


Depends on / 依赖: Cocone, Cocone.mk, hc.desc, whiskerLeft
-/
noncomputable def isColimitCoconeOfIsLeftKanExtension {c : Cocone F} (hc : IsColimit c) :
    IsColimit (F'.coconeOfIsLeftKanExtension α c) where
  desc s := hc.desc (Cocone.mk _ (α ≫ whiskerLeft L s.ι))
  fac s := by
    have : F'.descOfIsLeftKanExtension α ((const D).obj c.pt) c.ι ≫
        (Functor.const _).map (hc.desc (Cocone.mk _ (α ≫ whiskerLeft L s.ι))) = s.ι :=
      F'.hom_ext_of_isLeftKanExtension α _ _ (by cat_disch)
    exact congr_app this
  uniq s m hm := hc.hom_ext (fun j => by
    have := hm (L.obj j)
    nth_rw 1 [← F'.descOfIsLeftKanExtension_fac_app α ((const D).obj c.pt)]
    dsimp at this ⊢
    rw [assoc]; rw [this]; rw [IsColimit.fac]; rw [NatTrans.comp_app]; rw [whiskerLeft_app])

variable [HasColimit F] [HasColimit F']

/--
Definition of `colimitIsoOfIsLeftKanExtension` / `colimitIsoOfIsLeftKanExtension` 的定义

English:
definition colimitIsoOfIsLeftKanExtension
  signature: : colimit F' ≅ colimit F
  body: IsColimit.coconePointUniqueUpToIso (colimit.isColimit F')
    (F'.isColimitCoconeOfIsLeftKanExtension α (colimit.isColimit F))

中文:
定义 colimitIsoOfIsLeftKanExtension
  签名: : colimit F' ≅ colimit F
  定义体: IsColimit.coconePointUniqueUpToIso (colimit.isColimit F')
    (F'.isColimitCoconeOfIsLeftKanExtension α (colimit.isColimit F))

Depends on / 依赖: IsColimit, IsColimit.coconePointUniqueUpToIso, coconePointUniqueUpToIso, colimit, colimit.isColimit, isColimit, isColimitCoconeOfIsLeftKanExtension
-/
noncomputable def colimitIsoOfIsLeftKanExtension : colimit F' ≅ colimit F :=
  IsColimit.coconePointUniqueUpToIso (colimit.isColimit F')
    (F'.isColimitCoconeOfIsLeftKanExtension α (colimit.isColimit F))

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `ι_colimitIsoOfIsLeftKanExtension_hom` / 引理 `ι_colimitIsoOfIsLeftKanExtension_hom`

English:
lemma ι_colimitIsoOfIsLeftKanExtension_hom
  given: (i : C)
  proof: by
  simp [colimitIsoOfIsLeftKanExtension]

@[reassoc (attr := simp)]

中文:
引理 ι_colimitIsoOfIsLeftKanExtension_hom
  条件: (i : C)
  证明: by
  simp [colimitIsoOfIsLeftKanExtension]

@[reassoc (attr := simp)]

Depends on / 依赖: colimitIsoOfIsLeftKanExtension
-/
lemma ι_colimitIsoOfIsLeftKanExtension_hom (i : C) :
    α.app i ≫ colimit.ι F' (L.obj i) ≫ (F'.colimitIsoOfIsLeftKanExtension α).hom =
      colimit.ι F i := by
  simp [colimitIsoOfIsLeftKanExtension]

@[reassoc (attr := simp)]
/--
lemma `ι_colimitIsoOfIsLeftKanExtension_inv` / 引理 `ι_colimitIsoOfIsLeftKanExtension_inv`

English:
lemma ι_colimitIsoOfIsLeftKanExtension_inv
  given: (i : C)
  proof: by
  rw [Iso.comp_inv_eq]; rw [assoc]; rw [ι_colimitIsoOfIsLeftKanExtension_hom]

中文:
引理 ι_colimitIsoOfIsLeftKanExtension_inv
  条件: (i : C)
  证明: by
  rw [Iso.comp_inv_eq]; rw [assoc]; rw [ι_colimitIsoOfIsLeftKanExtension_hom]

Depends on / 依赖: Iso.comp_inv_eq, comp_inv_eq
-/
lemma ι_colimitIsoOfIsLeftKanExtension_inv (i : C) :
    colimit.ι F i ≫ (F'.colimitIsoOfIsLeftKanExtension α).inv =
    α.app i ≫ colimit.ι F' (L.obj i) := by
  rw [Iso.comp_inv_eq]; rw [assoc]; rw [ι_colimitIsoOfIsLeftKanExtension_hom]

end Colimit

section Limit

variable (F' : D ⥤ H) {L : C ⥤ D} {F : C ⥤ H} (α : L ⋙ F' ⟶ F) [F'.IsRightKanExtension α]

/-- Construct a cone for a right Kan extension `F' : D ⥤ H` of `F : C ⥤ H` along a functor
`L : C ⥤ D` given a cone for `F`. -/
@[simps, implicit_reducible]
/--
Definition of `coneOfIsRightKanExtension` / `coneOfIsRightKanExtension` 的定义

English:
definition coneOfIsRightKanExtension
  signature: (c : Cone F)
  body: c.pt
  π := F'.liftOfIsRightKanExtension α _ c.π

中文:
定义 coneOfIsRightKanExtension
  签名: (c : 锥 F)
  定义体: c.pt
  π := F'.liftOfIsRightKanExtension α _ c.π

Depends on / 依赖: c.pt
-/
noncomputable def coneOfIsRightKanExtension (c : Cone F) : Cone F' where
  pt := c.pt
  π := F'.liftOfIsRightKanExtension α _ c.π

set_option backward.isDefEq.respectTransparency false in
/-- If `c` is a limit cone for a functor `F : C ⥤ H` and `α : L ⋙ F' ⟶ F` is the counit of any
right Kan extension `F' : D ⥤ H` of `F` along `L : C ⥤ D`, then `coneOfIsRightKanExtension α c` is
a limit cone, too. -/
@[simps]
/--
Definition of `isLimitConeOfIsRightKanExtension` / `isLimitConeOfIsRightKanExtension` 的定义

English:
definition isLimitConeOfIsRightKanExtension
  signature: {c : Cone F} (hc : IsLimit c)
  body: hc.lift (Cone.mk _ (whiskerLeft L s.π ≫ α))
  fac s := by
    have : (Functor.const _).map (hc.lift (Cone.mk _ (whiskerLeft L s.π ≫ α))) ≫
        F'.liftOfIsRightKanExtension α ((const D).obj c.pt) c.π = s.π :=
      F'.hom_ext_of_isRightKanExtension α _ _ (by cat_disch)
    exact congr_app this
  

中文:
定义 isLimitConeOfIsRightKanExtension
  签名: {c : 锥 F} (hc : 是极限 c)
  定义体: hc.lift (Cone.mk _ (whiskerLeft L s.π ≫ α))
  fac s := by
    have : (Functor.const _).map (hc.lift (Cone.mk _ (whiskerLeft L s.π ≫ α))) ≫
        F'.liftOfIsRightKanExtension α ((const D).obj c.pt) c.π = s.π :=
      F'.hom_ext_of_isRightKanExtension α _ _ (by cat_disch)
    exact congr_app this
  

Depends on / 依赖: Cone.mk, hc.lift, whiskerLeft
-/
noncomputable def isLimitConeOfIsRightKanExtension {c : Cone F} (hc : IsLimit c) :
    IsLimit (F'.coneOfIsRightKanExtension α c) where
  lift s := hc.lift (Cone.mk _ (whiskerLeft L s.π ≫ α))
  fac s := by
    have : (Functor.const _).map (hc.lift (Cone.mk _ (whiskerLeft L s.π ≫ α))) ≫
        F'.liftOfIsRightKanExtension α ((const D).obj c.pt) c.π = s.π :=
      F'.hom_ext_of_isRightKanExtension α _ _ (by cat_disch)
    exact congr_app this
  uniq s m hm := hc.hom_ext (fun j => by
    have := hm (L.obj j)
    nth_rw 1 [← F'.liftOfIsRightKanExtension_fac_app α ((const D).obj c.pt)]
    dsimp at this ⊢
    rw [← assoc]; rw [this]; rw [IsLimit.fac]; rw [NatTrans.comp_app]; rw [whiskerLeft_app])

variable [HasLimit F] [HasLimit F']

/--
Definition of `limitIsoOfIsRightKanExtension` / `limitIsoOfIsRightKanExtension` 的定义

English:
definition limitIsoOfIsRightKanExtension
  signature: : limit F' ≅ limit F
  body: IsLimit.conePointUniqueUpToIso (limit.isLimit F')
    (F'.isLimitConeOfIsRightKanExtension α (limit.isLimit F))

@[reassoc (attr := simp)]

中文:
定义 limitIsoOfIsRightKanExtension
  签名: : limit F' ≅ limit F
  定义体: IsLimit.conePointUniqueUpToIso (limit.isLimit F')
    (F'.isLimitConeOfIsRightKanExtension α (limit.isLimit F))

@[reassoc (attr := simp)]

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso, conePointUniqueUpToIso, isLimit, isLimitConeOfIsRightKanExtension, limit.isLimit
-/
noncomputable def limitIsoOfIsRightKanExtension : limit F' ≅ limit F :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit F')
    (F'.isLimitConeOfIsRightKanExtension α (limit.isLimit F))

@[reassoc (attr := simp)]
/--
lemma `limitIsoOfIsRightKanExtension_inv_π` / 引理 `limitIsoOfIsRightKanExtension_inv_π`

English:
lemma limitIsoOfIsRightKanExtension_inv_π
  given: (i : C)
  proof: by
  simp [limitIsoOfIsRightKanExtension]

@[reassoc (attr := simp)]

中文:
引理 limitIsoOfIsRightKanExtension_inv_π
  条件: (i : C)
  证明: by
  simp [limitIsoOfIsRightKanExtension]

@[reassoc (attr := simp)]

Depends on / 依赖: limitIsoOfIsRightKanExtension
-/
lemma limitIsoOfIsRightKanExtension_inv_π (i : C) :
    (F'.limitIsoOfIsRightKanExtension α).inv ≫ limit.π F' (L.obj i) ≫ α.app i = limit.π F i := by
  simp [limitIsoOfIsRightKanExtension]

@[reassoc (attr := simp)]
/--
lemma `limitIsoOfIsRightKanExtension_hom_π` / 引理 `limitIsoOfIsRightKanExtension_hom_π`

English:
lemma limitIsoOfIsRightKanExtension_hom_π
  given: (i : C)
  proof: by
  rw [← Iso.eq_inv_comp]; rw [limitIsoOfIsRightKanExtension_inv_π]

中文:
引理 limitIsoOfIsRightKanExtension_hom_π
  条件: (i : C)
  证明: by
  rw [← Iso.eq_inv_comp]; rw [limitIsoOfIsRightKanExtension_inv_π]

Depends on / 依赖: Iso.eq_inv_comp, cancel_mono, cat_disch, eq_inv_comp, kernel, kernel.lift
-/
lemma limitIsoOfIsRightKanExtension_hom_π (i : C) :
    (F'.limitIsoOfIsRightKanExtension α).hom ≫ limit.π F i = limit.π F' (L.obj i) ≫ α.app i := by
  rw [← Iso.eq_inv_comp]; rw [limitIsoOfIsRightKanExtension_inv_π]

end Limit

section

variable {L : C ≌ D} {F₀ : C ⥤ H} {F₁ : D ⥤ H}

variable (F₀) in
/--
Instance `isLeftKanExtensionId` / 实例 `isLeftKanExtensionId`

English:
instance isLeftKanExtensionId
  signature: : F₀.IsLeftKanExtension F₀.leftUnitor.inv where
  body: ⟨StructuredArrow.mkIdInitial⟩

中文:
实例 isLeftKanExtensionId
  签名: : F₀.是LeftKanExtension F₀.leftUnitor.inv where
  定义体: ⟨StructuredArrow.mkIdInitial⟩

Depends on / 依赖: StructuredArrow, StructuredArrow.mkIdInitial, mkIdInitial
-/
instance isLeftKanExtensionId : F₀.IsLeftKanExtension F₀.leftUnitor.inv where
  nonempty_isUniversal := ⟨StructuredArrow.mkIdInitial⟩

variable (F₀) in
/--
Instance `isRightKanExtensionId` / 实例 `isRightKanExtensionId`

English:
instance isRightKanExtensionId
  signature: : F₀.IsRightKanExtension F₀.leftUnitor.hom where
  body: ⟨CostructuredArrow.mkIdTerminal⟩

中文:
实例 isRightKanExtensionId
  签名: : F₀.是RightKanExtension F₀.leftUnitor.hom where
  定义体: ⟨CostructuredArrow.mkIdTerminal⟩

Depends on / 依赖: CostructuredArrow, CostructuredArrow.mkIdTerminal, mkIdTerminal
-/
instance isRightKanExtensionId : F₀.IsRightKanExtension F₀.leftUnitor.hom where
  nonempty_isUniversal := ⟨CostructuredArrow.mkIdTerminal⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `isLeftKanExtensionAlongEquivalence` / 实例 `isLeftKanExtensionAlongEquivalence`

English:
instance isLeftKanExtensionAlongEquivalence
  signature: (α : F₀ ≅ L.functor ⋙ F₁)
  body: by
  refine ⟨⟨?_⟩⟩
  apply LeftExtension.isUniversalPostcomp₁Equiv
.invFun (G := L.functor) L.functor.leftUnitor F₀ _
  refine IsInitial.ofUniqueHom
    (fun y => StructuredArrow.homMk <| α.inv ≫ y.hom ≫ y.right.leftUnitor.hom) ?_
  intro y m
  ext x
  simpa using α.inv.app x ≫= congr_app m.w x

中文:
实例 isLeftKanExtensionAlongEquivalence
  签名: (α : F₀ ≅ L.functor ⋙ F₁)
  定义体: by
  refine ⟨⟨?_⟩⟩
  apply LeftExtension.isUniversalPostcomp₁Equiv
.invFun (G := L.functor) L.functor.leftUnitor F₀ _
  refine IsInitial.ofUniqueHom
    (fun y => StructuredArrow.homMk <| α.inv ≫ y.hom ≫ y.right.leftUnitor.hom) ?_
  intro y m
  ext x
  simpa using α.inv.app x ≫= congr_app m.w x

Depends on / 依赖: IsInitial, IsInitial.ofUniqueHom, L.functor, L.functor.leftUnitor, LeftExtension, LeftExtension.isUniversalPostcomp, StructuredArrow, StructuredArrow.homMk, congr_app, functor, inv.app, invFun, leftUnitor, ofUniqueHom, y.hom, y.right.leftUnitor.hom
-/
instance isLeftKanExtensionAlongEquivalence (α : F₀ ≅ L.functor ⋙ F₁) :
    F₁.IsLeftKanExtension α.hom := by
  refine ⟨⟨?_⟩⟩
  apply LeftExtension.isUniversalPostcomp₁Equiv
.invFun (G := L.functor) L.functor.leftUnitor F₀ _
  refine IsInitial.ofUniqueHom
    (fun y => StructuredArrow.homMk <| α.inv ≫ y.hom ≫ y.right.leftUnitor.hom) ?_
  intro y m
  ext x
  simpa using α.inv.app x ≫= congr_app m.w x

set_option backward.isDefEq.respectTransparency false in
/--
Instance `isLeftKanExtensionAlongEquivalence'` / 实例 `isLeftKanExtensionAlongEquivalence'`

English:
instance isLeftKanExtensionAlongEquivalence'
  signature: (L : C ⥤ D) (α : F₀ ⟶ L ⋙ F₁)
  body: inferInstanceAs
    F₁.IsLeftKanExtension (asIso α : F₀ ≅ (asEquivalence L).functor ⋙ F₁).hom

中文:
实例 isLeftKanExtensionAlongEquivalence'
  签名: (L : C ⥤ D) (α : F₀ ⟶ L ⋙ F₁)
  定义体: inferInstanceAs
    F₁.IsLeftKanExtension (asIso α : F₀ ≅ (asEquivalence L).functor ⋙ F₁).hom

Depends on / 依赖: IsLeftKanExtension, asEquivalence, functor
-/
instance isLeftKanExtensionAlongEquivalence' (L : C ⥤ D) (α : F₀ ⟶ L ⋙ F₁)
    [IsEquivalence L] [IsIso α] :
    F₁.IsLeftKanExtension α :=
inferInstanceAs
    F₁.IsLeftKanExtension (asIso α : F₀ ≅ (asEquivalence L).functor ⋙ F₁).hom

set_option backward.isDefEq.respectTransparency false in
/--
Instance `isRightKanExtensionAlongEquivalence` / 实例 `isRightKanExtensionAlongEquivalence`

English:
instance isRightKanExtensionAlongEquivalence
  signature: (α : L.functor ⋙ F₁ ≅ F₀)
  body: by
  refine ⟨⟨?_⟩⟩
  apply RightExtension.isUniversalPostcomp₁Equiv
.invFun (G := L.functor) L.functor.leftUnitor F₀ _
  refine IsTerminal.ofUniqueHom
    (fun y => CostructuredArrow.homMk <| y.left.leftUnitor.inv ≫ y.hom ≫ α.inv) ?_
  intro y m
  ext x
  simpa using congr_app m.w x =≫ α.inv.app x

中文:
实例 isRightKanExtensionAlongEquivalence
  签名: (α : L.functor ⋙ F₁ ≅ F₀)
  定义体: by
  refine ⟨⟨?_⟩⟩
  apply RightExtension.isUniversalPostcomp₁Equiv
.invFun (G := L.functor) L.functor.leftUnitor F₀ _
  refine IsTerminal.ofUniqueHom
    (fun y => CostructuredArrow.homMk <| y.left.leftUnitor.inv ≫ y.hom ≫ α.inv) ?_
  intro y m
  ext x
  simpa using congr_app m.w x =≫ α.inv.app x

Depends on / 依赖: CostructuredArrow, CostructuredArrow.homMk, IsTerminal, IsTerminal.ofUniqueHom, L.functor, L.functor.leftUnitor, RightExtension, RightExtension.isUniversalPostcomp, congr_app, functor, inv.app, invFun, leftUnitor, ofUniqueHom, y.hom, y.left.leftUnitor.inv
-/
instance isRightKanExtensionAlongEquivalence (α : L.functor ⋙ F₁ ≅ F₀) :
    F₁.IsRightKanExtension α.hom := by
  refine ⟨⟨?_⟩⟩
  apply RightExtension.isUniversalPostcomp₁Equiv
.invFun (G := L.functor) L.functor.leftUnitor F₀ _
  refine IsTerminal.ofUniqueHom
    (fun y => CostructuredArrow.homMk <| y.left.leftUnitor.inv ≫ y.hom ≫ α.inv) ?_
  intro y m
  ext x
  simpa using congr_app m.w x =≫ α.inv.app x

set_option backward.isDefEq.respectTransparency false in
/--
Instance `isRightKanExtensionAlongEquivalence'` / 实例 `isRightKanExtensionAlongEquivalence'`

English:
instance isRightKanExtensionAlongEquivalence'
  signature: (L : C ⥤ D) (α : L ⋙ F₁ ⟶ F₀)
  body: inferInstanceAs
    F₁.IsRightKanExtension (asIso α : (asEquivalence L).functor ⋙ F₁ ≅ F₀).hom

中文:
实例 isRightKanExtensionAlongEquivalence'
  签名: (L : C ⥤ D) (α : L ⋙ F₁ ⟶ F₀)
  定义体: inferInstanceAs
    F₁.IsRightKanExtension (asIso α : (asEquivalence L).functor ⋙ F₁ ≅ F₀).hom

Depends on / 依赖: IsRightKanExtension, asEquivalence, functor
-/
instance isRightKanExtensionAlongEquivalence' (L : C ⥤ D) (α : L ⋙ F₁ ⟶ F₀)
    [IsEquivalence L] [IsIso α] :
    F₁.IsRightKanExtension α :=
inferInstanceAs
    F₁.IsRightKanExtension (asIso α : (asEquivalence L).functor ⋙ F₁ ≅ F₀).hom

end

end Functor

end CategoryTheory
