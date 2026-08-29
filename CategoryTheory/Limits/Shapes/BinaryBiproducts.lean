/-
Copyright (c) 2019 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Jakob von Raumer
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

/-!
# Binary biproducts

We introduce the notion of binary biproducts.

These are slightly unusual relative to the other shapes in the library,
as they are simultaneously limits and colimits.
(Zero objects are similar; they are "biterminal".)

For results about biproducts in preadditive categories see
`CategoryTheory.Preadditive.Biproducts`.

In a category with zero morphisms, we model the (binary) biproduct of `P Q : C`
using a `BinaryBicone`, which has a cone point `X`,
and morphisms `fst : X ⟶ P`, `snd : X ⟶ Q`, `inl : P ⟶ X` and `inr : X ⟶ Q`,
such that `inl ≫ fst = 𝟙 P`, `inl ≫ snd = 0`, `inr ≫ fst = 0`, and `inr ≫ snd = 𝟙 Q`.
Such a `BinaryBicone` is a biproduct if the cone is a limit cone, and the cocone is a colimit
cocone.

-/

@[expose] public section

noncomputable section

universe w w' v u

open CategoryTheory Functor Opposite

namespace CategoryTheory.Limits

variable {J : Type w}
universe uC' uC uD' uD
variable {C : Type uC} [Category.{uC'} C] [HasZeroMorphisms C]
variable {D : Type uD} [Category.{uD'} D] [HasZeroMorphisms D]

/--
Definition of `BinaryBicone` / `BinaryBicone` 的定义

English:
structure BinaryBicone
  parameters: (P Q : C)
  axioms and operations (9):
    - pt : C
    - fst : pt ⟶ P
    - snd : pt ⟶ Q
    - inl : P ⟶ pt
    - inr : Q ⟶ pt
    - inl_fst : inl ≫ fst = 𝟙 P  [default: by aesop]
    - inl_snd : inl ≫ snd = 0  [default: by aesop]
    - inr_fst : inr ≫ fst = 0  [default: by aesop]
    - inr_snd : inr ≫ snd = 𝟙 Q  [default: by aesop]

中文:
结构 BinaryBicone
  参数: (P Q : C)
  公理与运算 (9 个):
    - pt : C
    - fst : pt ⟶ P
    - snd : pt ⟶ Q
    - inl : P ⟶ pt
    - inr : Q ⟶ pt
    - inl_fst : inl ≫ fst = 𝟙 P  [默认: by aesop]
    - inl_snd : inl ≫ snd = 0  [默认: by aesop]
    - inr_fst : inr ≫ fst = 0  [默认: by aesop]
    - inr_snd : inr ≫ snd = 𝟙 Q  [默认: by aesop]

Depends on / 依赖: inl_snd, inr_fst, inr_snd
-/
structure BinaryBicone (P Q : C) where
  pt : C
  fst : pt ⟶ P
  snd : pt ⟶ Q
  inl : P ⟶ pt
  inr : Q ⟶ pt
  inl_fst : inl ≫ fst = 𝟙 P := by aesop
  inl_snd : inl ≫ snd = 0 := by aesop
  inr_fst : inr ≫ fst = 0 := by aesop
  inr_snd : inr ≫ snd = 𝟙 Q := by aesop

attribute [inherit_doc BinaryBicone] BinaryBicone.pt BinaryBicone.fst BinaryBicone.snd
  BinaryBicone.inl BinaryBicone.inr BinaryBicone.inl_fst BinaryBicone.inl_snd
  BinaryBicone.inr_fst BinaryBicone.inr_snd

attribute [reassoc (attr := simp)]
  BinaryBicone.inl_fst BinaryBicone.inl_snd BinaryBicone.inr_fst BinaryBicone.inr_snd

/--
Definition of `BinaryBiconeMorphism` / `BinaryBiconeMorphism` 的定义

English:
structure BinaryBiconeMorphism
  parameters: {P Q : C} (A B : BinaryBicone P Q)
  axioms and operations (5):
    - hom : A.pt ⟶ B.pt
    - wfst : hom ≫ B.fst = A.fst  [default: by cat_disch]
    - wsnd : hom ≫ B.snd = A.snd  [default: by cat_disch]
    - winl : A.inl ≫ hom = B.inl  [default: by cat_disch]
    - winr : A.inr ≫ hom = B.inr  [default: by cat_disch]

中文:
结构 BinaryBicone态射
  参数: {P Q : C} (A B : BinaryBicone P Q)
  公理与运算 (5 个):
    - hom : A.pt ⟶ B.pt
    - wfst : hom ≫ B.fst = A.fst  [默认: by cat_disch]
    - wsnd : hom ≫ B.snd = A.snd  [默认: by cat_disch]
    - winl : A.inl ≫ hom = B.inl  [默认: by cat_disch]
    - winr : A.inr ≫ hom = B.inr  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure BinaryBiconeMorphism {P Q : C} (A B : BinaryBicone P Q) where
  /-- A morphism between the two vertex objects of the bicones -/
  hom : A.pt ⟶ B.pt
  /-- The triangle consisting of the two natural transformations and `hom` commutes -/
  wfst : hom ≫ B.fst = A.fst := by cat_disch
  /-- The triangle consisting of the two natural transformations and `hom` commutes -/
  wsnd : hom ≫ B.snd = A.snd := by cat_disch
  /-- The triangle consisting of the two natural transformations and `hom` commutes -/
  winl : A.inl ≫ hom = B.inl := by cat_disch
  /-- The triangle consisting of the two natural transformations and `hom` commutes -/
  winr : A.inr ≫ hom = B.inr := by cat_disch

attribute [reassoc (attr := simp)] BinaryBiconeMorphism.wfst BinaryBiconeMorphism.wsnd
attribute [reassoc (attr := simp)] BinaryBiconeMorphism.winl BinaryBiconeMorphism.winr

/-- The category of binary bicones on a given diagram. -/
@[simps]
/--
Instance `BinaryBicone.category` / 实例 `BinaryBicone.category`

English:
instance BinaryBicone.category
  signature: {P Q : C}
  body: BinaryBiconeMorphism A B
  comp f g := { hom := f.hom ≫ g.hom }
  id B := { hom := 𝟙 B.pt }

中文:
实例 BinaryBicone.category
  签名: {P Q : C}
  定义体: BinaryBiconeMorphism A B
  comp f g := { hom := f.hom ≫ g.hom }
  id B := { hom := 𝟙 B.pt }

Depends on / 依赖: BinaryBiconeMorphism
-/
instance BinaryBicone.category {P Q : C} : Category (BinaryBicone P Q) where
  Hom A B := BinaryBiconeMorphism A B
  comp f g := { hom := f.hom ≫ g.hom }
  id B := { hom := 𝟙 B.pt }

/-- We do not want `simps` automatically generate the lemma for simplifying the `Hom` field of
-- a category. So we need to write the `ext` lemma in terms of the categorical morphism, rather than
the underlying structure. -/
@[ext]
/--
theorem `BinaryBiconeMorphism.ext` / 定理 `BinaryBiconeMorphism.ext`

English:
theorem BinaryBiconeMorphism.ext
  statement: {P Q : C} {c c' : BinaryBicone P Q}
  proof: by
  cases f
  cases g
  congr

中文:
定理 BinaryBicone态射.ext
  结论: {P Q : C} {c c' : BinaryBicone P Q}
  证明: by
  cases f
  cases g
  congr
-/
theorem BinaryBiconeMorphism.ext {P Q : C} {c c' : BinaryBicone P Q}
    (f g : c ⟶ c') (w : f.hom = g.hom) : f = g := by
  cases f
  cases g
  congr

namespace BinaryBicones

/-- To give an isomorphism between cocones, it suffices to give an
  isomorphism between their vertices which commutes with the cocone
  maps. -/
@[aesop apply safe (rule_sets := [CategoryTheory]), simps]
/--
Definition of `ext` / `ext` 的定义

English:
definition ext
  signature: {P Q : C} {c c' : BinaryBicone P Q} (φ : c.pt ≅ c'.pt)
  body: { hom := φ.hom }
  inv :=
    { hom := φ.inv
      wfst := φ.inv_comp_eq.mpr wfst.symm
      wsnd := φ.inv_comp_eq.mpr wsnd.symm
      winl := φ.comp_inv_eq.mpr winl.symm
      winr := φ.comp_inv_eq.mpr winr.symm }

中文:
定义 ext
  签名: {P Q : C} {c c' : BinaryBicone P Q} (φ : c.pt ≅ c'.pt)
  定义体: { hom := φ.hom }
  inv :=
    { hom := φ.inv
      wfst := φ.inv_comp_eq.mpr wfst.symm
      wsnd := φ.inv_comp_eq.mpr wsnd.symm
      winl := φ.comp_inv_eq.mpr winl.symm
      winr := φ.comp_inv_eq.mpr winr.symm }

Depends on / 依赖: c.fst, c.inr, c.snd, cat_disch, comp_inv_eq, comp_inv_eq.mpr, inv_comp_eq, inv_comp_eq.mpr, wfst.symm, winl.symm, winr.symm, wsnd.symm
-/
def ext {P Q : C} {c c' : BinaryBicone P Q} (φ : c.pt ≅ c'.pt)
    (winl : c.inl ≫ φ.hom = c'.inl := by cat_disch)
    (winr : c.inr ≫ φ.hom = c'.inr := by cat_disch)
    (wfst : φ.hom ≫ c'.fst = c.fst := by cat_disch)
    (wsnd : φ.hom ≫ c'.snd = c.snd := by cat_disch) : c ≅ c' where
  hom := { hom := φ.hom }
  inv :=
    { hom := φ.inv
      wfst := φ.inv_comp_eq.mpr wfst.symm
      wsnd := φ.inv_comp_eq.mpr wsnd.symm
      winl := φ.comp_inv_eq.mpr winl.symm
      winr := φ.comp_inv_eq.mpr winr.symm }

variable (P Q : C) (F : C ⥤ D) [Functor.PreservesZeroMorphisms F]

/-- A functor `F : C ⥤ D` sends binary bicones for `P` and `Q`
to binary bicones for `G.obj P` and `G.obj Q` functorially. -/
@[simps]
/--
Definition of `functoriality` / `functoriality` 的定义

English:
definition functoriality
  signature: : BinaryBicone P Q ⥤ BinaryBicone (F.obj P) (F.obj Q) where
  body: { pt := F.obj A.pt
      fst := F.map A.fst
      snd := F.map A.snd
      inl := F.map A.inl
      inr := F.map A.inr
      inl_fst := by rw [← F.map_comp, A.inl_fst, F.map_id]
      inl_snd := by rw [← F.map_comp, A.inl_snd, F.map_zero]
      inr_fst := by rw [← F.map_comp, A.inr_fst, F.map_zero]
      inr_snd := by rw [← F.map_comp, A.inr_snd, F.map_id] }
  map f :=
    { hom := F.map f.hom
      wfst := by simp [-BinaryBiconeMorphism.wfst, ← f.wfst]
      wsnd := by simp [-BinaryBiconeMorphism.wsnd, ← f.wsnd]
      winl := by simp [-BinaryBiconeMorphism.winl, ← f.winl]
      winr := by simp [-BinaryBiconeMorphism.winr, ← f.winr] }

中文:
定义 functoriality
  签名: : BinaryBicone P Q ⥤ BinaryBicone (F.obj P) (F.obj Q) where
  定义体: { pt := F.obj A.pt
      fst := F.map A.fst
      snd := F.map A.snd
      inl := F.map A.inl
      inr := F.map A.inr
      inl_fst := by rw [← F.map_comp, A.inl_fst, F.map_id]
      inl_snd := by rw [← F.map_comp, A.inl_snd, F.map_zero]
      inr_fst := by rw [← F.map_comp, A.inr_fst, F.map_zero]
      inr_snd := by rw [← F.map_comp, A.inr_snd, F.map_id] }
  map f :=
    { hom := F.map f.hom
      wfst := by simp [-BinaryBiconeMorphism.wfst, ← f.wfst]
      wsnd := by simp [-BinaryBiconeMorphism.wsnd, ← f.wsnd]
      winl := by simp [-BinaryBiconeMorphism.winl, ← f.winl]
      winr := by simp [-BinaryBiconeMorphism.winr, ← f.winr] }

Depends on / 依赖: A.fst, A.inl, A.inl_fst, A.inl_snd, A.inr, A.inr_fst, A.inr_snd, A.pt, A.snd, BinaryBiconeMorphism, BinaryBiconeMorphism.wfst, BinaryBiconeMorphism.winl, BinaryBiconeMorphism.wsnd, F.map, F.map_comp, F.map_id, F.map_zero, F.obj, f.hom, f.wfst
-/
def functoriality : BinaryBicone P Q ⥤ BinaryBicone (F.obj P) (F.obj Q) where
  obj A :=
    { pt := F.obj A.pt
      fst := F.map A.fst
      snd := F.map A.snd
      inl := F.map A.inl
      inr := F.map A.inr
      inl_fst := by rw [← F.map_comp, A.inl_fst, F.map_id]
      inl_snd := by rw [← F.map_comp, A.inl_snd, F.map_zero]
      inr_fst := by rw [← F.map_comp, A.inr_fst, F.map_zero]
      inr_snd := by rw [← F.map_comp, A.inr_snd, F.map_id] }
  map f :=
    { hom := F.map f.hom
      wfst := by simp [-BinaryBiconeMorphism.wfst, ← f.wfst]
      wsnd := by simp [-BinaryBiconeMorphism.wsnd, ← f.wsnd]
      winl := by simp [-BinaryBiconeMorphism.winl, ← f.winl]
      winr := by simp [-BinaryBiconeMorphism.winr, ← f.winr] }

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `functoriality_full` / 实例 `functoriality_full`

English:
instance functoriality_full
  signature: [F.Full] [F.Faithful]
  body: ⟨{ hom := F.preimage t.hom
      winl := F.map_injective (by simpa using! t.winl)
      winr := F.map_injective (by simpa using! t.winr)
      wfst := F.map_injective (by simpa using! t.wfst)
      wsnd := F.map_injective (by simpa using! t.wsnd) }, by cat_disch⟩

中文:
实例 functoriality_full
  签名: [F.满] [F.忠实]
  定义体: ⟨{ hom := F.preimage t.hom
      winl := F.map_injective (by simpa using! t.winl)
      winr := F.map_injective (by simpa using! t.winr)
      wfst := F.map_injective (by simpa using! t.wfst)
      wsnd := F.map_injective (by simpa using! t.wsnd) }, by cat_disch⟩

Depends on / 依赖: F.map_injective, F.preimage, cat_disch, map_injective, preimage, t.hom, t.wfst, t.winl, t.winr, t.wsnd
-/
instance functoriality_full [F.Full] [F.Faithful] : (functoriality P Q F).Full where
  map_surjective t :=
   ⟨{ hom := F.preimage t.hom
      winl := F.map_injective (by simpa using! t.winl)
      winr := F.map_injective (by simpa using! t.winr)
      wfst := F.map_injective (by simpa using! t.wfst)
      wsnd := F.map_injective (by simpa using! t.wsnd) }, by cat_disch⟩

/--
Instance `functoriality_faithful` / 实例 `functoriality_faithful`

English:
instance functoriality_faithful
  signature: [F.Faithful]
  body: BinaryBiconeMorphism.ext f g F.map_injective congr_arg BinaryBiconeMorphism.hom h

中文:
实例 functoriality_faithful
  签名: [F.忠实]
  定义体: BinaryBiconeMorphism.ext f g F.map_injective congr_arg BinaryBiconeMorphism.hom h

Depends on / 依赖: BinaryBiconeMorphism, BinaryBiconeMorphism.ext, BinaryBiconeMorphism.hom, F.map_injective, congr_arg, map_injective
-/
instance functoriality_faithful [F.Faithful] : (functoriality P Q F).Faithful where
  map_injective {_X} {_Y} f g h :=
BinaryBiconeMorphism.ext f g F.map_injective congr_arg BinaryBiconeMorphism.hom h

end BinaryBicones

namespace BinaryBicone

variable {P P' Q Q' : C}

/--
Definition of `toCone` / `toCone` 的定义

English:
definition toCone
  signature: (c : BinaryBicone P Q)
  body: BinaryFan.mk c.fst c.snd

@[simp]

中文:
定义 toCone
  签名: (c : BinaryBicone P Q)
  定义体: BinaryFan.mk c.fst c.snd

@[simp]

Depends on / 依赖: BinaryFan, BinaryFan.mk, c.fst, c.snd
-/
def toCone (c : BinaryBicone P Q) : Cone (pair P Q) :=
  BinaryFan.mk c.fst c.snd

@[simp]
/--
theorem `toCone_pt` / 定理 `toCone_pt`

English:
theorem toCone_pt
  given: (c : BinaryBicone P Q)
  statement: c.toCone.pt = c.pt
  proof: rfl

@[simp]

中文:
定理 toCone_pt
  条件: (c : BinaryBicone P Q)
  结论: c.toCone.pt = c.pt
  证明: rfl

@[simp]
-/
theorem toCone_pt (c : BinaryBicone P Q) : c.toCone.pt = c.pt := rfl

@[simp]
/--
theorem `toCone_π_app_left` / 定理 `toCone_π_app_left`

English:
theorem toCone_π_app_left
  given: (c : BinaryBicone P Q)
  statement: c.toCone.π.app ⟨WalkingPair.left⟩ = c.fst
  proof: rfl

@[simp]

中文:
定理 toCone_π_app_left
  条件: (c : BinaryBicone P Q)
  结论: c.toCone.π.app ⟨WalkingPair.left⟩ = c.fst
  证明: rfl

@[simp]
-/
theorem toCone_π_app_left (c : BinaryBicone P Q) : c.toCone.π.app ⟨WalkingPair.left⟩ = c.fst :=
  rfl

@[simp]
/--
theorem `toCone_π_app_right` / 定理 `toCone_π_app_right`

English:
theorem toCone_π_app_right
  given: (c : BinaryBicone P Q)
  statement: c.toCone.π.app ⟨WalkingPair.right⟩ = c.snd
  proof: rfl

@[simp]

中文:
定理 toCone_π_app_right
  条件: (c : BinaryBicone P Q)
  结论: c.toCone.π.app ⟨WalkingPair.right⟩ = c.snd
  证明: rfl

@[simp]
-/
theorem toCone_π_app_right (c : BinaryBicone P Q) : c.toCone.π.app ⟨WalkingPair.right⟩ = c.snd :=
  rfl

@[simp]
/--
theorem `binary_fan_fst_toCone` / 定理 `binary_fan_fst_toCone`

English:
theorem binary_fan_fst_toCone
  given: (c : BinaryBicone P Q)
  statement: BinaryFan.fst c.toCone = c.fst
  proof: rfl

@[simp]

中文:
定理 binary_fan_fst_toCone
  条件: (c : BinaryBicone P Q)
  结论: BinaryFan.fst c.toCone = c.fst
  证明: rfl

@[simp]
-/
theorem binary_fan_fst_toCone (c : BinaryBicone P Q) : BinaryFan.fst c.toCone = c.fst := rfl

@[simp]
/--
theorem `binary_fan_snd_toCone` / 定理 `binary_fan_snd_toCone`

English:
theorem binary_fan_snd_toCone
  given: (c : BinaryBicone P Q)
  statement: BinaryFan.snd c.toCone = c.snd
  proof: rfl

中文:
定理 binary_fan_snd_toCone
  条件: (c : BinaryBicone P Q)
  结论: BinaryFan.snd c.toCone = c.snd
  证明: rfl
-/
theorem binary_fan_snd_toCone (c : BinaryBicone P Q) : BinaryFan.snd c.toCone = c.snd := rfl

/--
Definition of `toCocone` / `toCocone` 的定义

English:
definition toCocone
  signature: (c : BinaryBicone P Q)
  body: BinaryCofan.mk c.inl c.inr

@[simp]

中文:
定义 toCocone
  签名: (c : BinaryBicone P Q)
  定义体: BinaryCofan.mk c.inl c.inr

@[simp]

Depends on / 依赖: BinaryCofan, BinaryCofan.mk, c.inl, c.inr
-/
def toCocone (c : BinaryBicone P Q) : Cocone (pair P Q) := BinaryCofan.mk c.inl c.inr

@[simp]
/--
theorem `toCocone_pt` / 定理 `toCocone_pt`

English:
theorem toCocone_pt
  given: (c : BinaryBicone P Q)
  statement: c.toCocone.pt = c.pt
  proof: rfl

@[simp]

中文:
定理 toCocone_pt
  条件: (c : BinaryBicone P Q)
  结论: c.toCocone.pt = c.pt
  证明: rfl

@[simp]
-/
theorem toCocone_pt (c : BinaryBicone P Q) : c.toCocone.pt = c.pt := rfl

@[simp]
/--
theorem `toCocone_ι_app_left` / 定理 `toCocone_ι_app_left`

English:
theorem toCocone_ι_app_left
  given: (c : BinaryBicone P Q)
  statement: c.toCocone.ι.app ⟨WalkingPair.left⟩ = c.inl
  proof: rfl

@[simp]

中文:
定理 toCocone_ι_app_left
  条件: (c : BinaryBicone P Q)
  结论: c.toCocone.ι.app ⟨WalkingPair.left⟩ = c.inl
  证明: rfl

@[simp]
-/
theorem toCocone_ι_app_left (c : BinaryBicone P Q) : c.toCocone.ι.app ⟨WalkingPair.left⟩ = c.inl :=
  rfl

@[simp]
/--
theorem `toCocone_ι_app_right` / 定理 `toCocone_ι_app_right`

English:
theorem toCocone_ι_app_right
  given: (c : BinaryBicone P Q)
  proof: rfl

@[simp]

中文:
定理 toCocone_ι_app_right
  条件: (c : BinaryBicone P Q)
  证明: rfl

@[simp]
-/
theorem toCocone_ι_app_right (c : BinaryBicone P Q) :
    c.toCocone.ι.app ⟨WalkingPair.right⟩ = c.inr := rfl

@[simp]
/--
theorem `binary_cofan_inl_toCocone` / 定理 `binary_cofan_inl_toCocone`

English:
theorem binary_cofan_inl_toCocone
  given: (c : BinaryBicone P Q)
  statement: BinaryCofan.inl c.toCocone = c.inl
  proof: rfl

@[simp]

中文:
定理 binary_cofan_inl_toCocone
  条件: (c : BinaryBicone P Q)
  结论: BinaryCofan.inl c.toCocone = c.inl
  证明: rfl

@[simp]
-/
theorem binary_cofan_inl_toCocone (c : BinaryBicone P Q) : BinaryCofan.inl c.toCocone = c.inl :=
  rfl

@[simp]
/--
theorem `binary_cofan_inr_toCocone` / 定理 `binary_cofan_inr_toCocone`

English:
theorem binary_cofan_inr_toCocone
  given: (c : BinaryBicone P Q)
  statement: BinaryCofan.inr c.toCocone = c.inr
  proof: rfl

中文:
定理 binary_cofan_inr_toCocone
  条件: (c : BinaryBicone P Q)
  结论: BinaryCofan.inr c.toCocone = c.inr
  证明: rfl
-/
theorem binary_cofan_inr_toCocone (c : BinaryBicone P Q) : BinaryCofan.inr c.toCocone = c.inr :=
  rfl

/--
Definition of `retract_left` / `retract_left` 的定义

English:
definition retract_left
  signature: (c : BinaryBicone P Q)
  body: c.inl
  r := c.fst

中文:
定义 retract_left
  签名: (c : BinaryBicone P Q)
  定义体: c.inl
  r := c.fst

Depends on / 依赖: c.inl
-/
def retract_left (c : BinaryBicone P Q) : Retract P c.pt where
  i := c.inl
  r := c.fst

/--
Definition of `retract_right` / `retract_right` 的定义

English:
definition retract_right
  signature: (c : BinaryBicone P Q)
  body: c.inr
  r := c.snd

中文:
定义 retract_right
  签名: (c : BinaryBicone P Q)
  定义体: c.inr
  r := c.snd

Depends on / 依赖: c.inr
-/
def retract_right (c : BinaryBicone P Q) : Retract Q c.pt where
  i := c.inr
  r := c.snd

instance (c : BinaryBicone P Q) : IsSplitMono c.inl := c.retract_left.instIsSplitMonoI

instance (c : BinaryBicone P Q) : IsSplitMono c.inr := c.retract_right.instIsSplitMonoI

instance (c : BinaryBicone P Q) : IsSplitEpi c.fst := c.retract_left.instIsSplitEpiR

instance (c : BinaryBicone P Q) : IsSplitEpi c.snd := c.retract_right.instIsSplitEpiR

set_option backward.isDefEq.respectTransparency false in
/-- Convert a `BinaryBicone` into a `Bicone` over a pair. -/
@[simps]
/--
Definition of `toBiconeFunctor` / `toBiconeFunctor` 的定义

English:
definition toBiconeFunctor
  signature: {X Y : C}
  body: { pt := b.pt
      π := fun j => WalkingPair.casesOn j b.fst b.snd
      ι := fun j => WalkingPair.casesOn j b.inl b.inr
      ι_π := fun j j' => by
        rcases j with ⟨⟩ <;> rcases j' with ⟨⟩ <;> simp }
  map f := {
    hom := f.hom
    wπ := fun i => WalkingPair.casesOn i f.wfst f.wsnd
    wι := fun i => WalkingPair.casesOn i f.winl f.winr }

中文:
定义 toBiconeFunctor
  签名: {X Y : C}
  定义体: { pt := b.pt
      π := fun j => WalkingPair.casesOn j b.fst b.snd
      ι := fun j => WalkingPair.casesOn j b.inl b.inr
      ι_π := fun j j' => by
        rcases j with ⟨⟩ <;> rcases j' with ⟨⟩ <;> simp }
  map f := {
    hom := f.hom
    wπ := fun i => WalkingPair.casesOn i f.wfst f.wsnd
    wι := fun i => WalkingPair.casesOn i f.winl f.winr }

Depends on / 依赖: WalkingPair, WalkingPair.casesOn, b.fst, b.inl, b.inr, b.pt, b.snd, casesOn, f.hom, f.wfst, f.winl, f.winr, f.wsnd
-/
def toBiconeFunctor {X Y : C} : BinaryBicone X Y ⥤ Bicone (pairFunction X Y) where
  obj b :=
    { pt := b.pt
      π := fun j => WalkingPair.casesOn j b.fst b.snd
      ι := fun j => WalkingPair.casesOn j b.inl b.inr
      ι_π := fun j j' => by
        rcases j with ⟨⟩ <;> rcases j' with ⟨⟩ <;> simp }
  map f := {
    hom := f.hom
    wπ := fun i => WalkingPair.casesOn i f.wfst f.wsnd
    wι := fun i => WalkingPair.casesOn i f.winl f.winr }

/--
Definition of `toBicone` / `toBicone` 的定义

English:
abbreviation toBicone
  signature: {X Y : C} (b : BinaryBicone X Y)
  body: toBiconeFunctor.obj b

中文:
缩写 toBicone
  签名: {X Y : C} (b : BinaryBicone X Y)
  定义体: toBiconeFunctor.obj b

Depends on / 依赖: toBiconeFunctor, toBiconeFunctor.obj
-/
abbrev toBicone {X Y : C} (b : BinaryBicone X Y) : Bicone (pairFunction X Y) :=
  toBiconeFunctor.obj b

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `toBiconeIsLimit` / `toBiconeIsLimit` 的定义

English:
definition toBiconeIsLimit
  signature: {X Y : C} (b : BinaryBicone X Y)
  body: IsLimit.equivIsoLimit Cone.ext (Iso.refl _) fun ⟨as⟩ => by cases as <;> simp

中文:
定义 toBiconeIsLimit
  签名: {X Y : C} (b : BinaryBicone X Y)
  定义体: IsLimit.equivIsoLimit Cone.ext (Iso.refl _) fun ⟨as⟩ => by cases as <;> simp

Depends on / 依赖: Cone.ext, IsLimit, IsLimit.equivIsoLimit, Iso.refl, equivIsoLimit
-/
def toBiconeIsLimit {X Y : C} (b : BinaryBicone X Y) :
    IsLimit b.toBicone.toCone ≃ IsLimit b.toCone :=
IsLimit.equivIsoLimit Cone.ext (Iso.refl _) fun ⟨as⟩ => by cases as <;> simp

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `toBiconeIsColimit` / `toBiconeIsColimit` 的定义

English:
definition toBiconeIsColimit
  signature: {X Y : C} (b : BinaryBicone X Y)
  body: IsColimit.equivIsoColimit Cocone.ext (Iso.refl _) fun ⟨as⟩ => by cases as <;> simp

中文:
定义 toBiconeIsColimit
  签名: {X Y : C} (b : BinaryBicone X Y)
  定义体: IsColimit.equivIsoColimit Cocone.ext (Iso.refl _) fun ⟨as⟩ => by cases as <;> simp

Depends on / 依赖: Cocone, Cocone.ext, IsColimit, IsColimit.equivIsoColimit, Iso.refl, equivIsoColimit
-/
def toBiconeIsColimit {X Y : C} (b : BinaryBicone X Y) :
    IsColimit b.toBicone.toCocone ≃ IsColimit b.toCocone :=
IsColimit.equivIsoColimit Cocone.ext (Iso.refl _) fun ⟨as⟩ => by cases as <;> simp

/-- Transport a binary bicone via isomorphisms. -/
@[simps]
/--
Definition of `ofIso` / `ofIso` 的定义

English:
definition ofIso
  signature: (b : BinaryBicone P Q) (eP : P ≅ P') (eQ : Q ≅ Q')
  body: b.pt
  fst := b.fst ≫ eP.hom
  snd := b.snd ≫ eQ.hom
  inl := eP.inv ≫ b.inl
  inr := eQ.inv ≫ b.inr

中文:
定义 ofIso
  签名: (b : BinaryBicone P Q) (eP : P ≅ P') (eQ : Q ≅ Q')
  定义体: b.pt
  fst := b.fst ≫ eP.hom
  snd := b.snd ≫ eQ.hom
  inl := eP.inv ≫ b.inl
  inr := eQ.inv ≫ b.inr

Depends on / 依赖: b.pt
-/
def ofIso (b : BinaryBicone P Q) (eP : P ≅ P') (eQ : Q ≅ Q') :
    BinaryBicone P' Q' where
  pt := b.pt
  fst := b.fst ≫ eP.hom
  snd := b.snd ≫ eQ.hom
  inl := eP.inv ≫ b.inl
  inr := eQ.inv ≫ b.inr

attribute [local simp←] op_comp in
/-- The opposite of a binary bicone. -/
@[simps]
/--
Definition of `op` / `op` 的定义

English:
definition op
  signature: (b : BinaryBicone P Q)
  body: Opposite.op b.pt
  fst := b.inl.op
  snd := b.inr.op
  inl := b.fst.op
  inr := b.snd.op

中文:
定义 op
  签名: (b : BinaryBicone P Q)
  定义体: Opposite.op b.pt
  fst := b.inl.op
  snd := b.inr.op
  inl := b.fst.op
  inr := b.snd.op
-/
protected def op (b : BinaryBicone P Q) :
    BinaryBicone (op P) (op Q) where
  pt := Opposite.op b.pt
  fst := b.inl.op
  snd := b.inr.op
  inl := b.fst.op
  inr := b.snd.op

end BinaryBicone

namespace Bicone

set_option backward.isDefEq.respectTransparency false in
/-- Convert a `Bicone` over a function on `WalkingPair` to a BinaryBicone. -/
@[simps]
/--
Definition of `toBinaryBiconeFunctor` / `toBinaryBiconeFunctor` 的定义

English:
definition toBinaryBiconeFunctor
  signature: {X Y : C}
  body: { pt := b.pt
      fst := b.π WalkingPair.left
      snd := b.π WalkingPair.right
      inl := b.ι WalkingPair.left
      inr := b.ι WalkingPair.right
      inl_fst := by simp
      inr_fst := by simp
      inl_snd := by simp
      inr_snd := by simp }
  map f :=
    { hom := f.hom }

中文:
定义 toBinaryBiconeFunctor
  签名: {X Y : C}
  定义体: { pt := b.pt
      fst := b.π WalkingPair.left
      snd := b.π WalkingPair.right
      inl := b.ι WalkingPair.left
      inr := b.ι WalkingPair.right
      inl_fst := by simp
      inr_fst := by simp
      inl_snd := by simp
      inr_snd := by simp }
  map f :=
    { hom := f.hom }

Depends on / 依赖: WalkingPair, WalkingPair.left, WalkingPair.right, b.pt, f.hom, inl_fst, inl_snd, inr_fst, inr_snd
-/
def toBinaryBiconeFunctor {X Y : C} : Bicone (pairFunction X Y) ⥤ BinaryBicone X Y where
  obj b :=
    { pt := b.pt
      fst := b.π WalkingPair.left
      snd := b.π WalkingPair.right
      inl := b.ι WalkingPair.left
      inr := b.ι WalkingPair.right
      inl_fst := by simp
      inr_fst := by simp
      inl_snd := by simp
      inr_snd := by simp }
  map f :=
    { hom := f.hom }

/--
Definition of `toBinaryBicone` / `toBinaryBicone` 的定义

English:
abbreviation toBinaryBicone
  signature: {X Y : C} (b : Bicone (pairFunction X Y))
  body: toBinaryBiconeFunctor.obj b

中文:
缩写 toBinaryBicone
  签名: {X Y : C} (b : Bicone (pairFunction X Y))
  定义体: toBinaryBiconeFunctor.obj b

Depends on / 依赖: toBinaryBiconeFunctor, toBinaryBiconeFunctor.obj
-/
abbrev toBinaryBicone {X Y : C} (b : Bicone (pairFunction X Y)) : BinaryBicone X Y :=
  toBinaryBiconeFunctor.obj b

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `toBinaryBiconeIsLimit` / `toBinaryBiconeIsLimit` 的定义

English:
definition toBinaryBiconeIsLimit
  signature: {X Y : C} (b : Bicone (pairFunction X Y))
  body: IsLimit.equivIsoLimit Cone.ext (Iso.refl _) fun j => by rcases j with ⟨⟨⟩⟩ <;> simp

中文:
定义 toBinaryBiconeIsLimit
  签名: {X Y : C} (b : Bicone (pairFunction X Y))
  定义体: IsLimit.equivIsoLimit Cone.ext (Iso.refl _) fun j => by rcases j with ⟨⟨⟩⟩ <;> simp

Depends on / 依赖: Cone.ext, IsLimit, IsLimit.equivIsoLimit, Iso.refl, equivIsoLimit
-/
def toBinaryBiconeIsLimit {X Y : C} (b : Bicone (pairFunction X Y)) :
    IsLimit b.toBinaryBicone.toCone ≃ IsLimit b.toCone :=
IsLimit.equivIsoLimit Cone.ext (Iso.refl _) fun j => by rcases j with ⟨⟨⟩⟩ <;> simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `toBinaryBiconeIsColimit` / `toBinaryBiconeIsColimit` 的定义

English:
definition toBinaryBiconeIsColimit
  signature: {X Y : C} (b : Bicone (pairFunction X Y))
  body: IsColimit.equivIsoColimit Cocone.ext (Iso.refl _) fun j => by rcases j with ⟨⟨⟩⟩ <;> simp

中文:
定义 toBinaryBiconeIsColimit
  签名: {X Y : C} (b : Bicone (pairFunction X Y))
  定义体: IsColimit.equivIsoColimit Cocone.ext (Iso.refl _) fun j => by rcases j with ⟨⟨⟩⟩ <;> simp

Depends on / 依赖: Cocone, Cocone.ext, IsColimit, IsColimit.equivIsoColimit, Iso.refl, equivIsoColimit
-/
def toBinaryBiconeIsColimit {X Y : C} (b : Bicone (pairFunction X Y)) :
    IsColimit b.toBinaryBicone.toCocone ≃ IsColimit b.toCocone :=
IsColimit.equivIsoColimit Cocone.ext (Iso.refl _) fun j => by rcases j with ⟨⟨⟩⟩ <;> simp

end Bicone

/--
Definition of `BinaryBicone.IsBilimit` / `BinaryBicone.IsBilimit` 的定义

English:
structure BinaryBicone.IsBilimit
  parameters: {P Q : C} (b : BinaryBicone P Q)
  axioms and operations (2):
    - isLimit : IsLimit b.toCone
    - isColimit : IsColimit b.toCocone

中文:
结构 BinaryBicone.是Bilimit
  参数: {P Q : C} (b : BinaryBicone P Q)
  公理与运算 (2 个):
    - isLimit : 是极限 b.toCone
    - isColimit : 是余极限 b.toCocone
-/
structure BinaryBicone.IsBilimit {P Q : C} (b : BinaryBicone P Q) where
  isLimit : IsLimit b.toCone
  isColimit : IsColimit b.toCocone

attribute [inherit_doc BinaryBicone.IsBilimit] BinaryBicone.IsBilimit.isLimit
  BinaryBicone.IsBilimit.isColimit

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `BinaryBicone.IsBilimit.ofIso` / `BinaryBicone.IsBilimit.ofIso` 的定义

English:
definition BinaryBicone.IsBilimit.ofIso
  signature: {P Q P' Q' : C} {b : BinaryBicone P Q} (hb : b.IsBilimit)
  body: by
    refine (IsLimit.equivOfNatIsoOfIso (mapPairIso eP eQ) _ _ ?_).1 hb.isLimit
    exact BinaryFan.ext (Iso.refl _) (by simp [BinaryFan.fst])
      (by simp [BinaryFan.snd])
  isColimit := by
    refine (IsColimit.equivOfNatIsoOfIso (mapPairIso eP eQ) _ _ ?_).1 hb.isColimit
    exact BinaryCofan.ext (Iso.refl _) (by simp [BinaryCofan.inl])
      (by simp [BinaryCofan.inr])

中文:
定义 BinaryBicone.是Bilimit.ofIso
  签名: {P Q P' Q' : C} {b : BinaryBicone P Q} (hb : b.是Bilimit)
  定义体: by
    refine (IsLimit.equivOfNatIsoOfIso (mapPairIso eP eQ) _ _ ?_).1 hb.isLimit
    exact BinaryFan.ext (Iso.refl _) (by simp [BinaryFan.fst])
      (by simp [BinaryFan.snd])
  isColimit := by
    refine (IsColimit.equivOfNatIsoOfIso (mapPairIso eP eQ) _ _ ?_).1 hb.isColimit
    exact BinaryCofan.ext (Iso.refl _) (by simp [BinaryCofan.inl])
      (by simp [BinaryCofan.inr])

Depends on / 依赖: BinaryCofan, BinaryCofan.ext, BinaryCofan.inl, BinaryCofan.inr, BinaryFan, BinaryFan.ext, BinaryFan.fst, BinaryFan.snd, IsColimit, IsColimit.equivOfNatIsoOfIso, IsLimit, IsLimit.equivOfNatIsoOfIso, Iso.refl, equivOfNatIsoOfIso, hb.isColimit, hb.isLimit, isColimit, isLimit, mapPairIso
-/
def BinaryBicone.IsBilimit.ofIso {P Q P' Q' : C} {b : BinaryBicone P Q} (hb : b.IsBilimit)
    (eP : P ≅ P') (eQ : Q ≅ Q') :
    (b.ofIso eP eQ).IsBilimit where
  isLimit := by
    refine (IsLimit.equivOfNatIsoOfIso (mapPairIso eP eQ) _ _ ?_).1 hb.isLimit
    exact BinaryFan.ext (Iso.refl _) (by simp [BinaryFan.fst])
      (by simp [BinaryFan.snd])
  isColimit := by
    refine (IsColimit.equivOfNatIsoOfIso (mapPairIso eP eQ) _ _ ?_).1 hb.isColimit
    exact BinaryCofan.ext (Iso.refl _) (by simp [BinaryCofan.inl])
      (by simp [BinaryCofan.inr])

/--
Definition of `BinaryBicone.IsBilimit.op` / `BinaryBicone.IsBilimit.op` 的定义

English:
definition BinaryBicone.IsBilimit.op
  signature: {P Q : C} {b : BinaryBicone P Q} (h : b.IsBilimit)
  body: BinaryCofan.IsColimit.op h.isColimit
  isColimit := BinaryFan.IsLimit.op h.isLimit

中文:
定义 BinaryBicone.是Bilimit.op
  签名: {P Q : C} {b : BinaryBicone P Q} (h : b.是Bilimit)
  定义体: BinaryCofan.IsColimit.op h.isColimit
  isColimit := BinaryFan.IsLimit.op h.isLimit
-/
protected def BinaryBicone.IsBilimit.op {P Q : C} {b : BinaryBicone P Q} (h : b.IsBilimit) :
    b.op.IsBilimit where
  isLimit := BinaryCofan.IsColimit.op h.isColimit
  isColimit := BinaryFan.IsLimit.op h.isLimit

/--
Definition of `BinaryBicone.toBiconeIsBilimit` / `BinaryBicone.toBiconeIsBilimit` 的定义

English:
definition BinaryBicone.toBiconeIsBilimit
  signature: {X Y : C} (b : BinaryBicone X Y)
  body: ⟨b.toBiconeIsLimit h.isLimit, b.toBiconeIsColimit h.isColimit⟩
  invFun h := ⟨b.toBiconeIsLimit.symm h.isLimit, b.toBiconeIsColimit.symm h.isColimit⟩
  left_inv := fun ⟨h, h'⟩ => by dsimp only; simp
  right_inv := fun ⟨h, h'⟩ => by dsimp only; simp

中文:
定义 BinaryBicone.toBiconeIsBilimit
  签名: {X Y : C} (b : BinaryBicone X Y)
  定义体: ⟨b.toBiconeIsLimit h.isLimit, b.toBiconeIsColimit h.isColimit⟩
  invFun h := ⟨b.toBiconeIsLimit.symm h.isLimit, b.toBiconeIsColimit.symm h.isColimit⟩
  left_inv := fun ⟨h, h'⟩ => by dsimp only; simp
  right_inv := fun ⟨h, h'⟩ => by dsimp only; simp

Depends on / 依赖: b.toBiconeIsColimit, b.toBiconeIsLimit, h.isColimit, h.isLimit, isColimit, isLimit, toBiconeIsColimit, toBiconeIsLimit
-/
def BinaryBicone.toBiconeIsBilimit {X Y : C} (b : BinaryBicone X Y) :
    b.toBicone.IsBilimit ≃ b.IsBilimit where
  toFun h := ⟨b.toBiconeIsLimit h.isLimit, b.toBiconeIsColimit h.isColimit⟩
  invFun h := ⟨b.toBiconeIsLimit.symm h.isLimit, b.toBiconeIsColimit.symm h.isColimit⟩
  left_inv := fun ⟨h, h'⟩ => by dsimp only; simp
  right_inv := fun ⟨h, h'⟩ => by dsimp only; simp

/--
Definition of `Bicone.toBinaryBiconeIsBilimit` / `Bicone.toBinaryBiconeIsBilimit` 的定义

English:
definition Bicone.toBinaryBiconeIsBilimit
  signature: {X Y : C} (b : Bicone (pairFunction X Y))
  body: ⟨b.toBinaryBiconeIsLimit h.isLimit, b.toBinaryBiconeIsColimit h.isColimit⟩
  invFun h := ⟨b.toBinaryBiconeIsLimit.symm h.isLimit, b.toBinaryBiconeIsColimit.symm h.isColimit⟩
  left_inv := fun ⟨h, h'⟩ => by dsimp only; simp
  right_inv := fun ⟨h, h'⟩ => by dsimp only; simp

中文:
定义 Bicone.toBinaryBiconeIsBilimit
  签名: {X Y : C} (b : Bicone (pairFunction X Y))
  定义体: ⟨b.toBinaryBiconeIsLimit h.isLimit, b.toBinaryBiconeIsColimit h.isColimit⟩
  invFun h := ⟨b.toBinaryBiconeIsLimit.symm h.isLimit, b.toBinaryBiconeIsColimit.symm h.isColimit⟩
  left_inv := fun ⟨h, h'⟩ => by dsimp only; simp
  right_inv := fun ⟨h, h'⟩ => by dsimp only; simp

Depends on / 依赖: b.toBinaryBiconeIsColimit, b.toBinaryBiconeIsLimit, h.isColimit, h.isLimit, isColimit, isLimit, toBinaryBiconeIsColimit, toBinaryBiconeIsLimit
-/
def Bicone.toBinaryBiconeIsBilimit {X Y : C} (b : Bicone (pairFunction X Y)) :
    b.toBinaryBicone.IsBilimit ≃ b.IsBilimit where
  toFun h := ⟨b.toBinaryBiconeIsLimit h.isLimit, b.toBinaryBiconeIsColimit h.isColimit⟩
  invFun h := ⟨b.toBinaryBiconeIsLimit.symm h.isLimit, b.toBinaryBiconeIsColimit.symm h.isColimit⟩
  left_inv := fun ⟨h, h'⟩ => by dsimp only; simp
  right_inv := fun ⟨h, h'⟩ => by dsimp only; simp

/--
Definition of `BinaryBiproductData` / `BinaryBiproductData` 的定义

English:
structure BinaryBiproductData
  parameters: (P Q : C)
  axioms and operations (2):
    - bicone : BinaryBicone P Q
    - isBilimit : bicone.IsBilimit

中文:
结构 BinaryBiproductData
  参数: (P Q : C)
  公理与运算 (2 个):
    - bicone : BinaryBicone P Q
    - isBilimit : bicone.是Bilimit
-/
structure BinaryBiproductData (P Q : C) where
  bicone : BinaryBicone P Q
  isBilimit : bicone.IsBilimit

initialize_simps_projections BinaryBiproductData (-isBilimit)

attribute [inherit_doc BinaryBiproductData] BinaryBiproductData.bicone
  BinaryBiproductData.isBilimit

/-- Transport a binary bicone data via isomorphisms. -/
@[simps]
/--
Definition of `BinaryBiproductData.ofIso` / `BinaryBiproductData.ofIso` 的定义

English:
definition BinaryBiproductData.ofIso
  signature: {P Q P' Q' : C} (d : BinaryBiproductData P Q)
  body: d.bicone.ofIso eP eQ
  isBilimit := d.isBilimit.ofIso _ _

中文:
定义 BinaryBiproductData.ofIso
  签名: {P Q P' Q' : C} (d : BinaryBiproductData P Q)
  定义体: d.bicone.ofIso eP eQ
  isBilimit := d.isBilimit.ofIso _ _

Depends on / 依赖: bicone, d.bicone.ofIso
-/
def BinaryBiproductData.ofIso {P Q P' Q' : C} (d : BinaryBiproductData P Q)
    (eP : P ≅ P') (eQ : Q ≅ Q') :
    BinaryBiproductData P' Q' where
  bicone := d.bicone.ofIso eP eQ
  isBilimit := d.isBilimit.ofIso _ _

/-- The opposite of a binary biproduct data. -/
@[simps]
/--
Definition of `BinaryBiproductData.op` / `BinaryBiproductData.op` 的定义

English:
definition BinaryBiproductData.op
  signature: {P Q : C} (d : BinaryBiproductData P Q)
  body: d.bicone.op
  isBilimit := d.isBilimit.op

中文:
定义 BinaryBiproductData.op
  签名: {P Q : C} (d : BinaryBiproductData P Q)
  定义体: d.bicone.op
  isBilimit := d.isBilimit.op
-/
protected def BinaryBiproductData.op {P Q : C} (d : BinaryBiproductData P Q) :
    BinaryBiproductData (op P) (op Q) where
  bicone := d.bicone.op
  isBilimit := d.isBilimit.op

/--
Definition of `HasBinaryBiproduct` / `HasBinaryBiproduct` 的定义

English:
class HasBinaryBiproduct
  parameters: (P Q : C)
  (no additional axioms)

中文:
类 有BinaryBiproduct
  参数: (P Q : C)
  (无附加公理)
-/
class HasBinaryBiproduct (P Q : C) : Prop where mk' ::
  exists_binary_biproduct : Nonempty (BinaryBiproductData P Q)

attribute [inherit_doc HasBinaryBiproduct] HasBinaryBiproduct.exists_binary_biproduct

/--
theorem `HasBinaryBiproduct.mk` / 定理 `HasBinaryBiproduct.mk`

English:
theorem HasBinaryBiproduct.mk
  given: {P Q : C} (d : BinaryBiproductData P Q)
  statement: HasBinaryBiproduct P Q
  proof: ⟨Nonempty.intro d⟩

中文:
定理 有BinaryBiproduct.mk
  条件: {P Q : C} (d : BinaryBiproductData P Q)
  结论: 有BinaryBiproduct P Q
  证明: ⟨Nonempty.intro d⟩

Depends on / 依赖: Nonempty, Nonempty.intro
-/
theorem HasBinaryBiproduct.mk {P Q : C} (d : BinaryBiproductData P Q) : HasBinaryBiproduct P Q :=
  ⟨Nonempty.intro d⟩

/--
Definition of `getBinaryBiproductData` / `getBinaryBiproductData` 的定义

English:
definition getBinaryBiproductData
  signature: (P Q : C) [HasBinaryBiproduct P Q]
  body: Classical.choice HasBinaryBiproduct.exists_binary_biproduct

中文:
定义 getBinaryBiproductData
  签名: (P Q : C) [有BinaryBiproduct P Q]
  定义体: Classical.choice HasBinaryBiproduct.exists_binary_biproduct

Depends on / 依赖: Classical, Classical.choice, HasBinaryBiproduct, HasBinaryBiproduct.exists_binary_biproduct, choice, exists_binary_biproduct
-/
def getBinaryBiproductData (P Q : C) [HasBinaryBiproduct P Q] : BinaryBiproductData P Q :=
  Classical.choice HasBinaryBiproduct.exists_binary_biproduct

/--
Definition of `BinaryBiproduct.bicone` / `BinaryBiproduct.bicone` 的定义

English:
definition BinaryBiproduct.bicone
  signature: (P Q : C) [HasBinaryBiproduct P Q]
  body: (getBinaryBiproductData P Q).bicone

中文:
定义 BinaryBiproduct.bicone
  签名: (P Q : C) [有BinaryBiproduct P Q]
  定义体: (getBinaryBiproductData P Q).bicone

Depends on / 依赖: bicone, getBinaryBiproductData
-/
def BinaryBiproduct.bicone (P Q : C) [HasBinaryBiproduct P Q] : BinaryBicone P Q :=
  (getBinaryBiproductData P Q).bicone

/--
Definition of `BinaryBiproduct.isBilimit` / `BinaryBiproduct.isBilimit` 的定义

English:
definition BinaryBiproduct.isBilimit
  signature: (P Q : C) [HasBinaryBiproduct P Q]
  body: (getBinaryBiproductData P Q).isBilimit

中文:
定义 BinaryBiproduct.isBilimit
  签名: (P Q : C) [有BinaryBiproduct P Q]
  定义体: (getBinaryBiproductData P Q).isBilimit

Depends on / 依赖: getBinaryBiproductData, isBilimit
-/
def BinaryBiproduct.isBilimit (P Q : C) [HasBinaryBiproduct P Q] :
    (BinaryBiproduct.bicone P Q).IsBilimit :=
  (getBinaryBiproductData P Q).isBilimit

/--
Definition of `BinaryBiproduct.isLimit` / `BinaryBiproduct.isLimit` 的定义

English:
definition BinaryBiproduct.isLimit
  signature: (P Q : C) [HasBinaryBiproduct P Q]
  body: (getBinaryBiproductData P Q).isBilimit.isLimit

中文:
定义 BinaryBiproduct.isLimit
  签名: (P Q : C) [有BinaryBiproduct P Q]
  定义体: (getBinaryBiproductData P Q).isBilimit.isLimit

Depends on / 依赖: getBinaryBiproductData, isBilimit, isBilimit.isLimit, isLimit
-/
def BinaryBiproduct.isLimit (P Q : C) [HasBinaryBiproduct P Q] :
    IsLimit (BinaryBiproduct.bicone P Q).toCone :=
  (getBinaryBiproductData P Q).isBilimit.isLimit

/--
Definition of `BinaryBiproduct.isColimit` / `BinaryBiproduct.isColimit` 的定义

English:
definition BinaryBiproduct.isColimit
  signature: (P Q : C) [HasBinaryBiproduct P Q]
  body: (getBinaryBiproductData P Q).isBilimit.isColimit

中文:
定义 BinaryBiproduct.isColimit
  签名: (P Q : C) [有BinaryBiproduct P Q]
  定义体: (getBinaryBiproductData P Q).isBilimit.isColimit

Depends on / 依赖: getBinaryBiproductData, isBilimit, isBilimit.isColimit, isColimit
-/
def BinaryBiproduct.isColimit (P Q : C) [HasBinaryBiproduct P Q] :
    IsColimit (BinaryBiproduct.bicone P Q).toCocone :=
  (getBinaryBiproductData P Q).isBilimit.isColimit

/--
lemma `hasBinaryBiproduct_of_iso` / 引理 `hasBinaryBiproduct_of_iso`

English:
lemma hasBinaryBiproduct_of_iso
  statement: {P Q P' Q' : C} [HasBinaryBiproduct P Q]
  proof: ⟨(getBinaryBiproductData P Q).ofIso eP eQ⟩

中文:
引理 hasBinaryBiproduct_of_iso
  结论: {P Q P' Q' : C} [有BinaryBiproduct P Q]
  证明: ⟨(getBinaryBiproductData P Q).ofIso eP eQ⟩

Depends on / 依赖: getBinaryBiproductData
-/
lemma hasBinaryBiproduct_of_iso {P Q P' Q' : C} [HasBinaryBiproduct P Q]
    (eP : P ≅ P') (eQ : Q ≅ Q') :
    HasBinaryBiproduct P' Q' where
  exists_binary_biproduct := ⟨(getBinaryBiproductData P Q).ofIso eP eQ⟩

instance {P Q : C} [HasBinaryBiproduct P Q] :
    HasBinaryBiproduct (op P) (op Q) where
  exists_binary_biproduct := ⟨(getBinaryBiproductData P Q).op⟩

section

variable (C)

/--
Definition of `HasBinaryBiproducts` / `HasBinaryBiproducts` 的定义

English:
class HasBinaryBiproducts
  parameters: : Prop where
  axioms and operations (1):
    - has_binary_biproduct : forall P Q : C, HasBinaryBiproduct P Q

中文:
类 有BinaryBiproducts
  参数: : 命题 where
  公理与运算 (1 个):
    - has_binary_biproduct : 对任意 P Q : C, 有BinaryBiproduct P Q
-/
class HasBinaryBiproducts : Prop where
  has_binary_biproduct : forall P Q : C, HasBinaryBiproduct P Q

attribute [instance 100] HasBinaryBiproducts.has_binary_biproduct

/--
theorem `hasBinaryBiproducts_of_finite_biproducts` / 定理 `hasBinaryBiproducts_of_finite_biproducts`

English:
theorem hasBinaryBiproducts_of_finite_biproducts
  given: [HasFiniteBiproducts C]
  statement: HasBinaryBiproducts C
  proof: { has_binary_biproduct := fun P Q =>
      HasBinaryBiproduct.mk
        { bicone := (biproduct.bicone (pairFunction P Q)).toBinaryBicone
          isBilimit := (Bicone.toBinaryBiconeIsBilimit _).symm (biproduct.isBilimit _) } }

中文:
定理 hasBinaryBiproducts_of_finite_biproducts
  条件: [有FiniteBiproducts C]
  结论: 有BinaryBiproducts C
  证明: { has_binary_biproduct := fun P Q =>
      HasBinaryBiproduct.mk
        { bicone := (biproduct.bicone (pairFunction P Q)).toBinaryBicone
          isBilimit := (Bicone.toBinaryBiconeIsBilimit _).symm (biproduct.isBilimit _) } }

Depends on / 依赖: Bicone, Bicone.toBinaryBiconeIsBilimit, HasBinaryBiproduct, HasBinaryBiproduct.mk, bicone, biproduct, biproduct.bicone, biproduct.isBilimit, has_binary_biproduct, isBilimit, pairFunction, toBinaryBicone, toBinaryBiconeIsBilimit
-/
theorem hasBinaryBiproducts_of_finite_biproducts [HasFiniteBiproducts C] : HasBinaryBiproducts C :=
  { has_binary_biproduct := fun P Q =>
      HasBinaryBiproduct.mk
        { bicone := (biproduct.bicone (pairFunction P Q)).toBinaryBicone
          isBilimit := (Bicone.toBinaryBiconeIsBilimit _).symm (biproduct.isBilimit _) } }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HasBinaryBiproducts
  signature: C] : HasBinaryBiproducts Cᵒᵖ where
  body: inferInstanceAs (HasBinaryBiproduct (op X.unop) (op Y.unop))

中文:
实例 [有BinaryBiproducts
  签名: C] : 有BinaryBiproducts Cᵒᵖ where
  定义体: inferInstanceAs (HasBinaryBiproduct (op X.unop) (op Y.unop))

Depends on / 依赖: HasBinaryBiproduct, X.unop, Y.unop
-/
instance [HasBinaryBiproducts C] : HasBinaryBiproducts Cᵒᵖ where
  has_binary_biproduct X Y :=
    inferInstanceAs (HasBinaryBiproduct (op X.unop) (op Y.unop))

end

variable {P Q : C}

/--
Instance `HasBinaryBiproduct.hasLimit_pair` / 实例 `HasBinaryBiproduct.hasLimit_pair`

English:
instance HasBinaryBiproduct.hasLimit_pair
  signature: [HasBinaryBiproduct P Q]
  body: HasLimit.mk ⟨_, BinaryBiproduct.isLimit P Q⟩

中文:
实例 有BinaryBiproduct.hasLimit_pair
  签名: [有BinaryBiproduct P Q]
  定义体: HasLimit.mk ⟨_, BinaryBiproduct.isLimit P Q⟩

Depends on / 依赖: BinaryBiproduct, BinaryBiproduct.isLimit, HasLimit, HasLimit.mk, isLimit
-/
instance HasBinaryBiproduct.hasLimit_pair [HasBinaryBiproduct P Q] : HasLimit (pair P Q) :=
  HasLimit.mk ⟨_, BinaryBiproduct.isLimit P Q⟩

/--
Instance `HasBinaryBiproduct.hasColimit_pair` / 实例 `HasBinaryBiproduct.hasColimit_pair`

English:
instance HasBinaryBiproduct.hasColimit_pair
  signature: [HasBinaryBiproduct P Q]
  body: HasColimit.mk ⟨_, BinaryBiproduct.isColimit P Q⟩

中文:
实例 有BinaryBiproduct.hasColimit_pair
  签名: [有BinaryBiproduct P Q]
  定义体: HasColimit.mk ⟨_, BinaryBiproduct.isColimit P Q⟩

Depends on / 依赖: BinaryBiproduct, BinaryBiproduct.isColimit, HasColimit, HasColimit.mk, isColimit
-/
instance HasBinaryBiproduct.hasColimit_pair [HasBinaryBiproduct P Q] : HasColimit (pair P Q) :=
  HasColimit.mk ⟨_, BinaryBiproduct.isColimit P Q⟩

instance (priority := 100) hasBinaryProducts_of_hasBinaryBiproducts [HasBinaryBiproducts C] :
    HasBinaryProducts C where
  has_limit F := hasLimit_of_iso (diagramIsoPair F).symm

instance (priority := 100) hasBinaryCoproducts_of_hasBinaryBiproducts [HasBinaryBiproducts C] :
    HasBinaryCoproducts C where
  has_colimit F := hasColimit_of_iso (diagramIsoPair F)

/--
Definition of `biprodIso` / `biprodIso` 的定义

English:
definition biprodIso
  signature: (X Y : C) [HasBinaryBiproduct X Y]
  body: (IsLimit.conePointUniqueUpToIso (limit.isLimit _) (BinaryBiproduct.isLimit X Y)).trans
    IsColimit.coconePointUniqueUpToIso (BinaryBiproduct.isColimit X Y) (colimit.isColimit _)

中文:
定义 biprodIso
  签名: (X Y : C) [有BinaryBiproduct X Y]
  定义体: (IsLimit.conePointUniqueUpToIso (limit.isLimit _) (BinaryBiproduct.isLimit X Y)).trans
    IsColimit.coconePointUniqueUpToIso (BinaryBiproduct.isColimit X Y) (colimit.isColimit _)

Depends on / 依赖: BinaryBiproduct, BinaryBiproduct.isColimit, BinaryBiproduct.isLimit, IsColimit, IsColimit.coconePointUniqueUpToIso, IsLimit, IsLimit.conePointUniqueUpToIso, coconePointUniqueUpToIso, colimit, colimit.isColimit, conePointUniqueUpToIso, isColimit, isLimit, limit.isLimit
-/
def biprodIso (X Y : C) [HasBinaryBiproduct X Y] : Limits.prod X Y ≅ Limits.coprod X Y :=
(IsLimit.conePointUniqueUpToIso (limit.isLimit _) (BinaryBiproduct.isLimit X Y)).trans
    IsColimit.coconePointUniqueUpToIso (BinaryBiproduct.isColimit X Y) (colimit.isColimit _)

/--
Definition of `biprod` / `biprod` 的定义

English:
abbreviation biprod
  signature: (X Y : C) [HasBinaryBiproduct X Y]
  body: (BinaryBiproduct.bicone X Y).pt

@[inherit_doc biprod]
notation:20 X " ⊞ " Y:20 => biprod X Y

中文:
缩写 biprod
  签名: (X Y : C) [有BinaryBiproduct X Y]
  定义体: (BinaryBiproduct.bicone X Y).pt

@[inherit_doc biprod]
notation:20 X " ⊞ " Y:20 => biprod X Y

Depends on / 依赖: BinaryBiproduct, BinaryBiproduct.bicone, bicone
-/
abbrev biprod (X Y : C) [HasBinaryBiproduct X Y] :=
  (BinaryBiproduct.bicone X Y).pt

@[inherit_doc biprod]
notation:20 X " ⊞ " Y:20 => biprod X Y

/--
Definition of `biprod.fst` / `biprod.fst` 的定义

English:
abbreviation biprod.fst
  signature: {X Y : C} [HasBinaryBiproduct X Y]
  body: (BinaryBiproduct.bicone X Y).fst

中文:
缩写 biprod.fst
  签名: {X Y : C} [有BinaryBiproduct X Y]
  定义体: (BinaryBiproduct.bicone X Y).fst

Depends on / 依赖: BinaryBiproduct, BinaryBiproduct.bicone, bicone
-/
abbrev biprod.fst {X Y : C} [HasBinaryBiproduct X Y] : X ⊞ Y ⟶ X :=
  (BinaryBiproduct.bicone X Y).fst

/--
Definition of `biprod.snd` / `biprod.snd` 的定义

English:
abbreviation biprod.snd
  signature: {X Y : C} [HasBinaryBiproduct X Y]
  body: (BinaryBiproduct.bicone X Y).snd

中文:
缩写 biprod.snd
  签名: {X Y : C} [有BinaryBiproduct X Y]
  定义体: (BinaryBiproduct.bicone X Y).snd

Depends on / 依赖: BinaryBiproduct, BinaryBiproduct.bicone, bicone
-/
abbrev biprod.snd {X Y : C} [HasBinaryBiproduct X Y] : X ⊞ Y ⟶ Y :=
  (BinaryBiproduct.bicone X Y).snd

/--
Definition of `biprod.inl` / `biprod.inl` 的定义

English:
abbreviation biprod.inl
  signature: {X Y : C} [HasBinaryBiproduct X Y]
  body: (BinaryBiproduct.bicone X Y).inl

中文:
缩写 biprod.inl
  签名: {X Y : C} [有BinaryBiproduct X Y]
  定义体: (BinaryBiproduct.bicone X Y).inl

Depends on / 依赖: BinaryBiproduct, BinaryBiproduct.bicone, bicone
-/
abbrev biprod.inl {X Y : C} [HasBinaryBiproduct X Y] : X ⟶ X ⊞ Y :=
  (BinaryBiproduct.bicone X Y).inl

/--
Definition of `biprod.inr` / `biprod.inr` 的定义

English:
abbreviation biprod.inr
  signature: {X Y : C} [HasBinaryBiproduct X Y]
  body: (BinaryBiproduct.bicone X Y).inr

中文:
缩写 biprod.inr
  签名: {X Y : C} [有BinaryBiproduct X Y]
  定义体: (BinaryBiproduct.bicone X Y).inr

Depends on / 依赖: BinaryBiproduct, BinaryBiproduct.bicone, bicone
-/
abbrev biprod.inr {X Y : C} [HasBinaryBiproduct X Y] : Y ⟶ X ⊞ Y :=
  (BinaryBiproduct.bicone X Y).inr

section

variable {X Y : C} [HasBinaryBiproduct X Y]

/--
theorem `BinaryBiproduct.bicone_fst` / 定理 `BinaryBiproduct.bicone_fst`

English:
theorem BinaryBiproduct.bicone_fst
  statement: (BinaryBiproduct.bicone X Y).fst = biprod.fst
  proof: rfl

中文:
定理 BinaryBiproduct.bicone_fst
  结论: (BinaryBiproduct.bicone X Y).fst = biprod.fst
  证明: rfl
-/
@[simp] theorem BinaryBiproduct.bicone_fst : (BinaryBiproduct.bicone X Y).fst = biprod.fst := rfl

/--
theorem `BinaryBiproduct.bicone_snd` / 定理 `BinaryBiproduct.bicone_snd`

English:
theorem BinaryBiproduct.bicone_snd
  statement: (BinaryBiproduct.bicone X Y).snd = biprod.snd
  proof: rfl

中文:
定理 BinaryBiproduct.bicone_snd
  结论: (BinaryBiproduct.bicone X Y).snd = biprod.snd
  证明: rfl
-/
@[simp] theorem BinaryBiproduct.bicone_snd : (BinaryBiproduct.bicone X Y).snd = biprod.snd := rfl

/--
theorem `BinaryBiproduct.bicone_inl` / 定理 `BinaryBiproduct.bicone_inl`

English:
theorem BinaryBiproduct.bicone_inl
  statement: (BinaryBiproduct.bicone X Y).inl = biprod.inl
  proof: rfl

中文:
定理 BinaryBiproduct.bicone_inl
  结论: (BinaryBiproduct.bicone X Y).inl = biprod.inl
  证明: rfl
-/
@[simp] theorem BinaryBiproduct.bicone_inl : (BinaryBiproduct.bicone X Y).inl = biprod.inl := rfl

/--
theorem `BinaryBiproduct.bicone_inr` / 定理 `BinaryBiproduct.bicone_inr`

English:
theorem BinaryBiproduct.bicone_inr
  statement: (BinaryBiproduct.bicone X Y).inr = biprod.inr
  proof: rfl

中文:
定理 BinaryBiproduct.bicone_inr
  结论: (BinaryBiproduct.bicone X Y).inr = biprod.inr
  证明: rfl
-/
@[simp] theorem BinaryBiproduct.bicone_inr : (BinaryBiproduct.bicone X Y).inr = biprod.inr := rfl

end

@[reassoc]
/--
theorem `biprod.inl_fst` / 定理 `biprod.inl_fst`

English:
theorem biprod.inl_fst
  given: {X Y : C} [HasBinaryBiproduct X Y]
  proof: (BinaryBiproduct.bicone X Y).inl_fst

@[reassoc]

中文:
定理 biprod.inl_fst
  条件: {X Y : C} [有BinaryBiproduct X Y]
  证明: (BinaryBiproduct.bicone X Y).inl_fst

@[reassoc]

Depends on / 依赖: BinaryBiproduct, BinaryBiproduct.bicone, bicone, inl_fst
-/
theorem biprod.inl_fst {X Y : C} [HasBinaryBiproduct X Y] :
    (biprod.inl : X ⟶ X ⊞ Y) ≫ (biprod.fst : X ⊞ Y ⟶ X) = 𝟙 X :=
  (BinaryBiproduct.bicone X Y).inl_fst

@[reassoc]
/--
theorem `biprod.inl_snd` / 定理 `biprod.inl_snd`

English:
theorem biprod.inl_snd
  given: {X Y : C} [HasBinaryBiproduct X Y]
  proof: (BinaryBiproduct.bicone X Y).inl_snd

@[reassoc]

中文:
定理 biprod.inl_snd
  条件: {X Y : C} [有BinaryBiproduct X Y]
  证明: (BinaryBiproduct.bicone X Y).inl_snd

@[reassoc]

Depends on / 依赖: BinaryBiproduct, BinaryBiproduct.bicone, bicone, inl_snd
-/
theorem biprod.inl_snd {X Y : C} [HasBinaryBiproduct X Y] :
    (biprod.inl : X ⟶ X ⊞ Y) ≫ (biprod.snd : X ⊞ Y ⟶ Y) = 0 :=
  (BinaryBiproduct.bicone X Y).inl_snd

@[reassoc]
/--
theorem `biprod.inr_fst` / 定理 `biprod.inr_fst`

English:
theorem biprod.inr_fst
  given: {X Y : C} [HasBinaryBiproduct X Y]
  proof: (BinaryBiproduct.bicone X Y).inr_fst

@[reassoc]

中文:
定理 biprod.inr_fst
  条件: {X Y : C} [有BinaryBiproduct X Y]
  证明: (BinaryBiproduct.bicone X Y).inr_fst

@[reassoc]

Depends on / 依赖: BinaryBiproduct, BinaryBiproduct.bicone, bicone, inr_fst
-/
theorem biprod.inr_fst {X Y : C} [HasBinaryBiproduct X Y] :
    (biprod.inr : Y ⟶ X ⊞ Y) ≫ (biprod.fst : X ⊞ Y ⟶ X) = 0 :=
  (BinaryBiproduct.bicone X Y).inr_fst

@[reassoc]
/--
theorem `biprod.inr_snd` / 定理 `biprod.inr_snd`

English:
theorem biprod.inr_snd
  given: {X Y : C} [HasBinaryBiproduct X Y]
  proof: (BinaryBiproduct.bicone X Y).inr_snd

中文:
定理 biprod.inr_snd
  条件: {X Y : C} [有BinaryBiproduct X Y]
  证明: (BinaryBiproduct.bicone X Y).inr_snd

Depends on / 依赖: BinaryBiproduct, BinaryBiproduct.bicone, bicone, inr_snd
-/
theorem biprod.inr_snd {X Y : C} [HasBinaryBiproduct X Y] :
    (biprod.inr : Y ⟶ X ⊞ Y) ≫ (biprod.snd : X ⊞ Y ⟶ Y) = 𝟙 Y :=
  (BinaryBiproduct.bicone X Y).inr_snd

/--
Definition of `biprod.lift` / `biprod.lift` 的定义

English:
abbreviation biprod.lift
  signature: {W X Y : C} [HasBinaryBiproduct X Y] (f : W ⟶ X) (g : W ⟶ Y)
  body: BinaryFan.IsLimit.lift (BinaryBiproduct.isLimit X Y) f g

中文:
缩写 biprod.lift
  签名: {W X Y : C} [有BinaryBiproduct X Y] (f : W ⟶ X) (g : W ⟶ Y)
  定义体: BinaryFan.IsLimit.lift (BinaryBiproduct.isLimit X Y) f g

Depends on / 依赖: BinaryBiproduct, BinaryBiproduct.isLimit, BinaryFan, BinaryFan.IsLimit.lift, IsLimit, isLimit
-/
abbrev biprod.lift {W X Y : C} [HasBinaryBiproduct X Y] (f : W ⟶ X) (g : W ⟶ Y) : W ⟶ X ⊞ Y :=
  BinaryFan.IsLimit.lift (BinaryBiproduct.isLimit X Y) f g

/--
Definition of `biprod.desc` / `biprod.desc` 的定义

English:
abbreviation biprod.desc
  signature: {W X Y : C} [HasBinaryBiproduct X Y] (f : X ⟶ W) (g : Y ⟶ W)
  body: BinaryCofan.IsColimit.desc (BinaryBiproduct.isColimit X Y) f g

@[reassoc (attr := simp)]

中文:
缩写 biprod.desc
  签名: {W X Y : C} [有BinaryBiproduct X Y] (f : X ⟶ W) (g : Y ⟶ W)
  定义体: BinaryCofan.IsColimit.desc (BinaryBiproduct.isColimit X Y) f g

@[reassoc (attr := simp)]

Depends on / 依赖: BinaryBiproduct, BinaryBiproduct.isColimit, BinaryCofan, BinaryCofan.IsColimit.desc, IsColimit, isColimit
-/
abbrev biprod.desc {W X Y : C} [HasBinaryBiproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) : X ⊞ Y ⟶ W :=
  BinaryCofan.IsColimit.desc (BinaryBiproduct.isColimit X Y) f g

@[reassoc (attr := simp)]
/--
theorem `biprod.lift_fst` / 定理 `biprod.lift_fst`

English:
theorem biprod.lift_fst
  given: {W X Y : C} [HasBinaryBiproduct X Y] (f : W ⟶ X) (g : W ⟶ Y)
  proof: (BinaryBiproduct.isLimit X Y).fac _ ⟨WalkingPair.left⟩

@[reassoc (attr := simp)]

中文:
定理 biprod.lift_fst
  条件: {W X Y : C} [有BinaryBiproduct X Y] (f : W ⟶ X) (g : W ⟶ Y)
  证明: (BinaryBiproduct.isLimit X Y).fac _ ⟨WalkingPair.left⟩

@[reassoc (attr := simp)]

Depends on / 依赖: BinaryBiproduct, BinaryBiproduct.isLimit, WalkingPair, WalkingPair.left, isLimit
-/
theorem biprod.lift_fst {W X Y : C} [HasBinaryBiproduct X Y] (f : W ⟶ X) (g : W ⟶ Y) :
    biprod.lift f g ≫ biprod.fst = f :=
  (BinaryBiproduct.isLimit X Y).fac _ ⟨WalkingPair.left⟩

@[reassoc (attr := simp)]
/--
theorem `biprod.lift_snd` / 定理 `biprod.lift_snd`

English:
theorem biprod.lift_snd
  given: {W X Y : C} [HasBinaryBiproduct X Y] (f : W ⟶ X) (g : W ⟶ Y)
  proof: (BinaryBiproduct.isLimit X Y).fac _ ⟨WalkingPair.right⟩

@[reassoc (attr := simp)]

中文:
定理 biprod.lift_snd
  条件: {W X Y : C} [有BinaryBiproduct X Y] (f : W ⟶ X) (g : W ⟶ Y)
  证明: (BinaryBiproduct.isLimit X Y).fac _ ⟨WalkingPair.right⟩

@[reassoc (attr := simp)]

Depends on / 依赖: BinaryBiproduct, BinaryBiproduct.isLimit, WalkingPair, WalkingPair.right, isLimit
-/
theorem biprod.lift_snd {W X Y : C} [HasBinaryBiproduct X Y] (f : W ⟶ X) (g : W ⟶ Y) :
    biprod.lift f g ≫ biprod.snd = g :=
  (BinaryBiproduct.isLimit X Y).fac _ ⟨WalkingPair.right⟩

@[reassoc (attr := simp)]
/--
theorem `biprod.inl_desc` / 定理 `biprod.inl_desc`

English:
theorem biprod.inl_desc
  given: {W X Y : C} [HasBinaryBiproduct X Y] (f : X ⟶ W) (g : Y ⟶ W)
  proof: (BinaryBiproduct.isColimit X Y).fac _ ⟨WalkingPair.left⟩

@[reassoc (attr := simp)]

中文:
定理 biprod.inl_desc
  条件: {W X Y : C} [有BinaryBiproduct X Y] (f : X ⟶ W) (g : Y ⟶ W)
  证明: (BinaryBiproduct.isColimit X Y).fac _ ⟨WalkingPair.left⟩

@[reassoc (attr := simp)]

Depends on / 依赖: BinaryBiproduct, BinaryBiproduct.isColimit, WalkingPair, WalkingPair.left, isColimit
-/
theorem biprod.inl_desc {W X Y : C} [HasBinaryBiproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) :
    biprod.inl ≫ biprod.desc f g = f :=
  (BinaryBiproduct.isColimit X Y).fac _ ⟨WalkingPair.left⟩

@[reassoc (attr := simp)]
/--
theorem `biprod.inr_desc` / 定理 `biprod.inr_desc`

English:
theorem biprod.inr_desc
  given: {W X Y : C} [HasBinaryBiproduct X Y] (f : X ⟶ W) (g : Y ⟶ W)
  proof: (BinaryBiproduct.isColimit X Y).fac _ ⟨WalkingPair.right⟩

中文:
定理 biprod.inr_desc
  条件: {W X Y : C} [有BinaryBiproduct X Y] (f : X ⟶ W) (g : Y ⟶ W)
  证明: (BinaryBiproduct.isColimit X Y).fac _ ⟨WalkingPair.right⟩

Depends on / 依赖: BinaryBiproduct, BinaryBiproduct.isColimit, WalkingPair, WalkingPair.right, isColimit
-/
theorem biprod.inr_desc {W X Y : C} [HasBinaryBiproduct X Y] (f : X ⟶ W) (g : Y ⟶ W) :
    biprod.inr ≫ biprod.desc f g = g :=
  (BinaryBiproduct.isColimit X Y).fac _ ⟨WalkingPair.right⟩

/--
Instance `biprod.mono_lift_of_mono_left` / 实例 `biprod.mono_lift_of_mono_left`

English:
instance biprod.mono_lift_of_mono_left
  signature: {W X Y : C} [HasBinaryBiproduct X Y] (f : W ⟶ X) (g : W ⟶ Y)
  body: mono_of_mono_fac biprod.lift_fst _ _

中文:
实例 biprod.mono_lift_of_mono_left
  签名: {W X Y : C} [有BinaryBiproduct X Y] (f : W ⟶ X) (g : W ⟶ Y)
  定义体: mono_of_mono_fac biprod.lift_fst _ _

Depends on / 依赖: biprod, biprod.lift_fst, lift_fst, mono_of_mono_fac
-/
instance biprod.mono_lift_of_mono_left {W X Y : C} [HasBinaryBiproduct X Y] (f : W ⟶ X) (g : W ⟶ Y)
    [Mono f] : Mono (biprod.lift f g) :=
mono_of_mono_fac biprod.lift_fst _ _

/--
Instance `biprod.mono_lift_of_mono_right` / 实例 `biprod.mono_lift_of_mono_right`

English:
instance biprod.mono_lift_of_mono_right
  signature: {W X Y : C} [HasBinaryBiproduct X Y] (f : W ⟶ X) (g : W ⟶ Y)
  body: mono_of_mono_fac biprod.lift_snd _ _

中文:
实例 biprod.mono_lift_of_mono_right
  签名: {W X Y : C} [有BinaryBiproduct X Y] (f : W ⟶ X) (g : W ⟶ Y)
  定义体: mono_of_mono_fac biprod.lift_snd _ _

Depends on / 依赖: biprod, biprod.lift_snd, lift_snd, mono_of_mono_fac
-/
instance biprod.mono_lift_of_mono_right {W X Y : C} [HasBinaryBiproduct X Y] (f : W ⟶ X) (g : W ⟶ Y)
    [Mono g] : Mono (biprod.lift f g) :=
mono_of_mono_fac biprod.lift_snd _ _

/--
Instance `biprod.epi_desc_of_epi_left` / 实例 `biprod.epi_desc_of_epi_left`

English:
instance biprod.epi_desc_of_epi_left
  signature: {W X Y : C} [HasBinaryBiproduct X Y] (f : X ⟶ W) (g : Y ⟶ W)
  body: epi_of_epi_fac biprod.inl_desc _ _

中文:
实例 biprod.epi_desc_of_epi_left
  签名: {W X Y : C} [有BinaryBiproduct X Y] (f : X ⟶ W) (g : Y ⟶ W)
  定义体: epi_of_epi_fac biprod.inl_desc _ _

Depends on / 依赖: biprod, biprod.inl_desc, epi_of_epi_fac, inl_desc
-/
instance biprod.epi_desc_of_epi_left {W X Y : C} [HasBinaryBiproduct X Y] (f : X ⟶ W) (g : Y ⟶ W)
    [Epi f] : Epi (biprod.desc f g) :=
epi_of_epi_fac biprod.inl_desc _ _

/--
Instance `biprod.epi_desc_of_epi_right` / 实例 `biprod.epi_desc_of_epi_right`

English:
instance biprod.epi_desc_of_epi_right
  signature: {W X Y : C} [HasBinaryBiproduct X Y] (f : X ⟶ W) (g : Y ⟶ W)
  body: epi_of_epi_fac biprod.inr_desc _ _

中文:
实例 biprod.epi_desc_of_epi_right
  签名: {W X Y : C} [有BinaryBiproduct X Y] (f : X ⟶ W) (g : Y ⟶ W)
  定义体: epi_of_epi_fac biprod.inr_desc _ _

Depends on / 依赖: biprod, biprod.inr_desc, epi_of_epi_fac, inr_desc
-/
instance biprod.epi_desc_of_epi_right {W X Y : C} [HasBinaryBiproduct X Y] (f : X ⟶ W) (g : Y ⟶ W)
    [Epi g] : Epi (biprod.desc f g) :=
epi_of_epi_fac biprod.inr_desc _ _

/--
Definition of `biprod.map` / `biprod.map` 的定义

English:
abbreviation biprod.map
  signature: {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] (f : W ⟶ Y)
  body: IsLimit.map (BinaryBiproduct.bicone W X).toCone (BinaryBiproduct.isLimit Y Z)
    (@mapPair _ _ (pair W X) (pair Y Z) f g)

中文:
缩写 biprod.map
  签名: {W X Y Z : C} [有BinaryBiproduct W X] [有BinaryBiproduct Y Z] (f : W ⟶ Y)
  定义体: IsLimit.map (BinaryBiproduct.bicone W X).toCone (BinaryBiproduct.isLimit Y Z)
    (@mapPair _ _ (pair W X) (pair Y Z) f g)

Depends on / 依赖: BinaryBiproduct, BinaryBiproduct.bicone, BinaryBiproduct.isLimit, IsLimit, IsLimit.map, bicone, isLimit, mapPair, toCone
-/
abbrev biprod.map {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : W ⊞ X ⟶ Y ⊞ Z :=
  IsLimit.map (BinaryBiproduct.bicone W X).toCone (BinaryBiproduct.isLimit Y Z)
    (@mapPair _ _ (pair W X) (pair Y Z) f g)

/--
Definition of `biprod.map'` / `biprod.map'` 的定义

English:
abbreviation biprod.map'
  signature: {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] (f : W ⟶ Y)
  body: IsColimit.map (BinaryBiproduct.isColimit W X) (BinaryBiproduct.bicone Y Z).toCocone
    (@mapPair _ _ (pair W X) (pair Y Z) f g)

@[ext]

中文:
缩写 biprod.map'
  签名: {W X Y Z : C} [有BinaryBiproduct W X] [有BinaryBiproduct Y Z] (f : W ⟶ Y)
  定义体: IsColimit.map (BinaryBiproduct.isColimit W X) (BinaryBiproduct.bicone Y Z).toCocone
    (@mapPair _ _ (pair W X) (pair Y Z) f g)

@[ext]

Depends on / 依赖: BinaryBiproduct, BinaryBiproduct.bicone, BinaryBiproduct.isColimit, IsColimit, IsColimit.map, bicone, isColimit, mapPair, toCocone
-/
abbrev biprod.map' {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : W ⊞ X ⟶ Y ⊞ Z :=
  IsColimit.map (BinaryBiproduct.isColimit W X) (BinaryBiproduct.bicone Y Z).toCocone
    (@mapPair _ _ (pair W X) (pair Y Z) f g)

@[ext]
/--
theorem `biprod.hom_ext` / 定理 `biprod.hom_ext`

English:
theorem biprod.hom_ext
  statement: {X Y Z : C} [HasBinaryBiproduct X Y] (f g : Z ⟶ X ⊞ Y)
  proof: BinaryFan.IsLimit.hom_ext (BinaryBiproduct.isLimit X Y) h₀ h₁

@[ext]

中文:
定理 biprod.hom_ext
  结论: {X Y Z : C} [有BinaryBiproduct X Y] (f g : Z ⟶ X ⊞ Y)
  证明: BinaryFan.IsLimit.hom_ext (BinaryBiproduct.isLimit X Y) h₀ h₁

@[ext]

Depends on / 依赖: BinaryBiproduct, BinaryBiproduct.isLimit, BinaryFan, BinaryFan.IsLimit.hom_ext, IsLimit, hom_ext, isLimit
-/
theorem biprod.hom_ext {X Y Z : C} [HasBinaryBiproduct X Y] (f g : Z ⟶ X ⊞ Y)
    (h₀ : f ≫ biprod.fst = g ≫ biprod.fst) (h₁ : f ≫ biprod.snd = g ≫ biprod.snd) : f = g :=
  BinaryFan.IsLimit.hom_ext (BinaryBiproduct.isLimit X Y) h₀ h₁

@[ext]
/--
theorem `biprod.hom_ext'` / 定理 `biprod.hom_ext'`

English:
theorem biprod.hom_ext'
  statement: {X Y Z : C} [HasBinaryBiproduct X Y] (f g : X ⊞ Y ⟶ Z)
  proof: BinaryCofan.IsColimit.hom_ext (BinaryBiproduct.isColimit X Y) h₀ h₁

中文:
定理 biprod.hom_ext'
  结论: {X Y Z : C} [有BinaryBiproduct X Y] (f g : X ⊞ Y ⟶ Z)
  证明: BinaryCofan.IsColimit.hom_ext (BinaryBiproduct.isColimit X Y) h₀ h₁

Depends on / 依赖: BinaryBiproduct, BinaryBiproduct.isColimit, BinaryCofan, BinaryCofan.IsColimit.hom_ext, IsColimit, hom_ext, isColimit
-/
theorem biprod.hom_ext' {X Y Z : C} [HasBinaryBiproduct X Y] (f g : X ⊞ Y ⟶ Z)
    (h₀ : biprod.inl ≫ f = biprod.inl ≫ g) (h₁ : biprod.inr ≫ f = biprod.inr ≫ g) : f = g :=
  BinaryCofan.IsColimit.hom_ext (BinaryBiproduct.isColimit X Y) h₀ h₁

/--
Definition of `biprod.isoProd` / `biprod.isoProd` 的定义

English:
definition biprod.isoProd
  signature: (X Y : C) [HasBinaryBiproduct X Y]
  body: IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit X Y) (limit.isLimit _)

中文:
定义 biprod.isoProd
  签名: (X Y : C) [有BinaryBiproduct X Y]
  定义体: IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit X Y) (limit.isLimit _)

Depends on / 依赖: BinaryBiproduct, BinaryBiproduct.isLimit, IsLimit, IsLimit.conePointUniqueUpToIso, conePointUniqueUpToIso, isLimit, limit.isLimit
-/
def biprod.isoProd (X Y : C) [HasBinaryBiproduct X Y] : X ⊞ Y ≅ X ⨯ Y :=
  IsLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit X Y) (limit.isLimit _)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `biprod.isoProd_hom` / 定理 `biprod.isoProd_hom`

English:
theorem biprod.isoProd_hom
  given: {X Y : C} [HasBinaryBiproduct X Y]
  proof: by
      ext <;> simp [biprod.isoProd]

中文:
定理 biprod.isoProd_hom
  条件: {X Y : C} [有BinaryBiproduct X Y]
  证明: by
      ext <;> simp [biprod.isoProd]

Depends on / 依赖: biprod, biprod.isoProd, isoProd
-/
theorem biprod.isoProd_hom {X Y : C} [HasBinaryBiproduct X Y] :
    (biprod.isoProd X Y).hom = prod.lift biprod.fst biprod.snd := by
      ext <;> simp [biprod.isoProd]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `biprod.isoProd_inv` / 定理 `biprod.isoProd_inv`

English:
theorem biprod.isoProd_inv
  given: {X Y : C} [HasBinaryBiproduct X Y]
  proof: by
  ext <;> simp [Iso.inv_comp_eq]

中文:
定理 biprod.isoProd_inv
  条件: {X Y : C} [有BinaryBiproduct X Y]
  证明: by
  ext <;> simp [Iso.inv_comp_eq]

Depends on / 依赖: Iso.inv_comp_eq, inv_comp_eq
-/
theorem biprod.isoProd_inv {X Y : C} [HasBinaryBiproduct X Y] :
    (biprod.isoProd X Y).inv = biprod.lift prod.fst prod.snd := by
  ext <;> simp [Iso.inv_comp_eq]

/--
Definition of `biprod.isoCoprod` / `biprod.isoCoprod` 的定义

English:
definition biprod.isoCoprod
  signature: (X Y : C) [HasBinaryBiproduct X Y]
  body: IsColimit.coconePointUniqueUpToIso (BinaryBiproduct.isColimit X Y) (colimit.isColimit _)

中文:
定义 biprod.isoCoprod
  签名: (X Y : C) [有BinaryBiproduct X Y]
  定义体: IsColimit.coconePointUniqueUpToIso (BinaryBiproduct.isColimit X Y) (colimit.isColimit _)

Depends on / 依赖: BinaryBiproduct, BinaryBiproduct.isColimit, IsColimit, IsColimit.coconePointUniqueUpToIso, coconePointUniqueUpToIso, colimit, colimit.isColimit, isColimit
-/
def biprod.isoCoprod (X Y : C) [HasBinaryBiproduct X Y] : X ⊞ Y ≅ X ⨿ Y :=
  IsColimit.coconePointUniqueUpToIso (BinaryBiproduct.isColimit X Y) (colimit.isColimit _)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `biprod.isoCoprod_inv` / 定理 `biprod.isoCoprod_inv`

English:
theorem biprod.isoCoprod_inv
  given: {X Y : C} [HasBinaryBiproduct X Y]
  proof: by
  ext <;> simp [biprod.isoCoprod]

中文:
定理 biprod.isoCoprod_inv
  条件: {X Y : C} [有BinaryBiproduct X Y]
  证明: by
  ext <;> simp [biprod.isoCoprod]

Depends on / 依赖: biprod, biprod.isoCoprod, isoCoprod
-/
theorem biprod.isoCoprod_inv {X Y : C} [HasBinaryBiproduct X Y] :
    (biprod.isoCoprod X Y).inv = coprod.desc biprod.inl biprod.inr := by
  ext <;> simp [biprod.isoCoprod]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `biprod_isoCoprod_hom` / 定理 `biprod_isoCoprod_hom`

English:
theorem biprod_isoCoprod_hom
  given: {X Y : C} [HasBinaryBiproduct X Y]
  proof: by
  ext <;> simp [← Iso.eq_comp_inv]

中文:
定理 biprod_isoCoprod_hom
  条件: {X Y : C} [有BinaryBiproduct X Y]
  证明: by
  ext <;> simp [← Iso.eq_comp_inv]

Depends on / 依赖: Iso.eq_comp_inv, eq_comp_inv
-/
theorem biprod_isoCoprod_hom {X Y : C} [HasBinaryBiproduct X Y] :
    (biprod.isoCoprod X Y).hom = biprod.desc coprod.inl coprod.inr := by
  ext <;> simp [← Iso.eq_comp_inv]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `biprod.map_eq_map'` / 定理 `biprod.map_eq_map'`

English:
theorem biprod.map_eq_map'
  statement: {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z]
  proof: by
  ext
  · simp only [mapPair_left, IsColimit.ι_map, IsLimit.map_π,
      Category.assoc, ← BinaryBicone.toCone_π_app_left, ←
      BinaryBicone.toCocone_ι_app_left]
    simp
  · simp only [mapPair_left, IsColimit.ι_map, IsLimit.map_π,
      Category.assoc, ← BinaryBicone.toCone_π_app_right, ←
      BinaryBicone.toCocone_ι_app_left]
    simp
  · simp only [mapPair_right, IsColimit.ι_map, IsLimit.map_π,
      Category.assoc, ← BinaryBicone.toCone_π_app_left, ←
      BinaryBicone.toCocone_ι_app_right]
    simp
  · simp only [mapPair_right, IsColimit.ι_map, IsLimit.map_π,
      Category.assoc, ← BinaryBicone.toCone_π_app_right, ←
      BinaryBicone.toCocone_ι_app_right]
    simp

中文:
定理 biprod.map_eq_map'
  结论: {W X Y Z : C} [有BinaryBiproduct W X] [有BinaryBiproduct Y Z]
  证明: by
  ext
  · simp only [mapPair_left, IsColimit.ι_map, IsLimit.map_π,
      Category.assoc, ← BinaryBicone.toCone_π_app_left, ←
      BinaryBicone.toCocone_ι_app_left]
    simp
  · simp only [mapPair_left, IsColimit.ι_map, IsLimit.map_π,
      Category.assoc, ← BinaryBicone.toCone_π_app_right, ←
      BinaryBicone.toCocone_ι_app_left]
    simp
  · simp only [mapPair_right, IsColimit.ι_map, IsLimit.map_π,
      Category.assoc, ← BinaryBicone.toCone_π_app_left, ←
      BinaryBicone.toCocone_ι_app_right]
    simp
  · simp only [mapPair_right, IsColimit.ι_map, IsLimit.map_π,
      Category.assoc, ← BinaryBicone.toCone_π_app_right, ←
      BinaryBicone.toCocone_ι_app_right]
    simp

Depends on / 依赖: BinaryBicone, BinaryBicone.toCocone_, BinaryBicone.toCone_, Category, Category.assoc, IsColimit, IsLimit, IsLimit.map_, mapPair_left, mapPair_right
-/
theorem biprod.map_eq_map' {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z]
    (f : W ⟶ Y) (g : X ⟶ Z) : biprod.map f g = biprod.map' f g := by
  ext
  · simp only [mapPair_left, IsColimit.ι_map, IsLimit.map_π,
      Category.assoc, ← BinaryBicone.toCone_π_app_left, ←
      BinaryBicone.toCocone_ι_app_left]
    simp
  · simp only [mapPair_left, IsColimit.ι_map, IsLimit.map_π,
      Category.assoc, ← BinaryBicone.toCone_π_app_right, ←
      BinaryBicone.toCocone_ι_app_left]
    simp
  · simp only [mapPair_right, IsColimit.ι_map, IsLimit.map_π,
      Category.assoc, ← BinaryBicone.toCone_π_app_left, ←
      BinaryBicone.toCocone_ι_app_right]
    simp
  · simp only [mapPair_right, IsColimit.ι_map, IsLimit.map_π,
      Category.assoc, ← BinaryBicone.toCone_π_app_right, ←
      BinaryBicone.toCocone_ι_app_right]
    simp

/--
Instance `biprod.inl_mono` / 实例 `biprod.inl_mono`

English:
instance biprod.inl_mono
  signature: {X Y : C} [HasBinaryBiproduct X Y]
  body: IsSplitMono.mk' { retraction := biprod.fst }

中文:
实例 biprod.inl_mono
  签名: {X Y : C} [有BinaryBiproduct X Y]
  定义体: IsSplitMono.mk' { retraction := biprod.fst }

Depends on / 依赖: IsSplitMono, IsSplitMono.mk, biprod, biprod.fst, retraction
-/
instance biprod.inl_mono {X Y : C} [HasBinaryBiproduct X Y] :
    IsSplitMono (biprod.inl : X ⟶ X ⊞ Y) :=
  IsSplitMono.mk' { retraction := biprod.fst }

/--
Instance `biprod.inr_mono` / 实例 `biprod.inr_mono`

English:
instance biprod.inr_mono
  signature: {X Y : C} [HasBinaryBiproduct X Y]
  body: IsSplitMono.mk' { retraction := biprod.snd }

中文:
实例 biprod.inr_mono
  签名: {X Y : C} [有BinaryBiproduct X Y]
  定义体: IsSplitMono.mk' { retraction := biprod.snd }

Depends on / 依赖: IsSplitMono, IsSplitMono.mk, biprod, biprod.snd, retraction
-/
instance biprod.inr_mono {X Y : C} [HasBinaryBiproduct X Y] :
    IsSplitMono (biprod.inr : Y ⟶ X ⊞ Y) :=
  IsSplitMono.mk' { retraction := biprod.snd }

/--
Instance `biprod.fst_epi` / 实例 `biprod.fst_epi`

English:
instance biprod.fst_epi
  signature: {X Y : C} [HasBinaryBiproduct X Y]
  body: IsSplitEpi.mk' { section_ := biprod.inl }

中文:
实例 biprod.fst_epi
  签名: {X Y : C} [有BinaryBiproduct X Y]
  定义体: IsSplitEpi.mk' { section_ := biprod.inl }

Depends on / 依赖: IsSplitEpi, IsSplitEpi.mk, biprod, biprod.inl, section_
-/
instance biprod.fst_epi {X Y : C} [HasBinaryBiproduct X Y] : IsSplitEpi (biprod.fst : X ⊞ Y ⟶ X) :=
  IsSplitEpi.mk' { section_ := biprod.inl }

/--
Instance `biprod.snd_epi` / 实例 `biprod.snd_epi`

English:
instance biprod.snd_epi
  signature: {X Y : C} [HasBinaryBiproduct X Y]
  body: IsSplitEpi.mk' { section_ := biprod.inr }

@[reassoc (attr := simp)]

中文:
实例 biprod.snd_epi
  签名: {X Y : C} [有BinaryBiproduct X Y]
  定义体: IsSplitEpi.mk' { section_ := biprod.inr }

@[reassoc (attr := simp)]

Depends on / 依赖: IsSplitEpi, IsSplitEpi.mk, biprod, biprod.inr, section_
-/
instance biprod.snd_epi {X Y : C} [HasBinaryBiproduct X Y] : IsSplitEpi (biprod.snd : X ⊞ Y ⟶ Y) :=
  IsSplitEpi.mk' { section_ := biprod.inr }

@[reassoc (attr := simp)]
/--
theorem `biprod.map_fst` / 定理 `biprod.map_fst`

English:
theorem biprod.map_fst
  statement: {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] (f : W ⟶ Y)
  proof: IsLimit.map_π _ _ _ (⟨WalkingPair.left⟩ : Discrete WalkingPair)

@[reassoc (attr := simp)]

中文:
定理 biprod.map_fst
  结论: {W X Y Z : C} [有BinaryBiproduct W X] [有BinaryBiproduct Y Z] (f : W ⟶ Y)
  证明: IsLimit.map_π _ _ _ (⟨WalkingPair.left⟩ : Discrete WalkingPair)

@[reassoc (attr := simp)]

Depends on / 依赖: Discrete, IsLimit, IsLimit.map_, WalkingPair, WalkingPair.left
-/
theorem biprod.map_fst {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : biprod.map f g ≫ biprod.fst = biprod.fst ≫ f :=
  IsLimit.map_π _ _ _ (⟨WalkingPair.left⟩ : Discrete WalkingPair)

@[reassoc (attr := simp)]
/--
theorem `biprod.map_snd` / 定理 `biprod.map_snd`

English:
theorem biprod.map_snd
  statement: {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] (f : W ⟶ Y)
  proof: IsLimit.map_π _ _ _ (⟨WalkingPair.right⟩ : Discrete WalkingPair)

中文:
定理 biprod.map_snd
  结论: {W X Y Z : C} [有BinaryBiproduct W X] [有BinaryBiproduct Y Z] (f : W ⟶ Y)
  证明: IsLimit.map_π _ _ _ (⟨WalkingPair.right⟩ : Discrete WalkingPair)

Depends on / 依赖: Discrete, IsLimit, IsLimit.map_, WalkingPair, WalkingPair.right
-/
theorem biprod.map_snd {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : biprod.map f g ≫ biprod.snd = biprod.snd ≫ g :=
  IsLimit.map_π _ _ _ (⟨WalkingPair.right⟩ : Discrete WalkingPair)

-- Because `biprod.map` is defined in terms of `lim` rather than `colim`,
-- we need to provide additional `simp` lemmas.
@[reassoc (attr := simp)]
/--
theorem `biprod.inl_map` / 定理 `biprod.inl_map`

English:
theorem biprod.inl_map
  statement: {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] (f : W ⟶ Y)
  proof: by
  rw [biprod.map_eq_map']
  exact IsColimit.ι_map (BinaryBiproduct.isColimit W X) _ _ ⟨WalkingPair.left⟩

@[reassoc (attr := simp)]

中文:
定理 biprod.inl_map
  结论: {W X Y Z : C} [有BinaryBiproduct W X] [有BinaryBiproduct Y Z] (f : W ⟶ Y)
  证明: by
  rw [biprod.map_eq_map']
  exact IsColimit.ι_map (BinaryBiproduct.isColimit W X) _ _ ⟨WalkingPair.left⟩

@[reassoc (attr := simp)]

Depends on / 依赖: BinaryBiproduct, BinaryBiproduct.isColimit, IsColimit, WalkingPair, WalkingPair.left, biprod, biprod.map_eq_map, isColimit, map_eq_map
-/
theorem biprod.inl_map {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : biprod.inl ≫ biprod.map f g = f ≫ biprod.inl := by
  rw [biprod.map_eq_map']
  exact IsColimit.ι_map (BinaryBiproduct.isColimit W X) _ _ ⟨WalkingPair.left⟩

@[reassoc (attr := simp)]
/--
theorem `biprod.inr_map` / 定理 `biprod.inr_map`

English:
theorem biprod.inr_map
  statement: {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] (f : W ⟶ Y)
  proof: by
  rw [biprod.map_eq_map']
  exact IsColimit.ι_map (BinaryBiproduct.isColimit W X) _ _ ⟨WalkingPair.right⟩

中文:
定理 biprod.inr_map
  结论: {W X Y Z : C} [有BinaryBiproduct W X] [有BinaryBiproduct Y Z] (f : W ⟶ Y)
  证明: by
  rw [biprod.map_eq_map']
  exact IsColimit.ι_map (BinaryBiproduct.isColimit W X) _ _ ⟨WalkingPair.right⟩

Depends on / 依赖: BinaryBiproduct, BinaryBiproduct.isColimit, IsColimit, WalkingPair, WalkingPair.right, biprod, biprod.map_eq_map, isColimit, map_eq_map
-/
theorem biprod.inr_map {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] (f : W ⟶ Y)
    (g : X ⟶ Z) : biprod.inr ≫ biprod.map f g = g ≫ biprod.inr := by
  rw [biprod.map_eq_map']
  exact IsColimit.ι_map (BinaryBiproduct.isColimit W X) _ _ ⟨WalkingPair.right⟩

/-- Given a pair of isomorphisms between the summands of a pair of binary biproducts,
we obtain an isomorphism between the binary biproducts. -/
@[simps]
/--
Definition of `biprod.mapIso` / `biprod.mapIso` 的定义

English:
definition biprod.mapIso
  signature: {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] (f : W ≅ Y)
  body: biprod.map f.hom g.hom
  inv := biprod.map f.inv g.inv

中文:
定义 biprod.mapIso
  签名: {W X Y Z : C} [有BinaryBiproduct W X] [有BinaryBiproduct Y Z] (f : W ≅ Y)
  定义体: biprod.map f.hom g.hom
  inv := biprod.map f.inv g.inv

Depends on / 依赖: biprod, biprod.map, f.hom, g.hom
-/
def biprod.mapIso {W X Y Z : C} [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] (f : W ≅ Y)
    (g : X ≅ Z) : W ⊞ X ≅ Y ⊞ Z where
  hom := biprod.map f.hom g.hom
  inv := biprod.map f.inv g.inv

/--
theorem `biprod.conePointUniqueUpToIso_hom` / 定理 `biprod.conePointUniqueUpToIso_hom`

English:
theorem biprod.conePointUniqueUpToIso_hom
  statement: (X Y : C) [HasBinaryBiproduct X Y] {b : BinaryBicone X Y}
  proof: rfl

中文:
定理 biprod.conePointUniqueUpToIso_hom
  结论: (X Y : C) [有BinaryBiproduct X Y] {b : BinaryBicone X Y}
  证明: rfl
-/
theorem biprod.conePointUniqueUpToIso_hom (X Y : C) [HasBinaryBiproduct X Y] {b : BinaryBicone X Y}
    (hb : b.IsBilimit) :
    (hb.isLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit _ _)).hom =
      biprod.lift b.fst b.snd := rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `biprod.conePointUniqueUpToIso_inv` / 定理 `biprod.conePointUniqueUpToIso_inv`

English:
theorem biprod.conePointUniqueUpToIso_inv
  statement: (X Y : C) [HasBinaryBiproduct X Y] {b : BinaryBicone X Y}
  proof: by
  refine biprod.hom_ext' _ _ (hb.isLimit.hom_ext fun j => ?_) (hb.isLimit.hom_ext fun j => ?_)
  all_goals
    simp only [Category.assoc, IsLimit.conePointUniqueUpToIso_inv_comp]
    rcases j with ⟨⟨⟩⟩
  all_goals simp

中文:
定理 biprod.conePointUniqueUpToIso_inv
  结论: (X Y : C) [有BinaryBiproduct X Y] {b : BinaryBicone X Y}
  证明: by
  refine biprod.hom_ext' _ _ (hb.isLimit.hom_ext fun j => ?_) (hb.isLimit.hom_ext fun j => ?_)
  all_goals
    simp only [Category.assoc, IsLimit.conePointUniqueUpToIso_inv_comp]
    rcases j with ⟨⟨⟩⟩
  all_goals simp

Depends on / 依赖: Category, Category.assoc, IsLimit, IsLimit.conePointUniqueUpToIso_inv_comp, all_goals, biprod, biprod.hom_ext, conePointUniqueUpToIso_inv_comp, hb.isLimit.hom_ext, hom_ext, isLimit
-/
theorem biprod.conePointUniqueUpToIso_inv (X Y : C) [HasBinaryBiproduct X Y] {b : BinaryBicone X Y}
    (hb : b.IsBilimit) :
    (hb.isLimit.conePointUniqueUpToIso (BinaryBiproduct.isLimit _ _)).inv =
      biprod.desc b.inl b.inr := by
  refine biprod.hom_ext' _ _ (hb.isLimit.hom_ext fun j => ?_) (hb.isLimit.hom_ext fun j => ?_)
  all_goals
    simp only [Category.assoc, IsLimit.conePointUniqueUpToIso_inv_comp]
    rcases j with ⟨⟨⟩⟩
  all_goals simp

set_option backward.isDefEq.respectTransparency.types false in
/-- Binary biproducts are unique up to isomorphism. This already follows because bilimits are
limits, but in the case of biproducts we can give an isomorphism with particularly nice
definitional properties, namely that `biprod.lift b.fst b.snd` and `biprod.desc b.inl b.inr`
are inverses of each other. -/
@[simps]
/--
Definition of `biprod.uniqueUpToIso` / `biprod.uniqueUpToIso` 的定义

English:
definition biprod.uniqueUpToIso
  signature: (X Y : C) [HasBinaryBiproduct X Y] {b : BinaryBicone X Y}
  body: biprod.lift b.fst b.snd
  inv := biprod.desc b.inl b.inr
  hom_inv_id := by
    rw [← biprod.conePointUniqueUpToIso_hom X Y hb]; rw [←
      biprod.conePointUniqueUpToIso_inv X Y hb]; rw [Iso.hom_inv_id]
  inv_hom_id := by
    rw [← biprod.conePointUniqueUpToIso_hom X Y hb]; rw [←
      biprod.conePointUniqueUpToIso_inv X Y hb]; rw [Iso.inv_hom_id]

中文:
定义 biprod.uniqueUpToIso
  签名: (X Y : C) [有BinaryBiproduct X Y] {b : BinaryBicone X Y}
  定义体: biprod.lift b.fst b.snd
  inv := biprod.desc b.inl b.inr
  hom_inv_id := by
    rw [← biprod.conePointUniqueUpToIso_hom X Y hb]; rw [←
      biprod.conePointUniqueUpToIso_inv X Y hb]; rw [Iso.hom_inv_id]
  inv_hom_id := by
    rw [← biprod.conePointUniqueUpToIso_hom X Y hb]; rw [←
      biprod.conePointUniqueUpToIso_inv X Y hb]; rw [Iso.inv_hom_id]

Depends on / 依赖: b.fst, b.snd, biprod, biprod.lift
-/
def biprod.uniqueUpToIso (X Y : C) [HasBinaryBiproduct X Y] {b : BinaryBicone X Y}
    (hb : b.IsBilimit) : b.pt ≅ X ⊞ Y where
  hom := biprod.lift b.fst b.snd
  inv := biprod.desc b.inl b.inr
  hom_inv_id := by
    rw [← biprod.conePointUniqueUpToIso_hom X Y hb]; rw [←
      biprod.conePointUniqueUpToIso_inv X Y hb]; rw [Iso.hom_inv_id]
  inv_hom_id := by
    rw [← biprod.conePointUniqueUpToIso_hom X Y hb]; rw [←
      biprod.conePointUniqueUpToIso_inv X Y hb]; rw [Iso.inv_hom_id]

-- There are three further variations,
-- about `IsIso biprod.inr`, `IsIso biprod.fst` and `IsIso biprod.snd`,
-- but any one suffices to prove `indecomposable_of_simple`
-- and they are likely not separately useful.
/--
theorem `biprod.isIso_inl_iff_id_eq_fst_comp_inl` / 定理 `biprod.isIso_inl_iff_id_eq_fst_comp_inl`

English:
theorem biprod.isIso_inl_iff_id_eq_fst_comp_inl
  given: (X Y : C) [HasBinaryBiproduct X Y]
  proof: by
  constructor
  · intro h
have := (cancel_epi (inv biprod.inl : X ⊞ Y ⟶ X)).2 @biprod.inl_fst _ _ _ X Y _
    rw [IsIso.inv_hom_id_assoc]; rw [Category.comp_id] at this
    rw [this]; rw [IsIso.inv_hom_id]
  · intro h
    exact ⟨⟨biprod.fst, biprod.inl_fst, h.symm⟩⟩

中文:
定理 biprod.isIso_inl_iff_id_eq_fst_comp_inl
  条件: (X Y : C) [有BinaryBiproduct X Y]
  证明: by
  constructor
  · intro h
have := (cancel_epi (inv biprod.inl : X ⊞ Y ⟶ X)).2 @biprod.inl_fst _ _ _ X Y _
    rw [IsIso.inv_hom_id_assoc]; rw [Category.comp_id] at this
    rw [this]; rw [IsIso.inv_hom_id]
  · intro h
    exact ⟨⟨biprod.fst, biprod.inl_fst, h.symm⟩⟩

Depends on / 依赖: Category, Category.comp_id, IsIso.inv_hom_id, IsIso.inv_hom_id_assoc, biprod, biprod.fst, biprod.inl, biprod.inl_fst, cancel_epi, comp_id, h.symm, inl_fst, inv_hom_id, inv_hom_id_assoc
-/
theorem biprod.isIso_inl_iff_id_eq_fst_comp_inl (X Y : C) [HasBinaryBiproduct X Y] :
    IsIso (biprod.inl : X ⟶ X ⊞ Y) ↔ 𝟙 (X ⊞ Y) = biprod.fst ≫ biprod.inl := by
  constructor
  · intro h
have := (cancel_epi (inv biprod.inl : X ⊞ Y ⟶ X)).2 @biprod.inl_fst _ _ _ X Y _
    rw [IsIso.inv_hom_id_assoc]; rw [Category.comp_id] at this
    rw [this]; rw [IsIso.inv_hom_id]
  · intro h
    exact ⟨⟨biprod.fst, biprod.inl_fst, h.symm⟩⟩

set_option backward.isDefEq.respectTransparency false in
/--
Instance `biprod.map_epi` / 实例 `biprod.map_epi`

English:
instance biprod.map_epi
  signature: {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [Epi f]
  body: by
  rw [show biprod.map f g =
    (biprod.isoCoprod _ _).hom ≫ coprod.map f g ≫ (biprod.isoCoprod _ _).inv by aesop]
  infer_instance

中文:
实例 biprod.map_epi
  签名: {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [满态射 f]
  定义体: by
  rw [show biprod.map f g =
    (biprod.isoCoprod _ _).hom ≫ coprod.map f g ≫ (biprod.isoCoprod _ _).inv by aesop]
  infer_instance

Depends on / 依赖: biprod, biprod.isoCoprod, biprod.map, coprod, coprod.map, infer_instance, isoCoprod
-/
instance biprod.map_epi {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [Epi f]
    [Epi g] [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] : Epi (biprod.map f g) := by
  rw [show biprod.map f g =
    (biprod.isoCoprod _ _).hom ≫ coprod.map f g ≫ (biprod.isoCoprod _ _).inv by aesop]
  infer_instance

/--
Instance `prod.map_epi` / 实例 `prod.map_epi`

English:
instance prod.map_epi
  signature: {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [Epi f]
  body: by
  rw [show prod.map f g = (biprod.isoProd _ _).inv ≫ biprod.map f g ≫
    (biprod.isoProd _ _).hom by simp]
  infer_instance

中文:
实例 乘积.map_epi
  签名: {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [满态射 f]
  定义体: by
  rw [show prod.map f g = (biprod.isoProd _ _).inv ≫ biprod.map f g ≫
    (biprod.isoProd _ _).hom by simp]
  infer_instance

Depends on / 依赖: biprod, biprod.isoProd, biprod.map, infer_instance, isoProd, prod.map
-/
instance prod.map_epi {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [Epi f]
    [Epi g] [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] : Epi (prod.map f g) := by
  rw [show prod.map f g = (biprod.isoProd _ _).inv ≫ biprod.map f g ≫
    (biprod.isoProd _ _).hom by simp]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
Instance `biprod.map_mono` / 实例 `biprod.map_mono`

English:
instance biprod.map_mono
  signature: {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [Mono f]
  body: by
  rw [show biprod.map f g = (biprod.isoProd _ _).hom ≫ prod.map f g ≫
    (biprod.isoProd _ _).inv by aesop]
  infer_instance

中文:
实例 biprod.map_mono
  签名: {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [单态射 f]
  定义体: by
  rw [show biprod.map f g = (biprod.isoProd _ _).hom ≫ prod.map f g ≫
    (biprod.isoProd _ _).inv by aesop]
  infer_instance

Depends on / 依赖: biprod, biprod.isoProd, biprod.map, infer_instance, isoProd, prod.map
-/
instance biprod.map_mono {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [Mono f]
    [Mono g] [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] : Mono (biprod.map f g) := by
  rw [show biprod.map f g = (biprod.isoProd _ _).hom ≫ prod.map f g ≫
    (biprod.isoProd _ _).inv by aesop]
  infer_instance

/--
Instance `coprod.map_mono` / 实例 `coprod.map_mono`

English:
instance coprod.map_mono
  signature: {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [Mono f]
  body: by
  rw [show coprod.map f g = (biprod.isoCoprod _ _).inv ≫ biprod.map f g ≫
    (biprod.isoCoprod _ _).hom by simp]
  infer_instance

中文:
实例 coprod.map_mono
  签名: {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [单态射 f]
  定义体: by
  rw [show coprod.map f g = (biprod.isoCoprod _ _).inv ≫ biprod.map f g ≫
    (biprod.isoCoprod _ _).hom by simp]
  infer_instance

Depends on / 依赖: biprod, biprod.isoCoprod, biprod.map, coprod, coprod.map, infer_instance, isoCoprod
-/
instance coprod.map_mono {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) [Mono f]
    [Mono g] [HasBinaryBiproduct W X] [HasBinaryBiproduct Y Z] : Mono (coprod.map f g) := by
  rw [show coprod.map f g = (biprod.isoCoprod _ _).inv ≫ biprod.map f g ≫
    (biprod.isoCoprod _ _).hom by simp]
  infer_instance

section BiprodKernel

section BinaryBicone

variable {X Y : C} (c : BinaryBicone X Y)

/--
Definition of `BinaryBicone.fstKernelFork` / `BinaryBicone.fstKernelFork` 的定义

English:
definition BinaryBicone.fstKernelFork
  signature: : KernelFork c.fst
  body: KernelFork.ofι c.inr c.inr_fst

@[simp]

中文:
定义 BinaryBicone.fstKernelFork
  签名: : 核叉 c.fst
  定义体: KernelFork.ofι c.inr c.inr_fst

@[simp]

Depends on / 依赖: KernelFork, KernelFork.of, c.inr, c.inr_fst, inr_fst
-/
def BinaryBicone.fstKernelFork : KernelFork c.fst :=
  KernelFork.ofι c.inr c.inr_fst

@[simp]
/--
theorem `BinaryBicone.fstKernelFork_ι` / 定理 `BinaryBicone.fstKernelFork_ι`

English:
theorem BinaryBicone.fstKernelFork_ι
  statement: (BinaryBicone.fstKernelFork c).ι = c.inr
  proof: rfl

中文:
定理 BinaryBicone.fstKernelFork_ι
  结论: (BinaryBicone.fstKernelFork c).ι = c.inr
  证明: rfl
-/
theorem BinaryBicone.fstKernelFork_ι : (BinaryBicone.fstKernelFork c).ι = c.inr := rfl

/--
Definition of `BinaryBicone.sndKernelFork` / `BinaryBicone.sndKernelFork` 的定义

English:
definition BinaryBicone.sndKernelFork
  signature: : KernelFork c.snd
  body: KernelFork.ofι c.inl c.inl_snd

@[simp]

中文:
定义 BinaryBicone.sndKernelFork
  签名: : 核叉 c.snd
  定义体: KernelFork.ofι c.inl c.inl_snd

@[simp]

Depends on / 依赖: KernelFork, KernelFork.of, c.inl, c.inl_snd, inl_snd
-/
def BinaryBicone.sndKernelFork : KernelFork c.snd :=
  KernelFork.ofι c.inl c.inl_snd

@[simp]
/--
theorem `BinaryBicone.sndKernelFork_ι` / 定理 `BinaryBicone.sndKernelFork_ι`

English:
theorem BinaryBicone.sndKernelFork_ι
  statement: (BinaryBicone.sndKernelFork c).ι = c.inl
  proof: rfl

中文:
定理 BinaryBicone.sndKernelFork_ι
  结论: (BinaryBicone.sndKernelFork c).ι = c.inl
  证明: rfl
-/
theorem BinaryBicone.sndKernelFork_ι : (BinaryBicone.sndKernelFork c).ι = c.inl := rfl

/--
Definition of `BinaryBicone.inlCokernelCofork` / `BinaryBicone.inlCokernelCofork` 的定义

English:
definition BinaryBicone.inlCokernelCofork
  signature: : CokernelCofork c.inl
  body: CokernelCofork.ofπ c.snd c.inl_snd

@[simp]

中文:
定义 BinaryBicone.inlCokernelCofork
  签名: : 余核余叉 c.inl
  定义体: CokernelCofork.ofπ c.snd c.inl_snd

@[simp]

Depends on / 依赖: CokernelCofork, CokernelCofork.of, c.inl_snd, c.snd, inl_snd
-/
def BinaryBicone.inlCokernelCofork : CokernelCofork c.inl :=
  CokernelCofork.ofπ c.snd c.inl_snd

@[simp]
/--
theorem `BinaryBicone.inlCokernelCofork_π` / 定理 `BinaryBicone.inlCokernelCofork_π`

English:
theorem BinaryBicone.inlCokernelCofork_π
  statement: (BinaryBicone.inlCokernelCofork c).π = c.snd
  proof: rfl

中文:
定理 BinaryBicone.inlCokernelCofork_π
  结论: (BinaryBicone.inlCokernelCofork c).π = c.snd
  证明: rfl
-/
theorem BinaryBicone.inlCokernelCofork_π : (BinaryBicone.inlCokernelCofork c).π = c.snd := rfl

/--
Definition of `BinaryBicone.inrCokernelCofork` / `BinaryBicone.inrCokernelCofork` 的定义

English:
definition BinaryBicone.inrCokernelCofork
  signature: : CokernelCofork c.inr
  body: CokernelCofork.ofπ c.fst c.inr_fst

@[simp]

中文:
定义 BinaryBicone.inrCokernelCofork
  签名: : 余核余叉 c.inr
  定义体: CokernelCofork.ofπ c.fst c.inr_fst

@[simp]

Depends on / 依赖: CokernelCofork, CokernelCofork.of, c.fst, c.inr_fst, inr_fst
-/
def BinaryBicone.inrCokernelCofork : CokernelCofork c.inr :=
  CokernelCofork.ofπ c.fst c.inr_fst

@[simp]
/--
theorem `BinaryBicone.inrCokernelCofork_π` / 定理 `BinaryBicone.inrCokernelCofork_π`

English:
theorem BinaryBicone.inrCokernelCofork_π
  statement: (BinaryBicone.inrCokernelCofork c).π = c.fst
  proof: rfl

中文:
定理 BinaryBicone.inrCokernelCofork_π
  结论: (BinaryBicone.inrCokernelCofork c).π = c.fst
  证明: rfl
-/
theorem BinaryBicone.inrCokernelCofork_π : (BinaryBicone.inrCokernelCofork c).π = c.fst := rfl

variable {c}

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `BinaryBicone.isLimitFstKernelFork` / `BinaryBicone.isLimitFstKernelFork` 的定义

English:
definition BinaryBicone.isLimitFstKernelFork
  signature: (i : IsLimit c.toCone)
  body: Fork.IsLimit.mk' _ fun s =>
    ⟨s.ι ≫ c.snd, by apply BinaryFan.IsLimit.hom_ext i <;> simp, fun hm => by simp [← hm]⟩

中文:
定义 BinaryBicone.isLimitFstKernelFork
  签名: (i : 是极限 c.toCone)
  定义体: Fork.IsLimit.mk' _ fun s =>
    ⟨s.ι ≫ c.snd, by apply BinaryFan.IsLimit.hom_ext i <;> simp, fun hm => by simp [← hm]⟩

Depends on / 依赖: BinaryFan, BinaryFan.IsLimit.hom_ext, Fork.IsLimit.mk, IsLimit, c.snd, hom_ext
-/
def BinaryBicone.isLimitFstKernelFork (i : IsLimit c.toCone) : IsLimit c.fstKernelFork :=
  Fork.IsLimit.mk' _ fun s =>
    ⟨s.ι ≫ c.snd, by apply BinaryFan.IsLimit.hom_ext i <;> simp, fun hm => by simp [← hm]⟩

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `BinaryBicone.isLimitSndKernelFork` / `BinaryBicone.isLimitSndKernelFork` 的定义

English:
definition BinaryBicone.isLimitSndKernelFork
  signature: (i : IsLimit c.toCone)
  body: Fork.IsLimit.mk' _ fun s =>
    ⟨s.ι ≫ c.fst, by apply BinaryFan.IsLimit.hom_ext i <;> simp, fun hm => by simp [← hm]⟩

中文:
定义 BinaryBicone.isLimitSndKernelFork
  签名: (i : 是极限 c.toCone)
  定义体: Fork.IsLimit.mk' _ fun s =>
    ⟨s.ι ≫ c.fst, by apply BinaryFan.IsLimit.hom_ext i <;> simp, fun hm => by simp [← hm]⟩

Depends on / 依赖: BinaryFan, BinaryFan.IsLimit.hom_ext, Fork.IsLimit.mk, IsLimit, c.fst, hom_ext
-/
def BinaryBicone.isLimitSndKernelFork (i : IsLimit c.toCone) : IsLimit c.sndKernelFork :=
  Fork.IsLimit.mk' _ fun s =>
    ⟨s.ι ≫ c.fst, by apply BinaryFan.IsLimit.hom_ext i <;> simp, fun hm => by simp [← hm]⟩

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `BinaryBicone.isColimitInlCokernelCofork` / `BinaryBicone.isColimitInlCokernelCofork` 的定义

English:
definition BinaryBicone.isColimitInlCokernelCofork
  signature: (i : IsColimit c.toCocone)
  body: Cofork.IsColimit.mk' _ fun s =>
    ⟨c.inr ≫ s.π, by apply BinaryCofan.IsColimit.hom_ext i <;> simp, fun hm => by simp [← hm]⟩

中文:
定义 BinaryBicone.isColimitInlCokernelCofork
  签名: (i : 是余极限 c.toCocone)
  定义体: Cofork.IsColimit.mk' _ fun s =>
    ⟨c.inr ≫ s.π, by apply BinaryCofan.IsColimit.hom_ext i <;> simp, fun hm => by simp [← hm]⟩

Depends on / 依赖: BinaryCofan, BinaryCofan.IsColimit.hom_ext, Cofork, Cofork.IsColimit.mk, IsColimit, c.inr, hom_ext
-/
def BinaryBicone.isColimitInlCokernelCofork (i : IsColimit c.toCocone) :
    IsColimit c.inlCokernelCofork :=
  Cofork.IsColimit.mk' _ fun s =>
    ⟨c.inr ≫ s.π, by apply BinaryCofan.IsColimit.hom_ext i <;> simp, fun hm => by simp [← hm]⟩

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `BinaryBicone.isColimitInrCokernelCofork` / `BinaryBicone.isColimitInrCokernelCofork` 的定义

English:
definition BinaryBicone.isColimitInrCokernelCofork
  signature: (i : IsColimit c.toCocone)
  body: Cofork.IsColimit.mk' _ fun s =>
    ⟨c.inl ≫ s.π, by apply BinaryCofan.IsColimit.hom_ext i <;> simp, fun hm => by simp [← hm]⟩

中文:
定义 BinaryBicone.isColimitInrCokernelCofork
  签名: (i : 是余极限 c.toCocone)
  定义体: Cofork.IsColimit.mk' _ fun s =>
    ⟨c.inl ≫ s.π, by apply BinaryCofan.IsColimit.hom_ext i <;> simp, fun hm => by simp [← hm]⟩

Depends on / 依赖: BinaryCofan, BinaryCofan.IsColimit.hom_ext, Cofork, Cofork.IsColimit.mk, IsColimit, c.inl, hom_ext
-/
def BinaryBicone.isColimitInrCokernelCofork (i : IsColimit c.toCocone) :
    IsColimit c.inrCokernelCofork :=
  Cofork.IsColimit.mk' _ fun s =>
    ⟨c.inl ≫ s.π, by apply BinaryCofan.IsColimit.hom_ext i <;> simp, fun hm => by simp [← hm]⟩

end BinaryBicone

section HasBinaryBiproduct

variable (X Y : C) [HasBinaryBiproduct X Y]

/--
Definition of `biprod.fstKernelFork` / `biprod.fstKernelFork` 的定义

English:
definition biprod.fstKernelFork
  signature: : KernelFork (biprod.fst : X ⊞ Y ⟶ X)
  body: BinaryBicone.fstKernelFork _

@[simp]

中文:
定义 biprod.fstKernelFork
  签名: : 核叉 (biprod.fst : X ⊞ Y ⟶ X)
  定义体: BinaryBicone.fstKernelFork _

@[simp]

Depends on / 依赖: BinaryBicone, BinaryBicone.fstKernelFork, fstKernelFork
-/
def biprod.fstKernelFork : KernelFork (biprod.fst : X ⊞ Y ⟶ X) :=
  BinaryBicone.fstKernelFork _

@[simp]
/--
theorem `biprod.fstKernelFork_ι` / 定理 `biprod.fstKernelFork_ι`

English:
theorem biprod.fstKernelFork_ι
  statement: Fork.ι (biprod.fstKernelFork X Y) = (biprod.inr : Y ⟶ X ⊞ Y)
  proof: rfl

中文:
定理 biprod.fstKernelFork_ι
  结论: 叉.ι (biprod.fstKernelFork X Y) = (biprod.inr : Y ⟶ X ⊞ Y)
  证明: rfl
-/
theorem biprod.fstKernelFork_ι : Fork.ι (biprod.fstKernelFork X Y) = (biprod.inr : Y ⟶ X ⊞ Y) :=
  rfl

/--
Definition of `biprod.isKernelFstKernelFork` / `biprod.isKernelFstKernelFork` 的定义

English:
definition biprod.isKernelFstKernelFork
  signature: : IsLimit (biprod.fstKernelFork X Y)
  body: BinaryBicone.isLimitFstKernelFork (BinaryBiproduct.isLimit _ _)

中文:
定义 biprod.isKernelFstKernelFork
  签名: : 是极限 (biprod.fstKernelFork X Y)
  定义体: BinaryBicone.isLimitFstKernelFork (BinaryBiproduct.isLimit _ _)

Depends on / 依赖: BinaryBicone, BinaryBicone.isLimitFstKernelFork, BinaryBiproduct, BinaryBiproduct.isLimit, Monoidal, functor, functor.Monoidal, isLimit, isLimitFstKernelFork
-/
def biprod.isKernelFstKernelFork : IsLimit (biprod.fstKernelFork X Y) :=
  BinaryBicone.isLimitFstKernelFork (BinaryBiproduct.isLimit _ _)

/--
Definition of `biprod.sndKernelFork` / `biprod.sndKernelFork` 的定义

English:
definition biprod.sndKernelFork
  signature: : KernelFork (biprod.snd : X ⊞ Y ⟶ Y)
  body: BinaryBicone.sndKernelFork _

@[simp]

中文:
定义 biprod.sndKernelFork
  签名: : 核叉 (biprod.snd : X ⊞ Y ⟶ Y)
  定义体: BinaryBicone.sndKernelFork _

@[simp]

Depends on / 依赖: BinaryBicone, BinaryBicone.sndKernelFork, Monoidal, inverse, inverse.Monoidal, sndKernelFork
-/
def biprod.sndKernelFork : KernelFork (biprod.snd : X ⊞ Y ⟶ Y) :=
  BinaryBicone.sndKernelFork _

@[simp]
/--
theorem `biprod.sndKernelFork_ι` / 定理 `biprod.sndKernelFork_ι`

English:
theorem biprod.sndKernelFork_ι
  statement: Fork.ι (biprod.sndKernelFork X Y) = (biprod.inl : X ⟶ X ⊞ Y)
  proof: rfl

中文:
定理 biprod.sndKernelFork_ι
  结论: 叉.ι (biprod.sndKernelFork X Y) = (biprod.inl : X ⟶ X ⊞ Y)
  证明: rfl

Depends on / 依赖: IsMonoidal
-/
theorem biprod.sndKernelFork_ι : Fork.ι (biprod.sndKernelFork X Y) = (biprod.inl : X ⟶ X ⊞ Y) :=
  rfl

/--
Definition of `biprod.isKernelSndKernelFork` / `biprod.isKernelSndKernelFork` 的定义

English:
definition biprod.isKernelSndKernelFork
  signature: : IsLimit (biprod.sndKernelFork X Y)
  body: BinaryBicone.isLimitSndKernelFork (BinaryBiproduct.isLimit _ _)

中文:
定义 biprod.isKernelSndKernelFork
  签名: : 是极限 (biprod.sndKernelFork X Y)
  定义体: BinaryBicone.isLimitSndKernelFork (BinaryBiproduct.isLimit _ _)

Depends on / 依赖: BinaryBicone, BinaryBicone.isLimitSndKernelFork, BinaryBiproduct, BinaryBiproduct.isLimit, isLimit, isLimitSndKernelFork
-/
def biprod.isKernelSndKernelFork : IsLimit (biprod.sndKernelFork X Y) :=
  BinaryBicone.isLimitSndKernelFork (BinaryBiproduct.isLimit _ _)

/--
Definition of `biprod.inlCokernelCofork` / `biprod.inlCokernelCofork` 的定义

English:
definition biprod.inlCokernelCofork
  signature: : CokernelCofork (biprod.inl : X ⟶ X ⊞ Y)
  body: BinaryBicone.inlCokernelCofork _

@[simp]

中文:
定义 biprod.inlCokernelCofork
  签名: : 余核余叉 (biprod.inl : X ⟶ X ⊞ Y)
  定义体: BinaryBicone.inlCokernelCofork _

@[simp]

Depends on / 依赖: BinaryBicone, BinaryBicone.inlCokernelCofork, inlCokernelCofork
-/
def biprod.inlCokernelCofork : CokernelCofork (biprod.inl : X ⟶ X ⊞ Y) :=
  BinaryBicone.inlCokernelCofork _

@[simp]
/--
theorem `biprod.inlCokernelCofork_π` / 定理 `biprod.inlCokernelCofork_π`

English:
theorem biprod.inlCokernelCofork_π
  statement: Cofork.π (biprod.inlCokernelCofork X Y) = biprod.snd
  proof: rfl

中文:
定理 biprod.inlCokernelCofork_π
  结论: 余叉.π (biprod.inlCokernelCofork X Y) = biprod.snd
  证明: rfl
-/
theorem biprod.inlCokernelCofork_π : Cofork.π (biprod.inlCokernelCofork X Y) = biprod.snd :=
  rfl

/--
Definition of `biprod.isCokernelInlCokernelFork` / `biprod.isCokernelInlCokernelFork` 的定义

English:
definition biprod.isCokernelInlCokernelFork
  signature: : IsColimit (biprod.inlCokernelCofork X Y)
  body: BinaryBicone.isColimitInlCokernelCofork (BinaryBiproduct.isColimit _ _)

中文:
定义 biprod.isCokernelInlCokernelFork
  签名: : 是余极限 (biprod.inlCokernelCofork X Y)
  定义体: BinaryBicone.isColimitInlCokernelCofork (BinaryBiproduct.isColimit _ _)

Depends on / 依赖: BinaryBicone, BinaryBicone.isColimitInlCokernelCofork, BinaryBiproduct, BinaryBiproduct.isColimit, isColimit, isColimitInlCokernelCofork
-/
def biprod.isCokernelInlCokernelFork : IsColimit (biprod.inlCokernelCofork X Y) :=
  BinaryBicone.isColimitInlCokernelCofork (BinaryBiproduct.isColimit _ _)

/--
Definition of `biprod.inrCokernelCofork` / `biprod.inrCokernelCofork` 的定义

English:
definition biprod.inrCokernelCofork
  signature: : CokernelCofork (biprod.inr : Y ⟶ X ⊞ Y)
  body: BinaryBicone.inrCokernelCofork _

@[simp]

中文:
定义 biprod.inrCokernelCofork
  签名: : 余核余叉 (biprod.inr : Y ⟶ X ⊞ Y)
  定义体: BinaryBicone.inrCokernelCofork _

@[simp]

Depends on / 依赖: BinaryBicone, BinaryBicone.inrCokernelCofork, inrCokernelCofork
-/
def biprod.inrCokernelCofork : CokernelCofork (biprod.inr : Y ⟶ X ⊞ Y) :=
  BinaryBicone.inrCokernelCofork _

@[simp]
/--
theorem `biprod.inrCokernelCofork_π` / 定理 `biprod.inrCokernelCofork_π`

English:
theorem biprod.inrCokernelCofork_π
  statement: Cofork.π (biprod.inrCokernelCofork X Y) = biprod.fst
  proof: rfl

中文:
定理 biprod.inrCokernelCofork_π
  结论: 余叉.π (biprod.inrCokernelCofork X Y) = biprod.fst
  证明: rfl
-/
theorem biprod.inrCokernelCofork_π : Cofork.π (biprod.inrCokernelCofork X Y) = biprod.fst :=
  rfl

/--
Definition of `biprod.isCokernelInrCokernelFork` / `biprod.isCokernelInrCokernelFork` 的定义

English:
definition biprod.isCokernelInrCokernelFork
  signature: : IsColimit (biprod.inrCokernelCofork X Y)
  body: BinaryBicone.isColimitInrCokernelCofork (BinaryBiproduct.isColimit _ _)

中文:
定义 biprod.isCokernelInrCokernelFork
  签名: : 是余极限 (biprod.inrCokernelCofork X Y)
  定义体: BinaryBicone.isColimitInrCokernelCofork (BinaryBiproduct.isColimit _ _)

Depends on / 依赖: BinaryBicone, BinaryBicone.isColimitInrCokernelCofork, BinaryBiproduct, BinaryBiproduct.isColimit, isColimit, isColimitInrCokernelCofork
-/
def biprod.isCokernelInrCokernelFork : IsColimit (biprod.inrCokernelCofork X Y) :=
  BinaryBicone.isColimitInrCokernelCofork (BinaryBiproduct.isColimit _ _)

section

variable (P Q) [HasBinaryBiproduct P Q]

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `biprod.opIso` / `biprod.opIso` 的定义

English:
definition biprod.opIso
  signature: : op (P ⊞ Q) ≅ op P ⊞ op Q
  body: biprod.uniqueUpToIso _ _ (getBinaryBiproductData P Q).op.isBilimit

@[reassoc (attr := simp)]

中文:
定义 biprod.opIso
  签名: : op (P ⊞ Q) ≅ op P ⊞ op Q
  定义体: biprod.uniqueUpToIso _ _ (getBinaryBiproductData P Q).op.isBilimit

@[reassoc (attr := simp)]

Depends on / 依赖: biprod, biprod.uniqueUpToIso, getBinaryBiproductData, isBilimit, op.isBilimit, uniqueUpToIso
-/
def biprod.opIso : op (P ⊞ Q) ≅ op P ⊞ op Q :=
  biprod.uniqueUpToIso _ _ (getBinaryBiproductData P Q).op.isBilimit

@[reassoc (attr := simp)]
/--
lemma `biprod.opIso_hom_fst` / 引理 `biprod.opIso_hom_fst`

English:
lemma biprod.opIso_hom_fst
  statement: (opIso P Q).hom ≫ fst = inl.op
  proof: lift_fst _ _

@[reassoc (attr := simp)]

中文:
引理 biprod.opIso_hom_fst
  结论: (opIso P Q).hom ≫ fst = inl.op
  证明: lift_fst _ _

@[reassoc (attr := simp)]

Depends on / 依赖: lift_fst
-/
lemma biprod.opIso_hom_fst : (opIso P Q).hom ≫ fst = inl.op := lift_fst _ _

@[reassoc (attr := simp)]
/--
lemma `biprod.opIso_hom_snd` / 引理 `biprod.opIso_hom_snd`

English:
lemma biprod.opIso_hom_snd
  statement: (opIso P Q).hom ≫ snd = inr.op
  proof: lift_snd _ _

@[reassoc (attr := simp)]

中文:
引理 biprod.opIso_hom_snd
  结论: (opIso P Q).hom ≫ snd = inr.op
  证明: lift_snd _ _

@[reassoc (attr := simp)]

Depends on / 依赖: lift_snd
-/
lemma biprod.opIso_hom_snd : (opIso P Q).hom ≫ snd = inr.op := lift_snd _ _

@[reassoc (attr := simp)]
/--
lemma `biprod.inl_opIso_inv` / 引理 `biprod.inl_opIso_inv`

English:
lemma biprod.inl_opIso_inv
  statement: inl ≫ (opIso P Q).inv = fst.op
  proof: inl_desc _ _

@[reassoc (attr := simp)]

中文:
引理 biprod.inl_opIso_inv
  结论: inl ≫ (opIso P Q).inv = fst.op
  证明: inl_desc _ _

@[reassoc (attr := simp)]

Depends on / 依赖: inl_desc
-/
lemma biprod.inl_opIso_inv : inl ≫ (opIso P Q).inv = fst.op := inl_desc _ _

@[reassoc (attr := simp)]
/--
lemma `biprod.inr_opIso_inv` / 引理 `biprod.inr_opIso_inv`

English:
lemma biprod.inr_opIso_inv
  statement: inr ≫ (opIso P Q).inv = snd.op
  proof: inr_desc _ _

@[reassoc (attr := simp)]

中文:
引理 biprod.inr_opIso_inv
  结论: inr ≫ (opIso P Q).inv = snd.op
  证明: inr_desc _ _

@[reassoc (attr := simp)]

Depends on / 依赖: inr_desc
-/
lemma biprod.inr_opIso_inv : inr ≫ (opIso P Q).inv = snd.op := inr_desc _ _

@[reassoc (attr := simp)]
/--
lemma `biprod.fst_op_opIso_hom` / 引理 `biprod.fst_op_opIso_hom`

English:
lemma biprod.fst_op_opIso_hom
  statement: fst.op ≫ (opIso P Q).hom = inl
  proof: by
  ext <;> simp [← op_comp]

@[reassoc (attr := simp)]

中文:
引理 biprod.fst_op_opIso_hom
  结论: fst.op ≫ (opIso P Q).hom = inl
  证明: by
  ext <;> simp [← op_comp]

@[reassoc (attr := simp)]

Depends on / 依赖: op_comp
-/
lemma biprod.fst_op_opIso_hom : fst.op ≫ (opIso P Q).hom = inl := by
  ext <;> simp [← op_comp]

@[reassoc (attr := simp)]
/--
lemma `biprod.snd_op_opIso_hom` / 引理 `biprod.snd_op_opIso_hom`

English:
lemma biprod.snd_op_opIso_hom
  statement: snd.op ≫ (opIso P Q).hom = inr
  proof: by
  ext <;> simp [← op_comp]

@[reassoc (attr := simp)]

中文:
引理 biprod.snd_op_opIso_hom
  结论: snd.op ≫ (opIso P Q).hom = inr
  证明: by
  ext <;> simp [← op_comp]

@[reassoc (attr := simp)]

Depends on / 依赖: op_comp
-/
lemma biprod.snd_op_opIso_hom : snd.op ≫ (opIso P Q).hom = inr := by
  ext <;> simp [← op_comp]

@[reassoc (attr := simp)]
/--
lemma `biprod.opIso_inv_inl_op` / 引理 `biprod.opIso_inv_inl_op`

English:
lemma biprod.opIso_inv_inl_op
  statement: (opIso P Q).inv ≫ inl.op = fst
  proof: by
  ext <;> simp [← op_comp]

@[reassoc (attr := simp)]

中文:
引理 biprod.opIso_inv_inl_op
  结论: (opIso P Q).inv ≫ inl.op = fst
  证明: by
  ext <;> simp [← op_comp]

@[reassoc (attr := simp)]

Depends on / 依赖: op_comp
-/
lemma biprod.opIso_inv_inl_op : (opIso P Q).inv ≫ inl.op = fst := by
  ext <;> simp [← op_comp]

@[reassoc (attr := simp)]
/--
lemma `biprod.opIso_inv_inr_op` / 引理 `biprod.opIso_inv_inr_op`

English:
lemma biprod.opIso_inv_inr_op
  statement: (opIso P Q).inv ≫ inr.op = snd
  proof: by
  ext <;> simp [← op_comp]

中文:
引理 biprod.opIso_inv_inr_op
  结论: (opIso P Q).inv ≫ inr.op = snd
  证明: by
  ext <;> simp [← op_comp]

Depends on / 依赖: op_comp
-/
lemma biprod.opIso_inv_inr_op : (opIso P Q).inv ≫ inr.op = snd := by
  ext <;> simp [← op_comp]

end

end HasBinaryBiproduct

variable {X Y : C} [HasBinaryBiproduct X Y]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasKernel (biprod.fst : X ⊞ Y ⟶ X)
  body: HasLimit.mk ⟨_, biprod.isKernelFstKernelFork X Y⟩

中文:
实例 :
  签名: HasKernel (biprod.fst : X ⊞ Y ⟶ X)
  定义体: HasLimit.mk ⟨_, biprod.isKernelFstKernelFork X Y⟩

Depends on / 依赖: HasLimit, HasLimit.mk, biprod, biprod.isKernelFstKernelFork, isKernelFstKernelFork
-/
instance : HasKernel (biprod.fst : X ⊞ Y ⟶ X) :=
  HasLimit.mk ⟨_, biprod.isKernelFstKernelFork X Y⟩

/-- The kernel of `biprod.fst : X ⊞ Y ⟶ X` is `Y`. -/
@[simps!]
/--
Definition of `kernelBiprodFstIso` / `kernelBiprodFstIso` 的定义

English:
definition kernelBiprodFstIso
  signature: : kernel (biprod.fst : X ⊞ Y ⟶ X) ≅ Y
  body: limit.isoLimitCone ⟨_, biprod.isKernelFstKernelFork X Y⟩

中文:
定义 kernelBiprodFstIso
  签名: : kernel (biprod.fst : X ⊞ Y ⟶ X) ≅ Y
  定义体: limit.isoLimitCone ⟨_, biprod.isKernelFstKernelFork X Y⟩

Depends on / 依赖: biprod, biprod.isKernelFstKernelFork, isKernelFstKernelFork, isoLimitCone, limit.isoLimitCone
-/
def kernelBiprodFstIso : kernel (biprod.fst : X ⊞ Y ⟶ X) ≅ Y :=
  limit.isoLimitCone ⟨_, biprod.isKernelFstKernelFork X Y⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasKernel (biprod.snd : X ⊞ Y ⟶ Y)
  body: HasLimit.mk ⟨_, biprod.isKernelSndKernelFork X Y⟩

中文:
实例 :
  签名: HasKernel (biprod.snd : X ⊞ Y ⟶ Y)
  定义体: HasLimit.mk ⟨_, biprod.isKernelSndKernelFork X Y⟩

Depends on / 依赖: HasLimit, HasLimit.mk, biprod, biprod.isKernelSndKernelFork, isKernelSndKernelFork
-/
instance : HasKernel (biprod.snd : X ⊞ Y ⟶ Y) :=
  HasLimit.mk ⟨_, biprod.isKernelSndKernelFork X Y⟩

/-- The kernel of `biprod.snd : X ⊞ Y ⟶ Y` is `X`. -/
@[simps!]
/--
Definition of `kernelBiprodSndIso` / `kernelBiprodSndIso` 的定义

English:
definition kernelBiprodSndIso
  signature: : kernel (biprod.snd : X ⊞ Y ⟶ Y) ≅ X
  body: limit.isoLimitCone ⟨_, biprod.isKernelSndKernelFork X Y⟩

中文:
定义 kernelBiprodSndIso
  签名: : kernel (biprod.snd : X ⊞ Y ⟶ Y) ≅ X
  定义体: limit.isoLimitCone ⟨_, biprod.isKernelSndKernelFork X Y⟩

Depends on / 依赖: biprod, biprod.isKernelSndKernelFork, isKernelSndKernelFork, isoLimitCone, limit.isoLimitCone
-/
def kernelBiprodSndIso : kernel (biprod.snd : X ⊞ Y ⟶ Y) ≅ X :=
  limit.isoLimitCone ⟨_, biprod.isKernelSndKernelFork X Y⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasCokernel (biprod.inl : X ⟶ X ⊞ Y)
  body: HasColimit.mk ⟨_, biprod.isCokernelInlCokernelFork X Y⟩

中文:
实例 :
  签名: HasCokernel (biprod.inl : X ⟶ X ⊞ Y)
  定义体: HasColimit.mk ⟨_, biprod.isCokernelInlCokernelFork X Y⟩

Depends on / 依赖: HasColimit, HasColimit.mk, biprod, biprod.isCokernelInlCokernelFork, isCokernelInlCokernelFork
-/
instance : HasCokernel (biprod.inl : X ⟶ X ⊞ Y) :=
  HasColimit.mk ⟨_, biprod.isCokernelInlCokernelFork X Y⟩

/-- The cokernel of `biprod.inl : X ⟶ X ⊞ Y` is `Y`. -/
@[simps!]
/--
Definition of `cokernelBiprodInlIso` / `cokernelBiprodInlIso` 的定义

English:
definition cokernelBiprodInlIso
  signature: : cokernel (biprod.inl : X ⟶ X ⊞ Y) ≅ Y
  body: colimit.isoColimitCocone ⟨_, biprod.isCokernelInlCokernelFork X Y⟩

中文:
定义 cokernelBiprodInlIso
  签名: : cokernel (biprod.inl : X ⟶ X ⊞ Y) ≅ Y
  定义体: colimit.isoColimitCocone ⟨_, biprod.isCokernelInlCokernelFork X Y⟩

Depends on / 依赖: biprod, biprod.isCokernelInlCokernelFork, colimit, colimit.isoColimitCocone, isCokernelInlCokernelFork, isoColimitCocone
-/
def cokernelBiprodInlIso : cokernel (biprod.inl : X ⟶ X ⊞ Y) ≅ Y :=
  colimit.isoColimitCocone ⟨_, biprod.isCokernelInlCokernelFork X Y⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasCokernel (biprod.inr : Y ⟶ X ⊞ Y)
  body: HasColimit.mk ⟨_, biprod.isCokernelInrCokernelFork X Y⟩

中文:
实例 :
  签名: HasCokernel (biprod.inr : Y ⟶ X ⊞ Y)
  定义体: HasColimit.mk ⟨_, biprod.isCokernelInrCokernelFork X Y⟩

Depends on / 依赖: HasColimit, HasColimit.mk, biprod, biprod.isCokernelInrCokernelFork, isCokernelInrCokernelFork
-/
instance : HasCokernel (biprod.inr : Y ⟶ X ⊞ Y) :=
  HasColimit.mk ⟨_, biprod.isCokernelInrCokernelFork X Y⟩

/-- The cokernel of `biprod.inr : Y ⟶ X ⊞ Y` is `X`. -/
@[simps!]
/--
Definition of `cokernelBiprodInrIso` / `cokernelBiprodInrIso` 的定义

English:
definition cokernelBiprodInrIso
  signature: : cokernel (biprod.inr : Y ⟶ X ⊞ Y) ≅ X
  body: colimit.isoColimitCocone ⟨_, biprod.isCokernelInrCokernelFork X Y⟩

中文:
定义 cokernelBiprodInrIso
  签名: : cokernel (biprod.inr : Y ⟶ X ⊞ Y) ≅ X
  定义体: colimit.isoColimitCocone ⟨_, biprod.isCokernelInrCokernelFork X Y⟩

Depends on / 依赖: biprod, biprod.isCokernelInrCokernelFork, colimit, colimit.isoColimitCocone, isCokernelInrCokernelFork, isoColimitCocone
-/
def cokernelBiprodInrIso : cokernel (biprod.inr : Y ⟶ X ⊞ Y) ≅ X :=
  colimit.isoColimitCocone ⟨_, biprod.isCokernelInrCokernelFork X Y⟩

end BiprodKernel

section IsZero

/-- If `Y` is a zero object, `X ≅ X ⊞ Y` for any `X`. -/
@[simps!]
/--
Definition of `isoBiprodZero` / `isoBiprodZero` 的定义

English:
definition isoBiprodZero
  signature: {X Y : C} [HasBinaryBiproduct X Y] (hY : IsZero Y)
  body: biprod.inl
  inv := biprod.fst
  inv_hom_id := by
    apply CategoryTheory.Limits.biprod.hom_ext <;>
      simp only [Category.assoc, biprod.inl_fst, Category.comp_id, Category.id_comp, biprod.inl_snd,
        comp_zero]
    apply hY.eq_of_tgt

中文:
定义 isoBiprodZero
  签名: {X Y : C} [有BinaryBiproduct X Y] (hY : 是零 Y)
  定义体: biprod.inl
  inv := biprod.fst
  inv_hom_id := by
    apply CategoryTheory.Limits.biprod.hom_ext <;>
      simp only [Category.assoc, biprod.inl_fst, Category.comp_id, Category.id_comp, biprod.inl_snd,
        comp_zero]
    apply hY.eq_of_tgt

Depends on / 依赖: biprod, biprod.inl
-/
def isoBiprodZero {X Y : C} [HasBinaryBiproduct X Y] (hY : IsZero Y) : X ≅ X ⊞ Y where
  hom := biprod.inl
  inv := biprod.fst
  inv_hom_id := by
    apply CategoryTheory.Limits.biprod.hom_ext <;>
      simp only [Category.assoc, biprod.inl_fst, Category.comp_id, Category.id_comp, biprod.inl_snd,
        comp_zero]
    apply hY.eq_of_tgt

/-- If `X` is a zero object, `Y ≅ X ⊞ Y` for any `Y`. -/
@[simps]
/--
Definition of `isoZeroBiprod` / `isoZeroBiprod` 的定义

English:
definition isoZeroBiprod
  signature: {X Y : C} [HasBinaryBiproduct X Y] (hY : IsZero X)
  body: biprod.inr
  inv := biprod.snd
  inv_hom_id := by
    apply CategoryTheory.Limits.biprod.hom_ext <;>
      simp only [Category.assoc, biprod.inr_snd, Category.comp_id, Category.id_comp, biprod.inr_fst,
        comp_zero]
    apply hY.eq_of_tgt

@[simp]

中文:
定义 isoZeroBiprod
  签名: {X Y : C} [有BinaryBiproduct X Y] (hY : 是零 X)
  定义体: biprod.inr
  inv := biprod.snd
  inv_hom_id := by
    apply CategoryTheory.Limits.biprod.hom_ext <;>
      simp only [Category.assoc, biprod.inr_snd, Category.comp_id, Category.id_comp, biprod.inr_fst,
        comp_zero]
    apply hY.eq_of_tgt

@[simp]

Depends on / 依赖: biprod, biprod.inr
-/
def isoZeroBiprod {X Y : C} [HasBinaryBiproduct X Y] (hY : IsZero X) : Y ≅ X ⊞ Y where
  hom := biprod.inr
  inv := biprod.snd
  inv_hom_id := by
    apply CategoryTheory.Limits.biprod.hom_ext <;>
      simp only [Category.assoc, biprod.inr_snd, Category.comp_id, Category.id_comp, biprod.inr_fst,
        comp_zero]
    apply hY.eq_of_tgt

@[simp]
/--
lemma `biprod_isZero_iff` / 引理 `biprod_isZero_iff`

English:
lemma biprod_isZero_iff
  given: (A B : C) [HasBinaryBiproduct A B]
  proof: by
  constructor
  · intro h
    simp only [IsZero.iff_id_eq_zero] at h ⊢
    simp only [show 𝟙 A = biprod.inl ≫ 𝟙 (A ⊞ B) ≫ biprod.fst by simp,
      show 𝟙 B = biprod.inr ≫ 𝟙 (A ⊞ B) ≫ biprod.snd by simp, h, zero_comp, comp_zero,
      and_self]
  · rintro ⟨hA, hB⟩
    rw [IsZero.iff_id_eq_zero]
    apply biprod.hom_ext
    · apply hA.eq_of_tgt
    · apply hB.eq_of_tgt

中文:
引理 biprod_isZero_iff
  条件: (A B : C) [有BinaryBiproduct A B]
  证明: by
  constructor
  · intro h
    simp only [IsZero.iff_id_eq_zero] at h ⊢
    simp only [show 𝟙 A = biprod.inl ≫ 𝟙 (A ⊞ B) ≫ biprod.fst by simp,
      show 𝟙 B = biprod.inr ≫ 𝟙 (A ⊞ B) ≫ biprod.snd by simp, h, zero_comp, comp_zero,
      and_self]
  · rintro ⟨hA, hB⟩
    rw [IsZero.iff_id_eq_zero]
    apply biprod.hom_ext
    · apply hA.eq_of_tgt
    · apply hB.eq_of_tgt

Depends on / 依赖: IsZero, IsZero.iff_id_eq_zero, and_self, biprod, biprod.fst, biprod.hom_ext, biprod.inl, biprod.inr, biprod.snd, comp_zero, eq_of_tgt, hA.eq_of_tgt, hB.eq_of_tgt, hom_ext, iff_id_eq_zero, zero_comp
-/
lemma biprod_isZero_iff (A B : C) [HasBinaryBiproduct A B] :
    IsZero (biprod A B) ↔ IsZero A ∧ IsZero B := by
  constructor
  · intro h
    simp only [IsZero.iff_id_eq_zero] at h ⊢
    simp only [show 𝟙 A = biprod.inl ≫ 𝟙 (A ⊞ B) ≫ biprod.fst by simp,
      show 𝟙 B = biprod.inr ≫ 𝟙 (A ⊞ B) ≫ biprod.snd by simp, h, zero_comp, comp_zero,
      and_self]
  · rintro ⟨hA, hB⟩
    rw [IsZero.iff_id_eq_zero]
    apply biprod.hom_ext
    · apply hA.eq_of_tgt
    · apply hB.eq_of_tgt

end IsZero

section

variable [HasBinaryBiproducts C]

/-- The braiding isomorphism which swaps a binary biproduct. -/
@[simps]
/--
Definition of `biprod.braiding` / `biprod.braiding` 的定义

English:
definition biprod.braiding
  signature: (P Q : C)
  body: biprod.lift biprod.snd biprod.fst
  inv := biprod.lift biprod.snd biprod.fst

中文:
定义 biprod.braiding
  签名: (P Q : C)
  定义体: biprod.lift biprod.snd biprod.fst
  inv := biprod.lift biprod.snd biprod.fst

Depends on / 依赖: biprod, biprod.fst, biprod.lift, biprod.snd
-/
def biprod.braiding (P Q : C) : P ⊞ Q ≅ Q ⊞ P where
  hom := biprod.lift biprod.snd biprod.fst
  inv := biprod.lift biprod.snd biprod.fst

/-- An alternative formula for the braiding isomorphism which swaps a binary biproduct,
using the fact that the biproduct is a coproduct. -/
@[simps]
/--
Definition of `biprod.braiding'` / `biprod.braiding'` 的定义

English:
definition biprod.braiding'
  signature: (P Q : C)
  body: biprod.desc biprod.inr biprod.inl
  inv := biprod.desc biprod.inr biprod.inl

中文:
定义 biprod.braiding'
  签名: (P Q : C)
  定义体: biprod.desc biprod.inr biprod.inl
  inv := biprod.desc biprod.inr biprod.inl

Depends on / 依赖: biprod, biprod.desc, biprod.inl, biprod.inr
-/
def biprod.braiding' (P Q : C) : P ⊞ Q ≅ Q ⊞ P where
  hom := biprod.desc biprod.inr biprod.inl
  inv := biprod.desc biprod.inr biprod.inl

/--
theorem `biprod.braiding'_eq_braiding` / 定理 `biprod.braiding'_eq_braiding`

English:
theorem biprod.braiding'_eq_braiding
  given: {P Q : C}
  statement: biprod.braiding' P Q = biprod.braiding P Q
  proof: by
  cat_disch

中文:
定理 biprod.braiding'_eq_braiding
  条件: {P Q : C}
  结论: biprod.braiding' P Q = biprod.braiding P Q
  证明: by
  cat_disch
-/
theorem biprod.braiding'_eq_braiding {P Q : C} : biprod.braiding' P Q = biprod.braiding P Q := by
  cat_disch

/-- The braiding isomorphism can be passed through a map by swapping the order. -/
@[reassoc]
/--
theorem `biprod.braid_natural` / 定理 `biprod.braid_natural`

English:
theorem biprod.braid_natural
  given: {W X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ W)
  proof: by
  cat_disch

@[reassoc]

中文:
定理 biprod.braid_natural
  条件: {W X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ W)
  证明: by
  cat_disch

@[reassoc]

Depends on / 依赖: cat_disch
-/
theorem biprod.braid_natural {W X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ W) :
    biprod.map f g ≫ (biprod.braiding _ _).hom = (biprod.braiding _ _).hom ≫ biprod.map g f := by
  cat_disch

@[reassoc]
/--
theorem `biprod.braiding_map_braiding` / 定理 `biprod.braiding_map_braiding`

English:
theorem biprod.braiding_map_braiding
  given: {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z)
  proof: by
  cat_disch

@[reassoc (attr := simp)]

中文:
定理 biprod.braiding_map_braiding
  条件: {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z)
  证明: by
  cat_disch

@[reassoc (attr := simp)]

Depends on / 依赖: cat_disch
-/
theorem biprod.braiding_map_braiding {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z) :
    (biprod.braiding X W).hom ≫ biprod.map f g ≫ (biprod.braiding Y Z).hom = biprod.map g f := by
  cat_disch

@[reassoc (attr := simp)]
/--
theorem `biprod.symmetry'` / 定理 `biprod.symmetry'`

English:
theorem biprod.symmetry'
  given: (P Q : C)
  proof: by
  cat_disch

中文:
定理 biprod.symmetry'
  条件: (P Q : C)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
theorem biprod.symmetry' (P Q : C) :
    biprod.lift biprod.snd biprod.fst ≫ biprod.lift biprod.snd biprod.fst = 𝟙 (P ⊞ Q) := by
  cat_disch

/-- The braiding isomorphism is symmetric. -/
@[reassoc]
/--
theorem `biprod.symmetry` / 定理 `biprod.symmetry`

English:
theorem biprod.symmetry
  given: (P Q : C)
  proof: by simp

中文:
定理 biprod.symmetry
  条件: (P Q : C)
  证明: by simp
-/
theorem biprod.symmetry (P Q : C) :
    (biprod.braiding P Q).hom ≫ (biprod.braiding Q P).hom = 𝟙 _ := by simp

/-- The associator isomorphism which associates a binary biproduct. -/
@[simps]
/--
Definition of `biprod.associator` / `biprod.associator` 的定义

English:
definition biprod.associator
  signature: (P Q R : C)
  body: biprod.lift (biprod.fst ≫ biprod.fst) (biprod.lift (biprod.fst ≫ biprod.snd) biprod.snd)
  inv := biprod.lift (biprod.lift biprod.fst (biprod.snd ≫ biprod.fst)) (biprod.snd ≫ biprod.snd)

中文:
定义 biprod.associator
  签名: (P Q R : C)
  定义体: biprod.lift (biprod.fst ≫ biprod.fst) (biprod.lift (biprod.fst ≫ biprod.snd) biprod.snd)
  inv := biprod.lift (biprod.lift biprod.fst (biprod.snd ≫ biprod.fst)) (biprod.snd ≫ biprod.snd)

Depends on / 依赖: biprod, biprod.fst, biprod.lift, biprod.snd
-/
def biprod.associator (P Q R : C) : (P ⊞ Q) ⊞ R ≅ P ⊞ (Q ⊞ R) where
  hom := biprod.lift (biprod.fst ≫ biprod.fst) (biprod.lift (biprod.fst ≫ biprod.snd) biprod.snd)
  inv := biprod.lift (biprod.lift biprod.fst (biprod.snd ≫ biprod.fst)) (biprod.snd ≫ biprod.snd)

/-- The associator isomorphism can be passed through a map by swapping the order. -/
@[reassoc]
/--
theorem `biprod.associator_natural` / 定理 `biprod.associator_natural`

English:
theorem biprod.associator_natural
  given: {U V W X Y Z : C} (f : U ⟶ X) (g : V ⟶ Y) (h : W ⟶ Z)
  proof: by
  cat_disch

中文:
定理 biprod.associator_natural
  条件: {U V W X Y Z : C} (f : U ⟶ X) (g : V ⟶ Y) (h : W ⟶ Z)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
theorem biprod.associator_natural {U V W X Y Z : C} (f : U ⟶ X) (g : V ⟶ Y) (h : W ⟶ Z) :
    biprod.map (biprod.map f g) h ≫ (biprod.associator _ _ _).hom
      = (biprod.associator _ _ _).hom ≫ biprod.map f (biprod.map g h) := by
  cat_disch

/-- The associator isomorphism can be passed through a map by swapping the order. -/
@[reassoc]
/--
theorem `biprod.associator_inv_natural` / 定理 `biprod.associator_inv_natural`

English:
theorem biprod.associator_inv_natural
  given: {U V W X Y Z : C} (f : U ⟶ X) (g : V ⟶ Y) (h : W ⟶ Z)
  proof: by
  cat_disch

中文:
定理 biprod.associator_inv_natural
  条件: {U V W X Y Z : C} (f : U ⟶ X) (g : V ⟶ Y) (h : W ⟶ Z)
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
theorem biprod.associator_inv_natural {U V W X Y Z : C} (f : U ⟶ X) (g : V ⟶ Y) (h : W ⟶ Z) :
    biprod.map f (biprod.map g h) ≫ (biprod.associator _ _ _).inv
      = (biprod.associator _ _ _).inv ≫ biprod.map (biprod.map f g) h := by
  cat_disch

end

end Limits

open CategoryTheory.Limits

section

-- TODO:
-- If someone is interested, they could provide the constructions:
-- HasBinaryBiproducts ↔ HasFiniteBiproducts
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasBinaryBiproducts C]

/--
Definition of `Indecomposable` / `Indecomposable` 的定义

English:
definition Indecomposable
  signature: (X : C)
  body: ¬IsZero X ∧ forall Y Z, (X ≅ Y ⊞ Z) -> IsZero Y ∨ IsZero Z

中文:
定义 Indecomposable
  签名: (X : C)
  定义体: ¬IsZero X ∧ forall Y Z, (X ≅ Y ⊞ Z) -> IsZero Y ∨ IsZero Z

Depends on / 依赖: IsZero
-/
def Indecomposable (X : C) : Prop :=
  ¬IsZero X ∧ forall Y Z, (X ≅ Y ⊞ Z) -> IsZero Y ∨ IsZero Z

/--
theorem `isIso_left_of_isIso_biprod_map` / 定理 `isIso_left_of_isIso_biprod_map`

English:
theorem isIso_left_of_isIso_biprod_map
  statement: {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z)
  proof: ⟨⟨biprod.inl ≫ inv (biprod.map f g) ≫ biprod.fst,
      ⟨by
        have t := congrArg (fun p : W ⊞ X ⟶ W ⊞ X => biprod.inl ≫ p ≫ biprod.fst)
          (IsIso.hom_inv_id (biprod.map f g))
        simp only [Category.id_comp, Category.assoc, biprod.inl_map_assoc] at t
        simp [t], by
        have t := congrArg (fun p : Y ⊞ Z ⟶ Y ⊞ Z => biprod.inl ≫ p ≫ biprod.fst)
          (IsIso.inv_hom_id (biprod.map f g))
        simp only [Category.id_comp, Category.assoc, biprod.map_fst] at t
        simp only [Category.assoc]
        simp [t]⟩⟩⟩

中文:
定理 isIso_left_of_isIso_biprod_map
  结论: {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z)
  证明: ⟨⟨biprod.inl ≫ inv (biprod.map f g) ≫ biprod.fst,
      ⟨by
        have t := congrArg (fun p : W ⊞ X ⟶ W ⊞ X => biprod.inl ≫ p ≫ biprod.fst)
          (IsIso.hom_inv_id (biprod.map f g))
        simp only [Category.id_comp, Category.assoc, biprod.inl_map_assoc] at t
        simp [t], by
        have t := congrArg (fun p : Y ⊞ Z ⟶ Y ⊞ Z => biprod.inl ≫ p ≫ biprod.fst)
          (IsIso.inv_hom_id (biprod.map f g))
        simp only [Category.id_comp, Category.assoc, biprod.map_fst] at t
        simp only [Category.assoc]
        simp [t]⟩⟩⟩

Depends on / 依赖: Category, Category.assoc, Category.id_comp, IsIso.hom_inv_id, IsIso.inv_hom_id, biprod, biprod.fst, biprod.inl, biprod.inl_map_assoc, biprod.map, biprod.map_fst, hom_inv_id, id_comp, inl_map_assoc, inv_hom_id, map_fst
-/
theorem isIso_left_of_isIso_biprod_map {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z)
    [IsIso (biprod.map f g)] : IsIso f :=
  ⟨⟨biprod.inl ≫ inv (biprod.map f g) ≫ biprod.fst,
      ⟨by
        have t := congrArg (fun p : W ⊞ X ⟶ W ⊞ X => biprod.inl ≫ p ≫ biprod.fst)
          (IsIso.hom_inv_id (biprod.map f g))
        simp only [Category.id_comp, Category.assoc, biprod.inl_map_assoc] at t
        simp [t], by
        have t := congrArg (fun p : Y ⊞ Z ⟶ Y ⊞ Z => biprod.inl ≫ p ≫ biprod.fst)
          (IsIso.inv_hom_id (biprod.map f g))
        simp only [Category.id_comp, Category.assoc, biprod.map_fst] at t
        simp only [Category.assoc]
        simp [t]⟩⟩⟩

/--
theorem `isIso_right_of_isIso_biprod_map` / 定理 `isIso_right_of_isIso_biprod_map`

English:
theorem isIso_right_of_isIso_biprod_map
  statement: {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z)
  proof: letI : IsIso (biprod.map g f) := by
    rw [← biprod.braiding_map_braiding]
    infer_instance
  isIso_left_of_isIso_biprod_map g f

中文:
定理 isIso_right_of_isIso_biprod_map
  结论: {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z)
  证明: letI : IsIso (biprod.map g f) := by
    rw [← biprod.braiding_map_braiding]
    infer_instance
  isIso_left_of_isIso_biprod_map g f

Depends on / 依赖: biprod, biprod.braiding_map_braiding, biprod.map, braiding_map_braiding, infer_instance, isIso_left_of_isIso_biprod_map
-/
theorem isIso_right_of_isIso_biprod_map {W X Y Z : C} (f : W ⟶ Y) (g : X ⟶ Z)
    [IsIso (biprod.map f g)] : IsIso g :=
  letI : IsIso (biprod.map g f) := by
    rw [← biprod.braiding_map_braiding]
    infer_instance
  isIso_left_of_isIso_biprod_map g f

end

end CategoryTheory
