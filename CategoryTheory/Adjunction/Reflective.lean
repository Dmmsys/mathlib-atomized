/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.HomCongr

/-!
# Reflective functors

Basic properties of reflective functors, especially those relating to their essential image.

Note properties of reflective functors relating to limits and colimits are included in
`Mathlib/CategoryTheory/Monad/Limits.lean`.
-/

@[expose] public section


universe v₁ v₂ v₃ u₁ u₂ u₃

noncomputable section

namespace CategoryTheory

open Category Adjunction

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
variable [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]

/--
Definition of `Reflective` / `Reflective` 的定义

English:
class Reflective
  parameters: (R : D ⥤ C)
  extends: R.Full, R.Faithful
  axioms and operations (2):
    - L : C ⥤ D
    - adj : L ⊣ R

中文:
类 反射
  参数: (R : D ⥤ C)
  继承: R.满, R.忠实
  公理与运算 (2 个):
    - L : C ⥤ D
    - adj : L ⊣ R
-/
class Reflective (R : D ⥤ C) extends R.Full, R.Faithful where
  /-- a choice of a left adjoint to `R` -/
  L : C ⥤ D
  /-- `R` is a right adjoint -/
  adj : L ⊣ R

variable (i : D ⥤ C)

/--
Definition of `reflector` / `reflector` 的定义

English:
definition reflector
  signature: [Reflective i]
  body: Reflective.L (R := i)

中文:
定义 reflector
  签名: [反射 i]
  定义体: Reflective.L (R := i)

Depends on / 依赖: Reflective, Reflective.L
-/
def reflector [Reflective i] : C ⥤ D := Reflective.L (R := i)

/--
Definition of `reflectorAdjunction` / `reflectorAdjunction` 的定义

English:
definition reflectorAdjunction
  signature: [Reflective i]
  body: Reflective.adj

中文:
定义 reflectorAdjunction
  签名: [反射 i]
  定义体: Reflective.adj

Depends on / 依赖: Reflective, Reflective.adj
-/
def reflectorAdjunction [Reflective i] : reflector i ⊣ i := Reflective.adj

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Reflective
  signature: i] : i.IsRightAdjoint
  body: ⟨_, ⟨reflectorAdjunction i⟩⟩

中文:
实例 [反射
  签名: i] : i.是右伴随
  定义体: ⟨_, ⟨reflectorAdjunction i⟩⟩

Depends on / 依赖: reflectorAdjunction
-/
instance [Reflective i] : i.IsRightAdjoint := ⟨_, ⟨reflectorAdjunction i⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Reflective
  signature: i] : (reflector i).IsLeftAdjoint
  body: ⟨_, ⟨reflectorAdjunction i⟩⟩

中文:
实例 [反射
  签名: i] : (reflector i).是左伴随
  定义体: ⟨_, ⟨reflectorAdjunction i⟩⟩

Depends on / 依赖: reflectorAdjunction
-/
instance [Reflective i] : (reflector i).IsLeftAdjoint := ⟨_, ⟨reflectorAdjunction i⟩⟩

/--
Definition of `Functor.fullyFaithfulOfReflective` / `Functor.fullyFaithfulOfReflective` 的定义

English:
definition Functor.fullyFaithfulOfReflective
  signature: [Reflective i]
  body: (reflectorAdjunction i).fullyFaithfulROfIsIsoCounit

中文:
定义 函子.fullyFaithfulOfReflective
  签名: [反射 i]
  定义体: (reflectorAdjunction i).fullyFaithfulROfIsIsoCounit

Depends on / 依赖: fullyFaithfulROfIsIsoCounit, reflectorAdjunction
-/
def Functor.fullyFaithfulOfReflective [Reflective i] : i.FullyFaithful :=
  (reflectorAdjunction i).fullyFaithfulROfIsIsoCounit

-- TODO: This holds more generally for idempotent adjunctions, not just reflective adjunctions.
/--
theorem `unit_obj_eq_map_unit` / 定理 `unit_obj_eq_map_unit`

English:
theorem unit_obj_eq_map_unit
  given: [Reflective i] (X : C)
  proof: by
  rw [← cancel_mono (i.map ((reflectorAdjunction i).counit.app ((reflector i).obj X)))]; rw [← i.map_comp]
  simp

中文:
定理 unit_obj_eq_map_unit
  条件: [反射 i] (X : C)
  证明: by
  rw [← cancel_mono (i.map ((reflectorAdjunction i).counit.app ((reflector i).obj X)))]; rw [← i.map_comp]
  simp

Depends on / 依赖: cancel_mono, counit, counit.app, i.map, i.map_comp, map_comp, reflector, reflectorAdjunction
-/
theorem unit_obj_eq_map_unit [Reflective i] (X : C) :
    (reflectorAdjunction i).unit.app (i.obj ((reflector i).obj X)) =
      i.map ((reflector i).map ((reflectorAdjunction i).unit.app X)) := by
  rw [← cancel_mono (i.map ((reflectorAdjunction i).counit.app ((reflector i).obj X)))]; rw [← i.map_comp]
  simp

/--
When restricted to objects in `D` given by `i : D ⥤ C`, the unit is an isomorphism. In other words,
`η_iX` is an isomorphism for any `X` in `D`.
More generally this applies to objects essentially in the reflective subcategory, see
`Functor.essImage.unit_isIso`.
-/
example [Reflective i] {B : D} : IsIso ((reflectorAdjunction i).unit.app (i.obj B)) :=
  inferInstance

variable {i}

/--
theorem `Functor.essImage.unit_isIso` / 定理 `Functor.essImage.unit_isIso`

English:
theorem Functor.essImage.unit_isIso
  given: [Reflective i] {A : C} (h : i.essImage A)
  proof: by
  rwa [isIso_unit_app_iff_mem_essImage]

中文:
定理 函子.essImage.unit_isIso
  条件: [反射 i] {A : C} (h : i.essImage A)
  证明: by
  rwa [isIso_unit_app_iff_mem_essImage]

Depends on / 依赖: isIso_unit_app_iff_mem_essImage
-/
theorem Functor.essImage.unit_isIso [Reflective i] {A : C} (h : i.essImage A) :
    IsIso ((reflectorAdjunction i).unit.app A) := by
  rwa [isIso_unit_app_iff_mem_essImage]

/--
theorem `mem_essImage_of_unit_isSplitMono` / 定理 `mem_essImage_of_unit_isSplitMono`

English:
theorem mem_essImage_of_unit_isSplitMono
  statement: [Reflective i] {A : C}
  proof: by
  let η : 𝟭 C ⟶ reflector i ⋙ i := (reflectorAdjunction i).unit
  have : IsIso (η.app (i.obj ((reflector i).obj A))) :=
    Functor.essImage.unit_isIso ((i.obj_mem_essImage _))
  have : Epi (η.app A) := by
    refine @epi_of_epi _ _ _ _ _ (retraction (η.app A)) (η.app A) ?_
    rw [show retraction _ ≫ η.app A = _ from η.naturality (retraction (η.app A))]
    apply epi_comp (η.app (i.obj ((reflector i).obj A)))
  have := isIso_of_epi_of_isSplitMono (η.app A)
  exact (reflectorAdjunction i).mem_essImage_of_unit_isIso A

中文:
定理 mem_essImage_of_unit_isSplitMono
  结论: [反射 i] {A : C}
  证明: by
  let η : 𝟭 C ⟶ reflector i ⋙ i := (reflectorAdjunction i).unit
  have : IsIso (η.app (i.obj ((reflector i).obj A))) :=
    Functor.essImage.unit_isIso ((i.obj_mem_essImage _))
  have : Epi (η.app A) := by
    refine @epi_of_epi _ _ _ _ _ (retraction (η.app A)) (η.app A) ?_
    rw [show retraction _ ≫ η.app A = _ from η.naturality (retraction (η.app A))]
    apply epi_comp (η.app (i.obj ((reflector i).obj A)))
  have := isIso_of_epi_of_isSplitMono (η.app A)
  exact (reflectorAdjunction i).mem_essImage_of_unit_isIso A

Depends on / 依赖: Functor, Functor.essImage.unit_isIso, epi_comp, epi_of_epi, essImage, i.obj, i.obj_mem_essImage, isIso_of_epi_of_isSplitMono, mem_essImage_of_unit_isIso, naturality, obj_mem_essImage, reflector, reflectorAdjunction, retraction, unit_isIso
-/
theorem mem_essImage_of_unit_isSplitMono [Reflective i] {A : C}
    [IsSplitMono ((reflectorAdjunction i).unit.app A)] : i.essImage A := by
  let η : 𝟭 C ⟶ reflector i ⋙ i := (reflectorAdjunction i).unit
  have : IsIso (η.app (i.obj ((reflector i).obj A))) :=
    Functor.essImage.unit_isIso ((i.obj_mem_essImage _))
  have : Epi (η.app A) := by
    refine @epi_of_epi _ _ _ _ _ (retraction (η.app A)) (η.app A) ?_
    rw [show retraction _ ≫ η.app A = _ from η.naturality (retraction (η.app A))]
    apply epi_comp (η.app (i.obj ((reflector i).obj A)))
  have := isIso_of_epi_of_isSplitMono (η.app A)
  exact (reflectorAdjunction i).mem_essImage_of_unit_isIso A

/--
Instance `Reflective.comp` / 实例 `Reflective.comp`

English:
instance Reflective.comp
  signature: (F : C ⥤ D) (G : D ⥤ E) [Reflective F] [Reflective G]
  body: reflector G ⋙ reflector F
  adj := (reflectorAdjunction G).comp (reflectorAdjunction F)

中文:
实例 反射.comp
  签名: (F : C ⥤ D) (G : D ⥤ E) [反射 F] [反射 G]
  定义体: reflector G ⋙ reflector F
  adj := (reflectorAdjunction G).comp (reflectorAdjunction F)

Depends on / 依赖: reflector
-/
instance Reflective.comp (F : C ⥤ D) (G : D ⥤ E) [Reflective F] [Reflective G] :
    Reflective (F ⋙ G) where
  L := reflector G ⋙ reflector F
  adj := (reflectorAdjunction G).comp (reflectorAdjunction F)

/--
Definition of `unitCompPartialBijectiveAux` / `unitCompPartialBijectiveAux` 的定义

English:
definition unitCompPartialBijectiveAux
  signature: [Reflective i] (A : C) (B : D)
  body: ((reflectorAdjunction i).homEquiv _ _).symm.trans
    (Functor.FullyFaithful.ofFullyFaithful i).homEquiv

中文:
定义 unitCompPartialBijectiveAux
  签名: [反射 i] (A : C) (B : D)
  定义体: ((reflectorAdjunction i).homEquiv _ _).symm.trans
    (Functor.FullyFaithful.ofFullyFaithful i).homEquiv

Depends on / 依赖: FullyFaithful, Functor, Functor.FullyFaithful.ofFullyFaithful, homEquiv, ofFullyFaithful, reflectorAdjunction, symm.trans
-/
def unitCompPartialBijectiveAux [Reflective i] (A : C) (B : D) :
    (A ⟶ i.obj B) ≃ (i.obj ((reflector i).obj A) ⟶ i.obj B) :=
  ((reflectorAdjunction i).homEquiv _ _).symm.trans
    (Functor.FullyFaithful.ofFullyFaithful i).homEquiv

/--
theorem `unitCompPartialBijectiveAux_symm_apply` / 定理 `unitCompPartialBijectiveAux_symm_apply`

English:
theorem unitCompPartialBijectiveAux_symm_apply
  statement: [Reflective i] {A : C} {B : D}
  proof: by
  simp [unitCompPartialBijectiveAux, Adjunction.homEquiv_unit]

中文:
定理 unitCompPartialBijectiveAux_symm_apply
  结论: [反射 i] {A : C} {B : D}
  证明: by
  simp [unitCompPartialBijectiveAux, Adjunction.homEquiv_unit]

Depends on / 依赖: Adjunction, Adjunction.homEquiv_unit, homEquiv_unit, unitCompPartialBijectiveAux
-/
theorem unitCompPartialBijectiveAux_symm_apply [Reflective i] {A : C} {B : D}
    (f : i.obj ((reflector i).obj A) ⟶ i.obj B) :
    (unitCompPartialBijectiveAux _ _).symm f = (reflectorAdjunction i).unit.app A ≫ f := by
  simp [unitCompPartialBijectiveAux, Adjunction.homEquiv_unit]

/--
Definition of `unitCompPartialBijective` / `unitCompPartialBijective` 的定义

English:
definition unitCompPartialBijective
  signature: [Reflective i] (A : C) {B : C} (hB : i.essImage B)
  body: calc
    (A ⟶ B) ≃ (A ⟶ i.obj (Functor.essImage.witness hB)) := Iso.homCongr (Iso.refl _) hB.getIso.symm
    _ ≃ (i.obj _ ⟶ i.obj (Functor.essImage.witness hB)) := unitCompPartialBijectiveAux _ _
    _ ≃ (i.obj ((reflector i).obj A) ⟶ B) :=
      Iso.homCongr (Iso.refl _) (Functor.essImage.getIso hB)

中文:
定义 unitCompPartialBijective
  签名: [反射 i] (A : C) {B : C} (hB : i.essImage B)
  定义体: calc
    (A ⟶ B) ≃ (A ⟶ i.obj (Functor.essImage.witness hB)) := Iso.homCongr (Iso.refl _) hB.getIso.symm
    _ ≃ (i.obj _ ⟶ i.obj (Functor.essImage.witness hB)) := unitCompPartialBijectiveAux _ _
    _ ≃ (i.obj ((reflector i).obj A) ⟶ B) :=
      Iso.homCongr (Iso.refl _) (Functor.essImage.getIso hB)

Depends on / 依赖: Functor, Functor.essImage.getIso, Functor.essImage.witness, Iso.homCongr, Iso.refl, essImage, getIso, hB.getIso.symm, homCongr, i.obj, reflector, unitCompPartialBijectiveAux, witness
-/
def unitCompPartialBijective [Reflective i] (A : C) {B : C} (hB : i.essImage B) :
    (A ⟶ B) ≃ (i.obj ((reflector i).obj A) ⟶ B) :=
  calc
    (A ⟶ B) ≃ (A ⟶ i.obj (Functor.essImage.witness hB)) := Iso.homCongr (Iso.refl _) hB.getIso.symm
    _ ≃ (i.obj _ ⟶ i.obj (Functor.essImage.witness hB)) := unitCompPartialBijectiveAux _ _
    _ ≃ (i.obj ((reflector i).obj A) ⟶ B) :=
      Iso.homCongr (Iso.refl _) (Functor.essImage.getIso hB)

set_option backward.defeqAttrib.useBackward true in
@[simp]
/--
theorem `unitCompPartialBijective_symm_apply` / 定理 `unitCompPartialBijective_symm_apply`

English:
theorem unitCompPartialBijective_symm_apply
  statement: [Reflective i] (A : C) {B : C} (hB : i.essImage B)
  proof: by
  simp [unitCompPartialBijective, unitCompPartialBijectiveAux_symm_apply]

中文:
定理 unitCompPartialBijective_symm_apply
  结论: [反射 i] (A : C) {B : C} (hB : i.essImage B)
  证明: by
  simp [unitCompPartialBijective, unitCompPartialBijectiveAux_symm_apply]

Depends on / 依赖: unitCompPartialBijective, unitCompPartialBijectiveAux_symm_apply
-/
theorem unitCompPartialBijective_symm_apply [Reflective i] (A : C) {B : C} (hB : i.essImage B)
    (f) : (unitCompPartialBijective A hB).symm f = (reflectorAdjunction i).unit.app A ≫ f := by
  simp [unitCompPartialBijective, unitCompPartialBijectiveAux_symm_apply]

set_option backward.defeqAttrib.useBackward true in
/--
theorem `unitCompPartialBijective_symm_natural` / 定理 `unitCompPartialBijective_symm_natural`

English:
theorem unitCompPartialBijective_symm_natural
  statement: [Reflective i] (A : C) {B B' : C} (h : B ⟶ B')
  proof: by
  simp

中文:
定理 unitCompPartialBijective_symm_natural
  结论: [反射 i] (A : C) {B B' : C} (h : B ⟶ B')
  证明: by
  simp
-/
theorem unitCompPartialBijective_symm_natural [Reflective i] (A : C) {B B' : C} (h : B ⟶ B')
    (hB : i.essImage B) (hB' : i.essImage B') (f : i.obj ((reflector i).obj A) ⟶ B) :
    (unitCompPartialBijective A hB').symm (f ≫ h) = (unitCompPartialBijective A hB).symm f ≫ h := by
  simp

/--
theorem `unitCompPartialBijective_natural` / 定理 `unitCompPartialBijective_natural`

English:
theorem unitCompPartialBijective_natural
  statement: [Reflective i] (A : C) {B B' : C} (h : B ⟶ B')
  proof: by
  rw [← Equiv.eq_symm_apply]; rw [unitCompPartialBijective_symm_natural A h hB]; rw [Equiv.symm_apply_apply]

中文:
定理 unitCompPartialBijective_natural
  结论: [反射 i] (A : C) {B B' : C} (h : B ⟶ B')
  证明: by
  rw [← Equiv.eq_symm_apply]; rw [unitCompPartialBijective_symm_natural A h hB]; rw [Equiv.symm_apply_apply]

Depends on / 依赖: Equiv.eq_symm_apply, Equiv.symm_apply_apply, eq_symm_apply, symm_apply_apply, unitCompPartialBijective_symm_natural
-/
theorem unitCompPartialBijective_natural [Reflective i] (A : C) {B B' : C} (h : B ⟶ B')
    (hB : i.essImage B) (hB' : i.essImage B') (f : A ⟶ B) :
    (unitCompPartialBijective A hB') (f ≫ h) = unitCompPartialBijective A hB f ≫ h := by
  rw [← Equiv.eq_symm_apply]; rw [unitCompPartialBijective_symm_natural A h hB]; rw [Equiv.symm_apply_apply]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Reflective
  signature: i] (X
  body: Functor.essImage.unit_isIso X.property

中文:
实例 [反射
  签名: i] (X
  定义体: Functor.essImage.unit_isIso X.property

Depends on / 依赖: Functor, Functor.essImage.unit_isIso, X.property, essImage, property, unit_isIso
-/
instance [Reflective i] (X : Functor.EssImageSubcategory i) :
    IsIso (NatTrans.app (reflectorAdjunction i).unit X.obj) :=
  Functor.essImage.unit_isIso X.property

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
-- These attributes are necessary to make automation work in `equivEssImageOfReflective`.
-- Making them global doesn't break anything elsewhere, but this is enough for now.
-- TODO: investigate further.
attribute [local simp 900] ObjectProperty.ι_map in
attribute [local ext] Functor.essImage_ext in
/-- If `i : D ⥤ C` is reflective, the inverse functor of `i ≌ F.essImage` can be explicitly
defined by the reflector. -/
@[simps]
/--
Definition of `equivEssImageOfReflective` / `equivEssImageOfReflective` 的定义

English:
definition equivEssImageOfReflective
  signature: [Reflective i]
  body: i.toEssImage
  inverse := i.essImage.ι ⋙ reflector i
  unitIso := (asIso <| (reflectorAdjunction i).counit).symm
counitIso := Functor.fullyFaithfulCancelRight i.essImage.ι
    NatIso.ofComponents (fun X => (asIso ((reflectorAdjunction i).unit.app X.obj)).symm)

中文:
定义 equivEssImageOfReflective
  签名: [反射 i]
  定义体: i.toEssImage
  inverse := i.essImage.ι ⋙ reflector i
  unitIso := (asIso <| (reflectorAdjunction i).counit).symm
counitIso := Functor.fullyFaithfulCancelRight i.essImage.ι
    NatIso.ofComponents (fun X => (asIso ((reflectorAdjunction i).unit.app X.obj)).symm)

Depends on / 依赖: i.toEssImage, toEssImage
-/
def equivEssImageOfReflective [Reflective i] : D ≌ i.EssImageSubcategory where
  functor := i.toEssImage
  inverse := i.essImage.ι ⋙ reflector i
  unitIso := (asIso <| (reflectorAdjunction i).counit).symm
counitIso := Functor.fullyFaithfulCancelRight i.essImage.ι
    NatIso.ofComponents (fun X => (asIso ((reflectorAdjunction i).unit.app X.obj)).symm)

/--
Definition of `Coreflective` / `Coreflective` 的定义

English:
class Coreflective
  parameters: (L : C ⥤ D)
  extends: L.Full, L.Faithful
  axioms and operations (2):
    - R : D ⥤ C
    - adj : L ⊣ R

中文:
类 余反射
  参数: (L : C ⥤ D)
  继承: L.满, L.忠实
  公理与运算 (2 个):
    - R : D ⥤ C
    - adj : L ⊣ R
-/
class Coreflective (L : C ⥤ D) extends L.Full, L.Faithful where
  /-- a choice of a right adjoint to `L` -/
  R : D ⥤ C
  /-- `L` is a left adjoint -/
  adj : L ⊣ R

variable (j : C ⥤ D)

/--
Definition of `coreflector` / `coreflector` 的定义

English:
definition coreflector
  signature: [Coreflective j]
  body: Coreflective.R (L := j)

中文:
定义 coreflector
  签名: [余反射 j]
  定义体: Coreflective.R (L := j)

Depends on / 依赖: Coreflective, Coreflective.R
-/
def coreflector [Coreflective j] : D ⥤ C := Coreflective.R (L := j)

/--
Definition of `coreflectorAdjunction` / `coreflectorAdjunction` 的定义

English:
definition coreflectorAdjunction
  signature: [Coreflective j]
  body: Coreflective.adj

中文:
定义 coreflectorAdjunction
  签名: [余反射 j]
  定义体: Coreflective.adj

Depends on / 依赖: Coreflective, Coreflective.adj
-/
def coreflectorAdjunction [Coreflective j] : j ⊣ coreflector j := Coreflective.adj

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Coreflective
  signature: j] : j.IsLeftAdjoint
  body: ⟨_, ⟨coreflectorAdjunction j⟩⟩

中文:
实例 [余反射
  签名: j] : j.是左伴随
  定义体: ⟨_, ⟨coreflectorAdjunction j⟩⟩

Depends on / 依赖: coreflectorAdjunction
-/
instance [Coreflective j] : j.IsLeftAdjoint := ⟨_, ⟨coreflectorAdjunction j⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Coreflective
  signature: j] : (coreflector j).IsRightAdjoint
  body: ⟨_, ⟨coreflectorAdjunction j⟩⟩

中文:
实例 [余反射
  签名: j] : (coreflector j).是右伴随
  定义体: ⟨_, ⟨coreflectorAdjunction j⟩⟩

Depends on / 依赖: coreflectorAdjunction
-/
instance [Coreflective j] : (coreflector j).IsRightAdjoint := ⟨_, ⟨coreflectorAdjunction j⟩⟩

/--
Definition of `Functor.fullyFaithfulOfCoreflective` / `Functor.fullyFaithfulOfCoreflective` 的定义

English:
definition Functor.fullyFaithfulOfCoreflective
  signature: [Coreflective j]
  body: (coreflectorAdjunction j).fullyFaithfulLOfIsIsoUnit

中文:
定义 函子.fullyFaithfulOfCoreflective
  签名: [余反射 j]
  定义体: (coreflectorAdjunction j).fullyFaithfulLOfIsIsoUnit

Depends on / 依赖: coreflectorAdjunction, fullyFaithfulLOfIsIsoUnit
-/
def Functor.fullyFaithfulOfCoreflective [Coreflective j] : j.FullyFaithful :=
  (coreflectorAdjunction j).fullyFaithfulLOfIsIsoUnit

/--
lemma `counit_obj_eq_map_counit` / 引理 `counit_obj_eq_map_counit`

English:
lemma counit_obj_eq_map_counit
  given: [Coreflective j] (X : D)
  proof: by
  rw [← cancel_epi (j.map ((coreflectorAdjunction j).unit.app ((coreflector j).obj X)))]; rw [← j.map_comp]
  simp

example [Coreflective j] {B : C} : IsIso ((coreflectorAdjunction j).counit.app (j.obj B)) :=
  inferInstance

中文:
引理 counit_obj_eq_map_counit
  条件: [余反射 j] (X : D)
  证明: by
  rw [← cancel_epi (j.map ((coreflectorAdjunction j).unit.app ((coreflector j).obj X)))]; rw [← j.map_comp]
  simp

example [Coreflective j] {B : C} : IsIso ((coreflectorAdjunction j).counit.app (j.obj B)) :=
  inferInstance

Depends on / 依赖: cancel_epi, coreflector, coreflectorAdjunction, j.map, j.map_comp, map_comp, unit.app
-/
lemma counit_obj_eq_map_counit [Coreflective j] (X : D) :
    (coreflectorAdjunction j).counit.app (j.obj ((coreflector j).obj X)) =
      j.map ((coreflector j).map ((coreflectorAdjunction j).counit.app X)) := by
  rw [← cancel_epi (j.map ((coreflectorAdjunction j).unit.app ((coreflector j).obj X)))]; rw [← j.map_comp]
  simp

example [Coreflective j] {B : C} : IsIso ((coreflectorAdjunction j).counit.app (j.obj B)) :=
  inferInstance

variable {j}

/--
lemma `Functor.essImage.counit_isIso` / 引理 `Functor.essImage.counit_isIso`

English:
lemma Functor.essImage.counit_isIso
  given: [Coreflective j] {A : D} (h : j.essImage A)
  proof: by
  rwa [isIso_counit_app_iff_mem_essImage]

中文:
引理 函子.essImage.counit_isIso
  条件: [余反射 j] {A : D} (h : j.essImage A)
  证明: by
  rwa [isIso_counit_app_iff_mem_essImage]

Depends on / 依赖: isIso_counit_app_iff_mem_essImage
-/
lemma Functor.essImage.counit_isIso [Coreflective j] {A : D} (h : j.essImage A) :
    IsIso ((coreflectorAdjunction j).counit.app A) := by
  rwa [isIso_counit_app_iff_mem_essImage]

/--
lemma `mem_essImage_of_counit_isSplitEpi` / 引理 `mem_essImage_of_counit_isSplitEpi`

English:
lemma mem_essImage_of_counit_isSplitEpi
  statement: [Coreflective j] {A : D}
  proof: by
  let ε : coreflector j ⋙ j ⟶ 𝟭 D := (coreflectorAdjunction j).counit
  have : IsIso (ε.app (j.obj ((coreflector j).obj A))) :=
    Functor.essImage.counit_isIso ((j.obj_mem_essImage _))
  have : Mono (ε.app A) := by
    refine @mono_of_mono _ _ _ _ _ (ε.app A) (section_ (ε.app A)) ?_
    rw [show ε.app A ≫ section_ _ = _ from (ε.naturality (section_ (ε.app A))).symm]
    apply mono_comp _ (ε.app (j.obj ((coreflector j).obj A)))
  have := isIso_of_mono_of_isSplitEpi (ε.app A)
  exact (coreflectorAdjunction j).mem_essImage_of_counit_isIso A

中文:
引理 mem_essImage_of_counit_isSplitEpi
  结论: [余反射 j] {A : D}
  证明: by
  let ε : coreflector j ⋙ j ⟶ 𝟭 D := (coreflectorAdjunction j).counit
  have : IsIso (ε.app (j.obj ((coreflector j).obj A))) :=
    Functor.essImage.counit_isIso ((j.obj_mem_essImage _))
  have : Mono (ε.app A) := by
    refine @mono_of_mono _ _ _ _ _ (ε.app A) (section_ (ε.app A)) ?_
    rw [show ε.app A ≫ section_ _ = _ from (ε.naturality (section_ (ε.app A))).symm]
    apply mono_comp _ (ε.app (j.obj ((coreflector j).obj A)))
  have := isIso_of_mono_of_isSplitEpi (ε.app A)
  exact (coreflectorAdjunction j).mem_essImage_of_counit_isIso A

Depends on / 依赖: Functor, Functor.essImage.counit_isIso, coreflector, coreflectorAdjunction, counit, counit_isIso, essImage, isIso_of_mono_of_isSplitEpi, j.obj, j.obj_mem_essImage, mem_essI, mono_comp, mono_of_mono, naturality, obj_mem_essImage, section_
-/
lemma mem_essImage_of_counit_isSplitEpi [Coreflective j] {A : D}
    [IsSplitEpi ((coreflectorAdjunction j).counit.app A)] : j.essImage A := by
  let ε : coreflector j ⋙ j ⟶ 𝟭 D := (coreflectorAdjunction j).counit
  have : IsIso (ε.app (j.obj ((coreflector j).obj A))) :=
    Functor.essImage.counit_isIso ((j.obj_mem_essImage _))
  have : Mono (ε.app A) := by
    refine @mono_of_mono _ _ _ _ _ (ε.app A) (section_ (ε.app A)) ?_
    rw [show ε.app A ≫ section_ _ = _ from (ε.naturality (section_ (ε.app A))).symm]
    apply mono_comp _ (ε.app (j.obj ((coreflector j).obj A)))
  have := isIso_of_mono_of_isSplitEpi (ε.app A)
  exact (coreflectorAdjunction j).mem_essImage_of_counit_isIso A

/--
Instance `Coreflective.comp` / 实例 `Coreflective.comp`

English:
instance Coreflective.comp
  signature: (F : C ⥤ D) (G : D ⥤ E) [Coreflective F] [Coreflective G]
  body: coreflector G ⋙ coreflector F
  adj := (coreflectorAdjunction F).comp (coreflectorAdjunction G)

中文:
实例 余反射.comp
  签名: (F : C ⥤ D) (G : D ⥤ E) [余反射 F] [余反射 G]
  定义体: coreflector G ⋙ coreflector F
  adj := (coreflectorAdjunction F).comp (coreflectorAdjunction G)

Depends on / 依赖: coreflector
-/
instance Coreflective.comp (F : C ⥤ D) (G : D ⥤ E) [Coreflective F] [Coreflective G] :
    Coreflective (F ⋙ G) where
  R := coreflector G ⋙ coreflector F
  adj := (coreflectorAdjunction F).comp (coreflectorAdjunction G)

end CategoryTheory
