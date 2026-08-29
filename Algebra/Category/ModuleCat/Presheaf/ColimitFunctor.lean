/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Filtered.FinallySmall
public import Mathlib.CategoryTheory.Monoidal.Limits.Colimits

/-!
# The colimit module of a presheaf of modules on a cofiltered category

Given a colimit cocone `cR` for a presheaf of rings `R` on a cofiltered category `C`,
`M` a presheaf of modules over `R`, and a colimit cocone `cM` for the underlying
functor `Cᵒᵖ ⥤ AddCommGrpCat` of `M`, we define a structure of module over `cR.pt`
on a type-synonym `PresheafOfModules.ModuleColimit` for `cM.pt`. This extends to
a functor `PresheafOfModules.colimitFunctor : PresheafOfModules R ⥤ ModuleCat cR.pt`.

## TODO (@joelriou)
* Define fiber functors on categories of (pre)sheaves of modules
* Refactor `Mathlib/Algebra/Category/ModuleCat/Stalk.lean` so that it uses
this slightly more general construction.

-/

@[expose] public section

universe w v u

open CategoryTheory Limits MonoidalCategory

attribute [local instance] hasColimitsOfShape_of_finallySmall
  IsFiltered.isSifted FinallySmall.preservesColimitsOfShape_of_isFiltered

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
  [IsCofiltered C] [InitiallySmall.{w} C]
  {R : Cᵒᵖ ⥤ RingCat.{w}} {cR : Cocone R} (hcR : IsColimit cR)

set_option backward.defeqAttrib.useBackward true in
variable (cR) in
/--
Definition of `constFunctor` / `constFunctor` 的定义

English:
definition constFunctor
  signature: : ModuleCat cR.pt ⥤ PresheafOfModules.{w} R where
  body: { obj X := (ModuleCat.restrictScalars (cR.ι.app X).hom).obj M
      map {X Y} f :=
        (ModuleCat.restrictScalarsComp' _ _ _
          (by ext; dsimp; rw [← Cocone.w cR f]; dsimp)).hom.app _ }
  map φ := { app X := (ModuleCat.restrictScalars (cR.ι.app X).hom).map φ }

中文:
定义 constFunctor
  签名: : 模范畴 cR.pt ⥤ 预模层.{w} R where
  定义体: { obj X := (ModuleCat.restrictScalars (cR.ι.app X).hom).obj M
      map {X Y} f :=
        (ModuleCat.restrictScalarsComp' _ _ _
          (by ext; dsimp; rw [← Cocone.w cR f]; dsimp)).hom.app _ }
  map φ := { app X := (ModuleCat.restrictScalars (cR.ι.app X).hom).map φ }

Depends on / 依赖: Cocone, Cocone.w, ModuleCat, ModuleCat.restrictScalars, ModuleCat.restrictScalarsComp, hom.app, restrictScalars, restrictScalarsComp
-/
noncomputable def constFunctor : ModuleCat cR.pt ⥤ PresheafOfModules.{w} R where
  obj M :=
    { obj X := (ModuleCat.restrictScalars (cR.ι.app X).hom).obj M
      map {X Y} f :=
        (ModuleCat.restrictScalarsComp' _ _ _
          (by ext; dsimp; rw [← Cocone.w cR f]; dsimp)).hom.app _ }
  map φ := { app X := (ModuleCat.restrictScalars (cR.ι.app X).hom).map φ }

section

variable {M : PresheafOfModules.{w} R} {cM : Cocone M.presheaf} (hcM : IsColimit cM)
  {M' : PresheafOfModules.{w} R} {cM' : Cocone M'.presheaf} (hcM' : IsColimit cM')
  {M'' : PresheafOfModules.{w} R} {cM'' : Cocone M''.presheaf} (hcM'' : IsColimit cM'')

/-- Given a colimit cocone for a presheaf of rings `R` on a cofiltered category `C`,
`M` a presheaf of modules over `R`, and a colimit cocone `cM` for the underlying
functor `Cᵒᵖ ⥤ AddCommGrpCat` of `M`, this is the type `cM.pt` on which we define
a module structure below. -/
@[nolint unusedArguments]
/--
Definition of `ModuleColimit` / `ModuleColimit` 的定义

English:
definition ModuleColimit
  signature: (_ : IsColimit cR) (_ : IsColimit cM)
  body: cM.pt

中文:
定义 ModuleColimit
  签名: (_ : 是余极限 cR) (_ : 是余极限 cM)
  定义体: cM.pt

Depends on / 依赖: cM.pt
-/
def ModuleColimit (_ : IsColimit cR) (_ : IsColimit cM) : Type w := cM.pt

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup (ModuleColimit hcR hcM)
  body: inferInstanceAs (AddCommGroup cM.pt)

中文:
实例 :
  签名: 加法交换群 (ModuleColimit hcR hcM)
  定义体: inferInstanceAs (AddCommGroup cM.pt)

Depends on / 依赖: AddCommGroup, cM.pt
-/
instance : AddCommGroup (ModuleColimit hcR hcM) :=
  inferInstanceAs (AddCommGroup cM.pt)

namespace ModuleColimit

/-- The cocone for `R ⋙ forget _ ⊗ M.presheaf ⋙ forget _` with point
`ModuleColimit hcR hcM` which allows to define the scalar multiplication
by `cR.pt` on `ModuleColimit hcR hcM`. -/
@[simps]
/--
Definition of `coconeSMul` / `coconeSMul` 的定义

English:
definition coconeSMul
  signature: :
  body: ModuleColimit hcR hcM
  ι.app U := ↾fun ⟨(r : R.obj U), (m : M.obj U)⟩ => by exact cM.ι.app U (r • m)
  ι.naturality V U f := by
    ext ⟨r, m⟩
    exact (ConcreteCategory.congr_arg (cM.ι.app U)
      (M.map_smul f r m).symm).trans (ConcreteCategory.congr_hom (cM.w f) _)

中文:
定义 coconeSMul
  签名: :
  定义体: ModuleColimit hcR hcM
  ι.app U := ↾fun ⟨(r : R.obj U), (m : M.obj U)⟩ => by exact cM.ι.app U (r • m)
  ι.naturality V U f := by
    ext ⟨r, m⟩
    exact (ConcreteCategory.congr_arg (cM.ι.app U)
      (M.map_smul f r m).symm).trans (ConcreteCategory.congr_hom (cM.w f) _)

Depends on / 依赖: ModuleColimit
-/
noncomputable def coconeSMul :
    Cocone (R ⋙ forget _ otimes M.presheaf ⋙ forget _) where
  pt := ModuleColimit hcR hcM
  ι.app U := ↾fun ⟨(r : R.obj U), (m : M.obj U)⟩ => by exact cM.ι.app U (r • m)
  ι.naturality V U f := by
    ext ⟨r, m⟩
    exact (ConcreteCategory.congr_arg (cM.ι.app U)
      (M.map_smul f r m).symm).trans (ConcreteCategory.congr_hom (cM.w f) _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul cR.pt (ModuleColimit hcR hcM)
  body: (((isColimitOfPreserves (forget _) hcR).tensor
      (isColimitOfPreserves (forget _) hcM)).desc (coconeSMul hcR hcM) : _ -> _).curry

中文:
实例 :
  签名: 标量乘法 cR.pt (ModuleColimit hcR hcM)
  定义体: (((isColimitOfPreserves (forget _) hcR).tensor
      (isColimitOfPreserves (forget _) hcM)).desc (coconeSMul hcR hcM) : _ -> _).curry

Depends on / 依赖: coconeSMul, forget, isColimitOfPreserves, tensor
-/
noncomputable instance : SMul cR.pt (ModuleColimit hcR hcM) where
  smul :=
    (((isColimitOfPreserves (forget _) hcR).tensor
      (isColimitOfPreserves (forget _) hcM)).desc (coconeSMul hcR hcM) : _ -> _).curry

variable (cR) in
/--
Definition of `ιR` / `ιR` 的定义

English:
abbreviation ιR
  signature: {U : Cᵒᵖ}
  body: (cR.ι.app U).hom

中文:
缩写 ιR
  签名: {U : Cᵒᵖ}
  定义体: (cR.ι.app U).hom
-/
abbrev ιR {U : Cᵒᵖ} : R.obj U ->+* cR.pt := (cR.ι.app U).hom

variable {hcR hcM} in
/--
Definition of `ιM` / `ιM` 的定义

English:
abbreviation ιM
  signature: {U : Cᵒᵖ}
  body: (cM.ι.app U).hom

@[simp]

中文:
缩写 ιM
  签名: {U : Cᵒᵖ}
  定义体: (cM.ι.app U).hom

@[simp]
-/
noncomputable abbrev ιM {U : Cᵒᵖ} : M.obj U ->+ ModuleColimit hcR hcM :=
  (cM.ι.app U).hom

@[simp]
/--
lemma `smul_eq` / 引理 `smul_eq`

English:
lemma smul_eq
  given: {U : Cᵒᵖ} (r : R.obj U) (m : M.obj U)
  proof: ConcreteCategory.congr_hom (((isColimitOfPreserves (forget _) hcR).tensor
    (isColimitOfPreserves (forget _) hcM)).fac (coconeSMul hcR hcM) U) ⟨r, m⟩

中文:
引理 smul_eq
  条件: {U : Cᵒᵖ} (r : R.obj U) (m : M.obj U)
  证明: ConcreteCategory.congr_hom (((isColimitOfPreserves (forget _) hcR).tensor
    (isColimitOfPreserves (forget _) hcM)).fac (coconeSMul hcR hcM) U) ⟨r, m⟩

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom, HopfAlgCat
-/
lemma smul_eq {U : Cᵒᵖ} (r : R.obj U) (m : M.obj U) :
    ιR cR r • ιM (hcR := hcR) (hcM := hcM) m = ιM (r • m) :=
  ConcreteCategory.congr_hom (((isColimitOfPreserves (forget _) hcR).tensor
    (isColimitOfPreserves (forget _) hcM)).fac (coconeSMul hcR hcM) U) ⟨r, m⟩

variable {hcR hcM} in
/--
lemma `ιM_jointly_surjective` / 引理 `ιM_jointly_surjective`

English:
lemma ιM_jointly_surjective
  given: (m : ModuleColimit hcR hcM)
  proof: Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget AddCommGrpCat) hcM) m

中文:
引理 ιM_jointly_surjective
  条件: (m : ModuleColimit hcR hcM)
  证明: Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget AddCommGrpCat) hcM) m

Depends on / 依赖: AddCommGrpCat, Types.jointly_surjective_of_isColimit, forget, isColimitOfPreserves, jointly_surjective_of_isColimit
-/
lemma ιM_jointly_surjective (m : ModuleColimit hcR hcM) :
    exists (U : Cᵒᵖ) (x : M.obj U), ιM x = m :=
  Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget AddCommGrpCat) hcM) m

set_option backward.isDefEq.respectTransparency false in
variable {hcR hcM hcM'} in
/--
lemma `ιM_jointly_surjective₂` / 引理 `ιM_jointly_surjective₂`

English:
lemma ιM_jointly_surjective₂
  given: (m : ModuleColimit hcR hcM) (m' : ModuleColimit hcR hcM')
  proof: by
  obtain ⟨U, ⟨x, x'⟩, h⟩ := Types.jointly_surjective_of_isColimit
    ((isColimitOfPreserves (forget AddCommGrpCat) hcM).tensor
      (isColimitOfPreserves (forget AddCommGrpCat) hcM')) ⟨m, m'⟩
  rw [Prod.ext_iff] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨U, x, x', rfl, rfl⟩

中文:
引理 ιM_jointly_surjective₂
  条件: (m : ModuleColimit hcR hcM) (m' : ModuleColimit hcR hcM')
  证明: by
  obtain ⟨U, ⟨x, x'⟩, h⟩ := Types.jointly_surjective_of_isColimit
    ((isColimitOfPreserves (forget AddCommGrpCat) hcM).tensor
      (isColimitOfPreserves (forget AddCommGrpCat) hcM')) ⟨m, m'⟩
  rw [Prod.ext_iff] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨U, x, x', rfl, rfl⟩

Depends on / 依赖: AddCommGrpCat, Prod.ext_iff, Types.jointly_surjective_of_isColimit, ext_iff, forget, isColimitOfPreserves, jointly_surjective_of_isColimit, tensor
-/
lemma ιM_jointly_surjective₂ (m : ModuleColimit hcR hcM) (m' : ModuleColimit hcR hcM') :
    exists (U : Cᵒᵖ) (x : M.obj U) (x' : M'.obj U), ιM x = m ∧ ιM x' = m' := by
  obtain ⟨U, ⟨x, x'⟩, h⟩ := Types.jointly_surjective_of_isColimit
    ((isColimitOfPreserves (forget AddCommGrpCat) hcM).tensor
      (isColimitOfPreserves (forget AddCommGrpCat) hcM')) ⟨m, m'⟩
  rw [Prod.ext_iff] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨U, x, x', rfl, rfl⟩

set_option backward.isDefEq.respectTransparency false in
variable {hcR hcM hcM' hcM''} in
/--
lemma `ιM_jointly_surjective₃` / 引理 `ιM_jointly_surjective₃`

English:
lemma ιM_jointly_surjective₃
  statement: (m : ModuleColimit hcR hcM) (m' : ModuleColimit hcR hcM')
  proof: by
  obtain ⟨U, ⟨x, x', x''⟩, h⟩ := Types.jointly_surjective_of_isColimit
    ((isColimitOfPreserves (forget AddCommGrpCat) hcM).tensor
      ((isColimitOfPreserves (forget AddCommGrpCat) hcM').tensor
        (isColimitOfPreserves (forget AddCommGrpCat) hcM''))) ⟨m, m', m''⟩
  rw [Prod.ext_iff]; rw [Prod.ext_iff] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨U, x, x', x'', rfl, rfl, rfl⟩

include hcR in

中文:
引理 ιM_jointly_surjective₃
  结论: (m : ModuleColimit hcR hcM) (m' : ModuleColimit hcR hcM')
  证明: by
  obtain ⟨U, ⟨x, x', x''⟩, h⟩ := Types.jointly_surjective_of_isColimit
    ((isColimitOfPreserves (forget AddCommGrpCat) hcM).tensor
      ((isColimitOfPreserves (forget AddCommGrpCat) hcM').tensor
        (isColimitOfPreserves (forget AddCommGrpCat) hcM''))) ⟨m, m', m''⟩
  rw [Prod.ext_iff]; rw [Prod.ext_iff] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨U, x, x', x'', rfl, rfl, rfl⟩

include hcR in

Depends on / 依赖: AddCommGrpCat, Prod.ext_iff, Types.jointly_surjective_of_isColimit, ext_iff, forget, isColimitOfPreserves, jointly_surjective_of_isColimit, tensor
-/
lemma ιM_jointly_surjective₃ (m : ModuleColimit hcR hcM) (m' : ModuleColimit hcR hcM')
    (m'' : ModuleColimit hcR hcM'') :
    exists (U : Cᵒᵖ) (x : M.obj U) (x' : M'.obj U) (x'' : M''.obj U),
      ιM x = m ∧ ιM x' = m' ∧ ιM x'' = m'' := by
  obtain ⟨U, ⟨x, x', x''⟩, h⟩ := Types.jointly_surjective_of_isColimit
    ((isColimitOfPreserves (forget AddCommGrpCat) hcM).tensor
      ((isColimitOfPreserves (forget AddCommGrpCat) hcM').tensor
        (isColimitOfPreserves (forget AddCommGrpCat) hcM''))) ⟨m, m', m''⟩
  rw [Prod.ext_iff]; rw [Prod.ext_iff] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨U, x, x', x'', rfl, rfl, rfl⟩

include hcR in
/--
lemma `ιR_jointly_surjective` / 引理 `ιR_jointly_surjective`

English:
lemma ιR_jointly_surjective
  given: (r : cR.pt)
  proof: Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget RingCat) hcR) r

中文:
引理 ιR_jointly_surjective
  条件: (r : cR.pt)
  证明: Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget RingCat) hcR) r

Depends on / 依赖: RingCat, Types.jointly_surjective_of_isColimit, forget, isColimitOfPreserves, jointly_surjective_of_isColimit
-/
lemma ιR_jointly_surjective (r : cR.pt) :
    exists (U : Cᵒᵖ) (a : R.obj U), ιR cR a = r :=
  Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget RingCat) hcR) r

set_option backward.isDefEq.respectTransparency false in
variable {hcR hcM} in
/--
lemma `jointly_surjective₂` / 引理 `jointly_surjective₂`

English:
lemma jointly_surjective₂
  given: (r : cR.pt) (m : ModuleColimit hcR hcM)
  proof: by
  obtain ⟨U, ⟨a, x⟩, h⟩ := Types.jointly_surjective_of_isColimit
    ((isColimitOfPreserves (forget RingCat) hcR).tensor
      (isColimitOfPreserves (forget AddCommGrpCat) hcM)) ⟨r, m⟩
  rw [Prod.ext_iff] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨U, a, x, rfl, rfl⟩

中文:
引理 jointly_surjective₂
  条件: (r : cR.pt) (m : ModuleColimit hcR hcM)
  证明: by
  obtain ⟨U, ⟨a, x⟩, h⟩ := Types.jointly_surjective_of_isColimit
    ((isColimitOfPreserves (forget RingCat) hcR).tensor
      (isColimitOfPreserves (forget AddCommGrpCat) hcM)) ⟨r, m⟩
  rw [Prod.ext_iff] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨U, a, x, rfl, rfl⟩

Depends on / 依赖: AddCommGrpCat, Prod.ext_iff, RingCat, Types.jointly_surjective_of_isColimit, ext_iff, forget, isColimitOfPreserves, jointly_surjective_of_isColimit, tensor
-/
lemma jointly_surjective₂ (r : cR.pt) (m : ModuleColimit hcR hcM) :
    exists (U : Cᵒᵖ) (a : R.obj U) (x : M.obj U),
      ιR cR a = r ∧ ιM x = m := by
  obtain ⟨U, ⟨a, x⟩, h⟩ := Types.jointly_surjective_of_isColimit
    ((isColimitOfPreserves (forget RingCat) hcR).tensor
      (isColimitOfPreserves (forget AddCommGrpCat) hcM)) ⟨r, m⟩
  rw [Prod.ext_iff] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨U, a, x, rfl, rfl⟩

set_option backward.isDefEq.respectTransparency false in
variable {hcR hcM} in
/--
lemma `jointly_surjective₃` / 引理 `jointly_surjective₃`

English:
lemma jointly_surjective₃
  given: (r₁ r₂ : cR.pt) (m : ModuleColimit hcR hcM)
  proof: by
  obtain ⟨U, ⟨a₁, a₂, x⟩, h⟩ := Types.jointly_surjective_of_isColimit
    ((isColimitOfPreserves (forget RingCat) hcR).tensor
      ((isColimitOfPreserves (forget RingCat) hcR).tensor
        (isColimitOfPreserves (forget AddCommGrpCat) hcM))) ⟨r₁, r₂, m⟩
  rw [Prod.ext_iff]; rw [Prod.ext_iff] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨U, a₁, a₂, x, rfl, rfl, rfl⟩

中文:
引理 jointly_surjective₃
  条件: (r₁ r₂ : cR.pt) (m : ModuleColimit hcR hcM)
  证明: by
  obtain ⟨U, ⟨a₁, a₂, x⟩, h⟩ := Types.jointly_surjective_of_isColimit
    ((isColimitOfPreserves (forget RingCat) hcR).tensor
      ((isColimitOfPreserves (forget RingCat) hcR).tensor
        (isColimitOfPreserves (forget AddCommGrpCat) hcM))) ⟨r₁, r₂, m⟩
  rw [Prod.ext_iff]; rw [Prod.ext_iff] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨U, a₁, a₂, x, rfl, rfl, rfl⟩

Depends on / 依赖: AddCommGrpCat, Prod.ext_iff, RingCat, Types.jointly_surjective_of_isColimit, ext_iff, forget, isColimitOfPreserves, jointly_surjective_of_isColimit, tensor
-/
lemma jointly_surjective₃ (r₁ r₂ : cR.pt) (m : ModuleColimit hcR hcM) :
    exists (U : Cᵒᵖ) (a₁ a₂ : R.obj U) (x : M.obj U),
      ιR cR a₁ = r₁ ∧ ιR cR a₂ = r₂ ∧ ιM x = m := by
  obtain ⟨U, ⟨a₁, a₂, x⟩, h⟩ := Types.jointly_surjective_of_isColimit
    ((isColimitOfPreserves (forget RingCat) hcR).tensor
      ((isColimitOfPreserves (forget RingCat) hcR).tensor
        (isColimitOfPreserves (forget AddCommGrpCat) hcM))) ⟨r₁, r₂, m⟩
  rw [Prod.ext_iff]; rw [Prod.ext_iff] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨U, a₁, a₂, x, rfl, rfl, rfl⟩

set_option backward.isDefEq.respectTransparency false in
variable {hcR hcM hcM'} in
/--
lemma `jointly_surjective₃'` / 引理 `jointly_surjective₃'`

English:
lemma jointly_surjective₃'
  given: (r : cR.pt) (m₁ : ModuleColimit hcR hcM) (m₂ : ModuleColimit hcR hcM')
  proof: by
  obtain ⟨U, ⟨a, x₁, x₂⟩, h⟩ := Types.jointly_surjective_of_isColimit
    ((isColimitOfPreserves (forget RingCat) hcR).tensor
      ((isColimitOfPreserves (forget AddCommGrpCat) hcM).tensor
        (isColimitOfPreserves (forget AddCommGrpCat) hcM'))) ⟨r, m₁, m₂⟩
  rw [Prod.ext_iff]; rw [Prod.ext_iff] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨U, a, x₁, x₂, rfl, rfl, rfl⟩

中文:
引理 jointly_surjective₃'
  条件: (r : cR.pt) (m₁ : ModuleColimit hcR hcM) (m₂ : ModuleColimit hcR hcM')
  证明: by
  obtain ⟨U, ⟨a, x₁, x₂⟩, h⟩ := Types.jointly_surjective_of_isColimit
    ((isColimitOfPreserves (forget RingCat) hcR).tensor
      ((isColimitOfPreserves (forget AddCommGrpCat) hcM).tensor
        (isColimitOfPreserves (forget AddCommGrpCat) hcM'))) ⟨r, m₁, m₂⟩
  rw [Prod.ext_iff]; rw [Prod.ext_iff] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨U, a, x₁, x₂, rfl, rfl, rfl⟩

Depends on / 依赖: AddCommGrpCat, Prod.ext_iff, RingCat, Types.jointly_surjective_of_isColimit, ext_iff, forget, isColimitOfPreserves, jointly_surjective_of_isColimit, tensor
-/
lemma jointly_surjective₃' (r : cR.pt) (m₁ : ModuleColimit hcR hcM) (m₂ : ModuleColimit hcR hcM') :
    exists (U : Cᵒᵖ) (a : R.obj U) (x₁ : M.obj U) (x₂ : M'.obj U),
      ιR cR a = r ∧ ιM x₁ = m₁ ∧ ιM x₂ = m₂ := by
  obtain ⟨U, ⟨a, x₁, x₂⟩, h⟩ := Types.jointly_surjective_of_isColimit
    ((isColimitOfPreserves (forget RingCat) hcR).tensor
      ((isColimitOfPreserves (forget AddCommGrpCat) hcM).tensor
        (isColimitOfPreserves (forget AddCommGrpCat) hcM'))) ⟨r, m₁, m₂⟩
  rw [Prod.ext_iff]; rw [Prod.ext_iff] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨U, a, x₁, x₂, rfl, rfl, rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module cR.pt (ModuleColimit hcR hcM)
  body: by
    obtain ⟨U, r₁, r₂, m, rfl, rfl, rfl⟩ := jointly_surjective₃ r₁ r₂ m
    simp only [smul_eq, ← mul_smul, ← map_mul]
  one_smul m := by
    obtain ⟨U, m, rfl⟩ := ιM_jointly_surjective m
    simpa using smul_eq hcR hcM 1 m
  zero_smul m := by
    obtain ⟨U, m, rfl⟩ := ιM_jointly_surjective m
    simpa using smul_eq hcR hcM 0 m
  smul_zero r := by
    obtain ⟨U, r, rfl⟩ := ιR_jointly_surjective hcR r
    simpa using smul_eq hcR hcM r 0
  smul_add r m₁ m₂ := by
    obtain ⟨U, r, m₁, m₂, rfl, rfl, rfl⟩ := jointly_surjective₃' r m₁ m₂
    simp only [smul_eq, smul_add, ← map_add]
  add_smul r₁ r₂ m := by
    obtain ⟨U, r₁, r₂, m, rfl, rfl, rfl⟩ := jointly_surjective₃ r₁ r₂ m
    simp only [smul_eq, ← map_add, add_smul]

中文:
实例 :
  签名: 模 cR.pt (ModuleColimit hcR hcM)
  定义体: by
    obtain ⟨U, r₁, r₂, m, rfl, rfl, rfl⟩ := jointly_surjective₃ r₁ r₂ m
    simp only [smul_eq, ← mul_smul, ← map_mul]
  one_smul m := by
    obtain ⟨U, m, rfl⟩ := ιM_jointly_surjective m
    simpa using smul_eq hcR hcM 1 m
  zero_smul m := by
    obtain ⟨U, m, rfl⟩ := ιM_jointly_surjective m
    simpa using smul_eq hcR hcM 0 m
  smul_zero r := by
    obtain ⟨U, r, rfl⟩ := ιR_jointly_surjective hcR r
    simpa using smul_eq hcR hcM r 0
  smul_add r m₁ m₂ := by
    obtain ⟨U, r, m₁, m₂, rfl, rfl, rfl⟩ := jointly_surjective₃' r m₁ m₂
    simp only [smul_eq, smul_add, ← map_add]
  add_smul r₁ r₂ m := by
    obtain ⟨U, r₁, r₂, m, rfl, rfl, rfl⟩ := jointly_surjective₃ r₁ r₂ m
    simp only [smul_eq, ← map_add, add_smul]

Depends on / 依赖: map_mul, mul_smul, one_smul, smul_add, smul_eq, smul_zero, zero_smul
-/
noncomputable instance : Module cR.pt (ModuleColimit hcR hcM) where
  mul_smul r₁ r₂ m := by
    obtain ⟨U, r₁, r₂, m, rfl, rfl, rfl⟩ := jointly_surjective₃ r₁ r₂ m
    simp only [smul_eq, ← mul_smul, ← map_mul]
  one_smul m := by
    obtain ⟨U, m, rfl⟩ := ιM_jointly_surjective m
    simpa using smul_eq hcR hcM 1 m
  zero_smul m := by
    obtain ⟨U, m, rfl⟩ := ιM_jointly_surjective m
    simpa using smul_eq hcR hcM 0 m
  smul_zero r := by
    obtain ⟨U, r, rfl⟩ := ιR_jointly_surjective hcR r
    simpa using smul_eq hcR hcM r 0
  smul_add r m₁ m₂ := by
    obtain ⟨U, r, m₁, m₂, rfl, rfl, rfl⟩ := jointly_surjective₃' r m₁ m₂
    simp only [smul_eq, smul_add, ← map_add]
  add_smul r₁ r₂ m := by
    obtain ⟨U, r₁, r₂, m, rfl, rfl, rfl⟩ := jointly_surjective₃ r₁ r₂ m
    simp only [smul_eq, ← map_add, add_smul]

/--
Definition of `homEquiv'` / `homEquiv'` 的定义

English:
definition homEquiv'
  signature: {N : Type w} [AddCommGroup N]
  body: (ConcreteCategory.homEquiv (X := AddCommGrpCat.of (ModuleColimit hcR hcM))
    (Y := AddCommGrpCat.of N)).symm.trans hcM.homEquiv
  map_add' _ _ := rfl

omit [LocallySmall.{w, v, u} C] [IsCofiltered C] [InitiallySmall C] in

中文:
定义 homEquiv'
  签名: {N : 类型 w} [加法交换群 N]
  定义体: (ConcreteCategory.homEquiv (X := AddCommGrpCat.of (ModuleColimit hcR hcM))
    (Y := AddCommGrpCat.of N)).symm.trans hcM.homEquiv
  map_add' _ _ := rfl

omit [LocallySmall.{w, v, u} C] [IsCofiltered C] [InitiallySmall C] in

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.of, ConcreteCategory, ConcreteCategory.homEquiv, ModuleColimit, homEquiv
-/
noncomputable def homEquiv' {N : Type w} [AddCommGroup N] :
    (ModuleColimit hcR hcM ->+ N) ≃+ (M.presheaf ⟶ (Functor.const _).obj (.of N)) where
  toEquiv := (ConcreteCategory.homEquiv (X := AddCommGrpCat.of (ModuleColimit hcR hcM))
    (Y := AddCommGrpCat.of N)).symm.trans hcM.homEquiv
  map_add' _ _ := rfl

omit [LocallySmall.{w, v, u} C] [IsCofiltered C] [InitiallySmall C] in
/--
lemma `homEquiv'_app_apply` / 引理 `homEquiv'_app_apply`

English:
lemma homEquiv'_app_apply
  statement: {N : ModuleCat.{w} cR.pt}
  proof: rfl

omit [LocallySmall.{w, v, u} C] [IsCofiltered C] [InitiallySmall C] in

中文:
引理 homEquiv'_app_apply
  结论: {N : 模范畴.{w} cR.pt}
  证明: rfl

omit [LocallySmall.{w, v, u} C] [IsCofiltered C] [InitiallySmall C] in

Depends on / 依赖: Iso.refl
-/
lemma homEquiv'_app_apply {N : ModuleCat.{w} cR.pt}
    (α : ModuleColimit hcR hcM ->+ N) {X : Cᵒᵖ} (x : M.obj X) :
    dsimp% (homEquiv' hcR hcM α).app X x = α (cM.ι.app X x) :=
  rfl

omit [LocallySmall.{w, v, u} C] [IsCofiltered C] [InitiallySmall C] in
/--
lemma `homEquiv'_symm_apply` / 引理 `homEquiv'_symm_apply`

English:
lemma homEquiv'_symm_apply
  statement: {N : ModuleCat.{w} cR.pt}
  proof: ConcreteCategory.congr_hom (hcM.ι_app_homEquiv_symm β X) x

中文:
引理 homEquiv'_symm_apply
  结论: {N : 模范畴.{w} cR.pt}
  证明: ConcreteCategory.congr_hom (hcM.ι_app_homEquiv_symm β X) x
-/
lemma homEquiv'_symm_apply {N : ModuleCat.{w} cR.pt}
    (β : M.presheaf ⟶ (Functor.const _).obj (.of N)) {X : Cᵒᵖ} (x : M.obj X) :
    (homEquiv' hcR hcM).symm β (cM.ι.app X x) = β.app X x :=
  ConcreteCategory.congr_hom (hcM.ι_app_homEquiv_symm β X) x

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `map_smul_homEquiv'_iff` / 引理 `map_smul_homEquiv'_iff`

English:
lemma map_smul_homEquiv'_iff
  statement: {N : ModuleCat.{w} cR.pt}
  proof: by
  refine ⟨fun h r m => ?_, fun h U r m => ?_⟩
  · obtain ⟨U, r, m, rfl, rfl⟩ := jointly_surjective₂ r m
    refine Eq.trans ?_ ((homEquiv'_app_apply ..).symm.trans (h U r m))
    congr 1
    apply smul_eq
  · rw [homEquiv'_app_apply, homEquiv'_app_apply, ← h]
    congr 1
    exact (smul_eq ..).symm

中文:
引理 map_smul_homEquiv'_iff
  结论: {N : 模范畴.{w} cR.pt}
  证明: by
  refine ⟨fun h r m => ?_, fun h U r m => ?_⟩
  · obtain ⟨U, r, m, rfl, rfl⟩ := jointly_surjective₂ r m
    refine Eq.trans ?_ ((homEquiv'_app_apply ..).symm.trans (h U r m))
    congr 1
    apply smul_eq
  · rw [homEquiv'_app_apply, homEquiv'_app_apply, ← h]
    congr 1
    exact (smul_eq ..).symm

Depends on / 依赖: AddCommGrpCat, HasExactColimitsOfShape, HasExactColimitsOfShape.domain_of_functor, ModuleCat, cR.pt, domain_of_functor, homEquiv
-/
lemma map_smul_homEquiv'_iff {N : ModuleCat.{w} cR.pt}
    (α : ModuleColimit hcR hcM ->+ N) :
    dsimp% (forall (U : Cᵒᵖ) (r : R.obj U) (m : M.obj U), (homEquiv' hcR hcM α).app U (r • m) =
        letI m' : N := (homEquiv' hcR hcM α).app U m; letI r' : cR.pt := cR.ι.app U r
        r' • m') ↔
    forall (r : cR.pt) (m : ModuleColimit hcR hcM), α (r • m) = r • α m := by
  refine ⟨fun h r m => ?_, fun h U r m => ?_⟩
  · obtain ⟨U, r, m, rfl, rfl⟩ := jointly_surjective₂ r m
    refine Eq.trans ?_ ((homEquiv'_app_apply ..).symm.trans (h U r m))
    congr 1
    apply smul_eq
  · rw [homEquiv'_app_apply, homEquiv'_app_apply, ← h]
    congr 1
    exact (smul_eq ..).symm

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `homEquiv` / `homEquiv` 的定义

English:
definition homEquiv
  signature: {N : ModuleCat.{w} cR.pt}
  body: PresheafOfModules.homMk
    (homEquiv' hcR hcM ((forget₂ _ AddCommGrpCat).map φ).hom)
      ((map_smul_homEquiv'_iff hcR hcM ((forget₂ _ AddCommGrpCat).map φ).hom).2 (by simp))
  invFun ψ := ModuleCat.ofHom
    { toFun := (homEquiv' hcR hcM).symm ((toPresheaf _).map ψ)
      map_add' := by simp
      map_smul' := by
        obtain ⟨φ, hφ⟩ := (homEquiv' hcR hcM).surjective ((toPresheaf _).map ψ)
        simp only [← hφ, AddEquiv.symm_apply_apply, RingHom.id_apply]
        refine (map_smul_homEquiv'_iff hcR hcM φ).1 (fun U r m => ?_)
        rw [hφ]
        erw [toPresheaf_map_app_apply]
        rw [map_smul]
        rfl }
  left_inv φ := (forget₂ _ AddCommGrpCat).map_injective (by
    ext : 1
    exact (homEquiv' hcR hcM).left_inv ((forget₂ _ AddCommGrpCat).map φ).hom)
  right_inv ψ := (toPresheaf _).map_injective ((homEquiv' hcR hcM).right_inv _)
  map_add' φ₁ φ₂ := (toPresheaf _).map_injective
    ((homEquiv' hcR hcM).map_add ((forget₂ _ AddCommGrpCat).map φ₁).hom
      ((forget₂ _ AddCommGrpCat).map φ₂).hom)

中文:
定义 homEquiv
  签名: {N : 模范畴.{w} cR.pt}
  定义体: PresheafOfModules.homMk
    (homEquiv' hcR hcM ((forget₂ _ AddCommGrpCat).map φ).hom)
      ((map_smul_homEquiv'_iff hcR hcM ((forget₂ _ AddCommGrpCat).map φ).hom).2 (by simp))
  invFun ψ := ModuleCat.ofHom
    { toFun := (homEquiv' hcR hcM).symm ((toPresheaf _).map ψ)
      map_add' := by simp
      map_smul' := by
        obtain ⟨φ, hφ⟩ := (homEquiv' hcR hcM).surjective ((toPresheaf _).map ψ)
        simp only [← hφ, AddEquiv.symm_apply_apply, RingHom.id_apply]
        refine (map_smul_homEquiv'_iff hcR hcM φ).1 (fun U r m => ?_)
        rw [hφ]
        erw [toPresheaf_map_app_apply]
        rw [map_smul]
        rfl }
  left_inv φ := (forget₂ _ AddCommGrpCat).map_injective (by
    ext : 1
    exact (homEquiv' hcR hcM).left_inv ((forget₂ _ AddCommGrpCat).map φ).hom)
  right_inv ψ := (toPresheaf _).map_injective ((homEquiv' hcR hcM).right_inv _)
  map_add' φ₁ φ₂ := (toPresheaf _).map_injective
    ((homEquiv' hcR hcM).map_add ((forget₂ _ AddCommGrpCat).map φ₁).hom
      ((forget₂ _ AddCommGrpCat).map φ₂).hom)

Depends on / 依赖: PresheafOfModules, PresheafOfModules.homMk
-/
noncomputable def homEquiv {N : ModuleCat.{w} cR.pt} :
    (ModuleCat.of cR.pt (ModuleColimit hcR hcM) ⟶ N) ≃+ (M ⟶ (constFunctor cR).obj N) where
  toFun φ := PresheafOfModules.homMk
    (homEquiv' hcR hcM ((forget₂ _ AddCommGrpCat).map φ).hom)
      ((map_smul_homEquiv'_iff hcR hcM ((forget₂ _ AddCommGrpCat).map φ).hom).2 (by simp))
  invFun ψ := ModuleCat.ofHom
    { toFun := (homEquiv' hcR hcM).symm ((toPresheaf _).map ψ)
      map_add' := by simp
      map_smul' := by
        obtain ⟨φ, hφ⟩ := (homEquiv' hcR hcM).surjective ((toPresheaf _).map ψ)
        simp only [← hφ, AddEquiv.symm_apply_apply, RingHom.id_apply]
        refine (map_smul_homEquiv'_iff hcR hcM φ).1 (fun U r m => ?_)
        rw [hφ]
        erw [toPresheaf_map_app_apply]
        rw [map_smul]
        rfl }
  left_inv φ := (forget₂ _ AddCommGrpCat).map_injective (by
    ext : 1
    exact (homEquiv' hcR hcM).left_inv ((forget₂ _ AddCommGrpCat).map φ).hom)
  right_inv ψ := (toPresheaf _).map_injective ((homEquiv' hcR hcM).right_inv _)
  map_add' φ₁ φ₂ := (toPresheaf _).map_injective
    ((homEquiv' hcR hcM).map_add ((forget₂ _ AddCommGrpCat).map φ₁).hom
      ((forget₂ _ AddCommGrpCat).map φ₂).hom)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `homEquiv_app_apply` / 引理 `homEquiv_app_apply`

English:
lemma homEquiv_app_apply
  statement: {N : ModuleCat.{w} cR.pt}
  proof: rfl

中文:
引理 homEquiv_app_apply
  结论: {N : 模范畴.{w} cR.pt}
  证明: rfl
-/
lemma homEquiv_app_apply {N : ModuleCat.{w} cR.pt}
    (α : ModuleCat.of cR.pt (ModuleColimit hcR hcM) ⟶ N) {X : Cᵒᵖ} (x : M.obj X) :
    dsimp% (homEquiv hcR hcM α).app X x = α (cM.ι.app X x) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `homEquiv_naturality_right` / 引理 `homEquiv_naturality_right`

English:
lemma homEquiv_naturality_right
  statement: {N N' : ModuleCat.{w} cR.pt}
  proof: rfl

中文:
引理 homEquiv_naturality_right
  结论: {N N' : 模范畴.{w} cR.pt}
  证明: rfl
-/
lemma homEquiv_naturality_right {N N' : ModuleCat.{w} cR.pt}
    (φ : ModuleCat.of cR.pt (ModuleColimit hcR hcM) ⟶ N) (g : N ⟶ N') :
    homEquiv hcR hcM (φ ≫ g) = homEquiv hcR hcM φ ≫ (constFunctor cR).map g := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `homEquiv_symm_apply` / 引理 `homEquiv_symm_apply`

English:
lemma homEquiv_symm_apply
  statement: {N : ModuleCat.{w} cR.pt} (β : M ⟶ (constFunctor cR).obj N)
  proof: by
  exact homEquiv'_symm_apply ..

中文:
引理 homEquiv_symm_apply
  结论: {N : 模范畴.{w} cR.pt} (β : M ⟶ (constFunctor cR).obj N)
  证明: by
  exact homEquiv'_symm_apply ..

Depends on / 依赖: _symm_apply, homEquiv
-/
lemma homEquiv_symm_apply {N : ModuleCat.{w} cR.pt} (β : M ⟶ (constFunctor cR).obj N)
    {X : Cᵒᵖ} (x : M.obj X) :
    dsimp% (homEquiv hcR hcM).symm β (cM.ι.app X x) = β.app X x := by
  exact homEquiv'_symm_apply ..

section

variable {M' : PresheafOfModules.{w} R} {cM' : Cocone M'.presheaf}
  (hcM' : IsColimit cM')

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : M ⟶ M')
  body: hcM.desc ((Cocone.precompose ((toPresheaf _).map f)).obj cM')
  map_add' _ _ := map_add _ _ _
  map_smul' r m := by
    obtain ⟨U, r, m, rfl, rfl⟩ := ModuleColimit.jointly_surjective₂ r m
    let c := (Cocone.precompose ((toPresheaf _).map f)).obj cM'
    have h₁ := ConcreteCategory.congr_hom (hcM.fac c U) (r • m)
    have h₂ := ConcreteCategory.congr_hom (hcM.fac c U) m
    dsimp [c] at h₁ h₂ ⊢
    rw [ModuleColimit.smul_eq]
    erw [h₁, h₂, ModuleColimit.smul_eq, ← (f.app U).hom.map_smul]
    rfl

中文:
定义 map
  签名: (f : M ⟶ M')
  定义体: hcM.desc ((Cocone.precompose ((toPresheaf _).map f)).obj cM')
  map_add' _ _ := map_add _ _ _
  map_smul' r m := by
    obtain ⟨U, r, m, rfl, rfl⟩ := ModuleColimit.jointly_surjective₂ r m
    let c := (Cocone.precompose ((toPresheaf _).map f)).obj cM'
    have h₁ := ConcreteCategory.congr_hom (hcM.fac c U) (r • m)
    have h₂ := ConcreteCategory.congr_hom (hcM.fac c U) m
    dsimp [c] at h₁ h₂ ⊢
    rw [ModuleColimit.smul_eq]
    erw [h₁, h₂, ModuleColimit.smul_eq, ← (f.app U).hom.map_smul]
    rfl

Depends on / 依赖: Cocone, Cocone.precompose, hcM.desc, precompose, toPresheaf
-/
noncomputable def map (f : M ⟶ M') :
    ModuleColimit hcR hcM ->ₗ[cR.pt] ModuleColimit hcR hcM' where
  toFun := hcM.desc ((Cocone.precompose ((toPresheaf _).map f)).obj cM')
  map_add' _ _ := map_add _ _ _
  map_smul' r m := by
    obtain ⟨U, r, m, rfl, rfl⟩ := ModuleColimit.jointly_surjective₂ r m
    let c := (Cocone.precompose ((toPresheaf _).map f)).obj cM'
    have h₁ := ConcreteCategory.congr_hom (hcM.fac c U) (r • m)
    have h₂ := ConcreteCategory.congr_hom (hcM.fac c U) m
    dsimp [c] at h₁ h₂ ⊢
    rw [ModuleColimit.smul_eq]
    erw [h₁, h₂, ModuleColimit.smul_eq, ← (f.app U).hom.map_smul]
    rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `map_apply` / 引理 `map_apply`

English:
lemma map_apply
  given: (f : M ⟶ M') {U : Cᵒᵖ} (m : M.obj U)
  proof: ConcreteCategory.congr_hom (hcM.fac ((Cocone.precompose ((toPresheaf _).map f)).obj cM') U) m

中文:
引理 map_apply
  条件: (f : M ⟶ M') {U : Cᵒᵖ} (m : M.obj U)
  证明: ConcreteCategory.congr_hom (hcM.fac ((Cocone.precompose ((toPresheaf _).map f)).obj cM') U) m

Depends on / 依赖: Cocone, Cocone.precompose, ConcreteCategory, ConcreteCategory.congr_hom, congr_hom, hcM.fac, precompose, toPresheaf
-/
lemma map_apply (f : M ⟶ M') {U : Cᵒᵖ} (m : M.obj U) :
    dsimp% map hcR hcM hcM' f (ιM m) = ιM (f.app _ m) :=
  ConcreteCategory.congr_hom (hcM.fac ((Cocone.precompose ((toPresheaf _).map f)).obj cM') U) m

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  statement: map hcR hcM hcM (𝟙 M) = .id
  proof: by
  ext m
  obtain ⟨U, m, rfl⟩ := ιM_jointly_surjective m
  simp

中文:
引理 map_id
  结论: map hcR hcM hcM (𝟙 M) = .id
  证明: by
  ext m
  obtain ⟨U, m, rfl⟩ := ιM_jointly_surjective m
  simp
-/
lemma map_id : map hcR hcM hcM (𝟙 M) = .id := by
  ext m
  obtain ⟨U, m, rfl⟩ := ιM_jointly_surjective m
  simp

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `comp_map` / 引理 `comp_map`

English:
lemma comp_map
  proof: by
  ext m
  obtain ⟨U, m, rfl⟩ := ιM_jointly_surjective m
  simp

中文:
引理 comp_map
  证明: by
  ext m
  obtain ⟨U, m, rfl⟩ := ιM_jointly_surjective m
  simp
-/
lemma comp_map
    (f : M ⟶ M')
    {M'' : PresheafOfModules.{w} R} {cM'' : Cocone M''.presheaf}
    (hcM'' : IsColimit cM'') (g : M' ⟶ M'') :
    (map hcR hcM' hcM'' g).comp (map hcR hcM hcM' f) = map hcR hcM hcM'' (f ≫ g) := by
  ext m
  obtain ⟨U, m, rfl⟩ := ιM_jointly_surjective m
  simp

end

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `homEquiv_naturality_left` / 引理 `homEquiv_naturality_left`

English:
lemma homEquiv_naturality_left
  statement: {M' : PresheafOfModules.{w} R} {cM' : Cocone M'.presheaf}
  proof: by
  ext U m
  simp only [homEquiv_app_apply, ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp,
    Function.comp_apply, comp_app]
  apply congr_arg
  exact map_apply hcR hcM hcM' f m

中文:
引理 homEquiv_naturality_left
  结论: {M' : 预模层.{w} R} {cM' : 余锥 M'.presheaf}
  证明: by
  ext U m
  simp only [homEquiv_app_apply, ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp,
    Function.comp_apply, comp_app]
  apply congr_arg
  exact map_apply hcR hcM hcM' f m

Depends on / 依赖: Function, Function.comp_apply, LinearMap, LinearMap.coe_comp, ModuleCat, ModuleCat.hom_comp, ModuleCat.hom_ofHom, coe_comp, comp_app, comp_apply, congr_arg, homEquiv_app_apply, hom_comp, hom_ofHom, map_apply
-/
lemma homEquiv_naturality_left {M' : PresheafOfModules.{w} R} {cM' : Cocone M'.presheaf}
    (hcM' : IsColimit cM') {N : ModuleCat.{w} cR.pt}
    (φ' : ModuleCat.of cR.pt (ModuleColimit hcR hcM') ⟶ N)
    (f : M ⟶ M') :
    homEquiv hcR hcM (ModuleCat.ofHom (map hcR hcM hcM' f) ≫ φ') =
      f ≫ homEquiv hcR hcM' φ' := by
  ext U m
  simp only [homEquiv_app_apply, ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp,
    Function.comp_apply, comp_app]
  apply congr_arg
  exact map_apply hcR hcM hcM' f m

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `homEquiv_naturality_left_symm` / 引理 `homEquiv_naturality_left_symm`

English:
lemma homEquiv_naturality_left_symm
  statement: {M' : PresheafOfModules.{w} R} {cM' : Cocone M'.presheaf}
  proof: (homEquiv hcR hcM).injective (by
    obtain ⟨g, rfl⟩ := (homEquiv hcR hcM').surjective g
    simp [homEquiv_naturality_left])

中文:
引理 homEquiv_naturality_left_symm
  结论: {M' : 预模层.{w} R} {cM' : 余锥 M'.presheaf}
  证明: (homEquiv hcR hcM).injective (by
    obtain ⟨g, rfl⟩ := (homEquiv hcR hcM').surjective g
    simp [homEquiv_naturality_left])

Depends on / 依赖: homEquiv, homEquiv_naturality_left, injective, surjective
-/
lemma homEquiv_naturality_left_symm {M' : PresheafOfModules.{w} R} {cM' : Cocone M'.presheaf}
    (hcM' : IsColimit cM') {N : ModuleCat.{w} cR.pt}
    (f : M ⟶ M') (g : M' ⟶ (constFunctor cR).obj N) :
    (homEquiv hcR hcM).symm (f ≫ g) =
      ModuleCat.ofHom (map hcR hcM hcM' f) ≫ (homEquiv hcR hcM').symm g :=
  (homEquiv hcR hcM).injective (by
    obtain ⟨g, rfl⟩ := (homEquiv hcR hcM').surjective g
    simp [homEquiv_naturality_left])

end ModuleColimit

end

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `colimitFunctor` / `colimitFunctor` 的定义

English:
definition colimitFunctor
  signature: : PresheafOfModules.{w} R ⥤ ModuleCat.{w} cR.pt where
  body: ModuleCat.of _ (ModuleColimit hcR (colimit.isColimit M.presheaf))
  map f := ModuleCat.ofHom (ModuleColimit.map _ _ _ f)
  map_comp f g := by ext : 1; exact (ModuleColimit.comp_map ..).symm

中文:
定义 colimitFunctor
  签名: : 预模层.{w} R ⥤ 模范畴.{w} cR.pt where
  定义体: ModuleCat.of _ (ModuleColimit hcR (colimit.isColimit M.presheaf))
  map f := ModuleCat.ofHom (ModuleColimit.map _ _ _ f)
  map_comp f g := by ext : 1; exact (ModuleColimit.comp_map ..).symm

Depends on / 依赖: M.presheaf, ModuleCat, ModuleCat.of, ModuleColimit, colimit, colimit.isColimit, isColimit, presheaf
-/
noncomputable def colimitFunctor : PresheafOfModules.{w} R ⥤ ModuleCat.{w} cR.pt where
  obj M := ModuleCat.of _ (ModuleColimit hcR (colimit.isColimit M.presheaf))
  map f := ModuleCat.ofHom (ModuleColimit.map _ _ _ f)
  map_comp f g := by ext : 1; exact (ModuleColimit.comp_map ..).symm

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `colimitAdjunction` / `colimitAdjunction` 的定义

English:
definition colimitAdjunction
  signature: :
  body: Adjunction.mkOfHomEquiv
    { homEquiv _ _ := (ModuleColimit.homEquiv _ _).toEquiv
      homEquiv_naturality_left_symm _ _ := ModuleColimit.homEquiv_naturality_left_symm _ _ _ _ _
      homEquiv_naturality_right _ _ := ModuleColimit.homEquiv_naturality_right _ _ _ _ }

中文:
定义 colimitAdjunction
  签名: :
  定义体: Adjunction.mkOfHomEquiv
    { homEquiv _ _ := (ModuleColimit.homEquiv _ _).toEquiv
      homEquiv_naturality_left_symm _ _ := ModuleColimit.homEquiv_naturality_left_symm _ _ _ _ _
      homEquiv_naturality_right _ _ := ModuleColimit.homEquiv_naturality_right _ _ _ _ }

Depends on / 依赖: Adjunction, Adjunction.mkOfHomEquiv, ModuleColimit, ModuleColimit.homEquiv, ModuleColimit.homEquiv_naturality_left_symm, ModuleColimit.homEquiv_naturality_right, homEquiv, homEquiv_naturality_left_symm, homEquiv_naturality_right, mkOfHomEquiv, toEquiv
-/
noncomputable def colimitAdjunction :
    colimitFunctor.{w} hcR ⊣ constFunctor.{w} cR :=
  Adjunction.mkOfHomEquiv
    { homEquiv _ _ := (ModuleColimit.homEquiv _ _).toEquiv
      homEquiv_naturality_left_symm _ _ := ModuleColimit.homEquiv_naturality_left_symm _ _ _ _ _
      homEquiv_naturality_right _ _ := ModuleColimit.homEquiv_naturality_right _ _ _ _ }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `colimitAdjunction_homEquiv` / 引理 `colimitAdjunction_homEquiv`

English:
lemma colimitAdjunction_homEquiv
  proof: by
  simp [colimitAdjunction]

中文:
引理 colimitAdjunction_homEquiv
  证明: by
  simp [colimitAdjunction]

Depends on / 依赖: colimitAdjunction
-/
lemma colimitAdjunction_homEquiv
    (F : PresheafOfModules R) (G : ModuleCat cR.pt) :
    dsimp% (colimitAdjunction.{w} hcR).homEquiv F G =
      (ModuleColimit.homEquiv hcR
        (colimit.isColimit F.presheaf)).toEquiv := by
  simp [colimitAdjunction]

set_option backward.isDefEq.respectTransparency.types false in
open ModuleColimit in
/--
lemma `colimitAdjunction_homEquiv_symm_apply` / 引理 `colimitAdjunction_homEquiv_symm_apply`

English:
lemma colimitAdjunction_homEquiv_symm_apply
  proof: by
  rw [colimitAdjunction_homEquiv]
  apply homEquiv_symm_apply

中文:
引理 colimitAdjunction_homEquiv_symm_apply
  证明: by
  rw [colimitAdjunction_homEquiv]
  apply homEquiv_symm_apply

Depends on / 依赖: F.presheaf, colimit, colimit.isColimit, isColimit, presheaf
-/
lemma colimitAdjunction_homEquiv_symm_apply
    {F : PresheafOfModules R} {G : ModuleCat cR.pt}
    (β : F ⟶ (constFunctor cR).obj G) {X : Cᵒᵖ} (m : F.obj X) :
    ((colimitAdjunction.{w} hcR).homEquiv F G).symm β
      (ModuleColimit.ιM (hcR := hcR) (hcM := colimit.isColimit F.presheaf) m) =
        β.app X m := by
  rw [colimitAdjunction_homEquiv]
  apply homEquiv_symm_apply

end PresheafOfModules
