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
/-- Given a cocone `cR` for a functor `R : Cᵒᵖ ⥤ RingCat`, this is the
functor `ModuleCat cR.pt ⥤ PresheafOfModules R` which sends a module `M`
over `cR.pt` to a presheaf of modules whose underlying presheaf of
abelian groups is the constant functor `Cᵒᵖ ⥤ AddCommGrpCat` with value `M`. -/
/-
**PresheafOfModules.constFunctor** 是 Mathlib 中的一个定义，位于命名空间 `PresheafOfModules`。
形式化陈述：constFunctor : ModuleCat cR.pt ⥤ PresheafOfModules.{w} R where obj M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a cocone `cR` for a functor `R : Cᵒᵖ ⥤ RingCat`, this is the
functor `ModuleCat cR.pt ⥤ PresheafOfModules R` which sends a module `M`
over `cR.pt` to a presheaf of modules whose underlying presheaf of
abelian groups is the constant functor `Cᵒᵖ ⥤ AddCommGrpCat` with value `M`.
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
/-
**PresheafOfModules.ModuleColimit** 是 Mathlib 中的一个定义，位于命名空间 `PresheafOfModules`。
形式化陈述：ModuleColimit (_ : IsColimit cR) (_ : IsColimit cM) : Type w
参数：_ : IsColimit cR；_ : IsColimit cM。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a colimit cocone for a presheaf of rings `R` on a cofiltered category `C`,
`M` a presheaf of modules over `R`, and a colimit cocone `cM` for the underlying
functor `Cᵒᵖ ⥤ AddCommGrpCat` of `M`, this is the type `cM.pt` on which we defin
e
a module structure below.
-/
def ModuleColimit (_ : IsColimit cR) (_ : IsColimit cM) : Type w := cM.pt
/-
**PresheafOfModules.** 是 Mathlib 中的一个实例，位于命名空间 `PresheafOfModules`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommGroup (ModuleColimit hcR hcM) :=
  inferInstanceAs (AddCommGroup cM.pt)

namespace ModuleColimit

/-- The cocone for `R ⋙ forget _ ⊗ M.presheaf ⋙ forget _` with point
`ModuleColimit hcR hcM` which allows to define the scalar multiplication
by `cR.pt` on `ModuleColimit hcR hcM`. -/
@[simps]
/-
**PresheafOfModules.ModuleColimit.coconeSMul** 是 Mathlib 中的一个定义，位于命名空间 `Presheaf
OfModules.ModuleColimit`。
形式化陈述：coconeSMul : Cocone (R ⋙ forget _ otimes M.presheaf ⋙ forget _) where pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cocone for `R ⋙ forget _ ⊗ M.presheaf ⋙ forget _` with point
`ModuleColimit hcR hcM` which allows to define the scalar multiplication
by `cR.pt` on `ModuleColimit hcR hcM`.
-/
noncomputable def coconeSMul :
    Cocone (R ⋙ forget _ ⊗ M.presheaf ⋙ forget _) where
  pt := ModuleColimit hcR hcM
  ι.app U := ↾fun ⟨(r : R.obj U), (m : M.obj U)⟩ ↦ by exact cM.ι.app U (r • m)
  ι.naturality V U f := by
    ext ⟨r, m⟩
    exact (ConcreteCategory.congr_arg (cM.ι.app U)
      (M.map_smul f r m).symm).trans (ConcreteCategory.congr_hom (cM.w f) _)
/-
**PresheafOfModules.ModuleColimit.** 是 Mathlib 中的一个实例，位于命名空间 `PresheafOfModules.
ModuleColimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : SMul cR.pt (ModuleColimit hcR hcM) where
  smul :=
    (((isColimitOfPreserves (forget _) hcR).tensor
      (isColimitOfPreserves (forget _) hcM)).desc (coconeSMul hcR hcM) : _ → _).curry

variable (cR) in
/-- The "inclusion" maps to the colimit ring. -/
/-
**PresheafOfModules.ModuleColimit.** 是 Mathlib 中的一个缩写定义，位于命名空间 `PresheafOfModule
s.ModuleColimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "inclusion" maps to the colimit ring.
-/
abbrev ιR {U : Cᵒᵖ} : R.obj U →+* cR.pt := (cR.ι.app U).hom

variable {hcR hcM} in
/-- The "inclusion" maps to the colimit module, as an additive map. -/
/-
**PresheafOfModules.ModuleColimit.** 是 Mathlib 中的一个缩写定义，位于命名空间 `PresheafOfModule
s.ModuleColimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "inclusion" maps to the colimit module, as an additive map.
-/
noncomputable abbrev ιM {U : Cᵒᵖ} : M.obj U →+ ModuleColimit hcR hcM :=
  (cM.ι.app U).hom

@[simp]
/-
**PresheafOfModules.ModuleColimit.smul_eq** 是 Mathlib 中的一个引理，位于命名空间 `PresheafOfM
odules.ModuleColimit`。
形式化陈述：smul_eq {U : Cᵒᵖ} (r : R.obj U) (m : M.obj U) : ιR cR r • ιM (hcR
参数：r : R.obj U；m : M.obj U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用引理 `CategoryTheory.FinallySmall.preservesColimitsOfShape_of_isFiltered`：pres
ervesColimitsOfShape_of_isFiltered {D E : Type*} [Category* D] [Category* E] (F 
: D ⥤ E) [PreservesFilteredColimitsOfSize.{w, w} F] : Pr…
· 使用定理 `CategoryTheory.instLocallySmallOpposite`：∀ (C : Type u) [inst : Category
Theory.Category.{v, u} C] [CategoryTheory.LocallySmall.{w, v, u} C],   CategoryT
heory.LocallySmall.{w, v, u} …
· 使用定理 `CategoryTheory.instFinallySmallOppositeOfInitiallySmall`：∀ {J : Type u} 
[inst : CategoryTheory.Category.{v, u} J] [CategoryTheory.InitiallySmall J],   C
ategoryTheory.FinallySmall Jᵒᵖ
· 使用定理 `CategoryTheory.Limits.PreservesColimits.preservesFilteredColimits`：∀ {C 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : C
ategoryTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.instPreservesColimitsTensorLeft`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.MonoidalCategory C] (A
 : C)   [CategoryTheory.Closed A], C…
· 使用定理 `CategoryTheory.IsFiltered.isSifted`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] [CategoryTheory.IsFiltered C], CategoryTheory.IsSifted C
· 使用定理 `AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits`：Categor
yTheory.Limits.PreservesFilteredColimits (CategoryTheory.forget AddCommGrpCat)
· 使用定理 `CategoryTheory.Limits.IsColimit.fac`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} C]   {F : CategoryTheor…
-/
lemma smul_eq {U : Cᵒᵖ} (r : R.obj U) (m : M.obj U) :
    ιR cR r • ιM (hcR := hcR) (hcM := hcM) m = ιM (r • m) :=
  ConcreteCategory.congr_hom (((isColimitOfPreserves (forget _) hcR).tensor
    (isColimitOfPreserves (forget _) hcM)).fac (coconeSMul hcR hcM) U) ⟨r, m⟩

variable {hcR hcM} in
/-
**PresheafOfModules.ModuleColimit.** 是 Mathlib 中的一个引理，位于命名空间 `PresheafOfModules.
ModuleColimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ιM_jointly_surjective (m : ModuleColimit hcR hcM) :
    ∃ (U : Cᵒᵖ) (x : M.obj U), ιM x = m :=
  Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget AddCommGrpCat) hcM) m

set_option backward.isDefEq.respectTransparency false in
variable {hcR hcM hcM'} in
/-
**PresheafOfModules.ModuleColimit.** 是 Mathlib 中的一个引理，位于命名空间 `PresheafOfModules.
ModuleColimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ιM_jointly_surjective₂ (m : ModuleColimit hcR hcM) (m' : ModuleColimit hcR hcM') :
    ∃ (U : Cᵒᵖ) (x : M.obj U) (x' : M'.obj U), ιM x = m ∧ ιM x' = m' := by
  obtain ⟨U, ⟨x, x'⟩, h⟩ := Types.jointly_surjective_of_isColimit
    ((isColimitOfPreserves (forget AddCommGrpCat) hcM).tensor
      (isColimitOfPreserves (forget AddCommGrpCat) hcM')) ⟨m, m'⟩
  rw [Prod.ext_iff] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨U, x, x', rfl, rfl⟩

set_option backward.isDefEq.respectTransparency false in
variable {hcR hcM hcM' hcM''} in
/-
**PresheafOfModules.ModuleColimit.** 是 Mathlib 中的一个引理，位于命名空间 `PresheafOfModules.
ModuleColimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ιM_jointly_surjective₃ (m : ModuleColimit hcR hcM) (m' : ModuleColimit hcR hcM')
    (m'' : ModuleColimit hcR hcM'') :
    ∃ (U : Cᵒᵖ) (x : M.obj U) (x' : M'.obj U) (x'' : M''.obj U),
      ιM x = m ∧ ιM x' = m' ∧ ιM x'' = m'' := by
  obtain ⟨U, ⟨x, x', x''⟩, h⟩ := Types.jointly_surjective_of_isColimit
    ((isColimitOfPreserves (forget AddCommGrpCat) hcM).tensor
      ((isColimitOfPreserves (forget AddCommGrpCat) hcM').tensor
        (isColimitOfPreserves (forget AddCommGrpCat) hcM''))) ⟨m, m', m''⟩
  rw [Prod.ext_iff, Prod.ext_iff] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨U, x, x', x'', rfl, rfl, rfl⟩

include hcR in
/-
**PresheafOfModules.ModuleColimit.** 是 Mathlib 中的一个引理，位于命名空间 `PresheafOfModules.
ModuleColimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ιR_jointly_surjective (r : cR.pt) :
    ∃ (U : Cᵒᵖ) (a : R.obj U), ιR cR a = r :=
  Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget RingCat) hcR) r

set_option backward.isDefEq.respectTransparency false in
variable {hcR hcM} in
/-
**PresheafOfModules.ModuleColimit.jointly_surjective** 是 Mathlib 中的一个引理，位于命名空间 `
PresheafOfModules.ModuleColimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma jointly_surjective₂ (r : cR.pt) (m : ModuleColimit hcR hcM) :
    ∃ (U : Cᵒᵖ) (a : R.obj U) (x : M.obj U),
      ιR cR a = r ∧ ιM x = m := by
  obtain ⟨U, ⟨a, x⟩, h⟩ := Types.jointly_surjective_of_isColimit
    ((isColimitOfPreserves (forget RingCat) hcR).tensor
      (isColimitOfPreserves (forget AddCommGrpCat) hcM)) ⟨r, m⟩
  rw [Prod.ext_iff] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨U, a, x, rfl, rfl⟩

set_option backward.isDefEq.respectTransparency false in
variable {hcR hcM} in
/-
**PresheafOfModules.ModuleColimit.jointly_surjective** 是 Mathlib 中的一个引理，位于命名空间 `
PresheafOfModules.ModuleColimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma jointly_surjective₃ (r₁ r₂ : cR.pt) (m : ModuleColimit hcR hcM) :
    ∃ (U : Cᵒᵖ) (a₁ a₂ : R.obj U) (x : M.obj U),
      ιR cR a₁ = r₁ ∧ ιR cR a₂ = r₂ ∧ ιM x = m := by
  obtain ⟨U, ⟨a₁, a₂, x⟩, h⟩ := Types.jointly_surjective_of_isColimit
    ((isColimitOfPreserves (forget RingCat) hcR).tensor
      ((isColimitOfPreserves (forget RingCat) hcR).tensor
        (isColimitOfPreserves (forget AddCommGrpCat) hcM))) ⟨r₁, r₂, m⟩
  rw [Prod.ext_iff, Prod.ext_iff] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨U, a₁, a₂, x, rfl, rfl, rfl⟩

set_option backward.isDefEq.respectTransparency false in
variable {hcR hcM hcM'} in
/-
**PresheafOfModules.ModuleColimit.jointly_surjective** 是 Mathlib 中的一个引理，位于命名空间 `
PresheafOfModules.ModuleColimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma jointly_surjective₃' (r : cR.pt) (m₁ : ModuleColimit hcR hcM) (m₂ : ModuleColimit hcR hcM') :
    ∃ (U : Cᵒᵖ) (a : R.obj U) (x₁ : M.obj U) (x₂ : M'.obj U),
      ιR cR a = r ∧ ιM x₁ = m₁ ∧ ιM x₂ = m₂ := by
  obtain ⟨U, ⟨a, x₁, x₂⟩, h⟩ := Types.jointly_surjective_of_isColimit
    ((isColimitOfPreserves (forget RingCat) hcR).tensor
      ((isColimitOfPreserves (forget AddCommGrpCat) hcM).tensor
        (isColimitOfPreserves (forget AddCommGrpCat) hcM'))) ⟨r, m₁, m₂⟩
  rw [Prod.ext_iff, Prod.ext_iff] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨U, a, x₁, x₂, rfl, rfl, rfl⟩
/-
**PresheafOfModules.ModuleColimit.** 是 Mathlib 中的一个实例，位于命名空间 `PresheafOfModules.
ModuleColimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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

/-- Auxiliary definition for `homEquiv`. This is the universal property
of `PresheafOfModules.ModuleColimit`, as an abelian group. -/
/-
**PresheafOfModules.ModuleColimit.homEquiv'** 是 Mathlib 中的一个定义，位于命名空间 `PresheafO
fModules.ModuleColimit`。
形式化陈述：homEquiv' {N : Type w} [AddCommGroup N] : (ModuleColimit hcR hcM ->+ N) ≃+
 (M.presheaf ⟶ (Functor.const _).obj (.of N)) where toEquiv
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Auxiliary definition for `homEquiv`. This is the universal property
of `PresheafOfModules.ModuleColimit`, as an abelian group.
-/
noncomputable def homEquiv' {N : Type w} [AddCommGroup N] :
    (ModuleColimit hcR hcM →+ N) ≃+ (M.presheaf ⟶ (Functor.const _).obj (.of N)) where
  toEquiv := (ConcreteCategory.homEquiv (X := AddCommGrpCat.of (ModuleColimit hcR hcM))
    (Y := AddCommGrpCat.of N)).symm.trans hcM.homEquiv
  map_add' _ _ := rfl

omit [LocallySmall.{w, v, u} C] [IsCofiltered C] [InitiallySmall C] in
/-
**PresheafOfModules.ModuleColimit.homEquiv'_app_apply** 是 Mathlib 中的一个定理，位于命名空间 
`PresheafOfModules.ModuleColimit`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {R : CategoryTheo
ry.Functor Cᵒᵖ RingCat}   {cR : CategoryTheory.Limits.Cocone R} (hcR : CategoryT
heory.Limits.IsColimit cR) {M : PresheafOfModules R}   {cM : CategoryTheory.Limi
ts.Cocone M.presheaf} (hcM : CategoryTheory.Limits.IsColimit cM) {N : ModuleCat 
↑cR.pt}   (α : PresheafOfModules.ModuleColimit hcR hcM →+ ↑N) {X : Cᵒᵖ} (x : ↑(M
.obj X)),   (CategoryTheory.ConcreteCategory.hom (((PresheafOfModules.ModuleColi
mit.homEquiv' hcR hcM) α).app X)) x =     α ((CategoryTheory.ConcreteCategory.ho
m (cM.ι.app X)) x)
参数：hcR : CategoryTheory.Limits.IsColimit cR；hcM : CategoryTheory.Limits.IsColimi
t cM；α : PresheafOfModules.ModuleColimit hcR hcM →+ ↑N；x : ↑(M.obj X)；CategoryTh
eory.ConcreteCategory.hom (((PresheafOfModules.ModuleColimit.homEquiv' hcR hcM) 
α).app X)；(CategoryTheory.ConcreteCategory.hom (cM.ι.app X)) x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homEquiv'_app_apply {N : ModuleCat.{w} cR.pt}
    (α : ModuleColimit hcR hcM →+ N) {X : Cᵒᵖ} (x : M.obj X) :
    dsimp% (homEquiv' hcR hcM α).app X x = α (cM.ι.app X x) :=
  rfl

omit [LocallySmall.{w, v, u} C] [IsCofiltered C] [InitiallySmall C] in
/-
**PresheafOfModules.ModuleColimit.homEquiv'_symm_apply** 是 Mathlib 中的一个定理，位于命名空间
 `PresheafOfModules.ModuleColimit`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {R : CategoryTheo
ry.Functor Cᵒᵖ RingCat}   {cR : CategoryTheory.Limits.Cocone R} (hcR : CategoryT
heory.Limits.IsColimit cR) {M : PresheafOfModules R}   {cM : CategoryTheory.Limi
ts.Cocone M.presheaf} (hcM : CategoryTheory.Limits.IsColimit cM) {N : ModuleCat 
↑cR.pt}   (β : M.presheaf ⟶ (CategoryTheory.Functor.const Cᵒᵖ).obj (AddCommGrpCa
t.of ↑N)) {X : Cᵒᵖ} (x : ↑(M.obj X)),   ((PresheafOfModules.ModuleColimit.homEqu
iv' hcR hcM).symm β) ((CategoryTheory.ConcreteCategory.hom (cM.ι.app X)) x) =   
  (CategoryTheory.ConcreteCategory.hom (β.app X)) x
参数：hcR : CategoryTheory.Limits.IsColimit cR；hcM : CategoryTheory.Limits.IsColimi
t cM；β : M.presheaf ⟶ (CategoryTheory.Functor.const Cᵒᵖ).obj (AddCommGrpCat.of ↑
N)；x : ↑(M.obj X)；(PresheafOfModules.ModuleColimit.homEquiv' hcR hcM).symm β；(Ca
tegoryTheory.ConcreteCategory.hom (cM.ι.app X)) x；CategoryTheory.ConcreteCategor
y.hom (β.app X)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.Limits.IsColimit.ι_app_homEquiv_symm`：∀ {J : Type u₁} [in
st : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.
Category.{v₃, u₃} C]   {F : CategoryTheor…
-/
lemma homEquiv'_symm_apply {N : ModuleCat.{w} cR.pt}
    (β : M.presheaf ⟶ (Functor.const _).obj (.of N)) {X : Cᵒᵖ} (x : M.obj X) :
    (homEquiv' hcR hcM).symm β (cM.ι.app X x) = β.app X x :=
  ConcreteCategory.congr_hom (hcM.ι_app_homEquiv_symm β X) x

set_option backward.isDefEq.respectTransparency.types false in
/-
**PresheafOfModules.ModuleColimit.map_smul_homEquiv'_iff** 是 Mathlib 中的一个定理，位于命名
空间 `PresheafOfModules.ModuleColimit`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.LocallySmall.{w, v, u} C]   [inst_2 : CategoryTheory.IsCofiltered C] [in
st_3 : CategoryTheory.InitiallySmall C]   {R : CategoryTheory.Functor Cᵒᵖ RingCa
t} {cR : CategoryTheory.Limits.Cocone R}   (hcR : CategoryTheory.Limits.IsColimi
t cR) {M : PresheafOfModules R} {cM : CategoryTheory.Limits.Cocone M.presheaf}  
 (hcM : CategoryTheory.Limits.IsColimit cM) {N : ModuleCat ↑cR.pt} (α : Presheaf
OfModules.ModuleColimit hcR hcM →+ ↑N),   (∀ (U : Cᵒᵖ) (r : ↑(R.obj U)) (m : ↑(M
.obj U)),       (CategoryTheory.ConcreteCategory.hom (((PresheafOfModules.Module
Colimit.homEquiv' hcR hcM) α).app U)) (r • m) =         (CategoryTheory.Concrete
Category.hom (cR.ι.app U)) r •           (CategoryTheory.ConcreteCategory.hom ((
(PresheafOfModules.ModuleColimit.homEquiv' hcR hcM) α).app U)) m) ↔     ∀ (r : ↑
cR.pt) (m : PresheafOfModules.ModuleColimit hcR hcM), α (r • m) = r • α m
参数：hcR : CategoryTheory.Limits.IsColimit cR；hcM : CategoryTheory.Limits.IsColimi
t cM；α : PresheafOfModules.ModuleColimit hcR hcM →+ ↑N；∀ (U : Cᵒᵖ) (r : ↑(R.obj 
U)) (m : ↑(M.obj U)),       (CategoryTheory.ConcreteCategory.hom (((PresheafOfMo
dules.ModuleColimit.homEquiv' hcR hcM) α).app U)) (r • m) =         (CategoryThe
ory.ConcreteCategory.hom (cR.ι.app U)) r •           (CategoryTheory.ConcreteCat
egory.hom (((PresheafOfModules.ModuleColimit.homEquiv' hcR hcM) α).app U)) m；r :
 ↑cR.pt；m : PresheafOfModules.ModuleColimit hcR hcM；r • m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PresheafOfModules.ModuleColimit.jointly_surjective₂`：jointly_surjective₂
 (r : cR.pt) (m : ModuleColimit hcR hcM) : exists (U : Cᵒᵖ) (a : R.obj U) (x : M
.obj U), ιR cR a = r ∧ ιM x = m
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用引理 `PresheafOfModules.ModuleColimit.smul_eq`：smul_eq {U : Cᵒᵖ} (r : R.obj U)
 (m : M.obj U) : ιR cR r • ιM (hcR
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PresheafOfModules.ModuleColimit.homEquiv'_app_apply`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {R : CategoryTheory.Functor Cᵒᵖ RingCat}  
 {cR : CategoryTheory.Limits.Cocone R} (h…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma map_smul_homEquiv'_iff {N : ModuleCat.{w} cR.pt}
    (α : ModuleColimit hcR hcM →+ N) :
    dsimp% (∀ (U : Cᵒᵖ) (r : R.obj U) (m : M.obj U), (homEquiv' hcR hcM α).app U (r • m) =
        letI m' : N := (homEquiv' hcR hcM α).app U m; letI r' : cR.pt := cR.ι.app U r
        r' • m') ↔
    ∀ (r : cR.pt) (m : ModuleColimit hcR hcM), α (r • m) = r • α m := by
  refine ⟨fun h r m ↦ ?_, fun h U r m ↦ ?_⟩
  · obtain ⟨U, r, m, rfl, rfl⟩ := jointly_surjective₂ r m
    refine Eq.trans ?_ ((homEquiv'_app_apply ..).symm.trans (h U r m))
    congr 1
    apply smul_eq
  · rw [homEquiv'_app_apply, homEquiv'_app_apply, ← h]
    congr 1
    exact (smul_eq ..).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- This is the universal property of `PresheafOfModules.ModuleColimit` as a module.
See also `PresheafOfModules.colimitAdjunction`. -/
/-
**PresheafOfModules.ModuleColimit.homEquiv** 是 Mathlib 中的一个定义，位于命名空间 `PresheafOf
Modules.ModuleColimit`。
形式化陈述：homEquiv {N : ModuleCat.{w} cR.pt} : (ModuleCat.of cR.pt (ModuleColimit hc
R hcM) ⟶ N) ≃+ (M ⟶ (constFunctor cR).obj N) where toFun φ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the universal property of `PresheafOfModules.ModuleColimit` as a module.
See also `PresheafOfModules.colimitAdjunction`.
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
        refine (map_smul_homEquiv'_iff hcR hcM φ).1 (fun U r m ↦ ?_)
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
/-
**PresheafOfModules.ModuleColimit.homEquiv_app_apply** 是 Mathlib 中的一个引理，位于命名空间 `
PresheafOfModules.ModuleColimit`。
形式化陈述：homEquiv_app_apply {N : ModuleCat.{w} cR.pt} (α : ModuleCat.of cR.pt (Modu
leColimit hcR hcM) ⟶ N) {X : Cᵒᵖ} (x : M.obj X) : dsimp% (homEquiv hcR hcM α).ap
p X x = α (cM.ι.app X x)
参数：α : ModuleCat.of cR.pt (ModuleColimit hcR hcM) ⟶ N；x : M.obj X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homEquiv_app_apply {N : ModuleCat.{w} cR.pt}
    (α : ModuleCat.of cR.pt (ModuleColimit hcR hcM) ⟶ N) {X : Cᵒᵖ} (x : M.obj X) :
    dsimp% (homEquiv hcR hcM α).app X x = α (cM.ι.app X x) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**PresheafOfModules.ModuleColimit.homEquiv_naturality_right** 是 Mathlib 中的一个引理，位
于命名空间 `PresheafOfModules.ModuleColimit`。
形式化陈述：homEquiv_naturality_right {N N' : ModuleCat.{w} cR.pt} (φ : ModuleCat.of c
R.pt (ModuleColimit hcR hcM) ⟶ N) (g : N ⟶ N') : homEquiv hcR hcM (φ ≫ g) = homE
quiv hcR hcM φ ≫ (constFunctor cR).map g
参数：φ : ModuleCat.of cR.pt (ModuleColimit hcR hcM) ⟶ N；g : N ⟶ N'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homEquiv_naturality_right {N N' : ModuleCat.{w} cR.pt}
    (φ : ModuleCat.of cR.pt (ModuleColimit hcR hcM) ⟶ N) (g : N ⟶ N') :
    homEquiv hcR hcM (φ ≫ g) = homEquiv hcR hcM φ ≫ (constFunctor cR).map g := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**PresheafOfModules.ModuleColimit.homEquiv_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 
`PresheafOfModules.ModuleColimit`。
形式化陈述：homEquiv_symm_apply {N : ModuleCat.{w} cR.pt} (β : M ⟶ (constFunctor cR).o
bj N) {X : Cᵒᵖ} (x : M.obj X) : dsimp% (homEquiv hcR hcM).symm β (cM.ι.app X x) 
= β.app X x
参数：β : M ⟶ (constFunctor cR).obj N；x : M.obj X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PresheafOfModules.ModuleColimit.homEquiv'_symm_apply`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {R : CategoryTheory.Functor Cᵒᵖ RingCat} 
  {cR : CategoryTheory.Limits.Cocone R} (h…
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
/-- The linear map between the colimit modules induced by a morphism of modules. -/
/-
**PresheafOfModules.ModuleColimit.map** 是 Mathlib 中的一个定义，位于命名空间 `PresheafOfModul
es.ModuleColimit`。
形式化陈述：map (f : M ⟶ M') : ModuleColimit hcR hcM ->ₗ[cR.pt] ModuleColimit hcR hcM'
 where toFun
参数：f : M ⟶ M'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear map between the colimit modules induced by a morphism of modules.
-/
noncomputable def map (f : M ⟶ M') :
    ModuleColimit hcR hcM →ₗ[cR.pt] ModuleColimit hcR hcM' where
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
/-
**PresheafOfModules.ModuleColimit.map_apply** 是 Mathlib 中的一个引理，位于命名空间 `PresheafO
fModules.ModuleColimit`。
形式化陈述：map_apply (f : M ⟶ M') {U : Cᵒᵖ} (m : M.obj U) : dsimp% map hcR hcM hcM' f
 (ιM m) = ιM (f.app _ m)
参数：f : M ⟶ M'；m : M.obj U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.Limits.IsColimit.fac`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃
} C]   {F : CategoryTheor…
-/
lemma map_apply (f : M ⟶ M') {U : Cᵒᵖ} (m : M.obj U) :
    dsimp% map hcR hcM hcM' f (ιM m) = ιM (f.app _ m) :=
  ConcreteCategory.congr_hom (hcM.fac ((Cocone.precompose ((toPresheaf _).map f)).obj cM') U) m

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**PresheafOfModules.ModuleColimit.map_id** 是 Mathlib 中的一个引理，位于命名空间 `PresheafOfMo
dules.ModuleColimit`。
形式化陈述：map_id : map hcR hcM hcM (𝟙 M) = .id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用引理 `PresheafOfModules.ModuleColimit.ιM_jointly_surjective`：ιM_jointly_surjec
tive (m : ModuleColimit hcR hcM) : exists (U : Cᵒᵖ) (x : M.obj U), ιM x = m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PresheafOfModules.ModuleColimit.map_apply`：map_apply (f : M ⟶ M') {U : C
ᵒᵖ} (m : M.obj U) : dsimp% map hcR hcM hcM' f (ιM m) = ιM (f.app _ m)
· 使用引理 `PresheafOfModules.id_app`：id_app (M : PresheafOfModules R) (X : Cᵒᵖ) : H
om.app (𝟙 M) X = 𝟙 _
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_id : map hcR hcM hcM (𝟙 M) = .id := by
  ext m
  obtain ⟨U, m, rfl⟩ := ιM_jointly_surjective m
  simp

set_option backward.isDefEq.respectTransparency.types false in
/-
**PresheafOfModules.ModuleColimit.comp_map** 是 Mathlib 中的一个引理，位于命名空间 `PresheafOf
Modules.ModuleColimit`。
形式化陈述：comp_map (f : M ⟶ M') {M'' : PresheafOfModules.{w} R} {cM'' : Cocone M''.p
resheaf} (hcM'' : IsColimit cM'') (g : M' ⟶ M'') : (map hcR hcM' hcM'' g).comp (
map hcR hcM hcM' f) = map hcR hcM hcM'' (f ≫ g)
参数：f : M ⟶ M'；hcM'' : IsColimit cM''；g : M' ⟶ M''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用引理 `PresheafOfModules.ModuleColimit.ιM_jointly_surjective`：ιM_jointly_surjec
tive (m : ModuleColimit hcR hcM) : exists (U : Cᵒᵖ) (x : M.obj U), ιM x = m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PresheafOfModules.ModuleColimit.map_apply`：map_apply (f : M ⟶ M') {U : C
ᵒᵖ} (m : M.obj U) : dsimp% map hcR hcM hcM' f (ιM m) = ιM (f.app _ m)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `PresheafOfModules.comp_app`：comp_app {M₁ M₂ M₃ : PresheafOfModules R} (f
 : M₁ ⟶ M₂) (g : M₂ ⟶ M₃) (X : Cᵒᵖ) : (f ≫ g).app X = f.app X ≫ g.app X
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
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
/-
**PresheafOfModules.ModuleColimit.homEquiv_naturality_left** 是 Mathlib 中的一个引理，位于
命名空间 `PresheafOfModules.ModuleColimit`。
形式化陈述：homEquiv_naturality_left {M' : PresheafOfModules.{w} R} {cM' : Cocone M'.p
resheaf} (hcM' : IsColimit cM') {N : ModuleCat.{w} cR.pt} (φ' : ModuleCat.of cR.
pt (ModuleColimit hcR hcM') ⟶ N) (f : M ⟶ M') : homEquiv hcR hcM (ModuleCat.ofHo
m (map hcR hcM hcM' f) ≫ φ') = f ≫ homEquiv hcR hcM' φ'
参数：hcM' : IsColimit cM'；φ' : ModuleCat.of cR.pt (ModuleColimit hcR hcM') ⟶ N；f :
 M ⟶ M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PresheafOfModules.hom_ext`：hom_ext {f g : M₁ ⟶ M₂} (h : forall (X : Cᵒᵖ)
, f.app X = g.app X) : f = g
· 使用引理 `ModuleCat.hom_ext`：hom_ext {M N : ModuleCat.{v} R} {f g : M ⟶ N} (hf : f
.hom = g.hom) : f = g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `PresheafOfModules.comp_app`：comp_app {M₁ M₂ M₃ : PresheafOfModules R} (f
 : M₁ ⟶ M₂) (g : M₂ ⟶ M₃) (X : Cᵒᵖ) : (f ≫ g).app X = f.app X ≫ g.app X
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `PresheafOfModules.ModuleColimit.map_apply`：map_apply (f : M ⟶ M') {U : C
ᵒᵖ} (m : M.obj U) : dsimp% map hcR hcM hcM' f (ιM m) = ιM (f.app _ m)
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
/-
**PresheafOfModules.ModuleColimit.homEquiv_naturality_left_symm** 是 Mathlib 中的一个
引理，位于命名空间 `PresheafOfModules.ModuleColimit`。
形式化陈述：homEquiv_naturality_left_symm {M' : PresheafOfModules.{w} R} {cM' : Cocone
 M'.presheaf} (hcM' : IsColimit cM') {N : ModuleCat.{w} cR.pt} (f : M ⟶ M') (g :
 M' ⟶ (constFunctor cR).obj N) : (homEquiv hcR hcM).symm (f ≫ g) = ModuleCat.ofH
om (map hcR hcM hcM' f) ≫ (homEquiv hcR hcM').symm g
参数：hcM' : IsColimit cM'；f : M ⟶ M'；g : M' ⟶ (constFunctor cR).obj N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst
_1 : Add N] (e : M ≃+ N), Function.Injective ⇑e
· 使用定理 `AddEquiv.surjective`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [ins
t_1 : Add N] (e : M ≃+ N), Function.Surjective ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddEquiv.apply_symm_apply`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M
] [inst_1 : Add N] (e : M ≃+ N) (y : N), e (e.symm y) = y
· 使用定理 `AddEquiv.symm_apply_apply`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M
] [inst_1 : Add N] (e : M ≃+ N) (x : M), e.symm (e x) = x
· 使用引理 `PresheafOfModules.ModuleColimit.homEquiv_naturality_left`：homEquiv_natur
ality_left {M' : PresheafOfModules.{w} R} {cM' : Cocone M'.presheaf} (hcM' : IsC
olimit cM') {N : ModuleCat.{w} cR.pt} (φ' : Mo…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
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
/-- The colimit module functor from the category of presheaves of modules
over a presheaf of rings `R` on a cofiltered category to the category
of modules over a colimit of `R`. -/
/-
**PresheafOfModules.colimitFunctor** 是 Mathlib 中的一个定义，位于命名空间 `PresheafOfModules`
。
形式化陈述：colimitFunctor : PresheafOfModules.{w} R ⥤ ModuleCat.{w} cR.pt where obj M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The colimit module functor from the category of presheaves of modules
over a presheaf of rings `R` on a cofiltered category to the category
of modules over a colimit of `R`.
-/
noncomputable def colimitFunctor : PresheafOfModules.{w} R ⥤ ModuleCat.{w} cR.pt where
  obj M := ModuleCat.of _ (ModuleColimit hcR (colimit.isColimit M.presheaf))
  map f := ModuleCat.ofHom (ModuleColimit.map _ _ _ f)
  map_comp f g := by ext : 1; exact (ModuleColimit.comp_map ..).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- Given a presheaf of rings `R` on a cofiltered category, this is the
adjunction between `colimitFunctor : PresheafOfModules R ⥤ ModuleCat cR.pt`
and the constant functor. -/
/-
**PresheafOfModules.colimitAdjunction** 是 Mathlib 中的一个定义，位于命名空间 `PresheafOfModul
es`。
形式化陈述：colimitAdjunction : colimitFunctor.{w} hcR ⊣ constFunctor.{w} cR
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a presheaf of rings `R` on a cofiltered category, this is the
adjunction between `colimitFunctor : PresheafOfModules R ⥤ ModuleCat cR.pt`
and the constant functor.
-/
noncomputable def colimitAdjunction :
    colimitFunctor.{w} hcR ⊣ constFunctor.{w} cR :=
  Adjunction.mkOfHomEquiv
    { homEquiv _ _ := (ModuleColimit.homEquiv _ _).toEquiv
      homEquiv_naturality_left_symm _ _ := ModuleColimit.homEquiv_naturality_left_symm _ _ _ _ _
      homEquiv_naturality_right _ _ := ModuleColimit.homEquiv_naturality_right _ _ _ _ }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**PresheafOfModules.colimitAdjunction_homEquiv** 是 Mathlib 中的一个引理，位于命名空间 `Preshe
afOfModules`。
形式化陈述：colimitAdjunction_homEquiv (F : PresheafOfModules R) (G : ModuleCat cR.pt)
 : dsimp% (colimitAdjunction.{w} hcR).homEquiv F G = (ModuleColimit.homEquiv hcR
 (colimit.isColimit F.presheaf)).toEquiv
参数：F : PresheafOfModules R；G : ModuleCat cR.pt。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_finallySmall`：hasColimitsOfS
hape_of_finallySmall (J : Type u) [Category.{v} J] [FinallySmall.{w} J] (C : Typ
e u₁) [Category.{v₁} C] [HasColimitsOfSize.{w,…
· 使用定理 `CategoryTheory.instFinallySmallOppositeOfInitiallySmall`：∀ {J : Type u} 
[inst : CategoryTheory.Category.{v, u} J] [CategoryTheory.InitiallySmall J],   C
ategoryTheory.FinallySmall Jᵒᵖ
· 使用定理 `AddCommGrpCat.hasColimitsOfSize`：∀ [UnivLE.{u, w}], CategoryTheory.Limit
s.HasColimitsOfSize.{v, u, w, w + 1} AddCommGrpCat
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `CategoryTheory.Adjunction.mkOfHomEquiv_homEquiv`：mkOfHomEquiv_homEquiv (
adj : CoreHomEquiv F G) : (mkOfHomEquiv adj).homEquiv = adj.homEquiv
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma colimitAdjunction_homEquiv
    (F : PresheafOfModules R) (G : ModuleCat cR.pt) :
    dsimp% (colimitAdjunction.{w} hcR).homEquiv F G =
      (ModuleColimit.homEquiv hcR
        (colimit.isColimit F.presheaf)).toEquiv := by
  simp [colimitAdjunction]

set_option backward.isDefEq.respectTransparency.types false in
open ModuleColimit in
/-
**PresheafOfModules.colimitAdjunction_homEquiv_symm_apply** 是 Mathlib 中的一个引理，位于命
名空间 `PresheafOfModules`。
形式化陈述：colimitAdjunction_homEquiv_symm_apply {F : PresheafOfModules R} {G : Modul
eCat cR.pt} (β : F ⟶ (constFunctor cR).obj G) {X : Cᵒᵖ} (m : F.obj X) : ((colimi
tAdjunction.{w} hcR).homEquiv F G).symm β (ModuleColimit.ιM (hcR
参数：β : F ⟶ (constFunctor cR).obj G；m : F.obj X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.Limits.hasColimitsOfShape_of_finallySmall`：hasColimitsOfS
hape_of_finallySmall (J : Type u) [Category.{v} J] [FinallySmall.{w} J] (C : Typ
e u₁) [Category.{v₁} C] [HasColimitsOfSize.{w,…
· 使用定理 `CategoryTheory.instFinallySmallOppositeOfInitiallySmall`：∀ {J : Type u} 
[inst : CategoryTheory.Category.{v, u} J] [CategoryTheory.InitiallySmall J],   C
ategoryTheory.FinallySmall Jᵒᵖ
· 使用定理 `AddCommGrpCat.hasColimitsOfSize`：∀ [UnivLE.{u, w}], CategoryTheory.Limit
s.HasColimitsOfSize.{v, u, w, w + 1} AddCommGrpCat
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PresheafOfModules.colimitAdjunction_homEquiv`：colimitAdjunction_homEquiv
 (F : PresheafOfModules R) (G : ModuleCat cR.pt) : dsimp% (colimitAdjunction.{w}
 hcR).homEquiv F G = (ModuleColimi…
· 使用引理 `PresheafOfModules.ModuleColimit.homEquiv_symm_apply`：homEquiv_symm_apply
 {N : ModuleCat.{w} cR.pt} (β : M ⟶ (constFunctor cR).obj N) {X : Cᵒᵖ} (x : M.ob
j X) : dsimp% (homEquiv hcR hcM).symm β (…
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

