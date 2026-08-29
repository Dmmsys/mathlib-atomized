/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ConcreteCategory
public import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
# Homology and exactness of short complexes of modules

In this file, the homology of a short complex `S` of abelian groups is identified
with the quotient of `LinearMap.ker S.g` by the image of the morphism
`S.moduleCatToCycles : S.X₁ →ₗ[R] LinearMap.ker S.g` induced by `S.f`.

-/

@[expose] public section

universe v u

variable {R : Type u} [Ring R]

namespace CategoryTheory

open Limits

namespace ShortComplex

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget₂ (ModuleCat.{v} R) Ab).PreservesHomology

中文:
实例 :
  签名: (forget₂ (模范畴.{v} R) Ab).保持同调
-/
noncomputable instance : (forget₂ (ModuleCat.{v} R) Ab).PreservesHomology where

/-- Constructor for short complexes in `ModuleCat.{v} R` taking as inputs
linear maps `f` and `g` and the vanishing of their composition. -/
@[simps]
/--
Definition of `moduleCatMk` / `moduleCatMk` 的定义

English:
definition moduleCatMk
  signature: {X₁ X₂ X₃ : Type v} [AddCommGroup X₁] [AddCommGroup X₂] [AddCommGroup X₃]
  body: ShortComplex.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g) (ModuleCat.hom_ext hfg)

中文:
定义 moduleCatMk
  签名: {X₁ X₂ X₃ : 类型v} [加法交换群 X₁] [加法交换群 X₂] [加法交换群 X₃]
  定义体: ShortComplex.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g) (ModuleCat.hom_ext hfg)

Depends on / 依赖: ModuleCat, ModuleCat.hom_ext, ModuleCat.ofHom, ShortComplex, ShortComplex.mk, hom_ext
-/
def moduleCatMk {X₁ X₂ X₃ : Type v} [AddCommGroup X₁] [AddCommGroup X₂] [AddCommGroup X₃]
    [Module R X₁] [Module R X₂] [Module R X₃] (f : X₁ ->ₗ[R] X₂) (g : X₂ ->ₗ[R] X₃)
    (hfg : g.comp f = 0) : ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g) (ModuleCat.hom_ext hfg)

variable (S : ShortComplex (ModuleCat.{v} R))

@[simp]
/--
lemma `moduleCat_zero_apply` / 引理 `moduleCat_zero_apply`

English:
lemma moduleCat_zero_apply
  given: (x : S.X₁)
  statement: S.g (S.f x) = 0
  proof: S.zero_apply x

中文:
引理 moduleCat_zero_apply
  条件: (x : S.X₁)
  结论: S.g (S.f x) = 0
  证明: S.zero_apply x

Depends on / 依赖: S.zero_apply, zero_apply
-/
lemma moduleCat_zero_apply (x : S.X₁) : S.g (S.f x) = 0 :=
  S.zero_apply x

/--
lemma `moduleCat_exact_iff` / 引理 `moduleCat_exact_iff`

English:
lemma moduleCat_exact_iff
  proof: S.exact_iff_of_hasForget

中文:
引理 moduleCat_exact_iff
  证明: S.exact_iff_of_hasForget

Depends on / 依赖: S.exact_iff_of_hasForget, exact_iff_of_hasForget
-/
lemma moduleCat_exact_iff :
    S.Exact ↔ forall (x₂ : S.X₂) (_ : S.g x₂ = 0), exists (x₁ : S.X₁), S.f x₁ = x₂ :=
  S.exact_iff_of_hasForget

/--
lemma `moduleCat_exact_iff_ker_sub_range` / 引理 `moduleCat_exact_iff_ker_sub_range`

English:
lemma moduleCat_exact_iff_ker_sub_range
  proof: by
  rw [moduleCat_exact_iff]
  aesop

中文:
引理 moduleCat_exact_iff_ker_sub_range
  证明: by
  rw [moduleCat_exact_iff]
  aesop

Depends on / 依赖: moduleCat_exact_iff
-/
lemma moduleCat_exact_iff_ker_sub_range :
    S.Exact ↔ LinearMap.ker S.g.hom <= LinearMap.range S.f.hom := by
  rw [moduleCat_exact_iff]
  aesop

/--
lemma `moduleCat_exact_iff_range_eq_ker` / 引理 `moduleCat_exact_iff_range_eq_ker`

English:
lemma moduleCat_exact_iff_range_eq_ker
  proof: by
  rw [moduleCat_exact_iff_ker_sub_range]
  aesop

中文:
引理 moduleCat_exact_iff_range_eq_ker
  证明: by
  rw [moduleCat_exact_iff_ker_sub_range]
  aesop

Depends on / 依赖: moduleCat_exact_iff_ker_sub_range
-/
lemma moduleCat_exact_iff_range_eq_ker :
    S.Exact ↔ LinearMap.range S.f.hom = LinearMap.ker S.g.hom := by
  rw [moduleCat_exact_iff_ker_sub_range]
  aesop

variable {S}

/--
lemma `Exact.moduleCat_range_eq_ker` / 引理 `Exact.moduleCat_range_eq_ker`

English:
lemma Exact.moduleCat_range_eq_ker
  given: (hS : S.Exact)
  proof: by
  simpa only [moduleCat_exact_iff_range_eq_ker] using hS

中文:
引理 正合.moduleCat_range_eq_ker
  条件: (hS : S.正合)
  证明: by
  simpa only [moduleCat_exact_iff_range_eq_ker] using hS

Depends on / 依赖: moduleCat_exact_iff_range_eq_ker
-/
lemma Exact.moduleCat_range_eq_ker (hS : S.Exact) :
    LinearMap.range S.f.hom = LinearMap.ker S.g.hom := by
  simpa only [moduleCat_exact_iff_range_eq_ker] using hS

/--
lemma `ShortExact.moduleCat_injective_f` / 引理 `ShortExact.moduleCat_injective_f`

English:
lemma ShortExact.moduleCat_injective_f
  given: (hS : S.ShortExact)
  proof: hS.injective_f

中文:
引理 短正合.moduleCat_injective_f
  条件: (hS : S.短正合)
  证明: hS.injective_f

Depends on / 依赖: hS.injective_f, injective_f
-/
lemma ShortExact.moduleCat_injective_f (hS : S.ShortExact) :
    Function.Injective S.f :=
  hS.injective_f

/--
lemma `ShortExact.moduleCat_surjective_g` / 引理 `ShortExact.moduleCat_surjective_g`

English:
lemma ShortExact.moduleCat_surjective_g
  given: (hS : S.ShortExact)
  proof: hS.surjective_g

中文:
引理 短正合.moduleCat_surjective_g
  条件: (hS : S.短正合)
  证明: hS.surjective_g

Depends on / 依赖: hS.surjective_g, surjective_g
-/
lemma ShortExact.moduleCat_surjective_g (hS : S.ShortExact) :
    Function.Surjective S.g :=
  hS.surjective_g

variable (S)

/--
lemma `ShortExact.moduleCat_exact_iff_function_exact` / 引理 `ShortExact.moduleCat_exact_iff_function_exact`

English:
lemma ShortExact.moduleCat_exact_iff_function_exact
  proof: by
  rw [moduleCat_exact_iff_range_eq_ker]; rw [LinearMap.exact_iff]
  tauto

中文:
引理 短正合.moduleCat_exact_iff_function_exact
  证明: by
  rw [moduleCat_exact_iff_range_eq_ker]; rw [LinearMap.exact_iff]
  tauto

Depends on / 依赖: LinearMap, LinearMap.exact_iff, exact_iff, moduleCat_exact_iff_range_eq_ker
-/
lemma ShortExact.moduleCat_exact_iff_function_exact :
    S.Exact ↔ Function.Exact S.f S.g := by
  rw [moduleCat_exact_iff_range_eq_ker]; rw [LinearMap.exact_iff]
  tauto

/-- Constructor for short complexes in `ModuleCat.{v} R` taking as inputs
morphisms `f` and `g` and the assumption `LinearMap.range f ≤ LinearMap.ker g`. -/
@[simps]
/--
Definition of `moduleCatMkOfKerLERange` / `moduleCatMkOfKerLERange` 的定义

English:
definition moduleCatMkOfKerLERange
  signature: {X₁ X₂ X₃ : ModuleCat.{v} R} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)
  body: ShortComplex.mk f g (by aesop)

中文:
定义 moduleCatMkOfKerLERange
  签名: {X₁ X₂ X₃ : 模范畴.{v} R} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)
  定义体: ShortComplex.mk f g (by aesop)

Depends on / 依赖: ShortComplex, ShortComplex.mk
-/
def moduleCatMkOfKerLERange {X₁ X₂ X₃ : ModuleCat.{v} R} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)
    (hfg : LinearMap.range f.hom <= LinearMap.ker g.hom) : ShortComplex (ModuleCat.{v} R) :=
  ShortComplex.mk f g (by aesop)

/--
lemma `Exact.moduleCat_of_range_eq_ker` / 引理 `Exact.moduleCat_of_range_eq_ker`

English:
lemma Exact.moduleCat_of_range_eq_ker
  statement: {X₁ X₂ X₃ : ModuleCat.{v} R}
  proof: by
  simpa only [moduleCat_exact_iff_range_eq_ker] using! hfg

中文:
引理 正合.moduleCat_of_range_eq_ker
  结论: {X₁ X₂ X₃ : 模范畴.{v} R}
  证明: by
  simpa only [moduleCat_exact_iff_range_eq_ker] using! hfg

Depends on / 依赖: moduleCat_exact_iff_range_eq_ker
-/
lemma Exact.moduleCat_of_range_eq_ker {X₁ X₂ X₃ : ModuleCat.{v} R}
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (hfg : LinearMap.range f.hom = LinearMap.ker g.hom) :
    (moduleCatMkOfKerLERange f g (by rw [hfg])).Exact := by
  simpa only [moduleCat_exact_iff_range_eq_ker] using! hfg

/--
Definition of `moduleCatToCycles` / `moduleCatToCycles` 的定义

English:
abbreviation moduleCatToCycles
  signature: : S.X₁ ->ₗ[R] LinearMap.ker S.g.hom
  body: S.f.hom.codRestrict _ S.moduleCat_zero_apply

中文:
缩写 moduleCatToCycles
  签名: : S.X₁ ->ₗ[R] 线性映射.ker S.g.hom
  定义体: S.f.hom.codRestrict _ S.moduleCat_zero_apply

Depends on / 依赖: S.f.hom.codRestrict, S.moduleCat_zero_apply, codRestrict, moduleCat_zero_apply
-/
abbrev moduleCatToCycles : S.X₁ ->ₗ[R] LinearMap.ker S.g.hom :=
S.f.hom.codRestrict _ S.moduleCat_zero_apply

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The explicit left homology data of a short complex of modules that is
given by a kernel and a quotient given by the `LinearMap` API. The projections to `K` and `H` are
not simp lemmas because the generic lemmas about `LeftHomologyData` are more useful here. -/
@[simps! K H i_hom π_hom]
/--
Definition of `moduleCatLeftHomologyData` / `moduleCatLeftHomologyData` 的定义

English:
definition moduleCatLeftHomologyData
  signature: : S.LeftHomologyData where
  body: ModuleCat.of R (LinearMap.ker S.g.hom)
  H := ModuleCat.of R (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles)
  i := ModuleCat.ofHom (LinearMap.ker S.g.hom).subtype
  π := ModuleCat.ofHom (LinearMap.range S.moduleCatToCycles).mkQ
  wi := by aesop
  hi := ModuleCat.kernelIsLimit _
  wπ :

中文:
定义 moduleCatLeftHomologyData
  签名: : S.LeftHomologyData where
  定义体: ModuleCat.of R (LinearMap.ker S.g.hom)
  H := ModuleCat.of R (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles)
  i := ModuleCat.ofHom (LinearMap.ker S.g.hom).subtype
  π := ModuleCat.ofHom (LinearMap.range S.moduleCatToCycles).mkQ
  wi := by aesop
  hi := ModuleCat.kernelIsLimit _
  wπ :

Depends on / 依赖: LinearMap, LinearMap.ker, ModuleCat, ModuleCat.of, S.g.hom
-/
def moduleCatLeftHomologyData : S.LeftHomologyData where
  K := ModuleCat.of R (LinearMap.ker S.g.hom)
  H := ModuleCat.of R (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles)
  i := ModuleCat.ofHom (LinearMap.ker S.g.hom).subtype
  π := ModuleCat.ofHom (LinearMap.range S.moduleCatToCycles).mkQ
  wi := by aesop
  hi := ModuleCat.kernelIsLimit _
  wπ := by aesop
  hπ := ModuleCat.cokernelIsColimit (ModuleCat.ofHom S.moduleCatToCycles)

@[simp]
/--
lemma `moduleCatLeftHomologyData_f'_hom` / 引理 `moduleCatLeftHomologyData_f'_hom`

English:
lemma moduleCatLeftHomologyData_f'_hom
  proof: rfl

@[simp]

中文:
引理 moduleCatLeftHomologyData_f'_hom
  证明: rfl

@[simp]
-/
lemma moduleCatLeftHomologyData_f'_hom :
    S.moduleCatLeftHomologyData.f'.hom = S.moduleCatToCycles := rfl

@[simp]
/--
lemma `moduleCatLeftHomologyData_descH_hom` / 引理 `moduleCatLeftHomologyData_descH_hom`

English:
lemma moduleCatLeftHomologyData_descH_hom
  statement: {M : ModuleCat R}
  proof: rfl

@[simp]

中文:
引理 moduleCatLeftHomologyData_descH_hom
  结论: {M : 模范畴 R}
  证明: rfl

@[simp]
-/
lemma moduleCatLeftHomologyData_descH_hom {M : ModuleCat R}
    (φ : S.moduleCatLeftHomologyData.K ⟶ M) (h : S.moduleCatLeftHomologyData.f' ≫ φ = 0) :
    (S.moduleCatLeftHomologyData.descH φ h).hom =
      (LinearMap.range <| ModuleCat.Hom.hom _).liftQ
         φ.hom (LinearMap.range_le_ker_iff.2 <| ModuleCat.hom_ext_iff.1 h) := rfl

@[simp]
/--
lemma `moduleCatLeftHomologyData_liftK_hom` / 引理 `moduleCatLeftHomologyData_liftK_hom`

English:
lemma moduleCatLeftHomologyData_liftK_hom
  given: {M : ModuleCat R} (φ : M ⟶ S.X₂) (h : φ ≫ S.g = 0)
  proof: rfl

中文:
引理 moduleCatLeftHomologyData_liftK_hom
  条件: {M : 模范畴 R} (φ : M ⟶ S.X₂) (h : φ ≫ S.g = 0)
  证明: rfl
-/
lemma moduleCatLeftHomologyData_liftK_hom {M : ModuleCat R} (φ : M ⟶ S.X₂) (h : φ ≫ S.g = 0) :
    (S.moduleCatLeftHomologyData.liftK φ h).hom =
      φ.hom.codRestrict (LinearMap.ker S.g.hom) (fun m => congr($h m)) := rfl

/--
Definition of `moduleCatCyclesIso` / `moduleCatCyclesIso` 的定义

English:
definition moduleCatCyclesIso
  signature: : S.cycles ≅ S.moduleCatLeftHomologyData.K
  body: S.moduleCatLeftHomologyData.cyclesIso

@[reassoc (attr := simp, elementwise)]

中文:
定义 moduleCatCyclesIso
  签名: : S.cycles ≅ S.moduleCatLeftHomologyData.K
  定义体: S.moduleCatLeftHomologyData.cyclesIso

@[reassoc (attr := simp, elementwise)]

Depends on / 依赖: S.moduleCatLeftHomologyData.cyclesIso, cyclesIso, moduleCatLeftHomologyData
-/
noncomputable def moduleCatCyclesIso : S.cycles ≅ S.moduleCatLeftHomologyData.K :=
  S.moduleCatLeftHomologyData.cyclesIso

@[reassoc (attr := simp, elementwise)]
/--
lemma `moduleCatCyclesIso_hom_i` / 引理 `moduleCatCyclesIso_hom_i`

English:
lemma moduleCatCyclesIso_hom_i
  proof: S.moduleCatLeftHomologyData.cyclesIso_hom_comp_i

@[reassoc (attr := simp, elementwise)]

中文:
引理 moduleCatCyclesIso_hom_i
  证明: S.moduleCatLeftHomologyData.cyclesIso_hom_comp_i

@[reassoc (attr := simp, elementwise)]

Depends on / 依赖: S.moduleCatLeftHomologyData.cyclesIso_hom_comp_i, cyclesIso_hom_comp_i, moduleCatLeftHomologyData
-/
lemma moduleCatCyclesIso_hom_i :
    S.moduleCatCyclesIso.hom ≫ S.moduleCatLeftHomologyData.i = S.iCycles :=
  S.moduleCatLeftHomologyData.cyclesIso_hom_comp_i

@[reassoc (attr := simp, elementwise)]
/--
lemma `moduleCatCyclesIso_inv_iCycles` / 引理 `moduleCatCyclesIso_inv_iCycles`

English:
lemma moduleCatCyclesIso_inv_iCycles
  proof: S.moduleCatLeftHomologyData.cyclesIso_inv_comp_iCycles

@[reassoc (attr := simp, elementwise)]

中文:
引理 moduleCatCyclesIso_inv_iCycles
  证明: S.moduleCatLeftHomologyData.cyclesIso_inv_comp_iCycles

@[reassoc (attr := simp, elementwise)]

Depends on / 依赖: S.moduleCatLeftHomologyData.cyclesIso_inv_comp_iCycles, cyclesIso_inv_comp_iCycles, moduleCatLeftHomologyData
-/
lemma moduleCatCyclesIso_inv_iCycles :
    S.moduleCatCyclesIso.inv ≫ S.iCycles = S.moduleCatLeftHomologyData.i :=
  S.moduleCatLeftHomologyData.cyclesIso_inv_comp_iCycles

@[reassoc (attr := simp, elementwise)]
/--
lemma `toCycles_moduleCatCyclesIso_hom` / 引理 `toCycles_moduleCatCyclesIso_hom`

English:
lemma toCycles_moduleCatCyclesIso_hom
  proof: by
  simp [← cancel_mono S.moduleCatLeftHomologyData.i]

中文:
引理 toCycles_moduleCatCyclesIso_hom
  证明: by
  simp [← cancel_mono S.moduleCatLeftHomologyData.i]

Depends on / 依赖: S.moduleCatLeftHomologyData.i, cancel_mono, moduleCatLeftHomologyData
-/
lemma toCycles_moduleCatCyclesIso_hom :
    S.toCycles ≫ S.moduleCatCyclesIso.hom = S.moduleCatLeftHomologyData.f' := by
  simp [← cancel_mono S.moduleCatLeftHomologyData.i]

/--
Definition of `moduleCatOpcyclesIso` / `moduleCatOpcyclesIso` 的定义

English:
definition moduleCatOpcyclesIso
  signature: :
  body: S.opcyclesIsoCokernel ≪≫ ModuleCat.cokernelIsoRangeQuotient _

@[reassoc (attr := simp), elementwise (attr := simp)]

中文:
定义 moduleCatOpcyclesIso
  签名: :
  定义体: S.opcyclesIsoCokernel ≪≫ ModuleCat.cokernelIsoRangeQuotient _

@[reassoc (attr := simp), elementwise (attr := simp)]

Depends on / 依赖: ModuleCat, ModuleCat.cokernelIsoRangeQuotient, S.opcyclesIsoCokernel, cokernelIsoRangeQuotient, opcyclesIsoCokernel
-/
noncomputable def moduleCatOpcyclesIso :
    S.opcycles ≅ ModuleCat.of R (S.X₂ ⧸ LinearMap.range S.f.hom) :=
  S.opcyclesIsoCokernel ≪≫ ModuleCat.cokernelIsoRangeQuotient _

@[reassoc (attr := simp), elementwise (attr := simp)]
/--
theorem `pOpcycles_comp_moduleCatOpcyclesIso_hom` / 定理 `pOpcycles_comp_moduleCatOpcyclesIso_hom`

English:
theorem pOpcycles_comp_moduleCatOpcyclesIso_hom
  proof: by
  simp [moduleCatOpcyclesIso]

中文:
定理 pOpcycles_comp_moduleCatOpcyclesIso_hom
  证明: by
  simp [moduleCatOpcyclesIso]

Depends on / 依赖: moduleCatOpcyclesIso
-/
theorem pOpcycles_comp_moduleCatOpcyclesIso_hom :
    S.pOpcycles ≫ S.moduleCatOpcyclesIso.hom = ModuleCat.ofHom (Submodule.mkQ _) := by
  simp [moduleCatOpcyclesIso]

/--
theorem `moduleCat_pOpcycles_eq_iff` / 定理 `moduleCat_pOpcycles_eq_iff`

English:
theorem moduleCat_pOpcycles_eq_iff
  given: (x y : S.X₂)
  proof: Iff.trans ⟨fun h => by simpa using congr(S.moduleCatOpcyclesIso.hom $h),
    fun h => (ModuleCat.mono_iff_injective S.moduleCatOpcyclesIso.hom).1 inferInstance (by simpa)⟩
    (Submodule.Quotient.eq _)

中文:
定理 moduleCat_pOpcycles_eq_iff
  条件: (x y : S.X₂)
  证明: Iff.trans ⟨fun h => by simpa using congr(S.moduleCatOpcyclesIso.hom $h),
    fun h => (ModuleCat.mono_iff_injective S.moduleCatOpcyclesIso.hom).1 inferInstance (by simpa)⟩
    (Submodule.Quotient.eq _)

Depends on / 依赖: Iff.trans, ModuleCat, ModuleCat.mono_iff_injective, Quotient, S.moduleCatOpcyclesIso.hom, Submodule, Submodule.Quotient.eq, moduleCatOpcyclesIso, mono_iff_injective
-/
theorem moduleCat_pOpcycles_eq_iff (x y : S.X₂) :
    S.pOpcycles x = S.pOpcycles y ↔ x - y in LinearMap.range S.f.hom :=
  Iff.trans ⟨fun h => by simpa using congr(S.moduleCatOpcyclesIso.hom $h),
    fun h => (ModuleCat.mono_iff_injective S.moduleCatOpcyclesIso.hom).1 inferInstance (by simpa)⟩
    (Submodule.Quotient.eq _)

/--
theorem `moduleCat_pOpcycles_eq_zero_iff` / 定理 `moduleCat_pOpcycles_eq_zero_iff`

English:
theorem moduleCat_pOpcycles_eq_zero_iff
  given: (x : S.X₂)
  proof: by
  simpa using moduleCat_pOpcycles_eq_iff _ x 0

中文:
定理 moduleCat_pOpcycles_eq_zero_iff
  条件: (x : S.X₂)
  证明: by
  simpa using moduleCat_pOpcycles_eq_iff _ x 0

Depends on / 依赖: moduleCat_pOpcycles_eq_iff
-/
theorem moduleCat_pOpcycles_eq_zero_iff (x : S.X₂) :
    S.pOpcycles x = 0 ↔ x in LinearMap.range S.f.hom := by
  simpa using moduleCat_pOpcycles_eq_iff _ x 0

/--
Definition of `moduleCatHomologyIso` / `moduleCatHomologyIso` 的定义

English:
definition moduleCatHomologyIso
  signature: :
  body: S.moduleCatLeftHomologyData.homologyIso

@[reassoc (attr := simp, elementwise)]

中文:
定义 moduleCatHomologyIso
  签名: :
  定义体: S.moduleCatLeftHomologyData.homologyIso

@[reassoc (attr := simp, elementwise)]

Depends on / 依赖: S.moduleCatLeftHomologyData.homologyIso, homologyIso, moduleCatLeftHomologyData
-/
noncomputable def moduleCatHomologyIso :
    S.homology ≅ S.moduleCatLeftHomologyData.H :=
  S.moduleCatLeftHomologyData.homologyIso

@[reassoc (attr := simp, elementwise)]
/--
lemma `π_moduleCatCyclesIso_hom` / 引理 `π_moduleCatCyclesIso_hom`

English:
lemma π_moduleCatCyclesIso_hom
  proof: S.moduleCatLeftHomologyData.homologyπ_comp_homologyIso_hom

@[reassoc (attr := simp, elementwise)]

中文:
引理 π_moduleCatCyclesIso_hom
  证明: S.moduleCatLeftHomologyData.homologyπ_comp_homologyIso_hom

@[reassoc (attr := simp, elementwise)]

Depends on / 依赖: S.moduleCatLeftHomologyData.homology, moduleCatLeftHomologyData
-/
lemma π_moduleCatCyclesIso_hom :
    S.homologyπ ≫ S.moduleCatHomologyIso.hom =
      S.moduleCatCyclesIso.hom ≫ S.moduleCatLeftHomologyData.π :=
  S.moduleCatLeftHomologyData.homologyπ_comp_homologyIso_hom

@[reassoc (attr := simp, elementwise)]
/--
lemma `moduleCatCyclesIso_inv_π` / 引理 `moduleCatCyclesIso_inv_π`

English:
lemma moduleCatCyclesIso_inv_π
  proof: S.moduleCatLeftHomologyData.π_comp_homologyIso_inv

中文:
引理 moduleCatCyclesIso_inv_π
  证明: S.moduleCatLeftHomologyData.π_comp_homologyIso_inv

Depends on / 依赖: S.moduleCatLeftHomologyData, moduleCatLeftHomologyData
-/
lemma moduleCatCyclesIso_inv_π :
    S.moduleCatCyclesIso.inv ≫ S.homologyπ =
       S.moduleCatLeftHomologyData.π ≫ S.moduleCatHomologyIso.inv :=
  S.moduleCatLeftHomologyData.π_comp_homologyIso_inv

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `exact_iff_surjective_moduleCatToCycles` / 引理 `exact_iff_surjective_moduleCatToCycles`

English:
lemma exact_iff_surjective_moduleCatToCycles
  proof: by
  simp [S.moduleCatLeftHomologyData.exact_iff_epi_f',
    ModuleCat.epi_iff_surjective, moduleCatLeftHomologyData_K]

中文:
引理 exact_iff_surjective_moduleCatToCycles
  证明: by
  simp [S.moduleCatLeftHomologyData.exact_iff_epi_f',
    ModuleCat.epi_iff_surjective, moduleCatLeftHomologyData_K]

Depends on / 依赖: ModuleCat, ModuleCat.epi_iff_surjective, S.moduleCatLeftHomologyData.exact_iff_epi_f, epi_iff_surjective, exact_iff_epi_f, moduleCatLeftHomologyData, moduleCatLeftHomologyData_K
-/
lemma exact_iff_surjective_moduleCatToCycles :
    S.Exact ↔ Function.Surjective S.moduleCatToCycles := by
  simp [S.moduleCatLeftHomologyData.exact_iff_epi_f',
    ModuleCat.epi_iff_surjective, moduleCatLeftHomologyData_K]

end ShortComplex

end CategoryTheory

section

variable {M : Type v} [AddCommGroup M] [Module R M] {N : Type v} [AddCommGroup N] [Module R N]

open CategoryTheory

/--
Definition of `LinearMap.shortComplexKer` / `LinearMap.shortComplexKer` 的定义

English:
abbreviation LinearMap.shortComplexKer
  signature: (f : M ->ₗ[R] N)
  body: ModuleCat.ofHom.{v} (LinearMap.ker f).subtype
  g := ModuleCat.ofHom.{v} f
  zero := by ext; simp

中文:
缩写 线性映射.shortComplexKer
  签名: (f : M ->ₗ[R] N)
  定义体: ModuleCat.ofHom.{v} (LinearMap.ker f).subtype
  g := ModuleCat.ofHom.{v} f
  zero := by ext; simp

Depends on / 依赖: LinearMap, LinearMap.ker, ModuleCat, ModuleCat.ofHom, subtype
-/
abbrev LinearMap.shortComplexKer (f : M ->ₗ[R] N) : ShortComplex (ModuleCat.{v} R) where
  f := ModuleCat.ofHom.{v} (LinearMap.ker f).subtype
  g := ModuleCat.ofHom.{v} f
  zero := by ext; simp

/--
theorem `LinearMap.shortExact_shortComplexKer` / 定理 `LinearMap.shortExact_shortComplexKer`

English:
theorem LinearMap.shortExact_shortComplexKer
  given: {f : M ->ₗ[R] N} (h : Function.Surjective f)
  proof: (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    fun _ => by simp [shortComplexKer]
  mono_f := (ModuleCat.mono_iff_injective _).mpr (LinearMap.ker f).injective_subtype
  epi_g := (ModuleCat.epi_iff_surjective _).mpr h

中文:
定理 线性映射.shortExact_shortComplexKer
  条件: {f : M ->ₗ[R] N} (h : 函数.满射 f)
  证明: (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    fun _ => by simp [shortComplexKer]
  mono_f := (ModuleCat.mono_iff_injective _).mpr (LinearMap.ker f).injective_subtype
  epi_g := (ModuleCat.epi_iff_surjective _).mpr h

Depends on / 依赖: ShortComplex, ShortComplex.ShortExact.moduleCat_exact_iff_function_exact, ShortExact, moduleCat_exact_iff_function_exact
-/
theorem LinearMap.shortExact_shortComplexKer {f : M ->ₗ[R] N} (h : Function.Surjective f) :
    f.shortComplexKer.ShortExact where
  exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    fun _ => by simp [shortComplexKer]
  mono_f := (ModuleCat.mono_iff_injective _).mpr (LinearMap.ker f).injective_subtype
  epi_g := (ModuleCat.epi_iff_surjective _).mpr h

variable {L : Type v} [AddCommGroup L] [Module R L]

/--
Definition of `ModuleCat.shortComplexOfCompEqZero` / `ModuleCat.shortComplexOfCompEqZero` 的定义

English:
abbreviation ModuleCat.shortComplexOfCompEqZero
  signature: (f : M ->ₗ[R] N) (g : N ->ₗ[R] L) (eq0 : g.comp f = 0)
  body: ModuleCat.ofHom f
  g := ModuleCat.ofHom g

中文:
缩写 模范畴.shortComplexOfCompEqZero
  签名: (f : M ->ₗ[R] N) (g : N ->ₗ[R] L) (eq0 : g.comp f = 0)
  定义体: ModuleCat.ofHom f
  g := ModuleCat.ofHom g

Depends on / 依赖: ModuleCat, ModuleCat.ofHom
-/
abbrev ModuleCat.shortComplexOfCompEqZero (f : M ->ₗ[R] N) (g : N ->ₗ[R] L) (eq0 : g.comp f = 0) :
    ShortComplex (ModuleCat.{v} R) where
  f := ModuleCat.ofHom f
  g := ModuleCat.ofHom g

/--
lemma `ModuleCat.shortComplex_exact` / 引理 `ModuleCat.shortComplex_exact`

English:
lemma ModuleCat.shortComplex_exact
  statement: (S : ShortComplex (ModuleCat.{v} R))
  proof: (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr exac

中文:
引理 模范畴.shortComplex_exact
  结论: (S : 短复形 (模范畴.{v} R))
  证明: (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr exac

Depends on / 依赖: ShortComplex, ShortComplex.ShortExact.moduleCat_exact_iff_function_exact, ShortExact, moduleCat_exact_iff_function_exact
-/
lemma ModuleCat.shortComplex_exact (S : ShortComplex (ModuleCat.{v} R))
    (exac : Function.Exact S.f S.g) : S.Exact :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr exac

/--
lemma `ModuleCat.shortComplex_shortExact` / 引理 `ModuleCat.shortComplex_shortExact`

English:
lemma ModuleCat.shortComplex_shortExact
  statement: (S : ShortComplex (ModuleCat.{v} R))
  proof: (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr exac
  mono_f := (ModuleCat.mono_iff_injective _).mpr inj
  epi_g := (ModuleCat.epi_iff_surjective _).mpr surj

中文:
引理 模范畴.shortComplex_shortExact
  结论: (S : 短复形 (模范畴.{v} R))
  证明: (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr exac
  mono_f := (ModuleCat.mono_iff_injective _).mpr inj
  epi_g := (ModuleCat.epi_iff_surjective _).mpr surj

Depends on / 依赖: ShortComplex, ShortComplex.ShortExact.moduleCat_exact_iff_function_exact, ShortExact, moduleCat_exact_iff_function_exact
-/
lemma ModuleCat.shortComplex_shortExact (S : ShortComplex (ModuleCat.{v} R))
    (exac : Function.Exact S.f S.g) (inj : Function.Injective S.f)
    (surj : Function.Surjective S.g) : S.ShortExact where
  exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr exac
  mono_f := (ModuleCat.mono_iff_injective _).mpr inj
  epi_g := (ModuleCat.epi_iff_surjective _).mpr surj

variable {M' N' L' : Type*} [AddCommGroup M'] [AddCommGroup N'] [AddCommGroup L']
  [Module R M'] [Module R N'] [Module R L']

variable (eM : M ≃ₗ[R] M') (eN : N ≃ₗ[R] N') (eL : L ≃ₗ[R] L') (f : M' ->ₗ[R] N') (g : N' ->ₗ[R] L')

/--
Definition of `ModuleCat.shortComplexOfConj` / `ModuleCat.shortComplexOfConj` 的定义

English:
abbreviation ModuleCat.shortComplexOfConj
  signature: (eq0 : g ∘ₗ f = 0)
  body: ModuleCat.shortComplexOfCompEqZero ((eN.symm.comp f).comp eM.toLinearMap)
    (eL.symm.comp (g.comp eN.toLinearMap)) (by
      ext x
      simpa using LinearMap.congr_fun eq0 (eM x))

中文:
缩写 模范畴.shortComplexOfConj
  签名: (eq0 : g ∘ₗ f = 0)
  定义体: ModuleCat.shortComplexOfCompEqZero ((eN.symm.comp f).comp eM.toLinearMap)
    (eL.symm.comp (g.comp eN.toLinearMap)) (by
      ext x
      simpa using LinearMap.congr_fun eq0 (eM x))

Depends on / 依赖: LinearMap, LinearMap.congr_fun, ModuleCat, ModuleCat.shortComplexOfCompEqZero, congr_fun, eL.symm.comp, eM.toLinearMap, eN.symm.comp, eN.toLinearMap, g.comp, shortComplexOfCompEqZero, toLinearMap
-/
abbrev ModuleCat.shortComplexOfConj (eq0 : g ∘ₗ f = 0) :
    ShortComplex (ModuleCat.{v} R) :=
  ModuleCat.shortComplexOfCompEqZero ((eN.symm.comp f).comp eM.toLinearMap)
    (eL.symm.comp (g.comp eN.toLinearMap)) (by
      ext x
      simpa using LinearMap.congr_fun eq0 (eM x))

/--
lemma `exact_conj_of_exact` / 引理 `exact_conj_of_exact`

English:
lemma exact_conj_of_exact
  given: (exact : Function.Exact f g)
  statement: Function.Exact
  proof: by
  rwa [LinearEquiv.precomp_exact_iff_exact, LinearEquiv.postcomp_exact_iff_exact,
    LinearEquiv.conj_symm_exact_iff_exact]

中文:
引理 exact_conj_of_exact
  条件: (exact : 函数.正合 f g)
  结论: 函数.正合
  证明: by
  rwa [LinearEquiv.precomp_exact_iff_exact, LinearEquiv.postcomp_exact_iff_exact,
    LinearEquiv.conj_symm_exact_iff_exact]
-/
private lemma exact_conj_of_exact (exact : Function.Exact f g) : Function.Exact
    ((eN.symm.comp f).comp eM.toLinearMap) (eL.symm.comp (g.comp eN.toLinearMap)) := by
  rwa [LinearEquiv.precomp_exact_iff_exact, LinearEquiv.postcomp_exact_iff_exact,
    LinearEquiv.conj_symm_exact_iff_exact]

/--
lemma `ModuleCat.shortComplexOfConj_exact` / 引理 `ModuleCat.shortComplexOfConj_exact`

English:
lemma ModuleCat.shortComplexOfConj_exact
  given: (exact : Function.Exact f g)
  proof: ModuleCat.shortComplex_exact _ (exact_conj_of_exact eM eN eL f g exact)

中文:
引理 模范畴.shortComplexOfConj_exact
  条件: (exact : 函数.正合 f g)
  证明: ModuleCat.shortComplex_exact _ (exact_conj_of_exact eM eN eL f g exact)

Depends on / 依赖: ModuleCat, ModuleCat.shortComplex_exact, exact_conj_of_exact, shortComplex_exact
-/
lemma ModuleCat.shortComplexOfConj_exact (exact : Function.Exact f g) :
    (ModuleCat.shortComplexOfConj eM eN eL f g exact.linearMap_comp_eq_zero).Exact :=
  ModuleCat.shortComplex_exact _ (exact_conj_of_exact eM eN eL f g exact)

/--
lemma `ModuleCat.shortComplexOfConj_shortExact` / 引理 `ModuleCat.shortComplexOfConj_shortExact`

English:
lemma ModuleCat.shortComplexOfConj_shortExact
  statement: (exact : Function.Exact f g)
  proof: by
  refine ModuleCat.shortComplex_shortExact _ (exact_conj_of_exact eM eN eL f g exact) ?_ ?_
  all_goals simpa

中文:
引理 模范畴.shortComplexOfConj_shortExact
  结论: (exact : 函数.正合 f g)
  证明: by
  refine ModuleCat.shortComplex_shortExact _ (exact_conj_of_exact eM eN eL f g exact) ?_ ?_
  all_goals simpa

Depends on / 依赖: ModuleCat, ModuleCat.shortComplex_shortExact, all_goals, exact_conj_of_exact, shortComplex_shortExact
-/
lemma ModuleCat.shortComplexOfConj_shortExact (exact : Function.Exact f g)
    (inj : Function.Injective f) (surj : Function.Surjective g) :
    (ModuleCat.shortComplexOfConj eM eN eL f g exact.linearMap_comp_eq_zero).ShortExact := by
  refine ModuleCat.shortComplex_shortExact _ (exact_conj_of_exact eM eN eL f g exact) ?_ ?_
  all_goals simpa

end
