/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Kernels
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.GroupTheory.QuotientGroup.Finite

/-!
# Homology and exactness of short complexes of abelian groups

In this file, the homology of a short complex `S` of abelian groups is identified
with the quotient of `AddMonoidHom.ker S.g` by the image of the morphism
`S.abToCycles : S.X₁ →+ AddMonoidHom.ker S.g` induced by `S.f`.

The definitions are made in the `ShortComplex` namespace so as to enable dot notation.
The names contain the prefix `ab` in order to allow similar constructions for
other categories like `ModuleCat`.

## Main definitions
- `ShortComplex.abHomologyIso` identifies the homology of a short complex of abelian
  groups to an explicit quotient.
- `ShortComplex.ab_exact_iff` expresses that a short complex of abelian groups `S`
  is exact iff any element in the kernel of `S.g` belongs to the image of `S.f`.

-/

@[expose] public section

universe u

namespace CategoryTheory

namespace ShortComplex

variable (S : ShortComplex Ab.{u})

@[simp]
/--
lemma `ab_zero_apply` / 引理 `ab_zero_apply`

English:
lemma ab_zero_apply
  given: (x : S.X₁)
  statement: S.g (S.f x) = 0
  proof: by
  rw [← ConcreteCategory.comp_apply]; rw [S.zero]
  rfl

中文:
引理 ab_zero_apply
  条件: (x : S.X₁)
  结论: S.g (S.f x) = 0
  证明: by
  rw [← ConcreteCategory.comp_apply]; rw [S.zero]
  rfl

Depends on / 依赖: ConcreteCategory, ConcreteCategory.comp_apply, S.zero, comp_apply
-/
lemma ab_zero_apply (x : S.X₁) : S.g (S.f x) = 0 := by
  rw [← ConcreteCategory.comp_apply]; rw [S.zero]
  rfl

/-- The canonical additive morphism `S.X₁ →+ AddMonoidHom.ker S.g` induced by `S.f`. -/
@[simps!]
/--
Definition of `abToCycles` / `abToCycles` 的定义

English:
definition abToCycles
  signature: : S.X₁ ->+ AddMonoidHom.ker S.g.hom
  body: AddMonoidHom.mk' (fun x => ⟨S.f x, S.ab_zero_apply x⟩) (by aesop)

中文:
定义 abToCycles
  签名: : S.X₁ ->+ AddMonoidHom.ker S.g.hom
  定义体: AddMonoidHom.mk' (fun x => ⟨S.f x, S.ab_zero_apply x⟩) (by aesop)

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mk, S.ab_zero_apply, ab_zero_apply
-/
def abToCycles : S.X₁ ->+ AddMonoidHom.ker S.g.hom :=
    AddMonoidHom.mk' (fun x => ⟨S.f x, S.ab_zero_apply x⟩) (by aesop)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The explicit left homology data of a short complex of abelian group that is
given by a kernel and a quotient given by the `AddMonoidHom` API. -/
@[simps]
/--
Definition of `abLeftHomologyData` / `abLeftHomologyData` 的定义

English:
definition abLeftHomologyData
  signature: : S.LeftHomologyData where
  body: AddCommGrpCat.of (AddMonoidHom.ker S.g.hom)
  H := AddCommGrpCat.of ((AddMonoidHom.ker S.g.hom) ⧸ AddMonoidHom.range S.abToCycles)
i := AddCommGrpCat.ofHom (AddMonoidHom.ker S.g.hom).subtype
π := AddCommGrpCat.ofHom QuotientAddGroup.mk' _
  wi := by
    ext ⟨_, hx⟩
    exact hx
  hi := AddCommGrpCat

中文:
定义 abLeftHomologyData
  签名: : S.LeftHomologyData where
  定义体: AddCommGrpCat.of (AddMonoidHom.ker S.g.hom)
  H := AddCommGrpCat.of ((AddMonoidHom.ker S.g.hom) ⧸ AddMonoidHom.range S.abToCycles)
i := AddCommGrpCat.ofHom (AddMonoidHom.ker S.g.hom).subtype
π := AddCommGrpCat.ofHom QuotientAddGroup.mk' _
  wi := by
    ext ⟨_, hx⟩
    exact hx
  hi := AddCommGrpCat

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.of, AddMonoidHom, AddMonoidHom.ker, S.g.hom
-/
def abLeftHomologyData : S.LeftHomologyData where
  K := AddCommGrpCat.of (AddMonoidHom.ker S.g.hom)
  H := AddCommGrpCat.of ((AddMonoidHom.ker S.g.hom) ⧸ AddMonoidHom.range S.abToCycles)
i := AddCommGrpCat.ofHom (AddMonoidHom.ker S.g.hom).subtype
π := AddCommGrpCat.ofHom QuotientAddGroup.mk' _
  wi := by
    ext ⟨_, hx⟩
    exact hx
  hi := AddCommGrpCat.kernelIsLimit _
  wπ := by
    ext (x : S.X₁)
    dsimp
    rw [QuotientAddGroup.eq_zero_iff]; rw [AddMonoidHom.mem_range]
    apply exists_apply_eq_apply
  hπ := AddCommGrpCat.cokernelIsColimit (AddCommGrpCat.ofHom S.abToCycles)

@[simp]
/--
lemma `abLeftHomologyData_f'` / 引理 `abLeftHomologyData_f'`

English:
lemma abLeftHomologyData_f'
  statement: S.abLeftHomologyData.f' = AddCommGrpCat.ofHom S.abToCycles
  proof: rfl

中文:
引理 abLeftHomologyData_f'
  结论: S.abLeftHomologyData.f' = AddCommGrpCat.ofHom S.abToCycles
  证明: rfl
-/
lemma abLeftHomologyData_f' : S.abLeftHomologyData.f' = AddCommGrpCat.ofHom S.abToCycles := rfl

/--
Definition of `abCyclesIso` / `abCyclesIso` 的定义

English:
definition abCyclesIso
  signature: : S.cycles ≅ AddCommGrpCat.of (AddMonoidHom.ker S.g.hom)
  body: S.abLeftHomologyData.cyclesIso

中文:
定义 abCyclesIso
  签名: : S.cycles ≅ AddCommGrpCat.of (AddMonoidHom.ker S.g.hom)
  定义体: S.abLeftHomologyData.cyclesIso

Depends on / 依赖: S.abLeftHomologyData.cyclesIso, abLeftHomologyData, cyclesIso
-/
noncomputable def abCyclesIso : S.cycles ≅ AddCommGrpCat.of (AddMonoidHom.ker S.g.hom) :=
  S.abLeftHomologyData.cyclesIso

set_option backward.isDefEq.respectTransparency false in
-- This was a simp lemma until we made `AddCommGrpCat.coe_of` a simp lemma,
-- after which the simp normal form linter complains.
-- It was not used a simp lemma in Mathlib.
-- Possible solution: higher priority function coercions that remove the `of`?
-- @[simp]
/--
lemma `abCyclesIso_inv_apply_iCycles` / 引理 `abCyclesIso_inv_apply_iCycles`

English:
lemma abCyclesIso_inv_apply_iCycles
  given: (x : AddMonoidHom.ker S.g.hom)
  proof: by
  dsimp only [abCyclesIso]
  rw [← ConcreteCategory.comp_apply]; rw [S.abLeftHomologyData.cyclesIso_inv_comp_iCycles]
  rfl

中文:
引理 abCyclesIso_inv_apply_iCycles
  条件: (x : AddMonoidHom.ker S.g.hom)
  证明: by
  dsimp only [abCyclesIso]
  rw [← ConcreteCategory.comp_apply]; rw [S.abLeftHomologyData.cyclesIso_inv_comp_iCycles]
  rfl

Depends on / 依赖: ConcreteCategory, ConcreteCategory.comp_apply, RightHomologyData, RightHomologyData.ofEpiOfIsIsoOfMono, RightHomologyMapData, RightHomologyMapData.ofEpiOfIsIsoOfMono, S.abLeftHomologyData.cyclesIso_inv_comp_iCycles, _comp, abCyclesIso, abLeftHomologyData, comp_apply, comp_id, cyclesIso_inv_comp_iCycles, infer_instance, ofEpiOfIsIsoOfMono, rightHomologyMap
-/
lemma abCyclesIso_inv_apply_iCycles (x : AddMonoidHom.ker S.g.hom) :
    S.iCycles (S.abCyclesIso.inv x) = x := by
  dsimp only [abCyclesIso]
  rw [← ConcreteCategory.comp_apply]; rw [S.abLeftHomologyData.cyclesIso_inv_comp_iCycles]
  rfl

/--
Definition of `abHomologyIso` / `abHomologyIso` 的定义

English:
definition abHomologyIso
  signature: : S.homology ≅
  body: S.abLeftHomologyData.homologyIso

中文:
定义 abHomologyIso
  签名: : S.homology ≅
  定义体: S.abLeftHomologyData.homologyIso

Depends on / 依赖: S.abLeftHomologyData.homologyIso, abLeftHomologyData, homologyIso, infer_instance, rightHomologyMap
-/
noncomputable def abHomologyIso : S.homology ≅
    AddCommGrpCat.of ((AddMonoidHom.ker S.g.hom) ⧸ AddMonoidHom.range S.abToCycles) :=
  S.abLeftHomologyData.homologyIso

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `exact_iff_surjective_abToCycles` / 引理 `exact_iff_surjective_abToCycles`

English:
lemma exact_iff_surjective_abToCycles
  proof: by
  rw [S.abLeftHomologyData.exact_iff_epi_f']; rw [abLeftHomologyData_f']; rw [AddCommGrpCat.epi_iff_surjective]
  rfl

中文:
引理 exact_iff_surjective_abToCycles
  证明: by
  rw [S.abLeftHomologyData.exact_iff_epi_f']; rw [abLeftHomologyData_f']; rw [AddCommGrpCat.epi_iff_surjective]
  rfl

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.epi_iff_surjective, S.abLeftHomologyData.exact_iff_epi_f, abLeftHomologyData, abLeftHomologyData_f, epi_iff_surjective, exact_iff_epi_f
-/
lemma exact_iff_surjective_abToCycles :
    S.Exact ↔ Function.Surjective S.abToCycles := by
  rw [S.abLeftHomologyData.exact_iff_epi_f']; rw [abLeftHomologyData_f']; rw [AddCommGrpCat.epi_iff_surjective]
  rfl

/--
lemma `ab_exact_iff` / 引理 `ab_exact_iff`

English:
lemma ab_exact_iff
  proof: by
  rw [exact_iff_surjective_abToCycles]
  constructor
  · intro h x₂ hx₂
    obtain ⟨x₁, hx₁⟩ := h ⟨x₂, hx₂⟩
    exact ⟨x₁, by simpa only [Subtype.ext_iff, abToCycles_apply_coe] using hx₁⟩
  · rintro h ⟨x₂, hx₂⟩
    obtain ⟨x₁, rfl⟩ := h x₂ hx₂
    exact ⟨x₁, rfl⟩

中文:
引理 ab_exact_iff
  证明: by
  rw [exact_iff_surjective_abToCycles]
  constructor
  · intro h x₂ hx₂
    obtain ⟨x₁, hx₁⟩ := h ⟨x₂, hx₂⟩
    exact ⟨x₁, by simpa only [Subtype.ext_iff, abToCycles_apply_coe] using hx₁⟩
  · rintro h ⟨x₂, hx₂⟩
    obtain ⟨x₁, rfl⟩ := h x₂ hx₂
    exact ⟨x₁, rfl⟩

Depends on / 依赖: Subtype, Subtype.ext_iff, abToCycles_apply_coe, exact_iff_surjective_abToCycles, ext_iff
-/
lemma ab_exact_iff :
    S.Exact ↔ forall (x₂ : S.X₂) (_ : S.g x₂ = 0), exists (x₁ : S.X₁), S.f x₁ = x₂ := by
  rw [exact_iff_surjective_abToCycles]
  constructor
  · intro h x₂ hx₂
    obtain ⟨x₁, hx₁⟩ := h ⟨x₂, hx₂⟩
    exact ⟨x₁, by simpa only [Subtype.ext_iff, abToCycles_apply_coe] using hx₁⟩
  · rintro h ⟨x₂, hx₂⟩
    obtain ⟨x₁, rfl⟩ := h x₂ hx₂
    exact ⟨x₁, rfl⟩

/--
lemma `ab_exact_iff_function_exact` / 引理 `ab_exact_iff_function_exact`

English:
lemma ab_exact_iff_function_exact
  proof: by
  rw [S.ab_exact_iff]
  apply forall_congr'
  intro x₂
  constructor
  · intro h
    refine ⟨h, ?_⟩
    rintro ⟨x₁, rfl⟩
    simp only [ab_zero_apply]
  · tauto

中文:
引理 ab_exact_iff_function_exact
  证明: by
  rw [S.ab_exact_iff]
  apply forall_congr'
  intro x₂
  constructor
  · intro h
    refine ⟨h, ?_⟩
    rintro ⟨x₁, rfl⟩
    simp only [ab_zero_apply]
  · tauto

Depends on / 依赖: S.ab_exact_iff, ab_exact_iff, ab_zero_apply, forall_congr
-/
lemma ab_exact_iff_function_exact :
    S.Exact ↔ Function.Exact S.f S.g := by
  rw [S.ab_exact_iff]
  apply forall_congr'
  intro x₂
  constructor
  · intro h
    refine ⟨h, ?_⟩
    rintro ⟨x₁, rfl⟩
    simp only [ab_zero_apply]
  · tauto

variable {S}

/--
lemma `ab_exact_iff_ker_le_range` / 引理 `ab_exact_iff_ker_le_range`

English:
lemma ab_exact_iff_ker_le_range
  statement: S.Exact ↔ S.g.hom.ker <= S.f.hom.range
  proof: S.ab_exact_iff

中文:
引理 ab_exact_iff_ker_le_range
  结论: S.Exact ↔ S.g.hom.ker <= S.f.hom.range
  证明: S.ab_exact_iff

Depends on / 依赖: S.ab_exact_iff, ab_exact_iff
-/
lemma ab_exact_iff_ker_le_range : S.Exact ↔ S.g.hom.ker <= S.f.hom.range := S.ab_exact_iff

/--
lemma `ab_exact_iff_range_eq_ker` / 引理 `ab_exact_iff_range_eq_ker`

English:
lemma ab_exact_iff_range_eq_ker
  statement: S.Exact ↔ S.f.hom.range = S.g.hom.ker
  proof: by
  rw [ab_exact_iff_ker_le_range]
  constructor
  · intro h
    refine le_antisymm ?_ h
    rintro _ ⟨x₁, rfl⟩
    rw [AddMonoidHom.mem_ker]; rw [← ConcreteCategory.comp_apply]; rw [S.zero]
    rfl
  · intro h
    rw [h]

alias ⟨Exact.ab_range_eq_ker, _⟩ := ab_exact_iff_range_eq_ker

中文:
引理 ab_exact_iff_range_eq_ker
  结论: S.Exact ↔ S.f.hom.range = S.g.hom.ker
  证明: by
  rw [ab_exact_iff_ker_le_range]
  constructor
  · intro h
    refine le_antisymm ?_ h
    rintro _ ⟨x₁, rfl⟩
    rw [AddMonoidHom.mem_ker]; rw [← ConcreteCategory.comp_apply]; rw [S.zero]
    rfl
  · intro h
    rw [h]

alias ⟨Exact.ab_range_eq_ker, _⟩ := ab_exact_iff_range_eq_ker

Depends on / 依赖: AddMonoidHom, AddMonoidHom.mem_ker, ConcreteCategory, ConcreteCategory.comp_apply, S.zero, ab_exact_iff_ker_le_range, comp_apply, le_antisymm, mem_ker
-/
lemma ab_exact_iff_range_eq_ker : S.Exact ↔ S.f.hom.range = S.g.hom.ker := by
  rw [ab_exact_iff_ker_le_range]
  constructor
  · intro h
    refine le_antisymm ?_ h
    rintro _ ⟨x₁, rfl⟩
    rw [AddMonoidHom.mem_ker]; rw [← ConcreteCategory.comp_apply]; rw [S.zero]
    rfl
  · intro h
    rw [h]

alias ⟨Exact.ab_range_eq_ker, _⟩ := ab_exact_iff_range_eq_ker

/--
lemma `Exact.ab_finite` / 引理 `Exact.ab_finite`

English:
lemma Exact.ab_finite
  given: {S : ShortComplex Ab.{u}} (hS : S.Exact) [Finite S.X₁] [Finite S.X₃]
  proof: by
  have : Finite S.f.hom.range := Set.finite_range _
  have : Finite (S.X₂ ⧸ S.f.hom.range) := by
    rw [hS.ab_range_eq_ker]
    exact .of_equiv _ (QuotientAddGroup.quotientKerEquivRange _).toEquiv.symm
  exact .of_addSubgroup_quotient (H := S.f.hom.range)

中文:
引理 Exact.ab_finite
  条件: {S : ShortComplex Ab.{u}} (hS : S.Exact) [Finite S.X₁] [Finite S.X₃]
  证明: by
  have : Finite S.f.hom.range := Set.finite_range _
  have : Finite (S.X₂ ⧸ S.f.hom.range) := by
    rw [hS.ab_range_eq_ker]
    exact .of_equiv _ (QuotientAddGroup.quotientKerEquivRange _).toEquiv.symm
  exact .of_addSubgroup_quotient (H := S.f.hom.range)

Depends on / 依赖: Finite, QuotientAddGroup, QuotientAddGroup.quotientKerEquivRange, S.f.hom.range, Set.finite_range, ab_range_eq_ker, finite_range, hS.ab_range_eq_ker, of_addSubgroup_quotient, of_equiv, quotientKerEquivRange, toEquiv, toEquiv.symm
-/
lemma Exact.ab_finite {S : ShortComplex Ab.{u}} (hS : S.Exact) [Finite S.X₁] [Finite S.X₃] :
    Finite S.X₂ := by
  have : Finite S.f.hom.range := Set.finite_range _
  have : Finite (S.X₂ ⧸ S.f.hom.range) := by
    rw [hS.ab_range_eq_ker]
    exact .of_equiv _ (QuotientAddGroup.quotientKerEquivRange _).toEquiv.symm
  exact .of_addSubgroup_quotient (H := S.f.hom.range)

/--
lemma `ShortExact.ab_injective_f` / 引理 `ShortExact.ab_injective_f`

English:
lemma ShortExact.ab_injective_f
  given: (hS : S.ShortExact)
  proof: (AddCommGrpCat.mono_iff_injective _).1 hS.mono_f

中文:
引理 ShortExact.ab_injective_f
  条件: (hS : S.ShortExact)
  证明: (AddCommGrpCat.mono_iff_injective _).1 hS.mono_f

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.mono_iff_injective, hS.mono_f, mono_f, mono_iff_injective
-/
lemma ShortExact.ab_injective_f (hS : S.ShortExact) :
    Function.Injective S.f :=
  (AddCommGrpCat.mono_iff_injective _).1 hS.mono_f

/--
lemma `ShortExact.ab_surjective_g` / 引理 `ShortExact.ab_surjective_g`

English:
lemma ShortExact.ab_surjective_g
  given: (hS : S.ShortExact)
  proof: (AddCommGrpCat.epi_iff_surjective _).1 hS.epi_g

中文:
引理 ShortExact.ab_surjective_g
  条件: (hS : S.ShortExact)
  证明: (AddCommGrpCat.epi_iff_surjective _).1 hS.epi_g

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.epi_iff_surjective, epi_g, epi_iff_surjective, hS.epi_g
-/
lemma ShortExact.ab_surjective_g (hS : S.ShortExact) :
    Function.Surjective S.g :=
  (AddCommGrpCat.epi_iff_surjective _).1 hS.epi_g

/--
lemma `ShortExact.ab_finite_iff` / 引理 `ShortExact.ab_finite_iff`

English:
lemma ShortExact.ab_finite_iff
  given: {S : ShortComplex Ab.{u}} (hS : S.ShortExact)
  proof: ⟨.of_injective _ hS.ab_injective_f, .of_surjective _ hS.ab_surjective_g⟩
  mpr | ⟨_, _⟩ => hS.exact.ab_finite

中文:
引理 ShortExact.ab_finite_iff
  条件: {S : ShortComplex Ab.{u}} (hS : S.ShortExact)
  证明: ⟨.of_injective _ hS.ab_injective_f, .of_surjective _ hS.ab_surjective_g⟩
  mpr | ⟨_, _⟩ => hS.exact.ab_finite

Depends on / 依赖: ab_injective_f, ab_surjective_g, hS.ab_injective_f, hS.ab_surjective_g, of_injective, of_surjective
-/
lemma ShortExact.ab_finite_iff {S : ShortComplex Ab.{u}} (hS : S.ShortExact) :
    Finite S.X₂ ↔ Finite S.X₁ ∧ Finite S.X₃ where
  mp _ := ⟨.of_injective _ hS.ab_injective_f, .of_surjective _ hS.ab_surjective_g⟩
  mpr | ⟨_, _⟩ => hS.exact.ab_finite

end ShortComplex

end CategoryTheory
