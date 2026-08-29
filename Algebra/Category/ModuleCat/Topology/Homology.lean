/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Hill, Andrew Yang
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Topology.Basic
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!

# `TopModuleCat` is a `CategoryWithHomology`

`TopModuleCat R`, the category of topological `R`-modules, is not an abelian category.
But since the topology on subquotients is well-defined, we can still talk about homology in this
category. See the `CategoryWithHomology (TopModuleCat R)` instance in this file.

-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace TopModuleCat

variable {R : Type u} [Ring R] [TopologicalSpace R]

variable {M N : TopModuleCat.{v} R} (φ : M ⟶ N)

section kernel

/--
Definition of `ker` / `ker` 的定义

English:
abbreviation ker
  signature: : TopModuleCat R
  body: .of R φ.hom.ker

中文:
缩写 ker
  签名: : 顶元素模范畴 R
  定义体: .of R φ.hom.ker

Depends on / 依赖: hom.ker
-/
abbrev ker : TopModuleCat R := .of R φ.hom.ker

/--
Definition of `kerι` / `kerι` 的定义

English:
definition kerι
  signature: : ker φ ⟶ M
  body: ofHom ⟨Submodule.subtype _, continuous_subtype_val⟩

中文:
定义 kerι
  签名: : ker φ ⟶ M
  定义体: ofHom ⟨Submodule.subtype _, continuous_subtype_val⟩

Depends on / 依赖: Submodule, Submodule.subtype, continuous_subtype_val, subtype
-/
def kerι : ker φ ⟶ M := ofHom ⟨Submodule.subtype _, continuous_subtype_val⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mono (kerι φ)
  body: ConcreteCategory.mono_of_injective (kerι φ) Subtype.val_injective

中文:
实例 :
  签名: 单态射 (kerι φ)
  定义体: ConcreteCategory.mono_of_injective (kerι φ) Subtype.val_injective

Depends on / 依赖: ConcreteCategory, ConcreteCategory.mono_of_injective, Subtype, Subtype.val_injective, mono_of_injective, val_injective
-/
instance : Mono (kerι φ) := ConcreteCategory.mono_of_injective (kerι φ) Subtype.val_injective

/--
lemma `kerι_comp` / 引理 `kerι_comp`

English:
lemma kerι_comp
  statement: kerι φ ≫ φ = 0
  proof: by ext ⟨_, hm⟩; exact hm

中文:
引理 kerι_comp
  结论: kerι φ ≫ φ = 0
  证明: by ext ⟨_, hm⟩; exact hm
-/
@[simp] lemma kerι_comp : kerι φ ≫ φ = 0 := by ext ⟨_, hm⟩; exact hm

/--
lemma `kerι_apply` / 引理 `kerι_apply`

English:
lemma kerι_apply
  given: (x)
  statement: kerι φ x = x.1
  proof: rfl

中文:
引理 kerι_apply
  条件: (x)
  结论: kerι φ x = x.1
  证明: rfl
-/
@[simp] lemma kerι_apply (x) : kerι φ x = x.1 := rfl

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isLimitKer` / `isLimitKer` 的定义

English:
definition isLimitKer
  signature: : IsLimit (KernelFork.ofι (kerι φ) (kerι_comp φ))
  body: isLimitAux (KernelFork.ofι (kerι φ) (kerι_comp φ))
    (fun s => ofHom <| (Fork.ι s).hom.codRestrict φ.hom.ker fun m => by
      rw [LinearMap.mem_ker]; rw [ContinuousLinearMap.coe_coe]; rw [← ConcreteCategory.comp_apply (Fork.ι s) φ]; rw [KernelFork.condition]; rw [hom_zero_apply])
    (fun s => rf

中文:
定义 isLimitKer
  签名: : 是极限 (核叉.ofι (kerι φ) (kerι_comp φ))
  定义体: isLimitAux (KernelFork.ofι (kerι φ) (kerι_comp φ))
    (fun s => ofHom <| (Fork.ι s).hom.codRestrict φ.hom.ker fun m => by
      rw [LinearMap.mem_ker]; rw [ContinuousLinearMap.coe_coe]; rw [← ConcreteCategory.comp_apply (Fork.ι s) φ]; rw [KernelFork.condition]; rw [hom_zero_apply])
    (fun s => rf

Depends on / 依赖: ConcreteCategory, ConcreteCategory.comp_apply, ContinuousLinearMap, ContinuousLinearMap.coe_coe, KernelFork, KernelFork.condition, KernelFork.of, LinearMap, LinearMap.mem_ker, cancel_mono, codRestrict, coe_coe, comp_apply, condition, hom.codRestrict, hom.ker, hom_zero_apply, isLimitAux, mem_ker
-/
def isLimitKer : IsLimit (KernelFork.ofι (kerι φ) (kerι_comp φ)) :=
  isLimitAux (KernelFork.ofι (kerι φ) (kerι_comp φ))
    (fun s => ofHom <| (Fork.ι s).hom.codRestrict φ.hom.ker fun m => by
      rw [LinearMap.mem_ker]; rw [ContinuousLinearMap.coe_coe]; rw [← ConcreteCategory.comp_apply (Fork.ι s) φ]; rw [KernelFork.condition]; rw [hom_zero_apply])
    (fun s => rfl)
    (fun s m h => by dsimp at h ⊢; rw [← cancel_mono (kerι φ), h]; rfl)

end kernel

section cokernel

/--
Definition of `coker` / `coker` 的定义

English:
abbreviation coker
  signature: : TopModuleCat R
  body: .of R (N ⧸ φ.hom.range)

中文:
缩写 coker
  签名: : 顶元素模范畴 R
  定义体: .of R (N ⧸ φ.hom.range)

Depends on / 依赖: hom.range
-/
abbrev coker : TopModuleCat R := .of R (N ⧸ φ.hom.range)

/--
Definition of `cokerπ` / `cokerπ` 的定义

English:
definition cokerπ
  signature: : N ⟶ coker φ
  body: ofHom ⟨Submodule.mkQ _, by tauto⟩

@[simp]

中文:
定义 cokerπ
  签名: : N ⟶ coker φ
  定义体: ofHom ⟨Submodule.mkQ _, by tauto⟩

@[simp]

Depends on / 依赖: Submodule, Submodule.mkQ
-/
def cokerπ : N ⟶ coker φ := ofHom ⟨Submodule.mkQ _, by tauto⟩

@[simp]
/--
lemma `hom_cokerπ` / 引理 `hom_cokerπ`

English:
lemma hom_cokerπ
  given: (x)
  statement: (cokerπ φ).hom x = Submodule.mkQ _ x
  proof: rfl

中文:
引理 hom_cokerπ
  条件: (x)
  结论: (cokerπ φ).hom x = 子模.mkQ _ x
  证明: rfl
-/
lemma hom_cokerπ (x) : (cokerπ φ).hom x = Submodule.mkQ _ x := rfl

/--
lemma `cokerπ_surjective` / 引理 `cokerπ_surjective`

English:
lemma cokerπ_surjective
  statement: Function.Surjective (cokerπ φ).hom
  proof: Submodule.mkQ_surjective _

中文:
引理 cokerπ_surjective
  结论: 函数.满射 (cokerπ φ).hom
  证明: Submodule.mkQ_surjective _

Depends on / 依赖: Submodule, Submodule.mkQ_surjective, mkQ_surjective
-/
lemma cokerπ_surjective : Function.Surjective (cokerπ φ).hom := Submodule.mkQ_surjective _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Epi (cokerπ φ)
  body: ConcreteCategory.epi_of_surjective (cokerπ φ) (cokerπ_surjective φ)

中文:
实例 :
  签名: 满态射 (cokerπ φ)
  定义体: ConcreteCategory.epi_of_surjective (cokerπ φ) (cokerπ_surjective φ)

Depends on / 依赖: ConcreteCategory, ConcreteCategory.epi_of_surjective, epi_of_surjective
-/
instance : Epi (cokerπ φ) := ConcreteCategory.epi_of_surjective (cokerπ φ) (cokerπ_surjective φ)

/--
lemma `comp_cokerπ` / 引理 `comp_cokerπ`

English:
lemma comp_cokerπ
  statement: φ ≫ cokerπ φ = 0
  proof: by
  ext m
  change Submodule.mkQ _ (φ m) = 0
  simp

中文:
引理 comp_cokerπ
  结论: φ ≫ cokerπ φ = 0
  证明: by
  ext m
  change Submodule.mkQ _ (φ m) = 0
  simp
-/
@[simp] lemma comp_cokerπ : φ ≫ cokerπ φ = 0 := by
  ext m
  change Submodule.mkQ _ (φ m) = 0
  simp

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isColimitCoker` / `isColimitCoker` 的定义

English:
definition isColimitCoker
  signature: : IsColimit (CokernelCofork.ofπ (cokerπ φ) (comp_cokerπ φ))
  body: isColimitAux (.ofπ (cokerπ φ) (comp_cokerπ φ))
  (fun s => ofHom <|
    { toLinearMap := φ.hom.range.liftQ s.π.hom.toLinearMap
        (LinearMap.range_le_ker_iff.mpr <| show (φ ≫ s.π).hom.toLinearMap = 0 by
          rw [s.condition]; rw [hom_zero]; rw [ContinuousLinearMap.toLinearMap_zero])
      

中文:
定义 isColimitCoker
  签名: : 是余极限 (余核余叉.ofπ (cokerπ φ) (comp_cokerπ φ))
  定义体: isColimitAux (.ofπ (cokerπ φ) (comp_cokerπ φ))
  (fun s => ofHom <|
    { toLinearMap := φ.hom.range.liftQ s.π.hom.toLinearMap
        (LinearMap.range_le_ker_iff.mpr <| show (φ ≫ s.π).hom.toLinearMap = 0 by
          rw [s.condition]; rw [hom_zero]; rw [ContinuousLinearMap.toLinearMap_zero])
      

Depends on / 依赖: Continuous, Continuous.quotient_lift, ContinuousLinearMap, ContinuousLinearMap.toLinearMap_zero, LinearMap, LinearMap.range_le_ker_iff.mpr, cancel_epi, condition, hom.range.liftQ, hom.toLinearMap, hom_zero, isColimitAux, quotient_lift, range_le_ker_iff, s.condition, toLinearMap, toLinearMap_zero
-/
def isColimitCoker : IsColimit (CokernelCofork.ofπ (cokerπ φ) (comp_cokerπ φ)) :=
  isColimitAux (.ofπ (cokerπ φ) (comp_cokerπ φ))
  (fun s => ofHom <|
    { toLinearMap := φ.hom.range.liftQ s.π.hom.toLinearMap
        (LinearMap.range_le_ker_iff.mpr <| show (φ ≫ s.π).hom.toLinearMap = 0 by
          rw [s.condition]; rw [hom_zero]; rw [ContinuousLinearMap.toLinearMap_zero])
      cont := Continuous.quotient_lift s.π.hom.2 _ })
  (fun s => rfl)
  (fun s m h => by dsimp at h ⊢; rw [← cancel_epi (cokerπ φ), h]; rfl)

end cokernel

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CategoryWithHomology (TopModuleCat R)
  body: by
  constructor
  intro S
  let D₁ : S.LeftHomologyData := ⟨_, _, _, _, _, isLimitKer _, by simp, isColimitCoker _⟩
  let D₂ : S.RightHomologyData := ⟨_, _, _, _, by simp, isColimitCoker _, _, isLimitKer _⟩
  let F := ShortComplex.leftRightHomologyComparison' D₁ D₂
  suffices IsIso F from ⟨⟨.ofIsIs

中文:
实例 :
  签名: 带同调范畴 (顶元素模范畴 R)
  定义体: by
  constructor
  intro S
  let D₁ : S.LeftHomologyData := ⟨_, _, _, _, _, isLimitKer _, by simp, isColimitCoker _⟩
  let D₂ : S.RightHomologyData := ⟨_, _, _, _, by simp, isColimitCoker _, _, isLimitKer _⟩
  let F := ShortComplex.leftRightHomologyComparison' D₁ D₂
  suffices IsIso F from ⟨⟨.ofIsIs

Depends on / 依赖: Bijective, ConcreteCategory, ConcreteCategory.isIso_iff_bijective, Function, Function.Bijective, LeftHomologyData, ModuleCat, RightHomologyData, S.LeftHomologyData, S.RightHomologyData, ShortComplex, ShortComplex.leftRightHomologyComparison, ShortComplex.map_leftRightHo, isColimitCoker, isIso_iff_bijective, isLimitKer, leftRightHomologyComparison, map_leftRightHo, ofIsIsoLeftRightHomologyComparison
-/
instance : CategoryWithHomology (TopModuleCat R) := by
  constructor
  intro S
  let D₁ : S.LeftHomologyData := ⟨_, _, _, _, _, isLimitKer _, by simp, isColimitCoker _⟩
  let D₂ : S.RightHomologyData := ⟨_, _, _, _, by simp, isColimitCoker _, _, isLimitKer _⟩
  let F := ShortComplex.leftRightHomologyComparison' D₁ D₂
  suffices IsIso F from ⟨⟨.ofIsIsoLeftRightHomologyComparison' D₁ D₂⟩⟩
  have hF : Function.Bijective F := by
    change Function.Bijective ((forget₂ _ (ModuleCat R)).map F)
    rw [← ConcreteCategory.isIso_iff_bijective]; rw [ShortComplex.map_leftRightHomologyComparison']
    infer_instance
  have hF' : Topology.IsEmbedding F := by
    refine .of_comp F.1.2 D₂.ι.1.2 ?_
    -- `isEmbedding_of_isOpenQuotientMap_of_isInducing` is the key lemma that shows the two
    -- definitions of homology give the same topology.
    refine isEmbedding_of_isOpenQuotientMap_of_isInducing
      D₁.i (F ≫ D₂.ι) D₁.π D₂.p ?_ .subtypeVal
      (Submodule.isOpenQuotientMap_mkQ _).isQuotientMap
      (Submodule.isOpenQuotientMap_mkQ _)
      (Subtype.val_injective.comp hF.1) ?_
    · rw [← ContinuousLinearMap.coe_comp, ← ContinuousLinearMap.coe_comp,
        ← hom_comp, ← hom_comp, ShortComplex.π_leftRightHomologyComparison'_ι]
    · suffices forall x y, S.g y = 0 -> D₂.p y = D₂.p x -> S.g x = 0 by
        simpa [Set.subset_def, D₁, kerι_apply S.g] using this
      intro x y hy e
      obtain ⟨z, hz⟩ := (Submodule.Quotient.eq _).mp e
      obtain rfl := eq_sub_iff_add_eq.mp hz
      simpa [show S.g (S.f z) = 0 from ConcreteCategory.congr_hom S.zero z] using hy
  rw [← isIso_iff_of_reflects_iso _ (forget₂ (TopModuleCat R) TopCat)]; rw [TopCat.isIso_iff_isHomeomorph]; rw [isHomeomorph_iff_isEmbedding_surjective]
  exact ⟨hF', hF.2⟩

end TopModuleCat
