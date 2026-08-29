/-
Copyright (c) 2026 Thomas Browning, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Subscheme structure on an irreducible component

We define the subscheme structure on an irreducible component of a Noetherian scheme. Typically,
one takes the reduced induced subscheme structure, but this will throw away information if the
irreducible component is not already reduced. Instead, we take the closed subscheme defined by
the kernel of the restriction to the complement of the union of the other irreducible components.
For example, if `X` is irreducible then this will give back the original scheme `X`.

## Main definition
* `AlgebraicGeometry.Scheme.irreducibleComponentIdeal`: The ideal sheaf data associated to an
  irreducible component of a Noetherian scheme.
* `AlgebraicGeometry.Scheme.irreducibleComponent`: The subscheme structure on an irreducible
  component of a Noetherian scheme.

## TODO

Prove that for affine schemes this subscheme structure is defined by the kernel of the
localization away from the union of the other minimal prime ideals.

-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (Z : Set X) (hZ : Z in irreducibleComponents X) [IsNoetherian X]

/--
Definition of `irreducibleComponentOpen` / `irreducibleComponentOpen` 的定义

English:
definition irreducibleComponentOpen
  signature: : Opens X
  body: ⟨(⋃₀ (irreducibleComponents X \ {Z}))ᶜ, by
    rw [Set.sUnion_eq_biUnion]; rw [isOpen_compl_iff]
    exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.sdiff.isClosed_biUnion
      fun W hW => isClosed_of_mem_irreducibleComponents W hW.1⟩

中文:
定义 irreducibleComponentOpen
  签名: : Opens X
  定义体: ⟨(⋃₀ (irreducibleComponents X \ {Z}))ᶜ, by
    rw [Set.sUnion_eq_biUnion]; rw [isOpen_compl_iff]
    exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.sdiff.isClosed_biUnion
      fun W hW => isClosed_of_mem_irreducibleComponents W hW.1⟩

Depends on / 依赖: NoetherianSpace, Set.sUnion_eq_biUnion, TopologicalSpace, TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.sdiff.isClosed_biUnion, finite_irreducibleComponents, irreducibleComponents, isClosed_biUnion, isClosed_of_mem_irreducibleComponents, isOpen_compl_iff, sUnion_eq_biUnion
-/
def irreducibleComponentOpen : Opens X :=
  ⟨(⋃₀ (irreducibleComponents X \ {Z}))ᶜ, by
    rw [Set.sUnion_eq_biUnion]; rw [isOpen_compl_iff]
    exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.sdiff.isClosed_biUnion
      fun W hW => isClosed_of_mem_irreducibleComponents W hW.1⟩

/--
Definition of `irreducibleComponentIdeal` / `irreducibleComponentIdeal` 的定义

English:
definition irreducibleComponentIdeal
  signature: : X.IdealSheafData where
  body: (irreducibleComponentOpen X Z).ι.ker
  supportSet := Z
  supportSet_eq_iInter_zeroLocus := by
    rw [← IdealSheafData.coe_support_eq_eq_iInter_zeroLocus]; rw [Hom.support_ker]; rw [Opens.range_ι]
    exact (closure_sUnion_irreducibleComponents_sdiff_singleton
      TopologicalSpace.NoetherianSpace.

中文:
定义 irreducibleComponentIdeal
  签名: : X.IdealSheafData where
  定义体: (irreducibleComponentOpen X Z).ι.ker
  supportSet := Z
  supportSet_eq_iInter_zeroLocus := by
    rw [← IdealSheafData.coe_support_eq_eq_iInter_zeroLocus]; rw [Hom.support_ker]; rw [Opens.range_ι]
    exact (closure_sUnion_irreducibleComponents_sdiff_singleton
      TopologicalSpace.NoetherianSpace.

Depends on / 依赖: irreducibleComponentOpen
-/
def irreducibleComponentIdeal : X.IdealSheafData where
  __ := (irreducibleComponentOpen X Z).ι.ker
  supportSet := Z
  supportSet_eq_iInter_zeroLocus := by
    rw [← IdealSheafData.coe_support_eq_eq_iInter_zeroLocus]; rw [Hom.support_ker]; rw [Opens.range_ι]
    exact (closure_sUnion_irreducibleComponents_sdiff_singleton
      TopologicalSpace.NoetherianSpace.finite_irreducibleComponents Z hZ).symm

/--
theorem `irreducibleComponentIdeal_def` / 定理 `irreducibleComponentIdeal_def`

English:
theorem irreducibleComponentIdeal_def
  proof: by
  ext
  rfl

中文:
定理 irreducibleComponentIdeal_def
  证明: by
  ext
  rfl
-/
theorem irreducibleComponentIdeal_def :
    irreducibleComponentIdeal X Z hZ = (irreducibleComponentOpen X Z).ι.ker := by
  ext
  rfl

/--
Definition of `irreducibleComponent` / `irreducibleComponent` 的定义

English:
definition irreducibleComponent
  signature: : Scheme
  body: (X.irreducibleComponentIdeal Z hZ).subscheme

中文:
定义 irreducibleComponent
  签名: : 概形
  定义体: (X.irreducibleComponentIdeal Z hZ).subscheme

Depends on / 依赖: X.irreducibleComponentIdeal, irreducibleComponentIdeal, subscheme
-/
noncomputable def irreducibleComponent : Scheme :=
  (X.irreducibleComponentIdeal Z hZ).subscheme

/--
Definition of `irreducibleComponentι` / `irreducibleComponentι` 的定义

English:
definition irreducibleComponentι
  signature: : X.irreducibleComponent Z hZ ⟶ X
  body: (X.irreducibleComponentIdeal Z hZ).subschemeι

中文:
定义 irreducibleComponentι
  签名: : X.irreducibleComponent Z hZ ⟶ X
  定义体: (X.irreducibleComponentIdeal Z hZ).subschemeι

Depends on / 依赖: X.irreducibleComponentIdeal, irreducibleComponentIdeal
-/
noncomputable def irreducibleComponentι : X.irreducibleComponent Z hZ ⟶ X :=
  (X.irreducibleComponentIdeal Z hZ).subschemeι

/--
lemma `irreducibleComponentι_apply` / 引理 `irreducibleComponentι_apply`

English:
lemma irreducibleComponentι_apply
  given: (x : X.irreducibleComponent Z hZ)
  proof: rfl

中文:
引理 irreducibleComponentι_apply
  条件: (x : X.irreducibleComponent Z hZ)
  证明: rfl
-/
lemma irreducibleComponentι_apply (x : X.irreducibleComponent Z hZ) :
    X.irreducibleComponentι Z hZ x = x.1 :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsClosedImmersion (X.irreducibleComponentι Z hZ)
  body: inferInstanceAs (IsClosedImmersion (X.irreducibleComponentIdeal Z hZ).subschemeι)

中文:
实例 :
  签名: 是闭浸入 (X.irreducibleComponentι Z hZ)
  定义体: inferInstanceAs (IsClosedImmersion (X.irreducibleComponentIdeal Z hZ).subschemeι)

Depends on / 依赖: IsClosedImmersion, X.irreducibleComponentIdeal, irreducibleComponentIdeal
-/
instance : IsClosedImmersion (X.irreducibleComponentι Z hZ) :=
  inferInstanceAs (IsClosedImmersion (X.irreducibleComponentIdeal Z hZ).subschemeι)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IrreducibleSpace (X.irreducibleComponent Z hZ)
  body: Subtype.irreducibleSpace hZ.1

include hZ in

中文:
实例 :
  签名: 不可约空间 (X.irreducibleComponent Z hZ)
  定义体: Subtype.irreducibleSpace hZ.1

include hZ in

Depends on / 依赖: Subtype, Subtype.irreducibleSpace, irreducibleSpace
-/
instance : IrreducibleSpace (X.irreducibleComponent Z hZ) :=
  Subtype.irreducibleSpace hZ.1

include hZ in
/--
theorem `irreducibleComponentOpen_eq_top` / 定理 `irreducibleComponentOpen_eq_top`

English:
theorem irreducibleComponentOpen_eq_top
  given: [IrreducibleSpace X]
  proof: by
  rw [irreducibleComponents_eq_singleton]; rw [Set.mem_singleton_iff] at hZ
  simp [irreducibleComponentOpen, irreducibleComponents_eq_singleton, hZ]

中文:
定理 irreducibleComponentOpen_eq_top
  条件: [不可约空间 X]
  证明: by
  rw [irreducibleComponents_eq_singleton]; rw [Set.mem_singleton_iff] at hZ
  simp [irreducibleComponentOpen, irreducibleComponents_eq_singleton, hZ]

Depends on / 依赖: Set.mem_singleton_iff, irreducibleComponentOpen, irreducibleComponents_eq_singleton, mem_singleton_iff
-/
theorem irreducibleComponentOpen_eq_top [IrreducibleSpace X] :
    irreducibleComponentOpen X Z = ⊤ := by
  rw [irreducibleComponents_eq_singleton]; rw [Set.mem_singleton_iff] at hZ
  simp [irreducibleComponentOpen, irreducibleComponents_eq_singleton, hZ]

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IrreducibleSpace
  signature: X] : CategoryTheory.IsIso (X.irreducibleComponentι Z hZ)
  body: by
  have : CategoryTheory.IsIso (irreducibleComponentOpen X Z).ι := by
    rw [irreducibleComponentOpen_eq_top X Z hZ]
    exact X.topIso.isIso_hom
  rw [irreducibleComponentι]; rw [isIso_subschemeι_iff_eq_bot]; rw [irreducibleComponentIdeal_def]; rw [irreducibleComponentOpen_eq_top X Z hZ]
  exact

中文:
实例 [不可约空间
  签名: X] : 范畴论.是同构 (X.irreducibleComponentι Z hZ)
  定义体: by
  have : CategoryTheory.IsIso (irreducibleComponentOpen X Z).ι := by
    rw [irreducibleComponentOpen_eq_top X Z hZ]
    exact X.topIso.isIso_hom
  rw [irreducibleComponentι]; rw [isIso_subschemeι_iff_eq_bot]; rw [irreducibleComponentIdeal_def]; rw [irreducibleComponentOpen_eq_top X Z hZ]
  exact

Depends on / 依赖: CategoryTheory, CategoryTheory.IsIso, X.topIso.hom.ker_eq_bot_of_isIso, X.topIso.isIso_hom, irreducibleComponentIdeal_def, irreducibleComponentOpen, irreducibleComponentOpen_eq_top, isIso_hom, ker_eq_bot_of_isIso, topIso
-/
instance [IrreducibleSpace X] : CategoryTheory.IsIso (X.irreducibleComponentι Z hZ) := by
  have : CategoryTheory.IsIso (irreducibleComponentOpen X Z).ι := by
    rw [irreducibleComponentOpen_eq_top X Z hZ]
    exact X.topIso.isIso_hom
  rw [irreducibleComponentι]; rw [isIso_subschemeι_iff_eq_bot]; rw [irreducibleComponentIdeal_def]; rw [irreducibleComponentOpen_eq_top X Z hZ]
  exact X.topIso.hom.ker_eq_bot_of_isIso

end AlgebraicGeometry.Scheme
