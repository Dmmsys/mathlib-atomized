/-
Copyright (c) 2025 Janos Wolosz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Janos Wolosz
-/
module

public import Mathlib.Algebra.Lie.CartanCriterion
public import Mathlib.Algebra.Lie.Weights.RootSystem
public import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas

/-!
# Lie ideals, invariant root submodules, and simple Lie algebras

Given a semisimple Lie algebra, the lattice of ideals is order isomorphic to the lattice of
Weyl-group-invariant submodules of the corresponding root system. In this file we provide
`LieIdeal.toInvtRootSubmodule`, which constructs the invariant submodule associated to an ideal,
and `LieAlgebra.IsKilling.invtSubmoduleToLieIdeal`, which constructs the ideal associated to an
invariant submodule.

## Main definitions
* `LieIdeal.rootSet`: the set of roots whose root space is contained in a given Lie ideal.
* `LieIdeal.rootSpan`: the submodule of `Dual K H` spanned by `LieIdeal.rootSet`.
* `LieIdeal.toInvtRootSubmodule`: the invariant root submodule associated to an ideal.
* `LieAlgebra.IsKilling.invtSubmoduleToLieIdeal`: constructs a Lie ideal from an invariant
  submodule of the dual space.
* `LieAlgebra.IsKilling.lieIdealOrderIso`: the order isomorphism between Lie ideals and
  invariant root submodules.

## Main results
* `LieAlgebra.IsKilling.restr_inf_cartan_eq_iSup_corootSubmodule`: the intersection of a Lie ideal
  and a Cartan subalgebra is the span of the coroots whose roots have root spaces in the ideal.
* `LieAlgebra.IsKilling.isSimple_iff_isIrreducible`: a Killing Lie algebra is simple if and only
  if its root system is irreducible.
-/

@[expose] public section

namespace LieIdeal

open LieAlgebra LieAlgebra.IsKilling LieModule Module

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra]

/--
lemma `corootSubmodule_le` / 引理 `corootSubmodule_le`

English:
lemma corootSubmodule_le
  statement: (I : LieIdeal K L) {α : Weight K H L}
  proof: by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := (LieSubmodule.mem_map _).mp hx
  have : (⟨a.val, a.property⟩ : H) in corootSpace α := ha
  rw [mem_corootSpace] at this
  refine (Submodule.span_le.mpr ?_) this
  rintro _ ⟨y, hy, _, -, rfl⟩
  exact lie_mem_left K L I y _ (hα hy)

中文:
引理 corootSubmodule_le
  结论: (I : LieIdeal K L) {α : Weight K H L}
  证明: by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := (LieSubmodule.mem_map _).mp hx
  have : (⟨a.val, a.property⟩ : H) in corootSpace α := ha
  rw [mem_corootSpace] at this
  refine (Submodule.span_le.mpr ?_) this
  rintro _ ⟨y, hy, _, -, rfl⟩
  exact lie_mem_left K L I y _ (hα hy)

Depends on / 依赖: LieSubmodule, LieSubmodule.mem_map, Submodule, Submodule.span_le.mpr, a.property, a.val, corootSpace, lie_mem_left, mem_corootSpace, mem_map, property, span_le
-/
lemma corootSubmodule_le (I : LieIdeal K L) {α : Weight K H L}
    (hα : rootSpace H α <= I.restr H) :
    corootSubmodule α <= I.restr H := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := (LieSubmodule.mem_map _).mp hx
  have : (⟨a.val, a.property⟩ : H) in corootSpace α := ha
  rw [mem_corootSpace] at this
  refine (Submodule.span_le.mpr ?_) this
  rintro _ ⟨y, hy, _, -, rfl⟩
  exact lie_mem_left K L I y _ (hα hy)

/--
Definition of `rootSet` / `rootSet` 的定义

English:
definition rootSet
  signature: (I : LieIdeal K L)
  body: { α | rootSpace H α.1 <= I.restr H }

中文:
定义 rootSet
  签名: (I : LieIdeal K L)
  定义体: { α | rootSpace H α.1 <= I.restr H }

Depends on / 依赖: I.restr, rootSpace
-/
def rootSet (I : LieIdeal K L) : Set H.root := { α | rootSpace H α.1 <= I.restr H }

/--
lemma `mem_rootSet` / 引理 `mem_rootSet`

English:
lemma mem_rootSet
  given: {I : LieIdeal K L} {α : H.root}
  proof: Iff.rfl

中文:
引理 mem_rootSet
  条件: {I : LieIdeal K L} {α : H.root}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_rootSet {I : LieIdeal K L} {α : H.root} :
    α in I.rootSet ↔ rootSpace H α.1 <= I.restr H := Iff.rfl

variable [CharZero K] [IsKilling K L] [IsTriangularizable K H L]

/--
Definition of `rootSpan` / `rootSpan` 的定义

English:
definition rootSpan
  signature: (I : LieIdeal K L)
  body: Submodule.span K ((rootSystem H).root '' I.rootSet)

中文:
定义 rootSpan
  签名: (I : LieIdeal K L)
  定义体: Submodule.span K ((rootSystem H).root '' I.rootSet)

Depends on / 依赖: I.rootSet, Submodule, Submodule.span, rootSet, rootSystem
-/
noncomputable def rootSpan (I : LieIdeal K L) : Submodule K (Dual K H) :=
  Submodule.span K ((rootSystem H).root '' I.rootSet)

/--
lemma `rootSpace_le_of_apply_coroot_ne_zero` / 引理 `rootSpace_le_of_apply_coroot_ne_zero`

English:
lemma rootSpace_le_of_apply_coroot_ne_zero
  statement: (I : LieIdeal K L)
  proof: by
  intro y hy
  have : γ (coroot α) • y in I.toSubmodule := by
    rw [← lie_eq_smul_of_mem_rootSpace hy (coroot α)]
    exact lie_mem_left K L I _ y
      (I.corootSubmodule_le hα (coe_coroot_mem_corootSubmodule α))
.mp this exact I.toSubmodule.smul_mem_iff hγ_ne

中文:
引理 rootSpace_le_of_apply_coroot_ne_zero
  结论: (I : LieIdeal K L)
  证明: by
  intro y hy
  have : γ (coroot α) • y in I.toSubmodule := by
    rw [← lie_eq_smul_of_mem_rootSpace hy (coroot α)]
    exact lie_mem_left K L I _ y
      (I.corootSubmodule_le hα (coe_coroot_mem_corootSubmodule α))
.mp this exact I.toSubmodule.smul_mem_iff hγ_ne

Depends on / 依赖: I.corootSubmodule_le, I.toSubmodule, I.toSubmodule.smul_mem_iff, coe_coroot_mem_corootSubmodule, coroot, corootSubmodule_le, lie_eq_smul_of_mem_rootSpace, lie_mem_left, smul_mem_iff, toSubmodule
-/
lemma rootSpace_le_of_apply_coroot_ne_zero (I : LieIdeal K L)
    {α : Weight K H L} (hα : rootSpace H α <= I.restr H)
    {γ : H -> K} (hγ_ne : γ (coroot α) != 0) :
    rootSpace H γ <= I.restr H := by
  intro y hy
  have : γ (coroot α) • y in I.toSubmodule := by
    rw [← lie_eq_smul_of_mem_rootSpace hy (coroot α)]
    exact lie_mem_left K L I _ y
      (I.corootSubmodule_le hα (coe_coroot_mem_corootSubmodule α))
.mp this exact I.toSubmodule.smul_mem_iff hγ_ne

/--
lemma `reflectionPerm_mem_rootSet_iff` / 引理 `reflectionPerm_mem_rootSet_iff`

English:
lemma reflectionPerm_mem_rootSet_iff
  given: (I : LieIdeal K L) (α β : H.root)
  proof: by
  let S := rootSystem H
  suffices h : forall γ δ : H.root, δ in I.rootSet -> S.reflectionPerm γ δ in I.rootSet by
    exact ⟨fun hα => S.reflectionPerm_self β α ▸ h β _ hα, h β α⟩
  intro γ δ hδ
  simp only [mem_rootSet] at hδ ⊢
  by_cases hp : S.pairing δ γ = 0
  · rwa [S.reflectionPerm_eq_of_pairing_eq_zero hp]
  · have hγ := I.rootSpace_le_of_apply_coroot_ne_zero hδ
      (mt S.pairing_eq_zero_iff.mpr hp)
    have h_neg : S.pairing (S.reflectionPerm γ δ) γ != 0 := by
      rwa [← S.pairing_reflectionPerm γ δ γ, S.pairing_reflectionPerm_self_right, neg_ne_zero]
    exact I.rootSpace_le_of_apply_coroot_ne_zero hγ h_neg

中文:
引理 reflectionPerm_mem_rootSet_iff
  条件: (I : LieIdeal K L) (α β : H.root)
  证明: by
  let S := rootSystem H
  suffices h : forall γ δ : H.root, δ in I.rootSet -> S.reflectionPerm γ δ in I.rootSet by
    exact ⟨fun hα => S.reflectionPerm_self β α ▸ h β _ hα, h β α⟩
  intro γ δ hδ
  simp only [mem_rootSet] at hδ ⊢
  by_cases hp : S.pairing δ γ = 0
  · rwa [S.reflectionPerm_eq_of_pairing_eq_zero hp]
  · have hγ := I.rootSpace_le_of_apply_coroot_ne_zero hδ
      (mt S.pairing_eq_zero_iff.mpr hp)
    have h_neg : S.pairing (S.reflectionPerm γ δ) γ != 0 := by
      rwa [← S.pairing_reflectionPerm γ δ γ, S.pairing_reflectionPerm_self_right, neg_ne_zero]
    exact I.rootSpace_le_of_apply_coroot_ne_zero hγ h_neg

Depends on / 依赖: H.root, I.rootSet, I.rootSpace_le_of_apply_coroot_ne_zero, S.pairing, S.pairing_, S.pairing_eq_zero_iff.mpr, S.pairing_reflectionPerm, S.reflectionPerm, S.reflectionPerm_eq_of_pairing_eq_zero, S.reflectionPerm_self, h_neg, mem_rootSet, pairing, pairing_, pairing_eq_zero_iff, pairing_reflectionPerm, reflectionPerm, reflectionPerm_eq_of_pairing_eq_zero, reflectionPerm_self, rootSet
-/
lemma reflectionPerm_mem_rootSet_iff (I : LieIdeal K L) (α β : H.root) :
    (rootSystem H).reflectionPerm β α in I.rootSet ↔ α in I.rootSet := by
  let S := rootSystem H
  suffices h : forall γ δ : H.root, δ in I.rootSet -> S.reflectionPerm γ δ in I.rootSet by
    exact ⟨fun hα => S.reflectionPerm_self β α ▸ h β _ hα, h β α⟩
  intro γ δ hδ
  simp only [mem_rootSet] at hδ ⊢
  by_cases hp : S.pairing δ γ = 0
  · rwa [S.reflectionPerm_eq_of_pairing_eq_zero hp]
  · have hγ := I.rootSpace_le_of_apply_coroot_ne_zero hδ
      (mt S.pairing_eq_zero_iff.mpr hp)
    have h_neg : S.pairing (S.reflectionPerm γ δ) γ != 0 := by
      rwa [← S.pairing_reflectionPerm γ δ γ, S.pairing_reflectionPerm_self_right, neg_ne_zero]
    exact I.rootSpace_le_of_apply_coroot_ne_zero hγ h_neg

/--
lemma `rootSpan_mem_invtRootSubmodule` / 引理 `rootSpan_mem_invtRootSubmodule`

English:
lemma rootSpan_mem_invtRootSubmodule
  given: (I : LieIdeal K L)
  proof: by
  rw [RootPairing.mem_invtRootSubmodule_iff]
  intro β
  rw [Module.End.mem_invtSubmodule]; rw [rootSpan]; rw [Submodule.span_le]
  rintro - ⟨α, hα, rfl⟩
  rw [SetLike.mem_coe]; rw [Submodule.mem_comap]; rw [LinearEquiv.coe_coe]; rw [← RootPairing.root_reflectionPerm]
  exact Submodule.subset_span ⟨_, (I.reflectionPerm_mem_rootSet_iff α β).mpr hα, rfl⟩

中文:
引理 rootSpan_mem_invtRootSubmodule
  条件: (I : LieIdeal K L)
  证明: by
  rw [RootPairing.mem_invtRootSubmodule_iff]
  intro β
  rw [Module.End.mem_invtSubmodule]; rw [rootSpan]; rw [Submodule.span_le]
  rintro - ⟨α, hα, rfl⟩
  rw [SetLike.mem_coe]; rw [Submodule.mem_comap]; rw [LinearEquiv.coe_coe]; rw [← RootPairing.root_reflectionPerm]
  exact Submodule.subset_span ⟨_, (I.reflectionPerm_mem_rootSet_iff α β).mpr hα, rfl⟩

Depends on / 依赖: I.reflectionPerm_mem_rootSet_iff, LinearEquiv, LinearEquiv.coe_coe, Module, Module.End.mem_invtSubmodule, RootPairing, RootPairing.mem_invtRootSubmodule_iff, RootPairing.root_reflectionPerm, SetLike, SetLike.mem_coe, Submodule, Submodule.mem_comap, Submodule.span_le, Submodule.subset_span, coe_coe, mem_coe, mem_comap, mem_invtRootSubmodule_iff, mem_invtSubmodule, reflectionPerm_mem_rootSet_iff
-/
lemma rootSpan_mem_invtRootSubmodule (I : LieIdeal K L) :
    I.rootSpan in (rootSystem H).invtRootSubmodule := by
  rw [RootPairing.mem_invtRootSubmodule_iff]
  intro β
  rw [Module.End.mem_invtSubmodule]; rw [rootSpan]; rw [Submodule.span_le]
  rintro - ⟨α, hα, rfl⟩
  rw [SetLike.mem_coe]; rw [Submodule.mem_comap]; rw [LinearEquiv.coe_coe]; rw [← RootPairing.root_reflectionPerm]
  exact Submodule.subset_span ⟨_, (I.reflectionPerm_mem_rootSet_iff α β).mpr hα, rfl⟩

/--
Definition of `toInvtRootSubmodule` / `toInvtRootSubmodule` 的定义

English:
definition toInvtRootSubmodule
  signature: (I : LieIdeal K L)
  body: ⟨I.rootSpan, I.rootSpan_mem_invtRootSubmodule⟩

@[gcongr]

中文:
定义 toInvtRootSubmodule
  签名: (I : LieIdeal K L)
  定义体: ⟨I.rootSpan, I.rootSpan_mem_invtRootSubmodule⟩

@[gcongr]

Depends on / 依赖: I.rootSpan, I.rootSpan_mem_invtRootSubmodule, rootSpan, rootSpan_mem_invtRootSubmodule
-/
noncomputable def toInvtRootSubmodule (I : LieIdeal K L) :
    (rootSystem H).invtRootSubmodule :=
  ⟨I.rootSpan, I.rootSpan_mem_invtRootSubmodule⟩

@[gcongr]
/--
lemma `toInvtRootSubmodule_mono` / 引理 `toInvtRootSubmodule_mono`

English:
lemma toInvtRootSubmodule_mono
  given: {I J : LieIdeal K L} (h : I <= J)
  proof: Submodule.span_mono (Set.image_mono
    fun α (hα : rootSpace H α.1 <= I.restr H) => hα.trans (show I.restr H <= J.restr H from h))

中文:
引理 toInvtRootSubmodule_mono
  条件: {I J : LieIdeal K L} (h : I <= J)
  证明: Submodule.span_mono (Set.image_mono
    fun α (hα : rootSpace H α.1 <= I.restr H) => hα.trans (show I.restr H <= J.restr H from h))

Depends on / 依赖: J.toInvtRootSubmodule, toInvtRootSubmodule
-/
lemma toInvtRootSubmodule_mono {I J : LieIdeal K L} (h : I <= J) :
    I.toInvtRootSubmodule (H := H) <= J.toInvtRootSubmodule :=
  Submodule.span_mono (Set.image_mono
    fun α (hα : rootSpace H α.1 <= I.restr H) => hα.trans (show I.restr H <= J.restr H from h))

/--
lemma `root_apply_eq_zero_of_notMem_rootSet` / 引理 `root_apply_eq_zero_of_notMem_rootSet`

English:
lemma root_apply_eq_zero_of_notMem_rootSet
  statement: (I : LieIdeal K L)
  proof: by
  simp only [LieIdeal.mem_rootSet] at hβ
  contrapose! hβ
  intro y hy
  have h_smul : (β : Weight K H L) h • y in I.toSubmodule := by
    rw [← lie_eq_smul_of_mem_rootSpace hy h]
    exact lie_mem_left K L I h y hI
  rwa [I.toSubmodule.smul_mem_iff hβ] at h_smul

中文:
引理 root_apply_eq_zero_of_notMem_rootSet
  结论: (I : LieIdeal K L)
  证明: by
  simp only [LieIdeal.mem_rootSet] at hβ
  contrapose! hβ
  intro y hy
  have h_smul : (β : Weight K H L) h • y in I.toSubmodule := by
    rw [← lie_eq_smul_of_mem_rootSpace hy h]
    exact lie_mem_left K L I h y hI
  rwa [I.toSubmodule.smul_mem_iff hβ] at h_smul

Depends on / 依赖: I.toSubmodule, I.toSubmodule.smul_mem_iff, LieIdeal, LieIdeal.mem_rootSet, Weight, contrapose, h_smul, lie_eq_smul_of_mem_rootSpace, lie_mem_left, mem_rootSet, smul_mem_iff, toSubmodule
-/
lemma root_apply_eq_zero_of_notMem_rootSet (I : LieIdeal K L)
    {h : H} (hI : (h : L) in I) {β : H.root} (hβ : β ∉ I.rootSet) :
    (β : Weight K H L) h = 0 := by
  simp only [LieIdeal.mem_rootSet] at hβ
  contrapose! hβ
  intro y hy
  have h_smul : (β : Weight K H L) h • y in I.toSubmodule := by
    rw [← lie_eq_smul_of_mem_rootSpace hy h]
    exact lie_mem_left K L I h y hI
  rwa [I.toSubmodule.smul_mem_iff hβ] at h_smul

/--
lemma `rootSet_apply_coroot_eq_zero_of_notMem_rootSet` / 引理 `rootSet_apply_coroot_eq_zero_of_notMem_rootSet`

English:
lemma rootSet_apply_coroot_eq_zero_of_notMem_rootSet
  statement: (I : LieIdeal K L)
  proof: by
  have h_ker : coroot (α : Weight K H L) in (β : Weight K H L).ker :=
    I.root_apply_eq_zero_of_notMem_rootSet
      (I.corootSubmodule_le hα (coe_coroot_mem_corootSubmodule _)) hβ
  change coroot (β : Weight K H L) in (α : Weight K H L).ker
  rw [← orthogonal_span_coroot_eq_ker]; rw [LinearMap.BilinForm.orthogonal_span_singleton_eq_toLin_ker]; rw [LinearMap.mem_ker]
  exact traceForm_eq_zero_of_mem_ker_of_mem_span_coroot h_ker (Submodule.mem_span_singleton_self _)

中文:
引理 rootSet_apply_coroot_eq_zero_of_notMem_rootSet
  结论: (I : LieIdeal K L)
  证明: by
  have h_ker : coroot (α : Weight K H L) in (β : Weight K H L).ker :=
    I.root_apply_eq_zero_of_notMem_rootSet
      (I.corootSubmodule_le hα (coe_coroot_mem_corootSubmodule _)) hβ
  change coroot (β : Weight K H L) in (α : Weight K H L).ker
  rw [← orthogonal_span_coroot_eq_ker]; rw [LinearMap.BilinForm.orthogonal_span_singleton_eq_toLin_ker]; rw [LinearMap.mem_ker]
  exact traceForm_eq_zero_of_mem_ker_of_mem_span_coroot h_ker (Submodule.mem_span_singleton_self _)

Depends on / 依赖: BilinForm, I.corootSubmodule_le, I.root_apply_eq_zero_of_notMem_rootSet, LinearMap, LinearMap.BilinForm.orthogonal_span_singleton_eq_toLin_ker, LinearMap.mem_ker, Submodule, Submodule.mem_span_singleton_self, Weight, coe_coroot_mem_corootSubmodule, coroot, corootSubmodule_le, h_ker, mem_ker, mem_span_singleton_self, orthogonal_span_coroot_eq_ker, orthogonal_span_singleton_eq_toLin_ker, root_apply_eq_zero_of_notMem_rootSet, traceForm_eq_zero_of_mem_ker_of_mem_span_coroot
-/
lemma rootSet_apply_coroot_eq_zero_of_notMem_rootSet (I : LieIdeal K L)
    {α : H.root} (hα : α in I.rootSet)
    {β : H.root} (hβ : β ∉ I.rootSet) :
    (α : Weight K H L) (coroot β) = 0 := by
  have h_ker : coroot (α : Weight K H L) in (β : Weight K H L).ker :=
    I.root_apply_eq_zero_of_notMem_rootSet
      (I.corootSubmodule_le hα (coe_coroot_mem_corootSubmodule _)) hβ
  change coroot (β : Weight K H L) in (α : Weight K H L).ker
  rw [← orthogonal_span_coroot_eq_ker]; rw [LinearMap.BilinForm.orthogonal_span_singleton_eq_toLin_ker]; rw [LinearMap.mem_ker]
  exact traceForm_eq_zero_of_mem_ker_of_mem_span_coroot h_ker (Submodule.mem_span_singleton_self _)

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `restr_inf_cartan_eq_biSup_corootSubmodule` / 引理 `restr_inf_cartan_eq_biSup_corootSubmodule`

English:
lemma restr_inf_cartan_eq_biSup_corootSubmodule
  given: (I : LieIdeal K L)
  proof: by
  refine le_antisymm ?_ (iSup₂_le fun _ hα =>
    le_inf (I.corootSubmodule_le hα) LieSubmodule.map_incl_le)
  intro x ⟨hxI, hxH⟩
  let f : H.root -> LieIdeal K H := fun α => corootSpace α.1
  set span_I_roots := ⨆ α in I.rootSet, f α
  set span_compl_roots := ⨆ (β : H.root) (_ : β ∉ I.rootSet), f β
  have h_split : span_I_roots ⊔ span_compl_roots = ⨆ α, f α :=
    (iSup_split f (· in I.rootSet)).symm
  have h_top : span_I_roots ⊔ span_compl_roots = ⊤ := by
    rw [h_split]; rw [eq_top_iff]; rw [← biSup_corootSpace_eq_top]
    exact iSup₂_le fun α hα => le_iSup_of_le ⟨α, by simpa [LieSubalgebra.root] using hα⟩ le_rfl
  have hspan_I_roots_incl : LieSubmodule.map H.toLieSubmodule.incl span_I_roots =
      ⨆ α in I.rootSet, corootSubmodule α.1 := by
    change LieSubmodule.map _ (⨆ α in I.rootSet, f α) = ⨆ α in I.rootSet, _
    simp_rw [LieSubmodule.map_iSup]; rfl
  have hspan_compl_roots_vanish (μ : H.root) (hμ : μ in I.rootSet) :
      span_compl_roots.toSubmodule <= μ.1.ker := by
    have : span_compl_roots.toSubmodule = ⨆ β ∉ I.rootSet, (f β).toSubmodule := by
      simp_rw [span_compl_roots, LieSubmodule.iSup_toSubmodule]
    rw [this]
    exact iSup₂_le fun γ hγ => by
      rw [coe_corootSpace_eq_span_singleton]; rw [Submodule.span_singleton_le_iff_mem]; rw [LinearMap.mem_ker]
      exact I.rootSet_apply_coroot_eq_zero_of_notMem_rootSet hμ hγ
  have hx_top : (⟨x, hxH⟩ : H) in span_I_roots ⊔ span_compl_roots := h_top ▸ trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx_top
  have haI : (a : L) in I :=
    (iSup₂_le (fun _ hα => I.corootSubmodule_le hα) :
      ⨆ α in I.rootSet, corootSubmodule α.1 <= _)
      (hspan_I_roots_incl ▸ LieSubmodule.mem_map_of_mem ha)
  have hbI : (b : L) in I := by
    have h_sum : (a : L) + b = x := congr_arg Subtype.val hab
    have h_b_eq : (b : L) = x - a := by rw [← h_sum, add_sub_cancel_left]
    rw [h_b_eq]; exact I.toSubmodule.sub_mem hxI haI
  suffices b = 0 by
    subst this; simp only [add_zero] at hab; subst hab
    exact hspan_I_roots_incl ▸ LieSubmodule.mem_map_of_mem ha
  suffices b in ⨅ α : Weight K H L, α.ker by simpa [iInf_ker_weight_eq_bot] using this
  refine (Submodule.mem_iInf _).mpr fun μ => ?_
  by_cases hμ : μ.IsNonZero
  · have hμ_root : μ in H.root := by simpa [LieSubalgebra.root] using hμ
    by_cases hμI : (⟨μ, hμ_root⟩ : H.root) in I.rootSet
    · exact hspan_compl_roots_vanish ⟨μ, hμ_root⟩ hμI hb
    · exact I.root_apply_eq_zero_of_notMem_rootSet hbI hμI
  · simp only [Weight.IsNonZero, not_not] at hμ
    exact LinearMap.mem_ker.mpr (congr_fun hμ b)

中文:
引理 restr_inf_cartan_eq_biSup_corootSubmodule
  条件: (I : LieIdeal K L)
  证明: by
  refine le_antisymm ?_ (iSup₂_le fun _ hα =>
    le_inf (I.corootSubmodule_le hα) LieSubmodule.map_incl_le)
  intro x ⟨hxI, hxH⟩
  let f : H.root -> LieIdeal K H := fun α => corootSpace α.1
  set span_I_roots := ⨆ α in I.rootSet, f α
  set span_compl_roots := ⨆ (β : H.root) (_ : β ∉ I.rootSet), f β
  have h_split : span_I_roots ⊔ span_compl_roots = ⨆ α, f α :=
    (iSup_split f (· in I.rootSet)).symm
  have h_top : span_I_roots ⊔ span_compl_roots = ⊤ := by
    rw [h_split]; rw [eq_top_iff]; rw [← biSup_corootSpace_eq_top]
    exact iSup₂_le fun α hα => le_iSup_of_le ⟨α, by simpa [LieSubalgebra.root] using hα⟩ le_rfl
  have hspan_I_roots_incl : LieSubmodule.map H.toLieSubmodule.incl span_I_roots =
      ⨆ α in I.rootSet, corootSubmodule α.1 := by
    change LieSubmodule.map _ (⨆ α in I.rootSet, f α) = ⨆ α in I.rootSet, _
    simp_rw [LieSubmodule.map_iSup]; rfl
  have hspan_compl_roots_vanish (μ : H.root) (hμ : μ in I.rootSet) :
      span_compl_roots.toSubmodule <= μ.1.ker := by
    have : span_compl_roots.toSubmodule = ⨆ β ∉ I.rootSet, (f β).toSubmodule := by
      simp_rw [span_compl_roots, LieSubmodule.iSup_toSubmodule]
    rw [this]
    exact iSup₂_le fun γ hγ => by
      rw [coe_corootSpace_eq_span_singleton]; rw [Submodule.span_singleton_le_iff_mem]; rw [LinearMap.mem_ker]
      exact I.rootSet_apply_coroot_eq_zero_of_notMem_rootSet hμ hγ
  have hx_top : (⟨x, hxH⟩ : H) in span_I_roots ⊔ span_compl_roots := h_top ▸ trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx_top
  have haI : (a : L) in I :=
    (iSup₂_le (fun _ hα => I.corootSubmodule_le hα) :
      ⨆ α in I.rootSet, corootSubmodule α.1 <= _)
      (hspan_I_roots_incl ▸ LieSubmodule.mem_map_of_mem ha)
  have hbI : (b : L) in I := by
    have h_sum : (a : L) + b = x := congr_arg Subtype.val hab
    have h_b_eq : (b : L) = x - a := by rw [← h_sum, add_sub_cancel_left]
    rw [h_b_eq]; exact I.toSubmodule.sub_mem hxI haI
  suffices b = 0 by
    subst this; simp only [add_zero] at hab; subst hab
    exact hspan_I_roots_incl ▸ LieSubmodule.mem_map_of_mem ha
  suffices b in ⨅ α : Weight K H L, α.ker by simpa [iInf_ker_weight_eq_bot] using this
  refine (Submodule.mem_iInf _).mpr fun μ => ?_
  by_cases hμ : μ.IsNonZero
  · have hμ_root : μ in H.root := by simpa [LieSubalgebra.root] using hμ
    by_cases hμI : (⟨μ, hμ_root⟩ : H.root) in I.rootSet
    · exact hspan_compl_roots_vanish ⟨μ, hμ_root⟩ hμI hb
    · exact I.root_apply_eq_zero_of_notMem_rootSet hbI hμI
  · simp only [Weight.IsNonZero, not_not] at hμ
    exact LinearMap.mem_ker.mpr (congr_fun hμ b)

Depends on / 依赖: H.root, I.corootSubmodule_le, I.rootSet, LieIdeal, LieSubmodule, LieSubmodule.map_incl_le, biSup_corootSpace_eq, corootSpace, corootSubmodule_le, eq_top_iff, h_split, h_top, iSup_split, le_antisymm, le_inf, map_incl_le, rootSet, span_I_roots, span_compl_roots
-/
lemma restr_inf_cartan_eq_biSup_corootSubmodule (I : LieIdeal K L) :
    I.restr H ⊓ H.toLieSubmodule = ⨆ α in I.rootSet, corootSubmodule α.1 := by
  refine le_antisymm ?_ (iSup₂_le fun _ hα =>
    le_inf (I.corootSubmodule_le hα) LieSubmodule.map_incl_le)
  intro x ⟨hxI, hxH⟩
  let f : H.root -> LieIdeal K H := fun α => corootSpace α.1
  set span_I_roots := ⨆ α in I.rootSet, f α
  set span_compl_roots := ⨆ (β : H.root) (_ : β ∉ I.rootSet), f β
  have h_split : span_I_roots ⊔ span_compl_roots = ⨆ α, f α :=
    (iSup_split f (· in I.rootSet)).symm
  have h_top : span_I_roots ⊔ span_compl_roots = ⊤ := by
    rw [h_split]; rw [eq_top_iff]; rw [← biSup_corootSpace_eq_top]
    exact iSup₂_le fun α hα => le_iSup_of_le ⟨α, by simpa [LieSubalgebra.root] using hα⟩ le_rfl
  have hspan_I_roots_incl : LieSubmodule.map H.toLieSubmodule.incl span_I_roots =
      ⨆ α in I.rootSet, corootSubmodule α.1 := by
    change LieSubmodule.map _ (⨆ α in I.rootSet, f α) = ⨆ α in I.rootSet, _
    simp_rw [LieSubmodule.map_iSup]; rfl
  have hspan_compl_roots_vanish (μ : H.root) (hμ : μ in I.rootSet) :
      span_compl_roots.toSubmodule <= μ.1.ker := by
    have : span_compl_roots.toSubmodule = ⨆ β ∉ I.rootSet, (f β).toSubmodule := by
      simp_rw [span_compl_roots, LieSubmodule.iSup_toSubmodule]
    rw [this]
    exact iSup₂_le fun γ hγ => by
      rw [coe_corootSpace_eq_span_singleton]; rw [Submodule.span_singleton_le_iff_mem]; rw [LinearMap.mem_ker]
      exact I.rootSet_apply_coroot_eq_zero_of_notMem_rootSet hμ hγ
  have hx_top : (⟨x, hxH⟩ : H) in span_I_roots ⊔ span_compl_roots := h_top ▸ trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx_top
  have haI : (a : L) in I :=
    (iSup₂_le (fun _ hα => I.corootSubmodule_le hα) :
      ⨆ α in I.rootSet, corootSubmodule α.1 <= _)
      (hspan_I_roots_incl ▸ LieSubmodule.mem_map_of_mem ha)
  have hbI : (b : L) in I := by
    have h_sum : (a : L) + b = x := congr_arg Subtype.val hab
    have h_b_eq : (b : L) = x - a := by rw [← h_sum, add_sub_cancel_left]
    rw [h_b_eq]; exact I.toSubmodule.sub_mem hxI haI
  suffices b = 0 by
    subst this; simp only [add_zero] at hab; subst hab
    exact hspan_I_roots_incl ▸ LieSubmodule.mem_map_of_mem ha
  suffices b in ⨅ α : Weight K H L, α.ker by simpa [iInf_ker_weight_eq_bot] using this
  refine (Submodule.mem_iInf _).mpr fun μ => ?_
  by_cases hμ : μ.IsNonZero
  · have hμ_root : μ in H.root := by simpa [LieSubalgebra.root] using hμ
    by_cases hμI : (⟨μ, hμ_root⟩ : H.root) in I.rootSet
    · exact hspan_compl_roots_vanish ⟨μ, hμ_root⟩ hμI hb
    · exact I.root_apply_eq_zero_of_notMem_rootSet hbI hμI
  · simp only [Weight.IsNonZero, not_not] at hμ
    exact LinearMap.mem_ker.mpr (congr_fun hμ b)

/--
lemma `mem_rootSet_of_mem_rootSpan` / 引理 `mem_rootSet_of_mem_rootSpan`

English:
lemma mem_rootSet_of_mem_rootSpan
  statement: (I : LieIdeal K L)
  proof: by
  by_contra hα_not
  have hα_nz := H.isNonZero_coe_root α
  have : I.rootSpan <= LinearMap.ker (Dual.eval K H (coroot (α : Weight K H L))) := by
    rw [LieIdeal.rootSpan]; rw [Submodule.span_le]
    rintro _ ⟨γ, hγ, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, Dual.eval_apply, rootSystem_root_apply]
    exact I.rootSet_apply_coroot_eq_zero_of_notMem_rootSet hγ hα_not
  have := LinearMap.mem_ker.mp (this hα_span)
  simp only [Dual.eval_apply, Weight.toLinear_apply, root_apply_coroot hα_nz] at this
  exact absurd this two_ne_zero

中文:
引理 mem_rootSet_of_mem_rootSpan
  结论: (I : LieIdeal K L)
  证明: by
  by_contra hα_not
  have hα_nz := H.isNonZero_coe_root α
  have : I.rootSpan <= LinearMap.ker (Dual.eval K H (coroot (α : Weight K H L))) := by
    rw [LieIdeal.rootSpan]; rw [Submodule.span_le]
    rintro _ ⟨γ, hγ, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, Dual.eval_apply, rootSystem_root_apply]
    exact I.rootSet_apply_coroot_eq_zero_of_notMem_rootSet hγ hα_not
  have := LinearMap.mem_ker.mp (this hα_span)
  simp only [Dual.eval_apply, Weight.toLinear_apply, root_apply_coroot hα_nz] at this
  exact absurd this two_ne_zero

Depends on / 依赖: Dual.eval, Dual.eval_apply, H.isNonZero_coe_root, I.rootSet_apply_coroot_eq_zero_of_notMem_rootSet, I.rootSpan, LieIdeal, LieIdeal.rootSpan, LinearMap, LinearMap.ker, LinearMap.mem_ker, LinearMap.mem_ker.mp, SetLike, SetLike.mem_coe, Submodule, Submodule.span_le, Weight, Weight.toLinear_apply, coroot, eval_apply, isNonZero_coe_root
-/
lemma mem_rootSet_of_mem_rootSpan (I : LieIdeal K L)
    {α : H.root} (hα_span : (α : Dual K H) in I.rootSpan) :
    α in I.rootSet := by
  by_contra hα_not
  have hα_nz := H.isNonZero_coe_root α
  have : I.rootSpan <= LinearMap.ker (Dual.eval K H (coroot (α : Weight K H L))) := by
    rw [LieIdeal.rootSpan]; rw [Submodule.span_le]
    rintro _ ⟨γ, hγ, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, Dual.eval_apply, rootSystem_root_apply]
    exact I.rootSet_apply_coroot_eq_zero_of_notMem_rootSet hγ hα_not
  have := LinearMap.mem_ker.mp (this hα_span)
  simp only [Dual.eval_apply, Weight.toLinear_apply, root_apply_coroot hα_nz] at this
  exact absurd this two_ne_zero

/--
lemma `restr_eq_iSup_sl2SubmoduleOfRoot` / 引理 `restr_eq_iSup_sl2SubmoduleOfRoot`

English:
lemma restr_eq_iSup_sl2SubmoduleOfRoot
  given: (I : LieIdeal K L)
  proof: by
  apply le_antisymm
  · rw [lieIdeal_eq_inf_cartan_sup_biSup_rootSpace, restr_inf_cartan_eq_biSup_corootSubmodule]
    apply sup_le
    · exact iSup₂_le fun β hβ => le_iSup₂_of_le β hβ
        (by rw [sl2SubmoduleOfRoot_eq_sup]; exact le_sup_right)
    · exact iSup₂_le fun α hα => le_iSup₂_of_le α hα
        (by rw [sl2SubmoduleOfRoot_eq_sup]; exact le_sup_of_le_left le_sup_left)
  · exact iSup₂_le fun α hα => by
      rw [sl2SubmoduleOfRoot_eq_sup]
      refine sup_le (sup_le ?_ ?_) ?_
      · exact hα
      · apply I.rootSpace_le_of_apply_coroot_ne_zero hα
        simp [Pi.neg_apply, root_apply_coroot (H.isNonZero_coe_root α)]
      · exact I.corootSubmodule_le hα

中文:
引理 restr_eq_iSup_sl2SubmoduleOfRoot
  条件: (I : LieIdeal K L)
  证明: by
  apply le_antisymm
  · rw [lieIdeal_eq_inf_cartan_sup_biSup_rootSpace, restr_inf_cartan_eq_biSup_corootSubmodule]
    apply sup_le
    · exact iSup₂_le fun β hβ => le_iSup₂_of_le β hβ
        (by rw [sl2SubmoduleOfRoot_eq_sup]; exact le_sup_right)
    · exact iSup₂_le fun α hα => le_iSup₂_of_le α hα
        (by rw [sl2SubmoduleOfRoot_eq_sup]; exact le_sup_of_le_left le_sup_left)
  · exact iSup₂_le fun α hα => by
      rw [sl2SubmoduleOfRoot_eq_sup]
      refine sup_le (sup_le ?_ ?_) ?_
      · exact hα
      · apply I.rootSpace_le_of_apply_coroot_ne_zero hα
        simp [Pi.neg_apply, root_apply_coroot (H.isNonZero_coe_root α)]
      · exact I.corootSubmodule_le hα

Depends on / 依赖: I.rootSpace_le_of_apply_coroot_n, le_antisymm, le_sup_left, le_sup_of_le_left, le_sup_right, lieIdeal_eq_inf_cartan_sup_biSup_rootSpace, restr_inf_cartan_eq_biSup_corootSubmodule, rootSpace_le_of_apply_coroot_n, sl2SubmoduleOfRoot_eq_sup, sup_le
-/
lemma restr_eq_iSup_sl2SubmoduleOfRoot (I : LieIdeal K L) :
    I.restr H =
      ⨆ (α : H.root) (_ : α in I.rootSet), sl2SubmoduleOfRoot (H.isNonZero_coe_root α) := by
  apply le_antisymm
  · rw [lieIdeal_eq_inf_cartan_sup_biSup_rootSpace, restr_inf_cartan_eq_biSup_corootSubmodule]
    apply sup_le
    · exact iSup₂_le fun β hβ => le_iSup₂_of_le β hβ
        (by rw [sl2SubmoduleOfRoot_eq_sup]; exact le_sup_right)
    · exact iSup₂_le fun α hα => le_iSup₂_of_le α hα
        (by rw [sl2SubmoduleOfRoot_eq_sup]; exact le_sup_of_le_left le_sup_left)
  · exact iSup₂_le fun α hα => by
      rw [sl2SubmoduleOfRoot_eq_sup]
      refine sup_le (sup_le ?_ ?_) ?_
      · exact hα
      · apply I.rootSpace_le_of_apply_coroot_ne_zero hα
        simp [Pi.neg_apply, root_apply_coroot (H.isNonZero_coe_root α)]
      · exact I.corootSubmodule_le hα

end LieIdeal

namespace LieAlgebra.IsKilling

open LieAlgebra LieModule Module

variable {K L : Type*} [Field K] [CharZero K]
  [LieRing L] [LieAlgebra K L] [FiniteDimensional K L] [IsKilling K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]

section aux

variable (q : Submodule K (Dual K H))
  (hq : forall i, q in End.invtSubmodule ((rootSystem H).reflection i))
  (χ : Weight K H L)
  (x_χ m_α : L) (hx_χ : x_χ in genWeightSpace L χ)
  (α : Weight K H L) (hαq : ↑α in q) (hα₀ : α.IsNonZero)

section

variable
  (w_plus : χ.toLinear + α.toLinear != 0)
  (w_minus : χ.toLinear - α.toLinear != 0)
  (w_chi : χ.toLinear != 0)
  (m_pos m_neg : L)
  (y : H) (hy : y in corootSpace α)
  (h_bracket_sum : ⁅x_χ, m_α⁆ = ⁅x_χ, m_pos⁆ + ⁅x_χ, m_neg⁆ + ⁅x_χ, (y : L)⁆)
  (h_pos_containment : ⁅x_χ, m_pos⁆ in genWeightSpace L (⇑χ + ⇑α))
  (h_neg_containment : ⁅x_χ, m_neg⁆ in genWeightSpace L (⇑χ - ⇑α))

include hx_χ w_plus w_minus w_chi h_bracket_sum h_pos_containment h_neg_containment hαq

/--
theorem `chi_in_q_aux` / 定理 `chi_in_q_aux`

English:
theorem chi_in_q_aux
  given: (h_chi_in_q : ↑χ in q)
  proof: by
  have h_h_containment : ⁅x_χ, (y : L)⁆ in genWeightSpace L χ := by
    have h_zero_weight : H.toLieSubmodule.incl y in genWeightSpace L (0 : H -> K) := by
      apply toLieSubmodule_le_rootSpace_zero
      exact y.property
    convert! lie_mem_genWeightSpace_of_mem_genWeightSpace hx_χ h_zero_weight
    ext h; simp
  have h_bracket_decomp : ⁅x_χ, m_α⁆ in
      genWeightSpace L (χ.toLinear + α.toLinear) ⊔
      genWeightSpace L (χ.toLinear - α.toLinear) ⊔ genWeightSpace L χ := by
    rw [h_bracket_sum]
    exact add_mem (add_mem
      (Submodule.mem_sup_left (Submodule.mem_sup_left h_pos_containment))
      (Submodule.mem_sup_left (Submodule.mem_sup_right h_neg_containment)))
      (Submodule.mem_sup_right h_h_containment)
  let I := ⨆ β : {β : Weight K H L // ↑β in q ∧ β.IsNonZero}, sl2SubmoduleOfRoot β.2.2
  have genWeightSpace_le_I (β_lin : H ->ₗ[K] K) (hβ_in_q : β_lin in q)
      (hβ_ne_zero : β_lin != 0) : genWeightSpace L β_lin <= I := by
    by_cases h_trivial : genWeightSpace L β_lin = ⊥
    · simp [h_trivial]
    · let β : Weight K H L := ⟨β_lin, h_trivial⟩
      have hβ_nonzero : β.IsNonZero := Weight.coe_toLinear_ne_zero_iff.mp hβ_ne_zero
      refine le_trans ?_ (le_iSup _ ⟨β, hβ_in_q, hβ_nonzero⟩)
      rw [sl2SubmoduleOfRoot_eq_sup]
      exact le_sup_of_le_left (le_sup_of_le_left le_rfl)
  have h_plus_contain : genWeightSpace L (χ.toLinear + α.toLinear) <= I :=
    genWeightSpace_le_I _ (q.add_mem h_chi_in_q hαq) w_plus
  have h_minus_contain : genWeightSpace L (χ.toLinear - α.toLinear) <= I :=
    genWeightSpace_le_I _ (by
      have : -α.toLinear = (-1 : K) • α.toLinear := by simp
      rw [sub_eq_add_neg]; rw [this]
      exact q.add_mem h_chi_in_q (q.smul_mem (-1) hαq)) w_minus
  have h_chi_contain : genWeightSpace L χ.toLinear <= I :=
    genWeightSpace_le_I _ h_chi_in_q (fun h_eq => (w_chi h_eq).elim)
  exact sup_le (sup_le h_plus_contain h_minus_contain) h_chi_contain h_bracket_decomp

include hq hα₀ hy

中文:
定理 chi_in_q_aux
  条件: (h_chi_in_q : ↑χ in q)
  证明: by
  have h_h_containment : ⁅x_χ, (y : L)⁆ in genWeightSpace L χ := by
    have h_zero_weight : H.toLieSubmodule.incl y in genWeightSpace L (0 : H -> K) := by
      apply toLieSubmodule_le_rootSpace_zero
      exact y.property
    convert! lie_mem_genWeightSpace_of_mem_genWeightSpace hx_χ h_zero_weight
    ext h; simp
  have h_bracket_decomp : ⁅x_χ, m_α⁆ in
      genWeightSpace L (χ.toLinear + α.toLinear) ⊔
      genWeightSpace L (χ.toLinear - α.toLinear) ⊔ genWeightSpace L χ := by
    rw [h_bracket_sum]
    exact add_mem (add_mem
      (Submodule.mem_sup_left (Submodule.mem_sup_left h_pos_containment))
      (Submodule.mem_sup_left (Submodule.mem_sup_right h_neg_containment)))
      (Submodule.mem_sup_right h_h_containment)
  let I := ⨆ β : {β : Weight K H L // ↑β in q ∧ β.IsNonZero}, sl2SubmoduleOfRoot β.2.2
  have genWeightSpace_le_I (β_lin : H ->ₗ[K] K) (hβ_in_q : β_lin in q)
      (hβ_ne_zero : β_lin != 0) : genWeightSpace L β_lin <= I := by
    by_cases h_trivial : genWeightSpace L β_lin = ⊥
    · simp [h_trivial]
    · let β : Weight K H L := ⟨β_lin, h_trivial⟩
      have hβ_nonzero : β.IsNonZero := Weight.coe_toLinear_ne_zero_iff.mp hβ_ne_zero
      refine le_trans ?_ (le_iSup _ ⟨β, hβ_in_q, hβ_nonzero⟩)
      rw [sl2SubmoduleOfRoot_eq_sup]
      exact le_sup_of_le_left (le_sup_of_le_left le_rfl)
  have h_plus_contain : genWeightSpace L (χ.toLinear + α.toLinear) <= I :=
    genWeightSpace_le_I _ (q.add_mem h_chi_in_q hαq) w_plus
  have h_minus_contain : genWeightSpace L (χ.toLinear - α.toLinear) <= I :=
    genWeightSpace_le_I _ (by
      have : -α.toLinear = (-1 : K) • α.toLinear := by simp
      rw [sub_eq_add_neg]; rw [this]
      exact q.add_mem h_chi_in_q (q.smul_mem (-1) hαq)) w_minus
  have h_chi_contain : genWeightSpace L χ.toLinear <= I :=
    genWeightSpace_le_I _ h_chi_in_q (fun h_eq => (w_chi h_eq).elim)
  exact sup_le (sup_le h_plus_contain h_minus_contain) h_chi_contain h_bracket_decomp

include hq hα₀ hy

Depends on / 依赖: IsStablyFree, IsStablyFree.exist_free_prod, LinearMap, LinearMap.ext, LinearMap.fst, LinearMap.inl, Projective, Projective.of_split, exist_free_prod, of_split
-/
private theorem chi_in_q_aux (h_chi_in_q : ↑χ in q) :
    ⁅x_χ, m_α⁆ in ⨆ α : {α : Weight K H L // ↑α in q ∧ α.IsNonZero}, sl2SubmoduleOfRoot α.2.2 := by
  have h_h_containment : ⁅x_χ, (y : L)⁆ in genWeightSpace L χ := by
    have h_zero_weight : H.toLieSubmodule.incl y in genWeightSpace L (0 : H -> K) := by
      apply toLieSubmodule_le_rootSpace_zero
      exact y.property
    convert! lie_mem_genWeightSpace_of_mem_genWeightSpace hx_χ h_zero_weight
    ext h; simp
  have h_bracket_decomp : ⁅x_χ, m_α⁆ in
      genWeightSpace L (χ.toLinear + α.toLinear) ⊔
      genWeightSpace L (χ.toLinear - α.toLinear) ⊔ genWeightSpace L χ := by
    rw [h_bracket_sum]
    exact add_mem (add_mem
      (Submodule.mem_sup_left (Submodule.mem_sup_left h_pos_containment))
      (Submodule.mem_sup_left (Submodule.mem_sup_right h_neg_containment)))
      (Submodule.mem_sup_right h_h_containment)
  let I := ⨆ β : {β : Weight K H L // ↑β in q ∧ β.IsNonZero}, sl2SubmoduleOfRoot β.2.2
  have genWeightSpace_le_I (β_lin : H ->ₗ[K] K) (hβ_in_q : β_lin in q)
      (hβ_ne_zero : β_lin != 0) : genWeightSpace L β_lin <= I := by
    by_cases h_trivial : genWeightSpace L β_lin = ⊥
    · simp [h_trivial]
    · let β : Weight K H L := ⟨β_lin, h_trivial⟩
      have hβ_nonzero : β.IsNonZero := Weight.coe_toLinear_ne_zero_iff.mp hβ_ne_zero
      refine le_trans ?_ (le_iSup _ ⟨β, hβ_in_q, hβ_nonzero⟩)
      rw [sl2SubmoduleOfRoot_eq_sup]
      exact le_sup_of_le_left (le_sup_of_le_left le_rfl)
  have h_plus_contain : genWeightSpace L (χ.toLinear + α.toLinear) <= I :=
    genWeightSpace_le_I _ (q.add_mem h_chi_in_q hαq) w_plus
  have h_minus_contain : genWeightSpace L (χ.toLinear - α.toLinear) <= I :=
    genWeightSpace_le_I _ (by
      have : -α.toLinear = (-1 : K) • α.toLinear := by simp
      rw [sub_eq_add_neg]; rw [this]
      exact q.add_mem h_chi_in_q (q.smul_mem (-1) hαq)) w_minus
  have h_chi_contain : genWeightSpace L χ.toLinear <= I :=
    genWeightSpace_le_I _ h_chi_in_q (fun h_eq => (w_chi h_eq).elim)
  exact sup_le (sup_le h_plus_contain h_minus_contain) h_chi_contain h_bracket_decomp

include hq hα₀ hy

/--
theorem `chi_not_in_q_aux` / 定理 `chi_not_in_q_aux`

English:
theorem chi_not_in_q_aux
  given: (h_chi_not_in_q : ↑χ ∉ q)
  proof: by
  let S := rootSystem H
  have exists_root_index (γ : Weight K H L) (hγ : γ.IsNonZero) : exists i, S.root i = ↑γ :=
    ⟨⟨γ, by simpa [LieSubalgebra.root]⟩, rfl⟩
  have h_plus_bot : genWeightSpace L (χ.toLinear + α.toLinear) = ⊥ := by
    by_contra h_plus_ne_bot
    let γ : Weight K H L := ⟨χ.toLinear + α.toLinear, h_plus_ne_bot⟩
    have hγ_nonzero : γ.IsNonZero := Weight.coe_toLinear_ne_zero_iff.mp w_plus
    obtain ⟨i, hi⟩ := exists_root_index χ (Weight.coe_toLinear_ne_zero_iff.mp w_chi)
    obtain ⟨j, hj⟩ := exists_root_index α hα₀
    have h_sum_in_range : S.root i + S.root j in Set.range S.root := by
      rw [hi]; rw [hj]
      exact ⟨⟨γ, by simpa [LieSubalgebra.root]⟩, rfl⟩
    have h_equiv := RootPairing.root_mem_submodule_iff_of_add_mem_invtSubmodule
      ⟨q, by rw [RootPairing.mem_invtRootSubmodule_iff]; exact hq⟩ h_sum_in_range
    rw [hi] at h_equiv
    exact h_chi_not_in_q (h_equiv.mpr (by rw [hj]; exact hαq))
  have h_minus_bot : genWeightSpace L (χ.toLinear - α.toLinear) = ⊥ := by
    by_contra h_minus_ne_bot
    let γ : Weight K H L := ⟨χ.toLinear - α.toLinear, h_minus_ne_bot⟩
    have hγ_nonzero : γ.IsNonZero := Weight.coe_toLinear_ne_zero_iff.mp w_minus
    obtain ⟨i, hi⟩ := exists_root_index χ (Weight.coe_toLinear_ne_zero_iff.mp w_chi)
    obtain ⟨j, hj⟩ := exists_root_index (-α) (Weight.IsNonZero.neg hα₀)
    have h_sum_in_range : S.root i + S.root j in Set.range S.root := by
      rw [hi]; rw [hj]; rw [Weight.toLinear_neg]; rw [← sub_eq_add_neg]
      exact ⟨⟨γ, by simpa [LieSubalgebra.root]⟩, rfl⟩
    have h_equiv := RootPairing.root_mem_submodule_iff_of_add_mem_invtSubmodule
      ⟨q, by rw [RootPairing.mem_invtRootSubmodule_iff]; exact hq⟩ h_sum_in_range
    rw [hi] at h_equiv
    exact h_chi_not_in_q (h_equiv.mpr (by
      rw [hj]; rw [Weight.toLinear_neg]
      convert q.smul_mem (-1) hαq
      rw [neg_smul]; rw [one_smul]))
  obtain ⟨i, hi⟩ := exists_root_index χ (Weight.coe_toLinear_ne_zero_iff.mp w_chi)
  obtain ⟨j, hj⟩ := exists_root_index α hα₀
  have h_pairing_zero : S.pairing i j = 0 := by
    apply RootPairing.pairing_eq_zero_of_add_notMem_of_sub_notMem S
    · intro h_eq; exact w_minus (by rw [← hi, ← hj, h_eq, sub_self])
    · intro h_eq; exact w_plus (by rw [← hi, ← hj, h_eq, neg_add_cancel])
    · intro ⟨idx, hidx⟩
      have : genWeightSpace L (S.root idx) != ⊥ := idx.val.genWeightSpace_ne_bot
      rw [hidx]; rw [hi]; rw [hj] at this
      exact this h_plus_bot
    · intro ⟨idx, hidx⟩
      have : genWeightSpace L (S.root idx) != ⊥ := idx.val.genWeightSpace_ne_bot
      rw [hidx]; rw [hi]; rw [hj] at this
      exact this h_minus_bot
  have h_pos_zero : ⁅x_χ, m_pos⁆ = 0 := by
    have h_in_bot : ⁅x_χ, m_pos⁆ in (⊥ : LieSubmodule K H L) := by
      rw [← h_plus_bot]
      exact h_pos_containment
    rwa [LieSubmodule.mem_bot] at h_in_bot
  have h_neg_zero : ⁅x_χ, m_neg⁆ = 0 := by
    have h_in_bot : ⁅x_χ, m_neg⁆ in (⊥ : LieSubmodule K H L) := by
      rw [← h_minus_bot]
      exact h_neg_containment
    rwa [LieSubmodule.mem_bot] at h_in_bot
  have h_bracket_zero : ⁅x_χ, (y : L)⁆ = 0 := by
    have h_chi_coroot_zero : χ (coroot α) = 0 := by
      have h_pairing_eq : S.pairing i j = i.1 (coroot j.1) := by
        rw [rootSystem_pairing_apply]
      rw [h_pairing_zero] at h_pairing_eq
      have w_eq {w₁ w₂ : Weight K H L} (h : w₁.toLinear = w₂.toLinear) : w₁ = w₂ := by
        apply Weight.ext; intro x; exact LinearMap.ext_iff.mp h x
      have hi_val : i.1 = χ := w_eq (by rw [← hi]; rfl)
      have hj_val : j.1 = α := w_eq (by rw [← hj]; rfl)
      rw [hi_val]; rw [hj_val] at h_pairing_eq
      exact h_pairing_eq.symm
    have h_lie_eq_smul : ⁅(y : L), x_χ⁆ = χ y • x_χ := lie_eq_smul_of_mem_rootSpace hx_χ y
    have h_chi_h_zero : χ y = 0 := by
obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp by
        rw [← coe_corootSpace_eq_span_singleton α]; rw [LieSubmodule.mem_toSubmodule]
        exact hy
      rw [← hc]; rw [map_smul]; rw [h_chi_coroot_zero]; rw [smul_zero]
    have h_bracket_elem : ⁅x_χ, (y : L)⁆ = 0 := by
      rw [← lie_skew]; rw [h_lie_eq_smul]; rw [h_chi_h_zero]; rw [zero_smul]; rw [neg_zero]
    exact h_bracket_elem
  rw [h_bracket_sum]; rw [h_pos_zero]; rw [h_neg_zero]; rw [h_bracket_zero]
  simp only [add_zero, zero_mem]

中文:
定理 chi_not_in_q_aux
  条件: (h_chi_not_in_q : ↑χ ∉ q)
  证明: by
  let S := rootSystem H
  have exists_root_index (γ : Weight K H L) (hγ : γ.IsNonZero) : exists i, S.root i = ↑γ :=
    ⟨⟨γ, by simpa [LieSubalgebra.root]⟩, rfl⟩
  have h_plus_bot : genWeightSpace L (χ.toLinear + α.toLinear) = ⊥ := by
    by_contra h_plus_ne_bot
    let γ : Weight K H L := ⟨χ.toLinear + α.toLinear, h_plus_ne_bot⟩
    have hγ_nonzero : γ.IsNonZero := Weight.coe_toLinear_ne_zero_iff.mp w_plus
    obtain ⟨i, hi⟩ := exists_root_index χ (Weight.coe_toLinear_ne_zero_iff.mp w_chi)
    obtain ⟨j, hj⟩ := exists_root_index α hα₀
    have h_sum_in_range : S.root i + S.root j in Set.range S.root := by
      rw [hi]; rw [hj]
      exact ⟨⟨γ, by simpa [LieSubalgebra.root]⟩, rfl⟩
    have h_equiv := RootPairing.root_mem_submodule_iff_of_add_mem_invtSubmodule
      ⟨q, by rw [RootPairing.mem_invtRootSubmodule_iff]; exact hq⟩ h_sum_in_range
    rw [hi] at h_equiv
    exact h_chi_not_in_q (h_equiv.mpr (by rw [hj]; exact hαq))
  have h_minus_bot : genWeightSpace L (χ.toLinear - α.toLinear) = ⊥ := by
    by_contra h_minus_ne_bot
    let γ : Weight K H L := ⟨χ.toLinear - α.toLinear, h_minus_ne_bot⟩
    have hγ_nonzero : γ.IsNonZero := Weight.coe_toLinear_ne_zero_iff.mp w_minus
    obtain ⟨i, hi⟩ := exists_root_index χ (Weight.coe_toLinear_ne_zero_iff.mp w_chi)
    obtain ⟨j, hj⟩ := exists_root_index (-α) (Weight.IsNonZero.neg hα₀)
    have h_sum_in_range : S.root i + S.root j in Set.range S.root := by
      rw [hi]; rw [hj]; rw [Weight.toLinear_neg]; rw [← sub_eq_add_neg]
      exact ⟨⟨γ, by simpa [LieSubalgebra.root]⟩, rfl⟩
    have h_equiv := RootPairing.root_mem_submodule_iff_of_add_mem_invtSubmodule
      ⟨q, by rw [RootPairing.mem_invtRootSubmodule_iff]; exact hq⟩ h_sum_in_range
    rw [hi] at h_equiv
    exact h_chi_not_in_q (h_equiv.mpr (by
      rw [hj]; rw [Weight.toLinear_neg]
      convert q.smul_mem (-1) hαq
      rw [neg_smul]; rw [one_smul]))
  obtain ⟨i, hi⟩ := exists_root_index χ (Weight.coe_toLinear_ne_zero_iff.mp w_chi)
  obtain ⟨j, hj⟩ := exists_root_index α hα₀
  have h_pairing_zero : S.pairing i j = 0 := by
    apply RootPairing.pairing_eq_zero_of_add_notMem_of_sub_notMem S
    · intro h_eq; exact w_minus (by rw [← hi, ← hj, h_eq, sub_self])
    · intro h_eq; exact w_plus (by rw [← hi, ← hj, h_eq, neg_add_cancel])
    · intro ⟨idx, hidx⟩
      have : genWeightSpace L (S.root idx) != ⊥ := idx.val.genWeightSpace_ne_bot
      rw [hidx]; rw [hi]; rw [hj] at this
      exact this h_plus_bot
    · intro ⟨idx, hidx⟩
      have : genWeightSpace L (S.root idx) != ⊥ := idx.val.genWeightSpace_ne_bot
      rw [hidx]; rw [hi]; rw [hj] at this
      exact this h_minus_bot
  have h_pos_zero : ⁅x_χ, m_pos⁆ = 0 := by
    have h_in_bot : ⁅x_χ, m_pos⁆ in (⊥ : LieSubmodule K H L) := by
      rw [← h_plus_bot]
      exact h_pos_containment
    rwa [LieSubmodule.mem_bot] at h_in_bot
  have h_neg_zero : ⁅x_χ, m_neg⁆ = 0 := by
    have h_in_bot : ⁅x_χ, m_neg⁆ in (⊥ : LieSubmodule K H L) := by
      rw [← h_minus_bot]
      exact h_neg_containment
    rwa [LieSubmodule.mem_bot] at h_in_bot
  have h_bracket_zero : ⁅x_χ, (y : L)⁆ = 0 := by
    have h_chi_coroot_zero : χ (coroot α) = 0 := by
      have h_pairing_eq : S.pairing i j = i.1 (coroot j.1) := by
        rw [rootSystem_pairing_apply]
      rw [h_pairing_zero] at h_pairing_eq
      have w_eq {w₁ w₂ : Weight K H L} (h : w₁.toLinear = w₂.toLinear) : w₁ = w₂ := by
        apply Weight.ext; intro x; exact LinearMap.ext_iff.mp h x
      have hi_val : i.1 = χ := w_eq (by rw [← hi]; rfl)
      have hj_val : j.1 = α := w_eq (by rw [← hj]; rfl)
      rw [hi_val]; rw [hj_val] at h_pairing_eq
      exact h_pairing_eq.symm
    have h_lie_eq_smul : ⁅(y : L), x_χ⁆ = χ y • x_χ := lie_eq_smul_of_mem_rootSpace hx_χ y
    have h_chi_h_zero : χ y = 0 := by
obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp by
        rw [← coe_corootSpace_eq_span_singleton α]; rw [LieSubmodule.mem_toSubmodule]
        exact hy
      rw [← hc]; rw [map_smul]; rw [h_chi_coroot_zero]; rw [smul_zero]
    have h_bracket_elem : ⁅x_χ, (y : L)⁆ = 0 := by
      rw [← lie_skew]; rw [h_lie_eq_smul]; rw [h_chi_h_zero]; rw [zero_smul]; rw [neg_zero]
    exact h_bracket_elem
  rw [h_bracket_sum]; rw [h_pos_zero]; rw [h_neg_zero]; rw [h_bracket_zero]
  simp only [add_zero, zero_mem]
-/
private theorem chi_not_in_q_aux (h_chi_not_in_q : ↑χ ∉ q) :
    ⁅x_χ, m_α⁆ in ⨆ α : {α : Weight K H L // ↑α in q ∧ α.IsNonZero}, sl2SubmoduleOfRoot α.2.2 := by
  let S := rootSystem H
  have exists_root_index (γ : Weight K H L) (hγ : γ.IsNonZero) : exists i, S.root i = ↑γ :=
    ⟨⟨γ, by simpa [LieSubalgebra.root]⟩, rfl⟩
  have h_plus_bot : genWeightSpace L (χ.toLinear + α.toLinear) = ⊥ := by
    by_contra h_plus_ne_bot
    let γ : Weight K H L := ⟨χ.toLinear + α.toLinear, h_plus_ne_bot⟩
    have hγ_nonzero : γ.IsNonZero := Weight.coe_toLinear_ne_zero_iff.mp w_plus
    obtain ⟨i, hi⟩ := exists_root_index χ (Weight.coe_toLinear_ne_zero_iff.mp w_chi)
    obtain ⟨j, hj⟩ := exists_root_index α hα₀
    have h_sum_in_range : S.root i + S.root j in Set.range S.root := by
      rw [hi]; rw [hj]
      exact ⟨⟨γ, by simpa [LieSubalgebra.root]⟩, rfl⟩
    have h_equiv := RootPairing.root_mem_submodule_iff_of_add_mem_invtSubmodule
      ⟨q, by rw [RootPairing.mem_invtRootSubmodule_iff]; exact hq⟩ h_sum_in_range
    rw [hi] at h_equiv
    exact h_chi_not_in_q (h_equiv.mpr (by rw [hj]; exact hαq))
  have h_minus_bot : genWeightSpace L (χ.toLinear - α.toLinear) = ⊥ := by
    by_contra h_minus_ne_bot
    let γ : Weight K H L := ⟨χ.toLinear - α.toLinear, h_minus_ne_bot⟩
    have hγ_nonzero : γ.IsNonZero := Weight.coe_toLinear_ne_zero_iff.mp w_minus
    obtain ⟨i, hi⟩ := exists_root_index χ (Weight.coe_toLinear_ne_zero_iff.mp w_chi)
    obtain ⟨j, hj⟩ := exists_root_index (-α) (Weight.IsNonZero.neg hα₀)
    have h_sum_in_range : S.root i + S.root j in Set.range S.root := by
      rw [hi]; rw [hj]; rw [Weight.toLinear_neg]; rw [← sub_eq_add_neg]
      exact ⟨⟨γ, by simpa [LieSubalgebra.root]⟩, rfl⟩
    have h_equiv := RootPairing.root_mem_submodule_iff_of_add_mem_invtSubmodule
      ⟨q, by rw [RootPairing.mem_invtRootSubmodule_iff]; exact hq⟩ h_sum_in_range
    rw [hi] at h_equiv
    exact h_chi_not_in_q (h_equiv.mpr (by
      rw [hj]; rw [Weight.toLinear_neg]
      convert q.smul_mem (-1) hαq
      rw [neg_smul]; rw [one_smul]))
  obtain ⟨i, hi⟩ := exists_root_index χ (Weight.coe_toLinear_ne_zero_iff.mp w_chi)
  obtain ⟨j, hj⟩ := exists_root_index α hα₀
  have h_pairing_zero : S.pairing i j = 0 := by
    apply RootPairing.pairing_eq_zero_of_add_notMem_of_sub_notMem S
    · intro h_eq; exact w_minus (by rw [← hi, ← hj, h_eq, sub_self])
    · intro h_eq; exact w_plus (by rw [← hi, ← hj, h_eq, neg_add_cancel])
    · intro ⟨idx, hidx⟩
      have : genWeightSpace L (S.root idx) != ⊥ := idx.val.genWeightSpace_ne_bot
      rw [hidx]; rw [hi]; rw [hj] at this
      exact this h_plus_bot
    · intro ⟨idx, hidx⟩
      have : genWeightSpace L (S.root idx) != ⊥ := idx.val.genWeightSpace_ne_bot
      rw [hidx]; rw [hi]; rw [hj] at this
      exact this h_minus_bot
  have h_pos_zero : ⁅x_χ, m_pos⁆ = 0 := by
    have h_in_bot : ⁅x_χ, m_pos⁆ in (⊥ : LieSubmodule K H L) := by
      rw [← h_plus_bot]
      exact h_pos_containment
    rwa [LieSubmodule.mem_bot] at h_in_bot
  have h_neg_zero : ⁅x_χ, m_neg⁆ = 0 := by
    have h_in_bot : ⁅x_χ, m_neg⁆ in (⊥ : LieSubmodule K H L) := by
      rw [← h_minus_bot]
      exact h_neg_containment
    rwa [LieSubmodule.mem_bot] at h_in_bot
  have h_bracket_zero : ⁅x_χ, (y : L)⁆ = 0 := by
    have h_chi_coroot_zero : χ (coroot α) = 0 := by
      have h_pairing_eq : S.pairing i j = i.1 (coroot j.1) := by
        rw [rootSystem_pairing_apply]
      rw [h_pairing_zero] at h_pairing_eq
      have w_eq {w₁ w₂ : Weight K H L} (h : w₁.toLinear = w₂.toLinear) : w₁ = w₂ := by
        apply Weight.ext; intro x; exact LinearMap.ext_iff.mp h x
      have hi_val : i.1 = χ := w_eq (by rw [← hi]; rfl)
      have hj_val : j.1 = α := w_eq (by rw [← hj]; rfl)
      rw [hi_val]; rw [hj_val] at h_pairing_eq
      exact h_pairing_eq.symm
    have h_lie_eq_smul : ⁅(y : L), x_χ⁆ = χ y • x_χ := lie_eq_smul_of_mem_rootSpace hx_χ y
    have h_chi_h_zero : χ y = 0 := by
obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp by
        rw [← coe_corootSpace_eq_span_singleton α]; rw [LieSubmodule.mem_toSubmodule]
        exact hy
      rw [← hc]; rw [map_smul]; rw [h_chi_coroot_zero]; rw [smul_zero]
    have h_bracket_elem : ⁅x_χ, (y : L)⁆ = 0 := by
      rw [← lie_skew]; rw [h_lie_eq_smul]; rw [h_chi_h_zero]; rw [zero_smul]; rw [neg_zero]
    exact h_bracket_elem
  rw [h_bracket_sum]; rw [h_pos_zero]; rw [h_neg_zero]; rw [h_bracket_zero]
  simp only [add_zero, zero_mem]

end

set_option backward.isDefEq.respectTransparency.types false in
include hq hx_χ hαq in
/--
theorem `invtSubmoduleToLieIdeal_aux` / 定理 `invtSubmoduleToLieIdeal_aux`

English:
theorem invtSubmoduleToLieIdeal_aux
  given: (hm_α : m_α in sl2SubmoduleOfRoot hα₀)
  proof: by
  have hm_α_original : m_α in sl2SubmoduleOfRoot hα₀ := hm_α
  rw [sl2SubmoduleOfRoot_eq_sup] at hm_α
  obtain ⟨m_αneg, hm_αneg, m_h, hm_h, hm_eq⟩ := Submodule.mem_sup.mp hm_α
  obtain ⟨m_pos, hm_pos, m_neg, hm_neg, hm_αneg_eq⟩ := Submodule.mem_sup.mp hm_αneg
  have hm_α_decomp : m_α = m_pos + m_neg + m_h := by
    rw [← hm_eq]; rw [← hm_αneg_eq]
  have h_bracket_sum : ⁅x_χ, m_α⁆ = ⁅x_χ, m_pos⁆ + ⁅x_χ, m_neg⁆ + ⁅x_χ, m_h⁆ := by
    rw [hm_α_decomp]; rw [lie_add]; rw [lie_add]
  by_cases w_plus : χ.toLinear + α.toLinear = 0
  · apply LieSubmodule.mem_iSup_of_mem ⟨α, hαq, hα₀⟩
    have hx_χ_in_sl2 : x_χ in sl2SubalgebraOfRoot hα₀ := by
      obtain ⟨h, e, f, ht, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα₀
      rw [mem_sl2SubalgebraOfRoot_iff hα₀ ht he hf]
      have hx_χ_neg : x_χ in genWeightSpace L (-α.toLinear) := by
        rw [← (add_eq_zero_iff_eq_neg.mp w_plus)]
        exact hx_χ
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' ⟨f, hf⟩ (by simp [ht.f_ne_zero])).mp
        (finrank_rootSpace_eq_one (-α) (by simpa using hα₀)) ⟨x_χ, hx_χ_neg⟩
      exact ⟨0, c, 0, by simpa using hc.symm⟩
    apply LieSubalgebra.lie_mem <;> [exact hx_χ_in_sl2; exact hm_α_original]
  by_cases w_minus : χ.toLinear - α.toLinear = 0
  · apply LieSubmodule.mem_iSup_of_mem ⟨α, hαq, hα₀⟩
    have hx_χ_in_sl2 : x_χ in sl2SubalgebraOfRoot hα₀ := by
      obtain ⟨h, e, f, ht, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα₀
      rw [mem_sl2SubalgebraOfRoot_iff hα₀ ht he hf]
      have hx_χ_pos : x_χ in genWeightSpace L α.toLinear := by
        rw [← (sub_eq_zero.mp w_minus)]
        exact hx_χ
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' ⟨e, he⟩ (by simp [ht.e_ne_zero])).mp
        (finrank_rootSpace_eq_one α hα₀) ⟨x_χ, hx_χ_pos⟩
      exact ⟨c, 0, 0, by simpa using hc.symm⟩
    apply LieSubalgebra.lie_mem <;> [exact hx_χ_in_sl2; exact hm_α_original]
  by_cases w_chi : χ.toLinear = 0
  · have hx_χ_in_H : x_χ in H.toLieSubmodule := by
      rw [← rootSpace_zero_eq K L H]
      convert! hx_χ; ext h; simp only [Pi.zero_apply]
      have h_apply : (χ.toLinear : H -> K) h = 0 := by rw [w_chi, LinearMap.zero_apply]
      exact h_apply.symm
    apply LieSubmodule.mem_iSup_of_mem ⟨α, hαq, hα₀⟩
    rw [← (by rfl : ⁅(⟨x_χ]; rw [hx_χ_in_H⟩ : H)]; rw [m_α⁆ = ⁅x_χ]; rw [m_α⁆)]
    exact (sl2SubmoduleOfRoot hα₀).lie_mem hm_α_original
  have h_pos_containment : ⁅x_χ, m_pos⁆ in genWeightSpace L (χ.toLinear + α.toLinear) :=
    lie_mem_genWeightSpace_of_mem_genWeightSpace hx_χ hm_pos
  have h_neg_containment : ⁅x_χ, m_neg⁆ in genWeightSpace L (χ.toLinear - α.toLinear) := by
    rw [sub_eq_add_neg]; exact lie_mem_genWeightSpace_of_mem_genWeightSpace hx_χ hm_neg
  obtain ⟨y, hy, rfl⟩ := hm_h
  by_cases h_chi_in_q : ↑χ in q
  · exact chi_in_q_aux q χ x_χ m_α hx_χ α hαq w_plus w_minus w_chi m_pos m_neg y h_bracket_sum
      h_pos_containment h_neg_containment h_chi_in_q
  · exact chi_not_in_q_aux q hq χ x_χ m_α hx_χ α hαq hα₀ w_plus w_minus w_chi m_pos m_neg y hy
      h_bracket_sum h_pos_containment h_neg_containment h_chi_in_q

中文:
定理 invtSubmoduleToLieIdeal_aux
  条件: (hm_α : m_α in sl2SubmoduleOfRoot hα₀)
  证明: by
  have hm_α_original : m_α in sl2SubmoduleOfRoot hα₀ := hm_α
  rw [sl2SubmoduleOfRoot_eq_sup] at hm_α
  obtain ⟨m_αneg, hm_αneg, m_h, hm_h, hm_eq⟩ := Submodule.mem_sup.mp hm_α
  obtain ⟨m_pos, hm_pos, m_neg, hm_neg, hm_αneg_eq⟩ := Submodule.mem_sup.mp hm_αneg
  have hm_α_decomp : m_α = m_pos + m_neg + m_h := by
    rw [← hm_eq]; rw [← hm_αneg_eq]
  have h_bracket_sum : ⁅x_χ, m_α⁆ = ⁅x_χ, m_pos⁆ + ⁅x_χ, m_neg⁆ + ⁅x_χ, m_h⁆ := by
    rw [hm_α_decomp]; rw [lie_add]; rw [lie_add]
  by_cases w_plus : χ.toLinear + α.toLinear = 0
  · apply LieSubmodule.mem_iSup_of_mem ⟨α, hαq, hα₀⟩
    have hx_χ_in_sl2 : x_χ in sl2SubalgebraOfRoot hα₀ := by
      obtain ⟨h, e, f, ht, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα₀
      rw [mem_sl2SubalgebraOfRoot_iff hα₀ ht he hf]
      have hx_χ_neg : x_χ in genWeightSpace L (-α.toLinear) := by
        rw [← (add_eq_zero_iff_eq_neg.mp w_plus)]
        exact hx_χ
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' ⟨f, hf⟩ (by simp [ht.f_ne_zero])).mp
        (finrank_rootSpace_eq_one (-α) (by simpa using hα₀)) ⟨x_χ, hx_χ_neg⟩
      exact ⟨0, c, 0, by simpa using hc.symm⟩
    apply LieSubalgebra.lie_mem <;> [exact hx_χ_in_sl2; exact hm_α_original]
  by_cases w_minus : χ.toLinear - α.toLinear = 0
  · apply LieSubmodule.mem_iSup_of_mem ⟨α, hαq, hα₀⟩
    have hx_χ_in_sl2 : x_χ in sl2SubalgebraOfRoot hα₀ := by
      obtain ⟨h, e, f, ht, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα₀
      rw [mem_sl2SubalgebraOfRoot_iff hα₀ ht he hf]
      have hx_χ_pos : x_χ in genWeightSpace L α.toLinear := by
        rw [← (sub_eq_zero.mp w_minus)]
        exact hx_χ
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' ⟨e, he⟩ (by simp [ht.e_ne_zero])).mp
        (finrank_rootSpace_eq_one α hα₀) ⟨x_χ, hx_χ_pos⟩
      exact ⟨c, 0, 0, by simpa using hc.symm⟩
    apply LieSubalgebra.lie_mem <;> [exact hx_χ_in_sl2; exact hm_α_original]
  by_cases w_chi : χ.toLinear = 0
  · have hx_χ_in_H : x_χ in H.toLieSubmodule := by
      rw [← rootSpace_zero_eq K L H]
      convert! hx_χ; ext h; simp only [Pi.zero_apply]
      have h_apply : (χ.toLinear : H -> K) h = 0 := by rw [w_chi, LinearMap.zero_apply]
      exact h_apply.symm
    apply LieSubmodule.mem_iSup_of_mem ⟨α, hαq, hα₀⟩
    rw [← (by rfl : ⁅(⟨x_χ]; rw [hx_χ_in_H⟩ : H)]; rw [m_α⁆ = ⁅x_χ]; rw [m_α⁆)]
    exact (sl2SubmoduleOfRoot hα₀).lie_mem hm_α_original
  have h_pos_containment : ⁅x_χ, m_pos⁆ in genWeightSpace L (χ.toLinear + α.toLinear) :=
    lie_mem_genWeightSpace_of_mem_genWeightSpace hx_χ hm_pos
  have h_neg_containment : ⁅x_χ, m_neg⁆ in genWeightSpace L (χ.toLinear - α.toLinear) := by
    rw [sub_eq_add_neg]; exact lie_mem_genWeightSpace_of_mem_genWeightSpace hx_χ hm_neg
  obtain ⟨y, hy, rfl⟩ := hm_h
  by_cases h_chi_in_q : ↑χ in q
  · exact chi_in_q_aux q χ x_χ m_α hx_χ α hαq w_plus w_minus w_chi m_pos m_neg y h_bracket_sum
      h_pos_containment h_neg_containment h_chi_in_q
  · exact chi_not_in_q_aux q hq χ x_χ m_α hx_χ α hαq hα₀ w_plus w_minus w_chi m_pos m_neg y hy
      h_bracket_sum h_pos_containment h_neg_containment h_chi_in_q
-/
private theorem invtSubmoduleToLieIdeal_aux (hm_α : m_α in sl2SubmoduleOfRoot hα₀) :
    ⁅x_χ, m_α⁆ in ⨆ α : {α : Weight K H L // ↑α in q ∧ α.IsNonZero}, sl2SubmoduleOfRoot α.2.2 := by
  have hm_α_original : m_α in sl2SubmoduleOfRoot hα₀ := hm_α
  rw [sl2SubmoduleOfRoot_eq_sup] at hm_α
  obtain ⟨m_αneg, hm_αneg, m_h, hm_h, hm_eq⟩ := Submodule.mem_sup.mp hm_α
  obtain ⟨m_pos, hm_pos, m_neg, hm_neg, hm_αneg_eq⟩ := Submodule.mem_sup.mp hm_αneg
  have hm_α_decomp : m_α = m_pos + m_neg + m_h := by
    rw [← hm_eq]; rw [← hm_αneg_eq]
  have h_bracket_sum : ⁅x_χ, m_α⁆ = ⁅x_χ, m_pos⁆ + ⁅x_χ, m_neg⁆ + ⁅x_χ, m_h⁆ := by
    rw [hm_α_decomp]; rw [lie_add]; rw [lie_add]
  by_cases w_plus : χ.toLinear + α.toLinear = 0
  · apply LieSubmodule.mem_iSup_of_mem ⟨α, hαq, hα₀⟩
    have hx_χ_in_sl2 : x_χ in sl2SubalgebraOfRoot hα₀ := by
      obtain ⟨h, e, f, ht, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα₀
      rw [mem_sl2SubalgebraOfRoot_iff hα₀ ht he hf]
      have hx_χ_neg : x_χ in genWeightSpace L (-α.toLinear) := by
        rw [← (add_eq_zero_iff_eq_neg.mp w_plus)]
        exact hx_χ
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' ⟨f, hf⟩ (by simp [ht.f_ne_zero])).mp
        (finrank_rootSpace_eq_one (-α) (by simpa using hα₀)) ⟨x_χ, hx_χ_neg⟩
      exact ⟨0, c, 0, by simpa using hc.symm⟩
    apply LieSubalgebra.lie_mem <;> [exact hx_χ_in_sl2; exact hm_α_original]
  by_cases w_minus : χ.toLinear - α.toLinear = 0
  · apply LieSubmodule.mem_iSup_of_mem ⟨α, hαq, hα₀⟩
    have hx_χ_in_sl2 : x_χ in sl2SubalgebraOfRoot hα₀ := by
      obtain ⟨h, e, f, ht, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hα₀
      rw [mem_sl2SubalgebraOfRoot_iff hα₀ ht he hf]
      have hx_χ_pos : x_χ in genWeightSpace L α.toLinear := by
        rw [← (sub_eq_zero.mp w_minus)]
        exact hx_χ
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' ⟨e, he⟩ (by simp [ht.e_ne_zero])).mp
        (finrank_rootSpace_eq_one α hα₀) ⟨x_χ, hx_χ_pos⟩
      exact ⟨c, 0, 0, by simpa using hc.symm⟩
    apply LieSubalgebra.lie_mem <;> [exact hx_χ_in_sl2; exact hm_α_original]
  by_cases w_chi : χ.toLinear = 0
  · have hx_χ_in_H : x_χ in H.toLieSubmodule := by
      rw [← rootSpace_zero_eq K L H]
      convert! hx_χ; ext h; simp only [Pi.zero_apply]
      have h_apply : (χ.toLinear : H -> K) h = 0 := by rw [w_chi, LinearMap.zero_apply]
      exact h_apply.symm
    apply LieSubmodule.mem_iSup_of_mem ⟨α, hαq, hα₀⟩
    rw [← (by rfl : ⁅(⟨x_χ]; rw [hx_χ_in_H⟩ : H)]; rw [m_α⁆ = ⁅x_χ]; rw [m_α⁆)]
    exact (sl2SubmoduleOfRoot hα₀).lie_mem hm_α_original
  have h_pos_containment : ⁅x_χ, m_pos⁆ in genWeightSpace L (χ.toLinear + α.toLinear) :=
    lie_mem_genWeightSpace_of_mem_genWeightSpace hx_χ hm_pos
  have h_neg_containment : ⁅x_χ, m_neg⁆ in genWeightSpace L (χ.toLinear - α.toLinear) := by
    rw [sub_eq_add_neg]; exact lie_mem_genWeightSpace_of_mem_genWeightSpace hx_χ hm_neg
  obtain ⟨y, hy, rfl⟩ := hm_h
  by_cases h_chi_in_q : ↑χ in q
  · exact chi_in_q_aux q χ x_χ m_α hx_χ α hαq w_plus w_minus w_chi m_pos m_neg y h_bracket_sum
      h_pos_containment h_neg_containment h_chi_in_q
  · exact chi_not_in_q_aux q hq χ x_χ m_α hx_χ α hαq hα₀ w_plus w_minus w_chi m_pos m_neg y hy
      h_bracket_sum h_pos_containment h_neg_containment h_chi_in_q

end aux

/--
Definition of `invtSubmoduleToLieIdeal` / `invtSubmoduleToLieIdeal` 的定义

English:
definition invtSubmoduleToLieIdeal
  signature: (q : Submodule K (Dual K H))
  body: ⨆ α : {α : Weight K H L // ↑α in q ∧ α.IsNonZero}, sl2SubmoduleOfRoot α.2.2
  lie_mem := by
    intro x m hm
    have hx : x in ⨆ χ : Weight K H L, genWeightSpace L χ := by
      simp [LieModule.iSup_genWeightSpace_eq_top']
    induction hx using LieSubmodule.iSup_induction' with
    | mem χ x_χ hx_χ =>
      induction hm using LieSubmodule.iSup_induction' with
      | mem α m_α hm_α => exact invtSubmoduleToLieIdeal_aux q hq χ x_χ m_α hx_χ α.1 α.2.1 α.2.2 hm_α
      | zero =>
        simp only [Submodule.carrier_eq_coe, lie_zero, SetLike.mem_coe, zero_mem]
      | add m₁ m₂ _ _ ih₁ ih₂ =>
        simp only [lie_add, Submodule.carrier_eq_coe, SetLike.mem_coe] at ih₁ ih₂ ⊢
        exact add_mem ih₁ ih₂
    | zero =>
      simp only [Submodule.carrier_eq_coe, zero_lie, SetLike.mem_coe, zero_mem]
    | add x₁ x₂ _ _ ih₁ ih₂ =>
      simp only [add_lie, Submodule.carrier_eq_coe, SetLike.mem_coe] at ih₁ ih₂ ⊢
      exact add_mem ih₁ ih₂

中文:
定义 invtSubmoduleToLieIdeal
  签名: (q : 子模 K (对偶 K H))
  定义体: ⨆ α : {α : Weight K H L // ↑α in q ∧ α.IsNonZero}, sl2SubmoduleOfRoot α.2.2
  lie_mem := by
    intro x m hm
    have hx : x in ⨆ χ : Weight K H L, genWeightSpace L χ := by
      simp [LieModule.iSup_genWeightSpace_eq_top']
    induction hx using LieSubmodule.iSup_induction' with
    | mem χ x_χ hx_χ =>
      induction hm using LieSubmodule.iSup_induction' with
      | mem α m_α hm_α => exact invtSubmoduleToLieIdeal_aux q hq χ x_χ m_α hx_χ α.1 α.2.1 α.2.2 hm_α
      | zero =>
        simp only [Submodule.carrier_eq_coe, lie_zero, SetLike.mem_coe, zero_mem]
      | add m₁ m₂ _ _ ih₁ ih₂ =>
        simp only [lie_add, Submodule.carrier_eq_coe, SetLike.mem_coe] at ih₁ ih₂ ⊢
        exact add_mem ih₁ ih₂
    | zero =>
      simp only [Submodule.carrier_eq_coe, zero_lie, SetLike.mem_coe, zero_mem]
    | add x₁ x₂ _ _ ih₁ ih₂ =>
      simp only [add_lie, Submodule.carrier_eq_coe, SetLike.mem_coe] at ih₁ ih₂ ⊢
      exact add_mem ih₁ ih₂

Depends on / 依赖: IsNonZero, Weight, sl2SubmoduleOfRoot
-/
noncomputable def invtSubmoduleToLieIdeal (q : Submodule K (Dual K H))
    (hq : forall i, q in End.invtSubmodule ((rootSystem H).reflection i)) : LieIdeal K L where
  __ := ⨆ α : {α : Weight K H L // ↑α in q ∧ α.IsNonZero}, sl2SubmoduleOfRoot α.2.2
  lie_mem := by
    intro x m hm
    have hx : x in ⨆ χ : Weight K H L, genWeightSpace L χ := by
      simp [LieModule.iSup_genWeightSpace_eq_top']
    induction hx using LieSubmodule.iSup_induction' with
    | mem χ x_χ hx_χ =>
      induction hm using LieSubmodule.iSup_induction' with
      | mem α m_α hm_α => exact invtSubmoduleToLieIdeal_aux q hq χ x_χ m_α hx_χ α.1 α.2.1 α.2.2 hm_α
      | zero =>
        simp only [Submodule.carrier_eq_coe, lie_zero, SetLike.mem_coe, zero_mem]
      | add m₁ m₂ _ _ ih₁ ih₂ =>
        simp only [lie_add, Submodule.carrier_eq_coe, SetLike.mem_coe] at ih₁ ih₂ ⊢
        exact add_mem ih₁ ih₂
    | zero =>
      simp only [Submodule.carrier_eq_coe, zero_lie, SetLike.mem_coe, zero_mem]
    | add x₁ x₂ _ _ ih₁ ih₂ =>
      simp only [add_lie, Submodule.carrier_eq_coe, SetLike.mem_coe] at ih₁ ih₂ ⊢
      exact add_mem ih₁ ih₂

/--
lemma `coe_invtSubmoduleToLieIdeal_eq_iSup` / 引理 `coe_invtSubmoduleToLieIdeal_eq_iSup`

English:
lemma coe_invtSubmoduleToLieIdeal_eq_iSup
  statement: (q : Submodule K (Dual K H))
  proof: rfl

中文:
引理 coe_invtSubmoduleToLieIdeal_eq_iSup
  结论: (q : 子模 K (对偶 K H))
  证明: rfl
-/
@[simp] lemma coe_invtSubmoduleToLieIdeal_eq_iSup (q : Submodule K (Dual K H))
    (hq : forall i, q in End.invtSubmodule ((rootSystem H).reflection i).toLinearMap) :
    (invtSubmoduleToLieIdeal q hq).toSubmodule =
      ⨆ α : {α : Weight K H L // ↑α in q ∧ α.IsNonZero}, sl2SubmoduleOfRoot α.2.2 :=
  rfl

/--
lemma `restr_invtSubmoduleToLieIdeal_eq_iSup` / 引理 `restr_invtSubmoduleToLieIdeal_eq_iSup`

English:
lemma restr_invtSubmoduleToLieIdeal_eq_iSup
  statement: (q : Submodule K (Dual K H))
  proof: by
  rw [← LieSubmodule.toSubmodule_inj]; rw [LieSubmodule.restr_toSubmodule]; rw [coe_invtSubmoduleToLieIdeal_eq_iSup]; rw [LieSubmodule.iSup_toSubmodule]

中文:
引理 restr_invtSubmoduleToLieIdeal_eq_iSup
  结论: (q : 子模 K (对偶 K H))
  证明: by
  rw [← LieSubmodule.toSubmodule_inj]; rw [LieSubmodule.restr_toSubmodule]; rw [coe_invtSubmoduleToLieIdeal_eq_iSup]; rw [LieSubmodule.iSup_toSubmodule]
-/
@[simp] lemma restr_invtSubmoduleToLieIdeal_eq_iSup (q : Submodule K (Dual K H))
    (hq : forall i, q in End.invtSubmodule ((rootSystem H).reflection i).toLinearMap) :
    (invtSubmoduleToLieIdeal q hq).restr H =
      ⨆ α : {α : Weight K H L // ↑α in q ∧ α.IsNonZero}, sl2SubmoduleOfRoot α.2.2 := by
  rw [← LieSubmodule.toSubmodule_inj]; rw [LieSubmodule.restr_toSubmodule]; rw [coe_invtSubmoduleToLieIdeal_eq_iSup]; rw [LieSubmodule.iSup_toSubmodule]

/--
lemma `mem_rootSet_invtSubmoduleToLieIdeal` / 引理 `mem_rootSet_invtSubmoduleToLieIdeal`

English:
lemma mem_rootSet_invtSubmoduleToLieIdeal
  statement: (q : Submodule K (Dual K H))
  proof: by
  set J := invtSubmoduleToLieIdeal q hq
  constructor
  · intro hα_mem
    by_contra hα_not
    have hα_nz := H.isNonZero_coe_root α
    have hne (χ : Weight K H L) (hχ : ↑χ in q) : (χ : H -> K) != ((α : Weight K H L) : H -> K) :=
      fun heq => hα_not (by simpa [rootSystem_root_apply] using DFunLike.coe_injective heq ▸ hχ)
    have h_le : J.restr H <= ⨆ (χ : H -> K) (_ : χ != (α : Weight K H L)), genWeightSpace L χ := by
      refine iSup_le fun ⟨β, hβ_mem, hβ_nz⟩ => ?_
      rw [sl2SubmoduleOfRoot_eq_sup]
      refine sup_le (sup_le ?_ ?_) ?_
      · exact le_iSup₂_of_le _ (hne β hβ_mem) le_rfl
      · have : ↑(-β) in q := by rw [Weight.toLinear_neg]; exact q.neg_mem hβ_mem
        exact le_iSup₂_of_le _ (hne (-β) this) le_rfl
      · apply (LieSubmodule.map_incl_le.trans (rootSpace_zero_eq K L H).symm.le).trans
        exact le_iSup₂_of_le 0 (fun h => hα_nz h.symm) le_rfl
    have h_disj := ((iSupIndep_genWeightSpace K H L _).mono_right h_le).mono_right hα_mem
    exact (α : Weight K H L).genWeightSpace_ne_bot L (disjoint_self.mp h_disj)
  · intro hα
    calc rootSpace H (α : Weight K H L)
        <= sl2SubmoduleOfRoot (H.isNonZero_coe_root α) := by
          rw [sl2SubmoduleOfRoot_eq_sup]; exact le_sup_of_le_left le_sup_left
      _ <= ⨆ x : {β : Weight K H L // ↑β in q ∧ β.IsNonZero}, sl2SubmoduleOfRoot x.2.2 :=
          le_iSup_of_le ⟨↑α, hα, H.isNonZero_coe_root α⟩ le_rfl
      _ = J.restr H := (restr_invtSubmoduleToLieIdeal_eq_iSup q hq).symm

@[gcongr]

中文:
引理 mem_rootSet_invtSubmoduleToLieIdeal
  结论: (q : 子模 K (对偶 K H))
  证明: by
  set J := invtSubmoduleToLieIdeal q hq
  constructor
  · intro hα_mem
    by_contra hα_not
    have hα_nz := H.isNonZero_coe_root α
    have hne (χ : Weight K H L) (hχ : ↑χ in q) : (χ : H -> K) != ((α : Weight K H L) : H -> K) :=
      fun heq => hα_not (by simpa [rootSystem_root_apply] using DFunLike.coe_injective heq ▸ hχ)
    have h_le : J.restr H <= ⨆ (χ : H -> K) (_ : χ != (α : Weight K H L)), genWeightSpace L χ := by
      refine iSup_le fun ⟨β, hβ_mem, hβ_nz⟩ => ?_
      rw [sl2SubmoduleOfRoot_eq_sup]
      refine sup_le (sup_le ?_ ?_) ?_
      · exact le_iSup₂_of_le _ (hne β hβ_mem) le_rfl
      · have : ↑(-β) in q := by rw [Weight.toLinear_neg]; exact q.neg_mem hβ_mem
        exact le_iSup₂_of_le _ (hne (-β) this) le_rfl
      · apply (LieSubmodule.map_incl_le.trans (rootSpace_zero_eq K L H).symm.le).trans
        exact le_iSup₂_of_le 0 (fun h => hα_nz h.symm) le_rfl
    have h_disj := ((iSupIndep_genWeightSpace K H L _).mono_right h_le).mono_right hα_mem
    exact (α : Weight K H L).genWeightSpace_ne_bot L (disjoint_self.mp h_disj)
  · intro hα
    calc rootSpace H (α : Weight K H L)
        <= sl2SubmoduleOfRoot (H.isNonZero_coe_root α) := by
          rw [sl2SubmoduleOfRoot_eq_sup]; exact le_sup_of_le_left le_sup_left
      _ <= ⨆ x : {β : Weight K H L // ↑β in q ∧ β.IsNonZero}, sl2SubmoduleOfRoot x.2.2 :=
          le_iSup_of_le ⟨↑α, hα, H.isNonZero_coe_root α⟩ le_rfl
      _ = J.restr H := (restr_invtSubmoduleToLieIdeal_eq_iSup q hq).symm

@[gcongr]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, H.isNonZero_coe_root, J.restr, Weight, coe_injective, genWeightSpace, h_le, iSup_le, invtSubmoduleToLieIdeal, isNonZero_coe_root, rootSystem_root_apply, sl2SubmoduleOfRoot_eq_sup, sup_le
-/
lemma mem_rootSet_invtSubmoduleToLieIdeal (q : Submodule K (Dual K H))
    (hq : forall i, q in End.invtSubmodule ((rootSystem H).reflection i).toLinearMap) {α : H.root} :
    α in (invtSubmoduleToLieIdeal q hq).rootSet ↔ (rootSystem H).root α in q := by
  set J := invtSubmoduleToLieIdeal q hq
  constructor
  · intro hα_mem
    by_contra hα_not
    have hα_nz := H.isNonZero_coe_root α
    have hne (χ : Weight K H L) (hχ : ↑χ in q) : (χ : H -> K) != ((α : Weight K H L) : H -> K) :=
      fun heq => hα_not (by simpa [rootSystem_root_apply] using DFunLike.coe_injective heq ▸ hχ)
    have h_le : J.restr H <= ⨆ (χ : H -> K) (_ : χ != (α : Weight K H L)), genWeightSpace L χ := by
      refine iSup_le fun ⟨β, hβ_mem, hβ_nz⟩ => ?_
      rw [sl2SubmoduleOfRoot_eq_sup]
      refine sup_le (sup_le ?_ ?_) ?_
      · exact le_iSup₂_of_le _ (hne β hβ_mem) le_rfl
      · have : ↑(-β) in q := by rw [Weight.toLinear_neg]; exact q.neg_mem hβ_mem
        exact le_iSup₂_of_le _ (hne (-β) this) le_rfl
      · apply (LieSubmodule.map_incl_le.trans (rootSpace_zero_eq K L H).symm.le).trans
        exact le_iSup₂_of_le 0 (fun h => hα_nz h.symm) le_rfl
    have h_disj := ((iSupIndep_genWeightSpace K H L _).mono_right h_le).mono_right hα_mem
    exact (α : Weight K H L).genWeightSpace_ne_bot L (disjoint_self.mp h_disj)
  · intro hα
    calc rootSpace H (α : Weight K H L)
        <= sl2SubmoduleOfRoot (H.isNonZero_coe_root α) := by
          rw [sl2SubmoduleOfRoot_eq_sup]; exact le_sup_of_le_left le_sup_left
      _ <= ⨆ x : {β : Weight K H L // ↑β in q ∧ β.IsNonZero}, sl2SubmoduleOfRoot x.2.2 :=
          le_iSup_of_le ⟨↑α, hα, H.isNonZero_coe_root α⟩ le_rfl
      _ = J.restr H := (restr_invtSubmoduleToLieIdeal_eq_iSup q hq).symm

@[gcongr]
/--
lemma `invtSubmoduleToLieIdeal_mono` / 引理 `invtSubmoduleToLieIdeal_mono`

English:
lemma invtSubmoduleToLieIdeal_mono
  statement: {q₁ q₂ : Submodule K (Dual K H)}
  proof: by
  change (invtSubmoduleToLieIdeal q₁ hq₁).restr H <= (invtSubmoduleToLieIdeal q₂ hq₂).restr H
  exact iSup_le fun ⟨α, hα_mem, hα_nz⟩ => le_iSup_of_le ⟨α, h hα_mem, hα_nz⟩ le_rfl

中文:
引理 invtSubmoduleToLieIdeal_mono
  结论: {q₁ q₂ : 子模 K (对偶 K H)}
  证明: by
  change (invtSubmoduleToLieIdeal q₁ hq₁).restr H <= (invtSubmoduleToLieIdeal q₂ hq₂).restr H
  exact iSup_le fun ⟨α, hα_mem, hα_nz⟩ => le_iSup_of_le ⟨α, h hα_mem, hα_nz⟩ le_rfl

Depends on / 依赖: iSup_le, invtSubmoduleToLieIdeal, le_iSup_of_le, le_rfl
-/
lemma invtSubmoduleToLieIdeal_mono {q₁ q₂ : Submodule K (Dual K H)}
    (hq₁ : forall i, q₁ in End.invtSubmodule ((rootSystem H).reflection i).toLinearMap)
    (hq₂ : forall i, q₂ in End.invtSubmodule ((rootSystem H).reflection i).toLinearMap)
    (h : q₁ <= q₂) :
    invtSubmoduleToLieIdeal q₁ hq₁ <= invtSubmoduleToLieIdeal q₂ hq₂ := by
  change (invtSubmoduleToLieIdeal q₁ hq₁).restr H <= (invtSubmoduleToLieIdeal q₂ hq₂).restr H
  exact iSup_le fun ⟨α, hα_mem, hα_nz⟩ => le_iSup_of_le ⟨α, h hα_mem, hα_nz⟩ le_rfl

/--
lemma `lieIdealOrderIso_left_inv` / 引理 `lieIdealOrderIso_left_inv`

English:
lemma lieIdealOrderIso_left_inv
  statement: (I : LieIdeal K L)
  proof: by
  set J := invtSubmoduleToLieIdeal I.rootSpan
    ((rootSystem H).mem_invtRootSubmodule_iff.mp I.rootSpan_mem_invtRootSubmodule)
  have h_eq : forall α : H.root, α in J.rootSet ↔ α in I.rootSet := fun α => by
    rw [mem_rootSet_invtSubmoduleToLieIdeal]; rw [rootSystem_root_apply]
    exact ⟨I.mem_rootSet_of_mem_rootSpan, fun h => Submodule.subset_span ⟨α, h, rfl⟩⟩
  have h_restr : J.restr H = I.restr H := by
    rw [J.restr_eq_iSup_sl2SubmoduleOfRoot]; rw [I.restr_eq_iSup_sl2SubmoduleOfRoot]
    exact le_antisymm
      (iSup₂_le fun α hα => le_iSup₂_of_le α ((h_eq α).1 hα) le_rfl)
      (iSup₂_le fun α hα => le_iSup₂_of_le α ((h_eq α).2 hα) le_rfl)
  rw [← LieSubmodule.toSubmodule_inj]; rw [← LieSubmodule.restr_toSubmodule J H]; rw [← LieSubmodule.restr_toSubmodule I H]; rw [h_restr]

中文:
引理 lieIdealOrderIso_left_inv
  结论: (I : LieIdeal K L)
  证明: by
  set J := invtSubmoduleToLieIdeal I.rootSpan
    ((rootSystem H).mem_invtRootSubmodule_iff.mp I.rootSpan_mem_invtRootSubmodule)
  have h_eq : forall α : H.root, α in J.rootSet ↔ α in I.rootSet := fun α => by
    rw [mem_rootSet_invtSubmoduleToLieIdeal]; rw [rootSystem_root_apply]
    exact ⟨I.mem_rootSet_of_mem_rootSpan, fun h => Submodule.subset_span ⟨α, h, rfl⟩⟩
  have h_restr : J.restr H = I.restr H := by
    rw [J.restr_eq_iSup_sl2SubmoduleOfRoot]; rw [I.restr_eq_iSup_sl2SubmoduleOfRoot]
    exact le_antisymm
      (iSup₂_le fun α hα => le_iSup₂_of_le α ((h_eq α).1 hα) le_rfl)
      (iSup₂_le fun α hα => le_iSup₂_of_le α ((h_eq α).2 hα) le_rfl)
  rw [← LieSubmodule.toSubmodule_inj]; rw [← LieSubmodule.restr_toSubmodule J H]; rw [← LieSubmodule.restr_toSubmodule I H]; rw [h_restr]

Depends on / 依赖: H.root, I.mem_rootSet_of_mem_rootSpan, I.rootSet, I.rootSpan, I.rootSpan_mem_invtRootSubmodule, J.res, J.rootSet, Submodule, Submodule.subset_span, h_eq, h_restr, invtSubmoduleToLieIdeal, mem_invtRootSubmodule_iff, mem_invtRootSubmodule_iff.mp, mem_rootSet_invtSubmoduleToLieIdeal, mem_rootSet_of_mem_rootSpan, rootSet, rootSpan, rootSpan_mem_invtRootSubmodule, rootSystem
-/
lemma lieIdealOrderIso_left_inv (I : LieIdeal K L)
    (hI : forall α, I.rootSpan in End.invtSubmodule ((rootSystem H).reflection α).toLinearMap :=
      (rootSystem H).mem_invtRootSubmodule_iff.mp I.rootSpan_mem_invtRootSubmodule) :
    invtSubmoduleToLieIdeal I.rootSpan hI = I := by
  set J := invtSubmoduleToLieIdeal I.rootSpan
    ((rootSystem H).mem_invtRootSubmodule_iff.mp I.rootSpan_mem_invtRootSubmodule)
  have h_eq : forall α : H.root, α in J.rootSet ↔ α in I.rootSet := fun α => by
    rw [mem_rootSet_invtSubmoduleToLieIdeal]; rw [rootSystem_root_apply]
    exact ⟨I.mem_rootSet_of_mem_rootSpan, fun h => Submodule.subset_span ⟨α, h, rfl⟩⟩
  have h_restr : J.restr H = I.restr H := by
    rw [J.restr_eq_iSup_sl2SubmoduleOfRoot]; rw [I.restr_eq_iSup_sl2SubmoduleOfRoot]
    exact le_antisymm
      (iSup₂_le fun α hα => le_iSup₂_of_le α ((h_eq α).1 hα) le_rfl)
      (iSup₂_le fun α hα => le_iSup₂_of_le α ((h_eq α).2 hα) le_rfl)
  rw [← LieSubmodule.toSubmodule_inj]; rw [← LieSubmodule.restr_toSubmodule J H]; rw [← LieSubmodule.restr_toSubmodule I H]; rw [h_restr]

/--
lemma `lieIdealOrderIso_right_inv` / 引理 `lieIdealOrderIso_right_inv`

English:
lemma lieIdealOrderIso_right_inv
  statement: (q : (rootSystem H).invtRootSubmodule)
  proof: by
  simp only [Subtype.ext_iff, LieIdeal.toInvtRootSubmodule, LieIdeal.rootSpan, LieIdeal.rootSet]
  conv_rhs => rw [RootPairing.invtRootSubmodule.eq_span_root q]
  congr 2; ext α
  exact mem_rootSet_invtSubmoduleToLieIdeal _ _

中文:
引理 lieIdealOrderIso_right_inv
  结论: (q : (rootSystem H).invtRootSubmodule)
  证明: by
  simp only [Subtype.ext_iff, LieIdeal.toInvtRootSubmodule, LieIdeal.rootSpan, LieIdeal.rootSet]
  conv_rhs => rw [RootPairing.invtRootSubmodule.eq_span_root q]
  congr 2; ext α
  exact mem_rootSet_invtSubmoduleToLieIdeal _ _

Depends on / 依赖: LieIdeal, LieIdeal.rootSet, LieIdeal.rootSpan, LieIdeal.toInvtRootSubmodule, RootPairing, RootPairing.invtRootSubmodule.eq_span_root, Subtype, Subtype.ext_iff, conv_rhs, eq_span_root, ext_iff, invtRootSubmodule, invtSubmoduleToLieIdeal, mem_invtRootSubmodule_iff, mem_invtRootSubmodule_iff.mp, mem_rootSet_invtSubmoduleToLieIdeal, property, q.property, rootSet, rootSpan
-/
lemma lieIdealOrderIso_right_inv (q : (rootSystem H).invtRootSubmodule)
    (hq : forall α, ↑q in End.invtSubmodule ((rootSystem H).reflection α).toLinearMap :=
      (rootSystem H).mem_invtRootSubmodule_iff.mp q.property) :
    (invtSubmoduleToLieIdeal q.1 hq).toInvtRootSubmodule = q := by
  simp only [Subtype.ext_iff, LieIdeal.toInvtRootSubmodule, LieIdeal.rootSpan, LieIdeal.rootSet]
  conv_rhs => rw [RootPairing.invtRootSubmodule.eq_span_root q]
  congr 2; ext α
  exact mem_rootSet_invtSubmoduleToLieIdeal _ _

variable (H) in
/--
Definition of `lieIdealOrderIso` / `lieIdealOrderIso` 的定义

English:
definition lieIdealOrderIso
  signature: :
  body: LieIdeal.toInvtRootSubmodule
  invFun q := invtSubmoduleToLieIdeal q.1 ((rootSystem H).mem_invtRootSubmodule_iff.mp q.2)
  left_inv := lieIdealOrderIso_left_inv
  right_inv := lieIdealOrderIso_right_inv
  map_rel_iff' {I J} := by
    refine ⟨fun h => ?_, LieIdeal.toInvtRootSubmodule_mono⟩
    rw [← lieIdealOrderIso_left_inv (H := H) I]; rw [← lieIdealOrderIso_left_inv (H := H) J]
    exact invtSubmoduleToLieIdeal_mono _ _ h

中文:
定义 lieIdealOrderIso
  签名: :
  定义体: LieIdeal.toInvtRootSubmodule
  invFun q := invtSubmoduleToLieIdeal q.1 ((rootSystem H).mem_invtRootSubmodule_iff.mp q.2)
  left_inv := lieIdealOrderIso_left_inv
  right_inv := lieIdealOrderIso_right_inv
  map_rel_iff' {I J} := by
    refine ⟨fun h => ?_, LieIdeal.toInvtRootSubmodule_mono⟩
    rw [← lieIdealOrderIso_left_inv (H := H) I]; rw [← lieIdealOrderIso_left_inv (H := H) J]
    exact invtSubmoduleToLieIdeal_mono _ _ h

Depends on / 依赖: LieIdeal, LieIdeal.toInvtRootSubmodule, toInvtRootSubmodule
-/
noncomputable def lieIdealOrderIso :
    LieIdeal K L ≃o (rootSystem H).invtRootSubmodule where
  toFun := LieIdeal.toInvtRootSubmodule
  invFun q := invtSubmoduleToLieIdeal q.1 ((rootSystem H).mem_invtRootSubmodule_iff.mp q.2)
  left_inv := lieIdealOrderIso_left_inv
  right_inv := lieIdealOrderIso_right_inv
  map_rel_iff' {I J} := by
    refine ⟨fun h => ?_, LieIdeal.toInvtRootSubmodule_mono⟩
    rw [← lieIdealOrderIso_left_inv (H := H) I]; rw [← lieIdealOrderIso_left_inv (H := H) J]
    exact invtSubmoduleToLieIdeal_mono _ _ h

/--
theorem `isSimple_iff_isIrreducible` / 定理 `isSimple_iff_isIrreducible`

English:
theorem isSimple_iff_isIrreducible
  statement: (rootSystem H).IsIrreducible ↔ IsSimple K L
  proof: by
  nontriviality L
  have hL : ¬ IsLieAbelian L :=
    (isLieAbelian_iff_subsingleton K (L := L)).not.mpr (not_subsingleton L)
  rw [RootPairing.isIrreducible_iff_invtRootSubmodule]; rw [← isSimple_iff_of_not_isLieAbelian K L hL]; rw [(lieIdealOrderIso H).isSimpleOrder_iff]

中文:
定理 isSimple_iff_isIrreducible
  结论: (rootSystem H).是不可约 ↔ 是单 K L
  证明: by
  nontriviality L
  have hL : ¬ IsLieAbelian L :=
    (isLieAbelian_iff_subsingleton K (L := L)).not.mpr (not_subsingleton L)
  rw [RootPairing.isIrreducible_iff_invtRootSubmodule]; rw [← isSimple_iff_of_not_isLieAbelian K L hL]; rw [(lieIdealOrderIso H).isSimpleOrder_iff]

Depends on / 依赖: IsLieAbelian, RootPairing, RootPairing.isIrreducible_iff_invtRootSubmodule, isIrreducible_iff_invtRootSubmodule, isLieAbelian_iff_subsingleton, isSimpleOrder_iff, isSimple_iff_of_not_isLieAbelian, lieIdealOrderIso, nontriviality, not.mpr, not_subsingleton
-/
theorem isSimple_iff_isIrreducible : (rootSystem H).IsIrreducible ↔ IsSimple K L := by
  nontriviality L
  have hL : ¬ IsLieAbelian L :=
    (isLieAbelian_iff_subsingleton K (L := L)).not.mpr (not_subsingleton L)
  rw [RootPairing.isIrreducible_iff_invtRootSubmodule]; rw [← isSimple_iff_of_not_isLieAbelian K L hL]; rw [(lieIdealOrderIso H).isSimpleOrder_iff]

end LieAlgebra.IsKilling

namespace LieAlgebra

open LieModule

variable {K L : Type*} [Field K] [CharZero K]
  [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]

/--
Instance `instIsIrreducibleRootSystem_of_isSimple` / 实例 `instIsIrreducibleRootSystem_of_isSimple`

English:
instance instIsIrreducibleRootSystem_of_isSimple
  signature: [IsSimple K L]
  body: LieAlgebra.IsKilling.isSimple_iff_isIrreducible.mpr ‹_›

中文:
实例 instIsIrreducibleRootSystem_of_isSimple
  签名: [是单 K L]
  定义体: LieAlgebra.IsKilling.isSimple_iff_isIrreducible.mpr ‹_›

Depends on / 依赖: IsKilling, LieAlgebra, LieAlgebra.IsKilling.isSimple_iff_isIrreducible.mpr, isSimple_iff_isIrreducible
-/
instance instIsIrreducibleRootSystem_of_isSimple [IsSimple K L] :
    (IsKilling.rootSystem H).IsIrreducible :=
  LieAlgebra.IsKilling.isSimple_iff_isIrreducible.mpr ‹_›

end LieAlgebra
