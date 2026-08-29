/-
Copyright (c) 2024 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Lie.Semisimple.Defs
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Lie algebras with non-degenerate invariant bilinear forms are semisimple

In this file we prove that a finite-dimensional Lie algebra over a field is semisimple
if it does not have non-trivial abelian ideals and it admits a
non-degenerate reflexive invariant bilinear form.
Here a form is *invariant* if it is invariant under the Lie bracket
in the sense that `⁅x, Φ⁆ = 0` for all `x` or equivalently, `Φ ⁅x, y⁆ z = Φ x ⁅y, z⁆`.

## Main results

* `LieAlgebra.InvariantForm.orthogonal`: given a Lie submodule `N` of a Lie module `M`,
  we define its orthogonal complement with respect to a non-degenerate invariant bilinear form `Φ`
  as the Lie ideal of elements `x` such that `Φ n x = 0` for all `n ∈ N`.
* `LieAlgebra.InvariantForm.isSemisimple_of_nondegenerate`: the main result of this file;
  a finite-dimensional Lie algebra over a field is semisimple
  if it does not have non-trivial abelian ideals and admits
  a non-degenerate invariant reflexive bilinear form.

## References

We follow the short and excellent paper [dieudonne1953].
-/

@[expose] public section

namespace LieAlgebra

namespace InvariantForm

section ring

variable {R L M : Type*}
variable [CommRing R] [LieRing L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M]

variable (Φ : LinearMap.BilinForm R M) (hΦ_nondeg : Φ.Nondegenerate)

variable (L) in
/--
Definition of `_root_.LinearMap.BilinForm.lieInvariant` / `_root_.LinearMap.BilinForm.lieInvariant` 的定义

English:
definition _root_.LinearMap.BilinForm.lieInvariant
  signature: : Prop
  body: forall (x : L) (y z : M), Φ ⁅x, y⁆ z = -Φ y ⁅x, z⁆

中文:
定义 _root_.线性映射.BilinForm.lieInvariant
  签名: : 命题
  定义体: forall (x : L) (y z : M), Φ ⁅x, y⁆ z = -Φ y ⁅x, z⁆
-/
def _root_.LinearMap.BilinForm.lieInvariant : Prop :=
  forall (x : L) (y z : M), Φ ⁅x, y⁆ z = -Φ y ⁅x, z⁆

/--
lemma `_root_.LinearMap.BilinForm.lieInvariant_iff` / 引理 `_root_.LinearMap.BilinForm.lieInvariant_iff`

English:
lemma _root_.LinearMap.BilinForm.lieInvariant_iff
  given: [LieAlgebra R L] [LieModule R L M]
  proof: by
  refine ⟨fun h x => ?_, fun h x y z => ?_⟩
  · ext y z
    rw [LieHom.lie_apply]; rw [LinearMap.sub_apply]; rw [Module.Dual.lie_apply]; rw [LinearMap.zero_apply]; rw [LinearMap.zero_apply]; rw [h]; rw [sub_self]
  · replace h := LinearMap.congr_fun₂ (h x) y z
    simp only [LieHom.lie_apply, LinearMap.sub_apply, Module.Dual.lie_apply,
      LinearMap.zero_apply, sub_eq_zero] at h
    simp [← h]

中文:
引理 _root_.线性映射.BilinForm.lieInvariant_iff
  条件: [Lie代数 R L] [Lie模 R L M]
  证明: by
  refine ⟨fun h x => ?_, fun h x y z => ?_⟩
  · ext y z
    rw [LieHom.lie_apply]; rw [LinearMap.sub_apply]; rw [Module.Dual.lie_apply]; rw [LinearMap.zero_apply]; rw [LinearMap.zero_apply]; rw [h]; rw [sub_self]
  · replace h := LinearMap.congr_fun₂ (h x) y z
    simp only [LieHom.lie_apply, LinearMap.sub_apply, Module.Dual.lie_apply,
      LinearMap.zero_apply, sub_eq_zero] at h
    simp [← h]

Depends on / 依赖: LieHom, LieHom.lie_apply, LinearMap, LinearMap.congr_fun, LinearMap.sub_apply, LinearMap.zero_apply, Module, Module.Dual.lie_apply, lie_apply, replace, sub_apply, sub_eq_zero, sub_self, zero_apply
-/
lemma _root_.LinearMap.BilinForm.lieInvariant_iff [LieAlgebra R L] [LieModule R L M] :
    Φ.lieInvariant L ↔ Φ in LieModule.maxTrivSubmodule R L (LinearMap.BilinForm R M) := by
  refine ⟨fun h x => ?_, fun h x y z => ?_⟩
  · ext y z
    rw [LieHom.lie_apply]; rw [LinearMap.sub_apply]; rw [Module.Dual.lie_apply]; rw [LinearMap.zero_apply]; rw [LinearMap.zero_apply]; rw [h]; rw [sub_self]
  · replace h := LinearMap.congr_fun₂ (h x) y z
    simp only [LieHom.lie_apply, LinearMap.sub_apply, Module.Dual.lie_apply,
      LinearMap.zero_apply, sub_eq_zero] at h
    simp [← h]

/--
The orthogonal complement of a Lie submodule `N` with respect to an invariant bilinear form `Φ` is
the Lie submodule of elements `y` such that `Φ x y = 0` for all `x ∈ N`.
-/
@[simps!]
/--
Definition of `orthogonal` / `orthogonal` 的定义

English:
definition orthogonal
  signature: (hΦ_inv : Φ.lieInvariant L) (N : LieSubmodule R L M)
  body: Φ.orthogonal N
  lie_mem {x y} := by
    suffices (forall n in N, Φ n y = 0) -> forall n in N, Φ n ⁅x, y⁆ = 0 by
      simpa only [
        AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup, Submodule.mem_toAddSubmonoid,
        LinearMap.BilinForm.mem_orthogonal_iff, LieSubmodule.mem_toSubmodule]
    intro H a ha
    rw [← neg_eq_zero]; rw [← hΦ_inv]
exact H _ N.lie_mem ha

中文:
定义 orthogonal
  签名: (hΦ_inv : Φ.lieInvariant L) (N : Lie子模 R L M)
  定义体: Φ.orthogonal N
  lie_mem {x y} := by
    suffices (forall n in N, Φ n y = 0) -> forall n in N, Φ n ⁅x, y⁆ = 0 by
      simpa only [
        AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup, Submodule.mem_toAddSubmonoid,
        LinearMap.BilinForm.mem_orthogonal_iff, LieSubmodule.mem_toSubmodule]
    intro H a ha
    rw [← neg_eq_zero]; rw [← hΦ_inv]
exact H _ N.lie_mem ha

Depends on / 依赖: orthogonal
-/
def orthogonal (hΦ_inv : Φ.lieInvariant L) (N : LieSubmodule R L M) : LieSubmodule R L M where
  __ := Φ.orthogonal N
  lie_mem {x y} := by
    suffices (forall n in N, Φ n y = 0) -> forall n in N, Φ n ⁅x, y⁆ = 0 by
      simpa only [
        AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup, Submodule.mem_toAddSubmonoid,
        LinearMap.BilinForm.mem_orthogonal_iff, LieSubmodule.mem_toSubmodule]
    intro H a ha
    rw [← neg_eq_zero]; rw [← hΦ_inv]
exact H _ N.lie_mem ha

variable (hΦ_inv : Φ.lieInvariant L)

@[simp]
/--
lemma `orthogonal_toSubmodule` / 引理 `orthogonal_toSubmodule`

English:
lemma orthogonal_toSubmodule
  given: (N : LieSubmodule R L M)
  proof: rfl

中文:
引理 orthogonal_toSubmodule
  条件: (N : Lie子模 R L M)
  证明: rfl
-/
lemma orthogonal_toSubmodule (N : LieSubmodule R L M) :
    (orthogonal Φ hΦ_inv N).toSubmodule = Φ.orthogonal N.toSubmodule := rfl

/--
lemma `mem_orthogonal` / 引理 `mem_orthogonal`

English:
lemma mem_orthogonal
  given: (N : LieSubmodule R L M) (y : M)
  proof: by
  simp [orthogonal, LinearMap.BilinForm.mem_orthogonal_iff]

中文:
引理 mem_orthogonal
  条件: (N : Lie子模 R L M) (y : M)
  证明: by
  simp [orthogonal, LinearMap.BilinForm.mem_orthogonal_iff]

Depends on / 依赖: BilinForm, LinearMap, LinearMap.BilinForm.mem_orthogonal_iff, mem_orthogonal_iff, orthogonal
-/
lemma mem_orthogonal (N : LieSubmodule R L M) (y : M) :
    y in orthogonal Φ hΦ_inv N ↔ forall x in N, Φ x y = 0 := by
  simp [orthogonal, LinearMap.BilinForm.mem_orthogonal_iff]

variable [LieAlgebra R L]

/--
lemma `orthogonal_disjoint` / 引理 `orthogonal_disjoint`

English:
lemma orthogonal_disjoint
  proof: by
  rw [disjoint_iff]; rw [← hI.lt_iff]; rw [lt_iff_le_and_ne]
  suffices ¬I <= orthogonal Φ hΦ_inv I by simpa
  intro contra
  apply hI.1
  rw [eq_bot_iff]; rw [← lie_eq_self_of_isAtom_of_nonabelian I hI (hL I hI)]; rw [LieSubmodule.lieIdeal_oper_eq_span]; rw [LieSubmodule.lieSpan_le]
  rintro _ ⟨x, y, rfl⟩
  simp only [LieSubmodule.bot_coe, Set.mem_singleton_iff]
  apply hΦ_nondeg.1
  intro z
  rw [hΦ_inv]; rw [neg_eq_zero]
  have hyz : ⁅(x : L), z⁆ in I := lie_mem_left _ _ _ _ _ x.2
  exact contra hyz y y.2

中文:
引理 orthogonal_disjoint
  证明: by
  rw [disjoint_iff]; rw [← hI.lt_iff]; rw [lt_iff_le_and_ne]
  suffices ¬I <= orthogonal Φ hΦ_inv I by simpa
  intro contra
  apply hI.1
  rw [eq_bot_iff]; rw [← lie_eq_self_of_isAtom_of_nonabelian I hI (hL I hI)]; rw [LieSubmodule.lieIdeal_oper_eq_span]; rw [LieSubmodule.lieSpan_le]
  rintro _ ⟨x, y, rfl⟩
  simp only [LieSubmodule.bot_coe, Set.mem_singleton_iff]
  apply hΦ_nondeg.1
  intro z
  rw [hΦ_inv]; rw [neg_eq_zero]
  have hyz : ⁅(x : L), z⁆ in I := lie_mem_left _ _ _ _ _ x.2
  exact contra hyz y y.2

Depends on / 依赖: LieSubmodule, LieSubmodule.bot_coe, LieSubmodule.lieIdeal_oper_eq_span, LieSubmodule.lieSpan_le, Set.mem_singleton_iff, bot_coe, contra, disjoint_iff, eq_bot_iff, hI.lt_iff, lieIdeal_oper_eq_span, lieSpan_le, lie_eq_self_of_isAtom_of_nonabelian, lie_mem_left, lt_iff, lt_iff_le_and_ne, mem_singleton_iff, neg_eq_zero, orthogonal
-/
lemma orthogonal_disjoint
    (Φ : LinearMap.BilinForm R L) (hΦ_nondeg : Φ.Nondegenerate) (hΦ_inv : Φ.lieInvariant L)
    -- TODO: replace the following assumption by a typeclass assumption `[HasNonAbelianAtoms]`
    (hL : forall I : LieIdeal R L, IsAtom I -> ¬IsLieAbelian I)
    (I : LieIdeal R L) (hI : IsAtom I) :
    Disjoint I (orthogonal Φ hΦ_inv I) := by
  rw [disjoint_iff]; rw [← hI.lt_iff]; rw [lt_iff_le_and_ne]
  suffices ¬I <= orthogonal Φ hΦ_inv I by simpa
  intro contra
  apply hI.1
  rw [eq_bot_iff]; rw [← lie_eq_self_of_isAtom_of_nonabelian I hI (hL I hI)]; rw [LieSubmodule.lieIdeal_oper_eq_span]; rw [LieSubmodule.lieSpan_le]
  rintro _ ⟨x, y, rfl⟩
  simp only [LieSubmodule.bot_coe, Set.mem_singleton_iff]
  apply hΦ_nondeg.1
  intro z
  rw [hΦ_inv]; rw [neg_eq_zero]
  have hyz : ⁅(x : L), z⁆ in I := lie_mem_left _ _ _ _ _ x.2
  exact contra hyz y y.2

end ring

section field

variable {K L M : Type*}
variable [Field K] [LieRing L] [LieAlgebra K L]
variable [AddCommGroup M] [Module K M] [LieRingModule L M]

variable [Module.Finite K L]
variable (Φ : LinearMap.BilinForm K L) (hΦ_nondeg : Φ.Nondegenerate)
variable (hΦ_inv : Φ.lieInvariant L) (hΦ_refl : Φ.IsRefl)
-- TODO: replace the following assumption by a typeclass assumption `[HasNonAbelianAtoms]`
variable (hL : forall I : LieIdeal K L, IsAtom I -> ¬IsLieAbelian I)
include hΦ_nondeg hΦ_refl hL

open Module Submodule in
/--
lemma `orthogonal_isCompl_toSubmodule` / 引理 `orthogonal_isCompl_toSubmodule`

English:
lemma orthogonal_isCompl_toSubmodule
  given: (I : LieIdeal K L) (hI : IsAtom I)
  proof: by
  rw [orthogonal_toSubmodule]; rw [LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint hΦ_refl]; rw [← orthogonal_toSubmodule _ hΦ_inv]; rw [LieSubmodule.disjoint_toSubmodule]
  exact orthogonal_disjoint Φ hΦ_nondeg hΦ_inv hL I hI

中文:
引理 orthogonal_isCompl_toSubmodule
  条件: (I : LieIdeal K L) (hI : IsAtom I)
  证明: by
  rw [orthogonal_toSubmodule]; rw [LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint hΦ_refl]; rw [← orthogonal_toSubmodule _ hΦ_inv]; rw [LieSubmodule.disjoint_toSubmodule]
  exact orthogonal_disjoint Φ hΦ_nondeg hΦ_inv hL I hI

Depends on / 依赖: BilinForm, LieSubmodule, LieSubmodule.disjoint_toSubmodule, LinearMap, LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint, Module, Module.Free, Module.Projective, Projective, Projective.of_free, disjoint_toSubmodule, isCompl_orthogonal_iff_disjoint, of_free, orthogonal_disjoint, orthogonal_toSubmodule
-/
lemma orthogonal_isCompl_toSubmodule (I : LieIdeal K L) (hI : IsAtom I) :
    IsCompl I.toSubmodule (orthogonal Φ hΦ_inv I).toSubmodule := by
  rw [orthogonal_toSubmodule]; rw [LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint hΦ_refl]; rw [← orthogonal_toSubmodule _ hΦ_inv]; rw [LieSubmodule.disjoint_toSubmodule]
  exact orthogonal_disjoint Φ hΦ_nondeg hΦ_inv hL I hI

open Module Submodule in
/--
lemma `orthogonal_isCompl` / 引理 `orthogonal_isCompl`

English:
lemma orthogonal_isCompl
  given: (I : LieIdeal K L) (hI : IsAtom I)
  proof: by
  rw [← LieSubmodule.isCompl_toSubmodule]
  exact orthogonal_isCompl_toSubmodule Φ hΦ_nondeg hΦ_inv hΦ_refl hL I hI

include hΦ_inv

中文:
引理 orthogonal_isCompl
  条件: (I : LieIdeal K L) (hI : IsAtom I)
  证明: by
  rw [← LieSubmodule.isCompl_toSubmodule]
  exact orthogonal_isCompl_toSubmodule Φ hΦ_nondeg hΦ_inv hΦ_refl hL I hI

include hΦ_inv

Depends on / 依赖: LieSubmodule, LieSubmodule.isCompl_toSubmodule, isCompl_toSubmodule, orthogonal_isCompl_toSubmodule
-/
lemma orthogonal_isCompl (I : LieIdeal K L) (hI : IsAtom I) :
    IsCompl I (orthogonal Φ hΦ_inv I) := by
  rw [← LieSubmodule.isCompl_toSubmodule]
  exact orthogonal_isCompl_toSubmodule Φ hΦ_nondeg hΦ_inv hΦ_refl hL I hI

include hΦ_inv

/--
lemma `restrict_nondegenerate` / 引理 `restrict_nondegenerate`

English:
lemma restrict_nondegenerate
  given: (I : LieIdeal K L) (hI : IsAtom I)
  proof: by
  rw [LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal hΦ_refl]
  exact orthogonal_isCompl_toSubmodule Φ hΦ_nondeg hΦ_inv hΦ_refl hL I hI

中文:
引理 restrict_nondegenerate
  条件: (I : LieIdeal K L) (hI : IsAtom I)
  证明: by
  rw [LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal hΦ_refl]
  exact orthogonal_isCompl_toSubmodule Φ hΦ_nondeg hΦ_inv hΦ_refl hL I hI

Depends on / 依赖: BilinForm, LinearMap, LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal, orthogonal_isCompl_toSubmodule, restrict_nondegenerate_iff_isCompl_orthogonal
-/
lemma restrict_nondegenerate (I : LieIdeal K L) (hI : IsAtom I) :
    (Φ.restrict I).Nondegenerate := by
  rw [LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal hΦ_refl]
  exact orthogonal_isCompl_toSubmodule Φ hΦ_nondeg hΦ_inv hΦ_refl hL I hI

/--
lemma `restrict_orthogonal_nondegenerate` / 引理 `restrict_orthogonal_nondegenerate`

English:
lemma restrict_orthogonal_nondegenerate
  given: (I : LieIdeal K L) (hI : IsAtom I)
  proof: by
  rw [LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal hΦ_refl]
  simp only [LieIdeal.toLieSubalgebra_toSubmodule, orthogonal_toSubmodule,
    LinearMap.BilinForm.orthogonal_orthogonal hΦ_nondeg hΦ_refl]
  exact (orthogonal_isCompl_toSubmodule Φ hΦ_nondeg hΦ_inv hΦ_refl hL I hI).symm

中文:
引理 restrict_orthogonal_nondegenerate
  条件: (I : LieIdeal K L) (hI : IsAtom I)
  证明: by
  rw [LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal hΦ_refl]
  simp only [LieIdeal.toLieSubalgebra_toSubmodule, orthogonal_toSubmodule,
    LinearMap.BilinForm.orthogonal_orthogonal hΦ_nondeg hΦ_refl]
  exact (orthogonal_isCompl_toSubmodule Φ hΦ_nondeg hΦ_inv hΦ_refl hL I hI).symm

Depends on / 依赖: BilinForm, LieIdeal, LieIdeal.toLieSubalgebra_toSubmodule, LinearMap, LinearMap.BilinForm.orthogonal_orthogonal, LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal, orthogonal_isCompl_toSubmodule, orthogonal_orthogonal, orthogonal_toSubmodule, restrict_nondegenerate_iff_isCompl_orthogonal, toLieSubalgebra_toSubmodule
-/
lemma restrict_orthogonal_nondegenerate (I : LieIdeal K L) (hI : IsAtom I) :
    (Φ.restrict (orthogonal Φ hΦ_inv I)).Nondegenerate := by
  rw [LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal hΦ_refl]
  simp only [LieIdeal.toLieSubalgebra_toSubmodule, orthogonal_toSubmodule,
    LinearMap.BilinForm.orthogonal_orthogonal hΦ_nondeg hΦ_refl]
  exact (orthogonal_isCompl_toSubmodule Φ hΦ_nondeg hΦ_inv hΦ_refl hL I hI).symm

open Module Submodule in
/--
lemma `atomistic` / 引理 `atomistic`

English:
lemma atomistic
  statement: forall I : LieIdeal K L, sSup {J : LieIdeal K L | IsAtom J ∧ J <= I} = I
  proof: by
  intro I
  apply le_antisymm
  · apply sSup_le
    rintro J ⟨-, hJ'⟩
    exact hJ'
  by_cases hI : I = ⊥
  · exact hI.le.trans bot_le
  obtain ⟨J, hJ, hJI⟩ := (eq_bot_or_exists_atom_le I).resolve_left hI
  let J' := orthogonal Φ hΦ_inv J
  suffices I <= J ⊔ (J' ⊓ I) by
    refine this.trans ?_
    apply sup_le
    · exact le_sSup ⟨hJ, hJI⟩
    rw [← atomistic (J' ⊓ I)]
    apply sSup_le_sSup
    simp only [le_inf_iff, Set.ofPred_subset_ofPred, and_imp]
    tauto
  suffices J ⊔ J' = ⊤ by rw [← sup_inf_assoc_of_le _ hJI, this, top_inf_eq]
  exact (orthogonal_isCompl Φ hΦ_nondeg hΦ_inv hΦ_refl hL J hJ).codisjoint.eq_top
termination_by I => finrank K I
decreasing_by
  apply finrank_lt_finrank_of_lt
  suffices ¬I <= J' by simpa
  intro hIJ'
  apply hJ.1
  rw [eq_bot_iff]
  exact orthogonal_disjoint Φ hΦ_nondeg hΦ_inv hL J hJ le_rfl (hJI.trans hIJ')

中文:
引理 atomistic
  结论: 对任意 I : LieIdeal K L, sSup {J : LieIdeal K L | IsAtom J ∧ J <= I} = I
  证明: by
  intro I
  apply le_antisymm
  · apply sSup_le
    rintro J ⟨-, hJ'⟩
    exact hJ'
  by_cases hI : I = ⊥
  · exact hI.le.trans bot_le
  obtain ⟨J, hJ, hJI⟩ := (eq_bot_or_exists_atom_le I).resolve_left hI
  let J' := orthogonal Φ hΦ_inv J
  suffices I <= J ⊔ (J' ⊓ I) by
    refine this.trans ?_
    apply sup_le
    · exact le_sSup ⟨hJ, hJI⟩
    rw [← atomistic (J' ⊓ I)]
    apply sSup_le_sSup
    simp only [le_inf_iff, Set.ofPred_subset_ofPred, and_imp]
    tauto
  suffices J ⊔ J' = ⊤ by rw [← sup_inf_assoc_of_le _ hJI, this, top_inf_eq]
  exact (orthogonal_isCompl Φ hΦ_nondeg hΦ_inv hΦ_refl hL J hJ).codisjoint.eq_top
termination_by I => finrank K I
decreasing_by
  apply finrank_lt_finrank_of_lt
  suffices ¬I <= J' by simpa
  intro hIJ'
  apply hJ.1
  rw [eq_bot_iff]
  exact orthogonal_disjoint Φ hΦ_nondeg hΦ_inv hL J hJ le_rfl (hJI.trans hIJ')

Depends on / 依赖: Set.ofPred_subset_ofPred, and_imp, atomistic, bot_le, eq_bot_or_exists_atom_le, hI.le.trans, le_antisymm, le_inf_iff, le_sSup, ofPred_subset_ofPred, orthogonal, resolve_left, sSup_le, sSup_le_sSup, sup_inf_assoc_of_le, sup_le, this.trans, top_inf_eq
-/
lemma atomistic : forall I : LieIdeal K L, sSup {J : LieIdeal K L | IsAtom J ∧ J <= I} = I := by
  intro I
  apply le_antisymm
  · apply sSup_le
    rintro J ⟨-, hJ'⟩
    exact hJ'
  by_cases hI : I = ⊥
  · exact hI.le.trans bot_le
  obtain ⟨J, hJ, hJI⟩ := (eq_bot_or_exists_atom_le I).resolve_left hI
  let J' := orthogonal Φ hΦ_inv J
  suffices I <= J ⊔ (J' ⊓ I) by
    refine this.trans ?_
    apply sup_le
    · exact le_sSup ⟨hJ, hJI⟩
    rw [← atomistic (J' ⊓ I)]
    apply sSup_le_sSup
    simp only [le_inf_iff, Set.ofPred_subset_ofPred, and_imp]
    tauto
  suffices J ⊔ J' = ⊤ by rw [← sup_inf_assoc_of_le _ hJI, this, top_inf_eq]
  exact (orthogonal_isCompl Φ hΦ_nondeg hΦ_inv hΦ_refl hL J hJ).codisjoint.eq_top
termination_by I => finrank K I
decreasing_by
  apply finrank_lt_finrank_of_lt
  suffices ¬I <= J' by simpa
  intro hIJ'
  apply hJ.1
  rw [eq_bot_iff]
  exact orthogonal_disjoint Φ hΦ_nondeg hΦ_inv hL J hJ le_rfl (hJI.trans hIJ')

open LieSubmodule in
/--
theorem `isSemisimple_of_nondegenerate` / 定理 `isSemisimple_of_nondegenerate`

English:
theorem isSemisimple_of_nondegenerate
  statement: IsSemisimple K L
  proof: by
  refine ⟨?_, ?_, hL⟩
  · simpa using atomistic Φ hΦ_nondeg hΦ_inv hΦ_refl hL ⊤
  intro I hI
  apply (orthogonal_disjoint Φ hΦ_nondeg hΦ_inv hL I hI).mono_right
  apply sSup_le
  simp only [Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_singleton_iff, and_imp]
  intro J hJ hJI
  rw [← lie_eq_self_of_isAtom_of_nonabelian J hJ (hL J hJ)]; rw [lieIdeal_oper_eq_span]; rw [lieSpan_le]
  rintro _ ⟨x, y, rfl⟩
  simp only [orthogonal_carrier, Set.mem_ofPred_eq]
  intro z hz
  rw [← neg_eq_zero]; rw [← hΦ_inv]
  suffices ⁅(x : L), z⁆ = 0 by simp only [this, map_zero, LinearMap.zero_apply]
  rw [← LieSubmodule.mem_bot (R := K) (L := L)]; rw [← (hJ.disjoint_of_ne hI hJI).eq_bot]
  apply lie_le_inf
  exact lie_mem_lie x.2 hz

中文:
定理 isSemisimple_of_nondegenerate
  结论: 是半单 K L
  证明: by
  refine ⟨?_, ?_, hL⟩
  · simpa using atomistic Φ hΦ_nondeg hΦ_inv hΦ_refl hL ⊤
  intro I hI
  apply (orthogonal_disjoint Φ hΦ_nondeg hΦ_inv hL I hI).mono_right
  apply sSup_le
  simp only [Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_singleton_iff, and_imp]
  intro J hJ hJI
  rw [← lie_eq_self_of_isAtom_of_nonabelian J hJ (hL J hJ)]; rw [lieIdeal_oper_eq_span]; rw [lieSpan_le]
  rintro _ ⟨x, y, rfl⟩
  simp only [orthogonal_carrier, Set.mem_ofPred_eq]
  intro z hz
  rw [← neg_eq_zero]; rw [← hΦ_inv]
  suffices ⁅(x : L), z⁆ = 0 by simp only [this, map_zero, LinearMap.zero_apply]
  rw [← LieSubmodule.mem_bot (R := K) (L := L)]; rw [← (hJ.disjoint_of_ne hI hJI).eq_bot]
  apply lie_le_inf
  exact lie_mem_lie x.2 hz

Depends on / 依赖: Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_singleton_iff, and_imp, atomistic, lieIdeal_oper_eq_span, lieSpan_le, lie_eq_self_of_isAtom_of_nonabelian, mem_ofPred_eq, mem_sdiff, mem_singleton_iff, mono_right, neg_eq_zero, orthogonal_carrier, orthogonal_disjoint, sSup_le
-/
theorem isSemisimple_of_nondegenerate : IsSemisimple K L := by
  refine ⟨?_, ?_, hL⟩
  · simpa using atomistic Φ hΦ_nondeg hΦ_inv hΦ_refl hL ⊤
  intro I hI
  apply (orthogonal_disjoint Φ hΦ_nondeg hΦ_inv hL I hI).mono_right
  apply sSup_le
  simp only [Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_singleton_iff, and_imp]
  intro J hJ hJI
  rw [← lie_eq_self_of_isAtom_of_nonabelian J hJ (hL J hJ)]; rw [lieIdeal_oper_eq_span]; rw [lieSpan_le]
  rintro _ ⟨x, y, rfl⟩
  simp only [orthogonal_carrier, Set.mem_ofPred_eq]
  intro z hz
  rw [← neg_eq_zero]; rw [← hΦ_inv]
  suffices ⁅(x : L), z⁆ = 0 by simp only [this, map_zero, LinearMap.zero_apply]
  rw [← LieSubmodule.mem_bot (R := K) (L := L)]; rw [← (hJ.disjoint_of_ne hI hJI).eq_bot]
  apply lie_le_inf
  exact lie_mem_lie x.2 hz

end field

end InvariantForm

end LieAlgebra
