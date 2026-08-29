/-
Copyright (c) 2026 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Morrison
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Basis for `ExteriorAlgebra`
-/

@[expose] public section

namespace ExteriorAlgebra

open Module Set Set.powersetCard exteriorPower

variable {R M : Type*} {m n : Nat} {I : Type*} [LinearOrder I] [CommRing R]
  [AddCommGroup M] [Module R M] (b : Module.Basis I R M)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DirectSum.Decomposition (fun n => ⋀[R]^n M)
  body: GradedRing.toDecomposition (self := ExteriorAlgebra.gradedAlgebra R M)

中文:
实例 :
  签名: 直和.分解 (fun n => ⋀[R]^n M)
  定义体: GradedRing.toDecomposition (self := ExteriorAlgebra.gradedAlgebra R M)

Depends on / 依赖: ExteriorAlgebra, ExteriorAlgebra.gradedAlgebra, GradedRing, GradedRing.toDecomposition, gradedAlgebra, toDecomposition
-/
instance : DirectSum.Decomposition (fun n => ⋀[R]^n M) :=
  GradedRing.toDecomposition (self := ExteriorAlgebra.gradedAlgebra R M)

/--
Definition of `_root_.Module.Basis.ExteriorAlgebra` / `_root_.Module.Basis.ExteriorAlgebra` 的定义

English:
definition _root_.Module.Basis.ExteriorAlgebra
  signature: : Basis (Finset I) R (ExteriorAlgebra R M)
  body: .reindex
    ((DirectSum.Decomposition.isInternal (fun n => ⋀[R]^n M)).collectedBasis b.exteriorPower)
    Set.powersetCard.prodEquiv

中文:
定义 _root_.模.基.ExteriorAlgebra
  签名: : 基 (有限集 I) R (ExteriorAlgebra R M)
  定义体: .reindex
    ((DirectSum.Decomposition.isInternal (fun n => ⋀[R]^n M)).collectedBasis b.exteriorPower)
    Set.powersetCard.prodEquiv

Depends on / 依赖: Decomposition, DirectSum, DirectSum.Decomposition.isInternal, Set.powersetCard.prodEquiv, b.exteriorPower, collectedBasis, exteriorPower, isInternal, powersetCard, prodEquiv, reindex
-/
noncomputable def _root_.Module.Basis.ExteriorAlgebra : Basis (Finset I) R (ExteriorAlgebra R M) :=
  .reindex
    ((DirectSum.Decomposition.isInternal (fun n => ⋀[R]^n M)).collectedBasis b.exteriorPower)
    Set.powersetCard.prodEquiv

/--
lemma `basis_apply` / 引理 `basis_apply`

English:
lemma basis_apply
  given: (s : Finset I)
  proof: by
  simp [Basis.ExteriorAlgebra]

中文:
引理 basis_apply
  条件: (s : 有限集 I)
  证明: by
  simp [Basis.ExteriorAlgebra]

Depends on / 依赖: Basis.ExteriorAlgebra, ExteriorAlgebra
-/
lemma basis_apply (s : Finset I) :
    b.ExteriorAlgebra s = ιMulti_family R s.card b (prodEquiv.symm s).2 := by
  simp [Basis.ExteriorAlgebra]

/--
lemma `basis_apply_ofCard` / 引理 `basis_apply_ofCard`

English:
lemma basis_apply_ofCard
  given: {s : Finset I} (s_card : s.card = n)
  proof: by
  subst s_card
  simp [basis_apply]

中文:
引理 basis_apply_ofCard
  条件: {s : 有限集 I} (s_card : s.card = n)
  证明: by
  subst s_card
  simp [basis_apply]

Depends on / 依赖: basis_apply, s_card
-/
lemma basis_apply_ofCard {s : Finset I} (s_card : s.card = n) :
    b.ExteriorAlgebra s = ιMulti_family R n b (ofCard s_card) := by
  subst s_card
  simp [basis_apply]

variable (s : powersetCard I m) (t : powersetCard I n)

/--
lemma `basis_apply_powersetCard` / 引理 `basis_apply_powersetCard`

English:
lemma basis_apply_powersetCard
  proof: by
  simp [basis_apply_ofCard]

中文:
引理 basis_apply_powersetCard
  证明: by
  simp [basis_apply_ofCard]

Depends on / 依赖: basis_apply_ofCard
-/
lemma basis_apply_powersetCard :
    b.ExteriorAlgebra s = ιMulti_family R m b s := by
  simp [basis_apply_ofCard]

/--
lemma `basis_eq_coe_basis` / 引理 `basis_eq_coe_basis`

English:
lemma basis_eq_coe_basis
  proof: by
  rw [basis_apply_powersetCard]; rw [exteriorPower.basis_apply]; rw [ιMulti_family_apply_coe]

中文:
引理 basis_eq_coe_basis
  证明: by
  rw [basis_apply_powersetCard]; rw [exteriorPower.basis_apply]; rw [ιMulti_family_apply_coe]

Depends on / 依赖: basis_apply, basis_apply_powersetCard, exteriorPower, exteriorPower.basis_apply
-/
lemma basis_eq_coe_basis :
    b.ExteriorAlgebra s = (b.exteriorPower m s : ExteriorAlgebra R M) := by
  rw [basis_apply_powersetCard]; rw [exteriorPower.basis_apply]; rw [ιMulti_family_apply_coe]

/--
lemma `basis_mul_of_not_disjoint` / 引理 `basis_mul_of_not_disjoint`

English:
lemma basis_mul_of_not_disjoint
  given: (h : ¬Disjoint s.val t.val)
  proof: by
  simpa only [basis_apply_powersetCard] using ιMulti_family_mul_of_not_disjoint R b s t h

中文:
引理 basis_mul_of_not_disjoint
  条件: (h : ¬Disjoint s.val t.val)
  证明: by
  simpa only [basis_apply_powersetCard] using ιMulti_family_mul_of_not_disjoint R b s t h

Depends on / 依赖: basis_apply_powersetCard
-/
lemma basis_mul_of_not_disjoint (h : ¬Disjoint s.val t.val) :
    b.ExteriorAlgebra s * b.ExteriorAlgebra t = 0 := by
  simpa only [basis_apply_powersetCard] using ιMulti_family_mul_of_not_disjoint R b s t h

/--
lemma `basis_mul_of_disjoint` / 引理 `basis_mul_of_disjoint`

English:
lemma basis_mul_of_disjoint
  given: (h : Disjoint s.val t.val)
  proof: by
  simpa only [basis_apply_powersetCard] using ιMulti_family_mul_of_disjoint R b s t h

中文:
引理 basis_mul_of_disjoint
  条件: (h : Disjoint s.val t.val)
  证明: by
  simpa only [basis_apply_powersetCard] using ιMulti_family_mul_of_disjoint R b s t h

Depends on / 依赖: basis_apply_powersetCard
-/
lemma basis_mul_of_disjoint (h : Disjoint s.val t.val) :
    b.ExteriorAlgebra s * b.ExteriorAlgebra t =
      (permOfDisjoint h).sign • b.ExteriorAlgebra (disjUnion h) := by
  simpa only [basis_apply_powersetCard] using ιMulti_family_mul_of_disjoint R b s t h

end ExteriorAlgebra
