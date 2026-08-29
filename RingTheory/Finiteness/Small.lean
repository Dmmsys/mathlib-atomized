/-
Copyright (c) 2025 Antoine Chambert-Loir, María-Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, Maria-Inés de Frutos-Fernandez
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.FiniteType
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.LinearAlgebra.Basis.Cardinality
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Data.DFinsupp.Small

/-! # Smallness properties of modules and algebras -/

public section

universe u

namespace Submodule

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/--
Instance `small_sup` / 实例 `small_sup`

English:
instance small_sup
  signature: {P Q : Submodule R M} [smallP : Small.{u} P] [smallQ : Small.{u} Q]
  body: by
  rw [Submodule.sup_eq_range]
  exact small_range _

中文:
实例 small_sup
  签名: {P Q : 子模 R M} [smallP : Small.{u} P] [smallQ : Small.{u} Q]
  定义体: by
  rw [Submodule.sup_eq_range]
  exact small_range _

Depends on / 依赖: Submodule, Submodule.sup_eq_range, small_range, sup_eq_range
-/
instance small_sup {P Q : Submodule R M} [smallP : Small.{u} P] [smallQ : Small.{u} Q] :
    Small.{u} (P ⊔ Q : Submodule R M) := by
  rw [Submodule.sup_eq_range]
  exact small_range _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SemilatticeSup {P : Submodule R M // Small.{u} P}
  body: fun P Q => ⟨P.val ⊔ Q.val, small_sup (smallP := P.property) (smallQ := Q.property)⟩
  le_sup_left := fun P Q => by rw [← Subtype.coe_le_coe]; exact le_sup_left
  le_sup_right := fun P Q => by rw [← Subtype.coe_le_coe]; exact le_sup_right
  sup_le := fun _ _ _ hPR hQR => by
    rw [← Subtype.coe_le_coe] at hPR hQR ⊢
    exact sup_le hPR hQR

中文:
实例 :
  签名: SemilatticeSup {P : 子模 R M // Small.{u} P}
  定义体: fun P Q => ⟨P.val ⊔ Q.val, small_sup (smallP := P.property) (smallQ := Q.property)⟩
  le_sup_left := fun P Q => by rw [← Subtype.coe_le_coe]; exact le_sup_left
  le_sup_right := fun P Q => by rw [← Subtype.coe_le_coe]; exact le_sup_right
  sup_le := fun _ _ _ hPR hQR => by
    rw [← Subtype.coe_le_coe] at hPR hQR ⊢
    exact sup_le hPR hQR

Depends on / 依赖: P.property, P.val, Q.property, Q.val, property, smallP, smallQ, small_sup
-/
instance : SemilatticeSup {P : Submodule R M // Small.{u} P} where
  sup := fun P Q => ⟨P.val ⊔ Q.val, small_sup (smallP := P.property) (smallQ := Q.property)⟩
  le_sup_left := fun P Q => by rw [← Subtype.coe_le_coe]; exact le_sup_left
  le_sup_right := fun P Q => by rw [← Subtype.coe_le_coe]; exact le_sup_right
  sup_le := fun _ _ _ hPR hQR => by
    rw [← Subtype.coe_le_coe] at hPR hQR ⊢
    exact sup_le hPR hQR

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited {P : Submodule R M // Small.{u} P}
  body: ⟨⊥, inferInstance⟩

中文:
实例 :
  签名: 可居 {P : 子模 R M // Small.{u} P}
  定义体: ⟨⊥, inferInstance⟩
-/
instance : Inhabited {P : Submodule R M // Small.{u} P} where
  default := ⟨⊥, inferInstance⟩

/--
Instance `small_iSup` / 实例 `small_iSup`

English:
instance small_iSup
  body: by
  classical
  rw [iSup_eq_range_dfinsupp_lsum]
  apply small_range

中文:
实例 small_iSup
  定义体: by
  classical
  rw [iSup_eq_range_dfinsupp_lsum]
  apply small_range

Depends on / 依赖: classical, iSup_eq_range_dfinsupp_lsum, small_range
-/
instance small_iSup
    {ι : Type*} {P : ι -> Submodule R M} [Small.{u} ι] [forall i, Small.{u} (P i)] :
    Small.{u} (iSup P : Submodule R M) := by
  classical
  rw [iSup_eq_range_dfinsupp_lsum]
  apply small_range

/--
theorem `FG.small` / 定理 `FG.small`

English:
theorem FG.small
  given: [Small.{u} R] (P : Submodule R M) (hP : P.FG)
  statement: Small.{u} P
  proof: by
  rw [fg_iff_exists_fin_generating_family] at hP
  obtain ⟨n, s, rfl⟩ := hP
  rw [← Fintype.range_linearCombination]
  apply small_range

中文:
定理 FG.small
  条件: [Small.{u} R] (P : 子模 R M) (hP : P.FG)
  结论: Small.{u} P
  证明: by
  rw [fg_iff_exists_fin_generating_family] at hP
  obtain ⟨n, s, rfl⟩ := hP
  rw [← Fintype.range_linearCombination]
  apply small_range

Depends on / 依赖: Fintype, Fintype.range_linearCombination, fg_iff_exists_fin_generating_family, range_linearCombination, small_range
-/
theorem FG.small [Small.{u} R] (P : Submodule R M) (hP : P.FG) : Small.{u} P := by
  rw [fg_iff_exists_fin_generating_family] at hP
  obtain ⟨n, s, rfl⟩ := hP
  rw [← Fintype.range_linearCombination]
  apply small_range

variable (R M) in
/--
theorem `_root_.Module.Finite.small` / 定理 `_root_.Module.Finite.small`

English:
theorem _root_.Module.Finite.small
  given: [Small.{u} R] [Module.Finite R M]
  statement: Small.{u} M
  proof: by
  have : Small.{u} (⊤ : Submodule R M) :=
    FG.small _ (Module.finite_def.mp inferInstance)
  rwa [← small_univ_iff]

中文:
定理 _root_.模.有限.small
  条件: [Small.{u} R] [模.有限 R M]
  结论: Small.{u} M
  证明: by
  have : Small.{u} (⊤ : Submodule R M) :=
    FG.small _ (Module.finite_def.mp inferInstance)
  rwa [← small_univ_iff]

Depends on / 依赖: FG.small, Module, Module.finite_def.mp, Submodule, finite_def, small_univ_iff
-/
theorem _root_.Module.Finite.small [Small.{u} R] [Module.Finite R M] : Small.{u} M := by
  have : Small.{u} (⊤ : Submodule R M) :=
    FG.small _ (Module.finite_def.mp inferInstance)
  rwa [← small_univ_iff]

/--
Instance `small_span_singleton` / 实例 `small_span_singleton`

English:
instance small_span_singleton
  signature: [Small.{u} R] (m : M)
  body: FG.small _ (fg_span_singleton _)

中文:
实例 small_span_singleton
  签名: [Small.{u} R] (m : M)
  定义体: FG.small _ (fg_span_singleton _)

Depends on / 依赖: FG.small, fg_span_singleton
-/
instance small_span_singleton [Small.{u} R] (m : M) :
    Small.{u} (span R {m}) := FG.small _ (fg_span_singleton _)

/--
theorem `small_span` / 定理 `small_span`

English:
theorem small_span
  given: [Small.{u} R] (s : Set M) [Small.{u} s]
  proof: by
  suffices span R s = iSup (fun i : s => span R ({(↑i : M)} : Set M)) by
    rw [this]
    apply small_iSup
  simp [← Submodule.span_iUnion]

中文:
定理 small_span
  条件: [Small.{u} R] (s : 集合 M) [Small.{u} s]
  证明: by
  suffices span R s = iSup (fun i : s => span R ({(↑i : M)} : Set M)) by
    rw [this]
    apply small_iSup
  simp [← Submodule.span_iUnion]

Depends on / 依赖: Submodule, Submodule.span_iUnion, small_iSup, span_iUnion
-/
theorem small_span [Small.{u} R] (s : Set M) [Small.{u} s] :
    Small.{u} (span R s) := by
  suffices span R s = iSup (fun i : s => span R ({(↑i : M)} : Set M)) by
    rw [this]
    apply small_iSup
  simp [← Submodule.span_iUnion]

end Submodule

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

namespace Algebra

open MvPolynomial AlgHom

/--
Instance `small_adjoin` / 实例 `small_adjoin`

English:
instance small_adjoin
  signature: [Small.{u} R] {s : Set S} [Small.{u} s]
  body: by
  rw [Algebra.adjoin_eq_range]
  apply small_range

中文:
实例 small_adjoin
  签名: [Small.{u} R] {s : 集合 S} [Small.{u} s]
  定义体: by
  rw [Algebra.adjoin_eq_range]
  apply small_range

Depends on / 依赖: Algebra, Algebra.adjoin_eq_range, adjoin_eq_range, small_range
-/
instance small_adjoin [Small.{u} R] {s : Set S} [Small.{u} s] :
    Small.{u} (adjoin R s : Subalgebra R S) := by
  rw [Algebra.adjoin_eq_range]
  apply small_range

/--
theorem `_root_.Subalgebra.FG.small` / 定理 `_root_.Subalgebra.FG.small`

English:
theorem _root_.Subalgebra.FG.small
  given: [Small.{u} R] {A : Subalgebra R S} (fgS : A.FG)
  proof: by
  obtain ⟨s, hs, rfl⟩ := fgS
  exact small_adjoin

中文:
定理 _root_.子代数.FG.small
  条件: [Small.{u} R] {A : 子代数 R S} (fgS : A.FG)
  证明: by
  obtain ⟨s, hs, rfl⟩ := fgS
  exact small_adjoin

Depends on / 依赖: small_adjoin
-/
theorem _root_.Subalgebra.FG.small [Small.{u} R] {A : Subalgebra R S} (fgS : A.FG) :
    Small.{u} A := by
  obtain ⟨s, hs, rfl⟩ := fgS
  exact small_adjoin

/--
theorem `FiniteType.small` / 定理 `FiniteType.small`

English:
theorem FiniteType.small
  given: [Small.{u} R] [Algebra.FiniteType R S]
  proof: by
  have : Small.{u} (⊤ : Subalgebra R S) :=
    Subalgebra.FG.small Algebra.FiniteType.out
  rwa [← small_univ_iff]

中文:
定理 有限型.small
  条件: [Small.{u} R] [代数.有限型 R S]
  证明: by
  have : Small.{u} (⊤ : Subalgebra R S) :=
    Subalgebra.FG.small Algebra.FiniteType.out
  rwa [← small_univ_iff]

Depends on / 依赖: Algebra, Algebra.FiniteType.out, FiniteType, Subalgebra, Subalgebra.FG.small, small_univ_iff
-/
theorem FiniteType.small [Small.{u} R] [Algebra.FiniteType R S] :
    Small.{u} S := by
  have : Small.{u} (⊤ : Subalgebra R S) :=
    Subalgebra.FG.small Algebra.FiniteType.out
  rwa [← small_univ_iff]

end Algebra
