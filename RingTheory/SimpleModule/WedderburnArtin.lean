/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.SimpleModule.Isotypic
public import Mathlib.RingTheory.SimpleRing.Congr
public import Mathlib.RingTheory.SimpleRing.Matrix

/-!
# Wedderburn–Artin Theorem

## Main results

* `IsSimpleRing.tfae`: a simple ring is semisimple iff it is Artinian,
  iff it has a minimal left ideal.

* `isSimpleRing_isArtinianRing_iff`: a ring is simple Artinian iff it is semisimple, isotypic,
  and nontrivial.

* `IsSimpleRing.exists_algEquiv_matrix_end_mulOpposite`: a simple Artinian algebra is
  isomorphic to a (finite-dimensional) matrix algebra over a division algebra. The division
  algebra is the opposite of the endomorphism algebra of a simple (i.e., minimal) left ideal.

* `IsSemisimpleRing.exists_algEquiv_pi_matrix_end_mulOpposite`: a semisimple algebra is
  isomorphic to a finite direct product of matrix algebras over division algebras. The division
  algebras are the opposites of the endomorphism algebras of the simple (i.e., minimal)
  left ideals.

* `IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite`,
  `IsSemisimpleRing.exists_algEquiv_pi_matrix_divisionRing_finite`:
  if the simple Artinian / semisimple algebra is finite as a module over a base ring, then the
  division algebra(s) are also finite over the same ring.
  If the base ring is an algebraically closed field, the only finite-dimensional division algebra
  over it is itself, and we obtain `IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed` and
  `IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed` (in a later file).

-/

public section

universe u
variable (R₀ : Type*) {R : Type u} [CommSemiring R₀] [Ring R] [Algebra R₀ R]

/--
theorem `IsSimpleRing.tfae` / 定理 `IsSimpleRing.tfae`

English:
theorem IsSimpleRing.tfae
  given: [IsSimpleRing R]
  statement: List.TFAE
  proof: by
  tfae_have 1 -> 2 := fun _ => inferInstance
  tfae_have 2 -> 3 := fun _ => IsAtomic.exists_atom _
  tfae_have 3 -> 1 := fun ⟨I, hI⟩ => by
    have ⟨_, h⟩ := isSimpleRing_iff_isTwoSided_imp.mp ‹IsSimpleRing R›
    simp_rw [← isFullyInvariant_iff_isTwoSided] at h
    have := isSimpleModule_iff_isA

中文:
定理 是单环.tfae
  条件: [是单环 R]
  结论: 列表.TFAE
  证明: by
  tfae_have 1 -> 2 := fun _ => inferInstance
  tfae_have 2 -> 3 := fun _ => IsAtomic.exists_atom _
  tfae_have 3 -> 1 := fun ⟨I, hI⟩ => by
    have ⟨_, h⟩ := isSimpleRing_iff_isTwoSided_imp.mp ‹IsSimpleRing R›
    simp_rw [← isFullyInvariant_iff_isTwoSided] at h
    have := isSimpleModule_iff_isA

Depends on / 依赖: IsAtomic, IsAtomic.exists_atom, IsSimpleRing, Submodule, Submodule.topEquiv, bot_lt, exists_atom, hI.bot_lt.not_ge, isFullyInvariant_iff_isTwoSided, isSimpleModule_iff_isAtom, isSimpleModule_iff_isAtom.mpr, isSimpleRing_iff_isTwoSided_imp, isSimpleRing_iff_isTwoSided_imp.mp, isotypicComponent, le_sSup, not_ge, simp_rw, tfae_finish, tfae_have, topEquiv
-/
theorem IsSimpleRing.tfae [IsSimpleRing R] : List.TFAE
    [IsSemisimpleRing R, IsArtinianRing R, exists I : Ideal R, IsAtom I] := by
  tfae_have 1 -> 2 := fun _ => inferInstance
  tfae_have 2 -> 3 := fun _ => IsAtomic.exists_atom _
  tfae_have 3 -> 1 := fun ⟨I, hI⟩ => by
    have ⟨_, h⟩ := isSimpleRing_iff_isTwoSided_imp.mp ‹IsSimpleRing R›
    simp_rw [← isFullyInvariant_iff_isTwoSided] at h
    have := isSimpleModule_iff_isAtom.mpr hI
    obtain eq | eq := h _ (.isotypicComponent R R I)
    · exact (hI.bot_lt.not_ge <| (le_sSup <| by exact ⟨.refl ..⟩).trans_eq eq).elim
    exact .congr (.symm <| .trans (.ofEq _ _ eq) Submodule.topEquiv)
  tfae_finish

/--
theorem `IsSimpleRing.isSemisimpleRing_iff_isArtinianRing` / 定理 `IsSimpleRing.isSemisimpleRing_iff_isArtinianRing`

English:
theorem IsSimpleRing.isSemisimpleRing_iff_isArtinianRing
  given: [IsSimpleRing R]
  proof: tfae.out 0 1

中文:
定理 是单环.isSemisimpleRing_iff_isArtinianRing
  条件: [是单环 R]
  证明: tfae.out 0 1

Depends on / 依赖: tfae.out
-/
theorem IsSimpleRing.isSemisimpleRing_iff_isArtinianRing [IsSimpleRing R] :
    IsSemisimpleRing R ↔ IsArtinianRing R := tfae.out 0 1

/--
theorem `isSimpleRing_isArtinianRing_iff` / 定理 `isSimpleRing_isArtinianRing_iff`

English:
theorem isSimpleRing_isArtinianRing_iff
  proof: by
  refine ⟨fun ⟨_, _⟩ => ?_, fun ⟨_, _, _⟩ => ?_⟩
  on_goal 1 => have := IsSimpleRing.isSemisimpleRing_iff_isArtinianRing.mpr ‹_›
  all_goals simp_rw [isIsotypic_iff_isFullyInvariant_imp_bot_or_top,
      isFullyInvariant_iff_isTwoSided, isSimpleRing_iff_isTwoSided_imp] at *
  · exact ⟨this, by rw

中文:
定理 isSimpleRing_isArtinianRing_iff
  证明: by
  refine ⟨fun ⟨_, _⟩ => ?_, fun ⟨_, _, _⟩ => ?_⟩
  on_goal 1 => have := IsSimpleRing.isSemisimpleRing_iff_isArtinianRing.mpr ‹_›
  all_goals simp_rw [isIsotypic_iff_isFullyInvariant_imp_bot_or_top,
      isFullyInvariant_iff_isTwoSided, isSimpleRing_iff_isTwoSided_imp] at *
  · exact ⟨this, by rw

Depends on / 依赖: IsSimpleRing, IsSimpleRing.isSemisimpleRing_iff_isArtinianRing.mpr, all_goals, and_comm, isFullyInvariant_iff_isTwoSided, isIsotypic_iff_isFullyInvariant_imp_bot_or_top, isSemisimpleRing_iff_isArtinianRing, isSimpleRing_iff_isTwoSided_imp, on_goal, simp_rw
-/
theorem isSimpleRing_isArtinianRing_iff :
    IsSimpleRing R ∧ IsArtinianRing R ↔ IsSemisimpleRing R ∧ IsIsotypic R R ∧ Nontrivial R := by
  refine ⟨fun ⟨_, _⟩ => ?_, fun ⟨_, _, _⟩ => ?_⟩
  on_goal 1 => have := IsSimpleRing.isSemisimpleRing_iff_isArtinianRing.mpr ‹_›
  all_goals simp_rw [isIsotypic_iff_isFullyInvariant_imp_bot_or_top,
      isFullyInvariant_iff_isTwoSided, isSimpleRing_iff_isTwoSided_imp] at *
  · exact ⟨this, by rwa [and_comm]⟩
  · exact ⟨⟨‹_›, ‹_›⟩, inferInstance⟩

namespace IsSimpleRing

variable (R) [IsSimpleRing R] [IsArtinianRing R]

instance (priority := low) : IsSemisimpleRing R :=
  (isSimpleRing_isArtinianRing_iff.mp ⟨‹_›, ‹_›⟩).1

/--
theorem `isIsotypic` / 定理 `isIsotypic`

English:
theorem isIsotypic
  given: (M) [AddCommGroup M] [Module R M]
  statement: IsIsotypic R M
  proof: (isSimpleRing_isArtinianRing_iff.mp ⟨‹_›, ‹_›⟩).2.1.of_self M

中文:
定理 isIsotypic
  条件: (M) [加法交换群 M] [模 R M]
  结论: IsIsotypic R M
  证明: (isSimpleRing_isArtinianRing_iff.mp ⟨‹_›, ‹_›⟩).2.1.of_self M

Depends on / 依赖: isSimpleRing_isArtinianRing_iff, isSimpleRing_isArtinianRing_iff.mp, of_self
-/
theorem isIsotypic (M) [AddCommGroup M] [Module R M] : IsIsotypic R M :=
  (isSimpleRing_isArtinianRing_iff.mp ⟨‹_›, ‹_›⟩).2.1.of_self M

/--
theorem `exists_ringEquiv_matrix_end_mulOpposite` / 定理 `exists_ringEquiv_matrix_end_mulOpposite`

English:
theorem exists_ringEquiv_matrix_end_mulOpposite
  proof: by
  have ⟨n, hn, S, hS, ⟨e⟩⟩ := (isIsotypic R R).linearEquiv_fun
refine ⟨n, hn, S, hS, ⟨.trans (.opOp R) .trans (.op ?_) (.symm .mopMatrix)⟩⟩
exact .trans (.moduleEndSelf R) .trans e.conjRingEquiv (endVecRingEquivMatrixEnd ..)

中文:
定理 存在_ringEquiv_matrix_end_mulOpposite
  证明: by
  have ⟨n, hn, S, hS, ⟨e⟩⟩ := (isIsotypic R R).linearEquiv_fun
refine ⟨n, hn, S, hS, ⟨.trans (.opOp R) .trans (.op ?_) (.symm .mopMatrix)⟩⟩
exact .trans (.moduleEndSelf R) .trans e.conjRingEquiv (endVecRingEquivMatrixEnd ..)

Depends on / 依赖: conjRingEquiv, e.conjRingEquiv, endVecRingEquivMatrixEnd, isIsotypic, linearEquiv_fun, moduleEndSelf, mopMatrix
-/
theorem exists_ringEquiv_matrix_end_mulOpposite :
    exists (n : Nat) (_ : NeZero n) (I : Ideal R) (_ : IsSimpleModule R I),
      Nonempty (R ≃+* Matrix (Fin n) (Fin n) (Module.End R I)ᵐᵒᵖ) := by
  have ⟨n, hn, S, hS, ⟨e⟩⟩ := (isIsotypic R R).linearEquiv_fun
refine ⟨n, hn, S, hS, ⟨.trans (.opOp R) .trans (.op ?_) (.symm .mopMatrix)⟩⟩
exact .trans (.moduleEndSelf R) .trans e.conjRingEquiv (endVecRingEquivMatrixEnd ..)

/--
theorem `exists_ringEquiv_matrix_divisionRing` / 定理 `exists_ringEquiv_matrix_divisionRing`

English:
theorem exists_ringEquiv_matrix_divisionRing
  proof: by
  have ⟨n, hn, I, _, ⟨e⟩⟩ := exists_ringEquiv_matrix_end_mulOpposite R
  classical exact ⟨n, hn, _, _, ⟨e⟩⟩

中文:
定理 存在_ringEquiv_matrix_divisionRing
  证明: by
  have ⟨n, hn, I, _, ⟨e⟩⟩ := exists_ringEquiv_matrix_end_mulOpposite R
  classical exact ⟨n, hn, _, _, ⟨e⟩⟩

Depends on / 依赖: classical, exists_ringEquiv_matrix_end_mulOpposite
-/
theorem exists_ringEquiv_matrix_divisionRing :
    exists (n : Nat) (_ : NeZero n) (D : Type u) (_ : DivisionRing D),
      Nonempty (R ≃+* Matrix (Fin n) (Fin n) D) := by
  have ⟨n, hn, I, _, ⟨e⟩⟩ := exists_ringEquiv_matrix_end_mulOpposite R
  classical exact ⟨n, hn, _, _, ⟨e⟩⟩

/--
theorem `exists_algEquiv_matrix_end_mulOpposite` / 定理 `exists_algEquiv_matrix_end_mulOpposite`

English:
theorem exists_algEquiv_matrix_end_mulOpposite
  proof: by
  have ⟨n, hn, S, hS, ⟨e⟩⟩ := (isIsotypic R R).linearEquiv_fun
refine ⟨n, hn, S, hS, ⟨.trans (.opOp R₀ R) .trans (.op ?_) (.symm .mopMatrix)⟩⟩
exact .trans (.moduleEndSelf R₀) .trans (e.conjAlgEquiv R₀) (endVecAlgEquivMatrixEnd ..)

中文:
定理 存在_algEquiv_matrix_end_mulOpposite
  证明: by
  have ⟨n, hn, S, hS, ⟨e⟩⟩ := (isIsotypic R R).linearEquiv_fun
refine ⟨n, hn, S, hS, ⟨.trans (.opOp R₀ R) .trans (.op ?_) (.symm .mopMatrix)⟩⟩
exact .trans (.moduleEndSelf R₀) .trans (e.conjAlgEquiv R₀) (endVecAlgEquivMatrixEnd ..)

Depends on / 依赖: conjAlgEquiv, e.conjAlgEquiv, endVecAlgEquivMatrixEnd, isIsotypic, linearEquiv_fun, moduleEndSelf, mopMatrix
-/
theorem exists_algEquiv_matrix_end_mulOpposite :
    exists (n : Nat) (_ : NeZero n) (I : Ideal R) (_ : IsSimpleModule R I),
      Nonempty (R ≃ₐ[R₀] Matrix (Fin n) (Fin n) (Module.End R I)ᵐᵒᵖ) := by
  have ⟨n, hn, S, hS, ⟨e⟩⟩ := (isIsotypic R R).linearEquiv_fun
refine ⟨n, hn, S, hS, ⟨.trans (.opOp R₀ R) .trans (.op ?_) (.symm .mopMatrix)⟩⟩
exact .trans (.moduleEndSelf R₀) .trans (e.conjAlgEquiv R₀) (endVecAlgEquivMatrixEnd ..)

/--
theorem `exists_algEquiv_matrix_divisionRing` / 定理 `exists_algEquiv_matrix_divisionRing`

English:
theorem exists_algEquiv_matrix_divisionRing
  proof: by
  have ⟨n, hn, I, _, ⟨e⟩⟩ := exists_algEquiv_matrix_end_mulOpposite R₀ R
  classical exact ⟨n, hn, _, _, _, ⟨e⟩⟩

中文:
定理 存在_algEquiv_matrix_divisionRing
  证明: by
  have ⟨n, hn, I, _, ⟨e⟩⟩ := exists_algEquiv_matrix_end_mulOpposite R₀ R
  classical exact ⟨n, hn, _, _, _, ⟨e⟩⟩

Depends on / 依赖: classical, exists_algEquiv_matrix_end_mulOpposite
-/
theorem exists_algEquiv_matrix_divisionRing :
    exists (n : Nat) (_ : NeZero n) (D : Type u) (_ : DivisionRing D) (_ : Algebra R₀ D),
      Nonempty (R ≃ₐ[R₀] Matrix (Fin n) (Fin n) D) := by
  have ⟨n, hn, I, _, ⟨e⟩⟩ := exists_algEquiv_matrix_end_mulOpposite R₀ R
  classical exact ⟨n, hn, _, _, _, ⟨e⟩⟩

/--
theorem `exists_algEquiv_matrix_divisionRing_finite` / 定理 `exists_algEquiv_matrix_divisionRing_finite`

English:
theorem exists_algEquiv_matrix_divisionRing_finite
  given: [Module.Finite R₀ R]
  proof: by
  have ⟨n, hn, I, _, ⟨e⟩⟩ := exists_algEquiv_matrix_end_mulOpposite R₀ R
  have := Module.Finite.equiv e.toLinearEquiv
  classical exact ⟨n, hn, _, _, _, .of_surjective
    (Matrix.entryLinearMap R₀ _ (0 : Fin n) (0 : Fin n)) fun f => ⟨fun _ _ => f, rfl⟩, ⟨e⟩⟩

中文:
定理 存在_algEquiv_matrix_divisionRing_finite
  条件: [模.有限 R₀ R]
  证明: by
  have ⟨n, hn, I, _, ⟨e⟩⟩ := exists_algEquiv_matrix_end_mulOpposite R₀ R
  have := Module.Finite.equiv e.toLinearEquiv
  classical exact ⟨n, hn, _, _, _, .of_surjective
    (Matrix.entryLinearMap R₀ _ (0 : Fin n) (0 : Fin n)) fun f => ⟨fun _ _ => f, rfl⟩, ⟨e⟩⟩

Depends on / 依赖: Finite, LindelofSpace, Matrix, Matrix.entryLinearMap, Module, Module.Finite.equiv, Subsingleton, Subsingleton.lindelofSpace, classical, e.toLinearEquiv, entryLinearMap, exists_algEquiv_matrix_end_mulOpposite, lindelofSpace, of_surjective, toLinearEquiv
-/
theorem exists_algEquiv_matrix_divisionRing_finite [Module.Finite R₀ R] :
    exists (n : Nat) (_ : NeZero n) (D : Type u) (_ : DivisionRing D) (_ : Algebra R₀ D)
      (_ : Module.Finite R₀ D), Nonempty (R ≃ₐ[R₀] Matrix (Fin n) (Fin n) D) := by
  have ⟨n, hn, I, _, ⟨e⟩⟩ := exists_algEquiv_matrix_end_mulOpposite R₀ R
  have := Module.Finite.equiv e.toLinearEquiv
  classical exact ⟨n, hn, _, _, _, .of_surjective
    (Matrix.entryLinearMap R₀ _ (0 : Fin n) (0 : Fin n)) fun f => ⟨fun _ _ => f, rfl⟩, ⟨e⟩⟩

end IsSimpleRing

namespace IsSemisimpleModule

open Module (End)

universe v
variable (R) (M : Type v) [AddCommGroup M] [Module R₀ M] [Module R M] [IsScalarTower R₀ R M]
  [IsSemisimpleModule R M] [Module.Finite R M]

/--
theorem `exists_end_algEquiv_pi_matrix_end` / 定理 `exists_end_algEquiv_pi_matrix_end`

English:
theorem exists_end_algEquiv_pi_matrix_end
  proof: by
  choose d pos S _ simple e using fun c : isotypicComponents R M =>
    (IsIsotypic.isotypicComponents c.2).submodule_linearEquiv_fun
exact ⟨_, _, _, fun _ => simple _, fun _ => pos _, ⟨.trans (endAlgEquiv R₀ R M) .trans
(.piCongrRight fun c => ((e c).some.conjAlgEquiv R₀).trans (endVecAlgEquivMa

中文:
定理 存在_end_algEquiv_pi_matrix_end
  证明: by
  choose d pos S _ simple e using fun c : isotypicComponents R M =>
    (IsIsotypic.isotypicComponents c.2).submodule_linearEquiv_fun
exact ⟨_, _, _, fun _ => simple _, fun _ => pos _, ⟨.trans (endAlgEquiv R₀ R M) .trans
(.piCongrRight fun c => ((e c).some.conjAlgEquiv R₀).trans (endVecAlgEquivMa

Depends on / 依赖: Finite, Finite.equivFin, IsIsotypic, IsIsotypic.isotypicComponents, conjAlgEquiv, endAlgEquiv, endVecAlgEquivMatrixEnd, equivFin, isotypicComponents, piCongrLeft, piCongrRight, simple, some.conjAlgEquiv, submodule_linearEquiv_fun
-/
theorem exists_end_algEquiv_pi_matrix_end :
    exists (n : Nat) (S : Fin n -> Submodule R M) (d : Fin n -> Nat),
      (forall i, IsSimpleModule R (S i)) ∧ (forall i, NeZero (d i)) ∧
      Nonempty (End R M ≃ₐ[R₀] Π i, Matrix (Fin (d i)) (Fin (d i)) (End R (S i))) := by
  choose d pos S _ simple e using fun c : isotypicComponents R M =>
    (IsIsotypic.isotypicComponents c.2).submodule_linearEquiv_fun
exact ⟨_, _, _, fun _ => simple _, fun _ => pos _, ⟨.trans (endAlgEquiv R₀ R M) .trans
(.piCongrRight fun c => ((e c).some.conjAlgEquiv R₀).trans (endVecAlgEquivMatrixEnd ..))
    (.piCongrLeft' R₀ _ (Finite.equivFin _))⟩⟩

/--
theorem `exists_end_ringEquiv_pi_matrix_end` / 定理 `exists_end_ringEquiv_pi_matrix_end`

English:
theorem exists_end_ringEquiv_pi_matrix_end
  proof: have ⟨n, S, d, hS, hd, ⟨e⟩⟩ := exists_end_algEquiv_pi_matrix_end Nat R M; ⟨n, S, d, hS, hd, ⟨e⟩⟩

中文:
定理 存在_end_ringEquiv_pi_matrix_end
  证明: have ⟨n, S, d, hS, hd, ⟨e⟩⟩ := exists_end_algEquiv_pi_matrix_end Nat R M; ⟨n, S, d, hS, hd, ⟨e⟩⟩

Depends on / 依赖: exists_end_algEquiv_pi_matrix_end
-/
theorem exists_end_ringEquiv_pi_matrix_end :
    exists (n : Nat) (S : Fin n -> Submodule R M) (d : Fin n -> Nat),
      (forall i, IsSimpleModule R (S i)) ∧ (forall i, NeZero (d i)) ∧
      Nonempty (End R M ≃+* Π i, Matrix (Fin (d i)) (Fin (d i)) (End R (S i))) :=
  have ⟨n, S, d, hS, hd, ⟨e⟩⟩ := exists_end_algEquiv_pi_matrix_end Nat R M; ⟨n, S, d, hS, hd, ⟨e⟩⟩

-- TODO: can also require D be in `Type u`, since every simple module is the quotient by an ideal.
/--
theorem `exists_end_algEquiv_pi_matrix_divisionRing` / 定理 `exists_end_algEquiv_pi_matrix_divisionRing`

English:
theorem exists_end_algEquiv_pi_matrix_divisionRing
  proof: by
  have ⟨n, S, d, _, hd, ⟨e⟩⟩ := exists_end_algEquiv_pi_matrix_end R₀ R M
  classical exact ⟨n, _, d, inferInstance, inferInstance, hd, ⟨e⟩⟩

中文:
定理 存在_end_algEquiv_pi_matrix_divisionRing
  证明: by
  have ⟨n, S, d, _, hd, ⟨e⟩⟩ := exists_end_algEquiv_pi_matrix_end R₀ R M
  classical exact ⟨n, _, d, inferInstance, inferInstance, hd, ⟨e⟩⟩

Depends on / 依赖: classical, exists_end_algEquiv_pi_matrix_end
-/
theorem exists_end_algEquiv_pi_matrix_divisionRing :
    exists (n : Nat) (D : Fin n -> Type v) (d : Fin n -> Nat) (_ : forall i, DivisionRing (D i))
      (_ : forall i, Algebra R₀ (D i)), (forall i, NeZero (d i)) ∧
      Nonempty (End R M ≃ₐ[R₀] Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) := by
  have ⟨n, S, d, _, hd, ⟨e⟩⟩ := exists_end_algEquiv_pi_matrix_end R₀ R M
  classical exact ⟨n, _, d, inferInstance, inferInstance, hd, ⟨e⟩⟩

/--
theorem `exists_end_ringEquiv_pi_matrix_divisionRing` / 定理 `exists_end_ringEquiv_pi_matrix_divisionRing`

English:
theorem exists_end_ringEquiv_pi_matrix_divisionRing
  proof: have ⟨n, D, d, _, _, hd, ⟨e⟩⟩ := exists_end_algEquiv_pi_matrix_divisionRing Nat R M
  ⟨n, D, d, _, hd, ⟨e⟩⟩

中文:
定理 存在_end_ringEquiv_pi_matrix_divisionRing
  证明: have ⟨n, D, d, _, _, hd, ⟨e⟩⟩ := exists_end_algEquiv_pi_matrix_divisionRing Nat R M
  ⟨n, D, d, _, hd, ⟨e⟩⟩

Depends on / 依赖: exists_end_algEquiv_pi_matrix_divisionRing
-/
theorem exists_end_ringEquiv_pi_matrix_divisionRing :
    exists (n : Nat) (D : Fin n -> Type v) (d : Fin n -> Nat) (_ : forall i, DivisionRing (D i)),
      (forall i, NeZero (d i)) ∧ Nonempty (End R M ≃+* Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) :=
  have ⟨n, D, d, _, _, hd, ⟨e⟩⟩ := exists_end_algEquiv_pi_matrix_divisionRing Nat R M
  ⟨n, D, d, _, hd, ⟨e⟩⟩

/--
theorem `_root_.IsSemisimpleRing.moduleEnd` / 定理 `_root_.IsSemisimpleRing.moduleEnd`

English:
theorem _root_.IsSemisimpleRing.moduleEnd
  statement: IsSemisimpleRing (Module.End R M)
  proof: have ⟨_, _, _, _, _, ⟨e⟩⟩ := exists_end_ringEquiv_pi_matrix_divisionRing R M
  e.symm.isSemisimpleRing

中文:
定理 _root_.IsSemisimpleRing.moduleEnd
  结论: IsSemisimpleRing (模.End R M)
  证明: have ⟨_, _, _, _, _, ⟨e⟩⟩ := exists_end_ringEquiv_pi_matrix_divisionRing R M
  e.symm.isSemisimpleRing

Depends on / 依赖: e.symm.isSemisimpleRing, exists_end_ringEquiv_pi_matrix_divisionRing, isSemisimpleRing
-/
theorem _root_.IsSemisimpleRing.moduleEnd : IsSemisimpleRing (Module.End R M) :=
  have ⟨_, _, _, _, _, ⟨e⟩⟩ := exists_end_ringEquiv_pi_matrix_divisionRing R M
  e.symm.isSemisimpleRing

end IsSemisimpleModule

namespace IsSemisimpleRing

variable (R) [IsSemisimpleRing R]

/--
theorem `exists_algEquiv_pi_matrix_end_mulOpposite` / 定理 `exists_algEquiv_pi_matrix_end_mulOpposite`

English:
theorem exists_algEquiv_pi_matrix_end_mulOpposite
  proof: have ⟨n, S, d, hS, hd, ⟨e⟩⟩ := IsSemisimpleModule.exists_end_algEquiv_pi_matrix_end R₀ R R
⟨n, S, d, hS, hd, ⟨.trans (.opOp R₀ R) .trans (.op <| .trans (.moduleEndSelf R₀) e)
    .trans (.piMulOpposite _ _) (.piCongrRight fun _ => .symm .mopMatrix)⟩⟩

中文:
定理 存在_algEquiv_pi_matrix_end_mulOpposite
  证明: have ⟨n, S, d, hS, hd, ⟨e⟩⟩ := IsSemisimpleModule.exists_end_algEquiv_pi_matrix_end R₀ R R
⟨n, S, d, hS, hd, ⟨.trans (.opOp R₀ R) .trans (.op <| .trans (.moduleEndSelf R₀) e)
    .trans (.piMulOpposite _ _) (.piCongrRight fun _ => .symm .mopMatrix)⟩⟩

Depends on / 依赖: IsSemisimpleModule, IsSemisimpleModule.exists_end_algEquiv_pi_matrix_end, exists_end_algEquiv_pi_matrix_end, moduleEndSelf, mopMatrix, piCongrRight, piMulOpposite
-/
theorem exists_algEquiv_pi_matrix_end_mulOpposite :
    exists (n : Nat) (S : Fin n -> Ideal R) (d : Fin n -> Nat),
      (forall i, IsSimpleModule R (S i)) ∧ (forall i, NeZero (d i)) ∧
      Nonempty (R ≃ₐ[R₀] Π i, Matrix (Fin (d i)) (Fin (d i)) (Module.End R (S i))ᵐᵒᵖ) :=
  have ⟨n, S, d, hS, hd, ⟨e⟩⟩ := IsSemisimpleModule.exists_end_algEquiv_pi_matrix_end R₀ R R
⟨n, S, d, hS, hd, ⟨.trans (.opOp R₀ R) .trans (.op <| .trans (.moduleEndSelf R₀) e)
    .trans (.piMulOpposite _ _) (.piCongrRight fun _ => .symm .mopMatrix)⟩⟩

/--
theorem `exists_algEquiv_pi_matrix_divisionRing` / 定理 `exists_algEquiv_pi_matrix_divisionRing`

English:
theorem exists_algEquiv_pi_matrix_divisionRing
  proof: by
  have ⟨n, S, d, _, hd, ⟨e⟩⟩ := exists_algEquiv_pi_matrix_end_mulOpposite R₀ R
  classical exact ⟨n, _, d, inferInstance, inferInstance, hd, ⟨e⟩⟩

中文:
定理 存在_algEquiv_pi_matrix_divisionRing
  证明: by
  have ⟨n, S, d, _, hd, ⟨e⟩⟩ := exists_algEquiv_pi_matrix_end_mulOpposite R₀ R
  classical exact ⟨n, _, d, inferInstance, inferInstance, hd, ⟨e⟩⟩

Depends on / 依赖: classical, exists_algEquiv_pi_matrix_end_mulOpposite
-/
theorem exists_algEquiv_pi_matrix_divisionRing :
    exists (n : Nat) (D : Fin n -> Type u) (d : Fin n -> Nat) (_ : forall i, DivisionRing (D i))
      (_ : forall i, Algebra R₀ (D i)), (forall i, NeZero (d i)) ∧
      Nonempty (R ≃ₐ[R₀] Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) := by
  have ⟨n, S, d, _, hd, ⟨e⟩⟩ := exists_algEquiv_pi_matrix_end_mulOpposite R₀ R
  classical exact ⟨n, _, d, inferInstance, inferInstance, hd, ⟨e⟩⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `exists_algEquiv_pi_matrix_divisionRing_finite` / 定理 `exists_algEquiv_pi_matrix_divisionRing_finite`

English:
theorem exists_algEquiv_pi_matrix_divisionRing_finite
  given: [Module.Finite R₀ R]
  proof: by
  have ⟨n, D, d, _, _, hd, ⟨e⟩⟩ := exists_algEquiv_pi_matrix_divisionRing R₀ R
  have := Module.Finite.equiv e.toLinearEquiv
  refine ⟨n, D, d, _, _, fun i => ?_, hd, ⟨e⟩⟩
  let l := Matrix.entryLinearMap R₀ (D i) 0 0 ∘ₗ
    .proj (φ := fun i => Matrix (Fin (d i)) (Fin (d i)) _) i
  exact .of_sur

中文:
定理 存在_algEquiv_pi_matrix_divisionRing_finite
  条件: [模.有限 R₀ R]
  证明: by
  have ⟨n, D, d, _, _, hd, ⟨e⟩⟩ := exists_algEquiv_pi_matrix_divisionRing R₀ R
  have := Module.Finite.equiv e.toLinearEquiv
  refine ⟨n, D, d, _, _, fun i => ?_, hd, ⟨e⟩⟩
  let l := Matrix.entryLinearMap R₀ (D i) 0 0 ∘ₗ
    .proj (φ := fun i => Matrix (Fin (d i)) (Fin (d i)) _) i
  exact .of_sur

Depends on / 依赖: Finite, Function, Function.update, Matrix, Matrix.entryLinearMap, Module, Module.Finite.equiv, e.toLinearEquiv, entryLinearMap, exists_algEquiv_pi_matrix_divisionRing, of_surjective, toLinearEquiv, update
-/
theorem exists_algEquiv_pi_matrix_divisionRing_finite [Module.Finite R₀ R] :
    exists (n : Nat) (D : Fin n -> Type u) (d : Fin n -> Nat) (_ : forall i, DivisionRing (D i))
      (_ : forall i, Algebra R₀ (D i)) (_ : forall i, Module.Finite R₀ (D i)), (forall i, NeZero (d i)) ∧
      Nonempty (R ≃ₐ[R₀] Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) := by
  have ⟨n, D, d, _, _, hd, ⟨e⟩⟩ := exists_algEquiv_pi_matrix_divisionRing R₀ R
  have := Module.Finite.equiv e.toLinearEquiv
  refine ⟨n, D, d, _, _, fun i => ?_, hd, ⟨e⟩⟩
  let l := Matrix.entryLinearMap R₀ (D i) 0 0 ∘ₗ
    .proj (φ := fun i => Matrix (Fin (d i)) (Fin (d i)) _) i
  exact .of_surjective l fun x => ⟨fun j _ _ => Function.update (fun _ => 0) i x j, by simp [l]⟩

/--
theorem `exists_ringEquiv_pi_matrix_end_mulOpposite` / 定理 `exists_ringEquiv_pi_matrix_end_mulOpposite`

English:
theorem exists_ringEquiv_pi_matrix_end_mulOpposite
  proof: have ⟨n, S, d, hS, hd, ⟨e⟩⟩ := exists_algEquiv_pi_matrix_end_mulOpposite Nat R
  ⟨n, S, d, hS, hd, ⟨e⟩⟩

中文:
定理 存在_ringEquiv_pi_matrix_end_mulOpposite
  证明: have ⟨n, S, d, hS, hd, ⟨e⟩⟩ := exists_algEquiv_pi_matrix_end_mulOpposite Nat R
  ⟨n, S, d, hS, hd, ⟨e⟩⟩

Depends on / 依赖: CompactSpace, LindelofSpace, exists_algEquiv_pi_matrix_end_mulOpposite
-/
theorem exists_ringEquiv_pi_matrix_end_mulOpposite :
    exists (n : Nat) (D : Fin n -> Ideal R) (d : Fin n -> Nat),
      (forall i, IsSimpleModule R (D i)) ∧ (forall i, NeZero (d i)) ∧
      Nonempty (R ≃+* Π i, Matrix (Fin (d i)) (Fin (d i)) (Module.End R (D i))ᵐᵒᵖ) :=
  have ⟨n, S, d, hS, hd, ⟨e⟩⟩ := exists_algEquiv_pi_matrix_end_mulOpposite Nat R
  ⟨n, S, d, hS, hd, ⟨e⟩⟩

/--
theorem `exists_ringEquiv_pi_matrix_divisionRing` / 定理 `exists_ringEquiv_pi_matrix_divisionRing`

English:
theorem exists_ringEquiv_pi_matrix_divisionRing
  proof: have ⟨n, D, d, _, _, hd, ⟨e⟩⟩ := exists_algEquiv_pi_matrix_divisionRing Nat R
  ⟨n, D, d, _, hd, ⟨e⟩⟩

中文:
定理 存在_ringEquiv_pi_matrix_divisionRing
  证明: have ⟨n, D, d, _, _, hd, ⟨e⟩⟩ := exists_algEquiv_pi_matrix_divisionRing Nat R
  ⟨n, D, d, _, hd, ⟨e⟩⟩

Depends on / 依赖: LindelofSpace, SigmaCompactSpace, exists_algEquiv_pi_matrix_divisionRing
-/
theorem exists_ringEquiv_pi_matrix_divisionRing :
    exists (n : Nat) (D : Fin n -> Type u) (d : Fin n -> Nat) (_ : forall i, DivisionRing (D i)),
      (forall i, NeZero (d i)) ∧ Nonempty (R ≃+* Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) :=
  have ⟨n, D, d, _, _, hd, ⟨e⟩⟩ := exists_algEquiv_pi_matrix_divisionRing Nat R
  ⟨n, D, d, _, hd, ⟨e⟩⟩

instance (n) [Fintype n] [DecidableEq n] : IsSemisimpleRing (Matrix n n R) :=
  (isEmpty_or_nonempty n).elim (fun _ => inferInstance) fun _ =>
    have ⟨_, _, _, _, _, ⟨e⟩⟩ := exists_ringEquiv_pi_matrix_divisionRing R
    (e.mapMatrix (m := n).trans Matrix.piRingEquiv).symm.isSemisimpleRing

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSemisimpleRing Rᵐᵒᵖ
  body: have ⟨_, _, _, _, _, ⟨e⟩⟩ := exists_ringEquiv_pi_matrix_divisionRing R
  ((e.op.trans (.piMulOpposite _)).trans (.piCongrRight fun _ => .symm .mopMatrix)).symm
.isSemisimpleRing

中文:
实例 :
  签名: IsSemisimpleRing Rᵐᵒᵖ
  定义体: have ⟨_, _, _, _, _, ⟨e⟩⟩ := exists_ringEquiv_pi_matrix_divisionRing R
  ((e.op.trans (.piMulOpposite _)).trans (.piCongrRight fun _ => .symm .mopMatrix)).symm
.isSemisimpleRing

Depends on / 依赖: e.op.trans, exists_ringEquiv_pi_matrix_divisionRing, isSemisimpleRing, mopMatrix, piCongrRight, piMulOpposite
-/
instance : IsSemisimpleRing Rᵐᵒᵖ :=
  have ⟨_, _, _, _, _, ⟨e⟩⟩ := exists_ringEquiv_pi_matrix_divisionRing R
  ((e.op.trans (.piMulOpposite _)).trans (.piCongrRight fun _ => .symm .mopMatrix)).symm
.isSemisimpleRing

end IsSemisimpleRing

/--
theorem `isSemisimpleRing_mulOpposite_iff` / 定理 `isSemisimpleRing_mulOpposite_iff`

English:
theorem isSemisimpleRing_mulOpposite_iff
  statement: IsSemisimpleRing Rᵐᵒᵖ ↔ IsSemisimpleRing R
  proof: ⟨fun _ => (RingEquiv.opOp R).symm.isSemisimpleRing, fun _ => inferInstance⟩

中文:
定理 isSemisimpleRing_mulOpposite_iff
  结论: IsSemisimpleRing Rᵐᵒᵖ ↔ IsSemisimpleRing R
  证明: ⟨fun _ => (RingEquiv.opOp R).symm.isSemisimpleRing, fun _ => inferInstance⟩

Depends on / 依赖: RingEquiv, RingEquiv.opOp, isSemisimpleRing, symm.isSemisimpleRing
-/
theorem isSemisimpleRing_mulOpposite_iff : IsSemisimpleRing Rᵐᵒᵖ ↔ IsSemisimpleRing R :=
  ⟨fun _ => (RingEquiv.opOp R).symm.isSemisimpleRing, fun _ => inferInstance⟩

/--
theorem `isSemisimpleRing_iff_pi_matrix_divisionRing` / 定理 `isSemisimpleRing_iff_pi_matrix_divisionRing`

English:
theorem isSemisimpleRing_iff_pi_matrix_divisionRing
  statement: IsSemisimpleRing R ↔
  proof: have ⟨n, D, d, _, _, e⟩ := IsSemisimpleRing.exists_ringEquiv_pi_matrix_divisionRing R
    ⟨n, D, d, _, e⟩
  mpr := fun ⟨_, _, _, _, ⟨e⟩⟩ => e.symm.isSemisimpleRing

中文:
定理 isSemisimpleRing_iff_pi_matrix_divisionRing
  结论: IsSemisimpleRing R ↔
  证明: have ⟨n, D, d, _, _, e⟩ := IsSemisimpleRing.exists_ringEquiv_pi_matrix_divisionRing R
    ⟨n, D, d, _, e⟩
  mpr := fun ⟨_, _, _, _, ⟨e⟩⟩ => e.symm.isSemisimpleRing

Depends on / 依赖: IsSemisimpleRing, IsSemisimpleRing.exists_ringEquiv_pi_matrix_divisionRing, exists_ringEquiv_pi_matrix_divisionRing
-/
theorem isSemisimpleRing_iff_pi_matrix_divisionRing : IsSemisimpleRing R ↔
    exists (n : Nat) (D : Fin n -> Type u) (d : Fin n -> Nat) (_ : Π i, DivisionRing (D i)),
      Nonempty (R ≃+* Π i, Matrix (Fin (d i)) (Fin (d i)) (D i)) where
  mp _ := have ⟨n, D, d, _, _, e⟩ := IsSemisimpleRing.exists_ringEquiv_pi_matrix_divisionRing R
    ⟨n, D, d, _, e⟩
  mpr := fun ⟨_, _, _, _, ⟨e⟩⟩ => e.symm.isSemisimpleRing

-- Need left-right symmetry of Jacobson radical
proof_wanted IsSemiprimaryRing.mulOpposite [IsSemiprimaryRing R] : IsSemiprimaryRing Rᵐᵒᵖ

proof_wanted isSemiprimaryRing_mulOpposite_iff : IsSemiprimaryRing Rᵐᵒᵖ ↔ IsSemiprimaryRing R

-- A left Artinian ring is right Noetherian iff it is right Artinian. To be left as an `example`.
proof_wanted IsArtinianRing.isNoetherianRing_iff_isArtinianRing_mulOpposite
    [IsArtinianRing R] : IsNoetherianRing Rᵐᵒᵖ ↔ IsArtinianRing Rᵐᵒᵖ
