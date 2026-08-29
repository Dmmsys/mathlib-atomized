/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.SimpleModule.WedderburnArtin

/-!
# Wedderburn–Artin Theorem over an algebraically closed field
-/

public section

variable (F R : Type*) [Field F] [IsAlgClosed F] [Ring R] [Algebra F R]

/--
theorem `IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed` / 定理 `IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed`

English:
theorem IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed
  proof: have := IsArtinianRing.of_finite F R
  have ⟨n, hn, D, _, _, _, ⟨e⟩⟩ := exists_algEquiv_matrix_divisionRing_finite F R
⟨n, hn, ⟨e.trans .mapMatrix .symm .ofBijective (Algebra.ofId F D)
    IsAlgClosed.algebraMap_bijective_of_isIntegral⟩⟩

中文:
定理 IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed
  证明: have := IsArtinianRing.of_finite F R
  have ⟨n, hn, D, _, _, _, ⟨e⟩⟩ := exists_algEquiv_matrix_divisionRing_finite F R
⟨n, hn, ⟨e.trans .mapMatrix .symm .ofBijective (Algebra.ofId F D)
    IsAlgClosed.algebraMap_bijective_of_isIntegral⟩⟩

Depends on / 依赖: Algebra, Algebra.ofId, IsAlgClosed, IsAlgClosed.algebraMap_bijective_of_isIntegral, IsArtinianRing, IsArtinianRing.of_finite, algebraMap_bijective_of_isIntegral, e.trans, exists_algEquiv_matrix_divisionRing_finite, mapMatrix, ofBijective, of_finite
-/
theorem IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed
    [IsSimpleRing R] [FiniteDimensional F R] :
    exists (n : Nat) (_ : NeZero n), Nonempty (R ≃ₐ[F] Matrix (Fin n) (Fin n) F) :=
  have := IsArtinianRing.of_finite F R
  have ⟨n, hn, D, _, _, _, ⟨e⟩⟩ := exists_algEquiv_matrix_divisionRing_finite F R
⟨n, hn, ⟨e.trans .mapMatrix .symm .ofBijective (Algebra.ofId F D)
    IsAlgClosed.algebraMap_bijective_of_isIntegral⟩⟩

/--
theorem `IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed` / 定理 `IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed`

English:
theorem IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed
  proof: have ⟨n, D, d, _, _, _, hd, ⟨e⟩⟩ := exists_algEquiv_pi_matrix_divisionRing_finite F R
⟨n, d, hd, ⟨e.trans .piCongrRight fun i => .mapMatrix .symm .ofBijective
    (Algebra.ofId F (D i)) IsAlgClosed.algebraMap_bijective_of_isIntegral⟩⟩

中文:
定理 IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed
  证明: have ⟨n, D, d, _, _, _, hd, ⟨e⟩⟩ := exists_algEquiv_pi_matrix_divisionRing_finite F R
⟨n, d, hd, ⟨e.trans .piCongrRight fun i => .mapMatrix .symm .ofBijective
    (Algebra.ofId F (D i)) IsAlgClosed.algebraMap_bijective_of_isIntegral⟩⟩

Depends on / 依赖: Algebra, Algebra.ofId, IsAlgClosed, IsAlgClosed.algebraMap_bijective_of_isIntegral, algebraMap_bijective_of_isIntegral, e.trans, exists_algEquiv_pi_matrix_divisionRing_finite, mapMatrix, ofBijective, piCongrRight
-/
theorem IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed
    [IsSemisimpleRing R] [FiniteDimensional F R] :
    exists (n : Nat) (d : Fin n -> Nat), (forall i, NeZero (d i)) ∧
      Nonempty (R ≃ₐ[F] Π i, Matrix (Fin (d i)) (Fin (d i)) F) :=
  have ⟨n, D, d, _, _, _, hd, ⟨e⟩⟩ := exists_algEquiv_pi_matrix_divisionRing_finite F R
⟨n, d, hd, ⟨e.trans .piCongrRight fun i => .mapMatrix .symm .ofBijective
    (Algebra.ofId F (D i)) IsAlgClosed.algebraMap_bijective_of_isIntegral⟩⟩
