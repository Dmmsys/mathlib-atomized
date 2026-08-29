/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Bialgebra structure on `SymmetricAlgebra R M`

`SymmetricAlgebra R M` is the cocommutative commutative `R`-bialgebra on `M`
in which each generator `ι x` is primitive: `Δ(ι x) = ι x ⊗ 1 + 1 ⊗ ι x` and
`ε(ι x) = 0`.
-/

public noncomputable section

namespace SymmetricAlgebra

variable (R : Type*) [CommSemiring R] (M : Type*) [AddCommMonoid M] [Module R M]

open scoped TensorProduct

/--
Instance `instBialgebra` / 实例 `instBialgebra`

English:
instance instBialgebra
  signature: : Bialgebra R (SymmetricAlgebra R M)
  body: .ofAlgHom
    (lift <| (TensorProduct.mk R _ _).flip 1 ∘ₗ ι R M + TensorProduct.mk R _ _ 1 ∘ₗ ι R M)
    algebraMapInv
    (by
      ext x
      simp [Algebra.TensorProduct.one_def, TensorProduct.add_tmul, TensorProduct.tmul_add]
      abel)
    (by ext x; simp [algebraMapInv_ι])
    (by ext x; simp

中文:
实例 instBialgebra
  签名: : 双代数 R (SymmetricAlgebra R M)
  定义体: .ofAlgHom
    (lift <| (TensorProduct.mk R _ _).flip 1 ∘ₗ ι R M + TensorProduct.mk R _ _ 1 ∘ₗ ι R M)
    algebraMapInv
    (by
      ext x
      simp [Algebra.TensorProduct.one_def, TensorProduct.add_tmul, TensorProduct.tmul_add]
      abel)
    (by ext x; simp [algebraMapInv_ι])
    (by ext x; simp

Depends on / 依赖: Algebra, Algebra.TensorProduct.one_def, TensorProduct, TensorProduct.add_tmul, TensorProduct.mk, TensorProduct.tmul_add, add_tmul, algebraMapInv, ofAlgHom, one_def, tmul_add
-/
instance instBialgebra : Bialgebra R (SymmetricAlgebra R M) :=
  .ofAlgHom
    (lift <| (TensorProduct.mk R _ _).flip 1 ∘ₗ ι R M + TensorProduct.mk R _ _ 1 ∘ₗ ι R M)
    algebraMapInv
    (by
      ext x
      simp [Algebra.TensorProduct.one_def, TensorProduct.add_tmul, TensorProduct.tmul_add]
      abel)
    (by ext x; simp [algebraMapInv_ι])
    (by ext x; simp [algebraMapInv_ι])

@[simp]
/--
theorem `comul_ι` / 定理 `comul_ι`

English:
theorem comul_ι
  given: (x : M)
  proof: lift_ι_apply _ x

@[simp]

中文:
定理 comul_ι
  条件: (x : M)
  证明: lift_ι_apply _ x

@[simp]
-/
theorem comul_ι (x : M) :
    Coalgebra.comul (R := R) (ι R M x) = ι R M x otimesₜ[R] 1 + 1 otimesₜ[R] ι R M x :=
  lift_ι_apply _ x

@[simp]
/--
theorem `counit_ι` / 定理 `counit_ι`

English:
theorem counit_ι
  given: (x : M)
  proof: algebraMapInv_ι x

中文:
定理 counit_ι
  条件: (x : M)
  证明: algebraMapInv_ι x
-/
theorem counit_ι (x : M) :
    Coalgebra.counit (R := R) (ι R M x) = 0 :=
  algebraMapInv_ι x

/--
Instance `instIsCocomm` / 实例 `instIsCocomm`

English:
instance instIsCocomm
  signature: : Coalgebra.IsCocomm R (SymmetricAlgebra R M) where
  body: by
    have h : (Algebra.TensorProduct.comm R (SymmetricAlgebra R M)
          (SymmetricAlgebra R M)).toAlgHom.comp (Bialgebra.comulAlgHom R _) =
        Bialgebra.comulAlgHom R (SymmetricAlgebra R M) := by
      ext x
      simp
      abel
    exact congr(($h).toLinearMap)

@[simp]

中文:
实例 instIsCocomm
  签名: : 余algebra.是余comm R (SymmetricAlgebra R M) where
  定义体: by
    have h : (Algebra.TensorProduct.comm R (SymmetricAlgebra R M)
          (SymmetricAlgebra R M)).toAlgHom.comp (Bialgebra.comulAlgHom R _) =
        Bialgebra.comulAlgHom R (SymmetricAlgebra R M) := by
      ext x
      simp
      abel
    exact congr(($h).toLinearMap)

@[simp]

Depends on / 依赖: Algebra, Algebra.TensorProduct.comm, Bialgebra, Bialgebra.comulAlgHom, SymmetricAlgebra, TensorProduct, comulAlgHom, toAlgHom, toAlgHom.comp, toLinearMap
-/
instance instIsCocomm : Coalgebra.IsCocomm R (SymmetricAlgebra R M) where
  comm_comp_comul := by
    have h : (Algebra.TensorProduct.comm R (SymmetricAlgebra R M)
          (SymmetricAlgebra R M)).toAlgHom.comp (Bialgebra.comulAlgHom R _) =
        Bialgebra.comulAlgHom R (SymmetricAlgebra R M) := by
      ext x
      simp
      abel
    exact congr(($h).toLinearMap)

@[simp]
/--
theorem `counitAlgHom_eq` / 定理 `counitAlgHom_eq`

English:
theorem counitAlgHom_eq
  proof: rfl

中文:
定理 counitAlgHom_eq
  证明: rfl
-/
theorem counitAlgHom_eq :
    Bialgebra.counitAlgHom R (SymmetricAlgebra R M) = algebraMapInv := rfl

end SymmetricAlgebra
