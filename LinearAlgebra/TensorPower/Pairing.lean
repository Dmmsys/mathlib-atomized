/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.TensorPower.Basic

/-!
# The pairing between the tensor power of the dual and the tensor power

We construct the pairing
`TensorPower.pairingDual : ⨂[R]^n (Module.Dual R M) →ₗ[R] (Module.Dual R (⨂[R]^n M))`.

-/

@[expose] public section

open TensorProduct PiTensorProduct

namespace TensorPower

variable (R : Type*) (M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M]
  (n : Nat)


/--
Definition of `multilinearMapToDual` / `multilinearMapToDual` 的定义

English:
definition multilinearMapToDual
  signature: :
  body: have : forall (_ : DecidableEq (Fin n)) (f : Fin n -> Module.Dual R M)
      (φ : Module.Dual R M) (i j : Fin n) (v : Fin n -> M),
      (Function.update f i φ) j (v j) =
      Function.update (fun j => f j (v j)) i (φ (v i)) j := fun _ f φ i j v => by
    by_cases h : j = i
    · subst h
      simp

中文:
定义 multilinearMapToDual
  签名: :
  定义体: have : forall (_ : DecidableEq (Fin n)) (f : Fin n -> Module.Dual R M)
      (φ : Module.Dual R M) (i j : Fin n) (v : Fin n -> M),
      (Function.update f i φ) j (v j) =
      Function.update (fun j => f j (v j)) i (φ (v i)) j := fun _ f φ i j v => by
    by_cases h : j = i
    · subst h
      simp

Depends on / 依赖: DecidableEq, Function, Function.update, Function.update_of_ne, Function.update_self, Module, Module.Dual, MultilinearMap, MultilinearMap.compLinearMap, MultilinearMap.mkPiRing, PiTensorProduct, PiTensorProduct.lift, compLinearMap, map_update_add, mkPiRing, update, update_of_ne, update_self
-/
noncomputable def multilinearMapToDual :
    MultilinearMap R (fun (_ : Fin n) => Module.Dual R M)
      (Module.Dual R (⨂[R]^n M)) :=
  have : forall (_ : DecidableEq (Fin n)) (f : Fin n -> Module.Dual R M)
      (φ : Module.Dual R M) (i j : Fin n) (v : Fin n -> M),
      (Function.update f i φ) j (v j) =
      Function.update (fun j => f j (v j)) i (φ (v i)) j := fun _ f φ i j v => by
    by_cases h : j = i
    · subst h
      simp only [Function.update_self]
    · simp only [Function.update_of_ne h]
  { toFun := fun f => PiTensorProduct.lift
      (MultilinearMap.compLinearMap (MultilinearMap.mkPiRing R (Fin n) 1) f)
    map_update_add' := fun f i φ₁ φ₂ => by
      ext v
      simp [this]
    map_update_smul' := fun f i a φ => by
      ext v
      simp [this, Finset.prod_update_of_mem, Semigroup.mul_assoc] }

variable {R M n} in
@[simp]
/--
theorem `multilinearMapToDual_apply_tprod` / 定理 `multilinearMapToDual_apply_tprod`

English:
theorem multilinearMapToDual_apply_tprod
  given: (f : (_ : Fin n) -> Module.Dual R M) (v : Fin n -> M)
  proof: by
  simp [multilinearMapToDual]

中文:
定理 multilinearMapToDual_apply_tprod
  条件: (f : (_ : Fin n) -> Module.Dual R M) (v : Fin n -> M)
  证明: by
  simp [multilinearMapToDual]

Depends on / 依赖: multilinearMapToDual
-/
theorem multilinearMapToDual_apply_tprod (f : (_ : Fin n) -> Module.Dual R M) (v : Fin n -> M) :
    multilinearMapToDual R M n f (tprod _ v) = ∏ i, (f i (v i)) := by
  simp [multilinearMapToDual]

/--
Definition of `pairingDual` / `pairingDual` 的定义

English:
definition pairingDual
  signature: :
  body: PiTensorProduct.lift (multilinearMapToDual R M n)

中文:
定义 pairingDual
  签名: :
  定义体: PiTensorProduct.lift (multilinearMapToDual R M n)

Depends on / 依赖: PiTensorProduct, PiTensorProduct.lift, multilinearMapToDual
-/
noncomputable def pairingDual :
    ⨂[R]^n (Module.Dual R M) ->ₗ[R] (Module.Dual R (⨂[R]^n M)) :=
  PiTensorProduct.lift (multilinearMapToDual R M n)

variable {R M n} in
@[simp]
/--
lemma `pairingDual_tprod_tprod` / 引理 `pairingDual_tprod_tprod`

English:
lemma pairingDual_tprod_tprod
  given: (f : (_ : Fin n) -> Module.Dual R M) (v : Fin n -> M)
  proof: by
  simp [pairingDual]

中文:
引理 pairingDual_tprod_tprod
  条件: (f : (_ : Fin n) -> Module.Dual R M) (v : Fin n -> M)
  证明: by
  simp [pairingDual]

Depends on / 依赖: pairingDual
-/
lemma pairingDual_tprod_tprod (f : (_ : Fin n) -> Module.Dual R M) (v : Fin n -> M) :
    pairingDual R M n (tprod _ f) (tprod _ v) = ∏ i, (f i (v i)) := by
  simp [pairingDual]

end TensorPower
