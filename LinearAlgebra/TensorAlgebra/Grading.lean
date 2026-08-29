/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.TensorAlgebra.Basic
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Results about the grading structure of the tensor algebra

The main result is `TensorAlgebra.gradedAlgebra`, which says that the tensor algebra is a
ℕ-graded algebra.
-/

@[expose] public section

namespace TensorAlgebra

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

open scoped DirectSum

variable (R M)

/-- A version of `TensorAlgebra.ι` that maps directly into the graded structure. This is
primarily an auxiliary construction used to provide `TensorAlgebra.gradedAlgebra`. -/
nonrec def GradedAlgebra.ι : M ->ₗ[R] ⨁ i : Nat, ↥(LinearMap.range (ι R : M ->ₗ[_] _) ^ i) :=
  DirectSum.lof R Nat (fun i => ↥(LinearMap.range (ι R : M ->ₗ[_] _) ^ i)) 1 ∘ₗ
    (ι R).codRestrict _ fun m => by simpa only [pow_one] using LinearMap.mem_range_self _ m

/--
theorem `GradedAlgebra.ι_apply` / 定理 `GradedAlgebra.ι_apply`

English:
theorem GradedAlgebra.ι_apply
  given: (m : M)
  proof: rfl

中文:
定理 GradedAlgebra.ι_apply
  条件: (m : M)
  证明: rfl
-/
theorem GradedAlgebra.ι_apply (m : M) :
    GradedAlgebra.ι R M m =
      DirectSum.of (fun (i : Nat) => ↥(LinearMap.range (TensorAlgebra.ι R : M ->ₗ[_] _) ^ i)) 1
        ⟨TensorAlgebra.ι R m, by simpa only [pow_one] using LinearMap.mem_range_self _ m⟩ :=
  rfl

variable {R M}

/--
Instance `gradedAlgebra` / 实例 `gradedAlgebra`

English:
instance gradedAlgebra
  signature: :
  body: fast_instance% GradedAlgebra.ofAlgHom _ (lift R <| GradedAlgebra.ι R M)
    (by
      ext m
      dsimp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
        AlgHom.id_apply]
      rw [lift_ι_apply]; rw [GradedAlgebra.ι_apply R M]; rw [DirectSum.coeAlgHom_of]; rw [Subtype.

中文:
实例 gradedAlgebra
  签名: :
  定义体: fast_instance% GradedAlgebra.ofAlgHom _ (lift R <| GradedAlgebra.ι R M)
    (by
      ext m
      dsimp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
        AlgHom.id_apply]
      rw [lift_ι_apply]; rw [GradedAlgebra.ι_apply R M]; rw [DirectSum.coeAlgHom_of]; rw [Subtype.

Depends on / 依赖: AlgHom, AlgHom.commutes, AlgHom.comp_apply, AlgHom.id_apply, AlgHom.toLinearMap_apply, DirectSum, DirectSum.algebraMap_apply, DirectSum.coeAlgHom_of, DirectSum.lof_eq_of, GradedAlgebra, GradedAlgebra.ofAlgHom, LinearMap, LinearMap.comp_apply, Submodule, Submodule.pow_induction_on_left, Subtype, Subtype.coe_mk, algebraMap, algebraMap_apply, coeAlgHom_of
-/
instance gradedAlgebra :
    GradedAlgebra ((LinearMap.range (ι R : M ->ₗ[R] TensorAlgebra R M) ^ ·) : Nat -> Submodule R _) :=
  fast_instance% GradedAlgebra.ofAlgHom _ (lift R <| GradedAlgebra.ι R M)
    (by
      ext m
      dsimp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
        AlgHom.id_apply]
      rw [lift_ι_apply]; rw [GradedAlgebra.ι_apply R M]; rw [DirectSum.coeAlgHom_of]; rw [Subtype.coe_mk])
    fun i x => by
    obtain ⟨x, hx⟩ := x
    dsimp only [Subtype.coe_mk, DirectSum.lof_eq_of]
    induction hx using Submodule.pow_induction_on_left' with
    | algebraMap r =>
      rw [AlgHom.commutes]; rw [DirectSum.algebraMap_apply]; rfl
    | add x y i hx hy ihx ihy =>
      rw [map_add]; rw [ihx]; rw [ihy]; rw [← map_add]
      rfl
    | mem_mul m hm i x hx ih =>
      obtain ⟨_, rfl⟩ := hm
      rw [map_mul]; rw [ih]; rw [lift_ι_apply]; rw [GradedAlgebra.ι_apply R M]; rw [DirectSum.of_mul_of]
      exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext (add_comm _ _) rfl)

end TensorAlgebra
