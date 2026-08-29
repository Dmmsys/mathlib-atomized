/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.TensorAlgebra.Basic
public import Mathlib.LinearAlgebra.FreeAlgebra

/-!
# A basis for `TensorAlgebra R M`

## Main definitions

* `TensorAlgebra.equivMonoidAlgebra b : TensorAlgebra R M ≃ₐ[R] FreeAlgebra R κ`:
  the isomorphism given by a basis `b : Basis κ R M`.
* `Basis.tensorAlgebra b : Basis (FreeMonoid κ) R (TensorAlgebra R M)`:
  the basis on the tensor algebra given by a basis `b : Basis κ R M`.

## Main results

* `TensorAlgebra.instFreeModule`: the tensor algebra over `M` is free when `M` is
* `TensorAlgebra.rank_eq`

-/

@[expose] public section

open Module

namespace TensorAlgebra

universe uκ uR uM
variable {κ : Type uκ} {R : Type uR} {M : Type uM}

section CommSemiring
variable [CommSemiring R] [AddCommMonoid M] [Module R M]

/--
Definition of `equivFreeAlgebra` / `equivFreeAlgebra` 的定义

English:
definition equivFreeAlgebra
  signature: (b : Basis κ R M)
  body: AlgEquiv.ofAlgHom
    (TensorAlgebra.lift _ (Finsupp.linearCombination _ (FreeAlgebra.ι _) ∘ₗ b.repr.toLinearMap))
    (FreeAlgebra.lift _ (ι R ∘ b))
    (by ext; simp)
    (hom_ext <| b.ext fun i => by simp)

@[simp]

中文:
定义 equivFreeAlgebra
  签名: (b : Basis κ R M)
  定义体: AlgEquiv.ofAlgHom
    (TensorAlgebra.lift _ (Finsupp.linearCombination _ (FreeAlgebra.ι _) ∘ₗ b.repr.toLinearMap))
    (FreeAlgebra.lift _ (ι R ∘ b))
    (by ext; simp)
    (hom_ext <| b.ext fun i => by simp)

@[simp]

Depends on / 依赖: AlgEquiv, AlgEquiv.ofAlgHom, Finsupp, Finsupp.linearCombination, FreeAlgebra, FreeAlgebra.lift, TensorAlgebra, TensorAlgebra.lift, b.ext, b.repr.toLinearMap, hom_ext, linearCombination, ofAlgHom, toLinearMap
-/
noncomputable def equivFreeAlgebra (b : Basis κ R M) :
    TensorAlgebra R M ≃ₐ[R] FreeAlgebra R κ :=
  AlgEquiv.ofAlgHom
    (TensorAlgebra.lift _ (Finsupp.linearCombination _ (FreeAlgebra.ι _) ∘ₗ b.repr.toLinearMap))
    (FreeAlgebra.lift _ (ι R ∘ b))
    (by ext; simp)
    (hom_ext <| b.ext fun i => by simp)

@[simp]
/--
lemma `equivFreeAlgebra_ι_apply` / 引理 `equivFreeAlgebra_ι_apply`

English:
lemma equivFreeAlgebra_ι_apply
  given: (b : Basis κ R M) (i : κ)
  proof: (TensorAlgebra.lift_ι_apply _ _).trans by simp

@[simp]

中文:
引理 equivFreeAlgebra_ι_apply
  条件: (b : Basis κ R M) (i : κ)
  证明: (TensorAlgebra.lift_ι_apply _ _).trans by simp

@[simp]

Depends on / 依赖: TensorAlgebra, TensorAlgebra.lift_
-/
lemma equivFreeAlgebra_ι_apply (b : Basis κ R M) (i : κ) :
    equivFreeAlgebra b (ι R (b i)) = FreeAlgebra.ι R i :=
(TensorAlgebra.lift_ι_apply _ _).trans by simp

@[simp]
/--
lemma `equivFreeAlgebra_symm_ι` / 引理 `equivFreeAlgebra_symm_ι`

English:
lemma equivFreeAlgebra_symm_ι
  given: (b : Basis κ R M) (i : κ)
  proof: (equivFreeAlgebra b).toEquiv.symm_apply_eq.mpr .symm equivFreeAlgebra_ι_apply b i

中文:
引理 equivFreeAlgebra_symm_ι
  条件: (b : Basis κ R M) (i : κ)
  证明: (equivFreeAlgebra b).toEquiv.symm_apply_eq.mpr .symm equivFreeAlgebra_ι_apply b i

Depends on / 依赖: equivFreeAlgebra, symm_apply_eq, toEquiv, toEquiv.symm_apply_eq.mpr
-/
lemma equivFreeAlgebra_symm_ι (b : Basis κ R M) (i : κ) :
    (equivFreeAlgebra b).symm (FreeAlgebra.ι R i) = ι R (b i) :=
(equivFreeAlgebra b).toEquiv.symm_apply_eq.mpr .symm equivFreeAlgebra_ι_apply b i

/-- A basis on `M` can be lifted to a basis on `TensorAlgebra R M` -/
@[simps! repr_apply]
/--
Definition of `_root_.Module.Basis.tensorAlgebra` / `_root_.Module.Basis.tensorAlgebra` 的定义

English:
definition _root_.Module.Basis.tensorAlgebra
  signature: (b : Basis κ R M)
  body: (FreeAlgebra.basisFreeMonoid R κ).map (equivFreeAlgebra b).symm.toLinearEquiv

中文:
定义 _root_.Module.Basis.tensorAlgebra
  签名: (b : Basis κ R M)
  定义体: (FreeAlgebra.basisFreeMonoid R κ).map (equivFreeAlgebra b).symm.toLinearEquiv

Depends on / 依赖: FreeAlgebra, FreeAlgebra.basisFreeMonoid, basisFreeMonoid, equivFreeAlgebra, symm.toLinearEquiv, toLinearEquiv
-/
noncomputable def _root_.Module.Basis.tensorAlgebra (b : Basis κ R M) :
    Basis (FreeMonoid κ) R (TensorAlgebra R M) :=
(FreeAlgebra.basisFreeMonoid R κ).map (equivFreeAlgebra b).symm.toLinearEquiv

/--
Instance `instModuleFree` / 实例 `instModuleFree`

English:
instance instModuleFree
  signature: [Module.Free R M]
  body: let ⟨⟨_κ, b⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
  .of_basis b.tensorAlgebra

中文:
实例 instModuleFree
  签名: [Module.Free R M]
  定义体: let ⟨⟨_κ, b⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
  .of_basis b.tensorAlgebra

Depends on / 依赖: Module, Module.Free.exists_basis, b.tensorAlgebra, exists_basis, of_basis, tensorAlgebra
-/
instance instModuleFree [Module.Free R M] : Module.Free R (TensorAlgebra R M) :=
  let ⟨⟨_κ, b⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
  .of_basis b.tensorAlgebra

/--
Instance `instNoZeroDivisors` / 实例 `instNoZeroDivisors`

English:
instance instNoZeroDivisors
  signature: [NoZeroDivisors R] [Module.Free R M]
  body: have ⟨⟨_, b⟩⟩ := ‹Module.Free R M›
  (equivFreeAlgebra b).toMulEquiv.noZeroDivisors

中文:
实例 instNoZeroDivisors
  签名: [NoZeroDivisors R] [Module.Free R M]
  定义体: have ⟨⟨_, b⟩⟩ := ‹Module.Free R M›
  (equivFreeAlgebra b).toMulEquiv.noZeroDivisors

Depends on / 依赖: Module, Module.Free, equivFreeAlgebra, noZeroDivisors, toMulEquiv, toMulEquiv.noZeroDivisors
-/
instance instNoZeroDivisors [NoZeroDivisors R] [Module.Free R M] :
    NoZeroDivisors (TensorAlgebra R M) :=
  have ⟨⟨_, b⟩⟩ := ‹Module.Free R M›
  (equivFreeAlgebra b).toMulEquiv.noZeroDivisors

end CommSemiring

section CommRing
variable [CommRing R] [AddCommGroup M] [Module R M]

/--
Instance `instIsDomain` / 实例 `instIsDomain`

English:
instance instIsDomain
  signature: [IsDomain R] [Module.Free R M]
  body: NoZeroDivisors.to_isDomain _

中文:
实例 instIsDomain
  签名: [IsDomain R] [Module.Free R M]
  定义体: NoZeroDivisors.to_isDomain _

Depends on / 依赖: NoZeroDivisors, NoZeroDivisors.to_isDomain, to_isDomain
-/
instance instIsDomain [IsDomain R] [Module.Free R M] : IsDomain (TensorAlgebra R M) :=
  NoZeroDivisors.to_isDomain _

attribute [pp_with_univ] Cardinal.lift

open Cardinal in
/--
lemma `rank_eq` / 引理 `rank_eq`

English:
lemma rank_eq
  given: [Nontrivial R] [Module.Free R M]
  proof: by
  let ⟨⟨κ, b⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
  rw [(equivFreeAlgebra b).toLinearEquiv.rank_eq]; rw [FreeAlgebra.rank_eq]; rw [mk_list_eq_sum_pow]; rw [Basis.mk_eq_rank'' b]

中文:
引理 rank_eq
  条件: [Nontrivial R] [Module.Free R M]
  证明: by
  let ⟨⟨κ, b⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
  rw [(equivFreeAlgebra b).toLinearEquiv.rank_eq]; rw [FreeAlgebra.rank_eq]; rw [mk_list_eq_sum_pow]; rw [Basis.mk_eq_rank'' b]

Depends on / 依赖: Basis.mk_eq_rank, FreeAlgebra, FreeAlgebra.rank_eq, Module, Module.Free.exists_basis, equivFreeAlgebra, exists_basis, mk_eq_rank, mk_list_eq_sum_pow, rank_eq, toLinearEquiv, toLinearEquiv.rank_eq
-/
lemma rank_eq [Nontrivial R] [Module.Free R M] :
    Module.rank R (TensorAlgebra R M) = Cardinal.lift.{uR} (sum fun n => Module.rank R M ^ n) := by
  let ⟨⟨κ, b⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
  rw [(equivFreeAlgebra b).toLinearEquiv.rank_eq]; rw [FreeAlgebra.rank_eq]; rw [mk_list_eq_sum_pow]; rw [Basis.mk_eq_rank'' b]

end CommRing

end TensorAlgebra
