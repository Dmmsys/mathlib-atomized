/-
Copyright (c) 2025 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles, Zhixuan Dai, Zhenyan Fu, Yiming Fu, Jingting Wang, Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.RingTheory.MvPolynomial

/-!
# A basis for `SymmetricAlgebra R M`

## Main definitions

* `SymmetricAlgebra.equivMvPolynomial b : SymmetricAlgebra R M ≃ₐ[R] MvPolynomial I R`:
  the isomorphism given by a basis `b : Basis I R M`.
* `Basis.symmetricAlgebra b : Basis (I →₀ ℕ) R (SymmetricAlgebra R M)`:
  the basis on the symmetric algebra given by a basis `b : Basis I R M`.

## Main results

* `SymmetricAlgebra.instFreeModule`: the symmetric algebra over `M` is free when `M` is free.
* `SymmetricAlgebra.rank_eq`: the rank of `SymmetricAlgebra R M` when `M` is a nontrivial free
  module is equal to `max (Module.rank R M) Cardinal.aleph0`.

## Implementation notes

This file closely mirrors the corresponding file for `TensorAlgebra`.
-/

@[expose] public section

open Module

namespace SymmetricAlgebra

universe uκ uR uM
variable {κ : Type uκ} {R : Type uR} {M : Type uM}

section CommSemiring
variable [CommSemiring R] [AddCommMonoid M] [Module R M]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `equivMvPolynomial` / `equivMvPolynomial` 的定义

English:
definition equivMvPolynomial
  signature: (b : Basis κ R M)
  body: .ofAlgHom
    (SymmetricAlgebra.lift <| Basis.constr b R .X)
    (MvPolynomial.aeval fun i => ι R M (b i))
    (MvPolynomial.algHom_ext fun i => by simp)
    (algHom_ext <| b.ext fun i => by simp)

@[simp]

中文:
定义 equivMvPolynomial
  签名: (b : Basis κ R M)
  定义体: .ofAlgHom
    (SymmetricAlgebra.lift <| Basis.constr b R .X)
    (MvPolynomial.aeval fun i => ι R M (b i))
    (MvPolynomial.algHom_ext fun i => by simp)
    (algHom_ext <| b.ext fun i => by simp)

@[simp]

Depends on / 依赖: Basis.constr, MvPolynomial, MvPolynomial.aeval, MvPolynomial.algHom_ext, SymmetricAlgebra, SymmetricAlgebra.lift, algHom_ext, b.ext, constr, ofAlgHom
-/
noncomputable def equivMvPolynomial (b : Basis κ R M) :
    SymmetricAlgebra R M ≃ₐ[R] MvPolynomial κ R :=
  .ofAlgHom
    (SymmetricAlgebra.lift <| Basis.constr b R .X)
    (MvPolynomial.aeval fun i => ι R M (b i))
    (MvPolynomial.algHom_ext fun i => by simp)
    (algHom_ext <| b.ext fun i => by simp)

@[simp]
/--
lemma `equivMvPolynomial_ι_apply` / 引理 `equivMvPolynomial_ι_apply`

English:
lemma equivMvPolynomial_ι_apply
  given: (b : Basis κ R M) (i : κ)
  proof: (SymmetricAlgebra.lift_ι_apply _ _).trans by simp

@[simp]

中文:
引理 equivMvPolynomial_ι_apply
  条件: (b : Basis κ R M) (i : κ)
  证明: (SymmetricAlgebra.lift_ι_apply _ _).trans by simp

@[simp]
-/
lemma equivMvPolynomial_ι_apply (b : Basis κ R M) (i : κ) :
    equivMvPolynomial b (ι R M (b i)) = .X (R := R) i :=
(SymmetricAlgebra.lift_ι_apply _ _).trans by simp

@[simp]
/--
lemma `equivMvPolynomial_symm_X` / 引理 `equivMvPolynomial_symm_X`

English:
lemma equivMvPolynomial_symm_X
  given: (b : Basis κ R M) (i : κ)
  proof: (equivMvPolynomial b).toEquiv.symm_apply_eq.mpr .symm equivMvPolynomial_ι_apply b i

中文:
引理 equivMvPolynomial_symm_X
  条件: (b : Basis κ R M) (i : κ)
  证明: (equivMvPolynomial b).toEquiv.symm_apply_eq.mpr .symm equivMvPolynomial_ι_apply b i

Depends on / 依赖: equivMvPolynomial, symm_apply_eq, toEquiv, toEquiv.symm_apply_eq.mpr
-/
lemma equivMvPolynomial_symm_X (b : Basis κ R M) (i : κ) :
    (equivMvPolynomial b).symm (MvPolynomial.X i) = ι R M (b i) :=
(equivMvPolynomial b).toEquiv.symm_apply_eq.mpr .symm equivMvPolynomial_ι_apply b i

set_option backward.isDefEq.respectTransparency false in
/--
theorem `IsSymmetricAlgebra.mvPolynomial` / 定理 `IsSymmetricAlgebra.mvPolynomial`

English:
theorem IsSymmetricAlgebra.mvPolynomial
  given: (I : Type*) (b : Basis I R M)
  proof: (SymmetricAlgebra.equivMvPolynomial b).bijective

中文:
定理 IsSymmetricAlgebra.mvPolynomial
  条件: (I : 类型) (b : Basis I R M)
  证明: (SymmetricAlgebra.equivMvPolynomial b).bijective

Depends on / 依赖: SymmetricAlgebra, SymmetricAlgebra.equivMvPolynomial, bijective, equivMvPolynomial
-/
theorem IsSymmetricAlgebra.mvPolynomial (I : Type*) (b : Basis I R M) :
    IsSymmetricAlgebra (Basis.constr b R (.X : I -> MvPolynomial I R)) :=
  (SymmetricAlgebra.equivMvPolynomial b).bijective

/-- A basis on `M` can be lifted to a basis on `SymmetricAlgebra R M`. -/
@[simps! repr_apply]
/--
Definition of `_root_.Module.Basis.symmetricAlgebra` / `_root_.Module.Basis.symmetricAlgebra` 的定义

English:
definition _root_.Module.Basis.symmetricAlgebra
  signature: (b : Basis κ R M)
  body: (MvPolynomial.basisMonomials κ R).map (SymmetricAlgebra.equivMvPolynomial b).symm.toLinearEquiv

中文:
定义 _root_.Module.Basis.symmetricAlgebra
  签名: (b : Basis κ R M)
  定义体: (MvPolynomial.basisMonomials κ R).map (SymmetricAlgebra.equivMvPolynomial b).symm.toLinearEquiv

Depends on / 依赖: MvPolynomial, MvPolynomial.basisMonomials, SymmetricAlgebra, SymmetricAlgebra.equivMvPolynomial, basisMonomials, equivMvPolynomial, symm.toLinearEquiv, toLinearEquiv
-/
noncomputable def _root_.Module.Basis.symmetricAlgebra (b : Basis κ R M) :
    Basis (κ ->₀ Nat) R (SymmetricAlgebra R M) :=
(MvPolynomial.basisMonomials κ R).map (SymmetricAlgebra.equivMvPolynomial b).symm.toLinearEquiv

/--
Instance `instModuleFree` / 实例 `instModuleFree`

English:
instance instModuleFree
  signature: [Module.Free R M]
  body: let ⟨⟨_I, b⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
  .of_basis b.symmetricAlgebra

中文:
实例 instModuleFree
  签名: [Module.Free R M]
  定义体: let ⟨⟨_I, b⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
  .of_basis b.symmetricAlgebra

Depends on / 依赖: Module, Module.Free.exists_basis, b.symmetricAlgebra, exists_basis, of_basis, symmetricAlgebra
-/
instance instModuleFree [Module.Free R M] : Module.Free R (SymmetricAlgebra R M) :=
  let ⟨⟨_I, b⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
  .of_basis b.symmetricAlgebra

/--
Instance `instNoZeroDivisors` / 实例 `instNoZeroDivisors`

English:
instance instNoZeroDivisors
  signature: [NoZeroDivisors R] [Module.Free R M]
  body: have ⟨⟨_, b⟩⟩ := ‹Module.Free R M›
  (equivMvPolynomial b).toMulEquiv.noZeroDivisors

中文:
实例 instNoZeroDivisors
  签名: [NoZeroDivisors R] [Module.Free R M]
  定义体: have ⟨⟨_, b⟩⟩ := ‹Module.Free R M›
  (equivMvPolynomial b).toMulEquiv.noZeroDivisors

Depends on / 依赖: Module, Module.Free, equivMvPolynomial, noZeroDivisors, toMulEquiv, toMulEquiv.noZeroDivisors
-/
instance instNoZeroDivisors [NoZeroDivisors R] [Module.Free R M] :
    NoZeroDivisors (SymmetricAlgebra R M) :=
  have ⟨⟨_, b⟩⟩ := ‹Module.Free R M›
  (equivMvPolynomial b).toMulEquiv.noZeroDivisors

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
instance instIsDomain [IsDomain R] [Module.Free R M] : IsDomain (SymmetricAlgebra R M) :=
  NoZeroDivisors.to_isDomain _

attribute [pp_with_univ] Cardinal.lift

open Cardinal in
/--
lemma `rank_eq` / 引理 `rank_eq`

English:
lemma rank_eq
  given: [Nontrivial M] [Module.Free R M]
  proof: by
  let ⟨⟨κ, b⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
  have : Nonempty κ := Basis.index_nonempty b
  have : Nontrivial R := Module.nontrivial R M
  rw [(equivMvPolynomial b).toLinearEquiv.rank_eq]; rw [MvPolynomial.rank_eq_lift]; rw [Cardinal.mk_finsupp_nat]; rw [Basis.mk_eq_rank'' b]

中文:
引理 rank_eq
  条件: [Nontrivial M] [Module.Free R M]
  证明: by
  let ⟨⟨κ, b⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
  have : Nonempty κ := Basis.index_nonempty b
  have : Nontrivial R := Module.nontrivial R M
  rw [(equivMvPolynomial b).toLinearEquiv.rank_eq]; rw [MvPolynomial.rank_eq_lift]; rw [Cardinal.mk_finsupp_nat]; rw [Basis.mk_eq_rank'' b]

Depends on / 依赖: Basis.index_nonempty, Basis.mk_eq_rank, Cardinal, Cardinal.mk_finsupp_nat, Module, Module.Free.exists_basis, Module.nontrivial, MvPolynomial, MvPolynomial.rank_eq_lift, Nonempty, Nontrivial, equivMvPolynomial, exists_basis, index_nonempty, mk_eq_rank, mk_finsupp_nat, nontrivial, rank_eq, rank_eq_lift, toLinearEquiv
-/
lemma rank_eq [Nontrivial M] [Module.Free R M] :
    Module.rank R (SymmetricAlgebra R M) = Cardinal.lift.{uR} (max (Module.rank R M) ℵ₀) := by
  let ⟨⟨κ, b⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
  have : Nonempty κ := Basis.index_nonempty b
  have : Nontrivial R := Module.nontrivial R M
  rw [(equivMvPolynomial b).toLinearEquiv.rank_eq]; rw [MvPolynomial.rank_eq_lift]; rw [Cardinal.mk_finsupp_nat]; rw [Basis.mk_eq_rank'' b]

end CommRing

end SymmetricAlgebra
