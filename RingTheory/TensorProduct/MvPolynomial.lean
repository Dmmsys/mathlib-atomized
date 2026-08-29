/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.IsTensorProduct

/-!

# Tensor Product of (multivariate) polynomial rings

Let `Semiring R`, `Algebra R S` and `Module R N`.

* `MvPolynomial.rTensor` gives the linear equivalence
  `MvPolynomial σ S ⊗[R] N ≃ₗ[R] (σ →₀ ℕ) →₀ (S ⊗[R] N)` characterized,
  for `p : MvPolynomial σ S`, `n : N` and `d : σ →₀ ℕ`, by
  `rTensor (p ⊗ₜ[R] n) d = (coeff d p) ⊗ₜ[R] n`
* `MvPolynomial.scalarRTensor` gives the linear equivalence
  `MvPolynomial σ R ⊗[R] N ≃ₗ[R] (σ →₀ ℕ) →₀ N`
  such that `MvPolynomial.scalarRTensor (p ⊗ₜ[R] n) d = coeff d p • n`
  for `p : MvPolynomial σ R`, `n : N` and `d : σ →₀ ℕ`, by

* `MvPolynomial.rTensorAlgHom`, the algebra morphism from the tensor product
  of a polynomial algebra by an algebra to a polynomial algebra
* `MvPolynomial.rTensorAlgEquiv`, `MvPolynomial.scalarRTensorAlgEquiv`,
  the tensor product of a polynomial algebra by an algebra
  is algebraically equivalent to a polynomial algebra

## TODO :
* `MvPolynomial.rTensor` could be phrased in terms of `AddMonoidAlgebra`, and
  `MvPolynomial.rTensor` then has `smul` by the polynomial algebra.
* `MvPolynomial.rTensorAlgHom` and `MvPolynomial.scalarRTensorAlgEquiv`
  are morphisms for the algebra structure by `MvPolynomial σ R`.
-/

@[expose] public section


universe u v

noncomputable section

namespace MvPolynomial

open DirectSum TensorProduct

open Set LinearMap Submodule

variable {R : Type u} {N : Type v} [CommSemiring R]

variable {σ ι : Type*}

variable {S : Type*} [CommSemiring S] [Algebra R S]

section Algebra

variable [CommSemiring N] [Algebra R N]

/--
Definition of `rTensorAlgEquiv` / `rTensorAlgEquiv` 的定义

English:
definition rTensorAlgEquiv
  signature: : S otimes[R] MvPolynomial σ N ≃ₐ[S] MvPolynomial σ (S otimes[R] N)
  body: AddMonoidAlgebra.rTensorEquivAlgEquiv R ..

@[deprecated (since := "2026-06-18")] alias rTensorAlgHom := rTensorAlgEquiv

@[simp]

中文:
定义 rTensorAlgEquiv
  签名: : S otimes[R] MvPolynomial σ N ≃ₐ[S] MvPolynomial σ (S otimes[R] N)
  定义体: AddMonoidAlgebra.rTensorEquivAlgEquiv R ..

@[deprecated (since := "2026-06-18")] alias rTensorAlgHom := rTensorAlgEquiv

@[simp]

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.rTensorEquivAlgEquiv, rTensorEquivAlgEquiv
-/
noncomputable def rTensorAlgEquiv : S otimes[R] MvPolynomial σ N ≃ₐ[S] MvPolynomial σ (S otimes[R] N) :=
  AddMonoidAlgebra.rTensorEquivAlgEquiv R ..

@[deprecated (since := "2026-06-18")] alias rTensorAlgHom := rTensorAlgEquiv

@[simp]
/--
lemma `coeff_rTensorAlgEquiv_tmul` / 引理 `coeff_rTensorAlgEquiv_tmul`

English:
lemma coeff_rTensorAlgEquiv_tmul
  given: (s : S) (p : MvPolynomial σ N) (d : σ ->₀ Nat)
  proof: by
  simp [rTensorAlgEquiv, coeff, MvPolynomial, ← tmul_eq_smul_one_tmul]

中文:
引理 coeff_rTensorAlgEquiv_tmul
  条件: (s : S) (p : MvPolynomial σ N) (d : σ ->₀ 自然数)
  证明: by
  simp [rTensorAlgEquiv, coeff, MvPolynomial, ← tmul_eq_smul_one_tmul]

Depends on / 依赖: MvPolynomial, rTensorAlgEquiv, tmul_eq_smul_one_tmul
-/
lemma coeff_rTensorAlgEquiv_tmul (s : S) (p : MvPolynomial σ N) (d : σ ->₀ Nat) :
    coeff d (rTensorAlgEquiv (s otimesₜ[R] p)) = s otimesₜ[R] coeff d p := by
  simp [rTensorAlgEquiv, coeff, MvPolynomial, ← tmul_eq_smul_one_tmul]

/--
lemma `coeff_rTensorAlgEquiv_monomial_tmul` / 引理 `coeff_rTensorAlgEquiv_monomial_tmul`

English:
lemma coeff_rTensorAlgEquiv_monomial_tmul
  statement: [DecidableEq σ] (e : σ ->₀ Nat) (s : S) (n : N)
  proof: by
  simp [tmul_ite]

@[deprecated "Now a syntactic tautology" (since := "2026-06-18")]

中文:
引理 coeff_rTensorAlgEquiv_monomial_tmul
  结论: [DecidableEq σ] (e : σ ->₀ 自然数) (s : S) (n : N)
  证明: by
  simp [tmul_ite]

@[deprecated "Now a syntactic tautology" (since := "2026-06-18")]

Depends on / 依赖: tmul_ite
-/
lemma coeff_rTensorAlgEquiv_monomial_tmul [DecidableEq σ] (e : σ ->₀ Nat) (s : S) (n : N)
    (d : σ ->₀ Nat) :
    coeff d (rTensorAlgEquiv (s otimesₜ[R] monomial e n)) = if e = d then s otimesₜ[R] n else 0 := by
  simp [tmul_ite]

@[deprecated "Now a syntactic tautology" (since := "2026-06-18")]
/--
lemma `rTensorAlgEquiv_apply` / 引理 `rTensorAlgEquiv_apply`

English:
lemma rTensorAlgEquiv_apply
  given: (x : N otimes[R] MvPolynomial σ S)
  proof: rfl

中文:
引理 rTensorAlgEquiv_apply
  条件: (x : N otimes[R] MvPolynomial σ S)
  证明: rfl
-/
lemma rTensorAlgEquiv_apply (x : N otimes[R] MvPolynomial σ S) :
    rTensorAlgEquiv x = rTensorAlgHom x := rfl

/--
Definition of `scalarRTensorAlgEquiv` / `scalarRTensorAlgEquiv` 的定义

English:
definition scalarRTensorAlgEquiv
  signature: : N otimes[R] MvPolynomial σ R ≃ₐ[N] MvPolynomial σ N
  body: AddMonoidAlgebra.scalarTensorEquiv R N

中文:
定义 scalarRTensorAlgEquiv
  签名: : N otimes[R] MvPolynomial σ R ≃ₐ[N] MvPolynomial σ N
  定义体: AddMonoidAlgebra.scalarTensorEquiv R N

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.scalarTensorEquiv, scalarTensorEquiv
-/
noncomputable def scalarRTensorAlgEquiv : N otimes[R] MvPolynomial σ R ≃ₐ[N] MvPolynomial σ N :=
  AddMonoidAlgebra.scalarTensorEquiv R N

variable (R)
variable (A : Type*) [CommSemiring A] [Algebra R A]

/--
Definition of `algebraTensorAlgEquiv` / `algebraTensorAlgEquiv` 的定义

English:
definition algebraTensorAlgEquiv
  signature: :
  body: AddMonoidAlgebra.scalarTensorEquiv ..

@[simp]

中文:
定义 algebraTensorAlgEquiv
  签名: :
  定义体: AddMonoidAlgebra.scalarTensorEquiv ..

@[simp]

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.scalarTensorEquiv, scalarTensorEquiv
-/
noncomputable def algebraTensorAlgEquiv :
    A otimes[R] MvPolynomial σ R ≃ₐ[A] MvPolynomial σ A :=
  AddMonoidAlgebra.scalarTensorEquiv ..

@[simp]
/--
lemma `algebraTensorAlgEquiv_tmul` / 引理 `algebraTensorAlgEquiv_tmul`

English:
lemma algebraTensorAlgEquiv_tmul
  given: (a : A) (p : MvPolynomial σ R)
  proof: AddMonoidAlgebra.scalarTensorEquiv_tmul ..

@[simp]

中文:
引理 algebraTensorAlgEquiv_tmul
  条件: (a : A) (p : MvPolynomial σ R)
  证明: AddMonoidAlgebra.scalarTensorEquiv_tmul ..

@[simp]

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.scalarTensorEquiv_tmul, scalarTensorEquiv_tmul
-/
lemma algebraTensorAlgEquiv_tmul (a : A) (p : MvPolynomial σ R) :
    algebraTensorAlgEquiv R A (a otimesₜ p) = a • MvPolynomial.map (algebraMap R A) p :=
  AddMonoidAlgebra.scalarTensorEquiv_tmul ..

@[simp]
/--
lemma `algebraTensorAlgEquiv_symm_X` / 引理 `algebraTensorAlgEquiv_symm_X`

English:
lemma algebraTensorAlgEquiv_symm_X
  given: (s : σ)
  proof: AddMonoidAlgebra.scalarTensorEquiv_symm_single ..

@[simp]

中文:
引理 algebraTensorAlgEquiv_symm_X
  条件: (s : σ)
  证明: AddMonoidAlgebra.scalarTensorEquiv_symm_single ..

@[simp]

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.scalarTensorEquiv_symm_single, scalarTensorEquiv_symm_single
-/
lemma algebraTensorAlgEquiv_symm_X (s : σ) :
    (algebraTensorAlgEquiv R A).symm (X s) = 1 otimesₜ X s :=
  AddMonoidAlgebra.scalarTensorEquiv_symm_single ..

@[simp]
/--
lemma `algebraTensorAlgEquiv_symm_monomial` / 引理 `algebraTensorAlgEquiv_symm_monomial`

English:
lemma algebraTensorAlgEquiv_symm_monomial
  given: (m : σ ->₀ Nat) (a : A)
  proof: AddMonoidAlgebra.scalarTensorEquiv_symm_single ..

@[simp]

中文:
引理 algebraTensorAlgEquiv_symm_monomial
  条件: (m : σ ->₀ 自然数) (a : A)
  证明: AddMonoidAlgebra.scalarTensorEquiv_symm_single ..

@[simp]

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.scalarTensorEquiv_symm_single, scalarTensorEquiv_symm_single
-/
lemma algebraTensorAlgEquiv_symm_monomial (m : σ ->₀ Nat) (a : A) :
    (algebraTensorAlgEquiv R A).symm (monomial m a) = a otimesₜ monomial m 1 :=
  AddMonoidAlgebra.scalarTensorEquiv_symm_single ..

@[simp]
/--
lemma `algebraTensorAlgEquiv_symm_comp_aeval` / 引理 `algebraTensorAlgEquiv_symm_comp_aeval`

English:
lemma algebraTensorAlgEquiv_symm_comp_aeval
  proof: by
  ext; simp [mapAlgHom, algebraTensorAlgEquiv, X, monomial]

@[simp]

中文:
引理 algebraTensorAlgEquiv_symm_comp_aeval
  证明: by
  ext; simp [mapAlgHom, algebraTensorAlgEquiv, X, monomial]

@[simp]

Depends on / 依赖: restrictScalars, symm.toAlgHom.restrictScalars, toAlgHom
-/
lemma algebraTensorAlgEquiv_symm_comp_aeval :
    ((algebraTensorAlgEquiv (σ := σ) R A).symm.toAlgHom.restrictScalars R).comp
      (MvPolynomial.mapAlgHom (R := R) (S₁ := R) (S₂ := A) (Algebra.ofId R A)) =
      Algebra.TensorProduct.includeRight := by
  ext; simp [mapAlgHom, algebraTensorAlgEquiv, X, monomial]

@[simp]
/--
lemma `algebraTensorAlgEquiv_symm_map` / 引理 `algebraTensorAlgEquiv_symm_map`

English:
lemma algebraTensorAlgEquiv_symm_map
  given: (x : MvPolynomial σ R)
  proof: DFunLike.congr_fun (algebraTensorAlgEquiv_symm_comp_aeval R A) x

中文:
引理 algebraTensorAlgEquiv_symm_map
  条件: (x : MvPolynomial σ R)
  证明: DFunLike.congr_fun (algebraTensorAlgEquiv_symm_comp_aeval R A) x

Depends on / 依赖: DFunLike, DFunLike.congr_fun, algebraTensorAlgEquiv_symm_comp_aeval, congr_fun
-/
lemma algebraTensorAlgEquiv_symm_map (x : MvPolynomial σ R) :
    (algebraTensorAlgEquiv R A).symm (map (algebraMap R A) x) = 1 otimesₜ x :=
  DFunLike.congr_fun (algebraTensorAlgEquiv_symm_comp_aeval R A) x

/--
lemma `aeval_one_tmul` / 引理 `aeval_one_tmul`

English:
lemma aeval_one_tmul
  given: (f : σ -> S) (p : MvPolynomial σ R)
  proof: by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [algHom_C, Algebra.TensorProduct.algebraMap_apply]
    rw [← mul_one ((algebraMap R N) a)]; rw [← Algebra.smul_def]; rw [smul_tmul]; rw [Algebra.smul_def]; rw [mul_one]
  | add p q hp hq => simp [hp, hq, tmul_add]
  | mul

中文:
引理 aeval_one_tmul
  条件: (f : σ -> S) (p : MvPolynomial σ R)
  证明: by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [algHom_C, Algebra.TensorProduct.algebraMap_apply]
    rw [← mul_one ((algebraMap R N) a)]; rw [← Algebra.smul_def]; rw [smul_tmul]; rw [Algebra.smul_def]; rw [mul_one]
  | add p q hp hq => simp [hp, hq, tmul_add]
  | mul

Depends on / 依赖: Algebra, Algebra.TensorProduct.algebraMap_apply, Algebra.smul_def, MvPolynomial, MvPolynomial.induction_on, TensorProduct, algHom_C, algebraMap, algebraMap_apply, induction_on, mul_X, mul_one, smul_def, smul_tmul, tmul_add
-/
lemma aeval_one_tmul (f : σ -> S) (p : MvPolynomial σ R) :
    (aeval fun x => (1 otimesₜ[R] f x : N otimes[R] S)) p = 1 otimesₜ[R] (aeval f) p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [algHom_C, Algebra.TensorProduct.algebraMap_apply]
    rw [← mul_one ((algebraMap R N) a)]; rw [← Algebra.smul_def]; rw [smul_tmul]; rw [Algebra.smul_def]; rw [mul_one]
  | add p q hp hq => simp [hp, hq, tmul_add]
  | mul_X p i h => simp [h]

variable (S σ ι) in
/--
Definition of `tensorEquivSum` / `tensorEquivSum` 的定义

English:
definition tensorEquivSum
  signature: :
  body: ((algebraTensorAlgEquiv _ _).restrictScalars _).trans
    ((sumAlgEquiv _ _ _).symm.trans (renameEquiv _ (.sumComm ι σ)))

中文:
定义 tensorEquivSum
  签名: :
  定义体: ((algebraTensorAlgEquiv _ _).restrictScalars _).trans
    ((sumAlgEquiv _ _ _).symm.trans (renameEquiv _ (.sumComm ι σ)))

Depends on / 依赖: Pi.mul_apply, Pi.smul_apply, algebraTensorAlgEquiv, coe_mul, coe_smul, mul_apply, renameEquiv, restrictScalars, smul_apply, smul_assoc, smul_eq_mul, sumAlgEquiv, sumComm, symm.trans
-/
def tensorEquivSum :
    MvPolynomial σ S otimes[R] MvPolynomial ι R ≃ₐ[S] MvPolynomial (σ oplus ι) S :=
  ((algebraTensorAlgEquiv _ _).restrictScalars _).trans
    ((sumAlgEquiv _ _ _).symm.trans (renameEquiv _ (.sumComm ι σ)))

variable {R}

attribute [local simp] Algebra.smul_def

/--
lemma `tensorEquivSum_X_tmul_one` / 引理 `tensorEquivSum_X_tmul_one`

English:
lemma tensorEquivSum_X_tmul_one
  given: (i)
  proof: by
  simp [tensorEquivSum, algebraTensorAlgEquiv, sumAlgEquiv, renameEquiv, rename, X, X, C, monomial]

中文:
引理 tensorEquivSum_X_tmul_one
  条件: (i)
  证明: by
  simp [tensorEquivSum, algebraTensorAlgEquiv, sumAlgEquiv, renameEquiv, rename, X, X, C, monomial]

Depends on / 依赖: Pi.mul_apply, Pi.smul_apply, coe_mul, coe_smul, mul_apply, smul_apply, smul_comm, smul_eq_mul
-/
@[simp] lemma tensorEquivSum_X_tmul_one (i) :
    tensorEquivSum R σ ι S (.X i otimesₜ 1) = .X (.inl i) := by
  simp [tensorEquivSum, algebraTensorAlgEquiv, sumAlgEquiv, renameEquiv, rename, X, X, C, monomial]

/--
lemma `tensorEquivSum_C_tmul_one` / 引理 `tensorEquivSum_C_tmul_one`

English:
lemma tensorEquivSum_C_tmul_one
  given: (r)
  proof: by
  simp [tensorEquivSum, algebraTensorAlgEquiv, sumAlgEquiv, renameEquiv, rename, C, monomial]

中文:
引理 tensorEquivSum_C_tmul_one
  条件: (r)
  证明: by
  simp [tensorEquivSum, algebraTensorAlgEquiv, sumAlgEquiv, renameEquiv, rename, C, monomial]
-/
@[simp] lemma tensorEquivSum_C_tmul_one (r) :
    tensorEquivSum R σ ι S (.C r otimesₜ 1) = .C r := by
  simp [tensorEquivSum, algebraTensorAlgEquiv, sumAlgEquiv, renameEquiv, rename, C, monomial]

/--
lemma `tensorEquivSum_one_tmul_X` / 引理 `tensorEquivSum_one_tmul_X`

English:
lemma tensorEquivSum_one_tmul_X
  given: (i)
  proof: by
  simp [tensorEquivSum, algebraTensorAlgEquiv, sumAlgEquiv, renameEquiv, rename, X, C, monomial]

中文:
引理 tensorEquivSum_one_tmul_X
  条件: (i)
  证明: by
  simp [tensorEquivSum, algebraTensorAlgEquiv, sumAlgEquiv, renameEquiv, rename, X, C, monomial]
-/
@[simp] lemma tensorEquivSum_one_tmul_X (i) :
    tensorEquivSum R σ ι S (1 otimesₜ .X i) = .X (.inr i) := by
  simp [tensorEquivSum, algebraTensorAlgEquiv, sumAlgEquiv, renameEquiv, rename, X, C, monomial]

/--
lemma `tensorEquivSum_one_tmul_C` / 引理 `tensorEquivSum_one_tmul_C`

English:
lemma tensorEquivSum_one_tmul_C
  given: (r)
  proof: by
  simp [tensorEquivSum, algebraTensorAlgEquiv, sumAlgEquiv, renameEquiv, rename, C, monomial]

中文:
引理 tensorEquivSum_one_tmul_C
  条件: (r)
  证明: by
  simp [tensorEquivSum, algebraTensorAlgEquiv, sumAlgEquiv, renameEquiv, rename, C, monomial]
-/
@[simp] lemma tensorEquivSum_one_tmul_C (r) :
    tensorEquivSum R σ ι S (1 otimesₜ .C r) = .C (algebraMap R S r) := by
  simp [tensorEquivSum, algebraTensorAlgEquiv, sumAlgEquiv, renameEquiv, rename, C, monomial]

/--
lemma `tensorEquivSum_C_tmul_C` / 引理 `tensorEquivSum_C_tmul_C`

English:
lemma tensorEquivSum_C_tmul_C
  given: (r : R) (s : S)
  proof: by
  simp [tensorEquivSum, algebraTensorAlgEquiv, sumAlgEquiv, renameEquiv, rename, C, monomial,
    mul_comm]

中文:
引理 tensorEquivSum_C_tmul_C
  条件: (r : R) (s : S)
  证明: by
  simp [tensorEquivSum, algebraTensorAlgEquiv, sumAlgEquiv, renameEquiv, rename, C, monomial,
    mul_comm]
-/
@[simp] lemma tensorEquivSum_C_tmul_C (r : R) (s : S) :
    tensorEquivSum R σ ι S (.C s otimesₜ .C r) = .C (r • s) := by
  simp [tensorEquivSum, algebraTensorAlgEquiv, sumAlgEquiv, renameEquiv, rename, C, monomial,
    mul_comm]

/--
lemma `tensorEquivSum_X_tmul_X` / 引理 `tensorEquivSum_X_tmul_X`

English:
lemma tensorEquivSum_X_tmul_X
  given: (i j)
  proof: by
  simp [tensorEquivSum, algebraTensorAlgEquiv, sumAlgEquiv, renameEquiv, rename, X, C, monomial,
    Finsupp.mapDomain_add, add_comm]

中文:
引理 tensorEquivSum_X_tmul_X
  条件: (i j)
  证明: by
  simp [tensorEquivSum, algebraTensorAlgEquiv, sumAlgEquiv, renameEquiv, rename, X, C, monomial,
    Finsupp.mapDomain_add, add_comm]
-/
@[simp] lemma tensorEquivSum_X_tmul_X (i j) :
    tensorEquivSum R σ ι S (.X i otimesₜ .X j) = .X (.inl i) * .X (.inr j) := by
  simp [tensorEquivSum, algebraTensorAlgEquiv, sumAlgEquiv, renameEquiv, rename, X, C, monomial,
    Finsupp.mapDomain_add, add_comm]

section Pushout

attribute [local instance] algebraMvPolynomial

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra.IsPushout R S (MvPolynomial σ R) (MvPolynomial σ S)
  body: AddMonoidAlgebra.instIsPushout

中文:
实例 :
  签名: Algebra.IsPushout R S (MvPolynomial σ R) (MvPolynomial σ S)
  定义体: AddMonoidAlgebra.instIsPushout

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.instIsPushout, instIsPushout
-/
instance : Algebra.IsPushout R S (MvPolynomial σ R) (MvPolynomial σ S) :=
  AddMonoidAlgebra.instIsPushout

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra.IsPushout R (MvPolynomial σ R) S (MvPolynomial σ S)
  body: .symm inferInstance

中文:
实例 :
  签名: Algebra.IsPushout R (MvPolynomial σ R) S (MvPolynomial σ S)
  定义体: .symm inferInstance
-/
instance : Algebra.IsPushout R (MvPolynomial σ R) S (MvPolynomial σ S) := .symm inferInstance

end Pushout

end Algebra

end MvPolynomial

end
