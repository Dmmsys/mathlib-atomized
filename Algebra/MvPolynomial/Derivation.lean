/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.MvPolynomial.Supported
public import Mathlib.RingTheory.Derivation.Basic

/-!
# Derivations of multivariate polynomials

In this file we prove that a derivation of `MvPolynomial σ R` is determined by its values on all
monomials `MvPolynomial.X i`. We also provide a constructor `MvPolynomial.mkDerivation` that
builds a derivation from its values on `X i`s and a linear equivalence
`MvPolynomial.mkDerivationEquiv` between `σ → A` and `Derivation (MvPolynomial σ R) A`.
-/

@[expose] public section


namespace MvPolynomial

noncomputable section

variable {σ R A : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A]
  [Module (MvPolynomial σ R) A]

section

variable (R)

/--
Definition of `mkDerivationₗ` / `mkDerivationₗ` 的定义

English:
definition mkDerivationₗ
  signature: (f : σ -> A)
  body: Finsupp.lsum R (fun xs : σ ->₀ Nat =>
(LinearMap.ringLmapEquivSelf R R A).symm
      xs.sum fun i k => monomial (xs - Finsupp.single i 1) (k : R) • f i)
    ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

中文:
定义 mkDerivationₗ
  签名: (f : σ -> A)
  定义体: Finsupp.lsum R (fun xs : σ ->₀ Nat =>
(LinearMap.ringLmapEquivSelf R R A).symm
      xs.sum fun i k => monomial (xs - Finsupp.single i 1) (k : R) • f i)
    ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.coeffLinearEquiv, Finsupp, Finsupp.lsum, Finsupp.single, LinearMap, LinearMap.ringLmapEquivSelf, coeffLinearEquiv, monomial, ringLmapEquivSelf, single, toLinearMap, xs.sum
-/
def mkDerivationₗ (f : σ -> A) : MvPolynomial σ R ->ₗ[R] A :=
  Finsupp.lsum R (fun xs : σ ->₀ Nat =>
(LinearMap.ringLmapEquivSelf R R A).symm
      xs.sum fun i k => monomial (xs - Finsupp.single i 1) (k : R) • f i)
    ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

end

/--
theorem `mkDerivationₗ_monomial` / 定理 `mkDerivationₗ_monomial`

English:
theorem mkDerivationₗ_monomial
  given: (f : σ -> A) (s : σ ->₀ Nat) (r : R)
  proof: sum_monomial_eq map_zero _

中文:
定理 mkDerivationₗ_monomial
  条件: (f : σ -> A) (s : σ ->₀ 自然数) (r : R)
  证明: sum_monomial_eq map_zero _

Depends on / 依赖: map_zero, sum_monomial_eq
-/
theorem mkDerivationₗ_monomial (f : σ -> A) (s : σ ->₀ Nat) (r : R) :
    mkDerivationₗ R f (monomial s r) =
      r • s.sum fun i k => monomial (s - Finsupp.single i 1) (k : R) • f i :=
sum_monomial_eq map_zero _

/--
theorem `mkDerivationₗ_C` / 定理 `mkDerivationₗ_C`

English:
theorem mkDerivationₗ_C
  given: (f : σ -> A) (r : R)
  statement: mkDerivationₗ R f (C r) = 0
  proof: (mkDerivationₗ_monomial f _ _).trans (smul_zero _)

中文:
定理 mkDerivationₗ_C
  条件: (f : σ -> A) (r : R)
  结论: mkDerivationₗ R f (C r) = 0
  证明: (mkDerivationₗ_monomial f _ _).trans (smul_zero _)

Depends on / 依赖: smul_zero
-/
theorem mkDerivationₗ_C (f : σ -> A) (r : R) : mkDerivationₗ R f (C r) = 0 :=
  (mkDerivationₗ_monomial f _ _).trans (smul_zero _)

/--
theorem `mkDerivationₗ_X` / 定理 `mkDerivationₗ_X`

English:
theorem mkDerivationₗ_X
  given: (f : σ -> A) (i : σ)
  statement: mkDerivationₗ R f (X i) = f i
  proof: (mkDerivationₗ_monomial f _ _).trans by simp [tsub_self]

@[simp]

中文:
定理 mkDerivationₗ_X
  条件: (f : σ -> A) (i : σ)
  结论: mkDerivationₗ R f (X i) = f i
  证明: (mkDerivationₗ_monomial f _ _).trans by simp [tsub_self]

@[simp]

Depends on / 依赖: tsub_self
-/
theorem mkDerivationₗ_X (f : σ -> A) (i : σ) : mkDerivationₗ R f (X i) = f i :=
(mkDerivationₗ_monomial f _ _).trans by simp [tsub_self]

@[simp]
/--
theorem `derivation_C` / 定理 `derivation_C`

English:
theorem derivation_C
  given: (D : Derivation R (MvPolynomial σ R) A) (a : R)
  statement: D (C a) = 0
  proof: D.map_algebraMap a

@[simp]

中文:
定理 derivation_C
  条件: (D : 导子 R (多元多项式 σ R) A) (a : R)
  结论: D (C a) = 0
  证明: D.map_algebraMap a

@[simp]

Depends on / 依赖: D.map_algebraMap, map_algebraMap
-/
theorem derivation_C (D : Derivation R (MvPolynomial σ R) A) (a : R) : D (C a) = 0 :=
  D.map_algebraMap a

@[simp]
/--
theorem `derivation_C_mul` / 定理 `derivation_C_mul`

English:
theorem derivation_C_mul
  given: (D : Derivation R (MvPolynomial σ R) A) (a : R) (f : MvPolynomial σ R)
  proof: by
  have : C (σ := σ) a • D f = D (C a * f) := by simp
  rw [this]; rw [C_mul']; rw [D.map_smul]

中文:
定理 derivation_C_mul
  条件: (D : 导子 R (多元多项式 σ R) A) (a : R) (f : 多元多项式 σ R)
  证明: by
  have : C (σ := σ) a • D f = D (C a * f) := by simp
  rw [this]; rw [C_mul']; rw [D.map_smul]

Depends on / 依赖: C_mul, D.map_smul, map_smul
-/
theorem derivation_C_mul (D : Derivation R (MvPolynomial σ R) A) (a : R) (f : MvPolynomial σ R) :
    C (σ := σ) a • D f = a • D f := by
  have : C (σ := σ) a • D f = D (C a * f) := by simp
  rw [this]; rw [C_mul']; rw [D.map_smul]

/--
theorem `derivation_eqOn_supported` / 定理 `derivation_eqOn_supported`

English:
theorem derivation_eqOn_supported
  statement: {D₁ D₂ : Derivation R (MvPolynomial σ R) A} {s : Set σ}
  proof: Derivation.eqOn_adjoin (Set.forall_mem_image.2 h) hf

中文:
定理 derivation_eqOn_supported
  结论: {D₁ D₂ : 导子 R (多元多项式 σ R) A} {s : 集合 σ}
  证明: Derivation.eqOn_adjoin (Set.forall_mem_image.2 h) hf

Depends on / 依赖: Derivation, Derivation.eqOn_adjoin, Set.forall_mem_image, eqOn_adjoin, forall_mem_image
-/
theorem derivation_eqOn_supported {D₁ D₂ : Derivation R (MvPolynomial σ R) A} {s : Set σ}
    (h : Set.EqOn (D₁ ∘ X) (D₂ ∘ X) s) {f : MvPolynomial σ R} (hf : f in supported R s) :
    D₁ f = D₂ f :=
  Derivation.eqOn_adjoin (Set.forall_mem_image.2 h) hf

/--
theorem `derivation_eq_of_forall_mem_vars` / 定理 `derivation_eq_of_forall_mem_vars`

English:
theorem derivation_eq_of_forall_mem_vars
  statement: {D₁ D₂ : Derivation R (MvPolynomial σ R) A}
  proof: derivation_eqOn_supported h f.mem_supported_vars

中文:
定理 derivation_eq_of_对任意_mem_vars
  结论: {D₁ D₂ : 导子 R (多元多项式 σ R) A}
  证明: derivation_eqOn_supported h f.mem_supported_vars

Depends on / 依赖: derivation_eqOn_supported, f.mem_supported_vars, mem_supported_vars
-/
theorem derivation_eq_of_forall_mem_vars {D₁ D₂ : Derivation R (MvPolynomial σ R) A}
    {f : MvPolynomial σ R} (h : forall i in f.vars, D₁ (X i) = D₂ (X i)) : D₁ f = D₂ f :=
  derivation_eqOn_supported h f.mem_supported_vars

/--
theorem `derivation_eq_zero_of_forall_mem_vars` / 定理 `derivation_eq_zero_of_forall_mem_vars`

English:
theorem derivation_eq_zero_of_forall_mem_vars
  statement: {D : Derivation R (MvPolynomial σ R) A}
  proof: show D f = (0 : Derivation R (MvPolynomial σ R) A) f from derivation_eq_of_forall_mem_vars h

@[ext]

中文:
定理 derivation_eq_zero_of_对任意_mem_vars
  结论: {D : 导子 R (多元多项式 σ R) A}
  证明: show D f = (0 : Derivation R (MvPolynomial σ R) A) f from derivation_eq_of_forall_mem_vars h

@[ext]

Depends on / 依赖: Derivation, MvPolynomial, derivation_eq_of_forall_mem_vars
-/
theorem derivation_eq_zero_of_forall_mem_vars {D : Derivation R (MvPolynomial σ R) A}
    {f : MvPolynomial σ R} (h : forall i in f.vars, D (X i) = 0) : D f = 0 :=
  show D f = (0 : Derivation R (MvPolynomial σ R) A) f from derivation_eq_of_forall_mem_vars h

@[ext]
/--
theorem `derivation_ext` / 定理 `derivation_ext`

English:
theorem derivation_ext
  given: {D₁ D₂ : Derivation R (MvPolynomial σ R) A} (h : forall i, D₁ (X i) = D₂ (X i))
  proof: Derivation.ext fun _ => derivation_eq_of_forall_mem_vars fun i _ => h i

中文:
定理 derivation_ext
  条件: {D₁ D₂ : 导子 R (多元多项式 σ R) A} (h : 对任意 i, D₁ (X i) = D₂ (X i))
  证明: Derivation.ext fun _ => derivation_eq_of_forall_mem_vars fun i _ => h i

Depends on / 依赖: Derivation, Derivation.ext, derivation_eq_of_forall_mem_vars
-/
theorem derivation_ext {D₁ D₂ : Derivation R (MvPolynomial σ R) A} (h : forall i, D₁ (X i) = D₂ (X i)) :
    D₁ = D₂ :=
  Derivation.ext fun _ => derivation_eq_of_forall_mem_vars fun i _ => h i

variable [IsScalarTower R (MvPolynomial σ R) A]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `leibniz_iff_X` / 定理 `leibniz_iff_X`

English:
theorem leibniz_iff_X
  given: (D : MvPolynomial σ R ->ₗ[R] A) (h₁ : D 1 = 0)
  proof: by
  refine ⟨fun H p i => H _ _, fun H => ?_⟩
  have hC : forall r, D (C r) = 0 := by intro r; rw [C_eq_smul_one, D.map_smul, h₁, smul_zero]
  have : forall p i, D (p * X i) = p • D (X i) + (X i : MvPolynomial σ R) • D p := by
    intro p i
    induction p using MvPolynomial.induction_on' with
    |

中文:
定理 leibniz_iff_X
  条件: (D : 多元多项式 σ R ->ₗ[R] A) (h₁ : D 1 = 0)
  证明: by
  refine ⟨fun H p i => H _ _, fun H => ?_⟩
  have hC : forall r, D (C r) = 0 := by intro r; rw [C_eq_smul_one, D.map_smul, h₁, smul_zero]
  have : forall p i, D (p * X i) = p • D (X i) + (X i : MvPolynomial σ R) • D p := by
    intro p i
    induction p using MvPolynomial.induction_on' with
    |

Depends on / 依赖: C_eq_smul_one, C_mul, C_mul_monomial, D.map_smul, MvPolynomial, MvPolynomial.induction_on, induction_on, map_smul, monomial, mul_assoc, mul_one, smul_add, smul_assoc, smul_comm, smul_zero
-/
theorem leibniz_iff_X (D : MvPolynomial σ R ->ₗ[R] A) (h₁ : D 1 = 0) :
    (forall p q, D (p * q) = p • D q + q • D p) ↔ forall s i, D (monomial s 1 * X i) =
    (monomial s 1 : MvPolynomial σ R) • D (X i) + (X i : MvPolynomial σ R) • D (monomial s 1) := by
  refine ⟨fun H p i => H _ _, fun H => ?_⟩
  have hC : forall r, D (C r) = 0 := by intro r; rw [C_eq_smul_one, D.map_smul, h₁, smul_zero]
  have : forall p i, D (p * X i) = p • D (X i) + (X i : MvPolynomial σ R) • D p := by
    intro p i
    induction p using MvPolynomial.induction_on' with
    | monomial s r =>
      rw [← mul_one r]; rw [← C_mul_monomial]; rw [mul_assoc]; rw [C_mul']; rw [D.map_smul]; rw [H]; rw [C_mul']; rw [smul_assoc]; rw [smul_add]; rw [D.map_smul]; rw [smul_comm r (X i)]
    | add p q hp hq => rw [add_mul, map_add, map_add, hp, hq, add_smul, smul_add, add_add_add_comm]
  intro p q
  induction q using MvPolynomial.induction_on with
  | C c =>
    rw [mul_comm]; rw [C_mul']; rw [hC]; rw [smul_zero]; rw [zero_add]; rw [D.map_smul]; rw [C_eq_smul_one]; rw [smul_one_smul]
  | add q₁ q₂ h₁ h₂ => simp only [mul_add, map_add, h₁, h₂, smul_add, add_smul]; abel
  | mul_X q i hq =>
    simp only [this, ← mul_assoc, hq, mul_smul, smul_add, add_assoc]
    rw [smul_comm (X i)]; rw [smul_comm (X i)]

variable (R)

/--
Definition of `mkDerivation` / `mkDerivation` 的定义

English:
definition mkDerivation
  signature: (f : σ -> A)
  body: mkDerivationₗ R f
  map_one_eq_zero' := mkDerivationₗ_C _ 1
  leibniz' :=
    (leibniz_iff_X (mkDerivationₗ R f) (mkDerivationₗ_C _ 1)).2 fun s i => by
      simp only [mkDerivationₗ_monomial, X, monomial_mul, one_smul, one_mul]
      rw [Finsupp.sum_add_index'] <;>
        [skip; simp; (intros; sim

中文:
定义 mkDerivation
  签名: (f : σ -> A)
  定义体: mkDerivationₗ R f
  map_one_eq_zero' := mkDerivationₗ_C _ 1
  leibniz' :=
    (leibniz_iff_X (mkDerivationₗ R f) (mkDerivationₗ_C _ 1)).2 fun s i => by
      simp only [mkDerivationₗ_monomial, X, monomial_mul, one_smul, one_mul]
      rw [Finsupp.sum_add_index'] <;>
        [skip; simp; (intros; sim
-/
def mkDerivation (f : σ -> A) : Derivation R (MvPolynomial σ R) A where
  toLinearMap := mkDerivationₗ R f
  map_one_eq_zero' := mkDerivationₗ_C _ 1
  leibniz' :=
    (leibniz_iff_X (mkDerivationₗ R f) (mkDerivationₗ_C _ 1)).2 fun s i => by
      simp only [mkDerivationₗ_monomial, X, monomial_mul, one_smul, one_mul]
      rw [Finsupp.sum_add_index'] <;>
        [skip; simp; (intros; simp only [Nat.cast_add, (monomial _).map_add, add_smul])]
      rw [Finsupp.sum_single_index]; rw [Finsupp.sum_single_index] <;> [skip; simp; simp]
      rw [tsub_self]; rw [add_tsub_cancel_right]; rw [Nat.cast_one]; rw [← C_apply]; rw [C_1]; rw [one_smul]; rw [add_comm]; rw [Finsupp.smul_sum]
      refine congr_arg₂ (· + ·) rfl (Finset.sum_congr rfl fun j hj => ?_); dsimp only
      rw [smul_smul]; rw [monomial_mul]; rw [one_mul]; rw [add_comm s]; rw [add_tsub_assoc_of_le]
      rwa [Finsupp.single_le_iff, Nat.succ_le_iff, pos_iff_ne_zero, ← Finsupp.mem_support_iff]

@[simp]
/--
theorem `mkDerivation_X` / 定理 `mkDerivation_X`

English:
theorem mkDerivation_X
  given: (f : σ -> A) (i : σ)
  statement: mkDerivation R f (X i) = f i
  proof: mkDerivationₗ_X f i

中文:
定理 mkDerivation_X
  条件: (f : σ -> A) (i : σ)
  结论: mkDerivation R f (X i) = f i
  证明: mkDerivationₗ_X f i
-/
theorem mkDerivation_X (f : σ -> A) (i : σ) : mkDerivation R f (X i) = f i :=
  mkDerivationₗ_X f i

/--
theorem `mkDerivation_monomial` / 定理 `mkDerivation_monomial`

English:
theorem mkDerivation_monomial
  given: (f : σ -> A) (s : σ ->₀ Nat) (r : R)
  proof: mkDerivationₗ_monomial f s r

中文:
定理 mkDerivation_monomial
  条件: (f : σ -> A) (s : σ ->₀ 自然数) (r : R)
  证明: mkDerivationₗ_monomial f s r
-/
theorem mkDerivation_monomial (f : σ -> A) (s : σ ->₀ Nat) (r : R) :
    mkDerivation R f (monomial s r) =
      r • s.sum fun i k => monomial (s - Finsupp.single i 1) (k : R) • f i :=
  mkDerivationₗ_monomial f s r

/--
Definition of `mkDerivationEquiv` / `mkDerivationEquiv` 的定义

English:
definition mkDerivationEquiv
  signature: : (σ -> A) ≃ₗ[R] Derivation R (MvPolynomial σ R) A
  body: LinearEquiv.symm
    { invFun := mkDerivation R
      toFun := fun D i => D (X i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
left_inv := fun _ => derivation_ext mkDerivation_X _ _
right_inv := fun _ => funext mkDerivation_X _ _ }

中文:
定义 mkDerivationEquiv
  签名: : (σ -> A) ≃ₗ[R] 导子 R (多元多项式 σ R) A
  定义体: LinearEquiv.symm
    { invFun := mkDerivation R
      toFun := fun D i => D (X i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
left_inv := fun _ => derivation_ext mkDerivation_X _ _
right_inv := fun _ => funext mkDerivation_X _ _ }

Depends on / 依赖: LinearEquiv, LinearEquiv.symm, derivation_ext, invFun, left_inv, map_add, map_smul, mkDerivation, mkDerivation_X, right_inv
-/
def mkDerivationEquiv : (σ -> A) ≃ₗ[R] Derivation R (MvPolynomial σ R) A :=
LinearEquiv.symm
    { invFun := mkDerivation R
      toFun := fun D i => D (X i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
left_inv := fun _ => derivation_ext mkDerivation_X _ _
right_inv := fun _ => funext mkDerivation_X _ _ }

end

end MvPolynomial
