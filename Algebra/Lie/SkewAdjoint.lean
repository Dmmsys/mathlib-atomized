/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.Matrix
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.Tactic.NoncommRing

/-!
# Lie algebras of skew-adjoint endomorphisms of a bilinear form

When a module carries a bilinear form, the Lie algebra of endomorphisms of the module contains a
distinguished Lie subalgebra: the skew-adjoint endomorphisms. Such subalgebras are important
because they provide a simple, explicit construction of the so-called classical Lie algebras.

This file defines the Lie subalgebra of skew-adjoint endomorphisms cut out by a bilinear form on
a module and proves some basic related results. It also provides the corresponding definitions and
results for the Lie algebra of square matrices.

## Main definitions

  * `skewAdjointLieSubalgebra`
  * `skewAdjointLieSubalgebraEquiv`
  * `skewAdjointMatricesLieSubalgebra`
  * `skewAdjointMatricesLieSubalgebraEquiv`

## Tags

lie algebra, skew-adjoint, bilinear form
-/

@[expose] public section


universe u v w w₁

section SkewAdjointEndomorphisms

open LinearMap (BilinForm)

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
variable (B : BilinForm R M)

/--
theorem `LinearMap.BilinForm.isSkewAdjoint_bracket` / 定理 `LinearMap.BilinForm.isSkewAdjoint_bracket`

English:
theorem LinearMap.BilinForm.isSkewAdjoint_bracket
  statement: {f g : Module.End R M}
  proof: by
  rw [mem_skewAdjointSubmodule] at *
  have hfg : IsAdjointPair B B (f * g) (g * f) := by rw [← neg_mul_neg g f]; exact hg.comp hf
  have hgf : IsAdjointPair B B (g * f) (f * g) := by rw [← neg_mul_neg f g]; exact hf.comp hg
  change IsAdjointPair B B (f * g - g * f) (-(f * g - g * f)); rw [neg_s

中文:
定理 线性映射.BilinForm.isSkewAdjoint_bracket
  结论: {f g : 模.End R M}
  证明: by
  rw [mem_skewAdjointSubmodule] at *
  have hfg : IsAdjointPair B B (f * g) (g * f) := by rw [← neg_mul_neg g f]; exact hg.comp hf
  have hgf : IsAdjointPair B B (g * f) (f * g) := by rw [← neg_mul_neg f g]; exact hf.comp hg
  change IsAdjointPair B B (f * g - g * f) (-(f * g - g * f)); rw [neg_s

Depends on / 依赖: IsAdjointPair, hf.comp, hfg.sub, hg.comp, mem_skewAdjointSubmodule, neg_mul_neg, neg_sub
-/
theorem LinearMap.BilinForm.isSkewAdjoint_bracket {f g : Module.End R M}
    (hf : f in B.skewAdjointSubmodule) (hg : g in B.skewAdjointSubmodule) :
    ⁅f, g⁆ in B.skewAdjointSubmodule := by
  rw [mem_skewAdjointSubmodule] at *
  have hfg : IsAdjointPair B B (f * g) (g * f) := by rw [← neg_mul_neg g f]; exact hg.comp hf
  have hgf : IsAdjointPair B B (g * f) (f * g) := by rw [← neg_mul_neg f g]; exact hf.comp hg
  change IsAdjointPair B B (f * g - g * f) (-(f * g - g * f)); rw [neg_sub]
  exact hfg.sub hgf

attribute [local instance 100] LieRing.ofAssociativeRing

/--
Definition of `skewAdjointLieSubalgebra` / `skewAdjointLieSubalgebra` 的定义

English:
definition skewAdjointLieSubalgebra
  signature: : LieSubalgebra R (Module.End R M)
  body: { B.skewAdjointSubmodule with
    lie_mem' := B.isSkewAdjoint_bracket }

中文:
定义 skewAdjointLieSubalgebra
  签名: : Lie子代数 R (模.End R M)
  定义体: { B.skewAdjointSubmodule with
    lie_mem' := B.isSkewAdjoint_bracket }

Depends on / 依赖: B.isSkewAdjoint_bracket, B.skewAdjointSubmodule, isSkewAdjoint_bracket, lie_mem, skewAdjointSubmodule
-/
def skewAdjointLieSubalgebra : LieSubalgebra R (Module.End R M) :=
  { B.skewAdjointSubmodule with
    lie_mem' := B.isSkewAdjoint_bracket }

variable {N : Type w} [AddCommGroup N] [Module R N] (e : N ≃ₗ[R] M)

/--
Definition of `skewAdjointLieSubalgebraEquiv` / `skewAdjointLieSubalgebraEquiv` 的定义

English:
definition skewAdjointLieSubalgebraEquiv
  signature: :
  body: by
  apply LieEquiv.ofSubalgebras _ _ e.lieConj
  ext f
  simp only [Submodule.mem_map_equiv, LieSubalgebra.mem_map_submodule]
  exact (LinearMap.isPairSelfAdjoint_equiv (B := -B) (F := B) e f).symm

@[simp]

中文:
定义 skewAdjointLieSubalgebraEquiv
  签名: :
  定义体: by
  apply LieEquiv.ofSubalgebras _ _ e.lieConj
  ext f
  simp only [Submodule.mem_map_equiv, LieSubalgebra.mem_map_submodule]
  exact (LinearMap.isPairSelfAdjoint_equiv (B := -B) (F := B) e f).symm

@[simp]

Depends on / 依赖: LieEquiv, LieEquiv.ofSubalgebras, LieSubalgebra, LieSubalgebra.mem_map_submodule, LinearMap, LinearMap.isPairSelfAdjoint_equiv, Submodule, Submodule.mem_map_equiv, e.lieConj, isPairSelfAdjoint_equiv, lieConj, mem_map_equiv, mem_map_submodule, ofSubalgebras
-/
def skewAdjointLieSubalgebraEquiv :
    skewAdjointLieSubalgebra (B.compl₁₂ (e : N ->ₗ[R] M) e) ≃ₗ⁅R⁆ skewAdjointLieSubalgebra B := by
  apply LieEquiv.ofSubalgebras _ _ e.lieConj
  ext f
  simp only [Submodule.mem_map_equiv, LieSubalgebra.mem_map_submodule]
  exact (LinearMap.isPairSelfAdjoint_equiv (B := -B) (F := B) e f).symm

@[simp]
/--
theorem `skewAdjointLieSubalgebraEquiv_apply` / 定理 `skewAdjointLieSubalgebraEquiv_apply`

English:
theorem skewAdjointLieSubalgebraEquiv_apply
  proof: by
  simp [skewAdjointLieSubalgebraEquiv]

@[simp]

中文:
定理 skewAdjointLieSubalgebraEquiv_apply
  证明: by
  simp [skewAdjointLieSubalgebraEquiv]

@[simp]
-/
theorem skewAdjointLieSubalgebraEquiv_apply
    (f : skewAdjointLieSubalgebra (B.compl₁₂ (Qₗ := N) (Qₗ' := N) ↑e ↑e)) :
    ↑(skewAdjointLieSubalgebraEquiv B e f) = e.lieConj f := by
  simp [skewAdjointLieSubalgebraEquiv]

@[simp]
/--
theorem `skewAdjointLieSubalgebraEquiv_symm_apply` / 定理 `skewAdjointLieSubalgebraEquiv_symm_apply`

English:
theorem skewAdjointLieSubalgebraEquiv_symm_apply
  given: (f : skewAdjointLieSubalgebra B)
  proof: by
  simp [skewAdjointLieSubalgebraEquiv]

中文:
定理 skewAdjointLieSubalgebraEquiv_symm_apply
  条件: (f : skewAdjointLieSubalgebra B)
  证明: by
  simp [skewAdjointLieSubalgebraEquiv]

Depends on / 依赖: skewAdjointLieSubalgebraEquiv
-/
theorem skewAdjointLieSubalgebraEquiv_symm_apply (f : skewAdjointLieSubalgebra B) :
    ↑((skewAdjointLieSubalgebraEquiv B e).symm f) = e.symm.lieConj f := by
  simp [skewAdjointLieSubalgebraEquiv]

end SkewAdjointEndomorphisms

section SkewAdjointMatrices

open scoped Matrix

variable {R : Type u} {n : Type w} [CommRing R] [Fintype n]
variable (J : Matrix n n R)

/--
theorem `Matrix.lie_transpose` / 定理 `Matrix.lie_transpose`

English:
theorem Matrix.lie_transpose
  given: (A B : Matrix n n R)
  statement: ⁅A, B⁆ᵀ = ⁅Bᵀ, Aᵀ⁆
  proof: show (A * B - B * A)ᵀ = Bᵀ * Aᵀ - Aᵀ * Bᵀ by simp

中文:
定理 矩阵.lie_transpose
  条件: (A B : 矩阵 n n R)
  结论: ⁅A, B⁆ᵀ = ⁅Bᵀ, Aᵀ⁆
  证明: show (A * B - B * A)ᵀ = Bᵀ * Aᵀ - Aᵀ * Bᵀ by simp
-/
theorem Matrix.lie_transpose (A B : Matrix n n R) : ⁅A, B⁆ᵀ = ⁅Bᵀ, Aᵀ⁆ :=
  show (A * B - B * A)ᵀ = Bᵀ * Aᵀ - Aᵀ * Bᵀ by simp

variable [DecidableEq n]

/--
theorem `Matrix.isSkewAdjoint_bracket` / 定理 `Matrix.isSkewAdjoint_bracket`

English:
theorem Matrix.isSkewAdjoint_bracket
  statement: {A B : Matrix n n R} (hA : A in skewAdjointMatricesSubmodule J)
  proof: by
  simp only [mem_skewAdjointMatricesSubmodule] at *
  change ⁅A, B⁆ᵀ * J = J * (-⁅A, B⁆)
  change Aᵀ * J = J * (-A) at hA
  change Bᵀ * J = J * (-B) at hB
  rw [Matrix.lie_transpose]; rw [LieRing.of_associative_ring_bracket]; rw [LieRing.of_associative_ring_bracket]; rw [sub_mul]; rw [mul_assoc];

中文:
定理 矩阵.isSkewAdjoint_bracket
  结论: {A B : 矩阵 n n R} (hA : A in skewAdjointMatricesSubmodule J)
  证明: by
  simp only [mem_skewAdjointMatricesSubmodule] at *
  change ⁅A, B⁆ᵀ * J = J * (-⁅A, B⁆)
  change Aᵀ * J = J * (-A) at hA
  change Bᵀ * J = J * (-B) at hB
  rw [Matrix.lie_transpose]; rw [LieRing.of_associative_ring_bracket]; rw [LieRing.of_associative_ring_bracket]; rw [sub_mul]; rw [mul_assoc];

Depends on / 依赖: LieRing, LieRing.of_associative_ring_bracket, Matrix, Matrix.lie_transpose, lie_transpose, mem_skewAdjointMatricesSubmodule, mul_assoc, noncomm_ring, of_associative_ring_bracket, sub_mul
-/
theorem Matrix.isSkewAdjoint_bracket {A B : Matrix n n R} (hA : A in skewAdjointMatricesSubmodule J)
    (hB : B in skewAdjointMatricesSubmodule J) : ⁅A, B⁆ in skewAdjointMatricesSubmodule J := by
  simp only [mem_skewAdjointMatricesSubmodule] at *
  change ⁅A, B⁆ᵀ * J = J * (-⁅A, B⁆)
  change Aᵀ * J = J * (-A) at hA
  change Bᵀ * J = J * (-B) at hB
  rw [Matrix.lie_transpose]; rw [LieRing.of_associative_ring_bracket]; rw [LieRing.of_associative_ring_bracket]; rw [sub_mul]; rw [mul_assoc]; rw [mul_assoc]; rw [hA]; rw [hB]; rw [← mul_assoc]; rw [← mul_assoc]; rw [hA]; rw [hB]
  noncomm_ring

attribute [local instance 100] LieRing.ofAssociativeRing

/--
Definition of `skewAdjointMatricesLieSubalgebra` / `skewAdjointMatricesLieSubalgebra` 的定义

English:
definition skewAdjointMatricesLieSubalgebra
  signature: : LieSubalgebra R (Matrix n n R)
  body: { skewAdjointMatricesSubmodule J with
    lie_mem' := J.isSkewAdjoint_bracket }

@[simp]

中文:
定义 skewAdjointMatricesLieSubalgebra
  签名: : Lie子代数 R (矩阵 n n R)
  定义体: { skewAdjointMatricesSubmodule J with
    lie_mem' := J.isSkewAdjoint_bracket }

@[simp]

Depends on / 依赖: J.isSkewAdjoint_bracket, isSkewAdjoint_bracket, lie_mem, skewAdjointMatricesSubmodule
-/
def skewAdjointMatricesLieSubalgebra : LieSubalgebra R (Matrix n n R) :=
  { skewAdjointMatricesSubmodule J with
    lie_mem' := J.isSkewAdjoint_bracket }

@[simp]
/--
theorem `mem_skewAdjointMatricesLieSubalgebra` / 定理 `mem_skewAdjointMatricesLieSubalgebra`

English:
theorem mem_skewAdjointMatricesLieSubalgebra
  given: (A : Matrix n n R)
  proof: Iff.rfl

中文:
定理 mem_skewAdjointMatricesLieSubalgebra
  条件: (A : 矩阵 n n R)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_skewAdjointMatricesLieSubalgebra (A : Matrix n n R) :
    A in skewAdjointMatricesLieSubalgebra J ↔ A in skewAdjointMatricesSubmodule J :=
  Iff.rfl

/--
Definition of `skewAdjointMatricesLieSubalgebraEquiv` / `skewAdjointMatricesLieSubalgebraEquiv` 的定义

English:
definition skewAdjointMatricesLieSubalgebraEquiv
  signature: (P : Matrix n n R) (h : Invertible P)
  body: LieEquiv.ofSubalgebras _ _ (P.lieConj h).symm by
    ext A
    suffices P.lieConj h A in skewAdjointMatricesSubmodule J ↔
        A in skewAdjointMatricesSubmodule (Pᵀ * J * P) by
      simp only [Submodule.mem_map_equiv, LieSubalgebra.mem_map_submodule]
      exact this
    simp [Matrix.IsSkewAdjoi

中文:
定义 skewAdjointMatricesLieSubalgebraEquiv
  签名: (P : 矩阵 n n R) (h : 可逆 P)
  定义体: LieEquiv.ofSubalgebras _ _ (P.lieConj h).symm by
    ext A
    suffices P.lieConj h A in skewAdjointMatricesSubmodule J ↔
        A in skewAdjointMatricesSubmodule (Pᵀ * J * P) by
      simp only [Submodule.mem_map_equiv, LieSubalgebra.mem_map_submodule]
      exact this
    simp [Matrix.IsSkewAdjoi

Depends on / 依赖: IsSkewAdjoint, J.isAdjointPair_equiv, LieEquiv, LieEquiv.ofSubalgebras, LieSubalgebra, LieSubalgebra.mem_map_submodule, Matrix, Matrix.IsSkewAdjoint, P.lieConj, Submodule, Submodule.mem_map_equiv, isAdjointPair_equiv, isUnit_of_invertible, lieConj, mem_map_equiv, mem_map_submodule, ofSubalgebras, skewAdjointMatricesSubmodule
-/
def skewAdjointMatricesLieSubalgebraEquiv (P : Matrix n n R) (h : Invertible P) :
    skewAdjointMatricesLieSubalgebra J ≃ₗ⁅R⁆ skewAdjointMatricesLieSubalgebra (Pᵀ * J * P) :=
LieEquiv.ofSubalgebras _ _ (P.lieConj h).symm by
    ext A
    suffices P.lieConj h A in skewAdjointMatricesSubmodule J ↔
        A in skewAdjointMatricesSubmodule (Pᵀ * J * P) by
      simp only [Submodule.mem_map_equiv, LieSubalgebra.mem_map_submodule]
      exact this
    simp [Matrix.IsSkewAdjoint, J.isAdjointPair_equiv _ _ P (isUnit_of_invertible P)]

/--
theorem `skewAdjointMatricesLieSubalgebraEquiv_apply` / 定理 `skewAdjointMatricesLieSubalgebraEquiv_apply`

English:
theorem skewAdjointMatricesLieSubalgebraEquiv_apply
  statement: (P : Matrix n n R) (h : Invertible P)
  proof: by
  simp [skewAdjointMatricesLieSubalgebraEquiv]

中文:
定理 skewAdjointMatricesLieSubalgebraEquiv_apply
  结论: (P : 矩阵 n n R) (h : 可逆 P)
  证明: by
  simp [skewAdjointMatricesLieSubalgebraEquiv]

Depends on / 依赖: skewAdjointMatricesLieSubalgebraEquiv
-/
theorem skewAdjointMatricesLieSubalgebraEquiv_apply (P : Matrix n n R) (h : Invertible P)
    (A : skewAdjointMatricesLieSubalgebra J) :
    ↑(skewAdjointMatricesLieSubalgebraEquiv J P h A) = P⁻¹ * A * P := by
  simp [skewAdjointMatricesLieSubalgebraEquiv]

/--
Definition of `skewAdjointMatricesLieSubalgebraEquivTranspose` / `skewAdjointMatricesLieSubalgebraEquivTranspose` 的定义

English:
definition skewAdjointMatricesLieSubalgebraEquivTranspose
  signature: {m : Type w} [DecidableEq m] [Fintype m]
  body: LieEquiv.ofSubalgebras _ _ e.toLieEquiv by
    ext A
    suffices J.IsSkewAdjoint (e.symm A) ↔ (e J).IsSkewAdjoint A by
      simpa [-LieSubalgebra.mem_map, LieSubalgebra.mem_map_submodule]
    simp only [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair, ← h,
      ← Function.Injective.eq_iff e.injective,

中文:
定义 skewAdjointMatricesLieSubalgebraEquivTranspose
  签名: {m : 类型 w} [DecidableEq m] [有限类型 m]
  定义体: LieEquiv.ofSubalgebras _ _ e.toLieEquiv by
    ext A
    suffices J.IsSkewAdjoint (e.symm A) ↔ (e J).IsSkewAdjoint A by
      simpa [-LieSubalgebra.mem_map, LieSubalgebra.mem_map_submodule]
    simp only [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair, ← h,
      ← Function.Injective.eq_iff e.injective,

Depends on / 依赖: AlgEquiv, AlgEquiv.apply_symm_apply, Function, Function.Injective.eq_iff, Injective, IsAdjointPair, IsSkewAdjoint, J.IsSkewAdjoint, LieEquiv, LieEquiv.ofSubalgebras, LieSubalgebra, LieSubalgebra.mem_map, LieSubalgebra.mem_map_submodule, Matrix, Matrix.IsAdjointPair, Matrix.IsSkewAdjoint, apply_symm_apply, e.injective, e.symm, e.toLieEquiv
-/
def skewAdjointMatricesLieSubalgebraEquivTranspose {m : Type w} [DecidableEq m] [Fintype m]
    (e : Matrix n n R ≃ₐ[R] Matrix m m R) (h : forall A, (e A)ᵀ = e Aᵀ) :
    skewAdjointMatricesLieSubalgebra J ≃ₗ⁅R⁆ skewAdjointMatricesLieSubalgebra (e J) :=
LieEquiv.ofSubalgebras _ _ e.toLieEquiv by
    ext A
    suffices J.IsSkewAdjoint (e.symm A) ↔ (e J).IsSkewAdjoint A by
      simpa [-LieSubalgebra.mem_map, LieSubalgebra.mem_map_submodule]
    simp only [Matrix.IsSkewAdjoint, Matrix.IsAdjointPair, ← h,
      ← Function.Injective.eq_iff e.injective, map_mul, AlgEquiv.apply_symm_apply, map_neg]

@[simp]
/--
theorem `skewAdjointMatricesLieSubalgebraEquivTranspose_apply` / 定理 `skewAdjointMatricesLieSubalgebraEquivTranspose_apply`

English:
theorem skewAdjointMatricesLieSubalgebraEquivTranspose_apply
  statement: {m : Type w} [DecidableEq m]
  proof: rfl

中文:
定理 skewAdjointMatricesLieSubalgebraEquivTranspose_apply
  结论: {m : 类型 w} [DecidableEq m]
  证明: rfl
-/
theorem skewAdjointMatricesLieSubalgebraEquivTranspose_apply {m : Type w} [DecidableEq m]
    [Fintype m] (e : Matrix n n R ≃ₐ[R] Matrix m m R) (h : forall A, (e A)ᵀ = e Aᵀ)
    (A : skewAdjointMatricesLieSubalgebra J) :
    (skewAdjointMatricesLieSubalgebraEquivTranspose J e h A : Matrix m m R) = e A :=
  rfl

/--
theorem `mem_skewAdjointMatricesLieSubalgebra_unit_smul` / 定理 `mem_skewAdjointMatricesLieSubalgebra_unit_smul`

English:
theorem mem_skewAdjointMatricesLieSubalgebra_unit_smul
  given: (u : Rˣ) (J A : Matrix n n R)
  proof: by
  change A in skewAdjointMatricesSubmodule (u • J) ↔ A in skewAdjointMatricesSubmodule J
  simp only [mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint, Matrix.IsAdjointPair]
  constructor <;> intro h
  · simpa using congr_arg (fun B => u⁻¹ • B) h
  · simp [h]

中文:
定理 mem_skewAdjointMatricesLieSubalgebra_unit_smul
  条件: (u : Rˣ) (J A : 矩阵 n n R)
  证明: by
  change A in skewAdjointMatricesSubmodule (u • J) ↔ A in skewAdjointMatricesSubmodule J
  simp only [mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint, Matrix.IsAdjointPair]
  constructor <;> intro h
  · simpa using congr_arg (fun B => u⁻¹ • B) h
  · simp [h]

Depends on / 依赖: IsAdjointPair, IsSkewAdjoint, Matrix, Matrix.IsAdjointPair, Matrix.IsSkewAdjoint, congr_arg, mem_skewAdjointMatricesSubmodule, skewAdjointMatricesSubmodule
-/
theorem mem_skewAdjointMatricesLieSubalgebra_unit_smul (u : Rˣ) (J A : Matrix n n R) :
    A in skewAdjointMatricesLieSubalgebra (u • J) ↔ A in skewAdjointMatricesLieSubalgebra J := by
  change A in skewAdjointMatricesSubmodule (u • J) ↔ A in skewAdjointMatricesSubmodule J
  simp only [mem_skewAdjointMatricesSubmodule, Matrix.IsSkewAdjoint, Matrix.IsAdjointPair]
  constructor <;> intro h
  · simpa using congr_arg (fun B => u⁻¹ • B) h
  · simp [h]

end SkewAdjointMatrices
