/-
Copyright (c) 2022 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
module

public import Mathlib.Algebra.Star.UnitaryStarAlgAut
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Eigenspace.Matrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.LinearAlgebra.Matrix.Rank

/-! # Spectral theory of Hermitian matrices

This file proves the spectral theorem for matrices. The proof of the spectral theorem is based on
the spectral theorem for linear maps (`LinearMap.IsSymmetric.eigenvectorBasis_apply_self_apply`).

## Tags

spectral theorem, diagonalization theorem -/

@[expose] public section

open WithLp

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
variable {A B : Matrix n n 𝕜}

/-
**Matrix.finite_real_spectrum** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：finite_real_spectrum [DecidableEq n] : (spectrum Real A).Finite
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `spectrum.preimage_algebraMap`：preimage_algebraMap (S : Type*) {R A : Typ
e*} [CommSemiring R] [CommSemiring S] [Ring A] [Algebra R S] [Algebra R A] [Alge
bra S A] [IsScalar…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Set.Finite.preimage`：∀ {α : Type u} {β : Type v} {f : α → β} {s : Set β}
, Set.InjOn f (f ⁻¹' s) → s.Finite → (f ⁻¹' s).Finite
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Matrix.finite_spectrum`：Matrix.finite_spectrum (A : Matrix n n R) : Set.
Finite (spectrum R A)
-/
lemma finite_real_spectrum [DecidableEq n] : (spectrum ℝ A).Finite := by
  rw [← spectrum.preimage_algebraMap 𝕜]
  exact A.finite_spectrum.preimage (FaithfulSMul.algebraMap_injective ℝ 𝕜).injOn
/-
**Matrix.** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq n] : Finite (spectrum ℝ A) := A.finite_real_spectrum

/-- The spectrum of a matrix `A` coincides with the spectrum of `toLpLin p p A`. -/
/-
**Matrix.spectrum_toLpLin** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：spectrum_toLpLin [DecidableEq n] (p : ENNReal) : spectrum 𝕜 (toLpLin p p A
) = spectrum 𝕜 A
参数：p : ENNReal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.spectrum_eq`：AlgEquiv.spectrum_eq {F R A B : Type*} [CommSemiri
ng R] [Ring A] [Ring B] [Algebra R A] [Algebra R B] [EquivLike F A B] [AlgEquivC
lass F R A…
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
The spectrum of a matrix `A` coincides with the spectrum of `toLpLin p p A`.
-/
theorem spectrum_toLpLin [DecidableEq n] (p : ENNReal) :
    spectrum 𝕜 (toLpLin p p A) = spectrum 𝕜 A :=
  AlgEquiv.spectrum_eq (Matrix.toLinAlgEquiv (PiLp.basisFun p 𝕜 n)) _

/-- The spectrum of a matrix `A` coincides with the spectrum of `toEuclideanLin A`. -/
@[deprecated spectrum_toLpLin (since := "2026-01-21")]
/-
**Matrix.spectrum_toEuclideanLin** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：spectrum_toEuclideanLin [DecidableEq n] : spectrum 𝕜 (toEuclideanLin A) = 
spectrum 𝕜 A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.spectrum_toLpLin`：spectrum_toLpLin [DecidableEq n] (p : ENNReal) 
: spectrum 𝕜 (toLpLin p p A) = spectrum 𝕜 A
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)

--- 原说明 ---
The spectrum of a matrix `A` coincides with the spectrum of `toEuclideanLin A`.
-/
theorem spectrum_toEuclideanLin [DecidableEq n] : spectrum 𝕜 (toEuclideanLin A) = spectrum 𝕜 A :=
  spectrum_toLpLin 2

namespace IsHermitian

section DecidableEq

variable [DecidableEq n]
variable (hA : A.IsHermitian) (hB : B.IsHermitian)

/-- The eigenvalues of a Hermitian matrix, indexed by `Fin (Fintype.card n)` where `n` is the index
type of the matrix. -/
/-
**Matrix.IsHermitian.eigenvalues** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.IsHermitian`。
形式化陈述：eigenvalues : n -> Real
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The eigenvalues of a Hermitian matrix, indexed by `Fin (Fintype.card n)` where `
n` is the index
type of the matrix.
-/
noncomputable def eigenvalues₀ : Fin (Fintype.card n) → ℝ :=
  (isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues finrank_euclideanSpace
/-
**Matrix.IsHermitian.eigenvalues** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.IsHermitian`。
形式化陈述：eigenvalues : n -> Real
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma eigenvalues₀_antitone : Antitone hA.eigenvalues₀ :=
  LinearMap.IsSymmetric.eigenvalues_antitone ..

/-- The eigenvalues of a Hermitian matrix, reusing the index `n` of the matrix entries. -/
/-
**Matrix.IsHermitian.eigenvalues** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.IsHermitian`。
形式化陈述：eigenvalues : n -> Real
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The eigenvalues of a Hermitian matrix, reusing the index `n` of the matrix entri
es.
-/
noncomputable def eigenvalues : n → ℝ := fun i =>
  hA.eigenvalues₀ <| (Fintype.equivOfCardEq (Fintype.card_fin _)).symm i

/-- A choice of an orthonormal basis of eigenvectors of a Hermitian matrix. -/
/-
**Matrix.IsHermitian.eigenvectorBasis** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.IsHermit
ian`。
形式化陈述：eigenvectorBasis : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `finrank_euclideanSpace`：finrank_euclideanSpace : Module.finrank 𝕜 (Eucli
deanSpace 𝕜 ι) = Fintype.card ι

--- 原说明 ---
A choice of an orthonormal basis of eigenvectors of a Hermitian matrix.
-/
noncomputable def eigenvectorBasis : OrthonormalBasis n 𝕜 (EuclideanSpace 𝕜 n) :=
  ((isSymmetric_toEuclideanLin_iff.mpr hA).eigenvectorBasis finrank_euclideanSpace).reindex
    (Fintype.equivOfCardEq (Fintype.card_fin _))
/-
**Matrix.IsHermitian.mulVec_eigenvectorBasis** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.I
sHermitian`。
形式化陈述：mulVec_eigenvectorBasis (j : n) : A *ᵥ ⇑(hA.eigenvectorBasis j) = (hA.eige
nvalues j) • ⇑(hA.eigenvectorBasis j)
参数：j : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `finrank_euclideanSpace`：finrank_euclideanSpace : Module.finrank 𝕜 (Eucli
deanSpace 𝕜 ι) = Fintype.card ι
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrthonormalBasis.reindex_apply`：∀ {ι : Type u_1} {ι' : Type u_2} {𝕜 : Ty
pe u_3} [inst : RCLike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst
_2 : InnerProductSpa…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `RCLike.real_smul_eq_coe_smul`：real_smul_eq_coe_smul [AddCommGroup E] [Mo
dule K E] [Module Real E] [IsScalarTower Real K E] (r : Real) (x : E) : r • x = 
(r : K) • x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Matrix.isSymmetric_toEuclideanLin_iff`：isSymmetric_toEuclideanLin_iff [F
intype n] [DecidableEq n] : A.toEuclideanLin.IsSymmetric ↔ A.IsHermitian
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `LinearMap.IsSymmetric.apply_eigenvectorBasis`：apply_eigenvectorBasis (hT
 : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (i : Fin n) : T (hT.eigenvectorB
asis hn i) = (hT.eigenvalues hn i …
-/
lemma mulVec_eigenvectorBasis (j : n) :
    A *ᵥ ⇑(hA.eigenvectorBasis j) = (hA.eigenvalues j) • ⇑(hA.eigenvectorBasis j) := by
  simpa only [eigenvectorBasis, OrthonormalBasis.reindex_apply, toLpLin_apply,
    RCLike.real_smul_eq_coe_smul (K := 𝕜)] using!
      congr(⇑$((isSymmetric_toEuclideanLin_iff.mpr hA).apply_eigenvectorBasis
        finrank_euclideanSpace ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm j)))

/-- Eigenvalues of a Hermitian matrix A are in the ℝ spectrum of A. -/
/-
**Matrix.IsHermitian.eigenvalues_mem_spectrum_real** 是 Mathlib 中的一个定理，位于命名空间 `Ma
trix.IsHermitian`。
形式化陈述：eigenvalues_mem_spectrum_real (i : n) : hA.eigenvalues i in spectrum Real 
A
参数：i : n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `spectrum.of_algebraMap_mem`：∀ (S : Type u_1) {R : Type u_2} {A : Type u_
3} [inst : CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Ring A]   [inst_3
 : Algebra R S] …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.spectrum_toLpLin`：spectrum_toLpLin [DecidableEq n] (p : ENNReal) 
: spectrum 𝕜 (toLpLin p p A) = spectrum 𝕜 A
· 使用定理 `Module.End.HasEigenvalue.mem_spectrum`：∀ {R : Type v} {M : Type w} [inst
 : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {f : Mod
ule.End R M} {μ : R}, f.Has…
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `finrank_euclideanSpace`：finrank_euclideanSpace : Module.finrank 𝕜 (Eucli
deanSpace 𝕜 ι) = Fintype.card ι
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `LinearMap.IsSymmetric.hasEigenvalue_eigenvalues`：hasEigenvalue_eigenvalu
es (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (i : Fin n) : HasEigenvalu
e T (hT.eigenvalues hn i)

--- 原说明 ---
Eigenvalues of a Hermitian matrix A are in the ℝ spectrum of A.
-/
theorem eigenvalues_mem_spectrum_real (i : n) : hA.eigenvalues i ∈ spectrum ℝ A := by
  apply spectrum.of_algebraMap_mem 𝕜
  rw [← Matrix.spectrum_toLpLin 2]
  exact LinearMap.IsSymmetric.hasEigenvalue_eigenvalues _ _ _ |>.mem_spectrum

/-- Unitary matrix whose columns are `Matrix.IsHermitian.eigenvectorBasis`. -/
/-
**Matrix.IsHermitian.eigenvectorUnitary** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.IsHerm
itian`。
形式化陈述：eigenvectorUnitary {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] {A : Mat
rix n n 𝕜} [DecidableEq n] (hA : Matrix.IsHermitian A) : Matrix.unitaryGroup n 𝕜
参数：hA : Matrix.IsHermitian A。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)

--- 原说明 ---
Unitary matrix whose columns are `Matrix.IsHermitian.eigenvectorBasis`.
-/
noncomputable def eigenvectorUnitary {𝕜 : Type*} [RCLike 𝕜] {n : Type*}
    [Fintype n] {A : Matrix n n 𝕜} [DecidableEq n] (hA : Matrix.IsHermitian A) :
    Matrix.unitaryGroup n 𝕜 :=
  ⟨(EuclideanSpace.basisFun n 𝕜).toBasis.toMatrix (hA.eigenvectorBasis).toBasis,
    (EuclideanSpace.basisFun n 𝕜).toMatrix_orthonormalBasis_mem_unitary (eigenvectorBasis hA)⟩
/-
**Matrix.IsHermitian.eigenvectorUnitary_coe** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.Is
Hermitian`。
形式化陈述：eigenvectorUnitary_coe {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] {A :
 Matrix n n 𝕜} [DecidableEq n] (hA : Matrix.IsHermitian A) : eigenvectorUnitary 
hA = (EuclideanSpace.basisFun n 𝕜).toBasis.toMatrix (hA.eigenvectorBasis).toBasi
s
参数：hA : Matrix.IsHermitian A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eigenvectorUnitary_coe {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
    {A : Matrix n n 𝕜} [DecidableEq n] (hA : Matrix.IsHermitian A) :
    eigenvectorUnitary hA =
      (EuclideanSpace.basisFun n 𝕜).toBasis.toMatrix (hA.eigenvectorBasis).toBasis :=
  rfl

@[simp]
/-
**Matrix.IsHermitian.eigenvectorUnitary_transpose_apply** 是 Mathlib 中的一个定理，位于命名空
间 `Matrix.IsHermitian`。
形式化陈述：eigenvectorUnitary_transpose_apply (j : n) : (eigenvectorUnitary hA)ᵀ j = 
⇑(hA.eigenvectorBasis j)
参数：j : n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eigenvectorUnitary_transpose_apply (j : n) :
    (eigenvectorUnitary hA)ᵀ j = ⇑(hA.eigenvectorBasis j) :=
  rfl

@[simp]
/-
**Matrix.IsHermitian.eigenvectorUnitary_col_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matrix
.IsHermitian`。
形式化陈述：eigenvectorUnitary_col_eq (j : n) : Matrix.col (eigenvectorUnitary hA) j =
 ⇑(hA.eigenvectorBasis j)
参数：j : n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eigenvectorUnitary_col_eq (j : n) :
    Matrix.col (eigenvectorUnitary hA) j = ⇑(hA.eigenvectorBasis j) :=
  rfl

@[simp]
/-
**Matrix.IsHermitian.eigenvectorUnitary_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.
IsHermitian`。
形式化陈述：eigenvectorUnitary_apply (i j : n) : eigenvectorUnitary hA i j = ⇑(hA.eige
nvectorBasis j) i
参数：i j : n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eigenvectorUnitary_apply (i j : n) :
    eigenvectorUnitary hA i j = ⇑(hA.eigenvectorBasis j) i :=
  rfl
/-
**Matrix.IsHermitian.eigenvectorUnitary_mulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix
.IsHermitian`。
形式化陈述：eigenvectorUnitary_mulVec (j : n) : eigenvectorUnitary hA *ᵥ Pi.single j 1
 = ⇑(hA.eigenvectorBasis j)
参数：j : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.mulVec_single_one`：mulVec_single_one [Fintype n] [DecidableEq n] 
[NonAssocSemiring R] (M : Matrix m n R) (j : n) : M *ᵥ Pi.single j 1 = M.col j
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eigenvectorUnitary_mulVec (j : n) :
    eigenvectorUnitary hA *ᵥ Pi.single j 1 = ⇑(hA.eigenvectorBasis j) := by
  simp_rw [mulVec_single_one, eigenvectorUnitary_col_eq]
/-
**Matrix.IsHermitian.star_eigenvectorUnitary_mulVec** 是 Mathlib 中的一个定理，位于命名空间 `M
atrix.IsHermitian`。
形式化陈述：star_eigenvectorUnitary_mulVec (j : n) : (star (eigenvectorUnitary hA : Ma
trix n n 𝕜)) *ᵥ ⇑(hA.eigenvectorBasis j) = Pi.single j 1
参数：j : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.IsHermitian.eigenvectorUnitary_mulVec`：eigenvectorUnitary_mulVec 
(j : n) : eigenvectorUnitary hA *ᵥ Pi.single j 1 = ⇑(hA.eigenvectorBasis j)
· 使用定理 `Matrix.mulVec_mulVec`：mulVec_mulVec [Fintype n] [Fintype o] (v : o -> α)
 (M : Matrix m n α) (N : Matrix n o α) : M *ᵥ N *ᵥ v = (M * N) *ᵥ v
· 使用定理 `Unitary.coe_star_mul_self`：coe_star_mul_self (U : unitary R) : (star U :
 R) * U = 1
· 使用定理 `Matrix.one_mulVec`：one_mulVec (v : m -> α) : 1 *ᵥ v = v
-/
theorem star_eigenvectorUnitary_mulVec (j : n) :
    (star (eigenvectorUnitary hA : Matrix n n 𝕜)) *ᵥ ⇑(hA.eigenvectorBasis j) = Pi.single j 1 := by
  rw [← eigenvectorUnitary_mulVec, mulVec_mulVec, Unitary.coe_star_mul_self, one_mulVec]

open Unitary

/-- Unitary diagonalization of a Hermitian matrix. -/
/-
**Matrix.IsHermitian.conjStarAlgAut_star_eigenvectorUnitary** 是 Mathlib 中的一个定理，位
于命名空间 `Matrix.IsHermitian`。
形式化陈述：conjStarAlgAut_star_eigenvectorUnitary : conjStarAlgAut 𝕜 _ (star hA.eigen
vectorUnitary) A = diagonal (RCLike.ofReal ∘ hA.eigenvalues)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Unitary.conjStarAlgAut_star_apply`：conjStarAlgAut_star_apply (u : unitar
y R) (x : R) : conjStarAlgAut S R (star u) x = (star u : R) * x * u
· 使用定理 `EuclideanSpace.basisFun_apply`：basisFun_apply [DecidableEq ι] (i : ι) : 
basisFun ι 𝕜 i = EuclideanSpace.single i 1
· 使用定理 `Matrix.IsHermitian.eigenvectorUnitary_mulVec`：eigenvectorUnitary_mulVec 
(j : n) : eigenvectorUnitary hA *ᵥ Pi.single j 1 = ⇑(hA.eigenvectorBasis j)
· 使用引理 `Matrix.IsHermitian.mulVec_eigenvectorBasis`：mulVec_eigenvectorBasis (j :
 n) : A *ᵥ ⇑(hA.eigenvectorBasis j) = (hA.eigenvalues j) • ⇑(hA.eigenvectorBasis
 j)
· 使用定理 `RCLike.real_smul_eq_coe_smul`：real_smul_eq_coe_smul [AddCommGroup E] [Mo
dule K E] [Module Real E] [IsScalarTower Real K E] (r : Real) (x : E) : r • x = 
(r : K) • x
· 使用定理 `Matrix.mulVec_smul`：mulVec_smul [Fintype n] [DistribSMul R α] [SMulCommC
lass R α α] (M : Matrix m n α) (b : R) (v : n -> α) : M *ᵥ (b • v) = b • M *ᵥ v
· 使用定理 `Matrix.IsHermitian.star_eigenvectorUnitary_mulVec`：star_eigenvectorUnita
ry_mulVec (j : n) : (star (eigenvectorUnitary hA : Matrix n n 𝕜)) *ᵥ ⇑(hA.eigenv
ectorBasis j) = Pi.single j 1
· 使用定理 `Matrix.diagonal_mulVec_single`：diagonal_mulVec_single [Fintype n] [Decid
ableEq n] [NonUnitalNonAssocSemiring R] (v : n -> R) (j : n) (x : R) : diagonal 
v *ᵥ Pi.single j x …
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `PiLp.ext`：∀ {p : ENNReal} {ι : Type u_1} {α : ι → Type u_2} {x y : PiLp 
p α}, (∀ (i : ι), x.ofLp i = y.ofLp i) → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `PiLp.single_apply`：single_apply [Zero 𝕜] (i : ι) (a : 𝕜) (j : ι) : (sing
le p i a : PiLp p (fun _ => 𝕜)) j = ite (j = i) a 0
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Unitary diagonalization of a Hermitian matrix.
-/
theorem conjStarAlgAut_star_eigenvectorUnitary :
    conjStarAlgAut 𝕜 _ (star hA.eigenvectorUnitary) A =
      diagonal (RCLike.ofReal ∘ hA.eigenvalues) := by
  apply Matrix.toEuclideanLin.injective <| (EuclideanSpace.basisFun n 𝕜).toBasis.ext fun i ↦ ?_
  simp only [conjStarAlgAut_star_apply, toLpLin_apply, OrthonormalBasis.coe_toBasis,
    EuclideanSpace.basisFun_apply, PiLp.ofLp_single, ← mulVec_mulVec,
    eigenvectorUnitary_mulVec, ← mulVec_mulVec, mulVec_eigenvectorBasis,
    Matrix.diagonal_mulVec_single, mulVec_smul, star_eigenvectorUnitary_mulVec,
    RCLike.real_smul_eq_coe_smul (K := 𝕜), WithLp.toLp_smul, PiLp.toLp_single,
    Function.comp_apply, mul_one]
  apply PiLp.ext fun j ↦ ?_
  simp only [PiLp.smul_apply, PiLp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]

/-- **Diagonalization theorem**, **spectral theorem** for matrices; A Hermitian matrix can be
diagonalized by a change of basis. For the spectral theorem on linear maps, see
`LinearMap.IsSymmetric.eigenvectorBasis_apply_self_apply`. -/
/-
**Matrix.IsHermitian.spectral_theorem** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsHermit
ian`。
形式化陈述：spectral_theorem : A = conjStarAlgAut 𝕜 _ hA.eigenvectorUnitary (diagonal 
(RCLike.ofReal ∘ hA.eigenvalues))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.IsHermitian.conjStarAlgAut_star_eigenvectorUnitary`：conjStarAlgAu
t_star_eigenvectorUnitary : conjStarAlgAut 𝕜 _ (star hA.eigenvectorUnitary) A = 
diagonal (RCLike.ofReal ∘ hA.eigenvalues)
· 使用定理 `Unitary.conjStarAlgAut_mul_apply`：conjStarAlgAut_mul_apply (u₁ u₂ : unit
ary R) (x : R) : conjStarAlgAut S R (u₁ * u₂) x = conjStarAlgAut S R u₁ (conjSta
rAlgAut S R u₂ x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Unitary.mul_star_self`：mul_star_self (U : unitary R) : U * star U = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
**Diagonalization theorem**, **spectral theorem** for matrices; A Hermitian matr
ix can be
diagonalized by a change of basis. For the spectral theorem on linear maps, see
`LinearMap.IsSymmetric.eigenvectorBasis_apply_self_apply`.
-/
theorem spectral_theorem :
    A = conjStarAlgAut 𝕜 _ hA.eigenvectorUnitary (diagonal (RCLike.ofReal ∘ hA.eigenvalues)) := by
  rw [← conjStarAlgAut_star_eigenvectorUnitary, ← conjStarAlgAut_mul_apply]
  simp
/-
**Matrix.IsHermitian.eigenvalues_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsHermitia
n`。
形式化陈述：eigenvalues_eq (i : n) : (hA.eigenvalues i) = RCLike.re (dotProduct (star 
⇑(hA.eigenvectorBasis i)) (A *ᵥ ⇑(hA.eigenvectorBasis i)))
参数：i : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dotProduct_comm`：dotProduct_comm [AddCommMonoid α] [CommMagma α] (v w : 
m -> α) : v ⬝ᵥ w = w ⬝ᵥ v
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Matrix.IsHermitian.mulVec_eigenvectorBasis`：mulVec_eigenvectorBasis (j :
 n) : A *ᵥ ⇑(hA.eigenvectorBasis j) = (hA.eigenvalues j) • ⇑(hA.eigenvectorBasis
 j)
· 使用定理 `smul_dotProduct`：smul_dotProduct [IsScalarTower R α α] (x : R) (v w : m 
-> α) : x • v ⬝ᵥ w = x • (v ⬝ᵥ w)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `OrthonormalBasis.orthonormal`：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : RC
Like 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductS
pace 𝕜 E] [inst_3 …
· 使用定理 `algebraMap.coe_one`：coe_one : (↑(1 : R) : A) = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `RCLike.smul_re`：smul_re (r : Real) (z : K) : re (r • z) = r * re z
· 使用定理 `RCLike.one_re`：one_re : re (1 : K) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eigenvalues_eq (i : n) :
    (hA.eigenvalues i) = RCLike.re (dotProduct (star ⇑(hA.eigenvectorBasis i))
    (A *ᵥ ⇑(hA.eigenvectorBasis i))) := by
  rw [dotProduct_comm]
  simp only [mulVec_eigenvectorBasis, smul_dotProduct, ← EuclideanSpace.inner_eq_star_dotProduct,
    inner_self_eq_norm_sq_to_K, RCLike.smul_re, hA.eigenvectorBasis.orthonormal.1 i,
    mul_one, algebraMap.coe_one, one_pow, RCLike.one_re]

open Polynomial in
/-
**Matrix.IsHermitian.charpoly_eq** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.IsHermitian`。
形式化陈述：charpoly_eq : A.charpoly = ∏ i, (X - C (hA.eigenvalues i : 𝕜))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.IsHermitian.spectral_theorem`：spectral_theorem : A = conjStarAlgA
ut 𝕜 _ hA.eigenvectorUnitary (diagonal (RCLike.ofReal ∘ hA.eigenvalues))
· 使用定理 `Unitary.conjStarAlgAut_apply`：∀ {S : Type u_1} {R : Type u_2} [inst : Se
miring R] [inst_1 : StarMul R] [inst_2 : SMul S R]   [inst_3 : IsScalarTower S R
 R] [inst_4 : SMul…
· 使用定理 `Matrix.charpoly_mul_comm`：charpoly_mul_comm (A B : Matrix n n R) : (A * 
B).charpoly = (B * A).charpoly
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.charpoly.congr_simp`：∀ {R : Type u_1} [inst : CommRing R] {n : Ty
pe u_4} {inst_1 : DecidableEq n} [inst_2 : DecidableEq n]   [inst_3 : Fintype n]
 (M M_1 : Matrix…
· 使用定理 `Unitary.star_mul_self_of_mem`：star_mul_self_of_mem {U : R} (hU : U in un
itary R) : star U * U = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Matrix.charpoly_diagonal`：charpoly_diagonal (d : n -> R) : charpoly (dia
gonal d) = ∏ i, (X - C (d i))
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma charpoly_eq : A.charpoly = ∏ i, (X - C (hA.eigenvalues i : 𝕜)) := by
  conv_lhs => rw [hA.spectral_theorem, conjStarAlgAut_apply, charpoly_mul_comm, ← mul_assoc]
  simp [charpoly_diagonal]
/-
**Matrix.IsHermitian.roots_charpoly_eq_eigenvalues** 是 Mathlib 中的一个引理，位于命名空间 `Ma
trix.IsHermitian`。
形式化陈述：roots_charpoly_eq_eigenvalues : A.charpoly.roots = Multiset.map (RCLike.of
Real ∘ hA.eigenvalues) Finset.univ.val
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matrix.IsHermitian.charpoly_eq`：charpoly_eq : A.charpoly = ∏ i, (X - C (
hA.eigenvalues i : 𝕜))
· 使用定理 `Polynomial.roots_prod`：roots_prod {ι : Type*} (f : ι -> R[X]) (s : Finse
t ι) : s.prod f != 0 -> (s.prod f).roots = s.val.bind fun i => roots (f i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.bind_congr`：bind_congr {f g : α -> Multiset β} {m : Multiset α}
 : (forall a in m, f a = g a) -> bind m f = bind m g
· 使用定理 `Polynomial.roots_X_sub_C`：roots_X_sub_C (r : R) : roots (X - C r) = {r}
· 使用定理 `Multiset.bind_singleton`：bind_singleton (f : α -> β) : (s.bind fun x => 
({f x} : Multiset β)) = map f s
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma roots_charpoly_eq_eigenvalues :
    A.charpoly.roots = Multiset.map (RCLike.ofReal ∘ hA.eigenvalues) Finset.univ.val := by
  rw [hA.charpoly_eq, Polynomial.roots_prod]
  · simp
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

set_option backward.isDefEq.respectTransparency.types false in
/-
**Matrix.IsHermitian.roots_charpoly_eq_eigenvalues** 是 Mathlib 中的一个引理，位于命名空间 `Ma
trix.IsHermitian`。
形式化陈述：roots_charpoly_eq_eigenvalues : A.charpoly.roots = Multiset.map (RCLike.of
Real ∘ hA.eigenvalues) Finset.univ.val
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matrix.IsHermitian.charpoly_eq`：charpoly_eq : A.charpoly = ∏ i, (X - C (
hA.eigenvalues i : 𝕜))
· 使用定理 `Polynomial.roots_prod`：roots_prod {ι : Type*} (f : ι -> R[X]) (s : Finse
t ι) : s.prod f != 0 -> (s.prod f).roots = s.val.bind fun i => roots (f i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.bind_congr`：bind_congr {f g : α -> Multiset β} {m : Multiset α}
 : (forall a in m, f a = g a) -> bind m f = bind m g
· 使用定理 `Polynomial.roots_X_sub_C`：roots_X_sub_C (r : R) : roots (X - C r) = {r}
· 使用定理 `Multiset.bind_singleton`：bind_singleton (f : α -> β) : (s.bind fun x => 
({f x} : Multiset β)) = map f s
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma roots_charpoly_eq_eigenvalues₀ :
    A.charpoly.roots = Multiset.map (RCLike.ofReal ∘ hA.eigenvalues₀) Finset.univ.val := by
  rw [hA.roots_charpoly_eq_eigenvalues]
  simp only [← Multiset.map_map, eigenvalues, ← Function.comp_apply (f := hA.eigenvalues₀)]
  simp
/-
**Matrix.IsHermitian.sort_roots_charpoly_eq_eigenvalues** 是 Mathlib 中的一个引理，位于命名空
间 `Matrix.IsHermitian`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sort_roots_charpoly_eq_eigenvalues₀ :
    (A.charpoly.roots.map RCLike.re).sort (· ≥ ·) = List.ofFn hA.eigenvalues₀ := by
  simp_rw [hA.roots_charpoly_eq_eigenvalues₀, Fin.univ_val_map, Multiset.map_coe, List.map_ofFn,
    Function.comp_def, RCLike.ofReal_re, Multiset.coe_sort]
  apply List.mergeSort_of_pairwise
  simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
  exact (eigenvalues₀_antitone hA).sortedGE_ofFn
/-
**Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff** 是 Mathlib 中的一个引理，位于命名空间 `M
atrix.IsHermitian`。
形式化陈述：eigenvalues_eq_eigenvalues_iff : hA.eigenvalues = hB.eigenvalues ↔ A.charp
oly = B.charpoly
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matrix.IsHermitian.charpoly_eq`：charpoly_eq : A.charpoly = ∏ i, (X - C (
hA.eigenvalues i : 𝕜))
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTransGe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x2 ≤ x1
· 使用定理 `instAntisymmGe`：∀ {α : Type u} [inst : PartialOrder α], Std.Antisymm fun
 x1 x2 => x2 ≤ x1
· 使用定理 `LE.total'`：∀ {α : Type u} [inst : LinearOrder α], Std.Total fun x1 x2 =>
 x2 ≤ x1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.sort.congr_simp`：∀ {α : Type u_1} (s s_1 : Multiset α),   s = s
_1 →     ∀ (r r_1 : α → α → Prop) (e_r : r = r_1) {inst : DecidableRel r} [inst_
1 : DecidableR…
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Polynomial.roots.congr_simp`：∀ {R : Type u} [inst : CommRing R] [inst_1 
: IsDomain R] (p p_1 : Polynomial R), p = p_1 → p.roots = p_1.roots
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma eigenvalues_eq_eigenvalues_iff :
    hA.eigenvalues = hB.eigenvalues ↔ A.charpoly = B.charpoly := by
  constructor <;> intro h
  · rw [hA.charpoly_eq, hB.charpoly_eq, h]
  · suffices hA.eigenvalues₀ = hB.eigenvalues₀ by unfold eigenvalues; rw [this]
    simp_rw [← List.ofFn_inj, ← sort_roots_charpoly_eq_eigenvalues₀, h]
/-
**Matrix.IsHermitian.splits_charpoly** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsHermiti
an`。
形式化陈述：splits_charpoly (hA : A.IsHermitian) : A.charpoly.Splits
参数：hA : A.IsHermitian。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.splits_iff_card_roots`：splits_iff_card_roots : Splits f ↔ f.r
oots.card = f.natDegree
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matrix.IsHermitian.roots_charpoly_eq_eigenvalues`：roots_charpoly_eq_eige
nvalues : A.charpoly.roots = Multiset.map (RCLike.ofReal ∘ hA.eigenvalues) Finse
t.univ.val
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.card_map`：card_map (f : α -> β) (s) : card (map f s) = card s
· 使用定理 `Matrix.charpoly_natDegree_eq_dim`：∀ {R : Type u} [inst : CommRing R] {n 
: Type v} [inst_1 : DecidableEq n] [inst_2 : Fintype n] [Nontrivial R]   (M : Ma
trix n n R), M.charpol…
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem splits_charpoly (hA : A.IsHermitian) : A.charpoly.Splits :=
  Polynomial.splits_iff_card_roots.mpr (by simp [hA.roots_charpoly_eq_eigenvalues])

/-- The determinant of a Hermitian matrix is the product of its eigenvalues. -/
/-
**Matrix.IsHermitian.det_eq_prod_eigenvalues** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.I
sHermitian`。
形式化陈述：det_eq_prod_eigenvalues : det A = ∏ i, (hA.eigenvalues i : 𝕜)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Matrix.det_eq_prod_roots_charpoly_of_splits`：det_eq_prod_roots_charpoly_
of_splits [IsDomain R] (hAps : B.charpoly.Splits) : B.det = (Matrix.charpoly B).
roots.prod
· 使用定理 `Matrix.IsHermitian.splits_charpoly`：splits_charpoly (hA : A.IsHermitian)
 : A.charpoly.Splits
· 使用引理 `Matrix.IsHermitian.roots_charpoly_eq_eigenvalues`：roots_charpoly_eq_eige
nvalues : A.charpoly.roots = Multiset.map (RCLike.ofReal ∘ hA.eigenvalues) Finse
t.univ.val
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The determinant of a Hermitian matrix is the product of its eigenvalues.
-/
theorem det_eq_prod_eigenvalues : det A = ∏ i, (hA.eigenvalues i : 𝕜) := by
  simp [det_eq_prod_roots_charpoly_of_splits hA.splits_charpoly, hA.roots_charpoly_eq_eigenvalues]

/-- rank of a Hermitian matrix is the rank of after diagonalization by the eigenvector unitary -/
/-
**Matrix.IsHermitian.rank_eq_rank_diagonal** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.IsH
ermitian`。
形式化陈述：rank_eq_rank_diagonal : A.rank = (diagonal hA.eigenvalues).rank
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.IsHermitian.spectral_theorem`：spectral_theorem : A = conjStarAlgA
ut 𝕜 _ hA.eigenvectorUnitary (diagonal (RCLike.ofReal ∘ hA.eigenvalues))
· 使用定理 `Unitary.conjStarAlgAut_apply`：∀ {S : Type u_1} {R : Type u_2} [inst : Se
miring R] [inst_1 : StarMul R] [inst_2 : SMul S R]   [inst_3 : IsScalarTower S R
 R] [inst_4 : SMul…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Unitary.coe_star`：coe_star {U : unitary R} : ↑(star U) = (star U : R)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Matrix.rank_mul_eq_left_of_isUnit_det`：rank_mul_eq_left_of_isUnit_det {R
 : Type*} [CommRing R] [DecidableEq n] (A : Matrix n n R) (B : Matrix m n R) (hA
 : IsUnit A.det) : (B * A).…
· 使用引理 `Matrix.rank_mul_eq_right_of_isUnit_det`：rank_mul_eq_right_of_isUnit_det 
{R : Type*} [CommRing R] [Fintype m] [DecidableEq m] (A : Matrix m m R) (B : Mat
rix m n R) (hA : IsUnit A.de…
· 使用定理 `Matrix.rank_diagonal`：rank_diagonal [Fintype m] [DecidableEq m] [Decidab
leEq R] (w : m -> R) : (diagonal w).rank = Fintype.card {i // (w i) != 0}
· 使用定理 `Fintype.card_congr'`：card_congr' {α β} [Fintype α] [Fintype β] (h : α = 
β) : card α = card β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Fintype.card_subtype_compl`：Fintype.card_subtype_compl [Fintype α] (p : 
α -> Prop) [Fintype { x // p x }] [Fintype { x // ¬p x }] : Fintype.card { x // 
¬p x } = Fintype…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
rank of a Hermitian matrix is the rank of after diagonalization by the eigenvect
or unitary
-/
lemma rank_eq_rank_diagonal : A.rank = (diagonal hA.eigenvalues).rank := by
  conv_lhs => rw [hA.spectral_theorem, conjStarAlgAut_apply, ← coe_star]
  simp [-isUnit_iff_ne_zero, -coe_star, rank_diagonal]

/-- rank of a Hermitian matrix is the number of nonzero eigenvalues of the Hermitian matrix -/
/-
**Matrix.IsHermitian.rank_eq_card_non_zero_eigs** 是 Mathlib 中的一个引理，位于命名空间 `Matri
x.IsHermitian`。
形式化陈述：rank_eq_card_non_zero_eigs : A.rank = Fintype.card {i // hA.eigenvalues i 
!= 0}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matrix.IsHermitian.rank_eq_rank_diagonal`：rank_eq_rank_diagonal : A.rank
 = (diagonal hA.eigenvalues).rank
· 使用定理 `Matrix.rank_diagonal`：rank_diagonal [Fintype m] [DecidableEq m] [Decidab
leEq R] (w : m -> R) : (diagonal w).rank = Fintype.card {i // (w i) != 0}

--- 原说明 ---
rank of a Hermitian matrix is the number of nonzero eigenvalues of the Hermitian
 matrix
-/
lemma rank_eq_card_non_zero_eigs : A.rank = Fintype.card {i // hA.eigenvalues i ≠ 0} := by
  rw [rank_eq_rank_diagonal hA, Matrix.rank_diagonal]

/-- The spectrum of a Hermitian matrix is the range of its eigenvalues under `RCLike.ofReal`. -/
/-
**Matrix.IsHermitian.spectrum_eq_image_range** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.I
sHermitian`。
形式化陈述：spectrum_eq_image_range : spectrum 𝕜 A = RCLike.ofReal '' Set.range hA.eig
envalues
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.IsHermitian.spectral_theorem`：spectral_theorem : A = conjStarAlgA
ut 𝕜 _ hA.eigenvectorUnitary (diagonal (RCLike.ofReal ∘ hA.eigenvalues))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Unitary.spectrum_star_right_conjugate`：spectrum_star_right_conjugate {a 
: A} {U : unitary A} : spectrum R (U * a * (star U : A)) = spectrum R a
· 使用定理 `spectrum_diagonal`：∀ {R : Type u_1} {n : Type u_2} [inst : DecidableEq n
] [inst_1 : Fintype n] [inst_2 : Field R] (d : n → R),   spectrum R (Matrix.diag
onal d)…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The spectrum of a Hermitian matrix is the range of its eigenvalues under `RCLike
.ofReal`.
-/
theorem spectrum_eq_image_range :
    spectrum 𝕜 A = RCLike.ofReal '' Set.range hA.eigenvalues := Set.ext fun x => by
  conv_lhs => rw [hA.spectral_theorem]
  simp

/-- The `ℝ`-spectrum of a Hermitian matrix over `RCLike` field is the range of the eigenvalue
function. -/
/-
**Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues** 是 Mathlib 中的一个定理，位于命名空
间 `Matrix.IsHermitian`。
形式化陈述：spectrum_real_eq_range_eigenvalues : spectrum Real A = Set.range hA.eigenv
alues
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.IsHermitian.spectral_theorem`：spectral_theorem : A = conjStarAlgA
ut 𝕜 _ hA.eigenvectorUnitary (diagonal (RCLike.ofReal ∘ hA.eigenvalues))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `spectrum.algebraMap_mem_iff`：algebraMap_mem_iff (S : Type*) {R A : Type*
} [CommSemiring R] [CommSemiring S] [Ring A] [Algebra R S] [Algebra R A] [Algebr
a S A] [IsScalarT…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Unitary.spectrum_star_right_conjugate`：spectrum_star_right_conjugate {a 
: A} {U : unitary A} : spectrum R (U * a * (star U : A)) = spectrum R a
· 使用定理 `spectrum_diagonal`：∀ {R : Type u_1} {n : Type u_2} [inst : DecidableEq n
] [inst_1 : Fintype n] [inst_2 : Field R] (d : n → R),   spectrum R (Matrix.diag
onal d)…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The `ℝ`-spectrum of a Hermitian matrix over `RCLike` field is the range of the e
igenvalue
function.
-/
theorem spectrum_real_eq_range_eigenvalues :
    spectrum ℝ A = Set.range hA.eigenvalues := Set.ext fun x => by
  conv_lhs => rw [hA.spectral_theorem, ← spectrum.algebraMap_mem_iff 𝕜]
  simp

/-- The eigenvalues of a Hermitian matrix `A` are all zero iff `A = 0`. -/
/-
**Matrix.IsHermitian.eigenvalues_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.I
sHermitian`。
形式化陈述：eigenvalues_eq_zero_iff : hA.eigenvalues = 0 ↔ A = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.IsHermitian.spectral_theorem`：spectral_theorem : A = conjStarAlgA
ut 𝕜 _ hA.eigenvectorUnitary (diagonal (RCLike.ofReal ∘ hA.eigenvalues))
· 使用定理 `Pi.comp_zero`：∀ {α : Type u_2} {β : Type u_3} {M : Type u_7} [inst : Zer
o M] (f : M → β), f ∘ 0 = Function.const α (f 0)
· 使用定理 `RCLike.ofReal_zero`：ofReal_zero : ((0 : Real) : K) = 0
· 使用定理 `Function.const_zero`：∀ {α : Type u_2} {M : Type u_7} [inst : Zero M], Fu
nction.const α 0 = 0
· 使用定理 `Pi.zero_def`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zero 
(M i)], 0 = fun x => 0
· 使用定理 `Matrix.diagonal_zero`：diagonal_zero [Zero α] : (diagonal fun _ => 0 : Ma
trix n n α) = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `instAlgEquivClassOfNonUnitalAlgEquivClass`：∀ (F : Type u_1) (R : Type u_
2) (A : Type u_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]  
 [inst_2 : Algebra R A] [inst_3…
· 使用定理 `StarAlgEquiv.instNonUnitalAlgEquivClass`：∀ {R : Type u_2} {A : Type u_3}
 {B : Type u_4} [inst : Add A] [inst_1 : Add B] [inst_2 : Mul A] [inst_3 : Mul B
]   [inst_4 : SMul R A] [inst…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Matrix.IsHermitian.eigenvalues.congr_simp`：∀ {𝕜 : Type u_1} [inst : RCLi
ke 𝕜] {n : Type u_2} [inst_1 : Fintype n] {A A_1 : Matrix n n 𝕜} (e_A : A = A_1)
   {inst_2 : DecidableEq n} [in…
· 使用定理 `Matrix.IsHermitian.eigenvalues_eq`：eigenvalues_eq (i : n) : (hA.eigenval
ues i) = RCLike.re (dotProduct (star ⇑(hA.eigenvectorBasis i)) (A *ᵥ ⇑(hA.eigenv
ectorBasis i)))
· 使用定理 `Matrix.zero_mulVec`：zero_mulVec [Fintype n] (v : n -> α) : (0 : Matrix m
 n α) *ᵥ v = 0
· 使用定理 `dotProduct_zero`：dotProduct_zero : v ⬝ᵥ 0 = 0
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The eigenvalues of a Hermitian matrix `A` are all zero iff `A = 0`.
-/
theorem eigenvalues_eq_zero_iff :
    hA.eigenvalues = 0 ↔ A = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by ext; simp [h, eigenvalues_eq]⟩
  rw [hA.spectral_theorem, h, Pi.comp_zero, RCLike.ofReal_zero, Function.const_zero,
    Pi.zero_def, diagonal_zero, map_zero]

end DecidableEq

/-- A nonzero Hermitian matrix has an eigenvector with nonzero eigenvalue. -/
/-
**Matrix.IsHermitian.exists_eigenvector_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Ma
trix.IsHermitian`。
形式化陈述：exists_eigenvector_of_ne_zero (hA : IsHermitian A) (h_ne : A != 0) : exist
s (v : n -> 𝕜) (t : Real), t != 0 ∧ v != 0 ∧ A *ᵥ v = t • v
参数：hA : IsHermitian A；h_ne : A != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Matrix.IsHermitian.spectral_theorem`：spectral_theorem : A = conjStarAlgA
ut 𝕜 _ hA.eigenvectorUnitary (diagonal (RCLike.ofReal ∘ hA.eigenvalues))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `instAlgEquivClassOfNonUnitalAlgEquivClass`：∀ (F : Type u_1) (R : Type u_
2) (A : Type u_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]  
 [inst_2 : Algebra R A] [inst_3…
· 使用定理 `StarAlgEquiv.instNonUnitalAlgEquivClass`：∀ {R : Type u_2} {A : Type u_3}
 {B : Type u_4} [inst : Add A] [inst_1 : Add B] [inst_2 : Mul A] [inst_3 : Mul B
]   [inst_4 : SMul R A] [inst…
· 使用定理 `Matrix.diagonal_zero`：diagonal_zero [Zero α] : (diagonal fun _ => 0 : Ma
trix n n α) = 0
· 使用定理 `RCLike.ofReal_zero`：ofReal_zero : ((0 : Real) : K) = 0
· 使用定理 `Pi.comp_zero`：∀ {α : Type u_2} {β : Type u_3} {M : Type u_7} [inst : Zer
o M] (f : M → β), f ∘ 0 = Function.const α (f 0)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.ne_iff`：ne_iff {β : α -> Sort*} {f₁ f₂ : forall a, β a} : f₁ !=
 f₂ ↔ exists a, f₁ a != f₂ a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.ne`：∀ {α : Sort u_1} {β : Sort u_2} {a b : α} {c d : β}, (a = b ↔ c 
= d) → (a ≠ b ↔ c ≠ d)
· 使用定理 `WithLp.ofLp_eq_zero`：∀ (p : ENNReal) {V : Type u_4} [inst : AddCommGroup
 V] {x : WithLp p V}, x.ofLp = 0 ↔ x = 0
· 使用定理 `Orthonormal.ne_zero`：Orthonormal.ne_zero {v : ι -> E} (hv : Orthonormal 
𝕜 v) (i : ι) : v i != 0
· 使用定理 `OrthonormalBasis.orthonormal`：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : RC
Like 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductS
pace 𝕜 E] [inst_3 …
· 使用引理 `Matrix.IsHermitian.mulVec_eigenvectorBasis`：mulVec_eigenvectorBasis (j :
 n) : A *ᵥ ⇑(hA.eigenvectorBasis j) = (hA.eigenvalues j) • ⇑(hA.eigenvectorBasis
 j)

--- 原说明 ---
A nonzero Hermitian matrix has an eigenvector with nonzero eigenvalue.
-/
lemma exists_eigenvector_of_ne_zero (hA : IsHermitian A) (h_ne : A ≠ 0) :
    ∃ (v : n → 𝕜) (t : ℝ), t ≠ 0 ∧ v ≠ 0 ∧ A *ᵥ v = t • v := by
  classical
  have : hA.eigenvalues ≠ 0 := by
    contrapose h_ne
    have := hA.spectral_theorem
    rwa [h_ne, Pi.comp_zero, RCLike.ofReal_zero, (by rfl : Function.const n (0 : 𝕜) = fun _ ↦ 0),
      diagonal_zero, map_zero] at this
  obtain ⟨i, hi⟩ := Function.ne_iff.mp this
  exact ⟨_, _, hi, (ofLp_eq_zero 2).ne.2 <| hA.eigenvectorBasis.orthonormal.ne_zero i,
    hA.mulVec_eigenvectorBasis i⟩
/-
**Matrix.IsHermitian.trace_eq_sum_eigenvalues** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.
IsHermitian`。
形式化陈述：trace_eq_sum_eigenvalues [DecidableEq n] (hA : A.IsHermitian) : A.trace = 
∑ i, (hA.eigenvalues i : 𝕜)
参数：hA : A.IsHermitian。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Matrix.trace_eq_sum_roots_charpoly_of_splits`：trace_eq_sum_roots_charpol
y_of_splits [IsDomain R] (hAps : B.charpoly.Splits) : B.trace = (Matrix.charpoly
 B).roots.sum
· 使用定理 `Matrix.IsHermitian.splits_charpoly`：splits_charpoly (hA : A.IsHermitian)
 : A.charpoly.Splits
· 使用引理 `Matrix.IsHermitian.roots_charpoly_eq_eigenvalues`：roots_charpoly_eq_eige
nvalues : A.charpoly.roots = Multiset.map (RCLike.ofReal ∘ hA.eigenvalues) Finse
t.univ.val
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem trace_eq_sum_eigenvalues [DecidableEq n] (hA : A.IsHermitian) :
    A.trace = ∑ i, (hA.eigenvalues i : 𝕜) := by
  simp [trace_eq_sum_roots_charpoly_of_splits hA.splits_charpoly, hA.roots_charpoly_eq_eigenvalues]

end IsHermitian

end Matrix

