/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
module

public import Mathlib.Analysis.InnerProductSpace.Rayleigh
public import Mathlib.Analysis.Normed.Group.Submodule
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.Data.Fin.Tuple.Sort

/-! # Spectral theory of self-adjoint operators

This file covers the spectral theory of self-adjoint operators on an inner product space.

The first part of the file covers general properties, true without any condition on boundedness or
compactness of the operator or finite-dimensionality of the underlying space, notably:
* `LinearMap.IsSymmetric.conj_eigenvalue_eq_self`: the eigenvalues are real
* `LinearMap.IsSymmetric.orthogonalFamily_eigenspaces`: the eigenspaces are orthogonal
* `LinearMap.IsSymmetric.orthogonalComplement_iSup_eigenspaces`: the restriction of the operator to
  the mutual orthogonal complement of the eigenspaces has, itself, no eigenvectors

The second part of the file covers properties of self-adjoint operators in finite dimension.
Letting `T` be a self-adjoint operator on a finite-dimensional inner product space `T`,
* The definition `LinearMap.IsSymmetric.diagonalization` provides a linear isometry equivalence `E`
  to the direct sum of the eigenspaces of `T`.  The theorem
  `LinearMap.IsSymmetric.diagonalization_apply_self_apply` states that, when `T` is transferred via
  this equivalence to an operator on the direct sum, it acts diagonally.
* The definition `LinearMap.IsSymmetric.eigenvectorBasis` provides an orthonormal basis for `E`
  consisting of eigenvectors of `T`, with `LinearMap.IsSymmetric.eigenvalues` giving the
  corresponding list of eigenvalues, as real numbers.  The definition
  `LinearMap.IsSymmetric.eigenvectorBasis` gives the associated linear isometry equivalence
  from `E` to Euclidean space, and the theorem
  `LinearMap.IsSymmetric.eigenvectorBasis_apply_self_apply` states that, when `T` is
  transferred via this equivalence to an operator on Euclidean space, it acts diagonally.
* `LinearMap.IsSymmetric.eigenvalues` gives the eigenvalues in decreasing order.  This is
  done for several reasons: (i) This agrees with the standard convention of listing singular
  values in decreasing order, with the operator norm as the first singular value
  (ii) For positive compact operators on an infinite-dimensional space, one can list the nonzero
  eigenvalues in decreasing (but not increasing) order since they converge to zero. (iii) This
  simplifies several theorem statements. For example the Schur-Horn theorem states that the diagonal
  of the matrix representation of a selfadjoint linear map is majorized by the eigenvalue sequence
  listed in decreasing order.

These are forms of the *diagonalization theorem* for self-adjoint operators on finite-dimensional
inner product spaces.

The third part of the file covers properties of compact self-adjoint operators:
* `orthogonalComplement_iSup_eigenspaces_eq_bot`: the eigenspaces of a compact self-adjoint operator
  have trivial orthogonal complement.
* `finite_dimensional_eigenspace`: the eigenspaces of a compact self-adjoint operator are
  finite-dimensional.

## TODO

Spectral theory for bounded self-adjoint operators.

## Tags

self-adjoint operator, spectral theorem, diagonalization theorem

-/

@[expose] public section

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

open scoped ComplexConjugate

open Module End WithLp

namespace LinearMap

namespace IsSymmetric

variable {T : E →ₗ[𝕜] E}

/-- A self-adjoint operator preserves orthogonal complements of its eigenspaces. -/
/-
**LinearMap.IsSymmetric.invariant_orthogonalComplement_eigenspace** 是 Mathlib 中的
一个定理，位于命名空间 `LinearMap.IsSymmetric`。
形式化陈述：invariant_orthogonalComplement_eigenspace (hT : T.IsSymmetric) (μ : 𝕜) (v 
: E) (hv : v in (eigenspace T μ)ᗮ) : T v in (eigenspace T μ)ᗮ
参数：hT : T.IsSymmetric；μ : 𝕜；v : E；hv : v in (eigenspace T μ)ᗮ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.End.mem_eigenspace_iff`：mem_eigenspace_iff {f : End R M} {μ : R} 
{x : M} : x in eigenspace f μ ↔ f x = μ • x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_smul_left`：inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪
x, y⟫
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A self-adjoint operator preserves orthogonal complements of its eigenspaces.
-/
theorem invariant_orthogonalComplement_eigenspace (hT : T.IsSymmetric) (μ : 𝕜)
    (v : E) (hv : v ∈ (eigenspace T μ)ᗮ) : T v ∈ (eigenspace T μ)ᗮ := by
  intro w hw
  have : T w = (μ : 𝕜) • w := by rwa [mem_eigenspace_iff] at hw
  simp [← hT w, this, inner_smul_left, hv w hw]

/-- The eigenvalues of a self-adjoint operator are real. -/
/-
**LinearMap.IsSymmetric.conj_eigenvalue_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Linea
rMap.IsSymmetric`。
形式化陈述：conj_eigenvalue_eq_self (hT : T.IsSymmetric) {μ : 𝕜} (hμ : HasEigenvalue T
 μ) : conj μ = μ
参数：hT : T.IsSymmetric；hμ : HasEigenvalue T μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.End.HasEigenvalue.exists_hasEigenvector`：∀ {R : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]  
 {f : Module.End R M} {μ : R}, f.Has…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.End.mem_eigenspace_iff`：mem_eigenspace_iff {f : End R M} {μ : R} 
{x : M} : x in eigenspace f μ ↔ f x = μ • x
· 使用定理 `inner_smul_left`：inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪
x, y⟫
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p

--- 原说明 ---
The eigenvalues of a self-adjoint operator are real.
-/
theorem conj_eigenvalue_eq_self (hT : T.IsSymmetric) {μ : 𝕜} (hμ : HasEigenvalue T μ) :
    conj μ = μ := by
  obtain ⟨v, hv₁, hv₂⟩ := hμ.exists_hasEigenvector
  rw [mem_eigenspace_iff] at hv₁
  simpa [hv₂, inner_smul_left, inner_smul_right, hv₁] using hT v v

/-- The eigenspaces of a self-adjoint operator are mutually orthogonal. -/
/-
**LinearMap.IsSymmetric.orthogonalFamily_eigenspaces** 是 Mathlib 中的一个定理，位于命名空间 `
LinearMap.IsSymmetric`。
形式化陈述：orthogonalFamily_eigenspaces (hT : T.IsSymmetric) : OrthogonalFamily 𝕜 (fu
n μ => eigenspace T μ) fun μ => (eigenspace T μ).subtypeₗᵢ
参数：hT : T.IsSymmetric。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `inner_zero_left`：inner_zero_left (x : E) : ⟪0, x⟫ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearMap.IsSymmetric.conj_eigenvalue_eq_self`：conj_eigenvalue_eq_self (
hT : T.IsSymmetric) {μ : 𝕜} (hμ : HasEigenvalue T μ) : conj μ = μ
· 使用定理 `Module.End.hasEigenvalue_of_hasEigenvector`：hasEigenvalue_of_hasEigenvec
tor {f : End R M} {μ : R} {x : M} (h : HasEigenvector f μ x) : HasEigenvalue f μ
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Module.End.mem_eigenspace_iff`：mem_eigenspace_iff {f : End R M} {μ : R} 
{x : M} : x in eigenspace f μ ↔ f x = μ • x
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用定理 `inner_smul_left`：inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪
x, y⟫
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a

--- 原说明 ---
The eigenspaces of a self-adjoint operator are mutually orthogonal.
-/
theorem orthogonalFamily_eigenspaces (hT : T.IsSymmetric) :
    OrthogonalFamily 𝕜 (fun μ => eigenspace T μ) fun μ => (eigenspace T μ).subtypeₗᵢ := by
  rintro μ ν hμν ⟨v, hv⟩ ⟨w, hw⟩
  by_cases hv' : v = 0
  · simp [hv']
  have H := hT.conj_eigenvalue_eq_self (hasEigenvalue_of_hasEigenvector ⟨hv, hv'⟩)
  rw [mem_eigenspace_iff] at hv hw
  refine Or.resolve_left ?_ hμν.symm
  simpa [inner_smul_left, inner_smul_right, hv, hw, H] using (hT v w).symm
/-
**LinearMap.IsSymmetric.orthogonalFamily_eigenspaces'** 是 Mathlib 中的一个定理，位于命名空间 
`LinearMap.IsSymmetric`。
形式化陈述：orthogonalFamily_eigenspaces' (hT : T.IsSymmetric) : OrthogonalFamily 𝕜 (f
un μ : Eigenvalues T => eigenspace T μ) fun μ => (eigenspace T μ).subtypeₗᵢ
参数：hT : T.IsSymmetric。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrthogonalFamily.comp`：OrthogonalFamily.comp {γ : Type*} {f : γ -> ι} (h
f : Function.Injective f) : OrthogonalFamily 𝕜 (fun g => G (f g)) fun g => V (f 
g)
· 使用定理 `LinearMap.IsSymmetric.orthogonalFamily_eigenspaces`：orthogonalFamily_eig
enspaces (hT : T.IsSymmetric) : OrthogonalFamily 𝕜 (fun μ => eigenspace T μ) fun
 μ => (eigenspace T μ).subtypeₗᵢ
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
theorem orthogonalFamily_eigenspaces' (hT : T.IsSymmetric) :
    OrthogonalFamily 𝕜 (fun μ : Eigenvalues T => eigenspace T μ) fun μ =>
      (eigenspace T μ).subtypeₗᵢ :=
  hT.orthogonalFamily_eigenspaces.comp Subtype.coe_injective

/-- The mutual orthogonal complement of the eigenspaces of a self-adjoint operator on an inner
product space is an invariant subspace of the operator. -/
/-
**LinearMap.IsSymmetric.orthogonalComplement_iSup_eigenspaces_invariant** 是 Math
lib 中的一个定理，位于命名空间 `LinearMap.IsSymmetric`。
形式化陈述：orthogonalComplement_iSup_eigenspaces_invariant (hT : T.IsSymmetric) ⦃v : 
E⦄ (hv : v in (⨆ μ, eigenspace T μ)ᗮ) : T v in (⨆ μ, eigenspace T μ)ᗮ
参数：hT : T.IsSymmetric。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.iInf_orthogonal`：iInf_orthogonal {ι : Type*} (K : ι -> Submodu
le 𝕜 E) : ⨅ i, (K i)ᗮ = (iSup K)ᗮ
· 使用定理 `LinearMap.iInf_invariant`：∀ {R : Type u_1} {M : Type u_5} [inst : Semiri
ng R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {σ : R →+* R} {ι
 : Sort u_9} (…
· 使用定理 `LinearMap.IsSymmetric.invariant_orthogonalComplement_eigenspace`：invaria
nt_orthogonalComplement_eigenspace (hT : T.IsSymmetric) (μ : 𝕜) (v : E) (hv : v 
in (eigenspace T μ)ᗮ) : T v in (eigenspace T μ)ᗮ

--- 原说明 ---
The mutual orthogonal complement of the eigenspaces of a self-adjoint operator o
n an inner
product space is an invariant subspace of the operator.
-/
theorem orthogonalComplement_iSup_eigenspaces_invariant (hT : T.IsSymmetric)
    ⦃v : E⦄ (hv : v ∈ (⨆ μ, eigenspace T μ)ᗮ) : T v ∈ (⨆ μ, eigenspace T μ)ᗮ := by
  rw [← Submodule.iInf_orthogonal] at hv ⊢
  exact T.iInf_invariant hT.invariant_orthogonalComplement_eigenspace v hv

/-- The mutual orthogonal complement of the eigenspaces of a self-adjoint operator on an inner
product space has no eigenvalues. -/
/-
**LinearMap.IsSymmetric.orthogonalComplement_iSup_eigenspaces** 是 Mathlib 中的一个定理
，位于命名空间 `LinearMap.IsSymmetric`。
形式化陈述：orthogonalComplement_iSup_eigenspaces (hT : T.IsSymmetric) (μ : 𝕜) : eigen
space (T.restrict hT.orthogonalComplement_iSup_eigenspaces_invariant) μ = ⊥
参数：hT : T.IsSymmetric；μ : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.End.eigenspace_restrict_eq_bot`：eigenspace_restrict_eq_bot {f : E
nd R M} {p : Submodule R M} (hfp : forall x in p, f x in p) {μ : R} (hμp : Disjo
int (f.eigenspace μ) p) : e…
· 使用定理 `LinearMap.IsSymmetric.orthogonalComplement_iSup_eigenspaces_invariant`：o
rthogonalComplement_iSup_eigenspaces_invariant (hT : T.IsSymmetric) ⦃v : E⦄ (hv 
: v in (⨆ μ, eigenspace T μ)ᗮ) : T v in (⨆ μ, eigenspace T …
· 使用定理 `Submodule.IsOrtho.mono_left`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCL
ike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {U₁ U₂
 V : Submodule 𝕜 …
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `Submodule.isOrtho_orthogonal_right`：isOrtho_orthogonal_right (U : Submod
ule 𝕜 E) : U ⟂ Uᗮ
· 使用定理 `Submodule.IsOrtho.disjoint`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : RCLi
ke 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {U V : 
Submodule 𝕜 E}, …

--- 原说明 ---
The mutual orthogonal complement of the eigenspaces of a self-adjoint operator o
n an inner
product space has no eigenvalues.
-/
theorem orthogonalComplement_iSup_eigenspaces (hT : T.IsSymmetric) (μ : 𝕜) :
    eigenspace (T.restrict hT.orthogonalComplement_iSup_eigenspaces_invariant) μ = ⊥ := by
  set p : Submodule 𝕜 E := (⨆ μ, eigenspace T μ)ᗮ
  refine eigenspace_restrict_eq_bot hT.orthogonalComplement_iSup_eigenspaces_invariant ?_
  have H₂ : eigenspace T μ ⟂ p := (Submodule.isOrtho_orthogonal_right _).mono_left (le_iSup _ _)
  exact H₂.disjoint

/-! ### Finite-dimensional theory -/

variable [FiniteDimensional 𝕜 E]

/-- The mutual orthogonal complement of the eigenspaces of a self-adjoint operator on a
finite-dimensional inner product space is trivial. -/
/-
**LinearMap.IsSymmetric.orthogonalComplement_iSup_eigenspaces_eq_bot** 是 Mathlib
 中的一个定理，位于命名空间 `LinearMap.IsSymmetric`。
形式化陈述：orthogonalComplement_iSup_eigenspaces_eq_bot (hT : T.IsSymmetric) : (⨆ μ, 
eigenspace T μ)ᗮ = ⊥
参数：hT : T.IsSymmetric。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsSymmetric.orthogonalComplement_iSup_eigenspaces_invariant`：o
rthogonalComplement_iSup_eigenspaces_invariant (hT : T.IsSymmetric) ⦃v : E⦄ (hv 
: v in (⨆ μ, eigenspace T μ)ᗮ) : T v in (⨆ μ, eigenspace T …
· 使用定理 `LinearMap.IsSymmetric.restrict_invariant`：∀ {𝕜 : Type u_1} {E : Type u_2
} [inst : RCLike 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : InnerProductSp
ace 𝕜 E]   {T : E →ₗ[𝕜] E}, T.…
· 使用定理 `LinearMap.IsSymmetric.subsingleton_of_no_eigenvalue_finiteDimensional`：s
ubsingleton_of_no_eigenvalue_finiteDimensional (hT : T.IsSymmetric) (hT' : foral
l μ : 𝕜, Module.End.eigenspace (T : E ->ₗ[𝕜] E) μ = ⊥) : Su…
· 使用定理 `LinearMap.IsSymmetric.orthogonalComplement_iSup_eigenspaces`：orthogonalC
omplement_iSup_eigenspaces (hT : T.IsSymmetric) (μ : 𝕜) : eigenspace (T.restrict
 hT.orthogonalComplement_iSup_eigenspaces_invaria…
· 使用定理 `Submodule.eq_bot_of_subsingleton`：eq_bot_of_subsingleton [Subsingleton p
] : p = ⊥

--- 原说明 ---
The mutual orthogonal complement of the eigenspaces of a self-adjoint operator o
n a
finite-dimensional inner product space is trivial.
-/
theorem orthogonalComplement_iSup_eigenspaces_eq_bot (hT : T.IsSymmetric) :
    (⨆ μ, eigenspace T μ)ᗮ = ⊥ := by
  have hT' : IsSymmetric _ :=
    hT.restrict_invariant hT.orthogonalComplement_iSup_eigenspaces_invariant
  -- a self-adjoint operator on a nontrivial inner product space has an eigenvalue
  have :=
    hT'.subsingleton_of_no_eigenvalue_finiteDimensional hT.orthogonalComplement_iSup_eigenspaces
  exact Submodule.eq_bot_of_subsingleton
/-
**LinearMap.IsSymmetric.orthogonalComplement_iSup_eigenspaces_eq_bot'** 是 Mathli
b 中的一个定理，位于命名空间 `LinearMap.IsSymmetric`。
形式化陈述：orthogonalComplement_iSup_eigenspaces_eq_bot' (hT : T.IsSymmetric) : (⨆ μ 
: Eigenvalues T, eigenspace T μ)ᗮ = ⊥
参数：hT : T.IsSymmetric。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iSup_ne_bot_subtype`：iSup_ne_bot_subtype (f : ι -> α) : ⨆ i : { i // f i
 != ⊥ }, f i = ⨆ i, f i
· 使用定理 `LinearMap.IsSymmetric.orthogonalComplement_iSup_eigenspaces_eq_bot`：orth
ogonalComplement_iSup_eigenspaces_eq_bot (hT : T.IsSymmetric) : (⨆ μ, eigenspace
 T μ)ᗮ = ⊥
-/
theorem orthogonalComplement_iSup_eigenspaces_eq_bot' (hT : T.IsSymmetric) :
    (⨆ μ : Eigenvalues T, eigenspace T μ)ᗮ = ⊥ :=
  show (⨆ μ : { μ // eigenspace T μ ≠ ⊥ }, eigenspace T μ)ᗮ = ⊥ by
    rw [iSup_ne_bot_subtype, hT.orthogonalComplement_iSup_eigenspaces_eq_bot]

/-- The eigenspaces of a self-adjoint operator on a finite-dimensional inner product space `E` gives
an internal direct sum decomposition of `E`.

Note this takes `hT` as a `Fact` to allow it to be an instance. -/
/-
**LinearMap.IsSymmetric.directSumDecomposition** 是 Mathlib 中的一个实例，位于命名空间 `Linear
Map.IsSymmetric`。
形式化陈述：directSumDecomposition [hT : Fact T.IsSymmetric] : DirectSum.Decomposition
 fun μ : Eigenvalues T => eigenspace T μ
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The eigenspaces of a self-adjoint operator on a finite-dimensional inner product
 space `E` gives
an internal direct sum decomposition of `E`.

Note this takes `hT` as a `Fact` to allow it to be an instance.
-/
noncomputable instance directSumDecomposition [hT : Fact T.IsSymmetric] :
    DirectSum.Decomposition fun μ : Eigenvalues T => eigenspace T μ :=
  haveI h : ∀ μ : Eigenvalues T, CompleteSpace (eigenspace T μ) := fun μ => by infer_instance
  hT.out.orthogonalFamily_eigenspaces'.decomposition
    (Submodule.orthogonal_eq_bot_iff.mp hT.out.orthogonalComplement_iSup_eigenspaces_eq_bot')
/-
**LinearMap.IsSymmetric.directSum_decompose_apply** 是 Mathlib 中的一个定理，位于命名空间 `Lin
earMap.IsSymmetric`。
形式化陈述：directSum_decompose_apply [_hT : Fact T.IsSymmetric] (x : E) (μ : Eigenval
ues T) : DirectSum.decompose (fun μ : Eigenvalues T => eigenspace T μ) x μ = (ei
genspace T μ).orthogonalProjectionOnto x
参数：x : E；μ : Eigenvalues T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem directSum_decompose_apply [_hT : Fact T.IsSymmetric] (x : E) (μ : Eigenvalues T) :
    DirectSum.decompose (fun μ : Eigenvalues T => eigenspace T μ) x μ =
      (eigenspace T μ).orthogonalProjectionOnto x :=
  rfl

/-- The eigenspaces of a self-adjoint operator on a finite-dimensional inner product space `E` gives
an internal direct sum decomposition of `E`. -/
/-
**LinearMap.IsSymmetric.direct_sum_isInternal** 是 Mathlib 中的一个定理，位于命名空间 `LinearM
ap.IsSymmetric`。
形式化陈述：direct_sum_isInternal (hT : T.IsSymmetric) : DirectSum.IsInternal fun μ : 
Eigenvalues T => eigenspace T μ
参数：hT : T.IsSymmetric。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `OrthogonalFamily.isInternal_iff`：OrthogonalFamily.isInternal_iff [Decida
bleEq ι] [FiniteDimensional 𝕜 E] {V : ι -> Submodule 𝕜 E} (hV : OrthogonalFamily
 𝕜 (fun i => V i) fun…
· 使用定理 `LinearMap.IsSymmetric.orthogonalFamily_eigenspaces'`：orthogonalFamily_ei
genspaces' (hT : T.IsSymmetric) : OrthogonalFamily 𝕜 (fun μ : Eigenvalues T => e
igenspace T μ) fun μ => (eigenspace T μ).…
· 使用定理 `LinearMap.IsSymmetric.orthogonalComplement_iSup_eigenspaces_eq_bot'`：ort
hogonalComplement_iSup_eigenspaces_eq_bot' (hT : T.IsSymmetric) : (⨆ μ : Eigenva
lues T, eigenspace T μ)ᗮ = ⊥

--- 原说明 ---
The eigenspaces of a self-adjoint operator on a finite-dimensional inner product
 space `E` gives
an internal direct sum decomposition of `E`.
-/
theorem direct_sum_isInternal (hT : T.IsSymmetric) :
    DirectSum.IsInternal fun μ : Eigenvalues T => eigenspace T μ :=
  hT.orthogonalFamily_eigenspaces'.isInternal_iff.mpr
    hT.orthogonalComplement_iSup_eigenspaces_eq_bot'

section Version1

/-- Isometry from an inner product space `E` to the direct sum of the eigenspaces of some
self-adjoint operator `T` on `E`. -/
/-
**LinearMap.IsSymmetric.diagonalization** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap.IsS
ymmetric`。
形式化陈述：diagonalization (hT : T.IsSymmetric) : E ≃ₗᵢ[𝕜] PiLp 2 fun μ : Eigenvalues
 T => eigenspace T μ
参数：hT : T.IsSymmetric。
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsSymmetric.direct_sum_isInternal`：direct_sum_isInternal (hT :
 T.IsSymmetric) : DirectSum.IsInternal fun μ : Eigenvalues T => eigenspace T μ
· 使用定理 `LinearMap.IsSymmetric.orthogonalFamily_eigenspaces'`：orthogonalFamily_ei
genspaces' (hT : T.IsSymmetric) : OrthogonalFamily 𝕜 (fun μ : Eigenvalues T => e
igenspace T μ) fun μ => (eigenspace T μ).…

--- 原说明 ---
Isometry from an inner product space `E` to the direct sum of the eigenspaces of
 some
self-adjoint operator `T` on `E`.
-/
noncomputable def diagonalization (hT : T.IsSymmetric) : E ≃ₗᵢ[𝕜] PiLp 2 fun μ :
    Eigenvalues T => eigenspace T μ :=
  hT.direct_sum_isInternal.isometryL2OfOrthogonalFamily hT.orthogonalFamily_eigenspaces'

@[simp]
/-
**LinearMap.IsSymmetric.diagonalization_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Li
nearMap.IsSymmetric`。
形式化陈述：diagonalization_symm_apply (hT : T.IsSymmetric) (w : PiLp 2 fun μ : Eigenv
alues T => eigenspace T μ) : hT.diagonalization.symm w = ∑ μ, w μ
参数：hT : T.IsSymmetric；w : PiLp 2 fun μ : Eigenvalues T => eigenspace T μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `DirectSum.IsInternal.isometryL2OfOrthogonalFamily_symm_apply`：DirectSum.
IsInternal.isometryL2OfOrthogonalFamily_symm_apply [DecidableEq ι] {V : ι -> Sub
module 𝕜 E} (hV : DirectSum.IsInternal V) (hV' : O…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `LinearMap.IsSymmetric.direct_sum_isInternal`：direct_sum_isInternal (hT :
 T.IsSymmetric) : DirectSum.IsInternal fun μ : Eigenvalues T => eigenspace T μ
· 使用定理 `LinearMap.IsSymmetric.orthogonalFamily_eigenspaces'`：orthogonalFamily_ei
genspaces' (hT : T.IsSymmetric) : OrthogonalFamily 𝕜 (fun μ : Eigenvalues T => e
igenspace T μ) fun μ => (eigenspace T μ).…
-/
theorem diagonalization_symm_apply (hT : T.IsSymmetric)
    (w : PiLp 2 fun μ : Eigenvalues T => eigenspace T μ) :
    hT.diagonalization.symm w = ∑ μ, w μ :=
  hT.direct_sum_isInternal.isometryL2OfOrthogonalFamily_symm_apply
    hT.orthogonalFamily_eigenspaces' w

/-- *Diagonalization theorem*, *spectral theorem*; version 1: A self-adjoint operator `T` on a
finite-dimensional inner product space `E` acts diagonally on the decomposition of `E` into the
direct sum of the eigenspaces of `T`. -/
/-
**LinearMap.IsSymmetric.diagonalization_apply_self_apply** 是 Mathlib 中的一个定理，位于命名
空间 `LinearMap.IsSymmetric`。
形式化陈述：diagonalization_apply_self_apply (hT : T.IsSymmetric) (v : E) (μ : Eigenva
lues T) : hT.diagonalization (T v) μ = (μ : 𝕜) • hT.diagonalization v μ
参数：hT : T.IsSymmetric；v : E；μ : Eigenvalues T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.End.mem_eigenspace_iff`：mem_eigenspace_iff {f : End R M} {μ : R} 
{x : M} : x in eigenspace f μ ↔ f x = μ • x
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.IsSymmetric.diagonalization_symm_apply`：diagonalization_symm_a
pply (hT : T.IsSymmetric) (w : PiLp 2 fun μ : Eigenvalues T => eigenspace T μ) :
 hT.diagonalization.symm w = ∑ μ, w μ
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearIsometryEquiv.symm_apply_apply`：symm_apply_apply (x : E) : e.symm 
(e x) = x
· 使用定理 `LinearIsometryEquiv.apply_symm_apply`：apply_symm_apply (x : E₂) : e (e.s
ymm x) = x
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂

--- 原说明 ---
*Diagonalization theorem*, *spectral theorem*; version 1: A self-adjoint operato
r `T` on a
finite-dimensional inner product space `E` acts diagonally on the decomposition 
of `E` into the
direct sum of the eigenspaces of `T`.
-/
theorem diagonalization_apply_self_apply (hT : T.IsSymmetric) (v : E) (μ : Eigenvalues T) :
    hT.diagonalization (T v) μ = (μ : 𝕜) • hT.diagonalization v μ := by
  suffices
    ∀ w : PiLp 2 fun μ : Eigenvalues T => eigenspace T μ,
      T (hT.diagonalization.symm w) = hT.diagonalization.symm (toLp 2 fun μ => (μ : 𝕜) • w μ) by
    simpa only [LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.apply_symm_apply] using
      congr_arg (fun w => hT.diagonalization w μ) (this (hT.diagonalization v))
  intro w
  have hwT : ∀ μ, T (w μ) = (μ : 𝕜) • w μ := fun μ => mem_eigenspace_iff.1 (w μ).2
  simp only [diagonalization_symm_apply, map_sum, hwT, SetLike.val_smul]

end Version1

section Version2

variable {n : ℕ}

set_option backward.privateInPublic true in
/-- Unsorted eigenvalues and eigenvectors.  These private definitions should not be used directly.
Instead use the functions eigenvalues and eigenvectorBasis defined below. -/
/-
**LinearMap.IsSymmetric.unsortedEigenvalues** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap
.IsSymmetric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Unsorted eigenvalues and eigenvectors.  These private definitions should not be 
used directly.
Instead use the functions eigenvalues and eigenvectorBasis defined below.
-/
private noncomputable def unsortedEigenvalues (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
    (i : Fin n) : ℝ :=
  @RCLike.re 𝕜 _ <| (hT.direct_sum_isInternal.subordinateOrthonormalBasisIndex hn i
    hT.orthogonalFamily_eigenspaces').val
/-
**LinearMap.IsSymmetric.hasEigenvalue_unsortedEigenvalues** 是 Mathlib 中的一个定理，位于命
名空间 `LinearMap.IsSymmetric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem hasEigenvalue_unsortedEigenvalues (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
    (i : Fin n) : HasEigenvalue T (hT.unsortedEigenvalues hn i) := by
  unfold unsortedEigenvalues
  let ⟨x, hx⟩ := hT.direct_sum_isInternal.subordinateOrthonormalBasisIndex hn i
    hT.orthogonalFamily_eigenspaces'
  rwa [Eigenvalues.val_mk, RCLike.conj_eq_iff_re.mp (hT.conj_eigenvalue_eq_self hx)]
/-
**LinearMap.IsSymmetric.exists_unsortedEigenvalues_eq** 是 Mathlib 中的一个定理，位于命名空间 
`LinearMap.IsSymmetric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem exists_unsortedEigenvalues_eq (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
    {μ : 𝕜} (hμ : HasEigenvalue T μ) : ∃ i : Fin n, hT.unsortedEigenvalues hn i = μ := by
  let (eq := hx) x : Eigenvalues T := ⟨μ, hμ⟩
  obtain ⟨i, hi⟩ := hT.direct_sum_isInternal.exists_subordinateOrthonormalBasisIndex_eq hn
    hT.orthogonalFamily_eigenspaces' (hasEigenvalue_iff.mp x.prop)
  use i
  rw [unsortedEigenvalues, hi, hx, Eigenvalues.val_mk, ← RCLike.conj_eq_iff_re,
    hT.conj_eigenvalue_eq_self hμ]
/-
**LinearMap.IsSymmetric.card_filter_unsortedEigenvalues_eq** 是 Mathlib 中的一个定理，位于
命名空间 `LinearMap.IsSymmetric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem card_filter_unsortedEigenvalues_eq (hT : T.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) (μ : 𝕜) :
    Finset.card {i | hT.unsortedEigenvalues hn i = μ} = Module.finrank 𝕜 (eigenspace T μ) := by
  by_cases hμ : HasEigenvalue T μ
  · convert!
      hT.direct_sum_isInternal.card_filter_subordinateOrthonormalBasisIndex_eq hn
        hT.orthogonalFamily_eigenspaces' ⟨μ, hμ⟩ with i
    unfold unsortedEigenvalues
    let ⟨x, hx⟩ := hT.direct_sum_isInternal.subordinateOrthonormalBasisIndex hn i
      hT.orthogonalFamily_eigenspaces'
    rw [Eigenvalues.val_mk, RCLike.conj_eq_iff_re.mp (hT.conj_eigenvalue_eq_self hx)]
    exact Subtype.mk_eq_mk.symm
  · rw [Module.End.hasEigenvalue_iff.not_left.mp hμ, finrank_bot, Finset.card_filter_eq_zero_iff]
    intro i _ rfl
    exact hμ (hT.hasEigenvalue_unsortedEigenvalues hn i)
/-
**LinearMap.IsSymmetric.unsortedEigenvectorBasis** 是 Mathlib 中的一个定义，位于命名空间 `Line
arMap.IsSymmetric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private noncomputable def unsortedEigenvectorBasis (hT : T.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) : OrthonormalBasis (Fin n) 𝕜 E :=
  hT.direct_sum_isInternal.subordinateOrthonormalBasis hn hT.orthogonalFamily_eigenspaces'
/-
**LinearMap.IsSymmetric.hasEigenvector_eigenvectorBasis_helper** 是 Mathlib 中的一个定
理，位于命名空间 `LinearMap.IsSymmetric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem hasEigenvector_eigenvectorBasis_helper (hT : T.IsSymmetric)
    (hn : Module.finrank 𝕜 E = n) (i : Fin n) :
    HasEigenvector T (hT.unsortedEigenvalues hn i) (hT.unsortedEigenvectorBasis hn i) := by
  let v : E := hT.unsortedEigenvectorBasis hn i
  let μ : 𝕜 :=
    (hT.direct_sum_isInternal.subordinateOrthonormalBasisIndex hn i
      hT.orthogonalFamily_eigenspaces').val
  simp_rw [unsortedEigenvalues]
  change HasEigenvector T (RCLike.re μ) v
  have key : HasEigenvector T μ v := by
    have H₁ : v ∈ eigenspace T μ := by
      simp_rw [v, unsortedEigenvectorBasis]
      exact
        hT.direct_sum_isInternal.subordinateOrthonormalBasis_subordinate hn i
          hT.orthogonalFamily_eigenspaces'
    have H₂ : v ≠ 0 := by simpa using (hT.unsortedEigenvectorBasis hn).toBasis.ne_zero i
    exact ⟨H₁, H₂⟩
  have re_μ : ↑(RCLike.re μ) = μ := by
    rw [← RCLike.conj_eq_iff_re]
    exact hT.conj_eigenvalue_eq_self (hasEigenvalue_of_hasEigenvector key)
  simpa [re_μ] using key

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The eigenvalues for a self-adjoint operator `T` on a
finite-dimensional inner product space `E`, sorted in decreasing order -/
noncomputable irreducible_def eigenvalues (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) :
    Fin n → ℝ :=
  (hT.unsortedEigenvalues hn) ∘ Tuple.sort (hT.unsortedEigenvalues hn) ∘ @Fin.revPerm n

/-
**LinearMap.IsSymmetric.exists_eigenvalues_eq** 是 Mathlib 中的一个定理，位于命名空间 `LinearM
ap.IsSymmetric`。
形式化陈述：exists_eigenvalues_eq (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) {
μ : 𝕜} (hμ : HasEigenvalue T μ) : exists i : Fin n, hT.eigenvalues hn i = μ
参数：hT : T.IsSymmetric；hn : Module.finrank 𝕜 E = n；hμ : HasEigenvalue T μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Analysis.InnerProductSpace.Spectrum.0.LinearMap.IsSymme
tric.exists_unsortedEigenvalues_eq`：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {E : Type
 u_2} [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {T : E 
→ₗ[𝕜] E} [inst_3…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.IsSymmetric.eigenvalues.congr_simp`：∀ {𝕜 : Type u_3} [inst : R
CLike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSp
ace 𝕜 E]   {T T_1 : E →ₗ[𝕜] E} (e_…
· 使用定理 `Fin.revPerm_apply`：∀ {n : ℕ} (i : Fin n), Fin.revPerm i = i.rev
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearMap.IsSymmetric.eigenvalues_def`：∀ {𝕜 : Type u_3} [inst : RCLike 𝕜
] {E : Type u_4} [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E
]   {T : E →ₗ[𝕜] E} [inst_3…
· 使用定理 `_private.Mathlib.Analysis.InnerProductSpace.Spectrum.0.LinearMap.IsSymme
tric.unsortedEigenvalues.congr_simp`：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {E : Typ
e u_2} [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {T T_1
 : E →ₗ[𝕜] E} (e_…
· 使用定理 `Fin.rev_rev`：∀ {n : ℕ} (i : Fin n), i.rev.rev = i
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem exists_eigenvalues_eq (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) {μ : 𝕜}
    (hμ : HasEigenvalue T μ) : ∃ i : Fin n, hT.eigenvalues hn i = μ := by
  obtain ⟨i, hi⟩ := hT.exists_unsortedEigenvalues_eq hn hμ
  use ((Tuple.sort (hT.unsortedEigenvalues hn)).symm i).revPerm
  simp [eigenvalues_def, hi]
/-
**LinearMap.IsSymmetric.card_filter_eigenvalues_eq** 是 Mathlib 中的一个定理，位于命名空间 `Li
nearMap.IsSymmetric`。
形式化陈述：card_filter_eigenvalues_eq (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E =
 n) (μ : 𝕜) : Finset.card {i | hT.eigenvalues hn i = μ} = Module.finrank 𝕜 (eige
nspace T μ)
参数：hT : T.IsSymmetric；hn : Module.finrank 𝕜 E = n；μ : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `_private.Mathlib.Analysis.InnerProductSpace.Spectrum.0.LinearMap.IsSymme
tric.card_filter_unsortedEigenvalues_eq`：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {E :
 Type u_2} [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {T
 : E →ₗ[𝕜] E} [inst_3…
· 使用定理 `LinearMap.IsSymmetric.eigenvalues_def`：∀ {𝕜 : Type u_3} [inst : RCLike 𝕜
] {E : Type u_4} [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E
]   {T : E →ₗ[𝕜] E} [inst_3…
· 使用引理 `Finset.card_equiv`：card_equiv (e : α ≃ β) (hst : forall i, i in s ↔ e i 
in t) : #s = #t
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `_private.Mathlib.Analysis.InnerProductSpace.Spectrum.0.LinearMap.IsSymme
tric.unsortedEigenvalues.congr_simp`：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {E : Typ
e u_2} [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E]   {T T_1
 : E →ₗ[𝕜] E} (e_…
· 使用定理 `Fin.revPerm_apply`：∀ {n : ℕ} (i : Fin n), Fin.revPerm i = i.rev
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem card_filter_eigenvalues_eq (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (μ : 𝕜) :
    Finset.card {i | hT.eigenvalues hn i = μ} = Module.finrank 𝕜 (eigenspace T μ) := by
  rw [← hT.card_filter_unsortedEigenvalues_eq hn, eigenvalues_def]
  apply Finset.card_equiv (Fin.revPerm.trans (Tuple.sort (hT.unsortedEigenvalues hn)))
  simp

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- A choice of orthonormal basis of eigenvectors for self-adjoint operator `T` on a
finite-dimensional inner product space `E`.  Eigenvectors are sorted in decreasing
order of their eigenvalues. -/
noncomputable irreducible_def eigenvectorBasis (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) :
    OrthonormalBasis (Fin n) 𝕜 E :=
  (hT.direct_sum_isInternal.subordinateOrthonormalBasis
    hn hT.orthogonalFamily_eigenspaces').reindex
      (Tuple.sort (hT.unsortedEigenvalues hn) * @Fin.revPerm n).symm

/-
**LinearMap.IsSymmetric.hasEigenvector_eigenvectorBasis** 是 Mathlib 中的一个定理，位于命名空
间 `LinearMap.IsSymmetric`。
形式化陈述：hasEigenvector_eigenvectorBasis (hT : T.IsSymmetric) (hn : Module.finrank 
𝕜 E = n) (i : Fin n) : HasEigenvector T (hT.eigenvalues hn i) (hT.eigenvectorBas
is hn i)
参数：hT : T.IsSymmetric；hn : Module.finrank 𝕜 E = n；i : Fin n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.IsSymmetric.eigenvalues_def`：∀ {𝕜 : Type u_3} [inst : RCLike 𝕜
] {E : Type u_4} [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E
]   {T : E →ₗ[𝕜] E} [inst_3…
· 使用定理 `LinearMap.IsSymmetric.direct_sum_isInternal`：direct_sum_isInternal (hT :
 T.IsSymmetric) : DirectSum.IsInternal fun μ : Eigenvalues T => eigenspace T μ
· 使用定理 `LinearMap.IsSymmetric.orthogonalFamily_eigenspaces'`：orthogonalFamily_ei
genspaces' (hT : T.IsSymmetric) : OrthogonalFamily 𝕜 (fun μ : Eigenvalues T => e
igenspace T μ) fun μ => (eigenspace T μ).…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `LinearMap.IsSymmetric.eigenvectorBasis_def`：∀ {𝕜 : Type u_3} [inst : RCL
ike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpac
e 𝕜 E]   {T : E →ₗ[𝕜] E} [inst_3…
· 使用定理 `OrthonormalBasis.reindex_apply`：∀ {ι : Type u_1} {ι' : Type u_2} {𝕜 : Ty
pe u_3} [inst : RCLike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst
_2 : InnerProductSpa…
· 使用定理 `_private.Mathlib.Analysis.InnerProductSpace.Spectrum.0.LinearMap.IsSymme
tric.hasEigenvector_eigenvectorBasis_helper`：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] 
{E : Type u_2} [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] 
  {T : E →ₗ[𝕜] E} [inst_3…
-/
theorem hasEigenvector_eigenvectorBasis (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
    (i : Fin n) : HasEigenvector T (hT.eigenvalues hn i) (hT.eigenvectorBasis hn i) := by
  rw [eigenvalues_def, eigenvectorBasis_def, OrthonormalBasis.reindex_apply]
  apply hasEigenvector_eigenvectorBasis_helper

/-- Eigenvalues are sorted in decreasing order. -/
/-
**LinearMap.IsSymmetric.eigenvalues_antitone** 是 Mathlib 中的一个定理，位于命名空间 `LinearMa
p.IsSymmetric`。
形式化陈述：eigenvalues_antitone (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) : 
Antitone (hT.eigenvalues hn)
参数：hT : T.IsSymmetric；hn : Module.finrank 𝕜 E = n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.IsSymmetric.eigenvalues_def`：∀ {𝕜 : Type u_3} [inst : RCLike 𝕜
] {E : Type u_4} [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E
]   {T : E →ₗ[𝕜] E} [inst_3…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_assoc`：comp_assoc (f : φ -> δ) (g : β -> φ) (h : α -> β) :
 (f ∘ g) ∘ h = f ∘ g ∘ h
· 使用定理 `Monotone.comp_antitone`：Monotone.comp_antitone (hg : Monotone g) (hf : A
ntitone f) : Antitone (g ∘ f)
· 使用定理 `Tuple.monotone_sort`：monotone_sort (f : Fin n -> α) : Monotone (f ∘ sort
 f)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.rev_le_rev`：∀ {n : ℕ} {i j : Fin n}, i.rev ≤ j.rev ↔ j ≤ i

--- 原说明 ---
Eigenvalues are sorted in decreasing order.
-/
theorem eigenvalues_antitone (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) :
    Antitone (hT.eigenvalues hn) := by
  rw [eigenvalues_def, ← Function.comp_assoc]
  refine Monotone.comp_antitone ?_ ?_
  · apply Tuple.monotone_sort
  intro _ _ h
  exact Fin.rev_le_rev.mpr h
/-
**LinearMap.IsSymmetric.hasEigenvalue_eigenvalues** 是 Mathlib 中的一个定理，位于命名空间 `Lin
earMap.IsSymmetric`。
形式化陈述：hasEigenvalue_eigenvalues (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = 
n) (i : Fin n) : HasEigenvalue T (hT.eigenvalues hn i)
参数：hT : T.IsSymmetric；hn : Module.finrank 𝕜 E = n；i : Fin n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.End.hasEigenvalue_of_hasEigenvector`：hasEigenvalue_of_hasEigenvec
tor {f : End R M} {μ : R} {x : M} (h : HasEigenvector f μ x) : HasEigenvalue f μ
· 使用定理 `LinearMap.IsSymmetric.hasEigenvector_eigenvectorBasis`：hasEigenvector_ei
genvectorBasis (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (i : Fin n) : 
HasEigenvector T (hT.eigenvalues hn i) (hT.…
-/
theorem hasEigenvalue_eigenvalues (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (i : Fin n) :
    HasEigenvalue T (hT.eigenvalues hn i) :=
  Module.End.hasEigenvalue_of_hasEigenvector (hT.hasEigenvector_eigenvectorBasis hn i)

@[simp]
/-
**LinearMap.IsSymmetric.apply_eigenvectorBasis** 是 Mathlib 中的一个定理，位于命名空间 `Linear
Map.IsSymmetric`。
形式化陈述：apply_eigenvectorBasis (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) 
(i : Fin n) : T (hT.eigenvectorBasis hn i) = (hT.eigenvalues hn i : 𝕜) • hT.eige
nvectorBasis hn i
参数：hT : T.IsSymmetric；hn : Module.finrank 𝕜 E = n；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.End.mem_eigenspace_iff`：mem_eigenspace_iff {f : End R M} {μ : R} 
{x : M} : x in eigenspace f μ ↔ f x = μ • x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LinearMap.IsSymmetric.hasEigenvector_eigenvectorBasis`：hasEigenvector_ei
genvectorBasis (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (i : Fin n) : 
HasEigenvector T (hT.eigenvalues hn i) (hT.…
-/
theorem apply_eigenvectorBasis (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (i : Fin n) :
    T (hT.eigenvectorBasis hn i) = (hT.eigenvalues hn i : 𝕜) • hT.eigenvectorBasis hn i :=
  mem_eigenspace_iff.mp (hT.hasEigenvector_eigenvectorBasis hn i).1

/-- *Diagonalization theorem*, *spectral theorem*; version 2: A self-adjoint operator `T` on a
finite-dimensional inner product space `E` acts diagonally on the identification of `E` with
Euclidean space induced by an orthonormal basis of eigenvectors of `T`. -/
/-
**LinearMap.IsSymmetric.eigenvectorBasis_apply_self_apply** 是 Mathlib 中的一个定理，位于命
名空间 `LinearMap.IsSymmetric`。
形式化陈述：eigenvectorBasis_apply_self_apply (hT : T.IsSymmetric) (hn : Module.finran
k 𝕜 E = n) (v : E) (i : Fin n) : (hT.eigenvectorBasis hn).repr (T v) i = hT.eige
nvalues hn i * (hT.eigenvectorBasis hn).repr v i
参数：hT : T.IsSymmetric；hn : Module.finrank 𝕜 E = n；v : E；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `LinearMap.IsSymmetric.apply_eigenvectorBasis`：apply_eigenvectorBasis (hT
 : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (i : Fin n) : T (hT.eigenvectorB
asis hn i) = (hT.eigenvalues hn i …
· 使用定理 `Fintype.sum_congr`：∀ {α : Type u_1} {M : Type u_4} [inst : Fintype α] [i
nst_1 : AddCommMonoid M] (f g : α → M),   (∀ (a : α), f a = g a) → ∑ a, f a = ∑ 
a, g a
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `WithLp.ofLp_toLp`：ofLp_toLp (x : V) : ofLp (toLp p x) = x
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearIsometryEquiv.symm_apply_apply`：symm_apply_apply (x : E) : e.symm 
(e x) = x
· 使用定理 `LinearIsometryEquiv.apply_symm_apply`：apply_symm_apply (x : E₂) : e (e.s
ymm x) = x
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂

--- 原说明 ---
*Diagonalization theorem*, *spectral theorem*; version 2: A self-adjoint operato
r `T` on a
finite-dimensional inner product space `E` acts diagonally on the identification
 of `E` with
Euclidean space induced by an orthonormal basis of eigenvectors of `T`.
-/
theorem eigenvectorBasis_apply_self_apply (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
    (v : E) (i : Fin n) :
    (hT.eigenvectorBasis hn).repr (T v) i =
      hT.eigenvalues hn i * (hT.eigenvectorBasis hn).repr v i := by
  suffices
    ∀ w : EuclideanSpace 𝕜 (Fin n),
      T ((hT.eigenvectorBasis hn).repr.symm w) =
        (hT.eigenvectorBasis hn).repr.symm (toLp 2 fun i ↦ hT.eigenvalues hn i * w i) by
    simpa [OrthonormalBasis.sum_repr_symm] using
      congr_arg (fun v => (hT.eigenvectorBasis hn).repr v i)
        (this ((hT.eigenvectorBasis hn).repr v))
  intro w
  simp_rw [← OrthonormalBasis.sum_repr_symm, map_sum, map_smul, apply_eigenvectorBasis]
  apply Fintype.sum_congr
  intro a
  rw [smul_smul, mul_comm, ofLp_toLp]
/-
**LinearMap.IsSymmetric.toMatrix_eigenvectorBasis** 是 Mathlib 中的一个定理，位于命名空间 `Lin
earMap.IsSymmetric`。
形式化陈述：toMatrix_eigenvectorBasis (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = 
n) : letI b
参数：hT : T.IsSymmetric；hn : Module.finrank 𝕜 E = n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.toMatrix_apply`：LinearMap.toMatrix_apply (f : M₁ ->ₗ[R] M₂) (i
 : m) (j : n) : LinearMap.toMatrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.IsSymmetric.apply_eigenvectorBasis`：apply_eigenvectorBasis (hT
 : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (i : Fin n) : T (hT.eigenvectorB
asis hn i) = (hT.eigenvalues hn i …
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `OrthonormalBasis.coe_toBasis_repr_apply`：∀ {ι : Type u_1} {𝕜 : Type u_3}
 [inst : RCLike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : In
nerProductSpace 𝕜 E] [inst_3 …
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `OrthonormalBasis.repr_self`：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : RCLi
ke 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpa
ce 𝕜 E] [inst_3 …
· 使用引理 `PiLp.single_apply`：single_apply [Zero 𝕜] (i : ι) (a : 𝕜) (j : ι) : (sing
le p i a : PiLp p (fun _ => 𝕜)) j = ite (j = i) a 0
· 使用定理 `smul_ite`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a b : α) (c : β),   (c • if p then a else b) = if p the…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `RCLike.real_smul_eq_coe_mul`：real_smul_eq_coe_mul (r : Real) (z : K) : r
 • z = (r : K) * z
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem toMatrix_eigenvectorBasis (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) :
    letI b := (hT.eigenvectorBasis hn).toBasis
    T.toMatrix b b = Matrix.diagonal (RCLike.ofReal ∘ hT.eigenvalues hn) := by
  ext i j
  simp [toMatrix_apply, Matrix.diagonal_apply, RCLike.real_smul_eq_coe_mul]
  grind

open Polynomial in
/-
**LinearMap.IsSymmetric.charpoly_eq** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsSymme
tric`。
形式化陈述：charpoly_eq (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) : T.charpol
y = ∏ i, (X - C (hT.eigenvalues hn i : 𝕜))
参数：hT : T.IsSymmetric；hn : Module.finrank 𝕜 E = n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.charpoly_toMatrix`：charpoly_toMatrix {ι : Type w} [DecidableEq
 ι] [Fintype ι] (b : Basis ι R M) : (toMatrix b b f).charpoly = f.charpoly
· 使用定理 `Matrix.charpoly.congr_simp`：∀ {R : Type u_1} [inst : CommRing R] {n : Ty
pe u_4} {inst_1 : DecidableEq n} [inst_2 : DecidableEq n]   [inst_3 : Fintype n]
 (M M_1 : Matrix…
· 使用定理 `LinearMap.IsSymmetric.toMatrix_eigenvectorBasis`：toMatrix_eigenvectorBas
is (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) : letI b
· 使用定理 `Matrix.charpoly_diagonal`：charpoly_diagonal (d : n -> R) : charpoly (dia
gonal d) = ∏ i, (X - C (d i))
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem charpoly_eq (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) :
    T.charpoly = ∏ i, (X - C (hT.eigenvalues hn i : 𝕜)) := by
  simp [← T.charpoly_toMatrix (hT.eigenvectorBasis hn).toBasis, toMatrix_eigenvectorBasis,
    Matrix.charpoly_diagonal]
/-
**LinearMap.IsSymmetric.roots_charpoly_eq_eigenvalues** 是 Mathlib 中的一个定理，位于命名空间 
`LinearMap.IsSymmetric`。
形式化陈述：roots_charpoly_eq_eigenvalues (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 
E = n) : T.charpoly.roots = Multiset.map (RCLike.ofReal ∘ hT.eigenvalues hn) Fin
set.univ.val
参数：hT : T.IsSymmetric；hn : Module.finrank 𝕜 E = n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.charpoly_toMatrix`：charpoly_toMatrix {ι : Type w} [DecidableEq
 ι] [Fintype ι] (b : Basis ι R M) : (toMatrix b b f).charpoly = f.charpoly
· 使用定理 `LinearMap.IsSymmetric.toMatrix_eigenvectorBasis`：toMatrix_eigenvectorBas
is (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) : letI b
· 使用定理 `Matrix.charpoly_diagonal`：charpoly_diagonal (d : n -> R) : charpoly (dia
gonal d) = ∏ i, (X - C (d i))
· 使用定理 `Polynomial.roots_prod`：roots_prod {ι : Type*} (f : ι -> R[X]) (s : Finse
t ι) : s.prod f != 0 -> (s.prod f).roots = s.val.bind fun i => roots (f i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
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
· 使用定理 `Fin.univ_val_map`：∀ {α : Type u_1} {n : ℕ} (f : Fin n → α), Multiset.map
 f Finset.univ.val = ↑(List.ofFn f)
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem roots_charpoly_eq_eigenvalues (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) :
    T.charpoly.roots = Multiset.map (RCLike.ofReal ∘ hT.eigenvalues hn) Finset.univ.val := by
  rw [← charpoly_toMatrix _ (hT.eigenvectorBasis hn).toBasis, toMatrix_eigenvectorBasis,
    Matrix.charpoly_diagonal, Polynomial.roots_prod _ _ (by
      simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])]
  simp
/-
**LinearMap.IsSymmetric.sort_roots_charpoly_eq_eigenvalues** 是 Mathlib 中的一个定理，位于
命名空间 `LinearMap.IsSymmetric`。
形式化陈述：sort_roots_charpoly_eq_eigenvalues (hT : T.IsSymmetric) (hn : Module.finra
nk 𝕜 E = n) : (T.charpoly.roots.map RCLike.re).sort (· >= ·) = List.ofFn (hT.eig
envalues hn)
参数：hT : T.IsSymmetric；hn : Module.finrank 𝕜 E = n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `instIsTransGe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x2 ≤ x1
· 使用定理 `instAntisymmGe`：∀ {α : Type u} [inst : PartialOrder α], Std.Antisymm fun
 x1 x2 => x2 ≤ x1
· 使用定理 `LE.total'`：∀ {α : Type u} [inst : LinearOrder α], Std.Total fun x1 x2 =>
 x2 ≤ x1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.sort.congr_simp`：∀ {α : Type u_1} (s s_1 : Multiset α),   s = s
_1 →     ∀ (r r_1 : α → α → Prop) (e_r : r = r_1) {inst : DecidableRel r} [inst_
1 : DecidableR…
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `LinearMap.IsSymmetric.roots_charpoly_eq_eigenvalues`：roots_charpoly_eq_e
igenvalues (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) : T.charpoly.roots
 = Multiset.map (RCLike.ofReal ∘ hT.eigen…
· 使用定理 `Fin.univ_val_map`：∀ {α : Type u_1} {n : ℕ} (f : Fin n → α), Multiset.map
 f Finset.univ.val = ↑(List.ofFn f)
· 使用定理 `List.map_ofFn`：∀ {n : ℕ} {α : Type u_1} {β : Type u_2} {f : Fin n → α} {
g : α → β}, List.map g (List.ofFn f) = List.ofFn (g ∘ f)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `List.mergeSort_of_pairwise`：∀ {α : Type u_1} {le : α → α → Bool} {l : Li
st α}, List.Pairwise (fun a b => le a b = true) l → l.mergeSort le = l
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
· 使用定理 `Antitone.sortedGE_ofFn`：∀ {α : Type u_1} [inst : Preorder α] {n : ℕ} {f 
: Fin n → α}, Antitone f → (List.ofFn f).SortedGE
· 使用定理 `LinearMap.IsSymmetric.eigenvalues_antitone`：eigenvalues_antitone (hT : T
.IsSymmetric) (hn : Module.finrank 𝕜 E = n) : Antitone (hT.eigenvalues hn)
-/
theorem sort_roots_charpoly_eq_eigenvalues (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) :
    (T.charpoly.roots.map RCLike.re).sort (· ≥ ·) = List.ofFn (hT.eigenvalues hn) := by
  simp_rw [hT.roots_charpoly_eq_eigenvalues, Fin.univ_val_map, Multiset.map_coe, List.map_ofFn,
    Function.comp_def, RCLike.ofReal_re, Multiset.coe_sort]
  have := hn.symm
  convert! List.mergeSort_of_pairwise ?_
  simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
  convert! (hT.eigenvalues_antitone hn).sortedGE_ofFn
/-
**LinearMap.IsSymmetric.eigenvalues_eq_eigenvalues_iff** 是 Mathlib 中的一个定理，位于命名空间
 `LinearMap.IsSymmetric`。
形式化陈述：eigenvalues_eq_eigenvalues_iff {E' : Type*} [NormedAddCommGroup E'] [Inner
ProductSpace 𝕜 E'] [FiniteDimensional 𝕜 E'] {T' : E' ->ₗ[𝕜] E'} (hT : T.IsSymmet
ric) (hn : Module.finrank 𝕜 E = n) (hT' : T'.IsSymmetric) (hn' : Module.finrank 
𝕜 E' = n) : hT.eigenvalues hn = hT'.eigenvalues hn' ↔ T.charpoly = T'.charpoly w
here mp h
参数：hT : T.IsSymmetric；hn : Module.finrank 𝕜 E = n；hT' : T'.IsSymmetric；hn' : Mod
ule.finrank 𝕜 E' = n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.IsSymmetric.charpoly_eq`：charpoly_eq (hT : T.IsSymmetric) (hn 
: Module.finrank 𝕜 E = n) : T.charpoly = ∏ i, (X - C (hT.eigenvalues hn i : 𝕜))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.ofFn_inj`：ofFn_inj {n : Nat} {f g : Fin n -> α} : ofFn f = ofFn g ↔
 f = g
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTransGe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x2 ≤ x1
· 使用定理 `instAntisymmGe`：∀ {α : Type u} [inst : PartialOrder α], Std.Antisymm fun
 x1 x2 => x2 ≤ x1
· 使用定理 `LE.total'`：∀ {α : Type u} [inst : LinearOrder α], Std.Total fun x1 x2 =>
 x2 ≤ x1
· 使用定理 `LinearMap.IsSymmetric.sort_roots_charpoly_eq_eigenvalues`：sort_roots_cha
rpoly_eq_eigenvalues (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) : (T.cha
rpoly.roots.map RCLike.re).sort (· >= ·) = Lis…
-/
theorem eigenvalues_eq_eigenvalues_iff {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E']
    [FiniteDimensional 𝕜 E'] {T' : E' →ₗ[𝕜] E'} (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
    (hT' : T'.IsSymmetric) (hn' : Module.finrank 𝕜 E' = n) :
    hT.eigenvalues hn = hT'.eigenvalues hn' ↔ T.charpoly = T'.charpoly where
  mp h := by rw [hT.charpoly_eq hn, hT'.charpoly_eq hn', h]
  mpr h := by
    rw [← List.ofFn_inj, ← sort_roots_charpoly_eq_eigenvalues, ← sort_roots_charpoly_eq_eigenvalues,
      h]
/-
**LinearMap.IsSymmetric.splits_charpoly** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsS
ymmetric`。
形式化陈述：splits_charpoly (hT : T.IsSymmetric) : T.charpoly.Splits
参数：hT : T.IsSymmetric。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.splits_iff_card_roots`：splits_iff_card_roots : Splits f ↔ f.r
oots.card = f.natDegree
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.IsSymmetric.roots_charpoly_eq_eigenvalues`：roots_charpoly_eq_e
igenvalues (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) : T.charpoly.roots
 = Multiset.map (RCLike.ofReal ∘ hT.eigen…
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Fin.univ_val_map`：∀ {α : Type u_1} {n : ℕ} (f : Fin n → α), Multiset.map
 f Finset.univ.val = ↑(List.ofFn f)
· 使用定理 `List.length_ofFn`：∀ {n : ℕ} {α : Type u_1} {f : Fin n → α}, (List.ofFn f
).length = n
· 使用引理 `LinearMap.charpoly_natDegree`：charpoly_natDegree [StrongRankCondition R]
 : natDegree (charpoly f) = finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem splits_charpoly (hT : T.IsSymmetric) : T.charpoly.Splits := by
  refine Polynomial.splits_iff_card_roots.mpr ?_
  simp [hT.roots_charpoly_eq_eigenvalues rfl, LinearMap.charpoly_natDegree]
/-
**LinearMap.IsSymmetric.det_eq_prod_eigenvalues** 是 Mathlib 中的一个定理，位于命名空间 `Linea
rMap.IsSymmetric`。
形式化陈述：det_eq_prod_eigenvalues (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n)
 : T.det = ∏ i, (hT.eigenvalues hn i : 𝕜)
参数：hT : T.IsSymmetric；hn : Module.finrank 𝕜 E = n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用引理 `Module.End.det_eq_prod_roots_charpoly_of_splits`：det_eq_prod_roots_charp
oly_of_splits {f : End K V} (h : f.charpoly.Splits) : f.det = f.charpoly.roots.p
rod
· 使用定理 `LinearMap.IsSymmetric.splits_charpoly`：splits_charpoly (hT : T.IsSymmetr
ic) : T.charpoly.Splits
· 使用定理 `LinearMap.IsSymmetric.roots_charpoly_eq_eigenvalues`：roots_charpoly_eq_e
igenvalues (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) : T.charpoly.roots
 = Multiset.map (RCLike.ofReal ∘ hT.eigen…
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Fin.univ_val_map`：∀ {α : Type u_1} {n : ℕ} (f : Fin n → α), Multiset.map
 f Finset.univ.val = ↑(List.ofFn f)
· 使用定理 `List.prod_ofFn`：prod_ofFn {n : Nat} {f : Fin n -> M} : (ofFn f).prod = ∏
 i, f i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem det_eq_prod_eigenvalues (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) :
    T.det = ∏ i, (hT.eigenvalues hn i : 𝕜) := by
  simp [det_eq_prod_roots_charpoly_of_splits hT.splits_charpoly,
    hT.roots_charpoly_eq_eigenvalues hn, List.prod_ofFn]

end Version2

end IsSymmetric

end LinearMap

section Nonneg

-- Cannot be @[simp] because the LHS is not in simp normal form
/-
**inner_product_apply_eigenvector** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_product_apply_eigenvector {μ : 𝕜} {v : E} {T : E ->ₗ[𝕜] E} (h : T v 
= μ • v) : ⟪v, T v⟫ = μ * (‖v‖ : 𝕜) ^ 2
参数：h : T v = μ • v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inner_smul_right`：inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * 
⟪x, y⟫
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inner_product_apply_eigenvector {μ : 𝕜} {v : E} {T : E →ₗ[𝕜] E}
    (h : T v = μ • v) : ⟪v, T v⟫ = μ * (‖v‖ : 𝕜) ^ 2 := by
  simp only [h, inner_smul_right, inner_self_eq_norm_sq_to_K]
/-
**eigenvalue_nonneg_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eigenvalue_nonneg_of_nonneg {μ : Real} {T : E ->ₗ[𝕜] E} (hμ : HasEigenvalu
e T μ) (hnn : forall x : E, 0 <= RCLike.re ⟪x, T x⟫) : 0 <= μ
参数：hμ : HasEigenvalue T μ；hnn : forall x : E, 0 <= RCLike.re ⟪x, T x⟫。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.End.HasEigenvalue.exists_hasEigenvector`：∀ {R : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]  
 {f : Module.End R M} {μ : R}, f.Has…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `inner_product_apply_eigenvector`：inner_product_apply_eigenvector {μ : 𝕜}
 {v : E} {T : E ->ₗ[𝕜] E} (h : T v = μ • v) : ⟪v, T v⟫ = μ * (‖v‖ : 𝕜) ^ 2
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_nonneg_iff_of_pos_right`：mul_nonneg_iff_of_pos_right [MulPosStrictMo
no R] (h : 0 < c) : 0 <= b * c ↔ 0 <= b
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
-/
theorem eigenvalue_nonneg_of_nonneg {μ : ℝ} {T : E →ₗ[𝕜] E} (hμ : HasEigenvalue T μ)
    (hnn : ∀ x : E, 0 ≤ RCLike.re ⟪x, T x⟫) : 0 ≤ μ := by
  obtain ⟨v, hv₁, hv₂⟩ := hμ.exists_hasEigenvector
  have hpos : (0 : ℝ) < ‖v‖ ^ 2 := by simpa only [sq_pos_iff, norm_ne_zero_iff] using hv₂
  simp only [mem_genEigenspace_one] at hv₁
  have : RCLike.re ⟪v, T v⟫ = μ * ‖v‖ ^ 2 :=
    mod_cast congr_arg RCLike.re (inner_product_apply_eigenvector hv₁)
  exact (mul_nonneg_iff_of_pos_right hpos).mp (this ▸ hnn v)
/-
**eigenvalue_pos_of_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eigenvalue_pos_of_pos {μ : Real} {T : E ->ₗ[𝕜] E} (hμ : HasEigenvalue T μ)
 (hnn : forall x : E, 0 < RCLike.re ⟪x, T x⟫) : 0 < μ
参数：hμ : HasEigenvalue T μ；hnn : forall x : E, 0 < RCLike.re ⟪x, T x⟫。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.End.HasEigenvalue.exists_hasEigenvector`：∀ {R : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]  
 {f : Module.End R M} {μ : R}, f.Has…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `inner_product_apply_eigenvector`：inner_product_apply_eigenvector {μ : 𝕜}
 {v : E} {T : E ->ₗ[𝕜] E} (h : T v = μ • v) : ⟪v, T v⟫ = μ * (‖v‖ : 𝕜) ^ 2
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_pos_iff_of_pos_right`：mul_pos_iff_of_pos_right [MulPosStrictMono α] 
[MulPosReflectLT α] (h : 0 < b) : 0 < a * b ↔ 0 < a
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
-/
theorem eigenvalue_pos_of_pos {μ : ℝ} {T : E →ₗ[𝕜] E} (hμ : HasEigenvalue T μ)
    (hnn : ∀ x : E, 0 < RCLike.re ⟪x, T x⟫) : 0 < μ := by
  obtain ⟨v, hv₁, hv₂⟩ := hμ.exists_hasEigenvector
  have hpos : (0 : ℝ) < ‖v‖ ^ 2 := by simpa only [sq_pos_iff, norm_ne_zero_iff] using hv₂
  simp only [mem_genEigenspace_one] at hv₁
  have : RCLike.re ⟪v, T v⟫ = μ * ‖v‖ ^ 2 :=
    mod_cast congr_arg RCLike.re (inner_product_apply_eigenvector hv₁)
  exact (mul_pos_iff_of_pos_right hpos).mp (this ▸ hnn v)

end Nonneg

namespace ContinuousLinearMap

variable [CompleteSpace E] {T : E →L[𝕜] E}

/-
**ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero** 是 Mathlib 中的一个定理
，位于命名空间 `ContinuousLinearMap`。
形式化陈述：eq_zero_of_forall_hasEigenvalue_eq_zero (hT : IsCompactOperator T) (hT' : 
T.IsSymmetric) : (forall μ, HasEigenvalue (T : End 𝕜 E) μ -> μ = 0) ↔ T = 0
参数：hT : IsCompactOperator T；hT' : T.IsSymmetric。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nnnorm_eq_zero`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a‖₊
 = 0 ↔ a = 0
· 使用定理 `ENNReal.coe_eq_zero`：∀ {r : NNReal}, ↑r = 0 ↔ r = 0
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousLinearMap.spectralRadius_eq_nnnorm`：spectralRadius_eq_nnnorm [
CompleteSpace E] (hT : IsSelfAdjoint T) : spectralRadius 𝕜 T = ‖T‖₊
· 使用定理 `LinearMap.IsSymmetric.isSelfAdjoint`：∀ {𝕜 : Type u_1} {E : Type u_2} [in
st : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] 
  [inst_3 : CompleteSpace…
· 使用定理 `spectralRadius.eq_1`：∀ (𝕜 : Type u_1) {A : Type u_2} [inst : NormedField
 𝕜] [inst_1 : Ring A] [inst_2 : Algebra 𝕜 A] (a : A),   spectralRadius 𝕜 a = ⨆ k
 ∈ spectr…
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `ENNReal.iSup_eq_zero`：∀ {ι : Sort u_1} {f : ι → ENNReal}, ⨆ i, f i = 0 ↔
 ∀ (i : ι), f i = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsCompactOperator.hasEigenvalue_iff_mem_spectrum`：hasEigenvalue_iff_mem_
spectrum (hT : IsCompactOperator T) (hμ : μ != 0) : HasEigenvalue (T : End 𝕜 X) 
μ ↔ μ in spectrum 𝕜 T
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem eq_zero_of_forall_hasEigenvalue_eq_zero (hT : IsCompactOperator T) (hT' : T.IsSymmetric) :
    (∀ μ, HasEigenvalue (T : End 𝕜 E) μ → μ = 0) ↔ T = 0 := by
  rw [← nnnorm_eq_zero, ← ENNReal.coe_eq_zero, ← T.spectralRadius_eq_nnnorm hT'.isSelfAdjoint,
    spectralRadius, ← not_iff_not, ENNReal.iSup_eq_zero]
  push Not
  apply exists_congr
  simp +contextual [hT.hasEigenvalue_iff_mem_spectrum]

/-- The **Spectral Theorem** for compact self-adjoint operators: the eigenspaces of a compact
self-adjoint operator have trivial orthogonal complement. -/
/-
**ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot** 是 Mathlib 中
的一个定理，位于命名空间 `ContinuousLinearMap`。
形式化陈述：orthogonalComplement_iSup_eigenspaces_eq_bot (hT : IsCompactOperator T) (h
T' : T.IsSymmetric) : (⨆ μ, eigenspace (T : Module.End 𝕜 E) μ)ᗮ = ⊥
参数：hT : IsCompactOperator T；hT' : T.IsSymmetric。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsSymmetric.orthogonalComplement_iSup_eigenspaces_invariant`：o
rthogonalComplement_iSup_eigenspaces_invariant (hT : T.IsSymmetric) ⦃v : E⦄ (hv 
: v in (⨆ μ, eigenspace T μ)ᗮ) : T v in (⨆ μ, eigenspace T …
· 使用定理 `IsCompactOperator.restrict'`：IsCompactOperator.restrict' [T0Space M₂] {f
 : M₂ ->ₗ[R₂] M₂} (hf : IsCompactOperator f) {V : Submodule R₂ M₂} (hV : forall 
v in V, f v in V)…
· 使用定理 `T3Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T3
Space X], T0Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `instT4SpaceOfT1SpaceOfNormalSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [T1Space X] [NormalSpace X], T4Space X
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `CompletelyNormalSpace.toNormalSpace`：∀ {X : Type u_1} [inst : Topologica
lSpace X] [CompletelyNormalSpace X], NormalSpace X
· 使用定理 `UniformSpace.completelyNormalSpace_of_isCountablyGenerated_uniformity`：∀
 {α : Type u} [inst : UniformSpace α] [(uniformity α).IsCountablyGenerated], Com
pletelyNormalSpace α
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `LinearMap.IsSymmetric.restrict_invariant`：∀ {𝕜 : Type u_1} {E : Type u_2
} [inst : RCLike 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : InnerProductSp
ace 𝕜 E]   {T : E →ₗ[𝕜] E}, T.…
· 使用定理 `LinearMap.IsSymmetric.orthogonalComplement_iSup_eigenspaces`：orthogonalC
omplement_iSup_eigenspaces (hT : T.IsSymmetric) (μ : 𝕜) : eigenspace (T.restrict
 hT.orthogonalComplement_iSup_eigenspaces_invaria…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.subsingleton_iff_eq_bot`：subsingleton_iff_eq_bot : Subsingleto
n p ↔ p = ⊥
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero`：eq_zero_of_
forall_hasEigenvalue_eq_zero (hT : IsCompactOperator T) (hT' : T.IsSymmetric) : 
(forall μ, HasEigenvalue (T : End 𝕜 E) μ -> μ = 0…
· 使用定理 `Module.End.eigenspace_zero`：eigenspace_zero (f : End R M) : f.eigenspace
 0 = LinearMap.ker f
· 使用定理 `LinearMap.ker_zero`：ker_zero : ker (0 : M ->ₛₗ[τ₁₂] M₂) = ⊤
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
The **Spectral Theorem** for compact self-adjoint operators: the eigenspaces of 
a compact
self-adjoint operator have trivial orthogonal complement.
-/
theorem orthogonalComplement_iSup_eigenspaces_eq_bot
    (hT : IsCompactOperator T) (hT' : T.IsSymmetric) :
    (⨆ μ, eigenspace (T : Module.End 𝕜 E) μ)ᗮ = ⊥ := by
  let S : (⨆ μ, eigenspace T μ : Submodule 𝕜 E)ᗮ →L[𝕜] (⨆ μ, eigenspace T μ : Submodule 𝕜 E)ᗮ :=
    T.restrict hT'.orthogonalComplement_iSup_eigenspaces_invariant
  have hS_compact : IsCompactOperator S :=
    hT.restrict' hT'.orthogonalComplement_iSup_eigenspaces_invariant
  have hS_symm : S.IsSymmetric :=
    hT'.restrict_invariant (hT'.orthogonalComplement_iSup_eigenspaces_invariant)
  have hS μ : eigenspace (S : Module.End 𝕜 (⨆ μ, eigenspace T μ : Submodule 𝕜 E)ᗮ) μ = ⊥ :=
    hT'.orthogonalComplement_iSup_eigenspaces _
  have h μ : HasEigenvalue (S : End 𝕜 (⨆ μ, eigenspace T μ : Submodule 𝕜 E)ᗮ) μ → μ = 0 := by
    simp_all [hasEigenvalue_iff]
  rw [eq_zero_of_forall_hasEigenvalue_eq_zero hS_compact hS_symm] at h
  rw [← Submodule.subsingleton_iff_eq_bot]
  by_contra! hV
  simpa [h] using hS 0

/-- The **Spectral Theorem** for compact self-adjoint operators: the eigenspaces of a compact
self-adjoint operator are finite-dimensional. -/
/-
**ContinuousLinearMap.finite_dimensional_eigenspace** 是 Mathlib 中的一个定理，位于命名空间 `C
ontinuousLinearMap`。
形式化陈述：finite_dimensional_eigenspace (hT : IsCompactOperator T) (μ : 𝕜) (hμ : μ !
= 0) : FiniteDimensional 𝕜 (eigenspace T.toLinearMap μ)
参数：hT : IsCompactOperator T；μ : 𝕜；hμ : μ != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.End.mem_invtSubmodule_iff_forall_mem_of_mem`：mem_invtSubmodule_if
f_forall_mem_of_mem {p : Submodule R M} : p in f.invtSubmodule ↔ forall x in p, 
f x in p
· 使用定理 `Module.End.eigenspace_mem_invtSubmodule`：eigenspace_mem_invtSubmodule (f
 : End R M) (μ : R) : eigenspace f μ in invtSubmodule f
· 使用定理 `IsCompactOperator.restrict'`：IsCompactOperator.restrict' [T0Space M₂] {f
 : M₂ ->ₗ[R₂] M₂} (hf : IsCompactOperator f) {V : Submodule R₂ M₂} (hV : forall 
v in V, f v in V)…
· 使用定理 `T3Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T3
Space X], T0Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `instT4SpaceOfT1SpaceOfNormalSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [T1Space X] [NormalSpace X], T4Space X
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `CompletelyNormalSpace.toNormalSpace`：∀ {X : Type u_1} [inst : Topologica
lSpace X] [CompletelyNormalSpace X], NormalSpace X
· 使用定理 `UniformSpace.completelyNormalSpace_of_isCountablyGenerated_uniformity`：∀
 {α : Type u} [inst : UniformSpace α] [(uniformity α).IsCountablyGenerated], Com
pletelyNormalSpace α
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `instCompleteSpaceSubtypeMemSubmoduleOfIsClosedCoe`：∀ {R : Type u_1} {M :
 Type u_2} [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : UniformSpace
 M]   [inst_3 : _root_.Module R M] [Com…
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isCompactOperator_id_iff_finiteDimensional`：isCompactOperator_id_iff_fin
iteDimensional [LocallyCompactSpace 𝕜] : IsCompactOperator (_root_.id : E -> E) 
↔ FiniteDimensional 𝕜 E
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `instT2SpaceSubtype`：∀ {X : Type u_1} [inst : TopologicalSpace X] {p : X 
→ Prop} [T2Space X], T2Space (Subtype p)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `FiniteDimensional.proper_real`：∀ (E : Type u) [inst : NormedAddCommGroup
 E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E], ProperSpace E
· 使用定理 `IsCompactOperator.smul_iff₀`：IsCompactOperator.smul_iff₀ {S : Type*} [Gr
oupWithZero S] [DistribMulAction S M₂] [ContinuousConstSMul S M₂] {f : M₁ -> M₂}
 {c : S} (hc : c …
· 使用定理 `LinearMap.coe_smul`：coe_smul (a : S) (f : M ->ₛₗ[σ₁₂] M₂) : (a • f : M -
>ₛₗ[σ₁₂] M₂) = a • (f : M -> M₂)
· 使用定理 `Module.End.restrict_eigenspace`：restrict_eigenspace (f : End R M) (μ : R
) : f.restrict (f.mem_invtSubmodule_iff_forall_mem_of_mem.mp (eigenspace_mem_inv
tSubmodule f μ)) = μ…

--- 原说明 ---
The **Spectral Theorem** for compact self-adjoint operators: the eigenspaces of 
a compact
self-adjoint operator are finite-dimensional.
-/
theorem finite_dimensional_eigenspace (hT : IsCompactOperator T) (μ : 𝕜) (hμ : μ ≠ 0) :
    FiniteDimensional 𝕜 (eigenspace T.toLinearMap μ) := by
  replace hT := hT.restrict'
    ((mem_invtSubmodule_iff_forall_mem_of_mem _).mp (eigenspace_mem_invtSubmodule T.toLinearMap μ))
  rw [restrict_eigenspace, LinearMap.coe_smul, IsCompactOperator.smul_iff₀ hμ] at hT
  rwa [← isCompactOperator_id_iff_finiteDimensional]

end ContinuousLinearMap

