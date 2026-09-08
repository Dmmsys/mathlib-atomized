/-
Copyright (c) 2022 Hans Parshall. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hans Parshall
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Topology.UniformSpace.Matrix

/-!
# Analytic properties of the `star` operation on matrices

This transports the operator norm on `EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 m` to
`Matrix m n 𝕜`. See the file `Mathlib/Analysis/Matrix.lean` for many other matrix norms.

## Main definitions

* `Matrix.instNormedRingL2Op`: the (necessarily unique) normed ring structure on `Matrix n n 𝕜`
  which ensure it is a `CStarRing` in `Matrix.instCStarRing`. This is a scoped instance in the
  namespace `Matrix.Norms.L2Operator` in order to avoid choosing a global norm for `Matrix`.

## Main statements

* `entry_norm_bound_of_unitary`: the entries of a unitary matrix are uniformly bound by `1`.

## Implementation details

We take care to ensure the topology and uniformity induced by `Matrix.instMetricSpaceL2Op`
coincide with the existing topology and uniformity on matrices.

-/

@[expose] public section

open WithLp
open scoped Matrix

variable {𝕜 m n l E : Type*}

section EntrywiseSupNorm

variable [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-
**entry_norm_bound_of_unitary** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} {n : Type u_3} [inst : RCLike 𝕜] [inst_1 : Fintype n] [in
st_2 : DecidableEq n] {U : Matrix n n 𝕜},   U ∈ Matrix.unitaryGroup n 𝕜 → ∀ (i j
 : n), ‖U i j‖ ≤ 1
参数：i j : n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.single_le_sum`：∀ {α : Type u_2} [inst : AddCommMonoid α] [inst_
1 : Preorder α] {s : Multiset α} [IsOrderedAddMonoid α],   (∀ x ∈ s, 0 ≤ x) → ∀ 
x ∈ s, x ≤ s…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.mem_map`：mem_map {f : α -> β} {b : β} {s : Multiset α} : b in m
ap f s ↔ exists a, a in s ∧ f a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `RCLike.mul_conj`：mul_conj (z : K) : z * conj z = ‖z‖ ^ 2
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `RCLike.ext_iff`：ext_iff {z w : K} : z = w ↔ re z = re w ∧ im z = im w
· 使用定理 `RCLike.ofReal_re`：ofReal_re : forall r : Real, re (r : K) = r
· 使用定理 `Unitary.mul_star_self_of_mem`：mul_star_self_of_mem {U : R} (hU : U in un
itary R) : U * star U = 1
· 使用定理 `Matrix.one_apply_eq`：one_apply_eq (i) : (1 : Matrix n n α) i i = 1
· 使用定理 `RCLike.one_re`：one_re : re (1 : K) = 1
· 使用引理 `sq_le_one_iff₀`：sq_le_one_iff₀ (ha : 0 <= a) : a ^ 2 <= 1 ↔ a <= 1
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem entry_norm_bound_of_unitary {U : Matrix n n 𝕜} (hU : U ∈ Matrix.unitaryGroup n 𝕜)
    (i j : n) : ‖U i j‖ ≤ 1 := by
  -- The norm squared of an entry is at most the L2 norm of its row.
  have norm_sum : ‖U i j‖ ^ 2 ≤ ∑ x, ‖U i x‖ ^ 2 := by
    apply Multiset.single_le_sum
    · intro x h_x
      rw [Multiset.mem_map] at h_x
      obtain ⟨a, h_a⟩ := h_x
      rw [← h_a.2]
      apply sq_nonneg
    · rw [Multiset.mem_map]
      use j
      simp only [Finset.mem_univ_val, and_self_iff]
  -- The L2 norm of a row is a diagonal entry of U * Uᴴ
  have diag_eq_norm_sum : (U * Uᴴ) i i = (∑ x : n, ‖U i x‖ ^ 2 : ℝ) := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, ← starRingEnd_apply, RCLike.mul_conj]
    norm_cast
  -- The L2 norm of a row is a diagonal entry of U * Uᴴ, real part
  have re_diag_eq_norm_sum : RCLike.re ((U * Uᴴ) i i) = ∑ x : n, ‖U i x‖ ^ 2 := by
    rw [RCLike.ext_iff] at diag_eq_norm_sum
    rw [diag_eq_norm_sum.1]
    norm_cast
  -- Since U is unitary, the diagonal entries of U * Uᴴ are all 1
  have mul_eq_one : U * Uᴴ = 1 := Unitary.mul_star_self_of_mem hU
  have diag_eq_one : RCLike.re ((U * Uᴴ) i i) = 1 := by
    simp only [mul_eq_one, Matrix.one_apply_eq, RCLike.one_re]
  -- Putting it all together
  rw [← sq_le_one_iff₀ (norm_nonneg (U i j)), ← diag_eq_one, re_diag_eq_norm_sum]
  exact norm_sum

set_option backward.isDefEq.respectTransparency false in
open scoped Matrix.Norms.Elementwise in
/-- The entrywise sup norm of a unitary matrix is at most 1. -/
/-
**entrywise_sup_norm_bound_of_unitary** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {𝕜 : Type u_1} {n : Type u_3} [inst : RCLike 𝕜] [inst_1 : Fintype n] [in
st_2 : DecidableEq n] {U : Matrix n n 𝕜},   U ∈ Matrix.unitaryGroup n 𝕜 → ‖U‖ ≤ 
1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `pi_norm_le_iff_of_nonneg`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : Fi
ntype ι] [inst_1 : (i : ι) → SeminormedAddGroup (G i)] {x : (i : ι) → G i}   {r 
: ℝ}, 0 ≤ r → …
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `entry_norm_bound_of_unitary`：∀ {𝕜 : Type u_1} {n : Type u_3} [inst : RCL
ike 𝕜] [inst_1 : Fintype n] [inst_2 : DecidableEq n] {U : Matrix n n 𝕜},   U ∈ M
atrix.unitaryGrou…

--- 原说明 ---
The entrywise sup norm of a unitary matrix is at most 1.
-/
theorem entrywise_sup_norm_bound_of_unitary {U : Matrix n n 𝕜} (hU : U ∈ Matrix.unitaryGroup n 𝕜) :
    ‖U‖ ≤ 1 := by
  simp_rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intros
  exact entry_norm_bound_of_unitary hU _ _

end EntrywiseSupNorm

noncomputable section L2OpNorm

namespace Matrix
open LinearMap

variable [RCLike 𝕜]
variable [Fintype m] [Fintype n] [DecidableEq n] [Fintype l] [DecidableEq l]

/-- The natural star algebra equivalence between matrices and continuous linear endomorphisms
of Euclidean space induced by the orthonormal basis `EuclideanSpace.basisFun`.

This is a more-bundled version of `Matrix.toEuclideanLin`, for the special case of square matrices,
followed by a more-bundled version of `LinearMap.toContinuousLinearMap`. -/
/-
**Matrix.toEuclideanCLM** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：{𝕜 : Type u_1} →   {n : Type u_3} →     [inst : RCLike 𝕜] →       [inst_1 
: Fintype n] → [DecidableEq n] → Matrix n n 𝕜 ≃⋆ₐ[𝕜] EuclideanSpace 𝕜 n →L[𝕜] Eu
clideanSpace 𝕜 n
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K

--- 原说明 ---
The natural star algebra equivalence between matrices and continuous linear endo
morphisms
of Euclidean space induced by the orthonormal basis `EuclideanSpace.basisFun`.

This is a more-bundled version of `Matrix.toEuclideanLin`, for the special case 
of square matrices,
followed by a more-bundled version of `LinearMap.toContinuousLinearMap`.
-/
def toEuclideanCLM :
    Matrix n n 𝕜 ≃⋆ₐ[𝕜] (EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n) :=
  toMatrixOrthonormal (EuclideanSpace.basisFun n 𝕜) |>.symm.trans <|
    { toContinuousLinearMap with
      map_mul' := fun _ _ ↦ rfl
      map_star' := adjoint_toContinuousLinearMap }
/-
**Matrix.coe_toEuclideanCLM_eq_toEuclideanLin** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`
。
形式化陈述：∀ {𝕜 : Type u_1} {n : Type u_3} [inst : RCLike 𝕜] [inst_1 : Fintype n] [in
st_2 : DecidableEq n] (A : Matrix n n 𝕜),   ↑(Matrix.toEuclideanCLM A) = Matrix.
toEuclideanLin A
参数：A : Matrix n n 𝕜；Matrix.toEuclideanCLM A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
-/
lemma coe_toEuclideanCLM_eq_toEuclideanLin (A : Matrix n n 𝕜) :
    (toEuclideanCLM (n := n) (𝕜 := 𝕜) A : _ →ₗ[𝕜] _) = toEuclideanLin A :=
  rfl

@[simp]
/-
**Matrix.toEuclideanCLM_toLp** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {𝕜 : Type u_1} {n : Type u_3} [inst : RCLike 𝕜] [inst_1 : Fintype n] [in
st_2 : DecidableEq n] (A : Matrix n n 𝕜)   (x : n → 𝕜), (Matrix.toEuclideanCLM A
) (WithLp.toLp 2 x) = WithLp.toLp 2 (A.mulVec x)
参数：A : Matrix n n 𝕜；x : n → 𝕜；Matrix.toEuclideanCLM A；WithLp.toLp 2 x；A.mulVec x
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
-/
lemma toEuclideanCLM_toLp (A : Matrix n n 𝕜) (x : n → 𝕜) :
    toEuclideanCLM (n := n) (𝕜 := 𝕜) A (toLp _ x) = toLp _ (A *ᵥ x) := rfl

@[simp]
/-
**Matrix.ofLp_toEuclideanCLM** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {𝕜 : Type u_1} {n : Type u_3} [inst : RCLike 𝕜] [inst_1 : Fintype n] [in
st_2 : DecidableEq n] (A : Matrix n n 𝕜)   (x : EuclideanSpace 𝕜 n), ((Matrix.to
EuclideanCLM A) x).ofLp = A.mulVec x.ofLp
参数：A : Matrix n n 𝕜；x : EuclideanSpace 𝕜 n；(Matrix.toEuclideanCLM A) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
-/
lemma ofLp_toEuclideanCLM (A : Matrix n n 𝕜) (x : EuclideanSpace 𝕜 n) :
    ofLp (toEuclideanCLM (n := n) (𝕜 := 𝕜) A x) = A *ᵥ ofLp x := rfl

open scoped RealInnerProductSpace in
/-
**Matrix.inner_toEuclideanCLM** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {n : Type u_3} [inst : Fintype n] [inst_1 : DecidableEq n] (A : Matrix n
 n ℝ) (x y : EuclideanSpace ℝ n),   inner ℝ x ((Matrix.toEuclideanCLM A) y) = x.
ofLp ⬝ᵥ A.mulVec y.ofLp
参数：A : Matrix n n ℝ；x y : EuclideanSpace ℝ n；(Matrix.toEuclideanCLM A) y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.toMatrixOrthonormal_symm_apply`：∀ {𝕜 : Type u_1} {E : Type u_2
} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 
𝕜 E]   {n : Type u_6} [inst_3 …
· 使用定理 `Matrix.toLin_apply`：Matrix.toLin_apply [Fintype m] (M : Matrix m n R) (v
 : M₁) : Matrix.toLin v₁ v₂ M v = ∑ j, (M *ᵥ v₁.repr v) j • v₂ j
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.mulVec_eq_sum`：mulVec_eq_sum [Fintype n] (v : n -> α) (M : Matrix
 m n α) : M *ᵥ v = ∑ i, MulOpposite.op (v i) • Mᵀ i
· 使用定理 `OrthonormalBasis.coe_toBasis_repr_apply`：∀ {ι : Type u_1} {𝕜 : Type u_3}
 [inst : RCLike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : In
nerProductSpace 𝕜 E] [inst_3 …
· 使用定理 `IsCentralScalar.op_smul_eq_smul`：∀ {M : Type u_9} {α : Type u_10} {inst 
: SMul M α} {inst_1 : SMul Mᵐᵒᵖ α} [self : IsCentralScalar M α] (m : M) (a : α),
   MulOpposite.op m •…
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `EuclideanSpace.basisFun_apply`：basisFun_apply [DecidableEq ι] (i : ι) : 
basisFun ι 𝕜 i = EuclideanSpace.single i 1
· 使用引理 `WithLp.ofLp_sum`：ofLp_sum [AddCommGroup V] {ι : Type*} (s : Finset ι) (f
 : ι -> WithLp p V) : (∑ i in s, f i).ofLp = ∑ i in s, (f i).ofLp
· 使用定理 `conj_trivial`：∀ {R : Type u} [inst : CommSemiring R] [inst_1 : StarRing 
R] [TrivialStar R] (a : R), (starRingEnd R) a = a
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
（共 37 条，此处仅展示前 30 条）
-/
lemma inner_toEuclideanCLM (A : Matrix n n ℝ) (x y : EuclideanSpace ℝ n) :
    ⟪x, toEuclideanCLM (𝕜 := ℝ) A y⟫ = x ⬝ᵥ A *ᵥ y := by
  simp only [toEuclideanCLM, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
    LinearEquiv.invFun_eq_symm, LinearMap.coe_toContinuousLinearMap_symm, StarAlgEquiv.trans_apply,
    LinearMap.toMatrixOrthonormal_symm_apply, LinearMap.toMatrix_symm, StarAlgEquiv.coe_mk,
    StarRingEquiv.coe_mk, RingEquiv.coe_mk, Equiv.coe_fn_mk, LinearMap.coe_toContinuousLinearMap',
    toLin_apply, mulVec_eq_sum, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr, op_smul_eq_smul, Finset.sum_apply, Pi.smul_apply, transpose_apply,
    smul_eq_mul, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply, PiLp.inner_apply,
    ofLp_sum, ofLp_smul, PiLp.ofLp_single, RCLike.inner_apply, conj_trivial, dotProduct]
  congr with i
  rw [mul_comm (x.ofLp i)]
  simp [Pi.single_apply]

/-- An auxiliary definition used only to construct the true `NormedAddCommGroup` (and `Metric`)
/-
**Matrix.provided** 是 Mathlib 中的一个结构，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
structure provided by `Matrix.instMetricSpaceL2Op` and `Matrix.instNormedAddCommGroupL2Op`. -/
@[instance_reducible]
/-
**Matrix.l2OpNormedAddCommGroupAux** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：{𝕜 : Type u_1} →   {m : Type u_2} →     {n : Type u_3} → [RCLike 𝕜] → [Fin
type m] → [Fintype n] → [DecidableEq n] → NormedAddCommGroup (Matrix m n 𝕜)
参数：Matrix m n 𝕜。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K

--- 原说明 ---
An auxiliary definition used only to construct the true `NormedAddCommGroup` (an
d `Metric`)
structure provided by `Matrix.instMetricSpaceL2Op` and `Matrix.instNormedAddComm
GroupL2Op`.
-/
def l2OpNormedAddCommGroupAux : NormedAddCommGroup (Matrix m n 𝕜) :=
  @NormedAddCommGroup.induced ((Matrix m n 𝕜) ≃ₗ[𝕜] (EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 m)) _
    _ _ _ ContinuousLinearMap.toNormedAddCommGroup.toNormedAddGroup _ _ <|
    (toEuclideanLin.trans toContinuousLinearMap).injective

/-- An auxiliary definition used only to construct the true `NormedRing` (and `Metric`) structure
provided by `Matrix.instMetricSpaceL2Op` and `Matrix.instNormedRingL2Op`. -/
@[instance_reducible]
/-
**Matrix.l2OpNormedRingAux** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：{𝕜 : Type u_1} → {n : Type u_3} → [RCLike 𝕜] → [Fintype n] → [DecidableEq 
n] → NormedRing (Matrix n n 𝕜)
参数：Matrix n n 𝕜。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)

--- 原说明 ---
An auxiliary definition used only to construct the true `NormedRing` (and `Metri
c`) structure
provided by `Matrix.instMetricSpaceL2Op` and `Matrix.instNormedRingL2Op`.
-/
def l2OpNormedRingAux : NormedRing (Matrix n n 𝕜) :=
  @NormedRing.induced ((Matrix n n 𝕜) ≃⋆ₐ[𝕜] (EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n)) _
    _ _ _ ContinuousLinearMap.toNormedRing _ _ toEuclideanCLM.injective

open Bornology Filter
open scoped Topology Uniformity

/-- The metric on `Matrix m n 𝕜` arising from the operator norm given by the identification with
(continuous) linear maps of `EuclideanSpace`. -/
@[instance_reducible]
/-
**Matrix.instL2OpMetricSpace** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：{𝕜 : Type u_1} →   {m : Type u_2} →     {n : Type u_3} → [RCLike 𝕜] → [Fin
type m] → [Fintype n] → [DecidableEq n] → MetricSpace (Matrix m n 𝕜)
参数：Matrix m n 𝕜。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The metric on `Matrix m n 𝕜` arising from the operator norm given by the identif
ication with
(continuous) linear maps of `EuclideanSpace`.
-/
def instL2OpMetricSpace : MetricSpace (Matrix m n 𝕜) := by
  /- We first replace the topology so that we can automatically replace the uniformity using
  `IsUniformAddGroup.toUniformSpace_eq`. -/
  letI normed_add_comm_group : NormedAddCommGroup (Matrix m n 𝕜) :=
    { l2OpNormedAddCommGroupAux.replaceTopology <|
        (toEuclideanLin (𝕜 := 𝕜) (m := m) (n := n)).trans toContinuousLinearMap
        |>.toContinuousLinearEquiv.toHomeomorph.isInducing.eq_induced with
      norm := l2OpNormedAddCommGroupAux.norm
      dist_eq := l2OpNormedAddCommGroupAux.dist_eq }
  exact normed_add_comm_group.replaceUniformity <| by
    congr
    rw [← @IsUniformAddGroup.rightUniformSpace_eq _ (Matrix.instUniformSpace m n 𝕜) _ _]
    rw [@IsUniformAddGroup.rightUniformSpace_eq _ PseudoEMetricSpace.toUniformSpace _ _]

scoped[Matrix.Norms.L2Operator] attribute [instance] Matrix.instL2OpMetricSpace

open scoped Matrix.Norms.L2Operator

/-- The norm structure on `Matrix m n 𝕜` arising from the operator norm given by the identification
with (continuous) linear maps of `EuclideanSpace`. -/
@[instance_reducible]
/-
**Matrix.instL2OpNormedAddCommGroup** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：{𝕜 : Type u_1} →   {m : Type u_2} →     {n : Type u_3} → [RCLike 𝕜] → [Fin
type m] → [Fintype n] → [DecidableEq n] → NormedAddCommGroup (Matrix m n 𝕜)
参数：Matrix m n 𝕜。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The norm structure on `Matrix m n 𝕜` arising from the operator norm given by the
 identification
with (continuous) linear maps of `EuclideanSpace`.
-/
def instL2OpNormedAddCommGroup : NormedAddCommGroup (Matrix m n 𝕜) where
  norm := l2OpNormedAddCommGroupAux.norm
  dist_eq := l2OpNormedAddCommGroupAux.dist_eq

scoped[Matrix.Norms.L2Operator] attribute [instance] Matrix.instL2OpNormedAddCommGroup
/-
**Matrix.l2_opNorm_def** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {𝕜 : Type u_1} {m : Type u_2} {n : Type u_3} [inst : RCLike 𝕜] [inst_1 :
 Fintype m] [inst_2 : Fintype n]   [inst_3 : DecidableEq n] (A : Matrix m n 𝕜), 
‖A‖ = ‖(Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) A‖
参数：A : Matrix m n 𝕜；Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma l2_opNorm_def (A : Matrix m n 𝕜) :
    ‖A‖ = ‖(toEuclideanLin (𝕜 := 𝕜) (m := m) (n := n)).trans toContinuousLinearMap A‖ := rfl
/-
**Matrix.l2_opNNNorm_def** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {𝕜 : Type u_1} {m : Type u_2} {n : Type u_3} [inst : RCLike 𝕜] [inst_1 :
 Fintype m] [inst_2 : Fintype n]   [inst_3 : DecidableEq n] (A : Matrix m n 𝕜), 
‖A‖₊ = ‖(Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) A‖₊
参数：A : Matrix m n 𝕜；Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma l2_opNNNorm_def (A : Matrix m n 𝕜) :
    ‖A‖₊ = ‖(toEuclideanLin (𝕜 := 𝕜) (m := m) (n := n)).trans toContinuousLinearMap A‖₊ := rfl
/-
**Matrix.l2_opNorm_conjTranspose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {𝕜 : Type u_1} {m : Type u_2} {n : Type u_3} [inst : RCLike 𝕜] [inst_1 :
 Fintype m] [inst_2 : Fintype n]   [inst_3 : DecidableEq n] [inst_4 : DecidableE
q m] (A : Matrix m n 𝕜), ‖A.conjTranspose‖ = ‖A‖
参数：A : Matrix m n 𝕜。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.l2_opNorm_def`：∀ {𝕜 : Type u_1} {m : Type u_2} {n : Type u_3} [in
st : RCLike 𝕜] [inst_1 : Fintype m] [inst_2 : Fintype n]   [inst_3 : DecidableEq
 n] (A : M…
· 使用引理 `Matrix.toEuclideanLin_eq_toLin_orthonormal`：toEuclideanLin_eq_toLin_orth
onormal [Fintype m] : toEuclideanLin = toLin (basisFun n 𝕜).toBasis (basisFun m 
𝕜).toBasis
· 使用定理 `LinearEquiv.trans_apply`：trans_apply (c : M₁) : (e₁₂.trans e₂₃ : M₁ ≃ₛₗ[
σ₁₃] M₃) c = e₂₃ (e₁₂ c)
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用引理 `Matrix.toLin_conjTranspose`：Matrix.toLin_conjTranspose (A : Matrix m n 𝕜
) : toLin v₂.toBasis v₁.toBasis Aᴴ = adjoint (toLin v₁.toBasis v₂.toBasis A)
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `FiniteDimensional.complete`：FiniteDimensional.complete [FiniteDimensiona
l 𝕜 E] : CompleteSpace E
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `LinearMap.adjoint_toContinuousLinearMap`：adjoint_toContinuousLinearMap (
A : E ->ₗ[𝕜] F) : haveI
· 使用定理 `LinearIsometryEquiv.norm_map`：∀ {R : Type u_1} {R₂ : Type u_2} {E : Type
 u_5} {E₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   {σ₁₂ : R →+* 
R₂} {σ₂₁ : R₂ →+* …
-/
lemma l2_opNorm_conjTranspose [DecidableEq m] (A : Matrix m n 𝕜) : ‖Aᴴ‖ = ‖A‖ := by
  rw [l2_opNorm_def, toEuclideanLin_eq_toLin_orthonormal, LinearEquiv.trans_apply,
    toLin_conjTranspose, adjoint_toContinuousLinearMap]
  exact ContinuousLinearMap.adjoint.norm_map _
/-
**Matrix.l2_opNNNorm_conjTranspose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {𝕜 : Type u_1} {m : Type u_2} {n : Type u_3} [inst : RCLike 𝕜] [inst_1 :
 Fintype m] [inst_2 : Fintype n]   [inst_3 : DecidableEq n] [inst_4 : DecidableE
q m] (A : Matrix m n 𝕜), ‖A.conjTranspose‖₊ = ‖A‖₊
参数：A : Matrix m n 𝕜。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Matrix.l2_opNorm_conjTranspose`：∀ {𝕜 : Type u_1} {m : Type u_2} {n : Typ
e u_3} [inst : RCLike 𝕜] [inst_1 : Fintype m] [inst_2 : Fintype n]   [inst_3 : D
ecidableEq n] [inst_…
-/
lemma l2_opNNNorm_conjTranspose [DecidableEq m] (A : Matrix m n 𝕜) : ‖Aᴴ‖₊ = ‖A‖₊ :=
  Subtype.ext <| l2_opNorm_conjTranspose _
/-
**Matrix.l2_opNorm_conjTranspose_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {𝕜 : Type u_1} {m : Type u_2} {n : Type u_3} [inst : RCLike 𝕜] [inst_1 :
 Fintype m] [inst_2 : Fintype n]   [inst_3 : DecidableEq n] (A : Matrix m n 𝕜), 
‖A.conjTranspose * A‖ = ‖A‖ * ‖A‖
参数：A : Matrix m n 𝕜。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.l2_opNorm_def`：∀ {𝕜 : Type u_1} {m : Type u_2} {n : Type u_3} [in
st : RCLike 𝕜] [inst_1 : Fintype m] [inst_2 : Fintype n]   [inst_3 : DecidableEq
 n] (A : M…
· 使用引理 `Matrix.toEuclideanLin_eq_toLin_orthonormal`：toEuclideanLin_eq_toLin_orth
onormal [Fintype m] : toEuclideanLin = toLin (basisFun n 𝕜).toBasis (basisFun m 
𝕜).toBasis
· 使用定理 `LinearEquiv.trans_apply`：trans_apply (c : M₁) : (e₁₂.trans e₂₃ : M₁ ≃ₛₗ[
σ₁₃] M₃) c = e₂₃ (e₁₂ c)
· 使用定理 `Matrix.toLin_mul`：Matrix.toLin_mul [Finite l] [DecidableEq m] (A : Matri
x l m R) (B : Matrix m n R) : Matrix.toLin v₁ v₃ (A * B) = (Matrix.toLin v₂ v₃ A
).comp…
· 使用定理 `RingHomInvPair.instStarRingEnd`：∀ {R : Type u} [inst : CommSemiring R] [
inst_1 : StarRing R], RingHomInvPair (starRingEnd R) (starRingEnd R)
· 使用引理 `Matrix.toLin_conjTranspose`：Matrix.toLin_conjTranspose (A : Matrix m n 𝕜
) : toLin v₂.toBasis v₁.toBasis Aᴴ = adjoint (toLin v₁.toBasis v₂.toBasis A)
· 使用定理 `ContinuousLinearMap.norm_adjoint_comp_self`：norm_adjoint_comp_self (A : 
E ->L[𝕜] F) : ‖A† ∘L A‖ = ‖A‖ * ‖A‖
-/
lemma l2_opNorm_conjTranspose_mul_self (A : Matrix m n 𝕜) : ‖Aᴴ * A‖ = ‖A‖ * ‖A‖ := by
  classical
  rw [l2_opNorm_def, toEuclideanLin_eq_toLin_orthonormal, LinearEquiv.trans_apply,
    Matrix.toLin_mul (v₂ := (EuclideanSpace.basisFun m 𝕜).toBasis), toLin_conjTranspose]
  exact ContinuousLinearMap.norm_adjoint_comp_self _
/-
**Matrix.l2_opNNNorm_conjTranspose_mul_self** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {𝕜 : Type u_1} {m : Type u_2} {n : Type u_3} [inst : RCLike 𝕜] [inst_1 :
 Fintype m] [inst_2 : Fintype n]   [inst_3 : DecidableEq n] (A : Matrix m n 𝕜), 
‖A.conjTranspose * A‖₊ = ‖A‖₊ * ‖A‖₊
参数：A : Matrix m n 𝕜。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Matrix.l2_opNorm_conjTranspose_mul_self`：∀ {𝕜 : Type u_1} {m : Type u_2}
 {n : Type u_3} [inst : RCLike 𝕜] [inst_1 : Fintype m] [inst_2 : Fintype n]   [i
nst_3 : DecidableEq n] (A : M…
-/
lemma l2_opNNNorm_conjTranspose_mul_self (A : Matrix m n 𝕜) : ‖Aᴴ * A‖₊ = ‖A‖₊ * ‖A‖₊ :=
  Subtype.ext <| l2_opNorm_conjTranspose_mul_self _

-- note: with only a type ascription in the left-hand side, Lean picks the wrong norm.
/-
**Matrix.l2_opNorm_mulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {𝕜 : Type u_1} {m : Type u_2} {n : Type u_3} [inst : RCLike 𝕜] [inst_1 :
 Fintype m] [inst_2 : Fintype n]   [inst_3 : DecidableEq n] (A : Matrix m n 𝕜) (
x : EuclideanSpace 𝕜 n),   ‖(EuclideanSpace.equiv m 𝕜).symm (A.mulVec x.ofLp)‖ ≤
 ‖A‖ * ‖x‖
参数：A : Matrix m n 𝕜；x : EuclideanSpace 𝕜 n；EuclideanSpace.equiv m 𝕜；A.mulVec x.o
fLp。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.le_opNorm`：le_opNorm : ‖f x‖ <= ‖f‖ * ‖x‖
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
lemma l2_opNorm_mulVec (A : Matrix m n 𝕜) (x : EuclideanSpace 𝕜 n) :
    ‖(EuclideanSpace.equiv m 𝕜).symm <| A *ᵥ x‖ ≤ ‖A‖ * ‖x‖ :=
  toEuclideanLin (n := n) (m := m) (𝕜 := 𝕜) |>.trans toContinuousLinearMap A |>.le_opNorm x
/-
**Matrix.l2_opNNNorm_mulVec** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {𝕜 : Type u_1} {m : Type u_2} {n : Type u_3} [inst : RCLike 𝕜] [inst_1 :
 Fintype m] [inst_2 : Fintype n]   [inst_3 : DecidableEq n] (A : Matrix m n 𝕜) (
x : EuclideanSpace 𝕜 n),   ‖(EuclideanSpace.equiv m 𝕜).symm (A.mulVec x.ofLp)‖₊ 
≤ ‖A‖₊ * ‖x‖₊
参数：A : Matrix m n 𝕜；x : EuclideanSpace 𝕜 n；EuclideanSpace.equiv m 𝕜；A.mulVec x.o
fLp。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.l2_opNorm_mulVec`：∀ {𝕜 : Type u_1} {m : Type u_2} {n : Type u_3} 
[inst : RCLike 𝕜] [inst_1 : Fintype m] [inst_2 : Fintype n]   [inst_3 : Decidabl
eEq n] (A : M…
-/
lemma l2_opNNNorm_mulVec (A : Matrix m n 𝕜) (x : EuclideanSpace 𝕜 n) :
    ‖(EuclideanSpace.equiv m 𝕜).symm <| A *ᵥ x‖₊ ≤ ‖A‖₊ * ‖x‖₊ :=
  A.l2_opNorm_mulVec x
/-
**Matrix.l2_opNorm_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {𝕜 : Type u_1} {m : Type u_2} {n : Type u_3} {l : Type u_4} [inst : RCLi
ke 𝕜] [inst_1 : Fintype m]   [inst_2 : Fintype n] [inst_3 : DecidableEq n] [inst
_4 : Fintype l] [inst_5 : DecidableEq l] (A : Matrix m n 𝕜)   (B : Matrix n l 𝕜)
, ‖A * B‖ ≤ ‖A‖ * ‖B‖
参数：A : Matrix m n 𝕜；B : Matrix n l 𝕜。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `ContinuousLinearMap.opNorm_comp_le`：opNorm_comp_le (f : E ->SL[σ₁₂] F) :
 ‖h.comp f‖ <= ‖h‖ * ‖f‖
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Matrix.toLin'_mul`：∀ {R : Type u_1} [inst : CommSemiring R] {l : Type u_
3} {m : Type u_4} {n : Type u_5} [inst_1 : DecidableEq n]   [inst_2 : Fintype n]
 [inst_…
-/
lemma l2_opNorm_mul (A : Matrix m n 𝕜) (B : Matrix n l 𝕜) :
    ‖A * B‖ ≤ ‖A‖ * ‖B‖ := by
  simp only [l2_opNorm_def]
  have := (toEuclideanLin (n := n) (m := m) (𝕜 := 𝕜) ≪≫ₗ toContinuousLinearMap) A
    |>.opNorm_comp_le <| (toEuclideanLin (n := l) (m := n) (𝕜 := 𝕜) ≪≫ₗ toContinuousLinearMap) B
  convert! this
  ext1 x
  exact congr(toLp 2 ($(Matrix.toLin'_mul A B) x))
/-
**Matrix.l2_opNNNorm_mul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {𝕜 : Type u_1} {m : Type u_2} {n : Type u_3} {l : Type u_4} [inst : RCLi
ke 𝕜] [inst_1 : Fintype m]   [inst_2 : Fintype n] [inst_3 : DecidableEq n] [inst
_4 : Fintype l] [inst_5 : DecidableEq l] (A : Matrix m n 𝕜)   (B : Matrix n l 𝕜)
, ‖A * B‖₊ ≤ ‖A‖₊ * ‖B‖₊
参数：A : Matrix m n 𝕜；B : Matrix n l 𝕜。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.l2_opNorm_mul`：∀ {𝕜 : Type u_1} {m : Type u_2} {n : Type u_3} {l 
: Type u_4} [inst : RCLike 𝕜] [inst_1 : Fintype m]   [inst_2 : Fintype n] [inst_
3 : Decida…
-/
lemma l2_opNNNorm_mul (A : Matrix m n 𝕜) (B : Matrix n l 𝕜) : ‖A * B‖₊ ≤ ‖A‖₊ * ‖B‖₊ :=
  l2_opNorm_mul A B
/-
**Matrix.l2_opNorm_toEuclideanCLM** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {𝕜 : Type u_1} {n : Type u_3} [inst : RCLike 𝕜] [inst_1 : Fintype n] [in
st_2 : DecidableEq n] (A : Matrix n n 𝕜),   ‖Matrix.toEuclideanCLM A‖ = ‖A‖
参数：A : Matrix n n 𝕜。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
-/
lemma l2_opNorm_toEuclideanCLM (A : Matrix n n 𝕜) :
    ‖toEuclideanCLM (n := n) (𝕜 := 𝕜) A‖ = ‖A‖ := rfl

@[simp]
/-
**Matrix.l2_opNorm_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {𝕜 : Type u_1} {n : Type u_3} [inst : RCLike 𝕜] [inst_1 : Fintype n] [in
st_2 : DecidableEq n] (v : n → 𝕜),   ‖Matrix.diagonal v‖ = ‖v‖
参数：v : n → 𝕜。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.l2_opNorm_toEuclideanCLM`：∀ {𝕜 : Type u_1} {n : Type u_3} [inst :
 RCLike 𝕜] [inst_1 : Fintype n] [inst_2 : DecidableEq n] (A : Matrix n n 𝕜),   ‖
Matrix.toEuclideanCLM…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `ContinuousLinearMap.opNorm_le_bound`：opNorm_le_bound (f : E ->SL[σ₁₂] F)
 {M : Real} (hMp : 0 <= M) (hM : forall x, ‖f x‖ <= M * ‖x‖) : ‖f‖ <= M
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `sq_le_sq₀`：sq_le_sq₀ (ha : 0 <= a) (hb : 0 <= b) : a ^ 2 <= b ^ 2 ↔ a <=
 b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `EuclideanSpace.norm_sq_eq`：EuclideanSpace.norm_sq_eq {𝕜 : Type*} [RCLike
 𝕜] {n : Type*} [Fintype n] (x : EuclideanSpace 𝕜 n) : ‖x‖ ^ 2 = ∑ i, ‖x i‖ ^ 2
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Matrix.mulVec_diagonal`：mulVec_diagonal [Fintype m] [DecidableEq m] (v w
 : m -> α) (x : m) : (diagonal v *ᵥ w) x = v x * w x
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
（共 54 条，此处仅展示前 30 条）
-/
lemma l2_opNorm_diagonal (v : n → 𝕜) : ‖(diagonal v : Matrix n n 𝕜)‖ = ‖v‖ := by
  set T := toEuclideanCLM (n := n) (𝕜 := 𝕜) (diagonal v)
  rw [← l2_opNorm_toEuclideanCLM]
  refine le_antisymm ?_ ?_
  · refine T.opNorm_le_bound (norm_nonneg _) fun x ↦ ?_
    refine (sq_le_sq₀ (by positivity) (by positivity)).mp ?_
    simp only [(T x).norm_sq_eq, ofLp_toEuclideanCLM, mulVec_diagonal, norm_mul, T]
    calc _ ≤ _ := Finset.sum_le_sum fun i _ ↦ by grw [mul_pow, norm_le_pi_norm v i]
      _ = _ := by simp [mul_pow, EuclideanSpace.norm_sq_eq x, Finset.mul_sum]
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg T)).mpr fun i ↦ ?_
    calc _ = ‖T (toLp 2 (Pi.single i (1 : 𝕜)))‖ := by
          rw [toEuclideanCLM_toLp (diagonal v) (Pi.single i (1 : 𝕜))]
          simp
      _ ≤ _ := by grw [T.le_opNorm]; simp

@[simp]
/-
**Matrix.l2_opNNNorm_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {𝕜 : Type u_1} {n : Type u_3} [inst : RCLike 𝕜] [inst_1 : Fintype n] [in
st_2 : DecidableEq n] (v : n → 𝕜),   ‖Matrix.diagonal v‖₊ = ‖v‖₊
参数：v : n → 𝕜。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Matrix.l2_opNorm_diagonal`：∀ {𝕜 : Type u_1} {n : Type u_3} [inst : RCLik
e 𝕜] [inst_1 : Fintype n] [inst_2 : DecidableEq n] (v : n → 𝕜),   ‖Matrix.diagon
al v‖ = ‖v‖
-/
lemma l2_opNNNorm_diagonal (v : n → 𝕜) : ‖(diagonal v : Matrix n n 𝕜)‖₊ = ‖v‖₊ :=
  Subtype.ext <| l2_opNorm_diagonal (n := n) (𝕜 := 𝕜) v

/-- The normed algebra structure on `Matrix n n 𝕜` arising from the operator norm given by the
identification with (continuous) linear endomorphisms of `EuclideanSpace 𝕜 n`. -/
@[instance_reducible]
/-
**Matrix.instL2OpNormedSpace** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：{𝕜 : Type u_1} →   {m : Type u_2} →     {n : Type u_3} →       [inst : RCL
ike 𝕜] →         [inst_1 : Fintype m] → [inst_2 : Fintype n] → [inst_3 : Decidab
leEq n] → NormedSpace 𝕜 (Matrix m n 𝕜)
参数：Matrix m n 𝕜。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The normed algebra structure on `Matrix n n 𝕜` arising from the operator norm gi
ven by the
identification with (continuous) linear endomorphisms of `EuclideanSpace 𝕜 n`.
-/
def instL2OpNormedSpace : NormedSpace 𝕜 (Matrix m n 𝕜) where
  norm_smul_le r x := by
    rw [l2_opNorm_def, map_smul]
    exact norm_smul_le r ((toEuclideanLin (𝕜 := 𝕜) (m := m) (n := n)).trans toContinuousLinearMap x)

scoped[Matrix.Norms.L2Operator] attribute [instance] Matrix.instL2OpNormedSpace

/-- The normed ring structure on `Matrix n n 𝕜` arising from the operator norm given by the
identification with (continuous) linear endomorphisms of `EuclideanSpace 𝕜 n`. -/
@[instance_reducible]
/-
**Matrix.instL2OpNormedRing** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：{𝕜 : Type u_1} → {n : Type u_3} → [RCLike 𝕜] → [Fintype n] → [DecidableEq 
n] → NormedRing (Matrix n n 𝕜)
参数：Matrix n n 𝕜。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The normed ring structure on `Matrix n n 𝕜` arising from the operator norm given
 by the
identification with (continuous) linear endomorphisms of `EuclideanSpace 𝕜 n`.
-/
def instL2OpNormedRing : NormedRing (Matrix n n 𝕜) where
  dist_eq := l2OpNormedRingAux.dist_eq
  norm_mul_le := l2OpNormedRingAux.norm_mul_le

scoped[Matrix.Norms.L2Operator] attribute [instance] Matrix.instL2OpNormedRing

/-- This is the same as `Matrix.l2_opNorm_def`, but with a more bundled RHS for square matrices. -/
/-
**Matrix.cstar_norm_def** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {𝕜 : Type u_1} {n : Type u_3} [inst : RCLike 𝕜] [inst_1 : Fintype n] [in
st_2 : DecidableEq n] (A : Matrix n n 𝕜),   ‖A‖ = ‖Matrix.toEuclideanCLM A‖
参数：A : Matrix n n 𝕜。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the same as `Matrix.l2_opNorm_def`, but with a more bundled RHS for squa
re matrices.
-/
lemma cstar_norm_def (A : Matrix n n 𝕜) : ‖A‖ = ‖toEuclideanCLM (n := n) (𝕜 := 𝕜) A‖ := rfl

/-- This is the same as `Matrix.l2_opNNNorm_def`, but with a more bundled RHS for square
matrices. -/
/-
**Matrix.cstar_nnnorm_def** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {𝕜 : Type u_1} {n : Type u_3} [inst : RCLike 𝕜] [inst_1 : Fintype n] [in
st_2 : DecidableEq n] (A : Matrix n n 𝕜),   ‖A‖₊ = ‖Matrix.toEuclideanCLM A‖₊
参数：A : Matrix n n 𝕜。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the same as `Matrix.l2_opNNNorm_def`, but with a more bundled RHS for sq
uare
matrices.
-/
lemma cstar_nnnorm_def (A : Matrix n n 𝕜) : ‖A‖₊ = ‖toEuclideanCLM (n := n) (𝕜 := 𝕜) A‖₊ := rfl

/-- The normed algebra structure on `Matrix n n 𝕜` arising from the operator norm given by the
identification with (continuous) linear endomorphisms of `EuclideanSpace 𝕜 n`. -/
@[instance_reducible]
/-
**Matrix.instL2OpNormedAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：{𝕜 : Type u_1} →   {n : Type u_3} → [inst : RCLike 𝕜] → [inst_1 : Fintype 
n] → [inst_2 : DecidableEq n] → NormedAlgebra 𝕜 (Matrix n n 𝕜)
参数：Matrix n n 𝕜。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The normed algebra structure on `Matrix n n 𝕜` arising from the operator norm gi
ven by the
identification with (continuous) linear endomorphisms of `EuclideanSpace 𝕜 n`.
-/
def instL2OpNormedAlgebra : NormedAlgebra 𝕜 (Matrix n n 𝕜) where
  norm_smul_le := norm_smul_le

scoped[Matrix.Norms.L2Operator] attribute [instance] Matrix.instL2OpNormedAlgebra

/-- The operator norm on `Matrix n n 𝕜` given by the identification with (continuous) linear
endomorphisms of `EuclideanSpace 𝕜 n` makes it into a `L2OpRing`. -/
/-
**Matrix.instCStarRing** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：∀ {𝕜 : Type u_1} {n : Type u_3} [inst : RCLike 𝕜] [inst_1 : Fintype n] [in
st_2 : DecidableEq n],   CStarRing (Matrix n n 𝕜)
参数：Matrix n n 𝕜。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.l2_opNorm_conjTranspose_mul_self`：∀ {𝕜 : Type u_1} {m : Type u_2}
 {n : Type u_3} [inst : RCLike 𝕜] [inst_1 : Fintype m] [inst_2 : Fintype n]   [i
nst_3 : DecidableEq n] (A : M…

--- 原说明 ---
The operator norm on `Matrix n n 𝕜` given by the identification with (continuous
) linear
endomorphisms of `EuclideanSpace 𝕜 n` makes it into a `L2OpRing`.
-/
lemma instCStarRing : CStarRing (Matrix n n 𝕜) where
  norm_mul_self_le M := le_of_eq <| Eq.symm <| l2_opNorm_conjTranspose_mul_self M

scoped[Matrix.Norms.L2Operator] attribute [instance] Matrix.instCStarRing

/-- The matrices `Matrix n n ℂ` with the L2 operator norm form a `CStarAlgebra`. -/
/-
**Matrix.instCStarAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：{n : Type u_6} → [Fintype n] → [DecidableEq n] → CStarAlgebra (Matrix n n 
ℂ)
参数：Matrix n n ℂ。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.instCStarRing`：∀ {𝕜 : Type u_1} {n : Type u_3} [inst : RCLike 𝕜] 
[inst_1 : Fintype n] [inst_2 : DecidableEq n],   CStarRing (Matrix n n 𝕜)

--- 原说明 ---
The matrices `Matrix n n ℂ` with the L2 operator norm form a `CStarAlgebra`.
-/
@[instance_reducible] noncomputable def instCStarAlgebra {n : Type*} [Fintype n] [DecidableEq n] :
    CStarAlgebra (Matrix n n ℂ) where

scoped[Matrix.Norms.L2Operator] attribute [instance] Matrix.instCStarAlgebra

end Matrix

end L2OpNorm

