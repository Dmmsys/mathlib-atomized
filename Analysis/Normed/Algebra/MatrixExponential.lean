/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.ZPow
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Topology.UniformSpace.Matrix
public import Mathlib.Topology.Instances.Matrix

/-!
# Lemmas about the matrix exponential

In this file, we provide results about `NormedSpace.exp` on `Matrix`s
over a topological or normed algebra.
Note that generic results over all topological spaces such as `NormedSpace.exp_zero`
can be used on matrices without issue, so are not repeated here.
The topological results specific to matrices are:

* `Matrix.exp_transpose`
* `Matrix.exp_conjTranspose`
* `Matrix.exp_diagonal`
* `Matrix.exp_blockDiagonal`
* `Matrix.exp_blockDiagonal'`

Lemmas like `NormedSpace.exp_add_of_commute` require a canonical norm on the type;
while there are multiple sensible choices for the norm of a `Matrix` (`Matrix.normedAddCommGroup`,
`Matrix.frobeniusNormedAddCommGroup`, `Matrix.linftyOpNormedAddCommGroup`), none of them
are canonical. In an application where a particular norm is chosen using
`attribute [local instance]`, then the usual lemmas about `NormedSpace.exp` are fine.
When choosing a norm is undesirable, the results in this file can be used.

In this file, we copy across the lemmas about `NormedSpace.exp`,
but hide the requirement for a norm inside the proof.

* `Matrix.exp_add_of_commute`
* `Matrix.exp_sum_of_commute`
* `Matrix.exp_nsmul`
* `Matrix.isUnit_exp`
* `Matrix.exp_units_conj`
* `Matrix.exp_units_conj'`

Additionally, we prove some results about `matrix.has_inv` and `matrix.div_inv_monoid`, as the
results for general rings are instead stated about `Ring.inverse`:

* `Matrix.exp_neg`
* `Matrix.exp_zsmul`
* `Matrix.exp_conj`
* `Matrix.exp_conj'`

## TODO

* Show that `Matrix.det (NormedSpace.exp A) = NormedSpace.exp (Matrix.trace A)`

## References

* https://en.wikipedia.org/wiki/Matrix_exponential
-/

public section

open scoped Matrix

open NormedSpace -- For `exp`.

variable {m n : Type*} {n' : m → Type*} {α 𝔸 : Type*}

namespace Matrix

section Topological

section Ring

variable [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [∀ i, Fintype (n' i)]
  [∀ i, DecidableEq (n' i)] [Ring 𝔸] [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸]
  [T2Space 𝔸]

/-
**Matrix.exp_diagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：exp_diagonal [Algebra Rat 𝔸] (v : m -> 𝔸) : exp (diagonal v) = diagonal (e
xp v)
参数：v : m -> 𝔸。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.topologicalRing`：∀ {n : Type u_5} {R : Type u_8} [inst : Topologi
calSpace R] [inst_1 : Fintype n] [inst_2 : NonUnitalNonAssocRing R]   [IsTopolog
icalRing R],…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `NormedSpace.exp_eq_tsum_rat`：exp_eq_tsum_rat [Algebra Rat 𝔸] : exp = fun
 x : 𝔸 => ∑' n : Nat, (n !⁻¹ : Rat) • x ^ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.diagonal_pow`：diagonal_pow [Fintype n] [DecidableEq n] (v : n -> 
α) (k : Nat) : diagonal v ^ k = diagonal (v ^ k)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem exp_diagonal [Algebra ℚ 𝔸] (v : m → 𝔸) : exp (diagonal v) = diagonal (exp v) := by
  simp_rw [exp_eq_tsum_rat, diagonal_pow, ← diagonal_smul, ← diagonal_tsum]
/-
**Matrix.exp_blockDiagonal** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：exp_blockDiagonal [Algebra Rat 𝔸] (v : m -> Matrix n n 𝔸) : exp (blockDiag
onal v) = blockDiagonal (exp v)
参数：v : m -> Matrix n n 𝔸。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.topologicalRing`：∀ {n : Type u_5} {R : Type u_8} [inst : Topologi
calSpace R] [inst_1 : Fintype n] [inst_2 : NonUnitalNonAssocRing R]   [IsTopolog
icalRing R],…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `NormedSpace.exp_eq_tsum_rat`：exp_eq_tsum_rat [Algebra Rat 𝔸] : exp = fun
 x : 𝔸 => ∑' n : Nat, (n !⁻¹ : Rat) • x ^ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem exp_blockDiagonal [Algebra ℚ 𝔸] (v : m → Matrix n n 𝔸) :
    exp (blockDiagonal v) = blockDiagonal (exp v) := by
  simp_rw [exp_eq_tsum_rat, ← blockDiagonal_pow, ← blockDiagonal_smul, ← blockDiagonal_tsum]
/-
**Matrix.exp_blockDiagonal'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：exp_blockDiagonal' [Algebra Rat 𝔸] (v : forall i, Matrix (n' i) (n' i) 𝔸) 
: exp (blockDiagonal' v) = blockDiagonal' (exp v)
参数：v : forall i, Matrix (n' i) (n' i) 𝔸。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.topologicalRing`：∀ {n : Type u_5} {R : Type u_8} [inst : Topologi
calSpace R] [inst_1 : Fintype n] [inst_2 : NonUnitalNonAssocRing R]   [IsTopolog
icalRing R],…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `NormedSpace.exp_eq_tsum_rat`：exp_eq_tsum_rat [Algebra Rat 𝔸] : exp = fun
 x : 𝔸 => ∑' n : Nat, (n !⁻¹ : Rat) • x ^ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem exp_blockDiagonal' [Algebra ℚ 𝔸] (v : ∀ i, Matrix (n' i) (n' i) 𝔸) :
    exp (blockDiagonal' v) = blockDiagonal' (exp v) := by
  simp_rw [exp_eq_tsum_rat, ← blockDiagonal'_pow, ← blockDiagonal'_smul, ← blockDiagonal'_tsum]
/-
**Matrix.exp_conjTranspose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：exp_conjTranspose [StarRing 𝔸] [ContinuousStar 𝔸] (A : Matrix m m 𝔸) : exp
 Aᴴ = (exp A)ᴴ
参数：A : Matrix m m 𝔸。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.topologicalRing`：∀ {n : Type u_5} {R : Type u_8} [inst : Topologi
calSpace R] [inst_1 : Fintype n] [inst_2 : NonUnitalNonAssocRing R]   [IsTopolog
icalRing R],…
· 使用定理 `NormedSpace.star_exp`：star_exp [T2Space 𝔸] [StarRing 𝔸] [ContinuousStar 
𝔸] (x : 𝔸) : star (exp x) = exp (star x)
· 使用定理 `instT2SpaceMatrix`：∀ {m : Type u_4} {n : Type u_5} {R : Type u_8} [inst 
: TopologicalSpace R] [T2Space R], T2Space (Matrix m n R)
· 使用定理 `instContinuousStarMatrix`：∀ {m : Type u_4} {R : Type u_8} [inst : Topolo
gicalSpace R] [inst_1 : Star R] [ContinuousStar R],   ContinuousStar (Matrix m m
 R)
-/
theorem exp_conjTranspose [StarRing 𝔸] [ContinuousStar 𝔸] (A : Matrix m m 𝔸) :
    exp Aᴴ = (exp A)ᴴ :=
  (star_exp A).symm
/-
**Matrix.IsHermitian.exp** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsHermitian`。
形式化陈述：∀ {m : Type u_1} {𝔸 : Type u_5} [inst : Fintype m] [inst_1 : DecidableEq m
] [inst_2 : Ring 𝔸]   [inst_3 : TopologicalSpace 𝔸] [inst_4 : IsTopologicalRing 
𝔸] [T2Space 𝔸] [inst_6 : StarRing 𝔸] [ContinuousStar 𝔸]   {A : Matrix m m 𝔸}, A.
IsHermitian → (NormedSpace.exp A).IsHermitian
参数：NormedSpace.exp A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.topologicalRing`：∀ {n : Type u_5} {R : Type u_8} [inst : Topologi
calSpace R] [inst_1 : Fintype n] [inst_2 : NonUnitalNonAssocRing R]   [IsTopolog
icalRing R],…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.exp_conjTranspose`：exp_conjTranspose [StarRing 𝔸] [ContinuousStar
 𝔸] (A : Matrix m m 𝔸) : exp Aᴴ = (exp A)ᴴ
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem IsHermitian.exp [StarRing 𝔸] [ContinuousStar 𝔸] {A : Matrix m m 𝔸} (h : A.IsHermitian) :
    (exp A).IsHermitian :=
  (exp_conjTranspose _).symm.trans <| congr_arg _ h
/-
**Matrix.BlockTriangular.exp** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.BlockTriangular`。
形式化陈述：∀ {m : Type u_1} {α : Type u_4} {𝔸 : Type u_5} [inst : Fintype m] [inst_1 
: DecidableEq m] [inst_2 : Ring 𝔸]   [inst_3 : TopologicalSpace 𝔸] [inst_4 : IsT
opologicalRing 𝔸] [T2Space 𝔸] [inst_6 : LinearOrder α] [Algebra ℚ 𝔸]   {M : Matr
ix m m 𝔸} {b : m → α}, M.BlockTriangular b → (NormedSpace.exp M).BlockTriangular
 b
参数：NormedSpace.exp M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedSpace.exp_mem`：exp_mem {R S : Type*} [Monoid R] [SMul Rat R] [MulA
ction R 𝔸] [Algebra Rat 𝔸] [IsScalarTower Rat R 𝔸] [SetLike S 𝔸] [SubsemiringCla
ss S 𝔸] […
· 使用定理 `Matrix.topologicalRing`：∀ {n : Type u_5} {R : Type u_8} [inst : Topologi
calSpace R] [inst_1 : Fintype n] [inst_2 : NonUnitalNonAssocRing R]   [IsTopolog
icalRing R],…
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `isClosed_setOfPred_blockTriangular`：isClosed_setOfPred_blockTriangular {
α : Type*} {b : m -> α} [LinearOrder α] [Zero R] [T2Space R] : IsClosed {M : Mat
rix m m R | M.BlockTrian…
-/
theorem BlockTriangular.exp [LinearOrder α] [Algebra ℚ 𝔸] {M : Matrix m m 𝔸} {b : m → α}
    (hM : BlockTriangular M b) :
    (exp M).BlockTriangular b :=
  exp_mem (s := blockTriangularSubalgebra ℚ _ b) isClosed_setOfPred_blockTriangular hM

end Ring

section CommRing

variable [Fintype m] [DecidableEq m] [CommRing 𝔸] [TopologicalSpace 𝔸]
  [IsTopologicalRing 𝔸] [Algebra ℚ 𝔸] [T2Space 𝔸]

/-
**Matrix.exp_transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：exp_transpose (A : Matrix m m 𝔸) : exp Aᵀ = (exp A)ᵀ
参数：A : Matrix m m 𝔸。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.topologicalRing`：∀ {n : Type u_5} {R : Type u_8} [inst : Topologi
calSpace R] [inst_1 : Fintype n] [inst_2 : NonUnitalNonAssocRing R]   [IsTopolog
icalRing R],…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `NormedSpace.exp_eq_tsum_rat`：exp_eq_tsum_rat [Algebra Rat 𝔸] : exp = fun
 x : 𝔸 => ∑' n : Nat, (n !⁻¹ : Rat) • x ^ n
· 使用定理 `Matrix.transpose_tsum`：Matrix.transpose_tsum [T2Space R] {f : X -> Matri
x m n R} : (∑'[L] x, f x)ᵀ = ∑'[L] x, (f x)ᵀ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.transpose_pow`：transpose_pow [CommSemiring α] [Fintype m] [Decida
bleEq m] (M : Matrix m m α) (k : Nat) : (M ^ k)ᵀ = Mᵀ ^ k
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem exp_transpose (A : Matrix m m 𝔸) : exp Aᵀ = (exp A)ᵀ := by
  simp_rw [exp_eq_tsum_rat, transpose_tsum, transpose_smul, transpose_pow]
/-
**Matrix.IsSymm.exp** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsSymm`。
形式化陈述：∀ {m : Type u_1} {𝔸 : Type u_5} [inst : Fintype m] [inst_1 : DecidableEq m
] [inst_2 : CommRing 𝔸]   [inst_3 : TopologicalSpace 𝔸] [inst_4 : IsTopologicalR
ing 𝔸] [Algebra ℚ 𝔸] [T2Space 𝔸] {A : Matrix m m 𝔸},   A.IsSymm → (NormedSpace.e
xp A).IsSymm
参数：NormedSpace.exp A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.topologicalRing`：∀ {n : Type u_5} {R : Type u_8} [inst : Topologi
calSpace R] [inst_1 : Fintype n] [inst_2 : NonUnitalNonAssocRing R]   [IsTopolog
icalRing R],…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.exp_transpose`：exp_transpose (A : Matrix m m 𝔸) : exp Aᵀ = (exp A
)ᵀ
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem IsSymm.exp {A : Matrix m m 𝔸} (h : A.IsSymm) : (exp A).IsSymm :=
  (exp_transpose _).symm.trans <| congr_arg _ h

end CommRing

end Topological

section Normed

variable [Fintype m] [DecidableEq m] [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]

set_option backward.isDefEq.respectTransparency false in
nonrec theorem exp_add_of_commute (A B : Matrix m m 𝔸) (h : Commute A B) :
    exp (A + B) = exp A * exp B :=
  open scoped Norms.Operator in exp_add_of_commute h

set_option backward.isDefEq.respectTransparency false in
open scoped Function in -- required for scoped `on` notation
nonrec theorem exp_sum_of_commute {ι} (s : Finset ι) (f : ι → Matrix m m 𝔸)
    (h : (s : Set ι).Pairwise (Commute on f)) :
    exp (∑ i ∈ s, f i) =
      s.noncommProd (fun i => exp (f i)) fun _ hi _ hj _ => (h.of_refl hi hj).exp :=
  open scoped Norms.Operator in exp_sum_of_commute s f h

set_option backward.isDefEq.respectTransparency false in
nonrec theorem exp_nsmul (n : ℕ) (A : Matrix m m 𝔸) : exp (n • A) = exp A ^ n :=
  open scoped Norms.Operator in exp_nsmul n A

set_option backward.isDefEq.respectTransparency false in
nonrec theorem isUnit_exp (A : Matrix m m 𝔸) : IsUnit (exp A) :=
  open scoped Norms.Operator in isUnit_exp A

set_option backward.isDefEq.respectTransparency false in
-- TODO: without disabling this instance we get a timeout, see lean4#10414:
-- https://github.com/leanprover/lean4/issues/10414
-- and zulip discussion at
-- https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Coercion.20instance.20problems.20with.20matrix.20exponential/with/539770030
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
nonrec theorem exp_units_conj (U : (Matrix m m 𝔸)ˣ) (A : Matrix m m 𝔸) :
    exp (U * A * U⁻¹) = U * exp A * U⁻¹ :=
  open scoped Norms.Operator in exp_units_conj U A

-- TODO: without disabling this instance we get a timeout, see lean4#10414:
-- https://github.com/leanprover/lean4/issues/10414
-- and zulip discussion at
-- https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Coercion.20instance.20problems.20with.20matrix.20exponential/with/539770030
attribute [-instance] Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
/-
**Matrix.exp_units_conj'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：exp_units_conj' (U : (Matrix m m 𝔸)ˣ) (A : Matrix m m 𝔸) : exp (U⁻¹ * A * 
U) = U⁻¹ * exp A * U
参数：U : (Matrix m m 𝔸)ˣ；A : Matrix m m 𝔸。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.exp_units_conj`：∀ {m : Type u_1} {𝔸 : Type u_5} [inst : Fintype m
] [inst_1 : DecidableEq m] [inst_2 : NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]   [Comple
teSpace 𝔸] …
-/
theorem exp_units_conj' (U : (Matrix m m 𝔸)ˣ) (A : Matrix m m 𝔸) :
    exp (U⁻¹ * A * U) = U⁻¹ * exp A * U :=
  exp_units_conj U⁻¹ A

end Normed

section NormedComm

variable [Fintype m] [DecidableEq m]
  [NormedCommRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]

set_option backward.isDefEq.respectTransparency false in
/-
**Matrix.exp_neg** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：exp_neg (A : Matrix m m 𝔸) : exp (-A) = (exp A)⁻¹
参数：A : Matrix m m 𝔸。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.topologicalRing`：∀ {n : Type u_5} {R : Type u_8} [inst : Topologi
calSpace R] [inst_1 : Fintype n] [inst_2 : NonUnitalNonAssocRing R]   [IsTopolog
icalRing R],…
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.nonsing_inv_eq_ringInverse`：nonsing_inv_eq_ringInverse : A⁻¹ = A⁻
¹ʳ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ring.inverse_exp`：∀ {𝔸 : Type u_1} [inst : NormedRing 𝔸] [NormedAlgebra 
ℚ 𝔸] [CompleteSpace 𝔸] (x : 𝔸),   Ring.inverse (NormedSpace.exp x) = NormedSpace
.exp (…
· 使用定理 `Matrix.instCompleteSpace`：∀ (m : Type u_1) (n : Type u_2) (𝕜 : Type u_3)
 [inst : UniformSpace 𝕜] [CompleteSpace 𝕜], CompleteSpace (Matrix m n 𝕜)
-/
theorem exp_neg (A : Matrix m m 𝔸) : exp (-A) = (exp A)⁻¹ := by
  rw [nonsing_inv_eq_ringInverse]
  open scoped Norms.Operator in exact (Ring.inverse_exp A).symm
/-
**Matrix.exp_zsmul** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：exp_zsmul (z : Int) (A : Matrix m m 𝔸) : exp (z • A) = exp A ^ z
参数：z : Int；A : Matrix m m 𝔸。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.topologicalRing`：∀ {n : Type u_5} {R : Type u_8} [inst : Topologi
calSpace R] [inst_1 : Fintype n] [inst_2 : NonUnitalNonAssocRing R]   [IsTopolog
icalRing R],…
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Int.eq_nat_or_neg`：∀ (a : ℤ), ∃ n, a = ↑n ∨ a = -↑n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `natCast_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G) (n : ℕ),
 ↑n • a = n • a
· 使用定理 `Matrix.exp_nsmul`：∀ {m : Type u_1} {𝔸 : Type u_5} [inst : Fintype m] [in
st_1 : DecidableEq m] [inst_2 : NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]   [CompleteSpa
ce 𝔸] …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Matrix.isUnit_iff_isUnit_det`：isUnit_iff_isUnit_det : IsUnit A ↔ IsUnit 
A.det
· 使用定理 `Matrix.isUnit_exp`：∀ {m : Type u_1} {𝔸 : Type u_5} [inst : Fintype m] [i
nst_1 : DecidableEq m] [inst_2 : NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]   [CompleteSp
ace 𝔸] …
· 使用定理 `Matrix.zpow_neg`：∀ {n' : Type u_1} [inst : DecidableEq n'] [inst_1 : Fin
type n'] {R : Type u_2} [inst_2 : CommRing R]   {A : Matrix n' n' R}, IsUnit A.d
et → …
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `Matrix.exp_neg`：exp_neg (A : Matrix m m 𝔸) : exp (-A) = (exp A)⁻¹
-/
theorem exp_zsmul (z : ℤ) (A : Matrix m m 𝔸) : exp (z • A) = exp A ^ z := by
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · rw [zpow_natCast, natCast_zsmul, exp_nsmul]
  · have : IsUnit (exp A).det := (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_exp _)
    rw [Matrix.zpow_neg this, zpow_natCast, neg_smul, exp_neg, natCast_zsmul, exp_nsmul]
/-
**Matrix.exp_conj** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：exp_conj (U : Matrix m m 𝔸) (A : Matrix m m 𝔸) (hy : IsUnit U) : exp (U * 
A * U⁻¹) = U * exp A * U⁻¹
参数：U : Matrix m m 𝔸；A : Matrix m m 𝔸；hy : IsUnit U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.topologicalRing`：∀ {n : Type u_5} {R : Type u_8} [inst : Topologi
calSpace R] [inst_1 : Fintype n] [inst_2 : NonUnitalNonAssocRing R]   [IsTopolog
icalRing R],…
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedSpace.exp.congr_simp`：∀ {𝔸 : Type u_3} [inst : Ring 𝔸] [inst_1 : T
opologicalSpace 𝔸] [inst_2 : IsTopologicalRing 𝔸] (x x_1 : 𝔸),   x = x_1 → Norme
dSpace.exp x = N…
· 使用定理 `Matrix.coe_units_inv`：coe_units_inv (A : (Matrix n n α)ˣ) : ↑A⁻¹ = (A⁻¹ 
: Matrix n n α)
· 使用定理 `Matrix.exp_units_conj`：∀ {m : Type u_1} {𝔸 : Type u_5} [inst : Fintype m
] [inst_1 : DecidableEq m] [inst_2 : NormedRing 𝔸] [NormedAlgebra ℚ 𝔸]   [Comple
teSpace 𝔸] …
-/
theorem exp_conj (U : Matrix m m 𝔸) (A : Matrix m m 𝔸) (hy : IsUnit U) :
    exp (U * A * U⁻¹) = U * exp A * U⁻¹ :=
  let ⟨u, hu⟩ := hy
  hu ▸ by simpa only [Matrix.coe_units_inv] using exp_units_conj u A
/-
**Matrix.exp_conj'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：exp_conj' (U : Matrix m m 𝔸) (A : Matrix m m 𝔸) (hy : IsUnit U) : exp (U⁻¹
 * A * U) = U⁻¹ * exp A * U
参数：U : Matrix m m 𝔸；A : Matrix m m 𝔸；hy : IsUnit U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.topologicalRing`：∀ {n : Type u_5} {R : Type u_8} [inst : Topologi
calSpace R] [inst_1 : Fintype n] [inst_2 : NonUnitalNonAssocRing R]   [IsTopolog
icalRing R],…
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedSpace.exp.congr_simp`：∀ {𝔸 : Type u_3} [inst : Ring 𝔸] [inst_1 : T
opologicalSpace 𝔸] [inst_2 : IsTopologicalRing 𝔸] (x x_1 : 𝔸),   x = x_1 → Norme
dSpace.exp x = N…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.coe_units_inv`：coe_units_inv (A : (Matrix n n α)ˣ) : ↑A⁻¹ = (A⁻¹ 
: Matrix n n α)
· 使用定理 `Matrix.exp_units_conj'`：exp_units_conj' (U : (Matrix m m 𝔸)ˣ) (A : Matri
x m m 𝔸) : exp (U⁻¹ * A * U) = U⁻¹ * exp A * U
-/
theorem exp_conj' (U : Matrix m m 𝔸) (A : Matrix m m 𝔸) (hy : IsUnit U) :
    exp (U⁻¹ * A * U) = U⁻¹ * exp A * U :=
  let ⟨u, hu⟩ := hy
  hu ▸ by simpa only [Matrix.coe_units_inv] using exp_units_conj' u A

end NormedComm

end Matrix

