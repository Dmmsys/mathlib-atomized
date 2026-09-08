/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Sébastien Gouëzel, Heather Macbeth
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Lp.Matrix
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Util.Superscript

/-!
# `L²` inner product space structure on finite products of inner product spaces

The `L²` norm on a finite product of inner product spaces is compatible with an inner product
$$
\langle x, y\rangle = \sum \langle x_i, y_i \rangle.
$$
This is recorded in this file as an inner product space instance on `PiLp 2`.

This file develops the notion of a finite-dimensional Hilbert space over `𝕜 = ℂ, ℝ`, referred to as
`E`. We define an `OrthonormalBasis 𝕜 ι E` as a linear isometric equivalence
between `E` and `EuclideanSpace 𝕜 ι`. Then `stdOrthonormalBasis` shows that such an equivalence
always exists if `E` is finite dimensional. We provide language for converting between a basis
that is orthonormal and an orthonormal basis (e.g. `Basis.toOrthonormalBasis`). We show that
orthonormal bases for each summand in a direct sum of spaces can be combined into an orthonormal
basis for the whole sum in `DirectSum.IsInternal.subordinateOrthonormalBasis`. In
the last section, various properties of matrices are explored.

## Main definitions

- `EuclideanSpace 𝕜 n`: defined to be `PiLp 2 (n → 𝕜)` for any `Fintype n`, i.e., the space
  from functions to `n` to `𝕜` with the `L²` norm. We register several instances on it (notably
  that it is a finite-dimensional inner product space), and provide a `!ₚ[]` notation (for numeric
  subscripts like `₂`) for the case when the indexing type is `Fin n`.

- `OrthonormalBasis 𝕜 ι`: defined to be an isometry to Euclidean space from a given
  finite-dimensional inner product space, `E ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 ι`.

- `Basis.toOrthonormalBasis`: constructs an `OrthonormalBasis` for a finite-dimensional
  Euclidean space from a `Basis` which is `Orthonormal`.

- `Orthonormal.exists_orthonormalBasis_extension`: provides an existential result of an
  `OrthonormalBasis` extending a given orthonormal set

- `exists_orthonormalBasis`: provides an orthonormal basis on a finite-dimensional vector space

- `stdOrthonormalBasis`: provides an arbitrarily-chosen `OrthonormalBasis` of a given
  finite-dimensional inner product space

- `orthonormalBasisSingleton`: an orthonormal basis formed by a single unit vector in a
  one-dimensional inner product space.

For consequences in infinite dimension (Hilbert bases, etc.), see the file
`Analysis.InnerProductSpace.L2Space`.

-/

@[expose] public section


open Module Real Set Filter RCLike Submodule Function Uniformity Topology NNReal ENNReal
  ComplexConjugate DirectSum WithLp

noncomputable section

variable {ι ι' 𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {F' : Type*} [NormedAddCommGroup F'] [InnerProductSpace ℝ F']

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-
If `ι` is a finite type and each space `f i`, `i : ι`, is an inner product space,
then `Π i, f i` is an inner product space as well. Since `Π i, f i` is endowed with the sup norm,
we use instead `PiLp 2 f` for the product space, which is endowed with the `L^2` norm.
-/
/-
**PiLp.innerProductSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：PiLp.innerProductSpace {ι : Type*} [Fintype ι] (f : ι -> Type*) [forall i,
 NormedAddCommGroup (f i)] [forall i, InnerProductSpace 𝕜 (f i)] : InnerProductS
pace 𝕜 (PiLp 2 f) where inner x y
参数：f : ι -> Type*；f i；f i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)

--- 原说明 ---
If `ι` is a finite type and each space `f i`, `i : ι`, is an inner product space
,
then `Π i, f i` is an inner product space as well. Since `Π i, f i` is endowed w
ith the sup norm,
we use instead `PiLp 2 f` for the product space, which is endowed with the `L^2`
 norm.
-/
instance PiLp.innerProductSpace {ι : Type*} [Fintype ι] (f : ι → Type*)
    [∀ i, NormedAddCommGroup (f i)] [∀ i, InnerProductSpace 𝕜 (f i)] :
    InnerProductSpace 𝕜 (PiLp 2 f) where
  inner x y := ∑ i, ⟪x i, y i⟫
  norm_sq_eq_re_inner x := by
    simp only [PiLp.norm_sq_eq_of_L2, map_sum, ← norm_sq_eq_re_inner]
  conj_inner_symm := by
    intro x y
    unfold inner
    rw [map_sum]
    apply Finset.sum_congr rfl
    rintro z -
    apply inner_conj_symm
  add_left x y z :=
    show (∑ i, ⟪x i + y i, z i⟫ = ∑ i, ⟪x i, z i⟫ + ∑ i, ⟪y i, z i⟫) by
      simp only [inner_add_left, Finset.sum_add_distrib]
  smul_left x y r :=
    show (∑ i : ι, ⟪r • x i, y i⟫ = conj r * ∑ i, ⟪x i, y i⟫) by
      simp only [Finset.mul_sum, inner_smul_left]
/-
**PiLp.inner_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PiLp.inner_apply {ι : Type*} [Fintype ι] {f : ι -> Type*} [forall i, Norme
dAddCommGroup (f i)] [forall i, InnerProductSpace 𝕜 (f i)] (x y : PiLp 2 f) : ⟪x
, y⟫ = ∑ i, ⟪x i, y i⟫
参数：f i；f i；x y : PiLp 2 f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
-/
theorem PiLp.inner_apply {ι : Type*} [Fintype ι] {f : ι → Type*} [∀ i, NormedAddCommGroup (f i)]
    [∀ i, InnerProductSpace 𝕜 (f i)] (x y : PiLp 2 f) : ⟪x, y⟫ = ∑ i, ⟪x i, y i⟫ :=
  rfl

/-- The standard real/complex Euclidean space, functions on a finite type. For an `n`-dimensional
space use `EuclideanSpace 𝕜 (Fin n)`.

For the case when `n = Fin _`, there is `!₂[x, y, ...]` notation for building elements of this type,
analogous to `![x, y, ...]` notation. -/
@[wikidata Q17295]
/-
**EuclideanSpace** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：EuclideanSpace (𝕜 : Type*) (n : Type*) : Type _
参数：𝕜 : Type*；n : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The standard real/complex Euclidean space, functions on a finite type. For an `n
`-dimensional
space use `EuclideanSpace 𝕜 (Fin n)`.

For the case when `n = Fin _`, there is `!₂[x, y, ...]` notation for building el
ements of this type,
analogous to `![x, y, ...]` notation.
-/
abbrev EuclideanSpace (𝕜 : Type*) (n : Type*) : Type _ :=
  PiLp 2 fun _ : n => 𝕜

section Notation
open Lean Meta Elab Term Macro TSyntax PrettyPrinter.Delaborator SubExpr
open Mathlib.Tactic (subscriptTerm)

/-- Notation for vectors in Lp space. `!₂[x, y, ...]` is a shorthand for
`WithLp.toLp 2 ![x, y, ...]`, of type `EuclideanSpace _ (Fin _)`.

This also works for other subscripts. -/
syntax (name := PiLp.vecNotation) "!" noWs subscriptTerm noWs "[" term,* "]" : term
macro_rules | `(!$p:subscript[$e:term,*]) => do
  -- override the `Fin n.succ` to a literal
  let n := e.getElems.size
  `(WithLp.toLp $p (V := ∀ _ : Fin $(quote n), _) ![$e,*])

/-- Unexpander for the `!₂[x, y, ...]` notation. -/
@[app_delab WithLp.toLp]
meta def EuclideanSpace.delabVecNotation : Delab :=
  whenNotPPOption getPPExplicit <| whenPPOption getPPNotation <| withOverApp 3 do
    -- check that the `WithLp.toLp _` is present
    let p : Term ← withNaryArg 0 <| delab
    -- to be conservative, only allow subscripts which are numerals
    guard <| p matches `($_:num)
    let `(![$elems,*]) ← withNaryArg 2 delab | failure
    `(!$p[$elems,*])

end Notation

/-
**EuclideanSpace.nnnorm_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EuclideanSpace.nnnorm_eq {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] (x
 : EuclideanSpace 𝕜 n) : ‖x‖₊ = NNReal.sqrt (∑ i, ‖x i‖₊ ^ 2)
参数：x : EuclideanSpace 𝕜 n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiLp.nnnorm_eq_of_L2`：nnnorm_eq_of_L2 (x : PiLp 2 β) : ‖x‖₊ = NNReal.sqr
t (∑ i : ι, ‖x i‖₊ ^ 2)
-/
theorem EuclideanSpace.nnnorm_eq {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
    (x : EuclideanSpace 𝕜 n) : ‖x‖₊ = NNReal.sqrt (∑ i, ‖x i‖₊ ^ 2) :=
  PiLp.nnnorm_eq_of_L2 x
/-
**EuclideanSpace.norm_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EuclideanSpace.norm_eq {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] (x :
 EuclideanSpace 𝕜 n) : ‖x‖ = √(∑ i, ‖x i‖ ^ 2)
参数：x : EuclideanSpace 𝕜 n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Real.coe_sqrt`：coe_sqrt {x : Real>=0} : (NNReal.sqrt x : Real) = √(x : R
eal)
· 使用定理 `NNReal.coe_sum`：coe_sum (s : Finset ι) (f : ι -> Real>=0) : ∑ i in s, f 
i = ∑ i in s, (f i : Real)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `EuclideanSpace.nnnorm_eq`：EuclideanSpace.nnnorm_eq {𝕜 : Type*} [RCLike 𝕜
] {n : Type*} [Fintype n] (x : EuclideanSpace 𝕜 n) : ‖x‖₊ = NNReal.sqrt (∑ i, ‖x
 i‖₊ ^ 2)
-/
theorem EuclideanSpace.norm_eq {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
    (x : EuclideanSpace 𝕜 n) : ‖x‖ = √(∑ i, ‖x i‖ ^ 2) := by
  simpa only [Real.coe_sqrt, NNReal.coe_sum] using! congr_arg ((↑) : ℝ≥0 → ℝ) x.nnnorm_eq
/-
**EuclideanSpace.norm_sq_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EuclideanSpace.norm_sq_eq {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] (
x : EuclideanSpace 𝕜 n) : ‖x‖ ^ 2 = ∑ i, ‖x i‖ ^ 2
参数：x : EuclideanSpace 𝕜 n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiLp.norm_sq_eq_of_L2`：norm_sq_eq_of_L2 (β : ι -> Type*) [forall i, Semi
normedAddCommGroup (β i)] (x : PiLp 2 β) : ‖x‖ ^ 2 = ∑ i : ι, ‖x i‖ ^ 2
-/
theorem EuclideanSpace.norm_sq_eq {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
    (x : EuclideanSpace 𝕜 n) : ‖x‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 :=
  PiLp.norm_sq_eq_of_L2 _ x
/-
**EuclideanSpace.real_norm_sq_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EuclideanSpace.real_norm_sq_eq {n : Type*} [Fintype n] (x : EuclideanSpace
 Real n) : ‖x‖ ^ 2 = ∑ i, (x i) ^ 2
参数：x : EuclideanSpace Real n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanSpace.norm_sq_eq`：EuclideanSpace.norm_sq_eq {𝕜 : Type*} [RCLike
 𝕜] {n : Type*} [Fintype n] (x : EuclideanSpace 𝕜 n) : ‖x‖ ^ 2 = ∑ i, ‖x i‖ ^ 2
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `sq_abs`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] (a : α
), |a| ^ 2 = a ^ 2
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem EuclideanSpace.real_norm_sq_eq {n : Type*} [Fintype n] (x : EuclideanSpace ℝ n) :
    ‖x‖ ^ 2 = ∑ i, (x i) ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq]

@[wikidata Q847073]
/-
**EuclideanSpace.dist_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EuclideanSpace.dist_eq {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] (x y
 : EuclideanSpace 𝕜 n) : dist x y = √(∑ i, dist (x i) (y i) ^ 2)
参数：x y : EuclideanSpace 𝕜 n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiLp.dist_eq_of_L2`：dist_eq_of_L2 (x y : PiLp 2 β) : dist x y = √(∑ i, d
ist (x i) (y i) ^ 2)
-/
theorem EuclideanSpace.dist_eq {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
    (x y : EuclideanSpace 𝕜 n) : dist x y = √(∑ i, dist (x i) (y i) ^ 2) :=
  PiLp.dist_eq_of_L2 x y
/-
**EuclideanSpace.dist_sq_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EuclideanSpace.dist_sq_eq {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] (
x y : EuclideanSpace 𝕜 n) : dist x y ^ 2 = ∑ i, dist (x i) (y i) ^ 2
参数：x y : EuclideanSpace 𝕜 n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiLp.dist_sq_eq_of_L2`：dist_sq_eq_of_L2 (x y : PiLp 2 β) : dist x y ^ 2 
= ∑ i, dist (x i) (y i) ^ 2
-/
theorem EuclideanSpace.dist_sq_eq {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
    (x y : EuclideanSpace 𝕜 n) : dist x y ^ 2 = ∑ i, dist (x i) (y i) ^ 2 :=
  PiLp.dist_sq_eq_of_L2 x y
/-
**EuclideanSpace.nndist_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EuclideanSpace.nndist_eq {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] (x
 y : EuclideanSpace 𝕜 n) : nndist x y = NNReal.sqrt (∑ i, nndist (x i) (y i) ^ 2
)
参数：x y : EuclideanSpace 𝕜 n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiLp.nndist_eq_of_L2`：nndist_eq_of_L2 (x y : PiLp 2 β) : nndist x y = NN
Real.sqrt (∑ i, nndist (x i) (y i) ^ 2)
-/
theorem EuclideanSpace.nndist_eq {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
    (x y : EuclideanSpace 𝕜 n) : nndist x y = NNReal.sqrt (∑ i, nndist (x i) (y i) ^ 2) :=
  PiLp.nndist_eq_of_L2 x y
/-
**EuclideanSpace.edist_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EuclideanSpace.edist_eq {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] (x 
y : EuclideanSpace 𝕜 n) : edist x y = (∑ i, edist (x i) (y i) ^ 2) ^ (1 / 2 : Re
al)
参数：x y : EuclideanSpace 𝕜 n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiLp.edist_eq_of_L2`：edist_eq_of_L2 (x y : PiLp 2 β) : edist x y = (∑ i,
 edist (x i) (y i) ^ 2) ^ (1 / 2 : Real)
-/
theorem EuclideanSpace.edist_eq {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
    (x y : EuclideanSpace 𝕜 n) : edist x y = (∑ i, edist (x i) (y i) ^ 2) ^ (1 / 2 : ℝ) :=
  PiLp.edist_eq_of_L2 x y
/-
**EuclideanSpace.ball_zero_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EuclideanSpace.ball_zero_eq {n : Type*} [Fintype n] (r : Real) (hr : 0 <= 
r) : Metric.ball (0 : EuclideanSpace Real n) r = {x | ∑ i, x i ^ 2 < r ^ 2}
参数：r : Real；hr : 0 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `EuclideanSpace.norm_eq`：EuclideanSpace.norm_eq {𝕜 : Type*} [RCLike 𝕜] {n
 : Type*} [Fintype n] (x : EuclideanSpace 𝕜 n) : ‖x‖ = √(∑ i, ‖x i‖ ^ 2)
· 使用定理 `sq_abs`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] (a : α
), |a| ^ 2 = a ^ 2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Real.sqrt_lt`：sqrt_lt (hx : 0 <= x) (hy : 0 <= y) : √x < y ↔ x < y ^ 2
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem EuclideanSpace.ball_zero_eq {n : Type*} [Fintype n] (r : ℝ) (hr : 0 ≤ r) :
    Metric.ball (0 : EuclideanSpace ℝ n) r = {x | ∑ i, x i ^ 2 < r ^ 2} := by
  ext x
  have : (0 : ℝ) ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  simp_rw [mem_ofPred, mem_ball_zero_iff, norm_eq, norm_eq_abs, sq_abs, sqrt_lt this hr]
/-
**EuclideanSpace.closedBall_zero_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EuclideanSpace.closedBall_zero_eq {n : Type*} [Fintype n] (r : Real) (hr :
 0 <= r) : Metric.closedBall (0 : EuclideanSpace Real n) r = {x | ∑ i, x i ^ 2 <
= r ^ 2}
参数：r : Real；hr : 0 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `EuclideanSpace.norm_eq`：EuclideanSpace.norm_eq {𝕜 : Type*} [RCLike 𝕜] {n
 : Type*} [Fintype n] (x : EuclideanSpace 𝕜 n) : ‖x‖ = √(∑ i, ‖x i‖ ^ 2)
· 使用定理 `sq_abs`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] (a : α
), |a| ^ 2 = a ^ 2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Real.sqrt_le_left`：sqrt_le_left (hy : 0 <= y) : √x <= y ↔ x <= y ^ 2
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem EuclideanSpace.closedBall_zero_eq {n : Type*} [Fintype n] (r : ℝ) (hr : 0 ≤ r) :
    Metric.closedBall (0 : EuclideanSpace ℝ n) r = {x | ∑ i, x i ^ 2 ≤ r ^ 2} := by
  ext
  simp_rw [mem_ofPred, mem_closedBall_zero_iff, norm_eq, norm_eq_abs, sq_abs, sqrt_le_left hr]
/-
**EuclideanSpace.sphere_zero_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EuclideanSpace.sphere_zero_eq {n : Type*} [Fintype n] (r : Real) (hr : 0 <
= r) : Metric.sphere (0 : EuclideanSpace Real n) r = {x | ∑ i, x i ^ 2 = r ^ 2}
参数：r : Real；hr : 0 <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `EuclideanSpace.norm_eq`：EuclideanSpace.norm_eq {𝕜 : Type*} [RCLike 𝕜] {n
 : Type*} [Fintype n] (x : EuclideanSpace 𝕜 n) : ‖x‖ = √(∑ i, ‖x i‖ ^ 2)
· 使用定理 `sq_abs`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] (a : α
), |a| ^ 2 = a ^ 2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Real.sqrt_eq_iff_eq_sq`：sqrt_eq_iff_eq_sq (hx : 0 <= x) (hy : 0 <= y) : 
√x = y ↔ x = y ^ 2
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem EuclideanSpace.sphere_zero_eq {n : Type*} [Fintype n] (r : ℝ) (hr : 0 ≤ r) :
    Metric.sphere (0 : EuclideanSpace ℝ n) r = {x | ∑ i, x i ^ 2 = r ^ 2} := by
  ext x
  have : (0 : ℝ) ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  simp_rw [mem_ofPred, mem_sphere_zero_iff_norm, norm_eq, norm_eq_abs, sq_abs,
    Real.sqrt_eq_iff_eq_sq this hr]

section

/-
**EuclideanSpace.infinite** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：EuclideanSpace.infinite [Nonempty ι] : Infinite (EuclideanSpace 𝕜 ι)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.infinite`：infinite [Infinite R] [Nontrivial M] : Infinite M
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `NontriviallyNormedField.infinite`：∀ (𝕜 : Type u_1) [NontriviallyNormedFi
eld 𝕜], Infinite 𝕜
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
-/
instance EuclideanSpace.infinite [Nonempty ι] : Infinite (EuclideanSpace 𝕜 ι) :=
  Module.Free.infinite 𝕜 _

variable [Fintype ι]

@[simp]
/-
**finrank_euclideanSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finrank_euclideanSpace : Module.finrank 𝕜 (EuclideanSpace 𝕜 ι) = Fintype.c
ard ι
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.finrank_fintype_fun_eq_card`：Module.finrank_fintype_fun_eq_card :
 finrank R (η -> R) = Fintype.card η
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
-/
theorem finrank_euclideanSpace :
    Module.finrank 𝕜 (EuclideanSpace 𝕜 ι) = Fintype.card ι := by
  convert! (WithLp.linearEquiv 2 𝕜 (ι → 𝕜)).finrank_eq
  simp
/-
**finrank_euclideanSpace_fin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finrank_euclideanSpace_fin {n : Nat} : Module.finrank 𝕜 (EuclideanSpace 𝕜 
(Fin n)) = n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finrank_euclideanSpace`：finrank_euclideanSpace : Module.finrank 𝕜 (Eucli
deanSpace 𝕜 ι) = Fintype.card ι
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finrank_euclideanSpace_fin {n : ℕ} :
    Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin n)) = n := by simp

namespace EuclideanSpace

/-
**EuclideanSpace.** 是 Mathlib 中的一个实例，位于命名空间 `EuclideanSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
scoped instance (n : ℕ) : Fact (Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin n)) = n) :=
  ⟨finrank_euclideanSpace_fin⟩
/-
**EuclideanSpace.inner_eq_star_dotProduct** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanSp
ace`。
形式化陈述：inner_eq_star_dotProduct (x y : EuclideanSpace 𝕜 ι) : ⟪x, y⟫ = ofLp y ⬝ᵥ s
tar (ofLp x)
参数：x y : EuclideanSpace 𝕜 ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
-/
theorem inner_eq_star_dotProduct (x y : EuclideanSpace 𝕜 ι) :
    ⟪x, y⟫ = ofLp y ⬝ᵥ star (ofLp x) := rfl
/-
**EuclideanSpace.inner_toLp_toLp** 是 Mathlib 中的一个引理，位于命名空间 `EuclideanSpace`。
形式化陈述：inner_toLp_toLp (x y : ι -> 𝕜) : ⟪toLp 2 x, toLp 2 y⟫ = dotProduct y (star
 x)
参数：x y : ι -> 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
-/
lemma inner_toLp_toLp (x y : ι → 𝕜) :
    ⟪toLp 2 x, toLp 2 y⟫ = dotProduct y (star x) := rfl

section restrict₂

variable {I J : Finset ι'}

/-- The restriction from `EuclideanSpace 𝕜 J` to `EuclideanSpace 𝕜 I` when `I ⊆ J`. -/
noncomputable
/-
**EuclideanSpace.restrict** 是 Mathlib 中的一个定义，位于命名空间 `EuclideanSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def restrict₂ (hIJ : I ⊆ J) :
    EuclideanSpace 𝕜 J →L[𝕜] EuclideanSpace 𝕜 I where
  toFun x := toLp 2 (Finset.restrict₂ («π» := fun _ ↦ 𝕜) hIJ x.ofLp)
  map_add' x y := by ext; simp
  map_smul' m x := by ext; simp

@[simp]
/-
**EuclideanSpace.restrict** 是 Mathlib 中的一个引理，位于命名空间 `EuclideanSpace`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma restrict₂_apply (hIJ : I ⊆ J) (x : EuclideanSpace 𝕜 J) (i : I) :
    EuclideanSpace.restrict₂ hIJ x i = x ⟨i.1, hIJ i.2⟩ := rfl

end restrict₂

end EuclideanSpace

/-- A finite, mutually orthogonal family of subspaces of `E`, which span `E`, induce an isometry
from `E` to `PiLp 2` of the subspaces equipped with the `L2` inner product. -/
/-
**DirectSum.IsInternal.isometryL2OfOrthogonalFamily** 是 Mathlib 中的一个定义，位于命名空间 ``
。
形式化陈述：DirectSum.IsInternal.isometryL2OfOrthogonalFamily [DecidableEq ι] {V : ι -
> Submodule 𝕜 E} (hV : DirectSum.IsInternal V) (hV' : OrthogonalFamily 𝕜 (fun i 
=> V i) fun i => (V i).subtypeₗᵢ) : E ≃ₗᵢ[𝕜] PiLp 2 fun i => V i
参数：hV : DirectSum.IsInternal V；hV' : OrthogonalFamily 𝕜 (fun i => V i) fun i => 
(V i).subtypeₗᵢ。
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)

--- 原说明 ---
A finite, mutually orthogonal family of subspaces of `E`, which span `E`, induce
 an isometry
from `E` to `PiLp 2` of the subspaces equipped with the `L2` inner product.
-/
def DirectSum.IsInternal.isometryL2OfOrthogonalFamily [DecidableEq ι] {V : ι → Submodule 𝕜 E}
    (hV : DirectSum.IsInternal V)
    (hV' : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) :
    E ≃ₗᵢ[𝕜] PiLp 2 fun i => V i := by
  let e₁ := DirectSum.linearEquivFunOnFintype 𝕜 ι fun i => V i
  let e₂ := LinearEquiv.ofBijective (DirectSum.coeLinearMap V) hV
  refine LinearEquiv.isometryOfInner ((e₂.symm.trans e₁).trans
    (WithLp.linearEquiv 2 𝕜 (Π i, V i)).symm) ?_
  suffices ∀ (v w : PiLp 2 fun i => V i), ⟪v, w⟫ = ⟪e₂ (e₁.symm v), e₂ (e₁.symm w)⟫ by
    intro v₀ w₀
    simp only [LinearEquiv.trans_apply]
    convert! this (toLp 2 (e₁ (e₂.symm v₀))) (toLp 2 (e₁ (e₂.symm w₀))) <;> simp
  intro v w
  trans ⟪∑ i, (V i).subtypeₗᵢ (v i), ∑ i, (V i).subtypeₗᵢ (w i)⟫
  · simp only [sum_inner, hV'.inner_right_fintype, PiLp.inner_apply]
  · congr <;> simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**DirectSum.IsInternal.isometryL2OfOrthogonalFamily_symm_apply** 是 Mathlib 中的一个定
理，位于命名空间 ``。
形式化陈述：DirectSum.IsInternal.isometryL2OfOrthogonalFamily_symm_apply [DecidableEq 
ι] {V : ι -> Submodule 𝕜 E} (hV : DirectSum.IsInternal V) (hV' : OrthogonalFamil
y 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) (w : PiLp 2 fun i => V i) : (hV.iso
metryL2OfOrthogonalFamily hV').symm w = ∑ i, (w i : E)
参数：hV : DirectSum.IsInternal V；hV' : OrthogonalFamily 𝕜 (fun i => V i) fun i => 
(V i).subtypeₗᵢ；w : PiLp 2 fun i => V i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.sumAddHom_apply`：sumAddHom_apply [forall i, AddZeroClass (β i)]
 [forall (i) (x : β i), Decidable (x != 0)] [AddCommMonoid γ] (φ : forall i, β i
 ->+ γ) (f : Π…
· 使用定理 `DFinsupp.sum_eq_sum_fintype`：∀ {ι : Type u} {γ : Type w} {β : ι → Type v
} [inst : DecidableEq ι] [inst_1 : Fintype ι] [inst_2 : (i : ι) → Zero (β i)]   
[inst_3 : (i : ι)…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `DFinsupp.equivFunOnFintype_apply`：∀ {ι : Type u} {β : ι → Type v} [inst 
: (i : ι) → Zero (β i)] [inst_1 : Fintype ι] (a : Π₀ (i : ι), β i) (a_1 : ι),   
DFinsupp.equivFunOnFin…
· 使用定理 `DirectSum.linearEquivFunOnFintype_apply`：∀ (R : Type u) [inst : Semiring
 R] (ι : Type v) (M : ι → Type w) [inst_1 : (i : ι) → AddCommMonoid (M i)]   [in
st_2 : (i : ι) → _root_.Modul…
-/
theorem DirectSum.IsInternal.isometryL2OfOrthogonalFamily_symm_apply [DecidableEq ι]
    {V : ι → Submodule 𝕜 E} (hV : DirectSum.IsInternal V)
    (hV' : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) (w : PiLp 2 fun i => V i) :
    (hV.isometryL2OfOrthogonalFamily hV').symm w = ∑ i, (w i : E) := by
  classical
    let e₁ := DirectSum.linearEquivFunOnFintype 𝕜 ι fun i => V i
    let e₂ := LinearEquiv.ofBijective (DirectSum.coeLinearMap V) hV
    suffices ∀ v : ⨁ i, V i, e₂ v = ∑ i, e₁ v i by exact this (e₁.symm w)
    simp [e₁, e₂, DirectSum.coeLinearMap, DirectSum.toModule, DFinsupp.lsum,
      DFinsupp.sumAddHom_apply]

end

variable (ι 𝕜)

/-- A shorthand for `PiLp.continuousLinearEquiv`. -/
/-
**EuclideanSpace.equiv** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：EuclideanSpace.equiv : EuclideanSpace 𝕜 ι ≃L[𝕜] ι -> 𝕜
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A shorthand for `PiLp.continuousLinearEquiv`.
-/
abbrev EuclideanSpace.equiv : EuclideanSpace 𝕜 ι ≃L[𝕜] ι → 𝕜 :=
  PiLp.continuousLinearEquiv 2 𝕜 _

variable {ι 𝕜}

/-- The projection on the `i`-th coordinate of `EuclideanSpace 𝕜 ι`, as a linear map. -/
/-
**EuclideanSpace.proj** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：EuclideanSpace.proj (i : ι) : StrongDual 𝕜 (EuclideanSpace 𝕜 ι)
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection on the `i`-th coordinate of `EuclideanSpace 𝕜 ι`, as a linear map
.
-/
abbrev EuclideanSpace.projₗ (i : ι) : EuclideanSpace 𝕜 ι →ₗ[𝕜] 𝕜 := PiLp.projₗ _ _ i

/-- The projection on the `i`-th coordinate of `EuclideanSpace 𝕜 ι`, as a continuous linear map. -/
/-
**EuclideanSpace.proj** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：EuclideanSpace.proj (i : ι) : StrongDual 𝕜 (EuclideanSpace 𝕜 ι)
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection on the `i`-th coordinate of `EuclideanSpace 𝕜 ι`, as a continuous
 linear map.
-/
abbrev EuclideanSpace.proj (i : ι) : StrongDual 𝕜 (EuclideanSpace 𝕜 ι) := PiLp.proj _ _ i

@[simp]
/-
**EuclideanSpace.coe_proj** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：EuclideanSpace.coe_proj {ι : Type*} (𝕜 : Type*) [RCLike 𝕜] {i : ι} : ⇑(@pr
oj ι 𝕜 _ i) = fun x => x i
参数：𝕜 : Type*。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma EuclideanSpace.coe_proj {ι : Type*} (𝕜 : Type*) [RCLike 𝕜] {i : ι} :
    ⇑(@proj ι 𝕜 _ i) = fun x ↦ x i := rfl

section DecEq

variable [DecidableEq ι]

/-- The vector given in Euclidean space by being `a : 𝕜` at coordinate `i : ι` and `0 : 𝕜` at
all other coordinates. -/
/-
**EuclideanSpace.single** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：EuclideanSpace.single (i : ι) (a : 𝕜) : EuclideanSpace 𝕜 ι
参数：i : ι；a : 𝕜。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The vector given in Euclidean space by being `a : 𝕜` at coordinate `i : ι` and `
0 : 𝕜` at
all other coordinates.
-/
abbrev EuclideanSpace.single (i : ι) (a : 𝕜) : EuclideanSpace 𝕜 ι := PiLp.single 2 i a

@[deprecated PiLp.ofLp_single (since := "2026-03-15")]
/-
**EuclideanSpace.ofLp_single** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：EuclideanSpace.ofLp_single (i : ι) (a : 𝕜) : ofLp (single i a) = Pi.single
 i a
参数：i : ι；a : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma EuclideanSpace.ofLp_single (i : ι) (a : 𝕜) : ofLp (single i a) = Pi.single i a := by
  simp

@[deprecated PiLp.toLp_single (since := "2026-03-15")]
/-
**EuclideanSpace.toLp_single** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：EuclideanSpace.toLp_single (i : ι) (a : 𝕜) : toLp _ (Pi.single i a) = sing
le i a
参数：i : ι；a : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma EuclideanSpace.toLp_single (i : ι) (a : 𝕜) : toLp _ (Pi.single i a) = single i a := by
  simp

@[deprecated PiLp.single_apply (since := "2026-03-15")]
/-
**EuclideanSpace.single_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EuclideanSpace.single_apply (i : ι) (a : 𝕜) (j : ι) : (EuclideanSpace.sing
le i a) j = ite (j = i) a 0
参数：i : ι；a : 𝕜；j : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PiLp.single_apply`：single_apply [Zero 𝕜] (i : ι) (a : 𝕜) (j : ι) : (sing
le p i a : PiLp p (fun _ => 𝕜)) j = ite (j = i) a 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem EuclideanSpace.single_apply (i : ι) (a : 𝕜) (j : ι) :
    (EuclideanSpace.single i a) j = ite (j = i) a 0 := by
  simp

@[deprecated PiLp.single_eq_zero_iff (since := "2026-03-15")]
/-
**EuclideanSpace.single_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EuclideanSpace.single_eq_zero_iff {i : ι} {a : 𝕜} : EuclideanSpace.single 
i a = 0 ↔ a = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem EuclideanSpace.single_eq_zero_iff {i : ι} {a : 𝕜} :
    EuclideanSpace.single i a = 0 ↔ a = 0 := by simp

variable [Fintype ι]
/-
**EuclideanSpace.inner_single_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EuclideanSpace.inner_single_left (i : ι) (a : 𝕜) (v : EuclideanSpace 𝕜 ι) 
: ⟪EuclideanSpace.single i (a : 𝕜), v⟫ = conj a * v i
参数：i : ι；a : 𝕜；v : EuclideanSpace 𝕜 ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `PiLp.single_apply`：single_apply [Zero 𝕜] (i : ι) (a : 𝕜) (j : ι) : (sing
le p i a : PiLp p (fun _ => 𝕜)) j = ite (j = i) a 0
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem EuclideanSpace.inner_single_left (i : ι) (a : 𝕜) (v : EuclideanSpace 𝕜 ι) :
    ⟪EuclideanSpace.single i (a : 𝕜), v⟫ = conj a * v i := by
  simp [PiLp.inner_apply, apply_ite conj, mul_comm]
/-
**EuclideanSpace.inner_single_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EuclideanSpace.inner_single_right (i : ι) (a : 𝕜) (v : EuclideanSpace 𝕜 ι)
 : ⟪v, EuclideanSpace.single i (a : 𝕜)⟫ = a * conj (v i)
参数：i : ι；a : 𝕜；v : EuclideanSpace 𝕜 ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `PiLp.single_apply`：single_apply [Zero 𝕜] (i : ι) (a : 𝕜) (j : ι) : (sing
le p i a : PiLp p (fun _ => 𝕜)) j = ite (j = i) a 0
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem EuclideanSpace.inner_single_right (i : ι) (a : 𝕜) (v : EuclideanSpace 𝕜 ι) :
    ⟪v, EuclideanSpace.single i (a : 𝕜)⟫ = a * conj (v i) := by simp [PiLp.inner_apply]

@[deprecated PiLp.norm_single (since := "2026-03-15")]
/-
**EuclideanSpace.norm_single** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EuclideanSpace.norm_single (i : ι) (a : 𝕜) : ‖EuclideanSpace.single i (a :
 𝕜)‖ = ‖a‖
参数：i : ι；a : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PiLp.norm_single`：norm_single (i : ι) (b : β i) : ‖single p i b‖ = ‖b‖
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem EuclideanSpace.norm_single (i : ι) (a : 𝕜) :
    ‖EuclideanSpace.single i (a : 𝕜)‖ = ‖a‖ := by simp

@[deprecated PiLp.nnnorm_single (since := "2026-03-15")]
/-
**EuclideanSpace.nnnorm_single** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EuclideanSpace.nnnorm_single (i : ι) (a : 𝕜) : ‖EuclideanSpace.single i (a
 : 𝕜)‖₊ = ‖a‖₊
参数：i : ι；a : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PiLp.nnnorm_single`：nnnorm_single (i : ι) (b : β i) : ‖single p i b‖₊ = 
‖b‖₊
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem EuclideanSpace.nnnorm_single (i : ι) (a : 𝕜) :
    ‖EuclideanSpace.single i (a : 𝕜)‖₊ = ‖a‖₊ := by simp

@[deprecated PiLp.dist_single_same (since := "2026-03-15")]
/-
**EuclideanSpace.dist_single_same** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EuclideanSpace.dist_single_same (i : ι) (a b : 𝕜) : dist (EuclideanSpace.s
ingle i (a : 𝕜)) (EuclideanSpace.single i (b : 𝕜)) = dist a b
参数：i : ι；a b : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PiLp.dist_single_same`：dist_single_same (i : ι) (b₁ b₂ : β i) : dist (si
ngle p i b₁) (single p i b₂) = dist b₁ b₂
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem EuclideanSpace.dist_single_same (i : ι) (a b : 𝕜) :
    dist (EuclideanSpace.single i (a : 𝕜)) (EuclideanSpace.single i (b : 𝕜)) = dist a b := by
  simp

@[deprecated PiLp.nndist_single_same (since := "2026-03-15")]
/-
**EuclideanSpace.nndist_single_same** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EuclideanSpace.nndist_single_same (i : ι) (a b : 𝕜) : nndist (EuclideanSpa
ce.single i (a : 𝕜)) (EuclideanSpace.single i (b : 𝕜)) = nndist a b
参数：i : ι；a b : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PiLp.nndist_single_same`：nndist_single_same (i : ι) (b₁ b₂ : β i) : nndi
st (single p i b₁) (single p i b₂) = nndist b₁ b₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem EuclideanSpace.nndist_single_same (i : ι) (a b : 𝕜) :
    nndist (EuclideanSpace.single i (a : 𝕜)) (EuclideanSpace.single i (b : 𝕜)) = nndist a b := by
  simp

@[deprecated PiLp.edist_single_same (since := "2026-03-15")]
/-
**EuclideanSpace.edist_single_same** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EuclideanSpace.edist_single_same (i : ι) (a b : 𝕜) : edist (EuclideanSpace
.single i (a : 𝕜)) (EuclideanSpace.single i (b : 𝕜)) = edist a b
参数：i : ι；a b : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PiLp.edist_single_same`：edist_single_same (i : ι) (b₁ b₂ : β i) : edist 
(single p i b₁) (single p i b₂) = edist b₁ b₂
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem EuclideanSpace.edist_single_same (i : ι) (a b : 𝕜) :
    edist (EuclideanSpace.single i (a : 𝕜)) (EuclideanSpace.single i (b : 𝕜)) = edist a b := by
  simp

/-- `EuclideanSpace.single` forms an orthonormal family. -/
/-
**EuclideanSpace.orthonormal_single** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EuclideanSpace.orthonormal_single : Orthonormal 𝕜 fun i : ι => EuclideanSp
ace.single i (1 : 𝕜)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EuclideanSpace.inner_single_left`：EuclideanSpace.inner_single_left (i : 
ι) (a : 𝕜) (v : EuclideanSpace 𝕜 ι) : ⟪EuclideanSpace.single i (a : 𝕜), v⟫ = con
j a * v i
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `PiLp.single_apply`：single_apply [Zero 𝕜] (i : ι) (a : 𝕜) (j : ι) : (sing
le p i a : PiLp p (fun _ => 𝕜)) j = ite (j = i) a 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`EuclideanSpace.single` forms an orthonormal family.
-/
theorem EuclideanSpace.orthonormal_single :
    Orthonormal 𝕜 fun i : ι => EuclideanSpace.single i (1 : 𝕜) := by
  simp_rw [orthonormal_iff_ite, EuclideanSpace.inner_single_left, map_one, one_mul,
    PiLp.single_apply]
  intros
  trivial
/-
**EuclideanSpace.piLpCongrLeft_single** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EuclideanSpace.piLpCongrLeft_single {ι' : Type*} [Fintype ι'] [DecidableEq
 ι'] (e : ι' ≃ ι) (i' : ι') (v : 𝕜) : LinearIsometryEquiv.piLpCongrLeft 2 𝕜 𝕜 e 
(EuclideanSpace.single i' v) = EuclideanSpace.single (e i') v
参数：e : ι' ≃ ι；i' : ι'；v : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIsometryEquiv.piLpCongrLeft_single`：∀ {p : ENNReal} {𝕜 : Type u_1}
 {ι : Type u_2} [hp : Fact (1 ≤ p)] [inst : Fintype ι] [inst_1 : Semiring 𝕜]   {
ι' : Type u_5} [inst_2 : Finty…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
-/
theorem EuclideanSpace.piLpCongrLeft_single
    {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (e : ι' ≃ ι) (i' : ι') (v : 𝕜) :
    LinearIsometryEquiv.piLpCongrLeft 2 𝕜 𝕜 e (EuclideanSpace.single i' v) =
      EuclideanSpace.single (e i') v :=
  LinearIsometryEquiv.piLpCongrLeft_single e i' _

end DecEq

section finAddEquivProd

/-- The canonical linear homeomorphism between `EuclideanSpace 𝕜 (ι ⊕ κ)` and
`EuclideanSpace 𝕜 ι × EuclideanSpace 𝕜 κ`.

See `PiLp.sumPiLpEquivProdLpPiLp` for the isometry version,
where the RHS is equipped with the Euclidean norm rather than the supremum norm. -/
/-
**EuclideanSpace.sumEquivProd** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：EuclideanSpace.sumEquivProd {𝕜 : Type*} [RCLike 𝕜] {ι κ : Type*} [Fintype 
ι] [Fintype κ] : EuclideanSpace 𝕜 (ι oplus κ) ≃L[𝕜] EuclideanSpace 𝕜 ι × Euclide
anSpace 𝕜 κ
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)

--- 原说明 ---
The canonical linear homeomorphism between `EuclideanSpace 𝕜 (ι ⊕ κ)` and
`EuclideanSpace 𝕜 ι × EuclideanSpace 𝕜 κ`.

See `PiLp.sumPiLpEquivProdLpPiLp` for the isometry version,
where the RHS is equipped with the Euclidean norm rather than the supremum norm.
-/
abbrev EuclideanSpace.sumEquivProd {𝕜 : Type*} [RCLike 𝕜] {ι κ : Type*} [Fintype ι] [Fintype κ] :
    EuclideanSpace 𝕜 (ι ⊕ κ) ≃L[𝕜] EuclideanSpace 𝕜 ι × EuclideanSpace 𝕜 κ :=
  (PiLp.sumPiLpEquivProdLpPiLp 2 _).toContinuousLinearEquiv.trans <|
    WithLp.prodContinuousLinearEquiv _ _ _ _

/-- The canonical linear homeomorphism between `EuclideanSpace 𝕜 (Fin (n + m))` and
`EuclideanSpace 𝕜 (Fin n) × EuclideanSpace 𝕜 (Fin m)`. -/
/-
**EuclideanSpace.finAddEquivProd** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：EuclideanSpace.finAddEquivProd {𝕜 : Type*} [RCLike 𝕜] {n m : Nat} : Euclid
eanSpace 𝕜 (Fin (n + m)) ≃L[𝕜] EuclideanSpace 𝕜 (Fin n) × EuclideanSpace 𝕜 (Fin 
m)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The canonical linear homeomorphism between `EuclideanSpace 𝕜 (Fin (n + m))` and
`EuclideanSpace 𝕜 (Fin n) × EuclideanSpace 𝕜 (Fin m)`.
-/
abbrev EuclideanSpace.finAddEquivProd {𝕜 : Type*} [RCLike 𝕜] {n m : ℕ} :
    EuclideanSpace 𝕜 (Fin (n + m)) ≃L[𝕜] EuclideanSpace 𝕜 (Fin n) × EuclideanSpace 𝕜 (Fin m) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 𝕜 𝕜 finSumFinEquiv.symm).toContinuousLinearEquiv.trans
    sumEquivProd

end finAddEquivProd

variable (ι 𝕜 E)
variable [Fintype ι]

/-- An orthonormal basis on E is an identification of `E` with its dimensional-matching
`EuclideanSpace 𝕜 ι`. -/
/-
**OrthonormalBasis** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(ι : Type u_1) →   (𝕜 : Type u_3) →     [inst : RCLike 𝕜] →       (E : Typ
e u_4) →         [inst_1 : NormedAddCommGroup E] → [InnerProductSpace 𝕜 E] → [Fi
ntype ι] → Type (max (max u_1 u_3) u_4)
参数：max u_1 u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An orthonormal basis on E is an identification of `E` with its dimensional-match
ing
`EuclideanSpace 𝕜 ι`.
-/
structure OrthonormalBasis where ofRepr ::
  /-- Linear isometry between `E` and `EuclideanSpace 𝕜 ι` representing the orthonormal basis. -/
  repr : E ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 ι

variable {ι 𝕜 E}

namespace OrthonormalBasis

/-
**OrthonormalBasis.repr_injective** 是 Mathlib 中的一个定理，位于命名空间 `OrthonormalBasis`。
形式化陈述：repr_injective : Injective (repr : OrthonormalBasis ι 𝕜 E -> E ≃ₗᵢ[𝕜] Eucl
ideanSpace 𝕜 ι)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem repr_injective :
    Injective (repr : OrthonormalBasis ι 𝕜 E → E ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 ι) := fun f g h => by
  cases f
  cases g
  congr

set_option backward.isDefEq.respectTransparency false in
/-- `b i` is the `i`th basis vector. -/
/-
**OrthonormalBasis.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 `OrthonormalBasis`。
形式化陈述：instFunLike : FunLike (OrthonormalBasis ι 𝕜 E) ι E where coe b i
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)

--- 原说明 ---
`b i` is the `i`th basis vector.
-/
instance instFunLike : FunLike (OrthonormalBasis ι 𝕜 E) ι E where
  coe b i := by classical exact b.repr.symm (EuclideanSpace.single i (1 : 𝕜))
  coe_injective b b' h := repr_injective <| LinearIsometryEquiv.toLinearEquiv_injective <|
    LinearEquiv.symm_bijective.injective <| LinearEquiv.toLinearMap_injective <| by
      classical
        rw [← LinearMap.cancel_right (WithLp.linearEquiv 2 𝕜 (_ → 𝕜)).symm.surjective]
        simp +instances only
        refine LinearMap.pi_ext fun i k => ?_
        have : k = k • (1 : 𝕜) := by rw [smul_eq_mul, mul_one]
        rw [this, Pi.single_smul]
        replace h := congr_fun h i
        simp only [LinearEquiv.comp_coe, map_smul, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
          coe_symm_linearEquiv, PiLp.toLp_single,
          LinearIsometryEquiv.coe_symm_toLinearEquiv] at h ⊢
        rw [h]

@[simp]
/-
**OrthonormalBasis.coe_ofRepr** 是 Mathlib 中的一个定理，位于命名空间 `OrthonormalBasis`。
形式化陈述：coe_ofRepr [DecidableEq ι] (e : E ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 ι) : ⇑(Orthonorm
alBasis.ofRepr e) = fun i => e.symm (EuclideanSpace.single i (1 : 𝕜))
参数：e : E ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Lean.Meta.instFastSubsingletonForall`：∀ {α : Sort u} {β : α → Sort v} [i
nst : ∀ (x : α), Meta.FastSubsingleton (β x)], Meta.FastSubsingleton ((x : α) → 
β x)
· 使用定理 `Lean.Meta.instFastSubsingletonDecidable`：∀ {p : Prop}, Meta.FastSubsingl
eton (Decidable p)
-/
theorem coe_ofRepr [DecidableEq ι] (e : E ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 ι) :
    ⇑(OrthonormalBasis.ofRepr e) = fun i => e.symm (EuclideanSpace.single i (1 : 𝕜)) := by
  dsimp only [DFunLike.coe]
  funext
  congr!

@[simp]
/-
**OrthonormalBasis.repr_symm_single** 是 Mathlib 中的一个定理，位于命名空间 `OrthonormalBasis`
。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : RCLike 𝕜] {E : Type u_4} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : Fintype ι] [
inst_4 : DecidableEq ι] (b : OrthonormalBasis ι 𝕜 E) (i : ι),   b.repr.symm (Euc
lideanSpace.single i 1) = b i
参数：b : OrthonormalBasis ι 𝕜 E；i : ι；EuclideanSpace.single i 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Lean.Meta.instFastSubsingletonForall`：∀ {α : Sort u} {β : α → Sort v} [i
nst : ∀ (x : α), Meta.FastSubsingleton (β x)], Meta.FastSubsingleton ((x : α) → 
β x)
· 使用定理 `Lean.Meta.instFastSubsingletonDecidable`：∀ {p : Prop}, Meta.FastSubsingl
eton (Decidable p)
-/
protected theorem repr_symm_single [DecidableEq ι] (b : OrthonormalBasis ι 𝕜 E) (i : ι) :
    b.repr.symm (EuclideanSpace.single i (1 : 𝕜)) = b i := by
  dsimp only [DFunLike.coe]
  congr!

@[simp]
/-
**OrthonormalBasis.repr_self** 是 Mathlib 中的一个定理，位于命名空间 `OrthonormalBasis`。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : RCLike 𝕜] {E : Type u_4} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : Fintype ι] [
inst_4 : DecidableEq ι] (b : OrthonormalBasis ι 𝕜 E) (i : ι),   b.repr (b i) = E
uclideanSpace.single i 1
参数：b : OrthonormalBasis ι 𝕜 E；i : ι；b i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrthonormalBasis.repr_symm_single`：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst
 : RCLike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerPro
ductSpace 𝕜 E] [inst_3 …
· 使用定理 `LinearIsometryEquiv.apply_symm_apply`：apply_symm_apply (x : E₂) : e (e.s
ymm x) = x
-/
protected theorem repr_self [DecidableEq ι] (b : OrthonormalBasis ι 𝕜 E) (i : ι) :
    b.repr (b i) = EuclideanSpace.single i (1 : 𝕜) := by
  rw [← b.repr_symm_single i, LinearIsometryEquiv.apply_symm_apply]
/-
**OrthonormalBasis.repr_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrthonormalBasis`
。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : RCLike 𝕜] {E : Type u_4} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : Fintype ι] (
b : OrthonormalBasis ι 𝕜 E) (v : E) (i : ι),   (b.repr v).ofLp i = inner 𝕜 (b i)
 v
参数：b : OrthonormalBasis ι 𝕜 E；v : E；i : ι；b.repr v；b i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearIsometryEquiv.inner_map_map`：LinearIsometryEquiv.inner_map_map (f 
: E ≃ₗᵢ[𝕜] E') (x y : E) : ⟪f x, f y⟫ = ⟪x, y⟫
· 使用定理 `OrthonormalBasis.repr_self`：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : RCLi
ke 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpa
ce 𝕜 E] [inst_3 …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `EuclideanSpace.inner_single_left`：EuclideanSpace.inner_single_left (i : 
ι) (a : 𝕜) (v : EuclideanSpace 𝕜 ι) : ⟪EuclideanSpace.single i (a : 𝕜), v⟫ = con
j a * v i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem repr_apply_apply (b : OrthonormalBasis ι 𝕜 E) (v : E) (i : ι) :
    b.repr v i = ⟪b i, v⟫ := by
  classical
    rw [← b.repr.inner_map_map (b i) v, b.repr_self i, EuclideanSpace.inner_single_left]
    simp only [one_mul, map_one]

@[simp]
/-
**OrthonormalBasis.orthonormal** 是 Mathlib 中的一个定理，位于命名空间 `OrthonormalBasis`。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : RCLike 𝕜] {E : Type u_4} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : Fintype ι] (
b : OrthonormalBasis ι 𝕜 E), Orthonormal 𝕜 ⇑b
参数：b : OrthonormalBasis ι 𝕜 E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `orthonormal_iff_ite`：orthonormal_iff_ite [DecidableEq ι] {v : ι -> E} : 
Orthonormal 𝕜 v ↔ forall i j, ⟪v i, v j⟫ = if i = j then (1 : 𝕜) else (0 : 𝕜)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearIsometryEquiv.inner_map_map`：LinearIsometryEquiv.inner_map_map (f 
: E ≃ₗᵢ[𝕜] E') (x y : E) : ⟪f x, f y⟫ = ⟪x, y⟫
· 使用定理 `OrthonormalBasis.repr_self`：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : RCLi
ke 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpa
ce 𝕜 E] [inst_3 …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `EuclideanSpace.inner_single_left`：EuclideanSpace.inner_single_left (i : 
ι) (a : 𝕜) (v : EuclideanSpace 𝕜 ι) : ⟪EuclideanSpace.single i (a : 𝕜), v⟫ = con
j a * v i
· 使用引理 `PiLp.single_apply`：single_apply [Zero 𝕜] (i : ι) (a : 𝕜) (j : ι) : (sing
le p i a : PiLp p (fun _ => 𝕜)) j = ite (j = i) a 0
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
protected theorem orthonormal (b : OrthonormalBasis ι 𝕜 E) : Orthonormal 𝕜 b := by
  classical
    rw [orthonormal_iff_ite]
    intro i j
    rw [← b.repr.inner_map_map (b i) (b j), b.repr_self i, b.repr_self j,
      EuclideanSpace.inner_single_left, PiLp.single_apply, map_one, one_mul]

@[simp]
/-
**OrthonormalBasis.norm_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `OrthonormalBasis`。
形式化陈述：norm_eq_one (b : OrthonormalBasis ι 𝕜 E) (i : ι) : ‖b i‖ = 1
参数：b : OrthonormalBasis ι 𝕜 E；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Orthonormal.norm_eq_one`：Orthonormal.norm_eq_one {v : ι -> E} (h : Ortho
normal 𝕜 v) (i : ι) : ‖v i‖ = 1
· 使用定理 `OrthonormalBasis.orthonormal`：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : RC
Like 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductS
pace 𝕜 E] [inst_3 …
-/
lemma norm_eq_one (b : OrthonormalBasis ι 𝕜 E) (i : ι) :
    ‖b i‖ = 1 := b.orthonormal.norm_eq_one i

@[simp]
/-
**OrthonormalBasis.nnnorm_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `OrthonormalBasis`。
形式化陈述：nnnorm_eq_one (b : OrthonormalBasis ι 𝕜 E) (i : ι) : ‖b i‖₊ = 1
参数：b : OrthonormalBasis ι 𝕜 E；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Orthonormal.nnnorm_eq_one`：Orthonormal.nnnorm_eq_one {v : ι -> E} (h : O
rthonormal 𝕜 v) (i : ι) : ‖v i‖₊ = 1
· 使用定理 `OrthonormalBasis.orthonormal`：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : RC
Like 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductS
pace 𝕜 E] [inst_3 …
-/
lemma nnnorm_eq_one (b : OrthonormalBasis ι 𝕜 E) (i : ι) :
    ‖b i‖₊ = 1 := b.orthonormal.nnnorm_eq_one i

@[simp]
/-
**OrthonormalBasis.enorm_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `OrthonormalBasis`。
形式化陈述：enorm_eq_one (b : OrthonormalBasis ι 𝕜 E) (i : ι) : ‖b i‖ₑ = 1
参数：b : OrthonormalBasis ι 𝕜 E；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Orthonormal.enorm_eq_one`：Orthonormal.enorm_eq_one {v : ι -> E} (h : Ort
honormal 𝕜 v) (i : ι) : ‖v i‖ₑ = 1
· 使用定理 `OrthonormalBasis.orthonormal`：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : RC
Like 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductS
pace 𝕜 E] [inst_3 …
-/
lemma enorm_eq_one (b : OrthonormalBasis ι 𝕜 E) (i : ι) :
    ‖b i‖ₑ = 1 := b.orthonormal.enorm_eq_one i

@[simp]
/-
**OrthonormalBasis.inner_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `OrthonormalBasis`。
形式化陈述：inner_eq_zero (b : OrthonormalBasis ι 𝕜 E) {i j : ι} (hij : i != j) : ⟪b i
, b j⟫ = 0
参数：b : OrthonormalBasis ι 𝕜 E；hij : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Orthonormal.inner_eq_zero`：Orthonormal.inner_eq_zero {v : ι -> E} {i j :
 ι} (h : Orthonormal 𝕜 v) (hij : i != j) : ⟪v i, v j⟫ = 0
· 使用定理 `OrthonormalBasis.orthonormal`：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : RC
Like 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductS
pace 𝕜 E] [inst_3 …
-/
lemma inner_eq_zero (b : OrthonormalBasis ι 𝕜 E) {i j : ι} (hij : i ≠ j) :
    ⟪b i, b j⟫ = 0 := b.orthonormal.inner_eq_zero hij
/-
**OrthonormalBasis.inner_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `OrthonormalBasis`。
形式化陈述：inner_eq_one (b : OrthonormalBasis ι 𝕜 E) (i : ι) : ⟪b i, b i⟫ = 1
参数：b : OrthonormalBasis ι 𝕜 E；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
· 使用引理 `OrthonormalBasis.norm_eq_one`：norm_eq_one (b : OrthonormalBasis ι 𝕜 E) (
i : ι) : ‖b i‖ = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inner_eq_one (b : OrthonormalBasis ι 𝕜 E) (i : ι) : ⟪b i, b i⟫ = 1 := by
  simp
/-
**OrthonormalBasis.inner_eq_ite** 是 Mathlib 中的一个引理，位于命名空间 `OrthonormalBasis`。
形式化陈述：inner_eq_ite [DecidableEq ι] (b : OrthonormalBasis ι 𝕜 E) (i j : ι) : ⟪b i
, b j⟫ = if i = j then 1 else 0
参数：b : OrthonormalBasis ι 𝕜 E；i j : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inner_self_eq_norm_sq_to_K`：inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ 
= (‖x‖ : 𝕜) ^ 2
· 使用引理 `OrthonormalBasis.norm_eq_one`：norm_eq_one (b : OrthonormalBasis ι 𝕜 E) (
i : ι) : ‖b i‖ = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `OrthonormalBasis.inner_eq_zero`：inner_eq_zero (b : OrthonormalBasis ι 𝕜 
E) {i j : ι} (hij : i != j) : ⟪b i, b j⟫ = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
-/
lemma inner_eq_ite [DecidableEq ι] (b : OrthonormalBasis ι 𝕜 E) (i j : ι) :
    ⟪b i, b j⟫ = if i = j then 1 else 0 := by
  by_cases h : i = j <;> simp [h]

/-- The `Basis ι 𝕜 E` underlying the `OrthonormalBasis` -/
/-
**OrthonormalBasis.toBasis** 是 Mathlib 中的一个定义，位于命名空间 `OrthonormalBasis`。
形式化陈述：{ι : Type u_1} →   {𝕜 : Type u_3} →     [inst : RCLike 𝕜] →       {E : Typ
e u_4} →         [inst_1 : NormedAddCommGroup E] →           [inst_2 : InnerProd
uctSpace 𝕜 E] → [inst_3 : Fintype ι] → OrthonormalBasis ι 𝕜 E → Module.Basis ι 𝕜
 E
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)

--- 原说明 ---
The `Basis ι 𝕜 E` underlying the `OrthonormalBasis`
-/
protected def toBasis (b : OrthonormalBasis ι 𝕜 E) : Basis ι 𝕜 E :=
  Basis.ofEquivFun (b.repr.toLinearEquiv.trans (WithLp.linearEquiv 2 𝕜 (ι → 𝕜)))

@[simp]
/-
**OrthonormalBasis.coe_toBasis** 是 Mathlib 中的一个定理，位于命名空间 `OrthonormalBasis`。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : RCLike 𝕜] {E : Type u_4} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : Fintype ι] (
b : OrthonormalBasis ι 𝕜 E), ⇑b.toBasis = ⇑b
参数：b : OrthonormalBasis ι 𝕜 E。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem coe_toBasis (b : OrthonormalBasis ι 𝕜 E) : (⇑b.toBasis : ι → E) = ⇑b := rfl

@[simp]
/-
**OrthonormalBasis.coe_toBasis_repr** 是 Mathlib 中的一个定理，位于命名空间 `OrthonormalBasis`
。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : RCLike 𝕜] {E : Type u_4} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : Fintype ι] (
b : OrthonormalBasis ι 𝕜 E),   b.toBasis.equivFun = b.repr.toLinearEquiv ≪≫ₗ Wit
hLp.linearEquiv 2 𝕜 (ι → 𝕜)
参数：b : OrthonormalBasis ι 𝕜 E；ι → 𝕜。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.equivFun_ofEquivFun`：∀ {ι : Type u_1} {R : Type u_3} {M : T
ype u_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Modul
e R M] [inst_3 : Finit…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
-/
protected theorem coe_toBasis_repr (b : OrthonormalBasis ι 𝕜 E) :
    b.toBasis.equivFun = b.repr.toLinearEquiv.trans (WithLp.linearEquiv 2 𝕜 (ι → 𝕜)) :=
  Basis.equivFun_ofEquivFun _

@[simp]
/-
**OrthonormalBasis.coe_toBasis_repr_apply** 是 Mathlib 中的一个定理，位于命名空间 `Orthonormal
Basis`。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : RCLike 𝕜] {E : Type u_4} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : Fintype ι] (
b : OrthonormalBasis ι 𝕜 E) (x : E) (i : ι),   (b.toBasis.repr x) i = (b.repr x)
.ofLp i
参数：b : OrthonormalBasis ι 𝕜 E；x : E；i : ι；b.toBasis.repr x；b.repr x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `OrthonormalBasis.coe_toBasis_repr`：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst
 : RCLike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerPro
ductSpace 𝕜 E] [inst_3 …
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `WithLp.linearEquiv_apply`：∀ (p : ENNReal) (K : Type u_1) (V : Type u_4) 
[inst : Semiring K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]   (a 
: WithLp p V),…
· 使用定理 `WithLp.addEquiv_apply`：∀ (p : ENNReal) (V : Type u_4) [inst : AddCommGro
up V] (self : WithLp p V), (WithLp.addEquiv p V) self = self.ofLp
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem coe_toBasis_repr_apply (b : OrthonormalBasis ι 𝕜 E) (x : E) (i : ι) :
    b.toBasis.repr x i = b.repr x i := by
  simp [← Basis.equivFun_apply]
/-
**OrthonormalBasis.sum_repr** 是 Mathlib 中的一个定理，位于命名空间 `OrthonormalBasis`。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : RCLike 𝕜] {E : Type u_4} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : Fintype ι] (
b : OrthonormalBasis ι 𝕜 E) (x : E),   ∑ i, (b.repr x).ofLp i • b i = x
参数：b : OrthonormalBasis ι 𝕜 E；x : E；b.repr x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrthonormalBasis.coe_toBasis_repr_apply`：∀ {ι : Type u_1} {𝕜 : Type u_3}
 [inst : RCLike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : In
nerProductSpace 𝕜 E] [inst_3 …
· 使用定理 `Module.Basis.sum_repr`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} [i
nst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [ins
t_3 : Finty…
-/
protected theorem sum_repr (b : OrthonormalBasis ι 𝕜 E) (x : E) : ∑ i, b.repr x i • b i = x := by
  simp_rw [← b.coe_toBasis_repr_apply, ← b.coe_toBasis]
  exact b.toBasis.sum_repr x

open scoped InnerProductSpace in
/-
**OrthonormalBasis.sum_repr'** 是 Mathlib 中的一个定理，位于命名空间 `OrthonormalBasis`。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : RCLike 𝕜] {E : Type u_4} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : Fintype ι] (
b : OrthonormalBasis ι 𝕜 E) (x : E),   ∑ i, inner 𝕜 (b i) x • b i = x
参数：b : OrthonormalBasis ι 𝕜 E；x : E；b i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrthonormalBasis.sum_repr`：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : RCLik
e 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpac
e 𝕜 E] [inst_3 …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `OrthonormalBasis.repr_apply_apply`：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst
 : RCLike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerPro
ductSpace 𝕜 E] [inst_3 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem sum_repr' (b : OrthonormalBasis ι 𝕜 E) (x : E) : ∑ i, ⟪b i, x⟫_𝕜 • b i = x := by
  nth_rw 2 [← (b.sum_repr x)]
  simp_rw [b.repr_apply_apply x]
/-
**OrthonormalBasis.sum_repr_symm** 是 Mathlib 中的一个定理，位于命名空间 `OrthonormalBasis`。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : RCLike 𝕜] {E : Type u_4} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : Fintype ι] (
b : OrthonormalBasis ι 𝕜 E) (v : EuclideanSpace 𝕜 ι),   ∑ i, v.ofLp i • b i = b.
repr.symm v
参数：b : OrthonormalBasis ι 𝕜 E；v : EuclideanSpace 𝕜 ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `OrthonormalBasis.coe_toBasis_repr`：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst
 : RCLike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerPro
ductSpace 𝕜 E] [inst_3 …
· 使用定理 `WithLp.linearEquiv_symm_apply`：∀ (p : ENNReal) (K : Type u_1) (V : Type 
u_4) [inst : Semiring K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V] 
  (a : V), (WithLp.…
· 使用定理 `WithLp.addEquiv_symm_apply`：∀ (p : ENNReal) (V : Type u_4) [inst : AddCo
mmGroup V] (ofLp : V), (WithLp.addEquiv p V).symm ofLp = WithLp.toLp p ofLp
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.equivFun_symm_apply`：∀ {ι : Type u_1} {R : Type u_3} {M : T
ype u_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Modul
e R M] [inst_3 : Finty…
-/
protected theorem sum_repr_symm (b : OrthonormalBasis ι 𝕜 E) (v : EuclideanSpace 𝕜 ι) :
    ∑ i, v i • b i = b.repr.symm v := by simpa using (b.toBasis.equivFun_symm_apply v).symm
/-
**OrthonormalBasis.sum_inner_mul_inner** 是 Mathlib 中的一个定理，位于命名空间 `OrthonormalBas
is`。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : RCLike 𝕜] {E : Type u_4} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : Fintype ι] (
b : OrthonormalBasis ι 𝕜 E) (x y : E),   ∑ i, inner 𝕜 x (b i) * inner 𝕜 (b i) y 
= inner 𝕜 x y
参数：b : OrthonormalBasis ι 𝕜 E；x y : E；b i；b i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `OrthonormalBasis.sum_repr`：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : RCLik
e 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpac
e 𝕜 E] [inst_3 …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `OrthonormalBasis.repr_apply_apply`：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst
 : RCLike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerPro
ductSpace 𝕜 E] [inst_3 …
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
-/
protected theorem sum_inner_mul_inner (b : OrthonormalBasis ι 𝕜 E) (x y : E) :
    ∑ i, ⟪x, b i⟫ * ⟪b i, y⟫ = ⟪x, y⟫ := by
  have := congr_arg (innerSL 𝕜 x) (b.sum_repr y)
  rw [map_sum] at this
  convert! this
  rw [map_smul, b.repr_apply_apply, mul_comm]
  simp
/-
**OrthonormalBasis.sum_sq_norm_inner_right** 是 Mathlib 中的一个引理，位于命名空间 `Orthonorma
lBasis`。
形式化陈述：sum_sq_norm_inner_right (b : OrthonormalBasis ι 𝕜 E) (x : E) : ∑ i, ‖⟪b i,
 x⟫‖ ^ 2 = ‖x‖ ^ 2
参数：b : OrthonormalBasis ι 𝕜 E；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_eq_sqrt_re_inner`：norm_eq_sqrt_re_inner (x : E) : ‖x‖ = √(re ⟪x, x⟫
)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrthonormalBasis.sum_inner_mul_inner`：∀ {ι : Type u_1} {𝕜 : Type u_3} [i
nst : RCLike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : Inner
ProductSpace 𝕜 E] [inst_3 …
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `inner_mul_symm_re_eq_norm`：inner_mul_symm_re_eq_norm (x y : E) : re (⟪x,
 y⟫ * ⟪y, x⟫) = ‖⟪x, y⟫ * ⟪y, x⟫‖
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `inner_conj_symm`：inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫
· 使用引理 `norm_star`：norm_star (x : E) : ‖x⋆‖ = ‖x‖
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用定理 `RCLike.instCStarRing`：∀ {K : Type u_1} [inst : RCLike K], CStarRing K
· 使用定理 `Real.sq_sqrt`：sq_sqrt (h : 0 <= x) : √x ^ 2 = x
· 使用定理 `Fintype.sum_nonneg`：∀ {ι : Type u_1} {M : Type u_4} [inst : Fintype ι] [
inst_1 : AddCommMonoid M] [inst_2 : Preorder M] [AddLeftMono M]   {f : ι → M}, 0
 ≤ f → 0…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Even.pow_nonneg`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : LinearOr
der R] [IsOrderedRing R] [ExistsAddOfLE R] {n : ℕ},   Even n → ∀ (a : R), 0 ≤ a 
^ n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `even_two_mul`：even_two_mul (a : α) : Even (2 * a)
-/
lemma sum_sq_norm_inner_right (b : OrthonormalBasis ι 𝕜 E) (x : E) :
    ∑ i, ‖⟪b i, x⟫‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [@norm_eq_sqrt_re_inner 𝕜, ← OrthonormalBasis.sum_inner_mul_inner b x x, map_sum]
  simp_rw [inner_mul_symm_re_eq_norm, norm_mul, ← inner_conj_symm x, starRingEnd_apply,
    norm_star, ← pow_two]
  rw [Real.sq_sqrt]
  exact Fintype.sum_nonneg fun _ ↦ by positivity
/-
**OrthonormalBasis.sum_sq_norm_inner_left** 是 Mathlib 中的一个引理，位于命名空间 `Orthonormal
Basis`。
形式化陈述：sum_sq_norm_inner_left (b : OrthonormalBasis ι 𝕜 E) (x : E) : ∑ i, ‖⟪x, b 
i⟫‖ ^ 2 = ‖x‖ ^ 2
参数：b : OrthonormalBasis ι 𝕜 E；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inner_conj_symm`：inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫
· 使用定理 `RCLike.norm_conj`：norm_conj (z : K) : ‖conj z‖ = ‖z‖
· 使用引理 `OrthonormalBasis.sum_sq_norm_inner_right`：sum_sq_norm_inner_right (b : O
rthonormalBasis ι 𝕜 E) (x : E) : ∑ i, ‖⟪b i, x⟫‖ ^ 2 = ‖x‖ ^ 2
-/
lemma sum_sq_norm_inner_left (b : OrthonormalBasis ι 𝕜 E) (x : E) :
    ∑ i, ‖⟪x, b i⟫‖ ^ 2 = ‖x‖ ^ 2 := by
  convert! sum_sq_norm_inner_right b x using 2 with i -
  rw [← inner_conj_symm, RCLike.norm_conj]

open scoped RealInnerProductSpace in
/-
**OrthonormalBasis.sum_sq_inner_right** 是 Mathlib 中的一个定理，位于命名空间 `OrthonormalBasi
s`。
形式化陈述：sum_sq_inner_right {E : Type*} [NormedAddCommGroup E] [InnerProductSpace R
eal E] (b : OrthonormalBasis ι Real E) (x : E) : ∑ i : ι, ⟪b i, x⟫ ^ 2 = ‖x‖ ^ 2
参数：b : OrthonormalBasis ι Real E；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `OrthonormalBasis.sum_sq_norm_inner_right`：sum_sq_norm_inner_right (b : O
rthonormalBasis ι 𝕜 E) (x : E) : ∑ i, ‖⟪b i, x⟫‖ ^ 2 = ‖x‖ ^ 2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `sq_abs`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] (a : α
), |a| ^ 2 = a ^ 2
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_sq_inner_right {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (b : OrthonormalBasis ι ℝ E) (x : E) :
    ∑ i : ι, ⟪b i, x⟫ ^ 2 = ‖x‖ ^ 2 := by
  rw [← b.sum_sq_norm_inner_right]
  simp

open scoped RealInnerProductSpace in
/-
**OrthonormalBasis.sum_sq_inner_left** 是 Mathlib 中的一个定理，位于命名空间 `OrthonormalBasis
`。
形式化陈述：sum_sq_inner_left {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace 
Real E] [Fintype ι] (b : OrthonormalBasis ι Real E) (x : E) : ∑ i : ι, ⟪x, b i⟫ 
^ 2 = ‖x‖ ^ 2
参数：b : OrthonormalBasis ι Real E；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrthonormalBasis.sum_sq_inner_right`：sum_sq_inner_right {E : Type*} [Nor
medAddCommGroup E] [InnerProductSpace Real E] (b : OrthonormalBasis ι Real E) (x
 : E) : ∑ i : ι, ⟪b i, x⟫…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `real_inner_comm`：real_inner_comm (x y : F) : ⟪y, x⟫_Real = ⟪x, y⟫_Real
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_sq_inner_left {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Fintype ι] (b : OrthonormalBasis ι ℝ E) (x : E) :
    ∑ i : ι, ⟪x, b i⟫ ^ 2 = ‖x‖ ^ 2 := by
  simp_rw [← b.sum_sq_inner_right, real_inner_comm]
/-
**OrthonormalBasis.norm_le_card_mul_iSup_norm_inner** 是 Mathlib 中的一个引理，位于命名空间 `O
rthonormalBasis`。
形式化陈述：norm_le_card_mul_iSup_norm_inner (b : OrthonormalBasis ι 𝕜 E) (x : E) : ‖x
‖ <= √(Fintype.card ι) * ⨆ i, ‖⟪b i, x⟫‖
参数：b : OrthonormalBasis ι 𝕜 E；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `OrthonormalBasis.sum_sq_norm_inner_right`：sum_sq_norm_inner_right (b : O
rthonormalBasis ι 𝕜 E) (x : E) : ∑ i, ‖⟪b i, x⟫‖ ^ 2 = ‖x‖ ^ 2
· 使用定理 `Real.sqrt_sq`：sqrt_sq (h : 0 <= x) : √(x ^ 2) = x
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Real.sqrt_monotone`：sqrt_monotone : Monotone Real.sqrt
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `pow_le_pow_left₀`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 :
 Preorder M₀] {a b : M₀} [PosMulMono M₀] [MulPosMono M₀],   0 ≤ a → a ≤ b → ∀ (n
 : ℕ),…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `le_ciSup`：le_ciSup {f : ι -> α} (H : BddAbove (range f)) (c : ι) : f c <
= iSup f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `Real.sqrt_mul`：sqrt_mul {x : Real} (hx : 0 <= x) (y : Real) : √(x * y) =
 √x * √y
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `Real.iSup_of_isEmpty`：∀ {ι : Sort u_1} [IsEmpty ι] (f : ι → ℝ), ⨆ i, f i
 = 0
· 使用定理 `le_ciSup_of_le`：le_ciSup_of_le {f : ι -> α} (H : BddAbove (range f)) (c 
: ι) (h : a <= f c) : a <= iSup f
-/
lemma norm_le_card_mul_iSup_norm_inner (b : OrthonormalBasis ι 𝕜 E) (x : E) :
    ‖x‖ ≤ √(Fintype.card ι) * ⨆ i, ‖⟪b i, x⟫‖ := by
  calc ‖x‖
  _ = √(∑ i, ‖⟪b i, x⟫‖ ^ 2) := by rw [sum_sq_norm_inner_right, Real.sqrt_sq (by positivity)]
  _ ≤ √(∑ _ : ι, (⨆ j, ‖⟪b j, x⟫‖) ^ 2) := by
    gcongr with i
    exact le_ciSup (f := fun j ↦ ‖⟪b j, x⟫‖) (by simp) i
  _ = √(Fintype.card ι) * ⨆ i, ‖⟪b i, x⟫‖ := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_nonneg, Real.sqrt_mul]
    congr
    rw [Real.sqrt_sq]
    cases isEmpty_or_nonempty ι
    · simp
    · exact le_ciSup_of_le (by simp) (Nonempty.some inferInstance) (by positivity)
/-
**OrthonormalBasis.orthogonalProjectionOnto_apply_eq_sum** 是 Mathlib 中的一个定理，位于命名
空间 `OrthonormalBasis`。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : RCLike 𝕜] {E : Type u_4} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : Fintype ι] {
U : Submodule 𝕜 E} [inst_4 : U.HasOrthogonalProjection]   (b : OrthonormalBasis 
ι 𝕜 ↥U) (x : E), U.orthogonalProjectionOnto x = ∑ i, inner 𝕜 (↑(b i)) x • b i
参数：b : OrthonormalBasis ι 𝕜 ↥U；x : E；↑(b i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `OrthonormalBasis.repr_apply_apply`：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst
 : RCLike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerPro
ductSpace 𝕜 E] [inst_3 …
· 使用定理 `Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left`：inner_orthogona
lProjectionOnto_eq_of_mem_left [K.HasOrthogonalProjection] (u : K) (v : E) : ⟪u,
 K.orthogonalProjectionOnto v⟫ = ⟪(u : E), v⟫
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrthonormalBasis.sum_repr`：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : RCLik
e 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpac
e 𝕜 E] [inst_3 …
-/
protected theorem orthogonalProjectionOnto_apply_eq_sum {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (b : OrthonormalBasis ι 𝕜 U) (x : E) :
    U.orthogonalProjectionOnto x = ∑ i, ⟪(b i : E), x⟫ • b i := by
  simpa only [b.repr_apply_apply, inner_orthogonalProjectionOnto_eq_of_mem_left] using
    (b.sum_repr (U.orthogonalProjectionOnto x)).symm

@[deprecated (since := "2026-05-05")] alias orthogonalProjection_apply_eq_sum :=
  OrthonormalBasis.orthogonalProjectionOnto_apply_eq_sum
/-
**OrthonormalBasis.orthogonalProjectionOnto_eq_sum_rankOne** 是 Mathlib 中的一个定理，位于
命名空间 `OrthonormalBasis`。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : RCLike 𝕜] {E : Type u_4} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : Fintype ι] {
U : Submodule 𝕜 E} [inst_4 : U.HasOrthogonalProjection]   (b : OrthonormalBasis 
ι 𝕜 ↥U), U.orthogonalProjectionOnto = ∑ i, ((InnerProductSpace.rankOne 𝕜) (b i))
 ↑(b i)
参数：b : OrthonormalBasis ι 𝕜 ↥U；(InnerProductSpace.rankOne 𝕜) (b i)；b i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrthonormalBasis.orthogonalProjectionOnto_apply_eq_sum`：∀ {ι : Type u_1}
 {𝕜 : Type u_3} [inst : RCLike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]
   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 …
· 使用定理 `AddSubmonoidClass.coe_finsetSum`：∀ {B : Type u_3} {S : B} {ι : Type u_4}
 {M : Type u_5} [inst : AddCommMonoid M] [inst_1 : SetLike B M]   [inst_2 : AddS
ubmonoidClass B M] (f…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem orthogonalProjectionOnto_eq_sum_rankOne {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (b : OrthonormalBasis ι 𝕜 U) :
    U.orthogonalProjectionOnto = ∑ i, InnerProductSpace.rankOne 𝕜 (b i) (b i : E) := by
  ext; simp [b.orthogonalProjectionOnto_apply_eq_sum]

@[deprecated (since := "2026-05-05")] alias orthogonalProjection_eq_sum_rankOne :=
  OrthonormalBasis.orthogonalProjectionOnto_eq_sum_rankOne
/-
**OrthonormalBasis.starProjection_eq_sum_rankOne** 是 Mathlib 中的一个定理，位于命名空间 `Orth
onormalBasis`。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : RCLike 𝕜] {E : Type u_4} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : Fintype ι] {
U : Submodule 𝕜 E} [inst_4 : U.HasOrthogonalProjection]   (b : OrthonormalBasis 
ι 𝕜 ↥U), U.starProjection = ∑ i, ((InnerProductSpace.rankOne 𝕜) ↑(b i)) ↑(b i)
参数：b : OrthonormalBasis ι 𝕜 ↥U；(InnerProductSpace.rankOne 𝕜) ↑(b i)；b i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用定理 `OrthonormalBasis.orthogonalProjectionOnto_eq_sum_rankOne`：∀ {ι : Type u_
1} {𝕜 : Type u_3} [inst : RCLike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup 
E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 …
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem starProjection_eq_sum_rankOne {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (b : OrthonormalBasis ι 𝕜 U) :
    U.starProjection = ∑ i, InnerProductSpace.rankOne 𝕜 (b i : E) (b i : E) := by
  ext; simp [starProjection, b.orthogonalProjectionOnto_eq_sum_rankOne]
/-
**OrthonormalBasis.sum_rankOne_eq_id** 是 Mathlib 中的一个引理，位于命名空间 `OrthonormalBasis
`。
形式化陈述：sum_rankOne_eq_id (b : OrthonormalBasis ι 𝕜 E) : ∑ i, InnerProductSpace.ra
nkOne 𝕜 (b i) (b i) = .id 𝕜 E
参数：b : OrthonormalBasis ι 𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `ContinuousLinearMap.instIsZeroApply`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [
inst : Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [
inst_2 : TopologicalSpace…
· 使用定理 `OrthonormalBasis.sum_repr'`：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : RCLi
ke 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpa
ce 𝕜 E] [inst_3 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sum_rankOne_eq_id (b : OrthonormalBasis ι 𝕜 E) :
    ∑ i, InnerProductSpace.rankOne 𝕜 (b i) (b i) = .id 𝕜 E := by ext; simp [b.sum_repr']

/-- Mapping an orthonormal basis along a `LinearIsometryEquiv`. -/
/-
**OrthonormalBasis.map** 是 Mathlib 中的一个定义，位于命名空间 `OrthonormalBasis`。
形式化陈述：{ι : Type u_1} →   {𝕜 : Type u_3} →     [inst : RCLike 𝕜] →       {E : Typ
e u_4} →         [inst_1 : NormedAddCommGroup E] →           [inst_2 : InnerProd
uctSpace 𝕜 E] →             [inst_3 : Fintype ι] →               {G : Type u_7} 
→                 [inst_4 : NormedAddCommGroup G] →                   [inst_5 : 
InnerProductSpace 𝕜 G] → OrthonormalBasis ι 𝕜 E → (E ≃ₗᵢ[𝕜] G) → OrthonormalBasi
s ι 𝕜 G
参数：E ≃ₗᵢ[𝕜] G。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)

--- 原说明 ---
Mapping an orthonormal basis along a `LinearIsometryEquiv`.
-/
protected def map {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    (b : OrthonormalBasis ι 𝕜 E) (L : E ≃ₗᵢ[𝕜] G) : OrthonormalBasis ι 𝕜 G where
  repr := L.symm.trans b.repr

@[simp]
/-
**OrthonormalBasis.map_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrthonormalBasis`。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : RCLike 𝕜] {E : Type u_4} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : Fintype ι] {
G : Type u_7} [inst_4 : NormedAddCommGroup G]   [inst_5 : InnerProductSpace 𝕜 G]
 (b : OrthonormalBasis ι 𝕜 E) (L : E ≃ₗᵢ[𝕜] G) (i : ι), (b.map L) i = L (b i)
参数：b : OrthonormalBasis ι 𝕜 E；L : E ≃ₗᵢ[𝕜] G；i : ι；b.map L；b i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem map_apply {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    (b : OrthonormalBasis ι 𝕜 E) (L : E ≃ₗᵢ[𝕜] G) (i : ι) : b.map L i = L (b i) :=
  rfl
/-
**OrthonormalBasis.coe_map** 是 Mathlib 中的一个引理，位于命名空间 `OrthonormalBasis`。
形式化陈述：coe_map {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] (b : Or
thonormalBasis ι 𝕜 E) (L : E ≃ₗᵢ[𝕜] G) : ⇑(b.map L) = L ∘ b
参数：b : OrthonormalBasis ι 𝕜 E；L : E ≃ₗᵢ[𝕜] G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_map {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    (b : OrthonormalBasis ι 𝕜 E) (L : E ≃ₗᵢ[𝕜] G) : ⇑(b.map L) = L ∘ b := rfl

@[simp]
/-
**OrthonormalBasis.toBasis_map** 是 Mathlib 中的一个定理，位于命名空间 `OrthonormalBasis`。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : RCLike 𝕜] {E : Type u_4} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : Fintype ι] {
G : Type u_7} [inst_4 : NormedAddCommGroup G]   [inst_5 : InnerProductSpace 𝕜 G]
 (b : OrthonormalBasis ι 𝕜 E) (L : E ≃ₗᵢ[𝕜] G),   (b.map L).toBasis = b.toBasis.
map L.toLinearEquiv
参数：b : OrthonormalBasis ι 𝕜 E；L : E ≃ₗᵢ[𝕜] G；b.map L。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem toBasis_map {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    (b : OrthonormalBasis ι 𝕜 E) (L : E ≃ₗᵢ[𝕜] G) :
    (b.map L).toBasis = b.toBasis.map L.toLinearEquiv :=
  rfl

/-- A basis that is orthonormal is an orthonormal basis. -/
/-
**OrthonormalBasis._root_.Module.Basis.toOrthonormalBasis** 是 Mathlib 中的一个定义，位于命
名空间 `OrthonormalBasis`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A basis that is orthonormal is an orthonormal basis.
-/
def _root_.Module.Basis.toOrthonormalBasis (v : Basis ι 𝕜 E) (hv : Orthonormal 𝕜 v) :
    OrthonormalBasis ι 𝕜 E :=
  OrthonormalBasis.ofRepr <|
    LinearEquiv.isometryOfInner (v.equivFun.trans (WithLp.linearEquiv 2 𝕜 (ι → 𝕜)).symm)
      (by
        intro x y
        let p : EuclideanSpace 𝕜 ι := toLp 2 (v.equivFun x)
        let q : EuclideanSpace 𝕜 ι := toLp 2 (v.equivFun y)
        have key : ⟪p, q⟫ = ⟪∑ i, p i • v i, ∑ i, q i • v i⟫ := by
          simp [inner_sum, inner_smul_right, hv.inner_left_fintype, PiLp.inner_apply]
        convert! key
        · rw [← v.equivFun.symm_apply_apply x, v.equivFun_symm_apply]
        · rw [← v.equivFun.symm_apply_apply y, v.equivFun_symm_apply])

@[simp]
/-
**OrthonormalBasis._root_.Module.Basis.coe_toOrthonormalBasis_repr** 是 Mathlib 中
的一个定理，位于命名空间 `OrthonormalBasis`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Module.Basis.coe_toOrthonormalBasis_repr (v : Basis ι 𝕜 E) (hv : Orthonormal 𝕜 v) :
    ((v.toOrthonormalBasis hv).repr : E → EuclideanSpace 𝕜 ι) =
    v.equivFun.trans (WithLp.linearEquiv 2 𝕜 (ι → 𝕜)).symm :=
  rfl

@[simp]
/-
**OrthonormalBasis._root_.Module.Basis.coe_toOrthonormalBasis_repr_symm** 是 Math
lib 中的一个定理，位于命名空间 `OrthonormalBasis`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Module.Basis.coe_toOrthonormalBasis_repr_symm
    (v : Basis ι 𝕜 E) (hv : Orthonormal 𝕜 v) :
    ((v.toOrthonormalBasis hv).repr.symm : EuclideanSpace 𝕜 ι → E) =
    (WithLp.linearEquiv 2 𝕜 (ι → 𝕜)).trans v.equivFun.symm :=
  rfl

@[simp]
/-
**OrthonormalBasis._root_.Module.Basis.toBasis_toOrthonormalBasis** 是 Mathlib 中的
一个定理，位于命名空间 `OrthonormalBasis`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Module.Basis.toBasis_toOrthonormalBasis (v : Basis ι 𝕜 E) (hv : Orthonormal 𝕜 v) :
    (v.toOrthonormalBasis hv).toBasis = v := by
  simp only [OrthonormalBasis.toBasis, Basis.toOrthonormalBasis,
    LinearEquiv.isometryOfInner_toLinearEquiv]
  exact v.ofEquivFun_equivFun

@[simp]
/-
**OrthonormalBasis._root_.Module.Basis.coe_toOrthonormalBasis** 是 Mathlib 中的一个定理
，位于命名空间 `OrthonormalBasis`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Module.Basis.coe_toOrthonormalBasis (v : Basis ι 𝕜 E) (hv : Orthonormal 𝕜 v) :
    (v.toOrthonormalBasis hv : ι → E) = (v : ι → E) :=
  calc
    (v.toOrthonormalBasis hv : ι → E) = ((v.toOrthonormalBasis hv).toBasis : ι → E) := by
      rw [OrthonormalBasis.coe_toBasis]
    _ = (v : ι → E) := by simp

section Singleton
variable {ι 𝕜 : Type*} [Unique ι] [RCLike 𝕜]

variable (ι 𝕜) in
/-- `OrthonormalBasis.singleton ι 𝕜` is the orthonormal basis sending the unique element of `ι` to
`1 : 𝕜`. -/
/-
**OrthonormalBasis.singleton** 是 Mathlib 中的一个定义，位于命名空间 `OrthonormalBasis`。
形式化陈述：(ι : Type u_7) → (𝕜 : Type u_8) → [inst : Unique ι] → [inst_1 : RCLike 𝕜] 
→ OrthonormalBasis ι 𝕜 𝕜
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`OrthonormalBasis.singleton ι 𝕜` is the orthonormal basis sending the unique ele
ment of `ι` to
`1 : 𝕜`.
-/
protected noncomputable def singleton : OrthonormalBasis ι 𝕜 𝕜 :=
  (Basis.singleton ι 𝕜).toOrthonormalBasis (by simp)

@[simp]
/-
**OrthonormalBasis.singleton_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrthonormalBasis`。
形式化陈述：singleton_apply (i) : OrthonormalBasis.singleton ι 𝕜 i = 1
参数：i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.singleton_apply`：singleton_apply (ι R : Type*) [Unique ι] [
Semiring R] (i) : Basis.singleton ι R i = 1
-/
theorem singleton_apply (i) : OrthonormalBasis.singleton ι 𝕜 i = 1 := Basis.singleton_apply _ _ _

@[simp]
/-
**OrthonormalBasis.singleton_repr** 是 Mathlib 中的一个定理，位于命名空间 `OrthonormalBasis`。
形式化陈述：singleton_repr (x i) : (OrthonormalBasis.singleton ι 𝕜).repr x i = x
参数：x i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.singleton_repr`：singleton_repr (ι R : Type*) [Unique ι] [Se
miring R] (x i) : (Basis.singleton ι R).repr x i = x
-/
theorem singleton_repr (x i) : (OrthonormalBasis.singleton ι 𝕜).repr x i = x :=
  Basis.singleton_repr _ _ _ _

@[simp]
/-
**OrthonormalBasis.coe_singleton** 是 Mathlib 中的一个定理，位于命名空间 `OrthonormalBasis`。
形式化陈述：coe_singleton : ⇑(OrthonormalBasis.singleton ι 𝕜) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrthonormalBasis.singleton_apply`：singleton_apply (i) : OrthonormalBasis
.singleton ι 𝕜 i = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_singleton : ⇑(OrthonormalBasis.singleton ι 𝕜) = 1 := by
  ext; simp

@[simp]
/-
**OrthonormalBasis.toBasis_singleton** 是 Mathlib 中的一个定理，位于命名空间 `OrthonormalBasis
`。
形式化陈述：toBasis_singleton : (OrthonormalBasis.singleton ι 𝕜).toBasis = Basis.singl
eton ι 𝕜
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.toBasis_toOrthonormalBasis`：∀ {ι : Type u_1} {𝕜 : Type u_3}
 [inst : RCLike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : In
nerProductSpace 𝕜 E] [inst_3 …
-/
theorem toBasis_singleton : (OrthonormalBasis.singleton ι 𝕜).toBasis = Basis.singleton ι 𝕜 :=
  Basis.toBasis_toOrthonormalBasis _ _

end Singleton

/-- `Pi.orthonormalBasis (B : ∀ i, OrthonormalBasis (ι i) 𝕜 (E i))` is the
`Σ i, ι i`-indexed orthonormal basis on `Π i, E i` given by `B i` on each component. -/
/-
**OrthonormalBasis._root_.Pi.orthonormalBasis** 是 Mathlib 中的一个定义，位于命名空间 `Orthono
rmalBasis`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Pi.orthonormalBasis (B : ∀ i, OrthonormalBasis (ι i) 𝕜 (E i))` is the
`Σ i, ι i`-indexed orthonormal basis on `Π i, E i` given by `B i` on each compon
ent.
-/
protected def _root_.Pi.orthonormalBasis {η : Type*} [Fintype η] {ι : η → Type*}
    [∀ i, Fintype (ι i)] {𝕜 : Type*} [RCLike 𝕜] {E : η → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace 𝕜 (E i)] (B : ∀ i, OrthonormalBasis (ι i) 𝕜 (E i)) :
    OrthonormalBasis ((i : η) × ι i) 𝕜 (PiLp 2 E) where
  repr := .trans
      (.piLpCongrRight 2 fun i => (B i).repr)
      (.symm <| .piLpCurry 𝕜 2 fun _ _ => 𝕜)
/-
**OrthonormalBasis._root_.Pi.orthonormalBasis.toBasis** 是 Mathlib 中的一个定理，位于命名空间 
`OrthonormalBasis`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Pi.orthonormalBasis.toBasis {η : Type*} [Fintype η] {ι : η → Type*}
    [∀ i, Fintype (ι i)] {𝕜 : Type*} [RCLike 𝕜] {E : η → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace 𝕜 (E i)] (B : ∀ i, OrthonormalBasis (ι i) 𝕜 (E i)) :
    (Pi.orthonormalBasis B).toBasis =
      ((Pi.basis fun i : η ↦ (B i).toBasis).map (WithLp.linearEquiv 2 _ _).symm) := by ext; rfl

@[simp]
/-
**OrthonormalBasis._root_.Pi.orthonormalBasis_apply** 是 Mathlib 中的一个定理，位于命名空间 `O
rthonormalBasis`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Pi.orthonormalBasis_apply {η : Type*} [Fintype η] [DecidableEq η] {ι : η → Type*}
    [∀ i, Fintype (ι i)] {𝕜 : Type*} [RCLike 𝕜] {E : η → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace 𝕜 (E i)] (B : ∀ i, OrthonormalBasis (ι i) 𝕜 (E i))
    (j : (i : η) × (ι i)) :
    Pi.orthonormalBasis B j = PiLp.single 2 j.fst (B j.fst j.snd) := by
  classical
  ext k
  obtain ⟨i, j⟩ := j
  simp only [Pi.orthonormalBasis, coe_ofRepr, LinearIsometryEquiv.symm_trans,
    LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.piLpCongrRight_symm,
    LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.piLpCongrRight_apply,
    LinearIsometryEquiv.piLpCurry_apply, PiLp.ofLp_single, PiLp.toLp_apply,
    Sigma.curry_single (γ := fun _ _ => 𝕜)]
  obtain rfl | hi := Decidable.eq_or_ne i k
  · simp
  · simp [hi]

@[simp]
/-
**OrthonormalBasis._root_.Pi.orthonormalBasis_repr** 是 Mathlib 中的一个定理，位于命名空间 `Or
thonormalBasis`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Pi.orthonormalBasis_repr {η : Type*} [Fintype η] {ι : η → Type*}
    [∀ i, Fintype (ι i)] {𝕜 : Type*} [RCLike 𝕜] {E : η → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace 𝕜 (E i)] (B : ∀ i, OrthonormalBasis (ι i) 𝕜 (E i)) (x : (i : η) → E i)
    (j : (i : η) × (ι i)) :
    (Pi.orthonormalBasis B).repr (toLp 2 x) j = (B j.fst).repr (x j.fst) j.snd := rfl

variable {v : ι → E}

/-- A finite orthonormal set that spans is an orthonormal basis -/
/-
**OrthonormalBasis.mk** 是 Mathlib 中的一个定义，位于命名空间 `OrthonormalBasis`。
形式化陈述：{ι : Type u_1} →   {𝕜 : Type u_3} →     [inst : RCLike 𝕜] →       {E : Typ
e u_4} →         [inst_1 : NormedAddCommGroup E] →           [inst_2 : InnerProd
uctSpace 𝕜 E] →             [inst_3 : Fintype ι] →               {v : ι → E} → O
rthonormal 𝕜 v → ⊤ ≤ Submodule.span 𝕜 (Set.range v) → OrthonormalBasis ι 𝕜 E
参数：Set.range v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A finite orthonormal set that spans is an orthonormal basis
-/
protected def mk (hon : Orthonormal 𝕜 v) (hsp : ⊤ ≤ Submodule.span 𝕜 (Set.range v)) :
    OrthonormalBasis ι 𝕜 E :=
  (Basis.mk (Orthonormal.linearIndependent hon) hsp).toOrthonormalBasis (by rwa [Basis.coe_mk])

@[simp]
/-
**OrthonormalBasis.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `OrthonormalBasis`。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : RCLike 𝕜] {E : Type u_4} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : Fintype ι] {
v : ι → E} (hon : Orthonormal 𝕜 v)   (hsp : ⊤ ≤ Submodule.span 𝕜 (Set.range v)),
 ⇑(OrthonormalBasis.mk hon hsp) = v
参数：hon : Orthonormal 𝕜 v；hsp : ⊤ ≤ Submodule.span 𝕜 (Set.range v)；OrthonormalBas
is.mk hon hsp。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrthonormalBasis.mk.eq_1`：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : RCLike
 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace
 𝕜 E] [inst_3 …
· 使用定理 `Module.Basis.coe_toOrthonormalBasis`：∀ {ι : Type u_1} {𝕜 : Type u_3} [in
st : RCLike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerP
roductSpace 𝕜 E] [inst_3 …
· 使用定理 `Module.Basis.coe_mk`：coe_mk : ⇑(Basis.mk hli hsp) = v
-/
protected theorem coe_mk (hon : Orthonormal 𝕜 v) (hsp : ⊤ ≤ Submodule.span 𝕜 (Set.range v)) :
    ⇑(OrthonormalBasis.mk hon hsp) = v := by
  rw [OrthonormalBasis.mk, _root_.Module.Basis.coe_toOrthonormalBasis, Basis.coe_mk]

/-- Any finite subset of an orthonormal family is an `OrthonormalBasis` for its span. -/
/-
**OrthonormalBasis.span** 是 Mathlib 中的一个定义，位于命名空间 `OrthonormalBasis`。
形式化陈述：{ι' : Type u_2} →   {𝕜 : Type u_3} →     [inst : RCLike 𝕜] →       {E : Ty
pe u_4} →         [inst_1 : NormedAddCommGroup E] →           [inst_2 : InnerPro
ductSpace 𝕜 E] →             [inst_3 : DecidableEq E] →               {v' : ι' →
 E} →                 Orthonormal 𝕜 v' → (s : Finset ι') → OrthonormalBasis (↥s)
 𝕜 ↥(Submodule.span 𝕜 ↑(Finset.image v' s))
参数：s : Finset ι'；↥s；Submodule.span 𝕜 ↑(Finset.image v' s)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any finite subset of an orthonormal family is an `OrthonormalBasis` for its span
.
-/
protected def span [DecidableEq E] {v' : ι' → E} (h : Orthonormal 𝕜 v') (s : Finset ι') :
    OrthonormalBasis s 𝕜 (span 𝕜 (s.image v' : Set E)) :=
  let e₀' : Basis s 𝕜 _ :=
    Basis.span (h.linearIndependent.comp ((↑) : s → ι') Subtype.val_injective)
  let e₀ : OrthonormalBasis s 𝕜 _ :=
    OrthonormalBasis.mk
      (by
        convert! orthonormal_span (h.comp ((↑) : s → ι') Subtype.val_injective)
        simp [e₀', Basis.span_apply])
      e₀'.span_eq.ge
  let φ : span 𝕜 (s.image v' : Set E) ≃ₗᵢ[𝕜] span 𝕜 (range (v' ∘ ((↑) : s → ι'))) :=
    LinearIsometryEquiv.ofEq _ _
      (by
        rw [Finset.coe_image, image_eq_range]
        rfl)
  e₀.map φ.symm

@[simp]
/-
**OrthonormalBasis.span_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrthonormalBasis`。
形式化陈述：∀ {ι' : Type u_2} {𝕜 : Type u_3} [inst : RCLike 𝕜] {E : Type u_4} [inst_1 
: NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : DecidableEq
 E] {v' : ι' → E} (h : Orthonormal 𝕜 v') (s : Finset ι')   (i : ↥s), ↑((Orthonor
malBasis.span h s) i) = v' ↑i
参数：h : Orthonormal 𝕜 v'；s : Finset ι'；i : ↥s；(OrthonormalBasis.span h s) i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `OrthonormalBasis.coe_mk`：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : RCLike 
𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace 
𝕜 E] [inst_3 …
· 使用定理 `Module.Basis.span_apply`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} 
[inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] {v
 : ι → M} (hl…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem span_apply [DecidableEq E] {v' : ι' → E} (h : Orthonormal 𝕜 v') (s : Finset ι')
    (i : s) : (OrthonormalBasis.span h s i : E) = v' i := by
  simp only [OrthonormalBasis.span, Basis.span_apply, LinearIsometryEquiv.ofEq_symm,
    OrthonormalBasis.map_apply, OrthonormalBasis.coe_mk, LinearIsometryEquiv.coe_ofEq_apply,
    comp_apply]

open Submodule

/-- A finite orthonormal family of vectors whose span has trivial orthogonal complement is an
orthonormal basis. -/
/-
**OrthonormalBasis.mkOfOrthogonalEqBot** 是 Mathlib 中的一个定义，位于命名空间 `OrthonormalBas
is`。
形式化陈述：{ι : Type u_1} →   {𝕜 : Type u_3} →     [inst : RCLike 𝕜] →       {E : Typ
e u_4} →         [inst_1 : NormedAddCommGroup E] →           [inst_2 : InnerProd
uctSpace 𝕜 E] →             [inst_3 : Fintype ι] →               {v : ι → E} → O
rthonormal 𝕜 v → (Submodule.span 𝕜 (Set.range v))ᗮ = ⊥ → OrthonormalBasis ι 𝕜 E
参数：Submodule.span 𝕜 (Set.range v)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A finite orthonormal family of vectors whose span has trivial orthogonal complem
ent is an
orthonormal basis.
-/
protected def mkOfOrthogonalEqBot (hon : Orthonormal 𝕜 v) (hsp : (span 𝕜 (Set.range v))ᗮ = ⊥) :
    OrthonormalBasis ι 𝕜 E :=
  OrthonormalBasis.mk hon
    (by
      refine Eq.ge ?_
      have : FiniteDimensional 𝕜 (span 𝕜 (range v)) :=
        FiniteDimensional.span_of_finite 𝕜 (finite_range v)
      have : CompleteSpace (span 𝕜 (range v)) := FiniteDimensional.complete 𝕜 _
      rwa [orthogonal_eq_bot_iff] at hsp)

@[simp]
/-
**OrthonormalBasis.coe_of_orthogonal_eq_bot_mk** 是 Mathlib 中的一个定理，位于命名空间 `Orthon
ormalBasis`。
形式化陈述：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : RCLike 𝕜] {E : Type u_4} [inst_1 :
 NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 : Fintype ι] {
v : ι → E} (hon : Orthonormal 𝕜 v)   (hsp : (Submodule.span 𝕜 (Set.range v))ᗮ = 
⊥), ⇑(OrthonormalBasis.mkOfOrthogonalEqBot hon hsp) = v
参数：hon : Orthonormal 𝕜 v；hsp : (Submodule.span 𝕜 (Set.range v))ᗮ = ⊥；Orthonormal
Basis.mkOfOrthogonalEqBot hon hsp。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrthonormalBasis.coe_mk`：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : RCLike 
𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace 
𝕜 E] [inst_3 …
-/
protected theorem coe_of_orthogonal_eq_bot_mk (hon : Orthonormal 𝕜 v)
    (hsp : (span 𝕜 (Set.range v))ᗮ = ⊥) : ⇑(OrthonormalBasis.mkOfOrthogonalEqBot hon hsp) = v :=
  OrthonormalBasis.coe_mk hon _

variable [Fintype ι']

/-- `b.reindex (e : ι ≃ ι')` is an `OrthonormalBasis` indexed by `ι'` -/
/-
**OrthonormalBasis.reindex** 是 Mathlib 中的一个定义，位于命名空间 `OrthonormalBasis`。
形式化陈述：reindex (b : OrthonormalBasis ι 𝕜 E) (e : ι ≃ ι') : OrthonormalBasis ι' 𝕜 
E
参数：b : OrthonormalBasis ι 𝕜 E；e : ι ≃ ι'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)

--- 原说明 ---
`b.reindex (e : ι ≃ ι')` is an `OrthonormalBasis` indexed by `ι'`
-/
def reindex (b : OrthonormalBasis ι 𝕜 E) (e : ι ≃ ι') : OrthonormalBasis ι' 𝕜 E :=
  OrthonormalBasis.ofRepr (b.repr.trans (LinearIsometryEquiv.piLpCongrLeft 2 𝕜 𝕜 e))
/-
**OrthonormalBasis.reindex_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrthonormalBasis`。
形式化陈述：∀ {ι : Type u_1} {ι' : Type u_2} {𝕜 : Type u_3} [inst : RCLike 𝕜] {E : Typ
e u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_
3 : Fintype ι] [inst_4 : Fintype ι'] (b : OrthonormalBasis ι 𝕜 E) (e : ι ≃ ι')  
 (i' : ι'), (b.reindex e) i' = b (e.symm i')
参数：b : OrthonormalBasis ι 𝕜 E；e : ι ≃ ι'；i' : ι'；b.reindex e；e.symm i'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrthonormalBasis.coe_ofRepr`：coe_ofRepr [DecidableEq ι] (e : E ≃ₗᵢ[𝕜] Eu
clideanSpace 𝕜 ι) : ⇑(OrthonormalBasis.ofRepr e) = fun i => e.symm (EuclideanSpa
ce.single i (1 : …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrthonormalBasis.repr_symm_single`：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst
 : RCLike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerPro
ductSpace 𝕜 E] [inst_3 …
· 使用定理 `LinearIsometryEquiv.piLpCongrLeft_symm`：∀ {p : ENNReal} {𝕜 : Type u_1} {
ι : Type u_2} [hp : Fact (1 ≤ p)] [inst : Fintype ι] [inst_1 : Semiring 𝕜]   {ι'
 : Type u_5} [inst_2 : Finty…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `EuclideanSpace.piLpCongrLeft_single`：EuclideanSpace.piLpCongrLeft_single
 {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (e : ι' ≃ ι) (i' : ι') (v : 𝕜) : Lin
earIsometryEquiv.piLpCong…
-/
protected theorem reindex_apply (b : OrthonormalBasis ι 𝕜 E) (e : ι ≃ ι') (i' : ι') :
    (b.reindex e) i' = b (e.symm i') := by
  classical
    dsimp [reindex]
    rw [coe_ofRepr]
    dsimp
    rw [← b.repr_symm_single, LinearIsometryEquiv.piLpCongrLeft_symm,
      EuclideanSpace.piLpCongrLeft_single]

@[simp]
/-
**OrthonormalBasis.reindex_toBasis** 是 Mathlib 中的一个定理，位于命名空间 `OrthonormalBasis`。
形式化陈述：reindex_toBasis (b : OrthonormalBasis ι 𝕜 E) (e : ι ≃ ι') : (b.reindex e).
toBasis = b.toBasis.reindex e
参数：b : OrthonormalBasis ι 𝕜 E；e : ι ≃ ι'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.eq_ofRepr_eq_repr`：eq_ofRepr_eq_repr {b₁ b₂ : Basis ι R M} 
(h : forall x i, b₁.repr x i = b₂.repr x i) : b₁ = b₂
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
-/
theorem reindex_toBasis (b : OrthonormalBasis ι 𝕜 E) (e : ι ≃ ι') :
    (b.reindex e).toBasis = b.toBasis.reindex e := Basis.eq_ofRepr_eq_repr fun _ ↦ congr_fun rfl

@[simp]
/-
**OrthonormalBasis.coe_reindex** 是 Mathlib 中的一个定理，位于命名空间 `OrthonormalBasis`。
形式化陈述：∀ {ι : Type u_1} {ι' : Type u_2} {𝕜 : Type u_3} [inst : RCLike 𝕜] {E : Typ
e u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_
3 : Fintype ι] [inst_4 : Fintype ι'] (b : OrthonormalBasis ι 𝕜 E) (e : ι ≃ ι'), 
  ⇑(b.reindex e) = ⇑b ∘ ⇑e.symm
参数：b : OrthonormalBasis ι 𝕜 E；e : ι ≃ ι'；b.reindex e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `OrthonormalBasis.reindex_apply`：∀ {ι : Type u_1} {ι' : Type u_2} {𝕜 : Ty
pe u_3} [inst : RCLike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst
_2 : InnerProductSpa…
-/
protected theorem coe_reindex (b : OrthonormalBasis ι 𝕜 E) (e : ι ≃ ι') :
    ⇑(b.reindex e) = b ∘ e.symm :=
  funext (b.reindex_apply e)

@[simp]
/-
**OrthonormalBasis.repr_reindex** 是 Mathlib 中的一个定理，位于命名空间 `OrthonormalBasis`。
形式化陈述：∀ {ι : Type u_1} {ι' : Type u_2} {𝕜 : Type u_3} [inst : RCLike 𝕜] {E : Typ
e u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_
3 : Fintype ι] [inst_4 : Fintype ι'] (b : OrthonormalBasis ι 𝕜 E) (e : ι ≃ ι')  
 (x : E) (i' : ι'), ((b.reindex e).repr x).ofLp i' = (b.repr x).ofLp (e.symm i')
参数：b : OrthonormalBasis ι 𝕜 E；e : ι ≃ ι'；x : E；i' : ι'；(b.reindex e).repr x；b.re
pr x；e.symm i'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrthonormalBasis.repr_apply_apply`：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst
 : RCLike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerPro
ductSpace 𝕜 E] [inst_3 …
· 使用定理 `OrthonormalBasis.coe_reindex`：∀ {ι : Type u_1} {ι' : Type u_2} {𝕜 : Type
 u_3} [inst : RCLike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2
 : InnerProductSpa…
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
-/
protected theorem repr_reindex (b : OrthonormalBasis ι 𝕜 E) (e : ι ≃ ι') (x : E) (i' : ι') :
    (b.reindex e).repr x i' = b.repr x (e.symm i') := by
  rw [OrthonormalBasis.repr_apply_apply, b.repr_apply_apply, OrthonormalBasis.coe_reindex,
    comp_apply]

end OrthonormalBasis

namespace EuclideanSpace

variable (𝕜 ι)

/-- The basis `Pi.basisFun`, bundled as an orthonormal basis of `EuclideanSpace 𝕜 ι`. -/
/-
**EuclideanSpace.basisFun** 是 Mathlib 中的一个定义，位于命名空间 `EuclideanSpace`。
形式化陈述：basisFun : OrthonormalBasis ι 𝕜 (EuclideanSpace 𝕜 ι)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)

--- 原说明 ---
The basis `Pi.basisFun`, bundled as an orthonormal basis of `EuclideanSpace 𝕜 ι`
.
-/
noncomputable def basisFun : OrthonormalBasis ι 𝕜 (EuclideanSpace 𝕜 ι) :=
  ⟨LinearIsometryEquiv.refl _ _⟩

@[simp]
/-
**EuclideanSpace.basisFun_apply** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanSpace`。
形式化陈述：basisFun_apply [DecidableEq ι] (i : ι) : basisFun ι 𝕜 i = EuclideanSpace.s
ingle i 1
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiLp.basisFun_apply`：basisFun_apply [DecidableEq ι] (i) : basisFun p 𝕜 ι
 i = single p i 1
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem basisFun_apply [DecidableEq ι] (i : ι) : basisFun ι 𝕜 i = EuclideanSpace.single i 1 :=
  PiLp.basisFun_apply _ _ _ _

@[simp]
/-
**EuclideanSpace.basisFun_repr** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanSpace`。
形式化陈述：basisFun_repr (x : EuclideanSpace 𝕜 ι) (i : ι) : (basisFun ι 𝕜).repr x i =
 x i
参数：x : EuclideanSpace 𝕜 ι；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
-/
theorem basisFun_repr (x : EuclideanSpace 𝕜 ι) (i : ι) : (basisFun ι 𝕜).repr x i = x i := rfl

@[simp]
/-
**EuclideanSpace.basisFun_inner** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanSpace`。
形式化陈述：basisFun_inner (x : EuclideanSpace 𝕜 ι) (i : ι) : ⟪basisFun ι 𝕜 i, x⟫ = x 
i
参数：x : EuclideanSpace 𝕜 ι；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem basisFun_inner (x : EuclideanSpace 𝕜 ι) (i : ι) : ⟪basisFun ι 𝕜 i, x⟫ = x i := by
  simp [← OrthonormalBasis.repr_apply_apply]

@[simp]
/-
**EuclideanSpace.inner_basisFun_real** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanSpace`。
形式化陈述：inner_basisFun_real (x : EuclideanSpace Real ι) (i : ι) : inner Real x (ba
sisFun ι Real i) = x i
参数：x : EuclideanSpace Real ι；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `real_inner_comm`：real_inner_comm (x y : F) : ⟪y, x⟫_Real = ⟪x, y⟫_Real
· 使用定理 `EuclideanSpace.basisFun_inner`：basisFun_inner (x : EuclideanSpace 𝕜 ι) (
i : ι) : ⟪basisFun ι 𝕜 i, x⟫ = x i
-/
theorem inner_basisFun_real (x : EuclideanSpace ℝ ι) (i : ι) :
    inner ℝ x (basisFun ι ℝ i) = x i := by
  rw [real_inner_comm, basisFun_inner]
/-
**EuclideanSpace.basisFun_toBasis** 是 Mathlib 中的一个定理，位于命名空间 `EuclideanSpace`。
形式化陈述：basisFun_toBasis : (basisFun ι 𝕜).toBasis = PiLp.basisFun _ 𝕜 ι
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
-/
theorem basisFun_toBasis : (basisFun ι 𝕜).toBasis = PiLp.basisFun _ 𝕜 ι := rfl

end EuclideanSpace

/-
**OrthonormalBasis.instInhabited** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：OrthonormalBasis.instInhabited : Inhabited (OrthonormalBasis ι 𝕜 (Euclidea
nSpace 𝕜 ι))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
-/
instance OrthonormalBasis.instInhabited : Inhabited (OrthonormalBasis ι 𝕜 (EuclideanSpace 𝕜 ι)) :=
  ⟨EuclideanSpace.basisFun ι 𝕜⟩

namespace OrthonormalBasis

variable {E' : Type*} [Fintype ι'] [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E']
    (b : OrthonormalBasis ι 𝕜 E) (b' : OrthonormalBasis ι' 𝕜 E') (e : ι ≃ ι')

/-- The `LinearIsometryEquiv` which maps an orthonormal basis to another. This is a convenience
wrapper around `Orthonormal.equiv`. -/
/-
**OrthonormalBasis.equiv** 是 Mathlib 中的一个定义，位于命名空间 `OrthonormalBasis`。
形式化陈述：{ι : Type u_1} →   {ι' : Type u_2} →     {𝕜 : Type u_3} →       [inst : RC
Like 𝕜] →         {E : Type u_4} →           [inst_1 : NormedAddCommGroup E] →  
           [inst_2 : InnerProductSpace 𝕜 E] →               [inst_3 : Fintype ι]
 →                 {E' : Type u_7} →                   [inst_4 : Fintype ι'] →  
                   [inst_5 : NormedAddCommGroup E'] →                       [ins
t_6 : InnerProductSpace 𝕜 E'] →                         OrthonormalBasis ι 𝕜 E →
 OrthonormalBasis ι' 𝕜 E' → ι ≃ ι' → E ≃ₗᵢ[𝕜] E'
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)

--- 原说明 ---
The `LinearIsometryEquiv` which maps an orthonormal basis to another. This is a 
convenience
wrapper around `Orthonormal.equiv`.
-/
protected def equiv : E ≃ₗᵢ[𝕜] E' :=
  b.repr.trans <| .trans (.piLpCongrLeft _ _ _ e) b'.repr.symm

@[simp]
/-
**OrthonormalBasis.equiv_symm** 是 Mathlib 中的一个引理，位于命名空间 `OrthonormalBasis`。
形式化陈述：equiv_symm : (b.equiv b' e).symm = b'.equiv b e.symm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.ext_linearIsometryEquiv`：Module.Basis.ext_linearIsometryEqu
iv {ι : Type*} (b : Basis ι R E) {f₁ f₂ : E ≃ₛₗᵢ[σ₁₂] E₂} (h : forall i, f₁ (b i
) = f₂ (b i)) : f₁ = f₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearIsometryEquiv.trans.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} {E : Type u_5} {E₂ : Type u_6} {E₃ : Type u_7} [inst : Semiring R
]   [inst_1 : Semiring R₂]…
· 使用定理 `LinearIsometryEquiv.piLpCongrLeft_symm`：∀ {p : ENNReal} {𝕜 : Type u_1} {
ι : Type u_2} [hp : Fact (1 ≤ p)] [inst : Fintype ι] [inst_1 : Semiring 𝕜]   {ι'
 : Type u_5} [inst_2 : Finty…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma equiv_symm : (b.equiv b' e).symm = b'.equiv b e.symm := by
  apply b'.toBasis.ext_linearIsometryEquiv
  simp [OrthonormalBasis.equiv]

@[simp]
/-
**OrthonormalBasis.equiv_apply_basis** 是 Mathlib 中的一个引理，位于命名空间 `OrthonormalBasis
`。
形式化陈述：equiv_apply_basis (i : ι) : b.equiv b' e (b i) = b' (e i)
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrthonormalBasis.repr_self`：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : RCLi
ke 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpa
ce 𝕜 E] [inst_3 …
· 使用定理 `DFunLike.congr`：∀ {F : Sort u_1} {α : Sort u_2} {β : Sort u_3} [i : FunL
ike F α β] {f g : F} {x y : α}, f = g → x = y → f x = g y
· 使用定理 `PiLp.ext`：∀ {p : ENNReal} {ι : Type u_1} {α : ι → Type u_2} {x y : PiLp 
p α}, (∀ (i : ι), x.ofLp i = y.ofLp i) → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LinearIsometryEquiv.piLpCongrLeft_single`：∀ {p : ENNReal} {𝕜 : Type u_1}
 {ι : Type u_2} [hp : Fact (1 ≤ p)] [inst : Fintype ι] [inst_1 : Semiring 𝕜]   {
ι' : Type u_5} [inst_2 : Finty…
· 使用引理 `PiLp.single_apply`：single_apply [Zero 𝕜] (i : ι) (a : 𝕜) (j : ι) : (sing
le p i a : PiLp p (fun _ => 𝕜)) j = ite (j = i) a 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma equiv_apply_basis (i : ι) : b.equiv b' e (b i) = b' (e i) := by
  classical
  simp only [OrthonormalBasis.equiv, LinearIsometryEquiv.trans_apply, OrthonormalBasis.repr_self]
  refine DFunLike.congr rfl ?_
  ext j
  simp

@[simp]
/-
**OrthonormalBasis.equiv_self_rfl** 是 Mathlib 中的一个引理，位于命名空间 `OrthonormalBasis`。
形式化陈述：equiv_self_rfl : b.equiv b (.refl ι) = .refl 𝕜 E
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.ext_linearIsometryEquiv`：Module.Basis.ext_linearIsometryEqu
iv {ι : Type*} (b : Basis ι R E) {f₁ f₂ : E ≃ₛₗᵢ[σ₁₂] E₂} (h : forall i, f₁ (b i
) = f₂ (b i)) : f₁ = f₂
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `OrthonormalBasis.equiv_apply_basis`：equiv_apply_basis (i : ι) : b.equiv 
b' e (b i) = b' (e i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma equiv_self_rfl : b.equiv b (.refl ι) = .refl 𝕜 E := by
  apply b.toBasis.ext_linearIsometryEquiv
  simp

set_option backward.isDefEq.respectTransparency false in
/-
**OrthonormalBasis.equiv_apply** 是 Mathlib 中的一个引理，位于命名空间 `OrthonormalBasis`。
形式化陈述：equiv_apply (x : E) : b.equiv b' e x = ∑ i, b.repr x i • b' (e i)
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrthonormalBasis.sum_repr`：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : RCLik
e 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductSpac
e 𝕜 E] [inst_3 …
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `SemilinearIsometryEquivClass.toSemilinearIsometryClass`：∀ {R : Type u_1}
 {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} (𝓕 : Type u_10) [inst : Semiring
 R]   [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `OrthonormalBasis.equiv_apply_basis`：equiv_apply_basis (i : ι) : b.equiv 
b' e (b i) = b' (e i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma equiv_apply (x : E) : b.equiv b' e x = ∑ i, b.repr x i • b' (e i) := by
  nth_rw 1 [← b.sum_repr x, map_sum]
  simp_rw [map_smul, equiv_apply_basis]
/-
**OrthonormalBasis.equiv_apply_euclideanSpace** 是 Mathlib 中的一个引理，位于命名空间 `Orthono
rmalBasis`。
形式化陈述：equiv_apply_euclideanSpace (x : EuclideanSpace 𝕜 ι) : (EuclideanSpace.basi
sFun ι 𝕜).equiv b (Equiv.refl ι) x = ∑ i, x i • b i
参数：x : EuclideanSpace 𝕜 ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `OrthonormalBasis.equiv_apply`：equiv_apply (x : E) : b.equiv b' e x = ∑ i
, b.repr x i • b' (e i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma equiv_apply_euclideanSpace (x : EuclideanSpace 𝕜 ι) :
    (EuclideanSpace.basisFun ι 𝕜).equiv b (Equiv.refl ι) x = ∑ i, x i • b i := by
  simp_rw [equiv_apply, EuclideanSpace.basisFun_repr, Equiv.refl_apply]
/-
**OrthonormalBasis.coe_equiv_euclideanSpace** 是 Mathlib 中的一个引理，位于命名空间 `Orthonorm
alBasis`。
形式化陈述：coe_equiv_euclideanSpace : ⇑((EuclideanSpace.basisFun ι 𝕜).equiv b (Equiv.
refl ι)) = fun x => ∑ i, x i • b i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coe_equiv_euclideanSpace :
    ⇑((EuclideanSpace.basisFun ι 𝕜).equiv b (Equiv.refl ι)) = fun x ↦ ∑ i, x i • b i := by
  simp_rw [← equiv_apply_euclideanSpace]

end OrthonormalBasis

section Complex

/-- `![1, I]` is an orthonormal basis for `ℂ` considered as a real inner product space. -/
/-
**Complex.orthonormalBasisOneI** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Complex.orthonormalBasisOneI : OrthonormalBasis (Fin 2) Real Complex
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`![1, I]` is an orthonormal basis for `ℂ` considered as a real inner product spa
ce.
-/
def Complex.orthonormalBasisOneI : OrthonormalBasis (Fin 2) ℝ ℂ :=
  Complex.basisOneI.toOrthonormalBasis
    (by
      rw [orthonormal_iff_ite]
      intro i; fin_cases i <;> intro j <;> fin_cases j <;> simp [real_inner_eq_re_inner])

@[simp]
/-
**Complex.orthonormalBasisOneI_repr_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Complex.orthonormalBasisOneI_repr_apply (z : Complex) : Complex.orthonorma
lBasisOneI.repr z = ![z.re, z.im]
参数：z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
-/
theorem Complex.orthonormalBasisOneI_repr_apply (z : ℂ) :
    Complex.orthonormalBasisOneI.repr z = ![z.re, z.im] :=
  rfl

@[simp]
/-
**Complex.orthonormalBasisOneI_repr_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Complex.orthonormalBasisOneI_repr_symm_apply (x : EuclideanSpace Real (Fin
 2)) : Complex.orthonormalBasisOneI.repr.symm x = x 0 + x 1 * I
参数：x : EuclideanSpace Real (Fin 2)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
-/
theorem Complex.orthonormalBasisOneI_repr_symm_apply (x : EuclideanSpace ℝ (Fin 2)) :
    Complex.orthonormalBasisOneI.repr.symm x = x 0 + x 1 * I :=
  rfl

@[simp]
/-
**Complex.toBasis_orthonormalBasisOneI** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Complex.toBasis_orthonormalBasisOneI : Complex.orthonormalBasisOneI.toBasi
s = Complex.basisOneI
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.toBasis_toOrthonormalBasis`：∀ {ι : Type u_1} {𝕜 : Type u_3}
 [inst : RCLike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : In
nerProductSpace 𝕜 E] [inst_3 …
-/
theorem Complex.toBasis_orthonormalBasisOneI :
    Complex.orthonormalBasisOneI.toBasis = Complex.basisOneI :=
  Basis.toBasis_toOrthonormalBasis _ _

@[simp]
/-
**Complex.coe_orthonormalBasisOneI** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Complex.coe_orthonormalBasisOneI : (Complex.orthonormalBasisOneI : Fin 2 -
> Complex) = ![1, I]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.coe_toOrthonormalBasis`：∀ {ι : Type u_1} {𝕜 : Type u_3} [in
st : RCLike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerP
roductSpace 𝕜 E] [inst_3 …
· 使用定理 `Complex.coe_basisOneI`：coe_basisOneI : ⇑basisOneI = ![1, I]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Complex.coe_orthonormalBasisOneI :
    (Complex.orthonormalBasisOneI : Fin 2 → ℂ) = ![1, I] := by
  simp [Complex.orthonormalBasisOneI]

/-- The isometry between `ℂ` and a two-dimensional real inner product space given by a basis. -/
/-
**Complex.isometryOfOrthonormal** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Complex.isometryOfOrthonormal (v : OrthonormalBasis (Fin 2) Real F) : Comp
lex ≃ₗᵢ[Real] F
参数：v : OrthonormalBasis (Fin 2) Real F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)

--- 原说明 ---
The isometry between `ℂ` and a two-dimensional real inner product space given by
 a basis.
-/
def Complex.isometryOfOrthonormal (v : OrthonormalBasis (Fin 2) ℝ F) : ℂ ≃ₗᵢ[ℝ] F :=
  Complex.orthonormalBasisOneI.repr.trans v.repr.symm

@[simp]
/-
**Complex.map_isometryOfOrthonormal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Complex.map_isometryOfOrthonormal (v : OrthonormalBasis (Fin 2) Real F) (f
 : F ≃ₗᵢ[Real] F') : Complex.isometryOfOrthonormal (v.map f) = (Complex.isometry
OfOrthonormal v).trans f
参数：v : OrthonormalBasis (Fin 2) Real F；f : F ≃ₗᵢ[Real] F'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearIsometryEquiv.trans_assoc`：trans_assoc (eEE₂ : E ≃ₛₗᵢ[σ₁₂] E₂) (eE
₂E₃ : E₂ ≃ₛₗᵢ[σ₂₃] E₃) (eE₃E₄ : E₃ ≃ₛₗᵢ[σ₃₄] E₄) : eEE₂.trans (eE₂E₃.trans eE₃E₄
) = (eEE₂.trans eE₂E₃…
-/
theorem Complex.map_isometryOfOrthonormal (v : OrthonormalBasis (Fin 2) ℝ F) (f : F ≃ₗᵢ[ℝ] F') :
    Complex.isometryOfOrthonormal (v.map f) = (Complex.isometryOfOrthonormal v).trans f := by
  simp only [isometryOfOrthonormal, OrthonormalBasis.map, LinearIsometryEquiv.symm_trans,
    LinearIsometryEquiv.symm_symm]
  -- Porting note: `LinearIsometryEquiv.trans_assoc` doesn't trigger in the `simp` above
  rw [LinearIsometryEquiv.trans_assoc]
/-
**Complex.isometryOfOrthonormal_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Complex.isometryOfOrthonormal_symm_apply (v : OrthonormalBasis (Fin 2) Rea
l F) (f : F) : (Complex.isometryOfOrthonormal v).symm f = (v.toBasis.coord 0 f :
 Complex) + (v.toBasis.coord 1 f : Complex) * I
参数：v : OrthonormalBasis (Fin 2) Real F；f : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Module.Basis.coord_apply`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_
12} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] (b : Module.…
· 使用定理 `OrthonormalBasis.coe_toBasis_repr_apply`：∀ {ι : Type u_1} {𝕜 : Type u_3}
 [inst : RCLike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : In
nerProductSpace 𝕜 E] [inst_3 …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Complex.isometryOfOrthonormal_symm_apply (v : OrthonormalBasis (Fin 2) ℝ F) (f : F) :
    (Complex.isometryOfOrthonormal v).symm f =
      (v.toBasis.coord 0 f : ℂ) + (v.toBasis.coord 1 f : ℂ) * I := by
  simp [Complex.isometryOfOrthonormal]
/-
**Complex.isometryOfOrthonormal_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Complex.isometryOfOrthonormal_apply (v : OrthonormalBasis (Fin 2) Real F) 
(z : Complex) : Complex.isometryOfOrthonormal v z = z.re • v 0 + z.im • v 1
参数：v : OrthonormalBasis (Fin 2) Real F；z : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrthonormalBasis.sum_repr_symm`：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : 
RCLike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProduc
tSpace 𝕜 E] [inst_3 …
· 使用定理 `Fin.sum_univ_two`：∀ {M : Type u_2} [inst : AddCommMonoid M] (f : Fin 2 →
 M), ∑ i, f i = f 0 + f 1
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Complex.isometryOfOrthonormal_apply (v : OrthonormalBasis (Fin 2) ℝ F) (z : ℂ) :
    Complex.isometryOfOrthonormal v z = z.re • v 0 + z.im • v 1 := by
  simp [Complex.isometryOfOrthonormal, ← v.sum_repr_symm]

end Complex

open Module

/-! ### Matrix representation of an orthonormal basis with respect to another -/


section ToMatrix

variable [DecidableEq ι]

section
open scoped Matrix

/-- A version of `OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary` that works for bases with
different index types. -/
@[simp]
/-
**OrthonormalBasis.toMatrix_orthonormalBasis_conjTranspose_mul_self** 是 Mathlib 
中的一个定理，位于命名空间 ``。
形式化陈述：OrthonormalBasis.toMatrix_orthonormalBasis_conjTranspose_mul_self [Fintype
 ι'] (a : OrthonormalBasis ι' 𝕜 E) (b : OrthonormalBasis ι 𝕜 E) : (a.toBasis.toM
atrix b)ᴴ * a.toBasis.toMatrix b = 1
参数：a : OrthonormalBasis ι' 𝕜 E；b : OrthonormalBasis ι 𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `RCLike.inner_apply'`：RCLike.inner_apply' (x y : 𝕜) : ⟪x, y⟫ = conj x * y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `orthonormal_iff_ite`：orthonormal_iff_ite [DecidableEq ι] {v : ι -> E} : 
Orthonormal 𝕜 v ↔ forall i j, ⟪v i, v j⟫ = if i = j then (1 : 𝕜) else (0 : 𝕜)
· 使用定理 `OrthonormalBasis.orthonormal`：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : RC
Like 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductS
pace 𝕜 E] [inst_3 …
· 使用定理 `Matrix.one_apply`：one_apply {i j} : (1 : Matrix n n α) i j = if i = j th
en 1 else 0
· 使用定理 `LinearIsometryEquiv.inner_map_map`：LinearIsometryEquiv.inner_map_map (f 
: E ≃ₗᵢ[𝕜] E') (x y : E) : ⟪f x, f y⟫ = ⟪x, y⟫

--- 原说明 ---
A version of `OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary` that works
 for bases with
different index types.
-/
theorem OrthonormalBasis.toMatrix_orthonormalBasis_conjTranspose_mul_self [Fintype ι']
    (a : OrthonormalBasis ι' 𝕜 E) (b : OrthonormalBasis ι 𝕜 E) :
    (a.toBasis.toMatrix b)ᴴ * a.toBasis.toMatrix b = 1 := by
  ext i j
  convert! a.repr.inner_map_map (b i) (b j)
  · simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_def, PiLp.inner_apply,
      inner_apply']
    congr
  · rw [orthonormal_iff_ite.mp b.orthonormal i j, Matrix.one_apply]

/-- A version of `OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary` that works for bases with
different index types. -/
@[simp]
/-
**OrthonormalBasis.toMatrix_orthonormalBasis_self_mul_conjTranspose** 是 Mathlib 
中的一个定理，位于命名空间 ``。
形式化陈述：OrthonormalBasis.toMatrix_orthonormalBasis_self_mul_conjTranspose [Fintype
 ι'] (a : OrthonormalBasis ι 𝕜 E) (b : OrthonormalBasis ι' 𝕜 E) : a.toBasis.toMa
trix b * (a.toBasis.toMatrix b)ᴴ = 1
参数：a : OrthonormalBasis ι 𝕜 E；b : OrthonormalBasis ι' 𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.mul_eq_one_comm_of_equiv`：mul_eq_one_comm_of_equiv [IsStablyFinit
eRing R] {A : Matrix m n R} {B : Matrix n m R} (e : m ≃ n) : A * B = 1 ↔ B * A =
 1
· 使用定理 `instIsStablyFiniteRingOfOrzechProperty`：∀ {R : Type u_1} [inst : Semirin
g R] [OrzechProperty R], IsStablyFiniteRing R
· 使用定理 `CommRing.orzechProperty`：∀ (R : Type u_1) [inst : CommRing R], OrzechPro
perty R
· 使用定理 `invariantBasisNumber_of_nontrivial_of_commRing`：∀ {R : Type u} [inst : C
ommRing R] [Nontrivial R], InvariantBasisNumber R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `OrthonormalBasis.toMatrix_orthonormalBasis_conjTranspose_mul_self`：Ortho
normalBasis.toMatrix_orthonormalBasis_conjTranspose_mul_self [Fintype ι'] (a : O
rthonormalBasis ι' 𝕜 E) (b : OrthonormalBasis ι 𝕜 E) : …

--- 原说明 ---
A version of `OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary` that works
 for bases with
different index types.
-/
theorem OrthonormalBasis.toMatrix_orthonormalBasis_self_mul_conjTranspose [Fintype ι']
    (a : OrthonormalBasis ι 𝕜 E) (b : OrthonormalBasis ι' 𝕜 E) :
    a.toBasis.toMatrix b * (a.toBasis.toMatrix b)ᴴ = 1 := by
  classical
  rw [Matrix.mul_eq_one_comm_of_equiv (a.toBasis.indexEquiv b.toBasis),
    a.toMatrix_orthonormalBasis_conjTranspose_mul_self b]

variable (a b : OrthonormalBasis ι 𝕜 E)

/-- The change-of-basis matrix between two orthonormal bases `a`, `b` is a unitary matrix. -/
/-
**OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary : a.toBasis.toMatri
x b in Matrix.unitaryGroup ι 𝕜
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.mem_unitaryGroup_iff'`：mem_unitaryGroup_iff' : A in Matrix.unitar
yGroup n α ↔ star A * A = 1
· 使用定理 `OrthonormalBasis.toMatrix_orthonormalBasis_conjTranspose_mul_self`：Ortho
normalBasis.toMatrix_orthonormalBasis_conjTranspose_mul_self [Fintype ι'] (a : O
rthonormalBasis ι' 𝕜 E) (b : OrthonormalBasis ι 𝕜 E) : …

--- 原说明 ---
The change-of-basis matrix between two orthonormal bases `a`, `b` is a unitary m
atrix.
-/
theorem OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary :
    a.toBasis.toMatrix b ∈ Matrix.unitaryGroup ι 𝕜 := by
  rw [Matrix.mem_unitaryGroup_iff']
  exact a.toMatrix_orthonormalBasis_conjTranspose_mul_self b

/-- The determinant of the change-of-basis matrix between two orthonormal bases `a`, `b` has
unit length. -/
@[simp]
/-
**OrthonormalBasis.det_to_matrix_orthonormalBasis** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrthonormalBasis.det_to_matrix_orthonormalBasis : ‖a.toBasis.det b‖ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Matrix.det_of_mem_unitary`：det_of_mem_unitary {A : Matrix n n α} (hA : A
 in Matrix.unitaryGroup n α) : A.det in unitary α
· 使用定理 `OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary`：OrthonormalBasis
.toMatrix_orthonormalBasis_mem_unitary : a.toBasis.toMatrix b in Matrix.unitaryG
roup ι 𝕜
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_eq_one_iff_of_nonneg`：pow_eq_one_iff_of_nonneg (ha : 0 <= a) (hn : n
 != 0) : a ^ n = 1 ↔ a = 1
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `algebraMap.coe_one`：coe_one : (↑(1 : R) : A) = 1
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `RCLike.mul_conj`：mul_conj (z : K) : z * conj z = ‖z‖ ^ 2
· 使用定理 `RCLike.star_def`：star_def : (Star.star : K -> K) = conj

--- 原说明 ---
The determinant of the change-of-basis matrix between two orthonormal bases `a`,
 `b` has
unit length.
-/
theorem OrthonormalBasis.det_to_matrix_orthonormalBasis : ‖a.toBasis.det b‖ = 1 := by
  have := (Matrix.det_of_mem_unitary (a.toMatrix_orthonormalBasis_mem_unitary b)).2
  rw [star_def, RCLike.mul_conj] at this
  norm_cast at this
  rwa [pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero] at this

open OrthonormalBasis in
/-
**LinearIsometryEquiv.toMatrix_mem_unitaryGroup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIsometryEquiv.toMatrix_mem_unitaryGroup {G : Type*} [NormedAddCommGr
oup G] [InnerProductSpace 𝕜 G] (f : E ≃ₗᵢ[𝕜] G) (b : OrthonormalBasis ι 𝕜 E) (b'
 : OrthonormalBasis ι 𝕜 G) : f.toMatrix b.toBasis b'.toBasis in Matrix.unitaryGr
oup ι 𝕜
参数：f : E ≃ₗᵢ[𝕜] G；b : OrthonormalBasis ι 𝕜 E；b' : OrthonormalBasis ι 𝕜 G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.toMatrix_eq_basisToMatrix`：∀ {ι : Type u_1} {κ : Type u_3} {R 
: Type u_5} {M : Type u_6} [inst : CommSemiring R] [inst_1 : AddCommMonoid M]   
[inst_2 : _root_.Module R…
-/
theorem LinearIsometryEquiv.toMatrix_mem_unitaryGroup {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 G] (f : E ≃ₗᵢ[𝕜] G) (b : OrthonormalBasis ι 𝕜 E)
    (b' : OrthonormalBasis ι 𝕜 G) : f.toMatrix b.toBasis b'.toBasis ∈ Matrix.unitaryGroup ι 𝕜 := by
  simp [LinearMap.toMatrix_eq_basisToMatrix, ← coe_map, toMatrix_orthonormalBasis_mem_unitary]

end

section Real

variable (a b : OrthonormalBasis ι ℝ F)

/-- The change-of-basis matrix between two orthonormal bases `a`, `b` is an orthogonal matrix. -/
/-
**OrthonormalBasis.toMatrix_orthonormalBasis_mem_orthogonal** 是 Mathlib 中的一个定理，位
于命名空间 ``。
形式化陈述：OrthonormalBasis.toMatrix_orthonormalBasis_mem_orthogonal : a.toBasis.toMa
trix b in Matrix.orthogonalGroup ι Real
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary`：OrthonormalBasis
.toMatrix_orthonormalBasis_mem_unitary : a.toBasis.toMatrix b in Matrix.unitaryG
roup ι 𝕜

--- 原说明 ---
The change-of-basis matrix between two orthonormal bases `a`, `b` is an orthogon
al matrix.
-/
theorem OrthonormalBasis.toMatrix_orthonormalBasis_mem_orthogonal :
    a.toBasis.toMatrix b ∈ Matrix.orthogonalGroup ι ℝ :=
  a.toMatrix_orthonormalBasis_mem_unitary b

/-- The determinant of the change-of-basis matrix between two orthonormal bases `a`, `b` is ±1. -/
/-
**OrthonormalBasis.det_to_matrix_orthonormalBasis_real** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：OrthonormalBasis.det_to_matrix_orthonormalBasis_real : a.toBasis.det b = 1
 ∨ a.toBasis.det b = -1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sq_eq_one_iff`：∀ {R : Type u} [inst : Ring R] {a : R} [NoZeroDivisors R]
, a ^ 2 = 1 ↔ a = 1 ∨ a = -1
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `TrivialStar.star_trivial`：∀ {R : Type u} {inst : Star R} [self : Trivial
Star R] (r : R), star r = r
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Subsemigroup.mk.congr_simp`：∀ {M : Type u_3} [inst : Mul M] (carrier car
rier_1 : Set M) (e_carrier : carrier = carrier_1)   (mul_mem' : ∀ {a b : M}, a ∈
 carrier → b ∈ c…
· 使用定理 `Submonoid.mk.congr_simp`：∀ {M : Type u_3} [inst : MulOneClass M] (toSubs
emigroup toSubsemigroup_1 : Subsemigroup M)   (e_toSubsemigroup : toSubsemigroup
 = toSubsemig…
· 使用定理 `Matrix.det_of_mem_unitary`：det_of_mem_unitary {A : Matrix n n α} (hA : A
 in Matrix.unitaryGroup n α) : A.det in unitary α
· 使用定理 `OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary`：OrthonormalBasis
.toMatrix_orthonormalBasis_mem_unitary : a.toBasis.toMatrix b in Matrix.unitaryG
roup ι 𝕜

--- 原说明 ---
The determinant of the change-of-basis matrix between two orthonormal bases `a`,
 `b` is ±1.
-/
theorem OrthonormalBasis.det_to_matrix_orthonormalBasis_real :
    a.toBasis.det b = 1 ∨ a.toBasis.det b = -1 := by
  rw [← sq_eq_one_iff]
  simpa [unitary, sq] using! Matrix.det_of_mem_unitary (a.toMatrix_orthonormalBasis_mem_unitary b)

end Real

end ToMatrix

/-! ### Existence of orthonormal basis, etc. -/


section FiniteDimensional

variable {v : Set E}
variable {A : ι → Submodule 𝕜 E}

/-- Given an internal direct sum decomposition of a module `M`, and an orthonormal basis for each
of the components of the direct sum, the disjoint union of these orthonormal bases is an
orthonormal basis for `M`. -/
/-
**DirectSum.IsInternal.collectedOrthonormalBasis** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：DirectSum.IsInternal.collectedOrthonormalBasis (hV : OrthogonalFamily 𝕜 (f
un i => A i) fun i => (A i).subtypeₗᵢ) [DecidableEq ι] (hV_sum : DirectSum.IsInt
ernal fun i => A i) {α : ι -> Type*} [forall i, Fintype (α i)] (v_family : foral
l i, OrthonormalBasis (α i) 𝕜 (A i)) : OrthonormalBasis (Σ i, α i) 𝕜 E
参数：hV : OrthogonalFamily 𝕜 (fun i => A i) fun i => (A i).subtypeₗᵢ；hV_sum : Dire
ctSum.IsInternal fun i => A i；α i；v_family : forall i, OrthonormalBasis (α i) 𝕜 
(A i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an internal direct sum decomposition of a module `M`, and an orthonormal b
asis for each
of the components of the direct sum, the disjoint union of these orthonormal bas
es is an
orthonormal basis for `M`.
-/
noncomputable def DirectSum.IsInternal.collectedOrthonormalBasis
    (hV : OrthogonalFamily 𝕜 (fun i => A i) fun i => (A i).subtypeₗᵢ) [DecidableEq ι]
    (hV_sum : DirectSum.IsInternal fun i => A i) {α : ι → Type*} [∀ i, Fintype (α i)]
    (v_family : ∀ i, OrthonormalBasis (α i) 𝕜 (A i)) : OrthonormalBasis (Σ i, α i) 𝕜 E :=
  (hV_sum.collectedBasis fun i => (v_family i).toBasis).toOrthonormalBasis <| by
    simpa using
      hV.orthonormal_sigma_orthonormal (show ∀ i, Orthonormal 𝕜 (v_family i).toBasis by simp)
/-
**DirectSum.IsInternal.collectedOrthonormalBasis_mem** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：DirectSum.IsInternal.collectedOrthonormalBasis_mem [DecidableEq ι] (h : Di
rectSum.IsInternal A) {α : ι -> Type*} [forall i, Fintype (α i)] (hV : Orthogona
lFamily 𝕜 (fun i => A i) fun i => (A i).subtypeₗᵢ) (v : forall i, OrthonormalBas
is (α i) 𝕜 (A i)) (a : Σ i, α i) : h.collectedOrthonormalBasis hV v a in A a.1
参数：h : DirectSum.IsInternal A；α i；hV : OrthogonalFamily 𝕜 (fun i => A i) fun i =
> (A i).subtypeₗᵢ；v : forall i, OrthonormalBasis (α i) 𝕜 (A i)；a : Σ i, α i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Module.Basis.coe_toOrthonormalBasis`：∀ {ι : Type u_1} {𝕜 : Type u_3} [in
st : RCLike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerP
roductSpace 𝕜 E] [inst_3 …
· 使用定理 `DirectSum.IsInternal.collectedBasis_coe`：∀ {R : Type u} [inst : Semiring
 R] {ι : Type v} [dec_ι : DecidableEq ι] {M : Type u_1} [inst_1 : AddCommMonoid 
M]   [inst_2 : _root_.Module …
-/
theorem DirectSum.IsInternal.collectedOrthonormalBasis_mem [DecidableEq ι]
    (h : DirectSum.IsInternal A) {α : ι → Type*} [∀ i, Fintype (α i)]
    (hV : OrthogonalFamily 𝕜 (fun i => A i) fun i => (A i).subtypeₗᵢ)
    (v : ∀ i, OrthonormalBasis (α i) 𝕜 (A i)) (a : Σ i, α i) :
    h.collectedOrthonormalBasis hV v a ∈ A a.1 := by
  simp [DirectSum.IsInternal.collectedOrthonormalBasis]

variable [FiniteDimensional 𝕜 E]

/-- In a finite-dimensional `InnerProductSpace`, any orthonormal subset can be extended to an
orthonormal basis. -/
/-
**Orthonormal.exists_orthonormalBasis_extension** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Orthonormal.exists_orthonormalBasis_extension (hv : Orthonormal 𝕜 ((↑) : v
 -> E)) : exists (u : Finset E) (b : OrthonormalBasis u 𝕜 E), v subseteq u ∧ ⇑b 
= ((↑) : u -> E)
参数：hv : Orthonormal 𝕜 ((↑) : v -> E)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_maximal_orthonormal`：exists_maximal_orthonormal {s : Set E} (hs :
 Orthonormal 𝕜 (Subtype.val : s -> E)) : exists w ⊇ s, Orthonormal 𝕜 (Subtype.va
l : w -> E) ∧ fo…
· 使用定理 `LinearIndependent.setFinite`：setFinite [Module.Finite R M] {b : Set M} (
h : LinearIndependent R fun x : b => (x : M)) : b.Finite
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Orthonormal.linearIndependent`：Orthonormal.linearIndependent {v : ι -> E
} (hv : Orthonormal 𝕜 v) : LinearIndependent 𝕜 v
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Orthonormal.comp`：Orthonormal.comp {ι' : Type*} {v : ι -> E} (hv : Ortho
normal 𝕜 v) (f : ι' -> ι) (hf : Function.Injective f) : Orthonormal 𝕜 (v ∘ f)
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
· 使用定理 `maximal_orthonormal_iff_orthogonalComplement_eq_bot`：maximal_orthonormal
_iff_orthogonalComplement_eq_bot (hv : Orthonormal 𝕜 ((↑) : v -> E)) : (forall u
 ⊇ v, Orthonormal 𝕜 ((↑) : u -> E) -> u =…
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `OrthonormalBasis.coe_of_orthogonal_eq_bot_mk`：∀ {ι : Type u_1} {𝕜 : Type
 u_3} [inst : RCLike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2
 : InnerProductSpace 𝕜 E] [inst_3 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
In a finite-dimensional `InnerProductSpace`, any orthonormal subset can be exten
ded to an
orthonormal basis.
-/
theorem Orthonormal.exists_orthonormalBasis_extension (hv : Orthonormal 𝕜 ((↑) : v → E)) :
    ∃ (u : Finset E) (b : OrthonormalBasis u 𝕜 E), v ⊆ u ∧ ⇑b = ((↑) : u → E) := by
  obtain ⟨u₀, hu₀s, hu₀, hu₀_max⟩ := exists_maximal_orthonormal hv
  rw [maximal_orthonormal_iff_orthogonalComplement_eq_bot hu₀] at hu₀_max
  have hu₀_finite : u₀.Finite := hu₀.linearIndependent.setFinite
  let u : Finset E := hu₀_finite.toFinset
  let fu : ↥u ≃ ↥u₀ := hu₀_finite.subtypeEquivToFinset.symm
  have hu : Orthonormal 𝕜 ((↑) : u → E) := by simpa using! hu₀.comp _ fu.injective
  refine ⟨u, OrthonormalBasis.mkOfOrthogonalEqBot hu ?_, ?_, ?_⟩
  · simpa [u] using! hu₀_max
  · simpa [u] using! hu₀s
  · simp
/-
**Orthonormal.exists_orthonormalBasis_extension_of_card_eq** 是 Mathlib 中的一个定理，位于
命名空间 ``。
形式化陈述：Orthonormal.exists_orthonormalBasis_extension_of_card_eq {ι : Type*} [Fint
ype ι] (card_ι : finrank 𝕜 E = Fintype.card ι) {v : ι -> E} {s : Set ι} (hv : Or
thonormal 𝕜 (s.domRestrict v)) : exists b : OrthonormalBasis ι 𝕜 E, forall i in 
s, b i = v i
参数：card_ι : finrank 𝕜 E = Fintype.card ι；hv : Orthonormal 𝕜 (s.domRestrict v)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndependent.injective`：LinearIndependent.injective [Nontrivial R] 
(hv : LinearIndependent R v) : Injective v
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Orthonormal.linearIndependent`：Orthonormal.linearIndependent {v : ι -> E
} (hv : Orthonormal 𝕜 v) : LinearIndependent 𝕜 v
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `orthonormal_subtype_range`：orthonormal_subtype_range {v : ι -> E} (hv : 
Function.Injective v) : Orthonormal 𝕜 (Subtype.val : Set.range v -> E) ↔ Orthono
rmal 𝕜 v
· 使用定理 `Orthonormal.exists_orthonormalBasis_extension`：Orthonormal.exists_orthon
ormalBasis_extension (hv : Orthonormal 𝕜 ((↑) : v -> E)) : exists (u : Finset E)
 (b : OrthonormalBasis u 𝕜 E), v su…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.finrank_eq_card_finset_basis`：finrank_eq_card_finset_basis {ι : T
ype w} {b : Finset ι} (h : Basis b R M) : finrank R M = Finset.card b
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `Set.MapsTo.mono_right`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t₁ t
₂ : Set β} {f : α → β}, Set.MapsTo f s t₁ → t₁ ⊆ t₂ → Set.MapsTo f s t₂
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
· 使用定理 `Set.range_domRestrict`：range_domRestrict (f : α -> β) (s : Set α) : Set.
range (s.domRestrict f) = f '' s
· 使用定理 `Set.injOn_iff_injective`：injOn_iff_injective : InjOn f s ↔ Injective (s.
domRestrict f)
· 使用定理 `Set.MapsTo.exists_equiv_extend_of_card_eq`：Set.MapsTo.exists_equiv_exten
d_of_card_eq [Fintype α] {t : Finset β} (hαt : Fintype.card α = #t) {s : Set α} 
{f : α -> β} (hfst : s.MapsTo f…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `OrthonormalBasis.coe_reindex`：∀ {ι : Type u_1} {ι' : Type u_2} {𝕜 : Type
 u_3} [inst : RCLike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2
 : InnerProductSpa…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Orthonormal.exists_orthonormalBasis_extension_of_card_eq {ι : Type*} [Fintype ι]
    (card_ι : finrank 𝕜 E = Fintype.card ι) {v : ι → E} {s : Set ι}
    (hv : Orthonormal 𝕜 (s.domRestrict v)) :
    ∃ b : OrthonormalBasis ι 𝕜 E, ∀ i ∈ s, b i = v i := by
  have hsv : Injective (s.domRestrict v) := hv.linearIndependent.injective
  have hX : Orthonormal 𝕜 ((↑) : Set.range (s.domRestrict v) → E) := by
    rwa [orthonormal_subtype_range hsv]
  obtain ⟨Y, b₀, hX, hb₀⟩ := hX.exists_orthonormalBasis_extension
  have hιY : Fintype.card ι = Y.card := by
    refine card_ι.symm.trans ?_
    exact Module.finrank_eq_card_finset_basis b₀.toBasis
  have hvsY : s.MapsTo v Y := (s.mapsTo_image v).mono_right (by rwa [← range_domRestrict])
  have hsv' : Set.InjOn v s := by
    rw [Set.injOn_iff_injective]
    exact hsv
  obtain ⟨g, hg⟩ := hvsY.exists_equiv_extend_of_card_eq hιY hsv'
  use b₀.reindex g.symm
  intro i hi
  simp [hb₀, hg i hi]

variable (𝕜 E)

/-- A finite-dimensional inner product space admits an orthonormal basis. -/
/-
**_root_.exists_orthonormalBasis** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：_root_.exists_orthonormalBasis : exists (w : Finset E) (b : OrthonormalBas
is w 𝕜 E), ⇑b = ((↑) : w -> E)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A finite-dimensional inner product space admits an orthonormal basis.
-/
theorem _root_.exists_orthonormalBasis :
    ∃ (w : Finset E) (b : OrthonormalBasis w 𝕜 E), ⇑b = ((↑) : w → E) :=
  let ⟨w, hw, _, hw''⟩ := (orthonormal_empty 𝕜 E).exists_orthonormalBasis_extension
  ⟨w, hw, hw''⟩

/-- A finite-dimensional `InnerProductSpace` has an orthonormal basis. -/
irreducible_def stdOrthonormalBasis : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E := by
  let b := Classical.choose (Classical.choose_spec <| exists_orthonormalBasis 𝕜 E)
  rw [finrank_eq_card_basis b.toBasis]
  exact b.reindex (Fintype.equivFinOfCardEq rfl)

/-- An orthonormal basis of `ℝ` is made either of the vector `1`, or of the vector `-1`. -/
/-
**orthonormalBasis_one_dim** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：orthonormalBasis_one_dim (b : OrthonormalBasis ι Real Real) : (⇑b = fun _ 
=> (1 : Real)) ∨ ⇑b = fun _ => (-1 : Real)
参数：b : OrthonormalBasis ι Real Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `OrthonormalBasis.orthonormal`：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst : RC
Like 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerProductS
pace 𝕜 E] [inst_3 …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_eq`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOrder G
] [IsOrderedAddMonoid G] {a b : G},   0 ≤ b → (|a| = b ↔ a = b ∨ a = -b)
· 使用引理 `zero_le_one'`：zero_le_one' (α) [Zero α] [One α] [LE α] [ZeroLEOneClass α
] : (0 : α) <= 1
· 使用定理 `Real.norm_eq_abs`：norm_eq_abs (r : Real) : ‖r‖ = |r|
· 使用定理 `eq_const_of_unique`：eq_const_of_unique {β : Sort*} [Unique α] (f : α -> 
β) : f = Function.const α (f default)

--- 原说明 ---
An orthonormal basis of `ℝ` is made either of the vector `1`, or of the vector `
-1`.
-/
theorem orthonormalBasis_one_dim (b : OrthonormalBasis ι ℝ ℝ) :
    (⇑b = fun _ => (1 : ℝ)) ∨ ⇑b = fun _ => (-1 : ℝ) := by
  have : Unique ι := b.toBasis.unique
  have : b default = 1 ∨ b default = -1 := by
    have : ‖b default‖ = 1 := b.orthonormal.1 _
    rwa [Real.norm_eq_abs, abs_eq (zero_le_one' ℝ)] at this
  rw [eq_const_of_unique b]
  grind

variable {𝕜 E}

section SubordinateOrthonormalBasis

open DirectSum

variable {n : ℕ} (hn : finrank 𝕜 E = n) [DecidableEq ι] {V : ι → Submodule 𝕜 E} (hV : IsInternal V)

/-- Exhibit a bijection between `Fin n` and the index set of a certain basis of an `n`-dimensional
inner product space `E`.  This should not be accessed directly, but only via the subsequent API. -/
irreducible_def DirectSum.IsInternal.sigmaOrthonormalBasisIndexEquiv
    (hV' : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) :
    (Σ i, Fin (finrank 𝕜 (V i))) ≃ Fin n :=
  let b := hV.collectedOrthonormalBasis hV' fun i => stdOrthonormalBasis 𝕜 (V i)
  Fintype.equivFinOfCardEq <| (Module.finrank_eq_card_basis b.toBasis).symm.trans hn

/-- An `n`-dimensional `InnerProductSpace` equipped with a decomposition as an internal direct
sum has an orthonormal basis indexed by `Fin n` and subordinate to that direct sum. -/
irreducible_def DirectSum.IsInternal.subordinateOrthonormalBasis
    (hV' : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) :
    OrthonormalBasis (Fin n) 𝕜 E :=
  (hV.collectedOrthonormalBasis hV' fun i => stdOrthonormalBasis 𝕜 (V i)).reindex
    (hV.sigmaOrthonormalBasisIndexEquiv hn hV')

/-- An `n`-dimensional `InnerProductSpace` equipped with a decomposition as an internal direct
sum has an orthonormal basis indexed by `Fin n` and subordinate to that direct sum. This function
provides the mapping by which it is subordinate. -/
irreducible_def DirectSum.IsInternal.subordinateOrthonormalBasisIndex (a : Fin n)
    (hV' : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) : ι :=
  ((hV.sigmaOrthonormalBasisIndexEquiv hn hV').symm a).1

/-- The basis constructed in `DirectSum.IsInternal.subordinateOrthonormalBasis` is subordinate to
the `OrthogonalFamily` in question. -/
/-
**DirectSum.IsInternal.subordinateOrthonormalBasis_subordinate** 是 Mathlib 中的一个定
理，位于命名空间 ``。
形式化陈述：DirectSum.IsInternal.subordinateOrthonormalBasis_subordinate (a : Fin n) (
hV' : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) : hV.subordina
teOrthonormalBasis hn hV' a in V (hV.subordinateOrthonormalBasisIndex hn a hV')
参数：a : Fin n；hV' : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirectSum.IsInternal.subordinateOrthonormalBasisIndex_def`：∀ {ι : Type u
_7} {𝕜 : Type u_8} [inst : RCLike 𝕜] {E : Type u_9} [inst_1 : NormedAddCommGroup
 E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `DirectSum.IsInternal.subordinateOrthonormalBasis_def`：∀ {ι : Type u_7} {
𝕜 : Type u_8} [inst : RCLike 𝕜] {E : Type u_9} [inst_1 : NormedAddCommGroup E]  
 [inst_2 : InnerProductSpace 𝕜 E] [inst_3 …
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `OrthonormalBasis.coe_reindex`：∀ {ι : Type u_1} {ι' : Type u_2} {𝕜 : Type
 u_3} [inst : RCLike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2
 : InnerProductSpa…
· 使用定理 `DirectSum.IsInternal.collectedOrthonormalBasis_mem`：DirectSum.IsInternal
.collectedOrthonormalBasis_mem [DecidableEq ι] (h : DirectSum.IsInternal A) {α :
 ι -> Type*} [forall i, Fintype (α i)] (…

--- 原说明 ---
The basis constructed in `DirectSum.IsInternal.subordinateOrthonormalBasis` is s
ubordinate to
the `OrthogonalFamily` in question.
-/
theorem DirectSum.IsInternal.subordinateOrthonormalBasis_subordinate (a : Fin n)
    (hV' : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) :
    hV.subordinateOrthonormalBasis hn hV' a ∈ V (hV.subordinateOrthonormalBasisIndex hn a hV') := by
  simpa only [DirectSum.IsInternal.subordinateOrthonormalBasis, OrthonormalBasis.coe_reindex,
    DirectSum.IsInternal.subordinateOrthonormalBasisIndex] using!
    hV.collectedOrthonormalBasis_mem hV' (fun i => stdOrthonormalBasis 𝕜 (V i))
      ((hV.sigmaOrthonormalBasisIndexEquiv hn hV').symm a)
/-
**DirectSum.IsInternal.exists_subordinateOrthonormalBasisIndex_eq** 是 Mathlib 中的
一个定理，位于命名空间 ``。
形式化陈述：DirectSum.IsInternal.exists_subordinateOrthonormalBasisIndex_eq (hV' : Ort
hogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) {i : ι} (hi : V i != ⊥)
 : exists a : Fin n, hV.subordinateOrthonormalBasisIndex hn a hV' = i
参数：hV' : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ；hi : V i != 
⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `DirectSum.IsInternal.subordinateOrthonormalBasisIndex_def`：∀ {ι : Type u
_7} {𝕜 : Type u_8} [inst : RCLike 𝕜] {E : Type u_9} [inst_1 : NormedAddCommGroup
 E]   [inst_2 : InnerProductSpace 𝕜 E] [inst_3 …
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem DirectSum.IsInternal.exists_subordinateOrthonormalBasisIndex_eq
    (hV' : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) {i : ι} (hi : V i ≠ ⊥) :
    ∃ a : Fin n, hV.subordinateOrthonormalBasisIndex hn a hV' = i := by
  use hV.sigmaOrthonormalBasisIndexEquiv hn hV' ⟨i, ⟨0, by grind [finrank_eq_zero (S := V i)]⟩⟩
  simp [subordinateOrthonormalBasisIndex_def]
/-
**DirectSum.IsInternal.subordinateOrthonormalBasisIndexFiberEquiv** 是 Mathlib 中的
一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def DirectSum.IsInternal.subordinateOrthonormalBasisIndexFiberEquiv
    (hV' : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) (i : ι) :
    {a : Fin n // hV.subordinateOrthonormalBasisIndex hn a hV' = i} ≃ Fin (finrank 𝕜 (V i)) where
  toFun a := Fin.cast (by rw [← subordinateOrthonormalBasisIndex_def, a.property])
    ((hV.sigmaOrthonormalBasisIndexEquiv hn hV').symm a).snd
  invFun b := ⟨hV.sigmaOrthonormalBasisIndexEquiv hn hV' ⟨i, b⟩,
    by simp [subordinateOrthonormalBasisIndex_def]⟩
  left_inv := by grind [subordinateOrthonormalBasisIndex_def, Fin.cast_eq_self]
  right_inv := by grind
/-
**DirectSum.IsInternal.card_filter_subordinateOrthonormalBasisIndex_eq** 是 Mathl
ib 中的一个定理，位于命名空间 ``。
形式化陈述：DirectSum.IsInternal.card_filter_subordinateOrthonormalBasisIndex_eq (hV' 
: OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) (i : ι) : Finset.c
ard {a | hV.subordinateOrthonormalBasisIndex hn a hV' = i} = finrank 𝕜 (V i)
参数：hV' : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_eq_of_equiv_fin`：Finset.card_eq_of_equiv_fin {s : Finset α} 
{n : Nat} (i : s ≃ Fin n) : #s = n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem DirectSum.IsInternal.card_filter_subordinateOrthonormalBasisIndex_eq
    (hV' : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) (i : ι) :
    Finset.card {a | hV.subordinateOrthonormalBasisIndex hn a hV' = i} = finrank 𝕜 (V i) := by
  apply Finset.card_eq_of_equiv_fin
  simpa using hV.subordinateOrthonormalBasisIndexFiberEquiv hn hV' i

end SubordinateOrthonormalBasis

end FiniteDimensional

/-- Given a natural number `n` one less than the `finrank` of a finite-dimensional inner product
space, there exists an isometry from the orthogonal complement of a nonzero singleton to
`EuclideanSpace 𝕜 (Fin n)`. -/
/-
**OrthonormalBasis.fromOrthogonalSpanSingleton** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OrthonormalBasis.fromOrthogonalSpanSingleton (n : Nat) [Fact (finrank 𝕜 E 
= n + 1)] {v : E} (hv : v != 0) : OrthonormalBasis (Fin n) 𝕜 (𝕜 ∙ v)ᗮ
参数：n : Nat；finrank 𝕜 E = n + 1；hv : v != 0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.finrank_orthogonal_span_singleton`：finrank_orthogonal_span_sin
gleton {n : Nat} [_i : Fact (finrank 𝕜 E = n + 1)] {v : E} (hv : v != 0) : finra
nk 𝕜 (𝕜 ∙ v)ᗮ = n

--- 原说明 ---
Given a natural number `n` one less than the `finrank` of a finite-dimensional i
nner product
space, there exists an isometry from the orthogonal complement of a nonzero sing
leton to
`EuclideanSpace 𝕜 (Fin n)`.
-/
def OrthonormalBasis.fromOrthogonalSpanSingleton (n : ℕ) [Fact (finrank 𝕜 E = n + 1)] {v : E}
    (hv : v ≠ 0) : OrthonormalBasis (Fin n) 𝕜 (𝕜 ∙ v)ᗮ :=
  have : FiniteDimensional 𝕜 E := .of_fact_finrank_eq_succ (K := 𝕜) (V := E) n
  (stdOrthonormalBasis _ _).reindex <| finCongr <| finrank_orthogonal_span_singleton hv

section LinearIsometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
variable {S : Submodule 𝕜 V} {L : S →ₗᵢ[𝕜] V}

open Module

/-- Let `S` be a subspace of a finite-dimensional complex inner product space `V`.  A linear
isometry mapping `S` into `V` can be extended to a full isometry of `V`.

TODO:  The case when `S` is a finite-dimensional subspace of an infinite-dimensional `V`. -/
/-
**LinearIsometry.extend** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearIsometry.extend (L : S ->ₗᵢ[𝕜] V) : V ->ₗᵢ[𝕜] V
参数：L : S ->ₗᵢ[𝕜] V。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)

--- 原说明 ---
Let `S` be a subspace of a finite-dimensional complex inner product space `V`.  
A linear
isometry mapping `S` into `V` can be extended to a full isometry of `V`.

TODO:  The case when `S` is a finite-dimensional subspace of an infinite-dimensi
onal `V`.
-/
noncomputable def LinearIsometry.extend (L : S →ₗᵢ[𝕜] V) : V →ₗᵢ[𝕜] V := by
  -- Build an isometry from Sᗮ to L(S)ᗮ through `EuclideanSpace`
  let d := finrank 𝕜 Sᗮ
  let LS := LinearMap.range L.toLinearMap
  have E : Sᗮ ≃ₗᵢ[𝕜] LSᗮ := by
    have dim_LS_perp : finrank 𝕜 LSᗮ = d :=
      calc
        finrank 𝕜 LSᗮ = finrank 𝕜 V - finrank 𝕜 LS := by
          simp only [← LS.finrank_add_finrank_orthogonal, add_tsub_cancel_left]
        _ = finrank 𝕜 V - finrank 𝕜 S := by
          simp only [LS, LinearMap.finrank_range_of_inj L.injective]
        _ = finrank 𝕜 Sᗮ := by simp only [← S.finrank_add_finrank_orthogonal, add_tsub_cancel_left]
    exact
      (stdOrthonormalBasis 𝕜 Sᗮ).repr.trans
        ((stdOrthonormalBasis 𝕜 LSᗮ).reindex <| finCongr dim_LS_perp).repr.symm
  let L3 := LSᗮ.subtypeₗᵢ.comp E.toLinearIsometry
  -- Project onto S and Sᗮ
  haveI : CompleteSpace S := FiniteDimensional.complete 𝕜 S
  haveI : CompleteSpace V := FiniteDimensional.complete 𝕜 V
  let p1 := S.orthogonalProjectionOnto.toLinearMap
  let p2 := Sᗮ.orthogonalProjectionOnto.toLinearMap
  -- Build a linear map from the isometries on S and Sᗮ
  let M := L.toLinearMap.comp p1 + L3.toLinearMap.comp p2
  -- Prove that M is an isometry
  have M_norm_map : ∀ x : V, ‖M x‖ = ‖x‖ := by
    intro x
    -- Apply M to the orthogonal decomposition of x
    have Mx_decomp : M x = L (p1 x) + L3 (p2 x) := by
      simp only [M, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
        LinearIsometry.coe_toLinearMap]
    -- Mx_decomp is the orthogonal decomposition of M x
    have Mx_orth : ⟪L (p1 x), L3 (p2 x)⟫ = 0 := by
      have Lp1x : L (p1 x) ∈ LinearMap.range L.toLinearMap :=
        LinearMap.mem_range_self L.toLinearMap (p1 x)
      have Lp2x : L3 (p2 x) ∈ (LinearMap.range L.toLinearMap)ᗮ := by
        simp only [LS,
          ← Submodule.range_subtype LSᗮ]
        apply LinearMap.mem_range_self
      apply Submodule.inner_right_of_mem_orthogonal Lp1x Lp2x
    -- Apply the Pythagorean theorem and simplify
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_eq_add_norm_sq_projection x S]
    simp only [sq, Mx_decomp]
    rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (L (p1 x)) (L3 (p2 x)) Mx_orth]
    simp only [p1, p2, LinearIsometry.norm_map,
      ContinuousLinearMap.coe_coe, Submodule.coe_norm]
  exact
    { toLinearMap := M
      norm_map' := M_norm_map }
/-
**LinearIsometry.extend_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIsometry.extend_apply (L : S ->ₗᵢ[𝕜] V) (s : S) : L.extend s = L s
参数：L : S ->ₗᵢ[𝕜] V；s : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.orthogonalProjectionOnto_mem_subspace_eq_self`：orthogonalProje
ctionOnto_mem_subspace_eq_self (v : K) : K.orthogonalProjectionOnto v = v
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearIsometryClass.toSemilinearMapClass`：∀ {𝓕 : Type u_11} {R : out
Param (Type u_12)} {R₂ : outParam (Type u_13)} {inst : Semiring R} {inst_1 : Sem
iring R₂}   {σ₁₂ : outParam (R →+*…
· 使用定理 `SemilinearIsometryEquivClass.toSemilinearIsometryClass`：∀ {R : Type u_1}
 {R₂ : Type u_2} {E : Type u_5} {E₂ : Type u_6} (𝓕 : Type u_10) [inst : Semiring
 R]   [inst_1 : Semiring R₂] {σ₁₂ : R →+* R₂…
· 使用定理 `Submodule.orthogonal_orthogonal`：orthogonal_orthogonal [K.HasOrthogonalP
rojection] : Kᗮᗮ = K
· 使用定理 `Submodule.HasOrthogonalProjection.ofCompleteSpace`：∀ {𝕜 : Type u_1} {E :
 Type u_2} [inst : RCLike 𝕜] [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (K : Submodule 𝕜 E) [Co…
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `FiniteDimensional.RCLike.properSpace_submodule`：∀ (K : Type u_1) {E : Ty
pe u_2} [inst : RCLike K] [inst_1 : NormedAddCommGroup E] [inst_2 : NormedSpace 
K E]   (S : Submodule K E) [FiniteDi…
-/
theorem LinearIsometry.extend_apply (L : S →ₗᵢ[𝕜] V) (s : S) : L.extend s = L s := by
  simp only [LinearIsometry.extend, ← LinearIsometry.coe_toLinearMap]
  simp

end LinearIsometry

section Matrix

open Matrix

variable {m n : Type*}

namespace Matrix

variable [Fintype n] [DecidableEq n]

/-- A shorthand for `Matrix.toLpLin 2 2`. -/
/-
**Matrix.toEuclideanLin** 是 Mathlib 中的一个缩写定义，位于命名空间 `Matrix`。
形式化陈述：toEuclideanLin : Matrix m n 𝕜 ≃ₗ[𝕜] EuclideanSpace 𝕜 n ->ₗ[𝕜] EuclideanSpa
ce 𝕜 m
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A shorthand for `Matrix.toLpLin 2 2`.
-/
abbrev toEuclideanLin : Matrix m n 𝕜 ≃ₗ[𝕜] EuclideanSpace 𝕜 n →ₗ[𝕜] EuclideanSpace 𝕜 m :=
  toLpLin 2 2

@[deprecated toLpLin_toLp (since := "2026-01-22")]
/-
**Matrix.toEuclideanLin_toLp** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：toEuclideanLin_toLp (A : Matrix m n 𝕜) (x : n -> 𝕜) : Matrix.toEuclideanLi
n A (toLp _ x) = toLp _ (Matrix.toLin' A x)
参数：A : Matrix m n 𝕜；x : n -> 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
lemma toEuclideanLin_toLp (A : Matrix m n 𝕜) (x : n → 𝕜) :
    Matrix.toEuclideanLin A (toLp _ x) = toLp _ (Matrix.toLin' A x) := rfl

@[deprecated ofLp_toLpLin (since := "2026-01-22")]
/-
**Matrix.piLp_ofLp_toEuclideanLin** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：piLp_ofLp_toEuclideanLin (A : Matrix m n 𝕜) (x : EuclideanSpace 𝕜 n) : ofL
p (Matrix.toEuclideanLin A x) = Matrix.toLin' A (ofLp x)
参数：A : Matrix m n 𝕜；x : EuclideanSpace 𝕜 n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem piLp_ofLp_toEuclideanLin (A : Matrix m n 𝕜) (x : EuclideanSpace 𝕜 n) :
    ofLp (Matrix.toEuclideanLin A x) = Matrix.toLin' A (ofLp x) :=
  rfl

@[deprecated toLpLin_apply (since := "2026-01-22")]
/-
**Matrix.toEuclideanLin_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：toEuclideanLin_apply (M : Matrix m n 𝕜) (v : EuclideanSpace 𝕜 n) : toEucli
deanLin M v = toLp _ (M *ᵥ ofLp v)
参数：M : Matrix m n 𝕜；v : EuclideanSpace 𝕜 n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem toEuclideanLin_apply (M : Matrix m n 𝕜) (v : EuclideanSpace 𝕜 n) :
    toEuclideanLin M v = toLp _ (M *ᵥ ofLp v) := rfl

@[deprecated ofLp_toLpLin (since := "2026-01-22")]
/-
**Matrix.ofLp_toEuclideanLin_apply** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：ofLp_toEuclideanLin_apply (M : Matrix m n 𝕜) (v : EuclideanSpace 𝕜 n) : of
Lp (toEuclideanLin M v) = M *ᵥ ofLp v
参数：M : Matrix m n 𝕜；v : EuclideanSpace 𝕜 n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem ofLp_toEuclideanLin_apply (M : Matrix m n 𝕜) (v : EuclideanSpace 𝕜 n) :
    ofLp (toEuclideanLin M v) = M *ᵥ ofLp v :=
  rfl

@[deprecated toLpLin_toLp (since := "2026-01-22")]
/-
**Matrix.toEuclideanLin_apply_piLp_toLp** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：toEuclideanLin_apply_piLp_toLp (M : Matrix m n 𝕜) (v : n -> 𝕜) : toEuclide
anLin M (toLp _ v) = toLp _ (M *ᵥ v)
参数：M : Matrix m n 𝕜；v : n -> 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem toEuclideanLin_apply_piLp_toLp (M : Matrix m n 𝕜) (v : n → 𝕜) :
    toEuclideanLin M (toLp _ v) = toLp _ (M *ᵥ v) :=
  rfl

-- `Matrix.toEuclideanLin` is the same as `Matrix.toLin` applied to `PiLp.basisFun`,
@[deprecated toLpLin_eq_toLin (since := "2026-01-22")]
/-
**Matrix.toEuclideanLin_eq_toLin** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：toEuclideanLin_eq_toLin [Finite m] : (toEuclideanLin : Matrix m n 𝕜 ≃ₗ[𝕜] 
_) = Matrix.toLin (PiLp.basisFun _ _ _) (PiLp.basisFun _ _ _)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem toEuclideanLin_eq_toLin [Finite m] :
    (toEuclideanLin : Matrix m n 𝕜 ≃ₗ[𝕜] _) =
      Matrix.toLin (PiLp.basisFun _ _ _) (PiLp.basisFun _ _ _) :=
  rfl

open EuclideanSpace in
/-
**Matrix.toEuclideanLin_eq_toLin_orthonormal** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：toEuclideanLin_eq_toLin_orthonormal [Fintype m] : toEuclideanLin = toLin (
basisFun n 𝕜).toBasis (basisFun m 𝕜).toBasis
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
lemma toEuclideanLin_eq_toLin_orthonormal [Fintype m] :
    toEuclideanLin = toLin (basisFun n 𝕜).toBasis (basisFun m 𝕜).toBasis :=
  rfl

end Matrix

local notation "⟪" x ", " y "⟫ₑ" => inner 𝕜 (toLp 2 x) (toLp 2 y)

/-- The inner product of a row of `A` and a row of `B` is an entry of `B * Aᴴ`. -/
/-
**inner_matrix_row_row** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_matrix_row_row [Fintype n] (A B : Matrix m n 𝕜) (i j : m) : ⟪A i, B 
j⟫ₑ = (B * Aᴴ) j i
参数：A B : Matrix m n 𝕜；i j : m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The inner product of a row of `A` and a row of `B` is an entry of `B * Aᴴ`.
-/
theorem inner_matrix_row_row [Fintype n] (A B : Matrix m n 𝕜) (i j : m) :
    ⟪A i, B j⟫ₑ = (B * Aᴴ) j i := by
  simp [PiLp.inner_apply, dotProduct, mul_apply']

/-- The inner product of a column of `A` and a column of `B` is an entry of `Aᴴ * B`. -/
/-
**inner_matrix_col_col** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inner_matrix_col_col [Fintype m] (A B : Matrix m n 𝕜) (i j : n) : ⟪Aᵀ i, B
ᵀ j⟫ₑ = (Aᴴ * B) i j
参数：A B : Matrix m n 𝕜；i j : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The inner product of a column of `A` and a column of `B` is an entry of `Aᴴ * B`
.
-/
theorem inner_matrix_col_col [Fintype m] (A B : Matrix m n 𝕜) (i j : n) :
    ⟪Aᵀ i, Bᵀ j⟫ₑ = (Aᴴ * B) i j := by
  simp [PiLp.inner_apply, dotProduct, mul_apply', mul_comm]

/-- The matrix representation of `innerSL 𝕜 x` given by an orthonormal basis `b` and `b₂`
is equal to `vecMulVec (star b₂) (star (b.repr x))`. -/
/-
**LinearMap.toMatrix_inner** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The matrix representation of `innerSL 𝕜 x` given by an orthonormal basis `b` and
 `b₂`
is equal to `vecMulVec (star b₂) (star (b.repr x))`.
-/
theorem LinearMap.toMatrix_innerₛₗ_apply [Fintype n] [DecidableEq n] [Fintype m]
    (b : OrthonormalBasis n 𝕜 E) (b₂ : OrthonormalBasis m 𝕜 𝕜) (x : E) :
    (innerₛₗ 𝕜 x).toMatrix b.toBasis b₂.toBasis = vecMulVec (star b₂) (star (b.repr x)) := by
  ext; simp [LinearMap.toMatrix_apply, vecMulVec_apply, OrthonormalBasis.repr_apply_apply, mul_comm]

@[deprecated (since := "2026-01-03")] alias toMatrix_innerSL_apply :=
  LinearMap.toMatrix_innerₛₗ_apply

end Matrix

open ContinuousLinearMap LinearMap in
/-
**InnerProductSpace.toMatrix_rankOne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：InnerProductSpace.toMatrix_rankOne {𝕜 E F ι ι' : Type*} [RCLike 𝕜] [Semino
rmedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 
𝕜 F] [Finite ι] [Fintype ι'] [DecidableEq ι'] (x : E) (y : F) (b : Module.Basis 
ι 𝕜 E) (b' : OrthonormalBasis ι' 𝕜 F) : (rankOne 𝕜 x y).toMatrix b'.toBasis b = 
.vecMulVec (b.repr x) (star (b'.repr y))
参数：x : E；y : F；b : Module.Basis ι 𝕜 E；b' : OrthonormalBasis ι' 𝕜 F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `InnerProductSpace.rankOne_def'`：rankOne_def' (x : E) (y : F) : rankOne 𝕜
 x y = .toSpanSingleton 𝕜 x ∘L innerSL 𝕜 y
· 使用定理 `ContinuousLinearMap.toLinearMap_comp`：toLinearMap_comp (h : M₂ ->SL[σ₂₃]
 M₃) (f : M₁ ->SL[σ₁₂] M₂) : (h ∘SL f : M₁ ->ₛₗ[σ₁₃] M₃) = (h : M₂ ->ₛₗ[σ₂₃] M₃)
 ∘ₛₗ (f : M₁ ->ₛₗ[σ₁₂] M₂)
· 使用定理 `ContinuousLinearMap.toLinearMap_toSpanSingleton`：toLinearMap_toSpanSingl
eton (x : M₁) : (toSpanSingleton R₁ x).toLinearMap = LinearMap.toSpanSingleton R
₁ M₁ x
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LinearMap.toMatrix_comp`：LinearMap.toMatrix_comp [Finite l] [DecidableEq
 m] (f : M₂ ->ₗ[R] M₃) (g : M₁ ->ₗ[R] M₂) : LinearMap.toMatrix v₁ v₃ (f.comp g) 
= LinearMap.t…
· 使用定理 `LinearMap.toMatrix_toSpanSingleton`：LinearMap.toMatrix_toSpanSingleton [
Finite m] (v₁ : Basis n R R) (v₂ : Basis m R M₂) (x : M₂) : (toSpanSingleton R M
₂ x).toMatrix v₁ v₂ = ve…
· 使用定理 `ContinuousLinearMap.toLinearMap_innerSL_apply`：∀ (𝕜 : Type u_1) {E : Typ
e u_2} [inst : RCLike 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : InnerProd
uctSpace 𝕜 E]   (v : E), ↑((innerSL…
· 使用定理 `LinearMap.toMatrix_innerₛₗ_apply`：LinearMap.toMatrix_innerₛₗ_apply [Fint
ype n] [DecidableEq n] [Fintype m] (b : OrthonormalBasis n 𝕜 E) (b₂ : Orthonorma
lBasis m 𝕜 𝕜) (x : E) …
· 使用定理 `OrthonormalBasis.toBasis_singleton`：toBasis_singleton : (OrthonormalBasi
s.singleton ι 𝕜).toBasis = Basis.singleton ι 𝕜
· 使用定理 `Module.Basis.coe_singleton`：coe_singleton {ι R : Type*} [Unique ι] [Semi
ring R] : ⇑(Basis.singleton ι R) = 1
· 使用定理 `Matrix.vecMulVec_one`：vecMulVec_one [MulOneClass R] (x : n -> R) : vecMu
lVec x 1 = replicateCol m x
· 使用定理 `OrthonormalBasis.coe_singleton`：coe_singleton : ⇑(OrthonormalBasis.singl
eton ι 𝕜) = 1
· 使用定理 `star_one`：star_one [MulOneClass R] [StarMul R] : star (1 : R) = 1
· 使用定理 `Matrix.one_vecMulVec`：one_vecMulVec [MulOneClass R] (x : n -> R) : vecMu
lVec 1 x = replicateRow m x
· 使用定理 `Matrix.vecMulVec_eq`：vecMulVec_eq [Mul α] [AddCommMonoid α] [Unique ι] (
w : m -> α) (v : n -> α) : vecMulVec w v = replicateCol ι w * replicateRow ι v
-/
theorem InnerProductSpace.toMatrix_rankOne {𝕜 E F ι ι' : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [Finite ι] [Fintype ι'] [DecidableEq ι'] (x : E) (y : F) (b : Module.Basis ι 𝕜 E)
    (b' : OrthonormalBasis ι' 𝕜 F) :
    (rankOne 𝕜 x y).toMatrix b'.toBasis b = .vecMulVec (b.repr x) (star (b'.repr y)) := by
  have := Fintype.ofFinite ι
  rw [rankOne_def', ContinuousLinearMap.toLinearMap_comp, toLinearMap_toSpanSingleton,
    toMatrix_comp _ (OrthonormalBasis.singleton Unit 𝕜).toBasis, toMatrix_toSpanSingleton,
    toLinearMap_innerSL_apply, toMatrix_innerₛₗ_apply, OrthonormalBasis.toBasis_singleton,
    Basis.coe_singleton, Matrix.vecMulVec_one, OrthonormalBasis.coe_singleton, star_one,
    Matrix.one_vecMulVec, Matrix.vecMulVec_eq Unit]

set_option backward.isDefEq.respectTransparency false in
open Matrix LinearMap EuclideanSpace in
/-
**InnerProductSpace.symm_toEuclideanLin_rankOne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：InnerProductSpace.symm_toEuclideanLin_rankOne {𝕜 m n : Type*} [RCLike 𝕜] [
Fintype m] [Fintype n] [DecidableEq n] (x : EuclideanSpace 𝕜 m) (y : EuclideanSp
ace 𝕜 n) : toEuclideanLin.symm (rankOne 𝕜 x y) = .vecMulVec x (star y)
参数：x : EuclideanSpace 𝕜 m；y : EuclideanSpace 𝕜 n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.toLpLin.eq_1`：∀ {m : Type u_1} {n : Type u_2} {R : Type u_4} [ins
t : Fintype n] [inst_1 : DecidableEq n] [inst_2 : CommRing R]   (p q : ENNReal),
   Matrix…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `WithLp.linearEquiv_symm_apply`：∀ (p : ENNReal) (K : Type u_1) (V : Type 
u_4) [inst : Semiring K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V] 
  (a : V), (WithLp.…
· 使用定理 `WithLp.addEquiv_symm_apply`：∀ (p : ENNReal) (V : Type u_4) [inst : AddCo
mmGroup V] (ofLp : V), (WithLp.addEquiv p V).symm ofLp = WithLp.toLp p ofLp
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `EuclideanSpace.inner_single_right`：EuclideanSpace.inner_single_right (i 
: ι) (a : 𝕜) (v : EuclideanSpace 𝕜 ι) : ⟪v, EuclideanSpace.single i (a : 𝕜)⟫ = a
 * conj (v i)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
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
· 使用定理 `WithLp.linearEquiv_apply`：∀ (p : ENNReal) (K : Type u_1) (V : Type u_4) 
[inst : Semiring K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]   (a 
: WithLp p V),…
· 使用定理 `WithLp.addEquiv_apply`：∀ (p : ENNReal) (V : Type u_4) [inst : AddCommGro
up V] (self : WithLp p V), (WithLp.addEquiv p V) self = self.ofLp
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem InnerProductSpace.symm_toEuclideanLin_rankOne {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m]
    [Fintype n] [DecidableEq n] (x : EuclideanSpace 𝕜 m) (y : EuclideanSpace 𝕜 n) :
    toEuclideanLin.symm (rankOne 𝕜 x y) = .vecMulVec x (star y) := by
  simp [toLpLin, toMatrix', ← Matrix.ext_iff, vecMulVec_apply, inner_single_right, mul_comm]

namespace FiniteDimensional
variable [Unique ι] (h : Module.finrank 𝕜 E = 1) {v : E} (hv : ‖v‖ = 1)

variable (ι 𝕜 v) in
/-- In an inner product space with dimension 1, a set `{v}` is an orthonormal basis for
`‖v‖ = 1`. -/
/-
**FiniteDimensional.orthonormalBasisSingleton** 是 Mathlib 中的一个定义，位于命名空间 `FiniteD
imensional`。
形式化陈述：orthonormalBasisSingleton : OrthonormalBasis ι 𝕜 E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In an inner product space with dimension 1, a set `{v}` is an orthonormal basis 
for
`‖v‖ = 1`.
-/
def orthonormalBasisSingleton : OrthonormalBasis ι 𝕜 E :=
  (basisSingleton ι h v (by aesop)).toOrthonormalBasis (by simpa)

@[simp]
/-
**FiniteDimensional.orthonormalBasisSingleton_apply** 是 Mathlib 中的一个定理，位于命名空间 `F
initeDimensional`。
形式化陈述：orthonormalBasisSingleton_apply (i : ι) : orthonormalBasisSingleton ι 𝕜 h 
v hv i = v
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Module.Basis.coe_toOrthonormalBasis`：∀ {ι : Type u_1} {𝕜 : Type u_3} [in
st : RCLike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerP
roductSpace 𝕜 E] [inst_3 …
· 使用定理 `FiniteDimensional.basisSingleton_apply`：basisSingleton_apply (ι : Type*)
 [Unique ι] (h : finrank K V = 1) (v : V) (hv : v != 0) (i : ι) : basisSingleton
 ι h v hv i = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem orthonormalBasisSingleton_apply (i : ι) :
    orthonormalBasisSingleton ι 𝕜 h v hv i = v := by
  simp [orthonormalBasisSingleton]

@[simp]
/-
**FiniteDimensional.toBasis_orthonormalBasisSingleton** 是 Mathlib 中的一个定理，位于命名空间 
`FiniteDimensional`。
形式化陈述：toBasis_orthonormalBasisSingleton : (orthonormalBasisSingleton ι 𝕜 h v hv)
.toBasis = basisSingleton ι h v (by aesop)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.toBasis_toOrthonormalBasis`：∀ {ι : Type u_1} {𝕜 : Type u_3}
 [inst : RCLike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : In
nerProductSpace 𝕜 E] [inst_3 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toBasis_orthonormalBasisSingleton :
    (orthonormalBasisSingleton ι 𝕜 h v hv).toBasis = basisSingleton ι h v (by aesop) := by
  simp [orthonormalBasisSingleton]

@[simp]
/-
**FiniteDimensional.orthonormalBasisSingleton_repr_apply** 是 Mathlib 中的一个定理，位于命名
空间 `FiniteDimensional`。
形式化陈述：orthonormalBasisSingleton_repr_apply (w : E) : (orthonormalBasisSingleton 
ι 𝕜 h v hv).repr w = .single default ⟪v, w⟫
参数：w : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PiLp.ext`：∀ {p : ENNReal} {ι : Type u_1} {α : ι → Type u_2} {x y : PiLp 
p α}, (∀ (i : ι), x.ofLp i = y.ofLp i) → x = y
· 使用定理 `fact_one_le_two_ennreal`：Fact (1 ≤ 2)
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Unique.eq_default`：eq_default (a : α) : a = default
· 使用定理 `OrthonormalBasis.repr_apply_apply`：∀ {ι : Type u_1} {𝕜 : Type u_3} [inst
 : RCLike 𝕜] {E : Type u_4} [inst_1 : NormedAddCommGroup E]   [inst_2 : InnerPro
ductSpace 𝕜 E] [inst_3 …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FiniteDimensional.orthonormalBasisSingleton_apply`：orthonormalBasisSingl
eton_apply (i : ι) : orthonormalBasisSingleton ι 𝕜 h v hv i = v
· 使用引理 `PiLp.single_eq_same`：single_eq_same (i : ι) (a : β i) : single p i a i =
 a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem orthonormalBasisSingleton_repr_apply (w : E) :
    (orthonormalBasisSingleton ι 𝕜 h v hv).repr w = .single default ⟪v, w⟫ := by
  ext
  simp [OrthonormalBasis.repr_apply_apply, Unique.eq_default]
/-
**FiniteDimensional.range_orthonormalBasisSingleton** 是 Mathlib 中的一个定理，位于命名空间 `F
initeDimensional`。
形式化陈述：range_orthonormalBasisSingleton : Set.range (orthonormalBasisSingleton ι 𝕜
 h v hv) = {v}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FiniteDimensional.orthonormalBasisSingleton_apply`：orthonormalBasisSingl
eton_apply (i : ι) : orthonormalBasisSingleton ι 𝕜 h v hv i = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem range_orthonormalBasisSingleton :
    Set.range (orthonormalBasisSingleton ι 𝕜 h v hv) = {v} := by
  simp

end FiniteDimensional

