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
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace Real F]
variable {F' : Type*} [NormedAddCommGroup F'] [InnerProductSpace Real F']

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/--
Instance `PiLp.innerProductSpace` / 实例 `PiLp.innerProductSpace`

English:
instance PiLp.innerProductSpace
  signature: {ι : Type*} [Fintype ι] (f : ι -> Type*)
  body: ∑ i, ⟪x i, y i⟫
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

中文:
实例 PiLp.innerProductSpace
  签名: {ι : 类型} [有限类型 ι] (f : ι -> 类型)
  定义体: ∑ i, ⟪x i, y i⟫
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
-/
instance PiLp.innerProductSpace {ι : Type*} [Fintype ι] (f : ι -> Type*)
    [forall i, NormedAddCommGroup (f i)] [forall i, InnerProductSpace 𝕜 (f i)] :
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

/--
theorem `PiLp.inner_apply` / 定理 `PiLp.inner_apply`

English:
theorem PiLp.inner_apply
  statement: {ι : Type*} [Fintype ι] {f : ι -> Type*} [forall i, NormedAddCommGroup (f i)]
  proof: rfl

中文:
定理 PiLp.inner_apply
  结论: {ι : 类型} [有限类型 ι] {f : ι -> 类型} [对任意 i, 赋范交换加群 (f i)]
  证明: rfl
-/
theorem PiLp.inner_apply {ι : Type*} [Fintype ι] {f : ι -> Type*} [forall i, NormedAddCommGroup (f i)]
    [forall i, InnerProductSpace 𝕜 (f i)] (x y : PiLp 2 f) : ⟪x, y⟫ = ∑ i, ⟪x i, y i⟫ :=
  rfl

/-- The standard real/complex Euclidean space, functions on a finite type. For an `n`-dimensional
space use `EuclideanSpace 𝕜 (Fin n)`.

For the case when `n = Fin _`, there is `!₂[x, y, ...]` notation for building elements of this type,
analogous to `![x, y, ...]` notation. -/
@[wikidata Q17295]
/--
Definition of `EuclideanSpace` / `EuclideanSpace` 的定义

English:
abbreviation EuclideanSpace
  signature: (𝕜 : Type*) (n : Type*)
  body: PiLp 2 fun _ : n => 𝕜

中文:
缩写 EuclideanSpace
  签名: (𝕜 : 类型) (n : 类型)
  定义体: PiLp 2 fun _ : n => 𝕜
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
  `(WithLp.toLp $p (V := forall _ : Fin $(quote n), _) ![$e,*])

/-- Unexpander for the `!₂[x, y, ...]` notation. -/
@[app_delab WithLp.toLp]
meta def EuclideanSpace.delabVecNotation : Delab :=
whenNotPPOption getPPExplicit whenPPOption getPPNotation withOverApp 3 do
    -- check that the `WithLp.toLp _` is present
let p : Term ← withNaryArg 0 delab
    -- to be conservative, only allow subscripts which are numerals
guard p matches `($_:num)
    let `(![$elems,*]) ← withNaryArg 2 delab | failure
    `(!$p[$elems,*])

end Notation

/--
theorem `EuclideanSpace.nnnorm_eq` / 定理 `EuclideanSpace.nnnorm_eq`

English:
theorem EuclideanSpace.nnnorm_eq
  statement: {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
  proof: PiLp.nnnorm_eq_of_L2 x

中文:
定理 EuclideanSpace.nnnorm_eq
  结论: {𝕜 : 类型} [RCLike 𝕜] {n : 类型} [有限类型 n]
  证明: PiLp.nnnorm_eq_of_L2 x

Depends on / 依赖: PiLp.nnnorm_eq_of_L2, nnnorm_eq_of_L2
-/
theorem EuclideanSpace.nnnorm_eq {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
    (x : EuclideanSpace 𝕜 n) : ‖x‖₊ = NNReal.sqrt (∑ i, ‖x i‖₊ ^ 2) :=
  PiLp.nnnorm_eq_of_L2 x

/--
theorem `EuclideanSpace.norm_eq` / 定理 `EuclideanSpace.norm_eq`

English:
theorem EuclideanSpace.norm_eq
  statement: {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
  proof: by
  simpa only [Real.coe_sqrt, NNReal.coe_sum] using! congr_arg ((↑) : Real>=0 -> Real) x.nnnorm_eq

中文:
定理 EuclideanSpace.norm_eq
  结论: {𝕜 : 类型} [RCLike 𝕜] {n : 类型} [有限类型 n]
  证明: by
  simpa only [Real.coe_sqrt, NNReal.coe_sum] using! congr_arg ((↑) : Real>=0 -> Real) x.nnnorm_eq

Depends on / 依赖: NNReal, NNReal.coe_sum, Real.coe_sqrt, coe_sqrt, coe_sum, congr_arg, nnnorm_eq, x.nnnorm_eq
-/
theorem EuclideanSpace.norm_eq {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
    (x : EuclideanSpace 𝕜 n) : ‖x‖ = √(∑ i, ‖x i‖ ^ 2) := by
  simpa only [Real.coe_sqrt, NNReal.coe_sum] using! congr_arg ((↑) : Real>=0 -> Real) x.nnnorm_eq

/--
theorem `EuclideanSpace.norm_sq_eq` / 定理 `EuclideanSpace.norm_sq_eq`

English:
theorem EuclideanSpace.norm_sq_eq
  statement: {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
  proof: PiLp.norm_sq_eq_of_L2 _ x

中文:
定理 EuclideanSpace.norm_sq_eq
  结论: {𝕜 : 类型} [RCLike 𝕜] {n : 类型} [有限类型 n]
  证明: PiLp.norm_sq_eq_of_L2 _ x

Depends on / 依赖: PiLp.norm_sq_eq_of_L2, norm_sq_eq_of_L2
-/
theorem EuclideanSpace.norm_sq_eq {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
    (x : EuclideanSpace 𝕜 n) : ‖x‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 :=
  PiLp.norm_sq_eq_of_L2 _ x

/--
theorem `EuclideanSpace.real_norm_sq_eq` / 定理 `EuclideanSpace.real_norm_sq_eq`

English:
theorem EuclideanSpace.real_norm_sq_eq
  given: {n : Type*} [Fintype n] (x : EuclideanSpace Real n)
  proof: by
  simp [EuclideanSpace.norm_sq_eq]

@[wikidata Q847073]

中文:
定理 EuclideanSpace.real_norm_sq_eq
  条件: {n : 类型} [有限类型 n] (x : EuclideanSpace 实数 n)
  证明: by
  simp [EuclideanSpace.norm_sq_eq]

@[wikidata Q847073]

Depends on / 依赖: EuclideanSpace, EuclideanSpace.norm_sq_eq, norm_sq_eq
-/
theorem EuclideanSpace.real_norm_sq_eq {n : Type*} [Fintype n] (x : EuclideanSpace Real n) :
    ‖x‖ ^ 2 = ∑ i, (x i) ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq]

@[wikidata Q847073]
/--
theorem `EuclideanSpace.dist_eq` / 定理 `EuclideanSpace.dist_eq`

English:
theorem EuclideanSpace.dist_eq
  statement: {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
  proof: PiLp.dist_eq_of_L2 x y

中文:
定理 EuclideanSpace.dist_eq
  结论: {𝕜 : 类型} [RCLike 𝕜] {n : 类型} [有限类型 n]
  证明: PiLp.dist_eq_of_L2 x y

Depends on / 依赖: PiLp.dist_eq_of_L2, dist_eq_of_L2
-/
theorem EuclideanSpace.dist_eq {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
    (x y : EuclideanSpace 𝕜 n) : dist x y = √(∑ i, dist (x i) (y i) ^ 2) :=
  PiLp.dist_eq_of_L2 x y

/--
theorem `EuclideanSpace.dist_sq_eq` / 定理 `EuclideanSpace.dist_sq_eq`

English:
theorem EuclideanSpace.dist_sq_eq
  statement: {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
  proof: PiLp.dist_sq_eq_of_L2 x y

中文:
定理 EuclideanSpace.dist_sq_eq
  结论: {𝕜 : 类型} [RCLike 𝕜] {n : 类型} [有限类型 n]
  证明: PiLp.dist_sq_eq_of_L2 x y

Depends on / 依赖: PiLp.dist_sq_eq_of_L2, dist_sq_eq_of_L2
-/
theorem EuclideanSpace.dist_sq_eq {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
    (x y : EuclideanSpace 𝕜 n) : dist x y ^ 2 = ∑ i, dist (x i) (y i) ^ 2 :=
  PiLp.dist_sq_eq_of_L2 x y

/--
theorem `EuclideanSpace.nndist_eq` / 定理 `EuclideanSpace.nndist_eq`

English:
theorem EuclideanSpace.nndist_eq
  statement: {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
  proof: PiLp.nndist_eq_of_L2 x y

中文:
定理 EuclideanSpace.nndist_eq
  结论: {𝕜 : 类型} [RCLike 𝕜] {n : 类型} [有限类型 n]
  证明: PiLp.nndist_eq_of_L2 x y

Depends on / 依赖: PiLp.nndist_eq_of_L2, nndist_eq_of_L2
-/
theorem EuclideanSpace.nndist_eq {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
    (x y : EuclideanSpace 𝕜 n) : nndist x y = NNReal.sqrt (∑ i, nndist (x i) (y i) ^ 2) :=
  PiLp.nndist_eq_of_L2 x y

/--
theorem `EuclideanSpace.edist_eq` / 定理 `EuclideanSpace.edist_eq`

English:
theorem EuclideanSpace.edist_eq
  statement: {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
  proof: PiLp.edist_eq_of_L2 x y

中文:
定理 EuclideanSpace.edist_eq
  结论: {𝕜 : 类型} [RCLike 𝕜] {n : 类型} [有限类型 n]
  证明: PiLp.edist_eq_of_L2 x y

Depends on / 依赖: PiLp.edist_eq_of_L2, edist_eq_of_L2
-/
theorem EuclideanSpace.edist_eq {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]
    (x y : EuclideanSpace 𝕜 n) : edist x y = (∑ i, edist (x i) (y i) ^ 2) ^ (1 / 2 : Real) :=
  PiLp.edist_eq_of_L2 x y

/--
theorem `EuclideanSpace.ball_zero_eq` / 定理 `EuclideanSpace.ball_zero_eq`

English:
theorem EuclideanSpace.ball_zero_eq
  given: {n : Type*} [Fintype n] (r : Real) (hr : 0 <= r)
  proof: by
  ext x
  have : (0 : Real) <= ∑ i, x i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  simp_rw [mem_ofPred, mem_ball_zero_iff, norm_eq, norm_eq_abs, sq_abs, sqrt_lt this hr]

中文:
定理 EuclideanSpace.ball_zero_eq
  条件: {n : 类型} [有限类型 n] (r : 实数) (hr : 0 <= r)
  证明: by
  ext x
  have : (0 : Real) <= ∑ i, x i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  simp_rw [mem_ofPred, mem_ball_zero_iff, norm_eq, norm_eq_abs, sq_abs, sqrt_lt this hr]

Depends on / 依赖: Finset, Finset.sum_nonneg, mem_ball_zero_iff, mem_ofPred, norm_eq, norm_eq_abs, simp_rw, sq_abs, sq_nonneg, sqrt_lt, sum_nonneg
-/
theorem EuclideanSpace.ball_zero_eq {n : Type*} [Fintype n] (r : Real) (hr : 0 <= r) :
    Metric.ball (0 : EuclideanSpace Real n) r = {x | ∑ i, x i ^ 2 < r ^ 2} := by
  ext x
  have : (0 : Real) <= ∑ i, x i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  simp_rw [mem_ofPred, mem_ball_zero_iff, norm_eq, norm_eq_abs, sq_abs, sqrt_lt this hr]

/--
theorem `EuclideanSpace.closedBall_zero_eq` / 定理 `EuclideanSpace.closedBall_zero_eq`

English:
theorem EuclideanSpace.closedBall_zero_eq
  given: {n : Type*} [Fintype n] (r : Real) (hr : 0 <= r)
  proof: by
  ext
  simp_rw [mem_ofPred, mem_closedBall_zero_iff, norm_eq, norm_eq_abs, sq_abs, sqrt_le_left hr]

中文:
定理 EuclideanSpace.closedBall_zero_eq
  条件: {n : 类型} [有限类型 n] (r : 实数) (hr : 0 <= r)
  证明: by
  ext
  simp_rw [mem_ofPred, mem_closedBall_zero_iff, norm_eq, norm_eq_abs, sq_abs, sqrt_le_left hr]

Depends on / 依赖: mem_closedBall_zero_iff, mem_ofPred, norm_eq, norm_eq_abs, simp_rw, sq_abs, sqrt_le_left
-/
theorem EuclideanSpace.closedBall_zero_eq {n : Type*} [Fintype n] (r : Real) (hr : 0 <= r) :
    Metric.closedBall (0 : EuclideanSpace Real n) r = {x | ∑ i, x i ^ 2 <= r ^ 2} := by
  ext
  simp_rw [mem_ofPred, mem_closedBall_zero_iff, norm_eq, norm_eq_abs, sq_abs, sqrt_le_left hr]

/--
theorem `EuclideanSpace.sphere_zero_eq` / 定理 `EuclideanSpace.sphere_zero_eq`

English:
theorem EuclideanSpace.sphere_zero_eq
  given: {n : Type*} [Fintype n] (r : Real) (hr : 0 <= r)
  proof: by
  ext x
  have : (0 : Real) <= ∑ i, x i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  simp_rw [mem_ofPred, mem_sphere_zero_iff_norm, norm_eq, norm_eq_abs, sq_abs,
    Real.sqrt_eq_iff_eq_sq this hr]

中文:
定理 EuclideanSpace.sphere_zero_eq
  条件: {n : 类型} [有限类型 n] (r : 实数) (hr : 0 <= r)
  证明: by
  ext x
  have : (0 : Real) <= ∑ i, x i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  simp_rw [mem_ofPred, mem_sphere_zero_iff_norm, norm_eq, norm_eq_abs, sq_abs,
    Real.sqrt_eq_iff_eq_sq this hr]

Depends on / 依赖: Finset, Finset.sum_nonneg, Real.sqrt_eq_iff_eq_sq, mem_ofPred, mem_sphere_zero_iff_norm, norm_eq, norm_eq_abs, simp_rw, sq_abs, sq_nonneg, sqrt_eq_iff_eq_sq, sum_nonneg
-/
theorem EuclideanSpace.sphere_zero_eq {n : Type*} [Fintype n] (r : Real) (hr : 0 <= r) :
    Metric.sphere (0 : EuclideanSpace Real n) r = {x | ∑ i, x i ^ 2 = r ^ 2} := by
  ext x
  have : (0 : Real) <= ∑ i, x i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  simp_rw [mem_ofPred, mem_sphere_zero_iff_norm, norm_eq, norm_eq_abs, sq_abs,
    Real.sqrt_eq_iff_eq_sq this hr]

section

/--
Instance `EuclideanSpace.infinite` / 实例 `EuclideanSpace.infinite`

English:
instance EuclideanSpace.infinite
  signature: [Nonempty ι]
  body: Module.Free.infinite 𝕜 _

中文:
实例 EuclideanSpace.infinite
  签名: [非空 ι]
  定义体: Module.Free.infinite 𝕜 _

Depends on / 依赖: Module, Module.Free.infinite, infinite
-/
instance EuclideanSpace.infinite [Nonempty ι] : Infinite (EuclideanSpace 𝕜 ι) :=
  Module.Free.infinite 𝕜 _

variable [Fintype ι]

@[simp]
/--
theorem `finrank_euclideanSpace` / 定理 `finrank_euclideanSpace`

English:
theorem finrank_euclideanSpace
  proof: by
  convert! (WithLp.linearEquiv 2 𝕜 (ι -> 𝕜)).finrank_eq
  simp

中文:
定理 finrank_euclideanSpace
  证明: by
  convert! (WithLp.linearEquiv 2 𝕜 (ι -> 𝕜)).finrank_eq
  simp

Depends on / 依赖: WithLp, WithLp.linearEquiv, convert, finrank_eq, linearEquiv
-/
theorem finrank_euclideanSpace :
    Module.finrank 𝕜 (EuclideanSpace 𝕜 ι) = Fintype.card ι := by
  convert! (WithLp.linearEquiv 2 𝕜 (ι -> 𝕜)).finrank_eq
  simp

/--
theorem `finrank_euclideanSpace_fin` / 定理 `finrank_euclideanSpace_fin`

English:
theorem finrank_euclideanSpace_fin
  given: {n : Nat}
  proof: by simp

中文:
定理 finrank_euclideanSpace_fin
  条件: {n : 自然数}
  证明: by simp
-/
theorem finrank_euclideanSpace_fin {n : Nat} :
    Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin n)) = n := by simp

namespace EuclideanSpace

scoped instance (n : Nat) : Fact (Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin n)) = n) :=
  ⟨finrank_euclideanSpace_fin⟩

/--
theorem `inner_eq_star_dotProduct` / 定理 `inner_eq_star_dotProduct`

English:
theorem inner_eq_star_dotProduct
  given: (x y : EuclideanSpace 𝕜 ι)
  proof: rfl

中文:
定理 inner_eq_star_dotProduct
  条件: (x y : EuclideanSpace 𝕜 ι)
  证明: rfl
-/
theorem inner_eq_star_dotProduct (x y : EuclideanSpace 𝕜 ι) :
    ⟪x, y⟫ = ofLp y ⬝ᵥ star (ofLp x) := rfl

/--
lemma `inner_toLp_toLp` / 引理 `inner_toLp_toLp`

English:
lemma inner_toLp_toLp
  given: (x y : ι -> 𝕜)
  proof: rfl

中文:
引理 inner_toLp_toLp
  条件: (x y : ι -> 𝕜)
  证明: rfl
-/
lemma inner_toLp_toLp (x y : ι -> 𝕜) :
    ⟪toLp 2 x, toLp 2 y⟫ = dotProduct y (star x) := rfl

section restrict₂

variable {I J : Finset ι'}

/-- The restriction from `EuclideanSpace 𝕜 J` to `EuclideanSpace 𝕜 I` when `I ⊆ J`. -/
noncomputable
/--
Definition of `restrict₂` / `restrict₂` 的定义

English:
definition restrict₂
  signature: (hIJ : I subseteq J)
  body: toLp 2 (Finset.restrict₂ («π» := fun _ => 𝕜) hIJ x.ofLp)
  map_add' x y := by ext; simp
  map_smul' m x := by ext; simp

@[simp]

中文:
定义 restrict₂
  签名: (hIJ : I subseteq J)
  定义体: toLp 2 (Finset.restrict₂ («π» := fun _ => 𝕜) hIJ x.ofLp)
  map_add' x y := by ext; simp
  map_smul' m x := by ext; simp

@[simp]

Depends on / 依赖: Finset, Finset.restrict, x.ofLp
-/
def restrict₂ (hIJ : I subseteq J) :
    EuclideanSpace 𝕜 J ->L[𝕜] EuclideanSpace 𝕜 I where
  toFun x := toLp 2 (Finset.restrict₂ («π» := fun _ => 𝕜) hIJ x.ofLp)
  map_add' x y := by ext; simp
  map_smul' m x := by ext; simp

@[simp]
/--
lemma `restrict₂_apply` / 引理 `restrict₂_apply`

English:
lemma restrict₂_apply
  given: (hIJ : I subseteq J) (x : EuclideanSpace 𝕜 J) (i : I)
  proof: rfl

中文:
引理 restrict₂_apply
  条件: (hIJ : I subseteq J) (x : EuclideanSpace 𝕜 J) (i : I)
  证明: rfl
-/
lemma restrict₂_apply (hIJ : I subseteq J) (x : EuclideanSpace 𝕜 J) (i : I) :
    EuclideanSpace.restrict₂ hIJ x i = x ⟨i.1, hIJ i.2⟩ := rfl

end restrict₂

end EuclideanSpace

/--
Definition of `DirectSum.IsInternal.isometryL2OfOrthogonalFamily` / `DirectSum.IsInternal.isometryL2OfOrthogonalFamily` 的定义

English:
definition DirectSum.IsInternal.isometryL2OfOrthogonalFamily
  signature: [DecidableEq ι] {V : ι -> Submodule 𝕜 E}
  body: by
  let e₁ := DirectSum.linearEquivFunOnFintype 𝕜 ι fun i => V i
  let e₂ := LinearEquiv.ofBijective (DirectSum.coeLinearMap V) hV
  refine LinearEquiv.isometryOfInner ((e₂.symm.trans e₁).trans
    (WithLp.linearEquiv 2 𝕜 (Π i, V i)).symm) ?_
  suffices forall (v w : PiLp 2 fun i => V i), ⟪v, w⟫ = ⟪e₂ (e₁.symm v), e₂ (e₁.symm w)⟫ by
    intro v₀ w₀
    simp only [LinearEquiv.trans_apply]
    convert! this (toLp 2 (e₁ (e₂.symm v₀))) (toLp 2 (e₁ (e₂.symm w₀))) <;> simp
  intro v w
  trans ⟪∑ i, (V i).subtypeₗᵢ (v i), ∑ i, (V i).subtypeₗᵢ (w i)⟫
  · simp only [sum_inner, hV'.inner_right_fintype, PiLp.inner_apply]
  · congr <;> simp

中文:
定义 直和.Is整数ernal.isometryL2OfOrthogonalFamily
  签名: [DecidableEq ι] {V : ι -> 子模 𝕜 E}
  定义体: by
  let e₁ := DirectSum.linearEquivFunOnFintype 𝕜 ι fun i => V i
  let e₂ := LinearEquiv.ofBijective (DirectSum.coeLinearMap V) hV
  refine LinearEquiv.isometryOfInner ((e₂.symm.trans e₁).trans
    (WithLp.linearEquiv 2 𝕜 (Π i, V i)).symm) ?_
  suffices forall (v w : PiLp 2 fun i => V i), ⟪v, w⟫ = ⟪e₂ (e₁.symm v), e₂ (e₁.symm w)⟫ by
    intro v₀ w₀
    simp only [LinearEquiv.trans_apply]
    convert! this (toLp 2 (e₁ (e₂.symm v₀))) (toLp 2 (e₁ (e₂.symm w₀))) <;> simp
  intro v w
  trans ⟪∑ i, (V i).subtypeₗᵢ (v i), ∑ i, (V i).subtypeₗᵢ (w i)⟫
  · simp only [sum_inner, hV'.inner_right_fintype, PiLp.inner_apply]
  · congr <;> simp

Depends on / 依赖: DirectSum, DirectSum.coeLinearMap, DirectSum.linearEquivFunOnFintype, LinearEquiv, LinearEquiv.isometryOfInner, LinearEquiv.ofBijective, LinearEquiv.trans_apply, WithLp, WithLp.linearEquiv, coeLinearMap, convert, isometryOfInner, linearEquiv, linearEquivFunOnFintype, ofBijective, symm.trans, trans_apply
-/
def DirectSum.IsInternal.isometryL2OfOrthogonalFamily [DecidableEq ι] {V : ι -> Submodule 𝕜 E}
    (hV : DirectSum.IsInternal V)
    (hV' : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) :
    E ≃ₗᵢ[𝕜] PiLp 2 fun i => V i := by
  let e₁ := DirectSum.linearEquivFunOnFintype 𝕜 ι fun i => V i
  let e₂ := LinearEquiv.ofBijective (DirectSum.coeLinearMap V) hV
  refine LinearEquiv.isometryOfInner ((e₂.symm.trans e₁).trans
    (WithLp.linearEquiv 2 𝕜 (Π i, V i)).symm) ?_
  suffices forall (v w : PiLp 2 fun i => V i), ⟪v, w⟫ = ⟪e₂ (e₁.symm v), e₂ (e₁.symm w)⟫ by
    intro v₀ w₀
    simp only [LinearEquiv.trans_apply]
    convert! this (toLp 2 (e₁ (e₂.symm v₀))) (toLp 2 (e₁ (e₂.symm w₀))) <;> simp
  intro v w
  trans ⟪∑ i, (V i).subtypeₗᵢ (v i), ∑ i, (V i).subtypeₗᵢ (w i)⟫
  · simp only [sum_inner, hV'.inner_right_fintype, PiLp.inner_apply]
  · congr <;> simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `DirectSum.IsInternal.isometryL2OfOrthogonalFamily_symm_apply` / 定理 `DirectSum.IsInternal.isometryL2OfOrthogonalFamily_symm_apply`

English:
theorem DirectSum.IsInternal.isometryL2OfOrthogonalFamily_symm_apply
  statement: [DecidableEq ι]
  proof: by
  classical
    let e₁ := DirectSum.linearEquivFunOnFintype 𝕜 ι fun i => V i
    let e₂ := LinearEquiv.ofBijective (DirectSum.coeLinearMap V) hV
    suffices forall v : ⨁ i, V i, e₂ v = ∑ i, e₁ v i by exact this (e₁.symm w)
    simp [e₁, e₂, DirectSum.coeLinearMap, DirectSum.toModule, DFinsupp.lsum,
      DFinsupp.sumAddHom_apply]

中文:
定理 直和.Is整数ernal.isometryL2OfOrthogonalFamily_symm_apply
  结论: [DecidableEq ι]
  证明: by
  classical
    let e₁ := DirectSum.linearEquivFunOnFintype 𝕜 ι fun i => V i
    let e₂ := LinearEquiv.ofBijective (DirectSum.coeLinearMap V) hV
    suffices forall v : ⨁ i, V i, e₂ v = ∑ i, e₁ v i by exact this (e₁.symm w)
    simp [e₁, e₂, DirectSum.coeLinearMap, DirectSum.toModule, DFinsupp.lsum,
      DFinsupp.sumAddHom_apply]

Depends on / 依赖: DFinsupp, DFinsupp.lsum, DFinsupp.sumAddHom_apply, DirectSum, DirectSum.coeLinearMap, DirectSum.linearEquivFunOnFintype, DirectSum.toModule, LinearEquiv, LinearEquiv.ofBijective, classical, coeLinearMap, linearEquivFunOnFintype, ofBijective, sumAddHom_apply, toModule
-/
theorem DirectSum.IsInternal.isometryL2OfOrthogonalFamily_symm_apply [DecidableEq ι]
    {V : ι -> Submodule 𝕜 E} (hV : DirectSum.IsInternal V)
    (hV' : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) (w : PiLp 2 fun i => V i) :
    (hV.isometryL2OfOrthogonalFamily hV').symm w = ∑ i, (w i : E) := by
  classical
    let e₁ := DirectSum.linearEquivFunOnFintype 𝕜 ι fun i => V i
    let e₂ := LinearEquiv.ofBijective (DirectSum.coeLinearMap V) hV
    suffices forall v : ⨁ i, V i, e₂ v = ∑ i, e₁ v i by exact this (e₁.symm w)
    simp [e₁, e₂, DirectSum.coeLinearMap, DirectSum.toModule, DFinsupp.lsum,
      DFinsupp.sumAddHom_apply]

end

variable (ι 𝕜)

/--
Definition of `EuclideanSpace.equiv` / `EuclideanSpace.equiv` 的定义

English:
abbreviation EuclideanSpace.equiv
  signature: : EuclideanSpace 𝕜 ι ≃L[𝕜] ι -> 𝕜
  body: PiLp.continuousLinearEquiv 2 𝕜 _

中文:
缩写 EuclideanSpace.equiv
  签名: : EuclideanSpace 𝕜 ι ≃L[𝕜] ι -> 𝕜
  定义体: PiLp.continuousLinearEquiv 2 𝕜 _

Depends on / 依赖: PiLp.continuousLinearEquiv, continuousLinearEquiv
-/
abbrev EuclideanSpace.equiv : EuclideanSpace 𝕜 ι ≃L[𝕜] ι -> 𝕜 :=
  PiLp.continuousLinearEquiv 2 𝕜 _

variable {ι 𝕜}

/--
Definition of `EuclideanSpace.projₗ` / `EuclideanSpace.projₗ` 的定义

English:
abbreviation EuclideanSpace.projₗ
  signature: (i : ι)
  body: PiLp.projₗ _ _ i

中文:
缩写 EuclideanSpace.projₗ
  签名: (i : ι)
  定义体: PiLp.projₗ _ _ i

Depends on / 依赖: PiLp.proj
-/
abbrev EuclideanSpace.projₗ (i : ι) : EuclideanSpace 𝕜 ι ->ₗ[𝕜] 𝕜 := PiLp.projₗ _ _ i

/--
Definition of `EuclideanSpace.proj` / `EuclideanSpace.proj` 的定义

English:
abbreviation EuclideanSpace.proj
  signature: (i : ι)
  body: PiLp.proj _ _ i

@[simp]

中文:
缩写 EuclideanSpace.proj
  签名: (i : ι)
  定义体: PiLp.proj _ _ i

@[simp]

Depends on / 依赖: PiLp.proj
-/
abbrev EuclideanSpace.proj (i : ι) : StrongDual 𝕜 (EuclideanSpace 𝕜 ι) := PiLp.proj _ _ i

@[simp]
/--
lemma `EuclideanSpace.coe_proj` / 引理 `EuclideanSpace.coe_proj`

English:
lemma EuclideanSpace.coe_proj
  given: {ι : Type*} (𝕜 : Type*) [RCLike 𝕜] {i : ι}
  proof: rfl

中文:
引理 EuclideanSpace.coe_proj
  条件: {ι : 类型} (𝕜 : 类型) [RCLike 𝕜] {i : ι}
  证明: rfl
-/
lemma EuclideanSpace.coe_proj {ι : Type*} (𝕜 : Type*) [RCLike 𝕜] {i : ι} :
    ⇑(@proj ι 𝕜 _ i) = fun x => x i := rfl

section DecEq

variable [DecidableEq ι]

/--
Definition of `EuclideanSpace.single` / `EuclideanSpace.single` 的定义

English:
abbreviation EuclideanSpace.single
  signature: (i : ι) (a : 𝕜)
  body: PiLp.single 2 i a

@[deprecated PiLp.ofLp_single (since := "2026-03-15")]

中文:
缩写 EuclideanSpace.single
  签名: (i : ι) (a : 𝕜)
  定义体: PiLp.single 2 i a

@[deprecated PiLp.ofLp_single (since := "2026-03-15")]

Depends on / 依赖: PiLp.single, single
-/
abbrev EuclideanSpace.single (i : ι) (a : 𝕜) : EuclideanSpace 𝕜 ι := PiLp.single 2 i a

@[deprecated PiLp.ofLp_single (since := "2026-03-15")]
/--
lemma `EuclideanSpace.ofLp_single` / 引理 `EuclideanSpace.ofLp_single`

English:
lemma EuclideanSpace.ofLp_single
  given: (i : ι) (a : 𝕜)
  statement: ofLp (single i a) = Pi.single i a
  proof: by
  simp

@[deprecated PiLp.toLp_single (since := "2026-03-15")]

中文:
引理 EuclideanSpace.ofLp_single
  条件: (i : ι) (a : 𝕜)
  结论: ofLp (single i a) = 依赖函数类型.single i a
  证明: by
  simp

@[deprecated PiLp.toLp_single (since := "2026-03-15")]
-/
lemma EuclideanSpace.ofLp_single (i : ι) (a : 𝕜) : ofLp (single i a) = Pi.single i a := by
  simp

@[deprecated PiLp.toLp_single (since := "2026-03-15")]
/--
lemma `EuclideanSpace.toLp_single` / 引理 `EuclideanSpace.toLp_single`

English:
lemma EuclideanSpace.toLp_single
  given: (i : ι) (a : 𝕜)
  statement: toLp _ (Pi.single i a) = single i a
  proof: by
  simp

@[deprecated PiLp.single_apply (since := "2026-03-15")]

中文:
引理 EuclideanSpace.toLp_single
  条件: (i : ι) (a : 𝕜)
  结论: toLp _ (依赖函数类型.single i a) = single i a
  证明: by
  simp

@[deprecated PiLp.single_apply (since := "2026-03-15")]
-/
lemma EuclideanSpace.toLp_single (i : ι) (a : 𝕜) : toLp _ (Pi.single i a) = single i a := by
  simp

@[deprecated PiLp.single_apply (since := "2026-03-15")]
/--
theorem `EuclideanSpace.single_apply` / 定理 `EuclideanSpace.single_apply`

English:
theorem EuclideanSpace.single_apply
  given: (i : ι) (a : 𝕜) (j : ι)
  proof: by
  simp

@[deprecated PiLp.single_eq_zero_iff (since := "2026-03-15")]

中文:
定理 EuclideanSpace.single_apply
  条件: (i : ι) (a : 𝕜) (j : ι)
  证明: by
  simp

@[deprecated PiLp.single_eq_zero_iff (since := "2026-03-15")]
-/
theorem EuclideanSpace.single_apply (i : ι) (a : 𝕜) (j : ι) :
    (EuclideanSpace.single i a) j = ite (j = i) a 0 := by
  simp

@[deprecated PiLp.single_eq_zero_iff (since := "2026-03-15")]
/--
theorem `EuclideanSpace.single_eq_zero_iff` / 定理 `EuclideanSpace.single_eq_zero_iff`

English:
theorem EuclideanSpace.single_eq_zero_iff
  given: {i : ι} {a : 𝕜}
  proof: by simp

中文:
定理 EuclideanSpace.single_eq_zero_iff
  条件: {i : ι} {a : 𝕜}
  证明: by simp
-/
theorem EuclideanSpace.single_eq_zero_iff {i : ι} {a : 𝕜} :
    EuclideanSpace.single i a = 0 ↔ a = 0 := by simp

variable [Fintype ι]

/--
theorem `EuclideanSpace.inner_single_left` / 定理 `EuclideanSpace.inner_single_left`

English:
theorem EuclideanSpace.inner_single_left
  given: (i : ι) (a : 𝕜) (v : EuclideanSpace 𝕜 ι)
  proof: by
  simp [PiLp.inner_apply, apply_ite conj, mul_comm]

中文:
定理 EuclideanSpace.inner_single_left
  条件: (i : ι) (a : 𝕜) (v : EuclideanSpace 𝕜 ι)
  证明: by
  simp [PiLp.inner_apply, apply_ite conj, mul_comm]

Depends on / 依赖: PiLp.inner_apply, apply_ite, inner_apply, mul_comm
-/
theorem EuclideanSpace.inner_single_left (i : ι) (a : 𝕜) (v : EuclideanSpace 𝕜 ι) :
    ⟪EuclideanSpace.single i (a : 𝕜), v⟫ = conj a * v i := by
  simp [PiLp.inner_apply, apply_ite conj, mul_comm]

/--
theorem `EuclideanSpace.inner_single_right` / 定理 `EuclideanSpace.inner_single_right`

English:
theorem EuclideanSpace.inner_single_right
  given: (i : ι) (a : 𝕜) (v : EuclideanSpace 𝕜 ι)
  proof: by simp [PiLp.inner_apply]

@[deprecated PiLp.norm_single (since := "2026-03-15")]

中文:
定理 EuclideanSpace.inner_single_right
  条件: (i : ι) (a : 𝕜) (v : EuclideanSpace 𝕜 ι)
  证明: by simp [PiLp.inner_apply]

@[deprecated PiLp.norm_single (since := "2026-03-15")]

Depends on / 依赖: PiLp.inner_apply, inner_apply
-/
theorem EuclideanSpace.inner_single_right (i : ι) (a : 𝕜) (v : EuclideanSpace 𝕜 ι) :
    ⟪v, EuclideanSpace.single i (a : 𝕜)⟫ = a * conj (v i) := by simp [PiLp.inner_apply]

@[deprecated PiLp.norm_single (since := "2026-03-15")]
/--
theorem `EuclideanSpace.norm_single` / 定理 `EuclideanSpace.norm_single`

English:
theorem EuclideanSpace.norm_single
  given: (i : ι) (a : 𝕜)
  proof: by simp

@[deprecated PiLp.nnnorm_single (since := "2026-03-15")]

中文:
定理 EuclideanSpace.norm_single
  条件: (i : ι) (a : 𝕜)
  证明: by simp

@[deprecated PiLp.nnnorm_single (since := "2026-03-15")]
-/
theorem EuclideanSpace.norm_single (i : ι) (a : 𝕜) :
    ‖EuclideanSpace.single i (a : 𝕜)‖ = ‖a‖ := by simp

@[deprecated PiLp.nnnorm_single (since := "2026-03-15")]
/--
theorem `EuclideanSpace.nnnorm_single` / 定理 `EuclideanSpace.nnnorm_single`

English:
theorem EuclideanSpace.nnnorm_single
  given: (i : ι) (a : 𝕜)
  proof: by simp

@[deprecated PiLp.dist_single_same (since := "2026-03-15")]

中文:
定理 EuclideanSpace.nnnorm_single
  条件: (i : ι) (a : 𝕜)
  证明: by simp

@[deprecated PiLp.dist_single_same (since := "2026-03-15")]
-/
theorem EuclideanSpace.nnnorm_single (i : ι) (a : 𝕜) :
    ‖EuclideanSpace.single i (a : 𝕜)‖₊ = ‖a‖₊ := by simp

@[deprecated PiLp.dist_single_same (since := "2026-03-15")]
/--
theorem `EuclideanSpace.dist_single_same` / 定理 `EuclideanSpace.dist_single_same`

English:
theorem EuclideanSpace.dist_single_same
  given: (i : ι) (a b : 𝕜)
  proof: by
  simp

@[deprecated PiLp.nndist_single_same (since := "2026-03-15")]

中文:
定理 EuclideanSpace.dist_single_same
  条件: (i : ι) (a b : 𝕜)
  证明: by
  simp

@[deprecated PiLp.nndist_single_same (since := "2026-03-15")]
-/
theorem EuclideanSpace.dist_single_same (i : ι) (a b : 𝕜) :
    dist (EuclideanSpace.single i (a : 𝕜)) (EuclideanSpace.single i (b : 𝕜)) = dist a b := by
  simp

@[deprecated PiLp.nndist_single_same (since := "2026-03-15")]
/--
theorem `EuclideanSpace.nndist_single_same` / 定理 `EuclideanSpace.nndist_single_same`

English:
theorem EuclideanSpace.nndist_single_same
  given: (i : ι) (a b : 𝕜)
  proof: by
  simp

@[deprecated PiLp.edist_single_same (since := "2026-03-15")]

中文:
定理 EuclideanSpace.nndist_single_same
  条件: (i : ι) (a b : 𝕜)
  证明: by
  simp

@[deprecated PiLp.edist_single_same (since := "2026-03-15")]
-/
theorem EuclideanSpace.nndist_single_same (i : ι) (a b : 𝕜) :
    nndist (EuclideanSpace.single i (a : 𝕜)) (EuclideanSpace.single i (b : 𝕜)) = nndist a b := by
  simp

@[deprecated PiLp.edist_single_same (since := "2026-03-15")]
/--
theorem `EuclideanSpace.edist_single_same` / 定理 `EuclideanSpace.edist_single_same`

English:
theorem EuclideanSpace.edist_single_same
  given: (i : ι) (a b : 𝕜)
  proof: by
  simp

中文:
定理 EuclideanSpace.edist_single_same
  条件: (i : ι) (a b : 𝕜)
  证明: by
  simp
-/
theorem EuclideanSpace.edist_single_same (i : ι) (a b : 𝕜) :
    edist (EuclideanSpace.single i (a : 𝕜)) (EuclideanSpace.single i (b : 𝕜)) = edist a b := by
  simp

/--
theorem `EuclideanSpace.orthonormal_single` / 定理 `EuclideanSpace.orthonormal_single`

English:
theorem EuclideanSpace.orthonormal_single
  proof: by
  simp_rw [orthonormal_iff_ite, EuclideanSpace.inner_single_left, map_one, one_mul,
    PiLp.single_apply]
  intros
  trivial

中文:
定理 EuclideanSpace.orthonormal_single
  证明: by
  simp_rw [orthonormal_iff_ite, EuclideanSpace.inner_single_left, map_one, one_mul,
    PiLp.single_apply]
  intros
  trivial

Depends on / 依赖: EuclideanSpace, EuclideanSpace.inner_single_left, PiLp.single_apply, inner_single_left, intros, map_one, one_mul, orthonormal_iff_ite, simp_rw, single_apply
-/
theorem EuclideanSpace.orthonormal_single :
    Orthonormal 𝕜 fun i : ι => EuclideanSpace.single i (1 : 𝕜) := by
  simp_rw [orthonormal_iff_ite, EuclideanSpace.inner_single_left, map_one, one_mul,
    PiLp.single_apply]
  intros
  trivial

/--
theorem `EuclideanSpace.piLpCongrLeft_single` / 定理 `EuclideanSpace.piLpCongrLeft_single`

English:
theorem EuclideanSpace.piLpCongrLeft_single
  proof: LinearIsometryEquiv.piLpCongrLeft_single e i' _

中文:
定理 EuclideanSpace.piLpCongrLeft_single
  证明: LinearIsometryEquiv.piLpCongrLeft_single e i' _

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.piLpCongrLeft_single, piLpCongrLeft_single
-/
theorem EuclideanSpace.piLpCongrLeft_single
    {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (e : ι' ≃ ι) (i' : ι') (v : 𝕜) :
    LinearIsometryEquiv.piLpCongrLeft 2 𝕜 𝕜 e (EuclideanSpace.single i' v) =
      EuclideanSpace.single (e i') v :=
  LinearIsometryEquiv.piLpCongrLeft_single e i' _

end DecEq

section finAddEquivProd

/--
Definition of `EuclideanSpace.sumEquivProd` / `EuclideanSpace.sumEquivProd` 的定义

English:
abbreviation EuclideanSpace.sumEquivProd
  signature: {𝕜 : Type*} [RCLike 𝕜] {ι κ : Type*} [Fintype ι] [Fintype κ]
  body: (PiLp.sumPiLpEquivProdLpPiLp 2 _).toContinuousLinearEquiv.trans
    WithLp.prodContinuousLinearEquiv _ _ _ _

中文:
缩写 EuclideanSpace.sumEquivProd
  签名: {𝕜 : 类型} [RCLike 𝕜] {ι κ : 类型} [有限类型 ι] [有限类型 κ]
  定义体: (PiLp.sumPiLpEquivProdLpPiLp 2 _).toContinuousLinearEquiv.trans
    WithLp.prodContinuousLinearEquiv _ _ _ _

Depends on / 依赖: PiLp.sumPiLpEquivProdLpPiLp, WithLp, WithLp.prodContinuousLinearEquiv, prodContinuousLinearEquiv, sumPiLpEquivProdLpPiLp, toContinuousLinearEquiv, toContinuousLinearEquiv.trans
-/
abbrev EuclideanSpace.sumEquivProd {𝕜 : Type*} [RCLike 𝕜] {ι κ : Type*} [Fintype ι] [Fintype κ] :
    EuclideanSpace 𝕜 (ι oplus κ) ≃L[𝕜] EuclideanSpace 𝕜 ι × EuclideanSpace 𝕜 κ :=
(PiLp.sumPiLpEquivProdLpPiLp 2 _).toContinuousLinearEquiv.trans
    WithLp.prodContinuousLinearEquiv _ _ _ _

/--
Definition of `EuclideanSpace.finAddEquivProd` / `EuclideanSpace.finAddEquivProd` 的定义

English:
abbreviation EuclideanSpace.finAddEquivProd
  signature: {𝕜 : Type*} [RCLike 𝕜] {n m : Nat}
  body: (LinearIsometryEquiv.piLpCongrLeft 2 𝕜 𝕜 finSumFinEquiv.symm).toContinuousLinearEquiv.trans
    sumEquivProd

中文:
缩写 EuclideanSpace.finAddEquivProd
  签名: {𝕜 : 类型} [RCLike 𝕜] {n m : 自然数}
  定义体: (LinearIsometryEquiv.piLpCongrLeft 2 𝕜 𝕜 finSumFinEquiv.symm).toContinuousLinearEquiv.trans
    sumEquivProd

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.piLpCongrLeft, finSumFinEquiv, finSumFinEquiv.symm, piLpCongrLeft, sumEquivProd, toContinuousLinearEquiv, toContinuousLinearEquiv.trans
-/
abbrev EuclideanSpace.finAddEquivProd {𝕜 : Type*} [RCLike 𝕜] {n m : Nat} :
    EuclideanSpace 𝕜 (Fin (n + m)) ≃L[𝕜] EuclideanSpace 𝕜 (Fin n) × EuclideanSpace 𝕜 (Fin m) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 𝕜 𝕜 finSumFinEquiv.symm).toContinuousLinearEquiv.trans
    sumEquivProd

end finAddEquivProd

variable (ι 𝕜 E)
variable [Fintype ι]

/--
Definition of `OrthonormalBasis` / `OrthonormalBasis` 的定义

English:
structure OrthonormalBasis
  parameters: where ofRepr
  (no additional axioms)

中文:
结构 正交标准基
  参数: where ofRepr
  (无附加公理)
-/
structure OrthonormalBasis where ofRepr ::
  /-- Linear isometry between `E` and `EuclideanSpace 𝕜 ι` representing the orthonormal basis. -/
  repr : E ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 ι

variable {ι 𝕜 E}

namespace OrthonormalBasis

/--
theorem `repr_injective` / 定理 `repr_injective`

English:
theorem repr_injective
  proof: fun f g h => by
  cases f
  cases g
  congr

中文:
定理 repr_injective
  证明: fun f g h => by
  cases f
  cases g
  congr
-/
theorem repr_injective :
    Injective (repr : OrthonormalBasis ι 𝕜 E -> E ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 ι) := fun f g h => by
  cases f
  cases g
  congr

set_option backward.isDefEq.respectTransparency false in
/--
Instance `instFunLike` / 实例 `instFunLike`

English:
instance instFunLike
  signature: : FunLike (OrthonormalBasis ι 𝕜 E) ι E where
  body: by classical exact b.repr.symm (EuclideanSpace.single i (1 : 𝕜))
coe_injective b b' h := repr_injective LinearIsometryEquiv.toLinearEquiv_injective
LinearEquiv.symm_bijective.injective LinearEquiv.toLinearMap_injective by
      classical
        rw [← LinearMap.cancel_right (WithLp.linearEquiv 2 𝕜 (_ -> 𝕜)).symm.surjective]
        simp +instances only
        refine LinearMap.pi_ext fun i k => ?_
        have : k = k • (1 : 𝕜) := by rw [smul_eq_mul, mul_one]
        rw [this]; rw [Pi.single_smul]
        replace h := congr_fun h i
        simp only [LinearEquiv.comp_coe, map_smul, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
          coe_symm_linearEquiv, PiLp.toLp_single,
          LinearIsometryEquiv.coe_symm_toLinearEquiv] at h ⊢
        rw [h]

@[simp]

中文:
实例 instFunLike
  签名: : 函数状 (正交标准基 ι 𝕜 E) ι E where
  定义体: by classical exact b.repr.symm (EuclideanSpace.single i (1 : 𝕜))
coe_injective b b' h := repr_injective LinearIsometryEquiv.toLinearEquiv_injective
LinearEquiv.symm_bijective.injective LinearEquiv.toLinearMap_injective by
      classical
        rw [← LinearMap.cancel_right (WithLp.linearEquiv 2 𝕜 (_ -> 𝕜)).symm.surjective]
        simp +instances only
        refine LinearMap.pi_ext fun i k => ?_
        have : k = k • (1 : 𝕜) := by rw [smul_eq_mul, mul_one]
        rw [this]; rw [Pi.single_smul]
        replace h := congr_fun h i
        simp only [LinearEquiv.comp_coe, map_smul, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
          coe_symm_linearEquiv, PiLp.toLp_single,
          LinearIsometryEquiv.coe_symm_toLinearEquiv] at h ⊢
        rw [h]

@[simp]

Depends on / 依赖: EuclideanSpace, EuclideanSpace.single, LinearEquiv, LinearEquiv.symm_bijective.injective, LinearEquiv.toLinearMap_injective, LinearIsometryEquiv, LinearIsometryEquiv.toLinearEquiv_injective, LinearMap, LinearMap.cancel_right, LinearMap.pi_ext, Pi.single_smul, WithLp, WithLp.linearEquiv, b.repr.symm, cancel_right, classical, coe_injective, congr_fun, injective, instances
-/
instance instFunLike : FunLike (OrthonormalBasis ι 𝕜 E) ι E where
  coe b i := by classical exact b.repr.symm (EuclideanSpace.single i (1 : 𝕜))
coe_injective b b' h := repr_injective LinearIsometryEquiv.toLinearEquiv_injective
LinearEquiv.symm_bijective.injective LinearEquiv.toLinearMap_injective by
      classical
        rw [← LinearMap.cancel_right (WithLp.linearEquiv 2 𝕜 (_ -> 𝕜)).symm.surjective]
        simp +instances only
        refine LinearMap.pi_ext fun i k => ?_
        have : k = k • (1 : 𝕜) := by rw [smul_eq_mul, mul_one]
        rw [this]; rw [Pi.single_smul]
        replace h := congr_fun h i
        simp only [LinearEquiv.comp_coe, map_smul, LinearEquiv.coe_coe, LinearEquiv.trans_apply,
          coe_symm_linearEquiv, PiLp.toLp_single,
          LinearIsometryEquiv.coe_symm_toLinearEquiv] at h ⊢
        rw [h]

@[simp]
/--
theorem `coe_ofRepr` / 定理 `coe_ofRepr`

English:
theorem coe_ofRepr
  given: [DecidableEq ι] (e : E ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 ι)
  proof: by
  dsimp only [DFunLike.coe]
  funext
  congr!

@[simp]

中文:
定理 coe_ofRepr
  条件: [DecidableEq ι] (e : E ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 ι)
  证明: by
  dsimp only [DFunLike.coe]
  funext
  congr!

@[simp]

Depends on / 依赖: DFunLike, DFunLike.coe
-/
theorem coe_ofRepr [DecidableEq ι] (e : E ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 ι) :
    ⇑(OrthonormalBasis.ofRepr e) = fun i => e.symm (EuclideanSpace.single i (1 : 𝕜)) := by
  dsimp only [DFunLike.coe]
  funext
  congr!

@[simp]
/--
theorem `repr_symm_single` / 定理 `repr_symm_single`

English:
theorem repr_symm_single
  given: [DecidableEq ι] (b : OrthonormalBasis ι 𝕜 E) (i : ι)
  proof: by
  dsimp only [DFunLike.coe]
  congr!

@[simp]

中文:
定理 repr_symm_single
  条件: [DecidableEq ι] (b : 正交标准基 ι 𝕜 E) (i : ι)
  证明: by
  dsimp only [DFunLike.coe]
  congr!

@[simp]
-/
protected theorem repr_symm_single [DecidableEq ι] (b : OrthonormalBasis ι 𝕜 E) (i : ι) :
    b.repr.symm (EuclideanSpace.single i (1 : 𝕜)) = b i := by
  dsimp only [DFunLike.coe]
  congr!

@[simp]
/--
theorem `repr_self` / 定理 `repr_self`

English:
theorem repr_self
  given: [DecidableEq ι] (b : OrthonormalBasis ι 𝕜 E) (i : ι)
  proof: by
  rw [← b.repr_symm_single i]; rw [LinearIsometryEquiv.apply_symm_apply]

中文:
定理 repr_self
  条件: [DecidableEq ι] (b : 正交标准基 ι 𝕜 E) (i : ι)
  证明: by
  rw [← b.repr_symm_single i]; rw [LinearIsometryEquiv.apply_symm_apply]
-/
protected theorem repr_self [DecidableEq ι] (b : OrthonormalBasis ι 𝕜 E) (i : ι) :
    b.repr (b i) = EuclideanSpace.single i (1 : 𝕜) := by
  rw [← b.repr_symm_single i]; rw [LinearIsometryEquiv.apply_symm_apply]

/--
theorem `repr_apply_apply` / 定理 `repr_apply_apply`

English:
theorem repr_apply_apply
  given: (b : OrthonormalBasis ι 𝕜 E) (v : E) (i : ι)
  proof: by
  classical
    rw [← b.repr.inner_map_map (b i) v]; rw [b.repr_self i]; rw [EuclideanSpace.inner_single_left]
    simp only [one_mul, map_one]

@[simp]

中文:
定理 repr_apply_apply
  条件: (b : 正交标准基 ι 𝕜 E) (v : E) (i : ι)
  证明: by
  classical
    rw [← b.repr.inner_map_map (b i) v]; rw [b.repr_self i]; rw [EuclideanSpace.inner_single_left]
    simp only [one_mul, map_one]

@[simp]
-/
protected theorem repr_apply_apply (b : OrthonormalBasis ι 𝕜 E) (v : E) (i : ι) :
    b.repr v i = ⟪b i, v⟫ := by
  classical
    rw [← b.repr.inner_map_map (b i) v]; rw [b.repr_self i]; rw [EuclideanSpace.inner_single_left]
    simp only [one_mul, map_one]

@[simp]
/--
theorem `orthonormal` / 定理 `orthonormal`

English:
theorem orthonormal
  given: (b : OrthonormalBasis ι 𝕜 E)
  statement: Orthonormal 𝕜 b
  proof: by
  classical
    rw [orthonormal_iff_ite]
    intro i j
    rw [← b.repr.inner_map_map (b i) (b j)]; rw [b.repr_self i]; rw [b.repr_self j]; rw [EuclideanSpace.inner_single_left]; rw [PiLp.single_apply]; rw [map_one]; rw [one_mul]

@[simp]

中文:
定理 orthonormal
  条件: (b : 正交标准基 ι 𝕜 E)
  结论: Orthonormal 𝕜 b
  证明: by
  classical
    rw [orthonormal_iff_ite]
    intro i j
    rw [← b.repr.inner_map_map (b i) (b j)]; rw [b.repr_self i]; rw [b.repr_self j]; rw [EuclideanSpace.inner_single_left]; rw [PiLp.single_apply]; rw [map_one]; rw [one_mul]

@[simp]
-/
protected theorem orthonormal (b : OrthonormalBasis ι 𝕜 E) : Orthonormal 𝕜 b := by
  classical
    rw [orthonormal_iff_ite]
    intro i j
    rw [← b.repr.inner_map_map (b i) (b j)]; rw [b.repr_self i]; rw [b.repr_self j]; rw [EuclideanSpace.inner_single_left]; rw [PiLp.single_apply]; rw [map_one]; rw [one_mul]

@[simp]
/--
lemma `norm_eq_one` / 引理 `norm_eq_one`

English:
lemma norm_eq_one
  given: (b : OrthonormalBasis ι 𝕜 E) (i : ι)
  proof: b.orthonormal.norm_eq_one i

@[simp]

中文:
引理 norm_eq_one
  条件: (b : 正交标准基 ι 𝕜 E) (i : ι)
  证明: b.orthonormal.norm_eq_one i

@[simp]

Depends on / 依赖: b.orthonormal.norm_eq_one, norm_eq_one, orthonormal
-/
lemma norm_eq_one (b : OrthonormalBasis ι 𝕜 E) (i : ι) :
    ‖b i‖ = 1 := b.orthonormal.norm_eq_one i

@[simp]
/--
lemma `nnnorm_eq_one` / 引理 `nnnorm_eq_one`

English:
lemma nnnorm_eq_one
  given: (b : OrthonormalBasis ι 𝕜 E) (i : ι)
  proof: b.orthonormal.nnnorm_eq_one i

@[simp]

中文:
引理 nnnorm_eq_one
  条件: (b : 正交标准基 ι 𝕜 E) (i : ι)
  证明: b.orthonormal.nnnorm_eq_one i

@[simp]

Depends on / 依赖: b.orthonormal.nnnorm_eq_one, nnnorm_eq_one, orthonormal
-/
lemma nnnorm_eq_one (b : OrthonormalBasis ι 𝕜 E) (i : ι) :
    ‖b i‖₊ = 1 := b.orthonormal.nnnorm_eq_one i

@[simp]
/--
lemma `enorm_eq_one` / 引理 `enorm_eq_one`

English:
lemma enorm_eq_one
  given: (b : OrthonormalBasis ι 𝕜 E) (i : ι)
  proof: b.orthonormal.enorm_eq_one i

@[simp]

中文:
引理 enorm_eq_one
  条件: (b : 正交标准基 ι 𝕜 E) (i : ι)
  证明: b.orthonormal.enorm_eq_one i

@[simp]

Depends on / 依赖: b.orthonormal.enorm_eq_one, enorm_eq_one, orthonormal
-/
lemma enorm_eq_one (b : OrthonormalBasis ι 𝕜 E) (i : ι) :
    ‖b i‖ₑ = 1 := b.orthonormal.enorm_eq_one i

@[simp]
/--
lemma `inner_eq_zero` / 引理 `inner_eq_zero`

English:
lemma inner_eq_zero
  given: (b : OrthonormalBasis ι 𝕜 E) {i j : ι} (hij : i != j)
  proof: b.orthonormal.inner_eq_zero hij

中文:
引理 inner_eq_zero
  条件: (b : 正交标准基 ι 𝕜 E) {i j : ι} (hij : i != j)
  证明: b.orthonormal.inner_eq_zero hij

Depends on / 依赖: b.orthonormal.inner_eq_zero, inner_eq_zero, orthonormal
-/
lemma inner_eq_zero (b : OrthonormalBasis ι 𝕜 E) {i j : ι} (hij : i != j) :
    ⟪b i, b j⟫ = 0 := b.orthonormal.inner_eq_zero hij

/--
lemma `inner_eq_one` / 引理 `inner_eq_one`

English:
lemma inner_eq_one
  given: (b : OrthonormalBasis ι 𝕜 E) (i : ι)
  statement: ⟪b i, b i⟫ = 1
  proof: by
  simp

中文:
引理 inner_eq_one
  条件: (b : 正交标准基 ι 𝕜 E) (i : ι)
  结论: ⟪b i, b i⟫ = 1
  证明: by
  simp
-/
lemma inner_eq_one (b : OrthonormalBasis ι 𝕜 E) (i : ι) : ⟪b i, b i⟫ = 1 := by
  simp

/--
lemma `inner_eq_ite` / 引理 `inner_eq_ite`

English:
lemma inner_eq_ite
  given: [DecidableEq ι] (b : OrthonormalBasis ι 𝕜 E) (i j : ι)
  proof: by
  by_cases h : i = j <;> simp [h]

中文:
引理 inner_eq_ite
  条件: [DecidableEq ι] (b : 正交标准基 ι 𝕜 E) (i j : ι)
  证明: by
  by_cases h : i = j <;> simp [h]
-/
lemma inner_eq_ite [DecidableEq ι] (b : OrthonormalBasis ι 𝕜 E) (i j : ι) :
    ⟪b i, b j⟫ = if i = j then 1 else 0 := by
  by_cases h : i = j <;> simp [h]

/--
Definition of `toBasis` / `toBasis` 的定义

English:
definition toBasis
  signature: (b : OrthonormalBasis ι 𝕜 E)
  body: Basis.ofEquivFun (b.repr.toLinearEquiv.trans (WithLp.linearEquiv 2 𝕜 (ι -> 𝕜)))

@[simp]

中文:
定义 toBasis
  签名: (b : 正交标准基 ι 𝕜 E)
  定义体: Basis.ofEquivFun (b.repr.toLinearEquiv.trans (WithLp.linearEquiv 2 𝕜 (ι -> 𝕜)))

@[simp]
-/
protected def toBasis (b : OrthonormalBasis ι 𝕜 E) : Basis ι 𝕜 E :=
  Basis.ofEquivFun (b.repr.toLinearEquiv.trans (WithLp.linearEquiv 2 𝕜 (ι -> 𝕜)))

@[simp]
/--
theorem `coe_toBasis` / 定理 `coe_toBasis`

English:
theorem coe_toBasis
  given: (b : OrthonormalBasis ι 𝕜 E)
  statement: (⇑b.toBasis : ι -> E) = ⇑b
  proof: rfl

@[simp]

中文:
定理 coe_toBasis
  条件: (b : 正交标准基 ι 𝕜 E)
  结论: (⇑b.toBasis : ι -> E) = ⇑b
  证明: rfl

@[simp]
-/
protected theorem coe_toBasis (b : OrthonormalBasis ι 𝕜 E) : (⇑b.toBasis : ι -> E) = ⇑b := rfl

@[simp]
/--
theorem `coe_toBasis_repr` / 定理 `coe_toBasis_repr`

English:
theorem coe_toBasis_repr
  given: (b : OrthonormalBasis ι 𝕜 E)
  proof: Basis.equivFun_ofEquivFun _

@[simp]

中文:
定理 coe_toBasis_repr
  条件: (b : 正交标准基 ι 𝕜 E)
  证明: Basis.equivFun_ofEquivFun _

@[simp]
-/
protected theorem coe_toBasis_repr (b : OrthonormalBasis ι 𝕜 E) :
    b.toBasis.equivFun = b.repr.toLinearEquiv.trans (WithLp.linearEquiv 2 𝕜 (ι -> 𝕜)) :=
  Basis.equivFun_ofEquivFun _

@[simp]
/--
theorem `coe_toBasis_repr_apply` / 定理 `coe_toBasis_repr_apply`

English:
theorem coe_toBasis_repr_apply
  given: (b : OrthonormalBasis ι 𝕜 E) (x : E) (i : ι)
  proof: by
  simp [← Basis.equivFun_apply]

中文:
定理 coe_toBasis_repr_apply
  条件: (b : 正交标准基 ι 𝕜 E) (x : E) (i : ι)
  证明: by
  simp [← Basis.equivFun_apply]
-/
protected theorem coe_toBasis_repr_apply (b : OrthonormalBasis ι 𝕜 E) (x : E) (i : ι) :
    b.toBasis.repr x i = b.repr x i := by
  simp [← Basis.equivFun_apply]

/--
theorem `sum_repr` / 定理 `sum_repr`

English:
theorem sum_repr
  given: (b : OrthonormalBasis ι 𝕜 E) (x : E)
  statement: ∑ i, b.repr x i • b i = x
  proof: by
  simp_rw [← b.coe_toBasis_repr_apply, ← b.coe_toBasis]
  exact b.toBasis.sum_repr x

中文:
定理 sum_repr
  条件: (b : 正交标准基 ι 𝕜 E) (x : E)
  结论: ∑ i, b.repr x i • b i = x
  证明: by
  simp_rw [← b.coe_toBasis_repr_apply, ← b.coe_toBasis]
  exact b.toBasis.sum_repr x
-/
protected theorem sum_repr (b : OrthonormalBasis ι 𝕜 E) (x : E) : ∑ i, b.repr x i • b i = x := by
  simp_rw [← b.coe_toBasis_repr_apply, ← b.coe_toBasis]
  exact b.toBasis.sum_repr x

open scoped InnerProductSpace in
/--
theorem `sum_repr'` / 定理 `sum_repr'`

English:
theorem sum_repr'
  given: (b : OrthonormalBasis ι 𝕜 E) (x : E)
  statement: ∑ i, ⟪b i, x⟫_𝕜 • b i = x
  proof: by
  nth_rw 2 [← (b.sum_repr x)]
  simp_rw [b.repr_apply_apply x]

中文:
定理 sum_repr'
  条件: (b : 正交标准基 ι 𝕜 E) (x : E)
  结论: ∑ i, ⟪b i, x⟫_𝕜 • b i = x
  证明: by
  nth_rw 2 [← (b.sum_repr x)]
  simp_rw [b.repr_apply_apply x]
-/
protected theorem sum_repr' (b : OrthonormalBasis ι 𝕜 E) (x : E) : ∑ i, ⟪b i, x⟫_𝕜 • b i = x := by
  nth_rw 2 [← (b.sum_repr x)]
  simp_rw [b.repr_apply_apply x]

/--
theorem `sum_repr_symm` / 定理 `sum_repr_symm`

English:
theorem sum_repr_symm
  given: (b : OrthonormalBasis ι 𝕜 E) (v : EuclideanSpace 𝕜 ι)
  proof: by simpa using (b.toBasis.equivFun_symm_apply v).symm

中文:
定理 sum_repr_symm
  条件: (b : 正交标准基 ι 𝕜 E) (v : EuclideanSpace 𝕜 ι)
  证明: by simpa using (b.toBasis.equivFun_symm_apply v).symm
-/
protected theorem sum_repr_symm (b : OrthonormalBasis ι 𝕜 E) (v : EuclideanSpace 𝕜 ι) :
    ∑ i, v i • b i = b.repr.symm v := by simpa using (b.toBasis.equivFun_symm_apply v).symm

/--
theorem `sum_inner_mul_inner` / 定理 `sum_inner_mul_inner`

English:
theorem sum_inner_mul_inner
  given: (b : OrthonormalBasis ι 𝕜 E) (x y : E)
  proof: by
  have := congr_arg (innerSL 𝕜 x) (b.sum_repr y)
  rw [map_sum] at this
  convert! this
  rw [map_smul]; rw [b.repr_apply_apply]; rw [mul_comm]
  simp

中文:
定理 sum_inner_mul_inner
  条件: (b : 正交标准基 ι 𝕜 E) (x y : E)
  证明: by
  have := congr_arg (innerSL 𝕜 x) (b.sum_repr y)
  rw [map_sum] at this
  convert! this
  rw [map_smul]; rw [b.repr_apply_apply]; rw [mul_comm]
  simp
-/
protected theorem sum_inner_mul_inner (b : OrthonormalBasis ι 𝕜 E) (x y : E) :
    ∑ i, ⟪x, b i⟫ * ⟪b i, y⟫ = ⟪x, y⟫ := by
  have := congr_arg (innerSL 𝕜 x) (b.sum_repr y)
  rw [map_sum] at this
  convert! this
  rw [map_smul]; rw [b.repr_apply_apply]; rw [mul_comm]
  simp

/--
lemma `sum_sq_norm_inner_right` / 引理 `sum_sq_norm_inner_right`

English:
lemma sum_sq_norm_inner_right
  given: (b : OrthonormalBasis ι 𝕜 E) (x : E)
  proof: by
  rw [@norm_eq_sqrt_re_inner 𝕜]; rw [← OrthonormalBasis.sum_inner_mul_inner b x x]; rw [map_sum]
  simp_rw [inner_mul_symm_re_eq_norm, norm_mul, ← inner_conj_symm x, starRingEnd_apply,
    norm_star, ← pow_two]
  rw [Real.sq_sqrt]
  exact Fintype.sum_nonneg fun _ => by positivity

中文:
引理 sum_sq_norm_inner_right
  条件: (b : 正交标准基 ι 𝕜 E) (x : E)
  证明: by
  rw [@norm_eq_sqrt_re_inner 𝕜]; rw [← OrthonormalBasis.sum_inner_mul_inner b x x]; rw [map_sum]
  simp_rw [inner_mul_symm_re_eq_norm, norm_mul, ← inner_conj_symm x, starRingEnd_apply,
    norm_star, ← pow_two]
  rw [Real.sq_sqrt]
  exact Fintype.sum_nonneg fun _ => by positivity

Depends on / 依赖: Fintype, Fintype.sum_nonneg, OrthonormalBasis, OrthonormalBasis.sum_inner_mul_inner, Real.sq_sqrt, inner_conj_symm, inner_mul_symm_re_eq_norm, map_sum, norm_eq_sqrt_re_inner, norm_mul, norm_star, pow_two, simp_rw, sq_sqrt, starRingEnd_apply, sum_inner_mul_inner, sum_nonneg
-/
lemma sum_sq_norm_inner_right (b : OrthonormalBasis ι 𝕜 E) (x : E) :
    ∑ i, ‖⟪b i, x⟫‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [@norm_eq_sqrt_re_inner 𝕜]; rw [← OrthonormalBasis.sum_inner_mul_inner b x x]; rw [map_sum]
  simp_rw [inner_mul_symm_re_eq_norm, norm_mul, ← inner_conj_symm x, starRingEnd_apply,
    norm_star, ← pow_two]
  rw [Real.sq_sqrt]
  exact Fintype.sum_nonneg fun _ => by positivity

/--
lemma `sum_sq_norm_inner_left` / 引理 `sum_sq_norm_inner_left`

English:
lemma sum_sq_norm_inner_left
  given: (b : OrthonormalBasis ι 𝕜 E) (x : E)
  proof: by
  convert! sum_sq_norm_inner_right b x using 2 with i -
  rw [← inner_conj_symm]; rw [RCLike.norm_conj]

中文:
引理 sum_sq_norm_inner_left
  条件: (b : 正交标准基 ι 𝕜 E) (x : E)
  证明: by
  convert! sum_sq_norm_inner_right b x using 2 with i -
  rw [← inner_conj_symm]; rw [RCLike.norm_conj]

Depends on / 依赖: RCLike, RCLike.norm_conj, convert, inner_conj_symm, norm_conj, sum_sq_norm_inner_right
-/
lemma sum_sq_norm_inner_left (b : OrthonormalBasis ι 𝕜 E) (x : E) :
    ∑ i, ‖⟪x, b i⟫‖ ^ 2 = ‖x‖ ^ 2 := by
  convert! sum_sq_norm_inner_right b x using 2 with i -
  rw [← inner_conj_symm]; rw [RCLike.norm_conj]

open scoped RealInnerProductSpace in
/--
theorem `sum_sq_inner_right` / 定理 `sum_sq_inner_right`

English:
theorem sum_sq_inner_right
  statement: {E : Type*} [NormedAddCommGroup E]
  proof: by
  rw [← b.sum_sq_norm_inner_right]
  simp

中文:
定理 sum_sq_inner_right
  结论: {E : 类型} [赋范交换加群 E]
  证明: by
  rw [← b.sum_sq_norm_inner_right]
  simp

Depends on / 依赖: b.sum_sq_norm_inner_right, sum_sq_norm_inner_right
-/
theorem sum_sq_inner_right {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace Real E] (b : OrthonormalBasis ι Real E) (x : E) :
    ∑ i : ι, ⟪b i, x⟫ ^ 2 = ‖x‖ ^ 2 := by
  rw [← b.sum_sq_norm_inner_right]
  simp

open scoped RealInnerProductSpace in
/--
theorem `sum_sq_inner_left` / 定理 `sum_sq_inner_left`

English:
theorem sum_sq_inner_left
  statement: {ι E : Type*} [NormedAddCommGroup E]
  proof: by
  simp_rw [← b.sum_sq_inner_right, real_inner_comm]

中文:
定理 sum_sq_inner_left
  结论: {ι E : 类型} [赋范交换加群 E]
  证明: by
  simp_rw [← b.sum_sq_inner_right, real_inner_comm]

Depends on / 依赖: b.sum_sq_inner_right, real_inner_comm, simp_rw, sum_sq_inner_right
-/
theorem sum_sq_inner_left {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace Real E] [Fintype ι] (b : OrthonormalBasis ι Real E) (x : E) :
    ∑ i : ι, ⟪x, b i⟫ ^ 2 = ‖x‖ ^ 2 := by
  simp_rw [← b.sum_sq_inner_right, real_inner_comm]

/--
lemma `norm_le_card_mul_iSup_norm_inner` / 引理 `norm_le_card_mul_iSup_norm_inner`

English:
lemma norm_le_card_mul_iSup_norm_inner
  given: (b : OrthonormalBasis ι 𝕜 E) (x : E)
  proof: by
  calc ‖x‖
  _ = √(∑ i, ‖⟪b i, x⟫‖ ^ 2) := by rw [sum_sq_norm_inner_right, Real.sqrt_sq (by positivity)]
  _ <= √(∑ _ : ι, (⨆ j, ‖⟪b j, x⟫‖) ^ 2) := by
    gcongr with i
    exact le_ciSup (f := fun j => ‖⟪b j, x⟫‖) (by simp) i
  _ = √(Fintype.card ι) * ⨆ i, ‖⟪b i, x⟫‖ := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_nonneg, Real.sqrt_mul]
    congr
    rw [Real.sqrt_sq]
    cases isEmpty_or_nonempty ι
    · simp
    · exact le_ciSup_of_le (by simp) (Nonempty.some inferInstance) (by positivity)

中文:
引理 norm_le_card_mul_iSup_norm_inner
  条件: (b : 正交标准基 ι 𝕜 E) (x : E)
  证明: by
  calc ‖x‖
  _ = √(∑ i, ‖⟪b i, x⟫‖ ^ 2) := by rw [sum_sq_norm_inner_right, Real.sqrt_sq (by positivity)]
  _ <= √(∑ _ : ι, (⨆ j, ‖⟪b j, x⟫‖) ^ 2) := by
    gcongr with i
    exact le_ciSup (f := fun j => ‖⟪b j, x⟫‖) (by simp) i
  _ = √(Fintype.card ι) * ⨆ i, ‖⟪b i, x⟫‖ := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_nonneg, Real.sqrt_mul]
    congr
    rw [Real.sqrt_sq]
    cases isEmpty_or_nonempty ι
    · simp
    · exact le_ciSup_of_le (by simp) (Nonempty.some inferInstance) (by positivity)

Depends on / 依赖: Finset, Finset.card_univ, Finset.sum_const, Fintype, Fintype.card, Nat.cast_nonneg, Nonempty, Nonempty.some, Real.sqrt_mul, Real.sqrt_sq, card_univ, cast_nonneg, isEmpty_or_nonempty, le_ciSup, le_ciSup_of_le, nsmul_eq_mul, sqrt_mul, sqrt_sq, sum_const, sum_sq_norm_inner_right
-/
lemma norm_le_card_mul_iSup_norm_inner (b : OrthonormalBasis ι 𝕜 E) (x : E) :
    ‖x‖ <= √(Fintype.card ι) * ⨆ i, ‖⟪b i, x⟫‖ := by
  calc ‖x‖
  _ = √(∑ i, ‖⟪b i, x⟫‖ ^ 2) := by rw [sum_sq_norm_inner_right, Real.sqrt_sq (by positivity)]
  _ <= √(∑ _ : ι, (⨆ j, ‖⟪b j, x⟫‖) ^ 2) := by
    gcongr with i
    exact le_ciSup (f := fun j => ‖⟪b j, x⟫‖) (by simp) i
  _ = √(Fintype.card ι) * ⨆ i, ‖⟪b i, x⟫‖ := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_nonneg, Real.sqrt_mul]
    congr
    rw [Real.sqrt_sq]
    cases isEmpty_or_nonempty ι
    · simp
    · exact le_ciSup_of_le (by simp) (Nonempty.some inferInstance) (by positivity)

/--
theorem `orthogonalProjectionOnto_apply_eq_sum` / 定理 `orthogonalProjectionOnto_apply_eq_sum`

English:
theorem orthogonalProjectionOnto_apply_eq_sum
  statement: {U : Submodule 𝕜 E}
  proof: by
  simpa only [b.repr_apply_apply, inner_orthogonalProjectionOnto_eq_of_mem_left] using
    (b.sum_repr (U.orthogonalProjectionOnto x)).symm

@[deprecated (since := "2026-05-05")] alias orthogonalProjection_apply_eq_sum :=
  OrthonormalBasis.orthogonalProjectionOnto_apply_eq_sum

中文:
定理 orthogonalProjectionOnto_apply_eq_sum
  结论: {U : 子模 𝕜 E}
  证明: by
  simpa only [b.repr_apply_apply, inner_orthogonalProjectionOnto_eq_of_mem_left] using
    (b.sum_repr (U.orthogonalProjectionOnto x)).symm

@[deprecated (since := "2026-05-05")] alias orthogonalProjection_apply_eq_sum :=
  OrthonormalBasis.orthogonalProjectionOnto_apply_eq_sum
-/
protected theorem orthogonalProjectionOnto_apply_eq_sum {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (b : OrthonormalBasis ι 𝕜 U) (x : E) :
    U.orthogonalProjectionOnto x = ∑ i, ⟪(b i : E), x⟫ • b i := by
  simpa only [b.repr_apply_apply, inner_orthogonalProjectionOnto_eq_of_mem_left] using
    (b.sum_repr (U.orthogonalProjectionOnto x)).symm

@[deprecated (since := "2026-05-05")] alias orthogonalProjection_apply_eq_sum :=
  OrthonormalBasis.orthogonalProjectionOnto_apply_eq_sum

/--
theorem `orthogonalProjectionOnto_eq_sum_rankOne` / 定理 `orthogonalProjectionOnto_eq_sum_rankOne`

English:
theorem orthogonalProjectionOnto_eq_sum_rankOne
  statement: {U : Submodule 𝕜 E}
  proof: by
  ext; simp [b.orthogonalProjectionOnto_apply_eq_sum]

@[deprecated (since := "2026-05-05")] alias orthogonalProjection_eq_sum_rankOne :=
  OrthonormalBasis.orthogonalProjectionOnto_eq_sum_rankOne

中文:
定理 orthogonalProjectionOnto_eq_sum_rankOne
  结论: {U : 子模 𝕜 E}
  证明: by
  ext; simp [b.orthogonalProjectionOnto_apply_eq_sum]

@[deprecated (since := "2026-05-05")] alias orthogonalProjection_eq_sum_rankOne :=
  OrthonormalBasis.orthogonalProjectionOnto_eq_sum_rankOne
-/
protected theorem orthogonalProjectionOnto_eq_sum_rankOne {U : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] (b : OrthonormalBasis ι 𝕜 U) :
    U.orthogonalProjectionOnto = ∑ i, InnerProductSpace.rankOne 𝕜 (b i) (b i : E) := by
  ext; simp [b.orthogonalProjectionOnto_apply_eq_sum]

@[deprecated (since := "2026-05-05")] alias orthogonalProjection_eq_sum_rankOne :=
  OrthonormalBasis.orthogonalProjectionOnto_eq_sum_rankOne

/--
theorem `starProjection_eq_sum_rankOne` / 定理 `starProjection_eq_sum_rankOne`

English:
theorem starProjection_eq_sum_rankOne
  statement: {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
  proof: by
  ext; simp [starProjection, b.orthogonalProjectionOnto_eq_sum_rankOne]

中文:
定理 starProjection_eq_sum_rankOne
  结论: {U : 子模 𝕜 E} [U.有OrthogonalProjection]
  证明: by
  ext; simp [starProjection, b.orthogonalProjectionOnto_eq_sum_rankOne]
-/
protected theorem starProjection_eq_sum_rankOne {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (b : OrthonormalBasis ι 𝕜 U) :
    U.starProjection = ∑ i, InnerProductSpace.rankOne 𝕜 (b i : E) (b i : E) := by
  ext; simp [starProjection, b.orthogonalProjectionOnto_eq_sum_rankOne]

/--
lemma `sum_rankOne_eq_id` / 引理 `sum_rankOne_eq_id`

English:
lemma sum_rankOne_eq_id
  given: (b : OrthonormalBasis ι 𝕜 E)
  proof: by ext; simp [b.sum_repr']

中文:
引理 sum_rankOne_eq_id
  条件: (b : 正交标准基 ι 𝕜 E)
  证明: by ext; simp [b.sum_repr']

Depends on / 依赖: b.sum_repr, sum_repr
-/
lemma sum_rankOne_eq_id (b : OrthonormalBasis ι 𝕜 E) :
    ∑ i, InnerProductSpace.rankOne 𝕜 (b i) (b i) = .id 𝕜 E := by ext; simp [b.sum_repr']

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  body: L.symm.trans b.repr

@[simp]

中文:
定义 map
  签名: {G : 类型} [赋范交换加群 G] [内积空间 𝕜 G]
  定义体: L.symm.trans b.repr

@[simp]
-/
protected def map {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    (b : OrthonormalBasis ι 𝕜 E) (L : E ≃ₗᵢ[𝕜] G) : OrthonormalBasis ι 𝕜 G where
  repr := L.symm.trans b.repr

@[simp]
/--
theorem `map_apply` / 定理 `map_apply`

English:
theorem map_apply
  statement: {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  proof: rfl

中文:
定理 map_apply
  结论: {G : 类型} [赋范交换加群 G] [内积空间 𝕜 G]
  证明: rfl
-/
protected theorem map_apply {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    (b : OrthonormalBasis ι 𝕜 E) (L : E ≃ₗᵢ[𝕜] G) (i : ι) : b.map L i = L (b i) :=
  rfl

/--
lemma `coe_map` / 引理 `coe_map`

English:
lemma coe_map
  statement: {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  proof: rfl

@[simp]

中文:
引理 coe_map
  结论: {G : 类型} [赋范交换加群 G] [内积空间 𝕜 G]
  证明: rfl

@[simp]
-/
lemma coe_map {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    (b : OrthonormalBasis ι 𝕜 E) (L : E ≃ₗᵢ[𝕜] G) : ⇑(b.map L) = L ∘ b := rfl

@[simp]
/--
theorem `toBasis_map` / 定理 `toBasis_map`

English:
theorem toBasis_map
  statement: {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  proof: rfl

中文:
定理 toBasis_map
  结论: {G : 类型} [赋范交换加群 G] [内积空间 𝕜 G]
  证明: rfl
-/
protected theorem toBasis_map {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    (b : OrthonormalBasis ι 𝕜 E) (L : E ≃ₗᵢ[𝕜] G) :
    (b.map L).toBasis = b.toBasis.map L.toLinearEquiv :=
  rfl

/--
Definition of `_root_.Module.Basis.toOrthonormalBasis` / `_root_.Module.Basis.toOrthonormalBasis` 的定义

English:
definition _root_.Module.Basis.toOrthonormalBasis
  signature: (v : Basis ι 𝕜 E) (hv : Orthonormal 𝕜 v)
  body: OrthonormalBasis.ofRepr
    LinearEquiv.isometryOfInner (v.equivFun.trans (WithLp.linearEquiv 2 𝕜 (ι -> 𝕜)).symm)
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

中文:
定义 _root_.模.基.toOrthonormalBasis
  签名: (v : 基 ι 𝕜 E) (hv : Orthonormal 𝕜 v)
  定义体: OrthonormalBasis.ofRepr
    LinearEquiv.isometryOfInner (v.equivFun.trans (WithLp.linearEquiv 2 𝕜 (ι -> 𝕜)).symm)
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

Depends on / 依赖: EuclideanSpace, LinearEquiv, LinearEquiv.isometryOfInner, OrthonormalBasis, OrthonormalBasis.ofRepr, PiLp.inner_apply, WithLp, WithLp.linearEquiv, convert, equivFun, equivFun_symm_apply, hv.inner_left_fintype, inner_apply, inner_left_fintype, inner_smul_right, inner_sum, isometryOfInner, linearEquiv, ofRepr, symm_apply_apply
-/
def _root_.Module.Basis.toOrthonormalBasis (v : Basis ι 𝕜 E) (hv : Orthonormal 𝕜 v) :
    OrthonormalBasis ι 𝕜 E :=
OrthonormalBasis.ofRepr
    LinearEquiv.isometryOfInner (v.equivFun.trans (WithLp.linearEquiv 2 𝕜 (ι -> 𝕜)).symm)
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
/--
theorem `_root_.Module.Basis.coe_toOrthonormalBasis_repr` / 定理 `_root_.Module.Basis.coe_toOrthonormalBasis_repr`

English:
theorem _root_.Module.Basis.coe_toOrthonormalBasis_repr
  given: (v : Basis ι 𝕜 E) (hv : Orthonormal 𝕜 v)
  proof: rfl

@[simp]

中文:
定理 _root_.模.基.coe_toOrthonormalBasis_repr
  条件: (v : 基 ι 𝕜 E) (hv : Orthonormal 𝕜 v)
  证明: rfl

@[simp]
-/
theorem _root_.Module.Basis.coe_toOrthonormalBasis_repr (v : Basis ι 𝕜 E) (hv : Orthonormal 𝕜 v) :
    ((v.toOrthonormalBasis hv).repr : E -> EuclideanSpace 𝕜 ι) =
    v.equivFun.trans (WithLp.linearEquiv 2 𝕜 (ι -> 𝕜)).symm :=
  rfl

@[simp]
/--
theorem `_root_.Module.Basis.coe_toOrthonormalBasis_repr_symm` / 定理 `_root_.Module.Basis.coe_toOrthonormalBasis_repr_symm`

English:
theorem _root_.Module.Basis.coe_toOrthonormalBasis_repr_symm
  proof: rfl

@[simp]

中文:
定理 _root_.模.基.coe_toOrthonormalBasis_repr_symm
  证明: rfl

@[simp]
-/
theorem _root_.Module.Basis.coe_toOrthonormalBasis_repr_symm
    (v : Basis ι 𝕜 E) (hv : Orthonormal 𝕜 v) :
    ((v.toOrthonormalBasis hv).repr.symm : EuclideanSpace 𝕜 ι -> E) =
    (WithLp.linearEquiv 2 𝕜 (ι -> 𝕜)).trans v.equivFun.symm :=
  rfl

@[simp]
/--
theorem `_root_.Module.Basis.toBasis_toOrthonormalBasis` / 定理 `_root_.Module.Basis.toBasis_toOrthonormalBasis`

English:
theorem _root_.Module.Basis.toBasis_toOrthonormalBasis
  given: (v : Basis ι 𝕜 E) (hv : Orthonormal 𝕜 v)
  proof: by
  simp only [OrthonormalBasis.toBasis, Basis.toOrthonormalBasis,
    LinearEquiv.isometryOfInner_toLinearEquiv]
  exact v.ofEquivFun_equivFun

@[simp]

中文:
定理 _root_.模.基.toBasis_toOrthonormalBasis
  条件: (v : 基 ι 𝕜 E) (hv : Orthonormal 𝕜 v)
  证明: by
  simp only [OrthonormalBasis.toBasis, Basis.toOrthonormalBasis,
    LinearEquiv.isometryOfInner_toLinearEquiv]
  exact v.ofEquivFun_equivFun

@[simp]

Depends on / 依赖: Basis.toOrthonormalBasis, LinearEquiv, LinearEquiv.isometryOfInner_toLinearEquiv, OrthonormalBasis, OrthonormalBasis.toBasis, isometryOfInner_toLinearEquiv, ofEquivFun_equivFun, toBasis, toOrthonormalBasis, v.ofEquivFun_equivFun
-/
theorem _root_.Module.Basis.toBasis_toOrthonormalBasis (v : Basis ι 𝕜 E) (hv : Orthonormal 𝕜 v) :
    (v.toOrthonormalBasis hv).toBasis = v := by
  simp only [OrthonormalBasis.toBasis, Basis.toOrthonormalBasis,
    LinearEquiv.isometryOfInner_toLinearEquiv]
  exact v.ofEquivFun_equivFun

@[simp]
/--
theorem `_root_.Module.Basis.coe_toOrthonormalBasis` / 定理 `_root_.Module.Basis.coe_toOrthonormalBasis`

English:
theorem _root_.Module.Basis.coe_toOrthonormalBasis
  given: (v : Basis ι 𝕜 E) (hv : Orthonormal 𝕜 v)
  proof: calc
    (v.toOrthonormalBasis hv : ι -> E) = ((v.toOrthonormalBasis hv).toBasis : ι -> E) := by
      rw [OrthonormalBasis.coe_toBasis]
    _ = (v : ι -> E) := by simp

中文:
定理 _root_.模.基.coe_toOrthonormalBasis
  条件: (v : 基 ι 𝕜 E) (hv : Orthonormal 𝕜 v)
  证明: calc
    (v.toOrthonormalBasis hv : ι -> E) = ((v.toOrthonormalBasis hv).toBasis : ι -> E) := by
      rw [OrthonormalBasis.coe_toBasis]
    _ = (v : ι -> E) := by simp

Depends on / 依赖: OrthonormalBasis, OrthonormalBasis.coe_toBasis, coe_toBasis, toBasis, toOrthonormalBasis, v.toOrthonormalBasis
-/
theorem _root_.Module.Basis.coe_toOrthonormalBasis (v : Basis ι 𝕜 E) (hv : Orthonormal 𝕜 v) :
    (v.toOrthonormalBasis hv : ι -> E) = (v : ι -> E) :=
  calc
    (v.toOrthonormalBasis hv : ι -> E) = ((v.toOrthonormalBasis hv).toBasis : ι -> E) := by
      rw [OrthonormalBasis.coe_toBasis]
    _ = (v : ι -> E) := by simp

section Singleton
variable {ι 𝕜 : Type*} [Unique ι] [RCLike 𝕜]

variable (ι 𝕜) in
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def singleton
  body: (Basis.singleton ι 𝕜).toOrthonormalBasis (by simp)

@[simp]

中文:
定义 noncomputable
  签名: def singleton
  定义体: (Basis.singleton ι 𝕜).toOrthonormalBasis (by simp)

@[simp]
-/
protected noncomputable def singleton : OrthonormalBasis ι 𝕜 𝕜 :=
  (Basis.singleton ι 𝕜).toOrthonormalBasis (by simp)

@[simp]
/--
theorem `singleton_apply` / 定理 `singleton_apply`

English:
theorem singleton_apply
  given: (i)
  statement: OrthonormalBasis.singleton ι 𝕜 i = 1
  proof: Basis.singleton_apply _ _ _

@[simp]

中文:
定理 singleton_apply
  条件: (i)
  结论: 正交标准基.singleton ι 𝕜 i = 1
  证明: Basis.singleton_apply _ _ _

@[simp]

Depends on / 依赖: Basis.singleton_apply, singleton_apply
-/
theorem singleton_apply (i) : OrthonormalBasis.singleton ι 𝕜 i = 1 := Basis.singleton_apply _ _ _

@[simp]
/--
theorem `singleton_repr` / 定理 `singleton_repr`

English:
theorem singleton_repr
  given: (x i)
  statement: (OrthonormalBasis.singleton ι 𝕜).repr x i = x
  proof: Basis.singleton_repr _ _ _ _

@[simp]

中文:
定理 singleton_repr
  条件: (x i)
  结论: (正交标准基.singleton ι 𝕜).repr x i = x
  证明: Basis.singleton_repr _ _ _ _

@[simp]

Depends on / 依赖: Basis.singleton_repr, singleton_repr
-/
theorem singleton_repr (x i) : (OrthonormalBasis.singleton ι 𝕜).repr x i = x :=
  Basis.singleton_repr _ _ _ _

@[simp]
/--
theorem `coe_singleton` / 定理 `coe_singleton`

English:
theorem coe_singleton
  statement: ⇑(OrthonormalBasis.singleton ι 𝕜) = 1
  proof: by
  ext; simp

@[simp]

中文:
定理 coe_singleton
  结论: ⇑(正交标准基.singleton ι 𝕜) = 1
  证明: by
  ext; simp

@[simp]
-/
theorem coe_singleton : ⇑(OrthonormalBasis.singleton ι 𝕜) = 1 := by
  ext; simp

@[simp]
/--
theorem `toBasis_singleton` / 定理 `toBasis_singleton`

English:
theorem toBasis_singleton
  statement: (OrthonormalBasis.singleton ι 𝕜).toBasis = Basis.singleton ι 𝕜
  proof: Basis.toBasis_toOrthonormalBasis _ _

中文:
定理 toBasis_singleton
  结论: (正交标准基.singleton ι 𝕜).toBasis = 基.singleton ι 𝕜
  证明: Basis.toBasis_toOrthonormalBasis _ _

Depends on / 依赖: Basis.toBasis_toOrthonormalBasis, toBasis_toOrthonormalBasis
-/
theorem toBasis_singleton : (OrthonormalBasis.singleton ι 𝕜).toBasis = Basis.singleton ι 𝕜 :=
  Basis.toBasis_toOrthonormalBasis _ _

end Singleton

/--
Definition of `_root_.Pi.orthonormalBasis` / `_root_.Pi.orthonormalBasis` 的定义

English:
definition _root_.Pi.orthonormalBasis
  signature: {η : Type*} [Fintype η] {ι : η -> Type*}
  body: .trans
      (.piLpCongrRight 2 fun i => (B i).repr)
      (.symm <| .piLpCurry 𝕜 2 fun _ _ => 𝕜)

中文:
定义 _root_.依赖函数类型.orthonormalBasis
  签名: {η : 类型} [有限类型 η] {ι : η -> 类型}
  定义体: .trans
      (.piLpCongrRight 2 fun i => (B i).repr)
      (.symm <| .piLpCurry 𝕜 2 fun _ _ => 𝕜)
-/
protected def _root_.Pi.orthonormalBasis {η : Type*} [Fintype η] {ι : η -> Type*}
    [forall i, Fintype (ι i)] {𝕜 : Type*} [RCLike 𝕜] {E : η -> Type*} [forall i, NormedAddCommGroup (E i)]
    [forall i, InnerProductSpace 𝕜 (E i)] (B : forall i, OrthonormalBasis (ι i) 𝕜 (E i)) :
    OrthonormalBasis ((i : η) × ι i) 𝕜 (PiLp 2 E) where
  repr := .trans
      (.piLpCongrRight 2 fun i => (B i).repr)
      (.symm <| .piLpCurry 𝕜 2 fun _ _ => 𝕜)

/--
theorem `_root_.Pi.orthonormalBasis.toBasis` / 定理 `_root_.Pi.orthonormalBasis.toBasis`

English:
theorem _root_.Pi.orthonormalBasis.toBasis
  statement: {η : Type*} [Fintype η] {ι : η -> Type*}
  proof: by ext; rfl

@[simp]

中文:
定理 _root_.依赖函数类型.orthonormalBasis.toBasis
  结论: {η : 类型} [有限类型 η] {ι : η -> 类型}
  证明: by ext; rfl

@[simp]
-/
theorem _root_.Pi.orthonormalBasis.toBasis {η : Type*} [Fintype η] {ι : η -> Type*}
    [forall i, Fintype (ι i)] {𝕜 : Type*} [RCLike 𝕜] {E : η -> Type*} [forall i, NormedAddCommGroup (E i)]
    [forall i, InnerProductSpace 𝕜 (E i)] (B : forall i, OrthonormalBasis (ι i) 𝕜 (E i)) :
    (Pi.orthonormalBasis B).toBasis =
      ((Pi.basis fun i : η => (B i).toBasis).map (WithLp.linearEquiv 2 _ _).symm) := by ext; rfl

@[simp]
/--
theorem `_root_.Pi.orthonormalBasis_apply` / 定理 `_root_.Pi.orthonormalBasis_apply`

English:
theorem _root_.Pi.orthonormalBasis_apply
  statement: {η : Type*} [Fintype η] [DecidableEq η] {ι : η -> Type*}
  proof: by
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

中文:
定理 _root_.依赖函数类型.orthonormalBasis_apply
  结论: {η : 类型} [有限类型 η] [DecidableEq η] {ι : η -> 类型}
  证明: by
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

Depends on / 依赖: Decidable, Decidable.eq_or_ne, LinearIsometryEquiv, LinearIsometryEquiv.piLpCongrRight_apply, LinearIsometryEquiv.piLpCongrRight_symm, LinearIsometryEquiv.piLpCurry_apply, LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.symm_trans, LinearIsometryEquiv.trans_apply, Pi.orthonormalBasis, PiLp.ofLp_single, PiLp.toLp_apply, Sigma.curry_single, classical, coe_ofRepr, curry_single, eq_or_ne, ofLp_single, orthonormalBasis, piLpCongrRight_apply
-/
theorem _root_.Pi.orthonormalBasis_apply {η : Type*} [Fintype η] [DecidableEq η] {ι : η -> Type*}
    [forall i, Fintype (ι i)] {𝕜 : Type*} [RCLike 𝕜] {E : η -> Type*} [forall i, NormedAddCommGroup (E i)]
    [forall i, InnerProductSpace 𝕜 (E i)] (B : forall i, OrthonormalBasis (ι i) 𝕜 (E i))
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
/--
theorem `_root_.Pi.orthonormalBasis_repr` / 定理 `_root_.Pi.orthonormalBasis_repr`

English:
theorem _root_.Pi.orthonormalBasis_repr
  statement: {η : Type*} [Fintype η] {ι : η -> Type*}
  proof: rfl

中文:
定理 _root_.依赖函数类型.orthonormalBasis_repr
  结论: {η : 类型} [有限类型 η] {ι : η -> 类型}
  证明: rfl
-/
theorem _root_.Pi.orthonormalBasis_repr {η : Type*} [Fintype η] {ι : η -> Type*}
    [forall i, Fintype (ι i)] {𝕜 : Type*} [RCLike 𝕜] {E : η -> Type*} [forall i, NormedAddCommGroup (E i)]
    [forall i, InnerProductSpace 𝕜 (E i)] (B : forall i, OrthonormalBasis (ι i) 𝕜 (E i)) (x : (i : η) -> E i)
    (j : (i : η) × (ι i)) :
    (Pi.orthonormalBasis B).repr (toLp 2 x) j = (B j.fst).repr (x j.fst) j.snd := rfl

variable {v : ι -> E}

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: (hon : Orthonormal 𝕜 v) (hsp : ⊤ <= Submodule.span 𝕜 (Set.range v))
  body: (Basis.mk (Orthonormal.linearIndependent hon) hsp).toOrthonormalBasis (by rwa [Basis.coe_mk])

@[simp]

中文:
定义 mk
  签名: (hon : Orthonormal 𝕜 v) (hsp : ⊤ <= 子模.span 𝕜 (集合.range v))
  定义体: (Basis.mk (Orthonormal.linearIndependent hon) hsp).toOrthonormalBasis (by rwa [Basis.coe_mk])

@[simp]
-/
protected def mk (hon : Orthonormal 𝕜 v) (hsp : ⊤ <= Submodule.span 𝕜 (Set.range v)) :
    OrthonormalBasis ι 𝕜 E :=
  (Basis.mk (Orthonormal.linearIndependent hon) hsp).toOrthonormalBasis (by rwa [Basis.coe_mk])

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (hon : Orthonormal 𝕜 v) (hsp : ⊤ <= Submodule.span 𝕜 (Set.range v))
  proof: by
  rw [OrthonormalBasis.mk]; rw [_root_.Module.Basis.coe_toOrthonormalBasis]; rw [Basis.coe_mk]

中文:
定理 coe_mk
  条件: (hon : Orthonormal 𝕜 v) (hsp : ⊤ <= 子模.span 𝕜 (集合.range v))
  证明: by
  rw [OrthonormalBasis.mk]; rw [_root_.Module.Basis.coe_toOrthonormalBasis]; rw [Basis.coe_mk]
-/
protected theorem coe_mk (hon : Orthonormal 𝕜 v) (hsp : ⊤ <= Submodule.span 𝕜 (Set.range v)) :
    ⇑(OrthonormalBasis.mk hon hsp) = v := by
  rw [OrthonormalBasis.mk]; rw [_root_.Module.Basis.coe_toOrthonormalBasis]; rw [Basis.coe_mk]

/--
Definition of `span` / `span` 的定义

English:
definition span
  signature: [DecidableEq E] {v' : ι' -> E} (h : Orthonormal 𝕜 v') (s : Finset ι')
  body: let e₀' : Basis s 𝕜 _ :=
    Basis.span (h.linearIndependent.comp ((↑) : s -> ι') Subtype.val_injective)
  let e₀ : OrthonormalBasis s 𝕜 _ :=
    OrthonormalBasis.mk
      (by
        convert! orthonormal_span (h.comp ((↑) : s -> ι') Subtype.val_injective)
        simp [e₀', Basis.span_apply])
      e₀'.span_eq.ge
  let φ : span 𝕜 (s.image v' : Set E) ≃ₗᵢ[𝕜] span 𝕜 (range (v' ∘ ((↑) : s -> ι'))) :=
    LinearIsometryEquiv.ofEq _ _
      (by
        rw [Finset.coe_image]; rw [image_eq_range]
        rfl)
  e₀.map φ.symm

@[simp]

中文:
定义 span
  签名: [DecidableEq E] {v' : ι' -> E} (h : Orthonormal 𝕜 v') (s : 有限集 ι')
  定义体: let e₀' : Basis s 𝕜 _ :=
    Basis.span (h.linearIndependent.comp ((↑) : s -> ι') Subtype.val_injective)
  let e₀ : OrthonormalBasis s 𝕜 _ :=
    OrthonormalBasis.mk
      (by
        convert! orthonormal_span (h.comp ((↑) : s -> ι') Subtype.val_injective)
        simp [e₀', Basis.span_apply])
      e₀'.span_eq.ge
  let φ : span 𝕜 (s.image v' : Set E) ≃ₗᵢ[𝕜] span 𝕜 (range (v' ∘ ((↑) : s -> ι'))) :=
    LinearIsometryEquiv.ofEq _ _
      (by
        rw [Finset.coe_image]; rw [image_eq_range]
        rfl)
  e₀.map φ.symm

@[simp]
-/
protected def span [DecidableEq E] {v' : ι' -> E} (h : Orthonormal 𝕜 v') (s : Finset ι') :
    OrthonormalBasis s 𝕜 (span 𝕜 (s.image v' : Set E)) :=
  let e₀' : Basis s 𝕜 _ :=
    Basis.span (h.linearIndependent.comp ((↑) : s -> ι') Subtype.val_injective)
  let e₀ : OrthonormalBasis s 𝕜 _ :=
    OrthonormalBasis.mk
      (by
        convert! orthonormal_span (h.comp ((↑) : s -> ι') Subtype.val_injective)
        simp [e₀', Basis.span_apply])
      e₀'.span_eq.ge
  let φ : span 𝕜 (s.image v' : Set E) ≃ₗᵢ[𝕜] span 𝕜 (range (v' ∘ ((↑) : s -> ι'))) :=
    LinearIsometryEquiv.ofEq _ _
      (by
        rw [Finset.coe_image]; rw [image_eq_range]
        rfl)
  e₀.map φ.symm

@[simp]
/--
theorem `span_apply` / 定理 `span_apply`

English:
theorem span_apply
  statement: [DecidableEq E] {v' : ι' -> E} (h : Orthonormal 𝕜 v') (s : Finset ι')
  proof: by
  simp only [OrthonormalBasis.span, Basis.span_apply, LinearIsometryEquiv.ofEq_symm,
    OrthonormalBasis.map_apply, OrthonormalBasis.coe_mk, LinearIsometryEquiv.coe_ofEq_apply,
    comp_apply]

中文:
定理 span_apply
  结论: [DecidableEq E] {v' : ι' -> E} (h : Orthonormal 𝕜 v') (s : 有限集 ι')
  证明: by
  simp only [OrthonormalBasis.span, Basis.span_apply, LinearIsometryEquiv.ofEq_symm,
    OrthonormalBasis.map_apply, OrthonormalBasis.coe_mk, LinearIsometryEquiv.coe_ofEq_apply,
    comp_apply]
-/
protected theorem span_apply [DecidableEq E] {v' : ι' -> E} (h : Orthonormal 𝕜 v') (s : Finset ι')
    (i : s) : (OrthonormalBasis.span h s i : E) = v' i := by
  simp only [OrthonormalBasis.span, Basis.span_apply, LinearIsometryEquiv.ofEq_symm,
    OrthonormalBasis.map_apply, OrthonormalBasis.coe_mk, LinearIsometryEquiv.coe_ofEq_apply,
    comp_apply]

open Submodule

/--
Definition of `mkOfOrthogonalEqBot` / `mkOfOrthogonalEqBot` 的定义

English:
definition mkOfOrthogonalEqBot
  signature: (hon : Orthonormal 𝕜 v) (hsp : (span 𝕜 (Set.range v))ᗮ = ⊥)
  body: OrthonormalBasis.mk hon
    (by
      refine Eq.ge ?_
      have : FiniteDimensional 𝕜 (span 𝕜 (range v)) :=
        FiniteDimensional.span_of_finite 𝕜 (finite_range v)
      have : CompleteSpace (span 𝕜 (range v)) := FiniteDimensional.complete 𝕜 _
      rwa [orthogonal_eq_bot_iff] at hsp)

@[simp]

中文:
定义 mkOfOrthogonalEqBot
  签名: (hon : Orthonormal 𝕜 v) (hsp : (span 𝕜 (集合.range v))ᗮ = ⊥)
  定义体: OrthonormalBasis.mk hon
    (by
      refine Eq.ge ?_
      have : FiniteDimensional 𝕜 (span 𝕜 (range v)) :=
        FiniteDimensional.span_of_finite 𝕜 (finite_range v)
      have : CompleteSpace (span 𝕜 (range v)) := FiniteDimensional.complete 𝕜 _
      rwa [orthogonal_eq_bot_iff] at hsp)

@[simp]
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
/--
theorem `coe_of_orthogonal_eq_bot_mk` / 定理 `coe_of_orthogonal_eq_bot_mk`

English:
theorem coe_of_orthogonal_eq_bot_mk
  statement: (hon : Orthonormal 𝕜 v)
  proof: OrthonormalBasis.coe_mk hon _

中文:
定理 coe_of_orthogonal_eq_bot_mk
  结论: (hon : Orthonormal 𝕜 v)
  证明: OrthonormalBasis.coe_mk hon _
-/
protected theorem coe_of_orthogonal_eq_bot_mk (hon : Orthonormal 𝕜 v)
    (hsp : (span 𝕜 (Set.range v))ᗮ = ⊥) : ⇑(OrthonormalBasis.mkOfOrthogonalEqBot hon hsp) = v :=
  OrthonormalBasis.coe_mk hon _

variable [Fintype ι']

/--
Definition of `reindex` / `reindex` 的定义

English:
definition reindex
  signature: (b : OrthonormalBasis ι 𝕜 E) (e : ι ≃ ι')
  body: OrthonormalBasis.ofRepr (b.repr.trans (LinearIsometryEquiv.piLpCongrLeft 2 𝕜 𝕜 e))

中文:
定义 reindex
  签名: (b : 正交标准基 ι 𝕜 E) (e : ι ≃ ι')
  定义体: OrthonormalBasis.ofRepr (b.repr.trans (LinearIsometryEquiv.piLpCongrLeft 2 𝕜 𝕜 e))

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.piLpCongrLeft, OrthonormalBasis, OrthonormalBasis.ofRepr, b.repr.trans, ofRepr, piLpCongrLeft
-/
def reindex (b : OrthonormalBasis ι 𝕜 E) (e : ι ≃ ι') : OrthonormalBasis ι' 𝕜 E :=
  OrthonormalBasis.ofRepr (b.repr.trans (LinearIsometryEquiv.piLpCongrLeft 2 𝕜 𝕜 e))

/--
theorem `reindex_apply` / 定理 `reindex_apply`

English:
theorem reindex_apply
  given: (b : OrthonormalBasis ι 𝕜 E) (e : ι ≃ ι') (i' : ι')
  proof: by
  classical
    dsimp [reindex]
    rw [coe_ofRepr]
    dsimp
    rw [← b.repr_symm_single]; rw [LinearIsometryEquiv.piLpCongrLeft_symm]; rw [EuclideanSpace.piLpCongrLeft_single]

@[simp]

中文:
定理 reindex_apply
  条件: (b : 正交标准基 ι 𝕜 E) (e : ι ≃ ι') (i' : ι')
  证明: by
  classical
    dsimp [reindex]
    rw [coe_ofRepr]
    dsimp
    rw [← b.repr_symm_single]; rw [LinearIsometryEquiv.piLpCongrLeft_symm]; rw [EuclideanSpace.piLpCongrLeft_single]

@[simp]
-/
protected theorem reindex_apply (b : OrthonormalBasis ι 𝕜 E) (e : ι ≃ ι') (i' : ι') :
    (b.reindex e) i' = b (e.symm i') := by
  classical
    dsimp [reindex]
    rw [coe_ofRepr]
    dsimp
    rw [← b.repr_symm_single]; rw [LinearIsometryEquiv.piLpCongrLeft_symm]; rw [EuclideanSpace.piLpCongrLeft_single]

@[simp]
/--
theorem `reindex_toBasis` / 定理 `reindex_toBasis`

English:
theorem reindex_toBasis
  given: (b : OrthonormalBasis ι 𝕜 E) (e : ι ≃ ι')
  proof: Basis.eq_ofRepr_eq_repr fun _ => congr_fun rfl

@[simp]

中文:
定理 reindex_toBasis
  条件: (b : 正交标准基 ι 𝕜 E) (e : ι ≃ ι')
  证明: Basis.eq_ofRepr_eq_repr fun _ => congr_fun rfl

@[simp]

Depends on / 依赖: Basis.eq_ofRepr_eq_repr, congr_fun, eq_ofRepr_eq_repr
-/
theorem reindex_toBasis (b : OrthonormalBasis ι 𝕜 E) (e : ι ≃ ι') :
    (b.reindex e).toBasis = b.toBasis.reindex e := Basis.eq_ofRepr_eq_repr fun _ => congr_fun rfl

@[simp]
/--
theorem `coe_reindex` / 定理 `coe_reindex`

English:
theorem coe_reindex
  given: (b : OrthonormalBasis ι 𝕜 E) (e : ι ≃ ι')
  proof: funext (b.reindex_apply e)

@[simp]

中文:
定理 coe_reindex
  条件: (b : 正交标准基 ι 𝕜 E) (e : ι ≃ ι')
  证明: funext (b.reindex_apply e)

@[simp]
-/
protected theorem coe_reindex (b : OrthonormalBasis ι 𝕜 E) (e : ι ≃ ι') :
    ⇑(b.reindex e) = b ∘ e.symm :=
  funext (b.reindex_apply e)

@[simp]
/--
theorem `repr_reindex` / 定理 `repr_reindex`

English:
theorem repr_reindex
  given: (b : OrthonormalBasis ι 𝕜 E) (e : ι ≃ ι') (x : E) (i' : ι')
  proof: by
  rw [OrthonormalBasis.repr_apply_apply]; rw [b.repr_apply_apply]; rw [OrthonormalBasis.coe_reindex]; rw [comp_apply]

中文:
定理 repr_reindex
  条件: (b : 正交标准基 ι 𝕜 E) (e : ι ≃ ι') (x : E) (i' : ι')
  证明: by
  rw [OrthonormalBasis.repr_apply_apply]; rw [b.repr_apply_apply]; rw [OrthonormalBasis.coe_reindex]; rw [comp_apply]
-/
protected theorem repr_reindex (b : OrthonormalBasis ι 𝕜 E) (e : ι ≃ ι') (x : E) (i' : ι') :
    (b.reindex e).repr x i' = b.repr x (e.symm i') := by
  rw [OrthonormalBasis.repr_apply_apply]; rw [b.repr_apply_apply]; rw [OrthonormalBasis.coe_reindex]; rw [comp_apply]

end OrthonormalBasis

namespace EuclideanSpace

variable (𝕜 ι)

/--
Definition of `basisFun` / `basisFun` 的定义

English:
definition basisFun
  signature: : OrthonormalBasis ι 𝕜 (EuclideanSpace 𝕜 ι)
  body: ⟨LinearIsometryEquiv.refl _ _⟩

@[simp]

中文:
定义 basisFun
  签名: : 正交标准基 ι 𝕜 (EuclideanSpace 𝕜 ι)
  定义体: ⟨LinearIsometryEquiv.refl _ _⟩

@[simp]

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.refl
-/
noncomputable def basisFun : OrthonormalBasis ι 𝕜 (EuclideanSpace 𝕜 ι) :=
  ⟨LinearIsometryEquiv.refl _ _⟩

@[simp]
/--
theorem `basisFun_apply` / 定理 `basisFun_apply`

English:
theorem basisFun_apply
  given: [DecidableEq ι] (i : ι)
  statement: basisFun ι 𝕜 i = EuclideanSpace.single i 1
  proof: PiLp.basisFun_apply _ _ _ _

@[simp]

中文:
定理 basisFun_apply
  条件: [DecidableEq ι] (i : ι)
  结论: basisFun ι 𝕜 i = EuclideanSpace.single i 1
  证明: PiLp.basisFun_apply _ _ _ _

@[simp]

Depends on / 依赖: PiLp.basisFun_apply, basisFun_apply
-/
theorem basisFun_apply [DecidableEq ι] (i : ι) : basisFun ι 𝕜 i = EuclideanSpace.single i 1 :=
  PiLp.basisFun_apply _ _ _ _

@[simp]
/--
theorem `basisFun_repr` / 定理 `basisFun_repr`

English:
theorem basisFun_repr
  given: (x : EuclideanSpace 𝕜 ι) (i : ι)
  statement: (basisFun ι 𝕜).repr x i = x i
  proof: rfl

@[simp]

中文:
定理 basisFun_repr
  条件: (x : EuclideanSpace 𝕜 ι) (i : ι)
  结论: (basisFun ι 𝕜).repr x i = x i
  证明: rfl

@[simp]
-/
theorem basisFun_repr (x : EuclideanSpace 𝕜 ι) (i : ι) : (basisFun ι 𝕜).repr x i = x i := rfl

@[simp]
/--
theorem `basisFun_inner` / 定理 `basisFun_inner`

English:
theorem basisFun_inner
  given: (x : EuclideanSpace 𝕜 ι) (i : ι)
  statement: ⟪basisFun ι 𝕜 i, x⟫ = x i
  proof: by
  simp [← OrthonormalBasis.repr_apply_apply]

@[simp]

中文:
定理 basisFun_inner
  条件: (x : EuclideanSpace 𝕜 ι) (i : ι)
  结论: ⟪basisFun ι 𝕜 i, x⟫ = x i
  证明: by
  simp [← OrthonormalBasis.repr_apply_apply]

@[simp]

Depends on / 依赖: OrthonormalBasis, OrthonormalBasis.repr_apply_apply, repr_apply_apply
-/
theorem basisFun_inner (x : EuclideanSpace 𝕜 ι) (i : ι) : ⟪basisFun ι 𝕜 i, x⟫ = x i := by
  simp [← OrthonormalBasis.repr_apply_apply]

@[simp]
/--
theorem `inner_basisFun_real` / 定理 `inner_basisFun_real`

English:
theorem inner_basisFun_real
  given: (x : EuclideanSpace Real ι) (i : ι)
  proof: by
  rw [real_inner_comm]; rw [basisFun_inner]

中文:
定理 inner_basisFun_real
  条件: (x : EuclideanSpace 实数 ι) (i : ι)
  证明: by
  rw [real_inner_comm]; rw [basisFun_inner]

Depends on / 依赖: basisFun_inner, real_inner_comm
-/
theorem inner_basisFun_real (x : EuclideanSpace Real ι) (i : ι) :
    inner Real x (basisFun ι Real i) = x i := by
  rw [real_inner_comm]; rw [basisFun_inner]

/--
theorem `basisFun_toBasis` / 定理 `basisFun_toBasis`

English:
theorem basisFun_toBasis
  statement: (basisFun ι 𝕜).toBasis = PiLp.basisFun _ 𝕜 ι
  proof: rfl

中文:
定理 basisFun_toBasis
  结论: (basisFun ι 𝕜).toBasis = PiLp.basisFun _ 𝕜 ι
  证明: rfl
-/
theorem basisFun_toBasis : (basisFun ι 𝕜).toBasis = PiLp.basisFun _ 𝕜 ι := rfl

end EuclideanSpace

/--
Instance `OrthonormalBasis.instInhabited` / 实例 `OrthonormalBasis.instInhabited`

English:
instance OrthonormalBasis.instInhabited
  signature: : Inhabited (OrthonormalBasis ι 𝕜 (EuclideanSpace 𝕜 ι))
  body: ⟨EuclideanSpace.basisFun ι 𝕜⟩

中文:
实例 正交标准基.instInhabited
  签名: : 可居 (正交标准基 ι 𝕜 (EuclideanSpace 𝕜 ι))
  定义体: ⟨EuclideanSpace.basisFun ι 𝕜⟩

Depends on / 依赖: EuclideanSpace, EuclideanSpace.basisFun, basisFun
-/
instance OrthonormalBasis.instInhabited : Inhabited (OrthonormalBasis ι 𝕜 (EuclideanSpace 𝕜 ι)) :=
  ⟨EuclideanSpace.basisFun ι 𝕜⟩

namespace OrthonormalBasis

variable {E' : Type*} [Fintype ι'] [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E']
    (b : OrthonormalBasis ι 𝕜 E) (b' : OrthonormalBasis ι' 𝕜 E') (e : ι ≃ ι')

/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: : E ≃ₗᵢ[𝕜] E'
  body: b.repr.trans .trans (.piLpCongrLeft _ _ _ e) b'.repr.symm

@[simp]

中文:
定义 equiv
  签名: : E ≃ₗᵢ[𝕜] E'
  定义体: b.repr.trans .trans (.piLpCongrLeft _ _ _ e) b'.repr.symm

@[simp]
-/
protected def equiv : E ≃ₗᵢ[𝕜] E' :=
b.repr.trans .trans (.piLpCongrLeft _ _ _ e) b'.repr.symm

@[simp]
/--
lemma `equiv_symm` / 引理 `equiv_symm`

English:
lemma equiv_symm
  statement: (b.equiv b' e).symm = b'.equiv b e.symm
  proof: by
  apply b'.toBasis.ext_linearIsometryEquiv
  simp [OrthonormalBasis.equiv]

@[simp]

中文:
引理 equiv_symm
  结论: (b.equiv b' e).symm = b'.equiv b e.symm
  证明: by
  apply b'.toBasis.ext_linearIsometryEquiv
  simp [OrthonormalBasis.equiv]

@[simp]

Depends on / 依赖: OrthonormalBasis, OrthonormalBasis.equiv, ext_linearIsometryEquiv, toBasis, toBasis.ext_linearIsometryEquiv
-/
lemma equiv_symm : (b.equiv b' e).symm = b'.equiv b e.symm := by
  apply b'.toBasis.ext_linearIsometryEquiv
  simp [OrthonormalBasis.equiv]

@[simp]
/--
lemma `equiv_apply_basis` / 引理 `equiv_apply_basis`

English:
lemma equiv_apply_basis
  given: (i : ι)
  statement: b.equiv b' e (b i) = b' (e i)
  proof: by
  classical
  simp only [OrthonormalBasis.equiv, LinearIsometryEquiv.trans_apply, OrthonormalBasis.repr_self]
  refine DFunLike.congr rfl ?_
  ext j
  simp

@[simp]

中文:
引理 equiv_apply_basis
  条件: (i : ι)
  结论: b.equiv b' e (b i) = b' (e i)
  证明: by
  classical
  simp only [OrthonormalBasis.equiv, LinearIsometryEquiv.trans_apply, OrthonormalBasis.repr_self]
  refine DFunLike.congr rfl ?_
  ext j
  simp

@[simp]

Depends on / 依赖: DFunLike, DFunLike.congr, LinearIsometryEquiv, LinearIsometryEquiv.trans_apply, OrthonormalBasis, OrthonormalBasis.equiv, OrthonormalBasis.repr_self, classical, repr_self, trans_apply
-/
lemma equiv_apply_basis (i : ι) : b.equiv b' e (b i) = b' (e i) := by
  classical
  simp only [OrthonormalBasis.equiv, LinearIsometryEquiv.trans_apply, OrthonormalBasis.repr_self]
  refine DFunLike.congr rfl ?_
  ext j
  simp

@[simp]
/--
lemma `equiv_self_rfl` / 引理 `equiv_self_rfl`

English:
lemma equiv_self_rfl
  statement: b.equiv b (.refl ι) = .refl 𝕜 E
  proof: by
  apply b.toBasis.ext_linearIsometryEquiv
  simp

中文:
引理 equiv_self_rfl
  结论: b.equiv b (.refl ι) = .refl 𝕜 E
  证明: by
  apply b.toBasis.ext_linearIsometryEquiv
  simp

Depends on / 依赖: b.toBasis.ext_linearIsometryEquiv, ext_linearIsometryEquiv, toBasis
-/
lemma equiv_self_rfl : b.equiv b (.refl ι) = .refl 𝕜 E := by
  apply b.toBasis.ext_linearIsometryEquiv
  simp

set_option backward.isDefEq.respectTransparency false in
/--
lemma `equiv_apply` / 引理 `equiv_apply`

English:
lemma equiv_apply
  given: (x : E)
  statement: b.equiv b' e x = ∑ i, b.repr x i • b' (e i)
  proof: by
  nth_rw 1 [← b.sum_repr x, map_sum]
  simp_rw [map_smul, equiv_apply_basis]

中文:
引理 equiv_apply
  条件: (x : E)
  结论: b.equiv b' e x = ∑ i, b.repr x i • b' (e i)
  证明: by
  nth_rw 1 [← b.sum_repr x, map_sum]
  simp_rw [map_smul, equiv_apply_basis]

Depends on / 依赖: b.sum_repr, equiv_apply_basis, map_smul, map_sum, nth_rw, simp_rw, sum_repr
-/
lemma equiv_apply (x : E) : b.equiv b' e x = ∑ i, b.repr x i • b' (e i) := by
  nth_rw 1 [← b.sum_repr x, map_sum]
  simp_rw [map_smul, equiv_apply_basis]

/--
lemma `equiv_apply_euclideanSpace` / 引理 `equiv_apply_euclideanSpace`

English:
lemma equiv_apply_euclideanSpace
  given: (x : EuclideanSpace 𝕜 ι)
  proof: by
  simp_rw [equiv_apply, EuclideanSpace.basisFun_repr, Equiv.refl_apply]

中文:
引理 equiv_apply_euclideanSpace
  条件: (x : EuclideanSpace 𝕜 ι)
  证明: by
  simp_rw [equiv_apply, EuclideanSpace.basisFun_repr, Equiv.refl_apply]

Depends on / 依赖: Equiv.refl_apply, EuclideanSpace, EuclideanSpace.basisFun_repr, basisFun_repr, equiv_apply, refl_apply, simp_rw
-/
lemma equiv_apply_euclideanSpace (x : EuclideanSpace 𝕜 ι) :
    (EuclideanSpace.basisFun ι 𝕜).equiv b (Equiv.refl ι) x = ∑ i, x i • b i := by
  simp_rw [equiv_apply, EuclideanSpace.basisFun_repr, Equiv.refl_apply]

/--
lemma `coe_equiv_euclideanSpace` / 引理 `coe_equiv_euclideanSpace`

English:
lemma coe_equiv_euclideanSpace
  proof: by
  simp_rw [← equiv_apply_euclideanSpace]

中文:
引理 coe_equiv_euclideanSpace
  证明: by
  simp_rw [← equiv_apply_euclideanSpace]

Depends on / 依赖: equiv_apply_euclideanSpace, simp_rw
-/
lemma coe_equiv_euclideanSpace :
    ⇑((EuclideanSpace.basisFun ι 𝕜).equiv b (Equiv.refl ι)) = fun x => ∑ i, x i • b i := by
  simp_rw [← equiv_apply_euclideanSpace]

end OrthonormalBasis

section Complex

/--
Definition of `Complex.orthonormalBasisOneI` / `Complex.orthonormalBasisOneI` 的定义

English:
definition Complex.orthonormalBasisOneI
  signature: : OrthonormalBasis (Fin 2) Real Complex
  body: Complex.basisOneI.toOrthonormalBasis
    (by
      rw [orthonormal_iff_ite]
      intro i; fin_cases i <;> intro j <;> fin_cases j <;> simp [real_inner_eq_re_inner])

@[simp]

中文:
定义 复形.orthonormalBasisOneI
  签名: : 正交标准基 (有限集 2) 实数 复形
  定义体: Complex.basisOneI.toOrthonormalBasis
    (by
      rw [orthonormal_iff_ite]
      intro i; fin_cases i <;> intro j <;> fin_cases j <;> simp [real_inner_eq_re_inner])

@[simp]

Depends on / 依赖: Complex.basisOneI.toOrthonormalBasis, basisOneI, fin_cases, orthonormal_iff_ite, real_inner_eq_re_inner, toOrthonormalBasis
-/
def Complex.orthonormalBasisOneI : OrthonormalBasis (Fin 2) Real Complex :=
  Complex.basisOneI.toOrthonormalBasis
    (by
      rw [orthonormal_iff_ite]
      intro i; fin_cases i <;> intro j <;> fin_cases j <;> simp [real_inner_eq_re_inner])

@[simp]
/--
theorem `Complex.orthonormalBasisOneI_repr_apply` / 定理 `Complex.orthonormalBasisOneI_repr_apply`

English:
theorem Complex.orthonormalBasisOneI_repr_apply
  given: (z : Complex)
  proof: rfl

@[simp]

中文:
定理 复形.orthonormalBasisOneI_repr_apply
  条件: (z : 复形)
  证明: rfl

@[simp]
-/
theorem Complex.orthonormalBasisOneI_repr_apply (z : Complex) :
    Complex.orthonormalBasisOneI.repr z = ![z.re, z.im] :=
  rfl

@[simp]
/--
theorem `Complex.orthonormalBasisOneI_repr_symm_apply` / 定理 `Complex.orthonormalBasisOneI_repr_symm_apply`

English:
theorem Complex.orthonormalBasisOneI_repr_symm_apply
  given: (x : EuclideanSpace Real (Fin 2))
  proof: rfl

@[simp]

中文:
定理 复形.orthonormalBasisOneI_repr_symm_apply
  条件: (x : EuclideanSpace 实数 (有限集 2))
  证明: rfl

@[simp]
-/
theorem Complex.orthonormalBasisOneI_repr_symm_apply (x : EuclideanSpace Real (Fin 2)) :
    Complex.orthonormalBasisOneI.repr.symm x = x 0 + x 1 * I :=
  rfl

@[simp]
/--
theorem `Complex.toBasis_orthonormalBasisOneI` / 定理 `Complex.toBasis_orthonormalBasisOneI`

English:
theorem Complex.toBasis_orthonormalBasisOneI
  proof: Basis.toBasis_toOrthonormalBasis _ _

@[simp]

中文:
定理 复形.toBasis_orthonormalBasisOneI
  证明: Basis.toBasis_toOrthonormalBasis _ _

@[simp]

Depends on / 依赖: Basis.toBasis_toOrthonormalBasis, toBasis_toOrthonormalBasis
-/
theorem Complex.toBasis_orthonormalBasisOneI :
    Complex.orthonormalBasisOneI.toBasis = Complex.basisOneI :=
  Basis.toBasis_toOrthonormalBasis _ _

@[simp]
/--
theorem `Complex.coe_orthonormalBasisOneI` / 定理 `Complex.coe_orthonormalBasisOneI`

English:
theorem Complex.coe_orthonormalBasisOneI
  proof: by
  simp [Complex.orthonormalBasisOneI]

中文:
定理 复形.coe_orthonormalBasisOneI
  证明: by
  simp [Complex.orthonormalBasisOneI]

Depends on / 依赖: Complex.orthonormalBasisOneI, orthonormalBasisOneI
-/
theorem Complex.coe_orthonormalBasisOneI :
    (Complex.orthonormalBasisOneI : Fin 2 -> Complex) = ![1, I] := by
  simp [Complex.orthonormalBasisOneI]

/--
Definition of `Complex.isometryOfOrthonormal` / `Complex.isometryOfOrthonormal` 的定义

English:
definition Complex.isometryOfOrthonormal
  signature: (v : OrthonormalBasis (Fin 2) Real F)
  body: Complex.orthonormalBasisOneI.repr.trans v.repr.symm

@[simp]

中文:
定义 复形.isometryOfOrthonormal
  签名: (v : 正交标准基 (有限集 2) 实数 F)
  定义体: Complex.orthonormalBasisOneI.repr.trans v.repr.symm

@[simp]

Depends on / 依赖: Complex.orthonormalBasisOneI.repr.trans, orthonormalBasisOneI, v.repr.symm
-/
def Complex.isometryOfOrthonormal (v : OrthonormalBasis (Fin 2) Real F) : Complex ≃ₗᵢ[Real] F :=
  Complex.orthonormalBasisOneI.repr.trans v.repr.symm

@[simp]
/--
theorem `Complex.map_isometryOfOrthonormal` / 定理 `Complex.map_isometryOfOrthonormal`

English:
theorem Complex.map_isometryOfOrthonormal
  given: (v : OrthonormalBasis (Fin 2) Real F) (f : F ≃ₗᵢ[Real] F')
  proof: by
  simp only [isometryOfOrthonormal, OrthonormalBasis.map, LinearIsometryEquiv.symm_trans,
    LinearIsometryEquiv.symm_symm]
  -- Porting note: `LinearIsometryEquiv.trans_assoc` doesn't trigger in the `simp` above
  rw [LinearIsometryEquiv.trans_assoc]

中文:
定理 复形.map_isometryOfOrthonormal
  条件: (v : 正交标准基 (有限集 2) 实数 F) (f : F ≃ₗᵢ[实数] F')
  证明: by
  simp only [isometryOfOrthonormal, OrthonormalBasis.map, LinearIsometryEquiv.symm_trans,
    LinearIsometryEquiv.symm_symm]
  -- Porting note: `LinearIsometryEquiv.trans_assoc` doesn't trigger in the `simp` above
  rw [LinearIsometryEquiv.trans_assoc]

Depends on / 依赖: LinearIsometryEquiv, LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.symm_trans, OrthonormalBasis, OrthonormalBasis.map, isometryOfOrthonormal, symm_symm, symm_trans
-/
theorem Complex.map_isometryOfOrthonormal (v : OrthonormalBasis (Fin 2) Real F) (f : F ≃ₗᵢ[Real] F') :
    Complex.isometryOfOrthonormal (v.map f) = (Complex.isometryOfOrthonormal v).trans f := by
  simp only [isometryOfOrthonormal, OrthonormalBasis.map, LinearIsometryEquiv.symm_trans,
    LinearIsometryEquiv.symm_symm]
  -- Porting note: `LinearIsometryEquiv.trans_assoc` doesn't trigger in the `simp` above
  rw [LinearIsometryEquiv.trans_assoc]

/--
theorem `Complex.isometryOfOrthonormal_symm_apply` / 定理 `Complex.isometryOfOrthonormal_symm_apply`

English:
theorem Complex.isometryOfOrthonormal_symm_apply
  given: (v : OrthonormalBasis (Fin 2) Real F) (f : F)
  proof: by
  simp [Complex.isometryOfOrthonormal]

中文:
定理 复形.isometryOfOrthonormal_symm_apply
  条件: (v : 正交标准基 (有限集 2) 实数 F) (f : F)
  证明: by
  simp [Complex.isometryOfOrthonormal]

Depends on / 依赖: Complex.isometryOfOrthonormal, isometryOfOrthonormal
-/
theorem Complex.isometryOfOrthonormal_symm_apply (v : OrthonormalBasis (Fin 2) Real F) (f : F) :
    (Complex.isometryOfOrthonormal v).symm f =
      (v.toBasis.coord 0 f : Complex) + (v.toBasis.coord 1 f : Complex) * I := by
  simp [Complex.isometryOfOrthonormal]

/--
theorem `Complex.isometryOfOrthonormal_apply` / 定理 `Complex.isometryOfOrthonormal_apply`

English:
theorem Complex.isometryOfOrthonormal_apply
  given: (v : OrthonormalBasis (Fin 2) Real F) (z : Complex)
  proof: by
  simp [Complex.isometryOfOrthonormal, ← v.sum_repr_symm]

中文:
定理 复形.isometryOfOrthonormal_apply
  条件: (v : 正交标准基 (有限集 2) 实数 F) (z : 复形)
  证明: by
  simp [Complex.isometryOfOrthonormal, ← v.sum_repr_symm]

Depends on / 依赖: Complex.isometryOfOrthonormal, isometryOfOrthonormal, sum_repr_symm, v.sum_repr_symm
-/
theorem Complex.isometryOfOrthonormal_apply (v : OrthonormalBasis (Fin 2) Real F) (z : Complex) :
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
/--
theorem `OrthonormalBasis.toMatrix_orthonormalBasis_conjTranspose_mul_self` / 定理 `OrthonormalBasis.toMatrix_orthonormalBasis_conjTranspose_mul_self`

English:
theorem OrthonormalBasis.toMatrix_orthonormalBasis_conjTranspose_mul_self
  statement: [Fintype ι']
  proof: by
  ext i j
  convert! a.repr.inner_map_map (b i) (b j)
  · simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_def, PiLp.inner_apply,
      inner_apply']
    congr
  · rw [orthonormal_iff_ite.mp b.orthonormal i j, Matrix.one_apply]

中文:
定理 正交标准基.toMatrix_orthonormalBasis_conjTranspose_mul_self
  结论: [有限类型 ι']
  证明: by
  ext i j
  convert! a.repr.inner_map_map (b i) (b j)
  · simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_def, PiLp.inner_apply,
      inner_apply']
    congr
  · rw [orthonormal_iff_ite.mp b.orthonormal i j, Matrix.one_apply]

Depends on / 依赖: Matrix, Matrix.conjTranspose_apply, Matrix.mul_apply, Matrix.one_apply, PiLp.inner_apply, a.repr.inner_map_map, b.orthonormal, conjTranspose_apply, convert, inner_apply, inner_map_map, mul_apply, one_apply, orthonormal, orthonormal_iff_ite, orthonormal_iff_ite.mp, star_def
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
/--
theorem `OrthonormalBasis.toMatrix_orthonormalBasis_self_mul_conjTranspose` / 定理 `OrthonormalBasis.toMatrix_orthonormalBasis_self_mul_conjTranspose`

English:
theorem OrthonormalBasis.toMatrix_orthonormalBasis_self_mul_conjTranspose
  statement: [Fintype ι']
  proof: by
  classical
  rw [Matrix.mul_eq_one_comm_of_equiv (a.toBasis.indexEquiv b.toBasis)]; rw [a.toMatrix_orthonormalBasis_conjTranspose_mul_self b]

中文:
定理 正交标准基.toMatrix_orthonormalBasis_self_mul_conjTranspose
  结论: [有限类型 ι']
  证明: by
  classical
  rw [Matrix.mul_eq_one_comm_of_equiv (a.toBasis.indexEquiv b.toBasis)]; rw [a.toMatrix_orthonormalBasis_conjTranspose_mul_self b]

Depends on / 依赖: Matrix, Matrix.mul_eq_one_comm_of_equiv, a.toBasis.indexEquiv, a.toMatrix_orthonormalBasis_conjTranspose_mul_self, b.toBasis, classical, indexEquiv, mul_eq_one_comm_of_equiv, toBasis, toMatrix_orthonormalBasis_conjTranspose_mul_self
-/
theorem OrthonormalBasis.toMatrix_orthonormalBasis_self_mul_conjTranspose [Fintype ι']
    (a : OrthonormalBasis ι 𝕜 E) (b : OrthonormalBasis ι' 𝕜 E) :
    a.toBasis.toMatrix b * (a.toBasis.toMatrix b)ᴴ = 1 := by
  classical
  rw [Matrix.mul_eq_one_comm_of_equiv (a.toBasis.indexEquiv b.toBasis)]; rw [a.toMatrix_orthonormalBasis_conjTranspose_mul_self b]

variable (a b : OrthonormalBasis ι 𝕜 E)

/--
theorem `OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary` / 定理 `OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary`

English:
theorem OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary
  proof: by
  rw [Matrix.mem_unitaryGroup_iff']
  exact a.toMatrix_orthonormalBasis_conjTranspose_mul_self b

中文:
定理 正交标准基.toMatrix_orthonormalBasis_mem_unitary
  证明: by
  rw [Matrix.mem_unitaryGroup_iff']
  exact a.toMatrix_orthonormalBasis_conjTranspose_mul_self b

Depends on / 依赖: Matrix, Matrix.mem_unitaryGroup_iff, a.toMatrix_orthonormalBasis_conjTranspose_mul_self, mem_unitaryGroup_iff, toMatrix_orthonormalBasis_conjTranspose_mul_self
-/
theorem OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary :
    a.toBasis.toMatrix b in Matrix.unitaryGroup ι 𝕜 := by
  rw [Matrix.mem_unitaryGroup_iff']
  exact a.toMatrix_orthonormalBasis_conjTranspose_mul_self b

/-- The determinant of the change-of-basis matrix between two orthonormal bases `a`, `b` has
unit length. -/
@[simp]
/--
theorem `OrthonormalBasis.det_to_matrix_orthonormalBasis` / 定理 `OrthonormalBasis.det_to_matrix_orthonormalBasis`

English:
theorem OrthonormalBasis.det_to_matrix_orthonormalBasis
  statement: ‖a.toBasis.det b‖ = 1
  proof: by
  have := (Matrix.det_of_mem_unitary (a.toMatrix_orthonormalBasis_mem_unitary b)).2
  rw [star_def]; rw [RCLike.mul_conj] at this
  norm_cast at this
  rwa [pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero] at this

中文:
定理 正交标准基.det_to_matrix_orthonormalBasis
  结论: ‖a.toBasis.det b‖ = 1
  证明: by
  have := (Matrix.det_of_mem_unitary (a.toMatrix_orthonormalBasis_mem_unitary b)).2
  rw [star_def]; rw [RCLike.mul_conj] at this
  norm_cast at this
  rwa [pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero] at this

Depends on / 依赖: Matrix, Matrix.det_of_mem_unitary, RCLike, RCLike.mul_conj, a.toMatrix_orthonormalBasis_mem_unitary, det_of_mem_unitary, mul_conj, norm_nonneg, pow_eq_one_iff_of_nonneg, star_def, toMatrix_orthonormalBasis_mem_unitary, two_ne_zero
-/
theorem OrthonormalBasis.det_to_matrix_orthonormalBasis : ‖a.toBasis.det b‖ = 1 := by
  have := (Matrix.det_of_mem_unitary (a.toMatrix_orthonormalBasis_mem_unitary b)).2
  rw [star_def]; rw [RCLike.mul_conj] at this
  norm_cast at this
  rwa [pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero] at this

open OrthonormalBasis in
/--
theorem `LinearIsometryEquiv.toMatrix_mem_unitaryGroup` / 定理 `LinearIsometryEquiv.toMatrix_mem_unitaryGroup`

English:
theorem LinearIsometryEquiv.toMatrix_mem_unitaryGroup
  statement: {G : Type*} [NormedAddCommGroup G]
  proof: by
  simp [LinearMap.toMatrix_eq_basisToMatrix, ← coe_map, toMatrix_orthonormalBasis_mem_unitary]

中文:
定理 线性等距等价.toMatrix_mem_unitaryGroup
  结论: {G : 类型} [赋范交换加群 G]
  证明: by
  simp [LinearMap.toMatrix_eq_basisToMatrix, ← coe_map, toMatrix_orthonormalBasis_mem_unitary]

Depends on / 依赖: LinearMap, LinearMap.toMatrix_eq_basisToMatrix, coe_map, toMatrix_eq_basisToMatrix, toMatrix_orthonormalBasis_mem_unitary
-/
theorem LinearIsometryEquiv.toMatrix_mem_unitaryGroup {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 G] (f : E ≃ₗᵢ[𝕜] G) (b : OrthonormalBasis ι 𝕜 E)
    (b' : OrthonormalBasis ι 𝕜 G) : f.toMatrix b.toBasis b'.toBasis in Matrix.unitaryGroup ι 𝕜 := by
  simp [LinearMap.toMatrix_eq_basisToMatrix, ← coe_map, toMatrix_orthonormalBasis_mem_unitary]

end

section Real

variable (a b : OrthonormalBasis ι Real F)

/--
theorem `OrthonormalBasis.toMatrix_orthonormalBasis_mem_orthogonal` / 定理 `OrthonormalBasis.toMatrix_orthonormalBasis_mem_orthogonal`

English:
theorem OrthonormalBasis.toMatrix_orthonormalBasis_mem_orthogonal
  proof: a.toMatrix_orthonormalBasis_mem_unitary b

中文:
定理 正交标准基.toMatrix_orthonormalBasis_mem_orthogonal
  证明: a.toMatrix_orthonormalBasis_mem_unitary b

Depends on / 依赖: a.toMatrix_orthonormalBasis_mem_unitary, toMatrix_orthonormalBasis_mem_unitary
-/
theorem OrthonormalBasis.toMatrix_orthonormalBasis_mem_orthogonal :
    a.toBasis.toMatrix b in Matrix.orthogonalGroup ι Real :=
  a.toMatrix_orthonormalBasis_mem_unitary b

/--
theorem `OrthonormalBasis.det_to_matrix_orthonormalBasis_real` / 定理 `OrthonormalBasis.det_to_matrix_orthonormalBasis_real`

English:
theorem OrthonormalBasis.det_to_matrix_orthonormalBasis_real
  proof: by
  rw [← sq_eq_one_iff]
  simpa [unitary, sq] using! Matrix.det_of_mem_unitary (a.toMatrix_orthonormalBasis_mem_unitary b)

中文:
定理 正交标准基.det_to_matrix_orthonormalBasis_real
  证明: by
  rw [← sq_eq_one_iff]
  simpa [unitary, sq] using! Matrix.det_of_mem_unitary (a.toMatrix_orthonormalBasis_mem_unitary b)

Depends on / 依赖: Matrix, Matrix.det_of_mem_unitary, a.toMatrix_orthonormalBasis_mem_unitary, det_of_mem_unitary, sq_eq_one_iff, toMatrix_orthonormalBasis_mem_unitary, unitary
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
variable {A : ι -> Submodule 𝕜 E}

/--
Definition of `DirectSum.IsInternal.collectedOrthonormalBasis` / `DirectSum.IsInternal.collectedOrthonormalBasis` 的定义

English:
definition DirectSum.IsInternal.collectedOrthonormalBasis
  body: (hV_sum.collectedBasis fun i => (v_family i).toBasis).toOrthonormalBasis by
    simpa using
      hV.orthonormal_sigma_orthonormal (show forall i, Orthonormal 𝕜 (v_family i).toBasis by simp)

中文:
定义 直和.Is整数ernal.collectedOrthonormalBasis
  定义体: (hV_sum.collectedBasis fun i => (v_family i).toBasis).toOrthonormalBasis by
    simpa using
      hV.orthonormal_sigma_orthonormal (show forall i, Orthonormal 𝕜 (v_family i).toBasis by simp)

Depends on / 依赖: Orthonormal, collectedBasis, hV.orthonormal_sigma_orthonormal, hV_sum, hV_sum.collectedBasis, orthonormal_sigma_orthonormal, toBasis, toOrthonormalBasis, v_family
-/
noncomputable def DirectSum.IsInternal.collectedOrthonormalBasis
    (hV : OrthogonalFamily 𝕜 (fun i => A i) fun i => (A i).subtypeₗᵢ) [DecidableEq ι]
    (hV_sum : DirectSum.IsInternal fun i => A i) {α : ι -> Type*} [forall i, Fintype (α i)]
    (v_family : forall i, OrthonormalBasis (α i) 𝕜 (A i)) : OrthonormalBasis (Σ i, α i) 𝕜 E :=
(hV_sum.collectedBasis fun i => (v_family i).toBasis).toOrthonormalBasis by
    simpa using
      hV.orthonormal_sigma_orthonormal (show forall i, Orthonormal 𝕜 (v_family i).toBasis by simp)

/--
theorem `DirectSum.IsInternal.collectedOrthonormalBasis_mem` / 定理 `DirectSum.IsInternal.collectedOrthonormalBasis_mem`

English:
theorem DirectSum.IsInternal.collectedOrthonormalBasis_mem
  statement: [DecidableEq ι]
  proof: by
  simp [DirectSum.IsInternal.collectedOrthonormalBasis]

中文:
定理 直和.Is整数ernal.collectedOrthonormalBasis_mem
  结论: [DecidableEq ι]
  证明: by
  simp [DirectSum.IsInternal.collectedOrthonormalBasis]

Depends on / 依赖: DirectSum, DirectSum.IsInternal.collectedOrthonormalBasis, IsInternal, collectedOrthonormalBasis
-/
theorem DirectSum.IsInternal.collectedOrthonormalBasis_mem [DecidableEq ι]
    (h : DirectSum.IsInternal A) {α : ι -> Type*} [forall i, Fintype (α i)]
    (hV : OrthogonalFamily 𝕜 (fun i => A i) fun i => (A i).subtypeₗᵢ)
    (v : forall i, OrthonormalBasis (α i) 𝕜 (A i)) (a : Σ i, α i) :
    h.collectedOrthonormalBasis hV v a in A a.1 := by
  simp [DirectSum.IsInternal.collectedOrthonormalBasis]

variable [FiniteDimensional 𝕜 E]

/--
theorem `Orthonormal.exists_orthonormalBasis_extension` / 定理 `Orthonormal.exists_orthonormalBasis_extension`

English:
theorem Orthonormal.exists_orthonormalBasis_extension
  given: (hv : Orthonormal 𝕜 ((↑) : v -> E))
  proof: by
  obtain ⟨u₀, hu₀s, hu₀, hu₀_max⟩ := exists_maximal_orthonormal hv
  rw [maximal_orthonormal_iff_orthogonalComplement_eq_bot hu₀] at hu₀_max
  have hu₀_finite : u₀.Finite := hu₀.linearIndependent.setFinite
  let u : Finset E := hu₀_finite.toFinset
  let fu : ↥u ≃ ↥u₀ := hu₀_finite.subtypeEquivToFinset.symm
  have hu : Orthonormal 𝕜 ((↑) : u -> E) := by simpa using! hu₀.comp _ fu.injective
  refine ⟨u, OrthonormalBasis.mkOfOrthogonalEqBot hu ?_, ?_, ?_⟩
  · simpa [u] using! hu₀_max
  · simpa [u] using! hu₀s
  · simp

中文:
定理 Orthonormal.存在_orthonormalBasis_extension
  条件: (hv : Orthonormal 𝕜 ((↑) : v -> E))
  证明: by
  obtain ⟨u₀, hu₀s, hu₀, hu₀_max⟩ := exists_maximal_orthonormal hv
  rw [maximal_orthonormal_iff_orthogonalComplement_eq_bot hu₀] at hu₀_max
  have hu₀_finite : u₀.Finite := hu₀.linearIndependent.setFinite
  let u : Finset E := hu₀_finite.toFinset
  let fu : ↥u ≃ ↥u₀ := hu₀_finite.subtypeEquivToFinset.symm
  have hu : Orthonormal 𝕜 ((↑) : u -> E) := by simpa using! hu₀.comp _ fu.injective
  refine ⟨u, OrthonormalBasis.mkOfOrthogonalEqBot hu ?_, ?_, ?_⟩
  · simpa [u] using! hu₀_max
  · simpa [u] using! hu₀s
  · simp

Depends on / 依赖: Finite, Finset, Orthonormal, OrthonormalBasis, OrthonormalBasis.mkOfOrthogonalEqBot, _finite.subtypeEquivToFinset.symm, _finite.toFinset, exists_maximal_orthonormal, fu.injective, injective, linearIndependent, linearIndependent.setFinite, maximal_orthonormal_iff_orthogonalComplement_eq_bot, mkOfOrthogonalEqBot, setFinite, subtypeEquivToFinset, toFinset
-/
theorem Orthonormal.exists_orthonormalBasis_extension (hv : Orthonormal 𝕜 ((↑) : v -> E)) :
    exists (u : Finset E) (b : OrthonormalBasis u 𝕜 E), v subseteq u ∧ ⇑b = ((↑) : u -> E) := by
  obtain ⟨u₀, hu₀s, hu₀, hu₀_max⟩ := exists_maximal_orthonormal hv
  rw [maximal_orthonormal_iff_orthogonalComplement_eq_bot hu₀] at hu₀_max
  have hu₀_finite : u₀.Finite := hu₀.linearIndependent.setFinite
  let u : Finset E := hu₀_finite.toFinset
  let fu : ↥u ≃ ↥u₀ := hu₀_finite.subtypeEquivToFinset.symm
  have hu : Orthonormal 𝕜 ((↑) : u -> E) := by simpa using! hu₀.comp _ fu.injective
  refine ⟨u, OrthonormalBasis.mkOfOrthogonalEqBot hu ?_, ?_, ?_⟩
  · simpa [u] using! hu₀_max
  · simpa [u] using! hu₀s
  · simp

/--
theorem `Orthonormal.exists_orthonormalBasis_extension_of_card_eq` / 定理 `Orthonormal.exists_orthonormalBasis_extension_of_card_eq`

English:
theorem Orthonormal.exists_orthonormalBasis_extension_of_card_eq
  statement: {ι : Type*} [Fintype ι]
  proof: by
  have hsv : Injective (s.domRestrict v) := hv.linearIndependent.injective
  have hX : Orthonormal 𝕜 ((↑) : Set.range (s.domRestrict v) -> E) := by
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

中文:
定理 Orthonormal.存在_orthonormalBasis_extension_of_card_eq
  结论: {ι : 类型} [有限类型 ι]
  证明: by
  have hsv : Injective (s.domRestrict v) := hv.linearIndependent.injective
  have hX : Orthonormal 𝕜 ((↑) : Set.range (s.domRestrict v) -> E) := by
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

Depends on / 依赖: Fintype, Fintype.card, Injective, MapsTo, Module, Module.finrank_eq_card_finset_basis, Orthonormal, Set.InjOn, Set.in, Set.range, Y.card, domRestrict, exists_orthonormalBasis_extension, finrank_eq_card_finset_basis, hX.exists_orthonormalBasis_extension, hv.linearIndependent.injective, injective, linearIndependent, mapsTo_image, mono_right
-/
theorem Orthonormal.exists_orthonormalBasis_extension_of_card_eq {ι : Type*} [Fintype ι]
    (card_ι : finrank 𝕜 E = Fintype.card ι) {v : ι -> E} {s : Set ι}
    (hv : Orthonormal 𝕜 (s.domRestrict v)) :
    exists b : OrthonormalBasis ι 𝕜 E, forall i in s, b i = v i := by
  have hsv : Injective (s.domRestrict v) := hv.linearIndependent.injective
  have hX : Orthonormal 𝕜 ((↑) : Set.range (s.domRestrict v) -> E) := by
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

/--
theorem `_root_.exists_orthonormalBasis` / 定理 `_root_.exists_orthonormalBasis`

English:
theorem _root_.exists_orthonormalBasis
  proof: let ⟨w, hw, _, hw''⟩ := (orthonormal_empty 𝕜 E).exists_orthonormalBasis_extension
  ⟨w, hw, hw''⟩

中文:
定理 _root_.存在_orthonormalBasis
  证明: let ⟨w, hw, _, hw''⟩ := (orthonormal_empty 𝕜 E).exists_orthonormalBasis_extension
  ⟨w, hw, hw''⟩

Depends on / 依赖: exists_orthonormalBasis_extension, orthonormal_empty
-/
theorem _root_.exists_orthonormalBasis :
    exists (w : Finset E) (b : OrthonormalBasis w 𝕜 E), ⇑b = ((↑) : w -> E) :=
  let ⟨w, hw, _, hw''⟩ := (orthonormal_empty 𝕜 E).exists_orthonormalBasis_extension
  ⟨w, hw, hw''⟩

/-- A finite-dimensional `InnerProductSpace` has an orthonormal basis. -/
irreducible_def stdOrthonormalBasis : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E := by
  let b := Classical.choose (Classical.choose_spec <| exists_orthonormalBasis 𝕜 E)
  rw [finrank_eq_card_basis b.toBasis]
  exact b.reindex (Fintype.equivFinOfCardEq rfl)

/--
theorem `orthonormalBasis_one_dim` / 定理 `orthonormalBasis_one_dim`

English:
theorem orthonormalBasis_one_dim
  given: (b : OrthonormalBasis ι Real Real)
  proof: by
  have : Unique ι := b.toBasis.unique
  have : b default = 1 ∨ b default = -1 := by
    have : ‖b default‖ = 1 := b.orthonormal.1 _
    rwa [Real.norm_eq_abs, abs_eq (zero_le_one' Real)] at this
  rw [eq_const_of_unique b]
  grind

中文:
定理 orthonormalBasis_one_dim
  条件: (b : 正交标准基 ι 实数 实数)
  证明: by
  have : Unique ι := b.toBasis.unique
  have : b default = 1 ∨ b default = -1 := by
    have : ‖b default‖ = 1 := b.orthonormal.1 _
    rwa [Real.norm_eq_abs, abs_eq (zero_le_one' Real)] at this
  rw [eq_const_of_unique b]
  grind

Depends on / 依赖: Real.norm_eq_abs, Unique, abs_eq, b.orthonormal, b.toBasis.unique, eq_const_of_unique, norm_eq_abs, orthonormal, toBasis, unique, zero_le_one
-/
theorem orthonormalBasis_one_dim (b : OrthonormalBasis ι Real Real) :
    (⇑b = fun _ => (1 : Real)) ∨ ⇑b = fun _ => (-1 : Real) := by
  have : Unique ι := b.toBasis.unique
  have : b default = 1 ∨ b default = -1 := by
    have : ‖b default‖ = 1 := b.orthonormal.1 _
    rwa [Real.norm_eq_abs, abs_eq (zero_le_one' Real)] at this
  rw [eq_const_of_unique b]
  grind

variable {𝕜 E}

section SubordinateOrthonormalBasis

open DirectSum

variable {n : Nat} (hn : finrank 𝕜 E = n) [DecidableEq ι] {V : ι -> Submodule 𝕜 E} (hV : IsInternal V)

/-- Exhibit a bijection between `Fin n` and the index set of a certain basis of an `n`-dimensional
inner product space `E`. This should not be accessed directly, but only via the subsequent API. -/
irreducible_def DirectSum.IsInternal.sigmaOrthonormalBasisIndexEquiv
    (hV' : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) :
    (Σ i, Fin (finrank 𝕜 (V i))) ≃ Fin n :=
  let b := hV.collectedOrthonormalBasis hV' fun i => stdOrthonormalBasis 𝕜 (V i)
Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b.toBasis).symm.trans hn

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

/--
theorem `DirectSum.IsInternal.subordinateOrthonormalBasis_subordinate` / 定理 `DirectSum.IsInternal.subordinateOrthonormalBasis_subordinate`

English:
theorem DirectSum.IsInternal.subordinateOrthonormalBasis_subordinate
  statement: (a : Fin n)
  proof: by
  simpa only [DirectSum.IsInternal.subordinateOrthonormalBasis, OrthonormalBasis.coe_reindex,
    DirectSum.IsInternal.subordinateOrthonormalBasisIndex] using!
    hV.collectedOrthonormalBasis_mem hV' (fun i => stdOrthonormalBasis 𝕜 (V i))
      ((hV.sigmaOrthonormalBasisIndexEquiv hn hV').symm a)

中文:
定理 直和.Is整数ernal.subordinateOrthonormalBasis_subordinate
  结论: (a : 有限集 n)
  证明: by
  simpa only [DirectSum.IsInternal.subordinateOrthonormalBasis, OrthonormalBasis.coe_reindex,
    DirectSum.IsInternal.subordinateOrthonormalBasisIndex] using!
    hV.collectedOrthonormalBasis_mem hV' (fun i => stdOrthonormalBasis 𝕜 (V i))
      ((hV.sigmaOrthonormalBasisIndexEquiv hn hV').symm a)

Depends on / 依赖: DirectSum, DirectSum.IsInternal.subordinateOrthonormalBasis, DirectSum.IsInternal.subordinateOrthonormalBasisIndex, IsInternal, OrthonormalBasis, OrthonormalBasis.coe_reindex, coe_reindex, collectedOrthonormalBasis_mem, hV.collectedOrthonormalBasis_mem, hV.sigmaOrthonormalBasisIndexEquiv, sigmaOrthonormalBasisIndexEquiv, stdOrthonormalBasis, subordinateOrthonormalBasis, subordinateOrthonormalBasisIndex
-/
theorem DirectSum.IsInternal.subordinateOrthonormalBasis_subordinate (a : Fin n)
    (hV' : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) :
    hV.subordinateOrthonormalBasis hn hV' a in V (hV.subordinateOrthonormalBasisIndex hn a hV') := by
  simpa only [DirectSum.IsInternal.subordinateOrthonormalBasis, OrthonormalBasis.coe_reindex,
    DirectSum.IsInternal.subordinateOrthonormalBasisIndex] using!
    hV.collectedOrthonormalBasis_mem hV' (fun i => stdOrthonormalBasis 𝕜 (V i))
      ((hV.sigmaOrthonormalBasisIndexEquiv hn hV').symm a)

/--
theorem `DirectSum.IsInternal.exists_subordinateOrthonormalBasisIndex_eq` / 定理 `DirectSum.IsInternal.exists_subordinateOrthonormalBasisIndex_eq`

English:
theorem DirectSum.IsInternal.exists_subordinateOrthonormalBasisIndex_eq
  proof: by
  use hV.sigmaOrthonormalBasisIndexEquiv hn hV' ⟨i, ⟨0, by grind [finrank_eq_zero (S := V i)]⟩⟩
  simp [subordinateOrthonormalBasisIndex_def]

中文:
定理 直和.Is整数ernal.存在_subordinateOrthonormalBasisIndex_eq
  证明: by
  use hV.sigmaOrthonormalBasisIndexEquiv hn hV' ⟨i, ⟨0, by grind [finrank_eq_zero (S := V i)]⟩⟩
  simp [subordinateOrthonormalBasisIndex_def]

Depends on / 依赖: finrank_eq_zero, hV.sigmaOrthonormalBasisIndexEquiv, sigmaOrthonormalBasisIndexEquiv, subordinateOrthonormalBasisIndex_def
-/
theorem DirectSum.IsInternal.exists_subordinateOrthonormalBasisIndex_eq
    (hV' : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) {i : ι} (hi : V i != ⊥) :
    exists a : Fin n, hV.subordinateOrthonormalBasisIndex hn a hV' = i := by
  use hV.sigmaOrthonormalBasisIndexEquiv hn hV' ⟨i, ⟨0, by grind [finrank_eq_zero (S := V i)]⟩⟩
  simp [subordinateOrthonormalBasisIndex_def]

/--
Definition of `DirectSum.IsInternal.subordinateOrthonormalBasisIndexFiberEquiv` / `DirectSum.IsInternal.subordinateOrthonormalBasisIndexFiberEquiv` 的定义

English:
definition DirectSum.IsInternal.subordinateOrthonormalBasisIndexFiberEquiv
  body: Fin.cast (by rw [← subordinateOrthonormalBasisIndex_def, a.property])
    ((hV.sigmaOrthonormalBasisIndexEquiv hn hV').symm a).snd
  invFun b := ⟨hV.sigmaOrthonormalBasisIndexEquiv hn hV' ⟨i, b⟩,
    by simp [subordinateOrthonormalBasisIndex_def]⟩
  left_inv := by grind [subordinateOrthonormalBasisIndex_def, Fin.cast_eq_self]
  right_inv := by grind

中文:
定义 直和.Is整数ernal.subordinateOrthonormalBasisIndexFiberEquiv
  定义体: Fin.cast (by rw [← subordinateOrthonormalBasisIndex_def, a.property])
    ((hV.sigmaOrthonormalBasisIndexEquiv hn hV').symm a).snd
  invFun b := ⟨hV.sigmaOrthonormalBasisIndexEquiv hn hV' ⟨i, b⟩,
    by simp [subordinateOrthonormalBasisIndex_def]⟩
  left_inv := by grind [subordinateOrthonormalBasisIndex_def, Fin.cast_eq_self]
  right_inv := by grind
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

/--
theorem `DirectSum.IsInternal.card_filter_subordinateOrthonormalBasisIndex_eq` / 定理 `DirectSum.IsInternal.card_filter_subordinateOrthonormalBasisIndex_eq`

English:
theorem DirectSum.IsInternal.card_filter_subordinateOrthonormalBasisIndex_eq
  proof: by
  apply Finset.card_eq_of_equiv_fin
  simpa using hV.subordinateOrthonormalBasisIndexFiberEquiv hn hV' i

中文:
定理 直和.Is整数ernal.card_filter_subordinateOrthonormalBasisIndex_eq
  证明: by
  apply Finset.card_eq_of_equiv_fin
  simpa using hV.subordinateOrthonormalBasisIndexFiberEquiv hn hV' i

Depends on / 依赖: Finset, Finset.card_eq_of_equiv_fin, card_eq_of_equiv_fin, hV.subordinateOrthonormalBasisIndexFiberEquiv, subordinateOrthonormalBasisIndexFiberEquiv
-/
theorem DirectSum.IsInternal.card_filter_subordinateOrthonormalBasisIndex_eq
    (hV' : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) (i : ι) :
    Finset.card {a | hV.subordinateOrthonormalBasisIndex hn a hV' = i} = finrank 𝕜 (V i) := by
  apply Finset.card_eq_of_equiv_fin
  simpa using hV.subordinateOrthonormalBasisIndexFiberEquiv hn hV' i

end SubordinateOrthonormalBasis

end FiniteDimensional

/--
Definition of `OrthonormalBasis.fromOrthogonalSpanSingleton` / `OrthonormalBasis.fromOrthogonalSpanSingleton` 的定义

English:
definition OrthonormalBasis.fromOrthogonalSpanSingleton
  signature: (n : Nat) [Fact (finrank 𝕜 E = n + 1)] {v : E}
  body: have : FiniteDimensional 𝕜 E := .of_fact_finrank_eq_succ (K := 𝕜) (V := E) n
(stdOrthonormalBasis _ _).reindex finCongr finrank_orthogonal_span_singleton hv

中文:
定义 正交标准基.fromOrthogonalSpanSingleton
  签名: (n : 自然数) [Fact (finrank 𝕜 E = n + 1)] {v : E}
  定义体: have : FiniteDimensional 𝕜 E := .of_fact_finrank_eq_succ (K := 𝕜) (V := E) n
(stdOrthonormalBasis _ _).reindex finCongr finrank_orthogonal_span_singleton hv

Depends on / 依赖: FiniteDimensional, finCongr, finrank_orthogonal_span_singleton, of_fact_finrank_eq_succ, reindex, stdOrthonormalBasis
-/
def OrthonormalBasis.fromOrthogonalSpanSingleton (n : Nat) [Fact (finrank 𝕜 E = n + 1)] {v : E}
    (hv : v != 0) : OrthonormalBasis (Fin n) 𝕜 (𝕜 ∙ v)ᗮ :=
  have : FiniteDimensional 𝕜 E := .of_fact_finrank_eq_succ (K := 𝕜) (V := E) n
(stdOrthonormalBasis _ _).reindex finCongr finrank_orthogonal_span_singleton hv

section LinearIsometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
variable {S : Submodule 𝕜 V} {L : S ->ₗᵢ[𝕜] V}

open Module

/--
Definition of `LinearIsometry.extend` / `LinearIsometry.extend` 的定义

English:
definition LinearIsometry.extend
  signature: (L : S ->ₗᵢ[𝕜] V)
  body: by
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
  have M_norm_map : forall x : V, ‖M x‖ = ‖x‖ := by
    intro x
    -- Apply M to the orthogonal decomposition of x
    have Mx_decomp : M x = L (p1 x) + L3 (p2 x) := by
      simp only [M, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
        LinearIsometry.coe_toLinearMap]
    -- Mx_decomp is the orthogonal decomposition of M x
    have Mx_orth : ⟪L (p1 x), L3 (p2 x)⟫ = 0 := by
      have Lp1x : L (p1 x) in LinearMap.range L.toLinearMap :=
        LinearMap.mem_range_self L.toLinearMap (p1 x)
      have Lp2x : L3 (p2 x) in (LinearMap.range L.toLinearMap)ᗮ := by
        simp only [LS,
          ← Submodule.range_subtype LSᗮ]
        apply LinearMap.mem_range_self
      apply Submodule.inner_right_of_mem_orthogonal Lp1x Lp2x
    -- Apply the Pythagorean theorem and simplify
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]; rw [norm_sq_eq_add_norm_sq_projection x S]
    simp only [sq, Mx_decomp]
    rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (L (p1 x)) (L3 (p2 x)) Mx_orth]
    simp only [p1, p2, LinearIsometry.norm_map,
      ContinuousLinearMap.coe_coe, Submodule.coe_norm]
  exact
    { toLinearMap := M
      norm_map' := M_norm_map }

中文:
定义 线性等距.extend
  签名: (L : S ->ₗᵢ[𝕜] V)
  定义体: by
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
  have M_norm_map : forall x : V, ‖M x‖ = ‖x‖ := by
    intro x
    -- Apply M to the orthogonal decomposition of x
    have Mx_decomp : M x = L (p1 x) + L3 (p2 x) := by
      simp only [M, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
        LinearIsometry.coe_toLinearMap]
    -- Mx_decomp is the orthogonal decomposition of M x
    have Mx_orth : ⟪L (p1 x), L3 (p2 x)⟫ = 0 := by
      have Lp1x : L (p1 x) in LinearMap.range L.toLinearMap :=
        LinearMap.mem_range_self L.toLinearMap (p1 x)
      have Lp2x : L3 (p2 x) in (LinearMap.range L.toLinearMap)ᗮ := by
        simp only [LS,
          ← Submodule.range_subtype LSᗮ]
        apply LinearMap.mem_range_self
      apply Submodule.inner_right_of_mem_orthogonal Lp1x Lp2x
    -- Apply the Pythagorean theorem and simplify
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]; rw [norm_sq_eq_add_norm_sq_projection x S]
    simp only [sq, Mx_decomp]
    rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (L (p1 x)) (L3 (p2 x)) Mx_orth]
    simp only [p1, p2, LinearIsometry.norm_map,
      ContinuousLinearMap.coe_coe, Submodule.coe_norm]
  exact
    { toLinearMap := M
      norm_map' := M_norm_map }
-/
noncomputable def LinearIsometry.extend (L : S ->ₗᵢ[𝕜] V) : V ->ₗᵢ[𝕜] V := by
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
  have M_norm_map : forall x : V, ‖M x‖ = ‖x‖ := by
    intro x
    -- Apply M to the orthogonal decomposition of x
    have Mx_decomp : M x = L (p1 x) + L3 (p2 x) := by
      simp only [M, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
        LinearIsometry.coe_toLinearMap]
    -- Mx_decomp is the orthogonal decomposition of M x
    have Mx_orth : ⟪L (p1 x), L3 (p2 x)⟫ = 0 := by
      have Lp1x : L (p1 x) in LinearMap.range L.toLinearMap :=
        LinearMap.mem_range_self L.toLinearMap (p1 x)
      have Lp2x : L3 (p2 x) in (LinearMap.range L.toLinearMap)ᗮ := by
        simp only [LS,
          ← Submodule.range_subtype LSᗮ]
        apply LinearMap.mem_range_self
      apply Submodule.inner_right_of_mem_orthogonal Lp1x Lp2x
    -- Apply the Pythagorean theorem and simplify
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]; rw [norm_sq_eq_add_norm_sq_projection x S]
    simp only [sq, Mx_decomp]
    rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (L (p1 x)) (L3 (p2 x)) Mx_orth]
    simp only [p1, p2, LinearIsometry.norm_map,
      ContinuousLinearMap.coe_coe, Submodule.coe_norm]
  exact
    { toLinearMap := M
      norm_map' := M_norm_map }

/--
theorem `LinearIsometry.extend_apply` / 定理 `LinearIsometry.extend_apply`

English:
theorem LinearIsometry.extend_apply
  given: (L : S ->ₗᵢ[𝕜] V) (s : S)
  statement: L.extend s = L s
  proof: by
  simp only [LinearIsometry.extend, ← LinearIsometry.coe_toLinearMap]
  simp

中文:
定理 线性等距.extend_apply
  条件: (L : S ->ₗᵢ[𝕜] V) (s : S)
  结论: L.extend s = L s
  证明: by
  simp only [LinearIsometry.extend, ← LinearIsometry.coe_toLinearMap]
  simp

Depends on / 依赖: LinearIsometry, LinearIsometry.coe_toLinearMap, LinearIsometry.extend, coe_toLinearMap, extend
-/
theorem LinearIsometry.extend_apply (L : S ->ₗᵢ[𝕜] V) (s : S) : L.extend s = L s := by
  simp only [LinearIsometry.extend, ← LinearIsometry.coe_toLinearMap]
  simp

end LinearIsometry

section Matrix

open Matrix

variable {m n : Type*}

namespace Matrix

variable [Fintype n] [DecidableEq n]

/--
Definition of `toEuclideanLin` / `toEuclideanLin` 的定义

English:
abbreviation toEuclideanLin
  signature: : Matrix m n 𝕜 ≃ₗ[𝕜] EuclideanSpace 𝕜 n ->ₗ[𝕜] EuclideanSpace 𝕜 m
  body: toLpLin 2 2

@[deprecated toLpLin_toLp (since := "2026-01-22")]

中文:
缩写 toEuclideanLin
  签名: : 矩阵 m n 𝕜 ≃ₗ[𝕜] EuclideanSpace 𝕜 n ->ₗ[𝕜] EuclideanSpace 𝕜 m
  定义体: toLpLin 2 2

@[deprecated toLpLin_toLp (since := "2026-01-22")]

Depends on / 依赖: toLpLin
-/
abbrev toEuclideanLin : Matrix m n 𝕜 ≃ₗ[𝕜] EuclideanSpace 𝕜 n ->ₗ[𝕜] EuclideanSpace 𝕜 m :=
  toLpLin 2 2

@[deprecated toLpLin_toLp (since := "2026-01-22")]
/--
lemma `toEuclideanLin_toLp` / 引理 `toEuclideanLin_toLp`

English:
lemma toEuclideanLin_toLp
  given: (A : Matrix m n 𝕜) (x : n -> 𝕜)
  proof: rfl

@[deprecated ofLp_toLpLin (since := "2026-01-22")]

中文:
引理 toEuclideanLin_toLp
  条件: (A : 矩阵 m n 𝕜) (x : n -> 𝕜)
  证明: rfl

@[deprecated ofLp_toLpLin (since := "2026-01-22")]
-/
lemma toEuclideanLin_toLp (A : Matrix m n 𝕜) (x : n -> 𝕜) :
    Matrix.toEuclideanLin A (toLp _ x) = toLp _ (Matrix.toLin' A x) := rfl

@[deprecated ofLp_toLpLin (since := "2026-01-22")]
/--
theorem `piLp_ofLp_toEuclideanLin` / 定理 `piLp_ofLp_toEuclideanLin`

English:
theorem piLp_ofLp_toEuclideanLin
  given: (A : Matrix m n 𝕜) (x : EuclideanSpace 𝕜 n)
  proof: rfl

@[deprecated toLpLin_apply (since := "2026-01-22")]

中文:
定理 piLp_ofLp_toEuclideanLin
  条件: (A : 矩阵 m n 𝕜) (x : EuclideanSpace 𝕜 n)
  证明: rfl

@[deprecated toLpLin_apply (since := "2026-01-22")]
-/
theorem piLp_ofLp_toEuclideanLin (A : Matrix m n 𝕜) (x : EuclideanSpace 𝕜 n) :
    ofLp (Matrix.toEuclideanLin A x) = Matrix.toLin' A (ofLp x) :=
  rfl

@[deprecated toLpLin_apply (since := "2026-01-22")]
/--
theorem `toEuclideanLin_apply` / 定理 `toEuclideanLin_apply`

English:
theorem toEuclideanLin_apply
  given: (M : Matrix m n 𝕜) (v : EuclideanSpace 𝕜 n)
  proof: rfl

@[deprecated ofLp_toLpLin (since := "2026-01-22")]

中文:
定理 toEuclideanLin_apply
  条件: (M : 矩阵 m n 𝕜) (v : EuclideanSpace 𝕜 n)
  证明: rfl

@[deprecated ofLp_toLpLin (since := "2026-01-22")]
-/
theorem toEuclideanLin_apply (M : Matrix m n 𝕜) (v : EuclideanSpace 𝕜 n) :
    toEuclideanLin M v = toLp _ (M *ᵥ ofLp v) := rfl

@[deprecated ofLp_toLpLin (since := "2026-01-22")]
/--
theorem `ofLp_toEuclideanLin_apply` / 定理 `ofLp_toEuclideanLin_apply`

English:
theorem ofLp_toEuclideanLin_apply
  given: (M : Matrix m n 𝕜) (v : EuclideanSpace 𝕜 n)
  proof: rfl

@[deprecated toLpLin_toLp (since := "2026-01-22")]

中文:
定理 ofLp_toEuclideanLin_apply
  条件: (M : 矩阵 m n 𝕜) (v : EuclideanSpace 𝕜 n)
  证明: rfl

@[deprecated toLpLin_toLp (since := "2026-01-22")]
-/
theorem ofLp_toEuclideanLin_apply (M : Matrix m n 𝕜) (v : EuclideanSpace 𝕜 n) :
    ofLp (toEuclideanLin M v) = M *ᵥ ofLp v :=
  rfl

@[deprecated toLpLin_toLp (since := "2026-01-22")]
/--
theorem `toEuclideanLin_apply_piLp_toLp` / 定理 `toEuclideanLin_apply_piLp_toLp`

English:
theorem toEuclideanLin_apply_piLp_toLp
  given: (M : Matrix m n 𝕜) (v : n -> 𝕜)
  proof: rfl

中文:
定理 toEuclideanLin_apply_piLp_toLp
  条件: (M : 矩阵 m n 𝕜) (v : n -> 𝕜)
  证明: rfl
-/
theorem toEuclideanLin_apply_piLp_toLp (M : Matrix m n 𝕜) (v : n -> 𝕜) :
    toEuclideanLin M (toLp _ v) = toLp _ (M *ᵥ v) :=
  rfl

-- `Matrix.toEuclideanLin` is the same as `Matrix.toLin` applied to `PiLp.basisFun`,
@[deprecated toLpLin_eq_toLin (since := "2026-01-22")]
/--
theorem `toEuclideanLin_eq_toLin` / 定理 `toEuclideanLin_eq_toLin`

English:
theorem toEuclideanLin_eq_toLin
  given: [Finite m]
  proof: rfl

中文:
定理 toEuclideanLin_eq_toLin
  条件: [有限 m]
  证明: rfl
-/
theorem toEuclideanLin_eq_toLin [Finite m] :
    (toEuclideanLin : Matrix m n 𝕜 ≃ₗ[𝕜] _) =
      Matrix.toLin (PiLp.basisFun _ _ _) (PiLp.basisFun _ _ _) :=
  rfl

open EuclideanSpace in
/--
lemma `toEuclideanLin_eq_toLin_orthonormal` / 引理 `toEuclideanLin_eq_toLin_orthonormal`

English:
lemma toEuclideanLin_eq_toLin_orthonormal
  given: [Fintype m]
  proof: rfl

中文:
引理 toEuclideanLin_eq_toLin_orthonormal
  条件: [有限类型 m]
  证明: rfl
-/
lemma toEuclideanLin_eq_toLin_orthonormal [Fintype m] :
    toEuclideanLin = toLin (basisFun n 𝕜).toBasis (basisFun m 𝕜).toBasis :=
  rfl

end Matrix

local notation "⟪" x ", " y "⟫ₑ" => inner 𝕜 (toLp 2 x) (toLp 2 y)

/--
theorem `inner_matrix_row_row` / 定理 `inner_matrix_row_row`

English:
theorem inner_matrix_row_row
  given: [Fintype n] (A B : Matrix m n 𝕜) (i j : m)
  proof: by
  simp [PiLp.inner_apply, dotProduct, mul_apply']

中文:
定理 inner_matrix_row_row
  条件: [有限类型 n] (A B : 矩阵 m n 𝕜) (i j : m)
  证明: by
  simp [PiLp.inner_apply, dotProduct, mul_apply']

Depends on / 依赖: PiLp.inner_apply, dotProduct, inner_apply, mul_apply
-/
theorem inner_matrix_row_row [Fintype n] (A B : Matrix m n 𝕜) (i j : m) :
    ⟪A i, B j⟫ₑ = (B * Aᴴ) j i := by
  simp [PiLp.inner_apply, dotProduct, mul_apply']

/--
theorem `inner_matrix_col_col` / 定理 `inner_matrix_col_col`

English:
theorem inner_matrix_col_col
  given: [Fintype m] (A B : Matrix m n 𝕜) (i j : n)
  proof: by
  simp [PiLp.inner_apply, dotProduct, mul_apply', mul_comm]

中文:
定理 inner_matrix_col_col
  条件: [有限类型 m] (A B : 矩阵 m n 𝕜) (i j : n)
  证明: by
  simp [PiLp.inner_apply, dotProduct, mul_apply', mul_comm]

Depends on / 依赖: PiLp.inner_apply, dotProduct, inner_apply, mul_apply, mul_comm
-/
theorem inner_matrix_col_col [Fintype m] (A B : Matrix m n 𝕜) (i j : n) :
    ⟪Aᵀ i, Bᵀ j⟫ₑ = (Aᴴ * B) i j := by
  simp [PiLp.inner_apply, dotProduct, mul_apply', mul_comm]

/--
theorem `LinearMap.toMatrix_innerₛₗ_apply` / 定理 `LinearMap.toMatrix_innerₛₗ_apply`

English:
theorem LinearMap.toMatrix_innerₛₗ_apply
  statement: [Fintype n] [DecidableEq n] [Fintype m]
  proof: by
  ext; simp [LinearMap.toMatrix_apply, vecMulVec_apply, OrthonormalBasis.repr_apply_apply, mul_comm]

@[deprecated (since := "2026-01-03")] alias toMatrix_innerSL_apply :=
  LinearMap.toMatrix_innerₛₗ_apply

中文:
定理 线性映射.toMatrix_innerₛₗ_apply
  结论: [有限类型 n] [DecidableEq n] [有限类型 m]
  证明: by
  ext; simp [LinearMap.toMatrix_apply, vecMulVec_apply, OrthonormalBasis.repr_apply_apply, mul_comm]

@[deprecated (since := "2026-01-03")] alias toMatrix_innerSL_apply :=
  LinearMap.toMatrix_innerₛₗ_apply

Depends on / 依赖: LinearMap, LinearMap.toMatrix_apply, OrthonormalBasis, OrthonormalBasis.repr_apply_apply, mul_comm, repr_apply_apply, toMatrix_apply, vecMulVec_apply
-/
theorem LinearMap.toMatrix_innerₛₗ_apply [Fintype n] [DecidableEq n] [Fintype m]
    (b : OrthonormalBasis n 𝕜 E) (b₂ : OrthonormalBasis m 𝕜 𝕜) (x : E) :
    (innerₛₗ 𝕜 x).toMatrix b.toBasis b₂.toBasis = vecMulVec (star b₂) (star (b.repr x)) := by
  ext; simp [LinearMap.toMatrix_apply, vecMulVec_apply, OrthonormalBasis.repr_apply_apply, mul_comm]

@[deprecated (since := "2026-01-03")] alias toMatrix_innerSL_apply :=
  LinearMap.toMatrix_innerₛₗ_apply

end Matrix

open ContinuousLinearMap LinearMap in
/--
theorem `InnerProductSpace.toMatrix_rankOne` / 定理 `InnerProductSpace.toMatrix_rankOne`

English:
theorem InnerProductSpace.toMatrix_rankOne
  statement: {𝕜 E F ι ι' : Type*} [RCLike 𝕜]
  proof: by
  have := Fintype.ofFinite ι
  rw [rankOne_def']; rw [ContinuousLinearMap.toLinearMap_comp]; rw [toLinearMap_toSpanSingleton]; rw [toMatrix_comp _ (OrthonormalBasis.singleton Unit 𝕜).toBasis]; rw [toMatrix_toSpanSingleton]; rw [toLinearMap_innerSL_apply]; rw [toMatrix_innerₛₗ_apply]; rw [OrthonormalBasis.toBasis_singleton]; rw [Basis.coe_singleton]; rw [Matrix.vecMulVec_one]; rw [OrthonormalBasis.coe_singleton]; rw [star_one]; rw [Matrix.one_vecMulVec]; rw [Matrix.vecMulVec_eq Unit]

中文:
定理 内积空间.toMatrix_rankOne
  结论: {𝕜 E F ι ι' : 类型} [RCLike 𝕜]
  证明: by
  have := Fintype.ofFinite ι
  rw [rankOne_def']; rw [ContinuousLinearMap.toLinearMap_comp]; rw [toLinearMap_toSpanSingleton]; rw [toMatrix_comp _ (OrthonormalBasis.singleton Unit 𝕜).toBasis]; rw [toMatrix_toSpanSingleton]; rw [toLinearMap_innerSL_apply]; rw [toMatrix_innerₛₗ_apply]; rw [OrthonormalBasis.toBasis_singleton]; rw [Basis.coe_singleton]; rw [Matrix.vecMulVec_one]; rw [OrthonormalBasis.coe_singleton]; rw [star_one]; rw [Matrix.one_vecMulVec]; rw [Matrix.vecMulVec_eq Unit]

Depends on / 依赖: Basis.coe_singleton, ContinuousLinearMap, ContinuousLinearMap.toLinearMap_comp, Fintype, Fintype.ofFinite, Matrix, Matrix.one_vecMulVec, Matrix.vecMulVec_eq, Matrix.vecMulVec_one, OrthonormalBasis, OrthonormalBasis.coe_singleton, OrthonormalBasis.singleton, OrthonormalBasis.toBasis_singleton, coe_singleton, ofFinite, one_vecMulVec, rankOne_def, singleton, star_one, toBasis
-/
theorem InnerProductSpace.toMatrix_rankOne {𝕜 E F ι ι' : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [Finite ι] [Fintype ι'] [DecidableEq ι'] (x : E) (y : F) (b : Module.Basis ι 𝕜 E)
    (b' : OrthonormalBasis ι' 𝕜 F) :
    (rankOne 𝕜 x y).toMatrix b'.toBasis b = .vecMulVec (b.repr x) (star (b'.repr y)) := by
  have := Fintype.ofFinite ι
  rw [rankOne_def']; rw [ContinuousLinearMap.toLinearMap_comp]; rw [toLinearMap_toSpanSingleton]; rw [toMatrix_comp _ (OrthonormalBasis.singleton Unit 𝕜).toBasis]; rw [toMatrix_toSpanSingleton]; rw [toLinearMap_innerSL_apply]; rw [toMatrix_innerₛₗ_apply]; rw [OrthonormalBasis.toBasis_singleton]; rw [Basis.coe_singleton]; rw [Matrix.vecMulVec_one]; rw [OrthonormalBasis.coe_singleton]; rw [star_one]; rw [Matrix.one_vecMulVec]; rw [Matrix.vecMulVec_eq Unit]

set_option backward.isDefEq.respectTransparency false in
open Matrix LinearMap EuclideanSpace in
/--
theorem `InnerProductSpace.symm_toEuclideanLin_rankOne` / 定理 `InnerProductSpace.symm_toEuclideanLin_rankOne`

English:
theorem InnerProductSpace.symm_toEuclideanLin_rankOne
  statement: {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m]
  proof: by
  simp [toLpLin, toMatrix', ← Matrix.ext_iff, vecMulVec_apply, inner_single_right, mul_comm]

中文:
定理 内积空间.symm_toEuclideanLin_rankOne
  结论: {𝕜 m n : 类型} [RCLike 𝕜] [有限类型 m]
  证明: by
  simp [toLpLin, toMatrix', ← Matrix.ext_iff, vecMulVec_apply, inner_single_right, mul_comm]

Depends on / 依赖: Matrix, Matrix.ext_iff, ext_iff, inner_single_right, mul_comm, toLpLin, toMatrix, vecMulVec_apply
-/
theorem InnerProductSpace.symm_toEuclideanLin_rankOne {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m]
    [Fintype n] [DecidableEq n] (x : EuclideanSpace 𝕜 m) (y : EuclideanSpace 𝕜 n) :
    toEuclideanLin.symm (rankOne 𝕜 x y) = .vecMulVec x (star y) := by
  simp [toLpLin, toMatrix', ← Matrix.ext_iff, vecMulVec_apply, inner_single_right, mul_comm]

namespace FiniteDimensional
variable [Unique ι] (h : Module.finrank 𝕜 E = 1) {v : E} (hv : ‖v‖ = 1)

variable (ι 𝕜 v) in
/--
Definition of `orthonormalBasisSingleton` / `orthonormalBasisSingleton` 的定义

English:
definition orthonormalBasisSingleton
  signature: : OrthonormalBasis ι 𝕜 E
  body: (basisSingleton ι h v (by aesop)).toOrthonormalBasis (by simpa)

@[simp]

中文:
定义 orthonormalBasisSingleton
  签名: : 正交标准基 ι 𝕜 E
  定义体: (basisSingleton ι h v (by aesop)).toOrthonormalBasis (by simpa)

@[simp]

Depends on / 依赖: basisSingleton, toOrthonormalBasis
-/
def orthonormalBasisSingleton : OrthonormalBasis ι 𝕜 E :=
  (basisSingleton ι h v (by aesop)).toOrthonormalBasis (by simpa)

@[simp]
/--
theorem `orthonormalBasisSingleton_apply` / 定理 `orthonormalBasisSingleton_apply`

English:
theorem orthonormalBasisSingleton_apply
  given: (i : ι)
  proof: by
  simp [orthonormalBasisSingleton]

@[simp]

中文:
定理 orthonormalBasisSingleton_apply
  条件: (i : ι)
  证明: by
  simp [orthonormalBasisSingleton]

@[simp]

Depends on / 依赖: orthonormalBasisSingleton
-/
theorem orthonormalBasisSingleton_apply (i : ι) :
    orthonormalBasisSingleton ι 𝕜 h v hv i = v := by
  simp [orthonormalBasisSingleton]

@[simp]
/--
theorem `toBasis_orthonormalBasisSingleton` / 定理 `toBasis_orthonormalBasisSingleton`

English:
theorem toBasis_orthonormalBasisSingleton
  proof: by
  simp [orthonormalBasisSingleton]

@[simp]

中文:
定理 toBasis_orthonormalBasisSingleton
  证明: by
  simp [orthonormalBasisSingleton]

@[simp]

Depends on / 依赖: orthonormalBasisSingleton
-/
theorem toBasis_orthonormalBasisSingleton :
    (orthonormalBasisSingleton ι 𝕜 h v hv).toBasis = basisSingleton ι h v (by aesop) := by
  simp [orthonormalBasisSingleton]

@[simp]
/--
theorem `orthonormalBasisSingleton_repr_apply` / 定理 `orthonormalBasisSingleton_repr_apply`

English:
theorem orthonormalBasisSingleton_repr_apply
  given: (w : E)
  proof: by
  ext
  simp [OrthonormalBasis.repr_apply_apply, Unique.eq_default]

中文:
定理 orthonormalBasisSingleton_repr_apply
  条件: (w : E)
  证明: by
  ext
  simp [OrthonormalBasis.repr_apply_apply, Unique.eq_default]

Depends on / 依赖: OrthonormalBasis, OrthonormalBasis.repr_apply_apply, Unique, Unique.eq_default, eq_default, repr_apply_apply
-/
theorem orthonormalBasisSingleton_repr_apply (w : E) :
    (orthonormalBasisSingleton ι 𝕜 h v hv).repr w = .single default ⟪v, w⟫ := by
  ext
  simp [OrthonormalBasis.repr_apply_apply, Unique.eq_default]

/--
theorem `range_orthonormalBasisSingleton` / 定理 `range_orthonormalBasisSingleton`

English:
theorem range_orthonormalBasisSingleton
  proof: by
  simp

中文:
定理 range_orthonormalBasisSingleton
  证明: by
  simp
-/
theorem range_orthonormalBasisSingleton :
    Set.range (orthonormalBasisSingleton ι 𝕜 h v hv) = {v} := by
  simp

end FiniteDimensional
