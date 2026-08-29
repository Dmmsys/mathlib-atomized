/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Trace

/-!
# Trace for (finite) ring extensions.

Suppose we have an `R`-algebra `S` with a finite basis. For each `s : S`,
the trace of the linear map given by multiplying by `s` gives information about
the roots of the minimal polynomial of `s` over `R`.

## Main definitions

* `Algebra.trace R S x`: the trace of an element `s` of an `R`-algebra `S`
* `Algebra.traceForm R S`: bilinear form sending `x`, `y` to the trace of `x * y`
* `Algebra.traceMatrix R b`: the matrix whose `(i j)`-th element is the trace of `b i * b j`.

## Main results

* `trace_algebraMap_of_basis`, `trace_algebraMap`: if `x : K`, then `Tr_{L/K} x = [L : K] x`
* `trace_trace_of_basis`, `trace_trace`: `Tr_{L/K} (Tr_{F/L} x) = Tr_{F/K} x`

## Implementation notes

Typically, the trace is defined specifically for finite field extensions.
The definition is as general as possible and the assumption that the extension is finite
is added to the lemmas as needed.

We only define the trace for left multiplication (`Algebra.leftMulMatrix`,
i.e. `LinearMap.mulLeft`).
For now, the definitions assume `S` is commutative, so the choice doesn't matter anyway.

## References

* https://en.wikipedia.org/wiki/Field_trace

-/

@[expose] public section


universe w

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra R T]
variable {ι : Type w} [Fintype ι]

open Module

open LinearMap (BilinForm)
open LinearMap

open Matrix

open scoped Matrix

namespace Algebra

variable (R S)

/-- The trace of an element `s` of an `R`-algebra is the trace of `(s * ·)`,
as an `R`-linear map. -/
@[stacks 0BIF "Trace"]
/--
Definition of `trace` / `trace` 的定义

English:
definition trace
  signature: : S ->ₗ[R] R
  body: (LinearMap.trace R S).comp (lmul R S).toLinearMap

中文:
定义 trace
  签名: : S ->ₗ[R] R
  定义体: (LinearMap.trace R S).comp (lmul R S).toLinearMap

Depends on / 依赖: LinearMap, LinearMap.trace, toLinearMap
-/
noncomputable def trace : S ->ₗ[R] R :=
  (LinearMap.trace R S).comp (lmul R S).toLinearMap

variable {S}

-- Not a `simp` lemma since there are more interesting ways to rewrite `trace R S x`,
-- for example `trace_trace`
/--
theorem `trace_apply` / 定理 `trace_apply`

English:
theorem trace_apply
  given: (x)
  statement: trace R S x = LinearMap.trace R S (lmul R S x)
  proof: rfl

中文:
定理 trace_apply
  条件: (x)
  结论: trace R S x = 线性映射.trace R S (lmul R S x)
  证明: rfl
-/
theorem trace_apply (x) : trace R S x = LinearMap.trace R S (lmul R S x) :=
  rfl

/--
theorem `trace_eq_zero_of_not_exists_basis` / 定理 `trace_eq_zero_of_not_exists_basis`

English:
theorem trace_eq_zero_of_not_exists_basis
  given: (h : ¬exists s : Finset S, Nonempty (Basis s R S))
  proof: by ext s; simp [trace_apply, LinearMap.trace, h]

中文:
定理 trace_eq_zero_of_not_存在_basis
  条件: (h : ¬存在 s : 有限集 S, 非空 (基 s R S))
  证明: by ext s; simp [trace_apply, LinearMap.trace, h]

Depends on / 依赖: LinearMap, LinearMap.trace, trace_apply
-/
theorem trace_eq_zero_of_not_exists_basis (h : ¬exists s : Finset S, Nonempty (Basis s R S)) :
    trace R S = 0 := by ext s; simp [trace_apply, LinearMap.trace, h]

variable {R}

-- Can't be a `simp` lemma because it depends on a choice of basis
/--
theorem `trace_eq_matrix_trace` / 定理 `trace_eq_matrix_trace`

English:
theorem trace_eq_matrix_trace
  given: [DecidableEq ι] (b : Basis ι R S) (s : S)
  proof: by
  rw [trace_apply]; rw [LinearMap.trace_eq_matrix_trace _ b]; rw [← toMatrix_lmul_eq]; rfl

中文:
定理 trace_eq_matrix_trace
  条件: [DecidableEq ι] (b : 基 ι R S) (s : S)
  证明: by
  rw [trace_apply]; rw [LinearMap.trace_eq_matrix_trace _ b]; rw [← toMatrix_lmul_eq]; rfl

Depends on / 依赖: LinearMap, LinearMap.trace_eq_matrix_trace, toMatrix_lmul_eq, trace_apply, trace_eq_matrix_trace
-/
theorem trace_eq_matrix_trace [DecidableEq ι] (b : Basis ι R S) (s : S) :
    trace R S s = Matrix.trace (Algebra.leftMulMatrix b s) := by
  rw [trace_apply]; rw [LinearMap.trace_eq_matrix_trace _ b]; rw [← toMatrix_lmul_eq]; rfl

/--
theorem `trace_algebraMap_of_basis` / 定理 `trace_algebraMap_of_basis`

English:
theorem trace_algebraMap_of_basis
  given: (b : Basis ι R S) (x : R)
  proof: by
  have := Classical.decEq ι
  rw [trace_apply]; rw [LinearMap.trace_eq_matrix_trace R b]; rw [Matrix.trace]
  convert! Finset.sum_const x
  simp [-coe_lmul_eq_mul]

中文:
定理 trace_algebraMap_of_basis
  条件: (b : 基 ι R S) (x : R)
  证明: by
  have := Classical.decEq ι
  rw [trace_apply]; rw [LinearMap.trace_eq_matrix_trace R b]; rw [Matrix.trace]
  convert! Finset.sum_const x
  simp [-coe_lmul_eq_mul]

Depends on / 依赖: Classical, Classical.decEq, Finset, Finset.sum_const, LinearMap, LinearMap.trace_eq_matrix_trace, Matrix, Matrix.trace, coe_lmul_eq_mul, convert, sum_const, trace_apply, trace_eq_matrix_trace
-/
theorem trace_algebraMap_of_basis (b : Basis ι R S) (x : R) :
    trace R S (algebraMap R S x) = Fintype.card ι • x := by
  have := Classical.decEq ι
  rw [trace_apply]; rw [LinearMap.trace_eq_matrix_trace R b]; rw [Matrix.trace]
  convert! Finset.sum_const x
  simp [-coe_lmul_eq_mul]


/--
theorem `trace_self` / 定理 `trace_self`

English:
theorem trace_self
  statement: trace R R = LinearMap.id
  proof: by
  ext; simpa using trace_algebraMap_of_basis (.singleton (Fin 1) R) 1

中文:
定理 trace_self
  结论: trace R R = 线性映射.id
  证明: by
  ext; simpa using trace_algebraMap_of_basis (.singleton (Fin 1) R) 1
-/
@[simp] theorem trace_self : trace R R = LinearMap.id := by
  ext; simpa using trace_algebraMap_of_basis (.singleton (Fin 1) R) 1

/--
theorem `trace_self_apply` / 定理 `trace_self_apply`

English:
theorem trace_self_apply
  given: (a)
  statement: trace R R a = a
  proof: by simp

中文:
定理 trace_self_apply
  条件: (a)
  结论: trace R R a = a
  证明: by simp
-/
theorem trace_self_apply (a) : trace R R a = a := by simp

/-- If `x` is in the base field `K`, then the trace is `[L : K] * x`.

(If `L` is not finite-dimensional over `K`, then `trace` and `finrank` return `0`.)
-/
@[simp]
/--
theorem `trace_algebraMap` / 定理 `trace_algebraMap`

English:
theorem trace_algebraMap
  given: [StrongRankCondition R] [Module.Free R S] (x : R)
  proof: by
  by_cases H : exists s : Finset S, Nonempty (Basis s R S)
  · rw [trace_algebraMap_of_basis H.choose_spec.some, finrank_eq_card_basis H.choose_spec.some]
  · simp [trace_eq_zero_of_not_exists_basis R H, finrank_eq_zero_of_not_exists_basis_finset H]

中文:
定理 trace_algebraMap
  条件: [StrongRankCondition R] [模.自由 R S] (x : R)
  证明: by
  by_cases H : exists s : Finset S, Nonempty (Basis s R S)
  · rw [trace_algebraMap_of_basis H.choose_spec.some, finrank_eq_card_basis H.choose_spec.some]
  · simp [trace_eq_zero_of_not_exists_basis R H, finrank_eq_zero_of_not_exists_basis_finset H]

Depends on / 依赖: Finset, H.choose_spec.some, Nonempty, choose_spec, finrank_eq_card_basis, finrank_eq_zero_of_not_exists_basis_finset, trace_algebraMap_of_basis, trace_eq_zero_of_not_exists_basis
-/
theorem trace_algebraMap [StrongRankCondition R] [Module.Free R S] (x : R) :
    trace R S (algebraMap R S x) = finrank R S • x := by
  by_cases H : exists s : Finset S, Nonempty (Basis s R S)
  · rw [trace_algebraMap_of_basis H.choose_spec.some, finrank_eq_card_basis H.choose_spec.some]
  · simp [trace_eq_zero_of_not_exists_basis R H, finrank_eq_zero_of_not_exists_basis_finset H]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `trace_trace_of_basis` / 定理 `trace_trace_of_basis`

English:
theorem trace_trace_of_basis
  statement: [Algebra S T] [IsScalarTower R S T] {ι κ : Type*} [Finite ι]
  proof: by
  have := Classical.decEq ι
  have := Classical.decEq κ
  cases nonempty_fintype ι
  cases nonempty_fintype κ
  rw [trace_eq_matrix_trace (b.smulTower c)]; rw [trace_eq_matrix_trace b]; rw [trace_eq_matrix_trace c]; rw [Matrix.trace]; rw [Matrix.trace]; rw [Matrix.trace]; rw [← Finset.univ_produc

中文:
定理 trace_trace_of_basis
  结论: [代数 S T] [标量塔 R S T] {ι κ : 类型} [有限 ι]
  证明: by
  have := Classical.decEq ι
  have := Classical.decEq κ
  cases nonempty_fintype ι
  cases nonempty_fintype κ
  rw [trace_eq_matrix_trace (b.smulTower c)]; rw [trace_eq_matrix_trace b]; rw [trace_eq_matrix_trace c]; rw [Matrix.trace]; rw [Matrix.trace]; rw [Matrix.trace]; rw [← Finset.univ_produc

Depends on / 依赖: Classical, Classical.decEq, Finset, Finset.sum_apply, Finset.sum_congr, Finset.sum_product, Finset.univ, Finset.univ_product_univ, Matrix, Matrix.diag, Matrix.trace, b.smulTower, leftMu, map_sum, nonempty_fintype, smulTower, smulTower_leftMulMatrix, sum_apply, sum_congr, sum_product
-/
theorem trace_trace_of_basis [Algebra S T] [IsScalarTower R S T] {ι κ : Type*} [Finite ι]
    [Finite κ] (b : Basis ι R S) (c : Basis κ S T) (x : T) :
    trace R S (trace S T x) = trace R T x := by
  have := Classical.decEq ι
  have := Classical.decEq κ
  cases nonempty_fintype ι
  cases nonempty_fintype κ
  rw [trace_eq_matrix_trace (b.smulTower c)]; rw [trace_eq_matrix_trace b]; rw [trace_eq_matrix_trace c]; rw [Matrix.trace]; rw [Matrix.trace]; rw [Matrix.trace]; rw [← Finset.univ_product_univ]; rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_sum, smulTower_leftMulMatrix, Finset.sum_apply, Matrix.diag,
    Finset.sum_apply i (Finset.univ : Finset κ) fun y => leftMulMatrix b (leftMulMatrix c x y y)]

/--
theorem `trace_comp_trace_of_basis` / 定理 `trace_comp_trace_of_basis`

English:
theorem trace_comp_trace_of_basis
  statement: [Algebra S T] [IsScalarTower R S T] {ι κ : Type*} [Finite ι]
  proof: by
  ext
  rw [LinearMap.comp_apply]; rw [LinearMap.restrictScalars_apply]; rw [trace_trace_of_basis b c]

@[simp]

中文:
定理 trace_comp_trace_of_basis
  结论: [代数 S T] [标量塔 R S T] {ι κ : 类型} [有限 ι]
  证明: by
  ext
  rw [LinearMap.comp_apply]; rw [LinearMap.restrictScalars_apply]; rw [trace_trace_of_basis b c]

@[simp]

Depends on / 依赖: LinearMap, LinearMap.comp_apply, LinearMap.restrictScalars_apply, comp_apply, restrictScalars_apply, trace_trace_of_basis
-/
theorem trace_comp_trace_of_basis [Algebra S T] [IsScalarTower R S T] {ι κ : Type*} [Finite ι]
    [Finite κ] (b : Basis ι R S) (c : Basis κ S T) :
    (trace R S).comp ((trace S T).restrictScalars R) = trace R T := by
  ext
  rw [LinearMap.comp_apply]; rw [LinearMap.restrictScalars_apply]; rw [trace_trace_of_basis b c]

@[simp]
/--
theorem `trace_trace` / 定理 `trace_trace`

English:
theorem trace_trace
  statement: [Algebra S T] [IsScalarTower R S T]
  proof: trace_trace_of_basis (Module.Free.chooseBasis R S) (Module.Free.chooseBasis S T) x

中文:
定理 trace_trace
  结论: [代数 S T] [标量塔 R S T]
  证明: trace_trace_of_basis (Module.Free.chooseBasis R S) (Module.Free.chooseBasis S T) x

Depends on / 依赖: Module, Module.Free.chooseBasis, chooseBasis, trace_trace_of_basis
-/
theorem trace_trace [Algebra S T] [IsScalarTower R S T]
    [Module.Free R S] [Module.Finite R S] [Module.Free S T] [Module.Finite S T] (x : T) :
    trace R S (trace S T x) = trace R T x :=
  trace_trace_of_basis (Module.Free.chooseBasis R S) (Module.Free.chooseBasis S T) x

/-- Let `T / S / R` be a tower of finite extensions of fields. Then
$\text{Trace}_{T/R} = \text{Trace}_{S/R} \circ \text{Trace}_{T/S}$. -/
@[simp, stacks 0BIJ "Trace"]
/--
theorem `trace_comp_trace` / 定理 `trace_comp_trace`

English:
theorem trace_comp_trace
  statement: [Algebra S T] [IsScalarTower R S T]
  proof: LinearMap.ext trace_trace

@[simp]

中文:
定理 trace_comp_trace
  结论: [代数 S T] [标量塔 R S T]
  证明: LinearMap.ext trace_trace

@[simp]

Depends on / 依赖: LinearMap, LinearMap.ext, trace_trace
-/
theorem trace_comp_trace [Algebra S T] [IsScalarTower R S T]
    [Module.Free R S] [Module.Finite R S] [Module.Free S T] [Module.Finite S T] :
    (trace R S).comp ((trace S T).restrictScalars R) = trace R T :=
  LinearMap.ext trace_trace

@[simp]
/--
theorem `trace_prod_apply` / 定理 `trace_prod_apply`

English:
theorem trace_prod_apply
  statement: [Module.Free R S] [Module.Free R T] [Module.Finite R S] [Module.Finite R T]
  proof: by
  let f := (lmul R S).toLinearMap.prodMap (lmul R T).toLinearMap
  have : (lmul R (S × T)).toLinearMap = (prodMapLinear R S T S T R).comp f :=
    LinearMap.ext₂ Prod.mul_def
  simp_rw [trace, this]
  exact trace_prodMap' _ _

中文:
定理 trace_prod_apply
  结论: [模.自由 R S] [模.自由 R T] [模.有限 R S] [模.有限 R T]
  证明: by
  let f := (lmul R S).toLinearMap.prodMap (lmul R T).toLinearMap
  have : (lmul R (S × T)).toLinearMap = (prodMapLinear R S T S T R).comp f :=
    LinearMap.ext₂ Prod.mul_def
  simp_rw [trace, this]
  exact trace_prodMap' _ _

Depends on / 依赖: LinearMap, LinearMap.ext, Prod.mul_def, mul_def, prodMap, prodMapLinear, simp_rw, toLinearMap, toLinearMap.prodMap, trace_prodMap
-/
theorem trace_prod_apply [Module.Free R S] [Module.Free R T] [Module.Finite R S] [Module.Finite R T]
    (x : S × T) : trace R (S × T) x = trace R S x.fst + trace R T x.snd := by
  let f := (lmul R S).toLinearMap.prodMap (lmul R T).toLinearMap
  have : (lmul R (S × T)).toLinearMap = (prodMapLinear R S T S T R).comp f :=
    LinearMap.ext₂ Prod.mul_def
  simp_rw [trace, this]
  exact trace_prodMap' _ _

/--
theorem `trace_prod` / 定理 `trace_prod`

English:
theorem trace_prod
  given: [Module.Free R S] [Module.Free R T] [Module.Finite R S] [Module.Finite R T]
  proof: LinearMap.ext fun p => by rw [coprod_apply, trace_prod_apply]

中文:
定理 trace_prod
  条件: [模.自由 R S] [模.自由 R T] [模.有限 R S] [模.有限 R T]
  证明: LinearMap.ext fun p => by rw [coprod_apply, trace_prod_apply]

Depends on / 依赖: LinearMap, LinearMap.ext, coprod_apply, trace_prod_apply
-/
theorem trace_prod [Module.Free R S] [Module.Free R T] [Module.Finite R S] [Module.Finite R T] :
    trace R (S × T) = (trace R S).coprod (trace R T) :=
  LinearMap.ext fun p => by rw [coprod_apply, trace_prod_apply]

section TraceForm

variable (R S)
open LinearMap
/-- The `traceForm` maps `x y : S` to the trace of `x * y`.
It is a symmetric bilinear form and is nondegenerate if the extension is separable. -/
@[stacks 0BIK "Trace pairing"]
/--
Definition of `traceForm` / `traceForm` 的定义

English:
definition traceForm
  signature: : BilinForm R S
  body: LinearMap.compr₂ (lmul R S).toLinearMap (trace R S)

中文:
定义 traceForm
  签名: : BilinForm R S
  定义体: LinearMap.compr₂ (lmul R S).toLinearMap (trace R S)

Depends on / 依赖: LinearMap, LinearMap.compr, toLinearMap
-/
noncomputable def traceForm : BilinForm R S :=
  LinearMap.compr₂ (lmul R S).toLinearMap (trace R S)

variable {S}

-- This is a nicer lemma than the one produced by `@[simps] def traceForm`.
@[simp]
/--
theorem `traceForm_apply` / 定理 `traceForm_apply`

English:
theorem traceForm_apply
  given: (x y : S)
  statement: traceForm R S x y = trace R S (x * y)
  proof: rfl

中文:
定理 traceForm_apply
  条件: (x y : S)
  结论: traceForm R S x y = trace R S (x * y)
  证明: rfl
-/
theorem traceForm_apply (x y : S) : traceForm R S x y = trace R S (x * y) :=
  rfl

/--
theorem `traceForm_isSymm` / 定理 `traceForm_isSymm`

English:
theorem traceForm_isSymm
  statement: (traceForm R S).IsSymm
  proof: ⟨fun _ _ => congr_arg (trace R S) (mul_comm _ _)⟩

中文:
定理 traceForm_isSymm
  结论: (traceForm R S).是Symm
  证明: ⟨fun _ _ => congr_arg (trace R S) (mul_comm _ _)⟩

Depends on / 依赖: congr_arg, mul_comm
-/
theorem traceForm_isSymm : (traceForm R S).IsSymm :=
  ⟨fun _ _ => congr_arg (trace R S) (mul_comm _ _)⟩

/--
theorem `traceForm_toMatrix` / 定理 `traceForm_toMatrix`

English:
theorem traceForm_toMatrix
  given: [DecidableEq ι] (b : Basis ι R S) (i j)
  proof: by
  rw [LinearMap.BilinForm.toMatrix_apply]; rw [traceForm_apply]

中文:
定理 traceForm_toMatrix
  条件: [DecidableEq ι] (b : 基 ι R S) (i j)
  证明: by
  rw [LinearMap.BilinForm.toMatrix_apply]; rw [traceForm_apply]

Depends on / 依赖: BilinForm, LinearMap, LinearMap.BilinForm.toMatrix_apply, toMatrix_apply, traceForm_apply
-/
theorem traceForm_toMatrix [DecidableEq ι] (b : Basis ι R S) (i j) :
    (traceForm R S).toMatrix b i j = trace R S (b i * b j) := by
  rw [LinearMap.BilinForm.toMatrix_apply]; rw [traceForm_apply]

end TraceForm

end Algebra
