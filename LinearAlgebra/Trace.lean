/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen, Antoine Labelle
-/
module

public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.TensorProduct.Free

import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
import Mathlib.RingTheory.SimpleRing.Matrix

/-!
# Trace of a linear map

This file defines the trace of a linear map.

See also `Mathlib/LinearAlgebra/Matrix/Trace.lean` for the trace of a matrix.

## Tags

linear map, trace, diagonal
-/

@[expose] public section

noncomputable section

universe u v w

namespace LinearMap

open scoped Matrix
open Module TensorProduct

section

variable (R : Type u) [CommSemiring R] {M : Type v} [AddCommMonoid M] [Module R M]
variable {ι : Type w} [DecidableEq ι] [Fintype ι]
variable {κ : Type*} [DecidableEq κ] [Fintype κ]
variable (b : Basis ι R M) (c : Basis κ R M)

/--
Definition of `traceAux` / `traceAux` 的定义

English:
definition traceAux
  signature: : (M ->ₗ[R] M) ->ₗ[R] R
  body: Matrix.traceLinearMap ι R R ∘ₗ ↑(LinearMap.toMatrix b b)

中文:
定义 traceAux
  签名: : (M ->ₗ[R] M) ->ₗ[R] R
  定义体: Matrix.traceLinearMap ι R R ∘ₗ ↑(LinearMap.toMatrix b b)

Depends on / 依赖: LinearMap, LinearMap.toMatrix, Matrix, Matrix.traceLinearMap, toMatrix, traceLinearMap
-/
def traceAux : (M ->ₗ[R] M) ->ₗ[R] R :=
  Matrix.traceLinearMap ι R R ∘ₗ ↑(LinearMap.toMatrix b b)

-- Can't be `simp` because it would cause a loop.
/--
theorem `traceAux_def` / 定理 `traceAux_def`

English:
theorem traceAux_def
  given: (b : Basis ι R M) (f : M ->ₗ[R] M)
  proof: rfl

中文:
定理 traceAux_def
  条件: (b : 基 ι R M) (f : M ->ₗ[R] M)
  证明: rfl
-/
theorem traceAux_def (b : Basis ι R M) (f : M ->ₗ[R] M) :
    traceAux R b f = Matrix.trace (LinearMap.toMatrix b b f) :=
  rfl

/--
theorem `traceAux_eq` / 定理 `traceAux_eq`

English:
theorem traceAux_eq
  statement: traceAux R b = traceAux R c
  proof: LinearMap.ext fun f =>
    calc
      Matrix.trace (LinearMap.toMatrix b b f) =
          Matrix.trace (LinearMap.toMatrix b b ((LinearMap.id.comp f).comp LinearMap.id)) := by
        rw [LinearMap.id_comp]; rw [LinearMap.comp_id]
      _ = Matrix.trace (LinearMap.toMatrix c b LinearMap.id * LinearMap.toMatrix c c f *
          LinearMap.toMatrix b c LinearMap.id) := by
        rw [LinearMap.toMatrix_comp _ c]; rw [LinearMap.toMatrix_comp _ c]
      _ = Matrix.trace (LinearMap.toMatrix c c f * LinearMap.toMatrix b c LinearMap.id *
          LinearMap.toMatrix c b LinearMap.id) := by
        rw [Matrix.mul_assoc]; rw [Matrix.trace_mul_comm]
      _ = Matrix.trace (LinearMap.toMatrix c c ((f.comp LinearMap.id).comp LinearMap.id)) := by
        rw [LinearMap.toMatrix_comp _ b]; rw [LinearMap.toMatrix_comp _ c]
      _ = Matrix.trace (LinearMap.toMatrix c c f) := by rw [LinearMap.comp_id, LinearMap.comp_id]

中文:
定理 traceAux_eq
  结论: traceAux R b = traceAux R c
  证明: LinearMap.ext fun f =>
    calc
      Matrix.trace (LinearMap.toMatrix b b f) =
          Matrix.trace (LinearMap.toMatrix b b ((LinearMap.id.comp f).comp LinearMap.id)) := by
        rw [LinearMap.id_comp]; rw [LinearMap.comp_id]
      _ = Matrix.trace (LinearMap.toMatrix c b LinearMap.id * LinearMap.toMatrix c c f *
          LinearMap.toMatrix b c LinearMap.id) := by
        rw [LinearMap.toMatrix_comp _ c]; rw [LinearMap.toMatrix_comp _ c]
      _ = Matrix.trace (LinearMap.toMatrix c c f * LinearMap.toMatrix b c LinearMap.id *
          LinearMap.toMatrix c b LinearMap.id) := by
        rw [Matrix.mul_assoc]; rw [Matrix.trace_mul_comm]
      _ = Matrix.trace (LinearMap.toMatrix c c ((f.comp LinearMap.id).comp LinearMap.id)) := by
        rw [LinearMap.toMatrix_comp _ b]; rw [LinearMap.toMatrix_comp _ c]
      _ = Matrix.trace (LinearMap.toMatrix c c f) := by rw [LinearMap.comp_id, LinearMap.comp_id]

Depends on / 依赖: LinearMap, LinearMap.comp_id, LinearMap.ext, LinearMap.id, LinearMap.id.comp, LinearMap.id_comp, LinearMap.toMatrix, LinearMap.toMatrix_comp, Matrix, Matrix.trace, comp_id, id_comp, toMatrix, toMatrix_comp
-/
theorem traceAux_eq : traceAux R b = traceAux R c :=
  LinearMap.ext fun f =>
    calc
      Matrix.trace (LinearMap.toMatrix b b f) =
          Matrix.trace (LinearMap.toMatrix b b ((LinearMap.id.comp f).comp LinearMap.id)) := by
        rw [LinearMap.id_comp]; rw [LinearMap.comp_id]
      _ = Matrix.trace (LinearMap.toMatrix c b LinearMap.id * LinearMap.toMatrix c c f *
          LinearMap.toMatrix b c LinearMap.id) := by
        rw [LinearMap.toMatrix_comp _ c]; rw [LinearMap.toMatrix_comp _ c]
      _ = Matrix.trace (LinearMap.toMatrix c c f * LinearMap.toMatrix b c LinearMap.id *
          LinearMap.toMatrix c b LinearMap.id) := by
        rw [Matrix.mul_assoc]; rw [Matrix.trace_mul_comm]
      _ = Matrix.trace (LinearMap.toMatrix c c ((f.comp LinearMap.id).comp LinearMap.id)) := by
        rw [LinearMap.toMatrix_comp _ b]; rw [LinearMap.toMatrix_comp _ c]
      _ = Matrix.trace (LinearMap.toMatrix c c f) := by rw [LinearMap.comp_id, LinearMap.comp_id]

variable (M) in
open scoped Classical in
/--
Definition of `trace` / `trace` 的定义

English:
definition trace
  signature: : (M ->ₗ[R] M) ->ₗ[R] R
  body: if H : exists s : Finset M, Nonempty (Basis s R M) then traceAux R H.choose_spec.some else 0

中文:
定义 trace
  签名: : (M ->ₗ[R] M) ->ₗ[R] R
  定义体: if H : exists s : Finset M, Nonempty (Basis s R M) then traceAux R H.choose_spec.some else 0

Depends on / 依赖: Finset, H.choose_spec.some, Nonempty, choose_spec, traceAux
-/
def trace : (M ->ₗ[R] M) ->ₗ[R] R :=
  if H : exists s : Finset M, Nonempty (Basis s R M) then traceAux R H.choose_spec.some else 0

open scoped Classical in
/--
theorem `trace_eq_matrix_trace_of_finset` / 定理 `trace_eq_matrix_trace_of_finset`

English:
theorem trace_eq_matrix_trace_of_finset
  given: {s : Finset M} (b : Basis s R M) (f : M ->ₗ[R] M)
  proof: by
  have : exists s : Finset M, Nonempty (Basis s R M) := ⟨s, ⟨b⟩⟩
  rw [trace]; rw [dif_pos this]; rw [← traceAux_def]
  congr 1
  apply traceAux_eq

中文:
定理 trace_eq_matrix_trace_of_finset
  条件: {s : 有限集 M} (b : 基 s R M) (f : M ->ₗ[R] M)
  证明: by
  have : exists s : Finset M, Nonempty (Basis s R M) := ⟨s, ⟨b⟩⟩
  rw [trace]; rw [dif_pos this]; rw [← traceAux_def]
  congr 1
  apply traceAux_eq

Depends on / 依赖: Finset, Nonempty, dif_pos, traceAux_def, traceAux_eq
-/
theorem trace_eq_matrix_trace_of_finset {s : Finset M} (b : Basis s R M) (f : M ->ₗ[R] M) :
    trace R M f = Matrix.trace (LinearMap.toMatrix b b f) := by
  have : exists s : Finset M, Nonempty (Basis s R M) := ⟨s, ⟨b⟩⟩
  rw [trace]; rw [dif_pos this]; rw [← traceAux_def]
  congr 1
  apply traceAux_eq

/--
theorem `trace_eq_matrix_trace` / 定理 `trace_eq_matrix_trace`

English:
theorem trace_eq_matrix_trace
  given: (f : M ->ₗ[R] M)
  proof: by
  classical
  rw [trace_eq_matrix_trace_of_finset R b.reindexFinsetRange]; rw [← traceAux_def]; rw [← traceAux_def]; rw [traceAux_eq R b b.reindexFinsetRange]

中文:
定理 trace_eq_matrix_trace
  条件: (f : M ->ₗ[R] M)
  证明: by
  classical
  rw [trace_eq_matrix_trace_of_finset R b.reindexFinsetRange]; rw [← traceAux_def]; rw [← traceAux_def]; rw [traceAux_eq R b b.reindexFinsetRange]

Depends on / 依赖: b.reindexFinsetRange, classical, reindexFinsetRange, traceAux_def, traceAux_eq, trace_eq_matrix_trace_of_finset
-/
theorem trace_eq_matrix_trace (f : M ->ₗ[R] M) :
    trace R M f = Matrix.trace (LinearMap.toMatrix b b f) := by
  classical
  rw [trace_eq_matrix_trace_of_finset R b.reindexFinsetRange]; rw [← traceAux_def]; rw [← traceAux_def]; rw [traceAux_eq R b b.reindexFinsetRange]

variable {R} in
/--
theorem `_root_.Matrix.trace_toLin_eq` / 定理 `_root_.Matrix.trace_toLin_eq`

English:
theorem _root_.Matrix.trace_toLin_eq
  given: (A : Matrix ι ι R) (b : Basis ι R M)
  proof: by
  simp [trace_eq_matrix_trace R b]

中文:
定理 _root_.矩阵.trace_toLin_eq
  条件: (A : 矩阵 ι ι R) (b : 基 ι R M)
  证明: by
  simp [trace_eq_matrix_trace R b]
-/
@[simp] theorem _root_.Matrix.trace_toLin_eq (A : Matrix ι ι R) (b : Basis ι R M) :
    LinearMap.trace R _ (Matrix.toLin b b A) = A.trace := by
  simp [trace_eq_matrix_trace R b]

variable {R} in
/--
theorem `_root_.Matrix.trace_toLin'_eq` / 定理 `_root_.Matrix.trace_toLin'_eq`

English:
theorem _root_.Matrix.trace_toLin'_eq
  given: (A : Matrix ι ι R)
  proof: A.trace_toLin_eq (Pi.basisFun R ι)

中文:
定理 _root_.矩阵.trace_toLin'_eq
  条件: (A : 矩阵 ι ι R)
  证明: A.trace_toLin_eq (Pi.basisFun R ι)

Depends on / 依赖: Infinite, Infinite.of_injective, cg_of_countable, dlo_isExtensionPair, embedding_from_cg, f.injective, injective, of_injective, orderStructure
-/
@[simp] theorem _root_.Matrix.trace_toLin'_eq (A : Matrix ι ι R) :
    LinearMap.trace R _ A.toLin' = A.trace :=
  A.trace_toLin_eq (Pi.basisFun R ι)

/--
theorem `trace_mul_comm` / 定理 `trace_mul_comm`

English:
theorem trace_mul_comm
  given: (f g : M ->ₗ[R] M)
  statement: trace R M (f * g) = trace R M (g * f)
  proof: by
  classical
  by_cases H : exists s : Finset M, Nonempty (Basis s R M)
  · let ⟨s, ⟨b⟩⟩ := H
    simp_rw [trace_eq_matrix_trace R b, LinearMap.toMatrix_mul]
    apply Matrix.trace_mul_comm
  · rw [trace, dif_neg H, LinearMap.zero_apply, LinearMap.zero_apply]

中文:
定理 trace_mul_comm
  条件: (f g : M ->ₗ[R] M)
  结论: trace R M (f * g) = trace R M (g * f)
  证明: by
  classical
  by_cases H : exists s : Finset M, Nonempty (Basis s R M)
  · let ⟨s, ⟨b⟩⟩ := H
    simp_rw [trace_eq_matrix_trace R b, LinearMap.toMatrix_mul]
    apply Matrix.trace_mul_comm
  · rw [trace, dif_neg H, LinearMap.zero_apply, LinearMap.zero_apply]

Depends on / 依赖: Finset, LinearMap, LinearMap.toMatrix_mul, LinearMap.zero_apply, Matrix, Matrix.trace_mul_comm, Nonempty, classical, dif_neg, simp_rw, toMatrix_mul, trace_eq_matrix_trace, trace_mul_comm, zero_apply
-/
theorem trace_mul_comm (f g : M ->ₗ[R] M) : trace R M (f * g) = trace R M (g * f) := by
  classical
  by_cases H : exists s : Finset M, Nonempty (Basis s R M)
  · let ⟨s, ⟨b⟩⟩ := H
    simp_rw [trace_eq_matrix_trace R b, LinearMap.toMatrix_mul]
    apply Matrix.trace_mul_comm
  · rw [trace, dif_neg H, LinearMap.zero_apply, LinearMap.zero_apply]

/--
lemma `trace_mul_cycle` / 引理 `trace_mul_cycle`

English:
lemma trace_mul_cycle
  given: (f g h : M ->ₗ[R] M)
  proof: by
  rw [LinearMap.trace_mul_comm]; rw [← mul_assoc]

中文:
引理 trace_mul_cycle
  条件: (f g h : M ->ₗ[R] M)
  证明: by
  rw [LinearMap.trace_mul_comm]; rw [← mul_assoc]

Depends on / 依赖: LinearMap, LinearMap.trace_mul_comm, mul_assoc, trace_mul_comm
-/
lemma trace_mul_cycle (f g h : M ->ₗ[R] M) :
    trace R M (f * g * h) = trace R M (h * f * g) := by
  rw [LinearMap.trace_mul_comm]; rw [← mul_assoc]

/--
lemma `trace_mul_cycle'` / 引理 `trace_mul_cycle'`

English:
lemma trace_mul_cycle'
  given: (f g h : M ->ₗ[R] M)
  proof: by
  rw [← mul_assoc]; rw [LinearMap.trace_mul_comm]

中文:
引理 trace_mul_cycle'
  条件: (f g h : M ->ₗ[R] M)
  证明: by
  rw [← mul_assoc]; rw [LinearMap.trace_mul_comm]

Depends on / 依赖: LinearMap, LinearMap.trace_mul_comm, mul_assoc, trace_mul_comm
-/
lemma trace_mul_cycle' (f g h : M ->ₗ[R] M) :
    trace R M (f * (g * h)) = trace R M (h * (f * g)) := by
  rw [← mul_assoc]; rw [LinearMap.trace_mul_comm]

/--
lemma `trace_lie_mul_eq` / 引理 `trace_lie_mul_eq`

English:
lemma trace_lie_mul_eq
  statement: {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  proof: by
  simp only [Ring.lie_def, sub_mul, mul_sub, map_sub, mul_assoc]
  rw [trace_mul_comm R g (f * h)]; rw [mul_assoc]

中文:
引理 trace_lie_mul_eq
  结论: {R M : 类型} [交换环 R] [加法交换群 M] [模 R M]
  证明: by
  simp only [Ring.lie_def, sub_mul, mul_sub, map_sub, mul_assoc]
  rw [trace_mul_comm R g (f * h)]; rw [mul_assoc]

Depends on / 依赖: Ring.lie_def, lie_def, map_sub, mul_assoc, mul_sub, sub_mul, trace_mul_comm
-/
lemma trace_lie_mul_eq {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (f g h : M ->ₗ[R] M) : trace R M (⁅f, g⁆ * h) = trace R M (f * ⁅g, h⁆) := by
  simp only [Ring.lie_def, sub_mul, mul_sub, map_sub, mul_assoc]
  rw [trace_mul_comm R g (f * h)]; rw [mul_assoc]

/-- The trace of an endomorphism is invariant under conjugation -/
@[simp]
/--
theorem `trace_conj` / 定理 `trace_conj`

English:
theorem trace_conj
  given: (g : M ->ₗ[R] M) (f : (M ->ₗ[R] M)ˣ)
  proof: by
  rw [trace_mul_comm]
  simp

@[simp]

中文:
定理 trace_conj
  条件: (g : M ->ₗ[R] M) (f : (M ->ₗ[R] M)ˣ)
  证明: by
  rw [trace_mul_comm]
  simp

@[simp]

Depends on / 依赖: trace_mul_comm
-/
theorem trace_conj (g : M ->ₗ[R] M) (f : (M ->ₗ[R] M)ˣ) :
    trace R M (↑f * g * ↑f⁻¹) = trace R M g := by
  rw [trace_mul_comm]
  simp

@[simp]
/--
lemma `trace_lie` / 引理 `trace_lie`

English:
lemma trace_lie
  given: {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (f g : Module.End R M)
  proof: by
  rw [Ring.lie_def]; rw [map_sub]; rw [trace_mul_comm]
  exact sub_self _

中文:
引理 trace_lie
  条件: {R M : 类型} [交换环 R] [加法交换群 M] [模 R M] (f g : 模.End R M)
  证明: by
  rw [Ring.lie_def]; rw [map_sub]; rw [trace_mul_comm]
  exact sub_self _

Depends on / 依赖: Ring.lie_def, lie_def, map_sub, sub_self, trace_mul_comm
-/
lemma trace_lie {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (f g : Module.End R M) :
    trace R M ⁅f, g⁆ = 0 := by
  rw [Ring.lie_def]; rw [map_sub]; rw [trace_mul_comm]
  exact sub_self _

end

section

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
variable (N P : Type*) [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
variable {ι : Type*}

/--
theorem `trace_eq_contract_of_basis` / 定理 `trace_eq_contract_of_basis`

English:
theorem trace_eq_contract_of_basis
  given: [Finite ι] (b : Basis ι R M)
  proof: by
  classical
    cases nonempty_fintype ι
    apply Basis.ext (Basis.tensorProduct (Basis.dualBasis b) b)
    rintro ⟨i, j⟩
    simp only [Function.comp_apply, Basis.tensorProduct_apply, Basis.coe_dualBasis, coe_comp]
    rw [trace_eq_matrix_trace R b]; rw [toMatrix_dualTensorHom]
    obtain rfl | hij := eq_or_ne i j
    · simp
    rw [Matrix.trace_single_eq_of_ne j i (1 : R) hij.symm]
    simp [hij]

中文:
定理 trace_eq_contract_of_basis
  条件: [有限 ι] (b : 基 ι R M)
  证明: by
  classical
    cases nonempty_fintype ι
    apply Basis.ext (Basis.tensorProduct (Basis.dualBasis b) b)
    rintro ⟨i, j⟩
    simp only [Function.comp_apply, Basis.tensorProduct_apply, Basis.coe_dualBasis, coe_comp]
    rw [trace_eq_matrix_trace R b]; rw [toMatrix_dualTensorHom]
    obtain rfl | hij := eq_or_ne i j
    · simp
    rw [Matrix.trace_single_eq_of_ne j i (1 : R) hij.symm]
    simp [hij]

Depends on / 依赖: Basis.coe_dualBasis, Basis.dualBasis, Basis.ext, Basis.tensorProduct, Basis.tensorProduct_apply, Function, Function.comp_apply, Matrix, Matrix.trace_single_eq_of_ne, classical, coe_comp, coe_dualBasis, comp_apply, dualBasis, eq_or_ne, hij.symm, nonempty_fintype, tensorProduct, tensorProduct_apply, toMatrix_dualTensorHom
-/
theorem trace_eq_contract_of_basis [Finite ι] (b : Basis ι R M) :
    LinearMap.trace R M ∘ₗ dualTensorHom R M M = contractLeft R M := by
  classical
    cases nonempty_fintype ι
    apply Basis.ext (Basis.tensorProduct (Basis.dualBasis b) b)
    rintro ⟨i, j⟩
    simp only [Function.comp_apply, Basis.tensorProduct_apply, Basis.coe_dualBasis, coe_comp]
    rw [trace_eq_matrix_trace R b]; rw [toMatrix_dualTensorHom]
    obtain rfl | hij := eq_or_ne i j
    · simp
    rw [Matrix.trace_single_eq_of_ne j i (1 : R) hij.symm]
    simp [hij]

/--
theorem `trace_eq_contract_of_basis'` / 定理 `trace_eq_contract_of_basis'`

English:
theorem trace_eq_contract_of_basis'
  given: [Fintype ι] [DecidableEq ι] (b : Basis ι R M)
  proof: by
  simp [LinearEquiv.eq_comp_toLinearMap_symm, trace_eq_contract_of_basis b]

中文:
定理 trace_eq_contract_of_basis'
  条件: [有限类型 ι] [DecidableEq ι] (b : 基 ι R M)
  证明: by
  simp [LinearEquiv.eq_comp_toLinearMap_symm, trace_eq_contract_of_basis b]

Depends on / 依赖: LinearEquiv, LinearEquiv.eq_comp_toLinearMap_symm, eq_comp_toLinearMap_symm, trace_eq_contract_of_basis
-/
theorem trace_eq_contract_of_basis' [Fintype ι] [DecidableEq ι] (b : Basis ι R M) :
    LinearMap.trace R M = contractLeft R M ∘ₗ (dualTensorHomEquivOfBasis b).symm.toLinearMap := by
  simp [LinearEquiv.eq_comp_toLinearMap_symm, trace_eq_contract_of_basis b]

section
variable (R M)
variable [Module.Free R M] [Module.Finite R M] [Module.Free R N] [Module.Finite R N]

/-- When `M` is finite free, the trace of a linear map corresponds to the contraction pairing under
the isomorphism `End(M) ≃ M* ⊗ M`. -/
@[simp]
/--
theorem `trace_eq_contract` / 定理 `trace_eq_contract`

English:
theorem trace_eq_contract
  statement: LinearMap.trace R M ∘ₗ dualTensorHom R M M = contractLeft R M
  proof: trace_eq_contract_of_basis (Module.Free.chooseBasis R M)

@[simp]

中文:
定理 trace_eq_contract
  结论: 线性映射.trace R M ∘ₗ dualTensorHom R M M = contractLeft R M
  证明: trace_eq_contract_of_basis (Module.Free.chooseBasis R M)

@[simp]

Depends on / 依赖: Module, Module.Free.chooseBasis, chooseBasis, trace_eq_contract_of_basis
-/
theorem trace_eq_contract : LinearMap.trace R M ∘ₗ dualTensorHom R M M = contractLeft R M :=
  trace_eq_contract_of_basis (Module.Free.chooseBasis R M)

@[simp]
/--
theorem `trace_eq_contract_apply` / 定理 `trace_eq_contract_apply`

English:
theorem trace_eq_contract_apply
  given: (x : Module.Dual R M otimes[R] M)
  proof: by
  rw [← comp_apply]; rw [trace_eq_contract]

中文:
定理 trace_eq_contract_apply
  条件: (x : 模.对偶 R M otimes[R] M)
  证明: by
  rw [← comp_apply]; rw [trace_eq_contract]

Depends on / 依赖: comp_apply, trace_eq_contract
-/
theorem trace_eq_contract_apply (x : Module.Dual R M otimes[R] M) :
    (LinearMap.trace R M) ((dualTensorHom R M M) x) = contractLeft R M x := by
  rw [← comp_apply]; rw [trace_eq_contract]

/--
theorem `trace_eq_contract'` / 定理 `trace_eq_contract'`

English:
theorem trace_eq_contract'
  proof: by
  rw [dualTensorHomEquiv_eq_dualTensorHomEquivOfBasis (Module.Free.chooseBasis R M)]
  exact trace_eq_contract_of_basis' _

中文:
定理 trace_eq_contract'
  证明: by
  rw [dualTensorHomEquiv_eq_dualTensorHomEquivOfBasis (Module.Free.chooseBasis R M)]
  exact trace_eq_contract_of_basis' _

Depends on / 依赖: Module, Module.Free.chooseBasis, chooseBasis, dualTensorHomEquiv_eq_dualTensorHomEquivOfBasis, trace_eq_contract_of_basis
-/
theorem trace_eq_contract' :
    LinearMap.trace R M = contractLeft R M ∘ₗ (dualTensorHomEquiv R M M).symm.toLinearMap := by
  rw [dualTensorHomEquiv_eq_dualTensorHomEquivOfBasis (Module.Free.chooseBasis R M)]
  exact trace_eq_contract_of_basis' _

/-- The trace of the identity endomorphism is the dimension of the free module. -/
@[simp]
/--
theorem `trace_one` / 定理 `trace_one`

English:
theorem trace_one
  statement: trace R M 1 = (finrank R M : R)
  proof: by
  cases subsingleton_or_nontrivial R
  · simp [eq_iff_true_of_subsingleton]
  have b := Module.Free.chooseBasis R M
  rw [trace_eq_matrix_trace R b]; rw [toMatrix_one]; rw [finrank_eq_card_chooseBasisIndex]
  simp

中文:
定理 trace_one
  结论: trace R M 1 = (finrank R M : R)
  证明: by
  cases subsingleton_or_nontrivial R
  · simp [eq_iff_true_of_subsingleton]
  have b := Module.Free.chooseBasis R M
  rw [trace_eq_matrix_trace R b]; rw [toMatrix_one]; rw [finrank_eq_card_chooseBasisIndex]
  simp

Depends on / 依赖: Module, Module.Free.chooseBasis, chooseBasis, eq_iff_true_of_subsingleton, finrank_eq_card_chooseBasisIndex, subsingleton_or_nontrivial, toMatrix_one, trace_eq_matrix_trace
-/
theorem trace_one : trace R M 1 = (finrank R M : R) := by
  cases subsingleton_or_nontrivial R
  · simp [eq_iff_true_of_subsingleton]
  have b := Module.Free.chooseBasis R M
  rw [trace_eq_matrix_trace R b]; rw [toMatrix_one]; rw [finrank_eq_card_chooseBasisIndex]
  simp

/-- The trace of the identity endomorphism is the dimension of the free module. -/
@[simp]
/--
theorem `trace_id` / 定理 `trace_id`

English:
theorem trace_id
  statement: trace R M id = (finrank R M : R)
  proof: by rw [← Module.End.one_eq_id, trace_one]

@[simp]

中文:
定理 trace_id
  结论: trace R M id = (finrank R M : R)
  证明: by rw [← Module.End.one_eq_id, trace_one]

@[simp]

Depends on / 依赖: Module, Module.End.one_eq_id, one_eq_id, trace_one
-/
theorem trace_id : trace R M id = (finrank R M : R) := by rw [← Module.End.one_eq_id, trace_one]

@[simp]
/--
theorem `trace_transpose` / 定理 `trace_transpose`

English:
theorem trace_transpose
  statement: trace R (Module.Dual R M) ∘ₗ Module.Dual.transpose = trace R M
  proof: by
  let e := dualTensorHomEquiv R M M
  have h : Function.Surjective e.toLinearMap := e.surjective
  refine (cancel_right h).1 ?_
  ext f m; simp [e]

中文:
定理 trace_transpose
  结论: trace R (模.对偶 R M) ∘ₗ 模.对偶.transpose = trace R M
  证明: by
  let e := dualTensorHomEquiv R M M
  have h : Function.Surjective e.toLinearMap := e.surjective
  refine (cancel_right h).1 ?_
  ext f m; simp [e]

Depends on / 依赖: Function, Function.Surjective, Surjective, cancel_right, dualTensorHomEquiv, e.surjective, e.toLinearMap, surjective, toLinearMap
-/
theorem trace_transpose : trace R (Module.Dual R M) ∘ₗ Module.Dual.transpose = trace R M := by
  let e := dualTensorHomEquiv R M M
  have h : Function.Surjective e.toLinearMap := e.surjective
  refine (cancel_right h).1 ?_
  ext f m; simp [e]

/--
theorem `trace_prodMap` / 定理 `trace_prodMap`

English:
theorem trace_prodMap
  proof: by
  let e := (dualTensorHomEquiv R M M).prodCongr (dualTensorHomEquiv R N N)
  have h : Function.Surjective e.toLinearMap := e.surjective
  refine (cancel_right h).1 ?_
  ext <;> simp [e]

中文:
定理 trace_prodMap
  证明: by
  let e := (dualTensorHomEquiv R M M).prodCongr (dualTensorHomEquiv R N N)
  have h : Function.Surjective e.toLinearMap := e.surjective
  refine (cancel_right h).1 ?_
  ext <;> simp [e]

Depends on / 依赖: Function, Function.Surjective, Surjective, cancel_right, dualTensorHomEquiv, e.surjective, e.toLinearMap, prodCongr, surjective, toLinearMap
-/
theorem trace_prodMap :
    trace R (M × N) ∘ₗ prodMapLinear R M N M N R =
      (coprod id id : R × R ->ₗ[R] R) ∘ₗ prodMap (trace R M) (trace R N) := by
  let e := (dualTensorHomEquiv R M M).prodCongr (dualTensorHomEquiv R N N)
  have h : Function.Surjective e.toLinearMap := e.surjective
  refine (cancel_right h).1 ?_
  ext <;> simp [e]

variable {R M N P}

/--
theorem `trace_prodMap'` / 定理 `trace_prodMap'`

English:
theorem trace_prodMap'
  given: (f : M ->ₗ[R] M) (g : N ->ₗ[R] N)
  proof: by
  have h := LinearMap.ext_iff.1 (trace_prodMap R M N) (f, g)
  simp only [coe_comp, Function.comp_apply, prodMap_apply, coprod_apply, id,
    prodMapLinear_apply] at h
  exact h

中文:
定理 trace_prodMap'
  条件: (f : M ->ₗ[R] M) (g : N ->ₗ[R] N)
  证明: by
  have h := LinearMap.ext_iff.1 (trace_prodMap R M N) (f, g)
  simp only [coe_comp, Function.comp_apply, prodMap_apply, coprod_apply, id,
    prodMapLinear_apply] at h
  exact h

Depends on / 依赖: Function, Function.comp_apply, LinearMap, LinearMap.ext_iff, coe_comp, comp_apply, coprod_apply, ext_iff, prodMapLinear_apply, prodMap_apply, trace_prodMap
-/
theorem trace_prodMap' (f : M ->ₗ[R] M) (g : N ->ₗ[R] N) :
    trace R (M × N) (prodMap f g) = trace R M f + trace R N g := by
  have h := LinearMap.ext_iff.1 (trace_prodMap R M N) (f, g)
  simp only [coe_comp, Function.comp_apply, prodMap_apply, coprod_apply, id,
    prodMapLinear_apply] at h
  exact h

variable (R M N P)

open TensorProduct Function

/--
theorem `trace_tensorProduct` / 定理 `trace_tensorProduct`

English:
theorem trace_tensorProduct
  statement: compr₂ (mapBilinear (.id R) M N M N) (trace R (M otimes N)) =
  proof: by
  apply
    (compl₁₂_inj (show Surjective (dualTensorHom R M M) from (dualTensorHomEquiv R M M).surjective)
        (show Surjective (dualTensorHom R N N) from (dualTensorHomEquiv R N N).surjective)).1
  ext f m g n
  simp only [AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    coe_restrictScalars, compl₁₂_apply, compr₂_apply, mapBilinear_apply,
    trace_eq_contract_apply, contractLeft_apply, lsmul_apply, smul_eq_mul,
    map_dualTensorHom, dualDistrib_apply]

中文:
定理 trace_tensorProduct
  结论: compr₂ (mapBilinear (.id R) M N M N) (trace R (M otimes N)) =
  证明: by
  apply
    (compl₁₂_inj (show Surjective (dualTensorHom R M M) from (dualTensorHomEquiv R M M).surjective)
        (show Surjective (dualTensorHom R N N) from (dualTensorHomEquiv R N N).surjective)).1
  ext f m g n
  simp only [AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    coe_restrictScalars, compl₁₂_apply, compr₂_apply, mapBilinear_apply,
    trace_eq_contract_apply, contractLeft_apply, lsmul_apply, smul_eq_mul,
    map_dualTensorHom, dualDistrib_apply]

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.curry_apply, Surjective, TensorProduct, TensorProduct.curry_apply, coe_restrictScalars, contractLeft_apply, curry_apply, dualDistrib_apply, dualTensorHom, dualTensorHomEquiv, lsmul_apply, mapBilinear_apply, map_dualTensorHom, smul_eq_mul, surjective, trace_eq_contract_apply
-/
theorem trace_tensorProduct : compr₂ (mapBilinear (.id R) M N M N) (trace R (M otimes N)) =
    compl₁₂ (lsmul R R : R ->ₗ[R] R ->ₗ[R] R) (trace R M) (trace R N) := by
  apply
    (compl₁₂_inj (show Surjective (dualTensorHom R M M) from (dualTensorHomEquiv R M M).surjective)
        (show Surjective (dualTensorHom R N N) from (dualTensorHomEquiv R N N).surjective)).1
  ext f m g n
  simp only [AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    coe_restrictScalars, compl₁₂_apply, compr₂_apply, mapBilinear_apply,
    trace_eq_contract_apply, contractLeft_apply, lsmul_apply, smul_eq_mul,
    map_dualTensorHom, dualDistrib_apply]

/--
theorem `trace_comp_comm` / 定理 `trace_comp_comm`

English:
theorem trace_comp_comm
  proof: by
  apply
    (compl₁₂_inj (show Surjective (dualTensorHom R N M) from (dualTensorHomEquiv R N M).surjective)
        (show Surjective (dualTensorHom R M N) from (dualTensorHomEquiv R M N).surjective)).1
  ext g m f n
  simp only [AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    coe_restrictScalars, compl₁₂_apply, compr₂_apply, flip_apply, llcomp_apply',
    comp_dualTensorHom, LinearMapClass.map_smul, trace_eq_contract_apply,
    contractLeft_apply, smul_eq_mul, mul_comm]

中文:
定理 trace_comp_comm
  证明: by
  apply
    (compl₁₂_inj (show Surjective (dualTensorHom R N M) from (dualTensorHomEquiv R N M).surjective)
        (show Surjective (dualTensorHom R M N) from (dualTensorHomEquiv R M N).surjective)).1
  ext g m f n
  simp only [AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    coe_restrictScalars, compl₁₂_apply, compr₂_apply, flip_apply, llcomp_apply',
    comp_dualTensorHom, LinearMapClass.map_smul, trace_eq_contract_apply,
    contractLeft_apply, smul_eq_mul, mul_comm]

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.curry_apply, LinearMapClass, LinearMapClass.map_smul, Surjective, TensorProduct, TensorProduct.curry_apply, coe_restrictScalars, comp_dualTensorHom, contractLeft_apply, curry_apply, dualTensorHom, dualTensorHomEquiv, flip_apply, llcomp_apply, map_smul, mul_comm, smul_eq_mul, surjective, trace_eq_contract_apply
-/
theorem trace_comp_comm :
    compr₂ (llcomp R M N M) (trace R M) = compr₂ (llcomp R N M N).flip (trace R N) := by
  apply
    (compl₁₂_inj (show Surjective (dualTensorHom R N M) from (dualTensorHomEquiv R N M).surjective)
        (show Surjective (dualTensorHom R M N) from (dualTensorHomEquiv R M N).surjective)).1
  ext g m f n
  simp only [AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
    coe_restrictScalars, compl₁₂_apply, compr₂_apply, flip_apply, llcomp_apply',
    comp_dualTensorHom, LinearMapClass.map_smul, trace_eq_contract_apply,
    contractLeft_apply, smul_eq_mul, mul_comm]

variable {R M N P}

@[simp]
/--
theorem `trace_transpose'` / 定理 `trace_transpose'`

English:
theorem trace_transpose'
  given: (f : M ->ₗ[R] M)
  proof: by
  rw [← comp_apply]; rw [trace_transpose]

中文:
定理 trace_transpose'
  条件: (f : M ->ₗ[R] M)
  证明: by
  rw [← comp_apply]; rw [trace_transpose]

Depends on / 依赖: comp_apply, trace_transpose
-/
theorem trace_transpose' (f : M ->ₗ[R] M) :
    trace R _ (Module.Dual.transpose (R := R) f) = trace R M f := by
  rw [← comp_apply]; rw [trace_transpose]

/--
theorem `trace_tensorProduct'` / 定理 `trace_tensorProduct'`

English:
theorem trace_tensorProduct'
  given: (f : M ->ₗ[R] M) (g : N ->ₗ[R] N)
  proof: by
  have h := LinearMap.ext_iff.1 (LinearMap.ext_iff.1 (trace_tensorProduct R M N) f) g
  simp only [compr₂_apply, mapBilinear_apply, compl₁₂_apply, lsmul_apply,
    smul_eq_mul] at h
  exact h

中文:
定理 trace_tensorProduct'
  条件: (f : M ->ₗ[R] M) (g : N ->ₗ[R] N)
  证明: by
  have h := LinearMap.ext_iff.1 (LinearMap.ext_iff.1 (trace_tensorProduct R M N) f) g
  simp only [compr₂_apply, mapBilinear_apply, compl₁₂_apply, lsmul_apply,
    smul_eq_mul] at h
  exact h

Depends on / 依赖: LinearMap, LinearMap.ext_iff, ext_iff, lsmul_apply, mapBilinear_apply, smul_eq_mul, trace_tensorProduct
-/
theorem trace_tensorProduct' (f : M ->ₗ[R] M) (g : N ->ₗ[R] N) :
    trace R (M otimes N) (map f g) = trace R M f * trace R N g := by
  have h := LinearMap.ext_iff.1 (LinearMap.ext_iff.1 (trace_tensorProduct R M N) f) g
  simp only [compr₂_apply, mapBilinear_apply, compl₁₂_apply, lsmul_apply,
    smul_eq_mul] at h
  exact h

/--
theorem `trace_comp_comm'` / 定理 `trace_comp_comm'`

English:
theorem trace_comp_comm'
  given: (f : M ->ₗ[R] N) (g : N ->ₗ[R] M)
  proof: by
  have h := LinearMap.ext_iff.1 (LinearMap.ext_iff.1 (trace_comp_comm R M N) g) f
  simp only [llcomp_apply', compr₂_apply, flip_apply] at h
  exact h

@[simp]

中文:
定理 trace_comp_comm'
  条件: (f : M ->ₗ[R] N) (g : N ->ₗ[R] M)
  证明: by
  have h := LinearMap.ext_iff.1 (LinearMap.ext_iff.1 (trace_comp_comm R M N) g) f
  simp only [llcomp_apply', compr₂_apply, flip_apply] at h
  exact h

@[simp]

Depends on / 依赖: LinearMap, LinearMap.ext_iff, ext_iff, flip_apply, llcomp_apply, trace_comp_comm
-/
theorem trace_comp_comm' (f : M ->ₗ[R] N) (g : N ->ₗ[R] M) :
    trace R M (g ∘ₗ f) = trace R N (f ∘ₗ g) := by
  have h := LinearMap.ext_iff.1 (LinearMap.ext_iff.1 (trace_comp_comm R M N) g) f
  simp only [llcomp_apply', compr₂_apply, flip_apply] at h
  exact h

@[simp]
/--
lemma `trace_smulRight` / 引理 `trace_smulRight`

English:
lemma trace_smulRight
  given: (f : M ->ₗ[R] R) (x : M)
  proof: by
  rw [trace_eq_matrix_trace _ (Free.chooseBasis R M)]; rw [← (Free.chooseBasis R M).sum_repr x]
  simp [-Basis.sum_repr, dotProduct]

中文:
引理 trace_smulRight
  条件: (f : M ->ₗ[R] R) (x : M)
  证明: by
  rw [trace_eq_matrix_trace _ (Free.chooseBasis R M)]; rw [← (Free.chooseBasis R M).sum_repr x]
  simp [-Basis.sum_repr, dotProduct]

Depends on / 依赖: Basis.sum_repr, Free.chooseBasis, chooseBasis, dotProduct, sum_repr, trace_eq_matrix_trace
-/
lemma trace_smulRight (f : M ->ₗ[R] R) (x : M) :
    trace R M (f.smulRight x) = f x := by
  rw [trace_eq_matrix_trace _ (Free.chooseBasis R M)]; rw [← (Free.chooseBasis R M).sum_repr x]
  simp [-Basis.sum_repr, dotProduct]

end

variable {N P}

variable [Module.Free R N] [Module.Finite R N] [Module.Free R P] [Module.Finite R P] in
/--
lemma `trace_comp_cycle` / 引理 `trace_comp_cycle`

English:
lemma trace_comp_cycle
  given: (f : M ->ₗ[R] N) (g : N ->ₗ[R] P) (h : P ->ₗ[R] M)
  proof: by
  rw [trace_comp_comm']; rw [comp_assoc]

中文:
引理 trace_comp_cycle
  条件: (f : M ->ₗ[R] N) (g : N ->ₗ[R] P) (h : P ->ₗ[R] M)
  证明: by
  rw [trace_comp_comm']; rw [comp_assoc]

Depends on / 依赖: comp_assoc, trace_comp_comm
-/
lemma trace_comp_cycle (f : M ->ₗ[R] N) (g : N ->ₗ[R] P) (h : P ->ₗ[R] M) :
    trace R P (g ∘ₗ f ∘ₗ h) = trace R N (f ∘ₗ h ∘ₗ g) := by
  rw [trace_comp_comm']; rw [comp_assoc]

variable [Module.Free R M] [Module.Finite R M] [Module.Free R P] [Module.Finite R P] in
/--
lemma `trace_comp_cycle'` / 引理 `trace_comp_cycle'`

English:
lemma trace_comp_cycle'
  given: (f : M ->ₗ[R] N) (g : N ->ₗ[R] P) (h : P ->ₗ[R] M)
  proof: by
  rw [trace_comp_comm']; rw [← comp_assoc]

@[simp]

中文:
引理 trace_comp_cycle'
  条件: (f : M ->ₗ[R] N) (g : N ->ₗ[R] P) (h : P ->ₗ[R] M)
  证明: by
  rw [trace_comp_comm']; rw [← comp_assoc]

@[simp]

Depends on / 依赖: comp_assoc, trace_comp_comm
-/
lemma trace_comp_cycle' (f : M ->ₗ[R] N) (g : N ->ₗ[R] P) (h : P ->ₗ[R] M) :
    trace R P ((g ∘ₗ f) ∘ₗ h) = trace R M ((h ∘ₗ g) ∘ₗ f) := by
  rw [trace_comp_comm']; rw [← comp_assoc]

@[simp]
/--
theorem `trace_conj'` / 定理 `trace_conj'`

English:
theorem trace_conj'
  given: (f : M ->ₗ[R] M) (e : M ≃ₗ[R] N)
  statement: trace R N (e.conj f) = trace R M f
  proof: by
  classical
  by_cases hM : exists s : Finset M, Nonempty (Basis s R M)
  · obtain ⟨s, ⟨b⟩⟩ := hM
    have := Module.Finite.of_basis b
    have := (Module.free_def R M).mpr ⟨_, ⟨b⟩⟩
    have := Module.Finite.of_basis (b.map e)
    have := (Module.free_def R N).mpr ⟨_, ⟨(b.map e).reindex (e.toEquiv.image _)⟩⟩
    rw [e.conj_apply]; rw [trace_comp_comm']; rw [← comp_assoc]; rw [LinearEquiv.comp_coe]; rw [LinearEquiv.self_trans_symm]; rw [LinearEquiv.refl_toLinearMap]; rw [id_comp]
  · rw [trace, trace, dif_neg hM, dif_neg ?_, zero_apply, zero_apply]
    rintro ⟨s, ⟨b⟩⟩
    exact hM ⟨s.image e.symm, ⟨(b.map e.symm).reindex
      ((e.symm.toEquiv.image s).trans (Equiv.setCongr Finset.coe_image.symm))⟩⟩

中文:
定理 trace_conj'
  条件: (f : M ->ₗ[R] M) (e : M ≃ₗ[R] N)
  结论: trace R N (e.conj f) = trace R M f
  证明: by
  classical
  by_cases hM : exists s : Finset M, Nonempty (Basis s R M)
  · obtain ⟨s, ⟨b⟩⟩ := hM
    have := Module.Finite.of_basis b
    have := (Module.free_def R M).mpr ⟨_, ⟨b⟩⟩
    have := Module.Finite.of_basis (b.map e)
    have := (Module.free_def R N).mpr ⟨_, ⟨(b.map e).reindex (e.toEquiv.image _)⟩⟩
    rw [e.conj_apply]; rw [trace_comp_comm']; rw [← comp_assoc]; rw [LinearEquiv.comp_coe]; rw [LinearEquiv.self_trans_symm]; rw [LinearEquiv.refl_toLinearMap]; rw [id_comp]
  · rw [trace, trace, dif_neg hM, dif_neg ?_, zero_apply, zero_apply]
    rintro ⟨s, ⟨b⟩⟩
    exact hM ⟨s.image e.symm, ⟨(b.map e.symm).reindex
      ((e.symm.toEquiv.image s).trans (Equiv.setCongr Finset.coe_image.symm))⟩⟩

Depends on / 依赖: Finite, Finset, LinearEquiv, LinearEquiv.comp_coe, LinearEquiv.refl_toLinearMap, LinearEquiv.self_trans_symm, Module, Module.Finite.of_basis, Module.free_def, Nonempty, b.map, classical, comp_assoc, comp_coe, conj_apply, dif_neg, e.conj_apply, e.toEquiv.image, free_def, id_comp
-/
theorem trace_conj' (f : M ->ₗ[R] M) (e : M ≃ₗ[R] N) : trace R N (e.conj f) = trace R M f := by
  classical
  by_cases hM : exists s : Finset M, Nonempty (Basis s R M)
  · obtain ⟨s, ⟨b⟩⟩ := hM
    have := Module.Finite.of_basis b
    have := (Module.free_def R M).mpr ⟨_, ⟨b⟩⟩
    have := Module.Finite.of_basis (b.map e)
    have := (Module.free_def R N).mpr ⟨_, ⟨(b.map e).reindex (e.toEquiv.image _)⟩⟩
    rw [e.conj_apply]; rw [trace_comp_comm']; rw [← comp_assoc]; rw [LinearEquiv.comp_coe]; rw [LinearEquiv.self_trans_symm]; rw [LinearEquiv.refl_toLinearMap]; rw [id_comp]
  · rw [trace, trace, dif_neg hM, dif_neg ?_, zero_apply, zero_apply]
    rintro ⟨s, ⟨b⟩⟩
    exact hM ⟨s.image e.symm, ⟨(b.map e.symm).reindex
      ((e.symm.toEquiv.image s).trans (Equiv.setCongr Finset.coe_image.symm))⟩⟩

/--
theorem `trace_map` / 定理 `trace_map`

English:
theorem trace_map
  statement: {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W]
  proof: have ⟨_, h⟩ := (AlgEquivClass.toAlgEquiv f).eq_linearEquivConjAlgEquiv
  (by simpa using congr($h x)) ▸ trace_conj' _ _

中文:
定理 trace_map
  结论: {K V W : 类型} [域 K] [加法交换群 V] [模 K V] [加法交换群 W]
  证明: have ⟨_, h⟩ := (AlgEquivClass.toAlgEquiv f).eq_linearEquivConjAlgEquiv
  (by simpa using congr($h x)) ▸ trace_conj' _ _
-/
@[simp] theorem trace_map {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W]
    [Module K W] {F : Type*} [EquivLike F (End K V) (End K W)] [AlgEquivClass F K _ _]
    (f : F) (x : End K V) : (f x).trace K W = x.trace K V :=
  have ⟨_, h⟩ := (AlgEquivClass.toAlgEquiv f).eq_linearEquivConjAlgEquiv
  (by simpa using congr($h x)) ▸ trace_conj' _ _

/--
theorem `_root_.Matrix.trace_map` / 定理 `_root_.Matrix.trace_map`

English:
theorem _root_.Matrix.trace_map
  statement: {K m n : Type*} [Field K] [Fintype m] [Fintype n]
  proof: by
  simpa [toMatrixAlgEquiv', Matrix.toLinAlgEquiv'] using
    LinearMap.trace_map ((Matrix.toLinAlgEquiv'.symm.trans
      (AlgEquivClass.toAlgEquiv f)).trans Matrix.toLinAlgEquiv') x.toLin'

中文:
定理 _root_.矩阵.trace_map
  结论: {K m n : 类型} [域 K] [有限类型 m] [有限类型 n]
  证明: by
  simpa [toMatrixAlgEquiv', Matrix.toLinAlgEquiv'] using
    LinearMap.trace_map ((Matrix.toLinAlgEquiv'.symm.trans
      (AlgEquivClass.toAlgEquiv f)).trans Matrix.toLinAlgEquiv') x.toLin'
-/
@[simp] theorem _root_.Matrix.trace_map {K m n : Type*} [Field K] [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] {F : Type*} [EquivLike F (Matrix m m K) (Matrix n n K)]
    [AlgEquivClass F K _ _] (f : F) (x : Matrix m m K) : (f x).trace = x.trace := by
  simpa [toMatrixAlgEquiv', Matrix.toLinAlgEquiv'] using
    LinearMap.trace_map ((Matrix.toLinAlgEquiv'.symm.trans
      (AlgEquivClass.toAlgEquiv f)).trans Matrix.toLinAlgEquiv') x.toLin'

/--
theorem `_root_.Matrix.trace_map'` / 定理 `_root_.Matrix.trace_map'`

English:
theorem _root_.Matrix.trace_map'
  statement: {K m F : Type*} [Field K] [Fintype m] [DecidableEq m]
  proof: by
  by_cases! Nonempty m
  · exact Matrix.trace_map (AlgEquiv.ofBijective _ (AlgHomClass.toAlgHom f).bijective) x
  · simp

中文:
定理 _root_.矩阵.trace_map'
  结论: {K m F : 类型} [域 K] [有限类型 m] [DecidableEq m]
  证明: by
  by_cases! Nonempty m
  · exact Matrix.trace_map (AlgEquiv.ofBijective _ (AlgHomClass.toAlgHom f).bijective) x
  · simp
-/
@[simp] theorem _root_.Matrix.trace_map' {K m F : Type*} [Field K] [Fintype m] [DecidableEq m]
    [FunLike F (Matrix m m K) (Matrix m m K)] [AlgHomClass F K _ _] (f : F) (x : Matrix m m K) :
    (f x).trace = x.trace := by
  by_cases! Nonempty m
  · exact Matrix.trace_map (AlgEquiv.ofBijective _ (AlgHomClass.toAlgHom f).bijective) x
  · simp

/--
theorem `IsProj.trace` / 定理 `IsProj.trace`

English:
theorem IsProj.trace
  statement: {p : Submodule R M} {f : M ->ₗ[R] M} (h : IsProj p f) [Module.Free R p]
  proof: by
  rw [h.eq_conj_prodMap]; rw [trace_conj']; rw [trace_prodMap']; rw [trace_id]; rw [map_zero]; rw [add_zero]

中文:
定理 是Proj.trace
  结论: {p : 子模 R M} {f : M ->ₗ[R] M} (h : 是Proj p f) [模.自由 R p]
  证明: by
  rw [h.eq_conj_prodMap]; rw [trace_conj']; rw [trace_prodMap']; rw [trace_id]; rw [map_zero]; rw [add_zero]

Depends on / 依赖: add_zero, eq_conj_prodMap, h.eq_conj_prodMap, map_zero, trace_conj, trace_id, trace_prodMap
-/
theorem IsProj.trace {p : Submodule R M} {f : M ->ₗ[R] M} (h : IsProj p f) [Module.Free R p]
    [Module.Finite R p] [Module.Free R (ker f)] [Module.Finite R (ker f)] :
    trace R M f = (finrank R p : R) := by
  rw [h.eq_conj_prodMap]; rw [trace_conj']; rw [trace_prodMap']; rw [trace_id]; rw [map_zero]; rw [add_zero]

open LinearMap in
/--
theorem `IsIdempotentElem.trace_eq_zero_iff` / 定理 `IsIdempotentElem.trace_eq_zero_iff`

English:
theorem IsIdempotentElem.trace_eq_zero_iff
  statement: {R : Type*} [CommRing R] [CharZero R]
  proof: by
  rw [he.isProj_range.trace]; rw [Nat.cast_eq_zero]; rw [finrank_eq_zero_iff_of_free]; rw [Submodule.subsingleton_iff_eq_bot]; rw [range_eq_bot]

alias ⟨IsIdempotentElem.eq_zero_of_trace_eq_zero, _⟩ := IsIdempotentElem.trace_eq_zero_iff

中文:
定理 IsIdempotentElem.trace_eq_zero_iff
  结论: {R : 类型} [交换环 R] [特征零 R]
  证明: by
  rw [he.isProj_range.trace]; rw [Nat.cast_eq_zero]; rw [finrank_eq_zero_iff_of_free]; rw [Submodule.subsingleton_iff_eq_bot]; rw [range_eq_bot]

alias ⟨IsIdempotentElem.eq_zero_of_trace_eq_zero, _⟩ := IsIdempotentElem.trace_eq_zero_iff

Depends on / 依赖: Nat.cast_eq_zero, Submodule, Submodule.subsingleton_iff_eq_bot, cast_eq_zero, finrank_eq_zero_iff_of_free, he.isProj_range.trace, isProj_range, range_eq_bot, subsingleton_iff_eq_bot
-/
theorem IsIdempotentElem.trace_eq_zero_iff {R : Type*} [CommRing R] [CharZero R]
    {M : Type*} [AddCommGroup M] [Module R M]
    {e : M ->ₗ[R] M} (he : IsIdempotentElem e)
    [Module.Free R (range e)] [Module.Finite R (range e)]
    [Module.Free R (ker e)] [Module.Finite R (ker e)] :
    trace R M e = 0 ↔ e = 0 := by
  rw [he.isProj_range.trace]; rw [Nat.cast_eq_zero]; rw [finrank_eq_zero_iff_of_free]; rw [Submodule.subsingleton_iff_eq_bot]; rw [range_eq_bot]

alias ⟨IsIdempotentElem.eq_zero_of_trace_eq_zero, _⟩ := IsIdempotentElem.trace_eq_zero_iff

/--
lemma `isNilpotent_trace_of_isNilpotent` / 引理 `isNilpotent_trace_of_isNilpotent`

English:
lemma isNilpotent_trace_of_isNilpotent
  given: {f : M ->ₗ[R] M} (hf : IsNilpotent f)
  proof: by
  by_cases H : exists s : Finset M, Nonempty (Basis s R M)
  swap
  · rw [LinearMap.trace, dif_neg H]
    exact IsNilpotent.zero
  obtain ⟨s, ⟨b⟩⟩ := H
  classical
  rw [trace_eq_matrix_trace R b]
  apply Matrix.isNilpotent_trace_of_isNilpotent
  simpa

中文:
引理 isNilpotent_trace_of_isNilpotent
  条件: {f : M ->ₗ[R] M} (hf : 是幂零 f)
  证明: by
  by_cases H : exists s : Finset M, Nonempty (Basis s R M)
  swap
  · rw [LinearMap.trace, dif_neg H]
    exact IsNilpotent.zero
  obtain ⟨s, ⟨b⟩⟩ := H
  classical
  rw [trace_eq_matrix_trace R b]
  apply Matrix.isNilpotent_trace_of_isNilpotent
  simpa

Depends on / 依赖: Finset, IsNilpotent, IsNilpotent.zero, LinearMap, LinearMap.trace, Matrix, Matrix.isNilpotent_trace_of_isNilpotent, Nonempty, classical, dif_neg, isNilpotent_trace_of_isNilpotent, trace_eq_matrix_trace
-/
lemma isNilpotent_trace_of_isNilpotent {f : M ->ₗ[R] M} (hf : IsNilpotent f) :
    IsNilpotent (trace R M f) := by
  by_cases H : exists s : Finset M, Nonempty (Basis s R M)
  swap
  · rw [LinearMap.trace, dif_neg H]
    exact IsNilpotent.zero
  obtain ⟨s, ⟨b⟩⟩ := H
  classical
  rw [trace_eq_matrix_trace R b]
  apply Matrix.isNilpotent_trace_of_isNilpotent
  simpa

/--
lemma `trace_comp_eq_mul_of_commute_of_isNilpotent` / 引理 `trace_comp_eq_mul_of_commute_of_isNilpotent`

English:
lemma trace_comp_eq_mul_of_commute_of_isNilpotent
  statement: [IsReduced R] {f g : Module.End R M}
  proof: by
  set n := g - algebraMap R _ μ
  replace hg : trace R M (f ∘ₗ n) = 0 := by
    rw [← isNilpotent_iff_eq_zero]; rw [← Module.End.mul_eq_comp]
    refine isNilpotent_trace_of_isNilpotent (Commute.isNilpotent_mul_left ?_ hg)
    exact h_comm.sub_right (Algebra.commute_algebraMap_right μ f)
  have hμ : g = algebraMap R _ μ + n := eq_add_of_sub_eq' rfl
  have : f ∘ₗ algebraMap R _ μ = μ • f := by ext; simp -- TODO Surely exists?
  rw [hμ]; rw [comp_add]; rw [map_add]; rw [hg]; rw [add_zero]; rw [this]; rw [map_smul]; rw [smul_eq_mul]

中文:
引理 trace_comp_eq_mul_of_commute_of_isNilpotent
  结论: [是既约 R] {f g : 模.End R M}
  证明: by
  set n := g - algebraMap R _ μ
  replace hg : trace R M (f ∘ₗ n) = 0 := by
    rw [← isNilpotent_iff_eq_zero]; rw [← Module.End.mul_eq_comp]
    refine isNilpotent_trace_of_isNilpotent (Commute.isNilpotent_mul_left ?_ hg)
    exact h_comm.sub_right (Algebra.commute_algebraMap_right μ f)
  have hμ : g = algebraMap R _ μ + n := eq_add_of_sub_eq' rfl
  have : f ∘ₗ algebraMap R _ μ = μ • f := by ext; simp -- TODO Surely exists?
  rw [hμ]; rw [comp_add]; rw [map_add]; rw [hg]; rw [add_zero]; rw [this]; rw [map_smul]; rw [smul_eq_mul]

Depends on / 依赖: Algebra, Algebra.commute_algebraMap_right, Commute, Commute.isNilpotent_mul_left, Module, Module.End.mul_eq_comp, Surely, add_zero, algebraMap, commute_algebraMap_right, comp_add, eq_add_of_sub_eq, h_comm, h_comm.sub_right, isNilpotent_iff_eq_zero, isNilpotent_mul_left, isNilpotent_trace_of_isNilpotent, map_add, map_smul, mul_eq_comp
-/
lemma trace_comp_eq_mul_of_commute_of_isNilpotent [IsReduced R] {f g : Module.End R M}
    (μ : R) (h_comm : Commute f g) (hg : IsNilpotent (g - algebraMap R _ μ)) :
    trace R M (f ∘ₗ g) = μ * trace R M f := by
  set n := g - algebraMap R _ μ
  replace hg : trace R M (f ∘ₗ n) = 0 := by
    rw [← isNilpotent_iff_eq_zero]; rw [← Module.End.mul_eq_comp]
    refine isNilpotent_trace_of_isNilpotent (Commute.isNilpotent_mul_left ?_ hg)
    exact h_comm.sub_right (Algebra.commute_algebraMap_right μ f)
  have hμ : g = algebraMap R _ μ + n := eq_add_of_sub_eq' rfl
  have : f ∘ₗ algebraMap R _ μ = μ • f := by ext; simp -- TODO Surely exists?
  rw [hμ]; rw [comp_add]; rw [map_add]; rw [hg]; rw [add_zero]; rw [this]; rw [map_smul]; rw [smul_eq_mul]

-- This result requires `Mathlib/RingTheory/TensorProduct/Free.lean`.
-- Maybe it should move elsewhere?
@[simp]
/--
lemma `trace_baseChange` / 引理 `trace_baseChange`

English:
lemma trace_baseChange
  statement: [Module.Free R M] [Module.Finite R M]
  proof: by
  let b := Module.Free.chooseBasis R M
  let b' := Algebra.TensorProduct.basis A b
  change _ = (algebraMap R A : R ->+ A) _
  simp [b', trace_eq_matrix_trace R b, trace_eq_matrix_trace A b', AddMonoidHom.map_trace]

中文:
引理 trace_baseChange
  结论: [模.自由 R M] [模.有限 R M]
  证明: by
  let b := Module.Free.chooseBasis R M
  let b' := Algebra.TensorProduct.basis A b
  change _ = (algebraMap R A : R ->+ A) _
  simp [b', trace_eq_matrix_trace R b, trace_eq_matrix_trace A b', AddMonoidHom.map_trace]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.map_trace, Algebra, Algebra.TensorProduct.basis, Module, Module.Free.chooseBasis, TensorProduct, algebraMap, chooseBasis, map_trace, trace_eq_matrix_trace
-/
lemma trace_baseChange [Module.Free R M] [Module.Finite R M]
    (f : M ->ₗ[R] M) (A : Type*) [CommRing A] [Algebra R A] :
    trace A _ (f.baseChange A) = algebraMap R A (trace R _ f) := by
  let b := Module.Free.chooseBasis R M
  let b' := Algebra.TensorProduct.basis A b
  change _ = (algebraMap R A : R ->+ A) _
  simp [b', trace_eq_matrix_trace R b, trace_eq_matrix_trace A b', AddMonoidHom.map_trace]

end

end LinearMap

/--
lemma `Module.Free.bijective_algebraMap_of_finrank_eq_one` / 引理 `Module.Free.bijective_algebraMap_of_finrank_eq_one`

English:
lemma Module.Free.bijective_algebraMap_of_finrank_eq_one
  statement: {R S : Type*} [CommRing R] [Ring S]
  proof: by
  have : Module.Finite R S := finite_of_finrank_pos (by grind)
  have : Free R (Module.End R S) := .of_equiv (dualTensorHomEquiv R S S)
  let f : S ->ₐ[R] (S ->ₗ[R] S) := Algebra.lmul R S
  have h1 : LinearMap.trace R S ∘ₗ f ∘ₗ Algebra.linearMap R S = LinearMap.id := by ext; simp [h]
  let b : Basis (Unit × Unit) R (End R S) :=
    .map (.tensorProduct (.dualBasis <| basisUnique Unit h) (basisUnique Unit h))
      (dualTensorHomEquiv R S S)
  have h2 : (f ∘ₗ Algebra.linearMap R S) ∘ₗ LinearMap.trace R S = LinearMap.id :=
    b.ext fun i =>
      (basisUnique Unit h).ext fun j => (by simp [f, b, Basis.tensorProduct])
  let eq : R ≃ₗ[R] End R S := .ofLinearMap (f ∘ₗ Algebra.linearMap R S) (.trace R S) h2 h1
  have hf : Function.Bijective f := ⟨Algebra.lmul_injective, .of_comp eq.surjective⟩
  exact (Function.Bijective.of_comp_iff' hf _).mp eq.bijective

中文:
引理 模.自由.bijective_algebraMap_of_finrank_eq_one
  结论: {R S : 类型} [交换环 R] [环 S]
  证明: by
  have : Module.Finite R S := finite_of_finrank_pos (by grind)
  have : Free R (Module.End R S) := .of_equiv (dualTensorHomEquiv R S S)
  let f : S ->ₐ[R] (S ->ₗ[R] S) := Algebra.lmul R S
  have h1 : LinearMap.trace R S ∘ₗ f ∘ₗ Algebra.linearMap R S = LinearMap.id := by ext; simp [h]
  let b : Basis (Unit × Unit) R (End R S) :=
    .map (.tensorProduct (.dualBasis <| basisUnique Unit h) (basisUnique Unit h))
      (dualTensorHomEquiv R S S)
  have h2 : (f ∘ₗ Algebra.linearMap R S) ∘ₗ LinearMap.trace R S = LinearMap.id :=
    b.ext fun i =>
      (basisUnique Unit h).ext fun j => (by simp [f, b, Basis.tensorProduct])
  let eq : R ≃ₗ[R] End R S := .ofLinearMap (f ∘ₗ Algebra.linearMap R S) (.trace R S) h2 h1
  have hf : Function.Bijective f := ⟨Algebra.lmul_injective, .of_comp eq.surjective⟩
  exact (Function.Bijective.of_comp_iff' hf _).mp eq.bijective

Depends on / 依赖: Algebra, Algebra.linearMap, Algebra.lmul, Finite, LinearMa, LinearMap, LinearMap.id, LinearMap.trace, Module, Module.End, Module.Finite, basisUnique, dualBasis, dualTensorHomEquiv, finite_of_finrank_pos, linearMap, of_equiv, tensorProduct
-/
lemma Module.Free.bijective_algebraMap_of_finrank_eq_one {R S : Type*} [CommRing R] [Ring S]
    [Algebra R S] [Nontrivial R] [Free R S] (h : finrank R S = 1) :
    Function.Bijective (algebraMap R S) := by
  have : Module.Finite R S := finite_of_finrank_pos (by grind)
  have : Free R (Module.End R S) := .of_equiv (dualTensorHomEquiv R S S)
  let f : S ->ₐ[R] (S ->ₗ[R] S) := Algebra.lmul R S
  have h1 : LinearMap.trace R S ∘ₗ f ∘ₗ Algebra.linearMap R S = LinearMap.id := by ext; simp [h]
  let b : Basis (Unit × Unit) R (End R S) :=
    .map (.tensorProduct (.dualBasis <| basisUnique Unit h) (basisUnique Unit h))
      (dualTensorHomEquiv R S S)
  have h2 : (f ∘ₗ Algebra.linearMap R S) ∘ₗ LinearMap.trace R S = LinearMap.id :=
    b.ext fun i =>
      (basisUnique Unit h).ext fun j => (by simp [f, b, Basis.tensorProduct])
  let eq : R ≃ₗ[R] End R S := .ofLinearMap (f ∘ₗ Algebra.linearMap R S) (.trace R S) h2 h1
  have hf : Function.Bijective f := ⟨Algebra.lmul_injective, .of_comp eq.surjective⟩
  exact (Function.Bijective.of_comp_iff' hf _).mp eq.bijective
