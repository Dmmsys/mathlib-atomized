/-
Copyright (c) 2023 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.Trace.Defs

/-!
# Relation between norms and traces
-/

public section

open Module

/--
lemma `Algebra.norm_one_add_smul` / 引理 `Algebra.norm_one_add_smul`

English:
lemma Algebra.norm_one_add_smul
  statement: {A B} [CommRing A] [CommRing B] [Algebra A B]
  proof: by
  classical
  let ι := Module.Free.ChooseBasisIndex A B
  let b : Basis ι A B := Module.Free.chooseBasis _ _
  have : Fintype ι := inferInstance
  clear_value ι b
  simp_rw [Algebra.norm_eq_matrix_det b, Algebra.trace_eq_matrix_trace b]
  simp only [map_add, map_one, map_smul, Matrix.det_one_add_

中文:
引理 代数.norm_one_add_smul
  结论: {A B} [交换环 A] [交换环 B] [代数 A B]
  证明: by
  classical
  let ι := Module.Free.ChooseBasisIndex A B
  let b : Basis ι A B := Module.Free.chooseBasis _ _
  have : Fintype ι := inferInstance
  clear_value ι b
  simp_rw [Algebra.norm_eq_matrix_det b, Algebra.trace_eq_matrix_trace b]
  simp only [map_add, map_one, map_smul, Matrix.det_one_add_

Depends on / 依赖: Algebra, Algebra.norm_eq_matrix_det, Algebra.trace_eq_matrix_trace, ChooseBasisIndex, Fintype, Matrix, Matrix.det_one_add_smul, Module, Module.Free.ChooseBasisIndex, Module.Free.chooseBasis, chooseBasis, classical, clear_value, det_one_add_smul, map_add, map_one, map_smul, norm_eq_matrix_det, simp_rw, trace_eq_matrix_trace
-/
lemma Algebra.norm_one_add_smul {A B} [CommRing A] [CommRing B] [Algebra A B]
    [Module.Free A B] [Module.Finite A B] (a : A) (x : B) :
    exists r : A, Algebra.norm A (1 + a • x) = 1 + Algebra.trace A B x * a + r * a ^ 2 := by
  classical
  let ι := Module.Free.ChooseBasisIndex A B
  let b : Basis ι A B := Module.Free.chooseBasis _ _
  have : Fintype ι := inferInstance
  clear_value ι b
  simp_rw [Algebra.norm_eq_matrix_det b, Algebra.trace_eq_matrix_trace b]
  simp only [map_add, map_one, map_smul, Matrix.det_one_add_smul a]
  exact ⟨_, rfl⟩
