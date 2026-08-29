/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# Linear maps of modules with coefficients in a principal ideal domain

Since a submodule of a free module over a PID is free, certain constructions which are often
developed only for vector spaces may be generalised to any module with coefficients in a PID.

This file is a location for such results and exists to avoid making large parts of the linear
algebra import hierarchy have to depend on the theory of PIDs.

## Main results:
* `LinearMap.trace_restrict_eq_of_forall_mem`

-/

public section

namespace LinearMap

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [Module.Finite R M] [Module.Free R M]

/--
lemma `trace_restrict_eq_of_forall_mem` / 引理 `trace_restrict_eq_of_forall_mem`

English:
lemma trace_restrict_eq_of_forall_mem
  statement: [IsDomain R] [IsPrincipalIdealRing R]
  proof: by
  let ι := Module.Free.ChooseBasisIndex R M
  obtain ⟨n, snf⟩ := p.smithNormalForm (Module.Free.chooseBasis R M)
  rw [trace_eq_matrix_trace R snf.bM]; rw [trace_eq_matrix_trace R snf.bN]
  set A : Matrix (Fin n) (Fin n) R := toMatrix snf.bN snf.bN (f.restrict hf')
  set B : Matrix ι ι R := toMatrix snf.bM snf.bM f
  have aux : forall i, B i i != 0 -> i in Set.range snf.f := fun i hi => by
    contrapose hi; exact snf.repr_eq_zero_of_notMem_range ⟨_, (hf _)⟩ hi
  change ∑ i, A i i = ∑ i, B i i
  rw [← Finset.sum_filter_of_ne (p := fun j => j in Set.range snf.f) (by simpa using aux)]
  simp [A, B, hf, Finset.sum_image snf.f.injective.injOn]

中文:
引理 trace_restrict_eq_of_对任意_mem
  结论: [是整环 R] [是主理想环 R]
  证明: by
  let ι := Module.Free.ChooseBasisIndex R M
  obtain ⟨n, snf⟩ := p.smithNormalForm (Module.Free.chooseBasis R M)
  rw [trace_eq_matrix_trace R snf.bM]; rw [trace_eq_matrix_trace R snf.bN]
  set A : Matrix (Fin n) (Fin n) R := toMatrix snf.bN snf.bN (f.restrict hf')
  set B : Matrix ι ι R := toMatrix snf.bM snf.bM f
  have aux : forall i, B i i != 0 -> i in Set.range snf.f := fun i hi => by
    contrapose hi; exact snf.repr_eq_zero_of_notMem_range ⟨_, (hf _)⟩ hi
  change ∑ i, A i i = ∑ i, B i i
  rw [← Finset.sum_filter_of_ne (p := fun j => j in Set.range snf.f) (by simpa using aux)]
  simp [A, B, hf, Finset.sum_image snf.f.injective.injOn]
-/
lemma trace_restrict_eq_of_forall_mem [IsDomain R] [IsPrincipalIdealRing R]
    (p : Submodule R M) (f : M ->ₗ[R] M)
    (hf : forall x, f x in p) (hf' : forall x in p, f x in p := fun x _ => hf x) :
    trace R p (f.restrict hf') = trace R M f := by
  let ι := Module.Free.ChooseBasisIndex R M
  obtain ⟨n, snf⟩ := p.smithNormalForm (Module.Free.chooseBasis R M)
  rw [trace_eq_matrix_trace R snf.bM]; rw [trace_eq_matrix_trace R snf.bN]
  set A : Matrix (Fin n) (Fin n) R := toMatrix snf.bN snf.bN (f.restrict hf')
  set B : Matrix ι ι R := toMatrix snf.bM snf.bM f
  have aux : forall i, B i i != 0 -> i in Set.range snf.f := fun i hi => by
    contrapose hi; exact snf.repr_eq_zero_of_notMem_range ⟨_, (hf _)⟩ hi
  change ∑ i, A i i = ∑ i, B i i
  rw [← Finset.sum_filter_of_ne (p := fun j => j in Set.range snf.f) (by simpa using aux)]
  simp [A, B, hf, Finset.sum_image snf.f.injective.injOn]

end LinearMap
