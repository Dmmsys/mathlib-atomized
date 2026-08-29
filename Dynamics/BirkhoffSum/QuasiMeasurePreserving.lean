/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Lua Viana Reis
-/
module

public import Mathlib.Dynamics.BirkhoffSum.Average
public import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

/-!
# Birkhoff sum and average for quasi-measure-preserving maps

Given a map `f` and measure `μ`, under the assumption of `QuasiMeasurePreserving f μ μ` we prove:

- `birkhoffSum_ae_eq_of_ae_eq`: if observables `φ` and `ψ` are `μ`-a.e. equal then the
  corresponding `birkhoffSum f` are `μ`-a.e. equal.

- `birkhoffAverage_ae_eq_of_ae_eq`: if observables `φ` and `ψ` are `μ`-a.e. equal then the
  corresponding `birkhoffAverage R f` are `μ`-a.e. equal.

-/

public section

namespace MeasureTheory.Measure.QuasiMeasurePreserving

open Filter

variable {α M : Type*} [MeasurableSpace α] [AddCommMonoid M]
variable {f : α -> α} {μ : Measure α} {φ ψ : α -> M}

/--
theorem `birkhoffSum_ae_eq_of_ae_eq` / 定理 `birkhoffSum_ae_eq_of_ae_eq`

English:
theorem birkhoffSum_ae_eq_of_ae_eq
  given: (hf : QuasiMeasurePreserving f μ μ) (hφ : φ =ᵐ[μ] ψ) n
  proof: by
  apply Eventually.mono _ (fun _ => Finset.sum_congr rfl)
  apply ae_all_iff.mpr (fun i => ?_)
  exact (hf.iterate i).ae (hφ.mono (fun _ h _ => h))

中文:
定理 birkhoffSum_ae_eq_of_ae_eq
  条件: (hf : QuasiMeasurePreserving f μ μ) (hφ : φ =ᵐ[μ] ψ) n
  证明: by
  apply Eventually.mono _ (fun _ => Finset.sum_congr rfl)
  apply ae_all_iff.mpr (fun i => ?_)
  exact (hf.iterate i).ae (hφ.mono (fun _ h _ => h))

Depends on / 依赖: Eventually, Eventually.mono, Finset, Finset.sum_congr, ae_all_iff, ae_all_iff.mpr, hf.iterate, iterate, sum_congr
-/
theorem birkhoffSum_ae_eq_of_ae_eq (hf : QuasiMeasurePreserving f μ μ) (hφ : φ =ᵐ[μ] ψ) n :
    birkhoffSum f φ n =ᵐ[μ] birkhoffSum f ψ n := by
  apply Eventually.mono _ (fun _ => Finset.sum_congr rfl)
  apply ae_all_iff.mpr (fun i => ?_)
  exact (hf.iterate i).ae (hφ.mono (fun _ h _ => h))

/--
theorem `birkhoffAverage_ae_eq_of_ae_eq` / 定理 `birkhoffAverage_ae_eq_of_ae_eq`

English:
theorem birkhoffAverage_ae_eq_of_ae_eq
  statement: (R : Type*) [DivisionSemiring R] [Module R M]
  proof: EventuallyEq.const_smul (birkhoffSum_ae_eq_of_ae_eq hf hφ n) (n : R)⁻¹

中文:
定理 birkhoffAverage_ae_eq_of_ae_eq
  结论: (R : 类型) [DivisionSemiring R] [Module R M]
  证明: EventuallyEq.const_smul (birkhoffSum_ae_eq_of_ae_eq hf hφ n) (n : R)⁻¹

Depends on / 依赖: EventuallyEq, EventuallyEq.const_smul, birkhoffSum_ae_eq_of_ae_eq, const_smul
-/
theorem birkhoffAverage_ae_eq_of_ae_eq (R : Type*) [DivisionSemiring R] [Module R M]
    (hf : QuasiMeasurePreserving f μ μ) (hφ : φ =ᵐ[μ] ψ) n :
    birkhoffAverage R f φ n =ᵐ[μ] birkhoffAverage R f ψ n :=
  EventuallyEq.const_smul (birkhoffSum_ae_eq_of_ae_eq hf hφ n) (n : R)⁻¹

end MeasureTheory.Measure.QuasiMeasurePreserving
