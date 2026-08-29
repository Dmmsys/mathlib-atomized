/-
Copyright (c) 2025 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.PowerSeries.Basic

/-!

# Some results on the coefficients of multiplication of two power series

## Main results

- `PowerSeries.coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal`,
  `PowerSeries.coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal'`:
  if for all `i ≤ n` (resp. for all `i`), the `i`-th coefficients of power series `f` and `g` are
  in ideals `I` and `J`, respectively, then for all `i ≤ n` (resp. for all `i`), the `i`-th
  coefficients of `f * g` are in `I * J`.

- `PowerSeries.coeff_mul_mem_ideal_of_coeff_right_mem_ideal`,
  `PowerSeries.coeff_mul_mem_ideal_of_coeff_right_mem_ideal'`:
  if for all `i ≤ n` (resp. for all `i`), the `i`-th coefficients of power series `g` are
  in ideal `I`, then for all `i ≤ n` (resp. for all `i`), the `i`-th coefficients of `f * g` are
  in `I`.

- `PowerSeries.coeff_mul_mem_ideal_of_coeff_left_mem_ideal`,
  `PowerSeries.coeff_mul_mem_ideal_of_coeff_left_mem_ideal'`:
  if for all `i ≤ n` (resp. for all `i`), the `i`-th coefficients of power series `f` are
  in ideal `I`, then for all `i ≤ n` (resp. for all `i`), the `i`-th coefficients of `f * g` are
  in `I`.

-/

public section

namespace PowerSeries

variable {A : Type*} [Semiring A] {I J : Ideal A} {f g : A⟦X⟧} (n : Nat)

/--
theorem `coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal` / 定理 `coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal`

English:
theorem coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal
  statement: (hf : forall i <= n, coeff i f in I)
  proof: fun i hi => by
  rw [coeff_mul]
  exact Ideal.sum_mem _ fun p hp => Ideal.mul_mem_mul
    (hf _ ((Finset.HasAntidiagonal.antidiagonal.fst_le hp).trans hi))
    (hg _ ((Finset.HasAntidiagonal.antidiagonal.snd_le hp).trans hi))

中文:
定理 coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal
  结论: (hf : 对任意 i <= n, coeff i f in I)
  证明: fun i hi => by
  rw [coeff_mul]
  exact Ideal.sum_mem _ fun p hp => Ideal.mul_mem_mul
    (hf _ ((Finset.HasAntidiagonal.antidiagonal.fst_le hp).trans hi))
    (hg _ ((Finset.HasAntidiagonal.antidiagonal.snd_le hp).trans hi))

Depends on / 依赖: Finset, Finset.HasAntidiagonal.antidiagonal.fst_le, Finset.HasAntidiagonal.antidiagonal.snd_le, HasAntidiagonal, Ideal.mul_mem_mul, Ideal.sum_mem, antidiagonal, coeff_mul, fst_le, mul_mem_mul, snd_le, sum_mem
-/
theorem coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal (hf : forall i <= n, coeff i f in I)
    (hg : forall i <= n, coeff i g in J) : forall i <= n, coeff i (f * g) in I * J := fun i hi => by
  rw [coeff_mul]
  exact Ideal.sum_mem _ fun p hp => Ideal.mul_mem_mul
    (hf _ ((Finset.HasAntidiagonal.antidiagonal.fst_le hp).trans hi))
    (hg _ ((Finset.HasAntidiagonal.antidiagonal.snd_le hp).trans hi))

/--
theorem `coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal'` / 定理 `coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal'`

English:
theorem coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal'
  statement: (hf : forall i, coeff i f in I)
  proof: fun i => coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal i
    (fun i _ => hf i) (fun i _ => hg i) i le_rfl

中文:
定理 coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal'
  结论: (hf : 对任意 i, coeff i f in I)
  证明: fun i => coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal i
    (fun i _ => hf i) (fun i _ => hg i) i le_rfl

Depends on / 依赖: coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal, le_rfl
-/
theorem coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal' (hf : forall i, coeff i f in I)
    (hg : forall i, coeff i g in J) : forall i, coeff i (f * g) in I * J :=
  fun i => coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal i
    (fun i _ => hf i) (fun i _ => hg i) i le_rfl

/--
theorem `coeff_mul_mem_ideal_of_coeff_right_mem_ideal` / 定理 `coeff_mul_mem_ideal_of_coeff_right_mem_ideal`

English:
theorem coeff_mul_mem_ideal_of_coeff_right_mem_ideal
  proof: by
  simpa using coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal (I := ⊤) (f := f) n (by simp) hg

中文:
定理 coeff_mul_mem_ideal_of_coeff_right_mem_ideal
  证明: by
  simpa using coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal (I := ⊤) (f := f) n (by simp) hg

Depends on / 依赖: coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal
-/
theorem coeff_mul_mem_ideal_of_coeff_right_mem_ideal
    (hg : forall i <= n, coeff i g in I) : forall i <= n, coeff i (f * g) in I := by
  simpa using coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal (I := ⊤) (f := f) n (by simp) hg

/--
theorem `coeff_mul_mem_ideal_of_coeff_right_mem_ideal'` / 定理 `coeff_mul_mem_ideal_of_coeff_right_mem_ideal'`

English:
theorem coeff_mul_mem_ideal_of_coeff_right_mem_ideal'
  proof: by
  simpa using coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal' (I := ⊤) (f := f) (by simp) hg

中文:
定理 coeff_mul_mem_ideal_of_coeff_right_mem_ideal'
  证明: by
  simpa using coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal' (I := ⊤) (f := f) (by simp) hg

Depends on / 依赖: coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal
-/
theorem coeff_mul_mem_ideal_of_coeff_right_mem_ideal'
    (hg : forall i, coeff i g in I) : forall i, coeff i (f * g) in I := by
  simpa using coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal' (I := ⊤) (f := f) (by simp) hg

variable [I.IsTwoSided]

/--
theorem `coeff_mul_mem_ideal_of_coeff_left_mem_ideal` / 定理 `coeff_mul_mem_ideal_of_coeff_left_mem_ideal`

English:
theorem coeff_mul_mem_ideal_of_coeff_left_mem_ideal
  proof: by
  simpa only [Ideal.IsTwoSided.mul_one] using
    coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal (J := 1) (g := g) n hf (by simp)

中文:
定理 coeff_mul_mem_ideal_of_coeff_left_mem_ideal
  证明: by
  simpa only [Ideal.IsTwoSided.mul_one] using
    coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal (J := 1) (g := g) n hf (by simp)

Depends on / 依赖: Ideal.IsTwoSided.mul_one, IsTwoSided, coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal, mul_one
-/
theorem coeff_mul_mem_ideal_of_coeff_left_mem_ideal
    (hf : forall i <= n, coeff i f in I) : forall i <= n, coeff i (f * g) in I := by
  simpa only [Ideal.IsTwoSided.mul_one] using
    coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal (J := 1) (g := g) n hf (by simp)

/--
theorem `coeff_mul_mem_ideal_of_coeff_left_mem_ideal'` / 定理 `coeff_mul_mem_ideal_of_coeff_left_mem_ideal'`

English:
theorem coeff_mul_mem_ideal_of_coeff_left_mem_ideal'
  proof: by
  simpa only [Ideal.IsTwoSided.mul_one] using
    coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal' (J := 1) (g := g) hf (by simp)

中文:
定理 coeff_mul_mem_ideal_of_coeff_left_mem_ideal'
  证明: by
  simpa only [Ideal.IsTwoSided.mul_one] using
    coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal' (J := 1) (g := g) hf (by simp)

Depends on / 依赖: Ideal.IsTwoSided.mul_one, IsTwoSided, coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal, mul_one
-/
theorem coeff_mul_mem_ideal_of_coeff_left_mem_ideal'
    (hf : forall i, coeff i f in I) : forall i, coeff i (f * g) in I := by
  simpa only [Ideal.IsTwoSided.mul_one] using
    coeff_mul_mem_ideal_mul_ideal_of_coeff_mem_ideal' (J := 1) (g := g) hf (by simp)

end PowerSeries
