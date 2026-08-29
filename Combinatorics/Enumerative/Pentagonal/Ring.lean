/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Combinatorics.Enumerative.Pentagonal.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Topology.Algebra.TopologicallyNilpotent

/-!
# Pentagonal number theorem

This is an intermediate file that proves the pentagonal number theorem in a general topological ring
modulo summability and multipliability. The complete proof for formal power series is in
`Mathlib/RingTheory/PowerSeries/Pentagonal.lean`. TODO: also prove for real/complex numbers.

## Declarations

* `Pentagonal.tprod_one_sub_pow`: pentagonal number theorem with a few summability and
  multipliability assumptions.

## References

https://math.stackexchange.com/questions/55738/how-to-prove-eulers-pentagonal-theorem-some-hints-will-help

-/

namespace Pentagonal
open Filter Topology
variable {R : Type*} [CommRing R]

/--
Definition of `powMulProdOneSubPow` / `powMulProdOneSubPow` 的定义

English:
definition powMulProdOneSubPow
  signature: (k n : Nat) (x : R)
  body: x ^ ((k + 1) * n) * ∏ i in Finset.range (n + 1), (1 - x ^ (k + i + 1))

中文:
定义 powMulProdOneSubPow
  签名: (k n : 自然数) (x : R)
  定义体: x ^ ((k + 1) * n) * ∏ i in Finset.range (n + 1), (1 - x ^ (k + i + 1))

Depends on / 依赖: Finset, Finset.range
-/
def powMulProdOneSubPow (k n : Nat) (x : R) : R :=
  x ^ ((k + 1) * n) * ∏ i in Finset.range (n + 1), (1 - x ^ (k + i + 1))

/--
Definition of `aux` / `aux` 的定义

English:
definition aux
  signature: (k n : Nat) (x : R)
  body: x ^ ((k + 1) * n) * (x ^ (2 * k + n + 3) - 1) * ∏ i in Finset.range n, (1 - x ^ (k + i + 2))

中文:
定义 aux
  签名: (k n : 自然数) (x : R)
  定义体: x ^ ((k + 1) * n) * (x ^ (2 * k + n + 3) - 1) * ∏ i in Finset.range n, (1 - x ^ (k + i + 2))

Depends on / 依赖: Finset, Finset.range
-/
def aux (k n : Nat) (x : R) : R :=
  x ^ ((k + 1) * n) * (x ^ (2 * k + n + 3) - 1) * ∏ i in Finset.range n, (1 - x ^ (k + i + 2))

/--
theorem `aux_sub_aux` / 定理 `aux_sub_aux`

English:
theorem aux_sub_aux
  given: (k n : Nat) (x : R)
  proof: by
  simp_rw [aux, Finset.prod_range_succ, powMulProdOneSubPow]
  rw [Finset.prod_range_succ']; rw [Finset.prod_range_succ]
  ring_nf

中文:
定理 aux_sub_aux
  条件: (k n : 自然数) (x : R)
  证明: by
  simp_rw [aux, Finset.prod_range_succ, powMulProdOneSubPow]
  rw [Finset.prod_range_succ']; rw [Finset.prod_range_succ]
  ring_nf

Depends on / 依赖: Finset, Finset.prod_range_succ, powMulProdOneSubPow, prod_range_succ, ring_nf, simp_rw
-/
theorem aux_sub_aux (k n : Nat) (x : R) :
    powMulProdOneSubPow k n x + x ^ (3 * k + 5) * powMulProdOneSubPow (k + 1) n x =
    aux k (n + 1) x - aux k n x := by
  simp_rw [aux, Finset.prod_range_succ, powMulProdOneSubPow]
  rw [Finset.prod_range_succ']; rw [Finset.prod_range_succ]
  ring_nf

variable [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]

/--
theorem `tsum_powMulProdOneSubPow` / 定理 `tsum_powMulProdOneSubPow`

English:
theorem tsum_powMulProdOneSubPow
  statement: (k : Nat) {x : R} (hx : IsTopologicallyNilpotent x)
  proof: by
  rw [eq_sub_iff_add_eq]; rw [show 1 - x ^ (2 * k + 3) = 0 - aux k 0 x by simp [aux]]
  rw [← (hsum _).tsum_mul_left]; rw [← (hsum _).tsum_add ((hsum _).mul_left _)]
  apply HasSum.tsum_eq
  rw [((hsum _).add ((hsum _).mul_left _)).hasSum_iff_tendsto_nat]
  simp_rw [aux_sub_aux, Finset.sum_range_

中文:
定理 tsum_powMulProdOneSubPow
  结论: (k : 自然数) {x : R} (hx : IsTopologicallyNilpotent x)
  证明: by
  rw [eq_sub_iff_add_eq]; rw [show 1 - x ^ (2 * k + 3) = 0 - aux k 0 x by simp [aux]]
  rw [← (hsum _).tsum_mul_left]; rw [← (hsum _).tsum_add ((hsum _).mul_left _)]
  apply HasSum.tsum_eq
  rw [((hsum _).add ((hsum _).mul_left _)).hasSum_iff_tendsto_nat]
  simp_rw [aux_sub_aux, Finset.sum_range_

Depends on / 依赖: Finset, Finset.sum_range_sub, HasSum, HasSum.tsum_eq, Tendsto, Tendsto.mul, Tendsto.sub_const, aux_sub_aux, eq_sub_iff_add_eq, hasSum_iff_tendsto_nat, hx.comp, mul_left, simp_rw, strictMono_mul_left_of_pos, sub_const, sum_range_sub, tsum_add, tsum_eq, tsum_mul_left
-/
theorem tsum_powMulProdOneSubPow (k : Nat) {x : R} (hx : IsTopologicallyNilpotent x)
    (hsum : forall k, Summable (powMulProdOneSubPow k · x))
    (h : forall k, Multipliable (fun n => 1 - x ^ (n + k + 1))) :
    ∑' n, powMulProdOneSubPow k n x =
      1 - x ^ (2 * k + 3) - x ^ (3 * k + 5) * ∑' n, powMulProdOneSubPow (k + 1) n x := by
  rw [eq_sub_iff_add_eq]; rw [show 1 - x ^ (2 * k + 3) = 0 - aux k 0 x by simp [aux]]
  rw [← (hsum _).tsum_mul_left]; rw [← (hsum _).tsum_add ((hsum _).mul_left _)]
  apply HasSum.tsum_eq
  rw [((hsum _).add ((hsum _).mul_left _)).hasSum_iff_tendsto_nat]
  simp_rw [aux_sub_aux, Finset.sum_range_sub (aux k · x)]
  apply Tendsto.sub_const
  rw [show 𝓝 0 = 𝓝 (0 * (0 - 1) * ∏' i]; rw [(1 - x ^ (k + i + 2))) by simp]
  refine (Tendsto.mul ?_ ?_).mul ?_
  · exact hx.comp (strictMono_mul_left_of_pos (by simp)).tendsto_atTop
  · exact (hx.comp (add_right_strictMono.add_monotone monotone_const).tendsto_atTop).sub_const _
  · apply Multipliable.tendsto_prod_tprod_nat
    convert h (k + 1) using 4
    ring

/--
theorem `tprod_one_sub_pow_eq_powMulProdOneSubPow_zero` / 定理 `tprod_one_sub_pow_eq_powMulProdOneSubPow_zero`

English:
theorem tprod_one_sub_pow_eq_powMulProdOneSubPow_zero
  statement: {x : R}
  proof: by
  have hsum := hsum 0
  simp_rw [powMulProdOneSubPow, zero_add, one_mul] at hsum
  have hsum' : Summable fun i => x ^ (i + 1) * ∏ n in Finset.range i, (1 - x ^ (n + 1)) := by
    apply Summable.comp_nat_add (k := 1)
    conv in fun k => _ =>
      ext k
      rw [pow_add]; rw [pow_add]; rw [mul_a

中文:
定理 tprod_one_sub_pow_eq_powMulProdOneSubPow_zero
  结论: {x : R}
  证明: by
  have hsum := hsum 0
  simp_rw [powMulProdOneSubPow, zero_add, one_mul] at hsum
  have hsum' : Summable fun i => x ^ (i + 1) * ∏ n in Finset.range i, (1 - x ^ (n + 1)) := by
    apply Summable.comp_nat_add (k := 1)
    conv in fun k => _ =>
      ext k
      rw [pow_add]; rw [pow_add]; rw [mul_a

Depends on / 依赖: Finset, Finset.range, Iio_eq_range, Nat.Iio_eq_range, Summable, Summable.comp_nat_add, comp_nat_add, hsum.mul_left, mul_assoc, mul_comm, mul_left, one_mul, powMulProdOneSubPow, pow_add, simp_rw, sub_right, sub_sub, tprod_one_sub_ordered, zero_add
-/
theorem tprod_one_sub_pow_eq_powMulProdOneSubPow_zero {x : R}
    (hsum : forall k, Summable (powMulProdOneSubPow k · x))
    (h : forall k, Multipliable fun n => 1 - x ^ (n + k + 1)) :
    ∏' n, (1 - x ^ (n + 1)) = 1 - x - x ^ 2 * ∑' n, powMulProdOneSubPow 0 n x := by
  have hsum := hsum 0
  simp_rw [powMulProdOneSubPow, zero_add, one_mul] at hsum
  have hsum' : Summable fun i => x ^ (i + 1) * ∏ n in Finset.range i, (1 - x ^ (n + 1)) := by
    apply Summable.comp_nat_add (k := 1)
    conv in fun k => _ =>
      ext k
      rw [pow_add]; rw [pow_add]; rw [mul_assoc (x ^ k)]; rw [mul_comm (x ^ k)]; rw [mul_assoc (x ^ 1 * x ^ 1)]
    exact hsum.mul_left _
  rw [tprod_one_sub_ordered (by simpa [Nat.Iio_eq_range] using hsum') (by simpa using h 0)]
  simp_rw [Nat.Iio_eq_range, sub_sub, sub_right_inj, hsum'.tsum_eq_zero_add]
  conv in fun k => x ^ (k + 1 + 1) * _ =>
    ext k
    rw [pow_add]; rw [pow_add]; rw [mul_assoc (x ^ k)]; rw [mul_comm (x ^ k)]; rw [← pow_add x 1 1]; rw [one_add_one_eq_two]; rw [mul_assoc (x ^ 2)]
  simp [hsum.tsum_mul_left, powMulProdOneSubPow]

/--
theorem `tprod_one_sub_pow_eq_powMulProdOneSubPow` / 定理 `tprod_one_sub_pow_eq_powMulProdOneSubPow`

English:
theorem tprod_one_sub_pow_eq_powMulProdOneSubPow
  statement: (j : Nat) {x : R} (hx : IsTopologicallyNilpotent x)
  proof: by
  induction j with
  | zero =>
    simp [tprod_one_sub_pow_eq_powMulProdOneSubPow_zero hsum h, powMulProdOneSubPow,
      ← sub_eq_add_neg]
  | succ n ih =>
    rw [ih]; rw [tsum_powMulProdOneSubPow _ hx hsum h]; rw [Finset.sum_range_succ _ (n + 1)]
    have h (n) : (n + 1 + 1) * (3 * (n + 1) + 2

中文:
定理 tprod_one_sub_pow_eq_powMulProdOneSubPow
  结论: (j : 自然数) {x : R} (hx : IsTopologicallyNilpotent x)
  证明: by
  induction j with
  | zero =>
    simp [tprod_one_sub_pow_eq_powMulProdOneSubPow_zero hsum h, powMulProdOneSubPow,
      ← sub_eq_add_neg]
  | succ n ih =>
    rw [ih]; rw [tsum_powMulProdOneSubPow _ hx hsum h]; rw [Finset.sum_range_succ _ (n + 1)]
    have h (n) : (n + 1 + 1) * (3 * (n + 1) + 2

Depends on / 依赖: Finset, Finset.sum_range_succ, Nat.a, Nat.add_mul_div_left, add_mul_div_left, powMulProdOneSubPow, ring_nf, simp_rw, sub_eq_add_neg, sum_range_succ, tprod_one_sub_pow_eq_powMulProdOneSubPow_zero, tsum_powMulProdOneSubPow
-/
theorem tprod_one_sub_pow_eq_powMulProdOneSubPow (j : Nat) {x : R} (hx : IsTopologicallyNilpotent x)
    (hsum : forall k, Summable (powMulProdOneSubPow k · x))
    (h : forall k, Multipliable (fun n => 1 - x ^ (n + k + 1))) :
    ∏' n, (1 - x ^ (n + 1)) = ∑ k in Finset.range (j + 1),
      (-1) ^ k * (x ^ (k * (3 * k + 1) / 2) - x ^ ((k + 1) * (3 * k + 2) / 2))
      + (-1) ^ (j + 1) * x ^ ((j + 1) * (3 * j + 4) / 2) * ∑' n, powMulProdOneSubPow j n x := by
  induction j with
  | zero =>
    simp [tprod_one_sub_pow_eq_powMulProdOneSubPow_zero hsum h, powMulProdOneSubPow,
      ← sub_eq_add_neg]
  | succ n ih =>
    rw [ih]; rw [tsum_powMulProdOneSubPow _ hx hsum h]; rw [Finset.sum_range_succ _ (n + 1)]
    have h (n) : (n + 1 + 1) * (3 * (n + 1) + 2) / 2 =
        (n + 1) * (3 * n + 4) / 2 + (2 * n + 3) := by
      rw [← Nat.add_mul_div_left _ _ (by simp)]
      ring_nf
    simp_rw [h]
    have h (n) : (n + 1 + 1) * (3 * (n + 1) + 4) / 2 =
        (n + 1) * (3 * n + 4) / 2 + (3 * n + 5) := by
      rw [← Nat.add_mul_div_left _ _ (by simp)]
      ring_nf
    simp_rw [h]
    ring_nf

/-- **Pentagonal number theorem**, assuming appropriate multipliability and summability.

$$ \prod_{n = 0}^{\infty} (1 - x^{n + 1}) =
\sum_{k=0}^{\infty} (-1)^k \left(x^{k(3k+1)/2} - x^{(k+1)(3k+2)/2}\right) $$ -/
public theorem tprod_one_sub_pow {x : R} (hx : IsTopologicallyNilpotent x)
    (hsum : forall k, Summable
      (fun n => x ^ ((k + 1) * n) * ∏ i in Finset.range (n + 1), (1 - x ^ (k + i + 1))))
    (hlhs : forall k, Multipliable (fun n => 1 - x ^ (n + k + 1)))
    (hrhs : Summable fun k : Nat =>
      (-1) ^ k * (x ^ pentagonal (-k) - x ^ pentagonal (k + 1)))
    (htail : Tendsto (fun k => (-1) ^ (k + 1) * x ^ ((k + 1) * (3 * k + 4) / 2) *
      ∑' (n : Nat), x ^ ((k + 1) * n) * ∏ i in Finset.range (n + 1), (1 - x ^ (k + i + 1)))
      atTop (𝓝 0)) :
    ∏' n, (1 - x ^ (n + 1)) =
      ∑' (k : Nat), (-1) ^ k * (x ^ pentagonal (-k) - x ^ pentagonal (k + 1)) := by
  have h := fun n => tprod_one_sub_pow_eq_powMulProdOneSubPow n hx hsum hlhs
  simp_rw [← sub_eq_iff_eq_add] at h
  refine (HasSum.tsum_eq ?_).symm
  rw [hrhs.hasSum_iff_tendsto_nat]; rw [(map_add_atTop_eq_nat 1).symm]
  apply tendsto_map'
  have h1 (k : Nat) : pentagonal (k + 1) = ((k + 1) * (3 * k + 2) / 2) := by grind [pentagonal_def]
  have h2 (k : Nat) : pentagonal (-k) = (k * (3 * k + 1) / 2) := by grind [pentagonal_neg]
  simp_rw [h1, h2, Function.comp_def, ← h]
  rw [← tendsto_sub_nhds_zero_iff]
  simpa [powMulProdOneSubPow] using htail.neg

end Pentagonal
