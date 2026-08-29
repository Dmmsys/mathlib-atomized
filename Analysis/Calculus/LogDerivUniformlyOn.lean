/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn

/-!
# The Logarithmic derivative of an infinite product

We show that if we have an infinite product of functions `f` that is locally uniformly convergent,
then the logarithmic derivative of the product is the sum of the logarithmic derivatives of the
individual functions.

-/

public section

open Complex

/--
theorem `logDeriv_tprod_eq_tsum` / 定理 `logDeriv_tprod_eq_tsum`

English:
theorem logDeriv_tprod_eq_tsum
  statement: {ι : Type*} {s : Set Complex} (hs : IsOpen s) {x : Complex} (hx : x in s)
  proof: by
  rw [Eq.comm]; rw [← hm.hasSum_iff]
  refine logDeriv_tendsto hs hx htend.hasProdLocallyUniformlyOn (.of_forall <| by fun_prop) hnez
.congr fun b => ?_
  rw [logDeriv_prod (fun i _ => hf i) (fun i _ => (hd i x hx).differentiableAt (hs.mem_nhds hx))]

中文:
定理 logDeriv_tprod_eq_tsum
  结论: {ι : 类型} {s : 集合 复形} (hs : 是开集 s) {x : 复形} (hx : x in s)
  证明: by
  rw [Eq.comm]; rw [← hm.hasSum_iff]
  refine logDeriv_tendsto hs hx htend.hasProdLocallyUniformlyOn (.of_forall <| by fun_prop) hnez
.congr fun b => ?_
  rw [logDeriv_prod (fun i _ => hf i) (fun i _ => (hd i x hx).differentiableAt (hs.mem_nhds hx))]

Depends on / 依赖: Eq.comm, differentiableAt, fun_prop, hasProdLocallyUniformlyOn, hasSum_iff, hm.hasSum_iff, hs.mem_nhds, htend.hasProdLocallyUniformlyOn, logDeriv_prod, logDeriv_tendsto, mem_nhds, of_forall
-/
theorem logDeriv_tprod_eq_tsum {ι : Type*} {s : Set Complex} (hs : IsOpen s) {x : Complex} (hx : x in s)
    {f : ι -> Complex -> Complex} (hf : forall i, f i x != 0) (hd : forall i, DifferentiableOn Complex (f i) s)
    (hm : Summable fun i => logDeriv (f i) x) (htend : MultipliableLocallyUniformlyOn f s)
    (hnez : ∏' i, f i x != 0) :
    logDeriv (∏' i, f i ·) x = ∑' i, logDeriv (f i) x := by
  rw [Eq.comm]; rw [← hm.hasSum_iff]
  refine logDeriv_tendsto hs hx htend.hasProdLocallyUniformlyOn (.of_forall <| by fun_prop) hnez
.congr fun b => ?_
  rw [logDeriv_prod (fun i _ => hf i) (fun i _ => (hd i x hx).differentiableAt (hs.mem_nhds hx))]
