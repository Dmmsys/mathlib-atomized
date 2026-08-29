/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Anatole Dedecker
-/
module

public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Topology.Order.Rolle

/-!
# Rolle's Theorem

In this file we prove Rolle's Theorem. The theorem says that for a function `f : ℝ → ℝ` such that

* $f$ is differentiable on an open interval $(a, b)$, $a < b$;
* $f$ is continuous on the corresponding closed interval $[a, b]$;
* $f(a) = f(b)$,

there exists a point $c∈(a, b)$ such that $f'(c)=0$.

We prove four versions of this theorem.

* `exists_hasDerivAt_eq_zero` is closest to the statement given above. It assumes that at every
  point $x ∈ (a, b)$ function $f$ has derivative $f'(x)$, then concludes that $f'(c)=0$ for some
  $c∈(a, b)$.
* `exists_deriv_eq_zero` deals with `deriv f` instead of an arbitrary function `f'` and a predicate
  `HasDerivAt`; since we use zero as the "junk" value for `deriv f c`, this version does not
  assume that `f` is differentiable on the open interval.
* `exists_hasDerivAt_eq_zero'` is similar to `exists_hasDerivAt_eq_zero` but instead of assuming
  continuity on the closed interval $[a, b]$ it assumes that $f$ tends to the same limit as $x$
  tends to $a$ from the right and as $x$ tends to $b$ from the left.
* `exists_deriv_eq_zero'` relates to `exists_deriv_eq_zero` as `exists_hasDerivAt_eq_zero'`
  relates to `exists_hasDerivAt_eq_zero`.

## References

* [Rolle's Theorem](https://en.wikipedia.org/wiki/Rolle's_theorem);

## Tags

local extremum, Rolle's Theorem
-/

public section

open Set Filter Topology

variable {f f' : Real -> Real} {a b l : Real}

/--
theorem `exists_hasDerivAt_eq_zero` / 定理 `exists_hasDerivAt_eq_zero`

English:
theorem exists_hasDerivAt_eq_zero
  statement: (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b)
  proof: let ⟨c, cmem, hc⟩ := exists_isLocalExtr_Ioo hab hfc hfI
⟨c, cmem, hc.hasDerivAt_eq_zero hff' c cmem⟩

中文:
定理 存在_hasDerivAt_eq_zero
  结论: (hab : a < b) (hfc : ContinuousOn f (闭区间 a b)) (hfI : f a = f b)
  证明: let ⟨c, cmem, hc⟩ := exists_isLocalExtr_Ioo hab hfc hfI
⟨c, cmem, hc.hasDerivAt_eq_zero hff' c cmem⟩

Depends on / 依赖: exists_isLocalExtr_Ioo, hasDerivAt_eq_zero, hc.hasDerivAt_eq_zero
-/
theorem exists_hasDerivAt_eq_zero (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b)
    (hff' : forall x in Ioo a b, HasDerivAt f (f' x) x) : exists c in Ioo a b, f' c = 0 :=
  let ⟨c, cmem, hc⟩ := exists_isLocalExtr_Ioo hab hfc hfI
⟨c, cmem, hc.hasDerivAt_eq_zero hff' c cmem⟩

/-- **Rolle's Theorem** `deriv` version -/
@[wikidata Q193286]
/--
theorem `exists_deriv_eq_zero` / 定理 `exists_deriv_eq_zero`

English:
theorem exists_deriv_eq_zero
  given: (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b)
  proof: let ⟨c, cmem, hc⟩ := exists_isLocalExtr_Ioo hab hfc hfI
  ⟨c, cmem, hc.deriv_eq_zero⟩

中文:
定理 存在_deriv_eq_zero
  条件: (hab : a < b) (hfc : ContinuousOn f (闭区间 a b)) (hfI : f a = f b)
  证明: let ⟨c, cmem, hc⟩ := exists_isLocalExtr_Ioo hab hfc hfI
  ⟨c, cmem, hc.deriv_eq_zero⟩

Depends on / 依赖: deriv_eq_zero, exists_isLocalExtr_Ioo, hc.deriv_eq_zero
-/
theorem exists_deriv_eq_zero (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b) :
    exists c in Ioo a b, deriv f c = 0 :=
  let ⟨c, cmem, hc⟩ := exists_isLocalExtr_Ioo hab hfc hfI
  ⟨c, cmem, hc.deriv_eq_zero⟩

/--
theorem `exists_hasDerivAt_eq_zero'` / 定理 `exists_hasDerivAt_eq_zero'`

English:
theorem exists_hasDerivAt_eq_zero'
  statement: (hab : a < b) (hfa : Tendsto f (𝓝[>] a) (𝓝 l))
  proof: let ⟨c, cmem, hc⟩ := exists_isLocalExtr_Ioo_of_tendsto hab
    (fun x hx => (hff' x hx).continuousAt.continuousWithinAt) hfa hfb
⟨c, cmem, hc.hasDerivAt_eq_zero hff' c cmem⟩

中文:
定理 存在_hasDerivAt_eq_zero'
  结论: (hab : a < b) (hfa : 收敛 f (𝓝[>] a) (𝓝 l))
  证明: let ⟨c, cmem, hc⟩ := exists_isLocalExtr_Ioo_of_tendsto hab
    (fun x hx => (hff' x hx).continuousAt.continuousWithinAt) hfa hfb
⟨c, cmem, hc.hasDerivAt_eq_zero hff' c cmem⟩

Depends on / 依赖: continuousAt, continuousAt.continuousWithinAt, continuousWithinAt, exists_isLocalExtr_Ioo_of_tendsto, hasDerivAt_eq_zero, hc.hasDerivAt_eq_zero
-/
theorem exists_hasDerivAt_eq_zero' (hab : a < b) (hfa : Tendsto f (𝓝[>] a) (𝓝 l))
    (hfb : Tendsto f (𝓝[<] b) (𝓝 l)) (hff' : forall x in Ioo a b, HasDerivAt f (f' x) x) :
    exists c in Ioo a b, f' c = 0 :=
  let ⟨c, cmem, hc⟩ := exists_isLocalExtr_Ioo_of_tendsto hab
    (fun x hx => (hff' x hx).continuousAt.continuousWithinAt) hfa hfb
⟨c, cmem, hc.hasDerivAt_eq_zero hff' c cmem⟩

/--
theorem `exists_deriv_eq_zero'` / 定理 `exists_deriv_eq_zero'`

English:
theorem exists_deriv_eq_zero'
  statement: (hab : a < b) (hfa : Tendsto f (𝓝[>] a) (𝓝 l))
  proof: by
  by_cases! h : forall x in Ioo a b, DifferentiableAt Real f x
  · exact exists_hasDerivAt_eq_zero' hab hfa hfb fun x hx => (h x hx).hasDerivAt
  · obtain ⟨c, hc, hcdiff⟩ : exists x in Ioo a b, ¬DifferentiableAt Real f x := h
    exact ⟨c, hc, deriv_zero_of_not_differentiableAt hcdiff⟩

中文:
定理 存在_deriv_eq_zero'
  结论: (hab : a < b) (hfa : 收敛 f (𝓝[>] a) (𝓝 l))
  证明: by
  by_cases! h : forall x in Ioo a b, DifferentiableAt Real f x
  · exact exists_hasDerivAt_eq_zero' hab hfa hfb fun x hx => (h x hx).hasDerivAt
  · obtain ⟨c, hc, hcdiff⟩ : exists x in Ioo a b, ¬DifferentiableAt Real f x := h
    exact ⟨c, hc, deriv_zero_of_not_differentiableAt hcdiff⟩

Depends on / 依赖: DifferentiableAt, deriv_zero_of_not_differentiableAt, exists_hasDerivAt_eq_zero, hasDerivAt, hcdiff
-/
theorem exists_deriv_eq_zero' (hab : a < b) (hfa : Tendsto f (𝓝[>] a) (𝓝 l))
    (hfb : Tendsto f (𝓝[<] b) (𝓝 l)) : exists c in Ioo a b, deriv f c = 0 := by
  by_cases! h : forall x in Ioo a b, DifferentiableAt Real f x
  · exact exists_hasDerivAt_eq_zero' hab hfa hfb fun x hx => (h x hx).hasDerivAt
  · obtain ⟨c, hc, hcdiff⟩ : exists x in Ioo a b, ¬DifferentiableAt Real f x := h
    exact ⟨c, hc, deriv_zero_of_not_differentiableAt hcdiff⟩
