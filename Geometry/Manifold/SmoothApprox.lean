/-
Copyright (c) 2025 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Patrick Massot
-/
module

public import Mathlib.Geometry.Manifold.Notation
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Approximation of continuous functions by smooth functions

In this file, we deduce from the existence of smooth partitions of unity that any continuous map
from a real σ-compact finite dimensional manifold `M` to a real normed space `F` can be
approximated uniformly by smooth functions.

More precisely, we strengthen this result in three ways :
* instead of a single number `ε > 0`, one may prescribe the precision of the approximation using
  an arbitrary continuous positive function `ε : M → ℝ`. This allows, for example, a control
  on the asymptotic behaviour of the approximation (e.g, choosing a precision `ε` which vanishes
  at infinity yields that continuous functions vanishing at infinity can be approximated by
  smooth functions vanishing at infinity).
* if the original map `f` already has the desired regularity on some neighborhood of a closed
  set `M`, one can choose an approximation which stays equal to `f` on `S`. This allows
  for some additional control in a setting with iterated approximations.
* finally, one may prescribe the approximation to vanish wherever the original function vanishes.
  For example, this shows that continuous functions supported on some compact set `K` may be
  approximated uniformly by smooth function supported on the **same** compact `K`.
  (Compare with arguments based on convolution where one needs to thicken `K` a bit).

## Main results

* `Continuous.exists_contMDiff_approx_and_eqOn`: approximating a continuous function `f : M → F`
  by a `C^n` function `g : M → E`, with precision prescribed by a continuous positive `ε : M → ℝ`,
  while ensuring that `support g ⊆ support f` and that `g` coincides with `f` on some closed set `S`
  in the neighborhood of which `f` is already `C^n`.
* `Continuous.exists_contMDiff_approx`: a simpler version of the previous result when one does not
  care about prescribing points with `g x = f x`. One still gets `support g ⊆ support f` for free,
  so we put it in the conclusion.
* `Continuous.exists_contDiff_approx_and_eqOn`, `Continuous.exists_contDiff_approx`: specializations
  of the previous results when `M = E` is a normed space.

## Implementation notes

With minor work, we could strengthen the statements in the following ways:
- the precision function `ε : M → ℝ` may be assumed `LowerSemicontinuous` instead of `Continuous`,
- the condition `support g ⊆ support f`, which translates to `∀ x, f x = 0 → g x = 0`,
  may be strengthened to `∀ x, f x = h x → g x = h x` for some arbitrary smooth `h : M → F`.

This file depends on the manifold library, which may be annoying if you only need the normed space
statements. **Please do not let this refrain you from using them** if they apply naturally in your
context: if this is too much of a problem, you should complain on Zulip, so that we get more data
about the need for a non-manifold version of `SmoothPartitionOfUnity`.

## TODO

- More generally, all results should apply to approximating continuous sections of a smooth
  vector bundle by smooth sections.
- If needed, specialize to `M = U` an open subset of a normed space `E`
  (we currently do `M = E` only).

-/

public section

open Set Function
open scoped Topology ContDiff Manifold

noncomputable section

section Manifold

variable {E F H M : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E]
  [NormedAddCommGroup F] [NormedSpace Real F]
  [TopologicalSpace H] (I : ModelWithCorners Real E H)
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

variable {f : M -> F} {ε : M -> Real}

/--
theorem `Continuous.exists_contMDiff_approx_and_eqOn` / 定理 `Continuous.exists_contMDiff_approx_and_eqOn`

English:
theorem Continuous.exists_contMDiff_approx_and_eqOn
  statement: (n : Nat∞)
  proof: by
  have dist_f_f : forall x, dist (f x) (f x) < ε x := by simpa only [dist_self] using ε_pos
  let t : M -> Set F := fun x => {y | dist y (f x) < ε x ∧ (x in S -> y = f x) ∧ (f x = 0 -> y = 0)}
  suffices exists g : C^n⟮I, M; 𝓘(Real, F), F⟯, forall x, g x in t x by
    rcases this with ⟨g, hg⟩
   

中文:
定理 连续.存在_contMDiff_approx_and_eqOn
  结论: (n : 自然数∞)
  证明: by
  have dist_f_f : forall x, dist (f x) (f x) < ε x := by simpa only [dist_self] using ε_pos
  let t : M -> Set F := fun x => {y | dist y (f x) < ε x ∧ (x in S -> y = f x) ∧ (f x = 0 -> y = 0)}
  suffices exists g : C^n⟮I, M; 𝓘(Real, F), F⟯, forall x, g x in t x by
    rcases this with ⟨g, hg⟩
   

Depends on / 依赖: Convex, convex_ball, convex_singleton, dist_f_f, dist_self, setOfPred_const_imp, setOfPred_const_imp.inter, t_conv
-/
theorem Continuous.exists_contMDiff_approx_and_eqOn (n : Nat∞)
    (f_cont : Continuous f) (ε_cont : Continuous ε) (ε_pos : forall x, 0 < ε x)
    {S U : Set M} (hS : IsClosed S) (hU : U in 𝓝ˢ S) (hfU : CMDiff[U] n f) :
    exists g : C^n⟮I, M; 𝓘(Real, F), F⟯,
      (forall x, dist (g x) (f x) < ε x) ∧ EqOn g f S ∧ support g subseteq support f := by
  have dist_f_f : forall x, dist (f x) (f x) < ε x := by simpa only [dist_self] using ε_pos
  let t : M -> Set F := fun x => {y | dist y (f x) < ε x ∧ (x in S -> y = f x) ∧ (f x = 0 -> y = 0)}
  suffices exists g : C^n⟮I, M; 𝓘(Real, F), F⟯, forall x, g x in t x by
    rcases this with ⟨g, hg⟩
    exact ⟨g, fun x => (hg x).1, fun x => (hg x).2.1, fun x => mt (hg x).2.2⟩
have t_conv (x) : Convex Real (t x) := (convex_ball (f x) (ε x)).inter
    (convex_singleton _).setOfPred_const_imp.inter (convex_singleton _).setOfPred_const_imp
  apply exists_contMDiffMap_forall_mem_convex_of_local I t_conv
  intro x
  by_cases hx : x in S
  · refine ⟨U, mem_nhdsSet_iff_forall.mp hU x hx, ?_⟩
    exact ⟨f, hfU, fun y _ => ⟨dist_f_f y, fun _ => rfl, id⟩⟩
  · have : forallᶠ y in 𝓝 x, y ∉ S ∧ dist (f x) (f y) < ε y := (hS.isOpen_compl.eventually_mem hx).and
      ((continuous_const.dist f_cont).continuousAt.eventually_lt ε_cont.continuousAt (dist_f_f x))
    have : forallᶠ y in 𝓝 x, (y ∉ S ∧ dist (f x) (f y) < ε y) ∧ (f y = 0 -> f x = 0) := by
      by_cases hx' : f x = 0
      · simpa [hx'] using this
      · simpa [hx'] using this.and (f_cont.continuousAt.eventually_ne hx')
    exact ⟨_, this, (fun _ => f x), contMDiffOn_const, fun y hy => ⟨hy.1.2, by simp [hy.1.1], hy.2⟩⟩

/--
theorem `Continuous.exists_contMDiff_approx` / 定理 `Continuous.exists_contMDiff_approx`

English:
theorem Continuous.exists_contMDiff_approx
  statement: (n : Nat∞)
  proof: by
  obtain ⟨g, g_approx, -, g_supp⟩ := f_cont.exists_contMDiff_approx_and_eqOn I n ε_cont ε_pos
    isClosed_empty mem_nhdsSet_empty contMDiffOn_empty
  exact ⟨g, g_approx, g_supp⟩

中文:
定理 连续.存在_contMDiff_approx
  结论: (n : 自然数∞)
  证明: by
  obtain ⟨g, g_approx, -, g_supp⟩ := f_cont.exists_contMDiff_approx_and_eqOn I n ε_cont ε_pos
    isClosed_empty mem_nhdsSet_empty contMDiffOn_empty
  exact ⟨g, g_approx, g_supp⟩

Depends on / 依赖: contMDiffOn_empty, exists_contMDiff_approx_and_eqOn, f_cont, f_cont.exists_contMDiff_approx_and_eqOn, g_approx, g_supp, isClosed_empty, linearIndepOn_iff, mem_nhdsSet_empty
-/
theorem Continuous.exists_contMDiff_approx (n : Nat∞)
    (f_cont : Continuous f) (ε_cont : Continuous ε) (ε_pos : forall x, 0 < ε x) :
    exists g : C^n⟮I, M; 𝓘(Real, F), F⟯, (forall x, dist (g x) (f x) < ε x) ∧ support g subseteq support f := by
  obtain ⟨g, g_approx, -, g_supp⟩ := f_cont.exists_contMDiff_approx_and_eqOn I n ε_cont ε_pos
    isClosed_empty mem_nhdsSet_empty contMDiffOn_empty
  exact ⟨g, g_approx, g_supp⟩

end Manifold

section NormedSpace

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E]
  [NormedAddCommGroup F] [NormedSpace Real F]

variable {f : E -> F} {ε : E -> Real}

/--
theorem `Continuous.exists_contDiff_approx_and_eqOn` / 定理 `Continuous.exists_contDiff_approx_and_eqOn`

English:
theorem Continuous.exists_contDiff_approx_and_eqOn
  statement: (n : Nat∞)
  proof: by
  obtain ⟨g, g_approx, g_eqOn, g_supp⟩ := f_cont.exists_contMDiff_approx_and_eqOn 𝓘(Real, E) n
    ε_cont ε_pos hS hU hfU.contMDiffOn
  exact ⟨g, g.contMDiff.contDiff, g_approx, g_eqOn, g_supp⟩

中文:
定理 连续.存在_contDiff_approx_and_eqOn
  结论: (n : 自然数∞)
  证明: by
  obtain ⟨g, g_approx, g_eqOn, g_supp⟩ := f_cont.exists_contMDiff_approx_and_eqOn 𝓘(Real, E) n
    ε_cont ε_pos hS hU hfU.contMDiffOn
  exact ⟨g, g.contMDiff.contDiff, g_approx, g_eqOn, g_supp⟩

Depends on / 依赖: contDiff, contMDiff, contMDiffOn, exists_contMDiff_approx_and_eqOn, f_cont, f_cont.exists_contMDiff_approx_and_eqOn, g.contMDiff.contDiff, g_approx, g_eqOn, g_supp, hfU.contMDiffOn
-/
theorem Continuous.exists_contDiff_approx_and_eqOn (n : Nat∞)
    (f_cont : Continuous f) (ε_cont : Continuous ε) (ε_pos : forall x, 0 < ε x)
    {S U : Set E} (hS : IsClosed S) (hU : U in 𝓝ˢ S) (hfU : ContDiffOn Real n f U) :
    exists g : E -> F, ContDiff Real n g ∧
      (forall x, dist (g x) (f x) < ε x) ∧ EqOn g f S ∧ support g subseteq support f := by
  obtain ⟨g, g_approx, g_eqOn, g_supp⟩ := f_cont.exists_contMDiff_approx_and_eqOn 𝓘(Real, E) n
    ε_cont ε_pos hS hU hfU.contMDiffOn
  exact ⟨g, g.contMDiff.contDiff, g_approx, g_eqOn, g_supp⟩

/--
theorem `Continuous.exists_contDiff_approx` / 定理 `Continuous.exists_contDiff_approx`

English:
theorem Continuous.exists_contDiff_approx
  statement: (n : Nat∞)
  proof: by
  obtain ⟨g, g_contDiff, g_approx, -, g_supp⟩ := f_cont.exists_contDiff_approx_and_eqOn n
    ε_cont ε_pos isClosed_empty mem_nhdsSet_empty contDiffOn_empty
  exact ⟨g, g_contDiff, g_approx, g_supp⟩

中文:
定理 连续.存在_contDiff_approx
  结论: (n : 自然数∞)
  证明: by
  obtain ⟨g, g_contDiff, g_approx, -, g_supp⟩ := f_cont.exists_contDiff_approx_and_eqOn n
    ε_cont ε_pos isClosed_empty mem_nhdsSet_empty contDiffOn_empty
  exact ⟨g, g_contDiff, g_approx, g_supp⟩

Depends on / 依赖: contDiffOn_empty, exists_contDiff_approx_and_eqOn, f_cont, f_cont.exists_contDiff_approx_and_eqOn, g_approx, g_contDiff, g_supp, isClosed_empty, mem_nhdsSet_empty
-/
theorem Continuous.exists_contDiff_approx (n : Nat∞)
    (f_cont : Continuous f) (ε_cont : Continuous ε) (ε_pos : forall x, 0 < ε x) :
    exists g : E -> F, ContDiff Real n g ∧ (forall x, dist (g x) (f x) < ε x) ∧ support g subseteq support f := by
  obtain ⟨g, g_contDiff, g_approx, -, g_supp⟩ := f_cont.exists_contDiff_approx_and_eqOn n
    ε_cont ε_pos isClosed_empty mem_nhdsSet_empty contDiffOn_empty
  exact ⟨g, g_contDiff, g_approx, g_supp⟩

end NormedSpace
