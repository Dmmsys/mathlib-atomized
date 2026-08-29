/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Iterated derivatives of compositions

In this file we specialize Faà di Bruno's formula to one-dimensional domain
to deduce formulae for `iteratedDerivWithin k (g ∘ f) s x` for `k = 2` and `k = 3`.

We use
- `vcomp` for lemmas about the composition of `g : E → F` with `f : 𝕜 → E`;
- `scomp` for lemmas about the composition of `g : 𝕜 → E` with `f : 𝕜 → 𝕜`;
- `comp` for lemmas about the composition of `g : 𝕜 → 𝕜` with `f : 𝕜 → 𝕜`.

## TODO

- What `UniqueDiffOn` assumptions can be discarded?
- In case of dimension 1 (and, more generally, in case of symmetric iterated derivatives),
  some terms are equal.
  Add versions of Faà di Bruno's formula that take the symmetries into account.
- Can we generalize `scomp`/`comp` to `f : 𝕜 → 𝕜'`,
  where `𝕜'` is a normed algebra over `𝕜`? E.g., `𝕜 = ℝ`, `𝕜' = ℂ`.

Before starting to work on these TODOs, please contact Yury Kudryashov
who may have partial progress towards some of them.
-/

public section

open Function Set
open scoped ContDiff

section vcomp

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {g : E -> F} {f : 𝕜 -> E} {s : Set 𝕜} {t : Set E} {x : 𝕜} {n : Nat∞ω} {i : Nat}

/--
theorem `iteratedDerivWithin_vcomp_eq_sum_orderedFinpartition` / 定理 `iteratedDerivWithin_vcomp_eq_sum_orderedFinpartition`

English:
theorem iteratedDerivWithin_vcomp_eq_sum_orderedFinpartition
  proof: by
  simp only [iteratedDerivWithin, iteratedFDerivWithin_comp hg hf ht hs hx hst hi]
  simp [FormalMultilinearSeries.taylorComp, ftaylorSeriesWithin,
    OrderedFinpartition.applyOrderedFinpartition_apply, comp_def]

中文:
定理 iteratedDerivWithin_vcomp_eq_sum_orderedFinpartition
  证明: by
  simp only [iteratedDerivWithin, iteratedFDerivWithin_comp hg hf ht hs hx hst hi]
  simp [FormalMultilinearSeries.taylorComp, ftaylorSeriesWithin,
    OrderedFinpartition.applyOrderedFinpartition_apply, comp_def]

Depends on / 依赖: FormalMultilinearSeries, FormalMultilinearSeries.taylorComp, OrderedFinpartition, OrderedFinpartition.applyOrderedFinpartition_apply, applyOrderedFinpartition_apply, comp_def, ftaylorSeriesWithin, iteratedDerivWithin, iteratedFDerivWithin_comp, taylorComp
-/
theorem iteratedDerivWithin_vcomp_eq_sum_orderedFinpartition
    (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContDiffWithinAt 𝕜 n f s x)
    (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜 s) (hx : x in s) (hst : MapsTo f s t) (hi : i <= n) :
    iteratedDerivWithin i (g ∘ f) s x =
      ∑ c : OrderedFinpartition i, iteratedFDerivWithin 𝕜 c.length g t (f x) fun j =>
        iteratedDerivWithin (c.partSize j) f s x := by
  simp only [iteratedDerivWithin, iteratedFDerivWithin_comp hg hf ht hs hx hst hi]
  simp [FormalMultilinearSeries.taylorComp, ftaylorSeriesWithin,
    OrderedFinpartition.applyOrderedFinpartition_apply, comp_def]

/--
theorem `iteratedDeriv_vcomp_eq_sum_orderedFinpartition` / 定理 `iteratedDeriv_vcomp_eq_sum_orderedFinpartition`

English:
theorem iteratedDeriv_vcomp_eq_sum_orderedFinpartition
  proof: by
  simp only [← iteratedDerivWithin_univ, ← iteratedFDerivWithin_univ]
  exact iteratedDerivWithin_vcomp_eq_sum_orderedFinpartition hg hf uniqueDiffOn_univ
    uniqueDiffOn_univ (mem_univ x) (mapsTo_univ f _) hi

中文:
定理 iteratedDeriv_vcomp_eq_sum_orderedFinpartition
  证明: by
  simp only [← iteratedDerivWithin_univ, ← iteratedFDerivWithin_univ]
  exact iteratedDerivWithin_vcomp_eq_sum_orderedFinpartition hg hf uniqueDiffOn_univ
    uniqueDiffOn_univ (mem_univ x) (mapsTo_univ f _) hi

Depends on / 依赖: iteratedDerivWithin_univ, iteratedDerivWithin_vcomp_eq_sum_orderedFinpartition, iteratedFDerivWithin_univ, mapsTo_univ, mem_univ, uniqueDiffOn_univ
-/
theorem iteratedDeriv_vcomp_eq_sum_orderedFinpartition
    (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffAt 𝕜 n f x) (hi : i <= n) :
    iteratedDeriv i (g ∘ f) x =
      ∑ c : OrderedFinpartition i, iteratedFDeriv 𝕜 c.length g (f x) fun j =>
        iteratedDeriv (c.partSize j) f x := by
  simp only [← iteratedDerivWithin_univ, ← iteratedFDerivWithin_univ]
  exact iteratedDerivWithin_vcomp_eq_sum_orderedFinpartition hg hf uniqueDiffOn_univ
    uniqueDiffOn_univ (mem_univ x) (mapsTo_univ f _) hi

set_option backward.isDefEq.respectTransparency false in
/--
theorem `iteratedDerivWithin_vcomp_two` / 定理 `iteratedDerivWithin_vcomp_two`

English:
theorem iteratedDerivWithin_vcomp_two
  proof: by
  rw [iteratedDerivWithin_vcomp_eq_sum_orderedFinpartition hg hf ht hs hx hst le_rfl]
  simp only [← (OrderedFinpartition.extendEquiv 1).sum_comp, Fintype.sum_sigma, Fintype.sum_unique,
    OrderedFinpartition.default_eq, Fintype.sum_option]
  have : (Fin.cons 1 (fun _ => 1) : Fin 2 -> Nat) = fun

中文:
定理 iteratedDerivWithin_vcomp_two
  证明: by
  rw [iteratedDerivWithin_vcomp_eq_sum_orderedFinpartition hg hf ht hs hx hst le_rfl]
  simp only [← (OrderedFinpartition.extendEquiv 1).sum_comp, Fintype.sum_sigma, Fintype.sum_unique,
    OrderedFinpartition.default_eq, Fintype.sum_option]
  have : (Fin.cons 1 (fun _ => 1) : Fin 2 -> Nat) = fun

Depends on / 依赖: Fin.cons, Fin.forall_fin_two.mpr, Fintype, Fintype.sum_option, Fintype.sum_sigma, Fintype.sum_unique, OrderedFin, OrderedFinpartition, OrderedFinpartition.default_eq, OrderedFinpartition.extend, OrderedFinpartition.extendEquiv, OrderedFinpartition.extendLeft, OrderedFinpartition.extendMiddle, default_eq, extend, extendEquiv, extendLeft, extendMiddle, forall_fin_two, iteratedDerivWithin_vcomp_eq_sum_orderedFinpartition
-/
theorem iteratedDerivWithin_vcomp_two
    (hg : ContDiffWithinAt 𝕜 2 g t (f x)) (hf : ContDiffWithinAt 𝕜 2 f s x)
    (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜 s) (hx : x in s) (hst : MapsTo f s t) :
    iteratedDerivWithin 2 (g ∘ f) s x =
      iteratedFDerivWithin 𝕜 2 g t (f x) (fun _ => derivWithin f s x) +
      fderivWithin 𝕜 g t (f x) (iteratedDerivWithin 2 f s x) := by
  rw [iteratedDerivWithin_vcomp_eq_sum_orderedFinpartition hg hf ht hs hx hst le_rfl]
  simp only [← (OrderedFinpartition.extendEquiv 1).sum_comp, Fintype.sum_sigma, Fintype.sum_unique,
    OrderedFinpartition.default_eq, Fintype.sum_option]
  have : (Fin.cons 1 (fun _ => 1) : Fin 2 -> Nat) = fun _ => 1 :=
funext Fin.forall_fin_two.mpr ⟨rfl, rfl⟩
  simp [OrderedFinpartition.extendEquiv, OrderedFinpartition.extend,
    OrderedFinpartition.extendLeft, OrderedFinpartition.extendMiddle, ht _ (hst hx),
    OrderedFinpartition.atomic, this]

/--
theorem `iteratedDeriv_vcomp_two` / 定理 `iteratedDeriv_vcomp_two`

English:
theorem iteratedDeriv_vcomp_two
  given: (hg : ContDiffAt 𝕜 2 g (f x)) (hf : ContDiffAt 𝕜 2 f x)
  proof: by
  simp only [← iteratedDerivWithin_univ, ← iteratedFDerivWithin_univ,
    ← derivWithin_univ, ← fderivWithin_univ]
  exact iteratedDerivWithin_vcomp_two hg hf uniqueDiffOn_univ
    uniqueDiffOn_univ (mem_univ x) (mapsTo_univ f _)

中文:
定理 iteratedDeriv_vcomp_two
  条件: (hg : ContDiffAt 𝕜 2 g (f x)) (hf : ContDiffAt 𝕜 2 f x)
  证明: by
  simp only [← iteratedDerivWithin_univ, ← iteratedFDerivWithin_univ,
    ← derivWithin_univ, ← fderivWithin_univ]
  exact iteratedDerivWithin_vcomp_two hg hf uniqueDiffOn_univ
    uniqueDiffOn_univ (mem_univ x) (mapsTo_univ f _)

Depends on / 依赖: derivWithin_univ, fderivWithin_univ, iteratedDerivWithin_univ, iteratedDerivWithin_vcomp_two, iteratedFDerivWithin_univ, mapsTo_univ, mem_univ, uniqueDiffOn_univ
-/
theorem iteratedDeriv_vcomp_two (hg : ContDiffAt 𝕜 2 g (f x)) (hf : ContDiffAt 𝕜 2 f x) :
    iteratedDeriv 2 (g ∘ f) x =
      iteratedFDeriv 𝕜 2 g (f x) (fun _ => deriv f x) + fderiv 𝕜 g (f x) (iteratedDeriv 2 f x) := by
  simp only [← iteratedDerivWithin_univ, ← iteratedFDerivWithin_univ,
    ← derivWithin_univ, ← fderivWithin_univ]
  exact iteratedDerivWithin_vcomp_two hg hf uniqueDiffOn_univ
    uniqueDiffOn_univ (mem_univ x) (mapsTo_univ f _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `iteratedDerivWithin_vcomp_three` / 定理 `iteratedDerivWithin_vcomp_three`

English:
theorem iteratedDerivWithin_vcomp_three
  proof: by
  rw [iteratedDerivWithin_vcomp_eq_sum_orderedFinpartition hg hf ht hs hx hst le_rfl]
  simp only [← (OrderedFinpartition.extendEquiv 1).sum_comp,
    ← (OrderedFinpartition.extendEquiv 2).sum_comp, Fintype.sum_sigma,
    Fintype.sum_option, Nat.reduceAdd, OrderedFinpartition.extendEquiv_apply,
 

中文:
定理 iteratedDerivWithin_vcomp_three
  证明: by
  rw [iteratedDerivWithin_vcomp_eq_sum_orderedFinpartition hg hf ht hs hx hst le_rfl]
  simp only [← (OrderedFinpartition.extendEquiv 1).sum_comp,
    ← (OrderedFinpartition.extendEquiv 2).sum_comp, Fintype.sum_sigma,
    Fintype.sum_option, Nat.reduceAdd, OrderedFinpartition.extendEquiv_apply,
 

Depends on / 依赖: Fintype, Fintype.sum_option, Fintype.sum_sigma, Fintype.sum_unique, Nat.reduceAdd, OrderedFinpartition, OrderedFinpartition.atomic_length, OrderedFinpartition.default_eq, OrderedFinpartition.extendEquiv, OrderedFinpartition.extendEquiv_apply, OrderedFinpartition.extendMiddle_length, OrderedFinpartition.extend_none, OrderedFinpartition.extend_some, atomic_length, default_eq, extendEquiv, extendEquiv_apply, extendMiddle_length, extend_none, extend_some
-/
theorem iteratedDerivWithin_vcomp_three
    (hg : ContDiffWithinAt 𝕜 3 g t (f x)) (hf : ContDiffWithinAt 𝕜 3 f s x)
    (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜 s) (hx : x in s) (hst : MapsTo f s t) :
    iteratedDerivWithin 3 (g ∘ f) s x =
      iteratedFDerivWithin 𝕜 3 g t (f x) (fun _ => derivWithin f s x) +
      iteratedFDerivWithin 𝕜 2 g t (f x) ![iteratedDerivWithin 2 f s x, derivWithin f s x] +
      2 • iteratedFDerivWithin 𝕜 2 g t (f x) ![derivWithin f s x, iteratedDerivWithin 2 f s x] +
      fderivWithin 𝕜 g t (f x) (iteratedDerivWithin 3 f s x) := by
  rw [iteratedDerivWithin_vcomp_eq_sum_orderedFinpartition hg hf ht hs hx hst le_rfl]
  simp only [← (OrderedFinpartition.extendEquiv 1).sum_comp,
    ← (OrderedFinpartition.extendEquiv 2).sum_comp, Fintype.sum_sigma,
    Fintype.sum_option, Nat.reduceAdd, OrderedFinpartition.extendEquiv_apply,
    OrderedFinpartition.extend_none, OrderedFinpartition.extend_some,
    OrderedFinpartition.extendMiddle_length, OrderedFinpartition.default_eq, Fintype.sum_unique,
    OrderedFinpartition.atomic_length, OrderedFinpartition.extendLeft_length, Fin.sum_univ_two]
  simp? [add_assoc, two_smul, iteratedFDerivWithin_one_apply (ht _ <| hst hx)] says
    simp only [OrderedFinpartition.extendLeft_partSize, OrderedFinpartition.extendLeft_length,
      OrderedFinpartition.atomic_length, Nat.reduceAdd, OrderedFinpartition.atomic_partSize,
      Fin.isValue, OrderedFinpartition.extendMiddle_partSize, Fin.cons_zero, Fin.update_cons_zero,
      Fin.cons_one, Fin.default_eq_zero, OrderedFinpartition.extendMiddle_length, Fin.cons_update,
      Fin.succ_zero_eq_one, update_self, update_idem,
      iteratedFDerivWithin_one_apply (ht _ <| hst hx), add_assoc, two_smul]
  have (j : _) : (Fin.cons 1 (Fin.cons 1 fun _ => 1) : Fin 3 -> Nat) j = 1 := by
    fin_cases j <;> rfl
  congr <;> ext x <;> fin_cases x <;> simp [this]

/--
theorem `iteratedDeriv_vcomp_three` / 定理 `iteratedDeriv_vcomp_three`

English:
theorem iteratedDeriv_vcomp_three
  given: (hg : ContDiffAt 𝕜 3 g (f x)) (hf : ContDiffAt 𝕜 3 f x)
  proof: by
  simp only [← iteratedDerivWithin_univ, ← iteratedFDerivWithin_univ,
    ← derivWithin_univ, ← fderivWithin_univ]
  exact iteratedDerivWithin_vcomp_three hg hf uniqueDiffOn_univ
    uniqueDiffOn_univ (mem_univ x) (mapsTo_univ f _)

中文:
定理 iteratedDeriv_vcomp_three
  条件: (hg : ContDiffAt 𝕜 3 g (f x)) (hf : ContDiffAt 𝕜 3 f x)
  证明: by
  simp only [← iteratedDerivWithin_univ, ← iteratedFDerivWithin_univ,
    ← derivWithin_univ, ← fderivWithin_univ]
  exact iteratedDerivWithin_vcomp_three hg hf uniqueDiffOn_univ
    uniqueDiffOn_univ (mem_univ x) (mapsTo_univ f _)

Depends on / 依赖: derivWithin_univ, fderivWithin_univ, iteratedDerivWithin_univ, iteratedDerivWithin_vcomp_three, iteratedFDerivWithin_univ, mapsTo_univ, mem_univ, uniqueDiffOn_univ
-/
theorem iteratedDeriv_vcomp_three (hg : ContDiffAt 𝕜 3 g (f x)) (hf : ContDiffAt 𝕜 3 f x) :
    iteratedDeriv 3 (g ∘ f) x =
      iteratedFDeriv 𝕜 3 g (f x) (fun _ => deriv f x) +
      iteratedFDeriv 𝕜 2 g (f x) ![iteratedDeriv 2 f x, deriv f x] +
      2 • iteratedFDeriv 𝕜 2 g (f x) ![deriv f x, iteratedDeriv 2 f x] +
      fderiv 𝕜 g (f x) (iteratedDeriv 3 f x) := by
  simp only [← iteratedDerivWithin_univ, ← iteratedFDerivWithin_univ,
    ← derivWithin_univ, ← fderivWithin_univ]
  exact iteratedDerivWithin_vcomp_three hg hf uniqueDiffOn_univ
    uniqueDiffOn_univ (mem_univ x) (mapsTo_univ f _)

end vcomp

section scomp

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {g : 𝕜 -> E} {f : 𝕜 -> 𝕜} {s : Set 𝕜} {t : Set 𝕜} {x : 𝕜} {n : Nat∞ω} {i : Nat}

/--
theorem `iteratedDerivWithin_scomp_eq_sum_orderedFinpartition` / 定理 `iteratedDerivWithin_scomp_eq_sum_orderedFinpartition`

English:
theorem iteratedDerivWithin_scomp_eq_sum_orderedFinpartition
  proof: by
  rw [iteratedDerivWithin_vcomp_eq_sum_orderedFinpartition hg hf ht hs hx hst hi]
  simp only [iteratedFDerivWithin_apply_eq_iteratedDerivWithin_mul_prod]

中文:
定理 iteratedDerivWithin_scomp_eq_sum_orderedFinpartition
  证明: by
  rw [iteratedDerivWithin_vcomp_eq_sum_orderedFinpartition hg hf ht hs hx hst hi]
  simp only [iteratedFDerivWithin_apply_eq_iteratedDerivWithin_mul_prod]

Depends on / 依赖: iteratedDerivWithin_vcomp_eq_sum_orderedFinpartition, iteratedFDerivWithin_apply_eq_iteratedDerivWithin_mul_prod
-/
theorem iteratedDerivWithin_scomp_eq_sum_orderedFinpartition
    (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContDiffWithinAt 𝕜 n f s x)
    (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜 s) (hx : x in s) (hst : MapsTo f s t) (hi : i <= n) :
    iteratedDerivWithin i (g ∘ f) s x =
      ∑ c : OrderedFinpartition i,
        (∏ j, iteratedDerivWithin (c.partSize j) f s x) •
          iteratedDerivWithin c.length g t (f x) := by
  rw [iteratedDerivWithin_vcomp_eq_sum_orderedFinpartition hg hf ht hs hx hst hi]
  simp only [iteratedFDerivWithin_apply_eq_iteratedDerivWithin_mul_prod]

/--
theorem `iteratedDeriv_scomp_eq_sum_orderedFinpartition` / 定理 `iteratedDeriv_scomp_eq_sum_orderedFinpartition`

English:
theorem iteratedDeriv_scomp_eq_sum_orderedFinpartition
  proof: by
  rw [iteratedDeriv_vcomp_eq_sum_orderedFinpartition hg hf hi]
  simp only [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]

中文:
定理 iteratedDeriv_scomp_eq_sum_orderedFinpartition
  证明: by
  rw [iteratedDeriv_vcomp_eq_sum_orderedFinpartition hg hf hi]
  simp only [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]

Depends on / 依赖: iteratedDeriv_vcomp_eq_sum_orderedFinpartition, iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod
-/
theorem iteratedDeriv_scomp_eq_sum_orderedFinpartition
    (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffAt 𝕜 n f x) (hi : i <= n) :
    iteratedDeriv i (g ∘ f) x =
      ∑ c : OrderedFinpartition i,
        (∏ j, iteratedDeriv (c.partSize j) f x) • iteratedDeriv c.length g (f x) := by
  rw [iteratedDeriv_vcomp_eq_sum_orderedFinpartition hg hf hi]
  simp only [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]

/--
theorem `iteratedDerivWithin_scomp_two` / 定理 `iteratedDerivWithin_scomp_two`

English:
theorem iteratedDerivWithin_scomp_two
  proof: by
  rw [iteratedDerivWithin_vcomp_two hg hf ht hs hx hst]
  simp [← toSpanSingleton_derivWithin, iteratedFDerivWithin_apply_eq_iteratedDerivWithin_mul_prod]

中文:
定理 iteratedDerivWithin_scomp_two
  证明: by
  rw [iteratedDerivWithin_vcomp_two hg hf ht hs hx hst]
  simp [← toSpanSingleton_derivWithin, iteratedFDerivWithin_apply_eq_iteratedDerivWithin_mul_prod]

Depends on / 依赖: iteratedDerivWithin_vcomp_two, iteratedFDerivWithin_apply_eq_iteratedDerivWithin_mul_prod, toSpanSingleton_derivWithin
-/
theorem iteratedDerivWithin_scomp_two
    (hg : ContDiffWithinAt 𝕜 2 g t (f x)) (hf : ContDiffWithinAt 𝕜 2 f s x)
    (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜 s) (hx : x in s) (hst : MapsTo f s t) :
    iteratedDerivWithin 2 (g ∘ f) s x =
      derivWithin f s x ^ 2 • iteratedDerivWithin 2 g t (f x) +
      iteratedDerivWithin 2 f s x • derivWithin g t (f x) := by
  rw [iteratedDerivWithin_vcomp_two hg hf ht hs hx hst]
  simp [← toSpanSingleton_derivWithin, iteratedFDerivWithin_apply_eq_iteratedDerivWithin_mul_prod]

/--
theorem `iteratedDeriv_scomp_two` / 定理 `iteratedDeriv_scomp_two`

English:
theorem iteratedDeriv_scomp_two
  given: (hg : ContDiffAt 𝕜 2 g (f x)) (hf : ContDiffAt 𝕜 2 f x)
  proof: by
  simp only [← iteratedDerivWithin_univ, ← derivWithin_univ]
  exact iteratedDerivWithin_scomp_two hg hf uniqueDiffOn_univ uniqueDiffOn_univ (mem_univ _)
    (mapsTo_univ _ _)

中文:
定理 iteratedDeriv_scomp_two
  条件: (hg : ContDiffAt 𝕜 2 g (f x)) (hf : ContDiffAt 𝕜 2 f x)
  证明: by
  simp only [← iteratedDerivWithin_univ, ← derivWithin_univ]
  exact iteratedDerivWithin_scomp_two hg hf uniqueDiffOn_univ uniqueDiffOn_univ (mem_univ _)
    (mapsTo_univ _ _)

Depends on / 依赖: derivWithin_univ, iteratedDerivWithin_scomp_two, iteratedDerivWithin_univ, mapsTo_univ, mem_univ, uniqueDiffOn_univ
-/
theorem iteratedDeriv_scomp_two (hg : ContDiffAt 𝕜 2 g (f x)) (hf : ContDiffAt 𝕜 2 f x) :
    iteratedDeriv 2 (g ∘ f) x
      = deriv f x ^ 2 • iteratedDeriv 2 g (f x) + iteratedDeriv 2 f x • deriv g (f x) := by
  simp only [← iteratedDerivWithin_univ, ← derivWithin_univ]
  exact iteratedDerivWithin_scomp_two hg hf uniqueDiffOn_univ uniqueDiffOn_univ (mem_univ _)
    (mapsTo_univ _ _)

/--
theorem `iteratedDerivWithin_scomp_three` / 定理 `iteratedDerivWithin_scomp_three`

English:
theorem iteratedDerivWithin_scomp_three
  proof: by
  rw [iteratedDerivWithin_vcomp_three hg hf ht hs hx hst]
  simp [← toSpanSingleton_derivWithin, mul_smul, smul_comm (iteratedDerivWithin 2 f s x),
        iteratedFDerivWithin_apply_eq_iteratedDerivWithin_mul_prod]
  abel

中文:
定理 iteratedDerivWithin_scomp_three
  证明: by
  rw [iteratedDerivWithin_vcomp_three hg hf ht hs hx hst]
  simp [← toSpanSingleton_derivWithin, mul_smul, smul_comm (iteratedDerivWithin 2 f s x),
        iteratedFDerivWithin_apply_eq_iteratedDerivWithin_mul_prod]
  abel

Depends on / 依赖: iteratedDerivWithin, iteratedDerivWithin_vcomp_three, iteratedFDerivWithin_apply_eq_iteratedDerivWithin_mul_prod, mul_smul, smul_comm, toSpanSingleton_derivWithin
-/
theorem iteratedDerivWithin_scomp_three
    (hg : ContDiffWithinAt 𝕜 3 g t (f x)) (hf : ContDiffWithinAt 𝕜 3 f s x)
    (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜 s) (hx : x in s) (hst : MapsTo f s t) :
    iteratedDerivWithin 3 (g ∘ f) s x =
      derivWithin f s x ^ 3 • iteratedDerivWithin 3 g t (f x) +
      3 • iteratedDerivWithin 2 f s x • derivWithin f s x • iteratedDerivWithin 2 g t (f x) +
      iteratedDerivWithin 3 f s x • derivWithin g t (f x) := by
  rw [iteratedDerivWithin_vcomp_three hg hf ht hs hx hst]
  simp [← toSpanSingleton_derivWithin, mul_smul, smul_comm (iteratedDerivWithin 2 f s x),
        iteratedFDerivWithin_apply_eq_iteratedDerivWithin_mul_prod]
  abel

/--
theorem `iteratedDeriv_scomp_three` / 定理 `iteratedDeriv_scomp_three`

English:
theorem iteratedDeriv_scomp_three
  given: (hg : ContDiffAt 𝕜 3 g (f x)) (hf : ContDiffAt 𝕜 3 f x)
  proof: by
  simp only [← iteratedDerivWithin_univ, ← derivWithin_univ]
  exact iteratedDerivWithin_scomp_three hg hf uniqueDiffOn_univ uniqueDiffOn_univ (mem_univ _)
    (mapsTo_univ _ _)

中文:
定理 iteratedDeriv_scomp_three
  条件: (hg : ContDiffAt 𝕜 3 g (f x)) (hf : ContDiffAt 𝕜 3 f x)
  证明: by
  simp only [← iteratedDerivWithin_univ, ← derivWithin_univ]
  exact iteratedDerivWithin_scomp_three hg hf uniqueDiffOn_univ uniqueDiffOn_univ (mem_univ _)
    (mapsTo_univ _ _)

Depends on / 依赖: derivWithin_univ, iteratedDerivWithin_scomp_three, iteratedDerivWithin_univ, mapsTo_univ, mem_univ, uniqueDiffOn_univ
-/
theorem iteratedDeriv_scomp_three (hg : ContDiffAt 𝕜 3 g (f x)) (hf : ContDiffAt 𝕜 3 f x) :
    iteratedDeriv 3 (g ∘ f) x =
      deriv f x ^ 3 • iteratedDeriv 3 g (f x) +
      3 • iteratedDeriv 2 f x • deriv f x • iteratedDeriv 2 g (f x) +
      iteratedDeriv 3 f x • deriv g (f x) := by
  simp only [← iteratedDerivWithin_univ, ← derivWithin_univ]
  exact iteratedDerivWithin_scomp_three hg hf uniqueDiffOn_univ uniqueDiffOn_univ (mem_univ _)
    (mapsTo_univ _ _)

end scomp

section comp

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {g f : 𝕜 -> 𝕜} {s t : Set 𝕜} {x : 𝕜} {n : Nat∞ω} {i : Nat}

/--
theorem `iteratedDerivWithin_comp_eq_sum_orderedFinpartition` / 定理 `iteratedDerivWithin_comp_eq_sum_orderedFinpartition`

English:
theorem iteratedDerivWithin_comp_eq_sum_orderedFinpartition
  proof: by
  rw [iteratedDerivWithin_scomp_eq_sum_orderedFinpartition hg hf ht hs hx hst hi]
  simp only [smul_eq_mul, mul_comm]

中文:
定理 iteratedDerivWithin_comp_eq_sum_orderedFinpartition
  证明: by
  rw [iteratedDerivWithin_scomp_eq_sum_orderedFinpartition hg hf ht hs hx hst hi]
  simp only [smul_eq_mul, mul_comm]

Depends on / 依赖: iteratedDerivWithin_scomp_eq_sum_orderedFinpartition, mul_comm, smul_eq_mul
-/
theorem iteratedDerivWithin_comp_eq_sum_orderedFinpartition
    (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContDiffWithinAt 𝕜 n f s x)
    (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜 s) (hx : x in s) (hst : MapsTo f s t) (hi : i <= n) :
    iteratedDerivWithin i (g ∘ f) s x =
      ∑ c : OrderedFinpartition i,
        iteratedDerivWithin c.length g t (f x) * ∏ j, iteratedDerivWithin (c.partSize j) f s x := by
  rw [iteratedDerivWithin_scomp_eq_sum_orderedFinpartition hg hf ht hs hx hst hi]
  simp only [smul_eq_mul, mul_comm]

/--
theorem `iteratedDeriv_comp_eq_sum_orderedFinpartition` / 定理 `iteratedDeriv_comp_eq_sum_orderedFinpartition`

English:
theorem iteratedDeriv_comp_eq_sum_orderedFinpartition
  proof: by
  rw [iteratedDeriv_scomp_eq_sum_orderedFinpartition hg hf hi]
  simp only [smul_eq_mul, mul_comm]

中文:
定理 iteratedDeriv_comp_eq_sum_orderedFinpartition
  证明: by
  rw [iteratedDeriv_scomp_eq_sum_orderedFinpartition hg hf hi]
  simp only [smul_eq_mul, mul_comm]

Depends on / 依赖: iteratedDeriv_scomp_eq_sum_orderedFinpartition, mul_comm, smul_eq_mul
-/
theorem iteratedDeriv_comp_eq_sum_orderedFinpartition
    (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffAt 𝕜 n f x) (hi : i <= n) :
    iteratedDeriv i (g ∘ f) x =
      ∑ c : OrderedFinpartition i,
        iteratedDeriv c.length g (f x) * ∏ j, iteratedDeriv (c.partSize j) f x := by
  rw [iteratedDeriv_scomp_eq_sum_orderedFinpartition hg hf hi]
  simp only [smul_eq_mul, mul_comm]

/--
theorem `iteratedDerivWithin_comp_two` / 定理 `iteratedDerivWithin_comp_two`

English:
theorem iteratedDerivWithin_comp_two
  proof: by
  rw [iteratedDerivWithin_scomp_two hg hf ht hs hx hst]
  simp only [smul_eq_mul, mul_comm]

中文:
定理 iteratedDerivWithin_comp_two
  证明: by
  rw [iteratedDerivWithin_scomp_two hg hf ht hs hx hst]
  simp only [smul_eq_mul, mul_comm]

Depends on / 依赖: iteratedDerivWithin_scomp_two, mul_comm, smul_eq_mul
-/
theorem iteratedDerivWithin_comp_two
    (hg : ContDiffWithinAt 𝕜 2 g t (f x)) (hf : ContDiffWithinAt 𝕜 2 f s x)
    (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜 s) (hx : x in s) (hst : MapsTo f s t) :
    iteratedDerivWithin 2 (g ∘ f) s x =
      iteratedDerivWithin 2 g t (f x) * derivWithin f s x ^ 2 +
      derivWithin g t (f x) * iteratedDerivWithin 2 f s x := by
  rw [iteratedDerivWithin_scomp_two hg hf ht hs hx hst]
  simp only [smul_eq_mul, mul_comm]

/--
theorem `iteratedDeriv_comp_two` / 定理 `iteratedDeriv_comp_two`

English:
theorem iteratedDeriv_comp_two
  given: (hg : ContDiffAt 𝕜 2 g (f x)) (hf : ContDiffAt 𝕜 2 f x)
  proof: by
  simp only [← iteratedDerivWithin_univ, ← derivWithin_univ]
  exact iteratedDerivWithin_comp_two hg hf uniqueDiffOn_univ uniqueDiffOn_univ (mem_univ _)
    (mapsTo_univ _ _)

中文:
定理 iteratedDeriv_comp_two
  条件: (hg : ContDiffAt 𝕜 2 g (f x)) (hf : ContDiffAt 𝕜 2 f x)
  证明: by
  simp only [← iteratedDerivWithin_univ, ← derivWithin_univ]
  exact iteratedDerivWithin_comp_two hg hf uniqueDiffOn_univ uniqueDiffOn_univ (mem_univ _)
    (mapsTo_univ _ _)

Depends on / 依赖: derivWithin_univ, iteratedDerivWithin_comp_two, iteratedDerivWithin_univ, mapsTo_univ, mem_univ, uniqueDiffOn_univ
-/
theorem iteratedDeriv_comp_two (hg : ContDiffAt 𝕜 2 g (f x)) (hf : ContDiffAt 𝕜 2 f x) :
    iteratedDeriv 2 (g ∘ f) x =
      iteratedDeriv 2 g (f x) * deriv f x ^ 2 + deriv g (f x) * iteratedDeriv 2 f x := by
  simp only [← iteratedDerivWithin_univ, ← derivWithin_univ]
  exact iteratedDerivWithin_comp_two hg hf uniqueDiffOn_univ uniqueDiffOn_univ (mem_univ _)
    (mapsTo_univ _ _)

/--
theorem `iteratedDerivWithin_comp_three` / 定理 `iteratedDerivWithin_comp_three`

English:
theorem iteratedDerivWithin_comp_three
  proof: by
  rw [iteratedDerivWithin_scomp_three hg hf ht hs hx hst]
  simp only [nsmul_eq_mul, smul_eq_mul, Nat.cast_ofNat]
  ring

中文:
定理 iteratedDerivWithin_comp_three
  证明: by
  rw [iteratedDerivWithin_scomp_three hg hf ht hs hx hst]
  simp only [nsmul_eq_mul, smul_eq_mul, Nat.cast_ofNat]
  ring

Depends on / 依赖: Nat.cast_ofNat, cast_ofNat, iteratedDerivWithin_scomp_three, nsmul_eq_mul, smul_eq_mul
-/
theorem iteratedDerivWithin_comp_three
    (hg : ContDiffWithinAt 𝕜 3 g t (f x)) (hf : ContDiffWithinAt 𝕜 3 f s x)
    (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜 s) (hx : x in s) (hst : MapsTo f s t) :
    iteratedDerivWithin 3 (g ∘ f) s x =
      iteratedDerivWithin 3 g t (f x) * derivWithin f s x ^ 3 +
      3 * iteratedDerivWithin 2 g t (f x) * iteratedDerivWithin 2 f s x * derivWithin f s x +
      derivWithin g t (f x) * iteratedDerivWithin 3 f s x := by
  rw [iteratedDerivWithin_scomp_three hg hf ht hs hx hst]
  simp only [nsmul_eq_mul, smul_eq_mul, Nat.cast_ofNat]
  ring

/--
theorem `iteratedDeriv_comp_three` / 定理 `iteratedDeriv_comp_three`

English:
theorem iteratedDeriv_comp_three
  given: (hg : ContDiffAt 𝕜 3 g (f x)) (hf : ContDiffAt 𝕜 3 f x)
  proof: by
  simp only [← iteratedDerivWithin_univ, ← derivWithin_univ]
  exact iteratedDerivWithin_comp_three hg hf uniqueDiffOn_univ uniqueDiffOn_univ (mem_univ _)
    (mapsTo_univ _ _)

中文:
定理 iteratedDeriv_comp_three
  条件: (hg : ContDiffAt 𝕜 3 g (f x)) (hf : ContDiffAt 𝕜 3 f x)
  证明: by
  simp only [← iteratedDerivWithin_univ, ← derivWithin_univ]
  exact iteratedDerivWithin_comp_three hg hf uniqueDiffOn_univ uniqueDiffOn_univ (mem_univ _)
    (mapsTo_univ _ _)

Depends on / 依赖: derivWithin_univ, iteratedDerivWithin_comp_three, iteratedDerivWithin_univ, mapsTo_univ, mem_univ, uniqueDiffOn_univ
-/
theorem iteratedDeriv_comp_three (hg : ContDiffAt 𝕜 3 g (f x)) (hf : ContDiffAt 𝕜 3 f x) :
    iteratedDeriv 3 (g ∘ f) x =
      iteratedDeriv 3 g (f x) * deriv f x ^ 3 +
      3 * iteratedDeriv 2 g (f x) * iteratedDeriv 2 f x * deriv f x +
      deriv g (f x) * iteratedDeriv 3 f x := by
  simp only [← iteratedDerivWithin_univ, ← derivWithin_univ]
  exact iteratedDerivWithin_comp_three hg hf uniqueDiffOn_univ uniqueDiffOn_univ (mem_univ _)
    (mapsTo_univ _ _)

end comp
