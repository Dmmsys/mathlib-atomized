/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Higher differentiability of composition

We prove that the composition of `C^n` functions is `C^n`.
We also expand the API around `C^n` functions.

## Main results

* `ContDiff.comp` states that the composition of two `C^n` functions is `C^n`.

Similar results are given for `C^n` functions on domains.

## Notation

We use the notation `E [×n]→L[𝕜] F` for the space of continuous multilinear maps on `E^n` with
values in `F`. This is the space in which the `n`-th derivative of a function from `E` to `F` lives.

In this file, we denote `WithTop ℕ∞` with `ℕ∞ω`, `(⊤ : ℕ∞) : ℕ∞ω` with `∞` and `⊤ : ℕ∞ω` with `ω`.

## Tags

derivative, differentiability, higher derivative, `C^n`, multilinear, Taylor series, formal series
-/

public noncomputable section

open Set Filter Function

open scoped Topology ContDiff

attribute [local instance 1001] NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X] {s t : Set E} {f : E -> F}
  {g : F -> G} {x x₀ : E} {m n : Nat∞ω}

section comp

/-!
### Composition of `C^n` functions

We show that the composition of `C^n` functions is `C^n`. One way to do this would be to
use the following simple inductive proof. Assume it is done for `n`.
Then, to check it for `n+1`, one needs to check that the derivative of `g ∘ f` is `C^n`, i.e.,
that `Dg(f x) ⬝ Df(x)` is `C^n`. The term `Dg (f x)` is the composition of two `C^n` functions, so
it is `C^n` by the inductive assumption. The term `Df(x)` is also `C^n`. Then, the matrix
multiplication is the application of a bilinear map (which is `C^∞`, and therefore `C^n`) to
`x ↦ (Dg(f x), Df x)`. As the composition of two `C^n` maps, it is again `C^n`, and we are done.

There are two difficulties in this proof.

The first one is that it is an induction over all Banach
spaces. In Lean, this is only possible if they belong to a fixed universe. One could formalize this
by first proving the statement in this case, and then extending the result to general universes
by embedding all the spaces we consider in a common universe through `ULift`.

The second one is that it does not work cleanly for analytic maps: for this case, we need to
exhibit a whole sequence of derivatives which are all analytic, not just finitely many of them, so
an induction is never enough at a finite step.

Both these difficulties can be overcome with some cost. However, we choose a different path: we
write down an explicit formula for the `n`-th derivative of `g ∘ f` in terms of derivatives of
`g` and `f` (this is the formula of Faa-Di Bruno) and use this formula to get a suitable Taylor
expansion for `g ∘ f`. Writing down the formula of Faa-Di Bruno is not easy as the formula is quite
intricate, but it is also useful for other purposes and once available it makes the proof here
essentially trivial.
-/

/--
theorem `ContDiffWithinAt.comp` / 定理 `ContDiffWithinAt.comp`

English:
theorem ContDiffWithinAt.comp
  statement: {s : Set E} {t : Set F} {g : F -> G} {f : E -> F} (x : E)
  proof: by
  match n with
  | ω =>
    have h'f : ContDiffWithinAt 𝕜 ω f s x := hf
    obtain ⟨u, hu, p, hp, h'p⟩ := h'f
    obtain ⟨v, hv, q, hq, h'q⟩ := hg
    let w := insert x s inter (u inter f ⁻¹' v)
    have wv : w subseteq f ⁻¹' v := fun y hy => hy.2.2
    have wu : w subseteq u := fun y hy => hy.2.1
    refine ⟨w, ?_, fun y => (q (f y)).taylorComp (p y), hq.comp (hp.mono wu) wv, ?_⟩
    · apply inter_mem self_mem_nhdsWithin (inter_mem hu ?_)
      apply (continuousWithinAt_insert_self.2 hf.continuousWithinAt).preimage_mem_nhdsWithin'
      apply nhdsWithin_mono _ _ hv
      simp only [image_insert_eq]
      apply insert_subset_insert
      exact image_subset_iff.mpr st
    · have : AnalyticOn 𝕜 f w := by
        have : AnalyticOn 𝕜 (fun y => (continuousMultilinearCurryFin0 𝕜 E F).symm (f y)) w :=
          ((h'p 0).mono wu).congr fun y hy => (hp.zero_eq' (wu hy)).symm
        have : AnalyticOn 𝕜 (fun y => (continuousMultilinearCurryFin0 𝕜 E F)
            ((continuousMultilinearCurryFin0 𝕜 E F).symm (f y))) w :=
          AnalyticOnNhd.comp_analyticOn (LinearIsometryEquiv.analyticOnNhd _ _) this
          (mapsTo_univ _ _)
        simpa using this
      exact analyticOn_taylorComp h'q (fun n => (h'p n).mono wu) this wv
  | (n : Nat∞) =>
    intro m hm
    rcases hf m hm with ⟨u, hu, p, hp⟩
    rcases hg m hm with ⟨v, hv, q, hq⟩
    let w := insert x s inter (u inter f ⁻¹' v)
    have wv : w subseteq f ⁻¹' v := fun y hy => hy.2.2
    have wu : w subseteq u := fun y hy => hy.2.1
    refine ⟨w, ?_, fun y => (q (f y)).taylorComp (p y), hq.comp (hp.mono wu) wv⟩
    apply inter_mem self_mem_nhdsWithin (inter_mem hu ?_)
    apply (continuousWithinAt_insert_self.2 hf.continuousWithinAt).preimage_mem_nhdsWithin'
    apply nhdsWithin_mono _ _ hv
    simp only [image_insert_eq]
    apply insert_subset_insert
    exact image_subset_iff.mpr st

中文:
定理 ContDiffWithinAt.comp
  结论: {s : 集合 E} {t : 集合 F} {g : F -> G} {f : E -> F} (x : E)
  证明: by
  match n with
  | ω =>
    have h'f : ContDiffWithinAt 𝕜 ω f s x := hf
    obtain ⟨u, hu, p, hp, h'p⟩ := h'f
    obtain ⟨v, hv, q, hq, h'q⟩ := hg
    let w := insert x s inter (u inter f ⁻¹' v)
    have wv : w subseteq f ⁻¹' v := fun y hy => hy.2.2
    have wu : w subseteq u := fun y hy => hy.2.1
    refine ⟨w, ?_, fun y => (q (f y)).taylorComp (p y), hq.comp (hp.mono wu) wv, ?_⟩
    · apply inter_mem self_mem_nhdsWithin (inter_mem hu ?_)
      apply (continuousWithinAt_insert_self.2 hf.continuousWithinAt).preimage_mem_nhdsWithin'
      apply nhdsWithin_mono _ _ hv
      simp only [image_insert_eq]
      apply insert_subset_insert
      exact image_subset_iff.mpr st
    · have : AnalyticOn 𝕜 f w := by
        have : AnalyticOn 𝕜 (fun y => (continuousMultilinearCurryFin0 𝕜 E F).symm (f y)) w :=
          ((h'p 0).mono wu).congr fun y hy => (hp.zero_eq' (wu hy)).symm
        have : AnalyticOn 𝕜 (fun y => (continuousMultilinearCurryFin0 𝕜 E F)
            ((continuousMultilinearCurryFin0 𝕜 E F).symm (f y))) w :=
          AnalyticOnNhd.comp_analyticOn (LinearIsometryEquiv.analyticOnNhd _ _) this
          (mapsTo_univ _ _)
        simpa using this
      exact analyticOn_taylorComp h'q (fun n => (h'p n).mono wu) this wv
  | (n : Nat∞) =>
    intro m hm
    rcases hf m hm with ⟨u, hu, p, hp⟩
    rcases hg m hm with ⟨v, hv, q, hq⟩
    let w := insert x s inter (u inter f ⁻¹' v)
    have wv : w subseteq f ⁻¹' v := fun y hy => hy.2.2
    have wu : w subseteq u := fun y hy => hy.2.1
    refine ⟨w, ?_, fun y => (q (f y)).taylorComp (p y), hq.comp (hp.mono wu) wv⟩
    apply inter_mem self_mem_nhdsWithin (inter_mem hu ?_)
    apply (continuousWithinAt_insert_self.2 hf.continuousWithinAt).preimage_mem_nhdsWithin'
    apply nhdsWithin_mono _ _ hv
    simp only [image_insert_eq]
    apply insert_subset_insert
    exact image_subset_iff.mpr st

Depends on / 依赖: ContDiffWithinAt, continuousWithinAt, continuousWithinAt_insert_self, hf.continuousWithinAt, hp.mono, hq.comp, insert, inter_mem, preimage_mem_nhdsWithin, self_mem_nhdsWithin, subseteq, taylorComp
-/
theorem ContDiffWithinAt.comp {s : Set E} {t : Set F} {g : F -> G} {f : E -> F} (x : E)
    (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContDiffWithinAt 𝕜 n f s x) (st : MapsTo f s t) :
    ContDiffWithinAt 𝕜 n (g ∘ f) s x := by
  match n with
  | ω =>
    have h'f : ContDiffWithinAt 𝕜 ω f s x := hf
    obtain ⟨u, hu, p, hp, h'p⟩ := h'f
    obtain ⟨v, hv, q, hq, h'q⟩ := hg
    let w := insert x s inter (u inter f ⁻¹' v)
    have wv : w subseteq f ⁻¹' v := fun y hy => hy.2.2
    have wu : w subseteq u := fun y hy => hy.2.1
    refine ⟨w, ?_, fun y => (q (f y)).taylorComp (p y), hq.comp (hp.mono wu) wv, ?_⟩
    · apply inter_mem self_mem_nhdsWithin (inter_mem hu ?_)
      apply (continuousWithinAt_insert_self.2 hf.continuousWithinAt).preimage_mem_nhdsWithin'
      apply nhdsWithin_mono _ _ hv
      simp only [image_insert_eq]
      apply insert_subset_insert
      exact image_subset_iff.mpr st
    · have : AnalyticOn 𝕜 f w := by
        have : AnalyticOn 𝕜 (fun y => (continuousMultilinearCurryFin0 𝕜 E F).symm (f y)) w :=
          ((h'p 0).mono wu).congr fun y hy => (hp.zero_eq' (wu hy)).symm
        have : AnalyticOn 𝕜 (fun y => (continuousMultilinearCurryFin0 𝕜 E F)
            ((continuousMultilinearCurryFin0 𝕜 E F).symm (f y))) w :=
          AnalyticOnNhd.comp_analyticOn (LinearIsometryEquiv.analyticOnNhd _ _) this
          (mapsTo_univ _ _)
        simpa using this
      exact analyticOn_taylorComp h'q (fun n => (h'p n).mono wu) this wv
  | (n : Nat∞) =>
    intro m hm
    rcases hf m hm with ⟨u, hu, p, hp⟩
    rcases hg m hm with ⟨v, hv, q, hq⟩
    let w := insert x s inter (u inter f ⁻¹' v)
    have wv : w subseteq f ⁻¹' v := fun y hy => hy.2.2
    have wu : w subseteq u := fun y hy => hy.2.1
    refine ⟨w, ?_, fun y => (q (f y)).taylorComp (p y), hq.comp (hp.mono wu) wv⟩
    apply inter_mem self_mem_nhdsWithin (inter_mem hu ?_)
    apply (continuousWithinAt_insert_self.2 hf.continuousWithinAt).preimage_mem_nhdsWithin'
    apply nhdsWithin_mono _ _ hv
    simp only [image_insert_eq]
    apply insert_subset_insert
    exact image_subset_iff.mpr st

/--
theorem `ContDiffOn.comp` / 定理 `ContDiffOn.comp`

English:
theorem ContDiffOn.comp
  statement: {s : Set E} {t : Set F} {g : F -> G} {f : E -> F} (hg : ContDiffOn 𝕜 n g t)
  proof: fun x hx => ContDiffWithinAt.comp x (hg (f x) (st hx)) (hf x hx) st

中文:
定理 ContDiffOn.comp
  结论: {s : 集合 E} {t : 集合 F} {g : F -> G} {f : E -> F} (hg : ContDiffOn 𝕜 n g t)
  证明: fun x hx => ContDiffWithinAt.comp x (hg (f x) (st hx)) (hf x hx) st

Depends on / 依赖: ContDiffWithinAt, ContDiffWithinAt.comp
-/
theorem ContDiffOn.comp {s : Set E} {t : Set F} {g : F -> G} {f : E -> F} (hg : ContDiffOn 𝕜 n g t)
    (hf : ContDiffOn 𝕜 n f s) (st : MapsTo f s t) : ContDiffOn 𝕜 n (g ∘ f) s :=
  fun x hx => ContDiffWithinAt.comp x (hg (f x) (st hx)) (hf x hx) st

/--
theorem `ContDiffOn.comp_inter` / 定理 `ContDiffOn.comp_inter`

English:
theorem ContDiffOn.comp_inter
  proof: hg.comp (hf.mono inter_subset_left) inter_subset_right

中文:
定理 ContDiffOn.comp_inter
  证明: hg.comp (hf.mono inter_subset_left) inter_subset_right

Depends on / 依赖: hf.mono, hg.comp, inter_subset_left, inter_subset_right
-/
theorem ContDiffOn.comp_inter
    {s : Set E} {t : Set F} {g : F -> G} {f : E -> F} (hg : ContDiffOn 𝕜 n g t)
    (hf : ContDiffOn 𝕜 n f s) : ContDiffOn 𝕜 n (g ∘ f) (s inter f ⁻¹' t) :=
  hg.comp (hf.mono inter_subset_left) inter_subset_right

/--
theorem `ContDiff.comp_contDiffOn` / 定理 `ContDiff.comp_contDiffOn`

English:
theorem ContDiff.comp_contDiffOn
  statement: {s : Set E} {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 n g)
  proof: (contDiffOn_univ.2 hg).comp hf (mapsTo_univ _ _)

@[fun_prop]

中文:
定理 连续可微.comp_contDiffOn
  结论: {s : 集合 E} {g : F -> G} {f : E -> F} (hg : 连续可微 𝕜 n g)
  证明: (contDiffOn_univ.2 hg).comp hf (mapsTo_univ _ _)

@[fun_prop]

Depends on / 依赖: contDiffOn_univ, mapsTo_univ
-/
theorem ContDiff.comp_contDiffOn {s : Set E} {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 n g)
    (hf : ContDiffOn 𝕜 n f s) : ContDiffOn 𝕜 n (g ∘ f) s :=
  (contDiffOn_univ.2 hg).comp hf (mapsTo_univ _ _)

@[fun_prop]
/--
theorem `ContDiff.fun_comp_contDiffOn` / 定理 `ContDiff.fun_comp_contDiffOn`

English:
theorem ContDiff.fun_comp_contDiffOn
  statement: {s : Set E} {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 n g)
  proof: (contDiffOn_univ.2 hg).comp hf (mapsTo_univ _ _)

中文:
定理 连续可微.fun_comp_contDiffOn
  结论: {s : 集合 E} {g : F -> G} {f : E -> F} (hg : 连续可微 𝕜 n g)
  证明: (contDiffOn_univ.2 hg).comp hf (mapsTo_univ _ _)

Depends on / 依赖: contDiffOn_univ, mapsTo_univ
-/
theorem ContDiff.fun_comp_contDiffOn {s : Set E} {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 n g)
    (hf : ContDiffOn 𝕜 n f s) : ContDiffOn 𝕜 n (fun x => g (f x)) s :=
  (contDiffOn_univ.2 hg).comp hf (mapsTo_univ _ _)

/--
theorem `ContDiffOn.comp_contDiff` / 定理 `ContDiffOn.comp_contDiff`

English:
theorem ContDiffOn.comp_contDiff
  statement: {s : Set F} {g : F -> G} {f : E -> F} (hg : ContDiffOn 𝕜 n g s)
  proof: by
  rw [← contDiffOn_univ] at *
  exact hg.comp hf fun x _ => hs x

中文:
定理 ContDiffOn.comp_contDiff
  结论: {s : 集合 F} {g : F -> G} {f : E -> F} (hg : ContDiffOn 𝕜 n g s)
  证明: by
  rw [← contDiffOn_univ] at *
  exact hg.comp hf fun x _ => hs x

Depends on / 依赖: contDiffOn_univ, hg.comp
-/
theorem ContDiffOn.comp_contDiff {s : Set F} {g : F -> G} {f : E -> F} (hg : ContDiffOn 𝕜 n g s)
    (hf : ContDiff 𝕜 n f) (hs : forall x, f x in s) : ContDiff 𝕜 n (g ∘ f) := by
  rw [← contDiffOn_univ] at *
  exact hg.comp hf fun x _ => hs x

/--
theorem `ContDiffOn.image_comp_contDiff` / 定理 `ContDiffOn.image_comp_contDiff`

English:
theorem ContDiffOn.image_comp_contDiff
  statement: {s : Set E} {g : F -> G} {f : E -> F}
  proof: hg.comp hf.contDiffOn (s.mapsTo_image f)

中文:
定理 ContDiffOn.image_comp_contDiff
  结论: {s : 集合 E} {g : F -> G} {f : E -> F}
  证明: hg.comp hf.contDiffOn (s.mapsTo_image f)

Depends on / 依赖: contDiffOn, hf.contDiffOn, hg.comp, mapsTo_image, s.mapsTo_image
-/
theorem ContDiffOn.image_comp_contDiff {s : Set E} {g : F -> G} {f : E -> F}
    (hg : ContDiffOn 𝕜 n g (f '' s)) (hf : ContDiff 𝕜 n f) : ContDiffOn 𝕜 n (g ∘ f) s :=
  hg.comp hf.contDiffOn (s.mapsTo_image f)

/--
theorem `ContDiff.comp` / 定理 `ContDiff.comp`

English:
theorem ContDiff.comp
  given: {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 n g) (hf : ContDiff 𝕜 n f)
  proof: contDiffOn_univ.1 ContDiffOn.comp (contDiffOn_univ.2 hg) (contDiffOn_univ.2 hf) (subset_univ _)

@[fun_prop]

中文:
定理 连续可微.comp
  条件: {g : F -> G} {f : E -> F} (hg : 连续可微 𝕜 n g) (hf : 连续可微 𝕜 n f)
  证明: contDiffOn_univ.1 ContDiffOn.comp (contDiffOn_univ.2 hg) (contDiffOn_univ.2 hf) (subset_univ _)

@[fun_prop]

Depends on / 依赖: ContDiffOn, ContDiffOn.comp, contDiffOn_univ, subset_univ
-/
theorem ContDiff.comp {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 n g) (hf : ContDiff 𝕜 n f) :
    ContDiff 𝕜 n (g ∘ f) :=
contDiffOn_univ.1 ContDiffOn.comp (contDiffOn_univ.2 hg) (contDiffOn_univ.2 hf) (subset_univ _)

@[fun_prop]
/--
theorem `ContDiff.fun_comp` / 定理 `ContDiff.fun_comp`

English:
theorem ContDiff.fun_comp
  given: {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 n g) (hf : ContDiff 𝕜 n f)
  proof: hg.comp hf

中文:
定理 连续可微.fun_comp
  条件: {g : F -> G} {f : E -> F} (hg : 连续可微 𝕜 n g) (hf : 连续可微 𝕜 n f)
  证明: hg.comp hf

Depends on / 依赖: hg.comp
-/
theorem ContDiff.fun_comp {g : F -> G} {f : E -> F} (hg : ContDiff 𝕜 n g) (hf : ContDiff 𝕜 n f) :
    ContDiff 𝕜 n (fun x => g (f x)) := hg.comp hf

/--
theorem `ContDiffWithinAt.comp_of_eq` / 定理 `ContDiffWithinAt.comp_of_eq`

English:
theorem ContDiffWithinAt.comp_of_eq
  statement: {s : Set E} {t : Set F} {g : F -> G} {f : E -> F} {y : F} (x : E)
  proof: by
  subst hy; exact hg.comp x hf st

中文:
定理 ContDiffWithinAt.comp_of_eq
  结论: {s : 集合 E} {t : 集合 F} {g : F -> G} {f : E -> F} {y : F} (x : E)
  证明: by
  subst hy; exact hg.comp x hf st

Depends on / 依赖: hg.comp
-/
theorem ContDiffWithinAt.comp_of_eq {s : Set E} {t : Set F} {g : F -> G} {f : E -> F} {y : F} (x : E)
    (hg : ContDiffWithinAt 𝕜 n g t y) (hf : ContDiffWithinAt 𝕜 n f s x) (st : MapsTo f s t)
    (hy : f x = y) :
    ContDiffWithinAt 𝕜 n (g ∘ f) s x := by
  subst hy; exact hg.comp x hf st

/--
theorem `ContDiffWithinAt.comp_of_mem_nhdsWithin_image` / 定理 `ContDiffWithinAt.comp_of_mem_nhdsWithin_image`

English:
theorem ContDiffWithinAt.comp_of_mem_nhdsWithin_image
  proof: (hg.mono_of_mem_nhdsWithin hs).comp x hf (subset_preimage_image f s)

中文:
定理 ContDiffWithinAt.comp_of_mem_nhdsWithin_image
  证明: (hg.mono_of_mem_nhdsWithin hs).comp x hf (subset_preimage_image f s)

Depends on / 依赖: hg.mono_of_mem_nhdsWithin, mono_of_mem_nhdsWithin, subset_preimage_image
-/
theorem ContDiffWithinAt.comp_of_mem_nhdsWithin_image
    {s : Set E} {t : Set F} {g : F -> G} {f : E -> F} (x : E)
    (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContDiffWithinAt 𝕜 n f s x)
    (hs : t in 𝓝[f '' s] f x) : ContDiffWithinAt 𝕜 n (g ∘ f) s x :=
  (hg.mono_of_mem_nhdsWithin hs).comp x hf (subset_preimage_image f s)

/--
theorem `ContDiffWithinAt.comp_of_mem_nhdsWithin_image_of_eq` / 定理 `ContDiffWithinAt.comp_of_mem_nhdsWithin_image_of_eq`

English:
theorem ContDiffWithinAt.comp_of_mem_nhdsWithin_image_of_eq
  proof: by
  subst hy; exact hg.comp_of_mem_nhdsWithin_image x hf hs

中文:
定理 ContDiffWithinAt.comp_of_mem_nhdsWithin_image_of_eq
  证明: by
  subst hy; exact hg.comp_of_mem_nhdsWithin_image x hf hs

Depends on / 依赖: comp_of_mem_nhdsWithin_image, hg.comp_of_mem_nhdsWithin_image
-/
theorem ContDiffWithinAt.comp_of_mem_nhdsWithin_image_of_eq
    {s : Set E} {t : Set F} {g : F -> G} {f : E -> F} {y : F} (x : E)
    (hg : ContDiffWithinAt 𝕜 n g t y) (hf : ContDiffWithinAt 𝕜 n f s x)
    (hs : t in 𝓝[f '' s] f x) (hy : f x = y) : ContDiffWithinAt 𝕜 n (g ∘ f) s x := by
  subst hy; exact hg.comp_of_mem_nhdsWithin_image x hf hs

/--
theorem `ContDiffWithinAt.comp_inter` / 定理 `ContDiffWithinAt.comp_inter`

English:
theorem ContDiffWithinAt.comp_inter
  statement: {s : Set E} {t : Set F} {g : F -> G} {f : E -> F} (x : E)
  proof: hg.comp x (hf.mono inter_subset_left) inter_subset_right

中文:
定理 ContDiffWithinAt.comp_inter
  结论: {s : 集合 E} {t : 集合 F} {g : F -> G} {f : E -> F} (x : E)
  证明: hg.comp x (hf.mono inter_subset_left) inter_subset_right

Depends on / 依赖: hf.mono, hg.comp, inter_subset_left, inter_subset_right
-/
theorem ContDiffWithinAt.comp_inter {s : Set E} {t : Set F} {g : F -> G} {f : E -> F} (x : E)
    (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContDiffWithinAt 𝕜 n f s x) :
    ContDiffWithinAt 𝕜 n (g ∘ f) (s inter f ⁻¹' t) x :=
  hg.comp x (hf.mono inter_subset_left) inter_subset_right

/--
theorem `ContDiffWithinAt.comp_inter_of_eq` / 定理 `ContDiffWithinAt.comp_inter_of_eq`

English:
theorem ContDiffWithinAt.comp_inter_of_eq
  statement: {s : Set E} {t : Set F} {g : F -> G} {f : E -> F} {y : F}
  proof: by
  subst hy; exact hg.comp_inter x hf

中文:
定理 ContDiffWithinAt.comp_inter_of_eq
  结论: {s : 集合 E} {t : 集合 F} {g : F -> G} {f : E -> F} {y : F}
  证明: by
  subst hy; exact hg.comp_inter x hf

Depends on / 依赖: comp_inter, hg.comp_inter
-/
theorem ContDiffWithinAt.comp_inter_of_eq {s : Set E} {t : Set F} {g : F -> G} {f : E -> F} {y : F}
    (x : E) (hg : ContDiffWithinAt 𝕜 n g t y) (hf : ContDiffWithinAt 𝕜 n f s x) (hy : f x = y) :
    ContDiffWithinAt 𝕜 n (g ∘ f) (s inter f ⁻¹' t) x := by
  subst hy; exact hg.comp_inter x hf

/--
theorem `ContDiffWithinAt.comp_of_preimage_mem_nhdsWithin` / 定理 `ContDiffWithinAt.comp_of_preimage_mem_nhdsWithin`

English:
theorem ContDiffWithinAt.comp_of_preimage_mem_nhdsWithin
  proof: (hg.comp_inter x hf).mono_of_mem_nhdsWithin (inter_mem self_mem_nhdsWithin hs)

中文:
定理 ContDiffWithinAt.comp_of_preimage_mem_nhdsWithin
  证明: (hg.comp_inter x hf).mono_of_mem_nhdsWithin (inter_mem self_mem_nhdsWithin hs)

Depends on / 依赖: comp_inter, hg.comp_inter, inter_mem, mono_of_mem_nhdsWithin, self_mem_nhdsWithin
-/
theorem ContDiffWithinAt.comp_of_preimage_mem_nhdsWithin
    {s : Set E} {t : Set F} {g : F -> G} {f : E -> F} (x : E)
    (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContDiffWithinAt 𝕜 n f s x)
    (hs : f ⁻¹' t in 𝓝[s] x) : ContDiffWithinAt 𝕜 n (g ∘ f) s x :=
  (hg.comp_inter x hf).mono_of_mem_nhdsWithin (inter_mem self_mem_nhdsWithin hs)

/--
theorem `ContDiffWithinAt.comp_of_preimage_mem_nhdsWithin_of_eq` / 定理 `ContDiffWithinAt.comp_of_preimage_mem_nhdsWithin_of_eq`

English:
theorem ContDiffWithinAt.comp_of_preimage_mem_nhdsWithin_of_eq
  proof: by
  subst hy; exact hg.comp_of_preimage_mem_nhdsWithin x hf hs

中文:
定理 ContDiffWithinAt.comp_of_preimage_mem_nhdsWithin_of_eq
  证明: by
  subst hy; exact hg.comp_of_preimage_mem_nhdsWithin x hf hs

Depends on / 依赖: comp_of_preimage_mem_nhdsWithin, hg.comp_of_preimage_mem_nhdsWithin
-/
theorem ContDiffWithinAt.comp_of_preimage_mem_nhdsWithin_of_eq
    {s : Set E} {t : Set F} {g : F -> G} {f : E -> F} {y : F} (x : E)
    (hg : ContDiffWithinAt 𝕜 n g t y) (hf : ContDiffWithinAt 𝕜 n f s x)
    (hs : f ⁻¹' t in 𝓝[s] x) (hy : f x = y) : ContDiffWithinAt 𝕜 n (g ∘ f) s x := by
  subst hy; exact hg.comp_of_preimage_mem_nhdsWithin x hf hs

/--
theorem `ContDiffAt.comp_contDiffWithinAt` / 定理 `ContDiffAt.comp_contDiffWithinAt`

English:
theorem ContDiffAt.comp_contDiffWithinAt
  statement: (x : E) (hg : ContDiffAt 𝕜 n g (f x))
  proof: hg.comp x hf (mapsTo_univ _ _)

中文:
定理 ContDiffAt.comp_contDiffWithinAt
  结论: (x : E) (hg : ContDiffAt 𝕜 n g (f x))
  证明: hg.comp x hf (mapsTo_univ _ _)

Depends on / 依赖: hg.comp, mapsTo_univ
-/
theorem ContDiffAt.comp_contDiffWithinAt (x : E) (hg : ContDiffAt 𝕜 n g (f x))
    (hf : ContDiffWithinAt 𝕜 n f s x) : ContDiffWithinAt 𝕜 n (g ∘ f) s x :=
  hg.comp x hf (mapsTo_univ _ _)

/--
theorem `ContDiffAt.comp_contDiffWithinAt_of_eq` / 定理 `ContDiffAt.comp_contDiffWithinAt_of_eq`

English:
theorem ContDiffAt.comp_contDiffWithinAt_of_eq
  statement: {y : F} (x : E) (hg : ContDiffAt 𝕜 n g y)
  proof: by
  subst hy; exact hg.comp_contDiffWithinAt x hf

中文:
定理 ContDiffAt.comp_contDiffWithinAt_of_eq
  结论: {y : F} (x : E) (hg : ContDiffAt 𝕜 n g y)
  证明: by
  subst hy; exact hg.comp_contDiffWithinAt x hf

Depends on / 依赖: comp_contDiffWithinAt, hg.comp_contDiffWithinAt
-/
theorem ContDiffAt.comp_contDiffWithinAt_of_eq {y : F} (x : E) (hg : ContDiffAt 𝕜 n g y)
    (hf : ContDiffWithinAt 𝕜 n f s x) (hy : f x = y) : ContDiffWithinAt 𝕜 n (g ∘ f) s x := by
  subst hy; exact hg.comp_contDiffWithinAt x hf

/-- The composition of `C^n` functions at points is `C^n`. -/
nonrec theorem ContDiffAt.comp (x : E) (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffAt 𝕜 n f x) :
    ContDiffAt 𝕜 n (g ∘ f) x :=
  hg.comp x hf (mapsTo_univ _ _)

@[fun_prop]
/--
theorem `ContDiffAt.fun_comp` / 定理 `ContDiffAt.fun_comp`

English:
theorem ContDiffAt.fun_comp
  given: (x : E) (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffAt 𝕜 n f x)
  proof: hg.comp x hf

中文:
定理 ContDiffAt.fun_comp
  条件: (x : E) (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffAt 𝕜 n f x)
  证明: hg.comp x hf

Depends on / 依赖: hg.comp
-/
theorem ContDiffAt.fun_comp (x : E) (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffAt 𝕜 n f x) :
    ContDiffAt 𝕜 n (fun x => g (f x)) x := hg.comp x hf

/--
theorem `ContDiff.comp_contDiffWithinAt` / 定理 `ContDiff.comp_contDiffWithinAt`

English:
theorem ContDiff.comp_contDiffWithinAt
  statement: {g : F -> G} {f : E -> F} (h : ContDiff 𝕜 n g)
  proof: haveI : ContDiffWithinAt 𝕜 n g univ (f x) := h.contDiffAt.contDiffWithinAt
  this.comp x hf (subset_univ _)

中文:
定理 连续可微.comp_contDiffWithinAt
  结论: {g : F -> G} {f : E -> F} (h : 连续可微 𝕜 n g)
  证明: haveI : ContDiffWithinAt 𝕜 n g univ (f x) := h.contDiffAt.contDiffWithinAt
  this.comp x hf (subset_univ _)

Depends on / 依赖: ContDiffWithinAt, contDiffAt, contDiffWithinAt, h.contDiffAt.contDiffWithinAt, subset_univ, this.comp
-/
theorem ContDiff.comp_contDiffWithinAt {g : F -> G} {f : E -> F} (h : ContDiff 𝕜 n g)
    (hf : ContDiffWithinAt 𝕜 n f t x) : ContDiffWithinAt 𝕜 n (g ∘ f) t x :=
  haveI : ContDiffWithinAt 𝕜 n g univ (f x) := h.contDiffAt.contDiffWithinAt
  this.comp x hf (subset_univ _)

/--
theorem `ContDiff.comp_contDiffAt` / 定理 `ContDiff.comp_contDiffAt`

English:
theorem ContDiff.comp_contDiffAt
  statement: {g : F -> G} {f : E -> F} (x : E) (hg : ContDiff 𝕜 n g)
  proof: hg.comp_contDiffWithinAt hf

中文:
定理 连续可微.comp_contDiffAt
  结论: {g : F -> G} {f : E -> F} (x : E) (hg : 连续可微 𝕜 n g)
  证明: hg.comp_contDiffWithinAt hf

Depends on / 依赖: comp_contDiffWithinAt, hg.comp_contDiffWithinAt
-/
theorem ContDiff.comp_contDiffAt {g : F -> G} {f : E -> F} (x : E) (hg : ContDiff 𝕜 n g)
    (hf : ContDiffAt 𝕜 n f x) : ContDiffAt 𝕜 n (g ∘ f) x :=
  hg.comp_contDiffWithinAt hf

/--
theorem `iteratedFDerivWithin_comp_of_eventually_mem` / 定理 `iteratedFDerivWithin_comp_of_eventually_mem`

English:
theorem iteratedFDerivWithin_comp_of_eventually_mem
  statement: {t : Set F}
  proof: by
  obtain ⟨u, hxu, huo, hfu, hgu⟩ : exists u, x in u ∧ IsOpen u ∧
      HasFTaylorSeriesUpToOn i f (ftaylorSeriesWithin 𝕜 f s) (s inter u) ∧
      HasFTaylorSeriesUpToOn i g (ftaylorSeriesWithin 𝕜 g t) (f '' (s inter u)) := by
    have hxt : f x in t := hst.self_of_nhdsWithin hxs
    have hf_tendsto : Tendsto f (𝓝[s] x) (𝓝[t] (f x)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hf.continuousWithinAt, hst⟩
    have H₁ : forallᶠ u in (𝓝[s] x).smallSets,
        HasFTaylorSeriesUpToOn i f (ftaylorSeriesWithin 𝕜 f s) u :=
      hf.eventually_hasFTaylorSeriesUpToOn hs hxs hi
    have H₂ : forallᶠ u in (𝓝[s] x).smallSets,
        HasFTaylorSeriesUpToOn i g (ftaylorSeriesWithin 𝕜 g t) (f '' u) :=
      hf_tendsto.image_smallSets.eventually (hg.eventually_hasFTaylorSeriesUpToOn ht hxt hi)
    rcases (nhdsWithin_basis_open _ _).smallSets.eventually_iff.mp (H₁.and H₂)
      with ⟨u, ⟨hxu, huo⟩, hu⟩
    exact ⟨u, hxu, huo, hu (by simp [inter_comm])⟩
exact .symm (hgu.comp hfu (mapsTo_image _ _)).eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl
.trans iteratedFDerivWithin_inter_open huo hxu (hs.inter huo) ⟨hxs, hxu⟩

中文:
定理 iteratedFDerivWithin_comp_of_eventually_mem
  结论: {t : 集合 F}
  证明: by
  obtain ⟨u, hxu, huo, hfu, hgu⟩ : exists u, x in u ∧ IsOpen u ∧
      HasFTaylorSeriesUpToOn i f (ftaylorSeriesWithin 𝕜 f s) (s inter u) ∧
      HasFTaylorSeriesUpToOn i g (ftaylorSeriesWithin 𝕜 g t) (f '' (s inter u)) := by
    have hxt : f x in t := hst.self_of_nhdsWithin hxs
    have hf_tendsto : Tendsto f (𝓝[s] x) (𝓝[t] (f x)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hf.continuousWithinAt, hst⟩
    have H₁ : forallᶠ u in (𝓝[s] x).smallSets,
        HasFTaylorSeriesUpToOn i f (ftaylorSeriesWithin 𝕜 f s) u :=
      hf.eventually_hasFTaylorSeriesUpToOn hs hxs hi
    have H₂ : forallᶠ u in (𝓝[s] x).smallSets,
        HasFTaylorSeriesUpToOn i g (ftaylorSeriesWithin 𝕜 g t) (f '' u) :=
      hf_tendsto.image_smallSets.eventually (hg.eventually_hasFTaylorSeriesUpToOn ht hxt hi)
    rcases (nhdsWithin_basis_open _ _).smallSets.eventually_iff.mp (H₁.and H₂)
      with ⟨u, ⟨hxu, huo⟩, hu⟩
    exact ⟨u, hxu, huo, hu (by simp [inter_comm])⟩
exact .symm (hgu.comp hfu (mapsTo_image _ _)).eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl
.trans iteratedFDerivWithin_inter_open huo hxu (hs.inter huo) ⟨hxs, hxu⟩

Depends on / 依赖: HasFTaylorSeriesUpToOn, IsOpen, Tendsto, continuousWithinAt, eventually_hasFTaylo, ftaylorSeriesWithin, hf.continuousWithinAt, hf.eventually_hasFTaylo, hf_tendsto, hst.self_of_nhdsWithin, self_of_nhdsWithin, smallSets, tendsto_nhdsWithin_iff, tendsto_nhdsWithin_iff.mpr
-/
theorem iteratedFDerivWithin_comp_of_eventually_mem {t : Set F}
    (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContDiffWithinAt 𝕜 n f s x)
    (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜 s) (hxs : x in s) (hst : forallᶠ y in 𝓝[s] x, f y in t)
    {i : Nat} (hi : i <= n) :
    iteratedFDerivWithin 𝕜 i (g ∘ f) s x =
      (ftaylorSeriesWithin 𝕜 g t (f x)).taylorComp (ftaylorSeriesWithin 𝕜 f s x) i := by
  obtain ⟨u, hxu, huo, hfu, hgu⟩ : exists u, x in u ∧ IsOpen u ∧
      HasFTaylorSeriesUpToOn i f (ftaylorSeriesWithin 𝕜 f s) (s inter u) ∧
      HasFTaylorSeriesUpToOn i g (ftaylorSeriesWithin 𝕜 g t) (f '' (s inter u)) := by
    have hxt : f x in t := hst.self_of_nhdsWithin hxs
    have hf_tendsto : Tendsto f (𝓝[s] x) (𝓝[t] (f x)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hf.continuousWithinAt, hst⟩
    have H₁ : forallᶠ u in (𝓝[s] x).smallSets,
        HasFTaylorSeriesUpToOn i f (ftaylorSeriesWithin 𝕜 f s) u :=
      hf.eventually_hasFTaylorSeriesUpToOn hs hxs hi
    have H₂ : forallᶠ u in (𝓝[s] x).smallSets,
        HasFTaylorSeriesUpToOn i g (ftaylorSeriesWithin 𝕜 g t) (f '' u) :=
      hf_tendsto.image_smallSets.eventually (hg.eventually_hasFTaylorSeriesUpToOn ht hxt hi)
    rcases (nhdsWithin_basis_open _ _).smallSets.eventually_iff.mp (H₁.and H₂)
      with ⟨u, ⟨hxu, huo⟩, hu⟩
    exact ⟨u, hxu, huo, hu (by simp [inter_comm])⟩
exact .symm (hgu.comp hfu (mapsTo_image _ _)).eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl
.trans iteratedFDerivWithin_inter_open huo hxu (hs.inter huo) ⟨hxs, hxu⟩

/--
theorem `iteratedFDerivWithin_comp` / 定理 `iteratedFDerivWithin_comp`

English:
theorem iteratedFDerivWithin_comp
  statement: {t : Set F} (hg : ContDiffWithinAt 𝕜 n g t (f x))
  proof: iteratedFDerivWithin_comp_of_eventually_mem hg hf ht hs hx (eventually_mem_nhdsWithin.mono hst) hi

中文:
定理 iteratedFDerivWithin_comp
  结论: {t : 集合 F} (hg : ContDiffWithinAt 𝕜 n g t (f x))
  证明: iteratedFDerivWithin_comp_of_eventually_mem hg hf ht hs hx (eventually_mem_nhdsWithin.mono hst) hi

Depends on / 依赖: eventually_mem_nhdsWithin, eventually_mem_nhdsWithin.mono, iteratedFDerivWithin_comp_of_eventually_mem
-/
theorem iteratedFDerivWithin_comp {t : Set F} (hg : ContDiffWithinAt 𝕜 n g t (f x))
    (hf : ContDiffWithinAt 𝕜 n f s x) (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜 s)
    (hx : x in s) (hst : MapsTo f s t) {i : Nat} (hi : i <= n) :
    iteratedFDerivWithin 𝕜 i (g ∘ f) s x =
      (ftaylorSeriesWithin 𝕜 g t (f x)).taylorComp (ftaylorSeriesWithin 𝕜 f s x) i :=
  iteratedFDerivWithin_comp_of_eventually_mem hg hf ht hs hx (eventually_mem_nhdsWithin.mono hst) hi

/--
theorem `iteratedFDeriv_comp` / 定理 `iteratedFDeriv_comp`

English:
theorem iteratedFDeriv_comp
  statement: (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffAt 𝕜 n f x)
  proof: by
  simp only [← iteratedFDerivWithin_univ, ← ftaylorSeriesWithin_univ]
  exact iteratedFDerivWithin_comp hg.contDiffWithinAt hf.contDiffWithinAt
    uniqueDiffOn_univ uniqueDiffOn_univ (mem_univ _) (mapsTo_univ _ _) hi

中文:
定理 iteratedFDeriv_comp
  结论: (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffAt 𝕜 n f x)
  证明: by
  simp only [← iteratedFDerivWithin_univ, ← ftaylorSeriesWithin_univ]
  exact iteratedFDerivWithin_comp hg.contDiffWithinAt hf.contDiffWithinAt
    uniqueDiffOn_univ uniqueDiffOn_univ (mem_univ _) (mapsTo_univ _ _) hi

Depends on / 依赖: contDiffWithinAt, ftaylorSeriesWithin_univ, hf.contDiffWithinAt, hg.contDiffWithinAt, iteratedFDerivWithin_comp, iteratedFDerivWithin_univ, mapsTo_univ, mem_univ, uniqueDiffOn_univ
-/
theorem iteratedFDeriv_comp (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffAt 𝕜 n f x)
    {i : Nat} (hi : i <= n) :
    iteratedFDeriv 𝕜 i (g ∘ f) x =
      (ftaylorSeries 𝕜 g (f x)).taylorComp (ftaylorSeries 𝕜 f x) i := by
  simp only [← iteratedFDerivWithin_univ, ← ftaylorSeriesWithin_univ]
  exact iteratedFDerivWithin_comp hg.contDiffWithinAt hf.contDiffWithinAt
    uniqueDiffOn_univ uniqueDiffOn_univ (mem_univ _) (mapsTo_univ _ _) hi

end comp

/-!
### Smoothness of projections
-/

/-- The first projection in a product is `C^∞`. -/
@[fun_prop]
/--
theorem `contDiff_fst` / 定理 `contDiff_fst`

English:
theorem contDiff_fst
  statement: ContDiff 𝕜 n (Prod.fst : E × F -> E)
  proof: IsBoundedLinearMap.contDiff IsBoundedLinearMap.fst

中文:
定理 contDiff_fst
  结论: 连续可微 𝕜 n (积类型.fst : E × F -> E)
  证明: IsBoundedLinearMap.contDiff IsBoundedLinearMap.fst

Depends on / 依赖: IsBoundedLinearMap, IsBoundedLinearMap.contDiff, IsBoundedLinearMap.fst, contDiff
-/
theorem contDiff_fst : ContDiff 𝕜 n (Prod.fst : E × F -> E) :=
  IsBoundedLinearMap.contDiff IsBoundedLinearMap.fst

/-- Postcomposing `f` with `Prod.fst` is `C^n` -/
@[fun_prop]
/--
theorem `ContDiff.fst` / 定理 `ContDiff.fst`

English:
theorem ContDiff.fst
  given: {f : E -> F × G} (hf : ContDiff 𝕜 n f)
  statement: ContDiff 𝕜 n fun x => (f x).1
  proof: contDiff_fst.comp hf

中文:
定理 连续可微.fst
  条件: {f : E -> F × G} (hf : 连续可微 𝕜 n f)
  结论: 连续可微 𝕜 n fun x => (f x).1
  证明: contDiff_fst.comp hf

Depends on / 依赖: contDiff_fst, contDiff_fst.comp
-/
theorem ContDiff.fst {f : E -> F × G} (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun x => (f x).1 :=
  contDiff_fst.comp hf

/--
theorem `ContDiff.fst'` / 定理 `ContDiff.fst'`

English:
theorem ContDiff.fst'
  given: {f : E -> G} (hf : ContDiff 𝕜 n f)
  statement: ContDiff 𝕜 n fun x : E × F => f x.1
  proof: hf.comp contDiff_fst

中文:
定理 连续可微.fst'
  条件: {f : E -> G} (hf : 连续可微 𝕜 n f)
  结论: 连续可微 𝕜 n fun x : E × F => f x.1
  证明: hf.comp contDiff_fst

Depends on / 依赖: contDiff_fst, hf.comp
-/
theorem ContDiff.fst' {f : E -> G} (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun x : E × F => f x.1 :=
  hf.comp contDiff_fst

/-- The first projection on a domain in a product is `C^∞`. -/
@[fun_prop]
/--
theorem `contDiffOn_fst` / 定理 `contDiffOn_fst`

English:
theorem contDiffOn_fst
  given: {s : Set (E × F)}
  statement: ContDiffOn 𝕜 n (Prod.fst : E × F -> E) s
  proof: ContDiff.contDiffOn contDiff_fst

@[fun_prop]

中文:
定理 contDiffOn_fst
  条件: {s : 集合 (E × F)}
  结论: ContDiffOn 𝕜 n (积类型.fst : E × F -> E) s
  证明: ContDiff.contDiffOn contDiff_fst

@[fun_prop]

Depends on / 依赖: ContDiff, ContDiff.contDiffOn, contDiffOn, contDiff_fst
-/
theorem contDiffOn_fst {s : Set (E × F)} : ContDiffOn 𝕜 n (Prod.fst : E × F -> E) s :=
  ContDiff.contDiffOn contDiff_fst

@[fun_prop]
/--
theorem `ContDiffOn.fst` / 定理 `ContDiffOn.fst`

English:
theorem ContDiffOn.fst
  given: {f : E -> F × G} {s : Set E} (hf : ContDiffOn 𝕜 n f s)
  proof: contDiff_fst.comp_contDiffOn hf

中文:
定理 ContDiffOn.fst
  条件: {f : E -> F × G} {s : 集合 E} (hf : ContDiffOn 𝕜 n f s)
  证明: contDiff_fst.comp_contDiffOn hf

Depends on / 依赖: comp_contDiffOn, contDiff_fst, contDiff_fst.comp_contDiffOn
-/
theorem ContDiffOn.fst {f : E -> F × G} {s : Set E} (hf : ContDiffOn 𝕜 n f s) :
    ContDiffOn 𝕜 n (fun x => (f x).1) s :=
  contDiff_fst.comp_contDiffOn hf

/-- The first projection at a point in a product is `C^∞`. -/
@[fun_prop]
/--
theorem `contDiffAt_fst` / 定理 `contDiffAt_fst`

English:
theorem contDiffAt_fst
  given: {p : E × F}
  statement: ContDiffAt 𝕜 n (Prod.fst : E × F -> E) p
  proof: contDiff_fst.contDiffAt

中文:
定理 contDiffAt_fst
  条件: {p : E × F}
  结论: ContDiffAt 𝕜 n (积类型.fst : E × F -> E) p
  证明: contDiff_fst.contDiffAt

Depends on / 依赖: contDiffAt, contDiff_fst, contDiff_fst.contDiffAt
-/
theorem contDiffAt_fst {p : E × F} : ContDiffAt 𝕜 n (Prod.fst : E × F -> E) p :=
  contDiff_fst.contDiffAt

/-- Postcomposing `f` with `Prod.fst` is `C^n` at `(x, y)` -/
@[fun_prop]
/--
theorem `ContDiffAt.fst` / 定理 `ContDiffAt.fst`

English:
theorem ContDiffAt.fst
  given: {f : E -> F × G} {x : E} (hf : ContDiffAt 𝕜 n f x)
  proof: contDiffAt_fst.comp x hf

中文:
定理 ContDiffAt.fst
  条件: {f : E -> F × G} {x : E} (hf : ContDiffAt 𝕜 n f x)
  证明: contDiffAt_fst.comp x hf

Depends on / 依赖: contDiffAt_fst, contDiffAt_fst.comp
-/
theorem ContDiffAt.fst {f : E -> F × G} {x : E} (hf : ContDiffAt 𝕜 n f x) :
    ContDiffAt 𝕜 n (fun x => (f x).1) x :=
  contDiffAt_fst.comp x hf

/--
theorem `ContDiffAt.fst'` / 定理 `ContDiffAt.fst'`

English:
theorem ContDiffAt.fst'
  given: {f : E -> G} {x : E} {y : F} (hf : ContDiffAt 𝕜 n f x)
  proof: ContDiffAt.comp (x, y) hf contDiffAt_fst

中文:
定理 ContDiffAt.fst'
  条件: {f : E -> G} {x : E} {y : F} (hf : ContDiffAt 𝕜 n f x)
  证明: ContDiffAt.comp (x, y) hf contDiffAt_fst

Depends on / 依赖: ContDiffAt, ContDiffAt.comp, contDiffAt_fst
-/
theorem ContDiffAt.fst' {f : E -> G} {x : E} {y : F} (hf : ContDiffAt 𝕜 n f x) :
    ContDiffAt 𝕜 n (fun x : E × F => f x.1) (x, y) :=
  ContDiffAt.comp (x, y) hf contDiffAt_fst

/--
theorem `ContDiffAt.fst''` / 定理 `ContDiffAt.fst''`

English:
theorem ContDiffAt.fst''
  given: {f : E -> G} {x : E × F} (hf : ContDiffAt 𝕜 n f x.1)
  proof: hf.comp x contDiffAt_fst

中文:
定理 ContDiffAt.fst''
  条件: {f : E -> G} {x : E × F} (hf : ContDiffAt 𝕜 n f x.1)
  证明: hf.comp x contDiffAt_fst

Depends on / 依赖: contDiffAt_fst, hf.comp
-/
theorem ContDiffAt.fst'' {f : E -> G} {x : E × F} (hf : ContDiffAt 𝕜 n f x.1) :
    ContDiffAt 𝕜 n (fun x : E × F => f x.1) x :=
  hf.comp x contDiffAt_fst

/-- The first projection within a domain at a point in a product is `C^∞`. -/
@[fun_prop]
/--
theorem `contDiffWithinAt_fst` / 定理 `contDiffWithinAt_fst`

English:
theorem contDiffWithinAt_fst
  given: {s : Set (E × F)} {p : E × F}
  proof: contDiff_fst.contDiffWithinAt

中文:
定理 contDiffWithinAt_fst
  条件: {s : 集合 (E × F)} {p : E × F}
  证明: contDiff_fst.contDiffWithinAt

Depends on / 依赖: contDiffWithinAt, contDiff_fst, contDiff_fst.contDiffWithinAt
-/
theorem contDiffWithinAt_fst {s : Set (E × F)} {p : E × F} :
    ContDiffWithinAt 𝕜 n (Prod.fst : E × F -> E) s p :=
  contDiff_fst.contDiffWithinAt

/-- Postcomposing `f` with `Prod.fst` is `C^n` at `x` -/
@[fun_prop]
/--
theorem `ContDiffWithinAt.fst` / 定理 `ContDiffWithinAt.fst`

English:
theorem ContDiffWithinAt.fst
  given: {f : E -> F × G} {x : E} (hf : ContDiffWithinAt 𝕜 n f s x)
  proof: contDiffWithinAt_fst.comp x hf (mapsTo_image f s)

中文:
定理 ContDiffWithinAt.fst
  条件: {f : E -> F × G} {x : E} (hf : ContDiffWithinAt 𝕜 n f s x)
  证明: contDiffWithinAt_fst.comp x hf (mapsTo_image f s)

Depends on / 依赖: contDiffWithinAt_fst, contDiffWithinAt_fst.comp, mapsTo_image
-/
theorem ContDiffWithinAt.fst {f : E -> F × G} {x : E} (hf : ContDiffWithinAt 𝕜 n f s x) :
    ContDiffWithinAt 𝕜 n (fun x => (f x).1) s x :=
  contDiffWithinAt_fst.comp x hf (mapsTo_image f s)

/-- The second projection in a product is `C^∞`. -/
@[fun_prop]
/--
theorem `contDiff_snd` / 定理 `contDiff_snd`

English:
theorem contDiff_snd
  statement: ContDiff 𝕜 n (Prod.snd : E × F -> F)
  proof: IsBoundedLinearMap.contDiff IsBoundedLinearMap.snd

中文:
定理 contDiff_snd
  结论: 连续可微 𝕜 n (积类型.snd : E × F -> F)
  证明: IsBoundedLinearMap.contDiff IsBoundedLinearMap.snd

Depends on / 依赖: IsBoundedLinearMap, IsBoundedLinearMap.contDiff, IsBoundedLinearMap.snd, contDiff
-/
theorem contDiff_snd : ContDiff 𝕜 n (Prod.snd : E × F -> F) :=
  IsBoundedLinearMap.contDiff IsBoundedLinearMap.snd

/-- Postcomposing `f` with `Prod.snd` is `C^n` -/
@[fun_prop]
/--
theorem `ContDiff.snd` / 定理 `ContDiff.snd`

English:
theorem ContDiff.snd
  given: {f : E -> F × G} (hf : ContDiff 𝕜 n f)
  statement: ContDiff 𝕜 n fun x => (f x).2
  proof: contDiff_snd.comp hf

中文:
定理 连续可微.snd
  条件: {f : E -> F × G} (hf : 连续可微 𝕜 n f)
  结论: 连续可微 𝕜 n fun x => (f x).2
  证明: contDiff_snd.comp hf

Depends on / 依赖: contDiff_snd, contDiff_snd.comp
-/
theorem ContDiff.snd {f : E -> F × G} (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun x => (f x).2 :=
  contDiff_snd.comp hf

/--
theorem `ContDiff.snd'` / 定理 `ContDiff.snd'`

English:
theorem ContDiff.snd'
  given: {f : F -> G} (hf : ContDiff 𝕜 n f)
  statement: ContDiff 𝕜 n fun x : E × F => f x.2
  proof: hf.comp contDiff_snd

中文:
定理 连续可微.snd'
  条件: {f : F -> G} (hf : 连续可微 𝕜 n f)
  结论: 连续可微 𝕜 n fun x : E × F => f x.2
  证明: hf.comp contDiff_snd

Depends on / 依赖: contDiff_snd, hf.comp
-/
theorem ContDiff.snd' {f : F -> G} (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun x : E × F => f x.2 :=
  hf.comp contDiff_snd

/-- The second projection on a domain in a product is `C^∞`. -/
@[fun_prop]
/--
theorem `contDiffOn_snd` / 定理 `contDiffOn_snd`

English:
theorem contDiffOn_snd
  given: {s : Set (E × F)}
  statement: ContDiffOn 𝕜 n (Prod.snd : E × F -> F) s
  proof: ContDiff.contDiffOn contDiff_snd

@[fun_prop]

中文:
定理 contDiffOn_snd
  条件: {s : 集合 (E × F)}
  结论: ContDiffOn 𝕜 n (积类型.snd : E × F -> F) s
  证明: ContDiff.contDiffOn contDiff_snd

@[fun_prop]

Depends on / 依赖: ContDiff, ContDiff.contDiffOn, contDiffOn, contDiff_snd
-/
theorem contDiffOn_snd {s : Set (E × F)} : ContDiffOn 𝕜 n (Prod.snd : E × F -> F) s :=
  ContDiff.contDiffOn contDiff_snd

@[fun_prop]
/--
theorem `ContDiffOn.snd` / 定理 `ContDiffOn.snd`

English:
theorem ContDiffOn.snd
  given: {f : E -> F × G} {s : Set E} (hf : ContDiffOn 𝕜 n f s)
  proof: contDiff_snd.comp_contDiffOn hf

中文:
定理 ContDiffOn.snd
  条件: {f : E -> F × G} {s : 集合 E} (hf : ContDiffOn 𝕜 n f s)
  证明: contDiff_snd.comp_contDiffOn hf

Depends on / 依赖: comp_contDiffOn, contDiff_snd, contDiff_snd.comp_contDiffOn
-/
theorem ContDiffOn.snd {f : E -> F × G} {s : Set E} (hf : ContDiffOn 𝕜 n f s) :
    ContDiffOn 𝕜 n (fun x => (f x).2) s :=
  contDiff_snd.comp_contDiffOn hf

/-- The second projection within a domain at a point in a product is `C^∞`. -/
@[fun_prop]
/--
theorem `contDiffWithinAt_snd` / 定理 `contDiffWithinAt_snd`

English:
theorem contDiffWithinAt_snd
  given: {s : Set (E × F)} {p : E × F}
  proof: contDiff_snd.contDiffWithinAt

中文:
定理 contDiffWithinAt_snd
  条件: {s : 集合 (E × F)} {p : E × F}
  证明: contDiff_snd.contDiffWithinAt

Depends on / 依赖: contDiffWithinAt, contDiff_snd, contDiff_snd.contDiffWithinAt
-/
theorem contDiffWithinAt_snd {s : Set (E × F)} {p : E × F} :
    ContDiffWithinAt 𝕜 n (Prod.snd : E × F -> F) s p :=
  contDiff_snd.contDiffWithinAt

/-- The second projection at a point in a product is `C^∞`. -/
@[fun_prop]
/--
theorem `contDiffAt_snd` / 定理 `contDiffAt_snd`

English:
theorem contDiffAt_snd
  given: {p : E × F}
  statement: ContDiffAt 𝕜 n (Prod.snd : E × F -> F) p
  proof: contDiff_snd.contDiffAt

中文:
定理 contDiffAt_snd
  条件: {p : E × F}
  结论: ContDiffAt 𝕜 n (积类型.snd : E × F -> F) p
  证明: contDiff_snd.contDiffAt

Depends on / 依赖: contDiffAt, contDiff_snd, contDiff_snd.contDiffAt
-/
theorem contDiffAt_snd {p : E × F} : ContDiffAt 𝕜 n (Prod.snd : E × F -> F) p :=
  contDiff_snd.contDiffAt

/-- Postcomposing `f` with `Prod.snd` is `C^n` at `x` -/
@[fun_prop]
/--
theorem `ContDiffWithinAt.snd` / 定理 `ContDiffWithinAt.snd`

English:
theorem ContDiffWithinAt.snd
  given: {f : E -> F × G} {x : E} (hf : ContDiffWithinAt 𝕜 n f s x)
  proof: contDiffWithinAt_snd.comp x hf (mapsTo_image f s)

中文:
定理 ContDiffWithinAt.snd
  条件: {f : E -> F × G} {x : E} (hf : ContDiffWithinAt 𝕜 n f s x)
  证明: contDiffWithinAt_snd.comp x hf (mapsTo_image f s)

Depends on / 依赖: contDiffWithinAt_snd, contDiffWithinAt_snd.comp, mapsTo_image
-/
theorem ContDiffWithinAt.snd {f : E -> F × G} {x : E} (hf : ContDiffWithinAt 𝕜 n f s x) :
    ContDiffWithinAt 𝕜 n (fun x => (f x).2) s x :=
  contDiffWithinAt_snd.comp x hf (mapsTo_image f s)

/-- Postcomposing `f` with `Prod.snd` is `C^n` at `x` -/
@[fun_prop]
/--
theorem `ContDiffAt.snd` / 定理 `ContDiffAt.snd`

English:
theorem ContDiffAt.snd
  given: {f : E -> F × G} {x : E} (hf : ContDiffAt 𝕜 n f x)
  proof: contDiffAt_snd.comp x hf

中文:
定理 ContDiffAt.snd
  条件: {f : E -> F × G} {x : E} (hf : ContDiffAt 𝕜 n f x)
  证明: contDiffAt_snd.comp x hf

Depends on / 依赖: contDiffAt_snd, contDiffAt_snd.comp
-/
theorem ContDiffAt.snd {f : E -> F × G} {x : E} (hf : ContDiffAt 𝕜 n f x) :
    ContDiffAt 𝕜 n (fun x => (f x).2) x :=
  contDiffAt_snd.comp x hf

/--
theorem `ContDiffAt.snd'` / 定理 `ContDiffAt.snd'`

English:
theorem ContDiffAt.snd'
  given: {f : F -> G} {x : E} {y : F} (hf : ContDiffAt 𝕜 n f y)
  proof: ContDiffAt.comp (x, y) hf contDiffAt_snd

中文:
定理 ContDiffAt.snd'
  条件: {f : F -> G} {x : E} {y : F} (hf : ContDiffAt 𝕜 n f y)
  证明: ContDiffAt.comp (x, y) hf contDiffAt_snd

Depends on / 依赖: ContDiffAt, ContDiffAt.comp, contDiffAt_snd
-/
theorem ContDiffAt.snd' {f : F -> G} {x : E} {y : F} (hf : ContDiffAt 𝕜 n f y) :
    ContDiffAt 𝕜 n (fun x : E × F => f x.2) (x, y) :=
  ContDiffAt.comp (x, y) hf contDiffAt_snd

/--
theorem `ContDiffAt.snd''` / 定理 `ContDiffAt.snd''`

English:
theorem ContDiffAt.snd''
  given: {f : F -> G} {x : E × F} (hf : ContDiffAt 𝕜 n f x.2)
  proof: hf.comp x contDiffAt_snd

中文:
定理 ContDiffAt.snd''
  条件: {f : F -> G} {x : E × F} (hf : ContDiffAt 𝕜 n f x.2)
  证明: hf.comp x contDiffAt_snd

Depends on / 依赖: contDiffAt_snd, hf.comp
-/
theorem ContDiffAt.snd'' {f : F -> G} {x : E × F} (hf : ContDiffAt 𝕜 n f x.2) :
    ContDiffAt 𝕜 n (fun x : E × F => f x.2) x :=
  hf.comp x contDiffAt_snd

/--
theorem `contDiffWithinAt_prod_iff` / 定理 `contDiffWithinAt_prod_iff`

English:
theorem contDiffWithinAt_prod_iff
  given: (f : E -> F × G)
  proof: ⟨fun h => ⟨h.fst, h.snd⟩, fun h => h.1.prodMk h.2⟩

中文:
定理 contDiffWithinAt_prod_iff
  条件: (f : E -> F × G)
  证明: ⟨fun h => ⟨h.fst, h.snd⟩, fun h => h.1.prodMk h.2⟩

Depends on / 依赖: h.fst, h.snd, prodMk
-/
theorem contDiffWithinAt_prod_iff (f : E -> F × G) :
    ContDiffWithinAt 𝕜 n f s x ↔
      ContDiffWithinAt 𝕜 n (Prod.fst ∘ f) s x ∧ ContDiffWithinAt 𝕜 n (Prod.snd ∘ f) s x :=
  ⟨fun h => ⟨h.fst, h.snd⟩, fun h => h.1.prodMk h.2⟩

/--
theorem `contDiffAt_prod_iff` / 定理 `contDiffAt_prod_iff`

English:
theorem contDiffAt_prod_iff
  given: (f : E -> F × G)
  proof: ⟨fun h => ⟨h.fst, h.snd⟩, fun h => h.1.prodMk h.2⟩

中文:
定理 contDiffAt_prod_iff
  条件: (f : E -> F × G)
  证明: ⟨fun h => ⟨h.fst, h.snd⟩, fun h => h.1.prodMk h.2⟩

Depends on / 依赖: h.fst, h.snd, prodMk
-/
theorem contDiffAt_prod_iff (f : E -> F × G) :
    ContDiffAt 𝕜 n f x ↔
      ContDiffAt 𝕜 n (Prod.fst ∘ f) x ∧ ContDiffAt 𝕜 n (Prod.snd ∘ f) x :=
  ⟨fun h => ⟨h.fst, h.snd⟩, fun h => h.1.prodMk h.2⟩

/--
theorem `contDiffOn_prod_iff` / 定理 `contDiffOn_prod_iff`

English:
theorem contDiffOn_prod_iff
  given: (f : E -> F × G)
  proof: ⟨fun h => ⟨h.fst, h.snd⟩, fun h => h.1.prodMk h.2⟩

中文:
定理 contDiffOn_prod_iff
  条件: (f : E -> F × G)
  证明: ⟨fun h => ⟨h.fst, h.snd⟩, fun h => h.1.prodMk h.2⟩

Depends on / 依赖: h.fst, h.snd, prodMk
-/
theorem contDiffOn_prod_iff (f : E -> F × G) :
    ContDiffOn 𝕜 n f s ↔
      ContDiffOn 𝕜 n (Prod.fst ∘ f) s ∧ ContDiffOn 𝕜 n (Prod.snd ∘ f) s :=
  ⟨fun h => ⟨h.fst, h.snd⟩, fun h => h.1.prodMk h.2⟩

/--
theorem `contDiff_prod_iff` / 定理 `contDiff_prod_iff`

English:
theorem contDiff_prod_iff
  given: (f : E -> F × G)
  proof: ⟨fun h => ⟨h.fst, h.snd⟩, fun h => h.1.prodMk h.2⟩

中文:
定理 contDiff_prod_iff
  条件: (f : E -> F × G)
  证明: ⟨fun h => ⟨h.fst, h.snd⟩, fun h => h.1.prodMk h.2⟩

Depends on / 依赖: h.fst, h.snd, prodMk
-/
theorem contDiff_prod_iff (f : E -> F × G) :
    ContDiff 𝕜 n f ↔
      ContDiff 𝕜 n (Prod.fst ∘ f) ∧ ContDiff 𝕜 n (Prod.snd ∘ f) :=
  ⟨fun h => ⟨h.fst, h.snd⟩, fun h => h.1.prodMk h.2⟩

section NAry

variable {E₁ E₂ E₃ : Type*}
variable [NormedAddCommGroup E₁] [NormedAddCommGroup E₂] [NormedAddCommGroup E₃]
  [NormedSpace 𝕜 E₁] [NormedSpace 𝕜 E₂] [NormedSpace 𝕜 E₃]

/--
theorem `ContDiff.comp₂` / 定理 `ContDiff.comp₂`

English:
theorem ContDiff.comp₂
  statement: {g : E₁ × E₂ -> G} {f₁ : F -> E₁} {f₂ : F -> E₂} (hg : ContDiff 𝕜 n g)
  proof: hg.comp hf₁.prodMk hf₂

中文:
定理 连续可微.comp₂
  结论: {g : E₁ × E₂ -> G} {f₁ : F -> E₁} {f₂ : F -> E₂} (hg : 连续可微 𝕜 n g)
  证明: hg.comp hf₁.prodMk hf₂

Depends on / 依赖: hg.comp, prodMk
-/
theorem ContDiff.comp₂ {g : E₁ × E₂ -> G} {f₁ : F -> E₁} {f₂ : F -> E₂} (hg : ContDiff 𝕜 n g)
    (hf₁ : ContDiff 𝕜 n f₁) (hf₂ : ContDiff 𝕜 n f₂) : ContDiff 𝕜 n fun x => g (f₁ x, f₂ x) :=
hg.comp hf₁.prodMk hf₂

/--
theorem `ContDiffAt.comp₂` / 定理 `ContDiffAt.comp₂`

English:
theorem ContDiffAt.comp₂
  statement: {g : E₁ × E₂ -> G} {f₁ : F -> E₁} {f₂ : F -> E₂} {x : F}
  proof: hg.comp x (hf₁.prodMk hf₂)

中文:
定理 ContDiffAt.comp₂
  结论: {g : E₁ × E₂ -> G} {f₁ : F -> E₁} {f₂ : F -> E₂} {x : F}
  证明: hg.comp x (hf₁.prodMk hf₂)

Depends on / 依赖: hg.comp, prodMk
-/
theorem ContDiffAt.comp₂ {g : E₁ × E₂ -> G} {f₁ : F -> E₁} {f₂ : F -> E₂} {x : F}
    (hg : ContDiffAt 𝕜 n g (f₁ x, f₂ x))
    (hf₁ : ContDiffAt 𝕜 n f₁ x) (hf₂ : ContDiffAt 𝕜 n f₂ x) :
    ContDiffAt 𝕜 n (fun x => g (f₁ x, f₂ x)) x :=
  hg.comp x (hf₁.prodMk hf₂)

/--
theorem `ContDiffAt.comp₂_contDiffWithinAt` / 定理 `ContDiffAt.comp₂_contDiffWithinAt`

English:
theorem ContDiffAt.comp₂_contDiffWithinAt
  statement: {g : E₁ × E₂ -> G} {f₁ : F -> E₁} {f₂ : F -> E₂}
  proof: hg.comp_contDiffWithinAt x (hf₁.prodMk hf₂)

中文:
定理 ContDiffAt.comp₂_contDiffWithinAt
  结论: {g : E₁ × E₂ -> G} {f₁ : F -> E₁} {f₂ : F -> E₂}
  证明: hg.comp_contDiffWithinAt x (hf₁.prodMk hf₂)

Depends on / 依赖: comp_contDiffWithinAt, hg.comp_contDiffWithinAt, prodMk
-/
theorem ContDiffAt.comp₂_contDiffWithinAt {g : E₁ × E₂ -> G} {f₁ : F -> E₁} {f₂ : F -> E₂}
    {s : Set F} {x : F} (hg : ContDiffAt 𝕜 n g (f₁ x, f₂ x))
    (hf₁ : ContDiffWithinAt 𝕜 n f₁ s x) (hf₂ : ContDiffWithinAt 𝕜 n f₂ s x) :
    ContDiffWithinAt 𝕜 n (fun x => g (f₁ x, f₂ x)) s x :=
  hg.comp_contDiffWithinAt x (hf₁.prodMk hf₂)

/--
theorem `ContDiff.comp₂_contDiffAt` / 定理 `ContDiff.comp₂_contDiffAt`

English:
theorem ContDiff.comp₂_contDiffAt
  statement: {g : E₁ × E₂ -> G} {f₁ : F -> E₁} {f₂ : F -> E₂} {x : F}
  proof: hg.contDiffAt.comp₂ hf₁ hf₂

中文:
定理 连续可微.comp₂_contDiffAt
  结论: {g : E₁ × E₂ -> G} {f₁ : F -> E₁} {f₂ : F -> E₂} {x : F}
  证明: hg.contDiffAt.comp₂ hf₁ hf₂

Depends on / 依赖: contDiffAt, hg.contDiffAt.comp
-/
theorem ContDiff.comp₂_contDiffAt {g : E₁ × E₂ -> G} {f₁ : F -> E₁} {f₂ : F -> E₂} {x : F}
    (hg : ContDiff 𝕜 n g) (hf₁ : ContDiffAt 𝕜 n f₁ x) (hf₂ : ContDiffAt 𝕜 n f₂ x) :
    ContDiffAt 𝕜 n (fun x => g (f₁ x, f₂ x)) x :=
  hg.contDiffAt.comp₂ hf₁ hf₂

/--
theorem `ContDiff.comp₂_contDiffWithinAt` / 定理 `ContDiff.comp₂_contDiffWithinAt`

English:
theorem ContDiff.comp₂_contDiffWithinAt
  statement: {g : E₁ × E₂ -> G} {f₁ : F -> E₁} {f₂ : F -> E₂}
  proof: hg.contDiffAt.comp_contDiffWithinAt x (hf₁.prodMk hf₂)

中文:
定理 连续可微.comp₂_contDiffWithinAt
  结论: {g : E₁ × E₂ -> G} {f₁ : F -> E₁} {f₂ : F -> E₂}
  证明: hg.contDiffAt.comp_contDiffWithinAt x (hf₁.prodMk hf₂)

Depends on / 依赖: comp_contDiffWithinAt, contDiffAt, hg.contDiffAt.comp_contDiffWithinAt, prodMk
-/
theorem ContDiff.comp₂_contDiffWithinAt {g : E₁ × E₂ -> G} {f₁ : F -> E₁} {f₂ : F -> E₂}
    {s : Set F} {x : F} (hg : ContDiff 𝕜 n g)
    (hf₁ : ContDiffWithinAt 𝕜 n f₁ s x) (hf₂ : ContDiffWithinAt 𝕜 n f₂ s x) :
    ContDiffWithinAt 𝕜 n (fun x => g (f₁ x, f₂ x)) s x :=
  hg.contDiffAt.comp_contDiffWithinAt x (hf₁.prodMk hf₂)

/--
theorem `ContDiff.comp₂_contDiffOn` / 定理 `ContDiff.comp₂_contDiffOn`

English:
theorem ContDiff.comp₂_contDiffOn
  statement: {g : E₁ × E₂ -> G} {f₁ : F -> E₁} {f₂ : F -> E₂} {s : Set F}
  proof: hg.comp_contDiffOn hf₁.prodMk hf₂

中文:
定理 连续可微.comp₂_contDiffOn
  结论: {g : E₁ × E₂ -> G} {f₁ : F -> E₁} {f₂ : F -> E₂} {s : 集合 F}
  证明: hg.comp_contDiffOn hf₁.prodMk hf₂

Depends on / 依赖: comp_contDiffOn, hg.comp_contDiffOn, prodMk
-/
theorem ContDiff.comp₂_contDiffOn {g : E₁ × E₂ -> G} {f₁ : F -> E₁} {f₂ : F -> E₂} {s : Set F}
    (hg : ContDiff 𝕜 n g) (hf₁ : ContDiffOn 𝕜 n f₁ s) (hf₂ : ContDiffOn 𝕜 n f₂ s) :
    ContDiffOn 𝕜 n (fun x => g (f₁ x, f₂ x)) s :=
hg.comp_contDiffOn hf₁.prodMk hf₂

/--
theorem `ContDiff.comp₃` / 定理 `ContDiff.comp₃`

English:
theorem ContDiff.comp₃
  statement: {g : E₁ × E₂ × E₃ -> G} {f₁ : F -> E₁} {f₂ : F -> E₂} {f₃ : F -> E₃}
  proof: hg.comp₂ hf₁ hf₂.prodMk hf₃

中文:
定理 连续可微.comp₃
  结论: {g : E₁ × E₂ × E₃ -> G} {f₁ : F -> E₁} {f₂ : F -> E₂} {f₃ : F -> E₃}
  证明: hg.comp₂ hf₁ hf₂.prodMk hf₃

Depends on / 依赖: hg.comp, prodMk
-/
theorem ContDiff.comp₃ {g : E₁ × E₂ × E₃ -> G} {f₁ : F -> E₁} {f₂ : F -> E₂} {f₃ : F -> E₃}
    (hg : ContDiff 𝕜 n g) (hf₁ : ContDiff 𝕜 n f₁) (hf₂ : ContDiff 𝕜 n f₂) (hf₃ : ContDiff 𝕜 n f₃) :
    ContDiff 𝕜 n fun x => g (f₁ x, f₂ x, f₃ x) :=
hg.comp₂ hf₁ hf₂.prodMk hf₃

/--
theorem `ContDiff.comp₃_contDiffOn` / 定理 `ContDiff.comp₃_contDiffOn`

English:
theorem ContDiff.comp₃_contDiffOn
  statement: {g : E₁ × E₂ × E₃ -> G} {f₁ : F -> E₁} {f₂ : F -> E₂} {f₃ : F -> E₃}
  proof: hg.comp₂_contDiffOn hf₁ hf₂.prodMk hf₃

中文:
定理 连续可微.comp₃_contDiffOn
  结论: {g : E₁ × E₂ × E₃ -> G} {f₁ : F -> E₁} {f₂ : F -> E₂} {f₃ : F -> E₃}
  证明: hg.comp₂_contDiffOn hf₁ hf₂.prodMk hf₃

Depends on / 依赖: hg.comp, prodMk
-/
theorem ContDiff.comp₃_contDiffOn {g : E₁ × E₂ × E₃ -> G} {f₁ : F -> E₁} {f₂ : F -> E₂} {f₃ : F -> E₃}
    {s : Set F} (hg : ContDiff 𝕜 n g) (hf₁ : ContDiffOn 𝕜 n f₁ s) (hf₂ : ContDiffOn 𝕜 n f₂ s)
    (hf₃ : ContDiffOn 𝕜 n f₃ s) : ContDiffOn 𝕜 n (fun x => g (f₁ x, f₂ x, f₃ x)) s :=
hg.comp₂_contDiffOn hf₁ hf₂.prodMk hf₃

end NAry

section SpecificBilinearMaps

@[fun_prop]
/--
theorem `ContDiff.clm_comp` / 定理 `ContDiff.clm_comp`

English:
theorem ContDiff.clm_comp
  statement: {g : X -> F ->L[𝕜] G} {f : X -> E ->L[𝕜] F} (hg : ContDiff 𝕜 n g)
  proof: isBoundedBilinearMap_comp.contDiff.comp₂ (g := fun p => p.1.comp p.2) hg hf

@[fun_prop]

中文:
定理 连续可微.clm_comp
  结论: {g : X -> F ->L[𝕜] G} {f : X -> E ->L[𝕜] F} (hg : 连续可微 𝕜 n g)
  证明: isBoundedBilinearMap_comp.contDiff.comp₂ (g := fun p => p.1.comp p.2) hg hf

@[fun_prop]

Depends on / 依赖: contDiff, isBoundedBilinearMap_comp, isBoundedBilinearMap_comp.contDiff.comp
-/
theorem ContDiff.clm_comp {g : X -> F ->L[𝕜] G} {f : X -> E ->L[𝕜] F} (hg : ContDiff 𝕜 n g)
    (hf : ContDiff 𝕜 n f) : ContDiff 𝕜 n fun x => (g x).comp (f x) :=
  isBoundedBilinearMap_comp.contDiff.comp₂ (g := fun p => p.1.comp p.2) hg hf

@[fun_prop]
/--
theorem `ContDiffOn.clm_comp` / 定理 `ContDiffOn.clm_comp`

English:
theorem ContDiffOn.clm_comp
  statement: {g : X -> F ->L[𝕜] G} {f : X -> E ->L[𝕜] F} {s : Set X}
  proof: (isBoundedBilinearMap_comp (E := E) (F := F) (G := G)).contDiff.comp₂_contDiffOn hg hf

@[fun_prop]

中文:
定理 ContDiffOn.clm_comp
  结论: {g : X -> F ->L[𝕜] G} {f : X -> E ->L[𝕜] F} {s : 集合 X}
  证明: (isBoundedBilinearMap_comp (E := E) (F := F) (G := G)).contDiff.comp₂_contDiffOn hg hf

@[fun_prop]

Depends on / 依赖: contDiff, contDiff.comp, isBoundedBilinearMap_comp
-/
theorem ContDiffOn.clm_comp {g : X -> F ->L[𝕜] G} {f : X -> E ->L[𝕜] F} {s : Set X}
    (hg : ContDiffOn 𝕜 n g s) (hf : ContDiffOn 𝕜 n f s) :
    ContDiffOn 𝕜 n (fun x => (g x).comp (f x)) s :=
  (isBoundedBilinearMap_comp (E := E) (F := F) (G := G)).contDiff.comp₂_contDiffOn hg hf

@[fun_prop]
/--
theorem `ContDiffAt.clm_comp` / 定理 `ContDiffAt.clm_comp`

English:
theorem ContDiffAt.clm_comp
  statement: {g : X -> F ->L[𝕜] G} {f : X -> E ->L[𝕜] F} {x : X}
  proof: (isBoundedBilinearMap_comp (E := E) (G := G)).contDiff.comp₂_contDiffAt hg hf

@[fun_prop]

中文:
定理 ContDiffAt.clm_comp
  结论: {g : X -> F ->L[𝕜] G} {f : X -> E ->L[𝕜] F} {x : X}
  证明: (isBoundedBilinearMap_comp (E := E) (G := G)).contDiff.comp₂_contDiffAt hg hf

@[fun_prop]

Depends on / 依赖: contDiff, contDiff.comp, isBoundedBilinearMap_comp
-/
theorem ContDiffAt.clm_comp {g : X -> F ->L[𝕜] G} {f : X -> E ->L[𝕜] F} {x : X}
    (hg : ContDiffAt 𝕜 n g x) (hf : ContDiffAt 𝕜 n f x) :
    ContDiffAt 𝕜 n (fun x => (g x).comp (f x)) x :=
  (isBoundedBilinearMap_comp (E := E) (G := G)).contDiff.comp₂_contDiffAt hg hf

@[fun_prop]
/--
theorem `ContDiffWithinAt.clm_comp` / 定理 `ContDiffWithinAt.clm_comp`

English:
theorem ContDiffWithinAt.clm_comp
  statement: {g : X -> F ->L[𝕜] G} {f : X -> E ->L[𝕜] F} {s : Set X} {x : X}
  proof: (isBoundedBilinearMap_comp (E := E) (G := G)).contDiff.comp₂_contDiffWithinAt hg hf

@[fun_prop]

中文:
定理 ContDiffWithinAt.clm_comp
  结论: {g : X -> F ->L[𝕜] G} {f : X -> E ->L[𝕜] F} {s : 集合 X} {x : X}
  证明: (isBoundedBilinearMap_comp (E := E) (G := G)).contDiff.comp₂_contDiffWithinAt hg hf

@[fun_prop]

Depends on / 依赖: contDiff, contDiff.comp, isBoundedBilinearMap_comp
-/
theorem ContDiffWithinAt.clm_comp {g : X -> F ->L[𝕜] G} {f : X -> E ->L[𝕜] F} {s : Set X} {x : X}
    (hg : ContDiffWithinAt 𝕜 n g s x) (hf : ContDiffWithinAt 𝕜 n f s x) :
    ContDiffWithinAt 𝕜 n (fun x => (g x).comp (f x)) s x :=
  (isBoundedBilinearMap_comp (E := E) (G := G)).contDiff.comp₂_contDiffWithinAt hg hf

@[fun_prop]
/--
theorem `ContDiff.clm_apply` / 定理 `ContDiff.clm_apply`

English:
theorem ContDiff.clm_apply
  statement: {f : E -> F ->L[𝕜] G} {g : E -> F} (hf : ContDiff 𝕜 n f)
  proof: isBoundedBilinearMap_apply.contDiff.comp₂ hf hg

@[fun_prop]

中文:
定理 连续可微.clm_apply
  结论: {f : E -> F ->L[𝕜] G} {g : E -> F} (hf : 连续可微 𝕜 n f)
  证明: isBoundedBilinearMap_apply.contDiff.comp₂ hf hg

@[fun_prop]

Depends on / 依赖: contDiff, isBoundedBilinearMap_apply, isBoundedBilinearMap_apply.contDiff.comp
-/
theorem ContDiff.clm_apply {f : E -> F ->L[𝕜] G} {g : E -> F} (hf : ContDiff 𝕜 n f)
    (hg : ContDiff 𝕜 n g) : ContDiff 𝕜 n fun x => (f x) (g x) :=
  isBoundedBilinearMap_apply.contDiff.comp₂ hf hg

@[fun_prop]
/--
theorem `ContDiffOn.clm_apply` / 定理 `ContDiffOn.clm_apply`

English:
theorem ContDiffOn.clm_apply
  statement: {f : E -> F ->L[𝕜] G} {g : E -> F} (hf : ContDiffOn 𝕜 n f s)
  proof: isBoundedBilinearMap_apply.contDiff.comp₂_contDiffOn hf hg

@[fun_prop]

中文:
定理 ContDiffOn.clm_apply
  结论: {f : E -> F ->L[𝕜] G} {g : E -> F} (hf : ContDiffOn 𝕜 n f s)
  证明: isBoundedBilinearMap_apply.contDiff.comp₂_contDiffOn hf hg

@[fun_prop]

Depends on / 依赖: contDiff, isBoundedBilinearMap_apply, isBoundedBilinearMap_apply.contDiff.comp
-/
theorem ContDiffOn.clm_apply {f : E -> F ->L[𝕜] G} {g : E -> F} (hf : ContDiffOn 𝕜 n f s)
    (hg : ContDiffOn 𝕜 n g s) : ContDiffOn 𝕜 n (fun x => (f x) (g x)) s :=
  isBoundedBilinearMap_apply.contDiff.comp₂_contDiffOn hf hg

@[fun_prop]
/--
theorem `ContDiffAt.clm_apply` / 定理 `ContDiffAt.clm_apply`

English:
theorem ContDiffAt.clm_apply
  statement: {f : E -> F ->L[𝕜] G} {g : E -> F} (hf : ContDiffAt 𝕜 n f x)
  proof: isBoundedBilinearMap_apply.contDiff.comp₂_contDiffAt hf hg

@[fun_prop]

中文:
定理 ContDiffAt.clm_apply
  结论: {f : E -> F ->L[𝕜] G} {g : E -> F} (hf : ContDiffAt 𝕜 n f x)
  证明: isBoundedBilinearMap_apply.contDiff.comp₂_contDiffAt hf hg

@[fun_prop]

Depends on / 依赖: contDiff, isBoundedBilinearMap_apply, isBoundedBilinearMap_apply.contDiff.comp
-/
theorem ContDiffAt.clm_apply {f : E -> F ->L[𝕜] G} {g : E -> F} (hf : ContDiffAt 𝕜 n f x)
    (hg : ContDiffAt 𝕜 n g x) : ContDiffAt 𝕜 n (fun x => (f x) (g x)) x :=
  isBoundedBilinearMap_apply.contDiff.comp₂_contDiffAt hf hg

@[fun_prop]
/--
theorem `ContDiffWithinAt.clm_apply` / 定理 `ContDiffWithinAt.clm_apply`

English:
theorem ContDiffWithinAt.clm_apply
  statement: {f : E -> F ->L[𝕜] G} {g : E -> F}
  proof: isBoundedBilinearMap_apply.contDiff.comp₂_contDiffWithinAt hf hg

@[fun_prop]

中文:
定理 ContDiffWithinAt.clm_apply
  结论: {f : E -> F ->L[𝕜] G} {g : E -> F}
  证明: isBoundedBilinearMap_apply.contDiff.comp₂_contDiffWithinAt hf hg

@[fun_prop]

Depends on / 依赖: contDiff, isBoundedBilinearMap_apply, isBoundedBilinearMap_apply.contDiff.comp
-/
theorem ContDiffWithinAt.clm_apply {f : E -> F ->L[𝕜] G} {g : E -> F}
    (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) :
    ContDiffWithinAt 𝕜 n (fun x => (f x) (g x)) s x :=
  isBoundedBilinearMap_apply.contDiff.comp₂_contDiffWithinAt hf hg

@[fun_prop]
/--
theorem `ContDiff.smulRight` / 定理 `ContDiff.smulRight`

English:
theorem ContDiff.smulRight
  statement: {f : E -> StrongDual 𝕜 F} {g : E -> G} (hf : ContDiff 𝕜 n f)
  proof: isBoundedBilinearMap_smulRight.contDiff.comp₂ (g := fun p => p.1.smulRight p.2) hf hg

@[fun_prop]

中文:
定理 连续可微.smulRight
  结论: {f : E -> StrongDual 𝕜 F} {g : E -> G} (hf : 连续可微 𝕜 n f)
  证明: isBoundedBilinearMap_smulRight.contDiff.comp₂ (g := fun p => p.1.smulRight p.2) hf hg

@[fun_prop]

Depends on / 依赖: contDiff, isBoundedBilinearMap_smulRight, isBoundedBilinearMap_smulRight.contDiff.comp, smulRight
-/
theorem ContDiff.smulRight {f : E -> StrongDual 𝕜 F} {g : E -> G} (hf : ContDiff 𝕜 n f)
    (hg : ContDiff 𝕜 n g) : ContDiff 𝕜 n fun x => (f x).smulRight (g x) :=
  isBoundedBilinearMap_smulRight.contDiff.comp₂ (g := fun p => p.1.smulRight p.2) hf hg

@[fun_prop]
/--
theorem `ContDiffOn.smulRight` / 定理 `ContDiffOn.smulRight`

English:
theorem ContDiffOn.smulRight
  statement: {f : E -> StrongDual 𝕜 F} {g : E -> G} (hf : ContDiffOn 𝕜 n f s)
  proof: (isBoundedBilinearMap_smulRight (E := F)).contDiff.comp₂_contDiffOn hf hg

@[fun_prop]

中文:
定理 ContDiffOn.smulRight
  结论: {f : E -> StrongDual 𝕜 F} {g : E -> G} (hf : ContDiffOn 𝕜 n f s)
  证明: (isBoundedBilinearMap_smulRight (E := F)).contDiff.comp₂_contDiffOn hf hg

@[fun_prop]

Depends on / 依赖: contDiff, contDiff.comp, isBoundedBilinearMap_smulRight
-/
theorem ContDiffOn.smulRight {f : E -> StrongDual 𝕜 F} {g : E -> G} (hf : ContDiffOn 𝕜 n f s)
    (hg : ContDiffOn 𝕜 n g s) : ContDiffOn 𝕜 n (fun x => (f x).smulRight (g x)) s :=
  (isBoundedBilinearMap_smulRight (E := F)).contDiff.comp₂_contDiffOn hf hg

@[fun_prop]
/--
theorem `ContDiffAt.smulRight` / 定理 `ContDiffAt.smulRight`

English:
theorem ContDiffAt.smulRight
  statement: {f : E -> StrongDual 𝕜 F} {g : E -> G} (hf : ContDiffAt 𝕜 n f x)
  proof: (isBoundedBilinearMap_smulRight (E := F)).contDiff.comp₂_contDiffAt hf hg

@[fun_prop]

中文:
定理 ContDiffAt.smulRight
  结论: {f : E -> StrongDual 𝕜 F} {g : E -> G} (hf : ContDiffAt 𝕜 n f x)
  证明: (isBoundedBilinearMap_smulRight (E := F)).contDiff.comp₂_contDiffAt hf hg

@[fun_prop]

Depends on / 依赖: contDiff, contDiff.comp, isBoundedBilinearMap_smulRight
-/
theorem ContDiffAt.smulRight {f : E -> StrongDual 𝕜 F} {g : E -> G} (hf : ContDiffAt 𝕜 n f x)
    (hg : ContDiffAt 𝕜 n g x) : ContDiffAt 𝕜 n (fun x => (f x).smulRight (g x)) x :=
  (isBoundedBilinearMap_smulRight (E := F)).contDiff.comp₂_contDiffAt hf hg

@[fun_prop]
/--
theorem `ContDiffWithinAt.smulRight` / 定理 `ContDiffWithinAt.smulRight`

English:
theorem ContDiffWithinAt.smulRight
  statement: {f : E -> StrongDual 𝕜 F} {g : E -> G}
  proof: (isBoundedBilinearMap_smulRight (E := F)).contDiff.comp₂_contDiffWithinAt hf hg

中文:
定理 ContDiffWithinAt.smulRight
  结论: {f : E -> StrongDual 𝕜 F} {g : E -> G}
  证明: (isBoundedBilinearMap_smulRight (E := F)).contDiff.comp₂_contDiffWithinAt hf hg

Depends on / 依赖: contDiff, contDiff.comp, isBoundedBilinearMap_smulRight
-/
theorem ContDiffWithinAt.smulRight {f : E -> StrongDual 𝕜 F} {g : E -> G}
    (hf : ContDiffWithinAt 𝕜 n f s x) (hg : ContDiffWithinAt 𝕜 n g s x) :
    ContDiffWithinAt 𝕜 n (fun x => (f x).smulRight (g x)) s x :=
  (isBoundedBilinearMap_smulRight (E := F)).contDiff.comp₂_contDiffWithinAt hf hg

end SpecificBilinearMaps

section ClmApplyConst

/--
theorem `iteratedFDerivWithin_clm_apply_const_apply` / 定理 `iteratedFDerivWithin_clm_apply_const_apply`

English:
theorem iteratedFDerivWithin_clm_apply_const_apply
  proof: by
  induction i generalizing x with
  | zero => simp
  | succ i ih =>
    replace hi : (i : Nat∞ω) < n := lt_of_lt_of_le (by norm_cast; simp) hi
    have h_deriv_apply : DifferentiableOn 𝕜 (iteratedFDerivWithin 𝕜 i (fun y => (c y) u) s) s :=
      (hc.clm_apply contDiffOn_const).differentiableOn_iteratedFDerivWithin hi hs
    have h_deriv : DifferentiableOn 𝕜 (iteratedFDerivWithin 𝕜 i c s) s :=
      hc.differentiableOn_iteratedFDerivWithin hi hs
    simp only [iteratedFDerivWithin_succ_apply_left]
    rw [← fderivWithin_continuousMultilinear_apply_const_apply (hs x hx) (h_deriv_apply x hx)]
    rw [fderivWithin_congr' (fun x hx => ih hi.le hx) hx]
    rw [fderivWithin_clm_apply (hs x hx) (h_deriv.continuousMultilinear_apply_const _ x hx)
      (differentiableWithinAt_const u)]
    rw [fderivWithin_const_apply]
    simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_zero, zero_add]
    rw [fderivWithin_continuousMultilinear_apply_const_apply (hs x hx) (h_deriv x hx)]

中文:
定理 iteratedFDerivWithin_clm_apply_const_apply
  证明: by
  induction i generalizing x with
  | zero => simp
  | succ i ih =>
    replace hi : (i : Nat∞ω) < n := lt_of_lt_of_le (by norm_cast; simp) hi
    have h_deriv_apply : DifferentiableOn 𝕜 (iteratedFDerivWithin 𝕜 i (fun y => (c y) u) s) s :=
      (hc.clm_apply contDiffOn_const).differentiableOn_iteratedFDerivWithin hi hs
    have h_deriv : DifferentiableOn 𝕜 (iteratedFDerivWithin 𝕜 i c s) s :=
      hc.differentiableOn_iteratedFDerivWithin hi hs
    simp only [iteratedFDerivWithin_succ_apply_left]
    rw [← fderivWithin_continuousMultilinear_apply_const_apply (hs x hx) (h_deriv_apply x hx)]
    rw [fderivWithin_congr' (fun x hx => ih hi.le hx) hx]
    rw [fderivWithin_clm_apply (hs x hx) (h_deriv.continuousMultilinear_apply_const _ x hx)
      (differentiableWithinAt_const u)]
    rw [fderivWithin_const_apply]
    simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_zero, zero_add]
    rw [fderivWithin_continuousMultilinear_apply_const_apply (hs x hx) (h_deriv x hx)]

Depends on / 依赖: DifferentiableOn, clm_apply, contDiffOn_const, differentiableOn_iteratedFDerivWithin, fderivWithin_continuous, generalizing, h_deriv, h_deriv_apply, hc.clm_apply, hc.differentiableOn_iteratedFDerivWithin, iteratedFDerivWithin, iteratedFDerivWithin_succ_apply_left, lt_of_lt_of_le, replace
-/
theorem iteratedFDerivWithin_clm_apply_const_apply
    {s : Set E} (hs : UniqueDiffOn 𝕜 s) {c : E -> F ->L[𝕜] G}
    (hc : ContDiffOn 𝕜 n c s) {i : Nat} (hi : i <= n) {x : E} (hx : x in s) {u : F} {m : Fin i -> E} :
    (iteratedFDerivWithin 𝕜 i (fun y => (c y) u) s x) m = (iteratedFDerivWithin 𝕜 i c s x) m u := by
  induction i generalizing x with
  | zero => simp
  | succ i ih =>
    replace hi : (i : Nat∞ω) < n := lt_of_lt_of_le (by norm_cast; simp) hi
    have h_deriv_apply : DifferentiableOn 𝕜 (iteratedFDerivWithin 𝕜 i (fun y => (c y) u) s) s :=
      (hc.clm_apply contDiffOn_const).differentiableOn_iteratedFDerivWithin hi hs
    have h_deriv : DifferentiableOn 𝕜 (iteratedFDerivWithin 𝕜 i c s) s :=
      hc.differentiableOn_iteratedFDerivWithin hi hs
    simp only [iteratedFDerivWithin_succ_apply_left]
    rw [← fderivWithin_continuousMultilinear_apply_const_apply (hs x hx) (h_deriv_apply x hx)]
    rw [fderivWithin_congr' (fun x hx => ih hi.le hx) hx]
    rw [fderivWithin_clm_apply (hs x hx) (h_deriv.continuousMultilinear_apply_const _ x hx)
      (differentiableWithinAt_const u)]
    rw [fderivWithin_const_apply]
    simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_zero, zero_add]
    rw [fderivWithin_continuousMultilinear_apply_const_apply (hs x hx) (h_deriv x hx)]

/--
theorem `iteratedFDeriv_clm_apply_const_apply` / 定理 `iteratedFDeriv_clm_apply_const_apply`

English:
theorem iteratedFDeriv_clm_apply_const_apply
  proof: by
  simp only [← iteratedFDerivWithin_univ]
  exact iteratedFDerivWithin_clm_apply_const_apply uniqueDiffOn_univ hc.contDiffOn hi (mem_univ _)

中文:
定理 iteratedFDeriv_clm_apply_const_apply
  证明: by
  simp only [← iteratedFDerivWithin_univ]
  exact iteratedFDerivWithin_clm_apply_const_apply uniqueDiffOn_univ hc.contDiffOn hi (mem_univ _)

Depends on / 依赖: contDiffOn, hc.contDiffOn, iteratedFDerivWithin_clm_apply_const_apply, iteratedFDerivWithin_univ, mem_univ, uniqueDiffOn_univ
-/
theorem iteratedFDeriv_clm_apply_const_apply
    {c : E -> F ->L[𝕜] G} (hc : ContDiff 𝕜 n c)
    {i : Nat} (hi : i <= n) {x : E} {u : F} {m : Fin i -> E} :
    (iteratedFDeriv 𝕜 i (fun y => (c y) u) x) m = (iteratedFDeriv 𝕜 i c x) m u := by
  simp only [← iteratedFDerivWithin_univ]
  exact iteratedFDerivWithin_clm_apply_const_apply uniqueDiffOn_univ hc.contDiffOn hi (mem_univ _)

end ClmApplyConst

/-! ### Bundled derivatives are smooth -/
section bundled

/--
theorem `ContDiffWithinAt.hasFDerivWithinAt_nhds` / 定理 `ContDiffWithinAt.hasFDerivWithinAt_nhds`

English:
theorem ContDiffWithinAt.hasFDerivWithinAt_nhds
  statement: {f : E -> F -> G} {g : E -> F} {t : Set F} (hn : n != ∞)
  proof: by
  have hst : insert x₀ s ×ˢ t in 𝓝[(fun x => (x, g x)) '' s] (x₀, g x₀) := by
    refine nhdsWithin_mono _ ?_ (nhdsWithin_prod self_mem_nhdsWithin hgt)
    simp_rw [image_subset_iff, mk_preimage_prod, preimage_id', subset_inter_iff, subset_insert,
      true_and, subset_preimage_image]
  obtain ⟨v, hv, hvs, f_an, f', hvf', hf'⟩ :=
    (contDiffWithinAt_succ_iff_hasFDerivWithinAt' hn).mp hf
  refine
    ⟨(fun z => (z, g z)) ⁻¹' v inter insert x₀ s, ?_, inter_subset_right, fun z =>
      (f' (z, g z)).comp (ContinuousLinearMap.inr 𝕜 E F), ?_, ?_⟩
  · refine inter_mem ?_ self_mem_nhdsWithin
    have := mem_of_mem_nhdsWithin (mem_insert _ _) hv
    refine mem_nhdsWithin_insert.mpr ⟨this, ?_⟩
    refine (continuousWithinAt_id.prodMk hg.continuousWithinAt).preimage_mem_nhdsWithin' ?_
    rw [← nhdsWithin_le_iff] at hst hv ⊢
    exact (hst.trans <| nhdsWithin_mono _ <| subset_insert _ _).trans hv
  · intro z hz
    have := hvf' (z, g z) hz.1
    refine this.comp _ (hasFDerivAt_prodMk_right _ _).hasFDerivWithinAt ?_
    exact mapsTo_iff_image_subset.mpr (image_prodMk_subset_prod_right hz.2)
  · exact (hf'.continuousLinearMap_comp <| (ContinuousLinearMap.compL 𝕜 F (E × F) G).flip
      (ContinuousLinearMap.inr 𝕜 E F)).comp_of_mem_nhdsWithin_image x₀
      (contDiffWithinAt_id.prodMk hg) hst

中文:
定理 ContDiffWithinAt.hasFDerivWithinAt_nhds
  结论: {f : E -> F -> G} {g : E -> F} {t : 集合 F} (hn : n != ∞)
  证明: by
  have hst : insert x₀ s ×ˢ t in 𝓝[(fun x => (x, g x)) '' s] (x₀, g x₀) := by
    refine nhdsWithin_mono _ ?_ (nhdsWithin_prod self_mem_nhdsWithin hgt)
    simp_rw [image_subset_iff, mk_preimage_prod, preimage_id', subset_inter_iff, subset_insert,
      true_and, subset_preimage_image]
  obtain ⟨v, hv, hvs, f_an, f', hvf', hf'⟩ :=
    (contDiffWithinAt_succ_iff_hasFDerivWithinAt' hn).mp hf
  refine
    ⟨(fun z => (z, g z)) ⁻¹' v inter insert x₀ s, ?_, inter_subset_right, fun z =>
      (f' (z, g z)).comp (ContinuousLinearMap.inr 𝕜 E F), ?_, ?_⟩
  · refine inter_mem ?_ self_mem_nhdsWithin
    have := mem_of_mem_nhdsWithin (mem_insert _ _) hv
    refine mem_nhdsWithin_insert.mpr ⟨this, ?_⟩
    refine (continuousWithinAt_id.prodMk hg.continuousWithinAt).preimage_mem_nhdsWithin' ?_
    rw [← nhdsWithin_le_iff] at hst hv ⊢
    exact (hst.trans <| nhdsWithin_mono _ <| subset_insert _ _).trans hv
  · intro z hz
    have := hvf' (z, g z) hz.1
    refine this.comp _ (hasFDerivAt_prodMk_right _ _).hasFDerivWithinAt ?_
    exact mapsTo_iff_image_subset.mpr (image_prodMk_subset_prod_right hz.2)
  · exact (hf'.continuousLinearMap_comp <| (ContinuousLinearMap.compL 𝕜 F (E × F) G).flip
      (ContinuousLinearMap.inr 𝕜 E F)).comp_of_mem_nhdsWithin_image x₀
      (contDiffWithinAt_id.prodMk hg) hst

Depends on / 依赖: ContinuousLinearMap, contDiffWithinAt_succ_iff_hasFDerivWithinAt, f_an, image_subset_iff, insert, inter_subset_right, mk_preimage_prod, nhdsWithin_mono, nhdsWithin_prod, preimage_id, self_mem_nhdsWithin, simp_rw, subset_insert, subset_inter_iff, subset_preimage_image, true_and
-/
theorem ContDiffWithinAt.hasFDerivWithinAt_nhds {f : E -> F -> G} {g : E -> F} {t : Set F} (hn : n != ∞)
    {x₀ : E} (hf : ContDiffWithinAt 𝕜 (n + 1) (uncurry f) (insert x₀ s ×ˢ t) (x₀, g x₀))
    (hg : ContDiffWithinAt 𝕜 n g s x₀) (hgt : t in 𝓝[g '' s] g x₀) :
    exists v in 𝓝[insert x₀ s] x₀, v subseteq insert x₀ s ∧ exists f' : E -> F ->L[𝕜] G,
      (forall x in v, HasFDerivWithinAt (f x) (f' x) t (g x)) ∧
        ContDiffWithinAt 𝕜 n (fun x => f' x) s x₀ := by
  have hst : insert x₀ s ×ˢ t in 𝓝[(fun x => (x, g x)) '' s] (x₀, g x₀) := by
    refine nhdsWithin_mono _ ?_ (nhdsWithin_prod self_mem_nhdsWithin hgt)
    simp_rw [image_subset_iff, mk_preimage_prod, preimage_id', subset_inter_iff, subset_insert,
      true_and, subset_preimage_image]
  obtain ⟨v, hv, hvs, f_an, f', hvf', hf'⟩ :=
    (contDiffWithinAt_succ_iff_hasFDerivWithinAt' hn).mp hf
  refine
    ⟨(fun z => (z, g z)) ⁻¹' v inter insert x₀ s, ?_, inter_subset_right, fun z =>
      (f' (z, g z)).comp (ContinuousLinearMap.inr 𝕜 E F), ?_, ?_⟩
  · refine inter_mem ?_ self_mem_nhdsWithin
    have := mem_of_mem_nhdsWithin (mem_insert _ _) hv
    refine mem_nhdsWithin_insert.mpr ⟨this, ?_⟩
    refine (continuousWithinAt_id.prodMk hg.continuousWithinAt).preimage_mem_nhdsWithin' ?_
    rw [← nhdsWithin_le_iff] at hst hv ⊢
    exact (hst.trans <| nhdsWithin_mono _ <| subset_insert _ _).trans hv
  · intro z hz
    have := hvf' (z, g z) hz.1
    refine this.comp _ (hasFDerivAt_prodMk_right _ _).hasFDerivWithinAt ?_
    exact mapsTo_iff_image_subset.mpr (image_prodMk_subset_prod_right hz.2)
  · exact (hf'.continuousLinearMap_comp <| (ContinuousLinearMap.compL 𝕜 F (E × F) G).flip
      (ContinuousLinearMap.inr 𝕜 E F)).comp_of_mem_nhdsWithin_image x₀
      (contDiffWithinAt_id.prodMk hg) hst

/--
theorem `ContDiffWithinAt.fderivWithin''` / 定理 `ContDiffWithinAt.fderivWithin''`

English:
theorem ContDiffWithinAt.fderivWithin''
  statement: {f : E -> F -> G} {g : E -> F} {t : Set F}
  proof: by
  have : forall k : Nat, k <= m -> ContDiffWithinAt 𝕜 k (fun x => fderivWithin 𝕜 (f x) t (g x)) s x₀ := by
    intro k hkm
    obtain ⟨v, hv, -, f', hvf', hf'⟩ :=
      (hf.of_le <| by grw [hkm, hmn]).hasFDerivWithinAt_nhds (by simp) (hg.of_le hkm) hgt
    refine hf'.congr_of_eventuallyEq_insert ?_
    filter_upwards [hv, ht]
    exact fun y hy h2y => (hvf' y hy).fderivWithin h2y
  match m with
  | ω =>
    obtain rfl : n = ω := by simpa using hmn
    obtain ⟨v, hv, -, f', hvf', hf'⟩ := hf.hasFDerivWithinAt_nhds (by simp) hg hgt
    refine hf'.congr_of_eventuallyEq_insert ?_
    filter_upwards [hv, ht]
    exact fun y hy h2y => (hvf' y hy).fderivWithin h2y
  | ∞ =>
    rw [contDiffWithinAt_infty]
    exact fun k => this k (by exact_mod_cast le_top)
  | (m : Nat) => exact this _ le_rfl

中文:
定理 ContDiffWithinAt.fderivWithin''
  结论: {f : E -> F -> G} {g : E -> F} {t : 集合 F}
  证明: by
  have : forall k : Nat, k <= m -> ContDiffWithinAt 𝕜 k (fun x => fderivWithin 𝕜 (f x) t (g x)) s x₀ := by
    intro k hkm
    obtain ⟨v, hv, -, f', hvf', hf'⟩ :=
      (hf.of_le <| by grw [hkm, hmn]).hasFDerivWithinAt_nhds (by simp) (hg.of_le hkm) hgt
    refine hf'.congr_of_eventuallyEq_insert ?_
    filter_upwards [hv, ht]
    exact fun y hy h2y => (hvf' y hy).fderivWithin h2y
  match m with
  | ω =>
    obtain rfl : n = ω := by simpa using hmn
    obtain ⟨v, hv, -, f', hvf', hf'⟩ := hf.hasFDerivWithinAt_nhds (by simp) hg hgt
    refine hf'.congr_of_eventuallyEq_insert ?_
    filter_upwards [hv, ht]
    exact fun y hy h2y => (hvf' y hy).fderivWithin h2y
  | ∞ =>
    rw [contDiffWithinAt_infty]
    exact fun k => this k (by exact_mod_cast le_top)
  | (m : Nat) => exact this _ le_rfl

Depends on / 依赖: ContDiffWithinAt, congr_of_eventuallyEq_insert, fderivWithin, filter_upwards, hasFDerivWithinAt_nhds, hf.hasFDerivWithinAt_nhds, hf.of_le, hg.of_le, of_le
-/
theorem ContDiffWithinAt.fderivWithin'' {f : E -> F -> G} {g : E -> F} {t : Set F}
    (hf : ContDiffWithinAt 𝕜 n (Function.uncurry f) (insert x₀ s ×ˢ t) (x₀, g x₀))
    (hg : ContDiffWithinAt 𝕜 m g s x₀)
    (ht : forallᶠ x in 𝓝[insert x₀ s] x₀, UniqueDiffWithinAt 𝕜 t (g x)) (hmn : m + 1 <= n)
    (hgt : t in 𝓝[g '' s] g x₀) :
    ContDiffWithinAt 𝕜 m (fun x => fderivWithin 𝕜 (f x) t (g x)) s x₀ := by
  have : forall k : Nat, k <= m -> ContDiffWithinAt 𝕜 k (fun x => fderivWithin 𝕜 (f x) t (g x)) s x₀ := by
    intro k hkm
    obtain ⟨v, hv, -, f', hvf', hf'⟩ :=
      (hf.of_le <| by grw [hkm, hmn]).hasFDerivWithinAt_nhds (by simp) (hg.of_le hkm) hgt
    refine hf'.congr_of_eventuallyEq_insert ?_
    filter_upwards [hv, ht]
    exact fun y hy h2y => (hvf' y hy).fderivWithin h2y
  match m with
  | ω =>
    obtain rfl : n = ω := by simpa using hmn
    obtain ⟨v, hv, -, f', hvf', hf'⟩ := hf.hasFDerivWithinAt_nhds (by simp) hg hgt
    refine hf'.congr_of_eventuallyEq_insert ?_
    filter_upwards [hv, ht]
    exact fun y hy h2y => (hvf' y hy).fderivWithin h2y
  | ∞ =>
    rw [contDiffWithinAt_infty]
    exact fun k => this k (by exact_mod_cast le_top)
  | (m : Nat) => exact this _ le_rfl

/--
theorem `ContDiffWithinAt.fderivWithin'` / 定理 `ContDiffWithinAt.fderivWithin'`

English:
theorem ContDiffWithinAt.fderivWithin'
  statement: {f : E -> F -> G} {g : E -> F} {t : Set F}
  proof: hf.fderivWithin'' hg ht hmn mem_of_superset self_mem_nhdsWithin image_subset_iff.mpr hst

中文:
定理 ContDiffWithinAt.fderivWithin'
  结论: {f : E -> F -> G} {g : E -> F} {t : 集合 F}
  证明: hf.fderivWithin'' hg ht hmn mem_of_superset self_mem_nhdsWithin image_subset_iff.mpr hst

Depends on / 依赖: fderivWithin, hf.fderivWithin, image_subset_iff, image_subset_iff.mpr, mem_of_superset, self_mem_nhdsWithin
-/
theorem ContDiffWithinAt.fderivWithin' {f : E -> F -> G} {g : E -> F} {t : Set F}
    (hf : ContDiffWithinAt 𝕜 n (Function.uncurry f) (insert x₀ s ×ˢ t) (x₀, g x₀))
    (hg : ContDiffWithinAt 𝕜 m g s x₀)
    (ht : forallᶠ x in 𝓝[insert x₀ s] x₀, UniqueDiffWithinAt 𝕜 t (g x)) (hmn : m + 1 <= n)
    (hst : s subseteq g ⁻¹' t) : ContDiffWithinAt 𝕜 m (fun x => fderivWithin 𝕜 (f x) t (g x)) s x₀ :=
hf.fderivWithin'' hg ht hmn mem_of_superset self_mem_nhdsWithin image_subset_iff.mpr hst

/--
theorem `ContDiffWithinAt.fderivWithin` / 定理 `ContDiffWithinAt.fderivWithin`

English:
theorem ContDiffWithinAt.fderivWithin
  statement: {f : E -> F -> G} {g : E -> F} {t : Set F}
  proof: by
  rw [← insert_eq_self.mpr hx₀] at hf
  refine hf.fderivWithin' hg ?_ hmn hst
  rw [insert_eq_self.mpr hx₀]
  exact eventually_of_mem self_mem_nhdsWithin fun x hx => ht _ (hst hx)

中文:
定理 ContDiffWithinAt.fderivWithin
  结论: {f : E -> F -> G} {g : E -> F} {t : 集合 F}
  证明: by
  rw [← insert_eq_self.mpr hx₀] at hf
  refine hf.fderivWithin' hg ?_ hmn hst
  rw [insert_eq_self.mpr hx₀]
  exact eventually_of_mem self_mem_nhdsWithin fun x hx => ht _ (hst hx)
-/
protected theorem ContDiffWithinAt.fderivWithin {f : E -> F -> G} {g : E -> F} {t : Set F}
    (hf : ContDiffWithinAt 𝕜 n (Function.uncurry f) (s ×ˢ t) (x₀, g x₀))
    (hg : ContDiffWithinAt 𝕜 m g s x₀) (ht : UniqueDiffOn 𝕜 t) (hmn : m + 1 <= n) (hx₀ : x₀ in s)
    (hst : s subseteq g ⁻¹' t) : ContDiffWithinAt 𝕜 m (fun x => fderivWithin 𝕜 (f x) t (g x)) s x₀ := by
  rw [← insert_eq_self.mpr hx₀] at hf
  refine hf.fderivWithin' hg ?_ hmn hst
  rw [insert_eq_self.mpr hx₀]
  exact eventually_of_mem self_mem_nhdsWithin fun x hx => ht _ (hst hx)

/--
theorem `ContDiffWithinAt.fderivWithin_apply` / 定理 `ContDiffWithinAt.fderivWithin_apply`

English:
theorem ContDiffWithinAt.fderivWithin_apply
  statement: {f : E -> F -> G} {g k : E -> F} {t : Set F}
  proof: (contDiff_fst.clm_apply contDiff_snd).contDiffAt.comp_contDiffWithinAt x₀
    ((hf.fderivWithin hg ht hmn hx₀ hst).prodMk hk)

中文:
定理 ContDiffWithinAt.fderivWithin_apply
  结论: {f : E -> F -> G} {g k : E -> F} {t : 集合 F}
  证明: (contDiff_fst.clm_apply contDiff_snd).contDiffAt.comp_contDiffWithinAt x₀
    ((hf.fderivWithin hg ht hmn hx₀ hst).prodMk hk)

Depends on / 依赖: clm_apply, comp_contDiffWithinAt, contDiffAt, contDiffAt.comp_contDiffWithinAt, contDiff_fst, contDiff_fst.clm_apply, contDiff_snd, fderivWithin, hf.fderivWithin, prodMk
-/
theorem ContDiffWithinAt.fderivWithin_apply {f : E -> F -> G} {g k : E -> F} {t : Set F}
    (hf : ContDiffWithinAt 𝕜 n (Function.uncurry f) (s ×ˢ t) (x₀, g x₀))
    (hg : ContDiffWithinAt 𝕜 m g s x₀) (hk : ContDiffWithinAt 𝕜 m k s x₀) (ht : UniqueDiffOn 𝕜 t)
    (hmn : m + 1 <= n) (hx₀ : x₀ in s) (hst : s subseteq g ⁻¹' t) :
    ContDiffWithinAt 𝕜 m (fun x => fderivWithin 𝕜 (f x) t (g x) (k x)) s x₀ :=
  (contDiff_fst.clm_apply contDiff_snd).contDiffAt.comp_contDiffWithinAt x₀
    ((hf.fderivWithin hg ht hmn hx₀ hst).prodMk hk)

/--
theorem `ContDiffWithinAt.fderivWithin_right` / 定理 `ContDiffWithinAt.fderivWithin_right`

English:
theorem ContDiffWithinAt.fderivWithin_right
  statement: (hf : ContDiffWithinAt 𝕜 n f s x₀)
  proof: ContDiffWithinAt.fderivWithin
    (ContDiffWithinAt.comp (x₀, x₀) hf contDiffWithinAt_snd <| prod_subset_preimage_snd s s)
    contDiffWithinAt_id hs hmn hx₀s (by rw [preimage_id'])

中文:
定理 ContDiffWithinAt.fderivWithin_right
  结论: (hf : ContDiffWithinAt 𝕜 n f s x₀)
  证明: ContDiffWithinAt.fderivWithin
    (ContDiffWithinAt.comp (x₀, x₀) hf contDiffWithinAt_snd <| prod_subset_preimage_snd s s)
    contDiffWithinAt_id hs hmn hx₀s (by rw [preimage_id'])

Depends on / 依赖: ContDiffWithinAt, ContDiffWithinAt.comp, ContDiffWithinAt.fderivWithin, contDiffWithinAt_id, contDiffWithinAt_snd, fderivWithin, preimage_id, prod_subset_preimage_snd
-/
theorem ContDiffWithinAt.fderivWithin_right (hf : ContDiffWithinAt 𝕜 n f s x₀)
    (hs : UniqueDiffOn 𝕜 s) (hmn : m + 1 <= n) (hx₀s : x₀ in s) :
    ContDiffWithinAt 𝕜 m (fderivWithin 𝕜 f s) s x₀ :=
  ContDiffWithinAt.fderivWithin
    (ContDiffWithinAt.comp (x₀, x₀) hf contDiffWithinAt_snd <| prod_subset_preimage_snd s s)
    contDiffWithinAt_id hs hmn hx₀s (by rw [preimage_id'])

/--
theorem `ContDiffWithinAt.fderivWithin_right_apply` / 定理 `ContDiffWithinAt.fderivWithin_right_apply`

English:
theorem ContDiffWithinAt.fderivWithin_right_apply
  proof: ContDiffWithinAt.fderivWithin_apply
    (ContDiffWithinAt.comp (x₀, x₀) hf contDiffWithinAt_snd <| prod_subset_preimage_snd s s)
    contDiffWithinAt_id hk hs hmn hx₀s (by rw [preimage_id'])

中文:
定理 ContDiffWithinAt.fderivWithin_right_apply
  证明: ContDiffWithinAt.fderivWithin_apply
    (ContDiffWithinAt.comp (x₀, x₀) hf contDiffWithinAt_snd <| prod_subset_preimage_snd s s)
    contDiffWithinAt_id hk hs hmn hx₀s (by rw [preimage_id'])

Depends on / 依赖: ContDiffWithinAt, ContDiffWithinAt.comp, ContDiffWithinAt.fderivWithin_apply, contDiffWithinAt_id, contDiffWithinAt_snd, fderivWithin_apply, preimage_id, prod_subset_preimage_snd
-/
theorem ContDiffWithinAt.fderivWithin_right_apply
    {f : F -> G} {k : F -> F} {s : Set F} {x₀ : F}
    (hf : ContDiffWithinAt 𝕜 n f s x₀) (hk : ContDiffWithinAt 𝕜 m k s x₀)
    (hs : UniqueDiffOn 𝕜 s) (hmn : m + 1 <= n) (hx₀s : x₀ in s) :
    ContDiffWithinAt 𝕜 m (fun x => fderivWithin 𝕜 f s x (k x)) s x₀ :=
  ContDiffWithinAt.fderivWithin_apply
    (ContDiffWithinAt.comp (x₀, x₀) hf contDiffWithinAt_snd <| prod_subset_preimage_snd s s)
    contDiffWithinAt_id hk hs hmn hx₀s (by rw [preimage_id'])

-- TODO: can we make a version of `ContDiffWithinAt.fderivWithin` for iterated derivatives?
/--
theorem `ContDiffWithinAt.iteratedFDerivWithin_right` / 定理 `ContDiffWithinAt.iteratedFDerivWithin_right`

English:
theorem ContDiffWithinAt.iteratedFDerivWithin_right
  statement: {i : Nat} (hf : ContDiffWithinAt 𝕜 n f s x₀)
  proof: by
  induction i generalizing m with
  | zero =>
    simp only [CharP.cast_eq_zero, add_zero] at hmn
    exact (hf.of_le hmn).continuousLinearMap_comp
      ((continuousMultilinearCurryFin0 𝕜 E F).symm : _ ->L[𝕜] E [×0]->L[𝕜] F)
  | succ i hi =>
    rw [Nat.cast_succ]; rw [add_comm _ 1]; rw [← add_assoc] at hmn
    exact ((hi hmn).fderivWithin_right hs le_rfl hx₀s).continuousLinearMap_comp
      ((continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (i + 1) => E) F).symm :
        _ ->L[𝕜] E [×(i + 1)]->L[𝕜] F)

中文:
定理 ContDiffWithinAt.iteratedFDerivWithin_right
  结论: {i : 自然数} (hf : ContDiffWithinAt 𝕜 n f s x₀)
  证明: by
  induction i generalizing m with
  | zero =>
    simp only [CharP.cast_eq_zero, add_zero] at hmn
    exact (hf.of_le hmn).continuousLinearMap_comp
      ((continuousMultilinearCurryFin0 𝕜 E F).symm : _ ->L[𝕜] E [×0]->L[𝕜] F)
  | succ i hi =>
    rw [Nat.cast_succ]; rw [add_comm _ 1]; rw [← add_assoc] at hmn
    exact ((hi hmn).fderivWithin_right hs le_rfl hx₀s).continuousLinearMap_comp
      ((continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (i + 1) => E) F).symm :
        _ ->L[𝕜] E [×(i + 1)]->L[𝕜] F)

Depends on / 依赖: CharP.cast_eq_zero, Nat.cast_succ, add_assoc, add_comm, add_zero, cast_eq_zero, cast_succ, continuousLinearMap_comp, continuousMultilinearCurryFin0, continuousMultilinearCurryLeftEquiv, fderivWithin_right, generalizing, hf.of_le, le_rfl, of_le
-/
theorem ContDiffWithinAt.iteratedFDerivWithin_right {i : Nat} (hf : ContDiffWithinAt 𝕜 n f s x₀)
    (hs : UniqueDiffOn 𝕜 s) (hmn : m + i <= n) (hx₀s : x₀ in s) :
    ContDiffWithinAt 𝕜 m (iteratedFDerivWithin 𝕜 i f s) s x₀ := by
  induction i generalizing m with
  | zero =>
    simp only [CharP.cast_eq_zero, add_zero] at hmn
    exact (hf.of_le hmn).continuousLinearMap_comp
      ((continuousMultilinearCurryFin0 𝕜 E F).symm : _ ->L[𝕜] E [×0]->L[𝕜] F)
  | succ i hi =>
    rw [Nat.cast_succ]; rw [add_comm _ 1]; rw [← add_assoc] at hmn
    exact ((hi hmn).fderivWithin_right hs le_rfl hx₀s).continuousLinearMap_comp
      ((continuousMultilinearCurryLeftEquiv 𝕜 (fun _ : Fin (i + 1) => E) F).symm :
        _ ->L[𝕜] E [×(i + 1)]->L[𝕜] F)

/--
theorem `ContDiffAt.fderiv` / 定理 `ContDiffAt.fderiv`

English:
theorem ContDiffAt.fderiv
  statement: {f : E -> F -> G} {g : E -> F}
  proof: by
  simp_rw [← fderivWithin_univ]
  refine (ContDiffWithinAt.fderivWithin hf.contDiffWithinAt hg.contDiffWithinAt uniqueDiffOn_univ
    hmn (mem_univ x₀) ?_).contDiffAt univ_mem
  rw [preimage_univ]

@[fun_prop]

中文:
定理 ContDiffAt.fderiv
  结论: {f : E -> F -> G} {g : E -> F}
  证明: by
  simp_rw [← fderivWithin_univ]
  refine (ContDiffWithinAt.fderivWithin hf.contDiffWithinAt hg.contDiffWithinAt uniqueDiffOn_univ
    hmn (mem_univ x₀) ?_).contDiffAt univ_mem
  rw [preimage_univ]

@[fun_prop]
-/
protected theorem ContDiffAt.fderiv {f : E -> F -> G} {g : E -> F}
    (hf : ContDiffAt 𝕜 n (Function.uncurry f) (x₀, g x₀)) (hg : ContDiffAt 𝕜 m g x₀)
    (hmn : m + 1 <= n) : ContDiffAt 𝕜 m (fun x => fderiv 𝕜 (f x) (g x)) x₀ := by
  simp_rw [← fderivWithin_univ]
  refine (ContDiffWithinAt.fderivWithin hf.contDiffWithinAt hg.contDiffWithinAt uniqueDiffOn_univ
    hmn (mem_univ x₀) ?_).contDiffAt univ_mem
  rw [preimage_univ]

@[fun_prop]
/--
theorem `ContDiffAt.fderiv_succ` / 定理 `ContDiffAt.fderiv_succ`

English:
theorem ContDiffAt.fderiv_succ
  statement: {f : E -> F -> G} {g : E -> F}
  proof: ContDiffAt.fderiv hf hg (le_refl _)

中文:
定理 ContDiffAt.fderiv_succ
  结论: {f : E -> F -> G} {g : E -> F}
  证明: ContDiffAt.fderiv hf hg (le_refl _)
-/
protected theorem ContDiffAt.fderiv_succ {f : E -> F -> G} {g : E -> F}
    (hf : ContDiffAt 𝕜 (m + 1) (Function.uncurry f) (x₀, g x₀)) (hg : ContDiffAt 𝕜 m g x₀) :
    ContDiffAt 𝕜 m (fun x => fderiv 𝕜 (f x) (g x)) x₀ :=
  ContDiffAt.fderiv hf hg (le_refl _)

/--
theorem `ContDiffAt.fderiv_right` / 定理 `ContDiffAt.fderiv_right`

English:
theorem ContDiffAt.fderiv_right
  given: (hf : ContDiffAt 𝕜 n f x₀) (hmn : m + 1 <= n)
  proof: ContDiffAt.fderiv (ContDiffAt.comp (x₀, x₀) hf contDiffAt_snd) contDiffAt_id hmn

中文:
定理 ContDiffAt.fderiv_right
  条件: (hf : ContDiffAt 𝕜 n f x₀) (hmn : m + 1 <= n)
  证明: ContDiffAt.fderiv (ContDiffAt.comp (x₀, x₀) hf contDiffAt_snd) contDiffAt_id hmn

Depends on / 依赖: ContDiffAt, ContDiffAt.comp, ContDiffAt.fderiv, contDiffAt_id, contDiffAt_snd, fderiv
-/
theorem ContDiffAt.fderiv_right (hf : ContDiffAt 𝕜 n f x₀) (hmn : m + 1 <= n) :
    ContDiffAt 𝕜 m (fderiv 𝕜 f) x₀ :=
  ContDiffAt.fderiv (ContDiffAt.comp (x₀, x₀) hf contDiffAt_snd) contDiffAt_id hmn

/--
theorem `ContDiffAt.fderiv_right_succ` / 定理 `ContDiffAt.fderiv_right_succ`

English:
theorem ContDiffAt.fderiv_right_succ
  given: (hf : ContDiffAt 𝕜 (n + 1) f x₀)
  proof: ContDiffAt.fderiv (ContDiffAt.comp (x₀, x₀) hf contDiffAt_snd) contDiffAt_id (le_refl (n + 1))

中文:
定理 ContDiffAt.fderiv_right_succ
  条件: (hf : ContDiffAt 𝕜 (n + 1) f x₀)
  证明: ContDiffAt.fderiv (ContDiffAt.comp (x₀, x₀) hf contDiffAt_snd) contDiffAt_id (le_refl (n + 1))

Depends on / 依赖: ContDiffAt, ContDiffAt.comp, ContDiffAt.fderiv, contDiffAt_id, contDiffAt_snd, fderiv, le_refl
-/
theorem ContDiffAt.fderiv_right_succ (hf : ContDiffAt 𝕜 (n + 1) f x₀) :
    ContDiffAt 𝕜 n (fderiv 𝕜 f) x₀ :=
  ContDiffAt.fderiv (ContDiffAt.comp (x₀, x₀) hf contDiffAt_snd) contDiffAt_id (le_refl (n + 1))

/--
theorem `ContDiffAt.iteratedFDeriv_right` / 定理 `ContDiffAt.iteratedFDeriv_right`

English:
theorem ContDiffAt.iteratedFDeriv_right
  statement: {i : Nat} (hf : ContDiffAt 𝕜 n f x₀)
  proof: by
  rw [← iteratedFDerivWithin_univ]; rw [← contDiffWithinAt_univ] at *
  exact hf.iteratedFDerivWithin_right uniqueDiffOn_univ hmn trivial

中文:
定理 ContDiffAt.iteratedFDeriv_right
  结论: {i : 自然数} (hf : ContDiffAt 𝕜 n f x₀)
  证明: by
  rw [← iteratedFDerivWithin_univ]; rw [← contDiffWithinAt_univ] at *
  exact hf.iteratedFDerivWithin_right uniqueDiffOn_univ hmn trivial

Depends on / 依赖: contDiffWithinAt_univ, hf.iteratedFDerivWithin_right, iteratedFDerivWithin_right, iteratedFDerivWithin_univ, uniqueDiffOn_univ
-/
theorem ContDiffAt.iteratedFDeriv_right {i : Nat} (hf : ContDiffAt 𝕜 n f x₀)
    (hmn : m + i <= n) : ContDiffAt 𝕜 m (iteratedFDeriv 𝕜 i f) x₀ := by
  rw [← iteratedFDerivWithin_univ]; rw [← contDiffWithinAt_univ] at *
  exact hf.iteratedFDerivWithin_right uniqueDiffOn_univ hmn trivial

/--
theorem `ContDiff.fderiv` / 定理 `ContDiff.fderiv`

English:
theorem ContDiff.fderiv
  statement: {f : E -> F -> G} {g : E -> F}
  proof: contDiff_iff_contDiffAt.mpr fun _ => hf.contDiffAt.fderiv hg.contDiffAt hnm

@[fun_prop]

中文:
定理 连续可微.fderiv
  结论: {f : E -> F -> G} {g : E -> F}
  证明: contDiff_iff_contDiffAt.mpr fun _ => hf.contDiffAt.fderiv hg.contDiffAt hnm

@[fun_prop]
-/
protected theorem ContDiff.fderiv {f : E -> F -> G} {g : E -> F}
    (hf : ContDiff 𝕜 m <| Function.uncurry f) (hg : ContDiff 𝕜 n g) (hnm : n + 1 <= m) :
    ContDiff 𝕜 n fun x => fderiv 𝕜 (f x) (g x) :=
  contDiff_iff_contDiffAt.mpr fun _ => hf.contDiffAt.fderiv hg.contDiffAt hnm

@[fun_prop]
/--
theorem `ContDiff.fderiv_succ` / 定理 `ContDiff.fderiv_succ`

English:
theorem ContDiff.fderiv_succ
  statement: {f : E -> F -> G} {g : E -> F}
  proof: contDiff_iff_contDiffAt.mpr fun _ => hf.contDiffAt.fderiv hg.contDiffAt (le_refl (n + 1))

中文:
定理 连续可微.fderiv_succ
  结论: {f : E -> F -> G} {g : E -> F}
  证明: contDiff_iff_contDiffAt.mpr fun _ => hf.contDiffAt.fderiv hg.contDiffAt (le_refl (n + 1))
-/
protected theorem ContDiff.fderiv_succ {f : E -> F -> G} {g : E -> F}
    (hf : ContDiff 𝕜 (n + 1) <| Function.uncurry f) (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n fun x => fderiv 𝕜 (f x) (g x) :=
  contDiff_iff_contDiffAt.mpr fun _ => hf.contDiffAt.fderiv hg.contDiffAt (le_refl (n + 1))

/--
theorem `ContDiff.fderiv_right` / 定理 `ContDiff.fderiv_right`

English:
theorem ContDiff.fderiv_right
  given: (hf : ContDiff 𝕜 n f) (hmn : m + 1 <= n)
  proof: contDiff_iff_contDiffAt.mpr fun _x => hf.contDiffAt.fderiv_right hmn

中文:
定理 连续可微.fderiv_right
  条件: (hf : 连续可微 𝕜 n f) (hmn : m + 1 <= n)
  证明: contDiff_iff_contDiffAt.mpr fun _x => hf.contDiffAt.fderiv_right hmn

Depends on / 依赖: contDiffAt, contDiff_iff_contDiffAt, contDiff_iff_contDiffAt.mpr, fderiv_right, hf.contDiffAt.fderiv_right
-/
theorem ContDiff.fderiv_right (hf : ContDiff 𝕜 n f) (hmn : m + 1 <= n) :
    ContDiff 𝕜 m (fderiv 𝕜 f) :=
  contDiff_iff_contDiffAt.mpr fun _x => hf.contDiffAt.fderiv_right hmn

/--
theorem `ContDiff.iteratedFDeriv_right` / 定理 `ContDiff.iteratedFDeriv_right`

English:
theorem ContDiff.iteratedFDeriv_right
  statement: {i : Nat} (hf : ContDiff 𝕜 n f)
  proof: contDiff_iff_contDiffAt.mpr fun _x => hf.contDiffAt.iteratedFDeriv_right hmn

@[fun_prop]

中文:
定理 连续可微.iteratedFDeriv_right
  结论: {i : 自然数} (hf : 连续可微 𝕜 n f)
  证明: contDiff_iff_contDiffAt.mpr fun _x => hf.contDiffAt.iteratedFDeriv_right hmn

@[fun_prop]

Depends on / 依赖: contDiffAt, contDiff_iff_contDiffAt, contDiff_iff_contDiffAt.mpr, hf.contDiffAt.iteratedFDeriv_right, iteratedFDeriv_right
-/
theorem ContDiff.iteratedFDeriv_right {i : Nat} (hf : ContDiff 𝕜 n f)
    (hmn : m + i <= n) : ContDiff 𝕜 m (iteratedFDeriv 𝕜 i f) :=
  contDiff_iff_contDiffAt.mpr fun _x => hf.contDiffAt.iteratedFDeriv_right hmn

@[fun_prop]
/--
theorem `ContDiff.iteratedFDeriv_right'` / 定理 `ContDiff.iteratedFDeriv_right'`

English:
theorem ContDiff.iteratedFDeriv_right'
  given: {i : Nat} (hf : ContDiff 𝕜 (m + i) f)
  proof: contDiff_iff_contDiffAt.mpr fun _x => hf.contDiffAt.iteratedFDeriv_right (le_refl _)

中文:
定理 连续可微.iteratedFDeriv_right'
  条件: {i : 自然数} (hf : 连续可微 𝕜 (m + i) f)
  证明: contDiff_iff_contDiffAt.mpr fun _x => hf.contDiffAt.iteratedFDeriv_right (le_refl _)

Depends on / 依赖: contDiffAt, contDiff_iff_contDiffAt, contDiff_iff_contDiffAt.mpr, hf.contDiffAt.iteratedFDeriv_right, iteratedFDeriv_right, le_refl
-/
theorem ContDiff.iteratedFDeriv_right' {i : Nat} (hf : ContDiff 𝕜 (m + i) f) :
    ContDiff 𝕜 m (iteratedFDeriv 𝕜 i f) :=
  contDiff_iff_contDiffAt.mpr fun _x => hf.contDiffAt.iteratedFDeriv_right (le_refl _)

/--
theorem `Continuous.fderiv` / 定理 `Continuous.fderiv`

English:
theorem Continuous.fderiv
  statement: {f : E -> F -> G} {g : E -> F}
  proof: (hf.fderiv (contDiff_zero.mpr hg) hn).continuous

@[fun_prop]

中文:
定理 连续.fderiv
  结论: {f : E -> F -> G} {g : E -> F}
  证明: (hf.fderiv (contDiff_zero.mpr hg) hn).continuous

@[fun_prop]

Depends on / 依赖: contDiff_zero, contDiff_zero.mpr, continuous, fderiv, hf.fderiv
-/
theorem Continuous.fderiv {f : E -> F -> G} {g : E -> F}
    (hf : ContDiff 𝕜 n <| Function.uncurry f) (hg : Continuous g) (hn : 1 <= n) :
    Continuous fun x => fderiv 𝕜 (f x) (g x) :=
  (hf.fderiv (contDiff_zero.mpr hg) hn).continuous

@[fun_prop]
/--
theorem `Continuous.fderiv_one` / 定理 `Continuous.fderiv_one`

English:
theorem Continuous.fderiv_one
  statement: {f : E -> F -> G} {g : E -> F}
  proof: (hf.fderiv (contDiff_zero.mpr hg) (le_refl 1)).continuous

@[fun_prop]

中文:
定理 连续.fderiv_one
  结论: {f : E -> F -> G} {g : E -> F}
  证明: (hf.fderiv (contDiff_zero.mpr hg) (le_refl 1)).continuous

@[fun_prop]

Depends on / 依赖: contDiff_zero, contDiff_zero.mpr, continuous, fderiv, hf.fderiv, le_refl
-/
theorem Continuous.fderiv_one {f : E -> F -> G} {g : E -> F}
    (hf : ContDiff 𝕜 1 <| Function.uncurry f) (hg : Continuous g) :
    Continuous fun x => _root_.fderiv 𝕜 (f x) (g x) :=
  (hf.fderiv (contDiff_zero.mpr hg) (le_refl 1)).continuous

@[fun_prop]
/--
theorem `Differentiable.fderiv_two` / 定理 `Differentiable.fderiv_two`

English:
theorem Differentiable.fderiv_two
  statement: {f : E -> F -> G} {g : E -> F}
  proof: ContDiff.differentiable
    (contDiff_iff_contDiffAt.mpr fun _ => hf.contDiffAt.fderiv hg.contDiffAt (le_refl 2))
    one_ne_zero

中文:
定理 可微.fderiv_two
  结论: {f : E -> F -> G} {g : E -> F}
  证明: ContDiff.differentiable
    (contDiff_iff_contDiffAt.mpr fun _ => hf.contDiffAt.fderiv hg.contDiffAt (le_refl 2))
    one_ne_zero
-/
protected theorem Differentiable.fderiv_two {f : E -> F -> G} {g : E -> F}
    (hf : ContDiff 𝕜 2 <| Function.uncurry f) (hg : ContDiff 𝕜 1 g) :
    Differentiable 𝕜 fun x => fderiv 𝕜 (f x) (g x) :=
  ContDiff.differentiable
    (contDiff_iff_contDiffAt.mpr fun _ => hf.contDiffAt.fderiv hg.contDiffAt (le_refl 2))
    one_ne_zero

/--
theorem `ContDiff.fderiv_apply` / 定理 `ContDiff.fderiv_apply`

English:
theorem ContDiff.fderiv_apply
  statement: {f : E -> F -> G} {g k : E -> F}
  proof: (hf.fderiv hg hnm).clm_apply hk

中文:
定理 连续可微.fderiv_apply
  结论: {f : E -> F -> G} {g k : E -> F}
  证明: (hf.fderiv hg hnm).clm_apply hk

Depends on / 依赖: clm_apply, fderiv, hf.fderiv
-/
theorem ContDiff.fderiv_apply {f : E -> F -> G} {g k : E -> F}
    (hf : ContDiff 𝕜 m <| Function.uncurry f) (hg : ContDiff 𝕜 n g) (hk : ContDiff 𝕜 n k)
    (hnm : n + 1 <= m) : ContDiff 𝕜 n fun x => fderiv 𝕜 (f x) (g x) (k x) :=
  (hf.fderiv hg hnm).clm_apply hk

/--
theorem `contDiffOn_fderivWithin_apply` / 定理 `contDiffOn_fderivWithin_apply`

English:
theorem contDiffOn_fderivWithin_apply
  statement: {s : Set E} {f : E -> F} (hf : ContDiffOn 𝕜 n f s)
  proof: ((hf.fderivWithin hs hmn).comp contDiffOn_fst (prod_subset_preimage_fst _ _)).clm_apply
    contDiffOn_snd

中文:
定理 contDiffOn_fderivWithin_apply
  结论: {s : 集合 E} {f : E -> F} (hf : ContDiffOn 𝕜 n f s)
  证明: ((hf.fderivWithin hs hmn).comp contDiffOn_fst (prod_subset_preimage_fst _ _)).clm_apply
    contDiffOn_snd

Depends on / 依赖: clm_apply, contDiffOn_fst, contDiffOn_snd, fderivWithin, hf.fderivWithin, prod_subset_preimage_fst
-/
theorem contDiffOn_fderivWithin_apply {s : Set E} {f : E -> F} (hf : ContDiffOn 𝕜 n f s)
    (hs : UniqueDiffOn 𝕜 s) (hmn : m + 1 <= n) :
    ContDiffOn 𝕜 m (fun p : E × E => (fderivWithin 𝕜 f s p.1 : E ->L[𝕜] F) p.2) (s ×ˢ univ) :=
  ((hf.fderivWithin hs hmn).comp contDiffOn_fst (prod_subset_preimage_fst _ _)).clm_apply
    contDiffOn_snd

/--
theorem `ContDiffOn.continuousOn_fderivWithin_apply` / 定理 `ContDiffOn.continuousOn_fderivWithin_apply`

English:
theorem ContDiffOn.continuousOn_fderivWithin_apply
  statement: (hf : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s)
  proof: (contDiffOn_fderivWithin_apply (m := 0) hf hs hn).continuousOn

中文:
定理 ContDiffOn.continuousOn_fderivWithin_apply
  结论: (hf : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s)
  证明: (contDiffOn_fderivWithin_apply (m := 0) hf hs hn).continuousOn

Depends on / 依赖: contDiffOn_fderivWithin_apply, continuousOn
-/
theorem ContDiffOn.continuousOn_fderivWithin_apply (hf : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s)
    (hn : 1 <= n) :
    ContinuousOn (fun p : E × E => (fderivWithin 𝕜 f s p.1 : E -> F) p.2) (s ×ˢ univ) :=
  (contDiffOn_fderivWithin_apply (m := 0) hf hs hn).continuousOn

/--
theorem `ContDiff.contDiff_fderiv_apply` / 定理 `ContDiff.contDiff_fderiv_apply`

English:
theorem ContDiff.contDiff_fderiv_apply
  given: {f : E -> F} (hf : ContDiff 𝕜 n f) (hmn : m + 1 <= n)
  proof: by
  rw [← contDiffOn_univ] at hf ⊢
  rw [← fderivWithin_univ]; rw [← univ_prod_univ]
  exact contDiffOn_fderivWithin_apply hf uniqueDiffOn_univ hmn

中文:
定理 连续可微.contDiff_fderiv_apply
  条件: {f : E -> F} (hf : 连续可微 𝕜 n f) (hmn : m + 1 <= n)
  证明: by
  rw [← contDiffOn_univ] at hf ⊢
  rw [← fderivWithin_univ]; rw [← univ_prod_univ]
  exact contDiffOn_fderivWithin_apply hf uniqueDiffOn_univ hmn

Depends on / 依赖: contDiffOn_fderivWithin_apply, contDiffOn_univ, fderivWithin_univ, uniqueDiffOn_univ, univ_prod_univ
-/
theorem ContDiff.contDiff_fderiv_apply {f : E -> F} (hf : ContDiff 𝕜 n f) (hmn : m + 1 <= n) :
    ContDiff 𝕜 m fun p : E × E => (fderiv 𝕜 f p.1 : E ->L[𝕜] F) p.2 := by
  rw [← contDiffOn_univ] at hf ⊢
  rw [← fderivWithin_univ]; rw [← univ_prod_univ]
  exact contDiffOn_fderivWithin_apply hf uniqueDiffOn_univ hmn

/--
theorem `ContDiffWithinAt.continuousWithinAt_fderivWithin` / 定理 `ContDiffWithinAt.continuousWithinAt_fderivWithin`

English:
theorem ContDiffWithinAt.continuousWithinAt_fderivWithin
  proof: hf.fderivWithin_right (m := 0) hs (by simpa [ENat.one_le_iff_ne_zero_withTop]) hx
.continuousWithinAt

中文:
定理 ContDiffWithinAt.continuousWithinAt_fderivWithin
  证明: hf.fderivWithin_right (m := 0) hs (by simpa [ENat.one_le_iff_ne_zero_withTop]) hx
.continuousWithinAt

Depends on / 依赖: ENat.one_le_iff_ne_zero_withTop, continuousWithinAt, fderivWithin_right, hf.fderivWithin_right, one_le_iff_ne_zero_withTop
-/
theorem ContDiffWithinAt.continuousWithinAt_fderivWithin
    (hf : ContDiffWithinAt 𝕜 n f s x) (hs : UniqueDiffOn 𝕜 s) (hn : n != 0) (hx : x in s) :
    ContinuousWithinAt (fderivWithin 𝕜 f s) s x :=
  hf.fderivWithin_right (m := 0) hs (by simpa [ENat.one_le_iff_ne_zero_withTop]) hx
.continuousWithinAt

/--
theorem `ContDiffAt.continuousAt_fderiv` / 定理 `ContDiffAt.continuousAt_fderiv`

English:
theorem ContDiffAt.continuousAt_fderiv
  given: (hf : ContDiffAt 𝕜 n f x) (hn : n != 0)
  proof: .continuousAt hf.fderiv_right (m := 0) (by simpa [ENat.one_le_iff_ne_zero_withTop])

中文:
定理 ContDiffAt.continuousAt_fderiv
  条件: (hf : ContDiffAt 𝕜 n f x) (hn : n != 0)
  证明: .continuousAt hf.fderiv_right (m := 0) (by simpa [ENat.one_le_iff_ne_zero_withTop])

Depends on / 依赖: ENat.one_le_iff_ne_zero_withTop, continuousAt, fderiv_right, hf.fderiv_right, one_le_iff_ne_zero_withTop
-/
theorem ContDiffAt.continuousAt_fderiv (hf : ContDiffAt 𝕜 n f x) (hn : n != 0) :
    ContinuousAt (fderiv 𝕜 f) x :=
.continuousAt hf.fderiv_right (m := 0) (by simpa [ENat.one_le_iff_ne_zero_withTop])

/--
theorem `ContDiffWithinAt.continuousWithinAt_iteratedFDerivWithin` / 定理 `ContDiffWithinAt.continuousWithinAt_iteratedFDerivWithin`

English:
theorem ContDiffWithinAt.continuousWithinAt_iteratedFDerivWithin
  statement: {k : Nat}
  proof: .continuousWithinAt hf.iteratedFDerivWithin_right (m := 0) hs (by simpa) hx

中文:
定理 ContDiffWithinAt.continuousWithinAt_iteratedFDerivWithin
  结论: {k : 自然数}
  证明: .continuousWithinAt hf.iteratedFDerivWithin_right (m := 0) hs (by simpa) hx

Depends on / 依赖: continuousWithinAt, hf.iteratedFDerivWithin_right, iteratedFDerivWithin_right
-/
theorem ContDiffWithinAt.continuousWithinAt_iteratedFDerivWithin {k : Nat}
    (hf : ContDiffWithinAt 𝕜 n f s x) (hs : UniqueDiffOn 𝕜 s) (hk : k <= n) (hx : x in s) :
    ContinuousWithinAt (iteratedFDerivWithin 𝕜 k f s) s x :=
.continuousWithinAt hf.iteratedFDerivWithin_right (m := 0) hs (by simpa) hx

/--
theorem `ContinuousOn.continuousOn_iteratedFDerivWithin` / 定理 `ContinuousOn.continuousOn_iteratedFDerivWithin`

English:
theorem ContinuousOn.continuousOn_iteratedFDerivWithin
  statement: {k : Nat}
  proof: .continuousWithinAt_iteratedFDerivWithin hs hk hx fun _x hx => hf.contDiffWithinAt hx

中文:
定理 ContinuousOn.continuousOn_iteratedFDerivWithin
  结论: {k : 自然数}
  证明: .continuousWithinAt_iteratedFDerivWithin hs hk hx fun _x hx => hf.contDiffWithinAt hx

Depends on / 依赖: contDiffWithinAt, continuousWithinAt_iteratedFDerivWithin, hf.contDiffWithinAt
-/
theorem ContinuousOn.continuousOn_iteratedFDerivWithin {k : Nat}
    (hf : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s) (hk : k <= n) :
    ContinuousOn (iteratedFDerivWithin 𝕜 k f s) s :=
.continuousWithinAt_iteratedFDerivWithin hs hk hx fun _x hx => hf.contDiffWithinAt hx

/--
theorem `ContDiffAt.continuousAt_iteratedFDeriv` / 定理 `ContDiffAt.continuousAt_iteratedFDeriv`

English:
theorem ContDiffAt.continuousAt_iteratedFDeriv
  given: {k : Nat} (hf : ContDiffAt 𝕜 n f x) (hk : k <= n)
  proof: .continuousAt hf.iteratedFDeriv_right (m := 0) (by simpa)

中文:
定理 ContDiffAt.continuousAt_iteratedFDeriv
  条件: {k : 自然数} (hf : ContDiffAt 𝕜 n f x) (hk : k <= n)
  证明: .continuousAt hf.iteratedFDeriv_right (m := 0) (by simpa)

Depends on / 依赖: continuousAt, hf.iteratedFDeriv_right, iteratedFDeriv_right
-/
theorem ContDiffAt.continuousAt_iteratedFDeriv {k : Nat} (hf : ContDiffAt 𝕜 n f x) (hk : k <= n) :
    ContinuousAt (iteratedFDeriv 𝕜 k f) x :=
.continuousAt hf.iteratedFDeriv_right (m := 0) (by simpa)

/--
theorem `ContinuousOn.continuousOn_iteratedFDeriv` / 定理 `ContinuousOn.continuousOn_iteratedFDeriv`

English:
theorem ContinuousOn.continuousOn_iteratedFDeriv
  statement: {k : Nat}
  proof: .continuousWithinAt .continuousAt_iteratedFDeriv hk fun _x hx => hf.contDiffAt (hs.mem_nhds hx)

中文:
定理 ContinuousOn.continuousOn_iteratedFDeriv
  结论: {k : 自然数}
  证明: .continuousWithinAt .continuousAt_iteratedFDeriv hk fun _x hx => hf.contDiffAt (hs.mem_nhds hx)

Depends on / 依赖: contDiffAt, continuousAt_iteratedFDeriv, continuousWithinAt, hf.contDiffAt, hs.mem_nhds, mem_nhds
-/
theorem ContinuousOn.continuousOn_iteratedFDeriv {k : Nat}
    (hf : ContDiffOn 𝕜 n f s) (hs : IsOpen s) (hk : k <= n) :
    ContinuousOn (iteratedFDeriv 𝕜 k f) s :=
.continuousWithinAt .continuousAt_iteratedFDeriv hk fun _x hx => hf.contDiffAt (hs.mem_nhds hx)

end bundled
