/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-!
# Non-linear maps close to affine maps

In this file we study a map `f` such that `‖f x - f y - f' (x - y)‖ ≤ c * ‖x - y‖` on an open set
`s`, where `f' : E →L[𝕜] F` is a continuous linear map and `c` is suitably small. Maps of this type
behave like `f a + f' (x - a)` near each `a ∈ s`.

When `f'` is onto, we show that `f` is locally onto.

When `f'` is a continuous linear equiv, we show that `f` is a homeomorphism
between `s` and `f '' s`. More precisely, we define `ApproximatesLinearOn.toOpenPartialHomeomorph`
to be an `OpenPartialHomeomorph` with `toFun = f`, `source = s`, and `target = f '' s`.
between `s` and `f '' s`. More precisely, we define `ApproximatesLinearOn.toOpenPartialHomeomorph`
to be an `OpenPartialHomeomorph` with `toFun = f`, `source = s`, and `target = f '' s`.

Maps of this type naturally appear in the proof of the inverse function theorem (see next section),
and `ApproximatesLinearOn.toOpenPartialHomeomorph` will imply that the locally inverse function
and `ApproximatesLinearOn.toOpenPartialHomeomorph` will imply that the locally inverse function
exists.

We define this auxiliary notion to split the proof of the inverse function theorem into small
lemmas. This approach makes it possible

- to prove a lower estimate on the size of the domain of the inverse function;

- to reuse parts of the proofs in the case if a function is not strictly differentiable. E.g., for a
  function `f : E × F → G` with estimates on `f x y₁ - f x y₂` but not on `f x₁ y - f x₂ y`.

## Notation

We introduce some `local notation` to make formulas shorter:

* by `N` we denote `‖f'⁻¹‖`;
* by `g` we denote the auxiliary contracting map `x ↦ x + f'.symm (y - f x)` used to prove that
  `{x | f x = y}` is nonempty.
-/

@[expose] public section

open Function Set Filter Metric

open scoped Topology NNReal

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {ε : Real}

open Filter Metric Set

open ContinuousLinearMap (id)

/--
Definition of `ApproximatesLinearOn` / `ApproximatesLinearOn` 的定义

English:
definition ApproximatesLinearOn
  signature: (f : E -> F) (f' : E ->L[𝕜] F) (s : Set E) (c : Real>=0)
  body: forall x in s, forall y in s, ‖f x - f y - f' (x - y)‖ <= c * ‖x - y‖

@[simp]

中文:
定义 ApproximatesLinearOn
  签名: (f : E -> F) (f' : E ->L[𝕜] F) (s : Set E) (c : 实数>=0)
  定义体: forall x in s, forall y in s, ‖f x - f y - f' (x - y)‖ <= c * ‖x - y‖

@[simp]
-/
def ApproximatesLinearOn (f : E -> F) (f' : E ->L[𝕜] F) (s : Set E) (c : Real>=0) : Prop :=
  forall x in s, forall y in s, ‖f x - f y - f' (x - y)‖ <= c * ‖x - y‖

@[simp]
/--
theorem `approximatesLinearOn_empty` / 定理 `approximatesLinearOn_empty`

English:
theorem approximatesLinearOn_empty
  given: (f : E -> F) (f' : E ->L[𝕜] F) (c : Real>=0)
  proof: by simp [ApproximatesLinearOn]

中文:
定理 approximatesLinearOn_empty
  条件: (f : E -> F) (f' : E ->L[𝕜] F) (c : 实数>=0)
  证明: by simp [ApproximatesLinearOn]

Depends on / 依赖: ApproximatesLinearOn
-/
theorem approximatesLinearOn_empty (f : E -> F) (f' : E ->L[𝕜] F) (c : Real>=0) :
    ApproximatesLinearOn f f' ∅ c := by simp [ApproximatesLinearOn]

namespace ApproximatesLinearOn

variable {f : E -> F}

/-! First we prove some properties of a function that `ApproximatesLinearOn` a (not necessarily
invertible) continuous linear map. -/


section

variable {f' : E ->L[𝕜] F} {s t : Set E} {c c' : Real>=0}

/--
theorem `mono_num` / 定理 `mono_num`

English:
theorem mono_num
  given: (hc : c <= c') (hf : ApproximatesLinearOn f f' s c)
  proof: fun x hx y hy => le_trans (hf x hx y hy) (by gcongr)

中文:
定理 mono_num
  条件: (hc : c <= c') (hf : ApproximatesLinearOn f f' s c)
  证明: fun x hx y hy => le_trans (hf x hx y hy) (by gcongr)

Depends on / 依赖: le_trans
-/
theorem mono_num (hc : c <= c') (hf : ApproximatesLinearOn f f' s c) :
    ApproximatesLinearOn f f' s c' :=
  fun x hx y hy => le_trans (hf x hx y hy) (by gcongr)

/--
theorem `mono_set` / 定理 `mono_set`

English:
theorem mono_set
  given: (hst : s subseteq t) (hf : ApproximatesLinearOn f f' t c)
  proof: fun x hx y hy => hf x (hst hx) y (hst hy)

中文:
定理 mono_set
  条件: (hst : s subseteq t) (hf : ApproximatesLinearOn f f' t c)
  证明: fun x hx y hy => hf x (hst hx) y (hst hy)
-/
theorem mono_set (hst : s subseteq t) (hf : ApproximatesLinearOn f f' t c) :
    ApproximatesLinearOn f f' s c := fun x hx y hy => hf x (hst hx) y (hst hy)

/--
theorem `approximatesLinearOn_iff_lipschitzOnWith` / 定理 `approximatesLinearOn_iff_lipschitzOnWith`

English:
theorem approximatesLinearOn_iff_lipschitzOnWith
  statement: {f : E -> F} {f' : E ->L[𝕜] F} {s : Set E}
  proof: by
  have : forall x y, f x - f y - f' (x - y) = (f - f') x - (f - f') y := fun x y => by
    simp only [map_sub, Pi.sub_apply]; abel
  simp only [this, lipschitzOnWith_iff_norm_sub_le, ApproximatesLinearOn]

alias ⟨lipschitzOnWith, _root_.LipschitzOnWith.approximatesLinearOn⟩ :=
  approximatesLinea

中文:
定理 approximatesLinearOn_iff_lipschitzOnWith
  结论: {f : E -> F} {f' : E ->L[𝕜] F} {s : Set E}
  证明: by
  have : forall x y, f x - f y - f' (x - y) = (f - f') x - (f - f') y := fun x y => by
    simp only [map_sub, Pi.sub_apply]; abel
  simp only [this, lipschitzOnWith_iff_norm_sub_le, ApproximatesLinearOn]

alias ⟨lipschitzOnWith, _root_.LipschitzOnWith.approximatesLinearOn⟩ :=
  approximatesLinea

Depends on / 依赖: ApproximatesLinearOn, Pi.sub_apply, lipschitzOnWith_iff_norm_sub_le, map_sub, sub_apply
-/
theorem approximatesLinearOn_iff_lipschitzOnWith {f : E -> F} {f' : E ->L[𝕜] F} {s : Set E}
    {c : Real>=0} : ApproximatesLinearOn f f' s c ↔ LipschitzOnWith c (f - ⇑f') s := by
  have : forall x y, f x - f y - f' (x - y) = (f - f') x - (f - f') y := fun x y => by
    simp only [map_sub, Pi.sub_apply]; abel
  simp only [this, lipschitzOnWith_iff_norm_sub_le, ApproximatesLinearOn]

alias ⟨lipschitzOnWith, _root_.LipschitzOnWith.approximatesLinearOn⟩ :=
  approximatesLinearOn_iff_lipschitzOnWith

/--
theorem `lipschitz_sub` / 定理 `lipschitz_sub`

English:
theorem lipschitz_sub
  given: (hf : ApproximatesLinearOn f f' s c)
  proof: hf.lipschitzOnWith.to_restrict

中文:
定理 lipschitz_sub
  条件: (hf : ApproximatesLinearOn f f' s c)
  证明: hf.lipschitzOnWith.to_restrict

Depends on / 依赖: hf.lipschitzOnWith.to_restrict, lipschitzOnWith, to_restrict
-/
theorem lipschitz_sub (hf : ApproximatesLinearOn f f' s c) :
    LipschitzWith c fun x : s => f x - f' x :=
  hf.lipschitzOnWith.to_restrict

/--
theorem `lipschitz` / 定理 `lipschitz`

English:
theorem lipschitz
  given: (hf : ApproximatesLinearOn f f' s c)
  proof: by
  simpa only [domRestrict_apply, add_sub_cancel] using!
    (f'.lipschitz.restrict s).add hf.lipschitz_sub

中文:
定理 lipschitz
  条件: (hf : ApproximatesLinearOn f f' s c)
  证明: by
  simpa only [domRestrict_apply, add_sub_cancel] using!
    (f'.lipschitz.restrict s).add hf.lipschitz_sub
-/
protected theorem lipschitz (hf : ApproximatesLinearOn f f' s c) :
    LipschitzWith (‖f'‖₊ + c) (s.domRestrict f) := by
  simpa only [domRestrict_apply, add_sub_cancel] using!
    (f'.lipschitz.restrict s).add hf.lipschitz_sub

/--
theorem `continuous` / 定理 `continuous`

English:
theorem continuous
  given: (hf : ApproximatesLinearOn f f' s c)
  statement: Continuous (s.domRestrict f)
  proof: hf.lipschitz.continuous

中文:
定理 continuous
  条件: (hf : ApproximatesLinearOn f f' s c)
  结论: Continuous (s.domRestrict f)
  证明: hf.lipschitz.continuous
-/
protected theorem continuous (hf : ApproximatesLinearOn f f' s c) : Continuous (s.domRestrict f) :=
  hf.lipschitz.continuous

/--
theorem `continuousOn` / 定理 `continuousOn`

English:
theorem continuousOn
  given: (hf : ApproximatesLinearOn f f' s c)
  statement: ContinuousOn f s
  proof: continuousOn_iff_continuous_domRestrict.2 hf.continuous

中文:
定理 continuousOn
  条件: (hf : ApproximatesLinearOn f f' s c)
  结论: ContinuousOn f s
  证明: continuousOn_iff_continuous_domRestrict.2 hf.continuous
-/
protected theorem continuousOn (hf : ApproximatesLinearOn f f' s c) : ContinuousOn f s :=
  continuousOn_iff_continuous_domRestrict.2 hf.continuous

end

section LocallyOnto

/-!
We prove that a function which is linearly approximated by a continuous linear map with a nonlinear
right inverse is locally onto. This will apply to the case where the approximating map is a linear
equivalence, for the local inverse theorem, but also whenever the approximating map is onto,
by Banach's open mapping theorem. -/


variable [CompleteSpace E] {s : Set E} {c : Real>=0} {f' : E ->L[𝕜] F}

/--
theorem `surjOn_closedBall_of_nonlinearRightInverse` / 定理 `surjOn_closedBall_of_nonlinearRightInverse`

English:
theorem surjOn_closedBall_of_nonlinearRightInverse
  proof: by
  intro y hy
  rcases le_or_gt (f'symm.nnnorm : Real)⁻¹ c with hc | hc
  · refine ⟨b, by simp [ε0], ?_⟩
    have : dist y (f b) <= 0 :=
      (mem_closedBall.1 hy).trans (mul_nonpos_of_nonpos_of_nonneg (by linarith) ε0)
    simp only [dist_le_zero] at this
    rw [this]
  have If' : (0 : Real) < 

中文:
定理 surjOn_closedBall_of_nonlinearRightInverse
  证明: by
  intro y hy
  rcases le_or_gt (f'symm.nnnorm : Real)⁻¹ c with hc | hc
  · refine ⟨b, by simp [ε0], ?_⟩
    have : dist y (f b) <= 0 :=
      (mem_closedBall.1 hy).trans (mul_nonpos_of_nonpos_of_nonneg (by linarith) ε0)
    simp only [dist_le_zero] at this
    rw [this]
  have If' : (0 : Real) < 

Depends on / 依赖: NNReal, NNReal.coe_nonneg, coe_nonneg, dist_le_zero, inv_eq_one_div, inv_pos, le_or_gt, mem_closedBall, mul_nonpos_of_nonpos_of_nonneg, nnnorm, symm.nnnorm, trans_lt
-/
theorem surjOn_closedBall_of_nonlinearRightInverse
    (hf : ApproximatesLinearOn f f' s c)
    (f'symm : f'.NonlinearRightInverse) {ε : Real} {b : E} (ε0 : 0 <= ε) (hε : closedBall b ε subseteq s) :
    SurjOn f (closedBall b ε) (closedBall (f b) (((f'symm.nnnorm : Real)⁻¹ - c) * ε)) := by
  intro y hy
  rcases le_or_gt (f'symm.nnnorm : Real)⁻¹ c with hc | hc
  · refine ⟨b, by simp [ε0], ?_⟩
    have : dist y (f b) <= 0 :=
      (mem_closedBall.1 hy).trans (mul_nonpos_of_nonpos_of_nonneg (by linarith) ε0)
    simp only [dist_le_zero] at this
    rw [this]
  have If' : (0 : Real) < f'symm.nnnorm := by rw [← inv_pos]; exact (NNReal.coe_nonneg _).trans_lt hc
  have Icf' : (c : Real) * f'symm.nnnorm < 1 := by rwa [inv_eq_one_div, lt_div_iff₀ If'] at hc
  have Jcf' : (1 : Real) - c * f'symm.nnnorm != 0 := by apply ne_of_gt; linarith
  /- We have to show that `y` can be written as `f x` for some `x ∈ closedBall b ε`.
    The idea of the proof is to apply the Banach contraction principle to the map
    `g : x ↦ x + f'symm (y - f x)`, as a fixed point of this map satisfies `f x = y`.
    When `f'symm` is a genuine linear inverse, `g` is a contracting map. In our case, since `f'symm`
    is nonlinear, this map is not contracting (it is not even continuous), but still the proof of
    the contraction theorem holds: `uₙ = gⁿ b` is a Cauchy sequence, converging exponentially fast
    to the desired point `x`. Instead of appealing to general results, we check this by hand.

    The main point is that `f (u n)` becomes exponentially close to `y`, and therefore
    `dist (u (n+1)) (u n)` becomes exponentially small, making it possible to get an inductive
    bound on `dist (u n) b`, from which one checks that `u n` stays in the ball on which one has a
    control. Therefore, the bound can be checked at the next step, and so on inductively.
    -/
  set g := fun x => x + f'symm (y - f x) with hg
  set u := fun n : Nat => g^[n] b with hu
  have usucc : forall n, u (n + 1) = g (u n) := by simp [hu, ← iterate_succ_apply' g _ b]
  -- First bound: if `f z` is close to `y`, then `g z` is close to `z` (i.e., almost a fixed point).
  have A : forall z, dist (g z) z <= f'symm.nnnorm * dist (f z) y := by
    intro z
    rw [dist_eq_norm]; rw [hg]; rw [add_sub_cancel_left]; rw [dist_eq_norm']
    exact f'symm.bound _
  -- Second bound: if `z` and `g z` are in the set with good control, then `f (g z)` becomes closer
  -- to `y` than `f z` was (this uses the linear approximation property, and is the reason for the
  -- choice of the formula for `g`).
  have B :
    forall z in closedBall b ε,
      g z in closedBall b ε -> dist (f (g z)) y <= c * f'symm.nnnorm * dist (f z) y := by
    intro z hz hgz
    set v := f'symm (y - f z)
    calc
      dist (f (g z)) y = ‖f (z + v) - y‖ := by rw [dist_eq_norm]
      _ = ‖f (z + v) - f z - f' v + f' v - (y - f z)‖ := by congr 1; abel
      _ = ‖f (z + v) - f z - f' (z + v - z)‖ := by
        simp only [v, ContinuousLinearMap.NonlinearRightInverse.right_inv, add_sub_cancel_left,
          sub_add_cancel]
      _ <= c * ‖z + v - z‖ := hf _ (hε hgz) _ (hε hz)
      _ <= c * (f'symm.nnnorm * dist (f z) y) := by
        gcongr
        simpa [dist_eq_norm'] using f'symm.bound (y - f z)
      _ = c * f'symm.nnnorm * dist (f z) y := by ring
  -- Third bound: a complicated bound on `dist w b` (that will show up in the induction) is enough
  -- to check that `w` is in the ball on which one has controls. Will be used to check that `u n`
  -- belongs to this ball for all `n`.
  have C : forall (n : Nat) (w : E), dist w b <= f'symm.nnnorm * (1 - ((c : Real) * f'symm.nnnorm) ^ n) /
      (1 - c * f'symm.nnnorm) * dist (f b) y -> w in closedBall b ε := fun n w hw => by
    apply hw.trans
    rw [div_mul_eq_mul_div]; rw [div_le_iff₀]; swap; · linarith
    calc
      (f'symm.nnnorm : Real) * (1 - ((c : Real) * f'symm.nnnorm) ^ n) * dist (f b) y =
          f'symm.nnnorm * dist (f b) y * (1 - ((c : Real) * f'symm.nnnorm) ^ n) := by
        ring
      _ <= f'symm.nnnorm * dist (f b) y * 1 := by
        gcongr
        rw [sub_le_self_iff]
        positivity
      _ <= f'symm.nnnorm * (((f'symm.nnnorm : Real)⁻¹ - c) * ε) := by
        rw [mul_one]
        gcongr
        exact mem_closedBall'.1 hy
      _ = ε * (1 - c * f'symm.nnnorm) := by field
  /- Main inductive control: `f (u n)` becomes exponentially close to `y`, and therefore
    `dist (u (n+1)) (u n)` becomes exponentially small, making it possible to get an inductive
    bound on `dist (u n) b`, from which one checks that `u n` remains in the ball on which we
    have estimates. -/
  have D : forall n : Nat, dist (f (u n)) y <= ((c : Real) * f'symm.nnnorm) ^ n * dist (f b) y ∧
      dist (u n) b <= f'symm.nnnorm * (1 - ((c : Real) * f'symm.nnnorm) ^ n) /
        (1 - (c : Real) * f'symm.nnnorm) * dist (f b) y := fun n => by
    induction n with
    | zero => simp [hu]
    | succ n IH => ?_
    rw [usucc]
    have Ign : dist (g (u n)) b <= f'symm.nnnorm * (1 - ((c : Real) * f'symm.nnnorm) ^ n.succ) /
        (1 - c * f'symm.nnnorm) * dist (f b) y :=
      calc
        dist (g (u n)) b <= dist (g (u n)) (u n) + dist (u n) b := dist_triangle _ _ _
        _ <= f'symm.nnnorm * dist (f (u n)) y + dist (u n) b := add_le_add (A _) le_rfl
        _ <= f'symm.nnnorm * (((c : Real) * f'symm.nnnorm) ^ n * dist (f b) y) +
              f'symm.nnnorm * (1 - ((c : Real) * f'symm.nnnorm) ^ n) / (1 - c * f'symm.nnnorm) *
                dist (f b) y := by
                  gcongr
                  · exact IH.1
                  · exact IH.2
        _ = f'symm.nnnorm * (1 - ((c : Real) * f'symm.nnnorm) ^ n.succ) /
              (1 - (c : Real) * f'symm.nnnorm) * dist (f b) y := by
          replace Jcf' : (1 : Real) - f'symm.nnnorm * c != 0 := by convert! Jcf' using 1; ring
          simp [field, pow_succ, -mul_eq_mul_left_iff]
          ring
    refine ⟨?_, Ign⟩
    calc
      dist (f (g (u n))) y <= c * f'symm.nnnorm * dist (f (u n)) y :=
        B _ (C n _ IH.2) (C n.succ _ Ign)
      _ <= (c : Real) * f'symm.nnnorm * (((c : Real) * f'symm.nnnorm) ^ n * dist (f b) y) := by
        gcongr
        apply IH.1
      _ = ((c : Real) * f'symm.nnnorm) ^ n.succ * dist (f b) y := by simp only [pow_succ']; ring
  -- Deduce from the inductive bound that `uₙ` is a Cauchy sequence, therefore converging.
  have : CauchySeq u := by
    refine cauchySeq_of_le_geometric _ (↑f'symm.nnnorm * dist (f b) y) Icf' fun n => ?_
    calc
      dist (u n) (u (n + 1)) = dist (g (u n)) (u n) := by rw [usucc, dist_comm]
      _ <= f'symm.nnnorm * dist (f (u n)) y := A _
      _ <= f'symm.nnnorm * (((c : Real) * f'symm.nnnorm) ^ n * dist (f b) y) := by
        gcongr
        exact (D n).1
      _ = f'symm.nnnorm * dist (f b) y * ((c : Real) * f'symm.nnnorm) ^ n := by ring
  obtain ⟨x, hx⟩ : exists x, Tendsto u atTop (𝓝 x) := cauchySeq_tendsto_of_complete this
  -- As all the `uₙ` belong to the ball `closedBall b ε`, so does their limit `x`.
  have xmem : x in closedBall b ε :=
    isClosed_closedBall.mem_of_tendsto hx (Eventually.of_forall fun n => C n _ (D n).2)
  refine ⟨x, xmem, ?_⟩
  -- It remains to check that `f x = y`. This follows from continuity of `f` on `closedBall b ε`
  -- and from the fact that `f uₙ` is converging to `y` by construction.
  have hx' : Tendsto u atTop (𝓝[closedBall b ε] x) := by
    simp only [nhdsWithin, tendsto_inf, hx, true_and, tendsto_principal]
    exact Eventually.of_forall fun n => C n _ (D n).2
  have T1 : Tendsto (f ∘ u) atTop (𝓝 (f x)) :=
    (hf.continuousOn.mono hε x xmem).tendsto.comp hx'
  have T2 : Tendsto (f ∘ u) atTop (𝓝 y) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun _ => dist_nonneg) (fun n => (D n).1) ?_
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) Icf').mul tendsto_const_nhds
  exact tendsto_nhds_unique T1 T2

/--
theorem `open_image` / 定理 `open_image`

English:
theorem open_image
  statement: (hf : ApproximatesLinearOn f f' s c) (f'symm : f'.NonlinearRightInverse)
  proof: by
  rcases hc with hE | hc
  · exact isOpen_discrete _
  simp only [isOpen_iff_mem_nhds, nhds_basis_closedBall.mem_iff, forall_mem_image] at hs ⊢
  intro x hx
  rcases hs x hx with ⟨ε, ε0, hε⟩
  refine ⟨(f'symm.nnnorm⁻¹ - c) * ε, mul_pos (sub_pos.2 hc) ε0, ?_⟩
  exact (hf.surjOn_closedBall_of_nonli

中文:
定理 open_image
  结论: (hf : ApproximatesLinearOn f f' s c) (f'symm : f'.NonlinearRightInverse)
  证明: by
  rcases hc with hE | hc
  · exact isOpen_discrete _
  simp only [isOpen_iff_mem_nhds, nhds_basis_closedBall.mem_iff, forall_mem_image] at hs ⊢
  intro x hx
  rcases hs x hx with ⟨ε, ε0, hε⟩
  refine ⟨(f'symm.nnnorm⁻¹ - c) * ε, mul_pos (sub_pos.2 hc) ε0, ?_⟩
  exact (hf.surjOn_closedBall_of_nonli

Depends on / 依赖: Subset, Subset.rfl, forall_mem_image, hf.surjOn_closedBall_of_nonlinearRightInverse, isOpen_discrete, isOpen_iff_mem_nhds, le_of_lt, mem_iff, mul_pos, nhds_basis_closedBall, nhds_basis_closedBall.mem_iff, nnnorm, sub_pos, surjOn_closedBall_of_nonlinearRightInverse, symm.nnnorm
-/
theorem open_image (hf : ApproximatesLinearOn f f' s c) (f'symm : f'.NonlinearRightInverse)
    (hs : IsOpen s) (hc : Subsingleton F ∨ c < f'symm.nnnorm⁻¹) : IsOpen (f '' s) := by
  rcases hc with hE | hc
  · exact isOpen_discrete _
  simp only [isOpen_iff_mem_nhds, nhds_basis_closedBall.mem_iff, forall_mem_image] at hs ⊢
  intro x hx
  rcases hs x hx with ⟨ε, ε0, hε⟩
  refine ⟨(f'symm.nnnorm⁻¹ - c) * ε, mul_pos (sub_pos.2 hc) ε0, ?_⟩
  exact (hf.surjOn_closedBall_of_nonlinearRightInverse f'symm (le_of_lt ε0) hε).mono hε Subset.rfl

/--
theorem `image_mem_nhds` / 定理 `image_mem_nhds`

English:
theorem image_mem_nhds
  statement: (hf : ApproximatesLinearOn f f' s c) (f'symm : f'.NonlinearRightInverse)
  proof: by
  obtain ⟨t, hts, ht, xt⟩ : exists t, t subseteq s ∧ IsOpen t ∧ x in t := _root_.mem_nhds_iff.1 hs
  grw [← hts]
  exact IsOpen.mem_nhds ((hf.mono_set hts).open_image f'symm ht hc) (mem_image_of_mem _ xt)

中文:
定理 image_mem_nhds
  结论: (hf : ApproximatesLinearOn f f' s c) (f'symm : f'.NonlinearRightInverse)
  证明: by
  obtain ⟨t, hts, ht, xt⟩ : exists t, t subseteq s ∧ IsOpen t ∧ x in t := _root_.mem_nhds_iff.1 hs
  grw [← hts]
  exact IsOpen.mem_nhds ((hf.mono_set hts).open_image f'symm ht hc) (mem_image_of_mem _ xt)

Depends on / 依赖: IsOpen, IsOpen.mem_nhds, _root_, _root_.mem_nhds_iff, hf.mono_set, mem_image_of_mem, mem_nhds, mem_nhds_iff, mono_set, open_image, subseteq
-/
theorem image_mem_nhds (hf : ApproximatesLinearOn f f' s c) (f'symm : f'.NonlinearRightInverse)
    {x : E} (hs : s in 𝓝 x) (hc : Subsingleton F ∨ c < f'symm.nnnorm⁻¹) : f '' s in 𝓝 (f x) := by
  obtain ⟨t, hts, ht, xt⟩ : exists t, t subseteq s ∧ IsOpen t ∧ x in t := _root_.mem_nhds_iff.1 hs
  grw [← hts]
  exact IsOpen.mem_nhds ((hf.mono_set hts).open_image f'symm ht hc) (mem_image_of_mem _ xt)

/--
theorem `map_nhds_eq` / 定理 `map_nhds_eq`

English:
theorem map_nhds_eq
  statement: (hf : ApproximatesLinearOn f f' s c) (f'symm : f'.NonlinearRightInverse) {x : E}
  proof: by
  refine
    le_antisymm ((hf.continuousOn x (mem_of_mem_nhds hs)).continuousAt hs) (le_map fun t ht => ?_)
  have : f '' (s inter t) in 𝓝 (f x) :=
    (hf.mono_set inter_subset_left).image_mem_nhds f'symm (inter_mem hs ht) hc
  exact mem_of_superset this (image_mono inter_subset_right)

中文:
定理 map_nhds_eq
  结论: (hf : ApproximatesLinearOn f f' s c) (f'symm : f'.NonlinearRightInverse) {x : E}
  证明: by
  refine
    le_antisymm ((hf.continuousOn x (mem_of_mem_nhds hs)).continuousAt hs) (le_map fun t ht => ?_)
  have : f '' (s inter t) in 𝓝 (f x) :=
    (hf.mono_set inter_subset_left).image_mem_nhds f'symm (inter_mem hs ht) hc
  exact mem_of_superset this (image_mono inter_subset_right)

Depends on / 依赖: continuousAt, continuousOn, hf.continuousOn, hf.mono_set, image_mem_nhds, image_mono, inter_mem, inter_subset_left, inter_subset_right, le_antisymm, le_map, mem_of_mem_nhds, mem_of_superset, mono_set
-/
theorem map_nhds_eq (hf : ApproximatesLinearOn f f' s c) (f'symm : f'.NonlinearRightInverse) {x : E}
    (hs : s in 𝓝 x) (hc : Subsingleton F ∨ c < f'symm.nnnorm⁻¹) : map f (𝓝 x) = 𝓝 (f x) := by
  refine
    le_antisymm ((hf.continuousOn x (mem_of_mem_nhds hs)).continuousAt hs) (le_map fun t ht => ?_)
  have : f '' (s inter t) in 𝓝 (f x) :=
    (hf.mono_set inter_subset_left).image_mem_nhds f'symm (inter_mem hs ht) hc
  exact mem_of_superset this (image_mono inter_subset_right)

end LocallyOnto

/-!
From now on we assume that `f` approximates an invertible continuous linear map `f : E ≃L[𝕜] F`.

We also assume that either `E = {0}`, or `c < ‖f'⁻¹‖⁻¹`. We use `N` as an abbreviation for `‖f'⁻¹‖`.
-/


variable {f' : E ≃L[𝕜] F} {s : Set E} {c : Real>=0}

local notation "N" => ‖(f'.symm : F ->L[𝕜] E)‖₊

/--
theorem `antilipschitz` / 定理 `antilipschitz`

English:
theorem antilipschitz
  statement: (hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) s c)
  proof: by
  rcases hc with hE | hc
  · exact AntilipschitzWith.of_subsingleton
  convert! (f'.antilipschitz.domRestrict s).add_lipschitzWith hf.lipschitz_sub hc
  simp [domRestrict]

中文:
定理 antilipschitz
  结论: (hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) s c)
  证明: by
  rcases hc with hE | hc
  · exact AntilipschitzWith.of_subsingleton
  convert! (f'.antilipschitz.domRestrict s).add_lipschitzWith hf.lipschitz_sub hc
  simp [domRestrict]
-/
protected theorem antilipschitz (hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) s c)
    (hc : Subsingleton E ∨ c < N⁻¹) : AntilipschitzWith (N⁻¹ - c)⁻¹ (s.domRestrict f) := by
  rcases hc with hE | hc
  · exact AntilipschitzWith.of_subsingleton
  convert! (f'.antilipschitz.domRestrict s).add_lipschitzWith hf.lipschitz_sub hc
  simp [domRestrict]

/--
theorem `injective` / 定理 `injective`

English:
theorem injective
  statement: (hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) s c)
  proof: (hf.antilipschitz hc).injective

中文:
定理 injective
  结论: (hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) s c)
  证明: (hf.antilipschitz hc).injective
-/
protected theorem injective (hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) s c)
    (hc : Subsingleton E ∨ c < N⁻¹) : Injective (s.domRestrict f) :=
  (hf.antilipschitz hc).injective

/--
theorem `injOn` / 定理 `injOn`

English:
theorem injOn
  statement: (hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) s c)
  proof: injOn_iff_injective.2 hf.injective hc

中文:
定理 injOn
  结论: (hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) s c)
  证明: injOn_iff_injective.2 hf.injective hc
-/
protected theorem injOn (hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) s c)
    (hc : Subsingleton E ∨ c < N⁻¹) : InjOn f s :=
injOn_iff_injective.2 hf.injective hc

/--
theorem `surjective` / 定理 `surjective`

English:
theorem surjective
  statement: [CompleteSpace E] (hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) univ c)
  proof: by
  rcases hc with hE | hc
  · have : Subsingleton F := (Equiv.subsingleton_congr f'.toEquiv).1 hE
    exact surjective_to_subsingleton _
  · apply forall_of_forall_mem_closedBall (fun y : F => exists a, f a = y) (f 0) _
    have hc' : (0 : Real) < N⁻¹ - c := by rw [sub_pos]; exact hc
    let p : R

中文:
定理 surjective
  结论: [CompleteSpace E] (hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) univ c)
  证明: by
  rcases hc with hE | hc
  · have : Subsingleton F := (Equiv.subsingleton_congr f'.toEquiv).1 hE
    exact surjective_to_subsingleton _
  · apply forall_of_forall_mem_closedBall (fun y : F => exists a, f a = y) (f 0) _
    have hc' : (0 : Real) < N⁻¹ - c := by rw [sub_pos]; exact hc
    let p : R
-/
protected theorem surjective [CompleteSpace E] (hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) univ c)
    (hc : Subsingleton E ∨ c < N⁻¹) : Surjective f := by
  rcases hc with hE | hc
  · have : Subsingleton F := (Equiv.subsingleton_congr f'.toEquiv).1 hE
    exact surjective_to_subsingleton _
  · apply forall_of_forall_mem_closedBall (fun y : F => exists a, f a = y) (f 0) _
    have hc' : (0 : Real) < N⁻¹ - c := by rw [sub_pos]; exact hc
    let p : Real -> Prop := fun R => closedBall (f 0) R subseteq Set.range f
    have hp : forallᶠ r : Real in atTop, p ((N⁻¹ - c) * r) := by
      have hr : forallᶠ r : Real in atTop, 0 <= r := eventually_ge_atTop 0
      refine hr.mono fun r hr => Subset.trans ?_ (image_subset_range f (closedBall 0 r))
      refine hf.surjOn_closedBall_of_nonlinearRightInverse f'.toNonlinearRightInverse hr ?_
      exact subset_univ _
    refine ((tendsto_id.const_mul_atTop hc').frequently hp.frequently).mono ?_
    exact fun R h y hy => h hy

/--
Definition of `toPartialEquiv` / `toPartialEquiv` 的定义

English:
definition toPartialEquiv
  signature: (hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) s c)
  body: (hf.injOn hc).toPartialEquiv _ _

中文:
定义 toPartialEquiv
  签名: (hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) s c)
  定义体: (hf.injOn hc).toPartialEquiv _ _

Depends on / 依赖: hf.injOn, toPartialEquiv
-/
def toPartialEquiv (hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) s c)
    (hc : Subsingleton E ∨ c < N⁻¹) : PartialEquiv E F :=
  (hf.injOn hc).toPartialEquiv _ _

/--
theorem `inverse_continuousOn` / 定理 `inverse_continuousOn`

English:
theorem inverse_continuousOn
  statement: (hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) s c)
  proof: by
  apply continuousOn_iff_continuous_domRestrict.2
  refine ((hf.antilipschitz hc).to_rightInvOn' ?_ (hf.toPartialEquiv hc).right_inv').continuous
  exact fun x hx => (hf.toPartialEquiv hc).map_target hx

中文:
定理 inverse_continuousOn
  结论: (hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) s c)
  证明: by
  apply continuousOn_iff_continuous_domRestrict.2
  refine ((hf.antilipschitz hc).to_rightInvOn' ?_ (hf.toPartialEquiv hc).right_inv').continuous
  exact fun x hx => (hf.toPartialEquiv hc).map_target hx

Depends on / 依赖: antilipschitz, continuous, continuousOn_iff_continuous_domRestrict, hf.antilipschitz, hf.toPartialEquiv, map_target, right_inv, toPartialEquiv, to_rightInvOn
-/
theorem inverse_continuousOn (hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) s c)
    (hc : Subsingleton E ∨ c < N⁻¹) : ContinuousOn (hf.toPartialEquiv hc).symm (f '' s) := by
  apply continuousOn_iff_continuous_domRestrict.2
  refine ((hf.antilipschitz hc).to_rightInvOn' ?_ (hf.toPartialEquiv hc).right_inv').continuous
  exact fun x hx => (hf.toPartialEquiv hc).map_target hx

/--
theorem `to_inv` / 定理 `to_inv`

English:
theorem to_inv
  given: (hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) s c) (hc : Subsingleton E ∨ c < N⁻¹)
  proof: fun x hx y hy => by
  set A := hf.toPartialEquiv hc
  have Af : forall z, A z = f z := fun z => rfl
  rcases (mem_image _ _ _).1 hx with ⟨x', x's, rfl⟩
  rcases (mem_image _ _ _).1 hy with ⟨y', y's, rfl⟩
  rw [← Af x']; rw [← Af y']; rw [A.left_inv x's]; rw [A.left_inv y's]
  calc
    ‖x' - y' - f'.

中文:
定理 to_inv
  条件: (hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) s c) (hc : Subsingleton E ∨ c < N⁻¹)
  证明: fun x hx y hy => by
  set A := hf.toPartialEquiv hc
  have Af : forall z, A z = f z := fun z => rfl
  rcases (mem_image _ _ _).1 hx with ⟨x', x's, rfl⟩
  rcases (mem_image _ _ _).1 hy with ⟨y', y's, rfl⟩
  rw [← Af x']; rw [← Af y']; rw [A.left_inv x's]; rw [A.left_inv y's]
  calc
    ‖x' - y' - f'.

Depends on / 依赖: A.left_inv, ContinuousLinearEquiv, ContinuousLinearEquiv.app, antilipschitz, bound_of_antilipschitz, hf.toPartialEquiv, left_inv, mem_image, toPartialEquiv
-/
theorem to_inv (hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) s c) (hc : Subsingleton E ∨ c < N⁻¹) :
    ApproximatesLinearOn (hf.toPartialEquiv hc).symm (f'.symm : F ->L[𝕜] E) (f '' s)
      (N * (N⁻¹ - c)⁻¹ * c) := fun x hx y hy => by
  set A := hf.toPartialEquiv hc
  have Af : forall z, A z = f z := fun z => rfl
  rcases (mem_image _ _ _).1 hx with ⟨x', x's, rfl⟩
  rcases (mem_image _ _ _).1 hy with ⟨y', y's, rfl⟩
  rw [← Af x']; rw [← Af y']; rw [A.left_inv x's]; rw [A.left_inv y's]
  calc
    ‖x' - y' - f'.symm (A x' - A y')‖ <= N * ‖f' (x' - y' - f'.symm (A x' - A y'))‖ :=
      (f' : E ->L[𝕜] F).bound_of_antilipschitz f'.antilipschitz _
    _ = N * ‖A y' - A x' - f' (y' - x')‖ := by
      congr 2
      simp only [ContinuousLinearEquiv.apply_symm_apply, map_sub]
      abel
    _ <= N * (c * ‖y' - x'‖) := by gcongr; exact hf _ y's _ x's
    _ <= N * (c * (((N⁻¹ - c)⁻¹ : Real>=0) * ‖A y' - A x'‖)) := by
      gcongr
      rw [← dist_eq_norm]; rw [← dist_eq_norm]
      exact (hf.antilipschitz hc).le_mul_dist ⟨y', y's⟩ ⟨x', x's⟩
    _ = (N * (N⁻¹ - c)⁻¹ * c : Real>=0) * ‖A x' - A y'‖ := by
      simp only [norm_sub_rev, NNReal.coe_mul]; ring

variable [CompleteSpace E]

section

variable (f s)

/--
Definition of `toOpenPartialHomeomorph` / `toOpenPartialHomeomorph` 的定义

English:
definition toOpenPartialHomeomorph
  signature: (hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) s c)
  body: hf.toPartialEquiv hc
  open_source := hs
open_target := hf.open_image f'.toNonlinearRightInverse hs by
    rwa [f'.toEquiv.subsingleton_congr] at hc
  continuousOn_toFun := hf.continuousOn
  continuousOn_invFun := hf.inverse_continuousOn hc

@[simp]

中文:
定义 toOpenPartialHomeomorph
  签名: (hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) s c)
  定义体: hf.toPartialEquiv hc
  open_source := hs
open_target := hf.open_image f'.toNonlinearRightInverse hs by
    rwa [f'.toEquiv.subsingleton_congr] at hc
  continuousOn_toFun := hf.continuousOn
  continuousOn_invFun := hf.inverse_continuousOn hc

@[simp]

Depends on / 依赖: hf.toPartialEquiv, toPartialEquiv
-/
def toOpenPartialHomeomorph (hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) s c)
    (hc : Subsingleton E ∨ c < N⁻¹) (hs : IsOpen s) : OpenPartialHomeomorph E F where
  toPartialEquiv := hf.toPartialEquiv hc
  open_source := hs
open_target := hf.open_image f'.toNonlinearRightInverse hs by
    rwa [f'.toEquiv.subsingleton_congr] at hc
  continuousOn_toFun := hf.continuousOn
  continuousOn_invFun := hf.inverse_continuousOn hc

@[simp]
/--
theorem `toOpenPartialHomeomorph_coe` / 定理 `toOpenPartialHomeomorph_coe`

English:
theorem toOpenPartialHomeomorph_coe
  statement: (hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) s c)
  proof: rfl

@[simp]

中文:
定理 toOpenPartialHomeomorph_coe
  结论: (hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) s c)
  证明: rfl

@[simp]

Depends on / 依赖: StrictConvexSpace, UniformConvexSpace, UniformConvexSpace.toStrictConvexSpace, toStrictConvexSpace
-/
theorem toOpenPartialHomeomorph_coe (hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) s c)
    (hc : Subsingleton E ∨ c < N⁻¹) (hs : IsOpen s) :
    (hf.toOpenPartialHomeomorph f s hc hs : E -> F) = f :=
  rfl

@[simp]
/--
theorem `toOpenPartialHomeomorph_source` / 定理 `toOpenPartialHomeomorph_source`

English:
theorem toOpenPartialHomeomorph_source
  statement: (hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) s c)
  proof: rfl

@[simp]

中文:
定理 toOpenPartialHomeomorph_source
  结论: (hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) s c)
  证明: rfl

@[simp]
-/
theorem toOpenPartialHomeomorph_source (hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) s c)
    (hc : Subsingleton E ∨ c < N⁻¹) (hs : IsOpen s) :
    (hf.toOpenPartialHomeomorph f s hc hs).source = s :=
  rfl

@[simp]
/--
theorem `toOpenPartialHomeomorph_target` / 定理 `toOpenPartialHomeomorph_target`

English:
theorem toOpenPartialHomeomorph_target
  statement: (hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) s c)
  proof: rfl

中文:
定理 toOpenPartialHomeomorph_target
  结论: (hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) s c)
  证明: rfl
-/
theorem toOpenPartialHomeomorph_target (hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) s c)
    (hc : Subsingleton E ∨ c < N⁻¹) (hs : IsOpen s) :
    (hf.toOpenPartialHomeomorph f s hc hs).target = f '' s :=
  rfl

/--
Definition of `toHomeomorph` / `toHomeomorph` 的定义

English:
definition toHomeomorph
  signature: (hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) univ c)
  body: by
  refine
    (hf.toOpenPartialHomeomorph _ _ hc isOpen_univ).toHomeomorphOfSourceEqUnivTargetEqUniv rfl ?_
  rw [toOpenPartialHomeomorph_target]; rw [image_univ]; rw [range_eq_univ]
  exact hf.surjective hc

中文:
定义 toHomeomorph
  签名: (hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) univ c)
  定义体: by
  refine
    (hf.toOpenPartialHomeomorph _ _ hc isOpen_univ).toHomeomorphOfSourceEqUnivTargetEqUniv rfl ?_
  rw [toOpenPartialHomeomorph_target]; rw [image_univ]; rw [range_eq_univ]
  exact hf.surjective hc

Depends on / 依赖: hf.surjective, hf.toOpenPartialHomeomorph, image_univ, isOpen_univ, range_eq_univ, surjective, toHomeomorphOfSourceEqUnivTargetEqUniv, toOpenPartialHomeomorph, toOpenPartialHomeomorph_target
-/
def toHomeomorph (hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) univ c)
    (hc : Subsingleton E ∨ c < N⁻¹) : E ≃ₜ F := by
  refine
    (hf.toOpenPartialHomeomorph _ _ hc isOpen_univ).toHomeomorphOfSourceEqUnivTargetEqUniv rfl ?_
  rw [toOpenPartialHomeomorph_target]; rw [image_univ]; rw [range_eq_univ]
  exact hf.surjective hc

end

/--
theorem `closedBall_subset_target` / 定理 `closedBall_subset_target`

English:
theorem closedBall_subset_target
  statement: (hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) s c)
  proof: (hf.surjOn_closedBall_of_nonlinearRightInverse f'.toNonlinearRightInverse ε0 hε).mono hε
    Subset.rfl

中文:
定理 closedBall_subset_target
  结论: (hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) s c)
  证明: (hf.surjOn_closedBall_of_nonlinearRightInverse f'.toNonlinearRightInverse ε0 hε).mono hε
    Subset.rfl

Depends on / 依赖: Subset, Subset.rfl, hf.surjOn_closedBall_of_nonlinearRightInverse, surjOn_closedBall_of_nonlinearRightInverse, toNonlinearRightInverse
-/
theorem closedBall_subset_target (hf : ApproximatesLinearOn f (f' : E ->L[𝕜] F) s c)
    (hc : Subsingleton E ∨ c < N⁻¹) (hs : IsOpen s) {b : E} (ε0 : 0 <= ε) (hε : closedBall b ε subseteq s) :
    closedBall (f b) ((N⁻¹ - c) * ε) subseteq (hf.toOpenPartialHomeomorph f s hc hs).target :=
  (hf.surjOn_closedBall_of_nonlinearRightInverse f'.toNonlinearRightInverse ε0 hε).mono hε
    Subset.rfl

end ApproximatesLinearOn
