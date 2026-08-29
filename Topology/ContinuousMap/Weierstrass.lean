/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# The Weierstrass approximation theorem for continuous functions on `[a,b]`

We've already proved the Weierstrass approximation theorem
in the sense that we've shown that the Bernstein approximations
to a continuous function on `[0,1]` converge uniformly.

Here we rephrase this more abstractly as
`polynomialFunctions_closure_eq_top' : (polynomialFunctions I).topologicalClosure = ⊤`
and then, by precomposing with suitable affine functions,
`polynomialFunctions_closure_eq_top : (polynomialFunctions (Set.Icc a b)).topologicalClosure = ⊤`
-/

public section


open ContinuousMap Filter

open scoped unitInterval

/--
theorem `polynomialFunctions_closure_eq_top'` / 定理 `polynomialFunctions_closure_eq_top'`

English:
theorem polynomialFunctions_closure_eq_top'
  statement: (polynomialFunctions I).topologicalClosure = ⊤
  proof: by
  apply top_unique
  rintro f -
refine mem_closure_of_tendsto (bernsteinApproximation_uniform f) .of_forall fun n => ?_
  apply Subalgebra.sum_mem
  rintro i -
  rw [← SetLike.mem_coe]; rw [polynomialFunctions_coe]
  use bernsteinPolynomial Real n i * .C (f (bernstein.z i))
  ext
  simp [bernstei

中文:
定理 polynomialFunctions_closure_eq_top'
  结论: (polynomialFunctions I).topologicalClosure = ⊤
  证明: by
  apply top_unique
  rintro f -
refine mem_closure_of_tendsto (bernsteinApproximation_uniform f) .of_forall fun n => ?_
  apply Subalgebra.sum_mem
  rintro i -
  rw [← SetLike.mem_coe]; rw [polynomialFunctions_coe]
  use bernsteinPolynomial Real n i * .C (f (bernstein.z i))
  ext
  simp [bernstei

Depends on / 依赖: SetLike, SetLike.mem_coe, Subalgebra, Subalgebra.sum_mem, bernstein, bernstein.z, bernsteinApproximation_uniform, bernsteinPolynomial, mem_closure_of_tendsto, mem_coe, of_forall, polynomialFunctions_coe, sum_mem, top_unique
-/
theorem polynomialFunctions_closure_eq_top' : (polynomialFunctions I).topologicalClosure = ⊤ := by
  apply top_unique
  rintro f -
refine mem_closure_of_tendsto (bernsteinApproximation_uniform f) .of_forall fun n => ?_
  apply Subalgebra.sum_mem
  rintro i -
  rw [← SetLike.mem_coe]; rw [polynomialFunctions_coe]
  use bernsteinPolynomial Real n i * .C (f (bernstein.z i))
  ext
  simp [bernstein]

/--
theorem `polynomialFunctions_closure_eq_top` / 定理 `polynomialFunctions_closure_eq_top`

English:
theorem polynomialFunctions_closure_eq_top
  given: (a b : Real)
  proof: by
  rcases lt_or_ge a b with h | h
  -- (Otherwise it's easy; we'll deal with that later.)
  · -- We can pullback continuous functions on `[a,b]` to continuous functions on `[0,1]`,
    -- by precomposing with an affine map.
    let W : C(Set.Icc a b, Real) ->ₐ[Real] C(I, Real) :=
      compRightAl

中文:
定理 polynomialFunctions_closure_eq_top
  条件: (a b : 实数)
  证明: by
  rcases lt_or_ge a b with h | h
  -- (Otherwise it's easy; we'll deal with that later.)
  · -- We can pullback continuous functions on `[a,b]` to continuous functions on `[0,1]`,
    -- by precomposing with an affine map.
    let W : C(Set.Icc a b, Real) ->ₐ[Real] C(I, Real) :=
      compRightAl

Depends on / 依赖: lt_or_ge
-/
theorem polynomialFunctions_closure_eq_top (a b : Real) :
    (polynomialFunctions (Set.Icc a b)).topologicalClosure = ⊤ := by
  rcases lt_or_ge a b with h | h
  -- (Otherwise it's easy; we'll deal with that later.)
  · -- We can pullback continuous functions on `[a,b]` to continuous functions on `[0,1]`,
    -- by precomposing with an affine map.
    let W : C(Set.Icc a b, Real) ->ₐ[Real] C(I, Real) :=
      compRightAlgHom Real Real (iccHomeoI a b h).symm
    -- This operation is itself a homeomorphism
    -- (with respect to the norm topologies on continuous functions).
    let W' : C(Set.Icc a b, Real) ≃ₜ C(I, Real) := (iccHomeoI a b h).arrowCongr (.refl _)
    have w : (W : C(Set.Icc a b, Real) -> C(I, Real)) = W' := rfl
    -- Thus we take the statement of the Weierstrass approximation theorem for `[0,1]`,
    have p := polynomialFunctions_closure_eq_top'
    -- and pullback both sides, obtaining an equation between subalgebras of `C([a,b], ℝ)`.
    apply_fun fun s => s.comap W at p
    simp only [Algebra.comap_top] at p
    -- Since the pullback operation is continuous, it commutes with taking `topologicalClosure`,
    rw [Subalgebra.topologicalClosure_comap_homeomorph _ W W' w] at p
    -- and precomposing with an affine map takes polynomial functions to polynomial functions.
    rw [polynomialFunctions.comap_compRightAlgHom_iccHomeoI] at p
    -- 🎉
    exact p
  · -- Otherwise, `b ≤ a`, and the interval is a subsingleton,
    subsingleton [(Set.subsingleton_Icc_of_ge h).coe_sort]

/--
theorem `continuousMap_mem_polynomialFunctions_closure` / 定理 `continuousMap_mem_polynomialFunctions_closure`

English:
theorem continuousMap_mem_polynomialFunctions_closure
  given: (a b : Real) (f : C(Set.Icc a b, Real))
  proof: by
  rw [polynomialFunctions_closure_eq_top _ _]
  simp

中文:
定理 continuousMap_mem_polynomialFunctions_closure
  条件: (a b : 实数) (f : C(集合.闭区间 a b, 实数))
  证明: by
  rw [polynomialFunctions_closure_eq_top _ _]
  simp

Depends on / 依赖: polynomialFunctions_closure_eq_top
-/
theorem continuousMap_mem_polynomialFunctions_closure (a b : Real) (f : C(Set.Icc a b, Real)) :
    f in (polynomialFunctions (Set.Icc a b)).topologicalClosure := by
  rw [polynomialFunctions_closure_eq_top _ _]
  simp

open scoped Polynomial

/--
theorem `exists_polynomial_near_continuousMap` / 定理 `exists_polynomial_near_continuousMap`

English:
theorem exists_polynomial_near_continuousMap
  statement: (a b : Real) (f : C(Set.Icc a b, Real)) (ε : Real)
  proof: by
  have w := mem_closure_iff_frequently.mp (continuousMap_mem_polynomialFunctions_closure _ _ f)
  rw [Metric.nhds_basis_ball.frequently_iff] at w
  obtain ⟨-, H, ⟨m, ⟨-, rfl⟩⟩⟩ := w ε pos
  rw [Metric.mem_ball]; rw [dist_eq_norm] at H
  exact ⟨m, H⟩

中文:
定理 存在_polynomial_near_continuousMap
  结论: (a b : 实数) (f : C(集合.闭区间 a b, 实数)) (ε : 实数)
  证明: by
  have w := mem_closure_iff_frequently.mp (continuousMap_mem_polynomialFunctions_closure _ _ f)
  rw [Metric.nhds_basis_ball.frequently_iff] at w
  obtain ⟨-, H, ⟨m, ⟨-, rfl⟩⟩⟩ := w ε pos
  rw [Metric.mem_ball]; rw [dist_eq_norm] at H
  exact ⟨m, H⟩

Depends on / 依赖: Metric, Metric.mem_ball, Metric.nhds_basis_ball.frequently_iff, continuousMap_mem_polynomialFunctions_closure, dist_eq_norm, frequently_iff, mem_ball, mem_closure_iff_frequently, mem_closure_iff_frequently.mp, nhds_basis_ball
-/
theorem exists_polynomial_near_continuousMap (a b : Real) (f : C(Set.Icc a b, Real)) (ε : Real)
    (pos : 0 < ε) : exists p : Real[X], ‖p.toContinuousMapOn _ - f‖ < ε := by
  have w := mem_closure_iff_frequently.mp (continuousMap_mem_polynomialFunctions_closure _ _ f)
  rw [Metric.nhds_basis_ball.frequently_iff] at w
  obtain ⟨-, H, ⟨m, ⟨-, rfl⟩⟩⟩ := w ε pos
  rw [Metric.mem_ball]; rw [dist_eq_norm] at H
  exact ⟨m, H⟩

/--
theorem `exists_polynomial_near_of_continuousOn` / 定理 `exists_polynomial_near_of_continuousOn`

English:
theorem exists_polynomial_near_of_continuousOn
  statement: (a b : Real) (f : Real -> Real)
  proof: by
  let f' : C(Set.Icc a b, Real) := ⟨fun x => f x, continuousOn_iff_continuous_domRestrict.mp c⟩
  obtain ⟨p, b⟩ := exists_polynomial_near_continuousMap a b f' ε pos
  use p
  rw [norm_lt_iff _ pos] at b
  intro x m
  exact b ⟨x, m⟩

中文:
定理 存在_polynomial_near_of_continuousOn
  结论: (a b : 实数) (f : 实数 -> 实数)
  证明: by
  let f' : C(Set.Icc a b, Real) := ⟨fun x => f x, continuousOn_iff_continuous_domRestrict.mp c⟩
  obtain ⟨p, b⟩ := exists_polynomial_near_continuousMap a b f' ε pos
  use p
  rw [norm_lt_iff _ pos] at b
  intro x m
  exact b ⟨x, m⟩

Depends on / 依赖: Set.Icc, continuousOn_iff_continuous_domRestrict, continuousOn_iff_continuous_domRestrict.mp, exists_polynomial_near_continuousMap, norm_lt_iff
-/
theorem exists_polynomial_near_of_continuousOn (a b : Real) (f : Real -> Real)
    (c : ContinuousOn f (Set.Icc a b)) (ε : Real) (pos : 0 < ε) :
    exists p : Real[X], forall x in Set.Icc a b, |p.eval x - f x| < ε := by
  let f' : C(Set.Icc a b, Real) := ⟨fun x => f x, continuousOn_iff_continuous_domRestrict.mp c⟩
  obtain ⟨p, b⟩ := exists_polynomial_near_continuousMap a b f' ε pos
  use p
  rw [norm_lt_iff _ pos] at b
  intro x m
  exact b ⟨x, m⟩
