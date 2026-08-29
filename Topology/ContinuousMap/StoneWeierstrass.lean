/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Heather Macbeth
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Tower
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.Algebra.Star.Real
public import Mathlib.Topology.Algebra.StarSubalgebra
public import Mathlib.Topology.Algebra.NonUnitalStarAlgebra
public import Mathlib.Topology.ContinuousMap.ContinuousMapZero
public import Mathlib.Topology.ContinuousMap.Lattice
public import Mathlib.Topology.ContinuousMap.Weierstrass
public import Mathlib.Algebra.Order.Module.Basic

/-!
# The Stone-Weierstrass theorem

If a subalgebra `A` of `C(X, ℝ)`, where `X` is a compact topological space,
separates points, then it is dense.

We argue as follows.

* In any subalgebra `A` of `C(X, ℝ)`, if `f ∈ A`, then `abs f ∈ A.topologicalClosure`.
  This follows from the Weierstrass approximation theorem on `[-‖f‖, ‖f‖]` by
  approximating `abs` uniformly thereon by polynomials.
* This ensures that `A.topologicalClosure` is actually a sublattice:
  if it contains `f` and `g`, then it contains the pointwise supremum `f ⊔ g`
  and the pointwise infimum `f ⊓ g`.
* Any nonempty sublattice `L` of `C(X, ℝ)` which separates points is dense,
  by a nice argument approximating a given `f` above and below using separating functions.
  For each `x y : X`, we pick a function `g x y ∈ L` so `g x y x = f x` and `g x y y = f y`.
  By continuity these functions remain close to `f` on small patches around `x` and `y`.
  We use compactness to identify a certain finitely indexed infimum of finitely indexed supremums
  which is then close to `f` everywhere, obtaining the desired approximation.
* Finally we put these pieces together. `L = A.topologicalClosure` is a nonempty sublattice
  which separates points since `A` does, and so is dense (in fact equal to `⊤`).

We then prove the complex version for star subalgebras `A`, by separately approximating
the real and imaginary parts using the real subalgebra of real-valued functions in `A`
(which still separates points, by taking the norm-square of a separating function).

## Future work

Extend to cover the case of subalgebras of the continuous functions vanishing at infinity,
on non-compact spaces.

-/

@[expose] public section

assert_not_exists Unitization

noncomputable section

namespace ContinuousMap

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

open scoped Polynomial

/--
Definition of `attachBound` / `attachBound` 的定义

English:
definition attachBound
  signature: (f : C(X, Real))
  body: ⟨f x, ⟨neg_norm_le_apply f x, apply_le_norm f x⟩⟩

@[simp]

中文:
定义 attachBound
  签名: (f : C(X, 实数))
  定义体: ⟨f x, ⟨neg_norm_le_apply f x, apply_le_norm f x⟩⟩

@[simp]

Depends on / 依赖: apply_le_norm, neg_norm_le_apply
-/
def attachBound (f : C(X, Real)) : C(X, Set.Icc (-‖f‖) ‖f‖) where
  toFun x := ⟨f x, ⟨neg_norm_le_apply f x, apply_le_norm f x⟩⟩

@[simp]
/--
theorem `attachBound_apply_coe` / 定理 `attachBound_apply_coe`

English:
theorem attachBound_apply_coe
  given: (f : C(X, Real)) (x : X)
  statement: ((attachBound f) x : Real) = f x
  proof: rfl

中文:
定理 attachBound_apply_coe
  条件: (f : C(X, 实数)) (x : X)
  结论: ((attachBound f) x : 实数) = f x
  证明: rfl
-/
theorem attachBound_apply_coe (f : C(X, Real)) (x : X) : ((attachBound f) x : Real) = f x :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `polynomial_comp_attachBound` / 定理 `polynomial_comp_attachBound`

English:
theorem polynomial_comp_attachBound
  given: (A : Subalgebra Real C(X, Real)) (f : A) (g : Real[X])
  proof: by
  ext
  simp only [Polynomial.aeval_subalgebra_coe, Polynomial.aeval_continuousMap_apply]
  simp

中文:
定理 polynomial_comp_attachBound
  条件: (A : 子代数 实数 C(X, 实数)) (f : A) (g : 实数[X])
  证明: by
  ext
  simp only [Polynomial.aeval_subalgebra_coe, Polynomial.aeval_continuousMap_apply]
  simp

Depends on / 依赖: Polynomial, Polynomial.aeval_continuousMap_apply, Polynomial.aeval_subalgebra_coe, aeval_continuousMap_apply, aeval_subalgebra_coe
-/
theorem polynomial_comp_attachBound (A : Subalgebra Real C(X, Real)) (f : A) (g : Real[X]) :
    (g.toContinuousMapOn (Set.Icc (-‖f‖) ‖f‖)).comp (f : C(X, Real)).attachBound =
      Polynomial.aeval f g := by
  ext
  simp only [Polynomial.aeval_subalgebra_coe, Polynomial.aeval_continuousMap_apply]
  simp

/--
theorem `polynomial_comp_attachBound_mem` / 定理 `polynomial_comp_attachBound_mem`

English:
theorem polynomial_comp_attachBound_mem
  given: (A : Subalgebra Real C(X, Real)) (f : A) (g : Real[X])
  proof: by
  rw [polynomial_comp_attachBound]
  apply SetLike.coe_mem

中文:
定理 polynomial_comp_attachBound_mem
  条件: (A : 子代数 实数 C(X, 实数)) (f : A) (g : 实数[X])
  证明: by
  rw [polynomial_comp_attachBound]
  apply SetLike.coe_mem

Depends on / 依赖: SetLike, SetLike.coe_mem, coe_mem, polynomial_comp_attachBound
-/
theorem polynomial_comp_attachBound_mem (A : Subalgebra Real C(X, Real)) (f : A) (g : Real[X]) :
    (g.toContinuousMapOn (Set.Icc (-‖f‖) ‖f‖)).comp (f : C(X, Real)).attachBound in A := by
  rw [polynomial_comp_attachBound]
  apply SetLike.coe_mem

/--
theorem `comp_attachBound_mem_closure` / 定理 `comp_attachBound_mem_closure`

English:
theorem comp_attachBound_mem_closure
  statement: (A : Subalgebra Real C(X, Real)) (f : A)
  proof: by
  -- `p` itself is in the closure of polynomials, by the Weierstrass theorem,
  have mem_closure : p in (polynomialFunctions (Set.Icc (-‖f‖) ‖f‖)).topologicalClosure :=
    continuousMap_mem_polynomialFunctions_closure _ _ p
  -- and so there are polynomials arbitrarily close.
  have frequently_m

中文:
定理 comp_attachBound_mem_closure
  结论: (A : 子代数 实数 C(X, 实数)) (f : A)
  证明: by
  -- `p` itself is in the closure of polynomials, by the Weierstrass theorem,
  have mem_closure : p in (polynomialFunctions (Set.Icc (-‖f‖) ‖f‖)).topologicalClosure :=
    continuousMap_mem_polynomialFunctions_closure _ _ p
  -- and so there are polynomials arbitrarily close.
  have frequently_m
-/
theorem comp_attachBound_mem_closure (A : Subalgebra Real C(X, Real)) (f : A)
    (p : C(Set.Icc (-‖f‖) ‖f‖, Real)) : p.comp (attachBound (f : C(X, Real))) in A.topologicalClosure := by
  -- `p` itself is in the closure of polynomials, by the Weierstrass theorem,
  have mem_closure : p in (polynomialFunctions (Set.Icc (-‖f‖) ‖f‖)).topologicalClosure :=
    continuousMap_mem_polynomialFunctions_closure _ _ p
  -- and so there are polynomials arbitrarily close.
  have frequently_mem_polynomials := mem_closure_iff_frequently.mp mem_closure
  -- To prove `p.comp (attachBound f)` is in the closure of `A`,
  -- we show there are elements of `A` arbitrarily close.
  apply mem_closure_iff_frequently.mpr
  -- To show that, we pull back the polynomials close to `p`,
  refine
    ((compRightContinuousMap Real (attachBound (f : C(X, Real)))).continuousAt
            p).tendsto.frequently_map
      _ ?_ frequently_mem_polynomials
  -- but need to show that those pullbacks are actually in `A`.
  rintro _ ⟨g, ⟨-, rfl⟩⟩
  simp only [SetLike.mem_coe, AlgHom.coe_toRingHom,
    Polynomial.toContinuousMapOnAlgHom_apply]
  apply polynomial_comp_attachBound_mem

/--
theorem `abs_mem_subalgebra_closure` / 定理 `abs_mem_subalgebra_closure`

English:
theorem abs_mem_subalgebra_closure
  given: (A : Subalgebra Real C(X, Real)) (f : A)
  proof: by
  let f' := attachBound (f : C(X, Real))
  let abs : C(Set.Icc (-‖f‖) ‖f‖, Real) := { toFun := fun x : Set.Icc (-‖f‖) ‖f‖ => |(x : Real)| }
  change abs.comp f' in A.topologicalClosure
  apply comp_attachBound_mem_closure

中文:
定理 abs_mem_subalgebra_closure
  条件: (A : 子代数 实数 C(X, 实数)) (f : A)
  证明: by
  let f' := attachBound (f : C(X, Real))
  let abs : C(Set.Icc (-‖f‖) ‖f‖, Real) := { toFun := fun x : Set.Icc (-‖f‖) ‖f‖ => |(x : Real)| }
  change abs.comp f' in A.topologicalClosure
  apply comp_attachBound_mem_closure

Depends on / 依赖: A.topologicalClosure, Set.Icc, abs.comp, attachBound, comp_attachBound_mem_closure, topologicalClosure
-/
theorem abs_mem_subalgebra_closure (A : Subalgebra Real C(X, Real)) (f : A) :
    |(f : C(X, Real))| in A.topologicalClosure := by
  let f' := attachBound (f : C(X, Real))
  let abs : C(Set.Icc (-‖f‖) ‖f‖, Real) := { toFun := fun x : Set.Icc (-‖f‖) ‖f‖ => |(x : Real)| }
  change abs.comp f' in A.topologicalClosure
  apply comp_attachBound_mem_closure

/--
theorem `inf_mem_subalgebra_closure` / 定理 `inf_mem_subalgebra_closure`

English:
theorem inf_mem_subalgebra_closure
  given: (A : Subalgebra Real C(X, Real)) (f g : A)
  proof: by
  rw [inf_eq_half_smul_add_sub_abs_sub' Real]
  refine
    A.topologicalClosure.smul_mem
      (A.topologicalClosure.sub_mem
        (A.topologicalClosure.add_mem (A.le_topologicalClosure f.property)
          (A.le_topologicalClosure g.property))
        ?_)
      _
  exact mod_cast abs_mem_suba

中文:
定理 inf_mem_subalgebra_closure
  条件: (A : 子代数 实数 C(X, 实数)) (f g : A)
  证明: by
  rw [inf_eq_half_smul_add_sub_abs_sub' Real]
  refine
    A.topologicalClosure.smul_mem
      (A.topologicalClosure.sub_mem
        (A.topologicalClosure.add_mem (A.le_topologicalClosure f.property)
          (A.le_topologicalClosure g.property))
        ?_)
      _
  exact mod_cast abs_mem_suba

Depends on / 依赖: A.le_topologicalClosure, A.topologicalClosure.add_mem, A.topologicalClosure.smul_mem, A.topologicalClosure.sub_mem, abs_mem_subalgebra_closure, add_mem, f.property, g.property, inf_eq_half_smul_add_sub_abs_sub, le_topologicalClosure, mod_cast, property, smul_mem, sub_mem, topologicalClosure
-/
theorem inf_mem_subalgebra_closure (A : Subalgebra Real C(X, Real)) (f g : A) :
    (f : C(X, Real)) ⊓ (g : C(X, Real)) in A.topologicalClosure := by
  rw [inf_eq_half_smul_add_sub_abs_sub' Real]
  refine
    A.topologicalClosure.smul_mem
      (A.topologicalClosure.sub_mem
        (A.topologicalClosure.add_mem (A.le_topologicalClosure f.property)
          (A.le_topologicalClosure g.property))
        ?_)
      _
  exact mod_cast abs_mem_subalgebra_closure A _

/--
theorem `inf_mem_closed_subalgebra` / 定理 `inf_mem_closed_subalgebra`

English:
theorem inf_mem_closed_subalgebra
  statement: (A : Subalgebra Real C(X, Real)) (h : IsClosed (A : Set C(X, Real)))
  proof: by
  convert! inf_mem_subalgebra_closure A f g
  apply SetLike.ext'
  symm
  rw [Subalgebra.topologicalClosure_coe]; rw [closure_eq_iff_isClosed]
  exact h

中文:
定理 inf_mem_closed_subalgebra
  结论: (A : 子代数 实数 C(X, 实数)) (h : 是闭集 (A : 集合 C(X, 实数)))
  证明: by
  convert! inf_mem_subalgebra_closure A f g
  apply SetLike.ext'
  symm
  rw [Subalgebra.topologicalClosure_coe]; rw [closure_eq_iff_isClosed]
  exact h

Depends on / 依赖: SetLike, SetLike.ext, Subalgebra, Subalgebra.topologicalClosure_coe, closure_eq_iff_isClosed, convert, inf_mem_subalgebra_closure, topologicalClosure_coe
-/
theorem inf_mem_closed_subalgebra (A : Subalgebra Real C(X, Real)) (h : IsClosed (A : Set C(X, Real)))
    (f g : A) : (f : C(X, Real)) ⊓ (g : C(X, Real)) in A := by
  convert! inf_mem_subalgebra_closure A f g
  apply SetLike.ext'
  symm
  rw [Subalgebra.topologicalClosure_coe]; rw [closure_eq_iff_isClosed]
  exact h

/--
theorem `sup_mem_subalgebra_closure` / 定理 `sup_mem_subalgebra_closure`

English:
theorem sup_mem_subalgebra_closure
  given: (A : Subalgebra Real C(X, Real)) (f g : A)
  proof: by
  rw [sup_eq_half_smul_add_add_abs_sub' Real]
  refine
    A.topologicalClosure.smul_mem
      (A.topologicalClosure.add_mem
        (A.topologicalClosure.add_mem (A.le_topologicalClosure f.property)
          (A.le_topologicalClosure g.property))
        ?_)
      _
  exact mod_cast abs_mem_suba

中文:
定理 sup_mem_subalgebra_closure
  条件: (A : 子代数 实数 C(X, 实数)) (f g : A)
  证明: by
  rw [sup_eq_half_smul_add_add_abs_sub' Real]
  refine
    A.topologicalClosure.smul_mem
      (A.topologicalClosure.add_mem
        (A.topologicalClosure.add_mem (A.le_topologicalClosure f.property)
          (A.le_topologicalClosure g.property))
        ?_)
      _
  exact mod_cast abs_mem_suba

Depends on / 依赖: A.le_topologicalClosure, A.topologicalClosure.add_mem, A.topologicalClosure.smul_mem, abs_mem_subalgebra_closure, add_mem, f.property, g.property, le_topologicalClosure, mod_cast, property, smul_mem, sup_eq_half_smul_add_add_abs_sub, topologicalClosure
-/
theorem sup_mem_subalgebra_closure (A : Subalgebra Real C(X, Real)) (f g : A) :
    (f : C(X, Real)) ⊔ (g : C(X, Real)) in A.topologicalClosure := by
  rw [sup_eq_half_smul_add_add_abs_sub' Real]
  refine
    A.topologicalClosure.smul_mem
      (A.topologicalClosure.add_mem
        (A.topologicalClosure.add_mem (A.le_topologicalClosure f.property)
          (A.le_topologicalClosure g.property))
        ?_)
      _
  exact mod_cast abs_mem_subalgebra_closure A _

/--
theorem `sup_mem_closed_subalgebra` / 定理 `sup_mem_closed_subalgebra`

English:
theorem sup_mem_closed_subalgebra
  statement: (A : Subalgebra Real C(X, Real)) (h : IsClosed (A : Set C(X, Real)))
  proof: by
  convert! sup_mem_subalgebra_closure A f g
  apply SetLike.ext'
  simp

中文:
定理 sup_mem_closed_subalgebra
  结论: (A : 子代数 实数 C(X, 实数)) (h : 是闭集 (A : 集合 C(X, 实数)))
  证明: by
  convert! sup_mem_subalgebra_closure A f g
  apply SetLike.ext'
  simp

Depends on / 依赖: SetLike, SetLike.ext, convert, sup_mem_subalgebra_closure
-/
theorem sup_mem_closed_subalgebra (A : Subalgebra Real C(X, Real)) (h : IsClosed (A : Set C(X, Real)))
    (f g : A) : (f : C(X, Real)) ⊔ (g : C(X, Real)) in A := by
  convert! sup_mem_subalgebra_closure A f g
  apply SetLike.ext'
  simp

open scoped Topology

-- Here's the fun part of Stone-Weierstrass!
/--
theorem `sublattice_closure_eq_top` / 定理 `sublattice_closure_eq_top`

English:
theorem sublattice_closure_eq_top
  statement: (L : Set C(X, Real)) (nA : L.Nonempty)
  proof: by
  -- We start by boiling down to a statement about close approximation.
  rw [eq_top_iff]
  rintro f -
  refine
    Filter.Frequently.mem_closure
      ((Filter.HasBasis.frequently_iff Metric.nhds_basis_ball).mpr fun ε pos => ?_)
  simp only [Metric.mem_ball]
  -- It will be helpful to assume `X`

中文:
定理 sublattice_closure_eq_top
  结论: (L : 集合 C(X, 实数)) (nA : L.非空)
  证明: by
  -- We start by boiling down to a statement about close approximation.
  rw [eq_top_iff]
  rintro f -
  refine
    Filter.Frequently.mem_closure
      ((Filter.HasBasis.frequently_iff Metric.nhds_basis_ball).mpr fun ε pos => ?_)
  simp only [Metric.mem_ball]
  -- It will be helpful to assume `X`
-/
theorem sublattice_closure_eq_top (L : Set C(X, Real)) (nA : L.Nonempty)
    (inf_mem : forallᵉ (f in L) (g in L), f ⊓ g in L)
    (sup_mem : forallᵉ (f in L) (g in L), f ⊔ g in L) (sep : L.SeparatesPointsStrongly) :
    closure L = ⊤ := by
  -- We start by boiling down to a statement about close approximation.
  rw [eq_top_iff]
  rintro f -
  refine
    Filter.Frequently.mem_closure
      ((Filter.HasBasis.frequently_iff Metric.nhds_basis_ball).mpr fun ε pos => ?_)
  simp only [Metric.mem_ball]
  -- It will be helpful to assume `X` is nonempty later,
  -- so we get that out of the way here.
  by_cases nX : Nonempty X
  swap
  · exact ⟨nA.some, (dist_lt_iff pos).mpr fun x => False.elim (nX ⟨x⟩), nA.choose_spec⟩
  /-
    The strategy now is to pick a family of continuous functions `g x y` in `A`
    with the property that `g x y x = f x` and `g x y y = f y`
    (this is immediate from `h : SeparatesPointsStrongly`)
    then use continuity to see that `g x y` is close to `f` near both `x` and `y`,
    and finally using compactness to produce the desired function `h`
    as a maximum over finitely many `x` of a minimum over finitely many `y` of the `g x y`.
    -/
  dsimp only [Set.SeparatesPointsStrongly] at sep
  choose g hg w₁ w₂ using sep f
  -- For each `x y`, we define `U x y` to be `{z | f z - ε < g x y z}`,
  -- and observe this is a neighbourhood of `y`.
  let U : X -> X -> Set X := fun x y => {z | f z - ε < g x y z}
  have U_nhds_y : forall x y, U x y in 𝓝 y := by
    intro x y
    refine IsOpen.mem_nhds ?_ ?_
    · apply isOpen_lt <;> fun_prop
    · rw [Set.mem_ofPred_eq, w₂]
      exact sub_lt_self _ pos
  -- Fixing `x` for a moment, we have a family of functions `fun y ↦ g x y`
  -- which on different patches (the `U x y`) are greater than `f z - ε`.
  -- Taking the supremum of these functions
  -- indexed by a finite collection of patches which cover `X`
  -- will give us an element of `A` that is globally greater than `f z - ε`
  -- and still equal to `f x` at `x`.
  -- Since `X` is compact, for every `x` there is some finset `ys t`
  -- so the union of the `U x y` for `y ∈ ys x` still covers everything.
  let ys : X -> Finset X := fun x => (CompactSpace.elim_nhds_subcover (U x) (U_nhds_y x)).choose
  let ys_w : forall x, ⋃ y in ys x, U x y = ⊤ := fun x =>
    (CompactSpace.elim_nhds_subcover (U x) (U_nhds_y x)).choose_spec
  have ys_nonempty : forall x, (ys x).Nonempty := fun x =>
    Set.nonempty_of_union_eq_top_of_nonempty _ _ nX (ys_w x)
  -- Thus for each `x` we have the desired `h x : A` so `f z - ε < h x z` everywhere
  -- and `h x x = f x`.
  let h : X -> L := fun x =>
    ⟨(ys x).sup' (ys_nonempty x) fun y => (g x y : C(X, Real)),
      Finset.sup'_mem _ sup_mem _ _ _ fun y _ => hg x y⟩
  have lt_h : forall x z, f z - ε < (h x : X -> Real) z := by
    intro x z
    obtain ⟨y, ym, zm⟩ := Set.exists_set_mem_of_union_eq_top _ _ (ys_w x) z
    dsimp [h]
    simp only [coe_sup', Finset.sup'_apply, Finset.lt_sup'_iff]
    exact ⟨y, ym, zm⟩
  have h_eq : forall x, (h x : X -> Real) x = f x := by intro x; simp [h, w₁]
  -- For each `x`, we define `W x` to be `{z | h x z < f z + ε}`,
  let W : X -> Set X := fun x => {z | (h x : X -> Real) z < f z + ε}
  -- This is still a neighbourhood of `x`.
  have W_nhds : forall x, W x in 𝓝 x := by
    intro x
    refine IsOpen.mem_nhds ?_ ?_
    · apply isOpen_lt <;> fun_prop
    · dsimp only [W, Set.mem_ofPred_eq]
      rw [h_eq]
      exact lt_add_of_pos_right _ pos
  -- Since `X` is compact, there is some finset `ys t`
  -- so the union of the `W x` for `x ∈ xs` still covers everything.
  let xs : Finset X := (CompactSpace.elim_nhds_subcover W W_nhds).choose
  let xs_w : ⋃ x in xs, W x = ⊤ := (CompactSpace.elim_nhds_subcover W W_nhds).choose_spec
  have xs_nonempty : xs.Nonempty := Set.nonempty_of_union_eq_top_of_nonempty _ _ nX xs_w
  -- Finally our candidate function is the infimum over `x ∈ xs` of the `h x`.
  -- This function is then globally less than `f z + ε`.
  let k : (L : Type _) :=
    ⟨xs.inf' xs_nonempty fun x => (h x : C(X, Real)),
      Finset.inf'_mem _ inf_mem _ _ _ fun x _ => (h x).2⟩
  refine ⟨k.1, ?_, k.2⟩
  -- We just need to verify the bound, which we do pointwise.
  rw [dist_lt_iff pos]
  intro z
  -- We rewrite into this particular form,
  -- so that simp lemmas about inequalities involving `Finset.inf'` can fire.
  rw [show forall a b ε : Real]; rw [dist a b < ε ↔ a < b + ε ∧ b - ε < a by
        intros; simp only [← Metric.mem_ball]; rw [Real.ball_eq_Ioo]; rw [Set.mem_Ioo]; rw [and_comm]]
  constructor
  · simp only [k, Finset.inf'_lt_iff, ContinuousMap.inf'_apply]
    exact Set.exists_set_mem_of_union_eq_top _ _ xs_w z
  · simp only [k, Finset.lt_inf'_iff, ContinuousMap.inf'_apply]
    rintro x -
    apply lt_h

/-- The **Stone-Weierstrass Approximation Theorem**,
that a subalgebra `A` of `C(X, ℝ)`, where `X` is a compact topological space,
is dense if it separates points.
-/
@[wikidata Q939927]
/--
theorem `subalgebra_topologicalClosure_eq_top_of_separatesPoints` / 定理 `subalgebra_topologicalClosure_eq_top_of_separatesPoints`

English:
theorem subalgebra_topologicalClosure_eq_top_of_separatesPoints
  statement: (A : Subalgebra Real C(X, Real))
  proof: by
  -- The closure of `A` is closed under taking `sup` and `inf`,
  -- and separates points strongly (since `A` does),
  -- so we can apply `sublattice_closure_eq_top`.
  apply SetLike.ext'
  let L := A.topologicalClosure
  have n : Set.Nonempty (L : Set C(X, Real)) := ⟨(1 : C(X, Real)), A.le_topol

中文:
定理 subalgebra_topologicalClosure_eq_top_of_separatesPoints
  结论: (A : 子代数 实数 C(X, 实数))
  证明: by
  -- The closure of `A` is closed under taking `sup` and `inf`,
  -- and separates points strongly (since `A` does),
  -- so we can apply `sublattice_closure_eq_top`.
  apply SetLike.ext'
  let L := A.topologicalClosure
  have n : Set.Nonempty (L : Set C(X, Real)) := ⟨(1 : C(X, Real)), A.le_topol
-/
theorem subalgebra_topologicalClosure_eq_top_of_separatesPoints (A : Subalgebra Real C(X, Real))
    (w : A.SeparatesPoints) : A.topologicalClosure = ⊤ := by
  -- The closure of `A` is closed under taking `sup` and `inf`,
  -- and separates points strongly (since `A` does),
  -- so we can apply `sublattice_closure_eq_top`.
  apply SetLike.ext'
  let L := A.topologicalClosure
  have n : Set.Nonempty (L : Set C(X, Real)) := ⟨(1 : C(X, Real)), A.le_topologicalClosure A.one_mem⟩
  convert!
    sublattice_closure_eq_top (L : Set C(X, Real)) n
      (fun f fm g gm => inf_mem_closed_subalgebra L A.isClosed_topologicalClosure ⟨f, fm⟩ ⟨g, gm⟩)
      (fun f fm g gm => sup_mem_closed_subalgebra L A.isClosed_topologicalClosure ⟨f, fm⟩ ⟨g, gm⟩)
      (Subalgebra.SeparatesPoints.strongly
        (Subalgebra.separatesPoints_monotone A.le_topologicalClosure w))
  simp [L]

/--
theorem `continuousMap_mem_subalgebra_closure_of_separatesPoints` / 定理 `continuousMap_mem_subalgebra_closure_of_separatesPoints`

English:
theorem continuousMap_mem_subalgebra_closure_of_separatesPoints
  statement: (A : Subalgebra Real C(X, Real))
  proof: by
  rw [subalgebra_topologicalClosure_eq_top_of_separatesPoints A w]
  simp

中文:
定理 continuousMap_mem_subalgebra_closure_of_separatesPoints
  结论: (A : 子代数 实数 C(X, 实数))
  证明: by
  rw [subalgebra_topologicalClosure_eq_top_of_separatesPoints A w]
  simp

Depends on / 依赖: subalgebra_topologicalClosure_eq_top_of_separatesPoints
-/
theorem continuousMap_mem_subalgebra_closure_of_separatesPoints (A : Subalgebra Real C(X, Real))
    (w : A.SeparatesPoints) (f : C(X, Real)) : f in A.topologicalClosure := by
  rw [subalgebra_topologicalClosure_eq_top_of_separatesPoints A w]
  simp

/--
theorem `exists_mem_subalgebra_near_continuousMap_of_separatesPoints` / 定理 `exists_mem_subalgebra_near_continuousMap_of_separatesPoints`

English:
theorem exists_mem_subalgebra_near_continuousMap_of_separatesPoints
  statement: (A : Subalgebra Real C(X, Real))
  proof: by
  have w :=
    mem_closure_iff_frequently.mp (continuousMap_mem_subalgebra_closure_of_separatesPoints A w f)
  rw [Metric.nhds_basis_ball.frequently_iff] at w
  obtain ⟨g, H, m⟩ := w ε pos
  rw [Metric.mem_ball]; rw [dist_eq_norm] at H
  exact ⟨⟨g, m⟩, H⟩

中文:
定理 存在_mem_subalgebra_near_continuousMap_of_separatesPoints
  结论: (A : 子代数 实数 C(X, 实数))
  证明: by
  have w :=
    mem_closure_iff_frequently.mp (continuousMap_mem_subalgebra_closure_of_separatesPoints A w f)
  rw [Metric.nhds_basis_ball.frequently_iff] at w
  obtain ⟨g, H, m⟩ := w ε pos
  rw [Metric.mem_ball]; rw [dist_eq_norm] at H
  exact ⟨⟨g, m⟩, H⟩

Depends on / 依赖: Metric, Metric.mem_ball, Metric.nhds_basis_ball.frequently_iff, continuousMap_mem_subalgebra_closure_of_separatesPoints, dist_eq_norm, frequently_iff, mem_ball, mem_closure_iff_frequently, mem_closure_iff_frequently.mp, nhds_basis_ball
-/
theorem exists_mem_subalgebra_near_continuousMap_of_separatesPoints (A : Subalgebra Real C(X, Real))
    (w : A.SeparatesPoints) (f : C(X, Real)) (ε : Real) (pos : 0 < ε) :
    exists g : A, ‖(g : C(X, Real)) - f‖ < ε := by
  have w :=
    mem_closure_iff_frequently.mp (continuousMap_mem_subalgebra_closure_of_separatesPoints A w f)
  rw [Metric.nhds_basis_ball.frequently_iff] at w
  obtain ⟨g, H, m⟩ := w ε pos
  rw [Metric.mem_ball]; rw [dist_eq_norm] at H
  exact ⟨⟨g, m⟩, H⟩

/--
theorem `exists_mem_subalgebra_near_continuous_of_separatesPoints` / 定理 `exists_mem_subalgebra_near_continuous_of_separatesPoints`

English:
theorem exists_mem_subalgebra_near_continuous_of_separatesPoints
  statement: (A : Subalgebra Real C(X, Real))
  proof: by
  obtain ⟨g, b⟩ := exists_mem_subalgebra_near_continuousMap_of_separatesPoints A w ⟨f, c⟩ ε pos
  use g
  rwa [norm_lt_iff _ pos] at b

中文:
定理 存在_mem_subalgebra_near_continuous_of_separatesPoints
  结论: (A : 子代数 实数 C(X, 实数))
  证明: by
  obtain ⟨g, b⟩ := exists_mem_subalgebra_near_continuousMap_of_separatesPoints A w ⟨f, c⟩ ε pos
  use g
  rwa [norm_lt_iff _ pos] at b

Depends on / 依赖: exists_mem_subalgebra_near_continuousMap_of_separatesPoints, norm_lt_iff
-/
theorem exists_mem_subalgebra_near_continuous_of_separatesPoints (A : Subalgebra Real C(X, Real))
    (w : A.SeparatesPoints) (f : X -> Real) (c : Continuous f) (ε : Real) (pos : 0 < ε) :
    exists g : A, forall x, ‖(g : X -> Real) x - f x‖ < ε := by
  obtain ⟨g, b⟩ := exists_mem_subalgebra_near_continuousMap_of_separatesPoints A w ⟨f, c⟩ ε pos
  use g
  rwa [norm_lt_iff _ pos] at b

/--
theorem `exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints` / 定理 `exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints`

English:
theorem exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
  proof: by
  let restrict_on_K : C(X, Real) ->⋆ₐ[Real] C(K, Real) :=
    ContinuousMap.compStarAlgHom' Real Real ⟨(Subtype.val), continuous_subtype_val⟩
  --consider the subalgebra AK of functions with domain K
  let AK : Subalgebra Real C(K, Real) := Subalgebra.map restrict_on_K A
  have hsep : AK.Separate

中文:
定理 存在_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
  证明: by
  let restrict_on_K : C(X, Real) ->⋆ₐ[Real] C(K, Real) :=
    ContinuousMap.compStarAlgHom' Real Real ⟨(Subtype.val), continuous_subtype_val⟩
  --consider the subalgebra AK of functions with domain K
  let AK : Subalgebra Real C(K, Real) := Subalgebra.map restrict_on_K A
  have hsep : AK.Separate

Depends on / 依赖: ContinuousMap, ContinuousMap.compStarAlgHom, Subtype, Subtype.val, compStarAlgHom, continuous_subtype_val, restrict_on_K
-/
theorem exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
    {X : Type*} [TopologicalSpace X] {A : Subalgebra Real C(X, Real)} (hA : A.SeparatesPoints)
    (f : C(X, Real)) {K : Set X} (hK : IsCompact K) {ε : Real} (pos : 0 < ε) :
    exists g in A, forall x in K, ‖(g : X -> Real) x - f x‖ < ε := by
  let restrict_on_K : C(X, Real) ->⋆ₐ[Real] C(K, Real) :=
    ContinuousMap.compStarAlgHom' Real Real ⟨(Subtype.val), continuous_subtype_val⟩
  --consider the subalgebra AK of functions with domain K
  let AK : Subalgebra Real C(K, Real) := Subalgebra.map restrict_on_K A
  have hsep : AK.SeparatesPoints := by
    intro x y hxy
    obtain ⟨_, ⟨g, hg1, hg2⟩, hg_sep⟩ := hA (Subtype.coe_ne_coe.mpr hxy)
    simp only [Set.mem_image, SetLike.mem_coe, exists_exists_and_eq_and]
    use restrict_on_K g
    refine ⟨Subalgebra.mem_map.mpr ?_,
      by simpa only [compStarAlgHom'_apply, comp_apply, coe_mk, ne_eq, restrict_on_K, hg2]⟩
    use g, hg1
    simp
  obtain ⟨⟨gK, hgKAK⟩, hgapprox⟩ :=
    @ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints _ _
    (isCompact_iff_compactSpace.mp hK) AK hsep (K.domRestrict f)
    (ContinuousOn.domRestrict (Continuous.continuousOn f.continuous)) ε pos
  obtain ⟨g, hgA, hgKAK⟩ := Subalgebra.mem_map.mp hgKAK
  use g, hgA
  intro x hxK
  have eqg : g x = gK ⟨x, hxK⟩ := by
    rw [← hgKAK]; rfl
  rw [eqg]
  exact hgapprox ⟨x, hxK⟩

end ContinuousMap

section RCLike

open RCLike

-- Redefine `X`, since for the next lemma it need not be compact
variable {𝕜 : Type*} {X : Type*} [RCLike 𝕜] [TopologicalSpace X]

open ContinuousMap

/- a post-port refactor eliminated `conjInvariantSubalgebra`, which was only used to
state and prove the Stone-Weierstrass theorem, in favor of using `StarSubalgebra`s,
which didn't exist at the time Stone-Weierstrass was written. -/


set_option backward.isDefEq.respectTransparency false in
/--
theorem `Subalgebra.SeparatesPoints.rclike_to_real` / 定理 `Subalgebra.SeparatesPoints.rclike_to_real`

English:
theorem Subalgebra.SeparatesPoints.rclike_to_real
  statement: {A : StarSubalgebra 𝕜 C(X, 𝕜)}
  proof: by
  intro x₁ x₂ hx
  -- Let `f` in the subalgebra `A` separate the points `x₁`, `x₂`
  obtain ⟨_, ⟨f, hfA, rfl⟩, hf⟩ := hA hx
  let F : C(X, 𝕜) := f - const _ (f x₂)
  -- Subtract the constant `f x₂` from `f`; this is still an element of the subalgebra
  have hFA : F in A := by
    refine A.sub_mem

中文:
定理 子代数.SeparatesPoints.rclike_to_real
  结论: {A : 对合子代数 𝕜 C(X, 𝕜)}
  证明: by
  intro x₁ x₂ hx
  -- Let `f` in the subalgebra `A` separate the points `x₁`, `x₂`
  obtain ⟨_, ⟨f, hfA, rfl⟩, hf⟩ := hA hx
  let F : C(X, 𝕜) := f - const _ (f x₂)
  -- Subtract the constant `f x₂` from `f`; this is still an element of the subalgebra
  have hFA : F in A := by
    refine A.sub_mem
-/
theorem Subalgebra.SeparatesPoints.rclike_to_real {A : StarSubalgebra 𝕜 C(X, 𝕜)}
    (hA : A.SeparatesPoints) :
      ((A.restrictScalars Real).comap
        (ofRealAm.compLeftContinuous Real continuous_ofReal)).SeparatesPoints := by
  intro x₁ x₂ hx
  -- Let `f` in the subalgebra `A` separate the points `x₁`, `x₂`
  obtain ⟨_, ⟨f, hfA, rfl⟩, hf⟩ := hA hx
  let F : C(X, 𝕜) := f - const _ (f x₂)
  -- Subtract the constant `f x₂` from `f`; this is still an element of the subalgebra
  have hFA : F in A := by
    refine A.sub_mem hfA (@Eq.subst _ (· in A) _ _ ?_ <| A.smul_mem A.one_mem <| f x₂)
    ext1
    simp only [ContinuousMap.smul_apply, one_apply, smul_eq_mul, mul_one,
      const_apply]
  -- Consider now the function `fun x ↦ |f x - f x₂| ^ 2`
  refine ⟨_, ⟨⟨(‖F ·‖ ^ 2), by fun_prop⟩, ?_, rfl⟩, ?_⟩
  · -- This is also an element of the subalgebra, and takes only real values
    rw [SetLike.mem_coe]; rw [Subalgebra.mem_comap]
    convert! (A.restrictScalars Real).mul_mem hFA (star_mem hFA : star F in A)
    ext1
    simp [← RCLike.mul_conj]
  · -- And it also separates the points `x₁`, `x₂`
    simpa [F] using sub_ne_zero.mpr hf

variable [CompactSpace X]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints` / 定理 `ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints`

English:
theorem ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
  proof: by
  rw [StarSubalgebra.eq_top_iff]
  -- Let `I` be the natural inclusion of `C(X, ℝ)` into `C(X, 𝕜)`
  let I : C(X, Real) ->L[Real] C(X, 𝕜) := ofRealCLM.compLeftContinuous Real X
  -- The main point of the proof is that its range (i.e., every real-valued function) is contained
  -- in the closure o

中文:
定理 连续映射.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
  证明: by
  rw [StarSubalgebra.eq_top_iff]
  -- Let `I` be the natural inclusion of `C(X, ℝ)` into `C(X, 𝕜)`
  let I : C(X, Real) ->L[Real] C(X, 𝕜) := ofRealCLM.compLeftContinuous Real X
  -- The main point of the proof is that its range (i.e., every real-valued function) is contained
  -- in the closure o

Depends on / 依赖: StarSubalgebra, StarSubalgebra.eq_top_iff, eq_top_iff
-/
theorem ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    (A : StarSubalgebra 𝕜 C(X, 𝕜)) (hA : A.SeparatesPoints) : A.topologicalClosure = ⊤ := by
  rw [StarSubalgebra.eq_top_iff]
  -- Let `I` be the natural inclusion of `C(X, ℝ)` into `C(X, 𝕜)`
  let I : C(X, Real) ->L[Real] C(X, 𝕜) := ofRealCLM.compLeftContinuous Real X
  -- The main point of the proof is that its range (i.e., every real-valued function) is contained
  -- in the closure of `A`
  have key : I.range <= (A.toSubmodule.restrictScalars Real).topologicalClosure := by
    -- Let `A₀` be the subalgebra of `C(X, ℝ)` consisting of `A`'s purely real elements; it is the
    -- preimage of `A` under `I`. In this argument we only need its submodule structure.
    let A₀ : Submodule Real C(X, Real) := (A.toSubmodule.restrictScalars Real).comap I.toLinearMap
    -- By `Subalgebra.SeparatesPoints.rclike_to_real`, this subalgebra also separates points, so
    -- we may apply the real Stone-Weierstrass result to it.
    have SW : A₀.topologicalClosure = ⊤ :=
      haveI := subalgebra_topologicalClosure_eq_top_of_separatesPoints _ hA.rclike_to_real
      congr_arg Subalgebra.toSubmodule this
    rw [← Submodule.map_top]; rw [← SW]
    -- So it suffices to prove that the image under `I` of the closure of `A₀` is contained in the
    -- closure of `A`, which follows by abstract nonsense
    have h₁ := A₀.topologicalClosure_map I
    have h₂ := (A.toSubmodule.restrictScalars Real).map_comap_le I.toLinearMap
    exact h₁.trans (Submodule.topologicalClosure_mono h₂)
  -- In particular, for a function `f` in `C(X, 𝕜)`, the real and imaginary parts of `f` are in the
  -- closure of `A`
  intro f
  let f_re : C(X, Real) := (⟨RCLike.re, RCLike.reCLM.continuous⟩ : C(𝕜, Real)).comp f
  let f_im : C(X, Real) := (⟨RCLike.im, RCLike.imCLM.continuous⟩ : C(𝕜, Real)).comp f
  have h_f_re : I f_re in A.topologicalClosure := key ⟨f_re, rfl⟩
  have h_f_im : I f_im in A.topologicalClosure := key ⟨f_im, rfl⟩
  -- So `f_re + I • f_im` is in the closure of `A`
  have := A.topologicalClosure.add_mem h_f_re (A.topologicalClosure.smul_mem h_f_im RCLike.I)
  rw [StarSubalgebra.mem_toSubalgebra] at this
  convert! this
  -- And this, of course, is just `f`
  ext
  apply Eq.symm
  simp [I, f_re, f_im, mul_comm RCLike.I _]

end RCLike

section PolynomialFunctions

open StarSubalgebra Polynomial
open scoped Polynomial

/--
theorem `polynomialFunctions.topologicalClosure` / 定理 `polynomialFunctions.topologicalClosure`

English:
theorem polynomialFunctions.topologicalClosure
  statement: (s : Set Real)
  proof: ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints _
    (polynomialFunctions_separatesPoints s)

中文:
定理 polynomialFunctions.topologicalClosure
  结论: (s : 集合 实数)
  证明: ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints _
    (polynomialFunctions_separatesPoints s)

Depends on / 依赖: ContinuousMap, ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints, polynomialFunctions_separatesPoints, subalgebra_topologicalClosure_eq_top_of_separatesPoints
-/
theorem polynomialFunctions.topologicalClosure (s : Set Real)
    [CompactSpace s] : (polynomialFunctions s).topologicalClosure = ⊤ :=
  ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints _
    (polynomialFunctions_separatesPoints s)

/--
theorem `polynomialFunctions.starClosure_topologicalClosure` / 定理 `polynomialFunctions.starClosure_topologicalClosure`

English:
theorem polynomialFunctions.starClosure_topologicalClosure
  statement: {𝕜 : Type*} [RCLike 𝕜] (s : Set 𝕜)
  proof: ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _
    (Subalgebra.separatesPoints_monotone le_sup_left (polynomialFunctions_separatesPoints s))

中文:
定理 polynomialFunctions.starClosure_topologicalClosure
  结论: {𝕜 : 类型} [RCLike 𝕜] (s : 集合 𝕜)
  证明: ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _
    (Subalgebra.separatesPoints_monotone le_sup_left (polynomialFunctions_separatesPoints s))

Depends on / 依赖: ContinuousMap, ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints, Subalgebra, Subalgebra.separatesPoints_monotone, le_sup_left, polynomialFunctions_separatesPoints, separatesPoints_monotone, starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
-/
theorem polynomialFunctions.starClosure_topologicalClosure {𝕜 : Type*} [RCLike 𝕜] (s : Set 𝕜)
    [CompactSpace s] : (polynomialFunctions s).starClosure.topologicalClosure = ⊤ :=
  ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _
    (Subalgebra.separatesPoints_monotone le_sup_left (polynomialFunctions_separatesPoints s))

open StarAlgebra in
/--
lemma `ContinuousMap.elemental_id_eq_top` / 引理 `ContinuousMap.elemental_id_eq_top`

English:
lemma ContinuousMap.elemental_id_eq_top
  given: {𝕜 : Type*} [RCLike 𝕜] (s : Set 𝕜) [CompactSpace s]
  proof: by
  rw [StarAlgebra.elemental]; rw [← polynomialFunctions.starClosure_topologicalClosure]; rw [polynomialFunctions.starClosure_eq_adjoin_X]
  congr
  exact Polynomial.toContinuousMap_X_eq_id.symm

中文:
引理 连续映射.elemental_id_eq_top
  条件: {𝕜 : 类型} [RCLike 𝕜] (s : 集合 𝕜) [紧空间 s]
  证明: by
  rw [StarAlgebra.elemental]; rw [← polynomialFunctions.starClosure_topologicalClosure]; rw [polynomialFunctions.starClosure_eq_adjoin_X]
  congr
  exact Polynomial.toContinuousMap_X_eq_id.symm

Depends on / 依赖: Polynomial, Polynomial.toContinuousMap_X_eq_id.symm, StarAlgebra, StarAlgebra.elemental, elemental, polynomialFunctions, polynomialFunctions.starClosure_eq_adjoin_X, polynomialFunctions.starClosure_topologicalClosure, starClosure_eq_adjoin_X, starClosure_topologicalClosure, toContinuousMap_X_eq_id
-/
lemma ContinuousMap.elemental_id_eq_top {𝕜 : Type*} [RCLike 𝕜] (s : Set 𝕜) [CompactSpace s] :
    elemental 𝕜 (ContinuousMap.restrict s (.id 𝕜)) = ⊤ := by
  rw [StarAlgebra.elemental]; rw [← polynomialFunctions.starClosure_topologicalClosure]; rw [polynomialFunctions.starClosure_eq_adjoin_X]
  congr
  exact Polynomial.toContinuousMap_X_eq_id.symm

/-- An induction principle for `C(s, 𝕜)`. -/
@[elab_as_elim]
/--
theorem `ContinuousMap.induction_on` / 定理 `ContinuousMap.induction_on`

English:
theorem ContinuousMap.induction_on
  statement: {𝕜 : Type*} [RCLike 𝕜] {s : Set 𝕜}
  proof: by
  refine closure (fun f hf => ?_) f
  rw [polynomialFunctions.starClosure_eq_adjoin_X] at hf
  induction hf using Algebra.adjoin_induction with
  | mem f hf =>
    push _ in _ at hf
    rw [star_eq_iff_star_eq]; rw [eq_comm (b := f)] at hf
    obtain (rfl | rfl) := hf
    all_goals simpa only [to

中文:
定理 连续映射.induction_on
  结论: {𝕜 : 类型} [RCLike 𝕜] {s : 集合 𝕜}
  证明: by
  refine closure (fun f hf => ?_) f
  rw [polynomialFunctions.starClosure_eq_adjoin_X] at hf
  induction hf using Algebra.adjoin_induction with
  | mem f hf =>
    push _ in _ at hf
    rw [star_eq_iff_star_eq]; rw [eq_comm (b := f)] at hf
    obtain (rfl | rfl) := hf
    all_goals simpa only [to

Depends on / 依赖: Algebra, Algebra.adjoin_induction, adjoin_induction, algebraMap, all_goals, closure, eq_comm, polynomialFunctions, polynomialFunctions.starClosure_eq_adjoin_X, starClosure_eq_adjoin_X, star_eq_iff_star_eq, toContinuousMapOnAlgHom_apply, toContinuousMapOn_X_eq_restrict_id
-/
theorem ContinuousMap.induction_on {𝕜 : Type*} [RCLike 𝕜] {s : Set 𝕜}
    {p : C(s, 𝕜) -> Prop} (const : forall r, p (.const s r)) (id : p (.restrict s <| .id 𝕜))
    (star_id : p (star (.restrict s <| .id 𝕜)))
    (add : forall f g, p f -> p g -> p (f + g)) (mul : forall f g, p f -> p g -> p (f * g))
    (closure : (forall f in (polynomialFunctions s).starClosure, p f) -> forall f, p f) (f : C(s, 𝕜)) :
    p f := by
  refine closure (fun f hf => ?_) f
  rw [polynomialFunctions.starClosure_eq_adjoin_X] at hf
  induction hf using Algebra.adjoin_induction with
  | mem f hf =>
    push _ in _ at hf
    rw [star_eq_iff_star_eq]; rw [eq_comm (b := f)] at hf
    obtain (rfl | rfl) := hf
    all_goals simpa only [toContinuousMapOnAlgHom_apply, toContinuousMapOn_X_eq_restrict_id]
  | algebraMap r => exact const r
  | add _ _ _ _ hf hg => exact add _ _ hf hg
  | mul _ _ _ _ hf hg => exact mul _ _ hf hg

open Topology in
@[elab_as_elim]
/--
theorem `ContinuousMap.induction_on_of_compact` / 定理 `ContinuousMap.induction_on_of_compact`

English:
theorem ContinuousMap.induction_on_of_compact
  statement: {𝕜 : Type*} [RCLike 𝕜] {s : Set 𝕜} [CompactSpace s]
  proof: by
  refine f.induction_on const id star_id add mul fun h f => frequently f ?_
  have := polynomialFunctions.starClosure_topologicalClosure s ▸ mem_top (x := f)
  rw [← SetLike.mem_coe]; rw [topologicalClosure_coe]; rw [mem_closure_iff_frequently] at this
exact this.mp .of_forall h

中文:
定理 连续映射.induction_on_of_compact
  结论: {𝕜 : 类型} [RCLike 𝕜] {s : 集合 𝕜} [紧空间 s]
  证明: by
  refine f.induction_on const id star_id add mul fun h f => frequently f ?_
  have := polynomialFunctions.starClosure_topologicalClosure s ▸ mem_top (x := f)
  rw [← SetLike.mem_coe]; rw [topologicalClosure_coe]; rw [mem_closure_iff_frequently] at this
exact this.mp .of_forall h

Depends on / 依赖: SetLike, SetLike.mem_coe, f.induction_on, frequently, induction_on, mem_closure_iff_frequently, mem_coe, mem_top, of_forall, polynomialFunctions, polynomialFunctions.starClosure_topologicalClosure, starClosure_topologicalClosure, star_id, this.mp, topologicalClosure_coe
-/
theorem ContinuousMap.induction_on_of_compact {𝕜 : Type*} [RCLike 𝕜] {s : Set 𝕜} [CompactSpace s]
    {p : C(s, 𝕜) -> Prop} (const : forall r, p (.const s r)) (id : p (.restrict s <| .id 𝕜))
    (star_id : p (star (.restrict s <| .id 𝕜)))
    (add : forall f g, p f -> p g -> p (f + g)) (mul : forall f g, p f -> p g -> p (f * g))
    (frequently : forall f, (existsᶠ g in 𝓝 f, p g) -> p f) (f : C(s, 𝕜)) :
    p f := by
  refine f.induction_on const id star_id add mul fun h f => frequently f ?_
  have := polynomialFunctions.starClosure_topologicalClosure s ▸ mem_top (x := f)
  rw [← SetLike.mem_coe]; rw [topologicalClosure_coe]; rw [mem_closure_iff_frequently] at this
exact this.mp .of_forall h

/-- Continuous algebra homomorphisms from `C(s, ℝ)` into an `ℝ`-algebra `A` which agree
at `X : 𝕜[X]` (interpreted as a continuous map) are, in fact, equal. -/
@[ext (iff := false)]
/--
theorem `ContinuousMap.algHom_ext_map_X` / 定理 `ContinuousMap.algHom_ext_map_X`

English:
theorem ContinuousMap.algHom_ext_map_X
  statement: {A : Type*} [Semiring A]
  proof: by
  suffices (⊤ : Subalgebra Real C(s, Real)) <= AlgHom.equalizer φ ψ from
    AlgHom.ext fun x => this (by trivial)
  rw [← polynomialFunctions.topologicalClosure s]
  exact Subalgebra.topologicalClosure_minimal
    (polynomialFunctions.le_equalizer s φ ψ h) (isClosed_eq hφ hψ)

中文:
定理 连续映射.algHom_ext_map_X
  结论: {A : 类型} [半环 A]
  证明: by
  suffices (⊤ : Subalgebra Real C(s, Real)) <= AlgHom.equalizer φ ψ from
    AlgHom.ext fun x => this (by trivial)
  rw [← polynomialFunctions.topologicalClosure s]
  exact Subalgebra.topologicalClosure_minimal
    (polynomialFunctions.le_equalizer s φ ψ h) (isClosed_eq hφ hψ)

Depends on / 依赖: AlgHom, AlgHom.equalizer, AlgHom.ext, Subalgebra, Subalgebra.topologicalClosure_minimal, equalizer, isClosed_eq, le_equalizer, polynomialFunctions, polynomialFunctions.le_equalizer, polynomialFunctions.topologicalClosure, topologicalClosure, topologicalClosure_minimal
-/
theorem ContinuousMap.algHom_ext_map_X {A : Type*} [Semiring A]
    [Algebra Real A] [TopologicalSpace A] [T2Space A] {s : Set Real} [CompactSpace s]
    {φ ψ : C(s, Real) ->ₐ[Real] A} (hφ : Continuous φ) (hψ : Continuous ψ)
    (h : φ (toContinuousMapOnAlgHom s X) = ψ (toContinuousMapOnAlgHom s X)) : φ = ψ := by
  suffices (⊤ : Subalgebra Real C(s, Real)) <= AlgHom.equalizer φ ψ from
    AlgHom.ext fun x => this (by trivial)
  rw [← polynomialFunctions.topologicalClosure s]
  exact Subalgebra.topologicalClosure_minimal
    (polynomialFunctions.le_equalizer s φ ψ h) (isClosed_eq hφ hψ)

/-- Continuous star algebra homomorphisms from `C(s, 𝕜)` into a star `𝕜`-algebra `A` which agree
at `X : 𝕜[X]` (interpreted as a continuous map) are, in fact, equal. -/
@[ext (iff := false)]
/--
theorem `ContinuousMap.starAlgHom_ext_map_X` / 定理 `ContinuousMap.starAlgHom_ext_map_X`

English:
theorem ContinuousMap.starAlgHom_ext_map_X
  statement: {𝕜 A : Type*} [RCLike 𝕜] [Ring A] [StarRing A]
  proof: by
  suffices (⊤ : StarSubalgebra 𝕜 C(s, 𝕜)) <= StarAlgHom.equalizer φ ψ from
    StarAlgHom.ext fun x => this mem_top
  rw [← polynomialFunctions.starClosure_topologicalClosure s]
  exact StarSubalgebra.topologicalClosure_minimal
    (polynomialFunctions.starClosure_le_equalizer s φ ψ h) (isClosed_

中文:
定理 连续映射.starAlgHom_ext_map_X
  结论: {𝕜 A : 类型} [RCLike 𝕜] [环 A] [对合环 A]
  证明: by
  suffices (⊤ : StarSubalgebra 𝕜 C(s, 𝕜)) <= StarAlgHom.equalizer φ ψ from
    StarAlgHom.ext fun x => this mem_top
  rw [← polynomialFunctions.starClosure_topologicalClosure s]
  exact StarSubalgebra.topologicalClosure_minimal
    (polynomialFunctions.starClosure_le_equalizer s φ ψ h) (isClosed_

Depends on / 依赖: StarAlgHom, StarAlgHom.equalizer, StarAlgHom.ext, StarSubalgebra, StarSubalgebra.topologicalClosure_minimal, equalizer, isClosed_eq, mem_top, polynomialFunctions, polynomialFunctions.starClosure_le_equalizer, polynomialFunctions.starClosure_topologicalClosure, starClosure_le_equalizer, starClosure_topologicalClosure, topologicalClosure_minimal
-/
theorem ContinuousMap.starAlgHom_ext_map_X {𝕜 A : Type*} [RCLike 𝕜] [Ring A] [StarRing A]
    [Algebra 𝕜 A] [TopologicalSpace A] [T2Space A] {s : Set 𝕜} [CompactSpace s]
    {φ ψ : C(s, 𝕜) ->⋆ₐ[𝕜] A} (hφ : Continuous φ) (hψ : Continuous ψ)
    (h : φ (toContinuousMapOnAlgHom s X) = ψ (toContinuousMapOnAlgHom s X)) : φ = ψ := by
  suffices (⊤ : StarSubalgebra 𝕜 C(s, 𝕜)) <= StarAlgHom.equalizer φ ψ from
    StarAlgHom.ext fun x => this mem_top
  rw [← polynomialFunctions.starClosure_topologicalClosure s]
  exact StarSubalgebra.topologicalClosure_minimal
    (polynomialFunctions.starClosure_le_equalizer s φ ψ h) (isClosed_eq hφ hψ)

end PolynomialFunctions

/-! ### Continuous maps sending zero to zero -/

section ContinuousMapZero

variable {𝕜 : Type*} [RCLike 𝕜]
open NonUnitalStarAlgebra Submodule

namespace ContinuousMap

/--
lemma `adjoin_id_eq_span_one_union` / 引理 `adjoin_id_eq_span_one_union`

English:
lemma adjoin_id_eq_span_one_union
  given: (s : Set 𝕜)
  proof: by
  ext x
  rw [SetLike.mem_coe]; rw [SetLike.mem_coe]; rw [← StarAlgebra.adjoin_nonUnitalStarSubalgebra]; rw [← StarSubalgebra.mem_toSubalgebra]; rw [← Subalgebra.mem_toSubmodule]; rw [StarAlgebra.adjoin_nonUnitalStarSubalgebra_eq_span]; rw [span_union]; rw [span_eq_toSubmodule]

中文:
引理 adjoin_id_eq_span_one_union
  条件: (s : 集合 𝕜)
  证明: by
  ext x
  rw [SetLike.mem_coe]; rw [SetLike.mem_coe]; rw [← StarAlgebra.adjoin_nonUnitalStarSubalgebra]; rw [← StarSubalgebra.mem_toSubalgebra]; rw [← Subalgebra.mem_toSubmodule]; rw [StarAlgebra.adjoin_nonUnitalStarSubalgebra_eq_span]; rw [span_union]; rw [span_eq_toSubmodule]

Depends on / 依赖: SetLike, SetLike.mem_coe, StarAlgebra, StarAlgebra.adjoin_nonUnitalStarSubalgebra, StarAlgebra.adjoin_nonUnitalStarSubalgebra_eq_span, StarSubalgebra, StarSubalgebra.mem_toSubalgebra, Subalgebra, Subalgebra.mem_toSubmodule, adjoin_nonUnitalStarSubalgebra, adjoin_nonUnitalStarSubalgebra_eq_span, mem_coe, mem_toSubalgebra, mem_toSubmodule, span_eq_toSubmodule, span_union
-/
lemma adjoin_id_eq_span_one_union (s : Set 𝕜) :
    ((StarAlgebra.adjoin 𝕜 {(restrict s (.id 𝕜) : C(s, 𝕜))}) : Set C(s, 𝕜)) =
      span 𝕜 ({(1 : C(s, 𝕜))} union (adjoin 𝕜 {(restrict s (.id 𝕜) : C(s, 𝕜))})) := by
  ext x
  rw [SetLike.mem_coe]; rw [SetLike.mem_coe]; rw [← StarAlgebra.adjoin_nonUnitalStarSubalgebra]; rw [← StarSubalgebra.mem_toSubalgebra]; rw [← Subalgebra.mem_toSubmodule]; rw [StarAlgebra.adjoin_nonUnitalStarSubalgebra_eq_span]; rw [span_union]; rw [span_eq_toSubmodule]

open scoped Pointwise in
/--
lemma `adjoin_id_eq_span_one_add` / 引理 `adjoin_id_eq_span_one_add`

English:
lemma adjoin_id_eq_span_one_add
  given: (s : Set 𝕜)
  proof: by
  ext x
  rw [SetLike.mem_coe]; rw [← StarAlgebra.adjoin_nonUnitalStarSubalgebra]; rw [← StarSubalgebra.mem_toSubalgebra]; rw [← Subalgebra.mem_toSubmodule]; rw [StarAlgebra.adjoin_nonUnitalStarSubalgebra_eq_span]; rw [mem_sup]
  simp [Set.mem_add]

中文:
引理 adjoin_id_eq_span_one_add
  条件: (s : 集合 𝕜)
  证明: by
  ext x
  rw [SetLike.mem_coe]; rw [← StarAlgebra.adjoin_nonUnitalStarSubalgebra]; rw [← StarSubalgebra.mem_toSubalgebra]; rw [← Subalgebra.mem_toSubmodule]; rw [StarAlgebra.adjoin_nonUnitalStarSubalgebra_eq_span]; rw [mem_sup]
  simp [Set.mem_add]

Depends on / 依赖: Set.mem_add, SetLike, SetLike.mem_coe, StarAlgebra, StarAlgebra.adjoin_nonUnitalStarSubalgebra, StarAlgebra.adjoin_nonUnitalStarSubalgebra_eq_span, StarSubalgebra, StarSubalgebra.mem_toSubalgebra, Subalgebra, Subalgebra.mem_toSubmodule, adjoin_nonUnitalStarSubalgebra, adjoin_nonUnitalStarSubalgebra_eq_span, mem_add, mem_coe, mem_sup, mem_toSubalgebra, mem_toSubmodule
-/
lemma adjoin_id_eq_span_one_add (s : Set 𝕜) :
    ((StarAlgebra.adjoin 𝕜 {(restrict s (.id 𝕜) : C(s, 𝕜))}) : Set C(s, 𝕜)) =
      (span 𝕜 {(1 : C(s, 𝕜))} : Set C(s, 𝕜)) + (adjoin 𝕜 {(restrict s (.id 𝕜) : C(s, 𝕜))}) := by
  ext x
  rw [SetLike.mem_coe]; rw [← StarAlgebra.adjoin_nonUnitalStarSubalgebra]; rw [← StarSubalgebra.mem_toSubalgebra]; rw [← Subalgebra.mem_toSubmodule]; rw [StarAlgebra.adjoin_nonUnitalStarSubalgebra_eq_span]; rw [mem_sup]
  simp [Set.mem_add]

/--
lemma `nonUnitalStarAlgebraAdjoin_id_subset_ker_evalStarAlgHom` / 引理 `nonUnitalStarAlgebraAdjoin_id_subset_ker_evalStarAlgHom`

English:
lemma nonUnitalStarAlgebraAdjoin_id_subset_ker_evalStarAlgHom
  given: {s : Set 𝕜} (h0 : 0 in s)
  proof: by
  intro f hf
  induction hf using adjoin_induction with
  | mem f hf =>
    obtain rfl := Set.mem_singleton_iff.mp hf
    rfl
  | add f g _ _ hf hg => exact add_mem hf hg
  | zero => exact zero_mem _
  | mul f g _ _ _ hg => exact Ideal.mul_mem_left _ f hg
  | smul r f _ hf =>
    rw [SetLike.mem_

中文:
引理 nonUnitalStarAlgebraAdjoin_id_subset_ker_evalStarAlgHom
  条件: {s : 集合 𝕜} (h0 : 0 in s)
  证明: by
  intro f hf
  induction hf using adjoin_induction with
  | mem f hf =>
    obtain rfl := Set.mem_singleton_iff.mp hf
    rfl
  | add f g _ _ hf hg => exact add_mem hf hg
  | zero => exact zero_mem _
  | mul f g _ _ _ hg => exact Ideal.mul_mem_left _ f hg
  | smul r f _ hf =>
    rw [SetLike.mem_

Depends on / 依赖: Ideal.mul_mem_left, RingHom, RingHom.mem_ker, Set.mem_singleton_iff.mp, SetLike, SetLike.mem_coe, add_mem, adjoin_induction, map_smul, map_star, mem_coe, mem_ker, mem_singleton_iff, mul_mem_left, smul_zero, star_zero, zero_mem
-/
lemma nonUnitalStarAlgebraAdjoin_id_subset_ker_evalStarAlgHom {s : Set 𝕜} (h0 : 0 in s) :
    (adjoin 𝕜 {restrict s (.id 𝕜)} : Set C(s, 𝕜)) subseteq
      RingHom.ker (evalStarAlgHom 𝕜 𝕜 (⟨0, h0⟩ : s)) := by
  intro f hf
  induction hf using adjoin_induction with
  | mem f hf =>
    obtain rfl := Set.mem_singleton_iff.mp hf
    rfl
  | add f g _ _ hf hg => exact add_mem hf hg
  | zero => exact zero_mem _
  | mul f g _ _ _ hg => exact Ideal.mul_mem_left _ f hg
  | smul r f _ hf =>
    rw [SetLike.mem_coe]; rw [RingHom.mem_ker] at hf ⊢
    rw [map_smul]; rw [hf]; rw [smul_zero]
  | star f _ hf =>
    rw [SetLike.mem_coe]; rw [RingHom.mem_ker] at hf ⊢
    rw [map_star]; rw [hf]; rw [star_zero]

/--
lemma `ker_evalStarAlgHom_inter_adjoin_id` / 引理 `ker_evalStarAlgHom_inter_adjoin_id`

English:
lemma ker_evalStarAlgHom_inter_adjoin_id
  given: (s : Set 𝕜) (h0 : 0 in s)
  proof: by
  ext f
  constructor
  · rintro ⟨hf₁, hf₂⟩
    rw [SetLike.mem_coe] at hf₂ ⊢
    simp_rw [adjoin_id_eq_span_one_add, Set.mem_add, SetLike.mem_coe, mem_span_singleton] at hf₁
    obtain ⟨-, ⟨r, rfl⟩, f, hf, rfl⟩ := hf₁
    have := nonUnitalStarAlgebraAdjoin_id_subset_ker_evalStarAlgHom h0 hf
    

中文:
引理 ker_evalStarAlgHom_inter_adjoin_id
  条件: (s : 集合 𝕜) (h0 : 0 in s)
  证明: by
  ext f
  constructor
  · rintro ⟨hf₁, hf₂⟩
    rw [SetLike.mem_coe] at hf₂ ⊢
    simp_rw [adjoin_id_eq_span_one_add, Set.mem_add, SetLike.mem_coe, mem_span_singleton] at hf₁
    obtain ⟨-, ⟨r, rfl⟩, f, hf, rfl⟩ := hf₁
    have := nonUnitalStarAlgebraAdjoin_id_subset_ker_evalStarAlgHom h0 hf
    

Depends on / 依赖: RingHom, RingHom.mem_ker, Set.mem_add, SetLike, SetLike.mem_coe, add_apply, add_zero, adjoin_id_eq_span_one_add, evalStarAlgHom_apply, mem_add, mem_coe, mem_ker, mem_span_singleton, mul_one, nonUnitalStarAlgebraAdjoin_id_subset_ker_evalStarAlgHom, one_apply, simp_rw, smul_apply, smul_eq_mul, zero_add
-/
lemma ker_evalStarAlgHom_inter_adjoin_id (s : Set 𝕜) (h0 : 0 in s) :
    (StarAlgebra.adjoin 𝕜 {restrict s (.id 𝕜)} : Set C(s, 𝕜)) inter
      RingHom.ker (evalStarAlgHom 𝕜 𝕜 (⟨0, h0⟩ : s)) = adjoin 𝕜 {restrict s (.id 𝕜)} := by
  ext f
  constructor
  · rintro ⟨hf₁, hf₂⟩
    rw [SetLike.mem_coe] at hf₂ ⊢
    simp_rw [adjoin_id_eq_span_one_add, Set.mem_add, SetLike.mem_coe, mem_span_singleton] at hf₁
    obtain ⟨-, ⟨r, rfl⟩, f, hf, rfl⟩ := hf₁
    have := nonUnitalStarAlgebraAdjoin_id_subset_ker_evalStarAlgHom h0 hf
    simp only [SetLike.mem_coe, RingHom.mem_ker, evalStarAlgHom_apply] at hf₂ this
    rw [add_apply]; rw [this]; rw [add_zero]; rw [smul_apply]; rw [one_apply]; rw [smul_eq_mul]; rw [mul_one] at hf₂
    rwa [hf₂, zero_smul, zero_add]
  · simp only [Set.mem_inter_iff, SetLike.mem_coe]
    refine fun hf => ⟨?_, nonUnitalStarAlgebraAdjoin_id_subset_ker_evalStarAlgHom h0 hf⟩
    exact adjoin_le_starAlgebra_adjoin _ _ hf

set_option backward.isDefEq.respectTransparency false in
-- the statement should be in terms of nonunital subalgebras, but we lack API
open RingHom Filter Topology in
/--
theorem `AlgHom.closure_ker_inter` / 定理 `AlgHom.closure_ker_inter`

English:
theorem AlgHom.closure_ker_inter
  statement: {F S K A : Type*} [CommRing K] [Ring A] [Algebra K A]
  proof: by
  refine subset_antisymm ?_ ?_
  · simpa only [ker_eq, (isClosed_singleton.preimage hφ).closure_eq]
      using closure_inter_subset_inter_closure s (ker φ : Set A)
  · intro x ⟨hxs, (hxφ : φ x = 0)⟩
    rw [mem_closure_iff_clusterPt]; rw [ClusterPt] at hxs
    have : Tendsto (fun y => y - φ y • 

中文:
定理 代数态射.closure_ker_inter
  结论: {F S K A : 类型} [交换环 K] [环 A] [代数 K A]
  证明: by
  refine subset_antisymm ?_ ?_
  · simpa only [ker_eq, (isClosed_singleton.preimage hφ).closure_eq]
      using closure_inter_subset_inter_closure s (ker φ : Set A)
  · intro x ⟨hxs, (hxφ : φ x = 0)⟩
    rw [mem_closure_iff_clusterPt]; rw [ClusterPt] at hxs
    have : Tendsto (fun y => y - φ y • 

Depends on / 依赖: ClusterPt, Continuous, Continuous.tendsto, Filter, Filter.tendsto_inf_left, Tendsto, closure_eq, closure_inter_subset_inter_closure, eventually_inf_principal, fun_prop, isClosed_singleton, isClosed_singleton.preimage, ker_eq, mem_closure_iff_clusterPt, mem_closure_of_tendsto, preimage, sub_zero, subset_antisymm, tendsto, tendsto_inf_left
-/
theorem AlgHom.closure_ker_inter {F S K A : Type*} [CommRing K] [Ring A] [Algebra K A]
    [TopologicalSpace K] [T1Space K] [TopologicalSpace A] [ContinuousSub A] [ContinuousSMul K A]
    [FunLike F A K] [AlgHomClass F K A K] [SetLike S A] [OneMemClass S A] [AddSubgroupClass S A]
    [SMulMemClass S K A] (φ : F) (hφ : Continuous φ) (s : S) :
    closure (s inter RingHom.ker φ) = closure s inter (ker φ : Set A) := by
  refine subset_antisymm ?_ ?_
  · simpa only [ker_eq, (isClosed_singleton.preimage hφ).closure_eq]
      using closure_inter_subset_inter_closure s (ker φ : Set A)
  · intro x ⟨hxs, (hxφ : φ x = 0)⟩
    rw [mem_closure_iff_clusterPt]; rw [ClusterPt] at hxs
    have : Tendsto (fun y => y - φ y • 1) (𝓝 x ⊓ 𝓟 s) (𝓝 x) := by
      conv => congr; rfl; rfl; rw [← sub_zero x, ← zero_smul K 1, ← hxφ]
      exact Filter.tendsto_inf_left (Continuous.tendsto (by fun_prop) x)
refine mem_closure_of_tendsto this eventually_inf_principal.mpr ?_
    filter_upwards [] with g hg using
      ⟨sub_mem hg (SMulMemClass.smul_mem _ <| one_mem _), by simp [RingHom.mem_ker]⟩

/--
lemma `ker_evalStarAlgHom_eq_closure_adjoin_id` / 引理 `ker_evalStarAlgHom_eq_closure_adjoin_id`

English:
lemma ker_evalStarAlgHom_eq_closure_adjoin_id
  given: (s : Set 𝕜) (h0 : 0 in s) [CompactSpace s]
  proof: by
  rw [← ker_evalStarAlgHom_inter_adjoin_id s h0]; rw [AlgHom.closure_ker_inter (φ := evalStarAlgHom 𝕜 𝕜 (X := s) ⟨0]; rw [h0⟩) (continuous_eval_const _) _]
  convert! (Set.univ_inter _).symm
  rw [← Polynomial.toContinuousMapOn_X_eq_restrict_id]; rw [← Polynomial.toContinuousMapOnAlgHom_apply]; r

中文:
引理 ker_evalStarAlgHom_eq_closure_adjoin_id
  条件: (s : 集合 𝕜) (h0 : 0 in s) [紧空间 s]
  证明: by
  rw [← ker_evalStarAlgHom_inter_adjoin_id s h0]; rw [AlgHom.closure_ker_inter (φ := evalStarAlgHom 𝕜 𝕜 (X := s) ⟨0]; rw [h0⟩) (continuous_eval_const _) _]
  convert! (Set.univ_inter _).symm
  rw [← Polynomial.toContinuousMapOn_X_eq_restrict_id]; rw [← Polynomial.toContinuousMapOnAlgHom_apply]; r

Depends on / 依赖: AlgHom, AlgHom.closure_ker_inter, Polynomial, Polynomial.toContinuousMapOnAlgHom_apply, Polynomial.toContinuousMapOn_X_eq_restrict_id, Set.univ_inter, closure_ker_inter, congrm, continuous_eval_const, convert, evalStarAlgHom, ker_evalStarAlgHom_inter_adjoin_id, polynomialFunctions, polynomialFunctions.starClosure_eq_adjoin_X, polynomialFunctions.starClosure_topologicalClosure, starClosure_eq_adjoin_X, starClosure_topologicalClosure, toContinuousMapOnAlgHom_apply, toContinuousMapOn_X_eq_restrict_id, univ_inter
-/
lemma ker_evalStarAlgHom_eq_closure_adjoin_id (s : Set 𝕜) (h0 : 0 in s) [CompactSpace s] :
    (RingHom.ker (evalStarAlgHom 𝕜 𝕜 (⟨0, h0⟩ : s)) : Set C(s, 𝕜)) =
      closure (adjoin 𝕜 {(restrict s (.id 𝕜))}) := by
  rw [← ker_evalStarAlgHom_inter_adjoin_id s h0]; rw [AlgHom.closure_ker_inter (φ := evalStarAlgHom 𝕜 𝕜 (X := s) ⟨0]; rw [h0⟩) (continuous_eval_const _) _]
  convert! (Set.univ_inter _).symm
  rw [← Polynomial.toContinuousMapOn_X_eq_restrict_id]; rw [← Polynomial.toContinuousMapOnAlgHom_apply]; rw [← polynomialFunctions.starClosure_eq_adjoin_X s]
  congrm (($(polynomialFunctions.starClosure_topologicalClosure s) : Set C(s, 𝕜)))

end ContinuousMap

open scoped ContinuousMapZero

/--
lemma `ContinuousMapZero.adjoin_id_dense` / 引理 `ContinuousMapZero.adjoin_id_dense`

English:
lemma ContinuousMapZero.adjoin_id_dense
  statement: (s : Set 𝕜) [Fact (0 in s)]
  proof: by
  have h0' : 0 in s := Fact.out
  rw [dense_iff_closure_eq]; rw [← isClosedEmbedding_toContinuousMap.injective.preimage_image (closure _)]; rw [← isClosedEmbedding_toContinuousMap.closure_image_eq]; rw [← coe_toContinuousMapHom]; rw [← NonUnitalStarSubalgebra.coe_map]; rw [NonUnitalStarAlgHom.map

中文:
引理 余ntinuousMapZero.adjoin_id_dense
  结论: (s : 集合 𝕜) [Fact (0 in s)]
  证明: by
  have h0' : 0 in s := Fact.out
  rw [dense_iff_closure_eq]; rw [← isClosedEmbedding_toContinuousMap.injective.preimage_image (closure _)]; rw [← isClosedEmbedding_toContinuousMap.closure_image_eq]; rw [← coe_toContinuousMapHom]; rw [← NonUnitalStarSubalgebra.coe_map]; rw [NonUnitalStarAlgHom.map

Depends on / 依赖: ContinuousMap, ContinuousMap.ker_evalStarAlgHom_eq_closure_adjoin_id, Fact.out, NonUnitalStarAlgHom, NonUnitalStarAlgHom.map_adjoin_singleton, NonUnitalStarSubalgebra, NonUnitalStarSubalgebra.coe_map, Set.eq_univ_of_forall, Set.mem_prei, closure, closure_image_eq, coe_map, coe_toContinuousMapHom, dense_iff_closure_eq, eq_univ_of_forall, injective, isClosedEmbedding_toContinuousMap, isClosedEmbedding_toContinuousMap.closure_image_eq, isClosedEmbedding_toContinuousMap.injective.preimage_image, ker_evalStarAlgHom_eq_closure_adjoin_id
-/
lemma ContinuousMapZero.adjoin_id_dense (s : Set 𝕜) [Fact (0 in s)]
    [CompactSpace s] : Dense (adjoin 𝕜 {(.id s : C(s, 𝕜)₀)} : Set C(s, 𝕜)₀) := by
  have h0' : 0 in s := Fact.out
  rw [dense_iff_closure_eq]; rw [← isClosedEmbedding_toContinuousMap.injective.preimage_image (closure _)]; rw [← isClosedEmbedding_toContinuousMap.closure_image_eq]; rw [← coe_toContinuousMapHom]; rw [← NonUnitalStarSubalgebra.coe_map]; rw [NonUnitalStarAlgHom.map_adjoin_singleton]; rw [coe_toContinuousMapHom]; rw [toContinuousMap_id]; rw [← ContinuousMap.ker_evalStarAlgHom_eq_closure_adjoin_id s h0']
  apply Set.eq_univ_of_forall fun f => ?_
  simp only [Set.mem_preimage, SetLike.mem_coe, RingHom.mem_ker,
    ContinuousMap.evalStarAlgHom_apply, ContinuousMap.coe_coe]
  exact map_zero f

open NonUnitalStarAlgebra in
/--
lemma `ContinuousMapZero.elemental_eq_top` / 引理 `ContinuousMapZero.elemental_eq_top`

English:
lemma ContinuousMapZero.elemental_eq_top
  statement: {𝕜 : Type*} [RCLike 𝕜] (s : Set 𝕜) [Fact (0 in s)]
  proof: SetLike.ext'_iff.mpr (adjoin_id_dense s).closure_eq

中文:
引理 余ntinuousMapZero.elemental_eq_top
  结论: {𝕜 : 类型} [RCLike 𝕜] (s : 集合 𝕜) [Fact (0 in s)]
  证明: SetLike.ext'_iff.mpr (adjoin_id_dense s).closure_eq

Depends on / 依赖: SetLike, SetLike.ext, _iff, _iff.mpr, adjoin_id_dense, closure_eq
-/
lemma ContinuousMapZero.elemental_eq_top {𝕜 : Type*} [RCLike 𝕜] (s : Set 𝕜) [Fact (0 in s)]
    [CompactSpace s] : elemental 𝕜 (ContinuousMapZero.id s) = ⊤ :=
  SetLike.ext'_iff.mpr (adjoin_id_dense s).closure_eq

/-- An induction principle for `C(s, 𝕜)₀`. -/
@[elab_as_elim]
/--
lemma `ContinuousMapZero.induction_on` / 引理 `ContinuousMapZero.induction_on`

English:
lemma ContinuousMapZero.induction_on
  statement: {s : Set 𝕜} [Fact (0 in s)]
  proof: by
  refine closure (fun f hf => ?_) f
  induction hf using NonUnitalAlgebra.adjoin_induction with
  | mem f hf =>
    push _ in _ at hf
    rw [star_eq_iff_star_eq] at hf
    obtain (rfl | rfl) := hf
    all_goals assumption
  | zero => exact zero
  | add _ _ _ _ hf hg => exact add _ _ hf hg
  | mu

中文:
引理 余ntinuousMapZero.induction_on
  结论: {s : 集合 𝕜} [Fact (0 in s)]
  证明: by
  refine closure (fun f hf => ?_) f
  induction hf using NonUnitalAlgebra.adjoin_induction with
  | mem f hf =>
    push _ in _ at hf
    rw [star_eq_iff_star_eq] at hf
    obtain (rfl | rfl) := hf
    all_goals assumption
  | zero => exact zero
  | add _ _ _ _ hf hg => exact add _ _ hf hg
  | mu

Depends on / 依赖: NonUnitalAlgebra, NonUnitalAlgebra.adjoin_induction, adjoin_induction, all_goals, closure, star_eq_iff_star_eq
-/
lemma ContinuousMapZero.induction_on {s : Set 𝕜} [Fact (0 in s)]
    {p : C(s, 𝕜)₀ -> Prop} (zero : p 0) (id : p (.id s)) (star_id : p (star (.id s)))
    (add : forall f g, p f -> p g -> p (f + g)) (mul : forall f g, p f -> p g -> p (f * g))
    (smul : forall (r : 𝕜) f, p f -> p (r • f))
    (closure : (forall f in adjoin 𝕜 {(.id s : C(s, 𝕜)₀)}, p f) -> forall f, p f) (f : C(s, 𝕜)₀) :
    p f := by
  refine closure (fun f hf => ?_) f
  induction hf using NonUnitalAlgebra.adjoin_induction with
  | mem f hf =>
    push _ in _ at hf
    rw [star_eq_iff_star_eq] at hf
    obtain (rfl | rfl) := hf
    all_goals assumption
  | zero => exact zero
  | add _ _ _ _ hf hg => exact add _ _ hf hg
  | mul _ _ _ _ hf hg => exact mul _ _ hf hg
  | smul _ _ _ hf => exact smul _ _ hf

open Topology in
@[elab_as_elim]
/--
theorem `ContinuousMapZero.induction_on_of_compact` / 定理 `ContinuousMapZero.induction_on_of_compact`

English:
theorem ContinuousMapZero.induction_on_of_compact
  statement: {s : Set 𝕜} [Fact (0 in s)]
  proof: by
  refine f.induction_on zero id star_id add mul smul fun h f => frequently f ?_
  have := (ContinuousMapZero.adjoin_id_dense s).closure_eq ▸ Set.mem_univ (x := f)
.mp .of_forall h exact mem_closure_iff_frequently.mp this

中文:
定理 余ntinuousMapZero.induction_on_of_compact
  结论: {s : 集合 𝕜} [Fact (0 in s)]
  证明: by
  refine f.induction_on zero id star_id add mul smul fun h f => frequently f ?_
  have := (ContinuousMapZero.adjoin_id_dense s).closure_eq ▸ Set.mem_univ (x := f)
.mp .of_forall h exact mem_closure_iff_frequently.mp this

Depends on / 依赖: ContinuousMapZero, ContinuousMapZero.adjoin_id_dense, Set.mem_univ, adjoin_id_dense, closure_eq, f.induction_on, frequently, induction_on, mem_closure_iff_frequently, mem_closure_iff_frequently.mp, mem_univ, of_forall, star_id
-/
theorem ContinuousMapZero.induction_on_of_compact {s : Set 𝕜} [Fact (0 in s)]
    [CompactSpace s] {p : C(s, 𝕜)₀ -> Prop} (zero : p 0) (id : p (.id s))
    (star_id : p (star (.id s))) (add : forall f g, p f -> p g -> p (f + g))
    (mul : forall f g, p f -> p g -> p (f * g)) (smul : forall (r : 𝕜) f, p f -> p (r • f))
    (frequently : forall f, (existsᶠ g in 𝓝 f, p g) -> p f) (f : C(s, 𝕜)₀) :
    p f := by
  refine f.induction_on zero id star_id add mul smul fun h f => frequently f ?_
  have := (ContinuousMapZero.adjoin_id_dense s).closure_eq ▸ Set.mem_univ (x := f)
.mp .of_forall h exact mem_closure_iff_frequently.mp this

/--
lemma `ContinuousMapZero.nonUnitalStarAlgHom_apply_mul_eq_zero` / 引理 `ContinuousMapZero.nonUnitalStarAlgHom_apply_mul_eq_zero`

English:
lemma ContinuousMapZero.nonUnitalStarAlgHom_apply_mul_eq_zero
  statement: {𝕜 A : Type*}
  proof: by
  induction f using ContinuousMapZero.induction_on_of_compact with
  | zero => simp [map_zero]
  | id => exact hmul_id
  | star_id => exact hmul_star_id
  | add _ _ h₁ h₂ => simp only [map_add, add_mul, h₁, h₂, zero_add]
  | mul _ _ _ h => simp only [map_mul, mul_assoc, h, mul_zero]
  | smul _ _ 

中文:
引理 余ntinuousMapZero.nonUnitalStarAlgHom_apply_mul_eq_zero
  结论: {𝕜 A : 类型}
  证明: by
  induction f using ContinuousMapZero.induction_on_of_compact with
  | zero => simp [map_zero]
  | id => exact hmul_id
  | star_id => exact hmul_star_id
  | add _ _ h₁ h₂ => simp only [map_add, add_mul, h₁, h₂, zero_add]
  | mul _ _ _ h => simp only [map_mul, mul_assoc, h, mul_zero]
  | smul _ _ 

Depends on / 依赖: ContinuousMapZero, ContinuousMapZero.induction_on_of_compact, add_mul, continuous_zero, frequently, fun_prop, h.mem_of_closed, hmul_id, hmul_star_id, induction_on_of_compact, isClosed_eq, map_add, map_mul, map_smul, map_zero, mem_of_closed, mul_assoc, mul_zero, smul_mul_assoc, smul_zero
-/
lemma ContinuousMapZero.nonUnitalStarAlgHom_apply_mul_eq_zero {𝕜 A : Type*}
    [RCLike 𝕜] [NonUnitalSemiring A] [Star A] [TopologicalSpace A] [SeparatelyContinuousMul A]
    [T2Space A] [DistribMulAction 𝕜 A] [IsScalarTower 𝕜 A A] {s : Set 𝕜} [Fact (0 in s)]
    [CompactSpace s] (φ : C(s, 𝕜)₀ ->⋆ₙₐ[𝕜] A) (a : A) (hmul_id : φ (.id s) * a = 0)
    (hmul_star_id : φ (star (.id s)) * a = 0) (hφ : Continuous φ) (f : C(s, 𝕜)₀) :
    φ f * a = 0 := by
  induction f using ContinuousMapZero.induction_on_of_compact with
  | zero => simp [map_zero]
  | id => exact hmul_id
  | star_id => exact hmul_star_id
  | add _ _ h₁ h₂ => simp only [map_add, add_mul, h₁, h₂, zero_add]
  | mul _ _ _ h => simp only [map_mul, mul_assoc, h, mul_zero]
  | smul _ _ h => rw [map_smul, smul_mul_assoc, h, smul_zero]
| frequently f h => exact h.mem_of_closed isClosed_eq (by fun_prop) continuous_zero

/--
lemma `ContinuousMapZero.mul_nonUnitalStarAlgHom_apply_eq_zero` / 引理 `ContinuousMapZero.mul_nonUnitalStarAlgHom_apply_eq_zero`

English:
lemma ContinuousMapZero.mul_nonUnitalStarAlgHom_apply_eq_zero
  statement: {𝕜 A : Type*}
  proof: by
  induction f using ContinuousMapZero.induction_on_of_compact with
  | zero => simp [map_zero]
  | id => exact hmul_id
  | star_id => exact hmul_star_id
  | add _ _ h₁ h₂ => simp only [map_add, mul_add, h₁, h₂, zero_add]
  | mul _ _ h _ => simp only [map_mul, ← mul_assoc, h, zero_mul]
  | smul _ 

中文:
引理 余ntinuousMapZero.mul_nonUnitalStarAlgHom_apply_eq_zero
  结论: {𝕜 A : 类型}
  证明: by
  induction f using ContinuousMapZero.induction_on_of_compact with
  | zero => simp [map_zero]
  | id => exact hmul_id
  | star_id => exact hmul_star_id
  | add _ _ h₁ h₂ => simp only [map_add, mul_add, h₁, h₂, zero_add]
  | mul _ _ h _ => simp only [map_mul, ← mul_assoc, h, zero_mul]
  | smul _ 

Depends on / 依赖: ContinuousMapZero, ContinuousMapZero.induction_on_of_compact, continuous_zero, frequently, fun_prop, h.mem_of_closed, hmul_id, hmul_star_id, induction_on_of_compact, isClosed_eq, map_add, map_mul, map_smul, map_zero, mem_of_closed, mul_add, mul_assoc, mul_smul_comm, smul_zero, star_id
-/
lemma ContinuousMapZero.mul_nonUnitalStarAlgHom_apply_eq_zero {𝕜 A : Type*}
    [RCLike 𝕜] [NonUnitalSemiring A] [Star A] [TopologicalSpace A] [SeparatelyContinuousMul A]
    [T2Space A] [DistribMulAction 𝕜 A] [SMulCommClass 𝕜 A A] {s : Set 𝕜} [Fact (0 in s)]
    [CompactSpace s] (φ : C(s, 𝕜)₀ ->⋆ₙₐ[𝕜] A) (a : A) (hmul_id : a * φ (.id s) = 0)
    (hmul_star_id : a * φ (star (.id s)) = 0) (hφ : Continuous φ) (f : C(s, 𝕜)₀) :
    a * φ f = 0 := by
  induction f using ContinuousMapZero.induction_on_of_compact with
  | zero => simp [map_zero]
  | id => exact hmul_id
  | star_id => exact hmul_star_id
  | add _ _ h₁ h₂ => simp only [map_add, mul_add, h₁, h₂, zero_add]
  | mul _ _ h _ => simp only [map_mul, ← mul_assoc, h, zero_mul]
  | smul _ _ h => rw [map_smul, mul_smul_comm, h, smul_zero]
| frequently f h => exact h.mem_of_closed isClosed_eq (by fun_prop) continuous_zero

end ContinuousMapZero
