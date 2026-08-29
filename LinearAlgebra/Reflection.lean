/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Deepro Choudhury, Mitchell Lee, Johan Commelin
-/
module

public import Mathlib.Algebra.EuclideanDomain.Basic
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Algebra.Module.Submodule.Invariant
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.FiniteSpan
public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.Tactic.Module

/-!
# Reflections in linear algebra

Given an element `x` in a module `M` together with a linear form `f` on `M` such that `f x = 2`, the
map `y ↦ y - (f y) • x` is an involutive endomorphism of `M`, such that:
1. the kernel of `f` is fixed,
2. the point `x` maps to `-x`.

Such endomorphisms are often called reflections of the module `M`. When `M` carries an inner product
for which `x` is perpendicular to the kernel of `f`, then (with mild assumptions) the endomorphism
is characterised by properties 1 and 2 above, and is a linear isometry.

## Main definitions / results:

* `Module.preReflection`: the definition of the map `y ↦ y - (f y) • x`. Its main utility lies in
  the fact that it does not require the assumption `f x = 2`, giving the user freedom to defer
  discharging this proof obligation.
* `Module.reflection`: the definition of the map `y ↦ y - (f y) • x`. This requires the assumption
  that `f x = 2` but by way of compensation it produces a linear equivalence rather than a mere
  linear map.
* `Module.reflection_mul_reflection_pow_apply`: a formula for $(r_1 r_2)^m z$, where $r_1$ and
  $r_2$ are reflections and $z \in M$. It involves the Chebyshev polynomials and holds over any
  commutative ring. This is used to define reflection representations of Coxeter groups.
* `Module.Dual.eq_of_preReflection_mapsTo`: a uniqueness result about reflections that preserve
  finite spanning sets. It is useful in the theory of root data / systems.

## TODO

Related definitions of reflection exist elsewhere in the library. These more specialised
definitions, which require an ambient `InnerProductSpace` structure, are `reflection` (of type
`LinearIsometryEquiv`) and `EuclideanGeometry.reflection` (of type `AffineIsometryEquiv`). We
should connect (or unify) these definitions with `Module.reflection` defined here.

-/

@[expose] public section

open Function Set
open Module
open Submodule (span)

noncomputable section

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (x : M) (f : Dual R M) (y : M)

namespace Module

/--
Definition of `preReflection` / `preReflection` 的定义

English:
definition preReflection
  signature: : End R M
  body: LinearMap.id - f.smulRight x

中文:
定义 preReflection
  签名: : End R M
  定义体: LinearMap.id - f.smulRight x

Depends on / 依赖: LinearMap, LinearMap.id, f.smulRight, smulRight
-/
def preReflection : End R M :=
  LinearMap.id - f.smulRight x

/--
lemma `preReflection_apply` / 引理 `preReflection_apply`

English:
lemma preReflection_apply
  proof: by
  simp [preReflection]

中文:
引理 preReflection_apply
  证明: by
  simp [preReflection]

Depends on / 依赖: preReflection
-/
lemma preReflection_apply :
    preReflection x f y = y - (f y) • x := by
  simp [preReflection]

variable {x f}

/--
lemma `preReflection_apply_self` / 引理 `preReflection_apply_self`

English:
lemma preReflection_apply_self
  given: (h : f x = 2)
  proof: by
  rw [preReflection_apply]; rw [h]; rw [two_smul]; abel

中文:
引理 preReflection_apply_self
  条件: (h : f x = 2)
  证明: by
  rw [preReflection_apply]; rw [h]; rw [two_smul]; abel

Depends on / 依赖: preReflection_apply, two_smul
-/
lemma preReflection_apply_self (h : f x = 2) :
    preReflection x f x = -x := by
  rw [preReflection_apply]; rw [h]; rw [two_smul]; abel

/--
lemma `involutive_preReflection` / 引理 `involutive_preReflection`

English:
lemma involutive_preReflection
  given: (h : f x = 2)
  proof: fun y => by simp [map_sub, h, two_smul, preReflection_apply]

中文:
引理 involutive_preReflection
  条件: (h : f x = 2)
  证明: fun y => by simp [map_sub, h, two_smul, preReflection_apply]

Depends on / 依赖: map_sub, preReflection_apply, two_smul
-/
lemma involutive_preReflection (h : f x = 2) :
    Involutive (preReflection x f) :=
  fun y => by simp [map_sub, h, two_smul, preReflection_apply]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `preReflection_preReflection` / 引理 `preReflection_preReflection`

English:
lemma preReflection_preReflection
  given: (g : Dual R M) (h : f x = 2)
  proof: by
  ext m
  simp only [h, preReflection_apply, mul_comm (g x) (f m), mul_two, mul_assoc, Dual.eval_apply,
    LinearMap.sub_apply, LinearMap.coe_comp, LinearMap.smul_apply, smul_eq_mul, smul_sub, sub_smul,
    smul_smul, sub_mul, comp_apply, map_sub, map_smul, add_smul]
  abel

中文:
引理 preReflection_preReflection
  条件: (g : 对偶 R M) (h : f x = 2)
  证明: by
  ext m
  simp only [h, preReflection_apply, mul_comm (g x) (f m), mul_two, mul_assoc, Dual.eval_apply,
    LinearMap.sub_apply, LinearMap.coe_comp, LinearMap.smul_apply, smul_eq_mul, smul_sub, sub_smul,
    smul_smul, sub_mul, comp_apply, map_sub, map_smul, add_smul]
  abel

Depends on / 依赖: Dual.eval_apply, LinearMap, LinearMap.coe_comp, LinearMap.smul_apply, LinearMap.sub_apply, add_smul, coe_comp, comp_apply, eval_apply, map_smul, map_sub, mul_assoc, mul_comm, mul_two, preReflection_apply, smul_apply, smul_eq_mul, smul_smul, smul_sub, sub_apply
-/
lemma preReflection_preReflection (g : Dual R M) (h : f x = 2) :
    preReflection (preReflection x f y) (preReflection f (Dual.eval R M x) g) =
    (preReflection x f) ∘ₗ (preReflection y g) ∘ₗ (preReflection x f) := by
  ext m
  simp only [h, preReflection_apply, mul_comm (g x) (f m), mul_two, mul_assoc, Dual.eval_apply,
    LinearMap.sub_apply, LinearMap.coe_comp, LinearMap.smul_apply, smul_eq_mul, smul_sub, sub_smul,
    smul_smul, sub_mul, comp_apply, map_sub, map_smul, add_smul]
  abel

/--
Definition of `reflection` / `reflection` 的定义

English:
definition reflection
  signature: (h : f x = 2)
  body: { preReflection x f, (involutive_preReflection h).toPerm with }

中文:
定义 reflection
  签名: (h : f x = 2)
  定义体: { preReflection x f, (involutive_preReflection h).toPerm with }

Depends on / 依赖: involutive_preReflection, preReflection, toPerm
-/
def reflection (h : f x = 2) : M ≃ₗ[R] M :=
  { preReflection x f, (involutive_preReflection h).toPerm with }

/--
lemma `reflection_apply` / 引理 `reflection_apply`

English:
lemma reflection_apply
  given: (h : f x = 2)
  proof: preReflection_apply x f y

@[simp]

中文:
引理 reflection_apply
  条件: (h : f x = 2)
  证明: preReflection_apply x f y

@[simp]

Depends on / 依赖: preReflection_apply
-/
lemma reflection_apply (h : f x = 2) :
    reflection h y = y - (f y) • x :=
  preReflection_apply x f y

@[simp]
/--
lemma `reflection_apply_self` / 引理 `reflection_apply_self`

English:
lemma reflection_apply_self
  given: (h : f x = 2)
  proof: preReflection_apply_self h

中文:
引理 reflection_apply_self
  条件: (h : f x = 2)
  证明: preReflection_apply_self h

Depends on / 依赖: preReflection_apply_self
-/
lemma reflection_apply_self (h : f x = 2) :
    reflection h x = -x :=
  preReflection_apply_self h

/--
lemma `involutive_reflection` / 引理 `involutive_reflection`

English:
lemma involutive_reflection
  given: (h : f x = 2)
  proof: involutive_preReflection h

@[simp]

中文:
引理 involutive_reflection
  条件: (h : f x = 2)
  证明: involutive_preReflection h

@[simp]

Depends on / 依赖: involutive_preReflection
-/
lemma involutive_reflection (h : f x = 2) :
    Involutive (reflection h) :=
  involutive_preReflection h

@[simp]
/--
lemma `reflection_inv` / 引理 `reflection_inv`

English:
lemma reflection_inv
  given: (h : f x = 2)
  statement: (reflection h)⁻¹ = reflection h
  proof: rfl

@[simp]

中文:
引理 reflection_inv
  条件: (h : f x = 2)
  结论: (reflection h)⁻¹ = reflection h
  证明: rfl

@[simp]
-/
lemma reflection_inv (h : f x = 2) : (reflection h)⁻¹ = reflection h := rfl

@[simp]
/--
lemma `reflection_symm` / 引理 `reflection_symm`

English:
lemma reflection_symm
  given: (h : f x = 2)
  proof: rfl

中文:
引理 reflection_symm
  条件: (h : f x = 2)
  证明: rfl
-/
lemma reflection_symm (h : f x = 2) :
    (reflection h).symm = reflection h :=
  rfl

/--
lemma `invOn_reflection_of_mapsTo` / 引理 `invOn_reflection_of_mapsTo`

English:
lemma invOn_reflection_of_mapsTo
  given: {Φ : Set M} (h : f x = 2)
  proof: ⟨fun x _ => involutive_reflection h x, fun x _ => involutive_reflection h x⟩

中文:
引理 invOn_reflection_of_mapsTo
  条件: {Φ : 集合 M} (h : f x = 2)
  证明: ⟨fun x _ => involutive_reflection h x, fun x _ => involutive_reflection h x⟩

Depends on / 依赖: involutive_reflection
-/
lemma invOn_reflection_of_mapsTo {Φ : Set M} (h : f x = 2) :
    InvOn (reflection h) (reflection h) Φ Φ :=
  ⟨fun x _ => involutive_reflection h x, fun x _ => involutive_reflection h x⟩

/--
lemma `bijOn_reflection_of_mapsTo` / 引理 `bijOn_reflection_of_mapsTo`

English:
lemma bijOn_reflection_of_mapsTo
  given: {Φ : Set M} (h : f x = 2) (h' : MapsTo (reflection h) Φ Φ)
  proof: (invOn_reflection_of_mapsTo h).bijOn h' h'

中文:
引理 bijOn_reflection_of_mapsTo
  条件: {Φ : 集合 M} (h : f x = 2) (h' : 映射到 (reflection h) Φ Φ)
  证明: (invOn_reflection_of_mapsTo h).bijOn h' h'

Depends on / 依赖: invOn_reflection_of_mapsTo
-/
lemma bijOn_reflection_of_mapsTo {Φ : Set M} (h : f x = 2) (h' : MapsTo (reflection h) Φ Φ) :
    BijOn (reflection h) Φ Φ :=
  (invOn_reflection_of_mapsTo h).bijOn h' h'

/--
lemma `_root_.Submodule.mem_invtSubmodule_reflection_of_mem` / 引理 `_root_.Submodule.mem_invtSubmodule_reflection_of_mem`

English:
lemma _root_.Submodule.mem_invtSubmodule_reflection_of_mem
  statement: (h : f x = 2)
  proof: by
  suffices forall y in p, reflection h y in p from
    (End.mem_invtSubmodule _).mpr fun y hy => by simpa using this y hy
  intro y hy
  simpa only [reflection_apply, p.sub_mem_iff_right hy] using p.smul_mem (f y) hx

中文:
引理 _root_.子模.mem_invtSubmodule_reflection_of_mem
  结论: (h : f x = 2)
  证明: by
  suffices forall y in p, reflection h y in p from
    (End.mem_invtSubmodule _).mpr fun y hy => by simpa using this y hy
  intro y hy
  simpa only [reflection_apply, p.sub_mem_iff_right hy] using p.smul_mem (f y) hx

Depends on / 依赖: End.mem_invtSubmodule, mem_invtSubmodule, p.smul_mem, p.sub_mem_iff_right, reflection, reflection_apply, smul_mem, sub_mem_iff_right
-/
lemma _root_.Submodule.mem_invtSubmodule_reflection_of_mem (h : f x = 2)
    (p : Submodule R M) (hx : x in p) :
    p in End.invtSubmodule (reflection h) := by
  suffices forall y in p, reflection h y in p from
    (End.mem_invtSubmodule _).mpr fun y hy => by simpa using this y hy
  intro y hy
  simpa only [reflection_apply, p.sub_mem_iff_right hy] using p.smul_mem (f y) hx

/--
lemma `_root_.Submodule.mem_invtSubmodule_reflection_iff` / 引理 `_root_.Submodule.mem_invtSubmodule_reflection_iff`

English:
lemma _root_.Submodule.mem_invtSubmodule_reflection_iff
  statement: [IsDomain R] [NeZero (2 : R)]
  proof: by
  refine ⟨fun h' y hy => ?_, fun h' y hy => ?_⟩
· have hx : x != 0 := by rintro rfl; exact two_ne_zero (α := R) by simp [← h]
    suffices f y • x in p by
      have aux : f y • x in p ⊓ R ∙ x := ⟨this, Submodule.mem_span_singleton.mpr ⟨f y, rfl⟩⟩
      rw [hp.eq_bot]; rw [Submodule.mem_bot]; rw [smul_eq_zero] at aux
      exact aux.resolve_right hx
    specialize h' hy
    simp only [Submodule.mem_comap, LinearEquiv.coe_coe, reflection_apply] at h'
    simpa using p.sub_mem h' hy
  · have hy' : f y = 0 := by simpa using h' hy
    simpa [reflection_apply, hy']

中文:
引理 _root_.子模.mem_invtSubmodule_reflection_iff
  结论: [是整环 R] [NeZero (2 : R)]
  证明: by
  refine ⟨fun h' y hy => ?_, fun h' y hy => ?_⟩
· have hx : x != 0 := by rintro rfl; exact two_ne_zero (α := R) by simp [← h]
    suffices f y • x in p by
      have aux : f y • x in p ⊓ R ∙ x := ⟨this, Submodule.mem_span_singleton.mpr ⟨f y, rfl⟩⟩
      rw [hp.eq_bot]; rw [Submodule.mem_bot]; rw [smul_eq_zero] at aux
      exact aux.resolve_right hx
    specialize h' hy
    simp only [Submodule.mem_comap, LinearEquiv.coe_coe, reflection_apply] at h'
    simpa using p.sub_mem h' hy
  · have hy' : f y = 0 := by simpa using h' hy
    simpa [reflection_apply, hy']

Depends on / 依赖: LinearEquiv, LinearEquiv.coe_coe, Submodule, Submodule.mem_bot, Submodule.mem_comap, Submodule.mem_span_singleton.mpr, aux.resolve_right, coe_coe, eq_bot, hp.eq_bot, mem_bot, mem_comap, mem_span_singleton, p.sub_mem, reflection_apply, resolve_right, smul_eq_zero, specialize, sub_mem, two_ne_zero
-/
lemma _root_.Submodule.mem_invtSubmodule_reflection_iff [IsDomain R] [NeZero (2 : R)]
    [IsTorsionFree R M] (h : f x = 2) {p : Submodule R M} (hp : Disjoint p (R ∙ x)) :
    p in End.invtSubmodule (reflection h) ↔ p <= LinearMap.ker f := by
  refine ⟨fun h' y hy => ?_, fun h' y hy => ?_⟩
· have hx : x != 0 := by rintro rfl; exact two_ne_zero (α := R) by simp [← h]
    suffices f y • x in p by
      have aux : f y • x in p ⊓ R ∙ x := ⟨this, Submodule.mem_span_singleton.mpr ⟨f y, rfl⟩⟩
      rw [hp.eq_bot]; rw [Submodule.mem_bot]; rw [smul_eq_zero] at aux
      exact aux.resolve_right hx
    specialize h' hy
    simp only [Submodule.mem_comap, LinearEquiv.coe_coe, reflection_apply] at h'
    simpa using p.sub_mem h' hy
  · have hy' : f y = 0 := by simpa using h' hy
    simpa [reflection_apply, hy']

/-! ### Powers of the product of two reflections

Let $M$ be a module over a commutative ring $R$. Let $x, y \in M$ and $f, g \in M^*$ with
$f(x) = g(y) = 2$. The corresponding reflections $r_1, r_2 \colon M \to M$ (`Module.reflection`) are
given by $r_1z = z - f(z) x$ and $r_2 z = z - g(z) y$. These are linear automorphisms of $M$.

To define reflection representations of a Coxeter group, it is important to be able to compute the
order of the composition $r_1 r_2$.

Note that if $M$ is a real inner product space and $r_1$ and $r_2$ are both orthogonal
reflections (i.e. $f(z) = 2 \langle x, z \rangle / \langle x, x \rangle$ and
$g(z) = 2 \langle y, z\rangle / \langle y, y\rangle$ for all $z \in M$),
then $r_1 r_2$ is a rotation by the angle
$$\cos^{-1}\left(\frac{f(y) g(x) - 2}{2}\right)$$
and one may determine the order of $r_1 r_2$ accordingly.

However, if $M$ does not have an inner product, and even if $R$ is not $\mathbb{R}$, then we may
instead use the formulas in this section. These formulas all involve evaluating Chebyshev
$S$-polynomials (`Polynomial.Chebyshev.S`) at $t = f(y) g(x) - 2$, and they hold over any
commutative ring. -/
section

open Int Polynomial.Chebyshev

variable {x y : M} {f g : Dual R M} (hf : f x = 2) (hg : g y = 2)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `reflection_mul_reflection_pow_apply` / 引理 `reflection_mul_reflection_pow_apply`

English:
lemma reflection_mul_reflection_pow_apply
  statement: (m : Nat) (z : M)
  proof: by
  induction m with
  | zero => simp
  | succ m ih =>
    /- Now, let us collect two facts about the evaluations of `S r k`. These easily follow from the
    properties of the `S` polynomials. -/
    have S_eval_t_sub_two (k : Int) :
        (S R (k - 2)).eval t = t * (S R (k - 1)).eval t - (S R k).eval t := by
      simp [S_sub_two]
    have S_eval_t_sq_add_S_eval_t_sq (k : Int) :
        (S R k).eval t ^ 2 + (S R (k + 1)).eval t ^ 2 - t * (S R k).eval t * (S R (k + 1)).eval t
        = 1 := by
      simpa using congr_arg (Polynomial.eval t) (S_sq_add_S_sq R k)
    -- Apply the inductive hypothesis.
    rw [pow_succ']; rw [LinearEquiv.mul_apply]; rw [ih]; rw [LinearEquiv.mul_apply]
    -- Expand out all the reflections and use `hf`, `hg`.
    simp only [reflection_apply, map_add, map_sub, map_smul, hf, hg]
    -- `m` can be written in the form `2 * k + e`, where `e` is `0` or `1`.
    push_cast
    rw [← Int.mul_ediv_add_emod m 2]
    set k : Int := m / 2
    set e : Int := m % 2
    simp_rw [add_assoc (2 * k), add_sub_assoc (2 * k), add_comm (2 * k),
      add_mul_ediv_left _ k (by simp : (2 : Int) != 0)]
    have he : e = 0 ∨ e = 1 := by lia
    clear_value e
    /- Now, equate the coefficients on both sides. These linear combinations were
    found using `polyrith`. -/
    match_scalars
    · rfl
    · linear_combination (norm := skip) (-g z * f y * (S R (e - 1 + k)).eval t +
          f z * (S R (e - 1 + k)).eval t) * S_eval_t_sub_two (e + k) +
          (-g z * f y + f z) * S_eval_t_sq_add_S_eval_t_sq (k - 1)
      subst ht
      obtain rfl | rfl : e = 0 ∨ e = 1 := he <;> ring_nf
    · linear_combination (norm := skip)
          g z * (S R (e - 1 + k)).eval t * S_eval_t_sub_two (e + k) +
          g z * S_eval_t_sq_add_S_eval_t_sq (k - 1)
      subst ht
      obtain rfl | rfl : e = 0 ∨ e = 1 := he <;> ring_nf

中文:
引理 reflection_mul_reflection_pow_apply
  结论: (m : 自然数) (z : M)
  证明: by
  induction m with
  | zero => simp
  | succ m ih =>
    /- Now, let us collect two facts about the evaluations of `S r k`. These easily follow from the
    properties of the `S` polynomials. -/
    have S_eval_t_sub_two (k : Int) :
        (S R (k - 2)).eval t = t * (S R (k - 1)).eval t - (S R k).eval t := by
      simp [S_sub_two]
    have S_eval_t_sq_add_S_eval_t_sq (k : Int) :
        (S R k).eval t ^ 2 + (S R (k + 1)).eval t ^ 2 - t * (S R k).eval t * (S R (k + 1)).eval t
        = 1 := by
      simpa using congr_arg (Polynomial.eval t) (S_sq_add_S_sq R k)
    -- Apply the inductive hypothesis.
    rw [pow_succ']; rw [LinearEquiv.mul_apply]; rw [ih]; rw [LinearEquiv.mul_apply]
    -- Expand out all the reflections and use `hf`, `hg`.
    simp only [reflection_apply, map_add, map_sub, map_smul, hf, hg]
    -- `m` can be written in the form `2 * k + e`, where `e` is `0` or `1`.
    push_cast
    rw [← Int.mul_ediv_add_emod m 2]
    set k : Int := m / 2
    set e : Int := m % 2
    simp_rw [add_assoc (2 * k), add_sub_assoc (2 * k), add_comm (2 * k),
      add_mul_ediv_left _ k (by simp : (2 : Int) != 0)]
    have he : e = 0 ∨ e = 1 := by lia
    clear_value e
    /- Now, equate the coefficients on both sides. These linear combinations were
    found using `polyrith`. -/
    match_scalars
    · rfl
    · linear_combination (norm := skip) (-g z * f y * (S R (e - 1 + k)).eval t +
          f z * (S R (e - 1 + k)).eval t) * S_eval_t_sub_two (e + k) +
          (-g z * f y + f z) * S_eval_t_sq_add_S_eval_t_sq (k - 1)
      subst ht
      obtain rfl | rfl : e = 0 ∨ e = 1 := he <;> ring_nf
    · linear_combination (norm := skip)
          g z * (S R (e - 1 + k)).eval t * S_eval_t_sub_two (e + k) +
          g z * S_eval_t_sq_add_S_eval_t_sq (k - 1)
      subst ht
      obtain rfl | rfl : e = 0 ∨ e = 1 := he <;> ring_nf
-/
lemma reflection_mul_reflection_pow_apply (m : Nat) (z : M)
    (t : R := f y * g x - 2) (ht : t = f y * g x - 2 := by rfl) :
    ((reflection hf * reflection hg) ^ m) z =
      z +
        ((S R ((m - 2) / 2)).eval t * ((S R ((m - 1) / 2)).eval t + (S R ((m - 3) / 2)).eval t)) •
          ((g x * f z - g z) • y - f z • x) +
        ((S R ((m - 1) / 2)).eval t * ((S R (m / 2)).eval t + (S R ((m - 2) / 2)).eval t)) •
          ((f y * g z - f z) • x - g z • y) := by
  induction m with
  | zero => simp
  | succ m ih =>
    /- Now, let us collect two facts about the evaluations of `S r k`. These easily follow from the
    properties of the `S` polynomials. -/
    have S_eval_t_sub_two (k : Int) :
        (S R (k - 2)).eval t = t * (S R (k - 1)).eval t - (S R k).eval t := by
      simp [S_sub_two]
    have S_eval_t_sq_add_S_eval_t_sq (k : Int) :
        (S R k).eval t ^ 2 + (S R (k + 1)).eval t ^ 2 - t * (S R k).eval t * (S R (k + 1)).eval t
        = 1 := by
      simpa using congr_arg (Polynomial.eval t) (S_sq_add_S_sq R k)
    -- Apply the inductive hypothesis.
    rw [pow_succ']; rw [LinearEquiv.mul_apply]; rw [ih]; rw [LinearEquiv.mul_apply]
    -- Expand out all the reflections and use `hf`, `hg`.
    simp only [reflection_apply, map_add, map_sub, map_smul, hf, hg]
    -- `m` can be written in the form `2 * k + e`, where `e` is `0` or `1`.
    push_cast
    rw [← Int.mul_ediv_add_emod m 2]
    set k : Int := m / 2
    set e : Int := m % 2
    simp_rw [add_assoc (2 * k), add_sub_assoc (2 * k), add_comm (2 * k),
      add_mul_ediv_left _ k (by simp : (2 : Int) != 0)]
    have he : e = 0 ∨ e = 1 := by lia
    clear_value e
    /- Now, equate the coefficients on both sides. These linear combinations were
    found using `polyrith`. -/
    match_scalars
    · rfl
    · linear_combination (norm := skip) (-g z * f y * (S R (e - 1 + k)).eval t +
          f z * (S R (e - 1 + k)).eval t) * S_eval_t_sub_two (e + k) +
          (-g z * f y + f z) * S_eval_t_sq_add_S_eval_t_sq (k - 1)
      subst ht
      obtain rfl | rfl : e = 0 ∨ e = 1 := he <;> ring_nf
    · linear_combination (norm := skip)
          g z * (S R (e - 1 + k)).eval t * S_eval_t_sub_two (e + k) +
          g z * S_eval_t_sq_add_S_eval_t_sq (k - 1)
      subst ht
      obtain rfl | rfl : e = 0 ∨ e = 1 := he <;> ring_nf

/--
lemma `reflection_mul_reflection_pow` / 引理 `reflection_mul_reflection_pow`

English:
lemma reflection_mul_reflection_pow
  statement: (m : Nat)
  proof: by
  ext z
  simpa using reflection_mul_reflection_pow_apply hf hg m z t ht

中文:
引理 reflection_mul_reflection_pow
  结论: (m : 自然数)
  证明: by
  ext z
  simpa using reflection_mul_reflection_pow_apply hf hg m z t ht
-/
lemma reflection_mul_reflection_pow (m : Nat)
    (t : R := f y * g x - 2) (ht : t = f y * g x - 2 := by rfl) :
    ((reflection hf * reflection hg) ^ m).toLinearMap =
      LinearMap.id (R := R) (M := M) +
        ((S R ((m - 2) / 2)).eval t * ((S R ((m - 1) / 2)).eval t + (S R ((m - 3) / 2)).eval t)) •
          ((g x • f - g).smulRight y - f.smulRight x) +
        ((S R ((m - 1) / 2)).eval t * ((S R (m / 2)).eval t + (S R ((m - 2) / 2)).eval t)) •
          ((f y • g - f).smulRight x - g.smulRight y) := by
  ext z
  simpa using reflection_mul_reflection_pow_apply hf hg m z t ht

/--
lemma `reflection_mul_reflection_zpow_apply` / 引理 `reflection_mul_reflection_zpow_apply`

English:
lemma reflection_mul_reflection_zpow_apply
  statement: (m : Int) (z : M)
  proof: by
  induction m using Int.negInduction with
  | nat m => exact_mod_cast reflection_mul_reflection_pow_apply hf hg m z t ht
  | neg _ m =>
    have ht' : t = g x * f y - 2 := by rwa [mul_comm (g x)]
    rw [zpow_neg]; rw [← inv_zpow]; rw [mul_inv_rev]; rw [reflection_inv]; rw [reflection_inv]; rw [zpow_natCast]; rw [reflection_mul_reflection_pow_apply hg hf m z t ht']; rw [add_right_comm z]
    have aux (a b : Int) (hab : a + b = -3 := by lia) : a / 2 = -(b / 2) - 2 := by lia
    rw [aux (-m - 3) m]; rw [aux (-m - 2) (m - 1)]; rw [aux (-m - 1) (m - 2)]; rw [aux (-m) (m - 3)]
    simp only [S_neg_sub_two, Polynomial.eval_neg]
    ring_nf

中文:
引理 reflection_mul_reflection_zpow_apply
  结论: (m : 整数) (z : M)
  证明: by
  induction m using Int.negInduction with
  | nat m => exact_mod_cast reflection_mul_reflection_pow_apply hf hg m z t ht
  | neg _ m =>
    have ht' : t = g x * f y - 2 := by rwa [mul_comm (g x)]
    rw [zpow_neg]; rw [← inv_zpow]; rw [mul_inv_rev]; rw [reflection_inv]; rw [reflection_inv]; rw [zpow_natCast]; rw [reflection_mul_reflection_pow_apply hg hf m z t ht']; rw [add_right_comm z]
    have aux (a b : Int) (hab : a + b = -3 := by lia) : a / 2 = -(b / 2) - 2 := by lia
    rw [aux (-m - 3) m]; rw [aux (-m - 2) (m - 1)]; rw [aux (-m - 1) (m - 2)]; rw [aux (-m) (m - 3)]
    simp only [S_neg_sub_two, Polynomial.eval_neg]
    ring_nf
-/
lemma reflection_mul_reflection_zpow_apply (m : Int) (z : M)
    (t : R := f y * g x - 2) (ht : t = f y * g x - 2 := by rfl) :
    ((reflection hf * reflection hg) ^ m) z =
      z +
        ((S R ((m - 2) / 2)).eval t * ((S R ((m - 1) / 2)).eval t + (S R ((m - 3) / 2)).eval t)) •
          ((g x * f z - g z) • y - f z • x) +
        ((S R ((m - 1) / 2)).eval t * ((S R (m / 2)).eval t + (S R ((m - 2) / 2)).eval t)) •
          ((f y * g z - f z) • x - g z • y) := by
  induction m using Int.negInduction with
  | nat m => exact_mod_cast reflection_mul_reflection_pow_apply hf hg m z t ht
  | neg _ m =>
    have ht' : t = g x * f y - 2 := by rwa [mul_comm (g x)]
    rw [zpow_neg]; rw [← inv_zpow]; rw [mul_inv_rev]; rw [reflection_inv]; rw [reflection_inv]; rw [zpow_natCast]; rw [reflection_mul_reflection_pow_apply hg hf m z t ht']; rw [add_right_comm z]
    have aux (a b : Int) (hab : a + b = -3 := by lia) : a / 2 = -(b / 2) - 2 := by lia
    rw [aux (-m - 3) m]; rw [aux (-m - 2) (m - 1)]; rw [aux (-m - 1) (m - 2)]; rw [aux (-m) (m - 3)]
    simp only [S_neg_sub_two, Polynomial.eval_neg]
    ring_nf

/--
lemma `reflection_mul_reflection_zpow` / 引理 `reflection_mul_reflection_zpow`

English:
lemma reflection_mul_reflection_zpow
  statement: (m : Int)
  proof: by
  ext z
  simpa using reflection_mul_reflection_zpow_apply hf hg m z t ht

中文:
引理 reflection_mul_reflection_zpow
  结论: (m : 整数)
  证明: by
  ext z
  simpa using reflection_mul_reflection_zpow_apply hf hg m z t ht
-/
lemma reflection_mul_reflection_zpow (m : Int)
    (t : R := f y * g x - 2) (ht : t = f y * g x - 2 := by rfl) :
    ((reflection hf * reflection hg) ^ m).toLinearMap =
      LinearMap.id (R := R) (M := M) +
        ((S R ((m - 2) / 2)).eval t * ((S R ((m - 1) / 2)).eval t + (S R ((m - 3) / 2)).eval t)) •
          ((g x • f - g).smulRight y - f.smulRight x) +
        ((S R ((m - 1) / 2)).eval t * ((S R (m / 2)).eval t + (S R ((m - 2) / 2)).eval t)) •
          ((f y • g - f).smulRight x - g.smulRight y) := by
  ext z
  simpa using reflection_mul_reflection_zpow_apply hf hg m z t ht

set_option backward.isDefEq.respectTransparency false in
/--
lemma `reflection_mul_reflection_zpow_apply_self` / 引理 `reflection_mul_reflection_zpow_apply_self`

English:
lemma reflection_mul_reflection_zpow_apply_self
  statement: (m : Int)
  proof: by
  /- Even though this is a special case of `Module.reflection_mul_reflection_zpow_apply`, it is
  easier to prove it from scratch. -/
  have S_eval_t_sub_two (k : Int) :
      (S R (k - 2)).eval t = (f y * g x - 2) * (S R (k - 1)).eval t - (S R k).eval t := by
    simp [S_sub_two, ht]
  induction m with
  | zero => simp
  | succ m ih =>
    -- Apply the inductive hypothesis.
    rw [add_comm (m : Int) 1]; rw [zpow_one_add]; rw [LinearEquiv.mul_apply]; rw [LinearEquiv.mul_apply]; rw [ih]
    -- Expand out all the reflections and use `hf`, `hg`.
    simp only [reflection_apply, map_add, map_sub, map_smul, hf, hg]
    -- Equate coefficients of `x` and `y`.
    match_scalars
    · linear_combination (norm := ring_nf) -S_eval_t_sub_two (m + 1)
    · ring_nf
  | pred m ih =>
    -- Apply the inductive hypothesis.
    rw [sub_eq_add_neg (-m : Int) 1]; rw [add_comm (-m : Int) (-1)]; rw [zpow_add]; rw [zpow_neg_one]; rw [mul_inv_rev]; rw [reflection_inv]; rw [reflection_inv]; rw [LinearEquiv.mul_apply]; rw [LinearEquiv.mul_apply]; rw [ih]
    -- Expand out all the reflections and use `hf`, `hg`.
    simp only [reflection_apply, map_add, map_sub, map_smul, hf, hg]
    -- Equate coefficients of `x` and `y`.
    match_scalars
    · linear_combination (norm := ring_nf) -S_eval_t_sub_two (-m)
    · linear_combination (norm := ring_nf) g x * S_eval_t_sub_two (-m)

中文:
引理 reflection_mul_reflection_zpow_apply_self
  结论: (m : 整数)
  证明: by
  /- Even though this is a special case of `Module.reflection_mul_reflection_zpow_apply`, it is
  easier to prove it from scratch. -/
  have S_eval_t_sub_two (k : Int) :
      (S R (k - 2)).eval t = (f y * g x - 2) * (S R (k - 1)).eval t - (S R k).eval t := by
    simp [S_sub_two, ht]
  induction m with
  | zero => simp
  | succ m ih =>
    -- Apply the inductive hypothesis.
    rw [add_comm (m : Int) 1]; rw [zpow_one_add]; rw [LinearEquiv.mul_apply]; rw [LinearEquiv.mul_apply]; rw [ih]
    -- Expand out all the reflections and use `hf`, `hg`.
    simp only [reflection_apply, map_add, map_sub, map_smul, hf, hg]
    -- Equate coefficients of `x` and `y`.
    match_scalars
    · linear_combination (norm := ring_nf) -S_eval_t_sub_two (m + 1)
    · ring_nf
  | pred m ih =>
    -- Apply the inductive hypothesis.
    rw [sub_eq_add_neg (-m : Int) 1]; rw [add_comm (-m : Int) (-1)]; rw [zpow_add]; rw [zpow_neg_one]; rw [mul_inv_rev]; rw [reflection_inv]; rw [reflection_inv]; rw [LinearEquiv.mul_apply]; rw [LinearEquiv.mul_apply]; rw [ih]
    -- Expand out all the reflections and use `hf`, `hg`.
    simp only [reflection_apply, map_add, map_sub, map_smul, hf, hg]
    -- Equate coefficients of `x` and `y`.
    match_scalars
    · linear_combination (norm := ring_nf) -S_eval_t_sub_two (-m)
    · linear_combination (norm := ring_nf) g x * S_eval_t_sub_two (-m)
-/
lemma reflection_mul_reflection_zpow_apply_self (m : Int)
    (t : R := f y * g x - 2) (ht : t = f y * g x - 2 := by rfl) :
    ((reflection hf * reflection hg) ^ m) x =
      ((S R m).eval t + (S R (m - 1)).eval t) • x + ((S R (m - 1)).eval t * -g x) • y := by
  /- Even though this is a special case of `Module.reflection_mul_reflection_zpow_apply`, it is
  easier to prove it from scratch. -/
  have S_eval_t_sub_two (k : Int) :
      (S R (k - 2)).eval t = (f y * g x - 2) * (S R (k - 1)).eval t - (S R k).eval t := by
    simp [S_sub_two, ht]
  induction m with
  | zero => simp
  | succ m ih =>
    -- Apply the inductive hypothesis.
    rw [add_comm (m : Int) 1]; rw [zpow_one_add]; rw [LinearEquiv.mul_apply]; rw [LinearEquiv.mul_apply]; rw [ih]
    -- Expand out all the reflections and use `hf`, `hg`.
    simp only [reflection_apply, map_add, map_sub, map_smul, hf, hg]
    -- Equate coefficients of `x` and `y`.
    match_scalars
    · linear_combination (norm := ring_nf) -S_eval_t_sub_two (m + 1)
    · ring_nf
  | pred m ih =>
    -- Apply the inductive hypothesis.
    rw [sub_eq_add_neg (-m : Int) 1]; rw [add_comm (-m : Int) (-1)]; rw [zpow_add]; rw [zpow_neg_one]; rw [mul_inv_rev]; rw [reflection_inv]; rw [reflection_inv]; rw [LinearEquiv.mul_apply]; rw [LinearEquiv.mul_apply]; rw [ih]
    -- Expand out all the reflections and use `hf`, `hg`.
    simp only [reflection_apply, map_add, map_sub, map_smul, hf, hg]
    -- Equate coefficients of `x` and `y`.
    match_scalars
    · linear_combination (norm := ring_nf) -S_eval_t_sub_two (-m)
    · linear_combination (norm := ring_nf) g x * S_eval_t_sub_two (-m)

/--
lemma `reflection_mul_reflection_pow_apply_self` / 引理 `reflection_mul_reflection_pow_apply_self`

English:
lemma reflection_mul_reflection_pow_apply_self
  statement: (m : Nat)
  proof: mod_cast reflection_mul_reflection_zpow_apply_self hf hg m t ht

中文:
引理 reflection_mul_reflection_pow_apply_self
  结论: (m : 自然数)
  证明: mod_cast reflection_mul_reflection_zpow_apply_self hf hg m t ht
-/
lemma reflection_mul_reflection_pow_apply_self (m : Nat)
    (t : R := f y * g x - 2) (ht : t = f y * g x - 2 := by rfl) :
    ((reflection hf * reflection hg) ^ m) x =
      ((S R m).eval t + (S R (m - 1)).eval t) • x + ((S R (m - 1)).eval t * -g x) • y :=
  mod_cast reflection_mul_reflection_zpow_apply_self hf hg m t ht

set_option backward.isDefEq.respectTransparency false in
/--
lemma `reflection_mul_reflection_mul_reflection_zpow_apply_self` / 引理 `reflection_mul_reflection_mul_reflection_zpow_apply_self`

English:
lemma reflection_mul_reflection_mul_reflection_zpow_apply_self
  statement: (m : Int)
  proof: by
  rw [LinearEquiv.mul_apply]; rw [reflection_mul_reflection_zpow_apply_self hf hg m t ht]
  -- Expand out all the reflections and use `hf`, `hg`.
  simp only [reflection_apply, map_add, map_smul, hg]
  -- Equate coefficients of `x` and `y`.
  module

中文:
引理 reflection_mul_reflection_mul_reflection_zpow_apply_self
  结论: (m : 整数)
  证明: by
  rw [LinearEquiv.mul_apply]; rw [reflection_mul_reflection_zpow_apply_self hf hg m t ht]
  -- Expand out all the reflections and use `hf`, `hg`.
  simp only [reflection_apply, map_add, map_smul, hg]
  -- Equate coefficients of `x` and `y`.
  module
-/
lemma reflection_mul_reflection_mul_reflection_zpow_apply_self (m : Int)
    (t : R := f y * g x - 2) (ht : t = f y * g x - 2 := by rfl) :
    (reflection hg * (reflection hf * reflection hg) ^ m) x =
      ((S R m).eval t + (S R (m - 1)).eval t) • x + ((S R m).eval t * -g x) • y := by
  rw [LinearEquiv.mul_apply]; rw [reflection_mul_reflection_zpow_apply_self hf hg m t ht]
  -- Expand out all the reflections and use `hf`, `hg`.
  simp only [reflection_apply, map_add, map_smul, hg]
  -- Equate coefficients of `x` and `y`.
  module

/--
lemma `reflection_mul_reflection_mul_reflection_pow_apply_self` / 引理 `reflection_mul_reflection_mul_reflection_pow_apply_self`

English:
lemma reflection_mul_reflection_mul_reflection_pow_apply_self
  statement: (m : Nat)
  proof: mod_cast reflection_mul_reflection_mul_reflection_zpow_apply_self hf hg m t ht

中文:
引理 reflection_mul_reflection_mul_reflection_pow_apply_self
  结论: (m : 自然数)
  证明: mod_cast reflection_mul_reflection_mul_reflection_zpow_apply_self hf hg m t ht
-/
lemma reflection_mul_reflection_mul_reflection_pow_apply_self (m : Nat)
    (t : R := f y * g x - 2) (ht : t = f y * g x - 2 := by rfl) :
    (reflection hg * (reflection hf * reflection hg) ^ m) x =
      ((S R m).eval t + (S R (m - 1)).eval t) • x + ((S R m).eval t * -g x) • y :=
  mod_cast reflection_mul_reflection_mul_reflection_zpow_apply_self hf hg m t ht

end

/-! ### Lemmas used to prove uniqueness results for root data -/

set_option backward.isDefEq.respectTransparency false in
/--
lemma `Dual.eq_of_preReflection_mapsTo` / 引理 `Dual.eq_of_preReflection_mapsTo`

English:
lemma Dual.eq_of_preReflection_mapsTo
  statement: [CharZero R] [IsDomain R] [IsTorsionFree R M]
  proof: by
  have hx : x != 0 := by rintro rfl; simp at hf₁
  let u := reflection hg₁ * reflection hf₁
  have hu : u = LinearMap.id (R := R) (M := M) + (f - g).smulRight x := by
    ext y
    simp only [u, reflection_apply, hg₁, two_smul, LinearEquiv.coe_toLinearMap_mul,
      LinearMap.id_coe, LinearEquiv.coe_coe, Module.End.mul_apply, LinearMap.add_apply, id_eq,
      LinearMap.coe_smulRight, LinearMap.sub_apply, map_sub, map_smul, sub_add_cancel_left,
      smul_neg, sub_neg_eq_add, sub_smul]
    abel
  replace hu : forall (n : Nat),
      ↑(u ^ n) = LinearMap.id (R := R) (M := M) + (n : R) • (f - g).smulRight x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have : ((f - g).smulRight x).comp ((n : R) • (f - g).smulRight x) = 0 := by
        ext; simp [hf₁, hg₁]
      rw [pow_succ']; rw [LinearEquiv.coe_toLinearMap_mul]; rw [ih]; rw [hu]; rw [add_mul]; rw [mul_add]; rw [mul_add]
      simp_rw [Module.End.mul_eq_comp, LinearMap.comp_id, LinearMap.id_comp, this, add_zero,
        add_assoc, Nat.cast_succ, add_smul, one_smul]
  suffices IsOfFinOrder u by
    obtain ⟨n, hn₀, hn₁⟩ := isOfFinOrder_iff_pow_eq_one.mp this
    replace hn₁ : (↑(u ^ n) : M ->ₗ[R] M) = LinearMap.id := LinearEquiv.toLinearMap_inj.mpr hn₁
    simpa [hn₁, hn₀.ne', hx, sub_eq_zero] using hu n
  exact u.isOfFinOrder_of_finite_of_span_eq_top_of_mapsTo hΦ₁ hΦ₂ (hg₂.comp hf₂)

中文:
引理 对偶.eq_of_preReflection_mapsTo
  结论: [特征零 R] [是整环 R] [是无挠 R M]
  证明: by
  have hx : x != 0 := by rintro rfl; simp at hf₁
  let u := reflection hg₁ * reflection hf₁
  have hu : u = LinearMap.id (R := R) (M := M) + (f - g).smulRight x := by
    ext y
    simp only [u, reflection_apply, hg₁, two_smul, LinearEquiv.coe_toLinearMap_mul,
      LinearMap.id_coe, LinearEquiv.coe_coe, Module.End.mul_apply, LinearMap.add_apply, id_eq,
      LinearMap.coe_smulRight, LinearMap.sub_apply, map_sub, map_smul, sub_add_cancel_left,
      smul_neg, sub_neg_eq_add, sub_smul]
    abel
  replace hu : forall (n : Nat),
      ↑(u ^ n) = LinearMap.id (R := R) (M := M) + (n : R) • (f - g).smulRight x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have : ((f - g).smulRight x).comp ((n : R) • (f - g).smulRight x) = 0 := by
        ext; simp [hf₁, hg₁]
      rw [pow_succ']; rw [LinearEquiv.coe_toLinearMap_mul]; rw [ih]; rw [hu]; rw [add_mul]; rw [mul_add]; rw [mul_add]
      simp_rw [Module.End.mul_eq_comp, LinearMap.comp_id, LinearMap.id_comp, this, add_zero,
        add_assoc, Nat.cast_succ, add_smul, one_smul]
  suffices IsOfFinOrder u by
    obtain ⟨n, hn₀, hn₁⟩ := isOfFinOrder_iff_pow_eq_one.mp this
    replace hn₁ : (↑(u ^ n) : M ->ₗ[R] M) = LinearMap.id := LinearEquiv.toLinearMap_inj.mpr hn₁
    simpa [hn₁, hn₀.ne', hx, sub_eq_zero] using hu n
  exact u.isOfFinOrder_of_finite_of_span_eq_top_of_mapsTo hΦ₁ hΦ₂ (hg₂.comp hf₂)

Depends on / 依赖: LinearEquiv, LinearEquiv.coe_coe, LinearEquiv.coe_toLinearMap_mul, LinearMap, LinearMap.add_apply, LinearMap.coe_smulRight, LinearMap.id, LinearMap.id_coe, LinearMap.sub_apply, Module, Module.End.mul_apply, add_apply, coe_coe, coe_smulRight, coe_toLinearMap_mul, id_coe, id_eq, map_smul, map_sub, mul_apply
-/
lemma Dual.eq_of_preReflection_mapsTo [CharZero R] [IsDomain R] [IsTorsionFree R M]
    {x : M} {Φ : Set M} (hΦ₁ : Φ.Finite) (hΦ₂ : span R Φ = ⊤) {f g : Dual R M}
    (hf₁ : f x = 2) (hf₂ : MapsTo (preReflection x f) Φ Φ)
    (hg₁ : g x = 2) (hg₂ : MapsTo (preReflection x g) Φ Φ) :
    f = g := by
  have hx : x != 0 := by rintro rfl; simp at hf₁
  let u := reflection hg₁ * reflection hf₁
  have hu : u = LinearMap.id (R := R) (M := M) + (f - g).smulRight x := by
    ext y
    simp only [u, reflection_apply, hg₁, two_smul, LinearEquiv.coe_toLinearMap_mul,
      LinearMap.id_coe, LinearEquiv.coe_coe, Module.End.mul_apply, LinearMap.add_apply, id_eq,
      LinearMap.coe_smulRight, LinearMap.sub_apply, map_sub, map_smul, sub_add_cancel_left,
      smul_neg, sub_neg_eq_add, sub_smul]
    abel
  replace hu : forall (n : Nat),
      ↑(u ^ n) = LinearMap.id (R := R) (M := M) + (n : R) • (f - g).smulRight x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have : ((f - g).smulRight x).comp ((n : R) • (f - g).smulRight x) = 0 := by
        ext; simp [hf₁, hg₁]
      rw [pow_succ']; rw [LinearEquiv.coe_toLinearMap_mul]; rw [ih]; rw [hu]; rw [add_mul]; rw [mul_add]; rw [mul_add]
      simp_rw [Module.End.mul_eq_comp, LinearMap.comp_id, LinearMap.id_comp, this, add_zero,
        add_assoc, Nat.cast_succ, add_smul, one_smul]
  suffices IsOfFinOrder u by
    obtain ⟨n, hn₀, hn₁⟩ := isOfFinOrder_iff_pow_eq_one.mp this
    replace hn₁ : (↑(u ^ n) : M ->ₗ[R] M) = LinearMap.id := LinearEquiv.toLinearMap_inj.mpr hn₁
    simpa [hn₁, hn₀.ne', hx, sub_eq_zero] using hu n
  exact u.isOfFinOrder_of_finite_of_span_eq_top_of_mapsTo hΦ₁ hΦ₂ (hg₂.comp hf₂)

/--
lemma `Dual.eq_of_preReflection_mapsTo'` / 引理 `Dual.eq_of_preReflection_mapsTo'`

English:
lemma Dual.eq_of_preReflection_mapsTo'
  statement: [CharZero R] [IsDomain R] [IsTorsionFree R M]
  proof: by
  set Φ' : Set (span R Φ) := range (inclusion <| Submodule.subset_span (R := R) (s := Φ))
  rw [← finite_coe_iff] at hΦ₁
  have hΦ'₁ : Φ'.Finite := finite_range (inclusion Submodule.subset_span)
  have hΦ'₂ : span R Φ' = ⊤ := by
    simp only [Φ']
    rw [range_inclusion]
    simp
  let x' : span R Φ := ⟨x, hx⟩
  have : forall {F : Dual R M}, MapsTo (preReflection x F) Φ Φ ->
      MapsTo (preReflection x' ((span R Φ).subtype.dualMap F)) Φ' Φ' := by
    intro F hF ⟨y, hy⟩ hy'
    simp only [Φ'] at hy' ⊢
    rw [range_inclusion] at hy'
    simp only [SetLike.coe_sort_coe, mem_ofPred_eq] at hy' ⊢
    rw [range_inclusion]
    exact hF hy'
  exact eq_of_preReflection_mapsTo hΦ'₁ hΦ'₂ hf₁ (this hf₂) hg₁ (this hg₂)

中文:
引理 对偶.eq_of_preReflection_mapsTo'
  结论: [特征零 R] [是整环 R] [是无挠 R M]
  证明: by
  set Φ' : Set (span R Φ) := range (inclusion <| Submodule.subset_span (R := R) (s := Φ))
  rw [← finite_coe_iff] at hΦ₁
  have hΦ'₁ : Φ'.Finite := finite_range (inclusion Submodule.subset_span)
  have hΦ'₂ : span R Φ' = ⊤ := by
    simp only [Φ']
    rw [range_inclusion]
    simp
  let x' : span R Φ := ⟨x, hx⟩
  have : forall {F : Dual R M}, MapsTo (preReflection x F) Φ Φ ->
      MapsTo (preReflection x' ((span R Φ).subtype.dualMap F)) Φ' Φ' := by
    intro F hF ⟨y, hy⟩ hy'
    simp only [Φ'] at hy' ⊢
    rw [range_inclusion] at hy'
    simp only [SetLike.coe_sort_coe, mem_ofPred_eq] at hy' ⊢
    rw [range_inclusion]
    exact hF hy'
  exact eq_of_preReflection_mapsTo hΦ'₁ hΦ'₂ hf₁ (this hf₂) hg₁ (this hg₂)

Depends on / 依赖: Finite, MapsTo, Submodule, Submodule.subset_span, dualMap, finite_coe_iff, finite_range, inclusion, preReflection, range_inclusion, subset_span, subtype, subtype.dualMap
-/
lemma Dual.eq_of_preReflection_mapsTo' [CharZero R] [IsDomain R] [IsTorsionFree R M]
    {x : M} {Φ : Set M} (hΦ₁ : Φ.Finite) (hx : x in span R Φ) {f g : Dual R M}
    (hf₁ : f x = 2) (hf₂ : MapsTo (preReflection x f) Φ Φ)
    (hg₁ : g x = 2) (hg₂ : MapsTo (preReflection x g) Φ Φ) :
    (span R Φ).subtype.dualMap f = (span R Φ).subtype.dualMap g := by
  set Φ' : Set (span R Φ) := range (inclusion <| Submodule.subset_span (R := R) (s := Φ))
  rw [← finite_coe_iff] at hΦ₁
  have hΦ'₁ : Φ'.Finite := finite_range (inclusion Submodule.subset_span)
  have hΦ'₂ : span R Φ' = ⊤ := by
    simp only [Φ']
    rw [range_inclusion]
    simp
  let x' : span R Φ := ⟨x, hx⟩
  have : forall {F : Dual R M}, MapsTo (preReflection x F) Φ Φ ->
      MapsTo (preReflection x' ((span R Φ).subtype.dualMap F)) Φ' Φ' := by
    intro F hF ⟨y, hy⟩ hy'
    simp only [Φ'] at hy' ⊢
    rw [range_inclusion] at hy'
    simp only [SetLike.coe_sort_coe, mem_ofPred_eq] at hy' ⊢
    rw [range_inclusion]
    exact hF hy'
  exact eq_of_preReflection_mapsTo hΦ'₁ hΦ'₂ hf₁ (this hf₂) hg₁ (this hg₂)

variable {y}
variable {g : Dual R M}

set_option backward.isDefEq.respectTransparency false in
/--
lemma `reflection_reflection_iterate` / 引理 `reflection_reflection_iterate`

English:
lemma reflection_reflection_iterate
  proof: by
  induction n with
  | zero => simp
  | succ n ih =>
    have hz : forall z : M, f y • g x • z = 2 • 2 • z := by
      intro z
      rw [smul_smul]; rw [hgxfy]; rw [smul_smul]; rw [← Nat.cast_smul_eq_nsmul R (2 * 2)]; rw [show 2 * 2 = 4 from rfl]; rw [Nat.cast_ofNat]
    simp only [iterate_succ', comp_apply, ih, two_smul, smul_sub, smul_add, map_add,
      LinearEquiv.trans_apply, reflection_apply_self, map_neg, reflection_apply, neg_sub, map_sub,
      map_nsmul, map_smul, smul_neg, hz, add_smul]
    abel

中文:
引理 reflection_reflection_iterate
  证明: by
  induction n with
  | zero => simp
  | succ n ih =>
    have hz : forall z : M, f y • g x • z = 2 • 2 • z := by
      intro z
      rw [smul_smul]; rw [hgxfy]; rw [smul_smul]; rw [← Nat.cast_smul_eq_nsmul R (2 * 2)]; rw [show 2 * 2 = 4 from rfl]; rw [Nat.cast_ofNat]
    simp only [iterate_succ', comp_apply, ih, two_smul, smul_sub, smul_add, map_add,
      LinearEquiv.trans_apply, reflection_apply_self, map_neg, reflection_apply, neg_sub, map_sub,
      map_nsmul, map_smul, smul_neg, hz, add_smul]
    abel

Depends on / 依赖: LinearEquiv, LinearEquiv.trans_apply, Nat.cast_ofNat, Nat.cast_smul_eq_nsmul, add_smul, cast_ofNat, cast_smul_eq_nsmul, comp_apply, iterate_succ, map_add, map_neg, map_nsmul, map_smul, map_sub, neg_sub, reflection_apply, reflection_apply_self, smul_add, smul_neg, smul_smul
-/
lemma reflection_reflection_iterate
    (hfx : f x = 2) (hgy : g y = 2) (hgxfy : f y * g x = 4) (n : Nat) :
    ((reflection hgy).trans (reflection hfx))^[n] y = y + n • (f y • x - (2 : R) • y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hz : forall z : M, f y • g x • z = 2 • 2 • z := by
      intro z
      rw [smul_smul]; rw [hgxfy]; rw [smul_smul]; rw [← Nat.cast_smul_eq_nsmul R (2 * 2)]; rw [show 2 * 2 = 4 from rfl]; rw [Nat.cast_ofNat]
    simp only [iterate_succ', comp_apply, ih, two_smul, smul_sub, smul_add, map_add,
      LinearEquiv.trans_apply, reflection_apply_self, map_neg, reflection_apply, neg_sub, map_sub,
      map_nsmul, map_smul, smul_neg, hz, add_smul]
    abel

/--
lemma `infinite_range_reflection_reflection_iterate_iff` / 引理 `infinite_range_reflection_reflection_iterate_iff`

English:
lemma infinite_range_reflection_reflection_iterate_iff
  statement: [IsAddTorsionFree M]
  proof: by
  simp only [reflection_reflection_iterate hfx hgy hgxfy, infinite_range_add_nsmul_iff, sub_ne_zero]

中文:
引理 infinite_range_reflection_reflection_iterate_iff
  结论: [是加法无挠 M]
  证明: by
  simp only [reflection_reflection_iterate hfx hgy hgxfy, infinite_range_add_nsmul_iff, sub_ne_zero]

Depends on / 依赖: infinite_range_add_nsmul_iff, reflection_reflection_iterate, sub_ne_zero
-/
lemma infinite_range_reflection_reflection_iterate_iff [IsAddTorsionFree M]
    (hfx : f x = 2) (hgy : g y = 2) (hgxfy : f y * g x = 4) :
    (range <| fun n => ((reflection hgy).trans (reflection hfx))^[n] y).Infinite ↔
    f y • x != (2 : R) • y := by
  simp only [reflection_reflection_iterate hfx hgy hgxfy, infinite_range_add_nsmul_iff, sub_ne_zero]

/--
lemma `eq_of_mapsTo_reflection_of_mem` / 引理 `eq_of_mapsTo_reflection_of_mem`

English:
lemma eq_of_mapsTo_reflection_of_mem
  statement: [IsAddTorsionFree M] {Φ : Set M} (hΦ : Φ.Finite)
  proof: by
  suffices h : f y • x = (2 : R) • y by
    rw [hfy]; rw [two_smul R x]; rw [two_smul R y]; rw [← two_zsmul]; rw [← two_zsmul] at h
    exact smul_right_injective _ two_ne_zero h
  contrapose! hΦ
  apply ((infinite_range_reflection_reflection_iterate_iff hfx hgy
    (by rw [hfy, hgx]; norm_cast)).mpr hΦ).mono
  rw [range_subset_iff]
  intro n
  rw [← IsFixedPt.image_iterate ((bijOn_reflection_of_mapsTo hfx hxfΦ).comp
    (bijOn_reflection_of_mapsTo hgy hygΦ)).image_eq n]
  exact mem_image_of_mem _ hyΦ

中文:
引理 eq_of_mapsTo_reflection_of_mem
  结论: [是加法无挠 M] {Φ : 集合 M} (hΦ : Φ.有限)
  证明: by
  suffices h : f y • x = (2 : R) • y by
    rw [hfy]; rw [two_smul R x]; rw [two_smul R y]; rw [← two_zsmul]; rw [← two_zsmul] at h
    exact smul_right_injective _ two_ne_zero h
  contrapose! hΦ
  apply ((infinite_range_reflection_reflection_iterate_iff hfx hgy
    (by rw [hfy, hgx]; norm_cast)).mpr hΦ).mono
  rw [range_subset_iff]
  intro n
  rw [← IsFixedPt.image_iterate ((bijOn_reflection_of_mapsTo hfx hxfΦ).comp
    (bijOn_reflection_of_mapsTo hgy hygΦ)).image_eq n]
  exact mem_image_of_mem _ hyΦ

Depends on / 依赖: IsFixedPt, IsFixedPt.image_iterate, bijOn_reflection_of_mapsTo, contrapose, image_eq, image_iterate, infinite_range_reflection_reflection_iterate_iff, mem_image_of_mem, range_subset_iff, smul_right_injective, two_ne_zero, two_smul, two_zsmul
-/
lemma eq_of_mapsTo_reflection_of_mem [IsAddTorsionFree M] {Φ : Set M} (hΦ : Φ.Finite)
    (hfx : f x = 2) (hgy : g y = 2) (hgx : g x = 2) (hfy : f y = 2)
    (hxfΦ : MapsTo (preReflection x f) Φ Φ)
    (hygΦ : MapsTo (preReflection y g) Φ Φ)
    (hyΦ : y in Φ) :
    x = y := by
  suffices h : f y • x = (2 : R) • y by
    rw [hfy]; rw [two_smul R x]; rw [two_smul R y]; rw [← two_zsmul]; rw [← two_zsmul] at h
    exact smul_right_injective _ two_ne_zero h
  contrapose! hΦ
  apply ((infinite_range_reflection_reflection_iterate_iff hfx hgy
    (by rw [hfy, hgx]; norm_cast)).mpr hΦ).mono
  rw [range_subset_iff]
  intro n
  rw [← IsFixedPt.image_iterate ((bijOn_reflection_of_mapsTo hfx hxfΦ).comp
    (bijOn_reflection_of_mapsTo hgy hygΦ)).image_eq n]
  exact mem_image_of_mem _ hyΦ

/--
lemma `injOn_dualMap_subtype_span_range_range` / 引理 `injOn_dualMap_subtype_span_range_range`

English:
lemma injOn_dualMap_subtype_span_range_range
  statement: {ι : Type*} [IsAddTorsionFree M]
  proof: by
  rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩ hij
  congr
  suffices forall k, c i (r k) = c j (r k) by
    rw [← EmbeddingLike.apply_eq_iff_eq r]
    exact eq_of_mapsTo_reflection_of_mem (f := c i) (g := c j) hfin (h_two i) (h_two j)
      (by rw [← this, h_two]) (by rw [this, h_two]) (h_mapsTo i) (h_mapsTo j) (mem_range_self j)
  intro k
  simpa using LinearMap.congr_fun hij ⟨r k, Submodule.subset_span (mem_range_self k)⟩

中文:
引理 injOn_dualMap_subtype_span_range_range
  结论: {ι : 类型} [是加法无挠 M]
  证明: by
  rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩ hij
  congr
  suffices forall k, c i (r k) = c j (r k) by
    rw [← EmbeddingLike.apply_eq_iff_eq r]
    exact eq_of_mapsTo_reflection_of_mem (f := c i) (g := c j) hfin (h_two i) (h_two j)
      (by rw [← this, h_two]) (by rw [this, h_two]) (h_mapsTo i) (h_mapsTo j) (mem_range_self j)
  intro k
  simpa using LinearMap.congr_fun hij ⟨r k, Submodule.subset_span (mem_range_self k)⟩

Depends on / 依赖: EmbeddingLike, EmbeddingLike.apply_eq_iff_eq, LinearMap, LinearMap.congr_fun, Submodule, Submodule.subset_span, apply_eq_iff_eq, congr_fun, eq_of_mapsTo_reflection_of_mem, h_mapsTo, h_two, mem_range_self, subset_span
-/
lemma injOn_dualMap_subtype_span_range_range {ι : Type*} [IsAddTorsionFree M]
    {r : ι ↪ M} {c : ι -> Dual R M} (hfin : (range r).Finite)
    (h_two : forall i, c i (r i) = 2)
    (h_mapsTo : forall i, MapsTo (preReflection (r i) (c i)) (range r) (range r)) :
    InjOn (span R (range r)).subtype.dualMap (range c) := by
  rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩ hij
  congr
  suffices forall k, c i (r k) = c j (r k) by
    rw [← EmbeddingLike.apply_eq_iff_eq r]
    exact eq_of_mapsTo_reflection_of_mem (f := c i) (g := c j) hfin (h_two i) (h_two j)
      (by rw [← this, h_two]) (by rw [this, h_two]) (h_mapsTo i) (h_mapsTo j) (mem_range_self j)
  intro k
  simpa using LinearMap.congr_fun hij ⟨r k, Submodule.subset_span (mem_range_self k)⟩

end Module
