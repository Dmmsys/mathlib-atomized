/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.InnerProductSpace.Convex
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.Additive.AP.Three.Defs
public import Mathlib.Combinatorics.Pigeonhole

/-!
# Behrend's bound on Roth numbers

This file proves Behrend's lower bound on Roth numbers. This says that we can find a subset of
`{1, ..., n}` of size `n / exp (O (sqrt (log n)))` which does not contain arithmetic progressions of
length `3`.

The idea is that the sphere (in the `n`-dimensional Euclidean space) doesn't contain arithmetic
progressions (literally) because the corresponding ball is strictly convex. Thus we can take
integer points on that sphere and map them onto `ℕ` in a way that preserves arithmetic progressions
(`Behrend.map`).

## Main declarations

* `Behrend.sphere`: The intersection of the Euclidean sphere with the positive integer quadrant.
  This is the set that we will map on `ℕ`.
* `Behrend.map`: Given a natural number `d`, `Behrend.map d : ℕⁿ → ℕ` reads off the coordinates as
  digits in base `d`.
* `Behrend.card_sphere_le_rothNumberNat`: Implicit lower bound on Roth numbers in terms of
  `Behrend.sphere`.
* `Behrend.roth_lower_bound`: Behrend's explicit lower bound on Roth numbers.

## References

* [Bryan Gillespie, *Behrend’s Construction*]
  (http://www.epsilonsmall.com/resources/behrends-construction/behrend.pdf)
* Behrend, F. A., "On sets of integers which contain no three terms in arithmetical progression"
* [Wikipedia, *Salem-Spencer set*](https://en.wikipedia.org/wiki/Salem–Spencer_set)

## Tags

3AP-free, Salem-Spencer, Behrend construction, arithmetic progression, sphere, strictly convex
-/

@[expose] public section

assert_not_exists IsConformalMap Conformal

open Nat hiding log
open Finset Metric Real WithLp
open scoped Pointwise

/--
lemma `threeAPFree_frontier` / 引理 `threeAPFree_frontier`

English:
lemma threeAPFree_frontier
  statement: {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  proof: by
  intro a ha b hb c hc habc
  obtain rfl : (1 / 2 : 𝕜) • a + (1 / 2 : 𝕜) • c = b := by
    rwa [← smul_add, one_div, inv_smul_eq_iff₀ (show (2 : 𝕜) != 0 by simp), two_smul]
  have :=
    hs₁.eq (hs₀.frontier_subset ha) (hs₀.frontier_subset hc) one_half_pos one_half_pos
      (add_halves _) hb.2
 

中文:
引理 threeAPFree_frontier
  结论: {𝕜 E : 类型} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  证明: by
  intro a ha b hb c hc habc
  obtain rfl : (1 / 2 : 𝕜) • a + (1 / 2 : 𝕜) • c = b := by
    rwa [← smul_add, one_div, inv_smul_eq_iff₀ (show (2 : 𝕜) != 0 by simp), two_smul]
  have :=
    hs₁.eq (hs₀.frontier_subset ha) (hs₀.frontier_subset hc) one_half_pos one_half_pos
      (add_halves _) hb.2
 

Depends on / 依赖: add_halves, add_smul, frontier_subset, one_div, one_half_pos, ring_nf, smul_add, two_smul
-/
lemma threeAPFree_frontier {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [TopologicalSpace E]
    [AddCommMonoid E] [Module 𝕜 E] {s : Set E} (hs₀ : IsClosed s) (hs₁ : StrictConvex 𝕜 s) :
    ThreeAPFree (frontier s) := by
  intro a ha b hb c hc habc
  obtain rfl : (1 / 2 : 𝕜) • a + (1 / 2 : 𝕜) • c = b := by
    rwa [← smul_add, one_div, inv_smul_eq_iff₀ (show (2 : 𝕜) != 0 by simp), two_smul]
  have :=
    hs₁.eq (hs₀.frontier_subset ha) (hs₀.frontier_subset hc) one_half_pos one_half_pos
      (add_halves _) hb.2
  simp [this, ← add_smul]
  ring_nf
  simp

/--
lemma `threeAPFree_sphere` / 引理 `threeAPFree_sphere`

English:
lemma threeAPFree_sphere
  statement: {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  proof: by
  obtain rfl | hr := eq_or_ne r 0
  · rw [sphere_zero]
    exact threeAPFree_singleton _
  · convert! threeAPFree_frontier isClosed_closedBall (strictConvex_closedBall Real x r)
    exact (frontier_closedBall _ hr).symm

中文:
引理 threeAPFree_sphere
  结论: {E : 类型} [NormedAddCommGroup E] [NormedSpace 实数 E]
  证明: by
  obtain rfl | hr := eq_or_ne r 0
  · rw [sphere_zero]
    exact threeAPFree_singleton _
  · convert! threeAPFree_frontier isClosed_closedBall (strictConvex_closedBall Real x r)
    exact (frontier_closedBall _ hr).symm

Depends on / 依赖: convert, eq_or_ne, frontier_closedBall, isClosed_closedBall, sphere_zero, strictConvex_closedBall, threeAPFree_frontier, threeAPFree_singleton
-/
lemma threeAPFree_sphere {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [StrictConvexSpace Real E] (x : E) (r : Real) : ThreeAPFree (sphere x r) := by
  obtain rfl | hr := eq_or_ne r 0
  · rw [sphere_zero]
    exact threeAPFree_singleton _
  · convert! threeAPFree_frontier isClosed_closedBall (strictConvex_closedBall Real x r)
    exact (frontier_closedBall _ hr).symm

namespace Behrend

variable {n d k N : Nat} {x : Fin n -> Nat}

/-!
### Turning the sphere into 3AP-free set

We define `Behrend.sphere`, the intersection of the $L^2$ sphere with the positive quadrant of
integer points. Because the $L^2$ closed ball is strictly convex, the $L^2$ sphere and
`Behrend.sphere` are 3AP-free (`threeAPFree_sphere`). Then we can turn this set in
`Fin n → ℕ` into a set in `ℕ` using `Behrend.map`, which preserves `ThreeAPFree` because it is
an additive monoid homomorphism.
-/


/--
Definition of `box` / `box` 的定义

English:
definition box
  signature: (n d : Nat)
  body: Fintype.piFinset fun _ => range d

中文:
定义 box
  签名: (n d : 自然数)
  定义体: Fintype.piFinset fun _ => range d

Depends on / 依赖: Fintype, Fintype.piFinset, piFinset
-/
def box (n d : Nat) : Finset (Fin n -> Nat) :=
  Fintype.piFinset fun _ => range d

/--
theorem `mem_box` / 定理 `mem_box`

English:
theorem mem_box
  statement: x in box n d ↔ forall i, x i < d
  proof: by simp only [box, Fintype.mem_piFinset, mem_range]

@[simp]

中文:
定理 mem_box
  结论: x in box n d ↔ 对任意 i, x i < d
  证明: by simp only [box, Fintype.mem_piFinset, mem_range]

@[simp]

Depends on / 依赖: Fintype, Fintype.mem_piFinset, mem_piFinset, mem_range
-/
theorem mem_box : x in box n d ↔ forall i, x i < d := by simp only [box, Fintype.mem_piFinset, mem_range]

@[simp]
/--
theorem `card_box` / 定理 `card_box`

English:
theorem card_box
  statement: #(box n d) = d ^ n
  proof: by simp [box]

@[simp]

中文:
定理 card_box
  结论: #(box n d) = d ^ n
  证明: by simp [box]

@[simp]
-/
theorem card_box : #(box n d) = d ^ n := by simp [box]

@[simp]
/--
theorem `box_zero` / 定理 `box_zero`

English:
theorem box_zero
  statement: box (n + 1) 0 = ∅
  proof: by simp [box]

中文:
定理 box_zero
  结论: box (n + 1) 0 = ∅
  证明: by simp [box]
-/
theorem box_zero : box (n + 1) 0 = ∅ := by simp [box]

/--
Definition of `sphere` / `sphere` 的定义

English:
definition sphere
  signature: (n d k : Nat)
  body: {x in box n d | ∑ i, x i ^ 2 = k}

中文:
定义 sphere
  签名: (n d k : 自然数)
  定义体: {x in box n d | ∑ i, x i ^ 2 = k}
-/
def sphere (n d k : Nat) : Finset (Fin n -> Nat) := {x in box n d | ∑ i, x i ^ 2 = k}

/--
theorem `sphere_zero_subset` / 定理 `sphere_zero_subset`

English:
theorem sphere_zero_subset
  statement: sphere n d 0 subseteq 0
  proof: fun x => by simp [sphere, funext_iff]

@[simp]

中文:
定理 sphere_zero_subset
  结论: sphere n d 0 subseteq 0
  证明: fun x => by simp [sphere, funext_iff]

@[simp]

Depends on / 依赖: funext_iff, sphere
-/
theorem sphere_zero_subset : sphere n d 0 subseteq 0 := fun x => by simp [sphere, funext_iff]

@[simp]
/--
theorem `sphere_zero_right` / 定理 `sphere_zero_right`

English:
theorem sphere_zero_right
  given: (n k : Nat)
  statement: sphere (n + 1) 0 k = ∅
  proof: by simp [sphere]

中文:
定理 sphere_zero_right
  条件: (n k : 自然数)
  结论: sphere (n + 1) 0 k = ∅
  证明: by simp [sphere]

Depends on / 依赖: sphere
-/
theorem sphere_zero_right (n k : Nat) : sphere (n + 1) 0 k = ∅ := by simp [sphere]

/--
theorem `sphere_subset_box` / 定理 `sphere_subset_box`

English:
theorem sphere_subset_box
  statement: sphere n d k subseteq box n d
  proof: filter_subset _ _

中文:
定理 sphere_subset_box
  结论: sphere n d k subseteq box n d
  证明: filter_subset _ _

Depends on / 依赖: filter_subset
-/
theorem sphere_subset_box : sphere n d k subseteq box n d :=
  filter_subset _ _

/--
theorem `norm_of_mem_sphere` / 定理 `norm_of_mem_sphere`

English:
theorem norm_of_mem_sphere
  given: {x : Fin n -> Nat} (hx : x in sphere n d k)
  proof: by
  rw [EuclideanSpace.norm_eq]
  dsimp
  simp_rw [abs_cast, ← cast_pow, ← cast_sum, (mem_filter.1 hx).2]

中文:
定理 norm_of_mem_sphere
  条件: {x : Fin n -> 自然数} (hx : x in sphere n d k)
  证明: by
  rw [EuclideanSpace.norm_eq]
  dsimp
  simp_rw [abs_cast, ← cast_pow, ← cast_sum, (mem_filter.1 hx).2]

Depends on / 依赖: EuclideanSpace, EuclideanSpace.norm_eq, abs_cast, cast_pow, cast_sum, mem_filter, norm_eq, simp_rw
-/
theorem norm_of_mem_sphere {x : Fin n -> Nat} (hx : x in sphere n d k) :
    ‖toLp 2 ((↑) ∘ x : Fin n -> Real)‖ = √↑k := by
  rw [EuclideanSpace.norm_eq]
  dsimp
  simp_rw [abs_cast, ← cast_pow, ← cast_sum, (mem_filter.1 hx).2]

/--
theorem `sphere_subset_preimage_metric_sphere` / 定理 `sphere_subset_preimage_metric_sphere`

English:
theorem sphere_subset_preimage_metric_sphere
  statement: (sphere n d k : Set (Fin n -> Nat)) subseteq
  proof: fun x hx => by rw [Set.mem_preimage, mem_sphere_zero_iff_norm, norm_of_mem_sphere hx]

中文:
定理 sphere_subset_preimage_metric_sphere
  结论: (sphere n d k : Set (Fin n -> 自然数)) subseteq
  证明: fun x hx => by rw [Set.mem_preimage, mem_sphere_zero_iff_norm, norm_of_mem_sphere hx]

Depends on / 依赖: Set.mem_preimage, mem_preimage, mem_sphere_zero_iff_norm, norm_of_mem_sphere
-/
theorem sphere_subset_preimage_metric_sphere : (sphere n d k : Set (Fin n -> Nat)) subseteq
    (fun x : Fin n -> Nat => toLp 2 ((↑) ∘ x : Fin n -> Real)) ⁻¹'
      Metric.sphere (0 : PiLp 2 fun _ : Fin n => Real) (√↑k) :=
  fun x hx => by rw [Set.mem_preimage, mem_sphere_zero_iff_norm, norm_of_mem_sphere hx]

/-- The map that appears in Behrend's bound on Roth numbers. -/
@[simps]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (d : Nat)
  body: ∑ i, a i * d ^ (i : Nat)
  map_zero' := by simp_rw [Pi.zero_apply, zero_mul, sum_const_zero]
  map_add' a b := by simp_rw [Pi.add_apply, add_mul, sum_add_distrib]

中文:
定义 map
  签名: (d : 自然数)
  定义体: ∑ i, a i * d ^ (i : Nat)
  map_zero' := by simp_rw [Pi.zero_apply, zero_mul, sum_const_zero]
  map_add' a b := by simp_rw [Pi.add_apply, add_mul, sum_add_distrib]
-/
def map (d : Nat) : (Fin n -> Nat) ->+ Nat where
  toFun a := ∑ i, a i * d ^ (i : Nat)
  map_zero' := by simp_rw [Pi.zero_apply, zero_mul, sum_const_zero]
  map_add' a b := by simp_rw [Pi.add_apply, add_mul, sum_add_distrib]

/--
theorem `map_zero` / 定理 `map_zero`

English:
theorem map_zero
  given: (d : Nat) (a : Fin 0 -> Nat)
  statement: map d a = 0
  proof: by simp [map]

中文:
定理 map_zero
  条件: (d : 自然数) (a : Fin 0 -> 自然数)
  结论: map d a = 0
  证明: by simp [map]
-/
theorem map_zero (d : Nat) (a : Fin 0 -> Nat) : map d a = 0 := by simp [map]

/--
theorem `map_succ` / 定理 `map_succ`

English:
theorem map_succ
  given: (a : Fin (n + 1) -> Nat)
  proof: by
  simp [map, Fin.sum_univ_succ, _root_.pow_succ, ← mul_assoc, ← sum_mul]

中文:
定理 map_succ
  条件: (a : Fin (n + 1) -> 自然数)
  证明: by
  simp [map, Fin.sum_univ_succ, _root_.pow_succ, ← mul_assoc, ← sum_mul]

Depends on / 依赖: Fin.sum_univ_succ, _root_, _root_.pow_succ, mul_assoc, pow_succ, sum_mul, sum_univ_succ
-/
theorem map_succ (a : Fin (n + 1) -> Nat) :
    map d a = a 0 + (∑ x : Fin n, a x.succ * d ^ (x : Nat)) * d := by
  simp [map, Fin.sum_univ_succ, _root_.pow_succ, ← mul_assoc, ← sum_mul]

/--
theorem `map_succ'` / 定理 `map_succ'`

English:
theorem map_succ'
  given: (a : Fin (n + 1) -> Nat)
  statement: map d a = a 0 + map d (a ∘ Fin.succ) * d
  proof: map_succ _

中文:
定理 map_succ'
  条件: (a : Fin (n + 1) -> 自然数)
  结论: map d a = a 0 + map d (a ∘ Fin.succ) * d
  证明: map_succ _

Depends on / 依赖: map_succ
-/
theorem map_succ' (a : Fin (n + 1) -> Nat) : map d a = a 0 + map d (a ∘ Fin.succ) * d :=
  map_succ _

set_option backward.defeqAttrib.useBackward true in
/--
theorem `map_monotone` / 定理 `map_monotone`

English:
theorem map_monotone
  given: (d : Nat)
  statement: Monotone (map d : (Fin n -> Nat) -> Nat)
  proof: fun x y h => by
dsimp; exact sum_le_sum fun i _ => Nat.mul_le_mul_right _ h i

中文:
定理 map_monotone
  条件: (d : 自然数)
  结论: Monotone (map d : (Fin n -> 自然数) -> 自然数)
  证明: fun x y h => by
dsimp; exact sum_le_sum fun i _ => Nat.mul_le_mul_right _ h i

Depends on / 依赖: Nat.mul_le_mul_right, mul_le_mul_right, sum_le_sum
-/
theorem map_monotone (d : Nat) : Monotone (map d : (Fin n -> Nat) -> Nat) := fun x y h => by
dsimp; exact sum_le_sum fun i _ => Nat.mul_le_mul_right _ h i

/--
theorem `map_mod` / 定理 `map_mod`

English:
theorem map_mod
  given: (a : Fin n.succ -> Nat)
  statement: map d a % d = a 0 % d
  proof: by
  rw [map_succ]; rw [Nat.add_mul_mod_self_right]

中文:
定理 map_mod
  条件: (a : Fin n.succ -> 自然数)
  结论: map d a % d = a 0 % d
  证明: by
  rw [map_succ]; rw [Nat.add_mul_mod_self_right]

Depends on / 依赖: Nat.add_mul_mod_self_right, add_mul_mod_self_right, map_succ
-/
theorem map_mod (a : Fin n.succ -> Nat) : map d a % d = a 0 % d := by
  rw [map_succ]; rw [Nat.add_mul_mod_self_right]

/--
theorem `map_eq_iff` / 定理 `map_eq_iff`

English:
theorem map_eq_iff
  given: {x₁ x₂ : Fin n.succ -> Nat} (hx₁ : forall i, x₁ i < d) (hx₂ : forall i, x₂ i < d)
  proof: by
  refine ⟨fun h => ?_, fun h => by rw [map_succ', map_succ', h.1, h.2]⟩
  have : x₁ 0 = x₂ 0 := by
    rw [← mod_eq_of_lt (hx₁ _)]; rw [← map_mod]; rw [← mod_eq_of_lt (hx₂ _)]; rw [← map_mod]; rw [h]
  rw [map_succ]; rw [map_succ]; rw [this]; rw [add_right_inj]; rw [mul_eq_mul_right_iff] at h
  e

中文:
定理 map_eq_iff
  条件: {x₁ x₂ : Fin n.succ -> 自然数} (hx₁ : 对任意 i, x₁ i < d) (hx₂ : 对任意 i, x₂ i < d)
  证明: by
  refine ⟨fun h => ?_, fun h => by rw [map_succ', map_succ', h.1, h.2]⟩
  have : x₁ 0 = x₂ 0 := by
    rw [← mod_eq_of_lt (hx₁ _)]; rw [← map_mod]; rw [← mod_eq_of_lt (hx₂ _)]; rw [← map_mod]; rw [h]
  rw [map_succ]; rw [map_succ]; rw [this]; rw [add_right_inj]; rw [mul_eq_mul_right_iff] at h
  e

Depends on / 依赖: add_right_inj, h.resolve_right, map_mod, map_succ, mod_eq_of_lt, mul_eq_mul_right_iff, pos_of_gt, resolve_right
-/
theorem map_eq_iff {x₁ x₂ : Fin n.succ -> Nat} (hx₁ : forall i, x₁ i < d) (hx₂ : forall i, x₂ i < d) :
    map d x₁ = map d x₂ ↔ x₁ 0 = x₂ 0 ∧ map d (x₁ ∘ Fin.succ) = map d (x₂ ∘ Fin.succ) := by
  refine ⟨fun h => ?_, fun h => by rw [map_succ', map_succ', h.1, h.2]⟩
  have : x₁ 0 = x₂ 0 := by
    rw [← mod_eq_of_lt (hx₁ _)]; rw [← map_mod]; rw [← mod_eq_of_lt (hx₂ _)]; rw [← map_mod]; rw [h]
  rw [map_succ]; rw [map_succ]; rw [this]; rw [add_right_inj]; rw [mul_eq_mul_right_iff] at h
  exact ⟨this, h.resolve_right (pos_of_gt (hx₁ 0)).ne'⟩

/--
theorem `map_injOn` / 定理 `map_injOn`

English:
theorem map_injOn
  statement: {x : Fin n -> Nat | forall i, x i < d}.InjOn (map d)
  proof: by
  intro x₁ hx₁ x₂ hx₂ h
  induction n with
  | zero => simp [eq_iff_true_of_subsingleton]
  | succ n ih =>
    ext i
    have x := (map_eq_iff hx₁ hx₂).1 h
    exact Fin.cases x.1 (congr_fun <| ih (fun _ => hx₁ _) (fun _ => hx₂ _) x.2) i

中文:
定理 map_injOn
  结论: {x : Fin n -> 自然数 | 对任意 i, x i < d}.InjOn (map d)
  证明: by
  intro x₁ hx₁ x₂ hx₂ h
  induction n with
  | zero => simp [eq_iff_true_of_subsingleton]
  | succ n ih =>
    ext i
    have x := (map_eq_iff hx₁ hx₂).1 h
    exact Fin.cases x.1 (congr_fun <| ih (fun _ => hx₁ _) (fun _ => hx₂ _) x.2) i

Depends on / 依赖: Fin.cases, congr_fun, eq_iff_true_of_subsingleton, map_eq_iff
-/
theorem map_injOn : {x : Fin n -> Nat | forall i, x i < d}.InjOn (map d) := by
  intro x₁ hx₁ x₂ hx₂ h
  induction n with
  | zero => simp [eq_iff_true_of_subsingleton]
  | succ n ih =>
    ext i
    have x := (map_eq_iff hx₁ hx₂).1 h
    exact Fin.cases x.1 (congr_fun <| ih (fun _ => hx₁ _) (fun _ => hx₂ _) x.2) i

/--
theorem `map_le_of_mem_box` / 定理 `map_le_of_mem_box`

English:
theorem map_le_of_mem_box
  given: (hx : x in box n d)
  proof: map_monotone (2 * d - 1) fun _ => Nat.le_sub_one_of_lt mem_box.1 hx _

nonrec theorem threeAPFree_sphere : ThreeAPFree (sphere n d k : Set (Fin n -> Nat)) := by
  set f : (Fin n -> Nat) ->+ EuclideanSpace Real (Fin n) :=
    { toFun := fun f => toLp 2 (((↑) : Nat -> Real) ∘ f)
      map_zero' := PiL

中文:
定理 map_le_of_mem_box
  条件: (hx : x in box n d)
  证明: map_monotone (2 * d - 1) fun _ => Nat.le_sub_one_of_lt mem_box.1 hx _

nonrec theorem threeAPFree_sphere : ThreeAPFree (sphere n d k : Set (Fin n -> Nat)) := by
  set f : (Fin n -> Nat) ->+ EuclideanSpace Real (Fin n) :=
    { toFun := fun f => toLp 2 (((↑) : Nat -> Real) ∘ f)
      map_zero' := PiL

Depends on / 依赖: Nat.le_sub_one_of_lt, le_sub_one_of_lt, map_monotone, mem_box
-/
theorem map_le_of_mem_box (hx : x in box n d) :
    map (2 * d - 1) x <= ∑ i : Fin n, (d - 1) * (2 * d - 1) ^ (i : Nat) :=
map_monotone (2 * d - 1) fun _ => Nat.le_sub_one_of_lt mem_box.1 hx _

nonrec theorem threeAPFree_sphere : ThreeAPFree (sphere n d k : Set (Fin n -> Nat)) := by
  set f : (Fin n -> Nat) ->+ EuclideanSpace Real (Fin n) :=
    { toFun := fun f => toLp 2 (((↑) : Nat -> Real) ∘ f)
      map_zero' := PiLp.ext fun _ => cast_zero
      map_add' := fun _ _ => PiLp.ext fun _ => cast_add _ _ }
  refine ThreeAPFree.of_image (AddHomClass.isAddFreimanHom f (Set.mapsTo_image _ _))
    ((toLp_injective 2).comp_injOn cast_injective.comp_left.injOn) (Set.subset_univ _) ?_
  refine (threeAPFree_sphere 0 (√↑k)).mono (Set.image_subset_iff.2 fun x => ?_)
  rw [Set.mem_preimage]; rw [mem_sphere_zero_iff_norm]
  exact norm_of_mem_sphere

/--
theorem `threeAPFree_image_sphere` / 定理 `threeAPFree_image_sphere`

English:
theorem threeAPFree_image_sphere
  proof: by
  rw [coe_image]
  apply ThreeAPFree.image' (α := Fin n -> Nat) (β := Nat) (s := sphere n d k) (map (2 * d - 1))
    (map_injOn.mono _) threeAPFree_sphere
  rw [Set.add_subset_iff]
  rintro a ha b hb i
  have hai := mem_box.1 (sphere_subset_box ha) i
  have hbi := mem_box.1 (sphere_subset_box hb)

中文:
定理 threeAPFree_image_sphere
  证明: by
  rw [coe_image]
  apply ThreeAPFree.image' (α := Fin n -> Nat) (β := Nat) (s := sphere n d k) (map (2 * d - 1))
    (map_injOn.mono _) threeAPFree_sphere
  rw [Set.add_subset_iff]
  rintro a ha b hb i
  have hai := mem_box.1 (sphere_subset_box ha) i
  have hbi := mem_box.1 (sphere_subset_box hb)

Depends on / 依赖: Set.add_subset_iff, ThreeAPFree, ThreeAPFree.image, _root_, _root_.add_le_add, add_add_add_comm, add_le_add, add_subset_iff, coe_image, lt_tsub_iff_right, map_injOn, map_injOn.mono, mem_box, sphere, sphere_subset_box, succ_le_iff, threeAPFree_sphere, trans_le, two_mul
-/
theorem threeAPFree_image_sphere :
    ThreeAPFree ((sphere n d k).image (map (2 * d - 1)) : Set Nat) := by
  rw [coe_image]
  apply ThreeAPFree.image' (α := Fin n -> Nat) (β := Nat) (s := sphere n d k) (map (2 * d - 1))
    (map_injOn.mono _) threeAPFree_sphere
  rw [Set.add_subset_iff]
  rintro a ha b hb i
  have hai := mem_box.1 (sphere_subset_box ha) i
  have hbi := mem_box.1 (sphere_subset_box hb) i
  rw [lt_tsub_iff_right]; rw [← succ_le_iff]; rw [two_mul]
  exact (add_add_add_comm _ _ 1 1).trans_le (_root_.add_le_add hai hbi)

/--
theorem `sum_sq_le_of_mem_box` / 定理 `sum_sq_le_of_mem_box`

English:
theorem sum_sq_le_of_mem_box
  given: (hx : x in box n d)
  statement: ∑ i : Fin n, x i ^ 2 <= n * (d - 1) ^ 2
  proof: by
  rw [mem_box] at hx
  have : forall i, x i ^ 2 <= (d - 1) ^ 2 := fun i =>
    Nat.pow_le_pow_left (Nat.le_sub_one_of_lt (hx i)) _
  exact (sum_le_card_nsmul univ _ _ fun i _ => this i).trans (by rw [Finset.card_fin, smul_eq_mul])

中文:
定理 sum_sq_le_of_mem_box
  条件: (hx : x in box n d)
  结论: ∑ i : Fin n, x i ^ 2 <= n * (d - 1) ^ 2
  证明: by
  rw [mem_box] at hx
  have : forall i, x i ^ 2 <= (d - 1) ^ 2 := fun i =>
    Nat.pow_le_pow_left (Nat.le_sub_one_of_lt (hx i)) _
  exact (sum_le_card_nsmul univ _ _ fun i _ => this i).trans (by rw [Finset.card_fin, smul_eq_mul])

Depends on / 依赖: Finset, Finset.card_fin, Nat.le_sub_one_of_lt, Nat.pow_le_pow_left, card_fin, le_sub_one_of_lt, mem_box, pow_le_pow_left, smul_eq_mul, sum_le_card_nsmul
-/
theorem sum_sq_le_of_mem_box (hx : x in box n d) : ∑ i : Fin n, x i ^ 2 <= n * (d - 1) ^ 2 := by
  rw [mem_box] at hx
  have : forall i, x i ^ 2 <= (d - 1) ^ 2 := fun i =>
    Nat.pow_le_pow_left (Nat.le_sub_one_of_lt (hx i)) _
  exact (sum_le_card_nsmul univ _ _ fun i _ => this i).trans (by rw [Finset.card_fin, smul_eq_mul])

/--
theorem `sum_eq` / 定理 `sum_eq`

English:
theorem sum_eq
  statement: (∑ i : Fin n, d * (2 * d + 1) ^ (i : Nat)) = ((2 * d + 1) ^ n - 1) / 2
  proof: by
  refine (Nat.div_eq_of_eq_mul_left zero_lt_two ?_).symm
  rw [← sum_range fun i => d * (2 * d + 1) ^ (i : Nat)]; rw [← mul_sum]; rw [mul_right_comm]; rw [mul_comm d]; rw [←
    geom_sum_mul_add]; rw [add_tsub_cancel_right]; rw [mul_comm]

中文:
定理 sum_eq
  结论: (∑ i : Fin n, d * (2 * d + 1) ^ (i : 自然数)) = ((2 * d + 1) ^ n - 1) / 2
  证明: by
  refine (Nat.div_eq_of_eq_mul_left zero_lt_two ?_).symm
  rw [← sum_range fun i => d * (2 * d + 1) ^ (i : Nat)]; rw [← mul_sum]; rw [mul_right_comm]; rw [mul_comm d]; rw [←
    geom_sum_mul_add]; rw [add_tsub_cancel_right]; rw [mul_comm]

Depends on / 依赖: Nat.div_eq_of_eq_mul_left, add_tsub_cancel_right, div_eq_of_eq_mul_left, geom_sum_mul_add, mul_comm, mul_right_comm, mul_sum, sum_range, zero_lt_two
-/
theorem sum_eq : (∑ i : Fin n, d * (2 * d + 1) ^ (i : Nat)) = ((2 * d + 1) ^ n - 1) / 2 := by
  refine (Nat.div_eq_of_eq_mul_left zero_lt_two ?_).symm
  rw [← sum_range fun i => d * (2 * d + 1) ^ (i : Nat)]; rw [← mul_sum]; rw [mul_right_comm]; rw [mul_comm d]; rw [←
    geom_sum_mul_add]; rw [add_tsub_cancel_right]; rw [mul_comm]

/--
theorem `sum_lt` / 定理 `sum_lt`

English:
theorem sum_lt
  statement: (∑ i : Fin n, d * (2 * d + 1) ^ (i : Nat)) < (2 * d + 1) ^ n
  proof: sum_eq.trans_lt (Nat.div_le_self _ 2).trans_lt pred_lt (pow_pos (succ_pos _) _).ne'

中文:
定理 sum_lt
  结论: (∑ i : Fin n, d * (2 * d + 1) ^ (i : 自然数)) < (2 * d + 1) ^ n
  证明: sum_eq.trans_lt (Nat.div_le_self _ 2).trans_lt pred_lt (pow_pos (succ_pos _) _).ne'

Depends on / 依赖: Nat.div_le_self, div_le_self, pow_pos, pred_lt, succ_pos, sum_eq, sum_eq.trans_lt, trans_lt
-/
theorem sum_lt : (∑ i : Fin n, d * (2 * d + 1) ^ (i : Nat)) < (2 * d + 1) ^ n :=
sum_eq.trans_lt (Nat.div_le_self _ 2).trans_lt pred_lt (pow_pos (succ_pos _) _).ne'

/--
theorem `card_sphere_le_rothNumberNat` / 定理 `card_sphere_le_rothNumberNat`

English:
theorem card_sphere_le_rothNumberNat
  given: (n d k : Nat)
  proof: by
  cases n
  · dsimp; refine (card_le_univ _).trans_eq ?_; rfl
  cases d
  · simp
  apply threeAPFree_image_sphere.le_rothNumberNat _ _ (card_image_of_injOn _)
  · simp only [mem_image, and_imp, forall_exists_index,
      sphere, mem_filter]
    rintro _ x hx _ rfl
    exact (map_le_of_mem_box hx)

中文:
定理 card_sphere_le_rothNumberNat
  条件: (n d k : 自然数)
  证明: by
  cases n
  · dsimp; refine (card_le_univ _).trans_eq ?_; rfl
  cases d
  · simp
  apply threeAPFree_image_sphere.le_rothNumberNat _ _ (card_image_of_injOn _)
  · simp only [mem_image, and_imp, forall_exists_index,
      sphere, mem_filter]
    rintro _ x hx _ rfl
    exact (map_le_of_mem_box hx)

Depends on / 依赖: and_imp, card_image_of_injOn, card_le_univ, forall_exists_index, le_rothNumberNat, le_self_add, map_injOn, map_injOn.mono, map_le_of_mem_box, mem_box, mem_coe, mem_filter, mem_image, sphere, sum_lt, threeAPFree_image_sphere, threeAPFree_image_sphere.le_rothNumberNat, trans_eq, trans_le, trans_lt
-/
theorem card_sphere_le_rothNumberNat (n d k : Nat) :
    #(sphere n d k) <= rothNumberNat ((2 * d - 1) ^ n) := by
  cases n
  · dsimp; refine (card_le_univ _).trans_eq ?_; rfl
  cases d
  · simp
  apply threeAPFree_image_sphere.le_rothNumberNat _ _ (card_image_of_injOn _)
  · simp only [mem_image, and_imp, forall_exists_index,
      sphere, mem_filter]
    rintro _ x hx _ rfl
    exact (map_le_of_mem_box hx).trans_lt sum_lt
  apply map_injOn.mono fun x => ?_
  simp only [mem_coe, sphere, mem_filter, mem_box, and_imp, two_mul]
  exact fun h _ i => (h i).trans_le le_self_add



/--
theorem `exists_large_sphere_aux` / 定理 `exists_large_sphere_aux`

English:
theorem exists_large_sphere_aux
  given: (n d : Nat)
  statement: exists k in range (n * (d - 1) ^ 2 + 1),
  proof: by
  refine exists_le_card_fiber_of_nsmul_le_card_of_maps_to (fun x hx => ?_) nonempty_range_add_one ?_
  · rw [mem_range, Nat.lt_succ_iff]
    exact sum_sq_le_of_mem_box hx
  · rw [card_range, nsmul_eq_mul, mul_div_assoc', cast_add_one, mul_div_cancel_left₀, card_box]
    exact (cast_add_one_pos _)

中文:
定理 exists_large_sphere_aux
  条件: (n d : 自然数)
  结论: 存在 k in range (n * (d - 1) ^ 2 + 1),
  证明: by
  refine exists_le_card_fiber_of_nsmul_le_card_of_maps_to (fun x hx => ?_) nonempty_range_add_one ?_
  · rw [mem_range, Nat.lt_succ_iff]
    exact sum_sq_le_of_mem_box hx
  · rw [card_range, nsmul_eq_mul, mul_div_assoc', cast_add_one, mul_div_cancel_left₀, card_box]
    exact (cast_add_one_pos _)

Depends on / 依赖: Nat.lt_succ_iff, card_box, card_range, cast_add_one, cast_add_one_pos, exists_le_card_fiber_of_nsmul_le_card_of_maps_to, lt_succ_iff, mem_range, mul_div_assoc, nonempty_range_add_one, nsmul_eq_mul, sum_sq_le_of_mem_box
-/
theorem exists_large_sphere_aux (n d : Nat) : exists k in range (n * (d - 1) ^ 2 + 1),
    (↑(d ^ n) / ((n * (d - 1) ^ 2 :) + 1) : Real) <= #(sphere n d k) := by
  refine exists_le_card_fiber_of_nsmul_le_card_of_maps_to (fun x hx => ?_) nonempty_range_add_one ?_
  · rw [mem_range, Nat.lt_succ_iff]
    exact sum_sq_le_of_mem_box hx
  · rw [card_range, nsmul_eq_mul, mul_div_assoc', cast_add_one, mul_div_cancel_left₀, card_box]
    exact (cast_add_one_pos _).ne'

/--
theorem `exists_large_sphere` / 定理 `exists_large_sphere`

English:
theorem exists_large_sphere
  given: (n d : Nat)
  proof: by
  obtain ⟨k, -, hk⟩ := exists_large_sphere_aux n d
  refine ⟨k, ?_⟩
  obtain rfl | hn := n.eq_zero_or_pos
  · simp
  obtain rfl | hd := d.eq_zero_or_pos
  · simp
  refine (div_le_div_of_nonneg_left (by positivity) (by positivity) ?_).trans hk
  simp only [← le_sub_iff_add_le', cast_mul, ← mul_sub

中文:
定理 exists_large_sphere
  条件: (n d : 自然数)
  证明: by
  obtain ⟨k, -, hk⟩ := exists_large_sphere_aux n d
  refine ⟨k, ?_⟩
  obtain rfl | hn := n.eq_zero_or_pos
  · simp
  obtain rfl | hd := d.eq_zero_or_pos
  · simp
  refine (div_le_div_of_nonneg_left (by positivity) (by positivity) ?_).trans hk
  simp only [← le_sub_iff_add_le', cast_mul, ← mul_sub

Depends on / 依赖: _root_, _root_.le_sub_iff_add_le, cast_mul, cast_one, cast_pow, cast_sub, d.eq_zero_or_pos, div_le_div_of_nonneg_left, eq_zero_or_pos, exists_large_sphere_aux, le_sub_iff_add_le, mul_one, mul_sub, n.eq_zero_or_pos, one_le_cast, one_le_mul_of_one_le_of_one_le, one_pow, sub_add, sub_sq, sub_sub_self
-/
theorem exists_large_sphere (n d : Nat) :
    exists k, ((d ^ n :) / (n * d ^ 2 :) : Real) <= #(sphere n d k) := by
  obtain ⟨k, -, hk⟩ := exists_large_sphere_aux n d
  refine ⟨k, ?_⟩
  obtain rfl | hn := n.eq_zero_or_pos
  · simp
  obtain rfl | hd := d.eq_zero_or_pos
  · simp
  refine (div_le_div_of_nonneg_left (by positivity) (by positivity) ?_).trans hk
  simp only [← le_sub_iff_add_le', cast_mul, ← mul_sub, cast_pow, cast_sub hd, sub_sq, one_pow,
    cast_one, mul_one, sub_add, sub_sub_self]
  apply one_le_mul_of_one_le_of_one_le
  · rwa [one_le_cast]
  rw [_root_.le_sub_iff_add_le]
  norm_num
  exact one_le_cast.2 hd

/--
theorem `bound_aux'` / 定理 `bound_aux'`

English:
theorem bound_aux'
  given: (n d : Nat)
  statement: ((d ^ n :) / (n * d ^ 2 :) : Real) <= rothNumberNat ((2 * d - 1) ^ n)
  proof: let ⟨_, h⟩ := exists_large_sphere n d
h.trans cast_le.2 card_sphere_le_rothNumberNat _ _ _

中文:
定理 bound_aux'
  条件: (n d : 自然数)
  结论: ((d ^ n :) / (n * d ^ 2 :) : 实数) <= rothNumber自然数 ((2 * d - 1) ^ n)
  证明: let ⟨_, h⟩ := exists_large_sphere n d
h.trans cast_le.2 card_sphere_le_rothNumberNat _ _ _

Depends on / 依赖: card_sphere_le_rothNumberNat, cast_le, exists_large_sphere, h.trans
-/
theorem bound_aux' (n d : Nat) : ((d ^ n :) / (n * d ^ 2 :) : Real) <= rothNumberNat ((2 * d - 1) ^ n) :=
  let ⟨_, h⟩ := exists_large_sphere n d
h.trans cast_le.2 card_sphere_le_rothNumberNat _ _ _

/--
theorem `bound_aux` / 定理 `bound_aux`

English:
theorem bound_aux
  given: (hd : d != 0) (hn : 2 <= n)
  proof: by
  convert! bound_aux' n d using 1
  rw [cast_mul]; rw [cast_pow]; rw [mul_comm]; rw [← div_div]; rw [pow_sub₀ _ _ hn]; rw [← div_eq_mul_inv]; rw [cast_pow]
  rwa [cast_ne_zero]

中文:
定理 bound_aux
  条件: (hd : d != 0) (hn : 2 <= n)
  证明: by
  convert! bound_aux' n d using 1
  rw [cast_mul]; rw [cast_pow]; rw [mul_comm]; rw [← div_div]; rw [pow_sub₀ _ _ hn]; rw [← div_eq_mul_inv]; rw [cast_pow]
  rwa [cast_ne_zero]

Depends on / 依赖: bound_aux, cast_mul, cast_ne_zero, cast_pow, convert, div_div, div_eq_mul_inv, mul_comm
-/
theorem bound_aux (hd : d != 0) (hn : 2 <= n) :
    (d ^ (n - 2 :) / n : Real) <= rothNumberNat ((2 * d - 1) ^ n) := by
  convert! bound_aux' n d using 1
  rw [cast_mul]; rw [cast_pow]; rw [mul_comm]; rw [← div_div]; rw [pow_sub₀ _ _ hn]; rw [← div_eq_mul_inv]; rw [cast_pow]
  rwa [cast_ne_zero]

open scoped Filter Topology

open Real

section NumericalBounds

/--
theorem `log_two_mul_two_le_sqrt_log_eight` / 定理 `log_two_mul_two_le_sqrt_log_eight`

English:
theorem log_two_mul_two_le_sqrt_log_eight
  statement: log 2 * 2 <= √(log 8)
  proof: by
  rw [show (8 : Real) = 2 ^ 3 by norm_num1]; rw [Real.log_pow]; rw [Nat.cast_ofNat]
  apply le_sqrt_of_sq_le
  rw [mul_pow]; rw [sq (log 2)]; rw [mul_assoc]; rw [mul_comm]
  gcongr
  linarith only [log_two_lt_d9.le]

中文:
定理 log_two_mul_two_le_sqrt_log_eight
  结论: log 2 * 2 <= √(log 8)
  证明: by
  rw [show (8 : Real) = 2 ^ 3 by norm_num1]; rw [Real.log_pow]; rw [Nat.cast_ofNat]
  apply le_sqrt_of_sq_le
  rw [mul_pow]; rw [sq (log 2)]; rw [mul_assoc]; rw [mul_comm]
  gcongr
  linarith only [log_two_lt_d9.le]

Depends on / 依赖: Nat.cast_ofNat, Real.log_pow, cast_ofNat, le_sqrt_of_sq_le, log_pow, log_two_lt_d9, log_two_lt_d9.le, mul_assoc, mul_comm, mul_pow, norm_num1
-/
theorem log_two_mul_two_le_sqrt_log_eight : log 2 * 2 <= √(log 8) := by
  rw [show (8 : Real) = 2 ^ 3 by norm_num1]; rw [Real.log_pow]; rw [Nat.cast_ofNat]
  apply le_sqrt_of_sq_le
  rw [mul_pow]; rw [sq (log 2)]; rw [mul_assoc]; rw [mul_comm]
  gcongr
  linarith only [log_two_lt_d9.le]

/--
theorem `two_div_one_sub_two_div_e_le_eight` / 定理 `two_div_one_sub_two_div_e_le_eight`

English:
theorem two_div_one_sub_two_div_e_le_eight
  statement: 2 / (1 - 2 / exp 1) <= 8
  proof: by
  rw [div_le_iff₀]; rw [mul_sub]; rw [mul_one]; rw [mul_div_assoc']; rw [le_sub_comm]; rw [div_le_iff₀ (exp_pos _)]
  · linarith [exp_one_gt_d9]
  rw [sub_pos]; rw [div_lt_one] <;> exact exp_one_gt_d9.trans' (by norm_num)

中文:
定理 two_div_one_sub_two_div_e_le_eight
  结论: 2 / (1 - 2 / exp 1) <= 8
  证明: by
  rw [div_le_iff₀]; rw [mul_sub]; rw [mul_one]; rw [mul_div_assoc']; rw [le_sub_comm]; rw [div_le_iff₀ (exp_pos _)]
  · linarith [exp_one_gt_d9]
  rw [sub_pos]; rw [div_lt_one] <;> exact exp_one_gt_d9.trans' (by norm_num)

Depends on / 依赖: div_lt_one, exp_one_gt_d9, exp_one_gt_d9.trans, exp_pos, le_sub_comm, mul_div_assoc, mul_one, mul_sub, sub_pos
-/
theorem two_div_one_sub_two_div_e_le_eight : 2 / (1 - 2 / exp 1) <= 8 := by
  rw [div_le_iff₀]; rw [mul_sub]; rw [mul_one]; rw [mul_div_assoc']; rw [le_sub_comm]; rw [div_le_iff₀ (exp_pos _)]
  · linarith [exp_one_gt_d9]
  rw [sub_pos]; rw [div_lt_one] <;> exact exp_one_gt_d9.trans' (by norm_num)

/--
theorem `le_sqrt_log` / 定理 `le_sqrt_log`

English:
theorem le_sqrt_log
  given: (hN : 4096 <= N)
  statement: log (2 / (1 - 2 / exp 1)) * (69 / 50) <= √(log ↑N)
  proof: by
  calc
    _ <= log (2 ^ 3) * (69 / 50) := by
      gcongr
      · field_simp
        simp (disch := positivity) [exp_one_gt_two]
      · norm_num1
        exact two_div_one_sub_two_div_e_le_eight
    _ <= √(log (2 ^ 12)) := by
      simp only [Real.log_pow, Nat.cast_ofNat]
      apply le_sqrt_of

中文:
定理 le_sqrt_log
  条件: (hN : 4096 <= N)
  结论: log (2 / (1 - 2 / exp 1)) * (69 / 50) <= √(log ↑N)
  证明: by
  calc
    _ <= log (2 ^ 3) * (69 / 50) := by
      gcongr
      · field_simp
        simp (disch := positivity) [exp_one_gt_two]
      · norm_num1
        exact two_div_one_sub_two_div_e_le_eight
    _ <= √(log (2 ^ 12)) := by
      simp only [Real.log_pow, Nat.cast_ofNat]
      apply le_sqrt_of

Depends on / 依赖: Nat.cast_ofNat, Real.log_pow, cast_ofNat, exp_one_gt_two, le_sqrt_of_sq_le, log_pow, log_two_gt_d9, log_two_lt_d9, mod_cast, norm_num1, two_div_one_sub_two_div_e_le_eight
-/
theorem le_sqrt_log (hN : 4096 <= N) : log (2 / (1 - 2 / exp 1)) * (69 / 50) <= √(log ↑N) := by
  calc
    _ <= log (2 ^ 3) * (69 / 50) := by
      gcongr
      · field_simp
        simp (disch := positivity) [exp_one_gt_two]
      · norm_num1
        exact two_div_one_sub_two_div_e_le_eight
    _ <= √(log (2 ^ 12)) := by
      simp only [Real.log_pow, Nat.cast_ofNat]
      apply le_sqrt_of_sq_le
      nlinarith [log_two_lt_d9, log_two_gt_d9]
    _ <= √(log ↑N) := by
      gcongr
      exact mod_cast hN

/--
theorem `exp_neg_two_mul_le` / 定理 `exp_neg_two_mul_le`

English:
theorem exp_neg_two_mul_le
  given: {x : Real} (hx : 0 < x)
  statement: exp (-2 * x) < exp (2 - ⌈x⌉₊) / ⌈x⌉₊
  proof: by
  have h₁ := ceil_lt_add_one hx.le
  have h₂ : 1 - x <= 2 - ⌈x⌉₊ := by linarith
  calc
    _ <= exp (1 - x) / (x + 1) := ?_
    _ <= exp (2 - ⌈x⌉₊) / (x + 1) := by gcongr
    _ < _ := by gcongr
  rw [le_div_iff₀ (add_pos hx zero_lt_one)]; rw [← le_div_iff₀' (exp_pos _)]; rw [← exp_sub]; rw [neg_m

中文:
定理 exp_neg_two_mul_le
  条件: {x : 实数} (hx : 0 < x)
  结论: exp (-2 * x) < exp (2 - ⌈x⌉₊) / ⌈x⌉₊
  证明: by
  have h₁ := ceil_lt_add_one hx.le
  have h₂ : 1 - x <= 2 - ⌈x⌉₊ := by linarith
  calc
    _ <= exp (1 - x) / (x + 1) := ?_
    _ <= exp (2 - ⌈x⌉₊) / (x + 1) := by gcongr
    _ < _ := by gcongr
  rw [le_div_iff₀ (add_pos hx zero_lt_one)]; rw [← le_div_iff₀' (exp_pos _)]; rw [← exp_sub]; rw [neg_m

Depends on / 依赖: add_comm, add_one_le_exp, add_pos, ceil_lt_add_one, exp_pos, exp_sub, hx.le, le_add_of_nonneg_right, le_trans, neg_mul, sub_add_add_cancel, sub_neg_eq_add, two_mul, zero_le_one, zero_lt_one
-/
theorem exp_neg_two_mul_le {x : Real} (hx : 0 < x) : exp (-2 * x) < exp (2 - ⌈x⌉₊) / ⌈x⌉₊ := by
  have h₁ := ceil_lt_add_one hx.le
  have h₂ : 1 - x <= 2 - ⌈x⌉₊ := by linarith
  calc
    _ <= exp (1 - x) / (x + 1) := ?_
    _ <= exp (2 - ⌈x⌉₊) / (x + 1) := by gcongr
    _ < _ := by gcongr
  rw [le_div_iff₀ (add_pos hx zero_lt_one)]; rw [← le_div_iff₀' (exp_pos _)]; rw [← exp_sub]; rw [neg_mul]; rw [sub_neg_eq_add]; rw [two_mul]; rw [sub_add_add_cancel]; rw [add_comm _ x]
  exact le_trans (le_add_of_nonneg_right zero_le_one) (add_one_le_exp _)

/--
theorem `div_lt_floor` / 定理 `div_lt_floor`

English:
theorem div_lt_floor
  given: {x : Real} (hx : 2 / (1 - 2 / exp 1) <= x)
  statement: x / exp 1 < (⌊x / 2⌋₊ : Real)
  proof: by
  apply lt_of_le_of_lt _ (sub_one_lt_floor _)
  have : 0 < 1 - 2 / exp 1 := by
    rw [sub_pos]; rw [div_lt_one (exp_pos _)]
    exact exp_one_gt_two
  rwa [le_sub_comm, div_eq_mul_one_div x, div_eq_mul_one_div x, ← mul_sub, div_sub', ←
    div_eq_mul_one_div, mul_div_assoc', one_le_div, ← div_le

中文:
定理 div_lt_floor
  条件: {x : 实数} (hx : 2 / (1 - 2 / exp 1) <= x)
  结论: x / exp 1 < (⌊x / 2⌋₊ : 实数)
  证明: by
  apply lt_of_le_of_lt _ (sub_one_lt_floor _)
  have : 0 < 1 - 2 / exp 1 := by
    rw [sub_pos]; rw [div_lt_one (exp_pos _)]
    exact exp_one_gt_two
  rwa [le_sub_comm, div_eq_mul_one_div x, div_eq_mul_one_div x, ← mul_sub, div_sub', ←
    div_eq_mul_one_div, mul_div_assoc', one_le_div, ← div_le

Depends on / 依赖: div_eq_mul_one_div, div_lt_one, div_sub, exp_one_gt_two, exp_pos, le_sub_comm, lt_of_le_of_lt, mul_div_assoc, mul_sub, one_le_div, sub_one_lt_floor, sub_pos, two_ne_zero, zero_lt_two
-/
theorem div_lt_floor {x : Real} (hx : 2 / (1 - 2 / exp 1) <= x) : x / exp 1 < (⌊x / 2⌋₊ : Real) := by
  apply lt_of_le_of_lt _ (sub_one_lt_floor _)
  have : 0 < 1 - 2 / exp 1 := by
    rw [sub_pos]; rw [div_lt_one (exp_pos _)]
    exact exp_one_gt_two
  rwa [le_sub_comm, div_eq_mul_one_div x, div_eq_mul_one_div x, ← mul_sub, div_sub', ←
    div_eq_mul_one_div, mul_div_assoc', one_le_div, ← div_le_iff₀ this]
  · exact zero_lt_two
  · exact two_ne_zero

/--
theorem `ceil_lt_mul` / 定理 `ceil_lt_mul`

English:
theorem ceil_lt_mul
  given: {x : Real} (hx : 50 / 19 <= x)
  statement: (⌈x⌉₊ : Real) < 1.38 * x
  proof: by
  refine (ceil_lt_add_one <| hx.trans' <| by norm_num).trans_le ?_
  rw [← le_sub_iff_add_le']; rw [← sub_one_mul]
  have : (1.38 : Real) = 69 / 50 := by norm_num
  rwa [this, show (69 / 50 - 1 : Real) = (50 / 19)⁻¹ by norm_num1, ←
    div_eq_inv_mul, one_le_div]
  norm_num1

中文:
定理 ceil_lt_mul
  条件: {x : 实数} (hx : 50 / 19 <= x)
  结论: (⌈x⌉₊ : 实数) < 1.38 * x
  证明: by
  refine (ceil_lt_add_one <| hx.trans' <| by norm_num).trans_le ?_
  rw [← le_sub_iff_add_le']; rw [← sub_one_mul]
  have : (1.38 : Real) = 69 / 50 := by norm_num
  rwa [this, show (69 / 50 - 1 : Real) = (50 / 19)⁻¹ by norm_num1, ←
    div_eq_inv_mul, one_le_div]
  norm_num1

Depends on / 依赖: ceil_lt_add_one, div_eq_inv_mul, hx.trans, le_sub_iff_add_le, norm_num1, one_le_div, sub_one_mul, trans_le
-/
theorem ceil_lt_mul {x : Real} (hx : 50 / 19 <= x) : (⌈x⌉₊ : Real) < 1.38 * x := by
  refine (ceil_lt_add_one <| hx.trans' <| by norm_num).trans_le ?_
  rw [← le_sub_iff_add_le']; rw [← sub_one_mul]
  have : (1.38 : Real) = 69 / 50 := by norm_num
  rwa [this, show (69 / 50 - 1 : Real) = (50 / 19)⁻¹ by norm_num1, ←
    div_eq_inv_mul, one_le_div]
  norm_num1

end NumericalBounds

/--
Definition of `nValue` / `nValue` 的定义

English:
definition nValue
  signature: (N : Nat)
  body: ⌈√(log N)⌉₊

中文:
定义 nValue
  签名: (N : 自然数)
  定义体: ⌈√(log N)⌉₊
-/
noncomputable def nValue (N : Nat) : Nat :=
  ⌈√(log N)⌉₊

/--
Definition of `dValue` / `dValue` 的定义

English:
definition dValue
  signature: (N : Nat)
  body: ⌊(N : Real) ^ (nValue N : Real)⁻¹ / 2⌋₊

中文:
定义 dValue
  签名: (N : 自然数)
  定义体: ⌊(N : Real) ^ (nValue N : Real)⁻¹ / 2⌋₊

Depends on / 依赖: nValue
-/
noncomputable def dValue (N : Nat) : Nat := ⌊(N : Real) ^ (nValue N : Real)⁻¹ / 2⌋₊

/--
theorem `nValue_pos` / 定理 `nValue_pos`

English:
theorem nValue_pos
  given: (hN : 2 <= N)
  statement: 0 < nValue N
  proof: ceil_pos.2 Real.sqrt_pos.2 log_pos one_lt_cast.2 hN

中文:
定理 nValue_pos
  条件: (hN : 2 <= N)
  结论: 0 < nValue N
  证明: ceil_pos.2 Real.sqrt_pos.2 log_pos one_lt_cast.2 hN

Depends on / 依赖: Real.sqrt_pos, ceil_pos, log_pos, one_lt_cast, sqrt_pos
-/
theorem nValue_pos (hN : 2 <= N) : 0 < nValue N :=
ceil_pos.2 Real.sqrt_pos.2 log_pos one_lt_cast.2 hN

/--
theorem `three_le_nValue` / 定理 `three_le_nValue`

English:
theorem three_le_nValue
  given: (hN : 64 <= N)
  statement: 3 <= nValue N
  proof: by
  rw [nValue]; rw [← lt_iff_add_one_le]; rw [lt_ceil]; rw [cast_two]
  apply lt_sqrt_of_sq_lt
  have : (2 : Real) ^ ((6 : Nat) : Real) <= N := by
    rw [rpow_natCast]
    exact (cast_le.2 hN).trans' (by norm_num1)
  apply lt_of_lt_of_le _ (log_le_log (rpow_pos_of_pos zero_lt_two _) this)
  rw [l

中文:
定理 three_le_nValue
  条件: (hN : 64 <= N)
  结论: 3 <= nValue N
  证明: by
  rw [nValue]; rw [← lt_iff_add_one_le]; rw [lt_ceil]; rw [cast_two]
  apply lt_sqrt_of_sq_lt
  have : (2 : Real) ^ ((6 : Nat) : Real) <= N := by
    rw [rpow_natCast]
    exact (cast_le.2 hN).trans' (by norm_num1)
  apply lt_of_lt_of_le _ (log_le_log (rpow_pos_of_pos zero_lt_two _) this)
  rw [l

Depends on / 依赖: cast_le, cast_two, log_le_log, log_rpow, log_two_gt_d9, log_two_gt_d9.trans_le, lt_ceil, lt_iff_add_one_le, lt_of_lt_of_le, lt_sqrt_of_sq_lt, nValue, norm_num1, rpow_natCast, rpow_pos_of_pos, trans_le, zero_lt_two
-/
theorem three_le_nValue (hN : 64 <= N) : 3 <= nValue N := by
  rw [nValue]; rw [← lt_iff_add_one_le]; rw [lt_ceil]; rw [cast_two]
  apply lt_sqrt_of_sq_lt
  have : (2 : Real) ^ ((6 : Nat) : Real) <= N := by
    rw [rpow_natCast]
    exact (cast_le.2 hN).trans' (by norm_num1)
  apply lt_of_lt_of_le _ (log_le_log (rpow_pos_of_pos zero_lt_two _) this)
  rw [log_rpow zero_lt_two]; rw [← div_lt_iff₀']
  · exact log_two_gt_d9.trans_le' (by norm_num1)
  · norm_num1

/--
theorem `dValue_pos` / 定理 `dValue_pos`

English:
theorem dValue_pos
  given: (hN₃ : 8 <= N)
  statement: 0 < dValue N
  proof: by
  have hN₀ : 0 < (N : Real) := cast_pos.2 (succ_pos'.trans_le hN₃)
  rw [dValue]; rw [floor_pos]; rw [← log_le_log_iff zero_lt_one]; rw [log_one]; rw [log_div _ two_ne_zero]; rw [log_rpow hN₀]; rw [inv_mul_eq_div]; rw [sub_nonneg]; rw [le_div_iff₀]
  · have : (nValue N : Real) <= 2 * √(log N) := 

中文:
定理 dValue_pos
  条件: (hN₃ : 8 <= N)
  结论: 0 < dValue N
  证明: by
  have hN₀ : 0 < (N : Real) := cast_pos.2 (succ_pos'.trans_le hN₃)
  rw [dValue]; rw [floor_pos]; rw [← log_le_log_iff zero_lt_one]; rw [log_one]; rw [log_div _ two_ne_zero]; rw [log_rpow hN₀]; rw [inv_mul_eq_div]; rw [sub_nonneg]; rw [le_div_iff₀]
  · have : (nValue N : Real) <= 2 * √(log N) := 

Depends on / 依赖: add_le_add_iff_left, cast_pos, ceil_lt_add_one, dValue, exp_one_lt_d9, exp_one_lt_d9.le.trans, floor_pos, inv_mul_eq_div, le.trans, le_log_iff_exp_le, le_sqrt_of_sq_le, log_div, log_le_log_iff, log_one, log_rpow, nValue, one_pow, sqrt_nonneg, sub_nonneg, succ_pos
-/
theorem dValue_pos (hN₃ : 8 <= N) : 0 < dValue N := by
  have hN₀ : 0 < (N : Real) := cast_pos.2 (succ_pos'.trans_le hN₃)
  rw [dValue]; rw [floor_pos]; rw [← log_le_log_iff zero_lt_one]; rw [log_one]; rw [log_div _ two_ne_zero]; rw [log_rpow hN₀]; rw [inv_mul_eq_div]; rw [sub_nonneg]; rw [le_div_iff₀]
  · have : (nValue N : Real) <= 2 * √(log N) := by
      apply (ceil_lt_add_one <| sqrt_nonneg _).le.trans
      rw [two_mul]; rw [add_le_add_iff_left]
      apply le_sqrt_of_sq_le
      rw [one_pow]; rw [le_log_iff_exp_le hN₀]
      exact (exp_one_lt_d9.le.trans <| by norm_num).trans (cast_le.2 hN₃)
    apply (mul_le_mul_of_nonneg_left this <| log_nonneg one_le_two).trans _
    rw [← mul_assoc]; rw [← le_div_iff₀ (Real.sqrt_pos.2 <| log_pos <| one_lt_cast.2 _)]; rw [div_sqrt]
    · apply log_two_mul_two_le_sqrt_log_eight.trans
      apply Real.sqrt_le_sqrt
      exact log_le_log (by simp) (mod_cast hN₃)
    exact hN₃.trans_lt' (by simp)
  · exact cast_pos.2 (nValue_pos <| hN₃.trans' <| by simp)
  · exact (rpow_pos_of_pos hN₀ _).ne'
  · exact div_pos (rpow_pos_of_pos hN₀ _) zero_lt_two

/--
theorem `le_N` / 定理 `le_N`

English:
theorem le_N
  given: (hN : 2 <= N)
  statement: (2 * dValue N - 1) ^ nValue N <= N
  proof: by
  have : (2 * dValue N - 1) ^ nValue N <= (2 * dValue N) ^ nValue N :=
    Nat.pow_le_pow_left (Nat.sub_le _ _) _
  apply this.trans
  suffices ((2 * dValue N) ^ nValue N : Real) <= N from mod_cast this
  suffices i : (2 * dValue N : Real) <= (N : Real) ^ (nValue N : Real)⁻¹ by
    rw [← rpow_nat

中文:
定理 le_N
  条件: (hN : 2 <= N)
  结论: (2 * dValue N - 1) ^ nValue N <= N
  证明: by
  have : (2 * dValue N - 1) ^ nValue N <= (2 * dValue N) ^ nValue N :=
    Nat.pow_le_pow_left (Nat.sub_le _ _) _
  apply this.trans
  suffices ((2 * dValue N) ^ nValue N : Real) <= N from mod_cast this
  suffices i : (2 * dValue N : Real) <= (N : Real) ^ (nValue N : Real)⁻¹ by
    rw [← rpow_nat

Depends on / 依赖: Nat.pow_le_pow_left, Nat.sub_le, cast_ne_zero, cast_nonneg, dValue, le_di, mod_cast, mul_nonneg, nValue, nValue_pos, pow_le_pow_left, rpow_le_rpow, rpow_mul, rpow_natCast, rpow_one, sub_le, this.trans, zero_le_two
-/
theorem le_N (hN : 2 <= N) : (2 * dValue N - 1) ^ nValue N <= N := by
  have : (2 * dValue N - 1) ^ nValue N <= (2 * dValue N) ^ nValue N :=
    Nat.pow_le_pow_left (Nat.sub_le _ _) _
  apply this.trans
  suffices ((2 * dValue N) ^ nValue N : Real) <= N from mod_cast this
  suffices i : (2 * dValue N : Real) <= (N : Real) ^ (nValue N : Real)⁻¹ by
    rw [← rpow_natCast]
    apply (rpow_le_rpow (mul_nonneg zero_le_two (cast_nonneg _)) i (cast_nonneg _)).trans
    rw [← rpow_mul (cast_nonneg _)]; rw [inv_mul_cancel₀]; rw [rpow_one]
    rw [cast_ne_zero]
    apply (nValue_pos hN).ne'
  rw [← le_div_iff₀']
  · exact floor_le (by positivity)
  apply zero_lt_two

/--
theorem `bound` / 定理 `bound`

English:
theorem bound
  given: (hN : 4096 <= N)
  statement: (N : Real) ^ (nValue N : Real)⁻¹ / exp 1 < dValue N
  proof: by
  apply div_lt_floor _
  rw [← log_le_log_iff]; rw [log_rpow]; rw [mul_comm]; rw [← div_eq_mul_inv]; rw [nValue]
  · grw [ceil_lt_mul]
    · rw [mul_comm, ← div_div, div_sqrt, le_div_iff₀]
      · norm_num [le_sqrt_log hN]
      · norm_num1
    · rw [cast_pos, lt_ceil, cast_zero, Real.sqrt_pos]
 

中文:
定理 bound
  条件: (hN : 4096 <= N)
  结论: (N : 实数) ^ (nValue N : 实数)⁻¹ / exp 1 < dValue N
  证明: by
  apply div_lt_floor _
  rw [← log_le_log_iff]; rw [log_rpow]; rw [mul_comm]; rw [← div_eq_mul_inv]; rw [nValue]
  · grw [ceil_lt_mul]
    · rw [mul_comm, ← div_div, div_sqrt, le_div_iff₀]
      · norm_num [le_sqrt_log hN]
      · norm_num1
    · rw [cast_pos, lt_ceil, cast_zero, Real.sqrt_pos]
 

Depends on / 依赖: Real.sqrt_pos, cast_pos, cast_zero, ceil_lt_mul, div_div, div_eq_mul_inv, div_lt_floor, div_sqrt, hN.trans_lt, le_sqrt_log, le_sqrt_of_sq_le, log_le_log, log_le_log_iff, log_pos, log_rpow, lt_ceil, mod_cast, mul_comm, nValue, norm_num1
-/
theorem bound (hN : 4096 <= N) : (N : Real) ^ (nValue N : Real)⁻¹ / exp 1 < dValue N := by
  apply div_lt_floor _
  rw [← log_le_log_iff]; rw [log_rpow]; rw [mul_comm]; rw [← div_eq_mul_inv]; rw [nValue]
  · grw [ceil_lt_mul]
    · rw [mul_comm, ← div_div, div_sqrt, le_div_iff₀]
      · norm_num [le_sqrt_log hN]
      · norm_num1
    · rw [cast_pos, lt_ceil, cast_zero, Real.sqrt_pos]
      refine log_pos ?_
      rw [one_lt_cast]
      exact hN.trans_lt' (by norm_num1)
    apply le_sqrt_of_sq_le
    have : (12 : Nat) * log 2 <= log N := by
      rw [← log_rpow zero_lt_two]; rw [rpow_natCast]
      exact log_le_log (by positivity) (mod_cast hN)
    refine le_trans ?_ this
    rw [← div_le_iff₀']
    · exact log_two_gt_d9.le.trans' (by norm_num1)
    · norm_num1
  · rw [cast_pos]
    exact hN.trans_lt' (by norm_num1)
  · refine div_pos zero_lt_two ?_
    rw [sub_pos]; rw [div_lt_one (exp_pos _)]
    exact exp_one_gt_two
  positivity

/--
theorem `roth_lower_bound_explicit` / 定理 `roth_lower_bound_explicit`

English:
theorem roth_lower_bound_explicit
  given: (hN : 4096 <= N)
  proof: by
  let n := nValue N
  have hn : 0 < (n : Real) := cast_pos.2 (nValue_pos <| hN.trans' <| by norm_num1)
  have hd : 0 < dValue N := dValue_pos (hN.trans' <| by norm_num1)
  have hN₀ : 0 < (N : Real) := cast_pos.2 (hN.trans' <| by norm_num1)
have hn₂ : 2 < n := three_le_nValue hN.trans' by norm_num

中文:
定理 roth_lower_bound_explicit
  条件: (hN : 4096 <= N)
  证明: by
  let n := nValue N
  have hn : 0 < (n : Real) := cast_pos.2 (nValue_pos <| hN.trans' <| by norm_num1)
  have hd : 0 < dValue N := dValue_pos (hN.trans' <| by norm_num1)
  have hN₀ : 0 < (N : Real) := cast_pos.2 (hN.trans' <| by norm_num1)
have hn₂ : 2 < n := three_le_nValue hN.trans' by norm_num

Depends on / 依赖: cast_pos, dValue, dValue_pos, exacts, hN.trans, le_N, nValue, nValue_pos, norm_num1, three_le_nValue, tsub_pos_of_lt
-/
theorem roth_lower_bound_explicit (hN : 4096 <= N) :
    (N : Real) * exp (-4 * √(log N)) < rothNumberNat N := by
  let n := nValue N
  have hn : 0 < (n : Real) := cast_pos.2 (nValue_pos <| hN.trans' <| by norm_num1)
  have hd : 0 < dValue N := dValue_pos (hN.trans' <| by norm_num1)
  have hN₀ : 0 < (N : Real) := cast_pos.2 (hN.trans' <| by norm_num1)
have hn₂ : 2 < n := three_le_nValue hN.trans' by norm_num1
  have : (2 * dValue N - 1) ^ n <= N := le_N (hN.trans' <| by norm_num1)
  calc
    _ <= (N ^ (nValue N : Real)⁻¹ / rexp 1 : Real) ^ (n - 2) / n := ?_
    _ < _ := by gcongr; exacts [(tsub_pos_of_lt hn₂).ne', bound hN]
    _ <= rothNumberNat ((2 * dValue N - 1) ^ n) := bound_aux hd.ne' hn₂.le
    _ <= rothNumberNat N := mod_cast rothNumberNat.mono this
  rw [← rpow_natCast]; rw [div_rpow (rpow_nonneg hN₀.le _) (exp_pos _).le]; rw [← rpow_mul hN₀.le]; rw [inv_mul_eq_div]; rw [cast_sub hn₂.le]; rw [cast_two]; rw [same_sub_div hn.ne']; rw [exp_one_rpow]; rw [div_div]; rw [rpow_sub hN₀]; rw [rpow_one]; rw [div_div]; rw [div_eq_mul_inv]
  gcongr _ * ?_
  rw [mul_inv]; rw [mul_inv]; rw [← exp_neg]; rw [← rpow_neg (cast_nonneg _)]; rw [neg_sub]; rw [← div_eq_mul_inv]
  have : exp (-4 * √(log N)) = exp (-2 * √(log N)) * exp (-2 * √(log N)) := by
    rw [← exp_add]; rw [← add_mul]
    norm_num
  rw [this]
  gcongr
  · rw [← le_log_iff_exp_le (rpow_pos_of_pos hN₀ _), log_rpow hN₀, ← le_div_iff₀, mul_div_assoc,
      div_sqrt, neg_mul, neg_le_neg_iff, div_mul_eq_mul_div, div_le_iff₀ hn]
    · gcongr
      apply le_ceil
    refine Real.sqrt_pos.2 (log_pos ?_)
    rw [one_lt_cast]
    exact hN.trans_lt' (by norm_num1)
  · refine (exp_neg_two_mul_le <| Real.sqrt_pos.2 <| log_pos ?_).le
    rw [one_lt_cast]
    exact hN.trans_lt' (by norm_num1)

/--
theorem `exp_four_lt` / 定理 `exp_four_lt`

English:
theorem exp_four_lt
  statement: exp 4 < 64
  proof: by
  rw [show (64 : Real) = 2 ^ ((6 : Nat) : Real) by rw [rpow_natCast]; norm_num1,
    ← lt_log_iff_exp_lt (rpow_pos_of_pos zero_lt_two _), log_rpow zero_lt_two, ← div_lt_iff₀']
  · exact log_two_gt_d9.trans_le' (by norm_num1)
  · simp

中文:
定理 exp_four_lt
  结论: exp 4 < 64
  证明: by
  rw [show (64 : Real) = 2 ^ ((6 : Nat) : Real) by rw [rpow_natCast]; norm_num1,
    ← lt_log_iff_exp_lt (rpow_pos_of_pos zero_lt_two _), log_rpow zero_lt_two, ← div_lt_iff₀']
  · exact log_two_gt_d9.trans_le' (by norm_num1)
  · simp

Depends on / 依赖: log_rpow, log_two_gt_d9, log_two_gt_d9.trans_le, lt_log_iff_exp_lt, norm_num1, rpow_natCast, rpow_pos_of_pos, trans_le, zero_lt_two
-/
theorem exp_four_lt : exp 4 < 64 := by
  rw [show (64 : Real) = 2 ^ ((6 : Nat) : Real) by rw [rpow_natCast]; norm_num1,
    ← lt_log_iff_exp_lt (rpow_pos_of_pos zero_lt_two _), log_rpow zero_lt_two, ← div_lt_iff₀']
  · exact log_two_gt_d9.trans_le' (by norm_num1)
  · simp

/--
theorem `four_zero_nine_six_lt_exp_sixteen` / 定理 `four_zero_nine_six_lt_exp_sixteen`

English:
theorem four_zero_nine_six_lt_exp_sixteen
  statement: 4096 < exp 16
  proof: by
  rw [← log_lt_iff_lt_exp (show (0 : Real) < 4096 by simp)]; rw [show (4096 : Real) = 2 ^ 12 by norm_cast]; rw [← rpow_natCast]; rw [log_rpow zero_lt_two]; rw [cast_ofNat]
  linarith [log_two_lt_d9]

中文:
定理 four_zero_nine_six_lt_exp_sixteen
  结论: 4096 < exp 16
  证明: by
  rw [← log_lt_iff_lt_exp (show (0 : Real) < 4096 by simp)]; rw [show (4096 : Real) = 2 ^ 12 by norm_cast]; rw [← rpow_natCast]; rw [log_rpow zero_lt_two]; rw [cast_ofNat]
  linarith [log_two_lt_d9]

Depends on / 依赖: cast_ofNat, log_lt_iff_lt_exp, log_rpow, log_two_lt_d9, rpow_natCast, zero_lt_two
-/
theorem four_zero_nine_six_lt_exp_sixteen : 4096 < exp 16 := by
  rw [← log_lt_iff_lt_exp (show (0 : Real) < 4096 by simp)]; rw [show (4096 : Real) = 2 ^ 12 by norm_cast]; rw [← rpow_natCast]; rw [log_rpow zero_lt_two]; rw [cast_ofNat]
  linarith [log_two_lt_d9]

/--
theorem `lower_bound_le_one'` / 定理 `lower_bound_le_one'`

English:
theorem lower_bound_le_one'
  given: (hN : 2 <= N) (hN' : N <= 4096)
  proof: by
  rw [← log_le_log_iff (mul_pos (cast_pos.2 (zero_lt_two.trans_le hN)) (exp_pos _)) zero_lt_one]; rw [log_one]; rw [log_mul (cast_pos.2 (zero_lt_two.trans_le hN)).ne' (exp_pos _).ne']; rw [log_exp]; rw [neg_mul]; rw [←
    sub_eq_add_neg]; rw [sub_nonpos]; rw [←
    div_le_iff₀ (Real.sqrt_pos.2 <

中文:
定理 lower_bound_le_one'
  条件: (hN : 2 <= N) (hN' : N <= 4096)
  证明: by
  rw [← log_le_log_iff (mul_pos (cast_pos.2 (zero_lt_two.trans_le hN)) (exp_pos _)) zero_lt_one]; rw [log_one]; rw [log_mul (cast_pos.2 (zero_lt_two.trans_le hN)).ne' (exp_pos _).ne']; rw [log_exp]; rw [neg_mul]; rw [←
    sub_eq_add_neg]; rw [sub_nonpos]; rw [←
    div_le_iff₀ (Real.sqrt_pos.2 <

Depends on / 依赖: Real.sqrt_pos, cast_pos, div_sqrt, exp_pos, four_zero_nine_six, le_trans, log_exp, log_le_iff_le_exp, log_le_log_iff, log_mul, log_one, log_pos, mul_pos, neg_mul, norm_num1, one_lt_cast, one_lt_two, one_lt_two.trans_le, sqrt_le_left, sqrt_pos
-/
theorem lower_bound_le_one' (hN : 2 <= N) (hN' : N <= 4096) :
    (N : Real) * exp (-4 * √(log N)) <= 1 := by
  rw [← log_le_log_iff (mul_pos (cast_pos.2 (zero_lt_two.trans_le hN)) (exp_pos _)) zero_lt_one]; rw [log_one]; rw [log_mul (cast_pos.2 (zero_lt_two.trans_le hN)).ne' (exp_pos _).ne']; rw [log_exp]; rw [neg_mul]; rw [←
    sub_eq_add_neg]; rw [sub_nonpos]; rw [←
    div_le_iff₀ (Real.sqrt_pos.2 <| log_pos <| one_lt_cast.2 <| one_lt_two.trans_le hN)]; rw [div_sqrt]; rw [sqrt_le_left zero_le_four]; rw [log_le_iff_le_exp (cast_pos.2 (zero_lt_two.trans_le hN))]
  norm_num1
  apply le_trans _ four_zero_nine_six_lt_exp_sixteen.le
  exact mod_cast hN'

/--
theorem `lower_bound_le_one` / 定理 `lower_bound_le_one`

English:
theorem lower_bound_le_one
  given: (hN : 1 <= N) (hN' : N <= 4096)
  proof: by
  obtain rfl | hN := hN.eq_or_lt
  · simp
  · exact lower_bound_le_one' hN hN'

中文:
定理 lower_bound_le_one
  条件: (hN : 1 <= N) (hN' : N <= 4096)
  证明: by
  obtain rfl | hN := hN.eq_or_lt
  · simp
  · exact lower_bound_le_one' hN hN'

Depends on / 依赖: eq_or_lt, hN.eq_or_lt, lower_bound_le_one
-/
theorem lower_bound_le_one (hN : 1 <= N) (hN' : N <= 4096) :
    (N : Real) * exp (-4 * √(log N)) <= 1 := by
  obtain rfl | hN := hN.eq_or_lt
  · simp
  · exact lower_bound_le_one' hN hN'

/--
theorem `roth_lower_bound` / 定理 `roth_lower_bound`

English:
theorem roth_lower_bound
  statement: (N : Real) * exp (-4 * √(log N)) <= rothNumberNat N
  proof: by
  obtain rfl | hN := Nat.eq_zero_or_pos N
  · simp
  obtain h₁ | h₁ := le_or_gt 4096 N
  · exact (roth_lower_bound_explicit h₁).le
  · apply (lower_bound_le_one hN h₁.le).trans
    simpa using! rothNumberNat.monotone hN

中文:
定理 roth_lower_bound
  结论: (N : 实数) * exp (-4 * √(log N)) <= rothNumber自然数 N
  证明: by
  obtain rfl | hN := Nat.eq_zero_or_pos N
  · simp
  obtain h₁ | h₁ := le_or_gt 4096 N
  · exact (roth_lower_bound_explicit h₁).le
  · apply (lower_bound_le_one hN h₁.le).trans
    simpa using! rothNumberNat.monotone hN

Depends on / 依赖: Nat.eq_zero_or_pos, eq_zero_or_pos, le_or_gt, lower_bound_le_one, monotone, rothNumberNat, rothNumberNat.monotone, roth_lower_bound_explicit
-/
theorem roth_lower_bound : (N : Real) * exp (-4 * √(log N)) <= rothNumberNat N := by
  obtain rfl | hN := Nat.eq_zero_or_pos N
  · simp
  obtain h₁ | h₁ := le_or_gt 4096 N
  · exact (roth_lower_bound_explicit h₁).le
  · apply (lower_bound_le_one hN h₁.le).trans
    simpa using! rothNumberNat.monotone hN

end Behrend
