/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Andrew Yang, Yaël Dillies
-/
module
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finsupp.Order
public import Mathlib.LinearAlgebra.Finsupp.LSum

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity.Basic

/-!
# Convex spaces

This file defines convex spaces as an algebraic structure supporting finite convex combinations.

## Main definitions

* `Convexity.StdSimplex R M`: A finitely supported probability distribution over elements of `M`
  with coefficients in `R`. The weights are non-negative and sum to 1.
* `Convexity.StdSimplex.map`: Map a function over the support of a standard simplex.
* `Convexity.ConvexSpace R M`: A typeclass for spaces `M` equipped with an operation
  `Convexity.sConvexComb : StdSimplex R M → M` satisfying monadic laws.
* `Convexity.iConvexComb`: Indexed convex combination operator.
* `Convexity.convexCombPair`: Binary convex combinations of two points.

## Design

The design follows a monadic structure where `StdSimplex R` forms a monad and `convexCombination`
is a monadic algebra. This eliminates the need for explicit extensionality axioms and resolves
universe issues with indexed families.

-/

@[expose] public noncomputable section

universe u v w u₁ u₂

open Finsupp

namespace Convexity
variable {R X M N P I J K : Type*}

/--
Definition of `StdSimplex` / `StdSimplex` 的定义

English:
structure StdSimplex
  parameters: (R : Type u) [LE R] [AddCommMonoid R] [One R] (M : Type v)
  axioms and operations (3):
    - weights : M ->₀ R
    - nonneg : 0 <= weights
    - total : weights.sum (fun _ r => r) = 1

中文:
结构 标准单纯形
  参数: (R : 类型u) [LE R] [加法交换幺半群 R] [幺 R] (M : 类型v)
  公理与运算 (3 个):
    - weights : M ->₀ R
    - nonneg : 0 <= weights
    - total : weights.求和 (fun _ r => r) = 1
-/
structure StdSimplex (R : Type u) [LE R] [AddCommMonoid R] [One R] (M : Type v) where
  /-- The weights of the `StdSimplex` as a `Finsupp`. -/
  weights : M ->₀ R
  /-- All weights are non-negative. -/
  nonneg : 0 <= weights
  /-- The weights sum to 1. -/
  total : weights.sum (fun _ r => r) = 1

attribute [simp] StdSimplex.total
grind_pattern StdSimplex.nonneg => self.weights
grind_pattern StdSimplex.total => self.weights

initialize_simps_projections StdSimplex (as_prefix weights)

namespace StdSimplex
section Semiring
variable {R : Type u} [PartialOrder R] [Semiring R] {M N P : Type*} {w : StdSimplex R M} {x : M}

/--
lemma `weights_nonneg` / 引理 `weights_nonneg`

English:
lemma weights_nonneg
  given: {w : StdSimplex R M} (i : M)
  statement: 0 <= w.weights i
  proof: w.nonneg i

中文:
引理 weights_nonneg
  条件: {w : 标准单纯形 R M} (i : M)
  结论: 0 <= w.weights i
  证明: w.nonneg i
-/
@[simp] lemma weights_nonneg {w : StdSimplex R M} (i : M) : 0 <= w.weights i := w.nonneg i

/--
lemma `weights_ne_zero` / 引理 `weights_ne_zero`

English:
lemma weights_ne_zero
  given: [Nontrivial R]
  statement: forall w : StdSimplex R M, w.weights != 0
  proof: by
  rintro ⟨_, -, total⟩ rfl; simp at total

中文:
引理 weights_ne_zero
  条件: [非平凡 R]
  结论: 对任意 w : 标准单纯形 R M, w.weights != 0
  证明: by
  rintro ⟨_, -, total⟩ rfl; simp at total
-/
@[simp] lemma weights_ne_zero [Nontrivial R] : forall w : StdSimplex R M, w.weights != 0 := by
  rintro ⟨_, -, total⟩ rfl; simp at total

/--
lemma `support_weights_nonempty` / 引理 `support_weights_nonempty`

English:
lemma support_weights_nonempty
  given: [Nontrivial R] (w : StdSimplex R M)
  proof: by simp

中文:
引理 support_weights_nonempty
  条件: [非平凡 R] (w : 标准单纯形 R M)
  证明: by simp
-/
lemma support_weights_nonempty [Nontrivial R] (w : StdSimplex R M) :
    w.weights.support.Nonempty := by simp

/--
lemma `nonempty` / 引理 `nonempty`

English:
lemma nonempty
  given: [Nontrivial R] (w : StdSimplex R M)
  statement: Nonempty M
  proof: w.support_weights_nonempty.to_type

中文:
引理 nonempty
  条件: [非平凡 R] (w : 标准单纯形 R M)
  结论: 非空 M
  证明: w.support_weights_nonempty.to_type

Depends on / 依赖: support_weights_nonempty, to_type, w.support_weights_nonempty.to_type
-/
lemma nonempty [Nontrivial R] (w : StdSimplex R M) : Nonempty M :=
  w.support_weights_nonempty.to_type

/--
lemma `weights_inj` / 引理 `weights_inj`

English:
lemma weights_inj
  given: {f g : StdSimplex R M}
  statement: f.weights = g.weights ↔ f = g
  proof: by
  cases f; cases g; simp

@[ext] alias ⟨ext, _⟩ := weights_inj

中文:
引理 weights_inj
  条件: {f g : 标准单纯形 R M}
  结论: f.weights = g.weights ↔ f = g
  证明: by
  cases f; cases g; simp

@[ext] alias ⟨ext, _⟩ := weights_inj
-/
@[simp] lemma weights_inj {f g : StdSimplex R M} : f.weights = g.weights ↔ f = g := by
  cases f; cases g; simp

@[ext] alias ⟨ext, _⟩ := weights_inj

variable [IsStrictOrderedRing R]

/-- The point mass distribution concentrated at `x`. -/
@[simps weights]
/--
Definition of `single` / `single` 的定义

English:
definition single
  signature: (x : M)
  body: .single x 1
  nonneg := by simp
  total := by simp

中文:
定义 single
  签名: (x : M)
  定义体: .single x 1
  nonneg := by simp
  total := by simp

Depends on / 依赖: single
-/
def single (x : M) : StdSimplex R M where
  weights := .single x 1
  nonneg := by simp
  total := by simp

/--
theorem `mk_single` / 定理 `mk_single`

English:
theorem mk_single
  given: (x : M) {nonneg total}
  statement: (mk (.single x (1 : R)) nonneg total) = single x
  proof: rfl

中文:
定理 mk_single
  条件: (x : M) {nonneg total}
  结论: (mk (.single x (1 : R)) nonneg total) = single x
  证明: rfl
-/
theorem mk_single (x : M) {nonneg total} : (mk (.single x (1 : R)) nonneg total) = single x := rfl

/--
lemma `support_weights_eq_singleton` / 引理 `support_weights_eq_singleton`

English:
lemma support_weights_eq_singleton
  statement: w.weights.support = {x} ↔ w = single x where
  proof: by
    rw [support_eq_singleton']
    rintro ⟨a, ha, hwa⟩
    ext : 1
    simp only [hwa, weights_single]
    congr
    simpa [hwa] using w.total
  mpr := by rintro rfl; simp

中文:
引理 support_weights_eq_singleton
  结论: w.weights.support = {x} ↔ w = single x where
  证明: by
    rw [support_eq_singleton']
    rintro ⟨a, ha, hwa⟩
    ext : 1
    simp only [hwa, weights_single]
    congr
    simpa [hwa] using w.total
  mpr := by rintro rfl; simp
-/
@[simp] lemma support_weights_eq_singleton : w.weights.support = {x} ↔ w = single x where
  mp := by
    rw [support_eq_singleton']
    rintro ⟨a, ha, hwa⟩
    ext : 1
    simp only [hwa, weights_single]
    congr
    simpa [hwa] using w.total
  mpr := by rintro rfl; simp

/-- A probability distribution with weight `s` on `x` and weight `t` on `y`. -/
@[simps weights]
/--
Definition of `duple` / `duple` 的定义

English:
definition duple
  signature: (x y : M) {s t : R} (hs : 0 <= s) (ht : 0 <= t) (h : s + t = 1)
  body: .single x s + .single y t
  nonneg := add_nonneg (by simpa) (by simpa)
  total := by classical simpa [sum_add_index]

中文:
定义 duple
  签名: (x y : M) {s t : R} (hs : 0 <= s) (ht : 0 <= t) (h : s + t = 1)
  定义体: .single x s + .single y t
  nonneg := add_nonneg (by simpa) (by simpa)
  total := by classical simpa [sum_add_index]

Depends on / 依赖: single
-/
def duple (x y : M) {s t : R} (hs : 0 <= s) (ht : 0 <= t) (h : s + t = 1) : StdSimplex R M where
  weights := .single x s + .single y t
  nonneg := add_nonneg (by simpa) (by simpa)
  total := by classical simpa [sum_add_index]

/--
Map a function over the support of a standard simplex.
For each n : N, the weight is the sum of weights of all m : M with g m = n.
-/
@[simps weights]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {M : Type v} {N : Type w} (g : M -> N) (f : StdSimplex R M)
  body: f.weights.mapDomain g
  nonneg := f.weights.mapDomain_nonneg f.nonneg
  total := by simp [sum_mapDomain_index]

@[simp]

中文:
定义 map
  签名: {M : 类型v} {N : 类型 w} (g : M -> N) (f : 标准单纯形 R M)
  定义体: f.weights.mapDomain g
  nonneg := f.weights.mapDomain_nonneg f.nonneg
  total := by simp [sum_mapDomain_index]

@[simp]

Depends on / 依赖: f.weights.mapDomain, mapDomain, weights
-/
def map {M : Type v} {N : Type w} (g : M -> N) (f : StdSimplex R M) : StdSimplex R N where
  weights := f.weights.mapDomain g
  nonneg := f.weights.mapDomain_nonneg f.nonneg
  total := by simp [sum_mapDomain_index]

@[simp]
/--
lemma `map_const` / 引理 `map_const`

English:
lemma map_const
  given: (f : StdSimplex R M) (x : N)
  statement: f.map (fun _ => x) = .single x
  proof: by
  ext a; by_cases x = a <;> simp [*, mapDomain]

@[simp]

中文:
引理 map_const
  条件: (f : 标准单纯形 R M) (x : N)
  结论: f.map (fun _ => x) = .single x
  证明: by
  ext a; by_cases x = a <;> simp [*, mapDomain]

@[simp]

Depends on / 依赖: mapDomain
-/
lemma map_const (f : StdSimplex R M) (x : N) : f.map (fun _ => x) = .single x := by
  ext a; by_cases x = a <;> simp [*, mapDomain]

@[simp]
/--
lemma `map_single` / 引理 `map_single`

English:
lemma map_single
  given: (x : M) (f : M -> N)
  statement: (single (R := R) x).map f = .single (f x)
  proof: by
  ext; simp

@[simp]

中文:
引理 map_single
  条件: (x : M) (f : M -> N)
  结论: (single (R := R) x).map f = .single (f x)
  证明: by
  ext; simp

@[simp]

Depends on / 依赖: single
-/
lemma map_single (x : M) (f : M -> N) : (single (R := R) x).map f = .single (f x) := by
  ext; simp

@[simp]
/--
lemma `map_duple` / 引理 `map_duple`

English:
lemma map_duple
  given: {s t : R} (hs : 0 <= s) (ht : 0 <= t) (h : s + t = 1) (x y : M) (f : M -> N)
  proof: by
  ext; simp [mapDomain_add]

@[simp]

中文:
引理 map_duple
  条件: {s t : R} (hs : 0 <= s) (ht : 0 <= t) (h : s + t = 1) (x y : M) (f : M -> N)
  证明: by
  ext; simp [mapDomain_add]

@[simp]

Depends on / 依赖: mapDomain_add
-/
lemma map_duple {s t : R} (hs : 0 <= s) (ht : 0 <= t) (h : s + t = 1) (x y : M) (f : M -> N) :
    (duple x y hs ht h).map f = duple (f x) (f y) hs ht h := by
  ext; simp [mapDomain_add]

@[simp]
/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  given: (f : StdSimplex R M)
  statement: f.map id = f
  proof: by
  ext; simp

中文:
引理 map_id
  条件: (f : 标准单纯形 R M)
  结论: f.map id = f
  证明: by
  ext; simp
-/
lemma map_id (f : StdSimplex R M) : f.map id = f := by
  ext; simp

/--
lemma `map_comp` / 引理 `map_comp`

English:
lemma map_comp
  given: (f : StdSimplex R M) (g₁ : M -> N) (g₂ : N -> P)
  proof: by
  ext; simp [mapDomain_comp]

中文:
引理 map_comp
  条件: (f : 标准单纯形 R M) (g₁ : M -> N) (g₂ : N -> P)
  证明: by
  ext; simp [mapDomain_comp]

Depends on / 依赖: e.symm, mapDomain_comp
-/
lemma map_comp (f : StdSimplex R M) (g₁ : M -> N) (g₂ : N -> P) :
    f.map (g₂ ∘ g₁) = (f.map g₁).map g₂ := by
  ext; simp [mapDomain_comp]

/--
lemma `map_map` / 引理 `map_map`

English:
lemma map_map
  given: (f : StdSimplex R M) (g₁ : M -> N) (g₂ : N -> P)
  proof: (map_comp ..).symm

中文:
引理 map_map
  条件: (f : 标准单纯形 R M) (g₁ : M -> N) (g₂ : N -> P)
  证明: (map_comp ..).symm

Depends on / 依赖: map_comp
-/
lemma map_map (f : StdSimplex R M) (g₁ : M -> N) (g₂ : N -> P) :
    (f.map g₁).map g₂ = f.map (fun x => g₂ (g₁ x)) :=
  (map_comp ..).symm

/--
Join operation for standard simplices (monadic join).
Given a distribution over distributions, flattens it to a single distribution.

Use `ConvexSpace.sConvexComb` instead.
-/
@[simps weights]
/--
Definition of `join` / `join` 的定义

English:
definition join
  signature: (f : StdSimplex R (StdSimplex R M))
  body: f.weights.sum (fun d r => r • d.weights)
  nonneg := f.weights.sum_nonneg fun d _ => smul_nonneg (f.nonneg d) d.nonneg
  total := by simp [sum_sum_index, sum_smul_index, ← mul_sum]

中文:
定义 join
  签名: (f : 标准单纯形 R (标准单纯形 R M))
  定义体: f.weights.sum (fun d r => r • d.weights)
  nonneg := f.weights.sum_nonneg fun d _ => smul_nonneg (f.nonneg d) d.nonneg
  total := by simp [sum_sum_index, sum_smul_index, ← mul_sum]

Depends on / 依赖: d.weights, f.weights.sum, weights
-/
def join (f : StdSimplex R (StdSimplex R M)) : StdSimplex R M where
  weights := f.weights.sum (fun d r => r • d.weights)
  nonneg := f.weights.sum_nonneg fun d _ => smul_nonneg (f.nonneg d) d.nonneg
  total := by simp [sum_sum_index, sum_smul_index, ← mul_sum]

/--
lemma `join_join` / 引理 `join_join`

English:
lemma join_join
  given: (f : StdSimplex R (StdSimplex R (StdSimplex R M)))
  proof: by
  ext1; simp [mapDomain, add_smul, sum_sum_index, sum_smul_index, smul_sum, mul_smul]

中文:
引理 join_join
  条件: (f : 标准单纯形 R (标准单纯形 R (标准单纯形 R M)))
  证明: by
  ext1; simp [mapDomain, add_smul, sum_sum_index, sum_smul_index, smul_sum, mul_smul]
-/
private lemma join_join (f : StdSimplex R (StdSimplex R (StdSimplex R M))) :
    f.join.join = (f.map (·.join)).join := by
  ext1; simp [mapDomain, add_smul, sum_sum_index, sum_smul_index, smul_sum, mul_smul]

/--
lemma `map_join` / 引理 `map_join`

English:
lemma map_join
  given: (f : StdSimplex R (StdSimplex R M)) (g : M -> N)
  proof: by
  ext1; simp [mapDomain, add_smul, sum_sum_index, sum_smul_index, smul_sum]

中文:
引理 map_join
  条件: (f : 标准单纯形 R (标准单纯形 R M)) (g : M -> N)
  证明: by
  ext1; simp [mapDomain, add_smul, sum_sum_index, sum_smul_index, smul_sum]
-/
private lemma map_join (f : StdSimplex R (StdSimplex R M)) (g : M -> N) :
    f.join.map g = (f.map (·.map g)).join := by
  ext1; simp [mapDomain, add_smul, sum_sum_index, sum_smul_index, smul_sum]

/--
lemma `join_single` / 引理 `join_single`

English:
lemma join_single
  given: (x : StdSimplex R M)
  statement: join (.single x) = x
  proof: by
  ext; simp [join, ← mk_single]

中文:
引理 join_single
  条件: (x : 标准单纯形 R M)
  结论: join (.single x) = x
  证明: by
  ext; simp [join, ← mk_single]
-/
@[simp] private lemma join_single (x : StdSimplex R M) : join (.single x) = x := by
  ext; simp [join, ← mk_single]

end Semiring

section Semifield
variable [Semifield K] [LinearOrder K] [IsStrictOrderedRing K]

/--
lemma `restrict_nonneg_aux` / 引理 `restrict_nonneg_aux`

English:
lemma restrict_nonneg_aux
  given: {w : StdSimplex K X} {p : X -> Prop} [DecidablePred p]
  proof: sum_nonneg by simp [filter_apply, apply_ite]

中文:
引理 restrict_nonneg_aux
  条件: {w : 标准单纯形 K X} {p : X -> 命题} [DecidablePred p]
  证明: sum_nonneg by simp [filter_apply, apply_ite]
-/
private lemma restrict_nonneg_aux {w : StdSimplex K X} {p : X -> Prop} [DecidablePred p] :
    0 <= (filter p w.weights).sum fun _x k => k :=
sum_nonneg by simp [filter_apply, apply_ite]

/--
lemma `restrict_ne_zero_aux` / 引理 `restrict_ne_zero_aux`

English:
lemma restrict_ne_zero_aux
  statement: {w : StdSimplex K X} {p : X -> Prop} [DecidablePred p]
  proof: (sum_pos (by simp +contextual [lt_iff_le_and_ne, eq_comm]) <| by simpa [ne_iff, filter_apply]).ne'

中文:
引理 restrict_ne_zero_aux
  结论: {w : 标准单纯形 K X} {p : X -> 命题} [DecidablePred p]
  证明: (sum_pos (by simp +contextual [lt_iff_le_and_ne, eq_comm]) <| by simpa [ne_iff, filter_apply]).ne'
-/
private lemma restrict_ne_zero_aux {w : StdSimplex K X} {p : X -> Prop} [DecidablePred p]
    (hp : exists a, p a ∧ w.weights a != 0) :
    (filter p w.weights).sum (fun _x k => k) != 0 :=
  (sum_pos (by simp +contextual [lt_iff_le_and_ne, eq_comm]) <| by simpa [ne_iff, filter_apply]).ne'

/--
Definition of `restrict` / `restrict` 的定义

English:
definition restrict
  signature: (w : StdSimplex K X) (s : Set X) (hs : exists x in s, w.weights x != 0)
  body: open scoped Classical in
    ((w.weights.filter (· in s)).sum fun x k => k)⁻¹ • w.weights.filter (· in s)
  nonneg := by
    classical
    exact smul_nonneg (inv_nonneg.2 restrict_nonneg_aux) fun _ => by simp [filter_apply, apply_ite]
  total := by classical simp [sum_smul_index, ← mul_sum, restrict

中文:
定义 restrict
  签名: (w : 标准单纯形 K X) (s : 集合 X) (hs : 存在 x in s, w.weights x != 0)
  定义体: open scoped Classical in
    ((w.weights.filter (· in s)).sum fun x k => k)⁻¹ • w.weights.filter (· in s)
  nonneg := by
    classical
    exact smul_nonneg (inv_nonneg.2 restrict_nonneg_aux) fun _ => by simp [filter_apply, apply_ite]
  total := by classical simp [sum_smul_index, ← mul_sum, restrict

Depends on / 依赖: Classical, scoped
-/
def restrict (w : StdSimplex K X) (s : Set X) (hs : exists x in s, w.weights x != 0) : StdSimplex K X where
  weights := open scoped Classical in
    ((w.weights.filter (· in s)).sum fun x k => k)⁻¹ • w.weights.filter (· in s)
  nonneg := by
    classical
    exact smul_nonneg (inv_nonneg.2 restrict_nonneg_aux) fun _ => by simp [filter_apply, apply_ite]
  total := by classical simp [sum_smul_index, ← mul_sum, restrict_ne_zero_aux hs]

/--
lemma `weights_restrict` / 引理 `weights_restrict`

English:
lemma weights_restrict
  given: (w : StdSimplex K X) (s : Set X) (hs) [DecidablePred (· in s)]
  proof: by
  simp [restrict]; congr

中文:
引理 weights_restrict
  条件: (w : 标准单纯形 K X) (s : 集合 X) (hs) [DecidablePred (· in s)]
  证明: by
  simp [restrict]; congr

Depends on / 依赖: restrict
-/
lemma weights_restrict (w : StdSimplex K X) (s : Set X) (hs) [DecidablePred (· in s)] :
    (w.restrict s hs).weights =
      ((w.weights.filter (· in s)).sum fun _x k => k)⁻¹ • w.weights.filter (· in s) := by
  simp [restrict]; congr

variable [IsDomain K]

@[simp]
/--
lemma `support_weights_restrict` / 引理 `support_weights_restrict`

English:
lemma support_weights_restrict
  given: (w : StdSimplex K X) (s : Set X) (hs) [DecidablePred (· in s)]
  proof: by
  have : (w.weights.filter (· in s)).sum (fun x k => k) != 0 :=
    (sum_pos (by simp +contextual [lt_iff_le_and_ne, eq_comm]) <| by
      simpa [ne_iff, filter_apply]).ne'
  rw [weights_restrict]; rw [support_smul_eq (by convert inv_ne_zero this)]
  simp

中文:
引理 support_weights_restrict
  条件: (w : 标准单纯形 K X) (s : 集合 X) (hs) [DecidablePred (· in s)]
  证明: by
  have : (w.weights.filter (· in s)).sum (fun x k => k) != 0 :=
    (sum_pos (by simp +contextual [lt_iff_le_and_ne, eq_comm]) <| by
      simpa [ne_iff, filter_apply]).ne'
  rw [weights_restrict]; rw [support_smul_eq (by convert inv_ne_zero this)]
  simp

Depends on / 依赖: contextual, convert, eq_comm, filter, filter_apply, inv_ne_zero, lt_iff_le_and_ne, ne_iff, sum_pos, support_smul_eq, w.weights.filter, weights, weights_restrict
-/
lemma support_weights_restrict (w : StdSimplex K X) (s : Set X) (hs) [DecidablePred (· in s)] :
    (w.restrict s hs).weights.support = w.weights.support.filter (· in s) := by
  have : (w.weights.filter (· in s)).sum (fun x k => k) != 0 :=
    (sum_pos (by simp +contextual [lt_iff_le_and_ne, eq_comm]) <| by
      simpa [ne_iff, filter_apply]).ne'
  rw [weights_restrict]; rw [support_smul_eq (by convert inv_ne_zero this)]
  simp

/--
lemma `restrict_singleton` / 引理 `restrict_singleton`

English:
lemma restrict_singleton
  given: (w : StdSimplex K X) (x : X) (hx)
  proof: by
  classical
  simp only [← support_weights_eq_singleton, support_weights_restrict, Set.mem_singleton_iff]
  ext
  simp only [Finset.mem_filter, mem_support_iff, ne_eq, Finset.mem_singleton, and_iff_right_iff_imp]
  rintro rfl
  simpa using hx

中文:
引理 restrict_singleton
  条件: (w : 标准单纯形 K X) (x : X) (hx)
  证明: by
  classical
  simp only [← support_weights_eq_singleton, support_weights_restrict, Set.mem_singleton_iff]
  ext
  simp only [Finset.mem_filter, mem_support_iff, ne_eq, Finset.mem_singleton, and_iff_right_iff_imp]
  rintro rfl
  simpa using hx
-/
@[simp] lemma restrict_singleton (w : StdSimplex K X) (x : X) (hx) :
    w.restrict {x} hx = single x := by
  classical
  simp only [← support_weights_eq_singleton, support_weights_restrict, Set.mem_singleton_iff]
  ext
  simp only [Finset.mem_filter, mem_support_iff, ne_eq, Finset.mem_singleton, and_iff_right_iff_imp]
  rintro rfl
  simpa using hx

end Semifield
end StdSimplex

/--
Definition of `ConvexSpace` / `ConvexSpace` 的定义

English:
class ConvexSpace
  parameters: (R : Type u) (M : Type v)
  axioms and operations (4):
    - mk' : :
    - sConvexComb([inst₁] [inst₂] [inst₃] (f : StdSimplex R M)) : M
    - sConvexComb_single((x : M)) : sConvexComb (.single x) = x
    - assoc((f : StdSimplex R (StdSimplex R M))) : sConvexComb (f.map sConvexComb) = sConvexComb f.join

中文:
类 凸空间
  参数: (R : 类型u) (M : 类型v)
  公理与运算 (4 个):
    - mk' : :
    - sConvexComb([inst₁] [inst₂] [inst₃] (f : 标准单纯形 R M)) : M
    - sConvexComb_single((x : M)) : sConvexComb (.single x) = x
    - assoc((f : 标准单纯形 R (标准单纯形 R M))) : sConvexComb (f.map sConvexComb) = sConvexComb f.join
-/
class ConvexSpace (R : Type u) (M : Type v)
    [inst₁ : PartialOrder R] [inst₂ : Semiring R] [inst₃ : IsStrictOrderedRing R] where
  /-- Use `mk` instead. -/
  mk' ::
  /-- Take a convex combination with the given probability distribution over points. -/
  /- FIXME: Lean makes `inst₁`, `inst₂`, `inst₃` implicit by default, which renders `sConvexComb`
  unusable without these manual `[inst]` binders. Why is this so? Shouldn't typeclass arguments to
  a `structure` also be typeclass arguments to its fields? -/
  sConvexComb [inst₁] [inst₂] [inst₃] (f : StdSimplex R M) : M
  /-- A convex combination of a single point is that point. -/
  sConvexComb_single (x : M) : sConvexComb (.single x) = x
  /-- Associativity of convex combination (monadic join law).

  Use `sConvexComb_sConvexComb` instead. -/
  assoc (f : StdSimplex R (StdSimplex R M)) :
    sConvexComb (f.map sConvexComb) = sConvexComb f.join

open ConvexSpace StdSimplex

variable [PartialOrder R] [Semiring R] [IsStrictOrderedRing R]
  [ConvexSpace R M] [ConvexSpace R N] [ConvexSpace R P]

export ConvexSpace (sConvexComb sConvexComb_single)

attribute [simp] sConvexComb_single

@[deprecated (since := "2026-05-04")] alias ConvexSpace.convexCombination := sConvexComb

@[deprecated (since := "2026-05-04")]
alias ConvexSpace.convexCombination_single := sConvexComb_single

/--
Definition of `iConvexComb` / `iConvexComb` 的定义

English:
definition iConvexComb
  signature: (s : StdSimplex R I) (f : I -> M)
  body: sConvexComb (s.map f)

中文:
定义 iConvexComb
  签名: (s : 标准单纯形 R I) (f : I -> M)
  定义体: sConvexComb (s.map f)

Depends on / 依赖: s.map, sConvexComb
-/
def iConvexComb (s : StdSimplex R I) (f : I -> M) : M := sConvexComb (s.map f)

/--
Definition of `convexCombPair` / `convexCombPair` 的定义

English:
definition convexCombPair
  signature: (s t : R) (hs : 0 <= s) (ht : 0 <= t) (hst : s + t = 1) (x y : M)
  body: sConvexComb (.duple x y hs ht hst)

@[deprecated (since := "2026-05-15")] alias convexComboPair := convexCombPair

中文:
定义 convexCombPair
  签名: (s t : R) (hs : 0 <= s) (ht : 0 <= t) (hst : s + t = 1) (x y : M)
  定义体: sConvexComb (.duple x y hs ht hst)

@[deprecated (since := "2026-05-15")] alias convexComboPair := convexCombPair

Depends on / 依赖: sConvexComb
-/
def convexCombPair (s t : R) (hs : 0 <= s) (ht : 0 <= t) (hst : s + t = 1) (x y : M) : M :=
  sConvexComb (.duple x y hs ht hst)

@[deprecated (since := "2026-05-15")] alias convexComboPair := convexCombPair

namespace StdSimplex

-- We export `sConvexComb` and `iConvexComb` to allow dot notation on the `StdSimplex` argument.
export ConvexSpace (sConvexComb)
export Convexity (iConvexComb)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConvexSpace R (StdSimplex R I)
  body: σ.join
  assoc f := by exact (join_join f).symm
  sConvexComb_single := by exact join_single

中文:
实例 :
  签名: 凸空间 R (标准单纯形 R I)
  定义体: σ.join
  assoc f := by exact (join_join f).symm
  sConvexComb_single := by exact join_single
-/
instance : ConvexSpace R (StdSimplex R I) where
  sConvexComb σ := σ.join
  assoc f := by exact (join_join f).symm
  sConvexComb_single := by exact join_single

/--
lemma `weights_sConvexComb` / 引理 `weights_sConvexComb`

English:
lemma weights_sConvexComb
  given: (f : StdSimplex R (StdSimplex R I))
  proof: StdSimplex.weights_join _

中文:
引理 weights_sConvexComb
  条件: (f : 标准单纯形 R (标准单纯形 R I))
  证明: StdSimplex.weights_join _
-/
@[simp] lemma weights_sConvexComb (f : StdSimplex R (StdSimplex R I)) :
    f.sConvexComb.weights = f.weights.sum (fun d r => r • d.weights) :=
  StdSimplex.weights_join _

/--
lemma `weights_iConvexComb` / 引理 `weights_iConvexComb`

English:
lemma weights_iConvexComb
  given: (w : StdSimplex R I) (f : I -> StdSimplex R I)
  proof: by
  simp [iConvexComb, sum_mapDomain_index, add_smul]

中文:
引理 weights_iConvexComb
  条件: (w : 标准单纯形 R I) (f : I -> 标准单纯形 R I)
  证明: by
  simp [iConvexComb, sum_mapDomain_index, add_smul]
-/
@[simp] lemma weights_iConvexComb (w : StdSimplex R I) (f : I -> StdSimplex R I) :
    (iConvexComb w f).weights = w.weights.sum (fun i r => r • (f i).weights) := by
  simp [iConvexComb, sum_mapDomain_index, add_smul]

/--
lemma `weights_convexCombPair` / 引理 `weights_convexCombPair`

English:
lemma weights_convexCombPair
  given: (w w' : StdSimplex R I) (s t : R) (hs ht hst)
  proof: by
  classical simp [convexCombPair, sum_add_index, add_smul]

中文:
引理 weights_convexCombPair
  条件: (w w' : 标准单纯形 R I) (s t : R) (hs ht hst)
  证明: by
  classical simp [convexCombPair, sum_add_index, add_smul]
-/
@[simp] lemma weights_convexCombPair (w w' : StdSimplex R I) (s t : R) (hs ht hst) :
    (convexCombPair s t hs ht hst w w').weights = s • w.weights + t • w'.weights := by
  classical simp [convexCombPair, sum_add_index, add_smul]

/--
lemma `map_sConvexComb` / 引理 `map_sConvexComb`

English:
lemma map_sConvexComb
  given: (s : StdSimplex R (StdSimplex R I)) (f : I -> J)
  proof: StdSimplex.map_join s f

中文:
引理 map_sConvexComb
  条件: (s : 标准单纯形 R (标准单纯形 R I)) (f : I -> J)
  证明: StdSimplex.map_join s f

Depends on / 依赖: StdSimplex, StdSimplex.map_join, map_join
-/
lemma map_sConvexComb (s : StdSimplex R (StdSimplex R I)) (f : I -> J) :
    s.sConvexComb.map f = (s.map (map f)).sConvexComb :=
  StdSimplex.map_join s f

variable [Semifield K] [LinearOrder K] [IsStrictOrderedRing K]

/--
lemma `convexCombPair_restrict_restrict_compl` / 引理 `convexCombPair_restrict_restrict_compl`

English:
lemma convexCombPair_restrict_restrict_compl
  statement: (w : StdSimplex K I) (s : Set I) (hs hs')
  proof: by
  ext : 1
  simp only [Set.mem_compl_iff] at hs'
  simp [weights_restrict, smul_inv_smul₀, restrict_ne_zero_aux, hs, hs']

中文:
引理 convexCombPair_restrict_restrict_compl
  结论: (w : 标准单纯形 K I) (s : 集合 I) (hs hs')
  证明: by
  ext : 1
  simp only [Set.mem_compl_iff] at hs'
  simp [weights_restrict, smul_inv_smul₀, restrict_ne_zero_aux, hs, hs']

Depends on / 依赖: Set.mem_compl_iff, mem_compl_iff, restrict_ne_zero_aux, weights_restrict
-/
lemma convexCombPair_restrict_restrict_compl (w : StdSimplex K I) (s : Set I) (hs hs')
    [DecidablePred (· in s)] :
    convexCombPair
      ((w.weights.filter (· in s)).sum fun _x k => k)
      ((w.weights.filter (· ∉ s)).sum fun _x k => k)
      (by exact restrict_nonneg_aux) (by exact restrict_nonneg_aux) (by simp)
      (w.restrict s hs) (w.restrict sᶜ hs') = w := by
  ext : 1
  simp only [Set.mem_compl_iff] at hs'
  simp [weights_restrict, smul_inv_smul₀, restrict_ne_zero_aux, hs, hs']

end StdSimplex

/--
lemma `sConvexComb_sConvexComb` / 引理 `sConvexComb_sConvexComb`

English:
lemma sConvexComb_sConvexComb
  given: (f : StdSimplex R (StdSimplex R M))
  proof: (ConvexSpace.assoc f).symm

中文:
引理 sConvexComb_sConvexComb
  条件: (f : 标准单纯形 R (标准单纯形 R M))
  证明: (ConvexSpace.assoc f).symm

Depends on / 依赖: ConvexSpace, ConvexSpace.assoc
-/
lemma sConvexComb_sConvexComb (f : StdSimplex R (StdSimplex R M)) :
    f.sConvexComb.sConvexComb = (f.map sConvexComb).sConvexComb :=
  (ConvexSpace.assoc f).symm

/--
lemma `sConvexComb_convexCombPair` / 引理 `sConvexComb_convexCombPair`

English:
lemma sConvexComb_convexCombPair
  given: (s t : R) (hs ht hst) (w w' : StdSimplex R M)
  proof: by
  simp [convexCombPair, sConvexComb_sConvexComb]

中文:
引理 sConvexComb_convexCombPair
  条件: (s t : R) (hs ht hst) (w w' : 标准单纯形 R M)
  证明: by
  simp [convexCombPair, sConvexComb_sConvexComb]

Depends on / 依赖: convexCombPair, sConvexComb_sConvexComb
-/
lemma sConvexComb_convexCombPair (s t : R) (hs ht hst) (w w' : StdSimplex R M) :
    (convexCombPair s t hs ht hst w w').sConvexComb =
      convexCombPair s t hs ht hst w.sConvexComb w'.sConvexComb := by
  simp [convexCombPair, sConvexComb_sConvexComb]

/--
Definition of `ConvexSpace.mk` / `ConvexSpace.mk` 的定义

English:
abbreviation ConvexSpace.mk
  signature: {M : Type*} (sConvexComb : StdSimplex R M -> M)
  body: ⟨sConvexComb, single, assoc⟩

中文:
缩写 凸空间.mk
  签名: {M : 类型} (sConvexComb : 标准单纯形 R M -> M)
  定义体: ⟨sConvexComb, single, assoc⟩

Depends on / 依赖: sConvexComb, single
-/
abbrev ConvexSpace.mk {M : Type*} (sConvexComb : StdSimplex R M -> M)
    (single : forall x : M, sConvexComb (.single x) = x)
    (assoc : forall f : StdSimplex R (StdSimplex R M),
      sConvexComb (f.map sConvexComb) = sConvexComb f.sConvexComb) : ConvexSpace R M :=
  ⟨sConvexComb, single, assoc⟩

variable (R) in
/-- A map between convex spaces is affine if it preserves convex combinations.

TODO: Show that this generalises affine maps between affine spaces, see `AffineMap`. -/
@[fun_prop]
/--
Definition of `IsAffineMap` / `IsAffineMap` 的定义

English:
structure IsAffineMap
  parameters: (f : M -> N)
  axioms and operations (1):
    - map_sConvexComb((s : StdSimplex R M)) : f s.sConvexComb = (s.map f).sConvexComb

中文:
结构 是仿射映射
  参数: (f : M -> N)
  公理与运算 (1 个):
    - map_sConvexComb((s : 标准单纯形 R M)) : f s.sConvexComb = (s.map f).sConvexComb
-/
structure IsAffineMap (f : M -> N) : Prop where
  map_sConvexComb (s : StdSimplex R M) : f s.sConvexComb = (s.map f).sConvexComb

@[fun_prop]
/--
lemma `IsAffineMap.id` / 引理 `IsAffineMap.id`

English:
lemma IsAffineMap.id
  statement: IsAffineMap R (id : M -> M) where
  proof: by simp

@[fun_prop]

中文:
引理 是仿射映射.id
  结论: 是仿射映射 R (id : M -> M) where
  证明: by simp

@[fun_prop]
-/
protected lemma IsAffineMap.id : IsAffineMap R (id : M -> M) where
  map_sConvexComb s := by simp

@[fun_prop]
/--
lemma `IsAffineMap.comp` / 引理 `IsAffineMap.comp`

English:
lemma IsAffineMap.comp
  given: {g : N -> P} (hg : IsAffineMap R g) {f : M -> N} (hf : IsAffineMap R f)
  proof: by
    simp [StdSimplex.map_comp, hf.map_sConvexComb, hg.map_sConvexComb]

@[fun_prop]

中文:
引理 是仿射映射.comp
  条件: {g : N -> P} (hg : 是仿射映射 R g) {f : M -> N} (hf : 是仿射映射 R f)
  证明: by
    simp [StdSimplex.map_comp, hf.map_sConvexComb, hg.map_sConvexComb]

@[fun_prop]

Depends on / 依赖: StdSimplex, StdSimplex.map_comp, hf.map_sConvexComb, hg.map_sConvexComb, map_comp, map_sConvexComb
-/
lemma IsAffineMap.comp {g : N -> P} (hg : IsAffineMap R g) {f : M -> N} (hf : IsAffineMap R f) :
    IsAffineMap R (g ∘ f) where
  map_sConvexComb s := by
    simp [StdSimplex.map_comp, hf.map_sConvexComb, hg.map_sConvexComb]

@[fun_prop]
/--
lemma `IsAffineMap.const` / 引理 `IsAffineMap.const`

English:
lemma IsAffineMap.const
  given: (x : N)
  proof: by simp

中文:
引理 是仿射映射.const
  条件: (x : N)
  证明: by simp
-/
lemma IsAffineMap.const (x : N) :
    IsAffineMap R (fun (_ : M) => x) where
  map_sConvexComb _ := by simp

variable (R) in
@[fun_prop]
/--
lemma `StdSimplex.isAffineMap_map` / 引理 `StdSimplex.isAffineMap_map`

English:
lemma StdSimplex.isAffineMap_map
  given: (f : I -> J)
  statement: IsAffineMap R (StdSimplex.map (R := R) f)
  proof: ⟨(map_sConvexComb · f)⟩

中文:
引理 标准单纯形.isAffineMap_map
  条件: (f : I -> J)
  结论: 是仿射映射 R (标准单纯形.map (R := R) f)
  证明: ⟨(map_sConvexComb · f)⟩
-/
lemma StdSimplex.isAffineMap_map (f : I -> J) : IsAffineMap R (StdSimplex.map (R := R) f) :=
  ⟨(map_sConvexComb · f)⟩

section iConvexComb

/--
lemma `sConvexComb_map` / 引理 `sConvexComb_map`

English:
lemma sConvexComb_map
  given: (w : StdSimplex R I) (f : I -> M)
  proof: rfl

中文:
引理 sConvexComb_map
  条件: (w : 标准单纯形 R I) (f : I -> M)
  证明: rfl
-/
lemma sConvexComb_map (w : StdSimplex R I) (f : I -> M) :
    sConvexComb (w.map f) = iConvexComb w f := rfl

/--
lemma `iConvexComb_const` / 引理 `iConvexComb_const`

English:
lemma iConvexComb_const
  given: (s : StdSimplex R I) (m : M)
  proof: by simp [iConvexComb]

中文:
引理 iConvexComb_const
  条件: (s : 标准单纯形 R I) (m : M)
  证明: by simp [iConvexComb]
-/
@[simp] lemma iConvexComb_const (s : StdSimplex R I) (m : M) :
    s.iConvexComb (fun _ => m) = m := by simp [iConvexComb]

/--
lemma `iConvexComb_single` / 引理 `iConvexComb_single`

English:
lemma iConvexComb_single
  given: (i : I) (f : I -> M)
  proof: by simp [iConvexComb]

中文:
引理 iConvexComb_single
  条件: (i : I) (f : I -> M)
  证明: by simp [iConvexComb]
-/
@[simp] lemma iConvexComb_single (i : I) (f : I -> M) :
    (single (R := R) i).iConvexComb f = f i := by simp [iConvexComb]

/--
lemma `iConvexComb_id` / 引理 `iConvexComb_id`

English:
lemma iConvexComb_id
  given: (w : StdSimplex R M)
  statement: w.iConvexComb id = w.sConvexComb
  proof: by
  simp [iConvexComb]

中文:
引理 iConvexComb_id
  条件: (w : 标准单纯形 R M)
  结论: w.iConvexComb id = w.sConvexComb
  证明: by
  simp [iConvexComb]

Depends on / 依赖: iConvexComb
-/
lemma iConvexComb_id (w : StdSimplex R M) : w.iConvexComb id = w.sConvexComb := by
  simp [iConvexComb]

/--
lemma `iConvexComb_id'` / 引理 `iConvexComb_id'`

English:
lemma iConvexComb_id'
  given: (w : StdSimplex R M)
  proof: iConvexComb_id _

中文:
引理 iConvexComb_id'
  条件: (w : 标准单纯形 R M)
  证明: iConvexComb_id _
-/
@[simp] lemma iConvexComb_id' (w : StdSimplex R M) :
    w.iConvexComb (fun x => x) = w.sConvexComb := iConvexComb_id _

/--
lemma `iConvexComb_map` / 引理 `iConvexComb_map`

English:
lemma iConvexComb_map
  given: (s : StdSimplex R I) (f : I -> J) (g : J -> M)
  proof: by
  simp only [iConvexComb, map_map]

中文:
引理 iConvexComb_map
  条件: (s : 标准单纯形 R I) (f : I -> J) (g : J -> M)
  证明: by
  simp only [iConvexComb, map_map]
-/
@[simp] lemma iConvexComb_map (s : StdSimplex R I) (f : I -> J) (g : J -> M) :
    (s.map f).iConvexComb g = s.iConvexComb (fun i => g (f i)) := by
  simp only [iConvexComb, map_map]

/--
lemma `iConvexComb_congr` / 引理 `iConvexComb_congr`

English:
lemma iConvexComb_congr
  statement: {w : StdSimplex R I} {f g : I -> M}
  proof: by
  refine congr(sConvexComb $(?_))
  ext i
  simp only [weights_map]
  -- TODO: This should just be `congr! 2 with i hi`.
  congr 1
  refine Finsupp.mapDomain_congr fun i hi => ?_
  exact hfg i (by simpa using hi)

中文:
引理 iConvexComb_congr
  结论: {w : 标准单纯形 R I} {f g : I -> M}
  证明: by
  refine congr(sConvexComb $(?_))
  ext i
  simp only [weights_map]
  -- TODO: This should just be `congr! 2 with i hi`.
  congr 1
  refine Finsupp.mapDomain_congr fun i hi => ?_
  exact hfg i (by simpa using hi)
-/
@[congr] lemma iConvexComb_congr {w : StdSimplex R I} {f g : I -> M}
    (hfg : forall i, w.weights i != 0 -> f i = g i) :
    w.iConvexComb f = w.iConvexComb g := by
  refine congr(sConvexComb $(?_))
  ext i
  simp only [weights_map]
  -- TODO: This should just be `congr! 2 with i hi`.
  congr 1
  refine Finsupp.mapDomain_congr fun i hi => ?_
  exact hfg i (by simpa using hi)

/--
lemma `iConvexComb_reindex` / 引理 `iConvexComb_reindex`

English:
lemma iConvexComb_reindex
  given: (s : StdSimplex R I) (f : I ≃ J) (g : I -> M)
  proof: by
  simp [iConvexComb_map]

中文:
引理 iConvexComb_reindex
  条件: (s : 标准单纯形 R I) (f : I ≃ J) (g : I -> M)
  证明: by
  simp [iConvexComb_map]

Depends on / 依赖: iConvexComb_map
-/
lemma iConvexComb_reindex (s : StdSimplex R I) (f : I ≃ J) (g : I -> M) :
    s.iConvexComb g = (s.map f).iConvexComb (g ∘ f.symm) := by
  simp [iConvexComb_map]

/--
lemma `iConvexComb_assoc''` / 引理 `iConvexComb_assoc''`

English:
lemma iConvexComb_assoc''
  proof: by
  simp only [iConvexComb]
  rw [← map_map]; rw [← sConvexComb_sConvexComb]
  congr 1
  simp [map_sConvexComb, map_map, Sigma.uncurry]

中文:
引理 iConvexComb_assoc''
  证明: by
  simp only [iConvexComb]
  rw [← map_map]; rw [← sConvexComb_sConvexComb]
  congr 1
  simp [map_sConvexComb, map_map, Sigma.uncurry]

Depends on / 依赖: Sigma.uncurry, iConvexComb, map_map, map_sConvexComb, sConvexComb_sConvexComb, uncurry
-/
lemma iConvexComb_assoc''
    {J : I -> Type*} (s : StdSimplex R I) (f : Π i, StdSimplex R (J i)) (g : Π i, J i -> M) :
    s.iConvexComb (fun i => (f i).iConvexComb (g i)) =
      (s.iConvexComb fun i => (f i).map (⟨i, ·⟩)).iConvexComb (Sigma.uncurry g) := by
  simp only [iConvexComb]
  rw [← map_map]; rw [← sConvexComb_sConvexComb]
  congr 1
  simp [map_sConvexComb, map_map, Sigma.uncurry]

/--
lemma `iConvexComb_assoc'` / 引理 `iConvexComb_assoc'`

English:
lemma iConvexComb_assoc'
  statement: {J : Type*} (s : StdSimplex R I) (f : I -> StdSimplex R J)
  proof: by
  simp only [iConvexComb]
  rw [← map_map]; rw [← sConvexComb_sConvexComb]
  congr 1
  simp [map_sConvexComb, map_map, Function.uncurry]

中文:
引理 iConvexComb_assoc'
  结论: {J : 类型} (s : 标准单纯形 R I) (f : I -> 标准单纯形 R J)
  证明: by
  simp only [iConvexComb]
  rw [← map_map]; rw [← sConvexComb_sConvexComb]
  congr 1
  simp [map_sConvexComb, map_map, Function.uncurry]

Depends on / 依赖: Function, Function.uncurry, iConvexComb, map_map, map_sConvexComb, sConvexComb_sConvexComb, uncurry
-/
lemma iConvexComb_assoc' {J : Type*} (s : StdSimplex R I) (f : I -> StdSimplex R J)
    (g : I -> J -> M) :
    s.iConvexComb (fun i => (f i).iConvexComb (g i)) =
      (s.iConvexComb fun i => (f i).map (⟨i, ·⟩)).iConvexComb g.uncurry := by
  simp only [iConvexComb]
  rw [← map_map]; rw [← sConvexComb_sConvexComb]
  congr 1
  simp [map_sConvexComb, map_map, Function.uncurry]

/--
lemma `iConvexComb_assoc` / 引理 `iConvexComb_assoc`

English:
lemma iConvexComb_assoc
  statement: {J : Type*} (s : StdSimplex R I) (f : I -> StdSimplex R J)
  proof: by
  simp only [iConvexComb]
  rw [← map_map]; rw [← sConvexComb_sConvexComb]
  simp [map_sConvexComb, map_map]

中文:
引理 iConvexComb_assoc
  结论: {J : 类型} (s : 标准单纯形 R I) (f : I -> 标准单纯形 R J)
  证明: by
  simp only [iConvexComb]
  rw [← map_map]; rw [← sConvexComb_sConvexComb]
  simp [map_sConvexComb, map_map]

Depends on / 依赖: iConvexComb, map_map, map_sConvexComb, sConvexComb_sConvexComb
-/
lemma iConvexComb_assoc {J : Type*} (s : StdSimplex R I) (f : I -> StdSimplex R J)
    (g : J -> M) :
    s.iConvexComb (fun i => (f i).iConvexComb g) = (s.iConvexComb f).iConvexComb g := by
  simp only [iConvexComb]
  rw [← map_map]; rw [← sConvexComb_sConvexComb]
  simp [map_sConvexComb, map_map]

variable {R M I J : Type*} [PartialOrder R] [CommSemiring R] [IsStrictOrderedRing R]
  [ConvexSpace R M] in
/--
lemma `iConvexComb_comm` / 引理 `iConvexComb_comm`

English:
lemma iConvexComb_comm
  statement: (f : StdSimplex R I) (g : StdSimplex R J)
  proof: by
  rw [iConvexComb_assoc']; rw [iConvexComb_assoc']; rw [iConvexComb_reindex _ (.prodComm ..)]
  congr
  suffices (f.map fun x => g.map (Prod.mk · x)).sConvexComb =
      (g.map (f.map ∘ Prod.mk)).sConvexComb by
    simpa [iConvexComb, map_sConvexComb, map_map, Function.comp_def]
  ext1
  simp [ma

中文:
引理 iConvexComb_comm
  结论: (f : 标准单纯形 R I) (g : 标准单纯形 R J)
  证明: by
  rw [iConvexComb_assoc']; rw [iConvexComb_assoc']; rw [iConvexComb_reindex _ (.prodComm ..)]
  congr
  suffices (f.map fun x => g.map (Prod.mk · x)).sConvexComb =
      (g.map (f.map ∘ Prod.mk)).sConvexComb by
    simpa [iConvexComb, map_sConvexComb, map_map, Function.comp_def]
  ext1
  simp [ma

Depends on / 依赖: Function, Function.comp_def, Prod.mk, add_smul, comp_def, f.map, f.weights, g.map, g.weights, iConvexComb, iConvexComb_assoc, iConvexComb_reindex, mapDomain, map_map, map_sConvexComb, mul_comm, prodComm, sConvexComb, smul_sum, sum_comm
-/
lemma iConvexComb_comm (f : StdSimplex R I) (g : StdSimplex R J)
    (e : I -> J -> M) :
    f.iConvexComb (fun i => g.iConvexComb (e i)) =
      g.iConvexComb fun j => f.iConvexComb fun i => e i j := by
  rw [iConvexComb_assoc']; rw [iConvexComb_assoc']; rw [iConvexComb_reindex _ (.prodComm ..)]
  congr
  suffices (f.map fun x => g.map (Prod.mk · x)).sConvexComb =
      (g.map (f.map ∘ Prod.mk)).sConvexComb by
    simpa [iConvexComb, map_sConvexComb, map_map, Function.comp_def]
  ext1
  simp [mapDomain, sum_sum_index, add_smul, smul_sum, mul_comm, sum_comm f.weights g.weights]

/--
lemma `IsAffineMap.map_iConvexComb` / 引理 `IsAffineMap.map_iConvexComb`

English:
lemma IsAffineMap.map_iConvexComb
  statement: {f : M -> N} (hf : IsAffineMap R f)
  proof: by
  simp [iConvexComb, hf.map_sConvexComb, map_comp]

中文:
引理 是仿射映射.map_iConvexComb
  结论: {f : M -> N} (hf : 是仿射映射 R f)
  证明: by
  simp [iConvexComb, hf.map_sConvexComb, map_comp]

Depends on / 依赖: hf.map_sConvexComb, iConvexComb, map_comp, map_sConvexComb
-/
lemma IsAffineMap.map_iConvexComb {f : M -> N} (hf : IsAffineMap R f)
    (s : StdSimplex R I) (g : I -> M) : f (s.iConvexComb g) = s.iConvexComb (f ∘ g) := by
  simp [iConvexComb, hf.map_sConvexComb, map_comp]

/--
lemma `map_iConvexComb` / 引理 `map_iConvexComb`

English:
lemma map_iConvexComb
  statement: {f : J -> K}
  proof: (isAffineMap_map R f).map_iConvexComb s g

中文:
引理 map_iConvexComb
  结论: {f : J -> K}
  证明: (isAffineMap_map R f).map_iConvexComb s g

Depends on / 依赖: isAffineMap_map, map_iConvexComb
-/
lemma map_iConvexComb {f : J -> K}
    (s : StdSimplex R I) (g : I -> StdSimplex R J) :
    (s.iConvexComb g).map f = s.iConvexComb (map f ∘ g) :=
  (isAffineMap_map R f).map_iConvexComb s g

end iConvexComb

variable {s t : R} (hs : 0 <= s) (ht : 0 <= t) (h : s + t = 1)
variable {s' t' : R} (hs' : 0 <= s') (ht' : 0 <= t') (h' : s' + t' = 1)
variable {s'' t'' : R} (hs'' : 0 <= s'') (ht'' : 0 <= t'') (h'' : s'' + t'' = 1)

/--
lemma `convexCombPair_def` / 引理 `convexCombPair_def`

English:
lemma convexCombPair_def
  given: (p q : M)
  proof: by
  simp [StdSimplex.iConvexComb, convexCombPair]

中文:
引理 convexCombPair_def
  条件: (p q : M)
  证明: by
  simp [StdSimplex.iConvexComb, convexCombPair]

Depends on / 依赖: StdSimplex, StdSimplex.iConvexComb, convexCombPair, iConvexComb
-/
lemma convexCombPair_def (p q : M) :
    convexCombPair s t hs ht h p q = (StdSimplex.duple 0 1 hs ht h).iConvexComb ![p, q] := by
  simp [StdSimplex.iConvexComb, convexCombPair]

/-- A binary convex combination with weight 0 on the first point returns the second point. -/
@[simp]
/--
theorem `convexCombPair_zero` / 定理 `convexCombPair_zero`

English:
theorem convexCombPair_zero
  given: {x y : M}
  proof: by
  simp [convexCombPair, StdSimplex.duple, StdSimplex.mk_single]

@[deprecated (since := "2026-05-15")] alias convexComboPair_zero := convexCombPair_zero

中文:
定理 convexCombPair_zero
  条件: {x y : M}
  证明: by
  simp [convexCombPair, StdSimplex.duple, StdSimplex.mk_single]

@[deprecated (since := "2026-05-15")] alias convexComboPair_zero := convexCombPair_zero

Depends on / 依赖: StdSimplex, StdSimplex.duple, StdSimplex.mk_single, convexCombPair, mk_single
-/
theorem convexCombPair_zero {x y : M} :
    convexCombPair (0 : R) 1 (by simp) (by simp) (by simp) x y = y := by
  simp [convexCombPair, StdSimplex.duple, StdSimplex.mk_single]

@[deprecated (since := "2026-05-15")] alias convexComboPair_zero := convexCombPair_zero

/-- A binary convex combination with weight 1 on the first point returns the first point. -/
@[simp]
/--
theorem `convexCombPair_one` / 定理 `convexCombPair_one`

English:
theorem convexCombPair_one
  given: {x y : M}
  proof: by
  simp [convexCombPair, StdSimplex.duple, StdSimplex.mk_single]

@[deprecated (since := "2026-05-15")] alias convexComboPair_one := convexCombPair_one

中文:
定理 convexCombPair_one
  条件: {x y : M}
  证明: by
  simp [convexCombPair, StdSimplex.duple, StdSimplex.mk_single]

@[deprecated (since := "2026-05-15")] alias convexComboPair_one := convexCombPair_one

Depends on / 依赖: StdSimplex, StdSimplex.duple, StdSimplex.mk_single, convexCombPair, mk_single
-/
theorem convexCombPair_one {x y : M} :
    convexCombPair (1 : R) 0 (by simp) (by simp) (by simp) x y = x := by
  simp [convexCombPair, StdSimplex.duple, StdSimplex.mk_single]

@[deprecated (since := "2026-05-15")] alias convexComboPair_one := convexCombPair_one

/-- A convex combination of a point with itself is that point. -/
@[simp]
/--
theorem `convexCombPair_same` / 定理 `convexCombPair_same`

English:
theorem convexCombPair_same
  given: {x : M}
  proof: by
  unfold convexCombPair
  convert sConvexComb_single x
  simp only [StdSimplex.duple, StdSimplex.single, ← single_add, h]

@[deprecated (since := "2026-05-15")] alias convexComboPair_symm := convexCombPair_same

中文:
定理 convexCombPair_same
  条件: {x : M}
  证明: by
  unfold convexCombPair
  convert sConvexComb_single x
  simp only [StdSimplex.duple, StdSimplex.single, ← single_add, h]

@[deprecated (since := "2026-05-15")] alias convexComboPair_symm := convexCombPair_same

Depends on / 依赖: StdSimplex, StdSimplex.duple, StdSimplex.single, convert, convexCombPair, sConvexComb_single, single, single_add
-/
theorem convexCombPair_same {x : M} :
    convexCombPair s t hs ht h x x = x := by
  unfold convexCombPair
  convert sConvexComb_single x
  simp only [StdSimplex.duple, StdSimplex.single, ← single_add, h]

@[deprecated (since := "2026-05-15")] alias convexComboPair_symm := convexCombPair_same

/--
theorem `convexCombPair_symm` / 定理 `convexCombPair_symm`

English:
theorem convexCombPair_symm
  given: {x y : M}
  proof: by
  unfold convexCombPair
  congr 1
  ext1
  simp [StdSimplex.duple, add_comm]

中文:
定理 convexCombPair_symm
  条件: {x y : M}
  证明: by
  unfold convexCombPair
  congr 1
  ext1
  simp [StdSimplex.duple, add_comm]

Depends on / 依赖: StdSimplex, StdSimplex.duple, add_comm, convexCombPair
-/
theorem convexCombPair_symm {x y : M} :
    convexCombPair s t hs ht h x y = convexCombPair t s ht hs ((add_comm _ _).trans h) y x := by
  unfold convexCombPair
  congr 1
  ext1
  simp [StdSimplex.duple, add_comm]

/--
lemma `IsAffineMap.map_convexCombPair` / 引理 `IsAffineMap.map_convexCombPair`

English:
lemma IsAffineMap.map_convexCombPair
  statement: {f : M -> N} (hf : IsAffineMap R f)
  proof: by
  simp [hf.map_sConvexComb, convexCombPair]

中文:
引理 是仿射映射.map_convexCombPair
  结论: {f : M -> N} (hf : 是仿射映射 R f)
  证明: by
  simp [hf.map_sConvexComb, convexCombPair]

Depends on / 依赖: convexCombPair, hf.map_sConvexComb, map_sConvexComb
-/
lemma IsAffineMap.map_convexCombPair {f : M -> N} (hf : IsAffineMap R f)
    {s t : R} (hs : 0 <= s) (ht : 0 <= t) (h : s + t = 1) (x y : M) :
    f (convexCombPair s t hs ht h x y) = convexCombPair s t hs ht h (f x) (f y) := by
  simp [hf.map_sConvexComb, convexCombPair]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `convexCombPair_iConvexComb_iConvexComb` / 引理 `convexCombPair_iConvexComb_iConvexComb`

English:
lemma convexCombPair_iConvexComb_iConvexComb
  statement: {J₁ : Type u₁} {J₂ : Type u₂}
  proof: by
  have := iConvexComb_assoc'' (I := Fin 2) (.duple 0 1 hs ht h)
    (J := ![ULift.{max u₁ u₂} J₁, ULift.{max u₁ u₂} J₂])
    (M := M) (Fin.cons (g₁.map ULift.up) (Fin.cons (g₂.map ULift.up) nofun))
    (Fin.cons (m₁ ∘ ULift.down) (Fin.cons (m₂ ∘ ULift.down) nofun))
  simp [iConvexComb, map_sConve

中文:
引理 convexCombPair_iConvexComb_iConvexComb
  结论: {J₁ : 类型u₁} {J₂ : 类型u₂}
  证明: by
  have := iConvexComb_assoc'' (I := Fin 2) (.duple 0 1 hs ht h)
    (J := ![ULift.{max u₁ u₂} J₁, ULift.{max u₁ u₂} J₂])
    (M := M) (Fin.cons (g₁.map ULift.up) (Fin.cons (g₂.map ULift.up) nofun))
    (Fin.cons (m₁ ∘ ULift.down) (Fin.cons (m₂ ∘ ULift.down) nofun))
  simp [iConvexComb, map_sConve

Depends on / 依赖: Fin.cons, Sigma.uncurry, ULift.down, ULift.up, convexCombPair, convexCombPair_def, iConvexComb, iConvexComb_assoc, map_map, map_sConvexComb, uncurry
-/
lemma convexCombPair_iConvexComb_iConvexComb {J₁ : Type u₁} {J₂ : Type u₂}
    (g₁ : StdSimplex R J₁) (g₂ : StdSimplex R J₂)
    (m₁ : J₁ -> M) (m₂ : J₂ -> M) :
    convexCombPair s t hs ht h (g₁.iConvexComb m₁) (g₂.iConvexComb m₂) =
      (convexCombPair s t hs ht h (g₁.map m₁) (g₂.map m₂)).sConvexComb := by
  have := iConvexComb_assoc'' (I := Fin 2) (.duple 0 1 hs ht h)
    (J := ![ULift.{max u₁ u₂} J₁, ULift.{max u₁ u₂} J₂])
    (M := M) (Fin.cons (g₁.map ULift.up) (Fin.cons (g₂.map ULift.up) nofun))
    (Fin.cons (m₁ ∘ ULift.down) (Fin.cons (m₂ ∘ ULift.down) nofun))
  simp [iConvexComb, map_sConvexComb, map_map, Sigma.uncurry] at this
  simpa [convexCombPair, ← convexCombPair_def]

/--
lemma `iConvexComb_convexCombPair` / 引理 `iConvexComb_convexCombPair`

English:
lemma iConvexComb_convexCombPair
  proof: by
  have := iConvexComb_assoc' (I := I) (J := Fin 2) (R := R) (M := M) f
    (fun i => .duple 0 1 (hs i) (ht i) (h i)) (fun i => ![m₁ i, m₂ i])
  simp [iConvexComb, map_sConvexComb, map_map] at this
  simp only [← convexCombPair.eq_def] at this
  simp only [← iConvexComb.eq_def] at this
  simpa [co

中文:
引理 iConvexComb_convexCombPair
  证明: by
  have := iConvexComb_assoc' (I := I) (J := Fin 2) (R := R) (M := M) f
    (fun i => .duple 0 1 (hs i) (ht i) (h i)) (fun i => ![m₁ i, m₂ i])
  simp [iConvexComb, map_sConvexComb, map_map] at this
  simp only [← convexCombPair.eq_def] at this
  simp only [← iConvexComb.eq_def] at this
  simpa [co

Depends on / 依赖: convexCombPair, convexCombPair.eq_def, convexCombPair_def, eq_def, iConvexComb, iConvexComb.eq_def, iConvexComb_assoc, map_map, map_sConvexComb
-/
lemma iConvexComb_convexCombPair
    (s t : I -> R) (hs : forall i, 0 <= s i) (ht : forall i, 0 <= t i) (h : forall i, s i + t i = 1)
    (f : StdSimplex R I) (m₁ m₂ : I -> M) :
    f.iConvexComb (fun i => convexCombPair (s i) (t i) (hs i) (ht i) (h i) (m₁ i) (m₂ i)) =
    (f.iConvexComb fun i => duple (m₁ i) (m₂ i) (hs i) (ht i) (h i)).sConvexComb := by
  have := iConvexComb_assoc' (I := I) (J := Fin 2) (R := R) (M := M) f
    (fun i => .duple 0 1 (hs i) (ht i) (h i)) (fun i => ![m₁ i, m₂ i])
  simp [iConvexComb, map_sConvexComb, map_map] at this
  simp only [← convexCombPair.eq_def] at this
  simp only [← iConvexComb.eq_def] at this
  simpa [convexCombPair, ← convexCombPair_def]

/--
lemma `convexCombPair_iConvexComb_left` / 引理 `convexCombPair_iConvexComb_left`

English:
lemma convexCombPair_iConvexComb_left
  given: (g : StdSimplex R J) (e : J -> M) (m : M)
  proof: by
  simpa using convexCombPair_iConvexComb_iConvexComb hs ht h g g e (fun _ => m)

中文:
引理 convexCombPair_iConvexComb_left
  条件: (g : 标准单纯形 R J) (e : J -> M) (m : M)
  证明: by
  simpa using convexCombPair_iConvexComb_iConvexComb hs ht h g g e (fun _ => m)

Depends on / 依赖: convexCombPair_iConvexComb_iConvexComb
-/
lemma convexCombPair_iConvexComb_left (g : StdSimplex R J) (e : J -> M) (m : M) :
    convexCombPair s t hs ht h (g.iConvexComb e) m =
      (convexCombPair s t hs ht h (g.map e) (single m)).sConvexComb := by
  simpa using convexCombPair_iConvexComb_iConvexComb hs ht h g g e (fun _ => m)

/--
lemma `convexCombPair_iConvexComb_right` / 引理 `convexCombPair_iConvexComb_right`

English:
lemma convexCombPair_iConvexComb_right
  given: (m : M) (g : StdSimplex R J) (e : J -> M)
  proof: by
  simpa using convexCombPair_iConvexComb_iConvexComb hs ht h g g (fun _ => m) e

中文:
引理 convexCombPair_iConvexComb_right
  条件: (m : M) (g : 标准单纯形 R J) (e : J -> M)
  证明: by
  simpa using convexCombPair_iConvexComb_iConvexComb hs ht h g g (fun _ => m) e

Depends on / 依赖: convexCombPair_iConvexComb_iConvexComb
-/
lemma convexCombPair_iConvexComb_right (m : M) (g : StdSimplex R J) (e : J -> M) :
    convexCombPair s t hs ht h m (g.iConvexComb e) =
      (convexCombPair s t hs ht h (.single m) (g.map e)).sConvexComb := by
  simpa using convexCombPair_iConvexComb_iConvexComb hs ht h g g (fun _ => m) e

/--
lemma `convexCombPair_convexCombPair_left_eq_sConvexComb` / 引理 `convexCombPair_convexCombPair_left_eq_sConvexComb`

English:
lemma convexCombPair_convexCombPair_left_eq_sConvexComb
  given: (m₁ m₂ m₃ : M)
  proof: by
  simpa using! convexCombPair_iConvexComb_left hs ht h (.duple m₁ m₂ hs' ht' h') id m₃

中文:
引理 convexCombPair_convexCombPair_left_eq_sConvexComb
  条件: (m₁ m₂ m₃ : M)
  证明: by
  simpa using! convexCombPair_iConvexComb_left hs ht h (.duple m₁ m₂ hs' ht' h') id m₃

Depends on / 依赖: convexCombPair_iConvexComb_left
-/
lemma convexCombPair_convexCombPair_left_eq_sConvexComb (m₁ m₂ m₃ : M) :
    convexCombPair s t hs ht h (convexCombPair s' t' hs' ht' h' m₁ m₂) m₃ =
      (convexCombPair s t hs ht h (duple m₁ m₂ hs' ht' h') (single m₃)).sConvexComb := by
  simpa using! convexCombPair_iConvexComb_left hs ht h (.duple m₁ m₂ hs' ht' h') id m₃

/--
lemma `convexCombPair_convexCombPair_right_eq_sConvexComb` / 引理 `convexCombPair_convexCombPair_right_eq_sConvexComb`

English:
lemma convexCombPair_convexCombPair_right_eq_sConvexComb
  given: (m₁ m₂ m₃ : M)
  proof: by
  simpa using! convexCombPair_iConvexComb_right hs ht h m₁ (.duple m₂ m₃ hs' ht' h') id

中文:
引理 convexCombPair_convexCombPair_right_eq_sConvexComb
  条件: (m₁ m₂ m₃ : M)
  证明: by
  simpa using! convexCombPair_iConvexComb_right hs ht h m₁ (.duple m₂ m₃ hs' ht' h') id

Depends on / 依赖: convexCombPair_iConvexComb_right
-/
lemma convexCombPair_convexCombPair_right_eq_sConvexComb (m₁ m₂ m₃ : M) :
    convexCombPair s t hs ht h m₁ (convexCombPair s' t' hs' ht' h' m₂ m₃) =
      (convexCombPair s t hs ht h (.single m₁) (duple m₂ m₃ hs' ht' h')).sConvexComb := by
  simpa using! convexCombPair_iConvexComb_right hs ht h m₁ (.duple m₂ m₃ hs' ht' h') id

/--
lemma `convexCombPair_convexCombPair_assoc_left` / 引理 `convexCombPair_convexCombPair_assoc_left`

English:
lemma convexCombPair_convexCombPair_assoc_left
  given: (H : t * s'' = s * t' * t'') (m₁ m₂ m₃ : M)
  proof: by
  classical
  rw [convexCombPair_convexCombPair_left_eq_sConvexComb]; rw [convexCombPair_convexCombPair_right_eq_sConvexComb]
  congr 1
  ext1
  have : s * (t' * t'') + t * t'' = t := by rw [← mul_assoc, ← H, ← mul_add, h'', mul_one]
  simp [convexCombPair, sum_add_index, add_smul, ← single_add, 

中文:
引理 convexCombPair_convexCombPair_assoc_left
  条件: (H : t * s'' = s * t' * t'') (m₁ m₂ m₃ : M)
  证明: by
  classical
  rw [convexCombPair_convexCombPair_left_eq_sConvexComb]; rw [convexCombPair_convexCombPair_right_eq_sConvexComb]
  congr 1
  ext1
  have : s * (t' * t'') + t * t'' = t := by rw [← mul_assoc, ← H, ← mul_add, h'', mul_one]
  simp [convexCombPair, sum_add_index, add_smul, ← single_add, 

Depends on / 依赖: add_assoc, add_smul, classical, convexCombPair, convexCombPair_convexCombPair_left_eq_sConvexComb, convexCombPair_convexCombPair_right_eq_sConvexComb, mul_add, mul_assoc, mul_one, single_add, sum_add_index
-/
lemma convexCombPair_convexCombPair_assoc_left (H : t * s'' = s * t' * t'') (m₁ m₂ m₃ : M) :
    convexCombPair s t hs ht h (convexCombPair s' t' hs' ht' h' m₁ m₂) m₃ =
      convexCombPair (s * s') (s * t' + t) (by positivity) (by positivity)
        (by rw [← add_assoc, ← mul_add, h', mul_one, h]) m₁
        (convexCombPair s'' t'' hs'' ht'' h'' m₂ m₃) := by
  classical
  rw [convexCombPair_convexCombPair_left_eq_sConvexComb]; rw [convexCombPair_convexCombPair_right_eq_sConvexComb]
  congr 1
  ext1
  have : s * (t' * t'') + t * t'' = t := by rw [← mul_assoc, ← H, ← mul_add, h'', mul_one]
  simp [convexCombPair, sum_add_index, add_smul, ← single_add, H, mul_assoc, ← mul_add, h'',
    add_assoc, this]

/--
lemma `convexCombPair_convexCombPair_assoc_right` / 引理 `convexCombPair_convexCombPair_assoc_right`

English:
lemma convexCombPair_convexCombPair_assoc_right
  given: (H : s * t'' = t * s' * s'') (m₁ m₂ m₃ : M)
  proof: by
  simp only [add_comm s]
  rw [convexCombPair_symm]; rw [convexCombPair_symm (x := m₂)]; rw [convexCombPair_convexCombPair_assoc_left (hs'' := ht'') (ht'' := hs'')
      (h'' := (add_comm _ _).trans h'') (H := H)]; rw [convexCombPair_symm]; rw [convexCombPair_symm (x := m₂)]

中文:
引理 convexCombPair_convexCombPair_assoc_right
  条件: (H : s * t'' = t * s' * s'') (m₁ m₂ m₃ : M)
  证明: by
  simp only [add_comm s]
  rw [convexCombPair_symm]; rw [convexCombPair_symm (x := m₂)]; rw [convexCombPair_convexCombPair_assoc_left (hs'' := ht'') (ht'' := hs'')
      (h'' := (add_comm _ _).trans h'') (H := H)]; rw [convexCombPair_symm]; rw [convexCombPair_symm (x := m₂)]

Depends on / 依赖: add_comm, convexCombPair_convexCombPair_assoc_left, convexCombPair_symm
-/
lemma convexCombPair_convexCombPair_assoc_right (H : s * t'' = t * s' * s'') (m₁ m₂ m₃ : M) :
    convexCombPair s t hs ht h m₁ (convexCombPair s' t' hs' ht' h' m₂ m₃) =
      convexCombPair (s + t * s') (t * t') (by positivity) (by positivity)
        (by rw [add_assoc, ← mul_add, h', mul_one, h])
        (convexCombPair s'' t'' hs'' ht'' h'' m₁ m₂) m₃ := by
  simp only [add_comm s]
  rw [convexCombPair_symm]; rw [convexCombPair_symm (x := m₂)]; rw [convexCombPair_convexCombPair_assoc_left (hs'' := ht'') (ht'' := hs'')
      (h'' := (add_comm _ _).trans h'') (H := H)]; rw [convexCombPair_symm]; rw [convexCombPair_symm (x := m₂)]

section CommSemiring

variable {R M I : Type*} [PartialOrder R] [CommSemiring R] [IsStrictOrderedRing R]
  [ConvexSpace R M] {s t : R} (hs : 0 <= s) (ht : 0 <= t) (h : s + t = 1)

/--
lemma `iConvexComb_convexCombPair_comm` / 引理 `iConvexComb_convexCombPair_comm`

English:
lemma iConvexComb_convexCombPair_comm
  given: (f : StdSimplex R I) (e₁ e₂ : I -> M)
  proof: by
  simp only [convexCombPair_def]
  convert (iConvexComb_comm (.duple 0 1 hs ht h) f ![e₁, e₂]).symm with i _ j _ j
  · fin_cases j <;> simp
  · fin_cases j <;> simp

中文:
引理 iConvexComb_convexCombPair_comm
  条件: (f : 标准单纯形 R I) (e₁ e₂ : I -> M)
  证明: by
  simp only [convexCombPair_def]
  convert (iConvexComb_comm (.duple 0 1 hs ht h) f ![e₁, e₂]).symm with i _ j _ j
  · fin_cases j <;> simp
  · fin_cases j <;> simp

Depends on / 依赖: convert, convexCombPair_def, fin_cases, iConvexComb_comm
-/
lemma iConvexComb_convexCombPair_comm (f : StdSimplex R I) (e₁ e₂ : I -> M) :
    f.iConvexComb (fun x => convexCombPair s t hs ht h (e₁ x) (e₂ x)) =
      convexCombPair s t hs ht h (f.iConvexComb e₁) (f.iConvexComb e₂) := by
  simp only [convexCombPair_def]
  convert (iConvexComb_comm (.duple 0 1 hs ht h) f ![e₁, e₂]).symm with i _ j _ j
  · fin_cases j <;> simp
  · fin_cases j <;> simp

/--
lemma `iConvexComb_convexCombPair_comm_left` / 引理 `iConvexComb_convexCombPair_comm_left`

English:
lemma iConvexComb_convexCombPair_comm_left
  given: (f : StdSimplex R I) (m : M) (e : I -> M)
  proof: by
  simpa using iConvexComb_convexCombPair_comm hs ht h f e (fun _ => m)

中文:
引理 iConvexComb_convexCombPair_comm_left
  条件: (f : 标准单纯形 R I) (m : M) (e : I -> M)
  证明: by
  simpa using iConvexComb_convexCombPair_comm hs ht h f e (fun _ => m)

Depends on / 依赖: iConvexComb_convexCombPair_comm
-/
lemma iConvexComb_convexCombPair_comm_left (f : StdSimplex R I) (m : M) (e : I -> M) :
    f.iConvexComb (fun x => convexCombPair s t hs ht h (e x) m) =
    convexCombPair s t hs ht h (f.iConvexComb e) m := by
  simpa using iConvexComb_convexCombPair_comm hs ht h f e (fun _ => m)

/--
lemma `iConvexComb_convexCombPair_comm_right` / 引理 `iConvexComb_convexCombPair_comm_right`

English:
lemma iConvexComb_convexCombPair_comm_right
  given: (f : StdSimplex R I) (m : M) (e : I -> M)
  proof: by
  simpa using iConvexComb_convexCombPair_comm hs ht h f (fun _ => m) e

中文:
引理 iConvexComb_convexCombPair_comm_right
  条件: (f : 标准单纯形 R I) (m : M) (e : I -> M)
  证明: by
  simpa using iConvexComb_convexCombPair_comm hs ht h f (fun _ => m) e

Depends on / 依赖: iConvexComb_convexCombPair_comm
-/
lemma iConvexComb_convexCombPair_comm_right (f : StdSimplex R I) (m : M) (e : I -> M) :
    f.iConvexComb (convexCombPair s t hs ht h m <| e ·) =
    convexCombPair s t hs ht h m (f.iConvexComb e) := by
  simpa using iConvexComb_convexCombPair_comm hs ht h f (fun _ => m) e

/--
lemma `isAffineMap_convexCombPair` / 引理 `isAffineMap_convexCombPair`

English:
lemma isAffineMap_convexCombPair
  given: (m : M)
  proof: ⟨fun f => by simpa using! (iConvexComb_convexCombPair_comm_right hs ht h f m id).symm⟩

中文:
引理 isAffineMap_convexCombPair
  条件: (m : M)
  证明: ⟨fun f => by simpa using! (iConvexComb_convexCombPair_comm_right hs ht h f m id).symm⟩

Depends on / 依赖: iConvexComb_convexCombPair_comm_right
-/
lemma isAffineMap_convexCombPair (m : M) :
    IsAffineMap R (convexCombPair s t hs ht h m) :=
  ⟨fun f => by simpa using! (iConvexComb_convexCombPair_comm_right hs ht h f m id).symm⟩

end CommSemiring

end Convexity
