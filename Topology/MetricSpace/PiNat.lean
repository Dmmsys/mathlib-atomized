/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Topology.UnitInterval

/-!
# Topological study of spaces `Π (n : ℕ), E n`

When `E n` are topological spaces, the space `Π (n : ℕ), E n` is naturally a topological space
(with the product topology). When `E n` are uniform spaces, it also inherits a uniform structure.
However, it does not inherit a canonical metric space structure of the `E n`. Nevertheless, one
can put a noncanonical metric space structure (or rather, several of them). This is done in this
file.

## Main definitions and results

One can define a combinatorial distance on `Π (n : ℕ), E n`, as follows:

* `PiNat.cylinder x n` is the set of points `y` with `x i = y i` for `i < n`.
* `PiNat.firstDiff x y` is the first index at which `x i ≠ y i`.
* `PiNat.dist x y` is equal to `(1/2) ^ (firstDiff x y)`. It defines a distance
  on `Π (n : ℕ), E n`, compatible with the topology when the `E n` have the discrete topology.
* `PiNat.metricSpace`: the metric space structure, given by this distance. Not registered as an
  instance. This space is a complete metric space.
* `PiNat.metricSpaceOfDiscreteUniformity`: the same metric space structure, but adjusting the
  uniformity defeqness when the `E n` already have the discrete uniformity. Not registered as an
  instance
* `PiNat.metricSpaceNatNat`: the particular case of `ℕ → ℕ`, not registered as an instance.

These results are used to construct continuous functions on `Π n, E n`:

* `PiNat.exists_retraction_of_isClosed`: given a nonempty closed subset `s` of `Π (n : ℕ), E n`,
  there exists a retraction onto `s`, i.e., a continuous map from the whole space to `s`
  restricting to the identity on `s`.
* `exists_nat_nat_continuous_surjective_of_completeSpace`: given any nonempty complete metric
  space with second-countable topology, there exists a continuous surjection from `ℕ → ℕ` onto
  this space.

One can also put distances on `Π (i : ι), E i` when the spaces `E i` are metric spaces (not discrete
in general), and `ι` is countable.

* `PiCountable.dist` is the distance on `Π i, E i` given by
    `dist x y = ∑' i, min (1/2)^(encode i) (dist (x i) (y i))`.
* `PiCountable.metricSpace` is the corresponding metric space structure, adjusted so that
  the uniformity is definitionally the product uniformity. Not registered as an instance.
* `PiNatEmbed` gives an equivalence between a space and itself in a sequence of spaces
* `Metric.PiNatEmbed.metricSpace` proves that a topological `X` separated by countably many
  continuous functions to metric spaces, can be embedded inside their product.

-/

@[expose] public section

noncomputable section

open Topology TopologicalSpace Set Metric Filter Function

attribute [local simp] pow_le_pow_iff_right₀ one_lt_two inv_le_inv₀ zero_le_two zero_lt_two

variable {E : Nat -> Type*}

namespace PiNat

/-! ### The firstDiff function -/

open scoped Classical in
/-- In a product space `Π n, E n`, then `firstDiff x y` is the first index at which `x` and `y`
differ. If `x = y`, then by convention we set `firstDiff x x = 0`. -/
irreducible_def firstDiff (x y : forall n, E n) : Nat :=
  if h : x != y then Nat.find (ne_iff.1 h) else 0

/--
theorem `apply_firstDiff_ne` / 定理 `apply_firstDiff_ne`

English:
theorem apply_firstDiff_ne
  given: {x y : forall n, E n} (h : x != y)
  proof: by
  rw [firstDiff_def]; rw [dif_pos h]
  classical
  exact Nat.find_spec (ne_iff.1 h)

中文:
定理 apply_firstDiff_ne
  条件: {x y : 对任意 n, E n} (h : x != y)
  证明: by
  rw [firstDiff_def]; rw [dif_pos h]
  classical
  exact Nat.find_spec (ne_iff.1 h)

Depends on / 依赖: Nat.find_spec, classical, dif_pos, find_spec, firstDiff_def, ne_iff
-/
theorem apply_firstDiff_ne {x y : forall n, E n} (h : x != y) :
    x (firstDiff x y) != y (firstDiff x y) := by
  rw [firstDiff_def]; rw [dif_pos h]
  classical
  exact Nat.find_spec (ne_iff.1 h)

/--
theorem `apply_eq_of_lt_firstDiff` / 定理 `apply_eq_of_lt_firstDiff`

English:
theorem apply_eq_of_lt_firstDiff
  given: {x y : forall n, E n} {n : Nat} (hn : n < firstDiff x y)
  statement: x n = y n
  proof: by
  rw [firstDiff_def] at hn
  aesop

中文:
定理 apply_eq_of_lt_firstDiff
  条件: {x y : 对任意 n, E n} {n : 自然数} (hn : n < firstDiff x y)
  结论: x n = y n
  证明: by
  rw [firstDiff_def] at hn
  aesop

Depends on / 依赖: firstDiff_def
-/
theorem apply_eq_of_lt_firstDiff {x y : forall n, E n} {n : Nat} (hn : n < firstDiff x y) : x n = y n := by
  rw [firstDiff_def] at hn
  aesop

/--
theorem `firstDiff_comm` / 定理 `firstDiff_comm`

English:
theorem firstDiff_comm
  given: (x y : forall n, E n)
  statement: firstDiff x y = firstDiff y x
  proof: by
  classical
  simp only [firstDiff_def, ne_comm]

中文:
定理 firstDiff_comm
  条件: (x y : 对任意 n, E n)
  结论: firstDiff x y = firstDiff y x
  证明: by
  classical
  simp only [firstDiff_def, ne_comm]

Depends on / 依赖: classical, firstDiff_def, ne_comm
-/
theorem firstDiff_comm (x y : forall n, E n) : firstDiff x y = firstDiff y x := by
  classical
  simp only [firstDiff_def, ne_comm]

/--
theorem `min_firstDiff_le` / 定理 `min_firstDiff_le`

English:
theorem min_firstDiff_le
  given: (x y z : forall n, E n) (h : x != z)
  proof: by
  by_contra! H
  rw [lt_min_iff] at H
  refine apply_firstDiff_ne h ?_
  calc
    x (firstDiff x z) = y (firstDiff x z) := apply_eq_of_lt_firstDiff H.1
    _ = z (firstDiff x z) := apply_eq_of_lt_firstDiff H.2

中文:
定理 min_firstDiff_le
  条件: (x y z : 对任意 n, E n) (h : x != z)
  证明: by
  by_contra! H
  rw [lt_min_iff] at H
  refine apply_firstDiff_ne h ?_
  calc
    x (firstDiff x z) = y (firstDiff x z) := apply_eq_of_lt_firstDiff H.1
    _ = z (firstDiff x z) := apply_eq_of_lt_firstDiff H.2

Depends on / 依赖: apply_eq_of_lt_firstDiff, apply_firstDiff_ne, firstDiff, lt_min_iff
-/
theorem min_firstDiff_le (x y z : forall n, E n) (h : x != z) :
    min (firstDiff x y) (firstDiff y z) <= firstDiff x z := by
  by_contra! H
  rw [lt_min_iff] at H
  refine apply_firstDiff_ne h ?_
  calc
    x (firstDiff x z) = y (firstDiff x z) := apply_eq_of_lt_firstDiff H.1
    _ = z (firstDiff x z) := apply_eq_of_lt_firstDiff H.2

/-! ### Cylinders -/

/--
Definition of `cylinder` / `cylinder` 的定义

English:
definition cylinder
  signature: (x : forall n, E n) (n : Nat)
  body: { y | forall i, i < n -> y i = x i }

中文:
定义 cylinder
  签名: (x : 对任意 n, E n) (n : 自然数)
  定义体: { y | forall i, i < n -> y i = x i }
-/
def cylinder (x : forall n, E n) (n : Nat) : Set (forall n, E n) :=
  { y | forall i, i < n -> y i = x i }

/--
theorem `cylinder_eq_pi` / 定理 `cylinder_eq_pi`

English:
theorem cylinder_eq_pi
  given: (x : forall n, E n) (n : Nat)
  proof: by
  ext y
  simp [cylinder]

@[simp]

中文:
定理 cylinder_eq_pi
  条件: (x : 对任意 n, E n) (n : 自然数)
  证明: by
  ext y
  simp [cylinder]

@[simp]

Depends on / 依赖: cylinder
-/
theorem cylinder_eq_pi (x : forall n, E n) (n : Nat) :
    cylinder x n = Set.pi (Finset.range n : Set Nat) fun i : Nat => {x i} := by
  ext y
  simp [cylinder]

@[simp]
/--
theorem `cylinder_zero` / 定理 `cylinder_zero`

English:
theorem cylinder_zero
  given: (x : forall n, E n)
  statement: cylinder x 0 = univ
  proof: by simp [cylinder_eq_pi]

中文:
定理 cylinder_zero
  条件: (x : 对任意 n, E n)
  结论: cylinder x 0 = univ
  证明: by simp [cylinder_eq_pi]

Depends on / 依赖: cylinder_eq_pi
-/
theorem cylinder_zero (x : forall n, E n) : cylinder x 0 = univ := by simp [cylinder_eq_pi]

/--
theorem `cylinder_anti` / 定理 `cylinder_anti`

English:
theorem cylinder_anti
  given: (x : forall n, E n) {m n : Nat} (h : m <= n)
  statement: cylinder x n subseteq cylinder x m
  proof: fun _y hy i hi => hy i (hi.trans_le h)

@[simp]

中文:
定理 cylinder_anti
  条件: (x : 对任意 n, E n) {m n : 自然数} (h : m <= n)
  结论: cylinder x n subseteq cylinder x m
  证明: fun _y hy i hi => hy i (hi.trans_le h)

@[simp]

Depends on / 依赖: hi.trans_le, trans_le
-/
theorem cylinder_anti (x : forall n, E n) {m n : Nat} (h : m <= n) : cylinder x n subseteq cylinder x m :=
  fun _y hy i hi => hy i (hi.trans_le h)

@[simp]
/--
theorem `mem_cylinder_iff` / 定理 `mem_cylinder_iff`

English:
theorem mem_cylinder_iff
  given: {x y : forall n, E n} {n : Nat}
  statement: y in cylinder x n ↔ forall i < n, y i = x i
  proof: Iff.rfl

中文:
定理 mem_cylinder_iff
  条件: {x y : 对任意 n, E n} {n : 自然数}
  结论: y in cylinder x n ↔ 对任意 i < n, y i = x i
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_cylinder_iff {x y : forall n, E n} {n : Nat} : y in cylinder x n ↔ forall i < n, y i = x i :=
  Iff.rfl

/--
theorem `self_mem_cylinder` / 定理 `self_mem_cylinder`

English:
theorem self_mem_cylinder
  given: (x : forall n, E n) (n : Nat)
  statement: x in cylinder x n
  proof: by simp

中文:
定理 self_mem_cylinder
  条件: (x : 对任意 n, E n) (n : 自然数)
  结论: x in cylinder x n
  证明: by simp
-/
theorem self_mem_cylinder (x : forall n, E n) (n : Nat) : x in cylinder x n := by simp

/--
theorem `mem_cylinder_iff_eq` / 定理 `mem_cylinder_iff_eq`

English:
theorem mem_cylinder_iff_eq
  given: {x y : forall n, E n} {n : Nat}
  proof: by
  constructor
  · intro hy
    apply Subset.antisymm
    · intro z hz i hi
      rw [← hy i hi]
      exact hz i hi
    · intro z hz i hi
      rw [hy i hi]
      exact hz i hi
  · intro h
    rw [← h]
    exact self_mem_cylinder _ _

中文:
定理 mem_cylinder_iff_eq
  条件: {x y : 对任意 n, E n} {n : 自然数}
  证明: by
  constructor
  · intro hy
    apply Subset.antisymm
    · intro z hz i hi
      rw [← hy i hi]
      exact hz i hi
    · intro z hz i hi
      rw [hy i hi]
      exact hz i hi
  · intro h
    rw [← h]
    exact self_mem_cylinder _ _

Depends on / 依赖: Subset, Subset.antisymm, antisymm, self_mem_cylinder
-/
theorem mem_cylinder_iff_eq {x y : forall n, E n} {n : Nat} :
    y in cylinder x n ↔ cylinder y n = cylinder x n := by
  constructor
  · intro hy
    apply Subset.antisymm
    · intro z hz i hi
      rw [← hy i hi]
      exact hz i hi
    · intro z hz i hi
      rw [hy i hi]
      exact hz i hi
  · intro h
    rw [← h]
    exact self_mem_cylinder _ _

/--
theorem `mem_cylinder_comm` / 定理 `mem_cylinder_comm`

English:
theorem mem_cylinder_comm
  given: (x y : forall n, E n) (n : Nat)
  statement: y in cylinder x n ↔ x in cylinder y n
  proof: by
  simp [eq_comm]

中文:
定理 mem_cylinder_comm
  条件: (x y : 对任意 n, E n) (n : 自然数)
  结论: y in cylinder x n ↔ x in cylinder y n
  证明: by
  simp [eq_comm]

Depends on / 依赖: eq_comm
-/
theorem mem_cylinder_comm (x y : forall n, E n) (n : Nat) : y in cylinder x n ↔ x in cylinder y n := by
  simp [eq_comm]

/--
theorem `mem_cylinder_iff_le_firstDiff` / 定理 `mem_cylinder_iff_le_firstDiff`

English:
theorem mem_cylinder_iff_le_firstDiff
  given: {x y : forall n, E n} (hne : x != y) (i : Nat)
  proof: by
  constructor
  · intro h
    by_contra!
    exact apply_firstDiff_ne hne (h _ this)
  · intro hi j hj
    exact apply_eq_of_lt_firstDiff (hj.trans_le hi)

中文:
定理 mem_cylinder_iff_le_firstDiff
  条件: {x y : 对任意 n, E n} (hne : x != y) (i : 自然数)
  证明: by
  constructor
  · intro h
    by_contra!
    exact apply_firstDiff_ne hne (h _ this)
  · intro hi j hj
    exact apply_eq_of_lt_firstDiff (hj.trans_le hi)

Depends on / 依赖: apply_eq_of_lt_firstDiff, apply_firstDiff_ne, hj.trans_le, trans_le
-/
theorem mem_cylinder_iff_le_firstDiff {x y : forall n, E n} (hne : x != y) (i : Nat) :
    x in cylinder y i ↔ i <= firstDiff x y := by
  constructor
  · intro h
    by_contra!
    exact apply_firstDiff_ne hne (h _ this)
  · intro hi j hj
    exact apply_eq_of_lt_firstDiff (hj.trans_le hi)

/--
theorem `mem_cylinder_firstDiff` / 定理 `mem_cylinder_firstDiff`

English:
theorem mem_cylinder_firstDiff
  given: (x y : forall n, E n)
  statement: x in cylinder y (firstDiff x y)
  proof: fun _i hi =>
  apply_eq_of_lt_firstDiff hi

中文:
定理 mem_cylinder_firstDiff
  条件: (x y : 对任意 n, E n)
  结论: x in cylinder y (firstDiff x y)
  证明: fun _i hi =>
  apply_eq_of_lt_firstDiff hi
-/
theorem mem_cylinder_firstDiff (x y : forall n, E n) : x in cylinder y (firstDiff x y) := fun _i hi =>
  apply_eq_of_lt_firstDiff hi

/--
theorem `cylinder_eq_cylinder_of_le_firstDiff` / 定理 `cylinder_eq_cylinder_of_le_firstDiff`

English:
theorem cylinder_eq_cylinder_of_le_firstDiff
  given: (x y : forall n, E n) {n : Nat} (hn : n <= firstDiff x y)
  proof: by
  rw [← mem_cylinder_iff_eq]
  intro i hi
  exact apply_eq_of_lt_firstDiff (hi.trans_le hn)

中文:
定理 cylinder_eq_cylinder_of_le_firstDiff
  条件: (x y : 对任意 n, E n) {n : 自然数} (hn : n <= firstDiff x y)
  证明: by
  rw [← mem_cylinder_iff_eq]
  intro i hi
  exact apply_eq_of_lt_firstDiff (hi.trans_le hn)

Depends on / 依赖: apply_eq_of_lt_firstDiff, hi.trans_le, mem_cylinder_iff_eq, trans_le
-/
theorem cylinder_eq_cylinder_of_le_firstDiff (x y : forall n, E n) {n : Nat} (hn : n <= firstDiff x y) :
    cylinder x n = cylinder y n := by
  rw [← mem_cylinder_iff_eq]
  intro i hi
  exact apply_eq_of_lt_firstDiff (hi.trans_le hn)

/--
theorem `iUnion_cylinder_update` / 定理 `iUnion_cylinder_update`

English:
theorem iUnion_cylinder_update
  given: (x : forall n, E n) (n : Nat)
  proof: by
  ext y
  simp only [mem_cylinder_iff, mem_iUnion]
  constructor
  · rintro ⟨k, hk⟩ i hi
    simpa [hi.ne] using hk i (Nat.lt_succ_of_lt hi)
  · intro H
    refine ⟨y n, fun i hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with (h'i | rfl)
    · simp [H i h'i, h'i.ne]
    · simp

中文:
定理 iUnion_cylinder_update
  条件: (x : 对任意 n, E n) (n : 自然数)
  证明: by
  ext y
  simp only [mem_cylinder_iff, mem_iUnion]
  constructor
  · rintro ⟨k, hk⟩ i hi
    simpa [hi.ne] using hk i (Nat.lt_succ_of_lt hi)
  · intro H
    refine ⟨y n, fun i hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with (h'i | rfl)
    · simp [H i h'i, h'i.ne]
    · simp

Depends on / 依赖: Nat.lt_succ_iff_lt_or_eq, Nat.lt_succ_of_lt, hi.ne, i.ne, lt_succ_iff_lt_or_eq, lt_succ_of_lt, mem_cylinder_iff, mem_iUnion
-/
theorem iUnion_cylinder_update (x : forall n, E n) (n : Nat) :
    ⋃ k, cylinder (update x n k) (n + 1) = cylinder x n := by
  ext y
  simp only [mem_cylinder_iff, mem_iUnion]
  constructor
  · rintro ⟨k, hk⟩ i hi
    simpa [hi.ne] using hk i (Nat.lt_succ_of_lt hi)
  · intro H
    refine ⟨y n, fun i hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with (h'i | rfl)
    · simp [H i h'i, h'i.ne]
    · simp

/--
theorem `update_mem_cylinder` / 定理 `update_mem_cylinder`

English:
theorem update_mem_cylinder
  given: (x : forall n, E n) (n : Nat) (y : E n)
  statement: update x n y in cylinder x n
  proof: mem_cylinder_iff.2 fun i hi => by simp [hi.ne]

中文:
定理 update_mem_cylinder
  条件: (x : 对任意 n, E n) (n : 自然数) (y : E n)
  结论: update x n y in cylinder x n
  证明: mem_cylinder_iff.2 fun i hi => by simp [hi.ne]

Depends on / 依赖: hi.ne, mem_cylinder_iff
-/
theorem update_mem_cylinder (x : forall n, E n) (n : Nat) (y : E n) : update x n y in cylinder x n :=
  mem_cylinder_iff.2 fun i hi => by simp [hi.ne]

section Res

variable {α : Type*}

open List

/--
Definition of `res` / `res` 的定义

English:
definition res
  signature: (x : Nat -> α)

中文:
定义 res
  签名: (x : 自然数 -> α)
-/
def res (x : Nat -> α) : Nat -> List α
  | 0 => nil
  | Nat.succ n => x n :: res x n

@[simp]
/--
theorem `res_zero` / 定理 `res_zero`

English:
theorem res_zero
  given: (x : Nat -> α)
  statement: res x 0 = @nil α
  proof: rfl

@[simp]

中文:
定理 res_zero
  条件: (x : 自然数 -> α)
  结论: res x 0 = @nil α
  证明: rfl

@[simp]
-/
theorem res_zero (x : Nat -> α) : res x 0 = @nil α :=
  rfl

@[simp]
/--
theorem `res_succ` / 定理 `res_succ`

English:
theorem res_succ
  given: (x : Nat -> α) (n : Nat)
  statement: res x n.succ = x n :: res x n
  proof: rfl

@[simp]

中文:
定理 res_succ
  条件: (x : 自然数 -> α) (n : 自然数)
  结论: res x n.succ = x n :: res x n
  证明: rfl

@[simp]
-/
theorem res_succ (x : Nat -> α) (n : Nat) : res x n.succ = x n :: res x n :=
  rfl

@[simp]
/--
theorem `res_length` / 定理 `res_length`

English:
theorem res_length
  given: (x : Nat -> α) (n : Nat)
  statement: (res x n).length = n
  proof: by induction n <;> simp [*]

中文:
定理 res_length
  条件: (x : 自然数 -> α) (n : 自然数)
  结论: (res x n).length = n
  证明: by induction n <;> simp [*]
-/
theorem res_length (x : Nat -> α) (n : Nat) : (res x n).length = n := by induction n <;> simp [*]

/--
theorem `res_eq_res` / 定理 `res_eq_res`

English:
theorem res_eq_res
  given: {x y : Nat -> α} {n : Nat}
  proof: by
  constructor <;> intro h
  · induction n with
    | zero => simp
    | succ n ih =>
      intro m hm
      rw [Nat.lt_succ_iff_lt_or_eq] at hm
      simp only [res_succ, cons.injEq] at h
      rcases hm with hm | hm
      · exact ih h.2 hm
      rw [hm]
      exact h.1
  · induction n with
    |

中文:
定理 res_eq_res
  条件: {x y : 自然数 -> α} {n : 自然数}
  证明: by
  constructor <;> intro h
  · induction n with
    | zero => simp
    | succ n ih =>
      intro m hm
      rw [Nat.lt_succ_iff_lt_or_eq] at hm
      simp only [res_succ, cons.injEq] at h
      rcases hm with hm | hm
      · exact ih h.2 hm
      rw [hm]
      exact h.1
  · induction n with
    |

Depends on / 依赖: Nat.lt_succ_iff_lt_or_eq, Nat.lt_succ_self, cons.injEq, hm.trans, lt_succ_iff_lt_or_eq, lt_succ_self, res_succ
-/
theorem res_eq_res {x y : Nat -> α} {n : Nat} :
    res x n = res y n ↔ forall ⦃m⦄, m < n -> x m = y m := by
  constructor <;> intro h
  · induction n with
    | zero => simp
    | succ n ih =>
      intro m hm
      rw [Nat.lt_succ_iff_lt_or_eq] at hm
      simp only [res_succ, cons.injEq] at h
      rcases hm with hm | hm
      · exact ih h.2 hm
      rw [hm]
      exact h.1
  · induction n with
    | zero => simp
    | succ n ih =>
      simp only [res_succ, cons.injEq]
      refine ⟨h (Nat.lt_succ_self _), ih fun m hm => ?_⟩
      exact h (hm.trans (Nat.lt_succ_self _))

/--
theorem `res_injective` / 定理 `res_injective`

English:
theorem res_injective
  statement: Injective (@res α)
  proof: by
  intro x y h
  ext n
  apply res_eq_res.mp _ (Nat.lt_succ_self _)
  rw [h]

中文:
定理 res_injective
  结论: 单射 (@res α)
  证明: by
  intro x y h
  ext n
  apply res_eq_res.mp _ (Nat.lt_succ_self _)
  rw [h]

Depends on / 依赖: Nat.lt_succ_self, lt_succ_self, res_eq_res, res_eq_res.mp
-/
theorem res_injective : Injective (@res α) := by
  intro x y h
  ext n
  apply res_eq_res.mp _ (Nat.lt_succ_self _)
  rw [h]

/--
theorem `cylinder_eq_res` / 定理 `cylinder_eq_res`

English:
theorem cylinder_eq_res
  given: (x : Nat -> α) (n : Nat)
  proof: by
  ext y
  dsimp [cylinder]
  rw [res_eq_res]

中文:
定理 cylinder_eq_res
  条件: (x : 自然数 -> α) (n : 自然数)
  证明: by
  ext y
  dsimp [cylinder]
  rw [res_eq_res]

Depends on / 依赖: cylinder, res_eq_res
-/
theorem cylinder_eq_res (x : Nat -> α) (n : Nat) :
    cylinder x n = { y | res y n = res x n } := by
  ext y
  dsimp [cylinder]
  rw [res_eq_res]

end Res

/-!
### A distance function on `Π n, E n`

We define a distance function on `Π n, E n`, given by `dist x y = (1/2)^n` where `n` is the first
index at which `x` and `y` differ. When each `E n` has the discrete topology, this distance will
define the right topology on the product space. We do not record a global `Dist` instance nor
a `MetricSpace` instance, as other distances may be used on these spaces, but we register them as
local instances in this section.
-/

open scoped Classical in
/-- The distance function on a product space `Π n, E n`, given by `dist x y = (1/2)^n` where `n` is
the first index at which `x` and `y` differ. -/
@[instance_reducible]
/--
Definition of `dist` / `dist` 的定义

English:
definition dist
  signature: : Dist (forall n, E n)
  body: ⟨fun x y => if x != y then (1 / 2 : Real) ^ firstDiff x y else 0⟩

中文:
定义 dist
  签名: : Dist (对任意 n, E n)
  定义体: ⟨fun x y => if x != y then (1 / 2 : Real) ^ firstDiff x y else 0⟩
-/
protected def dist : Dist (forall n, E n) :=
  ⟨fun x y => if x != y then (1 / 2 : Real) ^ firstDiff x y else 0⟩

attribute [local instance] PiNat.dist

/--
theorem `dist_eq_of_ne` / 定理 `dist_eq_of_ne`

English:
theorem dist_eq_of_ne
  given: {x y : forall n, E n} (h : x != y)
  statement: dist x y = (1 / 2 : Real) ^ firstDiff x y
  proof: by
  simp [dist, h]

中文:
定理 dist_eq_of_ne
  条件: {x y : 对任意 n, E n} (h : x != y)
  结论: dist x y = (1 / 2 : 实数) ^ firstDiff x y
  证明: by
  simp [dist, h]
-/
theorem dist_eq_of_ne {x y : forall n, E n} (h : x != y) : dist x y = (1 / 2 : Real) ^ firstDiff x y := by
  simp [dist, h]

/--
theorem `dist_self` / 定理 `dist_self`

English:
theorem dist_self
  given: (x : forall n, E n)
  statement: dist x x = 0
  proof: by simp [dist]

中文:
定理 dist_self
  条件: (x : 对任意 n, E n)
  结论: dist x x = 0
  证明: by simp [dist]
-/
protected theorem dist_self (x : forall n, E n) : dist x x = 0 := by simp [dist]

/--
theorem `dist_comm` / 定理 `dist_comm`

English:
theorem dist_comm
  given: (x y : forall n, E n)
  statement: dist x y = dist y x
  proof: by
  classical
  simp [dist, @eq_comm _ x y, firstDiff_comm]

中文:
定理 dist_comm
  条件: (x y : 对任意 n, E n)
  结论: dist x y = dist y x
  证明: by
  classical
  simp [dist, @eq_comm _ x y, firstDiff_comm]
-/
protected theorem dist_comm (x y : forall n, E n) : dist x y = dist y x := by
  classical
  simp [dist, @eq_comm _ x y, firstDiff_comm]

/--
theorem `dist_nonneg` / 定理 `dist_nonneg`

English:
theorem dist_nonneg
  given: (x y : forall n, E n)
  statement: 0 <= dist x y
  proof: by
  rcases eq_or_ne x y with (rfl | h)
  · simp [dist]
  · simp [dist, h]

中文:
定理 dist_nonneg
  条件: (x y : 对任意 n, E n)
  结论: 0 <= dist x y
  证明: by
  rcases eq_or_ne x y with (rfl | h)
  · simp [dist]
  · simp [dist, h]
-/
protected theorem dist_nonneg (x y : forall n, E n) : 0 <= dist x y := by
  rcases eq_or_ne x y with (rfl | h)
  · simp [dist]
  · simp [dist, h]

/--
theorem `dist_le_one` / 定理 `dist_le_one`

English:
theorem dist_le_one
  given: (x y : forall n, E n)
  statement: dist x y <= 1
  proof: by
  rcases eq_or_ne x y with (rfl | h)
  · simp [dist]
  · simp only [dist, ne_eq, h, not_false_eq_true, ↓reduceIte, one_div, inv_pow]
    bound

中文:
定理 dist_le_one
  条件: (x y : 对任意 n, E n)
  结论: dist x y <= 1
  证明: by
  rcases eq_or_ne x y with (rfl | h)
  · simp [dist]
  · simp only [dist, ne_eq, h, not_false_eq_true, ↓reduceIte, one_div, inv_pow]
    bound
-/
protected theorem dist_le_one (x y : forall n, E n) : dist x y <= 1 := by
  rcases eq_or_ne x y with (rfl | h)
  · simp [dist]
  · simp only [dist, ne_eq, h, not_false_eq_true, ↓reduceIte, one_div, inv_pow]
    bound

/--
theorem `dist_triangle_nonarch` / 定理 `dist_triangle_nonarch`

English:
theorem dist_triangle_nonarch
  given: (x y z : forall n, E n)
  statement: dist x z <= max (dist x y) (dist y z)
  proof: by
  rcases eq_or_ne x z with (rfl | hxz)
  · simp [PiNat.dist_self x, PiNat.dist_nonneg]
  rcases eq_or_ne x y with (rfl | hxy)
  · simp
  rcases eq_or_ne y z with (rfl | hyz)
  · simp
  simp only [dist_eq_of_ne, hxz, hxy, hyz, inv_le_inv₀, one_div, inv_pow, zero_lt_two, Ne,
    not_false_iff, le_m

中文:
定理 dist_triangle_nonarch
  条件: (x y z : 对任意 n, E n)
  结论: dist x z <= 最大值 (dist x y) (dist y z)
  证明: by
  rcases eq_or_ne x z with (rfl | hxz)
  · simp [PiNat.dist_self x, PiNat.dist_nonneg]
  rcases eq_or_ne x y with (rfl | hxy)
  · simp
  rcases eq_or_ne y z with (rfl | hyz)
  · simp
  simp only [dist_eq_of_ne, hxz, hxy, hyz, inv_le_inv₀, one_div, inv_pow, zero_lt_two, Ne,
    not_false_iff, le_m

Depends on / 依赖: PiNat.dist_nonneg, PiNat.dist_self, dist_eq_of_ne, dist_nonneg, dist_self, eq_or_ne, inv_pow, le_max_iff, min_firstDiff_le, min_le_iff, not_false_iff, one_div, one_lt_two, pow_pos, zero_lt_two
-/
theorem dist_triangle_nonarch (x y z : forall n, E n) : dist x z <= max (dist x y) (dist y z) := by
  rcases eq_or_ne x z with (rfl | hxz)
  · simp [PiNat.dist_self x, PiNat.dist_nonneg]
  rcases eq_or_ne x y with (rfl | hxy)
  · simp
  rcases eq_or_ne y z with (rfl | hyz)
  · simp
  simp only [dist_eq_of_ne, hxz, hxy, hyz, inv_le_inv₀, one_div, inv_pow, zero_lt_two, Ne,
    not_false_iff, le_max_iff, pow_le_pow_iff_right₀, one_lt_two, pow_pos,
    min_le_iff.1 (min_firstDiff_le x y z hxz)]

/--
theorem `dist_triangle` / 定理 `dist_triangle`

English:
theorem dist_triangle
  given: (x y z : forall n, E n)
  statement: dist x z <= dist x y + dist y z
  proof: calc
    dist x z <= max (dist x y) (dist y z) := dist_triangle_nonarch x y z
    _ <= dist x y + dist y z := max_le_add_of_nonneg (PiNat.dist_nonneg _ _) (PiNat.dist_nonneg _ _)

中文:
定理 dist_triangle
  条件: (x y z : 对任意 n, E n)
  结论: dist x z <= dist x y + dist y z
  证明: calc
    dist x z <= max (dist x y) (dist y z) := dist_triangle_nonarch x y z
    _ <= dist x y + dist y z := max_le_add_of_nonneg (PiNat.dist_nonneg _ _) (PiNat.dist_nonneg _ _)
-/
protected theorem dist_triangle (x y z : forall n, E n) : dist x z <= dist x y + dist y z :=
  calc
    dist x z <= max (dist x y) (dist y z) := dist_triangle_nonarch x y z
    _ <= dist x y + dist y z := max_le_add_of_nonneg (PiNat.dist_nonneg _ _) (PiNat.dist_nonneg _ _)

/--
theorem `eq_of_dist_eq_zero` / 定理 `eq_of_dist_eq_zero`

English:
theorem eq_of_dist_eq_zero
  given: (x y : forall n, E n) (hxy : dist x y = 0)
  statement: x = y
  proof: by
  rcases eq_or_ne x y with (rfl | h); · rfl
  simp [dist_eq_of_ne h] at hxy

中文:
定理 eq_of_dist_eq_zero
  条件: (x y : 对任意 n, E n) (hxy : dist x y = 0)
  结论: x = y
  证明: by
  rcases eq_or_ne x y with (rfl | h); · rfl
  simp [dist_eq_of_ne h] at hxy
-/
protected theorem eq_of_dist_eq_zero (x y : forall n, E n) (hxy : dist x y = 0) : x = y := by
  rcases eq_or_ne x y with (rfl | h); · rfl
  simp [dist_eq_of_ne h] at hxy

/--
theorem `mem_cylinder_iff_dist_le` / 定理 `mem_cylinder_iff_dist_le`

English:
theorem mem_cylinder_iff_dist_le
  given: {x y : forall n, E n} {n : Nat}
  proof: by
  rcases eq_or_ne y x with (rfl | hne)
  · simp [PiNat.dist_self]
  suffices (forall i : Nat, i < n -> y i = x i) ↔ n <= firstDiff y x by simpa [dist_eq_of_ne hne]
  constructor
  · intro hy
    by_contra! H
    exact apply_firstDiff_ne hne (hy _ H)
  · intro h i hi
    exact apply_eq_of_lt_first

中文:
定理 mem_cylinder_iff_dist_le
  条件: {x y : 对任意 n, E n} {n : 自然数}
  证明: by
  rcases eq_or_ne y x with (rfl | hne)
  · simp [PiNat.dist_self]
  suffices (forall i : Nat, i < n -> y i = x i) ↔ n <= firstDiff y x by simpa [dist_eq_of_ne hne]
  constructor
  · intro hy
    by_contra! H
    exact apply_firstDiff_ne hne (hy _ H)
  · intro h i hi
    exact apply_eq_of_lt_first

Depends on / 依赖: PiNat.dist_self, apply_eq_of_lt_firstDiff, apply_firstDiff_ne, dist_eq_of_ne, dist_self, eq_or_ne, firstDiff, hi.trans_le, trans_le
-/
theorem mem_cylinder_iff_dist_le {x y : forall n, E n} {n : Nat} :
    y in cylinder x n ↔ dist y x <= (1 / 2) ^ n := by
  rcases eq_or_ne y x with (rfl | hne)
  · simp [PiNat.dist_self]
  suffices (forall i : Nat, i < n -> y i = x i) ↔ n <= firstDiff y x by simpa [dist_eq_of_ne hne]
  constructor
  · intro hy
    by_contra! H
    exact apply_firstDiff_ne hne (hy _ H)
  · intro h i hi
    exact apply_eq_of_lt_firstDiff (hi.trans_le h)

/--
theorem `apply_eq_of_dist_lt` / 定理 `apply_eq_of_dist_lt`

English:
theorem apply_eq_of_dist_lt
  statement: {x y : forall n, E n} {n : Nat} (h : dist x y < (1 / 2) ^ n) {i : Nat}
  proof: by
  rcases eq_or_ne x y with (rfl | hne)
  · rfl
  have : n < firstDiff x y := by
    simpa [dist_eq_of_ne hne, inv_lt_inv₀, pow_lt_pow_iff_right₀, one_lt_two] using h
  exact apply_eq_of_lt_firstDiff (hi.trans_lt this)

中文:
定理 apply_eq_of_dist_lt
  结论: {x y : 对任意 n, E n} {n : 自然数} (h : dist x y < (1 / 2) ^ n) {i : 自然数}
  证明: by
  rcases eq_or_ne x y with (rfl | hne)
  · rfl
  have : n < firstDiff x y := by
    simpa [dist_eq_of_ne hne, inv_lt_inv₀, pow_lt_pow_iff_right₀, one_lt_two] using h
  exact apply_eq_of_lt_firstDiff (hi.trans_lt this)

Depends on / 依赖: apply_eq_of_lt_firstDiff, dist_eq_of_ne, eq_or_ne, firstDiff, hi.trans_lt, one_lt_two, trans_lt
-/
theorem apply_eq_of_dist_lt {x y : forall n, E n} {n : Nat} (h : dist x y < (1 / 2) ^ n) {i : Nat}
    (hi : i <= n) : x i = y i := by
  rcases eq_or_ne x y with (rfl | hne)
  · rfl
  have : n < firstDiff x y := by
    simpa [dist_eq_of_ne hne, inv_lt_inv₀, pow_lt_pow_iff_right₀, one_lt_two] using h
  exact apply_eq_of_lt_firstDiff (hi.trans_lt this)

/--
theorem `lipschitz_with_one_iff_forall_dist_image_le_of_mem_cylinder` / 定理 `lipschitz_with_one_iff_forall_dist_image_le_of_mem_cylinder`

English:
theorem lipschitz_with_one_iff_forall_dist_image_le_of_mem_cylinder
  statement: {α : Type*}
  proof: by
  constructor
  · intro H x y n hxy
    apply (H x y).trans
    rw [PiNat.dist_comm]
    exact mem_cylinder_iff_dist_le.1 hxy
  · intro H x y
    rcases eq_or_ne x y with (rfl | hne)
    · simp [PiNat.dist_nonneg]
    rw [dist_eq_of_ne hne]
    apply H x y (firstDiff x y)
    rw [firstDiff_comm]


中文:
定理 lipschitz_with_one_iff_对任意_dist_image_le_of_mem_cylinder
  结论: {α : 类型}
  证明: by
  constructor
  · intro H x y n hxy
    apply (H x y).trans
    rw [PiNat.dist_comm]
    exact mem_cylinder_iff_dist_le.1 hxy
  · intro H x y
    rcases eq_or_ne x y with (rfl | hne)
    · simp [PiNat.dist_nonneg]
    rw [dist_eq_of_ne hne]
    apply H x y (firstDiff x y)
    rw [firstDiff_comm]


Depends on / 依赖: PiNat.dist_comm, PiNat.dist_nonneg, dist_comm, dist_eq_of_ne, dist_nonneg, eq_or_ne, firstDiff, firstDiff_comm, mem_cylinder_firstDiff, mem_cylinder_iff_dist_le
-/
theorem lipschitz_with_one_iff_forall_dist_image_le_of_mem_cylinder {α : Type*}
    [PseudoMetricSpace α] {f : (forall n, E n) -> α} :
    (forall x y : forall n, E n, dist (f x) (f y) <= dist x y) ↔
      forall x y n, y in cylinder x n -> dist (f x) (f y) <= (1 / 2) ^ n := by
  constructor
  · intro H x y n hxy
    apply (H x y).trans
    rw [PiNat.dist_comm]
    exact mem_cylinder_iff_dist_le.1 hxy
  · intro H x y
    rcases eq_or_ne x y with (rfl | hne)
    · simp [PiNat.dist_nonneg]
    rw [dist_eq_of_ne hne]
    apply H x y (firstDiff x y)
    rw [firstDiff_comm]
    exact mem_cylinder_firstDiff _ _

variable (E)
variable [forall n, TopologicalSpace (E n)] [forall n, DiscreteTopology (E n)]

/--
theorem `isOpen_cylinder` / 定理 `isOpen_cylinder`

English:
theorem isOpen_cylinder
  given: (x : forall n, E n) (n : Nat)
  statement: IsOpen (cylinder x n)
  proof: by
  rw [PiNat.cylinder_eq_pi]
  exact isOpen_set_pi (Finset.range n).finite_toSet fun a _ => isOpen_discrete _

中文:
定理 isOpen_cylinder
  条件: (x : 对任意 n, E n) (n : 自然数)
  结论: 是开集 (cylinder x n)
  证明: by
  rw [PiNat.cylinder_eq_pi]
  exact isOpen_set_pi (Finset.range n).finite_toSet fun a _ => isOpen_discrete _

Depends on / 依赖: Finset, Finset.range, PiNat.cylinder_eq_pi, cylinder_eq_pi, finite_toSet, isOpen_discrete, isOpen_set_pi
-/
theorem isOpen_cylinder (x : forall n, E n) (n : Nat) : IsOpen (cylinder x n) := by
  rw [PiNat.cylinder_eq_pi]
  exact isOpen_set_pi (Finset.range n).finite_toSet fun a _ => isOpen_discrete _

/--
theorem `isTopologicalBasis_cylinders` / 定理 `isTopologicalBasis_cylinders`

English:
theorem isTopologicalBasis_cylinders
  proof: by
  apply isTopologicalBasis_of_isOpen_of_nhds
  · rintro u ⟨x, n, rfl⟩
    apply isOpen_cylinder
  · intro x u hx u_open
    obtain ⟨v, ⟨U, F, -, rfl⟩, xU, Uu⟩ :
        exists v in { S : Set (forall i : Nat, E i) | exists (U : forall i : Nat, Set (E i)) (F : Finset Nat),
          (forall i : Nat

中文:
定理 isTopologicalBasis_cylinders
  证明: by
  apply isTopologicalBasis_of_isOpen_of_nhds
  · rintro u ⟨x, n, rfl⟩
    apply isOpen_cylinder
  · intro x u hx u_open
    obtain ⟨v, ⟨U, F, -, rfl⟩, xU, Uu⟩ :
        exists v in { S : Set (forall i : Nat, E i) | exists (U : forall i : Nat, Set (E i)) (F : Finset Nat),
          (forall i : Nat

Depends on / 依赖: Finset, Finset.bddAbove, IsOpen, bddAbove, exists_subset_of_mem_open, isOpen_cylinder, isTopologicalBasis_of_isOpen_of_nhds, isTopologicalBasis_opens, isTopologicalBasis_pi, subseteq, u_open
-/
theorem isTopologicalBasis_cylinders :
    IsTopologicalBasis { s : Set (forall n, E n) | exists (x : forall n, E n) (n : Nat), s = cylinder x n } := by
  apply isTopologicalBasis_of_isOpen_of_nhds
  · rintro u ⟨x, n, rfl⟩
    apply isOpen_cylinder
  · intro x u hx u_open
    obtain ⟨v, ⟨U, F, -, rfl⟩, xU, Uu⟩ :
        exists v in { S : Set (forall i : Nat, E i) | exists (U : forall i : Nat, Set (E i)) (F : Finset Nat),
          (forall i : Nat, i in F -> U i in { s : Set (E i) | IsOpen s }) ∧ S = (F : Set Nat).pi U },
        x in v ∧ v subseteq u :=
      (isTopologicalBasis_pi fun n : Nat => isTopologicalBasis_opens).exists_subset_of_mem_open hx
        u_open
    rcases Finset.bddAbove F with ⟨n, hn⟩
    refine ⟨cylinder x (n + 1), ⟨x, n + 1, rfl⟩, self_mem_cylinder _ _, Subset.trans ?_ Uu⟩
    intro y hy
    suffices forall i : Nat, i in F -> y i in U i by simpa
    intro i hi
    have : y i = x i := mem_cylinder_iff.1 hy i ((hn hi).trans_lt (lt_add_one n))
    rw [this]
    simp only [Set.mem_pi, Finset.mem_coe] at xU
    exact xU i hi

variable {E}

/--
theorem `isOpen_iff_dist` / 定理 `isOpen_iff_dist`

English:
theorem isOpen_iff_dist
  given: (s : Set (forall n, E n))
  proof: by
  constructor
  · intro hs x hx
    obtain ⟨v, ⟨y, n, rfl⟩, h'x, h's⟩ :
        exists v in { s | exists (x : forall n : Nat, E n) (n : Nat), s = cylinder x n }, x in v ∧ v subseteq s :=
      (isTopologicalBasis_cylinders E).exists_subset_of_mem_open hx hs
    rw [← mem_cylinder_iff_eq.1 h'x] at

中文:
定理 isOpen_iff_dist
  条件: (s : 集合 (对任意 n, E n))
  证明: by
  constructor
  · intro hs x hx
    obtain ⟨v, ⟨y, n, rfl⟩, h'x, h's⟩ :
        exists v in { s | exists (x : forall n : Nat, E n) (n : Nat), s = cylinder x n }, x in v ∧ v subseteq s :=
      (isTopologicalBasis_cylinders E).exists_subset_of_mem_open hx hs
    rw [← mem_cylinder_iff_eq.1 h'x] at

Depends on / 依赖: apply_eq_of_dist_lt, cylinder, exists_subset_of_mem_open, hi.le, isOpen_iff, isTopologicalBasis_cylinders, mem_cylinder_iff_eq, subseteq
-/
theorem isOpen_iff_dist (s : Set (forall n, E n)) :
    IsOpen s ↔ forall x in s, exists ε > 0, forall y, dist x y < ε -> y in s := by
  constructor
  · intro hs x hx
    obtain ⟨v, ⟨y, n, rfl⟩, h'x, h's⟩ :
        exists v in { s | exists (x : forall n : Nat, E n) (n : Nat), s = cylinder x n }, x in v ∧ v subseteq s :=
      (isTopologicalBasis_cylinders E).exists_subset_of_mem_open hx hs
    rw [← mem_cylinder_iff_eq.1 h'x] at h's
    exact
      ⟨(1 / 2 : Real) ^ n, by simp, fun y hy => h's fun i hi => (apply_eq_of_dist_lt hy hi.le).symm⟩
  · intro h
    refine (isTopologicalBasis_cylinders E).isOpen_iff.2 fun x hx => ?_
    rcases h x hx with ⟨ε, εpos, hε⟩
    obtain ⟨n, hn⟩ : exists n : Nat, (1 / 2 : Real) ^ n < ε := exists_pow_lt_of_lt_one εpos one_half_lt_one
    refine ⟨cylinder x n, ⟨x, n, rfl⟩, self_mem_cylinder x n, fun y hy => hε y ?_⟩
    rw [PiNat.dist_comm]
    exact (mem_cylinder_iff_dist_le.1 hy).trans_lt hn

/-- Metric space structure on `Π (n : ℕ), E n` when the spaces `E n` have the discrete topology,
where the distance is given by `dist x y = (1/2)^n`, where `n` is the smallest index where `x` and
`y` differ. Not registered as a global instance by default.
Warning: this definition makes sure that the topology is defeq to the original product topology,
but it does not take care of a possible uniformity. If the `E n` have a uniform structure, then
there will be two non-defeq uniform structures on `Π n, E n`, the product one and the one coming
from the metric structure. In this case, use `metricSpaceOfDiscreteUniformity` instead. -/
@[instance_reducible]
/--
Definition of `metricSpace` / `metricSpace` 的定义

English:
definition metricSpace
  signature: : MetricSpace (forall n, E n)
  body: MetricSpace.ofDistTopology dist PiNat.dist_self PiNat.dist_comm PiNat.dist_triangle
    isOpen_iff_dist PiNat.eq_of_dist_eq_zero

中文:
定义 metricSpace
  签名: : 度量空间 (对任意 n, E n)
  定义体: MetricSpace.ofDistTopology dist PiNat.dist_self PiNat.dist_comm PiNat.dist_triangle
    isOpen_iff_dist PiNat.eq_of_dist_eq_zero
-/
protected def metricSpace : MetricSpace (forall n, E n) :=
  MetricSpace.ofDistTopology dist PiNat.dist_self PiNat.dist_comm PiNat.dist_triangle
    isOpen_iff_dist PiNat.eq_of_dist_eq_zero

/-- Metric space structure on `Π (n : ℕ), E n` when the spaces `E n` have the discrete uniformity,
where the distance is given by `dist x y = (1/2)^n`, where `n` is the smallest index where `x` and
`y` differ. Not registered as a global instance by default. -/
@[instance_reducible]
/--
Definition of `metricSpaceOfDiscreteUniformity` / `metricSpaceOfDiscreteUniformity` 的定义

English:
definition metricSpaceOfDiscreteUniformity
  signature: {E : Nat -> Type*} [forall n, UniformSpace (E n)]
  body: haveI : forall n, DiscreteTopology (E n) := fun n => discreteTopology_of_discrete_uniformity (h n)
  { dist_triangle := PiNat.dist_triangle
    dist_comm := PiNat.dist_comm
    dist_self := PiNat.dist_self
    eq_of_dist_eq_zero := PiNat.eq_of_dist_eq_zero _ _
    toUniformSpace := Pi.uniformSpace _

中文:
定义 metricSpaceOfDiscreteUniformity
  签名: {E : 自然数 -> 类型} [对任意 n, 一致空间 (E n)]
  定义体: haveI : forall n, DiscreteTopology (E n) := fun n => discreteTopology_of_discrete_uniformity (h n)
  { dist_triangle := PiNat.dist_triangle
    dist_comm := PiNat.dist_comm
    dist_self := PiNat.dist_self
    eq_of_dist_eq_zero := PiNat.eq_of_dist_eq_zero _ _
    toUniformSpace := Pi.uniformSpace _
-/
protected def metricSpaceOfDiscreteUniformity {E : Nat -> Type*} [forall n, UniformSpace (E n)]
    (h : forall n, uniformity (E n) = 𝓟 SetRel.id) : MetricSpace (forall n, E n) :=
  haveI : forall n, DiscreteTopology (E n) := fun n => discreteTopology_of_discrete_uniformity (h n)
  { dist_triangle := PiNat.dist_triangle
    dist_comm := PiNat.dist_comm
    dist_self := PiNat.dist_self
    eq_of_dist_eq_zero := PiNat.eq_of_dist_eq_zero _ _
    toUniformSpace := Pi.uniformSpace _
    uniformity_dist := by
      simp only [Pi.uniformity, h, SetRel.id, comap_principal, preimage_ofPred_eq]
      apply le_antisymm
      · simp only [le_iInf_iff, le_principal_iff]
        intro ε εpos
        obtain ⟨n, hn⟩ : exists n, (1 / 2 : Real) ^ n < ε := exists_pow_lt_of_lt_one εpos (by norm_num)
        apply
          @mem_iInf_of_iInter _ _ _ _ _ (Finset.range n).finite_toSet fun i =>
            { p : (forall n : Nat, E n) × forall n : Nat, E n | p.fst i = p.snd i }
        · simp only [mem_principal, ofPred_subset_ofPred, imp_self, imp_true_iff]
        · rintro ⟨x, y⟩ hxy
          simp only [Finset.mem_coe, Finset.mem_range, iInter_coe_set, mem_iInter, mem_ofPred_eq]
            at hxy
          apply lt_of_le_of_lt _ hn
          rw [← mem_cylinder_iff_dist_le]; rw [mem_cylinder_iff]
          exact hxy
      · simp only [le_iInf_iff, le_principal_iff]
        intro n
        refine mem_iInf_of_mem ((1 / 2) ^ n : Real) ?_
        refine mem_iInf_of_mem (by positivity) ?_
        simp only [mem_principal, ofPred_subset_ofPred, Prod.forall]
        intro x y hxy
        exact apply_eq_of_dist_lt hxy le_rfl }

/-- Metric space structure on `ℕ → ℕ` where the distance is given by `dist x y = (1/2)^n`,
where `n` is the smallest index where `x` and `y` differ.
Not registered as a global instance by default. -/
@[instance_reducible]
/--
Definition of `metricSpaceNatNat` / `metricSpaceNatNat` 的定义

English:
definition metricSpaceNatNat
  signature: : MetricSpace (Nat -> Nat)
  body: PiNat.metricSpaceOfDiscreteUniformity fun _ => rfl

中文:
定义 metricSpace自然数自然数
  签名: : 度量空间 (自然数 -> 自然数)
  定义体: PiNat.metricSpaceOfDiscreteUniformity fun _ => rfl

Depends on / 依赖: PiNat.metricSpaceOfDiscreteUniformity, metricSpaceOfDiscreteUniformity
-/
def metricSpaceNatNat : MetricSpace (Nat -> Nat) :=
  PiNat.metricSpaceOfDiscreteUniformity fun _ => rfl

attribute [local instance] PiNat.metricSpace

/--
theorem `completeSpace` / 定理 `completeSpace`

English:
theorem completeSpace
  statement: CompleteSpace (forall n, E n)
  proof: by
  refine Metric.complete_of_convergent_controlled_sequences (fun n => (1 / 2) ^ n) (by simp) ?_
  intro u hu
  refine ⟨fun n => u n n, tendsto_pi_nhds.2 fun i => ?_⟩
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Filter.Ici_mem_atTop i] with n hn
  exact apply_eq_of_dist_lt (hu i i n le_

中文:
定理 completeSpace
  结论: 完备空间 (对任意 n, E n)
  证明: by
  refine Metric.complete_of_convergent_controlled_sequences (fun n => (1 / 2) ^ n) (by simp) ?_
  intro u hu
  refine ⟨fun n => u n n, tendsto_pi_nhds.2 fun i => ?_⟩
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Filter.Ici_mem_atTop i] with n hn
  exact apply_eq_of_dist_lt (hu i i n le_
-/
protected theorem completeSpace : CompleteSpace (forall n, E n) := by
  refine Metric.complete_of_convergent_controlled_sequences (fun n => (1 / 2) ^ n) (by simp) ?_
  intro u hu
  refine ⟨fun n => u n n, tendsto_pi_nhds.2 fun i => ?_⟩
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Filter.Ici_mem_atTop i] with n hn
  exact apply_eq_of_dist_lt (hu i i n le_rfl hn) le_rfl

/--
theorem `boundedSpace` / 定理 `boundedSpace`

English:
theorem boundedSpace
  statement: BoundedSpace (forall n, E n)
  proof: by
  rw [Metric.boundedSpace_iff]
  use 1
  apply PiNat.dist_le_one

中文:
定理 boundedSpace
  结论: 有界空间 (对任意 n, E n)
  证明: by
  rw [Metric.boundedSpace_iff]
  use 1
  apply PiNat.dist_le_one
-/
protected theorem boundedSpace : BoundedSpace (forall n, E n) := by
  rw [Metric.boundedSpace_iff]
  use 1
  apply PiNat.dist_le_one


/--
theorem `exists_disjoint_cylinder` / 定理 `exists_disjoint_cylinder`

English:
theorem exists_disjoint_cylinder
  statement: {s : Set (forall n, E n)} (hs : IsClosed s) {x : forall n, E n}
  proof: by
  rcases eq_empty_or_nonempty s with (rfl | hne)
  · exact ⟨0, by simp⟩
  have A : 0 < infDist x s := (hs.notMem_iff_infDist_pos hne).1 hx
  obtain ⟨n, hn⟩ : exists n, (1 / 2 : Real) ^ n < infDist x s := exists_pow_lt_of_lt_one A one_half_lt_one
  refine ⟨n, disjoint_left.2 fun y ys hy => ?_⟩
  a

中文:
定理 存在_disjoint_cylinder
  结论: {s : 集合 (对任意 n, E n)} (hs : 是闭集 s) {x : 对任意 n, E n}
  证明: by
  rcases eq_empty_or_nonempty s with (rfl | hne)
  · exact ⟨0, by simp⟩
  have A : 0 < infDist x s := (hs.notMem_iff_infDist_pos hne).1 hx
  obtain ⟨n, hn⟩ : exists n, (1 / 2 : Real) ^ n < infDist x s := exists_pow_lt_of_lt_one A one_half_lt_one
  refine ⟨n, disjoint_left.2 fun y ys hy => ?_⟩
  a

Depends on / 依赖: disjoint_left, eq_empty_or_nonempty, exists_pow_lt_of_lt_one, hs.notMem_iff_infDist_pos, infDist, infDist_le_dist_of_mem, lt_irrefl, mem_cylinder_comm, mem_cylinder_iff_dist_le, notMem_iff_infDist_pos, one_half_lt_one
-/
theorem exists_disjoint_cylinder {s : Set (forall n, E n)} (hs : IsClosed s) {x : forall n, E n}
    (hx : x ∉ s) : exists n, Disjoint s (cylinder x n) := by
  rcases eq_empty_or_nonempty s with (rfl | hne)
  · exact ⟨0, by simp⟩
  have A : 0 < infDist x s := (hs.notMem_iff_infDist_pos hne).1 hx
  obtain ⟨n, hn⟩ : exists n, (1 / 2 : Real) ^ n < infDist x s := exists_pow_lt_of_lt_one A one_half_lt_one
  refine ⟨n, disjoint_left.2 fun y ys hy => ?_⟩
  apply lt_irrefl (infDist x s)
  calc
    infDist x s <= dist x y := infDist_le_dist_of_mem ys
    _ <= (1 / 2) ^ n := by
      rw [mem_cylinder_comm] at hy
      exact mem_cylinder_iff_dist_le.1 hy
    _ < infDist x s := hn

open scoped Classical in
/--
Definition of `shortestPrefixDiff` / `shortestPrefixDiff` 的定义

English:
definition shortestPrefixDiff
  signature: {E : Nat -> Type*} (x : forall n, E n) (s : Set (forall n, E n))
  body: if h : exists n, Disjoint s (cylinder x n) then Nat.find h else 0

中文:
定义 shortestPrefixDiff
  签名: {E : 自然数 -> 类型} (x : 对任意 n, E n) (s : 集合 (对任意 n, E n))
  定义体: if h : exists n, Disjoint s (cylinder x n) then Nat.find h else 0

Depends on / 依赖: Disjoint, Nat.find, cylinder
-/
def shortestPrefixDiff {E : Nat -> Type*} (x : forall n, E n) (s : Set (forall n, E n)) : Nat :=
  if h : exists n, Disjoint s (cylinder x n) then Nat.find h else 0

/--
theorem `firstDiff_lt_shortestPrefixDiff` / 定理 `firstDiff_lt_shortestPrefixDiff`

English:
theorem firstDiff_lt_shortestPrefixDiff
  statement: {s : Set (forall n, E n)} (hs : IsClosed s) {x y : forall n, E n}
  proof: by
  have A := exists_disjoint_cylinder hs hx
  rw [shortestPrefixDiff]; rw [dif_pos A]
  classical
  have B := Nat.find_spec A
  contrapose! B
  rw [not_disjoint_iff_nonempty_inter]
  refine ⟨y, hy, ?_⟩
  rw [mem_cylinder_comm]
  exact cylinder_anti y B (mem_cylinder_firstDiff x y)

中文:
定理 firstDiff_lt_shortestPrefixDiff
  结论: {s : 集合 (对任意 n, E n)} (hs : 是闭集 s) {x y : 对任意 n, E n}
  证明: by
  have A := exists_disjoint_cylinder hs hx
  rw [shortestPrefixDiff]; rw [dif_pos A]
  classical
  have B := Nat.find_spec A
  contrapose! B
  rw [not_disjoint_iff_nonempty_inter]
  refine ⟨y, hy, ?_⟩
  rw [mem_cylinder_comm]
  exact cylinder_anti y B (mem_cylinder_firstDiff x y)

Depends on / 依赖: Nat.find_spec, classical, contrapose, cylinder_anti, dif_pos, exists_disjoint_cylinder, find_spec, mem_cylinder_comm, mem_cylinder_firstDiff, not_disjoint_iff_nonempty_inter, shortestPrefixDiff
-/
theorem firstDiff_lt_shortestPrefixDiff {s : Set (forall n, E n)} (hs : IsClosed s) {x y : forall n, E n}
    (hx : x ∉ s) (hy : y in s) : firstDiff x y < shortestPrefixDiff x s := by
  have A := exists_disjoint_cylinder hs hx
  rw [shortestPrefixDiff]; rw [dif_pos A]
  classical
  have B := Nat.find_spec A
  contrapose! B
  rw [not_disjoint_iff_nonempty_inter]
  refine ⟨y, hy, ?_⟩
  rw [mem_cylinder_comm]
  exact cylinder_anti y B (mem_cylinder_firstDiff x y)

/--
theorem `shortestPrefixDiff_pos` / 定理 `shortestPrefixDiff_pos`

English:
theorem shortestPrefixDiff_pos
  statement: {s : Set (forall n, E n)} (hs : IsClosed s) (hne : s.Nonempty)
  proof: by
  rcases hne with ⟨y, hy⟩
  exact (firstDiff_lt_shortestPrefixDiff hs hx hy).pos

中文:
定理 shortestPrefixDiff_pos
  结论: {s : 集合 (对任意 n, E n)} (hs : 是闭集 s) (hne : s.非空)
  证明: by
  rcases hne with ⟨y, hy⟩
  exact (firstDiff_lt_shortestPrefixDiff hs hx hy).pos

Depends on / 依赖: firstDiff_lt_shortestPrefixDiff
-/
theorem shortestPrefixDiff_pos {s : Set (forall n, E n)} (hs : IsClosed s) (hne : s.Nonempty)
    {x : forall n, E n} (hx : x ∉ s) : 0 < shortestPrefixDiff x s := by
  rcases hne with ⟨y, hy⟩
  exact (firstDiff_lt_shortestPrefixDiff hs hx hy).pos

/--
Definition of `longestPrefix` / `longestPrefix` 的定义

English:
definition longestPrefix
  signature: {E : Nat -> Type*} (x : forall n, E n) (s : Set (forall n, E n))
  body: shortestPrefixDiff x s - 1

中文:
定义 longestPrefix
  签名: {E : 自然数 -> 类型} (x : 对任意 n, E n) (s : 集合 (对任意 n, E n))
  定义体: shortestPrefixDiff x s - 1

Depends on / 依赖: shortestPrefixDiff
-/
def longestPrefix {E : Nat -> Type*} (x : forall n, E n) (s : Set (forall n, E n)) : Nat :=
  shortestPrefixDiff x s - 1

/--
theorem `firstDiff_le_longestPrefix` / 定理 `firstDiff_le_longestPrefix`

English:
theorem firstDiff_le_longestPrefix
  statement: {s : Set (forall n, E n)} (hs : IsClosed s) {x y : forall n, E n}
  proof: by
  rw [longestPrefix]; rw [le_tsub_iff_right]
  · exact firstDiff_lt_shortestPrefixDiff hs hx hy
  · exact shortestPrefixDiff_pos hs ⟨y, hy⟩ hx

中文:
定理 firstDiff_le_longestPrefix
  结论: {s : 集合 (对任意 n, E n)} (hs : 是闭集 s) {x y : 对任意 n, E n}
  证明: by
  rw [longestPrefix]; rw [le_tsub_iff_right]
  · exact firstDiff_lt_shortestPrefixDiff hs hx hy
  · exact shortestPrefixDiff_pos hs ⟨y, hy⟩ hx

Depends on / 依赖: firstDiff_lt_shortestPrefixDiff, le_tsub_iff_right, longestPrefix, shortestPrefixDiff_pos
-/
theorem firstDiff_le_longestPrefix {s : Set (forall n, E n)} (hs : IsClosed s) {x y : forall n, E n}
    (hx : x ∉ s) (hy : y in s) : firstDiff x y <= longestPrefix x s := by
  rw [longestPrefix]; rw [le_tsub_iff_right]
  · exact firstDiff_lt_shortestPrefixDiff hs hx hy
  · exact shortestPrefixDiff_pos hs ⟨y, hy⟩ hx

/--
theorem `inter_cylinder_longestPrefix_nonempty` / 定理 `inter_cylinder_longestPrefix_nonempty`

English:
theorem inter_cylinder_longestPrefix_nonempty
  statement: {s : Set (forall n, E n)} (hs : IsClosed s)
  proof: by
  by_cases hx : x in s
  · exact ⟨x, hx, self_mem_cylinder _ _⟩
  have A := exists_disjoint_cylinder hs hx
  have B : longestPrefix x s < shortestPrefixDiff x s :=
    Nat.pred_lt (shortestPrefixDiff_pos hs hne hx).ne'
  rw [longestPrefix]; rw [shortestPrefixDiff]; rw [dif_pos A] at B ⊢
  classic

中文:
定理 inter_cylinder_longestPrefix_nonempty
  结论: {s : 集合 (对任意 n, E n)} (hs : 是闭集 s)
  证明: by
  by_cases hx : x in s
  · exact ⟨x, hx, self_mem_cylinder _ _⟩
  have A := exists_disjoint_cylinder hs hx
  have B : longestPrefix x s < shortestPrefixDiff x s :=
    Nat.pred_lt (shortestPrefixDiff_pos hs hne hx).ne'
  rw [longestPrefix]; rw [shortestPrefixDiff]; rw [dif_pos A] at B ⊢
  classic

Depends on / 依赖: Nat.find, Nat.find_min, Nat.pred_lt, classical, cylinder, dif_pos, exists_disjoint_cylinder, find_min, longestPrefix, mem_cylinder_comm, mem_cylinder_iff_, not_disjoint_iff, pred_lt, self_mem_cylinder, shortestPrefixDiff, shortestPrefixDiff_pos
-/
theorem inter_cylinder_longestPrefix_nonempty {s : Set (forall n, E n)} (hs : IsClosed s)
    (hne : s.Nonempty) (x : forall n, E n) : (s inter cylinder x (longestPrefix x s)).Nonempty := by
  by_cases hx : x in s
  · exact ⟨x, hx, self_mem_cylinder _ _⟩
  have A := exists_disjoint_cylinder hs hx
  have B : longestPrefix x s < shortestPrefixDiff x s :=
    Nat.pred_lt (shortestPrefixDiff_pos hs hne hx).ne'
  rw [longestPrefix]; rw [shortestPrefixDiff]; rw [dif_pos A] at B ⊢
  classical
  obtain ⟨y, ys, hy⟩ : exists y : forall n : Nat, E n, y in s ∧ x in cylinder y (Nat.find A - 1) := by
    simpa only [not_disjoint_iff, mem_cylinder_comm] using Nat.find_min A B
  refine ⟨y, ys, ?_⟩
  rw [mem_cylinder_iff_eq] at hy ⊢
  rw [hy]

/--
theorem `disjoint_cylinder_of_longestPrefix_lt` / 定理 `disjoint_cylinder_of_longestPrefix_lt`

English:
theorem disjoint_cylinder_of_longestPrefix_lt
  statement: {s : Set (forall n, E n)} (hs : IsClosed s) {x : forall n, E n}
  proof: by
  contrapose! hn
  rcases not_disjoint_iff_nonempty_inter.1 hn with ⟨y, ys, hy⟩
  apply le_trans _ (firstDiff_le_longestPrefix hs hx ys)
  apply (mem_cylinder_iff_le_firstDiff (ne_of_mem_of_not_mem ys hx).symm _).1
  rwa [mem_cylinder_comm]

中文:
定理 disjoint_cylinder_of_longestPrefix_lt
  结论: {s : 集合 (对任意 n, E n)} (hs : 是闭集 s) {x : 对任意 n, E n}
  证明: by
  contrapose! hn
  rcases not_disjoint_iff_nonempty_inter.1 hn with ⟨y, ys, hy⟩
  apply le_trans _ (firstDiff_le_longestPrefix hs hx ys)
  apply (mem_cylinder_iff_le_firstDiff (ne_of_mem_of_not_mem ys hx).symm _).1
  rwa [mem_cylinder_comm]

Depends on / 依赖: contrapose, firstDiff_le_longestPrefix, le_trans, mem_cylinder_comm, mem_cylinder_iff_le_firstDiff, ne_of_mem_of_not_mem, not_disjoint_iff_nonempty_inter
-/
theorem disjoint_cylinder_of_longestPrefix_lt {s : Set (forall n, E n)} (hs : IsClosed s) {x : forall n, E n}
    (hx : x ∉ s) {n : Nat} (hn : longestPrefix x s < n) : Disjoint s (cylinder x n) := by
  contrapose! hn
  rcases not_disjoint_iff_nonempty_inter.1 hn with ⟨y, ys, hy⟩
  apply le_trans _ (firstDiff_le_longestPrefix hs hx ys)
  apply (mem_cylinder_iff_le_firstDiff (ne_of_mem_of_not_mem ys hx).symm _).1
  rwa [mem_cylinder_comm]

/--
theorem `cylinder_longestPrefix_eq_of_longestPrefix_lt_firstDiff` / 定理 `cylinder_longestPrefix_eq_of_longestPrefix_lt_firstDiff`

English:
theorem cylinder_longestPrefix_eq_of_longestPrefix_lt_firstDiff
  statement: {x y : forall n, E n}
  proof: by
  have l_eq : longestPrefix y s = longestPrefix x s := by
    rcases lt_trichotomy (longestPrefix y s) (longestPrefix x s) with (L | L | L)
    · have Ax : (s inter cylinder x (longestPrefix x s)).Nonempty :=
        inter_cylinder_longestPrefix_nonempty hs hne x
      have Z := disjoint_cylinder

中文:
定理 cylinder_longestPrefix_eq_of_longestPrefix_lt_firstDiff
  结论: {x y : 对任意 n, E n}
  证明: by
  have l_eq : longestPrefix y s = longestPrefix x s := by
    rcases lt_trichotomy (longestPrefix y s) (longestPrefix x s) with (L | L | L)
    · have Ax : (s inter cylinder x (longestPrefix x s)).Nonempty :=
        inter_cylinder_longestPrefix_nonempty hs hne x
      have Z := disjoint_cylinder

Depends on / 依赖: Ax.not_disjoint, H.le, Nonempty, cylinder, cylinder_eq_cylinder_of_le_firstDiff, disjoint_cylinder_of_longestPrefix_lt, firstDiff_comm, inter_cy, inter_cylinder_longestPrefix_nonempty, l_eq, longestPrefix, lt_trichotomy, not_disjoint
-/
theorem cylinder_longestPrefix_eq_of_longestPrefix_lt_firstDiff {x y : forall n, E n}
    {s : Set (forall n, E n)} (hs : IsClosed s) (hne : s.Nonempty)
    (H : longestPrefix x s < firstDiff x y) (xs : x ∉ s) (ys : y ∉ s) :
    cylinder x (longestPrefix x s) = cylinder y (longestPrefix y s) := by
  have l_eq : longestPrefix y s = longestPrefix x s := by
    rcases lt_trichotomy (longestPrefix y s) (longestPrefix x s) with (L | L | L)
    · have Ax : (s inter cylinder x (longestPrefix x s)).Nonempty :=
        inter_cylinder_longestPrefix_nonempty hs hne x
      have Z := disjoint_cylinder_of_longestPrefix_lt hs ys L
      rw [firstDiff_comm] at H
      rw [cylinder_eq_cylinder_of_le_firstDiff _ _ H.le] at Z
      exact (Ax.not_disjoint Z).elim
    · exact L
    · have Ay : (s inter cylinder y (longestPrefix y s)).Nonempty :=
        inter_cylinder_longestPrefix_nonempty hs hne y
      have A'y : (s inter cylinder y (longestPrefix x s).succ).Nonempty :=
        Ay.mono (inter_subset_inter_right s (cylinder_anti _ L))
      have Z := disjoint_cylinder_of_longestPrefix_lt hs xs (Nat.lt_succ_self _)
      rw [cylinder_eq_cylinder_of_le_firstDiff _ _ H] at Z
      exact (A'y.not_disjoint Z).elim
  rw [l_eq]; rw [← mem_cylinder_iff_eq]
  exact cylinder_anti y H.le (mem_cylinder_firstDiff x y)

/--
theorem `exists_lipschitz_retraction_of_isClosed` / 定理 `exists_lipschitz_retraction_of_isClosed`

English:
theorem exists_lipschitz_retraction_of_isClosed
  statement: {s : Set (forall n, E n)} (hs : IsClosed s)
  proof: by
  /- The map `f` is defined as follows. For `x ∈ s`, let `f x = x`. Otherwise, consider the longest
    prefix `w` that `x` shares with an element of `s`, and let `f x = z_w` where `z_w` is an element
    of `s` starting with `w`. All the desired properties are clear, except the fact that `f` is


中文:
定理 存在_lipschitz_retraction_of_isClosed
  结论: {s : 集合 (对任意 n, E n)} (hs : 是闭集 s)
  证明: by
  /- The map `f` is defined as follows. For `x ∈ s`, let `f x = x`. Otherwise, consider the longest
    prefix `w` that `x` shares with an element of `s`, and let `f x = z_w` where `z_w` is an element
    of `s` starting with `w`. All the desired properties are clear, except the fact that `f` is

-/
theorem exists_lipschitz_retraction_of_isClosed {s : Set (forall n, E n)} (hs : IsClosed s)
    (hne : s.Nonempty) :
    exists f : (forall n, E n) -> forall n, E n, (forall x in s, f x = x) ∧ range f = s ∧ LipschitzWith 1 f := by
  /- The map `f` is defined as follows. For `x ∈ s`, let `f x = x`. Otherwise, consider the longest
    prefix `w` that `x` shares with an element of `s`, and let `f x = z_w` where `z_w` is an element
    of `s` starting with `w`. All the desired properties are clear, except the fact that `f` is
    `1`-Lipschitz: if two points `x, y` belong to a common cylinder of length `n`, one should show
    that their images also belong to a common cylinder of length `n`. This is a case analysis:
    * if both `x, y ∈ s`, then this is clear.
    * if `x ∈ s` but `y ∉ s`, then the longest prefix `w` of `y` shared by an element of `s` is of
    length at least `n` (because of `x`), and then `f y` starts with `w` and therefore stays in the
    same length `n` cylinder.
    * if `x ∉ s`, `y ∉ s`, let `w` be the longest prefix of `x` shared by an element of `s`. If its
    length is `< n`, then it is also the longest prefix of `y`, and we get `f x = f y = z_w`.
    Otherwise, `f x` remains in the same `n`-cylinder as `x`. Similarly for `y`. Finally, `f x` and
    `f y` are again in the same `n`-cylinder, as desired. -/
  classical
  set f := fun x => if x in s then x else (inter_cylinder_longestPrefix_nonempty hs hne x).some
  have fs : forall x in s, f x = x := fun x xs => by simp [f, xs]
  refine ⟨f, fs, ?_, ?_⟩
  -- check that the range of `f` is `s`.
  · apply Subset.antisymm
    · rintro x ⟨y, rfl⟩
      by_cases hy : y in s
      · rwa [fs y hy]
      simpa [f, if_neg hy] using! (inter_cylinder_longestPrefix_nonempty hs hne y).choose_spec.1
    · intro x hx
      rw [← fs x hx]
      exact mem_range_self _
  -- check that `f` is `1`-Lipschitz, by a case analysis.
  · refine LipschitzWith.mk_one fun x y => ?_
    -- exclude the trivial cases where `x = y`, or `f x = f y`.
    rcases eq_or_ne x y with (rfl | hxy)
    · simp
    rcases eq_or_ne (f x) (f y) with (h' | hfxfy)
    · simp [h']
    have I2 : cylinder x (firstDiff x y) = cylinder y (firstDiff x y) := by
      rw [← mem_cylinder_iff_eq]
      apply mem_cylinder_firstDiff
    suffices firstDiff x y <= firstDiff (f x) (f y) by
      simpa [dist_eq_of_ne hxy, dist_eq_of_ne hfxfy]
    -- case where `x ∈ s`
    by_cases xs : x in s
    · rw [fs x xs] at hfxfy ⊢
      -- case where `y ∈ s`, trivial
      by_cases ys : y in s
      · rw [fs y ys]
      -- case where `y ∉ s`
      have A : (s inter cylinder y (longestPrefix y s)).Nonempty :=
        inter_cylinder_longestPrefix_nonempty hs hne y
      have fy : f y = A.some := by simp_rw [f, if_neg ys]
      have I : cylinder A.some (firstDiff x y) = cylinder y (firstDiff x y) := by
        rw [← mem_cylinder_iff_eq]; rw [firstDiff_comm]
        apply cylinder_anti y _ A.some_mem.2
        exact firstDiff_le_longestPrefix hs ys xs
      rwa [← fy, ← I2, ← mem_cylinder_iff_eq, mem_cylinder_iff_le_firstDiff hfxfy.symm,
        firstDiff_comm _ x] at I
    -- case where `x ∉ s`
    · by_cases ys : y in s
      -- case where `y ∈ s` (similar to the above)
      · have A : (s inter cylinder x (longestPrefix x s)).Nonempty :=
          inter_cylinder_longestPrefix_nonempty hs hne x
        have fx : f x = A.some := by simp_rw [f, if_neg xs]
        have I : cylinder A.some (firstDiff x y) = cylinder x (firstDiff x y) := by
          rw [← mem_cylinder_iff_eq]
          apply cylinder_anti x _ A.some_mem.2
          apply firstDiff_le_longestPrefix hs xs ys
        rw [fs y ys] at hfxfy ⊢
        rwa [← fx, I2, ← mem_cylinder_iff_eq, mem_cylinder_iff_le_firstDiff hfxfy] at I
      -- case where `y ∉ s`
      · have Ax : (s inter cylinder x (longestPrefix x s)).Nonempty :=
          inter_cylinder_longestPrefix_nonempty hs hne x
        have fx : f x = Ax.some := by simp_rw [f, if_neg xs]
        have Ay : (s inter cylinder y (longestPrefix y s)).Nonempty :=
          inter_cylinder_longestPrefix_nonempty hs hne y
        have fy : f y = Ay.some := by simp_rw [f, if_neg ys]
        -- case where the common prefix to `x` and `s`, or `y` and `s`, is shorter than the
        -- common part to `x` and `y` -- then `f x = f y`.
        by_cases! H : longestPrefix x s < firstDiff x y ∨ longestPrefix y s < firstDiff x y
        · have : cylinder x (longestPrefix x s) = cylinder y (longestPrefix y s) := by
            rcases H with H | H
            · exact cylinder_longestPrefix_eq_of_longestPrefix_lt_firstDiff hs hne H xs ys
            · symm
              rw [firstDiff_comm] at H
              exact cylinder_longestPrefix_eq_of_longestPrefix_lt_firstDiff hs hne H ys xs
          rw [fx]; rw [fy] at hfxfy
          apply (hfxfy _).elim
          congr
        -- case where the common prefix to `x` and `s` is long, as well as the common prefix to
        -- `y` and `s`. Then all points remain in the same cylinders.
        · have I1 : cylinder Ax.some (firstDiff x y) = cylinder x (firstDiff x y) := by
            rw [← mem_cylinder_iff_eq]
            exact cylinder_anti x H.1 Ax.some_mem.2
          have I3 : cylinder y (firstDiff x y) = cylinder Ay.some (firstDiff x y) := by
            rw [eq_comm]; rw [← mem_cylinder_iff_eq]
            exact cylinder_anti y H.2 Ay.some_mem.2
          have : cylinder Ax.some (firstDiff x y) = cylinder Ay.some (firstDiff x y) := by
            rw [I1]; rw [I2]; rw [I3]
          rw [← fx]; rw [← fy]; rw [← mem_cylinder_iff_eq]; rw [mem_cylinder_iff_le_firstDiff hfxfy] at this
          exact this

/--
theorem `exists_retraction_of_isClosed` / 定理 `exists_retraction_of_isClosed`

English:
theorem exists_retraction_of_isClosed
  given: {s : Set (forall n, E n)} (hs : IsClosed s) (hne : s.Nonempty)
  proof: by
  rcases exists_lipschitz_retraction_of_isClosed hs hne with ⟨f, fs, frange, hf⟩
  exact ⟨f, fs, frange, hf.continuous⟩

中文:
定理 存在_retraction_of_isClosed
  条件: {s : 集合 (对任意 n, E n)} (hs : 是闭集 s) (hne : s.非空)
  证明: by
  rcases exists_lipschitz_retraction_of_isClosed hs hne with ⟨f, fs, frange, hf⟩
  exact ⟨f, fs, frange, hf.continuous⟩

Depends on / 依赖: continuous, exists_lipschitz_retraction_of_isClosed, frange, hf.continuous
-/
theorem exists_retraction_of_isClosed {s : Set (forall n, E n)} (hs : IsClosed s) (hne : s.Nonempty) :
    exists f : (forall n, E n) -> forall n, E n, (forall x in s, f x = x) ∧ range f = s ∧ Continuous f := by
  rcases exists_lipschitz_retraction_of_isClosed hs hne with ⟨f, fs, frange, hf⟩
  exact ⟨f, fs, frange, hf.continuous⟩

/--
theorem `exists_retraction_subtype_of_isClosed` / 定理 `exists_retraction_subtype_of_isClosed`

English:
theorem exists_retraction_subtype_of_isClosed
  statement: {s : Set (forall n, E n)} (hs : IsClosed s)
  proof: by
  obtain ⟨f, fs, rfl, f_cont⟩ :
    exists f : (forall n, E n) -> forall n, E n, (forall x in s, f x = x) ∧ range f = s ∧ Continuous f :=
    exists_retraction_of_isClosed hs hne
have A : forall x : range f, rangeFactorization f x = x := fun x => Subtype.ext fs x x.2
  exact ⟨rangeFactorization f

中文:
定理 存在_retraction_subtype_of_isClosed
  结论: {s : 集合 (对任意 n, E n)} (hs : 是闭集 s)
  证明: by
  obtain ⟨f, fs, rfl, f_cont⟩ :
    exists f : (forall n, E n) -> forall n, E n, (forall x in s, f x = x) ∧ range f = s ∧ Continuous f :=
    exists_retraction_of_isClosed hs hne
have A : forall x : range f, rangeFactorization f x = x := fun x => Subtype.ext fs x x.2
  exact ⟨rangeFactorization f

Depends on / 依赖: Continuous, Subtype, Subtype.ext, exists_retraction_of_isClosed, f_cont, f_cont.subtype_mk, rangeFactorization, subtype_mk
-/
theorem exists_retraction_subtype_of_isClosed {s : Set (forall n, E n)} (hs : IsClosed s)
    (hne : s.Nonempty) :
    exists f : (forall n, E n) -> s, (forall x : s, f x = x) ∧ Surjective f ∧ Continuous f := by
  obtain ⟨f, fs, rfl, f_cont⟩ :
    exists f : (forall n, E n) -> forall n, E n, (forall x in s, f x = x) ∧ range f = s ∧ Continuous f :=
    exists_retraction_of_isClosed hs hne
have A : forall x : range f, rangeFactorization f x = x := fun x => Subtype.ext fs x x.2
  exact ⟨rangeFactorization f, A, fun x => ⟨x, A x⟩, f_cont.subtype_mk _⟩

end PiNat

open PiNat

/--
theorem `exists_nat_nat_continuous_surjective_of_completeSpace` / 定理 `exists_nat_nat_continuous_surjective_of_completeSpace`

English:
theorem exists_nat_nat_continuous_surjective_of_completeSpace
  statement: (α : Type*) [MetricSpace α]
  proof: by
  /- First, we define a surjective map from a closed subset `s` of `ℕ → ℕ`. Then, we compose
    this map with a retraction of `ℕ → ℕ` onto `s` to obtain the desired map.
    Let us consider a dense sequence `u` in `α`. Then `s` is the set of sequences `xₙ` such that the
    balls `closedBall (u 

中文:
定理 存在_nat_nat_continuous_surjective_of_completeSpace
  结论: (α : 类型) [度量空间 α]
  证明: by
  /- First, we define a surjective map from a closed subset `s` of `ℕ → ℕ`. Then, we compose
    this map with a retraction of `ℕ → ℕ` onto `s` to obtain the desired map.
    Let us consider a dense sequence `u` in `α`. Then `s` is the set of sequences `xₙ` such that the
    balls `closedBall (u 
-/
theorem exists_nat_nat_continuous_surjective_of_completeSpace (α : Type*) [MetricSpace α]
    [CompleteSpace α] [SecondCountableTopology α] [Nonempty α] :
    exists f : (Nat -> Nat) -> α, Continuous f ∧ Surjective f := by
  /- First, we define a surjective map from a closed subset `s` of `ℕ → ℕ`. Then, we compose
    this map with a retraction of `ℕ → ℕ` onto `s` to obtain the desired map.
    Let us consider a dense sequence `u` in `α`. Then `s` is the set of sequences `xₙ` such that the
    balls `closedBall (u xₙ) (1/2^n)` have a nonempty intersection. This set is closed,
    and we define `f x` there to be the unique point in the intersection.
    This function is continuous and surjective by design. -/
  let : MetricSpace (Nat -> Nat) := PiNat.metricSpaceNatNat
  have I0 : (0 : Real) < 1 / 2 := by simp
  have I1 : (1 / 2 : Real) < 1 := by norm_num
  rcases exists_dense_seq α with ⟨u, hu⟩
  let s : Set (Nat -> Nat) := { x | (⋂ n : Nat, closedBall (u (x n)) ((1 / 2) ^ n)).Nonempty }
  let g : s -> α := fun x => x.2.some
  have A : forall (x : s) (n : Nat), dist (g x) (u ((x : Nat -> Nat) n)) <= (1 / 2) ^ n := fun x n =>
    (mem_iInter.1 x.2.some_mem n :)
  have g_cont : Continuous g := by
    refine continuous_iff_continuousAt.2 fun y => ?_
    refine continuousAt_of_locally_lipschitz zero_lt_one 4 fun x hxy => ?_
    rcases eq_or_ne x y with (rfl | hne)
    · simp
    have hne' : x.1 != y.1 := Subtype.coe_injective.ne hne
    have dist' : dist x y = dist x.1 y.1 := rfl
    let n := firstDiff x.1 y.1 - 1
    have diff_pos : 0 < firstDiff x.1 y.1 := by
      by_contra! h
      apply apply_firstDiff_ne hne'
      rw [Nat.le_zero.1 h]
      apply apply_eq_of_dist_lt _ le_rfl
      rw [pow_zero]
      exact hxy
    have hn : firstDiff x.1 y.1 = n + 1 := (Nat.succ_pred_eq_of_pos diff_pos).symm
    rw [dist']; rw [dist_eq_of_ne hne']; rw [hn]
    have B : x.1 n = y.1 n := mem_cylinder_firstDiff x.1 y.1 n (Nat.pred_lt diff_pos.ne')
    calc
      dist (g x) (g y) <= dist (g x) (u (x.1 n)) + dist (g y) (u (x.1 n)) :=
        dist_triangle_right _ _ _
      _ = dist (g x) (u (x.1 n)) + dist (g y) (u (y.1 n)) := by rw [← B]
      _ <= (1 / 2) ^ n + (1 / 2) ^ n := add_le_add (A x n) (A y n)
      _ = 4 * (1 / 2) ^ (n + 1) := by ring
  have g_surj : Surjective g := fun y => by
    have : forall n : Nat, exists j, y in closedBall (u j) ((1 / 2) ^ n) := fun n => by
      rcases hu.exists_dist_lt y (by simp : (0 : Real) < (1 / 2) ^ n) with ⟨j, hj⟩
      exact ⟨j, hj.le⟩
    choose x hx using this
    have I : (⋂ n : Nat, closedBall (u (x n)) ((1 / 2) ^ n)).Nonempty := ⟨y, mem_iInter.2 hx⟩
    refine ⟨⟨x, I⟩, ?_⟩
    refine dist_le_zero.1 ?_
    have J : forall n : Nat, dist (g ⟨x, I⟩) y <= (1 / 2) ^ n + (1 / 2) ^ n := fun n =>
      calc
        dist (g ⟨x, I⟩) y <= dist (g ⟨x, I⟩) (u (x n)) + dist y (u (x n)) :=
          dist_triangle_right _ _ _
        _ <= (1 / 2) ^ n + (1 / 2) ^ n := add_le_add (A ⟨x, I⟩ n) (hx n)
    have L : Tendsto (fun n : Nat => (1 / 2 : Real) ^ n + (1 / 2) ^ n) atTop (𝓝 (0 + 0)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one I0.le I1).add
        (tendsto_pow_atTop_nhds_zero_of_lt_one I0.le I1)
    rw [add_zero] at L
    exact ge_of_tendsto' L J
  have s_closed : IsClosed s := by
    refine isClosed_iff_clusterPt.mpr fun x hx => ?_
    have L : Tendsto (fun n : Nat => diam (closedBall (u (x n)) ((1 / 2) ^ n))) atTop (𝓝 0) := by
      have : Tendsto (fun n : Nat => (2 : Real) * (1 / 2) ^ n) atTop (𝓝 (2 * 0)) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one I0.le I1).const_mul _
      rw [mul_zero] at this
      exact
        squeeze_zero (fun n => diam_nonneg) (fun n => diam_closedBall (pow_nonneg I0.le _)) this
    refine nonempty_iInter_of_nonempty_biInter (fun n => isClosed_closedBall)
      (fun n => isBounded_closedBall) (fun N => ?_) L
    obtain ⟨y, hxy, ys⟩ : exists y, y in ball x ((1 / 2) ^ N) inter s :=
      clusterPt_principal_iff.1 hx _ (ball_mem_nhds x (pow_pos I0 N))
    have E :
      ⋂ (n : Nat) (H : n <= N), closedBall (u (x n)) ((1 / 2) ^ n) =
        ⋂ (n : Nat) (H : n <= N), closedBall (u (y n)) ((1 / 2) ^ n) := by
      refine iInter_congr fun n => iInter_congr fun hn => ?_
      have : x n = y n := apply_eq_of_dist_lt (mem_ball'.1 hxy) hn
      rw [this]
    rw [E]
    apply Nonempty.mono _ ys
    apply iInter_subset_iInter₂
  obtain ⟨f, -, f_surj, f_cont⟩ :
    exists f : (Nat -> Nat) -> s, (forall x : s, f x = x) ∧ Surjective f ∧ Continuous f := by
    apply exists_retraction_subtype_of_isClosed s_closed
    simpa only [nonempty_coe_sort] using g_surj.nonempty
  exact ⟨g ∘ f, g_cont.comp f_cont, g_surj.comp f_surj⟩

open Encodable ENNReal
namespace PiCountable

/-!
### Products of (possibly non-discrete) metric spaces
-/

variable {ι : Type*} [Encodable ι] {F : ι -> Type*}

section EDist
variable [forall i, EDist (F i)] {x y : forall i, F i} {i : ι} {r : Real>=0∞}

/-- Given a countable family of extended metric spaces,
one may put an extended distance on their product `Π i, E i`.

It is highly non-canonical, though, and therefore not registered as a global instance.
The distance we use here is `edist x y = ∑' i, min (1/2)^(encode i) (edist (x i) (y i))`. -/
@[instance_reducible]
/--
Definition of `edist` / `edist` 的定义

English:
definition edist
  signature: : EDist (forall i, F i) where
  body: ∑' i, min (2⁻¹ ^ encode i) (edist (x i) (y i))

中文:
定义 edist
  签名: : EDist (对任意 i, F i) where
  定义体: ∑' i, min (2⁻¹ ^ encode i) (edist (x i) (y i))
-/
protected def edist : EDist (forall i, F i) where
  edist x y := ∑' i, min (2⁻¹ ^ encode i) (edist (x i) (y i))

attribute [scoped instance] PiCountable.edist

/--
lemma `edist_eq_tsum` / 引理 `edist_eq_tsum`

English:
lemma edist_eq_tsum
  given: (x y : forall i, F i)
  proof: rfl

中文:
引理 edist_eq_tsum
  条件: (x y : 对任意 i, F i)
  证明: rfl
-/
lemma edist_eq_tsum (x y : forall i, F i) :
    edist x y = ∑' i, min (2⁻¹ ^ encode i) (edist (x i) (y i)) := rfl

/--
lemma `min_edist_le_edist_pi` / 引理 `min_edist_le_edist_pi`

English:
lemma min_edist_le_edist_pi
  given: (x y : forall i, F i) (i : ι)
  proof: ENNReal.le_tsum _

中文:
引理 min_edist_le_edist_pi
  条件: (x y : 对任意 i, F i) (i : ι)
  证明: ENNReal.le_tsum _

Depends on / 依赖: ENNReal, ENNReal.le_tsum, le_tsum
-/
lemma min_edist_le_edist_pi (x y : forall i, F i) (i : ι) :
    min (2⁻¹ ^ encode i) (edist (x i) (y i)) <= edist x y := ENNReal.le_tsum _

/--
lemma `edist_le_two` / 引理 `edist_le_two`

English:
lemma edist_le_two
  statement: edist x y <= 2
  proof: (ENNReal.tsum_geometric_two_encode_le_two).trans' by
    rw [edist_eq_tsum]; gcongr; exact min_le_left ..

中文:
引理 edist_le_two
  结论: edist x y <= 2
  证明: (ENNReal.tsum_geometric_two_encode_le_two).trans' by
    rw [edist_eq_tsum]; gcongr; exact min_le_left ..

Depends on / 依赖: ENNReal, ENNReal.tsum_geometric_two_encode_le_two, edist_eq_tsum, min_le_left, tsum_geometric_two_encode_le_two
-/
lemma edist_le_two : edist x y <= 2 :=
(ENNReal.tsum_geometric_two_encode_le_two).trans' by
    rw [edist_eq_tsum]; gcongr; exact min_le_left ..

/--
lemma `edist_lt_top` / 引理 `edist_lt_top`

English:
lemma edist_lt_top
  statement: edist x y < ∞
  proof: edist_le_two.trans_lt (by simp)

中文:
引理 edist_lt_top
  结论: edist x y < ∞
  证明: edist_le_two.trans_lt (by simp)

Depends on / 依赖: edist_le_two, edist_le_two.trans_lt, trans_lt
-/
lemma edist_lt_top : edist x y < ∞ := edist_le_two.trans_lt (by simp)

/--
lemma `edist_le_edist_pi_of_edist_lt` / 引理 `edist_le_edist_pi_of_edist_lt`

English:
lemma edist_le_edist_pi_of_edist_lt
  given: (h : edist x y < 2⁻¹ ^ encode i)
  proof: by
  simpa only [not_le.2 h, false_or] using min_le_iff.1 (min_edist_le_edist_pi x y i)

中文:
引理 edist_le_edist_pi_of_edist_lt
  条件: (h : edist x y < 2⁻¹ ^ encode i)
  证明: by
  simpa only [not_le.2 h, false_or] using min_le_iff.1 (min_edist_le_edist_pi x y i)

Depends on / 依赖: false_or, min_edist_le_edist_pi, min_le_iff, not_le
-/
lemma edist_le_edist_pi_of_edist_lt (h : edist x y < 2⁻¹ ^ encode i) :
    edist (x i) (y i) <= edist x y := by
  simpa only [not_le.2 h, false_or] using min_le_iff.1 (min_edist_le_edist_pi x y i)

end EDist

attribute [scoped instance] PiCountable.edist

section PseudoEMetricSpace
variable [forall i, PseudoEMetricSpace (F i)]

/-- Given a countable family of extended pseudometric spaces,
one may put an extended distance on their product `Π i, E i`.

It is highly non-canonical, though, and therefore not registered as a global instance.
The distance we use here is `edist x y = ∑' i, min (1/2)^(encode i) (edist (x i) (y i))`. -/
@[instance_reducible]
/--
Definition of `pseudoEMetricSpace` / `pseudoEMetricSpace` 的定义

English:
definition pseudoEMetricSpace
  signature: : PseudoEMetricSpace (forall i, F i) where
  body: by simp [edist_eq_tsum]
  edist_comm x y := by simp [edist_eq_tsum, edist_comm]
  edist_triangle x y z := calc
        ∑' i, min (2⁻¹ ^ encode i) (edist (x i) (z i))
    _ <= ∑' i, (min (2⁻¹ ^ encode i) (edist (x i) (y i)) +
         min (2⁻¹ ^ encode i) (edist (y i) (z i))) := by
      gcongr with 

中文:
定义 pseudoEMetricSpace
  签名: : PseudoEMetric空间 (对任意 i, F i) where
  定义体: by simp [edist_eq_tsum]
  edist_comm x y := by simp [edist_eq_tsum, edist_comm]
  edist_triangle x y z := calc
        ∑' i, min (2⁻¹ ^ encode i) (edist (x i) (z i))
    _ <= ∑' i, (min (2⁻¹ ^ encode i) (edist (x i) (y i)) +
         min (2⁻¹ ^ encode i) (edist (y i) (z i))) := by
      gcongr with 
-/
protected def pseudoEMetricSpace : PseudoEMetricSpace (forall i, F i) where
  edist_self x := by simp [edist_eq_tsum]
  edist_comm x y := by simp [edist_eq_tsum, edist_comm]
  edist_triangle x y z := calc
        ∑' i, min (2⁻¹ ^ encode i) (edist (x i) (z i))
    _ <= ∑' i, (min (2⁻¹ ^ encode i) (edist (x i) (y i)) +
         min (2⁻¹ ^ encode i) (edist (y i) (z i))) := by
      gcongr with n; grw [edist_triangle _ (y n), min_add_distrib, min_le_right]
    _ = _ := ENNReal.tsum_add ..
  toUniformSpace := Pi.uniformSpace _
  uniformity_edist := by
    simp only [Pi.uniformity, comap_iInf, gt_iff_lt, preimage_ofPred_eq, comap_principal,
      PseudoEMetricSpace.uniformity_edist, le_antisymm_iff, le_iInf_iff, le_principal_iff]
    constructor
    · intro ε hε
      obtain ⟨K, hK⟩ : exists K : Finset ι, ∑' i : {j // j ∉ K}, 2⁻¹ ^ encode (i : ι) < ε / 2 :=
        ((tendsto_order.1 <| ENNReal.tendsto_tsum_compl_atTop_zero
          (tsum_geometric_encode_lt_top ENNReal.one_half_lt_one).ne).2 _
 by simpa using hε.ne').exists
      obtain ⟨δ, δpos, hδ⟩ : exists δ, 0 < δ ∧ δ * K.card < ε / 2 :=
        ENNReal.exists_pos_mul_lt (by simp) (by simpa using hε.ne')
      apply @mem_iInf_of_iInter _ _ _ _ _ K.finite_toSet fun i =>
          {p : (forall i : ι, F i) × forall i : ι, F i | edist (p.fst i) (p.snd i) < δ}
      · rintro ⟨i, hi⟩
        refine mem_iInf_of_mem δ (mem_iInf_of_mem δpos ?_)
        simp only [mem_principal, Subset.rfl]
      · rintro ⟨x, y⟩ hxy
        simp only [mem_iInter, mem_ofPred_eq, SetCoe.forall, Finset.mem_coe] at hxy
        calc
          edist x y = ∑' i : ι, min (2⁻¹ ^ encode i) (edist (x i) (y i)) := rfl
          _ = ∑ i in K, min (2⁻¹ ^ encode i) (edist (x i) (y i)) +
                ∑' i : ↑(K : Set ι)ᶜ, min (2⁻¹ ^ encode (i : ι)) (edist (x i) (y i)) :=
            (ENNReal.sum_add_tsum_compl ..).symm
          _ <= ∑ i in K, edist (x i) (y i) + ∑' i : ↑(K : Set ι)ᶜ, 2⁻¹ ^ encode (i : ι) := by
            gcongr
            · apply min_le_right
            · apply min_le_left
          _ < ∑ _i in K, δ + ε / 2 := by
            refine ENNReal.add_lt_add_of_le_of_lt (by simpa using fun i hi => (hxy i hi).ne_top) ?_
              hK
            gcongr with i hi
            exact (hxy i hi).le
          _ <= ε / 2 + ε / 2 := by gcongr; simpa [mul_comm] using hδ.le
          _ = ε := ENNReal.add_halves _
    · intro i ε hε₀
      have : (0 : Real>=0∞) < 2⁻¹ ^ encode i := ENNReal.pow_pos (by norm_num) _
refine mem_iInf_of_mem (min (2⁻¹ ^ encode i) ε) mem_iInf_of_mem (by positivity) ?_
      simp only [and_imp, Prod.forall, ofPred_subset_ofPred, lt_min_iff, mem_principal]
      intro x y hn
      exact (edist_le_edist_pi_of_edist_lt hn).trans_lt

end PseudoEMetricSpace

attribute [scoped instance] PiCountable.pseudoEMetricSpace

section EMetricSpace
variable [forall i, EMetricSpace (F i)]

/-- Given a countable family of extended metric spaces,
one may put an extended distance on their product `Π i, E i`.

It is highly non-canonical, though, and therefore not registered as a global instance.
The distance we use here is `edist x y = ∑' i, min (1/2)^(encode i) (edist (x i) (y i))`. -/
@[instance_reducible]
/--
Definition of `emetricSpace` / `emetricSpace` 的定义

English:
definition emetricSpace
  signature: : EMetricSpace (forall i, F i) where
  body: by simp [edist_eq_tsum, funext_iff]

中文:
定义 emetricSpace
  签名: : 广义度量空间 (对任意 i, F i) where
  定义体: by simp [edist_eq_tsum, funext_iff]
-/
protected def emetricSpace : EMetricSpace (forall i, F i) where
  eq_of_edist_eq_zero := by simp [edist_eq_tsum, funext_iff]

end EMetricSpace

attribute [scoped instance] PiCountable.emetricSpace

section PseudoMetricSpace
variable [forall i, PseudoMetricSpace (F i)] {x y : forall i, F i} {i : ι}


/-- Given a countable family of metric spaces, one may put a distance on their product `Π i, E i`.

It is highly non-canonical, though, and therefore not registered as a global instance.
The distance we use here is `dist x y = ∑' i, min (1/2)^(encode i) (dist (x i) (y i))`. -/
@[instance_reducible]
/--
Definition of `dist` / `dist` 的定义

English:
definition dist
  signature: : Dist (forall i, F i) where
  body: ∑' i, min (2⁻¹ ^ encode i) (dist (x i) (y i))

中文:
定义 dist
  签名: : Dist (对任意 i, F i) where
  定义体: ∑' i, min (2⁻¹ ^ encode i) (dist (x i) (y i))
-/
protected def dist : Dist (forall i, F i) where
  dist x y := ∑' i, min (2⁻¹ ^ encode i) (dist (x i) (y i))

attribute [scoped instance] PiCountable.dist

/--
lemma `dist_eq_tsum` / 引理 `dist_eq_tsum`

English:
lemma dist_eq_tsum
  given: (x y : forall i, F i)
  statement: dist x y = ∑' i, min (2⁻¹ ^ encode i) (dist (x i) (y i))
  proof: rfl

中文:
引理 dist_eq_tsum
  条件: (x y : 对任意 i, F i)
  结论: dist x y = ∑' i, 最小值 (2⁻¹ ^ encode i) (dist (x i) (y i))
  证明: rfl
-/
lemma dist_eq_tsum (x y : forall i, F i) : dist x y = ∑' i, min (2⁻¹ ^ encode i) (dist (x i) (y i)) :=
  rfl

/--
lemma `dist_summable` / 引理 `dist_summable`

English:
lemma dist_summable
  given: (x y : forall i, F i)
  proof: by
refine .of_nonneg_of_le (fun i => ?_) (fun i => min_le_left _ _) by
    simpa [one_div] using summable_geometric_two_encode
  exact le_min (by positivity) dist_nonneg

中文:
引理 dist_summable
  条件: (x y : 对任意 i, F i)
  证明: by
refine .of_nonneg_of_le (fun i => ?_) (fun i => min_le_left _ _) by
    simpa [one_div] using summable_geometric_two_encode
  exact le_min (by positivity) dist_nonneg

Depends on / 依赖: dist_nonneg, le_min, min_le_left, of_nonneg_of_le, one_div, summable_geometric_two_encode
-/
lemma dist_summable (x y : forall i, F i) :
    Summable fun i => min (2⁻¹ ^ encode i) (dist (x i) (y i)) := by
refine .of_nonneg_of_le (fun i => ?_) (fun i => min_le_left _ _) by
    simpa [one_div] using summable_geometric_two_encode
  exact le_min (by positivity) dist_nonneg

/--
lemma `min_dist_le_dist_pi` / 引理 `min_dist_le_dist_pi`

English:
lemma min_dist_le_dist_pi
  given: (x y : forall i, F i) (i : ι)
  proof: (dist_summable x y).le_tsum i fun j _ => le_min (by simp) dist_nonneg

中文:
引理 min_dist_le_dist_pi
  条件: (x y : 对任意 i, F i) (i : ι)
  证明: (dist_summable x y).le_tsum i fun j _ => le_min (by simp) dist_nonneg

Depends on / 依赖: dist_nonneg, dist_summable, le_min, le_tsum
-/
lemma min_dist_le_dist_pi (x y : forall i, F i) (i : ι) :
    min (2⁻¹ ^ encode i) (dist (x i) (y i)) <= dist x y :=
  (dist_summable x y).le_tsum i fun j _ => le_min (by simp) dist_nonneg

/--
lemma `dist_le_dist_pi_of_dist_lt` / 引理 `dist_le_dist_pi_of_dist_lt`

English:
lemma dist_le_dist_pi_of_dist_lt
  given: (h : dist x y < 2⁻¹ ^ encode i)
  statement: dist (x i) (y i) <= dist x y
  proof: by
  simpa only [not_le.2 h, false_or] using min_le_iff.1 (min_dist_le_dist_pi x y i)

中文:
引理 dist_le_dist_pi_of_dist_lt
  条件: (h : dist x y < 2⁻¹ ^ encode i)
  结论: dist (x i) (y i) <= dist x y
  证明: by
  simpa only [not_le.2 h, false_or] using min_le_iff.1 (min_dist_le_dist_pi x y i)

Depends on / 依赖: false_or, min_dist_le_dist_pi, min_le_iff, not_le
-/
lemma dist_le_dist_pi_of_dist_lt (h : dist x y < 2⁻¹ ^ encode i) : dist (x i) (y i) <= dist x y := by
  simpa only [not_le.2 h, false_or] using min_le_iff.1 (min_dist_le_dist_pi x y i)

/-- Given a countable family of metric spaces, one may put a distance on their product `Π i, E i`.

It is highly non-canonical, though, and therefore not registered as a global instance.
The distance we use here is `dist x y = ∑' i, min (1/2)^(encode i) (dist (x i) (y i))`. -/
@[instance_reducible]
/--
Definition of `pseudoMetricSpace` / `pseudoMetricSpace` 的定义

English:
definition pseudoMetricSpace
  signature: : PseudoMetricSpace (forall i, F i)
  body: PseudoEMetricSpace.toPseudoMetricSpaceOfDist dist (fun x y => by rw [dist_eq_tsum]; positivity)
  fun x y => by
    rw [edist_eq_tsum]; rw [dist_eq_tsum]; rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) (dist_summable ..)]
    congr! with a
    simp [edist, ENNReal.inv_pow, PseudoMetricSp

中文:
定义 pseudoMetricSpace
  签名: : 伪度量空间 (对任意 i, F i)
  定义体: PseudoEMetricSpace.toPseudoMetricSpaceOfDist dist (fun x y => by rw [dist_eq_tsum]; positivity)
  fun x y => by
    rw [edist_eq_tsum]; rw [dist_eq_tsum]; rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) (dist_summable ..)]
    congr! with a
    simp [edist, ENNReal.inv_pow, PseudoMetricSp
-/
protected def pseudoMetricSpace : PseudoMetricSpace (forall i, F i) :=
  PseudoEMetricSpace.toPseudoMetricSpaceOfDist dist (fun x y => by rw [dist_eq_tsum]; positivity)
  fun x y => by
    rw [edist_eq_tsum]; rw [dist_eq_tsum]; rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) (dist_summable ..)]
    congr! with a
    simp [edist, ENNReal.inv_pow, PseudoMetricSpace.edist_dist (x a) (y a)]

end PseudoMetricSpace

attribute [scoped instance] PiCountable.pseudoMetricSpace

section MetricSpace
variable [forall i, MetricSpace (F i)]
/-- Given a countable family of metric spaces, one may put a distance on their product `Π i, E i`.

It is highly non-canonical, though, and therefore not registered as a global instance.
The distance we use here is `edist x y = ∑' i, min (1/2)^(encode i) (edist (x i) (y i))`. -/
@[instance_reducible]
/--
Definition of `metricSpace` / `metricSpace` 的定义

English:
definition metricSpace
  signature: : MetricSpace (forall i, F i)
  body: EMetricSpace.toMetricSpaceOfDist dist (by simp) (by simp [edist_dist])

中文:
定义 metricSpace
  签名: : 度量空间 (对任意 i, F i)
  定义体: EMetricSpace.toMetricSpaceOfDist dist (by simp) (by simp [edist_dist])
-/
protected def metricSpace : MetricSpace (forall i, F i) :=
  EMetricSpace.toMetricSpaceOfDist dist (by simp) (by simp [edist_dist])

end MetricSpace
end PiCountable

/-! ### Embedding a countably separated space inside a space of sequences -/

namespace Metric

open scoped PiCountable

variable {ι X : Type*} {Y : ι -> Type*} {f : forall i, X -> Y i}

include f in
variable (X Y f) in
/--
Definition of `PiNatEmbed` / `PiNatEmbed` 的定义

English:
structure PiNatEmbed
  parameters: (X : Type*) (Y : ι -> Type*) (f : forall i, X -> Y i)
  axioms and operations (2):
    - toPiNat : :
    - ofPiNat : X

中文:
结构 Pi自然数Embed
  参数: (X : 类型) (Y : ι -> 类型) (f : 对任意 i, X -> Y i)
  公理与运算 (2 个):
    - toPiNat : :
    - ofPiNat : X
-/
structure PiNatEmbed (X : Type*) (Y : ι -> Type*) (f : forall i, X -> Y i) where
  /-- The map from `X` to the subset of `∀ i, Y i`. -/
  toPiNat ::
  /-- The map from the subset of `∀ i, Y i` to `X`. -/
  ofPiNat : X

namespace PiNatEmbed

/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {x y : PiNatEmbed X Y f} (hxy : x.ofPiNat = y.ofPiNat)
  statement: x = y
  proof: by
  cases x; congr!

中文:
引理 ext
  条件: {x y : Pi自然数Embed X Y f} (hxy : x.ofPi自然数 = y.ofPi自然数)
  结论: x = y
  证明: by
  cases x; congr!
-/
@[ext] lemma ext {x y : PiNatEmbed X Y f} (hxy : x.ofPiNat = y.ofPiNat) : x = y := by
  cases x; congr!

variable (X Y f) in
/-- Equivalence between `X` and its embedding into `∀ i, Y i`. -/
@[simps]
/--
Definition of `toPiNatEquiv` / `toPiNatEquiv` 的定义

English:
definition toPiNatEquiv
  signature: : X ≃ PiNatEmbed X Y f where
  body: toPiNat
  invFun := ofPiNat
  left_inv _ := rfl
  right_inv _ := rfl

中文:
定义 toPi自然数Equiv
  签名: : X ≃ Pi自然数Embed X Y f where
  定义体: toPiNat
  invFun := ofPiNat
  left_inv _ := rfl
  right_inv _ := rfl

Depends on / 依赖: toPiNat
-/
def toPiNatEquiv : X ≃ PiNatEmbed X Y f where
  toFun := toPiNat
  invFun := ofPiNat
  left_inv _ := rfl
  right_inv _ := rfl

/--
lemma `ofPiNat_inj` / 引理 `ofPiNat_inj`

English:
lemma ofPiNat_inj
  given: {x y : PiNatEmbed X Y f}
  statement: x.ofPiNat = y.ofPiNat ↔ x = y
  proof: (toPiNatEquiv X Y f).symm.injective.eq_iff

中文:
引理 ofPi自然数_inj
  条件: {x y : Pi自然数Embed X Y f}
  结论: x.ofPi自然数 = y.ofPi自然数 ↔ x = y
  证明: (toPiNatEquiv X Y f).symm.injective.eq_iff
-/
@[simp] lemma ofPiNat_inj {x y : PiNatEmbed X Y f} : x.ofPiNat = y.ofPiNat ↔ x = y :=
  (toPiNatEquiv X Y f).symm.injective.eq_iff

/--
lemma `«forall»` / 引理 `«forall»`

English:
lemma «forall»
  given: {P : PiNatEmbed X Y f -> Prop}
  statement: (forall x, P x) ↔ forall x, P (toPiNat x)
  proof: (toPiNatEquiv X Y f).symm.forall_congr_left

中文:
引理 «对任意»
  条件: {P : Pi自然数Embed X Y f -> 命题}
  结论: (对任意 x, P x) ↔ 对任意 x, P (toPi自然数 x)
  证明: (toPiNatEquiv X Y f).symm.forall_congr_left
-/
@[simp] lemma «forall» {P : PiNatEmbed X Y f -> Prop} : (forall x, P x) ↔ forall x, P (toPiNat x) :=
  (toPiNatEquiv X Y f).symm.forall_congr_left

variable (X Y f) in
/--
Definition of `embed` / `embed` 的定义

English:
definition embed
  signature: : PiNatEmbed X Y f -> forall i, Y i
  body: fun x i => f i x.ofPiNat

中文:
定义 embed
  签名: : Pi自然数Embed X Y f -> 对任意 i, Y i
  定义体: fun x i => f i x.ofPiNat

Depends on / 依赖: ofPiNat, x.ofPiNat
-/
noncomputable def embed : PiNatEmbed X Y f -> forall i, Y i := fun x i => f i x.ofPiNat

/--
lemma `embed_injective` / 引理 `embed_injective`

English:
lemma embed_injective
  given: (separating_f : Pairwise fun x y => exists i, f i x != f i y)
  proof: by
  simpa [Pairwise, not_imp_comm (a := _ = _), funext_iff, Function.Injective] using! separating_f

中文:
引理 embed_injective
  条件: (separating_f : 两两 fun x y => 存在 i, f i x != f i y)
  证明: by
  simpa [Pairwise, not_imp_comm (a := _ = _), funext_iff, Function.Injective] using! separating_f

Depends on / 依赖: Function, Function.Injective, Injective, Pairwise, funext_iff, not_imp_comm, separating_f
-/
lemma embed_injective (separating_f : Pairwise fun x y => exists i, f i x != f i y) :
    Injective (embed X Y f) := by
  simpa [Pairwise, not_imp_comm (a := _ = _), funext_iff, Function.Injective] using! separating_f

variable [Encodable ι]

section PseudoEMetricSpace
variable [forall i, PseudoEMetricSpace (Y i)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PseudoEMetricSpace (PiNatEmbed X Y f)
  body: .induced (embed X Y f) PiCountable.pseudoEMetricSpace

中文:
实例 :
  签名: PseudoEMetric空间 (Pi自然数Embed X Y f)
  定义体: .induced (embed X Y f) PiCountable.pseudoEMetricSpace

Depends on / 依赖: PiCountable, PiCountable.pseudoEMetricSpace, induced, pseudoEMetricSpace
-/
noncomputable instance : PseudoEMetricSpace (PiNatEmbed X Y f) :=
  .induced (embed X Y f) PiCountable.pseudoEMetricSpace

/--
lemma `edist_def` / 引理 `edist_def`

English:
lemma edist_def
  given: (x y : PiNatEmbed X Y f)
  proof: rfl

中文:
引理 edist_def
  条件: (x y : Pi自然数Embed X Y f)
  证明: rfl
-/
lemma edist_def (x y : PiNatEmbed X Y f) :
    edist x y = ∑' i, min (2⁻¹ ^ encode i) (edist (f i x.ofPiNat) (f i y.ofPiNat)) := rfl

/--
lemma `isometry_embed` / 引理 `isometry_embed`

English:
lemma isometry_embed
  statement: Isometry (embed X Y f)
  proof: PseudoEMetricSpace.isometry_induced _

中文:
引理 isometry_embed
  结论: 等距 (embed X Y f)
  证明: PseudoEMetricSpace.isometry_induced _

Depends on / 依赖: PseudoEMetricSpace, PseudoEMetricSpace.isometry_induced, isometry_induced
-/
lemma isometry_embed : Isometry (embed X Y f) := PseudoEMetricSpace.isometry_induced _

end PseudoEMetricSpace

section PseudoMetricSpace
variable [forall i, PseudoMetricSpace (Y i)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PseudoMetricSpace (PiNatEmbed X Y f)
  body: .induced (embed X Y f) PiCountable.pseudoMetricSpace

中文:
实例 :
  签名: 伪度量空间 (Pi自然数Embed X Y f)
  定义体: .induced (embed X Y f) PiCountable.pseudoMetricSpace

Depends on / 依赖: PiCountable, PiCountable.pseudoMetricSpace, induced, pseudoMetricSpace
-/
noncomputable instance : PseudoMetricSpace (PiNatEmbed X Y f) :=
  .induced (embed X Y f) PiCountable.pseudoMetricSpace

/--
lemma `dist_def` / 引理 `dist_def`

English:
lemma dist_def
  given: (x y : PiNatEmbed X Y f)
  proof: rfl

中文:
引理 dist_def
  条件: (x y : Pi自然数Embed X Y f)
  证明: rfl
-/
lemma dist_def (x y : PiNatEmbed X Y f) :
    dist x y = ∑' i, min (2⁻¹ ^ encode i) (dist (f i x.ofPiNat) (f i y.ofPiNat)) := rfl

variable [TopologicalSpace X]

/--
lemma `continuous_toPiNat` / 引理 `continuous_toPiNat`

English:
lemma continuous_toPiNat
  given: (continuous_f : forall i, Continuous (f i))
  proof: by
  rw [continuous_iff_continuous_dist]
  simp only [dist_def]
apply continuous_tsum (by fun_prop) summable_geometric_two_encode by simp [abs_of_nonneg]

中文:
引理 continuous_toPi自然数
  条件: (continuous_f : 对任意 i, 连续 (f i))
  证明: by
  rw [continuous_iff_continuous_dist]
  simp only [dist_def]
apply continuous_tsum (by fun_prop) summable_geometric_two_encode by simp [abs_of_nonneg]

Depends on / 依赖: abs_of_nonneg, continuous_iff_continuous_dist, continuous_tsum, dist_def, fun_prop, summable_geometric_two_encode
-/
lemma continuous_toPiNat (continuous_f : forall i, Continuous (f i)) :
    Continuous (toPiNat : X -> PiNatEmbed X Y f) := by
  rw [continuous_iff_continuous_dist]
  simp only [dist_def]
apply continuous_tsum (by fun_prop) summable_geometric_two_encode by simp [abs_of_nonneg]

end PseudoMetricSpace

section EMetricSpace
variable [forall i, EMetricSpace (Y i)]

/--
Definition of `emetricSpace` / `emetricSpace` 的定义

English:
abbreviation emetricSpace
  signature: (separating_f : Pairwise fun x y => exists i, f i x != f i y)
  body: .induced (embed X Y f) (embed_injective separating_f) PiCountable.emetricSpace

中文:
缩写 emetricSpace
  签名: (separating_f : 两两 fun x y => 存在 i, f i x != f i y)
  定义体: .induced (embed X Y f) (embed_injective separating_f) PiCountable.emetricSpace

Depends on / 依赖: PiCountable, PiCountable.emetricSpace, embed_injective, emetricSpace, induced, separating_f
-/
noncomputable abbrev emetricSpace (separating_f : Pairwise fun x y => exists i, f i x != f i y) :
    EMetricSpace (PiNatEmbed X Y f) :=
  .induced (embed X Y f) (embed_injective separating_f) PiCountable.emetricSpace

/--
lemma `isUniformEmbedding_embed` / 引理 `isUniformEmbedding_embed`

English:
lemma isUniformEmbedding_embed
  given: (separating_f : Pairwise fun x y => exists i, f i x != f i y)
  proof: let := emetricSpace separating_f; isometry_embed.isUniformEmbedding

中文:
引理 isUniformEmbedding_embed
  条件: (separating_f : 两两 fun x y => 存在 i, f i x != f i y)
  证明: let := emetricSpace separating_f; isometry_embed.isUniformEmbedding

Depends on / 依赖: emetricSpace, isUniformEmbedding, isometry_embed, isometry_embed.isUniformEmbedding, separating_f
-/
lemma isUniformEmbedding_embed (separating_f : Pairwise fun x y => exists i, f i x != f i y) :
    IsUniformEmbedding (embed X Y f) :=
  let := emetricSpace separating_f; isometry_embed.isUniformEmbedding

end EMetricSpace


section MetricSpace
variable [forall i, MetricSpace (Y i)]

/--
Definition of `metricSpace` / `metricSpace` 的定义

English:
abbreviation metricSpace
  signature: (separating_f : Pairwise fun x y => exists i, f i x != f i y)
  body: (emetricSpace separating_f).toMetricSpace fun x y => by simp [edist_dist]

中文:
缩写 metricSpace
  签名: (separating_f : 两两 fun x y => 存在 i, f i x != f i y)
  定义体: (emetricSpace separating_f).toMetricSpace fun x y => by simp [edist_dist]

Depends on / 依赖: edist_dist, emetricSpace, separating_f, toMetricSpace
-/
noncomputable abbrev metricSpace (separating_f : Pairwise fun x y => exists i, f i x != f i y) :
    MetricSpace (PiNatEmbed X Y f) :=
  (emetricSpace separating_f).toMetricSpace fun x y => by simp [edist_dist]

section CompactSpace
variable [TopologicalSpace X] [CompactSpace X]

/--
lemma `isHomeomorph_toPiNat` / 引理 `isHomeomorph_toPiNat`

English:
lemma isHomeomorph_toPiNat
  statement: (continuous_f : forall i, Continuous (f i))
  proof: by
  let := emetricSpace separating_f
  rw [isHomeomorph_iff_continuous_bijective]
  exact ⟨continuous_toPiNat continuous_f, (toPiNatEquiv X Y f).bijective⟩

中文:
引理 isHomeomorph_toPi自然数
  结论: (continuous_f : 对任意 i, 连续 (f i))
  证明: by
  let := emetricSpace separating_f
  rw [isHomeomorph_iff_continuous_bijective]
  exact ⟨continuous_toPiNat continuous_f, (toPiNatEquiv X Y f).bijective⟩

Depends on / 依赖: bijective, continuous_f, continuous_toPiNat, emetricSpace, isHomeomorph_iff_continuous_bijective, separating_f, toPiNatEquiv
-/
lemma isHomeomorph_toPiNat (continuous_f : forall i, Continuous (f i))
    (separating_f : Pairwise fun x y => exists i, f i x != f i y) :
    IsHomeomorph (toPiNat : X -> PiNatEmbed X Y f) := by
  let := emetricSpace separating_f
  rw [isHomeomorph_iff_continuous_bijective]
  exact ⟨continuous_toPiNat continuous_f, (toPiNatEquiv X Y f).bijective⟩

variable (X Y f) in
/-- Homeomorphism between `X` and its embedding into `∀ i, Y i` induced by a separating family of
continuous functions `f i : X → Y i`. -/
@[simps!]
/--
Definition of `toPiNatHomeo` / `toPiNatHomeo` 的定义

English:
definition toPiNatHomeo
  signature: (continuous_f : forall i, Continuous (f i))
  body: (toPiNatEquiv X Y f).toHomeomorphOfIsInducing
    (isHomeomorph_toPiNat continuous_f separating_f).isInducing

中文:
定义 toPi自然数Homeo
  签名: (continuous_f : 对任意 i, 连续 (f i))
  定义体: (toPiNatEquiv X Y f).toHomeomorphOfIsInducing
    (isHomeomorph_toPiNat continuous_f separating_f).isInducing

Depends on / 依赖: continuous_f, isHomeomorph_toPiNat, isInducing, separating_f, toHomeomorphOfIsInducing, toPiNatEquiv
-/
noncomputable def toPiNatHomeo (continuous_f : forall i, Continuous (f i))
    (separating_f : Pairwise fun x y => exists i, f i x != f i y) :
    X ≃ₜ PiNatEmbed X Y f :=
  (toPiNatEquiv X Y f).toHomeomorphOfIsInducing
    (isHomeomorph_toPiNat continuous_f separating_f).isInducing

/--
lemma `TopologicalSpace.MetrizableSpace.of_countable_separating` / 引理 `TopologicalSpace.MetrizableSpace.of_countable_separating`

English:
lemma TopologicalSpace.MetrizableSpace.of_countable_separating
  statement: (f : forall i, X -> Y i)
  proof: letI := Metric.PiNatEmbed.metricSpace separating_f
  (Metric.PiNatEmbed.toPiNatHomeo X Y f continuous_f separating_f).isEmbedding.metrizableSpace

中文:
引理 拓扑空间.Metrizable空间.of_countable_separating
  结论: (f : 对任意 i, X -> Y i)
  证明: letI := Metric.PiNatEmbed.metricSpace separating_f
  (Metric.PiNatEmbed.toPiNatHomeo X Y f continuous_f separating_f).isEmbedding.metrizableSpace

Depends on / 依赖: Metric, Metric.PiNatEmbed.metricSpace, Metric.PiNatEmbed.toPiNatHomeo, PiNatEmbed, continuous_f, isEmbedding, isEmbedding.metrizableSpace, metricSpace, metrizableSpace, separating_f, toPiNatHomeo
-/
lemma TopologicalSpace.MetrizableSpace.of_countable_separating (f : forall i, X -> Y i)
    (continuous_f : forall i, Continuous (f i)) (separating_f : Pairwise fun x y => exists i, f i x != f i y) :
    MetrizableSpace X :=
  letI := Metric.PiNatEmbed.metricSpace separating_f
  (Metric.PiNatEmbed.toPiNatHomeo X Y f continuous_f separating_f).isEmbedding.metrizableSpace

end CompactSpace

open TopologicalSpace Filter unitInterval

variable [MetricSpace X] [SeparableSpace X]

variable (X) in
/--
Definition of `distDenseSeq` / `distDenseSeq` 的定义

English:
abbreviation distDenseSeq
  signature: (n : Nat) (x : X)
  body: have : Nonempty X := ⟨x⟩
projIcc _ _ zero_le_one dist x (denseSeq X n)

中文:
缩写 distDenseSeq
  签名: (n : 自然数) (x : X)
  定义体: have : Nonempty X := ⟨x⟩
projIcc _ _ zero_le_one dist x (denseSeq X n)

Depends on / 依赖: Nonempty, denseSeq, projIcc, zero_le_one
-/
noncomputable abbrev distDenseSeq (n : Nat) (x : X) : I :=
  have : Nonempty X := ⟨x⟩
projIcc _ _ zero_le_one dist x (denseSeq X n)

/--
lemma `continuous_distDenseSeq` / 引理 `continuous_distDenseSeq`

English:
lemma continuous_distDenseSeq
  given: (n : Nat)
  statement: Continuous (distDenseSeq X n)
  proof: by
  cases isEmpty_or_nonempty X
  · exact continuous_of_discreteTopology
refine continuous_projIcc.comp Continuous.dist continuous_id' ?_
  convert! continuous_const (y := denseSeq X n)

中文:
引理 continuous_distDenseSeq
  条件: (n : 自然数)
  结论: 连续 (distDenseSeq X n)
  证明: by
  cases isEmpty_or_nonempty X
  · exact continuous_of_discreteTopology
refine continuous_projIcc.comp Continuous.dist continuous_id' ?_
  convert! continuous_const (y := denseSeq X n)

Depends on / 依赖: Continuous, Continuous.dist, continuous_const, continuous_id, continuous_of_discreteTopology, continuous_projIcc, continuous_projIcc.comp, convert, denseSeq, isEmpty_or_nonempty
-/
lemma continuous_distDenseSeq (n : Nat) : Continuous (distDenseSeq X n) := by
  cases isEmpty_or_nonempty X
  · exact continuous_of_discreteTopology
refine continuous_projIcc.comp Continuous.dist continuous_id' ?_
  convert! continuous_const (y := denseSeq X n)

/--
lemma `separation` / 引理 `separation`

English:
lemma separation
  given: {x : X} {C : Set X} (hxC : C in 𝓝 x)
  proof: by
  let ε : Real := min (infDist x (closure Cᶜ)) 1
  obtain hC | hC := (closure Cᶜ).eq_empty_or_nonempty
  · simp_all
  have : Nonempty X := ⟨x⟩
  obtain ⟨n, hn⟩ := denseRange_iff.mp (denseRange_denseSeq X) x (ε / 2)
    (by simp_all [ε, ← IsClosed.notMem_iff_infDist_pos, mem_interior_iff_mem_nhds]

中文:
引理 separation
  条件: {x : X} {C : 集合 X} (hxC : C in 𝓝 x)
  证明: by
  let ε : Real := min (infDist x (closure Cᶜ)) 1
  obtain hC | hC := (closure Cᶜ).eq_empty_or_nonempty
  · simp_all
  have : Nonempty X := ⟨x⟩
  obtain ⟨n, hn⟩ := denseRange_iff.mp (denseRange_denseSeq X) x (ε / 2)
    (by simp_all [ε, ← IsClosed.notMem_iff_infDist_pos, mem_interior_iff_mem_nhds]

Depends on / 依赖: IsClosed, IsClosed.notMem_iff_infDist_pos, Nonempty, Subtype, Subtype.dist_eq, abs_eq_self, abs_eq_self.mpr, closure, coe_projIcc, denseRange_denseSeq, denseRange_iff, denseRange_iff.mp, denseSeq, dist_eq, eq_empty_or_nonempty, infDist, isOpen_ball, isOpen_ball.mem_nhds, mem_interior_iff_mem_nhds, mem_nhds
-/
lemma separation {x : X} {C : Set X} (hxC : C in 𝓝 x) :
    exists (n : Nat), C in (𝓝 (distDenseSeq X n x)).comap (distDenseSeq X n) := by
  let ε : Real := min (infDist x (closure Cᶜ)) 1
  obtain hC | hC := (closure Cᶜ).eq_empty_or_nonempty
  · simp_all
  have : Nonempty X := ⟨x⟩
  obtain ⟨n, hn⟩ := denseRange_iff.mp (denseRange_denseSeq X) x (ε / 2)
    (by simp_all [ε, ← IsClosed.notMem_iff_infDist_pos, mem_interior_iff_mem_nhds])
  refine ⟨n, ball 0 (ε / 2), isOpen_ball.mem_nhds ?_, ?_⟩
  · simp [Subtype.dist_eq, abs_eq_self.mpr, coe_projIcc, hn]
  · intro y hy
    replace hy : dist y (denseSeq X n) < ε / 2 := by
      simpa [Subtype.dist_eq, abs_eq_self.mpr, coe_projIcc, not_lt_of_ge, ε, div_le_iff₀] using hy
    have : dist x y < infDist x (closure Cᶜ) :=
      ((dist_triangle_right x y (denseSeq X n)).trans_lt (add_lt_add hn hy)).trans_le (by simp [ε])
    simpa using notMem_of_notMem_closure (mt infDist_le_dist_of_mem this.not_ge)

/--
lemma `injective_distDenseSeq` / 引理 `injective_distDenseSeq`

English:
lemma injective_distDenseSeq
  given: (x y : X) (hxy : x != y)
  proof: by
  obtain ⟨n, hn⟩ := separation ((isOpen_compl_singleton (x := y)).mem_nhds hxy)
  exact ⟨n, fun e => by simp +contextual [e, ← exists_prop, mem_of_mem_nhds] at hn⟩

中文:
引理 injective_distDenseSeq
  条件: (x y : X) (hxy : x != y)
  证明: by
  obtain ⟨n, hn⟩ := separation ((isOpen_compl_singleton (x := y)).mem_nhds hxy)
  exact ⟨n, fun e => by simp +contextual [e, ← exists_prop, mem_of_mem_nhds] at hn⟩

Depends on / 依赖: contextual, exists_prop, isOpen_compl_singleton, mem_nhds, mem_of_mem_nhds, separation
-/
lemma injective_distDenseSeq (x y : X) (hxy : x != y) :
    exists n, distDenseSeq X n x != distDenseSeq X n y := by
  obtain ⟨n, hn⟩ := separation ((isOpen_compl_singleton (x := y)).mem_nhds hxy)
  exact ⟨n, fun e => by simp +contextual [e, ← exists_prop, mem_of_mem_nhds] at hn⟩

variable (A : Type*) [TopologicalSpace A]

/--
lemma `continuous_distDenseSeq_inv` / 引理 `continuous_distDenseSeq_inv`

English:
lemma continuous_distDenseSeq_inv
  proof: by
  refine continuous_iff_continuousAt.mpr fun x s hs => ?_
  obtain ⟨i, t, ht, hts⟩ := separation hs
  rw [(isUniformEmbedding_embed injective_distDenseSeq).isEmbedding.nhds_eq_comap]; rw [nhds_pi]
  exact ⟨_, Filter.mem_pi_of_mem _ ht, fun x hx => hts hx⟩

中文:
引理 continuous_distDenseSeq_inv
  证明: by
  refine continuous_iff_continuousAt.mpr fun x s hs => ?_
  obtain ⟨i, t, ht, hts⟩ := separation hs
  rw [(isUniformEmbedding_embed injective_distDenseSeq).isEmbedding.nhds_eq_comap]; rw [nhds_pi]
  exact ⟨_, Filter.mem_pi_of_mem _ ht, fun x hx => hts hx⟩

Depends on / 依赖: Filter, Filter.mem_pi_of_mem, continuous_iff_continuousAt, continuous_iff_continuousAt.mpr, injective_distDenseSeq, isEmbedding, isEmbedding.nhds_eq_comap, isUniformEmbedding_embed, mem_pi_of_mem, nhds_eq_comap, nhds_pi, separation
-/
lemma continuous_distDenseSeq_inv :
    Continuous (ofPiNat : PiNatEmbed X (fun _ => I) (distDenseSeq X) -> X) := by
  refine continuous_iff_continuousAt.mpr fun x s hs => ?_
  obtain ⟨i, t, ht, hts⟩ := separation hs
  rw [(isUniformEmbedding_embed injective_distDenseSeq).isEmbedding.nhds_eq_comap]; rw [nhds_pi]
  exact ⟨_, Filter.mem_pi_of_mem _ ht, fun x hx => hts hx⟩

/--
theorem `exists_embedding_to_hilbert_cube` / 定理 `exists_embedding_to_hilbert_cube`

English:
theorem exists_embedding_to_hilbert_cube
  statement: exists F : X -> Nat -> I, IsEmbedding F
  proof: by
  let firststep : X ≃ₜ PiNatEmbed X (fun i => I) (distDenseSeq X) := {
    toFun := toPiNat
    invFun := ofPiNat
    left_inv _ := rfl
    right_inv _ := rfl
continuous_toFun := continuous_toPiNat fun i => continuous_distDenseSeq i
    continuous_invFun := continuous_distDenseSeq_inv }
  let sec

中文:
定理 存在_embedding_to_hilbert_cube
  结论: 存在 F : X -> 自然数 -> I, 是嵌入 F
  证明: by
  let firststep : X ≃ₜ PiNatEmbed X (fun i => I) (distDenseSeq X) := {
    toFun := toPiNat
    invFun := ofPiNat
    left_inv _ := rfl
    right_inv _ := rfl
continuous_toFun := continuous_toPiNat fun i => continuous_distDenseSeq i
    continuous_invFun := continuous_distDenseSeq_inv }
  let sec

Depends on / 依赖: IsEmbedding, PiNatEmbed, continuous_distDenseSeq, continuous_distDenseSeq_inv, continuous_invFun, continuous_toFun, continuous_toPiNat, distDenseSeq, firststep, injective_distDenseSeq, invFun, isEmbedding, isEmbedding_secon, isEmbedding_secondstep, isUniformEmbedding_embed, left_inv, ofPiNat, right_inv, secondstep, toPiNat
-/
theorem exists_embedding_to_hilbert_cube : exists F : X -> Nat -> I, IsEmbedding F := by
  let firststep : X ≃ₜ PiNatEmbed X (fun i => I) (distDenseSeq X) := {
    toFun := toPiNat
    invFun := ofPiNat
    left_inv _ := rfl
    right_inv _ := rfl
continuous_toFun := continuous_toPiNat fun i => continuous_distDenseSeq i
    continuous_invFun := continuous_distDenseSeq_inv }
  let secondstep : PiNatEmbed X (fun i => I) (distDenseSeq X) -> Nat -> I := embed _ _ _
  let isEmbedding_secondstep : IsEmbedding secondstep :=
      (isUniformEmbedding_embed injective_distDenseSeq).isEmbedding
  exact ⟨_, isEmbedding_secondstep.comp firststep.isEmbedding⟩

end MetricSpace
end PiNatEmbed
end Metric
