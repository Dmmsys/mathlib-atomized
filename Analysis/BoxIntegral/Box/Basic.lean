/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Data.NNReal.Basic
public import Mathlib.Order.Fin.Tuple
public import Mathlib.Order.Interval.Set.Monotone
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.MetricSpace.Pseudo.Real
public import Mathlib.Topology.Order.MonotoneConvergence
/-!
# Rectangular boxes in `ℝⁿ`

In this file we define rectangular boxes in `ℝⁿ`. As usual, we represent `ℝⁿ` as the type of
functions `ι → ℝ` (usually `ι = Fin n` for some `n`). When we need to interpret a box `[l, u]` as a
set, we use the product `{x | ∀ i, l i < x i ∧ x i ≤ u i}` of half-open intervals `(l i, u i]`. We
exclude `l i` because this way boxes of a partition are disjoint as sets in `ℝⁿ`.

Currently, the only use cases for these constructions are the definitions of Riemann-style integrals
(Riemann, Henstock-Kurzweil, McShane).

## Main definitions

We use the same structure `BoxIntegral.Box` both for ambient boxes and for elements of a partition.
Each box is stored as two points `lower upper : ι → ℝ` and a proof of `∀ i, lower i < upper i`. We
define instances `Membership (ι → ℝ) (Box ι)` and `CoeTC (Box ι) (Set <| ι → ℝ)` so that each box is
interpreted as the set `{x | ∀ i, x i ∈ Set.Ioc (I.lower i) (I.upper i)}`. This way boxes of a
partition are pairwise disjoint and their union is exactly the original box.

We require boxes to be nonempty, because this way coercion to sets is injective. The empty box can
be represented as `⊥ : WithBot (BoxIntegral.Box ι)`.

We define the following operations on boxes:

* coercion to `Set (ι → ℝ)` and `Membership (ι → ℝ) (BoxIntegral.Box ι)` as described above;
* `PartialOrder` and `SemilatticeSup` instances such that `I ≤ J` is equivalent to
  `(I : Set (ι → ℝ)) ⊆ J`;
* `Lattice` instances on `WithBot (BoxIntegral.Box ι)`;
* `BoxIntegral.Box.Icc`: the closed box `Set.Icc I.lower I.upper`; defined as a bundled monotone
  map from `Box ι` to `Set (ι → ℝ)`;
* `BoxIntegral.Box.face I i : Box (Fin n)`: a hyperface of `I : BoxIntegral.Box (Fin (n + 1))`;
* `BoxIntegral.Box.distortion`: the maximal ratio of two lengths of edges of a box; defined as the
  supremum of `nndist I.lower I.upper / nndist (I.lower i) (I.upper i)`.

We also provide a convenience constructor `BoxIntegral.Box.mk' (l u : ι → ℝ) : WithBot (Box ι)`
that returns the box `⟨l, u, _⟩` if it is nonempty and `⊥` otherwise.

## Tags

rectangular box
-/

@[expose] public section

open Set Function Metric Filter

noncomputable section

open scoped NNReal Topology

namespace BoxIntegral

variable {ι : Type*}

/-!
### Rectangular box: definition and partial order
-/


/--
Definition of `Box` / `Box` 的定义

English:
structure Box
  parameters: (ι : Type*)
  axioms and operations (2):
    - (lower(upper) : ι -> Real)
    - lower_lt_upper : forall i, lower i < upper i

中文:
结构 Box
  参数: (ι : 类型)
  公理与运算 (2 个):
    - (lower(upper) : ι -> 实数)
    - lower_lt_upper : 对任意 i, lower i < upper i
-/
structure Box (ι : Type*) where
  /-- coordinates of the lower and upper corners of the box -/
  (lower upper : ι -> Real)
  /-- Each lower coordinate is less than its upper coordinate: i.e., the box is non-empty -/
  lower_lt_upper : forall i, lower i < upper i

attribute [simp] Box.lower_lt_upper

namespace Box

variable (I J : Box ι) {x y : ι -> Real}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Box ι)
  body: ⟨⟨0, 1, fun _ => zero_lt_one⟩⟩

中文:
实例 :
  签名: 可居 (Box ι)
  定义体: ⟨⟨0, 1, fun _ => zero_lt_one⟩⟩

Depends on / 依赖: zero_lt_one
-/
instance : Inhabited (Box ι) :=
  ⟨⟨0, 1, fun _ => zero_lt_one⟩⟩

/--
theorem `lower_le_upper` / 定理 `lower_le_upper`

English:
theorem lower_le_upper
  statement: I.lower <= I.upper
  proof: fun i => (I.lower_lt_upper i).le

中文:
定理 lower_le_upper
  结论: I.lower <= I.upper
  证明: fun i => (I.lower_lt_upper i).le

Depends on / 依赖: I.lower_lt_upper, lower_lt_upper
-/
theorem lower_le_upper : I.lower <= I.upper :=
  fun i => (I.lower_lt_upper i).le

/--
theorem `lower_ne_upper` / 定理 `lower_ne_upper`

English:
theorem lower_ne_upper
  given: (i)
  statement: I.lower i != I.upper i
  proof: (I.lower_lt_upper i).ne

中文:
定理 lower_ne_upper
  条件: (i)
  结论: I.lower i != I.upper i
  证明: (I.lower_lt_upper i).ne

Depends on / 依赖: I.lower_lt_upper, lower_lt_upper
-/
theorem lower_ne_upper (i) : I.lower i != I.upper i :=
  (I.lower_lt_upper i).ne

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Membership (ι -> Real) (Box ι)
  body: ⟨fun I x => forall i, x i in Ioc (I.lower i) (I.upper i)⟩

中文:
实例 :
  签名: Membership (ι -> 实数) (Box ι)
  定义体: ⟨fun I x => forall i, x i in Ioc (I.lower i) (I.upper i)⟩

Depends on / 依赖: I.lower, I.upper
-/
instance : Membership (ι -> Real) (Box ι) :=
  ⟨fun I x => forall i, x i in Ioc (I.lower i) (I.upper i)⟩

/-- The set of points in this box: this is the product of half-open intervals `(lower i, upper i]`,
where `lower` and `upper` are this box' corners. -/
@[coe]
/--
Definition of `toSet` / `toSet` 的定义

English:
definition toSet
  signature: (I : Box ι)
  body: { x | x in I }

中文:
定义 toSet
  签名: (I : Box ι)
  定义体: { x | x in I }
-/
def toSet (I : Box ι) : Set (ι -> Real) := { x | x in I }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeTC (Box ι) (Set <| ι -> Real)
  body: ⟨toSet⟩

@[simp]

中文:
实例 :
  签名: CoeTC (Box ι) (集合 <| ι -> 实数)
  定义体: ⟨toSet⟩

@[simp]
-/
instance : CoeTC (Box ι) (Set <| ι -> Real) :=
  ⟨toSet⟩

@[simp]
/--
theorem `mem_mk` / 定理 `mem_mk`

English:
theorem mem_mk
  given: {l u x : ι -> Real} {H}
  statement: x in mk l u H ↔ forall i, x i in Ioc (l i) (u i)
  proof: Iff.rfl

@[simp, norm_cast]

中文:
定理 mem_mk
  条件: {l u x : ι -> 实数} {H}
  结论: x in mk l u H ↔ 对任意 i, x i in 左开右闭区间 (l i) (u i)
  证明: Iff.rfl

@[simp, norm_cast]

Depends on / 依赖: Iff.rfl
-/
theorem mem_mk {l u x : ι -> Real} {H} : x in mk l u H ↔ forall i, x i in Ioc (l i) (u i) := Iff.rfl

@[simp, norm_cast]
/--
theorem `mem_coe` / 定理 `mem_coe`

English:
theorem mem_coe
  statement: x in (I : Set (ι -> Real)) ↔ x in I
  proof: Iff.rfl

中文:
定理 mem_coe
  结论: x in (I : 集合 (ι -> 实数)) ↔ x in I
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_coe : x in (I : Set (ι -> Real)) ↔ x in I := Iff.rfl

/--
theorem `mem_def` / 定理 `mem_def`

English:
theorem mem_def
  statement: x in I ↔ forall i, x i in Ioc (I.lower i) (I.upper i)
  proof: Iff.rfl

中文:
定理 mem_def
  结论: x in I ↔ 对任意 i, x i in 左开右闭区间 (I.lower i) (I.upper i)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_def : x in I ↔ forall i, x i in Ioc (I.lower i) (I.upper i) := Iff.rfl

/--
theorem `mem_univ_Ioc` / 定理 `mem_univ_Ioc`

English:
theorem mem_univ_Ioc
  given: {I : Box ι}
  statement: (x in pi univ fun i => Ioc (I.lower i) (I.upper i)) ↔ x in I
  proof: mem_univ_pi

中文:
定理 mem_univ_Ioc
  条件: {I : Box ι}
  结论: (x in pi univ fun i => 左开右闭区间 (I.lower i) (I.upper i)) ↔ x in I
  证明: mem_univ_pi

Depends on / 依赖: mem_univ_pi
-/
theorem mem_univ_Ioc {I : Box ι} : (x in pi univ fun i => Ioc (I.lower i) (I.upper i)) ↔ x in I :=
  mem_univ_pi

/--
theorem `coe_eq_pi` / 定理 `coe_eq_pi`

English:
theorem coe_eq_pi
  statement: (I : Set (ι -> Real)) = pi univ fun i => Ioc (I.lower i) (I.upper i)
  proof: Set.ext fun _ => mem_univ_Ioc.symm

@[simp]

中文:
定理 coe_eq_pi
  结论: (I : 集合 (ι -> 实数)) = pi univ fun i => 左开右闭区间 (I.lower i) (I.upper i)
  证明: Set.ext fun _ => mem_univ_Ioc.symm

@[simp]

Depends on / 依赖: Set.ext, mem_univ_Ioc, mem_univ_Ioc.symm
-/
theorem coe_eq_pi : (I : Set (ι -> Real)) = pi univ fun i => Ioc (I.lower i) (I.upper i) :=
  Set.ext fun _ => mem_univ_Ioc.symm

@[simp]
/--
theorem `upper_mem` / 定理 `upper_mem`

English:
theorem upper_mem
  statement: I.upper in I
  proof: fun i => right_mem_Ioc.2 I.lower_lt_upper i

中文:
定理 upper_mem
  结论: I.upper in I
  证明: fun i => right_mem_Ioc.2 I.lower_lt_upper i

Depends on / 依赖: I.lower_lt_upper, lower_lt_upper, right_mem_Ioc
-/
theorem upper_mem : I.upper in I :=
fun i => right_mem_Ioc.2 I.lower_lt_upper i

/--
theorem `exists_mem` / 定理 `exists_mem`

English:
theorem exists_mem
  statement: exists x, x in I
  proof: ⟨_, I.upper_mem⟩

中文:
定理 存在_mem
  结论: 存在 x, x in I
  证明: ⟨_, I.upper_mem⟩

Depends on / 依赖: I.upper_mem, upper_mem
-/
theorem exists_mem : exists x, x in I :=
  ⟨_, I.upper_mem⟩

/--
theorem `nonempty_coe` / 定理 `nonempty_coe`

English:
theorem nonempty_coe
  statement: Set.Nonempty (I : Set (ι -> Real))
  proof: I.exists_mem

@[simp]

中文:
定理 nonempty_coe
  结论: 集合.非空 (I : 集合 (ι -> 实数))
  证明: I.exists_mem

@[simp]

Depends on / 依赖: I.exists_mem, exists_mem
-/
theorem nonempty_coe : Set.Nonempty (I : Set (ι -> Real)) :=
  I.exists_mem

@[simp]
/--
theorem `coe_ne_empty` / 定理 `coe_ne_empty`

English:
theorem coe_ne_empty
  statement: (I : Set (ι -> Real)) != ∅
  proof: I.nonempty_coe.ne_empty

@[simp]

中文:
定理 coe_ne_empty
  结论: (I : 集合 (ι -> 实数)) != ∅
  证明: I.nonempty_coe.ne_empty

@[simp]

Depends on / 依赖: I.nonempty_coe.ne_empty, ne_empty, nonempty_coe
-/
theorem coe_ne_empty : (I : Set (ι -> Real)) != ∅ :=
  I.nonempty_coe.ne_empty

@[simp]
/--
theorem `empty_ne_coe` / 定理 `empty_ne_coe`

English:
theorem empty_ne_coe
  statement: ∅ != (I : Set (ι -> Real))
  proof: I.coe_ne_empty.symm

中文:
定理 empty_ne_coe
  结论: ∅ != (I : 集合 (ι -> 实数))
  证明: I.coe_ne_empty.symm

Depends on / 依赖: I.coe_ne_empty.symm, coe_ne_empty
-/
theorem empty_ne_coe : ∅ != (I : Set (ι -> Real)) :=
  I.coe_ne_empty.symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LE (Box ι)
  body: ⟨fun I J => forall ⦃x⦄, x in I -> x in J⟩

中文:
实例 :
  签名: LE (Box ι)
  定义体: ⟨fun I J => forall ⦃x⦄, x in I -> x in J⟩
-/
instance : LE (Box ι) :=
  ⟨fun I J => forall ⦃x⦄, x in I -> x in J⟩

/--
theorem `le_def` / 定理 `le_def`

English:
theorem le_def
  statement: I <= J ↔ forall x in I, x in J
  proof: Iff.rfl

中文:
定理 le_def
  结论: I <= J ↔ 对任意 x in I, x in J
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem le_def : I <= J ↔ forall x in I, x in J := Iff.rfl

/--
theorem `le_TFAE` / 定理 `le_TFAE`

English:
theorem le_TFAE
  statement: List.TFAE [I <= J, (I : Set (ι -> Real)) subseteq J,
  proof: by
  tfae_have 1 ↔ 2 := Iff.rfl
  tfae_have 2 -> 3
  | h => by simpa [coe_eq_pi, closure_pi_set, lower_ne_upper] using closure_mono h
  tfae_have 3 ↔ 4 := Icc_subset_Icc_iff I.lower_le_upper
  tfae_have 4 -> 2
  | h, x, hx, i => Ioc_subset_Ioc (h.1 i) (h.2 i) (hx i)
  tfae_finish

中文:
定理 le_TFAE
  结论: 列表.TFAE [I <= J, (I : 集合 (ι -> 实数)) subseteq J,
  证明: by
  tfae_have 1 ↔ 2 := Iff.rfl
  tfae_have 2 -> 3
  | h => by simpa [coe_eq_pi, closure_pi_set, lower_ne_upper] using closure_mono h
  tfae_have 3 ↔ 4 := Icc_subset_Icc_iff I.lower_le_upper
  tfae_have 4 -> 2
  | h, x, hx, i => Ioc_subset_Ioc (h.1 i) (h.2 i) (hx i)
  tfae_finish

Depends on / 依赖: I.lower_le_upper, Icc_subset_Icc_iff, Iff.rfl, Ioc_subset_Ioc, closure_mono, closure_pi_set, coe_eq_pi, lower_le_upper, lower_ne_upper, tfae_finish, tfae_have
-/
theorem le_TFAE : List.TFAE [I <= J, (I : Set (ι -> Real)) subseteq J,
    Icc I.lower I.upper subseteq Icc J.lower J.upper, J.lower <= I.lower ∧ I.upper <= J.upper] := by
  tfae_have 1 ↔ 2 := Iff.rfl
  tfae_have 2 -> 3
  | h => by simpa [coe_eq_pi, closure_pi_set, lower_ne_upper] using closure_mono h
  tfae_have 3 ↔ 4 := Icc_subset_Icc_iff I.lower_le_upper
  tfae_have 4 -> 2
  | h, x, hx, i => Ioc_subset_Ioc (h.1 i) (h.2 i) (hx i)
  tfae_finish

variable {I J}

@[simp, norm_cast]
/--
theorem `coe_subset_coe` / 定理 `coe_subset_coe`

English:
theorem coe_subset_coe
  statement: (I : Set (ι -> Real)) subseteq J ↔ I <= J
  proof: Iff.rfl

中文:
定理 coe_subset_coe
  结论: (I : 集合 (ι -> 实数)) subseteq J ↔ I <= J
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem coe_subset_coe : (I : Set (ι -> Real)) subseteq J ↔ I <= J := Iff.rfl

/--
theorem `le_iff_bounds` / 定理 `le_iff_bounds`

English:
theorem le_iff_bounds
  statement: I <= J ↔ J.lower <= I.lower ∧ I.upper <= J.upper
  proof: (le_TFAE I J).out 0 3

中文:
定理 le_iff_bounds
  结论: I <= J ↔ J.lower <= I.lower ∧ I.upper <= J.upper
  证明: (le_TFAE I J).out 0 3

Depends on / 依赖: le_TFAE
-/
theorem le_iff_bounds : I <= J ↔ J.lower <= I.lower ∧ I.upper <= J.upper :=
  (le_TFAE I J).out 0 3

/--
theorem `injective_coe` / 定理 `injective_coe`

English:
theorem injective_coe
  statement: Injective ((↑) : Box ι -> Set (ι -> Real))
  proof: by
  rintro ⟨l₁, u₁, h₁⟩ ⟨l₂, u₂, h₂⟩ h
  simp only [Subset.antisymm_iff, coe_subset_coe, le_iff_bounds] at h
  congr
  exacts [le_antisymm h.2.1 h.1.1, le_antisymm h.1.2 h.2.2]

@[simp, norm_cast]

中文:
定理 injective_coe
  结论: 单射 ((↑) : Box ι -> 集合 (ι -> 实数))
  证明: by
  rintro ⟨l₁, u₁, h₁⟩ ⟨l₂, u₂, h₂⟩ h
  simp only [Subset.antisymm_iff, coe_subset_coe, le_iff_bounds] at h
  congr
  exacts [le_antisymm h.2.1 h.1.1, le_antisymm h.1.2 h.2.2]

@[simp, norm_cast]

Depends on / 依赖: Subset, Subset.antisymm_iff, antisymm_iff, coe_subset_coe, exacts, le_antisymm, le_iff_bounds
-/
theorem injective_coe : Injective ((↑) : Box ι -> Set (ι -> Real)) := by
  rintro ⟨l₁, u₁, h₁⟩ ⟨l₂, u₂, h₂⟩ h
  simp only [Subset.antisymm_iff, coe_subset_coe, le_iff_bounds] at h
  congr
  exacts [le_antisymm h.2.1 h.1.1, le_antisymm h.1.2 h.2.2]

@[simp, norm_cast]
/--
theorem `coe_inj` / 定理 `coe_inj`

English:
theorem coe_inj
  statement: (I : Set (ι -> Real)) = J ↔ I = J
  proof: injective_coe.eq_iff

@[ext]

中文:
定理 coe_inj
  结论: (I : 集合 (ι -> 实数)) = J ↔ I = J
  证明: injective_coe.eq_iff

@[ext]

Depends on / 依赖: eq_iff, injective_coe, injective_coe.eq_iff
-/
theorem coe_inj : (I : Set (ι -> Real)) = J ↔ I = J :=
  injective_coe.eq_iff

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: (H : forall x, x in I ↔ x in J)
  statement: I = J
  proof: injective_coe Set.ext H

中文:
定理 ext
  条件: (H : 对任意 x, x in I ↔ x in J)
  结论: I = J
  证明: injective_coe Set.ext H

Depends on / 依赖: Set.ext, injective_coe
-/
theorem ext (H : forall x, x in I ↔ x in J) : I = J :=
injective_coe Set.ext H

/--
theorem `ne_of_disjoint_coe` / 定理 `ne_of_disjoint_coe`

English:
theorem ne_of_disjoint_coe
  given: (h : Disjoint (I : Set (ι -> Real)) J)
  statement: I != J
  proof: mt coe_inj.2 h.ne I.coe_ne_empty

中文:
定理 ne_of_disjoint_coe
  条件: (h : Disjoint (I : 集合 (ι -> 实数)) J)
  结论: I != J
  证明: mt coe_inj.2 h.ne I.coe_ne_empty

Depends on / 依赖: I.coe_ne_empty, coe_inj, coe_ne_empty, h.ne
-/
theorem ne_of_disjoint_coe (h : Disjoint (I : Set (ι -> Real)) J) : I != J :=
mt coe_inj.2 h.ne I.coe_ne_empty

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (Box ι)
  body: { PartialOrder.lift ((↑) : Box ι -> Set (ι -> Real)) injective_coe with le := (· <= ·) }

中文:
实例 :
  签名: 偏序 (Box ι)
  定义体: { PartialOrder.lift ((↑) : Box ι -> Set (ι -> Real)) injective_coe with le := (· <= ·) }

Depends on / 依赖: PartialOrder, PartialOrder.lift, injective_coe
-/
instance : PartialOrder (Box ι) :=
  { PartialOrder.lift ((↑) : Box ι -> Set (ι -> Real)) injective_coe with le := (· <= ·) }

/--
Definition of `Icc` / `Icc` 的定义

English:
definition Icc
  signature: : Box ι ↪o Set (ι -> Real)
  body: OrderEmbedding.ofMapLEIff (fun I : Box ι => Icc I.lower I.upper) fun I J => (le_TFAE I J).out 2 0

中文:
定义 闭区间
  签名: : Box ι ↪o 集合 (ι -> 实数)
  定义体: OrderEmbedding.ofMapLEIff (fun I : Box ι => Icc I.lower I.upper) fun I J => (le_TFAE I J).out 2 0
-/
protected def Icc : Box ι ↪o Set (ι -> Real) :=
  OrderEmbedding.ofMapLEIff (fun I : Box ι => Icc I.lower I.upper) fun I J => (le_TFAE I J).out 2 0

/--
theorem `Icc_def` / 定理 `Icc_def`

English:
theorem Icc_def
  statement: Box.Icc I = Icc I.lower I.upper
  proof: rfl

@[simp]

中文:
定理 Icc_def
  结论: Box.闭区间 I = 闭区间 I.lower I.upper
  证明: rfl

@[simp]
-/
theorem Icc_def : Box.Icc I = Icc I.lower I.upper := rfl

@[simp]
/--
theorem `upper_mem_Icc` / 定理 `upper_mem_Icc`

English:
theorem upper_mem_Icc
  given: (I : Box ι)
  statement: I.upper in Box.Icc I
  proof: right_mem_Icc.2 I.lower_le_upper

@[simp]

中文:
定理 upper_mem_Icc
  条件: (I : Box ι)
  结论: I.upper in Box.闭区间 I
  证明: right_mem_Icc.2 I.lower_le_upper

@[simp]

Depends on / 依赖: I.lower_le_upper, lower_le_upper, right_mem_Icc
-/
theorem upper_mem_Icc (I : Box ι) : I.upper in Box.Icc I :=
  right_mem_Icc.2 I.lower_le_upper

@[simp]
/--
theorem `lower_mem_Icc` / 定理 `lower_mem_Icc`

English:
theorem lower_mem_Icc
  given: (I : Box ι)
  statement: I.lower in Box.Icc I
  proof: left_mem_Icc.2 I.lower_le_upper

中文:
定理 lower_mem_Icc
  条件: (I : Box ι)
  结论: I.lower in Box.闭区间 I
  证明: left_mem_Icc.2 I.lower_le_upper

Depends on / 依赖: I.lower_le_upper, left_mem_Icc, lower_le_upper
-/
theorem lower_mem_Icc (I : Box ι) : I.lower in Box.Icc I :=
  left_mem_Icc.2 I.lower_le_upper

/--
theorem `isCompact_Icc` / 定理 `isCompact_Icc`

English:
theorem isCompact_Icc
  given: (I : Box ι)
  statement: IsCompact (Box.Icc I)
  proof: isCompact_Icc

中文:
定理 isCompact_Icc
  条件: (I : Box ι)
  结论: 是紧集 (Box.闭区间 I)
  证明: isCompact_Icc
-/
protected theorem isCompact_Icc (I : Box ι) : IsCompact (Box.Icc I) :=
  isCompact_Icc

/--
theorem `Icc_eq_pi` / 定理 `Icc_eq_pi`

English:
theorem Icc_eq_pi
  statement: Box.Icc I = pi univ fun i => Icc (I.lower i) (I.upper i)
  proof: (pi_univ_Icc _ _).symm

中文:
定理 Icc_eq_pi
  结论: Box.闭区间 I = pi univ fun i => 闭区间 (I.lower i) (I.upper i)
  证明: (pi_univ_Icc _ _).symm

Depends on / 依赖: pi_univ_Icc
-/
theorem Icc_eq_pi : Box.Icc I = pi univ fun i => Icc (I.lower i) (I.upper i) :=
  (pi_univ_Icc _ _).symm

/--
theorem `le_iff_Icc` / 定理 `le_iff_Icc`

English:
theorem le_iff_Icc
  statement: I <= J ↔ Box.Icc I subseteq Box.Icc J
  proof: (le_TFAE I J).out 0 2

中文:
定理 le_iff_Icc
  结论: I <= J ↔ Box.闭区间 I subseteq Box.闭区间 J
  证明: (le_TFAE I J).out 0 2

Depends on / 依赖: le_TFAE
-/
theorem le_iff_Icc : I <= J ↔ Box.Icc I subseteq Box.Icc J :=
  (le_TFAE I J).out 0 2

/--
theorem `antitone_lower` / 定理 `antitone_lower`

English:
theorem antitone_lower
  statement: Antitone fun I : Box ι => I.lower
  proof: fun _ _ H => (le_iff_bounds.1 H).1

中文:
定理 antitone_lower
  结论: 递减 fun I : Box ι => I.lower
  证明: fun _ _ H => (le_iff_bounds.1 H).1

Depends on / 依赖: le_iff_bounds
-/
theorem antitone_lower : Antitone fun I : Box ι => I.lower :=
  fun _ _ H => (le_iff_bounds.1 H).1

/--
theorem `monotone_upper` / 定理 `monotone_upper`

English:
theorem monotone_upper
  statement: Monotone fun I : Box ι => I.upper
  proof: fun _ _ H => (le_iff_bounds.1 H).2

中文:
定理 monotone_upper
  结论: 递增 fun I : Box ι => I.upper
  证明: fun _ _ H => (le_iff_bounds.1 H).2

Depends on / 依赖: le_iff_bounds
-/
theorem monotone_upper : Monotone fun I : Box ι => I.upper :=
  fun _ _ H => (le_iff_bounds.1 H).2

/--
theorem `coe_subset_Icc` / 定理 `coe_subset_Icc`

English:
theorem coe_subset_Icc
  statement: ↑I subseteq Box.Icc I
  proof: fun _ hx => ⟨fun i => (hx i).1.le, fun i => (hx i).2⟩

中文:
定理 coe_subset_Icc
  结论: ↑I subseteq Box.闭区间 I
  证明: fun _ hx => ⟨fun i => (hx i).1.le, fun i => (hx i).2⟩
-/
theorem coe_subset_Icc : ↑I subseteq Box.Icc I :=
  fun _ hx => ⟨fun i => (hx i).1.le, fun i => (hx i).2⟩

/--
theorem `isBounded_Icc` / 定理 `isBounded_Icc`

English:
theorem isBounded_Icc
  given: [Finite ι] (I : Box ι)
  statement: Bornology.IsBounded (Box.Icc I)
  proof: by
  cases nonempty_fintype ι
  exact Metric.isBounded_Icc _ _

中文:
定理 isBounded_Icc
  条件: [有限 ι] (I : Box ι)
  结论: 有界结构.IsBounded (Box.闭区间 I)
  证明: by
  cases nonempty_fintype ι
  exact Metric.isBounded_Icc _ _

Depends on / 依赖: Metric, Metric.isBounded_Icc, isBounded_Icc, nonempty_fintype
-/
theorem isBounded_Icc [Finite ι] (I : Box ι) : Bornology.IsBounded (Box.Icc I) := by
  cases nonempty_fintype ι
  exact Metric.isBounded_Icc _ _

/--
theorem `isBounded` / 定理 `isBounded`

English:
theorem isBounded
  given: [Finite ι] (I : Box ι)
  statement: Bornology.IsBounded I.toSet
  proof: Bornology.IsBounded.subset I.isBounded_Icc coe_subset_Icc

中文:
定理 isBounded
  条件: [有限 ι] (I : Box ι)
  结论: 有界结构.IsBounded I.toSet
  证明: Bornology.IsBounded.subset I.isBounded_Icc coe_subset_Icc

Depends on / 依赖: Bornology, Bornology.IsBounded.subset, I.isBounded_Icc, IsBounded, coe_subset_Icc, isBounded_Icc, subset
-/
theorem isBounded [Finite ι] (I : Box ι) : Bornology.IsBounded I.toSet :=
  Bornology.IsBounded.subset I.isBounded_Icc coe_subset_Icc

/-!
### Supremum of two boxes
-/


/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SemilatticeSup (Box ι)
  body: { sup := fun I J => ⟨I.lower ⊓ J.lower, I.upper ⊔ J.upper,
fun i => (min_le_left _ _).trans_lt (I.lower_lt_upper i).trans_le (le_max_left _ _)⟩
    le_sup_left := fun _ _ => le_iff_bounds.2 ⟨inf_le_left, le_sup_left⟩
    le_sup_right := fun _ _ => le_iff_bounds.2 ⟨inf_le_right, le_sup_right⟩
    sup

中文:
实例 :
  签名: SemilatticeSup (Box ι)
  定义体: { sup := fun I J => ⟨I.lower ⊓ J.lower, I.upper ⊔ J.upper,
fun i => (min_le_left _ _).trans_lt (I.lower_lt_upper i).trans_le (le_max_left _ _)⟩
    le_sup_left := fun _ _ => le_iff_bounds.2 ⟨inf_le_left, le_sup_left⟩
    le_sup_right := fun _ _ => le_iff_bounds.2 ⟨inf_le_right, le_sup_right⟩
    sup

Depends on / 依赖: I.lower, I.lower_lt_upper, I.upper, J.lower, J.upper, antitone_lower, inf_le_left, inf_le_right, le_iff_bounds, le_inf, le_max_left, le_sup_left, le_sup_right, lower_lt_upper, min_le_left, monotone_upper, sup_le, trans_le, trans_lt
-/
instance : SemilatticeSup (Box ι) :=
  { sup := fun I J => ⟨I.lower ⊓ J.lower, I.upper ⊔ J.upper,
fun i => (min_le_left _ _).trans_lt (I.lower_lt_upper i).trans_le (le_max_left _ _)⟩
    le_sup_left := fun _ _ => le_iff_bounds.2 ⟨inf_le_left, le_sup_left⟩
    le_sup_right := fun _ _ => le_iff_bounds.2 ⟨inf_le_right, le_sup_right⟩
    sup_le := fun _ _ _ h₁ h₂ => le_iff_bounds.2
      ⟨le_inf (antitone_lower h₁) (antitone_lower h₂),
        sup_le (monotone_upper h₁) (monotone_upper h₂)⟩ }

/-!
### `WithBot (Box ι)`

In this section we define coercion from `WithBot (Box ι)` to `Set (ι → ℝ)` by sending `⊥` to `∅`.
-/

/-- The set underlying this box: `⊥` is mapped to `∅`. -/
@[coe]
/--
Definition of `withBotToSet` / `withBotToSet` 的定义

English:
definition withBotToSet
  signature: (o : WithBot (Box ι))
  body: o.elim ∅ (↑)

中文:
定义 withBotToSet
  签名: (o : WithBot (Box ι))
  定义体: o.elim ∅ (↑)

Depends on / 依赖: o.elim
-/
def withBotToSet (o : WithBot (Box ι)) : Set (ι -> Real) := o.elim ∅ (↑)

/--
Instance `withBotCoe` / 实例 `withBotCoe`

English:
instance withBotCoe
  signature: : CoeTC (WithBot (Box ι)) (Set (ι -> Real))
  body: ⟨withBotToSet⟩

@[simp, norm_cast]

中文:
实例 withBotCoe
  签名: : CoeTC (WithBot (Box ι)) (集合 (ι -> 实数))
  定义体: ⟨withBotToSet⟩

@[simp, norm_cast]

Depends on / 依赖: withBotToSet
-/
instance withBotCoe : CoeTC (WithBot (Box ι)) (Set (ι -> Real)) :=
  ⟨withBotToSet⟩

@[simp, norm_cast]
/--
theorem `coe_bot` / 定理 `coe_bot`

English:
theorem coe_bot
  statement: ((⊥ : WithBot (Box ι)) : Set (ι -> Real)) = ∅
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_bot
  结论: ((⊥ : WithBot (Box ι)) : 集合 (ι -> 实数)) = ∅
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_bot : ((⊥ : WithBot (Box ι)) : Set (ι -> Real)) = ∅ := rfl

@[simp, norm_cast]
/--
theorem `coe_coe` / 定理 `coe_coe`

English:
theorem coe_coe
  statement: ((I : WithBot (Box ι)) : Set (ι -> Real)) = I
  proof: rfl

中文:
定理 coe_coe
  结论: ((I : WithBot (Box ι)) : 集合 (ι -> 实数)) = I
  证明: rfl
-/
theorem coe_coe : ((I : WithBot (Box ι)) : Set (ι -> Real)) = I := rfl

/--
theorem `isSome_iff` / 定理 `isSome_iff`

English:
theorem isSome_iff
  statement: forall {I : WithBot (Box ι)}, I.isSome ↔ (I : Set (ι -> Real)).Nonempty

中文:
定理 isSome_iff
  结论: 对任意 {I : WithBot (Box ι)}, I.isSome ↔ (I : 集合 (ι -> 实数)).非空
-/
theorem isSome_iff : forall {I : WithBot (Box ι)}, I.isSome ↔ (I : Set (ι -> Real)).Nonempty
  | ⊥ => by
    unfold Option.isSome
    simp
  | (I : Box ι) => by
    unfold Option.isSome
    simp [I.nonempty_coe]

/--
theorem `biUnion_coe_eq_coe` / 定理 `biUnion_coe_eq_coe`

English:
theorem biUnion_coe_eq_coe
  given: (I : WithBot (Box ι))
  proof: by
  induction I <;> simp

@[simp, norm_cast]

中文:
定理 biUnion_coe_eq_coe
  条件: (I : WithBot (Box ι))
  证明: by
  induction I <;> simp

@[simp, norm_cast]
-/
theorem biUnion_coe_eq_coe (I : WithBot (Box ι)) :
    ⋃ (J : Box ι) (_ : ↑J = I), (J : Set (ι -> Real)) = I := by
  induction I <;> simp

@[simp, norm_cast]
/--
theorem `withBotCoe_subset_iff` / 定理 `withBotCoe_subset_iff`

English:
theorem withBotCoe_subset_iff
  given: {I J : WithBot (Box ι)}
  statement: (I : Set (ι -> Real)) subseteq J ↔ I <= J
  proof: by
  induction I; · simp
  induction J; · simp [subset_empty_iff]
  simp [le_def]

@[simp, norm_cast]

中文:
定理 withBotCoe_subset_iff
  条件: {I J : WithBot (Box ι)}
  结论: (I : 集合 (ι -> 实数)) subseteq J ↔ I <= J
  证明: by
  induction I; · simp
  induction J; · simp [subset_empty_iff]
  simp [le_def]

@[simp, norm_cast]

Depends on / 依赖: le_def, subset_empty_iff
-/
theorem withBotCoe_subset_iff {I J : WithBot (Box ι)} : (I : Set (ι -> Real)) subseteq J ↔ I <= J := by
  induction I; · simp
  induction J; · simp [subset_empty_iff]
  simp [le_def]

@[simp, norm_cast]
/--
theorem `withBotCoe_inj` / 定理 `withBotCoe_inj`

English:
theorem withBotCoe_inj
  given: {I J : WithBot (Box ι)}
  statement: (I : Set (ι -> Real)) = J ↔ I = J
  proof: by
  simp only [Subset.antisymm_iff, ← le_antisymm_iff, withBotCoe_subset_iff]

中文:
定理 withBotCoe_inj
  条件: {I J : WithBot (Box ι)}
  结论: (I : 集合 (ι -> 实数)) = J ↔ I = J
  证明: by
  simp only [Subset.antisymm_iff, ← le_antisymm_iff, withBotCoe_subset_iff]

Depends on / 依赖: Subset, Subset.antisymm_iff, antisymm_iff, le_antisymm_iff, withBotCoe_subset_iff
-/
theorem withBotCoe_inj {I J : WithBot (Box ι)} : (I : Set (ι -> Real)) = J ↔ I = J := by
  simp only [Subset.antisymm_iff, ← le_antisymm_iff, withBotCoe_subset_iff]

open scoped Classical in
/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: (l u : ι -> Real)
  body: if h : forall i, l i < u i then ↑(⟨l, u, h⟩ : Box ι) else ⊥

@[simp]

中文:
定义 mk'
  签名: (l u : ι -> 实数)
  定义体: if h : forall i, l i < u i then ↑(⟨l, u, h⟩ : Box ι) else ⊥

@[simp]
-/
def mk' (l u : ι -> Real) : WithBot (Box ι) :=
  if h : forall i, l i < u i then ↑(⟨l, u, h⟩ : Box ι) else ⊥

@[simp]
/--
theorem `mk'_eq_bot` / 定理 `mk'_eq_bot`

English:
theorem mk'_eq_bot
  given: {l u : ι -> Real}
  statement: mk' l u = ⊥ ↔ exists i, u i <= l i
  proof: by
  rw [mk']
  split_ifs with h <;> simpa using h

@[simp]

中文:
定理 mk'_eq_bot
  条件: {l u : ι -> 实数}
  结论: mk' l u = ⊥ ↔ 存在 i, u i <= l i
  证明: by
  rw [mk']
  split_ifs with h <;> simpa using h

@[simp]
-/
theorem mk'_eq_bot {l u : ι -> Real} : mk' l u = ⊥ ↔ exists i, u i <= l i := by
  rw [mk']
  split_ifs with h <;> simpa using h

@[simp]
/--
theorem `mk'_eq_coe` / 定理 `mk'_eq_coe`

English:
theorem mk'_eq_coe
  given: {l u : ι -> Real}
  statement: mk' l u = I ↔ l = I.lower ∧ u = I.upper
  proof: by
  obtain ⟨lI, uI, hI⟩ := I; rw [mk']; split_ifs with h
  · simp
  · suffices l = lI -> u != uI by simpa
    rintro rfl rfl
    exact h hI

@[simp]

中文:
定理 mk'_eq_coe
  条件: {l u : ι -> 实数}
  结论: mk' l u = I ↔ l = I.lower ∧ u = I.upper
  证明: by
  obtain ⟨lI, uI, hI⟩ := I; rw [mk']; split_ifs with h
  · simp
  · suffices l = lI -> u != uI by simpa
    rintro rfl rfl
    exact h hI

@[simp]
-/
theorem mk'_eq_coe {l u : ι -> Real} : mk' l u = I ↔ l = I.lower ∧ u = I.upper := by
  obtain ⟨lI, uI, hI⟩ := I; rw [mk']; split_ifs with h
  · simp
  · suffices l = lI -> u != uI by simpa
    rintro rfl rfl
    exact h hI

@[simp]
/--
theorem `coe_mk'` / 定理 `coe_mk'`

English:
theorem coe_mk'
  given: (l u : ι -> Real)
  statement: (mk' l u : Set (ι -> Real)) = pi univ fun i => Ioc (l i) (u i)
  proof: by
  rw [mk']; split_ifs with h
  · exact coe_eq_pi _
  · rcases not_forall.mp h with ⟨i, hi⟩
    rw [coe_bot]; rw [univ_pi_eq_empty]
    exact Ioc_eq_empty hi

中文:
定理 coe_mk'
  条件: (l u : ι -> 实数)
  结论: (mk' l u : 集合 (ι -> 实数)) = pi univ fun i => 左开右闭区间 (l i) (u i)
  证明: by
  rw [mk']; split_ifs with h
  · exact coe_eq_pi _
  · rcases not_forall.mp h with ⟨i, hi⟩
    rw [coe_bot]; rw [univ_pi_eq_empty]
    exact Ioc_eq_empty hi

Depends on / 依赖: Ioc_eq_empty, coe_bot, coe_eq_pi, not_forall, not_forall.mp, split_ifs, univ_pi_eq_empty
-/
theorem coe_mk' (l u : ι -> Real) : (mk' l u : Set (ι -> Real)) = pi univ fun i => Ioc (l i) (u i) := by
  rw [mk']; split_ifs with h
  · exact coe_eq_pi _
  · rcases not_forall.mp h with ⟨i, hi⟩
    rw [coe_bot]; rw [univ_pi_eq_empty]
    exact Ioc_eq_empty hi

/--
Instance `WithBot.inf` / 实例 `WithBot.inf`

English:
instance WithBot.inf
  signature: : Min (WithBot (Box ι))
  body: ⟨fun I =>
    WithBot.recBotCoe (fun _ => ⊥)
      (fun I J => WithBot.recBotCoe ⊥ (fun J => mk' (I.lower ⊔ J.lower) (I.upper ⊓ J.upper)) J) I⟩

@[simp]

中文:
实例 WithBot.下确界
  签名: : 最小值 (WithBot (Box ι))
  定义体: ⟨fun I =>
    WithBot.recBotCoe (fun _ => ⊥)
      (fun I J => WithBot.recBotCoe ⊥ (fun J => mk' (I.lower ⊔ J.lower) (I.upper ⊓ J.upper)) J) I⟩

@[simp]

Depends on / 依赖: I.lower, I.upper, J.lower, J.upper, WithBot, WithBot.recBotCoe, recBotCoe
-/
instance WithBot.inf : Min (WithBot (Box ι)) :=
  ⟨fun I =>
    WithBot.recBotCoe (fun _ => ⊥)
      (fun I J => WithBot.recBotCoe ⊥ (fun J => mk' (I.lower ⊔ J.lower) (I.upper ⊓ J.upper)) J) I⟩

@[simp]
/--
theorem `coe_inf` / 定理 `coe_inf`

English:
theorem coe_inf
  given: (I J : WithBot (Box ι))
  statement: (↑(I ⊓ J) : Set (ι -> Real)) = (I : Set _) inter J
  proof: by
  induction I
  · change ∅ = _
    simp
  induction J
  · change ∅ = _
    simp
  change ((mk' _ _ : WithBot (Box ι)) : Set (ι -> Real)) = _
  simp only [coe_eq_pi, ← pi_inter_distrib, Ioc_inter_Ioc, Pi.sup_apply, Pi.inf_apply, coe_mk',
    coe_coe]

中文:
定理 coe_inf
  条件: (I J : WithBot (Box ι))
  结论: (↑(I ⊓ J) : 集合 (ι -> 实数)) = (I : 集合 _) inter J
  证明: by
  induction I
  · change ∅ = _
    simp
  induction J
  · change ∅ = _
    simp
  change ((mk' _ _ : WithBot (Box ι)) : Set (ι -> Real)) = _
  simp only [coe_eq_pi, ← pi_inter_distrib, Ioc_inter_Ioc, Pi.sup_apply, Pi.inf_apply, coe_mk',
    coe_coe]

Depends on / 依赖: Ioc_inter_Ioc, Pi.inf_apply, Pi.sup_apply, WithBot, coe_coe, coe_eq_pi, coe_mk, inf_apply, pi_inter_distrib, sup_apply
-/
theorem coe_inf (I J : WithBot (Box ι)) : (↑(I ⊓ J) : Set (ι -> Real)) = (I : Set _) inter J := by
  induction I
  · change ∅ = _
    simp
  induction J
  · change ∅ = _
    simp
  change ((mk' _ _ : WithBot (Box ι)) : Set (ι -> Real)) = _
  simp only [coe_eq_pi, ← pi_inter_distrib, Ioc_inter_Ioc, Pi.sup_apply, Pi.inf_apply, coe_mk',
    coe_coe]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Lattice (WithBot (Box ι))
  body: { inf := min
    inf_le_left := fun I J => by
      rw [← withBotCoe_subset_iff]; rw [coe_inf]
      exact inter_subset_left
    inf_le_right := fun I J => by
      rw [← withBotCoe_subset_iff]; rw [coe_inf]
      exact inter_subset_right
    le_inf := fun I J₁ J₂ h₁ h₂ => by
      simp only [← with

中文:
实例 :
  签名: 格 (WithBot (Box ι))
  定义体: { inf := min
    inf_le_left := fun I J => by
      rw [← withBotCoe_subset_iff]; rw [coe_inf]
      exact inter_subset_left
    inf_le_right := fun I J => by
      rw [← withBotCoe_subset_iff]; rw [coe_inf]
      exact inter_subset_right
    le_inf := fun I J₁ J₂ h₁ h₂ => by
      simp only [← with

Depends on / 依赖: coe_inf, inf_le_left, inf_le_right, inter_subset_left, inter_subset_right, le_inf, subset_inter, withBotCoe_subset_iff
-/
instance : Lattice (WithBot (Box ι)) :=
  { inf := min
    inf_le_left := fun I J => by
      rw [← withBotCoe_subset_iff]; rw [coe_inf]
      exact inter_subset_left
    inf_le_right := fun I J => by
      rw [← withBotCoe_subset_iff]; rw [coe_inf]
      exact inter_subset_right
    le_inf := fun I J₁ J₂ h₁ h₂ => by
      simp only [← withBotCoe_subset_iff, coe_inf] at *
      exact subset_inter h₁ h₂ }

@[simp, norm_cast]
/--
theorem `disjoint_withBotCoe` / 定理 `disjoint_withBotCoe`

English:
theorem disjoint_withBotCoe
  given: {I J : WithBot (Box ι)}
  proof: by
  simp only [disjoint_iff_inf_le, ← withBotCoe_subset_iff, coe_inf]
  rfl

中文:
定理 disjoint_withBotCoe
  条件: {I J : WithBot (Box ι)}
  证明: by
  simp only [disjoint_iff_inf_le, ← withBotCoe_subset_iff, coe_inf]
  rfl

Depends on / 依赖: coe_inf, disjoint_iff_inf_le, withBotCoe_subset_iff
-/
theorem disjoint_withBotCoe {I J : WithBot (Box ι)} :
    Disjoint (I : Set (ι -> Real)) J ↔ Disjoint I J := by
  simp only [disjoint_iff_inf_le, ← withBotCoe_subset_iff, coe_inf]
  rfl

/--
theorem `disjoint_coe` / 定理 `disjoint_coe`

English:
theorem disjoint_coe
  statement: Disjoint (I : WithBot (Box ι)) J ↔ Disjoint (I : Set (ι -> Real)) J
  proof: disjoint_withBotCoe.symm

中文:
定理 disjoint_coe
  结论: Disjoint (I : WithBot (Box ι)) J ↔ Disjoint (I : 集合 (ι -> 实数)) J
  证明: disjoint_withBotCoe.symm

Depends on / 依赖: disjoint_withBotCoe, disjoint_withBotCoe.symm
-/
theorem disjoint_coe : Disjoint (I : WithBot (Box ι)) J ↔ Disjoint (I : Set (ι -> Real)) J :=
  disjoint_withBotCoe.symm

/--
theorem `not_disjoint_coe_iff_nonempty_inter` / 定理 `not_disjoint_coe_iff_nonempty_inter`

English:
theorem not_disjoint_coe_iff_nonempty_inter
  proof: by
  rw [disjoint_coe]; rw [Set.not_disjoint_iff_nonempty_inter]

中文:
定理 not_disjoint_coe_iff_nonempty_inter
  证明: by
  rw [disjoint_coe]; rw [Set.not_disjoint_iff_nonempty_inter]

Depends on / 依赖: Set.not_disjoint_iff_nonempty_inter, disjoint_coe, not_disjoint_iff_nonempty_inter
-/
theorem not_disjoint_coe_iff_nonempty_inter :
    ¬Disjoint (I : WithBot (Box ι)) J ↔ (I inter J : Set (ι -> Real)).Nonempty := by
  rw [disjoint_coe]; rw [Set.not_disjoint_iff_nonempty_inter]

/-!
### Hyperface of a box in `ℝⁿ⁺¹ = Fin (n + 1) → ℝ`
-/


/-- Face of a box in `ℝⁿ⁺¹ = Fin (n + 1) → ℝ`: the box in `ℝⁿ = Fin n → ℝ` with corners at
`I.lower ∘ Fin.succAbove i` and `I.upper ∘ Fin.succAbove i`. -/
@[simps +simpRhs]
/--
Definition of `face` / `face` 的定义

English:
definition face
  signature: {n} (I : Box (Fin (n + 1))) (i : Fin (n + 1))
  body: ⟨I.lower ∘ Fin.succAbove i, I.upper ∘ Fin.succAbove i, fun _ => I.lower_lt_upper _⟩

@[simp]

中文:
定义 face
  签名: {n} (I : Box (有限集 (n + 1))) (i : 有限集 (n + 1))
  定义体: ⟨I.lower ∘ Fin.succAbove i, I.upper ∘ Fin.succAbove i, fun _ => I.lower_lt_upper _⟩

@[simp]

Depends on / 依赖: Fin.succAbove, I.lower, I.lower_lt_upper, I.upper, lower_lt_upper, succAbove
-/
def face {n} (I : Box (Fin (n + 1))) (i : Fin (n + 1)) : Box (Fin n) :=
  ⟨I.lower ∘ Fin.succAbove i, I.upper ∘ Fin.succAbove i, fun _ => I.lower_lt_upper _⟩

@[simp]
/--
theorem `face_mk` / 定理 `face_mk`

English:
theorem face_mk
  given: {n} (l u : Fin (n + 1) -> Real) (h : forall i, l i < u i) (i : Fin (n + 1))
  proof: rfl

@[gcongr, mono]

中文:
定理 face_mk
  条件: {n} (l u : 有限集 (n + 1) -> 实数) (h : 对任意 i, l i < u i) (i : 有限集 (n + 1))
  证明: rfl

@[gcongr, mono]
-/
theorem face_mk {n} (l u : Fin (n + 1) -> Real) (h : forall i, l i < u i) (i : Fin (n + 1)) :
    face ⟨l, u, h⟩ i = ⟨l ∘ Fin.succAbove i, u ∘ Fin.succAbove i, fun _ => h _⟩ := rfl

@[gcongr, mono]
/--
theorem `face_mono` / 定理 `face_mono`

English:
theorem face_mono
  given: {n} {I J : Box (Fin (n + 1))} (h : I <= J) (i : Fin (n + 1))
  proof: fun _ hx _ => Ioc_subset_Ioc ((le_iff_bounds.1 h).1 _) ((le_iff_bounds.1 h).2 _) (hx _)

中文:
定理 face_mono
  条件: {n} {I J : Box (有限集 (n + 1))} (h : I <= J) (i : 有限集 (n + 1))
  证明: fun _ hx _ => Ioc_subset_Ioc ((le_iff_bounds.1 h).1 _) ((le_iff_bounds.1 h).2 _) (hx _)

Depends on / 依赖: Ioc_subset_Ioc, le_iff_bounds
-/
theorem face_mono {n} {I J : Box (Fin (n + 1))} (h : I <= J) (i : Fin (n + 1)) :
    face I i <= face J i :=
  fun _ hx _ => Ioc_subset_Ioc ((le_iff_bounds.1 h).1 _) ((le_iff_bounds.1 h).2 _) (hx _)

/--
theorem `monotone_face` / 定理 `monotone_face`

English:
theorem monotone_face
  given: {n} (i : Fin (n + 1))
  statement: Monotone fun I => face I i
  proof: fun _ _ h => face_mono h i

中文:
定理 monotone_face
  条件: {n} (i : 有限集 (n + 1))
  结论: 递增 fun I => face I i
  证明: fun _ _ h => face_mono h i

Depends on / 依赖: face_mono
-/
theorem monotone_face {n} (i : Fin (n + 1)) : Monotone fun I => face I i :=
  fun _ _ h => face_mono h i

/--
theorem `mapsTo_insertNth_face_Icc` / 定理 `mapsTo_insertNth_face_Icc`

English:
theorem mapsTo_insertNth_face_Icc
  statement: {n} (I : Box (Fin (n + 1))) {i : Fin (n + 1)} {x : Real}
  proof: fun _ hy => Fin.insertNth_mem_Icc.2 ⟨hx, hy⟩

中文:
定理 mapsTo_insertNth_face_Icc
  结论: {n} (I : Box (有限集 (n + 1))) {i : 有限集 (n + 1)} {x : 实数}
  证明: fun _ hy => Fin.insertNth_mem_Icc.2 ⟨hx, hy⟩

Depends on / 依赖: Fin.insertNth_mem_Icc, insertNth_mem_Icc
-/
theorem mapsTo_insertNth_face_Icc {n} (I : Box (Fin (n + 1))) {i : Fin (n + 1)} {x : Real}
    (hx : x in Icc (I.lower i) (I.upper i)) :
    MapsTo (i.insertNth x) (Box.Icc (I.face i)) (Box.Icc I) :=
  fun _ hy => Fin.insertNth_mem_Icc.2 ⟨hx, hy⟩

/--
theorem `mapsTo_insertNth_face` / 定理 `mapsTo_insertNth_face`

English:
theorem mapsTo_insertNth_face
  statement: {n} (I : Box (Fin (n + 1))) {i : Fin (n + 1)} {x : Real}
  proof: by
  intro y hy
  simp_rw [mem_coe, mem_def, i.forall_iff_succAbove, Fin.insertNth_apply_same,
    Fin.insertNth_apply_succAbove]
  exact ⟨hx, hy⟩

中文:
定理 mapsTo_insertNth_face
  结论: {n} (I : Box (有限集 (n + 1))) {i : 有限集 (n + 1)} {x : 实数}
  证明: by
  intro y hy
  simp_rw [mem_coe, mem_def, i.forall_iff_succAbove, Fin.insertNth_apply_same,
    Fin.insertNth_apply_succAbove]
  exact ⟨hx, hy⟩

Depends on / 依赖: Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, forall_iff_succAbove, i.forall_iff_succAbove, insertNth_apply_same, insertNth_apply_succAbove, mem_coe, mem_def, simp_rw
-/
theorem mapsTo_insertNth_face {n} (I : Box (Fin (n + 1))) {i : Fin (n + 1)} {x : Real}
    (hx : x in Ioc (I.lower i) (I.upper i)) :
    MapsTo (i.insertNth x) (I.face i : Set (_ -> _)) (I : Set (_ -> _)) := by
  intro y hy
  simp_rw [mem_coe, mem_def, i.forall_iff_succAbove, Fin.insertNth_apply_same,
    Fin.insertNth_apply_succAbove]
  exact ⟨hx, hy⟩

/--
theorem `continuousOn_face_Icc` / 定理 `continuousOn_face_Icc`

English:
theorem continuousOn_face_Icc
  statement: {X} [TopologicalSpace X] {n} {f : (Fin (n + 1) -> Real) -> X}
  proof: h.comp (continuousOn_const.finInsertNth i continuousOn_id) (I.mapsTo_insertNth_face_Icc hx)

中文:
定理 continuousOn_face_Icc
  结论: {X} [拓扑空间 X] {n} {f : (有限集 (n + 1) -> 实数) -> X}
  证明: h.comp (continuousOn_const.finInsertNth i continuousOn_id) (I.mapsTo_insertNth_face_Icc hx)

Depends on / 依赖: I.mapsTo_insertNth_face_Icc, continuousOn_const, continuousOn_const.finInsertNth, continuousOn_id, finInsertNth, h.comp, mapsTo_insertNth_face_Icc
-/
theorem continuousOn_face_Icc {X} [TopologicalSpace X] {n} {f : (Fin (n + 1) -> Real) -> X}
    {I : Box (Fin (n + 1))} (h : ContinuousOn f (Box.Icc I)) {i : Fin (n + 1)} {x : Real}
    (hx : x in Icc (I.lower i) (I.upper i)) :
    ContinuousOn (f ∘ i.insertNth x) (Box.Icc (I.face i)) :=
  h.comp (continuousOn_const.finInsertNth i continuousOn_id) (I.mapsTo_insertNth_face_Icc hx)

/-!
### Covering of the interior of a box by a monotone sequence of smaller boxes
-/


/--
Definition of `Ioo` / `Ioo` 的定义

English:
definition Ioo
  signature: : Box ι ->o Set (ι -> Real) where
  body: pi univ fun i => Ioo (I.lower i) (I.upper i)
  monotone' _ _ h :=
    pi_mono fun i _ => Ioo_subset_Ioo ((le_iff_bounds.1 h).1 i) ((le_iff_bounds.1 h).2 i)

中文:
定义 开区间
  签名: : Box ι ->o 集合 (ι -> 实数) where
  定义体: pi univ fun i => Ioo (I.lower i) (I.upper i)
  monotone' _ _ h :=
    pi_mono fun i _ => Ioo_subset_Ioo ((le_iff_bounds.1 h).1 i) ((le_iff_bounds.1 h).2 i)
-/
protected def Ioo : Box ι ->o Set (ι -> Real) where
  toFun I := pi univ fun i => Ioo (I.lower i) (I.upper i)
  monotone' _ _ h :=
    pi_mono fun i _ => Ioo_subset_Ioo ((le_iff_bounds.1 h).1 i) ((le_iff_bounds.1 h).2 i)

/--
theorem `Ioo_subset_coe` / 定理 `Ioo_subset_coe`

English:
theorem Ioo_subset_coe
  given: (I : Box ι)
  statement: Box.Ioo I subseteq I
  proof: fun _ hx i => Ioo_subset_Ioc_self (hx i trivial)

中文:
定理 Ioo_subset_coe
  条件: (I : Box ι)
  结论: Box.开区间 I subseteq I
  证明: fun _ hx i => Ioo_subset_Ioc_self (hx i trivial)

Depends on / 依赖: Ioo_subset_Ioc_self
-/
theorem Ioo_subset_coe (I : Box ι) : Box.Ioo I subseteq I :=
  fun _ hx i => Ioo_subset_Ioc_self (hx i trivial)

/--
theorem `Ioo_subset_Icc` / 定理 `Ioo_subset_Icc`

English:
theorem Ioo_subset_Icc
  given: (I : Box ι)
  statement: Box.Ioo I subseteq Box.Icc I
  proof: I.Ioo_subset_coe.trans coe_subset_Icc

中文:
定理 Ioo_subset_Icc
  条件: (I : Box ι)
  结论: Box.开区间 I subseteq Box.闭区间 I
  证明: I.Ioo_subset_coe.trans coe_subset_Icc
-/
protected theorem Ioo_subset_Icc (I : Box ι) : Box.Ioo I subseteq Box.Icc I :=
  I.Ioo_subset_coe.trans coe_subset_Icc

/--
theorem `iUnion_Ioo_of_tendsto` / 定理 `iUnion_Ioo_of_tendsto`

English:
theorem iUnion_Ioo_of_tendsto
  statement: [Finite ι] {I : Box ι} {J : Nat -> Box ι} (hJ : Monotone J)
  proof: have hl' : forall i, Antitone fun n => (J n).lower i :=
    fun i => (monotone_eval i).comp_antitone (antitone_lower.comp_monotone hJ)
  have hu' : forall i, Monotone fun n => (J n).upper i :=
    fun i => (monotone_eval i).comp (monotone_upper.comp hJ)
  calc
    ⋃ n, Box.Ioo (J n) = pi univ fun i 

中文:
定理 iUnion_Ioo_of_tendsto
  结论: [有限 ι] {I : Box ι} {J : 自然数 -> Box ι} (hJ : 递增 J)
  证明: have hl' : forall i, Antitone fun n => (J n).lower i :=
    fun i => (monotone_eval i).comp_antitone (antitone_lower.comp_monotone hJ)
  have hu' : forall i, Monotone fun n => (J n).upper i :=
    fun i => (monotone_eval i).comp (monotone_upper.comp hJ)
  calc
    ⋃ n, Box.Ioo (J n) = pi univ fun i 

Depends on / 依赖: Antitone, Box.Ioo, Monotone, antitone_lower, antitone_lower.comp_monotone, comp_antitone, comp_monotone, iUnion_Ioo_of_mono_of_isGLB_of_isLUB, iUnion_univ_pi_of_monotone, isGLB_of_tendsto_a, monotone_eval, monotone_upper, monotone_upper.comp, pi_congr
-/
theorem iUnion_Ioo_of_tendsto [Finite ι] {I : Box ι} {J : Nat -> Box ι} (hJ : Monotone J)
    (hl : Tendsto (lower ∘ J) atTop (𝓝 I.lower)) (hu : Tendsto (upper ∘ J) atTop (𝓝 I.upper)) :
    ⋃ n, Box.Ioo (J n) = Box.Ioo I :=
  have hl' : forall i, Antitone fun n => (J n).lower i :=
    fun i => (monotone_eval i).comp_antitone (antitone_lower.comp_monotone hJ)
  have hu' : forall i, Monotone fun n => (J n).upper i :=
    fun i => (monotone_eval i).comp (monotone_upper.comp hJ)
  calc
    ⋃ n, Box.Ioo (J n) = pi univ fun i => ⋃ n, Ioo ((J n).lower i) ((J n).upper i) :=
      iUnion_univ_pi_of_monotone fun i => (hl' i).Ioo (hu' i)
    _ = Box.Ioo I :=
      pi_congr rfl fun i _ =>
        iUnion_Ioo_of_mono_of_isGLB_of_isLUB (hl' i) (hu' i)
          (isGLB_of_tendsto_atTop (hl' i) (tendsto_pi_nhds.1 hl _))
          (isLUB_of_tendsto_atTop (hu' i) (tendsto_pi_nhds.1 hu _))

/--
theorem `exists_seq_mono_tendsto` / 定理 `exists_seq_mono_tendsto`

English:
theorem exists_seq_mono_tendsto
  given: (I : Box ι)
  proof: by
  choose a b ha_anti hb_mono ha_mem hb_mem hab ha_tendsto hb_tendsto using
    fun i => exists_seq_strictAnti_strictMono_tendsto (I.lower_lt_upper i)
  exact
    ⟨⟨fun k => ⟨flip a k, flip b k, fun i => hab _ _ _⟩, fun k l hkl =>
        le_iff_bounds.2 ⟨fun i => (ha_anti i).antitone hkl, fun i =

中文:
定理 存在_seq_mono_tendsto
  条件: (I : Box ι)
  证明: by
  choose a b ha_anti hb_mono ha_mem hb_mem hab ha_tendsto hb_tendsto using
    fun i => exists_seq_strictAnti_strictMono_tendsto (I.lower_lt_upper i)
  exact
    ⟨⟨fun k => ⟨flip a k, flip b k, fun i => hab _ _ _⟩, fun k l hkl =>
        le_iff_bounds.2 ⟨fun i => (ha_anti i).antitone hkl, fun i =

Depends on / 依赖: I.lower_lt_upper, antitone, exists_seq_strictAnti_strictMono_tendsto, ha_anti, ha_mem, ha_tendsto, hb_mem, hb_mono, hb_tendsto, le_iff_bounds, lower_lt_upper, monotone, tendsto_pi_nhds, trans_le, trans_lt
-/
theorem exists_seq_mono_tendsto (I : Box ι) :
    exists J : Nat ->o Box ι,
      (forall n, Box.Icc (J n) subseteq Box.Ioo I) ∧
        Tendsto (lower ∘ J) atTop (𝓝 I.lower) ∧ Tendsto (upper ∘ J) atTop (𝓝 I.upper) := by
  choose a b ha_anti hb_mono ha_mem hb_mem hab ha_tendsto hb_tendsto using
    fun i => exists_seq_strictAnti_strictMono_tendsto (I.lower_lt_upper i)
  exact
    ⟨⟨fun k => ⟨flip a k, flip b k, fun i => hab _ _ _⟩, fun k l hkl =>
        le_iff_bounds.2 ⟨fun i => (ha_anti i).antitone hkl, fun i => (hb_mono i).monotone hkl⟩⟩,
      fun n x hx i _ => ⟨(ha_mem _ _).1.trans_le (hx.1 _), (hx.2 _).trans_lt (hb_mem _ _).2⟩,
      tendsto_pi_nhds.2 ha_tendsto, tendsto_pi_nhds.2 hb_tendsto⟩

section Distortion

variable [Fintype ι]

/--
Definition of `distortion` / `distortion` 的定义

English:
definition distortion
  signature: (I : Box ι)
  body: Finset.univ.sup fun i : ι => nndist I.lower I.upper / nndist (I.lower i) (I.upper i)

中文:
定义 distortion
  签名: (I : Box ι)
  定义体: Finset.univ.sup fun i : ι => nndist I.lower I.upper / nndist (I.lower i) (I.upper i)

Depends on / 依赖: Finset, Finset.univ.sup, I.lower, I.upper, nndist
-/
def distortion (I : Box ι) : Real>=0 :=
  Finset.univ.sup fun i : ι => nndist I.lower I.upper / nndist (I.lower i) (I.upper i)

/--
theorem `distortion_eq_of_sub_eq_div` / 定理 `distortion_eq_of_sub_eq_div`

English:
theorem distortion_eq_of_sub_eq_div
  statement: {I J : Box ι} {r : Real}
  proof: by
  simp only [distortion, nndist_pi_def, Real.nndist_eq', h, map_div₀]
  congr 1 with i
  have : 0 < r := by
    by_contra hr
    have := div_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 <| J.lower_le_upper i) (not_lt.1 hr)
    rw [← h] at this
    exact this.not_gt (sub_pos.2 <| I.lower_lt_upper i)
 

中文:
定理 distortion_eq_of_sub_eq_div
  结论: {I J : Box ι} {r : 实数}
  证明: by
  simp only [distortion, nndist_pi_def, Real.nndist_eq', h, map_div₀]
  congr 1 with i
  have : 0 < r := by
    by_contra hr
    have := div_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 <| J.lower_le_upper i) (not_lt.1 hr)
    rw [← h] at this
    exact this.not_gt (sub_pos.2 <| I.lower_lt_upper i)
 

Depends on / 依赖: I.lower_lt_upper, J.lower_le_upper, NNReal, NNReal.finset_sup_div, Real.nnabs, Real.nndist_eq, distortion, div_nonpos_of_nonneg_of_nonpos, finset_sup_div, lower_le_upper, lower_lt_upper, map_ne_zero, nndist_eq, nndist_pi_def, not_gt, not_lt, simp_rw, sub_nonneg, sub_pos, this.ne
-/
theorem distortion_eq_of_sub_eq_div {I J : Box ι} {r : Real}
    (h : forall i, I.upper i - I.lower i = (J.upper i - J.lower i) / r) :
    distortion I = distortion J := by
  simp only [distortion, nndist_pi_def, Real.nndist_eq', h, map_div₀]
  congr 1 with i
  have : 0 < r := by
    by_contra hr
    have := div_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 <| J.lower_le_upper i) (not_lt.1 hr)
    rw [← h] at this
    exact this.not_gt (sub_pos.2 <| I.lower_lt_upper i)
  have hn0 := (map_ne_zero Real.nnabs).2 this.ne'
  simp_rw [NNReal.finset_sup_div, div_div_div_cancel_right₀ hn0]

/--
theorem `nndist_le_distortion_mul` / 定理 `nndist_le_distortion_mul`

English:
theorem nndist_le_distortion_mul
  given: (I : Box ι) (i : ι)
  proof: calc
    nndist I.lower I.upper =
        nndist I.lower I.upper / nndist (I.lower i) (I.upper i) * nndist (I.lower i) (I.upper i) :=
      (div_mul_cancel₀ _ <| mt nndist_eq_zero.1 (I.lower_lt_upper i).ne).symm
    _ <= I.distortion * nndist (I.lower i) (I.upper i) := by
      grw [distortion, ← Fi

中文:
定理 nndist_le_distortion_mul
  条件: (I : Box ι) (i : ι)
  证明: calc
    nndist I.lower I.upper =
        nndist I.lower I.upper / nndist (I.lower i) (I.upper i) * nndist (I.lower i) (I.upper i) :=
      (div_mul_cancel₀ _ <| mt nndist_eq_zero.1 (I.lower_lt_upper i).ne).symm
    _ <= I.distortion * nndist (I.lower i) (I.upper i) := by
      grw [distortion, ← Fi

Depends on / 依赖: Finset, Finset.le_sup, Finset.mem_univ, I.distortion, I.lower, I.lower_lt_upper, I.upper, distortion, le_sup, lower_lt_upper, mem_univ, nndist, nndist_eq_zero
-/
theorem nndist_le_distortion_mul (I : Box ι) (i : ι) :
    nndist I.lower I.upper <= I.distortion * nndist (I.lower i) (I.upper i) :=
  calc
    nndist I.lower I.upper =
        nndist I.lower I.upper / nndist (I.lower i) (I.upper i) * nndist (I.lower i) (I.upper i) :=
      (div_mul_cancel₀ _ <| mt nndist_eq_zero.1 (I.lower_lt_upper i).ne).symm
    _ <= I.distortion * nndist (I.lower i) (I.upper i) := by
      grw [distortion, ← Finset.le_sup (Finset.mem_univ i)]

/--
theorem `dist_le_distortion_mul` / 定理 `dist_le_distortion_mul`

English:
theorem dist_le_distortion_mul
  given: (I : Box ι) (i : ι)
  proof: by
  have A : I.lower i - I.upper i < 0 := sub_neg.2 (I.lower_lt_upper i)
  simpa only [← NNReal.coe_le_coe, ← dist_nndist, NNReal.coe_mul, Real.dist_eq, abs_of_neg A,
    neg_sub] using I.nndist_le_distortion_mul i

中文:
定理 dist_le_distortion_mul
  条件: (I : Box ι) (i : ι)
  证明: by
  have A : I.lower i - I.upper i < 0 := sub_neg.2 (I.lower_lt_upper i)
  simpa only [← NNReal.coe_le_coe, ← dist_nndist, NNReal.coe_mul, Real.dist_eq, abs_of_neg A,
    neg_sub] using I.nndist_le_distortion_mul i

Depends on / 依赖: I.lower, I.lower_lt_upper, I.nndist_le_distortion_mul, I.upper, NNReal, NNReal.coe_le_coe, NNReal.coe_mul, Real.dist_eq, abs_of_neg, coe_le_coe, coe_mul, dist_eq, dist_nndist, lower_lt_upper, neg_sub, nndist_le_distortion_mul, sub_neg
-/
theorem dist_le_distortion_mul (I : Box ι) (i : ι) :
    dist I.lower I.upper <= I.distortion * (I.upper i - I.lower i) := by
  have A : I.lower i - I.upper i < 0 := sub_neg.2 (I.lower_lt_upper i)
  simpa only [← NNReal.coe_le_coe, ← dist_nndist, NNReal.coe_mul, Real.dist_eq, abs_of_neg A,
    neg_sub] using I.nndist_le_distortion_mul i

/--
theorem `diam_Icc_le_of_distortion_le` / 定理 `diam_Icc_le_of_distortion_le`

English:
theorem diam_Icc_le_of_distortion_le
  given: (I : Box ι) (i : ι) {c : Real>=0} (h : I.distortion <= c)
  proof: have : (0 : Real) <= c * (I.upper i - I.lower i) :=
    mul_nonneg c.coe_nonneg (sub_nonneg.2 <| I.lower_le_upper _)
  diam_le_of_forall_dist_le this fun x hx y hy =>
    calc
      dist x y <= dist I.lower I.upper := Real.dist_le_of_mem_pi_Icc hx hy
      _ <= I.distortion * (I.upper i - I.lower i)

中文:
定理 diam_Icc_le_of_distortion_le
  条件: (I : Box ι) (i : ι) {c : 实数>=0} (h : I.distortion <= c)
  证明: have : (0 : Real) <= c * (I.upper i - I.lower i) :=
    mul_nonneg c.coe_nonneg (sub_nonneg.2 <| I.lower_le_upper _)
  diam_le_of_forall_dist_le this fun x hx y hy =>
    calc
      dist x y <= dist I.lower I.upper := Real.dist_le_of_mem_pi_Icc hx hy
      _ <= I.distortion * (I.upper i - I.lower i)

Depends on / 依赖: I.dist_le_distortion_mul, I.distortion, I.lower, I.lower_le_upper, I.upper, Real.dist_le_of_mem_pi_Icc, c.coe_nonneg, coe_nonneg, diam_le_of_forall_dist_le, dist_le_distortion_mul, dist_le_of_mem_pi_Icc, distortion, lower_le_upper, mul_nonneg, sub_nonneg
-/
theorem diam_Icc_le_of_distortion_le (I : Box ι) (i : ι) {c : Real>=0} (h : I.distortion <= c) :
    diam (Box.Icc I) <= c * (I.upper i - I.lower i) :=
  have : (0 : Real) <= c * (I.upper i - I.lower i) :=
    mul_nonneg c.coe_nonneg (sub_nonneg.2 <| I.lower_le_upper _)
  diam_le_of_forall_dist_le this fun x hx y hy =>
    calc
      dist x y <= dist I.lower I.upper := Real.dist_le_of_mem_pi_Icc hx hy
      _ <= I.distortion * (I.upper i - I.lower i) := I.dist_le_distortion_mul i
      _ <= c * (I.upper i - I.lower i) := by gcongr; exact sub_nonneg.2 (I.lower_le_upper i)

end Distortion

end Box

end BoxIntegral
