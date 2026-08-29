/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.BoxIntegral.Partition.SubboxInduction
public import Mathlib.Analysis.BoxIntegral.Partition.Split

/-!
# Filters used in box-based integrals

First we define a structure `BoxIntegral.IntegrationParams`. This structure will be used as an
argument in the definition of `BoxIntegral.integral` in order to use the same definition for a few
well-known definitions of integrals based on partitions of a rectangular box into subboxes (Riemann
integral, Henstock-Kurzweil integral, and McShane integral).

This structure holds three Boolean values (see below), and encodes eight different sets of
parameters; only four of these values are used somewhere in `mathlib4`. Three of them correspond to
the integration theories listed above, and one is a generalization of the one-dimensional
Henstock-Kurzweil integral such that the divergence theorem works without additional integrability
assumptions.

Finally, for each set of parameters `l : BoxIntegral.IntegrationParams` and a rectangular box
`I : BoxIntegral.Box ι`, we define several `Filter`s that will be used either in the definition of
the corresponding integral, or in the proofs of its properties. We equip
`BoxIntegral.IntegrationParams` with a `BoundedOrder` structure such that larger
`IntegrationParams` produce larger filters.

## Main definitions

### Integration parameters

The structure `BoxIntegral.IntegrationParams` has 3 Boolean fields with the following meaning:

* `bRiemann`: the value `true` means that the filter corresponds to a Riemann-style integral, i.e.
  in the definition of integrability we require a constant upper estimate `r` on the size of boxes
  of a tagged partition; the value `false` means that the estimate may depend on the position of the
  tag.

* `bHenstock`: the value `true` means that we require that each tag belongs to its own closed box;
  the value `false` means that we only require that tags belong to the ambient box.

* `bDistortion`: the value `true` means that `r` can depend on the maximal ratio of sides of the
  same box of a partition. Presence of this case make quite a few proofs harder but we can prove the
  divergence theorem only for the filter `BoxIntegral.IntegrationParams.GP = ⊥ =
  {bRiemann := false, bHenstock := true, bDistortion := true}`.

### Well-known sets of parameters

Out of eight possible values of `BoxIntegral.IntegrationParams`, the following four are used in
the library.

* `BoxIntegral.IntegrationParams.Riemann` (`bRiemann = true`, `bHenstock = true`,
  `bDistortion = false`): this value corresponds to the Riemann integral; in the corresponding
  filter, we require that the diameters of all boxes `J` of a tagged partition are bounded from
  above by a constant upper estimate that may not depend on the geometry of `J`, and each tag
  belongs to the corresponding closed box.

* `BoxIntegral.IntegrationParams.Henstock` (`bRiemann = false`, `bHenstock = true`,
  `bDistortion = false`): this value corresponds to the most natural generalization of
  Henstock-Kurzweil integral to higher dimension; the only (but important!) difference between this
  theory and Riemann integral is that instead of a constant upper estimate on the size of all boxes
  of a partition, we require that the partition is *subordinate* to a possibly discontinuous
  function `r : (ι → ℝ) → {x : ℝ | 0 < x}`, i.e. each box `J` is included in a closed ball with
  center `π.tag J` and radius `r J`.

* `BoxIntegral.IntegrationParams.McShane` (`bRiemann = false`, `bHenstock = false`,
  `bDistortion = false`): this value corresponds to the McShane integral; the only difference with
  the Henstock integral is that we allow tags to be outside of their boxes; the tags still have to
  be in the ambient closed box, and the partition still has to be subordinate to a function.

* `BoxIntegral.IntegrationParams.GP = ⊥` (`bRiemann = false`, `bHenstock = true`,
  `bDistortion = true`): this is the least integration theory in our list, i.e., all functions
  integrable in any other theory is integrable in this one as well. This is a non-standard
  generalization of the Henstock-Kurzweil integral to higher dimension. In dimension one, it
  generates the same filter as `Henstock`. In higher dimension, this generalization defines an
  integration theory such that the divergence of any Fréchet differentiable function `f` is
  integrable, and its integral is equal to the sum of integrals of `f` over the faces of the box,
  taken with appropriate signs.

  A function `f` is `GP`-integrable if for any `ε > 0` and `c : ℝ≥0` there exists
  `r : (ι → ℝ) → {x : ℝ | 0 < x}` such that for any tagged partition `π` subordinate to `r`, if each
  tag belongs to the corresponding closed box and for each box `J ∈ π`, the maximal ratio of its
  sides is less than or equal to `c`, then the integral sum of `f` over `π` is `ε`-close to the
  integral.

### Filters and predicates on `TaggedPrepartition I`

For each value of `IntegrationParams` and a rectangular box `I`, we define a few filters on
`TaggedPrepartition I`. First, we define a predicate

```
structure BoxIntegral.IntegrationParams.MemBaseSet (l : BoxIntegral.IntegrationParams)
  (I : BoxIntegral.Box ι) (c : ℝ≥0) (r : (ι → ℝ) → Ioi (0 : ℝ))
  (π : BoxIntegral.TaggedPrepartition I) : Prop where
```

This predicate says that

* if `l.bHenstock`, then `π` is a Henstock prepartition, i.e. each tag belongs to the corresponding
  closed box;
* `π` is subordinate to `r`;
* if `l.bDistortion`, then the distortion of each box in `π` is less than or equal to `c`;
* if `l.bDistortion`, then there exists a prepartition `π'` with distortion `≤ c` that covers
  exactly `I \ π.iUnion`.

The last condition is always true for `c > 1`, see TODO section for more details.

Then we define a predicate `BoxIntegral.IntegrationParams.RCond` on functions
`r : (ι → ℝ) → {x : ℝ | 0 < x}`. If `l.bRiemann`, then this predicate requires `r` to be a constant
function, otherwise it imposes no restrictions on `r`. We introduce this definition to prove a few
dot-notation lemmas: e.g., `BoxIntegral.IntegrationParams.RCond.min` says that the pointwise
minimum of two functions that satisfy this condition satisfies this condition as well.

Then we define four filters on `BoxIntegral.TaggedPrepartition I`.

* `BoxIntegral.IntegrationParams.toFilterDistortion`: an auxiliary filter that takes parameters
  `(l : BoxIntegral.IntegrationParams) (I : BoxIntegral.Box ι) (c : ℝ≥0)` and returns the
  filter generated by all sets `{π | MemBaseSet l I c r π}`, where `r` is a function satisfying
  the predicate `BoxIntegral.IntegrationParams.RCond l`;

* `BoxIntegral.IntegrationParams.toFilter l I`: the supremum of `l.toFilterDistortion I c`
  over all `c : ℝ≥0`;

* `BoxIntegral.IntegrationParams.toFilterDistortioniUnion l I c π₀`, where `π₀` is a
  prepartition of `I`: the infimum of `l.toFilterDistortion I c` and the principal filter
  generated by `{π | π.iUnion = π₀.iUnion}`;

* `BoxIntegral.IntegrationParams.toFilteriUnion l I π₀`: the supremum of
  `l.toFilterDistortioniUnion l I c π₀` over all `c : ℝ≥0`. This is the filter (in the case
  `π₀ = ⊤` is the one-box partition of `I`) used in the definition of the integral of a function
  over a box.

## Implementation details

* Later we define the integral of a function over a rectangular box as the limit (if it exists) of
  the integral sums along `BoxIntegral.IntegrationParams.toFilteriUnion l I ⊤`. While it is
  possible to define the integral with a general filter on `BoxIntegral.TaggedPrepartition I` as a
  parameter, many lemmas (e.g., Sacks-Henstock lemma and most results about integrability of
  functions) require the filter to have a predictable structure. So, instead of adding assumptions
  about the filter here and there, we define this auxiliary type that can encode all integration
  theories we need in practice.

* While the definition of the integral only uses the filter
  `BoxIntegral.IntegrationParams.toFilteriUnion l I ⊤` and partitions of a box, some lemmas
  (e.g., the Henstock-Sacks lemmas) are best formulated in terms of the predicate `MemBaseSet` and
  other filters defined above.

* We use `Bool` instead of `Prop` for the fields of `IntegrationParams` in order to have decidable
  equality and inequalities.

## TODO

Currently, `BoxIntegral.IntegrationParams.MemBaseSet` explicitly requires that there exists a
partition of the complement `I \ π.iUnion` with distortion `≤ c`. For `c > 1`, this condition is
always true but the proof of this fact requires more API about
`BoxIntegral.Prepartition.splitMany`. We should formalize this fact, then either require `c > 1`
everywhere, or replace `≤ c` with `< c` so that we automatically get `c > 1` for a non-trivial
prepartition (and consider the special case `π = ⊥` separately if needed).

## Tags

integral, rectangular box, partition, filter
-/

@[expose] public section

open Set Function Filter Metric Finset Bool
open scoped Topology Filter NNReal

noncomputable section

namespace BoxIntegral

variable {ι : Type*} [Fintype ι] {I J : Box ι} {c c₁ c₂ : Real>=0}

open TaggedPrepartition

/-- An `IntegrationParams` is a structure holding 3 Boolean values used to define a filter to be
used in the definition of a box-integrable function.
-/
@[ext]
/--
Definition of `IntegrationParams` / `IntegrationParams` 的定义

English:
structure IntegrationParams
  parameters: : Type where
  axioms and operations (3):
    - (bRiemann : Bool)
    - (bHenstock : Bool)
    - (bDistortion : Bool)

中文:
结构 整数egrationParams
  参数: : 类型 where
  公理与运算 (3 个):
    - (bRiemann : 布尔值)
    - (bHenstock : 布尔值)
    - (bDistortion : 布尔值)

Depends on / 依赖: bDistortion, bHenstock
-/
structure IntegrationParams : Type where
  /-- `true` if the filter corresponds to a Riemann-style integral,
  i.e. in the definition of integrability we require a constant upper estimate `r` on the size of
  boxes of a tagged partition; the value `false` means that the estimate may depend on the position
  of the tag. -/
  (bRiemann : Bool)
  /-- `true` if we require that each tag belongs to its own closed
  box; the value `false` means that we only require that tags belong to the ambient box. -/
  (bHenstock : Bool)
  /-- `true` if `r` can depend on the maximal ratio of sides of the
  same box of a partition. Presence of this case makes quite a few proofs harder but we can prove
  the divergence theorem only for the filter `BoxIntegral.IntegrationParams.GP = ⊥ =
  {bRiemann := false, bHenstock := true, bDistortion := true}`. -/
  (bDistortion : Bool)

variable {l l₁ l₂ : IntegrationParams}

namespace IntegrationParams

/--
Definition of `equivProd` / `equivProd` 的定义

English:
definition equivProd
  signature: : IntegrationParams ≃ Bool × Boolᵒᵈ × Boolᵒᵈ where
  body: ⟨l.1, OrderDual.toDual l.2, OrderDual.toDual l.3⟩
  invFun l := ⟨l.1, OrderDual.ofDual l.2.1, OrderDual.ofDual l.2.2⟩

中文:
定义 equivProd
  签名: : 整数egrationParams ≃ 布尔值 × 布尔ᵒᵈ × 布尔ᵒᵈ where
  定义体: ⟨l.1, OrderDual.toDual l.2, OrderDual.toDual l.3⟩
  invFun l := ⟨l.1, OrderDual.ofDual l.2.1, OrderDual.ofDual l.2.2⟩

Depends on / 依赖: OrderDual, OrderDual.toDual, toDual
-/
def equivProd : IntegrationParams ≃ Bool × Boolᵒᵈ × Boolᵒᵈ where
  toFun l := ⟨l.1, OrderDual.toDual l.2, OrderDual.toDual l.3⟩
  invFun l := ⟨l.1, OrderDual.ofDual l.2.1, OrderDual.ofDual l.2.2⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder IntegrationParams
  body: PartialOrder.lift equivProd equivProd.injective

中文:
实例 :
  签名: 偏序 整数egrationParams
  定义体: PartialOrder.lift equivProd equivProd.injective

Depends on / 依赖: PartialOrder, PartialOrder.lift, equivProd, equivProd.injective, injective
-/
instance : PartialOrder IntegrationParams :=
  PartialOrder.lift equivProd equivProd.injective

/--
Definition of `isoProd` / `isoProd` 的定义

English:
definition isoProd
  signature: : IntegrationParams ≃o Bool × Boolᵒᵈ × Boolᵒᵈ
  body: ⟨equivProd, Iff.rfl⟩

中文:
定义 isoProd
  签名: : 整数egrationParams ≃o 布尔值 × 布尔ᵒᵈ × 布尔ᵒᵈ
  定义体: ⟨equivProd, Iff.rfl⟩

Depends on / 依赖: Iff.rfl, equivProd
-/
def isoProd : IntegrationParams ≃o Bool × Boolᵒᵈ × Boolᵒᵈ :=
  ⟨equivProd, Iff.rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BoundedOrder IntegrationParams
  body: isoProd.symm.toGaloisInsertion.liftBoundedOrder

中文:
实例 :
  签名: 有界序 整数egrationParams
  定义体: isoProd.symm.toGaloisInsertion.liftBoundedOrder

Depends on / 依赖: isoProd, isoProd.symm.toGaloisInsertion.liftBoundedOrder, liftBoundedOrder, toGaloisInsertion
-/
instance : BoundedOrder IntegrationParams :=
  isoProd.symm.toGaloisInsertion.liftBoundedOrder

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited IntegrationParams
  body: ⟨⊥⟩

中文:
实例 :
  签名: 可居 整数egrationParams
  定义体: ⟨⊥⟩
-/
instance : Inhabited IntegrationParams :=
  ⟨⊥⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DecidableLE (IntegrationParams)
  body: fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

中文:
实例 :
  签名: DecidableLE (整数egrationParams)
  定义体: fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

Depends on / 依赖: Decidable
-/
instance : DecidableLE (IntegrationParams) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DecidableEq IntegrationParams
  body: fun _ _ => decidable_of_iff _ IntegrationParams.ext_iff.symm

中文:
实例 :
  签名: DecidableEq 整数egrationParams
  定义体: fun _ _ => decidable_of_iff _ IntegrationParams.ext_iff.symm

Depends on / 依赖: IntegrationParams, IntegrationParams.ext_iff.symm, decidable_of_iff, ext_iff
-/
instance : DecidableEq IntegrationParams :=
  fun _ _ => decidable_of_iff _ IntegrationParams.ext_iff.symm

/--
Definition of `Riemann` / `Riemann` 的定义

English:
definition Riemann
  signature: : IntegrationParams where
  body: true
  bHenstock := true
  bDistortion := false

中文:
定义 Riemann
  签名: : 整数egrationParams where
  定义体: true
  bHenstock := true
  bDistortion := false
-/
def Riemann : IntegrationParams where
  bRiemann := true
  bHenstock := true
  bDistortion := false

/--
Definition of `Henstock` / `Henstock` 的定义

English:
definition Henstock
  signature: : IntegrationParams
  body: ⟨false, true, false⟩

中文:
定义 Henstock
  签名: : 整数egrationParams
  定义体: ⟨false, true, false⟩
-/
def Henstock : IntegrationParams :=
  ⟨false, true, false⟩

/--
Definition of `McShane` / `McShane` 的定义

English:
definition McShane
  signature: : IntegrationParams
  body: ⟨false, false, false⟩

中文:
定义 McShane
  签名: : 整数egrationParams
  定义体: ⟨false, false, false⟩
-/
def McShane : IntegrationParams :=
  ⟨false, false, false⟩

/--
Definition of `GP` / `GP` 的定义

English:
definition GP
  signature: : IntegrationParams
  body: ⊥

中文:
定义 GP
  签名: : 整数egrationParams
  定义体: ⊥
-/
def GP : IntegrationParams := ⊥

/--
theorem `henstock_le_riemann` / 定理 `henstock_le_riemann`

English:
theorem henstock_le_riemann
  statement: Henstock <= Riemann
  proof: by trivial

中文:
定理 henstock_le_riemann
  结论: Henstock <= Riemann
  证明: by trivial
-/
theorem henstock_le_riemann : Henstock <= Riemann := by trivial

/--
theorem `henstock_le_mcShane` / 定理 `henstock_le_mcShane`

English:
theorem henstock_le_mcShane
  statement: Henstock <= McShane
  proof: by trivial

中文:
定理 henstock_le_mcShane
  结论: Henstock <= McShane
  证明: by trivial
-/
theorem henstock_le_mcShane : Henstock <= McShane := by trivial

/--
theorem `gp_le` / 定理 `gp_le`

English:
theorem gp_le
  statement: GP <= l
  proof: bot_le

中文:
定理 gp_le
  结论: GP <= l
  证明: bot_le

Depends on / 依赖: bot_le
-/
theorem gp_le : GP <= l :=
  bot_le

/--
Definition of `MemBaseSet` / `MemBaseSet` 的定义

English:
structure MemBaseSet
  parameters: (l : IntegrationParams) (I : Box ι) (c : Real>=0) (r : (ι -> Real) -> Ioi (0 : Real))
  axioms and operations (4):
    - isSubordinate : π.IsSubordinate r
    - isHenstock : l.bHenstock -> π.IsHenstock
    - distortion_le : l.bDistortion -> π.distortion <= c
    - exists_compl : l.bDistortion -> exists π' : Prepartition I, π'.iUnion = ↑I \ π.iUnion ∧ π'.distortion <= c

中文:
结构 MemBaseSet
  参数: (l : 整数egrationParams) (I : Box ι) (c : 实数>=0) (r : (ι -> 实数) -> 左开右无界区间 (0 : 实数))
  公理与运算 (4 个):
    - isSubordinate : π.IsSubordinate r
    - isHenstock : l.bHenstock -> π.IsHenstock
    - distortion_le : l.bDistortion -> π.distortion <= c
    - exists_compl : l.bDistortion -> 存在 π' : 预分拆 I, π'.iUnion = ↑I \ π.iUnion ∧ π'.distortion <= c
-/
structure MemBaseSet (l : IntegrationParams) (I : Box ι) (c : Real>=0) (r : (ι -> Real) -> Ioi (0 : Real))
    (π : TaggedPrepartition I) : Prop where
  protected isSubordinate : π.IsSubordinate r
  protected isHenstock : l.bHenstock -> π.IsHenstock
  protected distortion_le : l.bDistortion -> π.distortion <= c
  protected exists_compl : l.bDistortion -> exists π' : Prepartition I,
    π'.iUnion = ↑I \ π.iUnion ∧ π'.distortion <= c

/--
Definition of `RCond` / `RCond` 的定义

English:
definition RCond
  signature: {ι : Type*} (l : IntegrationParams) (r : (ι -> Real) -> Ioi (0 : Real))
  body: l.bRiemann -> forall x, r x = r 0

中文:
定义 RCond
  签名: {ι : 类型} (l : 整数egrationParams) (r : (ι -> 实数) -> 左开右无界区间 (0 : 实数))
  定义体: l.bRiemann -> forall x, r x = r 0

Depends on / 依赖: bRiemann, l.bRiemann
-/
def RCond {ι : Type*} (l : IntegrationParams) (r : (ι -> Real) -> Ioi (0 : Real)) : Prop :=
  l.bRiemann -> forall x, r x = r 0

/--
Definition of `toFilterDistortion` / `toFilterDistortion` 的定义

English:
definition toFilterDistortion
  signature: (l : IntegrationParams) (I : Box ι) (c : Real>=0)
  body: ⨅ (r : (ι -> Real) -> Ioi (0 : Real)) (_ : l.RCond r), 𝓟 { π | l.MemBaseSet I c r π }

中文:
定义 toFilterDistortion
  签名: (l : 整数egrationParams) (I : Box ι) (c : 实数>=0)
  定义体: ⨅ (r : (ι -> Real) -> Ioi (0 : Real)) (_ : l.RCond r), 𝓟 { π | l.MemBaseSet I c r π }

Depends on / 依赖: MemBaseSet, l.MemBaseSet, l.RCond
-/
def toFilterDistortion (l : IntegrationParams) (I : Box ι) (c : Real>=0) :
    Filter (TaggedPrepartition I) :=
  ⨅ (r : (ι -> Real) -> Ioi (0 : Real)) (_ : l.RCond r), 𝓟 { π | l.MemBaseSet I c r π }

/--
Definition of `toFilter` / `toFilter` 的定义

English:
definition toFilter
  signature: (l : IntegrationParams) (I : Box ι)
  body: ⨆ c : Real>=0, l.toFilterDistortion I c

中文:
定义 toFilter
  签名: (l : 整数egrationParams) (I : Box ι)
  定义体: ⨆ c : Real>=0, l.toFilterDistortion I c

Depends on / 依赖: l.toFilterDistortion, toFilterDistortion
-/
def toFilter (l : IntegrationParams) (I : Box ι) : Filter (TaggedPrepartition I) :=
  ⨆ c : Real>=0, l.toFilterDistortion I c

/--
Definition of `toFilterDistortioniUnion` / `toFilterDistortioniUnion` 的定义

English:
definition toFilterDistortioniUnion
  signature: (l : IntegrationParams) (I : Box ι) (c : Real>=0) (π₀ : Prepartition I)
  body: l.toFilterDistortion I c ⊓ 𝓟 { π | π.iUnion = π₀.iUnion }

中文:
定义 toFilterDistortioniUnion
  签名: (l : 整数egrationParams) (I : Box ι) (c : 实数>=0) (π₀ : 预分拆 I)
  定义体: l.toFilterDistortion I c ⊓ 𝓟 { π | π.iUnion = π₀.iUnion }

Depends on / 依赖: iUnion, l.toFilterDistortion, toFilterDistortion
-/
def toFilterDistortioniUnion (l : IntegrationParams) (I : Box ι) (c : Real>=0) (π₀ : Prepartition I) :=
  l.toFilterDistortion I c ⊓ 𝓟 { π | π.iUnion = π₀.iUnion }

/--
Definition of `toFilteriUnion` / `toFilteriUnion` 的定义

English:
definition toFilteriUnion
  signature: (I : Box ι) (π₀ : Prepartition I)
  body: ⨆ c : Real>=0, l.toFilterDistortioniUnion I c π₀

中文:
定义 toFilteriUnion
  签名: (I : Box ι) (π₀ : 预分拆 I)
  定义体: ⨆ c : Real>=0, l.toFilterDistortioniUnion I c π₀

Depends on / 依赖: l.toFilterDistortioniUnion, toFilterDistortioniUnion
-/
def toFilteriUnion (I : Box ι) (π₀ : Prepartition I) :=
  ⨆ c : Real>=0, l.toFilterDistortioniUnion I c π₀

/--
theorem `rCond_of_bRiemann_eq_false` / 定理 `rCond_of_bRiemann_eq_false`

English:
theorem rCond_of_bRiemann_eq_false
  statement: {ι} (l : IntegrationParams) (hl : l.bRiemann = false)
  proof: by
  simp [RCond, hl]

中文:
定理 rCond_of_bRiemann_eq_false
  结论: {ι} (l : 整数egrationParams) (hl : l.bRiemann = false)
  证明: by
  simp [RCond, hl]
-/
theorem rCond_of_bRiemann_eq_false {ι} (l : IntegrationParams) (hl : l.bRiemann = false)
    {r : (ι -> Real) -> Ioi (0 : Real)} : l.RCond r := by
  simp [RCond, hl]

/--
theorem `toFilter_inf_iUnion_eq` / 定理 `toFilter_inf_iUnion_eq`

English:
theorem toFilter_inf_iUnion_eq
  given: (l : IntegrationParams) (I : Box ι) (π₀ : Prepartition I)
  proof: (iSup_inf_principal _ _).symm

中文:
定理 toFilter_inf_iUnion_eq
  条件: (l : 整数egrationParams) (I : Box ι) (π₀ : 预分拆 I)
  证明: (iSup_inf_principal _ _).symm

Depends on / 依赖: iSup_inf_principal
-/
theorem toFilter_inf_iUnion_eq (l : IntegrationParams) (I : Box ι) (π₀ : Prepartition I) :
    l.toFilter I ⊓ 𝓟 { π | π.iUnion = π₀.iUnion } = l.toFilteriUnion I π₀ :=
  (iSup_inf_principal _ _).symm

variable {r₁ r₂ : (ι -> Real) -> Ioi (0 : Real)} {π π₁ π₂ : TaggedPrepartition I}

variable (I) in
/--
theorem `MemBaseSet.mono'` / 定理 `MemBaseSet.mono'`

English:
theorem MemBaseSet.mono'
  statement: (h : l₁ <= l₂) (hc : c₁ <= c₂)
  proof: ⟨hπ.1.mono' hr, fun h₂ => hπ.2 (le_iff_imp.1 h.2.1 h₂),
    fun hD => (hπ.3 (le_iff_imp.1 h.2.2 hD)).trans hc,
    fun hD => (hπ.4 (le_iff_imp.1 h.2.2 hD)).imp fun _ hπ => ⟨hπ.1, hπ.2.trans hc⟩⟩

中文:
定理 MemBaseSet.mono'
  结论: (h : l₁ <= l₂) (hc : c₁ <= c₂)
  证明: ⟨hπ.1.mono' hr, fun h₂ => hπ.2 (le_iff_imp.1 h.2.1 h₂),
    fun hD => (hπ.3 (le_iff_imp.1 h.2.2 hD)).trans hc,
    fun hD => (hπ.4 (le_iff_imp.1 h.2.2 hD)).imp fun _ hπ => ⟨hπ.1, hπ.2.trans hc⟩⟩

Depends on / 依赖: le_iff_imp
-/
theorem MemBaseSet.mono' (h : l₁ <= l₂) (hc : c₁ <= c₂)
    (hr : forall J in π, r₁ (π.tag J) <= r₂ (π.tag J)) (hπ : l₁.MemBaseSet I c₁ r₁ π) :
    l₂.MemBaseSet I c₂ r₂ π :=
  ⟨hπ.1.mono' hr, fun h₂ => hπ.2 (le_iff_imp.1 h.2.1 h₂),
    fun hD => (hπ.3 (le_iff_imp.1 h.2.2 hD)).trans hc,
    fun hD => (hπ.4 (le_iff_imp.1 h.2.2 hD)).imp fun _ hπ => ⟨hπ.1, hπ.2.trans hc⟩⟩

variable (I) in
@[gcongr, mono]
/--
theorem `MemBaseSet.mono` / 定理 `MemBaseSet.mono`

English:
theorem MemBaseSet.mono
  statement: (h : l₁ <= l₂) (hc : c₁ <= c₂)
  proof: hπ.mono' I h hc fun J _ => hr _ π.tag_mem_Icc J

中文:
定理 MemBaseSet.mono
  结论: (h : l₁ <= l₂) (hc : c₁ <= c₂)
  证明: hπ.mono' I h hc fun J _ => hr _ π.tag_mem_Icc J

Depends on / 依赖: tag_mem_Icc
-/
theorem MemBaseSet.mono (h : l₁ <= l₂) (hc : c₁ <= c₂)
    (hr : forall x in Box.Icc I, r₁ x <= r₂ x) (hπ : l₁.MemBaseSet I c₁ r₁ π) : l₂.MemBaseSet I c₂ r₂ π :=
hπ.mono' I h hc fun J _ => hr _ π.tag_mem_Icc J

/--
theorem `MemBaseSet.exists_common_compl` / 定理 `MemBaseSet.exists_common_compl`

English:
theorem MemBaseSet.exists_common_compl
  proof: by
  wlog hc : c₁ <= c₂ with H
  · simpa [hU, _root_.and_comm] using
      @H _ _ I c₂ c₁ l r₂ r₁ π₂ π₁ h₂ h₁ hU.symm (le_of_not_ge hc)
  by_cases hD : (l.bDistortion : Prop)
  · rcases h₁.4 hD with ⟨π, hπU, hπc⟩
    exact ⟨π, hπU, fun _ => hπc, fun _ => hπc.trans hc⟩
  · exact ⟨π₁.toPrepartition.compl, π₁.toPrepartition.iUnion_compl,
      fun h => (hD h).elim, fun h => (hD h).elim⟩

中文:
定理 MemBaseSet.存在_common_compl
  证明: by
  wlog hc : c₁ <= c₂ with H
  · simpa [hU, _root_.and_comm] using
      @H _ _ I c₂ c₁ l r₂ r₁ π₂ π₁ h₂ h₁ hU.symm (le_of_not_ge hc)
  by_cases hD : (l.bDistortion : Prop)
  · rcases h₁.4 hD with ⟨π, hπU, hπc⟩
    exact ⟨π, hπU, fun _ => hπc, fun _ => hπc.trans hc⟩
  · exact ⟨π₁.toPrepartition.compl, π₁.toPrepartition.iUnion_compl,
      fun h => (hD h).elim, fun h => (hD h).elim⟩

Depends on / 依赖: _root_, _root_.and_comm, and_comm, bDistortion, c.trans, hU.symm, iUnion_compl, l.bDistortion, le_of_not_ge, toPrepartition, toPrepartition.compl, toPrepartition.iUnion_compl
-/
theorem MemBaseSet.exists_common_compl
    (h₁ : l.MemBaseSet I c₁ r₁ π₁) (h₂ : l.MemBaseSet I c₂ r₂ π₂)
    (hU : π₁.iUnion = π₂.iUnion) :
    exists π : Prepartition I, π.iUnion = ↑I \ π₁.iUnion ∧
      (l.bDistortion -> π.distortion <= c₁) ∧ (l.bDistortion -> π.distortion <= c₂) := by
  wlog hc : c₁ <= c₂ with H
  · simpa [hU, _root_.and_comm] using
      @H _ _ I c₂ c₁ l r₂ r₁ π₂ π₁ h₂ h₁ hU.symm (le_of_not_ge hc)
  by_cases hD : (l.bDistortion : Prop)
  · rcases h₁.4 hD with ⟨π, hπU, hπc⟩
    exact ⟨π, hπU, fun _ => hπc, fun _ => hπc.trans hc⟩
  · exact ⟨π₁.toPrepartition.compl, π₁.toPrepartition.iUnion_compl,
      fun h => (hD h).elim, fun h => (hD h).elim⟩

/--
theorem `MemBaseSet.unionComplToSubordinate` / 定理 `MemBaseSet.unionComplToSubordinate`

English:
theorem MemBaseSet.unionComplToSubordinate
  statement: (hπ₁ : l.MemBaseSet I c r₁ π₁)
  proof: ⟨hπ₁.1.disjUnion ((π₂.isSubordinate_toSubordinate r₂).mono hle) _,
    fun h => (hπ₁.2 h).disjUnion (π₂.isHenstock_toSubordinate _) _,
    fun h => (distortion_unionComplToSubordinate _ _ _ _).trans_le (max_le (hπ₁.3 h) (hc h)),
    fun _ => ⟨⊥, by simp⟩⟩

中文:
定理 MemBaseSet.unionComplToSubordinate
  结论: (hπ₁ : l.MemBaseSet I c r₁ π₁)
  证明: ⟨hπ₁.1.disjUnion ((π₂.isSubordinate_toSubordinate r₂).mono hle) _,
    fun h => (hπ₁.2 h).disjUnion (π₂.isHenstock_toSubordinate _) _,
    fun h => (distortion_unionComplToSubordinate _ _ _ _).trans_le (max_le (hπ₁.3 h) (hc h)),
    fun _ => ⟨⊥, by simp⟩⟩
-/
protected theorem MemBaseSet.unionComplToSubordinate (hπ₁ : l.MemBaseSet I c r₁ π₁)
    (hle : forall x in Box.Icc I, r₂ x <= r₁ x) {π₂ : Prepartition I} (hU : π₂.iUnion = ↑I \ π₁.iUnion)
    (hc : l.bDistortion -> π₂.distortion <= c) :
    l.MemBaseSet I c r₁ (π₁.unionComplToSubordinate π₂ hU r₂) :=
  ⟨hπ₁.1.disjUnion ((π₂.isSubordinate_toSubordinate r₂).mono hle) _,
    fun h => (hπ₁.2 h).disjUnion (π₂.isHenstock_toSubordinate _) _,
    fun h => (distortion_unionComplToSubordinate _ _ _ _).trans_le (max_le (hπ₁.3 h) (hc h)),
    fun _ => ⟨⊥, by simp⟩⟩

variable {r : (ι -> Real) -> Ioi (0 : Real)}

set_option backward.isDefEq.respectTransparency false in
/--
theorem `MemBaseSet.filter` / 定理 `MemBaseSet.filter`

English:
theorem MemBaseSet.filter
  given: (hπ : l.MemBaseSet I c r π) (p : Box ι -> Prop)
  proof: by
  classical
  refine ⟨fun J hJ => hπ.1 J (π.mem_filter.1 hJ).1, fun hH J hJ => hπ.2 hH J (π.mem_filter.1 hJ).1,
    fun hD => (distortion_filter_le _ _).trans (hπ.3 hD), fun hD => ?_⟩
  rcases hπ.4 hD with ⟨π₁, hπ₁U, hc⟩
  set π₂ := π.filter fun J => ¬p J
  have : Disjoint π₁.iUnion π₂.iUnion := by
    simpa [π₂, hπ₁U] using disjoint_sdiff_self_left.mono_right sdiff_le
  refine ⟨π₁.disjUnion π₂.toPrepartition this, ?_, ?_⟩
  · suffices ↑I \ π.iUnion union π.iUnion \ (π.filter p).iUnion = ↑I \ (π.filter p).iUnion by
      simp [π₂, *]
    have h : (π.filter p).iUnion subseteq π.iUnion :=
      biUnion_subset_biUnion_left (Finset.filter_subset _ _)
    ext x
    fconstructor
    · rintro (⟨hxI, hxπ⟩ | ⟨hxπ, hxp⟩)
      exacts [⟨hxI, mt (@h x) hxπ⟩, ⟨π.iUnion_subset hxπ, hxp⟩]
    · rintro ⟨hxI, hxp⟩
      by_cases hxπ : x in π.iUnion
      exacts [Or.inr ⟨hxπ, hxp⟩, Or.inl ⟨hxI, hxπ⟩]
  · have : (π.filter fun J => ¬p J).distortion <= c := (distortion_filter_le _ _).trans (hπ.3 hD)
    simpa [hc]

中文:
定理 MemBaseSet.filter
  条件: (hπ : l.MemBaseSet I c r π) (p : Box ι -> 命题)
  证明: by
  classical
  refine ⟨fun J hJ => hπ.1 J (π.mem_filter.1 hJ).1, fun hH J hJ => hπ.2 hH J (π.mem_filter.1 hJ).1,
    fun hD => (distortion_filter_le _ _).trans (hπ.3 hD), fun hD => ?_⟩
  rcases hπ.4 hD with ⟨π₁, hπ₁U, hc⟩
  set π₂ := π.filter fun J => ¬p J
  have : Disjoint π₁.iUnion π₂.iUnion := by
    simpa [π₂, hπ₁U] using disjoint_sdiff_self_left.mono_right sdiff_le
  refine ⟨π₁.disjUnion π₂.toPrepartition this, ?_, ?_⟩
  · suffices ↑I \ π.iUnion union π.iUnion \ (π.filter p).iUnion = ↑I \ (π.filter p).iUnion by
      simp [π₂, *]
    have h : (π.filter p).iUnion subseteq π.iUnion :=
      biUnion_subset_biUnion_left (Finset.filter_subset _ _)
    ext x
    fconstructor
    · rintro (⟨hxI, hxπ⟩ | ⟨hxπ, hxp⟩)
      exacts [⟨hxI, mt (@h x) hxπ⟩, ⟨π.iUnion_subset hxπ, hxp⟩]
    · rintro ⟨hxI, hxp⟩
      by_cases hxπ : x in π.iUnion
      exacts [Or.inr ⟨hxπ, hxp⟩, Or.inl ⟨hxI, hxπ⟩]
  · have : (π.filter fun J => ¬p J).distortion <= c := (distortion_filter_le _ _).trans (hπ.3 hD)
    simpa [hc]
-/
protected theorem MemBaseSet.filter (hπ : l.MemBaseSet I c r π) (p : Box ι -> Prop) :
    l.MemBaseSet I c r (π.filter p) := by
  classical
  refine ⟨fun J hJ => hπ.1 J (π.mem_filter.1 hJ).1, fun hH J hJ => hπ.2 hH J (π.mem_filter.1 hJ).1,
    fun hD => (distortion_filter_le _ _).trans (hπ.3 hD), fun hD => ?_⟩
  rcases hπ.4 hD with ⟨π₁, hπ₁U, hc⟩
  set π₂ := π.filter fun J => ¬p J
  have : Disjoint π₁.iUnion π₂.iUnion := by
    simpa [π₂, hπ₁U] using disjoint_sdiff_self_left.mono_right sdiff_le
  refine ⟨π₁.disjUnion π₂.toPrepartition this, ?_, ?_⟩
  · suffices ↑I \ π.iUnion union π.iUnion \ (π.filter p).iUnion = ↑I \ (π.filter p).iUnion by
      simp [π₂, *]
    have h : (π.filter p).iUnion subseteq π.iUnion :=
      biUnion_subset_biUnion_left (Finset.filter_subset _ _)
    ext x
    fconstructor
    · rintro (⟨hxI, hxπ⟩ | ⟨hxπ, hxp⟩)
      exacts [⟨hxI, mt (@h x) hxπ⟩, ⟨π.iUnion_subset hxπ, hxp⟩]
    · rintro ⟨hxI, hxp⟩
      by_cases hxπ : x in π.iUnion
      exacts [Or.inr ⟨hxπ, hxp⟩, Or.inl ⟨hxI, hxπ⟩]
  · have : (π.filter fun J => ¬p J).distortion <= c := (distortion_filter_le _ _).trans (hπ.3 hD)
    simpa [hc]

/--
theorem `biUnionTagged_memBaseSet` / 定理 `biUnionTagged_memBaseSet`

English:
theorem biUnionTagged_memBaseSet
  statement: {π : Prepartition I} {πi : forall J, TaggedPrepartition J}
  proof: by
  refine ⟨TaggedPrepartition.isSubordinate_biUnionTagged.2 fun J hJ => (h J hJ).1,
    fun hH => TaggedPrepartition.isHenstock_biUnionTagged.2 fun J hJ => (h J hJ).2 hH,
    fun hD => ?_, fun hD => ?_⟩
  · rw [Prepartition.distortion_biUnionTagged, Finset.sup_le_iff]
    exact fun J hJ => (h J hJ).3 hD
  · refine ⟨_, ?_, hc hD⟩
    rw [π.iUnion_compl]; rw [← π.iUnion_biUnion_partition hp]
    rfl

@[gcongr, mono]

中文:
定理 biUnionTagged_memBaseSet
  结论: {π : 预分拆 I} {πi : 对任意 J, 标记预分拆 J}
  证明: by
  refine ⟨TaggedPrepartition.isSubordinate_biUnionTagged.2 fun J hJ => (h J hJ).1,
    fun hH => TaggedPrepartition.isHenstock_biUnionTagged.2 fun J hJ => (h J hJ).2 hH,
    fun hD => ?_, fun hD => ?_⟩
  · rw [Prepartition.distortion_biUnionTagged, Finset.sup_le_iff]
    exact fun J hJ => (h J hJ).3 hD
  · refine ⟨_, ?_, hc hD⟩
    rw [π.iUnion_compl]; rw [← π.iUnion_biUnion_partition hp]
    rfl

@[gcongr, mono]

Depends on / 依赖: Finset, Finset.sup_le_iff, Prepartition, Prepartition.distortion_biUnionTagged, TaggedPrepartition, TaggedPrepartition.isHenstock_biUnionTagged, TaggedPrepartition.isSubordinate_biUnionTagged, distortion_biUnionTagged, iUnion_biUnion_partition, iUnion_compl, isHenstock_biUnionTagged, isSubordinate_biUnionTagged, sup_le_iff
-/
theorem biUnionTagged_memBaseSet {π : Prepartition I} {πi : forall J, TaggedPrepartition J}
    (h : forall J in π, l.MemBaseSet J c r (πi J)) (hp : forall J in π, (πi J).IsPartition)
    (hc : l.bDistortion -> π.compl.distortion <= c) : l.MemBaseSet I c r (π.biUnionTagged πi) := by
  refine ⟨TaggedPrepartition.isSubordinate_biUnionTagged.2 fun J hJ => (h J hJ).1,
    fun hH => TaggedPrepartition.isHenstock_biUnionTagged.2 fun J hJ => (h J hJ).2 hH,
    fun hD => ?_, fun hD => ?_⟩
  · rw [Prepartition.distortion_biUnionTagged, Finset.sup_le_iff]
    exact fun J hJ => (h J hJ).3 hD
  · refine ⟨_, ?_, hc hD⟩
    rw [π.iUnion_compl]; rw [← π.iUnion_biUnion_partition hp]
    rfl

@[gcongr, mono]
/--
theorem `RCond.mono` / 定理 `RCond.mono`

English:
theorem RCond.mono
  given: {ι : Type*} {r : (ι -> Real) -> Ioi (0 : Real)} (h : l₁ <= l₂) (hr : l₂.RCond r)
  proof: fun hR => hr (le_iff_imp.1 h.1 hR)

nonrec theorem RCond.min {ι : Type*} {r₁ r₂ : (ι -> Real) -> Ioi (0 : Real)} (h₁ : l.RCond r₁)
    (h₂ : l.RCond r₂) : l.RCond fun x => min (r₁ x) (r₂ x) :=
  fun hR x => congr_arg₂ min (h₁ hR x) (h₂ hR x)

@[gcongr, mono]

中文:
定理 RCond.mono
  条件: {ι : 类型} {r : (ι -> 实数) -> 左开右无界区间 (0 : 实数)} (h : l₁ <= l₂) (hr : l₂.RCond r)
  证明: fun hR => hr (le_iff_imp.1 h.1 hR)

nonrec theorem RCond.min {ι : Type*} {r₁ r₂ : (ι -> Real) -> Ioi (0 : Real)} (h₁ : l.RCond r₁)
    (h₂ : l.RCond r₂) : l.RCond fun x => min (r₁ x) (r₂ x) :=
  fun hR x => congr_arg₂ min (h₁ hR x) (h₂ hR x)

@[gcongr, mono]

Depends on / 依赖: le_iff_imp
-/
theorem RCond.mono {ι : Type*} {r : (ι -> Real) -> Ioi (0 : Real)} (h : l₁ <= l₂) (hr : l₂.RCond r) :
    l₁.RCond r :=
  fun hR => hr (le_iff_imp.1 h.1 hR)

nonrec theorem RCond.min {ι : Type*} {r₁ r₂ : (ι -> Real) -> Ioi (0 : Real)} (h₁ : l.RCond r₁)
    (h₂ : l.RCond r₂) : l.RCond fun x => min (r₁ x) (r₂ x) :=
  fun hR x => congr_arg₂ min (h₁ hR x) (h₂ hR x)

@[gcongr, mono]
/--
theorem `toFilterDistortion_mono` / 定理 `toFilterDistortion_mono`

English:
theorem toFilterDistortion_mono
  given: (I : Box ι) (h : l₁ <= l₂) (hc : c₁ <= c₂)
  proof: iInf_mono fun _ =>
    iInf_mono' fun hr =>
      ⟨hr.mono h, principal_mono.2 fun _ => MemBaseSet.mono I h hc fun _ _ => le_rfl⟩

@[gcongr, mono]

中文:
定理 toFilterDistortion_mono
  条件: (I : Box ι) (h : l₁ <= l₂) (hc : c₁ <= c₂)
  证明: iInf_mono fun _ =>
    iInf_mono' fun hr =>
      ⟨hr.mono h, principal_mono.2 fun _ => MemBaseSet.mono I h hc fun _ _ => le_rfl⟩

@[gcongr, mono]

Depends on / 依赖: MemBaseSet, MemBaseSet.mono, hr.mono, iInf_mono, le_rfl, principal_mono
-/
theorem toFilterDistortion_mono (I : Box ι) (h : l₁ <= l₂) (hc : c₁ <= c₂) :
    l₁.toFilterDistortion I c₁ <= l₂.toFilterDistortion I c₂ :=
  iInf_mono fun _ =>
    iInf_mono' fun hr =>
      ⟨hr.mono h, principal_mono.2 fun _ => MemBaseSet.mono I h hc fun _ _ => le_rfl⟩

@[gcongr, mono]
/--
theorem `toFilter_mono` / 定理 `toFilter_mono`

English:
theorem toFilter_mono
  given: (I : Box ι) {l₁ l₂ : IntegrationParams} (h : l₁ <= l₂)
  proof: iSup_mono fun _ => toFilterDistortion_mono I h le_rfl

@[gcongr, mono]

中文:
定理 toFilter_mono
  条件: (I : Box ι) {l₁ l₂ : 整数egrationParams} (h : l₁ <= l₂)
  证明: iSup_mono fun _ => toFilterDistortion_mono I h le_rfl

@[gcongr, mono]

Depends on / 依赖: iSup_mono, le_rfl, toFilterDistortion_mono
-/
theorem toFilter_mono (I : Box ι) {l₁ l₂ : IntegrationParams} (h : l₁ <= l₂) :
    l₁.toFilter I <= l₂.toFilter I :=
  iSup_mono fun _ => toFilterDistortion_mono I h le_rfl

@[gcongr, mono]
/--
theorem `toFilteriUnion_mono` / 定理 `toFilteriUnion_mono`

English:
theorem toFilteriUnion_mono
  statement: (I : Box ι) {l₁ l₂ : IntegrationParams} (h : l₁ <= l₂)
  proof: iSup_mono fun _ => inf_le_inf_right _ toFilterDistortion_mono _ h le_rfl

中文:
定理 toFilteriUnion_mono
  结论: (I : Box ι) {l₁ l₂ : 整数egrationParams} (h : l₁ <= l₂)
  证明: iSup_mono fun _ => inf_le_inf_right _ toFilterDistortion_mono _ h le_rfl

Depends on / 依赖: iSup_mono, inf_le_inf_right, le_rfl, toFilterDistortion_mono
-/
theorem toFilteriUnion_mono (I : Box ι) {l₁ l₂ : IntegrationParams} (h : l₁ <= l₂)
    (π₀ : Prepartition I) : l₁.toFilteriUnion I π₀ <= l₂.toFilteriUnion I π₀ :=
iSup_mono fun _ => inf_le_inf_right _ toFilterDistortion_mono _ h le_rfl

/--
theorem `toFilteriUnion_congr` / 定理 `toFilteriUnion_congr`

English:
theorem toFilteriUnion_congr
  statement: (I : Box ι) (l : IntegrationParams) {π₁ π₂ : Prepartition I}
  proof: by
  simp only [toFilteriUnion, toFilterDistortioniUnion, h]

中文:
定理 toFilteriUnion_congr
  结论: (I : Box ι) (l : 整数egrationParams) {π₁ π₂ : 预分拆 I}
  证明: by
  simp only [toFilteriUnion, toFilterDistortioniUnion, h]

Depends on / 依赖: toFilterDistortioniUnion, toFilteriUnion
-/
theorem toFilteriUnion_congr (I : Box ι) (l : IntegrationParams) {π₁ π₂ : Prepartition I}
    (h : π₁.iUnion = π₂.iUnion) : l.toFilteriUnion I π₁ = l.toFilteriUnion I π₂ := by
  simp only [toFilteriUnion, toFilterDistortioniUnion, h]

/--
theorem `hasBasis_toFilterDistortion` / 定理 `hasBasis_toFilterDistortion`

English:
theorem hasBasis_toFilterDistortion
  given: (l : IntegrationParams) (I : Box ι) (c : Real>=0)
  proof: hasBasis_biInf_principal'
    (fun _ hr₁ _ hr₂ =>
      ⟨_, hr₁.min hr₂, fun _ => MemBaseSet.mono _ le_rfl le_rfl fun _ _ => min_le_left _ _,
        fun _ => MemBaseSet.mono _ le_rfl le_rfl fun _ _ => min_le_right _ _⟩)
    ⟨fun _ => ⟨1, Set.mem_Ioi.2 zero_lt_one⟩, fun _ _ => rfl⟩

中文:
定理 hasBasis_toFilterDistortion
  条件: (l : 整数egrationParams) (I : Box ι) (c : 实数>=0)
  证明: hasBasis_biInf_principal'
    (fun _ hr₁ _ hr₂ =>
      ⟨_, hr₁.min hr₂, fun _ => MemBaseSet.mono _ le_rfl le_rfl fun _ _ => min_le_left _ _,
        fun _ => MemBaseSet.mono _ le_rfl le_rfl fun _ _ => min_le_right _ _⟩)
    ⟨fun _ => ⟨1, Set.mem_Ioi.2 zero_lt_one⟩, fun _ _ => rfl⟩

Depends on / 依赖: MemBaseSet, MemBaseSet.mono, Set.mem_Ioi, hasBasis_biInf_principal, le_rfl, mem_Ioi, min_le_left, min_le_right, zero_lt_one
-/
theorem hasBasis_toFilterDistortion (l : IntegrationParams) (I : Box ι) (c : Real>=0) :
    (l.toFilterDistortion I c).HasBasis l.RCond fun r => { π | l.MemBaseSet I c r π } :=
  hasBasis_biInf_principal'
    (fun _ hr₁ _ hr₂ =>
      ⟨_, hr₁.min hr₂, fun _ => MemBaseSet.mono _ le_rfl le_rfl fun _ _ => min_le_left _ _,
        fun _ => MemBaseSet.mono _ le_rfl le_rfl fun _ _ => min_le_right _ _⟩)
    ⟨fun _ => ⟨1, Set.mem_Ioi.2 zero_lt_one⟩, fun _ _ => rfl⟩

/--
theorem `hasBasis_toFilterDistortioniUnion` / 定理 `hasBasis_toFilterDistortioniUnion`

English:
theorem hasBasis_toFilterDistortioniUnion
  statement: (l : IntegrationParams) (I : Box ι) (c : Real>=0)
  proof: (l.hasBasis_toFilterDistortion I c).inf_principal _

中文:
定理 hasBasis_toFilterDistortioniUnion
  结论: (l : 整数egrationParams) (I : Box ι) (c : 实数>=0)
  证明: (l.hasBasis_toFilterDistortion I c).inf_principal _

Depends on / 依赖: hasBasis_toFilterDistortion, inf_principal, l.hasBasis_toFilterDistortion
-/
theorem hasBasis_toFilterDistortioniUnion (l : IntegrationParams) (I : Box ι) (c : Real>=0)
    (π₀ : Prepartition I) :
    (l.toFilterDistortioniUnion I c π₀).HasBasis l.RCond fun r =>
      { π | l.MemBaseSet I c r π ∧ π.iUnion = π₀.iUnion } :=
  (l.hasBasis_toFilterDistortion I c).inf_principal _

/--
theorem `hasBasis_toFilteriUnion` / 定理 `hasBasis_toFilteriUnion`

English:
theorem hasBasis_toFilteriUnion
  given: (l : IntegrationParams) (I : Box ι) (π₀ : Prepartition I)
  proof: by
  have := fun c => l.hasBasis_toFilterDistortioniUnion I c π₀
  simpa only [ofPred_and, ofPred_exists] using! hasBasis_iSup this

中文:
定理 hasBasis_toFilteriUnion
  条件: (l : 整数egrationParams) (I : Box ι) (π₀ : 预分拆 I)
  证明: by
  have := fun c => l.hasBasis_toFilterDistortioniUnion I c π₀
  simpa only [ofPred_and, ofPred_exists] using! hasBasis_iSup this

Depends on / 依赖: hasBasis_iSup, hasBasis_toFilterDistortioniUnion, l.hasBasis_toFilterDistortioniUnion, ofPred_and, ofPred_exists
-/
theorem hasBasis_toFilteriUnion (l : IntegrationParams) (I : Box ι) (π₀ : Prepartition I) :
    (l.toFilteriUnion I π₀).HasBasis (fun r : Real>=0 -> (ι -> Real) -> Ioi (0 : Real) => forall c, l.RCond (r c))
      fun r => { π | exists c, l.MemBaseSet I c (r c) π ∧ π.iUnion = π₀.iUnion } := by
  have := fun c => l.hasBasis_toFilterDistortioniUnion I c π₀
  simpa only [ofPred_and, ofPred_exists] using! hasBasis_iSup this

/--
theorem `hasBasis_toFilteriUnion_top` / 定理 `hasBasis_toFilteriUnion_top`

English:
theorem hasBasis_toFilteriUnion_top
  given: (l : IntegrationParams) (I : Box ι)
  proof: by
  simpa only [TaggedPrepartition.isPartition_iff_iUnion_eq, Prepartition.iUnion_top] using
    l.hasBasis_toFilteriUnion I ⊤

中文:
定理 hasBasis_toFilteriUnion_top
  条件: (l : 整数egrationParams) (I : Box ι)
  证明: by
  simpa only [TaggedPrepartition.isPartition_iff_iUnion_eq, Prepartition.iUnion_top] using
    l.hasBasis_toFilteriUnion I ⊤

Depends on / 依赖: Prepartition, Prepartition.iUnion_top, TaggedPrepartition, TaggedPrepartition.isPartition_iff_iUnion_eq, hasBasis_toFilteriUnion, iUnion_top, isPartition_iff_iUnion_eq, l.hasBasis_toFilteriUnion
-/
theorem hasBasis_toFilteriUnion_top (l : IntegrationParams) (I : Box ι) :
    (l.toFilteriUnion I ⊤).HasBasis (fun r : Real>=0 -> (ι -> Real) -> Ioi (0 : Real) => forall c, l.RCond (r c))
      fun r => { π | exists c, l.MemBaseSet I c (r c) π ∧ π.IsPartition } := by
  simpa only [TaggedPrepartition.isPartition_iff_iUnion_eq, Prepartition.iUnion_top] using
    l.hasBasis_toFilteriUnion I ⊤

/--
theorem `hasBasis_toFilter` / 定理 `hasBasis_toFilter`

English:
theorem hasBasis_toFilter
  given: (l : IntegrationParams) (I : Box ι)
  proof: by
  simpa only [ofPred_exists] using! hasBasis_iSup (l.hasBasis_toFilterDistortion I)

中文:
定理 hasBasis_toFilter
  条件: (l : 整数egrationParams) (I : Box ι)
  证明: by
  simpa only [ofPred_exists] using! hasBasis_iSup (l.hasBasis_toFilterDistortion I)

Depends on / 依赖: hasBasis_iSup, hasBasis_toFilterDistortion, l.hasBasis_toFilterDistortion, ofPred_exists
-/
theorem hasBasis_toFilter (l : IntegrationParams) (I : Box ι) :
    (l.toFilter I).HasBasis (fun r : Real>=0 -> (ι -> Real) -> Ioi (0 : Real) => forall c, l.RCond (r c))
      fun r => { π | exists c, l.MemBaseSet I c (r c) π } := by
  simpa only [ofPred_exists] using! hasBasis_iSup (l.hasBasis_toFilterDistortion I)

/--
theorem `tendsto_embedBox_toFilteriUnion_top` / 定理 `tendsto_embedBox_toFilteriUnion_top`

English:
theorem tendsto_embedBox_toFilteriUnion_top
  given: (l : IntegrationParams) (h : I <= J)
  proof: by
  simp only [toFilteriUnion, tendsto_iSup]; intro c
  set π₀ := Prepartition.single J I h
  refine le_iSup_of_le (max c π₀.compl.distortion) ?_
  refine ((l.hasBasis_toFilterDistortioniUnion I c ⊤).tendsto_iff
    (l.hasBasis_toFilterDistortioniUnion J _ _)).2 fun r hr => ?_
  refine ⟨r, hr, fun π hπ => ?_⟩
  rw [mem_ofPred_eq]; rw [Prepartition.iUnion_top] at hπ
  refine ⟨⟨hπ.1.1, hπ.1.2, fun hD => le_trans (hπ.1.3 hD) (le_max_left _ _), fun _ => ?_⟩, ?_⟩
  · refine ⟨_, π₀.iUnion_compl.trans ?_, le_max_right _ _⟩
    congr 1
    exact (Prepartition.iUnion_single h).trans hπ.2.symm
  · exact hπ.2.trans (Prepartition.iUnion_single _).symm

中文:
定理 tendsto_embedBox_toFilteriUnion_top
  条件: (l : 整数egrationParams) (h : I <= J)
  证明: by
  simp only [toFilteriUnion, tendsto_iSup]; intro c
  set π₀ := Prepartition.single J I h
  refine le_iSup_of_le (max c π₀.compl.distortion) ?_
  refine ((l.hasBasis_toFilterDistortioniUnion I c ⊤).tendsto_iff
    (l.hasBasis_toFilterDistortioniUnion J _ _)).2 fun r hr => ?_
  refine ⟨r, hr, fun π hπ => ?_⟩
  rw [mem_ofPred_eq]; rw [Prepartition.iUnion_top] at hπ
  refine ⟨⟨hπ.1.1, hπ.1.2, fun hD => le_trans (hπ.1.3 hD) (le_max_left _ _), fun _ => ?_⟩, ?_⟩
  · refine ⟨_, π₀.iUnion_compl.trans ?_, le_max_right _ _⟩
    congr 1
    exact (Prepartition.iUnion_single h).trans hπ.2.symm
  · exact hπ.2.trans (Prepartition.iUnion_single _).symm

Depends on / 依赖: Prepartition, Prepartition.iUnion_top, Prepartition.single, compl.distortion, distortion, hasBasis_toFilterDistortioniUnion, iUnion_compl, iUnion_compl.trans, iUnion_top, l.hasBasis_toFilterDistortioniUnion, le_iSup_of_le, le_max_left, le_max_right, le_trans, mem_ofPred_eq, single, tendsto_iSup, tendsto_iff, toFilteriUnion
-/
theorem tendsto_embedBox_toFilteriUnion_top (l : IntegrationParams) (h : I <= J) :
    Tendsto (TaggedPrepartition.embedBox I J h) (l.toFilteriUnion I ⊤)
      (l.toFilteriUnion J (Prepartition.single J I h)) := by
  simp only [toFilteriUnion, tendsto_iSup]; intro c
  set π₀ := Prepartition.single J I h
  refine le_iSup_of_le (max c π₀.compl.distortion) ?_
  refine ((l.hasBasis_toFilterDistortioniUnion I c ⊤).tendsto_iff
    (l.hasBasis_toFilterDistortioniUnion J _ _)).2 fun r hr => ?_
  refine ⟨r, hr, fun π hπ => ?_⟩
  rw [mem_ofPred_eq]; rw [Prepartition.iUnion_top] at hπ
  refine ⟨⟨hπ.1.1, hπ.1.2, fun hD => le_trans (hπ.1.3 hD) (le_max_left _ _), fun _ => ?_⟩, ?_⟩
  · refine ⟨_, π₀.iUnion_compl.trans ?_, le_max_right _ _⟩
    congr 1
    exact (Prepartition.iUnion_single h).trans hπ.2.symm
  · exact hπ.2.trans (Prepartition.iUnion_single _).symm

/--
theorem `exists_memBaseSet_le_iUnion_eq` / 定理 `exists_memBaseSet_le_iUnion_eq`

English:
theorem exists_memBaseSet_le_iUnion_eq
  statement: (l : IntegrationParams) (π₀ : Prepartition I)
  proof: by
  rcases π₀.exists_tagged_le_isHenstock_isSubordinate_iUnion_eq r with ⟨π, hle, hH, hr, hd, hU⟩
  refine ⟨π, ⟨hr, fun _ => hH, fun _ => hd.trans_le hc₁, fun _ => ⟨π₀.compl, ?_, hc₂⟩⟩, ⟨hle, hU⟩⟩
  exact Prepartition.compl_congr hU ▸ π.toPrepartition.iUnion_compl

中文:
定理 存在_memBaseSet_le_iUnion_eq
  结论: (l : 整数egrationParams) (π₀ : 预分拆 I)
  证明: by
  rcases π₀.exists_tagged_le_isHenstock_isSubordinate_iUnion_eq r with ⟨π, hle, hH, hr, hd, hU⟩
  refine ⟨π, ⟨hr, fun _ => hH, fun _ => hd.trans_le hc₁, fun _ => ⟨π₀.compl, ?_, hc₂⟩⟩, ⟨hle, hU⟩⟩
  exact Prepartition.compl_congr hU ▸ π.toPrepartition.iUnion_compl

Depends on / 依赖: Prepartition, Prepartition.compl_congr, compl_congr, exists_tagged_le_isHenstock_isSubordinate_iUnion_eq, hd.trans_le, iUnion_compl, toPrepartition, toPrepartition.iUnion_compl, trans_le
-/
theorem exists_memBaseSet_le_iUnion_eq (l : IntegrationParams) (π₀ : Prepartition I)
    (hc₁ : π₀.distortion <= c) (hc₂ : π₀.compl.distortion <= c) (r : (ι -> Real) -> Ioi (0 : Real)) :
    exists π, l.MemBaseSet I c r π ∧ π.toPrepartition <= π₀ ∧ π.iUnion = π₀.iUnion := by
  rcases π₀.exists_tagged_le_isHenstock_isSubordinate_iUnion_eq r with ⟨π, hle, hH, hr, hd, hU⟩
  refine ⟨π, ⟨hr, fun _ => hH, fun _ => hd.trans_le hc₁, fun _ => ⟨π₀.compl, ?_, hc₂⟩⟩, ⟨hle, hU⟩⟩
  exact Prepartition.compl_congr hU ▸ π.toPrepartition.iUnion_compl

/--
theorem `exists_memBaseSet_isPartition` / 定理 `exists_memBaseSet_isPartition`

English:
theorem exists_memBaseSet_isPartition
  statement: (l : IntegrationParams) (I : Box ι) (hc : I.distortion <= c)
  proof: by
  rw [← Prepartition.distortion_top] at hc
  have hc' : (⊤ : Prepartition I).compl.distortion <= c := by simp
  simpa [isPartition_iff_iUnion_eq] using l.exists_memBaseSet_le_iUnion_eq ⊤ hc hc' r

中文:
定理 存在_memBaseSet_isPartition
  结论: (l : 整数egrationParams) (I : Box ι) (hc : I.distortion <= c)
  证明: by
  rw [← Prepartition.distortion_top] at hc
  have hc' : (⊤ : Prepartition I).compl.distortion <= c := by simp
  simpa [isPartition_iff_iUnion_eq] using l.exists_memBaseSet_le_iUnion_eq ⊤ hc hc' r

Depends on / 依赖: Prepartition, Prepartition.distortion_top, compl.distortion, distortion, distortion_top, exists_memBaseSet_le_iUnion_eq, isPartition_iff_iUnion_eq, l.exists_memBaseSet_le_iUnion_eq
-/
theorem exists_memBaseSet_isPartition (l : IntegrationParams) (I : Box ι) (hc : I.distortion <= c)
    (r : (ι -> Real) -> Ioi (0 : Real)) : exists π, l.MemBaseSet I c r π ∧ π.IsPartition := by
  rw [← Prepartition.distortion_top] at hc
  have hc' : (⊤ : Prepartition I).compl.distortion <= c := by simp
  simpa [isPartition_iff_iUnion_eq] using l.exists_memBaseSet_le_iUnion_eq ⊤ hc hc' r

/--
theorem `toFilterDistortioniUnion_neBot` / 定理 `toFilterDistortioniUnion_neBot`

English:
theorem toFilterDistortioniUnion_neBot
  statement: (l : IntegrationParams) (I : Box ι) (π₀ : Prepartition I)
  proof: ((l.hasBasis_toFilterDistortion I _).inf_principal _).neBot_iff.2
    fun {r} _ => (l.exists_memBaseSet_le_iUnion_eq π₀ hc₁ hc₂ r).imp fun _ hπ => ⟨hπ.1, hπ.2.2⟩

中文:
定理 toFilterDistortioniUnion_neBot
  结论: (l : 整数egrationParams) (I : Box ι) (π₀ : 预分拆 I)
  证明: ((l.hasBasis_toFilterDistortion I _).inf_principal _).neBot_iff.2
    fun {r} _ => (l.exists_memBaseSet_le_iUnion_eq π₀ hc₁ hc₂ r).imp fun _ hπ => ⟨hπ.1, hπ.2.2⟩

Depends on / 依赖: exists_memBaseSet_le_iUnion_eq, hasBasis_toFilterDistortion, inf_principal, l.exists_memBaseSet_le_iUnion_eq, l.hasBasis_toFilterDistortion, neBot_iff
-/
theorem toFilterDistortioniUnion_neBot (l : IntegrationParams) (I : Box ι) (π₀ : Prepartition I)
    (hc₁ : π₀.distortion <= c) (hc₂ : π₀.compl.distortion <= c) :
    (l.toFilterDistortioniUnion I c π₀).NeBot :=
  ((l.hasBasis_toFilterDistortion I _).inf_principal _).neBot_iff.2
    fun {r} _ => (l.exists_memBaseSet_le_iUnion_eq π₀ hc₁ hc₂ r).imp fun _ hπ => ⟨hπ.1, hπ.2.2⟩

/--
Instance `toFilterDistortioniUnion_neBot'` / 实例 `toFilterDistortioniUnion_neBot'`

English:
instance toFilterDistortioniUnion_neBot'
  signature: (l : IntegrationParams) (I : Box ι) (π₀ : Prepartition I)
  body: l.toFilterDistortioniUnion_neBot I π₀ (le_max_left _ _) (le_max_right _ _)

中文:
实例 toFilterDistortioniUnion_neBot'
  签名: (l : 整数egrationParams) (I : Box ι) (π₀ : 预分拆 I)
  定义体: l.toFilterDistortioniUnion_neBot I π₀ (le_max_left _ _) (le_max_right _ _)

Depends on / 依赖: l.toFilterDistortioniUnion_neBot, le_max_left, le_max_right, toFilterDistortioniUnion_neBot
-/
instance toFilterDistortioniUnion_neBot' (l : IntegrationParams) (I : Box ι) (π₀ : Prepartition I) :
    (l.toFilterDistortioniUnion I (max π₀.distortion π₀.compl.distortion) π₀).NeBot :=
  l.toFilterDistortioniUnion_neBot I π₀ (le_max_left _ _) (le_max_right _ _)

/--
Instance `toFilterDistortion_neBot` / 实例 `toFilterDistortion_neBot`

English:
instance toFilterDistortion_neBot
  signature: (l : IntegrationParams) (I : Box ι)
  body: by
  simpa using (l.toFilterDistortioniUnion_neBot' I ⊤).mono inf_le_left

中文:
实例 toFilterDistortion_neBot
  签名: (l : 整数egrationParams) (I : Box ι)
  定义体: by
  simpa using (l.toFilterDistortioniUnion_neBot' I ⊤).mono inf_le_left

Depends on / 依赖: inf_le_left, l.toFilterDistortioniUnion_neBot, toFilterDistortioniUnion_neBot
-/
instance toFilterDistortion_neBot (l : IntegrationParams) (I : Box ι) :
    (l.toFilterDistortion I I.distortion).NeBot := by
  simpa using (l.toFilterDistortioniUnion_neBot' I ⊤).mono inf_le_left

/--
Instance `toFilter_neBot` / 实例 `toFilter_neBot`

English:
instance toFilter_neBot
  signature: (l : IntegrationParams) (I : Box ι)
  body: (l.toFilterDistortion_neBot I).mono le_iSup _ _

中文:
实例 toFilter_neBot
  签名: (l : 整数egrationParams) (I : Box ι)
  定义体: (l.toFilterDistortion_neBot I).mono le_iSup _ _

Depends on / 依赖: l.toFilterDistortion_neBot, le_iSup, toFilterDistortion_neBot
-/
instance toFilter_neBot (l : IntegrationParams) (I : Box ι) : (l.toFilter I).NeBot :=
(l.toFilterDistortion_neBot I).mono le_iSup _ _

/--
Instance `toFilteriUnion_neBot` / 实例 `toFilteriUnion_neBot`

English:
instance toFilteriUnion_neBot
  signature: (l : IntegrationParams) (I : Box ι) (π₀ : Prepartition I)
  body: (l.toFilterDistortioniUnion_neBot' I π₀).mono
    le_iSup (fun c => l.toFilterDistortioniUnion I c π₀) _

中文:
实例 toFilteriUnion_neBot
  签名: (l : 整数egrationParams) (I : Box ι) (π₀ : 预分拆 I)
  定义体: (l.toFilterDistortioniUnion_neBot' I π₀).mono
    le_iSup (fun c => l.toFilterDistortioniUnion I c π₀) _

Depends on / 依赖: l.toFilterDistortioniUnion, l.toFilterDistortioniUnion_neBot, le_iSup, toFilterDistortioniUnion, toFilterDistortioniUnion_neBot
-/
instance toFilteriUnion_neBot (l : IntegrationParams) (I : Box ι) (π₀ : Prepartition I) :
    (l.toFilteriUnion I π₀).NeBot :=
(l.toFilterDistortioniUnion_neBot' I π₀).mono
    le_iSup (fun c => l.toFilterDistortioniUnion I c π₀) _

/--
theorem `eventually_isPartition` / 定理 `eventually_isPartition`

English:
theorem eventually_isPartition
  given: (l : IntegrationParams) (I : Box ι)
  proof: eventually_iSup.2 fun _ =>
eventually_inf_principal.2
      Eventually.of_forall fun π h =>
        π.isPartition_iff_iUnion_eq.2 (h.trans Prepartition.iUnion_top)

中文:
定理 eventually_isPartition
  条件: (l : 整数egrationParams) (I : Box ι)
  证明: eventually_iSup.2 fun _ =>
eventually_inf_principal.2
      Eventually.of_forall fun π h =>
        π.isPartition_iff_iUnion_eq.2 (h.trans Prepartition.iUnion_top)

Depends on / 依赖: Eventually, Eventually.of_forall, Prepartition, Prepartition.iUnion_top, eventually_iSup, eventually_inf_principal, h.trans, iUnion_top, isPartition_iff_iUnion_eq, of_forall
-/
theorem eventually_isPartition (l : IntegrationParams) (I : Box ι) :
    forallᶠ π in l.toFilteriUnion I ⊤, TaggedPrepartition.IsPartition π :=
  eventually_iSup.2 fun _ =>
eventually_inf_principal.2
      Eventually.of_forall fun π h =>
        π.isPartition_iff_iUnion_eq.2 (h.trans Prepartition.iUnion_top)

end IntegrationParams

end BoxIntegral
