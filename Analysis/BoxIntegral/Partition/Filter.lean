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
  integrable in any other theory is integrable in this one as well.  This is a non-standard
  generalization of the Henstock-Kurzweil integral to higher dimension.  In dimension one, it
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

variable {ι : Type*} [Fintype ι] {I J : Box ι} {c c₁ c₂ : ℝ≥0}

open TaggedPrepartition

/-- An `IntegrationParams` is a structure holding 3 Boolean values used to define a filter to be
used in the definition of a box-integrable function.
-/
@[ext]
/-
**BoxIntegral.IntegrationParams** 是 Mathlib 中的一个结构，位于命名空间 `BoxIntegral`。
形式化陈述：IntegrationParams : Type where /-- `true` if the filter corresponds to a R
iemann-style integral, i.e. in the definition of integrability we require a cons
tant upper estimate `r` on the size of boxes of a tagged partition; the value `f
alse` means that the estimate may depend on the position of the tag. -/ (bRieman
n : Bool) /-- `true` if we require that each tag belongs to its own closed box; 
the value `false` means that we only require that tags belong to the ambient box
. -/ (bHenstock : Bool) /-
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `IntegrationParams` is a structure holding 3 Boolean values used to define a 
filter to be
used in the definition of a box-integrable function. -/
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

/-- Auxiliary equivalence with a product type used to lift an order. -/
/-
**BoxIntegral.IntegrationParams.equivProd** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegral
.IntegrationParams`。
形式化陈述：equivProd : IntegrationParams ≃ Bool × Boolᵒᵈ × Boolᵒᵈ where toFun l
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary equivalence with a product type used to lift an order.
-/
def equivProd : IntegrationParams ≃ Bool × Boolᵒᵈ × Boolᵒᵈ where
  toFun l := ⟨l.1, OrderDual.toDual l.2, OrderDual.toDual l.3⟩
  invFun l := ⟨l.1, OrderDual.ofDual l.2.1, OrderDual.ofDual l.2.2⟩
/-
**BoxIntegral.IntegrationParams.** 是 Mathlib 中的一个实例，位于命名空间 `BoxIntegral.Integrat
ionParams`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder IntegrationParams :=
  PartialOrder.lift equivProd equivProd.injective

/-- Auxiliary `OrderIso` with a product type used to lift a `BoundedOrder` structure. -/
/-
**BoxIntegral.IntegrationParams.isoProd** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegral.I
ntegrationParams`。
形式化陈述：isoProd : IntegrationParams ≃o Bool × Boolᵒᵈ × Boolᵒᵈ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary `OrderIso` with a product type used to lift a `BoundedOrder` structure
.
-/
def isoProd : IntegrationParams ≃o Bool × Boolᵒᵈ × Boolᵒᵈ :=
  ⟨equivProd, Iff.rfl⟩
/-
**BoxIntegral.IntegrationParams.** 是 Mathlib 中的一个实例，位于命名空间 `BoxIntegral.Integrat
ionParams`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : BoundedOrder IntegrationParams :=
  isoProd.symm.toGaloisInsertion.liftBoundedOrder

/-- The value `BoxIntegral.IntegrationParams.GP = ⊥`
(`bRiemann = false`, `bHenstock = true`, `bDistortion = true`)
corresponds to a generalization of the Henstock integral such that the Divergence theorem holds true
without additional integrability assumptions, see the module docstring for details. -/
/-
**BoxIntegral.IntegrationParams.** 是 Mathlib 中的一个实例，位于命名空间 `BoxIntegral.Integrat
ionParams`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The value `BoxIntegral.IntegrationParams.GP = ⊥`
(`bRiemann = false`, `bHenstock = true`, `bDistortion = true`)
corresponds to a generalization of the Henstock integral such that the Divergenc
e theorem holds true
without additional integrability assumptions, see the module docstring for detai
ls.
-/
instance : Inhabited IntegrationParams :=
  ⟨⊥⟩
/-
**BoxIntegral.IntegrationParams.** 是 Mathlib 中的一个实例，位于命名空间 `BoxIntegral.Integrat
ionParams`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DecidableLE (IntegrationParams) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
/-
**BoxIntegral.IntegrationParams.** 是 Mathlib 中的一个实例，位于命名空间 `BoxIntegral.Integrat
ionParams`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DecidableEq IntegrationParams :=
  fun _ _ => decidable_of_iff _ IntegrationParams.ext_iff.symm

/-- The `BoxIntegral.IntegrationParams` corresponding to the Riemann integral. In the
corresponding filter, we require that the diameters of all boxes `J` of a tagged partition are
bounded from above by a constant upper estimate that may not depend on the geometry of `J`, and each
tag belongs to the corresponding closed box. -/
/-
**BoxIntegral.IntegrationParams.Riemann** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegral.I
ntegrationParams`。
形式化陈述：Riemann : IntegrationParams where bRiemann
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `BoxIntegral.IntegrationParams` corresponding to the Riemann integral. In th
e
corresponding filter, we require that the diameters of all boxes `J` of a tagged
 partition are
bounded from above by a constant upper estimate that may not depend on the geome
try of `J`, and each
tag belongs to the corresponding closed box.
-/
def Riemann : IntegrationParams where
  bRiemann := true
  bHenstock := true
  bDistortion := false

/-- The `BoxIntegral.IntegrationParams` corresponding to the Henstock-Kurzweil integral. In the
corresponding filter, we require that the tagged partition is subordinate to a (possibly,
discontinuous) positive function `r` and each tag belongs to the corresponding closed box. -/
/-
**BoxIntegral.IntegrationParams.Henstock** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegral.
IntegrationParams`。
形式化陈述：Henstock : IntegrationParams
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `BoxIntegral.IntegrationParams` corresponding to the Henstock-Kurzweil integ
ral. In the
corresponding filter, we require that the tagged partition is subordinate to a (
possibly,
discontinuous) positive function `r` and each tag belongs to the corresponding c
losed box.
-/
def Henstock : IntegrationParams :=
  ⟨false, true, false⟩

/-- The `BoxIntegral.IntegrationParams` corresponding to the McShane integral. In the
corresponding filter, we require that the tagged partition is subordinate to a (possibly,
discontinuous) positive function `r`; the tags may be outside of the corresponding closed box
(but still inside the ambient closed box `I.Icc`). -/
/-
**BoxIntegral.IntegrationParams.McShane** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegral.I
ntegrationParams`。
形式化陈述：McShane : IntegrationParams
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `BoxIntegral.IntegrationParams` corresponding to the McShane integral. In th
e
corresponding filter, we require that the tagged partition is subordinate to a (
possibly,
discontinuous) positive function `r`; the tags may be outside of the correspondi
ng closed box
(but still inside the ambient closed box `I.Icc`).
-/
def McShane : IntegrationParams :=
  ⟨false, false, false⟩

/-- The `BoxIntegral.IntegrationParams` corresponding to the generalized Perron integral. In the
corresponding filter, we require that the tagged partition is subordinate to a (possibly,
discontinuous) positive function `r` and each tag belongs to the corresponding closed box. We also
require an upper estimate on the distortion of all boxes of the partition. -/
/-
**BoxIntegral.IntegrationParams.GP** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegral.Integr
ationParams`。
形式化陈述：GP : IntegrationParams
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `BoxIntegral.IntegrationParams` corresponding to the generalized Perron inte
gral. In the
corresponding filter, we require that the tagged partition is subordinate to a (
possibly,
discontinuous) positive function `r` and each tag belongs to the corresponding c
losed box. We also
require an upper estimate on the distortion of all boxes of the partition.
-/
def GP : IntegrationParams := ⊥
/-
**BoxIntegral.IntegrationParams.henstock_le_riemann** 是 Mathlib 中的一个定理，位于命名空间 `B
oxIntegral.IntegrationParams`。
形式化陈述：henstock_le_riemann : Henstock <= Riemann
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem henstock_le_riemann : Henstock ≤ Riemann := by trivial
/-
**BoxIntegral.IntegrationParams.henstock_le_mcShane** 是 Mathlib 中的一个定理，位于命名空间 `B
oxIntegral.IntegrationParams`。
形式化陈述：henstock_le_mcShane : Henstock <= McShane
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem henstock_le_mcShane : Henstock ≤ McShane := by trivial
/-
**BoxIntegral.IntegrationParams.gp_le** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegral.Int
egrationParams`。
形式化陈述：gp_le : GP <= l
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
theorem gp_le : GP ≤ l :=
  bot_le

/-- The predicate corresponding to a base set of the filter defined by an
`IntegrationParams`. It says that

* if `l.bHenstock`, then `π` is a Henstock prepartition, i.e. each tag belongs to the corresponding
  closed box;
* `π` is subordinate to `r`;
* if `l.bDistortion`, then the distortion of each box in `π` is less than or equal to `c`;
* if `l.bDistortion`, then there exists a prepartition `π'` with distortion `≤ c` that covers
  exactly `I \ π.iUnion`.

The last condition is automatically verified for partitions, and is used in the proof of the
Sacks-Henstock inequality to compare two prepartitions covering the same part of the box.

It is also automatically satisfied for any `c > 1`, see TODO section of the module docstring for
details. -/
/-
**BoxIntegral.IntegrationParams.MemBaseSet** 是 Mathlib 中的一个归纳类型，位于命名空间 `BoxInteg
ral.IntegrationParams`。
形式化陈述：{ι : Type u_1} →   [Fintype ι] →     BoxIntegral.IntegrationParams →      
 (I : BoxIntegral.Box ι) → NNReal → ((ι → ℝ) → ↑(Set.Ioi 0)) → BoxIntegral.Tagge
dPrepartition I → Prop
参数：I : BoxIntegral.Box ι；(ι → ℝ) → ↑(Set.Ioi 0)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The predicate corresponding to a base set of the filter defined by an
`IntegrationParams`. It says that

* if `l.bHenstock`, then `π` is a Henstock prepartition, i.e. each tag belongs t
o the corresponding
  closed box;
* `π` is subordinate to `r`;
* if `l.bDistortion`, then the distortion of each box in `π` is less than or equ
al to `c`;
* if `l.bDistortion`, then there exists a prepartition `π'` with distortion `≤ c
` that covers
  exactly `I \ π.iUnion`.

The last condition is automatically verified for partitions, and is used in the 
proof of the
Sacks-Henstock inequality to compare two prepartitions covering the same part of
 the box.

It is also automatically satisfied for any `c > 1`, see TODO section of the modu
le docstring for
details.
-/
structure MemBaseSet (l : IntegrationParams) (I : Box ι) (c : ℝ≥0) (r : (ι → ℝ) → Ioi (0 : ℝ))
    (π : TaggedPrepartition I) : Prop where
  protected isSubordinate : π.IsSubordinate r
  protected isHenstock : l.bHenstock → π.IsHenstock
  protected distortion_le : l.bDistortion → π.distortion ≤ c
  protected exists_compl : l.bDistortion → ∃ π' : Prepartition I,
    π'.iUnion = ↑I \ π.iUnion ∧ π'.distortion ≤ c

/-- A predicate saying that in case `l.bRiemann = true`, the function `r` is a constant. -/
/-
**BoxIntegral.IntegrationParams.RCond** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegral.Int
egrationParams`。
形式化陈述：RCond {ι : Type*} (l : IntegrationParams) (r : (ι -> Real) -> Ioi (0 : Rea
l)) : Prop
参数：l : IntegrationParams；r : (ι -> Real) -> Ioi (0 : Real)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A predicate saying that in case `l.bRiemann = true`, the function `r` is a const
ant.
-/
def RCond {ι : Type*} (l : IntegrationParams) (r : (ι → ℝ) → Ioi (0 : ℝ)) : Prop :=
  l.bRiemann → ∀ x, r x = r 0

/-- A set `s : Set (TaggedPrepartition I)` belongs to `l.toFilterDistortion I c` if there exists
a function `r : ℝⁿ → (0, ∞)` (or a constant `r` if `l.bRiemann = true`) such that `s` contains each
prepartition `π` such that `l.MemBaseSet I c r π`. -/
/-
**BoxIntegral.IntegrationParams.toFilterDistortion** 是 Mathlib 中的一个定义，位于命名空间 `Bo
xIntegral.IntegrationParams`。
形式化陈述：toFilterDistortion (l : IntegrationParams) (I : Box ι) (c : Real>=0) : Fil
ter (TaggedPrepartition I)
参数：l : IntegrationParams；I : Box ι；c : Real>=0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set `s : Set (TaggedPrepartition I)` belongs to `l.toFilterDistortion I c` if 
there exists
a function `r : ℝⁿ → (0, ∞)` (or a constant `r` if `l.bRiemann = true`) such tha
t `s` contains each
prepartition `π` such that `l.MemBaseSet I c r π`.
-/
def toFilterDistortion (l : IntegrationParams) (I : Box ι) (c : ℝ≥0) :
    Filter (TaggedPrepartition I) :=
  ⨅ (r : (ι → ℝ) → Ioi (0 : ℝ)) (_ : l.RCond r), 𝓟 { π | l.MemBaseSet I c r π }

/-- A set `s : Set (TaggedPrepartition I)` belongs to `l.toFilter I` if for any `c : ℝ≥0` there
exists a function `r : ℝⁿ → (0, ∞)` (or a constant `r` if `l.bRiemann = true`) such that
`s` contains each prepartition `π` such that `l.MemBaseSet I c r π`. -/
/-
**BoxIntegral.IntegrationParams.toFilter** 是 Mathlib 中的一个定义，位于命名空间 `BoxIntegral.
IntegrationParams`。
形式化陈述：toFilter (l : IntegrationParams) (I : Box ι) : Filter (TaggedPrepartition 
I)
参数：l : IntegrationParams；I : Box ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set `s : Set (TaggedPrepartition I)` belongs to `l.toFilter I` if for any `c :
 ℝ≥0` there
exists a function `r : ℝⁿ → (0, ∞)` (or a constant `r` if `l.bRiemann = true`) s
uch that
`s` contains each prepartition `π` such that `l.MemBaseSet I c r π`.
-/
def toFilter (l : IntegrationParams) (I : Box ι) : Filter (TaggedPrepartition I) :=
  ⨆ c : ℝ≥0, l.toFilterDistortion I c

/-- A set `s : Set (TaggedPrepartition I)` belongs to `l.toFilterDistortioniUnion I c π₀` if
there exists a function `r : ℝⁿ → (0, ∞)` (or a constant `r` if `l.bRiemann = true`) such that `s`
contains each prepartition `π` such that `l.MemBaseSet I c r π` and `π.iUnion = π₀.iUnion`. -/
/-
**BoxIntegral.IntegrationParams.toFilterDistortioniUnion** 是 Mathlib 中的一个定义，位于命名
空间 `BoxIntegral.IntegrationParams`。
形式化陈述：toFilterDistortioniUnion (l : IntegrationParams) (I : Box ι) (c : Real>=0)
 (π₀ : Prepartition I)
参数：l : IntegrationParams；I : Box ι；c : Real>=0；π₀ : Prepartition I。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set `s : Set (TaggedPrepartition I)` belongs to `l.toFilterDistortioniUnion I 
c π₀` if
there exists a function `r : ℝⁿ → (0, ∞)` (or a constant `r` if `l.bRiemann = tr
ue`) such that `s`
contains each prepartition `π` such that `l.MemBaseSet I c r π` and `π.iUnion = 
π₀.iUnion`.
-/
def toFilterDistortioniUnion (l : IntegrationParams) (I : Box ι) (c : ℝ≥0) (π₀ : Prepartition I) :=
  l.toFilterDistortion I c ⊓ 𝓟 { π | π.iUnion = π₀.iUnion }

/-- A set `s : Set (TaggedPrepartition I)` belongs to `l.toFilteriUnion I π₀` if for any `c : ℝ≥0`
there exists a function `r : ℝⁿ → (0, ∞)` (or a constant `r` if `l.bRiemann = true`) such that `s`
contains each prepartition `π` such that `l.MemBaseSet I c r π` and `π.iUnion = π₀.iUnion`. -/
/-
**BoxIntegral.IntegrationParams.toFilteriUnion** 是 Mathlib 中的一个定义，位于命名空间 `BoxInt
egral.IntegrationParams`。
形式化陈述：toFilteriUnion (I : Box ι) (π₀ : Prepartition I)
参数：I : Box ι；π₀ : Prepartition I。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set `s : Set (TaggedPrepartition I)` belongs to `l.toFilteriUnion I π₀` if for
 any `c : ℝ≥0`
there exists a function `r : ℝⁿ → (0, ∞)` (or a constant `r` if `l.bRiemann = tr
ue`) such that `s`
contains each prepartition `π` such that `l.MemBaseSet I c r π` and `π.iUnion = 
π₀.iUnion`.
-/
def toFilteriUnion (I : Box ι) (π₀ : Prepartition I) :=
  ⨆ c : ℝ≥0, l.toFilterDistortioniUnion I c π₀
/-
**BoxIntegral.IntegrationParams.rCond_of_bRiemann_eq_false** 是 Mathlib 中的一个定理，位于
命名空间 `BoxIntegral.IntegrationParams`。
形式化陈述：rCond_of_bRiemann_eq_false {ι} (l : IntegrationParams) (hl : l.bRiemann = 
false) {r : (ι -> Real) -> Ioi (0 : Real)} : l.RCond r
参数：l : IntegrationParams；hl : l.bRiemann = false；ι -> Real；0 : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
-/
theorem rCond_of_bRiemann_eq_false {ι} (l : IntegrationParams) (hl : l.bRiemann = false)
    {r : (ι → ℝ) → Ioi (0 : ℝ)} : l.RCond r := by
  simp [RCond, hl]
/-
**BoxIntegral.IntegrationParams.toFilter_inf_iUnion_eq** 是 Mathlib 中的一个定理，位于命名空间
 `BoxIntegral.IntegrationParams`。
形式化陈述：toFilter_inf_iUnion_eq (l : IntegrationParams) (I : Box ι) (π₀ : Prepartit
ion I) : l.toFilter I ⊓ 𝓟 { π | π.iUnion = π₀.iUnion } = l.toFilteriUnion I π₀
参数：l : IntegrationParams；I : Box ι；π₀ : Prepartition I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Filter.iSup_inf_principal`：iSup_inf_principal (f : ι -> Filter α) (s : S
et α) : ⨆ i, f i ⊓ 𝓟 s = (⨆ i, f i) ⊓ 𝓟 s
-/
theorem toFilter_inf_iUnion_eq (l : IntegrationParams) (I : Box ι) (π₀ : Prepartition I) :
    l.toFilter I ⊓ 𝓟 { π | π.iUnion = π₀.iUnion } = l.toFilteriUnion I π₀ :=
  (iSup_inf_principal _ _).symm

variable {r₁ r₂ : (ι → ℝ) → Ioi (0 : ℝ)} {π π₁ π₂ : TaggedPrepartition I}

variable (I) in
/-
**BoxIntegral.IntegrationParams.MemBaseSet.mono'** 是 Mathlib 中的一个定理，位于命名空间 `BoxI
ntegral.IntegrationParams.MemBaseSet`。
形式化陈述：∀ {ι : Type u_1} [inst : Fintype ι] (I : BoxIntegral.Box ι) {c₁ c₂ : NNRea
l} {l₁ l₂ : BoxIntegral.IntegrationParams}   {r₁ r₂ : (ι → ℝ) → ↑(Set.Ioi 0)} {π
 : BoxIntegral.TaggedPrepartition I},   l₁ ≤ l₂ → c₁ ≤ c₂ → (∀ J ∈ π, r₁ (π.tag 
J) ≤ r₂ (π.tag J)) → l₁.MemBaseSet I c₁ r₁ π → l₂.MemBaseSet I c₂ r₂ π
参数：I : BoxIntegral.Box ι；ι → ℝ；Set.Ioi 0；∀ J ∈ π, r₁ (π.tag J) ≤ r₂ (π.tag J)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.TaggedPrepartition.IsSubordinate.mono'`：∀ {ι : Type u_1} {I 
: BoxIntegral.Box ι} {r₁ r₂ : (ι → ℝ) → ↑(Set.Ioi 0)} [inst : Fintype ι]   {π : 
BoxIntegral.TaggedPrepartition I},   π.I…
· 使用定理 `BoxIntegral.IntegrationParams.MemBaseSet.isSubordinate`：∀ {ι : Type u_1}
 [inst : Fintype ι] {l : BoxIntegral.IntegrationParams} {I : BoxIntegral.Box ι} 
{c : NNReal}   {r : (ι → ℝ) → ↑(Set.Ioi 0)} …
· 使用定理 `BoxIntegral.IntegrationParams.MemBaseSet.isHenstock`：∀ {ι : Type u_1} [i
nst : Fintype ι] {l : BoxIntegral.IntegrationParams} {I : BoxIntegral.Box ι} {c 
: NNReal}   {r : (ι → ℝ) → ↑(Set.Ioi 0)} …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Bool.le_iff_imp`：le_iff_imp : forall {x y : Bool}, x <= y ↔ x -> y
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `BoxIntegral.IntegrationParams.MemBaseSet.distortion_le`：∀ {ι : Type u_1}
 [inst : Fintype ι] {l : BoxIntegral.IntegrationParams} {I : BoxIntegral.Box ι} 
{c : NNReal}   {r : (ι → ℝ) → ↑(Set.Ioi 0)} …
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `BoxIntegral.IntegrationParams.MemBaseSet.exists_compl`：∀ {ι : Type u_1} 
[inst : Fintype ι] {l : BoxIntegral.IntegrationParams} {I : BoxIntegral.Box ι} {
c : NNReal}   {r : (ι → ℝ) → ↑(Set.Ioi 0)} …
-/
theorem MemBaseSet.mono' (h : l₁ ≤ l₂) (hc : c₁ ≤ c₂)
    (hr : ∀ J ∈ π, r₁ (π.tag J) ≤ r₂ (π.tag J)) (hπ : l₁.MemBaseSet I c₁ r₁ π) :
    l₂.MemBaseSet I c₂ r₂ π :=
  ⟨hπ.1.mono' hr, fun h₂ => hπ.2 (le_iff_imp.1 h.2.1 h₂),
    fun hD => (hπ.3 (le_iff_imp.1 h.2.2 hD)).trans hc,
    fun hD => (hπ.4 (le_iff_imp.1 h.2.2 hD)).imp fun _ hπ => ⟨hπ.1, hπ.2.trans hc⟩⟩

variable (I) in
@[gcongr, mono]
/-
**BoxIntegral.IntegrationParams.MemBaseSet.mono** 是 Mathlib 中的一个定理，位于命名空间 `BoxIn
tegral.IntegrationParams.MemBaseSet`。
形式化陈述：∀ {ι : Type u_1} [inst : Fintype ι] (I : BoxIntegral.Box ι) {c₁ c₂ : NNRea
l} {l₁ l₂ : BoxIntegral.IntegrationParams}   {r₁ r₂ : (ι → ℝ) → ↑(Set.Ioi 0)} {π
 : BoxIntegral.TaggedPrepartition I},   l₁ ≤ l₂ → c₁ ≤ c₂ → (∀ x ∈ BoxIntegral.B
ox.Icc I, r₁ x ≤ r₂ x) → l₁.MemBaseSet I c₁ r₁ π → l₂.MemBaseSet I c₂ r₂ π
参数：I : BoxIntegral.Box ι；ι → ℝ；Set.Ioi 0；∀ x ∈ BoxIntegral.Box.Icc I, r₁ x ≤ r₂ 
x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.IntegrationParams.MemBaseSet.mono'`：∀ {ι : Type u_1} [inst :
 Fintype ι] (I : BoxIntegral.Box ι) {c₁ c₂ : NNReal} {l₁ l₂ : BoxIntegral.Integr
ationParams}   {r₁ r₂ : (ι → ℝ) → ↑(…
· 使用定理 `BoxIntegral.TaggedPrepartition.tag_mem_Icc`：∀ {ι : Type u_1} {I : BoxInt
egral.Box ι} (self : BoxIntegral.TaggedPrepartition I) (J : BoxIntegral.Box ι), 
  self.tag J ∈ BoxIntegral.Box.I…
-/
theorem MemBaseSet.mono (h : l₁ ≤ l₂) (hc : c₁ ≤ c₂)
    (hr : ∀ x ∈ Box.Icc I, r₁ x ≤ r₂ x) (hπ : l₁.MemBaseSet I c₁ r₁ π) : l₂.MemBaseSet I c₂ r₂ π :=
  hπ.mono' I h hc fun J _ => hr _ <| π.tag_mem_Icc J
/-
**BoxIntegral.IntegrationParams.MemBaseSet.exists_common_compl** 是 Mathlib 中的一个定
理，位于命名空间 `BoxIntegral.IntegrationParams.MemBaseSet`。
形式化陈述：∀ {ι : Type u_1} [inst : Fintype ι] {I : BoxIntegral.Box ι} {c₁ c₂ : NNRea
l} {l : BoxIntegral.IntegrationParams}   {r₁ r₂ : (ι → ℝ) → ↑(Set.Ioi 0)} {π₁ π₂
 : BoxIntegral.TaggedPrepartition I},   l.MemBaseSet I c₁ r₁ π₁ →     l.MemBaseS
et I c₂ r₂ π₂ →       π₁.iUnion = π₂.iUnion →         ∃ π,           π.iUnion = 
↑I \ π₁.iUnion ∧             (l.bDistortion = true → π.distortion ≤ c₁) ∧ (l.bDi
stortion = true → π.distortion ≤ c₂)
参数：ι → ℝ；Set.Ioi 0；l.bDistortion = true → π.distortion ≤ c₁；l.bDistortion = true
 → π.distortion ≤ c₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `BoxIntegral.IntegrationParams.MemBaseSet.exists_compl`：∀ {ι : Type u_1} 
[inst : Fintype ι] {l : BoxIntegral.IntegrationParams} {I : BoxIntegral.Box ι} {
c : NNReal}   {r : (ι → ℝ) → ↑(Set.Ioi 0)} …
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `BoxIntegral.Prepartition.iUnion_compl`：iUnion_compl (π : Prepartition I)
 : π.compl.iUnion = ↑I \ π.iUnion
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b 
→ b ≤ a
-/
theorem MemBaseSet.exists_common_compl
    (h₁ : l.MemBaseSet I c₁ r₁ π₁) (h₂ : l.MemBaseSet I c₂ r₂ π₂)
    (hU : π₁.iUnion = π₂.iUnion) :
    ∃ π : Prepartition I, π.iUnion = ↑I \ π₁.iUnion ∧
      (l.bDistortion → π.distortion ≤ c₁) ∧ (l.bDistortion → π.distortion ≤ c₂) := by
  wlog hc : c₁ ≤ c₂ with H
  · simpa [hU, _root_.and_comm] using
      @H _ _ I c₂ c₁ l r₂ r₁ π₂ π₁ h₂ h₁ hU.symm (le_of_not_ge hc)
  by_cases hD : (l.bDistortion : Prop)
  · rcases h₁.4 hD with ⟨π, hπU, hπc⟩
    exact ⟨π, hπU, fun _ => hπc, fun _ => hπc.trans hc⟩
  · exact ⟨π₁.toPrepartition.compl, π₁.toPrepartition.iUnion_compl,
      fun h => (hD h).elim, fun h => (hD h).elim⟩
/-
**BoxIntegral.IntegrationParams.MemBaseSet.unionComplToSubordinate** 是 Mathlib 中
的一个定理，位于命名空间 `BoxIntegral.IntegrationParams.MemBaseSet`。
形式化陈述：∀ {ι : Type u_1} [inst : Fintype ι] {I : BoxIntegral.Box ι} {c : NNReal} {
l : BoxIntegral.IntegrationParams}   {r₁ r₂ : (ι → ℝ) → ↑(Set.Ioi 0)} {π₁ : BoxI
ntegral.TaggedPrepartition I},   l.MemBaseSet I c r₁ π₁ →     (∀ x ∈ BoxIntegral
.Box.Icc I, r₂ x ≤ r₁ x) →       ∀ {π₂ : BoxIntegral.Prepartition I} (hU : π₂.iU
nion = ↑I \ π₁.iUnion),         (l.bDistortion = true → π₂.distortion ≤ c) → l.M
emBaseSet I c r₁ (π₁.unionComplToSubordinate π₂ hU r₂)
参数：ι → ℝ；Set.Ioi 0；∀ x ∈ BoxIntegral.Box.Icc I, r₂ x ≤ r₁ x；hU : π₂.iUnion = ↑I 
\ π₁.iUnion；l.bDistortion = true → π₂.distortion ≤ c；π₁.unionComplToSubordinate 
π₂ hU r₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.TaggedPrepartition.IsSubordinate.disjUnion`：∀ {ι : Type u_1}
 {I : BoxIntegral.Box ι} {π₁ π₂ : BoxIntegral.TaggedPrepartition I} {r : (ι → ℝ)
 → ↑(Set.Ioi 0)}   [inst : Fintype ι],   π₁.…
· 使用定理 `BoxIntegral.IntegrationParams.MemBaseSet.isSubordinate`：∀ {ι : Type u_1}
 [inst : Fintype ι] {l : BoxIntegral.IntegrationParams} {I : BoxIntegral.Box ι} 
{c : NNReal}   {r : (ι → ℝ) → ↑(Set.Ioi 0)} …
· 使用定理 `BoxIntegral.TaggedPrepartition.IsSubordinate.mono`：∀ {ι : Type u_1} {I :
 BoxIntegral.Box ι} {r₁ r₂ : (ι → ℝ) → ↑(Set.Ioi 0)} [inst : Fintype ι]   {π : B
oxIntegral.TaggedPrepartition I},   π.I…
· 使用定理 `BoxIntegral.Prepartition.isSubordinate_toSubordinate`：isSubordinate_toSu
bordinate (π : Prepartition I) (r : (ι -> Real) -> Ioi (0 : Real)) : (π.toSubord
inate r).IsSubordinate r
· 使用定理 `BoxIntegral.TaggedPrepartition.IsHenstock.disjUnion`：∀ {ι : Type u_1} {I
 : BoxIntegral.Box ι} {π₁ π₂ : BoxIntegral.TaggedPrepartition I},   π₁.IsHenstoc
k → π₂.IsHenstock → ∀ (h : Disjoint π₁.iU…
· 使用定理 `BoxIntegral.IntegrationParams.MemBaseSet.isHenstock`：∀ {ι : Type u_1} [i
nst : Fintype ι] {l : BoxIntegral.IntegrationParams} {I : BoxIntegral.Box ι} {c 
: NNReal}   {r : (ι → ℝ) → ↑(Set.Ioi 0)} …
· 使用定理 `BoxIntegral.Prepartition.isHenstock_toSubordinate`：isHenstock_toSubordin
ate (π : Prepartition I) (r : (ι -> Real) -> Ioi (0 : Real)) : (π.toSubordinate 
r).IsHenstock
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `BoxIntegral.TaggedPrepartition.distortion_unionComplToSubordinate`：disto
rtion_unionComplToSubordinate (π₁ : TaggedPrepartition I) (π₂ : Prepartition I) 
(hU : π₂.iUnion = ↑I \ π₁.iUnion) (r : (ι -> Real) -> I…
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
· 使用定理 `BoxIntegral.IntegrationParams.MemBaseSet.distortion_le`：∀ {ι : Type u_1}
 [inst : Fintype ι] {l : BoxIntegral.IntegrationParams} {I : BoxIntegral.Box ι} 
{c : NNReal}   {r : (ι → ℝ) → ↑(Set.Ioi 0)} …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.Prepartition.iUnion_bot`：iUnion_bot : (⊥ : Prepartition I).i
Union = ∅
· 使用定理 `BoxIntegral.TaggedPrepartition.iUnion_unionComplToSubordinate_boxes`：iUn
ion_unionComplToSubordinate_boxes (π₁ : TaggedPrepartition I) (π₂ : Prepartition
 I) (hU : π₂.iUnion = ↑I \ π₁.iUnion) (r : (ι -> Real) ->…
· 使用定理 `sdiff_self`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a :
 α}, a \ a = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `BoxIntegral.Prepartition.distortion_bot`：distortion_bot (I : Box ι) : di
stortion (⊥ : Prepartition I) = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
protected theorem MemBaseSet.unionComplToSubordinate (hπ₁ : l.MemBaseSet I c r₁ π₁)
    (hle : ∀ x ∈ Box.Icc I, r₂ x ≤ r₁ x) {π₂ : Prepartition I} (hU : π₂.iUnion = ↑I \ π₁.iUnion)
    (hc : l.bDistortion → π₂.distortion ≤ c) :
    l.MemBaseSet I c r₁ (π₁.unionComplToSubordinate π₂ hU r₂) :=
  ⟨hπ₁.1.disjUnion ((π₂.isSubordinate_toSubordinate r₂).mono hle) _,
    fun h => (hπ₁.2 h).disjUnion (π₂.isHenstock_toSubordinate _) _,
    fun h => (distortion_unionComplToSubordinate _ _ _ _).trans_le (max_le (hπ₁.3 h) (hc h)),
    fun _ => ⟨⊥, by simp⟩⟩

variable {r : (ι → ℝ) → Ioi (0 : ℝ)}

set_option backward.isDefEq.respectTransparency false in
/-
**BoxIntegral.IntegrationParams.MemBaseSet.filter** 是 Mathlib 中的一个定理，位于命名空间 `Box
Integral.IntegrationParams.MemBaseSet`。
形式化陈述：∀ {ι : Type u_1} [inst : Fintype ι] {I : BoxIntegral.Box ι} {c : NNReal} {
l : BoxIntegral.IntegrationParams}   {π : BoxIntegral.TaggedPrepartition I} {r :
 (ι → ℝ) → ↑(Set.Ioi 0)},   l.MemBaseSet I c r π → ∀ (p : BoxIntegral.Box ι → Pr
op), l.MemBaseSet I c r (π.filter p)
参数：ι → ℝ；Set.Ioi 0；p : BoxIntegral.Box ι → Prop；π.filter p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.IntegrationParams.MemBaseSet.isSubordinate`：∀ {ι : Type u_1}
 [inst : Fintype ι] {l : BoxIntegral.IntegrationParams} {I : BoxIntegral.Box ι} 
{c : NNReal}   {r : (ι → ℝ) → ↑(Set.Ioi 0)} …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `BoxIntegral.TaggedPrepartition.mem_filter`：mem_filter {p : Box ι -> Prop
} : J in π.filter p ↔ J in π ∧ p J
· 使用定理 `BoxIntegral.IntegrationParams.MemBaseSet.isHenstock`：∀ {ι : Type u_1} [i
nst : Fintype ι] {l : BoxIntegral.IntegrationParams} {I : BoxIntegral.Box ι} {c 
: NNReal}   {r : (ι → ℝ) → ↑(Set.Ioi 0)} …
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `BoxIntegral.TaggedPrepartition.distortion_filter_le`：distortion_filter_l
e (p : Box ι -> Prop) : (π.filter p).distortion <= π.distortion
· 使用定理 `BoxIntegral.IntegrationParams.MemBaseSet.distortion_le`：∀ {ι : Type u_1}
 [inst : Fintype ι] {l : BoxIntegral.IntegrationParams} {I : BoxIntegral.Box ι} 
{c : NNReal}   {r : (ι → ℝ) → ↑(Set.Ioi 0)} …
· 使用定理 `BoxIntegral.IntegrationParams.MemBaseSet.exists_compl`：∀ {ι : Type u_1} 
[inst : Fintype ι] {l : BoxIntegral.IntegrationParams} {I : BoxIntegral.Box ι} {
c : NNReal}   {r : (ι → ℝ) → ↑(Set.Ioi 0)} …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.TaggedPrepartition.iUnion_filter_not`：iUnion_filter_not (π :
 TaggedPrepartition I) (p : Box ι -> Prop) : (π.filter fun J => ¬p J).iUnion = π
.iUnion \ (π.filter p).iUnion
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用定理 `sdiff_le`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a b :
 α}, a \ b ≤ a
· 使用定理 `disjoint_sdiff_self_left`：disjoint_sdiff_self_left : Disjoint (y \ x) x
· 使用定理 `Set.biUnion_subset_biUnion_left`：biUnion_subset_biUnion_left {s s' : Set
 α} {t : α -> Set β} (h : s subseteq s') : ⋃ x in s, t x subseteq ⋃ x in s', t x
· 使用定理 `Finset.filter_subset`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidableP
red p] (s : Finset α), Finset.filter p s ⊆ s
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `BoxIntegral.TaggedPrepartition.iUnion_subset`：iUnion_subset : π.iUnion s
ubseteq I
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `BoxIntegral.Prepartition.iUnion_disjUnion`：iUnion_disjUnion (h : Disjoin
t π₁.iUnion π₂.iUnion) : (π₁.disjUnion π₂ h).iUnion = π₁.iUnion union π₂.iUnion
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `BoxIntegral.Prepartition.distortion_disjUnion`：distortion_disjUnion (h :
 Disjoint π₁.iUnion π₂.iUnion) : (π₁.disjUnion π₂ h).distortion = max π₁.distort
ion π₂.distortion
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
protected theorem MemBaseSet.filter (hπ : l.MemBaseSet I c r π) (p : Box ι → Prop) :
    l.MemBaseSet I c r (π.filter p) := by
  classical
  refine ⟨fun J hJ => hπ.1 J (π.mem_filter.1 hJ).1, fun hH J hJ => hπ.2 hH J (π.mem_filter.1 hJ).1,
    fun hD => (distortion_filter_le _ _).trans (hπ.3 hD), fun hD => ?_⟩
  rcases hπ.4 hD with ⟨π₁, hπ₁U, hc⟩
  set π₂ := π.filter fun J => ¬p J
  have : Disjoint π₁.iUnion π₂.iUnion := by
    simpa [π₂, hπ₁U] using disjoint_sdiff_self_left.mono_right sdiff_le
  refine ⟨π₁.disjUnion π₂.toPrepartition this, ?_, ?_⟩
  · suffices ↑I \ π.iUnion ∪ π.iUnion \ (π.filter p).iUnion = ↑I \ (π.filter p).iUnion by
      simp [π₂, *]
    have h : (π.filter p).iUnion ⊆ π.iUnion :=
      biUnion_subset_biUnion_left (Finset.filter_subset _ _)
    ext x
    fconstructor
    · rintro (⟨hxI, hxπ⟩ | ⟨hxπ, hxp⟩)
      exacts [⟨hxI, mt (@h x) hxπ⟩, ⟨π.iUnion_subset hxπ, hxp⟩]
    · rintro ⟨hxI, hxp⟩
      by_cases hxπ : x ∈ π.iUnion
      exacts [Or.inr ⟨hxπ, hxp⟩, Or.inl ⟨hxI, hxπ⟩]
  · have : (π.filter fun J => ¬p J).distortion ≤ c := (distortion_filter_le _ _).trans (hπ.3 hD)
    simpa [hc]
/-
**BoxIntegral.IntegrationParams.biUnionTagged_memBaseSet** 是 Mathlib 中的一个定理，位于命名
空间 `BoxIntegral.IntegrationParams`。
形式化陈述：biUnionTagged_memBaseSet {π : Prepartition I} {πi : forall J, TaggedPrepar
tition J} (h : forall J in π, l.MemBaseSet J c r (πi J)) (hp : forall J in π, (π
i J).IsPartition) (hc : l.bDistortion -> π.compl.distortion <= c) : l.MemBaseSet
 I c r (π.biUnionTagged πi)
参数：h : forall J in π, l.MemBaseSet J c r (πi J)；hp : forall J in π, (πi J).IsPar
tition；hc : l.bDistortion -> π.compl.distortion <= c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `BoxIntegral.TaggedPrepartition.isSubordinate_biUnionTagged`：isSubordinat
e_biUnionTagged [Fintype ι] {π : Prepartition I} {πi : forall J, TaggedPrepartit
ion J} : IsSubordinate (π.biUnionTagged πi) r ↔ …
· 使用定理 `BoxIntegral.IntegrationParams.MemBaseSet.isSubordinate`：∀ {ι : Type u_1}
 [inst : Fintype ι] {l : BoxIntegral.IntegrationParams} {I : BoxIntegral.Box ι} 
{c : NNReal}   {r : (ι → ℝ) → ↑(Set.Ioi 0)} …
· 使用定理 `BoxIntegral.TaggedPrepartition.isHenstock_biUnionTagged`：isHenstock_biUn
ionTagged {π : Prepartition I} {πi : forall J, TaggedPrepartition J} : IsHenstoc
k (π.biUnionTagged πi) ↔ forall J in π, (πi J…
· 使用定理 `BoxIntegral.IntegrationParams.MemBaseSet.isHenstock`：∀ {ι : Type u_1} [i
nst : Fintype ι] {l : BoxIntegral.IntegrationParams} {I : BoxIntegral.Box ι} {c 
: NNReal}   {r : (ι → ℝ) → ↑(Set.Ioi 0)} …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BoxIntegral.Prepartition.distortion_biUnionTagged`：∀ {ι : Type u_1} {I :
 BoxIntegral.Box ι} [inst : Fintype ι] (π : BoxIntegral.Prepartition I)   (πi : 
(J : BoxIntegral.Box ι) → BoxIntegral.T…
· 使用定理 `Finset.sup_le_iff`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   s.sup f ≤ a ↔ ∀
 b ∈ s,…
· 使用定理 `BoxIntegral.IntegrationParams.MemBaseSet.distortion_le`：∀ {ι : Type u_1}
 [inst : Fintype ι] {l : BoxIntegral.IntegrationParams} {I : BoxIntegral.Box ι} 
{c : NNReal}   {r : (ι → ℝ) → ↑(Set.Ioi 0)} …
· 使用定理 `BoxIntegral.Prepartition.iUnion_compl`：iUnion_compl (π : Prepartition I)
 : π.compl.iUnion = ↑I \ π.iUnion
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `BoxIntegral.Prepartition.iUnion_biUnion_partition`：iUnion_biUnion_partit
ion (h : forall J in π, (πi J).IsPartition) : (π.biUnion πi).iUnion = π.iUnion
-/
theorem biUnionTagged_memBaseSet {π : Prepartition I} {πi : ∀ J, TaggedPrepartition J}
    (h : ∀ J ∈ π, l.MemBaseSet J c r (πi J)) (hp : ∀ J ∈ π, (πi J).IsPartition)
    (hc : l.bDistortion → π.compl.distortion ≤ c) : l.MemBaseSet I c r (π.biUnionTagged πi) := by
  refine ⟨TaggedPrepartition.isSubordinate_biUnionTagged.2 fun J hJ => (h J hJ).1,
    fun hH => TaggedPrepartition.isHenstock_biUnionTagged.2 fun J hJ => (h J hJ).2 hH,
    fun hD => ?_, fun hD => ?_⟩
  · rw [Prepartition.distortion_biUnionTagged, Finset.sup_le_iff]
    exact fun J hJ => (h J hJ).3 hD
  · refine ⟨_, ?_, hc hD⟩
    rw [π.iUnion_compl, ← π.iUnion_biUnion_partition hp]
    rfl

@[gcongr, mono]
/-
**BoxIntegral.IntegrationParams.RCond.mono** 是 Mathlib 中的一个定理，位于命名空间 `BoxIntegra
l.IntegrationParams.RCond`。
形式化陈述：∀ {l₁ l₂ : BoxIntegral.IntegrationParams} {ι : Type u_2} {r : (ι → ℝ) → ↑(
Set.Ioi 0)}, l₁ ≤ l₂ → l₂.RCond r → l₁.RCond r
参数：ι → ℝ；Set.Ioi 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Bool.le_iff_imp`：le_iff_imp : forall {x y : Bool}, x <= y ↔ x -> y
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem RCond.mono {ι : Type*} {r : (ι → ℝ) → Ioi (0 : ℝ)} (h : l₁ ≤ l₂) (hr : l₂.RCond r) :
    l₁.RCond r :=
  fun hR => hr (le_iff_imp.1 h.1 hR)

nonrec theorem RCond.min {ι : Type*} {r₁ r₂ : (ι → ℝ) → Ioi (0 : ℝ)} (h₁ : l.RCond r₁)
    (h₂ : l.RCond r₂) : l.RCond fun x => min (r₁ x) (r₂ x) :=
  fun hR x => congr_arg₂ min (h₁ hR x) (h₂ hR x)

@[gcongr, mono]
/-
**BoxIntegral.IntegrationParams.toFilterDistortion_mono** 是 Mathlib 中的一个定理，位于命名空
间 `BoxIntegral.IntegrationParams`。
形式化陈述：toFilterDistortion_mono (I : Box ι) (h : l₁ <= l₂) (hc : c₁ <= c₂) : l₁.to
FilterDistortion I c₁ <= l₂.toFilterDistortion I c₂
参数：I : Box ι；h : l₁ <= l₂；hc : c₁ <= c₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_mono`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f
 g : ι → α}, (∀ (i : ι), g i ≤ f i) → iInf g ≤ iInf f
· 使用定理 `iInf_mono'`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} [inst : Comp
leteLattice α] {f : ι → α} {g : ι' → α},   (∀ (i : ι), ∃ i', g i' ≤ f i) → iInf 
…
· 使用定理 `BoxIntegral.IntegrationParams.RCond.mono`：∀ {l₁ l₂ : BoxIntegral.Integra
tionParams} {ι : Type u_2} {r : (ι → ℝ) → ↑(Set.Ioi 0)}, l₁ ≤ l₂ → l₂.RCond r → 
l₁.RCond r
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.principal_mono`：principal_mono {s t : Set α} : 𝓟 s <= 𝓟 t ↔ s sub
seteq t
· 使用定理 `BoxIntegral.IntegrationParams.MemBaseSet.mono`：∀ {ι : Type u_1} [inst : 
Fintype ι] (I : BoxIntegral.Box ι) {c₁ c₂ : NNReal} {l₁ l₂ : BoxIntegral.Integra
tionParams}   {r₁ r₂ : (ι → ℝ) → ↑(…
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem toFilterDistortion_mono (I : Box ι) (h : l₁ ≤ l₂) (hc : c₁ ≤ c₂) :
    l₁.toFilterDistortion I c₁ ≤ l₂.toFilterDistortion I c₂ :=
  iInf_mono fun _ =>
    iInf_mono' fun hr =>
      ⟨hr.mono h, principal_mono.2 fun _ => MemBaseSet.mono I h hc fun _ _ => le_rfl⟩

@[gcongr, mono]
/-
**BoxIntegral.IntegrationParams.toFilter_mono** 是 Mathlib 中的一个定理，位于命名空间 `BoxInte
gral.IntegrationParams`。
形式化陈述：toFilter_mono (I : Box ι) {l₁ l₂ : IntegrationParams} (h : l₁ <= l₂) : l₁.
toFilter I <= l₂.toFilter I
参数：I : Box ι；h : l₁ <= l₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_mono`：iSup_mono (h : forall i, f i <= g i) : iSup f <= iSup g
· 使用定理 `BoxIntegral.IntegrationParams.toFilterDistortion_mono`：toFilterDistortio
n_mono (I : Box ι) (h : l₁ <= l₂) (hc : c₁ <= c₂) : l₁.toFilterDistortion I c₁ <
= l₂.toFilterDistortion I c₂
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem toFilter_mono (I : Box ι) {l₁ l₂ : IntegrationParams} (h : l₁ ≤ l₂) :
    l₁.toFilter I ≤ l₂.toFilter I :=
  iSup_mono fun _ => toFilterDistortion_mono I h le_rfl

@[gcongr, mono]
/-
**BoxIntegral.IntegrationParams.toFilteriUnion_mono** 是 Mathlib 中的一个定理，位于命名空间 `B
oxIntegral.IntegrationParams`。
形式化陈述：toFilteriUnion_mono (I : Box ι) {l₁ l₂ : IntegrationParams} (h : l₁ <= l₂)
 (π₀ : Prepartition I) : l₁.toFilteriUnion I π₀ <= l₂.toFilteriUnion I π₀
参数：I : Box ι；h : l₁ <= l₂；π₀ : Prepartition I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_mono`：iSup_mono (h : forall i, f i <= g i) : iSup f <= iSup g
· 使用定理 `inf_le_inf_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α} (c 
: α), b ≤ a → b ⊓ c ≤ a ⊓ c
· 使用定理 `BoxIntegral.IntegrationParams.toFilterDistortion_mono`：toFilterDistortio
n_mono (I : Box ι) (h : l₁ <= l₂) (hc : c₁ <= c₂) : l₁.toFilterDistortion I c₁ <
= l₂.toFilterDistortion I c₂
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem toFilteriUnion_mono (I : Box ι) {l₁ l₂ : IntegrationParams} (h : l₁ ≤ l₂)
    (π₀ : Prepartition I) : l₁.toFilteriUnion I π₀ ≤ l₂.toFilteriUnion I π₀ :=
  iSup_mono fun _ => inf_le_inf_right _ <| toFilterDistortion_mono _ h le_rfl
/-
**BoxIntegral.IntegrationParams.toFilteriUnion_congr** 是 Mathlib 中的一个定理，位于命名空间 `
BoxIntegral.IntegrationParams`。
形式化陈述：toFilteriUnion_congr (I : Box ι) (l : IntegrationParams) {π₁ π₂ : Preparti
tion I} (h : π₁.iUnion = π₂.iUnion) : l.toFilteriUnion I π₁ = l.toFilteriUnion I
 π₂
参数：I : Box ι；l : IntegrationParams；h : π₁.iUnion = π₂.iUnion。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toFilteriUnion_congr (I : Box ι) (l : IntegrationParams) {π₁ π₂ : Prepartition I}
    (h : π₁.iUnion = π₂.iUnion) : l.toFilteriUnion I π₁ = l.toFilteriUnion I π₂ := by
  simp only [toFilteriUnion, toFilterDistortioniUnion, h]
/-
**BoxIntegral.IntegrationParams.hasBasis_toFilterDistortion** 是 Mathlib 中的一个定理，位
于命名空间 `BoxIntegral.IntegrationParams`。
形式化陈述：hasBasis_toFilterDistortion (l : IntegrationParams) (I : Box ι) (c : Real>
=0) : (l.toFilterDistortion I c).HasBasis l.RCond fun r => { π | l.MemBaseSet I 
c r π }
参数：l : IntegrationParams；I : Box ι；c : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.hasBasis_biInf_principal'`：hasBasis_biInf_principal' {ι : Type*} 
{p : ι -> Prop} {s : ι -> Set α} (h : forall i, p i -> forall j, p j -> exists k
, p k ∧ s k subseteq s…
· 使用定理 `Std.instMinEqOrOfLawfulOrderLeftLeaningMin`：∀ {α : Type u} [inst : LE α]
 [inst_1 : Min α] [Std.LawfulOrderLeftLeaningMin α], Std.MinEqOr α
· 使用定理 `Std.instLawfulOrderLeftLeaningMinOfIsLinearOrderOfLawfulOrderInf`：∀ {α :
 Type u} [inst : LE α] [inst_1 : Min α] [Std.IsLinearOrder α] [Std.LawfulOrderIn
f α],   Std.LawfulOrderLeftLeaningMin α
· 使用定理 `instIsLinearOrder_mathlib`：∀ {α : Type u_1} [inst : LinearOrder α], Std.
IsLinearOrder α
· 使用定理 `instLawfulOrderInf_mathlib`：∀ {α : Type u} [inst : LinearOrder α], Std.L
awfulOrderInf α
· 使用定理 `BoxIntegral.IntegrationParams.RCond.min`：∀ {l : BoxIntegral.IntegrationP
arams} {ι : Type u_2} {r₁ r₂ : (ι → ℝ) → ↑(Set.Ioi 0)},   l.RCond r₁ → l.RCond r
₂ → l.RCond fun x => min (r₁ …
· 使用定理 `BoxIntegral.IntegrationParams.MemBaseSet.mono`：∀ {ι : Type u_1} [inst : 
Fintype ι] (I : BoxIntegral.Box ι) {c₁ c₂ : NNReal} {l₁ l₂ : BoxIntegral.Integra
tionParams}   {r₁ r₂ : (ι → ℝ) → ↑(…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用引理 `min_le_right`：min_le_right (a b : α) : min a b <= b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Ioi
 b ↔ b < x
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem hasBasis_toFilterDistortion (l : IntegrationParams) (I : Box ι) (c : ℝ≥0) :
    (l.toFilterDistortion I c).HasBasis l.RCond fun r => { π | l.MemBaseSet I c r π } :=
  hasBasis_biInf_principal'
    (fun _ hr₁ _ hr₂ =>
      ⟨_, hr₁.min hr₂, fun _ => MemBaseSet.mono _ le_rfl le_rfl fun _ _ => min_le_left _ _,
        fun _ => MemBaseSet.mono _ le_rfl le_rfl fun _ _ => min_le_right _ _⟩)
    ⟨fun _ => ⟨1, Set.mem_Ioi.2 zero_lt_one⟩, fun _ _ => rfl⟩
/-
**BoxIntegral.IntegrationParams.hasBasis_toFilterDistortioniUnion** 是 Mathlib 中的
一个定理，位于命名空间 `BoxIntegral.IntegrationParams`。
形式化陈述：hasBasis_toFilterDistortioniUnion (l : IntegrationParams) (I : Box ι) (c :
 Real>=0) (π₀ : Prepartition I) : (l.toFilterDistortioniUnion I c π₀).HasBasis l
.RCond fun r => { π | l.MemBaseSet I c r π ∧ π.iUnion = π₀.iUnion }
参数：l : IntegrationParams；I : Box ι；c : Real>=0；π₀ : Prepartition I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.inf_principal`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filt
er α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ (s' : Set α), (l ⊓ Fi
lter.principal s').…
· 使用定理 `BoxIntegral.IntegrationParams.hasBasis_toFilterDistortion`：hasBasis_toFi
lterDistortion (l : IntegrationParams) (I : Box ι) (c : Real>=0) : (l.toFilterDi
stortion I c).HasBasis l.RCond fun r => { π | l…
-/
theorem hasBasis_toFilterDistortioniUnion (l : IntegrationParams) (I : Box ι) (c : ℝ≥0)
    (π₀ : Prepartition I) :
    (l.toFilterDistortioniUnion I c π₀).HasBasis l.RCond fun r =>
      { π | l.MemBaseSet I c r π ∧ π.iUnion = π₀.iUnion } :=
  (l.hasBasis_toFilterDistortion I c).inf_principal _
/-
**BoxIntegral.IntegrationParams.hasBasis_toFilteriUnion** 是 Mathlib 中的一个定理，位于命名空
间 `BoxIntegral.IntegrationParams`。
形式化陈述：hasBasis_toFilteriUnion (l : IntegrationParams) (I : Box ι) (π₀ : Preparti
tion I) : (l.toFilteriUnion I π₀).HasBasis (fun r : Real>=0 -> (ι -> Real) -> Io
i (0 : Real) => forall c, l.RCond (r c)) fun r => { π | exists c, l.MemBaseSet I
 c (r c) π ∧ π.iUnion = π₀.iUnion }
参数：l : IntegrationParams；I : Box ι；π₀ : Prepartition I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.IntegrationParams.hasBasis_toFilterDistortioniUnion`：hasBasi
s_toFilterDistortioniUnion (l : IntegrationParams) (I : Box ι) (c : Real>=0) (π₀
 : Prepartition I) : (l.toFilterDistortioniUnion I c …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ofPred_exists`：ofPred_exists (p : ι -> β -> Prop) : { x | exists i, 
p i x } = ⋃ i, { x | p i x }
· 使用定理 `Filter.hasBasis_iSup`：hasBasis_iSup {ι : Sort*} {ι' : ι -> Type*} {l : ι
 -> Filter α} {p : forall i, ι' i -> Prop} {s : forall i, ι' i -> Set α} (hl : f
orall i, (…
-/
theorem hasBasis_toFilteriUnion (l : IntegrationParams) (I : Box ι) (π₀ : Prepartition I) :
    (l.toFilteriUnion I π₀).HasBasis (fun r : ℝ≥0 → (ι → ℝ) → Ioi (0 : ℝ) => ∀ c, l.RCond (r c))
      fun r => { π | ∃ c, l.MemBaseSet I c (r c) π ∧ π.iUnion = π₀.iUnion } := by
  have := fun c => l.hasBasis_toFilterDistortioniUnion I c π₀
  simpa only [ofPred_and, ofPred_exists] using! hasBasis_iSup this
/-
**BoxIntegral.IntegrationParams.hasBasis_toFilteriUnion_top** 是 Mathlib 中的一个定理，位
于命名空间 `BoxIntegral.IntegrationParams`。
形式化陈述：hasBasis_toFilteriUnion_top (l : IntegrationParams) (I : Box ι) : (l.toFil
teriUnion I ⊤).HasBasis (fun r : Real>=0 -> (ι -> Real) -> Ioi (0 : Real) => for
all c, l.RCond (r c)) fun r => { π | exists c, l.MemBaseSet I c (r c) π ∧ π.IsPa
rtition }
参数：l : IntegrationParams；I : Box ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `BoxIntegral.Prepartition.iUnion_top`：iUnion_top : (⊤ : Prepartition I).i
Union = I
· 使用定理 `BoxIntegral.IntegrationParams.hasBasis_toFilteriUnion`：hasBasis_toFilter
iUnion (l : IntegrationParams) (I : Box ι) (π₀ : Prepartition I) : (l.toFilteriU
nion I π₀).HasBasis (fun r : Real>=0 -> (ι …
-/
theorem hasBasis_toFilteriUnion_top (l : IntegrationParams) (I : Box ι) :
    (l.toFilteriUnion I ⊤).HasBasis (fun r : ℝ≥0 → (ι → ℝ) → Ioi (0 : ℝ) => ∀ c, l.RCond (r c))
      fun r => { π | ∃ c, l.MemBaseSet I c (r c) π ∧ π.IsPartition } := by
  simpa only [TaggedPrepartition.isPartition_iff_iUnion_eq, Prepartition.iUnion_top] using
    l.hasBasis_toFilteriUnion I ⊤
/-
**BoxIntegral.IntegrationParams.hasBasis_toFilter** 是 Mathlib 中的一个定理，位于命名空间 `Box
Integral.IntegrationParams`。
形式化陈述：hasBasis_toFilter (l : IntegrationParams) (I : Box ι) : (l.toFilter I).Has
Basis (fun r : Real>=0 -> (ι -> Real) -> Ioi (0 : Real) => forall c, l.RCond (r 
c)) fun r => { π | exists c, l.MemBaseSet I c (r c) π }
参数：l : IntegrationParams；I : Box ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ofPred_exists`：ofPred_exists (p : ι -> β -> Prop) : { x | exists i, 
p i x } = ⋃ i, { x | p i x }
· 使用定理 `Filter.hasBasis_iSup`：hasBasis_iSup {ι : Sort*} {ι' : ι -> Type*} {l : ι
 -> Filter α} {p : forall i, ι' i -> Prop} {s : forall i, ι' i -> Set α} (hl : f
orall i, (…
· 使用定理 `BoxIntegral.IntegrationParams.hasBasis_toFilterDistortion`：hasBasis_toFi
lterDistortion (l : IntegrationParams) (I : Box ι) (c : Real>=0) : (l.toFilterDi
stortion I c).HasBasis l.RCond fun r => { π | l…
-/
theorem hasBasis_toFilter (l : IntegrationParams) (I : Box ι) :
    (l.toFilter I).HasBasis (fun r : ℝ≥0 → (ι → ℝ) → Ioi (0 : ℝ) => ∀ c, l.RCond (r c))
      fun r => { π | ∃ c, l.MemBaseSet I c (r c) π } := by
  simpa only [ofPred_exists] using! hasBasis_iSup (l.hasBasis_toFilterDistortion I)
/-
**BoxIntegral.IntegrationParams.tendsto_embedBox_toFilteriUnion_top** 是 Mathlib 
中的一个定理，位于命名空间 `BoxIntegral.IntegrationParams`。
形式化陈述：tendsto_embedBox_toFilteriUnion_top (l : IntegrationParams) (h : I <= J) :
 Tendsto (TaggedPrepartition.embedBox I J h) (l.toFilteriUnion I ⊤) (l.toFilteri
Union J (Prepartition.single J I h))
参数：l : IntegrationParams；h : I <= J。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用定理 `BoxIntegral.IntegrationParams.hasBasis_toFilterDistortioniUnion`：hasBasi
s_toFilterDistortioniUnion (l : IntegrationParams) (I : Box ι) (c : Real>=0) (π₀
 : Prepartition I) : (l.toFilterDistortioniUnion I c …
· 使用定理 `BoxIntegral.IntegrationParams.MemBaseSet.isSubordinate`：∀ {ι : Type u_1}
 [inst : Fintype ι] {l : BoxIntegral.IntegrationParams} {I : BoxIntegral.Box ι} 
{c : NNReal}   {r : (ι → ℝ) → ↑(Set.Ioi 0)} …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `BoxIntegral.Prepartition.iUnion_top`：iUnion_top : (⊤ : Prepartition I).i
Union = I
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `BoxIntegral.IntegrationParams.MemBaseSet.isHenstock`：∀ {ι : Type u_1} [i
nst : Fintype ι] {l : BoxIntegral.IntegrationParams} {I : BoxIntegral.Box ι} {c 
: NNReal}   {r : (ι → ℝ) → ↑(Set.Ioi 0)} …
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `BoxIntegral.IntegrationParams.MemBaseSet.distortion_le`：∀ {ι : Type u_1}
 [inst : Fintype ι] {l : BoxIntegral.IntegrationParams} {I : BoxIntegral.Box ι} 
{c : NNReal}   {r : (ι → ℝ) → ↑(Set.Ioi 0)} …
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `BoxIntegral.Prepartition.iUnion_compl`：iUnion_compl (π : Prepartition I)
 : π.compl.iUnion = ↑I \ π.iUnion
· 使用定理 `BoxIntegral.Prepartition.iUnion_single`：iUnion_single (h : J <= I) : (si
ngle I J h).iUnion = J
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
-/
theorem tendsto_embedBox_toFilteriUnion_top (l : IntegrationParams) (h : I ≤ J) :
    Tendsto (TaggedPrepartition.embedBox I J h) (l.toFilteriUnion I ⊤)
      (l.toFilteriUnion J (Prepartition.single J I h)) := by
  simp only [toFilteriUnion, tendsto_iSup]; intro c
  set π₀ := Prepartition.single J I h
  refine le_iSup_of_le (max c π₀.compl.distortion) ?_
  refine ((l.hasBasis_toFilterDistortioniUnion I c ⊤).tendsto_iff
    (l.hasBasis_toFilterDistortioniUnion J _ _)).2 fun r hr => ?_
  refine ⟨r, hr, fun π hπ => ?_⟩
  rw [mem_ofPred_eq, Prepartition.iUnion_top] at hπ
  refine ⟨⟨hπ.1.1, hπ.1.2, fun hD => le_trans (hπ.1.3 hD) (le_max_left _ _), fun _ => ?_⟩, ?_⟩
  · refine ⟨_, π₀.iUnion_compl.trans ?_, le_max_right _ _⟩
    congr 1
    exact (Prepartition.iUnion_single h).trans hπ.2.symm
  · exact hπ.2.trans (Prepartition.iUnion_single _).symm
/-
**BoxIntegral.IntegrationParams.exists_memBaseSet_le_iUnion_eq** 是 Mathlib 中的一个定
理，位于命名空间 `BoxIntegral.IntegrationParams`。
形式化陈述：exists_memBaseSet_le_iUnion_eq (l : IntegrationParams) (π₀ : Prepartition 
I) (hc₁ : π₀.distortion <= c) (hc₂ : π₀.compl.distortion <= c) (r : (ι -> Real) 
-> Ioi (0 : Real)) : exists π, l.MemBaseSet I c r π ∧ π.toPrepartition <= π₀ ∧ π
.iUnion = π₀.iUnion
参数：l : IntegrationParams；π₀ : Prepartition I；hc₁ : π₀.distortion <= c；hc₂ : π₀.c
ompl.distortion <= c；r : (ι -> Real) -> Ioi (0 : Real)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `BoxIntegral.Prepartition.exists_tagged_le_isHenstock_isSubordinate_iUnio
n_eq`：exists_tagged_le_isHenstock_isSubordinate_iUnion_eq {I : Box ι} (r : (ι ->
 Real) -> Ioi (0 : Real)) (π : Prepartition I) : exists π' : Tagge…
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `BoxIntegral.Prepartition.iUnion_compl`：iUnion_compl (π : Prepartition I)
 : π.compl.iUnion = ↑I \ π.iUnion
· 使用定理 `BoxIntegral.Prepartition.compl_congr`：compl_congr {π₁ π₂ : Prepartition 
I} (h : π₁.iUnion = π₂.iUnion) : π₁.compl = π₂.compl
-/
theorem exists_memBaseSet_le_iUnion_eq (l : IntegrationParams) (π₀ : Prepartition I)
    (hc₁ : π₀.distortion ≤ c) (hc₂ : π₀.compl.distortion ≤ c) (r : (ι → ℝ) → Ioi (0 : ℝ)) :
    ∃ π, l.MemBaseSet I c r π ∧ π.toPrepartition ≤ π₀ ∧ π.iUnion = π₀.iUnion := by
  rcases π₀.exists_tagged_le_isHenstock_isSubordinate_iUnion_eq r with ⟨π, hle, hH, hr, hd, hU⟩
  refine ⟨π, ⟨hr, fun _ => hH, fun _ => hd.trans_le hc₁, fun _ => ⟨π₀.compl, ?_, hc₂⟩⟩, ⟨hle, hU⟩⟩
  exact Prepartition.compl_congr hU ▸ π.toPrepartition.iUnion_compl
/-
**BoxIntegral.IntegrationParams.exists_memBaseSet_isPartition** 是 Mathlib 中的一个定理
，位于命名空间 `BoxIntegral.IntegrationParams`。
形式化陈述：exists_memBaseSet_isPartition (l : IntegrationParams) (I : Box ι) (hc : I.
distortion <= c) (r : (ι -> Real) -> Ioi (0 : Real)) : exists π, l.MemBaseSet I 
c r π ∧ π.IsPartition
参数：l : IntegrationParams；I : Box ι；hc : I.distortion <= c；r : (ι -> Real) -> Ioi
 (0 : Real)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `BoxIntegral.Prepartition.compl_top`：compl_top : (⊤ : Prepartition I).com
pl = ⊥
· 使用定理 `BoxIntegral.Prepartition.distortion_bot`：distortion_bot (I : Box ι) : di
stortion (⊥ : Prepartition I) = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `BoxIntegral.Prepartition.iUnion_top`：iUnion_top : (⊤ : Prepartition I).i
Union = I
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `BoxIntegral.IntegrationParams.exists_memBaseSet_le_iUnion_eq`：exists_mem
BaseSet_le_iUnion_eq (l : IntegrationParams) (π₀ : Prepartition I) (hc₁ : π₀.dis
tortion <= c) (hc₂ : π₀.compl.distortion <= c) (r …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `BoxIntegral.Prepartition.distortion_top`：distortion_top (I : Box ι) : di
stortion (⊤ : Prepartition I) = I.distortion
-/
theorem exists_memBaseSet_isPartition (l : IntegrationParams) (I : Box ι) (hc : I.distortion ≤ c)
    (r : (ι → ℝ) → Ioi (0 : ℝ)) : ∃ π, l.MemBaseSet I c r π ∧ π.IsPartition := by
  rw [← Prepartition.distortion_top] at hc
  have hc' : (⊤ : Prepartition I).compl.distortion ≤ c := by simp
  simpa [isPartition_iff_iUnion_eq] using l.exists_memBaseSet_le_iUnion_eq ⊤ hc hc' r
/-
**BoxIntegral.IntegrationParams.toFilterDistortioniUnion_neBot** 是 Mathlib 中的一个定
理，位于命名空间 `BoxIntegral.IntegrationParams`。
形式化陈述：toFilterDistortioniUnion_neBot (l : IntegrationParams) (I : Box ι) (π₀ : P
repartition I) (hc₁ : π₀.distortion <= c) (hc₂ : π₀.compl.distortion <= c) : (l.
toFilterDistortioniUnion I c π₀).NeBot
参数：l : IntegrationParams；I : Box ι；π₀ : Prepartition I；hc₁ : π₀.distortion <= c；
hc₂ : π₀.compl.distortion <= c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.neBot_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α
} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → (l.NeBot ↔ ∀ {i : ι}, p i →
 (s i).Nonempty…
· 使用定理 `Filter.HasBasis.inf_principal`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filt
er α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ (s' : Set α), (l ⊓ Fi
lter.principal s').…
· 使用定理 `BoxIntegral.IntegrationParams.hasBasis_toFilterDistortion`：hasBasis_toFi
lterDistortion (l : IntegrationParams) (I : Box ι) (c : Real>=0) : (l.toFilterDi
stortion I c).HasBasis l.RCond fun r => { π | l…
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `BoxIntegral.IntegrationParams.exists_memBaseSet_le_iUnion_eq`：exists_mem
BaseSet_le_iUnion_eq (l : IntegrationParams) (π₀ : Prepartition I) (hc₁ : π₀.dis
tortion <= c) (hc₂ : π₀.compl.distortion <= c) (r …
-/
theorem toFilterDistortioniUnion_neBot (l : IntegrationParams) (I : Box ι) (π₀ : Prepartition I)
    (hc₁ : π₀.distortion ≤ c) (hc₂ : π₀.compl.distortion ≤ c) :
    (l.toFilterDistortioniUnion I c π₀).NeBot :=
  ((l.hasBasis_toFilterDistortion I _).inf_principal _).neBot_iff.2
    fun {r} _ => (l.exists_memBaseSet_le_iUnion_eq π₀ hc₁ hc₂ r).imp fun _ hπ => ⟨hπ.1, hπ.2.2⟩
/-
**BoxIntegral.IntegrationParams.toFilterDistortioniUnion_neBot'** 是 Mathlib 中的一个
实例，位于命名空间 `BoxIntegral.IntegrationParams`。
形式化陈述：toFilterDistortioniUnion_neBot' (l : IntegrationParams) (I : Box ι) (π₀ : 
Prepartition I) : (l.toFilterDistortioniUnion I (max π₀.distortion π₀.compl.dist
ortion) π₀).NeBot
参数：l : IntegrationParams；I : Box ι；π₀ : Prepartition I。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `BoxIntegral.IntegrationParams.toFilterDistortioniUnion_neBot`：toFilterDi
stortioniUnion_neBot (l : IntegrationParams) (I : Box ι) (π₀ : Prepartition I) (
hc₁ : π₀.distortion <= c) (hc₂ : π₀.compl.distorti…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
-/
instance toFilterDistortioniUnion_neBot' (l : IntegrationParams) (I : Box ι) (π₀ : Prepartition I) :
    (l.toFilterDistortioniUnion I (max π₀.distortion π₀.compl.distortion) π₀).NeBot :=
  l.toFilterDistortioniUnion_neBot I π₀ (le_max_left _ _) (le_max_right _ _)
/-
**BoxIntegral.IntegrationParams.toFilterDistortion_neBot** 是 Mathlib 中的一个实例，位于命名
空间 `BoxIntegral.IntegrationParams`。
形式化陈述：toFilterDistortion_neBot (l : IntegrationParams) (I : Box ι) : (l.toFilter
Distortion I I.distortion).NeBot
参数：l : IntegrationParams；I : Box ι。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `BoxIntegral.Prepartition.distortion_top`：distortion_top (I : Box ι) : di
stortion (⊤ : Prepartition I) = I.distortion
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `BoxIntegral.Prepartition.compl_top`：compl_top : (⊤ : Prepartition I).com
pl = ⊥
· 使用定理 `BoxIntegral.Prepartition.distortion_bot`：distortion_bot (I : Box ι) : di
stortion (⊥ : Prepartition I) = 0
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Filter.NeBot.mono`：∀ {α : Type u} {f g : Filter α}, f.NeBot → f ≤ g → g.
NeBot
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
instance toFilterDistortion_neBot (l : IntegrationParams) (I : Box ι) :
    (l.toFilterDistortion I I.distortion).NeBot := by
  simpa using (l.toFilterDistortioniUnion_neBot' I ⊤).mono inf_le_left
/-
**BoxIntegral.IntegrationParams.toFilter_neBot** 是 Mathlib 中的一个实例，位于命名空间 `BoxInt
egral.IntegrationParams`。
形式化陈述：toFilter_neBot (l : IntegrationParams) (I : Box ι) : (l.toFilter I).NeBot
参数：l : IntegrationParams；I : Box ι。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.NeBot.mono`：∀ {α : Type u} {f g : Filter α}, f.NeBot → f ≤ g → g.
NeBot
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
-/
instance toFilter_neBot (l : IntegrationParams) (I : Box ι) : (l.toFilter I).NeBot :=
  (l.toFilterDistortion_neBot I).mono <| le_iSup _ _
/-
**BoxIntegral.IntegrationParams.toFilteriUnion_neBot** 是 Mathlib 中的一个实例，位于命名空间 `
BoxIntegral.IntegrationParams`。
形式化陈述：toFilteriUnion_neBot (l : IntegrationParams) (I : Box ι) (π₀ : Prepartitio
n I) : (l.toFilteriUnion I π₀).NeBot
参数：l : IntegrationParams；I : Box ι；π₀ : Prepartition I。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.NeBot.mono`：∀ {α : Type u} {f g : Filter α}, f.NeBot → f ≤ g → g.
NeBot
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
-/
instance toFilteriUnion_neBot (l : IntegrationParams) (I : Box ι) (π₀ : Prepartition I) :
    (l.toFilteriUnion I π₀).NeBot :=
  (l.toFilterDistortioniUnion_neBot' I π₀).mono <|
    le_iSup (fun c => l.toFilterDistortioniUnion I c π₀) _
/-
**BoxIntegral.IntegrationParams.eventually_isPartition** 是 Mathlib 中的一个定理，位于命名空间
 `BoxIntegral.IntegrationParams`。
形式化陈述：eventually_isPartition (l : IntegrationParams) (I : Box ι) : forallᶠ π in 
l.toFilteriUnion I ⊤, TaggedPrepartition.IsPartition π
参数：l : IntegrationParams；I : Box ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_iSup`：eventually_iSup {p : α -> Prop} {fs : ι -> Filte
r α} : (forallᶠ x in ⨆ b, fs b, p x) ↔ forall b, forallᶠ x in fs b, p x
· 使用定理 `Filter.eventually_inf_principal`：eventually_inf_principal {f : Filter α}
 {p : α -> Prop} {s : Set α} : (forallᶠ x in f ⊓ 𝓟 s, p x) ↔ forallᶠ x in f, x i
n s -> p x
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `BoxIntegral.TaggedPrepartition.isPartition_iff_iUnion_eq`：isPartition_if
f_iUnion_eq : IsPartition π ↔ π.iUnion = I
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `BoxIntegral.Prepartition.iUnion_top`：iUnion_top : (⊤ : Prepartition I).i
Union = I
-/
theorem eventually_isPartition (l : IntegrationParams) (I : Box ι) :
    ∀ᶠ π in l.toFilteriUnion I ⊤, TaggedPrepartition.IsPartition π :=
  eventually_iSup.2 fun _ =>
    eventually_inf_principal.2 <|
      Eventually.of_forall fun π h =>
        π.isPartition_iff_iUnion_eq.2 (h.trans Prepartition.iUnion_top)

end IntegrationParams

end BoxIntegral

