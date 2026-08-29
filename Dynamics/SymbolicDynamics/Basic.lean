/-
Copyright (c) 2025 Silvère Gangloff. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Silvère Gangloff
-/
module

public import Mathlib.Topology.Separation.Basic

/-!
# Symbolic dynamics on cancellative monoids

This file develops a minimal API for symbolic dynamics over a
**left-cancellative monoid** `G`—formally, a structure carrying `[Monoid G]`
and `[IsLeftCancelMul G]` (which becomes `[AddMonoid G]` and
`[IsLeftCancelAdd G]` in the additive form). Throughout the documentation we use the
**additive** notations, which are the most common in symbolic dynamics, although
all the notions introduced are defined in the multiplicative notations and adapted
to the additive notation.

Given a finite alphabet `A`, the ambient configuration space is the set of
functions `G → A`, endowed with the product topology. We define the
left-translation action, cylinders, finite patterns, their occurrences,
forbidden sets, and subshifts (closed, shift-invariant subsets). Basic
topological facts (e.g. cylinders are clopen, occurrence sets are clopen,
forbidden sets are closed) are proved under discreteness assumptions on
the alphabet.

The development is generic for left-cancellative monoids. This covers both
groups (the standard setting of symbolic dynamics) and more general monoids
where cancellation holds but inverses may not exist. Geometry specific to
`ℤ^d` (boxes/cubes and the box-based entropy) is deferred to a separate
specialization.

## Why cancellativity?

Some constructions, such as translating a finite pattern to occur at a point `v`,
require solving equations of the form `w + v = h`. For this to have a unique
solution `w` given `h` and `v`, we assume **left-cancellation**:
if `v + a = v + b` then `a = b`. This allows us to define
`Pattern.shift` (which shifts a pattern) without using inverses,
so that the theory works not only for groups but also for cancellative monoids.

## Main definitions

* `shift g x` — left translation: in additive notation `(shift v x) u = x (v + u)` (using the
**left** action of `G` on configurations).
* `cylinder U x` — configurations agreeing with `x` on a finite set `U ⊆ G`.
* `Pattern A G` — a configuration which takes
default value outside of a finite support, together with this support.
* `Pattern.occursInAt p x g` — occurrence of `p` in `x` at translate `g`.
* `forbidden F` — configurations avoiding every pattern in `F`.
* `Subshift A G` — closed, shift-invariant subsets of the full shift.
* `MulSubshift.ofForbidden F` — the subshift defined by forbidding a family of patterns.
* `subshift_of_finite_type F` — a subshift of finite type defined by a finite set of
forbidden patterns.
* `languageOn X U` — the set of patterns of shape `U` obtained by restricting some `x ∈ X`.

## Design choice: ambient vs. inner (subshift-relative) viewpoint

All core notions (shift, cylinder, occurrence, language, …) are defined **in the
ambient full shift** `G → A`. A subshift is then a closed, invariant subset,
bundled as `Subshift A G`. Working inside a subshift is done by restriction.

**Motivation.**

If cylinders and shifts were defined only *inside* a subshift, local ergonomics
would improve but global operations would become awkward. For instance, to prove
that for finite shape `U`:

`languageOn (X ∪ Y) U = languageOn X U ∪ languageOn Y U,`

one must eventually move both sides to the ambient pattern type. Similar issues
arise for intersections, factors, and products. By contrast, with ambient
definitions these set-theoretic identities are tautological.
Thus the file develops the theory ambiently, and subshifts reuse it by restriction.

**Working inside a subshift.**

For `Y : Subshift A G`, cylinders and occurrence sets *inside `Y`* are simply
preimages of the ambient ones under the inclusion `Y → (G → A)`. For example:

`{ y : Y | ∀ i ∈ U, (y : G → A) i = (x : G → A) i } = (Subtype.val) ⁻¹' (cylinder U (x : G → A)).`

Shift invariance guarantees that the ambient shift restricts to `Y`.

**Ergonomics.**

Thin wrappers (e.g. `Subshift.shift`, `Subshift.cylinder`, `Subshift.languageOn`)
may be added for convenience. They introduce no new theory and unfold to the
ambient definitions.

## Namespacing policy

All ambient definitions live under the namespace `SymbolicDynamics.FullShift`.
If inner, subshift-relative wrappers are provided, they will be placed in the
subnamespace `SymbolicDynamics.Subshift`. This separation avoids name clashes
between the two viewpoints, since both may naturally want to reuse names like
`cylinder`, `shift`, `occursAt`, or `languageOn`.

## Implementation notes

* Openness results for cylinders and occurrence sets use
  `[DiscreteTopology A]`. Closeness results use `[T1Space A]`.
-/

@[expose] public section

noncomputable section
open Set Topology

namespace SymbolicDynamics

namespace FullShift

/-! ## Full shift and shift action -/

section ShiftDefinition

variable {A G : Type*} [Monoid G]

/-- The **left-translation shift** on configurations.

We call *configuration* an element of `G → A`.

Given a configuration `x : G → A` and an element `g : G` of the monoid, the shifted configuration
`mulShift g x` is defined by `(mulShift g x) h = x (g * h)`.

Intuitively, this moves the whole configuration "in the direction of `g`": the value
at position `h` in the shifted configuration is the value that was at position
`g * h` in the original one.

For example, if `G = ℤ` (with addition) and `A = {0, 1}`, then
`mulShift 1 x` is the sequence obtained from `x` by shifting every symbol one
step to the left. -/
@[to_additive /-- The **left-translation shift** on configurations, in additive notation.

We call *configuration* an element of `G → A`.

Given a configuration `x : G → A` and an element `g : G` of the additive monoid,
the shifted configuration `shift g x` is defined by `(shift g x) h = x (g + h)`.

Intuitively, this moves the whole configuration "in the direction of `g`": the value
at position `h` in the shifted configuration is the value that was at position
`g + h` in the original one.

For example, if `G = ℤ` and `A = {0, 1}`, then
`shift 1 x` is the sequence obtained from `x` by shifting every symbol one
step to the left. -/]
/--
Definition of `mulShift` / `mulShift` 的定义

English:
definition mulShift
  signature: (g : G) (x : G -> A)
  body: fun h => x (g * h)

中文:
定义 mulShift
  签名: (g : G) (x : G -> A)
  定义体: fun h => x (g * h)
-/
def mulShift (g : G) (x : G -> A) : G -> A :=
  fun h => x (g * h)

/--
lemma `mulShift_apply` / 引理 `mulShift_apply`

English:
lemma mulShift_apply
  given: (g : G) (x : G -> A) (h : G)
  proof: rfl

中文:
引理 mulShift_apply
  条件: (g : G) (x : G -> A) (h : G)
  证明: rfl
-/
@[to_additive (attr := simp)] lemma mulShift_apply (g : G) (x : G -> A) (h : G) :
    mulShift g x h = x (g * h) := rfl

/--
lemma `mulShift_one` / 引理 `mulShift_one`

English:
lemma mulShift_one
  given: (x : G -> A)
  statement: mulShift (1 : G) x = x
  proof: by
  ext h; simp [mulShift]

中文:
引理 mulShift_one
  条件: (x : G -> A)
  结论: mulShift (1 : G) x = x
  证明: by
  ext h; simp [mulShift]
-/
@[to_additive (attr := simp)] lemma mulShift_one (x : G -> A) : mulShift (1 : G) x = x := by
  ext h; simp [mulShift]

/-- Composition of left-translation shifts corresponds to multiplication in the monoid `G`. -/
@[to_additive
/-- Composition of left-translation shifts corresponds to addition in the additive monoid `G`. -/]
/--
lemma `mulShift_mul` / 引理 `mulShift_mul`

English:
lemma mulShift_mul
  given: (g₁ g₂ : G) (x : G -> A)
  proof: by
  ext h; simp [mulShift, mul_assoc]

中文:
引理 mulShift_mul
  条件: (g₁ g₂ : G) (x : G -> A)
  证明: by
  ext h; simp [mulShift, mul_assoc]

Depends on / 依赖: mulShift, mul_assoc
-/
lemma mulShift_mul (g₁ g₂ : G) (x : G -> A) :
    mulShift (g₁ * g₂) x = mulShift g₂ (mulShift g₁ x) := by
  ext h; simp [mulShift, mul_assoc]

variable [TopologicalSpace A]

/-- The left-translation shift is continuous. -/
@[to_additive (attr := fun_prop)
/-- The left-translation shift is continuous. -/]
/--
lemma `continuous_mulShift` / 引理 `continuous_mulShift`

English:
lemma continuous_mulShift
  given: (g : G)
  proof: by
  -- coordinate projections are continuous; composition preserves continuity
  unfold mulShift
  fun_prop

中文:
引理 continuous_mulShift
  条件: (g : G)
  证明: by
  -- coordinate projections are continuous; composition preserves continuity
  unfold mulShift
  fun_prop
-/
lemma continuous_mulShift (g : G) :
    Continuous (mulShift (A := A) g) := by
  -- coordinate projections are continuous; composition preserves continuity
  unfold mulShift
  fun_prop

end ShiftDefinition

/-! ## Cylinders -/

section Cylinders

variable {A G : Type*}

/--
Definition of `cylinder` / `cylinder` 的定义

English:
definition cylinder
  signature: (U : Finset G) (x : G -> A)
  body: { y | forall i in U, y i = x i }

中文:
定义 cylinder
  签名: (U : 有限集 G) (x : G -> A)
  定义体: { y | forall i in U, y i = x i }
-/
def cylinder (U : Finset G) (x : G -> A) : Set (G -> A) :=
  { y | forall i in U, y i = x i }

/--
lemma `cylinder_eq_set_pi` / 引理 `cylinder_eq_set_pi`

English:
lemma cylinder_eq_set_pi
  given: (U : Finset G) (x : G -> A)
  proof: by
  ext y; simp [cylinder, Set.pi]

中文:
引理 cylinder_eq_set_pi
  条件: (U : 有限集 G) (x : G -> A)
  证明: by
  ext y; simp [cylinder, Set.pi]

Depends on / 依赖: Set.pi, cylinder
-/
lemma cylinder_eq_set_pi (U : Finset G) (x : G -> A) :
    cylinder U x = Set.pi (↑U : Set G) (fun i => ({x i} : Set A)) := by
  ext y; simp [cylinder, Set.pi]

/--
lemma `mem_cylinder` / 引理 `mem_cylinder`

English:
lemma mem_cylinder
  given: {U : Finset G} {x y : G -> A}
  proof: Iff.rfl

中文:
引理 mem_cylinder
  条件: {U : 有限集 G} {x y : G -> A}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_cylinder {U : Finset G} {x y : G -> A} :
    y in cylinder U x ↔ forall i in U, y i = x i := Iff.rfl

variable [TopologicalSpace A]

/--
lemma `isOpen_cylinder` / 引理 `isOpen_cylinder`

English:
lemma isOpen_cylinder
  given: [DiscreteTopology A] (U : Finset G) (x : G -> A)
  proof: by
  simpa [cylinder_eq_set_pi U x] using isOpen_set_pi (U.finite_toSet) (by simp)

中文:
引理 isOpen_cylinder
  条件: [离散拓扑 A] (U : 有限集 G) (x : G -> A)
  证明: by
  simpa [cylinder_eq_set_pi U x] using isOpen_set_pi (U.finite_toSet) (by simp)

Depends on / 依赖: U.finite_toSet, cylinder_eq_set_pi, finite_toSet, isOpen_set_pi
-/
lemma isOpen_cylinder [DiscreteTopology A] (U : Finset G) (x : G -> A) :
    IsOpen (cylinder U x) := by
  simpa [cylinder_eq_set_pi U x] using isOpen_set_pi (U.finite_toSet) (by simp)

/--
lemma `isClosed_cylinder` / 引理 `isClosed_cylinder`

English:
lemma isClosed_cylinder
  given: [T1Space A] (U : Finset G) (x : G -> A)
  proof: by
  simpa [cylinder_eq_set_pi U x] using isClosed_set_pi (by simp)

中文:
引理 isClosed_cylinder
  条件: [T1空间 A] (U : 有限集 G) (x : G -> A)
  证明: by
  simpa [cylinder_eq_set_pi U x] using isClosed_set_pi (by simp)

Depends on / 依赖: cylinder_eq_set_pi, isClosed_set_pi
-/
lemma isClosed_cylinder [T1Space A] (U : Finset G) (x : G -> A) :
    IsClosed (cylinder U x) := by
  simpa [cylinder_eq_set_pi U x] using isClosed_set_pi (by simp)

end Cylinders

/-! ## Patterns and occurrences -/

/--
Definition of `Subshift` / `Subshift` 的定义

English:
structure Subshift
  parameters: (A : Type*) [TopologicalSpace A] (G : Type*) [AddMonoid G]
  axioms and operations (3):
    - carrier : Set (G -> A)
    - isClosed : IsClosed carrier
    - mapsTo : forall g : G, MapsTo (shift g) carrier carrier

中文:
结构 子平移
  参数: (A : 类型) [拓扑空间 A] (G : 类型) [加法幺半群 G]
  公理与运算 (3 个):
    - carrier : 集合 (G -> A)
    - isClosed : 是闭集 carrier
    - mapsTo : 对任意 g : G, 映射到 (shift g) carrier carrier
-/
structure Subshift (A : Type*) [TopologicalSpace A] (G : Type*) [AddMonoid G] where
  /-- The underlying set of configurations (additive monoid version). -/
  carrier : Set (G -> A)
  /-- Closedness of `carrier`. -/
  isClosed : IsClosed carrier
  /-- Shift invariance of `carrier` for the additive shift `shift`. -/
  mapsTo : forall g : G, MapsTo (shift g) carrier carrier

section MulSubshiftDef
variable (A : Type*) [TopologicalSpace A]
variable (G : Type*) [Monoid G]

/-- A *subshift* on an alphabet `A` over a multiplicative monoid `G` is a closed,
shift-invariant subset of `G → A`, where the shift is given by left-multiplication.
Formally, it is composed of:
* `carrier`: the underlying set of allowed configurations.
* `isClosed`: the set is topologically closed in `A^G`.
* `mapsTo`: the set is invariant under all left-translation shifts
  `(mulShift g)`. -/
@[to_additive existing]
/--
Definition of `MulSubshift` / `MulSubshift` 的定义

English:
structure MulSubshift
  parameters: where
  axioms and operations (3):
    - carrier : Set (G -> A)
    - isClosed : IsClosed carrier
    - mapsTo : forall g : G, MapsTo (mulShift g) carrier carrier

中文:
结构 MulSubshift
  参数: where
  公理与运算 (3 个):
    - carrier : 集合 (G -> A)
    - isClosed : 是闭集 carrier
    - mapsTo : 对任意 g : G, 映射到 (mulShift g) carrier carrier
-/
structure MulSubshift where
  /-- The underlying set of configurations. -/
  carrier : Set (G -> A)
  /-- Closedness of `carrier`. -/
  isClosed : IsClosed carrier
  /-- Shift invariance of `carrier`. -/
  mapsTo : forall g : G, MapsTo (mulShift g) carrier carrier

end MulSubshiftDef

/-- Example: the **full shift** on alphabet `A` over the multiplicative monoid `G`.
It is the subshift whose underlying set is the set of all configurations
`G → A`. -/
@[to_additive fullShift
/-- Example: the **full shift** on alphabet `A` over the additive monoid `G`.

It is the subshift whose underlying set is the set of all configurations
`G → A`.
-/]
/--
Definition of `mulFullShift` / `mulFullShift` 的定义

English:
definition mulFullShift
  signature: (A G) [TopologicalSpace A] [Monoid G]
  body: Set.univ
  isClosed := isClosed_univ
  mapsTo := fun _ _ _ => trivial

中文:
定义 mulFullShift
  签名: (A G) [拓扑空间 A] [幺半群 G]
  定义体: Set.univ
  isClosed := isClosed_univ
  mapsTo := fun _ _ _ => trivial

Depends on / 依赖: Set.univ
-/
def mulFullShift (A G) [TopologicalSpace A] [Monoid G] : MulSubshift A G where
  carrier := Set.univ
  isClosed := isClosed_univ
  mapsTo := fun _ _ _ => trivial

/--
Definition of `Pattern` / `Pattern` 的定义

English:
structure Pattern
  parameters: (A : Type*) (G : Type*) [Inhabited A]
  axioms and operations (3):
    - config : G -> A
    - support : Finset G
    - condition : forall g ∉ support, config g = default

中文:
结构 Pattern
  参数: (A : 类型) (G : 类型) [可居 A]
  公理与运算 (3 个):
    - config : G -> A
    - support : 有限集 G
    - condition : 对任意 g ∉ support, config g = default
-/
structure Pattern (A : Type*) (G : Type*) [Inhabited A] where
  /-- The full configuration in the full shift `A^G`. -/
  config : G -> A
  /-- Finite support of the pattern. -/
  support : Finset G
  /-- Outside the support, `config` takes the default value of `A`. -/
  condition : forall g ∉ support, config g = default

section Forbidden

variable {A G : Type*} [Inhabited A] [Monoid G]

/-- `p.mulOccursInAt x g` means that the finite pattern
`p` appears in the configuration `x`
at position `g`.

Formally: for every position `h` in the support of `p`, the value of the configuration
at `g * h` coincides with the value of `p.config` at `h`.

Intuitively, if you shift the configuration `x` by `g` (using `mulShift g`),
then on the support of `p` you exactly recover the pattern `p`. This is the basic
notion of "pattern occurrence" used to define subshifts via forbidden patterns. -/
@[to_additive Pattern.occursInAt
/-- `p.occursInAt x g` means that the finite pattern `p` appears in the configuration `x`
at position `g`.

Formally: for every position `h` in the support of `p`, the value of the configuration
at `g + h` coincides with the value of `p.config` at `h`.

Intuitively, if you shift the configuration `x` by `g` (using `shift g`),
then on the support of `p` you exactly recover the pattern `p`. This is the basic
notion of "pattern occurrence" used to define subshifts via forbidden patterns. -/]
/--
Definition of `Pattern.mulOccursInAt` / `Pattern.mulOccursInAt` 的定义

English:
definition Pattern.mulOccursInAt
  signature: (p : Pattern A G) (x : G -> A) (g : G)
  body: forall (h) (_ : h in p.support), x (g * h) = p.config h

中文:
定义 Pattern.mulOccursInAt
  签名: (p : Pattern A G) (x : G -> A) (g : G)
  定义体: forall (h) (_ : h in p.support), x (g * h) = p.config h

Depends on / 依赖: config, p.config, p.support, support
-/
def Pattern.mulOccursInAt (p : Pattern A G) (x : G -> A) (g : G) : Prop :=
  forall (h) (_ : h in p.support), x (g * h) = p.config h

/-- `mulForbidden F` is the set of configurations that avoid every pattern in `F`.

Formally: `x ∈ mulForbidden F` if and only if for every pattern `p ∈ F` and every
monoid element `g : G`, the pattern `p` does not occur in `x` at position `g`.

Intuitively, `mulForbidden F` is the shift space defined by declaring the finite set
(or family) of patterns `F` to be *forbidden*. A configuration belongs to the subshift if and only
it avoids all the forbidden patterns. -/
@[to_additive forbidden
/-- `forbidden F` is the set of configurations that avoid every pattern in `F`.

Formally: `x ∈ forbidden F` if and only if for every pattern `p ∈ F` and every
monoid element `g : G`, the pattern `p` does not occur in `x` at position `g`.

Intuitively, `forbidden F` is the shift space defined by declaring the finite set
(or family) of patterns `F` to be *forbidden*. A configuration belongs to the subshift if and only
it avoids all the forbidden patterns. -/]
/--
Definition of `mulForbidden` / `mulForbidden` 的定义

English:
definition mulForbidden
  signature: (F : Set (Pattern A G))
  body: { x | forall p in F, forall g : G, ¬ p.mulOccursInAt x g }

中文:
定义 mulForbidden
  签名: (F : 集合 (Pattern A G))
  定义体: { x | forall p in F, forall g : G, ¬ p.mulOccursInAt x g }

Depends on / 依赖: mulOccursInAt, p.mulOccursInAt
-/
def mulForbidden (F : Set (Pattern A G)) : Set (G -> A) :=
  { x | forall p in F, forall g : G, ¬ p.mulOccursInAt x g }

end Forbidden

section OccursInAt

variable {A : Type*} [Inhabited A]
variable {G : Type*} [Monoid G] [IsLeftCancelMul G]

/-- Translate a finite pattern `p` so that it occurs at the translate `v`, before completing into
a configuration.

On input `h : G`, we proceed as follows:
* if `h` lies in the left-translate of the support, i.e. `h ∈ p.support.image (v * ·)`,
  choose (noncomputably) `w ∈ p.support` with `v * w = h` and return `p.config w`;
* otherwise return `default`.

This definition does not assume left-cancellation; it only *chooses* a preimage.
Uniqueness (and the usual equations such as `Pattern.mulShift p v (v * w) = p.config w`)
require a left-cancellation hypothesis and are proved in separate lemmas.
-/
@[to_additive
/-- Translate a finite pattern `p` so that it occurs at the translate `v`, before completing into
a configuration.

On input `h : G`, we proceed as follows:
* if `h` lies in the left-translate of the support, i.e. `h ∈ p.support.image (v + ·)`,
  choose (noncomputably) `w ∈ p.support` with `v + w = h` and return `p.config w`;
* otherwise return `default`.

This definition does not assume left-cancellation; it only *chooses* a preimage.
Uniqueness (and the usual equations such as `Pattern.shift p v (v + w) = p.config w`)
require a left-cancellation hypothesis and are proved in separate lemmas.
-/]
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def Pattern.mulShift (p : Pattern A G) (v : G)
  body: by
  intro h
  if hmem : h in p.support.image (v * ·) then
    -- package existence of a preimage under (v * ·)
    let ex : exists w, w in p.support ∧ v * w = h := by
      simpa [Finset.mem_image] using hmem
    exact p.config (Classical.choose ex)
  else
    exact default

中文:
定义 noncomputable
  签名: def Pattern.mulShift (p : Pattern A G) (v : G)
  定义体: by
  intro h
  if hmem : h in p.support.image (v * ·) then
    -- package existence of a preimage under (v * ·)
    let ex : exists w, w in p.support ∧ v * w = h := by
      simpa [Finset.mem_image] using hmem
    exact p.config (Classical.choose ex)
  else
    exact default
-/
protected noncomputable def Pattern.mulShift (p : Pattern A G) (v : G) : G -> A := by
  intro h
  if hmem : h in p.support.image (v * ·) then
    -- package existence of a preimage under (v * ·)
    let ex : exists w, w in p.support ∧ v * w = h := by
      simpa [Finset.mem_image] using hmem
    exact p.config (Classical.choose ex)
  else
    exact default

namespace Pattern
/--
Definition of `fromConfig` / `fromConfig` 的定义

English:
definition fromConfig
  signature: (x : G -> A) (U : Finset G)
  body: by
  classical
  exact { config := fun g => if g in U then x g else default,
          support := U,
          condition := fun g hg => if_neg hg }

中文:
定义 fromConfig
  签名: (x : G -> A) (U : 有限集 G)
  定义体: by
  classical
  exact { config := fun g => if g in U then x g else default,
          support := U,
          condition := fun g hg => if_neg hg }

Depends on / 依赖: classical, condition, config, if_neg, support
-/
noncomputable def fromConfig (x : G -> A) (U : Finset G) : Pattern A G := by
  classical
  exact { config := fun g => if g in U then x g else default,
          support := U,
          condition := fun g hg => if_neg hg }

/-- On the translated support, `p.mulShift v` agrees with `p.config` at the preimage.

More precisely, if `w ∈ p.support`, then at the translated site `v * w`,
the configuration `p.mulShift v` takes the value `p.config w`.

This uses `[IsLeftCancelMul G]` to identify the unique preimage of `v * w`
under left-multiplication by `v`. -/
@[to_additive
  /-- On the translated support, `p.shift v` agrees with `p.config` at the preimage.

  More precisely, if `w ∈ p.support`, then at the translated site `v + w`,
  the configuration `p.shift v` takes the value `p.config w`.

  This uses `[IsLeftCancelAdd G]` to identify the unique preimage of `v + w`
  under left-translation by `v`. -/]
/--
lemma `mulShift_apply_mul_left_of_mem` / 引理 `mulShift_apply_mul_left_of_mem`

English:
lemma mulShift_apply_mul_left_of_mem
  proof: by
  classical
  -- (v * w) is in the translated support
  have hmem : (v * w) in p.support.image (v * ·) :=
    Finset.mem_image.mpr ⟨w, hw, rfl⟩
  -- existential used in the branch
  have ex : exists w', w' in p.support ∧ v * w' = v * w := by
    simpa [Finset.mem_image] using hmem
  -- open the `

中文:
引理 mulShift_apply_mul_left_of_mem
  证明: by
  classical
  -- (v * w) is in the translated support
  have hmem : (v * w) in p.support.image (v * ·) :=
    Finset.mem_image.mpr ⟨w, hw, rfl⟩
  -- existential used in the branch
  have ex : exists w', w' in p.support ∧ v * w' = v * w := by
    simpa [Finset.mem_image] using hmem
  -- open the `

Depends on / 依赖: classical
-/
lemma mulShift_apply_mul_left_of_mem
    (p : Pattern A G) (v w : G) (hw : w in p.support) :
    p.mulShift v (v * w) = p.config w := by
  classical
  -- (v * w) is in the translated support
  have hmem : (v * w) in p.support.image (v * ·) :=
    Finset.mem_image.mpr ⟨w, hw, rfl⟩
  -- existential used in the branch
  have ex : exists w', w' in p.support ∧ v * w' = v * w := by
    simpa [Finset.mem_image] using hmem
  -- open the `if` branch as returned by the definition
  have h1 : p.mulShift v (v * w) = p.config (Classical.choose ex) := by
    simp [Pattern.mulShift, hmem]
  -- the chosen witness equals w by left-cancellation
  have hwv' : v * Classical.choose ex = v * w := (Classical.choose_spec ex).2
  have h_eq : Classical.choose ex = w := mul_left_cancel hwv'
  rw [h1]; rw [h_eq]

/-- Shifting a configuration commutes with occurrences of a pattern.

Formally: a pattern `p` occurs in the shifted configuration `mulShift h x` at
position `g` if and only if it occurs in the original configuration `x` at
position `g * h`. -/
@[to_additive occursInAt_shift
/-- Shifting a configuration commutes with occurrences of a pattern.

Formally: a pattern `p` occurs in the shifted configuration `shift h x` at
position `g` if and only if it occurs in the original configuration `x` at
position `g + h`. -/]
/--
lemma `mulOccursInAt_mulShift` / 引理 `mulOccursInAt_mulShift`

English:
lemma mulOccursInAt_mulShift
  statement: {A G : Type*} [Inhabited A] [Monoid G]
  proof: by
  simp only [Pattern.mulOccursInAt, mulShift_apply, mul_assoc]

中文:
引理 mulOccursInAt_mulShift
  结论: {A G : 类型} [可居 A] [幺半群 G]
  证明: by
  simp only [Pattern.mulOccursInAt, mulShift_apply, mul_assoc]

Depends on / 依赖: Pattern, Pattern.mulOccursInAt, mulOccursInAt, mulShift_apply, mul_assoc
-/
lemma mulOccursInAt_mulShift {A G : Type*} [Inhabited A] [Monoid G]
    (p : Pattern A G) (x : G -> A) (g h : G) :
    p.mulOccursInAt (mulShift g x) h ↔ p.mulOccursInAt x (g * h) := by
  simp only [Pattern.mulOccursInAt, mulShift_apply, mul_assoc]

/-- Configurations that avoid a family `F` of patterns are stable under the shift.

Formally: if `x` avoids every `p ∈ F` at every position, then for any `h : G`,
the shifted configuration `mulShift h x` also avoids every `p ∈ F` at every position. -/
@[to_additive mapsTo_shift_forbidden
  /-- Configurations that avoid a family `F` of patterns are stable under the shift.

Formally: if `x` avoids every `p ∈ F` at every position, then for any `h : G`,
the shifted configuration `shift h x` also avoids every `p ∈ F` at every position. -/]
/--
lemma `mapsTo_mulShift_mulForbidden` / 引理 `mapsTo_mulShift_mulForbidden`

English:
lemma mapsTo_mulShift_mulForbidden
  statement: {A G : Type*} [Inhabited A] [Monoid G]
  proof: by
  -- unfold `MapsTo`
  intro x hx p hp g
  specialize hx p hp (h * g)
  contrapose! hx
  simpa [mulOccursInAt_mulShift] using hx

中文:
引理 mapsTo_mulShift_mulForbidden
  结论: {A G : 类型} [可居 A] [幺半群 G]
  证明: by
  -- unfold `MapsTo`
  intro x hx p hp g
  specialize hx p hp (h * g)
  contrapose! hx
  simpa [mulOccursInAt_mulShift] using hx

Depends on / 依赖: mulForbidden
-/
lemma mapsTo_mulShift_mulForbidden {A G : Type*} [Inhabited A] [Monoid G]
    (F : Set (Pattern A G)) (h : G) :
    Set.MapsTo (mulShift h) (mulForbidden (A := A) (G := G) F) (mulForbidden F) := by
  -- unfold `MapsTo`
  intro x hx p hp g
  specialize hx p hp (h * g)
  contrapose! hx
  simpa [mulOccursInAt_mulShift] using hx

end Pattern

open scoped Classical in
/-- We call *occurrence set* for pattern `p` and position `g` the set of configurations
in which a pattern `p` occurs at position `g`.

This proves that it is exactly the cylinder corresponding to the
pattern obtained by translating `p` by `g`.

Equivalently, `p.mulOccursInAt x g` iff on every translated site
`g * w` (with `w ∈ p.support`)
the configuration `x` agrees with the translated pattern `Pattern.mulShift p g`.

(This uses `[IsLeftCancelMul G]` to identify the preimage along left-multiplication by `g`.) -/
@[to_additive occursInAt_eq_cylinder
  /-- We call *occurrence set* for pattern `p` and position `g` the set of configurations
in which a pattern `p` occurs at position `g`.

This proves that it is exactly the cylinder corresponding to the
pattern obtained by translating `p` by `g`.

Equivalently, `p.occursInAt x g` iff on every translated site `g + w` (with `w ∈ p.support`)
the configuration `x` agrees with the translated pattern `Pattern.shift p g`.

(This uses `[IsLeftCancelMul G]` to identify the preimage along left-multiplication by `g`.) -/]
/--
lemma `mulOccursInAt_eq_cylinder` / 引理 `mulOccursInAt_eq_cylinder`

English:
lemma mulOccursInAt_eq_cylinder
  proof: by
  ext x; constructor
  · -- ⇒: from an occurrence, get membership in the cylinder
    intro H u hu
    rcases Finset.mem_image.mp hu with ⟨w, hw, rfl⟩
    -- want: x ( w * g) = Pattern.mulShift p g ( w * g)
    have hx : x (g * w) = p.config w := H w hw
    simpa [Pattern.mulShift_apply_mul_left_

中文:
引理 mulOccursInAt_eq_cylinder
  证明: by
  ext x; constructor
  · -- ⇒: from an occurrence, get membership in the cylinder
    intro H u hu
    rcases Finset.mem_image.mp hu with ⟨w, hw, rfl⟩
    -- want: x ( w * g) = Pattern.mulShift p g ( w * g)
    have hx : x (g * w) = p.config w := H w hw
    simpa [Pattern.mulShift_apply_mul_left_

Depends on / 依赖: Finset, Finset.mem_image.mp, cylinder, mem_image, membership, occurrence
-/
lemma mulOccursInAt_eq_cylinder
    (p : Pattern A G) (g : G) :
    { x | p.mulOccursInAt x g } = cylinder (p.support.image (g * ·)) (p.mulShift g) := by
  ext x; constructor
  · -- ⇒: from an occurrence, get membership in the cylinder
    intro H u hu
    rcases Finset.mem_image.mp hu with ⟨w, hw, rfl⟩
    -- want: x ( w * g) = Pattern.mulShift p g ( w * g)
    have hx : x (g * w) = p.config w := H w hw
    simpa [Pattern.mulShift_apply_mul_left_of_mem (p := p) (v := g) (w := w) hw] using hx
  · -- ⇐: from the cylinder, recover an occurrence
    intro H u hu
    -- H gives equality with the translated pattern on the image
    have hx : x (g * u) = p.mulShift g (g * u) :=
      H (g * u) (Finset.mem_image_of_mem (g * ·) hu)
    -- rewrite the RHS by the “apply_of_mem” lemma
    simpa [Pattern.mulShift_apply_mul_left_of_mem (p := p) (v := g) (w := u) hu] using hx
end OccursInAt

/-! ## Forbidden sets and subshifts -/

section DefSubshiftByForbidden

variable {A : Type*} [TopologicalSpace A] [Inhabited A]
variable {G : Type*} [Monoid G] [IsLeftCancelMul G]

/-- Occurrence sets are open. -/
@[to_additive isOpen_occursInAt /-- Occurrence sets are open. -/]
/--
lemma `isOpen_mulOccursInAt` / 引理 `isOpen_mulOccursInAt`

English:
lemma isOpen_mulOccursInAt
  given: [DiscreteTopology A] (p : Pattern A G) (g : G)
  proof: by
  simpa [mulOccursInAt_eq_cylinder] using isOpen_cylinder _ _

中文:
引理 isOpen_mulOccursInAt
  条件: [离散拓扑 A] (p : Pattern A G) (g : G)
  证明: by
  simpa [mulOccursInAt_eq_cylinder] using isOpen_cylinder _ _

Depends on / 依赖: isOpen_cylinder, mulOccursInAt_eq_cylinder
-/
lemma isOpen_mulOccursInAt [DiscreteTopology A] (p : Pattern A G) (g : G) :
    IsOpen { x | p.mulOccursInAt x g } := by
  simpa [mulOccursInAt_eq_cylinder] using isOpen_cylinder _ _

/-- Avoiding a fixed family of patterns is a closed condition (in the product topology on `G → A`).

Since each occurrence set `{ x | p.mulOccursInAt x v }` is open (when `A` is discrete),
its complement `{ x | ¬ p.mulOccursInAt x v }` is closed; `forbidden F` is the intersection
of these closed sets over `p ∈ F` and `v ∈ G`. -/
@[to_additive isClosed_forbidden /-- Avoiding a fixed family of patterns is a closed
condition (in the product topology on `G → A`).

Since each occurrence set `{ x | p.occursInAt x v }` is open (when `A` is discrete),
its complement `{ x | ¬ p.occursInAt x v }` is closed; `forbidden F` is the intersection
of these closed sets over `p ∈ F` and `v ∈ G`. -/]
/--
lemma `isClosed_mulForbidden` / 引理 `isClosed_mulForbidden`

English:
lemma isClosed_mulForbidden
  given: [DiscreteTopology A] (F : Set (Pattern A G))
  proof: by
  rw [mulForbidden]
  -- Rewrite as an intersection indexed by `p ∈ F` and `v : G`.
  have h_eq : {x | forall p in F, forall v : G, ¬ p.mulOccursInAt x v}
    = ⋂ (p : Pattern A G) (hp : p in F) (v : G), {x | ¬ p.mulOccursInAt x v} := by ext; simp
  rw [h_eq]
  -- Now prove that this big intersec

中文:
引理 isClosed_mulForbidden
  条件: [离散拓扑 A] (F : 集合 (Pattern A G))
  证明: by
  rw [mulForbidden]
  -- Rewrite as an intersection indexed by `p ∈ F` and `v : G`.
  have h_eq : {x | forall p in F, forall v : G, ¬ p.mulOccursInAt x v}
    = ⋂ (p : Pattern A G) (hp : p in F) (v : G), {x | ¬ p.mulOccursInAt x v} := by ext; simp
  rw [h_eq]
  -- Now prove that this big intersec

Depends on / 依赖: mulForbidden
-/
lemma isClosed_mulForbidden [DiscreteTopology A] (F : Set (Pattern A G)) :
    IsClosed (mulForbidden F) := by
  rw [mulForbidden]
  -- Rewrite as an intersection indexed by `p ∈ F` and `v : G`.
  have h_eq : {x | forall p in F, forall v : G, ¬ p.mulOccursInAt x v}
    = ⋂ (p : Pattern A G) (hp : p in F) (v : G), {x | ¬ p.mulOccursInAt x v} := by ext; simp
  rw [h_eq]
  -- Now prove that this big intersection is closed.
  refine isClosed_iInter (fun p => ?_)
  refine isClosed_iInter (fun hp => ?_)
  refine isClosed_iInter (fun v => ?_)
  -- For each `p, hp, v`, the section is the complement of an open occurrence set.
  have : {x | ¬ p.mulOccursInAt x v} = {x | p.mulOccursInAt x v}ᶜ := by ext; simp
  simpa [this, isClosed_compl_iff] using isOpen_mulOccursInAt (A := A) (G := G) p v

/-- Occurrence sets are closed. -/
@[to_additive isClosed_occursInAt /-- Occurrence sets are closed. -/]
/--
lemma `isClosed_mulOccursInAt` / 引理 `isClosed_mulOccursInAt`

English:
lemma isClosed_mulOccursInAt
  given: [T1Space A] (p : Pattern A G) (g : G)
  proof: by
  simpa [mulOccursInAt_eq_cylinder] using isClosed_cylinder _ _

中文:
引理 isClosed_mulOccursInAt
  条件: [T1空间 A] (p : Pattern A G) (g : G)
  证明: by
  simpa [mulOccursInAt_eq_cylinder] using isClosed_cylinder _ _

Depends on / 依赖: isClosed_cylinder, mulOccursInAt_eq_cylinder
-/
lemma isClosed_mulOccursInAt [T1Space A] (p : Pattern A G) (g : G) :
    IsClosed { x | p.mulOccursInAt x g } := by
  simpa [mulOccursInAt_eq_cylinder] using isClosed_cylinder _ _

/-- The subshift defined by a family of forbidden patterns `F`.

This is a standard way to construct subshifts:
`MulSubshift.ofForbidden F` consists of all configurations `x : G → A` in which no pattern
`p ∈ F` occurs at any position.

Formally:
* the carrier is `forbidden F` (configurations avoiding `F`),
* it is closed because each occurrence set is open, and
* it is shift-invariant since avoidance is preserved by shifts. -/
@[to_additive /-- The subshift defined by a family of forbidden patterns `F`.

This is a standard way to construct subshifts:
`Subshift.ofForbidden F` consists of all configurations `x : G → A` in which no pattern
`p ∈ F` occurs at any position.

Formally:
* the carrier is `forbidden F` (configurations avoiding `F`),
* it is closed because each occurrence set is open, and
* it is shift-invariant since avoidance is preserved by shifts. -/]
/--
Definition of `MulSubshift.ofForbidden` / `MulSubshift.ofForbidden` 的定义

English:
definition MulSubshift.ofForbidden
  signature: [DiscreteTopology A] (F : Set (Pattern A G))
  body: mulForbidden F
  isClosed := isClosed_mulForbidden F
  mapsTo := Pattern.mapsTo_mulShift_mulForbidden F

中文:
定义 MulSubshift.ofForbidden
  签名: [离散拓扑 A] (F : 集合 (Pattern A G))
  定义体: mulForbidden F
  isClosed := isClosed_mulForbidden F
  mapsTo := Pattern.mapsTo_mulShift_mulForbidden F

Depends on / 依赖: mulForbidden
-/
def MulSubshift.ofForbidden [DiscreteTopology A] (F : Set (Pattern A G)) : MulSubshift A G where
  carrier := mulForbidden F
  isClosed := isClosed_mulForbidden F
  mapsTo := Pattern.mapsTo_mulShift_mulForbidden F

end DefSubshiftByForbidden

section Language

variable {A : Type*} [Fintype A] [Inhabited A]
variable {G : Type*}

/--
lemma `finite_setOfPred_pattern_support_eq` / 引理 `finite_setOfPred_pattern_support_eq`

English:
lemma finite_setOfPred_pattern_support_eq
  proof: by
  -- 1. Upgrade Finite A to Fintype A locally
  cases nonempty_fintype A
  classical
  -- Patterns with support U biject with (U → A) via restriction/extension
  let e : { p : Pattern A G // p.support = U } ≃ (U -> A) :=
  { toFun := fun p i => p.1.config i.1
    invFun := fun f => ⟨{ config := f

中文:
引理 finite_setOfPred_pattern_support_eq
  证明: by
  -- 1. Upgrade Finite A to Fintype A locally
  cases nonempty_fintype A
  classical
  -- Patterns with support U biject with (U → A) via restriction/extension
  let e : { p : Pattern A G // p.support = U } ≃ (U -> A) :=
  { toFun := fun p i => p.1.config i.1
    invFun := fun f => ⟨{ config := f
-/
lemma finite_setOfPred_pattern_support_eq
    {A G : Type*} [Finite A] [Inhabited A]
    (U : Finset G) :
    ({p : Pattern A G | p.support = U}).Finite := by
  -- 1. Upgrade Finite A to Fintype A locally
  cases nonempty_fintype A
  classical
  -- Patterns with support U biject with (U → A) via restriction/extension
  let e : { p : Pattern A G // p.support = U } ≃ (U -> A) :=
  { toFun := fun p i => p.1.config i.1
    invFun := fun f => ⟨{ config := fun g => if h : g in U then f ⟨g, h⟩ else default,
                           support := U,
                           condition := fun g hg => by simp [hg] }, rfl⟩
    left_inv := by
      rintro ⟨⟨cfg, dom, cond⟩, hU⟩
      simp only at hU; subst hU
      apply Subtype.ext
      simp only [Pattern.mk.injEq, and_true]
      funext g
      by_cases hg : g in dom
      · simp [hg]
      · simp [hg, cond g hg]
    right_inv := fun f => by ext i; simp [i.2] }
  let : Fintype { p : Pattern A G | p.support = U } := Fintype.ofEquiv (U -> A) e.symm
  apply toFinite

@[deprecated (since := "2026-07-09")]
alias finite_setOf_pattern_support_eq := finite_setOfPred_pattern_support_eq

/--
Definition of `LanguageOn` / `LanguageOn` 的定义

English:
definition LanguageOn
  signature: (X : Set (G -> A)) (U : Finset G)
  body: { p | exists x in X, Pattern.fromConfig x U = p }

中文:
定义 LanguageOn
  签名: (X : 集合 (G -> A)) (U : 有限集 G)
  定义体: { p | exists x in X, Pattern.fromConfig x U = p }

Depends on / 依赖: Pattern, Pattern.fromConfig, fromConfig
-/
def LanguageOn (X : Set (G -> A)) (U : Finset G) : Set (Pattern A G) :=
  { p | exists x in X, Pattern.fromConfig x U = p }

/--
Definition of `MulSubshift.languageOn` / `MulSubshift.languageOn` 的定义

English:
definition MulSubshift.languageOn
  signature: {A G} [TopologicalSpace A] [Inhabited A] [Monoid G]
  body: SymbolicDynamics.FullShift.LanguageOn (A := A) (G := G) Y.carrier U

中文:
定义 MulSubshift.languageOn
  签名: {A G} [拓扑空间 A] [可居 A] [幺半群 G]
  定义体: SymbolicDynamics.FullShift.LanguageOn (A := A) (G := G) Y.carrier U

Depends on / 依赖: FullShift, LanguageOn, SymbolicDynamics, SymbolicDynamics.FullShift.LanguageOn, Y.carrier, carrier
-/
def MulSubshift.languageOn {A G} [TopologicalSpace A] [Inhabited A] [Monoid G]
    (Y : MulSubshift A G) (U : Finset G) : Set (Pattern A G) :=
  SymbolicDynamics.FullShift.LanguageOn (A := A) (G := G) Y.carrier U

end Language

end FullShift

end SymbolicDynamics
