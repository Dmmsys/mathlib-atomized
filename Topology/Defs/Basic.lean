/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Jeremy Avigad
-/
module

public import Mathlib.Order.SetNotation
public import Mathlib.Tactic.Continuity
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.MkIffOfInductiveProp
public import Mathlib.Data.Nat.Notation

public meta import Mathlib.Util.DelabNonCanonical

/-!
# Basic definitions about topological spaces

This file contains definitions about topology that do not require imports
other than `Mathlib/Data/Set/Lattice.lean`.

## Main definitions

* `TopologicalSpace X`: a typeclass endowing `X` with a topology.
  By definition, a topology is a collection of sets called *open sets* such that

  - `isOpen_univ`: the whole space is open;
  - `IsOpen.inter`: the intersection of two open sets is an open set;
  - `isOpen_sUnion`: the union of a family of open sets is an open set.

* `IsOpen s`: predicate saying that `s` is an open set, same as `TopologicalSpace.IsOpen`.

* `IsClosed s`: a set is called *closed*, if its complement is an open set.
  For technical reasons, this is a typeclass.

* `IsClopen s`: a set is *clopen* if it is both closed and open.

* `interior s`: the *interior* of a set `s` is the maximal open set that is included in `s`.

* `closure s`: the *closure* of a set `s` is the minimal closed set that includes `s`.

* `frontier s`: the *frontier* of a set is the set difference `closure s \ interior s`.
  A point `x` belongs to `frontier s`, if any neighborhood of `x`
  contains points both from `s` and `sᶜ`.

* `Dense s`: a set is *dense* if its closure is the whole space.
  We define it as `∀ x, x ∈ closure s` so that one can write `(h : Dense s) x`.

* `DenseRange f`: a function has *dense range*, if `Set.range f` is a dense set.

* `Continuous f`: a map is *continuous*, if the preimage of any open set is an open set.

* `IsOpenMap f`: a map is an *open map*, if the image of any open set is an open set.

* `IsClosedMap f`: a map is a *closed map*, if the image of any closed set is a closed set.

** Notation

We introduce notation `IsOpen[t]`, `IsClosed[t]`, `closure[t]`, `Continuous[t₁, t₂]`
that allow passing custom topologies to these predicates and functions without using `@`.
-/

@[expose] public section

assert_not_exists Monoid

universe u v
open Set

/-- A topology on `X`. -/
@[to_dual_dont_translate]
/--
Definition of `TopologicalSpace` / `TopologicalSpace` 的定义

English:
class TopologicalSpace
  parameters: (X : Type u)
  axioms and operations (4):
    - IsOpen : Set X -> Prop
    - isOpen_univ : IsOpen univ
    - isOpen_inter : forall s t, IsOpen s -> IsOpen t -> IsOpen (s inter t)
    - isOpen_sUnion : forall s, (forall t in s, IsOpen t) -> IsOpen (⋃₀ s)

中文:
类 TopologicalSpace
  参数: (X : 类型u)
  公理与运算 (4 个):
    - IsOpen : Set X -> 命题
    - isOpen_univ : IsOpen univ
    - isOpen_inter : 对任意 s t, IsOpen s -> IsOpen t -> IsOpen (s inter t)
    - isOpen_sUnion : 对任意 s, (对任意 t in s, IsOpen t) -> IsOpen (⋃₀ s)
-/
class TopologicalSpace (X : Type u) where
  /-- A predicate saying that a set is an open set. Use `IsOpen` in the root namespace instead. -/
  protected IsOpen : Set X -> Prop
  /-- The set representing the whole space is an open set.
  Use `isOpen_univ` in the root namespace instead. -/
  protected isOpen_univ : IsOpen univ
  /-- The intersection of two open sets is an open set. Use `IsOpen.inter` instead. -/
  protected isOpen_inter : forall s t, IsOpen s -> IsOpen t -> IsOpen (s inter t)
  /-- The union of a family of open sets is an open set.
  Use `isOpen_sUnion` in the root namespace instead. -/
  protected isOpen_sUnion : forall s, (forall t in s, IsOpen t) -> IsOpen (⋃₀ s)

variable {X : Type u} {Y : Type v}

/-! ### Predicates on sets -/

section Defs

variable [TopologicalSpace X] [TopologicalSpace Y] {s t : Set X}

/-- `IsOpen s` means that `s` is open in the ambient topological space on `X` -/
@[wikidata Q213363]
/--
Definition of `IsOpen` / `IsOpen` 的定义

English:
definition IsOpen
  signature: : Set X -> Prop
  body: TopologicalSpace.IsOpen

中文:
定义 IsOpen
  签名: : Set X -> 命题
  定义体: TopologicalSpace.IsOpen

Depends on / 依赖: IsOpen, TopologicalSpace, TopologicalSpace.IsOpen
-/
def IsOpen : Set X -> Prop := TopologicalSpace.IsOpen

/--
theorem `isOpen_univ` / 定理 `isOpen_univ`

English:
theorem isOpen_univ
  statement: IsOpen (univ : Set X)
  proof: TopologicalSpace.isOpen_univ

中文:
定理 isOpen_univ
  结论: IsOpen (univ : Set X)
  证明: TopologicalSpace.isOpen_univ
-/
@[simp] theorem isOpen_univ : IsOpen (univ : Set X) := TopologicalSpace.isOpen_univ

/--
theorem `IsOpen.inter` / 定理 `IsOpen.inter`

English:
theorem IsOpen.inter
  given: (hs : IsOpen s) (ht : IsOpen t)
  statement: IsOpen (s inter t)
  proof: TopologicalSpace.isOpen_inter s t hs ht

中文:
定理 IsOpen.inter
  条件: (hs : IsOpen s) (ht : IsOpen t)
  结论: IsOpen (s inter t)
  证明: TopologicalSpace.isOpen_inter s t hs ht
-/
theorem IsOpen.inter (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s inter t) :=
  TopologicalSpace.isOpen_inter s t hs ht

/--
theorem `isOpen_sUnion` / 定理 `isOpen_sUnion`

English:
theorem isOpen_sUnion
  given: {s : Set (Set X)} (h : forall t in s, IsOpen t)
  statement: IsOpen (⋃₀ s)
  proof: TopologicalSpace.isOpen_sUnion s h

中文:
定理 isOpen_sUnion
  条件: {s : Set (Set X)} (h : 对任意 t in s, IsOpen t)
  结论: IsOpen (⋃₀ s)
  证明: TopologicalSpace.isOpen_sUnion s h

Depends on / 依赖: TopologicalSpace, TopologicalSpace.isOpen_sUnion, isOpen_sUnion
-/
theorem isOpen_sUnion {s : Set (Set X)} (h : forall t in s, IsOpen t) : IsOpen (⋃₀ s) :=
  TopologicalSpace.isOpen_sUnion s h

/-- A set is closed if its complement is open -/
@[wikidata Q320357]
/--
Definition of `IsClosed` / `IsClosed` 的定义

English:
class IsClosed
  parameters: (s : Set X)
  axioms and operations (1):
    - isOpen_compl : IsOpen sᶜ

中文:
类 IsClosed
  参数: (s : Set X)
  公理与运算 (1 个):
    - isOpen_compl : IsOpen sᶜ
-/
class IsClosed (s : Set X) : Prop where
  /-- The complement of a closed set is an open set. -/
  isOpen_compl : IsOpen sᶜ

/--
Definition of `IsClopen` / `IsClopen` 的定义

English:
definition IsClopen
  signature: (s : Set X)
  body: IsClosed s ∧ IsOpen s

中文:
定义 IsClopen
  签名: (s : Set X)
  定义体: IsClosed s ∧ IsOpen s

Depends on / 依赖: IsClosed, IsOpen
-/
def IsClopen (s : Set X) : Prop :=
  IsClosed s ∧ IsOpen s

/--
Definition of `IsLocallyClosed` / `IsLocallyClosed` 的定义

English:
definition IsLocallyClosed
  signature: (s : Set X)
  body: exists (U Z : Set X), IsOpen U ∧ IsClosed Z ∧ s = U inter Z

中文:
定义 IsLocallyClosed
  签名: (s : Set X)
  定义体: exists (U Z : Set X), IsOpen U ∧ IsClosed Z ∧ s = U inter Z

Depends on / 依赖: IsClosed, IsOpen
-/
def IsLocallyClosed (s : Set X) : Prop := exists (U Z : Set X), IsOpen U ∧ IsClosed Z ∧ s = U inter Z

/--
Definition of `interior` / `interior` 的定义

English:
definition interior
  signature: (s : Set X)
  body: ⋃₀ { t | IsOpen t ∧ t subseteq s }

中文:
定义 interior
  签名: (s : Set X)
  定义体: ⋃₀ { t | IsOpen t ∧ t subseteq s }

Depends on / 依赖: IsOpen, subseteq
-/
def interior (s : Set X) : Set X :=
  ⋃₀ { t | IsOpen t ∧ t subseteq s }

/--
Definition of `closure` / `closure` 的定义

English:
definition closure
  signature: (s : Set X)
  body: ⋂₀ { t | IsClosed t ∧ s subseteq t }

中文:
定义 closure
  签名: (s : Set X)
  定义体: ⋂₀ { t | IsClosed t ∧ s subseteq t }

Depends on / 依赖: IsClosed, subseteq
-/
def closure (s : Set X) : Set X :=
  ⋂₀ { t | IsClosed t ∧ s subseteq t }

/--
Definition of `frontier` / `frontier` 的定义

English:
definition frontier
  signature: (s : Set X)
  body: closure s \ interior s

中文:
定义 frontier
  签名: (s : Set X)
  定义体: closure s \ interior s

Depends on / 依赖: closure, interior
-/
def frontier (s : Set X) : Set X :=
  closure s \ interior s

/--
Definition of `coborder` / `coborder` 的定义

English:
definition coborder
  signature: (s : Set X)
  body: (closure s \ s)ᶜ

中文:
定义 coborder
  签名: (s : Set X)
  定义体: (closure s \ s)ᶜ

Depends on / 依赖: closure
-/
def coborder (s : Set X) : Set X :=
  (closure s \ s)ᶜ

/--
Definition of `Dense` / `Dense` 的定义

English:
definition Dense
  signature: (s : Set X)
  body: forall x, x in closure s

中文:
定义 Dense
  签名: (s : Set X)
  定义体: forall x, x in closure s

Depends on / 依赖: closure
-/
def Dense (s : Set X) : Prop :=
  forall x, x in closure s

/--
Definition of `DenseRange` / `DenseRange` 的定义

English:
definition DenseRange
  signature: {α : Type*} (f : α -> X)
  body: Dense (range f)

中文:
定义 DenseRange
  签名: {α : 类型} (f : α -> X)
  定义体: Dense (range f)
-/
def DenseRange {α : Type*} (f : α -> X) := Dense (range f)

/-- A function between topological spaces is continuous if the preimage
  of every open set is open. Registered as a structure to make sure it is not unfolded by Lean. -/
@[fun_prop, wikidata Q170058]
/--
Definition of `Continuous` / `Continuous` 的定义

English:
structure Continuous
  parameters: (f : X -> Y)
  axioms and operations (1):
    - isOpen_preimage : forall s, IsOpen s -> IsOpen (f ⁻¹' s)

中文:
结构 Continuous
  参数: (f : X -> Y)
  公理与运算 (1 个):
    - isOpen_preimage : 对任意 s, IsOpen s -> IsOpen (f ⁻¹' s)
-/
structure Continuous (f : X -> Y) : Prop where
  /-- The preimage of an open set under a continuous function is an open set. Use `IsOpen.preimage`
  instead. -/
  isOpen_preimage : forall s, IsOpen s -> IsOpen (f ⁻¹' s)

/--
Definition of `IsOpenMap` / `IsOpenMap` 的定义

English:
definition IsOpenMap
  signature: (f : X -> Y)
  body: forall U : Set X, IsOpen U -> IsOpen (f '' U)

中文:
定义 IsOpenMap
  签名: (f : X -> Y)
  定义体: forall U : Set X, IsOpen U -> IsOpen (f '' U)

Depends on / 依赖: IsOpen
-/
def IsOpenMap (f : X -> Y) : Prop := forall U : Set X, IsOpen U -> IsOpen (f '' U)

/--
Definition of `IsClosedMap` / `IsClosedMap` 的定义

English:
definition IsClosedMap
  signature: (f : X -> Y)
  body: forall U : Set X, IsClosed U -> IsClosed (f '' U)

中文:
定义 IsClosedMap
  签名: (f : X -> Y)
  定义体: forall U : Set X, IsClosed U -> IsClosed (f '' U)

Depends on / 依赖: IsClosed
-/
def IsClosedMap (f : X -> Y) : Prop := forall U : Set X, IsClosed U -> IsClosed (f '' U)

/-- An open quotient map is an open map `f : X → Y` which is both an open map and a quotient map.
Equivalently, it is a surjective continuous open map.
We use the latter characterization as a definition.

Many important quotient maps are open quotient maps, including

- the quotient map from a topological space to its quotient by the action of a group;
- the quotient map from a topological group to its quotient by a normal subgroup;
- the quotient map from a topological space to its separation quotient.

Contrary to general quotient maps,
the category of open quotient maps is closed under `Prod.map`.
-/
@[mk_iff]
/--
Definition of `IsOpenQuotientMap` / `IsOpenQuotientMap` 的定义

English:
structure IsOpenQuotientMap
  parameters: (f : X -> Y)
  axioms and operations (3):
    - surjective : Function.Surjective f
    - continuous : Continuous f
    - isOpenMap : IsOpenMap f

中文:
结构 IsOpenQuotientMap
  参数: (f : X -> Y)
  公理与运算 (3 个):
    - surjective : Function.Surjective f
    - continuous : Continuous f
    - isOpenMap : IsOpenMap f
-/
structure IsOpenQuotientMap (f : X -> Y) : Prop where
  /-- An open quotient map is surjective. -/
  surjective : Function.Surjective f
  /-- An open quotient map is continuous. -/
  continuous : Continuous f
  /-- An open quotient map is an open map. -/
  isOpenMap : IsOpenMap f

end Defs

/-! ### Notation for non-standard topologies -/

namespace Topology

/-- Notation for `IsOpen` with respect to a non-standard topology. -/
scoped notation (name := IsOpen_of) "IsOpen[" t "]" => @IsOpen _ t

/-- Notation for `IsClosed` with respect to a non-standard topology. -/
scoped notation (name := IsClosed_of) "IsClosed[" t "]" => @IsClosed _ t

/-- Notation for `closure` with respect to a non-standard topology. -/
scoped notation (name := closure_of) "closure[" t "]" => @closure _ t

/-- Notation for `Continuous` with respect to non-standard topologies. -/
scoped notation (name := Continuous_of) "Continuous[" t₁ ", " t₂ "]" =>
  @Continuous _ _ t₁ t₂

open Topology Lean.PrettyPrinter.Delaborator Delab.Noncanonical

/-- Delaborator for `IsOpen[_]`. -/
@[scoped app_delab IsOpen] meta def delabIsOpen : Delab := delabUnary 2 1 fun x => `(IsOpen[$x])

/-- Delaborator for `IsClosed[_]`. -/
@[scoped app_delab IsClosed]
meta def delabIsClosed : Delab := delabUnary 2 1 fun x => `(IsClosed[$x])

/-- Delaborator for `closure[_]`. -/
@[scoped app_delab closure] meta def delabClosure : Delab := delabUnary 2 1 fun x => `(closure[$x])

/-- Delaborator for `Continuous[_, _]`. -/
@[scoped app_delab Continuous]
meta def delabContinuous : Delab :=
  delabBinary 4 2 3 (fun x y => `(Continuous[$x, $y]))

end Topology

/--
Definition of `BaireSpace` / `BaireSpace` 的定义

English:
class BaireSpace
  parameters: (X : Type*) [TopologicalSpace X]
  axioms and operations (1):
    - baire_property : forall f : Nat -> Set X, (forall n, IsOpen (f n)) -> (forall n, Dense (f n)) -> Dense (⋂ n, f n)

中文:
类 BaireSpace
  参数: (X : 类型) [TopologicalSpace X]
  公理与运算 (1 个):
    - baire_property : 对任意 f : 自然数 -> Set X, (对任意 n, IsOpen (f n)) -> (对任意 n, Dense (f n)) -> Dense (⋂ n, f n)
-/
class BaireSpace (X : Type*) [TopologicalSpace X] : Prop where
  baire_property : forall f : Nat -> Set X, (forall n, IsOpen (f n)) -> (forall n, Dense (f n)) -> Dense (⋂ n, f n)

/-- A one-field structure wrapper for `X` with the topology coinduced from `t`. -/
@[ext]
/--
Definition of `WithTopology` / `WithTopology` 的定义

English:
structure WithTopology
  parameters: (X : Type*) (t : TopologicalSpace X)
  axioms and operations (2):
    - toTopology((t)) : :
    - ofTopology : X

中文:
结构 WithTopology
  参数: (X : 类型) (t : TopologicalSpace X)
  公理与运算 (2 个):
    - toTopology((t)) : :
    - ofTopology : X
-/
structure WithTopology (X : Type*) (t : TopologicalSpace X) where
  /-- Converts an element of `X` to an element of `WithTopology X t`. -/
  toTopology (t) ::
  /-- Converts an element of `WithTopology X t` to an element of `X`. -/
  ofTopology : X

section Notation

open Lean.PrettyPrinter.Delaborator

/-- This prevents `toTopology t x` being printed as `{ ofTopology := x }`
by `delabStructureInstance`. -/
@[app_delab WithTopology.toTopology]
meta def WithTopology.delabToTopology : Delab := delabApp

end Notation
