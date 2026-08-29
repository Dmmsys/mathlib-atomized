/-
Copyright (c) 2022 Apurva Nakade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Apurva Nakade, Yaël Dillies
-/
module

public import Mathlib.Analysis.Convex.Cone.Closure
public import Mathlib.Geometry.Convex.Cone.Pointed
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars
public import Mathlib.Topology.Algebra.Order.Module
public import Mathlib.Topology.Order.DenselyOrdered

/-!
# Proper cones

We define a *proper cone* as a closed, pointed cone. Proper cones are used in defining conic
programs which generalize linear programs. A linear program is a conic program for the positive
cone. We then prove Farkas' lemma for conic programs following the proof in the reference below.
Farkas' lemma is equivalent to strong duality. So, once we have the definitions of conic and
linear programs, the results from this file can be used to prove duality theorems.

One can turn `C : PointedCone R E` + `hC : IsClosed C` into `C : ProperCone R E` in a tactic block
by doing `lift C to ProperCone R E using hC`.

One can also turn `C : ConvexCone 𝕜 E` + `hC : Set.Nonempty C ∧ IsClosed C` into
`C : ProperCone 𝕜 E` in a tactic block by doing `lift C to ProperCone 𝕜 E using hC`,
assuming `𝕜` is a dense topological field.

## TODO

The next steps are:
- Add `ConvexConeClass` that extends `SetLike` and replace the below instance
- Define primal and dual cone programs and prove weak duality.
- Prove regular and strong duality for cone programs using Farkas' lemma (see reference).
- Define linear programs and prove LP duality as a special case of cone duality.
- Find a better reference (textbook instead of lecture notes).

## References

- [B. Gartner and J. Matousek, Cone Programming][gartnerMatousek]

-/

@[expose] public section

open ContinuousLinearMap Filter Function Set

variable {𝕜 R E F G : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommMonoid E] [TopologicalSpace E] [Module R E]
variable [AddCommMonoid F] [TopologicalSpace F] [Module R F]
variable [AddCommMonoid G] [TopologicalSpace G] [Module R G]

local notation "R>=0" => {r : R // 0 <= r}

variable (R E) in
/--
Definition of `ProperCone` / `ProperCone` 的定义

English:
abbreviation ProperCone
  body: ClosedSubmodule R>=0 E

中文:
缩写 ProperCone
  定义体: ClosedSubmodule R>=0 E

Depends on / 依赖: ClosedSubmodule
-/
abbrev ProperCone := ClosedSubmodule R>=0 E

namespace ProperCone
section Module
variable {C C₁ C₂ : ProperCone R E} {r : R} {x : E}

/--
Definition of `toPointedCone` / `toPointedCone` 的定义

English:
abbreviation toPointedCone
  signature: (C : ProperCone R E)
  body: C.toSubmodule

中文:
缩写 toPointedCone
  签名: (C : 命题erCone R E)
  定义体: C.toSubmodule
-/
@[coe] abbrev toPointedCone (C : ProperCone R E) : PointedCone R E := C.toSubmodule

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (ProperCone R E) (PointedCone R E)
  body: ⟨toPointedCone⟩

中文:
实例 :
  签名: Coe (命题erCone R E) (PointedCone R E)
  定义体: ⟨toPointedCone⟩

Depends on / 依赖: toPointedCone
-/
instance : Coe (ProperCone R E) (PointedCone R E) := ⟨toPointedCone⟩

/--
lemma `toPointedCone_injective` / 引理 `toPointedCone_injective`

English:
lemma toPointedCone_injective
  statement: Injective ((↑) : ProperCone R E -> PointedCone R E)
  proof: ClosedSubmodule.toSubmodule_injective

中文:
引理 toPointedCone_injective
  结论: Injective ((↑) : 命题erCone R E -> PointedCone R E)
  证明: ClosedSubmodule.toSubmodule_injective

Depends on / 依赖: ClosedSubmodule, ClosedSubmodule.toSubmodule_injective, toSubmodule_injective
-/
lemma toPointedCone_injective : Injective ((↑) : ProperCone R E -> PointedCone R E) :=
  ClosedSubmodule.toSubmodule_injective

-- TODO: add `ConvexConeClass` that extends `SetLike` and replace the below instance
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (ProperCone R E) E
  body: C.carrier
coe_injective _ _ h := ProperCone.toPointedCone_injective SetLike.coe_injective h

中文:
实例 :
  签名: SetLike (命题erCone R E) E
  定义体: C.carrier
coe_injective _ _ h := ProperCone.toPointedCone_injective SetLike.coe_injective h

Depends on / 依赖: C.carrier, carrier
-/
instance : SetLike (ProperCone R E) E where
  coe C := C.carrier
coe_injective _ _ h := ProperCone.toPointedCone_injective SetLike.coe_injective h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (ProperCone R E)
  body: .ofSetLike (ProperCone R E) E

中文:
实例 :
  签名: PartialOrder (命题erCone R E)
  定义体: .ofSetLike (ProperCone R E) E

Depends on / 依赖: ProperCone, ofSetLike
-/
instance : PartialOrder (ProperCone R E) := .ofSetLike (ProperCone R E) E

/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: (h : forall x, x in C₁ ↔ x in C₂)
  statement: C₁ = C₂
  proof: SetLike.ext h

中文:
引理 ext
  条件: (h : 对任意 x, x in C₁ ↔ x in C₂)
  结论: C₁ = C₂
  证明: SetLike.ext h
-/
@[ext] lemma ext (h : forall x, x in C₁ ↔ x in C₂) : C₁ = C₂ := SetLike.ext h

/--
lemma `mem_toPointedCone` / 引理 `mem_toPointedCone`

English:
lemma mem_toPointedCone
  statement: x in C.toPointedCone ↔ x in C
  proof: .rfl

中文:
引理 mem_toPointedCone
  结论: x in C.toPointedCone ↔ x in C
  证明: .rfl
-/
lemma mem_toPointedCone : x in C.toPointedCone ↔ x in C := .rfl

/--
lemma `pointed_toConvexCone` / 引理 `pointed_toConvexCone`

English:
lemma pointed_toConvexCone
  given: (C : ProperCone R E)
  statement: (C : ConvexCone R E).Pointed
  proof: C.toPointedCone.pointed_toConvexCone

中文:
引理 pointed_toConvexCone
  条件: (C : 命题erCone R E)
  结论: (C : ConvexCone R E).Pointed
  证明: C.toPointedCone.pointed_toConvexCone

Depends on / 依赖: C.toPointedCone.pointed_toConvexCone, pointed_toConvexCone, toPointedCone
-/
lemma pointed_toConvexCone (C : ProperCone R E) : (C : ConvexCone R E).Pointed :=
  C.toPointedCone.pointed_toConvexCone

/--
lemma `nonempty` / 引理 `nonempty`

English:
lemma nonempty
  given: (C : ProperCone R E)
  statement: (C : Set E).Nonempty
  proof: C.toSubmodule.nonempty

中文:
引理 nonempty
  条件: (C : 命题erCone R E)
  结论: (C : Set E).Nonempty
  证明: C.toSubmodule.nonempty
-/
protected lemma nonempty (C : ProperCone R E) : (C : Set E).Nonempty := C.toSubmodule.nonempty
/--
lemma `isClosed` / 引理 `isClosed`

English:
lemma isClosed
  given: (C : ProperCone R E)
  statement: IsClosed (C : Set E)
  proof: C.isClosed'

中文:
引理 isClosed
  条件: (C : 命题erCone R E)
  结论: IsClosed (C : Set E)
  证明: C.isClosed'
-/
protected lemma isClosed (C : ProperCone R E) : IsClosed (C : Set E) := C.isClosed'
/--
lemma `convex` / 引理 `convex`

English:
lemma convex
  given: (C : ProperCone R E)
  statement: Convex R (C : Set E)
  proof: C.toPointedCone.convex

protected nonrec lemma smul_mem (C : ProperCone R E) (hx : x in C) (hr : 0 <= r) : r • x in C :=
  C.smul_mem ⟨r, hr⟩ hx

中文:
引理 convex
  条件: (C : 命题erCone R E)
  结论: Convex R (C : Set E)
  证明: C.toPointedCone.convex

protected nonrec lemma smul_mem (C : ProperCone R E) (hx : x in C) (hr : 0 <= r) : r • x in C :=
  C.smul_mem ⟨r, hr⟩ hx
-/
protected lemma convex (C : ProperCone R E) : Convex R (C : Set E) := C.toPointedCone.convex

protected nonrec lemma smul_mem (C : ProperCone R E) (hx : x in C) (hr : 0 <= r) : r • x in C :=
  C.smul_mem ⟨r, hr⟩ hx

section T1Space
variable [T1Space E]

/--
lemma `mem_bot` / 引理 `mem_bot`

English:
lemma mem_bot
  statement: x in (⊥ : ProperCone R E) ↔ x = 0
  proof: .rfl

中文:
引理 mem_bot
  结论: x in (⊥ : 命题erCone R E) ↔ x = 0
  证明: .rfl
-/
lemma mem_bot : x in (⊥ : ProperCone R E) ↔ x = 0 := .rfl

/--
lemma `coe_bot` / 引理 `coe_bot`

English:
lemma coe_bot
  statement: (⊥ : ProperCone R E) = ({0} : Set E)
  proof: rfl

中文:
引理 coe_bot
  结论: (⊥ : 命题erCone R E) = ({0} : Set E)
  证明: rfl
-/
@[simp, norm_cast] lemma coe_bot : (⊥ : ProperCone R E) = ({0} : Set E) := rfl
/--
lemma `toPointedCone_bot` / 引理 `toPointedCone_bot`

English:
lemma toPointedCone_bot
  statement: (⊥ : ProperCone R E).toPointedCone = ⊥
  proof: rfl

中文:
引理 toPointedCone_bot
  结论: (⊥ : 命题erCone R E).toPointedCone = ⊥
  证明: rfl
-/
@[simp, norm_cast] lemma toPointedCone_bot : (⊥ : ProperCone R E).toPointedCone = ⊥ := rfl

end T1Space

/--
Definition of `comap` / `comap` 的定义

English:
abbreviation comap
  signature: (f : E ->L[R] F) (C : ProperCone R F)
  body: ClosedSubmodule.comap (f.restrictScalars R>=0) C

中文:
缩写 comap
  签名: (f : E ->L[R] F) (C : 命题erCone R F)
  定义体: ClosedSubmodule.comap (f.restrictScalars R>=0) C

Depends on / 依赖: ClosedSubmodule, ClosedSubmodule.comap, f.restrictScalars, restrictScalars
-/
abbrev comap (f : E ->L[R] F) (C : ProperCone R F) : ProperCone R E :=
  ClosedSubmodule.comap (f.restrictScalars R>=0) C

/--
lemma `comap_id` / 引理 `comap_id`

English:
lemma comap_id
  given: (C : ProperCone R F)
  statement: C.comap (.id _ _) = C
  proof: rfl

中文:
引理 comap_id
  条件: (C : 命题erCone R F)
  结论: C.comap (.id _ _) = C
  证明: rfl
-/
@[simp] lemma comap_id (C : ProperCone R F) : C.comap (.id _ _) = C := rfl

/--
lemma `coe_comap` / 引理 `coe_comap`

English:
lemma coe_comap
  given: (f : E ->L[R] F) (C : ProperCone R F)
  statement: (C.comap f : Set E) = f ⁻¹' C
  proof: rfl

中文:
引理 coe_comap
  条件: (f : E ->L[R] F) (C : 命题erCone R F)
  结论: (C.comap f : Set E) = f ⁻¹' C
  证明: rfl
-/
@[simp] lemma coe_comap (f : E ->L[R] F) (C : ProperCone R F) : (C.comap f : Set E) = f ⁻¹' C := rfl

/--
lemma `comap_comap` / 引理 `comap_comap`

English:
lemma comap_comap
  given: (g : F ->L[R] G) (f : E ->L[R] F) (C : ProperCone R G)
  proof: rfl

中文:
引理 comap_comap
  条件: (g : F ->L[R] G) (f : E ->L[R] F) (C : 命题erCone R G)
  证明: rfl
-/
lemma comap_comap (g : F ->L[R] G) (f : E ->L[R] F) (C : ProperCone R G) :
    (C.comap g).comap f = C.comap (g.comp f) := rfl

/--
lemma `mem_comap` / 引理 `mem_comap`

English:
lemma mem_comap
  given: {C : ProperCone R F} {f : E ->L[R] F}
  statement: x in C.comap f ↔ f x in C
  proof: .rfl

中文:
引理 mem_comap
  条件: {C : 命题erCone R F} {f : E ->L[R] F}
  结论: x in C.comap f ↔ f x in C
  证明: .rfl
-/
lemma mem_comap {C : ProperCone R F} {f : E ->L[R] F} : x in C.comap f ↔ f x in C := .rfl

variable [ContinuousAdd F] [ContinuousConstSMul R F]

/--
Definition of `map` / `map` 的定义

English:
abbreviation map
  signature: (f : E ->L[R] F) (C : ProperCone R E)
  body: ClosedSubmodule.map (f.restrictScalars R>=0) C

中文:
缩写 map
  签名: (f : E ->L[R] F) (C : 命题erCone R E)
  定义体: ClosedSubmodule.map (f.restrictScalars R>=0) C

Depends on / 依赖: ClosedSubmodule, ClosedSubmodule.map, f.restrictScalars, restrictScalars
-/
abbrev map (f : E ->L[R] F) (C : ProperCone R E) : ProperCone R F :=
  ClosedSubmodule.map (f.restrictScalars R>=0) C

/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  given: (C : ProperCone R F)
  statement: C.map (.id _ _) = C
  proof: ClosedSubmodule.map_id _

@[simp, norm_cast]

中文:
引理 map_id
  条件: (C : 命题erCone R F)
  结论: C.map (.id _ _) = C
  证明: ClosedSubmodule.map_id _

@[simp, norm_cast]
-/
@[simp] lemma map_id (C : ProperCone R F) : C.map (.id _ _) = C := ClosedSubmodule.map_id _

@[simp, norm_cast]
/--
lemma `coe_map` / 引理 `coe_map`

English:
lemma coe_map
  given: (f : E ->L[R] F) (C : ProperCone R E)
  proof: rfl

@[simp]

中文:
引理 coe_map
  条件: (f : E ->L[R] F) (C : 命题erCone R E)
  证明: rfl

@[simp]
-/
lemma coe_map (f : E ->L[R] F) (C : ProperCone R E) :
    C.map f = (C.toPointedCone.map (f : E ->ₗ[R] F)).closure := rfl

@[simp]
/--
lemma `mem_map` / 引理 `mem_map`

English:
lemma mem_map
  given: {f : E ->L[R] F} {C : ProperCone R E} {y : F}
  proof: .rfl

中文:
引理 mem_map
  条件: {f : E ->L[R] F} {C : 命题erCone R E} {y : F}
  证明: .rfl
-/
lemma mem_map {f : E ->L[R] F} {C : ProperCone R E} {y : F} :
    y in C.map f ↔ y in (C.toPointedCone.map (f : E ->ₗ[R] F)).closure := .rfl

end Module

section PositiveCone
variable [PartialOrder E] [IsOrderedAddMonoid E] [PosSMulMono R E] [OrderClosedTopology E] {x : E}

variable (R E) in
/-- The positive cone is the proper cone formed by the set of nonnegative elements in an ordered
module. -/
@[simps!]
/--
Definition of `positive` / `positive` 的定义

English:
definition positive
  signature: : ProperCone R E where
  body: PointedCone.positive R E
  isClosed' := isClosed_Ici

中文:
定义 positive
  签名: : 命题erCone R E where
  定义体: PointedCone.positive R E
  isClosed' := isClosed_Ici

Depends on / 依赖: PointedCone, PointedCone.positive, positive
-/
def positive : ProperCone R E where
  toSubmodule := PointedCone.positive R E
  isClosed' := isClosed_Ici

/--
lemma `mem_positive` / 引理 `mem_positive`

English:
lemma mem_positive
  statement: x in positive R E ↔ 0 <= x
  proof: .rfl

中文:
引理 mem_positive
  结论: x in positive R E ↔ 0 <= x
  证明: .rfl
-/
@[simp] lemma mem_positive : x in positive R E ↔ 0 <= x := .rfl
/--
lemma `toPointedCone_positive` / 引理 `toPointedCone_positive`

English:
lemma toPointedCone_positive
  statement: (positive R E).toPointedCone = .positive R E
  proof: rfl

中文:
引理 toPointedCone_positive
  结论: (positive R E).toPointedCone = .positive R E
  证明: rfl
-/
@[simp] lemma toPointedCone_positive : (positive R E).toPointedCone = .positive R E := rfl

end PositiveCone
end ProperCone

/-!
### Topological properties of convex cones

This section proves topological results about convex cones.

#### TODO

This result generalises to G-submodules.
-/

namespace ConvexCone
variable [Semifield 𝕜] [LinearOrder 𝕜] [Module 𝕜 E] {s : Set E}

-- FIXME: This is necessary for the proof below but triggers the `unusedSectionVars` linter.
-- variable [IsStrictOrderedRing 𝕜] [IsTopologicalAddGroup M] in
/-- This is true essentially by `Submodule.span_eq_iUnion_nat`, except that `Submodule` currently
doesn't support that use case. See
https://leanprover.zulipchat.com/#narrow/channel/116395-maths/topic/G-submodules/with/514426583 -/
proof_wanted isOpen_hull (hs : IsOpen s) : IsOpen (hull 𝕜 s : Set E)

variable [TopologicalSpace 𝕜] [OrderTopology 𝕜] [DenselyOrdered 𝕜] [NoMaxOrder 𝕜]
  [ContinuousSMul 𝕜 E] {C : ConvexCone 𝕜 E}

/--
lemma `Pointed.of_nonempty_of_isClosed` / 引理 `Pointed.of_nonempty_of_isClosed`

English:
lemma Pointed.of_nonempty_of_isClosed
  given: (hC : (C : Set E).Nonempty) (hSclos : IsClosed (C : Set E))
  proof: by
  obtain ⟨x, hx⟩ := hC
  let f : 𝕜 -> E := (· • x)
  -- The closure of `f (0, ∞)` is a subset of `C`
  have hfS : closure (f '' Set.Ioi 0) subseteq C :=
hSclos.closure_subset_iff.2 by rintro _ ⟨_, h, rfl⟩; exact C.smul_mem h hx
  -- `f` is continuous at `0` from the right
  have fc : ContinuousWi

中文:
引理 Pointed.of_nonempty_of_isClosed
  条件: (hC : (C : Set E).Nonempty) (hSclos : IsClosed (C : Set E))
  证明: by
  obtain ⟨x, hx⟩ := hC
  let f : 𝕜 -> E := (· • x)
  -- The closure of `f (0, ∞)` is a subset of `C`
  have hfS : closure (f '' Set.Ioi 0) subseteq C :=
hSclos.closure_subset_iff.2 by rintro _ ⟨_, h, rfl⟩; exact C.smul_mem h hx
  -- `f` is continuous at `0` from the right
  have fc : ContinuousWi
-/
lemma Pointed.of_nonempty_of_isClosed (hC : (C : Set E).Nonempty) (hSclos : IsClosed (C : Set E)) :
    C.Pointed := by
  obtain ⟨x, hx⟩ := hC
  let f : 𝕜 -> E := (· • x)
  -- The closure of `f (0, ∞)` is a subset of `C`
  have hfS : closure (f '' Set.Ioi 0) subseteq C :=
hSclos.closure_subset_iff.2 by rintro _ ⟨_, h, rfl⟩; exact C.smul_mem h hx
  -- `f` is continuous at `0` from the right
  have fc : ContinuousWithinAt f (Set.Ioi (0 : 𝕜)) 0 := by fun_prop
  -- `0 ∈ closure f (0, ∞) ⊆ C, 0 ∈ C`
simpa [f, Pointed, ← SetLike.mem_coe] using hfS fc.mem_closure_image by simp

variable [IsOrderedRing 𝕜]

/--
Instance `canLift` / 实例 `canLift`

English:
instance canLift
  signature: : CanLift (ConvexCone 𝕜 E) (ProperCone 𝕜 E) (↑)
  body: ⟨⟨C.toPointedCone .of_nonempty_of_isClosed hC.1 hC.2, hC.2⟩, rfl⟩

中文:
实例 canLift
  签名: : CanLift (ConvexCone 𝕜 E) (命题erCone 𝕜 E) (↑)
  定义体: ⟨⟨C.toPointedCone .of_nonempty_of_isClosed hC.1 hC.2, hC.2⟩, rfl⟩

Depends on / 依赖: C.toPointedCone, of_nonempty_of_isClosed, toPointedCone
-/
instance canLift : CanLift (ConvexCone 𝕜 E) (ProperCone 𝕜 E) (↑)
    fun C => (C : Set E).Nonempty ∧ IsClosed (C : Set E) where
prf C hC := ⟨⟨C.toPointedCone .of_nonempty_of_isClosed hC.1 hC.2, hC.2⟩, rfl⟩

end ConvexCone
