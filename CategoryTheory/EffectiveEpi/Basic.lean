/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
/-!

# Effective epimorphisms

We define the notion of effective epimorphism and effective epimorphic family of morphisms.

A morphism is an *effective epi* if it is a joint coequalizer of all pairs of
morphisms which it coequalizes.

A family of morphisms with fixed target is *effective epimorphic* if it is initial among families
of morphisms with its sources and a general fixed target, coequalizing every pair of morphisms it
coequalizes (here, the pair of morphisms coequalized can have different targets among the sources
of the family).

We have defined the notion of effective epi for morphisms and families of morphisms in such a
way that avoids requiring the existence of pullbacks. However, if the relevant pullbacks exist
then these definitions are equivalent, see the file
`Mathlib/CategoryTheory/EffectiveEpi/RegularEpi.lean`
See [nlab: *Effective Epimorphism*](https://ncatlab.org/nlab/show/effective+epimorphism) and
[Stacks 00WP](https://stacks.math.columbia.edu/tag/00WP) for the standard definitions. Note that
our notion of `EffectiveEpi` is often called "strict epi" in the literature.

## References
- [Elephant]: *Sketches of an Elephant*, P. T. Johnstone: C2.1, Example 2.1.12.
- [nlab: *Effective Epimorphism*](https://ncatlab.org/nlab/show/effective+epimorphism) and
- [Stacks 00WP](https://stacks.math.columbia.edu/tag/00WP) for the standard definitions.

-/

@[expose] public section

namespace CategoryTheory

open Limits Category

variable {C : Type*} [Category* C]

/--
Definition of `EffectiveEpiStruct` / `EffectiveEpiStruct` 的定义

English:
structure EffectiveEpiStruct
  parameters: {X Y : C} (f : Y ⟶ X)
  axioms and operations (3):
    - desc : forall {W : C} (e : Y ⟶ W), (forall {Z : C} (g₁ g₂ : Z ⟶ Y), g₁ ≫ f = g₂ ≫ f -> g₁ ≫ e = g₂ ≫ e) -> (X ⟶ W)
    - fac : forall {W : C} (e : Y ⟶ W) (h : forall {Z : C} (g₁ g₂ : Z ⟶ Y), g₁ ≫ f = g₂ ≫ f -> g₁ ≫ e = g₂ ≫ e), f ≫ desc e h = e
    - uniq : forall {W : C} (e : Y ⟶ W) (h : forall {Z : C} (g₁ g₂ : Z ⟶ Y), g₁ ≫ f = g₂ ≫ f -> g₁ ≫ e = g₂ ≫ e) (m : X ⟶ W), f ≫ m = e -> m = desc e h

中文:
结构 EffectiveEpiStruct
  参数: {X Y : C} (f : Y ⟶ X)
  公理与运算 (3 个):
    - desc : 对任意 {W : C} (e : Y ⟶ W), (对任意 {Z : C} (g₁ g₂ : Z ⟶ Y), g₁ ≫ f = g₂ ≫ f -> g₁ ≫ e = g₂ ≫ e) -> (X ⟶ W)
    - fac : 对任意 {W : C} (e : Y ⟶ W) (h : 对任意 {Z : C} (g₁ g₂ : Z ⟶ Y), g₁ ≫ f = g₂ ≫ f -> g₁ ≫ e = g₂ ≫ e), f ≫ desc e h = e
    - uniq : 对任意 {W : C} (e : Y ⟶ W) (h : 对任意 {Z : C} (g₁ g₂ : Z ⟶ Y), g₁ ≫ f = g₂ ≫ f -> g₁ ≫ e = g₂ ≫ e) (m : X ⟶ W), f ≫ m = e -> m = desc e h
-/
structure EffectiveEpiStruct {X Y : C} (f : Y ⟶ X) where
  /--
  For every `W` with a morphism `e : Y ⟶ W` that coequalizes every pair of morphisms
  `g₁ g₂ : Z ⟶ Y` which `f` coequalizes, `desc e h` is a morphism `X ⟶ W`...
  -/
  desc : forall {W : C} (e : Y ⟶ W),
    (forall {Z : C} (g₁ g₂ : Z ⟶ Y), g₁ ≫ f = g₂ ≫ f -> g₁ ≫ e = g₂ ≫ e) -> (X ⟶ W)
  /-- ...factorizing `e` through `f`... -/
  fac : forall {W : C} (e : Y ⟶ W)
    (h : forall {Z : C} (g₁ g₂ : Z ⟶ Y), g₁ ≫ f = g₂ ≫ f -> g₁ ≫ e = g₂ ≫ e),
    f ≫ desc e h = e
  /-- ...and as such, unique. -/
  uniq : forall {W : C} (e : Y ⟶ W)
    (h : forall {Z : C} (g₁ g₂ : Z ⟶ Y), g₁ ≫ f = g₂ ≫ f -> g₁ ≫ e = g₂ ≫ e)
    (m : X ⟶ W), f ≫ m = e -> m = desc e h

/--
Definition of `EffectiveEpi` / `EffectiveEpi` 的定义

English:
class EffectiveEpi
  parameters: {X Y : C} (f : Y ⟶ X)
  axioms and operations (1):
    - effectiveEpi : Nonempty (EffectiveEpiStruct f)

中文:
类 EffectiveEpi
  参数: {X Y : C} (f : Y ⟶ X)
  公理与运算 (1 个):
    - effectiveEpi : Nonempty (EffectiveEpiStruct f)
-/
class EffectiveEpi {X Y : C} (f : Y ⟶ X) : Prop where
  /-- `f` is an effective epimorphism if there exists an `EffectiveEpiStruct` for `f`. -/
  effectiveEpi : Nonempty (EffectiveEpiStruct f)

/-- Some chosen `EffectiveEpiStruct` associated to an effective epi. -/
noncomputable
/--
Definition of `EffectiveEpi.getStruct` / `EffectiveEpi.getStruct` 的定义

English:
definition EffectiveEpi.getStruct
  signature: {X Y : C} (f : Y ⟶ X) [EffectiveEpi f]
  body: EffectiveEpi.effectiveEpi.some

中文:
定义 EffectiveEpi.getStruct
  签名: {X Y : C} (f : Y ⟶ X) [EffectiveEpi f]
  定义体: EffectiveEpi.effectiveEpi.some

Depends on / 依赖: EffectiveEpi, EffectiveEpi.effectiveEpi.some, createsLimitsOfShapeOfCreatesFiniteProducts, effectiveEpi
-/
def EffectiveEpi.getStruct {X Y : C} (f : Y ⟶ X) [EffectiveEpi f] : EffectiveEpiStruct f :=
  EffectiveEpi.effectiveEpi.some

/-- Descend along an effective epi. -/
noncomputable
/--
Definition of `EffectiveEpi.desc` / `EffectiveEpi.desc` 的定义

English:
definition EffectiveEpi.desc
  signature: {X Y W : C} (f : Y ⟶ X) [EffectiveEpi f]
  body: (EffectiveEpi.getStruct f).desc e h

@[reassoc (attr := simp)]

中文:
定义 EffectiveEpi.desc
  签名: {X Y W : C} (f : Y ⟶ X) [EffectiveEpi f]
  定义体: (EffectiveEpi.getStruct f).desc e h

@[reassoc (attr := simp)]

Depends on / 依赖: EffectiveEpi, EffectiveEpi.getStruct, getStruct
-/
def EffectiveEpi.desc {X Y W : C} (f : Y ⟶ X) [EffectiveEpi f]
    (e : Y ⟶ W) (h : forall {Z : C} (g₁ g₂ : Z ⟶ Y), g₁ ≫ f = g₂ ≫ f -> g₁ ≫ e = g₂ ≫ e) :
    X ⟶ W := (EffectiveEpi.getStruct f).desc e h

@[reassoc (attr := simp)]
/--
lemma `EffectiveEpi.fac` / 引理 `EffectiveEpi.fac`

English:
lemma EffectiveEpi.fac
  statement: {X Y W : C} (f : Y ⟶ X) [EffectiveEpi f]
  proof: (EffectiveEpi.getStruct f).fac e h

中文:
引理 EffectiveEpi.fac
  结论: {X Y W : C} (f : Y ⟶ X) [EffectiveEpi f]
  证明: (EffectiveEpi.getStruct f).fac e h

Depends on / 依赖: EffectiveEpi, EffectiveEpi.getStruct, getStruct
-/
lemma EffectiveEpi.fac {X Y W : C} (f : Y ⟶ X) [EffectiveEpi f]
    (e : Y ⟶ W) (h : forall {Z : C} (g₁ g₂ : Z ⟶ Y), g₁ ≫ f = g₂ ≫ f -> g₁ ≫ e = g₂ ≫ e) :
    f ≫ EffectiveEpi.desc f e h = e :=
  (EffectiveEpi.getStruct f).fac e h

/--
lemma `EffectiveEpi.uniq` / 引理 `EffectiveEpi.uniq`

English:
lemma EffectiveEpi.uniq
  statement: {X Y W : C} (f : Y ⟶ X) [EffectiveEpi f]
  proof: (EffectiveEpi.getStruct f).uniq e h _ hm

中文:
引理 EffectiveEpi.uniq
  结论: {X Y W : C} (f : Y ⟶ X) [EffectiveEpi f]
  证明: (EffectiveEpi.getStruct f).uniq e h _ hm

Depends on / 依赖: EffectiveEpi, EffectiveEpi.getStruct, getStruct
-/
lemma EffectiveEpi.uniq {X Y W : C} (f : Y ⟶ X) [EffectiveEpi f]
    (e : Y ⟶ W) (h : forall {Z : C} (g₁ g₂ : Z ⟶ Y), g₁ ≫ f = g₂ ≫ f -> g₁ ≫ e = g₂ ≫ e)
    (m : X ⟶ W) (hm : f ≫ m = e) :
    m = EffectiveEpi.desc f e h :=
  (EffectiveEpi.getStruct f).uniq e h _ hm

open EffectiveEpi Category

/--
Instance `epi_of_effectiveEpi` / 实例 `epi_of_effectiveEpi`

English:
instance epi_of_effectiveEpi
  signature: {X Y : C} (f : Y ⟶ X) [EffectiveEpi f]
  body: by
    rw [show m₂ = desc f (f ≫ m₂) (fun _ _ h => by simp [← assoc]; rw [h]) from uniq _ _ _ _ rfl]
    exact uniq _ _ _ _ h

中文:
实例 epi_of_effectiveEpi
  签名: {X Y : C} (f : Y ⟶ X) [EffectiveEpi f]
  定义体: by
    rw [show m₂ = desc f (f ≫ m₂) (fun _ _ h => by simp [← assoc]; rw [h]) from uniq _ _ _ _ rfl]
    exact uniq _ _ _ _ h
-/
instance epi_of_effectiveEpi {X Y : C} (f : Y ⟶ X) [EffectiveEpi f] : Epi f where
  left_cancellation m₁ m₂ h := by
    rw [show m₂ = desc f (f ≫ m₂) (fun _ _ h => by simp [← assoc]; rw [h]) from uniq _ _ _ _ rfl]
    exact uniq _ _ _ _ h

instance (priority := 100) strongEpi_of_effectiveEpi {X Y : C} (f : X ⟶ Y) [EffectiveEpi f] :
    StrongEpi f :=
  StrongEpi.mk' fun A B z hz u v sq =>
    have : forall {Z : C} (g₁ g₂ : Z ⟶ X), g₁ ≫ f = g₂ ≫ f -> g₁ ≫ u = g₂ ≫ u := fun _ _ h => by
      simpa [← sq.w, cancel_mono_assoc_iff] using h =≫ v
    CommSq.HasLift.mk' ⟨desc f u this, fac f u this, (cancel_epi f).1 ((by simp [← sq.w]))⟩

/--
Definition of `EffectiveEpiFamilyStruct` / `EffectiveEpiFamilyStruct` 的定义

English:
structure EffectiveEpiFamilyStruct
  parameters: {B : C} {α : Type*}
  axioms and operations (3):
    - desc : forall {W} (e : (a : α) -> (X a ⟶ W)), (forall {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂), g₁ ≫ π _ = g₂ ≫ π _ -> g₁ ≫ e _ = g₂ ≫ e _) -> (B ⟶ W)
    - fac : forall {W} (e : (a : α) -> (X a ⟶ W)) (h : forall {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂), g₁ ≫ π _ = g₂ ≫ π _ -> g₁ ≫ e _ = g₂ ≫ e _) (a : α), π a ≫ desc e h = e a
    - uniq : forall {W} (e : (a : α) -> (X a ⟶ W)) (h : forall {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂), g₁ ≫ π _ = g₂ ≫ π _ -> g₁ ≫ e _ = g₂ ≫ e _) (m : B ⟶ W), (forall (a : α), π a ≫ m = e a) -> m = desc e h

中文:
结构 EffectiveEpiFamilyStruct
  参数: {B : C} {α : 类型}
  公理与运算 (3 个):
    - desc : 对任意 {W} (e : (a : α) -> (X a ⟶ W)), (对任意 {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂), g₁ ≫ π _ = g₂ ≫ π _ -> g₁ ≫ e _ = g₂ ≫ e _) -> (B ⟶ W)
    - fac : 对任意 {W} (e : (a : α) -> (X a ⟶ W)) (h : 对任意 {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂), g₁ ≫ π _ = g₂ ≫ π _ -> g₁ ≫ e _ = g₂ ≫ e _) (a : α), π a ≫ desc e h = e a
    - uniq : 对任意 {W} (e : (a : α) -> (X a ⟶ W)) (h : 对任意 {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂), g₁ ≫ π _ = g₂ ≫ π _ -> g₁ ≫ e _ = g₂ ≫ e _) (m : B ⟶ W), (对任意 (a : α), π a ≫ m = e a) -> m = desc e h

Depends on / 依赖: createsColimitsOfShapeOfCreatesFiniteColimits
-/
structure EffectiveEpiFamilyStruct {B : C} {α : Type*}
    (X : α -> C) (π : (a : α) -> (X a ⟶ B)) where
  /--
  For every `W` with a family of morphisms `e a : Y a ⟶ W` that coequalizes every pair of morphisms
  `g₁ : Z ⟶ Y a₁`, `g₂ : Z ⟶ Y a₂` which the family `π` coequalizes, `desc e h` is a morphism
  `X ⟶ W`...
  -/
  desc : forall {W} (e : (a : α) -> (X a ⟶ W)),
      (forall {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),
      g₁ ≫ π _ = g₂ ≫ π _ -> g₁ ≫ e _ = g₂ ≫ e _) -> (B ⟶ W)
  /-- ...factorizing the components of `e` through the components of `π`... -/
  fac : forall {W} (e : (a : α) -> (X a ⟶ W))
          (h : forall {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),
            g₁ ≫ π _ = g₂ ≫ π _ -> g₁ ≫ e _ = g₂ ≫ e _)
          (a : α), π a ≫ desc e h = e a
  /-- ...and as such, unique. -/
  uniq : forall {W} (e : (a : α) -> (X a ⟶ W))
          (h : forall {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),
            g₁ ≫ π _ = g₂ ≫ π _ -> g₁ ≫ e _ = g₂ ≫ e _)
          (m : B ⟶ W), (forall (a : α), π a ≫ m = e a) -> m = desc e h

/--
Definition of `EffectiveEpiFamily` / `EffectiveEpiFamily` 的定义

English:
class EffectiveEpiFamily
  parameters: {B : C} {α : Type*} (X : α -> C) (π : (a : α) -> (X a ⟶ B))
  axioms and operations (1):
    - effectiveEpiFamily : Nonempty (EffectiveEpiFamilyStruct X π)

中文:
类 EffectiveEpiFamily
  参数: {B : C} {α : 类型} (X : α -> C) (π : (a : α) -> (X a ⟶ B))
  公理与运算 (1 个):
    - effectiveEpiFamily : Nonempty (EffectiveEpiFamilyStruct X π)
-/
class EffectiveEpiFamily {B : C} {α : Type*} (X : α -> C) (π : (a : α) -> (X a ⟶ B)) : Prop where
  /-- `π` is an effective epimorphic family if there exists an `EffectiveEpiFamilyStruct` for `π` -/
  effectiveEpiFamily : Nonempty (EffectiveEpiFamilyStruct X π)

/-- Some chosen `EffectiveEpiFamilyStruct` associated to an effective epi family. -/
noncomputable
/--
Definition of `EffectiveEpiFamily.getStruct` / `EffectiveEpiFamily.getStruct` 的定义

English:
definition EffectiveEpiFamily.getStruct
  signature: {B : C} {α : Type*} (X : α -> C) (π : (a : α) -> (X a ⟶ B))
  body: EffectiveEpiFamily.effectiveEpiFamily.some

中文:
定义 EffectiveEpiFamily.getStruct
  签名: {B : C} {α : 类型} (X : α -> C) (π : (a : α) -> (X a ⟶ B))
  定义体: EffectiveEpiFamily.effectiveEpiFamily.some

Depends on / 依赖: CreatesColimitsOfSize0, CreatesColimitsOfSize0.createsFiniteColimits, EffectiveEpiFamily, EffectiveEpiFamily.effectiveEpiFamily.some, createsFiniteColimits, effectiveEpiFamily
-/
def EffectiveEpiFamily.getStruct {B : C} {α : Type*} (X : α -> C) (π : (a : α) -> (X a ⟶ B))
    [EffectiveEpiFamily X π] : EffectiveEpiFamilyStruct X π :=
  EffectiveEpiFamily.effectiveEpiFamily.some

/-- Descend along an effective epi family. -/
noncomputable
/--
Definition of `EffectiveEpiFamily.desc` / `EffectiveEpiFamily.desc` 的定义

English:
definition EffectiveEpiFamily.desc
  signature: {B W : C} {α : Type*} (X : α -> C) (π : (a : α) -> (X a ⟶ B))
  body: (EffectiveEpiFamily.getStruct X π).desc e h

@[reassoc (attr := simp)]

中文:
定义 EffectiveEpiFamily.desc
  签名: {B W : C} {α : 类型} (X : α -> C) (π : (a : α) -> (X a ⟶ B))
  定义体: (EffectiveEpiFamily.getStruct X π).desc e h

@[reassoc (attr := simp)]

Depends on / 依赖: CreatesColimits, CreatesColimits.createsFiniteColimits, EffectiveEpiFamily, EffectiveEpiFamily.getStruct, createsFiniteColimits, getStruct
-/
def EffectiveEpiFamily.desc {B W : C} {α : Type*} (X : α -> C) (π : (a : α) -> (X a ⟶ B))
    [EffectiveEpiFamily X π] (e : (a : α) -> (X a ⟶ W))
    (h : forall {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),
      g₁ ≫ π _ = g₂ ≫ π _ -> g₁ ≫ e _ = g₂ ≫ e _) : B ⟶ W :=
  (EffectiveEpiFamily.getStruct X π).desc e h

@[reassoc (attr := simp)]
/--
lemma `EffectiveEpiFamily.fac` / 引理 `EffectiveEpiFamily.fac`

English:
lemma EffectiveEpiFamily.fac
  statement: {B W : C} {α : Type*} (X : α -> C) (π : (a : α) -> (X a ⟶ B))
  proof: (EffectiveEpiFamily.getStruct X π).fac e h a

中文:
引理 EffectiveEpiFamily.fac
  结论: {B W : C} {α : 类型} (X : α -> C) (π : (a : α) -> (X a ⟶ B))
  证明: (EffectiveEpiFamily.getStruct X π).fac e h a

Depends on / 依赖: EffectiveEpiFamily, EffectiveEpiFamily.getStruct, getStruct
-/
lemma EffectiveEpiFamily.fac {B W : C} {α : Type*} (X : α -> C) (π : (a : α) -> (X a ⟶ B))
    [EffectiveEpiFamily X π] (e : (a : α) -> (X a ⟶ W))
    (h : forall {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),
      g₁ ≫ π _ = g₂ ≫ π _ -> g₁ ≫ e _ = g₂ ≫ e _) (a : α) :
    π a ≫ EffectiveEpiFamily.desc X π e h = e a :=
  (EffectiveEpiFamily.getStruct X π).fac e h a

/--
lemma `EffectiveEpiFamily.uniq` / 引理 `EffectiveEpiFamily.uniq`

English:
lemma EffectiveEpiFamily.uniq
  statement: {B W : C} {α : Type*} (X : α -> C) (π : (a : α) -> (X a ⟶ B))
  proof: (EffectiveEpiFamily.getStruct X π).uniq e h m hm

中文:
引理 EffectiveEpiFamily.uniq
  结论: {B W : C} {α : 类型} (X : α -> C) (π : (a : α) -> (X a ⟶ B))
  证明: (EffectiveEpiFamily.getStruct X π).uniq e h m hm

Depends on / 依赖: EffectiveEpiFamily, EffectiveEpiFamily.getStruct, getStruct
-/
lemma EffectiveEpiFamily.uniq {B W : C} {α : Type*} (X : α -> C) (π : (a : α) -> (X a ⟶ B))
    [EffectiveEpiFamily X π] (e : (a : α) -> (X a ⟶ W))
    (h : forall {Z : C} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),
      g₁ ≫ π _ = g₂ ≫ π _ -> g₁ ≫ e _ = g₂ ≫ e _)
    (m : B ⟶ W) (hm : forall a, π a ≫ m = e a) :
    m = EffectiveEpiFamily.desc X π e h :=
  (EffectiveEpiFamily.getStruct X π).uniq e h m hm

-- TODO: Once we have "jointly epimorphic families", we could rephrase this as such a property.
/--
lemma `EffectiveEpiFamily.hom_ext` / 引理 `EffectiveEpiFamily.hom_ext`

English:
lemma EffectiveEpiFamily.hom_ext
  statement: {B W : C} {α : Type*} (X : α -> C) (π : (a : α) -> (X a ⟶ B))
  proof: by
  have : m₂ = EffectiveEpiFamily.desc X π (fun a => π a ≫ m₂)
      (fun a₁ a₂ g₁ g₂ h => by simp only [← assoc, h]) := by
    apply EffectiveEpiFamily.uniq; intro; rfl
  rw [this]
  exact EffectiveEpiFamily.uniq _ _ _ _ _ h

中文:
引理 EffectiveEpiFamily.hom_ext
  结论: {B W : C} {α : 类型} (X : α -> C) (π : (a : α) -> (X a ⟶ B))
  证明: by
  have : m₂ = EffectiveEpiFamily.desc X π (fun a => π a ≫ m₂)
      (fun a₁ a₂ g₁ g₂ h => by simp only [← assoc, h]) := by
    apply EffectiveEpiFamily.uniq; intro; rfl
  rw [this]
  exact EffectiveEpiFamily.uniq _ _ _ _ _ h

Depends on / 依赖: EffectiveEpiFamily, EffectiveEpiFamily.desc, EffectiveEpiFamily.uniq
-/
lemma EffectiveEpiFamily.hom_ext {B W : C} {α : Type*} (X : α -> C) (π : (a : α) -> (X a ⟶ B))
    [EffectiveEpiFamily X π] (m₁ m₂ : B ⟶ W) (h : forall a, π a ≫ m₁ = π a ≫ m₂) :
    m₁ = m₂ := by
  have : m₂ = EffectiveEpiFamily.desc X π (fun a => π a ≫ m₂)
      (fun a₁ a₂ g₁ g₂ h => by simp only [← assoc, h]) := by
    apply EffectiveEpiFamily.uniq; intro; rfl
  rw [this]
  exact EffectiveEpiFamily.uniq _ _ _ _ _ h

/--
An `EffectiveEpiFamily` consisting of a single `EffectiveEpi`
-/
noncomputable
/--
Definition of `effectiveEpiFamilyStructSingletonOfEffectiveEpi` / `effectiveEpiFamilyStructSingletonOfEffectiveEpi` 的定义

English:
definition effectiveEpiFamilyStructSingletonOfEffectiveEpi
  signature: {B X : C} (f : X ⟶ B) [EffectiveEpi f]
  body: EffectiveEpi.desc f (e ()) (fun g₁ g₂ hg => h () () g₁ g₂ hg)
  fac e h := fun _ => EffectiveEpi.fac f (e ()) (fun g₁ g₂ hg => h () () g₁ g₂ hg)
  uniq e h m hm := by apply EffectiveEpi.uniq f (e ()) (h () ()); exact hm ()

中文:
定义 effectiveEpiFamilyStructSingletonOfEffectiveEpi
  签名: {B X : C} (f : X ⟶ B) [EffectiveEpi f]
  定义体: EffectiveEpi.desc f (e ()) (fun g₁ g₂ hg => h () () g₁ g₂ hg)
  fac e h := fun _ => EffectiveEpi.fac f (e ()) (fun g₁ g₂ hg => h () () g₁ g₂ hg)
  uniq e h m hm := by apply EffectiveEpi.uniq f (e ()) (h () ()); exact hm ()

Depends on / 依赖: EffectiveEpi, EffectiveEpi.desc
-/
def effectiveEpiFamilyStructSingletonOfEffectiveEpi {B X : C} (f : X ⟶ B) [EffectiveEpi f] :
    EffectiveEpiFamilyStruct (fun () => X) (fun () => f) where
  desc e h := EffectiveEpi.desc f (e ()) (fun g₁ g₂ hg => h () () g₁ g₂ hg)
  fac e h := fun _ => EffectiveEpi.fac f (e ()) (fun g₁ g₂ hg => h () () g₁ g₂ hg)
  uniq e h m hm := by apply EffectiveEpi.uniq f (e ()) (h () ()); exact hm ()

instance {B X : C} (f : X ⟶ B) [EffectiveEpi f] : EffectiveEpiFamily (fun () => X) (fun () => f) :=
  ⟨⟨effectiveEpiFamilyStructSingletonOfEffectiveEpi f⟩⟩

/--
A single element `EffectiveEpiFamily` consists of an `EffectiveEpi`
-/
noncomputable
/--
Definition of `effectiveEpiStructOfEffectiveEpiFamilySingleton` / `effectiveEpiStructOfEffectiveEpiFamilySingleton` 的定义

English:
definition effectiveEpiStructOfEffectiveEpiFamilySingleton
  signature: {B X : C} (f : X ⟶ B)
  body: EffectiveEpiFamily.desc
    (fun () => X) (fun () => f) (fun () => e) (fun _ _ g₁ g₂ hg => h g₁ g₂ hg)
  fac e h := EffectiveEpiFamily.fac
    (fun () => X) (fun () => f) (fun () => e) (fun _ _ g₁ g₂ hg => h g₁ g₂ hg) ()
  uniq e h m hm := EffectiveEpiFamily.uniq
    (fun () => X) (fun () => f) (fun

中文:
定义 effectiveEpiStructOfEffectiveEpiFamilySingleton
  签名: {B X : C} (f : X ⟶ B)
  定义体: EffectiveEpiFamily.desc
    (fun () => X) (fun () => f) (fun () => e) (fun _ _ g₁ g₂ hg => h g₁ g₂ hg)
  fac e h := EffectiveEpiFamily.fac
    (fun () => X) (fun () => f) (fun () => e) (fun _ _ g₁ g₂ hg => h g₁ g₂ hg) ()
  uniq e h m hm := EffectiveEpiFamily.uniq
    (fun () => X) (fun () => f) (fun

Depends on / 依赖: EffectiveEpiFamily, EffectiveEpiFamily.desc, preservesFiniteColimits_of_createsFiniteColimits_and_hasFiniteColimits
-/
def effectiveEpiStructOfEffectiveEpiFamilySingleton {B X : C} (f : X ⟶ B)
    [EffectiveEpiFamily (fun () => X) (fun () => f)] :
    EffectiveEpiStruct f where
  desc e h := EffectiveEpiFamily.desc
    (fun () => X) (fun () => f) (fun () => e) (fun _ _ g₁ g₂ hg => h g₁ g₂ hg)
  fac e h := EffectiveEpiFamily.fac
    (fun () => X) (fun () => f) (fun () => e) (fun _ _ g₁ g₂ hg => h g₁ g₂ hg) ()
  uniq e h m hm := EffectiveEpiFamily.uniq
    (fun () => X) (fun () => f) (fun () => e) (fun _ _ g₁ g₂ hg => h g₁ g₂ hg) m (fun _ => hm)

instance {B X : C} (f : X ⟶ B) [EffectiveEpiFamily (fun () => X) (fun () => f)] :
    EffectiveEpi f :=
  ⟨⟨effectiveEpiStructOfEffectiveEpiFamilySingleton f⟩⟩

/--
theorem `effectiveEpi_iff_effectiveEpiFamily` / 定理 `effectiveEpi_iff_effectiveEpiFamily`

English:
theorem effectiveEpi_iff_effectiveEpiFamily
  given: {B X : C} (f : X ⟶ B)
  proof: ⟨fun _ => inferInstance, fun _ => inferInstance⟩

中文:
定理 effectiveEpi_iff_effectiveEpiFamily
  条件: {B X : C} (f : X ⟶ B)
  证明: ⟨fun _ => inferInstance, fun _ => inferInstance⟩
-/
theorem effectiveEpi_iff_effectiveEpiFamily {B X : C} (f : X ⟶ B) :
    EffectiveEpi f ↔ EffectiveEpiFamily (fun () => X) (fun () => f) :=
  ⟨fun _ => inferInstance, fun _ => inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
/--
A family of morphisms with the same target inducing an isomorphism from the coproduct to the target
is an `EffectiveEpiFamily`.
-/
noncomputable
/--
Definition of `effectiveEpiFamilyStructOfIsIsoDesc` / `effectiveEpiFamilyStructOfIsIsoDesc` 的定义

English:
definition effectiveEpiFamilyStructOfIsIsoDesc
  signature: {B : C} {α : Type*} (X : α -> C)
  body: (asIso (Sigma.desc π)).inv ≫ (Sigma.desc e)
  fac e h := by
    intro a
    have : π a = Sigma.ι X a ≫ (asIso (Sigma.desc π)).hom := by simp only [asIso_hom,
      colimit.ι_desc, Cofan.mk_ι_app]
    rw [this]; rw [assoc]
    simp only [asIso_hom, asIso_inv, IsIso.hom_inv_id_assoc, colimit.ι_desc,
 

中文:
定义 effectiveEpiFamilyStructOfIsIsoDesc
  签名: {B : C} {α : 类型} (X : α -> C)
  定义体: (asIso (Sigma.desc π)).inv ≫ (Sigma.desc e)
  fac e h := by
    intro a
    have : π a = Sigma.ι X a ≫ (asIso (Sigma.desc π)).hom := by simp only [asIso_hom,
      colimit.ι_desc, Cofan.mk_ι_app]
    rw [this]; rw [assoc]
    simp only [asIso_hom, asIso_inv, IsIso.hom_inv_id_assoc, colimit.ι_desc,
 

Depends on / 依赖: Sigma.desc, createsColimitsOfShapeOfCreatesFiniteProducts
-/
def effectiveEpiFamilyStructOfIsIsoDesc {B : C} {α : Type*} (X : α -> C)
    (π : (a : α) -> (X a ⟶ B)) [HasCoproduct X] [IsIso (Sigma.desc π)] :
    EffectiveEpiFamilyStruct X π where
  desc e _ := (asIso (Sigma.desc π)).inv ≫ (Sigma.desc e)
  fac e h := by
    intro a
    have : π a = Sigma.ι X a ≫ (asIso (Sigma.desc π)).hom := by simp only [asIso_hom,
      colimit.ι_desc, Cofan.mk_ι_app]
    rw [this]; rw [assoc]
    simp only [asIso_hom, asIso_inv, IsIso.hom_inv_id_assoc, colimit.ι_desc,
      Cofan.mk_ι_app]
  uniq e h m hm := by
    simp only [asIso_inv, IsIso.eq_inv_comp]
    ext a
    simp only [colimit.ι_desc_assoc, Discrete.functor_obj, Cofan.mk_ι_app,
      colimit.ι_desc]
    exact hm a

instance {B : C} {α : Type*} (X : α -> C) (π : (a : α) -> (X a ⟶ B)) [HasCoproduct X]
    [IsIso (Sigma.desc π)] : EffectiveEpiFamily X π :=
  ⟨⟨effectiveEpiFamilyStructOfIsIsoDesc X π⟩⟩

/-- Any isomorphism is an effective epi. -/
noncomputable
/--
Definition of `effectiveEpiStructOfIsIso` / `effectiveEpiStructOfIsIso` 的定义

English:
definition effectiveEpiStructOfIsIso
  signature: {X Y : C} (f : X ⟶ Y) [IsIso f]
  body: inv f ≫ e
  fac _ _ := by simp
  uniq _ _ _ h := by simpa using h

中文:
定义 effectiveEpiStructOfIsIso
  签名: {X Y : C} (f : X ⟶ Y) [IsIso f]
  定义体: inv f ≫ e
  fac _ _ := by simp
  uniq _ _ _ h := by simpa using h
-/
def effectiveEpiStructOfIsIso {X Y : C} (f : X ⟶ Y) [IsIso f] : EffectiveEpiStruct f where
  desc e _ := inv f ≫ e
  fac _ _ := by simp
  uniq _ _ _ h := by simpa using h

instance {X Y : C} (f : X ⟶ Y) [IsIso f] : EffectiveEpi f := ⟨⟨effectiveEpiStructOfIsIso f⟩⟩

example {X : C} : EffectiveEpiFamily (fun _ => X : Unit -> C) (fun _ => 𝟙 X) := inferInstance

/--
Definition of `EffectiveEpiFamilyStruct.reindex` / `EffectiveEpiFamilyStruct.reindex` 的定义

English:
definition EffectiveEpiFamilyStruct.reindex
  body: fun f h => P.desc (fun _ => f _) (fun _ _ => h _ _)
  fac _ _ a := by
    obtain ⟨a, rfl⟩ := e.surjective a
    apply P.fac
  uniq _ _ _ hm := P.uniq _ _ _ fun _ => hm _

中文:
定义 EffectiveEpiFamilyStruct.reindex
  定义体: fun f h => P.desc (fun _ => f _) (fun _ _ => h _ _)
  fac _ _ a := by
    obtain ⟨a, rfl⟩ := e.surjective a
    apply P.fac
  uniq _ _ _ hm := P.uniq _ _ _ fun _ => hm _

Depends on / 依赖: P.desc
-/
def EffectiveEpiFamilyStruct.reindex
    {B : C} {α α' : Type*}
    (X : α -> C)
    (π : (a : α) -> (X a ⟶ B))
    (e : α' ≃ α)
    (P : EffectiveEpiFamilyStruct (fun a => X (e a)) (fun a => π (e a))) :
    EffectiveEpiFamilyStruct X π where
  desc := fun f h => P.desc (fun _ => f _) (fun _ _ => h _ _)
  fac _ _ a := by
    obtain ⟨a, rfl⟩ := e.surjective a
    apply P.fac
  uniq _ _ _ hm := P.uniq _ _ _ fun _ => hm _

/--
lemma `EffectiveEpiFamily.reindex` / 引理 `EffectiveEpiFamily.reindex`

English:
lemma EffectiveEpiFamily.reindex
  proof: .mk .intro .reindex _ _ e @EffectiveEpiFamily.getStruct _ _ _ _ _ _ h

中文:
引理 EffectiveEpiFamily.reindex
  证明: .mk .intro .reindex _ _ e @EffectiveEpiFamily.getStruct _ _ _ _ _ _ h

Depends on / 依赖: EffectiveEpiFamily, EffectiveEpiFamily.getStruct, getStruct, reindex
-/
lemma EffectiveEpiFamily.reindex
    {B : C} {α α' : Type*}
    (X : α -> C)
    (π : (a : α) -> (X a ⟶ B))
    (e : α' ≃ α)
    (h : EffectiveEpiFamily (fun a => X (e a)) (fun a => π (e a))) :
    EffectiveEpiFamily X π :=
.mk .intro .reindex _ _ e @EffectiveEpiFamily.getStruct _ _ _ _ _ _ h

end CategoryTheory
