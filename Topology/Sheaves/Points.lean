/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Conservative
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sets.Opens

/-!
# The standard conservative family of points for the site attached to a topological space

If `X` is a topological space, any `x : X` defines a point of the site
attached to `X`.

## TODO

* Redefine the stalks functors in `Mathlib/Topology/Sheaves/Stalks.lean`
  using `GrothendieckTopology.Point.presheafFiber`.

-/

@[expose] public section

universe u

namespace Opens

open CategoryTheory GrothendieckTopology TopologicalSpace

variable {X : Type u} [TopologicalSpace X] (x : X)

/--
Definition of `pointGrothendieckTopology` / `pointGrothendieckTopology` 的定义

English:
definition pointGrothendieckTopology
  signature: : Point.{u} (grothendieckTopology X) where
  body: ULift.{u} (PLift (x in U))
  fiber.map f := ↾fun h => ⟨⟨leOfHom f h.down.down⟩⟩
  isCofiltered :=
    { nonempty := ⟨⊤, ⟨⟨by simp⟩⟩⟩
      cone_objs := by
        rintro ⟨U, ⟨⟨hU⟩⟩⟩ ⟨V, ⟨⟨hV⟩⟩⟩
        exact ⟨⟨U ⊓ V, ⟨⟨⟨hU, hV⟩⟩⟩⟩, ⟨homOfLE (by simp), rfl⟩,
          ⟨homOfLE (by simp), rfl⟩, ⟨⟩⟩
  

中文:
定义 pointGrothendieckTopology
  签名: : Point.{u} (grothendieckTopology X) where
  定义体: ULift.{u} (PLift (x in U))
  fiber.map f := ↾fun h => ⟨⟨leOfHom f h.down.down⟩⟩
  isCofiltered :=
    { nonempty := ⟨⊤, ⟨⟨by simp⟩⟩⟩
      cone_objs := by
        rintro ⟨U, ⟨⟨hU⟩⟩⟩ ⟨V, ⟨⟨hV⟩⟩⟩
        exact ⟨⟨U ⊓ V, ⟨⟨⟨hU, hV⟩⟩⟩⟩, ⟨homOfLE (by simp), rfl⟩,
          ⟨homOfLE (by simp), rfl⟩, ⟨⟩⟩
  
-/
def pointGrothendieckTopology : Point.{u} (grothendieckTopology X) where
  fiber.obj U := ULift.{u} (PLift (x in U))
  fiber.map f := ↾fun h => ⟨⟨leOfHom f h.down.down⟩⟩
  isCofiltered :=
    { nonempty := ⟨⊤, ⟨⟨by simp⟩⟩⟩
      cone_objs := by
        rintro ⟨U, ⟨⟨hU⟩⟩⟩ ⟨V, ⟨⟨hV⟩⟩⟩
        exact ⟨⟨U ⊓ V, ⟨⟨⟨hU, hV⟩⟩⟩⟩, ⟨homOfLE (by simp), rfl⟩,
          ⟨homOfLE (by simp), rfl⟩, ⟨⟩⟩
      cone_maps _ _ _ _ := ⟨_, 𝟙 _, rfl⟩ }
  initiallySmall := initiallySmall_of_essentiallySmall _
  jointly_surjective := by
    rintro U R hR ⟨⟨hU⟩⟩
    obtain ⟨V, f, hf, hV⟩ := hR x hU
    exact ⟨_, _, hf, ⟨⟨hV⟩⟩, rfl⟩

variable (X) in
/--
Definition of `pointsGrothendieckTopology` / `pointsGrothendieckTopology` 的定义

English:
definition pointsGrothendieckTopology
  signature: : ObjectProperty (Point.{u} (grothendieckTopology X))
  body: ObjectProperty.ofObj pointGrothendieckTopology
  deriving ObjectProperty.Small.{u}

中文:
定义 pointsGrothendieckTopology
  签名: : ObjectProperty (Point.{u} (grothendieckTopology X))
  定义体: ObjectProperty.ofObj pointGrothendieckTopology
  deriving ObjectProperty.Small.{u}

Depends on / 依赖: ObjectProperty, ObjectProperty.ofObj, pointGrothendieckTopology
-/
def pointsGrothendieckTopology : ObjectProperty (Point.{u} (grothendieckTopology X)) :=
  ObjectProperty.ofObj pointGrothendieckTopology
  deriving ObjectProperty.Small.{u}

variable (X) in
/--
lemma `isConservativeFamilyOfPoints_pointsGrothendieckTopology` / 引理 `isConservativeFamilyOfPoints_pointsGrothendieckTopology`

English:
lemma isConservativeFamilyOfPoints_pointsGrothendieckTopology
  proof: .mk' (fun U S hS x hx => by
    obtain ⟨V, f, hf, ⟨⟨hV⟩⟩, _⟩ := hS ⟨_, ⟨x⟩⟩ ⟨⟨hx⟩⟩
    exact ⟨V, f, hf, hV⟩)

中文:
引理 isConservativeFamilyOfPoints_pointsGrothendieckTopology
  证明: .mk' (fun U S hS x hx => by
    obtain ⟨V, f, hf, ⟨⟨hV⟩⟩, _⟩ := hS ⟨_, ⟨x⟩⟩ ⟨⟨hx⟩⟩
    exact ⟨V, f, hf, hV⟩)
-/
lemma isConservativeFamilyOfPoints_pointsGrothendieckTopology :
    (pointsGrothendieckTopology X).IsConservativeFamilyOfPoints :=
  .mk' (fun U S hS x hx => by
    obtain ⟨V, f, hf, ⟨⟨hV⟩⟩, _⟩ := hS ⟨_, ⟨x⟩⟩ ⟨⟨hx⟩⟩
    exact ⟨V, f, hf, hV⟩)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasEnoughPoints.{u} (grothendieckTopology X)
  body: ⟨_, inferInstance, isConservativeFamilyOfPoints_pointsGrothendieckTopology X⟩

中文:
实例 :
  签名: 有EnoughPoints.{u} (grothendieckTopology X)
  定义体: ⟨_, inferInstance, isConservativeFamilyOfPoints_pointsGrothendieckTopology X⟩

Depends on / 依赖: isConservativeFamilyOfPoints_pointsGrothendieckTopology
-/
instance : HasEnoughPoints.{u} (grothendieckTopology X) where
  exists_objectProperty :=
    ⟨_, inferInstance, isConservativeFamilyOfPoints_pointsGrothendieckTopology X⟩

instance (U : Opens X) (Φ : Point.{u} (grothendieckTopology X)) :
    Subsingleton (Φ.fiber.obj U) :=
  Φ.subsingleton_fiber_obj (homOfLE le_top) Limits.isTerminalTop

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Quiver.IsThin (Point.{u} (grothendieckTopology X))
  body: fun _ _ => ⟨fun _ _ => by ext; subsingleton⟩

中文:
实例 :
  签名: 箭图.IsThin (Point.{u} (grothendieckTopology X))
  定义体: fun _ _ => ⟨fun _ _ => by ext; subsingleton⟩

Depends on / 依赖: subsingleton
-/
instance : Quiver.IsThin (Point.{u} (grothendieckTopology X)) :=
  fun _ _ => ⟨fun _ _ => by ext; subsingleton⟩

/--
Definition of `pointGrothendieckTopologyHomEquiv` / `pointGrothendieckTopologyHomEquiv` 的定义

English:
definition pointGrothendieckTopologyHomEquiv
  signature: {x y : X}
  body: specializes_iff_forall_open.2 (fun U h₁ h₂ => (f.hom.app ⟨U, h₁⟩ ⟨⟨h₂⟩⟩).down.down)
  invFun s := { hom.app U := ↾fun hU =>
    ⟨⟨specializes_iff_forall_open.1 s _ U.2 hU.down.down⟩⟩ }
  left_inv _ := by subsingleton
  right_inv _ := rfl

中文:
定义 pointGrothendieckTopologyHomEquiv
  签名: {x y : X}
  定义体: specializes_iff_forall_open.2 (fun U h₁ h₂ => (f.hom.app ⟨U, h₁⟩ ⟨⟨h₂⟩⟩).down.down)
  invFun s := { hom.app U := ↾fun hU =>
    ⟨⟨specializes_iff_forall_open.1 s _ U.2 hU.down.down⟩⟩ }
  left_inv _ := by subsingleton
  right_inv _ := rfl

Depends on / 依赖: down.down, f.hom.app, specializes_iff_forall_open
-/
def pointGrothendieckTopologyHomEquiv {x y : X} :
    (pointGrothendieckTopology x ⟶ pointGrothendieckTopology y) ≃ x ⤳ y where
  toFun f := specializes_iff_forall_open.2 (fun U h₁ h₂ => (f.hom.app ⟨U, h₁⟩ ⟨⟨h₂⟩⟩).down.down)
  invFun s := { hom.app U := ↾fun hU =>
    ⟨⟨specializes_iff_forall_open.1 s _ U.2 hU.down.down⟩⟩ }
  left_inv _ := by subsingleton
  right_inv _ := rfl

end Opens
