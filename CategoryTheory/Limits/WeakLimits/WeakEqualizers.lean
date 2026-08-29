/-
Copyright (c) 2026 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
module

public import Mathlib.CategoryTheory.Limits.WeakLimits.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Weak equalizers

These are weak limits for diagrams of shape `WalkingParallelPair`.

-/

@[expose] public section

universe u v w

noncomputable section

open CategoryTheory Category Limits

variable {C : Type*} [Category* C]

namespace CategoryTheory.Limits

variable {X Y : C} (f g : X ⟶ Y)

/--
Definition of `HasWeakEqualizer` / `HasWeakEqualizer` 的定义

English:
abbreviation HasWeakEqualizer
  body: HasWeakLimit (parallelPair f g)

中文:
缩写 HasWeakEqualizer
  定义体: HasWeakLimit (parallelPair f g)

Depends on / 依赖: HasWeakLimit, parallelPair
-/
abbrev HasWeakEqualizer :=
  HasWeakLimit (parallelPair f g)

variable [HasWeakEqualizer f g]

/--
Definition of `weakEqualizer` / `weakEqualizer` 的定义

English:
abbreviation weakEqualizer
  signature: : C
  body: weakLimit (parallelPair f g)

中文:
缩写 weakEqualizer
  签名: : C
  定义体: weakLimit (parallelPair f g)

Depends on / 依赖: parallelPair, weakLimit
-/
noncomputable abbrev weakEqualizer : C :=
  weakLimit (parallelPair f g)

/--
Definition of `weakEqualizer.ι` / `weakEqualizer.ι` 的定义

English:
abbreviation weakEqualizer.ι
  signature: : weakEqualizer f g ⟶ X
  body: weakLimit.π (parallelPair f g) WalkingParallelPair.zero

中文:
缩写 weakEqualizer.ι
  签名: : weakEqualizer f g ⟶ X
  定义体: weakLimit.π (parallelPair f g) WalkingParallelPair.zero

Depends on / 依赖: WalkingParallelPair, WalkingParallelPair.zero, parallelPair, weakLimit
-/
noncomputable abbrev weakEqualizer.ι : weakEqualizer f g ⟶ X :=
  weakLimit.π (parallelPair f g) WalkingParallelPair.zero

/--
Definition of `weakEqualizer.fork` / `weakEqualizer.fork` 的定义

English:
abbreviation weakEqualizer.fork
  signature: : Fork f g
  body: weakLimit.cone (parallelPair f g)

@[simp]

中文:
缩写 weakEqualizer.fork
  签名: : 叉 f g
  定义体: weakLimit.cone (parallelPair f g)

@[simp]

Depends on / 依赖: parallelPair, weakLimit, weakLimit.cone
-/
noncomputable abbrev weakEqualizer.fork : Fork f g :=
  weakLimit.cone (parallelPair f g)

@[simp]
/--
theorem `weakEqualizer.fork_ι` / 定理 `weakEqualizer.fork_ι`

English:
theorem weakEqualizer.fork_ι
  statement: (weakEqualizer.fork f g).ι = weakEqualizer.ι f g
  proof: rfl

@[simp]

中文:
定理 weakEqualizer.fork_ι
  结论: (weakEqualizer.fork f g).ι = weakEqualizer.ι f g
  证明: rfl

@[simp]
-/
theorem weakEqualizer.fork_ι : (weakEqualizer.fork f g).ι = weakEqualizer.ι f g :=
  rfl

@[simp]
/--
theorem `weakEqualizer.fork_π_app_zero` / 定理 `weakEqualizer.fork_π_app_zero`

English:
theorem weakEqualizer.fork_π_app_zero
  proof: rfl

@[reassoc]

中文:
定理 weakEqualizer.fork_π_app_zero
  证明: rfl

@[reassoc]
-/
theorem weakEqualizer.fork_π_app_zero :
    (weakEqualizer.fork f g).π.app WalkingParallelPair.zero = weakEqualizer.ι f g :=
  rfl

@[reassoc]
/--
theorem `weakEqualizer.condition` / 定理 `weakEqualizer.condition`

English:
theorem weakEqualizer.condition
  statement: weakEqualizer.ι f g ≫ f = weakEqualizer.ι f g ≫ g
  proof: Fork.condition weakLimit.cone parallelPair f g

中文:
定理 weakEqualizer.condition
  结论: weakEqualizer.ι f g ≫ f = weakEqualizer.ι f g ≫ g
  证明: Fork.condition weakLimit.cone parallelPair f g

Depends on / 依赖: Fork.condition, condition, parallelPair, weakLimit, weakLimit.cone
-/
theorem weakEqualizer.condition : weakEqualizer.ι f g ≫ f = weakEqualizer.ι f g ≫ g :=
Fork.condition weakLimit.cone parallelPair f g

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `weakEqualizerIsWeakEqualizer` / `weakEqualizerIsWeakEqualizer` 的定义

English:
definition weakEqualizerIsWeakEqualizer
  signature: : IsWeakLimit (Fork.ofι (weakEqualizer.ι f g)
  body: IsWeakLimit.ofIsoWeakLimit (weakLimit.isWeakLimit _) (Fork.ext (Iso.refl _) (by simp))

中文:
定义 weakEqualizerIsWeakEqualizer
  签名: : 是WeakLimit (叉.ofι (weakEqualizer.ι f g)
  定义体: IsWeakLimit.ofIsoWeakLimit (weakLimit.isWeakLimit _) (Fork.ext (Iso.refl _) (by simp))

Depends on / 依赖: Fork.ext, IsWeakLimit, IsWeakLimit.ofIsoWeakLimit, Iso.refl, isWeakLimit, ofIsoWeakLimit, weakLimit, weakLimit.isWeakLimit
-/
def weakEqualizerIsWeakEqualizer : IsWeakLimit (Fork.ofι (weakEqualizer.ι f g)
    (weakEqualizer.condition f g)) :=
  IsWeakLimit.ofIsoWeakLimit (weakLimit.isWeakLimit _) (Fork.ext (Iso.refl _) (by simp))

variable {f g}

/--
Definition of `weakEqualizer.lift` / `weakEqualizer.lift` 的定义

English:
abbreviation weakEqualizer.lift
  signature: {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g)
  body: weakLimit.lift (parallelPair f g) (Fork.ofι k h)

@[reassoc]

中文:
缩写 weakEqualizer.lift
  签名: {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g)
  定义体: weakLimit.lift (parallelPair f g) (Fork.ofι k h)

@[reassoc]

Depends on / 依赖: Fork.of, parallelPair, weakLimit, weakLimit.lift
-/
noncomputable abbrev weakEqualizer.lift {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) :
    W ⟶ weakEqualizer f g :=
  weakLimit.lift (parallelPair f g) (Fork.ofι k h)

@[reassoc]
/--
theorem `weakEqualizer.lift_ι` / 定理 `weakEqualizer.lift_ι`

English:
theorem weakEqualizer.lift_ι
  given: {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g)
  proof: weakLimit.lift_π _ _

中文:
定理 weakEqualizer.lift_ι
  条件: {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g)
  证明: weakLimit.lift_π _ _

Depends on / 依赖: weakLimit, weakLimit.lift_
-/
theorem weakEqualizer.lift_ι {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) :
    weakEqualizer.lift k h ≫ weakEqualizer.ι f g = k :=
  weakLimit.lift_π _ _

/--
Definition of `weakEqualizer.lift'` / `weakEqualizer.lift'` 的定义

English:
definition weakEqualizer.lift'
  signature: {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g)
  body: ⟨weakEqualizer.lift k h, weakEqualizer.lift_ι _ _⟩

中文:
定义 weakEqualizer.lift'
  签名: {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g)
  定义体: ⟨weakEqualizer.lift k h, weakEqualizer.lift_ι _ _⟩

Depends on / 依赖: weakEqualizer, weakEqualizer.lift, weakEqualizer.lift_
-/
def weakEqualizer.lift' {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) :
    { l : W ⟶ weakEqualizer f g // l ≫ weakEqualizer.ι f g = k } :=
  ⟨weakEqualizer.lift k h, weakEqualizer.lift_ι _ _⟩

variable (C)

/--
Definition of `HasWeakEqualizers` / `HasWeakEqualizers` 的定义

English:
abbreviation HasWeakEqualizers
  body: HasWeakLimitsOfShape WalkingParallelPair C

中文:
缩写 HasWeakEqualizers
  定义体: HasWeakLimitsOfShape WalkingParallelPair C

Depends on / 依赖: HasWeakLimitsOfShape, WalkingParallelPair
-/
abbrev HasWeakEqualizers :=
  HasWeakLimitsOfShape WalkingParallelPair C

/-- A category with equalizers has weak equalizers. -/
instance (priority := 100) HasWeakEqualizersOfHasEqualizers [HasEqualizers C] :
    HasWeakEqualizers C where

/--
theorem `hasWeakEqualizers_of_hasWeakLimit_parallelPair` / 定理 `hasWeakEqualizers_of_hasWeakLimit_parallelPair`

English:
theorem hasWeakEqualizers_of_hasWeakLimit_parallelPair
  proof: hasWeakLimit_of_iso (diagramIsoParallelPair F).symm

中文:
定理 hasWeakEqualizers_of_hasWeakLimit_parallelPair
  证明: hasWeakLimit_of_iso (diagramIsoParallelPair F).symm

Depends on / 依赖: diagramIsoParallelPair, hasWeakLimit_of_iso
-/
theorem hasWeakEqualizers_of_hasWeakLimit_parallelPair
    [forall {X Y : C} {f g : X ⟶ Y}, HasWeakLimit (parallelPair f g)] : HasWeakEqualizers C where
      hasWeakLimit F := hasWeakLimit_of_iso (diagramIsoParallelPair F).symm

variable {C}

/-- This is a slightly more convenient method to verify that a fork is a weak limit cone. It
only asks for a proof of facts that carry any mathematical content -/
@[simps]
/--
Definition of `Fork.IsWeakLimit.mk` / `Fork.IsWeakLimit.mk` 的定义

English:
definition Fork.IsWeakLimit.mk
  signature: (t : Fork f g) (lift : forall s : Fork f g, s.pt ⟶ t.pt)
  body: { lift
    fac s j :=
WalkingParallelPair.casesOn j (fac s) by
        simp [← Category.assoc, fac] }

中文:
定义 叉.是WeakLimit.mk
  签名: (t : 叉 f g) (lift : 对任意 s : 叉 f g, s.pt ⟶ t.pt)
  定义体: { lift
    fac s j :=
WalkingParallelPair.casesOn j (fac s) by
        simp [← Category.assoc, fac] }

Depends on / 依赖: Category, Category.assoc, WalkingParallelPair, WalkingParallelPair.casesOn, casesOn
-/
def Fork.IsWeakLimit.mk (t : Fork f g) (lift : forall s : Fork f g, s.pt ⟶ t.pt)
    (fac : forall s : Fork f g, lift s ≫ Fork.ι t = Fork.ι s) : IsWeakLimit t :=
  { lift
    fac s j :=
WalkingParallelPair.casesOn j (fac s) by
        simp [← Category.assoc, fac] }

/--
Definition of `Fork.IsWeakLimit.mk'` / `Fork.IsWeakLimit.mk'` 的定义

English:
definition Fork.IsWeakLimit.mk'
  signature: {X Y : C} {f g : X ⟶ Y} (t : Fork f g)
  body: Fork.IsWeakLimit.mk t (fun s => (create s).1) (fun s => (create s).2)

中文:
定义 叉.是WeakLimit.mk'
  签名: {X Y : C} {f g : X ⟶ Y} (t : 叉 f g)
  定义体: Fork.IsWeakLimit.mk t (fun s => (create s).1) (fun s => (create s).2)

Depends on / 依赖: Fork.IsWeakLimit.mk, IsWeakLimit, create
-/
def Fork.IsWeakLimit.mk' {X Y : C} {f g : X ⟶ Y} (t : Fork f g)
    (create : forall s : Fork f g, { l // l ≫ t.ι = s.ι}) :
    IsWeakLimit t :=
  Fork.IsWeakLimit.mk t (fun s => (create s).1) (fun s => (create s).2)

end CategoryTheory.Limits
