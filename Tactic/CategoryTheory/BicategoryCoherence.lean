/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module

public import Mathlib.CategoryTheory.Bicategory.Free
public import Mathlib.Tactic.CategoryTheory.BicategoricalComp

/-!
# A `coherence` tactic for bicategories

We provide a `bicategory_coherence` tactic,
which proves that any two 2-morphisms (with the same source and target)
in a bicategory which are built out of associators and unitors
are equal.

This file mainly deals with the type class setup for the coherence tactic. The actual front end
tactic is given in `Mathlib/Tactic/CategoryTheory/Coherence.lean` at the same time as the coherence
tactic for monoidal categories.
-/

public section

noncomputable section

universe w v u

open CategoryTheory CategoryTheory.FreeBicategory

open scoped Bicategory

variable {B : Type u} [Bicategory.{w, v} B] {a b c d : B}

namespace Mathlib.Tactic.BicategoryCoherence

/--
Definition of `LiftHom` / `LiftHom` 的定义

English:
class LiftHom
  parameters: {a b : B} (f : a ⟶ b)
  axioms and operations (1):
    - lift : of.obj a ⟶ of.obj b

中文:
类 Lift态射
  参数: {a b : B} (f : a ⟶ b)
  公理与运算 (1 个):
    - lift : of.obj a ⟶ of.obj b
-/
class LiftHom {a b : B} (f : a ⟶ b) where
  /-- A lift of a morphism to the free bicategory.
  This should only exist for "structural" morphisms. -/
  lift : of.obj a ⟶ of.obj b

/--
Instance `liftHomId` / 实例 `liftHomId`

English:
instance liftHomId
  signature: : LiftHom (𝟙 a) where lift
  body: 𝟙 (of.obj a)

中文:
实例 liftHomId
  签名: : Lift态射 (𝟙 a) where lift
  定义体: 𝟙 (of.obj a)

Depends on / 依赖: of.obj
-/
instance liftHomId : LiftHom (𝟙 a) where lift := 𝟙 (of.obj a)

/--
Instance `liftHomComp` / 实例 `liftHomComp`

English:
instance liftHomComp
  signature: (f : a ⟶ b) (g : b ⟶ c) [LiftHom f] [LiftHom g]
  body: LiftHom.lift f ≫ LiftHom.lift g

中文:
实例 liftHomComp
  签名: (f : a ⟶ b) (g : b ⟶ c) [Lift态射 f] [Lift态射 g]
  定义体: LiftHom.lift f ≫ LiftHom.lift g

Depends on / 依赖: LiftHom, LiftHom.lift
-/
instance liftHomComp (f : a ⟶ b) (g : b ⟶ c) [LiftHom f] [LiftHom g] : LiftHom (f ≫ g) where
  lift := LiftHom.lift f ≫ LiftHom.lift g

instance (priority := 100) liftHomOf (f : a ⟶ b) : LiftHom f where lift := of.map f

/--
Definition of `LiftHom₂` / `LiftHom₂` 的定义

English:
class LiftHom₂
  parameters: {f g : a ⟶ b} [LiftHom f] [LiftHom g] (η : f ⟶ g)
  axioms and operations (1):
    - lift : LiftHom.lift f ⟶ LiftHom.lift g

中文:
类 LiftHom₂
  参数: {f g : a ⟶ b} [Lift态射 f] [Lift态射 g] (η : f ⟶ g)
  公理与运算 (1 个):
    - lift : Lift态射.lift f ⟶ Lift态射.lift g
-/
class LiftHom₂ {f g : a ⟶ b} [LiftHom f] [LiftHom g] (η : f ⟶ g) where
  /-- A lift of a 2-morphism to the free bicategory.
  This should only exist for "structural" 2-morphisms. -/
  lift : LiftHom.lift f ⟶ LiftHom.lift g

/--
Instance `liftHom₂Id` / 实例 `liftHom₂Id`

English:
instance liftHom₂Id
  signature: (f : a ⟶ b) [LiftHom f]
  body: 𝟙 _

中文:
实例 liftHom₂Id
  签名: (f : a ⟶ b) [Lift态射 f]
  定义体: 𝟙 _
-/
instance liftHom₂Id (f : a ⟶ b) [LiftHom f] : LiftHom₂ (𝟙 f) where
  lift := 𝟙 _

/--
Instance `liftHom₂LeftUnitorHom` / 实例 `liftHom₂LeftUnitorHom`

English:
instance liftHom₂LeftUnitorHom
  signature: (f : a ⟶ b) [LiftHom f]
  body: (fun_ (LiftHom.lift f)).hom

中文:
实例 liftHom₂LeftUnitorHom
  签名: (f : a ⟶ b) [Lift态射 f]
  定义体: (fun_ (LiftHom.lift f)).hom

Depends on / 依赖: LiftHom, LiftHom.lift, fun_
-/
instance liftHom₂LeftUnitorHom (f : a ⟶ b) [LiftHom f] : LiftHom₂ (fun_ f).hom where
  lift := (fun_ (LiftHom.lift f)).hom

/--
Instance `liftHom₂LeftUnitorInv` / 实例 `liftHom₂LeftUnitorInv`

English:
instance liftHom₂LeftUnitorInv
  signature: (f : a ⟶ b) [LiftHom f]
  body: (fun_ (LiftHom.lift f)).inv

中文:
实例 liftHom₂LeftUnitorInv
  签名: (f : a ⟶ b) [Lift态射 f]
  定义体: (fun_ (LiftHom.lift f)).inv

Depends on / 依赖: LiftHom, LiftHom.lift, fun_
-/
instance liftHom₂LeftUnitorInv (f : a ⟶ b) [LiftHom f] : LiftHom₂ (fun_ f).inv where
  lift := (fun_ (LiftHom.lift f)).inv

/--
Instance `liftHom₂RightUnitorHom` / 实例 `liftHom₂RightUnitorHom`

English:
instance liftHom₂RightUnitorHom
  signature: (f : a ⟶ b) [LiftHom f]
  body: (ρ_ (LiftHom.lift f)).hom

中文:
实例 liftHom₂RightUnitorHom
  签名: (f : a ⟶ b) [Lift态射 f]
  定义体: (ρ_ (LiftHom.lift f)).hom

Depends on / 依赖: LiftHom, LiftHom.lift
-/
instance liftHom₂RightUnitorHom (f : a ⟶ b) [LiftHom f] : LiftHom₂ (ρ_ f).hom where
  lift := (ρ_ (LiftHom.lift f)).hom

/--
Instance `liftHom₂RightUnitorInv` / 实例 `liftHom₂RightUnitorInv`

English:
instance liftHom₂RightUnitorInv
  signature: (f : a ⟶ b) [LiftHom f]
  body: (ρ_ (LiftHom.lift f)).inv

中文:
实例 liftHom₂RightUnitorInv
  签名: (f : a ⟶ b) [Lift态射 f]
  定义体: (ρ_ (LiftHom.lift f)).inv

Depends on / 依赖: LiftHom, LiftHom.lift
-/
instance liftHom₂RightUnitorInv (f : a ⟶ b) [LiftHom f] : LiftHom₂ (ρ_ f).inv where
  lift := (ρ_ (LiftHom.lift f)).inv

/--
Instance `liftHom₂AssociatorHom` / 实例 `liftHom₂AssociatorHom`

English:
instance liftHom₂AssociatorHom
  signature: (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) [LiftHom f] [LiftHom g]
  body: (α_ (LiftHom.lift f) (LiftHom.lift g) (LiftHom.lift h)).hom

中文:
实例 liftHom₂AssociatorHom
  签名: (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) [Lift态射 f] [Lift态射 g]
  定义体: (α_ (LiftHom.lift f) (LiftHom.lift g) (LiftHom.lift h)).hom

Depends on / 依赖: EqOnSource, LiftHom, LiftHom.lift, PartialEquiv, PartialEquiv.EqOnSource.symm
-/
instance liftHom₂AssociatorHom (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) [LiftHom f] [LiftHom g]
    [LiftHom h] : LiftHom₂ (α_ f g h).hom where
  lift := (α_ (LiftHom.lift f) (LiftHom.lift g) (LiftHom.lift h)).hom

/--
Instance `liftHom₂AssociatorInv` / 实例 `liftHom₂AssociatorInv`

English:
instance liftHom₂AssociatorInv
  signature: (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) [LiftHom f] [LiftHom g]
  body: (α_ (LiftHom.lift f) (LiftHom.lift g) (LiftHom.lift h)).inv

中文:
实例 liftHom₂AssociatorInv
  签名: (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) [Lift态射 f] [Lift态射 g]
  定义体: (α_ (LiftHom.lift f) (LiftHom.lift g) (LiftHom.lift h)).inv

Depends on / 依赖: LiftHom, LiftHom.lift
-/
instance liftHom₂AssociatorInv (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) [LiftHom f] [LiftHom g]
    [LiftHom h] : LiftHom₂ (α_ f g h).inv where
  lift := (α_ (LiftHom.lift f) (LiftHom.lift g) (LiftHom.lift h)).inv

/--
Instance `liftHom₂Comp` / 实例 `liftHom₂Comp`

English:
instance liftHom₂Comp
  signature: {f g h : a ⟶ b} [LiftHom f] [LiftHom g] [LiftHom h] (η : f ⟶ g) (θ : g ⟶ h)
  body: LiftHom₂.lift η ≫ LiftHom₂.lift θ

中文:
实例 liftHom₂Comp
  签名: {f g h : a ⟶ b} [Lift态射 f] [Lift态射 g] [Lift态射 h] (η : f ⟶ g) (θ : g ⟶ h)
  定义体: LiftHom₂.lift η ≫ LiftHom₂.lift θ

Depends on / 依赖: h.symm
-/
instance liftHom₂Comp {f g h : a ⟶ b} [LiftHom f] [LiftHom g] [LiftHom h] (η : f ⟶ g) (θ : g ⟶ h)
    [LiftHom₂ η] [LiftHom₂ θ] : LiftHom₂ (η ≫ θ) where
  lift := LiftHom₂.lift η ≫ LiftHom₂.lift θ

/--
Instance `liftHom₂WhiskerLeft` / 实例 `liftHom₂WhiskerLeft`

English:
instance liftHom₂WhiskerLeft
  signature: (f : a ⟶ b) [LiftHom f] {g h : b ⟶ c} (η : g ⟶ h) [LiftHom g]
  body: LiftHom.lift f ◁ LiftHom₂.lift η

中文:
实例 liftHom₂WhiskerLeft
  签名: (f : a ⟶ b) [Lift态射 f] {g h : b ⟶ c} (η : g ⟶ h) [Lift态射 g]
  定义体: LiftHom.lift f ◁ LiftHom₂.lift η

Depends on / 依赖: LiftHom, LiftHom.lift
-/
instance liftHom₂WhiskerLeft (f : a ⟶ b) [LiftHom f] {g h : b ⟶ c} (η : g ⟶ h) [LiftHom g]
    [LiftHom h] [LiftHom₂ η] : LiftHom₂ (f ◁ η) where
  lift := LiftHom.lift f ◁ LiftHom₂.lift η

/--
Instance `liftHom₂WhiskerRight` / 实例 `liftHom₂WhiskerRight`

English:
instance liftHom₂WhiskerRight
  signature: {f g : a ⟶ b} (η : f ⟶ g) [LiftHom f] [LiftHom g] [LiftHom₂ η]
  body: LiftHom₂.lift η ▷ LiftHom.lift h

中文:
实例 liftHom₂WhiskerRight
  签名: {f g : a ⟶ b} (η : f ⟶ g) [Lift态射 f] [Lift态射 g] [LiftHom₂ η]
  定义体: LiftHom₂.lift η ▷ LiftHom.lift h

Depends on / 依赖: LiftHom, LiftHom.lift
-/
instance liftHom₂WhiskerRight {f g : a ⟶ b} (η : f ⟶ g) [LiftHom f] [LiftHom g] [LiftHom₂ η]
    {h : b ⟶ c} [LiftHom h] : LiftHom₂ (η ▷ h) where
  lift := LiftHom₂.lift η ▷ LiftHom.lift h

open Lean Elab Tactic Meta

/-- Helper function for throwing exceptions. -/
meta def exception {α : Type} (g : MVarId) (msg : MessageData) : MetaM α :=
  throwTacticEx `bicategorical_coherence g msg

/-- Helper function for throwing exceptions with respect to the main goal. -/
meta def exception' (msg : MessageData) : TacticM Unit := do
  try
    liftMetaTactic (exception (msg := msg))
  catch _ =>
    -- There might not be any goals
    throwError msg

set_option quotPrecheck false in
/-- Auxiliary definition for `bicategorical_coherence`. -/
-- We could construct this expression directly without using `elabTerm`,
-- but it would require preparing many implicit arguments by hand.
meta def mkLiftMap₂LiftExpr (e : Expr) : TermElabM Expr := do
  Term.elabTerm
    (← ``((FreeBicategory.lift (Prefunctor.id _)).map₂ (LiftHom₂.lift $(← Term.exprToSyntax e))))
    none

/-- Coherence tactic for bicategories. -/
meta def bicategoryCoherence (g : MVarId) : TermElabM Unit := g.withContext do
  withOptions (fun opts => synthInstance.maxSize.set opts
    (max 256 (synthInstance.maxSize.get opts))) do
  let thms := [``BicategoricalCoherence.iso, ``Iso.trans, ``Iso.symm, ``Iso.refl,
    ``Bicategory.whiskerRightIso, ``Bicategory.whiskerLeftIso].foldl
    (·.addDeclToUnfoldCore ·) {}
  let (ty, _) ← dsimp (← g.getType) (← Simp.mkContext (simpTheorems := #[thms]))
  let some (_, lhs, rhs) := (← whnfR ty).eq? | exception g "Not an equation of morphisms."
  let lift_lhs ← mkLiftMap₂LiftExpr lhs
  let lift_rhs ← mkLiftMap₂LiftExpr rhs
  -- This new equation is defeq to the original by assumption
  -- on the `LiftHom` instances.
  let g₁ ← g.change (← mkEq lift_lhs lift_rhs)
  let [g₂] ← g₁.applyConst ``congrArg
    | exception g "congrArg failed in coherence"
  let [] ← g₂.applyConst ``Subsingleton.elim
    | exception g "This shouldn't happen; Subsingleton.elim does not create goals."

@[deprecated (since := "2026-05-27")] alias bicategory_coherence := bicategoryCoherence

open Lean.Parser.Tactic

/--
Simp lemmas for rewriting a 2-morphism into a normal form.
-/
syntax (name := whisker_simps) "whisker_simps" optConfig : tactic

@[inherit_doc whisker_simps]
elab_rules : tactic
| `(tactic| whisker_simps $cfg) => do
  evalTactic (← `(tactic|
simp cfg only [Category.assoc,
      Bicategory.comp_whiskerLeft, Bicategory.id_whiskerLeft,
      Bicategory.whiskerRight_comp, Bicategory.whiskerRight_id,
      Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_id,
      Bicategory.comp_whiskerRight, Bicategory.id_whiskerRight, Bicategory.whisker_assoc]
    ))

-- We have unused typeclass arguments here.
-- They are intentional, to ensure that `simp only [assoc_liftHom₂]` only left associates
-- bicategorical structural morphisms.
/-- Auxiliary simp lemma for the `coherence` tactic:
this move brackets to the left in order to expose a maximal prefix
built out of unitors and associators.
-/
@[nolint unusedArguments]
/--
theorem `assoc_liftHom₂` / 定理 `assoc_liftHom₂`

English:
theorem assoc_liftHom₂
  statement: {f g h i : a ⟶ b} [LiftHom f] [LiftHom g] [LiftHom h]
  proof: (Category.assoc _ _ _).symm

中文:
定理 assoc_liftHom₂
  结论: {f g h i : a ⟶ b} [Lift态射 f] [Lift态射 g] [Lift态射 h]
  证明: (Category.assoc _ _ _).symm

Depends on / 依赖: Category, Category.assoc, EqOnSource, PartialEquiv, PartialEquiv.EqOnSource.restr
-/
theorem assoc_liftHom₂ {f g h i : a ⟶ b} [LiftHom f] [LiftHom g] [LiftHom h]
    (η : f ⟶ g) (θ : g ⟶ h) (ι : h ⟶ i) [LiftHom₂ η] [LiftHom₂ θ] : η ≫ θ ≫ ι = (η ≫ θ) ≫ ι :=
  (Category.assoc _ _ _).symm

end Mathlib.Tactic.BicategoryCoherence
