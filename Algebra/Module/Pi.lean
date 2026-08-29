/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Regular.SMul
public import Mathlib.Algebra.Ring.Pi

/-!
# Pi instances for modules

This file defines instances for module and related structures on Pi Types
-/

public section


universe u v w

variable {I : Type u}

-- The indexing type
variable {f : I -> Type v}

namespace Pi

/--
theorem `_root_.IsSMulRegular.pi` / 定理 `_root_.IsSMulRegular.pi`

English:
theorem _root_.IsSMulRegular.pi
  statement: {α : Type*} [forall i, SMul α <| f i] {k : α}
  proof: fun _ _ h =>
  funext fun i => hk i (congr_fun h i :)

中文:
定理 _root_.IsSMulRegular.pi
  结论: {α : 类型} [对任意 i, SMul α <| f i] {k : α}
  证明: fun _ _ h =>
  funext fun i => hk i (congr_fun h i :)
-/
theorem _root_.IsSMulRegular.pi {α : Type*} [forall i, SMul α <| f i] {k : α}
    (hk : forall i, IsSMulRegular (f i) k) : IsSMulRegular (forall i, f i) k := fun _ _ h =>
  funext fun i => hk i (congr_fun h i :)

variable (I f)

/--
Instance `module` / 实例 `module`

English:
instance module
  signature: (α) {r : Semiring α} {m : forall i, AddCommMonoid <| f i} [forall i, Module α <| f i]
  body: { Pi.distribMulAction _ with
    add_smul := fun _ _ _ => funext fun _ => add_smul _ _ _
    zero_smul := fun _ => funext fun _ => zero_smul α _ }

中文:
实例 module
  签名: (α) {r : Semiring α} {m : 对任意 i, AddCommMonoid <| f i} [对任意 i, Module α <| f i]
  定义体: { Pi.distribMulAction _ with
    add_smul := fun _ _ _ => funext fun _ => add_smul _ _ _
    zero_smul := fun _ => funext fun _ => zero_smul α _ }

Depends on / 依赖: Pi.distribMulAction, add_smul, distribMulAction, zero_smul
-/
instance module (α) {r : Semiring α} {m : forall i, AddCommMonoid <| f i} [forall i, Module α <| f i] :
    @Module α (forall i : I, f i) r (@Pi.addCommMonoid I f m) :=
  { Pi.distribMulAction _ with
    add_smul := fun _ _ _ => funext fun _ => add_smul _ _ _
    zero_smul := fun _ => funext fun _ => zero_smul α _ }

/- Extra instance to short-circuit type class resolution.
For unknown reasons, this is necessary for certain inference problems. E.g., for this to succeed:
```lean
example (β X : Type*) [NormedAddCommGroup β] [NormedSpace ℝ β] : Module ℝ (X → β) := inferInstance
```
See: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Typeclass.20resolution.20under.20binders/near/281296989
-/
/--
Instance `Function.module` / 实例 `Function.module`

English:
instance Function.module
  signature: (α β : Type*) [Semiring α] [AddCommMonoid β] [Module α β]
  body: Pi.module _ _ _

中文:
实例 Function.module
  签名: (α β : 类型) [Semiring α] [AddCommMonoid β] [Module α β]
  定义体: Pi.module _ _ _

Depends on / 依赖: Pi.module, module
-/
instance Function.module (α β : Type*) [Semiring α] [AddCommMonoid β] [Module α β] :
    Module α (I -> β) :=
  Pi.module _ _ _

variable {I f}

/--
Instance `module'` / 实例 `module'`

English:
instance module'
  signature: {g : I -> Type*} {r : forall i, Semiring (f i)} {m : forall i, AddCommMonoid (g i)}
  body: by
    intros
    ext1
    apply add_smul
  zero_smul := by
    intros
    ext1
    rw [zero_smul]

中文:
实例 module'
  签名: {g : I -> 类型} {r : 对任意 i, Semiring (f i)} {m : 对任意 i, AddCommMonoid (g i)}
  定义体: by
    intros
    ext1
    apply add_smul
  zero_smul := by
    intros
    ext1
    rw [zero_smul]

Depends on / 依赖: add_smul, intros, zero_smul
-/
instance module' {g : I -> Type*} {r : forall i, Semiring (f i)} {m : forall i, AddCommMonoid (g i)}
    [forall i, Module (f i) (g i)] : Module (forall i, f i) (forall i, g i) where
  add_smul := by
    intros
    ext1
    apply add_smul
  zero_smul := by
    intros
    ext1
    rw [zero_smul]

end Pi
