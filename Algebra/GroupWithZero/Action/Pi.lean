/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
module

public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Pi
public import Mathlib.Tactic.Common

/-!
# Pi instances for multiplicative actions with zero

This file defines instances for `MulActionWithZero` and related structures on `Pi` types.

## See also

* `Algebra.GroupWithZero.Action.Opposite`
* `Algebra.GroupWithZero.Action.Prod`
* `Algebra.GroupWithZero.Action.Units`
-/

public section

assert_not_exists Ring

universe u v

variable {I : Type u}

-- The indexing type
variable {f : I -> Type v}

namespace Pi

/--
Instance `smulZeroClass` / 实例 `smulZeroClass`

English:
instance smulZeroClass
  signature: (α) {n : forall i, Zero <| f i} [forall i, SMulZeroClass α <| f i]
  body: funext fun _ => smul_zero _

中文:
实例 smulZeroClass
  签名: (α) {n : 对任意 i, 零 <| f i} [对任意 i, SMulZero类 α <| f i]
  定义体: funext fun _ => smul_zero _

Depends on / 依赖: smul_zero
-/
instance smulZeroClass (α) {n : forall i, Zero <| f i} [forall i, SMulZeroClass α <| f i] :
    @SMulZeroClass α (forall i : I, f i) (@Pi.instZero I f n) where
  smul_zero _ := funext fun _ => smul_zero _

/--
Instance `smulZeroClass'` / 实例 `smulZeroClass'`

English:
instance smulZeroClass'
  signature: {g : I -> Type*} {n : forall i, Zero <| g i} [forall i, SMulZeroClass (f i) (g i)]
  body: by intros; ext x; exact smul_zero _

中文:
实例 smulZeroClass'
  签名: {g : I -> 类型} {n : 对任意 i, 零 <| g i} [对任意 i, SMulZero类 (f i) (g i)]
  定义体: by intros; ext x; exact smul_zero _

Depends on / 依赖: intros, smul_zero
-/
instance smulZeroClass' {g : I -> Type*} {n : forall i, Zero <| g i} [forall i, SMulZeroClass (f i) (g i)] :
    @SMulZeroClass (forall i, f i) (forall i : I, g i) (@Pi.instZero I g n) where
  smul_zero := by intros; ext x; exact smul_zero _

/--
Instance `distribSMul` / 实例 `distribSMul`

English:
instance distribSMul
  signature: (α) {n : forall i, AddZeroClass <| f i} [forall i, DistribSMul α <| f i]
  body: funext fun _ => smul_zero _
  smul_add _ _ _ := funext fun _ => smul_add _ _ _

中文:
实例 distribSMul
  签名: (α) {n : 对任意 i, 加法零类 <| f i} [对任意 i, 分配标量乘法 α <| f i]
  定义体: funext fun _ => smul_zero _
  smul_add _ _ _ := funext fun _ => smul_add _ _ _

Depends on / 依赖: smul_zero
-/
instance distribSMul (α) {n : forall i, AddZeroClass <| f i} [forall i, DistribSMul α <| f i] :
    @DistribSMul α (forall i : I, f i) (@Pi.addZeroClass I f n) where
  smul_zero _ := funext fun _ => smul_zero _
  smul_add _ _ _ := funext fun _ => smul_add _ _ _

/--
Instance `distribSMul'` / 实例 `distribSMul'`

English:
instance distribSMul'
  signature: {g : I -> Type*} {n : forall i, AddZeroClass <| g i}
  body: by intros; ext x; exact smul_zero _
  smul_add := by intros; ext x; exact smul_add _ _ _

中文:
实例 distribSMul'
  签名: {g : I -> 类型} {n : 对任意 i, 加法零类 <| g i}
  定义体: by intros; ext x; exact smul_zero _
  smul_add := by intros; ext x; exact smul_add _ _ _

Depends on / 依赖: intros, smul_add, smul_zero
-/
instance distribSMul' {g : I -> Type*} {n : forall i, AddZeroClass <| g i}
    [forall i, DistribSMul (f i) (g i)] :
    @DistribSMul (forall i, f i) (forall i : I, g i) (@Pi.addZeroClass I g n) where
  smul_zero := by intros; ext x; exact smul_zero _
  smul_add := by intros; ext x; exact smul_add _ _ _

/--
Instance `distribMulAction` / 实例 `distribMulAction`

English:
instance distribMulAction
  signature: (α) {m : Monoid α} {n : forall i, AddMonoid <| f i}
  body: { Pi.mulAction _, Pi.distribSMul _ with }

中文:
实例 distribMulAction
  签名: (α) {m : 幺半群 α} {n : 对任意 i, 加法幺半群 <| f i}
  定义体: { Pi.mulAction _, Pi.distribSMul _ with }

Depends on / 依赖: Pi.distribSMul, Pi.mulAction, distribSMul, mulAction
-/
instance distribMulAction (α) {m : Monoid α} {n : forall i, AddMonoid <| f i}
    [forall i, DistribMulAction α <| f i] : @DistribMulAction α (forall i : I, f i) m (@Pi.addMonoid I f n) :=
  { Pi.mulAction _, Pi.distribSMul _ with }

/--
Instance `distribMulAction'` / 实例 `distribMulAction'`

English:
instance distribMulAction'
  signature: {g : I -> Type*} {m : forall i, Monoid (f i)} {n : forall i, AddMonoid <| g i}
  body: { Pi.mulAction', Pi.distribSMul' with }

中文:
实例 distribMulAction'
  签名: {g : I -> 类型} {m : 对任意 i, 幺半群 (f i)} {n : 对任意 i, 加法幺半群 <| g i}
  定义体: { Pi.mulAction', Pi.distribSMul' with }

Depends on / 依赖: Pi.distribSMul, Pi.mulAction, distribSMul, mulAction
-/
instance distribMulAction' {g : I -> Type*} {m : forall i, Monoid (f i)} {n : forall i, AddMonoid <| g i}
    [forall i, DistribMulAction (f i) (g i)] :
    @DistribMulAction (forall i, f i) (forall i : I, g i) (@Pi.monoid I f m) (@Pi.addMonoid I g n) :=
  { Pi.mulAction', Pi.distribSMul' with }

/--
Instance `smulWithZero` / 实例 `smulWithZero`

English:
instance smulWithZero
  signature: (α) [Zero α] [forall i, Zero (f i)] [forall i, SMulWithZero α (f i)]
  body: { Pi.instSMul with
    smul_zero := fun _ => funext fun _ => smul_zero _
    zero_smul := fun _ => funext fun _ => zero_smul _ _ }

中文:
实例 smulWithZero
  签名: (α) [零 α] [对任意 i, 零 (f i)] [对任意 i, 带零标量乘法 α (f i)]
  定义体: { Pi.instSMul with
    smul_zero := fun _ => funext fun _ => smul_zero _
    zero_smul := fun _ => funext fun _ => zero_smul _ _ }

Depends on / 依赖: Pi.instSMul, instSMul, smul_zero, zero_smul
-/
instance smulWithZero (α) [Zero α] [forall i, Zero (f i)] [forall i, SMulWithZero α (f i)] :
    SMulWithZero α (forall i, f i) :=
  { Pi.instSMul with
    smul_zero := fun _ => funext fun _ => smul_zero _
    zero_smul := fun _ => funext fun _ => zero_smul _ _ }

/--
Instance `smulWithZero'` / 实例 `smulWithZero'`

English:
instance smulWithZero'
  signature: {g : I -> Type*} [forall i, Zero (g i)] [forall i, Zero (f i)]
  body: { Pi.smul' with
    smul_zero := fun _ => funext fun _ => smul_zero _
    zero_smul := fun _ => funext fun _ => zero_smul _ _ }

中文:
实例 smulWithZero'
  签名: {g : I -> 类型} [对任意 i, 零 (g i)] [对任意 i, 零 (f i)]
  定义体: { Pi.smul' with
    smul_zero := fun _ => funext fun _ => smul_zero _
    zero_smul := fun _ => funext fun _ => zero_smul _ _ }

Depends on / 依赖: Pi.smul, smul_zero, zero_smul
-/
instance smulWithZero' {g : I -> Type*} [forall i, Zero (g i)] [forall i, Zero (f i)]
    [forall i, SMulWithZero (g i) (f i)] : SMulWithZero (forall i, g i) (forall i, f i) :=
  { Pi.smul' with
    smul_zero := fun _ => funext fun _ => smul_zero _
    zero_smul := fun _ => funext fun _ => zero_smul _ _ }

/--
Instance `mulActionWithZero` / 实例 `mulActionWithZero`

English:
instance mulActionWithZero
  signature: (α) [MonoidWithZero α] [forall i, Zero (f i)]
  body: { Pi.mulAction _, Pi.smulWithZero _ with }

中文:
实例 mulActionWithZero
  签名: (α) [带零幺半群 α] [对任意 i, 零 (f i)]
  定义体: { Pi.mulAction _, Pi.smulWithZero _ with }

Depends on / 依赖: Pi.mulAction, Pi.smulWithZero, mulAction, smulWithZero
-/
instance mulActionWithZero (α) [MonoidWithZero α] [forall i, Zero (f i)]
    [forall i, MulActionWithZero α (f i)] : MulActionWithZero α (forall i, f i) :=
  { Pi.mulAction _, Pi.smulWithZero _ with }

/--
Instance `mulActionWithZero'` / 实例 `mulActionWithZero'`

English:
instance mulActionWithZero'
  signature: {g : I -> Type*} [forall i, MonoidWithZero (g i)] [forall i, Zero (f i)]
  body: { Pi.mulAction', Pi.smulWithZero' with }

中文:
实例 mulActionWithZero'
  签名: {g : I -> 类型} [对任意 i, 带零幺半群 (g i)] [对任意 i, 零 (f i)]
  定义体: { Pi.mulAction', Pi.smulWithZero' with }

Depends on / 依赖: Pi.mulAction, Pi.smulWithZero, mulAction, smulWithZero
-/
instance mulActionWithZero' {g : I -> Type*} [forall i, MonoidWithZero (g i)] [forall i, Zero (f i)]
    [forall i, MulActionWithZero (g i) (f i)] : MulActionWithZero (forall i, g i) (forall i, f i) :=
  { Pi.mulAction', Pi.smulWithZero' with }

/--
theorem `single_smul` / 定理 `single_smul`

English:
theorem single_smul
  statement: {α} [Monoid α] [forall i, AddMonoid <| f i] [forall i, DistribMulAction α <| f i]
  proof: single_op (fun i : I => (r • · : f i -> f i)) (fun _ => smul_zero _) _ _

中文:
定理 single_smul
  结论: {α} [幺半群 α] [对任意 i, 加法幺半群 <| f i] [对任意 i, 分配乘法作用 α <| f i]
  证明: single_op (fun i : I => (r • · : f i -> f i)) (fun _ => smul_zero _) _ _

Depends on / 依赖: single_op, smul_zero
-/
theorem single_smul {α} [Monoid α] [forall i, AddMonoid <| f i] [forall i, DistribMulAction α <| f i]
    [DecidableEq I] (i : I) (r : α) (x : f i) : single i (r • x) = r • single i x :=
  single_op (fun i : I => (r • · : f i -> f i)) (fun _ => smul_zero _) _ _

/--
theorem `single_smul'` / 定理 `single_smul'`

English:
theorem single_smul'
  statement: {α β} [Monoid α] [AddMonoid β] [DistribMulAction α β] [DecidableEq I] (i : I)
  proof: single_smul (f := fun _ => β) i r x

中文:
定理 single_smul'
  结论: {α β} [幺半群 α] [加法幺半群 β] [分配乘法作用 α β] [DecidableEq I] (i : I)
  证明: single_smul (f := fun _ => β) i r x

Depends on / 依赖: single
-/
theorem single_smul' {α β} [Monoid α] [AddMonoid β] [DistribMulAction α β] [DecidableEq I] (i : I)
    (r : α) (x : β) : single (M := fun _ => β) i (r • x) = r • single (M := fun _ => β) i x :=
  single_smul (f := fun _ => β) i r x

/--
theorem `single_smul₀` / 定理 `single_smul₀`

English:
theorem single_smul₀
  statement: {g : I -> Type*} [forall i, MonoidWithZero (f i)] [forall i, AddMonoid (g i)]
  proof: single_op₂ (fun i : I => ((· • ·) : f i -> g i -> g i)) (fun _ => smul_zero _) _ _ _

中文:
定理 single_smul₀
  结论: {g : I -> 类型} [对任意 i, 带零幺半群 (f i)] [对任意 i, 加法幺半群 (g i)]
  证明: single_op₂ (fun i : I => ((· • ·) : f i -> g i -> g i)) (fun _ => smul_zero _) _ _ _

Depends on / 依赖: smul_zero
-/
theorem single_smul₀ {g : I -> Type*} [forall i, MonoidWithZero (f i)] [forall i, AddMonoid (g i)]
    [forall i, DistribMulAction (f i) (g i)] [DecidableEq I] (i : I) (r : f i) (x : g i) :
    single i (r • x) = single i r • single i x :=
  single_op₂ (fun i : I => ((· • ·) : f i -> g i -> g i)) (fun _ => smul_zero _) _ _ _

/--
Instance `mulDistribMulAction` / 实例 `mulDistribMulAction`

English:
instance mulDistribMulAction
  signature: (α) {m : Monoid α} {n : forall i, Monoid <| f i}
  body: { Pi.mulAction _ with
    smul_one := fun _ => funext fun _ => smul_one _
    smul_mul := fun _ _ _ => funext fun _ => smul_mul' _ _ _ }

中文:
实例 mulDistribMulAction
  签名: (α) {m : 幺半群 α} {n : 对任意 i, 幺半群 <| f i}
  定义体: { Pi.mulAction _ with
    smul_one := fun _ => funext fun _ => smul_one _
    smul_mul := fun _ _ _ => funext fun _ => smul_mul' _ _ _ }

Depends on / 依赖: Pi.mulAction, mulAction, smul_mul, smul_one
-/
instance mulDistribMulAction (α) {m : Monoid α} {n : forall i, Monoid <| f i}
    [forall i, MulDistribMulAction α <| f i] :
    @MulDistribMulAction α (forall i : I, f i) m (@Pi.monoid I f n) :=
  { Pi.mulAction _ with
    smul_one := fun _ => funext fun _ => smul_one _
    smul_mul := fun _ _ _ => funext fun _ => smul_mul' _ _ _ }

/--
Instance `mulDistribMulAction'` / 实例 `mulDistribMulAction'`

English:
instance mulDistribMulAction'
  signature: {g : I -> Type*} {m : forall i, Monoid (f i)} {n : forall i, Monoid <| g i}
  body: by
    intros
    ext x
    apply smul_mul'
  smul_one := by
    intros
    ext x
    apply smul_one

中文:
实例 mulDistribMulAction'
  签名: {g : I -> 类型} {m : 对任意 i, 幺半群 (f i)} {n : 对任意 i, 幺半群 <| g i}
  定义体: by
    intros
    ext x
    apply smul_mul'
  smul_one := by
    intros
    ext x
    apply smul_one

Depends on / 依赖: intros, smul_mul, smul_one
-/
instance mulDistribMulAction' {g : I -> Type*} {m : forall i, Monoid (f i)} {n : forall i, Monoid <| g i}
    [forall i, MulDistribMulAction (f i) (g i)] :
    @MulDistribMulAction (forall i, f i) (forall i : I, g i) (@Pi.monoid I f m) (@Pi.monoid I g n) where
  smul_mul := by
    intros
    ext x
    apply smul_mul'
  smul_one := by
    intros
    ext x
    apply smul_one

end Pi
