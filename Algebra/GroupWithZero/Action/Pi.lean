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
variable {f : I → Type v}

namespace Pi

/-
**Pi.smulZeroClass** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：smulZeroClass (α) {n : forall i, Zero <| f i} [forall i, SMulZeroClass α <
| f i] : @SMulZeroClass α (forall i : I, f i) (@Pi.instZero I f n) where smul_ze
ro _
参数：α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance smulZeroClass (α) {n : ∀ i, Zero <| f i} [∀ i, SMulZeroClass α <| f i] :
    @SMulZeroClass α (∀ i : I, f i) (@Pi.instZero I f n) where
  smul_zero _ := funext fun _ => smul_zero _
/-
**Pi.smulZeroClass'** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：smulZeroClass' {g : I -> Type*} {n : forall i, Zero <| g i} [forall i, SMu
lZeroClass (f i) (g i)] : @SMulZeroClass (forall i, f i) (forall i : I, g i) (@P
i.instZero I g n) where smul_zero
参数：f i；g i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance smulZeroClass' {g : I → Type*} {n : ∀ i, Zero <| g i} [∀ i, SMulZeroClass (f i) (g i)] :
    @SMulZeroClass (∀ i, f i) (∀ i : I, g i) (@Pi.instZero I g n) where
  smul_zero := by intros; ext x; exact smul_zero _
/-
**Pi.distribSMul** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：distribSMul (α) {n : forall i, AddZeroClass <| f i} [forall i, DistribSMul
 α <| f i] : @DistribSMul α (forall i : I, f i) (@Pi.addZeroClass I f n) where s
mul_zero _
参数：α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance distribSMul (α) {n : ∀ i, AddZeroClass <| f i} [∀ i, DistribSMul α <| f i] :
    @DistribSMul α (∀ i : I, f i) (@Pi.addZeroClass I f n) where
  smul_zero _ := funext fun _ => smul_zero _
  smul_add _ _ _ := funext fun _ => smul_add _ _ _
/-
**Pi.distribSMul'** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：distribSMul' {g : I -> Type*} {n : forall i, AddZeroClass <| g i} [forall 
i, DistribSMul (f i) (g i)] : @DistribSMul (forall i, f i) (forall i : I, g i) (
@Pi.addZeroClass I g n) where smul_zero
参数：f i；g i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance distribSMul' {g : I → Type*} {n : ∀ i, AddZeroClass <| g i}
    [∀ i, DistribSMul (f i) (g i)] :
    @DistribSMul (∀ i, f i) (∀ i : I, g i) (@Pi.addZeroClass I g n) where
  smul_zero := by intros; ext x; exact smul_zero _
  smul_add := by intros; ext x; exact smul_add _ _ _
/-
**Pi.distribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：distribMulAction (α) {m : Monoid α} {n : forall i, AddMonoid <| f i} [fora
ll i, DistribMulAction α <| f i] : @DistribMulAction α (forall i : I, f i) m (@P
i.addMonoid I f n)
参数：α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance distribMulAction (α) {m : Monoid α} {n : ∀ i, AddMonoid <| f i}
    [∀ i, DistribMulAction α <| f i] : @DistribMulAction α (∀ i : I, f i) m (@Pi.addMonoid I f n) :=
  { Pi.mulAction _, Pi.distribSMul _ with }
/-
**Pi.distribMulAction'** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：distribMulAction' {g : I -> Type*} {m : forall i, Monoid (f i)} {n : foral
l i, AddMonoid <| g i} [forall i, DistribMulAction (f i) (g i)] : @DistribMulAct
ion (forall i, f i) (forall i : I, g i) (@Pi.monoid I f m) (@Pi.addMonoid I g n)
参数：f i；f i；g i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance distribMulAction' {g : I → Type*} {m : ∀ i, Monoid (f i)} {n : ∀ i, AddMonoid <| g i}
    [∀ i, DistribMulAction (f i) (g i)] :
    @DistribMulAction (∀ i, f i) (∀ i : I, g i) (@Pi.monoid I f m) (@Pi.addMonoid I g n) :=
  { Pi.mulAction', Pi.distribSMul' with }
/-
**Pi.smulWithZero** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：smulWithZero (α) [Zero α] [forall i, Zero (f i)] [forall i, SMulWithZero α
 (f i)] : SMulWithZero α (forall i, f i)
参数：α；f i；f i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance smulWithZero (α) [Zero α] [∀ i, Zero (f i)] [∀ i, SMulWithZero α (f i)] :
    SMulWithZero α (∀ i, f i) :=
  { Pi.instSMul with
    smul_zero := fun _ => funext fun _ => smul_zero _
    zero_smul := fun _ => funext fun _ => zero_smul _ _ }
/-
**Pi.smulWithZero'** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：smulWithZero' {g : I -> Type*} [forall i, Zero (g i)] [forall i, Zero (f i
)] [forall i, SMulWithZero (g i) (f i)] : SMulWithZero (forall i, g i) (forall i
, f i)
参数：g i；f i；g i；f i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance smulWithZero' {g : I → Type*} [∀ i, Zero (g i)] [∀ i, Zero (f i)]
    [∀ i, SMulWithZero (g i) (f i)] : SMulWithZero (∀ i, g i) (∀ i, f i) :=
  { Pi.smul' with
    smul_zero := fun _ => funext fun _ => smul_zero _
    zero_smul := fun _ => funext fun _ => zero_smul _ _ }
/-
**Pi.mulActionWithZero** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：mulActionWithZero (α) [MonoidWithZero α] [forall i, Zero (f i)] [forall i,
 MulActionWithZero α (f i)] : MulActionWithZero α (forall i, f i)
参数：α；f i；f i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mulActionWithZero (α) [MonoidWithZero α] [∀ i, Zero (f i)]
    [∀ i, MulActionWithZero α (f i)] : MulActionWithZero α (∀ i, f i) :=
  { Pi.mulAction _, Pi.smulWithZero _ with }
/-
**Pi.mulActionWithZero'** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：mulActionWithZero' {g : I -> Type*} [forall i, MonoidWithZero (g i)] [fora
ll i, Zero (f i)] [forall i, MulActionWithZero (g i) (f i)] : MulActionWithZero 
(forall i, g i) (forall i, f i)
参数：g i；f i；g i；f i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mulActionWithZero' {g : I → Type*} [∀ i, MonoidWithZero (g i)] [∀ i, Zero (f i)]
    [∀ i, MulActionWithZero (g i) (f i)] : MulActionWithZero (∀ i, g i) (∀ i, f i) :=
  { Pi.mulAction', Pi.smulWithZero' with }
/-
**Pi.single_smul** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：single_smul {α} [Monoid α] [forall i, AddMonoid <| f i] [forall i, Distrib
MulAction α <| f i] [DecidableEq I] (i : I) (r : α) (x : f i) : single i (r • x)
 = r • single i x
参数：i : I；r : α；x : f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.single_op`：∀ {ι : Type u_1} {M : ι → Type u_6} {N : ι → Type u_7} [in
st : (i : ι) → Zero (M i)] [inst_1 : (i : ι) → Zero (N i)]   [inst_2 : Decidable
Eq…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem single_smul {α} [Monoid α] [∀ i, AddMonoid <| f i] [∀ i, DistribMulAction α <| f i]
    [DecidableEq I] (i : I) (r : α) (x : f i) : single i (r • x) = r • single i x :=
  single_op (fun i : I => (r • · : f i → f i)) (fun _ => smul_zero _) _ _

/-- A version of `Pi.single_smul` for non-dependent functions. It is useful in cases where Lean
fails to apply `Pi.single_smul`. -/
/-
**Pi.single_smul'** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：single_smul' {α β} [Monoid α] [AddMonoid β] [DistribMulAction α β] [Decida
bleEq I] (i : I) (r : α) (x : β) : single (M
参数：i : I；r : α；x : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.single_smul`：single_smul {α} [Monoid α] [forall i, AddMonoid <| f i] 
[forall i, DistribMulAction α <| f i] [DecidableEq I] (i : I) (r : α) (x : f i) 
: si…

--- 原说明 ---
A version of `Pi.single_smul` for non-dependent functions. It is useful in cases
 where Lean
fails to apply `Pi.single_smul`.
-/
theorem single_smul' {α β} [Monoid α] [AddMonoid β] [DistribMulAction α β] [DecidableEq I] (i : I)
    (r : α) (x : β) : single (M := fun _ => β) i (r • x) = r • single (M := fun _ => β) i x :=
  single_smul (f := fun _ => β) i r x
/-
**Pi.single_smul** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：single_smul {α} [Monoid α] [forall i, AddMonoid <| f i] [forall i, Distrib
MulAction α <| f i] [DecidableEq I] (i : I) (r : α) (x : f i) : single i (r • x)
 = r • single i x
参数：i : I；r : α；x : f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.single_op`：∀ {ι : Type u_1} {M : ι → Type u_6} {N : ι → Type u_7} [in
st : (i : ι) → Zero (M i)] [inst_1 : (i : ι) → Zero (N i)]   [inst_2 : Decidable
Eq…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem single_smul₀ {g : I → Type*} [∀ i, MonoidWithZero (f i)] [∀ i, AddMonoid (g i)]
    [∀ i, DistribMulAction (f i) (g i)] [DecidableEq I] (i : I) (r : f i) (x : g i) :
    single i (r • x) = single i r • single i x :=
  single_op₂ (fun i : I => ((· • ·) : f i → g i → g i)) (fun _ => smul_zero _) _ _ _
/-
**Pi.mulDistribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：mulDistribMulAction (α) {m : Monoid α} {n : forall i, Monoid <| f i} [fora
ll i, MulDistribMulAction α <| f i] : @MulDistribMulAction α (forall i : I, f i)
 m (@Pi.monoid I f n)
参数：α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mulDistribMulAction (α) {m : Monoid α} {n : ∀ i, Monoid <| f i}
    [∀ i, MulDistribMulAction α <| f i] :
    @MulDistribMulAction α (∀ i : I, f i) m (@Pi.monoid I f n) :=
  { Pi.mulAction _ with
    smul_one := fun _ => funext fun _ => smul_one _
    smul_mul := fun _ _ _ => funext fun _ => smul_mul' _ _ _ }
/-
**Pi.mulDistribMulAction'** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：mulDistribMulAction' {g : I -> Type*} {m : forall i, Monoid (f i)} {n : fo
rall i, Monoid <| g i} [forall i, MulDistribMulAction (f i) (g i)] : @MulDistrib
MulAction (forall i, f i) (forall i : I, g i) (@Pi.monoid I f m) (@Pi.monoid I g
 n) where smul_mul
参数：f i；f i；g i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mulDistribMulAction' {g : I → Type*} {m : ∀ i, Monoid (f i)} {n : ∀ i, Monoid <| g i}
    [∀ i, MulDistribMulAction (f i) (g i)] :
    @MulDistribMulAction (∀ i, f i) (∀ i : I, g i) (@Pi.monoid I f m) (@Pi.monoid I g n) where
  smul_mul := by
    intros
    ext x
    apply smul_mul'
  smul_one := by
    intros
    ext x
    apply smul_one

end Pi

