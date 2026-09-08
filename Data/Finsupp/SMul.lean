/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kim Morrison
-/
module

public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Module.Basic
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.Regular.SMul
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.SMulWithZero
public import Mathlib.GroupTheory.GroupAction.Hom

/-!
# Declarations about scalar multiplication on `Finsupp`

## Implementation notes

This file is a `noncomputable theory` and uses classical logic throughout.

-/

@[expose] public section


noncomputable section

open Finset Function

variable {α β M N G R : Type*}

namespace Finsupp

section

variable [Zero M] [MonoidWithZero R] [MulActionWithZero R M]

@[simp]
/-
**Finsupp.single_smul** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：single_smul (a b : α) (f : α -> M) (r : R) : single a r b • f a = single a
 (r • f b) b
参数：a b : α；f : α -> M；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finsupp.single_eq_of_ne'`：single_eq_of_ne' (h : a != a') : (single a b :
 α ->₀ M) a' = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
-/
theorem single_smul (a b : α) (f : α → M) (r : R) : single a r b • f a = single a (r • f b) b := by
  by_cases h : a = b <;> simp [h]

end

section

variable [Monoid G] [MulAction G α] [AddCommMonoid M]

/-- Scalar multiplication acting on the domain.

This is not an instance as it would conflict with the action on the range.
See the `instance_diamonds` test for examples of such conflicts. -/
@[instance_reducible]
/-
**Finsupp.comapSMul** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：comapSMul : SMul G (α ->₀ M) where smul g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Scalar multiplication acting on the domain.

This is not an instance as it would conflict with the action on the range.
See the `instance_diamonds` test for examples of such conflicts.
-/
def comapSMul : SMul G (α →₀ M) where smul g := mapDomain (g • ·)

attribute [local instance] comapSMul
/-
**Finsupp.comapSMul_def** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：comapSMul_def (g : G) (f : α ->₀ M) : g • f = mapDomain (g • ·) f
参数：g : G；f : α ->₀ M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comapSMul_def (g : G) (f : α →₀ M) : g • f = mapDomain (g • ·) f :=
  rfl

@[simp]
/-
**Finsupp.comapSMul_single** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：comapSMul_single (g : G) (a : α) (b : M) : g • single a b = single (g • a)
 b
参数：g : G；a : α；b : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.mapDomain_single`：mapDomain_single {f : α -> β} {a : α} {b : M} 
: mapDomain f (single a b) = single (f a) b
-/
theorem comapSMul_single (g : G) (a : α) (b : M) : g • single a b = single (g • a) b :=
  mapDomain_single

/-- `Finsupp.comapSMul` is multiplicative -/
@[instance_reducible]
/-
**Finsupp.comapMulAction** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：comapMulAction : MulAction G (α ->₀ M) where one_smul f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Finsupp.comapSMul` is multiplicative
-/
def comapMulAction : MulAction G (α →₀ M) where
  one_smul f := by rw [comapSMul_def, one_smul_eq_id, mapDomain_id]
  mul_smul g g' f := by
    rw [comapSMul_def, comapSMul_def, comapSMul_def, ← comp_smul_left, mapDomain_comp]

attribute [local instance] comapMulAction

/-- `Finsupp.comapSMul` is distributive -/
@[instance_reducible]
/-
**Finsupp.comapDistribMulAction** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：comapDistribMulAction : DistribMulAction G (α ->₀ M) where smul_zero g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Finsupp.comapSMul` is distributive
-/
def comapDistribMulAction : DistribMulAction G (α →₀ M) where
  smul_zero g := by
    ext a
    simp only [comapSMul_def]
    simp
  smul_add g f f' := by
    ext
    simp only [comapSMul_def]
    simp [mapDomain_add]

end

section

variable [Group G] [MulAction G α] [AddCommMonoid M]

attribute [local instance] comapSMul comapMulAction comapDistribMulAction

/-- When `G` is a group, `Finsupp.comapSMul` acts by precomposition with the action of `g⁻¹`.
-/
@[simp]
/-
**Finsupp.comapSMul_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：comapSMul_apply (g : G) (f : α ->₀ M) (a : α) : (g • f) a = f (g⁻¹ • a)
参数：g : G；f : α ->₀ M；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
· 使用定理 `Finsupp.mapDomain_apply`：∀ {α : Type u_1} {β : Type u_2} {M : Type u_5} 
[inst : AddCommMonoid M] {f : α → β},   Function.Injective f → ∀ (x : α →₀ M) (a
 : α), (Finsu…
· 使用定理 `MulAction.injective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [i
nst_1 : MulAction α β] (g : α), Function.Injective fun x => g • x

--- 原说明 ---
When `G` is a group, `Finsupp.comapSMul` acts by precomposition with the action 
of `g⁻¹`.
-/
theorem comapSMul_apply (g : G) (f : α →₀ M) (a : α) : (g • f) a = f (g⁻¹ • a) := by
  conv_lhs => rw [← smul_inv_smul g a]
  exact mapDomain_apply (MulAction.injective g) _ (g⁻¹ • a)

end

section

/-!
Throughout this section, some `Monoid` and `Semiring` arguments are specified with `{}` instead of
`[]`. See note [implicit instance arguments].
-/

/-
**Finsupp._root_.IsSMulRegular.finsupp** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Throughout this section, some `Monoid` and `Semiring` arguments are specified wi
th `{}` instead of
`[]`. See note [implicit instance arguments].
-/
theorem _root_.IsSMulRegular.finsupp [Zero M] [SMulZeroClass R M] {k : R}
    (hk : IsSMulRegular M k) : IsSMulRegular (α →₀ M) k :=
  fun _ _ h => ext fun i => hk (DFunLike.congr_fun h i)
/-
**Finsupp.faithfulSMul** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：faithfulSMul [Nonempty α] [Zero M] [SMulZeroClass R M] [FaithfulSMul R M] 
: FaithfulSMul R (α ->₀ M) where eq_of_smul_eq_smul h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FaithfulSMul.eq_of_smul_eq_smul`：∀ {M : Type u_4} {α : Type u_5} {inst :
 SMul M α} [self : FaithfulSMul M α] {m₁ m₂ : M},   (∀ (a : α), m₁ • a = m₂ • a)
 → m₁ = m₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.smul_single`：smul_single [Zero M] [SMulZeroClass R M] (c : R) (a
 : α) (b : M) : c • Finsupp.single a b = Finsupp.single a (c • b)
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
instance faithfulSMul [Nonempty α] [Zero M] [SMulZeroClass R M] [FaithfulSMul R M] :
    FaithfulSMul R (α →₀ M) where
  eq_of_smul_eq_smul h :=
    let ⟨a⟩ := ‹Nonempty α›
    eq_of_smul_eq_smul fun m : M => by simpa using DFunLike.congr_fun (h (single a m)) a

variable (α M)
/-
**Finsupp.distribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：distribMulAction [Monoid R] [AddMonoid M] [DistribMulAction R M] : Distrib
MulAction R (α ->₀ M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance distribMulAction [Monoid R] [AddMonoid M] [DistribMulAction R M] :
    DistribMulAction R (α →₀ M) :=
  { Finsupp.distribSMul _ _ with
    one_smul := fun x => ext fun y => one_smul R (x y)
    mul_smul := fun r s x => ext fun y => mul_smul r s (x y) }
/-
**Finsupp.module** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：module [Semiring R] [AddCommMonoid M] [Module R M] : Module R (α ->₀ M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance module [Semiring R] [AddCommMonoid M] [Module R M] : Module R (α →₀ M) :=
  { toDistribMulAction := Finsupp.distribMulAction α M
    zero_smul := fun _ => ext fun _ => zero_smul _ _
    add_smul := fun _ _ _ => ext fun _ => add_smul _ _ _ }

variable {α M}

@[simp]
/-
**Finsupp.support_smul_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：support_smul_eq [Semiring R] [IsDomain R] [AddCommMonoid M] [Module R M] [
Module.IsTorsionFree R M] {b : R} (hb : b != 0) {g : α ->₀ M} : (b • g).support 
= g.support
参数：hb : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem support_smul_eq [Semiring R] [IsDomain R] [AddCommMonoid M] [Module R M]
    [Module.IsTorsionFree R M] {b : R} (hb : b ≠ 0) {g : α →₀ M} : (b • g).support = g.support :=
  Finset.ext fun a => by simp [Finsupp.smul_apply, hb]

section

variable {p : α → Prop} [DecidablePred p]

@[simp]
/-
**Finsupp.filter_smul** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：filter_smul [Zero M] [SMulZeroClass R M] {b : R} {v : α ->₀ M} : (b • v).f
ilter p = b • v.filter p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.filter_eq_indicator`：filter_eq_indicator : ⇑(f.filter p) = Set.i
ndicator { x | p x } f
· 使用引理 `Set.indicator_const_smul`：indicator_const_smul (s : Set α) (r : R) (f : 
α -> M) : indicator s (r • f ·) = (r • indicator s f ·)
-/
theorem filter_smul [Zero M] [SMulZeroClass R M] {b : R} {v : α →₀ M} :
    (b • v).filter p = b • v.filter p :=
  DFunLike.coe_injective <| by
    simp only [filter_eq_indicator, coe_smul]
    exact Set.indicator_const_smul { x | p x } b v

end

/-
**Finsupp.mapDomain_smul** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mapDomain_smul [AddCommMonoid M] [DistribSMul R M] {f : α -> β} (b : R) (v
 : α ->₀ M) : mapDomain f (b • v) = b • mapDomain f v
参数：b : R；v : α ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.mapDomain_mapRange`：mapDomain_mapRange [AddCommMonoid N] (f : α 
-> β) (v : α ->₀ M) (g : M -> N) (h0 : g 0 = 0) (hadd : forall x y, g (x + y) = 
g x + g y) : map…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
-/
theorem mapDomain_smul [AddCommMonoid M] [DistribSMul R M] {f : α → β} (b : R)
    (v : α →₀ M) : mapDomain f (b • v) = b • mapDomain f v :=
  mapDomain_mapRange _ _ _ _ (smul_add b)
/-
**Finsupp.smul_single'** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：smul_single' {_ : Semiring R} (c : R) (a : α) (b : R) : c • Finsupp.single
 a b = Finsupp.single a (c * b)
参数：c : R；a : α；b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.smul_single`：smul_single [Zero M] [SMulZeroClass R M] (c : R) (a
 : α) (b : M) : c • Finsupp.single a b = Finsupp.single a (c • b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul_single' {_ : Semiring R} (c : R) (a : α) (b : R) :
    c • Finsupp.single a b = Finsupp.single a (c * b) := by simp
/-
**Finsupp.smul_single_one** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：smul_single_one [MulZeroOneClass R] (a : α) (b : R) : b • single a (1 : R)
 = single a b
参数：a : α；b : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.smul_single`：smul_single [Zero M] [SMulZeroClass R M] (c : R) (a
 : α) (b : M) : c • Finsupp.single a b = Finsupp.single a (c • b)
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem smul_single_one [MulZeroOneClass R] (a : α) (b : R) :
    b • single a (1 : R) = single a b := by
  rw [smul_single, smul_eq_mul, mul_one]
/-
**Finsupp.comapDomain_smul** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：comapDomain_smul [Zero M] [SMulZeroClass R M] {f : α -> β} (r : R) (v : β 
->₀ M) (hfv : Set.InjOn f (f ⁻¹' ↑v.support)) (hfrv : Set.InjOn f (f ⁻¹' ↑(r • v
).support)
参数：r : R；v : β ->₀ M；hfv : Set.InjOn f (f ⁻¹' ↑v.support)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
-/
theorem comapDomain_smul [Zero M] [SMulZeroClass R M] {f : α → β} (r : R)
    (v : β →₀ M) (hfv : Set.InjOn f (f ⁻¹' ↑v.support))
    (hfrv : Set.InjOn f (f ⁻¹' ↑(r • v).support) :=
      hfv.mono <| Set.preimage_mono <| Finset.coe_subset.mpr support_smul) :
    comapDomain f (r • v) hfrv = r • comapDomain f v hfv := by
  ext
  rfl

/-- A version of `Finsupp.comapDomain_smul` that's easier to use. -/
/-
**Finsupp.comapDomain_smul_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：comapDomain_smul_of_injective [Zero M] [SMulZeroClass R M] {f : α -> β} (h
f : Function.Injective f) (r : R) (v : β ->₀ M) : comapDomain f (r • v) hf.injOn
 = r • comapDomain f v hf.injOn
参数：hf : Function.Injective f；r : R；v : β ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.comapDomain_smul`：comapDomain_smul [Zero M] [SMulZeroClass R M] 
{f : α -> β} (r : R) (v : β ->₀ M) (hfv : Set.InjOn f (f ⁻¹' ↑v.support)) (hfrv 
: Set.InjOn f …
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s

--- 原说明 ---
A version of `Finsupp.comapDomain_smul` that's easier to use.
-/
theorem comapDomain_smul_of_injective [Zero M] [SMulZeroClass R M] {f : α → β}
    (hf : Function.Injective f) (r : R) (v : β →₀ M) :
    comapDomain f (r • v) hf.injOn = r • comapDomain f v hf.injOn :=
  comapDomain_smul _ _ _ _

end

/-
**Finsupp.sum_smul_index** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：sum_smul_index [MulZeroClass R] [AddCommMonoid M] {g : α ->₀ R} {b : R} {h
 : α -> R -> M} (h0 : forall i, h i 0 = 0) : (b • g).sum h = g.sum fun i a => h 
i (b * a)
参数：h0 : forall i, h i 0 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.sum_mapRange_index`：∀ {α : Type u_1} {M : Type u_8} {M' : Type u
_9} {N : Type u_10} [inst : Zero M] [inst_1 : Zero M']   [inst_2 : AddCommMonoid
 N] {f : M → M'}…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem sum_smul_index [MulZeroClass R] [AddCommMonoid M] {g : α →₀ R} {b : R} {h : α → R → M}
    (h0 : ∀ i, h i 0 = 0) : (b • g).sum h = g.sum fun i a => h i (b * a) :=
  Finsupp.sum_mapRange_index h0
/-
**Finsupp.sum_smul_index'** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：sum_smul_index' [Zero M] [SMulZeroClass R M] [AddCommMonoid N] {g : α ->₀ 
M} {b : R} {h : α -> M -> N} (h0 : forall i, h i 0 = 0) : (b • g).sum h = g.sum 
fun i c => h i (b • c)
参数：h0 : forall i, h i 0 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.sum_mapRange_index`：∀ {α : Type u_1} {M : Type u_8} {M' : Type u
_9} {N : Type u_10} [inst : Zero M] [inst_1 : Zero M']   [inst_2 : AddCommMonoid
 N] {f : M → M'}…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem sum_smul_index' [Zero M] [SMulZeroClass R M] [AddCommMonoid N] {g : α →₀ M} {b : R}
    {h : α → M → N} (h0 : ∀ i, h i 0 = 0) : (b • g).sum h = g.sum fun i c => h i (b • c) :=
  Finsupp.sum_mapRange_index h0

/-- A version of `Finsupp.sum_smul_index'` for bundled additive maps. -/
/-
**Finsupp.sum_smul_index_addMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：sum_smul_index_addMonoidHom [AddZeroClass M] [AddCommMonoid N] [SMulZeroCl
ass R M] {g : α ->₀ M} {b : R} {h : α -> M ->+ N} : ((b • g).sum fun a => h a) =
 g.sum fun i c => h i (b • c)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.sum_mapRange_index`：∀ {α : Type u_1} {M : Type u_8} {M' : Type u
_9} {N : Type u_10} [inst : Zero M] [inst_1 : Zero M']   [inst_2 : AddCommMonoid
 N] {f : M → M'}…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `AddMonoidHom.map_zero`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M
] [inst_1 : AddZero N] (f : M →+ N), f 0 = 0

--- 原说明 ---
A version of `Finsupp.sum_smul_index'` for bundled additive maps.
-/
theorem sum_smul_index_addMonoidHom [AddZeroClass M] [AddCommMonoid N] [SMulZeroClass R M]
    {g : α →₀ M} {b : R} {h : α → M →+ N} :
    ((b • g).sum fun a => h a) = g.sum fun i c => h i (b • c) :=
  sum_mapRange_index fun i => (h i).map_zero
/-
**Finsupp.moduleIsTorsionFree** 是 Mathlib 中的一个实例，位于命名空间 `Finsupp`。
形式化陈述：moduleIsTorsionFree [Semiring R] [AddCommMonoid M] [Module R M] {ι : Type*
} [Module.IsTorsionFree R M] : Module.IsTorsionFree R (ι ->₀ M) where isSMulRegu
lar r hr f g hfg
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `IsRegular.isSMulRegular`：∀ {R : Type u_1} {M : Type u_3} {inst : Semirin
g R} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Is
TorsionFree R…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
instance moduleIsTorsionFree [Semiring R] [AddCommMonoid M] [Module R M] {ι : Type*}
    [Module.IsTorsionFree R M] : Module.IsTorsionFree R (ι →₀ M) where
  isSMulRegular r hr f g hfg := by ext i; exact hr.isSMulRegular congr($hfg i)

section DistribMulActionSemiHom
variable [Monoid R] [AddMonoid M] [AddMonoid N] [DistribMulAction R M] [DistribMulAction R N]

/-- `Finsupp.single` as a `DistribMulActionSemiHom`.

See also `Finsupp.lsingle` for the version as a linear map. -/
/-
**Finsupp.DistribMulActionHom.single** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp.DistribM
ulActionHom`。
形式化陈述：{α : Type u_1} →   {M : Type u_3} →     {R : Type u_6} → [inst : Monoid R]
 → [inst_1 : AddMonoid M] → [inst_2 : DistribMulAction R M] → α → M →+[R] α →₀ M
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Finsupp.single` as a `DistribMulActionSemiHom`.

See also `Finsupp.lsingle` for the version as a linear map.
-/
def DistribMulActionHom.single (a : α) : M →+[R] α →₀ M :=
  { singleAddHom a with
    map_smul' := fun k m => by simp }
/-
**Finsupp.distribMulActionHom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：distribMulActionHom_ext {f g : (α ->₀ M) ->+[R] N} (h : forall (a : α) (m 
: M), f (single a m) = g (single a m)) : f = g
参数：α ->₀ M；h : forall (a : α) (m : M), f (single a m) = g (single a m)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DistribMulActionHom.toAddMonoidHom_injective`：∀ {M : Type u_1} [inst : M
onoid M] {N : Type u_2} [inst_1 : Monoid N] {φ : M →* N} {A : Type u_4} [inst_2 
: AddMonoid A]   [inst_3 : Distrib…
· 使用定理 `Finsupp.addHom_ext`：addHom_ext [AddZeroClass N] ⦃f g : (α ->₀ M) ->+ N⦄ 
(H : forall x y, f (single x y) = g (single x y)) : f = g
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `DistribMulActionHom.instAddDistribAddActionSemiHomClassCoeAddMonoidHom`：
∀ {M : Type u_1} [inst : Monoid M] {N : Type u_2} [inst_1 : Monoid N] (φ : M →* 
N) (A : Type u_4) [inst_2 : AddMonoid A]   [inst_3 : Distrib…
-/
theorem distribMulActionHom_ext {f g : (α →₀ M) →+[R] N}
    (h : ∀ (a : α) (m : M), f (single a m) = g (single a m)) : f = g :=
  DistribMulActionHom.toAddMonoidHom_injective <| addHom_ext h

/-- See note [partially-applied ext lemmas]. -/
@[ext]
/-
**Finsupp.distribMulActionHom_ext'** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：distribMulActionHom_ext' {f g : (α ->₀ M) ->+[R] N} (h : forall a : α, f.c
omp (DistribMulActionHom.single a) = g.comp (DistribMulActionHom.single a)) : f 
= g
参数：α ->₀ M；h : forall a : α, f.comp (DistribMulActionHom.single a) = g.comp (Dis
tribMulActionHom.single a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.distribMulActionHom_ext`：distribMulActionHom_ext {f g : (α ->₀ M
) ->+[R] N} (h : forall (a : α) (m : M), f (single a m) = g (single a m)) : f = 
g
· 使用定理 `DistribMulActionHom.congr_fun`：∀ {M : Type u_1} [inst : Monoid M] {N : T
ype u_2} [inst_1 : Monoid N] {φ : M →* N} {A : Type u_4} [inst_2 : AddMonoid A] 
  [inst_3 : Distrib…

--- 原说明 ---
See note [partially-applied ext lemmas].
-/
theorem distribMulActionHom_ext' {f g : (α →₀ M) →+[R] N}
    (h : ∀ a : α, f.comp (DistribMulActionHom.single a) = g.comp (DistribMulActionHom.single a)) :
    f = g :=
  distribMulActionHom_ext fun a => DistribMulActionHom.congr_fun (h a)

end DistribMulActionSemiHom

end Finsupp

