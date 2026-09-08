/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Pi
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Data.DFinsupp.Defs

/-!
# Group actions on `DFinsupp`

## Main results

* `DFinsupp.module`: pointwise scalar multiplication on `DFinsupp` gives a module structure
-/

@[expose] public section

universe u u₁ u₂ v v₁ v₂ v₃ w x y l

variable {ι : Type u} {γ : Type w} {β : ι → Type v} {β₁ : ι → Type v₁} {β₂ : ι → Type v₂}

namespace DFinsupp

section Algebra

/-- Dependent functions with finite support inherit a semiring action from an action on each
coordinate. -/
/-
**DFinsupp.** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Dependent functions with finite support inherit a semiring action from an action
 on each
coordinate.
-/
instance [∀ i, Zero (β i)] [∀ i, SMulZeroClass γ (β i)] : SMulZeroClass γ (Π₀ i, β i) where
  smul c v := v.mapRange (fun _ => (c • ·)) fun _ => smul_zero _
  smul_zero _ := mapRange_zero _ _
/-
**DFinsupp.smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：smul_apply [forall i, Zero (β i)] [forall i, SMulZeroClass γ (β i)] (b : γ
) (v : Π₀ i, β i) (i : ι) : (b • v) i = b • v i
参数：β i；β i；b : γ；v : Π₀ i, β i；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_apply [∀ i, Zero (β i)] [∀ i, SMulZeroClass γ (β i)] (b : γ)
    (v : Π₀ i, β i) (i : ι) : (b • v) i = b • v i :=
  rfl

@[simp, norm_cast]
/-
**DFinsupp.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：coe_smul [forall i, Zero (β i)] [forall i, SMulZeroClass γ (β i)] (b : γ) 
(v : Π₀ i, β i) : ⇑(b • v) = b • ⇑v
参数：β i；β i；b : γ；v : Π₀ i, β i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_smul [∀ i, Zero (β i)] [∀ i, SMulZeroClass γ (β i)] (b : γ)
    (v : Π₀ i, β i) : ⇑(b • v) = b • ⇑v :=
  rfl
/-
**DFinsupp.smulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
形式化陈述：smulCommClass {δ : Type*} [forall i, Zero (β i)] [forall i, SMulZeroClass 
γ (β i)] [forall i, SMulZeroClass δ (β i)] [forall i, SMulCommClass γ δ (β i)] :
 SMulCommClass γ δ (Π₀ i, β i) where smul_comm r s m
参数：β i；β i；β i；β i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance smulCommClass {δ : Type*} [∀ i, Zero (β i)]
    [∀ i, SMulZeroClass γ (β i)] [∀ i, SMulZeroClass δ (β i)] [∀ i, SMulCommClass γ δ (β i)] :
    SMulCommClass γ δ (Π₀ i, β i) where
  smul_comm r s m := ext fun i => by simp only [smul_apply, smul_comm r s (m i)]
/-
**DFinsupp.isScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
形式化陈述：isScalarTower {δ : Type*} [forall i, Zero (β i)] [forall i, SMulZeroClass 
γ (β i)] [forall i, SMulZeroClass δ (β i)] [SMul γ δ] [forall i, IsScalarTower γ
 δ (β i)] : IsScalarTower γ δ (Π₀ i, β i) where smul_assoc r s m
参数：β i；β i；β i；β i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance isScalarTower {δ : Type*} [∀ i, Zero (β i)]
    [∀ i, SMulZeroClass γ (β i)] [∀ i, SMulZeroClass δ (β i)] [SMul γ δ]
    [∀ i, IsScalarTower γ δ (β i)] : IsScalarTower γ δ (Π₀ i, β i) where
  smul_assoc r s m := ext fun i => by simp only [smul_apply, smul_assoc r s (m i)]
/-
**DFinsupp.isCentralScalar** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
形式化陈述：isCentralScalar [forall i, Zero (β i)] [forall i, SMulZeroClass γ (β i)] [
forall i, SMulZeroClass γᵐᵒᵖ (β i)] [forall i, IsCentralScalar γ (β i)] : IsCent
ralScalar γ (Π₀ i, β i) where op_smul_eq_smul r m
参数：β i；β i；β i；β i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCentralScalar.op_smul_eq_smul`：∀ {M : Type u_9} {α : Type u_10} {inst 
: SMul M α} {inst_1 : SMul Mᵐᵒᵖ α} [self : IsCentralScalar M α] (m : M) (a : α),
   MulOpposite.op m •…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance isCentralScalar [∀ i, Zero (β i)] [∀ i, SMulZeroClass γ (β i)]
    [∀ i, SMulZeroClass γᵐᵒᵖ (β i)] [∀ i, IsCentralScalar γ (β i)] :
    IsCentralScalar γ (Π₀ i, β i) where
  op_smul_eq_smul r m := ext fun i => by simp only [smul_apply, op_smul_eq_smul r (m i)]

/-- Dependent functions with finite support inherit a `DistribMulAction` structure from such a
/-
**DFinsupp.on** 是 Mathlib 中的一个结构，位于命名空间 `DFinsupp`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
structure on each coordinate. -/
/-
**DFinsupp.distribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
形式化陈述：distribMulAction [Monoid γ] [forall i, AddMonoid (β i)] [forall i, Distrib
MulAction γ (β i)] : DistribMulAction γ (Π₀ i, β i)
参数：β i；β i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Dependent functions with finite support inherit a `DistribMulAction` structure f
rom such a
structure on each coordinate.
-/
instance distribMulAction [Monoid γ] [∀ i, AddMonoid (β i)] [∀ i, DistribMulAction γ (β i)] :
    DistribMulAction γ (Π₀ i, β i) :=
  Function.Injective.distribMulAction coeFnAddMonoidHom DFunLike.coe_injective coe_smul

/-- Dependent functions with finite support inherit a module structure from such a structure on
each coordinate. -/
/-
**DFinsupp.module** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
形式化陈述：module [Semiring γ] [forall i, AddCommMonoid (β i)] [forall i, Module γ (β
 i)] : Module γ (Π₀ i, β i)
参数：β i；β i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Dependent functions with finite support inherit a module structure from such a s
tructure on
each coordinate.
-/
instance module [Semiring γ] [∀ i, AddCommMonoid (β i)] [∀ i, Module γ (β i)] :
    Module γ (Π₀ i, β i) :=
  { (inferInstance : DistribMulAction γ (Π₀ i, β i)) with
    zero_smul := fun c => ext fun i => by simp only [smul_apply, zero_smul, zero_apply]
    add_smul := fun c x y => ext fun i => by simp only [add_apply, smul_apply, add_smul] }

end Algebra

variable (γ) in
/-- Coercion from a `DFinsupp` to a pi type is a `LinearMap`. -/
/-
**DFinsupp.coeFnLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp`。
形式化陈述：coeFnLinearMap [Semiring γ] [forall i, AddCommMonoid (β i)] [forall i, Mod
ule γ (β i)] : (Π₀ i, β i) ->ₗ[γ] forall i, β i where toFun
参数：β i；β i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion from a `DFinsupp` to a pi type is a `LinearMap`.
-/
def coeFnLinearMap [Semiring γ] [∀ i, AddCommMonoid (β i)] [∀ i, Module γ (β i)] :
    (Π₀ i, β i) →ₗ[γ] ∀ i, β i where
  toFun := (⇑)
  map_add' := coe_add
  map_smul' := coe_smul

@[simp]
/-
**DFinsupp.coeFnLinearMap_apply** 是 Mathlib 中的一个引理，位于命名空间 `DFinsupp`。
形式化陈述：coeFnLinearMap_apply [Semiring γ] [forall i, AddCommMonoid (β i)] [forall 
i, Module γ (β i)] (v : Π₀ i, β i) : coeFnLinearMap γ v = v
参数：β i；β i；v : Π₀ i, β i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coeFnLinearMap_apply [Semiring γ] [∀ i, AddCommMonoid (β i)] [∀ i, Module γ (β i)]
    (v : Π₀ i, β i) : coeFnLinearMap γ v = v :=
  rfl

section FilterAndSubtypeDomain

@[simp]
/-
**DFinsupp.filter_smul** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：filter_smul [forall i, Zero (β i)] [forall i, SMulZeroClass γ (β i)] (p : 
ι -> Prop) [DecidablePred p] (r : γ) (f : Π₀ i, β i) : (r • f).filter p = r • f.
filter p
参数：β i；β i；p : ι -> Prop；r : γ；f : Π₀ i, β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_ite`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a b : α) (c : β),   (c • if p then a else b) = if p the…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem filter_smul [∀ i, Zero (β i)] [∀ i, SMulZeroClass γ (β i)] (p : ι → Prop)
    [DecidablePred p] (r : γ) (f : Π₀ i, β i) : (r • f).filter p = r • f.filter p := by
  ext
  simp [smul_apply, smul_ite]

variable (γ β)

/-- `DFinsupp.filter` as a `LinearMap`. -/
@[simps]
/-
**DFinsupp.filterLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp`。
形式化陈述：filterLinearMap [Semiring γ] [forall i, AddCommMonoid (β i)] [forall i, Mo
dule γ (β i)] (p : ι -> Prop) [DecidablePred p] : (Π₀ i, β i) ->ₗ[γ] Π₀ i, β i w
here toFun
参数：β i；β i；p : ι -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`DFinsupp.filter` as a `LinearMap`.
-/
def filterLinearMap [Semiring γ] [∀ i, AddCommMonoid (β i)] [∀ i, Module γ (β i)] (p : ι → Prop)
    [DecidablePred p] : (Π₀ i, β i) →ₗ[γ] Π₀ i, β i where
  toFun := filter p
  map_add' := filter_add p
  map_smul' := filter_smul p

variable {γ β}

@[simp]
/-
**DFinsupp.subtypeDomain_smul** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：subtypeDomain_smul [forall i, Zero (β i)] [forall i, SMulZeroClass γ (β i)
] {p : ι -> Prop} [DecidablePred p] (r : γ) (f : Π₀ i, β i) : (r • f).subtypeDom
ain p = r • f.subtypeDomain p
参数：β i；β i；r : γ；f : Π₀ i, β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem subtypeDomain_smul [∀ i, Zero (β i)] [∀ i, SMulZeroClass γ (β i)]
    {p : ι → Prop} [DecidablePred p] (r : γ) (f : Π₀ i, β i) :
    (r • f).subtypeDomain p = r • f.subtypeDomain p :=
  DFunLike.coe_injective rfl

variable (γ β)

/-- `DFinsupp.subtypeDomain` as a `LinearMap`. -/
@[simps]
/-
**DFinsupp.subtypeDomainLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `DFinsupp`。
形式化陈述：subtypeDomainLinearMap [Semiring γ] [forall i, AddCommMonoid (β i)] [foral
l i, Module γ (β i)] (p : ι -> Prop) [DecidablePred p] : (Π₀ i, β i) ->ₗ[γ] Π₀ i
 : Subtype p, β i where toFun
参数：β i；β i；p : ι -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`DFinsupp.subtypeDomain` as a `LinearMap`.
-/
def subtypeDomainLinearMap [Semiring γ] [∀ i, AddCommMonoid (β i)] [∀ i, Module γ (β i)]
    (p : ι → Prop) [DecidablePred p] : (Π₀ i, β i) →ₗ[γ] Π₀ i : Subtype p, β i where
  toFun := subtypeDomain p
  map_add' := subtypeDomain_add
  map_smul' := subtypeDomain_smul

end FilterAndSubtypeDomain

section DecidableEq
variable [DecidableEq ι]

section

variable [∀ i, Zero (β i)] [∀ i, SMulZeroClass γ (β i)]

@[simp]
/-
**DFinsupp.mk_smul** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：mk_smul {s : Finset ι} (c : γ) (x : forall i : (↑s : Set ι), β (i : ι)) : 
mk s (c • x) = c • mk s x
参数：c : γ；x : forall i : (↑s : Set ι), β (i : ι)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem mk_smul {s : Finset ι} (c : γ) (x : ∀ i : (↑s : Set ι), β (i : ι)) :
    mk s (c • x) = c • mk s x :=
  ext fun i => by simp only [smul_apply, mk_apply]; split_ifs <;> [rfl; rw [smul_zero]]

@[simp]
/-
**DFinsupp.single_smul** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：single_smul {i : ι} (c : γ) (x : β i) : single i (c • x) = c • single i x
参数：c : γ；x : β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `DFinsupp.single_apply`：single_apply {i i' b} : (single i b : Π₀ i, β i) 
i' = if h : i = i' then Eq.recOn h b else 0
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem single_smul {i : ι} (c : γ) (x : β i) : single i (c • x) = c • single i x :=
  ext fun i => by
    simp only [smul_apply, single_apply]
    split_ifs with h
    · cases h; rfl
    · rw [smul_zero]

end

/-
**DFinsupp.support_smul** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：support_smul {γ : Type w} [forall i, Zero (β i)] [forall i, SMulZeroClass 
γ (β i)] [forall (i : ι) (x : β i), Decidable (x != 0)] (b : γ) (v : Π₀ i, β i) 
: (b • v).support subseteq v.support
参数：β i；β i；i : ι；x : β i；x != 0；b : γ；v : Π₀ i, β i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.support_mapRange`：support_mapRange {f : forall i, β₁ i -> β₂ i}
 {hf : forall i, f i 0 = 0} {g : Π₀ i, β₁ i} : (mapRange f hf g).support subsete
q g.support
-/
theorem support_smul {γ : Type w} [∀ i, Zero (β i)] [∀ i, SMulZeroClass γ (β i)]
    [∀ (i : ι) (x : β i), Decidable (x ≠ 0)] (b : γ) (v : Π₀ i, β i) :
    (b • v).support ⊆ v.support :=
  support_mapRange

end DecidableEq

section Equiv

open Finset

variable {κ : Type*}

@[simp]
/-
**DFinsupp.comapDomain_smul** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：comapDomain_smul [forall i, Zero (β i)] [forall i, SMulZeroClass γ (β i)] 
(h : κ -> ι) (hh : Function.Injective h) (r : γ) (f : Π₀ i, β i) : comapDomain h
 hh (r • f) = r • comapDomain h hh f
参数：β i；β i；h : κ -> ι；hh : Function.Injective h；r : γ；f : Π₀ i, β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.smul_apply`：smul_apply [forall i, Zero (β i)] [forall i, SMulZe
roClass γ (β i)] (b : γ) (v : Π₀ i, β i) (i : ι) : (b • v) i = b • v i
· 使用定理 `DFinsupp.comapDomain_apply`：comapDomain_apply [forall i, Zero (β i)] (h 
: κ -> ι) (hh : Function.Injective h) (f : Π₀ i, β i) (k : κ) : comapDomain h hh
 f k = f (h k)
-/
theorem comapDomain_smul [∀ i, Zero (β i)] [∀ i, SMulZeroClass γ (β i)]
    (h : κ → ι) (hh : Function.Injective h) (r : γ) (f : Π₀ i, β i) :
    comapDomain h hh (r • f) = r • comapDomain h hh f := by
  ext
  rw [smul_apply, comapDomain_apply, smul_apply, comapDomain_apply]

@[simp]
/-
**DFinsupp.comapDomain'_smul** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：∀ {ι : Type u} {γ : Type w} {β : ι → Type v} {κ : Type u_1} [inst : (i : ι
) → Zero (β i)]   [inst_1 : (i : ι) → SMulZeroClass γ (β i)] (h : κ → ι) {h' : ι
 → κ} (hh' : Function.LeftInverse h' h) (r : γ)   (f : Π₀ (i : ι), β i), DFinsup
p.comapDomain' h hh' (r • f) = r • DFinsupp.comapDomain' h hh' f
参数：i : ι；β i；i : ι；β i；h : κ → ι；hh' : Function.LeftInverse h' h；r : γ；f : Π₀ (i
 : ι), β i；r • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.smul_apply`：smul_apply [forall i, Zero (β i)] [forall i, SMulZe
roClass γ (β i)] (b : γ) (v : Π₀ i, β i) (i : ι) : (b • v) i = b • v i
· 使用定理 `DFinsupp.comapDomain'_apply`：∀ {ι : Type u} {β : ι → Type v} {κ : Type u
_1} [inst : (i : ι) → Zero (β i)] (h : κ → ι) {h' : ι → κ}   (hh' : Function.Lef
tInverse h' h) (f…
-/
theorem comapDomain'_smul [∀ i, Zero (β i)] [∀ i, SMulZeroClass γ (β i)]
    (h : κ → ι) {h' : ι → κ} (hh' : Function.LeftInverse h' h) (r : γ) (f : Π₀ i, β i) :
    comapDomain' h hh' (r • f) = r • comapDomain' h hh' f := by
  ext
  rw [smul_apply, comapDomain'_apply, smul_apply, comapDomain'_apply]

section SigmaCurry

variable {α : ι → Type*} {δ : ∀ i, α i → Type v}

/-
**DFinsupp.distribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `DFinsupp`。
形式化陈述：distribMulAction [Monoid γ] [forall i, AddMonoid (β i)] [forall i, Distrib
MulAction γ (β i)] : DistribMulAction γ (Π₀ i, β i)
参数：β i；β i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance distribMulAction₂ [Monoid γ] [∀ i j, AddMonoid (δ i j)]
    [∀ i j, DistribMulAction γ (δ i j)] : DistribMulAction γ (Π₀ (i : ι) (j : α i), δ i j) :=
  @DFinsupp.distribMulAction ι _ (fun i => Π₀ j, δ i j) _ _ _

end SigmaCurry

variable {α : Option ι → Type v}

/-
**DFinsupp.equivProdDFinsupp_smul** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：equivProdDFinsupp_smul [forall i, Zero (α i)] [forall i, SMulZeroClass γ (
α i)] (r : γ) (f : Π₀ i, α i) : equivProdDFinsupp (r • f) = r • equivProdDFinsup
p f
参数：α i；α i；r : γ；f : Π₀ i, α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `DFinsupp.smul_apply`：smul_apply [forall i, Zero (β i)] [forall i, SMulZe
roClass γ (β i)] (b : γ) (v : Π₀ i, β i) (i : ι) : (b • v) i = b • v i
· 使用定理 `DFinsupp.comapDomain_smul`：comapDomain_smul [forall i, Zero (β i)] [fora
ll i, SMulZeroClass γ (β i)] (h : κ -> ι) (hh : Function.Injective h) (r : γ) (f
 : Π₀ i, β i) :…
· 使用定理 `Option.some_injective`：some_injective (α : Type*) : Function.Injective (
@some α)
-/
theorem equivProdDFinsupp_smul [∀ i, Zero (α i)] [∀ i, SMulZeroClass γ (α i)]
    (r : γ) (f : Π₀ i, α i) : equivProdDFinsupp (r • f) = r • equivProdDFinsupp f :=
  Prod.ext (smul_apply _ _ _) (comapDomain_smul _ (Option.some_injective _) _ _)

end Equiv

end DFinsupp

