/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Fin.Tuple
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Data.Fintype.Option

/-!
# Pi types of modules

This file defines constructors for linear maps whose domains or codomains are pi types.

It contains theorems relating these to each other, as well as to `LinearMap.ker`.

## Main definitions

- pi types in the codomain:
  - `LinearMap.pi`
  - `LinearMap.single`
- pi types in the domain:
  - `LinearMap.proj`
  - `LinearMap.diag`

-/

@[expose] public section


universe u v w x y z u' v' w' x' y'

variable {R : Type u} {K : Type u'} {M : Type v} {V : Type v'} {M₂ : Type w} {V₂ : Type w'}
variable {M₃ : Type y} {V₃ : Type y'} {M₄ : Type z} {ι : Type x} {ι' : Type x'}

open Function Submodule

namespace LinearMap

universe i

variable [Semiring R] [AddCommMonoid M₂] [Module R M₂] [AddCommMonoid M₃] [Module R M₃]
  {φ : ι → Type i} [(i : ι) → AddCommMonoid (φ i)] [(i : ι) → Module R (φ i)]

/-- `pi` construction for linear functions. From a family of linear functions it produces a linear
function into a family of modules. -/
/-
**LinearMap.pi** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：pi (f : (i : ι) -> M₂ ->ₗ[R] φ i) : M₂ ->ₗ[R] (i : ι) -> φ i
参数：f : (i : ι) -> M₂ ->ₗ[R] φ i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`pi` construction for linear functions. From a family of linear functions it pro
duces a linear
function into a family of modules.
-/
def pi (f : (i : ι) → M₂ →ₗ[R] φ i) : M₂ →ₗ[R] (i : ι) → φ i :=
  { AddHom.pi fun i => (f i).toAddHom with
    toFun := fun c i => f i c
    map_smul' := fun _ _ => funext fun i => (f i).map_smul _ _ }

@[simp]
/-
**LinearMap.pi_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：pi_apply (f : (i : ι) -> M₂ ->ₗ[R] φ i) (c : M₂) (i : ι) : pi f c i = f i 
c
参数：f : (i : ι) -> M₂ ->ₗ[R] φ i；c : M₂；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pi_apply (f : (i : ι) → M₂ →ₗ[R] φ i) (c : M₂) (i : ι) : pi f c i = f i c :=
  rfl
/-
**LinearMap.ker_pi** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ker_pi (f : (i : ι) -> M₂ ->ₗ[R] φ i) : ker (pi f) = ⨅ i : ι, ker (f i)
参数：f : (i : ι) -> M₂ ->ₗ[R] φ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ker_pi (f : (i : ι) → M₂ →ₗ[R] φ i) : ker (pi f) = ⨅ i : ι, ker (f i) := by
  ext c; simp [funext_iff]
/-
**LinearMap.pi_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：pi_eq_zero (f : (i : ι) -> M₂ ->ₗ[R] φ i) : pi f = 0 ↔ forall i, f i = 0
参数：f : (i : ι) -> M₂ ->ₗ[R] φ i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem pi_eq_zero (f : (i : ι) → M₂ →ₗ[R] φ i) : pi f = 0 ↔ ∀ i, f i = 0 := by
  simp only [LinearMap.ext_iff, pi_apply, funext_iff]
  exact ⟨fun h a b => h b a, fun h a b => h b a⟩
/-
**LinearMap.pi_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：pi_zero : pi (fun _ => 0 : (i : ι) -> M₂ ->ₗ[R] φ i) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem pi_zero : pi (fun _ => 0 : (i : ι) → M₂ →ₗ[R] φ i) = 0 := by ext; rfl
/-
**LinearMap.pi_comp** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：pi_comp (f : (i : ι) -> M₂ ->ₗ[R] φ i) (g : M₃ ->ₗ[R] M₂) : (pi f).comp g 
= pi fun i => (f i).comp g
参数：f : (i : ι) -> M₂ ->ₗ[R] φ i；g : M₃ ->ₗ[R] M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pi_comp (f : (i : ι) → M₂ →ₗ[R] φ i) (g : M₃ →ₗ[R] M₂) :
    (pi f).comp g = pi fun i => (f i).comp g :=
  rfl

/-- The constant linear map, taking `x` to `Function.const ι x`. -/
/-
**LinearMap.const** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：const : M₂ ->ₗ[R] (ι -> M₂)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constant linear map, taking `x` to `Function.const ι x`.
-/
def const : M₂ →ₗ[R] (ι → M₂) := pi fun _ ↦ .id
/-
**LinearMap.const_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u} {M₂ : Type w} {ι : Type x} [inst : Semiring R] [inst_1 : Ad
dCommMonoid M₂] [inst_2 : _root_.Module R M₂]   (x : M₂), LinearMap.const x = Fu
nction.const ι x
参数：x : M₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma const_apply (x : M₂) : LinearMap.const (R := R) x = Function.const ι x := rfl

/-- The projections from a family of modules are linear maps.

Note: this definition would be called `Pi.evalLinearMap` if we followed the pattern established by
`Pi.evalAddHom`, `Pi.evalMonoidHom`, `Pi.evalRingHom`, ... -/
/-
**LinearMap.proj** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：proj (i : ι) : ((i : ι) -> φ i) ->ₗ[R] φ i where toFun
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projections from a family of modules are linear maps.

Note: this definition would be called `Pi.evalLinearMap` if we followed the patt
ern established by
`Pi.evalAddHom`, `Pi.evalMonoidHom`, `Pi.evalRingHom`, ...
-/
def proj (i : ι) : ((i : ι) → φ i) →ₗ[R] φ i where
  toFun := Function.eval i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
/-
**LinearMap.coe_proj** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：coe_proj (i : ι) : ⇑(proj i : ((i : ι) -> φ i) ->ₗ[R] φ i) = Function.eval
 i
参数：i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_proj (i : ι) : ⇑(proj i : ((i : ι) → φ i) →ₗ[R] φ i) = Function.eval i :=
  rfl

@[simp]
/-
**LinearMap.toAddMonoidHom_proj** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：toAddMonoidHom_proj (i : ι) : (proj i).toAddMonoidHom (R
参数：i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAddMonoidHom_proj (i : ι) : (proj i).toAddMonoidHom (R := R) = Pi.evalAddMonoidHom φ i :=
  rfl
/-
**LinearMap.proj_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：proj_apply (i : ι) (b : (i : ι) -> φ i) : (proj i : ((i : ι) -> φ i) ->ₗ[R
] φ i) b = b i
参数：i : ι；b : (i : ι) -> φ i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem proj_apply (i : ι) (b : (i : ι) → φ i) : (proj i : ((i : ι) → φ i) →ₗ[R] φ i) b = b i :=
  rfl

@[simp]
/-
**LinearMap.proj_pi** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：proj_pi (f : (i : ι) -> M₂ ->ₗ[R] φ i) (i : ι) : (proj i).comp (pi f) = f 
i
参数：f : (i : ι) -> M₂ ->ₗ[R] φ i；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem proj_pi (f : (i : ι) → M₂ →ₗ[R] φ i) (i : ι) : (proj i).comp (pi f) = f i := rfl

@[simp]
/-
**LinearMap.pi_proj** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：pi_proj : pi proj = LinearMap.id (R
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pi_proj : pi proj = LinearMap.id (R := R) (M := ∀ i, φ i) := rfl

@[simp]
/-
**LinearMap.pi_proj_comp** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：pi_proj_comp (f : M₂ ->ₗ[R] forall i, φ i) : pi (proj · ∘ₗ f) = f
参数：f : M₂ ->ₗ[R] forall i, φ i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pi_proj_comp (f : M₂ →ₗ[R] ∀ i, φ i) : pi (proj · ∘ₗ f) = f := rfl
/-
**LinearMap.proj_surjective** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：proj_surjective (i : ι) : Surjective (proj i : ((i : ι) -> φ i) ->ₗ[R] φ i
)
参数：i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.surjective_eval`：surjective_eval {α : Sort u} {β : α -> Sort v}
 [h : forall a, Nonempty (β a)] (a : α) : Surjective (eval a : (forall a, β a) -
> β a)
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
-/
theorem proj_surjective (i : ι) : Surjective (proj i : ((i : ι) → φ i) →ₗ[R] φ i) :=
  surjective_eval i

/-- Homs to a pi module are canonically identified with a product of hom types, even linearly so. -/
/-
**LinearMap._root_.LinearEquiv.linearMapPi** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Homs to a pi module are canonically identified with a product of hom types, even
 linearly so.
-/
@[simps] def _root_.LinearEquiv.linearMapPi (S) [Semiring S] [(i : ι) → Module S (φ i)]
    [∀ i, SMulCommClass R S (φ i)] : (Π i, M₂ →ₗ[R] φ i) ≃ₗ[S] M₂ →ₗ[R] Π i, φ i where
  toFun := pi
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f i := proj i ∘ₗ f
  left_inv _ := rfl
  right_inv _ := rfl
/-
**LinearMap.iInf_ker_proj** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：iInf_ker_proj : (⨅ i, ker (proj i : ((i : ι) -> φ i) ->ₗ[R] φ i) : Submodu
le R ((i : ι) -> φ i)) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_unique`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ → a = ⊥
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SetLike.le_def`：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x 
in T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Submodule.mem_bot`：mem_bot {x : M} : x in (⊥ : Submodule R M) ↔ x = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem iInf_ker_proj : (⨅ i, ker (proj i : ((i : ι) → φ i) →ₗ[R] φ i) :
    Submodule R ((i : ι) → φ i)) = ⊥ :=
  bot_unique <|
    SetLike.le_def.2 fun a h => by
      simp only [mem_iInf, mem_ker, proj_apply] at h
      exact (mem_bot _).2 (funext fun i => h i)
/-
**LinearMap.CompatibleSMul.pi** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.CompatibleSMu
l`。
形式化陈述：∀ (R : Type u_1) (S : Type u_2) (M : Type u_3) (N : Type u_4) (ι : Type u_
5) [inst : Semiring S]   [inst_1 : AddCommMonoid M] [inst_2 : AddCommMonoid N] [
inst_3 : SMul R M] [inst_4 : SMul R N]   [inst_5 : _root_.Module S M] [inst_6 : 
_root_.Module S N] [LinearMap.CompatibleSMul M N R S],   LinearMap.CompatibleSMu
l M (ι → N) R S
参数：R : Type u_1；S : Type u_2；M : Type u_3；N : Type u_4；ι : Type u_5；ι → N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LinearMap.map_smul_of_tower`：map_smul_of_tower [CompatibleSMul M M₂ R S]
 (fₗ : M ->ₗ[S] M₂) (c : R) (x : M) : fₗ (c • x) = c • fₗ x
-/
instance CompatibleSMul.pi (R S M N ι : Type*) [Semiring S]
    [AddCommMonoid M] [AddCommMonoid N] [SMul R M] [SMul R N] [Module S M] [Module S N]
    [LinearMap.CompatibleSMul M N R S] : LinearMap.CompatibleSMul M (ι → N) R S where
  map_smul f r m := by ext i; apply ((LinearMap.proj i).comp f).map_smul_of_tower

/-- Construct a linear map between two (dependent) function spaces
by applying index-dependent linear maps to the coordinates.
A bundled version of `Pi.map`.

If the index type is finite, then this map can be seen as a “block diagonal” map
between indexed products of modules. -/
/-
**LinearMap.piMap** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：piMap {ψ : ι -> Type*} [forall i, AddCommMonoid (ψ i)] [forall i, Module R
 (ψ i)] (f : forall i, φ i ->ₗ[R] ψ i) : (forall i, φ i) ->ₗ[R] (forall i, ψ i)
参数：ψ i；ψ i；f : forall i, φ i ->ₗ[R] ψ i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a linear map between two (dependent) function spaces
by applying index-dependent linear maps to the coordinates.
A bundled version of `Pi.map`.

If the index type is finite, then this map can be seen as a “block diagonal” map
between indexed products of modules.
-/
def piMap {ψ : ι → Type*} [∀ i, AddCommMonoid (ψ i)] [∀ i, Module R (ψ i)]
    (f : ∀ i, φ i →ₗ[R] ψ i) : (∀ i, φ i) →ₗ[R] (∀ i, ψ i) :=
  .pi fun i ↦ f i ∘ₗ proj i

@[simp]
/-
**LinearMap.coe_piMap** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：coe_piMap {ψ : ι -> Type*} [forall i, AddCommMonoid (ψ i)] [forall i, Modu
le R (ψ i)] (f : forall i, φ i ->ₗ[R] ψ i) : ⇑(piMap f) = Pi.map fun i => f i
参数：ψ i；ψ i；f : forall i, φ i ->ₗ[R] ψ i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_piMap {ψ : ι → Type*} [∀ i, AddCommMonoid (ψ i)] [∀ i, Module R (ψ i)]
    (f : ∀ i, φ i →ₗ[R] ψ i) : ⇑(piMap f) = Pi.map fun i ↦ f i :=
  rfl

/-- Linear map between the function spaces `I → M₂` and `I → M₃`, induced by a linear map `f`
between `M₂` and `M₃`. -/
@[simps]
/-
**LinearMap.compLeft** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：{R : Type u} →   {M₂ : Type w} →     {M₃ : Type y} →       [inst : Semirin
g R] →         [inst_1 : AddCommMonoid M₂] →           [inst_2 : _root_.Module R
 M₂] →             [inst_3 : AddCommMonoid M₃] →               [inst_4 : _root_.
Module R M₃] → (M₂ →ₗ[R] M₃) → (I : Type u_1) → (I → M₂) →ₗ[R] I → M₃
参数：M₂ →ₗ[R] M₃；I : Type u_1；I → M₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Linear map between the function spaces `I → M₂` and `I → M₃`, induced by a linea
r map `f`
between `M₂` and `M₃`.
-/
protected def compLeft (f : M₂ →ₗ[R] M₃) (I : Type*) : (I → M₂) →ₗ[R] I → M₃ :=
  { f.toAddMonoidHom.compLeft I with
    toFun := fun h => f ∘ h
    map_smul' := fun c h => by
      ext x
      exact f.map_smul' c (h x) }
/-
**LinearMap.apply_single** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：apply_single [AddCommMonoid M] [Module R M] [DecidableEq ι] (f : (i : ι) -
> φ i ->ₗ[R] M) (i j : ι) (x : φ i) : f j (Pi.single i x j) = (Pi.single i (f i 
x) : ι -> M) j
参数：f : (i : ι) -> φ i ->ₗ[R] M；i j : ι；x : φ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.apply_single`：∀ {ι : Type u_1} {M : ι → Type u_6} {N : ι → Type u_7} 
[inst : (i : ι) → Zero (M i)] [inst_1 : (i : ι) → Zero (N i)]   [inst_2 : Decida
bleEq…
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
-/
theorem apply_single [AddCommMonoid M] [Module R M] [DecidableEq ι] (f : (i : ι) → φ i →ₗ[R] M)
    (i j : ι) (x : φ i) : f j (Pi.single i x j) = (Pi.single i (f i x) : ι → M) j :=
  Pi.apply_single (fun i => f i) (fun i => (f i).map_zero) _ _ _

variable (R φ)

/-- The `LinearMap` version of `AddMonoidHom.single` and `Pi.single`. -/
/-
**LinearMap.single** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：single [DecidableEq ι] (i : ι) : φ i ->ₗ[R] (i : ι) -> φ i
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `LinearMap` version of `AddMonoidHom.single` and `Pi.single`.
-/
def single [DecidableEq ι] (i : ι) : φ i →ₗ[R] (i : ι) → φ i :=
  { AddMonoidHom.single φ i with
    toFun := Pi.single i
    map_smul' := Pi.single_smul i }
/-
**LinearMap.single_apply** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：single_apply [DecidableEq ι] {i : ι} (v : φ i) : single R φ i v = Pi.singl
e i v
参数：v : φ i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma single_apply [DecidableEq ι] {i : ι} (v : φ i) :
    single R φ i v = Pi.single i v :=
  rfl
/-
**LinearMap.sum_single_apply** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：sum_single_apply [Fintype ι] [DecidableEq ι] (v : Π i, φ i) : ∑ i, Pi.sing
le i (v i) = v
参数：v : Π i, φ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finset.sum_pi_single`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : Decida
bleEq ι] [inst_1 : (a : ι) → AddCommMonoid (M a)] (a : ι)   (f : (a : ι) → M a) 
(s : Finse…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sum_single_apply [Fintype ι] [DecidableEq ι] (v : Π i, φ i) :
    ∑ i, Pi.single i (v i) = v := by ext; simp

@[simp]
/-
**LinearMap.coe_single** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：coe_single [DecidableEq ι] (i : ι) : ⇑(single R φ i : φ i ->ₗ[R] (i : ι) -
> φ i) = Pi.single i
参数：i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_single [DecidableEq ι] (i : ι) :
    ⇑(single R φ i : φ i →ₗ[R] (i : ι) → φ i) = Pi.single i :=
  rfl

variable [DecidableEq ι]
/-
**LinearMap.proj_comp_single_same** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：proj_comp_single_same (i : ι) : (proj i).comp (single R φ i) = id
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
-/
theorem proj_comp_single_same (i : ι) : (proj i).comp (single R φ i) = id :=
  LinearMap.ext <| Pi.single_eq_same i
/-
**LinearMap.proj_comp_single_ne** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：proj_comp_single_ne (i j : ι) (h : i != j) : (proj i).comp (single R φ j) 
= 0
参数：i j : ι；h : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
-/
theorem proj_comp_single_ne (i j : ι) (h : i ≠ j) : (proj i).comp (single R φ j) = 0 :=
  LinearMap.ext <| Pi.single_eq_of_ne h
/-
**LinearMap.iSup_range_single_le_iInf_ker_proj** 是 Mathlib 中的一个定理，位于命名空间 `Linear
Map`。
形式化陈述：iSup_range_single_le_iInf_ker_proj (I J : Set ι) (h : Disjoint I J) : ⨆ i 
in I, range (single R φ i) <= ⨅ i in J, ker (proj i : (forall i, φ i) ->ₗ[R] φ i
)
参数：I J : Set ι；h : Disjoint I J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.range_le_iff_comap`：range_le_iff_comap [RingHomSurjective τ₁₂]
 {f : M ->ₛₗ[τ₁₂] M₂} {p : Submodule R₂ M₂} : range f <= p ↔ comap f p = ⊤
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.comap_iInf`：comap_iInf {ι : Sort*} (f : M ->ₛₗ[σ₁₂] M₂) (p : ι
 -> Submodule R₂ M₂) : comap f (⨅ i, p i) = ⨅ i, comap f (p i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LinearMap.proj_comp_single_ne`：proj_comp_single_ne (i j : ι) (h : i != j
) : (proj i).comp (single R φ j) = 0
· 使用定理 `Disjoint.le_bot`：Disjoint.le_bot : Disjoint a b -> a ⊓ b <= ⊥
· 使用定理 `LinearMap.zero_apply`：zero_apply (x : M) : (0 : M ->ₛₗ[σ₁₂] M₂) x = 0
-/
theorem iSup_range_single_le_iInf_ker_proj (I J : Set ι) (h : Disjoint I J) :
    ⨆ i ∈ I, range (single R φ i) ≤ ⨅ i ∈ J, ker (proj i : (∀ i, φ i) →ₗ[R] φ i) := by
  refine iSup_le fun i => iSup_le fun hi => range_le_iff_comap.2 ?_
  simp only [← ker_comp, eq_top_iff, SetLike.le_def, mem_ker, comap_iInf, mem_iInf]
  rintro b - j hj
  rw [proj_comp_single_ne R φ j i, zero_apply]
  rintro rfl
  exact h.le_bot ⟨hi, hj⟩
/-
**LinearMap.iInf_ker_proj_le_iSup_range_single** 是 Mathlib 中的一个定理，位于命名空间 `Linear
Map`。
形式化陈述：iInf_ker_proj_le_iSup_range_single {I J : Set ι} (hI : I.Finite) (hIJ : Co
disjoint I J) : ⨅ i in J, ker (proj i : (forall i, φ i) ->ₗ[R] φ i) <= ⨆ i in I,
 range (single R φ i)
参数：hI : I.Finite；hIJ : Codisjoint I J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.instCanLiftFinsetCoeFinite`：∀ {α : Type u}, CanLift (Set α) (Finset 
α) SetLike.coe Set.Finite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Codisjoint.top_le`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : 
OrderTop α] {a b : α}, Codisjoint a b → ⊤ ≤ a ⊔ b
· 使用定理 `trivial`：True
· 使用定理 `Submodule.sum_mem_biSup`：sum_mem_biSup {ι : Type*} {s : Finset ι} {f : ι
 -> M} {p : ι -> Submodule R M} (h : forall i in s, f i in p i) : (∑ i in s, f i
) in ⨆ i in s…
· 使用定理 `LinearMap.mem_range_self`：mem_range_self [RingHomSurjective τ₁₂] (f : M 
->ₛₗ[τ₁₂] M₂) (x : M) : f x in range f
-/
theorem iInf_ker_proj_le_iSup_range_single {I J : Set ι} (hI : I.Finite) (hIJ : Codisjoint I J) :
    ⨅ i ∈ J, ker (proj i : (∀ i, φ i) →ₗ[R] φ i) ≤ ⨆ i ∈ I, range (single R φ i) := by
  lift I to Finset ι using hI
  intro b hb
  simp only [mem_iInf, mem_ker, proj_apply] at hb
  rw [←
    show (∑ i ∈ I, Pi.single i (b i)) = b by
      ext i
      rw [Finset.sum_apply, ← Pi.single_eq_same i (b i)]
      refine Finset.sum_eq_single i (fun j _ ne => Pi.single_eq_of_ne ne.symm _) ?_
      intro hiI
      rw [Pi.single_eq_same]
      exact hb _ ((hIJ.top_le trivial).resolve_left hiI)]
  exact sum_mem_biSup fun i _ => mem_range_self (single R φ i) (b i)
/-
**LinearMap.iSup_range_single_eq_iInf_ker_proj** 是 Mathlib 中的一个定理，位于命名空间 `Linear
Map`。
形式化陈述：iSup_range_single_eq_iInf_ker_proj {I J : Set ι} (hIJ : IsCompl I J) (hI :
 I.Finite) : ⨆ i in I, range (single R φ i) = ⨅ i in J, ker (proj i : (forall i,
 φ i) ->ₗ[R] φ i)
参数：hIJ : IsCompl I J；hI : I.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LinearMap.iSup_range_single_le_iInf_ker_proj`：iSup_range_single_le_iInf_
ker_proj (I J : Set ι) (h : Disjoint I J) : ⨆ i in I, range (single R φ i) <= ⨅ 
i in J, ker (proj i : (forall i, φ…
· 使用定理 `IsCompl.disjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bou
ndedOrder α] {x y : α}, IsCompl x y → Disjoint x y
· 使用定理 `LinearMap.iInf_ker_proj_le_iSup_range_single`：iInf_ker_proj_le_iSup_rang
e_single {I J : Set ι} (hI : I.Finite) (hIJ : Codisjoint I J) : ⨅ i in J, ker (p
roj i : (forall i, φ i) ->ₗ[R] φ i…
· 使用定理 `IsCompl.codisjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : B
oundedOrder α] {x y : α}, IsCompl x y → Codisjoint x y
-/
theorem iSup_range_single_eq_iInf_ker_proj {I J : Set ι} (hIJ : IsCompl I J) (hI : I.Finite) :
    ⨆ i ∈ I, range (single R φ i) = ⨅ i ∈ J, ker (proj i : (∀ i, φ i) →ₗ[R] φ i) :=
  le_antisymm (iSup_range_single_le_iInf_ker_proj _ _ _ _ hIJ.disjoint) <|
    iInf_ker_proj_le_iSup_range_single R φ hI hIJ.codisjoint
/-
**LinearMap.iSup_range_single** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：iSup_range_single [Finite ι] : ⨆ i, range (single R φ i) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iInf_neg`：∀ {α : Type u_1} [inst : CompleteLattice α] {p : Prop} {f : p 
→ α}, ¬p → ⨅ (h : p), f h = ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iInf_top`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α], ⨅ 
x, ⊤ = ⊤
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `iSup_pos`：iSup_pos {p : Prop} {f : p -> α} (hp : p) : ⨆ h : p, f h = f h
p
· 使用定理 `LinearMap.iInf_ker_proj_le_iSup_range_single`：iInf_ker_proj_le_iSup_rang
e_single {I J : Set ι} (hI : I.Finite) (hIJ : Codisjoint I J) : ⨅ i in J, ker (p
roj i : (forall i, φ i) ->ₗ[R] φ i…
· 使用定理 `Set.finite_univ`：∀ {α : Type u} [Finite α], Set.univ.Finite
· 使用定理 `IsCompl.codisjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : B
oundedOrder α] {x y : α}, IsCompl x y → Codisjoint x y
· 使用定理 `isCompl_top_bot`：isCompl_top_bot : IsCompl (⊤ : α) ⊥
-/
theorem iSup_range_single [Finite ι] : ⨆ i, range (single R φ i) = ⊤ := by
  simpa using iInf_ker_proj_le_iSup_range_single R φ Set.finite_univ isCompl_top_bot.codisjoint
/-
**LinearMap.disjoint_single_single** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：disjoint_single_single (I J : Set ι) (h : Disjoint I J) : Disjoint (⨆ i in
 I, range (single R φ i)) (⨆ i in J, range (single R φ i))
参数：I J : Set ι；h : Disjoint I J。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
· 使用定理 `LinearMap.iSup_range_single_le_iInf_ker_proj`：iSup_range_single_le_iInf_
ker_proj (I J : Set ι) (h : Disjoint I J) : ⨆ i in I, range (single R φ i) <= ⨅ 
i in J, ker (proj i : (forall i, φ…
· 使用定理 `disjoint_compl_right`：disjoint_compl_right : Disjoint a aᶜ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Disjoint.le_bot`：Disjoint.le_bot : Disjoint a b -> a ⊓ b <= ⊥
-/
theorem disjoint_single_single (I J : Set ι) (h : Disjoint I J) :
    Disjoint (⨆ i ∈ I, range (single R φ i)) (⨆ i ∈ J, range (single R φ i)) := by
  refine
    Disjoint.mono (iSup_range_single_le_iInf_ker_proj _ _ _ _ <| disjoint_compl_right)
      (iSup_range_single_le_iInf_ker_proj _ _ _ _ <| disjoint_compl_right) ?_
  simp only [disjoint_iff_inf_le, SetLike.le_def, mem_iInf, mem_inf, mem_ker, mem_bot, proj_apply,
    funext_iff]
  rintro b ⟨hI, hJ⟩ i
  classical
    by_cases hiI : i ∈ I
    · by_cases hiJ : i ∈ J
      · exact (h.le_bot ⟨hiI, hiJ⟩).elim
      · exact hJ i hiJ
    · exact hI i hiI

/-- The linear equivalence between linear functions on a finite product of modules and
families of functions on these modules. See note [bundled maps over different rings]. -/
@[simps symm_apply]
/-
**LinearMap.lsum** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：lsum (S) [AddCommMonoid M] [Module R M] [Fintype ι] [Semiring S] [Module S
 M] [SMulCommClass R S M] : ((i : ι) -> φ i ->ₗ[R] M) ≃ₗ[S] ((i : ι) -> φ i) ->ₗ
[R] M where toFun f
参数：S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear equivalence between linear functions on a finite product of modules a
nd
families of functions on these modules. See note [bundled maps over different ri
ngs].
-/
def lsum (S) [AddCommMonoid M] [Module R M] [Fintype ι] [Semiring S] [Module S M]
    [SMulCommClass R S M] : ((i : ι) → φ i →ₗ[R] M) ≃ₗ[S] ((i : ι) → φ i) →ₗ[R] M where
  toFun f := ∑ i : ι, (f i).comp (proj i)
  invFun f i := f.comp (single R φ i)
  map_add' f g := by simp only [Pi.add_apply, add_comp, Finset.sum_add_distrib]
  map_smul' c f := by simp only [Pi.smul_apply, smul_comp, Finset.smul_sum, RingHom.id_apply]
  left_inv f := by
    ext i x
    simp [apply_single]
  right_inv f := by
    ext x
    suffices f (∑ j, Pi.single j (x j)) = f x by simpa [apply_single]
    rw [Finset.univ_sum_single]

@[simp]
/-
**LinearMap.lsum_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：lsum_apply (S) [AddCommMonoid M] [Module R M] [Fintype ι] [Semiring S] [Mo
dule S M] [SMulCommClass R S M] (f : (i : ι) -> φ i ->ₗ[R] M) : lsum R φ S f = ∑
 i : ι, (f i).comp (proj i)
参数：S；f : (i : ι) -> φ i ->ₗ[R] M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lsum_apply (S) [AddCommMonoid M] [Module R M] [Fintype ι] [Semiring S]
    [Module S M] [SMulCommClass R S M] (f : (i : ι) → φ i →ₗ[R] M) :
    lsum R φ S f = ∑ i : ι, (f i).comp (proj i) := rfl
/-
**LinearMap.lsum_piSingle** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：lsum_piSingle (S) [AddCommMonoid M] [Module R M] [Fintype ι] [Semiring S] 
[Module S M] [SMulCommClass R S M] (f : (i : ι) -> φ i ->ₗ[R] M) (i : ι) (x : φ 
i) : lsum R φ S f (Pi.single i x) = f i x
参数：S；f : (i : ι) -> φ i ->ₗ[R] M；i : ι；x : φ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.sum_apply`：sum_apply (t : Finset ι) (f : ι -> M ->ₛₗ[σ₁₂] M₂) 
(b : M) : (∑ d in t, f d) b = ∑ d in t, f d b
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `LinearMap.apply_single`：apply_single [AddCommMonoid M] [Module R M] [Dec
idableEq ι] (f : (i : ι) -> φ i ->ₗ[R] M) (i j : ι) (x : φ i) : f j (Pi.single i
 x j) = (Pi.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Fintype.sum_pi_single'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommM
onoid M] [inst_1 : Fintype ι] [inst_2 : DecidableEq ι] (i : ι) (a : M),   ∑ j, P
i.single i a…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lsum_piSingle (S) [AddCommMonoid M] [Module R M] [Fintype ι] [Semiring S]
    [Module S M] [SMulCommClass R S M] (f : (i : ι) → φ i →ₗ[R] M) (i : ι) (x : φ i) :
    lsum R φ S f (Pi.single i x) = f i x := by
  simp_rw [lsum_apply, sum_apply, comp_apply, proj_apply, apply_single, Fintype.sum_pi_single']

@[simp high]
/-
**LinearMap.lsum_single** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：lsum_single (S) [Fintype ι] [Semiring S] [forall i, Module S (φ i)] [foral
l i, SMulCommClass R S (φ i)] : LinearMap.lsum R φ S (LinearMap.single R φ) = Li
nearMap.id
参数：S；φ i；φ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearMap.coe_sum`：coe_sum {ι : Type*} (t : Finset ι) (f : ι -> M ->ₛₗ[σ
₁₂] M₂) : ⇑(∑ i in t, f i) = ∑ i in t, (f i : M -> M₂)
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.univ_sum_single`：∀ {I : Type u_7} [inst : DecidableEq I] {M : I →
 Type u_8} [inst_1 : (i : I) → AddCommMonoid (M i)] [inst_2 : Fintype I]   (f : 
(i : I) → M …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lsum_single (S) [Fintype ι] [Semiring S]
    [∀ i, Module S (φ i)] [∀ i, SMulCommClass R S (φ i)] :
    LinearMap.lsum R φ S (LinearMap.single R φ) = LinearMap.id :=
  LinearMap.ext fun x => by simp [Finset.univ_sum_single]

variable {R φ}

section Ext

variable [Finite ι] [AddCommMonoid M] [Module R M] {f g : ((i : ι) → φ i) →ₗ[R] M}

/-
**LinearMap.pi_ext** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：pi_ext (h : forall i x, f (Pi.single i x) = g (Pi.single i x)) : f = g
参数：h : forall i x, f (Pi.single i x) = g (Pi.single i x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.toAddMonoidHom_injective`：toAddMonoidHom_injective : Function.
Injective (toAddMonoidHom : (M ->ₛₗ[σ] M₃) -> M ->+ M₃)
· 使用定理 `AddMonoidHom.functions_ext`：∀ {I : Type u_7} [inst : DecidableEq I] {M :
 I → Type u_8} [inst_1 : (i : I) → AddCommMonoid (M i)] [Finite I]   (N : Type u
_9) [inst_3 : Ad…
-/
theorem pi_ext (h : ∀ i x, f (Pi.single i x) = g (Pi.single i x)) : f = g :=
  toAddMonoidHom_injective <| AddMonoidHom.functions_ext _ _ _ h
/-
**LinearMap.pi_ext_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：pi_ext_iff : f = g ↔ forall i x, f (Pi.single i x) = g (Pi.single i x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.pi_ext`：pi_ext (h : forall i x, f (Pi.single i x) = g (Pi.sing
le i x)) : f = g
-/
theorem pi_ext_iff : f = g ↔ ∀ i x, f (Pi.single i x) = g (Pi.single i x) :=
  ⟨fun h _ _ => h ▸ rfl, pi_ext⟩

/-- This is used as the ext lemma instead of `LinearMap.pi_ext` for reasons explained in
note [partially-applied ext lemmas]. -/
@[ext]
/-
**LinearMap.pi_ext'** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：pi_ext' (h : forall i, f.comp (single R φ i) = g.comp (single R φ i)) : f 
= g
参数：h : forall i, f.comp (single R φ i) = g.comp (single R φ i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.pi_ext`：pi_ext (h : forall i x, f (Pi.single i x) = g (Pi.sing
le i x)) : f = g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…

--- 原说明 ---
This is used as the ext lemma instead of `LinearMap.pi_ext` for reasons explaine
d in
note [partially-applied ext lemmas].
-/
theorem pi_ext' (h : ∀ i, f.comp (single R φ i) = g.comp (single R φ i)) : f = g := by
  refine pi_ext fun i x => ?_
  convert! LinearMap.congr_fun (h i) x

end Ext

section

variable (R φ)

/-- If `I` and `J` are disjoint index sets, the product of the kernels of the `J`th projections of
`φ` is linearly equivalent to the product over `I`. -/
/-
**LinearMap.iInfKerProjEquiv** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：iInfKerProjEquiv {I J : Set ι} [DecidablePred fun i => i in I] (hd : Disjo
int I J) (hu : Set.univ subseteq I union J) : (⨅ i in J, ker (proj i : ((i : ι) 
-> φ i) ->ₗ[R] φ i) : Submodule R ((i : ι) -> φ i)) ≃ₗ[R] (i : I) -> φ i
参数：hd : Disjoint I J；hu : Set.univ subseteq I union J。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `I` and `J` are disjoint index sets, the product of the kernels of the `J`th 
projections of
`φ` is linearly equivalent to the product over `I`.
-/
def iInfKerProjEquiv {I J : Set ι} [DecidablePred fun i => i ∈ I] (hd : Disjoint I J)
    (hu : Set.univ ⊆ I ∪ J) :
    (⨅ i ∈ J, ker (proj i : ((i : ι) → φ i) →ₗ[R] φ i) :
    Submodule R ((i : ι) → φ i)) ≃ₗ[R] (i : I) → φ i := by
  refine
    LinearEquiv.ofLinearMap (pi fun i => (proj (i : ι)).comp (Submodule.subtype _))
      (codRestrict _ (pi fun i => if h : i ∈ I then proj (⟨i, h⟩ : I) else 0) ?_) ?_ ?_
  · intro b
    simp only [mem_iInf, mem_ker, proj_apply, pi_apply]
    intro j hjJ
    have : j ∉ I := fun hjI => hd.le_bot ⟨hjI, hjJ⟩
    rw [dif_neg this, zero_apply]
  · simp only [pi_comp, comp_assoc, subtype_comp_codRestrict, proj_pi, Subtype.coe_prop]
    ext b ⟨j, hj⟩
    simp only [dif_pos,
      LinearMap.coe_proj, LinearMap.pi_apply]
    rfl
  · ext1 ⟨b, hb⟩
    apply Subtype.ext
    ext j
    have hb : ∀ i ∈ J, b i = 0 := by
      simpa only [mem_iInf, mem_ker, proj_apply] using (mem_iInf _).1 hb
    simp only [comp_apply, pi_apply, id_apply, codRestrict_apply]
    split_ifs with h
    · rfl
    · exact (hb _ <| (hu trivial).resolve_left h).symm

end

section

/-- `diag i j` is the identity map if `i = j`. Otherwise it is the constant 0 map. -/
/-
**LinearMap.diag** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：diag (i j : ι) : φ i ->ₗ[R] φ j
参数：i j : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`diag i j` is the identity map if `i = j`. Otherwise it is the constant 0 map.
-/
def diag (i j : ι) : φ i →ₗ[R] φ j :=
  @Function.update ι (fun j => φ i →ₗ[R] φ j) _ 0 i id j
/-
**LinearMap.update_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：update_apply (f : (i : ι) -> M₂ ->ₗ[R] φ i) (c : M₂) (i j : ι) (b : M₂ ->ₗ
[R] φ i) : (update f i b j) c = update (fun i => f i c) i (b c) j
参数：f : (i : ι) -> M₂ ->ₗ[R] φ i；c : M₂；i j : ι；b : M₂ ->ₗ[R] φ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
-/
theorem update_apply (f : (i : ι) → M₂ →ₗ[R] φ i) (c : M₂) (i j : ι) (b : M₂ →ₗ[R] φ i) :
    (update f i b j) c = update (fun i => f i c) i (b c) j := by
  by_cases h : j = i
  · rw [h, update_self, update_self]
  · rw [update_of_ne h, update_of_ne h]

variable (R φ)
/-
**LinearMap.single_eq_pi_diag** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：single_eq_pi_diag (i : ι) : single R φ i = pi (diag i)
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.update_apply`：update_apply (f : (i : ι) -> M₂ ->ₗ[R] φ i) (c :
 M₂) (i j : ι) (b : M₂ ->ₗ[R] φ i) : (update f i b j) c = update (fun i => f i c
) i (b c) j
-/
theorem single_eq_pi_diag (i : ι) : single R φ i = pi (diag i) := by
  ext x j
  convert! (update_apply 0 x i j _).symm
  rfl
/-
**LinearMap.ker_single** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ker_single (i : ι) : ker (single R φ i) = ⊥
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ker_eq_bot_of_injective`：ker_eq_bot_of_injective {f : M ->ₛₗ[τ
₁₂] M₂} (hf : Injective f) : ker f = ⊥
· 使用定理 `Pi.single_injective`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι)
 → Zero (M i)] [inst_1 : DecidableEq ι] (i : ι),   Function.Injective (Pi.single
 i)
-/
theorem ker_single (i : ι) : ker (single R φ i) = ⊥ :=
  ker_eq_bot_of_injective <| Pi.single_injective _
/-
**LinearMap.proj_comp_single** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：proj_comp_single (i j : ι) : (proj i).comp (single R φ j) = diag j i
参数：i j : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.single_eq_pi_diag`：single_eq_pi_diag (i : ι) : single R φ i = 
pi (diag i)
· 使用定理 `LinearMap.proj_pi`：proj_pi (f : (i : ι) -> M₂ ->ₗ[R] φ i) (i : ι) : (pro
j i).comp (pi f) = f i
-/
theorem proj_comp_single (i j : ι) : (proj i).comp (single R φ j) = diag j i := by
  rw [single_eq_pi_diag, proj_pi]

end

/-- A linear map `f` applied to `x : ι → R` can be computed using the image under `f` of elements
of the canonical basis. -/
/-
**LinearMap.pi_apply_eq_sum_univ** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：pi_apply_eq_sum_univ [Fintype ι] (f : (ι -> R) ->ₗ[R] M₂) (x : ι -> R) : f
 x = ∑ i, x i • f fun j => if i = j then 1 else 0
参数：f : (ι -> R) ->ₗ[R] M₂；x : ι -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pi_eq_sum_univ`：pi_eq_sum_univ {ι : Type*} [Fintype ι] [DecidableEq ι] {
R : Type*} [NonAssocSemiring R] (x : ι -> R) : x = ∑ i, (x i) • fun j => if i = 
j th…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…

--- 原说明 ---
A linear map `f` applied to `x : ι → R` can be computed using the image under `f
` of elements
of the canonical basis.
-/
theorem pi_apply_eq_sum_univ [Fintype ι] (f : (ι → R) →ₗ[R] M₂) (x : ι → R) :
    f x = ∑ i, x i • f fun j => if i = j then 1 else 0 := by
  conv_lhs => rw [pi_eq_sum_univ x, map_sum]
  refine Finset.sum_congr rfl (fun _ _ => ?_)
  rw [map_smul]

end LinearMap

namespace Submodule

variable [Semiring R] {φ : ι → Type*} [(i : ι) → AddCommMonoid (φ i)] [(i : ι) → Module R (φ i)]

open LinearMap

/-- A version of `Set.pi` for submodules. Given an index set `I` and a family of submodules
`p : (i : ι) → Submodule R (φ i)`, `pi I p` is the submodule of dependent functions
`f : (i : ι) → φ i` such that `f i` belongs to `p i` whenever `i ∈ I`. -/
@[simps]
/-
**Submodule.pi** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：pi (I : Set ι) (p : (i : ι) -> Submodule R (φ i)) : Submodule R ((i : ι) -
> φ i) where carrier
参数：I : Set ι；p : (i : ι) -> Submodule R (φ i)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `Set.pi` for submodules. Given an index set `I` and a family of sub
modules
`p : (i : ι) → Submodule R (φ i)`, `pi I p` is the submodule of dependent functi
ons
`f : (i : ι) → φ i` such that `f i` belongs to `p i` whenever `i ∈ I`.
-/
def pi (I : Set ι) (p : (i : ι) → Submodule R (φ i)) : Submodule R ((i : ι) → φ i) where
  carrier := Set.pi I fun i => p i
  zero_mem' i _ := (p i).zero_mem
  add_mem' {_ _} hx hy i hi := (p i).add_mem (hx i hi) (hy i hi)
  smul_mem' c _ hx i hi := (p i).smul_mem c (hx i hi)

attribute [norm_cast] coe_pi

variable {I : Set ι} {p q : (i : ι) → Submodule R (φ i)} {x : (i : ι) → φ i}

@[simp]
/-
**Submodule.mem_pi** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mem_pi : x in pi I p ↔ forall i in I, x i in p i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_pi : x ∈ pi I p ↔ ∀ i ∈ I, x i ∈ p i :=
  Iff.rfl

@[simp]
/-
**Submodule.pi_empty** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：pi_empty (p : (i : ι) -> Submodule R (φ i)) : pi ∅ p = ⊤
参数：p : (i : ι) -> Submodule R (φ i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.empty_pi`：empty_pi (s : forall i, Set (α i)) : pi ∅ s = univ
-/
theorem pi_empty (p : (i : ι) → Submodule R (φ i)) : pi ∅ p = ⊤ :=
  SetLike.coe_injective <| Set.empty_pi _

@[simp]
/-
**Submodule.pi_top** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：pi_top (s : Set ι) : (pi s fun i : ι => (⊤ : Submodule R (φ i))) = ⊤
参数：s : Set ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.pi_univ`：pi_univ (s : Set ι) : (pi s fun i => (univ : Set (α i))) = 
univ
-/
theorem pi_top (s : Set ι) : (pi s fun i : ι ↦ (⊤ : Submodule R (φ i))) = ⊤ :=
  SetLike.coe_injective <| Set.pi_univ _

@[simp]
/-
**Submodule.pi_univ_bot** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：pi_univ_bot : (pi Set.univ fun i : ι => (⊥ : Submodule R (φ i))) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `trivial`：True
-/
theorem pi_univ_bot : (pi Set.univ fun i : ι ↦ (⊥ : Submodule R (φ i))) = ⊥ :=
  le_bot_iff.mp fun _ h ↦ funext fun i ↦ h i trivial

@[gcongr]
/-
**Submodule.pi_mono** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：pi_mono {s : Set ι} (h : forall i in s, p i <= q i) : pi s p <= pi s q
参数：h : forall i in s, p i <= q i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.pi_mono`：pi_mono (h : forall i in s, t₁ i subseteq t₂ i) : pi s t₁ s
ubseteq pi s t₂
-/
theorem pi_mono {s : Set ι} (h : ∀ i ∈ s, p i ≤ q i) : pi s p ≤ pi s q :=
  Set.pi_mono h
/-
**Submodule.biInf_comap_proj** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：biInf_comap_proj : ⨅ i in I, comap (proj i : ((i : ι) -> φ i) ->ₗ[R] φ i) 
(p i) = pi I p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem biInf_comap_proj :
    ⨅ i ∈ I, comap (proj i : ((i : ι) → φ i) →ₗ[R] φ i) (p i) = pi I p := by
  ext x
  simp
/-
**Submodule.iInf_comap_proj** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：iInf_comap_proj : ⨅ i, comap (proj i : ((i : ι) -> φ i) ->ₗ[R] φ i) (p i) 
= pi Set.univ p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem iInf_comap_proj :
    ⨅ i, comap (proj i : ((i : ι) → φ i) →ₗ[R] φ i) (p i) = pi Set.univ p := by
  ext x
  simp
/-
**Submodule.le_comap_single_pi** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：le_comap_single_pi [DecidableEq ι] (p : (i : ι) -> Submodule R (φ i)) {I i
} : p i <= Submodule.comap (LinearMap.single R φ i : φ i ->ₗ[R] _) (Submodule.pi
 I p)
参数：p : (i : ι) -> Submodule R (φ i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mem_comap`：mem_comap {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R₂ M₂
} : x in comap f p ↔ f x in p
· 使用定理 `Submodule.mem_pi`：mem_pi : x in pi I p ↔ forall i in I, x i in p i
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
-/
theorem le_comap_single_pi [DecidableEq ι] (p : (i : ι) → Submodule R (φ i)) {I i} :
    p i ≤ Submodule.comap (LinearMap.single R φ i : φ i →ₗ[R] _) (Submodule.pi I p) := by
  intro x hx
  rw [Submodule.mem_comap, Submodule.mem_pi]
  rintro j -
  rcases eq_or_ne j i with rfl | hne <;> simp [*]
/-
**Submodule.iSup_map_single_le** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：iSup_map_single_le [DecidableEq ι] : ⨆ i, map (LinearMap.single R φ i) (p 
i) <= pi I p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.map_le_iff_le_comap`：map_le_iff_le_comap {f : M ->ₛₗ[σ₁₂] M₂} 
{p : Submodule R M} {q : Submodule R₂ M₂} : map f p <= q ↔ p <= comap f q
· 使用定理 `Submodule.le_comap_single_pi`：le_comap_single_pi [DecidableEq ι] (p : (i
 : ι) -> Submodule R (φ i)) {I i} : p i <= Submodule.comap (LinearMap.single R φ
 i : φ i ->ₗ[R] _)…
-/
theorem iSup_map_single_le [DecidableEq ι] :
    ⨆ i, map (LinearMap.single R φ i) (p i) ≤ pi I p :=
  iSup_le fun _ => map_le_iff_le_comap.mpr <| le_comap_single_pi _
/-
**Submodule.iSup_map_single** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：iSup_map_single [DecidableEq ι] [Finite ι] : ⨆ i, map (LinearMap.single R 
φ i : φ i ->ₗ[R] (i : ι) -> φ i) (p i) = pi Set.univ p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Submodule.iSup_map_single_le`：iSup_map_single_le [DecidableEq ι] : ⨆ i, 
map (LinearMap.single R φ i) (p i) <= pi I p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.univ_sum_single`：∀ {I : Type u_7} [inst : DecidableEq I] {M : I →
 Type u_8} [inst_1 : (i : I) → AddCommMonoid (M i)] [inst_2 : Fintype I]   (f : 
(i : I) → M …
· 使用定理 `Submodule.sum_mem_iSup`：sum_mem_iSup {ι : Type*} [Fintype ι] {f : ι -> M
} {p : ι -> Submodule R M} (h : forall i, f i in p i) : (∑ i, f i) in ⨆ i, p i
· 使用定理 `Submodule.mem_map_of_mem`：mem_map_of_mem {f : M ->ₛₗ[σ₁₂] M₂} {p : Submo
dule R M} {r} (h : r in p) : f r in map f p
· 使用定理 `trivial`：True
-/
theorem iSup_map_single [DecidableEq ι] [Finite ι] :
    ⨆ i, map (LinearMap.single R φ i : φ i →ₗ[R] (i : ι) → φ i) (p i) = pi Set.univ p := by
  cases nonempty_fintype ι
  refine iSup_map_single_le.antisymm fun x hx => ?_
  rw [← Finset.univ_sum_single x]
  exact sum_mem_iSup fun i => mem_map_of_mem (hx i trivial)

end Submodule

namespace LinearMap

variable [Semiring R]

/-
**LinearMap.ker_compLeft** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：ker_compLeft [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R M
₂] (f : M ->ₗ[R] M₂) (I : Type*) : LinearMap.ker (f.compLeft I) = Submodule.pi (
Set.univ : Set I) (fun _ => LinearMap.ker f)
参数：f : M ->ₗ[R] M₂；I : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `trivial`：True
-/
lemma ker_compLeft [AddCommMonoid M] [AddCommMonoid M₂]
    [Module R M] [Module R M₂] (f : M →ₗ[R] M₂) (I : Type*) :
    LinearMap.ker (f.compLeft I) = Submodule.pi (Set.univ : Set I) (fun _ => LinearMap.ker f) :=
  Submodule.ext fun _ => ⟨fun (hx : _ = _) i _ => congr_fun hx i,
    fun hx => funext fun i => hx i trivial⟩
/-
**LinearMap.range_compLeft** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：range_compLeft [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R
 M₂] (f : M ->ₗ[R] M₂) (I : Type*) : LinearMap.range (f.compLeft I) = Submodule.
pi (Set.univ : Set I) (fun _ => LinearMap.range f)
参数：f : M ->ₗ[R] M₂；I : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `trivial`：True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma range_compLeft [AddCommMonoid M] [AddCommMonoid M₂]
    [Module R M] [Module R M₂] (f : M →ₗ[R] M₂) (I : Type*) :
    LinearMap.range (f.compLeft I) =
      Submodule.pi (Set.univ : Set I) (fun _ => LinearMap.range f) :=
  Submodule.ext fun _ => ⟨fun ⟨y, hy⟩ i _ => ⟨y i, congr_fun hy i⟩, fun hx => by
    choose y hy using hx
    exact ⟨fun i => y i trivial, funext fun i => hy i trivial⟩⟩

end LinearMap

namespace LinearEquiv

variable [Semiring R] {φ ψ χ : ι → Type*}
variable [(i : ι) → AddCommMonoid (φ i)] [(i : ι) → Module R (φ i)]
variable [(i : ι) → AddCommMonoid (ψ i)] [(i : ι) → Module R (ψ i)]
variable [(i : ι) → AddCommMonoid (χ i)] [(i : ι) → Module R (χ i)]

set_option backward.isDefEq.respectTransparency false in
/-- Combine a family of linear equivalences into a linear equivalence of `pi`-types.

This is `Equiv.piCongrRight` as a `LinearEquiv` -/
/-
**LinearEquiv.piCongrRight** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：piCongrRight (e : (i : ι) -> φ i ≃ₗ[R] ψ i) : ((i : ι) -> φ i) ≃ₗ[R] (i : 
ι) -> ψ i
参数：e : (i : ι) -> φ i ≃ₗ[R] ψ i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Combine a family of linear equivalences into a linear equivalence of `pi`-types.

This is `Equiv.piCongrRight` as a `LinearEquiv`
-/
def piCongrRight (e : (i : ι) → φ i ≃ₗ[R] ψ i) : ((i : ι) → φ i) ≃ₗ[R] (i : ι) → ψ i :=
  { AddEquiv.piCongrRight fun j => (e j).toAddEquiv with
    toFun := fun f i => e i (f i)
    invFun := fun f i => (e i).symm (f i)
    map_smul' := fun c f => by ext; simp }

@[simp]
/-
**LinearEquiv.piCongrRight_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：piCongrRight_apply (e : (i : ι) -> φ i ≃ₗ[R] ψ i) (f i) : piCongrRight e f
 i = e i (f i)
参数：e : (i : ι) -> φ i ≃ₗ[R] ψ i；f i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem piCongrRight_apply (e : (i : ι) → φ i ≃ₗ[R] ψ i) (f i) :
    piCongrRight e f i = e i (f i) := rfl

@[simp]
/-
**LinearEquiv.piCongrRight_refl** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：piCongrRight_refl : (piCongrRight fun j => refl R (φ j)) = refl _ _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem piCongrRight_refl : (piCongrRight fun j => refl R (φ j)) = refl _ _ :=
  rfl

@[simp]
/-
**LinearEquiv.piCongrRight_symm** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：piCongrRight_symm (e : (i : ι) -> φ i ≃ₗ[R] ψ i) : (piCongrRight e).symm =
 piCongrRight fun i => (e i).symm
参数：e : (i : ι) -> φ i ≃ₗ[R] ψ i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem piCongrRight_symm (e : (i : ι) → φ i ≃ₗ[R] ψ i) :
    (piCongrRight e).symm = piCongrRight fun i => (e i).symm :=
  rfl

@[simp]
/-
**LinearEquiv.piCongrRight_trans** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：piCongrRight_trans (e : (i : ι) -> φ i ≃ₗ[R] ψ i) (f : (i : ι) -> ψ i ≃ₗ[R
] χ i) : (piCongrRight e).trans (piCongrRight f) = piCongrRight fun i => (e i).t
rans (f i)
参数：e : (i : ι) -> φ i ≃ₗ[R] ψ i；f : (i : ι) -> ψ i ≃ₗ[R] χ i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem piCongrRight_trans (e : (i : ι) → φ i ≃ₗ[R] ψ i) (f : (i : ι) → ψ i ≃ₗ[R] χ i) :
    (piCongrRight e).trans (piCongrRight f) = piCongrRight fun i => (e i).trans (f i) :=
  rfl

variable (R φ)

/-- Transport dependent functions through an equivalence of the base space.

This is `Equiv.piCongrLeft'` as a `LinearEquiv`. -/
@[simps +simpRhs]
/-
**LinearEquiv.piCongrLeft'** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：piCongrLeft' (e : ι ≃ ι') : ((i' : ι) -> φ i') ≃ₗ[R] (i : ι') -> φ e.symm 
i
参数：e : ι ≃ ι'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Transport dependent functions through an equivalence of the base space.

This is `Equiv.piCongrLeft'` as a `LinearEquiv`.
-/
def piCongrLeft' (e : ι ≃ ι') : ((i' : ι) → φ i') ≃ₗ[R] (i : ι') → φ <| e.symm i :=
  { Equiv.piCongrLeft' φ e with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

/-- Transporting dependent functions through an equivalence of the base,
expressed as a "simplification".

This is `Equiv.piCongrLeft` as a `LinearEquiv` -/
/-
**LinearEquiv.piCongrLeft** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：piCongrLeft (e : ι' ≃ ι) : ((i' : ι') -> φ (e i')) ≃ₗ[R] (i : ι) -> φ i
参数：e : ι' ≃ ι。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Transporting dependent functions through an equivalence of the base,
expressed as a "simplification".

This is `Equiv.piCongrLeft` as a `LinearEquiv`
-/
def piCongrLeft (e : ι' ≃ ι) : ((i' : ι') → φ (e i')) ≃ₗ[R] (i : ι) → φ i :=
  (piCongrLeft' R φ e.symm).symm

/-- `Equiv.piCurry` as a `LinearEquiv`. -/
/-
**LinearEquiv.piCurry** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：piCurry {ι : Type*} {κ : ι -> Type*} (α : forall i, κ i -> Type*) [forall 
i k, AddCommMonoid (α i k)] [forall i k, Module R (α i k)] : (Π i : Sigma κ, α i
.1 i.2) ≃ₗ[R] Π i j, α i j where __
参数：α : forall i, κ i -> Type*；α i k；α i k。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Equiv.piCurry` as a `LinearEquiv`.
-/
def piCurry {ι : Type*} {κ : ι → Type*} (α : ∀ i, κ i → Type*)
    [∀ i k, AddCommMonoid (α i k)] [∀ i k, Module R (α i k)] :
    (Π i : Sigma κ, α i.1 i.2) ≃ₗ[R] Π i j, α i j where
  __ := Equiv.piCurry α
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
/-
**LinearEquiv.piCurry_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ (R : Type u) [inst : Semiring R] {ι : Type u_4} {κ : ι → Type u_5} (α : 
(i : ι) → κ i → Type u_6)   [inst_1 : (i : ι) → (k : κ i) → AddCommMonoid (α i k
)] [inst_2 : (i : ι) → (k : κ i) → _root_.Module R (α i k)]   (f : (x : (i : ι) 
× κ i) → α x.fst x.snd), (LinearEquiv.piCurry R α) f = Sigma.curry f
参数：R : Type u；α : (i : ι) → κ i → Type u_6；i : ι；k : κ i；α i k；i : ι；k : κ i；α i
 k；f : (x : (i : ι) × κ i) → α x.fst x.snd；LinearEquiv.piCurry R α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem piCurry_apply {ι : Type*} {κ : ι → Type*} (α : ∀ i, κ i → Type*)
    [∀ i k, AddCommMonoid (α i k)] [∀ i k, Module R (α i k)]
    (f : ∀ x : Σ i, κ i, α x.1 x.2) :
    piCurry R α f = Sigma.curry f :=
  rfl
/-
**LinearEquiv.piCurry_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ (R : Type u) [inst : Semiring R] {ι : Type u_4} {κ : ι → Type u_5} (α : 
(i : ι) → κ i → Type u_6)   [inst_1 : (i : ι) → (k : κ i) → AddCommMonoid (α i k
)] [inst_2 : (i : ι) → (k : κ i) → _root_.Module R (α i k)]   (f : (a : ι) → (b 
: κ a) → α a b), (LinearEquiv.piCurry R α).symm f = Sigma.uncurry f
参数：R : Type u；α : (i : ι) → κ i → Type u_6；i : ι；k : κ i；α i k；i : ι；k : κ i；α i
 k；f : (a : ι) → (b : κ a) → α a b；LinearEquiv.piCurry R α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem piCurry_symm_apply {ι : Type*} {κ : ι → Type*} (α : ∀ i, κ i → Type*)
    [∀ i k, AddCommMonoid (α i k)] [∀ i k, Module R (α i k)]
    (f : ∀ a b, α a b) :
    (piCurry R α).symm f = Sigma.uncurry f :=
  rfl

/-- This is `Equiv.piOptionEquivProd` as a `LinearEquiv` -/
/-
**LinearEquiv.piOptionEquivProd** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：piOptionEquivProd {ι : Type*} {M : Option ι -> Type*} [(i : Option ι) -> A
ddCommMonoid (M i)] [(i : Option ι) -> Module R (M i)] : ((i : Option ι) -> M i)
 ≃ₗ[R] M none × ((i : ι) -> M (some i))
参数：i : Option ι；M i；i : Option ι；M i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is `Equiv.piOptionEquivProd` as a `LinearEquiv`
-/
def piOptionEquivProd {ι : Type*} {M : Option ι → Type*} [(i : Option ι) → AddCommMonoid (M i)]
    [(i : Option ι) → Module R (M i)] :
    ((i : Option ι) → M i) ≃ₗ[R] M none × ((i : ι) → M (some i)) :=
  { Equiv.piOptionEquivProd with
    map_add' := by simp [funext_iff]
    map_smul' := by simp [funext_iff] }

variable (ι M) (S : Type*) [Fintype ι] [DecidableEq ι] [Semiring S] [AddCommMonoid M]
  [Module R M] [Module S M] [SMulCommClass R S M]

/-- Linear equivalence between linear functions `Rⁿ → M` and `Mⁿ`. The spaces `Rⁿ` and `Mⁿ`
are represented as `ι → R` and `ι → M`, respectively, where `ι` is a finite type.

This as an `S`-linear equivalence, under the assumption that `S` acts on `M` commuting with `R`.
When `R` is commutative, we can take this to be the usual action with `S = R`.
Otherwise, `S = ℕ` shows that the equivalence is additive.
See note [bundled maps over different rings]. -/
/-
**LinearEquiv.piRing** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：piRing : ((ι -> R) ->ₗ[R] M) ≃ₗ[S] ι -> M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Linear equivalence between linear functions `Rⁿ → M` and `Mⁿ`. The spaces `Rⁿ` a
nd `Mⁿ`
are represented as `ι → R` and `ι → M`, respectively, where `ι` is a finite type
.

This as an `S`-linear equivalence, under the assumption that `S` acts on `M` com
muting with `R`.
When `R` is commutative, we can take this to be the usual action with `S = R`.
Otherwise, `S = ℕ` shows that the equivalence is additive.
See note [bundled maps over different rings].
-/
def piRing : ((ι → R) →ₗ[R] M) ≃ₗ[S] ι → M :=
  (LinearMap.lsum R (fun _ : ι => R) S).symm.trans
    (piCongrRight fun _ => LinearMap.ringLmapEquivSelf R S M)

variable {ι R M}

@[simp]
/-
**LinearEquiv.piRing_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：piRing_apply (f : (ι -> R) ->ₗ[R] M) (i : ι) : piRing R M ι S f i = f (Pi.
single i 1)
参数：f : (ι -> R) ->ₗ[R] M；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem piRing_apply (f : (ι → R) →ₗ[R] M) (i : ι) : piRing R M ι S f i = f (Pi.single i 1) :=
  rfl

@[simp]
/-
**LinearEquiv.piRing_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：piRing_symm_apply (f : ι -> M) (g : ι -> R) : (piRing R M ι S).symm f g = 
∑ i, g i • f i
参数：f : ι -> M；g : ι -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `LinearMap.ringLmapEquivSelf_symm_apply`：∀ (R : Type u_1) (S : Type u_4) 
(M : Type u_5) [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : AddCommMonoid
 M]   [inst_3 : _root_.Modul…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearMap.coe_sum`：coe_sum {ι : Type*} (t : Finset ι) (f : ι -> M ->ₛₗ[σ
₁₂] M₂) : ⇑(∑ i in t, f i) = ∑ i in t, (f i : M -> M₂)
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem piRing_symm_apply (f : ι → M) (g : ι → R) : (piRing R M ι S).symm f g = ∑ i, g i • f i := by
  simp [piRing, LinearMap.lsum_apply]

-- TODO additive version?
/-- `Equiv.sumArrowEquivProdArrow` as a linear equivalence.
-/
/-
**LinearEquiv.sumArrowLequivProdArrow** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：sumArrowLequivProdArrow (α β R M : Type*) [Semiring R] [AddCommMonoid M] [
Module R M] : (α oplus β -> M) ≃ₗ[R] (α -> M) × (β -> M)
参数：α β R M : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Equiv.sumArrowEquivProdArrow` as a linear equivalence.
-/
def sumArrowLequivProdArrow (α β R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] :
    (α ⊕ β → M) ≃ₗ[R] (α → M) × (β → M) :=
  { Equiv.sumArrowEquivProdArrow α β
      M with
    map_add' := by
      intro f g
      ext <;> rfl
    map_smul' := by
      intro r f
      ext <;> rfl }

@[simp]
/-
**LinearEquiv.sumArrowLequivProdArrow_apply_fst** 是 Mathlib 中的一个定理，位于命名空间 `Linea
rEquiv`。
形式化陈述：sumArrowLequivProdArrow_apply_fst {α β} (f : α oplus β -> M) (a : α) : (su
mArrowLequivProdArrow α β R M f).1 a = f (Sum.inl a)
参数：f : α oplus β -> M；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumArrowLequivProdArrow_apply_fst {α β} (f : α ⊕ β → M) (a : α) :
    (sumArrowLequivProdArrow α β R M f).1 a = f (Sum.inl a) :=
  rfl

@[simp]
/-
**LinearEquiv.sumArrowLequivProdArrow_apply_snd** 是 Mathlib 中的一个定理，位于命名空间 `Linea
rEquiv`。
形式化陈述：sumArrowLequivProdArrow_apply_snd {α β} (f : α oplus β -> M) (b : β) : (su
mArrowLequivProdArrow α β R M f).2 b = f (Sum.inr b)
参数：f : α oplus β -> M；b : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumArrowLequivProdArrow_apply_snd {α β} (f : α ⊕ β → M) (b : β) :
    (sumArrowLequivProdArrow α β R M f).2 b = f (Sum.inr b) :=
  rfl

@[simp]
/-
**LinearEquiv.sumArrowLequivProdArrow_symm_apply_inl** 是 Mathlib 中的一个定理，位于命名空间 `
LinearEquiv`。
形式化陈述：sumArrowLequivProdArrow_symm_apply_inl {α β} (f : α -> M) (g : β -> M) (a 
: α) : ((sumArrowLequivProdArrow α β R M).symm (f, g)) (Sum.inl a) = f a
参数：f : α -> M；g : β -> M；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumArrowLequivProdArrow_symm_apply_inl {α β} (f : α → M) (g : β → M) (a : α) :
    ((sumArrowLequivProdArrow α β R M).symm (f, g)) (Sum.inl a) = f a :=
  rfl

@[simp]
/-
**LinearEquiv.sumArrowLequivProdArrow_symm_apply_inr** 是 Mathlib 中的一个定理，位于命名空间 `
LinearEquiv`。
形式化陈述：sumArrowLequivProdArrow_symm_apply_inr {α β} (f : α -> M) (g : β -> M) (b 
: β) : ((sumArrowLequivProdArrow α β R M).symm (f, g)) (Sum.inr b) = g b
参数：f : α -> M；g : β -> M；b : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sumArrowLequivProdArrow_symm_apply_inr {α β} (f : α → M) (g : β → M) (b : β) :
    ((sumArrowLequivProdArrow α β R M).symm (f, g)) (Sum.inr b) = g b :=
  rfl

/-- If `ι` has a unique element, then `ι → M` is linearly equivalent to `M`. -/
@[simps +simpRhs -fullyApplied symm_apply]
/-
**LinearEquiv.funUnique** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：funUnique (ι R M : Type*) [Unique ι] [Semiring R] [AddCommMonoid M] [Modul
e R M] : (ι -> M) ≃ₗ[R] M where toAddEquiv
参数：ι R M : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `ι` has a unique element, then `ι → M` is linearly equivalent to `M`.
-/
def funUnique (ι R M : Type*) [Unique ι] [Semiring R] [AddCommMonoid M] [Module R M] :
    (ι → M) ≃ₗ[R] M where
  toAddEquiv := .funUnique ι M
  map_smul' _ _ := rfl

@[simp]
/-
**LinearEquiv.funUnique_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：funUnique_apply (ι R M : Type*) [Unique ι] [Semiring R] [AddCommMonoid M] 
[Module R M] : (funUnique ι R M : (ι -> M) -> M) = eval default
参数：ι R M : Type*。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem funUnique_apply (ι R M : Type*) [Unique ι] [Semiring R] [AddCommMonoid M] [Module R M] :
    (funUnique ι R M : (ι → M) → M) = eval default := rfl

variable (R M)

/-- Linear equivalence between dependent functions `(i : Fin 2) → M i` and `M 0 × M 1`. -/
@[simps +simpRhs -fullyApplied symm_apply]
/-
**LinearEquiv.piFinTwo** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：piFinTwo (M : Fin 2 -> Type v) [(i : Fin 2) -> AddCommMonoid (M i)] [(i : 
Fin 2) -> Module R (M i)] : ((i : Fin 2) -> M i) ≃ₗ[R] M 0 × M 1
参数：M : Fin 2 -> Type v；i : Fin 2；M i；i : Fin 2；M i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Linear equivalence between dependent functions `(i : Fin 2) → M i` and `M 0 × M 
1`.
-/
def piFinTwo (M : Fin 2 → Type v)
    [(i : Fin 2) → AddCommMonoid (M i)] [(i : Fin 2) → Module R (M i)] :
    ((i : Fin 2) → M i) ≃ₗ[R] M 0 × M 1 :=
  { piFinTwoEquiv M with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

@[simp]
/-
**LinearEquiv.piFinTwo_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：piFinTwo_apply (M : Fin 2 -> Type v) [(i : Fin 2) -> AddCommMonoid (M i)] 
[(i : Fin 2) -> Module R (M i)] : (piFinTwo R M : ((i : Fin 2) -> M i) -> M 0 × 
M 1) = fun f => (f 0, f 1)
参数：M : Fin 2 -> Type v；i : Fin 2；M i；i : Fin 2；M i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem piFinTwo_apply (M : Fin 2 → Type v)
    [(i : Fin 2) → AddCommMonoid (M i)] [(i : Fin 2) → Module R (M i)] :
    (piFinTwo R M : ((i : Fin 2) → M i) → M 0 × M 1) = fun f => (f 0, f 1) := rfl

/-- Linear equivalence between vectors in `M² = Fin 2 → M` and `M × M`. -/
@[simps! -fullyApplied]
/-
**LinearEquiv.finTwoArrow** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：finTwoArrow : (Fin 2 -> M) ≃ₗ[R] M × M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Linear equivalence between vectors in `M² = Fin 2 → M` and `M × M`.
-/
def finTwoArrow : (Fin 2 → M) ≃ₗ[R] M × M :=
  { finTwoArrowEquiv M, piFinTwo R fun _ => M with }

end LinearEquiv

/-
**Pi.mem_span_range_single_inl_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Pi.mem_span_range_single_inl_iff [DecidableEq ι] [DecidableEq ι'] [Finite 
ι] [Semiring R] {x : ι oplus ι' -> R} : x in span R (Set.range fun i => single (
Sum.inl i) 1) ↔ forall k, x (Sum.inr k) = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Sum.inl.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : α), (Sum.inl val
 = Sum.inl val_1) = (val = val_1)
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `sum_mem`：∀ {B : Type u_3} {S : B} {M : Type u_4} [inst : AddCommMonoid M
] [inst_1 : SetLike B M] [AddSubmonoidClass B M]   {ι : Type u_5} {t : Finset…
· 使用定理 `SMulMemClass.smul_mem`：∀ {S : Type u_1} {R : outParam (Type u_2)} {M : T
ype u_3} {inst : SMul R M} {inst_1 : SetLike S M}   [self : SMulMemClass S R M] 
{s : S} (r …
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
lemma Pi.mem_span_range_single_inl_iff
    [DecidableEq ι] [DecidableEq ι'] [Finite ι] [Semiring R] {x : ι ⊕ ι' → R} :
    x ∈ span R (Set.range fun i ↦ single (Sum.inl i) 1) ↔ ∀ k, x (Sum.inr k) = 0 := by
  refine ⟨fun hx k ↦ ?_, fun hx ↦ ?_⟩
  · induction hx using span_induction with
    | mem x h => obtain ⟨i, rfl⟩ := h; simp
    | zero => simp
    | add u v _ _ hu hv => simp [hu, hv]
    | smul t u _ hu => simp [hu]
  · have := Fintype.ofFinite ι
    suffices x = ∑ i : ι, x (Sum.inl i) • Pi.single (M := fun _ ↦ R) (Sum.inl i) (1 : R) by
      rw [this]
      exact sum_mem <| fun i _ ↦ SMulMemClass.smul_mem _ <| subset_span <| Set.mem_range_self i
    ext (i | i)
    · simp [single_apply]
    · simp [hx i]

section Extend

variable (R) {η : Type*} [Semiring R] (s : ι → η)

/-- `Function.extend s f 0` as a bundled linear map. -/
@[simps]
/-
**Function.ExtendByZero.linearMap** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Function.ExtendByZero.linearMap : (ι -> R) ->ₗ[R] η -> R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Function.extend s f 0` as a bundled linear map.
-/
noncomputable def Function.ExtendByZero.linearMap : (ι → R) →ₗ[R] η → R :=
  { Function.ExtendByZero.hom R s with
    toFun := fun f => Function.extend s f 0
    map_smul' := fun r f => by simpa using Function.extend_smul r s f 0 }

end Extend

variable (R) in
/-- `Fin.consEquiv` as a continuous linear equivalence. -/
@[simps]
/-
**Fin.consLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Fin.consLinearEquiv {n : Nat} (M : Fin n.succ -> Type*) [Semiring R] [fora
ll i, AddCommMonoid (M i)] [forall i, Module R (M i)] : (M 0 × Π i, M (Fin.succ 
i)) ≃ₗ[R] (Π i, M i) where __
参数：M : Fin n.succ -> Type*；M i；M i。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)

--- 原说明 ---
`Fin.consEquiv` as a continuous linear equivalence.
-/
def Fin.consLinearEquiv
    {n : ℕ} (M : Fin n.succ → Type*) [Semiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] :
    (M 0 × Π i, M (Fin.succ i)) ≃ₗ[R] (Π i, M i) where
  __ := Fin.consEquiv M
  map_add' x y := funext <| Fin.cases rfl (by simp)
  map_smul' c x := funext <| Fin.cases rfl (by simp)


/-! ### Bundled versions of `Matrix.vecCons` and `Matrix.vecEmpty`

The idea of these definitions is to be able to define a map as `x ↦ ![f₁ x, f₂ x, f₃ x]`, where
`f₁ f₂ f₃` are already linear maps, as `f₁.vecCons <| f₂.vecCons <| f₃.vecCons <| vecEmpty`.

While the same thing could be achieved using `LinearMap.pi ![f₁, f₂, f₃]`, this is not
definitionally equal to the result using `LinearMap.vecCons`, as `Fin.cases` and function
application do not commute definitionally.

Versions for when `f₁ f₂ f₃` are bilinear maps are also provided.

-/


section Fin

section Semiring

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R M₂] [Module R M₃]

/-- The linear map defeq to `Matrix.vecEmpty` -/
/-
**LinearMap.vecEmpty** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearMap.vecEmpty : M ->ₗ[R] Fin 0 -> M₃ where toFun _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear map defeq to `Matrix.vecEmpty`
-/
def LinearMap.vecEmpty : M →ₗ[R] Fin 0 → M₃ where
  toFun _ := Matrix.vecEmpty
  map_add' _ _ := Subsingleton.elim _ _
  map_smul' _ _ := Subsingleton.elim _ _

@[simp]
/-
**LinearMap.vecEmpty_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.vecEmpty_apply (m : M) : (LinearMap.vecEmpty : M ->ₗ[R] Fin 0 ->
 M₃) m = ![]
参数：m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem LinearMap.vecEmpty_apply (m : M) : (LinearMap.vecEmpty : M →ₗ[R] Fin 0 → M₃) m = ![] :=
  rfl

/-- A linear map into `Fin n.succ → M₃` can be built out of a map into `M₃` and a map into
`Fin n → M₃`. -/
/-
**LinearMap.vecCons** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearMap.vecCons {n} (f : M ->ₗ[R] M₂) (g : M ->ₗ[R] Fin n -> M₂) : M ->ₗ
[R] Fin n.succ -> M₂
参数：f : M ->ₗ[R] M₂；g : M ->ₗ[R] Fin n -> M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear map into `Fin n.succ → M₃` can be built out of a map into `M₃` and a ma
p into
`Fin n → M₃`.
-/
def LinearMap.vecCons {n} (f : M →ₗ[R] M₂) (g : M →ₗ[R] Fin n → M₂) : M →ₗ[R] Fin n.succ → M₂ :=
  Fin.consLinearEquiv R (fun _ : Fin n.succ => M₂) ∘ₗ f.prod g

@[simp]
/-
**LinearMap.vecCons_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.vecCons_apply {n} (f : M ->ₗ[R] M₂) (g : M ->ₗ[R] Fin n -> M₂) (
m : M) : f.vecCons g m = Matrix.vecCons (f m) (g m)
参数：f : M ->ₗ[R] M₂；g : M ->ₗ[R] Fin n -> M₂；m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem LinearMap.vecCons_apply {n} (f : M →ₗ[R] M₂) (g : M →ₗ[R] Fin n → M₂) (m : M) :
    f.vecCons g m = Matrix.vecCons (f m) (g m) :=
  rfl

variable (R) in
/--
To show a property `motive` of modules holds for arbitrary finite products of modules, it suffices
to show
1. `motive` is stable under isomorphism.
2. `motive` holds for the zero module.
3. `motive` holds for `M × N` if it holds for both `M` and `N`.

Since we need to apply `motive` to modules in `Type u` and in `Type (max u v)`, there is a second
`motive'` argument which is required to be equivalent to `motive` up to universe lifting by `equiv`.

See `Module.pi_induction'` for a version where `motive` assumes `AddCommGroup` instead.
-/
@[elab_as_elim]
/-
**Module.pi_induction** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.pi_induction {ι : Type v} [Finite ι] (motive : forall (N : Type u) 
[AddCommMonoid N] [Module R N], Prop) (motive' : forall (N : Type (max u v)) [Ad
dCommMonoid N] [Module R N], Prop) (equiv : forall {N : Type u} {N' : Type (max 
u v)} [AddCommMonoid N] [AddCommMonoid N'] [Module R N] [Module R N'], (N ≃ₗ[R] 
N') -> motive N -> motive' N') (equiv' : forall {N N' : Type (max u v)} [AddComm
Monoid N] [AddCommMonoid N'] [Module R N] [Module R N'], (N ≃ₗ[R] N') -> motive'
 N -> motive' N') (unit : 
参数：motive : forall (N : Type u) [AddCommMonoid N] [Module R N], Prop；motive' : f
orall (N : Type (max u v)) [AddCommMonoid N] [Module R N], Prop；equiv : forall {
N : Type u} {N' : Type (max u v)} [AddCommMonoid N] [AddCommMonoid N'] [Module R
 N] [Module R N'], (N ≃ₗ[R] N') -> motive N -> motive' N'；equiv' : forall {N N' 
: Type (max u v)} [AddCommMonoid N] [AddCommMonoid N'] [Module R N] [Module R N'
], (N ≃ₗ[R] N') -> motive' N -> motive' N'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Fintype.induction_empty_option`：induction_empty_option {P : forall (α : 
Type u) [Fintype α], Prop} (of_equiv : forall (α β) [Fintype β] (e : α ≃ β), @P 
α (@Fintype.ofEquiv …
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α

--- 原说明 ---
To show a property `motive` of modules holds for arbitrary finite products of mo
dules, it suffices
to show
1. `motive` is stable under isomorphism.
2. `motive` holds for the zero module.
3. `motive` holds for `M × N` if it holds for both `M` and `N`.

Since we need to apply `motive` to modules in `Type u` and in `Type (max u v)`, 
there is a second
`motive'` argument which is required to be equivalent to `motive` up to universe
 lifting by `equiv`.

See `Module.pi_induction'` for a version where `motive` assumes `AddCommGroup` i
nstead.
-/
lemma Module.pi_induction {ι : Type v} [Finite ι]
    (motive : ∀ (N : Type u) [AddCommMonoid N] [Module R N], Prop)
    (motive' : ∀ (N : Type (max u v)) [AddCommMonoid N] [Module R N], Prop)
    (equiv : ∀ {N : Type u} {N' : Type (max u v)} [AddCommMonoid N] [AddCommMonoid N']
      [Module R N] [Module R N'], (N ≃ₗ[R] N') → motive N → motive' N')
    (equiv' : ∀ {N N' : Type (max u v)} [AddCommMonoid N] [AddCommMonoid N']
      [Module R N] [Module R N'], (N ≃ₗ[R] N') → motive' N → motive' N')
    (unit : motive PUnit) (prod : ∀ {N : Type u} {N' : Type (max u v)} [AddCommMonoid N]
      [AddCommMonoid N'] [Module R N] [Module R N'], motive N → motive' N' → motive' (N × N'))
    (M : ι → Type u) [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    (h : ∀ i, motive (M i)) : motive' (∀ i, M i) := by
  cases nonempty_fintype ι
  revert M
  refine Fintype.induction_empty_option
    (fun α β _ e h M _ _ hM ↦ equiv' (LinearEquiv.piCongrLeft R M e) <| h _ fun i ↦ hM _)
    (fun M _ _ _ ↦ equiv default unit) (fun α _ h M _ _ hn ↦ ?_) ι
  exact equiv' (LinearEquiv.piOptionEquivProd R).symm <| prod (hn _) (h _ fun i ↦ hn i)

end Semiring

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R M₂] [Module R M₃]

/-- The empty bilinear map defeq to `Matrix.vecEmpty` -/
@[simps]
/-
**LinearMap.vecEmpty** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearMap.vecEmpty : M ->ₗ[R] Fin 0 -> M₃ where toFun _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The empty bilinear map defeq to `Matrix.vecEmpty`
-/
def LinearMap.vecEmpty₂ : M →ₗ[R] M₂ →ₗ[R] Fin 0 → M₃ where
  toFun _ := LinearMap.vecEmpty
  map_add' _ _ := LinearMap.ext fun _ => Subsingleton.elim _ _
  map_smul' _ _ := LinearMap.ext fun _ => Subsingleton.elim _ _

/-- A bilinear map into `Fin n.succ → M₃` can be built out of a map into `M₃` and a map into
`Fin n → M₃` -/
@[simps]
/-
**LinearMap.vecCons** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearMap.vecCons {n} (f : M ->ₗ[R] M₂) (g : M ->ₗ[R] Fin n -> M₂) : M ->ₗ
[R] Fin n.succ -> M₂
参数：f : M ->ₗ[R] M₂；g : M ->ₗ[R] Fin n -> M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bilinear map into `Fin n.succ → M₃` can be built out of a map into `M₃` and a 
map into
`Fin n → M₃`
-/
def LinearMap.vecCons₂ {n} (f : M →ₗ[R] M₂ →ₗ[R] M₃) (g : M →ₗ[R] M₂ →ₗ[R] Fin n → M₃) :
    M →ₗ[R] M₂ →ₗ[R] Fin n.succ → M₃ where
  toFun m := LinearMap.vecCons (f m) (g m)
  map_add' x y :=
    LinearMap.ext fun z => by
      simp only [f.map_add, g.map_add, LinearMap.add_apply, LinearMap.vecCons_apply,
        Matrix.cons_add_cons (f x z)]
  map_smul' r x := LinearMap.ext fun z => by simp [Matrix.smul_cons r (f x z)]

end CommSemiring

/-- A variant of `Module.pi_induction` that assumes `AddCommGroup` instead of `AddCommMonoid`. -/
@[elab_as_elim]
/-
**Module.pi_induction'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.pi_induction' {ι : Type v} [Finite ι] (R : Type*) [Ring R] (motive 
: forall (N : Type u) [AddCommGroup N] [Module R N], Prop) (motive' : forall (N 
: Type (max u v)) [AddCommGroup N] [Module R N], Prop) (equiv : forall {N : Type
 u} {N' : Type (max u v)} [AddCommGroup N] [AddCommGroup N'] [Module R N] [Modul
e R N'], (N ≃ₗ[R] N') -> motive N -> motive' N') (equiv' : forall {N N' : Type (
max u v)} [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N'], (N ≃ₗ[R
] N') -> motive' N -> moti
参数：R : Type*；motive : forall (N : Type u) [AddCommGroup N] [Module R N], Prop；mo
tive' : forall (N : Type (max u v)) [AddCommGroup N] [Module R N], Prop；equiv : 
forall {N : Type u} {N' : Type (max u v)} [AddCommGroup N] [AddCommGroup N'] [Mo
dule R N] [Module R N'], (N ≃ₗ[R] N') -> motive N -> motive' N'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Fintype.induction_empty_option`：induction_empty_option {P : forall (α : 
Type u) [Fintype α], Prop} (of_equiv : forall (α β) [Fintype β] (e : α ≃ β), @P 
α (@Fintype.ofEquiv …
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α

--- 原说明 ---
A variant of `Module.pi_induction` that assumes `AddCommGroup` instead of `AddCo
mmMonoid`.
-/
lemma Module.pi_induction' {ι : Type v} [Finite ι] (R : Type*) [Ring R]
    (motive : ∀ (N : Type u) [AddCommGroup N] [Module R N], Prop)
    (motive' : ∀ (N : Type (max u v)) [AddCommGroup N] [Module R N], Prop)
    (equiv : ∀ {N : Type u} {N' : Type (max u v)} [AddCommGroup N] [AddCommGroup N']
      [Module R N] [Module R N'], (N ≃ₗ[R] N') → motive N → motive' N')
    (equiv' : ∀ {N N' : Type (max u v)} [AddCommGroup N] [AddCommGroup N']
      [Module R N] [Module R N'], (N ≃ₗ[R] N') → motive' N → motive' N')
    (unit : motive PUnit) (prod : ∀ {N : Type u} {N' : Type (max u v)} [AddCommGroup N]
      [AddCommGroup N'] [Module R N] [Module R N'], motive N → motive' N' → motive' (N × N'))
    (M : ι → Type u) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (h : ∀ i, motive (M i)) : motive' (∀ i, M i) := by
  cases nonempty_fintype ι
  revert M
  refine Fintype.induction_empty_option
    (fun α β _ e h M _ _ hM ↦ equiv' (LinearEquiv.piCongrLeft R M e) <| h _ fun i ↦ hM _)
    (fun M _ _ _ ↦ equiv default unit) (fun α _ h M _ _ hn ↦ ?_) ι
  exact equiv' (LinearEquiv.piOptionEquivProd R).symm <| prod (hn _) (h _ fun i ↦ hn i)

end Fin

